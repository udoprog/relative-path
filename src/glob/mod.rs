#[cfg(test)]
mod tests;

use std::collections::VecDeque;
use std::fmt;
use std::io;
use std::mem;

use crate::{RelativePath, RelativePathBuf, Root};

type Result<T> = std::result::Result<T, Error>;

#[derive(Debug)]
pub struct Error {
    kind: ErrorKind,
}

impl Error {
    fn new(kind: ErrorKind) -> Self {
        Self { kind }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            ErrorKind::ReadDir(..) => write!(f, "Error reading directory"),
            ErrorKind::DirEntry(..) => write!(f, "Error getting directory entry"),
        }
    }
}

impl From<ErrorKind> for Error {
    #[inline]
    fn from(kind: ErrorKind) -> Self {
        Self::new(kind)
    }
}

#[derive(Debug)]
enum ErrorKind {
    ReadDir(io::Error),
    DirEntry(io::Error),
}

impl std::error::Error for Error {
    #[allow(clippy::match_same_arms)]
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match &self.kind {
            ErrorKind::ReadDir(error) => Some(error),
            ErrorKind::DirEntry(error) => Some(error),
        }
    }
}

/// A compiled glob expression.
///
/// This is returned by [`Root::glob`].
pub struct Glob<'a> {
    root: &'a Root,
    components: Vec<Component<'a>>,
}

impl<'a> Glob<'a> {
    /// Construct a new glob pattern.
    pub(super) fn new(root: &'a Root, pattern: &'a RelativePath) -> Self {
        let components = compile_pattern(pattern);
        Self { root, components }
    }

    /// Construct a new matcher over the compiled glob pattern.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use relative_path::Root;
    ///
    /// let root = Root::new("src")?;
    ///
    /// let glob = root.glob("**/*.rs");
    ///
    /// let mut results = Vec::new();
    ///
    /// for e in glob.matcher() {
    ///     results.push(e?);
    /// }
    ///
    /// results.sort();
    /// assert_eq!(results, vec!["lib.rs", "main.rs"]);
    /// # Ok::<_, Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn matcher(&self) -> Matcher<'_> {
        Matcher {
            root: self.root,
            queue: [(RelativePathBuf::new(), self.components.as_ref())]
                .into_iter()
                .collect(),
        }
    }
}

impl<'a> Matcher<'a> {
    /// Perform an expansion in the filesystem.
    fn expand_filesystem<M>(
        &mut self,
        current: &RelativePath,
        rest: &'a [Component<'a>],
        mut m: M,
    ) -> Result<()>
    where
        M: FnMut(&str) -> bool,
    {
        if let Ok(m) = self.root.metadata(current) {
            if !m.is_dir() {
                return Ok(());
            }
        } else {
            return Ok(());
        }

        for e in self.root.read_dir(current).map_err(ErrorKind::ReadDir)? {
            let e = e.map_err(ErrorKind::DirEntry)?;
            let c = e.file_name();
            let c = c.to_string_lossy();

            if !m(c.as_ref()) {
                continue;
            }

            let mut new = current.to_owned();
            new.push(c.as_ref());
            self.queue.push_back((new, rest));
        }

        Ok(())
    }

    /// Perform star star expansion.
    fn walk(&mut self, current: &RelativePathBuf, rest: &'a [Component<'a>]) -> Result<()> {
        self.queue.push_back((current.clone(), rest));

        let mut queue = VecDeque::new();
        queue.push_back(current.clone());

        while let Some(current) = queue.pop_front() {
            if let Ok(m) = self.root.metadata(&current) {
                if !m.is_dir() {
                    continue;
                }
            } else {
                continue;
            }

            for e in self.root.read_dir(&current).map_err(ErrorKind::ReadDir)? {
                let e = e.map_err(ErrorKind::DirEntry)?;
                let c = e.file_name();
                let c = c.to_string_lossy();
                let next = current.join(c.as_ref());
                self.queue.push_back((next.clone(), rest));
                queue.push_back(next);
            }
        }

        Ok(())
    }
}

/// A matcher that can be iterated over for matched relative path buffers.
pub struct Matcher<'a> {
    root: &'a Root,
    queue: VecDeque<(RelativePathBuf, &'a [Component<'a>])>,
}

impl<'a> Iterator for Matcher<'a> {
    type Item = Result<RelativePathBuf>;

    fn next(&mut self) -> Option<Self::Item> {
        'outer: loop {
            let (mut path, mut components) = self.queue.pop_front()?;

            while let [first, rest @ ..] = components {
                match first {
                    Component::ParentDir => {
                        path = path.join(crate::Component::ParentDir);
                    }
                    Component::Normal(normal) => {
                        path = path.join(normal);
                    }
                    Component::Fragment(fragment) => {
                        if let Err(e) =
                            self.expand_filesystem(&path, rest, |name| fragment.is_match(name))
                        {
                            return Some(Err(e));
                        }

                        continue 'outer;
                    }
                    Component::StarStar => {
                        if let Err(e) = self.walk(&path, rest) {
                            return Some(Err(e));
                        }

                        continue 'outer;
                    }
                }

                components = rest;
            }

            return Some(Ok(path));
        }
    }
}

#[derive(Clone)]
enum Component<'a> {
    /// Parent directory.
    ParentDir,
    /// A normal component.
    Normal(&'a str),
    /// Normal component, compiled into a fragment.
    Fragment(Fragment<'a>),
    /// `**` component, which keeps expanding.
    StarStar,
}

fn compile_pattern(pattern: &RelativePath) -> Vec<Component<'_>> {
    let mut output = Vec::new();

    for c in pattern.components() {
        output.push(match c {
            crate::Component::CurDir => continue,
            crate::Component::ParentDir => Component::ParentDir,
            crate::Component::Normal("**") => Component::StarStar,
            crate::Component::Normal(normal) => {
                let fragment = Fragment::parse(normal);

                if let Some(normal) = fragment.as_literal() {
                    Component::Normal(normal)
                } else {
                    Component::Fragment(fragment)
                }
            }
        });
    }

    output
}

#[derive(Debug, Clone, Copy)]
enum Part<'a> {
    Star,
    Literal(&'a str),
}

/// A match fragment.
#[derive(Debug, Clone)]
pub(crate) struct Fragment<'a> {
    parts: Box<[Part<'a>]>,
}

impl<'a> Fragment<'a> {
    pub(crate) fn parse(string: &'a str) -> Fragment<'a> {
        let mut literal = true;
        let mut parts = Vec::new();
        let mut start = None;

        for (n, c) in string.char_indices() {
            if c == '*' {
                if let Some(s) = start.take() {
                    parts.push(Part::Literal(&string[s..n]));
                }

                if mem::take(&mut literal) {
                    parts.push(Part::Star);
                }
            } else {
                if start.is_none() {
                    start = Some(n);
                }

                literal = true;
            }
        }

        if let Some(s) = start {
            parts.push(Part::Literal(&string[s..]));
        }

        Fragment {
            parts: parts.into(),
        }
    }

    /// Test if the given string matches the current fragment.
    pub(crate) fn is_match(&self, string: &str) -> bool {
        let mut backtrack = VecDeque::new();
        backtrack.push_back((self.parts.as_ref(), string));

        while let Some((mut parts, mut string)) = backtrack.pop_front() {
            while let Some(part) = parts.first() {
                match part {
                    Part::Star => {
                        // Peek the next literal component. If we have a
                        // trailing wildcard (which this constitutes) then it
                        // is by definition a match.
                        let peek = match parts.get(1) {
                            Some(Part::Literal(peek)) => peek,
                            _ => return true,
                        };

                        let peek = match peek.chars().next() {
                            Some(peek) => peek,
                            _ => return true,
                        };

                        while let Some(c) = string.chars().next() {
                            if c == peek {
                                backtrack.push_front((
                                    parts,
                                    string.get(c.len_utf8()..).unwrap_or_default(),
                                ));
                                break;
                            }

                            string = string.get(c.len_utf8()..).unwrap_or_default();
                        }
                    }
                    Part::Literal(literal) => {
                        // The literal component must be an exact prefix of the
                        // current string.
                        let remainder = match string.strip_prefix(literal) {
                            Some(remainder) => remainder,
                            None => return false,
                        };

                        string = remainder;
                    }
                }

                parts = parts.get(1..).unwrap_or_default();
            }

            if string.is_empty() {
                return true;
            }
        }

        false
    }

    /// Treat the fragment as a single normal component.
    fn as_literal(&self) -> Option<&'a str> {
        if let [Part::Literal(one)] = self.parts.as_ref() {
            Some(one)
        } else {
            None
        }
    }
}

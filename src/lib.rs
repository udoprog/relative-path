//! A platform-neutral relative path structure.
//!
//! This library is analogous to `std::path::Path`, and `std::path::PathBuf`, with the exception of
//! the following characteristics:
//!
//! * It does not provide an API to manipulate the Paths in an absolute fashion.
//! * The path separator is set to a fixed character (`/`), making it portable.

use std::mem;
use std::borrow;
use std::path;
use std::fmt;

#[cfg(feature = "serde")]
extern crate serde;

#[cfg(feature = "serde")]
use serde::ser::{Serialize, Serializer};
#[cfg(feature = "serde")]
use serde::de::{self, Deserialize, Deserializer, Visitor};

const SEP: char = '/';

fn strip_prefix(input: &str) -> &str {
    for (i, c) in input.char_indices() {
        if c == SEP {
            continue;
        }

        return &input[i..];
    }

    // all slashes
    ""
}

/// Iterator over all the components in a relative path.
pub struct Components<'a> {
    iter: ::std::str::CharIndices<'a>,
    source: &'a str,
    last_slash: bool,
    offset: usize,
}

impl<'a> Iterator for Components<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((i, c)) = self.iter.next() {
            if c == SEP {
                if !self.last_slash {
                    let start = self.offset;
                    self.offset = i;
                    self.last_slash = true;
                    return Some(&self.source[start..i]);
                }

                continue;
            }

            if self.last_slash {
                self.last_slash = false;
                self.offset = i;
            }
        }

        if self.source.len() > self.offset {
            if self.last_slash {
                self.offset = self.source.len();
            } else {
                let start = self.offset;
                self.offset = self.source.len();
                return Some(&self.source[start..]);
            }
        }

        None
    }
}

/// An owned, mutable relative path.
///
/// This type provides methods to manipulate relative path objects.
pub struct RelativePathBuf {
    inner: String,
}

impl RelativePathBuf {
    pub fn new(inner: String) -> RelativePathBuf {
        RelativePathBuf { inner: inner }
    }

    /// Join this relative path with another relative path.
    pub fn join<P: AsRef<RelativePath>>(&self, path: P) -> RelativePathBuf {
        let mut out = self.to_relative_path_buf();
        out.push(path);
        out
    }

    /// Push another relative path to this path.
    ///
    /// * Ignore sequences of separators (`/`).
    /// * Any initial slashes will be stripped away.
    pub fn push<P: AsRef<RelativePath>>(&mut self, path: P) {
        let other = path.as_ref();

        if self.inner.len() > 0 {
            self.inner.push(SEP);
        }

        self.inner.push_str(strip_prefix(&other.inner))
    }

    /// Convert to an owned `RelativePathBuf`.
    pub fn to_relative_path_buf(&self) -> RelativePathBuf {
        RelativePathBuf::new(self.inner.to_string())
    }

    /// Iterate over all components in this relative path.
    ///
    /// Skips over the separator.
    pub fn components(&self) -> Components {
        Components {
            iter: self.inner.char_indices(),
            source: &self.inner,
            last_slash: true,
            offset: 0,
        }
    }

    /// Create a new path buffer relative to the given path.
    ///
    /// The created path will be relative to the provided `relative_to` argument.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use relative_path::RelativePath;
    /// use std::path::Path;
    ///
    /// let path_buf = RelativePath::new("foo/bar").to_path_buf(Path::new("."));
    /// ```
    pub fn to_path_buf(&self, relative_to: &path::Path) -> path::PathBuf {
        let mut p = relative_to.to_path_buf();
        p.extend(self.components());
        p
    }
}

impl fmt::Debug for RelativePathBuf {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{:?}", &self.inner)
    }
}

impl AsRef<RelativePath> for RelativePathBuf {
    fn as_ref(&self) -> &RelativePath {
        RelativePath::new(&self.inner)
    }
}

impl borrow::Borrow<RelativePath> for RelativePathBuf {
    fn borrow(&self) -> &RelativePath {
        RelativePath::new(&self.inner)
    }
}

/// A borrowed, immutable relative path.
pub struct RelativePath {
    inner: str,
}

impl RelativePath {
    /// Directly wraps a string slice as a `RelativePath` slice.
    pub fn new<S: AsRef<str> + ?Sized>(s: &S) -> &RelativePath {
        let s = strip_prefix(s.as_ref());
        unsafe { mem::transmute(s) }
    }

    /// Join this relative path with another relative path.
    pub fn join<P: AsRef<RelativePath>>(&self, path: P) -> RelativePathBuf {
        let mut out = self.to_relative_path_buf();
        out.push(path);
        out
    }

    /// Iterate over all components in this relative path.
    pub fn components(&self) -> Components {
        Components {
            iter: self.inner.char_indices(),
            source: &self.inner,
            last_slash: true,
            offset: 0,
        }
    }

    /// Convert to an owned `RelativePathBuf`.
    pub fn to_relative_path_buf(&self) -> RelativePathBuf {
        RelativePathBuf::new(self.inner.to_string())
    }

    /// Create a new path buffer relative to the given path.
    pub fn to_path_buf(&self, relative_to: &path::Path) -> path::PathBuf {
        let mut p = relative_to.to_path_buf();
        p.extend(self.components());
        p
    }
}

impl fmt::Debug for RelativePath {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{:?}", &self.inner)
    }
}

impl ToOwned for RelativePath {
    type Owned = RelativePathBuf;

    fn to_owned(&self) -> RelativePathBuf {
        self.to_relative_path_buf()
    }
}

impl AsRef<RelativePath> for String {
    fn as_ref(&self) -> &RelativePath {
        RelativePath::new(self)
    }
}

impl AsRef<RelativePath> for str {
    fn as_ref(&self) -> &RelativePath {
        RelativePath::new(self)
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;
    use super::*;

    #[test]
    fn test_join() {
        let path = RelativePath::new("hello/world").join("///foo/bar/baz");
        let result: Vec<_> = path.components().collect();
        assert_eq!(vec!["hello", "world", "foo", "bar", "baz"], result);
    }

    #[test]
    fn test_join_empty() {
        let path = RelativePath::new("").join("///foo/bar/baz");
        let result: Vec<_> = path.components().collect();
        assert_eq!(vec!["foo", "bar", "baz"], result);
    }

    #[test]
    fn test_components_iterator() {
        assert_eq!(
            vec!["hello", "world"],
            RelativePath::new("/hello///world//")
                .components()
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_to_path_buf() {
        let path = RelativePath::new("/hello///world//");
        let path_buf = path.to_path_buf(Path::new("."));
        let expected = Path::new(".").join("hello").join("world");
        assert_eq!(expected, path_buf);
    }
}

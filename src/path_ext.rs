// Copyright 2012-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Ported from the pathdiff crate, which adapted the original rustc's path_relative_from
// https://github.com/Manishearth/pathdiff/blob/master/src/lib.rs
// https://github.com/rust-lang/rust/blob/e1d0de82cc40b666b88d4a6d2c9dcbc81d7ed27f/src/librustc_back/rpath.rs#L116-L158

use std::error;
use std::fmt;
use std::path::{self, Path, PathBuf};

use crate::{Component, RelativePathBuf};

/// An error raised when attempting to convert a path using
/// [`PathExt::relative_to`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelativeToError {
    kind: RelativeToErrorKind,
}

/// Error kind for [`RelativeToError`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
enum RelativeToErrorKind {
    /// Non-relative component in path.
    NonRelative,
    /// Non-utf8 component in path.
    NonUtf8,
}

impl fmt::Display for RelativeToError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self.kind {
            RelativeToErrorKind::NonRelative => "path contains non-relative component".fmt(fmt),
            RelativeToErrorKind::NonUtf8 => "path contains non-utf8 component".fmt(fmt),
        }
    }
}

impl error::Error for RelativeToError {}

impl From<RelativeToErrorKind> for RelativeToError {
    #[inline]
    fn from(kind: RelativeToErrorKind) -> Self {
        Self { kind }
    }
}

/// Extension methods for [`Path`] and [`PathBuf`] to for building and
/// interacting with [`RelativePath`].
///
/// [`RelativePath`]: crate::RelativePath
pub trait PathExt: private::Sealed {
    /// Build a relative path from the provided directory to `self`.
    ///
    /// Producing a relative path like this is a logical operation and does not
    /// guarantee that the constructed path corresponds to what the filesystem
    /// would do. On Linux for example symbolic links could mean that the
    /// logical path doesn't correspond to the filesystem path.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::path::Path;
    /// use relative_path::{RelativePath, PathExt};
    ///
    /// let baz = Path::new("/foo/bar/baz");
    /// let bar = Path::new("/foo/bar");
    /// let qux = Path::new("/foo/bar/qux");
    ///
    /// assert_eq!(bar.relative_to(baz)?, RelativePath::new("../"));
    /// assert_eq!(baz.relative_to(bar)?, RelativePath::new("baz"));
    /// assert_eq!(qux.relative_to(baz)?, RelativePath::new("../qux"));
    /// assert_eq!(baz.relative_to(qux)?, RelativePath::new("../baz"));
    /// assert_eq!(bar.relative_to(qux)?, RelativePath::new("../"));
    /// # Ok::<_, relative_path::RelativeToError>(())
    /// ```
    fn relative_to<P: AsRef<Path>>(&self, root: P) -> Result<RelativePathBuf, RelativeToError>;
}

impl PathExt for Path {
    fn relative_to<P: AsRef<Path>>(&self, root: P) -> Result<RelativePathBuf, RelativeToError> {
        use path::Component::*;

        // Helper function to convert from a std::path::Component to a
        // relative_path::Component.
        fn std_to_c(c: path::Component<'_>) -> Result<Component<'_>, RelativeToError> {
            Ok(match c {
                CurDir => Component::CurDir,
                ParentDir => Component::ParentDir,
                Normal(n) => Component::Normal(n.to_str().ok_or(RelativeToErrorKind::NonUtf8)?),
                _ => return Err(RelativeToErrorKind::NonRelative.into()),
            })
        }

        let root = root.as_ref();
        let mut a_it = self.components();
        let mut b_it = root.components();

        // Ensure that the two paths are both either relative, or have the same
        // prefix. Strips any common prefix the two paths do have. Prefixes are
        // platform dependent, but different prefixes would for example indicate
        // paths for different drives on Windows.
        let (a_head, b_head) = loop {
            match (a_it.next(), b_it.next()) {
                (Some(RootDir), Some(RootDir)) => (),
                (Some(Prefix(a)), Some(Prefix(b))) if a == b => (),
                (Some(Prefix(_) | RootDir), _) | (_, Some(Prefix(_) | RootDir)) => {
                    return Err(RelativeToErrorKind::NonRelative.into());
                }
                (None, None) => break (None, None),
                (a, b) if a != b => break (a, b),
                _ => (),
            }
        };

        let mut a_it = a_head.into_iter().chain(a_it);
        let mut b_it = b_head.into_iter().chain(b_it);
        let mut buf = RelativePathBuf::new();

        loop {
            let a = match a_it.next() {
                Some(a) => a,
                None => {
                    for _ in b_it {
                        buf.push(Component::ParentDir);
                    }

                    break;
                }
            };

            match b_it.next() {
                Some(CurDir) => buf.push(std_to_c(a)?),
                Some(ParentDir) => {
                    return Err(RelativeToErrorKind::NonRelative.into());
                }
                root => {
                    if root.is_some() {
                        buf.push(Component::ParentDir);
                    }

                    for comp in b_it {
                        match comp {
                            ParentDir => {
                                if !buf.pop() {
                                    return Err(RelativeToErrorKind::NonRelative.into());
                                }
                            }
                            CurDir => (),
                            _ => buf.push(Component::ParentDir),
                        }
                    }

                    buf.push(std_to_c(a)?);

                    for c in a_it {
                        buf.push(std_to_c(c)?);
                    }

                    break;
                }
            }
        }

        Ok(buf)
    }
}

impl PathExt for PathBuf {
    #[inline]
    fn relative_to<P: AsRef<Path>>(&self, root: P) -> Result<RelativePathBuf, RelativeToError> {
        self.as_path().relative_to(root)
    }
}

// Prevent downstream implementations, so methods may be added without backwards breaking changes.
mod private {
    pub trait Sealed {}
}

impl private::Sealed for Path {}
impl private::Sealed for PathBuf {}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use crate::RelativeToError;

    use super::{PathExt, RelativeToErrorKind};
    use cfg_if::cfg_if;

    macro_rules! assert_diff_paths {
        ($path:expr, $base:expr, $expected:expr $(,)?) => {
            assert_eq!(
                PathBuf::from($path).relative_to(Path::new($base)),
                Result::<&str, RelativeToError>::map($expected, |s| s.into())
            );
        };
    }

    #[test]
    #[cfg(windows)]
    fn test_different_prefixes() {
        assert_diff_paths!(
            "C:/repo",
            "D:/repo",
            Err(RelativeToErrorKind::NonRelative.into()),
        );
        assert_diff_paths!("C:/repo", "C:/repo", Ok(""));
    }

    #[test]
    fn test_absolute() {
        fn abs(path: &str) -> String {
            // Absolute paths look different on Windows vs Unix.
            cfg_if! {
                if #[cfg(windows)] {
                    format!("C:\\{}", path)
                } else {
                    format!("/{}", path)
                }
            }
        }

        assert_diff_paths!(&abs("foo"), &abs("bar"), Ok("../foo"));
        assert_diff_paths!("foo", "bar", Ok("../foo"));
        assert_diff_paths!(
            &abs("foo"),
            "bar",
            Err(RelativeToErrorKind::NonRelative.into()),
        );
        assert_diff_paths!(
            "foo",
            &abs("bar"),
            Err(RelativeToErrorKind::NonRelative.into()),
        );
    }

    #[test]
    fn test_identity() {
        assert_diff_paths!(".", ".", Ok(""));
        assert_diff_paths!("../foo", "../foo", Ok(""));
        assert_diff_paths!("./foo", "./foo", Ok(""));
        assert_diff_paths!("/foo", "/foo", Ok(""));
        assert_diff_paths!("foo", "foo", Ok(""));

        assert_diff_paths!("../foo/bar/baz", "../foo/bar/baz", Ok(""));
        assert_diff_paths!("foo/bar/baz", "foo/bar/baz", Ok(""));
    }

    #[test]
    fn test_subset() {
        assert_diff_paths!("foo", "fo", Ok("../foo"));
        assert_diff_paths!("fo", "foo", Ok("../fo"));
    }

    #[test]
    fn test_empty() {
        assert_diff_paths!("", "", Ok(""));
        assert_diff_paths!("foo", "", Ok("foo"));
        assert_diff_paths!("", "foo", Ok(".."));
    }

    #[test]
    fn test_relative() {
        assert_diff_paths!("../foo", "../bar", Ok("../foo"));
        assert_diff_paths!("../foo", "../foo/bar/baz", Ok("../.."));
        assert_diff_paths!("../foo/bar/baz", "../foo", Ok("bar/baz"));

        assert_diff_paths!("foo/bar/baz", "foo", Ok("bar/baz"));
        assert_diff_paths!("foo/bar/baz", "foo/bar", Ok("baz"));
        assert_diff_paths!("foo/bar/baz", "foo/bar/baz", Ok(""));
        assert_diff_paths!("foo/bar/baz", "foo/bar/baz/", Ok(""));

        assert_diff_paths!("foo/bar/baz/", "foo", Ok("bar/baz"));
        assert_diff_paths!("foo/bar/baz/", "foo/bar", Ok("baz"));
        assert_diff_paths!("foo/bar/baz/", "foo/bar/baz", Ok(""));
        assert_diff_paths!("foo/bar/baz/", "foo/bar/baz/", Ok(""));

        assert_diff_paths!("foo/bar/baz", "foo/", Ok("bar/baz"));
        assert_diff_paths!("foo/bar/baz", "foo/bar/", Ok("baz"));
        assert_diff_paths!("foo/bar/baz", "foo/bar/baz", Ok(""));
    }

    #[test]
    fn test_current_directory() {
        assert_diff_paths!(".", "foo", Ok("../."));
        assert_diff_paths!("foo", ".", Ok("foo"));
        assert_diff_paths!("/foo", "/.", Ok("foo"));
    }

    #[test]
    fn assert_does_not_skip_parents() {
        assert_eq!(
            PathBuf::from("some/path").relative_to(PathBuf::from("some/foo/baz/path")),
            Ok("../../../path".into())
        );

        assert_eq!(
            PathBuf::from("some/path").relative_to(PathBuf::from("some/foo/bar/../baz/path")),
            Ok("../../../path".into())
        );

        // Parent directory name is unknown, so trying to make current directory relative to it is
        // impossible.
        assert_eq!(
            PathBuf::from(".").relative_to(PathBuf::from("a/../..")),
            Err(RelativeToErrorKind::NonRelative.into()),
        );
    }
}

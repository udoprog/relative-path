// Copyright 2012-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Taken from the pathdiff crate, which adapted the original rustc's path_relative_from
// https://github.com/Manishearth/pathdiff/blob/master/src/lib.rs
// https://github.com/rust-lang/rust/blob/e1d0de82cc40b666b88d4a6d2c9dcbc81d7ed27f/src/librustc_back/rpath.rs#L116-L158

use std::path::{self, Path, PathBuf};

use crate::{Component, FromPathError, FromPathErrorKind, RelativePathBuf};

/// Provides helper methods on Path and PathBuf to for creating RelativePath.
pub trait PathExt: private::Sealed {
    /// Make a relative path from a provided root directory path.
    ///
    /// This may not function correctly if either path includes a symlink.
    /// Resolve or discard symlink paths before making them relative.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::path::PathBuf;
    /// use relative_path::PathExt;
    ///
    /// let baz = PathBuf::from("/foo/bar/baz");
    /// let bar = PathBuf::from("/foo/bar");
    /// let quux = PathBuf::from("/foo/bar/quux");
    ///
    /// assert_eq!(bar.relative_to(&baz)?, "../");
    /// assert_eq!(baz.relative_to(&bar)?, "baz");
    /// assert_eq!(quux.relative_to(&baz)?, "../quux");
    /// assert_eq!(baz.relative_to(&quux)?, "../baz");
    /// assert_eq!(bar.relative_to(&quux)?, "../");
    ///
    /// assert_eq!(baz.as_path().relative_to(&bar)?, "baz");
    /// assert_eq!(baz.as_path().relative_to(bar.as_path())?, "baz");
    /// # Ok::<_, relative_path::FromPathError>(())
    /// ```
    fn relative_to<P: AsRef<Path>>(&self, root: P) -> Result<RelativePathBuf, FromPathError>;
}

impl PathExt for Path {
    fn relative_to<P: AsRef<Path>>(&self, root: P) -> Result<RelativePathBuf, FromPathError> {
        use path::Component as C;

        // Helper function to convert from a std::path::Component to a
        // relative_path::Component.
        fn std_to_c(c: C<'_>) -> Result<Component<'_>, FromPathError> {
            Ok(match c {
                C::CurDir => Component::CurDir,
                C::ParentDir => Component::ParentDir,
                C::Normal(n) => {
                    Component::Normal(n.to_str().ok_or_else(|| FromPathErrorKind::NonUtf8)?)
                }
                _ => return Err(FromPathErrorKind::NonRelative.into()),
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
                (Some(C::RootDir), Some(C::RootDir)) => (),
                (Some(C::Prefix(a)), Some(C::Prefix(b))) if a == b => (),
                (Some(C::Prefix(_) | C::RootDir), _) | (_, Some(C::Prefix(_) | C::RootDir)) => {
                    return Err(FromPathErrorKind::NonRelative.into());
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
                Some(C::CurDir) => buf.push(std_to_c(a)?),
                Some(C::ParentDir) => {
                    return Err(FromPathErrorKind::NonRelative.into());
                }
                root => {
                    if root.is_some() {
                        buf.push(Component::ParentDir);
                    }

                    for comp in b_it {
                        match comp {
                            C::ParentDir => {
                                if !buf.pop() {
                                    return Err(FromPathErrorKind::NonRelative.into());
                                }
                            }
                            C::CurDir => (),
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
    fn relative_to<P: AsRef<Path>>(&self, root: P) -> Result<RelativePathBuf, FromPathError> {
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

    use crate::{FromPathError, FromPathErrorKind};

    use super::PathExt;
    use cfg_if::cfg_if;

    macro_rules! assert_diff_paths {
        ($path:expr, $base:expr, $expected:expr $(,)?) => {
            assert_eq!(
                PathBuf::from($path).relative_to(Path::new($base)),
                Result::<&str, FromPathError>::map($expected, |s| s.into())
            );
        };
    }

    #[test]
    #[cfg(windows)]
    fn test_different_prefixes() {
        assert_diff_paths!(
            "C:/repo",
            "D:/repo",
            Err(FromPathErrorKind::NonRelative.into()),
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
            Err(FromPathErrorKind::NonRelative.into()),
        );
        assert_diff_paths!(
            "foo",
            &abs("bar"),
            Err(FromPathErrorKind::NonRelative.into()),
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
            Err(FromPathErrorKind::NonRelative.into()),
        );
    }
}

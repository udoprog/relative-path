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

use crate::{FromPathError, FromPathErrorKind, RelativePathBuf};
use std::path::*;

/// Provides helper methods on Path and PathBuf to for creating RelativePath.
pub trait PathExt: private::Sealed {
    /// Make a relative path from a provided root directory path.
    ///
    /// This may not function correctly if either path includes a symlink. Resolve or discard
    /// symlink paths before making them relative.
    ///
    /// ```rust
    /// use relative_path::PathExt;
    /// use std::path::*;
    ///
    /// let baz = PathBuf::from("/foo/bar/baz");
    /// let bar = PathBuf::from("/foo/bar");
    /// let quux = PathBuf::from("/foo/bar/quux");
    /// assert_eq!(bar.relative_to(&baz), Ok("../".into()));
    /// assert_eq!(baz.relative_to(&bar), Ok("baz".into()));
    /// assert_eq!(quux.relative_to(&baz), Ok("../quux".into()));
    /// assert_eq!(baz.relative_to(&quux), Ok("../baz".into()));
    /// assert_eq!(bar.relative_to(&quux), Ok("../".into()));
    ///
    /// assert_eq!(baz.as_path().relative_to(&bar), Ok("baz".into()));
    /// assert_eq!(baz.as_path().relative_to(bar.as_path()), Ok("baz".into()));
    /// ```
    fn relative_to(&self, root: impl AsRef<Path>) -> Result<RelativePathBuf, FromPathError>;
}

impl PathExt for Path {
    fn relative_to(&self, root: impl AsRef<Path>) -> Result<RelativePathBuf, FromPathError> {
        let root = root.as_ref();
        if self.is_absolute() != root.is_absolute() {
            Err(FromPathErrorKind::NonRelative.into())
        } else {
            let mut path_comps = self.components();
            let mut root_comps = root.components();
            let mut comps: Vec<Component> = vec![];
            loop {
                match (path_comps.next(), root_comps.next()) {
                    (None, None) => break,
                    (Some(a), None) => {
                        comps.push(a);
                        comps.extend(path_comps.by_ref());
                        break;
                    }
                    (None, _) => comps.push(Component::ParentDir),
                    (Some(a), Some(b)) if comps.is_empty() && a == b => (),
                    (Some(a), Some(b)) if b == Component::CurDir => comps.push(a),
                    (Some(_), Some(b)) if b == Component::ParentDir => {
                        return Err(FromPathErrorKind::NonRelative.into());
                    }
                    (Some(a), Some(_)) => {
                        comps.push(Component::ParentDir);
                        for comp in root_comps {
                            match comp {
                                Component::ParentDir => {
                                    comps.pop().ok_or(FromPathErrorKind::NonRelative)?;
                                }
                                Component::CurDir => (),
                                _ => comps.push(Component::ParentDir),
                            }
                        }
                        comps.push(a);
                        comps.extend(path_comps.by_ref());
                        break;
                    }
                }
            }

            comps
                .iter()
                .map(|c| {
                    c.as_os_str()
                        .to_str()
                        .ok_or_else(|| FromPathErrorKind::NonUtf8.into())
                })
                .collect()
        }
    }
}

impl PathExt for PathBuf {
    fn relative_to(&self, root: impl AsRef<Path>) -> Result<RelativePathBuf, FromPathError> {
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
    use std::path::PathBuf;

    use crate::{FromPathError, FromPathErrorKind};

    use super::PathExt;
    use cfg_if::cfg_if;

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

        assert_diff_paths(&abs("foo"), &abs("bar"), Ok("../foo"));
        assert_diff_paths("foo", "bar", Ok("../foo"));
        assert_diff_paths(
            &abs("foo"),
            "bar",
            Err(FromPathErrorKind::NonRelative.into()),
        );
        assert_diff_paths(
            "foo",
            &abs("bar"),
            Err(FromPathErrorKind::NonRelative.into()),
        );
    }

    #[test]
    fn test_identity() {
        assert_diff_paths(".", ".", Ok(""));
        assert_diff_paths("../foo", "../foo", Ok(""));
        assert_diff_paths("./foo", "./foo", Ok(""));
        assert_diff_paths("/foo", "/foo", Ok(""));
        assert_diff_paths("foo", "foo", Ok(""));

        assert_diff_paths("../foo/bar/baz", "../foo/bar/baz", Ok(""));
        assert_diff_paths("foo/bar/baz", "foo/bar/baz", Ok(""));
    }

    #[test]
    fn test_subset() {
        assert_diff_paths("foo", "fo", Ok("../foo"));
        assert_diff_paths("fo", "foo", Ok("../fo"));
    }

    #[test]
    fn test_empty() {
        assert_diff_paths("", "", Ok(""));
        assert_diff_paths("foo", "", Ok("foo"));
        assert_diff_paths("", "foo", Ok(".."));
    }

    #[test]
    fn test_relative() {
        assert_diff_paths("../foo", "../bar", Ok("../foo"));
        assert_diff_paths("../foo", "../foo/bar/baz", Ok("../.."));
        assert_diff_paths("../foo/bar/baz", "../foo", Ok("bar/baz"));

        assert_diff_paths("foo/bar/baz", "foo", Ok("bar/baz"));
        assert_diff_paths("foo/bar/baz", "foo/bar", Ok("baz"));
        assert_diff_paths("foo/bar/baz", "foo/bar/baz", Ok(""));
        assert_diff_paths("foo/bar/baz", "foo/bar/baz/", Ok(""));

        assert_diff_paths("foo/bar/baz/", "foo", Ok("bar/baz"));
        assert_diff_paths("foo/bar/baz/", "foo/bar", Ok("baz"));
        assert_diff_paths("foo/bar/baz/", "foo/bar/baz", Ok(""));
        assert_diff_paths("foo/bar/baz/", "foo/bar/baz/", Ok(""));

        assert_diff_paths("foo/bar/baz", "foo/", Ok("bar/baz"));
        assert_diff_paths("foo/bar/baz", "foo/bar/", Ok("baz"));
        assert_diff_paths("foo/bar/baz", "foo/bar/baz", Ok(""));
    }

    #[test]
    fn test_current_directory() {
        assert_diff_paths(".", "foo", Ok("../."));
        assert_diff_paths("foo", ".", Ok("foo"));
        assert_diff_paths("/foo", "/.", Ok("foo"));
    }

    fn assert_diff_paths(path: &str, base: &str, expected: Result<&str, FromPathError>) {
        assert_eq!(
            PathBuf::from(path).relative_to(PathBuf::from(base)),
            expected.map(|s| s.into())
        );
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

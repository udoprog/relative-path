// This file contains parts that are Copyright 2015 The Rust Project Developers, copied from:
// https://github.com/rust-lang/rust
// cb2a656cdfb6400ac0200c661267f91fabf237e2 src/libstd/path.rs

//! A platform-neutral relative path.
//!
//! This provide types which are analogous to `Path`, and `PathBuf` found in stdlib, with the
//! following characteristics:
//!
//! * The path separator is set to a fixed character (`/`), regardless of platform.
//! * Relative paths cannot represent a path in the filesystem, without first specifying what they
//!   are relative to through [`to_path`].
//!
//! When two relative paths are compared to each other, their exact component makeup is taken into
//! account:
//!
//! ```rust
//! use relative_path::RelativePath;
//!
//! assert!(RelativePath::new("foo/bar/../baz") != RelativePath::new("foo/baz"));
//! ```
//!
//! Using platform-specific path separators to construct relative paths is not supported.
//!
//! Path separators from other platforms are therefore treated as part of the component:
//!
//! ```rust
//! use relative_path::RelativePath;
//!
//! assert_ne!(RelativePath::new("foo/bar"), RelativePath::new("foo\\bar"));
//!
//! assert_eq!(1, RelativePath::new("foo\\bar").components().count());
//! assert_eq!(2, RelativePath::new("foo/bar").components().count());
//! ```
//!
//! To see if two logical paths are equivalent you can use [`normalize`]:
//!
//! ```rust
//! use relative_path::RelativePath;
//!
//! assert_eq!(
//!     RelativePath::new("foo/bar/../baz").normalize(),
//!     RelativePath::new("foo/baz").normalize(),
//! );
//! ```
//!
//! [`to_path`]: struct.RelativePath.html#method.to_path
//! [`normalize`]: struct.RelativePath.html#method.normalize
//! [`None`]: std::option::Option
//!
//! # Serde Support
//!
//! This library includes serde support that can be enabled with the `serde` feature.

use std::borrow::{Borrow, Cow};
use std::cmp;
use std::error;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem;
use std::ops::{self, Deref};
use std::path;
use std::str;

#[cfg(feature = "serde")]
extern crate serde;

const STEM_SEP: char = '.';
const CURRENT_STR: &str = ".";
const PARENT_STR: &str = "..";

const SEP: char = '/';

fn split_file_at_dot(input: &str) -> (Option<&str>, Option<&str>) {
    if input == PARENT_STR {
        return (Some(input), None);
    }

    let mut iter = input.rsplitn(2, STEM_SEP);

    let after = iter.next();
    let before = iter.next();

    if before == Some("") {
        (Some(input), None)
    } else {
        (before, after)
    }
}

// Iterate through `iter` while it matches `prefix`; return `None` if `prefix`
// is not a prefix of `iter`, otherwise return `Some(iter_after_prefix)` giving
// `iter` after having exhausted `prefix`.
fn iter_after<'a, 'b, I, J>(mut iter: I, mut prefix: J) -> Option<I>
where
    I: Iterator<Item = Component<'a>> + Clone,
    J: Iterator<Item = Component<'b>>,
{
    loop {
        let mut iter_next = iter.clone();
        match (iter_next.next(), prefix.next()) {
            (Some(ref x), Some(ref y)) if x == y => (),
            (Some(_), Some(_)) => return None,
            (Some(_), None) => return Some(iter),
            (None, None) => return Some(iter),
            (None, Some(_)) => return None,
        }
        iter = iter_next;
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Component<'a> {
    CurDir,
    ParentDir,
    Normal(&'a str),
}

impl<'a> Component<'a> {
    /// Extracts the underlying [`str`] slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use relative_path::{RelativePath, Component};
    ///
    /// let path = RelativePath::new("./tmp/../foo/bar.txt");
    /// let components: Vec<_> = path.components().map(Component::as_str).collect();
    /// assert_eq!(&components, &[".", "tmp", "..", "foo", "bar.txt"]);
    /// ```
    ///
    /// [`str`]: str
    pub fn as_str(self) -> &'a str {
        use self::Component::*;

        match self {
            CurDir => CURRENT_STR,
            ParentDir => PARENT_STR,
            Normal(name) => name,
        }
    }
}

/// Traverse the given components and apply to the provided stack.
///
/// This takes '.', and '..' into account. Where '.' doesn't change the stack, and '..' pops the
/// last item or further adds parent components.
#[inline(always)]
fn relative_traversal<'a, C>(stack: &mut Vec<&'a str>, components: C)
where
    C: IntoIterator<Item = Component<'a>>,
{
    use self::Component::*;

    for c in components {
        match c {
            CurDir => (),
            ParentDir => match stack.last().copied() {
                Some(PARENT_STR) | None => {
                    stack.push(PARENT_STR);
                }
                _ => {
                    stack.pop();
                }
            },
            Normal(name) => stack.push(name),
        }
    }
}

/// Iterator over all the components in a relative path.
#[derive(Clone)]
pub struct Components<'a> {
    source: &'a str,
}

impl<'a> Iterator for Components<'a> {
    type Item = Component<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.source = self.source.trim_start_matches(SEP);

        let slice = match self.source.find(SEP) {
            Some(i) => {
                let (slice, rest) = self.source.split_at(i);
                self.source = rest.trim_start_matches(SEP);
                slice
            }
            None => mem::replace(&mut self.source, ""),
        };

        match slice {
            "" => None,
            "." => Some(Component::CurDir),
            ".." => Some(Component::ParentDir),
            slice => Some(Component::Normal(slice)),
        }
    }
}

impl<'a> DoubleEndedIterator for Components<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.source = self.source.trim_end_matches(SEP);

        let slice = match self.source.rfind(SEP) {
            Some(i) => {
                let (rest, slice) = self.source.split_at(i + 1);
                self.source = rest.trim_end_matches(SEP);
                slice
            }
            None => mem::replace(&mut self.source, ""),
        };

        match slice {
            "" => None,
            "." => Some(Component::CurDir),
            ".." => Some(Component::ParentDir),
            slice => Some(Component::Normal(slice)),
        }
    }
}

impl<'a> Components<'a> {
    pub fn new(source: &'a str) -> Components<'a> {
        Self { source }
    }

    /// Extracts a slice corresponding to the portion of the path remaining for iteration.
    ///
    /// # Examples
    ///
    /// ```
    /// use relative_path::RelativePath;
    ///
    /// let mut components = RelativePath::new("tmp/foo/bar.txt").components();
    /// components.next();
    /// components.next();
    ///
    /// assert_eq!(RelativePath::new("bar.txt"), components.as_relative_path());
    /// ```
    pub fn as_relative_path(&self) -> &'a RelativePath {
        RelativePath::new(self.source)
    }
}

impl<'a> cmp::PartialEq for Components<'a> {
    fn eq(&self, other: &Components<'a>) -> bool {
        Iterator::eq(self.clone(), other.clone())
    }
}

/// An iterator over the [`Component`]s of a [`RelativePath`], as [`str`] slices.
///
/// This `struct` is created by the [`iter`] method on [`RelativePath`].
/// See its documentation for more.
///
/// [`Component`]: Component
/// [`iter`]: struct.RelativePath.html#method.iter
/// [`str`]: str
/// [`RelativePath`]: struct.RelativePath.html
#[derive(Clone)]
pub struct Iter<'a> {
    inner: Components<'a>,
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        self.inner.next().map(Component::as_str)
    }
}

impl<'a> DoubleEndedIterator for Iter<'a> {
    fn next_back(&mut self) -> Option<&'a str> {
        self.inner.next_back().map(Component::as_str)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum FromPathErrorKind {
    /// Non-relative component in path.
    NonRelative,
    /// Non-utf8 component in path.
    NonUtf8,
    /// Trying to convert a platform-specific path which uses a platform-specific separator.
    BadSeparator,
}

/// An error raised when attempting to convert a path using `RelativePathBuf::from_path`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FromPathError {
    kind: FromPathErrorKind,
}

impl FromPathError {
    /// Gets the underlying [FromPathErrorKind] that provides more details on
    /// what went wrong.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::path::Path;
    /// use relative_path::{FromPathErrorKind, RelativePathBuf};
    ///
    /// let result = RelativePathBuf::from_path(Path::new("/hello/world"));
    /// let e = result.unwrap_err();
    ///
    /// assert_eq!(FromPathErrorKind::NonRelative, e.kind());
    /// ```
    pub fn kind(&self) -> FromPathErrorKind {
        self.kind
    }
}

impl From<FromPathErrorKind> for FromPathError {
    fn from(value: FromPathErrorKind) -> Self {
        Self { kind: value }
    }
}

impl fmt::Display for FromPathError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self.kind {
            FromPathErrorKind::NonRelative => "path contains non-relative component".fmt(fmt),
            FromPathErrorKind::NonUtf8 => "path contains non-utf8 component".fmt(fmt),
            FromPathErrorKind::BadSeparator => {
                "path contains platform-specific path separator".fmt(fmt)
            }
        }
    }
}

impl error::Error for FromPathError {}

/// An owned, mutable relative path.
///
/// This type provides methods to manipulate relative path objects.
#[derive(Clone)]
pub struct RelativePathBuf {
    inner: String,
}

impl RelativePathBuf {
    /// Create a new relative path buffer.
    pub fn new() -> RelativePathBuf {
        RelativePathBuf {
            inner: String::new(),
        }
    }

    /// Try to convert a [`Path`] to a `RelativePathBuf`.
    ///
    /// [`Path`]: std::path::Path
    ///
    /// # Examples
    ///
    /// ```rust
    /// use relative_path::{RelativePath, RelativePathBuf, FromPathErrorKind};
    /// use std::path::Path;
    /// use std::ffi::OsStr;
    ///
    /// assert_eq!(
    ///     Ok(RelativePath::new("foo/bar").to_owned()),
    ///     RelativePathBuf::from_path(Path::new("foo/bar"))
    /// );
    /// ```
    pub fn from_path<P: AsRef<path::Path>>(path: P) -> Result<RelativePathBuf, FromPathError> {
        use std::path::Component::*;

        let mut buffer = RelativePathBuf::new();

        for c in path.as_ref().components() {
            match c {
                Prefix(_) | RootDir => return Err(FromPathErrorKind::NonRelative.into()),
                CurDir => continue,
                ParentDir => buffer.push(".."),
                Normal(s) => buffer.push(s.to_str().ok_or(FromPathErrorKind::NonUtf8)?),
            }
        }

        Ok(buffer)
    }

    /// Extends `self` with `path`.
    ///
    /// If `path` is absolute, it replaces the current path.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use relative_path::{RelativePathBuf, RelativePath};
    ///
    /// let mut path = RelativePathBuf::new();
    /// path.push("foo");
    /// path.push("bar");
    ///
    /// assert_eq!("foo/bar", path);
    /// ```
    pub fn push<P: AsRef<RelativePath>>(&mut self, path: P) {
        let other = path.as_ref();

        let other = if other.starts_with_sep() {
            &other.inner[1..]
        } else {
            &other.inner[..]
        };

        if !self.inner.is_empty() && !self.ends_with_sep() {
            self.inner.push(SEP);
        }

        self.inner.push_str(other)
    }

    /// Updates [`self.file_name`] to `file_name`.
    ///
    /// If [`self.file_name`] was [`None`], this is equivalent to pushing
    /// `file_name`.
    ///
    /// Otherwise it is equivalent to calling [`pop`] and then pushing
    /// `file_name`. The new path will be a sibling of the original path.
    /// (That is, it will have the same parent.)
    ///
    /// [`self.file_name`]: struct.RelativePathBuf.html#method.file_name
    /// [`pop`]: struct.RelativePathBuf.html#method.pop
    /// [`None`]: std::option::Option
    ///
    /// # Examples
    ///
    /// ```
    /// use relative_path::RelativePathBuf;
    ///
    /// let mut buf = RelativePathBuf::from("");
    /// assert!(buf.file_name() == None);
    /// buf.set_file_name("bar");
    /// assert_eq!(RelativePathBuf::from("bar"), buf);
    ///
    /// assert!(buf.file_name().is_some());
    /// buf.set_file_name("baz.txt");
    /// assert_eq!(RelativePathBuf::from("baz.txt"), buf);
    ///
    /// buf.push("bar");
    /// assert!(buf.file_name().is_some());
    /// buf.set_file_name("bar.txt");
    /// assert_eq!(RelativePathBuf::from("baz.txt/bar.txt"), buf);
    /// ```
    pub fn set_file_name<S: AsRef<str>>(&mut self, file_name: S) {
        let file_name = file_name.as_ref();

        if self.file_name().is_some() && !self.pop() {
            self.inner = file_name.to_string();
            return;
        }

        self.push(file_name);
    }

    /// Updates [`self.extension`] to `extension`.
    ///
    /// Returns `false` and does nothing if [`self.file_name`] is [`None`],
    /// returns `true` and updates the extension otherwise.
    ///
    /// If [`self.extension`] is [`None`], the extension is added; otherwise
    /// it is replaced.
    ///
    /// [`self.file_name`]: struct.RelativePathBuf.html#method.file_name
    /// [`self.extension`]: struct.RelativePathBuf.html#method.extension
    /// [`None`]: std::option::Option
    ///
    /// # Examples
    ///
    /// ```
    /// use relative_path::{RelativePath, RelativePathBuf};
    ///
    /// let mut p = RelativePathBuf::from("feel/the");
    ///
    /// p.set_extension("force");
    /// assert_eq!(RelativePath::new("feel/the.force"), p);
    ///
    /// p.set_extension("dark_side");
    /// assert_eq!(RelativePath::new("feel/the.dark_side"), p);
    ///
    /// assert!(p.pop());
    /// p.set_extension("nothing");
    /// assert_eq!(RelativePath::new("feel.nothing"), p);
    /// ```
    pub fn set_extension<S: AsRef<str>>(&mut self, extension: S) -> bool {
        if self.file_name().is_none() {
            return false;
        }

        let mut stem = match self.file_stem() {
            Some(stem) => stem.to_string(),
            None => String::new(),
        };

        let extension = extension.as_ref();

        if !extension.is_empty() {
            stem.push(STEM_SEP);
            stem += extension;
        }

        self.set_file_name(&stem);
        true
    }

    /// Truncates `self` to [`self.parent`].
    ///
    /// [`self.parent`]: RelativePathBuf::parent
    /// [`None`]: std::option::Option
    ///
    /// # Examples
    ///
    /// ```
    /// use relative_path::{RelativePath, RelativePathBuf};
    ///
    /// let mut p = RelativePathBuf::from("test/test.rs");
    ///
    /// assert_eq!(true, p.pop());
    /// assert_eq!(RelativePath::new("test"), p);
    /// assert_eq!(true, p.pop());
    /// assert_eq!(RelativePath::new(""), p);
    /// assert_eq!(false, p.pop());
    /// assert_eq!(RelativePath::new(""), p);
    /// ```
    pub fn pop(&mut self) -> bool {
        match self.parent().map(|p| p.as_u8_slice().len()) {
            Some(len) => {
                self.inner.truncate(len);
                true
            }
            None => false,
        }
    }

    /// Coerce to a [`RelativePath`] slice.
    ///
    /// [`RelativePath`]: RelativePath
    pub fn as_relative_path(&self) -> &RelativePath {
        self
    }
}

impl Default for RelativePathBuf {
    fn default() -> Self {
        RelativePathBuf::new()
    }
}

impl<'a> From<&'a RelativePath> for Cow<'a, RelativePath> {
    #[inline]
    fn from(s: &'a RelativePath) -> Cow<'a, RelativePath> {
        Cow::Borrowed(s)
    }
}

impl<'a> From<RelativePathBuf> for Cow<'a, RelativePath> {
    #[inline]
    fn from(s: RelativePathBuf) -> Cow<'a, RelativePath> {
        Cow::Owned(s)
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

impl Borrow<RelativePath> for RelativePathBuf {
    fn borrow(&self) -> &RelativePath {
        self.deref()
    }
}

impl<'a, T: ?Sized + AsRef<str>> From<&'a T> for RelativePathBuf {
    fn from(path: &'a T) -> RelativePathBuf {
        RelativePathBuf {
            inner: path.as_ref().to_owned(),
        }
    }
}

impl From<String> for RelativePathBuf {
    fn from(path: String) -> RelativePathBuf {
        RelativePathBuf { inner: path }
    }
}

impl ops::Deref for RelativePathBuf {
    type Target = RelativePath;

    fn deref(&self) -> &RelativePath {
        RelativePath::new(&self.inner)
    }
}

impl cmp::PartialEq for RelativePathBuf {
    fn eq(&self, other: &RelativePathBuf) -> bool {
        self.components() == other.components()
    }
}

impl cmp::Eq for RelativePathBuf {}

impl cmp::PartialOrd for RelativePathBuf {
    fn partial_cmp(&self, other: &RelativePathBuf) -> Option<cmp::Ordering> {
        self.components().partial_cmp(other.components())
    }
}

impl cmp::Ord for RelativePathBuf {
    fn cmp(&self, other: &RelativePathBuf) -> cmp::Ordering {
        self.components().cmp(other.components())
    }
}

impl Hash for RelativePathBuf {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.as_relative_path().hash(h)
    }
}

/// A borrowed, immutable relative path.
#[repr(transparent)]
pub struct RelativePath {
    inner: str,
}

/// An error returned from [`RelativePath::strip_prefix`][`strip_prefix`] if the prefix
/// was not found.
///
/// This `struct` is created by the [`strip_prefix`] method on [`RelativePath`].
/// See its documentation for more.
///
/// [`strip_prefix`]: struct.RelativePath.html#method.strip_prefix
/// [`RelativePath`]: RelativePath
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StripPrefixError(());

impl RelativePath {
    /// Directly wraps a string slice as a `RelativePath` slice.
    pub fn new<S: AsRef<str> + ?Sized>(s: &S) -> &RelativePath {
        unsafe { &*(s.as_ref() as *const str as *const RelativePath) }
    }

    /// Try to convert a [`Path`] to a `RelativePath` without allocating a buffer.
    ///
    /// This requires the Path to be a legal, platform-neutral relative path.
    ///
    /// [`Path`]: std::path::Path
    ///
    /// # Examples
    ///
    /// ```rust
    /// use relative_path::{RelativePath, FromPathErrorKind};
    /// use std::path::Path;
    /// use std::ffi::OsStr;
    ///
    /// assert_eq!(
    ///     Ok(RelativePath::new("foo/bar")),
    ///     RelativePath::from_path("foo/bar")
    /// );
    /// ```
    pub fn from_path<P: ?Sized + AsRef<path::Path>>(
        path: &P,
    ) -> Result<&RelativePath, FromPathError> {
        use std::path::Component::*;

        let other = path.as_ref();

        let s = match other.to_str() {
            Some(s) => s,
            None => return Err(FromPathErrorKind::NonUtf8.into()),
        };

        let rel = RelativePath::new(s);

        // check that the component compositions are equal.
        for (a, b) in other.components().zip(rel.components()) {
            match (a, b) {
                (Prefix(_), _) | (RootDir, _) => return Err(FromPathErrorKind::NonRelative.into()),
                (CurDir, Component::CurDir) => continue,
                (ParentDir, Component::ParentDir) => continue,
                (Normal(a), Component::Normal(b)) if a == b => continue,
                _ => return Err(FromPathErrorKind::BadSeparator.into()),
            }
        }

        Ok(rel)
    }

    // The following (private!) function reveals the byte encoding used for str.
    fn as_u8_slice(&self) -> &[u8] {
        self.inner.as_bytes()
    }

    /// Yields the underlying `str` slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use relative_path::RelativePath;
    ///
    /// assert_eq!(RelativePath::new("foo.txt").as_str(), "foo.txt");
    /// ```
    pub fn as_str(&self) -> &str {
        &self.inner
    }

    /// Returns an object that implements [`Display`].
    ///
    /// # Examples
    ///
    /// ```
    /// use relative_path::RelativePath;
    ///
    /// let path = RelativePath::new("tmp/foo.rs");
    ///
    /// println!("{}", path.display());
    /// ```
    #[deprecated(note = "RelativePath implements std::fmt::Display directly")]
    pub fn display(&self) -> Display {
        Display { path: self }
    }

    /// Creates an owned [`RelativePathBuf`] with path adjoined to self.
    ///
    /// [`RelativePathBuf`]: RelativePathBuf
    ///
    /// # Examples
    ///
    /// ```rust
    /// use relative_path::RelativePath;
    ///
    /// let path = RelativePath::new("foo/bar");
    /// assert_eq!("foo/bar/baz", path.join("baz"));
    /// ```
    pub fn join<P: AsRef<RelativePath>>(&self, path: P) -> RelativePathBuf {
        let mut out = self.to_relative_path_buf();
        out.push(path);
        out
    }

    /// Iterate over all components in this relative path.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use relative_path::{Component, RelativePath};
    ///
    /// let path = RelativePath::new("foo/bar/baz");
    /// let mut it = path.components();
    ///
    /// assert_eq!(Some(Component::Normal("foo")), it.next());
    /// assert_eq!(Some(Component::Normal("bar")), it.next());
    /// assert_eq!(Some(Component::Normal("baz")), it.next());
    /// assert_eq!(None, it.next());
    /// ```
    pub fn components(&self) -> Components {
        Components::new(&self.inner)
    }

    /// Produces an iterator over the path's components viewed as [`str`]
    /// slices.
    ///
    /// For more information about the particulars of how the path is separated
    /// into components, see [`components`].
    ///
    /// [`components`]: #method.components
    /// [`str`]: str
    ///
    /// # Examples
    ///
    /// ```
    /// use relative_path::RelativePath;
    ///
    /// let mut it = RelativePath::new("/tmp/foo.txt").iter();
    /// assert_eq!(it.next(), Some("tmp"));
    /// assert_eq!(it.next(), Some("foo.txt"));
    /// assert_eq!(it.next(), None)
    /// ```
    pub fn iter(&self) -> Iter {
        Iter {
            inner: self.components(),
        }
    }

    /// Convert to an owned [`RelativePathBuf`].
    ///
    /// [`RelativePathBuf`]: RelativePathBuf
    pub fn to_relative_path_buf(&self) -> RelativePathBuf {
        RelativePathBuf::from(self.inner.to_string())
    }

    /// Build an owned `PathBuf` relative to `path` for the current relative path.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use relative_path::RelativePath;
    /// use std::path::Path;
    ///
    /// let path = RelativePath::new("foo/bar").to_path(Path::new("."));
    /// assert_eq!(Path::new("./foo/bar"), path);
    /// ```
    pub fn to_path<P: AsRef<path::Path>>(&self, relative_to: P) -> path::PathBuf {
        let mut p = relative_to.as_ref().to_path_buf();
        p.extend(self.components().map(|c| c.as_str()));
        p
    }

    /// Returns a relative path, without its final component if there is one.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use relative_path::RelativePath;
    ///
    /// assert_eq!(Some(RelativePath::new("foo")), RelativePath::new("foo/bar").parent());
    /// assert_eq!(Some(RelativePath::new("")), RelativePath::new("foo").parent());
    /// assert_eq!(None, RelativePath::new("").parent());
    /// ```
    pub fn parent(&self) -> Option<&RelativePath> {
        use self::Component::*;

        if self.inner.is_empty() {
            return None;
        }

        let mut it = self.components();
        while let Some(CurDir) = it.next_back() {}
        Some(it.as_relative_path())
    }

    /// Returns the final component of the `RelativePath`, if there is one.
    ///
    /// If the path is a normal file, this is the file name. If it's the path of a directory, this
    /// is the directory name.
    ///
    /// Returns [`None`] If the path terminates in `..`.
    ///
    /// [`None`]: std::option::Option
    ///
    /// # Examples
    ///
    /// ```
    /// use relative_path::RelativePath;
    ///
    /// assert_eq!(Some("bin"), RelativePath::new("usr/bin/").file_name());
    /// assert_eq!(Some("foo.txt"), RelativePath::new("tmp/foo.txt").file_name());
    /// assert_eq!(Some("foo.txt"), RelativePath::new("tmp/foo.txt/").file_name());
    /// assert_eq!(Some("foo.txt"), RelativePath::new("foo.txt/.").file_name());
    /// assert_eq!(Some("foo.txt"), RelativePath::new("foo.txt/.//").file_name());
    /// assert_eq!(None, RelativePath::new("foo.txt/..").file_name());
    /// assert_eq!(None, RelativePath::new("/").file_name());
    /// ```
    pub fn file_name(&self) -> Option<&str> {
        use self::Component::*;

        let mut it = self.components();

        while let Some(c) = it.next_back() {
            return match c {
                CurDir => continue,
                Normal(name) => Some(name),
                _ => None,
            };
        }

        None
    }

    /// Returns a relative path that, when joined onto `base`, yields `self`.
    ///
    /// # Errors
    ///
    /// If `base` is not a prefix of `self` (i.e. [`starts_with`]
    /// returns `false`), returns [`Err`].
    ///
    /// [`starts_with`]: #method.starts_with
    /// [`Err`]: std::result::Result
    ///
    /// # Examples
    ///
    /// ```
    /// use relative_path::RelativePath;
    ///
    /// let path = RelativePath::new("test/haha/foo.txt");
    ///
    /// assert_eq!(path.strip_prefix("test"), Ok(RelativePath::new("haha/foo.txt")));
    /// assert_eq!(path.strip_prefix("test").is_ok(), true);
    /// assert_eq!(path.strip_prefix("haha").is_ok(), false);
    /// ```
    pub fn strip_prefix<P: AsRef<RelativePath>>(
        &self,
        base: P,
    ) -> Result<&RelativePath, StripPrefixError> {
        iter_after(self.components(), base.as_ref().components())
            .map(|c| c.as_relative_path())
            .ok_or(StripPrefixError(()))
    }

    /// Determines whether `base` is a prefix of `self`.
    ///
    /// Only considers whole path components to match.
    ///
    /// # Examples
    ///
    /// ```
    /// use relative_path::RelativePath;
    ///
    /// let path = RelativePath::new("etc/passwd");
    ///
    /// assert!(path.starts_with("etc"));
    ///
    /// assert!(!path.starts_with("e"));
    /// ```
    pub fn starts_with<P: AsRef<RelativePath>>(&self, base: P) -> bool {
        iter_after(self.components(), base.as_ref().components()).is_some()
    }

    /// Determines whether `child` is a suffix of `self`.
    ///
    /// Only considers whole path components to match.
    ///
    /// # Examples
    ///
    /// ```
    /// use relative_path::RelativePath;
    ///
    /// let path = RelativePath::new("etc/passwd");
    ///
    /// assert!(path.ends_with("passwd"));
    /// ```
    pub fn ends_with<P: AsRef<RelativePath>>(&self, child: P) -> bool {
        iter_after(self.components().rev(), child.as_ref().components().rev()).is_some()
    }

    /// Creates an owned [`RelativePathBuf`] like `self` but with the given file name.
    ///
    /// See [`RelativePathBuf::set_file_name`] for more details.
    ///
    /// [`RelativePathBuf`]: RelativePathBuf
    /// [`RelativePathBuf::set_file_name`]: struct.RelativePathBuf.html#method.set_file_name
    ///
    /// # Examples
    ///
    /// ```
    /// use relative_path::{RelativePath, RelativePathBuf};
    ///
    /// let path = RelativePath::new("tmp/foo.txt");
    /// assert_eq!(path.with_file_name("bar.txt"), RelativePathBuf::from("tmp/bar.txt"));
    ///
    /// let path = RelativePath::new("tmp");
    /// assert_eq!(path.with_file_name("var"), RelativePathBuf::from("var"));
    /// ```
    pub fn with_file_name<S: AsRef<str>>(&self, file_name: S) -> RelativePathBuf {
        let mut buf = self.to_relative_path_buf();
        buf.set_file_name(file_name);
        buf
    }

    /// Extracts the stem (non-extension) portion of [`self.file_name`].
    ///
    /// [`self.file_name`]: struct.RelativePath.html#method.file_name
    ///
    /// The stem is:
    ///
    /// * [`None`], if there is no file name;
    /// * The entire file name if there is no embedded `.`;
    /// * The entire file name if the file name begins with `.` and has no other `.`s within;
    /// * Otherwise, the portion of the file name before the final `.`
    ///
    /// [`None`]: std::option::Option
    ///
    /// # Examples
    ///
    /// ```
    /// use relative_path::RelativePath;
    ///
    /// let path = RelativePath::new("foo.rs");
    ///
    /// assert_eq!("foo", path.file_stem().unwrap());
    /// ```
    pub fn file_stem(&self) -> Option<&str> {
        self.file_name()
            .map(split_file_at_dot)
            .and_then(|(before, after)| before.or(after))
    }

    /// Extracts the extension of [`self.file_name`], if possible.
    ///
    /// The extension is:
    ///
    /// * [`None`], if there is no file name;
    /// * [`None`], if there is no embedded `.`;
    /// * [`None`], if the file name begins with `.` and has no other `.`s within;
    /// * Otherwise, the portion of the file name after the final `.`
    ///
    /// [`self.file_name`]: struct.RelativePath.html#method.file_name
    /// [`None`]: std::option::Option
    ///
    /// # Examples
    ///
    /// ```
    /// use relative_path::RelativePath;
    ///
    /// assert_eq!(Some("rs"), RelativePath::new("foo.rs").extension());
    /// assert_eq!(None, RelativePath::new(".rs").extension());
    /// assert_eq!(Some("rs"), RelativePath::new("foo.rs/.").extension());
    /// ```
    pub fn extension(&self) -> Option<&str> {
        self.file_name()
            .map(split_file_at_dot)
            .and_then(|(before, after)| before.and(after))
    }

    /// Creates an owned [`RelativePathBuf`] like `self` but with the given extension.
    ///
    /// See [`RelativePathBuf::set_extension`] for more details.
    ///
    /// [`RelativePathBuf`]: RelativePathBuf
    /// [`RelativePathBuf::set_extension`]: struct.RelativePathBuf.html#method.set_extension
    ///
    /// # Examples
    ///
    /// ```
    /// use relative_path::{RelativePath, RelativePathBuf};
    ///
    /// let path = RelativePath::new("foo.rs");
    /// assert_eq!(path.with_extension("txt"), RelativePathBuf::from("foo.txt"));
    /// ```
    pub fn with_extension<S: AsRef<str>>(&self, extension: S) -> RelativePathBuf {
        let mut buf = self.to_relative_path_buf();
        buf.set_extension(extension);
        buf
    }

    /// Build an owned `RelativePathBuf`, joined with the given path and normalized.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use relative_path::RelativePath;
    ///
    /// assert_eq!(
    ///     RelativePath::new("foo/baz.txt"),
    ///     RelativePath::new("foo/bar").join_normalized("../baz.txt").as_relative_path()
    /// );
    ///
    /// assert_eq!(
    ///     RelativePath::new("../foo/baz.txt"),
    ///     RelativePath::new("../foo/bar").join_normalized("../baz.txt").as_relative_path()
    /// );
    /// ```
    pub fn join_normalized<P: AsRef<RelativePath>>(&self, path: P) -> RelativePathBuf {
        let mut stack = Vec::new();
        relative_traversal(&mut stack, self.components());
        relative_traversal(&mut stack, path.as_ref().components());
        RelativePathBuf::from(stack.join("/"))
    }

    /// Return an owned `RelativePathBuf`, with all non-normal components moved to the beginning of
    /// the path.
    ///
    /// This permits for a normalized representation of different relative components.
    ///
    /// Normalization is a _destructive_ operation if the path references an actual filesystem
    /// path.
    /// An example of this is symlinks under unix, a path like `foo/../bar` might reference a
    /// different location other than `./bar`.
    ///
    /// Normalization is a logical operation that is only valid if the relative path is part of
    /// some context which doesn't have semantics that causes it to break, like symbolic links.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use relative_path::RelativePath;
    ///
    /// assert_eq!(
    ///     RelativePath::new("../foo/baz.txt"),
    ///     RelativePath::new("../foo/./bar/../baz.txt").normalize().as_relative_path()
    /// );
    /// ```
    pub fn normalize(&self) -> RelativePathBuf {
        let mut stack = Vec::new();
        relative_traversal(&mut stack, self.components());
        RelativePathBuf::from(stack.join("/"))
    }

    /// Constructs a relative path from the current path, to `path`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use relative_path::RelativePath;
    ///
    /// assert_eq!(
    ///     "../../e/f",
    ///     RelativePath::new("a/b/c/d").relative(RelativePath::new("a/b/e/f"))
    /// );
    ///
    /// assert_eq!(
    ///     "../bbb",
    ///     RelativePath::new("a/../aaa").relative(RelativePath::new("b/../bbb"))
    /// );
    ///
    /// let p = RelativePath::new("git/relative-path");
    /// let r = RelativePath::new("git");
    /// assert_eq!("relative-path", r.relative(p));
    /// assert_eq!("..", p.relative(r));
    ///
    /// let p = RelativePath::new("../../git/relative-path");
    /// let r = RelativePath::new("git");
    /// assert_eq!("../../../git/relative-path", r.relative(p));
    /// assert_eq!("", p.relative(r));
    ///
    /// let a = RelativePath::new("foo/bar/bap/foo.h");
    /// let b = RelativePath::new("../arch/foo.h");
    /// assert_eq!("../../../../../arch/foo.h", a.relative(b));
    /// assert_eq!("", b.relative(a));
    /// ```
    pub fn relative<P: AsRef<RelativePath>>(&self, path: P) -> RelativePathBuf {
        let mut from = Vec::new();
        let mut to = Vec::new();

        relative_traversal(&mut from, self.components());
        relative_traversal(&mut to, path.as_ref().components());

        // Special case: The path we are traversing from can't contain unnamed
        // components. A relative path might be any path, like `/`, or
        // `/foo/bar/baz`, and these components cannot be named in the relative
        // traversal.
        //
        // Also note that `relative_traversal` guarantees that all ParentDir
        // components are at the head of the stack.
        if !from.is_empty() && from[0] == PARENT_STR {
            return RelativePathBuf::new();
        }

        let mut from = from.into_iter();
        let mut to = to.into_iter();

        // keep track of the last component tracked in to, since we need to
        // append it after we've identified common components.
        let tail;

        let mut buffer = RelativePathBuf::new();

        // strip common prefixes
        loop {
            match (from.next(), to.next()) {
                (Some(from), Some(to)) if from == to => continue,
                (from, to) => {
                    if from.is_some() {
                        buffer.push(PARENT_STR);
                    }

                    tail = to;
                    break;
                }
            }
        }

        for c in from.map(|_| PARENT_STR).chain(tail).chain(to) {
            buffer.push(c);
        }

        buffer
    }

    /// Check if path starts with a path separator.
    fn starts_with_sep(&self) -> bool {
        self.inner.starts_with(SEP)
    }

    /// Check if path ends with a path separator.
    fn ends_with_sep(&self) -> bool {
        self.inner.ends_with(SEP)
    }
}

impl ToOwned for RelativePath {
    type Owned = RelativePathBuf;

    fn to_owned(&self) -> RelativePathBuf {
        self.to_relative_path_buf()
    }
}

impl fmt::Debug for RelativePath {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{:?}", &self.inner)
    }
}

impl AsRef<str> for RelativePathBuf {
    fn as_ref(&self) -> &str {
        &self.inner
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

impl AsRef<RelativePath> for RelativePath {
    fn as_ref(&self) -> &RelativePath {
        self
    }
}

impl cmp::PartialEq for RelativePath {
    fn eq(&self, other: &RelativePath) -> bool {
        self.components() == other.components()
    }
}

impl cmp::Eq for RelativePath {}

impl cmp::PartialOrd for RelativePath {
    fn partial_cmp(&self, other: &RelativePath) -> Option<cmp::Ordering> {
        self.components().partial_cmp(other.components())
    }
}

impl cmp::Ord for RelativePath {
    fn cmp(&self, other: &RelativePath) -> cmp::Ordering {
        self.components().cmp(other.components())
    }
}

impl Hash for RelativePath {
    fn hash<H: Hasher>(&self, h: &mut H) {
        for c in self.components() {
            c.hash(h);
        }
    }
}

impl fmt::Display for RelativePath {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.inner, f)
    }
}

impl fmt::Display for RelativePathBuf {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.inner, f)
    }
}

/// Helper struct for printing relative paths.
///
/// This is not strictly necessary in the same sense as it is for [`std::path::Display`], because
/// relative paths are guaranteed to be valid unicode. But the behavior is preserved to simplify
/// the transition between [`std::path::Path`] and [`RelativePath`].
///
/// [`std::path::Display`]: std::path::Display
/// [`RelativePath`]: RelativePath
pub struct Display<'a> {
    path: &'a RelativePath,
}

impl<'a> fmt::Debug for Display<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.path, f)
    }
}

impl<'a> fmt::Display for Display<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.path, f)
    }
}

#[cfg(feature = "serde")]
impl serde::ser::Serialize for RelativePathBuf {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::ser::Serializer,
    {
        serializer.serialize_str(&self.inner)
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::de::Deserialize<'de> for RelativePathBuf {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::de::Deserializer<'de>,
    {
        struct RelativePathBufVisitor;

        impl<'de> serde::de::Visitor<'de> for RelativePathBufVisitor {
            type Value = RelativePathBuf;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("a relative path")
            }

            fn visit_string<E>(self, input: String) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(RelativePathBuf::from(input))
            }

            fn visit_str<E>(self, input: &str) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(RelativePathBuf::from(input.to_string()))
            }
        }

        deserializer.deserialize_any(RelativePathBufVisitor)
    }
}

#[cfg(feature = "serde")]
impl serde::ser::Serialize for RelativePath {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::ser::Serializer,
    {
        serializer.serialize_str(&self.inner)
    }
}

macro_rules! impl_cmp {
    ($lhs:ty, $rhs:ty) => {
        impl<'a, 'b> PartialEq<$rhs> for $lhs {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool {
                <RelativePath as PartialEq>::eq(self, other)
            }
        }

        impl<'a, 'b> PartialEq<$lhs> for $rhs {
            #[inline]
            fn eq(&self, other: &$lhs) -> bool {
                <RelativePath as PartialEq>::eq(self, other)
            }
        }

        impl<'a, 'b> PartialOrd<$rhs> for $lhs {
            #[inline]
            fn partial_cmp(&self, other: &$rhs) -> Option<cmp::Ordering> {
                <RelativePath as PartialOrd>::partial_cmp(self, other)
            }
        }

        impl<'a, 'b> PartialOrd<$lhs> for $rhs {
            #[inline]
            fn partial_cmp(&self, other: &$lhs) -> Option<cmp::Ordering> {
                <RelativePath as PartialOrd>::partial_cmp(self, other)
            }
        }
    };
}

impl_cmp!(RelativePathBuf, RelativePath);
impl_cmp!(RelativePathBuf, &'a RelativePath);
impl_cmp!(Cow<'a, RelativePath>, RelativePath);
impl_cmp!(Cow<'a, RelativePath>, &'b RelativePath);
impl_cmp!(Cow<'a, RelativePath>, RelativePathBuf);

macro_rules! impl_cmp_str {
    ($lhs:ty, $rhs:ty) => {
        impl<'a, 'b> PartialEq<$rhs> for $lhs {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool {
                <RelativePath as PartialEq>::eq(self, other.as_ref())
            }
        }

        impl<'a, 'b> PartialEq<$lhs> for $rhs {
            #[inline]
            fn eq(&self, other: &$lhs) -> bool {
                <RelativePath as PartialEq>::eq(self.as_ref(), other)
            }
        }

        impl<'a, 'b> PartialOrd<$rhs> for $lhs {
            #[inline]
            fn partial_cmp(&self, other: &$rhs) -> Option<cmp::Ordering> {
                <RelativePath as PartialOrd>::partial_cmp(self, other.as_ref())
            }
        }

        impl<'a, 'b> PartialOrd<$lhs> for $rhs {
            #[inline]
            fn partial_cmp(&self, other: &$lhs) -> Option<cmp::Ordering> {
                <RelativePath as PartialOrd>::partial_cmp(self.as_ref(), other)
            }
        }
    };
}

impl_cmp_str!(RelativePathBuf, str);
impl_cmp_str!(RelativePathBuf, &'a str);
impl_cmp_str!(RelativePathBuf, String);
impl_cmp_str!(RelativePath, str);
impl_cmp_str!(RelativePath, &'a str);
impl_cmp_str!(RelativePath, String);
impl_cmp_str!(&'a RelativePath, str);
impl_cmp_str!(&'a RelativePath, String);

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    macro_rules! t(
        ($path:expr, iter: $iter:expr) => (
            {
                let path = RelativePath::new($path);

                // Forward iteration
                let comps = path.iter().map(str::to_string).collect::<Vec<String>>();
                let exp: &[&str] = &$iter;
                let exps = exp.iter().map(|s| s.to_string()).collect::<Vec<String>>();
                assert!(comps == exps, "iter: Expected {:?}, found {:?}",
                        exps, comps);

                // Reverse iteration
                let comps = RelativePath::new($path).iter().rev().map(str::to_string)
                    .collect::<Vec<String>>();
                let exps = exps.into_iter().rev().collect::<Vec<String>>();
                assert!(comps == exps, "iter().rev(): Expected {:?}, found {:?}",
                        exps, comps);
            }
        );

        ($path:expr, parent: $parent:expr, file_name: $file:expr) => (
            {
                let path = RelativePath::new($path);

                let parent = path.parent().map(|p| p.as_str());
                let exp_parent: Option<&str> = $parent;
                assert!(parent == exp_parent, "parent: Expected {:?}, found {:?}",
                        exp_parent, parent);

                let file = path.file_name();
                let exp_file: Option<&str> = $file;
                assert!(file == exp_file, "file_name: Expected {:?}, found {:?}",
                        exp_file, file);
            }
        );

        ($path:expr, file_stem: $file_stem:expr, extension: $extension:expr) => (
            {
                let path = RelativePath::new($path);

                let stem = path.file_stem();
                let exp_stem: Option<&str> = $file_stem;
                assert!(stem == exp_stem, "file_stem: Expected {:?}, found {:?}",
                        exp_stem, stem);

                let ext = path.extension();
                let exp_ext: Option<&str> = $extension;
                assert!(ext == exp_ext, "extension: Expected {:?}, found {:?}",
                        exp_ext, ext);
            }
        );

        ($path:expr, iter: $iter:expr,
                     parent: $parent:expr, file_name: $file:expr,
                     file_stem: $file_stem:expr, extension: $extension:expr) => (
            {
                t!($path, iter: $iter);
                t!($path, parent: $parent, file_name: $file);
                t!($path, file_stem: $file_stem, extension: $extension);
            }
        );
    );

    fn assert_components(components: &[&str], path: &RelativePath) {
        let components = components
            .iter()
            .cloned()
            .map(Component::Normal)
            .collect::<Vec<_>>();
        let result: Vec<_> = path.components().collect();
        assert_eq!(&components[..], &result[..]);
    }

    fn rp(input: &str) -> &RelativePath {
        RelativePath::new(input)
    }

    #[test]
    pub fn test_decompositions() {
        t!("",
        iter: [],
        parent: None,
        file_name: None,
        file_stem: None,
        extension: None
        );

        t!("foo",
        iter: ["foo"],
        parent: Some(""),
        file_name: Some("foo"),
        file_stem: Some("foo"),
        extension: None
        );

        t!("/",
        iter: [],
        parent: Some(""),
        file_name: None,
        file_stem: None,
        extension: None
        );

        t!("/foo",
        iter: ["foo"],
        parent: Some(""),
        file_name: Some("foo"),
        file_stem: Some("foo"),
        extension: None
        );

        t!("foo/",
        iter: ["foo"],
        parent: Some(""),
        file_name: Some("foo"),
        file_stem: Some("foo"),
        extension: None
        );

        t!("/foo/",
        iter: ["foo"],
        parent: Some(""),
        file_name: Some("foo"),
        file_stem: Some("foo"),
        extension: None
        );

        t!("foo/bar",
        iter: ["foo", "bar"],
        parent: Some("foo"),
        file_name: Some("bar"),
        file_stem: Some("bar"),
        extension: None
        );

        t!("/foo/bar",
        iter: ["foo", "bar"],
        parent: Some("/foo"),
        file_name: Some("bar"),
        file_stem: Some("bar"),
        extension: None
        );

        t!("///foo///",
        iter: ["foo"],
        parent: Some(""),
        file_name: Some("foo"),
        file_stem: Some("foo"),
        extension: None
        );

        t!("///foo///bar",
        iter: ["foo", "bar"],
        parent: Some("///foo"),
        file_name: Some("bar"),
        file_stem: Some("bar"),
        extension: None
        );

        t!("./.",
        iter: [".", "."],
        parent: Some(""),
        file_name: None,
        file_stem: None,
        extension: None
        );

        t!("/..",
        iter: [".."],
        parent: Some(""),
        file_name: None,
        file_stem: None,
        extension: None
        );

        t!("../",
        iter: [".."],
        parent: Some(""),
        file_name: None,
        file_stem: None,
        extension: None
        );

        t!("foo/.",
        iter: ["foo", "."],
        parent: Some(""),
        file_name: Some("foo"),
        file_stem: Some("foo"),
        extension: None
        );

        t!("foo/..",
        iter: ["foo", ".."],
        parent: Some("foo"),
        file_name: None,
        file_stem: None,
        extension: None
        );

        t!("foo/./",
        iter: ["foo", "."],
        parent: Some(""),
        file_name: Some("foo"),
        file_stem: Some("foo"),
        extension: None
        );

        t!("foo/./bar",
        iter: ["foo", ".", "bar"],
        parent: Some("foo/."),
        file_name: Some("bar"),
        file_stem: Some("bar"),
        extension: None
        );

        t!("foo/../",
        iter: ["foo", ".."],
        parent: Some("foo"),
        file_name: None,
        file_stem: None,
        extension: None
        );

        t!("foo/../bar",
        iter: ["foo", "..", "bar"],
        parent: Some("foo/.."),
        file_name: Some("bar"),
        file_stem: Some("bar"),
        extension: None
        );

        t!("./a",
        iter: [".", "a"],
        parent: Some("."),
        file_name: Some("a"),
        file_stem: Some("a"),
        extension: None
        );

        t!(".",
        iter: ["."],
        parent: Some(""),
        file_name: None,
        file_stem: None,
        extension: None
        );

        t!("./",
        iter: ["."],
        parent: Some(""),
        file_name: None,
        file_stem: None,
        extension: None
        );

        t!("a/b",
        iter: ["a", "b"],
        parent: Some("a"),
        file_name: Some("b"),
        file_stem: Some("b"),
        extension: None
        );

        t!("a//b",
        iter: ["a", "b"],
        parent: Some("a"),
        file_name: Some("b"),
        file_stem: Some("b"),
        extension: None
        );

        t!("a/./b",
        iter: ["a", ".", "b"],
        parent: Some("a/."),
        file_name: Some("b"),
        file_stem: Some("b"),
        extension: None
        );

        t!("a/b/c",
        iter: ["a", "b", "c"],
        parent: Some("a/b"),
        file_name: Some("c"),
        file_stem: Some("c"),
        extension: None
        );

        t!(".foo",
        iter: [".foo"],
        parent: Some(""),
        file_name: Some(".foo"),
        file_stem: Some(".foo"),
        extension: None
        );
    }

    #[test]
    pub fn test_stem_ext() {
        t!("foo",
        file_stem: Some("foo"),
        extension: None
        );

        t!("foo.",
        file_stem: Some("foo"),
        extension: Some("")
        );

        t!(".foo",
        file_stem: Some(".foo"),
        extension: None
        );

        t!("foo.txt",
        file_stem: Some("foo"),
        extension: Some("txt")
        );

        t!("foo.bar.txt",
        file_stem: Some("foo.bar"),
        extension: Some("txt")
        );

        t!("foo.bar.",
        file_stem: Some("foo.bar"),
        extension: Some("")
        );

        t!(".", file_stem: None, extension: None);

        t!("..", file_stem: None, extension: None);

        t!("", file_stem: None, extension: None);
    }

    #[test]
    pub fn test_set_file_name() {
        macro_rules! tfn(
                ($path:expr, $file:expr, $expected:expr) => ( {
                let mut p = RelativePathBuf::from($path);
                p.set_file_name($file);
                assert!(p.as_str() == $expected,
                        "setting file name of {:?} to {:?}: Expected {:?}, got {:?}",
                        $path, $file, $expected,
                        p.as_str());
            });
        );

        tfn!("foo", "foo", "foo");
        tfn!("foo", "bar", "bar");
        tfn!("foo", "", "");
        tfn!("", "foo", "foo");

        tfn!(".", "foo", "./foo");
        tfn!("foo/", "bar", "bar");
        tfn!("foo/.", "bar", "bar");
        tfn!("..", "foo", "../foo");
        tfn!("foo/..", "bar", "foo/../bar");
        tfn!("/", "foo", "/foo");
    }

    #[test]
    pub fn test_set_extension() {
        macro_rules! tse(
                ($path:expr, $ext:expr, $expected:expr, $output:expr) => ( {
                let mut p = RelativePathBuf::from($path);
                let output = p.set_extension($ext);
                assert!(p.as_str() == $expected && output == $output,
                        "setting extension of {:?} to {:?}: Expected {:?}/{:?}, got {:?}/{:?}",
                        $path, $ext, $expected, $output,
                        p.as_str(), output);
            });
        );

        tse!("foo", "txt", "foo.txt", true);
        tse!("foo.bar", "txt", "foo.txt", true);
        tse!("foo.bar.baz", "txt", "foo.bar.txt", true);
        tse!(".test", "txt", ".test.txt", true);
        tse!("foo.txt", "", "foo", true);
        tse!("foo", "", "foo", true);
        tse!("", "foo", "", false);
        tse!(".", "foo", ".", false);
        tse!("foo/", "bar", "foo.bar", true);
        tse!("foo/.", "bar", "foo.bar", true);
        tse!("..", "foo", "..", false);
        tse!("foo/..", "bar", "foo/..", false);
        tse!("/", "foo", "/", false);
    }

    #[test]
    fn test_eq_recievers() {
        use std::borrow::Cow;

        let borrowed: &RelativePath = RelativePath::new("foo/bar");
        let mut owned: RelativePathBuf = RelativePathBuf::new();
        owned.push("foo");
        owned.push("bar");
        let borrowed_cow: Cow<RelativePath> = borrowed.into();
        let owned_cow: Cow<RelativePath> = owned.clone().into();

        macro_rules! t {
            ($($current:expr),+) => {
                $(
                    assert_eq!($current, borrowed);
                    assert_eq!($current, owned);
                    assert_eq!($current, borrowed_cow);
                    assert_eq!($current, owned_cow);
                )+
            }
        }

        t!(borrowed, owned, borrowed_cow, owned_cow);
    }

    #[test]
    pub fn test_compare() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        fn hash<T: Hash>(t: T) -> u64 {
            let mut s = DefaultHasher::new();
            t.hash(&mut s);
            s.finish()
        }

        macro_rules! tc(
            ($path1:expr, $path2:expr, eq: $eq:expr,
             starts_with: $starts_with:expr, ends_with: $ends_with:expr,
             relative_from: $relative_from:expr) => ({
                 let path1 = RelativePath::new($path1);
                 let path2 = RelativePath::new($path2);

                 let eq = path1 == path2;
                 assert!(eq == $eq, "{:?} == {:?}, expected {:?}, got {:?}",
                         $path1, $path2, $eq, eq);
                 assert!($eq == (hash(path1) == hash(path2)),
                         "{:?} == {:?}, expected {:?}, got {} and {}",
                         $path1, $path2, $eq, hash(path1), hash(path2));

                 let starts_with = path1.starts_with(path2);
                 assert!(starts_with == $starts_with,
                         "{:?}.starts_with({:?}), expected {:?}, got {:?}", $path1, $path2,
                         $starts_with, starts_with);

                 let ends_with = path1.ends_with(path2);
                 assert!(ends_with == $ends_with,
                         "{:?}.ends_with({:?}), expected {:?}, got {:?}", $path1, $path2,
                         $ends_with, ends_with);

                 let relative_from = path1.strip_prefix(path2)
                                          .map(|p| p.as_str())
                                          .ok();
                 let exp: Option<&str> = $relative_from;
                 assert!(relative_from == exp,
                         "{:?}.strip_prefix({:?}), expected {:?}, got {:?}",
                         $path1, $path2, exp, relative_from);
            });
        );

        tc!("", "",
        eq: true,
        starts_with: true,
        ends_with: true,
        relative_from: Some("")
        );

        tc!("foo", "",
        eq: false,
        starts_with: true,
        ends_with: true,
        relative_from: Some("foo")
        );

        tc!("", "foo",
        eq: false,
        starts_with: false,
        ends_with: false,
        relative_from: None
        );

        tc!("foo", "foo",
        eq: true,
        starts_with: true,
        ends_with: true,
        relative_from: Some("")
        );

        tc!("foo/", "foo",
        eq: true,
        starts_with: true,
        ends_with: true,
        relative_from: Some("")
        );

        tc!("foo/bar", "foo",
        eq: false,
        starts_with: true,
        ends_with: false,
        relative_from: Some("bar")
        );

        tc!("foo/bar/baz", "foo/bar",
        eq: false,
        starts_with: true,
        ends_with: false,
        relative_from: Some("baz")
        );

        tc!("foo/bar", "foo/bar/baz",
        eq: false,
        starts_with: false,
        ends_with: false,
        relative_from: None
        );
    }

    #[test]
    fn test_join() {
        assert_components(&["foo", "bar", "baz"], &rp("foo/bar").join("baz///"));
        assert_components(
            &["hello", "world", "foo", "bar", "baz"],
            &rp("hello/world").join("///foo/bar/baz"),
        );
        assert_components(&["foo", "bar", "baz"], &rp("").join("foo/bar/baz"));
    }

    #[test]
    fn test_components_iterator() {
        use self::Component::*;

        assert_eq!(
            vec![Normal("hello"), Normal("world")],
            rp("/hello///world//").components().collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_to_path_buf() {
        let path = rp("/hello///world//");
        let path_buf = path.to_path(Path::new("."));
        let expected = Path::new(".").join("hello").join("world");
        assert_eq!(expected, path_buf);
    }

    #[test]
    fn test_eq() {
        assert_eq!(rp("//foo///bar"), rp("/foo/bar"));
        assert_eq!(rp("foo///bar"), rp("foo/bar"));
        assert_eq!(rp("foo"), rp("foo"));
        assert_eq!(rp("foo"), rp("foo").to_relative_path_buf());
    }

    #[test]
    fn test_next_back() {
        use self::Component::*;

        let mut it = rp("baz/bar///foo").components();
        assert_eq!(Some(Normal("foo")), it.next_back());
        assert_eq!(Some(Normal("bar")), it.next_back());
        assert_eq!(Some(Normal("baz")), it.next_back());
        assert_eq!(None, it.next_back());
    }

    #[test]
    fn test_parent() {
        let path = rp("baz/./bar/foo//./.");

        assert_eq!(Some(rp("baz/./bar")), path.parent());
        assert_eq!(
            Some(rp("baz/.")),
            path.parent().and_then(RelativePath::parent)
        );
        assert_eq!(
            Some(rp("")),
            path.parent()
                .and_then(RelativePath::parent)
                .and_then(RelativePath::parent)
        );
        assert_eq!(
            None,
            path.parent()
                .and_then(RelativePath::parent)
                .and_then(RelativePath::parent)
                .and_then(RelativePath::parent)
        );
    }

    #[test]
    fn test_relative_path_buf() {
        assert_eq!(
            rp("hello/world/."),
            rp("/hello///world//").to_owned().join(".")
        );
    }

    #[test]
    fn test_normalize() {
        assert_eq!(rp("c/d"), rp("a/.././b/../c/d").normalize());
    }

    #[test]
    fn test_relative_to() {
        assert_eq!(
            rp("foo/foo/bar"),
            rp("foo/bar").join_normalized("../foo/bar")
        );

        assert_eq!(
            rp("../c/e"),
            rp("x/y").join_normalized("../../a/b/../../../c/d/../e")
        );
    }

    #[test]
    fn test_from() {
        assert_eq!(
            rp("foo/bar").to_owned(),
            RelativePathBuf::from(String::from("foo/bar")),
        );

        assert_eq!(rp("foo/bar").to_owned(), RelativePathBuf::from("foo/bar"),);
    }

    #[test]
    fn test_default() {
        assert_eq!(RelativePathBuf::new(), RelativePathBuf::default(),);
    }

    #[test]
    pub fn test_push() {
        macro_rules! tp(
            ($path:expr, $push:expr, $expected:expr) => ( {
                let mut actual = RelativePathBuf::from($path);
                actual.push($push);
                assert!(actual.as_str() == $expected,
                        "pushing {:?} onto {:?}: Expected {:?}, got {:?}",
                        $push, $path, $expected, actual.as_str());
            });
        );

        tp!("", "foo", "foo");
        tp!("foo", "bar", "foo/bar");
        tp!("foo/", "bar", "foo/bar");
        tp!("foo//", "bar", "foo//bar");
        tp!("foo/.", "bar", "foo/./bar");
        tp!("foo./.", "bar", "foo././bar");
        tp!("foo", "", "foo/");
        tp!("foo", ".", "foo/.");
        tp!("foo", "..", "foo/..");
    }

    #[test]
    pub fn test_pop() {
        macro_rules! tp(
            ($path:expr, $expected:expr, $output:expr) => ( {
                let mut actual = RelativePathBuf::from($path);
                let output = actual.pop();
                assert!(actual.as_str() == $expected && output == $output,
                        "popping from {:?}: Expected {:?}/{:?}, got {:?}/{:?}",
                        $path, $expected, $output,
                        actual.as_str(), output);
            });
        );

        tp!("", "", false);
        tp!("/", "", true);
        tp!("foo", "", true);
        tp!(".", "", true);
        tp!("/foo", "", true);
        tp!("/foo/bar", "/foo", true);
        tp!("/foo/bar/.", "/foo", true);
        tp!("foo/bar", "foo", true);
        tp!("foo/.", "", true);
        tp!("foo//bar", "foo", true);
    }

    #[test]
    pub fn test_display() {
        // NB: display delegated to the underlying string.
        assert_eq!(RelativePathBuf::from("foo/bar").to_string(), "foo/bar");
        assert_eq!(RelativePath::new("foo/bar").to_string(), "foo/bar");

        assert_eq!(format!("{}", RelativePathBuf::from("foo/bar")), "foo/bar");
        assert_eq!(format!("{}", RelativePath::new("foo/bar")), "foo/bar");
    }

    #[cfg(unix)]
    #[test]
    pub fn test_unix_from_path() {
        use std::ffi::OsStr;
        use std::os::unix::ffi::OsStrExt;

        assert_eq!(
            Err(FromPathErrorKind::NonRelative.into()),
            RelativePath::from_path("/foo/bar")
        );

        // Continuation byte without continuation.
        let non_utf8 = OsStr::from_bytes(&[0x80u8]);

        assert_eq!(
            Err(FromPathErrorKind::NonUtf8.into()),
            RelativePath::from_path(non_utf8)
        );
    }

    #[cfg(windows)]
    #[test]
    pub fn test_windows_from_path() {
        assert_eq!(
            Err(FromPathErrorKind::NonRelative.into()),
            RelativePath::from_path("c:\\foo\\bar")
        );

        assert_eq!(
            Err(FromPathErrorKind::BadSeparator.into()),
            RelativePath::from_path("foo\\bar")
        );
    }

    #[cfg(unix)]
    #[test]
    pub fn test_unix_owned_from_path() {
        use std::ffi::OsStr;
        use std::os::unix::ffi::OsStrExt;

        assert_eq!(
            Err(FromPathErrorKind::NonRelative.into()),
            RelativePathBuf::from_path(Path::new("/foo/bar"))
        );

        // Continuation byte without continuation.
        let non_utf8 = OsStr::from_bytes(&[0x80u8]);

        assert_eq!(
            Err(FromPathErrorKind::NonUtf8.into()),
            RelativePathBuf::from_path(Path::new(non_utf8))
        );
    }

    #[cfg(windows)]
    #[test]
    pub fn test_windows_owned_from_path() {
        assert_eq!(
            Err(FromPathErrorKind::NonRelative.into()),
            RelativePathBuf::from_path(Path::new("c:\\foo\\bar"))
        );
    }
}

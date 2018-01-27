// This file contains parts that are Copyright 2015 The Rust Project Developers, copied from:
// https://github.com/rust-lang/rust
// cb2a656cdfb6400ac0200c661267f91fabf237e2 src/libstd/path.rs

//! A platform-neutral relative path.
//!
//! This provide types which are analogous to `Path`, and `PathBuf` found in stdlib, with the
//! following characteristics:
//!
//! * The path separator is set to a fixed character (`/`), regardless of platform.
//! * Relative paths cannot represent an absolute path in the filesystem, without first specifying
//!   what they are relative to through [`to_path`].
//!
//! [`to_path`]: struct.RelativePath.html#method.to_path
//!
//! # Serde Support
//!
//! This library includes serde support that can be enabled with the `serde` feature.

use std::borrow::{Borrow, Cow};
use std::cmp;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::{self, Deref};
use std::path;

#[cfg(feature = "serde")]
extern crate serde;

const STEM_SEP: char = '.';
const CURRENT: &str = ".";
const PARENT: &str = "..";
const SEP: char = '/';
const SEP_BYTE: u8 = SEP as u8;

/// Scan backwards until the given separator has been encountered using the provided `cmp`.
macro_rules! scan_back {
    ($source:expr, $init:expr, $cmp:tt, $sep:expr) => {{
        let mut n = $init;

        while n > 0 && $source[n - 1] $cmp $sep {
            n -= 1;
        }

        n
    }}
}

/// Scan forward until the given separator has been encountered using the provided `cmp`.
macro_rules! scan_forward {
    ($source:expr, $init:expr, $cmp:tt, $sep:expr) => {{
        let mut n = $init;

        while n < $source.len() && $source[n] $cmp $sep {
            n += 1;
        }

        n
    }}
}

fn split_file_at_dot(input: &str) -> (Option<&str>, Option<&str>) {
    if input == PARENT {
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

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Component<'a> {
    CurDir,
    ParentDir,
    Normal(&'a str),
}

impl<'a> Component<'a> {
    pub fn as_str(&self) -> &'a str {
        use self::Component::*;

        match *self {
            CurDir => CURRENT,
            ParentDir => PARENT,
            Normal(name) => name,
        }
    }
}

/// Traverse the given components and apply to the provided stack.
///
/// This takes '.', and '..' into account. Where '.' doesn't change the stack, and '..' pops the
/// last item or further adds parent components.
#[inline(always)]
fn relative_traversal<'a, C>(stack: &mut Vec<Component<'a>>, components: C)
    where C: IntoIterator<Item = Component<'a>>
{
    use self::Component::*;

    for c in components.into_iter() {
        match c {
            ParentDir => {
                match stack.last() {
                    Some(&ParentDir) | None => {
                        stack.push(ParentDir);
                    }
                    _ => {
                        stack.pop();
                    }
                }
            },
            CurDir => {},
            Normal(name) => stack.push(Normal(name)),
        }
    }
}

/// Iterator over all the components in a relative path.
#[derive(Clone)]
pub struct Components<'a> {
    source: &'a [u8],
}

impl<'a> Iterator for Components<'a> {
    type Item = Component<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.source.is_empty() {
            return None;
        }

        // strip prefixing separators
        let start = scan_forward!(self.source, 0usize, ==, SEP_BYTE);
        // collect component
        let end = scan_forward!(self.source, start, !=, SEP_BYTE);
        // strip suffixing separator
        let slice_end = scan_forward!(self.source, end, ==, SEP_BYTE);

        let slice = &self.source[start..end];
        self.source = &self.source[slice_end..];

        if slice.is_empty() {
            return None;
        }

        let slice = unsafe { ::std::str::from_utf8_unchecked(slice) };

        match slice {
            "." => Some(Component::CurDir),
            ".." => Some(Component::ParentDir),
            slice => Some(Component::Normal(slice)),
        }
    }
}

impl<'a> DoubleEndedIterator for Components<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.next_back_component().map(|(s, _)| s)
    }
}

impl<'a> Components<'a> {
    pub fn new(input: &str) -> Components {
        Components { source: input.as_bytes() }
    }

    /// Extracts the next back component and its length including separators.
    fn next_back_component(&mut self) -> Option<(Component<'a>, usize)> {
        if self.source.is_empty() {
            return None;
        }

        let slice_end = self.source.len();

        // strip suffixing separators
        let end = scan_back!(self.source, slice_end, ==, SEP_BYTE);
        // find component
        let start = scan_back!(self.source, end, !=, SEP_BYTE);
        // strip prefixing separator
        let slice_start = scan_back!(self.source, start, ==, SEP_BYTE);

        let slice = &self.source[start..end];
        self.source = &self.source[..slice_start];

        if slice.is_empty() {
            return None;
        }

        let slice = unsafe { ::std::str::from_utf8_unchecked(slice) };

        let w = slice_end - slice_start;

        match slice {
            "." => Some((Component::CurDir, w)),
            ".." => Some((Component::ParentDir, w)),
            slice => Some((Component::Normal(slice), w)),
        }
    }
}

impl<'a> cmp::PartialEq for Components<'a> {
    fn eq(&self, other: &Components<'a>) -> bool {
        Iterator::eq(self.clone(), other.clone())
    }
}

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
        RelativePathBuf { inner: String::new() }
    }

    fn as_mut_vec(&mut self) -> &mut Vec<u8> {
        unsafe { &mut *(self as *mut RelativePathBuf as *mut Vec<u8>) }
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

        if self.inner.len() > 0 {
            self.inner.push(SEP);
        }

        self.inner.push_str(other)
    }

    /// Updates [`self.file_name`] to `file_name`.
    ///
    /// If [`self.file_name`] was `None`, this is equivalent to pushing
    /// `file_name`.
    ///
    /// Otherwise it is equivalent to calling [`pop`] and then pushing
    /// `file_name`. The new path will be a sibling of the original path.
    /// (That is, it will have the same parent.)
    ///
    /// [`self.file_name`]: struct.RelativePathBuf.html#method.file_name
    /// [`pop`]: struct.RelativePathBuf.html#method.pop
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

        if self.file_name().is_some() {
            if !self.pop() {
                self.inner = file_name.to_string();
                return;
            }
        }

        self.push(file_name);
    }

    /// Updates [`self.extension`] to `extension`.
    ///
    /// Returns `false` and does nothing if [`self.file_name`] is `None`,
    /// returns `true` and updates the extension otherwise.
    ///
    /// If [`self.extension`] is `None`, the extension is added; otherwise
    /// it is replaced.
    ///
    /// [`self.file_name`]: struct.RelativePathBuf.html#method.file_name
    /// [`self.extension`]: struct.RelativePathBuf.html#method.extension
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
    /// Returns `false` and does nothing if [`self.file_name`] is [`None`].
    /// Otherwise, returns `true`.
    ///
    /// [`None`]: ../../std/option/enum.Option.html#variant.None
    /// [`self.parent`]: struct.PathBuf.html#method.parent
    /// [`self.file_name`]: struct.PathBuf.html#method.file_name
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
    /// assert_eq!(false, p.pop());
    /// assert_eq!(RelativePath::new("test"), p);
    /// ```
    pub fn pop(&mut self) -> bool {
        match self.parent().map(|p| p.as_u8_slice().len()) {
            Some(len) => {
                self.as_mut_vec().truncate(len);
                true
            }
            None => false,
        }
    }

    /// Coerce to a [`RelativePath`] slice.
    ///
    /// [`RelativePath`]: struct.RelativePath.html
    pub fn as_relative_path(&self) -> &RelativePath {
        self
    }
}

impl Default for RelativePathBuf {
    fn default() -> Self {
        RelativePathBuf::new()
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
        RelativePathBuf { inner: path.as_ref().to_owned() }
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
pub struct RelativePath {
    inner: str,
}

impl RelativePath {
    /// Directly wraps a string slice as a `RelativePath` slice.
    pub fn new<S: AsRef<str> + ?Sized>(s: &S) -> &RelativePath {
        unsafe { &*(s.as_ref() as *const str as *const RelativePath) }
    }

    // The following (private!) function reveals the byte encoding used for OsStr.
    fn as_u8_slice(&self) -> &[u8] {
        unsafe { &*(&self.inner as *const str as *const [u8]) }
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
    pub fn display(&self) -> Display {
        Display {
            path: self
        }
    }

    /// Creates an owned [`RelativePathBuf`] with path adjoined to self.
    ///
    /// [`RelativePathBuf`]: struct.RelativePathBuf.html
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

    /// Convert to an owned [`RelativePathBuf`].
    ///
    /// [`RelativePathBuf`]: struct.RelativePathBuf.html
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
    /// assert_eq!(None, RelativePath::new("foo").parent());
    /// assert_eq!(None, RelativePath::new("").parent());
    /// ```
    pub fn parent(&self) -> Option<&RelativePath> {
        self.components().next_back_component().and_then(
            |(_, size)| {
                let slice = &self.inner[..self.inner.len() - size];

                if slice.is_empty() {
                    return None;
                }

                Some(RelativePath::new(slice))
            },
        )
    }

    /// Returns the final component of the `RelativePath`, if there is one.
    ///
    /// If the path is a normal file, this is the file name. If it's the path of a directory, this
    /// is the directory name.
    ///
    /// Returns `None` If the path terminates in `..`.
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

        let mut c = self.components();

        while let Some(p) = c.next_back() {
            match p {
                Normal(name) => return Some(name),
                CurDir => continue,
                _ => return None,
            }
        }

        None
    }

    /// Creates an owned [`RelativePathBuf`] like `self` but with the given file name.
    ///
    /// See [`RelativePathBuf::set_file_name`] for more details.
    ///
    /// [`RelativePathBuf`]: struct.RelativePathBuf.html
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
    /// * `None`, if there is no file name;
    /// * The entire file name if there is no embedded `.`;
    /// * The entire file name if the file name begins with `.` and has no other `.`s within;
    /// * Otherwise, the portion of the file name before the final `.`
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
        self.file_name().map(split_file_at_dot).and_then(|(before, after)| before.or(after))
    }

    /// Extracts the extension of [`self.file_name`], if possible.
    ///
    /// The extension is:
    ///
    /// * `None`, if there is no file name;
    /// * `None`, if there is no embedded `.`;
    /// * `None`, if the file name begins with `.` and has no other `.`s within;
    /// * Otherwise, the portion of the file name after the final `.`
    ///
    /// [`self.file_name`]: struct.RelativePath.html#method.file_name
    /// [`None`]: ../../std/option/enum.Option.html#variant.None
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
        self.file_name().map(split_file_at_dot).and_then(|(before, after)| before.and(after))
    }

    /// Creates an owned [`RelativePathBuf`] like `self` but with the given extension.
    ///
    /// See [`RelativePathBuf::set_extension`] for more details.
    ///
    /// [`RelativePathBuf`]: struct.RelativePathBuf.html
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

    /// Return a relative path, resolved from the current path.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use relative_path::RelativePath;
    ///
    /// assert_eq!(
    ///     RelativePath::new("foo/baz.txt"),
    ///     RelativePath::new("foo/bar").relativize_with("../baz.txt").as_relative_path()
    /// );
    /// ```
    pub fn relativize_with<P: AsRef<RelativePath>>(&self, path: P) -> RelativePathBuf {
        let mut stack = Vec::new();
        relative_traversal(&mut stack, self.components());
        relative_traversal(&mut stack, path.as_ref().components());
        let string = stack.into_iter().map(|c| c.as_str()).collect::<Vec<_>>().join("/");
        RelativePathBuf::from(string)
    }

    /// Return a relative path, resolved from the current path by removing all relative components.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use relative_path::RelativePath;
    ///
    /// assert_eq!(
    ///     RelativePath::new("foo/baz.txt"),
    ///     RelativePath::new("foo/./bar/../baz.txt").relativize().as_relative_path()
    /// );
    /// ```
    pub fn relativize(&self) -> RelativePathBuf {
        let mut stack = Vec::new();
        relative_traversal(&mut stack, self.components());
        let string = stack.into_iter().map(|c| c.as_str()).collect::<Vec<_>>().join("/");
        RelativePathBuf::from(string)
    }

    /// Check if path starts with a path separator.
    fn starts_with_sep(&self) -> bool {
        self.inner.chars().next() == Some(SEP)
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
        self.path.inner.fmt(f)
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
    ($lhs:ty, $rhs: ty) => {
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
    }
}

impl_cmp!(RelativePathBuf, RelativePath);
impl_cmp!(RelativePathBuf, &'a RelativePath);
impl_cmp!(Cow<'a, RelativePath>, RelativePath);
impl_cmp!(Cow<'a, RelativePath>, &'b RelativePath);
impl_cmp!(Cow<'a, RelativePath>, RelativePathBuf);

macro_rules! impl_cmp_str {
    ($lhs:ty, $rhs: ty) => {
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
    }
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
    use std::path::Path;
    use super::*;

    fn assert_components(components: &[&str], path: &RelativePath) {
        let components = components.iter().cloned().map(Component::Normal).collect::<Vec<_>>();
        let result: Vec<_> = path.components().collect();
        assert_eq!(&components[..], &result[..]);
    }

    fn rp(input: &str) -> &RelativePath {
        RelativePath::new(input)
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
        let path = rp("baz//bar/foo//");
        assert_eq!(Some(rp("baz/bar")), path.parent());
        assert_eq!(Some(rp("baz")), path.parent().and_then(RelativePath::parent));
        assert_eq!(None,
            path.parent().and_then(RelativePath::parent).and_then(RelativePath::parent)
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
    fn test_relativize() {
        assert_eq!(
            rp("c/d"),
            rp("a/.././b/../c/d").relativize()
        );
    }

    #[test]
    fn test_relativize_with() {
        assert_eq!(
            rp("foo/foo/bar"),
            rp("foo/bar").relativize_with("../foo/bar")
        );

        assert_eq!(
            rp("../c/e"),
            rp("x/y").relativize_with("../../a/b/../../../c/d/../e")
        );
    }

    #[test]
    fn test_from() {
        assert_eq!(
            rp("foo/bar").to_owned(),
            RelativePathBuf::from(String::from("foo/bar")),
        );

        assert_eq!(
            rp("foo/bar").to_owned(),
            RelativePathBuf::from("foo/bar"),
        );
    }

    #[test]
    fn test_default() {
        assert_eq!(
            RelativePathBuf::new(),
            RelativePathBuf::default(),
        );
    }
}

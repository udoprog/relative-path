// Some documentation copied from the Rust project under the MIT license.
//
// See https://github.com/rust-lang/rust

use std::fs::File;
use std::io::{self, Read, Write};
use std::path::Path;

use crate::RelativePath;

#[cfg_attr(windows, path = "windows.rs")]
#[cfg_attr(unix, path = "unix.rs")]
mod imp;

#[cfg(not(any(windows, unix)))]
compile_error!("root is only supported on cfg(windows) and cfg(unix)");

/// An open root directory from which relative paths can be opened.
///
/// In contrast to using APIs such as [`RelativePath::to_path`], this does not
/// require allocations to open a path.
///
/// This is achieved by keeping an open handle to the directory and using
/// platform-specific APIs to open a relative path, such as [`openat`] on `unix`.
///
/// [`openat`]: https://linux.die.net/man/2/openat
pub struct Root {
    inner: imp::Root,
}

impl Root {
    /// Open the given directory that can be used as a root for opening and
    /// manipulating relative paths.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use relative_path::Root;
    ///
    /// let root = Root::new(".")?;
    /// # Ok::<_, std::io::Error>(())
    /// ```
    pub fn new<P>(path: P) -> io::Result<Self>
    where
        P: AsRef<Path>,
    {
        Ok(Self {
            inner: imp::Root::new(path)?,
        })
    }

    /// Construct an open options associated with this root.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use relative_path::Root;
    ///
    /// let root = Root::new(".")?;
    ///
    /// let file = root.open_options().read(true).open("foo.txt");
    /// # Ok::<_, std::io::Error>(())
    /// ```
    pub fn open_options(&self) -> OpenOptions {
        OpenOptions {
            root: &self.inner,
            options: imp::OpenOptions::new(),
        }
    }

    /// Create the given file.
    pub fn create<P>(&self, path: P) -> io::Result<File>
    where
        P: AsRef<RelativePath>,
    {
        self.open_options().write(true).create(true).open(path)
    }

    /// Open the given file for reading.
    pub fn open<P>(&self, path: P) -> io::Result<File>
    where
        P: AsRef<RelativePath>,
    {
        self.open_options().read(true).open(path)
    }

    /// Read the entire contents of a file into a bytes vector.
    ///
    /// This is a convenience function for using [`File::open`] and
    /// [`read_to_end`] with fewer imports and without an intermediate variable.
    ///
    /// [`read_to_end`]: Read::read_to_end
    ///
    /// # Errors
    ///
    /// This function will return an error if `path` does not already exist.
    /// Other errors may also be returned according to [`OpenOptions::open`].
    ///
    /// While reading from the file, this function handles
    /// [`io::ErrorKind::Interrupted`] with automatic retries. See [io::Read]
    /// documentation for details.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::SocketAddr;
    ///
    /// use relative_path::Root;
    ///
    /// let root = Root::new(".")?;
    /// let foo: SocketAddr = String::from_utf8_lossy(&root.read("address.txt")?).parse()?;
    /// # Ok::<_, Box<dyn std::error::Error>>(())
    /// ```
    pub fn read<P>(&self, path: P) -> io::Result<Vec<u8>>
    where
        P: AsRef<RelativePath>,
    {
        fn inner(this: &Root, path: &RelativePath) -> io::Result<Vec<u8>> {
            let mut file = this.open(path)?;
            let size = file.metadata().map(|m| m.len() as usize).ok();
            let mut bytes = Vec::with_capacity(size.unwrap_or(0));
            file.read_to_end(&mut bytes)?;
            Ok(bytes)
        }

        inner(self, path.as_ref())
    }

    /// Read the entire contents of a file into a string.
    ///
    /// This is a convenience function for using [`File::open`] and
    /// [`read_to_string`] with fewer imports and without an intermediate
    /// variable.
    ///
    /// [`read_to_string`]: Read::read_to_string
    ///
    /// # Errors
    ///
    /// This function will return an error if `path` does not already exist.
    /// Other errors may also be returned according to [`OpenOptions::open`].
    ///
    /// If the contents of the file are not valid UTF-8, then an error will also
    /// be returned.
    ///
    /// While reading from the file, this function handles
    /// [`io::ErrorKind::Interrupted`] with automatic retries. See [io::Read]
    /// documentation for details.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::SocketAddr;
    ///
    /// use relative_path::Root;
    ///
    /// let root = Root::new(".")?;
    /// let foo: SocketAddr = root.read_to_string("address.txt")?.parse()?;
    /// # Ok::<_, Box<dyn std::error::Error>>(())
    /// ```
    pub fn read_to_string<P>(&self, path: P) -> io::Result<String>
    where
        P: AsRef<RelativePath>,
    {
        fn inner(this: &Root, path: &RelativePath) -> io::Result<String> {
            let mut file = this.open(path)?;
            let size = file.metadata().map(|m| m.len() as usize).ok();
            let mut string = String::with_capacity(size.unwrap_or(0));
            file.read_to_string(&mut string)?;
            Ok(string)
        }

        inner(self, path.as_ref())
    }

    /// Write a slice as the entire contents of a file.
    ///
    /// This function will create a file if it does not exist,
    /// and will entirely replace its contents if it does.
    ///
    /// Depending on the platform, this function may fail if the
    /// full directory path does not exist.
    ///
    /// This is a convenience function for using [`File::create`] and
    /// [`write_all`] with fewer imports.
    ///
    /// [`write_all`]: Write::write_all
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use relative_path::Root;
    ///
    /// let root = Root::new(".")?;
    ///
    /// root.write("foo.txt", b"Lorem ipsum")?;
    /// root.write("bar.txt", "dolor sit")?;
    /// # Ok::<_, std::io::Error>(())
    /// ```
    /// ```
    pub fn write<P, C>(&self, path: P, contents: C) -> io::Result<()>
    where
        P: AsRef<RelativePath>,
        C: AsRef<[u8]>,
    {
        self.create(path)?.write_all(contents.as_ref())
    }
}

/// Options and flags which can be used to configure how a file is opened.
///
/// This builder exposes the ability to configure how a [`File`] is opened and
/// what operations are permitted on the open file. The [`File::open`] and
/// [`File::create`] methods are aliases for commonly used options using this
/// builder.
///
/// Generally speaking, when using `OpenOptions`, you'll first call
/// [`Root::open_options`], then chain calls to methods to set each option, then
/// call [`OpenOptions::open`], passing the path of the file you're trying to
/// open. This will give you a [`io::Result`] with a [`File`] inside that you
/// can further operate on.
///
/// # Examples
///
/// Opening a file to read:
///
/// ```no_run
/// use relative_path::Root;
///
/// let root = Root::new(".")?;
///
/// let file = root.open_options().read(true).open("foo.txt");
/// # Ok::<_, std::io::Error>(())
/// ```
///
/// Opening a file for both reading and writing, as well as creating it if it
/// doesn't exist:
///
/// ```no_run
/// use relative_path::Root;
///
/// let root = Root::new(".")?;
///
/// let file = root
///     .open_options()
///     .read(true)
///     .write(true)
///     .create(true)
///     .open("foo.txt")?;
/// # Ok::<_, std::io::Error>(())
/// ```
#[derive(Clone, Debug)]
pub struct OpenOptions<'a> {
    root: &'a imp::Root,
    options: imp::OpenOptions,
}

impl<'a> OpenOptions<'a> {
    /// Sets the option for read access.
    ///
    /// This option, when true, will indicate that the file should be
    /// `read`-able if opened.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use relative_path::Root;
    ///
    /// let root = Root::new(".")?;
    ///
    /// let file = root.open_options().read(true).open("foo.txt");
    /// # Ok::<_, std::io::Error>(())
    /// ```
    pub fn read(&mut self, read: bool) -> &mut Self {
        self.options.read(read);
        self
    }

    /// Sets the option for write access.
    ///
    /// This option, when true, will indicate that the file should be
    /// `write`-able if opened.
    ///
    /// If the file already exists, any write calls on it will overwrite its
    /// contents, without truncating it.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use relative_path::Root;
    ///
    /// let root = Root::new(".")?;
    ///
    /// let file = root.open_options().write(true).open("foo.txt");
    /// # Ok::<_, std::io::Error>(())
    /// ```
    pub fn write(&mut self, write: bool) -> &mut Self {
        self.options.write(write);
        self
    }

    /// Sets the option for the append mode.
    ///
    /// This option, when true, means that writes will append to a file instead
    /// of overwriting previous contents. Note that setting
    /// `.write(true).append(true)` has the same effect as setting only
    /// `.append(true)`.
    ///
    /// For most filesystems, the operating system guarantees that all writes
    /// are atomic: no writes get mangled because another process writes at the
    /// same time.
    ///
    /// One maybe obvious note when using append-mode: make sure that all data
    /// that belongs together is written to the file in one operation. This can
    /// be done by concatenating strings before passing them to [`write()`], or
    /// using a buffered writer (with a buffer of adequate size), and calling
    /// [`flush()`] when the message is complete.
    ///
    /// If a file is opened with both read and append access, beware that after
    /// opening, and after every write, the position for reading may be set at
    /// the end of the file. So, before writing, save the current position
    /// (using <code>[seek]\([SeekFrom]::[Current]\(0))</code>), and restore it
    /// before the next read.
    ///
    /// ## Note
    ///
    /// This function doesn't create the file if it doesn't exist. Use the
    /// [`OpenOptions::create`] method to do so.
    ///
    /// [`write()`]: Write::write "io::Write::write"
    /// [`flush()`]: Write::flush "io::Write::flush"
    /// [seek]: std::io::Seek::seek "io::Seek::seek"
    /// [SeekFrom]: std::io::SeekFrom
    /// [Current]: std::io::SeekFrom::Current
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use relative_path::Root;
    ///
    /// let root = Root::new(".")?;
    ///
    /// let file = root.open_options().append(true).open("foo.txt");
    /// # Ok::<_, std::io::Error>(())
    /// ```
    pub fn append(&mut self, append: bool) -> &mut Self {
        self.options.append(append);
        self
    }

    /// Sets the option for truncating a previous file.
    ///
    /// If a file is successfully opened with this option set it will truncate
    /// the file to 0 length if it already exists.
    ///
    /// The file must be opened with write access for truncate to work.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use relative_path::Root;
    ///
    /// let root = Root::new(".")?;
    ///
    /// let file = root.open_options().write(true).truncate(true).open("foo.txt");
    /// # Ok::<_, std::io::Error>(())
    /// ```
    pub fn truncate(&mut self, truncate: bool) -> &mut Self {
        self.options.truncate(truncate);
        self
    }

    /// Sets the option to create a new file, or open it if it already exists.
    ///
    /// In order for the file to be created, [`OpenOptions::write`] or
    /// [`OpenOptions::append`] access must be used.
    ///
    /// See also [`Root::write()`] for a simple function to create a file with a
    /// given data.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use relative_path::Root;
    ///
    /// let root = Root::new(".")?;
    ///
    /// let file = root.open_options().write(true).create(true).open("foo.txt");
    /// # Ok::<_, std::io::Error>(())
    /// ```
    pub fn create(&mut self, create: bool) -> &mut Self {
        self.options.create(create);
        self
    }

    /// Sets the option to create a new file, failing if it already exists.
    ///
    /// No file is allowed to exist at the target location, also no (dangling) symlink. In this
    /// way, if the call succeeds, the file returned is guaranteed to be new.
    ///
    /// This option is useful because it is atomic. Otherwise between checking
    /// whether a file exists and creating a new one, the file may have been
    /// created by another process (a TOCTOU race condition / attack).
    ///
    /// If `.create_new(true)` is set, [`.create()`] and [`.truncate()`] are
    /// ignored.
    ///
    /// The file must be opened with write or append access in order to create
    /// a new file.
    ///
    /// [`.create()`]: OpenOptions::create
    /// [`.truncate()`]: OpenOptions::truncate
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use relative_path::Root;
    ///
    /// let root = Root::new(".")?;
    ///
    /// let file = root.open_options().write(true).create_new(true).open("foo.txt");
    /// # Ok::<_, std::io::Error>(())
    /// ```
    pub fn create_new(&mut self, create_new: bool) -> &mut Self {
        self.options.create_new(create_new);
        self
    }

    /// Opens a file at `path` with the options specified by `self`.
    ///
    /// # Errors
    ///
    /// This function will return an error under a number of different
    /// circumstances. Some of these error conditions are listed here, together
    /// with their [`io::ErrorKind`]. The mapping to [`io::ErrorKind`]s is not
    /// part of the compatibility contract of the function.
    ///
    /// * [`NotFound`]: The specified file does not exist and neither `create`
    ///   or `create_new` is set.
    /// * [`NotFound`]: One of the directory components of the file path does
    ///   not exist.
    /// * [`PermissionDenied`]: The user lacks permission to get the specified
    ///   access rights for the file.
    /// * [`PermissionDenied`]: The user lacks permission to open one of the
    ///   directory components of the specified path.
    /// * [`AlreadyExists`]: `create_new` was specified and the file already
    ///   exists.
    /// * [`InvalidInput`]: Invalid combinations of open options (truncate
    ///   without write access, no access mode set, etc.).
    ///
    /// The following errors don't match any existing [`io::ErrorKind`] at the moment:
    /// * One of the directory components of the specified file path
    ///   was not, in fact, a directory.
    /// * Filesystem-level errors: full disk, write permission
    ///   requested on a read-only file system, exceeded disk quota, too many
    ///   open files, too long filename, too many symbolic links in the
    ///   specified path (Unix-like systems only), etc.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use relative_path::Root;
    ///
    /// let root = Root::new(".")?;
    ///
    /// let file = root.open_options().read(true).open("foo.txt");
    /// # Ok::<_, std::io::Error>(())
    /// ```
    ///
    /// [`AlreadyExists`]: io::ErrorKind::AlreadyExists
    /// [`InvalidInput`]: io::ErrorKind::InvalidInput
    /// [`NotFound`]: io::ErrorKind::NotFound
    /// [`PermissionDenied`]: io::ErrorKind::PermissionDenied
    pub fn open<P>(&self, path: P) -> io::Result<File>
    where
        P: AsRef<RelativePath>,
    {
        self.root.open_at(path, &self.options)
    }
}
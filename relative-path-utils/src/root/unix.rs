use std::ffi::{CString, OsString};
use std::fs::File;
use std::io;
use std::mem::MaybeUninit;
use std::os::fd::FromRawFd;
use std::os::fd::OwnedFd;
use std::os::fd::{AsFd, AsRawFd};
use std::path::{Path, MAIN_SEPARATOR};

#[cfg(not(any(
    all(target_os = "linux", not(target_env = "musl")),
    target_os = "emscripten",
    target_os = "l4re",
    target_os = "android",
    target_os = "hurd",
)))]
use libc::{fstat as fstat64, stat as stat64};
#[cfg(any(
    all(target_os = "linux", not(target_env = "musl")),
    target_os = "emscripten",
    target_os = "l4re",
    target_os = "hurd"
))]
use libc::{fstat64, stat64};

use relative_path::{Component, RelativePath};

#[derive(Debug)]
pub(super) struct Root {
    handle: OwnedFd,
}

impl Root {
    pub(super) fn new(path: &Path) -> io::Result<Self> {
        let file = std::fs::OpenOptions::new().read(true).open(path)?;

        Ok(Root {
            handle: OwnedFd::from(file),
        })
    }

    pub(super) fn open_at(&self, path: &RelativePath, options: &OpenOptions) -> io::Result<File> {
        Ok(File::from(self.open_at_inner(path, options)?))
    }

    fn open_at_inner(&self, path: &RelativePath, options: &OpenOptions) -> io::Result<OwnedFd> {
        let path = convert_to_c_string(path)?;

        let flags = libc::O_CLOEXEC | options.get_creation_mode()? | options.get_access_mode()?;

        unsafe {
            let fd = libc::openat(self.handle.as_raw_fd(), path.as_ptr(), flags);

            if fd == -1 {
                return Err(io::Error::last_os_error());
            }

            Ok(OwnedFd::from_raw_fd(fd))
        }
    }

    pub(super) fn metadata(&self, path: &RelativePath) -> io::Result<Metadata> {
        let owned;

        let fd = if is_current(path) {
            self.handle.as_fd()
        } else {
            let mut opts = OpenOptions::new();
            opts.read(true);
            owned = self.open_at_inner(path, &opts)?;
            owned.as_fd()
        };

        unsafe {
            let mut stat = MaybeUninit::zeroed();

            if fstat64(fd.as_raw_fd(), stat.as_mut_ptr()) == -1 {
                return Err(io::Error::last_os_error());
            }

            let stat = stat.assume_init();

            Ok(Metadata { stat })
        }
    }

    pub(super) fn read_dir(&self, path: &RelativePath) -> io::Result<ReadDir> {
        let mut opts = OpenOptions::new();
        opts.read(true);
        let fd = self.open_at_inner(path, &opts)?;

        let dir = unsafe {
            let handle = libc::fdopendir(fd.as_raw_fd());

            if handle.is_null() {
                return Err(io::Error::last_os_error());
            }

            Dir { handle }
        };

        Ok(ReadDir {
            dir,
            _fd: fd,
            end_of_stream: false,
        })
    }
}

pub(super) struct ReadDir {
    dir: Dir,
    _fd: OwnedFd,
    end_of_stream: bool,
}

impl Iterator for ReadDir {
    type Item = io::Result<DirEntry>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner_next()
    }
}

#[cfg(any(
    target_os = "android",
    target_os = "linux",
    target_os = "solaris",
    target_os = "fuchsia",
    target_os = "redox",
    target_os = "illumos",
    target_os = "aix",
    target_os = "nto",
    target_os = "vita",
    target_os = "hurd",
))]
mod read_dir {
    use std::ffi::c_char;
    use std::ffi::CStr;
    use std::ffi::OsString;
    use std::io;
    use std::mem::size_of;
    use std::os::unix::ffi::OsStringExt;

    use super::{DirEntry, ReadDir};

    impl ReadDir {
        pub(super) fn inner_next(&mut self) -> Option<io::Result<DirEntry>> {
            const D_NAME_OFFSET: usize = size_of::<libc::ino64_t>()
                + size_of::<libc::off64_t>()
                + size_of::<libc::c_ushort>()
                + size_of::<libc::c_uchar>();

            if self.end_of_stream {
                return None;
            }

            unsafe {
                loop {
                    // As of POSIX.1-2017, readdir() is not required to be thread safe; only
                    // readdir_r() is. However, readdir_r() cannot correctly handle platforms
                    // with unlimited or variable NAME_MAX. Many modern platforms guarantee
                    // thread safety for readdir() as long an individual DIR* is not accessed
                    // concurrently, which is sufficient for Rust.
                    errno::set_errno(errno::Errno(0));
                    let entry_ptr = libc::readdir64(self.dir.handle);

                    if entry_ptr.is_null() {
                        // We either encountered an error, or reached the end. Either way,
                        // the next call to next() should return None.
                        self.end_of_stream = true;

                        // To distinguish between errors and end-of-directory, we had to clear
                        // errno beforehand to check for an error now.
                        return match errno::errno().0 {
                            0 => None,
                            e => Some(Err(io::Error::from_raw_os_error(e))),
                        };
                    }

                    // d_name is guaranteed to be null-terminated.
                    let name =
                        CStr::from_ptr(entry_ptr.cast::<u8>().add(D_NAME_OFFSET).cast::<c_char>());

                    let name_bytes = name.to_bytes();

                    if name_bytes == b"." || name_bytes == b".." {
                        continue;
                    }

                    return Some(Ok(DirEntry {
                        file_name: OsString::from_vec(name_bytes.to_vec()),
                    }));
                }
            }
        }
    }
}

#[cfg(not(any(
    target_os = "android",
    target_os = "linux",
    target_os = "solaris",
    target_os = "fuchsia",
    target_os = "redox",
    target_os = "illumos",
    target_os = "aix",
    target_os = "nto",
    target_os = "vita",
    target_os = "hurd",
)))]
mod read_dir {
    use std::ffi::OsString;
    use std::io;
    use std::mem::MaybeUninit;
    use std::os::unix::ffi::OsStringExt;
    use std::ptr;
    use std::slice;

    use super::{DirEntry, ReadDir};

    impl ReadDir {
        pub(super) fn inner_next(&mut self) -> Option<io::Result<DirEntry>> {
            if self.end_of_stream {
                return None;
            }

            unsafe {
                loop {
                    let mut entry = MaybeUninit::zeroed();
                    let mut entry_ptr = ptr::null_mut();

                    let err = libc::readdir_r(self.dir.handle, entry.as_mut_ptr(), &mut entry_ptr);

                    if err != 0 {
                        if entry_ptr.is_null() {
                            // We encountered an error (which will be returned in this iteration), but
                            // we also reached the end of the directory stream. The `end_of_stream`
                            // flag is enabled to make sure that we return `None` in the next iteration
                            // (instead of looping forever)
                            self.end_of_stream = true;
                        }

                        return Some(Err(io::Error::from_raw_os_error(err)));
                    }

                    if entry_ptr.is_null() {
                        return None;
                    }

                    let entry = entry.assume_init();

                    let name_bytes = slice::from_raw_parts(
                        entry.d_name.as_ptr() as *const u8,
                        entry.d_namlen as usize,
                    );

                    if name_bytes == b"." || name_bytes == b".." {
                        continue;
                    }

                    return Some(Ok(DirEntry {
                        file_name: OsString::from_vec(name_bytes.to_vec()),
                    }));
                }
            }
        }
    }
}

pub(crate) struct DirEntry {
    file_name: OsString,
}

impl DirEntry {
    pub(crate) fn file_name(&self) -> OsString {
        self.file_name.clone()
    }
}

struct Dir {
    handle: *mut libc::DIR,
}

unsafe impl Send for Dir {}
unsafe impl Sync for Dir {}

impl Drop for Dir {
    #[inline]
    fn drop(&mut self) {
        _ = unsafe { libc::closedir(self.handle) };
    }
}

unsafe impl Send for OpenOptions {}
unsafe impl Sync for OpenOptions {}

#[derive(Clone, Debug)]
#[allow(clippy::struct_excessive_bools)]
pub(super) struct OpenOptions {
    // generic
    read: bool,
    write: bool,
    append: bool,
    truncate: bool,
    create: bool,
    create_new: bool,
}

impl OpenOptions {
    pub(super) fn new() -> OpenOptions {
        OpenOptions {
            // generic
            read: false,
            write: false,
            append: false,
            truncate: false,
            create: false,
            create_new: false,
        }
    }

    pub(super) fn read(&mut self, read: bool) {
        self.read = read;
    }

    pub(super) fn write(&mut self, write: bool) {
        self.write = write;
    }

    pub(super) fn append(&mut self, append: bool) {
        self.append = append;
    }

    pub(super) fn truncate(&mut self, truncate: bool) {
        self.truncate = truncate;
    }

    pub(super) fn create(&mut self, create: bool) {
        self.create = create;
    }

    pub(super) fn create_new(&mut self, create_new: bool) {
        self.create_new = create_new;
    }

    fn get_access_mode(&self) -> io::Result<i32> {
        match (self.read, self.write, self.append) {
            (true, false, false) => Ok(libc::O_RDONLY),
            (false, true, false) => Ok(libc::O_WRONLY),
            (true, true, false) => Ok(libc::O_RDWR),
            (false, _, true) => Ok(libc::O_WRONLY | libc::O_APPEND),
            (true, _, true) => Ok(libc::O_RDWR | libc::O_APPEND),
            (false, false, false) => Err(io::Error::from_raw_os_error(libc::EINVAL)),
        }
    }

    fn get_creation_mode(&self) -> io::Result<i32> {
        match (self.write, self.append) {
            (true, false) => {}
            (false, false) => {
                if self.truncate || self.create || self.create_new {
                    return Err(io::Error::from_raw_os_error(libc::EINVAL));
                }
            }
            (_, true) => {
                if self.truncate && !self.create_new {
                    return Err(io::Error::from_raw_os_error(libc::EINVAL));
                }
            }
        }

        Ok(match (self.create, self.truncate, self.create_new) {
            (false, false, false) => 0,
            (true, false, false) => libc::O_CREAT,
            (false, true, false) => libc::O_TRUNC,
            (true, true, false) => libc::O_CREAT | libc::O_TRUNC,
            (_, _, true) => libc::O_CREAT | libc::O_EXCL,
        })
    }
}

#[derive(Clone)]
pub(super) struct Metadata {
    stat: stat64,
}

impl Metadata {
    #[inline]
    pub(super) fn is_dir(&self) -> bool {
        self.stat.st_mode & libc::S_IFMT == libc::S_IFDIR
    }
}

fn is_current(path: &RelativePath) -> bool {
    path.components().all(|c| c == Component::CurDir)
}

fn convert_to_c_string(input: &RelativePath) -> io::Result<CString> {
    let mut path = Vec::new();

    for c in input.components() {
        match c {
            Component::CurDir => {}
            Component::ParentDir => {
                if path.is_empty() {
                    return Err(io::Error::from_raw_os_error(libc::EINVAL));
                }

                let index = path
                    .iter()
                    .rposition(|&b| b == MAIN_SEPARATOR as u8)
                    .unwrap_or(0);
                path.truncate(index);
            }
            Component::Normal(normal) => {
                if normal.as_bytes().contains(&b'\0') {
                    return Err(io::Error::from_raw_os_error(libc::EINVAL));
                }

                if !path.is_empty() {
                    path.push(b'/');
                }

                path.extend_from_slice(normal.as_bytes());
            }
        }
    }

    if path.is_empty() {
        path.push(b'.');
    }

    path.push(0);

    // SAFETY: We've checked safety requirements of CString above.
    let owned = unsafe { CString::from_vec_with_nul_unchecked(path) };
    Ok(owned)
}

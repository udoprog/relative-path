use std::ffi::c_char;
use std::ffi::{CStr, CString, OsString};
use std::fs::File;
use std::io;
use std::mem::{size_of, MaybeUninit};
use std::os::fd::AsRawFd;
use std::os::fd::FromRawFd;
use std::os::fd::OwnedFd;
use std::os::unix::ffi::OsStringExt;
use std::path::Path;

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
compile_error!("Unix platform is not supported");

use crate::{Component, RelativePath};

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
        let fd = if is_current(path) {
            self.handle.try_clone()?
        } else {
            let mut opts = OpenOptions::new();
            opts.read(true);
            self.open_at_inner(path, &opts)?
        };

        unsafe {
            let mut stat = MaybeUninit::zeroed();

            if libc::fstat64(fd.as_raw_fd(), stat.as_mut_ptr()) == -1 {
                return Err(io::Error::last_os_error());
            }

            let stat = stat.assume_init();

            Ok(Metadata { stat })
        }
    }

    pub(super) fn read_dir(&self, path: &RelativePath) -> io::Result<ReadDir> {
        let fd = if is_current(path) {
            self.handle.try_clone()?
        } else {
            let mut opts = OpenOptions::new();
            opts.read(true);
            self.open_at_inner(path, &opts)?
        };

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

    fn next(&mut self) -> Option<io::Result<DirEntry>> {
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

pub(super) struct DirEntry {
    file_name: OsString,
}

impl DirEntry {
    pub(super) fn file_name(&self) -> OsString {
        self.file_name.to_owned()
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

pub(super) struct Metadata {
    stat: libc::stat64,
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
        if !path.is_empty() {
            path.push(b'/');
        }

        match c {
            Component::CurDir => {}
            Component::ParentDir => {
                if path.is_empty() {
                    return Err(io::Error::from_raw_os_error(libc::EINVAL));
                }

                let index = path.iter().rposition(|&b| b == b'/').unwrap_or(0);
                path.truncate(index);
            }
            Component::Normal(normal) => {
                if normal.as_bytes().contains(&b'\0') {
                    return Err(io::Error::from_raw_os_error(libc::EINVAL));
                }

                path.extend_from_slice(normal.as_bytes());
            }
        }
    }

    path.push(0);

    // SAFETY: We've checked safety requirements of CString above.
    let owned = unsafe { CString::from_vec_with_nul_unchecked(path) };
    Ok(owned)
}

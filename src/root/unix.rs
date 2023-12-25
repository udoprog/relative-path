use std::ffi::CString;
use std::fs::File;
use std::io;
use std::os::fd::AsRawFd;
use std::os::fd::FromRawFd;
use std::os::fd::OwnedFd;
use std::path::Path;

use crate::{Component, RelativePath};

#[derive(Debug)]
pub(super) struct Root {
    handle: OwnedFd,
}

impl Root {
    pub(super) fn new<P>(path: P) -> io::Result<Self>
    where
        P: AsRef<Path>,
    {
        let file = std::fs::OpenOptions::new().read(true).open(path)?;

        Ok(Root {
            handle: OwnedFd::from(file),
        })
    }

    pub(super) fn open_at<P>(&self, path: P, options: &OpenOptions) -> io::Result<File>
    where
        P: AsRef<RelativePath>,
    {
        let path = convert_to_c_string(path.as_ref())?;

        let flags = libc::O_CLOEXEC | options.get_creation_mode()? | options.get_access_mode()?;

        unsafe {
            let fd = libc::openat(self.handle.as_raw_fd(), path.as_ptr(), flags);

            if fd == -1 {
                return Err(io::Error::last_os_error());
            }

            Ok(File::from_raw_fd(fd))
        }
    }
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
    unsafe { Ok(CString::from_vec_with_nul_unchecked(path)) }
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

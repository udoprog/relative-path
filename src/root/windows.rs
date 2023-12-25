use std::ffi::c_void;
use std::fs::File;
use std::io;
use std::mem;
use std::mem::size_of;
use std::mem::MaybeUninit;
use std::os::windows::fs::OpenOptionsExt;
use std::os::windows::io::{AsRawHandle, FromRawHandle, OwnedHandle};
use std::path::Path;
use std::path::MAIN_SEPARATOR;
use std::path::MAIN_SEPARATOR_STR;
use std::ptr;

use windows_sys::Wdk::Foundation::OBJECT_ATTRIBUTES;
use windows_sys::Wdk::Storage::FileSystem::FILE_SYNCHRONOUS_IO_ALERT;
use windows_sys::Wdk::Storage::FileSystem::{self as nt, NtCreateFile};
use windows_sys::Win32::Foundation::STATUS_SUCCESS;
use windows_sys::Win32::Foundation::{
    RtlNtStatusToDosError, ERROR_INVALID_PARAMETER, HANDLE, STATUS_PENDING, UNICODE_STRING,
};
use windows_sys::Win32::Storage::FileSystem as c;
use windows_sys::Win32::System::IO::IO_STATUS_BLOCK;

use crate::Component;
use crate::RelativePath;

#[derive(Debug)]
pub(super) struct Root {
    handle: OwnedHandle,
}

impl Root {
    pub(super) fn new<P>(path: P) -> io::Result<Self>
    where
        P: AsRef<Path>,
    {
        let file = std::fs::OpenOptions::new()
            .read(true)
            .attributes(c::FILE_FLAG_BACKUP_SEMANTICS)
            .open(path)?;

        Ok(Root {
            handle: OwnedHandle::from(file),
        })
    }

    pub(super) fn open_at<P>(&self, path: P, options: &OpenOptions) -> io::Result<File>
    where
        P: AsRef<RelativePath>,
    {
        let path = encode_path_wide(&path)?;

        // SAFETY: All the operations and parameters are correctly used.
        unsafe {
            let len = mem::size_of_val(&path[..]);

            let string = UNICODE_STRING {
                Length: len as u16,
                MaximumLength: len as u16,
                Buffer: path.as_ptr() as *mut u16,
            };

            let attributes = OBJECT_ATTRIBUTES {
                Length: size_of::<OBJECT_ATTRIBUTES>() as u32,
                RootDirectory: self.handle.as_raw_handle() as HANDLE,
                ObjectName: &string,
                Attributes: 0,
                SecurityDescriptor: ptr::null(),
                SecurityQualityOfService: ptr::null(),
            };

            let mut status_block = IO_STATUS_BLOCK {
                Anonymous: windows_sys::Win32::System::IO::IO_STATUS_BLOCK_0 {
                    Status: STATUS_PENDING,
                },
                Information: 0,
            };

            let mut handle = MaybeUninit::zeroed();

            let status = NtCreateFile(
                handle.as_mut_ptr(),
                options.get_access_mode()?,
                &attributes,
                &mut status_block,
                ptr::null_mut(),
                0,
                options.share_mode,
                options.get_creation_mode()?,
                FILE_SYNCHRONOUS_IO_ALERT,
                ptr::null(),
                0,
            );

            if status != STATUS_SUCCESS {
                return Err(io::Error::from_raw_os_error(
                    RtlNtStatusToDosError(status) as i32
                ));
            }

            let handle = handle.assume_init();
            Ok(File::from_raw_handle(handle as *mut c_void))
        }
    }
}

fn encode_path_wide<P>(path: &P) -> io::Result<Vec<u16>>
where
    P: AsRef<RelativePath>,
{
    let path = path.as_ref();
    let mut output = Vec::with_capacity(path.as_str().len() * 2);

    let mut separator = [0; 2];
    MAIN_SEPARATOR.encode_utf16(&mut separator);
    let separator = &separator[..];

    for c in path.components() {
        if !output.is_empty() {
            output.extend(MAIN_SEPARATOR_STR.encode_utf16());
        }

        match c {
            Component::CurDir => {}
            Component::ParentDir => {
                if output.is_empty() {
                    return Err(io::Error::from_raw_os_error(ERROR_INVALID_PARAMETER as i32));
                }

                let index = output
                    .windows(2)
                    .rposition(|window| window == separator)
                    .unwrap_or(0);

                output.truncate(index);
            }
            Component::Normal(normal) => {
                output.extend(normal.encode_utf16());
            }
        }
    }

    Ok(output)
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
    // system-specific
    share_mode: u32,
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
            // system-specific
            share_mode: c::FILE_SHARE_READ | c::FILE_SHARE_WRITE | c::FILE_SHARE_DELETE,
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

    fn get_access_mode(&self) -> io::Result<u32> {
        // NtCreateFile does not support `GENERIC_READ`.
        const DEFAULT_READ: u32 = c::STANDARD_RIGHTS_READ
            | c::SYNCHRONIZE
            | c::FILE_READ_DATA
            | c::FILE_READ_EA
            | c::FILE_READ_ATTRIBUTES;

        const DEFAULT_WRITE: u32 = c::STANDARD_RIGHTS_WRITE
            | c::SYNCHRONIZE
            | c::FILE_WRITE_DATA
            | c::FILE_WRITE_EA
            | c::FILE_WRITE_ATTRIBUTES;

        match (self.read, self.write, self.append) {
            (true, false, false) => Ok(DEFAULT_READ),
            (false, true, false) => Ok(DEFAULT_WRITE),
            (true, true, false) => Ok(DEFAULT_READ | DEFAULT_WRITE),
            (false, _, true) => Ok(c::FILE_GENERIC_WRITE & !c::FILE_WRITE_DATA),
            (true, _, true) => Ok(DEFAULT_READ | (c::FILE_GENERIC_WRITE & !c::FILE_WRITE_DATA)),
            (false, false, false) => {
                Err(io::Error::from_raw_os_error(ERROR_INVALID_PARAMETER as i32))
            }
        }
    }

    fn get_creation_mode(&self) -> io::Result<u32> {
        match (self.write, self.append) {
            (true, false) => {}
            (false, false) => {
                if self.truncate || self.create || self.create_new {
                    return Err(io::Error::from_raw_os_error(ERROR_INVALID_PARAMETER as i32));
                }
            }
            (_, true) => {
                if self.truncate && !self.create_new {
                    return Err(io::Error::from_raw_os_error(ERROR_INVALID_PARAMETER as i32));
                }
            }
        }

        Ok(match (self.create, self.truncate, self.create_new) {
            (false, false, false) => nt::FILE_OPEN,
            (true, false, false) => nt::FILE_OPEN_IF,
            (false, true, false) => nt::FILE_OVERWRITE,
            (true, true, false) => nt::FILE_OVERWRITE_IF,
            (_, _, true) => nt::FILE_CREATE,
        })
    }
}

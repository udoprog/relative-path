use std::ffi::OsString;
use std::fs::File;
use std::mem;
use std::mem::size_of;
use std::mem::MaybeUninit;
use std::os::windows::ffi::OsStringExt;
use std::os::windows::fs::OpenOptionsExt;
use std::os::windows::io::{AsRawHandle, FromRawHandle, OwnedHandle, RawHandle};
use std::path::Path;
use std::path::MAIN_SEPARATOR;
use std::ptr;
use std::{io, slice};

use windows_sys::Wdk::Foundation::OBJECT_ATTRIBUTES;
use windows_sys::Wdk::Storage::FileSystem as nt;
use windows_sys::Wdk::System::SystemServices::SL_RESTART_SCAN;
use windows_sys::Win32::Foundation::FALSE;
use windows_sys::Win32::Foundation::{
    RtlNtStatusToDosError, ERROR_INVALID_PARAMETER, HANDLE, STATUS_NO_MORE_FILES, STATUS_PENDING,
    STATUS_SUCCESS, UNICODE_STRING,
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
    pub(super) fn new(path: &Path) -> io::Result<Self> {
        let file = std::fs::OpenOptions::new()
            .read(true)
            .attributes(c::FILE_FLAG_BACKUP_SEMANTICS)
            .open(path)?;

        Ok(Root {
            handle: OwnedHandle::from(file),
        })
    }

    pub(super) fn open_at(&self, path: &RelativePath, options: &OpenOptions) -> io::Result<File> {
        let handle = self.open_at_inner(path, options)?;
        Ok(File::from(handle))
    }

    pub(super) fn open_at_inner(
        &self,
        path: &RelativePath,
        options: &OpenOptions,
    ) -> io::Result<OwnedHandle> {
        let path = encode_path_wide(path)?;

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

            let status = nt::NtCreateFile(
                handle.as_mut_ptr(),
                options.get_access_mode()?,
                &attributes,
                &mut status_block,
                ptr::null_mut(),
                0,
                options.share_mode,
                options.get_creation_mode()?,
                nt::FILE_SYNCHRONOUS_IO_ALERT | options.custom_create_options,
                ptr::null(),
                0,
            );

            if status != STATUS_SUCCESS {
                return Err(io::Error::from_raw_os_error(
                    RtlNtStatusToDosError(status) as i32
                ));
            }

            Ok(OwnedHandle::from_raw_handle(
                handle.assume_init() as RawHandle
            ))
        }
    }

    pub(super) fn metadata(&self, path: &RelativePath) -> io::Result<Metadata> {
        let handle = if is_current(path) {
            self.handle.try_clone()?
        } else {
            let mut opts = OpenOptions::new();
            opts.read(true);
            opts.access_mode = Some(c::FILE_READ_ATTRIBUTES);
            // No read or write permissions are necessary
            // opts.access_mode = Some(0);
            // opts.custom_create_options = nt::FILE_OPEN_FOR_BACKUP_INTENT;
            self.open_at_inner(path, &opts)?
        };

        unsafe {
            let mut info = MaybeUninit::zeroed();

            if c::GetFileInformationByHandle(handle.as_raw_handle() as isize, info.as_mut_ptr())
                == FALSE
            {
                return Err(io::Error::last_os_error());
            }

            let info = info.assume_init();

            Ok(Metadata {
                attributes: info.dwFileAttributes,
            })
        }
    }

    pub(super) fn read_dir(&self, path: &RelativePath) -> io::Result<ReadDir> {
        let handle = if is_current(path) {
            self.handle.try_clone()?
        } else {
            let mut opts = OpenOptions::new();
            opts.access_mode = Some(c::SYNCHRONIZE | c::FILE_LIST_DIRECTORY);
            self.open_at_inner(path, &opts)?
        };

        Ok(ReadDir {
            handle,
            buffer: [0; 1024],
            at: None,
            first: true,
        })
    }
}

pub(super) struct ReadDir {
    handle: OwnedHandle,
    buffer: [u8; 1024],
    first: bool,
    at: Option<usize>,
}

impl Iterator for ReadDir {
    type Item = io::Result<DirEntry>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            while let Some(at) = self.at.take() {
                unsafe {
                    let file_names = &*self.buffer[at..]
                        .as_ptr()
                        .cast::<nt::FILE_NAMES_INFORMATION>();

                    let len = file_names.FileNameLength;
                    let ptr = file_names.FileName.as_ptr();
                    let name = slice::from_raw_parts(ptr, len as usize / 2);

                    if file_names.NextEntryOffset != 0 {
                        self.at = Some(at + file_names.NextEntryOffset as usize);
                    }

                    if let Some(entry) = DirEntry::new(name) {
                        return Some(Ok(entry));
                    }
                }
            }

            unsafe {
                let mut status_block = IO_STATUS_BLOCK {
                    Anonymous: windows_sys::Win32::System::IO::IO_STATUS_BLOCK_0 {
                        Status: STATUS_PENDING,
                    },
                    Information: 0,
                };

                let status = nt::NtQueryDirectoryFileEx(
                    self.handle.as_raw_handle() as HANDLE,
                    0,
                    None,
                    ptr::null(),
                    &mut status_block,
                    self.buffer.as_mut_ptr().cast(),
                    self.buffer.len() as u32,
                    12, // FileNamesInformation
                    if mem::take(&mut self.first) {
                        SL_RESTART_SCAN
                    } else {
                        0
                    },
                    ptr::null(),
                );

                if status == STATUS_NO_MORE_FILES {
                    return None;
                }

                if status != STATUS_SUCCESS {
                    return Some(Err(io::Error::from_raw_os_error(
                        RtlNtStatusToDosError(status) as i32,
                    )));
                }

                self.at = Some(0);
            }
        }
    }
}

struct FindNextFileHandle(HANDLE);

unsafe impl Send for FindNextFileHandle {}
unsafe impl Sync for FindNextFileHandle {}

pub(super) struct DirEntry {
    file_name: OsString,
}

impl DirEntry {
    fn new(data: &[u16]) -> Option<Self> {
        match data {
            // check for '.' and '..'
            [46] | [46, 46] => return None,
            _ => {}
        }

        Some(DirEntry {
            file_name: OsString::from_wide(data),
        })
    }

    pub(super) fn file_name(&self) -> OsString {
        self.file_name.to_owned()
    }
}

impl Drop for FindNextFileHandle {
    fn drop(&mut self) {
        let r = unsafe { c::FindClose(self.0) };
        debug_assert!(r != 0);
    }
}

fn is_current(path: &RelativePath) -> bool {
    path.components().all(|c| c == Component::CurDir)
}

fn encode_path_wide(path: &RelativePath) -> io::Result<Vec<u16>> {
    let mut output = Vec::with_capacity(path.as_str().len() * 2);

    let mut separator = [0; 2];
    MAIN_SEPARATOR.encode_utf16(&mut separator);
    let separator = &separator[..];

    for c in path.components() {
        if !output.is_empty() {
            output.extend_from_slice(MAIN_SEPARATOR.encode_utf16(&mut [0; 2]));
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

                output.truncate(index * 2);
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
    custom_create_options: u32,
    share_mode: u32,
    access_mode: Option<u32>,
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
            custom_create_options: 0,
            share_mode: c::FILE_SHARE_READ | c::FILE_SHARE_WRITE | c::FILE_SHARE_DELETE,
            access_mode: None,
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
        const DEFAULT_READ: u32 =
            c::STANDARD_RIGHTS_READ | c::FILE_READ_DATA | c::FILE_READ_EA | c::FILE_READ_ATTRIBUTES;

        const DEFAULT_WRITE: u32 = c::STANDARD_RIGHTS_WRITE
            | c::FILE_WRITE_DATA
            | c::FILE_WRITE_EA
            | c::FILE_WRITE_ATTRIBUTES;

        let access_mode = match (self.read, self.write, self.append, self.access_mode) {
            (_, _, _, Some(access_mode)) => access_mode,
            (true, false, false, _) => DEFAULT_READ,
            (false, true, false, _) => DEFAULT_WRITE,
            (true, true, false, _) => DEFAULT_READ | DEFAULT_WRITE,
            (false, _, true, _) => c::FILE_GENERIC_WRITE & !c::FILE_WRITE_DATA,
            (true, _, true, _) => DEFAULT_READ | (c::FILE_GENERIC_WRITE & !c::FILE_WRITE_DATA),
            (false, false, false, _) => {
                return Err(io::Error::from_raw_os_error(ERROR_INVALID_PARAMETER as i32));
            }
        };

        Ok(access_mode | c::SYNCHRONIZE)
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

#[derive(Clone)]
pub(super) struct Metadata {
    attributes: u32,
}

impl Metadata {
    #[inline]
    pub(super) fn is_dir(&self) -> bool {
        self.attributes & c::FILE_ATTRIBUTE_DIRECTORY != 0
    }
}

//! [<img alt="github" src="https://img.shields.io/badge/github-udoprog/relative--path-8da0cb?style=for-the-badge&logo=github" height="20">](https://github.com/udoprog/relative-path)
//! [<img alt="crates.io" src="https://img.shields.io/crates/v/relative-path-utils.svg?style=for-the-badge&color=fc8d62&logo=rust" height="20">](https://crates.io/crates/relative-path-utils)
//! [<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-relative--path--utils-66c2a5?style=for-the-badge&logoColor=white&logo=data:image/svg+xml;base64,PHN2ZyByb2xlPSJpbWciIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyIgdmlld0JveD0iMCAwIDUxMiA1MTIiPjxwYXRoIGZpbGw9IiNmNWY1ZjUiIGQ9Ik00ODguNiAyNTAuMkwzOTIgMjE0VjEwNS41YzAtMTUtOS4zLTI4LjQtMjMuNC0zMy43bC0xMDAtMzcuNWMtOC4xLTMuMS0xNy4xLTMuMS0yNS4zIDBsLTEwMCAzNy41Yy0xNC4xIDUuMy0yMy40IDE4LjctMjMuNCAzMy43VjIxNGwtOTYuNiAzNi4yQzkuMyAyNTUuNSAwIDI2OC45IDAgMjgzLjlWMzk0YzAgMTMuNiA3LjcgMjYuMSAxOS45IDMyLjJsMTAwIDUwYzEwLjEgNS4xIDIyLjEgNS4xIDMyLjIgMGwxMDMuOS01MiAxMDMuOSA1MmMxMC4xIDUuMSAyMi4xIDUuMSAzMi4yIDBsMTAwLTUwYzEyLjItNi4xIDE5LjktMTguNiAxOS45LTMyLjJWMjgzLjljMC0xNS05LjMtMjguNC0yMy40LTMzLjd6TTM1OCAyMTQuOGwtODUgMzEuOXYtNjguMmw4NS0zN3Y3My4zek0xNTQgMTA0LjFsMTAyLTM4LjIgMTAyIDM4LjJ2LjZsLTEwMiA0MS40LTEwMi00MS40di0uNnptODQgMjkxLjFsLTg1IDQyLjV2LTc5LjFsODUtMzguOHY3NS40em0wLTExMmwtMTAyIDQxLjQtMTAyLTQxLjR2LS42bDEwMi0zOC4yIDEwMiAzOC4ydi42em0yNDAgMTEybC04NSA0Mi41di03OS4xbDg1LTM4Ljh2NzUuNHptMC0xMTJsLTEwMiA0MS40LTEwMi00MS40di0uNmwxMDItMzguMiAxMDIgMzguMnYuNnoiPjwvcGF0aD48L3N2Zz4K" height="20">](https://docs.rs/relative-path-utils)
//!
//! Utilities for working with relative paths.
//!
//! This crate contains:
//! * [`Root`] the `root` feature - A root directory that can be used to open
//!   files relative to it.
//! * [`Glob`] the `root` feature - A glob pattern that can be used to match
//!   files relative to a [`Root`].
//!
//! [`Root`]: https://docs.rs/relative-path-utils/latest/relative_path_utils/struct.Root.html
//! [`Glob`]: https://docs.rs/relative-path-utils/latest/relative_path_utils/struct.Glob.html

#![deny(missing_docs)]
#![no_std]
#![cfg_attr(relative_path_docsrs, feature(doc_cfg))]

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

#[cfg(feature = "root")]
#[cfg_attr(relative_path_docsrs, doc(cfg(feature = "root")))]
#[doc(inline)]
pub use self::root::{DirEntry, Metadata, OpenOptions, ReadDir, Root};
#[cfg(feature = "root")]
mod root;

#[cfg(feature = "root")]
#[cfg_attr(relative_path_docsrs, doc(cfg(feature = "root")))]
#[doc(inline)]
pub use self::glob::Glob;
#[cfg(feature = "root")]
mod glob;

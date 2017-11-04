# relative-path

Portable, relative paths for Rust.

[![Build Status](https://api.travis-ci.org/udoprog/relative-path.svg?branch=master)](https://travis-ci.org/udoprog/relative-path)

[Documentation](https://docs.rs/relative-path)

## Relative Paths

This library provides two structures: `RelativePath` and `RelativePathBuf`.
These are analogous to the `Path` and `PathBuf` structures provided through standard rust.

While `Path` provides an API that adapts to a given platform, `RelativePath` is platform-neutral.

`RelativePath` only uses `/` as a separator. Anything else will be considered part of distinct
components.

Only relative paths are permitted to be represented using this structure.
Conversion to `Path` can only happen if it is provided which path it is relative to, through the
`to_path_buf` function.

```rust
let relative_path = RelativePath::new("foo/bar");
let path = Path::new("C:\\");
let full_path = relative_path.to_path_buf(path);
```

## Portability Note

`RelativePath` similarly to `Path` makes no guarantees that the components represented in them
makes up a legal filesystem path.
Notable, `NUL` is not permitted on most unix platforms (this is a terminator in C-based filesystem
APIs).
Windows also has a number of [reserved characters][windows].

[windows]: https://msdn.microsoft.com/en-us/library/windows/desktop/aa365247(v=vs.85).aspx

## TODO

* Verify that relative paths are - indeed - portable.
* Serde support.
* Better function documentation with examples.
* Support more `Path`-like functions.

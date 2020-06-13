[![Build Status](https://github.com/udoprog/relative-path/workflows/Rust/badge.svg)](https://github.com/udoprog/relative-path/actions)
[![crates.io](https://img.shields.io/crates/v/relative-path.svg?maxAge=2592000)](https://crates.io/crates/relative-path)

# relative-path

Portable, relative paths for Rust.

[Documentation](https://docs.rs/relative-path)

## Relative Paths

This library provides two types: `RelativePath` and `RelativePathBuf`.
These are analogous to the `Path` and `PathBuf` structures provided through standard Rust.

While `Path` provides an API that adapts to a given platform, `RelativePath` does not.
Instead `RelativePath` uses a fixed, slash-separated representation regardless of platform.

Windows permits using drive volumes as a prefix (e.g. `"c:\"`) and backslash (`\`) as a separator.
Storing paths like this would build and run on one platform, but not others.
Another hairy issue is that data serialized for one platform through serde might not be
usable on another:

```rust
#[derive(Serialize, Deserialize)]
struct Message {
    path: PathBuf,
}
```

Since `RelativePath` only uses `/` as a separator it avoids this issue.
Anything non-slash else will be considered part of a distinc component.

Conversion to `Path` may only happen if it is known which path it is relative to through the
`to_path` function. This is where the relative part of the name comes from.

```rust
let relative_path = RelativePath::new("foo/bar");
let path = Path::new("C:\\");
let full_path = relative_path.to_path(path);
```

This would permit relative paths to portably be used in project manifests or configurations.
Where files are referenced from some specific, well-known point in the filesystem.

The following is an example configuration for a made up project:

```toml
lib = "src/lib.rs"
bin = "src/bin/hello.rs"
```

The corresponding Rust struct to deserialize it would look like this:

```rust
#[derive(Deserialize)]
pub struct Manifest {
    lib: RelativePathBuf,
    bin: RelativePathBuf,
}
```

## Portability Note

`RelativePath`, similarly to `Path`, makes no guarantees that the components represented in them
makes up legal file names.

`NUL` is not permitted on unix platforms - this is a terminator in C-based filesystem APIs. Slash
(`/`) is also used as a path separator.

Windows has a number of [reserved characters][windows].

[windows]: https://msdn.microsoft.com/en-us/library/windows/desktop/aa365247(v=vs.85).aspx
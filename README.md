# relative-path

Portable, relative paths for Rust.

[![Build Status](https://api.travis-ci.org/udoprog/relative-path.svg?branch=master)](https://travis-ci.org/udoprog/relative-path)
[![Build status](https://ci.appveyor.com/api/projects/status/x2spyavt5fe6lbeq?svg=true)](https://ci.appveyor.com/project/udoprog/relative-path/branch/master)

[Documentation](https://docs.rs/relative-path)

## Relative Paths

This library provides two structures: `RelativePath` and `RelativePathBuf`.
These are analogous to the `Path` and `PathBuf` structures provided through standard Rust.

While `Path` provides an API that adapts to a given platform, `RelativePath` does not, making the
representations it provide platform-neutral.

The representation of Rust's `Path` is not portable since it permits different things across
platforms.

Windows permit using drive volumes (e.g. `"c:\"`) and backslash (`\`) as a separator.
Using this to store relative paths would make it possible for software developers working to target
Windows to build projects which work on their platform, but not others.

`RelativePath` only uses `/` as a separator. Anything else will be considered part of distinct
components.

Conversion to `Path` can only happen if it is known which path it is relative to, through the
`to_path` function. This is where the 'relative' part of the name comes from.

```rust
let relative_path = RelativePath::new("foo/bar");
let path = Path::new("C:\\");
let full_path = relative_path.to_path(path);
```

This would for example, permit relative paths to portably be used in project manifests or
configurations, where files are references from some specific, well-known point in the filesystem.

The following is a simple example configuration for a made up project:

```toml
lib = "src/lib.rs"
bin = "src/bin/hello.rs"
```

The corresponding Rust struct could look like this:

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

## TODO

 * Verify that relative paths are - indeed - portable.
 * Better function documentation with examples.
 * Support more `Path`-like functions.

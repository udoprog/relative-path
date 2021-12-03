[![Build Status](https://github.com/udoprog/relative-path/workflows/Rust/badge.svg)](https://github.com/udoprog/relative-path/actions)
[![crates.io](https://img.shields.io/crates/v/relative-path.svg)](https://crates.io/crates/relative-path)
[![docs.rs](https://docs.rs/relative-path/badge.svg)](https://docs.rs/relative-path)
[![discord](https://img.shields.io/discord/558644981137670144.svg?logo=discord&style=flat-square)](https://discord.gg/v5AeNkT)

# relative-path

Portable relative UTF-8 paths for Rust.

This provide a module analogous to [std::path], with the following
characteristics:

* The path separator is set to a fixed character (`/`), regardless of
  platform.
* Relative paths cannot represent a path in the filesystem without first
  specifying what they are *relative to* through [to_path].
* Relative paths are always guaranteed to be a UTF-8 string.

On top of this we support many path-like operations that guarantee portable
behavior.

### Serde Support

This library includes serde support that can be enabled with the `serde`
feature.

### Why is `std::path` a portability hazard?

Path representations differ across platforms.

* Windows permits using drive volumes (multiple roots) as a prefix (e.g.
  `"c:\"`) and backslash (`\`) as a separator.
* Unix references absolute paths from a single root and uses slash (`/`) as
  a separator.

If we use `PathBuf`, Storing paths like this in a manifest would happily
allow our applications to build and run on one platform, but potentially not
others.

Consider the following manifest:

```rust
use std::path::PathBuf;
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize)]
struct Manifest {
    source: PathBuf,
}
```

Which represents this TOML file:

```toml
# Uh oh, trouble.
source = "C:\\path\\to\\source"
```

Assuming `"C:\\path\\to\\source"` is a legal path on Windows, this will
happily run for one platform when checked into source control but not
others.

Since [RelativePath] strictly uses `/` as a separator it avoids this issue.
Anything non-slash will simply be considered part of a *distinct component*.

Conversion to [Path] may only happen if it is known which path it is
relative to through the [to_path] or [to_logical_path] functions. This is
where the relative part of the name comes from.

```rust
use relative_path::RelativePath;
use std::path::Path;

// to_path unconditionally concatenates a relative path with its base:
let relative_path = RelativePath::new("../foo/./bar");
let full_path = relative_path.to_path("C:\\");
assert_eq!(full_path, Path::new("C:\\..\\foo\\.\\bar"));

// to_logical_path tries to apply the logical operations that the relative
// path corresponds to:
let relative_path = RelativePath::new("../foo/./bar");
let full_path = relative_path.to_logical_path("C:\\baz");
assert_eq!(full_path, Path::new("C:\\foo\\bar"));
```

This would permit relative paths to portably be used in project manifests or
configurations. Where files are referenced from some specific, well-known
point in the filesystem.

```toml
source = "path/to/source"
```

The fixed manifest would look like this:

```rust
use relative_path::RelativePathBuf;
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize)]
pub struct Manifest {
    source: RelativePathBuf,
}
```

### Overview

When two relative paths are compared to each other, their exact component
makeup determines equality.

```rust
use relative_path::RelativePath;

assert_ne!(
    RelativePath::new("foo/bar/../baz"),
    RelativePath::new("foo/baz")
);
```

Using platform-specific path separators to construct relative paths is not
supported.

Path separators from other platforms are simply treated as part of a
component:

```rust
use relative_path::RelativePath;

assert_ne!(
    RelativePath::new("foo/bar"),
    RelativePath::new("foo\\bar")
);

assert_eq!(1, RelativePath::new("foo\\bar").components().count());
assert_eq!(2, RelativePath::new("foo/bar").components().count());
```

To see if two relative paths are equivalent you can use [normalize]:

```rust
use relative_path::RelativePath;

assert_eq!(
    RelativePath::new("foo/bar/../baz").normalize(),
    RelativePath::new("foo/baz").normalize(),
);
```

### Additional portability notes

While relative paths avoid the most egregious portability issues, namely
that absolute paths will work equally unwell on all platforms. We do not
avoid all.

This section tries to document additional portability issues that we know
about.

[RelativePath], similarly to [Path], makes no guarantees that the components
represented in them makes up legal file names. While components are strictly
separated by slashes, we can still store things in path components which may
not be used as legal paths on all platforms.

* `NUL` is not permitted on unix platforms - this is a terminator in C-based
  filesystem APIs. Slash (`/`) is also used as a path separator.
* Windows has a number of [reserved characters and names][windows-reserved].

A relative path that *actually* contains a platform-specific absolute path
will result in a nonsensical path being generated.

```rust
use relative_path::RelativePath;
use std::path::Path;

if cfg!(windows) {
    assert_eq!(
        Path::new("foo\\c:\\bar\\baz"),
        RelativePath::new("c:\\bar\\baz").to_path("foo")
    );
}

if cfg!(unix) {
    assert_eq!(
        Path::new("foo/bar/baz"),
        RelativePath::new("/bar/baz").to_path("foo")
    );
}
```

This is intentional in order to cause an early breakage when a platform
encounters paths like `"foo/c:\\bar\\baz"` to signal that it is a
portability hazard. On Unix it's a bit more subtle with `""foo/bar/baz""`,
since the leading slash (`/`) will simply be ignored. The hope is that it
will be more probable to cause an early error unless a compatible relative
path *also* exists.

[windows-reserved]: https://msdn.microsoft.com/en-us/library/windows/desktop/aa365247(v=vs.85).aspx
[RelativePath]: https://docs.rs/relative-path/1/relative_path/struct.RelativePath.html
[to_path]: https://docs.rs/relative-path/1/relative_path/struct.RelativePath.html#method.to_path
[to_logical_path]: https://docs.rs/relative-path/1/relative_path/struct.RelativePath.html#method.to_logical_path
[normalize]: https://docs.rs/relative-path/1/relative_path/struct.RelativePath.html#method.normalize
[None]: https://doc.rust-lang.org/std/option/enum.Option.html
[std::path]: https://doc.rust-lang.org/std/path/index.html
[Path]: https://doc.rust-lang.org/std/path/struct.Path.html

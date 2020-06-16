# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [1.2.1] - 2020-06-16

### Changed
* Change signature of `RelativePath::strip_prefix` to be the same as `std::path::Path` ([#16]).

## [1.2.0] - 2020-06-13

### Added
* Added `FromPathError::kind` to get more detailed error information ([#15]).

### Changed
* Marked `FromPathErrorKind` `#[non_exhaustive]` which technically is a breaking
  change. But since it was not accessible from API code of this library, anyone
  who used it outside are on their own.

## [1.1.1] - 2020-06-13

### Changed
* Deprecated use of `std::error::Error::description` in favor of just having a `std::fmt::Display` impl.

## [1.1.0] - 2020-06-13

### Added
* Added `RelativePath::relative` to render a path relative from one path to another ([#14]).

[#16]: https://github.com/udoprog/relative-path/pull/16
[#15]: https://github.com/udoprog/relative-path/pull/15
[#14]: https://github.com/udoprog/relative-path/pull/14

[Unreleased]: https://github.com/udoprog/relative-path/compare/1.2.1...master
[1.2.1]: https://github.com/udoprog/relative-path/compare/1.2.0...1.2.1
[1.2.0]: https://github.com/udoprog/relative-path/compare/1.1.1...1.2.0
[1.1.1]: https://github.com/udoprog/relative-path/compare/1.1.0...1.1.1
[1.1.0]: https://github.com/udoprog/relative-path/compare/1.0.0...1.1.0

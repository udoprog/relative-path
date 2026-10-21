#![cfg(all(feature = "musli02", feature = "alloc"))]

use musli::{Allocator, Decode, Decoder, Encode};
use relative_path::{RelativePath, RelativePathBuf};

#[derive(Debug, PartialEq, Encode, Decode)]
struct Owned {
    buf: RelativePathBuf,
    boxed: Box<RelativePath>,
}

#[derive(Debug, PartialEq, Encode, Decode)]
struct Borrowed<'a> {
    path: &'a RelativePath,
}

fn owned() -> Owned {
    Owned {
        buf: RelativePathBuf::from("foo/bar"),
        boxed: Box::from(RelativePath::new("../baz/./qux")),
    }
}

#[test]
fn storage_roundtrip() {
    let value = owned();
    let bytes = musli::storage::to_vec(&value).unwrap();
    assert_eq!(musli::storage::from_slice::<Owned>(&bytes).unwrap(), value);

    let value = Borrowed {
        path: RelativePath::new("foo/bar"),
    };
    let bytes = musli::storage::to_vec(&value).unwrap();
    let decoded = musli::storage::from_slice::<Borrowed<'_>>(&bytes).unwrap();
    assert_eq!(decoded, value);
}

#[test]
fn json_roundtrip() {
    let value = owned();
    let json = musli::json::to_string(&value).unwrap();
    assert_eq!(musli::json::from_str::<Owned>(&json).unwrap(), value);

    let value = Borrowed {
        path: RelativePath::new("foo/bar"),
    };
    let json = musli::json::to_string(&value).unwrap();
    assert_eq!(musli::json::from_str::<Borrowed<'_>>(&json).unwrap(), value);
}

#[test]
fn encodes_as_string() {
    let path = RelativePath::new("foo/bar");
    let expected = musli::json::to_string("foo/bar").unwrap();
    assert_eq!(expected, "\"foo/bar\"");

    assert_eq!(musli::json::to_string(path).unwrap(), expected);
    assert_eq!(
        musli::json::to_string(&path.to_relative_path_buf()).unwrap(),
        expected
    );
    assert_eq!(
        musli::json::to_string(&Box::<RelativePath>::from(path)).unwrap(),
        expected
    );
    assert_eq!(
        musli::storage::to_vec(path).unwrap(),
        musli::storage::to_vec("foo/bar").unwrap()
    );
}

#[test]
fn owned_decode_from_unborrowable_input() {
    // The escape forces the decoder to unescape into a buffer.
    let json = r#""foo\/bar""#;
    assert_eq!(
        musli::json::from_str::<RelativePathBuf>(json).unwrap(),
        RelativePath::new("foo/bar")
    );
    assert_eq!(
        &*musli::json::from_str::<Box<RelativePath>>(json).unwrap(),
        RelativePath::new("foo/bar")
    );
    assert!(musli::json::from_str::<&RelativePath>(json).is_err());
}

struct Components(Vec<String>);

impl<'de, M, A> Decode<'de, M, A> for Components
where
    A: Allocator,
{
    fn decode<D>(decoder: D) -> Result<Self, D::Error>
    where
        D: Decoder<'de, Mode = M, Allocator = A>,
    {
        decoder.decode_unsized(|path: &RelativePath| {
            Ok(Components(
                path.components().map(|c| c.as_str().to_owned()).collect(),
            ))
        })
    }
}

#[test]
fn decode_unsized() {
    let bytes = musli::storage::to_vec(RelativePath::new("foo/../bar/baz")).unwrap();
    let Components(components) = musli::storage::from_slice(&bytes).unwrap();
    assert_eq!(components, ["foo", "..", "bar", "baz"]);

    let Components(components) = musli::json::from_str(r#""a\/b""#).unwrap();
    assert_eq!(components, ["a", "b"]);
}

//! Implementations of the [`musli` 0.2] traits, with the same string
//! representation as the `serde` implementations.
//!
//! [`musli` 0.2]: https://docs.rs/musli/0.2

#[cfg(feature = "alloc")]
use alloc::boxed::Box;

use musli_core02::de::DecodeUnsized;
use musli_core02::{Allocator, Decode, Decoder, Encode, Encoder};

use crate::RelativePath;
#[cfg(feature = "alloc")]
use crate::RelativePathBuf;

/// [`Encode`] implementation for [`RelativePath`], encoding it as a string.
///
/// ```
/// use musli::Encode;
/// use relative_path::RelativePath;
///
/// #[derive(Encode)]
/// struct Document<'a> {
///     path: &'a RelativePath,
/// }
/// ```
#[cfg_attr(relative_path_docsrs, doc(cfg(feature = "musli02")))]
impl<M> Encode<M> for RelativePath {
    type Encode = Self;

    #[inline]
    fn encode<E>(&self, encoder: E) -> Result<(), E::Error>
    where
        E: Encoder<Mode = M>,
    {
        encoder.encode_string(self.as_str())
    }

    #[inline]
    fn as_encode(&self) -> &Self::Encode {
        self
    }
}

/// [`Decode`] implementation for a [`RelativePath`] reference borrowed from
/// the decoded input.
///
/// Decoding fails if the format cannot borrow the string from its input. Use
/// [`RelativePathBuf`] or [`Box<RelativePath>`] when that is not possible.
///
/// ```
/// use musli::Decode;
/// use relative_path::RelativePath;
///
/// #[derive(Decode)]
/// struct Document<'a> {
///     path: &'a RelativePath,
/// }
/// ```
#[cfg_attr(relative_path_docsrs, doc(cfg(feature = "musli02")))]
impl<'de, M, A> Decode<'de, M, A> for &'de RelativePath
where
    A: Allocator,
{
    #[inline]
    fn decode<D>(decoder: D) -> Result<Self, D::Error>
    where
        D: Decoder<'de, Mode = M, Allocator = A>,
    {
        Ok(RelativePath::new(decoder.decode::<&'de str>()?))
    }
}

/// [`DecodeUnsized`] implementation for [`RelativePath`], which visits the
/// decoded path by reference without requiring it to be borrowed from the
/// input or allocated.
///
/// ```
/// use musli::{Decode, Decoder};
/// use musli::mode::Binary;
/// use relative_path::RelativePath;
///
/// struct Depth(usize);
///
/// impl<'de, A> Decode<'de, Binary, A> for Depth
/// where
///     A: musli::Allocator,
/// {
///     fn decode<D>(decoder: D) -> Result<Self, D::Error>
///     where
///         D: Decoder<'de, Mode = Binary, Allocator = A>,
///     {
///         decoder.decode_unsized(|path: &RelativePath| Ok(Depth(path.components().count())))
///     }
/// }
/// ```
#[cfg_attr(relative_path_docsrs, doc(cfg(feature = "musli02")))]
impl<'de, M> DecodeUnsized<'de, M> for RelativePath {
    #[inline]
    fn decode_unsized<D, F, O>(decoder: D, f: F) -> Result<O, D::Error>
    where
        D: Decoder<'de, Mode = M>,
        F: FnOnce(&Self) -> Result<O, D::Error>,
    {
        decoder.decode_unsized(|string: &str| f(RelativePath::new(string)))
    }
}

/// [`Encode`] implementation for [`RelativePathBuf`], encoding it as a string.
///
/// ```
/// use musli::Encode;
/// use relative_path::RelativePathBuf;
///
/// #[derive(Encode)]
/// struct Document {
///     path: RelativePathBuf,
/// }
/// ```
#[cfg(feature = "alloc")]
#[cfg_attr(
    relative_path_docsrs,
    doc(cfg(all(feature = "alloc", feature = "musli02")))
)]
impl<M> Encode<M> for RelativePathBuf {
    type Encode = RelativePath;

    #[inline]
    fn encode<E>(&self, encoder: E) -> Result<(), E::Error>
    where
        E: Encoder<Mode = M>,
    {
        encoder.encode_string(self.as_str())
    }

    #[inline]
    fn as_encode(&self) -> &Self::Encode {
        self
    }
}

/// [`Decode`] implementation for [`RelativePathBuf`].
///
/// ```
/// use musli::Decode;
/// use relative_path::RelativePathBuf;
///
/// #[derive(Decode)]
/// struct Document {
///     path: RelativePathBuf,
/// }
/// ```
#[cfg(feature = "alloc")]
#[cfg_attr(
    relative_path_docsrs,
    doc(cfg(all(feature = "alloc", feature = "musli02")))
)]
impl<'de, M, A> Decode<'de, M, A> for RelativePathBuf
where
    A: Allocator,
{
    #[inline]
    fn decode<D>(decoder: D) -> Result<Self, D::Error>
    where
        D: Decoder<'de, Mode = M, Allocator = A>,
    {
        decoder.decode_unsized(|path: &RelativePath| Ok(path.to_relative_path_buf()))
    }
}

/// [`Decode`] implementation for [`Box<RelativePath>`].
///
/// Encoding uses musli's implementation for [`Box`], which requires musli's
/// `alloc` feature.
///
/// ```
/// use musli::{Decode, Encode};
/// use relative_path::RelativePath;
///
/// #[derive(Encode, Decode)]
/// struct Document {
///     path: Box<RelativePath>,
/// }
/// ```
#[cfg(feature = "alloc")]
#[cfg_attr(
    relative_path_docsrs,
    doc(cfg(all(feature = "alloc", feature = "musli02")))
)]
impl<'de, M, A> Decode<'de, M, A> for Box<RelativePath>
where
    A: Allocator,
{
    #[inline]
    fn decode<D>(decoder: D) -> Result<Self, D::Error>
    where
        D: Decoder<'de, Mode = M, Allocator = A>,
    {
        decoder.decode_unsized(|path: &RelativePath| Ok(Box::<RelativePath>::from(path)))
    }
}

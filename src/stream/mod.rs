//! Traits and implementations of arbitrary data streams.
//!
//! Streams are similar to the `Iterator` trait in that they represent some sequential set of items
//! which can be retrieved one by one. Where `Stream`s differ is that they are allowed to return
//! errors instead of just `None` and if they implement the `RangeStreamOnce` trait they are also
//! capable of returning multiple items at the same time, usually in the form of a slice.
//!
//! In addition to he functionality above, a proper `Stream` usable by a `Parser` must also have a
//! position (marked by the `Positioned` trait) and must also be resetable (marked by the
//! `Resetable` trait). The former is used to ensure that errors at different points in the stream
//! aren't combined and the latter is used in parsers such as `or` to try multiple alternative
//! parses.

use lib::fmt;

#[cfg(feature = "std")]
use std::io::{Bytes, Read};

#[cfg(feature = "std")]
use stream::easy::Errors;

use Parser;

use error::FastResult::*;
use error::{
    ConsumedResult, FastResult, ParseError, StreamError, StringStreamError, Tracked,
    UnexpectedParse,
};

#[doc(hidden)]
#[macro_export]
macro_rules! clone_resetable {
    (( $($params: tt)* ) $ty: ty) => {
        impl<$($params)*> Resetable for $ty
        {
            type Checkpoint = Self;

            fn checkpoint(&self) -> Self {
                self.clone()
            }
            fn reset(&mut self, checkpoint: Self) {
                *self = checkpoint;
            }
        }
    }
}

#[cfg(feature = "std")]
pub mod buffered;
#[cfg(feature = "std")]
pub mod easy;
/// Stateful stream wrappers.
pub mod state;

/// A type which has a position.
pub trait Positioned: StreamOnce {
    /// Returns the current position of the stream.
    fn position(&self) -> Self::Position;
}

/// Convenience alias over the `StreamError` for the input stream `I`
///
/// ```
/// #[macro_use]
/// extern crate combine;
/// use combine::{easy, Parser, Stream, many1};
/// use combine::parser::char::letter;
/// use combine::stream::StreamErrorFor;
/// use combine::error::{ParseError, StreamError};
///
/// parser!{
///    fn parser[I]()(I) -> String
///     where [ I: Stream<Item = char>, ]
///     {
///         many1(letter()).and_then(|word: String| {
///             if word == "combine" {
///                 Ok(word)
///             } else {
///                 // The alias makes it easy to refer to the `StreamError` type of `I`
///                 Err(StreamErrorFor::<I>::expected_static_message("combine"))
///             }
///         })
///     }
/// }
///
/// fn main() {
/// }
/// ```
pub type StreamErrorFor<I> = <<I as StreamOnce>::Error as ParseError<
    <I as StreamOnce>::Item,
    <I as StreamOnce>::Range,
    <I as StreamOnce>::Position,
>>::StreamError;

/// `StreamOnce` represents a sequence of items that can be extracted one by one.
pub trait StreamOnce {
    /// The type of items which is yielded from this stream.
    type Item: Clone + PartialEq;

    /// The type of a range of items yielded from this stream.
    /// Types which do not a have a way of yielding ranges of items should just use the
    /// `Self::Item` for this type.
    type Range: Clone + PartialEq;

    /// Type which represents the position in a stream.
    /// `Ord` is required to allow parsers to determine which of two positions are further ahead.
    type Position: Clone + Ord;

    type Error: ParseError<Self::Item, Self::Range, Self::Position>;
    /// Takes a stream and removes its first item, yielding the item and the rest of the elements.
    /// Returns `Err` if no element could be retrieved.
    fn uncons(&mut self) -> Result<Self::Item, StreamErrorFor<Self>>;

    /// Returns `true` if this stream only contains partial input.
    ///
    /// See `PartialStream`.
    fn is_partial(&self) -> bool {
        false
    }
}

pub trait Resetable {
    type Checkpoint: Clone;

    fn checkpoint(&self) -> Self::Checkpoint;
    fn reset(&mut self, checkpoint: Self::Checkpoint);
}

clone_resetable!{('a) &'a str}
clone_resetable!{('a, T) &'a [T]}
clone_resetable!{('a, T) SliceStream<'a, T> }
clone_resetable!{(T: Clone) IteratorStream<T>}

/// A stream of tokens which can be duplicated
pub trait Stream: StreamOnce + Resetable + Positioned {}

impl<I> Stream for I
where
    I: StreamOnce + Positioned + Resetable,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
}

#[inline]
pub fn uncons<I>(input: &mut I) -> ConsumedResult<I::Item, I>
where
    I: ?Sized + Stream,
{
    match input.uncons() {
        Ok(x) => ConsumedOk(x),
        Err(err) => wrap_stream_error(input, err),
    }
}

/// A `RangeStream` is an extension of `StreamOnce` which allows for zero copy parsing.
pub trait RangeStreamOnce: StreamOnce + Resetable {
    /// Takes `size` elements from the stream.
    /// Fails if the length of the stream is less than `size`.
    fn uncons_range(&mut self, size: usize) -> Result<Self::Range, StreamErrorFor<Self>>;

    /// Takes items from stream, testing each one with `predicate`.
    /// returns the range of items which passed `predicate`.
    fn uncons_while<F>(&mut self, f: F) -> Result<Self::Range, StreamErrorFor<Self>>
    where
        F: FnMut(Self::Item) -> bool;

    #[inline]
    fn uncons_while1<F>(&mut self, mut f: F) -> FastResult<Self::Range, StreamErrorFor<Self>>
    where
        F: FnMut(Self::Item) -> bool,
    {
        let mut consumed = false;
        let result = self.uncons_while(|c| {
            let ok = f(c);
            consumed |= ok;
            ok
        });
        if consumed {
            match result {
                Ok(x) => ConsumedOk(x),
                Err(x) => ConsumedErr(x),
            }
        } else {
            EmptyErr(Tracked::from(
                StreamErrorFor::<Self>::unexpected_static_message(""),
            ))
        }
    }

    /// Returns the distance between `self` and `end`. The returned `usize` must be so that
    ///
    /// ```ignore
    /// let start = stream.checkpoint();
    /// stream.uncons_range(distance);
    /// stream.distance(&start) == distance
    /// ```
    fn distance(&self, end: &Self::Checkpoint) -> usize;
}

/// A `RangeStream` is an extension of `Stream` which allows for zero copy parsing.
pub trait RangeStream: Stream + RangeStreamOnce {}

impl<I> RangeStream for I
where
    I: RangeStreamOnce + Stream,
{
}

/// A `RangeStream` which is capable of providing it's entire range.
pub trait FullRangeStream: RangeStream {
    /// Returns the entire range of `self`
    fn range(&self) -> Self::Range;
}

#[doc(hidden)]
#[inline]
pub fn wrap_stream_error<T, I>(
    input: &I,
    err: <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError,
) -> ConsumedResult<T, I>
where
    I: ?Sized + StreamOnce + Positioned,
{
    let err = I::Error::from_error(input.position(), err);
    if input.is_partial() {
        ConsumedErr(err)
    } else {
        EmptyErr(err.into())
    }
}

#[inline]
pub fn uncons_range<I>(input: &mut I, size: usize) -> ConsumedResult<I::Range, I>
where
    I: ?Sized + RangeStream,
{
    match input.uncons_range(size) {
        Err(err) => wrap_stream_error(input, err),
        Ok(x) => if size == 0 {
            EmptyOk(x)
        } else {
            ConsumedOk(x)
        },
    }
}

fn input_at_eof<I>(input: &mut I) -> bool
where
    I: ?Sized + Stream,
{
    let before = input.checkpoint();
    let x = input.uncons() == Err(StreamError::end_of_input());
    input.reset(before);
    x
}

/// Removes items from the input while `predicate` returns `true`.
#[inline]
pub fn uncons_while<I, F>(input: &mut I, predicate: F) -> ConsumedResult<I::Range, I>
where
    F: FnMut(I::Item) -> bool,
    I: ?Sized + RangeStream,
    I::Range: Range,
{
    match input.uncons_while(predicate) {
        Err(err) => wrap_stream_error(input, err),
        Ok(x) => {
            if input.is_partial() && input_at_eof(input) {
                // Partial inputs which encounter end of file must fail to let more input be
                // retrieved
                ConsumedErr(I::Error::from_error(
                    input.position(),
                    StreamError::end_of_input(),
                ))
            } else {
                if x.len() == 0 {
                    EmptyOk(x)
                } else {
                    ConsumedOk(x)
                }
            }
        }
    }
}

#[inline]
pub fn uncons_while1<I, F>(input: &mut I, predicate: F) -> ConsumedResult<I::Range, I>
where
    F: FnMut(I::Item) -> bool,
    I: ?Sized + RangeStream,
{
    match input.uncons_while1(predicate) {
        ConsumedOk(x) => {
            if input.is_partial() && input_at_eof(input) {
                // Partial inputs which encounter end of file must fail to let more input be
                // retrieved
                ConsumedErr(I::Error::from_error(
                    input.position(),
                    StreamError::end_of_input(),
                ))
            } else {
                ConsumedOk(x)
            }
        }
        EmptyErr(_) => {
            if input.is_partial() && input_at_eof(input) {
                // Partial inputs which encounter end of file must fail to let more input be
                // retrieved
                ConsumedErr(I::Error::from_error(
                    input.position(),
                    StreamError::end_of_input(),
                ))
            } else {
                EmptyErr(I::Error::empty(input.position()).into())
            }
        }
        ConsumedErr(err) => {
            if input.is_partial() && input_at_eof(input) {
                // Partial inputs which encounter end of file must fail to let more input be
                // retrieved
                ConsumedErr(I::Error::from_error(
                    input.position(),
                    StreamError::end_of_input(),
                ))
            } else {
                wrap_stream_error(input, err)
            }
        }
        EmptyOk(_) => unreachable!(),
    }
}

pub trait Range {
    /// Returns the remaining length of `self`.
    /// The returned length need not be the same as the number of items left in the stream.
    fn len(&self) -> usize;

    /// Returns `true` if the range does not contain any elements (`Range::len() == 0`)
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<'a> RangeStreamOnce for &'a str {
    fn uncons_while<F>(&mut self, mut f: F) -> Result<&'a str, StreamErrorFor<Self>>
    where
        F: FnMut(Self::Item) -> bool,
    {
        let mut chars = self.chars();

        macro_rules! test_next {
            () => {

                match chars.next() {
                    Some(c) => {
                        if !f(c) {
                            let len = self.len() - chars.as_str().len() - c.len_utf8();
                            let (result, rest) = self.split_at(len);
                            *self = rest;
                            return Ok(result);
                        }
                    }
                    None => break,
                }
            };
        }
        loop {
            test_next!();
            test_next!();
            test_next!();
            test_next!();
            test_next!();
            test_next!();
            test_next!();
            test_next!();
        }
        let result = *self;
        *self = &self[self.len()..];
        Ok(result)
    }

    #[inline]
    fn uncons_range(&mut self, size: usize) -> Result<&'a str, StreamErrorFor<Self>> {
        fn is_char_boundary(s: &str, index: usize) -> bool {
            if index == s.len() {
                return true;
            }
            match s.as_bytes().get(index) {
                None => false,
                Some(&b) => b < 128 || b >= 192,
            }
        }
        if size <= self.len() {
            if is_char_boundary(self, size) {
                let (result, remaining) = self.split_at(size);
                *self = remaining;
                Ok(result)
            } else {
                Err(StringStreamError::CharacterBoundary)
            }
        } else {
            Err(StringStreamError::Eoi)
        }
    }

    #[inline]
    fn distance(&self, end: &Self) -> usize {
        self.position().0 - end.position().0
    }
}

impl<'a> FullRangeStream for &'a str {
    fn range(&self) -> Self::Range {
        self
    }
}

impl<'a> Range for &'a str {
    #[inline]
    fn len(&self) -> usize {
        str::len(self)
    }
}

impl<'a, T> Range for &'a [T] {
    #[inline]
    fn len(&self) -> usize {
        <[T]>::len(self)
    }
}

fn slice_take_while<'a, T, F>(slice: &mut &'a [T], mut i: usize, mut f: F) -> &'a [T]
where
    F: FnMut(T) -> bool,
    T: Clone + PartialEq,
{
    let len = slice.len();
    let mut found = false;

    macro_rules! check {
        () => {
            if !f(unsafe { (*slice.get_unchecked(i)).clone() }) {
                found = true;
                break;
            }
            i += 1;
        };
    }

    while len - i >= 8 {
        check!();
        check!();
        check!();
        check!();
        check!();
        check!();
        check!();
        check!();
    }

    if !found {
        while i < len {
            if !f(unsafe { (*slice.get_unchecked(i)).clone() }) {
                break;
            }
            i += 1;
        }
    }

    let (result, remaining) = slice.split_at(i);
    *slice = remaining;
    result
}

impl<'a, T> RangeStreamOnce for &'a [T]
where
    T: Clone + PartialEq,
{
    #[inline]
    fn uncons_range(&mut self, size: usize) -> Result<&'a [T], StreamErrorFor<Self>> {
        if size <= self.len() {
            let (result, remaining) = self.split_at(size);
            *self = remaining;
            Ok(result)
        } else {
            Err(UnexpectedParse::Eoi)
        }
    }

    #[inline]
    fn uncons_while<F>(&mut self, f: F) -> Result<&'a [T], StreamErrorFor<Self>>
    where
        F: FnMut(Self::Item) -> bool,
    {
        Ok(slice_take_while(self, 0, f))
    }

    #[inline]
    fn uncons_while1<F>(&mut self, mut f: F) -> FastResult<Self::Range, StreamErrorFor<Self>>
    where
        F: FnMut(Self::Item) -> bool,
    {
        if self.is_empty() || !f(unsafe { (*self.get_unchecked(0)).clone() }) {
            return EmptyErr(Tracked::from(UnexpectedParse::Unexpected));
        }

        ConsumedOk(slice_take_while(self, 1, f))
    }

    #[inline]
    fn distance(&self, end: &Self) -> usize {
        end.len() - self.len()
    }
}

impl<'a, T> FullRangeStream for &'a [T]
where
    T: Clone + PartialEq,
{
    fn range(&self) -> Self::Range {
        self
    }
}

impl<'a> Positioned for &'a str {
    #[inline(always)]
    fn position(&self) -> Self::Position {
        self.as_bytes().position()
    }
}

impl<'a> StreamOnce for &'a str {
    type Item = char;
    type Range = &'a str;
    type Position = PointerOffset;
    type Error = StringStreamError;

    #[inline]
    fn uncons(&mut self) -> Result<char, StreamErrorFor<Self>> {
        let mut chars = self.chars();
        match chars.next() {
            Some(c) => {
                *self = chars.as_str();
                Ok(c)
            }
            None => Err(StringStreamError::Eoi),
        }
    }
}

impl<'a, T> Positioned for &'a [T]
where
    T: Clone + PartialEq,
{
    #[inline(always)]
    fn position(&self) -> Self::Position {
        PointerOffset(self.as_ptr() as usize)
    }
}

impl<'a, T> StreamOnce for &'a [T]
where
    T: Clone + PartialEq,
{
    type Item = T;
    type Range = &'a [T];
    type Position = PointerOffset;
    type Error = UnexpectedParse;

    #[inline]
    fn uncons(&mut self) -> Result<T, StreamErrorFor<Self>> {
        match self.split_first() {
            Some((first, rest)) => {
                *self = rest;
                Ok(first.clone())
            }
            None => Err(UnexpectedParse::Eoi),
        }
    }
}

/// Stream type which indicates that the stream is partial if end of input is reached
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub struct PartialStream<S>(pub S);

impl<S> Positioned for PartialStream<S>
where
    S: Positioned,
{
    #[inline(always)]
    fn position(&self) -> Self::Position {
        self.0.position()
    }
}

impl<S> Resetable for PartialStream<S>
where
    S: Resetable,
{
    type Checkpoint = S::Checkpoint;

    #[inline(always)]
    fn checkpoint(&self) -> Self::Checkpoint {
        self.0.checkpoint()
    }

    #[inline(always)]
    fn reset(&mut self, checkpoint: Self::Checkpoint) {
        self.0.reset(checkpoint);
    }
}

impl<S> StreamOnce for PartialStream<S>
where
    S: StreamOnce,
{
    type Item = S::Item;
    type Range = S::Range;
    type Position = S::Position;
    type Error = S::Error;

    #[inline(always)]
    fn uncons(&mut self) -> Result<S::Item, StreamErrorFor<Self>> {
        self.0.uncons()
    }

    fn is_partial(&self) -> bool {
        true
    }
}

impl<S> RangeStreamOnce for PartialStream<S>
where
    S: RangeStreamOnce,
{
    #[inline(always)]
    fn uncons_range(&mut self, size: usize) -> Result<Self::Range, StreamErrorFor<Self>> {
        self.0.uncons_range(size)
    }

    #[inline(always)]
    fn uncons_while<F>(&mut self, f: F) -> Result<Self::Range, StreamErrorFor<Self>>
    where
        F: FnMut(Self::Item) -> bool,
    {
        self.0.uncons_while(f)
    }

    #[inline(always)]
    fn distance(&self, end: &Self::Checkpoint) -> usize {
        self.0.distance(end)
    }
}

impl<S> FullRangeStream for PartialStream<S>
where
    S: FullRangeStream,
{
    #[inline(always)]
    fn range(&self) -> Self::Range {
        self.0.range()
    }
}

/// Newtype for constructing a stream from a slice where the items in the slice are not copyable.
#[derive(Copy, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub struct SliceStream<'a, T: 'a>(pub &'a [T]);

impl<'a, T> Clone for SliceStream<'a, T> {
    fn clone(&self) -> SliceStream<'a, T> {
        SliceStream(self.0)
    }
}

impl<'a, T> Positioned for SliceStream<'a, T>
where
    T: PartialEq + 'a,
{
    #[inline(always)]
    fn position(&self) -> Self::Position {
        PointerOffset(self.0.as_ptr() as usize)
    }
}

impl<'a, T> StreamOnce for SliceStream<'a, T>
where
    T: PartialEq + 'a,
{
    type Item = &'a T;
    type Range = &'a [T];
    type Position = PointerOffset;
    type Error = UnexpectedParse;

    #[inline]
    fn uncons(&mut self) -> Result<&'a T, StreamErrorFor<Self>> {
        match self.0.split_first() {
            Some((first, rest)) => {
                self.0 = rest;
                Ok(first)
            }
            None => Err(UnexpectedParse::Eoi),
        }
    }
}

impl<'a, T> RangeStreamOnce for SliceStream<'a, T>
where
    T: PartialEq + 'a,
{
    #[inline]
    fn uncons_range(&mut self, size: usize) -> Result<&'a [T], StreamErrorFor<Self>> {
        if size <= self.0.len() {
            let (range, rest) = self.0.split_at(size);
            self.0 = rest;
            Ok(range)
        } else {
            Err(UnexpectedParse::Eoi)
        }
    }

    #[inline]
    fn uncons_while<F>(&mut self, mut f: F) -> Result<&'a [T], StreamErrorFor<Self>>
    where
        F: FnMut(Self::Item) -> bool,
    {
        let len = self.0.iter().take_while(|c| f(*c)).count();
        let (range, rest) = self.0.split_at(len);
        self.0 = rest;
        Ok(range)
    }

    #[inline]
    fn distance(&self, end: &Self) -> usize {
        end.0.len() - self.0.len()
    }
}

impl<'a, T> FullRangeStream for SliceStream<'a, T>
where
    T: PartialEq + 'a,
{
    fn range(&self) -> Self::Range {
        self.0
    }
}

/// Wrapper around iterators which allows them to be treated as a stream.
/// Returned by [`from_iter`].
///
/// [`from_iter`]: fn.from_iter.html
#[derive(Copy, Clone, Debug)]
pub struct IteratorStream<I>(I);

impl<I> IteratorStream<I>
where
    I: Iterator,
{
    /// Converts an `Iterator` into a stream.
    ///
    /// NOTE: This type do not implement `Positioned` and `Clone` and must be wrapped with types
    ///     such as `BufferedStreamRef` and `State` to become a `Stream` which can be parsed
    pub fn new<T>(iter: T) -> IteratorStream<I>
    where
        T: IntoIterator<IntoIter = I, Item = I::Item>,
    {
        IteratorStream(iter.into_iter())
    }
}

impl<I> Iterator for IteratorStream<I>
where
    I: Iterator,
{
    type Item = I::Item;
    fn next(&mut self) -> Option<I::Item> {
        self.0.next()
    }
}

impl<I: Iterator> StreamOnce for IteratorStream<I>
where
    I::Item: Clone + PartialEq,
{
    type Item = I::Item;
    type Range = I::Item;
    type Position = ();
    type Error = UnexpectedParse;

    #[inline]
    fn uncons(&mut self) -> Result<I::Item, StreamErrorFor<Self>> {
        match self.next() {
            Some(x) => Ok(x),
            None => Err(UnexpectedParse::Eoi),
        }
    }
}

#[cfg(feature = "std")]
pub struct ReadStream<R> {
    bytes: Bytes<R>,
}

#[cfg(feature = "std")]
impl<R: Read> StreamOnce for ReadStream<R> {
    type Item = u8;
    type Range = u8;
    type Position = usize;
    type Error = Errors<u8, u8, usize>;

    #[inline]
    fn uncons(&mut self) -> Result<u8, StreamErrorFor<Self>> {
        match self.bytes.next() {
            Some(Ok(b)) => Ok(b),
            Some(Err(err)) => Err(StreamErrorFor::<Self>::other(err)),
            None => Err(StreamErrorFor::<Self>::end_of_input()),
        }
    }
}

#[cfg(feature = "std")]
impl<R> ReadStream<R>
where
    R: Read,
{
    /// Creates a `StreamOnce` instance from a value implementing `std::io::Read`.
    ///
    /// NOTE: This type do not implement `Positioned` and `Clone` and must be wrapped with types
    ///     such as `BufferedStreamRef` and `State` to become a `Stream` which can be parsed
    ///
    /// ```rust
    /// # #![cfg(feature = "std")]
    /// # extern crate combine;
    /// use combine::*;
    /// use combine::parser::byte::*;
    /// use combine::stream::ReadStream;
    /// use combine::stream::buffered::BufferedStream;
    /// use combine::stream::state::State;
    /// use std::io::Read;
    ///
    /// # fn main() {
    /// let input: &[u8] = b"123,";
    /// let stream = BufferedStream::new(State::new(ReadStream::new(input)), 1);
    /// let result = (many(digit()), byte(b','))
    ///     .parse(stream)
    ///     .map(|t| t.0);
    /// assert_eq!(result, Ok((vec![b'1', b'2', b'3'], b',')));
    /// # }
    /// ```
    pub fn new(read: R) -> ReadStream<R> {
        ReadStream {
            bytes: read.bytes(),
        }
    }
}

/// Newtype around a pointer offset into a slice stream (`&[T]`/`&str`).
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Ord, PartialOrd)]
pub struct PointerOffset(pub usize);

impl fmt::Display for PointerOffset {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.0 as *const ())
    }
}

impl PointerOffset {
    /// Converts the pointer-based position into an indexed position.
    ///
    /// ```rust
    /// # extern crate combine;
    /// # use combine::*;
    /// # fn main() {
    /// let text = "b";
    /// let err = token('a').easy_parse(text).unwrap_err();
    /// assert_eq!(err.position.0, text.as_ptr() as usize);
    /// assert_eq!(err.map_position(|p| p.translate_position(text)).position, 0);
    /// # }
    /// ```
    pub fn translate_position<T>(mut self, initial_string: &T) -> usize
    where
        T: ?Sized,
    {
        self.0 -= initial_string as *const T as *const () as usize;
        self.0
    }
}

/// Decodes `input` using `parser`.
///
/// Return `Ok(Some(item), consumed_data)` if there was enough data to finish parsing using
/// `parser`.
/// Returns `Ok(None, consumed_data)` if `input` did not contain enough data to finish parsing
/// using `parser`.
///
/// See `examples/async.rs` for example usage in a `tokio_io::codec::Decoder`
pub fn decode<P>(
    mut parser: P,
    mut input: P::Input,
    partial_state: &mut P::PartialState,
) -> Result<(Option<P::Output>, usize), <P::Input as StreamOnce>::Error>
where
    P: Parser,
    P::Input: RangeStream,
{
    let start = input.checkpoint();
    match parser.parse_with_state(&mut input, partial_state) {
        Ok(message) => Ok((Some(message), input.distance(&start))),
        Err(err) => {
            return if input.is_partial() && err.is_unexpected_end_of_input() {
                Ok((None, input.distance(&start)))
            } else {
                Err(err)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    #[inline]
    fn uncons_range_at_end() {
        assert_eq!("".uncons_range(0), Ok(""));
        assert_eq!("123".uncons_range(3), Ok("123"));
        assert_eq!((&[1][..]).uncons_range(1), Ok(&[1][..]));
        let s: &[u8] = &[];
        assert_eq!(SliceStream(s).uncons_range(0), Ok(&[][..]));
    }

    #[test]
    fn larger_than_1_byte_items_return_correct_distance() {
        let mut input = &[123i32, 0i32][..];

        let before = input.checkpoint();
        assert_eq!(input.distance(&before), 0);

        input.uncons().unwrap();
        assert_eq!(input.distance(&before), 1);

        input.uncons().unwrap();
        assert_eq!(input.distance(&before), 2);

        input.reset(before.clone());
        assert_eq!(input.distance(&before), 0);
    }
}

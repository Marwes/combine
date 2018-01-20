use lib::fmt;

#[cfg(feature = "std")]
use std::io::{Bytes, Read};
#[cfg(feature = "std")]
use std::error::Error as StdError;

use either::Either;

use self::FastResult::*;

use ErrorOffset;
use combinator::{and_then, expected, flat_map, map, message, or, skip, then, with, AndThen,
                 Expected, FlatMap, Iter, Map, Message, Or, Skip, Then, With};

#[cfg(feature = "std")]
use easy::Error;

#[macro_export]
macro_rules! ctry {
    ($result: expr) => {
        match $result {
            $crate::primitives::FastResult::ConsumedOk(x) =>
                (x, $crate::primitives::Consumed::Consumed(())),
            $crate::primitives::FastResult::EmptyOk(x) =>
                (x, $crate::primitives::Consumed::Empty(())),
            $crate::primitives::FastResult::ConsumedErr(err) =>
                return $crate::primitives::FastResult::ConsumedErr(err.into()),
            $crate::primitives::FastResult::EmptyErr(err) =>
                return $crate::primitives::FastResult::EmptyErr(err.into()),
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

impl<R> From<char> for Info<char, R> {
    fn from(s: char) -> Info<char, R> {
        Info::Token(s)
    }
}

impl<T, R> From<&'static str> for Info<T, R> {
    fn from(s: &'static str) -> Info<T, R> {
        Info::Borrowed(s)
    }
}

impl<R> From<u8> for Info<u8, R> {
    fn from(s: u8) -> Info<u8, R> {
        Info::Token(s)
    }
}

/// Enum used to indicate if a parser consumed any items of the stream it was given as an input.
///
/// This is used by parsers such as `or` and `choice` to determine if they should try to parse
/// with another parser as they will only be able to provide good error reporting if the preceding
/// parser did not consume any tokens.
#[derive(Clone, PartialEq, Debug, Copy)]
pub enum Consumed<T> {
    /// Constructor indicating that the parser has consumed elements
    Consumed(T),
    /// Constructor indicating that the parser did not consume any elements
    Empty(T),
}

impl<T> AsMut<T> for Consumed<T> {
    fn as_mut(&mut self) -> &mut T {
        match *self {
            Consumed::Empty(ref mut t) | Consumed::Consumed(ref mut t) => t,
        }
    }
}

impl<T> AsRef<T> for Consumed<T> {
    fn as_ref(&self) -> &T {
        match *self {
            Consumed::Empty(ref t) | Consumed::Consumed(ref t) => t,
        }
    }
}

impl<T> Consumed<T> {
    /// Returns true if `self` is empty.
    pub fn is_empty(&self) -> bool {
        match *self {
            Consumed::Empty(_) => true,
            Consumed::Consumed(_) => false,
        }
    }

    /// Extracts the contained value.
    pub fn into_inner(self) -> T {
        match self {
            Consumed::Empty(x) | Consumed::Consumed(x) => x,
        }
    }

    /// Converts `self` into the `Consumed` state.
    pub fn into_consumed(self) -> Consumed<T> {
        Consumed::Consumed(self.into_inner())
    }

    /// Converts `self` into the `Empty` state.
    pub fn into_empty(self) -> Consumed<T> {
        Consumed::Empty(self.into_inner())
    }

    /// Maps over the contained value without changing the consumed state.
    pub fn map<F, U>(self, f: F) -> Consumed<U>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Consumed::Empty(x) => Consumed::Empty(f(x)),
            Consumed::Consumed(x) => Consumed::Consumed(f(x)),
        }
    }

    pub fn merge(&self, current: Consumed<T>) -> Consumed<T> {
        match *self {
            Consumed::Empty(_) => current,
            Consumed::Consumed(_) => current.into_consumed(),
        }
    }

    /// Combines the `Consumed` flags from `self` and the result of `f`.
    ///
    /// ```text
    /// Empty    <> Empty    -> Empty
    /// Consumed <> Empty    -> Consumed
    /// Empty    <> Consumed -> Consumed
    /// Consumed <> Consumed -> Consumed
    /// ```
    ///
    /// ```
    /// # extern crate combine as pc;
    /// # use pc::*;
    /// # fn main() {
    /// //Parses a character of string literal and handles the escaped characters \\ and \" as \
    /// //and " respectively
    /// fn char<I>(input: &mut I) -> ParseResult<char, I>
    ///     where I: Stream<Item = char>,
    ///           I::Error: ParseError<I::Item, I::Range, I::Position>,
    /// {
    ///     let (c, consumed) = try!(satisfy(|c| c != '"').parse_stream(input));
    ///     match c {
    ///         //Since the `char` parser has already consumed some of the input `combine` is used
    ///         //propagate the consumed state to the next part of the parser
    ///         '\\' => consumed.combine(|_| {
    ///             satisfy(|c| c == '"' || c == '\\')
    ///                 .map(|c| {
    ///                     match c {
    ///                         '"' => '"',
    ///                         '\\' => '\\',
    ///                         c => c
    ///                     }
    ///                 })
    ///                 .parse_stream(input)
    ///             }),
    ///         _ => Ok((c, consumed))
    ///     }
    /// }
    /// let result = many(parser(char))
    ///     .easy_parse(r#"abc\"\\"#);
    /// assert_eq!(result, Ok((r#"abc"\"#.to_string(), "")));
    /// }
    /// ```
    pub fn combine<F, U, E>(self, f: F) -> ParseResult2<U, E>
    where
        F: FnOnce(T) -> ParseResult2<U, E>,
    {
        match self {
            Consumed::Consumed(x) => match f(x) {
                Ok((v, Consumed::Empty(rest))) => Ok((v, Consumed::Consumed(rest))),
                Err(Consumed::Empty(err)) => Err(Consumed::Consumed(err)),
                y => y,
            },
            Consumed::Empty(x) => f(x),
        }
    }
    pub fn combine_consumed<F, U, E>(self, f: F) -> FastResult<U, E>
    where
        F: FnOnce(T) -> FastResult<U, E>,
    {
        use self::FastResult::*;
        match self {
            Consumed::Consumed(x) => match f(x) {
                EmptyOk(v) => ConsumedOk(v),
                EmptyErr(err) => ConsumedErr(err.error),
                y => y,
            },
            Consumed::Empty(x) => f(x),
        }
    }
}

/// A type alias over the specific `Result` type used by parsers to indicate wether they were
/// successful or not.
/// `O` is the type that is output on success.
/// `I` is the specific stream type used in the parser.
pub type ParseResult<O, I> = Result<(O, Consumed<()>), Consumed<Tracked<<I as StreamOnce>::Error>>>;
pub type ParseResult2<O, E> = Result<(O, Consumed<()>), Consumed<Tracked<E>>>;

#[derive(Clone, Debug)]
pub enum Info<T, R> {
    Token(T),
    Range(R),
    Borrowed(&'static str),
}

/// Enum used to store information about an error that has occurred during parsing.
#[derive(Debug)]
pub enum EasyError<T, R> {
    /// Error indicating an unexpected token has been encountered in the stream
    Unexpected(Info<T, R>),
    /// Error indicating that the parser expected something else
    Expected(Info<T, R>),
    /// Generic message
    Message(Info<T, R>),
}

/// `StreamError` represents a single error returned from a `Stream` or a `Parser`.
/// Usually this is composed into a `ParseError`
pub trait StreamError<Item, Range>: Sized + PartialEq {
    fn unexpected_token(token: Item) -> Self;
    fn unexpected_range(token: Range) -> Self;
    fn unexpected_message<T>(msg: T) -> Self
    where
        T: fmt::Display;
    fn unexpected(info: Info<Item, Range>) -> Self {
        match info {
            Info::Token(b) => Self::unexpected_token(b),
            Info::Range(b) => Self::unexpected_range(b),
            Info::Borrowed(b) => Self::unexpected_static_message(b),
        }
    }
    fn unexpected_static_message(msg: &'static str) -> Self {
        Self::unexpected_message(msg)
    }

    fn expected_token(token: Item) -> Self;
    fn expected_range(token: Range) -> Self;
    fn expected_message<T>(msg: T) -> Self
    where
        T: fmt::Display;
    fn expected(info: Info<Item, Range>) -> Self {
        match info {
            Info::Token(b) => Self::expected_token(b),
            Info::Range(b) => Self::expected_range(b),
            Info::Borrowed(b) => Self::expected_static_message(b),
        }
    }
    fn expected_static_message(msg: &'static str) -> Self {
        Self::expected_message(msg)
    }

    fn message_token(token: Item) -> Self;
    fn message_range(token: Range) -> Self;
    fn message_message<T>(msg: T) -> Self
    where
        T: fmt::Display;
    fn message_static_message(msg: &'static str) -> Self {
        Self::message_message(msg)
    }
    fn message(info: Info<Item, Range>) -> Self {
        match info {
            Info::Token(b) => Self::message_token(b),
            Info::Range(b) => Self::message_range(b),
            Info::Borrowed(b) => Self::message_static_message(b),
        }
    }

    #[cfg(feature = "std")]
    fn other<E>(err: E) -> Self
    where
        E: StdError + Send + Sync + 'static,
    {
        Self::message_message(err)
    }

    fn end_of_input() -> Self {
        Self::unexpected_static_message("end of input")
    }

    fn into_other<T>(self) -> T
    where
        T: StreamError<Item, Range>;
}

/// Trait which defines a gluon parse error.
///
/// A parse error is composed of one or more `StreamError`s
pub trait ParseError<Item, Range, Position>: Sized + PartialEq {
    type StreamError: StreamError<Item, Range>;

    /// Constructs an empty error.
    ///
    /// An empty error is expected to be cheap to create as it is frequently created and discarded.
    fn empty(position: Position) -> Self;

    /// Creates a `ParseError` from a single `Self::StreamError`
    fn from_error(position: Position, err: Self::StreamError) -> Self;

    /// Sets the position of this `ParseError`
    fn set_position(&mut self, position: Position);

    /// Merges two errors. If they exist at the same position the errors of `other` are
    /// added to `self` (using the semantics of `add`). If they are not at the same
    /// position the error furthest ahead are returned, ignoring the other `ParseError`.
    fn merge(self, other: Self) -> Self {
        other
    }

    /// Adds a `StreamError` to `self`.
    ///
    /// It is up to each individual error type to define what adding an error does, some may push
    /// it to a vector while others may only keep `self` or `err` to avoid allocation
    fn add(&mut self, err: Self::StreamError);

    fn add_expected(&mut self, info: Info<Item, Range>) {
        self.add(Self::StreamError::expected(info))
    }

    fn add_unexpected(&mut self, info: Info<Item, Range>) {
        self.add(Self::StreamError::unexpected(info))
    }

    fn add_message(&mut self, info: Info<Item, Range>) {
        self.add(Self::StreamError::message(info))
    }

    /// Sets `info` as the *only* `Expected` error of `self`
    fn set_expected<F>(self_: &mut Tracked<Self>, info: Self::StreamError, f: F)
    where
        F: FnOnce(&mut Tracked<Self>);

    fn is_unexpected_end_of_input(&self) -> bool;

    /// Does a best-effort conversion of `self` into another `ParseError`
    fn into_other<T>(self) -> T
    where
        T: ParseError<Item, Range, Position>;
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum UnexpectedParse {
    Eoi,
    Unexpected,
}

impl fmt::Display for UnexpectedParse {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::UnexpectedParse::*;
        write!(
            f,
            "{}",
            match *self {
                Unexpected => "unexpected parse",
                Eoi => "unexpected end of input",
            }
        )
    }
}

impl<Item, Range> StreamError<Item, Range> for UnexpectedParse {
    #[inline]
    fn unexpected_token(_: Item) -> Self {
        UnexpectedParse::Unexpected
    }
    #[inline]
    fn unexpected_range(_: Range) -> Self {
        UnexpectedParse::Unexpected
    }
    #[inline]
    fn unexpected_message<T>(_: T) -> Self
    where
        T: fmt::Display,
    {
        UnexpectedParse::Unexpected
    }

    #[inline]
    fn expected_token(_: Item) -> Self {
        UnexpectedParse::Unexpected
    }
    #[inline]
    fn expected_range(_: Range) -> Self {
        UnexpectedParse::Unexpected
    }
    #[inline]
    fn expected_message<T>(_: T) -> Self
    where
        T: fmt::Display,
    {
        UnexpectedParse::Unexpected
    }
    #[inline]
    fn message_message<T>(_: T) -> Self
    where
        T: fmt::Display,
    {
        UnexpectedParse::Unexpected
    }
    #[inline]
    fn message_token(_: Item) -> Self {
        UnexpectedParse::Unexpected
    }
    #[inline]
    fn message_range(_: Range) -> Self {
        UnexpectedParse::Unexpected
    }

    #[inline]
    fn end_of_input() -> Self {
        UnexpectedParse::Eoi
    }

    #[inline]
    fn into_other<T>(self) -> T
    where
        T: StreamError<Item, Range>,
    {
        let msg = match self {
            UnexpectedParse::Unexpected => "parse",
            UnexpectedParse::Eoi => "end of input",
        };
        T::unexpected_static_message(msg)
    }
}

impl<Item, Range, Position> ParseError<Item, Range, Position> for UnexpectedParse
where
    Position: Default,
{
    type StreamError = Self;
    #[inline]
    fn empty(_position: Position) -> Self {
        UnexpectedParse::Unexpected
    }

    #[inline]
    fn from_error(_: Position, err: Self::StreamError) -> Self {
        err
    }

    #[inline]
    fn set_position(&mut self, _position: Position) {}

    #[inline]
    fn add(&mut self, err: Self::StreamError) {
        *self = err;
    }

    #[inline]
    fn set_expected<F>(self_: &mut Tracked<Self>, info: Self::StreamError, f: F)
    where
        F: FnOnce(&mut Tracked<Self>),
    {
        f(self_);
        self_.error = info;
    }

    fn is_unexpected_end_of_input(&self) -> bool {
        *self == UnexpectedParse::Eoi
    }

    #[inline]
    fn into_other<T>(self) -> T
    where
        T: ParseError<Item, Range, Position>,
    {
        T::from_error(Position::default(), StreamError::into_other(self))
    }
}

pub trait Positioned: StreamOnce {
    /// Returns the current position of the stream.
    fn position(&self) -> Self::Position;
}

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

    fn uncons<E>(&mut self) -> Result<Self::Item, E>
    where
        E: StreamError<Self::Item, Self::Range>;
}

pub trait Resetable {
    type Checkpoint: Clone;

    fn checkpoint(&self) -> Self::Checkpoint;
    fn reset(&mut self, checkpoint: Self::Checkpoint);
}

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
pub fn uncons<I>(input: &mut I) -> ParseResult<I::Item, I>
where
    I: Stream,
{
    let position = input.position();
    let x = try!(
        input
            .uncons()
            .map_err(|err| Consumed::Empty(I::Error::from_error(position, err).into()))
    );
    Ok((x, Consumed::Consumed(())))
}

/// A `RangeStream` is an extension of `StreamOnce` which allows for zero copy parsing.
pub trait RangeStreamOnce: StreamOnce + Resetable {
    /// Takes `size` elements from the stream.
    /// Fails if the length of the stream is less than `size`.
    fn uncons_range<E>(&mut self, size: usize) -> Result<Self::Range, E>
    where
        E: StreamError<Self::Item, Self::Range>;

    /// Takes items from stream, testing each one with `predicate`.
    /// returns the range of items which passed `predicate`.
    fn uncons_while<E, F>(&mut self, f: F) -> Result<Self::Range, E>
    where
        F: FnMut(Self::Item) -> bool,
        E: StreamError<Self::Item, Self::Range>;

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

/// Removes items from the input while `predicate` returns `true`.
#[inline]
pub fn uncons_while<I, F>(input: &mut I, predicate: F) -> ConsumedResult<I::Range, I>
where
    F: FnMut(I::Item) -> bool,
    I: RangeStream,
    I::Range: Range,
{
    match input.uncons_while(predicate) {
        Err(err) => EmptyErr(I::Error::from_error(input.position(), err).into()),
        Ok(x) => if x.len() == 0 {
            EmptyOk(x)
        } else {
            ConsumedOk(x)
        },
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
    #[inline]
    fn uncons_while<E, F>(&mut self, mut f: F) -> Result<&'a str, E>
    where
        F: FnMut(Self::Item) -> bool,
        E: StreamError<Self::Item, Self::Range>,
    {
        let mut chars = self.chars();
        while let Some(c) = chars.next() {
            if !f(c) {
                let len = self.len() - chars.as_str().len() - c.len_utf8();
                let (result, rest) = self.split_at(len);
                *self = rest;
                return Ok(result);
            }
        }
        let result = *self;
        *self = &self[self.len()..];
        Ok(result)
    }

    #[inline]
    fn uncons_range<E>(&mut self, size: usize) -> Result<&'a str, E>
    where
        E: StreamError<Self::Item, Self::Range>,
    {
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
                Err(E::message_static_message(CHAR_BOUNDARY_ERROR_MESSAGE))
            }
        } else {
            Err(E::end_of_input())
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

impl<'a, T> RangeStreamOnce for &'a [T]
where
    T: Clone + PartialEq,
{
    #[inline]
    fn uncons_range<E>(&mut self, size: usize) -> Result<&'a [T], E>
    where
        E: StreamError<Self::Item, Self::Range>,
    {
        if size <= self.len() {
            let (result, remaining) = self.split_at(size);
            *self = remaining;
            Ok(result)
        } else {
            Err(E::end_of_input())
        }
    }

    #[inline]
    fn uncons_while<E, F>(&mut self, mut f: F) -> Result<&'a [T], E>
    where
        F: FnMut(Self::Item) -> bool,
        E: StreamError<Self::Item, Self::Range>,
    {
        let len = self.iter().take_while(|c| f((**c).clone())).count();
        let (result, remaining) = self.split_at(len);
        *self = remaining;
        Ok(result)
    }

    #[inline]
    fn distance(&self, end: &Self) -> usize {
        self.position().0 - end.position().0
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

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum StringStreamError {
    UnexpectedParse,
    Eoi,
    CharacterBoundary,
}

const CHAR_BOUNDARY_ERROR_MESSAGE: &str = "unexpected slice on character boundary";

impl fmt::Display for StringStreamError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::StringStreamError::*;
        write!(
            f,
            "{}",
            match *self {
                UnexpectedParse => "unexpected parse",
                Eoi => "unexpected end of input",
                CharacterBoundary => CHAR_BOUNDARY_ERROR_MESSAGE,
            }
        )
    }
}

impl<Item, Range> StreamError<Item, Range> for StringStreamError {
    #[inline]
    fn unexpected_token(_: Item) -> Self {
        StringStreamError::UnexpectedParse
    }
    #[inline]
    fn unexpected_range(_: Range) -> Self {
        StringStreamError::UnexpectedParse
    }
    #[inline]
    fn unexpected_message<T>(_msg: T) -> Self
    where
        T: fmt::Display,
    {
        StringStreamError::UnexpectedParse
    }

    #[inline]
    fn expected_token(_: Item) -> Self {
        StringStreamError::UnexpectedParse
    }
    #[inline]
    fn expected_range(_: Range) -> Self {
        StringStreamError::UnexpectedParse
    }
    #[inline]
    fn expected_message<T>(_: T) -> Self
    where
        T: fmt::Display,
    {
        StringStreamError::UnexpectedParse
    }
    #[inline]
    fn message_message<T>(_: T) -> Self
    where
        T: fmt::Display,
    {
        StringStreamError::UnexpectedParse
    }
    #[inline]
    fn message_token(_: Item) -> Self {
        StringStreamError::UnexpectedParse
    }
    #[inline]
    fn message_range(_: Range) -> Self {
        StringStreamError::UnexpectedParse
    }
    fn message_static_message(msg: &'static str) -> Self {
        if msg == CHAR_BOUNDARY_ERROR_MESSAGE {
            StringStreamError::CharacterBoundary
        } else {
            StringStreamError::UnexpectedParse
        }
    }
    #[inline]
    fn end_of_input() -> Self {
        StringStreamError::Eoi
    }
    #[inline]
    fn into_other<T>(self) -> T
    where
        T: StreamError<Item, Range>,
    {
        let msg = match self {
            StringStreamError::CharacterBoundary => CHAR_BOUNDARY_ERROR_MESSAGE,
            StringStreamError::UnexpectedParse => "parse",
            StringStreamError::Eoi => return T::end_of_input(),
        };
        T::unexpected_static_message(msg)
    }
}
impl<Item, Range, Position> ParseError<Item, Range, Position> for StringStreamError
where
    Position: Default,
{
    type StreamError = Self;
    #[inline]
    fn empty(_position: Position) -> Self {
        StringStreamError::UnexpectedParse
    }
    #[inline]
    fn from_error(_: Position, err: Self::StreamError) -> Self {
        err
    }

    #[inline]
    fn set_position(&mut self, _position: Position) {}

    #[inline]
    fn add(&mut self, err: Self::StreamError) {
        *self = err;
    }

    #[inline]
    fn set_expected<F>(self_: &mut Tracked<Self>, info: Self::StreamError, f: F)
    where
        F: FnOnce(&mut Tracked<Self>),
    {
        f(self_);
        self_.error = info;
    }

    fn is_unexpected_end_of_input(&self) -> bool {
        *self == StringStreamError::Eoi
    }

    #[inline]
    fn into_other<T>(self) -> T
    where
        T: ParseError<Item, Range, Position>,
    {
        T::from_error(Position::default(), StreamError::into_other(self))
    }
}

impl<'a> StreamOnce for &'a str {
    type Item = char;
    type Range = &'a str;
    type Position = PointerOffset;
    type Error = StringStreamError;

    #[inline]
    fn uncons<E>(&mut self) -> Result<char, E>
    where
        E: StreamError<Self::Item, Self::Range>,
    {
        let mut chars = self.chars();
        match chars.next() {
            Some(c) => {
                *self = chars.as_str();
                Ok(c)
            }
            None => Err(E::end_of_input()),
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
    fn uncons<E>(&mut self) -> Result<T, E>
    where
        E: StreamError<Self::Item, Self::Range>,
    {
        match self.split_first() {
            Some((first, rest)) => {
                *self = rest;
                Ok(first.clone())
            }
            None => Err(E::end_of_input()),
        }
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
    fn uncons<E>(&mut self) -> Result<&'a T, E>
    where
        E: StreamError<Self::Item, Self::Range>,
    {
        match self.0.split_first() {
            Some((first, rest)) => {
                self.0 = rest;
                Ok(first)
            }
            None => Err(E::end_of_input()),
        }
    }
}

impl<'a, T> RangeStreamOnce for SliceStream<'a, T>
where
    T: PartialEq + 'a,
{
    #[inline]
    fn uncons_range<E>(&mut self, size: usize) -> Result<&'a [T], E>
    where
        E: StreamError<Self::Item, Self::Range>,
    {
        if size <= self.0.len() {
            let (range, rest) = self.0.split_at(size);
            self.0 = rest;
            Ok(range)
        } else {
            Err(E::end_of_input())
        }
    }

    #[inline]
    fn uncons_while<E, F>(&mut self, mut f: F) -> Result<&'a [T], E>
    where
        F: FnMut(Self::Item) -> bool,
        E: StreamError<Self::Item, Self::Range>,
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
    pub fn new(iter: I) -> IteratorStream<I> {
        IteratorStream(iter)
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
    fn uncons<E>(&mut self) -> Result<I::Item, E>
    where
        E: StreamError<Self::Item, Self::Range>,
    {
        match self.next() {
            Some(x) => Ok(x),
            None => Err(E::end_of_input()),
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
    type Position = ();
    type Error = Error<u8, u8>;

    #[inline]
    fn uncons<E>(&mut self) -> Result<u8, E>
    where
        E: StreamError<Self::Item, Self::Range>,
    {
        match self.bytes.next() {
            Some(Ok(b)) => Ok(b),
            Some(Err(err)) => Err(E::other(err)),
            None => Err(E::end_of_input()),
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
    /// use combine::byte::*;
    /// use combine::primitives::ReadStream;
    /// use combine::buffered_stream::BufferedStream;
    /// use combine::state::State;
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

/// Error wrapper which lets parsers track which parser in a sequence of sub-parsers has emitted
/// the error. `Tracked::from` can be used to construct this and it should otherwise be
/// ignored outside of combine.
#[derive(Clone, PartialEq, Debug, Copy)]
pub struct Tracked<E> {
    /// The error returned
    pub error: E,
    #[doc(hidden)]
    pub offset: ErrorOffset,
}

impl<E> From<E> for Tracked<E> {
    fn from(error: E) -> Self {
        Tracked {
            error: error,
            offset: ErrorOffset(1),
        }
    }
}

#[derive(Clone, PartialEq, Debug, Copy)]
pub enum FastResult<T, E> {
    ConsumedOk(T),
    EmptyOk(T),
    ConsumedErr(E),
    EmptyErr(Tracked<E>),
}

impl<T, E> FastResult<T, E> {
    pub fn as_ref(&self) -> FastResult<&T, &E> {
        match *self {
            ConsumedOk(ref t) => ConsumedOk(t),
            EmptyOk(ref t) => EmptyOk(t),
            ConsumedErr(ref e) => ConsumedErr(e),
            EmptyErr(ref e) => EmptyErr(Tracked {
                error: &e.error,
                offset: e.offset,
            }),
        }
    }

    pub fn and_then<F, T2>(self, f: F) -> F::Output
    where
        F: FnOnce(T) -> FastResult<T2, E>,
    {
        match self {
            ConsumedOk(t) => match f(t) {
                ConsumedOk(t2) | EmptyOk(t2) => ConsumedOk(t2),
                EmptyErr(e) => ConsumedErr(e.error),
                ConsumedErr(e) => ConsumedErr(e),
            },
            EmptyOk(t) => f(t),
            ConsumedErr(e) => ConsumedErr(e),
            EmptyErr(e) => EmptyErr(e),
        }
    }

    pub fn map_err<F, E2>(self, f: F) -> FastResult<T, F::Output>
    where
        F: FnOnce(E) -> E2,
    {
        match self {
            ConsumedOk(t) => ConsumedOk(t),
            EmptyOk(t) => EmptyOk(t),
            ConsumedErr(e) => ConsumedErr(f(e)),
            EmptyErr(e) => EmptyErr(Tracked {
                error: f(e.error),
                offset: e.offset,
            }),
        }
    }
}

impl<T, E> FastResult<T, E> {
    pub fn map<F, T2>(self, f: F) -> FastResult<F::Output, E>
    where
        F: FnOnce(T) -> T2,
    {
        match self {
            ConsumedOk(t) => ConsumedOk(f(t)),
            EmptyOk(t) => EmptyOk(f(t)),
            ConsumedErr(e) => ConsumedErr(e),
            EmptyErr(e) => EmptyErr(e),
        }
    }
}

/// A `Result` type which has the consumed status flattened into the result.
/// Conversions to and from `std::result::Result` can be done using `result.into()` or
/// `From::from(result)`
pub type ConsumedResult<O, I> = FastResult<O, <I as StreamOnce>::Error>;

impl<T, E> Into<Result<Consumed<T>, Consumed<Tracked<E>>>> for FastResult<T, E> {
    fn into(self) -> Result<Consumed<T>, Consumed<Tracked<E>>> {
        match self {
            ConsumedOk(t) => Ok(Consumed::Consumed(t)),
            EmptyOk(t) => Ok(Consumed::Empty(t)),
            ConsumedErr(e) => Err(Consumed::Consumed(e.into())),
            EmptyErr(e) => Err(Consumed::Empty(e)),
        }
    }
}

impl<O, E> Into<ParseResult2<O, E>> for FastResult<O, E> {
    fn into(self) -> ParseResult2<O, E> {
        use self::FastResult::*;
        match self {
            ConsumedOk(t) => Ok((t, Consumed::Consumed(()))),
            EmptyOk(t) => Ok((t, Consumed::Empty(()))),
            ConsumedErr(e) => Err(Consumed::Consumed(e.into())),
            EmptyErr(e) => Err(Consumed::Empty(e)),
        }
    }
}

impl<O, E> From<ParseResult2<O, E>> for FastResult<O, E> {
    fn from(result: ParseResult2<O, E>) -> FastResult<O, E> {
        use self::FastResult::*;
        match result {
            Ok((t, Consumed::Consumed(()))) => ConsumedOk(t),
            Ok((t, Consumed::Empty(()))) => EmptyOk(t),
            Err(Consumed::Consumed(e)) => ConsumedErr(e.error),
            Err(Consumed::Empty(e)) => EmptyErr(e),
        }
    }
}

/// By implementing the `Parser` trait a type says that it can be used to parse an input stream
/// into the type `Output`.
///
/// All methods have a default implementation but there needs to be at least an implementation of
/// [`parse_stream`], [`parse_stream_consumed`], or [`parse_lazy`]. If the last is implemented, an
/// implementation of [`add_error`] may also be required. See the documentation for
/// [`parse_lazy`] for details.
///
/// [`parse_stream`]: trait.Parser.html#method.parse_stream
/// [`parse_stream_consumed`]: trait.Parser.html#method.parse_stream_consumed
/// [`parse_lazy`]: trait.Parser.html#method.parse_lazy
/// [`add_error`]: trait.Parser.html#method.add_error
pub trait Parser {
    /// The type which is taken as input for the parser. The type must implement the `Stream` trait
    /// which allows the parser to read items from the type.
    type Input: Stream;
    /// The type which is returned if the parser is successful.
    type Output;
    type PartialState: Default;

    /// Entry point of the parser. Takes some input and tries to parse it.
    ///
    /// Returns the parsed result and the remaining input if the parser succeeds, or a
    /// This function wraps requires `Self::Input == easy::Stream<I>` which makes it return
    /// return `easy::Errors` if an error occurs.
    ///
    /// [`ParseError`] otherwise.
    ///
    /// [`ParseError`]: struct.ParseError.html
    #[cfg(feature = "std")]
    fn easy_parse<I>(&mut self, input: I) -> Result<(Self::Output, I), ::easy::StreamErrors<I>>
    where
        I: Stream,
        ::easy::Stream<I>: StreamOnce<
            Item = I::Item,
            Range = I::Range,
            Error = ::easy::StreamErrors<::easy::Stream<I>>,
            Position = I::Position,
        >,
        I::Position: Default,
        Self: Sized + Parser<Input = ::easy::Stream<I>>,
    {
        let mut input = ::easy::Stream(input);
        match self.parse_stream(&mut input) {
            Ok((v, _)) => Ok((v, input.0)),
            Err(error) => Err(error.into_inner().error),
        }
    }

    /// Entry point of the parser. Takes some input and tries to parse it.
    ///
    /// Returns the parsed result and the remaining input if the parser succeeds, or a
    /// [`ParseError`] otherwise.
    ///
    /// [`ParseError`]: primitives/struct.ParseError.html
    fn parse(
        &mut self,
        mut input: Self::Input,
    ) -> Result<(Self::Output, Self::Input), <Self::Input as StreamOnce>::Error> {
        match self.parse_stream(&mut input) {
            Ok((v, _)) => Ok((v, input)),
            Err(error) => Err(error.into_inner().error),
        }
    }

    fn parse_with_state(
        &mut self,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> Result<Self::Output, <Self::Input as StreamOnce>::Error> {
        match self.parse_stream_consumed_partial(input, state).into() {
            Ok((v, _)) => Ok(v),
            Err(error) => Err(error.into_inner().error),
        }
    }

    /// Parses using the stream `input` by calling [`Stream::uncons`] one or more times.
    ///
    /// On success returns `Ok((value, new_state))`, and on failure returns `Err(error)`.
    /// Furthermore `new_state` and `error` are wrapped in [`Consumed`], providing information on
    /// whether this parser consumed any input data or not.
    ///
    /// [`Stream::uncons`]: trait.StreamOnce.html#tymethod.uncons
    /// [`Consumed`]: enum.Consumed.html
    #[inline(always)]
    fn parse_stream(&mut self, input: &mut Self::Input) -> ParseResult<Self::Output, Self::Input> {
        self.parse_stream_consumed(input).into()
    }

    /// Parses using the stream `input` by calling [`Stream::uncons`] one or more times.
    ///
    /// Semantically equivalent to [`parse_stream`], except this method returns a flattened result
    /// type, combining `Result` and [`Consumed`] into a single [`FastResult`].
    ///
    /// [`Stream::uncons`]: trait.StreamOnce.html#tymethod.uncons
    /// [`parse_stream`]: trait.Parser.html#method.parse_stream
    /// [`Consumed`]: enum.Consumed.html
    /// [`FastResult`]: enum.FastResult.html
    #[inline]
    fn parse_stream_consumed(
        &mut self,
        input: &mut Self::Input,
    ) -> ConsumedResult<Self::Output, Self::Input> {
        self.parse_stream_consumed_partial(input, &mut Default::default())
    }

    #[inline]
    fn parse_stream_consumed_partial(
        &mut self,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input> {
        let before = input.checkpoint();
        let mut result = self.parse_partial(input, state);
        if let FastResult::EmptyErr(ref mut error) = result {
            input.reset(before.clone());
            if let Ok(t) = input.uncons::<UnexpectedParse>() {
                input.reset(before);
                error.error.add_unexpected(Info::Token(t));
            }
            self.add_error(error);
        }
        result
    }

    /// Parses using the stream `input` by calling [`Stream::uncons`] one or more times.
    ///
    /// Specialized version of [`parse_stream_consumed`] which permits error value creation to be
    /// skipped in the common case.
    ///
    /// When this parser returns `EmptyErr`, this method is allowed to return an empty
    /// [`ParseError`]. The error value that would have been returned can instead be obtained by
    /// calling [`add_error`]. This allows a parent parser such as `choice` to skip the creation of
    /// an unnecessary error value, if an alternative parser succeeds.
    ///
    /// External callers should never have to call this function directly.
    ///
    /// Parsers should seek to implement this function instead of the above two, if errors can be
    /// encountered before consuming input. The default implementation always returns all errors,
    /// with [`add_error`] being a no-op.
    ///
    /// [`Stream::uncons`]: trait.StreamOnce.html#tymethod.uncons
    /// [`parse_stream_consumed`]: trait.Parser.html#method.parse_stream_consumed
    /// [`ParseError`]: struct.ParseError.html
    /// [`add_error`]: trait.Parser.html#method.add_error
    #[inline(always)]
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        self.parse_partial(input, &mut Default::default())
    }

    // TODO
    #[inline(always)]
    fn parse_partial(
        &mut self,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input> {
        let _ = state;
        self.parse_lazy(input)
    }

    /// Adds the first error that would normally be returned by this parser if it failed with an
    /// `EmptyErr` result.
    ///
    /// See [`parse_lazy`] for details.
    ///
    /// [`parse_lazy`]: trait.Parser.html#method.parse_lazy
    fn add_error(&mut self, _error: &mut Tracked<<Self::Input as StreamOnce>::Error>) {}

    /// Returns how many parsers this parser contains
    ///
    /// This should not be implemented explicitly outside of combine.
    #[doc(hidden)]
    fn parser_count(&self) -> ErrorOffset {
        ErrorOffset(1)
    }

    /// Borrows a parser instead of consuming it.
    ///
    /// Used to apply parser combinators on `self` without losing ownership.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::primitives::Consumed;
    /// # use combine::char::{digit, letter};
    /// fn test(input: &mut &'static str) -> ParseResult<(char, char), &'static str> {
    ///     let mut p = digit();
    ///     let ((d, _), consumed) = try!((p.by_ref(), letter()).parse_stream(input));
    ///     let (d2, consumed) = try!(consumed.combine(|_| p.parse_stream(input)));
    ///     Ok(((d, d2), consumed))
    /// }
    ///
    /// fn main() {
    ///     let mut input = "1a23";
    ///     assert_eq!(
    ///         test(&mut input).map(|(t, c)| (t, c.map(|_| input))),
    ///         Ok((('1', '2'), Consumed::Consumed("3")))
    ///     );
    /// }
    /// ```
    fn by_ref(&mut self) -> &mut Self
    where
        Self: Sized,
    {
        self
    }

    /// Discards the value of the `self` parser and returns the value of `p`.
    /// Fails if any of the parsers fails.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::char::digit;
    /// # fn main() {
    /// let result = digit()
    ///     .with(token('i'))
    ///     .parse("9i")
    ///     .map(|x| x.0);
    /// assert_eq!(result, Ok('i'));
    /// # }
    /// ```
    fn with<P2>(self, p: P2) -> With<Self, P2>
    where
        Self: Sized,
        P2: Parser<Input = Self::Input>,
    {
        with(self, p)
    }

    /// Discards the value of the `p` parser and returns the value of `self`.
    /// Fails if any of the parsers fails.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::char::digit;
    /// # fn main() {
    /// let result = digit()
    ///     .skip(token('i'))
    ///     .parse("9i")
    ///     .map(|x| x.0);
    /// assert_eq!(result, Ok('9'));
    /// # }
    /// ```
    fn skip<P2>(self, p: P2) -> Skip<Self, P2>
    where
        Self: Sized,
        P2: Parser<Input = Self::Input>,
    {
        skip(self, p)
    }

    /// Parses with `self` followed by `p`.
    /// Succeeds if both parsers succeed, otherwise fails.
    /// Returns a tuple with both values on success.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::char::digit;
    /// # fn main() {
    /// let result = digit()
    ///     .and(token('i'))
    ///     .parse("9i")
    ///     .map(|x| x.0);
    /// assert_eq!(result, Ok(('9', 'i')));
    /// # }
    /// ```
    fn and<P2>(self, p: P2) -> (Self, P2)
    where
        Self: Sized,
        P2: Parser<Input = Self::Input>,
    {
        (self, p)
    }

    /// Returns a parser which attempts to parse using `self`. If `self` fails without consuming
    /// any input it tries to consume the same input using `p`.
    ///
    /// If you are looking to chain 3 or more parsers using `or` you may consider using the
    /// [`choice!`] macro instead, which can be clearer and may result in a faster parser.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::char::{digit, string};
    /// # fn main() {
    /// let mut parser = string("let")
    ///     .or(digit().map(|_| "digit"))
    ///     .or(string("led"));
    /// assert_eq!(parser.parse("let"), Ok(("let", "")));
    /// assert_eq!(parser.parse("1"), Ok(("digit", "")));
    /// assert!(parser.parse("led").is_err());
    ///
    /// let mut parser2 = string("two").or(string("three"));
    /// // Fails as the parser for "two" consumes the first 't' before failing
    /// assert!(parser2.parse("three").is_err());
    ///
    /// // Use 'try' to make failing parsers always act as if they have not consumed any input
    /// let mut parser3 = try(string("two")).or(try(string("three")));
    /// assert_eq!(parser3.parse("three"), Ok(("three", "")));
    /// # }
    /// ```
    ///
    /// [`choice!`]: ../macro.choice.html
    fn or<P2>(self, p: P2) -> Or<Self, P2>
    where
        Self: Sized,
        P2: Parser<Input = Self::Input, Output = Self::Output>,
    {
        or(self, p)
    }

    /// Parses using `self` and then passes the value to `f` which returns a parser used to parse
    /// the rest of the input.
    ///
    /// Since the parser returned from `f` must have a single
    ///
    /// ```
    /// # #![cfg(feature = "std")]
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::char::digit;
    /// # use combine::primitives::Consumed;
    /// # use combine::easy;
    /// # fn main() {
    /// let result = digit()
    ///     .then(|d| {
    ///         if d == '9' {
    ///             value(9).left()
    ///         }
    ///         else {
    ///             unexpected(d).map(|_| 0).message("Not a nine").right()
    ///         }
    ///     })
    ///     .easy_parse("9");
    /// assert_eq!(result, Ok((9, "")));
    /// # }
    /// ```
    fn then<N, F>(self, f: F) -> Then<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Output) -> N,
        N: Parser<Input = Self::Input>,
    {
        then(self, f)
    }

    /// Uses `f` to map over the parsed value.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::char::digit;
    /// # fn main() {
    /// let result = digit()
    ///     .map(|c| c == '9')
    ///     .parse("9")
    ///     .map(|x| x.0);
    /// assert_eq!(result, Ok(true));
    /// # }
    /// ```
    fn map<F, B>(self, f: F) -> Map<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Output) -> B,
    {
        map(self, f)
    }

    /// Uses `f` to map over the output of `self`. If `f` returns an error the parser fails.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::char::digit;
    /// # use combine::range::take;
    /// # fn main() {
    /// let result = take(4)
    ///     .flat_map(|bs| many(digit()).parse(bs).map(|t| t.0))
    ///     .parse("12abcd");
    /// assert_eq!(result, Ok((String::from("12"), "cd")));
    /// # }
    /// ```
    fn flat_map<F, B>(self, f: F) -> FlatMap<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Output) -> Result<B, <Self::Input as StreamOnce>::Error>,
    {
        flat_map(self, f)
    }

    /// Parses with `self` and if it fails, adds the message `msg` to the error.
    ///
    /// ```
    /// # #![cfg(feature = "std")]
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::easy;
    /// # use combine::state::SourcePosition;
    /// # fn main() {
    /// let result = token('9')
    ///     .message("Not a nine")
    ///     .easy_parse(State::new("8"));
    /// assert_eq!(result, Err(easy::Errors {
    ///     position: SourcePosition::default(),
    ///     errors: vec![
    ///         easy::Error::Unexpected('8'.into()),
    ///         easy::Error::Expected('9'.into()),
    ///         easy::Error::Message("Not a nine".into())
    ///     ]
    /// }));
    /// # }
    /// ```
    fn message<S>(self, msg: S) -> Message<Self>
    where
        Self: Sized,
        S: Into<Info<<Self::Input as StreamOnce>::Item, <Self::Input as StreamOnce>::Range>>,
    {
        message(self, msg.into())
    }

    /// Parses with `self` and if it fails without consuming any input any expected errors are
    /// replaced by `msg`. `msg` is then used in error messages as "Expected `msg`".
    ///
    /// ```
    /// # #![cfg(feature = "std")]
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::easy;
    /// # use combine::state::SourcePosition;
    /// # fn main() {
    /// let result = token('9')
    ///     .expected("nine")
    ///     .easy_parse(State::new("8"));
    /// assert_eq!(result, Err(easy::Errors {
    ///     position: SourcePosition::default(),
    ///     errors: vec![
    ///         easy::Error::Unexpected('8'.into()),
    ///         easy::Error::Expected("nine".into())
    ///     ]
    /// }));
    /// # }
    /// ```
    fn expected<S>(self, msg: S) -> Expected<Self>
    where
        Self: Sized,
        S: Into<Info<<Self::Input as StreamOnce>::Item, <Self::Input as StreamOnce>::Range>>,
    {
        expected(self, msg.into())
    }

    /// Parses with `self` and applies `f` on the result if `self` parses successfully.
    /// `f` may optionally fail with an error which is automatically converted to a `ParseError`.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::state::SourcePosition;
    /// # use combine::char::digit;
    /// # fn main() {
    /// let mut parser = many1(digit())
    ///     .and_then(|s: String| s.parse::<i32>());
    /// let result = parser.easy_parse(State::new("1234")).map(|(x, state)| (x, state.input));
    /// assert_eq!(result, Ok((1234, "")));
    /// let result = parser.easy_parse(State::new("999999999999999999999999"));
    /// assert!(result.is_err());
    /// // Errors are report as if they occured at the start of the parse
    /// assert_eq!(result.unwrap_err().position, SourcePosition { line: 1, column: 1 });
    /// # }
    /// ```
    fn and_then<F, O, E, I>(self, f: F) -> AndThen<Self, F>
    where
        Self: Parser<Input = I> + Sized,
        F: FnMut(Self::Output) -> Result<O, E>,
        I: Stream,
        E: Into<<I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError>,
    {
        and_then(self, f)
    }

    /// Creates an iterator from a parser and a state. Can be used as an alternative to [`many`]
    /// when collecting directly into a `FromIterator` type is not desirable.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::char::{char, digit};
    /// # fn main() {
    /// let mut buffer = String::new();
    /// let number = parser(|input| {
    ///     buffer.clear();
    ///     let mut iter = digit().iter(input);
    ///     buffer.extend(&mut iter);
    ///     let i = buffer.parse::<i32>().unwrap();
    ///     iter.into_result(i)
    /// });
    /// let result = sep_by(number, char(','))
    ///     .parse("123,45,6");
    /// assert_eq!(result, Ok((vec![123, 45, 6], "")));
    /// # }
    /// ```
    ///
    /// [`many`]: ../combinator/fn.many.html
    fn iter<'a>(self, input: &'a mut <Self as Parser>::Input) -> Iter<'a, Self, Self::PartialState>
    where
        Self: Parser + Sized,
    {
        Iter::new(self, input, Default::default())
    }

    /// Creates an iterator from a parser and a state. Can be used as an alternative to [`many`]
    /// when collecting directly into a `FromIterator` type is not desirable.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::char::{char, digit};
    /// # fn main() {
    /// let mut buffer = String::new();
    /// let number = parser(|input| {
    ///     buffer.clear();
    ///     let mut iter = digit().iter(input);
    ///     buffer.extend(&mut iter);
    ///     let i = buffer.parse::<i32>().unwrap();
    ///     iter.into_result(i)
    /// });
    /// let result = sep_by(number, char(','))
    ///     .parse("123,45,6");
    /// assert_eq!(result, Ok((vec![123, 45, 6], "")));
    /// # }
    /// ```
    ///
    /// [`many`]: ../combinator/fn.many.html
    fn partial_iter<'a, 's>(
        self,
        input: &'a mut <Self as Parser>::Input,
        partial_state: &'s mut Self::PartialState,
    ) -> Iter<'a, Self, &'s mut Self::PartialState>
    where
        Self: Parser + Sized,
    {
        Iter::new(self, input, partial_state)
    }

    /// Turns the parser into a trait object by putting it in a `Box`. Can be used to easily
    /// return parsers from functions without naming the type.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # fn main() {
    /// fn test<'input, F>(
    ///     c: char,
    ///     f: F)
    ///     -> Box<Parser<Input = &'input str, Output = (char, char), PartialState = ()>>
    ///     where F: FnMut(char) -> bool + 'static
    /// {
    ///     ::combine::combinator::no_partial((token(c), satisfy(f))).boxed()
    /// }
    /// let result = test('a', |c| c >= 'a' && c <= 'f')
    ///     .parse("ac");
    /// assert_eq!(result, Ok((('a', 'c'), "")));
    /// # }
    /// ```
    #[cfg(feature = "std")]
    fn boxed<'a>(
        self,
    ) -> Box<
        Parser<Input = Self::Input, Output = Self::Output, PartialState = Self::PartialState> + 'a,
    >
    where
        Self: Sized + 'a,
    {
        Box::new(self)
    }

    /// Wraps the parser into the `Either` enum which allows combinators such as `then` to return
    /// multiple different parser types (merging them to one)
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::char::{digit, letter};
    /// # fn main() {
    /// let mut parser = any().then(|c|
    ///     if c == '#' {
    ///         skip_many(satisfy(|c| c != '\n'))
    ///             .with(value("".to_string()))
    ///             .left()
    ///     } else {
    ///         many1(letter())
    ///             .map(move |mut s: String| { s.insert(0, c); s })
    ///             .right()
    ///     });
    ///
    /// let result = parser.parse("ac2");
    /// assert_eq!(result, Ok(("ac".to_string(), "2")));
    ///
    /// let result = parser.parse("# ac2");
    /// assert_eq!(result, Ok(("".to_string(), "")));
    /// # }
    /// ```
    fn left<R>(self) -> Either<Self, R>
    where
        Self: Sized,
        R: Parser<Input = Self::Input, Output = Self::Output>,
    {
        Either::Left(self)
    }

    /// Wraps the parser into the `Either` enum which allows combinators such as `then` to return
    /// multiple different parser types (merging them to one)
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::char::{digit, letter};
    /// # fn main() {
    /// let mut parser = any().then(|c|
    ///     if c == '#' {
    ///         skip_many(satisfy(|c| c != '\n'))
    ///             .with(value("".to_string()))
    ///             .left()
    ///     } else {
    ///         many1(letter())
    ///             .map(move |mut s: String| { s.insert(0, c); s })
    ///             .right()
    ///     });
    ///
    /// let result = parser.parse("ac2");
    /// assert_eq!(result, Ok(("ac".to_string(), "2")));
    ///
    /// let result = parser.parse("# ac2");
    /// assert_eq!(result, Ok(("".to_string(), "")));
    /// # }
    /// ```
    fn right<L>(self) -> Either<L, Self>
    where
        Self: Sized,
        L: Parser<Input = Self::Input, Output = Self::Output>,
    {
        Either::Right(self)
    }
}

impl<'a, I, O, P: ?Sized> Parser for &'a mut P
where
    I: Stream,
    P: Parser<Input = I, Output = O>,
{
    type Input = I;
    type Output = O;
    type PartialState = P::PartialState;

    #[inline(always)]
    fn parse_partial(
        &mut self,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input> {
        (**self).parse_partial(input, state)
    }

    #[inline(always)]
    fn add_error(&mut self, error: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        (**self).add_error(error)
    }
}

#[cfg(feature = "std")]
impl<P> Parser for Box<P>
where
    P: ?Sized + Parser,
{
    type Input = P::Input;
    type Output = P::Output;
    type PartialState = P::PartialState;

    #[inline(always)]
    fn parse_partial(
        &mut self,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input> {
        (**self).parse_partial(input, state)
    }

    #[inline(always)]
    fn add_error(&mut self, error: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        (**self).add_error(error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    #[inline]
    fn uncons_range_at_end() {
        assert_eq!("".uncons_range::<UnexpectedParse>(0), Ok(""));
        assert_eq!("123".uncons_range::<UnexpectedParse>(3), Ok("123"));
        assert_eq!((&[1][..]).uncons_range::<UnexpectedParse>(1), Ok(&[1][..]));
        let s: &[u8] = &[];
        assert_eq!(
            SliceStream(s).uncons_range::<UnexpectedParse>(0),
            Ok(&[][..])
        );
    }
}

#[cfg(all(feature = "std", test))]
mod tests_std {
    use super::*;

    #[derive(Clone, PartialEq, Debug)]
    struct CloneOnly {
        s: String,
    }

    #[test]
    fn parse_clone_but_not_copy() {
        // This verifies we can parse slice references with an item type that is Clone but not Copy.
        let input = &[
            CloneOnly { s: "x".to_string() },
            CloneOnly { s: "y".to_string() },
        ][..];
        let result = ::range::take_while(|c: CloneOnly| c.s == "x".to_string()).parse(input);
        assert_eq!(
            result,
            Ok((
                &[CloneOnly { s: "x".to_string() }][..],
                &[CloneOnly { s: "y".to_string() }][..]
            ))
        );
    }
}

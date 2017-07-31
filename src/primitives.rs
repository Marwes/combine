use std::any::Any;
use std::cell::UnsafeCell;
use std::collections::VecDeque;
use std::error::Error as StdError;
use std::fmt;
use std::io::{Bytes, Read};

use self::FastResult::*;

use combinator::{and_then, expected, flat_map, map, message, or, skip, then, with, AndThen,
                 Expected, FlatMap, Iter, Map, Message, Or, Skip, Then, With};

#[macro_export]
macro_rules! ctry {
    ($result: expr) => {
        match $result {
            $crate::primitives::FastResult::ConsumedOk((x, i)) => (x, $crate::primitives::Consumed::Consumed(i)),
            $crate::primitives::FastResult::EmptyOk((x, i)) => (x, $crate::primitives::Consumed::Empty(i)),
            $crate::primitives::FastResult::ConsumedErr(err) => return $crate::primitives::FastResult::ConsumedErr(err.into()),
            $crate::primitives::FastResult::EmptyErr(err) => return $crate::primitives::FastResult::EmptyErr(err.into()),
        }
    }
}

/// Struct which represents a position in a source file.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct SourcePosition {
    /// Current line of the input
    pub line: i32,
    /// Current column of the input
    pub column: i32,
}

/// Newtype around a pointer offset into a slice stream (`&[T]`/`&str`).
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
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
    /// let err = token('a').parse(text).unwrap_err();
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

/// Struct which represents a position in a byte stream.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct BytePosition {
    /// Current position
    pub position: usize,
}

impl fmt::Display for BytePosition {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "position: {}", self.position)
    }
}

/// Enum holding error information. Variants are defined for `Stream::Item` and `Stream::Range` as
/// well as string variants holding simple descriptions.
///
/// As there is implementations of `From` for `T: Positioner`, `String` and `&'static str` the
/// constructor need not be used directly as calling `msg.into()` should turn a message into the
/// correct `Info` variant.
#[derive(Clone, Debug)]
pub enum Info<T, R> {
    Token(T),
    Range(R),
    Owned(String),
    Borrowed(&'static str),
}

impl<T, R> Info<T, R> {
    pub fn map_token<F, U>(self, f: F) -> Info<U, R>
    where
        F: FnOnce(T) -> U,
    {
        use self::Info::*;
        match self {
            Token(t) => Token(f(t)),
            Range(r) => Range(r),
            Owned(s) => Owned(s),
            Borrowed(x) => Borrowed(x),
        }
    }

    pub fn map_range<F, S>(self, f: F) -> Info<T, S>
    where
        F: FnOnce(R) -> S,
    {
        use self::Info::*;
        match self {
            Token(t) => Token(t),
            Range(r) => Range(f(r)),
            Owned(s) => Owned(s),
            Borrowed(x) => Borrowed(x),
        }
    }
}

impl<T: PartialEq, R: PartialEq> PartialEq for Info<T, R> {
    fn eq(&self, other: &Info<T, R>) -> bool {
        match (self, other) {
            (&Info::Token(ref l), &Info::Token(ref r)) => l == r,
            (&Info::Range(ref l), &Info::Range(ref r)) => l == r,
            (&Info::Owned(ref l), &Info::Owned(ref r)) => l == r,
            (&Info::Borrowed(l), &Info::Owned(ref r)) => l == r,
            (&Info::Owned(ref l), &Info::Borrowed(r)) => l == r,
            (&Info::Borrowed(l), &Info::Borrowed(r)) => l == r,
            _ => false,
        }
    }
}
impl<T: fmt::Display, R: fmt::Display> fmt::Display for Info<T, R> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Info::Token(ref c) => write!(f, "{}", c),
            Info::Range(ref c) => write!(f, "{}", c),
            Info::Owned(ref s) => write!(f, "{}", s),
            Info::Borrowed(s) => write!(f, "{}", s),
        }
    }
}

impl<R> From<char> for Info<char, R> {
    fn from(s: char) -> Info<char, R> {
        Info::Token(s)
    }
}
impl<T, R> From<String> for Info<T, R> {
    fn from(s: String) -> Info<T, R> {
        Info::Owned(s)
    }
}

impl<T, R> From<&'static str> for Info<T, R> {
    fn from(s: &'static str) -> Info<T, R> {
        Info::Borrowed(s)
    }
}

/// Enum used to store information about an error that has occurred during parsing.
#[derive(Debug)]
pub enum Error<T, R> {
    /// Error indicating an unexpected token has been encountered in the stream
    Unexpected(Info<T, R>),
    /// Error indicating that the parser expected something else
    Expected(Info<T, R>),
    /// Generic message
    Message(Info<T, R>),
    /// Variant for containing other types of errors
    Other(Box<StdError + Send + Sync>),
}

impl<T, R> Error<T, R> {
    pub fn map_token<F, U>(self, f: F) -> Error<U, R>
    where
        F: FnOnce(T) -> U,
    {
        use self::Error::*;
        match self {
            Unexpected(x) => Unexpected(x.map_token(f)),
            Expected(x) => Expected(x.map_token(f)),
            Message(x) => Message(x.map_token(f)),
            Other(x) => Other(x),
        }
    }

    pub fn map_range<F, S>(self, f: F) -> Error<T, S>
    where
        F: FnOnce(R) -> S,
    {
        use self::Error::*;
        match self {
            Unexpected(x) => Unexpected(x.map_range(f)),
            Expected(x) => Expected(x.map_range(f)),
            Message(x) => Message(x.map_range(f)),
            Other(x) => Other(x),
        }
    }
}

impl<T: PartialEq, R: PartialEq> PartialEq for Error<T, R> {
    fn eq(&self, other: &Error<T, R>) -> bool {
        match (self, other) {
            (&Error::Unexpected(ref l), &Error::Unexpected(ref r)) |
            (&Error::Expected(ref l), &Error::Expected(ref r)) |
            (&Error::Message(ref l), &Error::Message(ref r)) => l == r,
            _ => false,
        }
    }
}

impl<E, T, R> From<E> for Error<T, R>
where
    E: StdError + 'static + Send + Sync,
{
    fn from(e: E) -> Error<T, R> {
        Error::Other(Box::new(e))
    }
}

impl<T, R> Error<T, R> {
    /// Returns the `end_of_input` error.
    pub fn end_of_input() -> Error<T, R> {
        Error::Unexpected("end of input".into())
    }

    /// Formats a slice of errors in a human readable way.
    ///
    /// ```rust
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::char::*;
    ///
    /// # fn main() {
    /// let input = r"
    ///   ,123
    /// ";
    /// let result = spaces().with(char('.').or(char('a')).or(digit()))
    ///     .parse(State::new(input));
    /// let m = format!("{}", result.unwrap_err());
    /// let expected = r"Parse error at line: 2, column: 3
    /// Unexpected `,`
    /// Expected `.`, `a` or `digit`
    /// ";
    /// assert_eq!(m, expected);
    /// # }
    /// ```
    pub fn fmt_errors(errors: &[Error<T, R>], f: &mut fmt::Formatter) -> fmt::Result
    where
        T: fmt::Display,
        R: fmt::Display,
    {
        // First print the token that we did not expect
        // There should really just be one unexpected message at this point though we print them
        // all to be safe
        let unexpected = errors.iter().filter(|e| match **e {
            Error::Unexpected(_) => true,
            _ => false,
        });
        for error in unexpected {
            try!(writeln!(f, "{}", error));
        }

        // Then we print out all the things that were expected in a comma separated list
        // 'Expected 'a', 'expression' or 'let'
        let iter = || {
            errors.iter().filter_map(|e| match *e {
                Error::Expected(ref err) => Some(err),
                _ => None,
            })
        };
        let expected_count = iter().count();
        for (i, message) in iter().enumerate() {
            let s = match i {
                0 => "Expected",
                _ if i < expected_count - 1 => ",",
                // Last expected message to be written
                _ => " or",
            };
            try!(write!(f, "{} `{}`", s, message));
        }
        if expected_count != 0 {
            try!(writeln!(f, ""));
        }
        // If there are any generic messages we print them out last
        let messages = errors.iter().filter(|e| match **e {
            Error::Message(_) | Error::Other(_) => true,
            _ => false,
        });
        for error in messages {
            try!(writeln!(f, "{}", error));
        }
        Ok(())
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
    #[deprecated(since = "2.3.1", note = "Renamed to into_consumed")]
    pub fn as_consumed(self) -> Consumed<T> {
        self.into_consumed()
    }

    /// Converts `self` into the `Consumed` state.
    pub fn into_consumed(self) -> Consumed<T> {
        Consumed::Consumed(self.into_inner())
    }

    /// Converts `self` into the `Empty` state.
    #[deprecated(since = "2.3.1", note = "Renamed to into_empty")]
    pub fn as_empty(self) -> Consumed<T> {
        self.into_empty()
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
    /// fn char(input: &str) -> ParseResult<char, &str> {
    ///     let (c, input) = try!(satisfy(|c| c != '"').parse_stream(input));
    ///     match c {
    ///         //Since the `char` parser has already consumed some of the input `combine` is used
    ///         //propagate the consumed state to the next part of the parser
    ///         '\\' => input.combine(|input| {
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
    ///         _ => Ok((c, input))
    ///     }
    /// }
    /// let result = many(parser(char))
    ///     .parse(r#"abc\"\\"#);
    /// assert_eq!(result, Ok((r#"abc"\"#.to_string(), "")));
    /// }
    /// ```
    pub fn combine<F, U, I>(self, f: F) -> ParseResult<U, I>
    where
        F: FnOnce(T) -> ParseResult<U, I>,
        I: StreamOnce + Positioned,
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
    pub fn combine_consumed<F, U, I>(self, f: F) -> ConsumedResult<U, I>
    where
        F: FnOnce(T) -> ConsumedResult<U, I>,
        I: StreamOnce + Positioned,
    {
        use self::FastResult::*;
        match self {
            Consumed::Consumed(x) => match f(x) {
                EmptyOk((v, rest)) => ConsumedOk((v, rest)),
                EmptyErr(err) => ConsumedErr(err),
                y => y,
            },
            Consumed::Empty(x) => f(x),
        }
    }
}

/// Alias over `ParseError` for `StreamOnce` types
pub type StreamError<S> = ParseError<
    <S as Positioned>::Position,
    <S as StreamOnce>::Item,
    <S as StreamOnce>::Range,
>;

/// Struct which hold information about an error that occured at a specific position.
/// Can hold multiple instances of `Error` if more that one error occured in the same position.
#[derive(Debug, PartialEq)]
pub struct ParseError<P, I, R> {
    /// The position where the error occurred
    pub position: P,
    /// A vector containing specific information on what errors occurred at `position`. Usually
    /// a fully formed message contains one `Unexpected` error and one or more `Expected` errors.
    /// `Message` and `Other` may also appear (`combine` never generates these errors on its own)
    /// and may warrant custom handling.
    pub errors: Vec<Error<I, R>>,
}

impl<P, I, R> ParseError<P, I, R> {
    /// Constructs a new `ParseError` which occurred at `position`.
    pub fn new(position: P, error: Error<I, R>) -> ParseError<P, I, R> {
        ParseError::from_errors(position, vec![error])
    }

    /// Constructs an error with no other information than the position it occurred at.
    pub fn empty(position: P) -> ParseError<P, I, R> {
        ParseError::from_errors(position, vec![])
    }

    /// Constructs a `ParseError` with multiple causes.
    pub fn from_errors(position: P, errors: Vec<Error<I, R>>) -> ParseError<P, I, R> {
        ParseError {
            position: position,
            errors: errors,
        }
    }

    /// Constructs an end of input error. Should be returned by parsers which encounter end of
    /// input unexpectedly.
    pub fn end_of_input(position: P) -> ParseError<P, I, R> {
        ParseError::new(position, Error::end_of_input())
    }

    /// Adds a `Message` error, taking care not to add duplicated errors.
    #[deprecated(since = "2.3.0", note = "Use `add_error(Error::Message())` instead")]
    pub fn add_message<M>(&mut self, message: M)
    where
        M: Into<Info<I, R>>,
        I: PartialEq,
        R: PartialEq,
    {
        self.add_error(Error::Message(message.into()));
    }

    /// Adds an error if `error` does not exist in this `ParseError` already (as determined byte
    /// `PartialEq`).
    pub fn add_error(&mut self, error: Error<I, R>)
    where
        I: PartialEq,
        R: PartialEq,
    {
        // Don't add duplicate errors
        if self.errors.iter().all(|err| *err != error) {
            self.errors.push(error);
        }
    }

    /// Remvoes all `Expected` errors in `self` and adds `info` instead.
    pub fn set_expected(&mut self, info: Info<I, R>) {
        // Remove all other expected messages
        self.errors.retain(|e| match *e {
            Error::Expected(_) => false,
            _ => true,
        });
        self.errors.push(Error::Expected(info));
    }

    /// Merges two `ParseError`s. If they exist at the same position the errors of `other` are
    /// added to `self` (using `add_error` to skip duplicates). If they are not at the same
    /// position the error furthest ahead are returned, ignoring the other `ParseError`.
    pub fn merge(mut self, other: ParseError<P, I, R>) -> ParseError<P, I, R>
    where
        P: Ord,
        I: PartialEq,
        R: PartialEq,
    {
        use std::cmp::Ordering;
        // Only keep the errors which occurred after consuming the most amount of data
        match self.position.cmp(&other.position) {
            Ordering::Less => other,
            Ordering::Greater => self,
            Ordering::Equal => {
                for message in other.errors {
                    self.add_error(message);
                }
                self
            }
        }
    }

    /// Maps the position to a new value
    pub fn map_position<F, Q>(self, f: F) -> ParseError<Q, I, R>
    where
        F: FnOnce(P) -> Q,
    {
        ParseError::from_errors(f(self.position), self.errors)
    }

    /// Maps all token variants to a new value
    pub fn map_token<F, U>(self, mut f: F) -> ParseError<P, U, R>
    where
        F: FnMut(I) -> U,
    {
        ParseError::from_errors(
            self.position,
            self.errors
                .into_iter()
                .map(|error| error.map_token(&mut f))
                .collect(),
        )
    }

    /// Maps all range variants to a new value.
    ///
    /// ```
    /// use combine::Parser;
    /// use combine::range::range;
    /// println!(
    ///     "{}",
    ///     range(&"HTTP"[..])
    ///         .parse("HTT")
    ///         .unwrap_err()
    ///         .map_range(|bytes| format!("{:?}", bytes))
    /// );
    /// ```
    pub fn map_range<F, S>(self, mut f: F) -> ParseError<P, I, S>
    where
        F: FnMut(R) -> S,
    {
        ParseError::from_errors(
            self.position,
            self.errors
                .into_iter()
                .map(|error| error.map_range(&mut f))
                .collect(),
        )
    }
}

impl<P, I, R> StdError for ParseError<P, I, R>
where
    P: fmt::Display + fmt::Debug + Any,
    I: fmt::Display + fmt::Debug + Any,
    R: fmt::Display + fmt::Debug + Any,
{
    fn description(&self) -> &str {
        "parse error"
    }
}

impl<P, I, R> fmt::Display for ParseError<P, I, R>
where
    P: fmt::Display,
    I: fmt::Display,
    R: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(writeln!(f, "Parse error at {}", self.position));
        Error::fmt_errors(&self.errors, f)
    }
}

impl fmt::Display for SourcePosition {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "line: {}, column: {}", self.line, self.column)
    }
}
impl<T: fmt::Display, R: fmt::Display> fmt::Display for Error<T, R> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::Unexpected(ref c) => write!(f, "Unexpected `{}`", c),
            Error::Expected(ref s) => write!(f, "Expected `{}`", s),
            Error::Message(ref msg) => msg.fmt(f),
            Error::Other(ref err) => err.fmt(f),
        }
    }
}

/// The `State<I>` struct keeps track of the current position in the stream `I` using the
/// `Positioner` trait to update the position.
#[derive(Clone, PartialEq)]
pub struct State<I>
where
    I: StreamOnce,
    I::Item: Positioner,
{
    /// The current position
    pub position: <I::Item as Positioner>::Position,
    /// The input stream used when items are requested
    pub input: I,
}

impl<I> fmt::Debug for State<I>
where
    I: Stream + fmt::Debug,
    I::Item: Positioner,
    <I::Item as Positioner>::Position: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "State {{ position: {:?}, input: {:?} }}",
            self.position,
            self.input
        )
    }
}

impl<I> State<I>
where
    I: StreamOnce,
    I::Item: Positioner,
{
    /// Creates a new `State<I>` from an input stream. Initializes the position to
    /// `Positioner::start()`.
    pub fn new(input: I) -> State<I> {
        State {
            position: <I::Item as Positioner>::start(),
            input: input,
        }
    }
}

impl<I> Positioned for State<I>
where
    I: Stream,
    I::Item: Positioner,
{
    type Position = <I::Item as Positioner>::Position;

    #[inline(always)]
    fn position(&self) -> Self::Position {
        self.position.clone()
    }
}

impl<I> StreamOnce for State<I>
where
    I: StreamOnce,
    I::Item: Positioner,
{
    type Item = I::Item;
    type Range = I::Range;

    #[inline]
    fn uncons(&mut self) -> Result<I::Item, Error<I::Item, I::Range>> {
        match self.input.uncons() {
            Ok(c) => {
                c.update(&mut self.position);
                Ok(c)
            }
            Err(err) => Err(err),
        }
    }
}

impl<I, E> RangeStream for State<I>
where
    I: RangeStream<Item = E>,
    I::Range: Range + Positioner<Position = E::Position>,
    E: Positioner + Clone,
{
    #[inline]
    fn uncons_range(&mut self, size: usize) -> Result<I::Range, Error<I::Item, I::Range>> {
        let position = &mut self.position;
        self.input.uncons_range(size).map(|value| {
            value.update(position);
            value
        })
    }

    #[inline]
    fn uncons_while<F>(&mut self, mut predicate: F) -> Result<I::Range, Error<I::Item, I::Range>>
    where
        F: FnMut(I::Item) -> bool,
    {
        let position = &mut self.position;
        self.input.uncons_while(|t| if predicate(t.clone()) {
            t.update(position);
            true
        } else {
            false
        })
    }

    #[inline]
    fn distance(&self, end: &Self) -> usize {
        self.input.distance(&end.input)
    }
}

impl<I, E> FullRangeStream for State<I>
where
    I: RangeStream<Item = E>,
    I::Range: Range + Positioner<Position = E::Position>,
    E: Positioner + Clone,
    I: FullRangeStream,
{
    fn range(&self) -> Self::Range {
        self.input.range()
    }
}

/// A type alias over the specific `Result` type used by parsers to indicate wether they were
/// successful or not.
/// `O` is the type that is output on success.
/// `I` is the specific stream type used in the parser.
pub type ParseResult<O, I> = Result<(O, Consumed<I>), Consumed<StreamError<I>>>;

pub trait Positioned {
    /// Type which represents the position in a stream.
    /// `Ord` is required to allow parsers to determine which of two positions are further ahead.
    type Position: Clone + Ord;

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

    /// Takes a stream and removes its first item, yielding the item and the rest of the elements.
    /// Returns `Err` if no element could be retrieved.
    fn uncons(&mut self) -> Result<Self::Item, Error<Self::Item, Self::Range>>;
}

/// A stream of tokens which can be duplicated
pub trait Stream: StreamOnce + Positioned + Clone {}

impl<I> Stream for I
where
    I: StreamOnce + Positioned + Clone,
{
}

#[inline]
pub fn uncons<I>(mut input: I) -> ParseResult<I::Item, I>
where
    I: Stream,
{
    let position = input.position();
    let x = try!(
        input
            .uncons()
            .map_err(|err| Consumed::Empty(ParseError::new(position, err)))
    );
    Ok((x, Consumed::Consumed(input)))
}

/// A `RangeStream` is an extension of `Stream` which allows for zero copy parsing.
pub trait RangeStream: Stream {
    /// Takes `size` elements from the stream.
    /// Fails if the length of the stream is less than `size`.
    fn uncons_range(&mut self, size: usize) -> Result<Self::Range, Error<Self::Item, Self::Range>>;

    /// Takes items from stream, testing each one with `predicate`.
    /// returns the range of items which passed `predicate`.
    fn uncons_while<F>(&mut self, f: F) -> Result<Self::Range, Error<Self::Item, Self::Range>>
    where
        F: FnMut(Self::Item) -> bool;

    /// Returns the distance between `self` and `end`. The returned `usize` must be so that
    ///
    /// ```ignore
    /// let start = stream.clone();
    /// stream.uncons_range(distance);
    /// start.distance() == distance
    /// ```
    fn distance(&self, end: &Self) -> usize;
}

/// A `RangeStream` which is capable of providing it's entire range.
pub trait FullRangeStream: RangeStream {
    /// Returns the entire range of `self`
    fn range(&self) -> Self::Range;
}

/// Removes items from the input while `predicate` returns `true`.
#[inline]
pub fn uncons_while<I, F>(mut input: I, predicate: F) -> ConsumedResult<I::Range, I>
where
    F: FnMut(I::Item) -> bool,
    I: RangeStream,
    I::Range: Range,
{
    match input.uncons_while(predicate) {
        Err(err) => EmptyErr(ParseError::new(input.position(), err)),
        Ok(x) => if x.len() == 0 {
            EmptyOk((x, input))
        } else {
            ConsumedOk((x, input))
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

impl<'a> RangeStream for &'a str {
    #[inline]
    fn uncons_while<F>(&mut self, mut f: F) -> Result<&'a str, Error<char, &'a str>>
    where
        F: FnMut(Self::Item) -> bool,
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
    fn uncons_range(&mut self, size: usize) -> Result<&'a str, Error<char, &'a str>> {
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
                Err(Error::Message(
                    "uncons_range on non character boundary".into(),
                ))
            }
        } else {
            Err(Error::end_of_input())
        }
    }

    #[inline]
    fn distance(&self, end: &Self) -> usize {
        end.position().0 - self.position().0
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

impl<'a, T> RangeStream for &'a [T]
where
    T: Clone + PartialEq,
{
    #[inline]
    fn uncons_range(&mut self, size: usize) -> Result<&'a [T], Error<T, &'a [T]>> {
        if size <= self.len() {
            let (result, remaining) = self.split_at(size);
            *self = remaining;
            Ok(result)
        } else {
            Err(Error::end_of_input())
        }
    }

    #[inline]
    fn uncons_while<F>(&mut self, mut f: F) -> Result<&'a [T], Error<T, &'a [T]>>
    where
        F: FnMut(Self::Item) -> bool,
    {
        let len = self.iter().take_while(|c| f((**c).clone())).count();
        let (result, remaining) = self.split_at(len);
        *self = remaining;
        Ok(result)
    }

    #[inline]
    fn distance(&self, end: &Self) -> usize {
        end.position().0 - self.position().0
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
    type Position = PointerOffset;

    #[inline(always)]
    fn position(&self) -> Self::Position {
        self.as_bytes().position()
    }
}

impl<'a> StreamOnce for &'a str {
    type Item = char;
    type Range = &'a str;

    #[inline]
    fn uncons(&mut self) -> Result<char, Error<char, &'a str>> {
        let mut chars = self.chars();
        match chars.next() {
            Some(c) => {
                *self = chars.as_str();
                Ok(c)
            }
            None => Err(Error::end_of_input()),
        }
    }
}

impl<'a, T> Positioned for &'a [T] {
    type Position = PointerOffset;

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

    #[inline]
    fn uncons(&mut self) -> Result<T, Error<T, &'a [T]>> {
        match self.split_first() {
            Some((first, rest)) => {
                *self = rest;
                Ok(first.clone())
            }
            None => Err(Error::end_of_input()),
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

impl<'a, T> Positioned for SliceStream<'a, T> {
    type Position = PointerOffset;

    #[inline(always)]
    fn position(&self) -> Self::Position {
        self.0.position()
    }
}

impl<'a, T> StreamOnce for SliceStream<'a, T>
where
    T: Clone + PartialEq + 'a,
{
    type Item = &'a T;
    type Range = &'a [T];

    #[inline]
    fn uncons(&mut self) -> Result<&'a T, Error<&'a T, &'a [T]>> {
        match self.0.split_first() {
            Some((first, rest)) => {
                self.0 = rest;
                Ok(first)
            }
            None => Err(Error::end_of_input()),
        }
    }
}

impl<'a, T> RangeStream for SliceStream<'a, T>
where
    T: Clone + PartialEq + 'a,
{
    #[inline]
    fn uncons_range(&mut self, size: usize) -> Result<&'a [T], Error<&'a T, &'a [T]>> {
        if size <= self.0.len() {
            let (range, rest) = self.0.split_at(size);
            self.0 = rest;
            Ok(range)
        } else {
            Err(Error::end_of_input())
        }
    }

    #[inline]
    fn uncons_while<F>(&mut self, mut f: F) -> Result<&'a [T], Error<&'a T, &'a [T]>>
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
        self.0.distance(&end.0)
    }
}

impl<'a, T> FullRangeStream for SliceStream<'a, T>
where
    T: Clone + PartialEq + 'a,
{
    fn range(&self) -> Self::Range {
        self.0
    }
}

/// Wrapper around iterators which allows them to be treated as a stream.
/// Returned by [`from_iter`].
///
/// [`from_iter`]: fn.from_iter.html
#[derive(Clone, Debug)]
pub struct IteratorStream<I>(I, usize);


impl<I> IteratorStream<I>
where
    I: Iterator,
{
    /// Converts an `Iterator` into a stream.
    pub fn new(iter: I) -> IteratorStream<I> {
        IteratorStream(iter, 0)
    }
}

#[deprecated(since = "2.4.0", note = "please use `IteratorStream::new` instead")]
pub fn from_iter<I>(iter: I) -> IteratorStream<I>
where
    I: Iterator,
{
    IteratorStream::new(iter)
}

impl<I> Iterator for IteratorStream<I>
where
    I: Iterator,
{
    type Item = I::Item;
    fn next(&mut self) -> Option<I::Item> {
        match self.0.next() {
            Some(x) => {
                self.1 += 1;
                Some(x)
            }
            None => None,
        }
    }
}

impl<I> Positioned for IteratorStream<I> {
    type Position = usize;

    #[inline(always)]
    fn position(&self) -> Self::Position {
        self.1
    }
}

impl<I: Iterator> StreamOnce for IteratorStream<I>
where
    I::Item: Clone + PartialEq,
{
    type Item = I::Item;
    type Range = I::Item;

    #[inline]
    fn uncons(&mut self) -> Result<I::Item, Error<I::Item, I::Item>> {
        match self.next() {
            Some(x) => Ok(x),
            None => Err(Error::end_of_input()),
        }
    }
}

pub struct ReadStream<R> {
    bytes: Bytes<R>,
    offset: usize,
}

impl<R> Positioned for ReadStream<R> {
    type Position = usize;

    #[inline(always)]
    fn position(&self) -> Self::Position {
        self.offset
    }
}

impl<R: Read> StreamOnce for ReadStream<R> {
    type Item = u8;
    type Range = u8;

    #[inline]
    fn uncons(&mut self) -> Result<u8, Error<u8, u8>> {
        match self.bytes.next() {
            Some(Ok(b)) => {
                self.offset += 1;
                Ok(b)
            }
            Some(Err(err)) => Err(err.into()),
            None => Err(Error::end_of_input()),
        }
    }
}

impl<R> ReadStream<R>
where
    R: Read,
{
    /// Creates a `StreamOnce` instance from a value implementing `std::io::Read`.
    ///
    /// ```rust
    /// # extern crate combine;
    /// use combine::*;
    /// use combine::byte::*;
    /// use combine::primitives::{BufferedStream, ReadStream};
    /// use std::io::Read;
    ///
    /// # fn main() {
    /// let mut input: &[u8] = b"123,";
    /// let stream = BufferedStream::new(ReadStream::new(&mut input), 1);
    /// let result = (many(digit()), byte(b','))
    ///     .parse(stream.as_stream())
    ///     .map(|t| t.0);
    /// assert_eq!(result, Ok((vec![b'1', b'2', b'3'], b',')));
    /// # }
    /// ```
    pub fn new(read: R) -> ReadStream<R> {
        ReadStream {
            bytes: read.bytes(),
            offset: 0,
        }
    }
}

#[deprecated(since = "2.4.0", note = "please use `ReadStream::new` instead")]
pub fn from_read<R>(read: R) -> ReadStream<R>
where
    R: Read,
{
    ReadStream::new(read)
}

/// Trait for updating the position for types which can be yielded from a `Stream`.
pub trait Positioner: PartialEq {
    /// The type which keeps track of the position.
    type Position: Clone + Ord;
    /// Creates a start position
    fn start() -> Self::Position;
    /// Updates the position given that `self` has been taken from the stream
    fn update(&self, position: &mut Self::Position);
}

impl<'a, T: ?Sized> Positioner for &'a T
where
    T: Positioner,
{
    type Position = T::Position;
    fn start() -> T::Position {
        T::start()
    }
    fn update(&self, position: &mut T::Position) {
        (*self).update(position)
    }
}

impl<T> Positioner for [T]
where
    T: Positioner,
{
    type Position = T::Position;
    fn start() -> T::Position {
        T::start()
    }
    fn update(&self, position: &mut T::Position) {
        for t in self {
            t.update(position);
        }
    }
}

impl<'a, T> Positioner for SliceStream<'a, T>
where
    T: Positioner + 'a,
{
    type Position = T::Position;
    fn start() -> T::Position {
        T::start()
    }
    fn update(&self, position: &mut T::Position) {
        for t in self.0 {
            t.update(position);
        }
    }
}

impl Positioner for str {
    type Position = SourcePosition;
    fn start() -> SourcePosition {
        char::start()
    }
    fn update(&self, position: &mut SourcePosition) {
        for t in self.chars() {
            t.update(position);
        }
    }
}

impl Positioner for char {
    type Position = SourcePosition;
    fn start() -> SourcePosition {
        SourcePosition { line: 1, column: 1 }
    }
    fn update(&self, position: &mut SourcePosition) {
        position.column += 1;
        if *self == '\n' {
            position.column = 1;
            position.line += 1;
        }
    }
}

impl Positioner for u8 {
    type Position = BytePosition;

    fn start() -> BytePosition {
        BytePosition { position: 0 }
    }

    fn update(&self, b: &mut BytePosition) {
        b.position += 1;
    }
}

#[derive(Clone, PartialEq, Debug, Copy)]
pub enum FastResult<T, E> {
    ConsumedOk(T),
    EmptyOk(T),
    ConsumedErr(E),
    EmptyErr(E),
}

impl<T, E> FastResult<T, E> {
    pub fn as_ref(&self) -> FastResult<&T, &E> {
        match *self {
            ConsumedOk(ref t) => ConsumedOk(t),
            EmptyOk(ref t) => EmptyOk(t),
            ConsumedErr(ref e) => ConsumedErr(e),
            EmptyErr(ref e) => EmptyErr(e),
        }
    }

    pub fn and_then<F, T2>(self, f: F) -> F::Output
    where
        F: FnOnce(T) -> FastResult<T2, E>,
    {
        match self {
            ConsumedOk(t) => match f(t) {
                ConsumedOk(t2) | EmptyOk(t2) => ConsumedOk(t2),
                EmptyErr(e) | ConsumedErr(e) => ConsumedErr(e),
            },
            EmptyOk(t) => f(t),
            ConsumedErr(e) => ConsumedErr(e),
            EmptyErr(e) => EmptyErr(e),
        }
    }
}

impl<T, E> ConsumedResult<T, E>
where
    E: StreamOnce + Positioned,
{
    pub fn map<F, T2>(self, f: F) -> ConsumedResult<F::Output, E>
    where
        F: FnOnce(T) -> T2,
    {
        match self {
            ConsumedOk((t, i)) => ConsumedOk((f(t), i)),
            EmptyOk((t, i)) => EmptyOk((f(t), i)),
            ConsumedErr(e) => ConsumedErr(e),
            EmptyErr(e) => EmptyErr(e),
        }
    }
}


/// A `Result` type which has the consumed status flattened into the result.
/// Conversions to and from `std::result::Result` can be done using `result.into()` or
/// `From::from(result)`
pub type ConsumedResult<O, I> = FastResult<(O, I), StreamError<I>>;

impl<T, E> Into<Result<Consumed<T>, Consumed<E>>> for FastResult<T, E> {
    fn into(self) -> Result<Consumed<T>, Consumed<E>> {
        match self {
            ConsumedOk(t) => Ok(Consumed::Consumed(t)),
            EmptyOk(t) => Ok(Consumed::Empty(t)), 
            ConsumedErr(e) => Err(Consumed::Consumed(e)),
            EmptyErr(e) => Err(Consumed::Empty(e)),
        }
    }
}

impl<O, I> Into<ParseResult<O, I>> for ConsumedResult<O, I>
where
    I: StreamOnce + Positioned,
{
    fn into(self) -> ParseResult<O, I> {
        use self::FastResult::*;
        match self {
            ConsumedOk((t, i)) => Ok((t, Consumed::Consumed(i))),
            EmptyOk((t, i)) => Ok((t, Consumed::Empty(i))), 
            ConsumedErr(e) => Err(Consumed::Consumed(e)),
            EmptyErr(e) => Err(Consumed::Empty(e)),
        }
    }
}

impl<O, I> From<ParseResult<O, I>> for ConsumedResult<O, I>
where
    I: StreamOnce + Positioned,
{
    fn from(result: ParseResult<O, I>) -> ConsumedResult<O, I> {
        use self::FastResult::*;
        match result {
            Ok((t, Consumed::Consumed(i))) => ConsumedOk((t, i)),
            Ok((t, Consumed::Empty(i))) => EmptyOk((t, i)),
            Err(Consumed::Consumed(e)) => ConsumedErr(e),
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

    /// Entry point of the parser. Takes some input and tries to parse it.
    ///
    /// Returns the parsed result and the remaining input if the parser succeeds, or a
    /// [`ParseError`] otherwise.
    ///
    /// [`ParseError`]: struct.ParseError.html
    fn parse(
        &mut self,
        input: Self::Input,
    ) -> Result<(Self::Output, Self::Input), StreamError<Self::Input>> {
        match self.parse_stream(input) {
            Ok((v, state)) => Ok((v, state.into_inner())),
            Err(error) => Err(error.into_inner()),
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
    fn parse_stream(&mut self, input: Self::Input) -> ParseResult<Self::Output, Self::Input> {
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
        mut input: Self::Input,
    ) -> ConsumedResult<Self::Output, Self::Input> {
        let mut result = self.parse_lazy(input.clone());
        if let FastResult::EmptyErr(ref mut error) = result {
            if let Ok(t) = input.uncons() {
                error.add_error(Error::Unexpected(Info::Token(t)));
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
    #[inline]
    fn parse_lazy(&mut self, input: Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        self.parse_stream(input).into()
    }

    /// Adds the first error that would normally be returned by this parser if it failed with an
    /// `EmptyErr` result.
    ///
    /// See [`parse_lazy`] for details.
    ///
    /// [`parse_lazy`]: trait.Parser.html#method.parse_lazy
    fn add_error(&mut self, _error: &mut StreamError<Self::Input>) {}

    /// Borrows a parser instead of consuming it.
    ///
    /// Used to apply parser combinators on `self` without losing ownership.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::primitives::Consumed;
    /// # use combine::char::{digit, letter};
    /// fn test() -> ParseResult<(char, char), &'static str> {
    ///     let mut p = digit();
    ///     let ((d, _), input) = try!((p.by_ref(), letter()).parse_stream("1a23"));
    ///     let (d2, input) = try!(input.combine(|input| p.parse_stream(input)));
    ///     Ok(((d, d2), input))
    /// }
    ///
    /// fn main() {
    ///     assert_eq!(test(), Ok((('1', '2'), Consumed::Consumed("3"))));
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
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::char::digit;
    /// # use combine::primitives::{Consumed, Error};
    /// # fn main() {
    /// let result = digit()
    ///     .then(|d| parser(move |input| {
    ///             // Force input to be a &str
    ///             let _: &str = input;
    ///         if d == '9' {
    ///             Ok((9, Consumed::Empty(input)))
    ///         }
    ///         else {
    ///             let position = input.position();
    ///             let err = ParseError::new(position, Error::Message("Not a nine".into()));
    ///             Err((Consumed::Empty(err)))
    ///         }
    ///     }))
    ///     .parse("9");
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
        F: FnMut(Self::Output)
            -> Result<B, StreamError<Self::Input>>,
    {
        flat_map(self, f)
    }

    /// Parses with `self` and if it fails, adds the message `msg` to the error.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::primitives::{Error, Positioner};
    /// # fn main() {
    /// let result = token('9')
    ///     .message("Not a nine")
    ///     .parse(State::new("8"));
    /// assert_eq!(result, Err(ParseError {
    ///     position: <char as Positioner>::start(),
    ///     errors: vec![
    ///         Error::Unexpected('8'.into()),
    ///         Error::Expected('9'.into()),
    ///         Error::Message("Not a nine".into())
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
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::primitives::{Error, Positioner};
    /// # fn main() {
    /// let result = token('9')
    ///     .expected("nine")
    ///     .parse(State::new("8"));
    /// assert_eq!(result, Err(ParseError {
    ///     position: <char as Positioner>::start(),
    ///     errors: vec![Error::Unexpected('8'.into()), Error::Expected("nine".into())]
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
    /// # use combine::primitives::SourcePosition;
    /// # use combine::char::digit;
    /// # fn main() {
    /// let mut parser = many1(digit())
    ///     .and_then(|s: String| s.parse::<i32>());
    /// let result = parser.parse(State::new("1234")).map(|(x, state)| (x, state.input));
    /// assert_eq!(result, Ok((1234, "")));
    /// let result = parser.parse(State::new("999999999999999999999999"));
    /// assert!(result.is_err());
    /// // Errors are report as if they occured at the start of the parse
    /// assert_eq!(result.unwrap_err().position, SourcePosition { line: 1, column: 1 });
    /// # }
    /// ```
    fn and_then<F, O, E>(self, f: F) -> AndThen<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Output) -> Result<O, E>,
        E: Into<Error<<Self::Input as StreamOnce>::Item, <Self::Input as StreamOnce>::Range>>,
    {
        and_then(self, f)
    }

    /// Creates an iterator from a parser and a state. Can be used as an alternative to [`many`] when
    /// collecting directly into a `FromIterator` type is not desirable.
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
    fn iter(self, input: Self::Input) -> Iter<Self>
    where
        Self: Sized,
    {
        Iter::new(self, input)
    }

    /// Turns the parser into a trait object by putting it in a `Box`. Can be used to easily
    /// return parsers from functions without naming the type.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # fn main() {
    /// fn test<'input, F>(c: char, f: F) ->  Box<Parser<Input = &'input str, Output = (char, char)>>
    ///     where F: FnMut(char) -> bool + 'static
    /// {
    ///     (token(c), satisfy(f)).boxed()
    /// }
    /// let result = test('a', |c| c >= 'a' && c <= 'f')
    ///     .parse("ac");
    /// assert_eq!(result, Ok((('a', 'c'), "")));
    /// # }
    /// ```
    fn boxed<'a>(self) -> Box<Parser<Input = Self::Input, Output = Self::Output> + 'a>
    where
        Self: Sized + 'a,
    {
        Box::new(self)
    }
}
impl<'a, I, O, P: ?Sized> Parser for &'a mut P
where
    I: Stream,
    P: Parser<Input = I, Output = O>,
{
    type Input = I;
    type Output = O;

    #[inline(always)]
    fn parse_stream(&mut self, input: I) -> ParseResult<O, I> {
        (**self).parse_stream(input)
    }

    #[inline(always)]
    fn parse_stream_consumed(&mut self, input: I) -> ConsumedResult<O, I> {
        (**self).parse_stream_consumed(input)
    }

    #[inline(always)]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<O, I> {
        (**self).parse_lazy(input)
    }

    #[inline(always)]
    fn add_error(&mut self, error: &mut StreamError<Self::Input>) {
        (**self).add_error(error)
    }
}
impl<I, O, P: ?Sized> Parser for Box<P>
where
    I: Stream,
    P: Parser<Input = I, Output = O>,
{
    type Input = I;
    type Output = O;

    #[inline(always)]
    fn parse_stream(&mut self, input: I) -> ParseResult<O, I> {
        (**self).parse_stream(input)
    }

    #[inline(always)]
    fn parse_stream_consumed(&mut self, input: I) -> ConsumedResult<O, I> {
        (**self).parse_stream_consumed(input)
    }

    #[inline(always)]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<O, I> {
        (**self).parse_lazy(input)
    }

    #[inline(always)]
    fn add_error(&mut self, error: &mut StreamError<Self::Input>) {
        (**self).add_error(error)
    }
}

/// A `BufferedStream` wraps an instance `StreamOnce`, allowing it to be used as a `Stream`.
pub struct BufferedStream<'a, I>
where
    I: StreamOnce + Positioned + 'a,
    I::Item: 'a,
{
    offset: usize,
    buffer: &'a SharedBufferedStream<I>,
}

impl<'a, I> fmt::Debug for BufferedStream<'a, I>
where
    I: StreamOnce + Positioned + 'a,
    I::Item: 'a,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let buffer_offset = unsafe { (*self.buffer.buffer.get()).offset };
        write!(
            f,
            "BufferedStream {{ offset: {:?} buffer_offset: {:?} }}",
            self.offset,
            buffer_offset
        )
    }
}

impl<'a, I> Clone for BufferedStream<'a, I>
where
    I: StreamOnce + Positioned + 'a,
    I::Position: Clone,
    I::Item: 'a,
{
    fn clone(&self) -> BufferedStream<'a, I> {
        BufferedStream {
            offset: self.offset,
            buffer: self.buffer,
        }
    }
}

pub struct SharedBufferedStream<I>
where
    I: StreamOnce + Positioned,
{
    buffer: UnsafeCell<BufferedStreamInner<I>>,
}

struct BufferedStreamInner<I>
where
    I: StreamOnce + Positioned,
{
    offset: usize,
    iter: I,
    buffer: VecDeque<(I::Item, I::Position)>,
}

impl<I> BufferedStreamInner<I>
where
    I: StreamOnce + Positioned,
    I::Position: Clone,
    I::Item: Clone,
{
    #[inline]
    fn uncons(&mut self, offset: usize) -> Result<I::Item, Error<I::Item, I::Range>> {
        if offset >= self.offset {
            let position = self.iter.position();
            let item = try!(self.iter.uncons());
            self.offset += 1;
            // We want the VecDeque to only keep the last .capacity() elements so we need to remove
            // an element if it gets to large
            if self.buffer.len() == self.buffer.capacity() {
                self.buffer.pop_front();
            }
            self.buffer.push_back((item.clone(), position.clone()));
            Ok(item)
        } else if offset < self.offset - self.buffer.len() {
            // We have backtracked to far
            Err(Error::Message("Backtracked to far".into()))
        } else {
            Ok(
                self.buffer[self.buffer.len() - (self.offset - offset)]
                    .0
                    .clone(),
            )
        }
    }

    #[inline]
    fn position(&self, offset: usize) -> I::Position {
        if offset >= self.offset {
            self.iter.position()
        } else if offset < self.offset - self.buffer.len() {
            self.buffer
                .front()
                .expect("Atleast 1 element in the buffer")
                .1
                .clone()
        } else {
            self.buffer[self.buffer.len() - (self.offset - offset)]
                .1
                .clone()
        }
    }
}

impl<I> SharedBufferedStream<I>
where
    I: StreamOnce + Positioned,
    I::Position: Clone,
    I::Item: Clone,
{
    pub fn as_stream(&self) -> BufferedStream<I> {
        BufferedStream {
            offset: 0,
            buffer: self,
        }
    }
    #[inline]
    fn uncons(&self, offset: usize) -> Result<I::Item, Error<I::Item, I::Range>> {
        unsafe { (*self.buffer.get()).uncons(offset) }
    }
    #[inline(always)]
    fn position(&self, offset: usize) -> I::Position {
        unsafe { (*self.buffer.get()).position(offset) }
    }
}

impl<'a, I> BufferedStream<'a, I>
where
    I: StreamOnce + Positioned,
{
    /// Constructs a new `BufferedStream` froma a `StreamOnce` instance with a `lookahead` number
    /// of elements stored in the buffer.
    ///
    /// `BufferedStream` always implement `Stream` allowing one-shot streams to used as if it could
    /// be used multiple times.
    pub fn new(iter: I, lookahead: usize) -> SharedBufferedStream<I> {
        SharedBufferedStream {
            buffer: UnsafeCell::new(BufferedStreamInner {
                offset: 0,
                iter: iter,
                buffer: VecDeque::with_capacity(lookahead),
            }),
        }
    }
}

impl<'a, I> Positioned for BufferedStream<'a, I>
where
    I: StreamOnce + Positioned,
{
    type Position = I::Position;

    #[inline(always)]
    fn position(&self) -> Self::Position {
        self.buffer.position(self.offset)
    }
}

impl<'a, I> StreamOnce for BufferedStream<'a, I>
where
    I: StreamOnce + Positioned + 'a,
    I::Item: Clone + PartialEq + 'a,
{
    type Item = I::Item;
    type Range = I::Range;

    #[inline]
    fn uncons(&mut self) -> Result<I::Item, Error<I::Item, I::Range>> {
        let value = try!(self.buffer.uncons(self.offset));
        self.offset += 1;
        Ok(value)
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

//! Stream wrapper which provides an informative and easy to use error type.
//!
//! Unless you have specific constraints preventing you from using this error type (such as being
//! a `no_std` environment) you probably want to use this stream type. It can easily be used
//! through the [`Parser::easy_parse`][] method.
//!
//! The provided `Errors` type is roughly the same as `ParseError` in combine 1.x and 2.x.
//!
//! ```
//! #[macro_use]
//! extern crate combine;
//! use combine::{easy, Parser, EasyParser, Stream, many1};
//! use combine::parser::char::letter;
//! use combine::stream::StreamErrorFor;
//! use combine::error::{ParseError, StreamError};
//!
//! fn main() {
//!     parser!{
//!        fn parser[Input]()(Input) -> String
//!         where [
//!             Input: Stream<Item=char, Error = easy::ParseError<Input>>,
//!             Input::Range: PartialEq,
//!             // If we want to use the error type explicitly we need to help rustc infer
//!             // `StreamError` to `easy::Error` (rust-lang/rust#24159)
//!             Input::Error: ParseError<
//!                 Input::Item,
//!                 Input::Range,
//!                 Input::Position,
//!                 StreamError = easy::Error<Input::Item, Input::Range>
//!             >
//!         ]
//!         {
//!             many1(letter()).and_then(|word: String| {
//!                 if word == "combine" {
//!                     Ok(word)
//!                 } else {
//!                     Err(easy::Error::Expected(easy::Info::Borrowed("combine")))
//!                 }
//!             })
//!         }
//!     }
//!
//!     parser!{
//!        fn parser2[Input]()(Input) -> String
//!         where [
//!             Input: Stream<Item=char>,
//!         ]
//!         {
//!             many1(letter()).and_then(|word: String| {
//!                 if word == "combine" {
//!                     Ok(word)
//!                 } else {
//!                     // Alternatively it is possible to only use the methods provided by the
//!                     // `StreamError` trait.
//!                     // In that case the extra bound is not necessary (and this method will work
//!                     // for other errors than `easy::Errors`)
//!                     Err(StreamErrorFor::<Input>::expected_static_message("combine"))
//!                 }
//!             })
//!         }
//!     }
//!
//!     let input = "combin";
//!     let expected_error = Err(easy::Errors {
//!         errors: vec![
//!             easy::Error::Expected("combine".into())
//!         ],
//!         position: 0,
//!     });
//!     assert_eq!(
//!         parser().easy_parse(input).map_err(|err| err.map_position(|p| p.translate_position(input))),
//!         expected_error
//!     );
//!     assert_eq!(
//!         parser2().easy_parse(input).map_err(|err| err.map_position(|p| p.translate_position(input))),
//!         expected_error
//!     );
//! }
//!
//! ```
//!
//! [`Parser::easy_parse`]: ../parser/trait.Parser.html#method.easy_parse
use std::error::Error as StdError;
use std::fmt;

use crate::error::{Info as PrimitiveInfo, ParseResult, StreamError, Tracked};
use crate::stream::{
    FullRangeStream, Positioned, RangeStream, RangeStreamOnce, ResetStream, StreamErrorFor,
    StreamOnce,
};

/// Enum holding error information. Variants are defined for `Stream::Item` and `Stream::Range` as
/// well as string variants holding easy descriptions.
///
/// As there is implementations of `From` for `String` and `&'static str` the
/// constructor need not be used directly as calling `msg.into()` should turn a message into the
/// correct `Info` variant.
#[derive(Clone, Debug)]
pub enum Info<T, R> {
    Token(T),
    Range(R),
    Owned(String),
    Borrowed(&'static str),
}

impl<T, R, F> From<PrimitiveInfo<T, R, F>> for Info<T, R>
where
    F: fmt::Display,
{
    fn from(info: PrimitiveInfo<T, R, F>) -> Self {
        match info {
            PrimitiveInfo::Token(b) => Info::Token(b),
            PrimitiveInfo::Range(b) => Info::Range(b),
            PrimitiveInfo::Borrowed(b) => Info::Borrowed(b),
            PrimitiveInfo::Format(b) => Info::Owned(b.to_string()),
        }
    }
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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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

impl<R> From<u8> for Info<u8, R> {
    fn from(s: u8) -> Info<u8, R> {
        Info::Token(s)
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
    Other(Box<dyn StdError + Send + Sync>),
}

impl<Item, Range> StreamError<Item, Range> for Error<Item, Range>
where
    Item: PartialEq,
    Range: PartialEq,
{
    #[inline]
    fn unexpected_token(token: Item) -> Self {
        Error::Unexpected(Info::Token(token))
    }
    #[inline]
    fn unexpected_range(token: Range) -> Self {
        Error::Unexpected(Info::Range(token))
    }
    #[inline]
    fn unexpected_message<T>(msg: T) -> Self
    where
        T: fmt::Display,
    {
        Error::Unexpected(Info::Owned(msg.to_string()))
    }
    #[inline]
    fn unexpected_static_message(msg: &'static str) -> Self {
        Error::Unexpected(Info::Borrowed(msg))
    }

    #[inline]
    fn expected_token(token: Item) -> Self {
        Error::Expected(Info::Token(token))
    }
    #[inline]
    fn expected_range(token: Range) -> Self {
        Error::Expected(Info::Range(token))
    }
    #[inline]
    fn expected_message<T>(msg: T) -> Self
    where
        T: fmt::Display,
    {
        Error::Expected(Info::Owned(msg.to_string()))
    }
    #[inline]
    fn expected_static_message(msg: &'static str) -> Self {
        Error::Expected(Info::Borrowed(msg))
    }

    #[inline]
    fn message_message<T>(msg: T) -> Self
    where
        T: fmt::Display,
    {
        Error::Message(Info::Owned(msg.to_string()))
    }
    #[inline]
    fn message_static_message(msg: &'static str) -> Self {
        Error::Message(Info::Borrowed(msg))
    }
    #[inline]
    fn message_token(token: Item) -> Self {
        Error::Message(Info::Token(token))
    }
    #[inline]
    fn message_range(token: Range) -> Self {
        Error::Message(Info::Range(token))
    }

    fn is_unexpected_end_of_input(&self) -> bool {
        *self == Self::end_of_input()
    }

    #[inline]
    fn other<E>(err: E) -> Self
    where
        E: StdError + Send + Sync + 'static,
    {
        err.into()
    }

    #[inline]
    fn into_other<T>(self) -> T
    where
        T: StreamError<Item, Range>,
    {
        match self {
            Error::Unexpected(info) => match info {
                Info::Token(x) => T::unexpected_token(x),
                Info::Range(x) => T::unexpected_range(x),
                Info::Borrowed(x) => T::unexpected_static_message(x),
                Info::Owned(x) => T::unexpected_message(x),
            },
            Error::Expected(info) => match info {
                Info::Token(x) => T::expected_token(x),
                Info::Range(x) => T::expected_range(x),
                Info::Borrowed(x) => T::expected_static_message(x),
                Info::Owned(x) => T::expected_message(x),
            },
            Error::Message(info) => match info {
                Info::Token(x) => T::expected_token(x),
                Info::Range(x) => T::expected_range(x),
                Info::Borrowed(x) => T::expected_static_message(x),
                Info::Owned(x) => T::expected_message(x),
            },
            Error::Other(err) => T::message_message(err),
        }
    }
}

impl<Item, Range, Position> crate::error::ParseError<Item, Range, Position> for Error<Item, Range>
where
    Item: PartialEq,
    Range: PartialEq,
    Position: Default,
{
    type StreamError = Self;
    #[inline]
    fn empty(_: Position) -> Self {
        Self::message_static_message("")
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
        *self == Self::end_of_input()
    }

    #[inline]
    fn into_other<T>(self) -> T
    where
        T: crate::error::ParseError<Item, Range, Position>,
    {
        T::from_error(Position::default(), StreamError::into_other(self))
    }
}

impl<Item, Range, Position> crate::error::ParseError<Item, Range, Position>
    for Errors<Item, Range, Position>
where
    Item: PartialEq,
    Range: PartialEq,
    Position: Ord,
{
    type StreamError = Error<Item, Range>;
    #[inline]
    fn empty(pos: Position) -> Self {
        Errors::empty(pos)
    }
    #[inline]
    fn from_error(position: Position, err: Self::StreamError) -> Self {
        Self::new(position, Error::from(err))
    }

    #[inline]
    fn set_position(&mut self, position: Position) {
        self.position = position;
    }

    #[inline]
    fn merge(self, other: Self) -> Self {
        Errors::merge(self, other)
    }

    #[inline]
    fn add(&mut self, err: Self::StreamError) {
        self.add_error(err);
    }

    #[inline]
    fn set_expected<F>(self_: &mut Tracked<Self>, info: Self::StreamError, f: F)
    where
        F: FnOnce(&mut Tracked<Self>),
    {
        let start = self_.error.errors.len();
        f(self_);
        // Replace all expected errors that were added from the previous add_error
        // with this expected error
        let mut i = 0;
        self_.error.errors.retain(|e| {
            if i < start {
                i += 1;
                true
            } else {
                match *e {
                    Error::Expected(_) => false,
                    _ => true,
                }
            }
        });
        self_.error.add(info);
    }

    fn clear_expected(&mut self) {
        self.errors.retain(|e| match *e {
            Error::Expected(_) => false,
            _ => true,
        })
    }

    fn is_unexpected_end_of_input(&self) -> bool {
        self.errors
            .iter()
            .any(StreamError::is_unexpected_end_of_input)
    }

    #[inline]
    fn into_other<T>(mut self) -> T
    where
        T: crate::error::ParseError<Item, Range, Position>,
    {
        match self.errors.pop() {
            Some(err) => T::from_error(self.position, StreamError::into_other(err)),
            None => T::empty(self.position),
        }
    }
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
            (&Error::Unexpected(ref l), &Error::Unexpected(ref r))
            | (&Error::Expected(ref l), &Error::Expected(ref r))
            | (&Error::Message(ref l), &Error::Message(ref r)) => l == r,
            _ => false,
        }
    }
}

impl<T, R, E> From<E> for Error<T, R>
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
    /// # use combine::parser::char::*;
    /// # use combine::stream::state::{State, SourcePosition};
    ///
    /// # fn main() {
    /// let input = r"
    ///   ,123
    /// ";
    /// let result = spaces().silent().with(char('.').or(char('a')).or(digit()))
    ///     .easy_parse(State::new(input));
    /// let m = format!("{}", result.unwrap_err());
    /// let expected = r"Parse error at line: 2, column: 3
    /// Unexpected `,`
    /// Expected `.`, `a` or `digit`
    /// ";
    /// assert_eq!(m, expected);
    /// # }
    /// ```
    pub fn fmt_errors(errors: &[Error<T, R>], f: &mut fmt::Formatter<'_>) -> fmt::Result
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
            writeln!(f, "{}", error)?;
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
            write!(f, "{} `{}`", s, message)?;
        }
        if expected_count != 0 {
            writeln!(f, "")?;
        }
        // If there are any generic messages we print them out last
        let messages = errors.iter().filter(|e| match **e {
            Error::Message(_) | Error::Other(_) => true,
            _ => false,
        });
        for error in messages {
            writeln!(f, "{}", error)?;
        }
        Ok(())
    }
}

/// Convenience alias over `Errors` for `StreamOnce` types which makes it possible to specify the
/// `Errors` type from a `StreamOnce` by writing `ParseError<Input>` instead of `Errors<Input::Item,
/// Input::Range, Input::Position>`
pub type ParseError<S> =
    Errors<<S as StreamOnce>::Item, <S as StreamOnce>::Range, <S as StreamOnce>::Position>;

/// Struct which hold information about an error that occurred at a specific position.
/// Can hold multiple instances of `Error` if more that one error occurred in the same position.
#[derive(Debug, PartialEq)]
pub struct Errors<Input, R, P> {
    /// The position where the error occurred
    pub position: P,
    /// A vector containing specific information on what errors occurred at `position`. Usually
    /// a fully formed message contains one `Unexpected` error and one or more `Expected` errors.
    /// `Message` and `Other` may also appear (`combine` never generates these errors on its own)
    /// and may warrant custom handling.
    pub errors: Vec<Error<Input, R>>,
}

impl<Input, R, P> Errors<Input, R, P> {
    /// Constructs a new `ParseError` which occurred at `position`.
    #[inline]
    pub fn new(position: P, error: Error<Input, R>) -> Errors<Input, R, P> {
        Self::from_errors(position, vec![error])
    }

    /// Constructs an error with no other information than the position it occurred at.
    #[inline]
    pub fn empty(position: P) -> Errors<Input, R, P> {
        Self::from_errors(position, vec![])
    }

    /// Constructs a `ParseError` with multiple causes.
    #[inline]
    pub fn from_errors(position: P, errors: Vec<Error<Input, R>>) -> Errors<Input, R, P> {
        Errors {
            position: position,
            errors: errors,
        }
    }

    /// Constructs an end of input error. Should be returned by parsers which encounter end of
    /// input unexpectedly.
    #[inline]
    pub fn end_of_input(position: P) -> Errors<Input, R, P> {
        Self::new(position, Error::end_of_input())
    }

    /// Adds an error if `error` does not exist in this `ParseError` already (as determined byte
    /// `PartialEq`).
    pub fn add_error(&mut self, error: Error<Input, R>)
    where
        Input: PartialEq,
        R: PartialEq,
    {
        // Don't add duplicate errors
        if self.errors.iter().all(|err| *err != error) {
            self.errors.push(error);
        }
    }

    /// Removes all `Expected` errors in `self` and adds `info` instead.
    pub fn set_expected(&mut self, info: Info<Input, R>) {
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
    pub fn merge(mut self, mut other: Errors<Input, R, P>) -> Errors<Input, R, P>
    where
        P: Ord,
        Input: PartialEq,
        R: PartialEq,
    {
        use std::cmp::Ordering;
        // Only keep the errors which occurred after consuming the most amount of data
        match self.position.cmp(&other.position) {
            Ordering::Less => other,
            Ordering::Greater => self,
            Ordering::Equal => {
                for message in other.errors.drain(..) {
                    self.add_error(message);
                }
                self
            }
        }
    }

    /// Maps the position to a new value
    pub fn map_position<F, Q>(self, f: F) -> Errors<Input, R, Q>
    where
        F: FnOnce(P) -> Q,
    {
        Errors::from_errors(f(self.position), self.errors)
    }

    /// Maps all token variants to a new value
    pub fn map_token<F, U>(self, mut f: F) -> Errors<U, R, P>
    where
        F: FnMut(Input) -> U,
    {
        Errors::from_errors(
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
    /// use combine::*;
    /// use combine::parser::range::range;
    /// println!(
    ///     "{}",
    ///     range(&"HTTP"[..])
    ///         .easy_parse("HTT")
    ///         .unwrap_err()
    ///         .map_range(|bytes| format!("{:?}", bytes))
    /// );
    /// ```
    pub fn map_range<F, S>(self, mut f: F) -> Errors<Input, S, P>
    where
        F: FnMut(R) -> S,
    {
        Errors::from_errors(
            self.position,
            self.errors
                .into_iter()
                .map(|error| error.map_range(&mut f))
                .collect(),
        )
    }
}

impl<Input, R, P> StdError for Errors<Input, R, P>
where
    P: fmt::Display + fmt::Debug,
    Input: fmt::Display + fmt::Debug,
    R: fmt::Display + fmt::Debug,
{
    fn description(&self) -> &str {
        "parse error"
    }
}

impl<Input, R, P> fmt::Display for Errors<Input, R, P>
where
    P: fmt::Display,
    Input: fmt::Display,
    R: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Parse error at {}", self.position)?;
        Error::fmt_errors(&self.errors, f)
    }
}

impl<T: fmt::Display, R: fmt::Display> fmt::Display for Error<T, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Error::Unexpected(ref c) => write!(f, "Unexpected `{}`", c),
            Error::Expected(ref s) => write!(f, "Expected `{}`", s),
            Error::Message(ref msg) => msg.fmt(f),
            Error::Other(ref err) => err.fmt(f),
        }
    }
}

#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub struct Stream<S>(pub S);

impl<S> From<S> for Stream<S> {
    fn from(stream: S) -> Self {
        Stream(stream)
    }
}

impl<S> ResetStream for Stream<S>
where
    S: ResetStream + Positioned,
    S::Item: PartialEq,
    S::Range: PartialEq,
{
    type Checkpoint = S::Checkpoint;

    fn checkpoint(&self) -> Self::Checkpoint {
        self.0.checkpoint()
    }
    fn reset(&mut self, checkpoint: Self::Checkpoint) -> Result<(), Self::Error> {
        self.0
            .reset(checkpoint)
            .map_err(crate::error::ParseError::into_other)
    }
}

impl<S> StreamOnce for Stream<S>
where
    S: StreamOnce + Positioned,
    S::Item: PartialEq,
    S::Range: PartialEq,
{
    type Item = S::Item;
    type Range = S::Range;
    type Position = S::Position;
    type Error = ParseError<S>;

    #[inline]
    fn uncons(&mut self) -> Result<Self::Item, StreamErrorFor<Self>> {
        self.0.uncons().map_err(StreamError::into_other)
    }

    fn is_partial(&self) -> bool {
        self.0.is_partial()
    }
}

impl<S> RangeStreamOnce for Stream<S>
where
    S: RangeStream,
    S::Item: PartialEq,
    S::Range: PartialEq,
{
    #[inline]
    fn uncons_range(&mut self, size: usize) -> Result<Self::Range, StreamErrorFor<Self>> {
        self.0.uncons_range(size).map_err(StreamError::into_other)
    }

    #[inline]
    fn uncons_while<F>(&mut self, f: F) -> Result<Self::Range, StreamErrorFor<Self>>
    where
        F: FnMut(Self::Item) -> bool,
    {
        self.0.uncons_while(f).map_err(StreamError::into_other)
    }

    #[inline]
    fn uncons_while1<F>(&mut self, f: F) -> ParseResult<Self::Range, StreamErrorFor<Self>>
    where
        F: FnMut(Self::Item) -> bool,
    {
        self.0.uncons_while1(f).map_err(StreamError::into_other)
    }

    #[inline]
    fn distance(&self, end: &Self::Checkpoint) -> usize {
        self.0.distance(end)
    }
}

impl<S> Positioned for Stream<S>
where
    S: StreamOnce + Positioned,
    S::Item: PartialEq,
    S::Range: PartialEq,
{
    fn position(&self) -> S::Position {
        self.0.position()
    }
}

impl<S> FullRangeStream for Stream<S>
where
    S: FullRangeStream,
    S::Item: PartialEq,
    S::Range: PartialEq,
{
    fn range(&self) -> Self::Range {
        self.0.range()
    }
}

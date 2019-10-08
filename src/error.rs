use crate::lib::fmt;

#[cfg(feature = "std")]
use std::error::Error as StdError;

use self::ParseResult::*;

use crate::ErrorOffset;

use crate::stream::StreamOnce;

pub(crate) trait ResultExt<E, T> {
    fn consumed(self) -> ParseResult<E, T>;
}

impl<E, T> ResultExt<E, T> for Result<E, T> {
    fn consumed(self) -> ParseResult<E, T> {
        match self {
            Ok(x) => ConsumedOk(x),
            Err(x) => ConsumedErr(x),
        }
    }
}

#[macro_export]
#[doc(hidden)]
macro_rules! ctry {
    ($result:expr) => {
        match $result {
            $crate::error::ParseResult::ConsumedOk(x) => (x, $crate::error::Consumed::Consumed(())),
            $crate::error::ParseResult::EmptyOk(x) => (x, $crate::error::Consumed::Empty(())),
            $crate::error::ParseResult::ConsumedErr(err) => {
                return $crate::error::ParseResult::ConsumedErr(err.into())
            }
            $crate::error::ParseResult::EmptyErr(err) => {
                return $crate::error::ParseResult::EmptyErr(err.into())
            }
        }
    };
}

/// Trait for types which can be used to construct error information.
///
/// To call functions expecting this trait, use the wrappar types defined in this module
/// `Token`, `Range`, `Format` or `Static`/`&'static str`
pub trait ErrorInfo<'s, T, R> {
    type Format: fmt::Display;
    fn into_info(&'s self) -> Info<T, R, Self::Format>;
}

impl<'s, 'a, T, R, F> ErrorInfo<'s, T, R> for &'a F
where
    F: ErrorInfo<'s, T, R>,
{
    type Format = F::Format;
    fn into_info(&'s self) -> Info<T, R, Self::Format> {
        (**self).into_info()
    }
}

#[derive(Clone, Debug)]
pub enum Info<T, R, F = &'static str> {
    Token(T),
    Range(R),
    Static(&'static str),
    Format(F),
}

impl<'s, T, R, F> ErrorInfo<'s, T, R> for Info<T, R, F>
where
    T: Clone,
    R: Clone,
    F: fmt::Display + 's,
{
    type Format = &'s F;
    fn into_info(&'s self) -> Info<T, R, <Self as ErrorInfo<T, R>>::Format> {
        match self {
            Info::Token(b) => Info::Token(b.clone()),
            Info::Range(b) => Info::Range(b.clone()),
            Info::Static(b) => Info::Static(*b),
            Info::Format(b) => Info::Format(b),
        }
    }
}

impl<R, F> From<char> for Info<char, R, F> {
    fn from(s: char) -> Self {
        Info::Token(s)
    }
}

impl<'s, R> ErrorInfo<'s, char, R> for char {
    type Format = &'static str;
    fn into_info(&self) -> Info<char, R, Self::Format> {
        Info::Token(*self)
    }
}

impl<T, R, F> From<&'static str> for Info<T, R, F> {
    fn from(s: &'static str) -> Self {
        Info::Static(s)
    }
}

impl<'s, T, R> ErrorInfo<'s, T, R> for &'static str {
    type Format = &'static str;
    fn into_info(&self) -> Info<T, R, Self::Format> {
        Info::Static(*self)
    }
}

impl<R, F> From<u8> for Info<u8, R, F> {
    fn from(s: u8) -> Self {
        Info::Token(s)
    }
}

impl<R> ErrorInfo<'_, Self, R> for u8 {
    type Format = &'static str;
    fn into_info(&self) -> Info<Self, R, Self::Format> {
        Info::Token(*self)
    }
}

/// Newtype which constructs an `Info::Token` through `ErrorInfo`
pub struct Token<T>(pub T);

impl<T, R> From<Token<T>> for Info<T, R, &'static str> {
    fn from(s: Token<T>) -> Self {
        Info::Token(s.0)
    }
}

impl<'s, T, R> ErrorInfo<'s, T, R> for Token<T>
where
    T: Clone,
{
    type Format = &'static str;
    fn into_info(&'s self) -> Info<T, R, Self::Format> {
        Info::Token(self.0.clone())
    }
}

/// Newtype which constructs an `Info::Range` through `ErrorInfo`
pub struct Range<R>(pub R);

impl<T, R> From<Range<R>> for Info<T, R, &'static str> {
    fn from(s: Range<R>) -> Self {
        Info::Range(s.0)
    }
}

impl<'s, T, R> ErrorInfo<'s, T, R> for Range<R>
where
    R: Clone,
{
    type Format = &'static str;
    fn into_info(&'s self) -> Info<T, R, Self::Format> {
        Info::Range(self.0.clone())
    }
}

/// Newtype which constructs an `Info::Static` through `ErrorInfo`
/// A plain `&'static str` can also be used, this exists for consistency.
pub struct Static(&'static str);

impl<T, R, F> From<Static> for Info<T, R, F>
where
    F: fmt::Display,
{
    fn from(s: Static) -> Self {
        Info::Static(s.0)
    }
}

impl<'s, T, R> ErrorInfo<'s, T, R> for Static {
    type Format = &'static str;
    fn into_info(&'s self) -> Info<T, R, Self::Format> {
        Info::Static(self.0)
    }
}

/// Newtype which constructs an `Info::Format` through `ErrorInfo`
pub struct Format<F>(pub F)
where
    F: fmt::Display;

impl<T, R, F> From<Format<F>> for Info<T, R, F>
where
    F: fmt::Display,
{
    fn from(s: Format<F>) -> Self {
        Info::Format(s.0)
    }
}

impl<'s, T, R, F> ErrorInfo<'s, T, R> for Format<F>
where
    F: fmt::Display + 's,
{
    type Format = &'s F;
    fn into_info(&'s self) -> Info<T, R, Self::Format> {
        Info::Format(&self.0)
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
    /// fn char<Input>(input: &mut Input) -> StdParseResult<char, Input>
    ///     where Input: Stream<Token = char>,
    ///           Input::Error: ParseError<Input::Token, Input::Range, Input::Position>,
    /// {
    ///     let (c, consumed) = satisfy(|c| c != '"').parse_stream(input).into_result()?;
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
    ///                 .into_result()
    ///             }),
    ///         _ => Ok((c, consumed))
    ///     }
    /// }
    /// let result = many(parser(char))
    ///     .easy_parse(r#"abc\"\\"#);
    /// assert_eq!(result, Ok((r#"abc"\"#.to_string(), "")));
    /// }
    /// ```
    pub fn combine<F, U, E>(self, f: F) -> StdParseResult2<U, E>
    where
        F: FnOnce(T) -> StdParseResult2<U, E>,
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
    pub fn combine_consumed<F, U, E>(self, f: F) -> ParseResult<U, E>
    where
        F: FnOnce(T) -> ParseResult<U, E>,
    {
        use self::ParseResult::*;
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

/// A type alias over the specific `Result` type used by parsers to indicate whether they were
/// successful or not.
/// `O` is the type that is output on success.
/// `Input` is the specific stream type used in the parser.
pub type StdParseResult<O, Input> =
    Result<(O, Consumed<()>), Consumed<Tracked<<Input as StreamOnce>::Error>>>;
pub type StdParseResult2<O, E> = Result<(O, Consumed<()>), Consumed<Tracked<E>>>;

/// `StreamError` represents a single error returned from a `Stream` or a `Parser`.
///
/// Usually multiple instances of `StreamError` is composed into a `ParseError` to build the final
/// error value.
pub trait StreamError<Item, Range>: Sized {
    fn unexpected_token(token: Item) -> Self;
    fn unexpected_range(token: Range) -> Self;
    fn unexpected_format<T>(msg: T) -> Self
    where
        T: fmt::Display;
    fn unexpected<E>(info: E) -> Self
    where
        E: for<'s> ErrorInfo<'s, Item, Range>,
    {
        match info.into_info() {
            Info::Token(b) => Self::unexpected_token(b),
            Info::Range(b) => Self::unexpected_range(b),
            Info::Static(b) => Self::unexpected_static_message(b),
            Info::Format(b) => Self::unexpected_format(b),
        }
    }
    fn unexpected_static_message(msg: &'static str) -> Self {
        Self::unexpected_format(msg)
    }

    fn expected_token(token: Item) -> Self;
    fn expected_range(token: Range) -> Self;
    fn expected_format<T>(msg: T) -> Self
    where
        T: fmt::Display;
    fn expected<E>(info: E) -> Self
    where
        E: for<'s> ErrorInfo<'s, Item, Range>,
    {
        match info.into_info() {
            Info::Token(b) => Self::expected_token(b),
            Info::Range(b) => Self::expected_range(b),
            Info::Static(b) => Self::expected_static_message(b),
            Info::Format(b) => Self::expected_format(b),
        }
    }
    fn expected_static_message(msg: &'static str) -> Self {
        Self::expected_format(msg)
    }

    fn message_token(token: Item) -> Self;
    fn message_range(token: Range) -> Self;
    fn message_format<T>(msg: T) -> Self
    where
        T: fmt::Display;
    fn message_static_message(msg: &'static str) -> Self {
        Self::message_format(msg)
    }
    fn message<E>(info: E) -> Self
    where
        E: for<'s> ErrorInfo<'s, Item, Range>,
    {
        match info.into_info() {
            Info::Token(b) => Self::message_token(b),
            Info::Range(b) => Self::message_range(b),
            Info::Static(b) => Self::message_static_message(b),
            Info::Format(b) => Self::message_format(b),
        }
    }

    #[cfg(feature = "std")]
    fn other<E>(err: E) -> Self
    where
        E: StdError + Send + Sync + 'static,
    {
        Self::message_format(err)
    }

    fn end_of_input() -> Self {
        Self::unexpected_static_message("end of input")
    }

    fn is_unexpected_end_of_input(&self) -> bool;

    /// Converts `self` into a different `StreamError` type.
    ///
    /// This should aim to preserve as much information as possible into the returned `T` value but
    /// if `Self` ignores some information passed to it using one of the constructors that
    /// information is naturally lost.
    fn into_other<T>(self) -> T
    where
        T: StreamError<Item, Range>;
}

/// Trait which defines a combine parse error.
///
/// A parse error is composed of zero or more `StreamError` instances which gets added to it as
/// errors are encountered during parsing.
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

    fn add_expected<E>(&mut self, info: E)
    where
        E: for<'s> ErrorInfo<'s, Item, Range>,
    {
        self.add(Self::StreamError::expected(info))
    }

    fn add_unexpected<E>(&mut self, info: E)
    where
        E: for<'s> ErrorInfo<'s, Item, Range>,
    {
        self.add(Self::StreamError::unexpected(info))
    }

    fn add_message<E>(&mut self, info: E)
    where
        E: for<'s> ErrorInfo<'s, Item, Range>,
    {
        self.add(Self::StreamError::message(info))
    }

    /// Sets `info` as the *only* `Expected` error of `self`
    fn set_expected<F>(self_: &mut Tracked<Self>, info: Self::StreamError, f: F)
    where
        F: FnOnce(&mut Tracked<Self>);

    /// Removes any expected errors currently in `self`
    fn clear_expected(&mut self) {}

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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
    fn unexpected_format<T>(_: T) -> Self
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
    fn expected_format<T>(_: T) -> Self
    where
        T: fmt::Display,
    {
        UnexpectedParse::Unexpected
    }
    #[inline]
    fn message_format<T>(_: T) -> Self
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
    fn is_unexpected_end_of_input(&self) -> bool {
        *self == UnexpectedParse::Eoi
    }

    #[inline]
    fn into_other<T>(self) -> T
    where
        T: StreamError<Item, Range>,
    {
        match self {
            UnexpectedParse::Unexpected => T::unexpected_static_message("parse"),
            UnexpectedParse::Eoi => T::end_of_input(),
        }
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
        *self = match (*self, err) {
            (UnexpectedParse::Eoi, _) => UnexpectedParse::Eoi,
            (_, err) => err,
        };
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

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum StringStreamError {
    UnexpectedParse,
    Eoi,
    CharacterBoundary,
}

pub(crate) const CHAR_BOUNDARY_ERROR_MESSAGE: &str = "unexpected slice on character boundary";

impl fmt::Display for StringStreamError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
    fn unexpected_format<T>(_msg: T) -> Self
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
    fn expected_format<T>(_: T) -> Self
    where
        T: fmt::Display,
    {
        StringStreamError::UnexpectedParse
    }
    #[inline]
    fn message_format<T>(_: T) -> Self
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
    fn is_unexpected_end_of_input(&self) -> bool {
        *self == StringStreamError::Eoi
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
        *self = match (*self, err) {
            (StringStreamError::Eoi, _) => StringStreamError::Eoi,
            (_, err) => err,
        };
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

/// A `Result` type which has the consumed status flattened into the result.
/// Conversions to and from `std::result::Result` can be done using `result.into()` or
/// `From::from(result)`
#[derive(Clone, PartialEq, Debug, Copy)]
pub enum ParseResult<T, E> {
    ConsumedOk(T),
    EmptyOk(T),
    ConsumedErr(E),
    EmptyErr(Tracked<E>),
}

impl<T, E> ParseResult<T, E> {
    #[inline]
    pub fn is_ok(&self) -> bool {
        match *self {
            ConsumedOk(_) | EmptyOk(_) => true,
            ConsumedErr(_) | EmptyErr(_) => false,
        }
    }

    #[inline]
    pub fn is_err(&self) -> bool {
        !self.is_ok()
    }

    pub fn as_ref(&self) -> ParseResult<&T, &E> {
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
        F: FnOnce(T) -> ParseResult<T2, E>,
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

    pub fn map_err<F, E2>(self, f: F) -> ParseResult<T, F::Output>
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

    pub fn map<F, T2>(self, f: F) -> ParseResult<F::Output, E>
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

impl<O, E> ParseResult<O, E> {
    pub fn into_result(self) -> StdParseResult2<O, E> {
        self.into()
    }
}

impl<T, E> Into<Result<Consumed<T>, Consumed<Tracked<E>>>> for ParseResult<T, E> {
    #[inline]
    fn into(self) -> Result<Consumed<T>, Consumed<Tracked<E>>> {
        match self {
            ConsumedOk(t) => Ok(Consumed::Consumed(t)),
            EmptyOk(t) => Ok(Consumed::Empty(t)),
            ConsumedErr(e) => Err(Consumed::Consumed(e.into())),
            EmptyErr(e) => Err(Consumed::Empty(e)),
        }
    }
}

impl<O, E> Into<StdParseResult2<O, E>> for ParseResult<O, E> {
    #[inline]
    fn into(self) -> StdParseResult2<O, E> {
        use self::ParseResult::*;
        match self {
            ConsumedOk(t) => Ok((t, Consumed::Consumed(()))),
            EmptyOk(t) => Ok((t, Consumed::Empty(()))),
            ConsumedErr(e) => Err(Consumed::Consumed(e.into())),
            EmptyErr(e) => Err(Consumed::Empty(e)),
        }
    }
}

impl<O, E> From<StdParseResult2<O, E>> for ParseResult<O, E> {
    #[inline]
    fn from(result: StdParseResult2<O, E>) -> ParseResult<O, E> {
        use self::ParseResult::*;
        match result {
            Ok((t, Consumed::Consumed(()))) => ConsumedOk(t),
            Ok((t, Consumed::Empty(()))) => EmptyOk(t),
            Err(Consumed::Consumed(e)) => ConsumedErr(e.error),
            Err(Consumed::Empty(e)) => EmptyErr(e),
        }
    }
}

#[cfg(all(feature = "std", test))]
mod tests_std {
    use crate::Parser;

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
        let result =
            crate::parser::range::take_while(|c: CloneOnly| c.s == "x".to_string()).parse(input);
        assert_eq!(
            result,
            Ok((
                &[CloneOnly { s: "x".to_string() }][..],
                &[CloneOnly { s: "y".to_string() }][..]
            ))
        );
    }
}

use std::any::Any;
use std::error::Error as StdError;
use std::fmt;

use primitives::{Info as PrimitiveInfo, ParseError, StreamError, Tracked};
use stream::{FullRangeStream, Positioned, RangeStream, RangeStreamOnce, Resetable, StreamOnce};

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

impl<T, R> From<PrimitiveInfo<T, R>> for Info<T, R> {
    fn from(info: PrimitiveInfo<T, R>) -> Self {
        match info {
            PrimitiveInfo::Token(b) => Info::Token(b),
            PrimitiveInfo::Range(b) => Info::Range(b),
            PrimitiveInfo::Borrowed(b) => Info::Borrowed(b),
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
    Other(Box<StdError + Send + Sync>),
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

impl<Item, Range, Position> ParseError<Item, Range, Position> for Error<Item, Range>
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
        T: ParseError<Item, Range, Position>,
    {
        T::from_error(Position::default(), StreamError::into_other(self))
    }
}

impl<Item, Range, Position> ParseError<Item, Range, Position> for Errors<Position, Item, Range>
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

    fn is_unexpected_end_of_input(&self) -> bool {
        self.errors.iter().any(|err| *err == Error::end_of_input())
    }

    #[inline]
    fn into_other<T>(mut self) -> T
    where
        T: ParseError<Item, Range, Position>,
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
    /// # use combine::parser::char::*;
    ///
    /// # fn main() {
    /// let input = r"
    ///   ,123
    /// ";
    /// let result = spaces().with(char('.').or(char('a')).or(digit()))
    ///     .easy_parse(State::new(input));
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

/// Alias over `ParseError` for `StreamOnce` types
pub type StreamErrors<S> =
    Errors<<S as StreamOnce>::Position, <S as StreamOnce>::Item, <S as StreamOnce>::Range>;

/// Struct which hold information about an error that occured at a specific position.
/// Can hold multiple instances of `Error` if more that one error occured in the same position.
#[derive(Debug, PartialEq)]
pub struct Errors<P, I, R> {
    /// The position where the error occurred
    pub position: P,
    /// A vector containing specific information on what errors occurred at `position`. Usually
    /// a fully formed message contains one `Unexpected` error and one or more `Expected` errors.
    /// `Message` and `Other` may also appear (`combine` never generates these errors on its own)
    /// and may warrant custom handling.
    pub errors: Vec<Error<I, R>>,
}

impl<P, I, R> Errors<P, I, R> {
    /// Constructs a new `ParseError` which occurred at `position`.
    #[inline]
    pub fn new(position: P, error: Error<I, R>) -> Errors<P, I, R> {
        Self::from_errors(position, vec![error])
    }

    /// Constructs an error with no other information than the position it occurred at.
    #[inline]
    pub fn empty(position: P) -> Errors<P, I, R> {
        Self::from_errors(position, vec![])
    }

    /// Constructs a `ParseError` with multiple causes.
    #[inline]
    pub fn from_errors(position: P, errors: Vec<Error<I, R>>) -> Errors<P, I, R> {
        Errors {
            position: position,
            errors: errors,
        }
    }

    /// Constructs an end of input error. Should be returned by parsers which encounter end of
    /// input unexpectedly.
    #[inline]
    pub fn end_of_input(position: P) -> Errors<P, I, R> {
        Self::new(position, Error::end_of_input())
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
    pub fn merge(mut self, mut other: Errors<P, I, R>) -> Errors<P, I, R>
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
                for message in other.errors.drain(..) {
                    self.add_error(message);
                }
                self
            }
        }
    }

    /// Maps the position to a new value
    pub fn map_position<F, Q>(self, f: F) -> Errors<Q, I, R>
    where
        F: FnOnce(P) -> Q,
    {
        Errors::from_errors(f(self.position), self.errors)
    }

    /// Maps all token variants to a new value
    pub fn map_token<F, U>(self, mut f: F) -> Errors<P, U, R>
    where
        F: FnMut(I) -> U,
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
    /// use combine::Parser;
    /// use combine::parser::range::range;
    /// println!(
    ///     "{}",
    ///     range(&"HTTP"[..])
    ///         .easy_parse("HTT")
    ///         .unwrap_err()
    ///         .map_range(|bytes| format!("{:?}", bytes))
    /// );
    /// ```
    pub fn map_range<F, S>(self, mut f: F) -> Errors<P, I, S>
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

impl<P, I, R> StdError for Errors<P, I, R>
where
    P: fmt::Display + fmt::Debug + Any,
    I: fmt::Display + fmt::Debug + Any,
    R: fmt::Display + fmt::Debug + Any,
{
    fn description(&self) -> &str {
        "parse error"
    }
}

impl<P, I, R> fmt::Display for Errors<P, I, R>
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

#[derive(Copy, Clone, Debug)]
pub struct Stream<S>(pub S);

impl<S> Resetable for Stream<S>
where
    S: Resetable,
{
    type Checkpoint = S::Checkpoint;

    fn checkpoint(&self) -> Self::Checkpoint {
        self.0.checkpoint()
    }
    fn reset(&mut self, checkpoint: Self::Checkpoint) {
        self.0.reset(checkpoint);
    }
}

impl<S> StreamOnce for Stream<S>
where
    S: StreamOnce + Positioned,
{
    type Item = S::Item;
    type Range = S::Range;
    type Position = S::Position;
    type Error = StreamErrors<S>;

    #[inline]
    fn uncons<E>(&mut self) -> Result<Self::Item, E>
    where
        E: StreamError<Self::Item, Self::Range>,
    {
        self.0.uncons()
    }

    fn is_partial(&self) -> bool {
        self.0.is_partial()
    }
}

impl<S> RangeStreamOnce for Stream<S>
where
    S: RangeStream,
{
    #[inline]
    fn uncons_range<E>(&mut self, size: usize) -> Result<Self::Range, E>
    where
        E: StreamError<Self::Item, Self::Range>,
    {
        self.0.uncons_range(size)
    }

    #[inline]
    fn uncons_while<E, F>(&mut self, f: F) -> Result<Self::Range, E>
    where
        F: FnMut(Self::Item) -> bool,
        E: StreamError<Self::Item, Self::Range>,
    {
        self.0.uncons_while(f)
    }

    #[inline]
    fn distance(&self, end: &Self::Checkpoint) -> usize {
        self.0.distance(end)
    }
}

impl<S> Positioned for Stream<S>
where
    S: StreamOnce + Positioned,
{
    fn position(&self) -> S::Position {
        self.0.position()
    }
}

impl<S> FullRangeStream for Stream<S>
where
    S: FullRangeStream,
{
    fn range(&self) -> Self::Range {
        self.0.range()
    }
}

use std::fmt;
use std::error::Error as StdError;
use std::any::Any;
use std::cell::UnsafeCell;
use std::collections::VecDeque;

use self::FastResult::*;

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

/// Struct which represents a position in a source file
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct SourcePosition {
    /// Current line of the input
    pub line: i32,
    /// Current column of the input
    pub column: i32,
}

/// Struct which represents a position in a byte stream
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

/// Enum holding error information
/// As there is implementations of `From` for `T: Positioner`, `String` and `&'static str` the
/// constructor need not be used directly as calling `msg.into()` should turn a message into the
/// correct `Info` variant
#[derive(Clone, Debug)]
pub enum Info<T, R> {
    Token(T),
    Range(R),
    Owned(String),
    Borrowed(&'static str),
}

impl<T: PartialEq, R: PartialEq> PartialEq for Info<T, R> {
    fn eq(&self, other: &Info<T, R>) -> bool {
        match (self, other) {
            (&Info::Token(ref l), &Info::Token(ref r)) => l == r,
            (&Info::Range(ref l), &Info::Range(ref r)) => l == r,
            (&Info::Owned(ref l), &Info::Owned(ref r)) => l == r,
            (&Info::Borrowed(ref l), &Info::Owned(ref r)) => l == r,
            (&Info::Owned(ref l), &Info::Borrowed(ref r)) => l == r,
            (&Info::Borrowed(ref l), &Info::Borrowed(ref r)) => l == r,
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

/// Enum used to store information about an error that has occured
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

impl<T: PartialEq, R: PartialEq> PartialEq for Error<T, R> {
    fn eq(&self, other: &Error<T, R>) -> bool {
        match (self, other) {
            (&Error::Unexpected(ref l), &Error::Unexpected(ref r)) => l == r,
            (&Error::Expected(ref l), &Error::Expected(ref r)) => l == r,
            (&Error::Message(ref l), &Error::Message(ref r)) => l == r,
            _ => false,
        }
    }
}

impl<E, T, R> From<E> for Error<T, R>
    where E: StdError + 'static + Send + Sync
{
    fn from(e: E) -> Error<T, R> {
        Error::Other(Box::new(e))
    }
}

impl<T, R> Error<T, R> {
    pub fn end_of_input() -> Error<T, R> {
        Error::Unexpected("end of input".into())
    }
}

/// Enum used to indicate if a parser consumed any items of the stream it was given as an input
#[derive(Clone, PartialEq, Debug, Copy)]
pub enum Consumed<T> {
    /// Constructor indicating that the parser has consumed elements
    Consumed(T),
    /// Constructor indicating that the parser did not consume any elements
    Empty(T),
}

impl<T> Consumed<T> {
    pub fn as_mut(&mut self) -> &mut T {
        match *self {
            Consumed::Empty(ref mut t) => t,
            Consumed::Consumed(ref mut t) => t,
        }
    }
    pub fn as_ref(&self) -> &T {
        match *self {
            Consumed::Empty(ref t) => t,
            Consumed::Consumed(ref t) => t,
        }
    }
    /// Returns true if `self` is empty
    pub fn is_empty(&self) -> bool {
        match *self {
            Consumed::Empty(_) => true,
            Consumed::Consumed(_) => false,
        }
    }

    /// Extracts the contained value
    pub fn into_inner(self) -> T {
        match self {
            Consumed::Empty(x) => x,
            Consumed::Consumed(x) => x,
        }
    }

    /// Converts `self` into the Consumed state
    pub fn as_consumed(self) -> Consumed<T> {
        Consumed::Consumed(self.into_inner())
    }

    /// Converts `self` into theEmpty state
    pub fn as_empty(self) -> Consumed<T> {
        Consumed::Empty(self.into_inner())
    }

    /// Maps over the contained value without changing the consumed state
    pub fn map<F, U>(self, f: F) -> Consumed<U>
        where F: FnOnce(T) -> U
    {
        match self {
            Consumed::Empty(x) => Consumed::Empty(f(x)),
            Consumed::Consumed(x) => Consumed::Consumed(f(x)),
        }
    }

    pub fn merge(&self, current: Consumed<T>) -> Consumed<T> {
        match *self {
            Consumed::Empty(_) => current,
            Consumed::Consumed(_) => current.as_consumed(),
        }
    }

    /// Combines the Consumed flags from `self` and the result of `f`
    ///
    /// ```
    /// # extern crate combine as pc;
    /// # use pc::*;
    /// # fn main() {
    /// //Parses a character of string literal and handles the escaped characters \\ and \" as \
    /// //and " respectively
    /// fn char(input: &str) -> ParseResult<char, &str> {
    ///     let (c, input) = try!(satisfy(|c| c != '"').parse_state(input));
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
    ///                 .parse_state(input)
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
        where F: FnOnce(T) -> ParseResult<U, I>,
              I: StreamOnce
    {
        match self {
            Consumed::Consumed(x) => {
                match f(x) {
                    Ok((v, Consumed::Empty(rest))) => Ok((v, Consumed::Consumed(rest))),
                    Err(Consumed::Empty(err)) => Err(Consumed::Consumed(err)),
                    y => y,
                }
            }
            Consumed::Empty(x) => f(x),
        }
    }
    pub fn combine_fast<F, U, I>(self, f: F) -> ConsumedResult<U, I>
        where F: FnOnce(T) -> ConsumedResult<U, I>,
              I: StreamOnce
    {
        use self::FastResult::*;
        match self {
            Consumed::Consumed(x) => {
                match f(x) {
                    EmptyOk((v, rest)) => ConsumedOk((v, rest)),
                    EmptyErr(err) => ConsumedErr(err),
                    y => y,
                }
            }
            Consumed::Empty(x) => f(x),
        }
    }
}
/// Struct which hold information about an error that occured at a specific position.
/// Can hold multiple instances of `Error` if more that one error occured in the same position.
pub struct ParseError<S: StreamOnce> {
    /// The position where the error occured
    pub position: S::Position,
    /// A vector containing specific information on what errors occured at `position`
    pub errors: Vec<Error<S::Item, S::Range>>,
}

impl<S: StreamOnce> ParseError<S> {
    pub fn new(position: S::Position, error: Error<S::Item, S::Range>) -> ParseError<S> {
        ParseError::from_errors(position, vec![error])
    }

    pub fn empty(position: S::Position) -> ParseError<S> {
        ParseError::from_errors(position, vec![])
    }

    pub fn from_errors(position: S::Position,
                       errors: Vec<Error<S::Item, S::Range>>)
                       -> ParseError<S> {
        ParseError {
            position: position,
            errors: errors,
        }
    }

    pub fn end_of_input(position: S::Position) -> ParseError<S> {
        ParseError::new(position, Error::end_of_input())
    }

    pub fn add_message<M>(&mut self, message: M)
        where M: Into<Info<S::Item, S::Range>>
    {
        self.add_error(Error::Message(message.into()));
    }

    pub fn add_error(&mut self, message: Error<S::Item, S::Range>) {
        // Don't add duplicate errors
        if self.errors.iter().all(|msg| *msg != message) {
            self.errors.push(message);
        }
    }

    pub fn set_expected(&mut self, message: Info<S::Item, S::Range>) {
        // Remove all other expected messages
        self.errors.retain(|e| {
            match *e {
                Error::Expected(_) => false,
                _ => true,
            }
        });
        self.errors.push(Error::Expected(message));
    }

    pub fn merge(mut self, other: ParseError<S>) -> ParseError<S> {
        use std::cmp::Ordering;
        // Only keep the errors which occured after consuming the most amount of data
        match self.position.cmp(&other.position) {
            Ordering::Less => other,
            Ordering::Greater => self,
            Ordering::Equal => {
                for message in other.errors.into_iter() {
                    self.add_error(message);
                }
                self
            }
        }
    }
}

impl<S> StdError for ParseError<S>
    where S: Stream,
          S::Range: fmt::Display + fmt::Debug + Any,
          S::Item: fmt::Display + fmt::Debug + Any,
          S::Position: fmt::Display + fmt::Debug + Any
{
    fn description(&self) -> &str {
        "parse error"
    }
}

impl<S> PartialEq for ParseError<S>
    where S: Stream,
          S::Position: PartialEq
{
    fn eq(&self, other: &ParseError<S>) -> bool {
        self.position == other.position && self.errors == other.errors
    }
}

impl<S> fmt::Debug for ParseError<S>
    where S: Stream,
          S::Range: fmt::Debug,
          S::Item: fmt::Debug,
          S::Position: fmt::Debug
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f,
               "ParseError {{ position: {:?}, errors: {:?} }}",
               self.position,
               self.errors)
    }
}

impl<S> fmt::Display for ParseError<S>
    where S: Stream,
          S::Item: fmt::Display,
          S::Range: fmt::Display,
          S::Position: fmt::Display
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(writeln!(f, "Parse error at {}", self.position));

        // First print the token that we did not expect
        // There should really just be one unexpected message at this point though we print them
        // all to be safe
        let unexpected = self.errors
            .iter()
            .filter(|e| {
                match **e {
                    Error::Unexpected(_) => true,
                    _ => false,
                }
            });
        for error in unexpected {
            try!(writeln!(f, "{}", error));
        }

        // Then we print out all the things that were expected in a comma separated list
        // 'Expected 'a', 'expression' or 'let'
        let iter = || {
            self.errors
                .iter()
                .filter_map(|e| {
                    match *e {
                        Error::Expected(ref err) => Some(err),
                        _ => None,
                    }
                })
        };
        let expected_count = iter().count();
        let mut i = 0;
        for message in iter() {
            i += 1;
            if i == 1 {
                try!(write!(f, "Expected"));
            } else if i == expected_count {
                // Last expected message to be written
                try!(write!(f, " or"));
            } else {
                try!(write!(f, ","));
            }
            try!(write!(f, " '{}'", message));
        }
        if expected_count != 0 {
            try!(writeln!(f, ""));
        }
        // If there are any generic messages we print them out last
        let messages = self.errors
            .iter()
            .filter(|e| {
                match **e {
                    Error::Message(_) |
                    Error::Other(_) => true,
                    _ => false,
                }
            });
        for error in messages {
            try!(writeln!(f, "{}", error));
        }
        Ok(())
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
            Error::Unexpected(ref c) => write!(f, "Unexpected '{}'", c),
            Error::Expected(ref s) => write!(f, "Expected {}", s),
            Error::Message(ref msg) => msg.fmt(f),
            Error::Other(ref err) => err.fmt(f),
        }
    }
}

/// The `State<I>` struct keeps track of the current position in the stream `I` using the
/// `Positioner` trait to update the position.
#[derive(Clone, PartialEq)]
pub struct State<I>
    where I: Stream,
          I::Item: Positioner
{
    /// The current position
    pub position: <I::Item as Positioner>::Position,
    /// The input stream used when items are requested
    pub input: I,
}

impl<I> fmt::Debug for State<I>
    where I: Stream + fmt::Debug,
          I::Item: Positioner,
          <I::Item as Positioner>::Position: fmt::Debug
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f,
               "State {{ position: {:?}, input: {:?} }}",
               self.position,
               self.input)
    }
}

impl<I> State<I>
    where I: Stream,
          I::Item: Positioner
{
    /// Creates a new `State<I>` from an input stream. Initializes the position to
    /// `Positioner::start()`
    pub fn new(input: I) -> State<I> {
        State {
            position: <I::Item as Positioner>::start(),
            input: input,
        }
    }
}

impl<I> StreamOnce for State<I>
    where I: Stream,
          I::Item: Positioner
{
    type Item = I::Item;
    type Range = I::Range;
    type Position = <I::Item as Positioner>::Position;

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

    #[inline(always)]
    fn position(&self) -> Self::Position {
        self.position.clone()
    }
}

impl<I, E> RangeStream for State<I>
    where I: RangeStream<Item = E>,
          I::Range: Range + Positioner<Position = E::Position>,
          E: Positioner + Clone
{
    #[inline]
    fn uncons_range(&mut self, size: usize) -> Result<I::Range, Error<I::Item, I::Range>> {
        let position = &mut self.position;
        self.input
            .uncons_range(size)
            .map(|value| {
                value.update(position);
                value
            })
    }

    #[inline]
    fn uncons_while<F>(&mut self, mut predicate: F) -> Result<I::Range, Error<I::Item, I::Range>>
        where F: FnMut(I::Item) -> bool
    {
        let position = &mut self.position;
        self.input.uncons_while(|t| {
            if predicate(t.clone()) {
                t.update(position);
                true
            } else {
                false
            }
        })
    }
}

/// A type alias over the specific `Result` type used by parsers to indicate wether they were
/// successful or not.
/// `O` is the type that is output on success
/// `I` is the specific stream type used in the parser
pub type ParseResult<O, I> = Result<(O, Consumed<I>), Consumed<ParseError<I>>>;

/// `StreamOnce` represents a sequence of items that can be extracted one by one.
pub trait StreamOnce {
    /// The type of items which is yielded from this stream
    type Item: Clone + PartialEq;

    /// The type of a range of items yielded from this stream.
    /// Types which do not a have a way of yielding ranges of items should just use the
    /// Self::Item for this type
    type Range: Clone + PartialEq;

    /// Type which represents the position in a stream.
    /// Ord is required to allow parsers to determine which of two positions are further ahead.
    type Position: Ord;

    /// Takes a stream and removes its first item, yielding the item and the rest of the elements
    /// Returns `Err` if no element could be retrieved
    fn uncons(&mut self) -> Result<Self::Item, Error<Self::Item, Self::Range>>;

    /// Returns the current position of the stream
    fn position(&self) -> Self::Position;
}

/// A stream of tokens which can be duplicated
pub trait Stream: StreamOnce + Clone {}

impl<I> Stream for I where I: StreamOnce + Clone {}

#[inline]
pub fn uncons<I>(mut input: I) -> ParseResult<I::Item, I>
    where I: Stream
{
    let position = input.position();
    let x = try!(input.uncons().map_err(|err| Consumed::Empty(ParseError::new(position, err))));
    Ok((x, Consumed::Consumed(input)))
}

/// A `RangeStream` is an extension of Stream which allows for zero copy parsing
pub trait RangeStream: Stream {
    /// Takes `size` elements from the stream
    /// Fails if the length of the stream is less than `size`.
    fn uncons_range(&mut self, size: usize) -> Result<Self::Range, Error<Self::Item, Self::Range>>;

    /// Takes items from stream, testing each one with `predicate`
    /// returns the range of items which passed `predicate`
    fn uncons_while<F>(&mut self, f: F) -> Result<Self::Range, Error<Self::Item, Self::Range>>
        where F: FnMut(Self::Item) -> bool;
}

/// Removes items from the input while `predicate` returns `true`.
#[inline]
pub fn uncons_while<I, F>(mut input: I, predicate: F) -> ConsumedResult<I::Range, I>
    where F: FnMut(I::Item) -> bool,
          I: RangeStream,
          I::Range: Range
{
    match input.uncons_while(predicate) {
        Err(err) => EmptyErr(ParseError::new(input.position(), err)),
        Ok(x) => {
            if x.len() == 0 {
                EmptyOk((x, input))
            } else {
                ConsumedOk((x, input))
            }
        }
    }
}

pub trait Range {
    /// Returns the remaining length of `self`.
    /// The returned length need not be the same as the number of items left in the stream
    fn len(&self) -> usize;
}

impl<'a> RangeStream for &'a str {
    #[inline]
    fn uncons_while<F>(&mut self, mut f: F) -> Result<&'a str, Error<char, &'a str>>
        where F: FnMut(Self::Item) -> bool
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
                Err(Error::Message("uncons_range on non character boundary".into()))
            }
        } else {
            Err(Error::end_of_input())
        }
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
    where T: Copy + PartialEq
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
        where F: FnMut(Self::Item) -> bool
    {
        let len = self.iter()
            .take_while(|c| f(**c))
            .count();
        let (result, remaining) = self.split_at(len);
        *self = remaining;
        Ok(result)
    }
}

impl<'a> StreamOnce for &'a str {
    type Item = char;
    type Range = &'a str;
    type Position = usize;

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

    #[inline(always)]
    fn position(&self) -> Self::Position {
        self.as_bytes().as_ptr() as usize
    }
}

impl<'a, T> StreamOnce for &'a [T]
    where T: Copy + PartialEq
{
    type Item = T;
    type Range = &'a [T];
    type Position = usize;

    #[inline]
    fn uncons(&mut self) -> Result<T, Error<T, &'a [T]>> {
        match self.split_first() {
            Some((first, rest)) => {
                *self = rest;
                Ok(*first)
            }
            None => Err(Error::end_of_input()),
        }
    }

    #[inline(always)]
    fn position(&self) -> Self::Position {
        self.as_ptr() as usize
    }
}

/// Newtype for constructing a stream from a slice where the items in the slice are not copyable
#[derive(Copy, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub struct SliceStream<'a, T: 'a>(pub &'a [T]);

impl<'a, T> Clone for SliceStream<'a, T> {
    fn clone(&self) -> SliceStream<'a, T> {
        SliceStream(self.0)
    }
}

impl<'a, T> StreamOnce for SliceStream<'a, T>
    where T: Clone + PartialEq + 'a
{
    type Item = &'a T;
    type Range = &'a [T];
    type Position = usize;

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

    #[inline(always)]
    fn position(&self) -> Self::Position {
        self.0.as_ptr() as usize
    }
}

impl<'a, T> RangeStream for SliceStream<'a, T>
    where T: Clone + PartialEq + 'a
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
        where F: FnMut(Self::Item) -> bool
    {
        let len = self.0
            .iter()
            .take_while(|c| f(*c))
            .count();
        let (range, rest) = self.0.split_at(len);
        self.0 = rest;
        Ok(range)
    }
}

/// Wrapper around iterators which allows them to be treated as a stream.
/// Returned by `from_iter`.
#[derive(Clone, Debug)]
pub struct IteratorStream<I>(I, usize) where I: Iterator;


/// Converts an `Iterator` into a stream.
pub fn from_iter<I>(iter: I) -> IteratorStream<I>
    where I: Iterator
{
    IteratorStream(iter, 0)
}

impl<I> Iterator for IteratorStream<I>
    where I: Iterator
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

impl<I: Iterator> StreamOnce for IteratorStream<I>
    where I::Item: Clone + PartialEq
{
    type Item = I::Item;
    type Range = I::Item;
    type Position = usize;

    #[inline]
    fn uncons(&mut self) -> Result<I::Item, Error<I::Item, I::Item>> {
        match self.next() {
            Some(x) => Ok(x),
            None => Err(Error::end_of_input()),
        }
    }

    #[inline(always)]
    fn position(&self) -> Self::Position {
        self.1
    }
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
    where T: Positioner
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
    where T: Positioner
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
    where T: Positioner + 'a
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
        SourcePosition {
            line: 1,
            column: 1,
        }
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
        where F: FnOnce(T) -> FastResult<T2, E>
    {
        match self {
            ConsumedOk(t) => {
                match f(t) {
                    ConsumedOk(t2) | EmptyOk(t2) => ConsumedOk(t2),
                    EmptyErr(e) | ConsumedErr(e) => ConsumedErr(e),
                }
            }
            EmptyOk(t) => f(t),
            ConsumedErr(e) => ConsumedErr(e),
            EmptyErr(e) => EmptyErr(e),
        }
    }
}

impl<T, E> ConsumedResult<T, E>
    where E: StreamOnce
{
    pub fn map<F, T2>(self, f: F) -> ConsumedResult<F::Output, E>
        where F: FnOnce(T) -> T2
    {
        match self {
            ConsumedOk((t, i)) => ConsumedOk((f(t), i)),
            EmptyOk((t, i)) => EmptyOk((f(t), i)),
            ConsumedErr(e) => ConsumedErr(e),
            EmptyErr(e) => EmptyErr(e),
        }
    }
}

pub type ConsumedResult<O, I> = FastResult<(O, I), ParseError<I>>;

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
    where I: StreamOnce
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
    where I: StreamOnce
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

/// By implementing the `Parser` trait a type says that it can be used to parse an input stream into
/// the type `Output`.
///
/// All methods have a default implementation but there needs to be at least an implementation of
/// `parse_state` or`parse_lazy`. If `parse_lazy` is implemented an implementation of `add_error` is
/// also recommended to improve error reporting.
pub trait Parser {
    /// The type which is take as input for the parser. The type must implement the `Stream` trait
    /// which allows the parser to read item from the type.
    type Input: Stream;
    /// The type which is returned if the parser is successful.
    type Output;

    /// Entrypoint of the parser
    /// Takes some input and tries to parse it returning a `ParseResult`
    fn parse(&mut self,
             input: Self::Input)
             -> Result<(Self::Output, Self::Input), ParseError<Self::Input>> {
        match self.parse_state(input) {
            Ok((v, state)) => Ok((v, state.into_inner())),
            Err(error) => Err(error.into_inner()),
        }
    }

    /// Parses using the state `input` by calling Stream::uncons one or more times
    /// On success returns `Ok((value, new_state))` on failure it returns `Err(error)`
    #[inline(always)]
    fn parse_state(&mut self, input: Self::Input) -> ParseResult<Self::Output, Self::Input> {
        self.parse_state_fast(input).into()
    }

    #[inline]
    fn parse_state_fast(&mut self,
                        mut input: Self::Input)
                        -> ConsumedResult<Self::Output, Self::Input> {
        let mut result = self.parse_lazy(input.clone());
        if let FastResult::EmptyErr(ref mut error) = result {
            if let Ok(t) = input.uncons() {
                error.add_error(Error::Unexpected(Info::Token(t)));
            }
            self.add_error(error);
        }
        result.into()
    }

    /// Specialized version of parse_state where the parser does not need to add an error to the
    /// `ParseError` when it does not consume any input before encountering the error.
    /// Instead the error can be added later through the `add_error` method
    #[inline]
    fn parse_lazy(&mut self, input: Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        self.parse_state(input).into()
    }

    /// Adds the first error that would normally be returned by this parser if it failed
    fn add_error(&mut self, _error: &mut ParseError<Self::Input>) {}
}
impl<'a, I, O, P: ?Sized> Parser for &'a mut P
    where I: Stream,
          P: Parser<Input = I, Output = O>
{
    type Input = I;
    type Output = O;

    #[inline(always)]
    fn parse_state(&mut self, input: I) -> ParseResult<O, I> {
        (**self).parse_state(input)
    }

    #[inline(always)]
    fn parse_state_fast(&mut self, input: I) -> ConsumedResult<O, I> {
        (**self).parse_state_fast(input)
    }

    #[inline(always)]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<O, I> {
        (**self).parse_lazy(input)
    }

    #[inline(always)]
    fn add_error(&mut self, error: &mut ParseError<Self::Input>) {
        (**self).add_error(error)
    }
}
impl<I, O, P: ?Sized> Parser for Box<P>
    where I: Stream,
          P: Parser<Input = I, Output = O>
{
    type Input = I;
    type Output = O;

    #[inline(always)]
    fn parse_state(&mut self, input: I) -> ParseResult<O, I> {
        (**self).parse_state(input)
    }

    #[inline(always)]
    fn parse_state_fast(&mut self, input: I) -> ConsumedResult<O, I> {
        (**self).parse_state_fast(input)
    }

    #[inline(always)]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<O, I> {
        (**self).parse_lazy(input)
    }

    #[inline(always)]
    fn add_error(&mut self, error: &mut ParseError<Self::Input>) {
        (**self).add_error(error)
    }
}

/// A `BufferedStream` wraps an instance `StreamOnce`, allowing it to b used as a `Stream`
pub struct BufferedStream<'a, I>
    where I: StreamOnce + 'a,
          I::Item: 'a
{
    offset: usize,
    buffer: &'a SharedBufferedStream<I>,
}

impl<'a, I> fmt::Debug for BufferedStream<'a, I>
    where I: StreamOnce + 'a,
          I::Item: 'a
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let buffer_offset = unsafe { (*self.buffer.buffer.get()).offset };
        write!(f,
               "BufferedStream {{ offset: {:?} buffer_offset: {:?} }}",
               self.offset,
               buffer_offset)
    }
}

impl<'a, I> Clone for BufferedStream<'a, I>
    where I: StreamOnce + 'a,
          I::Position: Clone,
          I::Item: 'a
{
    fn clone(&self) -> BufferedStream<'a, I> {
        BufferedStream {
            offset: self.offset,
            buffer: self.buffer,
        }
    }
}

pub struct SharedBufferedStream<I>
    where I: StreamOnce
{
    buffer: UnsafeCell<BufferedStreamInner<I>>,
}

struct BufferedStreamInner<I>
    where I: StreamOnce
{
    offset: usize,
    iter: I,
    buffer: VecDeque<(I::Item, I::Position)>,
}

impl<I> BufferedStreamInner<I>
    where I: StreamOnce,
          I::Position: Clone,
          I::Item: Clone
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
            Ok(self.buffer[self.buffer.len() - (self.offset - offset)].0.clone())
        }
    }

    #[inline]
    fn position(&self, offset: usize) -> I::Position {
        if offset >= self.offset {
            self.iter.position()
        } else if offset < self.offset - self.buffer.len() {
            self.buffer.front().expect("Atleast 1 element in the buffer").1.clone()
        } else {
            self.buffer[self.buffer.len() - (self.offset - offset)].1.clone()
        }
    }
}

impl<I> SharedBufferedStream<I>
    where I: StreamOnce,
          I::Position: Clone,
          I::Item: Clone
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
    where I: StreamOnce
{
    /// Constructs a new `BufferedStream` froma a `StreamOnce` instance with a `lookahead` number
    /// of elements stored in the buffer.
    ///
    /// `BufferedStream` always implement `Stream` allowing one-shot streams to used as if could
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

impl<'a, I> StreamOnce for BufferedStream<'a, I>
    where I: StreamOnce + 'a,
          I::Position: Clone,
          I::Item: Clone + PartialEq + 'a
{
    type Item = I::Item;
    type Range = I::Range;
    type Position = I::Position;

    #[inline]
    fn uncons(&mut self) -> Result<I::Item, Error<I::Item, I::Range>> {
        let value = try!(self.buffer.uncons(self.offset));
        self.offset += 1;
        Ok(value)
    }

    #[inline(always)]
    fn position(&self) -> Self::Position {
        self.buffer.position(self.offset)
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
}

use std::fmt;
use std::error::Error as StdError;
use std::any::Any;
#[cfg(feature = "buffered_stream")]
use std::cell::UnsafeCell;
#[cfg(feature = "buffered_stream")]
use std::collections::VecDeque;

///Struct which represents a position in a source file
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct SourcePosition {
    ///Current line of the input
    pub line: i32,
    ///Current column of the input
    pub column: i32,
}

///Struct which represents a position in a byte stream
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct BytePosition {
    ///Current position
    pub position: usize,
}

impl fmt::Display for BytePosition {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "position: {}", self.position)
    }
}

///Enum holding error information
///As there is implementations of `From` for `T: Positioner`, `String` and `&'static str` the
///constructor need not be used directly as calling `msg.into()` should turn a message into the
///correct `Info` variant
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

///Enum used to store information about an error that has occured
#[derive(Debug)]
pub enum Error<T, R> {
    ///Error indicating an unexpected token has been encountered in the stream
    Unexpected(Info<T, R>),
    ///Error indicating that the parser expected something else
    Expected(Info<T, R>),
    ///Generic message
    Message(Info<T, R>),
    ///Variant for containing other types of errors
    Other(Box<StdError + Send>),
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

impl<E, T, R> From<E> for Error<T, R> where E: StdError + 'static + Send
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

///Enum used to indicate if a parser consumed any items of the stream it was given as an input
#[derive(Clone, PartialEq, Debug, Copy)]
pub enum Consumed<T> {
    ///Constructor indicating that the parser has consumed elements
    Consumed(T),
    ///Constructor indicating that the parser did not consume any elements
    Empty(T),
}

impl<T> Consumed<T> {
    ///Returns true if `self` is empty
    pub fn is_empty(&self) -> bool {
        match *self {
            Consumed::Empty(_) => true,
            Consumed::Consumed(_) => false,
        }
    }

    ///Extracts the contained value
    pub fn into_inner(self) -> T {
        match self {
            Consumed::Empty(x) => x,
            Consumed::Consumed(x) => x,
        }
    }

    ///Converts `self` into the Consumed state
    pub fn as_consumed(self) -> Consumed<T> {
        Consumed::Consumed(self.into_inner())
    }

    ///Converts `self` into theEmpty state
    pub fn as_empty(self) -> Consumed<T> {
        Consumed::Empty(self.into_inner())
    }

    ///Maps over the contained value without changing the consumed state
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

    ///Combines the Consumed flags from `self` and the result of `f`
    ///
    ///```
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
    ///```
    pub fn combine<F, U, I>(self, f: F) -> ParseResult<U, I>
        where F: FnOnce(T) -> ParseResult<U, I>,
              I: Stream
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
}
///Struct which hold information about an error that occured at a specific position.
///Can hold multiple instances of `Error` if more that one error occured in the same position.
pub struct ParseError<S: Stream> {
    ///The position where the error occured
    pub position: S::Position,
    ///A vector containing specific information on what errors occured at `position`
    pub errors: Vec<Error<S::Item, S::Range>>,
}

impl<S: Stream> ParseError<S> {
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
                                   Error::Message(_) | Error::Other(_) => true,
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

///The `State<I>` struct keeps track of the current position in the stream `I`
#[derive(Clone, PartialEq)]
pub struct State<I>
    where I: Stream,
          I::Item: Positioner
{
    ///The current position
    pub position: <I::Item as Positioner>::Position,
    ///The input stream used when items are requested
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
    ///Creates a new `State<I>` from an input stream. Initializes the position to
    ///`Positioner::start()`
    pub fn new(input: I) -> State<I> {
        State {
            position: <I::Item as Positioner>::start(),
            input: input,
        }
    }
}

impl<I> Stream for State<I>
    where I: Stream,
          I::Item: Positioner
{
    type Item = I::Item;
    type Range = I::Range;
    type Position = <I::Item as Positioner>::Position;

    fn uncons(self) -> Result<(I::Item, State<I>), Error<I::Item, I::Range>> {
        let State { mut position, input, .. } = self;
        match input.uncons() {
            Ok((c, input)) => {
                c.update(&mut position);
                Ok((c,
                    State {
                    position: position,
                    input: input,
                }))
            }
            Err(err) => Err(err),
        }
    }

    fn position(&self) -> Self::Position {
        self.position.clone()
    }
}

#[cfg(feature = "range_stream")]
impl<I, E> RangeStream for State<I>
    where I: RangeStream<Item = E>,
          I::Range: Range + Positioner<Position = E::Position>,
          E: Positioner + Clone
{
    fn uncons_range(self, size: usize) -> Result<(I::Range, State<I>), Error<I::Item, I::Range>> {
        let State { mut position, input, .. } = self;
        input.uncons_range(size)
             .map(|(value, input)| {
                 value.update(&mut position);
                 let state = State {
                     position: position,
                     input: input,
                 };
                 (value, state)
             })
    }

    fn uncons_while<F>(self,
                       mut predicate: F)
                       -> Result<(I::Range, State<I>), Error<I::Item, I::Range>>
        where F: FnMut(I::Item) -> bool
    {
        let State { mut position, input, .. } = self;
        input.uncons_while(|t| {
                 if predicate(t.clone()) {
                     t.update(&mut position);
                     true
                 } else {
                     false
                 }
             })
             .map(|(value, input)| {
                 let state = State {
                     position: position,
                     input: input,
                 };
                 (value, state)
             })
    }
}

///A type alias over the specific `Result` type used by parsers to indicate wether they were
///successful or not.
///`O` is the type that is output on success
///`I` is the specific stream type used in the parser
pub type ParseResult<O, I> = Result<(O, Consumed<I>), Consumed<ParseError<I>>>;

///A stream is a sequence of items that can be extracted one by one
pub trait Stream : Clone {
    ///The type of items which is yielded from this stream
    type Item: Clone + PartialEq;

    ///The type of a range of items yielded from this stream.
    ///Types which do not a have a way of yielding ranges of items should just use the
    ///Self::Item for this type
    type Range: Clone + PartialEq;

    type Position: Ord;

    ///Takes a stream and removes its first item, yielding the item and the rest of the elements
    ///Returns `Err` if no element could be retrieved
    fn uncons(self) -> Result<(Self::Item, Self), Error<Self::Item, Self::Range>>;

    fn position(&self) -> Self::Position;
}

pub fn uncons<I>(input: I) -> ParseResult<I::Item, I>
    where I: Stream
{
    let position = input.position();
    input.uncons()
         .map(|(x, input)| (x, Consumed::Consumed(input)))
         .map_err(|err| Consumed::Empty(ParseError::new(position, err)))
}

#[cfg(feature = "range_stream")]
pub trait RangeStream: Stream {
    ///Takes `size` elements from the stream
    ///Fails if the length of the stream is less than `size`.
    fn uncons_range(self,
                    size: usize)
                    -> Result<(Self::Range, Self), Error<Self::Item, Self::Range>>;

    ///Takes items from stream, testing each one with `predicate`
    ///returns the range of items which passed `predicate`
    fn uncons_while<F>(self, f: F) -> Result<(Self::Range, Self), Error<Self::Item, Self::Range>>
        where F: FnMut(Self::Item) -> bool;
}

#[cfg(feature = "range_stream")]
///Removes items from the input while `predicate` returns `true`.
pub fn uncons_while<I, F>(input: I, predicate: F) -> ParseResult<I::Range, I>
    where F: FnMut(I::Item) -> bool,
          I: RangeStream,
          I::Range: Range
{
    let position = input.position();
    input.uncons_while(predicate)
         .map(|(x, input)| {
             let input = if x.len() == 0 {
                 Consumed::Empty(input)
             } else {
                 Consumed::Consumed(input)
             };
             (x, input)
         })
         .map_err(|err| Consumed::Empty(ParseError::new(position, err)))
}

pub trait Range {
    ///Returns the remaining length of `self`.
    ///The returned length need not be the same as the number of items left in the stream
    fn len(&self) -> usize;
}

#[cfg(feature = "range_stream")]
impl<'a> RangeStream for &'a str {
    fn uncons_while<F>(self, mut f: F) -> Result<(&'a str, &'a str), Error<char, &'a str>>
        where F: FnMut(Self::Item) -> bool
    {
        let len = self.chars()
                      .take_while(|c| f(*c))
                      .fold(0, |len, c| len + c.len_utf8());
        Ok(self.split_at(len))
    }
    fn uncons_range(self, size: usize) -> Result<(&'a str, &'a str), Error<char, &'a str>> {
        fn is_char_boundary(s: &str, index: usize) -> bool {
            if index == s.len() {
                return true;
            }
            match s.as_bytes().get(index) {
                None => false,
                Some(&b) => b < 128 || b >= 192,
            }
        }
        if size < self.len() {
            if is_char_boundary(self, size) {
                Ok(self.split_at(size))
            } else {
                Err(Error::Message("uncons_range on non character boundary".into()))
            }
        } else {
            Err(Error::end_of_input())
        }
    }
}

impl<'a> Range for &'a str {
    fn len(&self) -> usize {
        str::len(self)
    }
}

impl<'a, T> Range for &'a [T] {
    fn len(&self) -> usize {
        <[T]>::len(self)
    }
}

#[cfg(feature = "range_stream")]
impl<'a, T> RangeStream for &'a [T] where T: Copy + PartialEq
{
    fn uncons_range(self, size: usize) -> Result<(&'a [T], &'a [T]), Error<T, &'a [T]>> {
        if size < self.len() {
            Ok(self.split_at(size))
        } else {
            Err(Error::end_of_input())
        }
    }
    fn uncons_while<F>(self, mut f: F) -> Result<(&'a [T], &'a [T]), Error<T, &'a [T]>>
        where F: FnMut(Self::Item) -> bool
    {
        let len = self.iter()
                      .take_while(|c| f(**c))
                      .count();
        Ok(self.split_at(len))
    }
}

impl<'a> Stream for &'a str {
    type Item = char;
    type Range = &'a str;
    type Position = usize;

    fn uncons(self) -> Result<(char, &'a str), Error<char, &'a str>> {
        match self.chars().next() {
            Some(c) => Ok((c, &self[c.len_utf8()..])),
            None => Err(Error::end_of_input()),
        }
    }
    fn position(&self) -> Self::Position {
        self.as_bytes().as_ptr() as usize
    }
}

impl<'a, T> Stream for &'a [T] where T: Copy + PartialEq
{
    type Item = T;
    type Range = &'a [T];
    type Position = usize;

    fn uncons(self) -> Result<(T, &'a [T]), Error<T, &'a [T]>> {
        match self.split_first() {
            Some((first, rest)) => Ok((*first, rest)),
            None => Err(Error::end_of_input()),
        }
    }

    fn position(&self) -> Self::Position {
        self.as_ptr() as usize
    }
}

///Newtype for constructing a stream from a slice where the items in the slice are not copyable
#[derive(Copy, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub struct SliceStream<'a, T: 'a>(pub &'a [T]);

impl<'a, T> Clone for SliceStream<'a, T> {
    fn clone(&self) -> SliceStream<'a, T> {
        SliceStream(self.0)
    }
}

impl<'a, T> Stream for SliceStream<'a, T> where T: Clone + PartialEq + 'a
{
    type Item = &'a T;
    type Range = &'a [T];
    type Position = usize;

    fn uncons(self) -> Result<(&'a T, SliceStream<'a, T>), Error<&'a T, &'a [T]>> {
        match self.0.split_first() {
            Some((first, rest)) => Ok((first, SliceStream(rest))),
            None => Err(Error::end_of_input()),
        }
    }

    fn position(&self) -> Self::Position {
        self.0.as_ptr() as usize
    }
}

#[cfg(feature = "range_stream")]
impl<'a, T> RangeStream for SliceStream<'a, T> where T: Clone + PartialEq + 'a
{
    fn uncons_range(self,
                    size: usize)
                    -> Result<(&'a [T], SliceStream<'a, T>), Error<&'a T, &'a [T]>> {
        if size < self.0.len() {
            let (range, rest) = self.0.split_at(size);
            Ok((range, SliceStream(rest)))
        } else {
            Err(Error::end_of_input())
        }
    }

    fn uncons_while<F>(self,
                       mut f: F)
                       -> Result<(&'a [T], SliceStream<'a, T>), Error<&'a T, &'a [T]>>
        where F: FnMut(Self::Item) -> bool
    {
        let len = self.0
                      .iter()
                      .take_while(|c| f(*c))
                      .count();
        let (range, rest) = self.0.split_at(len);
        Ok((range, SliceStream(rest)))
    }
}

///Wrapper around iterators which allows them to be treated as a stream.
///Returned by `from_iter`.
#[derive(Clone, Debug)]
pub struct IteratorStream<I>(I, usize) where I: Iterator + Clone;


///Converts an `Iterator` into a stream.
pub fn from_iter<I>(iter: I) -> IteratorStream<I>
    where I: Iterator + Clone
{
    IteratorStream(iter, 0)
}

impl<I: Iterator + Clone> Stream for IteratorStream<I> where I::Item: Clone + PartialEq
{
    type Item = I::Item;
    type Range = I::Item;
    type Position = usize;

    fn uncons(mut self) -> Result<(I::Item, Self), Error<I::Item, I::Item>> {
        match self.0.next() {
            Some(x) => {
                self.1 += 1;
                Ok((x, self))
            }
            None => Err(Error::end_of_input()),
        }
    }

    fn position(&self) -> Self::Position {
        self.1
    }
}

///Trait for updating the position for types which can be yielded from a `Stream`.
pub trait Positioner: PartialEq {
    ///The type which keeps track of the position.
    type Position: Clone + Ord;
    ///Creates a start position
    fn start() -> Self::Position;
    ///Updates the position given that `self` has been taken from the stream
    fn update(&self, position: &mut Self::Position);
}
impl<'a, T: ?Sized> Positioner for &'a T where T: Positioner
{
    type Position = T::Position;
    fn start() -> T::Position {
        T::start()
    }
    fn update(&self, position: &mut T::Position) {
        (*self).update(position)
    }
}
impl<T> Positioner for [T] where T: Positioner
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

impl<'a, T> Positioner for SliceStream<'a, T> where T: Positioner + 'a
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

///By implementing the `Parser` trait a type says that it can be used to parse an input stream into
///the type `Output`.
///
///All methods have a default implementation but there needs to be at least an implementation of
///`parse_state` or`parse_lazy`. If `parse_lazy` is implemented an implementation of `add_error` is
///also recommended to improve error reporting.
pub trait Parser {
    ///The type which is take as input for the parser. The type must implement the `Stream` trait
    ///which allows the parser to read item from the type.
    type Input: Stream;
    ///The type which is returned if the parser is successful.
    type Output;

    ///Entrypoint of the parser
    ///Takes some input and tries to parse it returning a `ParseResult`
    fn parse(&mut self,
             input: Self::Input)
             -> Result<(Self::Output, Self::Input), ParseError<Self::Input>> {
        match self.parse_state(input) {
            Ok((v, state)) => Ok((v, state.into_inner())),
            Err(error) => Err(error.into_inner()),
        }
    }

    ///Parses using the state `input` by calling Stream::uncons one or more times
    ///On success returns `Ok((value, new_state))` on failure it returns `Err(error)`
    fn parse_state(&mut self, input: Self::Input) -> ParseResult<Self::Output, Self::Input> {
        let mut result = self.parse_lazy(input.clone());
        if let Err(Consumed::Empty(ref mut error)) = result {
            if let Ok((t, _)) = input.uncons() {
                error.add_error(Error::Unexpected(Info::Token(t)));
            }
            self.add_error(error);
        }
        result
    }

    ///Specialized version of parse_state where the parser does not need to add an error to the
    ///`ParseError` when it does not consume any input before encountering the error.
    ///Instead the error can be added later through the `add_error` method
    fn parse_lazy(&mut self, input: Self::Input) -> ParseResult<Self::Output, Self::Input> {
        self.parse_state(input)
    }

    ///Adds the first error that would normally be returned by this parser if it failed
    fn add_error(&mut self, _error: &mut ParseError<Self::Input>) {}
}
impl<'a, I, O, P: ?Sized> Parser for &'a mut P
    where I: Stream,
          P: Parser<Input = I, Output = O>
{
    type Input = I;
    type Output = O;
    fn parse_state(&mut self, input: I) -> ParseResult<O, I> {
        (**self).parse_state(input)
    }
    fn parse_lazy(&mut self, input: I) -> ParseResult<O, I> {
        (**self).parse_lazy(input)
    }
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
    fn parse_state(&mut self, input: I) -> ParseResult<O, I> {
        (**self).parse_state(input)
    }
    fn parse_lazy(&mut self, input: I) -> ParseResult<O, I> {
        (**self).parse_lazy(input)
    }
    fn add_error(&mut self, error: &mut ParseError<Self::Input>) {
        (**self).add_error(error)
    }
}

#[cfg(feature = "buffered_stream")]
pub struct BufferedStream<'a, I>
    where I: Iterator + 'a,
          I::Item: 'a
{
    offset: usize,
    buffer: &'a SharedBufferedStream<I>,
}

#[cfg(feature = "buffered_stream")]
impl<'a, I> Clone for BufferedStream<'a, I>
    where I: Iterator + 'a,
          I::Item: 'a
{
    fn clone(&self) -> BufferedStream<'a, I> {
        BufferedStream {
            offset: self.offset,
            buffer: self.buffer,
        }
    }
}

#[cfg(feature = "buffered_stream")]
pub struct SharedBufferedStream<I>
    where I: Iterator
{
    buffer: UnsafeCell<BufferedStreamInner<I>>,
}

#[cfg(feature = "buffered_stream")]
struct BufferedStreamInner<I>
    where I: Iterator
{
    offset: usize,
    iter: I,
    buffer: VecDeque<I::Item>,
}

#[cfg(feature = "buffered_stream")]
impl<I> BufferedStreamInner<I>
    where I: Iterator,
          I::Item: Clone
{
    fn uncons(&mut self, offset: usize) -> Result<I::Item, Error<I::Item, I::Item>> {
        if offset >= self.offset {
            let item = match self.iter.next() {
                Some(item) => item,
                None => return Err(Error::end_of_input()),
            };
            self.offset += 1;
            // We want the VecDeque to only keep the last .capacity() elements so we need to remove
            // an element if it gets to large
            if self.buffer.len() == self.buffer.capacity() {
                self.buffer.pop_front();
            }
            self.buffer.push_back(item.clone());
            Ok(item)
        } else if offset < self.offset - self.buffer.len() {
            // We have backtracked to far
            Err(Error::Message("Backtracked to far".into()))
        } else {
            Ok(self.buffer[self.buffer.len() - (self.offset - offset)].clone())
        }
    }
}

#[cfg(feature = "buffered_stream")]
impl<I> SharedBufferedStream<I>
    where I: Iterator,
          I::Item: Clone
{
    pub fn as_stream(&self) -> BufferedStream<I> {
        BufferedStream {
            offset: 0,
            buffer: self,
        }
    }
    fn uncons(&self, offset: usize) -> Result<I::Item, Error<I::Item, I::Item>> {
        unsafe { (*self.buffer.get()).uncons(offset) }
    }
}

#[cfg(feature = "buffered_stream")]
impl<'a, I> BufferedStream<'a, I> where I: Iterator
{
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

#[cfg(feature = "buffered_stream")]
impl<'a, I> Stream for BufferedStream<'a, I>
    where I: Iterator + 'a,
          I::Item: Clone + PartialEq + 'a
{
    type Item = I::Item;
    type Range = I::Item;
    type Position = usize;

    fn uncons(mut self) -> Result<(I::Item, BufferedStream<'a, I>), Error<I::Item, I::Item>> {
        let value = try!(self.buffer.uncons(self.offset));
        self.offset += 1;
        Ok((value, self))
    }

    fn position(&self) -> Self::Position {
        self.offset
    }
}

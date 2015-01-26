use std::fmt;
use std::error::Error as StdError;
use std::any::Any;

///Struct which represents the positions in the source file
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct SourcePosition {
    ///Current line of the input
    pub line: i32,
    ///Current column of the input
    pub column: i32
}
impl SourcePosition {
    fn start() -> SourcePosition {
        SourcePosition { line: 1, column: 1 }
    }

    fn update(&mut self, c: &char) {
        self.column += 1;
        if *c == '\n' {
            self.column = 1;
            self.line += 1;
        }
    }
}

#[derive(Clone, Debug)]
pub enum Info {
    Token(char),
    Owned(String),
    Borrowed(&'static str)
}

impl PartialEq for Info {
    fn eq(&self, other: &Info) -> bool {
        match (self, other) {
            (&Info::Token(l), &Info::Token(r)) => l == r,
            (&Info::Owned(ref l), &Info::Owned(ref r)) => l == r,
            (&Info::Borrowed(ref l), &Info::Owned(ref r)) => l == r,
            (&Info::Owned(ref l), &Info::Borrowed(ref r)) => l == r,
            (&Info::Borrowed(ref l), &Info::Borrowed(ref r)) => l == r,
            _ => false
        }
    }
}
impl fmt::Display for Info {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Info::Token(c) => write!(f, "{}", c),
            Info::Owned(ref s) => write!(f, "{}", s),
            Info::Borrowed(s) => write!(f, "{}", s),
        }
    }
}

impl From<char> for Info {
    fn from(s: char) -> Info {
        Info::Token(s)
    }
}

impl From<String> for Info {
    fn from(s: String) -> Info {
        Info::Owned(s)
    }
}

impl From<&'static str> for Info {
    fn from(s: &'static str) -> Info {
        Info::Borrowed(s)
    }
}

///Enum used to store information about an error that has occured
#[derive(Debug)]
pub enum Error {
    ///Error indicating an unexpected token has been encountered in the stream
    Unexpected(char),
    ///Error indicating that the parser expected something else
    Expected(Info),
    ///Generic message
    Message(Info),
    ///Variant for containing other types of errors
    Other(Box<StdError+Send>)
}

impl PartialEq for Error {
    fn eq(&self, other: &Error) -> bool {
        match (self, other) {
            (&Error::Unexpected(l), &Error::Unexpected(r)) => l == r,
            (&Error::Expected(ref l), &Error::Expected(ref r)) => l == r,
            (&Error::Message(ref l), &Error::Message(ref r)) => l == r,
            _ => false
        }
    }
}

impl <E> From<E> for Error where E: StdError + 'static + Send {
    fn from(e: E) -> Error {
        Error::Other(Box::new(e))
    }
}

///Enum used to indicate if a parser consumed any items of the stream it was given as an input
#[derive(Clone, PartialEq, Debug, Copy)]
pub enum Consumed<T> {
    ///Constructor indicating that the parser has consumed elements
    Consumed(T),
    ///Constructor indicating that the parser did not consume any elements
    Empty(T)
}

impl <T> Consumed<T> {

    ///Returns true if `self` is empty
    pub fn is_empty(&self) -> bool {
        match *self {
            Consumed::Empty(_) => true,
            Consumed::Consumed(_) => false
        }
    }

    ///Extracts the contained value
    pub fn into_inner(self) -> T {
        match self {
            Consumed::Empty(x) => x,
            Consumed::Consumed(x) => x
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
        where F: FnOnce(T) -> U {
        match self {
            Consumed::Empty(x) => Consumed::Empty(f(x)),
            Consumed::Consumed(x) => Consumed::Consumed(f(x))
        }
    }

    ///Combines the Consumed flags from `self` and the result of `f`
    ///
    ///```
    /// # extern crate parser_combinators as pc;
    /// # use pc::*;
    /// # use pc::primitives::State;
    /// # fn main() {
    /// //Parses a characther of string literal and handles the escaped characthers \\ and \" as \
    /// //and " respectively
    /// fn char(input: State<&str>) -> ParseResult<char, &str> {
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
    pub fn combine<F, U, I>(self, f: F) -> ParseResult<U, I, I::Item>
        where F: FnOnce(T) -> ParseResult<U, I, I::Item>
            , I: Stream {
        match self {
            Consumed::Consumed(x) => {
                match f(x) {
                    Ok((v, Consumed::Empty(rest))) => Ok((v, Consumed::Consumed(rest))),
                    Err(Consumed::Empty(err)) => Err(Consumed::Consumed(err)),
                    y => y
                }
            }
            Consumed::Empty(x) => f(x)
        }
    }
}
///Struct which hold information about an error that occured at a specific position.
///Can hold multiple instances of `Error` if more that one error occured at the position.
#[derive(Debug, PartialEq)]
pub struct ParseError<P: Positioner> {
    ///The position where the error occured
    pub position: P::Position,
    ///A vector containing specific information on what errors occured at `position`
    pub errors: Vec<Error>
}

impl <P: Positioner> ParseError<P> {
    pub fn new(position: P::Position, error: Error) -> ParseError<P> {
        ParseError::from_errors(position, vec![error])
    }
    pub fn from_errors(position: P::Position, errors: Vec<Error>) -> ParseError<P> {
        ParseError { position: position, errors: errors }
    }
    pub fn add_message<S>(&mut self, message: S)
        where S: Into<Info> {
        self.add_error(Error::Message(message.into()));
    }
    pub fn add_error(&mut self, message: Error) {
        //Don't add duplicate errors
        if self.errors.iter().find(|msg| **msg == message).is_none() {
            self.errors.push(message);
        }
    }
    pub fn set_expected(&mut self, message: Info) {
        //Remove all other expected messages
        self.errors.retain(|e| match *e { Error::Expected(_) => false, _ => true });
        self.errors.push(Error::Expected(message));
    }
    pub fn merge(mut self, other: ParseError<P>) -> ParseError<P> {
        use std::cmp::Ordering;
        //Only keep the errors which occured after consuming the most amount of data
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

impl <P> StdError for ParseError<P>
    where P: fmt::Display + fmt::Debug + Positioner + Any
        , P::Position: fmt::Display + fmt::Debug + Positioner + Any {
    fn description(&self) -> &str { "parse error" }
}

impl <P: Positioner> fmt::Display for ParseError<P>
    where P::Position: fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(writeln!(f, "Parse error at {}", self.position));

        //First print the token that we did not expect
        //There should really just be one unexpected message at this point though we print them
        //all to be safe
        let unexpected = self.errors.iter()
            .filter(|e| match **e { Error::Unexpected(_) => true, _ => false } );
        for error in unexpected {
            try!(writeln!(f, "{}", error));
        }

        //Then we print out all the things that were expected in a comma separated list
        //'Expected 'a', 'expression' or 'let'
        let expected_count = self.errors.iter()
            .filter(|e| match **e { Error::Expected(_) => true, _ => false } )
            .count();
        let mut i = 0;
        for error in self.errors.iter() {
            match *error {
                Error::Expected(ref message) => {
                    i += 1;
                    if i == 1 {
                        try!(write!(f, "Expected"));
                    }
                    else if i == expected_count {//Last expected message to be written
                        try!(write!(f, " or"));
                    }
                    else {
                        try!(write!(f, ","));
                    }
                    try!(write!(f, " '{}'", message));
                }
                _ => ()
            }
        }
        if expected_count != 0 {
            try!(writeln!(f, ""));
        }
        //If there are any generic messages we print them out last
        let messages = self.errors.iter()
            .filter(|e| match **e { Error::Message(_) | Error::Other(_) => true, _ => false } );
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
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::Unexpected(c) => write!(f, "Unexpected character '{}'", c),
            Error::Expected(ref s) => write!(f, "Expected {}", s),
            Error::Message(ref msg) => write!(f, "{}", msg),
            Error::Other(ref err) => err.fmt(f)
        }
    }
}

///The `State<I>` struct keeps track of the current position in the stream `I`
#[derive(Clone, PartialEq, Debug)]
pub struct State<I>
    where I: Stream, <<I as Stream>::Item as Positioner>::Position: Clone + PartialEq + fmt::Debug {
    pub position: <<I as Stream>::Item as Positioner>::Position,
    pub input: I
}

impl <I: Stream> State<I> {
    pub fn new(input: I) -> State<I> {
        State { position: <I::Item as Positioner>::start(), input: input }
    }

    pub fn as_empty(&self) -> State<I> {
        State { position: self.position.clone(), input: self.input.clone() }
    }

    ///`uncons` is the most general way of extracting and item from a stream
    ///It takes a function `f` as argument which should update the position
    ///according to the item that was extracted
    ///Usually you want to use `uncons_char` instead which works directly on character streams
    pub fn uncons(self) -> ParseResult<I::Item, I, I::Item> {
        let State { mut position, input, .. } = self;
        match input.uncons() {
            Ok((c, input)) => {
                c.update(&mut position);
                Ok((c, Consumed::Consumed(State { position: position, input: input })))
            }
            Err(()) => Err(Consumed::Empty(ParseError::new(position, Error::Message("End of input".into()))))
        }
    }
}
impl <I: Stream<Item=char>> State<I> {
    ///Specialized uncons function for character streams which updates the position
    ///with no further action needed
    pub fn uncons_char(self) -> ParseResult<I::Item, I, I::Item> {
        self.uncons()
    }
}

///A type alias over the specific `Result` type used by parsers to indicate wether they were
///successful or not.
///`O` is the type that is output on success
///`I` is the specific stream type used in the parser
pub type ParseResult<O, I, T> = Result<(O, Consumed<State<I>>), Consumed<ParseError<T>>>;

///A stream is a sequence of items that can be extracted one by one
pub trait Stream : Clone {
    type Item: Positioner;
    ///Takes a stream and removes its first item, yielding the item and the rest of the elements
    ///Returns `Err` when no more elements could be retrieved
    fn uncons(self) -> Result<(Self::Item, Self), ()>;
}

impl <'a> Stream for &'a str {
    type Item = char;
    fn uncons(self) -> Result<(char, &'a str), ()> {
        match self.chars().next() {
            Some(c) => Ok((c, &self[c.len_utf8()..])),
            None => Err(())
        }
    }
}

impl <'a, T> Stream for &'a [T]
    where T: Positioner {
    type Item = &'a T;
    fn uncons(self) -> Result<(&'a T, &'a [T]), ()> {
        if self.len() > 0 {
            Ok((&self[0], &self[1..]))
        }
        else {
            Err(())
        }
    }
}

#[derive(Clone, Debug)]
pub struct IteratorStream<I>(I)
    where I: Iterator + Clone;


///Converts an `Iterator` into a stream.
pub fn from_iter<I>(iter: I) -> IteratorStream<I>
    where I: Iterator + Clone {
    IteratorStream(iter)
}

impl <I: Iterator + Clone> Stream for IteratorStream<I>
    where I::Item: Positioner {
    type Item = <I as Iterator>::Item;
    fn uncons(mut self) -> Result<(I::Item, Self), ()> {
        match self.0.next() {
            Some(x) => Ok((x, self)),
            None => Err(())
        }
    }
}

pub trait Positioner {
    type Position: Clone + Ord + fmt::Display + fmt::Debug;
    fn start() -> Self::Position;
    fn update(&self, position: &mut Self::Position);
}
impl <'a, T> Positioner for &'a T
    where T: Positioner {
    type Position = <T as Positioner>::Position;
    fn start() -> <T as Positioner>::Position {
        <T as Positioner>::start()
    }
    fn update(&self, position: &mut <T as Positioner>::Position) {
        (*self).update(position)
    }
}

impl Positioner for char {
    type Position = SourcePosition;
    fn start() -> SourcePosition {
        SourcePosition::start()
    }
    fn update(&self, position: &mut SourcePosition) {
        position.update(self);
    }
}

///By implementing the `Parser` trait a type says that it can be used to parse an input stream into
///the type `Output`.
pub trait Parser {
    ///A type implementing the `Stream` trait which is the specific type
    ///that is parsed.
    type Input: Stream;
    ///The type which is returned when the parsing is successful.
    type Output;

    ///Entrypoint of the parser
    ///Takes some input and tries to parse it returning a `ParseResult`
    fn parse(&mut self, input: Self::Input) -> Result<(Self::Output, Self::Input), ParseError<<Self::Input as Stream>::Item>> {
        match self.parse_state(State::new(input)) {
            Ok((v, state)) => Ok((v, state.into_inner().input)),
            Err(error) => Err(error.into_inner())
        }
    }
    ///Parses using the state `input` by calling Stream::uncons one or more times
    ///On success returns `Ok((value, new_state))` on failure it returns `Err(error)`
    fn parse_state(&mut self, input: State<Self::Input>) -> ParseResult<Self::Output, Self::Input, <Self::Input as Stream>::Item>;
}
impl <'a, I, O, P: ?Sized> Parser for &'a mut P 
    where I: Stream, P: Parser<Input=I, Output=O> {
    type Input = I;
    type Output = O;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<O, I, I::Item> {
        (*self).parse_state(input)
    }
}
impl <I, O, P: ?Sized> Parser for Box<P> 
    where I: Stream, P: Parser<Input=I, Output=O> {
    type Input = I;
    type Output = O;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<O, I, I::Item> {
        (**self).parse_state(input)
    }
}

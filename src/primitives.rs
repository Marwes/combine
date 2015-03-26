use std::fmt;
use std::borrow::{Cow, IntoCow};
use std::error::Error as StdError;

///Struct which containing the current position
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

///Enum used to store information about an error that has occured
#[derive(Clone, PartialEq, Debug)]
pub enum Error {
    ///Error indicating an unexpected token has been encountered in the stream
    Unexpected(char),
    ///Error indicating that the parser expected something else
    Expected(Cow<'static, str>),
    ///Generic message
    Message(Cow<'static, str>)
}

///Enum used to indicate if a stream has had any elements consumed
#[derive(Clone, PartialEq, Debug, Copy)]
pub enum Consumed<T> {
    ///Constructor indicating that the parser has consumed elements
    Consumed(T),
    ///Constructor indicating that the parser did not consume any elements
    Empty(T)
}

impl <T> Consumed<T> {

    ///Returns true if the `self` is empty
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

    ///Converts the consumed state into the Consumed state
    pub fn as_consumed(self) -> Consumed<T> {
        Consumed::Consumed(self.into_inner())
    }

    ///Converts the consumed state into the Empty state
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
    pub fn combine<F, U, I>(self, f: F) -> ParseResult<U, I>
        where F: FnOnce(T) -> ParseResult<U, I> {
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
#[derive(Clone, Debug, PartialEq)]
pub struct ParseError {
    ///The position where the error occured
    pub position: SourcePosition,
    ///A vector containing specific information on what errors occured at `position`
    pub errors: Vec<Error>
}

impl ParseError {
    pub fn new(position: SourcePosition, error: Error) -> ParseError {
        ParseError { position: position, errors: vec![error] }
    }
    pub fn add_message<S>(&mut self, message: S)
        where S: IntoCow<'static, str> {
        self.add_error(Error::Message(message.into_cow()));
    }
    pub fn add_error(&mut self, message: Error) {
        //Don't add duplicate errors
        if self.errors.iter().find(|msg| **msg == message).is_none() {
            self.errors.push(message);
        }
    }
    pub fn set_expected(&mut self, message: Cow<'static, str>) {
        //Remove all other expected messages
        self.errors.retain(|e| match *e { Error::Expected(_) => false, _ => true });
        self.errors.push(Error::Expected(message));
    }
    pub fn merge(mut self, other: ParseError) -> ParseError {
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

impl StdError for ParseError {
    fn description(&self) -> &str { "parse error" }
}

impl fmt::Display for ParseError {
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
            .filter(|e| match **e { Error::Message(_) => true, _ => false } );
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
        }
    }
}

///The `State<I>` struct keeps track of the current position in the stream `I`
#[derive(Clone, PartialEq, Debug)]
pub struct State<I> {
    pub position: SourcePosition,
    pub input: I
}

impl <I: Stream> State<I> {
    pub fn new(input: I) -> State<I> {
        State { position: SourcePosition::start(), input: input }
    }

    pub fn as_empty(&self) -> State<I> {
        State { position: self.position, input: self.input.clone() }
    }

    ///`uncons` is the most general way of extracting and item from a stream
    ///It takes a function `f` as argument which should update the position
    ///according to the item that was extracted
    ///Usually you want to use `uncons_char` instead which works directly on character streams
    pub fn uncons<F>(self, f: F) -> ParseResult<<I as Stream>::Item, I>
        where F: FnOnce(&mut SourcePosition, &<I as Stream>::Item) {
        let State { mut position, input, .. } = self;
        match input.uncons() {
            Ok((c, input)) => {
                f(&mut position, &c);
                Ok((c, Consumed::Consumed(State { position: position, input: input })))
            }
            Err(()) => Err(Consumed::Empty(ParseError::new(position, Error::Message("End of input".into_cow()))))
        }
    }
}
impl <I: Stream<Item=char>> State<I> {
    ///Specialized uncons function for character streams which updates the position
    ///with no further action needed
    pub fn uncons_char(self) -> ParseResult<<I as Stream>::Item, I> {
        self.uncons(SourcePosition::update)
    }

}

///A type alias over the specific `Result` type used to indicated parser success/failure.
///`O` is the type that is output on success
///`I` is the specific stream type used in the parser
pub type ParseResult<O, I> = Result<(O, Consumed<State<I>>), Consumed<ParseError>>;

///A stream is a sequence of items that can be extracted one by one
pub trait Stream : Clone {
    type Item;
    ///Takes a stream and removes its first item, yielding the item and the rest of the elements
    ///Returns `Err` when no more elements could be retrieved
    fn uncons(self) -> Result<(Self::Item, Self), ()>;
}

impl <I: Iterator + Clone> Stream for I {
    type Item = <I as Iterator>::Item;
    fn uncons(mut self) -> Result<(I::Item, Self), ()> {
        match self.next() {
            Some(x) => Ok((x, self)),
            None => Err(())
        }
    }
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

impl <'a, T> Stream for &'a [T] {
    type Item = &'a T;
    fn uncons(self) -> Result<(&'a T, &'a [T]), ()> {
        match self {
            [ref x, rest..] => Ok((x, rest)),
            [] => Err(())
        }
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
    fn parse(&mut self, input: Self::Input) -> Result<(Self::Output, Self::Input), ParseError> {
        match self.parse_state(State::new(input)) {
            Ok((v, state)) => Ok((v, state.into_inner().input)),
            Err(error) => Err(error.into_inner())
        }
    }
    ///Parses using the state `input` by calling Stream::uncons one or more times
    ///On success returns `Ok((value, new_state))` on failure it returns `Err(error)`
    fn parse_state(&mut self, input: State<Self::Input>) -> ParseResult<Self::Output, Self::Input>;
}
impl <'a, I, O, P: ?Sized> Parser for &'a mut P 
    where I: Stream, P: Parser<Input=I, Output=O> {
    type Input = I;
    type Output = O;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<O, I> {
        (*self).parse_state(input)
    }
}
impl <I, O, P: ?Sized> Parser for Box<P> 
    where I: Stream, P: Parser<Input=I, Output=O> {
    type Input = I;
    type Output = O;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<O, I> {
        (**self).parse_state(input)
    }
}

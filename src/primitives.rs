use std::fmt;

#[derive(Clone, Copy, Show, PartialEq)]
pub struct SourcePosition {
    pub line: i32,
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

#[derive(Clone, PartialEq, Show)]
pub enum Error {
    Unexpected(char),
    Expected(String),
    Message(String)
}

#[derive(Clone, PartialEq, Show, Copy)]
pub enum Consumed {
    Consumed,
    Empty
}

impl Consumed {
    pub fn combine(&mut self, other: Consumed) {
        if other == Consumed::Consumed {
            *self = Consumed::Consumed;
        }
    }
}

#[derive(Clone, Show, PartialEq)]
pub struct ParseError {
    pub position: SourcePosition,
    pub consumed: Consumed,
    pub errors: Vec<Error>
}

impl ParseError {
    pub fn new(position: SourcePosition, consumed: Consumed, error: Error) -> ParseError {
        ParseError { position: position, consumed: consumed, errors: vec![error] }
    }
    pub fn add_message(&mut self, message: String) {
        self.add_error(Error::Message(message));
    }
    pub fn add_error(&mut self, message: Error) {
        //Don't add duplicate errors
        if self.errors.iter().find(|msg| **msg == message).is_none() {
            self.errors.push(message);
        }
    }
    pub fn merge(mut self, other: ParseError) -> ParseError {
        for message in other.errors.into_iter() {
            self.add_error(message);
        }
        self
    }
}

impl fmt::String for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(writeln!(f, "Parse error at {}", self.position));
        for error in self.errors.iter() {
            try!(writeln!(f, "{}", error));
        }
        Ok(())
    }
}
impl fmt::String for SourcePosition {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "line: {}, column: {}", self.line, self.column)
    }
}
impl fmt::String for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::Unexpected(c) => write!(f, "Unexpected character '{}'", c),
            Error::Expected(ref s) => write!(f, "Expected {}", s),
            Error::Message(ref msg) => write!(f, "{}", msg),
        }
    }
}

#[derive(Clone, PartialEq, Show)]
pub struct State<I> {
    pub position: SourcePosition,
    pub input: I,
    pub consumed: Consumed
}

impl <I: Stream> State<I> {
    fn new(input: I) -> State<I> {
        State { position: SourcePosition::start(), input: input, consumed: Consumed::Empty }
    }

    pub fn as_empty(&self) -> State<I> {
        State { position: self.position, input: self.input.clone(), consumed: Consumed::Empty }
    }

    fn uncons<F>(self, f: F) -> ParseResult<<I as Stream>::Item, I>
        where F: FnOnce(&mut SourcePosition, &<I as Stream>::Item) {
        let State { mut position, input, .. } = self;
        match input.uncons() {
            Ok((c, input)) => {
                f(&mut position, &c);
                Ok((c, State { position: position, input: input, consumed: Consumed::Consumed }))
            }
            Err(()) => Err(ParseError::new(position, Consumed::Empty, Error::Message("End of input".to_string())))
        }
    }
}
impl <I: Stream<Item=char>> State<I> {
    pub fn uncons_char(self) -> ParseResult<<I as Stream>::Item, I> {
        self.uncons(SourcePosition::update)
    }

}

pub type ParseResult<O, I> = Result<(O, State<I>), ParseError>;

pub trait Stream : Clone {
    type Item;
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
        match self.slice_shift_char() {
            Some(x) => Ok(x),
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

pub trait Parser {
    type Input: Stream;
    type Output;

    ///Entrypoint of the parser
    ///Takes some input and tries to parse it returning a `ParseResult`
    fn parse(&mut self, input: Self::Input) -> ParseResult<Self::Output, Self::Input> {
        self.parse_state(State::new(input))
    }
    ///Parses using the state `input` by calling Stream::uncons one or more times
    ///On success returns `Ok((value, new_state))` on failure it returns `Err(error)`
    fn parse_state(&mut self, input: State<Self::Input>) -> ParseResult<Self::Output, Self::Input>;
}
impl <'a, I, O, P> Parser for &'a mut P 
    where I: Stream, P: Parser<Input=I, Output=O> {
    type Input = I;
    type Output = O;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<O, I> {
        (*self).parse_state(input)
    }
}
impl <I, O, P> Parser for Box<P> 
    where I: Stream, P: Parser<Input=I, Output=O> {
    type Input = I;
    type Output = O;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<O, I> {
        (*self).parse_state(input)
    }
}

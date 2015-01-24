use std::fmt;


///Struct which containing the current position
#[derive(Clone, Copy, Show, Eq, PartialEq, Ord, PartialOrd)]
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
#[derive(Clone, PartialEq, Show)]
pub enum Error {
    ///Error indicating an unexpected token has been encountered in the stream
    Unexpected(char),
    ///Error indicating that the parser expected something else
    Expected(String),
    ///Generic message
    Message(String)
}

///Enum used to indicate if a stream has had any elements consumed
#[derive(Clone, PartialEq, Show, Copy)]
pub enum Consumed {
    ///Flag indicating that the parser has consumed elements
    Consumed,
    ///Flag indicating that the parser did not consume any elements
    Empty
}

impl Consumed {
    pub fn combine(&mut self, other: Consumed) {
        if other == Consumed::Consumed {
            *self = Consumed::Consumed;
        }
    }
}
///Struct which hold information about an error that occured at a specific position.
///Can hold multiple instances of `Error` if more that one error occured at the position.
#[derive(Clone, Show, PartialEq)]
pub struct ParseError {
    ///The position where the error occured
    pub position: SourcePosition,
    ///Flag indicating wether the parser had consumed any elements from the stream before the error
    ///occured
    pub consumed: Consumed,
    ///A vector containing specific information on what errors occured at `position`
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

///The `State<I>` struct keeps track of the current position in the stream `I`
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
                Ok((c, State { position: position, input: input, consumed: Consumed::Consumed }))
            }
            Err(()) => Err(ParseError::new(position, Consumed::Empty, Error::Message("End of input".to_string())))
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
pub type ParseResult<O, I> = Result<(O, State<I>), ParseError>;

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

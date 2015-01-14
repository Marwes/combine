#![allow(unstable)]

#[cfg(test)]
extern crate test;

use std::fmt;



#[derive(Clone, Copy, Show, PartialEq)]
pub struct SourcePosition {
    line: i32,
    column: i32
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
enum Error {
    Unexpected(char),
    Expected(String),
    Message(String)
}

#[derive(Clone, PartialEq, Show)]
enum Consumed {
    Consumed,
    Empty
}

#[derive(Clone, Show, PartialEq)]
pub struct ParseError {
    position: SourcePosition,
    consumed: Consumed,
    errors: Vec<Error>
}

impl ParseError {
    fn new(position: SourcePosition, consumed: Consumed, error: Error) -> ParseError {
        ParseError { position: position, consumed: consumed, errors: vec![error] }
    }
    pub fn add_message(&mut self, message: String) {
        self.add_error(Error::Message(message));
    }
    fn add_error(&mut self, message: Error) {
        //Don't add duplicate errors
        if self.errors.iter().find(|msg| **msg == message).is_none() {
            self.errors.push(message);
        }
    }
    fn merge(mut self, other: ParseError) -> ParseError {
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
    position: SourcePosition,
    input: I
}

impl <I: Stream> State<I> {
    fn new(input: I) -> State<I> {
        State { position: SourcePosition::start(), input: input }
    }
    fn uncons<F>(self, f: F) -> ParseResult<<I as Stream>::Item, I>
        where F: FnOnce(&mut SourcePosition, &<I as Stream>::Item) {
        let State { mut position, input } = self;
        match input.uncons() {
            Ok((c, input)) => {
                f(&mut position, &c);
                Ok((c, State { position: position, input: input }))
            }
            Err(()) => Err(ParseError::new(position, Consumed::Empty, Error::Message("End of input".to_string())))
        }
    }
    fn into_inner(self) -> I {
        self.input
    }
}
impl <I: Stream<Item=char>> State<I> {
    fn uncons_char(self) -> ParseResult<<I as Stream>::Item, I> {
        self.uncons(SourcePosition::update)
    }

}

pub type ParseResult<O, I> = Result<(O, State<I>), ParseError>;

pub trait Stream : Clone {
    type Item;
    fn uncons(self) -> Result<(<Self as Stream>::Item, Self), ()>;
}

impl <I: Iterator + Clone> Stream for I {
    type Item = <I as Iterator>::Item;
    fn uncons(mut self) -> Result<(<Self as Stream>::Item, Self), ()> {
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

    ///Parses using `input` by calling Stream::uncons one or more times
    ///On success returns `Ok((value, new_state))` on failure it returns `Err(error)`
    fn parse(&mut self, input: State<<Self as Parser>::Input>) -> ParseResult<<Self as Parser>::Output, <Self as Parser>::Input>;
    fn start_parse(&mut self, input: <Self as Parser>::Input) -> ParseResult<<Self as Parser>::Output, <Self as Parser>::Input> {
        self.parse(State::new(input))
    }
}
impl <'a, I, O, P> Parser for &'a mut P 
    where I: Stream, P: Parser<Input=I, Output=O> {
    type Input = I;
    type Output = O;
    fn parse(&mut self, input: State<I>) -> ParseResult<O, I> {
        (*self).parse(input)
    }
}

///Parses any character
pub fn any_char<'a, I>(input: State<I>) -> ParseResult<char, I>
    where I: Stream<Item=char> {
    input.uncons_char()
}

#[derive(Clone)]
pub struct ConsumeMany<P, F>(P, F)
    where P: Parser
        , F: FnMut(<P as Parser>::Output);
impl <P, F> Parser for ConsumeMany<P, F>
    where P: Parser
        , F: FnMut(<P as Parser>::Output) {
    type Input = <P as Parser>::Input;
    type Output = ();
    fn parse(&mut self, mut input: State<<P as Parser>::Input>) -> ParseResult<(), <P as Parser>::Input> {
        loop {
            match self.0.parse(input.clone()) {
                Ok((x, rest)) => {
                    (self.1)(x);
                    input = rest;
                }
                Err(err@ParseError { consumed: Consumed::Consumed, .. }) => return Err(err),
                Err(_) => break
            }
        }
        Ok(((), input))
    }
}

#[derive(Clone)]
pub struct Many<P> {
    parser: P
}
impl <P: Parser> Parser for Many<P> {
    type Input = <P as Parser>::Input;
    type Output = Vec<<P as Parser>::Output>;
    fn parse(&mut self, input: State<<P as Parser>::Input>) -> ParseResult<Vec<<P as Parser>::Output>, <P as Parser>::Input> {
        let mut result = Vec::new();
        let ((), input) = try!(ConsumeMany(&mut self.parser, |x| result.push(x)).parse(input));
        Ok((result, input))
    }
}
///Parses `p` zero or more times
pub fn many<P: Parser>(p: P) -> Many<P> {
    Many { parser: p }
}

#[derive(Clone)]
pub struct Many1<P>(P);
impl <P: Parser> Parser for Many1<P> {
    type Input = <P as Parser>::Input;
    type Output = Vec<<P as Parser>::Output>;
    fn parse(&mut self, input: State<<P as Parser>::Input>) -> ParseResult<Vec<<P as Parser>::Output>, <P as Parser>::Input> {
        let (first, input) = try!(self.0.parse(input));
        let mut result = vec![first];
        let ((), input) = try!(ConsumeMany(&mut self.0, |x| result.push(x)).parse(input));
        Ok((result, input))
    }
}

///Parses `p` one or more times
pub fn many1<P>(p: P) -> Many1<P>
    where P: Parser {
    Many1(p)
}

#[derive(Clone)]
pub struct Chars<P> {
    parser: P
}
impl <P> Parser for Chars<P>
    where P: Parser<Output=char> {
    type Input = <P as Parser>::Input;
    type Output = String;
    fn parse(&mut self, input: State<<P as Parser>::Input>) -> ParseResult<String, <P as Parser>::Input> {
        let mut result = String::new();
        let ((), input) = try!(ConsumeMany(&mut self.parser, |x| result.push(x)).parse(input));
        Ok((result, input))
    }
}
///Parses `p` zero or more times
pub fn chars<P>(p: P) -> Chars<P>
    where P: Parser<Output=char> {
    Chars { parser: p }
}
#[derive(Clone)]
pub struct Chars1<P> {
    parser: P
}
impl <P> Parser for Chars1<P>
    where P: Parser<Output=char> {
    type Input = <P as Parser>::Input;
    type Output = String;
    fn parse(&mut self, input: State<<P as Parser>::Input>) -> ParseResult<String, <P as Parser>::Input> {
        let (first, input) = try!(self.parser.parse(input));
        let mut result = String::new();
        result.push(first);
        let ((), input) = try!(ConsumeMany(&mut self.parser, |x| result.push(x)).parse(input));
        Ok((result, input))
    }
}
///Parses `p` zero or more times
pub fn chars1<P>(p: P) -> Chars1<P>
    where P: Parser<Output=char> {
    Chars1 { parser: p }
}

#[derive(Clone)]
pub struct SepBy<P, S> {
    parser: P,
    separator: S
}
impl <P, S> Parser for SepBy<P, S>
    where P: Parser, S: Parser<Input=<P as Parser>::Input> {

    type Input = <P as Parser>::Input;
    type Output = Vec<<P as Parser>::Output>;
    fn parse(&mut self, mut input: State<<P as Parser>::Input>) -> ParseResult<Vec<<P as Parser>::Output>, <P as Parser>::Input> {
        let mut result = Vec::new();
        match self.parser.parse(input.clone()) {
            Ok((x, rest)) => {
                result.push(x);
                input = rest;
            }
            Err(_) => return Ok((result, input))
        }
        let rest = (&mut self.separator)
            .with(&mut self.parser);
        let ((), input) = try!(ConsumeMany(rest, |x| result.push(x)).parse(input));
        Ok((result, input))
    }
}

///Parses `parser` zero or more time separated by `separator`
pub fn sep_by<P: Parser, S: Parser>(parser: P, separator: S) -> SepBy<P, S> {
    SepBy { parser: parser, separator: separator }
}


impl <'a, I: Stream, O> Parser for Box<FnMut(State<I>) -> ParseResult<O, I> + 'a> {
    type Input = I;
    type Output = O;
    fn parse(&mut self, input: State<I>) -> ParseResult<O, I> {
        self(input)
    }
}

#[derive(Clone)]
struct FnParser<I: Stream, O, F: FnMut(State<I>) -> ParseResult<O, I>>(F);

impl <I, O, F> Parser for FnParser<I, O, F>
    where I: Stream, F: FnMut(State<I>) -> ParseResult<O, I> {
    type Input = I;
    type Output = O;
    fn parse(&mut self, input: State<I>) -> ParseResult<O, I> {
        (self.0)(input)
    }
}

impl <I, O> Parser for fn (State<I>) -> ParseResult<O, I>
    where I: Stream {
    type Input = I;
    type Output = O;
    fn parse(&mut self, input: State<I>) -> ParseResult<O, I> {
        self(input)
    }
}

#[derive(Clone)]
pub struct Satisfy<I, Pred> { pred: Pred }

impl <'a, I, Pred> Parser for Satisfy<I, Pred>
    where I: Stream<Item=char>, Pred: FnMut(char) -> bool {

    type Input = I;
    type Output = char;
    fn parse(&mut self, input: State<I>) -> ParseResult<char, I> {
        match input.clone().uncons_char() {
            Ok((c, s)) => {
                if (self.pred)(c) { Ok((c, s)) }
                else {
                    Err(ParseError::new(input.position, Consumed::Empty, Error::Unexpected(c)))
                }
            }
            Err(err) => Err(err)
        }
    }
}

///Parses a character and succeeds depending on the result of `pred`
pub fn satisfy<I, Pred>(pred: Pred) -> Satisfy<I, Pred>
    where I: Stream, Pred: FnMut(char) -> bool {
    Satisfy { pred: pred }
}

///Parses whitespace
pub fn space<I>() -> Satisfy<I, fn (char) -> bool>
    where I: Stream {
    satisfy(CharExt::is_whitespace as fn (char) -> bool)
}

#[derive(Clone)]
pub struct StringP<'a, I> { s: &'a str }
impl <'a, 'b, I> Parser for StringP<'b, I>
    where I: Stream<Item=char> {
    type Input = I;
    type Output = &'b str;
    fn parse(&mut self, mut input: State<I>) -> ParseResult<&'b str, I> {
        let start = input.position;
        for (i, c) in self.s.chars().enumerate() {
            match input.uncons_char() {
                Ok((other, rest)) => {
                    if c != other {
                        let consumed = if i == 0 { Consumed::Empty } else { Consumed::Consumed };
                        return Err(ParseError::new(start, consumed, Error::Expected(self.s.to_string())));
                    }
                    input = rest;
                }
                Err(err) => return Err(err)
            }
        }
        Ok((self.s, input))
    }
}

///Parses the string `s`
pub fn string<I>(s: &str) -> StringP<I>
    where I: Stream {
    StringP { s: s }
}

#[derive(Clone)]
pub struct And<P1, P2>(P1, P2);
impl <I, A, B, P1, P2> Parser for And<P1, P2>
    where I: Stream, P1: Parser<Input=I, Output=A>, P2: Parser<Input=I, Output=B> {

    type Input = I;
    type Output = (A, B);
    fn parse(&mut self, input: State<I>) -> ParseResult<(A, B), I> {
        let (a, rest) = try!(self.0.parse(input));
        let (b, rest) = try!(self.1.parse(rest));
        Ok(((a, b), rest))
    }
}

#[derive(Clone)]
pub struct Optional<P>(P);
impl <P> Parser for Optional<P>
    where P: Parser {
    type Input = <P as Parser>::Input;
    type Output = Option<<P as Parser>::Output>;
    fn parse(&mut self, input: State<<P as Parser>::Input>) -> ParseResult<Option<<P as Parser>::Output>, <P as Parser>::Input> {
        match self.0.parse(input.clone()) {
            Ok((x, rest)) => Ok((Some(x), rest)),
            Err(_) => Ok((None, input))
        }
    }
}

///Returns `Some(value)` and `None` on parse failure (always succeeds)
pub fn optional<P>(parser: P) -> Optional<P> {
    Optional(parser)
}

///Parses a digit from a stream containing characters
pub fn digit<'a, I>(input: State<I>) -> ParseResult<char, I>
    where I: Stream<Item=char> {
    match input.clone().uncons_char() {
        Ok((c, rest)) => {
            if c.is_digit(10) { Ok((c, rest)) }
            else {
                Err(ParseError::new(input.position, Consumed::Empty, Error::Message("Expected digit".to_string())))
            }
        }
        Err(err) => Err(err)
    }
}

pub type Between<L, R, P> = Skip<With<L, P>, R>;
///Parses `open` followed by `parser` followed by `close`
///Returns the value of `parser`
pub fn between<I, L, R, P>(open: L, close: R, parser: P) -> Between<L, R, P>
    where I: Stream
        , L: Parser<Input=I>
        , R: Parser<Input=I>
        , P: Parser<Input=I> {
    open.with(parser).skip(close)
}

#[derive(Clone)]
pub struct With<P1, P2>(P1, P2) where P1: Parser, P2: Parser;
impl <I, P1, P2> Parser for With<P1, P2>
    where I: Stream, P1: Parser<Input=I>, P2: Parser<Input=I> {

    type Input = I;
    type Output = <P2 as Parser>::Output;
    fn parse(&mut self, input: State<I>) -> ParseResult<<Self as Parser>::Output, I> {
        let ((_, b), rest) = try!((&mut self.0).and(&mut self.1).parse(input));
        Ok((b, rest))
    }
}

#[derive(Clone)]
pub struct Skip<P1, P2>(P1, P2) where P1: Parser, P2: Parser;
impl <I, P1, P2> Parser for Skip<P1, P2>
    where I: Stream, P1: Parser<Input=I>, P2: Parser<Input=I> {

    type Input = I;
    type Output = <P1 as Parser>::Output;
    fn parse(&mut self, input: State<I>) -> ParseResult<<Self as Parser>::Output, I> {
        let ((a, _), rest) = try!((&mut self.0).and(&mut self.1).parse(input));
        Ok((a, rest))
    }
}

#[derive(Clone)]
pub struct Message<P>(P, String) where P: Parser;
impl <I, P> Parser for Message<P>
    where I: Stream, P: Parser<Input=I> {

    type Input = I;
    type Output = <P as Parser>::Output;
    fn parse(&mut self, input: State<I>) -> ParseResult<<Self as Parser>::Output, I> {
        match self.0.parse(input.clone()) {
            Ok(x) => Ok(x),
            Err(mut err) => {
                err.add_message(self.1.clone());
                Err(err)
            }
        }
    }
}

#[derive(Clone)]
pub struct Or<P1, P2>(P1, P2) where P1: Parser, P2: Parser;
impl <I, O, P1, P2> Parser for Or<P1, P2>
    where I: Stream, P1: Parser<Input=I, Output=O>, P2: Parser<Input=I, Output=O> {

    type Input = I;
    type Output = O;
    fn parse(&mut self, input: State<I>) -> ParseResult<O, I> {
        match self.0.parse(input.clone()) {
            Ok(x) => Ok(x),
            Err(err@ParseError { consumed: Consumed::Consumed, .. }) => Err(err),
            Err(error1) => {
                match self.1.parse(input) {
                    Ok(x) => Ok(x),
                    Err(error2) => Err(error1.merge(error2))
                }
            }
        }
    }
}

#[derive(Clone)]
pub struct Map<P, F, B>(P, F);
impl <I, A, B, P, F> Parser for Map<P, F, B>
    where I: Stream, P: Parser<Input=I, Output=A>, F: FnMut(A) -> B {

    type Input = I;
    type Output = B;
    fn parse(&mut self, input: State<I>) -> ParseResult<B, I> {
        match self.0.parse(input.clone()) {
            Ok((x, input)) => Ok(((self.1)(x), input)),
            Err(err) => Err(err)
        }
    }
}

#[derive(Clone)]
pub struct Chainl1<P, Op>(P, Op);
impl <'a, I, O, P, Op> Parser for Chainl1<P, Op>
    where I: Stream
        , P: Parser<Input=I, Output=O>
        , Op: Parser<Input=I, Output=Box<FnMut(O, O) -> O + 'a>> {

    type Input = I;
    type Output = O;
    fn parse(&mut self, input: State<I>) -> ParseResult<O, I> {
        let (mut l, mut input) = try!(self.0.parse(input));
        loop {
            //FIXME
            match (&mut self.1).and(&mut self.0).parse(input.clone()) {
                Ok(((mut op, r), rest)) => {
                    l = op(l, r);
                    input = rest;
                }
                Err(_) => break
            };

        }
        Ok((l, input))
    }
}
pub fn chainl1<'a, I, O, P, Op>(parser: P, op: Op) -> Chainl1<P, Op>
    where I: Stream
        , P: Parser<Input=I, Output=O>
        , Op: Parser<Input=I, Output=Box<FnMut(O, O) -> O + 'a>> {
    Chainl1(parser, op)
}

#[derive(Clone)]
pub struct Try<P>(P);
impl <I, O, P> Parser for Try<P>
    where I: Stream
        , P: Parser<Input=I, Output=O> {

    type Input = I;
    type Output = O;
    fn parse(&mut self, input: State<I>) -> ParseResult<O, I> {
        self.0.parse(input)
            .map_err(|mut err| {
                err.consumed = Consumed::Empty;
                err
            })
    }
}
///Try acts as `p` except it acts as if the parser hadn't consumed any input
///if `p` returns an error after consuming input
pub fn try<P>(p : P) -> Try<P>
    where P: Parser {
    Try(p)
}

pub trait ParserExt : Parser + Sized {
    ///Discards the value of the `self` parser and returns the value of `p`
    ///Fails if any of the parsers fails
    fn with<P2>(self, p: P2) -> With<Self, P2>
        where P2: Parser {
        With(self, p)
    }
    ///Discards the value of the `p` parser and returns the value of `self`
    ///Fails if any of the parsers fails
    fn skip<P2>(self, p: P2) -> Skip<Self, P2>
        where P2: Parser {
        Skip(self, p)
    }
    ///Parses with `self` followed by `p`
    ///Succeds if both parsers succed, otherwise fails
    ///Returns a tuple with both values on success
    fn and<P2>(self, p: P2) -> And<Self, P2>
        where P2: Parser {
        And(self, p)
    }
    ///Tries to parse using `self` and if it fails returns the result of parsing `p`
    fn or<P2>(self, p: P2) -> Or<Self, P2>
        where P2: Parser {
        Or(self, p)
    }
    ///Uses `f` to map over the parsed value
    fn map<F, B>(self, f: F) -> Map<Self, F, B>
        where F: FnMut(<Self as Parser>::Output) -> B {
        Map(self, f)
    }
    ///Parses with `self` and if it fails, adds the message msg to the error
    fn message(self, msg: String) -> Message<Self> {
        Message(self, msg)
    }
}

impl <P: Parser> ParserExt for P { }

#[cfg(test)]
mod tests {
    use super::*;
    use super::{Error, Consumed};
    

    fn integer<'a, I>(input: State<I>) -> ParseResult<i64, I>
        where I: Stream<Item=char> {
        let (s, input) = try!(chars1(digit as fn(_) -> _)
            .parse(input));
        let mut n = 0;
        for c in s.chars() {
            n = n * 10 + (c as i64 - '0' as i64);
        }
        Ok((n, input))
    }

    #[test]
    fn test_integer() {
        let result = (integer as fn(_) -> _).start_parse("123")
            .map(|(x, s)| (x, s.into_inner()));
        assert_eq!(result, Ok((123i64, "")));
    }
    #[test]
    fn list() {
        let mut p = sep_by(integer as fn(_) -> _, satisfy(|c| c == ','));
        let result = p.start_parse("123,4,56")
            .map(|(x, s)| (x, s.into_inner()));
        assert_eq!(result, Ok((vec![123, 4, 56], "")));
    }
    #[test]
    fn iterator() {
        let result = (integer as fn(_) -> _).start_parse("123".chars())
            .map(|(i, iter)| (i, iter.into_inner().next()));
        assert_eq!(result, Ok((123i64, None)));
    }
    #[test]
    fn field() {
        let word = chars(satisfy(|c| c.is_alphanumeric()));
        let word2 = chars(satisfy(|c| c.is_alphanumeric()));
        let spaces = many(space());
        let c_decl = word
            .skip(spaces.clone())
            .skip(satisfy(|c| c == ':'))
            .skip(spaces)
            .and(word2)
            .start_parse("x: int")
            .map(|(x, s)| (x, s.into_inner()));
        assert_eq!(c_decl, Ok((("x".to_string(), "int".to_string()), "")));
    }
    #[test]
    fn source_position() {
        let source =
r"
123
";
        let result = many(space())
            .with(integer as fn(_) -> _)
            .skip(many(space()))
            .start_parse(source);
        assert_eq!(result, Ok((123i64, State { position: SourcePosition { line: 3, column: 1 }, input: "" })));
    }

    #[derive(Show, PartialEq)]
    enum Expr {
        Id(String),
        Int(i64),
        Array(Vec<Expr>),
        Plus(Box<Expr>, Box<Expr>),
        Times(Box<Expr>, Box<Expr>),
    }
    fn expr(input: State<&str>) -> ParseResult<Expr, &str> {
        let word = chars1(satisfy(|c| c.is_alphabetic()));
        let integer = integer as fn (_) -> _;
        let array = between(satisfy(|c| c == '['), satisfy(|c| c == ']'), sep_by(expr as fn (_) -> _, satisfy(|c| c == ',')));
        let spaces = many(space());
        spaces.clone().with(
                word.map(Expr::Id)
                .or(integer.map(Expr::Int))
                .or(array.map(Expr::Array))
                .or(between(satisfy(|c| c == '('), satisfy(|c| c == ')'), term as fn (_) -> _))
            ).skip(spaces)
            .parse(input)
    }

    #[test]
    fn expression() {
        let result = sep_by(expr as fn (_) -> _, satisfy(|c| c == ','))
            .start_parse("int, 100, [[], 123]")
            .map(|(x, s)| (x, s.into_inner()));
        let exprs = vec![
              Expr::Id("int".to_string())
            , Expr::Int(100)
            , Expr::Array(vec![Expr::Array(vec![]), Expr::Int(123)])
        ];
        assert_eq!(result, Ok((exprs, "")));
    }

    #[test]
    fn expression_error() {
        let input =
r"
,123
";
        let result = (expr as fn (_) -> _)
            .start_parse(input);
        let err = ParseError {
            position: SourcePosition { line: 2, column: 1 },
            consumed: Consumed::Empty,
            errors: vec![Error::Unexpected(','), Error::Message("Expected digit".to_string())]
        };
        assert_eq!(result, Err(err));
    }

    fn term(input: State<&str>) -> ParseResult<Expr, &str> {

        let mul = satisfy(|c| c == '*')
            .map(|_| Box::new(|&mut:l, r| Expr::Times(Box::new(l), Box::new(r))) as Box<FnMut(_, _) -> _>);
        let add = satisfy(|c| c == '+')
            .map(|_| Box::new(|&mut:l, r| Expr::Plus(Box::new(l), Box::new(r))) as Box<FnMut(_, _) -> _>);
        let factor = chainl1(expr as fn (_) -> _, mul);
        chainl1(factor, add)
            .parse(input)
    }

    #[test]
    fn operators() {
        let input =
r"
1 * 2 + 3 * test
";
        let (result, _) = (term as fn (_) -> _)
            .start_parse(input)
            .unwrap();

        let e1 = Expr::Times(Box::new(Expr::Int(1)), Box::new(Expr::Int(2)));
        let e2 = Expr::Times(Box::new(Expr::Int(3)), Box::new(Expr::Id("test".to_string())));
        assert_eq!(result, Expr::Plus(Box::new(e1), Box::new(e2)));
    }


    fn follow(input: State<&str>) -> ParseResult<(), &str> {
        match input.clone().uncons_char() {
            Ok((c, _)) => {
                if c.is_alphanumeric() {
                    Err(ParseError::new(input.position, Consumed::Empty, Error::Unexpected(c)))
                }
                else {
                    Ok(((), input))
                }
            }
            Err(_) => Ok(((), input))
        }
    }
    #[test]
    fn error_position() {
        let mut p = string("let").skip(follow as fn (_) -> _).map(|x| x.to_string())
            .or(chars1(satisfy(|c| c.is_digit(10))));
        match p.start_parse("le123") {
            Ok(_) => assert!(false),
            Err(err) => assert_eq!(err.position, SourcePosition { line: 1, column: 1 })
        }
    }

    #[test]
    fn try_parser() {
        let mut p = try(string("let").skip(follow as fn (_) -> _)).map(|x| x.to_string())
            .or(chars1(satisfy(CharExt::is_alphabetic)));
        let result = p.start_parse("lex  ").map(|x| x.0);
        assert_eq!(result, Ok("lex".to_string()));
    }

static LONG_EXPR: &'static str =
r"(3 * 4) + 2 * 4 * test + 4 * aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
* (a + 2 * ((476128368 + i * (((3 * 4) + 2 * 4 * test + 4 * aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
* (a + 2 * ((476128368 + i * ((476128368 + 21476)+ 21476)) + 21476)) * 2123 * 214 + (476128368 + 21476) * hello + 42 + 21476)+ 21476)) + 21476)) * 2123 * 214 + (476128368 + 21476) * hello + 42 +
(3 * 4) + 2 * 4 * test + 4 * aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
* (a + 2 * ((476128368 + i * (((3 * 4) + 2 * 4 * test + 4 * aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
* (a + 2 * ((476128368 + i * ((476128368 + 21476)+ 21476)) + 21476)) * 2123 * 214 + (476128368 + 21476) * hello + 42
+ 21476)+ 21476)) + 21476)) * 2123 * 214 + (476128368 + 21476) * hello + 42";
    #[bench]
    fn bench_expression(bench: &mut ::test::Bencher) {

        let result = (term as fn (_) -> _)
            .start_parse(LONG_EXPR);
        assert!(result.is_ok()); 
        assert_eq!(result.unwrap().1.input, "");
        bench.iter(|| {
            let result = (term as fn (_) -> _)
                .start_parse(LONG_EXPR);
            ::test::black_box(result);
        })
    }
}

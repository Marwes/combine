#![allow(unstable)]


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

#[derive(Clone, Show, PartialEq)]
pub struct Error {
    position: SourcePosition,
    messages: Vec<String>
}

impl Error {
    pub fn add_message(&mut self, message: String) {
        self.messages.push(message);
    }
    fn merge(mut self, other: Error) -> Error {
        self.messages.extend(other.messages.into_iter());
        self
    }
}

fn error() -> Error {
    Error { position: SourcePosition { line: 0, column: 0 }, messages: Vec::new() }
}
fn message(s: String) -> Error {
    Error { position: SourcePosition { line: 0, column: 0 }, messages: vec![s] }
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
            Err(()) => Err(message("End of input".to_string()))
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

pub type ParseResult<O, I> = Result<(O, State<I>), Error>;


pub trait Stream {
    type Item;
    fn uncons(self) -> Result<(<Self as Stream>::Item, Self), ()>;
}

impl <I: Iterator> Stream for I {
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
    type Input: Clone + Stream;
    type Output;
    fn parse(&mut self, input: State<<Self as Parser>::Input>) -> ParseResult<<Self as Parser>::Output, <Self as Parser>::Input>;
    fn start_parse(&mut self, input: <Self as Parser>::Input) -> ParseResult<<Self as Parser>::Output, <Self as Parser>::Input> {
        self.parse(State::new(input))
    }
}
impl <'a, I, O, P> Parser for &'a mut P 
    where I: Clone + Stream, P: Parser<Input=I, Output=O> {
    type Input = I;
    type Output = O;
    fn parse(&mut self, input: State<I>) -> ParseResult<O, I> {
        (*self).parse(input)
    }
}

pub fn char<'a, I>(input: State<I>) -> ParseResult<char, I>
    where I: Stream<Item=char> + Clone {
    input.uncons_char()
}

pub struct ManyAppend<'a, O: 'a, P: Parser<Output=O> + 'a> {
    parser: P,
    vec: &'a mut Vec<O>
}
impl <'a, O, P: Parser<Output=O> + 'a> Parser for ManyAppend<'a, O, P> {
    type Input = <P as Parser>::Input;
    type Output = ();
    fn parse(&mut self, mut input: State<<P as Parser>::Input>) -> ParseResult<(), <P as Parser>::Input> {
        loop {
            match self.parser.parse(input.clone()) {
                Ok((x, rest)) => {
                    self.vec.push(x);
                    input = rest;
                }
                Err(_) => break
            }
        }
        Ok(((), input))
    }
}

pub fn many_append<'a, O, P: Parser<Output=O>>(parser: P, vec: &'a mut Vec<O>) -> ManyAppend<'a, O, P> {
    ManyAppend { parser: parser, vec: vec }
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
        let ((), input) = try!(many_append(&mut self.parser, &mut result).parse(input));
        Ok((result, input))
    }
}
pub fn many<P: Parser>(p: P) -> Many<P> {
    Many { parser: p }
}

pub struct Many1<P>(P);
impl <P: Parser> Parser for Many1<P> {
    type Input = <P as Parser>::Input;
    type Output = Vec<<P as Parser>::Output>;
    fn parse(&mut self, input: State<<P as Parser>::Input>) -> ParseResult<Vec<<P as Parser>::Output>, <P as Parser>::Input> {
        let (first, input) = try!(self.0.parse(input));
        let mut result = vec![first];
        let ((), input) = try!(many_append(&mut self.0, &mut result).parse(input));
        Ok((result, input))
    }
}
pub fn many1<P>(p: P) -> Many1<P>
    where P: Parser {
    Many1(p)
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
        let rest = FnParser(|input| {
            let mut env = Env::new(input);
            try!(env.with(&mut self.separator));
            let v = try!(env.with(&mut self.parser));
            env.result(v)
        });
        let ((), input) = try!(many_append(rest, &mut result).parse(input));
        Ok((result, input))
    }
}
pub fn sep_by<P: Parser, S: Parser>(parser: P, separator: S) -> SepBy<P, S> {
    SepBy { parser: parser, separator: separator }
}


impl <'a, I: Clone + Stream, O> Parser for Box<FnMut(State<I>) -> ParseResult<O, I> + 'a> {
    type Input = I;
    type Output = O;
    fn parse(&mut self, input: State<I>) -> ParseResult<O, I> {
        self(input)
    }
}

#[derive(Clone)]
struct FnParser<'a, I: Stream, O, F: FnMut(State<I>) -> ParseResult<O, I>>(F);

impl <'a, I, O, F> Parser for FnParser<'a, I, O, F>
    where I: Clone + Stream, F: FnMut(State<I>) -> ParseResult<O, I> {
    type Input = I;
    type Output = O;
    fn parse(&mut self, input: State<I>) -> ParseResult<O, I> {
        (self.0)(input)
    }
}

impl <'a, I, O> Parser for fn (State<I>) -> ParseResult<O, I>
    where I: Clone + Stream {
    type Input = I;
    type Output = O;
    fn parse(&mut self, input: State<I>) -> ParseResult<O, I> {
        self(input)
    }
}

#[derive(Clone)]
pub struct Satisfy<I, Pred> { pred: Pred }

impl <'a, I, Pred> Parser for Satisfy<I, Pred>
    where I: Stream<Item=char> + Clone, Pred: FnMut(char) -> bool {

    type Input = I;
    type Output = char;
    fn parse(&mut self, input: State<I>) -> ParseResult<char, I> {
        match input.uncons_char() {
            Ok((c, s)) => {
                if (self.pred)(c) { Ok((c, s)) }
                else {
                    Err(message(format!("{} did not satisfy", c)))
                }
            }
            Err(err) => Err(err)
        }
    }
}

pub fn satisfy<I, Pred>(pred: Pred) -> Satisfy<I, Pred>
    where I: Stream + Clone, Pred: FnMut(char) -> bool {
    Satisfy { pred: pred }
}

pub fn space<I>() -> Satisfy<I, fn (char) -> bool>
    where I: Stream + Clone {
    satisfy(CharExt::is_whitespace as fn (char) -> bool)
}

#[derive(Clone)]
pub struct StringP<'a, I> { s: &'a str }
impl <'a, 'b, I> Parser for StringP<'b, I>
    where I: Stream<Item=char> + Clone {
    type Input = I;
    type Output = &'b str;
    fn parse(&mut self, mut input: State<I>) -> ParseResult<&'b str, I> {
        for c in self.s.chars() {
            match input.uncons_char() {
                Ok((other, rest)) => {
                    if c != other { return Err(error());  }
                    input = rest;
                }
                Err(err) => return Err(err)
            }
        }
        Ok((self.s, input))
    }
}

pub fn string<I>(s: &str) -> StringP<I>
    where I: Stream + Clone {
    StringP { s: s }
}

#[derive(Clone)]
pub struct AndThen<P1, P2>(P1, P2);
impl <I, A, B, P1, P2> Parser for AndThen<P1, P2>
    where I: Clone + Stream, P1: Parser<Input=I, Output=A>, P2: Parser<Input=I, Output=B> {

    type Input = I;
    type Output = (A, B);
    fn parse(&mut self, input: State<I>) -> ParseResult<(A, B), I> {
        let (a, rest) = try!(self.0.parse(input));
        let (b, rest) = try!(self.1.parse(rest));
        Ok(((a, b), rest))
    }
}
pub fn and_then<P1, P2>(p1: P1, p2: P2) -> AndThen<P1, P2>
    where P1: Parser, P2: Parser {
    AndThen(p1, p2)
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
pub fn optional<P>(parser: P) -> Optional<P> {
    Optional(parser)
}


pub struct Env<I> {
    input: State<I>
}

impl <I: Clone + Stream> Env<I> {
    pub fn new(input: State<I>) -> Env<I> {
        Env { input: input }
    }
    
    pub fn with<P, O>(&mut self, mut parser: P) -> Result<O, Error>
        where P: Parser<Input=I, Output=O> {
        let (o, rest) = try!(parser.parse(self.input.clone()));
        self.input = rest;
        Ok(o)
    }

    pub fn result<O>(self, output: O) -> ParseResult<O, I> {
        Ok((output, self.input))
    }
}

pub fn digit<'a, I>(input: State<I>) -> ParseResult<char, I>
    where I: Stream<Item=char> + Clone {
    match input.uncons_char() {
        Ok((c, rest)) => {
            if c.is_digit(10) { Ok((c, rest)) }
            else {
                let mut error = error();
                error.add_message("Expected digit".to_string());
                Err(error)
            }
        }
        Err(err) => Err(err)
    }
}


pub struct With<P1, P2>(P1, P2) where P1: Parser, P2: Parser;
impl <I, P1, P2> Parser for With<P1, P2>
    where I: Clone + Stream, P1: Parser<Input=I>, P2: Parser<Input=I> {

    type Input = I;
    type Output = <P2 as Parser>::Output;
    fn parse(&mut self, input: State<I>) -> ParseResult<<Self as Parser>::Output, I> {
        let ((_, b), rest) = try!((&mut self.0).and_then(&mut self.1).parse(input));
        Ok((b, rest))
    }
}
pub struct Skip<P1, P2>(P1, P2) where P1: Parser, P2: Parser;
impl <I, P1, P2> Parser for Skip<P1, P2>
    where I: Clone + Stream, P1: Parser<Input=I>, P2: Parser<Input=I> {

    type Input = I;
    type Output = <P1 as Parser>::Output;
    fn parse(&mut self, input: State<I>) -> ParseResult<<Self as Parser>::Output, I> {
        let ((a, _), rest) = try!((&mut self.0).and_then(&mut self.1).parse(input));
        Ok((a, rest))
    }
}
pub struct Message<P>(P, String) where P: Parser;
impl <I, P> Parser for Message<P>
    where I: Clone + Stream, P: Parser<Input=I> {

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

pub struct Or<P1, P2>(P1, P2) where P1: Parser, P2: Parser;
impl <I, O, P1, P2> Parser for Or<P1, P2>
    where I: Clone + Stream, P1: Parser<Input=I, Output=O>, P2: Parser<Input=I, Output=O> {

    type Input = I;
    type Output = O;
    fn parse(&mut self, input: State<I>) -> ParseResult<O, I> {
        match self.0.parse(input.clone()) {
            Ok(x) => Ok(x),
            Err(error1) => {
                match self.1.parse(input) {
                    Ok(x) => Ok(x),
                    Err(error2) => Err(error1.merge(error2))
                }
            }
        }
    }
}
pub struct Map<P, F, B>(P, F);
impl <I, A, B, P, F> Parser for Map<P, F, B>
    where I: Clone + Stream, P: Parser<Input=I, Output=A>, F: FnMut(A) -> B {

    type Input = I;
    type Output = B;
    fn parse(&mut self, input: State<I>) -> ParseResult<B, I> {
        match self.0.parse(input.clone()) {
            Ok((x, input)) => Ok(((self.1)(x), input)),
            Err(err) => Err(err)
        }
    }
}
pub trait ParserExt : Parser + Sized {
    fn and_then<P2>(self, p: P2) -> AndThen<Self, P2>
        where P2: Parser {
        and_then(self, p)
    }
    fn with<P2>(self, p: P2) -> With<Self, P2>
        where P2: Parser {
        With(self, p)
    }
    fn skip<P2>(self, p: P2) -> Skip<Self, P2>
        where P2: Parser {
        Skip(self, p)
    }
    fn or<P2>(self, p: P2) -> Or<Self, P2>
        where P2: Parser {
        Or(self, p)
    }
    fn map<F, B>(self, p: F) -> Map<Self, F, B>
        where F: FnMut(<Self as Parser>::Output) -> B {
        Map(self, p)
    }
    fn message(self, s: String) -> Message<Self> {
        Message(self, s)
    }
}

impl <P: Parser> ParserExt for P { }

#[cfg(test)]
mod tests {
    use super::*;
    

    fn integer<'a, I>(input: State<I>) -> ParseResult<i64, I>
        where I: Stream<Item=char> + Clone {
        let (chars, input) = try!(many1(digit as fn(_) -> _)
            .parse(input));
        let mut n = 0;
        for &c in chars.iter() {
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
        let word = many(satisfy(|c| c.is_alphanumeric()));
        let word2 = many(satisfy(|c| c.is_alphanumeric()));
        let spaces = many(space());
        let c_decl = word
            .skip(spaces.clone())
            .skip(satisfy(|c| c == ':'))
            .skip(spaces)
            .and_then(word2)
            .start_parse("x: int")
            .map(|(x, s)| (x, s.into_inner()));
        assert_eq!(c_decl, Ok(((vec!['x'], vec!['i', 'n', 't']), "")));
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
    #[test]
    fn expression() {
        #[derive(Show, PartialEq)]
        enum Expr {
            Id(Vec<char>),
            Int(i64)
        }
        let word = many1(satisfy(|c| c.is_alphabetic()));
        let integer = integer as fn (_) -> _;
        let spaces = many(space());
        let expr = spaces.clone()
            .with(word.map(Expr::Id)
                .or(integer.map(Expr::Int)));

        let result = sep_by(expr, satisfy(|c| c == ','))
            .start_parse("int, 100")
            .map(|(x, s)| (x, s.into_inner()));
        assert_eq!(result, Ok((vec![Expr::Id(vec!['i', 'n', 't']), Expr::Int(100)], "")));
    }
}

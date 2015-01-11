#![allow(unstable)]

#[derive(Show, PartialEq)]
pub struct Error;

pub type ParseResult<O, I> = Result<(O, I), Error>;
pub type StrResult<'a, O> = ParseResult<O, &'a str>;


pub trait Parser {
    type Input: Clone;
    type Output;
    fn parse(&mut self, input: <Self as Parser>::Input) -> 
        Result<(<Self as Parser>::Output, <Self as Parser>::Input), Error>;
}
impl <'a, I, O, P> Parser for &'a mut P 
    where I: Clone, P: Parser<Input=I, Output=O> {
    type Input = I;
    type Output = O;
    fn parse(&mut self, input: I) -> Result<(O, I), Error> {
        (*self).parse(input)
    }
}

pub fn char<'a>(input: &'a str) -> ParseResult<char, &'a str> {
    match input.slice_shift_char() {
        Some(x) => Ok(x),
        None => Err(Error)
    }
}

pub struct Many<P> {
    parser: P
}
impl <P: Parser> Parser for Many<P> {
    type Input = <P as Parser>::Input;
    type Output = Vec<<P as Parser>::Output>;
    fn parse(&mut self, mut input: <P as Parser>::Input) -> Result<(Vec<<P as Parser>::Output>, <P as Parser>::Input), Error> {
        let mut result = Vec::new();
        loop {
            match self.parser.parse(input.clone()) {
                Ok((x, rest)) => {
                    result.push(x);
                    input = rest;
                }
                Err(_) => break
            }
        }
        Ok((result, input))
    }
}
pub fn many<P: Parser>(p: P) -> Many<P> {
    Many { parser: p }
}

pub fn many1<'a, P: Clone + 'a>(mut p: P) -> FnParser<'a, <P as Parser>::Input, Vec<<P as Parser>::Output>>
    where P: Parser {
    Box::new(move |&mut:input| {
        let (first, input) = try!(p.parse(input));
        let (mut rest, input) = try!(many(&mut p).parse(input));
        rest.insert(0, first);
        Ok((rest, input))
    })
}

pub struct SepBy<P, S> {
    parser: P,
    separator: S
}
impl <P, S> Parser for SepBy<P, S>
    where P: Parser, S: Parser<Input=<P as Parser>::Input> {

    type Input = <P as Parser>::Input;
    type Output = Vec<<P as Parser>::Output>;
    fn parse(&mut self, mut input: <P as Parser>::Input) -> Result<(Vec<<P as Parser>::Output>, <P as Parser>::Input), Error> {
        let mut result = Vec::new();
        match self.parser.parse(input.clone()) {
            Ok((x, rest)) => {
                result.push(x);
                input = rest;
            }
            Err(_) => return Ok((result, input))
        }
        loop {
            match self.separator.parse(input.clone()) {
                Ok((_, rest)) => input = rest,
                Err(e) => break
            }
            match self.parser.parse(input.clone()) {
                Ok((x, rest)) => {
                    result.push(x);
                    input = rest;
                }
                Err(e) => return Err(e)
            }
        }
        Ok((result, input))
    }
}
pub fn sep_by<P: Parser, S: Parser>(parser: P, separator: S) -> SepBy<P, S> {
    SepBy { parser: parser, separator: separator }
}

pub type FnParser<'a, I, O> = Box<FnMut(I) -> Result<(O, I), Error> + 'a>;

impl <'a, I: Clone, O> Parser for FnParser<'a, I, O> {
    type Input = I;
    type Output = O;
    fn parse(&mut self, input: I) -> Result<(O, I), Error> {
        self(input)
    }
}

impl <'a, I: Clone, O> Parser for fn (I) -> ParseResult<O, I> {
    type Input = I;
    type Output = O;
    fn parse(&mut self, input: I) -> ParseResult<O, I> {
        self(input)
    }
}

pub struct Satisfy<Pred> { pred: Pred }

impl <'a, Pred> Parser for Satisfy<Pred>
    where Pred: FnMut(char) -> bool {

    type Input = &'a str;
    type Output = char;
    fn parse(&mut self, input: &'a str) -> Result<(char, &'a str), Error> {
        match input.slice_shift_char() {
            Some((c, s)) => {
                if (self.pred)(c) { Ok((c, s)) }
                else { Err(Error) }
            }
            None => Err(Error)
        }
    }
}

pub fn satisfy<Pred>(pred: Pred) -> Satisfy<Pred>
    where Pred: FnMut(char) -> bool {
    Satisfy { pred: pred }
}

pub fn space() -> Satisfy<fn (char) -> bool> {
    satisfy(CharExt::is_whitespace as fn (char) -> bool)
}

pub struct StringP<'a> { s: &'a str }
impl <'a, 'b> Parser for StringP<'b> {
    type Input = &'a str;
    type Output = &'a str;
    fn parse(&mut self, input: &'a str) -> Result<(&'a str, &'a str), Error> {
        if input.starts_with(self.s) {
            let l = self.s.len();
            Ok((&input[..l], &input[l..]))
        }
        else {
            Err(Error)
        }
    }
}

pub fn string(s: &str) -> StringP {
    StringP { s: s }
}

pub struct AndThen<P1, P2>(P1, P2);
impl <I: Clone, A, B, P1, P2> Parser for AndThen<P1, P2>
    where P1: Parser<Input=I, Output=A>, P2: Parser<Input=I, Output=B> {

    type Input = I;
    type Output = (A, B);
    fn parse(&mut self, input: I) -> Result<((A, B), I), Error> {
        let (a, rest) = try!(self.0.parse(input));
        let (b, rest) = try!(self.1.parse(rest));
        Ok(((a, b), rest))
    }
}
pub fn and_then<P1, P2>(p1: P1, p2: P2) -> AndThen<P1, P2>
    where P1: Parser, P2: Parser {
    AndThen(p1, p2)
}

pub struct Optional<P>(P);
impl <P> Parser for Optional<P>
    where P: Parser {
    type Input = <P as Parser>::Input;
    type Output = Option<<P as Parser>::Output>;
    fn parse(&mut self, input: <P as Parser>::Input) -> Result<(Option<<P as Parser>::Output>, <P as Parser>::Input), Error> {
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
    input: I
}

impl <I: Clone> Env<I> {
    pub fn new(input: I) -> Env<I> {
        Env { input: input }
    }
    
    pub fn with<P, O>(&mut self, mut parser: P) -> Result<O, Error>
        where P: Parser<Input=I, Output=O> {
        let (o, rest) = try!(parser.parse(self.input.clone()));
        self.input = rest;
        Ok(o)
    }

    pub fn result<O>(self, output: O) -> Result<(O, I), Error> {
        Ok((output, self.input))
    }
}

pub fn digit<'a>(input: &'a str) -> ParseResult<char, &'a str> {
    match input.slice_shift_char() {
        Some(x) if x.0.is_digit(10) => Ok(x),
        Some((c, _)) => Err(Error),
        None => Err(Error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    

    fn integer<'a>(input: &'a str) -> Result<(i64, &'a str), Error> {
        let mut env = Env::new(input);
        let chars = try!(env.with(many(digit as fn(_) -> _)));
        let mut n = 0;
        for &c in chars.iter() {
            n = n * 10 + (c as i64 - '0' as i64);
        }
        env.result(n)
    }

    #[test]
    fn test_integer() {
        assert_eq!((integer as fn(_) -> _).parse("123"), Ok((123i64, "")));
    }
    #[test]
    fn list() {
        let mut p = sep_by(integer as fn(_) -> _, satisfy(|c| c == ','));
        assert_eq!(p.parse("123,4,56"), Ok((vec![123, 4, 56], "")));
    }
}

/*

impl Parser for  {
    type Input = ;
    type Output = ;
    fn parse(&mut self, input: ) -> Result<(, ), Error>;
}
 */

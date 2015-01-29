use primitives::{Consumed, Parser, ParseError, ParseResult, Error, State, Stream};
use combinator::{FnParser, many, Many, Map, ParserExt};

macro_rules! impl_char_parser {
    ($name: ident ($($ty_var: ident),*), $inner_type: ty) => {
    #[derive(Clone)]
    pub struct $name<I $(,$ty_var)*>($inner_type)
        where I: Stream<Item=char> $(, $ty_var : Parser<Input=I>)*;
    impl <I $(,$ty_var)*> Parser for $name<I $(,$ty_var)*>
        where I: Stream<Item=char> $(, $ty_var : Parser<Input=I>)* {
        type Input = I;
        type Output = <$inner_type as Parser>::Output;
        fn parse_state(&mut self, input: State<<Self as Parser>::Input>) -> ParseResult<<Self as Parser>::Output, <Self as Parser>::Input> {
            self.0.parse_state(input)
        }
    }
}
}

///Parses any character
pub fn any_char<I>(input: State<I>) -> ParseResult<char, I>
    where I: Stream<Item=char> {
    input.uncons_char()
}

#[derive(Clone)]
pub struct Satisfy<I, Pred> { pred: Pred }

impl <I, Pred> Parser for Satisfy<I, Pred>
    where I: Stream<Item=char>, Pred: FnMut(char) -> bool {

    type Input = I;
    type Output = char;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<char, I> {
        match input.clone().uncons_char() {
            Ok((c, s)) => {
                if (self.pred)(c) { Ok((c, s)) }
                else {
                    Err(Consumed::Empty(ParseError::new(input.position, Error::Unexpected(c))))
                }
            }
            Err(err) => Err(err)
        }
    }
}

///Parses a character and succeeds depending on the result of `pred`
///
/// ```
/// # extern crate "parser-combinators" as pc;
/// # use pc::*;
/// # fn main() {
/// let result = satisfy(|c| c == '!')
///     .parse("!")
///     .map(|x| x.0);
/// assert_eq!(result, Ok('!'));
/// # }
/// ```
pub fn satisfy<I, Pred>(pred: Pred) -> Satisfy<I, Pred>
    where I: Stream, Pred: FnMut(char) -> bool {
    Satisfy { pred: pred }
}

///Parses a digit from a stream containing characters
pub fn digit<I>() -> FnParser<I, char, fn (State<I>) -> ParseResult<char, I>>
        where I: Stream<Item=char> {
    fn digit_<I>(input: State<I>) -> ParseResult<char, I>
        where I: Stream<Item=char> {
        match input.clone().uncons_char() {
            Ok((c, rest)) => {
                if c.is_digit(10) { Ok((c, rest)) }
                else {
                    Err(Consumed::Empty(ParseError::new(input.position, Error::Message("Expected digit".to_string()))))
                }
            }
            Err(err) => Err(err)
        }
    }
    FnParser(digit_ as fn (_) -> _)
}

///Parses whitespace
pub fn space<I>() -> Satisfy<I, fn (char) -> bool>
    where I: Stream {
    satisfy(CharExt::is_whitespace as fn (char) -> bool)
}
impl_char_parser! { Spaces(), Many<Vec<()>, Map<Satisfy<I, fn (char) -> bool>, fn (char), ()>> }
///Skips over zero or more spaces
pub fn spaces<I>() -> Spaces<I>
    where I: Stream<Item=char> {
    Spaces(many(space().map(static_fn!((_, char) -> () { () }))))
}

///Parses a newline character
pub fn newline<I>() -> Satisfy<I, fn (char) -> bool>
    where I: Stream {
    satisfy(static_fn!((ch, char) -> bool { ch == '\n' }))
}

///Parses a tab character
pub fn tab<I>() -> Satisfy<I, fn (char) -> bool>
    where I: Stream {
    satisfy(static_fn!((ch, char) -> bool { ch == '\t'}))
}

#[derive(Clone)]
pub struct StringP<'a, I> { s: &'a str }
impl <'a, I> Parser for StringP<'a, I>
    where I: Stream<Item=char> {
    type Input = I;
    type Output = &'a str;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<&'a str, I> {
        let start = input.position;
        let mut input = Consumed::Empty(input);
        for (i, c) in self.s.chars().enumerate() {
            match input.combine(|input| input.uncons_char()) {
                Ok((other, rest)) => {
                    if c != other {
                        let error = ParseError::new(start, Error::Expected(self.s.to_string()));
                        return Err(if i == 0 { Consumed::Empty(error) } else { Consumed::Consumed(error) });
                    }
                    input = rest;
                }
                Err(error) => {
                    return error.combine(move |mut error| {
                        error.position = start;
                        Err(if i == 0 { Consumed::Empty(error) } else { Consumed::Consumed(error) })
                    })
                }
            }
        }
        Ok((self.s, input))
    }
}

///Parses the string `s`
///
/// ```
/// # extern crate "parser-combinators" as pc;
/// # use pc::*;
/// # fn main() {
/// let result = string("rust")
///     .parse("rust")
///     .map(|x| x.0);
/// assert_eq!(result, Ok("rust"));
/// # }
/// ```
pub fn string<I>(s: &str) -> StringP<I>
    where I: Stream {
    StringP { s: s }
}

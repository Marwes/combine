use primitives::{Consumed, Parser, ParseError, ParseResult, Error, State, Stream};
use combinator::{Expected, many, Many, Map, ParserExt, With};
use std::borrow::IntoCow;

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
    where I: Stream<Item=char>, Pred: FnMut(char) -> bool {
    Satisfy { pred: pred }
}

impl_char_parser! { Digit(), Expected<Satisfy<I, fn (char) -> bool>> }
///Parses a digit from a stream containing characters
pub fn digit<I>() -> Digit<I>
    where I: Stream<Item=char> {
    Digit(satisfy(static_fn!((c, char) -> bool { c.is_digit(10) }))
         .expected("digit"))
}

impl_char_parser! { Space(), Expected<Satisfy<I, fn (char) -> bool>> }
///Parses whitespace
pub fn space<I>() -> Space<I>
    where I: Stream<Item=char> {
    Space(satisfy(CharExt::is_whitespace as fn (char) -> bool)
        .expected("whitespace"))
}
impl_char_parser! { Spaces(), Expected<Many<Vec<()>, Map<Space<I>, fn (char)>>> }
///Skips over zero or more spaces
pub fn spaces<I>() -> Spaces<I>
    where I: Stream<Item=char> {
    Spaces(many(space().map(static_fn!((_, char) -> () { () })))
          .expected("whitespaces"))
}

impl_char_parser! { NewLine(), Expected<Satisfy<I, fn (char) -> bool>> }
///Parses a newline character
pub fn newline<I>() -> NewLine<I>
    where I: Stream<Item=char> {
    NewLine(satisfy(static_fn!((ch, char) -> bool { ch == '\n' }))
           .expected("lf newline"))
}

impl_char_parser! { CrLf(), Expected<With<Satisfy<I, fn (char) -> bool>, NewLine<I>>> }
///Parses carriage return and newline, returning the newline character.
pub fn crlf<I>() -> CrLf<I>
    where I: Stream<Item=char> {
    CrLf(satisfy(static_fn!((ch, char) -> bool { ch == '\r' }))
        .with(newline())
        .expected("crlf newline"))
}

impl_char_parser! { Tab(), Expected<Satisfy<I, fn (char) -> bool>> }
///Parses a tab character
pub fn tab<I>() -> Tab<I>
    where I: Stream<Item=char> {
    Tab(satisfy(static_fn!((ch, char) -> bool { ch == '\t' }))
       .expected("tab"))
}

impl_char_parser! { Upper(), Expected<Satisfy<I, fn (char) -> bool>> }
///Parses an uppercase letter
pub fn upper<I>() -> Upper<I>
    where I: Stream<Item=char> {
    Upper(satisfy(static_fn!((ch, char) -> bool { ch.is_uppercase()}))
         .expected("uppercase letter"))
}

impl_char_parser! { Lower(), Expected<Satisfy<I, fn (char) -> bool>> }
///Parses an uppercase letter
pub fn lower<I>() -> Lower<I>
    where I: Stream<Item=char> {
    Lower(satisfy(static_fn!((ch, char) -> bool { ch.is_lowercase() }))
         .expected("lowercase letter"))
}

impl_char_parser! { AlphaNum(), Expected<Satisfy<I, fn (char) -> bool>> }
///Parses either an alphabet letter or digit
pub fn alpha_num<I>() -> AlphaNum<I>
    where I: Stream<Item=char> {
    AlphaNum(satisfy(static_fn!((ch, char) -> bool { ch.is_alphanumeric() }))
            .expected("letter or digit"))
}

impl_char_parser! { Letter(), Expected<Satisfy<I, fn (char) -> bool>> }
///Parses an alphabet letter
pub fn letter<I>() -> Letter<I>
    where I: Stream<Item=char> {
    Letter(satisfy(static_fn!((ch, char) -> bool { ch.is_alphabetic() }))
          .expected("letter"))
}

impl_char_parser! { OctDigit(), Expected<Satisfy<I, fn (char) -> bool>> }
///Parses an octal digit
pub fn oct_digit<I>() -> OctDigit<I>
    where I: Stream<Item=char> {
    OctDigit(satisfy(static_fn!((ch, char) -> bool { ch.is_digit(8) }))
            .expected("octal digit"))
}

impl_char_parser! { HexDigit(), Expected<Satisfy<I, fn (char) -> bool>> }
///Parses a hexdecimal digit with uppercase and lowercase
pub fn hex_digit<I>() -> HexDigit<I>
    where I: Stream<Item=char> {
    HexDigit(satisfy(static_fn!((ch, char) -> bool { ch.is_digit(0x10) }))
            .expected("hexadecimal digit"))
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
                        let error = ParseError::new(start, Error::Expected(self.s.to_string().into_cow()));
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
    where I: Stream<Item=char> {
    StringP { s: s }
}


#[cfg(test)]
mod tests {
    use super::space;
    use primitives::{Error, Parser};
    use std::borrow::IntoCow;

    #[test]
    fn space_error() {
        let result = space()
            .parse("");
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().errors, vec![Error::Message("End of input".into_cow()), Error::Expected("whitespace".into_cow())]);

    }
}

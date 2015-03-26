use primitives::{Consumed, Parser, ParseError, ParseResult, Error, State, Stream};
use combinator::{Expected, skip_many, SkipMany, ParserExt, With};
use std::marker::PhantomData;
use std::borrow::IntoCow;

macro_rules! impl_char_parser {
    ($name: ident ($($ty_var: ident),*), $inner_type: ty) => {
    #[derive(Clone)]
    pub struct $name<I $(,$ty_var)*>($inner_type, PhantomData<I>)
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
pub struct Satisfy<I, Pred> { pred: Pred, _marker: PhantomData<I> }

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
/// # extern crate parser_combinators as pc;
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
    Satisfy { pred: pred, _marker: PhantomData }
}

impl_char_parser! { Digit(), Expected<Satisfy<I, fn (char) -> bool>> }
///Parses a digit from a stream containing characters
pub fn digit<I>() -> Digit<I>
    where I: Stream<Item=char> {
    Digit(satisfy(static_fn!((c, char) -> bool { c.is_digit(10) }))
         .expected("digit"), PhantomData)
}

impl_char_parser! { Space(), Expected<Satisfy<I, fn (char) -> bool>> }
///Parses whitespace
pub fn space<I>() -> Space<I>
    where I: Stream<Item=char> {
    Space(satisfy(char::is_whitespace as fn (char) -> bool)
        .expected("whitespace"), PhantomData)
}
impl_char_parser! { Spaces(), Expected<SkipMany<Space<I>>> }
///Skips over zero or more spaces
pub fn spaces<I>() -> Spaces<I>
    where I: Stream<Item=char> {
    Spaces(skip_many(space())
          .expected("whitespaces"), PhantomData)
}

impl_char_parser! { NewLine(), Expected<Satisfy<I, fn (char) -> bool>> }
///Parses a newline character
pub fn newline<I>() -> NewLine<I>
    where I: Stream<Item=char> {
    NewLine(satisfy(static_fn!((ch, char) -> bool { ch == '\n' }))
           .expected("lf newline"), PhantomData)
}

impl_char_parser! { CrLf(), Expected<With<Satisfy<I, fn (char) -> bool>, NewLine<I>>> }
///Parses carriage return and newline, returning the newline character.
pub fn crlf<I>() -> CrLf<I>
    where I: Stream<Item=char> {
    CrLf(satisfy(static_fn!((ch, char) -> bool { ch == '\r' }))
        .with(newline())
        .expected("crlf newline"), PhantomData)
}

impl_char_parser! { Tab(), Expected<Satisfy<I, fn (char) -> bool>> }
///Parses a tab character
pub fn tab<I>() -> Tab<I>
    where I: Stream<Item=char> {
    Tab(satisfy(static_fn!((ch, char) -> bool { ch == '\t' }))
       .expected("tab"), PhantomData)
}

impl_char_parser! { Upper(), Expected<Satisfy<I, fn (char) -> bool>> }
///Parses an uppercase letter
pub fn upper<I>() -> Upper<I>
    where I: Stream<Item=char> {
    Upper(satisfy(static_fn!((ch, char) -> bool { ch.is_uppercase()}))
         .expected("uppercase letter"), PhantomData)
}

impl_char_parser! { Lower(), Expected<Satisfy<I, fn (char) -> bool>> }
///Parses an lowercase letter
pub fn lower<I>() -> Lower<I>
    where I: Stream<Item=char> {
    Lower(satisfy(static_fn!((ch, char) -> bool { ch.is_lowercase() }))
         .expected("lowercase letter"), PhantomData)
}

impl_char_parser! { AlphaNum(), Expected<Satisfy<I, fn (char) -> bool>> }
///Parses either an alphabet letter or digit
pub fn alpha_num<I>() -> AlphaNum<I>
    where I: Stream<Item=char> {
    AlphaNum(satisfy(static_fn!((ch, char) -> bool { ch.is_alphanumeric() }))
            .expected("letter or digit"), PhantomData)
}

impl_char_parser! { Letter(), Expected<Satisfy<I, fn (char) -> bool>> }
///Parses an alphabet letter
pub fn letter<I>() -> Letter<I>
    where I: Stream<Item=char> {
    Letter(satisfy(static_fn!((ch, char) -> bool { ch.is_alphabetic() }))
          .expected("letter"), PhantomData)
}

impl_char_parser! { OctDigit(), Expected<Satisfy<I, fn (char) -> bool>> }
///Parses an octal digit
pub fn oct_digit<I>() -> OctDigit<I>
    where I: Stream<Item=char> {
    OctDigit(satisfy(static_fn!((ch, char) -> bool { ch.is_digit(8) }))
            .expected("octal digit"), PhantomData)
}

impl_char_parser! { HexDigit(), Expected<Satisfy<I, fn (char) -> bool>> }
///Parses a hexdecimal digit with uppercase and lowercase
pub fn hex_digit<I>() -> HexDigit<I>
    where I: Stream<Item=char> {
    HexDigit(satisfy(static_fn!((ch, char) -> bool { ch.is_digit(0x10) }))
            .expected("hexadecimal digit"), PhantomData)
}


#[derive(Clone)]
pub struct String<I>(&'static str, PhantomData<I>);
impl <I> Parser for String<I>
    where I: Stream<Item=char> {
    type Input = I;
    type Output = &'static str;
    fn parse_state(&mut self, mut input: State<I>) -> ParseResult<&'static str, I> {
        let start = input.position;
        let mut consumed = false;
        for c in self.0.chars() {
            match input.uncons_char() {
                Ok((other, rest)) => {
                    if c != other {
                        let error = ParseError::new(start, Error::Expected(self.0.into_cow()));
                        return Err(if consumed { Consumed::Consumed(error) } else { Consumed::Empty(error) })
                    }
                    consumed = true;
                    input = rest.into_inner();
                }
                Err(error) => {
                    return error.combine(|mut error| {
                        error.position = start;
                        Err(if consumed { Consumed::Consumed(error) } else { Consumed::Empty(error) })
                    })
                }
            }
        }
        Ok((self.0, if consumed { Consumed::Consumed(input) } else { Consumed::Empty(input) }))
    }
}

///Parses the string `s`
///
/// ```
/// # extern crate parser_combinators as pc;
/// # use pc::*;
/// # fn main() {
/// let result = string("rust")
///     .parse("rust")
///     .map(|x| x.0);
/// assert_eq!(result, Ok("rust"));
/// # }
/// ```
pub fn string<I>(s: &'static str) -> String<I>
    where I: Stream<Item=char> {
    String(s, PhantomData)
}


#[cfg(test)]
mod tests {
    use super::*;
    use primitives::{Error, Parser, SourcePosition};
    use std::borrow::IntoCow;

    #[test]
    fn space_error() {
        let result = space()
            .parse("");
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().errors, vec![Error::Message("End of input".into_cow()), Error::Expected("whitespace".into_cow())]);

    }

    #[test]
    fn string_consumed() {
        let result = string("a").parse("b");
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().position, SourcePosition { line: 1, column: 1 });
    }
}

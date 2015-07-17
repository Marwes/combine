use primitives::{Consumed, Parser, ParseError, Error, State, Stream};
use combinator::{Expected, satisfy, Satisfy, skip_many, SkipMany, token, Token, ParserExt, With};
use std::marker::PhantomData;

pub type ParseResult<O, I> = ::primitives::ParseResult<O, I, char>;

macro_rules! impl_char_parser {
    ($name: ident ($($ty_var: ident),*), $inner_type: ty) => {
    #[derive(Clone)]
    pub struct $name<I $(,$ty_var)*>($inner_type, PhantomData<fn (I) -> I>)
        where I: Stream<Item=char> $(, $ty_var : Parser<Input=I>)*;
    impl <I $(,$ty_var)*> Parser for $name<I $(,$ty_var)*>
        where I: Stream<Item=char> $(, $ty_var : Parser<Input=I>)* {
        type Input = I;
        type Output = <$inner_type as Parser>::Output;
        fn parse_lazy(&mut self, input: State<<Self as Parser>::Input>) -> ParseResult<<Self as Parser>::Output, <Self as Parser>::Input> {
            self.0.parse_lazy(input)
        }
        fn add_error(&mut self, errors: &mut ParseError<<Self::Input as Stream>::Item>) {
            self.0.add_error(errors)
        }
    }
}
}

///Parses a character and succeeds if the characther is equal to `c`
///
/// ```
/// # extern crate combine as pc;
/// # use pc::*;
/// # fn main() {
/// let result = char('!')
///     .parse("!")
///     .map(|x| x.0);
/// assert_eq!(result, Ok('!'));
/// # }
/// ```
pub fn char<I>(c: char) -> Token<I>
    where I: Stream<Item=char> {
    token(c)
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
    let f: fn (char) -> bool = char::is_whitespace;
    Space(satisfy(f)
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
    fn parse_lazy(&mut self, mut input: State<I>) -> ParseResult<&'static str, I> {
        let start = input.position;
        let mut consumed = false;
        for c in self.0.chars() {
            match input.uncons() {
                Ok((other, rest)) => {
                    if c != other {
                        return Err(if consumed {
                            let errors = vec![Error::Unexpected(other), Error::Expected(self.0.into())];
                            let error = ParseError::from_errors(start, errors);
                            Consumed::Consumed(error)
                        } else {
                            Consumed::Empty(ParseError::empty(start))
                        })
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
    fn add_error(&mut self, errors: &mut ParseError<<Self::Input as Stream>::Item>) {
        errors.add_error(Error::Expected(self.0.into()));
    }
}

///Parses the string `s`
///
/// ```
/// # extern crate combine as pc;
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
    use primitives::{Error, ParseError, Parser, SourcePosition};

    #[test]
    fn space_error() {
        let result = space()
            .parse("");
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().errors, vec![Error::Message("End of input".into()), Error::Expected("whitespace".into())]);

    }

    #[test]
    fn string_consumed() {
        let result = string("a").parse("b");
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().position, SourcePosition { line: 1, column: 1 });
    }

    #[test]
    fn string_error() {
        let result = string("abc").parse("bc");
        assert_eq!(result, Err(ParseError {
            position: SourcePosition { line: 1, column: 1 },
            errors: vec![Error::Unexpected('b'), Error::Expected("abc".into())]
        }));
    }
}

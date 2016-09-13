use primitives::{Consumed, Parser, ParseError, ConsumedResult, Error, Stream};
use combinator::{Expected, satisfy, Satisfy, skip_many, SkipMany, token, Token, With};
use std::marker::PhantomData;

/// Parses a character and succeeds if the character is equal to `c`
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::char::char;
/// # fn main() {
/// let result = char('!')
///     .parse("!")
///     .map(|x| x.0);
/// assert_eq!(result, Ok('!'));
/// # }
/// ```
#[inline(always)]
pub fn char<I>(c: char) -> Token<I>
    where I: Stream<Item = char>
{
    token(c)
}

impl_token_parser! { Digit(), char, Expected<Satisfy<I, fn (char) -> bool>> }
/// Parses a digit from a stream containing characters
#[inline(always)]
pub fn digit<I>() -> Digit<I>
    where I: Stream<Item = char>
{
    Digit(satisfy(static_fn!((c, char) -> bool { c.is_digit(10) })).expected("digit"),
          PhantomData)
}

impl_token_parser! { Space(), char, Expected<Satisfy<I, fn (char) -> bool>> }
/// Parses whitespace
#[inline(always)]
pub fn space<I>() -> Space<I>
    where I: Stream<Item = char>
{
    let f: fn(char) -> bool = char::is_whitespace;
    Space(satisfy(f).expected("whitespace"), PhantomData)
}
impl_token_parser! { Spaces(), char, Expected<SkipMany<Space<I>>> }
/// Skips over zero or more spaces
#[inline(always)]
pub fn spaces<I>() -> Spaces<I>
    where I: Stream<Item = char>
{
    Spaces(skip_many(space()).expected("whitespaces"), PhantomData)
}

impl_token_parser! { Newline(), char, Expected<Satisfy<I, fn (char) -> bool>> }
/// Parses a newline character
#[inline(always)]
pub fn newline<I>() -> Newline<I>
    where I: Stream<Item = char>
{
    Newline(satisfy(static_fn!((ch, char) -> bool { ch == '\n' })).expected("lf newline"),
            PhantomData)
}

impl_token_parser! { CrLf(), char, Expected<With<Satisfy<I, fn (char) -> bool>, Newline<I>>> }
/// Parses carriage return and newline, returning the newline character.
#[inline(always)]
pub fn crlf<I>() -> CrLf<I>
    where I: Stream<Item = char>
{
    CrLf(satisfy(static_fn!((ch, char) -> bool { ch == '\r' }))
             .with(newline())
             .expected("crlf newline"),
         PhantomData)
}

impl_token_parser! { Tab(), char, Expected<Satisfy<I, fn (char) -> bool>> }
/// Parses a tab character
#[inline(always)]
pub fn tab<I>() -> Tab<I>
    where I: Stream<Item = char>
{
    Tab(satisfy(static_fn!((ch, char) -> bool { ch == '\t' })).expected("tab"),
        PhantomData)
}

impl_token_parser! { Upper(), char, Expected<Satisfy<I, fn (char) -> bool>> }
/// Parses an uppercase letter
#[inline(always)]
pub fn upper<I>() -> Upper<I>
    where I: Stream<Item = char>
{
    Upper(satisfy(static_fn!((ch, char) -> bool { ch.is_uppercase()})).expected("uppercase letter"),
          PhantomData)
}

impl_token_parser! { Lower(), char, Expected<Satisfy<I, fn (char) -> bool>> }
/// Parses an lowercase letter
#[inline(always)]
pub fn lower<I>() -> Lower<I>
    where I: Stream<Item = char>
{
    Lower(satisfy(static_fn!((ch, char) -> bool { ch.is_lowercase() }))
              .expected("lowercase letter"),
          PhantomData)
}

impl_token_parser! { AlphaNum(), char, Expected<Satisfy<I, fn (char) -> bool>> }
/// Parses either an alphabet letter or digit
#[inline(always)]
pub fn alpha_num<I>() -> AlphaNum<I>
    where I: Stream<Item = char>
{
    AlphaNum(satisfy(static_fn!((ch, char) -> bool { ch.is_alphanumeric() }))
                 .expected("letter or digit"),
             PhantomData)
}

impl_token_parser! { Letter(), char, Expected<Satisfy<I, fn (char) -> bool>> }
/// Parses an alphabet letter
#[inline(always)]
pub fn letter<I>() -> Letter<I>
    where I: Stream<Item = char>
{
    Letter(satisfy(static_fn!((ch, char) -> bool { ch.is_alphabetic() })).expected("letter"),
           PhantomData)
}

impl_token_parser! { OctDigit(), char, Expected<Satisfy<I, fn (char) -> bool>> }
/// Parses an octal digit
#[inline(always)]
pub fn oct_digit<I>() -> OctDigit<I>
    where I: Stream<Item = char>
{
    OctDigit(satisfy(static_fn!((ch, char) -> bool { ch.is_digit(8) })).expected("octal digit"),
             PhantomData)
}

impl_token_parser! { HexDigit(), char, Expected<Satisfy<I, fn (char) -> bool>> }
/// Parses a hexdecimal digit with uppercase and lowercase
#[inline(always)]
pub fn hex_digit<I>() -> HexDigit<I>
    where I: Stream<Item = char>
{
    HexDigit(satisfy(static_fn!((ch, char) -> bool { ch.is_digit(0x10) }))
                 .expected("hexadecimal digit"),
             PhantomData)
}


#[derive(Clone)]
pub struct Str<I>(&'static str, PhantomData<I>);
impl<I> Parser for Str<I>
    where I: Stream<Item = char>
{
    type Input = I;
    type Output = &'static str;
    #[inline]
    fn parse_lazy(&mut self, mut input: I) -> ConsumedResult<&'static str, I> {
        let start = input.position();
        let mut consumed = false;
        for c in self.0.chars() {
            match ::primitives::uncons(input) {
                Ok((other, rest)) => {
                    if c != other {
                        return Err(if consumed {
                                let errors = vec![Error::Unexpected(other.into()),
                                                  Error::Expected(self.0.into())];
                                let error = ParseError::from_errors(start, errors);
                                Consumed::Consumed(error)
                            } else {
                                Consumed::Empty(ParseError::empty(start))
                            })
                            .into();
                    }
                    consumed = true;
                    input = rest.into_inner();
                }
                Err(error) => {
                    return error.combine_consumed(|mut error| {
                        error.position = start;
                        Err(if consumed {
                                Consumed::Consumed(error)
                            } else {
                                Consumed::Empty(error)
                            })
                            .into()
                    })
                }
            }
        }
        Ok((self.0,
            if consumed {
                Consumed::Consumed(input)
            } else {
                Consumed::Empty(input)
            }))
            .into()
    }
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        errors.add_error(Error::Expected(self.0.into()));
    }
}

/// Parses the string `s`
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::char::string;
/// # fn main() {
/// let result = string("rust")
///     .parse("rust")
///     .map(|x| x.0);
/// assert_eq!(result, Ok("rust"));
/// # }
/// ```
#[inline(always)]
pub fn string<I>(s: &'static str) -> Str<I>
    where I: Stream<Item = char>
{
    Str(s, PhantomData)
}


#[cfg(test)]
mod tests {
    use super::*;
    use primitives::{Error, ParseError, Parser, SourcePosition, State};

    #[test]
    fn space_error() {
        let result = space().parse("");
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().errors,
                   vec![Error::end_of_input(), Error::Expected("whitespace".into())]);

    }

    #[test]
    fn string_consumed() {
        let result = string("a").parse(State::new("b"));
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().position,
                   SourcePosition {
                       line: 1,
                       column: 1,
                   });
    }

    #[test]
    fn string_error() {
        let result = string("abc").parse(State::new("bc"));
        assert_eq!(result,
                   Err(ParseError {
                       position: SourcePosition {
                           line: 1,
                           column: 1,
                       },
                       errors: vec![Error::Unexpected('b'.into()), Error::Expected("abc".into())],
                   }));
    }
}

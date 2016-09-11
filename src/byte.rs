extern crate ascii;

use std::marker::PhantomData;

use self::ascii::AsciiChar;

use combinator::{Expected, satisfy, Satisfy, skip_many, SkipMany, token, Token, With};
use primitives::{Consumed, ConsumedResult, Error, Info, Parser, ParseError, Stream};

/// Parses a character and succeeds if the character is equal to `c`
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::byte::byte;
/// # fn main() {
/// let result = byte(b'!')
///     .parse(&b"!"[..])
///     .map(|x| x.0);
/// assert_eq!(result, Ok(b'!'));
/// # }
/// ```
#[inline(always)]
pub fn byte<I>(c: u8) -> Token<I>
    where I: Stream<Item = u8>
{
    token(c)
}

impl_token_parser! { Digit(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }

macro_rules! byte_parser {
    ($name: ident, $ty : ident, $f : ident) => ({
        let f = static_fn!((c, u8) -> bool {
            AsciiChar::from(c).map(|c| c.$f()).unwrap_or(false)
        });
        $ty(satisfy(f).expected(stringify!($name)), PhantomData)
    })
}

/// Parses a digit from a stream containing characters
#[inline(always)]
pub fn digit<I>() -> Digit<I>
    where I: Stream<Item = u8>
{
    byte_parser!(digit, Digit, is_digit)
}

impl_token_parser! { Space(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }

/// Parses whitespace
#[inline(always)]
pub fn space<I>() -> Space<I>
    where I: Stream<Item = u8>
{
    byte_parser!(space, Space, is_whitespace)
}

impl_token_parser! { Spaces(), u8, Expected<SkipMany<Space<I>>> }
/// Skips over zero or more spaces
#[inline(always)]
pub fn spaces<I>() -> Spaces<I>
    where I: Stream<Item = u8>
{
    Spaces(skip_many(space()).expected("whitespaces"), PhantomData)
}

impl_token_parser! { Newline(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }

/// Parses a newline character
#[inline(always)]
pub fn newline<I>() -> Newline<I>
    where I: Stream<Item = u8>
{
    Newline(satisfy(static_fn!((ch, u8) -> bool { ch == b'\n' })).expected("lf newline"),
            PhantomData)
}

impl_token_parser! { CrLf(), u8, Expected<With<Satisfy<I, fn (u8) -> bool>, Newline<I>>> }

/// Parses carriage return and newline, returning the newline character.
#[inline(always)]
pub fn crlf<I>() -> CrLf<I>
    where I: Stream<Item = u8>
{
    CrLf(satisfy(static_fn!((ch, u8) -> bool { ch == b'\r' }))
             .with(newline())
             .expected("crlf newline"),
         PhantomData)
}

impl_token_parser! { Tab(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }
/// Parses a tab character
#[inline(always)]
pub fn tab<I>() -> Tab<I>
    where I: Stream<Item = u8>
{
    Tab(satisfy(static_fn!((ch, u8) -> bool { ch == b'\t' })).expected("tab"),
        PhantomData)
}

impl_token_parser! { Upper(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }
/// Parses an uppercase letter
#[inline(always)]
pub fn upper<I>() -> Upper<I>
    where I: Stream<Item = u8>
{
    byte_parser!(upper, Upper, is_uppercase)
}

impl_token_parser! { Lower(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }
/// Parses an lowercase letter
#[inline(always)]
pub fn lower<I>() -> Lower<I>
    where I: Stream<Item = u8>
{
    byte_parser!(lower, Lower, is_lowercase)
}

impl_token_parser! { AlphaNum(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }
/// Parses either an alphabet letter or digit
#[inline(always)]
pub fn alpha_num<I>() -> AlphaNum<I>
    where I: Stream<Item = u8>
{
    byte_parser!(alpha_num, AlphaNum, is_alphanumeric)
}

impl_token_parser! { Letter(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }
/// Parses an alphabet letter
#[inline(always)]
pub fn letter<I>() -> Letter<I>
    where I: Stream<Item = u8>
{
    byte_parser!(letter, Letter, is_alphabetic)
}

impl_token_parser! { HexDigit(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }
/// Parses a hexdecimal digit with uppercase and lowercase
#[inline(always)]
pub fn hex_digit<I>() -> HexDigit<I>
    where I: Stream<Item = u8>
{
    byte_parser!(hex_digit, HexDigit, is_hex)
}

#[derive(Clone)]
pub struct Bytes<I>(&'static [u8], PhantomData<I>);
impl<'a, I> Parser for Bytes<I>
    where I: Stream<Item = u8, Range = &'a [u8]>
{
    type Input = I;
    type Output = &'static [u8];
    #[inline]
    fn parse_lazy(&mut self, mut input: I) -> ConsumedResult<&'static [u8], I> {
        let start = input.position();
        let mut consumed = false;
        for &c in self.0 {
            match ::primitives::uncons(input) {
                Ok((other, rest)) => {
                    if c != other {
                        return Err(if consumed {
                                let errors = vec![Error::Unexpected(Info::Token(other)),
                                                  Error::Expected(Info::Range(self.0))];
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
                    return error.combine_fast(|mut error| {
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
        errors.add_error(Error::Expected(Info::Range(self.0)));
    }
}

/// Parses the bytes `s`. If you have a stream implementing `RangeStream` such as `&[u8]` you can
/// also use the `range` parser which may be more efficient.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::byte::bytes;
/// # fn main() {
/// let result = bytes(b"rust")
///     .parse(&b"rust"[..])
///     .map(|x| x.0);
/// assert_eq!(result, Ok(&b"rust"[..]));
/// # }
/// ```
#[inline(always)]
pub fn bytes<'a, I>(s: &'static [u8]) -> Bytes<I>
    where I: Stream<Item = u8, Range = &'a [u8]>
{
    Bytes(s, PhantomData)
}

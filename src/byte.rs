extern crate ascii;

use std::marker::PhantomData;

use self::ascii::AsciiChar;

use combinator::{Expected, satisfy, Satisfy, skip_many, SkipMany, token, Token, tokens, With};
use primitives::{ConsumedResult, Info, Parser, ParseError, Stream};

/// Parses a character and succeeds if the character is equal to `c`.
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
where
    I: Stream<Item = u8>,
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

/// Parses a base-10 digit (0–9).
#[inline(always)]
pub fn digit<I>() -> Digit<I>
where
    I: Stream<Item = u8>,
{
    byte_parser!(digit, Digit, is_digit)
}

impl_token_parser! { Space(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }

/// Parses a `b' '`, `b'\t'`, `b'\n'` or `'b\'r'`.
#[inline(always)]
pub fn space<I>() -> Space<I>
where
    I: Stream<Item = u8>,
{
    byte_parser!(space, Space, is_whitespace)
}

impl_token_parser! { Spaces(), u8, Expected<SkipMany<Space<I>>> }
/// Skips over [`space`] zero or more times
///
/// [`space`]: fn.space.html
#[inline(always)]
pub fn spaces<I>() -> Spaces<I>
where
    I: Stream<Item = u8>,
{
    Spaces(skip_many(space()).expected("whitespaces"), PhantomData)
}

impl_token_parser! { Newline(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }

/// Parses a newline character (`b'\n'`).
#[inline(always)]
pub fn newline<I>() -> Newline<I>
where
    I: Stream<Item = u8>,
{
    Newline(
        satisfy(static_fn!((ch, u8) -> bool { ch == b'\n' })).expected("lf newline"),
        PhantomData,
    )
}

impl_token_parser! { CrLf(), u8, Expected<With<Satisfy<I, fn (u8) -> bool>, Newline<I>>> }

/// Parses carriage return and newline (`b"\r\n"`), returning the newline character.
#[inline(always)]
pub fn crlf<I>() -> CrLf<I>
where
    I: Stream<Item = u8>,
{
    CrLf(
        satisfy(static_fn!((ch, u8) -> bool { ch == b'\r' }))
            .with(newline())
            .expected("crlf newline"),
        PhantomData,
    )
}

impl_token_parser! { Tab(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }
/// Parses a tab character (`b'\t'`).
#[inline(always)]
pub fn tab<I>() -> Tab<I>
where
    I: Stream<Item = u8>,
{
    Tab(
        satisfy(static_fn!((ch, u8) -> bool { ch == b'\t' })).expected("tab"),
        PhantomData,
    )
}

impl_token_parser! { Upper(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }
/// Parses an uppercase ASCII letter (A–Z).
#[inline(always)]
pub fn upper<I>() -> Upper<I>
where
    I: Stream<Item = u8>,
{
    byte_parser!(upper, Upper, is_uppercase)
}

impl_token_parser! { Lower(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }
/// Parses an lowercase ASCII letter (a–z).
#[inline(always)]
pub fn lower<I>() -> Lower<I>
where
    I: Stream<Item = u8>,
{
    byte_parser!(lower, Lower, is_lowercase)
}

impl_token_parser! { AlphaNum(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }
/// Parses either an ASCII alphabet letter or digit (a–z, A–Z, 0–9).
#[inline(always)]
pub fn alpha_num<I>() -> AlphaNum<I>
where
    I: Stream<Item = u8>,
{
    byte_parser!(alpha_num, AlphaNum, is_alphanumeric)
}

impl_token_parser! { Letter(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }
/// Parses an ASCII alphabet letter (a–z, A–Z).
#[inline(always)]
pub fn letter<I>() -> Letter<I>
where
    I: Stream<Item = u8>,
{
    byte_parser!(letter, Letter, is_alphabetic)
}

impl_token_parser! { HexDigit(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }
/// Parses an ASCII hexdecimal digit (accepts both uppercase and lowercase).
#[inline(always)]
pub fn hex_digit<I>() -> HexDigit<I>
where
    I: Stream<Item = u8>,
{
    byte_parser!(hex_digit, HexDigit, is_hex)
}

#[derive(Clone)]
pub struct Bytes<I>(&'static [u8], PhantomData<I>)
where
    I: Stream<Item = u8>;

impl<'a, I> Parser for Bytes<I>
where
    I: Stream<Item = u8, Range = &'a [u8]>,
{
    type Input = I;
    type Output = &'static [u8];
    #[inline]
    fn parse_lazy(&mut self, input: Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        tokens(|&l, r| l == r, Info::Range(self.0), self.0.iter())
            .parse_lazy(input)
            .map(|chars| chars.as_slice())
    }
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        tokens(|&l, r| l == r, Info::Range(self.0), self.0.iter()).add_error(errors)
    }
}

/// Parses the bytes `s`.
///
/// If you have a stream implementing [`RangeStream`] such as `&[u8]` you can also use the
/// [`range`] parser which may be more efficient.
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
///
/// [`RangeStream`]: ../primitives/trait.RangeStream.html
/// [`range`]: ../range/fn.range.html
#[inline(always)]
pub fn bytes<'a, I>(s: &'static [u8]) -> Bytes<I>
where
    I: Stream<Item = u8, Range = &'a [u8]>,
{
    Bytes(s, PhantomData)
}

#[derive(Clone)]
pub struct BytesCmp<C, I>(&'static [u8], C, PhantomData<I>)
where
    I: Stream<Item = u8>;

impl<'a, C, I> Parser for BytesCmp<C, I>
where
    C: FnMut(u8, u8) -> bool,
    I: Stream<Item = u8, Range = &'a [u8]>,
{
    type Input = I;
    type Output = &'static [u8];
    #[inline]
    fn parse_lazy(&mut self, input: Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        let cmp = &mut self.1;
        tokens(|&l, r| cmp(l, r), Info::Range(self.0), self.0).parse_lazy(input)
    }
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        let cmp = &mut self.1;
        tokens(|&l, r| cmp(l, r), Info::Range(self.0), self.0.iter()).add_error(errors)
    }
}

/// Parses the bytes `s` using `cmp` to compare each token.
///
/// If you have a stream implementing [`RangeStream`] such as `&[u8]` you can also use the
/// [`range`] parser which may be more efficient.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::byte::bytes_cmp;
/// # use combine::primitives::Info;
/// # fn main() {
/// use std::ascii::AsciiExt;
/// let result = bytes_cmp(&b"abc"[..], |l, r| l.eq_ignore_ascii_case(&r))
///     .parse(&b"AbC"[..]);
/// assert_eq!(result, Ok((&b"abc"[..], &b""[..])));
/// # }
/// ```
///
/// [`RangeStream`]: ../primitives/trait.RangeStream.html
/// [`range`]: ../range/fn.range.html
#[inline(always)]
pub fn bytes_cmp<'a, C, I>(s: &'static [u8], cmp: C) -> BytesCmp<C, I>
where
    C: FnMut(u8, u8) -> bool,
    I: Stream<Item = u8, Range = &'a [u8]>,
{
    BytesCmp(s, cmp, PhantomData)
}

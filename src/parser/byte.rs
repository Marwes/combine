//! Module containing parsers specialized on byte streams.
extern crate ascii;

use lib::marker::PhantomData;

use self::ascii::AsciiChar;

use combinator::{satisfy, skip_many, token, tokens, Expected, Satisfy, SkipMany, Token};
use error::{ConsumedResult, Info, ParseError, StreamError, Tracked};
use parser::sequence::With;
use parser::ParseMode;
use stream::{uncons_range, FullRangeStream, RangeStream, Stream, StreamOnce};
use Parser;

use error::FastResult::*;

/// Parses a byteacter and succeeds if the byteacter is equal to `c`.
///
/// ```
/// use combine::Parser;
/// use combine::parser::byte::byte;
/// assert_eq!(byte(b'!').parse(&b"!"[..]), Ok((b'!', &b""[..])));
/// assert!(byte(b'A').parse(&b""[..]).is_err());
/// assert!(byte(b'A').parse(&b"!"[..]).is_err());
/// ```
#[inline(always)]
pub fn byte<I>(c: u8) -> Token<I>
where
    I: Stream<Item = u8>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    token(c)
}

impl_token_parser! { Digit(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }

macro_rules! byte_parser {
    ($name:ident, $ty:ident, $f:ident) => {{
        let f = static_fn!((c, u8) -> bool {
                AsciiChar::from(c).map(|c| c.$f()).unwrap_or(false)
            });
        $ty(satisfy(f).expected(stringify!($name)), PhantomData)
    }};
}

/// Parses a base-10 digit (0–9).
///
/// ```
/// use combine::Parser;
/// use combine::parser::byte::digit;
/// assert_eq!(digit().parse(&b"9"[..]), Ok((b'9', &b""[..])));
/// assert!(digit().parse(&b"A"[..]).is_err());
/// ```
#[inline(always)]
pub fn digit<I>() -> Digit<I>
where
    I: Stream<Item = u8>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    byte_parser!(digit, Digit, is_digit)
}

impl_token_parser! { Space(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }

/// Parses a `b' '`, `b'\t'`, `b'\n'` or `'b\'r'`.
///
/// ```
/// use combine::Parser;
/// use combine::parser::byte::space;
/// assert_eq!(space().parse(&b" "[..]), Ok((b' ', &b""[..])));
/// assert_eq!(space().parse(&b"  "[..]), Ok((b' ', &b" "[..])));
/// assert!(space().parse(&b"!"[..]).is_err());
/// assert!(space().parse(&b""[..]).is_err());
/// ```
#[inline(always)]
pub fn space<I>() -> Space<I>
where
    I: Stream<Item = u8>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    byte_parser!(space, Space, is_whitespace)
}

impl_token_parser! { Spaces(), u8, Expected<SkipMany<Space<I>>> }
/// Skips over [`space`] zero or more times
///
/// [`space`]: fn.space.html
///
/// ```
/// use combine::Parser;
/// use combine::parser::byte::spaces;
/// assert_eq!(spaces().parse(&b""[..]), Ok(((), &b""[..])));
/// assert_eq!(spaces().parse(&b"   "[..]), Ok(((), &b""[..])));
/// ```
#[inline(always)]
pub fn spaces<I>() -> Spaces<I>
where
    I: Stream<Item = u8>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    Spaces(skip_many(space()).expected("whitespaces"), PhantomData)
}

impl_token_parser! { Newline(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }

/// Parses a newline byteacter (`b'\n'`).
///
/// ```
/// use combine::Parser;
/// use combine::parser::byte::newline;
/// assert_eq!(newline().parse(&b"\n"[..]), Ok((b'\n', &b""[..])));
/// assert!(newline().parse(&b"\r"[..]).is_err());
/// ```
#[inline(always)]
pub fn newline<I>() -> Newline<I>
where
    I: Stream<Item = u8>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    Newline(
        satisfy(static_fn!((ch, u8) -> bool { ch == b'\n' })).expected("lf newline"),
        PhantomData,
    )
}

impl_token_parser! { CrLf(), u8, Expected<With<Satisfy<I, fn (u8) -> bool>, Newline<I>>> }

/// Parses carriage return and newline (`&b"\r\n"`), returning the newline byteacter.
///
/// ```
/// use combine::Parser;
/// use combine::parser::byte::crlf;
/// assert_eq!(crlf().parse(&b"\r\n"[..]), Ok((b'\n', &b""[..])));
/// assert!(crlf().parse(&b"\r"[..]).is_err());
/// assert!(crlf().parse(&b"\n"[..]).is_err());
/// ```
#[inline(always)]
pub fn crlf<I>() -> CrLf<I>
where
    I: Stream<Item = u8>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    CrLf(
        satisfy(static_fn!((ch, u8) -> bool { ch == b'\r' }))
            .with(newline())
            .expected("crlf newline"),
        PhantomData,
    )
}

impl_token_parser! { Tab(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }
/// Parses a tab byteacter (`b'\t'`).
///
/// ```
/// use combine::Parser;
/// use combine::parser::byte::tab;
/// assert_eq!(tab().parse(&b"\t"[..]), Ok((b'\t', &b""[..])));
/// assert!(tab().parse(&b" "[..]).is_err());
/// ```
#[inline(always)]
pub fn tab<I>() -> Tab<I>
where
    I: Stream<Item = u8>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    Tab(
        satisfy(static_fn!((ch, u8) -> bool { ch == b'\t' })).expected("tab"),
        PhantomData,
    )
}

impl_token_parser! { Upper(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }
/// Parses an uppercase ASCII letter (A–Z).
///
/// ```
/// use combine::Parser;
/// use combine::parser::byte::upper;
/// assert_eq!(upper().parse(&b"A"[..]), Ok((b'A', &b""[..])));
/// assert!(upper().parse(&b"a"[..]).is_err());
/// ```
#[inline(always)]
pub fn upper<I>() -> Upper<I>
where
    I: Stream<Item = u8>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    byte_parser!(upper, Upper, is_uppercase)
}

impl_token_parser! { Lower(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }
/// Parses an lowercase ASCII letter (a–z).
///
/// ```
/// use combine::Parser;
/// use combine::parser::byte::lower;
/// assert_eq!(lower().parse(&b"a"[..]), Ok((b'a', &b""[..])));
/// assert!(lower().parse(&b"A"[..]).is_err());
/// ```
#[inline(always)]
pub fn lower<I>() -> Lower<I>
where
    I: Stream<Item = u8>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    byte_parser!(lower, Lower, is_lowercase)
}

impl_token_parser! { AlphaNum(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }
/// Parses either an ASCII alphabet letter or digit (a–z, A–Z, 0–9).
///
/// ```
/// use combine::Parser;
/// use combine::parser::byte::alpha_num;
/// assert_eq!(alpha_num().parse(&b"A"[..]), Ok((b'A', &b""[..])));
/// assert_eq!(alpha_num().parse(&b"1"[..]), Ok((b'1', &b""[..])));
/// assert!(alpha_num().parse(&b"!"[..]).is_err());
/// ```
#[inline(always)]
pub fn alpha_num<I>() -> AlphaNum<I>
where
    I: Stream<Item = u8>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    byte_parser!(alpha_num, AlphaNum, is_alphanumeric)
}

impl_token_parser! { Letter(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }
/// Parses an ASCII alphabet letter (a–z, A–Z).
///
/// ```
/// use combine::Parser;
/// use combine::parser::byte::letter;
/// assert_eq!(letter().parse(&b"a"[..]), Ok((b'a', &b""[..])));
/// assert_eq!(letter().parse(&b"A"[..]), Ok((b'A', &b""[..])));
/// assert!(letter().parse(&b"9"[..]).is_err());
/// ```
#[inline(always)]
pub fn letter<I>() -> Letter<I>
where
    I: Stream<Item = u8>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    byte_parser!(letter, Letter, is_alphabetic)
}

impl_token_parser! { OctDigit(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }

/// Parses an octal digit.
///
/// ```
/// use combine::Parser;
/// use combine::parser::byte::oct_digit;
/// assert_eq!(oct_digit().parse(&b"7"[..]), Ok((b'7', &b""[..])));
/// assert!(oct_digit().parse(&b"8"[..]).is_err());
/// ```
#[inline(always)]
pub fn oct_digit<I>() -> OctDigit<I>
where
    I: Stream<Item = u8>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    OctDigit(
        satisfy(static_fn!((ch, u8) -> bool { ch >= b'0' && ch <= b'7' })).expected("octal digit"),
        PhantomData,
    )
}

impl_token_parser! { HexDigit(), u8, Expected<Satisfy<I, fn (u8) -> bool>> }
/// Parses an ASCII hexdecimal digit (accepts both uppercase and lowercase).
///
/// ```
/// use combine::Parser;
/// use combine::parser::byte::hex_digit;
/// assert_eq!(hex_digit().parse(&b"F"[..]), Ok((b'F', &b""[..])));
/// assert!(hex_digit().parse(&b"H"[..]).is_err());
/// ```
#[inline(always)]
pub fn hex_digit<I>() -> HexDigit<I>
where
    I: Stream<Item = u8>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    byte_parser!(hex_digit, HexDigit, is_hex)
}

#[derive(Copy, Clone)]
pub struct Bytes<I>(&'static [u8], PhantomData<I>)
where
    I: Stream<Item = u8>,
    I::Error: ParseError<I::Item, I::Range, I::Position>;

impl<'a, I> Parser for Bytes<I>
where
    I: Stream<Item = u8, Range = &'a [u8]>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    type Input = I;
    type Output = &'static [u8];
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        tokens(|&l, r| l == r, Info::Range(self.0), self.0.iter())
            .parse_lazy(input)
            .map(|bytes| bytes.as_slice())
    }
    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        tokens::<_, _, I>(|&l, r| l == r, Info::Range(self.0), self.0.iter()).add_error(errors)
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
/// # use combine::parser::byte::bytes;
/// # fn main() {
/// let result = bytes(&b"rust"[..])
///     .parse(&b"rust"[..])
///     .map(|x| x.0);
/// assert_eq!(result, Ok(&b"rust"[..]));
/// # }
/// ```
///
/// [`RangeStream`]: ../error/trait.RangeStream.html
/// [`range`]: ../range/fn.range.html
#[inline(always)]
pub fn bytes<'a, I>(s: &'static [u8]) -> Bytes<I>
where
    I: Stream<Item = u8, Range = &'a [u8]>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    Bytes(s, PhantomData)
}

#[derive(Copy, Clone)]
pub struct BytesCmp<C, I>(&'static [u8], C, PhantomData<I>)
where
    I: Stream<Item = u8>,
    I::Error: ParseError<I::Item, I::Range, I::Position>;

impl<'a, C, I> Parser for BytesCmp<C, I>
where
    C: FnMut(u8, u8) -> bool,
    I: Stream<Item = u8, Range = &'a [u8]>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    type Input = I;
    type Output = &'static [u8];
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        let cmp = &mut self.1;
        tokens(|&l, r| cmp(l, r), Info::Range(self.0), self.0).parse_lazy(input)
    }
    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        let cmp = &mut self.1;
        tokens::<_, _, I>(|&l, r| cmp(l, r), Info::Range(self.0), self.0.iter()).add_error(errors)
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
/// # use combine::parser::byte::bytes_cmp;
/// # use combine::stream::easy::Info;
/// # fn main() {
/// use std::ascii::AsciiExt;
/// let result = bytes_cmp(&b"abc"[..], |l, r| l.eq_ignore_ascii_case(&r))
///     .parse(&b"AbC"[..]);
/// assert_eq!(result, Ok((&b"abc"[..], &b""[..])));
/// # }
/// ```
///
/// [`RangeStream`]: ../error/trait.RangeStream.html
/// [`range`]: ../range/fn.range.html
#[inline(always)]
pub fn bytes_cmp<'a, C, I>(s: &'static [u8], cmp: C) -> BytesCmp<C, I>
where
    C: FnMut(u8, u8) -> bool,
    I: Stream<Item = u8, Range = &'a [u8]>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    BytesCmp(s, cmp, PhantomData)
}

fn take_until_after<I>(
    input: &mut I,
    offset: &mut usize,
    bytes: &[u8],
    found: Option<usize>,
) -> ConsumedResult<I::Range, I>
where
    I: RangeStream,
    I::Range: ::stream::Range,
{
    match found {
        Some(i) => {
            let result = uncons_range(input, *offset + i);
            if result.is_ok() {
                *offset = 0;
            }
            result
        }
        None => {
            *offset = bytes.len();
            let _ = input.uncons_range(bytes.len());
            let err = I::Error::from_error(input.position(), StreamError::end_of_input());
            if !input.is_partial() && bytes.is_empty() {
                EmptyErr(err.into())
            } else {
                ConsumedErr(err)
            }
        }
    }
}

macro_rules! take_until {
    (
        $(#[$attr:meta])*
        $type_name: ident, $func_name: ident, $memchr: ident, $($param: ident),+
    ) => {
        pub struct $type_name<I> {
            $( $param: u8, )+
            _marker: PhantomData<fn(I)>
        }

        impl<I> Parser for $type_name<I>
        where
            I: RangeStream + FullRangeStream,
            I::Range: AsRef<[u8]> + ::stream::Range,
        {
            type Input = I;
            type Output = I::Range;
            type PartialState = usize;

            parse_mode!();
            #[inline]
            fn parse_mode<M>(
                &mut self,
                mode: M,
                input: &mut Self::Input,
                offset: &mut Self::PartialState,
            ) -> ConsumedResult<Self::Output, Self::Input>
            where
                M: ParseMode,
            {
                if mode.is_first() {
                    *offset = 0;
                }
                let range = input.range();
                let bytes = range.as_ref();
                let found = ::memchr::$memchr( $(self.$param),+ , &bytes[*offset..]);
                take_until_after(input, offset, bytes, found)
            }
        }

        $(#[$attr])*
        #[inline(always)]
        pub fn $func_name<I>( $($param: u8),+ ) -> $type_name<I>
        where
            I: RangeStream + FullRangeStream,
            I::Range: AsRef<[u8]>,
        {
            $type_name {
                $($param,)+
                _marker: PhantomData
            }
        }
    }
}

take_until!{
    /// Zero-copy parser which reads a range of 0 or more tokens until `a` is found.
    ///
    /// If `a` is not found, the parser will return an error.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::parser::byte::take_until_byte;
    /// # use combine::*;
    /// # fn main() {
    /// let mut parser = take_until_byte(b'\r');
    /// let result = parser.parse("To: user@example.com\r\n");
    /// assert_eq!(result, Ok(("To: user@example.com", "\r\n")));
    /// let result = parser.parse("Hello, world\n");
    /// assert!(result.is_err());
    /// # }
    /// ```
    TakeUntilByte, take_until_byte, memchr, a
}
take_until!{
    /// Zero-copy parser which reads a range of 0 or more tokens until `a` or `b` is found.
    ///
    /// If `a` or `b` is not found, the parser will return an error.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::parser::byte::take_until_byte2;
    /// # use combine::*;
    /// # fn main() {
    /// let mut parser = take_until_byte2(b'\r', b'\n');
    /// let result = parser.parse("To: user@example.com\r\n");
    /// assert_eq!(result, Ok(("To: user@example.com", "\r\n")));
    /// let result = parser.parse("Hello, world\n");
    /// assert_eq!(result, Ok(("Hello, world", "\n")));
    /// # }
    /// ```
    TakeUntilByte2, take_until_byte2, memchr2, a, b
}
take_until!{
    /// Zero-copy parser which reads a range of 0 or more tokens until `a`, 'b' or `c` is found.
    ///
    /// If `a`, 'b' or `c` is not found, the parser will return an error.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::parser::byte::take_until_byte3;
    /// # use combine::*;
    /// # fn main() {
    /// let mut parser = take_until_byte3(b'\r', b'\n', b' ');
    /// let result = parser.parse("To: user@example.com\r\n");
    /// assert_eq!(result, Ok(("To:", " user@example.com\r\n")));
    /// let result = parser.parse("Helloworld");
    /// assert!(result.is_err());
    /// # }
    /// ```
    TakeUntilByte3, take_until_byte3, memchr3, a, b, c
}

/// Parsers for decoding numbers in big-endian or little-endian order.
pub mod num {
    use super::*;
    use stream::uncons;

    use byteorder::{ByteOrder, BE, LE};

    use lib::mem::size_of;

    macro_rules! integer_parser {
        (
            $(#[$attr:meta])*
            pub $type_name: ident,
            $func_name: ident, $be_name: ident, $le_name: ident, $read_name: ident
        ) => {
            #[derive(Clone)]
            pub struct $type_name<B, I>(PhantomData<(B, I)>);

            impl<'a, B, I> Parser for $type_name<B, I>
            where
                I: Stream<Item = u8>,
                I::Error: ParseError<I::Item, I::Range, I::Position>,
                B: ByteOrder,
            {
                type Input = I;
                type Output = $func_name;
                type PartialState = ();

                #[inline]
                fn parse_lazy(
                    &mut self,
                    input: &mut Self::Input
                    ) -> ConsumedResult<Self::Output, Self::Input> {
                    let buffer = &mut [0u8; 8][..size_of::<Self::Output>()];
                    for elem in &mut *buffer {
                        *elem = ctry!(uncons(input)).0;
                    }
                    ConsumedOk(B::$read_name(buffer))
                }
            }

            $(#[$attr])*
            #[inline(always)]
            pub fn $func_name<'a, B, I>() -> $type_name<B, I>
            where
                I: Stream<Item = u8>,
                I::Error: ParseError<I::Item, I::Range, I::Position>,
                B: ByteOrder,
            {
                $type_name(PhantomData)
            }

            $(#[$attr])*
            #[inline(always)]
            pub fn $be_name<'a, I>() -> $type_name<BE, I>
            where
                I: Stream<Item = u8>,
                I::Error: ParseError<I::Item, I::Range, I::Position>,
            {
                $func_name()
            }

            $(#[$attr])*
            #[inline(always)]
            pub fn $le_name<'a, I>() -> $type_name<LE, I>
            where
                I: Stream<Item = u8>,
                I::Error: ParseError<I::Item, I::Range, I::Position>,
            {
                $func_name()
            }
        }
    }

    integer_parser!(
        /// Reads a u16 out of the byte stream with the specified endianess
        ///
        /// ```
        /// use combine::byteorder::LE;
        /// use combine::Parser;
        /// use combine::parser::byte::num::u16;
        ///
        /// assert_eq!(u16::<LE, _>().parse(&b"\x01\0"[..]), Ok((1, &b""[..])));
        /// assert!(u16::<LE, _>().parse(&b"\0"[..]).is_err());
        /// ```
        pub U16, u16, be_u16, le_u16, read_u16
    );
    integer_parser!(
        /// Reads a u32 out of the byte stream with the specified endianess
        ///
        /// ```
        /// use combine::byteorder::LE;
        /// use combine::Parser;
        /// use combine::parser::byte::num::u32;
        ///
        /// assert_eq!(u32::<LE, _>().parse(&b"\x01\0\0\0"[..]), Ok((1, &b""[..])));
        /// assert!(u32::<LE, _>().parse(&b"\x01\0\0"[..]).is_err());
        /// ```
        pub U32, u32, be_u32, le_u32, read_u32
    );
    integer_parser!(
        /// Reads a u64 out of the byte stream with the specified endianess
        ///
        /// ```
        /// use combine::byteorder::LE;
        /// use combine::Parser;
        /// use combine::parser::byte::num::u64;
        ///
        /// assert_eq!(u64::<LE, _>().parse(&b"\x01\0\0\0\0\0\0\0"[..]), Ok((1, &b""[..])));
        /// assert!(u64::<LE, _>().parse(&b"\x01\0\0\0\0\0\0"[..]).is_err());
        /// ```
        pub U64, u64, be_u64, le_u64, read_u64
    );

    integer_parser!(
        /// Reads a i16 out of the byte stream with the specified endianess
        ///
        /// ```
        /// use combine::byteorder::LE;
        /// use combine::Parser;
        /// use combine::parser::byte::num::i16;
        ///
        /// assert_eq!(i16::<LE, _>().parse(&b"\x01\0"[..]), Ok((1, &b""[..])));
        /// assert!(i16::<LE, _>().parse(&b"\x01"[..]).is_err());
        /// ```
        pub I16, i16, be_i16, le_i16, read_i16
    );

    integer_parser!(
        /// Reads a i32 out of the byte stream with the specified endianess
        ///
        /// ```
        /// use combine::byteorder::LE;
        /// use combine::Parser;
        /// use combine::parser::byte::num::i32;
        ///
        /// assert_eq!(i32::<LE, _>().parse(&b"\x01\0\0\0"[..]), Ok((1, &b""[..])));
        /// assert!(i32::<LE, _>().parse(&b"\x01\0\0"[..]).is_err());
        /// ```
        pub I32, i32, be_i32, le_i32, read_i32
    );
    integer_parser!(
        /// Reads a i64 out of the byte stream with the specified endianess
        ///
        /// ```
        /// use combine::byteorder::LE;
        /// use combine::Parser;
        /// use combine::parser::byte::num::i64;
        ///
        /// assert_eq!(i64::<LE, _>().parse(&b"\x01\0\0\0\0\0\0\0"[..]), Ok((1, &b""[..])));
        /// assert!(i64::<LE, _>().parse(&b"\x01\0\0\0\0\0\0"[..]).is_err());
        /// ```
        pub I64, i64, be_i64, le_i64, read_i64
    );

    integer_parser!(
        /// Reads a i32 out of the byte stream with the specified endianess
        ///
        /// ```
        /// use combine::byteorder::{LE, ByteOrder};
        /// use combine::Parser;
        /// use combine::parser::byte::num::f32;
        ///
        /// let mut buf = [0; 4];
        /// LE::write_f32(&mut buf, 123.45);
        /// assert_eq!(f32::<LE, _>().parse(&buf[..]), Ok((123.45, &b""[..])));
        /// assert!(f32::<LE, _>().parse(&b"\x01\0\0"[..]).is_err());
        /// ```
        pub F32, f32, be_f32, le_f32, read_f32
    );
    integer_parser!(
        /// Reads a i64 out of the byte stream with the specified endianess
        ///
        /// ```
        /// use combine::byteorder::{LE, ByteOrder};
        /// use combine::Parser;
        /// use combine::parser::byte::num::f64;
        ///
        /// let mut buf = [0; 8];
        /// LE::write_f64(&mut buf, 123.45);
        /// assert_eq!(f64::<LE, _>().parse(&buf[..]), Ok((123.45, &b""[..])));
        /// assert!(f64::<LE, _>().parse(&b"\x01\0\0\0\0\0\0"[..]).is_err());
        /// ```
        pub F64, f64, be_f64, le_f64, read_f64
    );

    #[cfg(test)]
    mod tests {
        use super::*;
        use stream::buffered::BufferedStream;
        use stream::state::State;
        use stream::IteratorStream;

        #[test]
        fn no_rangestream() {
            let mut buf = [0; 8];
            LE::write_f64(&mut buf, 123.45);
            assert_eq!(
                f64::<LE, _>()
                    .parse(BufferedStream::new(
                        State::new(IteratorStream::new(buf.iter().cloned())),
                        1
                    ))
                    .map(|(t, _)| t),
                Ok(123.45)
            );
            assert_eq!(
                le_f64()
                    .parse(BufferedStream::new(
                        State::new(IteratorStream::new(buf.iter().cloned())),
                        1
                    ))
                    .map(|(t, _)| t),
                Ok(123.45)
            );
            let mut buf = [0; 8];
            BE::write_f64(&mut buf, 123.45);
            assert_eq!(
                be_f64()
                    .parse(BufferedStream::new(
                        State::new(IteratorStream::new(buf.iter().cloned())),
                        1
                    ))
                    .map(|(t, _)| t),
                Ok(123.45)
            );
        }
    }
}

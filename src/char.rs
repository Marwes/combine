use primitives::{Parser, ParseError, ConsumedResult, Stream};
use combinator::{Expected, satisfy, Satisfy, skip_many, SkipMany, token, Token, tokens, With};
use std::marker::PhantomData;

/// Parses a character and succeeds if the character is equal to `c`.
///
/// ```
/// use combine::Parser;
/// use combine::char::char;
/// assert_eq!(char('!').parse("!"), Ok(('!', "")));
/// assert!(char('A').parse("!").is_err());
/// ```
#[inline(always)]
pub fn char<I>(c: char) -> Token<I>
where
    I: Stream<Item = char>,
{
    token(c)
}

impl_token_parser! { Digit(), char, Expected<Satisfy<I, fn (char) -> bool>> }

/// Parses a base-10 digit.
///
/// ```
/// use combine::Parser;
/// use combine::char::digit;
/// assert_eq!(digit().parse("9"), Ok(('9', "")));
/// assert!(digit().parse("A").is_err());
/// ```
#[inline(always)]
pub fn digit<I>() -> Digit<I>
where
    I: Stream<Item = char>,
{
    Digit(
        satisfy(static_fn!((c, char) -> bool { c.is_digit(10) })).expected("digit"),
        PhantomData,
    )
}

impl_token_parser! { Space(), char, Expected<Satisfy<I, fn (char) -> bool>> }

/// Parse a single whitespace according to [`std::char::is_whitespace`].
///
/// This includes space characters, tabs and newlines.
///
/// [`std::char::is_whitespace`]: https://doc.rust-lang.org/std/primitive.char.html#method.is_whitespace
///
/// ```
/// use combine::Parser;
/// use combine::char::space;
/// assert_eq!(space().parse(" "), Ok((' ', "")));
/// assert_eq!(space().parse("  "), Ok((' ', " ")));
/// assert!(space().parse("!").is_err());
/// assert!(space().parse("").is_err());
/// ```
#[inline(always)]
pub fn space<I>() -> Space<I>
where
    I: Stream<Item = char>,
{
    let f: fn(char) -> bool = char::is_whitespace;
    Space(satisfy(f).expected("whitespace"), PhantomData)
}

impl_token_parser! { Spaces(), char, Expected<SkipMany<Space<I>>> }

/// Skips over zero or more spaces according to [`std::char::is_whitespace`].
///
/// This includes space characters, tabs and newlines.
///
/// [`std::char::is_whitespace`]: https://doc.rust-lang.org/std/primitive.char.html#method.is_whitespace
///
/// ```
/// use combine::Parser;
/// use combine::char::spaces;
/// assert_eq!(spaces().parse(""), Ok(((), "")));
/// assert_eq!(spaces().parse("   "), Ok(((), "")));
/// ```
#[inline(always)]
pub fn spaces<I>() -> Spaces<I>
where
    I: Stream<Item = char>,
{
    Spaces(skip_many(space()).expected("whitespaces"), PhantomData)
}

impl_token_parser! { Newline(), char, Expected<Satisfy<I, fn (char) -> bool>> }

/// Parses a newline character.
///
/// ```
/// use combine::Parser;
/// use combine::char::newline;
/// assert_eq!(newline().parse("\n"), Ok(('\n', "")));
/// assert!(newline().parse("\r").is_err());
/// ```
#[inline(always)]
pub fn newline<I>() -> Newline<I>
where
    I: Stream<Item = char>,
{
    Newline(
        satisfy(static_fn!((ch, char) -> bool { ch == '\n' })).expected("lf newline"),
        PhantomData,
    )
}

impl_token_parser! { CrLf(), char, Expected<With<Satisfy<I, fn (char) -> bool>, Newline<I>>> }

/// Parses carriage return and newline, returning the newline character.
///
/// ```
/// use combine::Parser;
/// use combine::char::crlf;
/// assert_eq!(crlf().parse("\r\n"), Ok(('\n', "")));
/// assert!(crlf().parse("\r").is_err());
/// assert!(crlf().parse("\n").is_err());
/// ```
#[inline(always)]
pub fn crlf<I>() -> CrLf<I>
where
    I: Stream<Item = char>,
{
    CrLf(
        satisfy(static_fn!((ch, char) -> bool { ch == '\r' }))
            .with(newline())
            .expected("crlf newline"),
        PhantomData,
    )
}

impl_token_parser! { Tab(), char, Expected<Satisfy<I, fn (char) -> bool>> }

/// Parses a tab character.
///
/// ```
/// use combine::Parser;
/// use combine::char::tab;
/// assert_eq!(tab().parse("\t"), Ok(('\t', "")));
/// assert!(tab().parse(" ").is_err());
/// ```
#[inline(always)]
pub fn tab<I>() -> Tab<I>
where
    I: Stream<Item = char>,
{
    Tab(
        satisfy(static_fn!((ch, char) -> bool { ch == '\t' })).expected("tab"),
        PhantomData,
    )
}

impl_token_parser! { Upper(), char, Expected<Satisfy<I, fn (char) -> bool>> }

/// Parses an uppercase letter according to [`std::char::is_uppercase`].
///
/// [`std::char::is_uppercase`]: https://doc.rust-lang.org/std/primitive.char.html#method.is_uppercase
///
/// ```
/// use combine::Parser;
/// use combine::char::upper;
/// assert_eq!(upper().parse("A"), Ok(('A', "")));
/// assert!(upper().parse("a").is_err());
/// ```
#[inline(always)]
pub fn upper<I>() -> Upper<I>
where
    I: Stream<Item = char>,
{
    Upper(
        satisfy(static_fn!((ch, char) -> bool { ch.is_uppercase()})).expected("uppercase letter"),
        PhantomData,
    )
}

impl_token_parser! { Lower(), char, Expected<Satisfy<I, fn (char) -> bool>> }

/// Parses an lowercase letter according to [`std::char::is_lowercase`].
///
/// [`std::char::is_lowercase`]: https://doc.rust-lang.org/std/primitive.char.html#method.is_lowercase
///
/// ```
/// use combine::Parser;
/// use combine::char::lower;
/// assert_eq!(lower().parse("a"), Ok(('a', "")));
/// assert!(lower().parse("A").is_err());
/// ```
#[inline(always)]
pub fn lower<I>() -> Lower<I>
where
    I: Stream<Item = char>,
{
    Lower(
        satisfy(static_fn!((ch, char) -> bool { ch.is_lowercase() })).expected("lowercase letter"),
        PhantomData,
    )
}

impl_token_parser! { AlphaNum(), char, Expected<Satisfy<I, fn (char) -> bool>> }

/// Parses either an alphabet letter or digit according to [`std::char::is_alphanumeric`].
///
/// [`std::char::is_alphanumeric`]: https://doc.rust-lang.org/std/primitive.char.html#method.is_alphanumeric
///
/// ```
/// use combine::Parser;
/// use combine::char::alpha_num;
/// assert_eq!(alpha_num().parse("A"), Ok(('A', "")));
/// assert_eq!(alpha_num().parse("1"), Ok(('1', "")));
/// assert!(alpha_num().parse("!").is_err());
/// ```
#[inline(always)]
pub fn alpha_num<I>() -> AlphaNum<I>
where
    I: Stream<Item = char>,
{
    AlphaNum(
        satisfy(static_fn!((ch, char) -> bool { ch.is_alphanumeric() }))
            .expected("letter or digit"),
        PhantomData,
    )
}

impl_token_parser! { Letter(), char, Expected<Satisfy<I, fn (char) -> bool>> }

/// Parses an alphabet letter according to [`std::char::is_alphabetic`].
///
/// [`std::char::is_alphabetic`]: https://doc.rust-lang.org/std/primitive.char.html#method.is_alphabetic
///
/// ```
/// use combine::Parser;
/// use combine::char::letter;
/// assert_eq!(letter().parse("a"), Ok(('a', "")));
/// assert_eq!(letter().parse("A"), Ok(('A', "")));
/// assert!(letter().parse("9").is_err());
/// ```
#[inline(always)]
pub fn letter<I>() -> Letter<I>
where
    I: Stream<Item = char>,
{
    Letter(
        satisfy(static_fn!((ch, char) -> bool { ch.is_alphabetic() })).expected("letter"),
        PhantomData,
    )
}

impl_token_parser! { OctDigit(), char, Expected<Satisfy<I, fn (char) -> bool>> }

/// Parses an octal digit.
///
/// ```
/// use combine::Parser;
/// use combine::char::oct_digit;
/// assert_eq!(oct_digit().parse("7"), Ok(('7', "")));
/// assert!(oct_digit().parse("8").is_err());
/// ```
#[inline(always)]
pub fn oct_digit<I>() -> OctDigit<I>
where
    I: Stream<Item = char>,
{
    OctDigit(
        satisfy(static_fn!((ch, char) -> bool { ch.is_digit(8) })).expected("octal digit"),
        PhantomData,
    )
}

impl_token_parser! { HexDigit(), char, Expected<Satisfy<I, fn (char) -> bool>> }

/// Parses a hexdecimal digit with uppercase and lowercase.
///
/// ```
/// use combine::Parser;
/// use combine::char::hex_digit;
/// assert_eq!(hex_digit().parse("F"), Ok(('F', "")));
/// assert!(hex_digit().parse("H").is_err());
/// ```
#[inline(always)]
pub fn hex_digit<I>() -> HexDigit<I>
where
    I: Stream<Item = char>,
{
    HexDigit(
        satisfy(static_fn!((ch, char) -> bool { ch.is_digit(0x10) })).expected("hexadecimal digit"),
        PhantomData,
    )
}

fn eq(l: char, r: char) -> bool {
    l == r
}

#[derive(Clone)]
pub struct Str<I>(&'static str, PhantomData<fn(I) -> I>)
where
    I: Stream<Item = char>;
impl<I> Parser for Str<I>
where
    I: Stream<Item = char>,
{
    type Input = I;
    type Output = &'static str;
    #[inline]
    fn parse_lazy(&mut self, input: Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        tokens(eq, self.0.into(), self.0.chars())
            .parse_lazy(input)
            .map(|_| self.0)
    }
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        tokens(eq, self.0.into(), self.0.chars()).add_error(errors)
    }
}

/// Parses the string `s`.
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
where
    I: Stream<Item = char>,
{
    Str(s, PhantomData)
}

#[derive(Clone)]
pub struct StrCmp<C, I>(&'static str, C, PhantomData<fn(I) -> I>)
where
    I: Stream<Item = char>;
impl<C, I> Parser for StrCmp<C, I>
where
    C: FnMut(char, char) -> bool,
    I: Stream<Item = char>,
{
    type Input = I;
    type Output = &'static str;
    #[inline]
    fn parse_lazy(&mut self, input: Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        tokens(&mut self.1, self.0.into(), self.0.chars())
            .parse_lazy(input)
            .map(|_| self.0)
    }
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        tokens(&mut self.1, self.0.into(), self.0.chars()).add_error(errors)
    }
}

/// Parses the string `s`, using `cmp` to compare each character.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::char::string_cmp;
/// use std::ascii::AsciiExt;
/// # fn main() {
/// let result = string_cmp("rust", |l, r| l.eq_ignore_ascii_case(&r))
///     .parse("RusT")
///     .map(|x| x.0);
/// assert_eq!(result, Ok("rust"));
/// # }
/// ```
#[inline(always)]
pub fn string_cmp<C, I>(s: &'static str, cmp: C) -> StrCmp<C, I>
where
    C: FnMut(char, char) -> bool,
    I: Stream<Item = char>,
{
    StrCmp(s, cmp, PhantomData)
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::{Error, ParseError, Parser, SourcePosition, State};

    #[test]
    fn space_error() {
        let result = space().parse("");
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err().errors,
            vec![Error::end_of_input(), Error::Expected("whitespace".into())]
        );

    }

    #[test]
    fn string_consumed() {
        let result = string("a").parse(State::new("b"));
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err().position,
            SourcePosition { line: 1, column: 1 }
        );
    }

    #[test]
    fn string_error() {
        let result = string("abc").parse(State::new("bc"));
        assert_eq!(
            result,
            Err(ParseError {
                position: SourcePosition { line: 1, column: 1 },
                errors: vec![Error::Unexpected('b'.into()), Error::Expected("abc".into())],
            })
        );
    }
}

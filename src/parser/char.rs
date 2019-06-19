//! Module containing parsers specialized on character streams.

use crate::combinator::{satisfy, skip_many, token, Expected, Satisfy, SkipMany, Token};
use crate::error::{ParseError, ParseResult, Tracked};
use crate::lib::marker::PhantomData;
use crate::parser::item::tokens_cmp;
use crate::parser::sequence::With;
use crate::stream::Stream;
use crate::Parser;

/// Parses a character and succeeds if the character is equal to `c`.
///
/// ```
/// use combine::Parser;
/// use combine::parser::char::char;
/// assert_eq!(char('!').parse("!"), Ok(('!', "")));
/// assert!(char('A').parse("!").is_err());
/// ```
#[inline(always)]
pub fn char<Input>(c: char) -> Token<Input>
where
    Input: Stream<Item = char>,
    Input::Error: ParseError<Input::Item, Input::Range, Input::Position>,
{
    token(c)
}

parser! {
    #[derive(Copy, Clone)]
    pub struct Digit;
    /// Parses a base-10 digit.
    ///
    /// ```
    /// use combine::Parser;
    /// use combine::parser::char::digit;
    /// assert_eq!(digit().parse("9"), Ok(('9', "")));
    /// assert!(digit().parse("A").is_err());
    /// ```
    pub fn digit[Input]()(Input) -> char
    where
        [Input: Stream<Item = char>,]
    {
        satisfy(|c: char| c.is_digit(10)).expected("digit")
    }
}

impl_token_parser! { Space(), char, Expected<Satisfy<Input, fn (char) -> bool>, Input::Item, Input::Range> }

/// Parse a single whitespace according to [`std::char::is_whitespace`].
///
/// This includes space characters, tabs and newlines.
///
/// [`std::char::is_whitespace`]: https://doc.rust-lang.org/std/primitive.char.html#method.is_whitespace
///
/// ```
/// use combine::Parser;
/// use combine::parser::char::space;
/// assert_eq!(space().parse(" "), Ok((' ', "")));
/// assert_eq!(space().parse("  "), Ok((' ', " ")));
/// assert!(space().parse("!").is_err());
/// assert!(space().parse("").is_err());
/// ```
#[inline(always)]
pub fn space<Input>() -> Space<Input>
where
    Input: Stream<Item = char>,
    Input::Error: ParseError<Input::Item, Input::Range, Input::Position>,
{
    let f: fn(char) -> bool = char::is_whitespace;
    Space(satisfy(f).expected("whitespace"), PhantomData)
}

impl_token_parser! { Spaces(), char, Expected<SkipMany<Input, Space<Input>>, Input::Item, Input::Range> }

/// Skips over zero or more spaces according to [`std::char::is_whitespace`].
///
/// This includes space characters, tabs and newlines.
///
/// [`std::char::is_whitespace`]: https://doc.rust-lang.org/std/primitive.char.html#method.is_whitespace
///
/// ```
/// use combine::Parser;
/// use combine::parser::char::spaces;
/// assert_eq!(spaces().parse(""), Ok(((), "")));
/// assert_eq!(spaces().parse("   "), Ok(((), "")));
/// ```
#[inline(always)]
pub fn spaces<Input>() -> Spaces<Input>
where
    Input: Stream<Item = char>,
    Input::Error: ParseError<Input::Item, Input::Range, Input::Position>,
{
    Spaces(skip_many(space()).expected("whitespaces"), PhantomData)
}

impl_token_parser! { Newline(), char, Expected<Satisfy<Input, fn (char) -> bool>, Input::Item, Input::Range> }

/// Parses a newline character (`'\n'`).
///
/// ```
/// use combine::Parser;
/// use combine::parser::char::newline;
/// assert_eq!(newline().parse("\n"), Ok(('\n', "")));
/// assert!(newline().parse("\r").is_err());
/// ```
#[inline(always)]
pub fn newline<Input>() -> Newline<Input>
where
    Input: Stream<Item = char>,
    Input::Error: ParseError<Input::Item, Input::Range, Input::Position>,
{
    Newline(
        satisfy(static_fn!((ch, char) -> bool { ch == '\n' })).expected("lf newline"),
        PhantomData,
    )
}

impl_token_parser! { CrLf(), char, Expected<With<Satisfy<Input, fn (char) -> bool>, Newline<Input>>, Input::Item, Input::Range> }

/// Parses carriage return and newline (`"\r\n"`), returning the newline character.
///
/// ```
/// use combine::Parser;
/// use combine::parser::char::crlf;
/// assert_eq!(crlf().parse("\r\n"), Ok(('\n', "")));
/// assert!(crlf().parse("\r").is_err());
/// assert!(crlf().parse("\n").is_err());
/// ```
#[inline(always)]
pub fn crlf<Input>() -> CrLf<Input>
where
    Input: Stream<Item = char>,
    Input::Error: ParseError<Input::Item, Input::Range, Input::Position>,
{
    CrLf(
        satisfy(static_fn!((ch, char) -> bool { ch == '\r' }))
            .with(newline())
            .expected("crlf newline"),
        PhantomData,
    )
}

impl_token_parser! { Tab(), char, Expected<Satisfy<Input, fn (char) -> bool>, Input::Item, Input::Range> }

/// Parses a tab character (`'\t'`).
///
/// ```
/// use combine::Parser;
/// use combine::parser::char::tab;
/// assert_eq!(tab().parse("\t"), Ok(('\t', "")));
/// assert!(tab().parse(" ").is_err());
/// ```
#[inline(always)]
pub fn tab<Input>() -> Tab<Input>
where
    Input: Stream<Item = char>,
    Input::Error: ParseError<Input::Item, Input::Range, Input::Position>,
{
    Tab(
        satisfy(static_fn!((ch, char) -> bool { ch == '\t' })).expected("tab"),
        PhantomData,
    )
}

impl_token_parser! { Upper(), char, Expected<Satisfy<Input, fn (char) -> bool>, Input::Item, Input::Range> }

/// Parses an uppercase letter according to [`std::char::is_uppercase`].
///
/// [`std::char::is_uppercase`]: https://doc.rust-lang.org/std/primitive.char.html#method.is_uppercase
///
/// ```
/// use combine::Parser;
/// use combine::parser::char::upper;
/// assert_eq!(upper().parse("A"), Ok(('A', "")));
/// assert!(upper().parse("a").is_err());
/// ```
#[inline(always)]
pub fn upper<Input>() -> Upper<Input>
where
    Input: Stream<Item = char>,
    Input::Error: ParseError<Input::Item, Input::Range, Input::Position>,
{
    Upper(
        satisfy(static_fn!((ch, char) -> bool { ch.is_uppercase()})).expected("uppercase letter"),
        PhantomData,
    )
}

impl_token_parser! { Lower(), char, Expected<Satisfy<Input, fn (char) -> bool>, Input::Item, Input::Range> }

/// Parses an lowercase letter according to [`std::char::is_lowercase`].
///
/// [`std::char::is_lowercase`]: https://doc.rust-lang.org/std/primitive.char.html#method.is_lowercase
///
/// ```
/// use combine::Parser;
/// use combine::parser::char::lower;
/// assert_eq!(lower().parse("a"), Ok(('a', "")));
/// assert!(lower().parse("A").is_err());
/// ```
#[inline(always)]
pub fn lower<Input>() -> Lower<Input>
where
    Input: Stream<Item = char>,
    Input::Error: ParseError<Input::Item, Input::Range, Input::Position>,
{
    Lower(
        satisfy(static_fn!((ch, char) -> bool { ch.is_lowercase() })).expected("lowercase letter"),
        PhantomData,
    )
}

impl_token_parser! { AlphaNum(), char, Expected<Satisfy<Input, fn (char) -> bool>, Input::Item, Input::Range> }

/// Parses either an alphabet letter or digit according to [`std::char::is_alphanumeric`].
///
/// [`std::char::is_alphanumeric`]: https://doc.rust-lang.org/std/primitive.char.html#method.is_alphanumeric
///
/// ```
/// use combine::Parser;
/// use combine::parser::char::alpha_num;
/// assert_eq!(alpha_num().parse("A"), Ok(('A', "")));
/// assert_eq!(alpha_num().parse("1"), Ok(('1', "")));
/// assert!(alpha_num().parse("!").is_err());
/// ```
#[inline(always)]
pub fn alpha_num<Input>() -> AlphaNum<Input>
where
    Input: Stream<Item = char>,
    Input::Error: ParseError<Input::Item, Input::Range, Input::Position>,
{
    AlphaNum(
        satisfy(static_fn!((ch, char) -> bool { ch.is_alphanumeric() }))
            .expected("letter or digit"),
        PhantomData,
    )
}

impl_token_parser! { Letter(), char, Expected<Satisfy<Input, fn (char) -> bool>, Input::Item, Input::Range> }

/// Parses an alphabet letter according to [`std::char::is_alphabetic`].
///
/// [`std::char::is_alphabetic`]: https://doc.rust-lang.org/std/primitive.char.html#method.is_alphabetic
///
/// ```
/// use combine::Parser;
/// use combine::parser::char::letter;
/// assert_eq!(letter().parse("a"), Ok(('a', "")));
/// assert_eq!(letter().parse("A"), Ok(('A', "")));
/// assert!(letter().parse("9").is_err());
/// ```
#[inline(always)]
pub fn letter<Input>() -> Letter<Input>
where
    Input: Stream<Item = char>,
    Input::Error: ParseError<Input::Item, Input::Range, Input::Position>,
{
    Letter(
        satisfy(static_fn!((ch, char) -> bool { ch.is_alphabetic() })).expected("letter"),
        PhantomData,
    )
}

impl_token_parser! { OctDigit(), char, Expected<Satisfy<Input, fn (char) -> bool>, Input::Item, Input::Range> }

/// Parses an octal digit.
///
/// ```
/// use combine::Parser;
/// use combine::parser::char::oct_digit;
/// assert_eq!(oct_digit().parse("7"), Ok(('7', "")));
/// assert!(oct_digit().parse("8").is_err());
/// ```
#[inline(always)]
pub fn oct_digit<Input>() -> OctDigit<Input>
where
    Input: Stream<Item = char>,
    Input::Error: ParseError<Input::Item, Input::Range, Input::Position>,
{
    OctDigit(
        satisfy(static_fn!((ch, char) -> bool { ch.is_digit(8) })).expected("octal digit"),
        PhantomData,
    )
}

impl_token_parser! { HexDigit(), char, Expected<Satisfy<Input, fn (char) -> bool>, Input::Item, Input::Range> }

/// Parses a hexdecimal digit with uppercase and lowercase.
///
/// ```
/// use combine::Parser;
/// use combine::parser::char::hex_digit;
/// assert_eq!(hex_digit().parse("F"), Ok(('F', "")));
/// assert!(hex_digit().parse("H").is_err());
/// ```
#[inline(always)]
pub fn hex_digit<Input>() -> HexDigit<Input>
where
    Input: Stream<Item = char>,
    Input::Error: ParseError<Input::Item, Input::Range, Input::Position>,
{
    HexDigit(
        satisfy(static_fn!((ch, char) -> bool { ch.is_digit(0x10) })).expected("hexadecimal digit"),
        PhantomData,
    )
}

/// Parses the string `s`.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::parser::char::string;
/// # fn main() {
/// let result = string("rust")
///     .parse("rust")
///     .map(|x| x.0);
/// assert_eq!(result, Ok("rust"));
/// # }
/// ```
#[inline(always)]
pub fn string<'a, Input>(s: &'static str) -> impl Parser<Input, Output = &'a str>
where
    Input: Stream<Item = char>,
    Input::Error: ParseError<Input::Item, Input::Range, Input::Position>,
{
    string_cmp(s, |l, r| l == r)
}

/// Parses the string `s`, using `cmp` to compare each character.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::parser::char::string_cmp;
/// use std::ascii::AsciiExt;
/// # fn main() {
/// let result = string_cmp("rust", |l, r| l.eq_ignore_ascii_case(&r))
///     .parse("RusT")
///     .map(|x| x.0);
/// assert_eq!(result, Ok("rust"));
/// # }
/// ```
#[inline(always)]
pub fn string_cmp<'a, C, Input>(s: &'static str, cmp: C) -> impl Parser<Input, Output = &'a str>
where
    C: FnMut(char, char) -> bool,
    Input: Stream<Item = char>,
    Input::Error: ParseError<Input::Item, Input::Range, Input::Position>,
{
    tokens_cmp(s.chars(), cmp).map(move |_| s).expected(s)
}

#[cfg(all(feature = "std", test))]
mod tests {
    use super::*;

    use crate::{
        parser::EasyParser,
        stream::{
            easy::{Error, Errors},
            state::{SourcePosition, State},
        },
    };

    #[test]
    fn space_error() {
        let result = space().easy_parse("");
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err().errors,
            vec![Error::end_of_input(), Error::Expected("whitespace".into())]
        );
    }

    #[test]
    fn string_consumed() {
        let result = string("a").easy_parse(State::new("b"));
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err().position,
            SourcePosition { line: 1, column: 1 }
        );
    }

    #[test]
    fn string_error() {
        let result = string("abc").easy_parse(State::new("bc"));
        assert_eq!(
            result,
            Err(Errors {
                position: SourcePosition { line: 1, column: 1 },
                errors: vec![Error::Unexpected('b'.into()), Error::Expected("abc".into())],
            })
        );
    }
}

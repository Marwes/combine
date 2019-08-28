//! Parsers working with single stream items.

use crate::lib::marker::PhantomData;

use crate::{
    error::{Info, ParseError, ParseResult, ResultExt, StreamError, Tracked},
    stream::{uncons, Stream, StreamOnce},
    Parser,
};

use crate::error::ParseResult::*;

#[doc(inline)]
pub use self::token as item;

#[derive(Copy, Clone)]
pub struct Any<Input>(PhantomData<fn(Input) -> Input>);

impl<Input> Parser<Input> for Any<Input>
where
    Input: Stream,
{
    type Output = Input::Item;
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Input) -> ParseResult<Input::Item, Input::Error> {
        uncons(input)
    }
}

/// Parses any token.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # fn main() {
/// let mut char_parser = any();
/// assert_eq!(char_parser.parse("!").map(|x| x.0), Ok('!'));
/// assert!(char_parser.parse("").is_err());
/// let mut byte_parser = any();
/// assert_eq!(byte_parser.parse(&b"!"[..]).map(|x| x.0), Ok(b'!'));
/// assert!(byte_parser.parse(&b""[..]).is_err());
/// # }
/// ```
#[inline]
pub fn any<Input>() -> Any<Input>
where
    Input: Stream,
{
    Any(PhantomData)
}

#[derive(Copy, Clone)]
pub struct Satisfy<Input, P> {
    predicate: P,
    _marker: PhantomData<Input>,
}

fn satisfy_impl<Input, P, R>(input: &mut Input, mut predicate: P) -> ParseResult<R, Input::Error>
where
    Input: Stream,
    P: FnMut(Input::Item) -> Option<R>,
{
    let position = input.position();
    match uncons(input) {
        EmptyOk(c) | ConsumedOk(c) => match predicate(c.clone()) {
            Some(c) => ConsumedOk(c),
            None => EmptyErr(Input::Error::empty(position).into()),
        },
        EmptyErr(err) => EmptyErr(err),
        ConsumedErr(err) => ConsumedErr(err),
    }
}

impl<Input, P> Parser<Input> for Satisfy<Input, P>
where
    Input: Stream,
    P: FnMut(Input::Item) -> bool,
{
    type Output = Input::Item;
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Input) -> ParseResult<Self::Output, Input::Error> {
        satisfy_impl(input, |c| {
            if (self.predicate)(c.clone()) {
                Some(c)
            } else {
                None
            }
        })
    }
}

/// Parses a token and succeeds depending on the result of `predicate`.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # fn main() {
/// let mut parser = satisfy(|c| c == '!' || c == '?');
/// assert_eq!(parser.parse("!").map(|x| x.0), Ok('!'));
/// assert_eq!(parser.parse("?").map(|x| x.0), Ok('?'));
/// # }
/// ```
#[inline]
pub fn satisfy<Input, P>(predicate: P) -> Satisfy<Input, P>
where
    Input: Stream,
    P: FnMut(Input::Item) -> bool,
{
    Satisfy {
        predicate: predicate,
        _marker: PhantomData,
    }
}

#[derive(Copy, Clone)]
pub struct SatisfyMap<Input, P> {
    predicate: P,
    _marker: PhantomData<Input>,
}

impl<Input, P, R> Parser<Input> for SatisfyMap<Input, P>
where
    Input: Stream,
    P: FnMut(Input::Item) -> Option<R>,
{
    type Output = R;
    type PartialState = ();
    #[inline]
    fn parse_lazy(&mut self, input: &mut Input) -> ParseResult<Self::Output, Input::Error> {
        satisfy_impl(input, &mut self.predicate)
    }
}

/// Parses a token and passes it to `predicate`. If `predicate` returns `Some` the parser succeeds
/// and returns the value inside the `Option`. If `predicate` returns `None` the parser fails
/// without consuming any input.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # fn main() {
/// #[derive(Debug, PartialEq)]
/// enum YesNo {
///     Yes,
///     No,
/// }
/// let mut parser = satisfy_map(|c| {
///     match c {
///         'Y' => Some(YesNo::Yes),
///         'N' => Some(YesNo::No),
///         _ => None,
///     }
/// });
/// assert_eq!(parser.parse("Y").map(|x| x.0), Ok(YesNo::Yes));
/// assert!(parser.parse("A").map(|x| x.0).is_err());
/// # }
/// ```
#[inline]
pub fn satisfy_map<Input, P, R>(predicate: P) -> SatisfyMap<Input, P>
where
    Input: Stream,
    P: FnMut(Input::Item) -> Option<R>,
{
    SatisfyMap {
        predicate: predicate,
        _marker: PhantomData,
    }
}

#[derive(Copy, Clone)]
pub struct Token<Input>
where
    Input: Stream,
    Input::Item: PartialEq,
{
    c: Input::Item,
    _marker: PhantomData<Input>,
}

impl<Input> Parser<Input> for Token<Input>
where
    Input: Stream,
    Input::Item: PartialEq + Clone,
{
    type Output = Input::Item;
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Input) -> ParseResult<Input::Item, Input::Error> {
        satisfy_impl(input, |c| if c == self.c { Some(c) } else { None })
    }
    fn add_error(&mut self, errors: &mut Tracked<<Input as StreamOnce>::Error>) {
        errors.error.add_expected(Info::Token(self.c.clone()));
    }
}

/// Parses a character and succeeds if the character is equal to `c`.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # fn main() {
/// let result = token('!')
///     .parse("!")
///     .map(|x| x.0);
/// assert_eq!(result, Ok('!'));
/// # }
/// ```
#[inline]
pub fn token<Input>(c: Input::Item) -> Token<Input>
where
    Input: Stream,
    Input::Item: PartialEq,
{
    Token {
        c: c,
        _marker: PhantomData,
    }
}

#[derive(Clone)]
pub struct Tokens<C, T, Input>
where
    Input: Stream,
{
    cmp: C,
    expected: Info<Input::Item, Input::Range, &'static str>,
    tokens: T,
    _marker: PhantomData<Input>,
}

impl<Input, C, T> Parser<Input> for Tokens<C, T, Input>
where
    C: FnMut(T::Item, Input::Item) -> bool,
    T: Clone + IntoIterator,
    Input: Stream,
{
    type Output = T;
    type PartialState = ();
    #[inline]
    fn parse_lazy(&mut self, input: &mut Input) -> ParseResult<T, Input::Error> {
        let start = input.position();
        let mut consumed = false;
        for c in self.tokens.clone() {
            match crate::stream::uncons(input) {
                ConsumedOk(other) | EmptyOk(other) => {
                    if !(self.cmp)(c, other.clone()) {
                        return if consumed {
                            let mut errors = <Input as StreamOnce>::Error::from_error(
                                start,
                                StreamError::unexpected(Info::Token(other)),
                            );
                            errors.add_expected(self.expected.clone());
                            ConsumedErr(errors)
                        } else {
                            EmptyErr(<Input as StreamOnce>::Error::empty(start).into())
                        };
                    }
                    consumed = true;
                }
                EmptyErr(mut error) => {
                    error.error.set_position(start);
                    return if consumed {
                        ConsumedErr(error.error)
                    } else {
                        EmptyErr(error.into())
                    };
                }
                ConsumedErr(mut error) => {
                    error.set_position(start);
                    return ConsumedErr(error);
                }
            }
        }
        if consumed {
            ConsumedOk(self.tokens.clone())
        } else {
            EmptyOk(self.tokens.clone())
        }
    }
    fn add_error(&mut self, errors: &mut Tracked<<Input as StreamOnce>::Error>) {
        errors.error.add_expected(self.expected.clone());
    }
}

/// Parses multiple tokens.
///
/// Consumes items from the input and compares them to the values from `tokens` using the
/// comparison function `cmp`. Succeeds if all the items from `tokens` are matched in the input
/// stream and fails otherwise with `expected` used as part of the error.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::error::Info;
/// # fn main() {
/// use std::ascii::AsciiExt;
/// let result = tokens(|l, r| l.eq_ignore_ascii_case(&r), "abc".into(), "abc".chars())
///     .parse("AbC")
///     .map(|x| x.0.as_str());
/// assert_eq!(result, Ok("abc"));
/// let result = tokens(
///     |&l, r| (if l < r { r - l } else { l - r }) <= 2,
///     Info::Range(&b"025"[..]),
///     &b"025"[..]
/// )
///     .parse(&b"123"[..])
///     .map(|x| x.0);
/// assert_eq!(result, Ok(&b"025"[..]));
/// # }
/// ```
#[inline]
pub fn tokens<C, T, Input>(
    cmp: C,
    expected: Info<Input::Item, Input::Range, &'static str>,
    tokens: T,
) -> Tokens<C, T, Input>
where
    C: FnMut(T::Item, Input::Item) -> bool,
    T: Clone + IntoIterator,
    Input: Stream,
{
    Tokens {
        cmp: cmp,
        expected: expected,
        tokens: tokens,
        _marker: PhantomData,
    }
}

#[derive(Clone)]
pub struct TokensCmp<C, T, Input>
where
    Input: Stream,
{
    cmp: C,
    tokens: T,
    _marker: PhantomData<Input>,
}

impl<Input, C, T> Parser<Input> for TokensCmp<C, T, Input>
where
    C: FnMut(T::Item, Input::Item) -> bool,
    T: Clone + IntoIterator,
    Input: Stream,
{
    type Output = T;
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Input) -> ParseResult<T, Input::Error> {
        let start = input.position();
        let mut consumed = false;
        for c in self.tokens.clone() {
            match crate::stream::uncons(input) {
                ConsumedOk(other) | EmptyOk(other) => {
                    if !(self.cmp)(c, other.clone()) {
                        return if consumed {
                            let errors = <Input as StreamOnce>::Error::from_error(
                                start,
                                StreamError::unexpected(Info::Token(other)),
                            );
                            ConsumedErr(errors)
                        } else {
                            EmptyErr(<Input as StreamOnce>::Error::empty(start).into())
                        };
                    }
                    consumed = true;
                }
                EmptyErr(mut error) => {
                    error.error.set_position(start);
                    return if consumed {
                        ConsumedErr(error.error)
                    } else {
                        EmptyErr(error)
                    };
                }
                ConsumedErr(mut error) => {
                    error.set_position(start);
                    return ConsumedErr(error);
                }
            }
        }
        if consumed {
            ConsumedOk(self.tokens.clone())
        } else {
            EmptyOk(self.tokens.clone())
        }
    }
}

/// Parses multiple tokens.
///
/// Consumes items from the input and compares them to the values from `tokens` using the
/// comparison function `cmp`. Succeeds if all the items from `tokens` are matched in the input
/// stream and fails otherwise.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # fn main() {
/// # #[allow(deprecated)]
/// # use std::ascii::AsciiExt;
/// let result = tokens_cmp("abc".chars(), |l, r| l.eq_ignore_ascii_case(&r))
///     .parse("AbC")
///     .map(|x| x.0.as_str());
/// assert_eq!(result, Ok("abc"));
/// let result = tokens_cmp(
///     &b"025"[..],
///     |&l, r| (if l < r { r - l } else { l - r }) <= 2,
/// )
///     .parse(&b"123"[..])
///     .map(|x| x.0);
/// assert_eq!(result, Ok(&b"025"[..]));
/// # }
/// ```
#[inline]
pub fn tokens_cmp<C, T, I>(tokens: T, cmp: C) -> TokensCmp<C, T, I>
where
    C: FnMut(T::Item, I::Item) -> bool,
    T: Clone + IntoIterator,
    I: Stream,
{
    TokensCmp {
        cmp: cmp,
        tokens: tokens,
        _marker: PhantomData,
    }
}

#[derive(Copy, Clone)]
pub struct Position<Input>
where
    Input: Stream,
{
    _marker: PhantomData<Input>,
}

impl<Input> Parser<Input> for Position<Input>
where
    Input: Stream,
{
    type Output = Input::Position;
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Input) -> ParseResult<Input::Position, Input::Error> {
        EmptyOk(input.position())
    }
}

/// Parser which just returns the current position in the stream.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::stream::state::{State, SourcePosition};
/// # fn main() {
/// let result = (position(), token('!'), position())
///     .parse(State::new("!"))
///     .map(|x| x.0);
/// assert_eq!(result, Ok((SourcePosition { line: 1, column: 1 },
///                        '!',
///                        SourcePosition { line: 1, column: 2 })));
/// # }
/// ```
#[inline]
pub fn position<Input>() -> Position<Input>
where
    Input: Stream,
{
    Position {
        _marker: PhantomData,
    }
}

#[derive(Copy, Clone)]
pub struct OneOf<T, Input>
where
    Input: Stream,
{
    tokens: T,
    _marker: PhantomData<Input>,
}

impl<Input, T> Parser<Input> for OneOf<T, Input>
where
    T: Clone + IntoIterator<Item = Input::Item>,
    Input: Stream,
    Input::Item: PartialEq,
{
    type Output = Input::Item;
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Input) -> ParseResult<Input::Item, Input::Error> {
        satisfy(|c| self.tokens.clone().into_iter().any(|t| t == c)).parse_lazy(input)
    }

    fn add_error(&mut self, errors: &mut Tracked<<Input as StreamOnce>::Error>) {
        for expected in self.tokens.clone() {
            errors.error.add_expected(Info::Token(expected));
        }
    }
}

/// Extract one token and succeeds if it is part of `tokens`.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # fn main() {
/// let result = many(one_of("abc".chars()))
///     .parse("abd");
/// assert_eq!(result, Ok((String::from("ab"), "d")));
/// # }
/// ```
#[inline]
pub fn one_of<T, Input>(tokens: T) -> OneOf<T, Input>
where
    T: Clone + IntoIterator,
    Input: Stream,
    Input::Item: PartialEq<T::Item>,
{
    OneOf {
        tokens: tokens,
        _marker: PhantomData,
    }
}

#[derive(Copy, Clone)]
pub struct NoneOf<T, Input>
where
    Input: Stream,
{
    tokens: T,
    _marker: PhantomData<Input>,
}

impl<Input, T> Parser<Input> for NoneOf<T, Input>
where
    T: Clone + IntoIterator<Item = Input::Item>,
    Input: Stream,
    Input::Item: PartialEq,
{
    type Output = Input::Item;
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Input) -> ParseResult<Input::Item, Input::Error> {
        satisfy(|c| self.tokens.clone().into_iter().all(|t| t != c)).parse_lazy(input)
    }
}

/// Extract one token and succeeds if it is not part of `tokens`.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::stream::easy;
/// # use combine::stream::state::State;
/// # fn main() {
/// let mut parser = many1(none_of(b"abc".iter().cloned()));
/// let result = parser.easy_parse(State::new(&b"xyb"[..]))
///     .map(|(output, input)| (output, input.input));
/// assert_eq!(result, Ok((b"xy"[..].to_owned(), &b"b"[..])));
///
/// let result = parser.easy_parse(State::new(&b"ab"[..]));
/// assert_eq!(result, Err(easy::Errors {
///     position: 0,
///     errors: vec![
///         easy::Error::Unexpected(easy::Info::Token(b'a')),
///     ]
/// }));
/// # }
/// ```
#[inline]
pub fn none_of<T, Input>(tokens: T) -> NoneOf<T, Input>
where
    T: Clone + IntoIterator,
    Input: Stream,
    Input::Item: PartialEq<T::Item>,
{
    NoneOf {
        tokens: tokens,
        _marker: PhantomData,
    }
}

#[derive(Copy, Clone)]
pub struct Value<Input, T>(T, PhantomData<fn(Input) -> Input>);
impl<Input, T> Parser<Input> for Value<Input, T>
where
    Input: Stream,
    T: Clone,
{
    type Output = T;
    type PartialState = ();
    #[inline]
    fn parse_lazy(&mut self, _: &mut Input) -> ParseResult<T, Input::Error> {
        EmptyOk(self.0.clone())
    }
}

/// Always returns the value `v` without consuming any input.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # fn main() {
/// let result = value(42)
///     .parse("hello world")
///     .map(|x| x.0);
/// assert_eq!(result, Ok(42));
/// # }
/// ```
#[inline]
pub fn value<Input, T>(v: T) -> Value<Input, T>
where
    Input: Stream,
    T: Clone,
{
    Value(v, PhantomData)
}

#[derive(Copy, Clone)]
pub struct Eof<Input>(PhantomData<Input>);
impl<Input> Parser<Input> for Eof<Input>
where
    Input: Stream,
{
    type Output = ();
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Input) -> ParseResult<(), Input::Error> {
        let before = input.checkpoint();
        match input.uncons() {
            Err(ref err) if err.is_unexpected_end_of_input() => EmptyOk(()),
            _ => {
                ctry!(input.reset(before).consumed());
                EmptyErr(<Input as StreamOnce>::Error::empty(input.position()).into())
            }
        }
    }

    fn add_error(&mut self, errors: &mut Tracked<<Input as StreamOnce>::Error>) {
        errors.error.add_expected("end of input");
    }
}

/// Succeeds only if the stream is at end of input, fails otherwise.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::stream::easy;
/// # use combine::stream::state::{State, SourcePosition};
/// # fn main() {
/// let mut parser = eof();
/// assert_eq!(parser.easy_parse(State::new("")), Ok(((), State::new(""))));
/// assert_eq!(parser.easy_parse(State::new("x")), Err(easy::Errors {
///     position: SourcePosition::default(),
///     errors: vec![
///         easy::Error::Unexpected('x'.into()),
///         easy::Error::Expected("end of input".into())
///     ]
/// }));
/// # }
/// ```
#[inline]
pub fn eof<Input>() -> Eof<Input>
where
    Input: Stream,
{
    Eof(PhantomData)
}

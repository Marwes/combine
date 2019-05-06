//! Parsers working with single stream items.

use lib::marker::PhantomData;

use error::{ConsumedResult, Info, ParseError, ResultExt, StreamError, Tracked};
use stream::{uncons, Stream, StreamOnce};
use Parser;

use error::FastResult::*;

#[doc(inline)]
pub use self::token as item;

#[derive(Copy, Clone)]
pub struct Any<I>(PhantomData<fn(I) -> I>);

impl<I> Parser for Any<I>
where
    I: Stream,
{
    type Input = I;
    type Output = I::Item;
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<I::Item, I> {
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
#[inline(always)]
pub fn any<I>() -> Any<I>
where
    I: Stream,
{
    Any(PhantomData)
}

#[derive(Copy, Clone)]
pub struct Satisfy<I, P> {
    predicate: P,
    _marker: PhantomData<I>,
}

fn satisfy_impl<I, P, R>(input: &mut I, mut predicate: P) -> ConsumedResult<R, I>
where
    I: Stream,
    P: FnMut(I::Item) -> Option<R>,
{
    let position = input.position();
    match uncons(input) {
        EmptyOk(c) | ConsumedOk(c) => match predicate(c.clone()) {
            Some(c) => ConsumedOk(c),
            None => EmptyErr(I::Error::empty(position).into()),
        },
        EmptyErr(err) => EmptyErr(err),
        ConsumedErr(err) => ConsumedErr(err),
    }
}

impl<I, P> Parser for Satisfy<I, P>
where
    I: Stream,
    P: FnMut(I::Item) -> bool,
{
    type Input = I;
    type Output = I::Item;
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
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
#[inline(always)]
pub fn satisfy<I, P>(predicate: P) -> Satisfy<I, P>
where
    I: Stream,
    P: FnMut(I::Item) -> bool,
{
    Satisfy {
        predicate: predicate,
        _marker: PhantomData,
    }
}

#[derive(Copy, Clone)]
pub struct SatisfyMap<I, P> {
    predicate: P,
    _marker: PhantomData<I>,
}

impl<I, P, R> Parser for SatisfyMap<I, P>
where
    I: Stream,
    P: FnMut(I::Item) -> Option<R>,
{
    type Input = I;
    type Output = R;
    type PartialState = ();
    #[inline]
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
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
#[inline(always)]
pub fn satisfy_map<I, P, R>(predicate: P) -> SatisfyMap<I, P>
where
    I: Stream,
    P: FnMut(I::Item) -> Option<R>,
{
    SatisfyMap {
        predicate: predicate,
        _marker: PhantomData,
    }
}

#[derive(Copy, Clone)]
pub struct Token<I>
where
    I: Stream,
    I::Item: PartialEq,
{
    c: I::Item,
    _marker: PhantomData<I>,
}

impl<I> Parser for Token<I>
where
    I: Stream,
    I::Item: PartialEq + Clone,
{
    type Input = I;
    type Output = I::Item;
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<I::Item, I> {
        satisfy_impl(input, |c| if c == self.c { Some(c) } else { None })
    }
    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
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
#[inline(always)]
pub fn token<I>(c: I::Item) -> Token<I>
where
    I: Stream,
    I::Item: PartialEq,
{
    Token {
        c: c,
        _marker: PhantomData,
    }
}

#[derive(Clone)]
pub struct Tokens<C, T, I>
where
    I: Stream,
{
    cmp: C,
    expected: Info<I::Item, I::Range>,
    tokens: T,
    _marker: PhantomData<I>,
}

impl<C, T, I> Parser for Tokens<C, T, I>
where
    C: FnMut(T::Item, I::Item) -> bool,
    T: Clone + IntoIterator,
    I: Stream,
{
    type Input = I;
    type Output = T;
    type PartialState = ();
    #[inline]
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<T, I> {
        let start = input.position();
        let mut consumed = false;
        for c in self.tokens.clone() {
            match ::stream::uncons(input) {
                ConsumedOk(other) | EmptyOk(other) => {
                    if !(self.cmp)(c, other.clone()) {
                        return if consumed {
                            let mut errors = <Self::Input as StreamOnce>::Error::from_error(
                                start,
                                StreamError::unexpected(Info::Token(other)),
                            );
                            errors.add_expected(self.expected.clone());
                            ConsumedErr(errors)
                        } else {
                            EmptyErr(<Self::Input as StreamOnce>::Error::empty(start).into())
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
    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
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
#[inline(always)]
pub fn tokens<C, T, I>(cmp: C, expected: Info<I::Item, I::Range>, tokens: T) -> Tokens<C, T, I>
where
    C: FnMut(T::Item, I::Item) -> bool,
    T: Clone + IntoIterator,
    I: Stream,
{
    Tokens {
        cmp: cmp,
        expected: expected,
        tokens: tokens,
        _marker: PhantomData,
    }
}

#[derive(Clone)]
pub struct Tokens2<C, T, I>
where
    I: Stream,
{
    cmp: C,
    tokens: T,
    _marker: PhantomData<I>,
}

impl<C, T, I> Parser for Tokens2<C, T, I>
where
    C: FnMut(T::Item, I::Item) -> bool,
    T: Clone + IntoIterator,
    I: Stream,
{
    type Input = I;
    type Output = T;
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<T, I> {
        let start = input.position();
        let mut consumed = false;
        for c in self.tokens.clone() {
            match ::stream::uncons(input) {
                ConsumedOk(other) | EmptyOk(other) => {
                    if !(self.cmp)(c, other.clone()) {
                        return if consumed {
                            let errors = <Self::Input as StreamOnce>::Error::from_error(
                                start,
                                StreamError::unexpected(Info::Token(other)),
                            );
                            ConsumedErr(errors)
                        } else {
                            EmptyErr(<Self::Input as StreamOnce>::Error::empty(start).into())
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
/// let result = tokens2(|l, r| l.eq_ignore_ascii_case(&r), "abc".chars())
///     .parse("AbC")
///     .map(|x| x.0.as_str());
/// assert_eq!(result, Ok("abc"));
/// let result = tokens2(
///     |&l, r| (if l < r { r - l } else { l - r }) <= 2,
///     &b"025"[..]
/// )
///     .parse(&b"123"[..])
///     .map(|x| x.0);
/// assert_eq!(result, Ok(&b"025"[..]));
/// # }
/// ```
#[inline(always)]
pub fn tokens2<C, T, I>(cmp: C, tokens: T) -> Tokens2<C, T, I>
where
    C: FnMut(T::Item, I::Item) -> bool,
    T: Clone + IntoIterator,
    I: Stream,
{
    Tokens2 {
        cmp: cmp,
        tokens: tokens,
        _marker: PhantomData,
    }
}

#[derive(Copy, Clone)]
pub struct Position<I>
where
    I: Stream,
{
    _marker: PhantomData<I>,
}

impl<I> Parser for Position<I>
where
    I: Stream,
{
    type Input = I;
    type Output = I::Position;
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<I::Position, I> {
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
#[inline(always)]
pub fn position<I>() -> Position<I>
where
    I: Stream,
{
    Position {
        _marker: PhantomData,
    }
}

#[derive(Copy, Clone)]
pub struct OneOf<T, I>
where
    I: Stream,
{
    tokens: T,
    _marker: PhantomData<I>,
}

impl<T, I> Parser for OneOf<T, I>
where
    T: Clone + IntoIterator<Item = I::Item>,
    I: Stream,
    I::Item: PartialEq,
{
    type Input = I;
    type Output = I::Item;
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<I::Item, I> {
        satisfy(|c| self.tokens.clone().into_iter().any(|t| t == c)).parse_lazy(input)
    }

    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
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
#[inline(always)]
pub fn one_of<T, I>(tokens: T) -> OneOf<T, I>
where
    T: Clone + IntoIterator,
    I: Stream,
    I::Item: PartialEq<T::Item>,
{
    OneOf {
        tokens: tokens,
        _marker: PhantomData,
    }
}

#[derive(Copy, Clone)]
pub struct NoneOf<T, I>
where
    I: Stream,
{
    tokens: T,
    _marker: PhantomData<I>,
}

impl<T, I> Parser for NoneOf<T, I>
where
    T: Clone + IntoIterator<Item = I::Item>,
    I: Stream,
    I::Item: PartialEq,
{
    type Input = I;
    type Output = I::Item;
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<I::Item, I> {
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
#[inline(always)]
pub fn none_of<T, I>(tokens: T) -> NoneOf<T, I>
where
    T: Clone + IntoIterator,
    I: Stream,
    I::Item: PartialEq<T::Item>,
{
    NoneOf {
        tokens: tokens,
        _marker: PhantomData,
    }
}

#[derive(Copy, Clone)]
pub struct Value<I, T>(T, PhantomData<fn(I) -> I>);
impl<I, T> Parser for Value<I, T>
where
    I: Stream,
    T: Clone,
{
    type Input = I;
    type Output = T;
    type PartialState = ();
    #[inline]
    fn parse_lazy(&mut self, _: &mut Self::Input) -> ConsumedResult<T, I> {
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
#[inline(always)]
pub fn value<I, T>(v: T) -> Value<I, T>
where
    I: Stream,
    T: Clone,
{
    Value(v, PhantomData)
}

#[derive(Copy, Clone)]
pub struct Eof<I>(PhantomData<I>);
impl<I> Parser for Eof<I>
where
    I: Stream,
{
    type Input = I;
    type Output = ();
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<(), I> {
        let before = input.checkpoint();
        match input.uncons() {
            Err(ref err) if err.is_unexpected_end_of_input() => EmptyOk(()),
            _ => {
                ctry!(input.reset(before).consumed());
                EmptyErr(<Self::Input as StreamOnce>::Error::empty(input.position()).into())
            }
        }
    }

    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        errors.error.add_expected("end of input".into());
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
#[inline(always)]
pub fn eof<I>() -> Eof<I>
where
    I: Stream,
{
    Eof(PhantomData)
}

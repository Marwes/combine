//! Parsers constructor from regular functions

use crate::lib::marker::PhantomData;

use crate::error::{ParseResult, StdParseResult};
use crate::stream::{Stream, StreamOnce};
use crate::Parser;

impl<'a, I: Stream, O> Parser for FnMut(&mut I) -> StdParseResult<O, I> + 'a {
    type Input = I;
    type Output = O;
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Input) -> ParseResult<O, <I as StreamOnce>::Error> {
        self(input).into()
    }
}

#[derive(Copy, Clone)]
pub struct FnParser<I, F>(F, PhantomData<fn(I) -> I>);

/// Wraps a function, turning it into a parser.
///
/// Mainly needed to turn closures into parsers as function types can be casted to function pointers
/// to make them usable as a parser.
///
/// ```
/// extern crate combine;
/// # use combine::*;
/// # use combine::parser::char::digit;
/// # use combine::error::{Consumed, StreamError};
/// # use combine::stream::easy;
/// # fn main() {
/// let mut even_digit = parser(|input| {
///     // Help type inference out
///     let _: &mut easy::Stream<&str> = input;
///     let position = input.position();
///     let (char_digit, consumed) = digit().parse_stream(input).into_result()?;
///     let d = (char_digit as i32) - ('0' as i32);
///     if d % 2 == 0 {
///         Ok((d, consumed))
///     }
///     else {
///         //Return an empty error since we only tested the first token of the stream
///         let errors = easy::Errors::new(
///             position,
///             StreamError::expected(From::from("even number"))
///         );
///         Err(Consumed::Empty(errors.into()))
///     }
/// });
/// let result = even_digit
///     .easy_parse("8")
///     .map(|x| x.0);
/// assert_eq!(result, Ok(8));
/// # }
/// ```
#[inline(always)]
pub fn parser<I, O, F>(f: F) -> FnParser<I, F>
where
    I: Stream,
    F: FnMut(&mut I) -> StdParseResult<O, I>,
{
    FnParser(f, PhantomData)
}

impl<I, O, F> Parser for FnParser<I, F>
where
    I: Stream,
    F: FnMut(&mut I) -> StdParseResult<O, I>,
{
    type Input = I;
    type Output = O;
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Input) -> ParseResult<O, <I as StreamOnce>::Error> {
        (self.0)(input).into()
    }
}

impl<I, O> Parser for fn(&mut I) -> StdParseResult<O, I>
where
    I: Stream,
{
    type Input = I;
    type Output = O;
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Input) -> ParseResult<O, <I as StreamOnce>::Error> {
        self(input).into()
    }
}

#[derive(Copy)]
pub struct EnvParser<E, I, T>
where
    I: Stream,
{
    env: E,
    parser: fn(E, &mut I) -> StdParseResult<T, I>,
}

impl<E, I, T> Clone for EnvParser<E, I, T>
where
    I: Stream,
    E: Clone,
{
    fn clone(&self) -> Self {
        EnvParser {
            env: self.env.clone(),
            parser: self.parser,
        }
    }
}

impl<E, I, O> Parser for EnvParser<E, I, O>
where
    E: Clone,
    I: Stream,
{
    type Input = I;
    type Output = O;
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Input) -> ParseResult<O, <I as StreamOnce>::Error> {
        (self.parser)(self.env.clone(), input).into()
    }
}

/// Constructs a parser out of an environment and a function which needs the given environment to
/// do the parsing. This is commonly useful to allow multiple parsers to share some environment
/// while still allowing the parsers to be written in separate functions.
///
/// ```
/// # extern crate combine;
/// # use std::collections::HashMap;
/// # use combine::*;
/// # use combine::char::letter;
/// # fn main() {
/// struct Interner(HashMap<String, u32>);
/// impl Interner {
///     fn string<I>(&self, input: &mut I) -> StdParseResult<u32, I>
///         where I: Stream<Item=char>,
///               I::Error: ParseError<I::Item, I::Range, I::Position>,
///     {
///         many(letter())
///             .map(|s: String| self.0.get(&s).cloned().unwrap_or(0))
///             .parse_stream(input)
///             .into_result()
///     }
/// }
///
/// let mut map = HashMap::new();
/// map.insert("hello".into(), 1);
/// map.insert("test".into(), 2);
///
/// let env = Interner(map);
/// let mut parser = env_parser(&env, Interner::string);
///
/// let result = parser.parse("hello");
/// assert_eq!(result, Ok((1, "")));
///
/// let result = parser.parse("world");
/// assert_eq!(result, Ok((0, "")));
/// # }
/// ```
#[inline(always)]
pub fn env_parser<E, I, O>(
    env: E,
    parser: fn(E, &mut I) -> StdParseResult<O, I>,
) -> EnvParser<E, I, O>
where
    E: Clone,
    I: Stream,
{
    EnvParser {
        env: env,
        parser: parser,
    }
}

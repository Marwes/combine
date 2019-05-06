//! Combinators which take one or more parsers and applies them repeatedly.

use crate::lib::borrow::BorrowMut;
use crate::lib::marker::PhantomData;
use crate::lib::mem;

use crate::combinator::{ignore, optional, parser, value, FnParser, Ignore, Optional, Value};
use crate::error::{Consumed, ConsumedResult, ParseError, ParseResult, ResultExt, StreamError, Tracked};
use crate::parser::choice::Or;
use crate::parser::sequence::With;
use crate::parser::ParseMode;
use crate::stream::{uncons, Positioned, ResetStream, Stream, StreamOnce};
use crate::{ErrorOffset, Parser};

use crate::error::FastResult::*;

parser! {
#[derive(Copy, Clone)]
pub struct Count;

/// Parses `parser` from zero up to `count` times.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::error::Info;
/// # use combine::stream::easy::Error;
/// # fn main() {
/// let mut parser = count(2, token(b'a'));
///
/// let result = parser.parse(&b"aaab"[..]);
/// assert_eq!(result, Ok((b"aa"[..].to_owned(), &b"ab"[..])));
/// # }
/// ```
#[inline(always)]
pub fn count[F, P](count: usize, parser: P)(P::Input) -> F
where [
    P: Parser,
    F: Extend<P::Output> + Default,
]
{
    count_min_max(0, *count, parser)
}

}

parser! {
    #[derive(Copy, Clone)]
    pub struct SkipCount;
    type PartialState = <With<Count<Sink, P>, Value<P::Input, ()>> as Parser>::PartialState;
    /// Parses `parser` from zero up to `count` times skipping the output of `parser`.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::stream::easy::{Error, Info};
    /// # fn main() {
    /// let mut parser = skip_count(2, token(b'a'));
    ///
    /// let result = parser.parse(&b"aaab"[..]);
    /// assert_eq!(result, Ok(((), &b"ab"[..])));
    /// # }
    /// ```
    pub fn skip_count[P](count: usize, parser: P)(P::Input) -> ()
    where [
        P: Parser
    ]
    {
        crate::combinator::count::<Sink, _>(*count, parser.map(|_| ())).with(value(()))
    }
}

#[derive(Copy, Clone)]
pub struct CountMinMax<F, P> {
    parser: P,
    min: usize,
    max: usize,
    _marker: PhantomData<fn() -> F>,
}

impl<P, F> Parser for CountMinMax<F, P>
where
    P: Parser,
    F: Extend<P::Output> + Default,
{
    type Input = P::Input;
    type Output = F;
    type PartialState = (usize, F, P::PartialState);

    parse_mode!();
    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input>
    where
        M: ParseMode,
    {
        let (ref mut count, ref mut elements, ref mut child_state) = *state;

        let mut iter = self.parser.by_ref().partial_iter(mode, input, child_state);
        elements.extend(
            iter.by_ref()
                .take(self.max - *count)
                .inspect(|_| *count += 1),
        );
        if *count < self.min {
            let err = StreamError::message_message(format_args!(
                "expected {} more elements",
                self.min - *count
            ));
            iter.fail(err)
        } else {
            iter.into_result_fast(elements).map(|x| {
                *count = 0;
                x
            })
        }
    }

    fn add_error(&mut self, error: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.parser.add_error(error)
    }
}

/// Parses `parser` from `min` to `max` times (including `min` and `max`).
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::stream::easy::{Error, Info};
/// # fn main() {
/// let mut parser = count_min_max(2, 2, token(b'a'));
///
/// let result = parser.parse(&b"aaab"[..]);
/// assert_eq!(result, Ok((b"aa"[..].to_owned(), &b"ab"[..])));
/// let result = parser.parse(&b"ab"[..]);
/// assert!(result.is_err());
/// # }
/// ```
///
/// # Panics
///
/// If `min` > `max`.
#[inline(always)]
pub fn count_min_max<F, P>(min: usize, max: usize, parser: P) -> CountMinMax<F, P>
where
    P: Parser,
    F: Extend<P::Output> + Default,
{
    assert!(min <= max);

    CountMinMax {
        parser,
        min: min,
        max: max,
        _marker: PhantomData,
    }
}

parser! {
    #[derive(Copy, Clone)]
    pub struct SkipCountMinMax;
    type PartialState = <With<CountMinMax<Sink, P>, Value<P::Input, ()>> as Parser>::PartialState;
    /// Parses `parser` from `min` to `max` times (including `min` and `max`)
    /// skipping the output of `parser`.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # fn main() {
    /// let mut parser = skip_count_min_max(2, 2, token(b'a'));
    ///
    /// let result = parser.parse(&b"aaab"[..]);
    /// assert_eq!(result, Ok(((), &b"ab"[..])));
    /// let result = parser.parse(&b"ab"[..]);
    /// assert!(result.is_err());
    /// # }
    /// ```
    ///
    /// # Panics
    ///
    /// If `min` > `max`.
    pub fn skip_count_min_max[P](min: usize, max: usize, parser: P)(P::Input) -> ()
    where [
        P: Parser
    ]
    {
        crate::combinator::count_min_max::<Sink, _>(*min, *max, parser.map(|_| ())).with(value(()))
    }
}

pub struct Iter<'a, P: Parser, S, M>
where
    P::Input: 'a,
{
    parser: P,
    input: &'a mut P::Input,
    consumed: bool,
    state: State<<P::Input as StreamOnce>::Error>,
    partial_state: S,
    mode: M,
}

enum State<E> {
    Ok,
    EmptyErr,
    ConsumedErr(E),
}

impl<'a, P: Parser, S, M> Iter<'a, P, S, M>
where
    S: BorrowMut<P::PartialState>,
{
    pub fn new(parser: P, mode: M, input: &'a mut P::Input, partial_state: S) -> Self {
        Iter {
            parser,
            input,
            consumed: false,
            state: State::Ok,
            partial_state,
            mode,
        }
    }
    /// Converts the iterator to a `ParseResult`, returning `Ok` if the parsing so far has be done
    /// without any errors which consumed data.
    pub fn into_result<O>(self, value: O) -> ParseResult<O, P::Input> {
        self.into_result_(value).into()
    }

    fn into_result_<O>(self, value: O) -> ConsumedResult<O, P::Input> {
        match self.state {
            State::Ok | State::EmptyErr => {
                if self.consumed {
                    ConsumedOk(value)
                } else {
                    EmptyOk(value)
                }
            }
            State::ConsumedErr(e) => ConsumedErr(e),
        }
    }

    fn into_result_fast<O>(self, value: &mut O) -> ConsumedResult<O, P::Input>
    where
        O: Default,
    {
        match self.state {
            State::Ok | State::EmptyErr => {
                let value = mem::replace(value, O::default());
                if self.consumed {
                    ConsumedOk(value)
                } else {
                    EmptyOk(value)
                }
            }
            State::ConsumedErr(e) => ConsumedErr(e),
        }
    }

    fn fail<T>(
        self,
        err: <<P::Input as StreamOnce>::Error as ParseError<
            <P::Input as StreamOnce>::Item,
            <P::Input as StreamOnce>::Range,
            <P::Input as StreamOnce>::Position,
        >>::StreamError,
    ) -> ConsumedResult<T, P::Input> {
        match self.state {
            State::Ok | State::EmptyErr => {
                let err = <P::Input as StreamOnce>::Error::from_error(self.input.position(), err);
                if self.consumed {
                    ConsumedErr(err)
                } else {
                    EmptyErr(err.into())
                }
            }
            State::ConsumedErr(mut e) => {
                e.add(err);
                ConsumedErr(e)
            }
        }
    }
}

impl<'a, P: Parser, S, M> Iterator for Iter<'a, P, S, M>
where
    S: BorrowMut<P::PartialState>,
    M: ParseMode,
{
    type Item = P::Output;

    fn next(&mut self) -> Option<P::Output> {
        let before = self.input.checkpoint();
        match self
            .parser
            .parse_mode(self.mode, self.input, self.partial_state.borrow_mut())
        {
            EmptyOk(v) => {
                self.mode.set_first();
                Some(v)
            }
            ConsumedOk(v) => {
                self.mode.set_first();
                self.consumed = true;
                Some(v)
            }
            EmptyErr(_) => {
                self.state = match self.input.reset(before) {
                    Err(err) => State::ConsumedErr(err),
                    Ok(_) => State::EmptyErr,
                };
                None
            }
            ConsumedErr(e) => {
                self.state = State::ConsumedErr(e);
                None
            }
        }
    }
}

#[derive(Copy, Clone)]
pub struct Many<F, P>(P, PhantomData<F>);

impl<F, P> Parser for Many<F, P>
where
    P: Parser,
    F: Extend<P::Output> + Default,
{
    type Input = P::Input;
    type Output = F;
    type PartialState = (F, P::PartialState);

    parse_mode!();
    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input>
    where
        M: ParseMode,
    {
        // TODO
        let (ref mut elements, ref mut child_state) = *state;

        let mut iter = (&mut self.0).partial_iter(mode, input, child_state);
        elements.extend(iter.by_ref());
        iter.into_result_fast(elements)
    }

    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.0.add_error(errors)
    }

    fn add_consumed_expected_error(
        &mut self,
        errors: &mut Tracked<<Self::Input as StreamOnce>::Error>,
    ) {
        self.add_error(errors);
    }

    fn parser_count(&self) -> ErrorOffset {
        self.0.parser_count()
    }
}

/// Parses `p` zero or more times returning a collection with the values from `p`.
///
/// If the returned collection cannot be inferred type annotations must be supplied, either by
/// annotating the resulting type binding `let collection: Vec<_> = ...` or by specializing when
/// calling many, `many::<Vec<_>, _>(...)`.
///
/// NOTE: If `p` can succeed without consuming any input this may hang forever as `many` will
/// repeatedly use `p` to parse the same location in the input every time
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::parser::char::digit;
/// # fn main() {
/// let result = many(digit())
///     .parse("123A")
///     .map(|x| x.0);
/// assert_eq!(result, Ok(vec!['1', '2', '3']));
/// # }
/// ```
#[inline(always)]
pub fn many<F, P>(p: P) -> Many<F, P>
where
    P: Parser,
    F: Extend<P::Output> + Default,
{
    Many(p, PhantomData)
}

#[derive(Copy, Clone)]
pub struct Many1<F, P>(P, PhantomData<fn() -> F>);
impl<F, P> Parser for Many1<F, P>
where
    F: Extend<P::Output> + Default,
    P: Parser,
{
    type Input = P::Input;
    type Output = F;
    type PartialState = (bool, bool, F, P::PartialState);

    parse_mode!();
    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        mut mode: M,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<F, P::Input>
    where
        M: ParseMode,
    {
        let (ref mut parsed_one, ref mut consumed_state, ref mut elements, ref mut child_state) =
            *state;

        if mode.is_first() || !*parsed_one {
            debug_assert!(!*parsed_one);

            let (first, consumed) = ctry!(self.0.parse_mode(mode, input, child_state));
            elements.extend(Some(first));
            // TODO Should EmptyOk be an error?
            *consumed_state = !consumed.is_empty();
            *parsed_one = true;
            mode.set_first();
        }

        let mut iter = Iter {
            parser: &mut self.0,
            consumed: *consumed_state,
            input,
            state: State::Ok,
            partial_state: child_state,
            mode,
        };
        elements.extend(iter.by_ref());

        iter.into_result_fast(elements).map(|x| {
            *parsed_one = false;
            x
        })
    }

    fn add_consumed_expected_error(
        &mut self,
        errors: &mut Tracked<<Self::Input as StreamOnce>::Error>,
    ) {
        self.add_error(errors);
    }

    forward_parser!(add_error parser_count, 0);
}

/// Parses `p` one or more times returning a collection with the values from `p`.
///
/// If the returned collection cannot be inferred type annotations must be supplied, either by
/// annotating the resulting type binding `let collection: Vec<_> = ...` or by specializing when
/// calling many1 `many1::<Vec<_>, _>(...)`.
///
/// NOTE: If `p` can succeed without consuming any input this may hang forever as `many1` will
/// repeatedly use `p` to parse the same location in the input every time
///
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::parser::char::digit;
/// # fn main() {
/// let result = many1::<Vec<_>, _>(digit())
///     .parse("A123");
/// assert!(result.is_err());
/// # }
/// ```
#[inline(always)]
pub fn many1<F, P>(p: P) -> Many1<F, P>
where
    F: Extend<P::Output> + Default,
    P: Parser,
{
    Many1(p, PhantomData)
}

#[derive(Clone)]
#[doc(hidden)]
// FIXME Should not be public
pub struct Sink;

impl Default for Sink {
    fn default() -> Self {
        Sink
    }
}

impl<A> Extend<A> for Sink {
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = A>,
    {
        for _ in iter {}
    }
}

impl_parser! { SkipMany(P,), Ignore<Many<Sink, Ignore<P>>> }

/// Parses `p` zero or more times ignoring the result.
///
/// NOTE: If `p` can succeed without consuming any input this may hang forever as `skip_many` will
/// repeatedly use `p` to parse the same location in the input every time
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::parser::char::digit;
/// # fn main() {
/// let result = skip_many(digit())
///     .parse("A");
/// assert_eq!(result, Ok(((), "A")));
/// # }
/// ```
#[inline(always)]
pub fn skip_many<P>(p: P) -> SkipMany<P>
where
    P: Parser,
{
    SkipMany(ignore(many(ignore(p))))
}

impl_parser! { SkipMany1(P,), Ignore<Many1<Sink, Ignore<P>>> }

/// Parses `p` one or more times ignoring the result.
///
/// NOTE: If `p` can succeed without consuming any input this may hang forever as `skip_many1` will
/// repeatedly use `p` to parse the same location in the input every time
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::parser::char::digit;
/// # fn main() {
/// let result = skip_many1(digit())
///     .parse("123A");
/// assert_eq!(result, Ok(((), "A")));
/// # }
/// ```
#[inline(always)]
pub fn skip_many1<P>(p: P) -> SkipMany1<P>
where
    P: Parser,
{
    SkipMany1(ignore(many1(ignore(p))))
}

#[derive(Copy, Clone)]
pub struct SepBy<F, P, S> {
    parser: P,
    separator: S,
    _marker: PhantomData<fn() -> F>,
}
impl<F, P, S> Parser for SepBy<F, P, S>
where
    F: Extend<P::Output> + Default,
    P: Parser,
    S: Parser<Input = P::Input>,
{
    type Input = P::Input;
    type Output = F;
    type PartialState = <Or<
        SepBy1<F, P, S>,
        FnParser<P::Input, fn(&mut Self::Input) -> ParseResult<F, Self::Input>>,
    > as Parser>::PartialState;

    parse_mode!();
    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<F, P::Input>
    where
        M: ParseMode,
    {
        sep_by1(&mut self.parser, &mut self.separator)
            .or(parser(|_| Ok((F::default(), Consumed::Empty(())))))
            .parse_mode(mode, input, state)
    }

    fn add_consumed_expected_error(
        &mut self,
        errors: &mut Tracked<<Self::Input as StreamOnce>::Error>,
    ) {
        self.separator.add_error(errors)
    }

    forward_parser!(add_error parser_count, parser);
}

/// Parses `parser` zero or more time separated by `separator`, returning a collection with the
/// values from `p`.
///
/// If the returned collection cannot be inferred type annotations must be supplied, either by
/// annotating the resulting type binding `let collection: Vec<_> = ...` or by specializing when
/// calling `sep_by`, `sep_by::<Vec<_>, _, _>(...)`.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::parser::char::digit;
/// # fn main() {
/// let mut parser = sep_by(digit(), token(','));
/// let result_ok = parser.parse("1,2,3");
/// assert_eq!(result_ok, Ok((vec!['1', '2', '3'], "")));
/// let result_ok2 = parser.parse("");
/// assert_eq!(result_ok2, Ok((vec![], "")));
/// # }
/// ```
#[inline(always)]
pub fn sep_by<F, P, S>(parser: P, separator: S) -> SepBy<F, P, S>
where
    F: Extend<P::Output> + Default,
    P: Parser,
    S: Parser<Input = P::Input>,
{
    SepBy {
        parser,
        separator,
        _marker: PhantomData,
    }
}

#[derive(Copy, Clone)]
pub struct SepBy1<F, P, S> {
    parser: P,
    separator: S,
    _marker: PhantomData<fn() -> F>,
}
impl<F, P, S> Parser for SepBy1<F, P, S>
where
    F: Extend<P::Output> + Default,
    P: Parser,
    S: Parser<Input = P::Input>,
{
    type Input = P::Input;
    type Output = F;
    type PartialState = (
        Option<Consumed<()>>,
        F,
        <With<S, P> as Parser>::PartialState,
    );

    parse_mode!();
    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input>
    where
        M: ParseMode,
    {
        let (ref mut parsed_one, ref mut elements, ref mut child_state) = *state;

        let rest = match *parsed_one {
            Some(rest) => rest,
            None => {
                let (first, rest) =
                    ctry!(self
                        .parser
                        .parse_mode(mode, input, &mut child_state.B.state));
                elements.extend(Some(first));
                rest
            }
        };

        rest.combine_consumed(move |_| {
            let rest = (&mut self.separator).with(&mut self.parser);
            let mut iter = Iter::new(rest, mode, input, child_state);

            elements.extend(iter.by_ref());

            iter.into_result_fast(elements).map(|x| {
                *parsed_one = None;
                x
            })
        })
    }

    fn add_consumed_expected_error(
        &mut self,
        errors: &mut Tracked<<Self::Input as StreamOnce>::Error>,
    ) {
        self.separator.add_error(errors)
    }

    forward_parser!(add_error parser_count, parser);
}

/// Parses `parser` one or more time separated by `separator`, returning a collection with the
/// values from `p`.
///
/// If the returned collection cannot be inferred type annotations must be supplied, either by
/// annotating the resulting type binding `let collection: Vec<_> = ...` or by specializing when
/// calling `sep_by`, `sep_by1::<Vec<_>, _, _>(...)`.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::parser::char::digit;
/// # use combine::stream::easy;
/// # use combine::stream::state::{State, SourcePosition};
/// # fn main() {
/// let mut parser = sep_by1(digit(), token(','));
/// let result_ok = parser.easy_parse(State::new("1,2,3"))
///                       .map(|(vec, state)| (vec, state.input));
/// assert_eq!(result_ok, Ok((vec!['1', '2', '3'], "")));
/// let result_err = parser.easy_parse(State::new(""));
/// assert_eq!(result_err, Err(easy::Errors {
///     position: SourcePosition::default(),
///     errors: vec![
///         easy::Error::end_of_input(),
///         easy::Error::Expected("digit".into())
///     ]
/// }));
/// # }
/// ```
#[inline(always)]
pub fn sep_by1<F, P, S>(parser: P, separator: S) -> SepBy1<F, P, S>
where
    F: Extend<P::Output> + Default,
    P: Parser,
    S: Parser<Input = P::Input>,
{
    SepBy1 {
        parser,
        separator,
        _marker: PhantomData,
    }
}

#[derive(Copy, Clone)]
pub struct SepEndBy<F, P, S> {
    parser: P,
    separator: S,
    _marker: PhantomData<fn() -> F>,
}

impl<F, P, S> Parser for SepEndBy<F, P, S>
where
    F: Extend<P::Output> + Default,
    P: Parser,
    S: Parser<Input = P::Input>,
{
    type Input = P::Input;
    type Output = F;
    type PartialState = <Or<
        SepEndBy1<F, P, S>,
        FnParser<P::Input, fn(&mut Self::Input) -> ParseResult<F, Self::Input>>,
    > as Parser>::PartialState;

    parse_mode!();
    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input>
    where
        M: ParseMode,
    {
        sep_end_by1(&mut self.parser, &mut self.separator)
            .or(parser(|_| Ok((F::default(), Consumed::Empty(())))))
            .parse_mode(mode, input, state)
    }

    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.parser.add_error(errors)
    }
}

/// Parses `parser` zero or more times separated and ended by `separator`, returning a collection
/// with the values from `p`.
///
/// If the returned collection cannot be inferred type annotations must be supplied, either by
/// annotating the resulting type binding `let collection: Vec<_> = ...` or by specializing when
/// calling `sep_by`, `sep_by::<Vec<_>, _, _>(...)`
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::parser::char::digit;
/// # fn main() {
/// let mut parser = sep_end_by(digit(), token(';'));
/// let result_ok = parser.parse("1;2;3;");
/// assert_eq!(result_ok, Ok((vec!['1', '2', '3'], "")));
/// let result_ok2 = parser.parse("1;2;3");
/// assert_eq!(result_ok2, Ok((vec!['1', '2', '3'], "")));
/// # }
/// ```
#[inline(always)]
pub fn sep_end_by<F, P, S>(parser: P, separator: S) -> SepEndBy<F, P, S>
where
    F: Extend<P::Output> + Default,
    P: Parser,
    S: Parser<Input = P::Input>,
{
    SepEndBy {
        parser,
        separator,
        _marker: PhantomData,
    }
}

#[derive(Copy, Clone)]
pub struct SepEndBy1<F, P, S> {
    parser: P,
    separator: S,
    _marker: PhantomData<fn() -> F>,
}

impl<F, P, S> Parser for SepEndBy1<F, P, S>
where
    F: Extend<P::Output> + Default,
    P: Parser,
    S: Parser<Input = P::Input>,
{
    type Input = P::Input;
    type Output = F;
    type PartialState = (
        Option<Consumed<()>>,
        F,
        <With<S, Optional<P>> as Parser>::PartialState,
    );

    parse_mode!();
    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input>
    where
        M: ParseMode,
    {
        let (ref mut parsed_one, ref mut elements, ref mut child_state) = *state;

        let rest = match *parsed_one {
            Some(rest) => rest,
            None => {
                let (first, rest) =
                    ctry!(self
                        .parser
                        .parse_mode(mode, input, &mut child_state.B.state));
                elements.extend(Some(first));
                rest
            }
        };

        rest.combine_consumed(|_| {
            let rest = (&mut self.separator).with(optional(&mut self.parser));
            let mut iter = Iter::new(rest, mode, input, child_state);

            // Parse elements until `self.parser` returns `None`
            elements.extend(iter.by_ref().scan((), |_, x| x));

            iter.into_result_fast(elements).map(|x| {
                *parsed_one = None;
                x
            })
        })
    }

    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.parser.add_error(errors)
    }
}

/// Parses `parser` one or more times separated and ended by `separator`, returning a collection
/// with the values from `p`.
///
/// If the returned collection cannot be inferred type annotations must be
/// supplied, either by annotating the resulting type binding `let collection: Vec<_> = ...` or by
/// specializing when calling `sep_by`, `sep_by1::<Vec<_>, _, _>(...)`.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::parser::char::digit;
/// # use combine::stream::easy;
/// # use combine::stream::state::{State, SourcePosition};
/// # fn main() {
/// let mut parser = sep_end_by1(digit(), token(';'));
/// let result_ok = parser.easy_parse(State::new("1;2;3;"))
///                       .map(|(vec, state)| (vec, state.input));
/// assert_eq!(result_ok, Ok((vec!['1', '2', '3'], "")));
/// let result_err = parser.easy_parse(State::new(""));
/// assert_eq!(result_err, Err(easy::Errors {
///     position: SourcePosition::default(),
///     errors: vec![
///         easy::Error::end_of_input(),
///         easy::Error::Expected("digit".into())
///     ]
/// }));
/// # }
/// ```
#[inline(always)]
pub fn sep_end_by1<F, P, S>(parser: P, separator: S) -> SepEndBy1<F, P, S>
where
    F: Extend<P::Output> + Default,
    P: Parser,
    S: Parser<Input = P::Input>,
{
    SepEndBy1 {
        parser,
        separator,
        _marker: PhantomData,
    }
}

#[derive(Copy, Clone)]
pub struct Chainl1<P, Op>(P, Op);
impl<I, P, Op> Parser for Chainl1<P, Op>
where
    I: Stream,
    P: Parser<Input = I>,
    Op: Parser<Input = I>,
    Op::Output: FnOnce(P::Output, P::Output) -> P::Output,
{
    type Input = I;
    type Output = P::Output;
    type PartialState = (
        Option<(P::Output, Consumed<()>)>,
        <(Op, P) as Parser>::PartialState,
    );

    parse_mode!();
    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        mut mode: M,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input>
    where
        M: ParseMode,
    {
        let (ref mut l_state, ref mut child_state) = *state;

        let (mut l, mut consumed) = match l_state.take() {
            Some(x) => x,
            None => {
                let x = ctry!(self.0.parse_partial(input, &mut child_state.B.state));
                mode.set_first();
                x
            }
        };

        loop {
            let before = input.checkpoint();
            match (&mut self.1, &mut self.0)
                .parse_mode(mode, input, child_state)
                .into()
            {
                Ok(((op, r), rest)) => {
                    l = op(l, r);
                    consumed = consumed.merge(rest);
                    mode.set_first();
                }
                Err(Consumed::Consumed(err)) => {
                    *l_state = Some((l, consumed));
                    return ConsumedErr(err.error);
                }
                Err(Consumed::Empty(_)) => {
                    ctry!(input.reset(before).consumed());
                    break;
                }
            }
        }
        Ok((l, consumed)).into()
    }

    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.0.add_error(errors)
    }
}

/// Parses `p` 1 or more times separated by `op`. The value returned is the one produced by the
/// left associative application of the function returned by the parser `op`.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::parser::char::digit;
/// # fn main() {
/// let number = digit().map(|c: char| c.to_digit(10).unwrap());
/// let sub = token('-').map(|_| |l: u32, r: u32| l - r);
/// let mut parser = chainl1(number, sub);
/// assert_eq!(parser.parse("9-3-5"), Ok((1, "")));
/// # }
/// ```
#[inline(always)]
pub fn chainl1<P, Op>(parser: P, op: Op) -> Chainl1<P, Op>
where
    P: Parser,
    Op: Parser<Input = P::Input>,
    Op::Output: FnOnce(P::Output, P::Output) -> P::Output,
{
    Chainl1(parser, op)
}

#[derive(Copy, Clone)]
pub struct Chainr1<P, Op>(P, Op);
impl<I, P, Op> Parser for Chainr1<P, Op>
where
    I: Stream,
    P: Parser<Input = I>,
    Op: Parser<Input = I>,
    Op::Output: FnOnce(P::Output, P::Output) -> P::Output,
{
    type Input = I;
    type Output = P::Output;
    type PartialState = ();
    #[inline]
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<P::Output, I> {
        // FIXME FastResult
        let (mut l, mut consumed) = ctry!(self.0.parse_lazy(input));
        loop {
            let before = input.checkpoint();
            let op = match self.1.parse_lazy(input).into() {
                Ok((x, rest)) => {
                    consumed = consumed.merge(rest);
                    x
                }
                Err(Consumed::Consumed(err)) => return ConsumedErr(err.error),
                Err(Consumed::Empty(_)) => {
                    ctry!(input.reset(before).consumed());
                    break;
                }
            };
            let before = input.checkpoint();
            match self.parse_lazy(input).into() {
                Ok((r, rest)) => {
                    l = op(l, r);
                    consumed = consumed.merge(rest);
                }
                Err(Consumed::Consumed(err)) => return ConsumedErr(err.error),
                Err(Consumed::Empty(_)) => {
                    ctry!(input.reset(before).consumed());
                    break;
                }
            }
        }
        Ok((l, consumed)).into()
    }
    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.0.add_error(errors)
    }
}

/// Parses `p` one or more times separated by `op`. The value returned is the one produced by the
/// right associative application of the function returned by `op`.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::parser::char::digit;
/// # fn main() {
/// let number = digit().map(|c: char| c.to_digit(10).unwrap());
/// let pow = token('^').map(|_| |l: u32, r: u32| l.pow(r));
/// let mut parser = chainr1(number, pow);
///     assert_eq!(parser.parse("2^3^2"), Ok((512, "")));
/// }
/// ```
#[inline(always)]
pub fn chainr1<P, Op>(parser: P, op: Op) -> Chainr1<P, Op>
where
    P: Parser,
    Op: Parser<Input = P::Input>,
    Op::Output: FnOnce(P::Output, P::Output) -> P::Output,
{
    Chainr1(parser, op)
}

#[derive(Copy, Clone)]
pub struct TakeUntil<F, P> {
    end: P,
    _marker: PhantomData<fn() -> F>,
}
impl<F, P> Parser for TakeUntil<F, P>
where
    F: Extend<<P::Input as StreamOnce>::Item> + Default,
    P: Parser,
{
    type Input = P::Input;
    type Output = F;
    type PartialState = (F, P::PartialState);

    parse_mode!();
    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input>
    where
        M: ParseMode,
    {
        let (ref mut output, ref mut end_state) = *state;

        let mut consumed = Consumed::Empty(());
        loop {
            let before = input.checkpoint();
            match self.end.parse_mode(mode, input, end_state).into() {
                Ok((_, rest)) => {
                    ctry!(input.reset(before).consumed());
                    return match consumed.merge(rest) {
                        Consumed::Consumed(()) => ConsumedOk(mem::replace(output, F::default())),
                        Consumed::Empty(()) => EmptyOk(mem::replace(output, F::default())),
                    };
                }
                Err(Consumed::Empty(_)) => {
                    ctry!(input.reset(before).consumed());
                    output.extend(Some(ctry!(uncons(input)).0));
                    consumed = Consumed::Consumed(());
                }
                Err(Consumed::Consumed(e)) => {
                    ctry!(input.reset(before).consumed());
                    return ConsumedErr(e.error);
                }
            };
        }
    }
}

/// Takes input until `end` is encountered or `end` indicates that it has consumed input before
/// failing (`attempt` can be used to make it look like it has not consumed any input)
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::parser::char;
/// # use combine::parser::byte;
/// # use combine::parser::combinator::attempt;
/// # use combine::parser::repeat::take_until;
/// # fn main() {
///     let mut char_parser = take_until(char::digit());
///     assert_eq!(char_parser.parse("abc123"), Ok(("abc".to_string(), "123")));
///
///     let mut byte_parser = take_until(byte::bytes(&b"TAG"[..]));
///     assert_eq!(byte_parser.parse(&b"123TAG"[..]), Ok((b"123".to_vec(), &b"TAG"[..])));
///     assert!(byte_parser.parse(&b"123TATAG"[..]).is_err());
///
///     // `attempt` must be used if the `end` should be consume input before failing
///     let mut byte_parser = take_until(attempt(byte::bytes(&b"TAG"[..])));
///     assert_eq!(byte_parser.parse(&b"123TATAG"[..]), Ok((b"123TA".to_vec(), &b"TAG"[..])));
/// }
/// ```
#[inline(always)]
pub fn take_until<F, P>(end: P) -> TakeUntil<F, P>
where
    F: Extend<<P::Input as StreamOnce>::Item> + Default,
    P: Parser,
{
    TakeUntil {
        end,
        _marker: PhantomData,
    }
}

parser! {
    #[derive(Copy, Clone)]
    pub struct SkipUntil;
    type PartialState = <With<TakeUntil<Sink, P>, Value<P::Input, ()>> as Parser>::PartialState;
    /// Skips input until `end` is encountered or `end` indicates that it has consumed input before
    /// failing (`attempt` can be used to make it look like it has not consumed any input)
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::parser::char;
    /// # use combine::parser::byte;
    /// # use combine::parser::combinator::attempt;
    /// # use combine::parser::repeat::skip_until;
    /// # fn main() {
    ///     let mut char_parser = skip_until(char::digit());
    ///     assert_eq!(char_parser.parse("abc123"), Ok(((), "123")));
    ///
    ///     let mut byte_parser = skip_until(byte::bytes(&b"TAG"[..]));
    ///     assert_eq!(byte_parser.parse(&b"123TAG"[..]), Ok(((), &b"TAG"[..])));
    ///     assert!(byte_parser.parse(&b"123TATAG"[..]).is_err());
    ///
    ///     // `attempt` must be used if the `end` should be consume input before failing
    ///     let mut byte_parser = skip_until(attempt(byte::bytes(&b"TAG"[..])));
    ///     assert_eq!(byte_parser.parse(&b"123TATAG"[..]), Ok(((), &b"TAG"[..])));
    /// }
    /// ```
    pub fn skip_until[P](end: P)(P::Input) -> ()
    where [
        P: Parser,
    ]
    {
        take_until::<Sink, _>(end).with(value(()))
    }
}

#[derive(Default)]
pub struct EscapedState<T, U>(PhantomData<(T, U)>);

pub struct Escaped<P, Q>
where
    P: Parser,
{
    parser: P,
    escape: <P::Input as StreamOnce>::Item,
    escape_parser: Q,
}
impl<P, Q> Parser for Escaped<P, Q>
where
    P: Parser,
    <P::Input as StreamOnce>::Item: PartialEq,
    Q: Parser<Input = P::Input>,
{
    type Input = P::Input;
    type Output = ();
    type PartialState = EscapedState<P::PartialState, Q::PartialState>;

    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        let mut consumed = Consumed::Empty(());
        loop {
            match self.parser.parse_lazy(input) {
                EmptyOk(_) => {}
                ConsumedOk(_) => {
                    consumed = Consumed::Consumed(());
                }
                EmptyErr(_) => {
                    let checkpoint = input.checkpoint();
                    match uncons(input) {
                        ConsumedOk(ref c) | EmptyOk(ref c) if *c == self.escape => {
                            match self.escape_parser.parse_stream_consumed(input) {
                                EmptyOk(_) => {}
                                ConsumedOk(_) => {
                                    consumed = Consumed::Consumed(());
                                }
                                ConsumedErr(err) => return ConsumedErr(err),
                                EmptyErr(err) => {
                                    return ConsumedErr(err.error);
                                }
                            }
                        }
                        ConsumedErr(err) => {
                            return ConsumedErr(err);
                        }
                        _ => {
                            ctry!(input.reset(checkpoint).consumed());
                            return if consumed.is_empty() {
                                EmptyOk(())
                            } else {
                                ConsumedOk(())
                            };
                        }
                    }
                }
                ConsumedErr(err) => return ConsumedErr(err),
            }
        }
    }

    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        use crate::error::Info;
        self.parser.add_error(errors);

        errors.error.add_expected(Info::Token(self.escape.clone()));
    }
}

/// Parses an escaped string by first applying `parser` which accept the normal characters which do
/// not need escaping. Once `parser` can not consume any more input it checks if the next item
/// is `escape`. If it is then `escape_parser` is used to parse the escaped character and then
/// resumes parsing using `parser`. If `escape` was not found then the parser finishes
/// successfully.
///
/// This returns `()` since there isn't a good way to collect the output of the parsers so it is
/// best paired with one of the `recognize` parsers.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::parser::repeat::escaped;
/// # use combine::parser::char;
/// # use combine::parser::range::{recognize, take_while1};
/// # fn main() {
///     let mut parser = recognize(
///         escaped(take_while1(|c| c != '"' && c != '\\'), '\\', one_of(r#"nr"\"#.chars()))
///     );
///     assert_eq!(parser.parse(r#"ab\"12\n\rc""#), Ok((r#"ab\"12\n\rc"#, r#"""#)));
///     assert!(parser.parse(r#"\"#).is_err());
///     assert!(parser.parse(r#"\a"#).is_err());
/// }
/// ```
#[inline(always)]
pub fn escaped<P, Q>(
    parser: P,
    escape: <P::Input as StreamOnce>::Item,
    escape_parser: Q,
) -> Escaped<P, Q>
where
    P: Parser,
    <P::Input as StreamOnce>::Item: PartialEq,
    Q: Parser<Input = P::Input>,
{
    Escaped {
        parser,
        escape,
        escape_parser,
    }
}

use lib::marker::PhantomData;
use lib::borrow::BorrowMut;
use lib::iter::FromIterator;
use lib::mem;

use Parser;
use stream::{Positioned, Resetable, Stream, StreamOnce};
use parser::sequence::With;
use parser::choice::Or;
use combinator::{ignore, optional, parser, value, FnParser, Ignore, Optional};
use error::{Consumed, ConsumedResult, ParseError, ParseMode, ParseResult, StreamError, Tracked};

use error::FastResult::*;

#[derive(Copy, Clone)]
pub struct Count<F, P> {
    parser: P,
    count: usize,
    _marker: PhantomData<fn() -> F>,
}

impl<P, F> Parser for Count<F, P>
where
    P: Parser,
    F: FromIterator<P::Output> + Extend<P::Output> + Default,
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
                .take(self.count - *count)
                .inspect(|_| *count += 1),
        );

        iter.into_result_fast(elements)
    }

    fn add_error(&mut self, error: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.parser.add_error(error)
    }
}

/// Parses `parser` from zero up to `count` times.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::error::Info;
/// # use combine::easy::Error;
/// # fn main() {
/// let mut parser = count(2, token(b'a'));
///
/// let result = parser.parse(&b"aaab"[..]);
/// assert_eq!(result, Ok((b"aa"[..].to_owned(), &b"ab"[..])));
/// # }
/// ```
#[inline(always)]
pub fn count<F, P>(count: usize, parser: P) -> Count<F, P>
where
    P: Parser,
    F: FromIterator<P::Output> + Extend<P::Output> + Default,
{
    Count {
        parser: parser,
        count: count,
        _marker: PhantomData,
    }
}

parser!{
    #[derive(Copy, Clone)]
    pub struct SkipCount;
    /// Parses `parser` from zero up to `count` times skipping the output of `parser`.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::easy::{Error, Info};
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
        ::combinator::count::<Sink<()>, _>(*count, parser.map(|_| ())).with(value(()))
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
    F: FromIterator<P::Output> + Extend<P::Output> + Default,
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
/// # use combine::easy::{Error, Info};
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
    F: FromIterator<P::Output> + Extend<P::Output> + Default,
{
    assert!(min <= max);

    CountMinMax {
        parser: parser,
        min: min,
        max: max,
        _marker: PhantomData,
    }
}

parser!{
    #[derive(Copy, Clone)]
    pub struct SkipCountMinMax;
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
        ::combinator::count_min_max::<Sink<()>, _>(*min, *max, parser.map(|_| ())).with(value(()))
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
        match self.state {
            State::Ok => {
                let before = self.input.checkpoint();
                match self.parser
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
                        self.input.reset(before);
                        self.state = State::EmptyErr;
                        None
                    }
                    ConsumedErr(e) => {
                        self.state = State::ConsumedErr(e);
                        None
                    }
                }
            }
            State::ConsumedErr(_) | State::EmptyErr => None,
        }
    }
}

#[derive(Copy, Clone)]
pub struct Many<F, P>(P, PhantomData<F>);

impl<F, P> Parser for Many<F, P>
where
    P: Parser,
    F: FromIterator<P::Output> + Extend<P::Output> + Default,
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
}

/// Parses `p` zero or more times returning a collection with the values from `p`.
///
/// If the returned collection cannot be inferred type annotations must be supplied, either by
/// annotating the resulting type binding `let collection: Vec<_> = ...` or by specializing when
/// calling many, `many::<Vec<_>, _>(...)`.
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
    F: FromIterator<P::Output> + Extend<P::Output> + Default,
{
    Many(p, PhantomData)
}

#[derive(Copy, Clone)]
pub struct Many1<F, P>(P, PhantomData<fn() -> F>);
impl<F, P> Parser for Many1<F, P>
where
    F: FromIterator<P::Output> + Extend<P::Output> + Default,
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
            input: input,
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
    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.0.add_error(errors)
    }
}

/// Parses `p` one or more times returning a collection with the values from `p`.
///
/// If the returned collection cannot be inferred type annotations must be supplied, either by
/// annotating the resulting type binding `let collection: Vec<_> = ...` or by specializing when
/// calling many1 `many1::<Vec<_>, _>(...)`.
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
    F: FromIterator<P::Output> + Extend<P::Output> + Default,
    P: Parser,
{
    Many1(p, PhantomData)
}

#[derive(Clone)]
#[doc(hidden)]
// FIXME Should not be public
pub struct Sink<T>(PhantomData<T>);

impl<T> Default for Sink<T> {
    fn default() -> Self {
        Sink(PhantomData)
    }
}

impl<A> Extend<A> for Sink<A> {
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = A>,
    {
        for _ in iter {}
    }
}

impl<A> FromIterator<A> for Sink<A> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = A>,
    {
        for _ in iter {}
        Sink(PhantomData)
    }
}

impl_parser!{ SkipMany(P,), Ignore<Many<Sink<()>, Ignore<P>>> }

/// Parses `p` zero or more times ignoring the result.
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

impl_parser!{ SkipMany1(P,), Ignore<Many1<Sink<()>, Ignore<P>>> }

/// Parses `p` one or more times ignoring the result.
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
    F: FromIterator<P::Output> + Extend<P::Output> + Default,
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
            .or(parser(|_| {
                Ok((None.into_iter().collect(), Consumed::Empty(())))
            }))
            .parse_mode(mode, input, state)
    }

    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.parser.add_error(errors)
    }
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
    F: FromIterator<P::Output> + Extend<P::Output> + Default,
    P: Parser,
    S: Parser<Input = P::Input>,
{
    SepBy {
        parser: parser,
        separator: separator,
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
    F: FromIterator<P::Output> + Extend<P::Output> + Default,
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
                let (first, rest) = ctry!(self.parser.parse_mode(
                    mode,
                    input,
                    &mut child_state.B.state
                ));
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

    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.parser.add_error(errors)
    }
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
/// # use combine::easy;
/// # use combine::state::SourcePosition;
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
    F: FromIterator<P::Output> + Extend<P::Output> + Default,
    P: Parser,
    S: Parser<Input = P::Input>,
{
    SepBy1 {
        parser: parser,
        separator: separator,
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
    F: FromIterator<P::Output> + Extend<P::Output> + Default,
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
            .or(parser(|_| {
                Ok((None.into_iter().collect(), Consumed::Empty(())))
            }))
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
    F: FromIterator<P::Output> + Extend<P::Output> + Default,
    P: Parser,
    S: Parser<Input = P::Input>,
{
    SepEndBy {
        parser: parser,
        separator: separator,
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
    F: FromIterator<P::Output> + Extend<P::Output> + Default,
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
                let (first, rest) = ctry!(self.parser.parse_mode(
                    mode,
                    input,
                    &mut child_state.B.state
                ));
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
/// # use combine::easy;
/// # use combine::state::SourcePosition;
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
    F: FromIterator<P::Output> + Extend<P::Output> + Default,
    P: Parser,
    S: Parser<Input = P::Input>,
{
    SepEndBy1 {
        parser: parser,
        separator: separator,
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
                    input.reset(before);
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
                    input.reset(before);
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
                    input.reset(before);
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

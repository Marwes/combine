use lib::iter::FromIterator;
use lib::marker::PhantomData;
use lib::mem;
use lib::borrow::BorrowMut;

use Parser;
use primitives::{Consumed, ConsumedResult, Info, ParseError, ParseMode, ParseResult, StreamError,
                 Tracked, UnexpectedParse};
use stream::{Positioned, Resetable, Stream, StreamOnce};

use either::Either;

use primitives::FastResult::*;

#[doc(inline)]
pub use parser::sequence::*;
#[doc(inline)]
pub use parser::choice::*;
#[doc(inline)]
pub use parser::item::*;

macro_rules! impl_parser {
    ($name: ident ($first: ident, $($ty_var: ident),*), $inner_type: ty) => {
    #[derive(Clone)]
    pub struct $name<$first $(,$ty_var)*>($inner_type)
        where $first: Parser $(,$ty_var : Parser<Input=<$first as Parser>::Input>)*;
    impl <$first, $($ty_var),*> Parser for $name<$first $(,$ty_var)*>
        where $first: Parser $(, $ty_var : Parser<Input=<$first as Parser>::Input>)* {
        type Input = <$first as Parser>::Input;
        type Output = <$inner_type as Parser>::Output;
        type PartialState = <$inner_type as Parser>::PartialState;
        fn parse_lazy(
            &mut self,
            input: &mut Self::Input,
        ) -> ConsumedResult<Self::Output, Self::Input> {
            self.0.parse_lazy(input)
        }
        fn parse_partial(
            &mut self,
            input: &mut Self::Input,
            state: &mut Self::PartialState,
        ) -> ConsumedResult<Self::Output, Self::Input> {
            self.0.parse_partial(input, state)
        }
        fn add_error(&mut self, error: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
            self.0.add_error(error)
        }
    }
}
}

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
/// # use combine::primitives::Info;
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

#[derive(Clone)]
pub struct Unexpected<I>(Info<I::Item, I::Range>, PhantomData<fn(I) -> I>)
where
    I: Stream;
impl<I> Parser for Unexpected<I>
where
    I: Stream,
{
    type Input = I;
    type Output = ();
    type PartialState = ();
    #[inline]
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<(), I> {
        EmptyErr(<Self::Input as StreamOnce>::Error::empty(input.position()).into())
    }
    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        errors.error.add(StreamError::unexpected(self.0.clone()));
    }
}
/// Always fails with `message` as an unexpected error.
/// Never consumes any input.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::primitives::StreamError;
/// # fn main() {
/// let result = unexpected("token")
///     .easy_parse("a");
/// assert!(result.is_err());
/// assert!(
///     result.err()
///         .unwrap()
///         .errors
///         .iter()
///         .any(|m| *m == StreamError::unexpected("token".into()))
/// );
/// # }
/// ```
#[inline(always)]
pub fn unexpected<I, S>(message: S) -> Unexpected<I>
where
    I: Stream,
    S: Into<Info<I::Item, I::Range>>,
{
    Unexpected(message.into(), PhantomData)
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

parser!{
#[derive(Copy, Clone)]
pub struct NotFollowedBy;
/// Succeeds only if `parser` fails.
/// Never consumes any input.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::parser::char::{alpha_num, string};
/// # fn main() {
/// let result = string("let")
///     .skip(not_followed_by(alpha_num()))
///     .parse("letx")
///     .map(|x| x.0);
/// assert!(result.is_err());
/// # }
/// ```
#[inline(always)]
pub fn not_followed_by[P](parser: P)(P::Input) -> ()
where [
    P: Parser,
    P::Output: Into<Info<<P::Input as StreamOnce>::Item, <P::Input as StreamOnce>::Range>>,
]
{
    try(try(parser).then(unexpected)
        .or(value(())))
}
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
        match input.uncons::<UnexpectedParse>() {
            Err(ref err) if *err == UnexpectedParse::Eoi => EmptyOk(()),
            _ => {
                input.reset(before);
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
/// # use combine::easy;
/// # use combine::state::SourcePosition;
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
    SkipMany(Ignore(many(Ignore(p))))
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
    SkipMany1(Ignore(many1(Ignore(p))))
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

impl<'a, I: Stream, O> Parser for FnMut(&mut I) -> ParseResult<O, I> + 'a {
    type Input = I;
    type Output = O;
    type PartialState = ();
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<O, I> {
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
/// # use combine::primitives::{Consumed, StreamError};
/// # use combine::easy;
/// # fn main() {
/// let mut even_digit = parser(|input| {
///     // Help type inference out
///     let _: &mut easy::Stream<&str> = input;
///     let position = input.position();
///     let (char_digit, consumed) = try!(digit().parse_stream(input));
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
    F: FnMut(&mut I) -> ParseResult<O, I>,
{
    FnParser(f, PhantomData)
}

impl<I, O, F> Parser for FnParser<I, F>
where
    I: Stream,
    F: FnMut(&mut I) -> ParseResult<O, I>,
{
    type Input = I;
    type Output = O;
    type PartialState = ();
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<O, I> {
        (self.0)(input).into()
    }
}

impl<I, O> Parser for fn(&mut I) -> ParseResult<O, I>
where
    I: Stream,
{
    type Input = I;
    type Output = O;
    type PartialState = ();
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<O, I> {
        self(input).into()
    }
}

#[derive(Copy, Clone)]
pub struct Optional<P>(P);
impl<P> Parser for Optional<P>
where
    P: Parser,
{
    type Input = P::Input;
    type Output = Option<P::Output>;
    type PartialState = P::PartialState;

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
        let before = input.checkpoint();
        match self.0.parse_mode(mode, input, state) {
            EmptyOk(x) => EmptyOk(Some(x)),
            ConsumedOk(x) => ConsumedOk(Some(x)),
            ConsumedErr(err) => ConsumedErr(err),
            EmptyErr(_) => {
                input.reset(before);
                EmptyOk(None)
            }
        }
    }

    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.0.add_error(errors)
    }
}

/// Parses `parser` and outputs `Some(value)` if it succeeds, `None` if it fails without
/// consuming any input. Fails if `parser` fails after having consumed some input.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::parser::char::string;
/// # fn main() {
/// let mut parser = optional(string("hello"));
/// assert_eq!(parser.parse("hello"), Ok((Some("hello"), "")));
/// assert_eq!(parser.parse("world"), Ok((None, "world")));
/// assert!(parser.parse("heya").is_err());
/// # }
/// ```
#[inline(always)]
pub fn optional<P>(parser: P) -> Optional<P>
where
    P: Parser,
{
    Optional(parser)
}

impl_parser! { Between(L, R, P), Skip<With<L, P>, R> }
/// Parses `open` followed by `parser` followed by `close`.
/// Returns the value of `parser`.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::parser::char::string;
/// # fn main() {
/// let result = between(token('['), token(']'), string("rust"))
///     .parse("[rust]")
///     .map(|x| x.0);
/// assert_eq!(result, Ok("rust"));
/// # }
/// ```
#[inline(always)]
pub fn between<I, L, R, P>(open: L, close: R, parser: P) -> Between<L, R, P>
where
    I: Stream,
    L: Parser<Input = I>,
    R: Parser<Input = I>,
    P: Parser<Input = I>,
{
    Between(open.with(parser).skip(close))
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

#[derive(Copy, Clone)]
pub struct Try<P>(P);
impl<I, O, P> Parser for Try<P>
where
    I: Stream,
    P: Parser<Input = I, Output = O>,
{
    type Input = I;
    type Output = O;
    type PartialState = ();
    #[inline]
    fn parse_stream_consumed(&mut self, input: &mut Self::Input) -> ConsumedResult<O, I> {
        self.parse_lazy(input)
    }
    #[inline]
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<O, I> {
        self.0
            .parse_stream(input)
            .map_err(Consumed::into_empty)
            .into()
    }
}

/// `try(p)` behaves as `p` except it acts as if the parser hadn't consumed any input if `p` fails
/// after consuming input.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::parser::char::string;
/// # fn main() {
/// let mut p = try(string("let"))
///     .or(string("lex"));
/// let result = p.parse("lex").map(|x| x.0);
/// assert_eq!(result, Ok("lex"));
/// let result = p.parse("aet").map(|x| x.0);
/// assert!(result.is_err());
/// # }
/// ```
#[inline(always)]
pub fn try<P>(p: P) -> Try<P>
where
    P: Parser,
{
    Try(p)
}

#[derive(Copy, Clone)]
pub struct LookAhead<P>(P);

impl<I, O, P> Parser for LookAhead<P>
where
    I: Stream,
    P: Parser<Input = I, Output = O>,
{
    type Input = I;
    type Output = O;
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<O, I> {
        let before = input.checkpoint();
        let result = self.0.parse_lazy(input);
        input.reset(before);
        let (o, _input) = ctry!(result);
        EmptyOk(o)
    }

    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.0.add_error(errors);
    }
}

/// `look_ahead(p)` acts as `p` but doesn't consume input on success.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::parser::char::string;
/// # fn main() {
/// let mut p = look_ahead(string("test"));
///
/// let result = p.parse("test str");
/// assert_eq!(result, Ok(("test", "test str")));
///
/// let result = p.parse("aet");
/// assert!(result.is_err());
/// # }
/// ```
#[inline(always)]
pub fn look_ahead<P>(p: P) -> LookAhead<P>
where
    P: Parser,
{
    LookAhead(p)
}

#[derive(Clone)]
pub struct Message<P>(
    P,
    Info<<P::Input as StreamOnce>::Item, <P::Input as StreamOnce>::Range>,
)
where
    P: Parser;
impl<I, P> Parser for Message<P>
where
    I: Stream,
    P: Parser<Input = I>,
{
    type Input = I;
    type Output = P::Output;
    type PartialState = P::PartialState;

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
        match self.0.parse_mode(mode, input, state) {
            ConsumedOk(x) => ConsumedOk(x),
            EmptyOk(x) => EmptyOk(x),

            // The message should always be added even if some input was consumed before failing
            ConsumedErr(mut err) => {
                err.add_message(self.1.clone());
                ConsumedErr(err)
            }

            // The message will be added in `add_error`
            EmptyErr(err) => EmptyErr(err),
        }
    }

    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.0.add_error(errors);
        errors.error.add_message(self.1.clone());
    }
}

/// Equivalent to [`p1.message(msg)`].
///
/// [`p1.message(msg)`]: ../primitives/trait.Parser.html#method.message
#[inline(always)]
pub fn message<P>(
    p: P,
    msg: Info<<P::Input as StreamOnce>::Item, <P::Input as StreamOnce>::Range>,
) -> Message<P>
where
    P: Parser,
{
    Message(p, msg)
}

#[derive(Copy, Clone)]
pub struct Map<P, F>(P, F)
where
    P: Parser;
impl<I, A, B, P, F> Parser for Map<P, F>
where
    I: Stream,
    P: Parser<Input = I, Output = A>,
    F: FnMut(A) -> B,
{
    type Input = I;
    type Output = B;
    type PartialState = P::PartialState;

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
        match self.0.parse_mode(mode, input, state) {
            ConsumedOk(x) => ConsumedOk((self.1)(x)),
            EmptyOk(x) => EmptyOk((self.1)(x)),
            ConsumedErr(err) => ConsumedErr(err),
            EmptyErr(err) => EmptyErr(err),
        }
    }

    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.0.add_error(errors);
    }
}

/// Equivalent to [`p.map(f)`].
///
/// [`p.map(f)`]: ../primitives/trait.Parser.html#method.map
#[inline(always)]
pub fn map<P, F, B>(p: P, f: F) -> Map<P, F>
where
    P: Parser,
    F: FnMut(P::Output) -> B,
{
    Map(p, f)
}

#[derive(Copy, Clone)]
pub struct FlatMap<P, F>(P, F);
impl<I, A, B, P, F> Parser for FlatMap<P, F>
where
    I: Stream,
    P: Parser<Input = I, Output = A>,
    F: FnMut(A) -> Result<B, I::Error>,
{
    type Input = I;
    type Output = B;
    type PartialState = P::PartialState;

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
        match self.0.parse_mode(mode, input, state) {
            EmptyOk(o) => match (self.1)(o) {
                Ok(x) => EmptyOk(x),
                Err(err) => EmptyErr(err.into()),
            },
            ConsumedOk(o) => match (self.1)(o) {
                Ok(x) => ConsumedOk(x),
                Err(err) => ConsumedErr(err.into()),
            },
            EmptyErr(err) => EmptyErr(err),
            ConsumedErr(err) => ConsumedErr(err),
        }
    }

    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.0.add_error(errors);
    }
}

/// Equivalent to [`p.flat_map(f)`].
///
/// [`p.flat_map(f)`]: ../primitives/trait.Parser.html#method.flat_map
#[inline(always)]
pub fn flat_map<P, F, B>(p: P, f: F) -> FlatMap<P, F>
where
    P: Parser,
    F: FnMut(P::Output) -> Result<B, <P::Input as StreamOnce>::Error>,
{
    FlatMap(p, f)
}

#[derive(Copy, Clone)]
pub struct Then<P, F>(P, F);
impl<P, N, F> Parser for Then<P, F>
where
    F: FnMut(P::Output) -> N,
    P: Parser,
    N: Parser<Input = P::Input>,
{
    type Input = N::Input;
    type Output = N::Output;
    type PartialState = (P::PartialState, Option<(bool, N)>, N::PartialState);

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
        let (ref mut p_state, ref mut n_parser_cache, ref mut n_state) = *state;

        if mode.is_first() || n_parser_cache.is_none() {
            debug_assert!(n_parser_cache.is_none());

            match self.0.parse_mode(mode, input, p_state) {
                EmptyOk(value) => {
                    *n_parser_cache = Some((false, (self.1)(value)));
                }
                ConsumedOk(value) => {
                    *n_parser_cache = Some((true, (self.1)(value)));
                }
                EmptyErr(err) => return EmptyErr(err),
                ConsumedErr(err) => return ConsumedErr(err),
            }
            mode.set_first();
        }

        let result = n_parser_cache
            .as_mut()
            .unwrap()
            .1
            .parse_consumed_mode(mode, input, n_state);
        match result {
            EmptyOk(x) => {
                let (consumed, _) = *n_parser_cache.as_ref().unwrap();
                *n_parser_cache = None;
                if consumed {
                    ConsumedOk(x)
                } else {
                    EmptyOk(x)
                }
            }
            ConsumedOk(x) => {
                *n_parser_cache = None;
                ConsumedOk(x)
            }
            EmptyErr(x) => {
                let (consumed, _) = *n_parser_cache.as_ref().unwrap();
                *n_parser_cache = None;
                if consumed {
                    ConsumedErr(x.error)
                } else {
                    EmptyErr(x)
                }
            }
            ConsumedErr(x) => ConsumedErr(x),
        }
    }

    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.0.add_error(errors);
    }
}

/// Equivalent to [`p.then(f)`].
///
/// [`p.then(f)`]: ../primitives/trait.Parser.html#method.then
#[inline(always)]
pub fn then<P, F, N>(p: P, f: F) -> Then<P, F>
where
    F: FnMut(P::Output) -> N,
    P: Parser,
    N: Parser<Input = P::Input>,
{
    Then(p, f)
}

#[derive(Copy, Clone)]
pub struct ThenPartial<P, F>(P, F);
impl<P, N, F> Parser for ThenPartial<P, F>
where
    F: FnMut(&mut P::Output) -> N,
    P: Parser,
    N: Parser<Input = P::Input>,
{
    type Input = N::Input;
    type Output = N::Output;
    type PartialState = (P::PartialState, Option<(bool, P::Output)>, N::PartialState);

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
        let (ref mut p_state, ref mut n_parser_cache, ref mut n_state) = *state;

        if mode.is_first() || n_parser_cache.is_none() {
            debug_assert!(n_parser_cache.is_none());

            match self.0.parse_mode(mode, input, p_state) {
                EmptyOk(value) => {
                    *n_parser_cache = Some((false, value));
                }
                ConsumedOk(value) => {
                    *n_parser_cache = Some((true, value));
                }
                EmptyErr(err) => return EmptyErr(err),
                ConsumedErr(err) => return ConsumedErr(err),
            }
            mode.set_first();
        }

        let result = (self.1)(&mut n_parser_cache.as_mut().unwrap().1).parse_consumed_mode(
            mode,
            input,
            n_state,
        );
        match result {
            EmptyOk(x) => {
                let (consumed, _) = *n_parser_cache.as_ref().unwrap();
                *n_parser_cache = None;
                if consumed {
                    ConsumedOk(x)
                } else {
                    EmptyOk(x)
                }
            }
            ConsumedOk(x) => {
                *n_parser_cache = None;
                ConsumedOk(x)
            }
            EmptyErr(x) => {
                let (consumed, _) = *n_parser_cache.as_ref().unwrap();
                *n_parser_cache = None;
                if consumed {
                    ConsumedErr(x.error)
                } else {
                    EmptyErr(x)
                }
            }
            ConsumedErr(x) => ConsumedErr(x),
        }
    }

    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.0.add_error(errors);
    }
}

/// Equivalent to [`p.then_partial(f)`].
///
/// [`p.then_partial(f)`]: ../primitives/trait.Parser.html#method.then_partial
#[inline(always)]
pub fn then_partial<P, F, N>(p: P, f: F) -> ThenPartial<P, F>
where
    F: FnMut(&mut P::Output) -> N,
    P: Parser,
    N: Parser<Input = P::Input>,
{
    ThenPartial(p, f)
}

#[derive(Clone)]
pub struct Expected<P>(
    P,
    Info<<P::Input as StreamOnce>::Item, <P::Input as StreamOnce>::Range>,
)
where
    P: Parser;
impl<P> Parser for Expected<P>
where
    P: Parser,
{
    type Input = P::Input;
    type Output = P::Output;
    type PartialState = P::PartialState;

    parse_mode!();
    #[inline(always)]
    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input>
    where
        M: ParseMode,
    {
        self.0.parse_mode(mode, input, state)
    }

    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        ParseError::set_expected(errors, StreamError::expected(self.1.clone()), |errors| {
            self.0.add_error(errors);
        })
    }
}

/// Equivalent to [`p.expected(info)`].
///
/// [`p.expected(info)`]: ../primitives/trait.Parser.html#method.expected
#[inline(always)]
pub fn expected<P>(
    p: P,
    info: Info<<P::Input as StreamOnce>::Item, <P::Input as StreamOnce>::Range>,
) -> Expected<P>
where
    P: Parser,
{
    Expected(p, info)
}

#[derive(Copy, Clone)]
pub struct AndThen<P, F>(P, F);
impl<P, F, O, E, I> Parser for AndThen<P, F>
where
    I: Stream,
    P: Parser<Input = I>,
    F: FnMut(P::Output) -> Result<O, E>,
    E: Into<<I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    type Input = P::Input;
    type Output = O;
    type PartialState = P::PartialState;

    parse_mode!();
    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input>
    where
        M: ParseMode,
    {
        let position = input.position();
        match self.0.parse_mode(mode, input, state) {
            EmptyOk(o) => match (self.1)(o) {
                Ok(o) => EmptyOk(o),
                Err(err) => EmptyErr(
                    <Self::Input as StreamOnce>::Error::from_error(position, err.into()).into(),
                ),
            },
            ConsumedOk(o) => match (self.1)(o) {
                Ok(o) => ConsumedOk(o),
                Err(err) => ConsumedErr(
                    <Self::Input as StreamOnce>::Error::from_error(position, err.into()).into(),
                ),
            },
            EmptyErr(err) => EmptyErr(err),
            ConsumedErr(err) => ConsumedErr(err),
        }
    }

    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.0.add_error(errors);
    }
}

/// Equivalent to [`p.and_then(f)`].
///
/// [`p.and_then(f)`]: ../primitives/trait.Parser.html#method.and_then
#[inline(always)]
pub fn and_then<P, F, O, E, I>(p: P, f: F) -> AndThen<P, F>
where
    P: Parser<Input = I>,
    F: FnMut(P::Output) -> Result<O, E>,
    I: Stream,
    E: Into<<I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError>,
{
    AndThen(p, f)
}

#[derive(Copy, Clone)]
pub struct EnvParser<E, I, T>
where
    I: Stream,
{
    env: E,
    parser: fn(E, &mut I) -> ParseResult<T, I>,
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
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<O, I> {
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
///     fn string<I>(&self, input: &mut I) -> ParseResult<u32, I>
///         where I: Stream<Item=char>,
///               I::Error: ParseError<I::Item, I::Range, I::Position>,
///     {
///         many(letter())
///             .map(|s: String| self.0.get(&s).cloned().unwrap_or(0))
///             .parse_stream(input)
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
pub fn env_parser<E, I, O>(env: E, parser: fn(E, &mut I) -> ParseResult<O, I>) -> EnvParser<E, I, O>
where
    E: Clone,
    I: Stream,
{
    EnvParser {
        env: env,
        parser: parser,
    }
}

#[derive(Copy, Clone)]
pub struct Recognize<F, P>(P, PhantomData<fn() -> F>);

impl<F, P> Recognize<F, P>
where
    P: Parser,
    F: Default + Extend<<P::Input as StreamOnce>::Item>,
{
    #[inline]
    fn recognize_result(
        elements: &mut F,
        before: <<Self as Parser>::Input as Resetable>::Checkpoint,
        input: &mut <Self as Parser>::Input,
        result: ConsumedResult<P::Output, P::Input>,
    ) -> ConsumedResult<F, P::Input> {
        match result {
            EmptyOk(_) => {
                let last_position = input.position();
                input.reset(before);

                while input.position() != last_position {
                    match input.uncons() {
                        Ok(elem) => elements.extend(Some(elem)),
                        Err(err) => {
                            return EmptyErr(
                                <P::Input as StreamOnce>::Error::from_error(input.position(), err)
                                    .into(),
                            )
                        }
                    }
                }
                EmptyOk(mem::replace(elements, F::default()))
            }
            ConsumedOk(_) => {
                let last_position = input.position();
                input.reset(before);

                while input.position() != last_position {
                    match input.uncons() {
                        Ok(elem) => elements.extend(Some(elem)),
                        Err(err) => {
                            return ConsumedErr(
                                <P::Input as StreamOnce>::Error::from_error(input.position(), err)
                                    .into(),
                            )
                        }
                    }
                }
                ConsumedOk(mem::replace(elements, F::default()))
            }
            ConsumedErr(err) => {
                let last_position = input.position();
                input.reset(before);

                while input.position() != last_position {
                    match input.uncons() {
                        Ok(elem) => elements.extend(Some(elem)),
                        Err(err) => {
                            return ConsumedErr(
                                <P::Input as StreamOnce>::Error::from_error(input.position(), err)
                                    .into(),
                            )
                        }
                    }
                }
                ConsumedErr(err)
            }
            EmptyErr(err) => EmptyErr(err),
        }
    }
}

impl<P, F> Parser for Recognize<F, P>
where
    P: Parser,
    F: Default + Extend<<P::Input as StreamOnce>::Item>,
{
    type Input = P::Input;
    type Output = F;
    type PartialState = (F, P::PartialState);

    parse_mode!();
    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input>
    where
        M: ParseMode,
    {
        let (ref mut elements, ref mut child_state) = *state;

        let before = input.checkpoint();
        let result = self.0.parse_mode(mode, input, child_state);
        Self::recognize_result(elements, before, input, result)
    }

    #[inline]
    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.0.add_error(errors)
    }
}

/// Constructs a parser which returns the tokens parsed by `parser` accumulated in
/// `F: FromIterator<P::Input::Item>` instead of `P::Output`.
///
/// ```
/// use combine::Parser;
/// use combine::combinator::{skip_many1, token, recognize};
/// use combine::parser::char::digit;
///
/// let mut parser = recognize((skip_many1(digit()), token('.'), skip_many1(digit())));
/// assert_eq!(parser.parse("123.45"), Ok(("123.45".to_string(), "")));
/// assert_eq!(parser.parse("123.45"), Ok(("123.45".to_string(), "")));
/// ```
#[inline(always)]
pub fn recognize<F, P>(parser: P) -> Recognize<F, P>
where
    P: Parser,
    F: Default + Extend<<P::Input as StreamOnce>::Item>,
{
    Recognize(parser, PhantomData)
}

impl<L, R> Parser for Either<L, R>
where
    L: Parser,
    R: Parser<Input = L::Input, Output = L::Output>,
{
    type Input = L::Input;
    type Output = L::Output;
    type PartialState = Option<Either<L::PartialState, R::PartialState>>;

    #[inline]
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        match *self {
            Either::Left(ref mut x) => x.parse_lazy(input),
            Either::Right(ref mut x) => x.parse_lazy(input),
        }
    }

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
        match *self {
            Either::Left(ref mut x) => {
                match *state {
                    None | Some(Either::Right(_)) => {
                        *state = Some(Either::Left(L::PartialState::default()))
                    }
                    Some(Either::Left(_)) => (),
                }
                x.parse_mode(
                    mode,
                    input,
                    state.as_mut().unwrap().as_mut().left().unwrap(),
                )
            }
            Either::Right(ref mut x) => {
                match *state {
                    None | Some(Either::Left(_)) => {
                        *state = Some(Either::Right(R::PartialState::default()))
                    }
                    Some(Either::Right(_)) => (),
                }
                x.parse_mode(
                    mode,
                    input,
                    state.as_mut().unwrap().as_mut().right().unwrap(),
                )
            }
        }
    }

    #[inline]
    fn add_error(&mut self, error: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        match *self {
            Either::Left(ref mut x) => x.add_error(error),
            Either::Right(ref mut x) => x.add_error(error),
        }
    }
}

pub struct NoPartial<P>(P);

impl<P> Parser for NoPartial<P>
where
    P: Parser,
{
    type Input = <P as Parser>::Input;
    type Output = <P as Parser>::Output;
    type PartialState = ();

    #[inline(always)]
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        self.0.parse_lazy(input)
    }

    parse_mode!();
    #[inline(always)]
    fn parse_mode_impl<M>(
        &mut self,
        _mode: M,
        input: &mut Self::Input,
        _state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input>
    where
        M: ParseMode,
    {
        self.0.parse_lazy(input)
    }

    fn add_error(&mut self, error: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.0.add_error(error)
    }
}

pub fn no_partial<P>(p: P) -> NoPartial<P>
where
    P: Parser,
{
    NoPartial(p)
}

#[derive(Copy, Clone)]
pub struct Ignore<P>(P);
impl<P> Parser for Ignore<P>
where
    P: Parser,
{
    type Input = P::Input;
    type Output = ();
    type PartialState = P::PartialState;

    #[inline(always)]
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        self.0.parse_lazy(input).map(|_| ())
    }

    parse_mode!();
    #[inline(always)]
    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input>
    where
        M: ParseMode,
    {
        self.0.parse_mode(mode, input, state).map(|_| ())
    }

    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.0.add_error(errors)
    }
}

#[doc(hidden)]
pub fn ignore<P>(p: P) -> Ignore<P>
where
    P: Parser,
{
    Ignore(p)
}

#[cfg(feature = "std")]
#[derive(Default)]
pub struct AnyPartialState(Option<Box<::std::any::Any>>);

#[cfg(feature = "std")]
pub struct AnyPartialStateParser<P>(P);

#[cfg(feature = "std")]
impl<P> Parser for AnyPartialStateParser<P>
where
    P: Parser,
    P::PartialState: 'static,
{
    type Input = P::Input;
    type Output = P::Output;
    type PartialState = AnyPartialState;

    #[inline]
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        self.0.parse_lazy(input)
    }

    #[inline]
    fn parse_partial(
        &mut self,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input> {
        let mut new_child_state;
        let result = {
            let child_state = if let None = state.0 {
                new_child_state = Some(Default::default());
                new_child_state.as_mut().unwrap()
            } else {
                new_child_state = None;
                state.0.as_mut().unwrap().downcast_mut().unwrap()
            };

            self.0.parse_partial(input, child_state)
        };

        if let ConsumedErr(_) = result {
            if let None = state.0 {
                // FIXME Make None unreachable for LLVM
                state.0 = Some(Box::new(new_child_state.unwrap()));
            }
        }

        result
    }

    fn add_error(&mut self, error: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.0.add_error(error)
    }
}

/// Returns a parser where `P::PartialState` is boxed. Useful as a way to avoid writing the type
/// since it can get very large after combining a few parsers.
///
/// ```
/// # #[macro_use]
/// # extern crate combine;
/// # use combine::combinator::{AnyPartialState, any_partial_state};
/// # use combine::parser::char::letter;
/// # use combine::*;
///
/// # fn main() {
///
/// parser! {
///     type PartialState = AnyPartialState;
///     fn example[I]()(I) -> (char, char)
///     where [ I: Stream<Item = char> ]
///     {
///         any_partial_state((letter(), letter()))
///     }
/// }
///
/// assert_eq!(
///     example().easy_parse("ab"),
///     Ok((('a', 'b'), "")),
/// );
///
/// # }
/// ```
#[cfg(feature = "std")]
pub fn any_partial_state<P>(p: P) -> AnyPartialStateParser<P>
where
    P: Parser,
    P::PartialState: 'static,
{
    AnyPartialStateParser(p)
}

#[cfg(test)]
mod tests {
    use super::*;
    use Parser;
    use parser::char::{digit, letter};
    use parser::range::range;

    #[test]
    fn choice_empty() {
        let mut parser = choice::<&mut [Token<&str>]>(&mut []);
        let result_err = parser.parse("a");
        assert!(result_err.is_err());
    }

    #[test]
    fn tuple() {
        let mut parser = (digit(), token(','), digit(), token(','), letter());
        assert_eq!(parser.parse("1,2,z"), Ok((('1', ',', '2', ',', 'z'), "")));
    }

    #[test]
    fn issue_99() {
        let result = any().map(|_| ()).or(eof()).parse("");
        assert!(result.is_ok(), "{:?}", result);
    }

    #[test]
    fn not_followed_by_does_not_consume_any_input() {
        let mut parser = not_followed_by(range("a")).map(|_| "").or(range("a"));

        assert_eq!(parser.parse("a"), Ok(("a", "")));

        let mut parser = range("a").skip(not_followed_by(range("aa")));

        assert_eq!(parser.parse("aa"), Ok(("a", "a")));
        assert!(parser.parse("aaa").is_err());
    }
}

#[cfg(all(feature = "std", test))]
mod tests_std {
    use super::*;
    use Parser;
    use easy::{Error, Errors, StreamErrors};
    use parser::char::{char, digit, letter};
    use state::{SourcePosition, State};

    #[derive(Clone, PartialEq, Debug)]
    struct CloneOnly {
        s: String,
    }

    #[test]
    fn token_clone_but_not_copy() {
        // Verify we can use token() with a StreamSlice with an item type that is Clone but not
        // Copy.
        let input = &[
            CloneOnly { s: "x".to_string() },
            CloneOnly { s: "y".to_string() },
        ][..];
        let result = token(CloneOnly { s: "x".to_string() }).easy_parse(input);
        assert_eq!(
            result,
            Ok((
                CloneOnly { s: "x".to_string() },
                &[CloneOnly { s: "y".to_string() }][..]
            ))
        );
    }

    #[test]
    fn sep_by_consumed_error() {
        let mut parser2 = sep_by((letter(), letter()), token(','));
        let result_err: Result<(Vec<(char, char)>, &str), StreamErrors<&str>> =
            parser2.easy_parse("a,bc");
        assert!(result_err.is_err());
    }

    /// The expected combinator should retain only errors that are not `Expected`
    #[test]
    fn expected_retain_errors() {
        let mut parser = digit()
            .message("message")
            .expected("N/A")
            .expected("my expected digit");
        assert_eq!(
            parser.easy_parse(State::new("a")),
            Err(Errors {
                position: SourcePosition::default(),
                errors: vec![
                    Error::Unexpected('a'.into()),
                    Error::Message("message".into()),
                    Error::Expected("my expected digit".into()),
                ],
            })
        );
    }

    #[test]
    fn tuple_parse_error() {
        let mut parser = (digit(), digit());
        let result = parser.easy_parse(State::new("a"));
        assert_eq!(
            result,
            Err(Errors {
                position: SourcePosition::default(),
                errors: vec![
                    Error::Unexpected('a'.into()),
                    Error::Expected("digit".into()),
                ],
            })
        );
    }

    #[test]
    fn message_tests() {
        // Ensure message adds to both consumed and empty errors, interacting with parse_lazy and
        // parse_stream correctly on either side
        let input = "hi";

        let mut ok = char('h').message("not expected");
        let mut empty0 = char('o').message("expected message");
        let mut empty1 = char('o').message("expected message").map(|x| x);
        let mut empty2 = char('o').map(|x| x).message("expected message");
        let mut consumed0 = char('h').with(char('o')).message("expected message");
        let mut consumed1 = char('h')
            .with(char('o'))
            .message("expected message")
            .map(|x| x);
        let mut consumed2 = char('h')
            .with(char('o'))
            .map(|x| x)
            .message("expected message");

        assert!(ok.easy_parse(State::new(input)).is_ok());

        let empty_expected = Err(Errors {
            position: SourcePosition { line: 1, column: 1 },
            errors: vec![
                Error::Unexpected('h'.into()),
                Error::Expected('o'.into()),
                Error::Message("expected message".into()),
            ],
        });

        let consumed_expected = Err(Errors {
            position: SourcePosition { line: 1, column: 2 },
            errors: vec![
                Error::Unexpected('i'.into()),
                Error::Expected('o'.into()),
                Error::Message("expected message".into()),
            ],
        });

        assert_eq!(empty0.easy_parse(State::new(input)), empty_expected);
        assert_eq!(empty1.easy_parse(State::new(input)), empty_expected);
        assert_eq!(empty2.easy_parse(State::new(input)), empty_expected);

        assert_eq!(consumed0.easy_parse(State::new(input)), consumed_expected);
        assert_eq!(consumed1.easy_parse(State::new(input)), consumed_expected);
        assert_eq!(consumed2.easy_parse(State::new(input)), consumed_expected);
    }

    #[test]
    fn expected_tests() {
        // Ensure `expected` replaces only empty errors, interacting with parse_lazy and
        // parse_stream correctly on either side
        let input = "hi";

        let mut ok = char('h').expected("not expected");
        let mut empty0 = char('o').expected("expected message");
        let mut empty1 = char('o').expected("expected message").map(|x| x);
        let mut empty2 = char('o').map(|x| x).expected("expected message");
        let mut consumed0 = char('h').with(char('o')).expected("expected message");
        let mut consumed1 = char('h')
            .with(char('o'))
            .expected("expected message")
            .map(|x| x);
        let mut consumed2 = char('h')
            .with(char('o'))
            .map(|x| x)
            .expected("expected message");

        assert!(ok.easy_parse(State::new(input)).is_ok());

        let empty_expected = Err(Errors {
            position: SourcePosition { line: 1, column: 1 },
            errors: vec![
                Error::Unexpected('h'.into()),
                Error::Expected("expected message".into()),
            ],
        });

        let consumed_expected = Err(Errors {
            position: SourcePosition { line: 1, column: 2 },
            errors: vec![Error::Unexpected('i'.into()), Error::Expected('o'.into())],
        });

        assert_eq!(empty0.easy_parse(State::new(input)), empty_expected);
        assert_eq!(empty1.easy_parse(State::new(input)), empty_expected);
        assert_eq!(empty2.easy_parse(State::new(input)), empty_expected);

        assert_eq!(consumed0.easy_parse(State::new(input)), consumed_expected);
        assert_eq!(consumed1.easy_parse(State::new(input)), consumed_expected);
        assert_eq!(consumed2.easy_parse(State::new(input)), consumed_expected);
    }

    #[test]
    fn try_tests() {
        // Ensure try adds error messages exactly once
        assert_eq!(
            try(unexpected("test")).easy_parse(State::new("hi")),
            Err(Errors {
                position: SourcePosition { line: 1, column: 1 },
                errors: vec![
                    Error::Unexpected('h'.into()),
                    Error::Unexpected("test".into()),
                ],
            })
        );
        assert_eq!(
            try(char('h').with(unexpected("test"))).easy_parse(State::new("hi")),
            Err(Errors {
                position: SourcePosition { line: 1, column: 2 },
                errors: vec![
                    Error::Unexpected('i'.into()),
                    Error::Unexpected("test".into()),
                ],
            })
        );
    }

    #[test]
    fn sequence_error() {
        let mut parser = (char('a'), char('b'), char('c'));

        assert_eq!(
            parser.easy_parse(State::new("c")),
            Err(Errors {
                position: SourcePosition { line: 1, column: 1 },
                errors: vec![Error::Unexpected('c'.into()), Error::Expected('a'.into())],
            })
        );

        assert_eq!(
            parser.easy_parse(State::new("ac")),
            Err(Errors {
                position: SourcePosition { line: 1, column: 2 },
                errors: vec![Error::Unexpected('c'.into()), Error::Expected('b'.into())],
            })
        );
    }

    #[test]
    fn optional_empty_ok_then_error() {
        let mut parser = (optional(char('a')), char('b'));

        assert_eq!(
            parser.easy_parse(State::new("c")),
            Err(Errors {
                position: SourcePosition { line: 1, column: 1 },
                errors: vec![
                    Error::Unexpected('c'.into()),
                    Error::Expected('a'.into()),
                    Error::Expected('b'.into()),
                ],
            })
        );
    }

    #[test]
    fn nested_optional_empty_ok_then_error() {
        let mut parser = ((optional(char('a')), char('b')), char('c'));

        assert_eq!(
            parser.easy_parse(State::new("c")),
            Err(Errors {
                position: SourcePosition { line: 1, column: 1 },
                errors: vec![
                    Error::Unexpected('c'.into()),
                    Error::Expected('a'.into()),
                    Error::Expected('b'.into()),
                ],
            })
        );
    }

    #[test]
    fn consumed_then_optional_empty_ok_then_error() {
        let mut parser = (char('b'), optional(char('a')), char('b'));

        assert_eq!(
            parser.easy_parse(State::new("bc")),
            Err(Errors {
                position: SourcePosition { line: 1, column: 2 },
                errors: vec![
                    Error::Unexpected('c'.into()),
                    Error::Expected('a'.into()),
                    Error::Expected('b'.into()),
                ],
            })
        );
    }

    #[test]
    fn sequence_in_choice_parser_empty_err() {
        let mut parser = choice((
            (optional(char('a')), char('1')),
            (optional(char('b')), char('2')).skip(char('d')),
        ));

        assert_eq!(
            parser.easy_parse(State::new("c")),
            Err(Errors {
                position: SourcePosition { line: 1, column: 1 },
                errors: vec![
                    Error::Expected('a'.into()),
                    Error::Expected('1'.into()),
                    Error::Expected('b'.into()),
                    Error::Expected('2'.into()),
                    Error::Unexpected('c'.into()),
                ],
            })
        );
    }

    #[test]
    fn sequence_in_choice_array_parser_empty_err() {
        let mut parser = choice([
            (optional(char('a')), char('1')),
            (optional(char('b')), char('2')),
        ]);

        assert_eq!(
            parser.easy_parse(State::new("c")),
            Err(Errors {
                position: SourcePosition { line: 1, column: 1 },
                errors: vec![
                    Error::Expected('a'.into()),
                    Error::Expected('1'.into()),
                    Error::Expected('b'.into()),
                    Error::Expected('2'.into()),
                    Error::Unexpected('c'.into()),
                ],
            })
        );
    }

    #[test]
    fn sequence_in_choice_array_parser_empty_err_where_first_parser_delay_errors() {
        let mut p1 = char('1');
        let mut p2 = NoPartial((optional(char('b')), char('2')).map(|t| t.1));
        let mut parser =
            choice::<[&mut Parser<Input = _, Output = _, PartialState = _>; 2]>([&mut p1, &mut p2]);

        assert_eq!(
            parser.easy_parse(State::new("c")),
            Err(Errors {
                position: SourcePosition { line: 1, column: 1 },
                errors: vec![
                    Error::Expected('1'.into()),
                    Error::Expected('b'.into()),
                    Error::Expected('2'.into()),
                    Error::Unexpected('c'.into()),
                ],
            })
        );
    }

    #[test]
    fn sep_end_by1_dont_eat_separator_twice() {
        let mut parser = sep_end_by1(digit(), token(';'));
        assert_eq!(parser.parse("1;;"), Ok((vec!['1'], ";")));
    }

    #[test]
    fn count_min_max_empty_error() {
        assert_eq!(
            count_min_max(1, 1, char('a')).or(value(vec![])).parse("b"),
            Ok((vec![], "b"))
        );
    }
}

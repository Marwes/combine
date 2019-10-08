//! Various combinators which do not fit anywhere else.

use crate::lib::fmt;
use crate::lib::marker::PhantomData;
use crate::lib::mem;
use crate::lib::str;

use crate::error::{Info, ParseError, ParseResult, ResultExt, StreamError, Tracked};
use crate::parser::ParseMode;
use crate::stream::{input_at_eof, ResetStream, Stream, StreamErrorFor, StreamOnce};
use crate::Parser;

use either::Either;

use crate::error::ParseResult::*;

#[derive(Copy, Clone)]
pub struct NotFollowedBy<P>(P);
impl<Input, O, P> Parser<Input> for NotFollowedBy<P>
where
    Input: Stream,
    P: Parser<Input, Output = O>,
{
    type Output = ();
    type PartialState = P::PartialState;

    parse_mode!(Input);
    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Input,
        state: &mut Self::PartialState,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error>
    where
        M: ParseMode,
    {
        let checkpoint = input.checkpoint();
        let result = self.0.parse_mode(mode, input, state);
        ctry!(input.reset(checkpoint).consumed());
        match result {
            ConsumedOk(_) | EmptyOk(_) => EmptyErr(Input::Error::empty(input.position()).into()),
            ConsumedErr(_) | EmptyErr(_) => EmptyOk(()),
        }
    }

    #[inline]
    fn add_error(&mut self, _errors: &mut Tracked<<Input as StreamOnce>::Error>) {}

    fn add_consumed_expected_error(&mut self, _error: &mut Tracked<<Input as StreamOnce>::Error>) {}

    forward_parser!(Input, parser_count, 0);
}

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
///
/// # }
/// ```
#[inline]
pub fn not_followed_by<Input, P>(parser: P) -> NotFollowedBy<P>
where
    Input: Stream,
    P: Parser<Input>,
    P::Output: Into<Info<<Input as StreamOnce>::Token, <Input as StreamOnce>::Range, &'static str>>,
{
    NotFollowedBy(parser)
}

/*
 * TODO :: Rename `Try` to `Attempt`
 * Because this is public, it's name cannot be changed without also making a breaking change.
 */
#[derive(Copy, Clone)]
pub struct Try<P>(P);
impl<Input, O, P> Parser<Input> for Try<P>
where
    Input: Stream,
    P: Parser<Input, Output = O>,
{
    type Output = O;
    type PartialState = P::PartialState;

    #[inline]
    fn parse_stream(&mut self, input: &mut Input) -> ParseResult<O, <Input as StreamOnce>::Error> {
        self.parse_lazy(input)
    }

    parse_mode!(Input);
    #[inline]
    fn parse_consumed_mode<M>(
        &mut self,
        mode: M,
        input: &mut Input,
        state: &mut Self::PartialState,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error>
    where
        M: ParseMode,
    {
        self.parse_mode(mode, input, state)
    }

    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Input,
        state: &mut Self::PartialState,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error>
    where
        M: ParseMode,
    {
        match self.0.parse_consumed_mode(mode, input, state) {
            v @ ConsumedOk(_) | v @ EmptyOk(_) | v @ EmptyErr(_) => v,
            ConsumedErr(err) => {
                if input.is_partial() && err.is_unexpected_end_of_input() {
                    ConsumedErr(err)
                } else {
                    EmptyErr(err.into())
                }
            }
        }
    }

    forward_parser!(Input, add_error add_consumed_expected_error parser_count, 0);
}

/// `attempt(p)` behaves as `p` except it acts as if the parser hadn't consumed any input if `p` fails
/// after consuming input.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::parser::char::string;
/// # fn main() {
/// let mut p = attempt(string("let"))
///     .or(string("lex"));
/// let result = p.parse("lex").map(|x| x.0);
/// assert_eq!(result, Ok("lex"));
/// let result = p.parse("aet").map(|x| x.0);
/// assert!(result.is_err());
/// # }
/// ```
#[inline]
pub fn attempt<Input, P>(p: P) -> Try<P>
where
    Input: Stream,
    P: Parser<Input>,
{
    Try(p)
}

#[derive(Copy, Clone)]
pub struct LookAhead<P>(P);

impl<Input, O, P> Parser<Input> for LookAhead<P>
where
    Input: Stream,
    P: Parser<Input, Output = O>,
{
    type Output = O;
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Input) -> ParseResult<O, <Input as StreamOnce>::Error> {
        let before = input.checkpoint();
        let result = self.0.parse_lazy(input);
        ctry!(input.reset(before).consumed());
        let (o, _input) = ctry!(result);
        EmptyOk(o)
    }

    forward_parser!(Input, add_error add_consumed_expected_error parser_count, 0);
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
#[inline]
pub fn look_ahead<Input, P>(p: P) -> LookAhead<P>
where
    Input: Stream,
    P: Parser<Input>,
{
    LookAhead(p)
}

#[derive(Copy, Clone)]
pub struct Map<P, F>(P, F);
impl<Input, A, B, P, F> Parser<Input> for Map<P, F>
where
    Input: Stream,
    P: Parser<Input, Output = A>,
    F: FnMut(A) -> B,
{
    type Output = B;
    type PartialState = P::PartialState;

    parse_mode!(Input);
    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Input,
        state: &mut Self::PartialState,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error>
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

    forward_parser!(Input, add_error add_consumed_expected_error parser_count, 0);
}

/// Equivalent to [`p.map(f)`].
///
/// [`p.map(f)`]: ../trait.Parser.html#method.map
#[inline]
pub fn map<Input, P, F, B>(p: P, f: F) -> Map<P, F>
where
    Input: Stream,
    P: Parser<Input>,
    F: FnMut(P::Output) -> B,
{
    Map(p, f)
}

#[derive(Copy, Clone)]
pub struct MapInput<P, F>(P, F);
impl<Input, A, B, P, F> Parser<Input> for MapInput<P, F>
where
    Input: Stream,
    P: Parser<Input, Output = A>,
    F: FnMut(A, &mut Input) -> B,
{
    type Output = B;
    type PartialState = P::PartialState;

    parse_mode!(Input);
    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Input,
        state: &mut Self::PartialState,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error>
    where
        M: ParseMode,
    {
        match self.0.parse_mode(mode, input, state) {
            ConsumedOk(x) => ConsumedOk((self.1)(x, input)),
            EmptyOk(x) => EmptyOk((self.1)(x, input)),
            ConsumedErr(err) => ConsumedErr(err),
            EmptyErr(err) => EmptyErr(err),
        }
    }

    forward_parser!(Input, add_error add_consumed_expected_error parser_count, 0);
}

/// Equivalent to [`p.map_input(f)`].
///
/// [`p.map_input(f)`]: ../trait.Parser.html#method.map_input
#[inline]
pub fn map_input<Input, P, F, B>(p: P, f: F) -> MapInput<P, F>
where
    Input: Stream,
    P: Parser<Input>,
    F: FnMut(P::Output, &mut Input) -> B,
{
    MapInput(p, f)
}

#[derive(Copy, Clone)]
pub struct FlatMap<P, F>(P, F);
impl<Input, A, B, P, F> Parser<Input> for FlatMap<P, F>
where
    Input: Stream,
    P: Parser<Input, Output = A>,
    F: FnMut(A) -> Result<B, Input::Error>,
{
    type Output = B;
    type PartialState = P::PartialState;

    parse_mode!(Input);
    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Input,
        state: &mut Self::PartialState,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error>
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

    forward_parser!(Input, add_error add_consumed_expected_error parser_count, 0);
}

/// Equivalent to [`p.flat_map(f)`].
///
/// [`p.flat_map(f)`]: ../trait.Parser.html#method.flat_map
#[inline]
pub fn flat_map<Input, P, F, B>(p: P, f: F) -> FlatMap<P, F>
where
    Input: Stream,
    P: Parser<Input>,
    F: FnMut(P::Output) -> Result<B, <Input as StreamOnce>::Error>,
{
    FlatMap(p, f)
}

#[derive(Copy, Clone)]
pub struct AndThen<P, F>(P, F);
impl<Input, P, F, O, E> Parser<Input> for AndThen<P, F>
where
    Input: Stream,
    P: Parser<Input>,
    F: FnMut(P::Output) -> Result<O, E>,
    E: Into<<Input::Error as ParseError<Input::Token, Input::Range, Input::Position>>::StreamError>,
    Input::Error: ParseError<Input::Token, Input::Range, Input::Position>,
{
    type Output = O;
    type PartialState = P::PartialState;

    parse_mode!(Input);
    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Input,
        state: &mut Self::PartialState,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error>
    where
        M: ParseMode,
    {
        let position = input.position();
        let checkpoint = input.checkpoint();
        match self.0.parse_mode(mode, input, state) {
            EmptyOk(o) => match (self.1)(o) {
                Ok(o) => EmptyOk(o),
                Err(err) => {
                    let err = <Input as StreamOnce>::Error::from_error(position, err.into());

                    if input.is_partial() && input_at_eof(input) {
                        ctry!(input.reset(checkpoint).consumed());
                        ConsumedErr(err)
                    } else {
                        EmptyErr(err.into())
                    }
                }
            },
            ConsumedOk(o) => match (self.1)(o) {
                Ok(o) => ConsumedOk(o),
                Err(err) => {
                    if input.is_partial() && input_at_eof(input) {
                        ctry!(input.reset(checkpoint).consumed());
                    }
                    ConsumedErr(
                        <Input as StreamOnce>::Error::from_error(position, err.into()).into(),
                    )
                }
            },
            EmptyErr(err) => EmptyErr(err),
            ConsumedErr(err) => ConsumedErr(err),
        }
    }

    forward_parser!(Input, add_error add_consumed_expected_error parser_count, 0);
}

/// Equivalent to [`p.and_then(f)`].
///
/// [`p.and_then(f)`]: ../trait.Parser.html#method.and_then
#[inline]
pub fn and_then<Input, P, F, O, E>(p: P, f: F) -> AndThen<P, F>
where
    P: Parser<Input>,
    F: FnMut(P::Output) -> Result<O, E>,
    Input: Stream,
    E: Into<<Input::Error as ParseError<Input::Token, Input::Range, Input::Position>>::StreamError>,
{
    AndThen(p, f)
}

#[derive(Copy, Clone)]
pub struct Recognize<F, P>(P, PhantomData<fn() -> F>);

impl<F, P> Recognize<F, P> {
    #[inline]
    fn recognize_result<Input>(
        elements: &mut F,
        before: <Input as ResetStream>::Checkpoint,
        input: &mut Input,
        result: ParseResult<P::Output, <Input as StreamOnce>::Error>,
    ) -> ParseResult<F, <Input as StreamOnce>::Error>
    where
        P: Parser<Input>,
        Input: Stream,
        F: Default + Extend<Input::Token>,
    {
        match result {
            EmptyOk(_) => {
                let last_position = input.position();
                ctry!(input.reset(before).consumed());

                while input.position() != last_position {
                    match input.uncons() {
                        Ok(elem) => elements.extend(Some(elem)),
                        Err(err) => {
                            return EmptyErr(
                                <Input as StreamOnce>::Error::from_error(input.position(), err)
                                    .into(),
                            );
                        }
                    }
                }
                EmptyOk(mem::replace(elements, F::default()))
            }
            ConsumedOk(_) => {
                let last_position = input.position();
                ctry!(input.reset(before).consumed());

                while input.position() != last_position {
                    match input.uncons() {
                        Ok(elem) => elements.extend(Some(elem)),
                        Err(err) => {
                            return ConsumedErr(<Input as StreamOnce>::Error::from_error(
                                input.position(),
                                err,
                            ));
                        }
                    }
                }
                ConsumedOk(mem::replace(elements, F::default()))
            }
            ConsumedErr(err) => {
                let last_position = input.position();
                ctry!(input.reset(before).consumed());

                while input.position() != last_position {
                    match input.uncons() {
                        Ok(elem) => elements.extend(Some(elem)),
                        Err(err) => {
                            return ConsumedErr(<Input as StreamOnce>::Error::from_error(
                                input.position(),
                                err,
                            ));
                        }
                    }
                }
                ConsumedErr(err)
            }
            EmptyErr(err) => EmptyErr(err),
        }
    }
}

impl<Input, P, F> Parser<Input> for Recognize<F, P>
where
    Input: Stream,
    P: Parser<Input>,
    F: Default + Extend<<Input as StreamOnce>::Token>,
{
    type Output = F;
    type PartialState = (F, P::PartialState);

    parse_mode!(Input);
    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Input,
        state: &mut Self::PartialState,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error>
    where
        M: ParseMode,
    {
        let (ref mut elements, ref mut child_state) = *state;

        let before = input.checkpoint();
        let result = self.0.parse_mode(mode, input, child_state);
        Self::recognize_result(elements, before, input, result)
    }

    #[inline]
    fn add_error(&mut self, errors: &mut Tracked<<Input as StreamOnce>::Error>) {
        self.0.add_error(errors)
    }
}

/// Constructs a parser which returns the tokens parsed by `parser` accumulated in
/// `F: Extend<Input::Token>` instead of `P::Output`.
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
#[inline]
pub fn recognize<F, Input, P>(parser: P) -> Recognize<F, P>
where
    Input: Stream,
    P: Parser<Input>,
    F: Default + Extend<<Input as StreamOnce>::Token>,
{
    Recognize(parser, PhantomData)
}

impl<Input, L, R> Parser<Input> for Either<L, R>
where
    Input: Stream,
    L: Parser<Input>,
    R: Parser<Input, Output = L::Output>,
{
    type Output = L::Output;
    type PartialState = Option<Either<L::PartialState, R::PartialState>>;

    #[inline]
    fn parse_lazy(
        &mut self,
        input: &mut Input,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error> {
        match *self {
            Either::Left(ref mut x) => x.parse_lazy(input),
            Either::Right(ref mut x) => x.parse_lazy(input),
        }
    }

    parse_mode!(Input);
    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Input,
        state: &mut Self::PartialState,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error>
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
    fn add_error(&mut self, error: &mut Tracked<<Input as StreamOnce>::Error>) {
        match *self {
            Either::Left(ref mut x) => x.add_error(error),
            Either::Right(ref mut x) => x.add_error(error),
        }
    }
}

pub struct NoPartial<P>(P);

impl<Input, P> Parser<Input> for NoPartial<P>
where
    Input: Stream,
    P: Parser<Input>,
{
    type Output = <P as Parser<Input>>::Output;
    type PartialState = ();

    #[inline]
    fn parse_lazy(
        &mut self,
        input: &mut Input,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error> {
        self.0.parse_lazy(input)
    }

    parse_mode!(Input);
    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        _mode: M,
        input: &mut Input,
        _state: &mut Self::PartialState,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error>
    where
        M: ParseMode,
    {
        self.0.parse_lazy(input)
    }

    forward_parser!(Input, add_error add_consumed_expected_error parser_count, 0);
}

#[inline]
pub fn no_partial<Input, P>(p: P) -> NoPartial<P>
where
    Input: Stream,
    P: Parser<Input>,
{
    NoPartial(p)
}

#[derive(Copy, Clone)]
pub struct Ignore<P>(P);
impl<Input, P> Parser<Input> for Ignore<P>
where
    Input: Stream,
    P: Parser<Input>,
{
    type Output = ();
    type PartialState = P::PartialState;

    #[inline]
    fn parse_lazy(
        &mut self,
        input: &mut Input,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error> {
        self.0.parse_lazy(input).map(|_| ())
    }

    parse_mode!(Input);
    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Input,
        state: &mut Self::PartialState,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error>
    where
        M: ParseMode,
    {
        self.0.parse_mode(mode, input, state).map(|_| ())
    }

    forward_parser!(Input, add_error add_consumed_expected_error parser_count, 0);
}

#[doc(hidden)]
pub fn ignore<Input, P>(p: P) -> Ignore<P>
where
    Input: Stream,
    P: Parser<Input>,
{
    Ignore(p)
}

#[cfg(feature = "std")]
#[derive(Default)]
pub struct AnyPartialState(Option<Box<dyn std::any::Any>>);

#[cfg(feature = "std")]
pub struct AnyPartialStateParser<P>(P);

#[cfg(feature = "std")]
impl<Input, P> Parser<Input> for AnyPartialStateParser<P>
where
    Input: Stream,
    P: Parser<Input>,
    P::PartialState: 'static,
{
    type Output = P::Output;
    type PartialState = AnyPartialState;

    #[inline]
    fn parse_lazy(
        &mut self,
        input: &mut Input,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error> {
        self.0.parse_lazy(input)
    }

    parse_mode!(Input);
    #[inline]
    fn parse_mode<M>(
        &mut self,
        mode: M,
        input: &mut Input,
        state: &mut Self::PartialState,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error>
    where
        M: ParseMode,
    {
        let mut new_child_state;
        let result = {
            let child_state = if state.0.is_none() {
                new_child_state = Some(Default::default());
                new_child_state.as_mut().unwrap()
            } else {
                new_child_state = None;
                state.0.as_mut().unwrap().downcast_mut().unwrap()
            };

            self.0.parse_mode(mode, input, child_state)
        };

        if let ConsumedErr(_) = result {
            if state.0.is_none() {
                // FIXME Make None unreachable for LLVM
                state.0 = Some(Box::new(new_child_state.unwrap()));
            }
        }

        result
    }

    forward_parser!(Input, add_error add_consumed_expected_error parser_count, 0);
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
///     fn example[Input]()(Input) -> (char, char)
///     where [ Input: Stream<Token = char> ]
///     {
///         any_partial_state((letter(), letter()))
///     }
/// }
///
/// assert_eq!(
///     example().easy_parse("ab"),
///     Ok((('a', 'b'), ""))
/// );
///
/// # }
/// ```
#[cfg(feature = "std")]
pub fn any_partial_state<Input, P>(p: P) -> AnyPartialStateParser<P>
where
    Input: Stream,
    P: Parser<Input>,
    P::PartialState: 'static,
{
    AnyPartialStateParser(p)
}

#[cfg(feature = "std")]
#[derive(Default)]
pub struct AnySendPartialState(Option<Box<dyn std::any::Any + Send>>);

#[cfg(feature = "std")]
pub struct AnySendPartialStateParser<P>(P);

#[cfg(feature = "std")]
impl<Input, P> Parser<Input> for AnySendPartialStateParser<P>
where
    Input: Stream,
    P: Parser<Input>,
    P::PartialState: Send + 'static,
{
    type Output = P::Output;
    type PartialState = AnySendPartialState;

    #[inline]
    fn parse_lazy(
        &mut self,
        input: &mut Input,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error> {
        self.0.parse_lazy(input)
    }

    parse_mode!(Input);
    #[inline]
    fn parse_mode<M>(
        &mut self,
        mode: M,
        input: &mut Input,
        state: &mut Self::PartialState,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error>
    where
        M: ParseMode,
    {
        let mut new_child_state;
        let result = {
            let child_state = if let None = state.0 {
                new_child_state = Some(Default::default());
                new_child_state.as_mut().unwrap()
            } else {
                new_child_state = None;
                state.0.as_mut().unwrap().downcast_mut().unwrap()
            };

            self.0.parse_mode(mode, input, child_state)
        };

        if let ConsumedErr(_) = result {
            if state.0.is_none() {
                // FIXME Make None unreachable for LLVM
                state.0 = Some(Box::new(new_child_state.unwrap()));
            }
        }

        result
    }

    forward_parser!(Input, add_error add_consumed_expected_error parser_count, 0);
}

/// Returns a parser where `P::PartialState` is boxed. Useful as a way to avoid writing the type
/// since it can get very large after combining a few parsers.
///
/// ```
/// # #[macro_use]
/// # extern crate combine;
/// # use combine::combinator::{AnySendPartialState, any_send_partial_state};
/// # use combine::parser::char::letter;
/// # use combine::*;
///
/// # fn main() {
///
/// parser! {
///     type PartialState = AnySendPartialState;
///     fn example[Input]()(Input) -> (char, char)
///     where [ Input: Stream<Token = char> ]
///     {
///         any_send_partial_state((letter(), letter()))
///     }
/// }
///
/// assert_eq!(
///     example().easy_parse("ab"),
///     Ok((('a', 'b'), ""))
/// );
///
/// # }
/// ```
#[cfg(feature = "std")]
pub fn any_send_partial_state<Input, P>(p: P) -> AnySendPartialStateParser<P>
where
    Input: Stream,
    P: Parser<Input>,
    P::PartialState: Send + 'static,
{
    AnySendPartialStateParser(p)
}

#[derive(Copy, Clone)]
pub struct Lazy<P>(P);
impl<Input, O, P, R> Parser<Input> for Lazy<P>
where
    Input: Stream,
    P: FnMut() -> R,
    R: Parser<Input, Output = O>,
{
    type Output = O;
    type PartialState = R::PartialState;

    fn parse_stream(&mut self, input: &mut Input) -> ParseResult<O, <Input as StreamOnce>::Error> {
        (self.0)().parse_stream(input)
    }

    fn parse_lazy(&mut self, input: &mut Input) -> ParseResult<O, <Input as StreamOnce>::Error> {
        (self.0)().parse_lazy(input)
    }

    parse_mode!(Input);

    fn parse_consumed_mode<M>(
        &mut self,
        mode: M,
        input: &mut Input,
        state: &mut Self::PartialState,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error>
    where
        M: ParseMode,
    {
        (self.0)().parse_mode(mode, input, state)
    }

    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Input,
        state: &mut Self::PartialState,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error>
    where
        M: ParseMode,
    {
        (self.0)().parse_mode_impl(mode, input, state)
    }

    fn add_error(&mut self, errors: &mut Tracked<<Input as StreamOnce>::Error>) {
        (self.0)().add_error(errors);
    }

    fn add_consumed_expected_error(&mut self, errors: &mut Tracked<<Input as StreamOnce>::Error>) {
        (self.0)().add_consumed_expected_error(errors);
    }
}

/// Constructs the parser lazily on each `parse_*` call. Can be used to effectively reduce the
/// size of deeply nested parsers as only the function producing the parser is stored.
///
/// NOTE: Expects that the parser returned is always the same one, if that is not the case the
/// reported error may be wrong. If different parsers may be returned, use the [`factory`][] parser
/// instead.
///
/// [`factory`]: fn.factory.html
#[inline]
pub fn lazy<Input, P, R>(p: P) -> Lazy<P>
where
    Input: Stream,
    P: FnMut() -> R,
    R: Parser<Input>,
{
    Lazy(p)
}

#[derive(Copy, Clone)]
pub struct Factory<P, R>(P, Option<R>);

impl<P, R> Factory<P, R> {
    fn parser<Input>(&mut self, input: &mut Input) -> &mut R
    where
        P: FnMut(&mut Input) -> R,
    {
        if let Some(ref mut r) = self.1 {
            return r;
        }
        self.1 = Some((self.0)(input));
        self.1.as_mut().unwrap()
    }
}

impl<Input, O, P, R> Parser<Input> for Factory<P, R>
where
    Input: Stream,
    P: FnMut(&mut Input) -> R,
    R: Parser<Input, Output = O>,
{
    type Output = O;
    type PartialState = R::PartialState;

    parse_mode!(Input);

    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Input,
        state: &mut Self::PartialState,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error>
    where
        M: ParseMode,
    {
        // Always ask for a new parser except if we are in a partial call being resumed as we want
        // to resume the same parser then
        if mode.is_first() {
            self.1 = None;
        }
        self.parser(input).parse_mode_impl(mode, input, state)
    }

    fn add_error(&mut self, errors: &mut Tracked<<Input as StreamOnce>::Error>) {
        if let Some(parser) = &mut self.1 {
            parser.add_error(errors);
        }
    }

    fn add_consumed_expected_error(&mut self, errors: &mut Tracked<<Input as StreamOnce>::Error>) {
        if let Some(parser) = &mut self.1 {
            parser.add_consumed_expected_error(errors);
        }
    }
}

/// Constructs the parser lazily on each `parse_*` call. This is similar to [`lazy`][] but it
/// takes `Input` as an argument and allows different parsers to be returned on each call to
/// `p` while still reporting the correct errors.
///
/// [`lazy`]: fn.lazy.html
///
/// ```
/// # use combine::*;
/// # use combine::parser::char::{digit, letter};
/// # use combine::parser::combinator::{FnOpaque, opaque, factory};
///
/// let mut parsers: Vec<FnOpaque<_, _>> = vec![opaque(|f| f(&mut digit())), opaque(|f| f(&mut letter()))];
/// let mut iter = parsers.into_iter().cycle();
/// let mut parser = many(factory(move |_| iter.next().unwrap()));
/// assert_eq!(parser.parse("1a2b3cd"), Ok(("1a2b3c".to_string(), "d")));
/// ```
#[inline]
pub fn factory<Input, P, R>(p: P) -> Factory<P, R>
where
    Input: Stream,
    P: FnMut(&mut Input) -> R,
    R: Parser<Input>,
{
    Factory(p, None)
}

mod internal {
    pub trait Sealed {}
}

use self::internal::Sealed;

pub trait StrLike: Sealed {
    fn from_utf8(&self) -> Result<&str, ()>;
}

#[cfg(feature = "std")]
impl Sealed for String {}
#[cfg(feature = "std")]
impl StrLike for String {
    fn from_utf8(&self) -> Result<&str, ()> {
        Ok(self)
    }
}

impl<'a> Sealed for &'a str {}
impl<'a> StrLike for &'a str {
    fn from_utf8(&self) -> Result<&str, ()> {
        Ok(*self)
    }
}

impl Sealed for str {}
impl StrLike for str {
    fn from_utf8(&self) -> Result<&str, ()> {
        Ok(self)
    }
}

#[cfg(feature = "std")]
impl Sealed for Vec<u8> {}
#[cfg(feature = "std")]
impl StrLike for Vec<u8> {
    fn from_utf8(&self) -> Result<&str, ()> {
        (**self).from_utf8()
    }
}

impl<'a> Sealed for &'a [u8] {}
impl<'a> StrLike for &'a [u8] {
    fn from_utf8(&self) -> Result<&str, ()> {
        (**self).from_utf8()
    }
}

impl Sealed for [u8] {}
impl StrLike for [u8] {
    fn from_utf8(&self) -> Result<&str, ()> {
        str::from_utf8(self).map_err(|_| ())
    }
}

parser! {
pub struct FromStr;
type PartialState = P::PartialState;

/// Takes a parser that outputs a string like value (`&str`, `String`, `&[u8]` or `Vec<u8>`) and parses it
/// using `std::str::FromStr`. Errors if the output of `parser` is not UTF-8 or if
/// `FromStr::from_str` returns an error.
///
/// ```
/// # extern crate combine;
/// # use combine::parser::range;
/// # use combine::parser::repeat::many1;
/// # use combine::parser::combinator::from_str;
/// # use combine::char;
/// # use combine::*;
/// # fn main() {
/// let mut parser = from_str(many1::<String, _, _>(char::digit()));
/// let result = parser.parse("12345\r\n");
/// assert_eq!(result, Ok((12345i32, "\r\n")));
///
/// // Range parsers work as well
/// let mut parser = from_str(range::take_while1(|c: char| c.is_digit(10)));
/// let result = parser.parse("12345\r\n");
/// assert_eq!(result, Ok((12345i32, "\r\n")));
///
/// // As do parsers that work with bytes
/// let digits = || range::take_while1(|b: u8| b >= b'0' && b <= b'9');
/// let mut parser = from_str(range::recognize((
///     digits(),
///     byte::byte(b'.'),
///     digits(),
/// )));
/// let result = parser.parse(&b"123.45\r\n"[..]);
/// assert_eq!(result, Ok((123.45f64, &b"\r\n"[..])));
/// # }
/// ```
pub fn from_str[Input, O, P](parser: P)(Input) -> O
where [
    P: Parser<Input>,
    P::Output: StrLike,
    O: str::FromStr,
    O::Err: fmt::Display,
]
{
    parser.and_then(|r| {
        r.from_utf8()
            .map_err(|_| StreamErrorFor::<Input>::expected_static_message("UTF-8"))
            .and_then(|s| s.parse().map_err(StreamErrorFor::<Input>::message_format))
    })
}
}

#[derive(Copy, Clone)]
pub struct Opaque<F, Input, O, S>(F, PhantomData<fn(&mut Input, &mut S) -> O>);
impl<Input, F, O, S> Parser<Input> for Opaque<F, Input, O, S>
where
    Input: Stream,
    S: Default,
    F: FnMut(&mut dyn FnMut(&mut dyn Parser<Input, Output = O, PartialState = S>)),
{
    type Output = O;
    type PartialState = S;

    fn parse_stream(&mut self, input: &mut Input) -> ParseResult<O, <Input as StreamOnce>::Error> {
        let mut x = None;
        (self.0)(&mut |parser| x = Some(parser.parse_stream(input)));
        x.expect("Parser")
    }

    fn parse_lazy(&mut self, input: &mut Input) -> ParseResult<O, <Input as StreamOnce>::Error> {
        let mut x = None;
        (self.0)(&mut |parser| x = Some(parser.parse_lazy(input)));
        x.expect("Parser")
    }

    parse_mode!(Input);

    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Input,
        state: &mut Self::PartialState,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error>
    where
        M: ParseMode,
    {
        let mut x = None;
        (self.0)(&mut |parser| {
            x = Some(if mode.is_first() {
                parser.parse_first(input, state)
            } else {
                parser.parse_partial(input, state)
            })
        });
        x.expect("Parser")
    }

    fn add_error(&mut self, errors: &mut Tracked<<Input as StreamOnce>::Error>) {
        (self.0)(&mut |parser| parser.add_error(errors));
    }

    fn add_consumed_expected_error(&mut self, errors: &mut Tracked<<Input as StreamOnce>::Error>) {
        (self.0)(&mut |parser| parser.add_consumed_expected_error(errors));
    }
}

/// Alias over `Opaque` where the function can be a plain function pointer (does not need to
/// capture any values)
pub type FnOpaque<Input, O, S = ()> =
    Opaque<fn(&mut dyn FnMut(&mut dyn Parser<Input, Output = O, PartialState = S>)), Input, O, S>;

/// Creates a parser from a function which takes a function that are given the actual parser.
/// Though convoluted this makes it possible to hide the concrete parser type without `Box` or
/// losing the full information about the parser as is the case of [`parser`][].
///
/// Since this hides the type this can also be useful for writing mutually recursive `impl Parser`
/// parsers to break the otherwise arbitrarily large type that rustc creates internally.
///
/// If you need a more general version (that does not need trait objects) try the [`parser!`][]
/// macro.
///
/// ```
/// # #[macro_use]
/// # extern crate combine;
/// # use combine::combinator::{FnOpaque, no_partial};
/// # use combine::parser::char::{char, digit};
/// # use combine::*;
///
/// # fn main() {
///
/// #[derive(PartialEq, Debug)]
/// enum Expr {
///     Number(i64),
///     Pair(Box<Expr>, Box<Expr>),
/// }
///
/// fn expr<Input>() -> FnOpaque<Input, Expr>
/// where
///     Input: Stream<Token = char>,
///     Input::Error: ParseError<Input::Token, Input::Range, Input::Position>,
/// {
///     opaque!(
///         // `no_partial` disables partial parsing and replaces the partial state with `()`,
///         // letting us avoid naming that type
///         no_partial(choice((
///             from_str(many1::<String, _, _>(digit()))
///                 .map(Expr::Number),
///             (char('('), expr(), char(','), expr(), char(')'))
///                 .map(|(_, l, _, r, _)| Expr::Pair(Box::new(l), Box::new(r)))
///         ))),
///     )
/// }
///
/// assert_eq!(
///     expr().easy_parse("123"),
///     Ok((Expr::Number(123), ""))
/// );
///
/// # }
/// ```
///
/// [`parser`]: ../function/fn.parser.html
/// [`parser!`]: ../../macro.parser.html
pub fn opaque<Input, F, O, S>(f: F) -> Opaque<F, Input, O, S>
where
    Input: Stream,
    S: Default,
    F: FnMut(&mut dyn FnMut(&mut dyn Parser<Input, Output = O, PartialState = S>)),
{
    Opaque(f, PhantomData)
}

/// Convenience macro over [`opaque`][].
///
/// [`opaque`]: parser/combinator/fn.opaque.html
#[macro_export]
macro_rules! opaque {
    ($e: expr) => {
        opaque!($e,);
    };
    ($e: expr,) => {
        $crate::parser::combinator::opaque(
            move |f: &mut dyn FnMut(&mut $crate::Parser<_, Output = _, PartialState = _>)| {
                f(&mut $e)
            },
        )
    };
}

pub struct InputConverter<InputInner, P, C>
where
    InputInner: Stream,
{
    pub parser: P,
    pub converter: C,
    pub _marker: PhantomData<fn(InputInner)>,
}
impl<Input, InputInner, P, C> Parser<Input> for InputConverter<InputInner, P, C>
where
    Input: Stream,
    InputInner: Stream,
    P: Parser<InputInner>,
    for<'c> C: Converter<'c, Input, InputInner = InputInner>,
{
    type Output = P::Output;
    type PartialState = P::PartialState;

    parse_mode!(Input);

    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Input,
        state: &mut Self::PartialState,
    ) -> ParseResult<Self::Output, Input::Error>
    where
        M: ParseMode,
    {
        let mut input_inner = match self.converter.convert(input) {
            Ok(x) => x,
            Err(err) => return EmptyErr(err.into()),
        };
        self.parser
            .parse_mode(mode, &mut input_inner, state)
            .map_err(|err| self.converter.convert_error(input, err))
    }
}

pub trait Converter<'a, Input>
where
    Input: Stream,
{
    type InputInner: Stream + 'a;
    fn convert(&mut self, input: &'a mut Input) -> Result<Self::InputInner, Input::Error>;
    fn convert_error(
        &mut self,
        input: &'a mut Input,
        error: <Self::InputInner as StreamOnce>::Error,
    ) -> Input::Error;
}

impl<'a, Input, InputInner> Converter<'a, Input>
    for (
        fn(&'a mut Input) -> Result<InputInner, Input::Error>,
        fn(&'a mut Input, InputInner::Error) -> Input::Error,
    )
where
    Input: Stream,
    InputInner: Stream + 'a,
{
    type InputInner = InputInner;
    fn convert(&mut self, input: &'a mut Input) -> Result<InputInner, Input::Error> {
        (self.0)(input)
    }
    fn convert_error(&mut self, input: &'a mut Input, error: InputInner::Error) -> Input::Error {
        (self.1)(input, error)
    }
}

pub fn input_converter<Input, InputInner, P, C>(
    parser: P,
    converter: C,
) -> InputConverter<InputInner, P, C>
where
    Input: Stream,
    InputInner: Stream,
    P: Parser<InputInner>,
    for<'c> C: Converter<'c, Input, InputInner = InputInner>,
{
    InputConverter {
        parser,
        converter,
        _marker: PhantomData,
    }
}

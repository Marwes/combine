//! Parsers which cause errors or modifies the returned error on parse failure.

use lib::marker::PhantomData;

use error::{ConsumedResult, Info, ParseError, StreamError, Tracked};
use parser::ParseMode;
use {Parser, Stream, StreamOnce};

use error::FastResult::*;

#[derive(Clone)]
pub struct Unexpected<I, T>(Info<I::Item, I::Range>, PhantomData<fn(I) -> (I, T)>)
where
    I: Stream;
impl<I, T> Parser for Unexpected<I, T>
where
    I: Stream,
{
    type Input = I;
    type Output = T;
    type PartialState = ();
    #[inline]
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<T, I> {
        EmptyErr(<Self::Input as StreamOnce>::Error::empty(input.position()).into())
    }
    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        errors.error.add(StreamError::unexpected(self.0.clone()));
    }
}
/// Always fails with `message` as an unexpected error.
/// Never consumes any input.
///
/// Has `()` the output type
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::error::StreamError;
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
pub fn unexpected<I, S>(message: S) -> Unexpected<I, ()>
where
    I: Stream,
    S: Into<Info<I::Item, I::Range>>,
{
    unexpected_any(message)
}

/// Always fails with `message` as an unexpected error.
/// Never consumes any input.
///
/// May have anything as the output type but must be used such that the output type can inferred.
/// The `unexpected` parser can be used if the output type does not matter
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::parser::error::unexpected_any;
/// # use combine::error::StreamError;
/// # fn main() {
/// let result = token('b').or(unexpected_any("token"))
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
pub fn unexpected_any<I, S, T>(message: S) -> Unexpected<I, T>
where
    I: Stream,
    S: Into<Info<I::Item, I::Range>>,
{
    Unexpected(message.into(), PhantomData)
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

    forward_parser!(parser_count add_consumed_expected_error, 0);
}

/// Equivalent to [`p1.message(msg)`].
///
/// [`p1.message(msg)`]: ../parser/trait.Parser.html#method.message
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

    forward_parser!(parser_count add_consumed_expected_error, 0);
}

/// Equivalent to [`p.expected(info)`].
///
/// [`p.expected(info)`]: ../parser/trait.Parser.html#method.expected
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

#[derive(Clone)]
pub struct Silent<P>(P)
where
    P: Parser;
impl<P> Parser for Silent<P>
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
        self.0.parse_mode(mode, input, state).map_err(|mut err| {
            err.clear_expected();
            err
        })
    }

    fn add_error(&mut self, _errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {}

    fn add_consumed_expected_error(
        &mut self,
        _errors: &mut Tracked<<Self::Input as StreamOnce>::Error>,
    ) {
    }

    forward_parser!(parser_count, 0);
}

/// Equivalent to [`p.silent()`].
///
/// [`p.silent()`]: ../trait.Parser.html#method.silent
#[inline(always)]
pub fn silent<P>(p: P) -> Silent<P>
where
    P: Parser,
{
    Silent(p)
}

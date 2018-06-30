//! Various combinators which do not fit anywhere else.

use lib::marker::PhantomData;
use lib::mem;

use error::{ConsumedResult, Info, ParseError, Tracked};
use parser::error::unexpected;
use parser::item::value;
use parser::ParseMode;
use stream::{Positioned, Resetable, Stream, StreamOnce};
use Parser;

use either::Either;

use error::FastResult::*;

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
pub struct Try<P>(P);
impl<I, O, P> Parser for Try<P>
where
    I: Stream,
    P: Parser<Input = I, Output = O>,
{
    type Input = I;
    type Output = O;
    type PartialState = P::PartialState;

    #[inline]
    fn parse_stream_consumed(&mut self, input: &mut Self::Input) -> ConsumedResult<O, I> {
        self.parse_lazy(input)
    }

    parse_mode!();

    #[inline]
    fn parse_consumed_mode<M>(
        &mut self,
        mode: M,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input>
    where
        M: ParseMode,
    {
        self.parse_mode(mode, input, state)
    }

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
/// [`p.map(f)`]: ../parser/trait.Parser.html#method.map
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
/// [`p.flat_map(f)`]: ../parser/trait.Parser.html#method.flat_map
#[inline(always)]
pub fn flat_map<P, F, B>(p: P, f: F) -> FlatMap<P, F>
where
    P: Parser,
    F: FnMut(P::Output) -> Result<B, <P::Input as StreamOnce>::Error>,
{
    FlatMap(p, f)
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
/// [`p.and_then(f)`]: ../parser/trait.Parser.html#method.and_then
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
/// `F: Extend<P::Input::Item>` instead of `P::Output`.
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

#[inline(always)]
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

    parse_mode!();
    #[inline]
    fn parse_mode<M>(
        &mut self,
        mode: M,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input>
    where M: ParseMode
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
///     Ok((('a', 'b'), ""))
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

#[cfg(feature = "std")]
#[derive(Default)]
pub struct AnySendPartialState(Option<Box<::std::any::Any + Send>>);

#[cfg(feature = "std")]
pub struct AnySendPartialStateParser<P>(P);

#[cfg(feature = "std")]
impl<P> Parser for AnySendPartialStateParser<P>
where
    P: Parser,
    P::PartialState: Send + 'static,
{
    type Input = P::Input;
    type Output = P::Output;
    type PartialState = AnySendPartialState;

    #[inline]
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        self.0.parse_lazy(input)
    }

    #[inline]
    fn parse_mode<M>(
        &mut self,
        mode: M,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input>
    where M: ParseMode
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
/// # use combine::combinator::{AnySendPartialState, any_send_partial_state};
/// # use combine::parser::char::letter;
/// # use combine::*;
///
/// # fn main() {
///
/// parser! {
///     type PartialState = AnySendPartialState;
///     fn example[I]()(I) -> (char, char)
///     where [ I: Stream<Item = char> ]
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
pub fn any_send_partial_state<P>(p: P) -> AnySendPartialStateParser<P>
where
    P: Parser,
    P::PartialState: Send + 'static,
{
    AnySendPartialStateParser(p)
}

#[derive(Copy, Clone)]
pub struct Lazy<P>(P);
impl<I, O, P, R> Parser for Lazy<P>
where
    I: Stream,
    P: FnMut() -> R,
    R: Parser<Input = I, Output = O>,
{
    type Input = I;
    type Output = O;
    type PartialState = R::PartialState;

    fn parse_stream_consumed(&mut self, input: &mut Self::Input) -> ConsumedResult<O, I> {
        (self.0)().parse_stream_consumed(input)
    }

    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<O, I> {
        (self.0)().parse_lazy(input)
    }

    parse_mode!();

    fn parse_consumed_mode<M>(
        &mut self,
        mode: M,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input>
    where
        M: ParseMode,
    {
        (self.0)().parse_mode(mode, input, state)
    }

    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input>
    where
        M: ParseMode,
    {
        (self.0)().parse_mode_impl(mode, input, state)
    }
}

/// Constructs the parser lazily and on each `parse_*` call. Can be used to effectively reduce the
/// size of deeply nested parsers as only the function producing the parser is stored in `Lazy`
#[inline(always)]
pub fn lazy<P, R>(p: P) -> Lazy<P>
where
    P: FnMut() -> R,
    R: Parser,
{
    Lazy(p)
}

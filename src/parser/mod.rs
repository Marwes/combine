//! A collection of both concrete parsers as well as parser combinators.
//!
//! Implements the `Parser` trait which is the core of `combine` and contains the submodules
//! implementing all combine parsers.
use either::Either;

use crate::combinator::{
    and_then, expected, flat_map, map, message, then, then_partial, AndThen, Expected, FlatMap,
    Iter, Map, Message, Then, ThenPartial,
};
use crate::error::FastResult::*;
use crate::error::{ConsumedResult, FastResult, Info, ParseError, ParseResult, ResultExt, Tracked};
use crate::parser::error::{silent, Silent};
use crate::stream::{ResetStream, Stream, StreamOnce};
use crate::ErrorOffset;

use self::choice::{or, Or};
use self::sequence::{skip, with, Skip, With};

/// Internal API. May break without a semver bump
#[macro_export]
#[doc(hidden)]
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
        forward_parser!(0);
    }
}
}

/// Internal API. May break without a semver bump
#[macro_export]
#[doc(hidden)]
macro_rules! parse_mode {
    () => {
        #[inline(always)]
        fn parse_partial(
            &mut self,
            input: &mut Self::Input,
            state: &mut Self::PartialState,
        ) -> $crate::error::ConsumedResult<Self::Output, Self::Input> {
            self.parse_mode($crate::parser::PartialMode::default(), input, state)
        }

        #[inline(always)]
        fn parse_first(
            &mut self,
            input: &mut Self::Input,
            state: &mut Self::PartialState,
        ) -> $crate::error::ConsumedResult<Self::Output, Self::Input> {
            self.parse_mode($crate::parser::FirstMode, input, state)
        }
    }
}

pub mod byte;
pub mod char;
pub mod choice;
pub mod combinator;
pub mod error;
pub mod function;
pub mod item;
pub mod range;
#[cfg(any(feature = "regex", feature = "regex-1"))]
pub mod regex;
pub mod repeat;
pub mod sequence;

/// By implementing the `Parser` trait a type says that it can be used to parse an input stream
/// into the type `Output`.
///
/// All methods have a default implementation but there needs to be at least an implementation of
/// [`parse_stream`], [`parse_stream_consumed`], or [`parse_lazy`]. If the last is implemented, an
/// implementation of [`add_error`] may also be required. See the documentation for
/// [`parse_lazy`] for details.
///
/// [`parse_stream`]: trait.Parser.html#method.parse_stream
/// [`parse_stream_consumed`]: trait.Parser.html#method.parse_stream_consumed
/// [`parse_lazy`]: trait.Parser.html#method.parse_lazy
/// [`add_error`]: trait.Parser.html#method.add_error
pub trait Parser {
    /// The type which is taken as input for the parser. The type must implement the `Stream` trait
    /// which allows the parser to read items from the type.
    type Input: Stream;
    /// The type which is returned if the parser is successful.
    type Output;

    /// Determines the state necessary to resume parsing after more input is supplied.
    ///
    /// If partial parsing is not supported this can be set to `()`.
    type PartialState: Default;

    /// Entry point of the parser. Takes some input and tries to parse it, returning an easy to use
    /// and format error if parsing did not succeed.
    ///
    /// Returns the parsed result and the remaining input if the parser succeeds, or a
    /// This function wraps requires `Self::Input == easy::Stream<I>` which makes it return
    /// return `easy::Errors` if an error occurs. Due to this wrapping it is recommended that the
    /// parser `Self` is written with a generic input type.
    ///
    /// ```
    /// # #[macro_use]
    /// # extern crate combine;
    ///
    /// use combine::{Parser, Stream};
    /// use combine::parser::repeat::many1;
    /// use combine::parser::char::letter;
    ///
    /// // Good!
    /// parser!{
    /// fn my_parser[I]()(I) -> String
    ///     where [I: Stream<Item=char>]
    /// {
    ///     many1(letter())
    /// }
    /// }
    ///
    /// // Won't compile with `easy_parse` since it is specialized on `&str`
    /// parser!{
    /// fn my_parser2['a]()(&'a str) -> String
    /// {
    ///     many1(letter())
    /// }
    /// }
    ///
    /// fn main() {
    ///     assert_eq!(my_parser().parse("abc"), Ok(("abc".to_string(), "")));
    ///     // Would fail to compile if uncommented
    ///     // my_parser2().parse("abc")
    /// }
    /// ```
    ///
    /// [`ParseError`]: struct.ParseError.html
    #[cfg(feature = "std")]
    fn easy_parse<I>(&mut self, input: I) -> Result<(Self::Output, I), crate::easy::ParseError<I>>
    where
        I: Stream,
        crate::easy::Stream<I>: StreamOnce<
            Item = I::Item,
            Range = I::Range,
            Error = crate::easy::ParseError<crate::easy::Stream<I>>,
            Position = I::Position,
        >,
        I::Position: Default,
        I::Item: PartialEq,
        I::Range: PartialEq,
        Self: Sized + Parser<Input = crate::easy::Stream<I>>,
    {
        let input = crate::easy::Stream(input);
        self.parse(input).map(|(v, input)| (v, input.0))
    }

    /// Entry point of the parser. Takes some input and tries to parse it.
    ///
    /// Returns the parsed result and the remaining input if the parser succeeds, or a
    /// error otherwise.
    ///
    /// This is the most straightforward entry point to a parser. Since it does not decorate the
    /// input in any way you may find the error messages a hard to read. If that is the case you
    /// may want to try wrapping your input with an [`easy::Stream`][] or call [`easy_parse`][]
    /// instead.
    ///
    /// [`easy::Stream`]: ../easy/struct.Stream.html
    /// [`easy_parse`]: trait.Parser.html#method.easy_parse
    fn parse(
        &mut self,
        mut input: Self::Input,
    ) -> Result<(Self::Output, Self::Input), <Self::Input as StreamOnce>::Error> {
        match self.parse_stream(&mut input) {
            Ok((v, _)) => Ok((v, input)),
            Err(error) => Err(error.into_inner().error),
        }
    }

    /// Entry point of the parser when using partial parsing.
    /// Takes some input and tries to parse it.
    ///
    /// Returns the parsed result and the remaining input if the parser succeeds, or a
    /// error otherwise.
    fn parse_with_state(
        &mut self,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> Result<Self::Output, <Self::Input as StreamOnce>::Error> {
        match self.parse_stream_consumed_partial(input, state).into() {
            Ok((v, _)) => Ok(v),
            Err(error) => Err(error.into_inner().error),
        }
    }

    /// Parses using the stream `input` by calling [`Stream::uncons`] one or more times.
    ///
    /// On success returns `Ok((value, new_state))`, and on failure returns `Err(error)`.
    /// Furthermore `new_state` and `error` are wrapped in [`Consumed`], providing information on
    /// whether this parser consumed any input data or not.
    ///
    /// [`Stream::uncons`]: trait.StreamOnce.html#tymethod.uncons
    /// [`Consumed`]: enum.Consumed.html
    #[inline(always)]
    fn parse_stream(&mut self, input: &mut Self::Input) -> ParseResult<Self::Output, Self::Input> {
        self.parse_stream_consumed(input).into()
    }

    /// Parses using the stream `input` by calling [`Stream::uncons`] one or more times.
    ///
    /// Semantically equivalent to [`parse_stream`], except this method returns a flattened result
    /// type, combining `Result` and [`Consumed`] into a single [`FastResult`].
    ///
    /// [`Stream::uncons`]: trait.StreamOnce.html#tymethod.uncons
    /// [`parse_stream`]: trait.Parser.html#method.parse_stream
    /// [`Consumed`]: enum.Consumed.html
    /// [`FastResult`]: enum.FastResult.html
    #[inline]
    fn parse_stream_consumed(
        &mut self,
        input: &mut Self::Input,
    ) -> ConsumedResult<Self::Output, Self::Input> {
        let before = input.checkpoint();
        let mut state = Default::default();
        let mut result = self.parse_first(input, &mut state);
        if let FastResult::EmptyErr(ref mut error) = result {
            ctry!(input.reset(before.clone()).consumed());
            if let Ok(t) = input.uncons() {
                ctry!(input.reset(before).consumed());
                error.error.add_unexpected(Info::Token(t));
            }
            self.add_error(error);
        }
        result
    }

    #[inline]
    fn parse_stream_consumed_partial(
        &mut self,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input> {
        let before = input.checkpoint();
        let mut result = self.parse_partial(input, state);
        if let FastResult::EmptyErr(ref mut error) = result {
            ctry!(input.reset(before.clone()).consumed());
            if let Ok(t) = input.uncons() {
                ctry!(input.reset(before).consumed());
                error.error.add_unexpected(Info::Token(t));
            }
            self.add_error(error);
        }
        result
    }

    /// Parses using the stream `input` by calling [`Stream::uncons`] one or more times.
    ///
    /// Specialized version of [`parse_stream_consumed`] which permits error value creation to be
    /// skipped in the common case.
    ///
    /// When this parser returns `EmptyErr`, this method is allowed to return an empty
    /// [`Error`]. The error value that would have been returned can instead be obtained by
    /// calling [`add_error`]. This allows a parent parser such as `choice` to skip the creation of
    /// an unnecessary error value, if an alternative parser succeeds.
    ///
    /// External callers should never have to call this function directly.
    ///
    /// Parsers should seek to implement this function instead of the above two if errors can be
    /// encountered before consuming input. The default implementation always returns all errors,
    /// with [`add_error`] being a no-op.
    ///
    /// [`Stream::uncons`]: trait.StreamOnce.html#tymethod.uncons
    /// [`parse_stream_consumed`]: trait.Parser.html#method.parse_stream_consumed
    /// [`Error`]: trait.StreamOnce.html#associatedtype.Error
    /// [`add_error`]: trait.Parser.html#method.add_error
    #[inline(always)]
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        if input.is_partial() {
            // If a partial parser were called from a non-partial parser (as it is here) we must
            // reset the input to before the partial parser were called on errors that consumed
            // data as that parser's partial state was just temporary and it will not be able to
            // resume itself
            let before = input.checkpoint();
            let result = self.parse_first(input, &mut Default::default());
            if let ConsumedErr(_) = result {
                ctry!(input.reset(before).consumed());
            }
            result
        } else {
            self.parse_first(input, &mut Default::default())
        }
    }

    /// Parses using the stream `input` and allows itself to be resumed at a later point using
    /// `parse_partial` by storing the necessary intermediate state in `state`.
    ///
    /// Unlike `parse_partial` function this is allowed to assume that there is no partial state to
    /// resume.
    #[inline(always)]
    fn parse_first(
        &mut self,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input> {
        self.parse_partial(input, state)
    }

    /// Parses using the stream `input` and allows itself to be resumed at a later point using
    /// `parse_partial` by storing the necessary intermediate state in `state`
    #[inline(always)]
    fn parse_partial(
        &mut self,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input> {
        let _ = state;
        self.parse_lazy(input)
    }

    /// Internal API. May break without a semver bump
    #[doc(hidden)]
    #[inline(always)]
    fn parse_mode<M>(
        &mut self,
        mode: M,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input>
    where
        M: ParseMode,
        Self: Sized,
    {
        if mode.is_first() {
            self.parse_mode_impl(FirstMode, input, state)
        } else {
            self.parse_mode_impl(PartialMode::default(), input, state)
        }
    }

    /// Internal API. May break without a semver bump
    #[doc(hidden)]
    #[inline(always)]
    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input>
    where
        M: ParseMode,
        Self: Sized,
    {
        if mode.is_first() {
            self.parse_first(input, state)
        } else {
            self.parse_partial(input, state)
        }
    }

    /// Internal API. May break without a semver bump
    #[doc(hidden)]
    #[inline(always)]
    fn parse_consumed_mode<M>(
        &mut self,
        mode: M,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input>
    where
        M: ParseMode,
        Self: Sized,
    {
        if mode.is_first() {
            FirstMode.parse_consumed(self, input, state)
        } else {
            PartialMode::default().parse_consumed(self, input, state)
        }
    }

    /// Adds the first error that would normally be returned by this parser if it failed with an
    /// `EmptyErr` result.
    ///
    /// See [`parse_lazy`] for details.
    ///
    /// [`parse_lazy`]: trait.Parser.html#method.parse_lazy
    fn add_error(&mut self, _error: &mut Tracked<<Self::Input as StreamOnce>::Error>) {}

    /// Returns how many parsers this parser contains
    ///
    /// Internal API: This should not be implemented explicitly outside of combine.
    #[doc(hidden)]
    fn parser_count(&self) -> ErrorOffset {
        ErrorOffset(1)
    }

    /// Internal API: This should not be implemented explicitly outside of combine.
    #[doc(hidden)]
    fn add_consumed_expected_error(
        &mut self,
        _error: &mut Tracked<<Self::Input as StreamOnce>::Error>,
    ) {
    }

    /// Borrows a parser instead of consuming it.
    ///
    /// Used to apply parser combinators on `self` without losing ownership.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::error::Consumed;
    /// # use combine::parser::char::{digit, letter};
    /// fn test(input: &mut &'static str) -> ParseResult<(char, char), &'static str> {
    ///     let mut p = digit();
    ///     let ((d, _), consumed) = (p.by_ref(), letter()).parse_stream(input)?;
    ///     let (d2, consumed) = consumed.combine(|_| p.parse_stream(input))?;
    ///     Ok(((d, d2), consumed))
    /// }
    ///
    /// fn main() {
    ///     let mut input = "1a23";
    ///     assert_eq!(
    ///         test(&mut input).map(|(t, c)| (t, c.map(|_| input))),
    ///         Ok((('1', '2'), Consumed::Consumed("3")))
    ///     );
    /// }
    /// ```
    fn by_ref(&mut self) -> &mut Self
    where
        Self: Sized,
    {
        self
    }

    /// Discards the value of the `self` parser and returns the value of `p`.
    /// Fails if any of the parsers fails.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::parser::char::digit;
    /// # fn main() {
    /// let result = digit()
    ///     .with(token('i'))
    ///     .parse("9i")
    ///     .map(|x| x.0);
    /// assert_eq!(result, Ok('i'));
    /// # }
    /// ```
    fn with<P2>(self, p: P2) -> With<Self, P2>
    where
        Self: Sized,
        P2: Parser<Input = Self::Input>,
    {
        with(self, p)
    }

    /// Discards the value of the `p` parser and returns the value of `self`.
    /// Fails if any of the parsers fails.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::parser::char::digit;
    /// # fn main() {
    /// let result = digit()
    ///     .skip(token('i'))
    ///     .parse("9i")
    ///     .map(|x| x.0);
    /// assert_eq!(result, Ok('9'));
    /// # }
    /// ```
    fn skip<P2>(self, p: P2) -> Skip<Self, P2>
    where
        Self: Sized,
        P2: Parser<Input = Self::Input>,
    {
        skip(self, p)
    }

    /// Parses with `self` followed by `p`.
    /// Succeeds if both parsers succeed, otherwise fails.
    /// Returns a tuple with both values on success.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::parser::char::digit;
    /// # fn main() {
    /// let result = digit()
    ///     .and(token('i'))
    ///     .parse("9i")
    ///     .map(|x| x.0);
    /// assert_eq!(result, Ok(('9', 'i')));
    /// # }
    /// ```
    fn and<P2>(self, p: P2) -> (Self, P2)
    where
        Self: Sized,
        P2: Parser<Input = Self::Input>,
    {
        (self, p)
    }

    /// Returns a parser which attempts to parse using `self`. If `self` fails without consuming
    /// any input it tries to consume the same input using `p`.
    ///
    /// If you are looking to chain 3 or more parsers using `or` you may consider using the
    /// [`choice!`] macro instead, which can be clearer and may result in a faster parser.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::parser::char::{digit, string};
    /// # fn main() {
    /// let mut parser = string("let")
    ///     .or(digit().map(|_| "digit"))
    ///     .or(string("led"));
    /// assert_eq!(parser.parse("let"), Ok(("let", "")));
    /// assert_eq!(parser.parse("1"), Ok(("digit", "")));
    /// assert!(parser.parse("led").is_err());
    ///
    /// let mut parser2 = string("two").or(string("three"));
    /// // Fails as the parser for "two" consumes the first 't' before failing
    /// assert!(parser2.parse("three").is_err());
    ///
    /// // Use 'attempt' to make failing parsers always act as if they have not consumed any input
    /// let mut parser3 = attempt(string("two")).or(attempt(string("three")));
    /// assert_eq!(parser3.parse("three"), Ok(("three", "")));
    /// # }
    /// ```
    ///
    /// [`choice!`]: ../macro.choice.html
    fn or<P2>(self, p: P2) -> Or<Self, P2>
    where
        Self: Sized,
        P2: Parser<Input = Self::Input, Output = Self::Output>,
    {
        or(self, p)
    }

    /// Parses using `self` and then passes the value to `f` which returns a parser used to parse
    /// the rest of the input.
    ///
    /// Since the parser returned from `f` must have a single type it can be useful to use the
    /// `left` and `right` methods to merge parsers of differing types into one.
    ///
    /// If you are using partial parsing you may want to use `partial_then` instead.
    ///
    /// ```
    /// # #![cfg(feature = "std")]
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::parser::char::digit;
    /// # use combine::error::Consumed;
    /// # use combine::stream::easy;
    /// # fn main() {
    /// let result = digit()
    ///     .then(|d| {
    ///         if d == '9' {
    ///             value(9).left()
    ///         }
    ///         else {
    ///             unexpected_any(d).message("Not a nine").right()
    ///         }
    ///     })
    ///     .easy_parse("9");
    /// assert_eq!(result, Ok((9, "")));
    /// # }
    /// ```
    fn then<N, F>(self, f: F) -> Then<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Output) -> N,
        N: Parser<Input = Self::Input>,
    {
        then(self, f)
    }

    /// Variant of `then` which parses using `self` and then passes the value to `f` as a `&mut` reference.
    ///
    /// Useful when doing partial parsing since it does not need to store the parser returned by
    /// `f` in the partial state. Instead it will call `f` each to request a new parser each time
    /// parsing resumes and that parser is needed.
    ///
    /// Since the parser returned from `f` must have a single type it can be useful to use the
    /// `left` and `right` methods to merge parsers of differing types into one.
    ///
    /// ```
    /// # #![cfg(feature = "std")]
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::parser::char::digit;
    /// # use combine::error::Consumed;
    /// # use combine::stream::easy;
    /// # fn main() {
    /// let result = digit()
    ///     .then_partial(|d| {
    ///         if *d == '9' {
    ///             value(9).left()
    ///         }
    ///         else {
    ///             unexpected_any(*d).message("Not a nine").right()
    ///         }
    ///     })
    ///     .easy_parse("9");
    /// assert_eq!(result, Ok((9, "")));
    /// # }
    /// ```
    fn then_partial<N, F>(self, f: F) -> ThenPartial<Self, F>
    where
        Self: Sized,
        F: FnMut(&mut Self::Output) -> N,
        N: Parser<Input = Self::Input>,
    {
        then_partial(self, f)
    }

    /// Uses `f` to map over the parsed value.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::parser::char::digit;
    /// # fn main() {
    /// let result = digit()
    ///     .map(|c| c == '9')
    ///     .parse("9")
    ///     .map(|x| x.0);
    /// assert_eq!(result, Ok(true));
    /// # }
    /// ```
    fn map<F, B>(self, f: F) -> Map<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Output) -> B,
    {
        map(self, f)
    }

    /// Uses `f` to map over the output of `self`. If `f` returns an error the parser fails.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::parser::char::digit;
    /// # use combine::parser::range::take;
    /// # fn main() {
    /// let result = take(4)
    ///     .flat_map(|bs| many(digit()).parse(bs).map(|t| t.0))
    ///     .parse("12abcd");
    /// assert_eq!(result, Ok((String::from("12"), "cd")));
    /// # }
    /// ```
    fn flat_map<F, B>(self, f: F) -> FlatMap<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Output) -> Result<B, <Self::Input as StreamOnce>::Error>,
    {
        flat_map(self, f)
    }

    /// Parses with `self` and if it fails, adds the message `msg` to the error.
    ///
    /// ```
    /// # #![cfg(feature = "std")]
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::stream::easy;
    /// # use combine::stream::state::{State, SourcePosition};
    /// # fn main() {
    /// let result = token('9')
    ///     .message("Not a nine")
    ///     .easy_parse(State::new("8"));
    /// assert_eq!(result, Err(easy::Errors {
    ///     position: SourcePosition::default(),
    ///     errors: vec![
    ///         easy::Error::Unexpected('8'.into()),
    ///         easy::Error::Expected('9'.into()),
    ///         easy::Error::Message("Not a nine".into())
    ///     ]
    /// }));
    /// # }
    /// ```
    fn message<S>(self, msg: S) -> Message<Self>
    where
        Self: Sized,
        S: Into<Info<<Self::Input as StreamOnce>::Item, <Self::Input as StreamOnce>::Range>>,
    {
        message(self, msg.into())
    }

    /// Parses with `self` and if it fails without consuming any input any expected errors are
    /// replaced by `msg`. `msg` is then used in error messages as "Expected `msg`".
    ///
    /// ```
    /// # #![cfg(feature = "std")]
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::stream::easy;
    /// # use combine::stream::state::{State, SourcePosition};
    /// # fn main() {
    /// let result = token('9')
    ///     .expected("nine")
    ///     .easy_parse(State::new("8"));
    /// assert_eq!(result, Err(easy::Errors {
    ///     position: SourcePosition::default(),
    ///     errors: vec![
    ///         easy::Error::Unexpected('8'.into()),
    ///         easy::Error::Expected("nine".into())
    ///     ]
    /// }));
    /// # }
    /// ```
    fn expected<S>(self, msg: S) -> Expected<Self>
    where
        Self: Sized,
        S: Into<Info<<Self::Input as StreamOnce>::Item, <Self::Input as StreamOnce>::Range>>,
    {
        expected(self, msg.into())
    }

    /// Parses with `self`, if it fails without consuming any input any expected errors that would
    /// otherwise be emitted by `self` are suppressed.
    ///
    /// ```
    /// # #![cfg(feature = "std")]
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::stream::easy;
    /// # use combine::stream::state::{State, SourcePosition};
    /// # fn main() {
    /// let result = token('9')
    ///     .expected("nine")
    ///     .silent()
    ///     .easy_parse(State::new("8"));
    /// assert_eq!(result, Err(easy::Errors {
    ///     position: SourcePosition::default(),
    ///     errors: vec![
    ///         easy::Error::Unexpected('8'.into()),
    ///     ]
    /// }));
    /// # }
    /// ```
    fn silent(self) -> Silent<Self>
    where
        Self: Sized,
    {
        silent(self)
    }

    /// Parses with `self` and applies `f` on the result if `self` parses successfully.
    /// `f` may optionally fail with an error which is automatically converted to a `ParseError`.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::stream::state::{State, SourcePosition};
    /// # use combine::parser::char::digit;
    /// # fn main() {
    /// let mut parser = many1(digit())
    ///     .and_then(|s: String| s.parse::<i32>());
    /// let result = parser.easy_parse(State::new("1234")).map(|(x, state)| (x, state.input));
    /// assert_eq!(result, Ok((1234, "")));
    /// let result = parser.easy_parse(State::new("999999999999999999999999"));
    /// assert!(result.is_err());
    /// // Errors are report as if they occurred at the start of the parse
    /// assert_eq!(result.unwrap_err().position, SourcePosition { line: 1, column: 1 });
    /// # }
    /// ```
    fn and_then<F, O, E, I>(self, f: F) -> AndThen<Self, F>
    where
        Self: Parser<Input = I> + Sized,
        F: FnMut(Self::Output) -> Result<O, E>,
        I: Stream,
        E: Into<<I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError>,
    {
        and_then(self, f)
    }

    /// Creates an iterator from a parser and a state. Can be used as an alternative to [`many`]
    /// when collecting directly into a `Extend` type is not desirable.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::parser::char::{char, digit};
    /// # fn main() {
    /// let mut buffer = String::new();
    /// let number = parser(|input| {
    ///     buffer.clear();
    ///     let mut iter = digit().iter(input);
    ///     buffer.extend(&mut iter);
    ///     let i = buffer.parse::<i32>().unwrap();
    ///     iter.into_result(i)
    /// });
    /// let result = sep_by(number, char(','))
    ///     .parse("123,45,6");
    /// assert_eq!(result, Ok((vec![123, 45, 6], "")));
    /// # }
    /// ```
    ///
    /// [`many`]: ../combinator/fn.many.html
    fn iter(self, input: &mut <Self as Parser>::Input) -> Iter<Self, Self::PartialState, FirstMode>
    where
        Self: Parser + Sized,
    {
        Iter::new(self, FirstMode, input, Default::default())
    }

    /// Creates an iterator from a parser and a state. Can be used as an alternative to [`many`]
    /// when collecting directly into a `Extend` type is not desirable.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::parser::char::{char, digit};
    /// # fn main() {
    /// let mut buffer = String::new();
    /// let number = parser(|input| {
    ///     buffer.clear();
    ///     let mut iter = digit().iter(input);
    ///     buffer.extend(&mut iter);
    ///     let i = buffer.parse::<i32>().unwrap();
    ///     iter.into_result(i)
    /// });
    /// let result = sep_by(number, char(','))
    ///     .parse("123,45,6");
    /// assert_eq!(result, Ok((vec![123, 45, 6], "")));
    /// # }
    /// ```
    ///
    /// [`many`]: ../combinator/fn.many.html
    fn partial_iter<'a, 's, M>(
        self,
        mode: M,
        input: &'a mut <Self as Parser>::Input,
        partial_state: &'s mut Self::PartialState,
    ) -> Iter<'a, Self, &'s mut Self::PartialState, M>
    where
        Self: Parser + Sized,
        M: ParseMode,
    {
        Iter::new(self, mode, input, partial_state)
    }

    /// Turns the parser into a trait object by putting it in a `Box`. Can be used to easily
    /// return parsers from functions without naming the type.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # fn main() {
    /// fn test<'input, F>(
    ///     c: char,
    ///     f: F)
    ///     -> Box<Parser<Input = &'input str, Output = (char, char), PartialState = ()>>
    ///     where F: FnMut(char) -> bool + 'static
    /// {
    ///     ::combine::combinator::no_partial((token(c), satisfy(f))).boxed()
    /// }
    /// let result = test('a', |c| c >= 'a' && c <= 'f')
    ///     .parse("ac");
    /// assert_eq!(result, Ok((('a', 'c'), "")));
    /// # }
    /// ```
    #[cfg(feature = "std")]
    fn boxed<'a>(
        self,
    ) -> Box<
        Parser<Input = Self::Input, Output = Self::Output, PartialState = Self::PartialState> + 'a,
    >
    where
        Self: Sized + 'a,
    {
        Box::new(self)
    }

    /// Wraps the parser into the `Either` enum which allows combinators such as `then` to return
    /// multiple different parser types (merging them to one)
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::parser::char::{digit, letter};
    /// # fn main() {
    /// let mut parser = any().then(|c|
    ///     if c == '#' {
    ///         skip_many(satisfy(|c| c != '\n'))
    ///             .with(value("".to_string()))
    ///             .left()
    ///     } else {
    ///         many1(letter())
    ///             .map(move |mut s: String| { s.insert(0, c); s })
    ///             .right()
    ///     });
    ///
    /// let result = parser.parse("ac2");
    /// assert_eq!(result, Ok(("ac".to_string(), "2")));
    ///
    /// let result = parser.parse("# ac2");
    /// assert_eq!(result, Ok(("".to_string(), "")));
    /// # }
    /// ```
    fn left<R>(self) -> Either<Self, R>
    where
        Self: Sized,
        R: Parser<Input = Self::Input, Output = Self::Output>,
    {
        Either::Left(self)
    }

    /// Wraps the parser into the `Either` enum which allows combinators such as `then` to return
    /// multiple different parser types (merging them to one)
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::parser::char::{digit, letter};
    /// # fn main() {
    /// let mut parser = any().then(|c|
    ///     if c == '#' {
    ///         skip_many(satisfy(|c| c != '\n'))
    ///             .with(value("".to_string()))
    ///             .left()
    ///     } else {
    ///         many1(letter())
    ///             .map(move |mut s: String| { s.insert(0, c); s })
    ///             .right()
    ///     });
    ///
    /// let result = parser.parse("ac2");
    /// assert_eq!(result, Ok(("ac".to_string(), "2")));
    ///
    /// let result = parser.parse("# ac2");
    /// assert_eq!(result, Ok(("".to_string(), "")));
    /// # }
    /// ```
    fn right<L>(self) -> Either<L, Self>
    where
        Self: Sized,
        L: Parser<Input = Self::Input, Output = Self::Output>,
    {
        Either::Right(self)
    }
}

macro_rules! forward_deref {
    () => {
        type Input = P::Input;
        type Output = P::Output;
        type PartialState = P::PartialState;

        #[inline(always)]
        fn parse_first(
            &mut self,
            input: &mut Self::Input,
            state: &mut Self::PartialState,
        ) -> ConsumedResult<Self::Output, Self::Input> {
            (**self).parse_first(input, state)
        }

        #[inline(always)]
        fn parse_partial(
            &mut self,
            input: &mut Self::Input,
            state: &mut Self::PartialState,
        ) -> ConsumedResult<Self::Output, Self::Input> {
            (**self).parse_partial(input, state)
        }

        #[inline(always)]
        fn add_error(&mut self, error: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
            (**self).add_error(error)
        }

        #[inline(always)]
        fn add_consumed_expected_error(&mut self, error: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
            (**self).add_consumed_expected_error(error)
        }

        #[inline(always)]
        fn parser_count(&self) -> ErrorOffset {
            (**self).parser_count()
        }
    }
}

impl<'a, P> Parser for &'a mut P
where
    P: ?Sized + Parser,
{
    forward_deref!();
}

#[cfg(feature = "std")]
impl<P> Parser for Box<P>
where
    P: ?Sized + Parser,
{
    forward_deref!();
}

/// Internal API. May break without a semver bump
#[doc(hidden)]
/// Specifies whether the parser must check for partial state that must be resumed
pub trait ParseMode: Copy {
    /// If `true` then the parser has no previous state to resume otherwise the parser *might* have
    /// state to resume which it must check.
    fn is_first(self) -> bool;
    /// Puts the mode into `first` parsing.
    fn set_first(&mut self);

    #[inline]
    fn parse_consumed<P>(
        self,
        parser: &mut P,
        input: &mut P::Input,
        state: &mut P::PartialState,
    ) -> ConsumedResult<P::Output, P::Input>
    where
        P: Parser,
    {
        let before = input.checkpoint();
        let mut result = parser.parse_mode_impl(self, input, state);
        if let FastResult::EmptyErr(ref mut error) = result {
            ctry!(input.reset(before.clone()).consumed());
            if let Ok(t) = input.uncons() {
                ctry!(input.reset(before).consumed());
                error.error.add_unexpected(Info::Token(t));
            }
            parser.add_error(error);
        }
        result
    }
}

/// Internal API. May break without a semver bump
#[doc(hidden)]
#[derive(Copy, Clone)]
pub struct FirstMode;
impl ParseMode for FirstMode {
    #[inline(always)]
    fn is_first(self) -> bool {
        true
    }
    #[inline(always)]
    fn set_first(&mut self) {}
}

/// Internal API. May break without a semver bump
#[doc(hidden)]
#[derive(Copy, Clone, Default)]
pub struct PartialMode {
    pub first: bool,
}
impl ParseMode for PartialMode {
    #[inline(always)]
    fn is_first(self) -> bool {
        self.first
    }

    #[inline(always)]
    fn set_first(&mut self) {
        self.first = true;
    }
}

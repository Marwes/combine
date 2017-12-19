use lib::iter::FromIterator;
use lib::marker::PhantomData;
use primitives::{Consumed, ConsumedResult, Info, ParseError, ParseResult, Parser, Positioned,
                 Stream, StreamError, StreamOnce, Tracked, UnexpectedParse};
use primitives::FastResult::*;

use ErrorOffset;

macro_rules! impl_parser {
    ($name: ident ($first: ident, $($ty_var: ident),*), $inner_type: ty) => {
    #[derive(Clone)]
    pub struct $name<$first $(,$ty_var)*>($inner_type)
        where $first: Parser $(,$ty_var : Parser<Input=<$first as Parser>::Input>)*;
    impl <$first, $($ty_var),*> Parser for $name<$first $(,$ty_var)*>
        where $first: Parser $(, $ty_var : Parser<Input=<$first as Parser>::Input>)* {
        type Input = <$first as Parser>::Input;
        type Output = <$inner_type as Parser>::Output;
        fn parse_stream(&mut self,
                       input: Self::Input) -> ParseResult<Self::Output, Self::Input> {
            self.0.parse_stream(input)
        }
        fn parse_stream_consumed(&mut self,
                      input: Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
            self.0.parse_stream_consumed(input)
        }
        fn parse_lazy(&mut self,
                      input: Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
            self.0.parse_lazy(input)
        }
        fn add_error(&mut self, error: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
            self.0.add_error(error)
        }
    }
}
}

#[derive(Copy, Clone)]
pub struct Any<I>(PhantomData<fn(I) -> I>);

impl<I> Parser for Any<I>
where
    I: Stream,
{
    type Input = I;
    type Output = I::Item;
    #[inline]
    fn parse_lazy(&mut self, mut input: I) -> ConsumedResult<I::Item, I> {
        let position = input.position();
        match input.uncons() {
            Ok(x) => ConsumedOk((x, input)),
            Err(err) => EmptyErr(I::Error::from_error(position, err).into()),
        }
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

fn satisfy_impl<I, P, R>(mut input: I, mut predicate: P) -> ConsumedResult<R, I>
where
    I: Stream,
    P: FnMut(I::Item) -> Option<R>,
{
    let position = input.position();
    match input.uncons() {
        Ok(c) => match predicate(c.clone()) {
            Some(c) => ConsumedOk((c, input)),
            None => EmptyErr(I::Error::empty(position).into()),
        },
        Err(err) => EmptyErr(I::Error::from_error(position, err).into()),
    }
}

impl<I, P> Parser for Satisfy<I, P>
where
    I: Stream,
    P: FnMut(I::Item) -> bool,
{
    type Input = I;
    type Output = I::Item;
    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<I::Item, I> {
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
    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<R, I> {
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
    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<I::Item, I> {
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
    #[inline]
    fn parse_lazy(&mut self, mut input: I) -> ConsumedResult<T, I> {
        let start = input.position();
        let mut consumed = false;
        for c in self.tokens.clone() {
            match ::primitives::uncons(input) {
                Ok((other, rest)) => {
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
                    input = rest.into_inner();
                }
                Err(error) => {
                    return error.combine_consumed(|mut error| {
                        error.error.set_position(start);
                        if consumed {
                            ConsumedErr(error.error)
                        } else {
                            EmptyErr(error.into())
                        }
                    })
                }
            }
        }
        if consumed {
            ConsumedOk((self.tokens.clone(), input))
        } else {
            EmptyOk((self.tokens.clone(), input))
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
/// # use combine::primitives::Info;
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

    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<I::Position, I> {
        EmptyOk((input.position(), input))
    }
}

/// Parser which just returns the current position in the stream.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::state::SourcePosition;
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

    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<I::Item, I> {
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

    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<I::Item, I> {
        satisfy(|c| self.tokens.clone().into_iter().all(|t| t != c)).parse_lazy(input)
    }
}

/// Extract one token and succeeds if it is not part of `tokens`.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::easy;
/// # use combine::state::State;
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
pub struct Count<F, P> {
    parser: P,
    count: usize,
    _marker: PhantomData<fn() -> F>,
}

impl<P, F> Parser for Count<F, P>
where
    P: Parser,
    F: FromIterator<P::Output>,
{
    type Input = P::Input;
    type Output = F;

    #[inline]
    fn parse_lazy(&mut self, input: P::Input) -> ConsumedResult<F, P::Input> {
        let mut iter = self.parser.by_ref().iter(input);
        let value = iter.by_ref().take(self.count).collect();
        iter.into_result_fast(value)
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
    F: FromIterator<P::Output>,
{
    Count {
        parser: parser,
        count: count,
        _marker: PhantomData,
    }
}

/// Takes a number of parsers and tries to apply them each in order.
/// Fails if all the parsers fails or if an applied parser consumes input before failing.
///
/// ```
/// # #[macro_use]
/// # extern crate combine;
/// # use combine::*;
/// # use combine::char::{digit, letter, string};
/// # use combine::easy::Error;
/// # fn main() {
/// let mut parser = choice!(
///     many1(digit()),
///     string("let").map(|s| s.to_string()),
///     many1(letter()));
/// assert_eq!(parser.parse("let"), Ok(("let".to_string(), "")));
/// assert_eq!(parser.parse("123abc"), Ok(("123".to_string(), "abc")));
/// assert!(parser.parse(":123").is_err());
/// # }
/// ```
#[macro_export]
macro_rules! choice {
    ($first : expr) => {
        $first
    };
    ($first : expr, $($rest : expr),+) => {
        $first.or(choice!($($rest),+))
    }
}

/// `ChoiceParser` represents a parser which may parse one of several different choices depending
/// on the input.
///
/// This is an internal trait used to overload the `choice` function.
pub trait ChoiceParser {
    type Input: Stream;
    type Output;
    fn parse_choice(&mut self, input: Self::Input) -> ConsumedResult<Self::Output, Self::Input>;
    fn add_error_choice(&mut self, error: &mut Tracked<<Self::Input as StreamOnce>::Error>);
}

impl<'a, P> ChoiceParser for &'a mut P
where
    P: ?Sized + ChoiceParser,
{
    type Input = P::Input;
    type Output = P::Output;

    #[inline(always)]
    fn parse_choice(&mut self, input: Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        (**self).parse_choice(input)
    }
    fn add_error_choice(&mut self, error: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        (**self).add_error_choice(error)
    }
}

macro_rules! merge {
    ($head: ident) => {
        $head.error
    };
    ($head: ident $($tail: ident)+) => {
        $head.error.merge(merge!($($tail)+))
    };
}

macro_rules! do_choice {
    ($input: ident ( ) $($parser: ident $error: ident)+) => { {
        let mut error = Tracked::from(merge!($($error)+));
        // If offset != 1 then the nested parser is a sequence of parsers where 1 or
        // more parsers returned `EmptyOk` before the parser finally failed with
        // `EmptyErr`. Since we lose the offsets of the nested parsers when we merge
        // the errors we must first extract the errors before we do the merge.
        // If the offset == 0 on the other hand (which should be the common case) then
        // we can delay the addition of the error since we know for certain that only
        // the first parser in the sequence were tried
        $(
            if $error.offset != ErrorOffset(1) {
                error.offset = $error.offset;
                $parser.add_error(&mut error);
                error.offset = ErrorOffset(0);
            }
        )+
        EmptyErr(error)
    } };
    ($input: ident ( $head: ident $($tail: ident)* ) $($all: ident)*) => { {
        let parser = $head;
        match parser.parse_lazy($input.clone()) {
            ConsumedOk(x) => ConsumedOk(x),
            EmptyOk(x) => EmptyOk(x),
            ConsumedErr(err) => ConsumedErr(err),
            EmptyErr($head) => do_choice!($input ( $($tail)* ) $($all)* parser $head),
        } }
    }
}

macro_rules! tuple_choice_parser {
    ($head: ident) => {
    };
    ($head: ident $($id: ident)+) => {
        tuple_choice_parser_inner!($head $($id)+);
        tuple_choice_parser!($($id)+);
    };
}

macro_rules! tuple_choice_parser_inner {
    ($($id: ident)+) => {
        #[allow(non_snake_case)]
        impl<Input, Output $(,$id)+> ChoiceParser for ($($id),+)
        where
            Input: Stream,
            $($id: Parser<Input = Input, Output = Output>),+
        {
            type Input = Input;
            type Output = Output;
            #[inline]
            fn parse_choice(
                &mut self,
                input: Self::Input
            ) -> ConsumedResult<Self::Output, Self::Input> {
                let ($(ref mut $id),+) = *self;
                do_choice!(input ( $($id)+ ) )
            }
            fn add_error_choice(
                &mut self,
                error: &mut Tracked<<Self::Input as StreamOnce>::Error>
            ) {
                if error.offset != ErrorOffset(0) {
                    let ($(ref mut $id),+) = *self;
                    $(
                        $id.add_error(error);
                    )+
                }
            }
        }
    }
}

tuple_choice_parser!(A B C D E F G H I J K L M N O P Q R S T U V X Y Z);

macro_rules! array_choice_parser {
    ($($t: tt)+) => {
        $(
        impl<P> ChoiceParser for [P; $t]
        where
            P: Parser,
        {
            type Input = P::Input;
            type Output = P::Output;

            #[inline(always)]
            fn parse_choice(
                &mut self,
                input: Self::Input
            ) -> ConsumedResult<Self::Output, Self::Input> {
                self[..].parse_choice(input)
            }
            fn add_error_choice(
                &mut self,
                error: &mut Tracked<<Self::Input as StreamOnce>::Error>
            ) {
                self[..].add_error_choice(error)
            }
        }
        )+
    };
}

array_choice_parser!(
    0 1 2 3 4 5 6 7 8 9
    10 11 12 13 14 15 16 17 18 19
    20 21 22 23 24 25 26 27 28 29
    30 31 32
    );

#[derive(Copy, Clone)]
pub struct Choice<P>(P);

impl<P> Parser for Choice<P>
where
    P: ChoiceParser,
{
    type Input = P::Input;
    type Output = P::Output;

    #[inline(always)]
    fn parse_lazy(&mut self, input: Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        self.0.parse_choice(input)
    }

    fn add_error(&mut self, error: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.0.add_error_choice(error)
    }
}

impl<I, O, P> ChoiceParser for [P]
where
    I: Stream,
    P: Parser<Input = I, Output = O>,
{
    type Input = I;
    type Output = O;
    #[inline]
    fn parse_choice(&mut self, input: I) -> ConsumedResult<O, I> {
        let mut prev_err = None;
        let mut last_parser_having_non_1_offset = 0;
        for i in 0..self.len() {
            match self[i].parse_lazy(input.clone()) {
                consumed_err @ ConsumedErr(_) => return consumed_err,
                EmptyErr(err) => {
                    prev_err = match prev_err {
                        None => Some(err),
                        Some(mut prev_err) => {
                            if prev_err.offset != ErrorOffset(1) {
                                // First add the errors of all the preceding parsers which did not
                                // have a sequence of parsers returning `EmptyOk` before failing
                                // with `EmptyErr`.
                                let offset = prev_err.offset;
                                for p in &mut self[last_parser_having_non_1_offset..(i - 1)] {
                                    prev_err.offset = ErrorOffset(1);
                                    p.add_error(&mut prev_err);
                                }
                                // Then add the errors if the current parser
                                prev_err.offset = offset;
                                self[i - 1].add_error(&mut prev_err);
                                last_parser_having_non_1_offset = i;
                            }
                            Some(Tracked {
                                error: prev_err.error.merge(err.error),
                                offset: err.offset,
                            })
                        }
                    };
                }
                ok @ ConsumedOk(_) | ok @ EmptyOk(_) => return ok,
            }
        }
        EmptyErr(match prev_err {
            None => I::Error::from_error(
                input.position(),
                StreamError::message_static_message("parser choice is empty"),
            ).into(),
            Some(mut prev_err) => {
                if prev_err.offset != ErrorOffset(1) {
                    let offset = prev_err.offset;
                    let len = self.len();
                    for p in &mut self[last_parser_having_non_1_offset..(len - 1)] {
                        prev_err.offset = ErrorOffset(1);
                        p.add_error(&mut prev_err);
                    }
                    prev_err.offset = offset;
                    self.last_mut().unwrap().add_error(&mut prev_err);
                    prev_err.offset = ErrorOffset(0);
                }
                prev_err
            }
        })
    }
    fn add_error_choice(&mut self, error: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        if error.offset != ErrorOffset(0) {
            for p in self {
                p.add_error(error);
            }
        }
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
    F: FromIterator<P::Output>,
{
    type Input = P::Input;
    type Output = F;

    #[inline]
    fn parse_lazy(&mut self, input: P::Input) -> ConsumedResult<F, P::Input> {
        let mut iter = self.parser.by_ref().iter(input);
        let mut len = 0usize;
        let value = iter.by_ref().take(self.max).inspect(|_| len += 1).collect();
        if len < self.min {
            let err = <P::Input as StreamOnce>::Error::from_error(
                iter.input.position(),
                StreamError::message_message(format_args!(
                    "expected {} more elements",
                    self.min - len
                )),
            );
            ConsumedErr(err)
        } else {
            iter.into_result_fast(value)
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
    F: FromIterator<P::Output>,
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

/// Takes a tuple, a slice or an array of parsers and tries to apply them each in order.
/// Fails if all the parsers fails or if an applied parser consumes input before failing.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::char::{digit, string};
/// # fn main() {
/// // `choice` is overloaded on tuples so that different types of parsers can be used
/// // (each parser must still have the same input and output types)
/// let mut parser = choice((
///     string("Apple").map(|s| s.to_string()),
///     many1(digit()),
///     string("Orange").map(|s| s.to_string()),
/// ));
/// assert_eq!(parser.parse("1234"), Ok(("1234".to_string(), "")));
/// assert_eq!(parser.parse("Orangexx"), Ok(("Orange".to_string(), "xx")));
/// assert!(parser.parse("Appl").is_err());
/// assert!(parser.parse("Pear").is_err());
///
/// // If arrays or slices are used then all parsers must have the same type
/// // (`string` in this case)
/// let mut parser2 = choice([string("one"), string("two"), string("three")]);
/// // Fails as the parser for "two" consumes the first 't' before failing
/// assert!(parser2.parse("three").is_err());
///
/// // Use 'try' to make failing parsers always act as if they have not consumed any input
/// let mut parser3 = choice([try(string("one")), try(string("two")), try(string("three"))]);
/// assert_eq!(parser3.parse("three"), Ok(("three", "")));
/// # }
/// ```
#[inline(always)]
pub fn choice<P>(ps: P) -> Choice<P>
where
    P: ChoiceParser,
{
    Choice(ps)
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
    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<(), I> {
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
    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<T, I> {
        EmptyOk((self.0.clone(), input))
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
/// # use combine::char::{alpha_num, string};
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

    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<(), I> {
        match input.clone().uncons::<UnexpectedParse>() {
            Err(ref err) if *err == UnexpectedParse::Eoi => EmptyOk(((), input)),
            _ => EmptyErr(<Self::Input as StreamOnce>::Error::empty(input.position()).into()),
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

pub struct Iter<P: Parser> {
    parser: P,
    input: P::Input,
    consumed: bool,
    state: State<<P::Input as StreamOnce>::Error>,
}

enum State<E> {
    Ok,
    EmptyErr,
    ConsumedErr(E),
}

impl<P: Parser> Iter<P> {
    pub fn new(parser: P, input: P::Input) -> Iter<P> {
        Iter {
            parser: parser,
            input: input,
            consumed: false,
            state: State::Ok,
        }
    }
    /// Converts the iterator to a `ParseResult`, returning `Ok` if the parsing so far has be done
    /// without any errors which consumed data.
    pub fn into_result<O>(self, value: O) -> ParseResult<O, P::Input> {
        self.into_result_fast(value).into()
    }

    fn into_result_fast<O>(self, value: O) -> ConsumedResult<O, P::Input> {
        match self.state {
            State::Ok | State::EmptyErr => if self.consumed {
                ConsumedOk((value, self.input))
            } else {
                EmptyOk((value, self.input))
            },
            State::ConsumedErr(e) => ConsumedErr(e),
        }
    }
}

impl<P: Parser> Iterator for Iter<P> {
    type Item = P::Output;
    fn next(&mut self) -> Option<P::Output> {
        match self.state {
            State::Ok => match self.parser.parse_lazy(self.input.clone()) {
                EmptyOk((v, input)) => {
                    self.input = input;
                    Some(v)
                }
                ConsumedOk((v, input)) => {
                    self.input = input;
                    self.consumed = true;
                    Some(v)
                }
                EmptyErr(_) => {
                    self.state = State::EmptyErr;
                    None
                }
                ConsumedErr(e) => {
                    self.state = State::ConsumedErr(e);
                    None
                }
            },
            State::ConsumedErr(_) | State::EmptyErr => None,
        }
    }
}

#[derive(Copy, Clone)]
pub struct Many<F, P>(P, PhantomData<F>)
where
    P: Parser;
impl<F, P> Parser for Many<F, P>
where
    P: Parser,
    F: FromIterator<P::Output>,
{
    type Input = P::Input;
    type Output = F;
    fn parse_stream_consumed(&mut self, input: P::Input) -> ConsumedResult<F, P::Input> {
        let mut iter = (&mut self.0).iter(input);
        let result = iter.by_ref().collect();
        iter.into_result_fast(result)
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
/// # use combine::char::digit;
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
    F: FromIterator<P::Output>,
{
    Many(p, PhantomData)
}

#[derive(Copy, Clone)]
pub struct Many1<F, P>(P, PhantomData<fn() -> F>);
impl<F, P> Parser for Many1<F, P>
where
    F: FromIterator<P::Output>,
    P: Parser,
{
    type Input = P::Input;
    type Output = F;
    #[inline]
    fn parse_lazy(&mut self, input: P::Input) -> ConsumedResult<F, P::Input> {
        let (first, input) = ctry!(self.0.parse_lazy(input));
        let mut iter = Iter {
            parser: &mut self.0,
            consumed: !input.is_empty(),
            input: input.into_inner(),
            state: State::Ok,
        };
        let result = Some(first).into_iter().chain(iter.by_ref()).collect();
        iter.into_result_fast(result)
    }
    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.0.add_error(errors)
    }
}

#[derive(Clone)]
#[doc(hidden)]
// FIXME Should not be public
pub struct Sink<T>(PhantomData<T>);
impl<A> FromIterator<A> for Sink<A> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = A>,
    {
        for _ in iter {}
        Sink(PhantomData)
    }
}

impl_parser!{ SkipMany(P,), Map<Many<Sink<()>, Map<P, fn (P::Output)>>, fn (Sink<()>)> }

/// Parses `p` zero or more times ignoring the result.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::char::digit;
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
    fn ignore<T>(_: T) {}
    let ignore1: fn(P::Output) = ignore;
    let ignore2: fn(Sink<()>) = ignore;
    SkipMany(many(p.map(ignore1)).map(ignore2))
}

impl_parser!{ SkipMany1(P,), Map<Many1<Sink<()>, Map<P, fn (P::Output)>>, fn (Sink<()>)> }

/// Parses `p` one or more times ignoring the result.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::char::digit;
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
    fn ignore<T>(_: T) {}
    let ignore1: fn(P::Output) = ignore;
    let ignore2: fn(Sink<()>) = ignore;
    SkipMany1(many1(p.map(ignore1)).map(ignore2))
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
/// # use combine::char::digit;
/// # fn main() {
/// let result = many1::<Vec<_>, _>(digit())
///     .parse("A123");
/// assert!(result.is_err());
/// # }
/// ```
#[inline(always)]
pub fn many1<F, P>(p: P) -> Many1<F, P>
where
    F: FromIterator<P::Output>,
    P: Parser,
{
    Many1(p, PhantomData)
}

#[derive(Copy, Clone)]
pub struct SepBy<F, P, S> {
    parser: P,
    separator: S,
    _marker: PhantomData<fn() -> F>,
}
impl<F, P, S> Parser for SepBy<F, P, S>
where
    F: FromIterator<P::Output>,
    P: Parser,
    S: Parser<Input = P::Input>,
{
    type Input = P::Input;
    type Output = F;

    #[inline]
    fn parse_lazy(&mut self, input: P::Input) -> ConsumedResult<F, P::Input> {
        sep_by1(&mut self.parser, &mut self.separator)
            .or(parser(|input| {
                Ok((None.into_iter().collect(), Consumed::Empty(input)))
            }))
            .parse_lazy(input)
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
/// # use combine::char::digit;
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
    F: FromIterator<P::Output>,
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
    F: FromIterator<P::Output>,
    P: Parser,
    S: Parser<Input = P::Input>,
{
    type Input = P::Input;
    type Output = F;

    #[inline]
    fn parse_lazy(&mut self, input: P::Input) -> ConsumedResult<F, P::Input> {
        let (first, rest) = ctry!(self.parser.parse_lazy(input.clone()));

        rest.combine_consumed(move |input| {
            let rest = (&mut self.separator).with(&mut self.parser);
            let mut iter = Iter::new(rest, input);
            let result = Some(first).into_iter().chain(iter.by_ref()).collect();
            iter.into_result_fast(result)
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
/// # use combine::char::digit;
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
    F: FromIterator<P::Output>,
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
    F: FromIterator<P::Output>,
    P: Parser,
    S: Parser<Input = P::Input>,
{
    type Input = P::Input;
    type Output = F;

    #[inline]
    fn parse_lazy(&mut self, input: P::Input) -> ConsumedResult<F, P::Input> {
        sep_end_by1(&mut self.parser, &mut self.separator)
            .or(parser(|input| {
                Ok((None.into_iter().collect(), Consumed::Empty(input)))
            }))
            .parse_lazy(input)
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
/// # use combine::char::digit;
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
    F: FromIterator<P::Output>,
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
    F: FromIterator<P::Output>,
    P: Parser,
    S: Parser<Input = P::Input>,
{
    type Input = P::Input;
    type Output = F;

    #[inline]
    fn parse_lazy(&mut self, input: P::Input) -> ConsumedResult<F, P::Input> {
        let (first, input) = ctry!(self.parser.parse_lazy(input.clone()));

        input.combine_consumed(|input| {
            let rest = (&mut self.separator).with(optional(&mut self.parser));
            let mut iter = Iter::new(rest, input);
            let result = Some(first)
                .into_iter()
                // Parse elements until `self.parser` returns `None`
                .chain(iter.by_ref().scan((), |_, x| x))
                .collect();
            iter.into_result_fast(result)
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
/// # use combine::char::digit;
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
    F: FromIterator<P::Output>,
    P: Parser,
    S: Parser<Input = P::Input>,
{
    SepEndBy1 {
        parser: parser,
        separator: separator,
        _marker: PhantomData,
    }
}

impl<'a, I: Stream, O> Parser for FnMut(I) -> ParseResult<O, I> + 'a {
    type Input = I;
    type Output = O;
    fn parse_stream(&mut self, input: I) -> ParseResult<O, I> {
        self(input)
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
/// # use combine::char::digit;
/// # use combine::primitives::{Consumed, StreamError};
/// # use combine::easy;
/// # fn main() {
/// let mut even_digit = parser(|input| {
///     // Help type inference out
///     let _: easy::Stream<&str> = input;
///     let position = input.position();
///     let (char_digit, input) = try!(digit().parse_stream(input));
///     let d = (char_digit as i32) - ('0' as i32);
///     if d % 2 == 0 {
///         Ok((d, input))
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
    F: FnMut(I) -> ParseResult<O, I>,
{
    FnParser(f, PhantomData)
}

impl<I, O, F> Parser for FnParser<I, F>
where
    I: Stream,
    F: FnMut(I) -> ParseResult<O, I>,
{
    type Input = I;
    type Output = O;
    fn parse_stream(&mut self, input: I) -> ParseResult<O, I> {
        (self.0)(input)
    }
}

impl<I, O> Parser for fn(I) -> ParseResult<O, I>
where
    I: Stream,
{
    type Input = I;
    type Output = O;
    fn parse_stream(&mut self, input: I) -> ParseResult<O, I> {
        self(input)
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
    #[inline]
    fn parse_lazy(&mut self, input: P::Input) -> ConsumedResult<Option<P::Output>, P::Input> {
        match self.0.parse_lazy(input.clone()) {
            EmptyOk((x, rest)) => EmptyOk((Some(x), rest)),
            ConsumedOk((x, rest)) => ConsumedOk((Some(x), rest)),
            ConsumedErr(err) => ConsumedErr(err),
            EmptyErr(_) => EmptyOk((None, input)),
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
/// # use combine::char::string;
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
/// # use combine::char::string;
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

    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<P::Output, I> {
        let (mut l, mut input) = ctry!(self.0.parse_lazy(input));
        loop {
            match (&mut self.1, &mut self.0)
                .parse_lazy(input.clone().into_inner())
                .into()
            {
                Ok(((op, r), rest)) => {
                    l = op(l, r);
                    input = input.merge(rest);
                }
                Err(Consumed::Consumed(err)) => return ConsumedErr(err.error),
                Err(Consumed::Empty(_)) => break,
            }
        }
        Ok((l, input)).into()
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
/// # use combine::char::digit;
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
    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<P::Output, I> {
        // FIXME FastResult
        let (mut l, mut input) = ctry!(self.0.parse_lazy(input));
        loop {
            let op = match self.1.parse_lazy(input.clone().into_inner()).into() {
                Ok((x, rest)) => {
                    input = input.merge(rest);
                    x
                }
                Err(Consumed::Consumed(err)) => return ConsumedErr(err.error),
                Err(Consumed::Empty(_)) => break,
            };
            match self.parse_lazy(input.clone().into_inner()).into() {
                Ok((r, rest)) => {
                    l = op(l, r);
                    input = input.merge(rest);
                }
                Err(Consumed::Consumed(err)) => return ConsumedErr(err.error),
                Err(Consumed::Empty(_)) => break,
            }
        }
        Ok((l, input)).into()
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
/// # use combine::char::digit;
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
    #[inline]
    fn parse_stream(&mut self, input: I) -> ParseResult<O, I> {
        self.0.parse_stream(input).map_err(Consumed::into_empty)
    }
}

/// `try(p)` behaves as `p` except it acts as if the parser hadn't consumed any input if `p` fails
/// after consuming input.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::char::string;
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

    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<O, I> {
        let (o, _input) = ctry!(self.0.parse_lazy(input.clone()));
        EmptyOk((o, input))
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
/// # use combine::char::string;
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
pub struct With<P1, P2>((P1, P2))
where
    P1: Parser,
    P2: Parser;
impl<I, P1, P2> Parser for With<P1, P2>
where
    I: Stream,
    P1: Parser<Input = I>,
    P2: Parser<Input = I>,
{
    type Input = I;
    type Output = P2::Output;
    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<Self::Output, I> {
        self.0.parse_lazy(input).map(|(_, b)| b)
    }
    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.0.add_error(errors)
    }
}

/// Equivalent to [`p1.with(p2)`].
///
/// [`p1.with(p2)`]: ../primitives/trait.Parser.html#method.with
#[inline(always)]
pub fn with<P1, P2>(p1: P1, p2: P2) -> With<P1, P2>
where
    P1: Parser,
    P2: Parser<Input = P1::Input>,
{
    With((p1, p2))
}

#[derive(Copy, Clone)]
pub struct Skip<P1, P2>((P1, P2))
where
    P1: Parser,
    P2: Parser;
impl<I, P1, P2> Parser for Skip<P1, P2>
where
    I: Stream,
    P1: Parser<Input = I>,
    P2: Parser<Input = I>,
{
    type Input = I;
    type Output = P1::Output;
    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<Self::Output, I> {
        self.0.parse_lazy(input).map(|(a, _)| a)
    }
    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.0.add_error(errors)
    }
}

#[inline(always)]
pub fn skip<P1, P2>(p1: P1, p2: P2) -> Skip<P1, P2>
where
    P1: Parser,
    P2: Parser<Input = P1::Input>,
{
    Skip((p1, p2))
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

    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<Self::Output, I> {
        match self.0.parse_lazy(input) {
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
pub struct Or<P1, P2>(Choice<(P1, P2)>)
where
    P1: Parser,
    P2: Parser;
impl<I, O, P1, P2> Parser for Or<P1, P2>
where
    I: Stream,
    P1: Parser<Input = I, Output = O>,
    P2: Parser<Input = I, Output = O>,
{
    type Input = I;
    type Output = O;
    #[inline(always)]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<O, I> {
        self.0.parse_lazy(input)
    }
    #[inline]
    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        if errors.offset != ErrorOffset(0) {
            self.0.add_error(errors);
        }
    }
}

/// Equivalent to [`p1.or(p2)`].
///
/// If you are looking to chain 3 or more parsers using `or` you may consider using the
/// [`choice!`] macro instead, which can be clearer and may result in a faster parser.
///
/// [`p1.or(p2)`]: ../primitives/trait.Parser.html#method.or
#[inline(always)]
pub fn or<P1, P2>(p1: P1, p2: P2) -> Or<P1, P2>
where
    P1: Parser,
    P2: Parser<Input = P1::Input, Output = P1::Output>,
{
    Or(choice((p1, p2)))
}

#[derive(Copy, Clone)]
pub struct Map<P, F>(P, F);
impl<I, A, B, P, F> Parser for Map<P, F>
where
    I: Stream,
    P: Parser<Input = I, Output = A>,
    F: FnMut(A) -> B,
{
    type Input = I;
    type Output = B;
    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<B, I> {
        match self.0.parse_lazy(input) {
            ConsumedOk((x, input)) => ConsumedOk(((self.1)(x), input)),
            EmptyOk((x, input)) => EmptyOk(((self.1)(x), input)),
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
    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<B, I> {
        match self.0.parse_lazy(input) {
            EmptyOk((o, input)) => match (self.1)(o) {
                Ok(x) => EmptyOk((x, input)),
                Err(err) => EmptyErr(err.into()),
            },
            ConsumedOk((o, input)) => match (self.1)(o) {
                Ok(x) => ConsumedOk((x, input)),
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
    #[inline]
    fn parse_lazy(&mut self, input: Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        match self.0.parse_lazy(input) {
            EmptyOk((value, input)) => {
                let mut next = (self.1)(value);
                next.parse_stream_consumed(input)
            }
            ConsumedOk((value, input)) => {
                let mut next = (self.1)(value);
                match next.parse_stream_consumed(input) {
                    EmptyOk(x) | ConsumedOk(x) => ConsumedOk(x),
                    EmptyErr(x) => ConsumedErr(x.error),
                    ConsumedErr(x) => ConsumedErr(x),
                }
            }
            EmptyErr(err) => EmptyErr(err),
            ConsumedErr(err) => ConsumedErr(err),
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

    #[inline]
    fn parse_lazy(&mut self, input: Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        self.0.parse_lazy(input)
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
    #[inline]
    fn parse_lazy(&mut self, input: Self::Input) -> ConsumedResult<O, Self::Input> {
        let position = input.position();
        match self.0.parse_lazy(input) {
            EmptyOk((o, input)) => match (self.1)(o) {
                Ok(o) => EmptyOk((o, input)),
                Err(err) => EmptyErr(
                    <Self::Input as StreamOnce>::Error::from_error(position, err.into()).into(),
                ),
            },
            ConsumedOk((o, input)) => match (self.1)(o) {
                Ok(o) => ConsumedOk((o, input)),
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

macro_rules! dispatch_on {
    ($i: expr, $f: expr;) => {
    };
    ($i: expr, $f: expr; $first: ident $(, $id: ident)*) => { {
        $f($i, $first);
        dispatch_on!($i + 1, $f; $($id),*);
    } }
}

trait SeqParser {
    type Input: StreamOnce;
    type Output;

    #[inline]
    fn parse_lazy(&mut self, input: Self::Input) -> ConsumedResult<Self::Output, Self::Input>;
}

macro_rules! tuple_parser {
    ($h: ident, $($id: ident),+) => {
        // struct Seq<'a>( $(&'a mut $id ),* );

        #[allow(non_snake_case)]
        impl <Input: Stream, $h:, $($id:),+> Parser for ($h, $($id),+)
            where Input: Stream,
                  Input::Error: ParseError<Input::Item, Input::Range, Input::Position>,
                  $h: Parser<Input=Input>,
                  $($id: Parser<Input=Input>),+
        {
            type Input = Input;
            type Output = ($h::Output, $($id::Output),+);

            #[inline]
            #[allow(unused_assignments)]
            fn parse_lazy(&mut self,
                          mut input: Input)
                          -> ConsumedResult<($h::Output, $($id::Output),+), Input> {
                let (ref mut $h, $(ref mut $id),+) = *self;
                let mut first_empty_parser = 0;
                let mut current_parser = 0;

                fn add_errors<Input2, $h $(, $id)*>(
                    first_empty_parser: usize,
                    err: &mut Tracked<Input2::Error>,
                    $h: &mut $h $(, $id : &mut $id )*
                )
                    where Input2: Stream,
                          Input2::Error: ParseError<Input2::Item, Input2::Range, Input2::Position>,
                          $h: Parser<Input=Input2>,
                          $($id: Parser<Input=Input2>),+
                {
                    dispatch_on!(0, |i, p| {
                        if i >= first_empty_parser {
                            Parser::add_error(p, err);
                        }
                    }; $h, $($id),*);
                }

                macro_rules! add_errors {
                    ($err: ident) => { add_errors(first_empty_parser, &mut $err, $h, $($id),*) }
                }

                let temp = match $h.parse_lazy(input) {
                    ConsumedOk((x, new_input)) => {
                        first_empty_parser = current_parser + 1;
                        input = new_input;
                        x
                    }
                    EmptyErr(err) => return EmptyErr(err),
                    ConsumedErr(err) => return ConsumedErr(err),
                    EmptyOk((x, new_input)) => {
                        input = new_input;
                        x
                    }
                };
                let mut offset = $h.parser_count().0.saturating_add(1);
                let $h = temp;
                $(
                    current_parser += 1;
                    let temp = match $id.parse_lazy(input.clone()) {
                        ConsumedOk((x, new_input)) => {
                            first_empty_parser = current_parser + 1;
                            input = new_input;
                            x
                        }
                        EmptyErr(mut err) => {
                            if first_empty_parser != 0 {
                                if let Ok(t) = input.uncons::<UnexpectedParse>() {
                                    err.error.add(StreamError::unexpected_token(t));
                                }
                                add_errors!(err);
                                return ConsumedErr(err.error)
                            } else {
                                err.offset = ErrorOffset(offset);
                                return EmptyErr(err)
                            }
                        }
                        ConsumedErr(err) => return ConsumedErr(err),
                        EmptyOk((x, new_input)) => {
                            input = new_input;
                            x
                        }
                    };
                    offset = offset.saturating_add($id.parser_count().0);
                    let $id = temp;
                )+
                if first_empty_parser != 0 {
                    ConsumedOk((($h, $($id),+), input))
                } else {
                    EmptyOk((($h, $($id),+), input))
                }
            }

            #[inline(always)]
            fn parser_count(&self) -> ErrorOffset {
                let (ref $h, $(ref $id),+) = *self;
                ErrorOffset($h.parser_count().0 $( + $id.parser_count().0)+)
            }

            #[inline(always)]
            fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
                let (ref mut $h, $(ref mut $id),+) = *self;
                $h.add_error(errors);
                if errors.offset <= ErrorOffset(1) {
                    return;
                }
                errors.offset = ErrorOffset(errors.offset.0.saturating_sub($h.parser_count().0));
                $(
                    $id.add_error(errors);
                    if errors.offset <= ErrorOffset(1) {
                        return;
                    }
                    errors.offset = ErrorOffset(
                        errors.offset.0.saturating_sub($id.parser_count().0)
                    );
                )*
            }
        }
    }
}

tuple_parser!(A, B);
tuple_parser!(A, B, C);
tuple_parser!(A, B, C, D);
tuple_parser!(A, B, C, D, E);
tuple_parser!(A, B, C, D, E, F);
tuple_parser!(A, B, C, D, E, F, G);
tuple_parser!(A, B, C, D, E, F, G, H);
tuple_parser!(A, B, C, D, E, F, G, H, I);
tuple_parser!(A, B, C, D, E, F, G, H, I, J);
tuple_parser!(A, B, C, D, E, F, G, H, I, J, K);
tuple_parser!(A, B, C, D, E, F, G, H, I, J, K, L);

#[macro_export]
#[doc(hidden)]
macro_rules! seq_parser_expr {
    (; $($tt: tt)*) => {
        ( $($tt)* )
    };
    ( (_ : $first_parser: expr, $($remaining: tt)+ ); $($tt: tt)*) => {
        seq_parser_expr!( ( $($remaining)+ ) ; $($tt)* $first_parser, )
    };
    ( ($first_field: ident : $first_parser: expr, $($remaining: tt)+ ); $($tt: tt)*) => {
        seq_parser_expr!( ( $($remaining)+ ) ; $($tt)* $first_parser, )
    };
    ( (_ : $first_parser: expr ); $($tt: tt)*) => {
        ( $($tt)* $first_parser, )
    };
    ( ($first_field: ident : $first_parser: expr, ); $($tt: tt)*) => {
        seq_parser_expr!(; $($tt)* $first_parser,)
    };
    ( (_ : $first_parser: expr, ); $($tt: tt)*) => {
        ( $($tt)* $first_parser, )
    };
    ( ($first_field: ident : $first_parser: expr ); $($tt: tt)*) => {
        seq_parser_expr!(; $($tt)* $first_parser,)
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! seq_parser_pattern {
    (; $($tt: tt)*) => {
       ( $($tt)* )
    };
    ( (_ : $first_parser: expr, $($remaining: tt)+ ); $($tt: tt)*) => {
        seq_parser_pattern!( ( $($remaining)+ ) ; $($tt)* _, )
    };
    ( ($first_field: ident : $first_parser: expr, $($remaining: tt)+ ); $($tt: tt)*) => {
        seq_parser_pattern!( ( $($remaining)+ ) ; $($tt)* $first_field, )
    };
    ( ( _ : $first_parser: expr ); $($tt: tt)*) => {
        seq_parser_pattern!(; $($tt)* _, )
    };
    ( ($first_field: ident : $first_parser: expr ); $($tt: tt)*) => {
        seq_parser_pattern!(; $($tt)* $first_field,)
    };
    ( ( _ : $first_parser: expr, ); $($tt: tt)*) => {
        seq_parser_pattern!(; $($tt)* _, )
    };
    ( ($first_field: ident : $first_parser: expr, ); $($tt: tt)*) => {
        seq_parser_pattern!(; $($tt)* $first_field,)
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! seq_parser_impl {
    (; $name: ident $($tt: tt)*) => {
        $name { $($tt)* }
    };
    ( (_ : $first_parser: expr, $($remaining: tt)+ ); $name: ident $($tt: tt)*) => {
        seq_parser_impl!( ( $($remaining)+ ) ; $name $($tt)* )
    };
    ( ($first_field: ident : $first_parser: expr, $($remaining: tt)+ );
        $name: ident $($tt: tt)*) =>
    {
        seq_parser_impl!( ( $($remaining)+ ) ; $name $($tt)* $first_field: $first_field, )
    };
    ( ( _ : $first_parser: expr ); $name: ident $($tt: tt)*) => {
        seq_parser_impl!( ; $name $($tt)* )
    };
    ( ($first_field: ident : $first_parser: expr ); $name: ident $($tt: tt)*) => {
        seq_parser_impl!(; $name $($tt)* $first_field: $first_field,)
    };
    ( ( _ : $first_parser: expr, ); $name: ident $($tt: tt)*) => {
        seq_parser_impl!(; $name $($tt)*)
    };
    ( ($first_field: ident : $first_parser: expr, ); $name: ident $($tt: tt)*) => {
        seq_parser_impl!(; $name $($tt)* $first_field: $first_field,)
    };
}

/// Sequences multiple parsers and builds a struct out of them.
///
/// ```
/// #[macro_use]
/// extern crate combine;
/// use combine::{Parser, many, token};
/// use combine::byte::{letter, spaces};
///
/// #[derive(Debug, PartialEq)]
/// struct Field {
///     name: Vec<u8>,
///     value: Vec<u8>,
/// }
/// fn main() {
///     let mut parser = struct_parser!{
///         Field {
///             name: many(letter()),
///             // `_` fields are ignored when building the struct
///             _: spaces(),
///             _: token(b':'),
///             _: spaces(),
///             value: many(letter()),
///         }
///     };
///     assert_eq!(
///         parser.parse(&b"test: data"[..]),
///         Ok((Field { name: b"test"[..].to_owned(), value: b"data"[..].to_owned() }, &b""[..]))
///     );
/// }
/// ```
#[macro_export]
macro_rules! struct_parser {
    ($name: ident { $($tt: tt)* }) => {
        seq_parser_expr!( ( $($tt)* ); )
            .map(|seq_parser_pattern!( ( $($tt)* ); )|
                seq_parser_impl!(( $($tt)* ); $name )
            )
    }
}

#[derive(Copy, Clone)]
pub struct EnvParser<E, I, T>
where
    I: Stream,
{
    env: E,
    parser: fn(E, I) -> ParseResult<T, I>,
}

impl<E, I, O> Parser for EnvParser<E, I, O>
where
    E: Clone,
    I: Stream,
{
    type Input = I;
    type Output = O;

    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<O, I> {
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
///     fn string<I>(&self, input: I) -> ParseResult<u32, I>
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
pub fn env_parser<E, I, O>(env: E, parser: fn(E, I) -> ParseResult<O, I>) -> EnvParser<E, I, O>
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

impl<P, F> Parser for Recognize<F, P>
where
    P: Parser,
    F: FromIterator<<P::Input as StreamOnce>::Item>,
{
    type Input = P::Input;
    type Output = F;

    #[inline]
    fn parse_lazy(&mut self, mut input: P::Input) -> ConsumedResult<F, P::Input> {
        match self.0.parse_lazy(input.clone()) {
            EmptyOk((_, rest)) => {
                let result = (0..)
                    .scan((), |_, _| {
                        if input.position() != rest.position() {
                            Some(input.uncons())
                        } else {
                            None
                        }
                    })
                    .collect::<Result<_, _>>();
                match result {
                    Ok(x) => EmptyOk((x, rest)),
                    Err(err) => EmptyErr(
                        <P::Input as StreamOnce>::Error::from_error(input.position(), err).into(),
                    ),
                }
            }
            ConsumedOk((_, rest)) => {
                let result = (0..)
                    .scan((), |_, _| {
                        if input.position() != rest.position() {
                            Some(input.uncons())
                        } else {
                            None
                        }
                    })
                    .collect::<Result<_, _>>();
                match result {
                    Ok(x) => ConsumedOk((x, rest)),
                    Err(err) => ConsumedErr(
                        <P::Input as StreamOnce>::Error::from_error(input.position(), err).into(),
                    ),
                }
            }
            ConsumedErr(err) => ConsumedErr(err),
            EmptyErr(err) => EmptyErr(err),
        }
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
/// use combine::char::digit;
///
/// let mut parser = recognize((skip_many1(digit()), token('.'), skip_many1(digit())));
/// assert_eq!(parser.parse("123.45"), Ok(("123.45".to_string(), "")));
/// assert_eq!(parser.parse("123.45"), Ok(("123.45".to_string(), "")));
/// ```
#[inline(always)]
pub fn recognize<F, P>(parser: P) -> Recognize<F, P>
where
    P: Parser,
    F: FromIterator<<P::Input as StreamOnce>::Item>,
{
    Recognize(parser, PhantomData)
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::Parser;
    use char::{digit, letter};
    use range::range;

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
    use primitives::Parser;
    use easy::{Error, Errors, StreamErrors};
    use char::{char, digit, letter};
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
        let mut p2 = (optional(char('b')), char('2')).map(|t| t.1);
        let mut parser = choice::<[&mut Parser<Input = _, Output = _>; 2]>([&mut p1, &mut p2]);

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
}

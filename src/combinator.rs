use std::iter::FromIterator;
use std::marker::PhantomData;
use primitives::{Info, Parser, ParseResult, ConsumedResult, ParseError, Stream, StreamOnce, Error,
                 Consumed};
use primitives::FastResult::*;

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
        fn add_error(&mut self, error: &mut ParseError<Self::Input>) {
            self.0.add_error(error)
        }
    }
}
}

#[derive(Clone)]
pub struct Any<I>(PhantomData<fn(I) -> I>);

impl<I> Parser for Any<I>
    where I: Stream
{
    type Input = I;
    type Output = I::Item;
    #[inline]
    fn parse_lazy(&mut self, mut input: I) -> ConsumedResult<I::Item, I> {
        let position = input.position();
        match input.uncons() {
            Ok(x) => ConsumedOk((x, input)),
            Err(err) => ConsumedErr(ParseError::new(position, err)),
        }
    }
}

/// Parses any token
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
    where I: Stream
{
    Any(PhantomData)
}



#[derive(Clone)]
pub struct Satisfy<I, P> {
    predicate: P,
    _marker: PhantomData<I>,
}

fn satisfy_impl<I, P, R>(input: I, mut predicate: P) -> ConsumedResult<R, I>
    where I: Stream,
          P: FnMut(I::Item) -> Option<R>
{
    let mut next = input.clone();
    match next.uncons() {
        Ok(c) => {
            match predicate(c.clone()) {
                Some(c) => ConsumedOk((c, next)),
                None => EmptyErr(ParseError::empty(input.position())),
            }
        }
        Err(err) => EmptyErr(ParseError::new(input.position(), err)),
    }
}

impl<I, P> Parser for Satisfy<I, P>
    where I: Stream,
          P: FnMut(I::Item) -> bool
{
    type Input = I;
    type Output = I::Item;
    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<I::Item, I> {
        satisfy_impl(input, |c| if (self.predicate)(c.clone()) {
            Some(c)
        } else {
            None
        })
    }
}

/// Parses a token and succeeds depending on the result of `predicate`
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
    where I: Stream,
          P: FnMut(I::Item) -> bool
{
    Satisfy {
        predicate: predicate,
        _marker: PhantomData,
    }
}

#[derive(Clone)]
pub struct SatisfyMap<I, P> {
    predicate: P,
    _marker: PhantomData<I>,
}

impl<I, P, R> Parser for SatisfyMap<I, P>
    where I: Stream,
          P: FnMut(I::Item) -> Option<R>
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
    where I: Stream,
          P: FnMut(I::Item) -> Option<R>
{
    SatisfyMap {
        predicate: predicate,
        _marker: PhantomData,
    }
}

#[derive(Clone)]
pub struct Token<I>
    where I: Stream,
          I::Item: PartialEq
{
    c: I::Item,
    _marker: PhantomData<I>,
}

impl<I> Parser for Token<I>
    where I: Stream,
          I::Item: PartialEq + Clone
{
    type Input = I;
    type Output = I::Item;
    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<I::Item, I> {
        satisfy_impl(input, |c| if c == self.c { Some(c) } else { None })
    }
    fn add_error(&mut self, error: &mut ParseError<Self::Input>) {
        error.errors.push(Error::Expected(Info::Token(self.c.clone())));
    }
}

/// Parses a character and succeeds if the character is equal to `c`
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
    where I: Stream,
          I::Item: PartialEq
{
    Token {
        c: c,
        _marker: PhantomData,
    }
}

#[derive(Clone)]
pub struct Tokens<C, T, I>
    where I: Stream
{
    cmp: C,
    expected: Info<I::Item, I::Range>,
    tokens: T,
    _marker: PhantomData<I>,
}

impl<C, T, I> Parser for Tokens<C, T, I>
    where C: FnMut(T::Item, I::Item) -> bool,
          T: Clone + IntoIterator,
          I: Stream
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
                            let errors = vec![Error::Unexpected(Info::Token(other)),
                                              Error::Expected(self.expected.clone())];
                            let error = ParseError::from_errors(start, errors);
                            ConsumedErr(error)
                        } else {
                            EmptyErr(ParseError::empty(start))
                        };
                    }
                    consumed = true;
                    input = rest.into_inner();
                }
                Err(error) => {
                    return error.combine_consumed(|mut error| {
                        error.position = start;
                        if consumed {
                            ConsumedErr(error)
                        } else {
                            EmptyErr(error)
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
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        errors.add_error(Error::Expected(self.expected.clone()));
    }
}

/// Parses `tokens`.
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
/// let result = tokens(|&l, r| (if l < r { r - l } else { l - r }) <= 2, Info::Range(&b"025"[..]), &b"025"[..])
///     .parse(&b"123"[..])
///     .map(|x| x.0);
/// assert_eq!(result, Ok(&b"025"[..]));
/// # }
/// ```
#[inline(always)]
pub fn tokens<C, T, I>(cmp: C, expected: Info<I::Item, I::Range>, tokens: T) -> Tokens<C, T, I>
    where C: FnMut(T::Item, I::Item) -> bool,
          T: Clone + IntoIterator,
          I: Stream
{
    Tokens {
        cmp: cmp,
        expected: expected,
        tokens: tokens,
        _marker: PhantomData,
    }
}


#[derive(Clone)]
pub struct Position<I>
    where I: Stream
{
    _marker: PhantomData<I>,
}

impl<I> Parser for Position<I>
    where I: Stream
{
    type Input = I;
    type Output = I::Position;

    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<I::Position, I> {
        EmptyOk((input.position(), input))
    }
}

/// Parser which just returns the current position in the stream
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::primitives::SourcePosition;
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
    where I: Stream
{
    Position { _marker: PhantomData }
}

#[derive(Clone)]
pub struct Choice<S, P>(S, PhantomData<P>);

impl<I, O, S, P> Parser for Choice<S, P>
    where I: Stream,
          S: AsMut<[P]>,
          P: Parser<Input = I, Output = O>
{
    type Input = I;
    type Output = O;
    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<O, I> {
        let mut empty_err = None;
        for p in AsMut::as_mut(&mut self.0) {
            match p.parse_lazy(input.clone()) {
                consumed_err @ ConsumedErr(_) => return consumed_err,
                EmptyErr(err) => {
                    empty_err = match empty_err {
                        None => Some(err),
                        Some(prev_err) => Some(prev_err.merge(err)),
                    };
                }
                ok @ ConsumedOk(_) => return ok,
                ok @ EmptyOk(_) => return ok,
            }
        }
        EmptyErr(match empty_err {
            None => {
                ParseError::new(input.position(),
                                Error::Message("parser choice is empty".into()))
            }
            Some(err) => err,
        })
    }
    fn add_error(&mut self, error: &mut ParseError<Self::Input>) {
        for p in self.0.as_mut() {
            p.add_error(error);
        }
    }
}

#[derive(Clone)]
pub struct OneOf<T, I>
    where I: Stream
{
    tokens: T,
    _marker: PhantomData<I>,
}

impl<T, I> Parser for OneOf<T, I>
    where T: Clone + IntoIterator<Item = I::Item>,
          I: Stream,
          I::Item: PartialEq
{
    type Input = I;
    type Output = I::Item;

    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<I::Item, I> {
        satisfy(|c| self.tokens.clone().into_iter().any(|t| t == c)).parse_lazy(input)
    }

    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        for expected in self.tokens.clone() {
            errors.add_error(Error::Expected(Info::Token(expected)));
        }
    }
}

/// Extract one token and succeeds if it is part of `tokens`.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::primitives::Info;
/// # fn main() {
/// let result = many(one_of("abc".chars()))
///     .parse("abd");
/// assert_eq!(result, Ok((String::from("ab"), "d")));
/// # }
/// ```
#[inline(always)]
pub fn one_of<T, I>(tokens: T) -> OneOf<T, I>
    where T: Clone + IntoIterator,
          I: Stream,
          I::Item: PartialEq<T::Item>
{
    OneOf {
        tokens: tokens,
        _marker: PhantomData,
    }
}

#[derive(Clone)]
pub struct NoneOf<T, I>
    where I: Stream
{
    tokens: T,
    _marker: PhantomData<I>,
}

impl<T, I> Parser for NoneOf<T, I>
    where T: Clone + IntoIterator<Item = I::Item>,
          I: Stream,
          I::Item: PartialEq
{
    type Input = I;
    type Output = I::Item;

    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<I::Item, I> {
        satisfy(|c| self.tokens.clone().into_iter().all(|t| t != c)).parse_lazy(input)
    }
}

/// Extract one token and succeeds if it is part of `tokens`.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::primitives::Info;
/// # fn main() {
/// let result = many(none_of("abc".chars()))
///     .parse("edc");
/// assert_eq!(result, Ok((String::from("ed"), "c")));
/// # }
/// ```
#[inline(always)]
pub fn none_of<T, I>(tokens: T) -> NoneOf<T, I>
    where T: Clone + IntoIterator,
          I: Stream,
          I::Item: PartialEq<T::Item>
{
    NoneOf {
        tokens: tokens,
        _marker: PhantomData,
    }
}

#[derive(Clone)]
pub struct Count<F, P> {
    parser: P,
    count: usize,
    _marker: PhantomData<fn() -> F>,
}

impl<P, F> Parser for Count<F, P>
    where P: Parser,
          F: FromIterator<P::Output>
{
    type Input = P::Input;
    type Output = F;

    #[inline]
    fn parse_lazy(&mut self, input: P::Input) -> ConsumedResult<F, P::Input> {
        let mut iter = self.parser.by_ref().iter(input);
        let value = iter.by_ref().take(self.count).collect();
        iter.into_result_fast(value)
    }

    fn add_error(&mut self, error: &mut ParseError<Self::Input>) {
        self.parser.add_error(error)
    }
}

/// Extract one token and succeeds if it is part of `tokens`.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::primitives::Info;
/// # fn main() {
/// let result = many(none_of("abc".chars()))
///     .parse("edc");
/// assert_eq!(result, Ok((String::from("ed"), "c")));
/// # }
/// ```
#[inline(always)]
pub fn count<F, P>(count: usize, parser: P) -> Count<F, P>
    where P: Parser,
          F: FromIterator<P::Output>
{
    Count {
        parser: parser,
        count: count,
        _marker: PhantomData,
    }
}

/// Takes an array of parsers and tries to apply them each in order.
/// Fails if all parsers fails or if an applied parser consumes input before failing.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::char::string;
/// # use combine::primitives::Error;
/// # fn main() {
/// let mut parser = choice([string("Apple"), string("Banana"), string("Orange")]);
/// assert_eq!(parser.parse("Banana"), Ok(("Banana", "")));
/// assert_eq!(parser.parse("Orangexx"), Ok(("Orange", "xx")));
/// assert!(parser.parse("Appl").is_err());
/// assert!(parser.parse("Pear").is_err());
///
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
pub fn choice<S, P>(ps: S) -> Choice<S, P>
    where S: AsMut<[P]>,
          P: Parser
{
    Choice(ps, PhantomData)
}

#[derive(Clone)]
pub struct Unexpected<I>(Info<I::Item, I::Range>, PhantomData<fn(I) -> I>) where I: Stream;
impl<I> Parser for Unexpected<I>
    where I: Stream
{
    type Input = I;
    type Output = ();
    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<(), I> {
        EmptyErr(ParseError::empty(input.position()))
    }
    fn add_error(&mut self, error: &mut ParseError<Self::Input>) {
        error.errors.push(Error::Unexpected(self.0.clone()));
    }
}
/// Always fails with `message` as an unexpected error.
/// Never consumes any input.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::primitives::Error;
/// # fn main() {
/// let result = unexpected("token")
///     .parse("a");
/// assert!(result.is_err());
/// assert!(result.err().unwrap().errors.iter().any(|m| *m == Error::Unexpected("token".into())));
/// # }
/// ```
#[inline(always)]
pub fn unexpected<I, S>(message: S) -> Unexpected<I>
    where I: Stream,
          S: Into<Info<I::Item, I::Range>>
{
    Unexpected(message.into(), PhantomData)
}

#[derive(Clone)]
pub struct Value<I, T>(T, PhantomData<fn(I) -> I>);
impl<I, T> Parser for Value<I, T>
    where I: Stream,
          T: Clone
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
    where I: Stream,
          T: Clone
{
    Value(v, PhantomData)
}

impl_parser! { NotFollowedBy(P,),
               Or<Then<Try<P>, fn(P::Output) -> Unexpected<P::Input>>, Value<P::Input, ()>>
}

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
pub fn not_followed_by<P>(parser: P) -> NotFollowedBy<P>
    where P: Parser,
          P::Output: ::std::fmt::Display
{
    fn f<T: ::std::fmt::Display, I: Stream>(t: T) -> Unexpected<I> {
        unexpected(format!("{}", t))
    }
    let f: fn(P::Output) -> Unexpected<P::Input> = f;
    NotFollowedBy(try(parser)
        .then(f)
        .or(value(())))
}

#[derive(Clone)]
pub struct Eof<I>(PhantomData<I>);
impl<I> Parser for Eof<I>
    where I: Stream
{
    type Input = I;
    type Output = ();

    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<(), I> {
        match input.clone().uncons() {
            Err(ref err) if *err == Error::end_of_input() => EmptyOk(((), input)),
            _ => EmptyErr(ParseError::empty(input.position())),
        }
    }

    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        errors.add_error(Error::Expected("end of input".into()))
    }
}

/// Succeeds only if the stream is at end of input, fails otherwise.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::primitives::{Error, Positioner};
/// # fn main() {
/// let mut parser = eof();
/// assert_eq!(parser.parse(State::new("")), Ok(((), State::new(""))));
/// assert_eq!(parser.parse(State::new("x")), Err(ParseError {
///     position: <char as Positioner>::start(),
///     errors: vec![
///         Error::Unexpected('x'.into()),
///         Error::Expected("end of input".into())
///     ]
/// }));
/// # }
/// ```
#[inline(always)]
pub fn eof<I>() -> Eof<I>
    where I: Stream
{
    Eof(PhantomData)
}

pub struct Iter<P: Parser> {
    parser: P,
    input: P::Input,
    consumed: bool,
    state: State<P::Input>,
}

enum State<I: StreamOnce> {
    Ok,
    EmptyErr,
    ConsumedErr(ParseError<I>),
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
            State::Ok | State::EmptyErr => {
                if self.consumed {
                    ConsumedOk((value, self.input))
                } else {
                    EmptyOk((value, self.input))
                }
            }
            State::ConsumedErr(e) => ConsumedErr(e),
        }
    }
}

impl<P: Parser> Iterator for Iter<P> {
    type Item = P::Output;
    fn next(&mut self) -> Option<P::Output> {
        match self.state {
            State::Ok => {
                match self.parser.parse_lazy(self.input.clone()) {
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
                }
            }
            State::ConsumedErr(_) |
            State::EmptyErr => None,
        }
    }
}

#[derive(Clone)]
pub struct Many<F, P>(P, PhantomData<F>) where P: Parser;
impl<F, P> Parser for Many<F, P>
    where P: Parser,
          F: FromIterator<P::Output>
{
    type Input = P::Input;
    type Output = F;
    fn parse_stream_consumed(&mut self, input: P::Input) -> ConsumedResult<F, P::Input> {
        let mut iter = (&mut self.0).iter(input);
        let result = iter.by_ref().collect();
        iter.into_result_fast(result)
    }
}

/// Parses `p` zero or more times returning a collection with the values from `p`.
/// If the returned collection cannot be inferred type annotations must be supplied, either by
/// annotating the resulting type binding `let collection: Vec<_> = ...` or by specializing when
/// calling many, `many::<Vec<_>, _>(...)`
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
    where P: Parser,
          F: FromIterator<P::Output>
{
    Many(p, PhantomData)
}


#[derive(Clone)]
pub struct Many1<F, P>(P, PhantomData<fn() -> F>);
impl<F, P> Parser for Many1<F, P>
    where F: FromIterator<P::Output>,
          P: Parser
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
        let result = Some(first)
            .into_iter()
            .chain(iter.by_ref())
            .collect();
        iter.into_result_fast(result)
    }
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors)
    }
}

impl_parser!{ SkipMany(P,), Map<Many<Vec<()>, Map<P, fn (P::Output)>>, fn (Vec<()>)> }
/// Parses `p` zero or more times ignoring the result
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
    where P: Parser
{
    fn ignore<T>(_: T) {}
    let ignore1: fn(P::Output) = ignore;
    let ignore2: fn(Vec<()>) = ignore;
    SkipMany(many(p.map(ignore1)).map(ignore2))
}

impl_parser!{ SkipMany1(P,), Map<Many1<Vec<()>, Map<P, fn (P::Output)>>, fn (Vec<()>)> }
/// Parses `p` one or more times ignoring the result
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
    where P: Parser
{
    fn ignore<T>(_: T) {}
    let ignore1: fn(P::Output) = ignore;
    let ignore2: fn(Vec<()>) = ignore;
    SkipMany1(many1(p.map(ignore1)).map(ignore2))
}

/// Parses `p` one or more times returning a collection with the values from `p`.
/// If the returned collection cannot be inferred type annotations must be supplied, either by
/// annotating the resulting type binding `let collection: Vec<_> = ...` or by specializing when
/// calling many1 `many1::<Vec<_>, _>(...)`
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
    where F: FromIterator<P::Output>,
          P: Parser
{
    Many1(p, PhantomData)
}

#[derive(Clone)]
pub struct SepBy<F, P, S> {
    parser: P,
    separator: S,
    _marker: PhantomData<fn() -> F>,
}
impl<F, P, S> Parser for SepBy<F, P, S>
    where F: FromIterator<P::Output>,
          P: Parser,
          S: Parser<Input = P::Input>
{
    type Input = P::Input;
    type Output = F;

    #[inline]
    fn parse_lazy(&mut self, input: P::Input) -> ConsumedResult<F, P::Input> {
        sep_by1(&mut self.parser, &mut self.separator)
            .or(parser(|input| Ok((None.into_iter().collect(), Consumed::Empty(input)))))
            .parse_lazy(input)
    }

    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.parser.add_error(errors)
    }
}

/// Parses `parser` zero or more time separated by `separator`, returning a collection with the
/// values from `p`. If the returned collection cannot be inferred type annotations must be
/// supplied, either by annotating the resulting type binding `let collection: Vec<_> = ...` or by
/// specializing when calling sep_by, `sep_by::<Vec<_>, _, _>(...)`
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
    where F: FromIterator<P::Output>,
          P: Parser,
          S: Parser<Input = P::Input>
{
    SepBy {
        parser: parser,
        separator: separator,
        _marker: PhantomData,
    }
}

#[derive(Clone)]
pub struct SepBy1<F, P, S> {
    parser: P,
    separator: S,
    _marker: PhantomData<fn() -> F>,
}
impl<F, P, S> Parser for SepBy1<F, P, S>
    where F: FromIterator<P::Output>,
          P: Parser,
          S: Parser<Input = P::Input>
{
    type Input = P::Input;
    type Output = F;

    #[inline]
    fn parse_lazy(&mut self, input: P::Input) -> ConsumedResult<F, P::Input> {
        let (first, rest) = ctry!(self.parser.parse_lazy(input.clone()));

        rest.combine_consumed(move |input| {
            let rest = (&mut self.separator).with(&mut self.parser);
            let mut iter = Iter::new(rest, input);
            let result = Some(first)
                .into_iter()
                .chain(iter.by_ref())
                .collect();
            iter.into_result_fast(result)
        })
    }

    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.parser.add_error(errors)
    }
}

/// Parses `parser` one or more time separated by `separator`, returning a collection with the
/// values from `p`. If the returned collection cannot be inferred type annotations must be
/// supplied, either by annotating the resulting type binding `let collection: Vec<_> = ...` or by
/// specializing when calling sep_by, `sep_by1::<Vec<_>, _, _>(...)`
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::char::digit;
/// # use combine::primitives::{Error, Positioner};
/// # fn main() {
/// let mut parser = sep_by1(digit(), token(','));
/// let result_ok = parser.parse(State::new("1,2,3"))
///                       .map(|(vec, state)| (vec, state.input));
/// assert_eq!(result_ok, Ok((vec!['1', '2', '3'], "")));
/// let result_err = parser.parse(State::new(""));
/// assert_eq!(result_err, Err(ParseError {
///     position: <char as Positioner>::start(),
///     errors: vec![
///         Error::end_of_input(),
///         Error::Expected("digit".into())
///     ]
/// }));
/// # }
/// ```
#[inline(always)]
pub fn sep_by1<F, P, S>(parser: P, separator: S) -> SepBy1<F, P, S>
    where F: FromIterator<P::Output>,
          P: Parser,
          S: Parser<Input = P::Input>
{
    SepBy1 {
        parser: parser,
        separator: separator,
        _marker: PhantomData,
    }
}

#[derive(Clone)]
pub struct SepEndBy<F, P, S> {
    parser: P,
    separator: S,
    _marker: PhantomData<fn() -> F>,
}

impl<F, P, S> Parser for SepEndBy<F, P, S>
    where F: FromIterator<P::Output>,
          P: Parser,
          S: Parser<Input = P::Input>
{
    type Input = P::Input;
    type Output = F;

    #[inline]
    fn parse_lazy(&mut self, input: P::Input) -> ConsumedResult<F, P::Input> {
        sep_end_by1(&mut self.parser, &mut self.separator)
            .or(parser(|input| Ok((None.into_iter().collect(), Consumed::Empty(input)))))
            .parse_lazy(input)
    }

    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.parser.add_error(errors)
    }
}

/// Parses `parser` zero or more time separated by `separator`, returning a collection with the
/// values from `p`. If the returned collection cannot be inferred type annotations must be
/// supplied, either by annotating the resulting type binding `let collection: Vec<_> = ...` or by
/// specializing when calling sep_by, `sep_by::<Vec<_>, _, _>(...)`
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
    where F: FromIterator<P::Output>,
          P: Parser,
          S: Parser<Input = P::Input>
{
    SepEndBy {
        parser: parser,
        separator: separator,
        _marker: PhantomData,
    }
}

#[derive(Clone)]
pub struct SepEndBy1<F, P, S> {
    parser: P,
    separator: S,
    _marker: PhantomData<fn() -> F>,
}

impl<F, P, S> Parser for SepEndBy1<F, P, S>
    where F: FromIterator<P::Output>,
          P: Parser,
          S: Parser<Input = P::Input>
{
    type Input = P::Input;
    type Output = F;

    #[inline]
    fn parse_lazy(&mut self, input: P::Input) -> ConsumedResult<F, P::Input> {
        let (first, input) = ctry!(self.parser.parse_lazy(input.clone()));

        input.combine_consumed(|input| {
            let rest = (&mut self.separator).with(optional(&mut self.parser));
            let mut iter = Iter::new(rest, input);
            // `iter` yields Option<P::Output>, by using flat map we make sure that we stop
            // iterating once a None element is received, i.e `self.parser` did not parse
            // successfully
            let result = Some(first)
                .into_iter()
                .chain(iter.by_ref().flat_map(|x| x))
                .collect();
            iter.into_result_fast(result)
        })
    }

    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.parser.add_error(errors)
    }
}

/// Parses `parser` one or more time separated by `separator`, returning a collection with the
/// values from `p`. If the returned collection cannot be inferred type annotations must be
/// supplied, either by annotating the resulting type binding `let collection: Vec<_> = ...` or by
/// specializing when calling sep_by, `sep_by1::<Vec<_>, _, _>(...)`
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::char::digit;
/// # use combine::primitives::{Error, Positioner};
/// # fn main() {
/// let mut parser = sep_end_by1(digit(), token(';'));
/// let result_ok = parser.parse(State::new("1;2;3;"))
///                       .map(|(vec, state)| (vec, state.input));
/// assert_eq!(result_ok, Ok((vec!['1', '2', '3'], "")));
/// let result_err = parser.parse(State::new(""));
/// assert_eq!(result_err, Err(ParseError {
///     position: <char as Positioner>::start(),
///     errors: vec![
///         Error::end_of_input(),
///         Error::Expected("digit".into())
///     ]
/// }));
/// # }
/// ```
#[inline(always)]
pub fn sep_end_by1<F, P, S>(parser: P, separator: S) -> SepEndBy1<F, P, S>
    where F: FromIterator<P::Output>,
          P: Parser,
          S: Parser<Input = P::Input>
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
#[derive(Clone)]
pub struct FnParser<I, F>(F, PhantomData<fn(I) -> I>);

/// Wraps a function, turning it into a parser
/// Mainly needed to turn closures into parsers as function types can be casted to function pointers
/// to make them usable as a parser
///
/// ```
/// extern crate combine;
/// # use combine::*;
/// # use combine::char::digit;
/// # use combine::primitives::{Consumed, Error};
/// # fn main() {
/// let mut even_digit = parser(|input| {
///     // Help type inference out
///     let _: &str = input;
///     let position = input.position();
///     let (char_digit, input) = try!(digit().parse_stream(input));
///     let d = (char_digit as i32) - ('0' as i32);
///     if d % 2 == 0 {
///         Ok((d, input))
///     }
///     else {
///         //Return an empty error since we only tested the first token of the stream
///         let errors = ParseError::new(position, Error::Expected(From::from("even number")));
///         Err(Consumed::Empty(errors))
///     }
/// });
/// let result = even_digit
///     .parse("8")
///     .map(|x| x.0);
/// assert_eq!(result, Ok(8));
/// # }
/// ```
#[inline(always)]
pub fn parser<I, O, F>(f: F) -> FnParser<I, F>
    where I: Stream,
          F: FnMut(I) -> ParseResult<O, I>
{
    FnParser(f, PhantomData)
}

impl<I, O, F> Parser for FnParser<I, F>
    where I: Stream,
          F: FnMut(I) -> ParseResult<O, I>
{
    type Input = I;
    type Output = O;
    fn parse_stream(&mut self, input: I) -> ParseResult<O, I> {
        (self.0)(input)
    }
}

impl<I, O> Parser for fn(I) -> ParseResult<O, I>
    where I: Stream
{
    type Input = I;
    type Output = O;
    fn parse_stream(&mut self, input: I) -> ParseResult<O, I> {
        self(input)
    }
}

#[derive(Clone)]
pub struct Optional<P>(P);
impl<P> Parser for Optional<P>
    where P: Parser
{
    type Input = P::Input;
    type Output = Option<P::Output>;
    #[inline]
    fn parse_lazy(&mut self, input: P::Input) -> ConsumedResult<Option<P::Output>, P::Input> {
        match self.0.parse_stream(input.clone()) {
            Ok((x, rest)) => Ok((Some(x), rest)).into(),
            Err(Consumed::Consumed(err)) => ConsumedErr(err),
            Err(Consumed::Empty(_)) => EmptyOk((None, input)),
        }
    }
}

/// Returns `Some(value)` and `None` on parse failure (always succeeds)
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::char::digit;
/// # fn main() {
/// let mut parser = optional(digit());
/// let result1 = parser.parse("a");
/// assert_eq!(result1, Ok((None, "a")));
/// let result2 = parser.parse("1");
/// assert_eq!(result2, Ok((Some('1'), "")));
/// # }
/// ```
#[inline(always)]
pub fn optional<P>(parser: P) -> Optional<P>
    where P: Parser
{
    Optional(parser)
}

impl_parser! { Between(L, R, P), Skip<With<L, P>, R> }
/// Parses `open` followed by `parser` followed by `close`
/// Returns the value of `parser`
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
    where I: Stream,
          L: Parser<Input = I>,
          R: Parser<Input = I>,
          P: Parser<Input = I>
{
    Between(open.with(parser).skip(close))
}

#[derive(Clone)]
pub struct Chainl1<P, Op>(P, Op);
impl<I, P, Op> Parser for Chainl1<P, Op>
    where I: Stream,
          P: Parser<Input = I>,
          Op: Parser<Input = I>,
          Op::Output: FnOnce(P::Output, P::Output) -> P::Output
{
    type Input = I;
    type Output = P::Output;

    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<P::Output, I> {
        let (mut l, mut input) = ctry!(self.0.parse_lazy(input));
        loop {
            match (&mut self.1, &mut self.0).parse_lazy(input.clone().into_inner()).into() {
                Ok(((op, r), rest)) => {
                    l = op(l, r);
                    input = input.merge(rest);
                }
                Err(Consumed::Consumed(err)) => return ConsumedErr(err),
                Err(Consumed::Empty(_)) => break,
            }
        }
        Ok((l, input)).into()
    }

    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors)
    }
}

/// Parses `p` 1 or more times separated by `op`
/// The value returned is the one produced by the left associative application of `op`
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
    where P: Parser,
          Op: Parser<Input = P::Input>,
          Op::Output: FnOnce(P::Output, P::Output) -> P::Output
{
    Chainl1(parser, op)
}

#[derive(Clone)]
pub struct Chainr1<P, Op>(P, Op);
impl<I, P, Op> Parser for Chainr1<P, Op>
    where I: Stream,
          P: Parser<Input = I>,
          Op: Parser<Input = I>,
          Op::Output: FnOnce(P::Output, P::Output) -> P::Output
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
                Err(Consumed::Consumed(err)) => return ConsumedErr(err),
                Err(Consumed::Empty(_)) => break,
            };
            match self.parse_lazy(input.clone().into_inner()).into() {
                Ok((r, rest)) => {
                    l = op(l, r);
                    input = input.merge(rest);
                }
                Err(Consumed::Consumed(err)) => return ConsumedErr(err),
                Err(Consumed::Empty(_)) => break,
            }
        }
        Ok((l, input)).into()
    }
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors)
    }
}

/// Parses `p` one or more times separated by `op`
/// The value returned is the one produced by the right associative application of `op`
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
    where P: Parser,
          Op: Parser<Input = P::Input>,
          Op::Output: FnOnce(P::Output, P::Output) -> P::Output
{
    Chainr1(parser, op)
}

#[derive(Clone)]
pub struct Try<P>(P);
impl<I, O, P> Parser for Try<P>
    where I: Stream,
          P: Parser<Input = I, Output = O>
{
    type Input = I;
    type Output = O;
    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<O, I> {
        self.0
            .parse_stream(input)
            .map_err(Consumed::as_empty)
            .into()
    }
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors)
    }
}

/// Try acts as `p` except it acts as if the parser hadn't consumed any input
/// if `p` returns an error after consuming input
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
    where P: Parser
{
    Try(p)
}

#[derive(Clone)]
pub struct LookAhead<P>(P);

impl<I, O, P> Parser for LookAhead<P>
    where I: Stream,
          P: Parser<Input = I, Output = O>
{
    type Input = I;
    type Output = O;

    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<O, I> {
        let (o, _input) = ctry!(self.0.parse_lazy(input.clone()));
        EmptyOk((o, input))
    }

    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors);
    }
}

/// look_ahead acts as p but doesn't consume input on success.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::char::string;
/// # fn main() {
//        let mut p = look_ahead(string("test"));
//
//        let result = p.parse("test str");
//        assert_eq!(result, Ok(("test", "test str")));
//
//        let result = p.parse("aet");
//        assert!(result.is_err());
/// # }
/// ```
#[inline(always)]
pub fn look_ahead<P>(p: P) -> LookAhead<P>
    where P: Parser
{
    LookAhead(p)
}

#[derive(Clone)]
pub struct With<P1, P2>((P1, P2))
    where P1: Parser,
          P2: Parser;
impl<I, P1, P2> Parser for With<P1, P2>
    where I: Stream,
          P1: Parser<Input = I>,
          P2: Parser<Input = I>
{
    type Input = I;
    type Output = P2::Output;
    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<Self::Output, I> {
        self.0.parse_lazy(input).map(|(_, b)| b)
    }
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors)
    }
}

#[inline(always)]
pub fn with<P1, P2>(p1: P1, p2: P2) -> With<P1, P2>
    where P1: Parser,
          P2: Parser<Input = P1::Input>
{
    With((p1, p2))
}

#[derive(Clone)]
pub struct Skip<P1, P2>((P1, P2))
    where P1: Parser,
          P2: Parser;
impl<I, P1, P2> Parser for Skip<P1, P2>
    where I: Stream,
          P1: Parser<Input = I>,
          P2: Parser<Input = I>
{
    type Input = I;
    type Output = P1::Output;
    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<Self::Output, I> {
        self.0.parse_lazy(input).map(|(a, _)| a)
    }
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors)
    }
}

#[inline(always)]
pub fn skip<P1, P2>(p1: P1, p2: P2) -> Skip<P1, P2>
    where P1: Parser,
          P2: Parser<Input = P1::Input>
{
    Skip((p1, p2))
}

#[derive(Clone)]
pub struct Message<P>(P, Info<<P::Input as StreamOnce>::Item, <P::Input as StreamOnce>::Range>)
    where P: Parser;
impl<I, P> Parser for Message<P>
    where I: Stream,
          P: Parser<Input = I>
{
    type Input = I;
    type Output = P::Output;

    fn parse_stream(&mut self, input: I) -> ParseResult<Self::Output, I> {
        // The message should always be added even if some input was consumed before failing
        self.0
            .parse_stream(input.clone())
            .map_err(|errors| {
                errors.map(|mut errors| {
                    errors.add_message(self.1.clone());
                    errors
                })
            })
    }

    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<Self::Output, I> {
        self.0.parse_lazy(input.clone())
    }

    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors);
        errors.add_message(self.1.clone());
    }
}

#[inline(always)]
pub fn message<P>(p: P,
                  msg: Info<<P::Input as StreamOnce>::Item, <P::Input as StreamOnce>::Range>)
                  -> Message<P>
    where P: Parser
{
    Message(p, msg)
}

#[derive(Clone)]
pub struct Or<P1, P2>(P1, P2)
    where P1: Parser,
          P2: Parser;
impl<I, O, P1, P2> Parser for Or<P1, P2>
    where I: Stream,
          P1: Parser<Input = I, Output = O>,
          P2: Parser<Input = I, Output = O>
{
    type Input = I;
    type Output = O;
    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<O, I> {
        match self.0.parse_lazy(input.clone()) {
            ConsumedOk(x) => ConsumedOk(x),
            EmptyOk(x) => EmptyOk(x),
            ConsumedErr(err) => ConsumedErr(err),
            EmptyErr(error1) => {
                match self.1.parse_lazy(input) {
                    ConsumedOk(x) => ConsumedOk(x),
                    EmptyOk(x) => EmptyOk(x),
                    ConsumedErr(err) => ConsumedErr(err),
                    EmptyErr(error2) => EmptyErr(error1.merge(error2)),
                }
            }
        }
    }
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors);
        self.1.add_error(errors);
    }
}

#[inline(always)]
pub fn or<P1, P2>(p1: P1, p2: P2) -> Or<P1, P2>
    where P1: Parser,
          P2: Parser<Input = P1::Input, Output = P1::Output>
{
    Or(p1, p2)
}

#[derive(Clone)]
pub struct Map<P, F>(P, F);
impl<I, A, B, P, F> Parser for Map<P, F>
    where I: Stream,
          P: Parser<Input = I, Output = A>,
          F: FnMut(A) -> B
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
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors);
    }
}

#[inline(always)]
pub fn map<P, F, B>(p: P, f: F) -> Map<P, F>
    where P: Parser,
          F: FnMut(P::Output) -> B
{
    Map(p, f)
}

#[derive(Clone)]
pub struct FlatMap<P, F>(P, F);
impl<I, A, B, P, F> Parser for FlatMap<P, F>
    where I: Stream,
          P: Parser<Input = I, Output = A>,
          F: FnMut(A) -> Result<B, ParseError<I>>
{
    type Input = I;
    type Output = B;
    #[inline]
    fn parse_lazy(&mut self, input: I) -> ConsumedResult<B, I> {
        match self.0.parse_lazy(input) {
            EmptyOk((o, input)) => {
                match (self.1)(o) {
                    Ok(x) => EmptyOk((x, input)),
                    Err(err) => EmptyErr(err),
                }
            }
            ConsumedOk((o, input)) => {
                match (self.1)(o) {
                    Ok(x) => ConsumedOk((x, input)),
                    Err(err) => ConsumedErr(err),
                }
            }
            EmptyErr(err) => EmptyErr(err),
            ConsumedErr(err) => ConsumedErr(err),
        }
    }
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors);
    }
}

#[inline(always)]
pub fn flat_map<P, F, B>(p: P, f: F) -> FlatMap<P, F>
    where P: Parser,
          F: FnMut(P::Output) -> Result<B, ParseError<P::Input>>
{
    FlatMap(p, f)
}

#[derive(Clone)]
pub struct Then<P, F>(P, F);
impl<P, N, F> Parser for Then<P, F>
    where F: FnMut(P::Output) -> N,
          P: Parser,
          N: Parser<Input = P::Input>
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
                    EmptyErr(x) | ConsumedErr(x) => ConsumedErr(x),
                }
            }
            EmptyErr(err) => EmptyErr(err),
            ConsumedErr(err) => ConsumedErr(err),
        }
    }
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors);
    }
}

#[inline(always)]
pub fn then<P, F, N>(p: P, f: F) -> Then<P, F>
    where F: FnMut(P::Output) -> N,
          P: Parser,
          N: Parser<Input = P::Input>
{
    Then(p, f)
}

#[derive(Clone)]
pub struct Expected<P>(P, Info<<P::Input as StreamOnce>::Item, <P::Input as StreamOnce>::Range>)
    where P: Parser;
impl<P> Parser for Expected<P>
    where P: Parser
{
    type Input = P::Input;
    type Output = P::Output;

    fn parse_stream(&mut self, input: Self::Input) -> ParseResult<Self::Output, Self::Input> {
        // add_error is only called on unconsumed inputs but we want this expected message to always
        // replace the ones always present in the ParseError
        self.0
            .parse_stream(input)
            .map_err(|errors| {
                errors.map(|mut errors| {
                    errors.set_expected(self.1.clone());
                    errors
                })
            })
    }

    #[inline]
    fn parse_lazy(&mut self, input: Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        self.0.parse_lazy(input)
    }

    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        let start = errors.errors.len();
        self.0.add_error(errors);
        // Replace all expected errors that where added from the previous add_error
        // with this expected error
        let mut i = 0;
        errors.errors.retain(|e| {
            if i < start {
                i += 1;
                true
            } else {
                match *e {
                    Error::Expected(_) => false,
                    _ => true,
                }
            }
        });
        errors.add_error(Error::Expected(self.1.clone()));
    }
}

#[inline(always)]
pub fn expected<P>(p: P,
                   info: Info<<P::Input as StreamOnce>::Item, <P::Input as StreamOnce>::Range>)
                   -> Expected<P>
    where P: Parser
{
    Expected(p, info)
}

#[derive(Clone)]
pub struct AndThen<P, F>(P, F);
impl<P, F, O, E> Parser for AndThen<P, F>
    where P: Parser,
          F: FnMut(P::Output) -> Result<O, E>,
          E: Into<Error<<P::Input as StreamOnce>::Item, <P::Input as StreamOnce>::Range>>
{
    type Input = P::Input;
    type Output = O;
    #[inline]
    fn parse_lazy(&mut self, input: Self::Input) -> ConsumedResult<O, Self::Input> {
        match self.0.parse_lazy(input) {
            EmptyOk((o, input)) => {
                match (self.1)(o) {
                    Ok(o) => EmptyOk((o, input)),
                    Err(err) => EmptyErr(ParseError::new(input.position(), err.into())),
                }
            }
            ConsumedOk((o, input)) => {
                match (self.1)(o) {
                    Ok(o) => ConsumedOk((o, input)),
                    Err(err) => ConsumedErr(ParseError::new(input.position(), err.into())),
                }
            }
            EmptyErr(err) => EmptyErr(err),
            ConsumedErr(err) => ConsumedErr(err),
        }
    }
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors);
    }
}

#[inline(always)]
pub fn and_then<P, F, O, E>(p: P, f: F) -> AndThen<P, F>
    where P: Parser,
          F: FnMut(P::Output) -> Result<O, E>,
          E: Into<Error<<P::Input as StreamOnce>::Item, <P::Input as StreamOnce>::Range>>
{
    AndThen(p, f)
}

macro_rules! tuple_parser {
    ($h: ident, $($id: ident),+) => {
        impl <Input: Stream, $h:, $($id:),+> Parser for ($h, $($id),+)
            where Input: Stream,
                  $h: Parser<Input=Input>,
                  $($id: Parser<Input=Input>),+
        {
            type Input = Input;
            type Output = ($h::Output, $($id::Output),+);
            #[allow(non_snake_case)]
            fn parse_lazy(&mut self,
                          mut input: Input)
                          -> ConsumedResult<($h::Output, $($id::Output),+), Input> {
                let (ref mut $h, $(ref mut $id),+) = *self;
                let mut consumed = false;
                let $h = match $h.parse_lazy(input) {
                    ConsumedOk((x, new_input)) => {
                        consumed = true;
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
                $(
                    let $id = match $id.parse_lazy(input.clone()) {
                        ConsumedOk((x, new_input)) => {
                            consumed = true;
                            input = new_input;
                            x
                        }
                        EmptyErr(mut err) => {
                            if let Ok(t) = input.uncons() {
                                err.add_error(Error::Unexpected(Info::Token(t)));
                            }
                            $id.add_error(&mut err);
                            if consumed {
                                return ConsumedErr(err)
                            } else {
                                return EmptyErr(err)
                            }
                        }
                        ConsumedErr(err) => return ConsumedErr(err),
                        EmptyOk((x, new_input)) => {
                            input = new_input;
                            x
                        }
                    };
                )+
                if consumed {
                    ConsumedOk((($h, $($id),+), input))
                } else {
                    EmptyOk((($h, $($id),+), input))
                }
            }
            fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
                self.0.add_error(errors);
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

#[derive(Copy, Clone)]
pub struct EnvParser<E, I, T>
    where I: Stream
{
    env: E,
    parser: fn(E, I) -> ParseResult<T, I>,
}

impl<E, I, O> Parser for EnvParser<E, I, O>
    where E: Clone,
          I: Stream
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
///     struct Interner(HashMap<String, u32>);
///     impl Interner {
///         fn string<I>(&self, input: I) -> ParseResult<u32, I>
///             where I: Stream<Item=char>
///         {
///             many(letter())
///                 .map(|s: String| self.0.get(&s).cloned().unwrap_or(0))
///                 .parse_stream(input)
///         }
///     }
///
///     let mut map = HashMap::new();
///     map.insert("hello".into(), 1);
///     map.insert("test".into(), 2);
///
///     let env = Interner(map);
///     let mut parser = env_parser(&env, Interner::string);
///
///     let result = parser.parse("hello");
///     assert_eq!(result, Ok((1, "")));
///
///     let result = parser.parse("world");
///     assert_eq!(result, Ok((0, "")));
/// # }
/// ```
#[inline(always)]
pub fn env_parser<E, I, O>(env: E, parser: fn(E, I) -> ParseResult<O, I>) -> EnvParser<E, I, O>
    where E: Clone,
          I: Stream
{
    EnvParser {
        env: env,
        parser: parser,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::{Error, ParseError, Positioner, Parser, State};
    use char::{digit, letter};

    #[test]
    fn choice_empty() {
        let mut parser = choice::<&mut [Token<&str>], Token<&str>>(&mut []);
        let result_err = parser.parse("a");
        assert!(result_err.is_err());
    }
    #[test]
    fn sep_by_consumed_error() {
        let mut parser2 = sep_by((letter(), letter()), token(','));
        let result_err: Result<(Vec<(char, char)>, &str), ParseError<&str>> = parser2.parse("a,bc");
        assert!(result_err.is_err());
    }

    #[test]
    fn tuple() {
        let mut parser = (digit(), token(','), digit(), token(','), letter());
        assert_eq!(parser.parse("1,2,z"), Ok((('1', ',', '2', ',', 'z'), "")));
    }

    /// The expected combinator should retain only errors that are not `Expected`
    #[test]
    fn expected_retain_errors() {
        let mut parser = digit()
            .message("message")
            .expected("N/A")
            .expected("my expected digit");
        assert_eq!(parser.parse(State::new("a")),
                   Err(ParseError {
                       position: <char as Positioner>::start(),
                       errors: vec![Error::Unexpected('a'.into()),
                                    Error::Message("message".into()),
                                    Error::Expected("my expected digit".into())],
                   }));
    }

    #[test]
    fn tuple_parse_error() {
        let mut parser = (digit(), digit());
        let result = parser.parse(State::new("a"));
        assert_eq!(result,
                   Err(ParseError {
                       position: <char as Positioner>::start(),
                       errors: vec![Error::Unexpected('a'.into()), Error::Expected("digit".into())],
                   }));
    }

    #[derive(Clone, PartialEq, Debug)]
    struct CloneOnly {
        s: String,
    }

    #[test]
    fn token_clone_but_not_copy() {
        // Verify we can use token() with a StreamSlice with an item type that is Clone but not
        // Copy.
        let input = &[CloneOnly { s: "x".to_string() }, CloneOnly { s: "y".to_string() }][..];
        let result = token(CloneOnly { s: "x".to_string() }).parse(input);
        assert_eq!(result, Ok((CloneOnly { s: "x".to_string() }, &[CloneOnly { s: "y".to_string() }][..])));
    }
}

use std::iter::FromIterator;
use std::marker::PhantomData;
use primitives::{HasPosition, Info, Parser, ParseResult, ParseError, Stream, StreamOnce, Error, Consumed};
#[cfg(feature = "range_stream")]
use primitives::{RangeStream, Positioner};

macro_rules! impl_parser {
    ($name: ident ($first: ident, $($ty_var: ident),*), $inner_type: ty) => {
    #[derive(Clone)]
    pub struct $name<$first $(,$ty_var)*>($inner_type)
        where $first: Parser $(,$ty_var : Parser<Input=<$first as Parser>::Input>)*;
    impl <$first, $($ty_var),*> Parser for $name<$first $(,$ty_var)*>
        where $first: Parser $(, $ty_var : Parser<Input=<$first as Parser>::Input>)* {
        type Input = <$first as Parser>::Input;
        type Output = <$inner_type as Parser>::Output;
        fn parse_state(&mut self,
                       input: Self::Input) -> ParseResult<Self::Output, Self::Input> {
            self.0.parse_state(input)
        }
        fn parse_lazy(&mut self,
                      input: Self::Input) -> ParseResult<Self::Output, Self::Input> {
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

impl<I> Parser for Any<I> where I: Stream
{
    type Input = I;
    type Output = I::Item;
    fn parse_lazy(&mut self, mut input: I) -> ParseResult<I::Item, I> {
        let position = input.position();
        let x = try!(input.uncons()
             .map_err(|err| Consumed::Empty(ParseError::new(position, err))));
        Ok((x, Consumed::Consumed(input)))
    }
}

///Parses any token
///
/// ```
/// # extern crate combine as pc;
/// # use pc::*;
/// # fn main() {
/// let mut char_parser = any();
/// assert_eq!(char_parser.parse("!").map(|x| x.0), Ok('!'));
/// assert!(char_parser.parse("").is_err());
/// let mut byte_parser = any();
/// assert_eq!(byte_parser.parse(&b"!"[..]).map(|x| x.0), Ok(b'!'));
/// assert!(byte_parser.parse(&b""[..]).is_err());
/// # }
/// ```
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

fn satisfy_impl<I, P, F>(input: I, predicate: &mut P, f: F) -> ParseResult<I::Item, I>
    where I: Stream,
          P: FnMut(I::Item) -> bool,
          F: FnOnce(I::Position, I::Item) -> ParseError<I>
{
    let mut next = input.clone();
    match next.uncons() {
        Ok(c) => {
            if (predicate)(c.clone()) {
                Ok((c, Consumed::Consumed(next)))
            } else {
                Err(Consumed::Empty(f(input.position(), c)))
            }
        }
        Err(err) => Err(Consumed::Empty(ParseError::new(input.position(), err))),
    }
}

impl<I, P> Parser for Satisfy<I, P>
    where I: Stream,
          P: FnMut(I::Item) -> bool
{
    type Input = I;
    type Output = I::Item;
    fn parse_lazy(&mut self, input: I) -> ParseResult<I::Item, I> {
        satisfy_impl(input, &mut self.predicate, |pos, _| ParseError::empty(pos))
    }
}

///Parses a token and succeeds depending on the result of `predicate`
///
/// ```
/// # extern crate combine as pc;
/// # use pc::*;
/// # fn main() {
/// let mut parser = satisfy(|c| c == '!' || c == '?');
/// assert_eq!(parser.parse("!").map(|x| x.0), Ok('!'));
/// assert_eq!(parser.parse("?").map(|x| x.0), Ok('?'));
/// # }
/// ```
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
    fn parse_lazy(&mut self, input: I) -> ParseResult<I::Item, I> {
        satisfy_impl(input, &mut |c| c == self.c, |pos, _| ParseError::empty(pos))
    }
    fn add_error(&mut self, error: &mut ParseError<Self::Input>) {
        error.errors.push(Error::Expected(Info::Token(self.c.clone())));
    }
}

///Parses a character and succeeds if the character is equal to `c`
///
/// ```
/// # extern crate combine as pc;
/// # use pc::*;
/// # fn main() {
/// let result = token('!')
///     .parse("!")
///     .map(|x| x.0);
/// assert_eq!(result, Ok('!'));
/// # }
/// ```
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
pub struct Choice<S, P>(S, PhantomData<P>);

impl<I, O, S, P> Parser for Choice<S, P>
    where I: Stream,
          S: AsMut<[P]>,
          P: Parser<Input = I, Output = O>
{
    type Input = I;
    type Output = O;
    fn parse_lazy(&mut self, input: I) -> ParseResult<O, I> {
        let mut empty_err = None;
        for p in AsMut::as_mut(&mut self.0) {
            match p.parse_lazy(input.clone()) {
                consumed_err@Err(Consumed::Consumed(_)) => return consumed_err,
                Err(Consumed::Empty(err)) => {
                    empty_err = match empty_err {
                        None => Some(err),
                        Some(prev_err) => Some(prev_err.merge(err)),
                    };
                }
                ok@Ok(_) => return ok,
            }
        }
        Err(Consumed::Empty(match empty_err {
            None => {
                ParseError::new(input.position(),
                                Error::Message("parser choice is empty".into()))
            }
            Some(err) => err,
        }))
    }
    fn add_error(&mut self, error: &mut ParseError<Self::Input>) {
        for p in self.0.as_mut() {
            p.add_error(error);
        }
    }
}

/// Takes an array of parsers and tries to apply them each in order.
/// Fails if all parsers fails or if an applied parser consumes input before failing.
///
/// ```
/// # extern crate combine as pc;
/// # use pc::*;
/// # use pc::primitives::Error;
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
pub fn choice<S, P>(ps: S) -> Choice<S, P>
    where S: AsMut<[P]>,
          P: Parser
{
    Choice(ps, PhantomData)
}

#[derive(Clone)]
pub struct Unexpected<I>(Info<I::Item, I::Range>, PhantomData<fn(I) -> I>) where I: Stream;
impl<I> Parser for Unexpected<I> where I: Stream
{
    type Input = I;
    type Output = ();
    fn parse_lazy(&mut self, input: I) -> ParseResult<(), I> {
        Err(Consumed::Empty(ParseError::empty(input.position())))
    }
    fn add_error(&mut self, error: &mut ParseError<Self::Input>) {
        error.errors.push(Error::Unexpected(self.0.clone()));
    }
}
///Always fails with `message` as an unexpected error.
///Never consumes any input.
///
/// ```
/// # extern crate combine as pc;
/// # use pc::*;
/// # use pc::primitives::Error;
/// # fn main() {
/// let result = unexpected("token")
///     .parse("a");
/// assert!(result.is_err());
/// assert!(result.err().unwrap().errors.iter().any(|m| *m == Error::Unexpected("token".into())));
/// # }
/// ```
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
    fn parse_lazy(&mut self, input: I) -> ParseResult<T, I> {
        Ok((self.0.clone(), Consumed::Empty(input)))
    }
}
///Always returns the value `v` without consuming any input.
///
/// ```
/// # extern crate combine as pc;
/// # use pc::*;
/// # fn main() {
/// let result = value(42)
///     .parse("hello world")
///     .map(|x| x.0);
/// assert_eq!(result, Ok(42));
/// # }
/// ```
pub fn value<I, T>(v: T) -> Value<I, T>
    where I: Stream,
          T: Clone
{
    Value(v, PhantomData)
}

impl_parser! { NotFollowedBy(P,),
               Or<Then<Try<P>, fn(P::Output) -> Unexpected<P::Input>>, Value<P::Input, ()>>
}

///Succeeds only if `parser` fails.
///Never consumes any input.
///
/// ```
/// # extern crate combine as pc;
/// # use pc::*;
/// # fn main() {
/// let result = string("let")
///     .skip(not_followed_by(alpha_num()))
///     .parse("letx")
///     .map(|x| x.0);
/// assert!(result.is_err());
/// # }
/// ```
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

pub struct Iter<P: Parser> {
    parser: P,
    input: Consumed<P::Input>,
    error: Option<Consumed<ParseError<P::Input>>>,
}

impl<P: Parser> Iter<P> {
    fn new(parser: P, input: P::Input) -> Iter<P> {
        Iter {
            parser: parser,
            input: Consumed::Empty(input),
            error: None,
        }
    }
    ///Converts the iterator to a `ParseResult`, returning `Ok` if the parsing so far has be done
    ///without any errors which consumed data.
    pub fn into_result<O>(self, value: O) -> ParseResult<O, P::Input> {
        match self.error {
            Some(err@Consumed::Consumed(_)) => Err(err),
            _ => Ok((value, self.input)),
        }
    }
}

impl<P: Parser> Iterator for Iter<P> {
    type Item = P::Output;
    fn next(&mut self) -> Option<P::Output> {
        if self.error.is_some() {
            return None;
        }
        match self.parser.parse_lazy(self.input.clone().into_inner()) {
            Ok((value, rest)) => {
                self.input = self.input.merge(rest);
                Some(value)
            }
            Err(err) => {
                self.error = Some(err);
                None
            }
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
    fn parse_state(&mut self, input: P::Input) -> ParseResult<F, P::Input> {
        let mut iter = (&mut self.0).iter(input);
        let result = iter.by_ref().collect();
        iter.into_result(result)
    }
}

///Parses `p` zero or more times returning a collection with the values from `p`.
///If the returned collection cannot be inferred type annotations must be supplied, either by
///annotating the resulting type binding `let collection: Vec<_> = ...` or by specializing when
///calling many, `many::<Vec<_>, _>(...)`
///
/// ```
/// # extern crate combine as pc;
/// # use pc::*;
/// # fn main() {
/// let result = many(digit())
///     .parse("123A")
///     .map(|x| x.0);
/// assert_eq!(result, Ok(vec!['1', '2', '3']));
/// # }
/// ```
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
    fn parse_lazy(&mut self, input: P::Input) -> ParseResult<F, P::Input> {
        let (first, input) = try!(self.0.parse_lazy(input));
        input.combine(move |input| {
            let mut iter = Iter::new(&mut self.0, input);
            let result = Some(first)
                             .into_iter()
                             .chain(iter.by_ref())
                             .collect();
            iter.into_result(result)
        })
    }
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors)
    }
}

impl_parser!{ SkipMany(P,), Map<Many<Vec<()>, Map<P, fn (P::Output)>>, fn (Vec<()>)> }
///Parses `p` zero or more times ignoring the result
///
/// ```
/// # extern crate combine as pc;
/// # use pc::*;
/// # fn main() {
/// let result = skip_many(digit())
///     .parse("A");
/// assert_eq!(result, Ok(((), "A")));
/// # }
/// ```
pub fn skip_many<P>(p: P) -> SkipMany<P>
    where P: Parser
{
    fn ignore<T>(_: T) {}
    let ignore1: fn(P::Output) = ignore;
    let ignore2: fn(Vec<()>) = ignore;
    SkipMany(many(p.map(ignore1)).map(ignore2))
}

impl_parser!{ SkipMany1(P,), Map<Many1<Vec<()>, Map<P, fn (P::Output)>>, fn (Vec<()>)> }
///Parses `p` one or more times ignoring the result
///
/// ```
/// # extern crate combine as pc;
/// # use pc::*;
/// # fn main() {
/// let result = skip_many1(digit())
///     .parse("123A");
/// assert_eq!(result, Ok(((), "A")));
/// # }
/// ```
pub fn skip_many1<P>(p: P) -> SkipMany1<P>
    where P: Parser
{
    fn ignore<T>(_: T) {}
    let ignore1: fn(P::Output) = ignore;
    let ignore2: fn(Vec<()>) = ignore;
    SkipMany1(many1(p.map(ignore1)).map(ignore2))
}

///Parses `p` one or more times returning a collection with the values from `p`.
///If the returned collection cannot be inferred type annotations must be supplied, either by
///annotating the resulting type binding `let collection: Vec<_> = ...` or by specializing when
///calling many1 `many1::<Vec<_>, _>(...)`
///
///
/// ```
/// # extern crate combine as pc;
/// # use pc::*;
/// # fn main() {
/// let result = many1::<Vec<_>, _>(digit())
///     .parse("A123");
/// assert!(result.is_err());
/// # }
/// ```
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

    fn parse_lazy(&mut self, input: P::Input) -> ParseResult<F, P::Input> {
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
/// # extern crate combine as pc;
/// # use pc::*;
/// # fn main() {
/// let mut parser = sep_by(digit(), token(','));
/// let result_ok = parser.parse("1,2,3");
/// assert_eq!(result_ok, Ok((vec!['1', '2', '3'], "")));
/// let result_ok2 = parser.parse("");
/// assert_eq!(result_ok2, Ok((vec![], "")));
/// # }
/// ```
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

    fn parse_lazy(&mut self, input: P::Input) -> ParseResult<F, P::Input> {
        let (first, rest) = try!(self.parser.parse_lazy(input.clone()));

        rest.combine(move |input| {
            let rest = (&mut self.separator).with(&mut self.parser);
            let mut iter = Iter::new(rest, input);
            let result = Some(first)
                             .into_iter()
                             .chain(iter.by_ref())
                             .collect();
            iter.into_result(result)
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

    fn parse_lazy(&mut self, input: P::Input) -> ParseResult<F, P::Input> {
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
/// # fn main() {
/// let mut parser = sep_end_by(digit(), token(';'));
/// let result_ok = parser.parse("1;2;3;");
/// assert_eq!(result_ok, Ok((vec!['1', '2', '3'], "")));
/// let result_ok2 = parser.parse("1;2;3");
/// assert_eq!(result_ok2, Ok((vec!['1', '2', '3'], "")));
/// # }
/// ```
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

    fn parse_lazy(&mut self, input: P::Input) -> ParseResult<F, P::Input> {
        let (first, input) = try!(self.parser.parse_lazy(input.clone()));

        input.combine(|input| {
            let rest = (&mut self.separator).with(optional(&mut self.parser));
            let mut iter = Iter::new(rest, input);
            // `iter` yields Option<P::Output>, by using flat map we make sure that we stop
            // iterating once a None element is received, i.e `self.parser` did not parse
            // successfully
            let result = Some(first)
                             .into_iter()
                             .chain(iter.by_ref().flat_map(|x| x))
                             .collect();
            iter.into_result(result)
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
/// # use combine::{digit, token, sep_end_by1, Parser};
/// # use combine::primitives::{Error, ParseError, Positioner, State};
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
    fn parse_state(&mut self, input: I) -> ParseResult<O, I> {
        self(input)
    }
}
#[derive(Clone)]
pub struct FnParser<I, F>(F, PhantomData<fn(I) -> I>);

///Wraps a function, turning it into a parser
///Mainly needed to turn closures into parsers as function types can be casted to function pointers
///to make them usable as a parser
///
/// ```
/// extern crate combine;
/// use combine::*;
/// use combine::primitives::{Consumed, Error, Stream, HasPosition};
/// # fn main() {
/// let mut even_digit = parser(|input| {
///     // Force input to be a &str
///     let _: &str = input;
///     let position = input.position();
///     let (char_digit, input) = try!(digit().parse_state(input));
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
    fn parse_state(&mut self, input: I) -> ParseResult<O, I> {
        (self.0)(input)
    }
}

impl<I, O> Parser for fn(I) -> ParseResult<O, I> where I: Stream
{
    type Input = I;
    type Output = O;
    fn parse_state(&mut self, input: I) -> ParseResult<O, I> {
        self(input)
    }
}

#[derive(Clone)]
pub struct Optional<P>(P);
impl<P> Parser for Optional<P> where P: Parser
{
    type Input = P::Input;
    type Output = Option<P::Output>;
    fn parse_lazy(&mut self, input: P::Input) -> ParseResult<Option<P::Output>, P::Input> {
        match self.0.parse_state(input.clone()) {
            Ok((x, rest)) => Ok((Some(x), rest)),
            Err(err@Consumed::Consumed(_)) => return Err(err),
            Err(Consumed::Empty(_)) => Ok((None, Consumed::Empty(input))),
        }
    }
}

///Returns `Some(value)` and `None` on parse failure (always succeeds)
///
/// ```
/// # extern crate combine as pc;
/// # use pc::*;
/// # fn main() {
/// let mut parser = optional(digit());
/// let result1 = parser.parse("a");
/// assert_eq!(result1, Ok((None, "a")));
/// let result2 = parser.parse("1");
/// assert_eq!(result2, Ok((Some('1'), "")));
/// # }
/// ```
pub fn optional<P>(parser: P) -> Optional<P>
    where P: Parser
{
    Optional(parser)
}

impl_parser! { Between(L, R, P), Skip<With<L, P>, R> }
///Parses `open` followed by `parser` followed by `close`
///Returns the value of `parser`
///
/// ```
/// # extern crate combine as pc;
/// # use pc::*;
/// # fn main() {
/// let result = between(token('['), token(']'), string("rust"))
///     .parse("[rust]")
///     .map(|x| x.0);
/// assert_eq!(result, Ok("rust"));
/// # }
/// ```
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

    fn parse_lazy(&mut self, input: I) -> ParseResult<P::Output, I> {
        let (mut l, mut input) = try!(self.0.parse_lazy(input));
        loop {
            match (&mut self.1, &mut self.0).parse_lazy(input.clone().into_inner()) {
                Ok(((op, r), rest)) => {
                    l = op(l, r);
                    input = input.merge(rest);
                }
                Err(err@Consumed::Consumed(_)) => return Err(err),
                Err(Consumed::Empty(_)) => break,
            }
        }
        Ok((l, input))
    }

    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors)
    }
}

///Parses `p` 1 or more times separated by `op`
///The value returned is the one produced by the left associative application of `op`
///
/// ```
/// # extern crate combine as pc;
/// # use pc::*;
/// # fn main() {
/// let number = digit().map(|c: char| c.to_digit(10).unwrap());
/// let sub = token('-').map(|_| |l: u32, r: u32| l - r);
/// let mut parser = chainl1(number, sub);
///     assert_eq!(parser.parse("9-3-5"), Ok((1, "")));
/// }
/// ```
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
    fn parse_lazy(&mut self, input: I) -> ParseResult<P::Output, I> {
        let (mut l, mut input) = try!(self.0.parse_lazy(input));
        loop {
            let op = match self.1.parse_lazy(input.clone().into_inner()) {
                Ok((x, rest)) => {
                    input = input.merge(rest);
                    x
                }
                Err(err@Consumed::Consumed(_)) => return Err(err),
                Err(Consumed::Empty(_)) => break,
            };
            match self.parse_lazy(input.clone().into_inner()) {
                Ok((r, rest)) => {
                    l = op(l, r);
                    input = input.merge(rest);
                }
                Err(err@Consumed::Consumed(_)) => return Err(err),
                Err(Consumed::Empty(_)) => break,
            }
        }
        Ok((l, input))
    }
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors)
    }
}

///Parses `p` one or more times separated by `op`
///The value returned is the one produced by the right associative application of `op`
///
/// ```
/// # extern crate combine as pc;
/// # use pc::*;
/// # fn main() {
/// let number = digit().map(|c: char| c.to_digit(10).unwrap());
/// let pow = token('^').map(|_| |l: u32, r: u32| l.pow(r));
/// let mut parser = chainr1(number, pow);
///     assert_eq!(parser.parse("2^3^2"), Ok((512, "")));
/// }
/// ```
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
    fn parse_lazy(&mut self, input: I) -> ParseResult<O, I> {
        self.0
            .parse_state(input)
            .map_err(Consumed::as_empty)
    }
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors)
    }
}

///Try acts as `p` except it acts as if the parser hadn't consumed any input
///if `p` returns an error after consuming input
///
/// ```
/// # extern crate combine as pc;
/// # use pc::*;
/// # fn main() {
/// let mut p = try(string("let"))
///     .or(string("lex"));
/// let result = p.parse("lex").map(|x| x.0);
/// assert_eq!(result, Ok("lex"));
/// let result = p.parse("aet").map(|x| x.0);
/// assert!(result.is_err());
/// # }
/// ```
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

    fn parse_lazy(&mut self, input: I) -> ParseResult<O, I> {
        self.0.parse_lazy(input.clone()).map(|(o, _input)| (o, Consumed::Empty(input)))
    }

    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors);
    }
}

///look_ahead acts as p but doesn't consume input on success.
///
/// ```
/// # extern crate combine as pc;
/// # use pc::*;
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
pub fn look_ahead<P>(p: P) -> LookAhead<P>
    where P: Parser
{
    LookAhead(p)
}

#[derive(Clone)]
pub struct And<P1, P2>(P1, P2);
impl<I, P1, P2> Parser for And<P1, P2>
    where I: Stream,
          P1: Parser<Input = I>,
          P2: Parser<Input = I>
{
    type Input = I;
    type Output = (P1::Output, P2::Output);
    fn parse_lazy(&mut self, input: I) -> ParseResult<(P1::Output, P2::Output), I> {
        let (a, rest) = try!(self.0.parse_lazy(input));
        rest.combine(move |rest| {
            let (b, rest) = try!(self.1.parse_state(rest));
            Ok(((a, b), rest))
        })
    }
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors)
    }
}

#[derive(Clone)]
pub struct With<P1, P2>(P1, P2)
    where P1: Parser,
          P2: Parser;
impl<I, P1, P2> Parser for With<P1, P2>
    where I: Stream,
          P1: Parser<Input = I>,
          P2: Parser<Input = I>
{
    type Input = I;
    type Output = P2::Output;
    fn parse_lazy(&mut self, input: I) -> ParseResult<Self::Output, I> {
        let ((_, b), rest) = try!((&mut self.0).and(&mut self.1).parse_lazy(input));
        Ok((b, rest))
    }
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors)
    }
}

#[derive(Clone)]
pub struct Skip<P1, P2>(P1, P2)
    where P1: Parser,
          P2: Parser;
impl<I, P1, P2> Parser for Skip<P1, P2>
    where I: Stream,
          P1: Parser<Input = I>,
          P2: Parser<Input = I>
{
    type Input = I;
    type Output = P1::Output;
    fn parse_lazy(&mut self, input: I) -> ParseResult<Self::Output, I> {
        let ((a, _), rest) = try!((&mut self.0).and(&mut self.1).parse_lazy(input));
        Ok((a, rest))
    }
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors)
    }
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

    fn parse_state(&mut self, input: I) -> ParseResult<Self::Output, I> {
        // The message should always be added even if some input was consumed before failing
        self.0
            .parse_state(input.clone())
            .map_err(|errors| {
                errors.map(|mut errors| {
                    errors.add_message(self.1.clone());
                    errors
                })
            })
    }

    fn parse_lazy(&mut self, input: I) -> ParseResult<Self::Output, I> {
        self.0.parse_lazy(input.clone())
    }

    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors);
        errors.add_message(self.1.clone());
    }
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
    fn parse_lazy(&mut self, input: I) -> ParseResult<O, I> {
        match self.0.parse_lazy(input.clone()) {
            Ok(x) => Ok(x),
            Err(err@Consumed::Consumed(_)) => Err(err),
            Err(Consumed::Empty(error1)) => {
                match self.1.parse_lazy(input) {
                    Ok(x) => Ok(x),
                    Err(err@Consumed::Consumed(_)) => Err(err),
                    Err(Consumed::Empty(error2)) => Err(Consumed::Empty(error1.merge(error2))),
                }
            }
        }
    }
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors);
        self.1.add_error(errors);
    }
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
    fn parse_lazy(&mut self, input: I) -> ParseResult<B, I> {
        match self.0.parse_lazy(input) {
            Ok((x, input)) => Ok(((self.1)(x), input)),
            Err(err) => Err(err),
        }
    }
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors);
    }
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
    fn parse_lazy(&mut self, input: Self::Input) -> ParseResult<Self::Output, Self::Input> {
        let (value, input) = try!(self.0.parse_lazy(input));
        input.combine(move |input| {
            let mut next = (self.1)(value);
            next.parse_state(input)
        })
    }
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors);
    }
}

#[derive(Clone)]
pub struct Expected<P>(P, Info<<P::Input as StreamOnce>::Item, <P::Input as StreamOnce>::Range>)
    where P: Parser;
impl<P> Parser for Expected<P> where P: Parser
{
    type Input = P::Input;
    type Output = P::Output;

    fn parse_state(&mut self, input: Self::Input) -> ParseResult<Self::Output, Self::Input> {
        // add_error is only called on unconsumed inputs but we want this expected message to always
        // replace the ones always present in the ParseError
        self.0
            .parse_state(input)
            .map_err(|errors| {
                errors.map(|mut errors| {
                    errors.set_expected(self.1.clone());
                    errors
                })
            })
    }

    fn parse_lazy(&mut self, input: Self::Input) -> ParseResult<Self::Output, Self::Input> {
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

#[derive(Clone)]
pub struct AndThen<P, F>(P, F);
impl<P, F, O, E> Parser for AndThen<P, F>
    where P: Parser,
          F: FnMut(P::Output) -> Result<O, E>,
          E: Into<Error<<P::Input as StreamOnce>::Item, <P::Input as StreamOnce>::Range>>
{
    type Input = P::Input;
    type Output = O;
    fn parse_lazy(&mut self, input: Self::Input) -> ParseResult<O, Self::Input> {
        self.0
            .parse_lazy(input)
            .and_then(|(o, input)| {
                match (self.1)(o) {
                    Ok(o) => Ok((o, input)),
                    Err(err) => {
                        Err(input.map(move |input| ParseError::new(input.position(), err.into())))
                    }
                }
            })
    }
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        self.0.add_error(errors);
    }
}

///Extension trait which provides functions that are more conveniently used through method calls
pub trait ParserExt : Parser + Sized {

    ///Discards the value of the `self` parser and returns the value of `p`
    ///Fails if any of the parsers fails
    ///
    /// ```
    /// # extern crate combine as pc;
    /// # use pc::*;
    /// # fn main() {
    /// let result = digit()
    ///     .with(token('i'))
    ///     .parse("9i")
    ///     .map(|x| x.0);
    /// assert_eq!(result, Ok('i'));
    /// # }
    /// ```
    fn with<P2>(self, p: P2) -> With<Self, P2>
        where P2: Parser<Input = Self::Input>
    {
        With(self, p)
    }

    ///Discards the value of the `p` parser and returns the value of `self`
    ///Fails if any of the parsers fails
    ///
    /// ```
    /// # extern crate combine as pc;
    /// # use pc::*;
    /// # fn main() {
    /// let result = digit()
    ///     .skip(token('i'))
    ///     .parse("9i")
    ///     .map(|x| x.0);
    /// assert_eq!(result, Ok('9'));
    /// # }
    /// ```
    fn skip<P2>(self, p: P2) -> Skip<Self, P2>
        where P2: Parser<Input = Self::Input>
    {
        Skip(self, p)
    }

    ///Parses with `self` followed by `p`
    ///Succeeds if both parsers succeed, otherwise fails
    ///Returns a tuple with both values on success
    ///
    /// ```
    /// # extern crate combine as pc;
    /// # use pc::*;
    /// # fn main() {
    /// let result = digit()
    ///     .and(token('i'))
    ///     .parse("9i")
    ///     .map(|x| x.0);
    /// assert_eq!(result, Ok(('9', 'i')));
    /// # }
    /// ```
    fn and<P2>(self, p: P2) -> And<Self, P2>
        where P2: Parser<Input = Self::Input>
    {
        And(self, p)
    }

    /// Returns a parser which attempts to parse using `self`. If `self` fails without consuming any
    /// input it tries to consume the same input using `p`.
    ///
    /// ```
    /// # extern crate combine as pc;
    /// # use pc::*;
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
    /// // Use 'try' to make failing parsers always act as if they have not consumed any input
    /// let mut parser3 = try(string("two")).or(try(string("three")));
    /// assert_eq!(parser3.parse("three"), Ok(("three", "")));
    /// # }
    /// ```
    fn or<P2>(self, p: P2) -> Or<Self, P2>
        where P2: Parser<Input = Self::Input>
    {
        Or(self, p)
    }

    ///Parses using `self` and then passes the value to `f` which returns a parser used to parse
    ///the rest of the input
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::primitives::{Consumed, Error, Stream, HasPosition};
    /// # fn main() {
    /// let result = digit()
    ///     .then(|d| parser(move |input| {
    ///             // Force input to be a &str
    ///             let _: &str = input;
    ///         if d == '9' {
    ///             Ok((9, Consumed::Empty(input)))
    ///         }
    ///         else {
    ///             let position = input.position();
    ///             let err = ParseError::new(position, Error::Message("Not a nine".into()));
    ///             Err((Consumed::Empty(err)))
    ///         }
    ///     }))
    ///     .parse("9");
    /// assert_eq!(result, Ok((9, "")));
    /// # }
    /// ```
    fn then<N, F>(self, f: F) -> Then<Self, F>
        where F: FnMut(Self::Output) -> N,
              N: Parser<Input = Self::Input>
    {
        Then(self, f)
    }

    ///Uses `f` to map over the parsed value
    ///
    /// ```
    /// # extern crate combine as pc;
    /// # use pc::*;
    /// # fn main() {
    /// let result = digit()
    ///     .map(|c| c == '9')
    ///     .parse("9")
    ///     .map(|x| x.0);
    /// assert_eq!(result, Ok(true));
    /// # }
    /// ```
    fn map<F, B>(self, f: F) -> Map<Self, F>
        where F: FnMut(Self::Output) -> B
    {
        Map(self, f)
    }

    ///Parses with `self` and if it fails, adds the message `msg` to the error
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::primitives::{Error, Positioner};
    /// # fn main() {
    /// let result = token('9')
    ///     .message("Not a nine")
    ///     .parse(State::new("8"));
    /// assert_eq!(result, Err(ParseError {
    ///     position: <char as Positioner>::start(),
    ///     errors: vec![
    ///         Error::Unexpected('8'.into()),
    ///         Error::Expected('9'.into()),
    ///         Error::Message("Not a nine".into())
    ///     ]
    /// }));
    /// # }
    /// ```
    fn message<S>(self, msg: S) -> Message<Self>
        where S: Into<Info<<Self::Input as StreamOnce>::Item, <Self::Input as StreamOnce>::Range>>
    {
        Message(self, msg.into())
    }

    /// Parses with `self` and if it fails without consuming any input any expected errors are
    /// replaced by `msg`. `msg` is then used in error messages as "Expected `msg`".
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::*;
    /// # use combine::primitives::{Error, Positioner};
    /// # fn main() {
    /// let result = token('9')
    ///     .expected("nine")
    ///     .parse(State::new("8"));
    /// assert_eq!(result, Err(ParseError {
    ///     position: <char as Positioner>::start(),
    ///     errors: vec![Error::Unexpected('8'.into()), Error::Expected("nine".into())]
    /// }));
    /// # }
    /// ```
    fn expected<S>(self, msg: S) -> Expected<Self>
        where S: Into<Info<<Self::Input as StreamOnce>::Item, <Self::Input as StreamOnce>::Range>>
    {
        Expected(self, msg.into())
    }

    ///Parses with `self` and applies `f` on the result if `self` parses successfully
    ///`f` may optionally fail with an error which is automatically converted to a `ParseError`
    ///
    /// ```
    /// # extern crate combine as pc;
    /// # use pc::*;
    /// # fn main() {
    /// let mut parser = many1(digit())
    ///     .and_then(|s: String| s.parse::<i32>());
    /// let result = parser.parse("1234");
    /// assert_eq!(result, Ok((1234, "")));
    /// let err = parser.parse("abc");
    /// assert!(err.is_err());
    /// # }
    /// ```
    fn and_then<F, O, E>(self, f: F) -> AndThen<Self, F>
        where F: FnMut(Self::Output) -> Result<O, E>,
              E: Into<Error<<Self::Input as StreamOnce>::Item, <Self::Input as StreamOnce>::Range>>
    {
        AndThen(self, f)
    }

    /// Creates an iterator from a parser and a state. Can be used as an alternative to `many` when
    /// collecting directly into a `FromIterator` type is not desirable
    ///
    /// ```
    /// # extern crate combine as pc;
    /// # use pc::*;
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
    fn iter(self, input: Self::Input) -> Iter<Self> {
        Iter::new(self, input)
    }
}

impl<P: Parser> ParserExt for P {}

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
                          input: Input)
                          -> ParseResult<($h::Output, $($id::Output),+), Input> {
                let (ref mut $h, $(ref mut $id),+) = *self;
                let ($h, input) = try!($h.parse_lazy(input));
                $(let ($id, input) = try!(input.combine(|input| $id.parse_state(input)));)+
                Ok((($h, $($id),+), input))
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

    fn parse_lazy(&mut self, input: I) -> ParseResult<O, I> {
        (self.parser)(self.env.clone(), input)
    }
}

/// Constructs a parser out of an environment and a function which needs the given environment to
/// do the parsing. This is commonly useful to allow multiple parsers to share some environment
/// while still allowing the parsers to be written in separate functions.
///
/// ```
/// # extern crate combine as pc;
/// # use std::collections::HashMap;
/// # use pc::primitives::Stream;
/// # use pc::*;
/// # fn main() {
///     struct Interner(HashMap<String, u32>);
///     impl Interner {
///         fn string<I>(&self, input: I) -> ParseResult<u32, I>
///             where I: Stream<Item=char>
///         {
///             many(letter())
///                 .map(|s: String| self.0.get(&s).cloned().unwrap_or(0))
///                 .parse_state(input)
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
pub fn env_parser<E, I, O>(env: E, parser: fn(E, I) -> ParseResult<O, I>) -> EnvParser<E, I, O>
    where E: Clone,
          I: Stream
{
    EnvParser {
        env: env,
        parser: parser,
    }
}

#[cfg(feature = "range_stream")]
pub struct Range<I>(I::Range) where I: RangeStream;
#[cfg(feature = "range_stream")]
impl<I, E> Parser for Range<I>
    where I: RangeStream<Item = E>,
          I::Range: Positioner<Position = E::Position> + PartialEq + ::primitives::Range,
          E: Positioner + Clone
{
    type Input = I;
    type Output = I::Range;

    fn parse_lazy(&mut self, mut input: Self::Input) -> ParseResult<Self::Output, Self::Input> {
        use primitives::Range;
        let position = input.position();
        match input.uncons_range(self.0.len()) {
            Ok(other) => {
                if other == self.0 {
                    Ok((other, Consumed::Consumed(input)))
                } else {
                    Err(Consumed::Empty(ParseError::empty(position)))
                }
            }
            Err(err) => Err(Consumed::Empty(ParseError::new(position, err))),
        }
    }
    fn add_error(&mut self, errors: &mut ParseError<Self::Input>) {
        // TODO Add unexpected message?
        errors.add_error(Error::Expected(Info::Range(self.0.clone())));
    }
}

/// ```
/// # extern crate combine as pc;
/// # use pc::combinator::range;
/// # use pc::*;
/// # fn main() {
/// let mut parser = range("hello");
/// let result = parser.parse("hello world");
/// assert_eq!(result, Ok(("hello", " world")));
/// let result = parser.parse("hel world");
/// assert!(result.is_err());
/// # }
/// ```
#[cfg(feature = "range_stream")]
pub fn range<I, E>(i: I::Range) -> Range<I>
    where I: RangeStream<Item = E>,
          I::Range: Positioner<Position = E::Position> + PartialEq + ::primitives::Range,
          E: Positioner + Clone
{
    Range(i)
}

#[cfg(feature = "range_stream")]
pub struct Take<I>(usize, PhantomData<fn(I) -> I>);
#[cfg(feature = "range_stream")]
impl<I, E> Parser for Take<I>
    where I: RangeStream<Item = E>,
          I::Range: ::primitives::Range + Positioner<Position = E::Position>,
          E: Positioner + Clone
{
    type Input = I;
    type Output = I::Range;

    fn parse_lazy(&mut self, mut input: Self::Input) -> ParseResult<Self::Output, Self::Input> {
        let position = input.position();
        let x = try!(input.uncons_range(self.0)
             .map_err(|err| Consumed::Empty(ParseError::new(position, err))));
        Ok((x, Consumed::Consumed(input)))
    }
}

/// ```
/// # extern crate combine as pc;
/// # use pc::combinator::take;
/// # use pc::*;
/// # fn main() {
/// let mut parser = take(4);
/// let result = parser.parse("123abc");
/// assert_eq!(result, Ok(("123a", "bc")));
/// let result = parser.parse("abc");
/// assert!(result.is_err());
/// # }
/// ```
#[cfg(feature = "range_stream")]
pub fn take<I>(n: usize) -> Take<I>
    where I: RangeStream,
          I::Range: ::primitives::Range
{
    Take(n, PhantomData)
}

#[cfg(feature = "range_stream")]
pub struct TakeWhile<I, F>(F, PhantomData<fn(I) -> I>);
#[cfg(feature = "range_stream")]
impl<I, E, F> Parser for TakeWhile<I, F>
    where I: RangeStream<Item = E>,
          I::Range: ::primitives::Range + Positioner<Position = E::Position>,
          E: Positioner + Clone,
          F: FnMut(I::Item) -> bool
{
    type Input = I;
    type Output = I::Range;

    fn parse_lazy(&mut self, input: Self::Input) -> ParseResult<Self::Output, Self::Input> {
        ::primitives::uncons_while(input, &mut self.0)
    }
}

/// ```
/// # extern crate combine as pc;
/// # use pc::combinator::take_while;
/// # use pc::*;
/// # fn main() {
/// let mut parser = take_while(|c: char| c.is_digit(10));
/// let result = parser.parse("123abc");
/// assert_eq!(result, Ok(("123", "abc")));
/// let result = parser.parse("abc");
/// assert_eq!(result, Ok(("", "abc")));
/// # }
/// ```
#[cfg(feature = "range_stream")]
pub fn take_while<I, F>(f: F) -> TakeWhile<I, F>
    where I: RangeStream,
          F: FnMut(I::Item) -> bool
{
    TakeWhile(f, PhantomData)
}

#[cfg(feature = "range_stream")]
pub struct TakeWhile1<I, F>(F, PhantomData<fn(I) -> I>);
#[cfg(feature = "range_stream")]
impl<I, F> Parser for TakeWhile1<I, F>
    where I: RangeStream,
          I::Range: ::primitives::Range,
          F: FnMut(I::Item) -> bool
{
    type Input = I;
    type Output = I::Range;

    fn parse_lazy(&mut self, input: Self::Input) -> ParseResult<Self::Output, Self::Input> {
        ::primitives::uncons_while(input, &mut self.0).and_then(|(v, input)| {
            match input {
                Consumed::Consumed(_) => Ok((v, input)),
                Consumed::Empty(mut input) => {
                    let position = input.position();
                    let error = match input.uncons() {
                        Ok(t) => Error::Unexpected(Info::Token(t)),
                        Err(err) => err,
                    };
                    Err(Consumed::Empty(ParseError::new(position, error)))
                }
            }
        })
    }
}


/// ```
/// # extern crate combine as pc;
/// # use pc::combinator::take_while1;
/// # use pc::*;
/// # fn main() {
/// let mut parser = take_while1(|c: char| c.is_digit(10));
/// let result = parser.parse("123abc");
/// assert_eq!(result, Ok(("123", "abc")));
/// let result = parser.parse("abc");
/// assert!(result.is_err());
/// # }
/// ```
#[cfg(feature = "range_stream")]
pub fn take_while1<I, F>(f: F) -> TakeWhile1<I, F>
    where I: RangeStream,
          I::Range: ::primitives::Range,
          F: FnMut(I::Item) -> bool
{
    TakeWhile1(f, PhantomData)
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

    ///The expected combinator should retain only errors that are not `Expected`
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

    #[cfg(feature = "range_stream")]
    #[test]
    fn take_while_test() {
        let result = take_while(|c: char| c.is_digit(10)).parse("123abc");
        assert_eq!(result, Ok(("123", "abc")));
    }

    #[cfg(feature = "range_stream")]
    #[test]
    fn range_string_no_char_boundary_error() {
        let mut parser = range("hello");
        let result = parser.parse("hell\u{00EE} world");
        assert!(result.is_err());
    }
}

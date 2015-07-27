use std::iter::FromIterator;
use std::marker::PhantomData;
use primitives::{Info, Parser, ParseResult, ParseError, Positioner, Stream, State, Error, Consumed};

macro_rules! impl_parser {
    ($name: ident ($first: ident, $($ty_var: ident),*), $inner_type: ty) => {
    #[derive(Clone)]
    pub struct $name<$first $(,$ty_var)*>($inner_type)
        where $first: Parser $(,$ty_var : Parser<Input=<$first as Parser>::Input>)*;
    impl <$first, $($ty_var),*> Parser for $name<$first $(,$ty_var)*>
        where $first: Parser $(, $ty_var : Parser<Input=<$first as Parser>::Input>)* {
        type Input = <$first as Parser>::Input;
        type Output = <$inner_type as Parser>::Output;
        fn parse_state(&mut self, input: State<<Self as Parser>::Input>) -> ParseResult<<Self as Parser>::Output, <Self as Parser>::Input, <Self::Input as Stream>::Item> {
            self.0.parse_state(input)
        }
        fn parse_lazy(&mut self, input: State<<Self as Parser>::Input>) -> ParseResult<<Self as Parser>::Output, <Self as Parser>::Input, <Self::Input as Stream>::Item> {
            self.0.parse_lazy(input)
        }
        fn add_error(&mut self, error: &mut ParseError<<Self::Input as Stream>::Item>) {
            self.0.add_error(error)
        }
    }
}
}

#[derive(Clone)]
pub struct Any<I>(PhantomData<fn (I) -> I>);

impl <I> Parser for Any<I>
    where I: Stream {
    type Input = I;
    type Output = I::Item;
    fn parse_lazy(&mut self, input: State<I>) -> ParseResult<I::Item, I, I::Item> {
        input.uncons()
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
/// assert_eq!(byte_parser.parse(&b"!"[..]).map(|x| x.0), Ok(&b'!'));
/// assert!(byte_parser.parse(&b""[..]).is_err());
/// # }
/// ```
pub fn any<I>() -> Any<I>
    where I: Stream {
    Any(PhantomData)
}



#[derive(Clone)]
pub struct Satisfy<I, P> { predicate: P, _marker: PhantomData<I> }

fn satisfy_impl<I, P, F>(input: State<I>, predicate: &mut P, f: F) -> ParseResult<I::Item, I, I::Item>
    where I: Stream
        , P: FnMut(I::Item) -> bool
        , F: FnOnce(<I::Item as Positioner>::Position, I::Item) -> ParseError<I::Item> {
    match input.input.clone().uncons() {
        Ok((c, s)) => {
            if (predicate)(c.clone()) { input.update(c, s) }
            else {
                Err(Consumed::Empty(f(input.position, c)))
            }
        }
        Err(err) => Err(Consumed::Empty(ParseError::new(input.position, err)))
    }
}

impl <I, P> Parser for Satisfy<I, P>
    where I: Stream, P: FnMut(I::Item) -> bool {

    type Input = I;
    type Output = I::Item;
    fn parse_lazy(&mut self, input: State<I>) -> ParseResult<I::Item, I, I::Item> {
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
    where I: Stream, P: FnMut(I::Item) -> bool {
    Satisfy { predicate: predicate, _marker: PhantomData }
}

#[derive(Clone)]
pub struct Token<I>
    where I: Stream
        , I::Item: PartialEq {
    c: I::Item,
    _marker: PhantomData<I>
}

impl <I> Parser for Token<I>
    where I: Stream
        , I::Item: PartialEq {

    type Input = I;
    type Output = I::Item;
    fn parse_lazy(&mut self, input: State<I>) -> ParseResult<I::Item, I, I::Item> {
        satisfy_impl(input, &mut |c| c == self.c, |pos, _| ParseError::empty(pos))
    }
    fn add_error(&mut self, error: &mut ParseError<<Self::Input as Stream>::Item>) {
        error.errors.push(Error::Expected(self.c.clone().into()));
    }
}

///Parses a character and succeeds if the characther is equal to `c`
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
    where I: Stream
        , I::Item: PartialEq {
    Token { c: c, _marker: PhantomData }
}

#[derive(Clone)]
pub struct Choice<S, P>(S, PhantomData<P>);

impl <I, O, S, P> Parser for Choice<S, P>
    where I: Stream
        , S: AsMut<[P]>
        , P: Parser<Input=I, Output=O> {
    type Input = I;
    type Output = O;
    fn parse_lazy(&mut self, input: State<I>) -> ParseResult<O, I, I::Item> {
        let mut empty_err = None;
        for p in AsMut::as_mut(&mut self.0) {
            match p.parse_lazy(input.clone()) {
                consumed_err@Err(Consumed::Consumed(_)) => return consumed_err,
                Err(Consumed::Empty(err)) => {
                    empty_err = match empty_err {
                        None => Some(err),
                        Some(prev_err) => Some(prev_err.merge(err)),
                    };
                },
                ok@Ok(_) => return ok,
            }
        }
        Err(Consumed::Empty(match empty_err {
            None => ParseError::new(input.position.clone(), Error::Message("parser choice is empty".into())),
            Some(err) => err,
        }))
    }
    fn add_error(&mut self, error: &mut ParseError<<Self::Input as Stream>::Item>) {
        for p in self.0.as_mut() {
            p.add_error(error);
        }
    }
}

/// Takes an array of parsers and tries them each in turn.
/// Fails if all parsers fails or when a parsers fails with a consumed state.
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
/// # }
/// ```
pub fn choice<S, P>(ps: S) -> Choice<S, P>
    where S: AsMut<[P]>
        , P: Parser {
    Choice(ps, PhantomData)
}

#[derive(Clone)]
pub struct Unexpected<I>(Info<I::Item>, PhantomData<fn (I) -> I>)
    where I: Stream;
impl <I> Parser for Unexpected<I>
    where I : Stream {
    type Input = I;
    type Output = ();
    fn parse_lazy(&mut self, input: State<I>) -> ParseResult<(), I, I::Item> {
        Err(Consumed::Empty(ParseError::empty(input.position)))
    }
    fn add_error(&mut self, error: &mut ParseError<<Self::Input as Stream>::Item>) {
        error.errors.push(Error::Message(self.0.clone()));
    }
}
///Always fails with `message` as the error.
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
/// assert!(result.err().unwrap().errors.iter().any(|m| *m == Error::Message("token".into())));
/// # }
/// ```
pub fn unexpected<I, S>(message: S) -> Unexpected<I>
    where I: Stream
        , S: Into<Info<I::Item>> {
    Unexpected(message.into(), PhantomData)
}

#[derive(Clone)]
pub struct Value<I, T>(T, PhantomData<fn (I) -> I>);
impl <I, T> Parser for Value<I, T>
    where I: Stream
        , T: Clone {
    type Input = I;
    type Output = T;
    fn parse_lazy(&mut self, input: State<I>) -> ParseResult<T, I, I::Item> {
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
    where I: Stream
        , T: Clone {
    Value(v, PhantomData)
}

impl_parser! { NotFollowedBy(P,), Or<Then<Try<P>, fn(<P as Parser>::Output) -> Unexpected<<P as Parser>::Input>>, Value<<P as Parser>::Input, ()>> }
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
    where P: Parser
        , <P as Parser>::Output: ::std::fmt::Display {
    fn f<T: ::std::fmt::Display, I: Stream>(t: T) -> Unexpected<I> {
        unexpected(format!("{}", t))
    }
    let f : fn (P::Output) -> Unexpected<P::Input> = f;
    NotFollowedBy(try(parser).then(f)
                 .or(value(())))
}

pub struct Iter<P: Parser> {
    parser: P,
    input: State<P::Input>,
    error: Option<Consumed<ParseError<<P::Input as Stream>::Item>>>,
    consumed: bool,
}

impl <P: Parser> Iter<P> {
    fn new(parser: P, input: State<P::Input>) -> Iter<P> {
        Iter { parser: parser, input: input, error: None, consumed: false }
    }
    ///Converts the iterator to a `ParseResult`, returning `Ok` if the parsing so far has be done
    ///without any errors which consumed data.
    pub fn into_result<O>(self, value: O) -> ParseResult<O, P::Input, <P::Input as Stream>::Item> {
        match self.error {
            Some(err@Consumed::Consumed(_)) => Err(err),
            _ => if self.consumed { Ok((value, Consumed::Consumed(self.input))) }
                 else { Ok((value, Consumed::Empty(self.input))) }
        }
    }
}

impl <P: Parser> Iterator for Iter<P> {
    type Item = P::Output;
    fn next(&mut self) -> Option<P::Output> {
        if self.error.is_some() {
            return None;
        }
        match self.parser.parse_lazy(self.input.clone()) {
            Ok((value, rest)) => {
                self.consumed = self.consumed || !rest.is_empty();
                self.input = rest.into_inner();
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
pub struct Many<F, P>(P, PhantomData<F>)
    where P: Parser;
impl <F, P> Parser for Many<F, P>
    where P: Parser, F: FromIterator<<P as Parser>::Output> {
    type Input = <P as Parser>::Input;
    type Output = F;
    fn parse_state(&mut self, input: State<<P as Parser>::Input>) -> ParseResult<F, <P as Parser>::Input, <Self::Input as Stream>::Item> {
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
    where P: Parser, F: FromIterator<<P as Parser>::Output> {
    Many(p, PhantomData)
}


#[derive(Clone)]
pub struct Many1<F, P>(P, PhantomData<fn () -> F>);
impl <F, P> Parser for Many1<F, P>
    where F: FromIterator<<P as Parser>::Output>
        , P: Parser {
    type Input = <P as Parser>::Input;
    type Output = F;
    fn parse_lazy(&mut self, input: State<<P as Parser>::Input>) -> ParseResult<F, <P as Parser>::Input, <Self::Input as Stream>::Item> {
        let (first, input) = try!(self.0.parse_lazy(input));
		input.combine(move |input| {
	        let mut iter = Iter::new(&mut self.0, input);
	        let result = Some(first).into_iter()
	            .chain(iter.by_ref())
	            .collect();
	        iter.into_result(result)
		})
    }
    fn add_error(&mut self, errors: &mut ParseError<<Self::Input as Stream>::Item>) {
        self.0.add_error(errors)
    }
}

impl_parser!{ SkipMany(P,), Map<Many<Vec<()>, Map<P, fn (<P as Parser>::Output)>>, fn (Vec<()>)> }
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
    where P: Parser {
    fn ignore<T>(_: T) {  }
    let ignore1: fn (P::Output) = ignore;
    let ignore2: fn (Vec<()>) = ignore;
    SkipMany(many(p.map(ignore1)).map(ignore2))
}

impl_parser!{ SkipMany1(P,), Map<Many1<Vec<()>, Map<P, fn (<P as Parser>::Output)>>, fn (Vec<()>)> }
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
    where P: Parser {
    fn ignore<T>(_: T) {  }
    let ignore1: fn (P::Output) = ignore;
    let ignore2: fn (Vec<()>) = ignore;
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
    where F: FromIterator<<P as Parser>::Output>
        , P: Parser {
    Many1(p, PhantomData)
}

#[derive(Clone)]
pub struct SepBy<F, P, S> {
    parser: P,
    separator: S,
    _marker: PhantomData<fn () -> F>
}
impl <F, P, S> Parser for SepBy<F, P, S>
    where F: FromIterator<<P as Parser>::Output>
        , P: Parser
        , S: Parser<Input=<P as Parser>::Input> {

    type Input = <P as Parser>::Input;
    type Output = F;
    fn parse_lazy(&mut self, input: State<<P as Parser>::Input>) -> ParseResult<F, <P as Parser>::Input, <Self::Input as Stream>::Item> {
        let mut input = Consumed::Empty(input);
        let first;
        match input.clone().combine(|input| self.parser.parse_lazy(input)) {
            Ok((x, rest)) => {
                input = rest;
                first = x
            }
            Err(err@Consumed::Consumed(_)) => return Err(err),
            Err(Consumed::Empty(_)) => return Ok((None.into_iter().collect(), input))
        };

        let (result, input) = try!(input.combine(move |input| {
            let rest = (&mut self.separator)
                .with(&mut self.parser);
	        let mut iter = Iter::new(rest, input);
	        let result = Some(first).into_iter()
	            .chain(iter.by_ref())
	            .collect();
        	iter.into_result(result)
        }));
        Ok((result, input))
    }
    fn add_error(&mut self, errors: &mut ParseError<<Self::Input as Stream>::Item>) {
        self.parser.add_error(errors)
    }
}

///Parses `parser` zero or more time separated by `separator`, returning a collection with the values from `p`.
///If the returned collection cannot be inferred type annotations must be supplied, either by
///annotating the resulting type binding `let collection: Vec<_> = ...` or by specializing when
///calling sep_by, `sep_by::<Vec<_>, _, _>(...)`
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
    where F: FromIterator<<P as Parser>::Output>
        , P: Parser
        , S: Parser<Input=<P as Parser>::Input> {
    SepBy { parser: parser, separator: separator, _marker: PhantomData }
}


impl <'a, I: Stream, O> Parser for FnMut(State<I>) -> ParseResult<O, I, I::Item> + 'a {
    type Input = I;
    type Output = O;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<O, I, I::Item> {
        self(input)
    }
}
#[derive(Clone)]
pub struct FnParser<I, F>(F, PhantomData<fn (I) -> I>);

///Wraps a function, turning it into a parser
///Mainly needed to turn closures into parsers as function types can be casted to function pointers
///to make them usable as a parser
///
/// ```
/// extern crate combine as pc;
/// use pc::*;
/// use pc::primitives::{Consumed, Error};
/// # fn main() {
/// let mut even_digit = parser(|input| {
///     let position = input.position;
///     let (char_digit, input) = try!(digit().parse_state(input));
///     let d = (char_digit as i32) - ('0' as i32);
///     if d % 2 == 0 {
///         Ok((d, input))
///     }
///     else {
///         //Return an empty error since we only tested the first token of the stream
///         Err(Consumed::Empty(ParseError::new(position, Error::Expected(From::from("even number")))))
///     }
/// });
/// let result = even_digit
///     .parse("8")
///     .map(|x| x.0);
/// assert_eq!(result, Ok(8));
/// # }
/// ```
pub fn parser<I, O, F>(f: F) -> FnParser<I, F>
    where I: Stream
        , F: FnMut(State<I>) -> ParseResult<O, I, I::Item> {
    FnParser(f, PhantomData)
}

impl <I, O, F> Parser for FnParser<I, F>
    where I: Stream, F: FnMut(State<I>) -> ParseResult<O, I, I::Item> {
    type Input = I;
    type Output = O;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<O, I, I::Item> {
        (self.0)(input)
    }
}

impl <I, O> Parser for fn (State<I>) -> ParseResult<O, I, I::Item>
    where I: Stream {
    type Input = I;
    type Output = O;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<O, I, I::Item> {
        self(input)
    }
}

#[derive(Clone)]
pub struct Optional<P>(P);
impl <P> Parser for Optional<P>
    where P: Parser {
    type Input = <P as Parser>::Input;
    type Output = Option<<P as Parser>::Output>;
    fn parse_lazy(&mut self, input: State<<P as Parser>::Input>) -> ParseResult<Option<<P as Parser>::Output>, <P as Parser>::Input, <Self::Input as Stream>::Item> {
        match self.0.parse_state(input.clone()) {
            Ok((x, rest)) => Ok((Some(x), rest)),
            Err(err@Consumed::Consumed(_)) => return Err(err),
            Err(Consumed::Empty(_)) => Ok((None, Consumed::Empty(input)))
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
    where P: Parser {
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
    where I: Stream
        , L: Parser<Input=I>
        , R: Parser<Input=I>
        , P: Parser<Input=I> {
    Between(open.with(parser).skip(close))
}

#[derive(Clone)]
pub struct Chainl1<P, Op>(P, Op);
impl <I, O, P, Op> Parser for Chainl1<P, Op>
    where I: Stream
        , P: Parser<Input=I, Output=O>
        , Op: Parser<Input=I>
        , Op::Output: FnOnce(O, O) -> O {

    type Input = I;
    type Output = O;
    fn parse_lazy(&mut self, input: State<I>) -> ParseResult<O, I, I::Item> {
        let (mut l, mut input) = try!(self.0.parse_lazy(input));
        loop {
            let was_empty = input.is_empty();
            let rest = input.clone().into_inner();
            match (&mut self.1).and(&mut self.0).parse_lazy(rest) {
                Ok(((op, r), rest)) => {
                    l = op(l, r);
                    input = if was_empty { rest } else { rest.as_consumed() };
                }
                Err(err@Consumed::Consumed(_)) => return Err(err),
                Err(Consumed::Empty(_)) => break
            }
        }
        Ok((l, input))
    }
    fn add_error(&mut self, errors: &mut ParseError<<Self::Input as Stream>::Item>) {
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
    where P: Parser
        , Op: Parser<Input=P::Input>
        , Op::Output: FnOnce(P::Output, P::Output) -> P::Output {
    Chainl1(parser, op)
}

#[derive(Clone)]
pub struct Chainr1<P, Op>(P, Op);
impl <I, O, P, Op> Parser for Chainr1<P, Op>
    where I: Stream
        , P: Parser<Input=I, Output=O>
        , Op: Parser<Input=I>
        , Op::Output: FnOnce(O, O) -> O {

    type Input = I;
    type Output = O;
    fn parse_lazy(&mut self, input: State<I>) -> ParseResult<O, I, I::Item> {
        let (mut l, mut input) = try!(self.0.parse_lazy(input));
        loop {
            let was_empty = input.is_empty();
            let rest = input.clone().into_inner();
            let op = match self.1.parse_lazy(rest) {
                Ok((x, rest)) => {
                    input = if was_empty { rest } else { rest.as_consumed() };
                    x
                }
                Err(err@Consumed::Consumed(_)) => return Err(err),
                Err(Consumed::Empty(_)) => break
            };
            let was_empty = was_empty && input.is_empty();
            let rest = input.clone().into_inner();
            match self.parse_lazy(rest) {
                Ok((r, rest)) => {
                    l = op(l, r);
                    input = if was_empty { rest } else { rest.as_consumed() };
                }
                Err(err@Consumed::Consumed(_)) => return Err(err),
                Err(Consumed::Empty(_)) => break
            }
            

        }
        Ok((l, input))
    }
    fn add_error(&mut self, errors: &mut ParseError<<Self::Input as Stream>::Item>) {
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
    where P: Parser
        , Op: Parser<Input=P::Input>
        , Op::Output: FnOnce(P::Output, P::Output) -> P::Output {
    Chainr1(parser, op)
}

#[derive(Clone)]
pub struct Try<P>(P);
impl <I, O, P> Parser for Try<P>
    where I: Stream
        , P: Parser<Input=I, Output=O> {

    type Input = I;
    type Output = O;
    fn parse_lazy(&mut self, input: State<I>) -> ParseResult<O, I, I::Item> {
        self.0.parse_state(input)
            .map_err(Consumed::as_empty)
    }
    fn add_error(&mut self, errors: &mut ParseError<<Self::Input as Stream>::Item>) {
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
pub fn try<P>(p : P) -> Try<P>
    where P: Parser {
    Try(p)
}

#[derive(Clone)]
pub struct And<P1, P2>(P1, P2);
impl <I, A, B, P1, P2> Parser for And<P1, P2>
    where I: Stream, P1: Parser<Input=I, Output=A>, P2: Parser<Input=I, Output=B> {

    type Input = I;
    type Output = (A, B);
    fn parse_lazy(&mut self, input: State<I>) -> ParseResult<(A, B), I, I::Item> {
        let (a, rest) = try!(self.0.parse_lazy(input));
        rest.combine(move |rest| {
            let (b, rest) = try!(self.1.parse_state(rest));
            Ok(((a, b), rest))
        })
    }
    fn add_error(&mut self, errors: &mut ParseError<<Self::Input as Stream>::Item>) {
        self.0.add_error(errors)
    }
}

#[derive(Clone)]
pub struct With<P1, P2>(P1, P2) where P1: Parser, P2: Parser;
impl <I, P1, P2> Parser for With<P1, P2>
    where I: Stream, P1: Parser<Input=I>, P2: Parser<Input=I> {

    type Input = I;
    type Output = <P2 as Parser>::Output;
    fn parse_lazy(&mut self, input: State<I>) -> ParseResult<<Self as Parser>::Output, I, I::Item> {
        let ((_, b), rest) = try!((&mut self.0).and(&mut self.1).parse_lazy(input));
        Ok((b, rest))
    }
    fn add_error(&mut self, errors: &mut ParseError<<Self::Input as Stream>::Item>) {
        self.0.add_error(errors)
    }
}

#[derive(Clone)]
pub struct Skip<P1, P2>(P1, P2) where P1: Parser, P2: Parser;
impl <I, P1, P2> Parser for Skip<P1, P2>
    where I: Stream, P1: Parser<Input=I>, P2: Parser<Input=I> {

    type Input = I;
    type Output = <P1 as Parser>::Output;
    fn parse_lazy(&mut self, input: State<I>) -> ParseResult<<Self as Parser>::Output, I, I::Item> {
        let ((a, _), rest) = try!((&mut self.0).and(&mut self.1).parse_lazy(input));
        Ok((a, rest))
    }
    fn add_error(&mut self, errors: &mut ParseError<<Self::Input as Stream>::Item>) {
        self.0.add_error(errors)
    }
}

#[derive(Clone)]
pub struct Message<P>(P, Info<<P::Input as Stream>::Item>)
    where P: Parser;
impl <I, P> Parser for Message<P>
    where I: Stream, P: Parser<Input=I> {

    type Input = I;
    type Output = <P as Parser>::Output;
    fn parse_lazy(&mut self, input: State<I>) -> ParseResult<<Self as Parser>::Output, I, I::Item> {
        self.0.parse_lazy(input.clone())
    }
    fn add_error(&mut self, errors: &mut ParseError<<Self::Input as Stream>::Item>) {
        self.0.add_error(errors);
        errors.add_message(self.1.clone());
    }
}

#[derive(Clone)]
pub struct Or<P1, P2>(P1, P2) where P1: Parser, P2: Parser;
impl <I, O, P1, P2> Parser for Or<P1, P2>
    where I: Stream, P1: Parser<Input=I, Output=O>, P2: Parser<Input=I, Output=O> {

    type Input = I;
    type Output = O;
    fn parse_lazy(&mut self, input: State<I>) -> ParseResult<O, I, I::Item> {
        match self.0.parse_lazy(input.clone()) {
            Ok(x) => Ok(x),
            Err(err@Consumed::Consumed(_)) => Err(err),
            Err(Consumed::Empty(error1)) => {
                match self.1.parse_lazy(input) {
                    Ok(x) => Ok(x),
                    Err(err@Consumed::Consumed(_)) => Err(err),
                    Err(Consumed::Empty(error2)) => Err(Consumed::Empty(error1.merge(error2)))
                }
            }
        }
    }
    fn add_error(&mut self, errors: &mut ParseError<<Self::Input as Stream>::Item>) {
        self.0.add_error(errors);
        self.1.add_error(errors);
    }
}

#[derive(Clone)]
pub struct Map<P, F>(P, F);
impl <I, A, B, P, F> Parser for Map<P, F>
    where I: Stream, P: Parser<Input=I, Output=A>, F: FnMut(A) -> B {

    type Input = I;
    type Output = B;
    fn parse_lazy(&mut self, input: State<I>) -> ParseResult<B, I, I::Item> {
        match self.0.parse_lazy(input) {
            Ok((x, input)) => Ok(((self.1)(x), input)),
            Err(err) => Err(err)
        }
    }
    fn add_error(&mut self, errors: &mut ParseError<<Self::Input as Stream>::Item>) {
        self.0.add_error(errors);
    }
}

#[derive(Clone)]
pub struct Then<P, F>(P, F);
impl <P, N, F> Parser for Then<P, F>
    where F: FnMut(<P as Parser>::Output) -> N
        , P: Parser
        , N: Parser<Input=<P as Parser>::Input> {

    type Input = <N as Parser>::Input;
    type Output = <N as Parser>::Output;
    fn parse_lazy(&mut self, input: State<<Self as Parser>::Input>) -> ParseResult<<Self as Parser>::Output, <Self as Parser>::Input, <Self::Input as Stream>::Item> {
        let (value, input) = try!(self.0.parse_lazy(input));
        input.combine(move |input| {
            let mut next = (self.1)(value);
            next.parse_state(input)
        })
    }
    fn add_error(&mut self, errors: &mut ParseError<<Self::Input as Stream>::Item>) {
        self.0.add_error(errors);
    }
}

#[derive(Clone)]
pub struct Expected<P>(P, Info<<P::Input as Stream>::Item>)
    where P: Parser;
impl <P> Parser for Expected<P>
    where P: Parser {

    type Input = <P as Parser>::Input;
    type Output = <P as Parser>::Output;
    fn parse_lazy(&mut self, input: State<<Self as Parser>::Input>) -> ParseResult<<Self as Parser>::Output, <Self as Parser>::Input, <Self::Input as Stream>::Item> {
        self.0.parse_lazy(input)
    }
    fn add_error(&mut self, errors: &mut ParseError<<Self::Input as Stream>::Item>) {
        let start = errors.errors.len();
        self.0.add_error(errors);
        //Replace all expected errors that where added from the previous add_error
        //with this expected error
        let mut i = 0;
        errors.errors.retain(|e| {
            if i < start {
                i += 1;
                true
            }
            else {
                match *e { Error::Expected(_) => false, _ => true }
            }
        });
        errors.add_error(Error::Expected(self.1.clone()));
    }
}

#[derive(Clone)]
pub struct AndThen<P, F>(P, F);
impl <P, F, O, E> Parser for AndThen<P, F>
    where P: Parser
        , F: FnMut(P::Output) -> Result<O, E>
        , E: Into<Error<<P::Input as Stream>::Item>> {

    type Input = <P as Parser>::Input;
    type Output = O;
    fn parse_lazy(&mut self, input: State<<Self as Parser>::Input>) -> ParseResult<O, <Self as Parser>::Input, <Self::Input as Stream>::Item> {
        self.0.parse_lazy(input)
            .and_then(|(o, input)|
                match (self.1)(o) {
                    Ok(o) => Ok((o, input)),
                    Err(err) => Err(input.map(move |input| ParseError::new(input.position, err.into())))
                }
            )
    }
    fn add_error(&mut self, errors: &mut ParseError<<Self::Input as Stream>::Item>) {
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
        where P2: Parser<Input=Self::Input> {
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
        where P2: Parser<Input=Self::Input> {
        Skip(self, p)
    }

    ///Parses with `self` followed by `p`
    ///Succeds if both parsers succed, otherwise fails
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
        where P2: Parser<Input=Self::Input> {
        And(self, p)
    }
    ///Tries to parse using `self` and if it fails returns the result of parsing `p`
    ///
    /// ```
    /// # extern crate combine as pc;
    /// # use pc::*;
    /// # fn main() {
    /// let result = digit().map(|_| "")
    ///     .or(string("let"))
    ///     .parse("let")
    ///     .map(|x| x.0);
    /// assert_eq!(result, Ok("let"));
    /// # }
    /// ```
    fn or<P2>(self, p: P2) -> Or<Self, P2>
        where P2: Parser<Input=Self::Input> {
        Or(self, p)
    }

    ///Parses using `self` and then passes the value to `f` which returns a parser used to parse
    ///the rest of the input
    ///
    /// ```
    /// # extern crate combine as pc;
    /// # use pc::*;
    /// # use pc::primitives::{Consumed, Error};
    /// # fn main() {
    /// let result = digit()
    ///     .then(|d| parser(move |input| {
    ///         if d == '9' {
    ///             Ok((9, Consumed::Empty(input)))
    ///         }
    ///         else {
    ///             let err = ParseError::new(input.position, Error::Message("Not a nine".into()));
    ///             Err((Consumed::Empty(err)))
    ///         }
    ///     }))
    ///     .parse("9");
    /// assert_eq!(result, Ok((9, "")));
    /// # }
    /// ```
    fn then<N, F>(self, f: F) -> Then<Self, F>
        where F: FnMut(Self::Output) -> N
            , N: Parser<Input=Self::Input> {
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
        where F: FnMut(Self::Output) -> B {
        Map(self, f)
    }

    ///Parses with `self` and if it fails, adds the message `msg` to the error
    ///
    /// ```
    /// # extern crate combine as pc;
    /// # use pc::*;
    /// # use pc::primitives::Error;
    /// # fn main() {
    /// let result = token('9')
    ///     .message("Not a nine")
    ///     .parse("8");
    /// assert!(result.is_err());
    /// assert!(result.unwrap_err().errors.iter()
    ///     .find(|e| **e == Error::Message("Not a nine".into())).is_some());
    /// # }
    /// ```
    fn message<S>(self, msg: S) -> Message<Self>
        where S: Into<Info<<Self::Input as Stream>::Item>> {
        Message(self, msg.into())
    }

    ///Parses with `self` and if it fails without consuming any input any expected errors are replaced by
    ///`msg`. `msg` is then used in error messages as "Expected `msg`".
    ///
    /// ```
    /// # extern crate combine as pc;
    /// # use pc::*;
    /// # use pc::primitives::Error;
    /// # fn main() {
    /// let result = token('9')
    ///     .expected("9")
    ///     .parse("8");
    /// assert!(result.is_err());
    /// assert!(result.unwrap_err().errors.iter()
    ///     .find(|e| **e == Error::Expected("9".into())).is_some());
    /// # }
    /// ```
    fn expected<S>(self, msg: S) -> Expected<Self>
        where S: Into<Info<<Self::Input as Stream>::Item>> {
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
        where F: FnMut(Self::Output) -> Result<O, E>
            , E: Into<Error<<Self::Input as Stream>::Item>> {
        AndThen(self, f)
    }

    ///Creates an iterator from a parser and a state. Can be used as an alternative to `many` when
    ///collecting directly into a `FromIterator` type is not desirable
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
    fn iter(self, input: State<Self::Input>) -> Iter<Self> {
        Iter::new(self, input)
    }
}

impl <P: Parser> ParserExt for P { }

macro_rules! tuple_parser {
    ($h: ident, $($id: ident),+) => {
        impl <Input: Stream, $h: Parser<Input=Input>, $($id: Parser<Input=Input>),+> Parser for ($h, $($id),+) {
            type Input = Input;
            type Output = ($h::Output, $($id::Output),+);
            #[allow(non_snake_case)]
            fn parse_lazy(&mut self, input: State<Input>) -> ParseResult<($h::Output, $($id::Output),+), Input, Input::Item> {
                let (ref mut $h, $(ref mut $id),+) = *self;
                let ($h, input) = try!($h.parse_lazy(input));
                $(let ($id, input) = try!(input.combine(|input| $id.parse_state(input)));)+
                Ok((($h, $($id),+), input))
            }
            fn add_error(&mut self, errors: &mut ParseError<<Self::Input as Stream>::Item>) {
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

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::{Error, ParseError, Positioner, Parser};
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
        let result_err: Result<(Vec<(char, char)>, &str), ParseError<char>> = parser2.parse("a,bc");
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
        assert_eq!(parser.parse("a"), Err(ParseError {
            position: char::start(),
            errors: vec![Error::Unexpected('a'.into()),
                         Error::Message("message".into()),
                         Error::Expected("my expected digit".into())]
        }));
    }
    #[test]
    fn tuple_parse_error() {
        let mut parser = (digit(), digit());
        let result = parser.parse("a");
        assert_eq!(result, Err(ParseError {
            position: char::start(),
            errors: vec![
                Error::Unexpected('a'.into()),
                Error::Expected("digit".into())]
        }));
    }
}

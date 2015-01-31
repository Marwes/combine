
use std::iter::FromIterator;
use primitives::{Parser, ParseResult, ParseError, Stream, State, Error, Consumed};

macro_rules! impl_parser {
    ($name: ident ($first: ident, $($ty_var: ident),*), $inner_type: ty) => {
    #[derive(Clone)]
    pub struct $name<$first $(,$ty_var)*>($inner_type)
        where $first: Parser $(,$ty_var : Parser<Input=<$first as Parser>::Input>)*;
    impl <$first, $($ty_var),*> Parser for $name<$first $(,$ty_var)*>
        where $first: Parser $(, $ty_var : Parser<Input=<$first as Parser>::Input>)* {
        type Input = <$first as Parser>::Input;
        type Output = <$inner_type as Parser>::Output;
        fn parse_state(&mut self, input: State<<Self as Parser>::Input>) -> ParseResult<<Self as Parser>::Output, <Self as Parser>::Input> {
            self.0.parse_state(input)
        }
    }
}
}

struct Iter<P: Parser> {
    parser: P,
    input: Consumed<State<P::Input>>,
    error: Option<Consumed<ParseError>>
}

impl <P: Parser> Iter<P> {
    fn new(parser: P, input: State<P::Input>) -> Iter<P> {
        Iter { parser: parser, input: Consumed::Empty(input), error: None }
    }
    fn into_result<O>(self, result: O) -> ParseResult<O, P::Input> {
        match self.error {
            Some(err@Consumed::Consumed(_)) => Err(err),
            _ => Ok((result, self.input))
        }
    }
}

impl <P: Parser> Iterator for Iter<P> {
    type Item = P::Output;
    fn next(&mut self) -> Option<P::Output> {
        if self.error.is_some() {
            return None;
        }
        let was_empty = self.input.is_empty();
        match self.parser.parse_state(self.input.clone().into_inner()) {
            Ok((value, rest)) => {
                self.input = if was_empty { rest } else { rest.as_consumed() };
                Some(value)
            }
            Err(err) => {
                self.error = Some(err);
                None
            }
        }
    }
}

pub struct ChoiceSlice<'a, P>(&'a mut [P])
    where P: Parser + 'a;

impl <'a, I, O, P> Parser for ChoiceSlice<'a, P>
    where I: Stream
        , P: Parser<Input=I, Output=O> + 'a {
    type Input = I;
    type Output = O;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<O, I> {
        if self.0.len() == 0 { // err: slice empty of parsers
            return Err(Consumed::Empty(ParseError { position: input.position.clone(), errors: vec![] }))
        }
        for i in range(0, self.0.len()) {
            match self.0[i].parse_state(input.clone()) {
                Err(_) => {},
                Ok(x) => {
                    return Ok(x)
                }
            }
        }
        // err: no parsers matched
        Err(Consumed::Empty(ParseError { position: input.position.clone(), errors: vec![] }))
    }
}


pub fn choice_slice<'a, P>(ps: &'a mut [P]) -> ChoiceSlice<'a, P>
    where P: Parser + 'a {
    ChoiceSlice(ps)
}

#[derive(Clone)]
pub struct Many<F, P>(P)
    where P: Parser;
impl <F, P> Parser for Many<F, P>
    where P: Parser, F: FromIterator<<P as Parser>::Output> {
    type Input = <P as Parser>::Input;
    type Output = F;
    fn parse_state(&mut self, input: State<<P as Parser>::Input>) -> ParseResult<F, <P as Parser>::Input> {
        let mut iter = Iter::new(&mut self.0, input);
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
/// # extern crate "parser-combinators" as pc;
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
    Many(p)
}

#[derive(Clone)]
pub struct Unexpected<I>(String);
impl <I> Parser for Unexpected<I>
    where I : Stream {
    type Input = I;
    type Output = ();
    fn parse_state(&mut self, input: State<I>) -> ParseResult<(), I> {
        Err(Consumed::Empty(ParseError::new(input.position, Error::Message(self.0.clone()))))
    }
}
///Always fails with `message` as the error.
///Never consumes any input.
///
/// ```
/// # extern crate "parser-combinators" as pc;
/// # use pc::*;
/// # use pc::primitives::Error;
/// # fn main() {
/// let result = unexpected("token".to_string())
///     .parse("a");
/// assert!(result.is_err());
/// assert_eq!(result.err().unwrap().errors[0], Error::Message("token".to_string()));
/// # }
/// ```
pub fn unexpected<I>(message: String) -> Unexpected<I>
    where I: Stream {
    Unexpected(message)
}

#[derive(Clone)]
pub struct Value<I, T>(T);
impl <I, T> Parser for Value<I, T>
    where I: Stream
        , T: Clone {
    type Input = I;
    type Output = T;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<T, I> {
        Ok((self.0.clone(), Consumed::Empty(input)))
    }
}
///Always returns the value `v` without consuming any input.
///
/// ```
/// # extern crate "parser-combinators" as pc;
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
    Value(v)
}

impl_parser! { NotFollowedBy(P,), Or<Then<Try<P>, Unexpected<<P as Parser>::Input>, fn(<P as Parser>::Output) -> Unexpected<<P as Parser>::Input>>, Value<<P as Parser>::Input, ()>> }
///Succeeds only if `parser` fails.
///Never consumes any input.
///
/// ```
/// # extern crate "parser-combinators" as pc;
/// # use pc::*;
/// # fn main() {
/// let result = string("let")
///     .skip(not_followed_by(satisfy(|c| c.is_alphanumeric())))
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
    NotFollowedBy(try(parser).then(f as fn (_) -> _)
                 .or(value(())))
}

#[derive(Clone)]
pub struct Many1<F, P>(P);
impl <F, P> Parser for Many1<F, P>
    where F: FromIterator<<P as Parser>::Output>
        , P: Parser {
    type Input = <P as Parser>::Input;
    type Output = F;
    fn parse_state(&mut self, input: State<<P as Parser>::Input>) -> ParseResult<F, <P as Parser>::Input> {
        let (first, input) = try!(self.0.parse_state(input));
		input.combine(move |input| {
	        let mut iter = Iter::new(&mut self.0, input);
	        let result = Some(first).into_iter()
	            .chain(iter.by_ref())
	            .collect();
	        iter.into_result(result)
		})
    }
}

///Parses `p` one or more times returning a collection with the values from `p`.
///If the returned collection cannot be inferred type annotations must be supplied, either by
///annotating the resulting type binding `let collection: Vec<_> = ...` or by specializing when
///calling many1 `many1::<Vec<_>, _>(...)`
///
///
/// ```
/// # extern crate "parser-combinators" as pc;
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
    Many1(p)
}

#[derive(Clone)]
pub struct SepBy<F, P, S> {
    parser: P,
    separator: S
}
impl <F, P, S> Parser for SepBy<F, P, S>
    where F: FromIterator<<P as Parser>::Output>
        , P: Parser
        , S: Parser<Input=<P as Parser>::Input> {

    type Input = <P as Parser>::Input;
    type Output = F;
    fn parse_state(&mut self, input: State<<P as Parser>::Input>) -> ParseResult<F, <P as Parser>::Input> {
        let mut input = Consumed::Empty(input);
        let first;
        match input.clone().combine(|input| self.parser.parse_state(input)) {
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
}

///Parses `parser` zero or more time separated by `separator`, returning a collection with the values from `p`.
///If the returned collection cannot be inferred type annotations must be supplied, either by
///annotating the resulting type binding `let collection: Vec<_> = ...` or by specializing when
///calling sep_by, `sep_by::<Vec<_>, _, _>(...)`
///
/// ```
/// # extern crate "parser-combinators" as pc;
/// # use pc::*;
/// # fn main() {
/// let result = sep_by(digit(), satisfy(|c| c == ','))
///     .parse("1,2,3")
///     .map(|x| x.0);
/// assert_eq!(result, Ok(vec!['1', '2', '3']));
/// # }
/// ```
pub fn sep_by<F, P, S>(parser: P, separator: S) -> SepBy<F, P, S>
    where F: FromIterator<<P as Parser>::Output>
        , P: Parser
        , S: Parser<Input=<P as Parser>::Input> {
    SepBy { parser: parser, separator: separator }
}


impl <'a, I: Stream, O> Parser for FnMut(State<I>) -> ParseResult<O, I> + 'a {
    type Input = I;
    type Output = O;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<O, I> {
        self(input)
    }
}
#[derive(Clone)]
pub struct FnParser<I, O, F>(pub F)
    where I: Stream
        , F: FnMut(State<I>) -> ParseResult<O, I>;

impl <I, O, F> Parser for FnParser<I, O, F>
    where I: Stream, F: FnMut(State<I>) -> ParseResult<O, I> {
    type Input = I;
    type Output = O;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<O, I> {
        (self.0)(input)
    }
}

impl <I, O> Parser for fn (State<I>) -> ParseResult<O, I>
    where I: Stream {
    type Input = I;
    type Output = O;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<O, I> {
        self(input)
    }
}


#[derive(Clone)]
pub struct And<P1, P2>(P1, P2);
impl <I, A, B, P1, P2> Parser for And<P1, P2>
    where I: Stream, P1: Parser<Input=I, Output=A>, P2: Parser<Input=I, Output=B> {

    type Input = I;
    type Output = (A, B);
    fn parse_state(&mut self, input: State<I>) -> ParseResult<(A, B), I> {
        let (a, rest) = try!(self.0.parse_state(input));
        rest.combine(move |rest| {
            let (b, rest) = try!(self.1.parse_state(rest));
            Ok(((a, b), rest))
        })
    }
}

#[derive(Clone)]
pub struct Optional<P>(P);
impl <P> Parser for Optional<P>
    where P: Parser {
    type Input = <P as Parser>::Input;
    type Output = Option<<P as Parser>::Output>;
    fn parse_state(&mut self, input: State<<P as Parser>::Input>) -> ParseResult<Option<<P as Parser>::Output>, <P as Parser>::Input> {
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
/// # extern crate "parser-combinators" as pc;
/// # use pc::*;
/// # fn main() {
/// let result = optional(digit())
///     .parse("a")
///     .map(|x| x.0);
/// assert_eq!(result, Ok(None));
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
/// # extern crate "parser-combinators" as pc;
/// # use pc::*;
/// # fn main() {
/// let result = between(string("["), string("]"), string("rust"))
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
pub struct With<P1, P2>(P1, P2) where P1: Parser, P2: Parser;
impl <I, P1, P2> Parser for With<P1, P2>
    where I: Stream, P1: Parser<Input=I>, P2: Parser<Input=I> {

    type Input = I;
    type Output = <P2 as Parser>::Output;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<<Self as Parser>::Output, I> {
        let ((_, b), rest) = try!((&mut self.0).and(&mut self.1).parse_state(input));
        Ok((b, rest))
    }
}

#[derive(Clone)]
pub struct Skip<P1, P2>(P1, P2) where P1: Parser, P2: Parser;
impl <I, P1, P2> Parser for Skip<P1, P2>
    where I: Stream, P1: Parser<Input=I>, P2: Parser<Input=I> {

    type Input = I;
    type Output = <P1 as Parser>::Output;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<<Self as Parser>::Output, I> {
        let ((a, _), rest) = try!((&mut self.0).and(&mut self.1).parse_state(input));
        Ok((a, rest))
    }
}

#[derive(Clone)]
pub struct Message<P>(P, String) where P: Parser;
impl <I, P> Parser for Message<P>
    where I: Stream, P: Parser<Input=I> {

    type Input = I;
    type Output = <P as Parser>::Output;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<<Self as Parser>::Output, I> {
        match self.0.parse_state(input.clone()) {
            Ok(x) => Ok(x),
            Err(err@Consumed::Consumed(_)) => Err(err),
            Err(Consumed::Empty(mut err)) => {
                err.add_message(self.1.clone());
                Err(Consumed::Empty(err))
            }
        }
    }
}

#[derive(Clone)]
pub struct Or<P1, P2>(P1, P2) where P1: Parser, P2: Parser;
impl <I, O, P1, P2> Parser for Or<P1, P2>
    where I: Stream, P1: Parser<Input=I, Output=O>, P2: Parser<Input=I, Output=O> {

    type Input = I;
    type Output = O;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<O, I> {
        match self.0.parse_state(input.clone()) {
            Ok(x) => Ok(x),
            Err(err@Consumed::Consumed(_)) => Err(err),
            Err(Consumed::Empty(error1)) => {
                match self.1.parse_state(input) {
                    Ok(x) => Ok(x),
                    Err(err@Consumed::Consumed(_)) => Err(err),
                    Err(Consumed::Empty(error2)) => Err(Consumed::Empty(error1.merge(error2)))
                }
            }
        }
    }
}

#[derive(Clone)]
pub struct Map<P, F, B>(P, F);
impl <I, A, B, P, F> Parser for Map<P, F, B>
    where I: Stream, P: Parser<Input=I, Output=A>, F: FnMut(A) -> B {

    type Input = I;
    type Output = B;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<B, I> {
        match self.0.parse_state(input.clone()) {
            Ok((x, input)) => Ok(((self.1)(x), input)),
            Err(err) => Err(err)
        }
    }
}

#[derive(Clone)]
pub struct Chainl1<P, Op>(P, Op);
impl <'a, I, O, P, Op> Parser for Chainl1<P, Op>
    where I: Stream
        , P: Parser<Input=I, Output=O>
        , Op: Parser<Input=I, Output=Box<FnMut(O, O) -> O + 'a>> {

    type Input = I;
    type Output = O;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<O, I> {
        let (mut l, mut input) = try!(self.0.parse_state(input));
        loop {
            let was_empty = input.is_empty();
            let rest = input.clone().into_inner();
            match (&mut self.1).and(&mut self.0).parse_state(rest) {
                Ok(((mut op, r), rest)) => {
                    l = op(l, r);
                    input = if was_empty { rest } else { rest.as_consumed() };
                }
                Err(err@Consumed::Consumed(_)) => return Err(err),
                Err(_) => break
            }
            

        }
        Ok((l, input))
    }
}

///Parses `p` 1 or more times separated by `op`
///The value returned is the one produced by the left associative application of `op`
pub fn chainl1<'a, I, O, P, Op>(parser: P, op: Op) -> Chainl1<P, Op>
    where I: Stream
        , P: Parser<Input=I, Output=O>
        , Op: Parser<Input=I, Output=Box<FnMut(O, O) -> O + 'a>> {
    Chainl1(parser, op)
}

#[derive(Clone)]
pub struct Try<P>(P);
impl <I, O, P> Parser for Try<P>
    where I: Stream
        , P: Parser<Input=I, Output=O> {

    type Input = I;
    type Output = O;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<O, I> {
        self.0.parse_state(input)
            .map_err(Consumed::as_empty)
    }
}

#[derive(Clone)]
pub struct Then<P, N, F>(P, F);
impl <P, N, F> Parser for Then<P, N, F>
    where F: FnMut(<P as Parser>::Output) -> N
        , P: Parser
        , N: Parser<Input=<P as Parser>::Input> {

    type Input = <N as Parser>::Input;
    type Output = <N as Parser>::Output;
    fn parse_state(&mut self, input: State<<Self as Parser>::Input>) -> ParseResult<<Self as Parser>::Output, <Self as Parser>::Input> {
        let (value, input) = try!(self.0.parse_state(input));
        input.combine(move |input| {
            let mut next = (self.1)(value);
            next.parse_state(input)
        })
    }
}

///Try acts as `p` except it acts as if the parser hadn't consumed any input
///if `p` returns an error after consuming input
///
/// ```
/// # extern crate "parser-combinators" as pc;
/// # use pc::*;
/// # fn main() {
/// let mut p = try(string("let"))
///     .or(string("lex"));
/// let result = p.parse("lex").map(|x| x.0);
/// assert_eq!(result, Ok("lex"));
/// # }
/// ```
pub fn try<P>(p : P) -> Try<P>
    where P: Parser {
    Try(p)
}

///Extension trait which provides functions that are more conveniently used through method calls
pub trait ParserExt : Parser + Sized {

    ///Discards the value of the `self` parser and returns the value of `p`
    ///Fails if any of the parsers fails
    fn with<P2>(self, p: P2) -> With<Self, P2>
        where P2: Parser {
        With(self, p)
    }

    ///Discards the value of the `p` parser and returns the value of `self`
    ///Fails if any of the parsers fails
    fn skip<P2>(self, p: P2) -> Skip<Self, P2>
        where P2: Parser {
        Skip(self, p)
    }

    ///Parses with `self` followed by `p`
    ///Succeds if both parsers succed, otherwise fails
    ///Returns a tuple with both values on success
    ///
    /// ```
    /// # extern crate "parser-combinators" as pc;
    /// # use pc::*;
    /// # fn main() {
    /// let result = digit()
    ///     .and(satisfy(|c| c == 'i'))
    ///     .parse("9i")
    ///     .map(|x| x.0);
    /// assert_eq!(result, Ok(('9', 'i')));
    /// # }
    /// ```
    fn and<P2>(self, p: P2) -> And<Self, P2>
        where P2: Parser {
        And(self, p)
    }
    ///Tries to parse using `self` and if it fails returns the result of parsing `p`
    ///
    /// ```
    /// # extern crate "parser-combinators" as pc;
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
        where P2: Parser {
        Or(self, p)
    }

    ///Parses using `self` and then passes the value to `f` which returns the parser used to parse
    ///the rest of the input
    fn then<N, F>(self, f: F) -> Then<Self, N, F>
        where F: FnMut(Self::Output) -> N
            , N: Parser<Input=Self::Input> {
        Then(self, f)
    }

    ///Uses `f` to map over the parsed value
    fn map<F, B>(self, f: F) -> Map<Self, F, B>
        where F: FnMut(Self::Output) -> B {
        Map(self, f)
    }

    ///Parses with `self` and if it fails, adds the message msg to the error
    fn message(self, msg: String) -> Message<Self> {
        Message(self, msg)
    }
}

impl <P: Parser> ParserExt for P { }

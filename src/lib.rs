//! This crate contains parser combinators, roughly based on the Haskell library
//! [parsec](http://hackage.haskell.org/package/parsec).
//!
//! A parser in this library can be described as a function which takes some input and if it
//! is succesful, returns a value together with the remaining input.
//! A parser combinator is a function which takes one or more parsers and returns a new parser.
//! For instance the `many` parser can be used to convert a parser for single digits into one that
//! parses multiple digits. By modeling parsers in this way it becomes simple to compose complex
//! parsers in an almost declarative way.
//!
//! # Overview
//!
//! `combine` limits itself to creating [LL(1) parsers](https://en.wikipedia.org/wiki/LL_parser)
//! (it is possible to opt-in to LL(k) parsing using the `try` combinator) which makes the
//! parsers easy to reason about in both function and performance while sacrificing
//! some generality. In addition to you being able to reason better about the parsers you
//! construct `combine` the library also takes the knowledge of being an LL parser and uses it to
//! automatically construct good error messages.
//!
//! ```rust
//! extern crate combine;
//! use combine::{Parser, ParserExt};
//! use combine::char::{digit, letter};
//!
//! fn main() {
//!     if let Err(err) = digit().or(letter()).parse("|") {
//!         println!("{}", err);
//!         // The println! call above prints
//!         //
//!         // Parse error at line: 1, column: 1
//!         // Unexpected '|'
//!         // Expected 'digit' or 'letter'
//!     }
//! }
//! ```
//!
//! This library currently contains three modules.
//!
//! * `combinator` contains the before mentioned parser combinators and thus contains the main
//! building blocks for creating any sort of complex parsers. It consists of free functions `such`
//! as `many` and `satisfy` as well as a the `ParserExt` trait which provides a few functions such
//! as `or` which are more natural to use method calls.
//!
//! * `char` provides parsers specifically working with streams of characters.
//! As a few examples it has parsers for accepting digits, letters or whitespace.
//!
//! * `primitives` contains the `Parser` and `Stream` traits which are the core abstractions in
//! combine as well as various structs dealing with input streams and errors. You usually only need
//! to use this module if you want more control over parsing and input streams.
//!
//! # Examples
//!
//! ```
//! extern crate combine;
//! use combine::char::{spaces, digit, char};
//! use combine::{many1, sep_by, Parser, ParserExt, ParseError};
//!
//! fn main() {
//!     //Parse spaces first and use the with method to only keep the result of the next parser
//!     let integer = spaces()
//!         //parse a string of digits into an i32
//!         .with(many1(digit()).map(|string: String| string.parse::<i32>().unwrap()));
//!
//!     //Parse integers separated by commas, skipping whitespace
//!     let mut integer_list = sep_by(integer, spaces().skip(char(',')));
//!
//!     //Call parse with the input to execute the parser
//!     let input = "1234, 45,78";
//!     let result: Result<(Vec<i32>, &str), ParseError<&str>> = integer_list.parse(input);
//!     match result {
//!         Ok((value, _remaining_input)) => println!("{:?}", value),
//!         Err(err) => println!("{}", err)
//!     }
//! }
//! ```
//!
//! If we need a parser that is mutually recursive we can define a free function which internally
//! can in turn be used as a parser by using the `parser` function which turns a function with the
//! correct signature into a parser. In this case we define `expr` to work on any type of `Stream`
//! which is combine's way of abstracting over different data sources such as array slices, string
//! slices, iterators etc. If instead you would only need to parse string already in memory you
//! could define `expr` as `fn expr(input: &str) -> ParseResult<Expr, &str>`
//!
//! ```
//! extern crate combine;
//! use combine::char::{char, letter, spaces};
//! use combine::{between, many1, parser, sep_by, Parser, ParserExt};
//! use combine::primitives::{State, Stream, ParseResult};
//!
//! #[derive(Debug, PartialEq)]
//! enum Expr {
//!     Id(String),
//!     Array(Vec<Expr>),
//!     Pair(Box<Expr>, Box<Expr>)
//! }
//!
//! fn expr<I>(input: I) -> ParseResult<Expr, I>
//!     where I: Stream<Item=char>
//! {
//!     let word = many1(letter());
//!
//!     //Creates a parser which parses a char and skips any trailing whitespace
//!     let lex_char = |c| char(c).skip(spaces());
//!
//!     let comma_list = sep_by(parser(expr::<I>), lex_char(','));
//!     let array = between(lex_char('['), lex_char(']'), comma_list);
//!
//!     //We can use tuples to run several parsers in sequence
//!     //The resulting type is a tuple containing each parsers output
//!     let pair = (lex_char('('),
//!                 parser(expr::<I>),
//!                 lex_char(','),
//!                 parser(expr::<I>),
//!                 lex_char(')'))
//!                    .map(|t| Expr::Pair(Box::new(t.1), Box::new(t.3)));
//!
//!     word.map(Expr::Id)
//!         .or(array.map(Expr::Array))
//!         .or(pair)
//!         .skip(spaces())
//!         .parse_state(input)
//! }
//!
//! fn main() {
//!     let result = parser(expr)
//!         .parse("[[], (hello, world), [rust]]");
//!     let expr = Expr::Array(vec![
//!           Expr::Array(Vec::new())
//!         , Expr::Pair(Box::new(Expr::Id("hello".to_string())),
//!                      Box::new(Expr::Id("world".to_string())))
//!         , Expr::Array(vec![Expr::Id("rust".to_string())])
//!     ]);
//!     assert_eq!(result, Ok((expr, "")));
//! }
//! ```

#[doc(inline)]
pub use primitives::{Parser, ParseError, ParseResult, State, from_iter, Stream, StreamOnce};
#[doc(inline)]
pub use combinator::{any, between, chainl1, chainr1, choice, eof, env_parser, many, many1,
                     optional, parser, satisfy, satisfy_map, sep_by, sep_by1, sep_end_by,
                     sep_end_by1, skip_many, skip_many1, token, try, look_ahead, value,
                     unexpected, not_followed_by, ParserExt};

macro_rules! static_fn {
    (($($arg: pat, $arg_ty: ty),*) -> $ret: ty { $body: expr }) => { {
        fn temp($($arg: $arg_ty),*) -> $ret { $body }
        let temp: fn (_) -> _ = temp;
        temp
    } }
}

/// Module containing the primitive types which is used to create and compose more advanced parsers
#[macro_use]
pub mod primitives;
/// Module containing all specific parsers
pub mod combinator;
/// Module containing parsers specialized on character streams
pub mod char;
/// Module containing zero-copy parsers
pub mod range;

#[cfg(test)]
mod tests {
    use super::*;
    use super::primitives::{SourcePosition, Error, Consumed};
    use char::{alpha_num, char, digit, letter, spaces, string};


    fn integer<'a, I>(input: I) -> ParseResult<i64, I>
        where I: Stream<Item = char>
    {
        let (s, input) = try!(many1::<String, _>(digit())
            .expected("integer")
            .parse_state(input));
        let mut n = 0;
        for c in s.chars() {
            n = n * 10 + (c as i64 - '0' as i64);
        }
        Ok((n, input))
    }

    #[test]
    fn test_integer() {
        let result = parser(integer).parse("123");
        assert_eq!(result, Ok((123i64, "")));
    }
    #[test]
    fn list() {
        let mut p = sep_by(parser(integer), char(','));
        let result = p.parse("123,4,56");
        assert_eq!(result, Ok((vec![123i64, 4, 56], "")));
    }
    #[test]
    fn iterator() {
        let result = parser(integer)
            .parse(from_iter("123".chars()))
            .map(|(i, mut input)| (i, input.uncons().is_err()));
        assert_eq!(result, Ok((123i64, true)));
    }
    #[test]
    fn field() {
        let word = || many(alpha_num());
        let spaces = spaces();
        let c_decl = (word(), spaces.clone(), char(':'), spaces, word())
            .map(|t| (t.0, t.4))
            .parse("x: int");
        assert_eq!(c_decl, Ok((("x".to_string(), "int".to_string()), "")));
    }
    #[test]
    fn source_position() {
        let source = r"
123
";
        let result = (spaces(), parser(integer), spaces())
            .map(|t| t.1)
            .parse_state(State::new(source));
        let state = Consumed::Consumed(State {
            position: SourcePosition {
                line: 3,
                column: 1,
            },
            input: "",
        });
        assert_eq!(result, Ok((123i64, state)));
    }

    #[derive(Debug, PartialEq)]
    enum Expr {
        Id(String),
        Int(i64),
        Array(Vec<Expr>),
        Plus(Box<Expr>, Box<Expr>),
        Times(Box<Expr>, Box<Expr>),
    }

    #[allow(unconditional_recursion)]
    fn expr<I>(input: I) -> ParseResult<Expr, I>
        where I: Stream<Item = char>
    {
        let word = many1(letter()).expected("identifier");
        let integer = parser(integer);
        let array = between(char('['), char(']'), sep_by(parser(expr), char(','))).expected("[");
        let paren_expr = between(char('('), char(')'), parser(term)).expected("(");
        let spaces = spaces();
        spaces.clone()
            .with(word.map(Expr::Id)
                .or(integer.map(Expr::Int))
                .or(array.map(Expr::Array))
                .or(paren_expr))
            .skip(spaces)
            .parse_state(input)
    }

    #[test]
    fn expression() {
        let result = sep_by(parser(expr), char(',')).parse("int, 100, [[], 123]");
        let exprs = vec![Expr::Id("int".to_string()),
                         Expr::Int(100),
                         Expr::Array(vec![Expr::Array(vec![]), Expr::Int(123)])];
        assert_eq!(result, Ok((exprs, "")));
    }

    #[test]
    fn expression_error() {
        let input = r"
,123
";
        let result = parser(expr).parse(State::new(input));
        let err = ParseError {
            position: SourcePosition {
                line: 2,
                column: 1,
            },
            errors: vec![
                    Error::Unexpected(','.into()),
                    Error::Expected("integer".into()),
                    Error::Expected("identifier".into()),
                    Error::Expected("[".into()),
                    Error::Expected("(".into()),
                ],
        };
        assert_eq!(result, Err(err));
    }

    #[test]
    fn expression_error_message() {
        let input = r"
,123
";
        let result = parser(expr).parse(State::new(input));
        let m = format!("{}", result.unwrap_err());
        let expected = r"Parse error at line: 2, column: 1
Unexpected ','
Expected 'integer', 'identifier', '[' or '('
";
        assert_eq!(m, expected);
    }

    fn term<I>(input: I) -> ParseResult<Expr, I>
        where I: Stream<Item = char>
    {
        fn times(l: Expr, r: Expr) -> Expr {
            Expr::Times(Box::new(l), Box::new(r))
        }
        fn plus(l: Expr, r: Expr) -> Expr {
            Expr::Plus(Box::new(l), Box::new(r))
        }
        let mul = char('*').map(|_| times);
        let add = char('+').map(|_| plus);
        let factor = chainl1(parser(expr), mul);
        chainl1(factor, add).parse_state(input)
    }

    #[test]
    fn operators() {
        let input = r"
1 * 2 + 3 * test
";
        let (result, _) = parser(term)
            .parse(State::new(input))
            .unwrap();

        let e1 = Expr::Times(Box::new(Expr::Int(1)), Box::new(Expr::Int(2)));
        let e2 = Expr::Times(Box::new(Expr::Int(3)),
                             Box::new(Expr::Id("test".to_string())));
        assert_eq!(result, Expr::Plus(Box::new(e1), Box::new(e2)));
    }


    fn follow(input: State<&str>) -> ParseResult<(), State<&str>> {
        match input.clone().uncons() {
            Ok(c) => {
                if c.is_alphanumeric() {
                    let e = Error::Unexpected(c.into());
                    Err(Consumed::Empty(ParseError::new(input.position(), e)))
                } else {
                    Ok(((), Consumed::Empty(input)))
                }
            }
            Err(_) => Ok(((), Consumed::Empty(input))),
        }
    }
    #[test]
    fn error_position() {
        let mut p = string("let")
            .skip(parser(follow))
            .map(|x| x.to_string())
            .or(many1(digit()));
        match p.parse(State::new("le123")) {
            Ok(_) => assert!(false),
            Err(err) => {
                assert_eq!(err.position,
                           SourcePosition {
                               line: 1,
                               column: 1,
                           })
            }
        }
        match p.parse(State::new("let1")) {
            Ok(_) => assert!(false),
            Err(err) => {
                assert_eq!(err.position,
                           SourcePosition {
                               line: 1,
                               column: 4,
                           })
            }
        }
    }

    #[test]
    fn sep_by_error_consume() {
        let mut p = sep_by::<Vec<_>, _, _>(string("abc"), char(','));
        let err = p.parse(State::new("ab,abc"))
            .map(|x| format!("{:?}", x))
            .unwrap_err();
        assert_eq!(err.position,
                   SourcePosition {
                       line: 1,
                       column: 1,
                   });
    }

    #[test]
    fn optional_error_consume() {
        let mut p = optional(string("abc"));
        let err = p.parse(State::new("ab"))
            .map(|x| format!("{:?}", x))
            .unwrap_err();
        assert_eq!(err.position,
                   SourcePosition {
                       line: 1,
                       column: 1,
                   });
    }
    #[test]
    fn chainl1_error_consume() {
        fn first<T, U>(t: T, _: U) -> T {
            t
        }
        let mut p = chainl1(string("abc"), char(',').map(|_| first));
        assert!(p.parse("abc,ab").is_err());
    }

    #[test]
    fn inner_error_consume() {
        let mut p = many::<Vec<_>, _>(between(char('['), char(']'), digit()));
        let result = p.parse(State::new("[1][2][]"));
        assert!(result.is_err(), format!("{:?}", result));
        let error = result.map(|x| format!("{:?}", x))
            .unwrap_err();
        assert_eq!(error.position,
                   SourcePosition {
                       line: 1,
                       column: 8,
                   });
    }

    #[test]
    fn infinite_recursion_in_box_parser() {
        let _: Result<(Vec<_>, _), _> = (many(Box::new(digit()))).parse("1");
    }

    #[test]
    fn unsized_parser() {
        let mut parser: Box<Parser<Input = &str, Output = char>> = Box::new(digit());
        let borrow_parser = &mut *parser;
        assert_eq!(borrow_parser.parse("1"), Ok(('1', "")));
    }

    #[test]
    fn choice_strings() {
        let mut fruits = [try(string("Apple")),
                          try(string("Banana")),
                          try(string("Cherry")),
                          try(string("Date")),
                          try(string("Fig")),
                          try(string("Grape"))];
        let mut parser = choice(&mut fruits);
        assert_eq!(parser.parse("Apple"), Ok(("Apple", "")));
        assert_eq!(parser.parse("Banana"), Ok(("Banana", "")));
        assert_eq!(parser.parse("Cherry"), Ok(("Cherry", "")));
        assert_eq!(parser.parse("DateABC"), Ok(("Date", "ABC")));
        assert_eq!(parser.parse("Fig123"), Ok(("Fig", "123")));
        assert_eq!(parser.parse("GrapeApple"), Ok(("Grape", "Apple")));
    }

    #[test]
    fn std_error() {
        use std::fmt;
        use std::error::Error as StdError;
        #[derive(Debug)]
        struct Error;
        impl fmt::Display for Error {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "error")
            }
        }
        impl StdError for Error {
            fn description(&self) -> &str {
                "error"
            }
        }
        let result: Result<((), _), ParseError<&str>> = string("abc")
            .and_then(|_| Err(Error))
            .parse("abc");
        assert!(result.is_err());
        // Test that ParseError can be coerced to a StdError
        let _ = result.map_err(|err| {
            let err: Box<StdError> = Box::new(err);
            err
        });
    }
}

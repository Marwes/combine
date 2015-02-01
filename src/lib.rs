#![unstable]
#![feature(core, collections, unicode)]
#![cfg_attr(test, feature(test))]

//!This crate contains parser combinators, roughly based on the Haskell library [parsec](http://hackage.haskell.org/package/parsec).
//!
//!A parser in this library can be described as a function which takes some input and if it
//!is succesful, returns a value together with the remaining input.
//!A parser combinator is a function which takes one or more parsers and returns a new parser.
//!For instance the `many` parser can be used to convert a parser for single digits into one that
//!parses multiple digits.
//!
//!# Examples:
//!
//!```
//! extern crate "parser-combinators" as parser_combinators;
//! use parser_combinators::{spaces, many1, sep_by, digit, satisfy, Parser, ParserExt, ParseError};
//! 
//! fn main() {
//!     let input = "1234, 45,78";
//!     let spaces = spaces();
//!     let integer = spaces.clone()//Parse spaces first and use the with method to only keep the result of the next parser
//!         .with(many1(digit()).map(|string: String| string.parse::<i32>().unwrap()));//parse a string of digits into an i32
//!     //Parse integers separated by commas, skipping whitespace
//!     let mut integer_list = sep_by(integer, spaces.skip(satisfy(|c| c == ',')));
//! 
//!     //Call parse with the input to execute the parser
//!     let result: Result<(Vec<i32>, &str), ParseError> = integer_list.parse(input);
//!     match result {
//!         Ok((value, _remaining_input)) => println!("{:?}", value),
//!         Err(err) => println!("{}", err)
//!     }
//! }
//!```
//!
//!If we need a parser that is mutually recursive we can define a free function which internally
//!can in turn be used as a parser (Note that we need to explicitly cast the function, this should
//!not be necessary once changes in rustc to make orphan checking less restrictive gets implemented)
//!
//!`expr` is written fully general here which may not be necessary in a specific implementation
//!The `Stream` trait is predefined to work with array slices, string slices and iterators
//!meaning that in this case it could be defined as
//!`fn expr(input: State<&str>) -> ParseResult<Expr, &str>`
//!
//!```
//! extern crate "parser-combinators" as parser_combinators;
//! use parser_combinators::{between, spaces, many1, sep_by, satisfy, Parser, ParserExt,
//! ParseResult};
//! use parser_combinators::primitives::{State, Stream};
//!
//! #[derive(Debug, PartialEq)]
//! enum Expr {
//!     Id(String),
//!     Array(Vec<Expr>),
//! }
//! fn expr<I>(input: State<I>) -> ParseResult<Expr, I>
//!     where I: Stream<Item=char> {
//!     let word = many1(satisfy(|c| c.is_alphabetic()));
//!     let comma_list = sep_by(expr as fn (_) -> _, satisfy(|c| c == ','));
//!     let array = between(satisfy(|c| c == '['), satisfy(|c| c == ']'), comma_list);
//!     let spaces = spaces();
//!     spaces.clone().with(
//!             word.map(Expr::Id)
//!             .or(array.map(Expr::Array))
//!         ).parse_state(input)
//! }
//! 
//! fn main() {
//!     let result = (expr as fn (_) -> _)
//!         .parse("[[], hello, [world]]");
//!     let expr = Expr::Array(vec![
//!           Expr::Array(Vec::new())
//!         , Expr::Id("hello".to_string())
//!         , Expr::Array(vec![Expr::Id("world".to_string())])
//!     ]);
//!     assert_eq!(result, Ok((expr, "")));
//! }
//!```

#[cfg(test)]
extern crate test;

#[doc(inline)]
pub use primitives::{Parser, ParseResult, ParseError};
#[doc(inline)]
pub use char::{
    any_char,
    digit,
    space,
    spaces,
    newline,
    crlf,
    tab,
    upper,
    lower,
    letter,
    alpha_num,
    hex_digit,
    oct_digit,
    string,
    satisfy,
};
#[doc(inline)]
pub use combinator::{
    between,
    chainl1,
    many,
    many1,
    optional,
    sep_by,
    try,
    value,
    unexpected,
    not_followed_by,

    ParserExt
};

macro_rules! static_fn {
    (($($arg: pat, $arg_ty: ty),*) -> $ret: ty { $body: expr }) => { { fn temp($($arg: $arg_ty),*) -> $ret { $body } temp } }
}

///Module containing the primitive types which is used to create and compose more advanced parsers
pub mod primitives;
///Module containing all specific parsers
pub mod combinator;
///Module containg parsers specialized on character streams
pub mod char;

#[cfg(test)]
mod tests {
    use super::*;
    use super::primitives::{SourcePosition, State, Stream, Error, Consumed};
    

    fn integer<'a, I>(input: State<I>) -> ParseResult<i64, I>
        where I: Stream<Item=char> {
        let (s, input) = try!(many1::<String, _>(digit())
            .parse_state(input));
        let mut n = 0;
        for c in s.chars() {
            n = n * 10 + (c as i64 - '0' as i64);
        }
        Ok((n, input))
    }

    #[test]
    fn test_integer() {
        let result = (integer as fn(_) -> _).parse("123");
        assert_eq!(result, Ok((123i64, "")));
    }
    #[test]
    fn list() {
        let mut p = sep_by(integer as fn(_) -> _, satisfy(|c| c == ','));
        let result = p.parse("123,4,56");
        assert_eq!(result, Ok((vec![123, 4, 56], "")));
    }
    #[test]
    fn iterator() {
        let result = (integer as fn(_) -> _).parse("123".chars())
            .map(|(i, mut input)| (i, input.next()));
        assert_eq!(result, Ok((123i64, None)));
    }
    #[test]
    fn field() {
        let word = many(satisfy(|c| c.is_alphanumeric()));
        let word2 = many(satisfy(|c| c.is_alphanumeric()));
        let spaces = spaces();
        let c_decl = word
            .skip(spaces.clone())
            .skip(satisfy(|c| c == ':'))
            .skip(spaces)
            .and(word2)
            .parse("x: int");
        assert_eq!(c_decl, Ok((("x".to_string(), "int".to_string()), "")));
    }
    #[test]
    fn source_position() {
        let source =
r"
123
";
        let result = spaces()
            .with(integer as fn(_) -> _)
            .skip(spaces())
            .parse_state(State::new(source));
        let state = Consumed::Consumed(State {
            position: SourcePosition { line: 3, column: 1 },
            input: ""
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
    fn expr(input: State<&str>) -> ParseResult<Expr, &str> {
        let word = many1(satisfy(|c| c.is_alphabetic()));
        let integer = integer as fn (_) -> _;
        let array = between(satisfy(|c| c == '['), satisfy(|c| c == ']'), sep_by(expr as fn (_) -> _, satisfy(|c| c == ',')));
        let spaces = spaces();
        spaces.clone().with(
                word.map(Expr::Id)
                .or(integer.map(Expr::Int))
                .or(array.map(Expr::Array))
                .or(between(satisfy(|c| c == '('), satisfy(|c| c == ')'), term as fn (_) -> _))
            ).skip(spaces)
            .parse_state(input)
    }

    #[test]
    fn expression() {
        let result = sep_by(expr as fn (_) -> _, satisfy(|c| c == ','))
            .parse("int, 100, [[], 123]");
        let exprs = vec![
              Expr::Id("int".to_string())
            , Expr::Int(100)
            , Expr::Array(vec![Expr::Array(vec![]), Expr::Int(123)])
        ];
        assert_eq!(result, Ok((exprs, "")));
    }

    #[test]
    fn expression_error() {
        let input =
r"
,123
";
        let result = (expr as fn (_) -> _)
            .parse(input);
        let err = ParseError {
            position: SourcePosition { line: 2, column: 1 },
            errors: vec![Error::Unexpected(','), Error::Message("Expected digit".to_string())]
        };
        assert_eq!(result, Err(err));
    }

    fn term(input: State<&str>) -> ParseResult<Expr, &str> {

        let mul = satisfy(|c| c == '*')
            .map(|_| Box::new(|&mut:l, r| Expr::Times(Box::new(l), Box::new(r))) as Box<FnMut(_, _) -> _>);
        let add = satisfy(|c| c == '+')
            .map(|_| Box::new(|&mut:l, r| Expr::Plus(Box::new(l), Box::new(r))) as Box<FnMut(_, _) -> _>);
        let factor = chainl1(expr as fn (_) -> _, mul);
        chainl1(factor, add)
            .parse_state(input)
    }

    #[test]
    fn operators() {
        let input =
r"
1 * 2 + 3 * test
";
        let (result, _) = (term as fn (_) -> _)
            .parse(input)
            .unwrap();

        let e1 = Expr::Times(Box::new(Expr::Int(1)), Box::new(Expr::Int(2)));
        let e2 = Expr::Times(Box::new(Expr::Int(3)), Box::new(Expr::Id("test".to_string())));
        assert_eq!(result, Expr::Plus(Box::new(e1), Box::new(e2)));
    }


    fn follow(input: State<&str>) -> ParseResult<(), &str> {
        match input.clone().uncons_char() {
            Ok((c, _)) => {
                if c.is_alphanumeric() {
                    Err(Consumed::Empty(ParseError::new(input.position, Error::Unexpected(c))))
                }
                else {
                    Ok(((), Consumed::Empty(input)))
                }
            }
            Err(_) => Ok(((), Consumed::Empty(input)))
        }
    }
    #[test]
    fn error_position() {
        let mut p = string("let").skip(follow as fn (_) -> _).map(|x| x.to_string())
            .or(many1(satisfy(|c| c.is_digit(10))));
        match p.parse("le123") {
            Ok(_) => assert!(false),
            Err(err) => assert_eq!(err.position, SourcePosition { line: 1, column: 1 })
        }
    }

static LONG_EXPR: &'static str =
r"(3 * 4) + 2 * 4 * test + 4 * aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
* (a + 2 * ((476128368 + i * (((3 * 4) + 2 * 4 * test + 4 * aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
* (a + 2 * ((476128368 + i * ((476128368 + 21476)+ 21476)) + 21476)) * 2123 * 214 + (476128368 + 21476) * hello + 42 + 21476)+ 21476)) + 21476)) * 2123 * 214 + (476128368 + 21476) * hello + 42 +
(3 * 4) + 2 * 4 * test + 4 * aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
* (a + 2 * ((476128368 + i * (((3 * 4) + 2 * 4 * test + 4 * aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
* (a + 2 * ((476128368 + i * ((476128368 + 21476)+ 21476)) + 21476)) * 2123 * 214 + (476128368 + 21476) * hello + 42
+ 21476)+ 21476)) + 21476)) * 2123 * 214 + (476128368 + 21476) * hello + 42";
    #[bench]
    fn bench_expression(bench: &mut ::test::Bencher) {

        let result = (term as fn (_) -> _)
            .parse(LONG_EXPR);
        assert!(result.is_ok()); 
        assert_eq!(result.unwrap().1, "");
        bench.iter(|| {
            let result = (term as fn (_) -> _)
                .parse(LONG_EXPR);
            let _ = ::test::black_box(result);
        })
    }

    #[test]
    fn sep_by_error_consume() {
        let mut p = sep_by::<Vec<_>, _, _>(string("abc"), satisfy(|c| c == ','));
        let err = p.parse("ab,abc")
            .map(|x| format!("{:?}", x))
            .unwrap_err();
        assert_eq!(err.position, SourcePosition { line: 1, column: 1});
    }

    #[test]
    fn optional_error_consume() {
        let mut p = optional(string("abc"));
        let err = p.parse("ab")
            .map(|x| format!("{:?}", x))
            .unwrap_err();
        assert_eq!(err.position, SourcePosition { line: 1, column: 1});
    }
    #[test]
    fn chainl1_error_consume() {
        let mut p = chainl1(string("abc"), satisfy(|c| c == ',').map(|_| Box::new(|&:l, _| l) as Box<FnMut(_, _) -> _>));
        assert!(p.parse("abc,ab").is_err());
    }

    #[test]
    fn inner_error_consume() {
        let mut p = many::<Vec<_>, _>(between(string("["), string("]"), satisfy(|c| c.is_digit(10))));
        let result = p.parse("[1][2][]");
        assert!(result.is_err(), format!("{:?}", result));
        let error = result
            .map(|x| format!("{:?}", x))
            .unwrap_err();
        assert_eq!(error.position, SourcePosition { line: 1, column: 8 });
    }

    #[test]
    fn infinite_recursion_in_box_parser() {
        let _: Result<(Vec<_>, _), _> = (many(Box::new(digit())))
            .parse("1");
    }

    #[test]
    fn unsized_parser() {
        let mut parser = Box::new(digit()) as Box<Parser<Input=&str, Output=char>>;
        let borrow_parser = &mut *parser;
        assert_eq!(borrow_parser.parse("1"), Ok(('1', "")));
    }
}

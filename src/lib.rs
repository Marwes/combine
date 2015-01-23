#![allow(unstable)]
#![unstable]

#[cfg(test)]
extern crate test;

pub use primitives::{Parser, ParseResult, ParseError};
pub use parser::{
    any_char,
    between,
    chainl1,
    chars,
    chars1,
    digit,
    many,
    many1,
    optional,
    satisfy,
    sep_by,
    space,
    spaces,
    string,
    try,
    value,
    unexpected,
    not_followed_by,

    ParserExt
};

mod primitives;
mod parser;

#[cfg(test)]
mod tests {
    use super::*;
    use super::primitives::{SourcePosition, State, Stream, Error, Consumed};
    

    fn integer<'a, I>(input: State<I>) -> ParseResult<i64, I>
        where I: Stream<Item=char> {
        let (s, input) = try!(chars1(digit())
            .parse_state(input));
        let mut n = 0;
        for c in s.chars() {
            n = n * 10 + (c as i64 - '0' as i64);
        }
        Ok((n, input))
    }

    #[test]
    fn test_integer() {
        let result = (integer as fn(_) -> _).parse("123")
            .map(|(x, s)| (x, s.input));
        assert_eq!(result, Ok((123i64, "")));
    }
    #[test]
    fn list() {
        let mut p = sep_by(integer as fn(_) -> _, satisfy(|c| c == ','));
        let result = p.parse("123,4,56")
            .map(|(x, s)| (x, s.input));
        assert_eq!(result, Ok((vec![123, 4, 56], "")));
    }
    #[test]
    fn iterator() {
        let result = (integer as fn(_) -> _).parse("123".chars())
            .map(|(i, mut state)| (i, state.input.next()));
        assert_eq!(result, Ok((123i64, None)));
    }
    #[test]
    fn field() {
        let word = chars(satisfy(|c| c.is_alphanumeric()));
        let word2 = chars(satisfy(|c| c.is_alphanumeric()));
        let spaces = many(space());
        let c_decl = word
            .skip(spaces.clone())
            .skip(satisfy(|c| c == ':'))
            .skip(spaces)
            .and(word2)
            .parse("x: int")
            .map(|(x, s)| (x, s.input));
        assert_eq!(c_decl, Ok((("x".to_string(), "int".to_string()), "")));
    }
    #[test]
    fn source_position() {
        let source =
r"
123
";
        let result = many(space())
            .with(integer as fn(_) -> _)
            .skip(many(space()))
            .parse(source);
        let state = State {
            position: SourcePosition { line: 3, column: 1 },
            consumed: Consumed::Consumed,
            input: ""
        };
        assert_eq!(result, Ok((123i64, state)));
    }

    #[derive(Show, PartialEq)]
    enum Expr {
        Id(String),
        Int(i64),
        Array(Vec<Expr>),
        Plus(Box<Expr>, Box<Expr>),
        Times(Box<Expr>, Box<Expr>),
    }
    fn expr(input: State<&str>) -> ParseResult<Expr, &str> {
        let word = chars1(satisfy(|c| c.is_alphabetic()));
        let integer = integer as fn (_) -> _;
        let array = between(satisfy(|c| c == '['), satisfy(|c| c == ']'), sep_by(expr as fn (_) -> _, satisfy(|c| c == ',')));
        let spaces = many(space());
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
            .parse("int, 100, [[], 123]")
            .map(|(x, s)| (x, s.input));
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
            consumed: Consumed::Consumed,
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
                    Err(ParseError::new(input.position, Consumed::Empty, Error::Unexpected(c)))
                }
                else {
                    Ok(((), input))
                }
            }
            Err(_) => Ok(((), input))
        }
    }
    #[test]
    fn error_position() {
        let mut p = string("let").skip(follow as fn (_) -> _).map(|x| x.to_string())
            .or(chars1(satisfy(|c| c.is_digit(10))));
        match p.parse("le123") {
            Ok(_) => assert!(false),
            Err(err) => assert_eq!(err.position, SourcePosition { line: 1, column: 1 })
        }
    }

    #[test]
    fn try_parser() {
        let mut p = try(string("let").skip(follow as fn (_) -> _)).map(|x| x.to_string())
            .or(chars1(satisfy(CharExt::is_alphabetic)));
        let result = p.parse("lex  ").map(|x| x.0);
        assert_eq!(result, Ok("lex".to_string()));
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
        assert_eq!(result.unwrap().1.input, "");
        bench.iter(|| {
            let result = (term as fn (_) -> _)
                .parse(LONG_EXPR);
            let _ = ::test::black_box(result);
        })
    }

    #[test]
    fn sep_by_error_consume() {
        let mut p = sep_by(string("abc"), satisfy(|c| c == ','));
        let err = p.parse("ab,abc").unwrap_err();
        assert_eq!(err.position, SourcePosition { line: 1, column: 1});
    }

    #[test]
    fn optional_error_consume() {
        let mut p = optional(string("abc"));
        let err = p.parse("ab").unwrap_err();
        assert_eq!(err.position, SourcePosition { line: 1, column: 1});
    }
    #[test]
    fn chainl1_error_consume() {
        let mut p = chainl1(string("abc"), satisfy(|c| c == ',').map(|_| Box::new(|&:l, _| l) as Box<FnMut(_, _) -> _>));
        assert!(p.parse("abc,ab").is_err());
    }

    #[test]
    fn inner_error_consume() {
        let mut p = many(between(string("["), string("]"), satisfy(|c| c.is_digit(10))));
        let result = p.parse("[1][2][]");
        assert!(result.is_err(), format!("{:?}", result));
        let error = result.unwrap_err();
        assert_eq!(error.consumed, Consumed::Consumed);
        assert_eq!(error.position, SourcePosition { line: 1, column: 8 });
    }
}

#![feature(test)]
extern crate parser_combinators as pc;
extern crate test;

use std::collections::HashMap;
use std::io::Read;
use std::fs::File;
use std::path::Path;

use pc::primitives::{Parser, State, Stream, ParseResult};
use pc::combinator::{between, many, many1, optional, parser, sep_by, unexpected, With, ParserExt};
use pc::char::{any_char, char, digit, satisfy, spaces, Spaces, string};

#[derive(PartialEq, Debug)]
enum Value {
    Number(f64),
    String(String),
    Bool(bool),
    Null,
    Object(HashMap<String, Value>),
    Array(Vec<Value>)
}

fn lex<'a, P>(p: P) -> With<Spaces<P::Input>, P>
    where P: Parser
        , P::Input: Stream<Item=char> {
    spaces().with(p)
}
struct Json<I>(::std::marker::PhantomData<fn (I) -> I>);

impl <I> Json<I>
    where I: Stream<Item=char> {

    fn integer(input: State<I>) -> ParseResult<i64, I> {
        let (s, input) = try!(many1::<String, _>(digit())
            .expected("integer")
            .parse_state(input));
        let mut n = 0;
        for c in s.chars() {
            n = n * 10 + (c as i64 - '0' as i64);
        }
        Ok((n, input))
    }

    fn number(input: State<I>) -> ParseResult<f64, I> {
        let i = char('0').map(|_| 0.0)
                 .or(parser(Json::<I>::integer).map(|x| x as f64));
        let fractional = many(digit())
            .map(|digits: String| {
                let mut magnitude = 1.0;
                digits.chars().fold(0.0, |acc, d| {
                    magnitude /= 10.0;
                    match d.to_digit(10) {
                        Some(d) => acc + (d as f64) * magnitude,
                        None => panic!("Not a digit")
                    }
                })
            });

        let exp = satisfy(|c| c == 'e' || c == 'E')
            .with(optional(char('-')).and(parser(Json::<I>::integer)));
        optional(char('-'))
            .and(i)
            .map(|(sign, n)| if sign.is_some() { -n } else { n })
            .and(optional(char('.')).with(fractional))
            .map(|(x, y)| if x > 0.0 { x + y } else { x - y })
            .and(optional(exp))
            .map(|(n, exp_option)| {
                match exp_option {
                    Some((sign, e)) => {
                        let e = if sign.is_some() { -e } else { e };
                        n * 10.0f64.powi(e as i32)
                    }
                    None => n
                }
            })
        .parse_state(input)
    }

    fn char(input: State<I>) -> ParseResult<char, I> {
        let (c, input) = try!(any_char().parse_state(input));
        let mut back_slash_char = satisfy(|c| "\"\\/bfnrt".chars().find(|x| *x == c).is_some()).map(|c| {
            match c {
                '"' => '"',
                '\\' => '\\',
                '/' => '/',
                'b' => '\u{0008}',
                'f' => '\u{000c}',
                'n' => '\n',
                'r' => '\r',
                't' => '\t',
                c => c//Should never happen
            }
        });
        match c {
            '\\' => input.combine(|input| back_slash_char.parse_state(input)),
            '"'  => unexpected("\"").parse_state(input.into_inner()).map(|_| unreachable!()),
            _    => Ok((c, input))
        }
    }
    fn string(input: State<I>) -> ParseResult<String, I> {
        between(char('"'), char('"'), many(parser(Json::<I>::char)))
            .parse_state(input)
    }
    fn object(input: State<I>) -> ParseResult<Value, I> {
        let field = (lex(parser(Json::<I>::string)), lex(char(':')), lex(parser(Json::<I>::value)))
            .map(|t| (t.0, t.1);
        let fields = sep_by(field, char(','));
        between(char('{'), lex(char('}')), fields)
            .map(Value::Object)
            .parse_state(input)
    }

    #[allow(unconditional_recursion)]
    fn value(input: State<I>) -> ParseResult<Value, I>
        where I: Stream<Item=char> {
        let array = between(lex(char('[')), lex(char(']')), sep_by(parser(Json::<I>::value), char(',')))
            .map(Value::Array);

        //Wrap a few of the value parsers to workaround the slow compiletimes
        fn rest<I>(input: State<I>) -> ParseResult<Value, I>
            where I: Stream<Item=char> {
            string("false").map(|_| Value::Bool(false))
                .or(string("true").map(|_| Value::Bool(true)))
                .or(string("null").map(|_| Value::Null))
                .parse_state(input)
        }
        lex(parser(Json::<I>::string).map(Value::String)
            .or(parser(Json::<I>::object))
            .or(array)
            .or(parser(Json::<I>::number).map(Value::Number))
            .or(parser(rest))
        )
            .parse_state(input)
    }

}

#[test]
fn json_test() {
    use self::Value::*;
    let input =
r#"
{
    "array": [1, ""],
    "object": {},
    "number": 3.14,
    "int": -100,
    "exp": -1e2,
    "exp_neg": 23e-2,
    "true": true,
    "false"  : false,
    "null" : null
}"#;
    let result = parser(Json::value)
        .parse(input);
    let expected = Object(vec![
        ("array", Array(vec![Number(1.0), String("".to_string())])),
        ("object", Object(HashMap::new())),
        ("number", Number(3.14)),
        ("int", Number(-100.)),
        ("exp", Number(-1e2)),
        ("exp_neg", Number(23E-2)),
        ("true", Bool(true)),
        ("false", Bool(false)),
        ("null", Null)
    ].into_iter().map(|(k, v)| (k.to_string(), v)).collect());
    match result {
        Ok(result) => assert_eq!(result, (expected, "")),
        Err(e) => {
            println!("{}", e);
            assert!(false);
        }
    }
}

#[bench]
fn bench_json(bencher: &mut ::test::Bencher) {
    let mut data = String::new();
    File::open(&Path::new(&"benches/data.json"))
        .and_then(|mut file| file.read_to_string(&mut data))
        .unwrap();
    let mut parser = parser(Json::value);
    match parser.parse(&data[..]) {
        Ok((Value::Array(_), "\r\n")) => (),
        Ok(x) => { println!("{:?}", x); assert!(false); }
        Err(err) => { println!("{}", err); assert!(false); }
    }
    bencher.iter(|| {
        let result = parser.parse(&data);
        ::test::black_box(result)
    });
}

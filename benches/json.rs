#![feature(unicode, path, test, io, fs)]
extern crate "parser-combinators" as pc;
extern crate test;

use std::collections::HashMap;
use std::num::Float;
use std::io::Read;
use std::fs::File;
use std::path::Path;

use pc::primitives::{Parser, State, ParseResult};
use pc::combinator::{between, many, many1, optional, sep_by, With, ParserExt};
use pc::char::{digit, satisfy, spaces, Spaces, string};

#[derive(PartialEq, Debug)]
enum Value {
    Number(f64),
    String(String),
    Bool(bool),
    Null,
    Object(HashMap<String, Value>),
    Array(Vec<Value>)
}

fn lex<'a, P>(p: P) -> With<Spaces<&'a str>, P>
    where P: Parser<Input=&'a str> {
    spaces().with(p)
}

fn integer(input: State<&str>) -> ParseResult<i64, &str> {
    let (s, input) = try!(many1::<String, _>(digit())
        .expected("integer")
        .parse_state(input));
    let mut n = 0;
    for c in s.chars() {
        n = n * 10 + (c as i64 - '0' as i64);
    }
    Ok((n, input))
}

fn number(input: State<&str>) -> ParseResult<f64, &str> {
    let i = satisfy(|c| c == '0').map(|_| 0.0)
             .or((integer as fn (_) -> _).map(|x| x as f64));
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
        .with(optional(string("-")).and(integer as fn (_) -> _));
    optional(string("-"))
        .and(i)
        .map(|(sign, n)| if sign.is_some() { -n } else { n })
        .and(optional(string(".")).with(fractional))
        .map(|(x, y)| if x > 0.0 { x + y } else { x - y })
        .and(optional(exp))
        .map(|(n, exp_option)| {
            match exp_option {
                Some((sign, e)) => {
                    let e = if sign.is_some() { -e } else { e };
                    n * 10.0.powi(e as i32)
                }
                None => n
            }
        })
    .parse_state(input)
}

fn json_char(input: State<&str>) -> ParseResult<char, &str> {
    let back_slash_char = string("\\")
        .with(satisfy(|c| "\"\\/bfnrt".chars().find(|x| *x == c).is_some()).map(|c| {
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
        }));
    satisfy(|c| "\"\\".chars().find(|x| *x == c).is_none())
        .or(back_slash_char)
        .parse_state(input)
}
fn json_string(input: State<&str>) -> ParseResult<String, &str> {
    between(string("\""), string("\""), many(json_char as fn (_) -> _))
        .parse_state(input)
}
fn object(input: State<&str>) -> ParseResult<Value, &str> {
    let field = lex(json_string as fn (_) -> _)
        .skip(lex(string(":")))
        .and(lex(json_value as fn (_) -> _));
    let fields = sep_by(field, string(","));
    between(string("{"), lex(string("}")), fields)
        .map(Value::Object)
        .parse_state(input)
}


fn json_value(input: State<&str>) -> ParseResult<Value, &str> {
    let array = between(string("["), lex(string("]")), sep_by(json_value as fn (_) -> _, string(",")))
        .map(Value::Array);

    //Wrap a few of the value parsers to workaround the slow compiletimes
    fn rest(input: State<&str>) -> ParseResult<Value, &str> {
        string("false").map(|_| Value::Bool(false))
            .or(string("true").map(|_| Value::Bool(true)))
            .or(string("null").map(|_| Value::Null))
            .parse_state(input)
    }
    lex(array
        .or(object as fn (_) -> _)
        .or((number as fn (_) -> _).map(Value::Number))
        .or((json_string as fn (_) -> _).map(Value::String))
        .or(rest as fn (_) -> _)
    )
        .parse_state(input)
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
    let result = (json_value as fn (_) -> _)
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
    let mut parser = json_value as fn (_) -> _;
    match parser.parse(&data) {
        Ok((Value::Array(_), "\r\n")) => (),
        Ok(x) => { println!("{:?}", x); assert!(false); }
        Err(err) => { println!("{}", err); assert!(false); }
    }
    bencher.iter(|| {
        let result = parser.parse(&data);
        ::test::black_box(result)
    });
}

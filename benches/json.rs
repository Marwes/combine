#![feature(test)]
extern crate combine as pc;
extern crate test;

use std::collections::HashMap;
use std::io::Read;
use std::fs::File;
use std::path::Path;

use pc::primitives::{Consumed, Parser, ParseError, ParseResult, State, Stream, BufferedStream};
use pc::combinator::{any, between, choice, many, many1, optional, parser, satisfy, sep_by,
                     Expected, FnParser, Skip};
use pc::char::{char, digit, spaces, Spaces, string};
use pc::from_iter;

#[derive(PartialEq, Debug)]
enum Value {
    Number(f64),
    String(String),
    Bool(bool),
    Null,
    Object(HashMap<String, Value>),
    Array(Vec<Value>),
}

fn lex<'a, P>(p: P) -> Skip<P, Spaces<P::Input>>
    where P: Parser,
          P::Input: Stream<Item = char>
{
    p.skip(spaces())
}
struct Json<I>(::std::marker::PhantomData<fn(I) -> I>);

type JsonParser<O, I> = Expected<FnParser<I, fn(I) -> ParseResult<O, I>>>;

fn fn_parser<O, I>(f: fn(I) -> ParseResult<O, I>, err: &'static str) -> JsonParser<O, I>
    where I: Stream<Item = char>
{
    parser(f).expected(err)
}

impl<I> Json<I>
    where I: Stream<Item = char>
{
    fn integer() -> JsonParser<i64, I> {
        fn_parser(Json::<I>::integer_, "integer")
    }
    fn integer_(input: I) -> ParseResult<i64, I> {
        let (s, input) = try!(lex(many1::<String, _>(digit())).parse_lazy(input).into());
        let mut n = 0;
        for c in s.chars() {
            n = n * 10 + (c as i64 - '0' as i64);
        }
        Ok((n, input))
    }

    fn number() -> JsonParser<f64, I> {
        fn_parser(Json::<I>::number_, "number")
    }
    fn number_(input: I) -> ParseResult<f64, I> {
        let i = char('0')
            .map(|_| 0.0)
            .or(Json::<I>::integer().map(|x| x as f64));
        let fractional = many(digit()).map(|digits: String| {
            let mut magnitude = 1.0;
            digits.chars().fold(0.0, |acc, d| {
                magnitude /= 10.0;
                match d.to_digit(10) {
                    Some(d) => acc + (d as f64) * magnitude,
                    None => panic!("Not a digit"),
                }
            })
        });

        let exp = satisfy(|c| c == 'e' || c == 'E')
            .with(optional(char('-')).and(Json::<I>::integer()));
        lex(optional(char('-'))
                .and(i)
                .map(|(sign, n)| { if sign.is_some() { -n } else { n } })
                .and(optional(char('.')).with(fractional))
                .map(|(x, y)| { if x > 0.0 { x + y } else { x - y } })
                .and(optional(exp))
                .map(|(n, exp_option)| {
                    match exp_option {
                        Some((sign, e)) => {
                            let e = if sign.is_some() { -e } else { e };
                            n * 10.0f64.powi(e as i32)
                        }
                        None => n,
                    }
                }))
            .parse_lazy(input)
            .into()
    }

    fn char() -> JsonParser<char, I> {
        fn_parser(Json::<I>::char_, "char")
    }
    fn char_(input: I) -> ParseResult<char, I> {
        let (c, input) = try!(any().parse_lazy(input).into());
        let mut back_slash_char = satisfy(|c| "\"\\/bfnrt".chars().find(|x| *x == c).is_some())
            .map(|c| {
                match c {
                    '"' => '"',
                    '\\' => '\\',
                    '/' => '/',
                    'b' => '\u{0008}',
                    'f' => '\u{000c}',
                    'n' => '\n',
                    'r' => '\r',
                    't' => '\t',
                    c => c,//Should never happen
                }
            });
        match c {
            '\\' => input.combine(|input| back_slash_char.parse_state(input)),
            '"' => {
                Err(Consumed::Empty(ParseError::from_errors(input.into_inner().position(),
                                                            Vec::new())))
            }
            _ => Ok((c, input)),
        }
    }
    fn string() -> JsonParser<String, I> {
        fn_parser(Json::<I>::string_, "string")
    }
    fn string_(input: I) -> ParseResult<String, I> {
        between(char('"'), lex(char('"')), many(Json::<I>::char())).parse_lazy(input).into()
    }

    fn object() -> JsonParser<Value, I> {
        fn_parser(Json::<I>::object_, "object")
    }
    fn object_(input: I) -> ParseResult<Value, I> {
        let field = (Json::<I>::string(), lex(char(':')), Json::<I>::value()).map(|t| (t.0, t.2));
        let fields = sep_by(field, lex(char(',')));
        between(lex(char('{')), lex(char('}')), fields)
            .map(Value::Object)
            .parse_lazy(input)
            .into()
    }

    fn value() -> FnParser<I, fn(I) -> ParseResult<Value, I>> {
        parser({
            let f: fn(_) -> _ = Json::<I>::value_;
            f
        })
    }
    #[allow(unconditional_recursion)]
    fn value_(input: I) -> ParseResult<Value, I> {
        let mut array = between(lex(char('[')),
                                lex(char(']')),
                                sep_by(Json::<I>::value(), lex(char(','))))
            .map(Value::Array);

        choice::<[&mut Parser<Input = I, Output = Value>; 7], _>([&mut Json::<I>::string()
                                                                      .map(Value::String),
                                                                  &mut Json::<I>::object(),
                                                                  &mut array,
                                                                  &mut Json::<I>::number()
                                                                      .map(Value::Number),
                                                                  &mut lex(string("false")
                                                                      .map(|_| {
                                                                          Value::Bool(false)
                                                                      })),
                                                                  &mut lex(string("true")
                                                                      .map(|_| Value::Bool(true))),
                                                                  &mut lex(string("null")
                                                                      .map(|_| Value::Null))])
            .parse_lazy(input)
            .into()
    }
}

#[test]
fn json_test() {
    use self::Value::*;
    let input = r#"
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
    let result = Json::value().parse(input);
    let expected = Object(vec![("array", Array(vec![Number(1.0), String("".to_string())])),
                               ("object", Object(HashMap::new())),
                               ("number", Number(3.14)),
                               ("int", Number(-100.)),
                               ("exp", Number(-1e2)),
                               ("exp_neg", Number(23E-2)),
                               ("true", Bool(true)),
                               ("false", Bool(false)),
                               ("null", Null)]
        .into_iter()
        .map(|(k, v)| (k.to_string(), v))
        .collect());
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
    let mut parser = Json::value();
    match parser.parse(State::new(&data[..])) {
        Ok((Value::Array(_), _)) => (),
        Ok(_) => assert!(false),
        Err(err) => {
            println!("{}", err);
            assert!(false);
        }
    }
    bencher.iter(|| {
        let result = parser.parse(State::new(&data[..]));
        ::test::black_box(result)
    });
}

#[bench]
fn bench_buffered_json(bencher: &mut ::test::Bencher) {
    let mut data = String::new();
    File::open(&Path::new(&"benches/data.json"))
        .and_then(|mut file| file.read_to_string(&mut data))
        .unwrap();
    bencher.iter(|| {
        let buffer = BufferedStream::new(from_iter(data.chars()), 1);
        let mut parser = Json::value();
        match parser.parse(State::new(buffer.as_stream())) {
            Ok((Value::Array(v), _)) => {
                ::test::black_box(v);
            }
            Ok(_) => assert!(false),
            Err(err) => {
                println!("{}", err);
                assert!(false);
            }
        }
    });
}

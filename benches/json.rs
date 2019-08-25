// `impl Trait` is not required for this parser but we use to to show that it can be used to
// significantly simplify things

#[macro_use]
extern crate criterion;

#[macro_use]
extern crate combine;

use std::collections::HashMap;
use std::fs::File;
use std::io::Read;
use std::path::Path;

use criterion::{black_box, Bencher, Criterion};

use combine::error::{Consumed, ParseError};
use combine::stream::buffered;
use combine::{Parser, Stream, StreamOnce};

use combine::parser::char::{char, digit, spaces, string};
use combine::parser::choice::{choice, optional};
use combine::parser::function::parser;
use combine::parser::item::{any, satisfy, satisfy_map};
use combine::parser::repeat::{many, many1, sep_by};
use combine::parser::sequence::between;

use combine::stream::state::{SourcePosition, State};
use combine::stream::IteratorStream;

#[derive(PartialEq, Debug)]
enum Value {
    Number(f64),
    String(String),
    Bool(bool),
    Null,
    Object(HashMap<String, Value>),
    Array(Vec<Value>),
}

fn lex<P>(p: P) -> impl Parser< Input, Output = P::Output>
where
    P: Parser<Input>,
    Input: Stream<Item = char>,
    <Input as StreamOnce>::Error: ParseError<
        <Input as StreamOnce>::Item,
        <Input as StreamOnce>::Range,
        <Input as StreamOnce>::Position,
    >,
{
    p.skip(spaces())
}

fn integer<Input>() -> impl Parser< Input, Output = i64>
where
    Input: Stream<Item = char>,
    Input::Error: ParseError<Input::Item, Input::Range, Input::Position>,
{
    lex(many1(digit()))
        .map(|s: String| {
            let mut n = 0;
            for c in s.chars() {
                n = n * 10 + (c as i64 - '0' as i64);
            }
            n
        })
        .expected("integer")
}

fn number<Input>() -> impl Parser< Input, Output = f64>
where
    Input: Stream<Item = char>,
    Input::Error: ParseError<Input::Item, Input::Range, Input::Position>,
{
    let i = char('0').map(|_| 0.0).or(integer().map(|x| x as f64));
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

    let exp = satisfy(|c| c == 'e' || c == 'E').with(optional(char('-')).and(integer()));
    lex(optional(char('-'))
        .and(i)
        .map(|(sign, n)| if sign.is_some() { -n } else { n })
        .and(optional(char('.')).with(fractional))
        .map(|(x, y)| if x >= 0.0 { x + y } else { x - y })
        .and(optional(exp))
        .map(|(n, exp_option)| match exp_option {
            Some((sign, e)) => {
                let e = if sign.is_some() { -e } else { e };
                n * 10.0f64.powi(e as i32)
            }
            None => n,
        }))
    .expected("number")
}

fn json_char<Input>() -> impl Parser< Input, Output = char>
where
    Input: Stream<Item = char>,
    Input::Error: ParseError<Input::Item, Input::Range, Input::Position>,
{
    parser(|input: &mut Input| {
        let (c, consumed) = r#try!(any().parse_lazy(input).into());
        let mut back_slash_char = satisfy_map(|c| {
            Some(match c {
                '"' => '"',
                '\\' => '\\',
                '/' => '/',
                'b' => '\u{0008}',
                'f' => '\u{000c}',
                'n' => '\n',
                'r' => '\r',
                't' => '\t',
                _ => return None,
            })
        });
        match c {
            '\\' => consumed.combine(|_| back_slash_char.parse_stream(input).into_result()),
            '"' => Err(Consumed::Empty(Input::Error::empty(input.position()).into())),
            _ => Ok((c, consumed)),
        }
    })
}

fn json_string<Input>() -> impl Parser< Input, Output = String>
where
    Input: Stream<Item = char>,
    Input::Error: ParseError<Input::Item, Input::Range, Input::Position>,
{
    between(char('"'), lex(char('"')), many(json_char())).expected("string")
}

fn object<Input>() -> impl Parser< Input, Output = Value>
where
    Input: Stream<Item = char>,
    Input::Error: ParseError<Input::Item, Input::Range, Input::Position>,
{
    let field = (json_string(), lex(char(':')), json_value()).map(|t| (t.0, t.2));
    let fields = sep_by(field, lex(char(',')));
    between(lex(char('{')), lex(char('}')), fields)
        .map(Value::Object)
        .expected("object")
}

#[inline]
fn json_value<Input>() -> impl Parser< Input, Output = Value>
where
    Input: Stream<Item = char>,
    Input::Error: ParseError<Input::Item, Input::Range, Input::Position>,
{
    json_value_()
}

// We need to use `parser!` to break the recursive use of `value` to prevent the returned parser
// from containing itself
parser! {
    #[inline]
    fn json_value_[Input]()(Input) -> Value
        where [ Input: Stream<Item = char> ]
    {
        let array = between(
            lex(char('[')),
            lex(char(']')),
            sep_by(json_value(), lex(char(','))),
        ).map(Value::Array);

        choice((
            json_string().map(Value::String),
            object(),
            array,
            number().map(Value::Number),
            lex(string("false").map(|_| Value::Bool(false))),
            lex(string("true").map(|_| Value::Bool(true))),
            lex(string("null").map(|_| Value::Null)),
        ))
    }
}

#[test]
fn json_test() {
    use self::Value::*;
    let input = r#"{
    "array": [1, ""],
    "object": {},
    "number": 3.14,
    "small_number": 0.59,
    "int": -100,
    "exp": -1e2,
    "exp_neg": 23e-2,
    "true": true,
    "false"  : false,
    "null" : null
}"#;
    let result = json_value().easy_parse(input);
    let expected = Object(
        vec![
            ("array", Array(vec![Number(1.0), String("".to_string())])),
            ("object", Object(HashMap::new())),
            ("number", Number(3.14)),
            ("small_number", Number(0.59)),
            ("int", Number(-100.)),
            ("exp", Number(-1e2)),
            ("exp_neg", Number(23E-2)),
            ("true", Bool(true)),
            ("false", Bool(false)),
            ("null", Null),
        ]
        .into_iter()
        .map(|(k, v)| (k.to_string(), v))
        .collect(),
    );
    match result {
        Ok(result) => assert_eq!(result, (expected, "")),
        Err(e) => {
            println!("{}", e);
            assert!(false);
        }
    }
}

fn test_data() -> String {
    let mut data = String::new();
    File::open(&Path::new(&"benches/data.json"))
        .and_then(|mut file| file.read_to_string(&mut data))
        .unwrap();
    data
}

fn bench_json(bencher: &mut Bencher) {
    let data = test_data();
    let mut parser = json_value();
    match parser.easy_parse(State::new(&data[..])) {
        Ok((Value::Array(_), _)) => (),
        Ok(_) => assert!(false),
        Err(err) => {
            println!("{}", err);
            assert!(false);
        }
    }
    bencher.iter(|| {
        let result = parser.easy_parse(State::new(&data[..]));
        black_box(result)
    });
}

fn bench_json_core_error(bencher: &mut Bencher) {
    let data = test_data();
    let mut parser = json_value();
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
        black_box(result)
    });
}

fn bench_json_core_error_no_position(bencher: &mut Bencher) {
    let data = test_data();
    let mut parser = json_value();
    match parser.parse(&data[..]) {
        Ok((Value::Array(_), _)) => (),
        Ok(_) => assert!(false),
        Err(err) => {
            println!("{}", err);
            assert!(false);
        }
    }
    bencher.iter(|| {
        let result = parser.parse(&data[..]);
        black_box(result)
    });
}

fn bench_buffered_json(bencher: &mut Bencher) {
    let data = test_data();
    bencher.iter(|| {
        let buffer = buffered::Stream::new(State::new(IteratorStream::new(data.chars())), 1);
        let mut parser = json_value();
        match parser.easy_parse(State::with_positioner(buffer, SourcePosition::default())) {
            Ok((Value::Array(v), _)) => {
                black_box(v);
            }
            Ok(_) => assert!(false),
            Err(err) => {
                println!("{}", err);
                assert!(false);
            }
        }
    });
}

fn bench(c: &mut Criterion) {
    c.bench_function("json", bench_json);
    c.bench_function("json_core_error", bench_json_core_error);
    c.bench_function(
        "json_core_error_no_position",
    bench_json_core_error_no_position,
    );
    c.bench_function("buffered_json", bench_buffered_json);
}

criterion_group!(json, bench);
criterion_main!(json);

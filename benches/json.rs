// `impl Trait` is not required for this parser but we use to to show that it can be used to
// significantly simplify things

#![cfg(feature = "std")]

#[macro_use]
extern crate criterion;

#[macro_use]
extern crate combine;

use std::{collections::HashMap, fs::File, hash::Hash, io::Read, path::Path};

use {
    combine::{
        error::ParseError,
        one_of,
        parser::{
            char::{char, digit, spaces, string},
            choice::{choice, optional},
            range,
            repeat::{sep_by, skip_many, skip_many1},
            sequence::between,
        },
        stream::position,
        unexpected_any, value, EasyParser, Parser, RangeStream, Stream, StreamOnce,
    },
    criterion::{black_box, Bencher, Criterion},
};

#[derive(PartialEq, Debug)]
enum Value<S>
where
    S: Eq + Hash,
{
    Number(f64),
    String(S),
    Bool(bool),
    Null,
    Object(HashMap<S, Value<S>>),
    Array(Vec<Value<S>>),
}

trait Captures<'a> {}
impl<T> Captures<'_> for T {}

fn lex<Input, P>(p: P) -> impl Parser<Input, Output = P::Output>
where
    P: Parser<Input>,
    Input: Stream<Token = char>,
    <Input as StreamOnce>::Error: ParseError<
        <Input as StreamOnce>::Token,
        <Input as StreamOnce>::Range,
        <Input as StreamOnce>::Position,
    >,
{
    p.skip(spaces())
}

fn number<'a, I>() -> impl Parser<I, Output = f64> + Captures<'a>
where
    I: RangeStream<Token = char, Range = &'a str>,
    I::Error: ParseError<I::Token, I::Range, I::Position>,
{
    lex(range::recognize((
        optional(char('-')),
        (
            char('0').map(|_| ()).or(skip_many1(digit())),
            optional((char('.'), skip_many(digit()))),
        ),
        optional((
            (one_of("eE".chars()), optional(one_of("+-".chars()))),
            skip_many1(digit()),
        )),
    )))
    .map(|s: &'a str| s.parse().unwrap())
    .expected("number")
}

fn json_string<'a, I>() -> impl Parser<I, Output = &'a str>
where
    I: RangeStream<Token = char, Range = &'a str>,
    I::Error: ParseError<I::Token, I::Range, I::Position>,
{
    let mut in_escape = false;
    between(
        char('"'),
        lex(char('"')),
        range::take_while(move |c| {
            if in_escape {
                match c {
                    '"' | '\\' | '/' | 'b' | 'f' | 'n' | 'r' | 't' => {
                        in_escape = false;
                        true
                    }
                    _ => false,
                }
            } else {
                match c {
                    '\\' => {
                        in_escape = true;
                        true
                    }
                    '"' => false,
                    _ => true,
                }
            }
        })
        .then(|s: &'a str| {
            if s.ends_with('\\') {
                unexpected_any("escape character").left()
            } else {
                value(s).right()
            }
        }),
    )
    .expected("string")
}

fn object<'a, I>() -> impl Parser<I, Output = HashMap<&'a str, Value<&'a str>>>
where
    I: RangeStream<Token = char, Range = &'a str>,
    I::Error: ParseError<I::Token, I::Range, I::Position>,
{
    let field = (json_string(), lex(char(':')), json_value_()).map(|t| (t.0, t.2));
    let fields = sep_by(field, lex(char(',')));
    between(lex(char('{')), lex(char('}')), fields).expected("object")
}

fn array<'a, I>() -> impl Parser<I, Output = Vec<Value<&'a str>>>
where
    I: RangeStream<Token = char, Range = &'a str>,
    I::Error: ParseError<I::Token, I::Range, I::Position>,
{
    between(
        lex(char('[')),
        lex(char(']')),
        sep_by(json_value_(), lex(char(','))),
    )
    .expected("array")
}

#[inline(always)]
fn json_value<'a, I>() -> impl Parser<I, Output = Value<&'a str>>
where
    I: RangeStream<Token = char, Range = &'a str>,
    I::Error: ParseError<I::Token, I::Range, I::Position>,
{
    spaces().with(json_value_())
}

// We need to use `parser!` to break the recursive use of `value` to prevent the returned parser
// from containing itself
parser! {
    #[inline(always)]
    fn json_value_['a, I]()(I) -> Value<I::Range>
        where [ I: RangeStream<Token = char, Range = &'a str> ]
    {
        choice((
            json_string().map(Value::String),
            object().map(Value::Object),
            array().map(Value::Array),
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

    let input = r#" {
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
            panic!();
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
    match parser.easy_parse(position::Stream::new(&data[..])) {
        Ok((Value::Array(_), _)) => (),
        Ok(_) => panic!(),
        Err(err) => {
            println!("{}", err);
            panic!();
        }
    }
    bencher.iter(|| {
        let result = parser.easy_parse(position::Stream::new(&data[..]));
        black_box(result)
    });
}

fn bench_json_core_error(bencher: &mut Bencher<'_>) {
    let data = test_data();
    let mut parser = json_value();
    match parser.parse(position::Stream::new(&data[..])) {
        Ok((Value::Array(_), _)) => (),
        Ok(_) => panic!(),
        Err(err) => {
            println!("{}", err);
            panic!();
        }
    }
    bencher.iter(|| {
        let result = parser.parse(position::Stream::new(&data[..]));
        black_box(result)
    });
}

fn bench_json_core_error_no_position(bencher: &mut Bencher<'_>) {
    let data = test_data();
    let mut parser = json_value();
    match parser.parse(&data[..]) {
        Ok((Value::Array(_), _)) => (),
        Ok(_) => panic!(),
        Err(err) => {
            println!("{}", err);
            panic!();
        }
    }
    bencher.iter(|| {
        let result = parser.parse(&data[..]);
        black_box(result)
    });
}

/*
fn bench_buffered_json(bencher: &mut Bencher) {
    let data = test_data();
    bencher.iter(|| {
        let buffer =
            buffered::Stream::new(position::Stream::new(IteratorStream::new(data.chars())), 1);
        let mut parser = json_value();
        match parser.easy_parse(position::Stream::with_positioner(
            buffer,
            SourcePosition::default(),
        )) {
            Ok((Value::Array(v), _)) => {
                black_box(v);
            }
            Ok(_) => panic!(),
            Err(err) => {
                println!("{}", err);
                panic!();
            }
        }
    });
}

*/

fn bench(c: &mut Criterion) {
    c.bench_function("json", bench_json);
    c.bench_function("json_core_error", bench_json_core_error);
    c.bench_function(
        "json_core_error_no_position",
        bench_json_core_error_no_position,
    );
    // c.bench_function("buffered_json", bench_buffered_json);
}

criterion_group!(json, bench);
criterion_main!(json);

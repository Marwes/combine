#[macro_use]
extern crate bencher;

#[macro_use]
extern crate combine as pc;

use std::collections::HashMap;
use std::io::Read;
use std::fs::File;
use std::path::Path;

use bencher::{black_box, Bencher};

use pc::primitives::{BufferedStream, Consumed, IteratorStream, ParseError, ParseResult, Parser,
                     Stream};
use pc::char::{char, digit, spaces, string, Spaces};
use pc::combinator::{any, between, choice, many, optional, parser, satisfy, sep_by, Expected,
                     FnParser, Skip, many1};
use pc::state::{SourcePosition, State};

#[derive(PartialEq, Debug)]
pub enum Value {
    Number(f64),
    String(String),
    Bool(bool),
    Null,
    Object(HashMap<String, Value>),
    Array(Vec<Value>),
}

fn lex<P>(p: P) -> Skip<P, Spaces<P::Input>>
where
    P: Parser,
    P::Input: Stream<Item = char>,
{
    p.skip(spaces())
}

type FnPtrParser<O, I> = FnParser<I, fn(I) -> ParseResult<O, I>>;
type JsonParser<O, I> = Expected<FnPtrParser<O, I>>;

fn fn_parser<O, I>(f: fn(I) -> ParseResult<O, I>, err: &'static str) -> JsonParser<O, I>
where
    I: Stream<Item = char>,
{
    parser(f).expected(err)
}

fn integer<I>() -> JsonParser<i64, I>
    where I: Stream<Item = char>
{
    fn_parser(integer_, "integer")
}
fn integer_<I>(input: I) -> ParseResult<i64, I>
    where I: Stream<Item = char>
{
    let (s, input) = try!(lex(many1::<String, _>(digit())).parse_lazy(input).into());
    let mut n = 0;
    for c in s.chars() {
        n = n * 10 + (c as i64 - '0' as i64);
    }
    Ok((n, input))
}

fn number<I>() -> JsonParser<f64, I>
    where I: Stream<Item = char>
{
    fn_parser(number_, "number")
}
fn number_<I>(input: I) -> ParseResult<f64, I>
    where I: Stream<Item = char>
{
    let i = char('0')
        .map(|_| 0.0)
        .or(integer().map(|x| x as f64));
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
    lex(
        optional(char('-'))
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
            }),
    ).parse_lazy(input)
        .into()
}

fn json_char<I>() -> JsonParser<char, I>
    where I: Stream<Item = char>
{
    fn_parser(json_char_, "char")
}
fn json_char_<I>(input: I) -> ParseResult<char, I>
    where I: Stream<Item = char>
{
    let (c, input) = try!(any().parse_lazy(input).into());
    let mut back_slash_char = satisfy(|c| "\"\\/bfnrt".chars().any(|x| x == c)).map(|c| {
        match c {
            '"' => '"',
            '\\' => '\\',
            '/' => '/',
            'b' => '\u{0008}',
            'f' => '\u{000c}',
            'n' => '\n',
            'r' => '\r',
            't' => '\t',
            c => c, //Should never happen
        }
    });
    match c {
        '\\' => input.combine(|input| back_slash_char.parse_stream(input)),
        '"' => Err(Consumed::Empty(
            ParseError::from_errors(input.into_inner().position(), Vec::new()).into(),
        )),
        _ => Ok((c, input)),
    }
}

parser!{
fn json_string[I]()(I) -> String
    where [I: Stream<Item = char>]
{
    between(char('"'), lex(char('"')), many(json_char()))
}
}

parser!{
fn object[I]()(I) -> Value
    where [I: Stream<Item = char>]
{
    let field = (json_string(), lex(char(':')), value()).map(|t| (t.0, t.2));
    let fields = sep_by(field, lex(char(',')));
    between(lex(char('{')), lex(char('}')), fields)
        .map(Value::Object)
}
}

parser!{

fn value[I]()(I) -> Value
    where [I: Stream<Item = char>]
{
    let array = between(
        lex(char('[')),
        lex(char(']')),
        sep_by(value(), lex(char(','))),
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
    let result = value().parse(input);
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
        ].into_iter()
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

fn bench_json(bencher: &mut Bencher) {
    let mut data = String::new();
    File::open(&Path::new(&"benches/data.json"))
        .and_then(|mut file| file.read_to_string(&mut data))
        .unwrap();
    let mut parser = value();
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

fn bench_buffered_json(bencher: &mut Bencher) {
    let mut data = String::new();
    File::open(&Path::new(&"benches/data.json"))
        .and_then(|mut file| file.read_to_string(&mut data))
        .unwrap();
    bencher.iter(|| {
        let buffer = BufferedStream::new(State::new(IteratorStream::new(data.chars())), 1);
        let mut parser = value();
        match parser.parse(State::with_positioner(
            buffer.as_stream(),
            SourcePosition::default(),
        )) {
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

benchmark_group!(json, bench_json, bench_buffered_json);
benchmark_main!(json);

#![cfg(feature = "std")]
extern crate combine;
use combine::parser::char::{char, digit, spaces, string};
use combine::stream::buffered::BufferedStream;
use combine::stream::easy::{self, Error};
use combine::stream::state::State;
use combine::stream::IteratorStream;
use combine::{choice, many, many1, sep_by, try, Parser, Positioned};

#[test]
fn shared_stream_buffer() {
    // Iterator that can't be cloned
    let text = "10,222,3,44".chars().map(|c| {
        if c.is_digit(10) {
            (c as u8 + 1) as char
        } else {
            c
        }
    });
    let buffer = BufferedStream::new(State::new(IteratorStream::new(text)), 1);
    let int: &mut Parser<Input = _, Output = _, PartialState = _> =
        &mut many(digit()).map(|s: String| s.parse::<i64>().unwrap());
    let result = sep_by(int, char(',')).parse(buffer).map(|t| t.0);
    assert_eq!(result, Ok(vec![21, 333, 4, 55]));
}

#[test]
fn shared_stream_backtrack() {
    let text = "apple,apple,ananas,orangeblah";
    let mut iter = text.chars();
    // Iterator that can't be cloned
    let stream = BufferedStream::new(State::new(IteratorStream::new(&mut iter)), 2);

    let value: &mut Parser<Input = _, Output = _, PartialState = _> = &mut choice([
        try(string("apple")),
        try(string("orange")),
        try(string("ananas")),
    ]);
    let mut parser = sep_by(value, char(','));
    let result = parser.parse(stream).map(|t| t.0);
    assert_eq!(result, Ok(vec!["apple", "apple", "ananas", "orange"]));
}

#[test]
fn shared_stream_insufficent_backtrack() {
    let text = "apple,apple,ananas,orangeblah";
    let mut iter = text.chars();
    // Iterator that can't be cloned
    let stream = BufferedStream::new(easy::Stream(State::new(IteratorStream::new(&mut iter))), 1);

    let value: &mut Parser<Input = _, Output = _, PartialState = _> = &mut choice([
        try(string("apple")),
        try(string("orange")),
        try(string("ananas")),
    ]);
    let mut parser = sep_by(value, char(','));
    let result: Result<Vec<&str>, _> = parser.parse(stream).map(|t| t.0);
    assert!(result.is_err());
    assert!(
        result
            .as_ref()
            .unwrap_err()
            .errors
            .iter()
            .any(|err| *err == Error::Message("Backtracked to far".into())),
        "{}",
        result.unwrap_err()
    );
}

/// Test which checks that a stream which has ended does not repeat the last token in some cases in
/// which case this test would loop forever
#[test]
fn always_output_end_of_input_after_end_of_input() {
    let text = "10".chars();
    let buffer = BufferedStream::new(State::new(IteratorStream::new(text)), 1);
    let int = many1(digit()).map(|s: String| s.parse::<i64>().unwrap());
    let result = many(spaces().with(int)).parse(buffer).map(|t| t.0);
    assert_eq!(result, Ok(vec![10]));
}

#[test]
fn position() {
    let text = "10abc".chars();
    let stream = BufferedStream::new(State::new(IteratorStream::new(text)), 3);
    assert_eq!(stream.position(), 0);
    let result = many1::<Vec<_>, _>(digit()).parse(stream);
    assert!(result.is_ok());
    assert_eq!(result.unwrap().1.position(), 2);
}

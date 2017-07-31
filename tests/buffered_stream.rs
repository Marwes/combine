// The feature `buffered_stream` must be enabled to run these tests
extern crate combine;
use combine::primitives::{BufferedStream, Error};
use combine::char::{char, digit, spaces, string};
use combine::{choice, many, sep_by, try, Parser, Positioned, many1};

#[allow(deprecated)]
use combine::from_iter;

#[test]
#[allow(deprecated)]
fn shared_stream_buffer() {
    // Iterator that can't be cloned
    let text = "10,222,3,44".chars().map(|c| if c.is_digit(10) {
        (c as u8 + 1) as char
    } else {
        c
    });
    let buffer = BufferedStream::new(from_iter(text), 1);
    let int: &mut Parser<Input = _, Output = _> =
        &mut many(digit()).map(|s: String| s.parse::<i64>().unwrap());
    let result = sep_by(int, char(','))
        .parse(buffer.as_stream())
        .map(|t| t.0);
    assert_eq!(result, Ok(vec![21, 333, 4, 55]));
}

#[test]
#[allow(deprecated)]
fn shared_stream_backtrack() {
    let text = "apple,apple,ananas,orangeblah";
    let mut iter = text.chars();
    // Iterator that can't be cloned
    let buffer = BufferedStream::new(from_iter(&mut iter), 2);
    let stream = buffer.as_stream();

    let value: &mut Parser<Input = _, Output = _> = &mut choice([
        try(string("apple")),
        try(string("orange")),
        try(string("ananas")),
    ]);
    let mut parser = sep_by(value, char(','));
    let result = parser.parse(stream).map(|t| t.0);
    assert_eq!(result, Ok(vec!["apple", "apple", "ananas", "orange"]));
}

#[test]
#[allow(deprecated)]
fn shared_stream_insufficent_backtrack() {
    let text = "apple,apple,ananas,orangeblah";
    let mut iter = text.chars();
    // Iterator that can't be cloned
    let buffer = BufferedStream::new(from_iter(&mut iter), 1);
    let stream = buffer.as_stream();

    let value: &mut Parser<Input = _, Output = _> = &mut choice([
        try(string("apple")),
        try(string("orange")),
        try(string("ananas")),
    ]);
    let mut parser = sep_by(value, char(','));
    let result: Result<Vec<&str>, _> = parser.parse(stream).map(|t| t.0);
    assert!(result.is_err());
    assert!(
        result
            .unwrap_err()
            .errors
            .iter()
            .any(|err| *err == Error::Message("Backtracked to far".into()))
    );
}

/// Test which checks that a stream which has ended does not repeat the last token in some cases in
/// which case this test would loop forever
#[test]
#[allow(deprecated)]
fn always_output_end_of_input_after_end_of_input() {
    let text = "10".chars();
    let buffer = BufferedStream::new(from_iter(text), 1);
    let int = many1(digit()).map(|s: String| s.parse::<i64>().unwrap());
    let result = many(spaces().with(int))
        .parse(buffer.as_stream())
        .map(|t| t.0);
    assert_eq!(result, Ok(vec![10]));
}

#[test]
#[allow(deprecated)]
fn position() {
    let text = "10abc".chars();
    let buffer = BufferedStream::new(from_iter(text), 3);
    let stream = buffer.as_stream();
    println!("{:?}", stream);
    assert_eq!(stream.position(), 0);
    let result = many1::<Vec<_>, _>(digit()).parse(stream.clone());
    println!("{:?}", stream);
    assert_eq!(stream.position(), 0);
    assert!(result.is_ok());
    assert_eq!(result.unwrap().1.position(), 2);
}

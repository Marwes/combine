//The feature `buffered_stream` must be enabled to run these tests
extern crate combine;
use combine::*;
use combine::primitives::{BufferedStream, Error};

#[test]
fn shared_stream_buffer() {
    //Iterator that can't be cloned
    let text = "10,222,3,44".chars().map(|c| {
        if c.is_digit(10) {
            (c as u8 + 1) as char
        }
        else {
            c
        }
    });
    let buffer = BufferedStream::new(text, 1);
    let int = many(digit())
        .map(|s: String| s.parse::<i64>().unwrap());
    let result = sep_by(int, char(','))
        .parse(buffer.as_stream())
        .map(|t| t.0);
    assert_eq!(result, Ok(vec![21, 333, 4, 55]));
}

#[test]
fn shared_stream_backtrack() {
    let text = "apple,apple,ananas,orangeblah";
    let mut iter = text.chars();
    //Iterator that can't be cloned
    let buffer = BufferedStream::new(&mut iter, 2);
    let stream = buffer.as_stream();

    let value = choice([
        try(string("apple")),
        try(string("orange")),
        try(string("ananas"))
    ]);
    let mut parser = sep_by(value, char(','));
    let result = parser.parse(stream)
        .map(|t| t.0);
    assert_eq!(result, Ok(vec!["apple", "apple", "ananas", "orange"]));
}

#[test]
fn shared_stream_insufficent_backtrack() {
    let text = "apple,apple,ananas,orangeblah";
    let mut iter = text.chars();
    //Iterator that can't be cloned
    let buffer = BufferedStream::new(&mut iter, 1);
    let stream = buffer.as_stream();

    let value = choice([
        try(string("apple")),
        try(string("orange")),
        try(string("ananas"))
    ]);
    let mut parser = sep_by(value, char(','));
    let result: Result<Vec<&str>, _> = parser.parse(stream)
        .map(|t| t.0);
    assert!(result.is_err());
    assert!(result.unwrap_err().errors.iter()
            .any(|err| *err == Error::Message("Backtracked to far".into())));
}

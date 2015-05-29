
extern crate parser_combinators;
use parser_combinators::{many, Parser};
use parser_combinators::char::letter;

#[test]
fn readme() {
    let result = many(letter()).parse("hello world");
    assert_eq!(result, Ok(("hello".to_string(), " world")));
}

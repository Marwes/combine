//! Parser example for INI files.
extern crate combine;

use std::collections::HashMap;

use combine::*;
use combine::char::space;
use combine::primitives::{Error, SourcePosition};

#[derive(PartialEq, Debug)]
pub struct Ini {
    pub global: HashMap<String, String>,
    pub sections: HashMap<String, HashMap<String, String>>,
}

fn property<I>(input: I) -> ParseResult<(String, String), I>
    where I: Stream<Item = char>
{
    (many1(satisfy(|c| c != '=' && c != '[' && c != ';')),
     token('='),
     many1(satisfy(|c| c != '\n' && c != ';')))
            .map(|(key, _, value)| (key, value))
            .expected("property")
            .parse_stream(input)
}

fn whitespace<I>(input: I) -> ParseResult<(), I>
    where I: Stream<Item = char>
{
    let comment = (token(';'), skip_many(satisfy(|c| c != '\n'))).map(|_| ());
    // Wrap the `spaces().or(comment)` in `skip_many` so that it skips alternating whitespace and
    // comments
    skip_many(skip_many1(space()).or(comment)).parse_stream(input)
}

fn properties<I>(input: I) -> ParseResult<HashMap<String, String>, I>
    where I: Stream<Item = char>
{
    // After each property we skip any whitespace that followed it
    many(parser(property).skip(parser(whitespace))).parse_stream(input)
}

fn section<I>(input: I) -> ParseResult<(String, HashMap<String, String>), I>
    where I: Stream<Item = char>
{
    (between(token('['), token(']'), many(satisfy(|c| c != ']'))),
     parser(whitespace),
     parser(properties))
            .map(|(name, _, properties)| (name, properties))
            .expected("section")
            .parse_stream(input)
}

fn ini<I>(input: I) -> ParseResult<Ini, I>
    where I: Stream<Item = char>
{
    (parser(whitespace), parser(properties), many(parser(section)))
        .map(|(_, global, sections)| {
                 Ini {
                     global: global,
                     sections: sections,
                 }
             })
        .parse_stream(input)
}

#[test]
fn ini_ok() {
    let text = r#"
language=rust

[section]
name=combine; Comment
type=LL(1)

"#;
    let mut expected = Ini {
        global: HashMap::new(),
        sections: HashMap::new(),
    };
    expected
        .global
        .insert(String::from("language"), String::from("rust"));

    let mut section = HashMap::new();
    section.insert(String::from("name"), String::from("combine"));
    section.insert(String::from("type"), String::from("LL(1)"));
    expected
        .sections
        .insert(String::from("section"), section);

    let result = parser(ini).parse(text).map(|t| t.0);
    assert_eq!(result, Ok(expected));
}

#[test]
fn ini_error() {
    let text = "[error";
    let result = parser(ini).parse(State::new(text)).map(|t| t.0);
    assert_eq!(result,
               Err(ParseError {
                       position: SourcePosition { line: 1, column: 7 },
                       errors: vec![Error::end_of_input(), Error::Expected("section".into())],
                   }));
}

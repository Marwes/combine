//! Parser example for INI files.
#[macro_use]
extern crate combine;

use std::collections::HashMap;

use combine::*;
use combine::char::space;
use combine::primitives::Error;
use combine::state::SourcePosition;

#[derive(PartialEq, Debug)]
pub struct Ini {
    pub global: HashMap<String, String>,
    pub sections: HashMap<String, HashMap<String, String>>,
}

parser!{
    fn property[I]()(I) -> (String, String)
        where [I: Stream<Item = char>]
    {
        (
            many1(satisfy(|c| c != '=' && c != '[' && c != ';')),
            token('='),
            many1(satisfy(|c| c != '\n' && c != ';')),
        ).map(|(key, _, value)| (key, value))
            .message("while parsing property")
    }
}
parser!{
    fn whitespace[I]()(I) -> ()
    where
        [I: Stream<Item = char>,]
    {
        let comment = (token(';'), skip_many(satisfy(|c| c != '\n'))).map(|_| ());
        // Wrap the `spaces().or(comment)` in `skip_many` so that it skips alternating whitespace and
        // comments
        skip_many(skip_many1(space()).or(comment))
    }
}

parser!{
    fn properties[I]()(I) -> HashMap<String, String>
    where
        [I: Stream<Item = char>,]
    {
        // After each property we skip any whitespace that followed it
        many(property().skip(whitespace()))
    }
}

parser!{
    fn section[I]()(I) -> (String, HashMap<String, String>)
    where
        [I: Stream<Item = char>,]
    {
        (
            between(token('['), token(']'), many(satisfy(|c| c != ']'))),
            whitespace(),
            properties(),
        ).map(|(name, _, properties)| (name, properties))
            .message("while parsing section")
    }
}

parser!{
    fn ini[I]()(I) -> Ini
    where
        [I: Stream<Item = char>,]
    {
        (
            whitespace(),
            properties(),
            many(section()),
        ).map(|(_, global, sections)| {
                Ini {
                    global: global,
                    sections: sections,
                }
            })
    }
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
    expected.sections.insert(String::from("section"), section);

    let result = ini().parse(text).map(|t| t.0);
    assert_eq!(result, Ok(expected));
}

#[test]
fn ini_error() {
    let text = "[error";
    let result = ini().parse(State::new(text)).map(|t| t.0);
    assert_eq!(
        result,
        Err(ParseError {
            position: SourcePosition { line: 1, column: 7 },
            errors: vec![
                Error::end_of_input(),
                Error::Expected(']'.into()),
                Error::Message("while parsing section".into()),
            ],
        })
    );
}

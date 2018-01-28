//! Parser example for INI files.
#[macro_use]
extern crate combine;

use std::collections::HashMap;
use std::fmt;
use std::env;
use std::fs::File;
use std::io::{self, Read};

use combine::*;
use combine::parser::char::space;
use combine::stream::state::State;

#[cfg(feature = "std")]
use combine::stream::state::SourcePosition;
#[cfg(feature = "std")]
use combine::stream::easy;

enum Error<E> {
    Io(io::Error),
    Parse(E),
}

impl<E> fmt::Display for Error<E>
where
    E: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::Io(ref err) => write!(f, "{}", err),
            Error::Parse(ref err) => write!(f, "{}", err),
        }
    }
}

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

#[cfg(feature = "std")]
#[test]
fn ini_error() {
    let text = "[error";
    let result = ini().easy_parse(State::new(text)).map(|t| t.0);
    assert_eq!(
        result,
        Err(easy::Errors {
            position: SourcePosition { line: 1, column: 7 },
            errors: vec![
                easy::Error::end_of_input(),
                easy::Error::Expected(']'.into()),
                easy::Error::Message("while parsing section".into()),
            ],
        })
    );
}

fn main() {
    let result = match env::args().nth(1) {
        Some(file) => File::open(file).map_err(Error::Io).and_then(main_),
        None => main_(io::stdin()),
    };
    match result {
        Ok(_) => println!("OK"),
        Err(err) => println!("{}", err),
    }
}

#[cfg(feature = "std")]
fn main_<R>(mut read: R) -> Result<(), Error<easy::Errors<char, String, SourcePosition>>>
where
    R: Read,
{
    let mut text = String::new();
    read.read_to_string(&mut text).map_err(Error::Io)?;
    ini()
        .easy_parse(State::new(&*text))
        .map_err(|err| Error::Parse(err.map_range(|s| s.to_string())))?;
    Ok(())
}

#[cfg(not(feature = "std"))]
fn main_<R>(mut read: R) -> Result<(), Error<::combine::error::StringStreamError>>
where
    R: Read,
{
    let mut text = String::new();
    read.read_to_string(&mut text).map_err(Error::Io)?;
    ini().parse(State::new(&*text)).map_err(Error::Parse)?;
    Ok(())
}

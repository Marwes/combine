use combine::parser::char::{letter, space};
use combine::{many1, sep_by, Parser};

#[test]
fn readme() {
    main();
}

fn main() {
    let word = many1(letter());

    let mut parser = sep_by(word, space()).map(|mut words: Vec<String>| words.pop());
    let result = parser.parse("Pick up that word!");
    assert_eq!(result, Ok((Some("word".to_string()), "!")));
}

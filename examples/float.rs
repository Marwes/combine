extern crate combine;

use combine::parser::range::recognize;
use combine::parser::repeat::{skip_many, skip_many1};
use combine::parser::choice::optional;
use combine::parser::item::item;
use combine::parser::byte::digit;
use combine::Parser;

fn main() {
    let mut parser = recognize((
        skip_many1(digit()),
        optional((item(b'.'), skip_many(digit()))),
    )).and_then(|bs: &[u8]| {
        let s = unsafe { ::std::str::from_utf8_unchecked(bs) };
        s.parse::<f64>()
    });
    let result = parser.easy_parse(&b"123.45"[..]);
    assert_eq!(result, Ok((123.45, &b""[..])));
    println!("{:?}", result);
}

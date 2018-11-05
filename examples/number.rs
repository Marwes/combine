#![cfg_attr(not(feature = "std"), no_std)]

extern crate combine;

#[cfg(not(feature = "std"))]
use core::str;
#[cfg(feature = "std")]
use std::str;

use combine::error::UnexpectedParse;
use combine::parser::byte::digit;
use combine::parser::choice::optional;
use combine::parser::item::item;
use combine::parser::range::recognize;
use combine::parser::repeat::{skip_many, skip_many1};
use combine::Parser;

fn main() {
    let mut parser = recognize((
        skip_many1(digit()),
        optional((item(b'.'), skip_many(digit()))),
    ))
    .and_then(|bs: &[u8]| {
        // `bs` only contains digits which are ascii and thus UTF-8
        let s = unsafe { str::from_utf8_unchecked(bs) };
        s.parse::<f64>().map_err(|_| UnexpectedParse::Unexpected)
    });
    let result = parser.parse(&b"123.45"[..]);
    assert_eq!(result, Ok((123.45, &b""[..])));
}

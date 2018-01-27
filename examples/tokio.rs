#![cfg(feature = "std")]

extern crate bytes;
#[macro_use]
extern crate combine;

extern crate futures;
extern crate partial_io;
extern crate tokio_io;

use std::rc::Rc;
use std::cell::Cell;
use std::str;
use std::io::Cursor;

use bytes::BytesMut;

use tokio_io::codec::Decoder;

use combine::error::ParseError;
use combine::stream::{PartialStream, RangeStream};
use combine::combinator::{any_partial_state, AnyPartialState};
use combine::parser::range::{range, recognize, take};
use combine::{skip_many, skip_many1};
use combine::stream::easy;
use combine::parser::byte::digit;

pub struct LanguageServerDecoder {
    state: AnyPartialState,
    content_length_parses: Rc<Cell<i32>>,
}

impl LanguageServerDecoder {
    pub fn new() -> LanguageServerDecoder {
        LanguageServerDecoder {
            state: Default::default(),
            content_length_parses: Rc::new(Cell::new(0)),
        }
    }
}

parser! {
    type PartialState = AnyPartialState;
    fn decode_parser['a, I](content_length_parses: Rc<Cell<i32>>)(I) -> Vec<u8>
    where [ I: RangeStream<Item = u8, Range = &'a [u8], Error = easy::StreamErrors<I>>,
            I::Error: ParseError<u8, &'a [u8], I::Position, StreamError = easy::Error<u8, &'a [u8]>>,
        ]
    {
        let content_length =
            range(&b"Content-Length: "[..])
                .with(
                    recognize(skip_many1(digit()))
                        .and_then(|digits: &[u8]| unsafe {
                            str::from_utf8_unchecked(digits).parse::<usize>()
                        })
                )
                .map(|x| {
                    content_length_parses.set(content_length_parses.get() + 1);
                    x
                });
        any_partial_state((
            skip_many(range(&b"\r\n"[..])),
            content_length,
            range(&b"\r\n\r\n"[..]).map(|_| ()),
        ).map(|t| t.1)
            .then_partial(|&mut message_length| take(message_length).map(|bytes: &[u8]| bytes.to_owned())))
    }
}

impl Decoder for LanguageServerDecoder {
    type Item = String;
    type Error = Box<::std::error::Error + Send + Sync>;

    fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        println!("Decoding `{:?}`", str::from_utf8(src).unwrap_or("NOT UTF8"));

        let (opt, removed_len) = combine::stream::decode(
            decode_parser(self.content_length_parses.clone()),
            easy::Stream(PartialStream(&src[..])),
            &mut self.state,
        ).map_err(|err| {
            // Since err contains references into `src` we must remove these before
            // returning the error and before we call `split_to` to remove the input we
            // just consumed
            let err = err.map_range(|r| {
                str::from_utf8(r)
                    .ok()
                    .map_or_else(|| format!("{:?}", r), |s| s.to_string())
            }).map_position(|p| p.translate_position(&src[..]));
            format!("{}\nIn input: `{}`", err, str::from_utf8(src).unwrap())
        })?;

        println!(
            "Accepted {} bytes: `{:?}`",
            removed_len,
            str::from_utf8(&src[..removed_len]).unwrap_or("NOT UTF8")
        );
        src.split_to(removed_len);
        match opt {
            None => {
                println!("Requesting more input!");
                Ok(None)
            }
            Some(output) => {
                let value = String::from_utf8(output)?;
                println!("Decoded `{}`", value);
                Ok(Some(value))
            }
        }
    }
}

fn main() {
    use futures::{Future, Stream};
    use tokio_io::codec::FramedRead;
    use partial_io::{PartialAsyncRead, PartialOp};

    let input = "Content-Length: 6\r\n\
                 \r\n\
                 123456\r\n\
                 Content-Length: 4\r\n\
                 \r\n\
                 true";

    let seq = vec![
        PartialOp::Limited(20),
        PartialOp::Limited(1),
        PartialOp::Limited(2),
        PartialOp::Limited(3),
    ];
    let ref mut reader = Cursor::new(input.as_bytes());
    let partial_reader = PartialAsyncRead::new(reader, seq);

    let decoder = LanguageServerDecoder::new();
    let content_length_parses = decoder.content_length_parses.clone();

    let result = FramedRead::new(partial_reader, decoder).collect().wait();

    assert!(result.as_ref().is_ok(), "{}", result.unwrap_err());
    let values = result.unwrap();

    let expected_values = ["123456", "true"];
    assert_eq!(values, expected_values);

    assert_eq!(content_length_parses.get(), expected_values.len() as i32);

    println!("Successfully parsed: `{}`", input);
    println!(
        "Found {} items and never repeated a completed parse!",
        values.len(),
    );
    println!("Result: {:?}", values);
}

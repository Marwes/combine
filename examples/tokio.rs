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

use combine::primitives::{ParseError, PointerOffset, RangeStream, RangeStreamOnce, Resetable,
                          StreamOnce};
use combine::range::{range, recognize, take};
use combine::{skip_many, Parser, skip_many1};
use combine::easy::{self, Error as CombineError, Errors};
use combine::byte::digit;

pub struct LanguageServerDecoder {
    state: decode_parser::PartialState,
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
    fn decode_parser['a](content_length_parses: Rc<Cell<i32>>)(easy::Stream<&'a [u8]>) -> Vec<u8>
    where [ <easy::Stream<&'a [u8]> as StreamOnce>::Error:
                ParseError<u8, &'a [u8], PointerOffset, StreamError = easy::Error<u8, &'a [u8]>>
        ]
    {
        (
            skip_many(range(&b"\r\n"[..])),
            range(&b"Content-Length: "[..]).map(|_| content_length_parses.set(content_length_parses.get() + 1)),
            recognize(skip_many1(digit())),
            range(&b"\r\n\r\n"[..]),
        ).map(|t| t.2)
            .and_then(|digits: &[u8]| unsafe {
                str::from_utf8_unchecked(digits).parse::<usize>()
            })
            .then(|message_length| take(message_length).map(|bytes: &[u8]| bytes.to_owned()))
    }
}

impl Decoder for LanguageServerDecoder {
    type Item = String;
    type Error = Box<::std::error::Error + Send + Sync>;

    fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        let opt = combine::async::decode(
            decode_parser(self.content_length_parses.clone()),
            easy::Stream(&src[..]),
            &mut self.state,
        ).map_err(|err| {
            // Since err contains references into `src` we must remove these before
            // returning the error and before we call `split_to` to remove the input we
            // just consumed
            err.map_range(|r| {
                str::from_utf8(r)
                    .ok()
                    .map_or_else(|| format!("{:?}", r), |s| s.to_string())
            }).map_position(|p| p.translate_position(&src[..]))
        })?;

        match opt {
            None => Ok(None),
            Some((output, removed_len)) => {
                src.split_to(removed_len);
                Ok(Some(String::from_utf8(output)?))
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
        PartialOp::Limited(0),
        PartialOp::Limited(1),
        PartialOp::Limited(1),
    ];
    let ref mut reader = Cursor::new(input.as_bytes());
    let partial_reader = PartialAsyncRead::new(reader, seq);

    let decoder = LanguageServerDecoder::new();
    let content_length_parses = decoder.content_length_parses.clone();

    let result = FramedRead::new(partial_reader, decoder).collect().wait();

    assert!(result.as_ref().is_ok(), "{}", result.unwrap_err());
    assert_eq!(
        result.unwrap(),
        vec!["123456".to_string(), "true".to_string()]
    );

    assert_eq!(content_length_parses.get(), 2);
}

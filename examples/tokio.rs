extern crate bytes;
#[macro_use]
extern crate combine;

extern crate futures;
extern crate partial_io;
extern crate tokio_io;

use std::str;
use std::io::Cursor;

use bytes::BytesMut;

use tokio_io::codec::Decoder;

use combine::range::{range, recognize, take};
use combine::{skip_many, Parser};
use combine::easy::{self, Error as CombineError, Errors};
use combine::byte::digit;

#[derive(Debug)]
enum State {
    Nothing,
    ContentLength(usize),
}

#[derive(Debug)]
pub struct LanguageServerDecoder {
    state: State,
}

impl LanguageServerDecoder {
    pub fn new() -> LanguageServerDecoder {
        LanguageServerDecoder {
            state: State::Nothing,
        }
    }
}

fn combine_decode<'a, P, R>(
    mut parser: P,
    src: &'a [u8],
) -> Result<Option<(R, usize)>, Errors<usize, u8, String>>
where
    P: Parser<Input = easy::Stream<&'a [u8]>, Output = R>,
{
    match parser.parse(easy::Stream(&src[..])) {
        Ok((message, rest)) => Ok(Some((message, src.len() - rest.0.len()))),
        Err(err) => {
            return if err.errors
                .iter()
                .any(|err| *err == CombineError::end_of_input())
            {
                Ok(None)
            } else {
                Err(err.map_range(|r| {
                    str::from_utf8(r)
                        .ok()
                        .map_or_else(|| format!("{:?}", r), |s| s.to_string())
                }).map_position(|p| p.translate_position(&src[..])))
            }
        }
    }
}

macro_rules! decode {
    ($parser: expr, $src: expr) => {
        {
            let (output, removed_len) = {
                match combine_decode($parser, &$src[..])? {
                    None => return Ok(None),
                    Some(x) => x,
                }
            };
            $src.split_to(removed_len);
            output
        }
    };
}

impl Decoder for LanguageServerDecoder {
    type Item = String;
    type Error = Box<::std::error::Error + Send + Sync>;

    fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        loop {
            match self.state {
                State::Nothing => {
                    let value = decode!(
                        (
                            skip_many(range(&b"\r\n"[..])),
                            range(&b"Content-Length: "[..]),
                            recognize(digit()),
                            range(&b"\r\n\r\n"[..]),
                        ).map(|t| t.2)
                            .and_then(|digits: &[u8]| unsafe {
                                str::from_utf8_unchecked(digits).parse::<usize>()
                            }),
                        src
                    );

                    self.state = State::ContentLength(value);
                }
                State::ContentLength(message_length) => {
                    let message = decode!(
                        take(message_length).map(|bytes: &[u8]| bytes.to_owned()),
                        src
                    );
                    self.state = State::Nothing;
                    return Ok(Some(String::from_utf8(message)?));
                }
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
        PartialOp::Limited(2),
        PartialOp::Limited(1),
        PartialOp::Limited(20),
    ];
    let ref mut reader = Cursor::new(input.as_bytes());
    let partial_reader = PartialAsyncRead::new(reader, seq);
    let result = FramedRead::new(partial_reader, LanguageServerDecoder::new())
        .collect()
        .wait();
    assert!(result.as_ref().is_ok(), "{}", result.unwrap_err());
    assert_eq!(
        result.unwrap(),
        vec!["123456".to_string(), "true".to_string()]
    );
}

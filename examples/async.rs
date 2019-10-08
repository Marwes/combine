#![cfg(feature = "std")]

extern crate bytes_0_4 as bytes;
extern crate combine;

extern crate futures;
extern crate partial_io;
extern crate tokio_codec_0_1 as tokio_codec;
extern crate tokio_io;

use std::cell::Cell;
use std::io::Cursor;
use std::rc::Rc;
use std::str;

use bytes::BytesMut;

use tokio_io::codec::Decoder;

use combine::combinator::{any_partial_state, AnyPartialState};
use combine::error::{ParseError, StreamError};
use combine::parser::byte::digit;
use combine::parser::range::{range, recognize, take};
use combine::stream::easy;
use combine::stream::{PartialStream, RangeStream, StreamErrorFor};
use combine::{skip_many, skip_many1, Parser};

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

/// Parses blocks of data with length headers
///
/// ```
/// Content-Length: 18
///
/// { "some": "data" }
/// ```
// The `content_length_parses` parameter only exists to demonstrate that `content_length` only
// gets parsed once per message
fn decode_parser<'a, Input>(
    content_length_parses: Rc<Cell<i32>>,
) -> impl Parser<Input, Output = Vec<u8>, PartialState = AnyPartialState> + 'a
where
    Input: RangeStream<Token = u8, Range = &'a [u8]> + 'a,
    // Necessary due to rust-lang/rust#24159
    Input::Error: ParseError<Input::Token, Input::Range, Input::Position>,
{
    let content_length = range(&b"Content-Length: "[..])
        .with(recognize(skip_many1(digit())).and_then(|digits: &[u8]| {
            str::from_utf8(digits)
                .unwrap()
                .parse::<usize>()
                // Convert the error from `.parse` into an error combine understands
                .map_err(StreamErrorFor::<Input>::other)
        }))
        .map(move |x| {
            content_length_parses.set(content_length_parses.get() + 1);
            x
        });

    // `any_partial_state` boxes the state which hides the type and lets us store it in
    // `self`
    any_partial_state(
        (
            skip_many(range(&b"\r\n"[..])),
            content_length,
            range(&b"\r\n\r\n"[..]).map(|_| ()),
        )
            .then_partial(|&mut (_, message_length, _)| {
                take(message_length).map(|bytes: &[u8]| bytes.to_owned())
            }),
    )
}

impl Decoder for LanguageServerDecoder {
    type Item = String;
    type Error = Box<dyn std::error::Error + Send + Sync>;

    fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        println!("Decoding `{:?}`", str::from_utf8(src).unwrap_or("NOT UTF8"));

        let (opt, removed_len) = combine::stream::decode(
            decode_parser(self.content_length_parses.clone()),
            // easy::Stream gives us nice error messages
            // (the same error messages that combine has had since its inception)
            // PartialStream lets the parser know that more input should be
            // expected if end of input is unexpectedly reached
            &mut easy::Stream(PartialStream(&src[..])),
            &mut self.state,
        )
        .map_err(|err| {
            // Since err contains references into `src` we must replace these before
            // we can return an error or call `split_to` to remove the input we
            // just consumed
            let err = err
                .map_range(|r| {
                    str::from_utf8(r)
                        .ok()
                        .map_or_else(|| format!("{:?}", r), |s| s.to_string())
                })
                .map_position(|p| p.translate_position(&src[..]));
            format!("{}\nIn input: `{}`", err, str::from_utf8(src).unwrap())
        })?;

        println!(
            "Accepted {} bytes: `{:?}`",
            removed_len,
            str::from_utf8(&src[..removed_len]).unwrap_or("NOT UTF8")
        );

        // Remove the input we just consumed.
        // Ideally this would be done automatically by the call to
        // `stream::decode` but it does unfortunately not work due
        // to lifetime issues (Non lexical lifetimes might fix it!)
        src.split_to(removed_len);

        match opt {
            // `None` means we did not have enough input and we require that the
            // caller of `decode` supply more before calling us again
            None => {
                println!("Requesting more input!");
                Ok(None)
            }

            // `Some` means that a message was successfully decoded
            // (and that we are ready to start decoding the next message)
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
    use partial_io::{PartialAsyncRead, PartialOp};
    use tokio_codec::FramedRead;

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
    // Using the `partial_io` crate we emulate the partial reads that would happen when reading
    // asynchronously from an io device.
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

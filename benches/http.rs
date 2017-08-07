#[macro_use]
extern crate bencher;
extern crate combine;

use bencher::{black_box, Bencher};

use combine::*;
use combine::primitives::Error;
use combine::range::{range, take_while1};

#[derive(Debug)]
struct Request<'a> {
    method: &'a [u8],
    uri: &'a [u8],
    version: &'a [u8],
}

#[derive(Debug)]
struct Header<'a> {
    name: &'a [u8],
    value: Vec<&'a [u8]>,
}

fn is_token(c: u8) -> bool {
    match c {
        128...255 |
        0...31 |
        b'(' |
        b')' |
        b'<' |
        b'>' |
        b'@' |
        b',' |
        b';' |
        b':' |
        b'\\' |
        b'"' |
        b'/' |
        b'[' |
        b']' |
        b'?' |
        b'=' |
        b'{' |
        b'}' |
        b' ' => false,
        _ => true,
    }
}

fn is_horizontal_space(c: u8) -> bool {
    c == b' ' || c == b'\t'
}
fn is_space(c: u8) -> bool {
    c == b' '
}
fn is_not_space(c: u8) -> bool {
    c != b' '
}
fn is_http_version(c: u8) -> bool {
    c >= b'0' && c <= b'9' || c == b'.'
}

fn parse_http_request(input: &[u8]) -> Result<((Request, Vec<Header>), &[u8]), ParseError<&[u8]>> {
    // Making a closure, because parser instances cannot be reused
    let end_of_line = || (token(b'\r'), token(b'\n')).map(|_| b'\r').or(token(b'\n'));

    let http_version = range(&b"HTTP/"[..]).with(take_while1(is_http_version));

    let request_line = struct_parser!(
        Request {
            method: take_while1(is_token),
            _: take_while1(is_space),
            uri: take_while1(is_not_space),
            _: take_while1(is_space),
            version: http_version,
        }
    );


    let message_header_line = (
        take_while1(is_horizontal_space),
        take_while1(|c| c != b'\r' && c != b'\n'),
        end_of_line(),
    ).map(|(_, line, _)| line);

    let message_header = (
        take_while1(is_token),
        token(b':'),
        many1(message_header_line),
    ).map(|(name, _, value)| {
            Header {
                name: name,
                value: value,
            }
        });

    let mut request = (
        request_line,
        end_of_line(),
        many(message_header),
        end_of_line(),
    ).map(|(request, _, headers, _)| (request, headers));

    request.parse(input)
}

static REQUESTS: &'static [u8] = include_bytes!("http-requests.txt");

fn http_requests_small(b: &mut Bencher) {
    http_requests_bench(b, REQUESTS)
}

fn http_requests_large(b: &mut Bencher) {
    use std::iter;

    let mut buffer = Vec::with_capacity(REQUESTS.len() * 5);
    for buf in iter::repeat(REQUESTS).take(5) {
        buffer.extend_from_slice(buf);
    }
    http_requests_bench(b, &buffer)
}

fn http_requests_bench(b: &mut Bencher, buffer: &[u8]) {
    b.iter(|| {
        let mut i = 0;
        let mut buf = black_box(buffer);

        while !buf.is_empty() {
            // Needed for inferrence for many(message_header)
            match parse_http_request(buf) {
                Ok(((_, _), b)) => {
                    i += 1;

                    buf = b
                }
                Err(ref err) if err.errors[0] == Error::end_of_input() => {
                    black_box(i);
                    return;
                }
                Err(err) => panic!("{:?}", err),
            }
        }
    });
}

benchmark_group!(http, http_requests_small, http_requests_large);
benchmark_main!(http);

#[macro_use]
extern crate criterion;
#[macro_use]
extern crate combine;

use criterion::{black_box, Bencher, Criterion};

use std::fmt;

use combine::{
    easy, many, one_of,
    parser::combinator::no_partial,
    range::{range, take_while1},
    stream::FullRangeStream,
    token, ParseError, Parser, RangeStream,
};

#[derive(Debug)]
struct Request<'a> {
    method: &'a [u8],
    uri: &'a [u8],
    version: u8,
}

#[derive(Debug, Copy, Clone)]
struct Header<'a> {
    name: &'a [u8],
    value: &'a [u8],
}

fn is_token(c: u8) -> bool {
    match c {
        128...255
        | 0...31
        | b'('
        | b')'
        | b'<'
        | b'>'
        | b'@'
        | b','
        | b';'
        | b':'
        | b'\\'
        | b'"'
        | b'/'
        | b'['
        | b']'
        | b'?'
        | b'='
        | b'{'
        | b'}'
        | b' ' => false,
        _ => true,
    }
}

fn is_header_value_token(c: u8) -> bool {
    return c == '\t' as u8 || (c > 31 && c != 127);
}

fn is_url_token(c: u8) -> bool {
    c > 0x20 && c < 0x7F
}

fn is_horizontal_space(c: u8) -> bool {
    c == b' ' || c == b'\t'
}

fn end_of_line<'a, I>() -> impl Parser<Output = (), Input = I> + 'a
where
    I: RangeStream<Item = u8, Range = &'a [u8]> + 'a,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    range(b"\r\n" as &[u8])
        .or(range(b"\n" as &[u8]))
        .map(|_| ())
}

fn message_header<'a, I>() -> impl Parser<Output = Header<'a>, Input = I>
where
    I: FullRangeStream<Item = u8, Range = &'a [u8]> + 'a,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    let header_value = no_partial((
        take_while1(is_horizontal_space),
        take_while1(is_header_value_token),
        end_of_line(),
    ))
    .map(|(_, line, _)| line);

    no_partial((take_while1(is_token), token(b':'), header_value))
        .map(|(name, _, value)| Header { name, value })
}

fn parse_http_request<'a, I>(input: I) -> Result<((Request<'a>, Vec<Header<'a>>), I), I::Error>
where
    I: FullRangeStream<Item = u8, Range = &'a [u8]> + 'a,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    let http_version = range(&b"HTTP/1."[..]).with(one_of(b"01".iter().cloned()).map(|c| {
        if c == b'0' {
            0
        } else {
            1
        }
    }));

    let request_line = no_partial(struct_parser!(Request {
        method: take_while1(is_token),
        _: token(b' '),
        uri: take_while1(is_url_token),
        _: token(b' '),
        version: http_version,
    }));

    let mut request = no_partial((
        request_line,
        end_of_line(),
        many(message_header()),
        end_of_line(),
    ))
    .map(|(request, _, headers, _)| (request, headers));

    request.parse(input)
}

static REQUESTS: &'static [u8] = include_bytes!("http-requests.txt");

fn http_requests_small(b: &mut Bencher) {
    http_requests_bench(b, easy::Stream(REQUESTS))
}

fn http_requests_large(b: &mut Bencher) {
    use std::iter;

    let mut buffer = Vec::with_capacity(REQUESTS.len() * 5);
    for buf in iter::repeat(REQUESTS).take(5) {
        buffer.extend_from_slice(buf);
    }
    http_requests_bench(b, easy::Stream(&buffer[..]))
}

fn http_requests_large_cheap_error(b: &mut Bencher) {
    use std::iter;

    let mut buffer = Vec::with_capacity(REQUESTS.len() * 5);
    for buf in iter::repeat(REQUESTS).take(5) {
        buffer.extend_from_slice(buf);
    }
    http_requests_bench(b, &buffer[..])
}

fn http_requests_bench<'a, I>(b: &mut Bencher, buffer: I)
where
    I: FullRangeStream<Item = u8, Range = &'a [u8]> + Clone + 'a,
    I::Error: ParseError<I::Item, I::Range, I::Position> + fmt::Debug,
{
    b.iter(|| {
        let mut buf = black_box(buffer.clone());

        while buf.clone().uncons().is_ok() {
            match parse_http_request(buf) {
                Ok(((_, _), b)) => {
                    buf = b;
                }
                Err(err) => panic!("{:?}", err),
            }
        }
    });
}

fn http_requests(c: &mut Criterion) {
    c.bench_function("http_requests_small", http_requests_small);
    c.bench_function("http_requests_large", http_requests_large);
    c.bench_function(
        "http_requests_large_cheap_error",
        http_requests_large_cheap_error,
    );
}

criterion_group!(http, http_requests,);
criterion_main!(http);

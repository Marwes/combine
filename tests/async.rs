#![allow(renamed_and_removed_lints)]

use std::{
    cell::Cell,
    io::{self, Cursor},
    rc::Rc,
    str,
};

use {
    bytes_0_4::BytesMut,
    combine::{
        any, count_min_max,
        error::{ParseError, StreamError},
        many1, parser,
        parser::{
            byte::{num, take_until_bytes},
            char::{char, digit, letter, string},
            choice::optional,
            combinator::{
                any_partial_state, any_send_partial_state, attempt, from_str, no_partial,
                recognize, AnyPartialState, AnySendPartialState,
            },
            range::{
                self, range, recognize_with_value, take, take_fn, take_until_range, take_while,
                take_while1,
            },
            repeat,
            token::token,
        },
        skip_many, skip_many1,
        stream::{easy, RangeStream, StreamErrorFor},
        Parser,
    },
    futures::{Future, Stream},
    quick_error::quick_error,
    quickcheck::quickcheck,
    tokio_codec_0_1::{Decoder, FramedRead},
};

quick_error! {
    #[derive(Debug)]
    enum Error {
        Io(err: io::Error) {
            display("{}", err)
            from()
        }
        Parse(err: easy::Errors<char, String, usize>) {
            display("{}", err)
            from()
        }
        Utf8(err: std::str::Utf8Error) {
            display("{}", err)
            from()
        }
        Message(err: String) {
            display("{}", err)
            from()
        }
    }
}

macro_rules! mk_parser {
    ($parser:expr, $self_:expr,()) => {
        $parser
    };
    ($parser:expr, $self_:expr,($custom_state:ty)) => {
        $parser($self_.1.clone())
    };
}
macro_rules! impl_decoder {
    ($typ: ident, $token: ty, $parser: expr, $custom_state: ty) => {
        #[derive(Default)]
        struct $typ(AnyPartialState, $custom_state);
        impl_decoder!{$typ, $token, $parser; ($custom_state)}
    };
    ($typ: ident, $token: ty, $parser: expr) => {
        #[derive(Default)]
        struct $typ(AnyPartialState);
        impl_decoder!{$typ, $token, $parser; ()}
    };
    ($typ: ident, $token: ty, $parser: expr; ( $($custom_state: tt)* )) => {
        impl Decoder for $typ {
            type Item = $token;
            type Error = Error;

            fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
                (&mut &mut *self).decode(src)
            }
        }

        impl<'a> Decoder for &'a mut $typ {
            type Item = $token;
            type Error = Error;

            fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
                let (opt, removed_len) = {
                    let str_src = str::from_utf8(&src[..])?;
                    println!("Decoding `{}`", str_src);
                    combine::stream::decode(
                        any_partial_state(mk_parser!($parser, self, ($($custom_state)*))),
                        &mut easy::Stream(combine::stream::PartialStream(str_src)),
                        &mut self.0,
                    ).map_err(|err| {
                        // Since err contains references into `src` we must remove these before
                        // returning the error and before we call `split_to` to remove the input we
                        // just consumed
                        let err = err.map_range(|r| r.to_string())
                            .map_position(|p| p.translate_position(&str_src[..]));
                        format!("{}\nIn input: `{}`", err, str_src)
                    })?
                };

                src.split_to(removed_len);
                match opt {
                    None => println!("Need more input!"),
                    Some(_) => (),
                }
                Ok(opt)
            }
        }
    }
}

macro_rules! impl_byte_decoder {
    ($typ: ident, $token: ty, $parser: expr, $custom_state: ty) => {
        #[derive(Default)]
        struct $typ(AnyPartialState, $custom_state);
        impl_byte_decoder!{$typ, $token, $parser; ($custom_state)}
    };
    ($typ: ident, $token: ty, $parser: expr) => {
        #[derive(Default)]
        struct $typ(AnyPartialState);
        impl_byte_decoder!{$typ, $token, $parser; ()}
    };
    ($typ: ident, $token: ty, $parser: expr; ( $($custom_state: tt)* )) => {
        impl Decoder for $typ {
            type Item = $token;
            type Error = Error;

            fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
                (&mut &mut *self).decode(src)
            }
        }

        impl<'a> Decoder for &'a mut $typ {
            type Item = $token;
            type Error = Error;

            fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
                let (opt, removed_len) = {
                    let str_src = &src[..];
                    println!("Decoding `{:?}`", str_src);
                    combine::stream::decode(
                        any_partial_state(mk_parser!($parser, self, ($($custom_state)*))),
                        &mut easy::Stream(combine::stream::PartialStream(str_src)),
                        &mut self.0,
                    ).map_err(|err| {
                        // Since err contains references into `src` we must remove these before
                        // returning the error and before we call `split_to` to remove the input we
                        // just consumed
                        let err = err.map_range(|r| format!("{:?}", r))
                            .map_position(|p| p.translate_position(&str_src[..]));
                        format!("{}\nIn input: `{:?}`", err, str_src)
                    })?
                };

                src.split_to(removed_len);
                match opt {
                    None => println!("Need more input!"),
                    Some(_) => (),
                }
                Ok(opt)
            }
        }
    }
}

use partial_io::{GenWouldBlock, PartialAsyncRead, PartialOp, PartialWithErrors};

fn run_decoder<B, D, S>(input: &B, seq: S, decoder: D) -> Result<Vec<D::Item>, D::Error>
where
    D: Decoder<Error = Error>,
    D::Item: ::std::fmt::Debug,
    S: IntoIterator<Item = PartialOp> + 'static,
    S::IntoIter: Send,
    B: ?Sized + AsRef<[u8]>,
{
    let ref mut reader = Cursor::new(input.as_ref());
    let partial_reader = PartialAsyncRead::new(reader, seq);
    FramedRead::new(partial_reader, decoder)
        .map(|x| {
            println!("Decoded `{:?}`", x);
            x
        })
        .collect()
        .wait()
}

parser! {
    type PartialState = AnyPartialState;
    fn basic_parser['a, Input]()(Input) -> String
        where [ Input: RangeStream<Token = char, Range = &'a str> ]
    {
        any_partial_state(
            many1(digit()).skip(range(&"\r\n"[..])),
        )
    }
}

impl_decoder! { Basic, String, basic_parser() }

#[test]
fn many1_skip_no_errors() {
    let input = "123\r\n\
                 456\r\n";

    let result = run_decoder(input, vec![], Basic::default());

    assert!(result.as_ref().is_ok(), "{}", result.unwrap_err());
    assert_eq!(result.unwrap(), vec!["123".to_string(), "456".to_string()]);
}

parser! {
    type PartialState = AnyPartialState;
    fn prefix_many_then_parser['a, Input]()(Input) -> String
        where [ Input: RangeStream<Token = char, Range = &'a str> ]
    {
        let integer = from_str(many1::<String, _, _>(digit()));
        any_partial_state((char('#'), skip_many(char(' ')), integer)
            .then_partial(|t| {
                let c = t.2;
                count_min_max(c, c, any())
            })
        )
    }
}

parser! {
    type PartialState = AnyPartialState;
    fn choice_parser['a, Input]()(Input) -> String
        where [ Input: RangeStream<Token = char, Range = &'a str> ]
    {
        any_partial_state(
            many1(digit())
                .or(many1(letter()))
                .skip(range(&"\r\n"[..]))
        )
    }
}

fn content_length<'a, Input>(
) -> impl Parser<Input, Output = String, PartialState = AnySendPartialState> + 'a
where
    Input: RangeStream<Token = char, Range = &'a str> + 'a,
    // Necessary due to rust-lang/rust#24159
    Input::Error: ParseError<Input::Token, Input::Range, Input::Position>,
{
    let content_length = range("Content-Length: ").with(
        range::recognize(skip_many1(digit())).and_then(|digits: &str| {
            // Convert the error from `.parse` into an error combine understands
            digits
                .parse::<usize>()
                .map_err(StreamErrorFor::<Input>::other)
        }),
    );

    any_send_partial_state(
        (
            skip_many(range("\r\n")),
            content_length,
            range("\r\n\r\n").map(|_| ()),
        )
            .then_partial(|&mut (_, message_length, _)| {
                take(message_length).map(|bytes: &str| bytes.to_owned())
            }),
    )
}

quickcheck! {
    fn many1_skip_test(seq: PartialWithErrors<GenWouldBlock>) -> () {

        let input = "123\r\n\
                     456\r\n\
                     1\r\n\
                     5\r\n\
                     666666\r\n";

        let result = run_decoder(input, seq, Basic::default());

        assert!(result.as_ref().is_ok(), "{}", result.unwrap_err());
        assert_eq!(
            result.unwrap(),
            vec!["123".to_string(), "456".to_string(), "1".to_string(), "5".to_string(), "666666".to_string()]
        );
    }

    fn prefix_many_then_test(seq: PartialWithErrors<GenWouldBlock>) -> () {
        impl_decoder!{ TestParser, String, prefix_many_then_parser() }

        let input = "# 1a\
                     # 4abcd\
                     #0\
                     #3:?a\
                     #10abcdefghij";

        let result = run_decoder(input, seq, TestParser::default());

        assert!(result.as_ref().is_ok(), "{}", result.unwrap_err());
        assert_eq!(
            result.unwrap(),
            ["a", "abcd", "", ":?a", "abcdefghij"]
        );
    }

    fn choice_test(seq: PartialWithErrors<GenWouldBlock>) -> () {
        impl_decoder!{ TestParser, String, choice_parser() }

        let input = "1\r\n\
                     abcd\r\n\
                     123\r\n\
                     abc\r\n\
                     1232751\r\n";

        let result = run_decoder(input, seq, TestParser::default());

        assert!(result.as_ref().is_ok(), "{}", result.unwrap_err());
        assert_eq!(
            result.unwrap(),
            ["1", "abcd", "123", "abc", "1232751"]
        );
    }

    fn recognize_test(seq: PartialWithErrors<GenWouldBlock>) -> () {
        impl_decoder!{ TestParser, String,
            recognize(
                (skip_many1(digit()), optional((char('.'), skip_many(digit()))))
            )
                .skip(range(&"\r\n"[..]))
        }

        let input = "1.0\r\n\
                     123.123\r\n\
                     17824\r\n\
                     3.14\r\n\
                     1.\r\n\
                     2\r\n";

        let result = run_decoder(input, seq, TestParser::default());

        assert!(result.as_ref().is_ok(), "{}", result.unwrap_err());
        assert_eq!(
            result.unwrap(),
            ["1.0", "123.123", "17824", "3.14", "1.", "2"]
        );
    }

    fn recognize_range_test(seq: PartialWithErrors<GenWouldBlock>) -> () {
        impl_decoder!{ TestParser, String,
            recognize_with_value(
                (skip_many1(digit()), optional((char('.'), skip_many(digit()))))
            )
                .map(|(r, _)| String::from(r))
                .skip(range(&"\r\n"[..]))
        }

        let input = "1.0\r\n\
                     123.123\r\n\
                     17824\r\n\
                     3.14\r\n\
                     1.\r\n\
                     2\r\n";

        let result = run_decoder(input, seq, TestParser::default());

        assert!(result.as_ref().is_ok(), "{}", result.unwrap_err());
        assert_eq!(
            result.unwrap(),
            ["1.0", "123.123", "17824", "3.14", "1.", "2"]
        );
    }

    fn take_while_test(seq: PartialWithErrors<GenWouldBlock>) -> () {
        impl_decoder!{ TestParser, String,
            |counter: Rc<Cell<i32>>|
                take_while(move |c| { counter.set(counter.get() + 1); c != '\r' })
                    .map(String::from)
                    .skip(range("\r\n")),
            Rc<Cell<i32>>
        }

        let input = "1.0\r\n\
                     123.123\r\n\
                     17824\r\n\
                     3.14\r\n\
                     \r\n\
                     2\r\n";

        let counter = Rc::new(Cell::new(0));
        let result = run_decoder(input, seq, TestParser(Default::default(), counter.clone()));

        assert!(result.as_ref().is_ok(), "{}", result.unwrap_err());
        assert_eq!(
            result.unwrap(),
            ["1.0", "123.123", "17824", "3.14", "", "2"]
        );

        assert_eq!(counter.get(), 26);
    }

    fn take_while1_test(seq: PartialWithErrors<GenWouldBlock>) -> () {
        impl_decoder!{ TestParser, String,
            |count: Rc<Cell<i32>>|
                take_while1(move |c| { count.set(count.get() + 1); c != '\r' })
                    .map(String::from)
                    .skip(range("\r\n")),
            Rc<Cell<i32>>
        }

        let input = "1.0\r\n\
                     123.123\r\n\
                     17824\r\n\
                     3.14\r\n\
                     1.\r\n\
                     2\r\n";

        let counter = Rc::new(Cell::new(0));
        let result = run_decoder(input, seq, TestParser(Default::default(), counter.clone()));

        assert!(result.as_ref().is_ok(), "{}", result.unwrap_err());
        assert_eq!(
            result.unwrap(),
            ["1.0", "123.123", "17824", "3.14", "1.", "2"]
        );

        assert_eq!(counter.get(), 28);
    }

    fn take_until(seq: PartialWithErrors<GenWouldBlock>) -> () {
        impl_decoder!{ TestParser, String,
            |count: Rc<Cell<i32>>|
                repeat::take_until(token(',').map(move |_| count.set(count.get() + 1))).skip(token(',')),
            Rc<Cell<i32>>
        }

        let input = "123,456,789,";

        let counter = Rc::new(Cell::new(0));
        let result = run_decoder(input, seq, TestParser(Default::default(), counter.clone()));

        assert!(result.as_ref().is_ok(), "{}", result.unwrap_err());
        assert_eq!(
            result.unwrap(),
            ["123", "456", "789"]
        );

        assert_eq!(counter.get(), 3);
    }

    fn take_until_consumed(seq: PartialWithErrors<GenWouldBlock>) -> () {
        impl_decoder!{ TestParser, String,
            |count: Rc<Cell<i32>>| {
                let end = attempt((token(':').map(move |_| count.set(count.get() + 1)), token(':')));
                repeat::take_until(end).skip((token(':'), token(':')))
            },
            Rc<Cell<i32>>
        }

        let input = "123::456::789::";

        let counter = Rc::new(Cell::new(0));
        let result = run_decoder(input, seq, TestParser(Default::default(), counter.clone()));

        assert!(result.as_ref().is_ok(), "{}", result.unwrap_err());
        assert_eq!(
            result.unwrap(),
            ["123", "456", "789"]
        );

        assert_eq!(counter.get(), 3);
    }

    fn take_until_range_consumed(seq: PartialWithErrors<GenWouldBlock>) -> () {
        impl_decoder!{ TestParser, String,
            take_until_range("::").map(String::from).skip((token(':'), token(':')))
        }

        let input = "123::456::789::";

        let result = run_decoder(input, seq, TestParser(Default::default()));

        assert!(result.as_ref().is_ok(), "{}", result.unwrap_err());
        assert_eq!(result.unwrap(), ["123", "456", "789"]);
    }

    fn any_send_partial_state_do_not_forget_state(sizes: Vec<usize>, seq: PartialWithErrors<GenWouldBlock>) -> () {
        impl_decoder!{ TestParser, usize,
            any_send_partial_state(content_length().map(|bytes| bytes.len()))
        }

        let input : String = sizes
            .iter()
            .map(|s| {
                format!(
                    "Content-Length: {}\r\n\r\n{}\r\n",
                    s,
                    ::std::iter::repeat('a').take(*s).collect::<String>()
                )
            })
            .collect();

        let result = run_decoder(input.as_bytes(), seq, TestParser(Default::default()));

        assert!(result.as_ref().is_ok(), "{}", result.unwrap_err());
        assert_eq!(result.unwrap(), sizes);
    }

    fn take_fn_test(sizes: Vec<usize>, seq: PartialWithErrors<GenWouldBlock>) -> () {
        impl_decoder!{ TestParser, usize,
            take_fn(|s: &str| s.find("\r\n")).map(|bytes: &str| bytes.parse::<usize>().unwrap()).skip(take(2))
        }

        let input : String = sizes
            .iter()
            .map(|s| {
                format!(
                    "{}\r\n",
                    s,
                )
            })
            .collect();

        let result = run_decoder(input.as_bytes(), seq, TestParser(Default::default()));

        assert!(result.as_ref().is_ok(), "{}", result.unwrap_err());
        assert_eq!(result.unwrap(), sizes);
    }

    fn take_until_bytes_test(sizes: Vec<usize>, seq: PartialWithErrors<GenWouldBlock>) -> () {
        impl_decoder!{ TestParser, usize,
            take_until_bytes("\r\n".as_bytes())
                .map(|bytes: &str| bytes.parse::<usize>().unwrap())
                .skip(take(2))
        }

        let input : String = sizes
            .iter()
            .map(|s| {
                format!(
                    "{}\r\n",
                    s,
                )
            })
            .collect();

        let result = run_decoder(input.as_bytes(), seq, TestParser(Default::default()));

        assert!(result.as_ref().is_ok(), "{}", result.unwrap_err());
        assert_eq!(result.unwrap(), sizes);
    }

    fn num_test(ints: Vec<u16>, seq: PartialWithErrors<GenWouldBlock>) -> () {
        impl_byte_decoder!{ TestParser, u16,
            num::be_u16()
                .skip(take(2))
        }

        let input: Vec<u8> = ints.iter()
            .flat_map(|i| {
                let mut v = Vec::new();
                v.extend_from_slice(&i.to_be_bytes());
                v.extend_from_slice(b"\r\n");
                v
            })
            .collect();

        let result = run_decoder(&input, seq, TestParser(Default::default()));

        assert!(result.as_ref().is_ok(), "{}", result.unwrap_err());
        assert_eq!(result.unwrap(), ints);
    }

    fn sep_end_by_test(seq: PartialWithErrors<GenWouldBlock>) -> () {
        impl_decoder!{ TestParser, Vec<String>,
            repeat::sep_end_by((digit(), digit(), digit()).map(|(a, b, c)| vec![a, b, c].into_iter().collect()), no_partial(string("::")))
                .skip(no_partial(string("\r\n")))
        }

        let input = "123::456::789::\r\n";

        let result = run_decoder(&input, seq, TestParser(Default::default()));

        assert!(result.as_ref().is_ok(), "{}", result.unwrap_err());
        assert_eq!(result.unwrap(), vec![vec!["123".to_string(), "456".to_string(), "789".to_string()]]);
    }
}

#[test]
fn skip_count_min_max_test() {
    let seq = vec![PartialOp::Limited(1)];
    impl_decoder! { TestParser, String,
        repeat::skip_count_min_max(1, 2, char('_')).skip(char('.')).map(|_| "".to_string())
    }

    let input = "_.";

    let result = run_decoder(input, seq, TestParser::default());

    assert!(result.as_ref().is_ok(), "{}", result.unwrap_err());
    assert_eq!(result.unwrap(), [""]);
}

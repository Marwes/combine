use std::marker::PhantomData;

use primitives::{ConsumedResult, Parser, ParsingError, RangeStream, SimpleInfo, StreamOnce,
                 Tracked};
use primitives::FastResult::*;

pub struct Range<I>(I::Range)
where
    I: RangeStream;

impl<I> Parser for Range<I>
where
    I: RangeStream,
    I::Range: PartialEq + ::primitives::Range,
{
    type Input = I;
    type Output = I::Range;

    #[inline]
    fn parse_lazy(&mut self, mut input: Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        use primitives::Range;
        let position = input.position();
        match input.uncons_range(self.0.len()) {
            Ok(other) => if other == self.0 {
                ConsumedOk((other, input))
            } else {
                EmptyErr(I::Error::empty(position).into())
            },
            Err(err) => EmptyErr(err.into()),
        }
    }
    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        // TODO Add unexpected message?
        errors.error.add_expected(SimpleInfo::Range(self.0.clone()));
    }
}

parser!{
    #[derive(Clone)]
    pub struct Recognize;
    /// Zero-copy parser which returns consumed input range.
    ///
    /// ```
    /// # extern crate combine;
    /// # use combine::range::recognize;
    /// # use combine::char::letter;
    /// # use combine::*;
    /// # fn main() {
    /// let mut parser = recognize(skip_many1(letter()));
    /// assert_eq!(parser.parse("hello world"), Ok(("hello", " world")));
    /// assert!(parser.parse("!").is_err());
    /// # }
    /// ```
    #[inline(always)]
    pub fn recognize[P](parser: P)(P::Input) -> <P::Input as StreamOnce>::Range
    where [
        P: Parser,
        P::Input: RangeStream,
        <P::Input as StreamOnce>::Range: ::primitives::Range,
    ]
    {
        ::range::recognize_with_value(parser).map(|(range, _)| range)
    }
}

#[derive(Clone)]
pub struct RecognizeWithValue<P>(P);

impl<P> Parser for RecognizeWithValue<P>
where
    P: Parser,
    P::Input: RangeStream,
    <P::Input as StreamOnce>::Range: ::primitives::Range,
{
    type Input = P::Input;
    type Output = (<P::Input as StreamOnce>::Range, P::Output);

    #[inline]
    fn parse_lazy(&mut self, input: Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        let (value, new_input) = ctry!(self.0.parse_lazy(input.clone()));
        let distance = input.distance(&new_input.into_inner());
        take(distance).parse_lazy(input).map(|range| (range, value))
    }
    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.0.add_error(errors)
    }
}

/// Zero-copy parser which returns a pair: (consumed input range, parsed value).
///
/// ```
/// # extern crate combine;
/// # use combine::range::recognize_with_value;
/// # use combine::char::{digit, char};
/// # use combine::*;
/// # fn main() {
/// let mut parser = recognize_with_value((
///     skip_many1(digit()),
///     optional((try(char('.')), skip_many1(digit()))),
/// ).map(|(_, opt)| opt.is_some()));
///
/// assert_eq!(parser.parse("1234!"), Ok((("1234", false), "!")));
/// assert_eq!(parser.parse("1234.0001!"), Ok((("1234.0001", true), "!")));
/// assert!(parser.parse("!").is_err());
/// assert!(parser.parse("1234.").is_err());
/// # }
/// ```
#[inline(always)]
pub fn recognize_with_value<P>(parser: P) -> RecognizeWithValue<P>
where
    P: Parser,
    P::Input: RangeStream,
    <P::Input as StreamOnce>::Range: ::primitives::Range,
{
    RecognizeWithValue(parser)
}

/// Zero-copy parser which reads a range of length `i.len()` and succeds if `i` is equal to that
/// range.
///
/// ```
/// # extern crate combine;
/// # use combine::range::range;
/// # use combine::*;
/// # fn main() {
/// let mut parser = range("hello");
/// let result = parser.parse("hello world");
/// assert_eq!(result, Ok(("hello", " world")));
/// let result = parser.parse("hel world");
/// assert!(result.is_err());
/// # }
/// ```
#[inline(always)]
pub fn range<I>(i: I::Range) -> Range<I>
where
    I: RangeStream,
    I::Range: PartialEq + ::primitives::Range,
{
    Range(i)
}

pub struct Take<I>(usize, PhantomData<fn(I) -> I>);
impl<I> Parser for Take<I>
where
    I: RangeStream,
    I::Range: ::primitives::Range,
{
    type Input = I;
    type Output = I::Range;

    #[inline]
    fn parse_lazy(&mut self, mut input: Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        let position = input.position();
        match input.uncons_range(self.0) {
            Ok(x) => ConsumedOk((x, input)),
            Err(err) => EmptyErr(I::Error::empty(position).merge(err).into()),
        }
    }
}

/// Zero-copy parser which reads a range of length `n`.
///
/// ```
/// # extern crate combine;
/// # use combine::range::take;
/// # use combine::*;
/// # fn main() {
/// let mut parser = take(1);
/// let result = parser.parse("1");
/// assert_eq!(result, Ok(("1", "")));
/// let mut parser = take(4);
/// let result = parser.parse("123abc");
/// assert_eq!(result, Ok(("123a", "bc")));
/// let result = parser.parse("abc");
/// assert!(result.is_err());
/// # }
/// ```
#[inline(always)]
pub fn take<I>(n: usize) -> Take<I>
where
    I: RangeStream,
    I::Range: ::primitives::Range,
{
    Take(n, PhantomData)
}

pub struct TakeWhile<I, F>(F, PhantomData<fn(I) -> I>);
impl<I, F> Parser for TakeWhile<I, F>
where
    I: RangeStream,
    I::Range: ::primitives::Range,
    F: FnMut(I::Item) -> bool,
{
    type Input = I;
    type Output = I::Range;

    #[inline]
    fn parse_lazy(&mut self, input: Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        ::primitives::uncons_while(input, &mut self.0)
    }
}

/// Zero-copy parser which reads a range of 0 or more tokens which satisfy `f`.
///
/// ```
/// # extern crate combine;
/// # use combine::range::take_while;
/// # use combine::*;
/// # fn main() {
/// let mut parser = take_while(|c: char| c.is_digit(10));
/// let result = parser.parse("123abc");
/// assert_eq!(result, Ok(("123", "abc")));
/// let result = parser.parse("abc");
/// assert_eq!(result, Ok(("", "abc")));
/// # }
/// ```
#[inline(always)]
pub fn take_while<I, F>(f: F) -> TakeWhile<I, F>
where
    I: RangeStream,
    F: FnMut(I::Item) -> bool,
{
    TakeWhile(f, PhantomData)
}

pub struct TakeWhile1<I, F>(F, PhantomData<fn(I) -> I>);
impl<I, F> Parser for TakeWhile1<I, F>
where
    I: RangeStream,
    I::Range: ::primitives::Range,
    F: FnMut(I::Item) -> bool,
{
    type Input = I;
    type Output = I::Range;

    #[inline]
    fn parse_lazy(&mut self, input: Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        match ::primitives::uncons_while(input, &mut self.0) {
            ConsumedOk((v, input)) => ConsumedOk((v, input)),
            EmptyOk((_, input)) => {
                let position = input.position();
                EmptyErr(I::Error::empty(position).into())
            }
            EmptyErr(err) => EmptyErr(err),
            ConsumedErr(err) => ConsumedErr(err),
        }
    }
}

/// Zero-copy parser which reads a range of 1 or more tokens which satisfy `f`.
///
/// ```
/// # extern crate combine;
/// # use combine::range::take_while1;
/// # use combine::*;
/// # fn main() {
/// let mut parser = take_while1(|c: char| c.is_digit(10));
/// let result = parser.parse("123abc");
/// assert_eq!(result, Ok(("123", "abc")));
/// let result = parser.parse("abc");
/// assert!(result.is_err());
/// # }
/// ```
#[inline(always)]
pub fn take_while1<I, F>(f: F) -> TakeWhile1<I, F>
where
    I: RangeStream,
    I::Range: ::primitives::Range,
    F: FnMut(I::Item) -> bool,
{
    TakeWhile1(f, PhantomData)
}

pub struct TakeUntilRange<I>(I::Range)
where
    I: RangeStream;
impl<I> Parser for TakeUntilRange<I>
where
    I: RangeStream,
    I::Range: PartialEq + ::primitives::Range,
{
    type Input = I;
    type Output = I::Range;

    #[inline]
    fn parse_lazy(&mut self, mut input: Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        use primitives::Range;

        let len = self.0.len();
        let mut to_consume = 0;
        let mut look_ahead_input = input.clone();

        loop {
            match look_ahead_input.clone().uncons_range(len) {
                Ok(xs) => {
                    if xs == self.0 {
                        if let Ok(consumed) = input.uncons_range(to_consume) {
                            if to_consume == 0 {
                                return EmptyOk((consumed, input));
                            } else {
                                return ConsumedOk((consumed, input));
                            }
                        }

                        // We are guaranteed able to uncons to_consume characters here
                        // because we've already done it on look_ahead_input.
                        unreachable!();
                    } else {
                        to_consume += 1;
                        if look_ahead_input.uncons().is_err() {
                            unreachable!();
                        }
                    }
                }
                Err(e) => return EmptyErr(e.into()),
            };
        }
    }
}


/// Zero-copy parser which reads a range of 0 or more tokens until `r` is found.
///
/// The range `r` will not be consumed. If `r` is not found, the parser will
/// return an error.
///
/// ```
/// # extern crate combine;
/// # use combine::range::{range, take_until_range};
/// # use combine::*;
/// # fn main() {
/// let mut parser = take_until_range("\r\n");
/// let result = parser.parse("To: user@example.com\r\n");
/// assert_eq!(result, Ok(("To: user@example.com", "\r\n")));
/// let result = parser.parse("Hello, world\n");
/// assert!(result.is_err());
/// # }
/// ```
#[inline(always)]
pub fn take_until_range<I>(r: I::Range) -> TakeUntilRange<I>
where
    I: RangeStream,
{
    TakeUntilRange(r)
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::Parser;

    #[test]
    fn take_while_test() {
        let result = take_while(|c: char| c.is_digit(10)).parse("123abc");
        assert_eq!(result, Ok(("123", "abc")));
        let result = take_while(|c: char| c.is_digit(10)).parse("abc");
        assert_eq!(result, Ok(("", "abc")));
    }

    #[test]
    fn take_while1_test() {
        let result = take_while1(|c: char| c.is_digit(10)).parse("123abc");
        assert_eq!(result, Ok(("123", "abc")));
        let result = take_while1(|c: char| c.is_digit(10)).parse("abc");
        assert!(result.is_err());
    }

    #[test]
    fn range_string_no_char_boundary_error() {
        let mut parser = range("hello");
        let result = parser.parse("hell\u{00EE} world");
        assert!(result.is_err());
    }
}

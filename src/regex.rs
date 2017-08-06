extern crate regex;

use std::iter::FromIterator;
use std::marker::PhantomData;

use primitives::{ConsumedResult, FullRangeStream, Parser, ParseError};
use primitives::FastResult::*;
use range::take;

pub trait MatchFind {
    type Range;
    fn end(&self) -> usize;
    fn as_match(&self) -> Self::Range;
}

impl<'t> MatchFind for self::regex::Match<'t> {
    type Range = &'t str;
    fn end(&self) -> usize {
        self::regex::Match::end(self)
    }
    fn as_match(&self) -> Self::Range {
        self.as_str()
    }
}

impl<'t> MatchFind for self::regex::bytes::Match<'t> {
    type Range = &'t [u8];
    fn end(&self) -> usize {
        self::regex::bytes::Match::end(self)
    }
    fn as_match(&self) -> Self::Range {
        self.as_bytes()
    }
}

pub trait Regex<Range> {
    fn is_match(&self, range: Range) -> bool;
    fn find_iter<F>(&self, range: Range) -> (usize, F) where F: FromIterator<Range>;
}

impl<'a, R, Range> Regex<Range> for &'a R where R: Regex<Range> {
    fn is_match(&self, range: Range) -> bool {
        (**self).is_match(range)
    }
    fn find_iter<F>(&self, range: Range) -> (usize, F) where F: FromIterator<Range> {
        (**self).find_iter(range)
    }
}

impl<'a> Regex<&'a str> for self::regex::Regex {
    fn is_match(&self, range: &'a str) -> bool {
        self::regex::Regex::is_match(self, range)
    }
    fn find_iter<F>(&self, range: &'a str) -> (usize, F) where F: FromIterator<&'a str> {
        let mut end = 0;
        let value = self::regex::Regex::find_iter(self, range).map(|m| {
            end = m.end();
            m.as_match()
        })
        .collect();
        (end, value)
    }
}

impl<'a> Regex<&'a [u8]> for self::regex::bytes::Regex {
    fn is_match(&self, range: &'a [u8]) -> bool {
        self::regex::bytes::Regex::is_match(self, range)
    }
    fn find_iter<F>(&self, range: &'a [u8]) -> (usize, F) where F: FromIterator<&'a [u8]> {
        let mut end = 0;
        let value = self::regex::bytes::Regex::find_iter(self, range).map(|m| {
            end = m.end();
            m.as_match()
        })
        .collect();
        (end, value)
    }
}


pub struct Match<R, I>(R, PhantomData<I>);

impl<'a, R, I> Parser for Match<R, I>
where
    R: Regex<I::Range>,
    I: FullRangeStream,
{
    type Input = I;
    type Output = I::Range;

    #[inline]
    fn parse_lazy(&mut self, input: Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        if self.0.is_match(input.range()) {
            EmptyOk((input.range(), input))
        } else {
            EmptyErr(ParseError::empty(input.position()))
        }
    }
}

/// Matches `regex` on the input returning the entire input if it matches.
/// Never consumes any input.
pub fn match_<R, I>(regex: R) -> Match<R, I>
where
    R: Regex<I::Range>,
    I: FullRangeStream,
{
    Match(regex, PhantomData)
}

pub struct FindMany<F, R, I>(R, PhantomData<fn () -> (I, F)>);

impl<'a, F, R, I> Parser for FindMany<F, R, I>
where
    F: FromIterator<I::Range>,
    R: Regex<I::Range>,
    I: FullRangeStream,
    I::Range: ::primitives::Range,
{
    type Input = I;
    type Output = F;

    #[inline]
    fn parse_lazy(&mut self, input: Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        let (end, value) = self.0.find_iter(input.range());
        take(end).parse_lazy(input).map(|_| value)
    }
}

/// Matches `regex` on the input by running `find_iter` on the input.
/// Returns all matches in a `F: FromIterator<I::Range>`.
/// Consumes all input up until the end of the last match.
///
/// ```
/// extern crate regex;
/// extern crate combine;
/// use regex::Regex;
/// use regex::bytes;
/// use combine::Parser;
/// use combine::regex::find_many;
///
/// fn main() {
///     let mut digits = find_many(Regex::new("[0-9]+").unwrap());
///     assert_eq!(digits.parse("123 456 "), Ok((vec!["123", "456"], " ")));
///     assert_eq!(digits.parse("abc 123 456 "), Ok((vec!["123", "456"], " ")));
///     assert_eq!(digits.parse("abc"), Ok((vec![], "abc")));
/// 
///     let regex = bytes::Regex::new("[0-9]+").unwrap();
///     // Shared references to any regex works as well
///     assert_eq!(
///         find_many(&regex).parse(&b"123 456 "[..]),
///         Ok((vec![&b"123"[..], &b"456"[..]], &b" "[..]))
///     );
///     assert_eq!(
///         find_many(regex).parse(&b""[..]),
///         Ok((vec![], &b""[..]))
///     );
/// }
/// ```
pub fn find_many<F, R, I>(regex: R) -> FindMany<F, R, I>
where
    F: FromIterator<I::Range>,
    R: Regex<I::Range>,
    I: FullRangeStream,
    I::Range: ::primitives::Range,
{
    FindMany(regex, PhantomData)
}
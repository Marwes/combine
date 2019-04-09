//! Module containing regex parsers on streams returning ranges of `&str` or `&[u8]`.
//!
//! All regex parsers are overloaded on `&str` and `&[u8]` ranges and can take a `Regex` by value
//! or shared reference (`&`).
//!
//! Enabled using the `regex` feature (for `regex-0.2`) or the `regex-1` feature for `regex-1.0`.
//!
//! ```
//! extern crate regex;
//! #[macro_use]
//! extern crate lazy_static;
//! extern crate combine;
//! use regex::{bytes, Regex};
//! use combine::Parser;
//! use combine::parser::regex::{find_many, match_};
//!
//! fn main() {
//!     let regex = bytes::Regex::new("[0-9]+").unwrap();
//!     // Shared references to any regex works as well
//!     assert_eq!(
//!         find_many(&regex).parse(&b"123 456 "[..]),
//!         Ok((vec![&b"123"[..], &b"456"[..]], &b" "[..]))
//!     );
//!     assert_eq!(
//!         find_many(regex).parse(&b""[..]),
//!         Ok((vec![], &b""[..]))
//!     );
//!
//!     lazy_static! { static ref REGEX: Regex = Regex::new("[:alpha:]+").unwrap(); }
//!     assert_eq!(
//!         match_(&*REGEX).parse("abc123"),
//!         Ok(("abc123", "abc123"))
//!     );
//! }
//! ```

use std::iter::FromIterator;
use std::marker::PhantomData;

use error::FastResult::*;
use error::{ConsumedResult, ParseError, StreamError, Tracked};
use parser::range::take;
use stream::{FullRangeStream, StreamOnce};
use Parser;

struct First<T>(Option<T>);

impl<A> FromIterator<A> for First<A> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = A>,
    {
        First(iter.into_iter().next())
    }
}

pub trait MatchFind {
    type Range;
    fn end(&self) -> usize;
    fn as_match(&self) -> Self::Range;
}

pub trait Regex<Range> {
    fn is_match(&self, range: Range) -> bool;
    fn find_iter<F>(&self, range: Range) -> (usize, F)
    where
        F: FromIterator<Range>;
    fn captures<F, G>(&self, range: Range) -> (usize, G)
    where
        F: FromIterator<Range>,
        G: FromIterator<F>;
    fn as_str(&self) -> &str;
}

impl<'a, R, Range> Regex<Range> for &'a R
where
    R: Regex<Range>,
{
    fn is_match(&self, range: Range) -> bool {
        (**self).is_match(range)
    }
    fn find_iter<F>(&self, range: Range) -> (usize, F)
    where
        F: FromIterator<Range>,
    {
        (**self).find_iter(range)
    }
    fn captures<F, G>(&self, range: Range) -> (usize, G)
    where
        F: FromIterator<Range>,
        G: FromIterator<F>,
    {
        (**self).captures(range)
    }
    fn as_str(&self) -> &str {
        (**self).as_str()
    }
}

fn find_iter<'a, I, F>(iterable: I) -> (usize, F)
where
    I: IntoIterator,
    I::Item: MatchFind,
    F: FromIterator<<I::Item as MatchFind>::Range>,
{
    let mut end = 0;
    let value = iterable
        .into_iter()
        .map(|m| {
            end = m.end();
            m.as_match()
        })
        .collect();
    (end, value)
}

#[cfg(feature = "regex")]
mod regex {
    pub extern crate regex;

    use std::iter::FromIterator;

    pub use self::regex::*;

    use super::{find_iter, MatchFind, Regex};

    impl<'t> MatchFind for regex::Match<'t> {
        type Range = &'t str;
        fn end(&self) -> usize {
            regex::Match::end(self)
        }
        fn as_match(&self) -> Self::Range {
            self.as_str()
        }
    }

    impl<'t> MatchFind for regex::bytes::Match<'t> {
        type Range = &'t [u8];
        fn end(&self) -> usize {
            regex::bytes::Match::end(self)
        }
        fn as_match(&self) -> Self::Range {
            self.as_bytes()
        }
    }

    impl<'a> Regex<&'a str> for regex::Regex {
        fn is_match(&self, range: &'a str) -> bool {
            regex::Regex::is_match(self, range)
        }
        fn find_iter<F>(&self, range: &'a str) -> (usize, F)
        where
            F: FromIterator<&'a str>,
        {
            find_iter(regex::Regex::find_iter(self, range))
        }
        fn captures<F, G>(&self, range: &'a str) -> (usize, G)
        where
            F: FromIterator<&'a str>,
            G: FromIterator<F>,
        {
            let mut end = 0;
            let value = regex::Regex::captures_iter(self, range)
                .map(|captures| {
                    let mut captures_iter = captures.iter();
                    // The first group is the match on the entire regex
                    let first_match = captures_iter.next().unwrap().unwrap();
                    end = first_match.end();
                    Some(Some(first_match))
                        .into_iter()
                        .chain(captures_iter)
                        .filter_map(|match_| match_.map(|m| m.as_match()))
                        .collect()
                })
                .collect();
            (end, value)
        }
        fn as_str(&self) -> &str {
            regex::Regex::as_str(self)
        }
    }

    impl<'a> Regex<&'a [u8]> for regex::bytes::Regex {
        fn is_match(&self, range: &'a [u8]) -> bool {
            regex::bytes::Regex::is_match(self, range)
        }
        fn find_iter<F>(&self, range: &'a [u8]) -> (usize, F)
        where
            F: FromIterator<&'a [u8]>,
        {
            find_iter(regex::bytes::Regex::find_iter(self, range))
        }
        fn captures<F, G>(&self, range: &'a [u8]) -> (usize, G)
        where
            F: FromIterator<&'a [u8]>,
            G: FromIterator<F>,
        {
            let mut end = 0;
            let value = regex::bytes::Regex::captures_iter(self, range)
                .map(|captures| {
                    let mut captures_iter = captures.iter();
                    // The first group is the match on the entire regex
                    let first_match = captures_iter.next().unwrap().unwrap();
                    end = first_match.end();
                    Some(Some(first_match))
                        .into_iter()
                        .chain(captures_iter)
                        .filter_map(|match_| match_.map(|m| m.as_match()))
                        .collect()
                })
                .collect();
            (end, value)
        }
        fn as_str(&self) -> &str {
            regex::bytes::Regex::as_str(self)
        }
    }
}

#[cfg(feature = "regex-1")]
mod regex_1 {
    pub extern crate combine_regex_1 as regex_1;

    use std::iter::FromIterator;

    pub use self::regex_1::*;

    use super::{find_iter, MatchFind, Regex};

    impl<'t> MatchFind for regex_1::Match<'t> {
        type Range = &'t str;
        fn end(&self) -> usize {
            regex_1::Match::end(self)
        }
        fn as_match(&self) -> Self::Range {
            self.as_str()
        }
    }

    impl<'t> MatchFind for regex_1::bytes::Match<'t> {
        type Range = &'t [u8];
        fn end(&self) -> usize {
            regex_1::bytes::Match::end(self)
        }
        fn as_match(&self) -> Self::Range {
            self.as_bytes()
        }
    }

    impl<'a> Regex<&'a str> for regex_1::Regex {
        fn is_match(&self, range: &'a str) -> bool {
            regex_1::Regex::is_match(self, range)
        }
        fn find_iter<F>(&self, range: &'a str) -> (usize, F)
        where
            F: FromIterator<&'a str>,
        {
            find_iter(regex_1::Regex::find_iter(self, range))
        }
        fn captures<F, G>(&self, range: &'a str) -> (usize, G)
        where
            F: FromIterator<&'a str>,
            G: FromIterator<F>,
        {
            let mut end = 0;
            let value = regex_1::Regex::captures_iter(self, range)
                .map(|captures| {
                    let mut captures_iter = captures.iter();
                    // The first group is the match on the entire regex
                    let first_match = captures_iter.next().unwrap().unwrap();
                    end = first_match.end();
                    Some(Some(first_match))
                        .into_iter()
                        .chain(captures_iter)
                        .filter_map(|match_| match_.map(|m| m.as_match()))
                        .collect()
                })
                .collect();
            (end, value)
        }
        fn as_str(&self) -> &str {
            regex_1::Regex::as_str(self)
        }
    }

    impl<'a> Regex<&'a [u8]> for regex_1::bytes::Regex {
        fn is_match(&self, range: &'a [u8]) -> bool {
            regex_1::bytes::Regex::is_match(self, range)
        }
        fn find_iter<F>(&self, range: &'a [u8]) -> (usize, F)
        where
            F: FromIterator<&'a [u8]>,
        {
            find_iter(regex_1::bytes::Regex::find_iter(self, range))
        }
        fn captures<F, G>(&self, range: &'a [u8]) -> (usize, G)
        where
            F: FromIterator<&'a [u8]>,
            G: FromIterator<F>,
        {
            let mut end = 0;
            let value = regex_1::bytes::Regex::captures_iter(self, range)
                .map(|captures| {
                    let mut captures_iter = captures.iter();
                    // The first group is the match on the entire regex
                    let first_match = captures_iter.next().unwrap().unwrap();
                    end = first_match.end();
                    Some(Some(first_match))
                        .into_iter()
                        .chain(captures_iter)
                        .filter_map(|match_| match_.map(|m| m.as_match()))
                        .collect()
                })
                .collect();
            (end, value)
        }
        fn as_str(&self) -> &str {
            regex_1::bytes::Regex::as_str(self)
        }
    }
}

pub struct Match<R, I>(R, PhantomData<I>);

impl<'a, Input, R, I> Parser<Input> for Match<R, I>
where
    R: Regex<I::Range>,
    I: FullRangeStream,
{
    
    type Output = I::Range;
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Input) -> ConsumedResult<Self::Output, Input> {
        if self.0.is_match(input.range()) {
            EmptyOk(input.range())
        } else {
            EmptyErr(I::Error::empty(input.position()).into())
        }
    }
    fn add_error(&mut self, error: &mut Tracked<<Input as StreamOnce>::Error>) {
        error.error.add(StreamError::expected_message(format_args!(
            "/{}/",
            self.0.as_str()
        )))
    }
}

/// Matches `regex` on the input returning the entire input if it matches.
/// Never consumes any input.
///
/// ```
/// extern crate regex;
/// extern crate combine;
/// use regex::Regex;
/// use combine::Parser;
/// use combine::parser::regex::match_;
///
/// fn main() {
///     let regex = Regex::new("[:alpha:]+").unwrap();
///     assert_eq!(
///         match_(&regex).parse("abc123"),
///         Ok(("abc123", "abc123"))
///     );
/// }
/// ```
pub fn match_<R, I>(regex: R) -> Match<R, I>
where
    R: Regex<I::Range>,
    I: FullRangeStream,
{
    Match(regex, PhantomData)
}

#[derive(Clone)]
pub struct Find<R, I>(R, PhantomData<fn() -> I>);

impl<'a, Input, R, I> Parser<Input> for Find<R, I>
where
    R: Regex<I::Range>,
    I: FullRangeStream,
    I::Range: ::stream::Range,
{
    
    type Output = I::Range;
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Input) -> ConsumedResult<Self::Output, Input> {
        let (end, First(value)) = self.0.find_iter(input.range());
        match value {
            Some(value) => take(end).parse_lazy(input).map(|_| value),
            None => EmptyErr(I::Error::empty(input.position()).into()),
        }
    }
    fn add_error(&mut self, error: &mut Tracked<<Input as StreamOnce>::Error>) {
        error.error.add(StreamError::expected_message(format_args!(
            "/{}/",
            self.0.as_str()
        )))
    }
}

/// Matches `regex` on the input by running `find` on the input and returns the first match.
/// Consumes all input up until the end of the first match.
///
/// ```
/// extern crate regex;
/// extern crate combine;
/// use regex::Regex;
/// use combine::Parser;
/// use combine::parser::regex::find;
///
/// fn main() {
///     let mut digits = find(Regex::new("^[0-9]+").unwrap());
///     assert_eq!(digits.parse("123 456 "), Ok(("123", " 456 ")));
///     assert!(
///         digits.parse("abc 123 456 ").is_err());
///
///     let mut digits2 = find(Regex::new("[0-9]+").unwrap());
///     assert_eq!(digits2.parse("123 456 "), Ok(("123", " 456 ")));
///     assert_eq!(digits2.parse("abc 123 456 "), Ok(("123", " 456 ")));
/// }
/// ```
pub fn find<R, I>(regex: R) -> Find<R, I>
where
    R: Regex<I::Range>,
    I: FullRangeStream,
    I::Range: ::stream::Range,
{
    Find(regex, PhantomData)
}

#[derive(Clone)]
pub struct FindMany<F, R, I>(R, PhantomData<fn() -> (I, F)>);

impl<'a, Input, F, R, I> Parser<Input> for FindMany<F, R, I>
where
    F: FromIterator<I::Range>,
    R: Regex<I::Range>,
    I: FullRangeStream,
    I::Range: ::stream::Range,
{
    
    type Output = F;
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Input) -> ConsumedResult<Self::Output, Input> {
        let (end, value) = self.0.find_iter(input.range());
        take(end).parse_lazy(input).map(|_| value)
    }
    fn add_error(&mut self, error: &mut Tracked<<Input as StreamOnce>::Error>) {
        error.error.add(StreamError::expected_message(format_args!(
            "/{}/",
            self.0.as_str()
        )))
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
/// use combine::parser::regex::find_many;
///
/// fn main() {
///     let mut digits = find_many(Regex::new("[0-9]+").unwrap());
///     assert_eq!(digits.parse("123 456 "), Ok((vec!["123", "456"], " ")));
///     assert_eq!(digits.parse("abc 123 456 "), Ok((vec!["123", "456"], " ")));
///     assert_eq!(digits.parse("abc"), Ok((vec![], "abc")));
/// }
/// ```
pub fn find_many<F, R, I>(regex: R) -> FindMany<F, R, I>
where
    F: FromIterator<I::Range>,
    R: Regex<I::Range>,
    I: FullRangeStream,
    I::Range: ::stream::Range,
{
    FindMany(regex, PhantomData)
}

#[derive(Clone)]
pub struct Captures<F, R, I>(R, PhantomData<fn() -> (I, F)>);

impl<'a, Input, F, R, I> Parser<Input> for Captures<F, R, I>
where
    F: FromIterator<I::Range>,
    R: Regex<I::Range>,
    I: FullRangeStream,
    I::Range: ::stream::Range,
{
    
    type Output = F;
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Input) -> ConsumedResult<Self::Output, Input> {
        let (end, First(value)) = self.0.captures(input.range());
        match value {
            Some(value) => take(end).parse_lazy(input).map(|_| value),
            None => EmptyErr(I::Error::empty(input.position()).into()),
        }
    }
    fn add_error(&mut self, error: &mut Tracked<<Input as StreamOnce>::Error>) {
        error.error.add(StreamError::expected_message(format_args!(
            "/{}/",
            self.0.as_str()
        )))
    }
}

/// Matches `regex` on the input by running `captures_iter` on the input.
/// Returns the captures of the first match and consumes the input up until the end of that match.
///
/// ```
/// extern crate regex;
/// extern crate combine;
/// use regex::Regex;
/// use combine::Parser;
/// use combine::parser::regex::captures;
///
/// fn main() {
///     let mut fields = captures(Regex::new("([a-z]+):([0-9]+)").unwrap());
///     assert_eq!(
///         fields.parse("test:123 field:456 "),
///         Ok((vec!["test:123", "test", "123"],
///             " field:456 "
///         ))
///     );
///     assert_eq!(
///         fields.parse("test:123 :456 "),
///         Ok((vec!["test:123", "test", "123"],
///             " :456 "
///         ))
///     );
/// }
/// ```
pub fn captures<F, R, I>(regex: R) -> Captures<F, R, I>
where
    F: FromIterator<I::Range>,
    R: Regex<I::Range>,
    I: FullRangeStream,
    I::Range: ::stream::Range,
{
    Captures(regex, PhantomData)
}

#[derive(Clone)]
pub struct CapturesMany<F, G, R, I>(R, PhantomData<fn() -> (I, F, G)>);

impl<'a, Input, F, G, R, I> Parser<Input> for CapturesMany<F, G, R, I>
where
    F: FromIterator<I::Range>,
    G: FromIterator<F>,
    R: Regex<I::Range>,
    I: FullRangeStream,
    I::Range: ::stream::Range,
{
    
    type Output = G;
    type PartialState = ();

    #[inline]
    fn parse_lazy(&mut self, input: &mut Input) -> ConsumedResult<Self::Output, Input> {
        let (end, value) = self.0.captures(input.range());
        take(end).parse_lazy(input).map(|_| value)
    }
    fn add_error(&mut self, error: &mut Tracked<<Input as StreamOnce>::Error>) {
        error.error.add(StreamError::expected_message(format_args!(
            "/{}/",
            self.0.as_str()
        )))
    }
}

/// Matches `regex` on the input by running `captures_iter` on the input.
/// Returns all captures which is part of the match in a `F: FromIterator<I::Range>`.
/// Consumes all input up until the end of the last match.
///
/// ```
/// extern crate regex;
/// extern crate combine;
/// use regex::Regex;
/// use combine::Parser;
/// use combine::parser::regex::captures_many;
///
/// fn main() {
///     let mut fields = captures_many(Regex::new("([a-z]+):([0-9]+)").unwrap());
///     assert_eq!(
///         fields.parse("test:123 field:456 "),
///         Ok((vec![vec!["test:123", "test", "123"],
///                  vec!["field:456", "field", "456"]],
///             " "
///         ))
///     );
///     assert_eq!(
///         fields.parse("test:123 :456 "),
///         Ok((vec![vec!["test:123", "test", "123"]],
///             " :456 "
///         ))
///     );
/// }
/// ```
pub fn captures_many<F, G, R, I>(regex: R) -> CapturesMany<F, G, R, I>
where
    F: FromIterator<I::Range>,
    G: FromIterator<F>,
    R: Regex<I::Range>,
    I: FullRangeStream,
    I::Range: ::stream::Range,
{
    CapturesMany(regex, PhantomData)
}

#[cfg(all(test, feature = "regex-1"))]
mod tests {

    use parser::regex::find;
    use parser::regex::regex_1::regex_1::Regex;
    use Parser;

    #[test]
    fn test() {
        let mut digits = find(Regex::new("^[0-9]+").unwrap());
        assert_eq!(digits.parse("123 456 "), Ok(("123", " 456 ")));
        assert!(digits.parse("abc 123 456 ").is_err());

        let mut digits2 = find(Regex::new("[0-9]+").unwrap());
        assert_eq!(digits2.parse("123 456 "), Ok(("123", " 456 ")));
        assert_eq!(digits2.parse("abc 123 456 "), Ok(("123", " 456 ")));
    }
}

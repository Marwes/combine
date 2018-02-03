# combine
[![Build Status](https://travis-ci.org/Marwes/combine.svg?branch=master)](https://travis-ci.org/Marwes/combine) [![Docs v2](https://docs.rs/combine/badge.svg?version=^2)](https://docs.rs/combine/^2) [![Docs](https://docs.rs/combine/badge.svg)](https://docs.rs/combine) [![Gitter](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/Marwes/combine?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge)

An implementation of parser combinators for Rust, inspired by the Haskell library [Parsec](https://hackage.haskell.org/package/parsec). As in Parsec the parsers are [LL(1)](https://en.wikipedia.org/wiki/LL_parser) by default but they can opt-in to arbitrary lookahead using the [try  combinator](https://marwes.github.io/combine/combine/fn.try.html).

## Example

```rust
extern crate combine;
use combine::{many1, Parser, sep_by};
use combine::char::{letter, space};

let word = many1(letter());

let mut parser = sep_by(word, space())
    .map(|mut words: Vec<String>| words.pop());
let result = parser.parse("Pick up that word!");
assert_eq!(result, Ok((Some("word".to_string()), "!")));
```

Larger examples can be found in the [examples][], [tests][] and [benches][] folders.

[examples]:https://github.com/Marwes/combine/tree/master/examples
[tests]:https://github.com/Marwes/combine/tree/master/tests
[benches]:https://github.com/Marwes/combine/tree/master/benches

## Links

[Documentation and examples](https://docs.rs/crate/combine)

[crates.io](https://crates.io/crates/combine)

## About

A parser combinator is, broadly speaking, a function which takes several parsers as arguments and returns a new parser, created by combining those parsers. For instance, the [many](https://marwes.github.io/combine/combine/fn.many.html) parser takes one parser, `p`, as input and returns a new parser which applies `p` zero or more times. Thanks to the modularity that parser combinators gives it is possible to define parsers for a wide range of tasks without needing to implement the low level plumbing while still having the full power of Rust when you need it. 

The library adheres to [semantic versioning](http://semver.org).

If you end up trying it I welcome any feedback from your experience with it. I am usually reachable within a day by opening an issue, sending an email or posting a message on gitter.

## FAQ

### Why does my errors contain inscrutable positions?

Since `combine` aims to crate parsers with little to no overhead streams over `&str` and `&[T]` do not carry any extra position information but instead only rely on comparing the pointer of the buffer to check which `Stream` is further ahead than another `Stream`. To retrieve a better position, either call `translate_position` on the `PointerOffset` which represents the position or wrap your stream with `State`.

## Extra

There is an additional crate which has parsers to lex and parse programming languages in [combine-language](https://github.com/Marwes/combine-language).

You can find older versions of combine (parser-combinators) [here](https://crates.io/crates/parser-combinators).

## Contributing

Current master is the 3.0.0 branch. If you want to submit a fix or feature to the 2.x version of combine then
do so to the 2.x branch or submit the PR to master and request that it be backported.

The easiest way to contribute is to just open an issue about any problems you encounter using combine but if you are interested in adding something to the library here is a list of some of the easier things to work on to get started.

* __Add additional parsers__ There is a list of parsers which aren't implemented [here][add parsers] but if you have a suggestion for another parser just leave a suggestion on the issue itself.
* __Add additional examples__ More examples for using combine will always be useful!
* __Add and improve the docs__ Not the fanciest of work but one cannot overstate the importance of good documentation.

[add parsers]: https://github.com/Marwes/combine/issues/2

## Breaking changes

Here is a list containing most of the breaking changes in older versions of combine (parser-combinators).

A detailed list can be found in 

### 3.0.0-alpha.4

* Error handling has been completely rewritten to support `#![no_std]`. 
* `ParseError` is now `easy::Errors` and `StreamError` is now `easy::ParseError`.
* To keep using `ParseError` as the error type the `easy_parse` function should be used instead of `parse`.

See [CHANGELOG.md](https://github.com/Marwes/combine/blob/master/CHANGELOG.md) for a complete list of breaking changes.

### 3.0.0-alpha.1

* Deprecated items have been changed or removed. Upgrade to the latest version of 2.x first and fix all
    deprecations before upgrading to 3.x.
* If you have written the `ParseError<I>` explicitly it needs to be changed to `StreamError<I>` as
    `ParseError`s type signature have changed slightly. Function calls should not be affected however.
* Parsers now return `Tracked<StreamError<I>>` instead of plain `ParseError<I>`. `Tracked` is an internal
    wrapper which should just be constructed via `From::from` or `Into::into`. If you return errors explicitly
    somewhere you will need to add `.into()` on the errors to wrap them.
* A few other changes should be detected and fixed easily by simply compiling and fixing the compile errors.
    See [CHANGELOG.md](https://github.com/Marwes/combine/blob/master/CHANGELOG.md) for a complete list of breaking changes.

### 2.0.0-beta3

* `parse_state` renamed to `parse_stream`.
* `parse_lazy` changed to return a `ConsumedResult`. To make calls to `parse_lazy` return a `Result` you can call `parser.parse_lazy(input).into()`.
* `char::String` renamed to `char::Str` to avoid name collisions with `std::string::String`.
* The amount of reexports from the root module has been reduced.
* `ParserExt` removed, all methods now exist directly on `Parser`.
* `Stream` split into `Stream` and `StreamOnce`.
* `StreamOnce::uncons` now takes `&mut self` instead of `self`.
* `Position` added as an associated type on `StreamOnce`.

### 1.0.0
* `&[T]` streams has had the `Item` type changed from `&T` to `T` and requires a `T: Copy` bound. If you need the old behavior you can wrap the `&[T]` in the `SliceStream` newtype i.e `parser.parse(SliceStream(slice))`.

### 1.0.0-beta.3
* `Error::Unexpected` holds an `Info<T, R>` instead of just a T to make it consistent with the other variants.

### 1.0.0-beta.2
* `Info<T>` and `Error<T>` has had their signatures changed to `Info<T, R>` and `Error<T, R>`. `Info` has a new variant which is specified by `R` and defines the type for range errors. `ParseError<T: Positioner>` has been changed to `ParseError<S: Stream>` (S is the stream type of the parser).
* If you were using `ParseResult` from primitives you should no longer specify the item type of the stream.

### 0.7.0
* `Stream::uncons` changed its signature to allow it to return errors. Return `Error::end_of_input()` instead of `()` if you implemented `Stream`.

### 0.6.0
* Addition of `Parser::parse_lazy`, should not break anything but I can't say for certain.

### 0.5.0
* `any_char` -> `any`, `uncons_char` -> `uncons`
* Introduction of the `Positioner` trait which needs to be implemented on an custom token types.
* `satisfy` is moved to the `combinators` module and made generic, might cause type inference issues.

### 0.4.0
* `any_char` is no longer a free function but returns a parser when called as all parser functions (and its called `any` after 0.5.0)
* `Cow` is replaced by `Info` in the error messages.

### 0.3.2 / 0.3.0
* Added variant to `Error` which can hold any kind of `::std::error::Error`
* `choice_vec` and `choice_slice` is replaced by just `choice`

### 0.2.6
* Iterators cannot directly be used as streams but must be wrapped using `from_iter` function

If you have trouble updating to a newer version feel free to open an issue and I can take a look.

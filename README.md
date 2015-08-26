# combine
[![Build Status](https://travis-ci.org/Marwes/combine.svg?branch=master)](https://travis-ci.org/Marwes/combine) [![Coverage Status](https://coveralls.io/repos/Marwes/parser-combinators/badge.svg?branch=master&service=github)](https://coveralls.io/github/Marwes/parser-combinators?branch=master) [![Gitter](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/Marwes/combine?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge)

(Previously named parser-combinators)

An implementation of parser combinators for Rust, inspired by the Haskell library [Parsec](https://hackage.haskell.org/package/parsec). As in Parsec the parsers are [LL(1)](https://en.wikipedia.org/wiki/LL_parser) by default but they can opt-in to arbitrary lookahed using the [try  combinator](https://marwes.github.io/combine/combine/fn.try.html).

##Example

```rust
extern crate combine;
use combine::{many, Parser};
use combine::char::letter;

let result = many(letter()).parse("hello world");
assert_eq!(result, Ok(("hello".to_string(), " world")));
```

Larger examples can be found in the [examples][examples] and [benches][benches] folders.

[benches]:https://github.com/Marwes/combine/tree/master/benches
[examples]:https://github.com/Marwes/combine/tree/master/examples

## Links

[Documentation and examples](https://marwes.github.io/combine/combine/index.html)

[crates.io](https://crates.io/crates/combine)

## About

A parser combinator is, broadly speaking, a function which takes several parsers as arguments and returns a new parser, created by combining those parsers. For instance, the [many](https://marwes.github.io/combine/combine/fn.many.html) parser takes one parser, `p`, as input and returns a new parser which applies `p` zero or more times. Thanks to the modularity that parser combinators gives it is possible to define parsers for a wide range of tasks without needing to implement the low level plumbing while still having the full power of Rust when you need it. 

The library is almost stable but a few parts of the internals may still change before 1.0. After that the library will adhere to [semantic versioning](http://semver.org).

If you end up trying it I welcome any feedback from your experience with it. I am usually reachable within a dat by opening an issue or sending an email. I am also testing gitter for smaller questions.

## Extra

There is an additional crate which has parsers to lex and parse programming languages in [combine-language](https://github.com/Marwes/combine-language).

You can find older versions of combine (parser-combinators) [here](https://crates.io/crates/parser-combinators).

## Contributing

The easiest way to contribute is to just open an issue about any problems you encounter using combine but if you are intersted in adding something to the library here is a list of some of the easier things to work on to get started.

* __Add additional parsers__ There is a list of parsers which aren't implemented [here][add parsers] but if you have a suggestion for another parser just leave a suggestion on the issue itself.
* __Add additional examples__ More examples for using combine will always be useful!
* __Add and improve the docs__ Not the fanciest of work but one cannot overstate the importance of good documentation.

[add parsers]: https://github.com/Marwes/combine/issues/2

## Breaking changes

Here is a list containing most of the breaking changes in older versions of combine (parser-combinators).

### 1.0.0-beta.3
* `Error::Unexpected` holds an `Info<T, R>` instead of just a T to make it consitent with the other variants.

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

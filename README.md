# parser-combinators [![Build Status](https://travis-ci.org/Marwes/parser-combinators.svg?branch=master)](https://travis-ci.org/Marwes/parser-combinators)

An implementation of parser combinators for Rust, inspired by the Haskell library [Parsec](https://hackage.haskell.org/package/parsec). As in Parsec the parsers are [LL(1)](https://en.wikipedia.org/wiki/LL_parser) by default but they can opt-in to arbitrary lookahed using the [try](https://marwes.github.io/parser-combinators/parser_combinators/fn.try.html) combinator.

A parser combinators is, broadly speaking, a function which takes several parsers as arguments and returns a new parser, created by combining those parsers. For instance, the [many](https://marwes.github.io/parser-combinators/parser_combinators/fn.many.html) parser takes one parser, `p`, as input and returns a new parser which applies `p` zero or more times.

The library is mostly stable but a few parts of the internals may still change. If you end up trying it I welcome any feedback from your experience with it.

##Example

```rust
extern crate parser_combinators;
use parser_combinators::{many, Parser};
use parser_combinators::char::letter;

let result = many(letter()).parse("hello world");
assert_eq!(result, Ok(("hello".to_string(), " world")));
```

## Links

[Documentation and examples](https://marwes.github.io/parser-combinators/parser_combinators/index.html)

[crates.io](https://crates.io/crates/parser-combinators)

## Extra

There is an additional crate which has parsers to lex and parse programming languages in [parser-combinators-language](https://github.com/Marwes/parser-combinators-language).

## Breaking changes

Here is a list containing most of the breaking changes in older versions of parser-combinators.

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

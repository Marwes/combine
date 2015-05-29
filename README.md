# parser-combinators [![Build Status](https://travis-ci.org/Marwes/parser-combinators.svg?branch=master)](https://travis-ci.org/Marwes/parser-combinators)

An implementation of (LL(1)) parser combinators for Rust, inspired by the Haskell library [Parsec](https://hackage.haskell.org/package/parsec).

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

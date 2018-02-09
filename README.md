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

## Parsers written in combine

### Formats and protocols

* GraphQL https://github.com/tailhook/graphql-parser (Uses a custom tokenizer as input)
* DiffX https://github.com/brennie/diffx-rs
* Redis https://github.com/mitsuhiko/redis-rs/pull/141 (Uses partial parsing)
* Toml https://github.com/ordian/toml_edit
* Maker Interchange Format https://github.com/aidanhs/frametool (Uses combine as a lexer)

### Miscellaneous

* Template language https://github.com/tailhook/trimmer
* Code excercises https://github.com/dgel/adventOfCode2017
* Programming language https://github.com/MaikKlein/spire-lang
* Query parser (+ more) https://github.com/mozilla/mentat
* Query parser https://github.com/tantivy-search/tantivy

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


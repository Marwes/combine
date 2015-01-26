# parser-combinators
An early implementation of parser combinators implemented in Rust

Very much a work in progress at this point any suggestions or comments are welcome!
The API mostly mirrors the Haskell library [Parsec](https://hackage.haskell.org/package/parsec) but is implemented differntly behind the scenes.

##Example
```rust
extern crate "parser-combinators" as parser_combinators;
use parser_combinators::{spaces, chars1, sep_by, digit, satisfy, Parser, ParserExt};

fn main() {
    let input = "1234, 45,78";
    let spaces = spaces();
    let integer = spaces.clone()//Parse spaces first and use the with method to only keep the result of the next parser
        .with(chars1(digit()).map(|string| string.parse::<i32>().unwrap()));//parse a string of digits into an i32
    let mut integer_list = sep_by(integer, spaces.skip(satisfy(|c| c == ',')));//Parse integers separated by commas, skipping whitespace
    
    //Call parse with the input to execute the parser
    match integer_list.parse(input) {
        Ok((value, _remaining_input)) => println!("{:?}", value),
        Err(err) => println!("{}", err)
    }
}

```

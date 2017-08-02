//! This crate contains parser combinators, roughly based on the Haskell library
//! [parsec](http://hackage.haskell.org/package/parsec).
//!
//! A parser in this library can be described as a function which takes some input and if it
//! is succesful, returns a value together with the remaining input.
//! A parser combinator is a function which takes one or more parsers and returns a new parser.
//! For instance the [`many`] parser can be used to convert a parser for single digits into one that
//! parses multiple digits. By modeling parsers in this way it becomes simple to compose complex
//! parsers in an almost declarative way.
//!
//! # Overview
//!
//! `combine` limits itself to creating [LL(1) parsers](https://en.wikipedia.org/wiki/LL_parser)
//! (it is possible to opt-in to LL(k) parsing using the [`try`] combinator) which makes the
//! parsers easy to reason about in both function and performance while sacrificing
//! some generality. In addition to you being able to reason better about the parsers you
//! construct `combine` the library also takes the knowledge of being an LL parser and uses it to
//! automatically construct good error messages.
//!
//! ```rust
//! extern crate combine;
//! use combine::{Parser, State};
//! use combine::char::{digit, letter};
//! const MSG: &'static str = r#"Parse error at line: 1, column: 1
//! Unexpected `|`
//! Expected `digit` or `letter`
//! "#;
//!
//! fn main() {
//!     // Wrapping a `&str` with `State` provides automatic line and column tracking. If `State`
//!     // was not used the positions would instead only be pointers into the `&str`
//!     if let Err(err) = digit().or(letter()).parse(State::new("|")) {
//!         assert_eq!(MSG, format!("{}", err));
//!     }
//! }
//! ```
//!
//! This library currently contains five modules:
//!
//! * [`combinator`] contains the before mentioned parser combinators and thus contains the main
//! building exprs for creating any sort of complex parsers. It consists of free functions such
//! as [`many`] and [`satisfy`] as well as a few methods on the [`Parser`] trait which provides a
//! few functions such as [`or`] which are more natural to use method calls.
//!
//! * [`primitives`] contains the [`Parser`] and [`Stream`] traits which are the core abstractions
//! in combine as well as various structs dealing with input streams and errors. You usually only
//! need to use this module if you want more control over parsing and input streams.
//!
//! * [`char`] and [`byte`] provides parsers specifically working with streams of characters
//! (`char`) and bytes (`u8`) respectively. As a few examples it has parsers for accepting digits,
//! letters or whitespace.
//!
//! * [`range`] provides some zero-copy parsers for [`RangeStream`]s.
//!
//! # Examples
//!
//! ```
//! extern crate combine;
//! use combine::char::{spaces, digit, char};
//! use combine::{many1, sep_by, Parser, StreamError};
//!
//! fn main() {
//!     //Parse spaces first and use the with method to only keep the result of the next parser
//!     let integer = spaces()
//!         //parse a string of digits into an i32
//!         .with(many1(digit()).map(|string: String| string.parse::<i32>().unwrap()));
//!
//!     //Parse integers separated by commas, skipping whitespace
//!     let mut integer_list = sep_by(integer, spaces().skip(char(',')));
//!
//!     //Call parse with the input to execute the parser
//!     let input = "1234, 45,78";
//!     let result: Result<(Vec<i32>, &str), StreamError<&str>> = integer_list.parse(input);
//!     match result {
//!         Ok((value, _remaining_input)) => println!("{:?}", value),
//!         Err(err) => println!("{}", err)
//!     }
//! }
//! ```
//!
//! If we need a parser that is mutually recursive we can define a free function which internally
//! can in turn be used as a parser by using the [`parser`][fn parser] function which turns a
//! function with the correct signature into a parser. In this case we define `expr` to work on any
//! type of [`Stream`] which is combine's way of abstracting over different data sources such as
//! array slices, string slices, iterators etc. If instead you would only need to parse string
//! already in memory you could define `expr` as `fn expr(input: &str) -> ParseResult<Expr, &str>`
//!
//! ```
//! #[macro_use]
//! extern crate combine;
//! use combine::char::{char, letter, spaces};
//! use combine::{between, many1, parser, sep_by, Parser};
//! use combine::primitives::{Stream, Positioned, ParseResult};
//! use combine::state::State;
//!
//! #[derive(Debug, PartialEq)]
//! pub enum Expr {
//!     Id(String),
//!     Array(Vec<Expr>),
//!     Pair(Box<Expr>, Box<Expr>)
//! }
//!
//! // The `parser!` macro can be used to define parser producing functions in most cases
//! // (for more advanced uses standalone functions can be defined to handle parsing)
//! parser!{
//!    fn expr[I]()(I) -> Expr
//!     where [I: Stream<Item=char>]
//! {
//!     let word = many1(letter());
//!
//!     //Creates a parser which parses a char and skips any trailing whitespace
//!     let lex_char = |c| char(c).skip(spaces());
//!
//!     let comma_list = sep_by(expr(), lex_char(','));
//!     let array = between(lex_char('['), lex_char(']'), comma_list);
//!
//!     //We can use tuples to run several parsers in sequence
//!     //The resulting type is a tuple containing each parsers output
//!     let pair = (lex_char('('),
//!                 expr(),
//!                 lex_char(','),
//!                 expr(),
//!                 lex_char(')'))
//!                    .map(|t| Expr::Pair(Box::new(t.1), Box::new(t.3)));
//!
//!     word.map(Expr::Id)
//!         .or(array.map(Expr::Array))
//!         .or(pair)
//!         .skip(spaces())
//! }
//! }
//!
//! fn main() {
//!     let result = expr()
//!         .parse("[[], (hello, world), [rust]]");
//!     let expr = Expr::Array(vec![
//!           Expr::Array(Vec::new())
//!         , Expr::Pair(Box::new(Expr::Id("hello".to_string())),
//!                      Box::new(Expr::Id("world".to_string())))
//!         , Expr::Array(vec![Expr::Id("rust".to_string())])
//!     ]);
//!     assert_eq!(result, Ok((expr, "")));
//! }
//! ```
//!
//! [`combinator`]: combinator/index.html
//! [`primitives`]: primitives/index.html
//! [`char`]: char/index.html
//! [`byte`]: byte/index.html
//! [`range`]: range/index.html
//! [`many`]: combinator/fn.many.html
//! [`try`]: combinator/fn.try.html
//! [`satisfy`]: combinator/fn.satisfy.html
//! [`or`]: primitives/trait.Parser.html#method.or
//! [`Stream`]: primitives/trait.Stream.html
//! [`RangeStream`]: primitives/trait.RangeStream.html
//! [`Parser`]: primitives/trait.Parser.html
//! [fn parser]: combinator/fn.parser.html
// inline(always) is only used on trivial functions returning parsers
#![cfg_attr(feature = "cargo-clippy", allow(inline_always))]

#[doc(inline)]
pub use primitives::{ConsumedResult, ParseError, ParseResult, Parser, Positioned, Stream,
                     StreamError, StreamOnce};

#[doc(inline)]
pub use state::State;

#[doc(inline)]
pub use combinator::{any, between, choice, count, count_min_max, env_parser, eof, look_ahead,
                     many, none_of, not_followed_by, one_of, optional, parser, position, satisfy,
                     satisfy_map, sep_by, sep_end_by, skip_count, skip_count_min_max, skip_many,
                     token, tokens, try, unexpected, value, chainl1, chainr1, many1, sep_by1,
                     sep_end_by1, skip_many1};

macro_rules! static_fn {
    (($($arg: pat, $arg_ty: ty),*) -> $ret: ty { $body: expr }) => { {
        fn temp($($arg: $arg_ty),*) -> $ret { $body }
        temp as fn(_) -> _
    } }
}

macro_rules! impl_token_parser {
    ($name: ident($($ty_var: ident),*), $ty: ty, $inner_type: ty) => {
    #[derive(Clone)]
    pub struct $name<I $(,$ty_var)*>($inner_type, PhantomData<fn (I) -> I>)
        where I: Stream<Item=$ty> $(, $ty_var : Parser<Input=I>)*;
    impl <I $(,$ty_var)*> Parser for $name<I $(,$ty_var)*>
        where I: Stream<Item=$ty> $(, $ty_var : Parser<Input=I>)* {
        type Input = I;
        type Output = <$inner_type as Parser>::Output;
        #[inline]
        fn parse_lazy(&mut self,
                      input: Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
            self.0.parse_lazy(input)
        }
        fn add_error(&mut self, errors: &mut Tracked<StreamError<Self::Input>>) {
            self.0.add_error(errors)
        }
    }
}
}

/// Declares a named parser which can easily be reused.
///
/// The expression which creates the parser should have no side effects as it may be called
/// multiple times even during a single parse attempt.
///
/// ```
/// #[macro_use]
/// extern crate combine;
/// use combine::char::digit;
/// use combine::{any, choice, many1, Parser, Stream};
///
/// parser!{
///     fn integer[I]()(I) -> i32
///         where [I: Stream<Item = char>]
///     {
///         // The body must be a block body ( `{ <block body> }`) which ends with an expression
///         // which evaluates to a parser
///         let digits = many1(digit());
///         digits.and_then(|s: String| s.parse())
///     }
/// }
///
/// #[derive(Debug, PartialEq)]
/// pub enum IntOrString {
///     Int(i32),
///     String(String),
/// }
/// // prefix with `pub` to declare a public parser
/// parser!{
///     // Documentation comments works as well
///
///     /// Parses an integer or a string (any characters)
///     pub fn integer_or_string[I]()(I) -> IntOrString
///         where [I: Stream<Item = char>]
///     {
///         choice!(
///             integer().map(IntOrString::Int),
///             many1(any()).map(IntOrString::String)
///         )
///     }
/// }
///
/// parser!{
///     // Give the created type a unique name
///     #[derive(Clone)]
///     pub struct Twice;
///     pub fn twice[F, P](f: F)(P::Input) -> (P::Output, P::Output)
///         where [P: Parser,
///                F: FnMut() -> P]
///     {
///         (f(), f())
///     }
/// }
///
/// fn main() {
///     assert_eq!(integer().parse("123"), Ok((123, "")));
///     assert!(integer().parse("!").is_err());
///
///     assert_eq!(integer_or_string().parse("123"), Ok((IntOrString::Int(123), "")));
///     assert_eq!(
///         integer_or_string().parse("abc"),
///         Ok((IntOrString::String("abc".to_string()), ""))
///     );
///     assert_eq!(twice(|| digit()).parse("123"), Ok((('1', '2'), "3")));
/// }
/// ```
#[macro_export]
macro_rules! parser {
    (
        $(#[$attr:meta])*
        pub fn $name: ident [$($type_params: tt)*]( $($arg: ident :  $arg_type: ty),* )
            ($input_type: ty) -> $output_type: ty
            { $($parser: tt)* }
    ) => {
        parser!{
            $(#[$attr])*
            pub fn $name [$($type_params)*]( $($arg : $arg_type),* )($input_type) -> $output_type
                where []
            { $($parser)* }
        }
    };
    (
        $(#[$attr:meta])*
        fn $name: ident [$($type_params: tt)*]( $($arg: ident :  $arg_type: ty),* )
            ($input_type: ty) -> $output_type: ty
            { $($parser: tt)* }
    ) => {
        parser!{
            $(#[$attr])*
            fn $name [$($type_params)*]( $($arg : $arg_type),* )($input_type) -> $output_type
                where []
            { $($parser)* }
        }
    };
    (
        $(#[$attr:meta])*
        pub fn $name: ident [$($type_params: tt)*]( $($arg: ident :  $arg_type: ty),* )
            ($input_type: ty) -> $output_type: ty
            where [$($where_clause: tt)*]
        { $($parser: tt)* }
    ) => {
        parser!{
            pub struct __Parser;
            $(#[$attr])*
            pub fn $name [$($type_params)*]($($arg : $arg_type),*)($input_type) -> $output_type
                where [$($where_clause)*]
            { $($parser)* }
        }
    };
    (
        $(#[$attr:meta])*
        fn $name: ident [$($type_params: tt)*]( $($arg: ident :  $arg_type: ty),*) ($input_type: ty) -> $output_type: ty
            where [$($where_clause: tt)*]
        { $($parser: tt)* }
    ) => {
        parser!{
            struct __Parser;
            $(#[$attr])*
            fn $name [$($type_params)*]($($arg : $arg_type),*)($input_type) -> $output_type
                where [$($where_clause)*]
            { $($parser)* }
        }
    };
    (
        $(#[$derive:meta])*
        pub struct $type_name: ident;
        $(#[$attr:meta])*
        pub fn $name: ident [$($type_params: tt)*]( $($arg: ident :  $arg_type: ty),* )
            ($input_type: ty) -> $output_type: ty
            where [$($where_clause: tt)*]
        { $($parser: tt)* }
    ) => {
        combine_parser_impl!{
            (pub)
            $(#[$derive])*
            struct $type_name;
            $(#[$attr])*
            fn $name [$($type_params)*]($($arg : $arg_type),*)($input_type) -> $output_type
                where [$($where_clause)*]
            { $($parser)* }
        }
    };
    (
        $(#[$derive:meta])*
        struct $type_name: ident;
        $(#[$attr:meta])*
        fn $name: ident [$($type_params: tt)*]( $($arg: ident :  $arg_type: ty),*) ($input_type: ty) -> $output_type: ty
            where [$($where_clause: tt)*]
        { $($parser: tt)* }
    ) => {
        combine_parser_impl!{
            ()
            $(#[$derive])*
            struct $type_name;
            $(#[$attr:meta])*
            fn $name [$($type_params)*]($($arg : $arg_type),*)($input_type) -> $output_type
                where [$($where_clause)*]
            { $($parser)* }
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! combine_parse_lazy {
    ($input: ident
        $stmt: stmt; $($parser: tt)*
    ) => { {
        $stmt;
        combine_parse_lazy!{$input $($parser)*}
    } };
    ($input: ident
        $parser: expr
    ) => {
        $parser.parse_lazy($input)
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! combine_add_error {
    ($errors: ident ($input_type : ty, $output_type : ty)
        $stmt: stmt; $($parser: tt)*
    ) => { {
        $stmt;
        combine_add_error!{$errors ($input_type, $output_type) $($parser)*}
    } };
    ($errors: ident ($input_type : ty, $output_type : ty)
        $parser: expr
    ) => { {
        let mut parser = $parser;
        {
            let _: &mut Parser<Input = $input_type, Output = $output_type> = &mut parser;
        }
        parser.add_error($errors)
    } }
}

#[doc(hidden)]
#[macro_export]
macro_rules! combine_parser_impl {
    (
        ( $($pub_: tt)* )
        $(#[$derive:meta])*
        struct $type_name: ident;
        $(#[$attr:meta])*
        fn $name: ident [$($type_params: tt)*]( $($arg: ident :  $arg_type: ty),*) ($input_type: ty) -> $output_type: ty
            where [$($where_clause: tt)*]
        { $($parser: tt)* }
    ) => {
        mod $name {
            use super::*;

            $(#[$derive])*
            pub struct $type_name<$($type_params)*>
                where $($where_clause)*
            {
                $(pub $arg : $arg_type,)*
                __marker: ::std::marker::PhantomData<fn ($input_type) -> $output_type>
            }

            // We want this to work on older compilers, at least for a while
            #[allow(non_shorthand_field_patterns)]
            impl<$($type_params)*> $crate::Parser for $type_name<$($type_params)*>
                where $($where_clause)*
            {
                type Input = $input_type;
                type Output = $output_type;

                #[inline]
                fn parse_lazy(
                    &mut self,
                    input: $input_type
                    ) -> $crate::primitives::ConsumedResult<$output_type, $input_type>
                {
                    let $type_name { $( $arg: ref mut $arg,)* __marker: _ } = *self;
                    combine_parse_lazy!(input $($parser)*)
                }

                #[inline]
                fn add_error(
                    &mut self,
                    errors: &mut $crate::primitives::Tracked<$crate::StreamError<$input_type>>)
                {
                    let $type_name { $( $arg : ref mut $arg,)*  __marker: _ } = *self;
                    combine_add_error!(errors ($input_type, $output_type) $($parser)*)
                }
            }
            #[inline(always)]
            pub fn parse< $($type_params)* >(
                    $($arg : $arg_type),*
                ) -> self::$type_name<$($type_params)*>
                where $($where_clause)*
            {
                $type_name {
                    $($arg : $arg,)*
                    __marker: ::std::marker::PhantomData
                }
            }
        }

        $(#[$attr])*
        #[inline(always)]
        $($pub_)* fn $name< $($type_params)* >(
                $($arg : $arg_type),*
            ) -> self::$name::$type_name<$($type_params)*>
            where $($where_clause)*
        {
            self::$name::parse(
                $($arg,)*
            )
        }
    };
}


pub extern crate byteorder;

/// Module containing the primitive types which is used to create and compose more advanced
/// parsers.
#[macro_use]
pub mod primitives;
/// Module containing all specific parsers.
pub mod combinator;
/// Module containing zero-copy parsers.
pub mod range;
/// Module containing parsers specialized on byte streams.
pub mod byte;
/// Module containing parsers specialized on character streams.
pub mod char;
/// Module containing stateful stream wrappers
pub mod state;

#[cfg(feature = "regex")]
pub mod regex;

#[doc(hidden)]
#[derive(Clone, PartialEq, Debug, Copy)]
pub struct ErrorOffset(u8);


#[cfg(test)]
mod tests {
    use super::*;
    use super::primitives::{Consumed, Error, IteratorStream};
    use char::{alpha_num, char, digit, letter, spaces, string};

    use state::SourcePosition;


    fn integer<'a, I>(input: I) -> ParseResult<i64, I>
    where
        I: Stream<Item = char>,
    {
        let (s, input) = try!(
            many1::<String, _>(digit())
                .expected("integer")
                .parse_stream(input)
        );
        let mut n = 0;
        for c in s.chars() {
            n = n * 10 + (c as i64 - '0' as i64);
        }
        Ok((n, input))
    }

    #[test]
    fn test_integer() {
        let result = parser(integer).parse("123");
        assert_eq!(result, Ok((123i64, "")));
    }
    #[test]
    fn list() {
        let mut p = sep_by(parser(integer), char(','));
        let result = p.parse("123,4,56");
        assert_eq!(result, Ok((vec![123i64, 4, 56], "")));
    }
    #[test]
    fn iterator() {
        let result = parser(integer)
            .parse(State::new(IteratorStream::new("123".chars())))
            .map(|(i, mut input)| (i, input.uncons().is_err()));
        assert_eq!(result, Ok((123i64, true)));
    }
    #[test]
    fn field() {
        let word = || many(alpha_num());
        let spaces = spaces();
        let c_decl = (word(), spaces.clone(), char(':'), spaces, word())
            .map(|t| (t.0, t.4))
            .parse("x: int");
        assert_eq!(c_decl, Ok((("x".to_string(), "int".to_string()), "")));
    }
    #[test]
    fn source_position() {
        let source = r"
123
";
        let result = (spaces(), parser(integer), spaces())
            .map(|t| t.1)
            .parse_stream(State::with_positioner(source, SourcePosition::new()));
        let state = Consumed::Consumed(State {
            positioner: SourcePosition { line: 3, column: 1 },
            input: "",
        });
        assert_eq!(result, Ok((123i64, state)));
    }

    #[derive(Debug, PartialEq)]
    pub enum Expr {
        Id(String),
        Int(i64),
        Array(Vec<Expr>),
        Plus(Box<Expr>, Box<Expr>),
        Times(Box<Expr>, Box<Expr>),
    }

    parser!{
        fn expr[I]()(I) -> Expr
        where
            [I: Stream<Item = char>,]
        {
            let word = many1(letter()).expected("identifier");
            let integer = parser(integer);
            let array = between(char('['), char(']'), sep_by(expr(), char(','))).expected("[");
            let paren_expr = between(char('('), char(')'), parser(term)).expected("(");
            let spaces = spaces();
            spaces
                .clone()
                .with(
                    word.map(Expr::Id)
                        .or(integer.map(Expr::Int))
                        .or(array.map(Expr::Array))
                        .or(paren_expr),
                )
                .skip(spaces)
        }
    }

    #[test]
    fn expression() {
        let result = sep_by(expr(), char(',')).parse("int, 100, [[], 123]");
        let exprs = vec![
            Expr::Id("int".to_string()),
            Expr::Int(100),
            Expr::Array(vec![Expr::Array(vec![]), Expr::Int(123)]),
        ];
        assert_eq!(result, Ok((exprs, "")));
    }

    #[test]
    fn expression_error() {
        let input = r"
,123
";
        let result = expr().parse(State::new(input));
        let err = ParseError {
            position: SourcePosition { line: 2, column: 1 },
            errors: vec![
                Error::Unexpected(','.into()),
                Error::Expected("integer".into()),
                Error::Expected("identifier".into()),
                Error::Expected("[".into()),
                Error::Expected("(".into()),
            ],
        };
        assert_eq!(result, Err(err));
    }

    fn term<I>(input: I) -> ParseResult<Expr, I>
    where
        I: Stream<Item = char>,
    {
        fn times(l: Expr, r: Expr) -> Expr {
            Expr::Times(Box::new(l), Box::new(r))
        }
        fn plus(l: Expr, r: Expr) -> Expr {
            Expr::Plus(Box::new(l), Box::new(r))
        }
        let mul = char('*').map(|_| times);
        let add = char('+').map(|_| plus);
        let factor = chainl1(expr(), mul);
        chainl1(factor, add).parse_stream(input)
    }

    #[test]
    fn operators() {
        let input = r"
1 * 2 + 3 * test
";
        let (result, _) = parser(term).parse(State::new(input)).unwrap();

        let e1 = Expr::Times(Box::new(Expr::Int(1)), Box::new(Expr::Int(2)));
        let e2 = Expr::Times(
            Box::new(Expr::Int(3)),
            Box::new(Expr::Id("test".to_string())),
        );
        assert_eq!(result, Expr::Plus(Box::new(e1), Box::new(e2)));
    }


    fn follow(input: State<&str, SourcePosition>) -> ParseResult<(), State<&str, SourcePosition>> {
        match input.clone().uncons() {
            Ok(c) => if c.is_alphanumeric() {
                let e = Error::Unexpected(c.into());
                Err(Consumed::Empty(ParseError::new(input.position(), e).into()))
            } else {
                Ok(((), Consumed::Empty(input)))
            },
            Err(_) => Ok(((), Consumed::Empty(input))),
        }
    }
    #[test]
    fn error_position() {
        let mut p = string("let")
            .skip(parser(follow))
            .map(|x| x.to_string())
            .or(many1(digit()));
        match p.parse(State::new("le123")) {
            Ok(_) => assert!(false),
            Err(err) => assert_eq!(err.position, SourcePosition { line: 1, column: 1 }),
        }
        match p.parse(State::new("let1")) {
            Ok(_) => assert!(false),
            Err(err) => assert_eq!(err.position, SourcePosition { line: 1, column: 4 }),
        }
    }

    #[test]
    fn sep_by_error_consume() {
        let mut p = sep_by::<Vec<_>, _, _>(string("abc"), char(','));
        let err = p.parse(State::new("ab,abc")).unwrap_err();
        assert_eq!(err.position, SourcePosition { line: 1, column: 1 });
    }

    #[test]
    fn optional_error_consume() {
        let mut p = optional(string("abc"));
        let err = p.parse(State::new("ab")).unwrap_err();
        assert_eq!(err.position, SourcePosition { line: 1, column: 1 });
    }
    #[test]
    fn chainl1_error_consume() {
        fn first<T, U>(t: T, _: U) -> T {
            t
        }
        let mut p = chainl1(string("abc"), char(',').map(|_| first));
        assert!(p.parse("abc,ab").is_err());
    }

    #[test]
    fn inner_error_consume() {
        let mut p = many::<Vec<_>, _>(between(char('['), char(']'), digit()));
        let result = p.parse(State::new("[1][2][]"));
        assert!(result.is_err(), format!("{:?}", result));
        let error = result.map(|x| format!("{:?}", x)).unwrap_err();
        assert_eq!(error.position, SourcePosition { line: 1, column: 8 });
    }

    #[test]
    fn infinite_recursion_in_box_parser() {
        let _: Result<(Vec<_>, _), _> = (many(Box::new(digit()))).parse("1");
    }

    #[test]
    fn unsized_parser() {
        let mut parser: Box<Parser<Input = &str, Output = char>> = Box::new(digit());
        let borrow_parser = &mut *parser;
        assert_eq!(borrow_parser.parse("1"), Ok(('1', "")));
    }

    #[test]
    fn choice_strings() {
        let mut fruits = [
            try(string("Apple")),
            try(string("Banana")),
            try(string("Cherry")),
            try(string("Date")),
            try(string("Fig")),
            try(string("Grape")),
        ];
        let mut parser = choice(&mut fruits);
        assert_eq!(parser.parse("Apple"), Ok(("Apple", "")));
        assert_eq!(parser.parse("Banana"), Ok(("Banana", "")));
        assert_eq!(parser.parse("Cherry"), Ok(("Cherry", "")));
        assert_eq!(parser.parse("DateABC"), Ok(("Date", "ABC")));
        assert_eq!(parser.parse("Fig123"), Ok(("Fig", "123")));
        assert_eq!(parser.parse("GrapeApple"), Ok(("Grape", "Apple")));
    }

    #[test]
    fn std_error() {
        use std::fmt;
        use std::error::Error as StdError;
        #[derive(Debug)]
        struct Error;
        impl fmt::Display for Error {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "error")
            }
        }
        impl StdError for Error {
            fn description(&self) -> &str {
                "error"
            }
        }
        let result: Result<((), _), ParseError<_, char, &str>> =
            string("abc").and_then(|_| Err(Error)).parse("abc");
        assert!(result.is_err());
        // Test that ParseError can be coerced to a StdError
        let _ = result.map_err(|err| {
            let err: Box<StdError> = Box::new(err);
            err
        });
    }

    #[test]
    fn extract_std_error() {
        // The previous test verified that we could map a ParseError to a StdError by dropping the
        // internal error details.  This test verifies that we can map a ParseError to a StdError
        // without dropping the internal error details.  Consumers using `error-chain` will
        // appreciate this.  For technical reasons this is pretty janky; see the discussion in
        // https://github.com/Marwes/combine/issues/86, and excuse the test with significant
        // boilerplate!
        use std::fmt;
        use std::error::Error as StdError;

        #[derive(Clone, PartialEq, Debug)]
        struct CloneOnly(String);

        #[derive(Debug)]
        struct DisplayVec<T>(Vec<T>);

        #[derive(Debug)]
        struct ExtractedError(usize, DisplayVec<Error<CloneOnly, DisplayVec<CloneOnly>>>);

        impl StdError for ExtractedError {
            fn description(&self) -> &str {
                "extracted error"
            }
        }

        impl fmt::Display for CloneOnly {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "{}", self.0)
            }
        }

        impl<T: fmt::Debug> fmt::Display for DisplayVec<T> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "[{:?}]", self.0)
            }
        }

        impl fmt::Display for ExtractedError {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                try!(writeln!(f, "Parse error at {}", self.0));
                Error::fmt_errors(&(self.1).0, f)
            }
        }

        let input = &[CloneOnly("x".to_string()), CloneOnly("y".to_string())][..];
        let result = token(CloneOnly("z".to_string()))
            .parse(input)
            .map_err(|e| e.map_position(|p| p.translate_position(input)))
            .map_err(|e| {
                ExtractedError(
                    e.position,
                    DisplayVec(
                        e.errors
                            .into_iter()
                            .map(|e| e.map_range(|r| DisplayVec(r.to_owned())))
                            .collect(),
                    ),
                )
            });

        assert!(result.is_err());
        // Test that the fresh ExtractedError is Display, so that the internal errors can be
        // inspected by consuming code; and that the ExtractedError can be coerced to StdError.
        let _ = result.map_err(|err| {
            let s = format!("{}", err);
            assert!(s.starts_with("Parse error at 0"));
            assert!(s.contains("Expected"));
            let err: Box<StdError> = Box::new(err);
            err
        });
    }
}

//! This crate contains parser combinators, roughly based on the Haskell libraries
//! [parsec](http://hackage.haskell.org/package/parsec) and
//! [attoparsec](https://hackage.haskell.org/package/attoparsec).
//!
//! A parser in this library can be described as a function which takes some input and if it
//! is successful, returns a value together with the remaining input.
//! A parser combinator is a function which takes one or more parsers and returns a new parser.
//! For instance the [`many`] parser can be used to convert a parser for single digits into one that
//! parses multiple digits. By modeling parsers in this way it becomes easy to compose complex
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
//! use combine::Parser;
//! use combine::stream::state::State;
//! use combine::parser::char::{digit, letter};
//! const MSG: &'static str = r#"Parse error at line: 1, column: 1
//! Unexpected `|`
//! Expected `digit` or `letter`
//! "#;
//!
//! fn main() {
//!     // Wrapping a `&str` with `State` provides automatic line and column tracking. If `State`
//!     // was not used the positions would instead only be pointers into the `&str`
//!     if let Err(err) = digit().or(letter()).easy_parse(State::new("|")) {
//!         assert_eq!(MSG, format!("{}", err));
//!     }
//! }
//! ```
//!
//! This library is currently split into a few core modules:
//!
//! * [`parser`][mod parser] is where you will find all the parsers that combine provides. It contains the core
//! [`Parser`] trait as well as several submodules such as `sequence` or `choice` which each
//! contain several parsers aimed at a specific niche.
//!
//! * [`stream`] contains the second most important trait next to [`Parser`]. Streams represent the
//! data source which is being parsed such as `&[u8]`, `&str` or iterators.
//!
//! * [`easy`] contains combine's default "easy" error and stream handling. If you use the
//! `easy_parse` method to start your parsing these are the types that are used.
//!
//! * [`error`] contains the types and traits that make up combine's error handling. Unless you
//! need to customize the errors your parsers return you should not need to use this module much.
//!
//!
//! # Examples
//!
//! ```
//! extern crate combine;
//! use combine::parser::char::{spaces, digit, char};
//! use combine::{many1, sep_by, Parser};
//! use combine::stream::easy;
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
//!     let result: Result<(Vec<i32>, &str), easy::ParseError<&str>> =
//!         integer_list.easy_parse(input);
//!     match result {
//!         Ok((value, _remaining_input)) => println!("{:?}", value),
//!         Err(err) => println!("{}", err)
//!     }
//! }
//! ```
//!
//! If we need a parser that is mutually recursive or if we want to export a reusable parser the
//! [`parser!`] macro can be used. In effect it makes it possible to return a parser without naming
//! the type of the parser (which can be very large due to combine's trait based approach). While
//! it is possible to do avoid naming the type without the macro those solutions require either allocation
//! (`Box<Parser<Input = I, Output = O, PartialState = P>>`) or nightly rust via `impl Trait`. The
//! macro thus threads the needle and makes it possible to have non-allocating, anonymous parsers
//! on stable rust.
//!
//! ```
//! #[macro_use]
//! extern crate combine;
//! use combine::parser::char::{char, letter, spaces};
//! use combine::{between, choice, many1, parser, sep_by, Parser};
//! use combine::error::{ParseError, ParseResult};
//! use combine::stream::{Stream, Positioned};
//! use combine::stream::state::State;
//!
//! #[derive(Debug, PartialEq)]
//! pub enum Expr {
//!     Id(String),
//!     Array(Vec<Expr>),
//!     Pair(Box<Expr>, Box<Expr>)
//! }
//!
//! // `impl Parser` can be used to create reusable parsers with zero overhead
//! fn expr_<I>() -> impl Parser<Input = I, Output = Expr>
//!     where I: Stream<Item = char>,
//!           // Necessary due to rust-lang/rust#24159
//!           I::Error: ParseError<I::Item, I::Range, I::Position>,
//! {
//!     let word = many1(letter());
//!
//!     // A parser which skips past whitespace.
//!     // Since we aren't interested in knowing that our expression parser
//!     // could have accepted additional whitespace between the tokens we also silence the error.
//!     let skip_spaces = || spaces().silent();
//!
//!     //Creates a parser which parses a char and skips any trailing whitespace
//!     let lex_char = |c| char(c).skip(skip_spaces());
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
//!     choice((
//!         word.map(Expr::Id),
//!         array.map(Expr::Array),
//!         pair,
//!     ))
//!         .skip(skip_spaces())
//! }
//!
//! // As this expression parser needs to be able to call itself recursively `impl Parser` can't
//! // be used on its own as that would cause an infinitely large type. We can avoid this by using
//! // the `parser!` macro which erases the inner type and the size of that type entirely which
//! // lets it be used recursively.
//! //
//! // (This macro does not use `impl Trait` which means it can be used in rust < 1.26 as well to
//! // emulate `impl Parser`)
//! parser!{
//!     fn expr[I]()(I) -> Expr
//!     where [I: Stream<Item = char>]
//!     {
//!         expr_()
//!     }
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
//! [mod parser]: parser/index.html
//! [`easy`]: easy/index.html
//! [`error`]: error/index.html
//! [`char`]: parser/char/index.html
//! [`byte`]: parser/byte/index.html
//! [`range`]: parser/range/index.html
//! [`many`]: parser/repeat/fn.many.html
//! [`try`]: parser/combinator/fn.try.html
//! [`satisfy`]: parser/item/fn.satisfy.html
//! [`or`]: parser/trait.Parser.html#method.or
//! [`Stream`]: stream/trait.Stream.html
//! [`RangeStream`]: stream/trait.RangeStream.html
//! [`Parser`]: parser/trait.Parser.html
//! [fn parser]: parser/function/fn.parser.html
//! [`parser!`]: macro.parser.html
// inline(always) is only used on trivial functions returning parsers
#![cfg_attr(
    feature = "cargo-clippy",
    allow(clippy::inline_always, clippy::type_complexity)
)]
#![cfg_attr(feature = "cargo-clippy", feature(tool_lints))]
#![cfg_attr(not(feature = "std"), no_std)]

#[doc(inline)]
pub use error::{ConsumedResult, ParseError, ParseResult};
#[doc(inline)]
pub use parser::Parser;
#[doc(inline)]
pub use stream::{Positioned, RangeStream, RangeStreamOnce, Stream, StreamOnce};

#[doc(inline)]
pub use combinator::{
    any, between, chainl1, chainr1, count, count_min_max, env_parser, eof, look_ahead, many, many1,
    none_of, not_followed_by, one_of, optional, parser, position, satisfy, satisfy_map, sep_by,
    sep_by1, sep_end_by, sep_end_by1, skip_count, skip_count_min_max, skip_many, skip_many1, token,
    tokens, try, unexpected, unexpected_any, value,
};
#[doc(inline)]
pub use parser::choice::choice;
#[doc(inline)]
pub use parser::combinator::from_str;
#[doc(inline)]
pub use parser::item::tokens2;

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
        where I: Stream<Item=$ty>,
              I::Error: ParseError<$ty, I::Range, I::Position>
              $(, $ty_var : Parser<Input=I>)*;
    impl <I $(,$ty_var)*> Parser for $name<I $(,$ty_var)*>
        where I: Stream<Item=$ty>,
              I::Error: ParseError<$ty, I::Range, I::Position>
              $(, $ty_var : Parser<Input=I>)*
    {
        type Input = I;
        type Output = <$inner_type as Parser>::Output;
        type PartialState = <$inner_type as Parser>::PartialState;

        forward_parser!(0);
    }
}
}

/// Declares a named parser which can easily be reused.
///
/// The expression which creates the parser should have no side effects as it may be called
/// multiple times even during a single parse attempt.
///
/// NOTE: If you are using rust nightly you can use `impl Trait` instead. See the [json parser][] for
/// an example.
///
/// [json parser]:https://github.com/Marwes/combine/blob/master/benches/json.rs
///
/// ```
/// #[macro_use]
/// extern crate combine;
/// use combine::parser::char::digit;
/// use combine::{any, choice, from_str, many1, Parser, Stream};
/// use combine::error::ParseError;
///
/// parser!{
///     /// `[I]` represents a normal type parameters and lifetime declaration for the function
///     /// It gets expanded to `<I>`
///     fn integer[I]()(I) -> i32
///     where [
///         I: Stream<Item = char>,
///         I::Error: ParseError<char, I::Range, I::Position>,
///         <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
///             From<::std::num::ParseIntError>,
///     ]
///     {
///         // The body must be a block body ( `{ <block body> }`) which ends with an expression
///         // which evaluates to a parser
///         from_str(many1::<String, _>(digit()))
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
///     where [
///         I: Stream<Item = char>,
///         I::Error: ParseError<char, I::Range, I::Position>,
///         <I::Error as ParseError<I::Item, I::Range, I::Position>>::StreamError:
///             From<::std::num::ParseIntError>,
///     ]
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
///     assert_eq!(integer().easy_parse("123"), Ok((123, "")));
///     assert!(integer().easy_parse("!").is_err());
///
///     assert_eq!(
///         integer_or_string().easy_parse("123"),
///         Ok((IntOrString::Int(123), ""))
///     );
///     assert_eq!(
///         integer_or_string().easy_parse("abc"),
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
        $parser: block
    ) => {
        parser!{
            $(#[$attr])*
            pub fn $name [$($type_params)*]( $($arg : $arg_type),* )($input_type) -> $output_type
                where []
            $parser
        }
    };
    (
        $(#[$attr:meta])*
        fn $name: ident [$($type_params: tt)*]( $($arg: ident :  $arg_type: ty),* )
            ($input_type: ty) -> $output_type: ty
        $parser: block
    ) => {
        parser!{
            $(#[$attr])*
            fn $name [$($type_params)*]( $($arg : $arg_type),* )($input_type) -> $output_type
                where []
            $parser
        }
    };
    (
        $(#[$attr:meta])*
        pub fn $name: ident [$($type_params: tt)*]( $($arg: ident :  $arg_type: ty),* )
            ($input_type: ty) -> $output_type: ty
            where [$($where_clause: tt)*]
        $parser: block
    ) => {
        combine_parser_impl!{
            (pub)
            struct $name;
            type PartialState = (());
            $(#[$attr])*
            fn $name [$($type_params)*]($($arg : $arg_type),*)($input_type) -> $output_type
                where [$($where_clause)*]
            $parser
        }
    };
    (
        $(#[$attr:meta])*
        fn $name: ident [$($type_params: tt)*]( $($arg: ident :  $arg_type: ty),*)
            ($input_type: ty) -> $output_type: ty
            where [$($where_clause: tt)*]
        $parser: block
    ) => {
        combine_parser_impl!{
            ()
            struct $name;
            type PartialState = (());
            $(#[$attr])*
            fn $name [$($type_params)*]($($arg : $arg_type),*)($input_type) -> $output_type
                where [$($where_clause)*]
            $parser
        }
    };
    (
        $(#[$derive:meta])*
        pub struct $type_name: ident;
        $(#[$attr:meta])*
        pub fn $name: ident [$($type_params: tt)*]( $($arg: ident :  $arg_type: ty),* )
            ($input_type: ty) -> $output_type: ty
            where [$($where_clause: tt)*]
        $parser: block
    ) => {
        combine_parser_impl!{
            (pub)
            $(#[$derive])*
            struct $type_name;
            type PartialState = (());
            $(#[$attr])*
            fn $name [$($type_params)*]($($arg : $arg_type),*)($input_type) -> $output_type
                where [$($where_clause)*]
            $parser
        }
    };
    (
        $(#[$derive:meta])*
        struct $type_name: ident;
        $(#[$attr:meta])*
        fn $name: ident [$($type_params: tt)*]( $($arg: ident :  $arg_type: ty),*)
            ($input_type: ty) -> $output_type: ty
            where [$($where_clause: tt)*]
        $parser: block
    ) => {
        combine_parser_impl!{
            ()
            $(#[$derive])*
            struct $type_name;
            type PartialState = (());
            $(#[$attr:meta])*
            fn $name [$($type_params)*]($($arg : $arg_type),*)($input_type) -> $output_type
                where [$($where_clause)*]
            $parser
        }
    };
    (
        type PartialState = $partial_state: ty;
        $(#[$attr:meta])*
        pub fn $name: ident [$($type_params: tt)*]( $($arg: ident :  $arg_type: ty),* )
            ($input_type: ty) -> $output_type: ty
            $parser: block
    ) => {
        parser!{
            type PartialState = $partial_state;
            $(#[$attr])*
            pub fn $name [$($type_params)*]( $($arg : $arg_type),* )($input_type) -> $output_type
                where []
            $parser
        }
    };
    (
        type PartialState = $partial_state: ty;
        $(#[$attr:meta])*
        fn $name: ident [$($type_params: tt)*]( $($arg: ident :  $arg_type: ty),* )
            ($input_type: ty) -> $output_type: ty
            $parser: block
    ) => {
        parser!{
            type PartialState = $partial_state;
            $(#[$attr])*
            fn $name [$($type_params)*]( $($arg : $arg_type),* )($input_type) -> $output_type
                where []
            $parser
        }
    };
    (
        type PartialState = $partial_state: ty;
        $(#[$attr:meta])*
        pub fn $name: ident [$($type_params: tt)*]( $($arg: ident :  $arg_type: ty),* )
            ($input_type: ty) -> $output_type: ty
            where [$($where_clause: tt)*]
        $parser: block
    ) => {
        combine_parser_impl!{
            (pub)
            struct $name;
            type PartialState = ($partial_state);
            $(#[$attr])*
            pub fn $name [$($type_params)*]($($arg : $arg_type),*)($input_type) -> $output_type
                where [$($where_clause)*]
            $parser
        }
    };
    (
        type PartialState = $partial_state: ty;
        $(#[$attr:meta])*
        fn $name: ident [$($type_params: tt)*]( $($arg: ident :  $arg_type: ty),*)
            ($input_type: ty) -> $output_type: ty
            where [$($where_clause: tt)*]
        $parser: block
    ) => {
        combine_parser_impl!{
            ()
            struct $name;
            type PartialState = ($partial_state);
            $(#[$attr])*
            fn $name [$($type_params)*]($($arg : $arg_type),*)($input_type) -> $output_type
                where [$($where_clause)*]
            $parser
        }
    };
    (
        $(#[$derive:meta])*
        pub struct $type_name: ident;
        type PartialState = $partial_state: ty;
        $(#[$attr:meta])*
        pub fn $name: ident [$($type_params: tt)*]( $($arg: ident :  $arg_type: ty),* )
            ($input_type: ty) -> $output_type: ty
            where [$($where_clause: tt)*]
        $parser: block
    ) => {
        combine_parser_impl!{
            (pub)
            $(#[$derive])*
            struct $type_name;
            type PartialState = ($partial_state);
            $(#[$attr])*
            fn $name [$($type_params)*]($($arg : $arg_type),*)($input_type) -> $output_type
                where [$($where_clause)*]
            $parser
        }
    };
    (
        $(#[$derive:meta])*
        struct $type_name: ident;
        type PartialState = $partial_state: ty;
        $(#[$attr:meta])*
        fn $name: ident [$($type_params: tt)*]( $($arg: ident :  $arg_type: ty),*)
            ($input_type: ty) -> $output_type: ty
            where [$($where_clause: tt)*]
        $parser: block
    ) => {
        combine_parser_impl!{
            ()
            $(#[$derive])*
            struct $type_name;
            type PartialState = ($partial_state);
            $(#[$attr:meta])*
            fn $name [$($type_params)*]($($arg : $arg_type),*)($input_type) -> $output_type
                where [$($where_clause)*]
            $parser
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! combine_parse_partial {
    ((()) $mode:ident $input:ident $state:ident $parser:block) => {{
        let _ = $state;
        let mut state = Default::default();
        let state = &mut state;
        $parser.parse_mode($mode, $input, state)
    }};
    (($ignored:ty) $mode:ident $input:ident $state:ident $parser:block) => {
        $parser.parse_mode($mode, $input, $state)
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! combine_parser_impl {
    (
        ( $($pub_: tt)* )
        $(#[$derive:meta])*
        struct $type_name: ident;
        type PartialState = ($($partial_state: tt)*);
        $(#[$attr:meta])*
        fn $name: ident [$($type_params: tt)*]( $($arg: ident :  $arg_type: ty),*)
            ($input_type: ty) -> $output_type: ty
            where [$($where_clause: tt)*]
        $parser: block
    ) => {

        $(#[$derive])*
        #[allow(non_camel_case_types)]
        $($pub_)* struct $type_name<$($type_params)*>
            where <$input_type as $crate::stream::StreamOnce>::Error:
                $crate::error::ParseError<
                    <$input_type as $crate::stream::StreamOnce>::Item,
                    <$input_type as $crate::stream::StreamOnce>::Range,
                    <$input_type as $crate::stream::StreamOnce>::Position
                    >,
                $($where_clause)*
        {
            $(pub $arg : $arg_type,)*
            __marker: $crate::lib::marker::PhantomData<fn ($input_type) -> $output_type>
        }

        // We want this to work on older compilers, at least for a while
        #[allow(non_shorthand_field_patterns)]
        impl<$($type_params)*> $crate::Parser for $type_name<$($type_params)*>
            where <$input_type as $crate::stream::StreamOnce>::Error:
                    $crate::error::ParseError<
                        <$input_type as $crate::stream::StreamOnce>::Item,
                        <$input_type as $crate::stream::StreamOnce>::Range,
                        <$input_type as $crate::stream::StreamOnce>::Position
                        >,
                $($where_clause)*
        {
            type Input = $input_type;
            type Output = $output_type;
            type PartialState = $($partial_state)*;

            parse_mode!();
            #[inline]
            fn parse_mode_impl<M>(
                &mut self,
                mode: M,
                input: &mut Self::Input,
                state: &mut Self::PartialState,
                ) -> $crate::error::ConsumedResult<$output_type, $input_type>
            where M: $crate::parser::ParseMode
            {
                let $type_name { $( $arg: ref mut $arg,)* .. } = *self;
                combine_parse_partial!(($($partial_state)*) mode input state $parser)
            }

            #[inline]
            fn add_error(
                &mut self,
                errors: &mut $crate::error::Tracked<
                    <$input_type as $crate::stream::StreamOnce>::Error
                    >)
            {
                let $type_name { $( $arg : ref mut $arg,)*  .. } = *self;
                let mut parser = $parser;
                {
                    let _: &mut $crate::Parser<Input = $input_type, Output = $output_type, PartialState = _> = &mut parser;
                }
                parser.add_error(errors)
            }

            fn add_consumed_expected_error(
                &mut self,
                errors: &mut $crate::error::Tracked<
                    <$input_type as $crate::stream::StreamOnce>::Error
                    >)
            {
                let $type_name { $( $arg : ref mut $arg,)*  .. } = *self;
                let mut parser = $parser;
                {
                    let _: &mut $crate::Parser<Input = $input_type, Output = $output_type, PartialState = _> = &mut parser;
                }
                parser.add_consumed_expected_error(errors)
            }
        }

        $(#[$attr])*
        #[inline(always)]
        $($pub_)* fn $name< $($type_params)* >(
                $($arg : $arg_type),*
            ) -> $type_name<$($type_params)*>
            where <$input_type as $crate::stream::StreamOnce>::Error:
                    $crate::error::ParseError<
                        <$input_type as $crate::stream::StreamOnce>::Item,
                        <$input_type as $crate::stream::StreamOnce>::Range,
                        <$input_type as $crate::stream::StreamOnce>::Position
                        >,
                $($where_clause)*
        {
            $type_name {
                $($arg : $arg,)*
                __marker: $crate::lib::marker::PhantomData
            }
        }
    };
}

pub extern crate byteorder;
#[cfg(feature = "bytes")]
extern crate bytes;
pub extern crate either;

extern crate memchr;
extern crate unreachable;

/// Internal API. May break without a semver bump
macro_rules! forward_parser {
    (, $($field: tt)+) => {
    };
    ($method: ident $( $methods: ident)*, $($field: tt)*) => {
        forward_parser!($method $($field)+);
        forward_parser!($($methods)*, $($field)+);
    };
    (parse_mode $($field: tt)+) => {
        #[inline]
        fn parse_mode_impl<M>(
            &mut self,
            mode: M,
            input: &mut Self::Input,
            state: &mut Self::PartialState,
        ) -> ConsumedResult<Self::Output, Self::Input>
        where
            M: ParseMode,
        {
            self.$($field)+.parse_mode(mode, input, state).map(|(a, _)| a)
        }
    };
    (parse_lazy $($field: tt)+) => {
        fn parse_lazy(
            &mut self,
            input: &mut Self::Input,
        ) -> ConsumedResult<Self::Output, Self::Input> {
            self.$($field)+.parse_lazy(input)
        }
    };
    (parse_first $($field: tt)+) => {
        fn parse_first(
            &mut self,
            input: &mut Self::Input,
            state: &mut Self::PartialState,
        ) -> ConsumedResult<Self::Output, Self::Input> {
            self.$($field)+.parse_first(input, state)
        }
    };
    (parse_partial $($field: tt)+) => {
        fn parse_partial(
            &mut self,
            input: &mut Self::Input,
            state: &mut Self::PartialState,
        ) -> ConsumedResult<Self::Output, Self::Input> {
            self.$($field)+.parse_partial(input, state)
        }
    };
    (add_error $($field: tt)+) => {

        fn add_error(&mut self, error: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
            self.$($field)+.add_error(error)
        }
    };
    (add_consumed_expected_error $($field: tt)+) => {
        fn add_consumed_expected_error(&mut self, error: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
            self.$($field)+.add_consumed_expected_error(error)
        }
    };
    (parser_count $($field: tt)+) => {
        fn parser_count(&self) -> $crate::ErrorOffset {
            self.$($field)+.parser_count()
        }
    };
    ($field: tt) => {
        forward_parser!(parse_lazy parse_first parse_partial add_error add_consumed_expected_error parser_count, $field);
    }
}

// Facade over the core types we need
// Public but hidden to be accessible in macros
#[doc(hidden)]
pub mod lib {
    #[cfg(not(feature = "std"))]
    pub use core::*;
    #[cfg(feature = "std")]
    pub use std::*;
}

#[cfg(feature = "std")]
#[doc(inline)]
pub use stream::easy;

/// Error types and traits which define what kind of errors combine parsers may emit
#[macro_use]
pub mod error;
#[macro_use]
pub mod stream;
#[macro_use]
pub mod parser;

/// Re-exported parsers for compatibility with older versions
#[doc(hidden)]
#[deprecated(
    since = "3.0.0",
    note = "Please import parsers from the `parser` module and its submodules instead"
)]
pub mod combinator {
    #[doc(inline)]
    pub use parser::choice::*;
    #[doc(inline)]
    pub use parser::combinator::*;
    #[doc(inline)]
    pub use parser::error::*;
    #[doc(inline)]
    pub use parser::function::*;
    #[doc(inline)]
    pub use parser::item::*;
    #[doc(inline)]
    pub use parser::repeat::*;
    #[doc(inline)]
    pub use parser::sequence::*;
}

#[doc(hidden)]
#[deprecated(
    since = "3.0.0",
    note = "Please use the `parser::char` module instead"
)]
pub use parser::char;

#[doc(hidden)]
#[deprecated(
    since = "3.0.0",
    note = "Please use the `parser::byte` module instead"
)]
pub use parser::byte;

#[doc(hidden)]
#[deprecated(
    since = "3.0.0",
    note = "Please use the `parser::range` module instead"
)]
pub use parser::range;

#[doc(hidden)]
#[deprecated(
    since = "3.0.0",
    note = "Please use the `parser::regex` module instead"
)]
#[cfg(any(feature = "regex", feature = "regex-1"))]
pub use parser::regex;

#[doc(hidden)]
#[derive(Clone, PartialOrd, PartialEq, Debug, Copy)]
pub struct ErrorOffset(u8);

#[cfg(test)]
mod tests {
    use super::*;
    use parser::char::{char, string};

    #[test]
    fn chainl1_error_consume() {
        fn first<T, U>(t: T, _: U) -> T {
            t
        }
        let mut p = chainl1(string("abc"), char(',').map(|_| first));
        assert!(p.parse("abc,ab").is_err());
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
}

#[cfg(all(feature = "std", test))]
mod std_tests {
    use super::easy::Error;
    use super::error::Consumed;
    use super::stream::IteratorStream;
    use super::*;

    use parser::char::{alpha_num, char, digit, letter, spaces, string};
    use stream::easy;
    use stream::state::{SourcePosition, State};

    #[test]
    fn optional_error_consume() {
        let mut p = optional(string("abc"));
        let err = p.easy_parse(State::new("ab")).unwrap_err();
        assert_eq!(err.position, SourcePosition { line: 1, column: 1 });
    }

    fn follow<I>(input: &mut I) -> ParseResult<(), I>
    where
        I: Stream<Item = char, Error = easy::ParseError<I>>,
        I::Position: Default,
    {
        let before = input.checkpoint();
        match input.uncons() {
            Ok(c) => {
                if c.is_alphanumeric() {
                    input.reset(before);
                    let e = Error::Unexpected(c.into());
                    Err(Consumed::Empty(
                        easy::Errors::new(input.position(), e).into(),
                    ))
                } else {
                    Ok(((), Consumed::Empty(())))
                }
            }
            Err(_) => Ok(((), Consumed::Empty(()))),
        }
    }

    fn integer<'a, I>(input: &mut I) -> ParseResult<i64, I>
    where
        I: Stream<Item = char>,
        I::Error: ParseError<I::Item, I::Range, I::Position>,
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
        let mut parsed_state = State::with_positioner(source, SourcePosition::new());
        let result = (spaces(), parser(integer), spaces())
            .map(|t| t.1)
            .parse_stream(&mut parsed_state);
        let state = Consumed::Consumed(State {
            positioner: SourcePosition { line: 3, column: 1 },
            input: "",
        });
        assert_eq!(
            result.map(|(x, c)| (x, c.map(|_| parsed_state))),
            Ok((123i64, state))
        );
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
            spaces()
                .silent()
                .with(
                    word.map(Expr::Id)
                        .or(integer.map(Expr::Int))
                        .or(array.map(Expr::Array))
                        .or(paren_expr),
                )
                .skip(spaces().silent())
        }
    }

    #[test]
    fn expression_basic() {
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
        let result = expr().easy_parse(State::new(input));
        let err = easy::Errors {
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

    fn term<I>(input: &mut I) -> ParseResult<Expr, I>
    where
        I: Stream<Item = char>,
        I::Error: ParseError<I::Item, I::Range, I::Position>,
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

    #[test]
    fn error_position() {
        let mut p = string("let")
            .skip(parser(follow))
            .map(|x| x.to_string())
            .or(many1(digit()));
        match p.easy_parse(State::new("le123")) {
            Ok(_) => assert!(false),
            Err(err) => assert_eq!(err.position, SourcePosition { line: 1, column: 1 }),
        }
        match p.easy_parse(State::new("let1")) {
            Ok(_) => assert!(false),
            Err(err) => assert_eq!(err.position, SourcePosition { line: 1, column: 4 }),
        }
    }

    #[test]
    fn sep_by_error_consume() {
        let mut p = sep_by::<Vec<_>, _, _>(string("abc"), char(','));
        let err = p.easy_parse(State::new("ab,abc")).unwrap_err();
        assert_eq!(err.position, SourcePosition { line: 1, column: 1 });
    }

    #[test]
    fn inner_error_consume() {
        let mut p = many::<Vec<_>, _>(between(char('['), char(']'), digit()));
        let result = p.easy_parse(State::new("[1][2][]"));
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
        let mut parser: Box<Parser<Input = _, Output = char, PartialState = _>> = Box::new(digit());
        let borrow_parser = &mut *parser;
        assert_eq!(borrow_parser.parse("1"), Ok(('1', "")));
    }

    #[test]
    fn std_error() {
        use std::error::Error as StdError;
        use std::fmt;
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
        let result: Result<((), _), easy::Errors<char, &str, _>> =
            Parser::easy_parse(&mut string("abc").and_then(|_| Err(Error)), "abc");
        assert!(result.is_err());
        // Test that ParseError can be coerced to a StdError
        let _ = result.map_err(|err| {
            let err: Box<StdError> = Box::new(err);
            err
        });
    }

    #[test]
    fn extract_std_error() {
        // The previous test verified that we could map a ParseError to a StdError by dropping
        // the internal error details.
        // This test verifies that we can map a ParseError to a StdError
        // without dropping the internal error details.  Consumers using `error-chain` will
        // appreciate this.  For technical reasons this is pretty janky; see the discussion in
        // https://github.com/Marwes/combine/issues/86, and excuse the test with significant
        // boilerplate!
        use std::error::Error as StdError;
        use std::fmt;

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
            .easy_parse(input)
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

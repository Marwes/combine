use lib::marker::PhantomData;

use {ErrorOffset, Parser, Stream, StreamOnce};
use primitives::{ConsumedResult, ParseError, ParseMode, StreamError, Tracked, UnexpectedParse};
use primitives::FastResult::*;
use combinator::{ignore, Ignore};

macro_rules! dispatch_on {
    ($i: expr, $f: expr;) => {
    };
    ($i: expr, $f: expr; $first: ident $(, $id: ident)*) => { {
        if $f($i, $first) {
            dispatch_on!($i + 1, $f; $($id),*);
        }
    } }
}

#[doc(hidden)]
pub struct SequenceState<T, U> {
    pub value: Option<T>,
    pub state: U,
}

#[doc(hidden)]
pub type ParserSequenceState<P> = SequenceState<<P as Parser>::Output, <P as Parser>::PartialState>;

impl<T, U: Default> Default for SequenceState<T, U> {
    fn default() -> Self {
        SequenceState {
            value: None,
            state: U::default(),
        }
    }
}

impl<T, U> SequenceState<T, U>
where
    U: Default,
{
    unsafe fn unwrap_value(&mut self) -> T {
        match self.value.take() {
            Some(t) => t,
            None => ::unreachable::unreachable(),
        }
    }
}

macro_rules! tuple_parser {
    ($partial_state: ident; $h: ident, $($id: ident),+) => {
        #[allow(non_snake_case)]
        #[derive(Default)]
        pub struct $partial_state < $h $(, $id )* > {
            pub $h: $h,
            $(
                pub $id: $id,
            )*
            offset: u8,
            _marker: PhantomData <( $h $(, $id)* )>,
        }


        #[allow(non_snake_case)]
        impl<Input, $h $(, $id)*> $partial_state<$h $(, $id)*>
        where Input: Stream,
              Input::Error: ParseError<Input::Item, Input::Range, Input::Position>,
              $h: Parser<Input=Input>,
              $($id: Parser<Input=Input>),+
        {
            fn add_errors(
                input: &mut Input,
                mut err: Tracked<Input::Error>,
                first_empty_parser: usize,
                offset: u8,
                $h: &mut $h $(, $id : &mut $id )*
            ) -> ConsumedResult<($h::Output, $($id::Output),+), Input>
            {
                err.offset = ErrorOffset(offset);
                if first_empty_parser != 0 {
                    if let Ok(t) = input.uncons::<UnexpectedParse>() {
                        err.error.add(StreamError::unexpected_token(t));
                    }
                    dispatch_on!(0, |i, mut p| {
                        if i >= first_empty_parser {
                            Parser::add_error(&mut p, &mut err);
                            if err.offset <= ErrorOffset(1) {
                                return false;
                            }
                        }
                            err.offset = ErrorOffset(
                                err.offset.0.saturating_sub(Parser::parser_count(&p).0)
                            );
                        true
                    }; $h, $($id),*);
                    ConsumedErr(err.error)
                } else {
                    EmptyErr(err)
                }
            }
        }

        #[allow(non_snake_case)]
        impl <Input: Stream, $h:, $($id:),+> Parser for ($h, $($id),+)
            where Input: Stream,
                  Input::Error: ParseError<Input::Item, Input::Range, Input::Position>,
                  $h: Parser<Input=Input>,
                  $($id: Parser<Input=Input>),+
        {
            type Input = Input;
            type Output = ($h::Output, $($id::Output),+);
            type PartialState = $partial_state<
                SequenceState<$h::Output, $h::PartialState>
                $(, SequenceState<$id::Output, $id::PartialState>)*
            >;

            parse_mode!();
            fn parse_mode_impl<M>(
                &mut self,
                mut mode: M,
                input: &mut Self::Input,
                state: &mut Self::PartialState,
            ) -> ConsumedResult<Self::Output, Self::Input>
            where
                M: ParseMode,
            {
                let (ref mut $h, $(ref mut $id),+) = *self;
                let mut first_empty_parser = 0;
                let mut current_parser = 0;

                macro_rules! add_errors {
                    ($err: ident, $offset: expr) => {
                        $partial_state::add_errors(
                            input, $err, first_empty_parser, $offset, $h, $($id),*
                        )
                    }
                }

                if let None = state.$h.value {
                    let temp = match $h.parse_mode(mode, input, &mut state.$h.state) {
                        ConsumedOk(x) => {
                            first_empty_parser = current_parser + 1;
                            x
                        }
                        EmptyErr(err) => return EmptyErr(err),
                        ConsumedErr(err) => return ConsumedErr(err),
                        EmptyOk(x) => {
                            x
                        }
                    };
                    state.offset = $h.parser_count().0.saturating_add(1);
                    state.$h.value = Some(temp);

                    // Once we have successfully parsed the partial input we may resume parsing in
                    // "first mode"
                    mode.set_first();
                }

                $(
                    if let None = state.$id.value {
                        current_parser += 1;
                        let before = input.checkpoint();
                        let temp = match $id.parse_mode(mode, input, &mut state.$id.state) {
                            ConsumedOk(x) => {
                                first_empty_parser = current_parser + 1;
                                x
                            }
                            EmptyErr(err) => {
                                input.reset(before);
                                return add_errors!(err, state.offset)
                            }
                            ConsumedErr(err) => return ConsumedErr(err),
                            EmptyOk(x) => {
                                x
                            }
                        };
                        state.offset = state.offset.saturating_add($id.parser_count().0);
                        state.$id.value = Some(temp);

                        // Once we have successfully parsed the partial input we may resume parsing in
                        // "first mode"
                        mode.set_first();
                    }
                )+

                let value = unsafe { (state.$h.unwrap_value(), $(state.$id.unwrap_value()),+) };
                if first_empty_parser != 0 {
                    ConsumedOk(value)
                } else {
                    EmptyOk(value)
                }
            }

            #[inline(always)]
            fn parser_count(&self) -> ErrorOffset {
                let (ref $h, $(ref $id),+) = *self;
                ErrorOffset($h.parser_count().0 $( + $id.parser_count().0)+)
            }

            #[inline(always)]
            fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
                let (ref mut $h, $(ref mut $id),+) = *self;
                $h.add_error(errors);
                if errors.offset <= ErrorOffset(1) {
                    return;
                }
                errors.offset = ErrorOffset(errors.offset.0.saturating_sub($h.parser_count().0));
                $(
                    $id.add_error(errors);
                    if errors.offset <= ErrorOffset(1) {
                        return;
                    }
                    errors.offset = ErrorOffset(
                        errors.offset.0.saturating_sub($id.parser_count().0)
                    );
                )*
            }
        }
    }
}

tuple_parser!(PartialState2; A, B);
tuple_parser!(PartialState3; A, B, C);
tuple_parser!(PartialState4; A, B, C, D);
tuple_parser!(PartialState5; A, B, C, D, E);
tuple_parser!(PartialState6; A, B, C, D, E, F);
tuple_parser!(PartialState7; A, B, C, D, E, F, G);
tuple_parser!(PartialState8; A, B, C, D, E, F, G, H);
tuple_parser!(PartialState9; A, B, C, D, E, F, G, H, I);
tuple_parser!(PartialState10; A, B, C, D, E, F, G, H, I, J);
tuple_parser!(PartialState11; A, B, C, D, E, F, G, H, I, J, K);
tuple_parser!(PartialState12; A, B, C, D, E, F, G, H, I, J, K, L);

#[macro_export]
#[doc(hidden)]
macro_rules! seq_parser_expr {
    (; $($tt: tt)*) => {
        ( $($tt)* )
    };
    ( (_ : $first_parser: expr, $($remaining: tt)+ ); $($tt: tt)*) => {
        seq_parser_expr!( ( $($remaining)+ ) ; $($tt)* $first_parser, )
    };
    ( ($first_field: ident : $first_parser: expr, $($remaining: tt)+ ); $($tt: tt)*) => {
        seq_parser_expr!( ( $($remaining)+ ) ; $($tt)* $first_parser, )
    };
    ( (_ : $first_parser: expr ); $($tt: tt)*) => {
        ( $($tt)* $first_parser, )
    };
    ( ($first_field: ident : $first_parser: expr, ); $($tt: tt)*) => {
        seq_parser_expr!(; $($tt)* $first_parser,)
    };
    ( (_ : $first_parser: expr, ); $($tt: tt)*) => {
        ( $($tt)* $first_parser, )
    };
    ( ($first_field: ident : $first_parser: expr ); $($tt: tt)*) => {
        seq_parser_expr!(; $($tt)* $first_parser,)
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! seq_parser_pattern {
    (; $($tt: tt)*) => {
       ( $($tt)* )
    };
    ( (_ : $first_parser: expr, $($remaining: tt)+ ); $($tt: tt)*) => {
        seq_parser_pattern!( ( $($remaining)+ ) ; $($tt)* _, )
    };
    ( ($first_field: ident : $first_parser: expr, $($remaining: tt)+ ); $($tt: tt)*) => {
        seq_parser_pattern!( ( $($remaining)+ ) ; $($tt)* $first_field, )
    };
    ( ( _ : $first_parser: expr ); $($tt: tt)*) => {
        seq_parser_pattern!(; $($tt)* _, )
    };
    ( ($first_field: ident : $first_parser: expr ); $($tt: tt)*) => {
        seq_parser_pattern!(; $($tt)* $first_field,)
    };
    ( ( _ : $first_parser: expr, ); $($tt: tt)*) => {
        seq_parser_pattern!(; $($tt)* _, )
    };
    ( ($first_field: ident : $first_parser: expr, ); $($tt: tt)*) => {
        seq_parser_pattern!(; $($tt)* $first_field,)
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! seq_parser_impl {
    (; $name: ident $($tt: tt)*) => {
        $name { $($tt)* }
    };
    ( (_ : $first_parser: expr, $($remaining: tt)+ ); $name: ident $($tt: tt)*) => {
        seq_parser_impl!( ( $($remaining)+ ) ; $name $($tt)* )
    };
    ( ($first_field: ident : $first_parser: expr, $($remaining: tt)+ );
        $name: ident $($tt: tt)*) =>
    {
        seq_parser_impl!( ( $($remaining)+ ) ; $name $($tt)* $first_field: $first_field, )
    };
    ( ( _ : $first_parser: expr ); $name: ident $($tt: tt)*) => {
        seq_parser_impl!( ; $name $($tt)* )
    };
    ( ($first_field: ident : $first_parser: expr ); $name: ident $($tt: tt)*) => {
        seq_parser_impl!(; $name $($tt)* $first_field: $first_field,)
    };
    ( ( _ : $first_parser: expr, ); $name: ident $($tt: tt)*) => {
        seq_parser_impl!(; $name $($tt)*)
    };
    ( ($first_field: ident : $first_parser: expr, ); $name: ident $($tt: tt)*) => {
        seq_parser_impl!(; $name $($tt)* $first_field: $first_field,)
    };
}

/// Sequences multiple parsers and builds a struct out of them.
///
/// ```
/// #[macro_use]
/// extern crate combine;
/// use combine::{Parser, many, token};
/// use combine::byte::{letter, spaces};
///
/// #[derive(Debug, PartialEq)]
/// struct Field {
///     name: Vec<u8>,
///     value: Vec<u8>,
/// }
/// fn main() {
///     let mut parser = struct_parser!{
///         Field {
///             name: many(letter()),
///             // `_` fields are ignored when building the struct
///             _: spaces(),
///             _: token(b':'),
///             _: spaces(),
///             value: many(letter()),
///         }
///     };
///     assert_eq!(
///         parser.parse(&b"test: data"[..]),
///         Ok((Field { name: b"test"[..].to_owned(), value: b"data"[..].to_owned() }, &b""[..]))
///     );
/// }
/// ```
#[macro_export]
macro_rules! struct_parser {
    ($name: ident { $($tt: tt)* }) => {
        seq_parser_expr!( ( $($tt)* ); )
            .map(|seq_parser_pattern!( ( $($tt)* ); )|
                seq_parser_impl!(( $($tt)* ); $name )
            )
    }
}

#[derive(Copy, Clone)]
pub struct With<P1, P2>((Ignore<P1>, P2))
where
    P1: Parser,
    P2: Parser;
impl<I, P1, P2> Parser for With<P1, P2>
where
    I: Stream,
    P1: Parser<Input = I>,
    P2: Parser<Input = I>,
{
    type Input = I;
    type Output = P2::Output;
    type PartialState = <(Ignore<P1>, P2) as Parser>::PartialState;

    #[inline]
    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        self.0.parse_lazy(input).map(|(_, b)| b)
    }

    parse_mode!();
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
        self.0.parse_mode(mode, input, state).map(|(_, b)| b)
    }

    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.0.add_error(errors)
    }
}

/// Equivalent to [`p1.with(p2)`].
///
/// [`p1.with(p2)`]: ../primitives/trait.Parser.html#method.with
#[inline(always)]
pub fn with<P1, P2>(p1: P1, p2: P2) -> With<P1, P2>
where
    P1: Parser,
    P2: Parser<Input = P1::Input>,
{
    With((ignore(p1), p2))
}

#[derive(Copy, Clone)]
pub struct Skip<P1, P2>((P1, Ignore<P2>))
where
    P1: Parser,
    P2: Parser;
impl<I, P1, P2> Parser for Skip<P1, P2>
where
    I: Stream,
    P1: Parser<Input = I>,
    P2: Parser<Input = I>,
{
    type Input = I;
    type Output = P1::Output;
    type PartialState = <(P1, Ignore<P2>) as Parser>::PartialState;

    parse_mode!();
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
        self.0.parse_mode(mode, input, state).map(|(a, _)| a)
    }

    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.0.add_error(errors)
    }
}

#[inline(always)]
pub fn skip<P1, P2>(p1: P1, p2: P2) -> Skip<P1, P2>
where
    P1: Parser,
    P2: Parser<Input = P1::Input>,
{
    Skip((p1, ignore(p2)))
}

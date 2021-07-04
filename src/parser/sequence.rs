//! Combinators which take multiple parsers and applies them one after another.

use crate::{
    error::{
        ParseError,
        ParseResult::{self, *},
        StreamError, Tracked,
    },
    lib::marker::PhantomData,
    parser::{
        combinator::{ignore, Ignore, Map},
        ParseMode,
    },
    ErrorOffset, Parser, Stream, StreamOnce,
};

macro_rules! dispatch_on {
    ($i: expr, $f: expr;) => {
    };
    ($i: expr, $f: expr; $first: ident $(, $id: ident)*) => { {
        let b = $f($i, $first);
        if b {
            dispatch_on!($i + 1, $f; $($id),*);
        }
    } }
}

macro_rules! count {
    () => { 0 };
    ($f: ident) => { 1 };
    ($f: ident, $($rest: ident),+) => { 1 + count!($($rest),*) };
}

#[doc(hidden)]
pub struct SequenceState<T, U> {
    pub value: Option<T>,
    pub state: U,
}

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
            None => core::hint::unreachable_unchecked(),
        }
    }
}

macro_rules! last_ident {
    ($id: ident) => { $id };
    ($id: ident, $($rest: ident),+) => { last_ident!($($rest),+) };
}

macro_rules! tuple_parser {
    ($partial_state: ident; $h: ident $(, $id: ident)*) => {
        #[allow(non_snake_case)]
        #[derive(Default)]
        pub struct $partial_state < $h $(, $id )* > {
            pub $h: $h,
            $(
                pub $id: $id,
            )*
            #[allow(dead_code)]
            offset: u8,
            _marker: PhantomData <( $h, $( $id),* )>,
        }


        #[allow(non_snake_case)]
        impl<$h $(, $id)*> $partial_state<$h $(, $id)*> {
            #[allow(dead_code)]
            fn add_errors<Input>(
                input: &mut Input,
                mut err: Tracked<Input::Error>,
                first_empty_parser: usize,
                offset: u8,
                $h: &mut $h $(, $id : &mut $id )*
            ) -> ParseResult<($h::Output, $($id::Output),*), <Input as StreamOnce>::Error>
                where Input: Stream,
                      Input::Error: ParseError<Input::Token, Input::Range, Input::Position>,
                      $h: Parser<Input>,
                      $($id: Parser<Input>),*
            {
                let inner_offset = err.offset;
                err.offset = ErrorOffset(offset);
                if first_empty_parser != 0 {
                    if let Ok(t) = input.uncons() {
                        err.error.add(StreamError::unexpected_token(t));
                    }
                    dispatch_on!(0, |i, mut p| {
                        if i + 1 == first_empty_parser {
                            Parser::add_committed_expected_error(&mut p, &mut err);
                        }
                        if i >= first_empty_parser {
                            if err.offset <= ErrorOffset(1) {
                                // We reached the last parser we need to add errors to (and the
                                // parser that actually returned the error), use the returned
                                // offset for that parser.
                                err.offset = inner_offset;
                            }
                            Parser::add_error(&mut p, &mut err);
                            if err.offset <= ErrorOffset(1) {
                                return false;
                            }
                        }
                        err.offset = ErrorOffset(
                            err.offset.0.saturating_sub(Parser::parser_count(&p).0)
                        );
                        true
                    }; $h $(, $id)*);
                    CommitErr(err.error)
                } else {
                    PeekErr(err)
                }
            }
        }

        #[allow(non_snake_case)]
        impl <Input: Stream, $h:, $($id:),*> Parser<Input> for ($h, $($id),*)
            where Input: Stream,
                  Input::Error: ParseError<Input::Token, Input::Range, Input::Position>,
                  $h: Parser<Input>,
                  $($id: Parser<Input>),*
        {

            type Output = ($h::Output, $($id::Output),*);
            type PartialState = $partial_state<
                SequenceState<$h::Output, $h::PartialState>
                $(, SequenceState<$id::Output, $id::PartialState>)*
            >;

            parse_mode!(Input);
            #[inline]
            fn parse_mode_impl<MODE>(
                &mut self,
                mut mode: MODE,
                input: &mut Input,
                state: &mut Self::PartialState,
            ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error>
            where
                MODE: ParseMode,
            {
                let (ref mut $h, $(ref mut $id),*) = *self;
                let mut first_empty_parser = 0;
                #[allow(unused_mut)]
                let mut current_parser = 0;

                #[allow(unused_macros)]
                macro_rules! add_errors {
                    ($err: ident, $offset: expr) => {
                        $partial_state::add_errors(
                            input, $err, first_empty_parser, $offset, $h, $($id),*
                        )
                    }
                }

                if mode.is_first() || state.$h.value.is_none() {
                    let temp = match $h.parse_mode(mode, input, &mut state.$h.state) {
                        CommitOk(x) => {
                            first_empty_parser = current_parser + 1;
                            x
                        }
                        PeekErr(err) => return PeekErr(err),
                        CommitErr(err) => return CommitErr(err),
                        PeekOk(x) => {
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
                    if mode.is_first() || state.$id.value.is_none() {
                        current_parser += 1;
                        let before = input.checkpoint();
                        let temp = match $id.parse_mode(mode, input, &mut state.$id.state) {
                            CommitOk(x) => {
                                first_empty_parser = current_parser + 1;
                                x
                            }
                            PeekErr(err) => {
                                if let Err(err) = input.reset(before) {
                                    return if first_empty_parser != 0 {
                                        CommitErr(err.into())
                                    } else {
                                        PeekErr(err.into())
                                    };
                                }
                                return add_errors!(err, state.offset)
                            }
                            CommitErr(err) => return CommitErr(err),
                            PeekOk(x) => {
                                x
                            }
                        };
                        state.offset = state.offset.saturating_add($id.parser_count().0);
                        state.$id.value = Some(temp);

                        // Once we have successfully parsed the partial input we may resume parsing in
                        // "first mode"
                        mode.set_first();
                    }
                )*

                let value = unsafe { (state.$h.unwrap_value(), $(state.$id.unwrap_value()),*) };
                if first_empty_parser != 0 {
                    CommitOk(value)
                } else {
                    PeekOk(value)
                }
            }

            #[inline]
            fn parser_count(&self) -> ErrorOffset {
                let (ref $h, $(ref $id),*) = *self;
                ErrorOffset($h.parser_count().0 $( + $id.parser_count().0)*)
            }

            #[inline]
            fn add_error(&mut self, errors: &mut Tracked<<Input as StreamOnce>::Error>) {
                let (ref mut $h, $(ref mut $id),*) = *self;
                let prev = errors.offset;
                $h.add_error(errors);
                if errors.offset <= ErrorOffset(1) {
                    errors.offset = ErrorOffset(
                        errors.offset.0.saturating_sub(1)
                    );
                    return;
                }
                if errors.offset == prev {
                    errors.offset = ErrorOffset(errors.offset.0.saturating_sub($h.parser_count().0));
                }

                #[allow(dead_code)]
                const LAST: usize = count!($($id),*);
                #[allow(unused_mut, unused_variables)]
                let mut i = 0;
                $(
                    i += 1;
                    let prev = errors.offset;
                    $id.add_error(errors);
                    if errors.offset <= ErrorOffset(1) {
                        errors.offset = ErrorOffset(
                            errors.offset.0.saturating_sub(1)
                        );
                        return;
                    }
                    if i != LAST && errors.offset == prev {
                        errors.offset = ErrorOffset(
                            errors.offset.0.saturating_sub($id.parser_count().0)
                        );
                    }
                )*
            }

            fn add_committed_expected_error(&mut self, errors: &mut Tracked<<Input as StreamOnce>::Error>) {
                #[allow(unused_variables)]
                let (ref mut $h, $(ref mut $id),*) = *self;
                last_ident!($h $(, $id)*).add_committed_expected_error(errors)
            }
        }
    }
}

tuple_parser!(PartialState1; A);
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
tuple_parser!(PartialState13; A, B, C, D, E, F, G, H, I, J, K, L, M);
tuple_parser!(PartialState14; A, B, C, D, E, F, G, H, I, J, K, L, M, N);
tuple_parser!(PartialState15; A, B, C, D, E, F, G, H, I, J, K, L, M, N, P);
tuple_parser!(PartialState16; A, B, C, D, E, F, G, H, I, J, K, L, M, N, P, Q);
tuple_parser!(PartialState17; A, B, C, D, E, F, G, H, I, J, K, L, M, N, P, Q, R);
tuple_parser!(PartialState18; A, B, C, D, E, F, G, H, I, J, K, L, M, N, P, Q, R, S);
tuple_parser!(PartialState19; A, B, C, D, E, F, G, H, I, J, K, L, M, N, P, Q, R, S, T);
tuple_parser!(PartialState20; A, B, C, D, E, F, G, H, I, J, K, L, M, N, P, Q, R, S, T, U);

#[macro_export]
#[doc(hidden)]
macro_rules! seq_parser_expr {
    (; $($tt: tt)*) => {
        ( $($tt)* )
    };
    ( (_ : $first_parser: expr, $($remaining: tt)+ ); $($tt: tt)*) => {
        $crate::seq_parser_expr!( ( $($remaining)+ ) ; $($tt)* $first_parser, )
    };
    ( ($first_field: ident : $first_parser: expr, $($remaining: tt)+ ); $($tt: tt)*) => {
        $crate::seq_parser_expr!( ( $($remaining)+ ) ; $($tt)* $first_parser, )
    };
    ( (_ : $first_parser: expr ); $($tt: tt)*) => {
        ( $($tt)* $first_parser, )
    };
    ( ($first_field: ident : $first_parser: expr, ); $($tt: tt)*) => {
        $crate::seq_parser_expr!(; $($tt)* $first_parser,)
    };
    ( (_ : $first_parser: expr, ); $($tt: tt)*) => {
        ( $($tt)* $first_parser, )
    };
    ( ($first_field: ident : $first_parser: expr ); $($tt: tt)*) => {
        $crate::seq_parser_expr!(; $($tt)* $first_parser,)
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! seq_parser_pattern {
    (; $($tt: tt)*) => {
       ( $($tt)* )
    };
    ( (_ : $first_parser: expr, $($remaining: tt)+ ); $($tt: tt)*) => {
        $crate::seq_parser_pattern!( ( $($remaining)+ ) ; $($tt)* _, )
    };
    ( ($first_field: ident : $first_parser: expr, $($remaining: tt)+ ); $($tt: tt)*) => {
        $crate::seq_parser_pattern!( ( $($remaining)+ ) ; $($tt)* $first_field, )
    };
    ( ( _ : $first_parser: expr ); $($tt: tt)*) => {
        $crate::seq_parser_pattern!(; $($tt)* _, )
    };
    ( ($first_field: ident : $first_parser: expr ); $($tt: tt)*) => {
        $crate::seq_parser_pattern!(; $($tt)* $first_field,)
    };
    ( ( _ : $first_parser: expr, ); $($tt: tt)*) => {
        $crate::seq_parser_pattern!(; $($tt)* _, )
    };
    ( ($first_field: ident : $first_parser: expr, ); $($tt: tt)*) => {
        $crate::seq_parser_pattern!(; $($tt)* $first_field,)
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! seq_parser_impl {
    (; $name: ident $($tt: tt)*) => {
        $name { $($tt)* }
    };
    ( (_ : $first_parser: expr, $($remaining: tt)+ ); $name: ident $($tt: tt)*) => {
        $crate::seq_parser_impl!( ( $($remaining)+ ) ; $name $($tt)* )
    };
    ( ($first_field: ident : $first_parser: expr, $($remaining: tt)+ );
        $name: ident $($tt: tt)*) =>
    {
        $crate::seq_parser_impl!( ( $($remaining)+ ) ; $name $($tt)* $first_field: $first_field, )
    };
    ( ( _ : $first_parser: expr ); $name: ident $($tt: tt)*) => {
        $crate::seq_parser_impl!( ; $name $($tt)* )
    };
    ( ($first_field: ident : $first_parser: expr ); $name: ident $($tt: tt)*) => {
        $crate::seq_parser_impl!(; $name $($tt)* $first_field: $first_field,)
    };
    ( ( _ : $first_parser: expr, ); $name: ident $($tt: tt)*) => {
        $crate::seq_parser_impl!(; $name $($tt)*)
    };
    ( ($first_field: ident : $first_parser: expr, ); $name: ident $($tt: tt)*) => {
        $crate::seq_parser_impl!(; $name $($tt)* $first_field: $first_field,)
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! seq_tuple_extract {
    (; ; $name: ident ;  $($arg: expr),* $(,)? ) => {
        $name( $($arg,)* )
    };

    ( (_ : $first_parser: expr, $($remaining: tt)+ ); ( $first_arg: expr, $($arg: expr),* ) ; $($tt: tt)*) => {
        $crate::seq_tuple_extract!( ( $($remaining)+ ); ( $($arg),* ) ; $($tt)* )
    };

    ( ($first_parser: expr, $($remaining: tt)+ ); ( $first_arg: expr, $($arg: expr),* ) ; $($tt: tt)*) => {
        $crate::seq_tuple_extract!( ( $($remaining)+ ) ; ( $($arg),* ) ; $($tt)* $first_arg, )
    };

    ( (_ : $first_parser: expr $(,)? ); ( $first_arg: expr, $($arg: expr),* ) ; $($tt: tt)*) => {
        $crate::seq_tuple_extract!(; ; $($tt)*)
    };

    ( ($first_parser: expr $(,)? ); ( $first_arg: expr, $($arg: expr),* ) ; $($tt: tt)*) => {
        $crate::seq_tuple_extract!(; ; $($tt)* $first_arg)
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! seq_tuple_parser_impl {
    (; $($tt: tt)*) => {
        ($($tt)*)
    };

    ( (_ : $first_parser: expr, $($remaining: tt)+ ); $($tt: tt)*) => {
        $crate::seq_tuple_parser_impl!( ( $($remaining)+ ) ; $($tt)* $first_parser, )
    };

    ( ($first_parser: expr, $($remaining: tt)+ ); $($tt: tt)*) => {
        $crate::seq_tuple_parser_impl!( ( $($remaining)+ ) ; $($tt)* $first_parser, )
    };

    ( (_ : $first_parser: expr $(,)? ); $($tt: tt)*) => {
        $crate::seq_tuple_parser_impl!(; $($tt)* $first_parser, )
    };

    ( ($first_parser: expr $(,)? ); $($tt: tt)*) => {
        $crate::seq_tuple_parser_impl!(; $($tt)* $first_parser, )
    };
}

/// Sequences multiple parsers and builds a struct out of them.
///
/// ```
/// use combine::{Parser, between, from_str, many, struct_parser, token};
/// use combine::parser::range::take_while1;
/// use combine::parser::byte::{letter, spaces};
///
/// #[derive(Debug, PartialEq)]
/// struct Point(u32, u32);
///
/// #[derive(Debug, PartialEq)]
/// struct Field {
///     name: Vec<u8>,
///     value: Vec<u8>,
///     point: Point,
/// }
/// fn main() {
///     let num = || from_str(take_while1(|b: u8| b >= b'0' && b <= b'9'));
///     let spaced = |b| between(spaces(), spaces(), token(b));
///     let mut parser = struct_parser!{
///         Field {
///             name: many(letter()),
///             // `_` fields are ignored when building the struct
///             _: spaced(b':'),
///             value: many(letter()),
///             _: spaced(b':'),
///             point: struct_parser!(Point(num(), _: spaced(b','), num())),
///         }
///     };
///     assert_eq!(
///         parser.parse(&b"test: data: 123 , 4"[..]),
///         Ok((
///             Field {
///                 name: b"test"[..].to_owned(),
///                 value: b"data"[..].to_owned(),
///                 point: Point(123, 4),
///             },
///             &b""[..]
///         )),
///     );
/// }
/// ```
#[macro_export]
macro_rules! struct_parser {
    ($name: ident { $($tt: tt)* }) => {
        $crate::seq_parser_expr!( ( $($tt)* ); )
            .map(|$crate::seq_parser_pattern!( ( $($tt)* ); )|
                $crate::seq_parser_impl!(( $($tt)* ); $name )
            )
    };

    ($name: ident ( $($arg: tt)* )) => {
        $crate::seq_tuple_parser_impl!( ( $($arg)* ) ; )
            .map(|t|
                $crate::seq_tuple_extract!(
                    ( $($arg)* );
                    (t.0, t.1, t.2, t.3, t.4, t.5, t.6, t.7, t.8, t.9, t.10, t.11, t.12, t.13, t.14);
                    $name ;
                )
            )
    }
}

#[derive(Copy, Clone)]
pub struct With<P1, P2>((Ignore<P1>, P2));
impl<Input, P1, P2> Parser<Input> for With<P1, P2>
where
    Input: Stream,
    P1: Parser<Input>,
    P2: Parser<Input>,
{
    type Output = P2::Output;
    type PartialState = <(Ignore<P1>, P2) as Parser<Input>>::PartialState;

    #[inline]
    fn parse_lazy(
        &mut self,
        input: &mut Input,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error> {
        self.0.parse_lazy(input).map(|(_, b)| b)
    }

    parse_mode!(Input);
    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Input,
        state: &mut Self::PartialState,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error>
    where
        M: ParseMode,
    {
        self.0.parse_mode(mode, input, state).map(|(_, b)| b)
    }

    forward_parser!(Input, add_error add_committed_expected_error parser_count, 0);
}

/// Equivalent to [`p1.with(p2)`].
///
/// [`p1.with(p2)`]: ../trait.Parser.html#method.with
pub fn with<Input, P1, P2>(p1: P1, p2: P2) -> With<P1, P2>
where
    Input: Stream,
    P1: Parser<Input>,
    P2: Parser<Input>,
{
    With((ignore(p1), p2))
}

#[derive(Copy, Clone)]
pub struct Skip<P1, P2>((P1, Ignore<P2>));
impl<Input, P1, P2> Parser<Input> for Skip<P1, P2>
where
    Input: Stream,
    P1: Parser<Input>,
    P2: Parser<Input>,
{
    type Output = P1::Output;
    type PartialState = <(P1, Ignore<P2>) as Parser<Input>>::PartialState;

    parse_mode!(Input);
    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Input,
        state: &mut Self::PartialState,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error>
    where
        M: ParseMode,
    {
        self.0.parse_mode(mode, input, state).map(|(a, _)| a)
    }

    forward_parser!(Input, add_error add_committed_expected_error parser_count, 0);
}

pub fn skip<Input, P1, P2>(p1: P1, p2: P2) -> Skip<P1, P2>
where
    Input: Stream,
    P1: Parser<Input>,
    P2: Parser<Input>,
{
    Skip((p1, ignore(p2)))
}

parser! {
    #[derive(Copy, Clone)]
    pub struct Between;
    type PartialState = <Map<(L, P, R), fn ((L::Output, P::Output, R::Output)) -> P::Output> as Parser<Input>>::PartialState;
/// Parses `open` followed by `parser` followed by `close`.
/// Returns the value of `parser`.
///
/// ```
/// # extern crate combine;
/// # use combine::*;
/// # use combine::parser::char::string;
/// # fn main() {
/// let result = between(token('['), token(']'), string("rust"))
///     .parse("[rust]")
///     .map(|x| x.0);
/// assert_eq!(result, Ok("rust"));
/// # }
/// ```
pub fn between[Input, L, R, P](open: L, close: R, parser: P)(Input) -> P::Output
where [
    Input: Stream,
    L: Parser< Input>,
    R: Parser< Input>,
    P: Parser< Input>,
]
{
    fn middle<T, U, V>((_, x, _): (T, U, V)) -> U {
        x
    }
    (open, parser, close).map(middle)
}
}

#[derive(Copy, Clone)]
pub struct Then<P, F>(P, F);
impl<Input, P, N, F> Parser<Input> for Then<P, F>
where
    Input: Stream,
    F: FnMut(P::Output) -> N,
    P: Parser<Input>,
    N: Parser<Input>,
{
    type Output = N::Output;
    type PartialState = (P::PartialState, Option<(bool, N)>, N::PartialState);

    parse_mode!(Input);
    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        mut mode: M,
        input: &mut Input,
        state: &mut Self::PartialState,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error>
    where
        M: ParseMode,
    {
        let (ref mut p_state, ref mut n_parser_cache, ref mut n_state) = *state;

        if mode.is_first() || n_parser_cache.is_none() {
            debug_assert!(n_parser_cache.is_none());

            let (value, committed) = match self.0.parse_mode(mode, input, p_state) {
                PeekOk(value) => (value, false),
                CommitOk(value) => (value, true),

                PeekErr(err) => return PeekErr(err),
                CommitErr(err) => return CommitErr(err),
            };

            *n_parser_cache = Some((committed, (self.1)(value)));
            mode.set_first();
        }

        let result = n_parser_cache
            .as_mut()
            .unwrap()
            .1
            .parse_committed_mode(mode, input, n_state);
        match result {
            PeekOk(x) => {
                let (committed, _) = *n_parser_cache.as_ref().unwrap();
                *n_parser_cache = None;
                if committed {
                    CommitOk(x)
                } else {
                    PeekOk(x)
                }
            }
            CommitOk(x) => {
                *n_parser_cache = None;
                CommitOk(x)
            }
            PeekErr(x) => {
                let (committed, _) = *n_parser_cache.as_ref().unwrap();
                *n_parser_cache = None;
                if committed {
                    CommitErr(x.error)
                } else {
                    PeekErr(x)
                }
            }
            CommitErr(x) => CommitErr(x),
        }
    }

    fn add_error(&mut self, errors: &mut Tracked<<Input as StreamOnce>::Error>) {
        self.0.add_error(errors);
    }
}

/// Equivalent to [`p.then(f)`].
///
/// [`p.then(f)`]: ../trait.Parser.html#method.then
pub fn then<Input, P, F, N>(p: P, f: F) -> Then<P, F>
where
    Input: Stream,
    F: FnMut(P::Output) -> N,
    P: Parser<Input>,
    N: Parser<Input>,
{
    Then(p, f)
}

#[derive(Copy, Clone)]
pub struct ThenPartial<P, F>(P, F);
impl<Input, P, N, F> Parser<Input> for ThenPartial<P, F>
where
    Input: Stream,
    F: FnMut(&mut P::Output) -> N,
    P: Parser<Input>,
    N: Parser<Input>,
{
    type Output = N::Output;
    type PartialState = (P::PartialState, Option<(bool, P::Output)>, N::PartialState);

    parse_mode!(Input);
    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        mut mode: M,
        input: &mut Input,
        state: &mut Self::PartialState,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error>
    where
        M: ParseMode,
    {
        let (ref mut p_state, ref mut n_parser_cache, ref mut n_state) = *state;

        if mode.is_first() || n_parser_cache.is_none() {
            debug_assert!(n_parser_cache.is_none());

            match self.0.parse_mode(mode, input, p_state) {
                PeekOk(value) => {
                    *n_parser_cache = Some((false, value));
                }
                CommitOk(value) => {
                    *n_parser_cache = Some((true, value));
                }
                PeekErr(err) => return PeekErr(err),
                CommitErr(err) => return CommitErr(err),
            }
            mode.set_first();
        }

        let result = (self.1)(&mut n_parser_cache.as_mut().unwrap().1)
            .parse_committed_mode(mode, input, n_state);
        match result {
            PeekOk(x) => {
                let (committed, _) = n_parser_cache.take().unwrap();
                if committed {
                    CommitOk(x)
                } else {
                    PeekOk(x)
                }
            }
            CommitOk(x) => {
                *n_parser_cache = None;
                CommitOk(x)
            }
            PeekErr(x) => {
                let (committed, _) = n_parser_cache.take().unwrap();
                if committed {
                    CommitErr(x.error)
                } else {
                    PeekErr(x)
                }
            }
            CommitErr(x) => CommitErr(x),
        }
    }

    fn add_error(&mut self, errors: &mut Tracked<<Input as StreamOnce>::Error>) {
        self.0.add_error(errors);
    }
}

/// Equivalent to [`p.then_partial(f)`].
///
/// [`p.then_partial(f)`]: ../trait.Parser.html#method.then_partial
pub fn then_partial<Input, P, F, N>(p: P, f: F) -> ThenPartial<P, F>
where
    Input: Stream,
    F: FnMut(&mut P::Output) -> N,
    P: Parser<Input>,
    N: Parser<Input>,
{
    ThenPartial(p, f)
}

#[derive(Copy, Clone)]
pub struct ThenRef<P, F>(P, F);
impl<Input, P, N, F> Parser<Input> for ThenRef<P, F>
where
    Input: Stream,
    F: FnMut(&P::Output) -> N,
    P: Parser<Input>,
    N: Parser<Input>,
{
    type Output = (P::Output, N::Output);
    type PartialState = (
        P::PartialState,
        Option<(bool, P::Output, N)>,
        N::PartialState,
    );

    parse_mode!(Input);
    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        mut mode: M,
        input: &mut Input,
        state: &mut Self::PartialState,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error>
    where
        M: ParseMode,
    {
        let (ref mut p_state, ref mut n_parser_cache, ref mut n_state) = *state;

        if mode.is_first() || n_parser_cache.is_none() {
            debug_assert!(n_parser_cache.is_none());

            let (value, committed) = match self.0.parse_mode(mode, input, p_state) {
                PeekOk(value) => (value, false),
                CommitOk(value) => (value, true),

                PeekErr(err) => return PeekErr(err),
                CommitErr(err) => return CommitErr(err),
            };

            let parser = (self.1)(&value);
            *n_parser_cache = Some((committed, value, parser));

            mode.set_first();
        }

        let result = n_parser_cache
            .as_mut()
            .unwrap()
            .2
            .parse_committed_mode(mode, input, n_state);
        match result {
            PeekOk(x) => {
                let (committed, in_value, _) = n_parser_cache.take().unwrap();
                if committed {
                    CommitOk((in_value, x))
                } else {
                    PeekOk((in_value, x))
                }
            }
            CommitOk(x) => {
                let (_, in_value, _) = n_parser_cache.take().unwrap();
                *n_parser_cache = None;
                CommitOk((in_value, x))
            }
            PeekErr(x) => {
                let (committed, _, _) = n_parser_cache.take().unwrap();
                *n_parser_cache = None;
                if committed {
                    CommitErr(x.error)
                } else {
                    PeekErr(x)
                }
            }
            CommitErr(x) => CommitErr(x),
        }
    }

    fn add_error(&mut self, errors: &mut Tracked<<Input as StreamOnce>::Error>) {
        self.0.add_error(errors);
    }
}

/// Equivalent to [`p.then_ref(f)`].
///
/// [`p.then_ref(f)`]: ../trait.Parser.html#method.then
pub fn then_ref<Input, P, F, N>(p: P, f: F) -> ThenRef<P, F>
where
    Input: Stream,
    F: FnMut(&P::Output) -> N,
    P: Parser<Input>,
    N: Parser<Input>,
{
    ThenRef(p, f)
}

#[derive(Copy, Clone)]
pub struct Loop<F, G, S, P>(F, G, S, Option<P>);

impl<Input, F, G, S, P> Parser<Input> for Loop<F, G, S, P>
where
    Input: Stream,
    F: FnMut(&mut S) -> P,
    S: Clone,
    P: Parser<Input>,
    G: FnMut(&mut S, P::Output)
{
    type Output = S;
    type PartialState = (Option<S>, bool, P::PartialState);

    parse_mode!(Input);
    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        mode: M,
        input: &mut Input,
        state: &mut Self::PartialState,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error>
    where
        M: ParseMode,
    {
        let Self(ref mut next_func, ref mut state_gen, ref mut init_state, ref mut parser) = *self;
        let mut lg: LoopGen<&mut F, _, &mut G, P> = LoopGen(next_func, || init_state.clone(), state_gen, parser.take());
        let result = lg.parse_mode_impl(mode, input, state);
        *parser = lg.3;
        result
    }

    fn add_error(&mut self, errors: &mut Tracked<<Input as StreamOnce>::Error>) {
        if let Some(parser) = &mut self.3 {
            parser.add_error(errors);
        }
    }

    fn add_committed_expected_error(&mut self, errors: &mut Tracked<<Input as StreamOnce>::Error>) {
        self.add_error(errors);
    }

    fn parser_count(&self) -> ErrorOffset {
        if let Some(parser) = &self.3 {
            parser.parser_count()
        } else {
            ErrorOffset(1)
        }
    }
}

// Takes a function `func` and initial `state`. Function is applied to current
// state and generates a parser outputting function to update the state. This
// is repeated until the generated parser fails.
//
/// ```
/// # extern crate combine;
/// # use std::collections::HashMap;
/// # use combine::{Parser, Stream, many1, token, value, unexpected_any, optional, choice};
/// # use combine::parser::char::digit;
/// # use combine::parser::sequence::loop_parser;
/// # fn main() {
/// // Parses 'a', 'b' and 'c' such that there is no consecutive letters returning their count
/// #[derive(PartialEq, Eq, Clone, Hash)]
/// enum Token { A, B, C }
/// type State = (HashMap::<Token, usize>, Option<Token>);
/// fn token_parser<Input>((_, last_token): &mut State) -> impl Parser<Input, Output = Token>
/// where
///     Input: Stream<Token = char>
/// {
///     let mut choices = vec![];
///     if *last_token != Some(Token::A) {
///         choices.push(token('a').map(|_| Token::A).left());
///     }
///     if *last_token != Some(Token::B) {
///         choices.push(token('b').map(|_| Token::B).left().right());
///     }
///     if *last_token != Some(Token::C) {
///         choices.push(token('c').map(|_| Token::C).right().right());
///     }
///     choice(choices)
/// }
/// fn update_state((ref mut acc, ref mut last_token): &mut State, current_token: Token) {
///     *acc.entry(current_token.clone()).or_insert(0) += 1;
///     *last_token = Some(current_token);
/// }
/// let result = loop_parser((HashMap::<Token, usize>::new(), None), token_parser, update_state).map(|x| x.0).parse("ababacbcbcaa");
/// assert_eq!(result.as_ref().map(|x| x.0.get(&Token::A)), Ok(Some(&4)));
/// assert_eq!(result.as_ref().map(|x| x.0.get(&Token::B)), Ok(Some(&4)));
/// assert_eq!(result.as_ref().map(|x| x.0.get(&Token::C)), Ok(Some(&3)));
/// assert_eq!(result.as_ref().map(|x| x.1), Ok("a"));
/// # }
/// ```
pub fn loop_parser<Input, F, P, G, S>(init_state: S, next_parser: F, mutator: G) -> Loop<F, G, S, P>
where
    Input: Stream,
    F: FnMut(&mut S) -> P,
    S: Clone,
    P: Parser<Input>,
    G: FnMut(&mut S, P::Output)
{
    Loop(next_parser, mutator, init_state, None)
}

#[derive(Copy, Clone)]
pub struct LoopGen<F, G, H, P>(F, G, H, Option<P>);

impl<Input, F, G, S, P, H> Parser<Input> for LoopGen<F, G, H, P>
where
    Input: Stream,
    F: FnMut(&mut S) -> P,
    G: FnMut() -> S,
    P: Parser<Input>,
    H: FnMut(&mut S, P::Output)
{
    type Output = S;
    type PartialState = (Option<S>, bool, P::PartialState);

    parse_mode!(Input);
    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        mut mode: M,
        input: &mut Input,
        state: &mut Self::PartialState,
    ) -> ParseResult<Self::Output, <Input as StreamOnce>::Error>
    where
        M: ParseMode,
    {
        let Self(ref mut next_func, ref mut state_gen, ref mut mutator, ref mut parser) = *self;
        let (ref mut state, ref mut committed, ref mut partial_state) = *state;
        if mode.is_first() {
            debug_assert!(state.is_none());
            debug_assert!(parser.is_none());
            debug_assert!(!*committed);
            *state = Some(state_gen());
            *parser = Some(next_func(state.as_mut().unwrap()));
        }
        let parser = parser.as_mut().unwrap();
        loop {
            let before = input.checkpoint();
            let result = parser.parse_mode_impl(mode, input, partial_state);
            let value = match result {
                CommitOk(next_value) => {
                    *committed = true;
                    next_value
                },
                PeekOk(next_value) => next_value,
                CommitErr(e) => return CommitErr(e),
                PeekErr(_) => {
                    match input.reset(before) {
                        Ok(_) => if *committed {
                            return CommitOk(state.take().unwrap())
                        } else {
                            return PeekOk(state.take().unwrap())
                        },
                        Err(err) => return CommitErr(err)
                    };
                }
            };
            let state = state.as_mut().unwrap();
            mutator(state, value);
            *parser = next_func(state);
            *partial_state = Default::default();
            mode.set_first();
        }
    }

    fn add_error(&mut self, errors: &mut Tracked<<Input as StreamOnce>::Error>) {
        if let Some(parser) = &mut self.3 {
            parser.add_error(errors);
        }
    }

    fn add_committed_expected_error(&mut self, errors: &mut Tracked<<Input as StreamOnce>::Error>) {
        self.add_error(errors);
    }

    fn parser_count(&self) -> ErrorOffset {
        if let Some(parser) = &self.3 {
            parser.parser_count()
        } else {
            ErrorOffset(1)
        }
    }
}

// Takes a function `func` and initial `state`. Function is applied to current
// state and generates a parser outputting function to update the state. This
// is repeated until the generated parser fails.
//
/// ```
/// # extern crate combine;
/// # use std::collections::HashMap;
/// # use combine::{Parser, Stream, token, choice};
/// # use combine::parser::sequence::loop_gen;
/// # fn main() {
/// // Parses 'a', 'b' and 'c' such that there is no consecutive letters returning their count
/// #[derive(PartialEq, Eq, Clone, Hash)]
/// enum Token { A, B, C }
/// type State = (HashMap::<Token, usize>, Option<Token>);
/// fn token_parser<Input>((_, last_token): &mut State) -> impl Parser<Input, Output = Token>
/// where
///     Input: Stream<Token = char>
/// {
///     let mut choices = vec![];
///     if *last_token != Some(Token::A) {
///         choices.push(token('a').map(|_| Token::A).left());
///     }
///     if *last_token != Some(Token::B) {
///         choices.push(token('b').map(|_| Token::B).left().right());
///     }
///     if *last_token != Some(Token::C) {
///         choices.push(token('c').map(|_| Token::C).right().right());
///     }
///     choice(choices)
/// }
/// fn update_state((ref mut acc, ref mut last_token): &mut State, current_token: Token) {
///     *acc.entry(current_token.clone()).or_insert(0) += 1;
///     *last_token = Some(current_token);
/// }
/// let result = loop_gen(|| (HashMap::<Token, usize>::new(), None), token_parser, update_state).map(|x| x.0).parse("ababacbcbcaa");
/// assert_eq!(result.as_ref().map(|x| x.0.get(&Token::A)), Ok(Some(&4)));
/// assert_eq!(result.as_ref().map(|x| x.0.get(&Token::B)), Ok(Some(&4)));
/// assert_eq!(result.as_ref().map(|x| x.0.get(&Token::C)), Ok(Some(&3)));
/// assert_eq!(result.as_ref().map(|x| x.1), Ok("a"));
/// # }
/// ```
pub fn loop_gen<Input, F, G, S, P, H>(state_gen: G, next_parser: F, mutator: H) -> LoopGen<F, G, H, P>
where
    Input: Stream,
    F: FnMut(&mut S) -> P,
    G: FnMut() -> S,
    P: Parser<Input>,
    H: FnMut(&mut S, P::Output)
{
    LoopGen(next_parser, state_gen, mutator, None)
}


#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use crate::{Parser, Stream, token, choice, eof};
    use crate::parser::{token::any, EasyParser};
    use crate::parser::sequence::loop_gen;
    use crate::stream::easy::{Info, Error};

    #[test]
    fn sequence_single_parser() {
        assert!((any(),).easy_parse("a").is_ok());
    }

    #[test]
    fn loop_gen_error() {
        #[derive(PartialEq, Eq, Clone, Debug, Hash)]
        enum Token { A, B, C }
        type State = (HashMap::<Token, usize>, Option<Token>);
        fn token_parser<Input>((_, last_token): &mut State) -> impl Parser<Input, Output = Token>
        where
            Input: Stream<Token = char>
        {
            let mut choices = vec![];
            if *last_token != Some(Token::A) {
                choices.push(token('a').map(|_| Token::A).left());
            }
            if *last_token != Some(Token::B) {
                choices.push(token('b').map(|_| Token::B).left().right());
            }
            if *last_token != Some(Token::C) {
                choices.push(token('c').map(|_| Token::C).right().right());
            }
            choice(choices)
        }
        fn update_state((ref mut acc, ref mut last_token): &mut State, current_token: Token) {
            *acc.entry(current_token.clone()).or_insert(0) += 1;
            *last_token = Some(current_token);
        }
        let string = "ababacbcbcaa";
        let result = (
            loop_gen(|| (HashMap::<Token, usize>::new(), None), token_parser, update_state),
            eof()
        ).easy_parse(string);
        let result = result.as_ref();
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert_eq!(
            err.errors,
            vec![
                Error::Unexpected(Info::Token('a')),
                Error::Expected(Info::Token('b')),
                Error::Expected(Info::Token('c')),
                Error::Expected(Info::Static("end of input"))
            ]
        );
        assert_eq!(11, err.position.translate_position(string));
    }
}

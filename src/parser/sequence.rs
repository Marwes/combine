//! Combinators which take multiple parsers and applies them one after another.
use lib::marker::PhantomData;

use combinator::{ignore, Ignore};
use error::FastResult::*;
use error::{ConsumedResult, ParseError, StreamError, Tracked};
use parser::ParseMode;
use {ErrorOffset, Parser, Stream, StreamOnce};

macro_rules! dispatch_on {
    ($i: expr, $f: expr;) => {
    };
    ($i: expr, $f: expr; $first: ident $(, $id: ident)*) => { {
        if $f($i, $first) {
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
    ($partial_state: ident; $h: ident $(, $id: ident)*) => {
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
              $($id: Parser<Input=Input>),*
        {
            #[allow(dead_code)]
            fn add_errors(
                input: &mut Input,
                mut err: Tracked<Input::Error>,
                first_empty_parser: usize,
                offset: u8,
                $h: &mut $h $(, $id : &mut $id )*
            ) -> ConsumedResult<($h::Output, $($id::Output),*), Input>
            {
                err.offset = ErrorOffset(offset);
                if first_empty_parser != 0 {
                    if let Ok(t) = input.uncons() {
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
                    }; $h $(, $id)*);
                    ConsumedErr(err.error)
                } else {
                    EmptyErr(err)
                }
            }
        }

        #[allow(non_snake_case)]
        impl <Input: Stream, $h:, $($id:),*> Parser for ($h, $($id),*)
            where Input: Stream,
                  Input::Error: ParseError<Input::Item, Input::Range, Input::Position>,
                  $h: Parser<Input=Input>,
                  $($id: Parser<Input=Input>),*
        {
            type Input = Input;
            type Output = ($h::Output, $($id::Output),*);
            type PartialState = $partial_state<
                SequenceState<$h::Output, $h::PartialState>
                $(, SequenceState<$id::Output, $id::PartialState>)*
            >;

            parse_mode!();
            #[inline]
            fn parse_mode_impl<M>(
                &mut self,
                mut mode: M,
                input: &mut Self::Input,
                state: &mut Self::PartialState,
            ) -> ConsumedResult<Self::Output, Self::Input>
            where
                M: ParseMode,
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
                    if mode.is_first() || state.$id.value.is_none() {
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
                )*

                let value = unsafe { (state.$h.unwrap_value(), $(state.$id.unwrap_value()),*) };
                if first_empty_parser != 0 {
                    ConsumedOk(value)
                } else {
                    EmptyOk(value)
                }
            }

            #[inline(always)]
            fn parser_count(&self) -> ErrorOffset {
                let (ref $h, $(ref $id),*) = *self;
                ErrorOffset($h.parser_count().0 $( + $id.parser_count().0)*)
            }

            #[inline(always)]
            fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
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

    fn parser_count(&self) -> ErrorOffset {
        self.0.parser_count()
    }
}

/// Equivalent to [`p1.with(p2)`].
///
/// [`p1.with(p2)`]: ../parser/trait.Parser.html#method.with
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

    fn parser_count(&self) -> ErrorOffset {
        self.0.parser_count()
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

impl_parser! { Between(L, R, P), Skip<With<L, P>, R> }
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
#[inline(always)]
pub fn between<I, L, R, P>(open: L, close: R, parser: P) -> Between<L, R, P>
where
    I: Stream,
    L: Parser<Input = I>,
    R: Parser<Input = I>,
    P: Parser<Input = I>,
{
    Between(open.with(parser).skip(close))
}

#[derive(Copy, Clone)]
pub struct Then<P, F>(P, F);
impl<P, N, F> Parser for Then<P, F>
where
    F: FnMut(P::Output) -> N,
    P: Parser,
    N: Parser<Input = P::Input>,
{
    type Input = N::Input;
    type Output = N::Output;
    type PartialState = (P::PartialState, Option<(bool, N)>, N::PartialState);

    parse_mode!();
    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        mut mode: M,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input>
    where
        M: ParseMode,
    {
        let (ref mut p_state, ref mut n_parser_cache, ref mut n_state) = *state;

        if mode.is_first() || n_parser_cache.is_none() {
            debug_assert!(n_parser_cache.is_none());

            match self.0.parse_mode(mode, input, p_state) {
                EmptyOk(value) => {
                    *n_parser_cache = Some((false, (self.1)(value)));
                }
                ConsumedOk(value) => {
                    *n_parser_cache = Some((true, (self.1)(value)));
                }
                EmptyErr(err) => return EmptyErr(err),
                ConsumedErr(err) => return ConsumedErr(err),
            }
            mode.set_first();
        }

        let result = n_parser_cache
            .as_mut()
            .unwrap()
            .1
            .parse_consumed_mode(mode, input, n_state);
        match result {
            EmptyOk(x) => {
                let (consumed, _) = *n_parser_cache.as_ref().unwrap();
                *n_parser_cache = None;
                if consumed {
                    ConsumedOk(x)
                } else {
                    EmptyOk(x)
                }
            }
            ConsumedOk(x) => {
                *n_parser_cache = None;
                ConsumedOk(x)
            }
            EmptyErr(x) => {
                let (consumed, _) = *n_parser_cache.as_ref().unwrap();
                *n_parser_cache = None;
                if consumed {
                    ConsumedErr(x.error)
                } else {
                    EmptyErr(x)
                }
            }
            ConsumedErr(x) => ConsumedErr(x),
        }
    }

    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.0.add_error(errors);
    }
}

/// Equivalent to [`p.then(f)`].
///
/// [`p.then(f)`]: ../parser/trait.Parser.html#method.then
#[inline(always)]
pub fn then<P, F, N>(p: P, f: F) -> Then<P, F>
where
    F: FnMut(P::Output) -> N,
    P: Parser,
    N: Parser<Input = P::Input>,
{
    Then(p, f)
}

#[derive(Copy, Clone)]
pub struct ThenPartial<P, F>(P, F);
impl<P, N, F> Parser for ThenPartial<P, F>
where
    F: FnMut(&mut P::Output) -> N,
    P: Parser,
    N: Parser<Input = P::Input>,
{
    type Input = N::Input;
    type Output = N::Output;
    type PartialState = (P::PartialState, Option<(bool, P::Output)>, N::PartialState);

    parse_mode!();
    #[inline]
    fn parse_mode_impl<M>(
        &mut self,
        mut mode: M,
        input: &mut Self::Input,
        state: &mut Self::PartialState,
    ) -> ConsumedResult<Self::Output, Self::Input>
    where
        M: ParseMode,
    {
        let (ref mut p_state, ref mut n_parser_cache, ref mut n_state) = *state;

        if mode.is_first() || n_parser_cache.is_none() {
            debug_assert!(n_parser_cache.is_none());

            match self.0.parse_mode(mode, input, p_state) {
                EmptyOk(value) => {
                    *n_parser_cache = Some((false, value));
                }
                ConsumedOk(value) => {
                    *n_parser_cache = Some((true, value));
                }
                EmptyErr(err) => return EmptyErr(err),
                ConsumedErr(err) => return ConsumedErr(err),
            }
            mode.set_first();
        }

        let result = (self.1)(&mut n_parser_cache.as_mut().unwrap().1)
            .parse_consumed_mode(mode, input, n_state);
        match result {
            EmptyOk(x) => {
                let (consumed, _) = *n_parser_cache.as_ref().unwrap();
                *n_parser_cache = None;
                if consumed {
                    ConsumedOk(x)
                } else {
                    EmptyOk(x)
                }
            }
            ConsumedOk(x) => {
                *n_parser_cache = None;
                ConsumedOk(x)
            }
            EmptyErr(x) => {
                let (consumed, _) = *n_parser_cache.as_ref().unwrap();
                *n_parser_cache = None;
                if consumed {
                    ConsumedErr(x.error)
                } else {
                    EmptyErr(x)
                }
            }
            ConsumedErr(x) => ConsumedErr(x),
        }
    }

    fn add_error(&mut self, errors: &mut Tracked<<Self::Input as StreamOnce>::Error>) {
        self.0.add_error(errors);
    }
}

/// Equivalent to [`p.then_partial(f)`].
///
/// [`p.then_partial(f)`]: ../parser/trait.Parser.html#method.then_partial
#[inline(always)]
pub fn then_partial<P, F, N>(p: P, f: F) -> ThenPartial<P, F>
where
    F: FnMut(&mut P::Output) -> N,
    P: Parser,
    N: Parser<Input = P::Input>,
{
    ThenPartial(p, f)
}

#[cfg(test)]
mod tests {
    use super::*;
    use parser::item::any;

    #[test]
    fn sequence_single_parser() {
        assert!((any(),).easy_parse("a").is_ok());
    }
}

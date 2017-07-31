#[macro_export]
#[doc(hidden)]
macro_rules! seq_parser_impl {
    (; $name: ident $($tt: tt)*) => {
        $name { $($tt)* }
    };
    (_ : $first_parser: expr; $name: ident $($tt: tt)*) => {
        $name { $($tt)* }
    };
    ($first_field: ident : $first_parser: expr; $name: ident $($tt: tt)*) => {
        seq_parser_impl!(; $name $($tt)* $first_field : $first_field,)
    };
    (_ : $first_parser: expr, $($field: ident : $parser: expr),+; $name: ident $($tt: tt)*) => {
        seq_parser_impl!( $($field : $parser),+; $name $($tt)* )
    };
    ($first_field: ident : $first_parser: expr, $($field: ident : $parser: expr),+; $name: ident $($tt: tt)*) => {
        seq_parser_impl!( $($field : $parser),+; $name $($tt)* $first_field: $first_field, )
    };
}

#[macro_export]
macro_rules! seq_parser { 
    ($name: ident { $($field: ident : $parser: expr),* }) => {
        ( $($parser),* )
            .map(|( $($field),* )|
                seq_parser_impl!($($field : $parser),*; $name )
            )
    }
}
struct Test {
    a: i32,
    b: i32,
}
fn main() {
    seq_parser!(Test { a: 1, b: 2 });
}
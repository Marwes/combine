#[macro_use]
extern crate combine;

parser!{
    pub fn test[I]()(I) -> ()
        where [I: ::combine::Stream<Item = char>]
    {
        use combine::combinator::value;
        let _ = ();
        fn _test() { }
        match Some(1) {
            Some(_) => (),
            None => (),
        }
        value(())
    }
}

parser!{
    pub fn test_that_parsers_with_unnamed_types_can_be_in_same_scope[I]()(I) -> ()
        where [I: ::combine::Stream<Item = char>]
    {
        use combine::combinator::value;
        value(())
    }
}

#[test]
fn test_that_we_dont_need_imports_for_this_macro_to_work() {
    test::<&str>();
    test_that_parsers_with_unnamed_types_can_be_in_same_scope::<&str>();
}

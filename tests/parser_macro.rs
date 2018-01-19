#[macro_use]
extern crate combine;

parser!{
    fn test[I]()(I) -> ()
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

#[test]
fn test_that_we_dont_need_imports_for_this_macro_to_work() {
    test::<&str>();
}

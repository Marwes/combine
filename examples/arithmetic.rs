#[macro_use]
extern crate combine;

use combine::{
    between, chainl1, choice,
    error::ParseError,
    many1,
    parser::char::{char, digit, spaces},
    Parser, Stream,
};

#[derive(Debug)]
pub enum Expr {
    Scalar(f64),
    Prod(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Sum(Box<Expr>, Box<Expr>),
    Diff(Box<Expr>, Box<Expr>),
}

fn parse_expr<Input>() -> impl Parser<Input, Output = Expr>
where
    Input: Stream<Token = char>,
    Input::Error: ParseError<Input::Token, Input::Range, Input::Position>,
{
    let tok = choice([char('-'), char('+')]).map(|op| {
        move |a, b| {
            if op == '+' {
                Expr::Sum(Box::new(a), Box::new(b))
            } else if op == '-' {
                Expr::Diff(Box::new(a), Box::new(b))
            } else {
                unimplemented!()
            }
        }
    });
    let sum_or_sub = chainl1(parse_term(), tok);
    sum_or_sub
}

fn parse_term<Input>() -> impl Parser<Input, Output = Expr>
where
    Input: Stream<Token = char>,
    Input::Error: ParseError<Input::Token, Input::Range, Input::Position>,
{
    let tok = choice([char('*'), char('/')]).map(|op| {
        move |a, b| {
            if op == '*' {
                Expr::Prod(Box::new(a), Box::new(b))
            } else if op == '/' {
                Expr::Div(Box::new(a), Box::new(b))
            } else {
                unimplemented!()
            }
        }
    });
    let prod_or_div = chainl1(parse_factor_(), tok);
    prod_or_div
}

parser! {
    pub fn parse_factor_[Input]()(Input) -> Expr
    where [Input: Stream<Token=char>, Input::Error: ParseError<Input::Token, Input::Range, Input::Position>]
    {
        let scalar = many1(digit()).map(|t: String| Expr::Scalar(t.parse().unwrap()));
        let parens = between(char('('), char(')'), parse_expr());
        let p = spaces().with(scalar.or(parens));
        p
    }
}

fn print_calc_result(ast: Box<Expr>) -> f64 {
    match *ast {
        Expr::Scalar(val) => val,
        Expr::Sum(left, right) => print_calc_result(left) + print_calc_result(right),
        Expr::Diff(left, right) => print_calc_result(left) - print_calc_result(right),
        Expr::Prod(left, right) => print_calc_result(left) * print_calc_result(right),
        Expr::Div(left, right) => print_calc_result(left) / print_calc_result(right),
    }
}

#[test]
fn test() {
    // without parens
    let parsed = parse_expr().parse("3*1+2");
    let ast = parsed.expect("fail to parse").0;
    let calculated = print_calc_result(ast.into());
    assert_eq!(calculated, 5.0);

    // with paren
    let parsed = parse_expr().parse("3*(1+2)");
    let ast = parsed.expect("fail to parse").0;
    let calculated = print_calc_result(ast.into());
    assert_eq!(calculated, 9.0);

    // div and diff
    let parsed = parse_expr().parse("6/(2-4)");
    let ast = parsed.expect("fail to parse").0;
    let calculated = print_calc_result(ast.into());
    assert_eq!(calculated, -3.0);
}

fn main() {
    let res = parse_expr().parse("3*(1+2)");
    let ast = res.expect("fail to parse").0;
    println!("{:?}", print_calc_result(ast.into()));
}

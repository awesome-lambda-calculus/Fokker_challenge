use lambda_calculus::term::*;
use lambda_calculus::*;
use lambda_calculus::{abs, app, beta, combinators::K, data::num::convert::IntoChurchNum};
use rust_scripts::parse_term_in_any_format;
use std::env::args;

fn main() {
    let t = args().nth(1).unwrap();

    let s = parse_term_in_any_format(&t).unwrap();
    println!("{:?}", s);
}

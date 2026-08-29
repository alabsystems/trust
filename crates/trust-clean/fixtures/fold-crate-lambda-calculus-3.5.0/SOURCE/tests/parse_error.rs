extern crate lambda_calculus as lambda;

use std::error::Error;

use lambda::parser::parse;
use lambda::term::Notation::Classic;

#[test]
fn parse_error_question_mark_operator() {
    match using_question_mark_operator() {
        Result::Ok(_) => panic!("Should not be Ok"),
        Result::Err(e) => assert_eq!(e.to_string(), "syntax error; the expression is empty"),
    }
}

fn using_question_mark_operator() -> Result<(), Box<dyn Error>> {
    parse("λλλ", Classic)?;
    Ok(())
}

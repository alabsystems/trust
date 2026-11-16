//@ only-apple
//@ edition: 2021
//@ proc-macro: thiserror_shaped.rs
//@ revisions: in_process isolated
//@ compile-flags: -Zunpretty=expanded
//@[isolated] compile-flags: -Ztrust-proc-macro-isolation
//@ check-pass
//! Trust (D21): a thiserror-shaped derive (a format string per variant, positional
//! and captured fields, a `#[from]` conversion, mixed-site hygiene) expands to the
//! same program in rustc (`in_process`) and in the sandboxed worker (`isolated`).
//! `expansions_are_identical.rs` requires the two expected files to be
//! byte-identical.

#[macro_use]
extern crate thiserror_shaped;

#[derive(Debug, Failure)]
pub enum LoadFailure {
    #[error("the file is empty")]
    Empty,
    #[error("line {line}: {reason}")]
    Parse { line: usize, reason: String },
    #[error("expected {0} fields, found {1}")]
    Arity(usize, usize),
    #[error("i/o: {0}")]
    Io(#[from] std::io::Error),
}

fn main() {}

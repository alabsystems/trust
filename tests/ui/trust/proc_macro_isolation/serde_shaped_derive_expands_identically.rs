//@ only-apple
//@ edition: 2021
//@ proc-macro: serde_shaped.rs
//@ revisions: in_process isolated
//@ compile-flags: -Zunpretty=expanded
//@[isolated] compile-flags: -Ztrust-proc-macro-isolation
//@ check-pass
//! Trust (D21): a serde-shaped derive (helper attributes, generics, an impl built
//! from token trees and from parsed text) expands to the same program whether its
//! dylib is loaded into rustc (`in_process`) or only into the sandboxed worker
//! (`isolated`). Each revision's expansion is its own expected file, and
//! `expansions_are_identical.rs` requires the two files to be byte-identical.

#[macro_use]
extern crate serde_shaped;

pub trait Shape {
    const NAME: &'static str;
    const SKIPPED: usize;
    fn fields(&self) -> Vec<(&'static str, String)>;
}

#[derive(Shape)]
pub struct Point<T> {
    #[shape(rename = "ex")]
    pub x: T,
    y: u32,
    #[shape(skip)]
    cache: Vec<Option<T>>,
    r#type: &'static str,
}

#[derive(Shape)]
struct Empty {}

fn main() {}

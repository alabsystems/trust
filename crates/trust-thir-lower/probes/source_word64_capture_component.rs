//! Same-SDK compilation harness for the identical production source module.
//! No metadata decoder, IR, alternative source constructor or proof authority.
#![feature(rustc_private)]
extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;
#[path = "../src/source_word64.rs"]
pub mod source_word64;

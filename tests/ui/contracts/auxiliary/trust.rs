//! Trust: minimal stand-in for the `trust-spec` passthrough proc-macro crate
//! (its lib crate name is `trust`). Under tRustc, the resolver's spec-contract
//! hook (`trust_spec_contract_attr_extension`) replaces these crate-root
//! `trust::{requires,ensures}` attribute proc macros with the compiler-owned
//! Trust contract builtins before expansion, so the passthrough bodies below
//! never run for those two attributes.

// Auxiliary proc-macro crates are built at the default (2015) edition, where
// `proc_macro` is not in the extern prelude for `use` paths: declare it.
extern crate proc_macro;

use proc_macro::TokenStream;

#[proc_macro_attribute]
pub fn requires(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}

#[proc_macro_attribute]
pub fn ensures(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}

#[proc_macro_attribute]
pub fn invariant(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}

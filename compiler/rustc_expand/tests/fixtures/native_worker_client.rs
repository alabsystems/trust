//! Real proc-macro DSO for the explicit native Client-table integration test.
//! Built by the matching compiler; not linked into the test parent.
#![feature(proc_macro_internals, proc_macro_span, proc_macro_diagnostic, proc_macro_expand, proc_macro_tracked_env, proc_macro_tracked_path)]
extern crate proc_macro;
use proc_macro as pm;

#[path = "../../src/proc_macro_server/isolation/dispatch/tests/native_client_methods.rs"]
mod native_client_methods;

use proc_macro::TokenStream;

#[proc_macro]
pub fn first_declaration(_: TokenStream) -> TokenStream {
    "selected_first_declaration".parse().unwrap()
}

#[proc_macro]
pub fn second_declaration(input: TokenStream) -> TokenStream {
    native_client_methods::all_methods(input)
}

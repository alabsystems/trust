#![crate_type = "proc-macro"]

extern crate proc_macro;

use proc_macro::TokenStream;

#[proc_macro]
pub fn noop(_input: TokenStream) -> TokenStream {
    TokenStream::new()
}

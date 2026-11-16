//! A proc macro nobody audited: loading it into a bounded verifying session must
//! be refused before its dylib is opened (PM-1).
extern crate proc_macro;
use proc_macro::TokenStream;

#[proc_macro_derive(Pm1Sentinel)]
pub fn pm1_sentinel(_input: TokenStream) -> TokenStream {
    TokenStream::new()
}

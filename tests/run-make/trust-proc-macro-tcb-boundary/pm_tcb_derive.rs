//! A derive that records, when it EXPANDS, that it ran: it writes the file the
//! loading compilation names in `PM_TCB_SENTINEL`. It emits no tokens, so an
//! admitted expansion adds nothing the verifier has to prove.
extern crate proc_macro;
use proc_macro::TokenStream;

#[proc_macro_derive(Sentinel)]
pub fn derive_sentinel(_input: TokenStream) -> TokenStream {
    if let Some(path) = std::env::var_os("PM_TCB_SENTINEL") {
        let _ = std::fs::write(path, b"derive expanded\n");
    }
    TokenStream::new()
}

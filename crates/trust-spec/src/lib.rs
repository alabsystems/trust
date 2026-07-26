//! Compatibility contract attributes for non-tRustc builds.
//!
//! tRustc owns `#[requires]`, `#[ensures]`, and `#[invariant]` as first-class
//! compiler syntax. These proc macros are only a stable-Rust compatibility shim
//! for crates that need to parse before the tRustc contract query is available.
//! They must not be treated as the canonical Trust contract representation.

#![forbid(unsafe_code)]

use proc_macro::TokenStream;

fn passthrough(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}

/// Compatibility precondition marker.
///
/// The real Trust contract is captured by tRustc before macro-expanded
/// passthrough code reaches verification.
#[proc_macro_attribute]
pub fn requires(attr: TokenStream, item: TokenStream) -> TokenStream {
    passthrough(attr, item)
}

/// Compatibility postcondition marker.
///
/// The real Trust contract is captured by tRustc before macro-expanded
/// passthrough code reaches verification.
#[proc_macro_attribute]
pub fn ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
    passthrough(attr, item)
}

/// Compatibility invariant marker.
///
/// The real Trust contract is captured by tRustc before macro-expanded
/// passthrough code reaches verification.
#[proc_macro_attribute]
pub fn invariant(attr: TokenStream, item: TokenStream) -> TokenStream {
    passthrough(attr, item)
}

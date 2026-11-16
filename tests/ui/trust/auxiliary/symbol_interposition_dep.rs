//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! A verify-off dependency that IMPORTS a symbol it does not define, for
//! `symbol_interposition_refused.rs` (revision `dep_import`): its code calls
//! whatever the linked program supplies under `trust_interposition_dep_hook`.

extern "C" {
    fn trust_interposition_dep_hook(x: u32) -> u32;
}

/// Calls the imported hook. The dependency's own contract for the hook (here,
/// a total function) is nothing the verifying crate's build checks.
pub fn call_hook(x: u32) -> u32 {
    unsafe { trust_interposition_dep_hook(x) }
}

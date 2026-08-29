//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-fail
//! Bare helper names in native contract text may expand only from rustc's exact
//! owner-module binding. These are the three tempting string-only collisions:
//! an item outside the scope, an imported alias, and a function-pointer
//! parameter shadowing a same-module item. Every one must remain an obligation
//! failure rather than selecting a function by displayed name.

mod hidden {
    pub(super) fn hidden_id(v: u64) -> u64 {
        v
    }
}

pub fn inaccessible_name(x: u64) -> u64 ensures result == hidden_id(x) { //~ ERROR safety verification incomplete
    //~| ERROR strict verification failed
    x
}
mod imported {
    pub fn source_id(v: u64) -> u64 {
        v
    }
}

use imported::source_id as visible_alias;

pub fn imported_alias(x: u64) -> u64 ensures result == visible_alias(x) { //~ ERROR safety verification incomplete
    //~| ERROR strict verification failed
    x
}

fn shadow_id(v: u64) -> u64 {
    v
}

pub fn signature_shadow(shadow_id: fn(u64) -> u64, x: u64) -> u64 //~ ERROR safety verification incomplete
    //~| ERROR strict verification failed
    ensures result == shadow_id(x)
{
    // The caller may pass any function. Expanding the module `shadow_id` here
    // would falsely turn the postcondition into `result == x`.
    x
}

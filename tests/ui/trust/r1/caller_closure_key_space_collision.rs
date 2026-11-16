//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-name=t --crate-type=lib
//@ rustc-env: TRUST_R1_TRACE=1
//@ normalize-stderr: "formula=.* freevars=\{[^}]*\}" -> "formula=$$FORMULA freevars=$$FREEVARS"
//@ normalize-stderr: "sealed [0-9a-f]{64}" -> "sealed $$DIGEST"
//@ check-pass

// R1-MONO-SUPPRESSION-1: sealed row harvesting remains enabled, but its
// root-only evidence cannot suppress a failed/discarded native bundle.
// The former generic-coverage registry and transitive caller census are gone.
// The raw diagnostic name of one helper collides with another helper's
// crate-prefixed sealed-row key only in the collision variant. Both genuine
// per-row sealed flips must still apply to their own source functions.
#![allow(dead_code)]
mod t {
    pub(crate) fn helper(x: u32, d: u32) -> u32 {
        x / d
    }
    pub(crate) fn call() -> u32 {
        helper(10, 5)
    }
}
fn helper(x: u32, d: u32) -> u32 {
    x / d
}
fn call2() -> u32 {
    helper(20, 4)
}
fn go() {
    let _ = t::call();
    let _ = call2();
}

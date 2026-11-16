// trust-soundness-corpus entry `tvc-untyped-literal-call-arg` (trust-vc untyped literal (930d025f)). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
#![allow(unused_variables, dead_code)]
fn g8(x: u8) {}

pub fn never_binding_typed_by_call_arg_used_in_assert() {
    let a = 200;
    let r = &a;
    let b = *r + 100 > 0;
    g8(a);
}

// Twin: the same shape where the literal really is an i32.
pub fn verified_borrow_i32() {
    let a = 200;
    let r = &a;
    let b = *r + 100 > 0;
}

#![crate_type = "lib"]
// MUTANT of proved/match_ref_payload.rs: the `Some` arm computes `x + 1`, which
// overflows when the referent is `i32::MAX`. The verifier MUST refuse this
// (exit 1) — the `[overflow:add]` obligation fails with a verified
// counterexample. Guards the `ValidBorrow` reference-load lane: modeling the
// dereferenced value as a fresh-symbolic value must NOT mask an arithmetic bug
// that depends on it.
pub fn match_ref_payload(o: Option<&i32>) -> i32 {
    match o {
        Some(&x) => x + 1,
        None => 0,
    }
}

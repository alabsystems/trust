#![crate_type = "lib"]
// MUTANT of proved/match_call_result.rs: the `Some` arm computes `x + 1`, which
// overflows when the first element is `i32::MAX`. The verifier MUST refuse this
// (exit 1) — `[overflow:add]` fails with a verified counterexample. Guards the
// cross-block threading lane: threading the call-result Option across blocks must
// not mask an arithmetic bug in the matched value.
pub fn match_call_result(s: &[i32]) -> i32 {
    match s.first() {
        Some(&x) => x + 1,
        None => 0,
    }
}

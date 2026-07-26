#![crate_type = "lib"]
// GUARDED TWIN of `mutant/bitmask_index.rs`: the SAME `s[i & 31]` over `[i32; 16]`
// (mask 31 > len 16), but the access is dominated by `if i < 16`. Inside that
// guard `i & 31 == i < 16`, so the index is in bounds — this is valid, panic-free
// Rust and MUST verify (exit 0), never be refuted.
//
// This is the regression guard for the `-full` free-index bitmask refutation
// (`bitmask_free_index_oob_refutation` in `trust_verify.rs`). That recognizer's
// candidate counterexample seed is `i = 31` (the mask). Here the guard conjunct
// `Lt(i, 16)` is FALSE under `i = 31`, so the witness is not a model of the VC
// and the recognizer ABANDONS — the obligation stays runtime_checked (exit 0).
// If the recognizer ever false-refuted a guarded access this fixture would flip
// the gate RED.
pub fn bitmask_index_guarded(s: &[i32; 16], i: usize) -> i32 {
    if i < 16 { s[i & 31] } else { 0 }
}

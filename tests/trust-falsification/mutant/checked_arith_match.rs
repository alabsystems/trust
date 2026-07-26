#![crate_type = "lib"]
// MUTANT of proved/checked_arith_match.rs: the `Some` arm computes `v + 1`, which
// overflows when `a + b == u32::MAX` (so `checked_add` returns `Some(u32::MAX)`).
// The verifier MUST refuse this (exit 1) — `[overflow:add]` fails with a verified
// counterexample. Guards the total-checked-arith lane: modeling `checked_add`'s
// result as a fresh-symbolic value must NOT mask an overflow in code that uses it.
pub fn checked_arith_match(a: u32, b: u32) -> u32 {
    match a.checked_add(b) {
        Some(v) => v + 1,
        None => 0,
    }
}

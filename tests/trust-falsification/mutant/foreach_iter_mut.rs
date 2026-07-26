#![crate_type = "lib"]
// MUTANT of proved/foreach_iter_mut.rs: the body uses non-wrapping `*x = *x + 1`,
// which overflows when an element is `i32::MAX`. The verifier MUST refuse this
// (exit 1) — `[overflow:add]` fails with a verified counterexample. Guards the
// `iter_mut` / store-through-`&mut` lane: leaving the store unmodeled (sound,
// since the location is untracked) must NOT mask an overflow in the value being
// stored.
pub fn foreach_iter_mut(s: &mut [i32]) {
    for x in s.iter_mut() {
        *x = *x + 1;
    }
}

#![crate_type = "lib"]
// MUTANT of proved/scrollback_trim_excess.rs: the `len >= keep` guard is
// dropped, so the subtraction underflows whenever keep > len. The verifier
// MUST refuse this (exit 1) — a surviving mutant means the "proof" of the
// guarded version was vacuous.
pub fn scrollback_trim_excess(len: u32, keep: u32) -> u32 {
    len - keep
}

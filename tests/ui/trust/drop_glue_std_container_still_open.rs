//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! KNOWN-OPEN: a std container's drop glue is still refused, and this file pins
//! WHY so the gap is visible rather than folklore.
//!
//! `Holder` has no `Drop`, so the structural closure records it and explores its
//! fields; `Vec<u8>` DOES have one, so the destructor check runs on
//! `<Vec<u8> as Drop>::drop` — and that body does not itself verify panic-free
//! today, so the node stays cut and the row is kept. That is the CORRECT
//! fail-closed answer, not a defect in the rule: `drop_glue_proved_destructor_credits.rs`
//! shows the same code path crediting a destructor that does prove.
//!
//! Measured (trustc 12:30:39): `0 proved, 0 failed, 0 unknown, 1 runtime-checked`
//! — that single runtime-checked row IS the drop-glue assumption and is this
//! file's ONLY blocker. The `[trust-drop-glue-assumption]` text itself is printed
//! only under `TRUST_ASSERT_DEBUG=1` (2 rows there); plain output shows the row
//! as runtime-checked. When std's `Vec::drop` verifies, this file should flip to
//! clean; until then it is the honest marker of the remaining gap.
pub struct Holder {
    v: Vec<u8>,
}
pub fn len(h: Holder) -> usize {
    h.v.len()
    //~^^ ERROR Trust strict verification failed
}

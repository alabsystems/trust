//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! FLIPPED TO CLEAN 2026-09-13 — this file used to be the KNOWN-OPEN marker for
//! a std container's drop glue, and its own header said: "When std's `Vec::drop`
//! verifies, this file should flip to clean." It flipped, and this header
//! records how, so the flip is evidence rather than folklore.
//!
//! `Holder` has no `Drop`, so the structural closure records it and explores its
//! fields; `Vec<u8>` DOES have one, so the destructor check runs on
//! `<Vec<u8> as Drop>::drop`. Until 2026-09-13 that body could not even be
//! LOWERED: the native bundle for this function was rejected by trust-ir's own
//! validator (bundled std bodies carried dangling struct ids — `map_type_ctx`
//! discarded the id `add_struct_def`'s structural dedup returned — and erased
//! continuations behind a substring `is_panic_call` match), and the compiler
//! honestly refused the function ("native typed-TrustIr lowering did not
//! complete"). Both producer defects were fixed at the root in
//! `crates/trust-ir-bridge/src/lower.rs`; with a valid bundle the drop glue
//! lowers and the panic-freedom obligation PROVES (solver
//! `trust-assert-refute`: no assertion, `unreachable!`, or panic is reachable).
//!
//! Measured on that compiler (`-Ztrust-verify-output=json`):
//! `1 proved, 0 failed, 0 unknown, 0 runtime-checked, 1 skipped out of 2` —
//! the skipped row is the DISCLOSED `contract:global-alloc-dealloc-panic-free`
//! assumption ("allocation-owning drop(s) rely on `GlobalAlloc::dealloc` never
//! panicking; DISCHARGED vacuously — no `#[global_allocator]` in the crate graph,
//! conditional on the final link registering no other allocator"), which the
//! sealed pre-fix toolchain reported IDENTICALLY beside its refusal. So the flip
//! adds one proved row and removes one refusal; it does not hide anything the
//! refusal used to disclose. `drop_glue_proved_destructor_credits.rs` is the
//! sibling that credited a destructor that already proved.
pub struct Holder {
    v: Vec<u8>,
}
pub fn len(h: Holder) -> usize {
    h.v.len()
}

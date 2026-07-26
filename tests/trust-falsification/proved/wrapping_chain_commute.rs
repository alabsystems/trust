#![crate_type = "lib"]
// HUNT-FRONTIER (2026-06-25): wrapping-arithmetic invariants that CHAIN wrapping ops.
// `wrapping_call_assert_model` grounds each `wrapping_{add,sub}` as a faithful single-
// /two-sided-Ite modular reduction; chained ops (operand is itself a wrap result) are
// grounded inner-before-outer via the resolution fixpoint. The 4-op both-sides chain
// `advance_commutes` (order-independence of two wrapping advances) produces a DEEP
// nested-ite QF_LIA obligation that the thin deferred-trust re-translate left Unknown;
// the deferred-trust whole-problem re-solve now runs the COMPLETE Executor over a clone
// of the full solving context, which decides it. All four PROVE; their twins (a wrong
// equality) refute (see the falsification mutants).

// 2-level chain: advance then retreat by the same amount returns to start (ring buffer).
pub fn ring_roundtrip(head: u32, n: u32) {
    assert!(head.wrapping_add(n).wrapping_sub(n) == head);
}

// 4-op both-sides chain: two wrapping advances are order-independent.
pub fn advance_commutes(pos: u32, a: u32, b: u32) {
    assert!(pos.wrapping_add(a).wrapping_add(b) == pos.wrapping_add(b).wrapping_add(a));
}

// width 64 (usize): the same roundtrip over pointer-width wrapping.
pub fn usize_roundtrip(head: usize, n: usize) {
    assert!(head.wrapping_add(n).wrapping_sub(n) == head);
}

// signed two's-complement commutativity.
pub fn i32_commute(a: i32, b: i32) {
    assert!(a.wrapping_add(b) == b.wrapping_add(a));
}

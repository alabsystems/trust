#![crate_type = "lib"]
// `contract_panic` is a TOOL attribute (unlike the builtin-mapped
// `trust::requires`/`ensures`), so the `trust` tool namespace must be
// registered — same convention as clean-kernel's
// `#![cfg_attr(trust_verify, register_tool(trust))]`.
#![feature(register_tool)]
#![register_tool(trust)]
// T9 (contract-panic annotation surface, aterm-alloc ArrayVec::push shape): a
// DECLARED fail-closed panic — `#[trust::contract_panic(message_contains =
// "capacity is")]` on a function whose only panic is the annotated capacity
// guard, with a STATIC message. In edition 2021 `panic!("static str")`
// post-inline lowers to `panic_fmt(fmt::Arguments::from_str("static str"))`,
// so the matcher harvests the constant both as a direct `&str` operand
// (`core::panicking::panic(&str)`) and through the one-level
// `Arguments::from_str`/`new_const` chase (`panic_call_const_str_messages`);
// only a compile-time-constant message can ever message-match — runtime-
// formatted messages stay unmatched, fail-closed. MUST PROVE (exit 0) under
// the default strict policy: the clamp makes the guarded panic provably
// unreachable (the documented `if c { .. } else { 7 }` refute-lane UNSAT
// shape), and T9 pins two anti-false-positive edges on top:
//   * the UNUSED-annotation check is SYNTACTIC (a panic call whose const-str
//     message contains the payload counts as used) — a provably-guarded panic
//     must NOT mint the always-FAILED `contract-panic-unused` row;
//   * a PROVED annotated obligation stays Proved — the marker reclassifies
//     only a FAILED row, so the annotation must not perturb the strict lane
//     (byte-identical rows; the row rewrite is default-lane only).
// The REACHABLE-panic half of the T9 contract — a message-matched refutation
// lands as a visible `contract-panic:matched` row only under lame/survey and
// gates as at best Targo's advisory CONDITIONAL pass (1 contract-panic), never
// a bare pass, while strict and memory-safe keep folding it to failure — is
// pinned by the targo-trust unit tests (`gate_advisory_lane_contract_panics_conditional_
// pass`, `partition_counts_contract_panic_rows_into_their_own_bucket`); this
// strict-lane runner cannot exercise a ConditionalPass. The abuse edges
// are pinned by mutant/contract_panic_unused.rs (annotation on panic-free
// code = FAILED) and mutant/contract_panic_cannot_mask.rs (the annotation
// cannot absorb a second, unrelated panic).

/// Clamp-then-guard: `k` is provably `< 8` on every path, so the annotated
/// capacity panic is unreachable — the verifier PROVES it rather than
/// tolerating it, and the annotation is still "used" (the panic call with the
/// matching message exists in the body).
#[trust::contract_panic(message_contains = "capacity is")]
pub fn slot_index(i: usize) -> usize {
    let k = if i < 8 { i } else { 7 };
    if k >= 8 {
        panic!("ArrayVec overflow: capacity is 8");
    }
    k
}

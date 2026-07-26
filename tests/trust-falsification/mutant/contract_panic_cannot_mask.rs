#![crate_type = "lib"]
// `contract_panic` is a TOOL attribute: register the `trust` tool namespace so
// the fixture refutes on the REAL second-panic row, not vacuously via E0433
// (see proved/contract_panic_annotated.rs).
#![feature(register_tool)]
#![register_tool(trust)]
// T9 (contract-panic annotation surface) — CANNOT-MASK mutant: the function
// carries a correctly annotated, message-MATCHED capacity panic AND a second,
// UNRELATED reachable panic ("other bug", which the `message_contains =
// "capacity is"` payload does not match). The annotation surface must be
// per-obligation, never per-function: only the message-matched panic's FAILED
// row is reclassified to `contract-panic:matched` only in lame/survey; the
// second refutation keeps its plain FAILED row, so the build stays RED in every
// gate lane —
//   * the default strict policy (this runner): both raw refutations abort;
//     MUST FAIL (exit 1);
//   * Targo advisory: the unmatched `failed` row rules (Fail beats
//     ConditionalPass — pinned by the advisory gate's cannot-mask case).
// If this mutant ever survives, the annotation has become a function-wide
// panic amnesty — the exact abuse T9's site+message match exists to prevent.

/// The first panic is the declared capacity contract (input-reachable: any
/// `len >= 8`); the second is a plain bug the annotation must not absorb.
#[trust::contract_panic(message_contains = "capacity is")]
pub fn push_slot(len: usize, x: usize) -> usize {
    if len >= 8 {
        panic!("ArrayVec overflow: capacity is 8");
    }
    if x == 3 {
        panic!("other bug");
    }
    len
}

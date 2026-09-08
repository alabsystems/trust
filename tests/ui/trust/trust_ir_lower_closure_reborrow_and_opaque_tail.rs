//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-CB2 + wave-CVR): two closure asymmetries, pinned together because
//! both are "a guard standing in for a position test" and both regress the same way.
//!
//! wave-CB2 — `try_lower_zst_closure_arg`'s peel walked only `Scope`/`Use`, so THIR's
//! reborrow layer for a REFERENCE-TYPED CALL ARGUMENT hid the literal from it.
//! `take_gen(&|| 22)` is `Borrow{Shared, Deref{Borrow{Shared, Closure}}}`, so the
//! `Borrow` arm handed the helper a `Deref` node and it declined — while the
//! byte-identical `let _r = &|| 22;`, which has no reborrow layer, lowered clean.
//! `&*&c == &c`, so exactly one `Deref{Borrow{..}}` pair is peeled and nothing else:
//! `neg_deref_place` is a bare `Deref` over something that is NOT a borrow and must
//! keep failing closed.
//!
//! wave-CVR — wave-CV's opaque conjunct was BODY-WIDE
//! (`!fn_return_rty.has_opaque_types()`), so it refused a capture-free closure in
//! positions that provably cannot reach the `Return` (`cvr_non_tail`, an ADT field)
//! where the identical closure under a CONCRETE return lowered clean.
//!
//! THE TAIL CASE IS RE-SORTED, NOT MERELY ADMITTED, and that half is a type
//! correctness fix. At the direct tail of a body whose declared return maps to the
//! opaque-alias sort, the value's only consumer is the implicit `Return`, whose
//! declared type IS that sort — so it is minted there. Minting `Ty::Unit` instead
//! would emit `ReturnTypeMismatch { expected: "struct.N", actual: "()" }`, the #189
//! family named at `guard_sig_position_ty`.
//!
//! WHAT THIS FIXTURE CAN AND CANNOT OBSERVE, stated so nobody reads more into a
//! green than it carries. Measured on this file: every `cvr_*` body is
//! `spliced = false`, because an unrevealed-opaque return sets `param_opaque`, which
//! marks the body `symbolic`, which `splice_ok` refuses. Only the assembled CRATE
//! module is validated, so none of these reach `validate_module` today and a wrong
//! sort here would NOT show up as `modules_invalid`. The re-sort is therefore
//! belt-and-braces against that containment lapsing — which is not hypothetical:
//! wave-RD is exactly the case where it did, and `modules_invalid` went 0 -> 1.
//! What this file pins is the COVERAGE half (each body lowers clean, each negative
//! control still declines); the validity half is pinned by the producer sweep's
//! `modules_invalid` ratchet across the corpus.
//!
//! `If`/`Match`/`Loop` tails are deliberately NOT peeled: their arm values merge
//! through a join whose declared type comes from `map_ty`, so re-sorting one arm
//! would move the mismatch into the join instead of removing it. `cvr_match_tail`
//! is that shape. It lowers clean either way — the peel simply does not claim it —
//! so this is a pin on the PEEL's scope, readable by diffing the emitted `Const`
//! sort (`-Ztrust-dump=ir:<dir>`, which needs an explicit `--crate-name`), not by
//! the pass/fail of this test.

pub fn take_gen<F: Fn() -> i32>(_f: &F) -> i32 {
    0
}

// wave-CB2: the reborrow layer, and its already-clean control.
pub fn cb2_arg() -> i32 {
    take_gen(&|| 22)
}
pub fn cb2_let() {
    let _r = &|| 22;
}

// wave-CB2 negative control: a bare `Deref` over a place, not over a borrow.
pub fn neg_deref_place(p: &&dyn Fn() -> i32) -> i32 {
    (**p)()
}

// wave-CVR: capture-free closure at the DIRECT TAIL of an opaque-returning fn.
pub fn cvr_tail() -> impl Fn() -> i32 {
    || 22
}

// wave-CVR: the same closure in a position that cannot reach the `Return`.
pub struct Holder<F> {
    pub f: F,
    pub n: u32,
}
pub fn cvr_non_tail() -> impl Sized {
    Holder { f: || 22, n: 3 }
}

// Control: identical closure under a CONCRETE return, clean before the wave too.
pub fn cvr_concrete() -> u32 {
    let _f = || 22;
    7
}

// Not a direct tail — a `Match` join whose arm value is the closure. Pinned so the
// peel is never widened to a join. (An `If` with two DISTINCT closure literals is not
// expressible in Rust at all — each closure has its own type and they cannot unify
// under one `impl Fn` — so a single-arm match is the only way to write this shape.)
pub fn cvr_match_tail(b: bool) -> impl Fn() -> i32 {
    match b {
        _ => || 22,
    }
}

pub fn main() {}

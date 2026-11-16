//@ probe-shape: Projection
//@ probe-expect: discharged
//@ probe-note: `usize` CLAUSE BINDERS. Until 2026-09-17 this row read
//@ probe-note: `clause-outside-fragment`: usize was admissible on the body side (the
//@ probe-note: verifier's extraction lane spells it `Int { width: <target pointer
//@ probe-note: width> }`, so the E6 import is minted at `UInt64` on a 64-bit target) but
//@ probe-note: the clause side handed the elaborator the bare name `usize`, which it
//@ probe-note: refuses on purpose ("unsupported clause variable type `usize`") because
//@ probe-note: the name does not say which carrier it means — an internal inconsistency,
//@ probe-note: not a deliberate exclusion. The compiler now resolves the row from the
//@ probe-note: TARGET's pointer width before the E9 lanes see it
//@ probe-note: (`trust_fn_discharge_binder_types`), to the SAME fixed-width carrier the
//@ probe-note: import carries.
//@ probe-note:
//@ probe-note: MEASURED both ways on 2026-09-17: `discharged` on a stage1 carrying the
//@ probe-note: change, and `clause-outside-fragment` ("unsupported clause variable type
//@ probe-note: `usize`") on the stage2 built from the parent commit, which is the
//@ probe-note: negative control for this row. 64-BIT HOSTS ONLY — the island below is
//@ probe-note: stated at `UInt64`; on a 32-bit target the binder is `UInt32` and this
//@ probe-note: row must read `clause-outside-fragment`, which is the width control
//@ probe-note: working, not a regression. `f67` is the close negative twin.
clean { def ident_isl (x : UInt64) : UInt64 := x }
pub fn f(x: usize) -> usize
    ensures result == ident_isl(x)
{
    x
}

//@ battery-lane: C-combo
//@ battery-expect: reject
//@ battery-flags: -Ztrust-verify=on --crate-type=lib
//! LANE C NEGATIVE CONTROL — defeq must not be a rubber stamp.
//!
//! The island definition says `x`. The body returns `x + 1`. These are
//! STRUCTURALLY not definitionally equal, so the constructed `Eq.refl` must
//! fail to typecheck and the clause must stay undischarged.
//!
//! If this file passes, the uncited lane in `c2_uncited_defeq` is discharging
//! by name-matching rather than by kernel checking, and the "one program, two
//! languages" claim collapses into a naming convention.

clean {
    def ident_isl (x : UInt64) : UInt64 := x
}

/// FALSE: `x + 1` is not `ident_isl x`.
pub fn diverges(x: u64) -> u64
    ensures result == ident_isl(x)
{
    x + 1
}

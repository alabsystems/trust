//@ battery-lane: C-combo
//@ battery-expect: pass
//@ battery-flags: -Ztrust-verify=on --crate-type=lib
//! LANE C (THE COMBO) — UNCITED discharge by kernel definitional equality.
//!
//! The harder half of the thesis: the programmer writes NO citation at all.
//! An `ensures` that calls an island definition discharges because the
//! kernel checks a constructed `Eq.refl` term — E6 admission supplies the
//! imported Rust body, the island environment supplies the Lean definition,
//! and DEFEQ closes the goal (§1 typed-citation discharge, the composed lane).
//!
//! This is the mode that makes the two languages one program rather than two
//! artifacts stapled together: the Lean definition and the Rust body are the
//! same object to the kernel.

clean {
    def ident_isl (x : UInt64) : UInt64 := x
}

/// No `by`. The kernel closes this because the body IS the island definition.
pub fn pass_through(x: u64) -> u64
    ensures result == ident_isl(x)
{
    x
}

/// Same discharge, exercised twice in one signature.
pub fn pass_through_twice(x: u64) -> u64
    ensures result == ident_isl(x)
    ensures result == ident_isl(x)
{
    x
}

//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: ERROR
//! The CLOSE NEGATIVE TWIN of `e9_island_literal_decide_sugar`: the same
//! `decide (d < N)` sugar, at the same carrier, in the same clause position —
//! with `N` off by one from the constant the Rust body tests.
//!
//! Making the literal sugar discharge must not make it discharge against the
//! WRONG constant. `21` and `22` are two different decisions, the kernel says
//! so, and the clause fails closed: an uncited island-calling clause has
//! exactly one route, so a refusal here leaves it constraining nothing and the
//! build stops.
//!
//! `e9_island_literal_decide_sugar` (the same file with `22` written `21`) is
//! the positive half; the two differ by one character.
//!
//! MEASURED on the packed `trustc` 379912412b1 (2026-09-19), i.e. before the
//! Clean repair: ``uncited `ensures` naming the Clean island definition
//! `depth_fits_isl` was not discharged by definitional equality: the two sides
//! are not definitionally equal (Eq.refl does not check)``, then the strict
//! gate on two unproved obligations. The repair does not touch this file's
//! verdict — only the reason it holds changes from "the instances never met"
//! to "21 and 22 are different decisions", and
//! `clean-elab/tests/uint_literal_decide_instance_e2e.rs::
//! a_different_literal_is_still_refused` is the control that says so.

clean {
    def depth_fits_isl (d : UInt32) : Bool := decide (d < 22)
}

fn octree_depth_fits(depth: u32) -> bool
    ensures result == depth_fits_isl(depth)
{
    depth < 21
}

fn main() {
    let _ = octree_depth_fits(3);
}

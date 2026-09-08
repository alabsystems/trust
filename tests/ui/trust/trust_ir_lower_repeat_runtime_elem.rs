//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-RRE): a large repeat with a RUNTIME element falls back to the
//! ordinary first-class build.
//!
//! The compact form ENCODES its constant N times in one instruction, so it
//! needs a right-here-known constant; a parameter read or a binop result is
//! neither. But the same expression already takes the first-class N-element
//! build below `REPEAT_COMPACT_MIN`, so the only thing missing was the
//! fallback — placed INSIDE the compact helper, because the element has
//! already been lowered and re-lowering would duplicate its side effects.
//!
//! `over_budget_declines` pins the budget: 2N+1 instructions are invisible to
//! the THIR-expr cap (a repeat is three THIR exprs however large N is), so the
//! cap has to be stated separately and must not be raised silently. That body
//! keeps its refusal and must still compute correctly.

pub fn runtime_elem(x: u64) -> u64 {
    let a = [x; 1024];
    a[0] + a[1023]
}

pub fn binop_elem() -> u64 {
    let a = [10u64 + 20; 1200];
    a[0] + a[1199]
}

/// Above the budget: refuses, and is still right.
pub fn over_budget_declines(x: u64) -> u64 {
    let a = [x; 4096];
    a[0] + a[4095]
}

fn main() {
    assert_eq!(runtime_elem(3), 6);
    assert_eq!(binop_elem(), 60);
    assert_eq!(over_budget_declines(2), 4);
}

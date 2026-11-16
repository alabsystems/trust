//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust: a repeat with a RUNTIME element lowers at every count, as ONE `Inst::ArraySplat`
//! (trust-ir v50) — the element register repeated, constant size in N.
//!
//! History (wave-RRE): the compact form encoded a CONSTANT N times in one instruction, so a
//! runtime element (a parameter read, a binop result) fell back to the first-class N-element
//! build — 2N+1 instructions — behind an instruction budget (`REPEAT_RUNTIME_ELEM_MAX`, 2048)
//! that `over_budget_declines` below used to pin as a refusal. The uniform-array value makes
//! the budget's reason disappear, and the budget with it: that body lowers now, and all three
//! must still compute correctly. (Under `-Ztrust-verify=off` a refusal is a silent coverage
//! skip; `trust_ir_uniform_array_strict.rs` pins the no-refusal half under `strict`.)

pub fn runtime_elem(x: u64) -> u64 {
    let a = [x; 1024];
    a[0] + a[1023]
}

pub fn binop_elem() -> u64 {
    let a = [10u64 + 20; 1200];
    a[0] + a[1199]
}

/// Past the retired budget: lowers, and is still right.
pub fn over_budget_declines(x: u64) -> u64 {
    let a = [x; 4096];
    a[0] + a[4095]
}

fn main() {
    assert_eq!(runtime_elem(3), 6);
    assert_eq!(binop_elem(), 60);
    assert_eq!(over_budget_declines(2), 4);
}

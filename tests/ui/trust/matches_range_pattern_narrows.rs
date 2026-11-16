//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
#![crate_type = "lib"]
//! `matches!(c, L..=U)` narrows `c` for the branch it guards, whether it is
//! tested directly or held in a `bool` first.
//!
//! MEASURED OVER-REFUSAL, 2026-09-29, on the 659-program ordinary-Rust sweep:
//! each function below was refuted — a counterexample, fatal on the default lane —
//! with `c = 0`. rustc lowers the range pattern to two chained comparisons whose
//! FALSE edges both reach ONE `_b = false` block, and the nested switch-merge lane
//! (`guards::nested_switch_branch_merge_definitions`) admitted only a TREE of
//! arms, so the joined `bool` had no definition. A leaf shared by several switches
//! of the tree is now admitted when every one of its predecessors is a switch of
//! that tree.
//!
//! `matches_range_pattern_narrows_refused.rs` holds the twins that really overflow.

pub fn upper(c: u8) -> u8 {
    if matches!(c, b'a'..=b'z') { c - 32 } else { c }
}

pub fn upper_via_bool(c: u8) -> u8 {
    let is_lower = matches!(c, b'a'..=b'z');
    if is_lower { c - 32 } else { c }
}

pub fn shifted(c: u32) -> u32 {
    if matches!(c, 100..=200) { c - 50 } else { c }
}

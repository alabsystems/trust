//@ revisions: inline unit
//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **I8 — THE IDENTICAL-GRAPH-ENTRIES CONTROL.**
//!
//! One `def`, two spellings, two revisions, ZERO other source change:
//!
//!  * `inline`: `clean { def pick … }` written in this file;
//!  * `unit`:   `clean mod clean_unit_equiv_helper;` +
//!              `clean_unit_equiv_helper.clean` holding the SAME text.
//!
//! Both revisions must mint the same name into the same module (the crate
//! root — the unit introduces NO module scope; its ident names the file), so
//! `crate::pick` resolves identically, the same kernel-gated body is emitted,
//! and the same value comes back. If the two forms produced different graph
//! entries — a different parent, a different name, a refusal on one side —
//! one revision goes red and the control has done its job.
//!
//! This test ALSO pins cfg-strippability of both forms, which is the seam
//! decision itself: in each revision the other form is `#[cfg]`'d out, and in
//! the `inline` revision that means the `clean mod` item is stripped BEFORE
//! its file would load (loading happens at the out-of-line-module expansion
//! seam, after cfg). `clean_unit_cfg_off.rs` pins the stronger form of that
//! (cfg'd-out unit with NO file on disk at all).

#[cfg(inline)]
clean {
    def pick (a b : UInt64) : UInt64 := a
}

#[cfg(unit)]
clean mod clean_unit_equiv_helper;

fn main() {
    let g = crate::pick(6u64, 7u64);
    assert_eq!(g, 6, "both spellings must denote the same projection");
}

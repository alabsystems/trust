//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-name=t --crate-type=lib
//@ rustc-env: TRUST_R1_TRACE=1
//@ normalize-stderr: "formula=.* freevars=\{[^}]*\}" -> "formula=$$FORMULA freevars=$$FREEVARS"
//@ normalize-stderr: "sealed [0-9a-f]{64}" -> "sealed $$DIGEST"
//@ check-pass
//
// SOUNDNESS GUARD (R1 def-path identity, item 2). The R1 seam renders def paths
// through TWO different producers and their key spaces are NOT disjoint:
//
//   RAW  = `with_no_trimmed_paths!(tcx.def_path_str(d))`      (no crate prefix)
//   SEAM = `trust_mir_extract::safe_def_path_str(tcx, d)`     (crate prefix)
//
// RAW drops exactly one leading segment (`print_crate_name` skips `LOCAL_CRATE`
// unless `with_resolve_crate_name` is in force), so any nesting that eats one
// segment makes the two spaces COLLIDE. Below, crate `t` contains `mod t`, and
// the checked-in stderr shows all four renderings in ONE run:
//
//   RAW(t::t::helper) == "t::helper"   <- `t::helper: found Failed VC ... loc=42:8`
//   SEAM(t::t::helper) == "t::t::helper"
//   RAW(t::helper)     == "helper"     <- `helper: found Failed VC ... loc=49:4`
//   SEAM(t::helper)    == "t::helper"  <- byte-identical to RAW of the OTHER DefId
//
// (Those `loc=` values are the line/column of the two `x / d` expressions below and
// move with this comment; re-bless after editing it.)
//
// So a set keyed RAW and consulted with a SEAM key does not merely miss (lost
// recovery) — it can HIT THE WRONG DefId (fail-open). That is why
// `r1_generic_mono_caller_closure` is keyed through `safe_def_path_str`, the same
// producer its sole consumer (`r1_generic_mono_coverage`) looks up with.
//
// This file pins the KEY SPACES with an EMPTY caller closure
// (`covered=0 caller-closure=0` below). `generic_mono_caller_closure_collision.rs`
// is the same collision with a NON-EMPTY one, which is where the fail-open is live.
//
// Falsify-once control: `caller_closure_key_space_no_collision.rs` is this file
// with the module renamed `u`; there RAW = {`u::helper`, `helper`} and
// SEAM = {`t::u::helper`, `t::helper`} are disjoint, and its stderr differs.
#![allow(dead_code)]
mod t {
    pub(crate) fn helper(x: u32, d: u32) -> u32 {
        x / d
    }
    pub(crate) fn call() -> u32 {
        helper(10, 5)
    }
}
fn helper(x: u32, d: u32) -> u32 {
    x / d
}
fn call2() -> u32 {
    helper(20, 4)
}
fn go() {
    let _ = t::call();
    let _ = call2();
}

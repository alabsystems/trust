//@ needs-trust-verify
//@ no-prefer-dynamic
//@ aux-build:unauthenticated_iter_adaptor_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! THE CRATE-FREE GRANT — an unbounded-allocation obligation deleted by renaming
//! one user function, with no impersonation of anything.
//!
//! The four `trusted_root_spoof_*` tests in this directory are about a crate that
//! WEARS a sysroot name. This one needs none of that. `is_len_preserving_adaptor`
//! matched on the callee's LAST PATH SEGMENT — `map`/`filter_map`/`inspect`/
//! `enumerate`/`copied`/`cloned`/`rev`/`by_ref`, plus the sibling `filter`/`take`/
//! `skip`/`step_by`/`take_while` arm and the `chain` arm — naming no crate,
//! anchoring no root and consulting no stamp. So an ORDINARY dependency's
//! `Adapt::map` stepped the bounded-source walk through to argument 0, where the
//! genuine `core::slice::<impl [u8]>::iter` sat, and
//! `generate_unbounded_allocation_vcs` executed `continue`: the obligation was not
//! weakened, it DISAPPEARED.
//!
//! `mycrate::Endless::next` never returns `None`, so `boom` allocates without
//! bound in EVERY execution — the exact 203 GB growth the unbounded-allocation
//! lane was written for.
//!
//! The engine had the evidence and threw it away. The collect sink is spelled
//!
//! ```text
//! <mycrate::Endless as core::iter::traits::iterator::Iterator>::collect::<alloc::vec::Vec<u8>>
//! ```
//!
//! — the iterator being collected is a USER ADT. The fix authenticates the chain
//! std end to end: every adaptor step must be a genuine std `Iterator` method
//! (anchored trait root, no unauthenticated-crate stamp), and the value at every
//! step must have a root-authenticated sysroot iterator type.
//!
//! The control is `unauthenticated_iter_adaptor_collect_control.rs`: the same
//! bytes with `nudge` in place of `map`. It reports these two errors on pristine
//! `main`, which is what makes this file's silence a defect and not a modeling
//! gap.
//!
//! The two annotated errors are the ones the control produces verbatim. They are
//! a PREDICTION for this file: the patched compiler was NOT built (x.py is out of
//! scope for this work). If the post-fix wording or count differs, this test fails
//! loudly.
//!
//! NON-VACUITY, MEASURED — and the earlier claim here, *"with the hole open there
//! is no diagnostic at all"*, was simply false. Compiled with this file's own
//! `compile-flags` on `stage2/bin/trustc` (`rustc 1.99.0-dev (0a3cd0152)`, the
//! compiler that still HAS the hole), it exits 1 and emits:
//!
//! ```text
//! warning: Trust Level 0 safety verification incomplete for `…::boom`: 1 obligation(s) were not proved
//! error:   Trust strict verification failed for `…::boom`: 1 obligation(s) were not fully verified
//! ```
//!
//! against the control's TWO errors and `2 obligation(s)`. So the hole-open state
//! is distinguishable in three independent ways, and the first is the one
//! compiletest reads: the `Level 0 … incomplete` diagnostic is a WARNING there and
//! an ERROR here, so the first `//~^ ERROR` annotation has no matching error and
//! the test fails on the level mismatch. The obligation count (1 vs 2) and the
//! missing `count-not-derivable` note are the other two.
//!
//! ANNOTATION PLACEMENT. Both errors' PRIMARY SPAN is the whole function item, so
//! its `line_start` is the `pub fn boom(..)` signature line, not the expression
//! inside — MEASURED on the shipped compiler, which reports
//! `consumer.rs:5:1` with the caret under the entire `pub fn boom(..) { .. }`.
//! compiletest resolves `//~^` against that start line, so the annotations sit
//! directly under the signature, exactly as `e2_mut_prime_undischarged.rs:19` and
//! `e9_definitional_call_undischarged.rs:14` do.
#![allow(dead_code)]

extern crate mycrate;

#[inline(never)]
pub fn boom(v: &Vec<u8>) -> Vec<u8> {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    mycrate::Adapt::map(v.iter(), 0).collect()
}

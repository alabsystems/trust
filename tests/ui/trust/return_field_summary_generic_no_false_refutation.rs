//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: [overflow:sub] FAILED
//@ check-pass
//! bit-vec 0.9.1's `pop` in its own GENERIC spelling (`impl<B: BitBlock>
//! BitVec<B>`, `src/lib.rs:1638`) is no longer refuted (TRUST-10).
//!
//! On the installed toolchain (`trustc 0.10.0+g450403669`) `pop`'s subtraction
//! was reported
//!
//!     [overflow:sub] FAILED (ay-in-process); counterexample: _3*#s0_0 = 0, _4 = false, …, self*.1#e_s1_t = 0
//!
//! — `is_empty()` false at `nbits == 0`, not an execution for any `B`. The
//! summary is derived from the generic bodies and applies at every call
//! rendered with the same instantiation (`BitVec::<B>::is_empty`).
//!
//! WHY ADVISORY, and what is asserted. Under the strict default this function
//! still fails, on a row TRUST-10 does not touch: each call from a generic body
//! to a same-crate generic callee is an "unproven panic-freedom obligation for
//! a call to an absent callee" (a generic absent callee keeps the function
//! fail-closed), so the `[assert]` row stays runtime-checked. The assertion is
//! therefore two-part: `forbid-output` — no `[overflow:sub]` row is FAILED —
//! and the NOTE below — the function WAS verified, with exactly one row (the
//! subtraction) proved and none failed. When the absent-callee row closes, the
//! count becomes 2 and this function belongs in the strict
//! `return_field_summary_no_false_refutation.rs`.

pub struct BitVec<B> {
    storage: Vec<B>,
    nbits: usize,
}

impl<B> BitVec<B> {
    // bit-vec's is `if cfg!(test) { debug_assert!(..) }`: a `&self` call that
    // does nothing outside its own test build.
    fn ensure_invariant(&self) {
        let _ = &self.storage;
    }

    pub fn len(&self) -> usize {
        self.nbits
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn pop(&mut self) -> Option<usize> {
        //~^ NOTE Trust verification: 1 proved, 0 failed
        self.ensure_invariant();
        if self.is_empty() {
            None
        } else {
            let i = self.nbits - 1;
            self.nbits = i;
            Some(i)
        }
    }
}

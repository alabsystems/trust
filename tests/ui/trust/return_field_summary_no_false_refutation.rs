//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! A same-crate `bool` callee that compares a field THROUGH A GETTER is
//! summarised (TRUST-10, the last false class bit-vec 0.9.1 showed).
//!
//! `pop` is bit-vec's (`src/lib.rs:1638`) with the bit storage reduced away:
//! `is_empty()` is `self.len() == 0` and `len()` is `self.nbits`, and the
//! subtraction sits on the non-empty branch. On the installed toolchain
//! (`trustc 0.10.0+g450403669`) every subtraction below was reported, e.g.
//!
//!     [overflow:sub] FAILED (ay-in-process); counterexample: _2 = false, …, self*.0#e_s0_t = 0
//!
//! i.e. `is_empty()` false at `nbits == 0`, which no execution produces: the
//! call's result was a free variable. `generate::return_field_summary` derives
//! `len: ret == (*self).nbits` and `is_empty: ret ⇔ ((*self).nbits == 0)` from
//! the two bodies and states the second over the caller's own spelling of the
//! field, before and after the call.
//!
//! THE STRICT BUILD IS THE ASSERTION: every row must be proved under the
//! default policy, so this file compiles exactly when none is refuted (or left
//! unknown). The paired `return_field_summary_real_underflow_still_refutes.rs`
//! keeps the real bugs next to the same helpers refuted, and
//! `return_field_summary_generic_no_false_refutation.rs` carries bit-vec's own
//! generic spelling (`impl<B> BitVec<B>`), which strict mode refuses for an
//! unrelated coverage row.

pub struct Plain {
    nbits: usize,
}

impl Plain {
    /// bit-vec's `ensure_invariant`: a `&self` call ahead of the check, which
    /// re-versions `self`'s fields before `is_empty()` reads them.
    fn ensure_invariant(&self) {
        let _ = self.nbits;
    }

    pub fn len(&self) -> usize {
        self.nbits
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn holds_at_least(&self) -> bool {
        !(4 > self.len())
    }

    pub fn pop(&mut self) -> Option<usize> {
        if self.is_empty() {
            None
        } else {
            let i = self.nbits - 1;
            self.nbits = i;
            Some(i)
        }
    }

    pub fn pop_after_check(&mut self) -> Option<usize> {
        self.ensure_invariant();
        if self.is_empty() {
            None
        } else {
            let i = self.nbits - 1;
            self.nbits = i;
            Some(i)
        }
    }

    pub fn last_index(&self) -> Option<usize> {
        if self.is_empty() { None } else { Some(self.len() - 1) }
    }

    pub fn drop_four(&mut self) -> Option<usize> {
        if self.holds_at_least() { Some(self.nbits - 4) } else { None }
    }
}

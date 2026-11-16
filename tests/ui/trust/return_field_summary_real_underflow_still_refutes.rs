//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! FAIL-OPEN GUARD for the field-read return summary (TRUST-10).
//!
//! The helpers are the ones `return_field_summary_no_false_refutation.rs`
//! proves through; every subtraction below REALLY underflows, so the summary
//! (a true fact about the helper) must leave each one refuted with a
//! counterexample:
//!
//! * `pop_inverted` — the subtraction on the EMPTY branch (`nbits == 0`);
//! * `pop_wrong_field` — the guard compares `cap`, not `nbits`;
//! * `pop_after_reset` — `nbits = 0` between the check and the use;
//! * `drop_five` — `len() >= 4` does not cover `- 5` (`nbits == 4`);
//! * `pop_weird` — `weird()` branches, so it is not summarised at all and
//!   returns `false` at `cap == 0, nbits == 0`;
//! * `G::<B>::pop_inverted` — `pop_inverted` in bit-vec's generic spelling:
//!   the summary is applied to generic bodies too, and must not hide this one.
//!
//! If a row here stops being `FAILED`, the summary has stopped being a fact
//! about the callee (or reached a place it does not describe).

pub struct V {
    nbits: usize,
    cap: usize,
}

impl V {
    pub fn len(&self) -> usize {
        self.nbits
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn cap_is_zero(&self) -> bool {
        self.cap == 0
    }

    pub fn holds_at_least(&self) -> bool {
        !(4 > self.len())
    }

    pub fn weird(&self) -> bool {
        if self.cap > 0 { self.nbits == 0 } else { false }
    }

    pub fn pop_inverted(&mut self) -> Option<usize> {
        //~^ ERROR Trust strict verification failed
        //~| NOTE [overflow:sub] FAILED
        if self.is_empty() { Some(self.nbits - 1) } else { None }
    }

    pub fn pop_wrong_field(&mut self) -> Option<usize> {
        //~^ ERROR Trust strict verification failed
        //~| NOTE [overflow:sub] FAILED
        if self.cap_is_zero() { None } else { Some(self.nbits - 1) }
    }

    pub fn pop_after_reset(&mut self) -> Option<usize> {
        //~^ ERROR Trust strict verification failed
        //~| NOTE [overflow:sub] FAILED
        if self.is_empty() {
            None
        } else {
            self.nbits = 0;
            Some(self.nbits - 1)
        }
    }

    pub fn drop_five(&mut self) -> Option<usize> {
        //~^ ERROR Trust strict verification failed
        //~| NOTE [overflow:sub] FAILED
        if self.holds_at_least() { Some(self.nbits - 5) } else { None }
    }

    pub fn pop_weird(&mut self) -> Option<usize> {
        //~^ ERROR Trust strict verification failed
        //~| NOTE [overflow:sub] FAILED
        if self.weird() { None } else { Some(self.nbits - 1) }
    }
}

pub struct G<B> {
    storage: Vec<B>,
    nbits: usize,
}

impl<B> G<B> {
    pub fn len(&self) -> usize {
        self.nbits
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn pop_inverted(&mut self) -> Option<usize> {
        //~^ ERROR Trust strict verification failed
        //~| NOTE [overflow:sub] FAILED
        let _ = &self.storage;
        if self.is_empty() { Some(self.nbits - 1) } else { None }
    }
}

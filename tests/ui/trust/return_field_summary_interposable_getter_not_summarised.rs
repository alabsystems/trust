//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! IDENTITY GATE of the field-read return summary (TRUST-10).
//!
//! `pop` is `return_field_summary_no_false_refutation.rs`'s `Plain::pop`, whose
//! subtraction PROVES through `is_empty -> len`. Here the getter is exported
//! (`#[no_mangle]` / `#[export_name]`): its symbol can be interposed at link
//! time, so the body the compiler read need not be the one a call runs, and
//! `trust_init_backing_certificates` admits no field-read summary for it — nor
//! for `is_empty`, which reads the field only THROUGH it.
//!
//! The rows below are therefore what they were before TRUST-10: the call
//! result is free and the subtraction is refuted (D5-A's hold screens free
//! `fn`s only, and these are inherent methods). That refutation is NOT a real
//! bug; it is pinned because it is the observable edge of the gate. If a row
//! here starts to prove, an interposable body has started to lend a summary.

pub struct Mangled {
    nbits: usize,
}

impl Mangled {
    #[no_mangle]
    pub fn return_field_summary_mangled_len(&self) -> usize {
        self.nbits
    }

    pub fn is_empty(&self) -> bool {
        self.return_field_summary_mangled_len() == 0
    }

    pub fn pop(&mut self) -> Option<usize> {
        //~^ ERROR Trust strict verification failed
        //~| NOTE [overflow:sub] FAILED
        if self.is_empty() {
            None
        } else {
            let i = self.nbits - 1;
            self.nbits = i;
            Some(i)
        }
    }
}

pub struct Exported {
    nbits: usize,
}

impl Exported {
    #[export_name = "return_field_summary_exported_is_empty"]
    pub fn is_empty(&self) -> bool {
        self.nbits == 0
    }

    pub fn pop(&mut self) -> Option<usize> {
        //~^ ERROR Trust strict verification failed
        //~| NOTE [overflow:sub] FAILED
        if self.is_empty() { None } else { Some(self.nbits - 1) }
    }
}

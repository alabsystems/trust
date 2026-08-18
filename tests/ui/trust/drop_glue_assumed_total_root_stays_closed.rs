//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! MUTANT of `drop_glue_proved_destructor_credits.rs`: a destructor whose panic
//! freedom RESTS ON a `#[trust::assume_total]` axiom must not credit the glue.
//!
//! The drop-glue premise (`drop_glue_discharges_panic_freedom`) reads the SAME
//! evidence bar as Φ and the two reliance lanes, so it inherited the same defect:
//! `<Q as Drop>::drop` verifies conditionally on `boom`'s declared totality and
//! publishes the row set of a body with no obligations at all, so the bar credited
//! it, the dropped ADT entered the structural-drop set, and `take`'s drop-glue row
//! was DROPPED. `take` then verified with zero obligations while the real drop
//! panics.
//!
//! The paired `drop_glue_panicking_drop_stays_closed.rs` plants a panic the
//! verifier can SEE. This file plants one the verifier was told to assume away —
//! the difference between an unproved row and a vanished one.
//!
//! MEASURED on stage-equivalent main `0a3cd01520`: rc=0 (ACCEPTED).
#![feature(register_tool)]
#![register_tool(trust)]

/// An axiom the author asserted and nobody proved — and it is FALSE.
#[trust::assume_total]
fn boom() {
    panic!("boom");
}

pub struct Q {
    a: u8,
}

impl Drop for Q {
    fn drop(&mut self) {
        boom();
    }
}

pub fn take(q: Q) -> u8 {
    q.a
}

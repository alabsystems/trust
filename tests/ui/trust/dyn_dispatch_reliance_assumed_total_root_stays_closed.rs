//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! MUTANT: a C-FLOW case-split member whose own verdict RESTS ON a
//! `#[trust::assume_total]` axiom must REFUSE the discharge.
//!
//! The sibling fixture `dyn_dispatch_reliance_skipped_target_refuses.rs` pins the
//! attribute ON THE TARGET. This one puts the user declaration one frame DOWN,
//! where no attribute on `<S as Tick>::tick` can be seen: `tick` verifies
//! conditionally on `boom`'s declared totality, and MEASURED on pristine main its
//! published ledger is byte-identical to a genuinely obligation-free body
//! (`no_obligations` / `proved`, empty dispositions, no transport rows, a native
//! run reporting `requested_obligations: 0`). There is nothing in the row set to
//! read, which is why the gate consults the bundle's own user-axiom census.
//!
//! Every OTHER conjunct of the case split passes: the coercion provenance is
//! complete inside `drive`'s bundle, the reachable target set is exactly `{S}`,
//! `<S as Tick>::tick` is a concrete local `Item`, and it carries no authored
//! clause. The axiom under it is the only thing keeping `drive` red.
//!
//! MEASURED on stage-equivalent main `0a3cd01520` (WITHOUT the gate): this file
//! compiles CLEAN, rc=0, with `TRUST_DYN_RELIANCE_PROBE=1` printing
//! `site=<dyn Tick>::tick (1 site(s)) method=Tick::tick => DISCHARGED`.
#![no_std]
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(trust)]

/// An axiom the author asserted and nobody proved — and it is FALSE.
#[trust::assume_total]
fn boom() {
    panic!("boom");
}

pub trait Tick {
    fn tick(&mut self);
}

pub struct S {
    n: u32,
}

impl Tick for S {
    fn tick(&mut self) {
        boom();
        self.n = self.n.wrapping_add(1);
    }
}

pub fn drive() {
    let mut s = S { n: 0 };
    let t: &mut dyn Tick = &mut s;
    t.tick();
}

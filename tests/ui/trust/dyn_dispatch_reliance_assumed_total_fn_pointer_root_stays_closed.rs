//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! MUTANT: the `dyn` C-FLOW case split must refuse a target that reaches a
//! `#[trust::assume_total]` axiom through a REIFIED FUNCTION POINTER.
//!
//! Same shape as `dyn_dispatch_reliance_assumed_total_root_stays_closed.rs`, with
//! the axiom spelled `let f: fn() = boom; f();` instead of `boom()`. That lowering
//! has no `FnDef` call operand at all, so the axiom reaches the verdict without
//! passing through the bridge's assumption sets — the channel the bundle census
//! used to be keyed on.
//!
//! MEASURED, both states, on two compilers built from this tree: with the
//! call-operand census alone, `axiom census root=<S as Tick>::tick axiom_free=true`
//! and `site=<dyn Tick>::tick (1 site(s)) method=Tick::tick => DISCHARGED`, rc=0.
//! With `collect_user_axiom_value_mentions` the census reads `axiom_free=false`
//! with `user_axiom_keys=1, assumed_total=0` — censused, never spent — and the
//! C-FLOW case split declines the target.
//!
//! Every other conjunct of the case split still passes here: the coercion
//! provenance is complete inside `drive`'s bundle, the reachable target set is
//! exactly `{S}`, `<S as Tick>::tick` is a concrete local `Item`, and it carries no
//! authored clause. The reified axiom under it is the only thing keeping `drive`
//! red.
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
        let f: fn() = boom;
        f();
        self.n = self.n.wrapping_add(1);
    }
}

pub fn drive() {
    let mut s = S { n: 0 };
    let t: &mut dyn Tick = &mut s;
    t.tick();
}

//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! MUTANT: the `dyn` C-FLOW case split must refuse a target whose only path to a
//! `#[trust::assume_total]` axiom runs through a FUNCTION POINTER IN A STATIC.
//!
//! Same shape as `dyn_dispatch_reliance_assumed_total_root_stays_closed.rs` and its
//! `_fn_pointer_` sibling, with the axiom moved one step further out of sight:
//! `<S as Tick>::tick` names only `TABLE`, and `boom as fn()` exists only inside
//! TABLE's own initializer body, which is not a member of the DefId walk. The
//! call-operand census and the value-mention scan are both blind to it.
//!
//! MEASURED, both states, on three compilers built from this tree. On pristine main
//! AND on the round-3 compiler this file compiles rc=0 with `C-FLOW admitted 1
//! target(s)` and `site=<dyn Tick>::tick (1 site(s)) method=Tick::tick =>
//! DISCHARGED`; on round 3 the census prints `axiom census root=<S as Tick>::tick
//! axiom_free=true (user_axiom_keys=0, assumed_total=0)`. (Pristine main emits no
//! `axiom census` line at all, so that half is a round-3 measurement.) With the
//! constant-memory walk the same probe prints `axiom_free=false
//! (const_memory_reads_complete=true, user_axiom_keys=1, assumed_total=0)` and the
//! ONE decline it reports is `C-FLOW declined: target <S as Tick>::tick the body is
//! proved only CONDITIONALLY`.
//!
//! This is the SHARED-BAR half of the same one-function change that closes
//! `static_str_write_fmt_assumed_total_static_table_root_stays_closed.rs`: the
//! refusal lives at conjunct 5 of `instance_discharges_panic_freedom`, so the
//! `write!` reduction, this C-FLOW split and the drop-glue premise inherit it
//! together rather than each re-deriving it.
//!
//! The recovery control is `dyn_dispatch_reliance_cflow_concrete_sink.rs`, which
//! must stay green: a legitimately proved target with no axiom under it is still
//! admitted.
#![no_std]
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(trust)]

/// An axiom the author asserted and nobody proved — and it is FALSE.
#[trust::assume_total]
fn boom() {
    panic!("boom");
}

/// The dispatched body never mentions `boom`. It mentions THIS.
static TABLE: [fn(); 1] = [boom];

pub trait Tick {
    fn tick(&mut self);
}

pub struct S {
    n: u32,
}

impl Tick for S {
    fn tick(&mut self) {
        (TABLE[0])();
        self.n = self.n.wrapping_add(1);
    }
}

pub fn drive() {
    let mut s = S { n: 0 };
    let t: &mut dyn Tick = &mut s;
    t.tick();
}

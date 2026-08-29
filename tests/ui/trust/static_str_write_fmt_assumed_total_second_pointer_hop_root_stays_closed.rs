//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! MUTANT: the `write!` reduction must refuse a target that reaches a
//! `#[trust::assume_total]` axiom through a SECOND reified function pointer.
//!
//! This is the depth case, and it is NOT the one
//! `static_str_write_fmt_assumed_total_transitive_root_stays_closed.rs` pins. There
//! the axiom sits under a DIRECT call, so `helper` is a walked member of
//! `write_str`'s bundle and the census reads its body as a matter of course. Here
//! BOTH edges are reified:
//!
//! ```text
//! write_str --(let f: fn() = mid)--> mid --(let f: fn() = boom)--> boom
//! ```
//!
//! A reified edge produces no `FnDef` call operand, so `mid` is not a direct callee,
//! is not bundled, and is not walked — `defid_walk_members` never counts it. The
//! one-hop census resolved the pointer to `mid`'s `DefId` and read that `DefId`'s
//! ATTRIBUTES only; `mid` carries none, so the walk stopped there and the axiom one
//! frame below was censused NOWHERE.
//!
//! WHY THIS FILE EXISTS. The transitive hop
//! (`follow_user_axiom_pointer_hop`) landed with its reproducer as a throwaway probe
//! program and NO fixture, so nothing in the suite held it: reverting the recursion
//! left every ui test green. `verdict_rests_on_user_axiom` said so itself — it named
//! the fn-pointer and static-table spellings as "the two spellings whose closure
//! this gate DOES claim ... the ones with fixtures", and this third one had none.
//!
//! MEASURED, both states, on ONE binary — stage2 `trustc` built from
//! `ddb545d35b`, whose `trust_verify.rs` is byte-identical to the one at
//! `28220d5879` where these numbers were taken — by the axiom/control pair. The
//! control is `static_str_write_fmt_assumed_total_second_pointer_hop_control.rs`,
//! which is this file with the attribute and the `panic!` removed and is
//! `check-pass`:
//!
//! ```text
//! THIS FILE      axiom census root=<…Sink as core::fmt::Write>::write_str
//!                axiom_free=false  user_axiom_keys=1  assumed_total=0   rc=1
//! THE CONTROL    axiom census root=<…Sink as core::fmt::Write>::write_str
//!                axiom_free=true   user_axiom_keys=0  assumed_total=0   rc=0
//! ```
//!
//! The pair is the whole assertion. A census that refused on SHAPE — "this bundle
//! reifies a pointer at all" — would take the control down with it, and that is the
//! over-decline direction this pair rules out. `user_axiom_keys=1` with
//! `assumed_total=0` is the signature of the value-mention channel: censused, never
//! spent, so no `assumed_total` row exists to read the fact off.
//!
//! WHAT THIS PAIR HAS NOT BEEN WATCHED DOING, stated because the two older fixtures
//! in this family carry the stronger provenance and the difference must not blur.
//! `*_assumed_total_fn_pointer_root_stays_closed.rs` and
//! `*_assumed_total_static_table_root_stays_closed.rs` were each watched ACCEPTING
//! their planted violation on a prior binary. This pair was not, and cannot be: the
//! only binary that accepts it is one built without the transitive hop, and building
//! a second compiler is out of reach here. What HAS been watched, on the current
//! binary, is the pair going red in both directions — strip the axiom from this file
//! and compiletest reports "ui test did not emit an error"; plant the axiom in the
//! control and the control fails. That establishes the assertion is load-bearing, not
//! that the census is what makes it hold.
#![no_std]
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(trust)]

use core::fmt;

/// An axiom the author asserted and nobody proved — and it is FALSE.
#[trust::assume_total]
fn boom() {
    panic!("boom");
}

/// HOP 2. No attribute of its own, so reading this item's attributes — which is all
/// the one-hop census did — says nothing. The axiom is one reified edge BELOW.
fn mid() {
    let f: fn() = boom;
    f();
}

pub struct Sink {
    written: u32,
}

impl fmt::Write for Sink {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        // HOP 1. Reified, so there is no `FnDef` call operand for `mid` and `mid`
        // never becomes a bundled member.
        let f: fn() = mid;
        f();
        self.written = s.len() as u32;
        Ok(())
    }
}

pub fn render(sink: &mut Sink) -> fmt::Result {
    use fmt::Write as _;
    write!(sink, "constant")
}

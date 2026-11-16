//~ NOTE "line_start":43,"col_start":0,"line_end":45,"col_end":1},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":53,"col_start":0,"line_end":55,"col_end":1},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":61,"col_start":0,"line_end":63,"col_end":1},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//@ revisions: advisory
//@ needs-trust-verify
//@ edition: 2021
//@ aux-crate: dyn_arg_upstream_visitor=dyn_arg_upstream_visitor.rs
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//! DYN-ARG-PROVENANCE-1 review controls (2026-10-06): the private-function exemption
//! of `dyn_private_fn_local_values_stays_runtime_checked.rs` rests on "whatever the
//! virtual call reaches is code with its OWN row in this crate". Three values every call
//! site builds itself, with nothing adversarial inside, break that premise, so each
//! private function here keeps OD-1 item 14's class (c) `failed` row (line 1 pins
//! all three); the six other controls are in `dyn_private_fn_adversarial_values_is_failed.rs`
//! (a separate file only because compiletest truncates a test's output at 512 KiB):
//! (1) `via_bodyless_fn_item` is handed the fn item `<dyn Open as Open>::o`, a virtual
//!     shim with no body in this crate: the builtin `Fn` shim forwards `f(t)`'s OTHER
//!     argument, a public caller's trait object, into dispatch no row here covers.
//!     Before the fix (stage 1 of `d8ea7c3c6b`) it read `runtime_checked`, the crate
//!     had no `failed` row, and a verify-off downstream `impl Open` that panics
//!     panicked through `use_bodyless_fn_item`;
//! (2) `via_upstream_adt` is handed `&UpV`, an UPSTREAM fieldless ADT whose upstream
//!     impl of the open, non-blanket `Visitor<T>` dispatches on the trait object it is
//!     given (`auxiliary/dyn_arg_upstream_visitor.rs`): no body of this crate runs.
//!     Same before-fix reading; a downstream `impl Open2` panicked through
//!     `use_upstream_adt`;
//! (3) `via_upstream_fn_item` is handed `&dispatch_open2`, a NON-GENERIC upstream fn
//!     item (so only the locality of the fn item, not its generic arguments, decides
//!     it) that dispatches on the forwarded trait object in the dependency's body.
use dyn_arg_upstream_visitor::{Open2, UpV, Visitor, dispatch_open2};

pub trait Open {
    fn o(&self) -> u32;
}

type StaticOpen = dyn Open + 'static;

fn via_bodyless_fn_item(f: &dyn Fn(&StaticOpen) -> u32, t: &StaticOpen) -> u32 {
    f(t)
}

pub fn use_bodyless_fn_item(t: &StaticOpen) -> u32 {
    via_bodyless_fn_item(&<StaticOpen as Open>::o, t)
}

type StaticOpen2 = dyn Open2 + 'static;

fn via_upstream_adt(v: &dyn Visitor<StaticOpen2>, t: &StaticOpen2) -> u32 {
    v.visit(t)
}

pub fn use_upstream_adt(t: &StaticOpen2) -> u32 {
    via_upstream_adt(&UpV, t)
}

fn via_upstream_fn_item(f: &dyn Fn(&StaticOpen2) -> u32, t: &StaticOpen2) -> u32 {
    f(t)
}

pub fn use_upstream_fn_item(t: &StaticOpen2) -> u32 {
    via_upstream_fn_item(&dispatch_open2, t)
}

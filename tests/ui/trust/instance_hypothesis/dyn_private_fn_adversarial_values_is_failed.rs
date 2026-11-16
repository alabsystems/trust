//~ NOTE "line_start":39,"col_start":0,"line_end":41,"col_end":1},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":47,"col_start":0,"line_end":49,"col_end":1},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":55,"col_start":0,"line_end":57,"col_end":1},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":75,"col_start":0,"line_end":77,"col_end":1},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":91,"col_start":0,"line_end":93,"col_end":1},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":99,"col_start":0,"line_end":101,"col_end":1},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":104,"col_start":27,"line_end":104,"col_end":35},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//@ revisions: advisory
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//! DYN-ARG-PROVENANCE-1 controls (2026-10-05): the private-function exemption of
//! `dyn_private_fn_local_values_stays_runtime_checked.rs` holds only when EVERY call
//! site builds the value itself. Each private function here keeps OD-1 item 14's
//! class (c) `failed` row (line 1 pins all six), because a crate this compilation
//! does not see can still choose the trait object:
//! (1) `forward_inner` is handed the trait object a PUBLIC caller received;
//! (2) `via_fn_ptr` is handed a `fn() -> u32` pointer (any function, downstream ones
//!     included) unsized into `&dyn Fn`;
//! (3) `escapes` is itself handed out as a fn pointer, so anything can call it, though
//!     its one direct call site passes a local `&Calm`;
//! (4) `mixed` has one local closure call site and one forwarded trait object;
//! (5) `via_wrapper` is handed a LOCAL wrapper whose field is a forwarded trait object
//!     (ty `tla-backend`'s `RunFixedFacts(f)` shape): `Wrap::o` reaches it through a
//!     field projection, which no refutation sees, so this row must stay `failed`;
//! (6) `via_capturing_closure` is handed a local closure that CAPTURES a forwarded
//!     trait object (clean-ck0's `map_children_depth` shape). Since CLOSURE-CAPTURE-ROOT
//!     (2026-10-11) that closure's own row (`|| t.o()`, a capture of `pub fn`
//!     `use_capturing_closure`'s parameter) refutes too; before, it read
//!     `runtime_checked`. Line 1's last pin.
pub trait Open {
    fn o(&self) -> u32;
}

fn forward_inner(t: &dyn Open) -> u32 {
    t.o()
}

pub fn forward(t: &dyn Open) -> u32 {
    forward_inner(t)
}

fn via_fn_ptr(f: &dyn Fn() -> u32) -> u32 {
    f()
}

pub fn use_fn_ptr(p: fn() -> u32) -> u32 {
    via_fn_ptr(&p)
}

fn escapes(t: &dyn Open) -> u32 {
    t.o()
}

pub fn hand_out() -> fn(&dyn Open) -> u32 {
    escapes
}

struct Calm;

impl Open for Calm {
    fn o(&self) -> u32 {
        3
    }
}

pub fn call_escapes() -> u32 {
    escapes(&Calm)
}

fn mixed(f: &dyn Fn() -> u32) -> u32 {
    f()
}

pub fn use_mixed(g: &dyn Fn() -> u32) -> u32 {
    mixed(&|| 1).wrapping_add(mixed(g))
}

struct Wrap<'a>(&'a dyn Open);

impl Open for Wrap<'_> {
    fn o(&self) -> u32 {
        self.0.o()
    }
}

fn via_wrapper(t: &dyn Open) -> u32 {
    t.o()
}

pub fn use_wrapper(t: &dyn Open) -> u32 {
    via_wrapper(&Wrap(t))
}

fn via_capturing_closure(f: &dyn Fn() -> u32) -> u32 {
    f()
}

pub fn use_capturing_closure(t: &dyn Open) -> u32 {
    via_capturing_closure(&|| t.o())
}

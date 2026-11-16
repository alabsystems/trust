//~ NOTE "line_start":35,"col_start":0,"line_end":37,"col_end":1},"outcome":"runtime_checked","solver":"trust-full-verifier"
//~| NOTE "line_start":39,"col_start":0,"line_end":41,"col_end":1},"outcome":"runtime_checked","solver":"trust-full-verifier"
//@ revisions: advisory
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//! DYN-ARG-PROVENANCE-1 (2026-10-05; docs/DECISION_QUEUE.md "OD-1" item 14 amendment):
//! OD-1 item 14 refutes a virtual call on a body's ARGUMENT because "the caller
//! chooses the value". A PRIVATE function has no caller outside this crate; when
//! every call site hands that argument a pointer to a concrete value it builds (a
//! closure, a concrete ADT), the adversary item 14 names does not exist and the row
//! keeps its disclosed `runtime_checked` label, exactly as `local_dyn`'s does in
//! `dyn_sealed_or_blanket_trait_stays_runtime_checked.rs`. Measured shape: clean-ck0
//! `nested_replace.rs` `map_children_depth(.., f: &dyn Fn(&Term, u32) -> Term)`.
//! Line 1 pins `map_closure` and `call_local_adt` `runtime_checked`.
//! Controls (`dyn_private_fn_adversarial_values_is_failed.rs`): the same private
//! shape reached by a forwarded trait object, a fn pointer, or an escaping fn item
//! stays `failed`.
pub trait Open {
    fn o(&self) -> u32;
}

pub struct Quiet;

impl Open for Quiet {
    fn o(&self) -> u32 {
        7
    }
}

fn map_closure(f: &dyn Fn(u32) -> u32, x: u32) -> u32 {
    f(x)
}

fn call_local_adt(t: &dyn Open) -> u32 {
    t.o()
}

pub fn use_closures(x: u32) -> u32 {
    let a = map_closure(&|v| v / 2, x);
    let b = map_closure(&|v| v % 3, x);
    a.wrapping_add(b)
}

pub fn use_adt() -> u32 {
    call_local_adt(&Quiet)
}

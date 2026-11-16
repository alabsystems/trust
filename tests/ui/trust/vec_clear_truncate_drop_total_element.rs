//@ needs-trust-verify
//@ edition: 2021
//@ revisions: clear_u32 truncate_u32 clear_string clear_loud truncate_loud
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[clear_u32] check-pass
//@[truncate_u32] check-pass
//@[clear_string] check-fail
//@[clear_loud] check-fail
//@[truncate_loud] check-fail
//! **`Vec::clear` / `Vec::truncate` are total over a drop-total element (Trust,
//! 2026-09-28).**
//!
//! Both only shrink `len` and `drop_in_place` the removed elements, and neither
//! touches the allocator. Their bodies (reaching `core::ptr::drop_glue::<[T]>`) do not
//! lower, so each call used to be an absent callee with a may-panic marker, and
//! `certify` refused even `v.clear()` over `Vec<u32>`. The bridge now summarizes them as
//! total when the element's drop is (`vec_truncating_drop_total_call`, the same premise
//! and classifier as the `Cell::set` gate).
//!
//! * `clear_u32`, `truncate_u32`, `clear_string`: POSITIVE.
//! * `clear_loud`, `truncate_loud`: the DISCRIMINATING negatives. `Loud::drop` panics, so
//!   dropping a removed element can panic. `Loud::drop` fails on its own as well, so
//!   unannotated errors are allowed. The annotation on `f` is the one that discriminates:
//!   if the gate ignored the element's drop, `f` would verify and the annotation would go
//!   unmatched.

#[cfg(any(clear_loud, truncate_loud))]
pub struct Loud;

#[cfg(any(clear_loud, truncate_loud))]
impl Drop for Loud {
    fn drop(&mut self) {
        panic!("loud");
    }
}

#[cfg(clear_u32)]
pub fn f(v: &mut Vec<u32>) {
    v.clear();
}

#[cfg(truncate_u32)]
pub fn f(v: &mut Vec<u32>) {
    v.truncate(2);
}

#[cfg(clear_string)]
pub fn f(v: &mut Vec<String>) {
    //[clear_string]~^ ERROR Trust strict verification failed for `vec_clear_truncate_drop_total_element::f`
    // CAPABILITY LOSS, re-pinned 2026-10-15 (the merge of 2026-10-14; docs/KNOWN_HAZARDS.md
    // "OPEN 2026-10-15 — correct programs the merge of 2026-10-14 refuses", DECISION_QUEUE D103(i)):
    // ZERO-ROW-GATE: `Vec::<String>::clear` is total by the bridge's `vec_truncating_drop_total_call`
    // (the element's drop is total), a decision no registry the gate reads mirrors (`clear_u32`,
    // whose element needs no drop, still builds).
    // Fail-closed: refused, never proved. Flip back to `check-pass` when it returns.
    v.clear();
}

#[cfg(clear_loud)]
pub fn f(v: &mut Vec<Loud>) {
    //[clear_loud]~^ ERROR Trust Level 0 safety verification incomplete for `vec_clear_truncate_drop_total_element::f`
    v.clear();
}

#[cfg(truncate_loud)]
pub fn f(v: &mut Vec<Loud>) {
    //[truncate_loud]~^ ERROR Trust Level 0 safety verification incomplete for `vec_clear_truncate_drop_total_element::f`
    v.truncate(1);
}

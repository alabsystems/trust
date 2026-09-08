//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// F1 Increment B0 — THE CONVERGED LOADED-PTR RULE (adversarial review record,
// docs/design/2026-08-31-f1-value-transport-entry.md): a `Load {ty: Ptr}` of a
// `ty::Ref`-typed lane is admitted with its result LEDGERED — borrow_ptrs +
// frame_interior_ptrs UNCONDITIONALLY (a Load's result region is whatever was
// last stored, which the container does not determine — never interior), plus
// mut_borrow_ptrs iff the lane's declared type is `&mut`. The
// ptr_slot_contents pure forward stays first. Probed refuters, kept in the
// probe suite (they are compile-valid shapes that must stay refused):
// `fn escape<'a>(q: &'a &'a i64) -> &'a i64 { *q }` refuses with
// Return(borrow ptr escapes tail) — the frame class is what closes R2's
// memory-transport false-verify channel — and a loaded RAW pointer keeps the
// Deref(non-scalar pointee) tag (no borrowck warrant).

pub fn double_ref(q: &&i64) -> i64 {
    **q
}

fn main() {
    let x = 5i64;
    let r = &x;
    assert_eq!(double_ref(&r), 5);
}

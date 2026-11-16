//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (Lane A, 2026-09-14): a shared borrow of a STATIC'S ARRAY ELEMENT with a
//! LITERAL in-bounds index lowers as an interior GEP off the static's `GlobalAddr`
//! — the `Index` sibling of the wave-SF field lane — not as a snapshot of the
//! element's VALUE into a stack slot, whose address the tail guard rightly refuses
//! to return. rustc never promotes this shape (the candidate place carries a
//! `Deref`); the reference is `'static` because the STATIC's storage is. Covers
//! both the direct spelling `&D[1]` in a fn and the `&'static`-coercion wrapper
//! `Borrow{Deref{Borrow{Index{Deref{StaticRef}}}}}` a `static` initializer produces
//! (the issue-17718 `static F: &'static usize = &D[0]` shape). The out-of-lane
//! twins — a symbolic index, a non-array base — keep the historical path.

pub static D: [usize; 3] = [1, 2, 3];

// direct: Index{Deref{StaticRef}}
pub fn direct() -> &'static usize {
    &D[1]
}

// wrapper: the &'static coercion shape (issue-17718 `F`)
pub static F: &'static usize = &D[0];

pub fn through_wrapper() -> usize {
    *F + *direct()
}

fn main() {}

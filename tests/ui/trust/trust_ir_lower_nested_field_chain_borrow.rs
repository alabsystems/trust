//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off --crate-type=lib
// wave-MD: `&mut b.a.x` — a DEPTH >= 2 all-struct field chain over a bare
// struct local. Classified as its own `ReborrowTarget::FieldChainOfLocal`
// (the depth-1 lane's gate ORDER is a probe surface per the FS2 standing
// rule, so it stays byte-identical and the chain lane fires only on shapes
// that were NotAPlace before). The emitter applies the depth-1 gates AT
// EVERY LEVEL (registered struct, rustc-authority byte offset,
// `struct_interior_offset_admissible`), sums the offsets into ONE GEP off
// the promoted slot, and joins the same ledger classes (borrow +
// frame-interior, + mut on the mut path). Promotion of the nested base
// rides `snapshotable_aggregate_pointee`'s new TRANSITIVE arm — the leaf
// set is unchanged (scalars only; floats stay out), so a nested all-scalar
// struct round-trips through memory by the same aggregate Store/Load
// argument. Tuples (`ty::Tuple` — no trust-ir layout evidence), boxes,
// enums, and derefs all keep their fail-closed paths (see `tup` below).

pub struct A {
    pub x: i64,
    pub y: i64,
}
pub struct B {
    pub a: A,
}
pub struct C {
    pub b: B,
    pub tag: i64,
}

// Depth 2, mutable: write through the chain address, read back.
pub fn depth2() -> i64 {
    let mut b = B { a: A { x: 1, y: 2 } };
    let r = &mut b.a.x;
    *r = 9;
    b.a.x
}

// Depth 3, non-zero summed offset (c.b.a.y = 0 + 0 + 8).
pub fn depth3() -> i64 {
    let mut c = C { b: B { a: A { x: 1, y: 2 } }, tag: 7 };
    let r = &mut c.b.a.y;
    *r = 11;
    c.b.a.y + c.tag
}

// Shared chain: scalar leaf read through the summed-offset address. (A
// nested-field ASSIGN `local.a.x += ..` is a separate lane and still
// refuses with its own tag — kept out of this body on purpose.)
pub fn shared_depth2() -> i64 {
    let mut local = B { a: A { x: 3, y: 4 } };
    let r = &mut local.a.x;
    *r = 6;
    let p = &local.a.y;
    *p + local.a.x
}

// NEGATIVE — a TUPLE level has no trust-ir layout evidence and must keep
// failing closed; this body must NOT lower.
pub fn tup() -> i64 {
    let mut v = (1i64, 2i64);
    let q = &mut v.0;
    *q = 7;
    v.0 + v.1
}

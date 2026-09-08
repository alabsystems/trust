//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// F1 Increment B1 (rev2, divergence-narrowed): a struct whose ptr-mapped
// fields are all RAW pointers promotes to a memory slot when &mut-collected,
// behind the field-type unpromotable fence (any write to a pointer-typed
// field keeps the base on the Undef-surgery lane — the fence's rev1 tested
// the RHS's shape and MISSED a param-valued rhs, measured). B2 re-admitted
// REF-field structs: the rev1 divergence's root cause was the differential's
// leaf-read probe being VACUOUS for memory-transported aggregates (the
// oracle's GEP+Load field form left ptr_leaves empty), and
// aggregate_ptr_leaf_is_read now conservatively treats ANY stored derived
// value as read — re-borrowing bodies refuse sampling (coverage-only)
// instead of feeding null into a Borrow, and the ex-diverger lowers clean.

pub struct S {
    pub p: *mut i64,
    pub n: u32,
}

pub fn scalar_sibling(mut s: S) -> u32 {
    let t = &mut s.n;
    *t = 9;
    s.n
}

pub fn ptr_field(mut s: S) {
    let t = &mut s.p;
    let _ = t;
}

pub fn addr_write(mut s: S, x: &mut i64) {
    s.p = x;
    let _ = s.n;
}

fn main() {}

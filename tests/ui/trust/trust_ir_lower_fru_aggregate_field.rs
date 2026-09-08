//@ check-pass
//@ compile-flags: --crate-type=lib -Ztrust-ir-lower -Ztrust-verify=off
//@ forbid-output: final Trust-IR module validation failed
// wave-FRU2: a functional-record-update (`S { a, ..base }`) copies each
// OMITTED field from `base` with a plain `ExtractField` — an op that is
// legal IR at an aggregate type, and the same one the destructure path
// emits. The scalar-only gate on that copy was conservatism, and the
// three things it stood in for are checkable directly:
//
//  * a DEGRADED `Ty::Unit` placeholder must still refuse, because copying
//    it hands out a fabricated value for bytes that exist. It is now
//    excluded BY NAME rather than by falling out of "non-scalar" — the
//    distinction the previous comment leaned on this gate to make;
//  * a UNION-LANE field must still refuse, on the standing ledger
//    (`union_lane_ty_transitive`) rather than by proxy;
//  * and the field must SEED, since the aggregate seed below needs a
//    placeholder for every lane. `seed_overwritten_ty` is the seeder that
//    loop itself uses, so asking it here cannot disagree with it.
#[derive(Clone, Copy)]
pub struct Inner {
    pub a: i64,
    pub b: i64,
}

#[derive(Clone, Copy)]
pub struct Outer {
    pub n: i64,
    pub inner: Inner,
    pub arr: [i64; 2],
}

// A STRUCT-typed and an ARRAY-typed omitted field, both copied from base.
pub fn fru_aggregate_fields(base: Outer) -> i64 {
    let o = Outer { n: 9, ..base };
    o.inner.a + o.arr[0]
}

// The same shape written explicitly — it always lowered, and pins that
// this wave changed the OMITTED path only.
pub fn fru_explicit(base: Outer) -> i64 {
    let o = Outer { n: 9, inner: base.inner, arr: base.arr };
    o.n
}

fn main() {}

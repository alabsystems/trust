//@ check-pass
//@ compile-flags: --crate-type=lib -Ztrust-ir-lower -Ztrust-verify=off
//@ forbid-output: final Trust-IR module validation failed
// wave-DRW2: `*r = <aggregate>` through a ledgered `&mut`. The store is
// the same instruction the non-scalar array lane already emits and the
// differential already validated there — `Alloca` + `Store` of an
// aggregate, read back through element ops, Agreed against the MIR oracle
// on a struct with INTERIOR PADDING (wave-NSA).
//
// What the scalar-only gate was standing in for, named and checked
// directly: a DEGRADED `Ty::Unit` placeholder (storing one writes a
// fabricated image over real bytes), a UNION-LANE aggregate (the same,
// one level down), and a shape with no constant image. The first two are
// ledger questions; the third is `seed_overwritten_ty`'s.
//
// The POINTER is not this gate's business and is unchanged: the check
// above it still demands a ledgered `&mut` or an adjudicated field
// pointer, which is what makes the destination a real slot rather than a
// snapshot.
//
// HONEST LIMIT, stated because it would be easy to imply otherwise: the
// DIFFERENTIAL gives no evidence for this shape either way. It refuses to
// sample a body whose pointer parameter is dereferenced ("param 0 (ptr)
// is READ — opaque sampling refused"), and it refuses the pre-existing
// SCALAR store for exactly the same reason. So this widening rests on the
// validator, on the store instruction's own validation under wave-NSA,
// and on the unchanged pointer discipline — not on a comparator verdict.
#[derive(Clone, Copy)]
pub struct Pair(pub u8, pub u32);

pub fn store_aggregate(p: &mut Pair, a: u8, b: u32) -> u32 {
    *p = Pair(a, b);
    p.1
}

// The scalar store this lane always admitted — pins that the widening
// left it alone.
pub fn store_scalar(p: &mut u32, v: u32) -> u32 {
    *p = v;
    *p
}

fn main() {}

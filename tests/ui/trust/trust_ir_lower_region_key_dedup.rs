//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off --crate-type=lib
// The enum-id-collision root-fix (the last of the six full-population
// divergences, wave-full-0831): ADT registration keys erase REGIONS
// unconditionally (`canonical_adt_args`). Two region spellings of ONE
// instantiation — the struct field's `Option<&'static T>` instantiated via
// `field.ty(tcx, args)` vs the ctor expression's region-erased THIR type —
// used to register as TWO enums, and `S::<()>(None)`'s aggregate seed then
// carried field slot `enum.0` while the inserted `None` const was
// `enum.1`: the interpreter's `type_error at bb0` (issue-25700-1::main).
// Regions never affect an ADT's registered shape, so: one instantiation,
// one key. Probe-verified: the divergent body now runs the differential
// and AGREES.

pub struct S<T: 'static>(pub Option<&'static T>);

pub fn build() {
    S::<()>(None);
}

pub fn build_and_read(x: &'static i64) -> bool {
    let s = S::<i64>(Some(x));
    s.0.is_some()
}

// Trust: KNOWN_HAZARDS "a verdict forced from inside a bundle's absent-callee collection
// replaces that bundle's admitted-destructor record". `f` drops a `Box<u8>`, so its
// bundle admits `Box`'s destructor and records it. In the `dyn` revision `f` also calls
// `Sq::area` through `&dyn Shape` on a declared dependency, and C-FLOW forces
// `Sq::area`'s verdict while `f`'s bundle is still collecting its absent callees. That
// nested build cleared the shared record, so `f` read `destructor_adts={}` back and lost
// its drop-glue discharge. Both revisions must now print `f`'s record non-empty.
//
// Re-targeted 2026-10-15 (the merge of 2026-10-14): `Vec<u8>` now extracts as `Ty::Seq`,
// whose drop the Seq drop gate discharges without admitting `Vec`'s destructor, so
// `f`'s record read `destructor_adts={}` in BOTH revisions, nested verdict or not, and the
// forbids below no longer told the hazard apart. `Box<u8>` still admits its destructor
// (`destructor_adts={"alloc::boxed::Box"}`, measured on the merged stage 1), so `f` drops
// a `Box<u8>` instead; the nested `Sq::area` verdict is unchanged.
//@ needs-trust-verify
//@ aux-build:xcrate_shape_dep.rs
//@ revisions: plain dyn
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ compile-flags: -Ztrust-bundle-foreign-crate=xcshape_dep
//@ rustc-env:TRUST_DROP_GATE_DEBUG=1
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: fn=admitted_destructor_record_survives_nested_verdict::f bundled_members=1 destructor_adts={}
//@ forbid-output: fn=admitted_destructor_record_survives_nested_verdict::f bundled_members=2 destructor_adts={}
//@ forbid-output: fn=admitted_destructor_record_survives_nested_verdict::f bundled_members=3 destructor_adts={}
//@ forbid-output: fn=admitted_destructor_record_survives_nested_verdict::f bundled_members=4 destructor_adts={}
extern crate xcshape_dep;

#[cfg(plain)]
pub fn f(v: Box<u8>) -> u32 {
    drop(v);
    3
}

#[cfg(dyn)]
pub fn f(v: Box<u8>) -> u32 {
    use xcshape_dep::Shape;
    let s: &dyn Shape = &xcshape_dep::Sq(3);
    let r = s.area();
    drop(v);
    r
}

//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off -Aprivate_interfaces
//@ edition: 2021
//! Trust (wave-FTR), the NEGATIVE half: the EMPTY tuple stays refused by the tuple-field head
//! test. Kept out of `trust_ir_lower_tuple_field_registration.rs` because a deliberate decline
//! is a compile ERROR under `=strict`, and those positives are worth pinning at strict.
//!
// FAIL-CLOSED, unchanged: the EMPTY tuple stays refused by the head test. That exclusion is
// deliberate and load-bearing rather than an oversight -- the corpus bodies it keeps out are
// `(NoDrop { inner: ManuallyDrop::new(NeedDrop) }, ()).1`, whose real blocker is the UNION
// carrier. Admitting the unit read there would lower the holder and turn one tag into four
// without making a single body clean: a wrong +0 that also makes the census worse.
struct WithUnit {
    u: (),
    v: i64,
}

pub fn unit_field_still_declines(w: &WithUnit) -> i64 {
    let _ = w.u;
    w.v
}


fn main() {}

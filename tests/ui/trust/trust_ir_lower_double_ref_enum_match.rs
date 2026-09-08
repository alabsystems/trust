//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// wave-MR3: `match x` on a DOUBLE shared reference `&&E` (rfc-2005's
// ref-region shape). THIR normalizes BOTH the match-ergonomics arm and the
// explicit `&`-pattern arm to the identical `Deref{Deref{Variant}}`
// nesting (measured on the dump), so the arm strip is uniform: exactly two
// layers under the double peel. The scrutinee side loads the inner `&E`
// pointer ONCE — ledgered by the B0 converged rule (borrow_ptrs +
// unconditional frame class; shared, so never mut) — and the discriminant
// read plus every by-ref payload GEP base off the INNER pointer. Shared at
// BOTH layers only, matching the single-ref lane's contract; the opaque
// lane keeps its single-layer strip (a double-ref opaque enum stays
// fail-closed).

pub fn foo(x: &&Option<u32>) -> u32 {
    match x {
        Some(r) => *r,
        &None => panic!(),
    }
}

// Discriminant-only arms, both spellings.
pub enum E3 {
    A,
    B(i64),
    C,
}
pub fn tag(x: &&E3) -> i64 {
    match x {
        E3::A => 1,
        E3::B(v) => *v,
        E3::C => 3,
    }
}

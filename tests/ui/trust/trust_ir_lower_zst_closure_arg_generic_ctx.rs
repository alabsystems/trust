//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-ZG): a capture-free closure literal passed as a call argument
//! INSIDE A GENERIC FUNCTION lowers as the oracle's `(Unit, PhantomData)`
//! spelling. The wave-ZC lane always admitted the monomorphic case; the
//! generic enclosing context made `is_drop_free_zst`'s layout query
//! unavailable (`layout_query_is_reentrant_safe` refuses a closure type
//! carrying the parent's generics), and the lane declined a fact its own
//! G1-G4 gates had already proved twice over. The structural fallback covers
//! exactly the query-unavailable case; a query that answers "no" still
//! declines.

fn inside<F: Fn() -> u64>(c: F) -> u64 {
    c()
}

fn outside<A, B>(x: u64) -> u64 {
    inside(|| 41) + x
}

fn main() {
    assert_eq!(outside::<u8, u16>(1), 42);
}

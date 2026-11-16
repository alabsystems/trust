//@ revisions: plain debuginfo
//@ needs-trust-verify
//@ edition: 2021
//@[plain] compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@[debuginfo] compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib -Cdebuginfo=2
//@ check-pass
//@ dont-check-compiler-stderr
//! A loop clause name binds the local its exact HIR binding resolved to at the
//! loop header (`resolve_loop_clause_source_locals`), never a local that merely
//! carries the same debug name. A same-named binding in a sibling block after the
//! loop used to make `i` ambiguous at `-Cdebuginfo>=1` (two `i` rows), refusing a
//! true invariant; the verdict must not depend on the debuginfo level.
pub fn f(n: u8) -> u8 {
    let mut i: u8 = 0;
    while i < n
        invariant i <= n
    {
        i += 1;
    }
    {
        let i: u8 = 7;
        std::hint::black_box(i);
    }
    i
}

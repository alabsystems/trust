//! A fat-pointer payload read out of an ENUM and then used BY VALUE compiles,
//! and computes the right answer.
//!
//! Regression pin for the refusal that stopped the stage1 `library/std` build at
//! `memchr`:
//!
//!     error: [TCG-MIR-UNSUPPORTED] ... memory leaf type is a fat pointer
//!            (ScalarPair {data,len}), not a single scalar: &[u8]
//!
//! raised for `<Option<&[u8]> as Try>::branch` — the `?` operator on an `Option`
//! whose payload is a fat pointer. The MIR shape is
//!
//!     _3 = copy ((_1 as Some).0: &[u8]);   // read a fat leaf out of an enum
//!     _0 = W::<'_> { s: copy _3 };         // ... and use it BY VALUE
//!
//! `lower_memory_fat_leaf_use` loaded both lanes correctly and then had nowhere
//! to put them: a slice destination wanted a `{data,len}` slot, and
//! `compute_memory_backed_locals`'s `(0d-slice)` rule REFUSES a slot to any local
//! that flows by value — a refusal that is load-bearing, because a slot passed as
//! a value operand is mis-read. So the local has to stay scalarized, and a
//! scalarized fat pointer is a two-lane binding, which the `&dyn` half already
//! had and the slice half did not.
//!
//! The cases below are the bisection set that located it. The first five
//! compiled before the fix and must keep compiling; the last four did not.
//!
//! This test RUNS the result rather than only compiling it: the whole hazard
//! class here is a TRUNCATED fat pointer (a data half whose length was dropped),
//! and a length that survives the round trip is the thing worth asserting.

//@ needs-trust-ir-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, run, rustc};

fn main() {
    rfs::write(
        "fatleaf.rs",
        r#"
pub struct W<'a> { pub s: &'a [u8] }
pub enum E<'a> { A(&'a [u8]), B(u64) }
pub enum F<'a> { A(&'a [u8]), B(u64) }

// --- shapes that already worked; they must not regress ---
pub struct A2<'a> { s: &'a [u8] }
pub struct B2<'a> { s: &'a [u8] }
#[inline(never)] pub fn struct_to_struct(a: A2<'_>) -> B2<'_> { B2 { s: a.s } }
#[inline(never)] pub fn construct_some(s: &[u8]) -> Option<&[u8]> { Some(s) }
#[inline(never)] pub fn destructure_len(x: Option<&[u8]>) -> usize {
    match x { Some(s) => s.len(), None => 0 }
}
#[inline(never)] pub fn both_niche_variants(b: bool) -> Option<&'static [u8]> {
    if b { Some(b"xyz") } else { None }
}
#[inline(never)] pub fn struct_to_enum(w: W<'_>, b: bool) -> Option<&[u8]> {
    if b { Some(w.s) } else { None }
}

// --- the shapes that FAILED: an enum-sourced fat leaf used by value ---
#[inline(never)] pub fn enum_to_struct(x: Option<&[u8]>) -> W<'_> {
    match x { Some(s) => W { s }, None => W { s: b"" } }
}
#[inline(never)] pub fn enum_to_enum(x: E<'_>) -> F<'_> {
    match x { E::A(s) => F::A(s), E::B(n) => F::B(n) }
}
// `?` on a FAT Option — the exact `Try::branch` monomorphization memchr needs.
#[inline(never)] pub fn question_mark(x: Option<&[u8]>) -> Option<usize> {
    let s = x?;
    Some(s.len())
}

fn main() {
    let hay: &[u8] = b"hello world";

    // The length must survive every round trip. A truncated fat pointer is the
    // failure mode this whole lane exists to prevent, so assert the LENGTH, not
    // merely that the program ran.
    assert_eq!(struct_to_struct(A2 { s: hay }).s.len(), 11);
    assert_eq!(construct_some(hay).unwrap().len(), 11);
    assert_eq!(destructure_len(Some(hay)), 11);
    assert_eq!(both_niche_variants(true).unwrap().len(), 3);
    assert!(both_niche_variants(false).is_none());
    assert_eq!(struct_to_enum(W { s: hay }, true).unwrap().len(), 11);
    assert!(struct_to_enum(W { s: hay }, false).is_none());

    assert_eq!(enum_to_struct(Some(hay)).s.len(), 11);
    assert_eq!(enum_to_struct(None).s.len(), 0);
    match enum_to_enum(E::A(hay)) { F::A(s) => assert_eq!(s.len(), 11), F::B(_) => panic!() }
    match enum_to_enum(E::B(7)) { F::B(n) => assert_eq!(n, 7), F::A(_) => panic!() }
    assert_eq!(question_mark(Some(hay)), Some(11));
    assert_eq!(question_mark(None), None);

    // And the CONTENTS, so a data half that survived while pointing elsewhere
    // cannot pass either.
    assert_eq!(enum_to_struct(Some(hay)).s, b"hello world");

    println!("fat-leaf round trips ok");
}
"#,
    );

    rustc()
        .input("fatleaf.rs")
        .crate_type("bin")
        .arg("-Zcodegen-backend=trust-ir-cg")
        // Codegen axis only: the certificate lane is a separate axis (like
        // `-Ztrust-verify=off` above). AArch64 pair opcodes have no checker-accepted
        // certificate yet, so leaving proofs on would refuse every compile here with
        // [TCG-PROOF-465] regardless of what this test measures.
        .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
        // The verifier is a separate axis; this test is about codegen alone.
        .arg("-Ztrust-verify=off")
        .arg("-Cdebuginfo=0")
        .run();

    run("fatleaf").assert_stdout_contains("fat-leaf round trips ok");
}

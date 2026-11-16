//@ revisions: forgot covered
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@[forgot] rustc-env:TRUST_SPAWN_CENSUS_TEST_FAULT=forget-coverage
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[covered] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census, self-audit check 2 (design §5.6): TrustVerify walks the CODEGEN
//! body (every call, drop, unsize, reification, closure cast and panic) and
//! refuses as UNKNOWN anything the census did not cover where it came from
//! (this body; a local body the MIR inliner inlined, at that instance). Under
//! `forgot`, a TEST-ONLY fault (`TRUST_SPAWN_CENSUS_TEST_FAULT=forget-coverage`)
//! makes the census record no panic as covered, so the bounds check of `first`
//! and the overflow check of `add` must each be refused by check 2. Under
//! `covered`, nothing here can reach a spawn and no row appears.

#![allow(dead_code)]

pub fn first(v: &[u8]) -> u8 { v[0] } //[forgot]~ NOTE not enumerated (no spawn was found): the codegen MIR of this body mentions

pub fn add(a: u8, b: u8) -> u8 { a + b } //[forgot]~ NOTE not enumerated (no spawn was found): the codegen MIR of this body mentions

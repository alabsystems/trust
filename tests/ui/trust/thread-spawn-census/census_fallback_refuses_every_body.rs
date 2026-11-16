//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ rustc-env:TRUST_SPAWN_CENSUS_TEST_FAULT=defect
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Spawn census, self-audit check 1 (design §5.6): a malformed fact, or a
//! certificate the independent checker rejects, makes the engine refuse every
//! node UNKNOWN, and every row says so. A TEST-ONLY fault
//! (`TRUST_SPAWN_CENSUS_TEST_FAULT=defect`) adds one malformed fact (an adapter
//! APPROX edge): even a body that calls nothing is refused, with the reason.

#![allow(dead_code)]

pub fn nothing() {} //~ NOTE the spawn census refused every body as UNKNOWN: its graph or certificate was rejected

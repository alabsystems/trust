//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ compile-flags: -Ztrust-spawn-census-shadow=check
//@ rustc-env:TRUST_SPAWN_CENSUS_TEST_FAULT=shadow-forge-quiet
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Spawn census, plan step P4 review: `-Ztrust-spawn-census-shadow=check` fails the build on an
//! invariant violation, end to end. A TEST-ONLY fault
//! (`TRUST_SPAWN_CENSUS_TEST_FAULT=shadow-forge-quiet`) forges every trust-ir answer to QUIET,
//! which is a fail-open beside the MIR lane's SPAWNS for `launch` (and agrees with its QUIET
//! elsewhere). The fault touches only the shadow report; the MIR lane ignores the value.
//@ regex-error-pattern:(?m)^trust-spawn-census-shadow: body `launch` mir=SPAWNS trust-ir=QUIET fail-open gaps=-$

#![allow(dead_code)]

pub fn launch() {
    let _handle = std::thread::spawn(|| {});
}

pub fn nothing() {}

//~? ERROR the spawn census's trust-ir shadow lane violates its invariant on 1 body: `launch` (fail-open)

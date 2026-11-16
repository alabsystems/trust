//@ revisions: report check
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@[report] compile-flags: -Ztrust-spawn-census-shadow=report
//@[check] compile-flags: -Ztrust-spawn-census-shadow=check
//@ rustc-env:TRUST_SPAWN_CENSUS_TEST_FAULT=defect
//@[report] check-pass
//@[check] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output:violates its invariant
//! Spawn census, plan step P4: when the MIR lane's census falls back (here the TEST-ONLY fault of
//! `census_fallback_refuses_every_body.rs`), every MIR verdict is its fallback UNKNOWN, so the
//! shadow differential compares nothing: each body is `mir-fell-back`, never a fail-open, and the
//! trust-ir lane's own answer (QUIET for a body that calls nothing) is still printed. A comparison
//! that did not run is not a pass: `check` fails the crate.
//@ regex-error-pattern:(?m)^trust-spawn-census-shadow: crate `trust_ir_shadow_lane_mir_fallback` mir lane fell back: .+$
//@ regex-error-pattern:(?m)^trust-spawn-census-shadow: body `nothing` mir=UNKNOWN trust-ir=QUIET mir-fell-back gaps=-$
//@ regex-error-pattern:(?m)^trust-spawn-census-shadow: crate `trust_ir_shadow_lane_mir_fallback` bodies=1 equal=0 trust-ir-unknown=0 differs=0 fail-open=0 mir-quiet-claim=0 mir-not-walked=0 mir-fell-back=1 decided=0 residue=0$

#![allow(dead_code)]

pub fn nothing() {}

//[check]~? ERROR the spawn census's trust-ir shadow lane compared nothing on 1 body: the MIR lane's census fell back

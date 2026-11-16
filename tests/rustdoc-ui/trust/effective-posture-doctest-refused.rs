// Trust: `trustdoc --test` refuses, before collecting a single doctest, a posture whose
// EFFECTIVE verification is on (ay's committed posture with no off-switch after it) and an
// evidence control that survives the off-switch (a TrustIR artifact sink). The doctests of
// a refused invocation are never compiled, so no canonical compile can inherit either.
//
//@ revisions: ay-left-on ir-dump
//@ compile-flags: --test --test-args=--test-threads=1
//@[ay-left-on] compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Ztrust-verify-level=2
//@[ay-left-on] compile-flags: -Ztrust-verify-profile=unix_hardened
//@[ay-left-on] compile-flags: -Ztrust-verify-include-dependencies=yes -Ztrust-ir-lower=strict
//@[ir-dump] compile-flags: -Ztrust-verify=on -Ztrust-verify=off
//@[ir-dump] compile-flags: -Ztrust-dump=ir:{{build-base}}/trust/no-doctest-ir-dump

/// ```
/// assert_eq!(2 + 2, 4);
/// ```
pub fn documented() {}

//[ay-left-on]~? RAW EmbeddedNoOfficialEvidence compiler frontend rejects semantic, evidence, or backend control `-Ztrust-verify`
//[ir-dump]~? RAW EmbeddedNoOfficialEvidence compiler frontend rejects semantic, evidence, or backend control `-Ztrust-dump`

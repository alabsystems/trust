// Trust: what trustdoc, an evidence-deauthorized frontend, still refuses once it decides on
// the EFFECTIVE configuration. `ay-left-on` and `off-then-on` demand verification (the last
// explicit `-Ztrust-verify` is `on`) from a frontend that cannot verify. Every other
// revision keeps the effective off-switch but adds an evidence control whose effect does
// not depend on verification running (an artifact sink, a session identity, a certified
// monitor, a trust-cg codegen control) or an adversarial/measurement control: a frontend
// that produces no evidence can neither honour those nor silently drop them.
//
//@ revisions: ay-left-on off-then-on ir-dump body-census session test-monitor
//@ revisions: cg-output-gate sat-perturb witness
//@[ay-left-on] compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Ztrust-verify-level=2
//@[ay-left-on] compile-flags: -Ztrust-verify-profile=unix_hardened
//@[ay-left-on] compile-flags: -Ztrust-verify-include-dependencies=yes -Ztrust-ir-lower=strict
//@[off-then-on] compile-flags: -Ztrust-verify=off -Ztrust-verify=on
//@[ir-dump] compile-flags: -Ztrust-verify=on -Ztrust-verify=off
//@[ir-dump] compile-flags: -Ztrust-dump=ir:{{build-base}}/trust/no-ir-dump
//@[body-census] compile-flags: -Ztrust-verify=on -Ztrust-verify=off
//@[body-census] compile-flags: -Ztrust-body-census={{build-base}}/trust/no-census.jsonl
//@[session] compile-flags: -Ztrust-verify=on -Ztrust-verify=off
//@[session] compile-flags: -Ztrust-verify-session=posture-session
//@[test-monitor] compile-flags: -Ztrust-verify=on -Ztrust-verify=off -Ztrust-targo-test-monitor
//@[cg-output-gate] compile-flags: -Ztrust-verify=on -Ztrust-verify=off
//@[cg-output-gate] compile-flags: -Ztrust-cg-output-gate=off
//@[sat-perturb] compile-flags: -Ztrust-verify=on -Ztrust-verify=off
//@[sat-perturb] compile-flags: -Ztrust-sat-perturb=enum-reshape
//@[witness] compile-flags: -Ztrust-verify=on -Ztrust-verify=off -Ztrust-witness=off

/// One.
pub fn one() -> u32 {
    1
}

//[ay-left-on]~? RAW EmbeddedNoOfficialEvidence compiler frontend rejects semantic, evidence, or backend control `-Ztrust-verify`
//[off-then-on]~? RAW EmbeddedNoOfficialEvidence compiler frontend rejects semantic, evidence, or backend control `-Ztrust-verify`
//[ir-dump]~? RAW EmbeddedNoOfficialEvidence compiler frontend rejects semantic, evidence, or backend control `-Ztrust-dump`
//[body-census]~? RAW EmbeddedNoOfficialEvidence compiler frontend rejects semantic, evidence, or backend control `-Ztrust-body-census`
//[session]~? RAW EmbeddedNoOfficialEvidence compiler frontend rejects semantic, evidence, or backend control `-Ztrust-verify-session`
//[test-monitor]~? RAW EmbeddedNoOfficialEvidence compiler frontend rejects semantic, evidence, or backend control `-Ztrust-targo-test-monitor`
//[cg-output-gate]~? RAW EmbeddedNoOfficialEvidence compiler frontend rejects semantic, evidence, or backend control `-Ztrust-cg-output-gate`
//[sat-perturb]~? RAW EmbeddedNoOfficialEvidence compiler frontend rejects semantic, evidence, or backend control `-Ztrust-sat-perturb`
//[witness]~? RAW EmbeddedNoOfficialEvidence compiler frontend rejects semantic, evidence, or backend control `-Ztrust-witness`

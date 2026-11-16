//! The structured-multiplier-proof gate (G16): kernel-checked, axiom-free proof
//! that ay's shift-and-add ARRAY MULTIPLIER construction is (1) equivalent to a
//! separately-stated reference multiplier (machine gates == IR gates, by
//! induction over the width) and (2) built on a ripple adder that computes the
//! genuine integer sum (the adder value law, by induction).
//!
//! `proofs/codegen-equivalence/g16_multiplier_equivalence.lean` proves these in
//! clean's `List Bool` model with ZERO domain-specific axioms. This gate asserts
//! BOTH that the file kernel-checks (`clean check`) AND that the headline
//! theorems `G16Mul.mul_equiv` / `G16Mul.addval` are REAL Theorems whose
//! transitive axiom closure is ⊆ FOUNDATIONAL (propext / Quot.sound /
//! Classical.choice) — i.e. NO sorry / admit / axiom / postulate — mirroring the
//! `checkRefutes_sound` empty-domain-axiom precedent in clean's
//! `tests_bv_blast_reflection.rs`. The empty-axiom evidence is the `clean
//! export-cert --json-report`'s `all_axiom_closures_foundational_only` flag plus
//! the per-theorem `exported_theorems` list.
//!
//! HONESTY (residual): this gate proves the STRUCTURED THEOREM is real and
//! axiom-free. It does NOT (yet) assert that the live trust-cg gate emits
//! `Proven{KernelRecheckable}` for a wide `Mul` via this theorem: the runtime
//! [PROVED] path uses the SAT-refutation reflection (`certify_unsat_by_reflection`),
//! and instantiating the structured theorem at the gate would require a
//! Formula <-> List-Bool reconstruction bridge that does not exist for any op
//! yet (the g16 layer is standalone corroboration). Wide `Mul` therefore stays
//! [VALIDATED] (the `MAX_RECHECKABLE_MUL_WIDTH` guard in `verify_output` holds).
//! See the proof-rung report for the precise wiring residual.
//!
//! This is the BINARY half. The same headline theorems
//! (`clean_proof_obligations::G16_HEADLINE_THEOREMS`) are required IN PROCESS
//! by `trust_integration_tests::clean_proof_obligations`, as real theorems of
//! the file with a certified (foundational-only) closure, through the Clean
//! kernel linked into this crate; nothing there is discovered and nothing
//! skips. This file checks that a `clean` built from the pinned
//! `first-party/clean` agrees. It is `#[ignore]`d and runs only under
//! `slow.clean-binary-proof-gates`, which builds that `clean` and names it in
//! `TRUST_CLEAN_BIN`; selected without it, it panics with the build recipe.

use std::process::Command;

use trust_integration_tests::clean_proof_obligations::{
    G16_HEADLINE_THEOREMS, G16_MULTIPLIER_PROOF, repo_path,
};
use trust_integration_tests::clean_test_support::require_clean_bin;

#[test]
#[ignore = "needs TRUST_CLEAN_BIN (slow.clean-binary-proof-gates)"]
fn structured_multiplier_proof_gate() {
    let proof = repo_path(G16_MULTIPLIER_PROOF)
        .canonicalize()
        .expect("g16_multiplier_equivalence.lean must exist");

    let bin = require_clean_bin();

    // (1) The whole file kernel-checks with ZERO sorry-axioms.
    let check = Command::new(&bin)
        .arg("check")
        .arg("--json")
        .arg(&proof)
        .output()
        .expect("run clean check --json");
    let check_out = String::from_utf8_lossy(&check.stdout);
    assert!(check.status.success(), "clean check must succeed:\n{check_out}");
    let check_json: serde_json::Value =
        serde_json::from_str(&check_out).expect("clean check --json must emit JSON");
    assert_eq!(check_json["status"], "pass", "all declarations must kernel-check");
    assert_eq!(
        check_json["trust_summary"]["sorry_axioms"], 0,
        "the multiplier proof must use ZERO sorry-axioms; got {}",
        check_json["trust_summary"]["sorry_axioms"]
    );

    // (2) The headline theorems are REAL Theorems whose axiom closure is ⊆
    // FOUNDATIONAL — via the export-cert audit's per-theorem axiom-closure report.
    let report_path = std::env::temp_dir().join("g16mul_gate_report.json");
    let bundle_path = std::env::temp_dir().join("g16mul_gate.cleancert");
    let cert = Command::new(&bin)
        .arg("export-cert")
        .arg(&proof)
        .arg("--out")
        .arg(&bundle_path)
        .arg("--json-report")
        .arg(&report_path)
        .output()
        .expect("run clean export-cert");
    // export-cert may exit non-zero only on a hard error; the axiom audit is in
    // the JSON report regardless of the literal-form cert-replay quirks on the
    // pure-Nat helper lemmas (which still kernel-check under `clean check`).
    let report_text =
        std::fs::read_to_string(&report_path).expect("export-cert must write a JSON report");
    let report: serde_json::Value =
        serde_json::from_str(&report_text).expect("export-cert report must be JSON");

    assert_eq!(
        report["all_axiom_closures_foundational_only"],
        true,
        "every exported theorem's axiom closure must be ⊆ FOUNDATIONAL (no domain axioms); \
         export-cert stdout:\n{}",
        String::from_utf8_lossy(&cert.stdout)
    );
    assert_eq!(
        report["sorry_axioms_observed"], 0,
        "no sorry-axioms may be observed by the cert exporter"
    );

    let exported = report["exported_theorems"]
        .as_array()
        .expect("exported_theorems array")
        .iter()
        .filter_map(|v| v.as_str())
        .collect::<Vec<_>>();
    for needed in G16_HEADLINE_THEOREMS {
        assert!(
            exported.contains(needed),
            "headline theorem {needed} must export with a FOUNDATIONAL-only axiom closure; \
             exported = {exported:?}"
        );
    }

    eprintln!(
        "STRUCTURED-MULTIPLIER-PROOF GATE GREEN: g16_multiplier_equivalence.lean kernel-checks \
         (0 sorry-axioms) and {} headline theorems (incl. mul_equiv, addval) are REAL Theorems \
         with axiom closure ⊆ FOUNDATIONAL ({})",
        G16_HEADLINE_THEOREMS.len(),
        bin.display()
    );
}

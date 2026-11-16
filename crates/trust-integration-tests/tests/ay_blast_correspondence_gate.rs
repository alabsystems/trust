//! The ay-blast correspondence gate: pins the obligations standing between the
//! structured multiplier theorem and a wide-`Mul` `[PROVED]` verdict, and
//! COUPLES them to the width cap so code and proof state cannot drift.
//!
//! # What is already proved
//!
//! `proofs/codegen-equivalence/g16_multiplier_equivalence.lean` proves the MODEL
//! correct, axiom-free: `mul_equiv` (machine-gate array multiplier == the
//! separately-stated IR one) and `addval` (its ripple adder computes the genuine
//! integer sum). Both are width-GENERIC, so applying them at live gate width is
//! a plain instantiation, not a new proof — measured: `mul_equiv` at width 32
//! kernel-checks in ~3.5s.
//!
//! # The two obligations
//!
//! Stating the gap directly against `mul_m` asked a reader to accept by
//! inspection that two STRUCTURALLY DIFFERENT algorithms agree — ay accumulates
//! PRE-SHIFTED rows left-associated, `mul_m` is Horner-recursive
//! right-associated. `mul_ay` now mirrors ay's loop line by line, splitting that
//! into two obligations of different KIND:
//!
//!   1. `AyBlastAgrees` — ay's Rust emits `mul_ay`. CANNOT be discharged inside
//!      clean (the encoder is Rust), so it stays an inspection obligation, but
//!      it is now a structural comparison against the loop rather than an
//!      algebraic argument. Proof name when it lands: `DISCHARGE_THEOREM`.
//!   2. `AyModelMatches` — `mul_ay = mul_m`. Pure mathematics, entirely inside
//!      clean, closable by anyone with no reference to ay. Proof name:
//!      `MODEL_MATCH_THEOREM`.
//!
//! Obligation 2 is additionally verified EXHAUSTIVELY at widths 1..5 (`exh1`..
//! `exh5`): every pair of n-bit words, 1_364 pairs, covering all carry patterns,
//! decided by kernel computation rather than asserted. Width 6 (4_096 pairs) was
//! verified too and left out only for cost (~23s vs ~8s). That range matters —
//! `MAX_RECHECKABLE_MUL_WIDTH = 8` is the widest multiply the live gate
//! re-checks at all. `exh_negative_control` pins that the harness is
//! discriminating: pointed at the wrong function it reports false.
//!
//! `toNat_inj` — two equal-length words with equal value are equal — is now
//! proved from the bare prelude (via a parity extractor and 2m=2n cancellation,
//! neither of which clean's environment exposes). That was the piece obligation
//! 2's general proof was blocked on; what remains of it is the `wadd` value law
//! in the form associativity needs, plus the `dropLast` interaction.
//!
//! OBLIGATION 1 is now MACHINE-CHECKED, though still not kernel-proved — see
//! `crates/trust-cg-bridge/tests/ay_blast_agrees_differential.rs`, which
//! evaluates the gates ay ACTUALLY emits for `BvExpr::Mul` and compares them
//! against a transcription of `mul_ay`: EXHAUSTIVELY at widths 1..=8 — i.e.
//! every width up to `MAX_RECHECKABLE_MUL_WIDTH` itself — and by structured plus
//! pseudo-random SAMPLING at 16, 32 and 64, where 32 is the live gate width.
//! The evaluator's own gate semantics are validated against ay's emitted CNF.
//! That is evidence, not a proof for all widths, so the cap below stays in
//! force.
//!
//! OBLIGATION 2 IS DISCHARGED. All three supporting lemmas are proved —
//! (a) `wadd_assoc`, (b) `shl1_wadd`, (c) `accRows_lemma` — and
//! `mul_ay_matches_model` closes `AyModelMatches` outright. Only obligation 1
//! remains, and it is the one clean can never prove: ay's encoder is Rust.
//!
//! Both were needed and neither implied the other. `blast_equals_ir` and
//! `blast_value_eq` are proved FROM the pair, so discharging them is all that
//! remains. Obligation 2 is witnessed true on concrete inputs (`ay_w1`/`ay_w3`,
//! `rfl`, so the kernel computes both multipliers and compares words); its proof
//! route needs ripple-adder associativity via the value law plus `toNat`
//! injectivity, and `shlk_shl1` is its first brick.
//!
//! # The coupling, which is the point
//!
//! The obligations being OPEN and `MAX_RECHECKABLE_MUL_WIDTH = 8` being IN FORCE
//! are the same fact — the cap exists only because a wide `Mul` has no
//! structured theorem to cite, and its per-instance SAT refutation is
//! intractable (~16x steps per +2 bits: width 2 -> 234, 4 -> 5_210, 6 -> 88_250,
//! 8 -> ~2.0M). This gate asserts them together, reading the cap out of the
//! bridge source rather than copying it:
//!
//!   * lifting the cap while either obligation is open FAILS the gate — that
//!     would claim a kernel grade on an inspection-level assumption;
//!   * discharging BOTH also fails it, deliberately, with instructions to raise
//!     the cap and rewrite this gate for the new state.
//!
//! A failure here is therefore never flaky; it always means the proof state and
//! the code disagree about what is claimed.
//!
//! # Two halves
//!
//! The theorem names, the obligation-2 non-regression and the cap coupling are
//! asserted IN PROCESS by `trust_integration_tests::clean_proof_obligations`
//! (`fast.clean-proof-obligations`, and the push lane when `proofs/` or the
//! bridge source moves), through the Clean kernel linked into this crate:
//! nothing there is discovered and nothing skips. This file is the BINARY
//! cross-check: a `clean` built from the pinned `first-party/clean` must reach
//! the same verdicts through `clean check` and `clean export-cert`, reading the
//! same constants. It is `#[ignore]`d and runs only under
//! `slow.clean-binary-proof-gates`, which builds that `clean` and names it in
//! `TRUST_CLEAN_BIN`; selected without it, it panics with the build recipe.

use std::process::Command;

use trust_integration_tests::clean_proof_obligations::{
    DISCHARGE_THEOREM, G16_MULTIPLIER_PROOF, G16_REDUCTION_THEOREMS, MODEL_MATCH_THEOREM,
    declared_mul_width_cap, mul_width_coupling_violation, repo_path,
};
use trust_integration_tests::clean_test_support::require_clean_bin;

#[test]
#[ignore = "needs TRUST_CLEAN_BIN (slow.clean-binary-proof-gates)"]
fn ay_blast_correspondence_gate() {
    let proof = repo_path(G16_MULTIPLIER_PROOF);
    assert!(proof.exists(), "g16_multiplier_equivalence.lean must exist at {}", proof.display());

    let bin = require_clean_bin();

    // (1) The file kernel-checks with no sorry-axioms.
    let check = Command::new(&bin)
        .arg("check")
        .arg("--json")
        .arg(&proof)
        .output()
        .expect("`clean check` must run");
    let check_out = String::from_utf8_lossy(&check.stdout);
    assert!(
        check.status.success(),
        "`clean check` must accept the multiplier proof.\nstdout: {check_out}\nstderr: {}",
        String::from_utf8_lossy(&check.stderr)
    );
    let report: serde_json::Value =
        serde_json::from_str(&check_out).expect("`clean check --json` must emit JSON");
    assert_eq!(
        report["trust_summary"]["sorry_axioms"].as_u64(),
        Some(0),
        "the correspondence reduction must carry NO sorry-axioms; report: {report}"
    );

    // (2) The reduction is real, exported and axiom-free.
    let tmp = std::env::temp_dir().join("trust_ay_blast_correspondence");
    let json = tmp.with_extension("json");
    let export = Command::new(&bin)
        .arg("export-cert")
        .arg("--out")
        .arg(tmp.with_extension("cleancert"))
        .arg("--json-report")
        .arg(&json)
        .arg(&proof)
        .output()
        .expect("`clean export-cert` must run");
    assert!(
        export.status.success(),
        "`clean export-cert` must succeed.\nstderr: {}",
        String::from_utf8_lossy(&export.stderr)
    );
    let cert: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&json).expect("export report must exist"))
            .expect("export report must be JSON");
    assert_eq!(
        cert["all_axiom_closures_foundational_only"].as_bool(),
        Some(true),
        "every exported theorem must have a FOUNDATIONAL-only axiom closure; report: {cert}"
    );

    let exported: Vec<String> = cert["exported_theorems"]
        .as_array()
        .expect("exported_theorems must be an array")
        .iter()
        .map(|t| {
            t.as_str().map(str::to_string).unwrap_or_else(|| {
                t["name"].as_str().expect("exported theorem must have a name").to_string()
            })
        })
        .collect();
    let has = |n: &str| exported.iter().any(|t| t == n || t.ends_with(n));

    for required in G16_REDUCTION_THEOREMS {
        assert!(
            has(required),
            "{required} must be an EXPORTED, axiom-free Theorem — the reduction from the \
             correspondence to the headline results is what makes the remaining gap a SINGLE \
             obligation; exported: {exported:?}"
        );
    }

    // (3) THE COUPLING, by the same rule the in-process half applies
    // (`mul_width_coupling_violation`): obligation 2 must stay discharged,
    // discharging both marks the transition, and otherwise the cap must stay
    // in force. The cap is read out of the bridge source, not copied.
    if let Some(violation) = mul_width_coupling_violation(has, declared_mul_width_cap()) {
        panic!("{violation}\nexported: {exported:?}");
    }
    if !has(DISCHARGE_THEOREM) {
        eprintln!(
            "NOTE: obligation 2 (mul_ay = mul_m) is CLOSED by {MODEL_MATCH_THEOREM}. The cap \
             stays in force because {DISCHARGE_THEOREM} (ay's encoder emits mul_ay) remains \
             open — that one is an inspection obligation and cannot be discharged inside clean."
        );
    }
}

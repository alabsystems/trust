//! The bounded-corner-multiply proof gate: kernel-checked, axiom-free proof of
//! the INTERVAL ARITHMETIC law that the i128 `Mul` overflow suppression rests on.
//!
//! `crates/trust-vcgen/src/generate/overflow_vc.rs` mints NO overflow obligation
//! for a signed 128-bit `a * b` when both operands carry finite constant boxes on
//! every reaching path and all four CORNER products fit i128
//! (`v2_signed_mul_provably_cannot_overflow`). Signed 128-bit Mul is nonlinear
//! and the native lane declines it, so that suppression rests on an argument
//! decided in Rust: the extremes of a product over a box are attained at its
//! corners.
//!
//! `proofs/trust-soundness/i128_mul_corner_bounds.lean` proves that argument in
//! clean with ZERO domain-specific axioms. This gate asserts BOTH that the file
//! kernel-checks (`clean check`) AND that the headline theorems
//! `CornerBox.mul_box_upper` / `CornerBox.mul_box_lower` are REAL Theorems whose
//! transitive axiom closure is ⊆ FOUNDATIONAL (propext / Quot.sound /
//! Classical.choice) — i.e. NO sorry / admit / axiom / postulate. The evidence is
//! `clean export-cert --json-report`'s `all_axiom_closures_foundational_only`
//! flag plus the per-theorem `exported_theorems` list, mirroring
//! `structured_multiplier_proof_gate.rs`.
//!
//! HONESTY (residual): this gate proves the INTERVAL THEOREM is real and
//! axiom-free. It does NOT assert that the live vcgen path discharges the
//! multiply THROUGH this theorem — the suppression is still decided by the Rust
//! pre-pass, and nothing in the verdict path consults the proof. Instantiating a
//! structured theorem at the gate would require a Formula <-> model
//! reconstruction bridge that does not exist for any op yet; the identical note
//! in `structured_multiplier_proof_gate.rs` is why wide `Mul` stays [VALIDATED].
//! What this file buys is that the interval argument is no longer Rust-only.
//!
//! Opt-in: skips with a notice when no `clean` checker is discoverable.

use std::path::Path;
use std::process::Command;

use trust_integration_tests::clean_test_support::clean_checker_path;

/// The theorems that MUST be present, real Theorems, and axiom-free.
///
/// The two `mul_box_*` entries are the law the suppression rests on. The
/// witnesses are included deliberately: without them the development could
/// degenerate into statements about a multiplication that computes to nothing,
/// and the gate would still pass.
const REQUIRED_FOUNDATIONAL_THEOREMS: &[&str] = &[
    "CornerBox.mul_box_upper",
    "CornerBox.mul_box_lower",
    "CornerBox.imul_comm",
    "CornerBox.corner_witness_products",
    "CornerBox.corner_witness_negative",
];

#[test]
fn i128_corner_bounds_proof_gate() {
    let proof = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../proofs/trust-soundness/i128_mul_corner_bounds.lean")
        .canonicalize()
        .expect("i128_mul_corner_bounds.lean must exist");

    let Some(bin) = clean_checker_path() else {
        eprintln!(
            "NOTICE: no `clean` checker discoverable — skipping the bounded-corner-multiply \
             proof gate. Proof at {}.",
            proof.display()
        );
        return;
    };

    // (1) The whole file kernel-checks with ZERO sorry-axioms.
    let check = Command::new(&bin)
        .arg("check")
        .arg("--json")
        .arg(&proof)
        .output()
        .expect("`clean check` must run");
    let check_out = String::from_utf8_lossy(&check.stdout);
    assert!(
        check.status.success(),
        "`clean check` must accept the corner-bounds proof.\nstdout: {check_out}\nstderr: {}",
        String::from_utf8_lossy(&check.stderr)
    );
    let report: serde_json::Value =
        serde_json::from_str(&check_out).expect("`clean check --json` must emit a JSON report");
    assert_eq!(
        report["trust_summary"]["sorry_axioms"].as_u64(),
        Some(0),
        "the corner-bounds proof must carry NO sorry-axioms; report: {report}"
    );
    assert_eq!(
        report["trust_summary"]["kernel_check_failures"].as_u64(),
        Some(0),
        "every declaration must pass the kernel; report: {report}"
    );

    // (2) Every exported theorem's axiom closure is FOUNDATIONAL-only, and the
    //     headline theorems are actually among them. The flag alone is not
    //     enough: a file that exported nothing would satisfy it vacuously.
    let tmp = std::env::temp_dir().join("trust_i128_corner_bounds_cert");
    let bundle = tmp.with_extension("cleancert");
    let json = tmp.with_extension("json");
    let export = Command::new(&bin)
        .arg("export-cert")
        .arg("--out")
        .arg(&bundle)
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
    let cert: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(&json).expect("the export report must be written"),
    )
    .expect("the export report must be JSON");

    assert_eq!(
        cert["all_axiom_closures_foundational_only"].as_bool(),
        Some(true),
        "every exported theorem must have a FOUNDATIONAL-only axiom closure; report: {cert}"
    );
    assert_eq!(
        cert["sorry_axioms_observed"].as_u64(),
        Some(0),
        "no sorry-axiom may be observed during export; report: {cert}"
    );

    let exported: Vec<String> = cert["exported_theorems"]
        .as_array()
        .expect("exported_theorems must be an array")
        .iter()
        .map(|t| {
            t.as_str().map(str::to_string).unwrap_or_else(|| {
                t["name"].as_str().expect("each exported theorem must carry a name").to_string()
            })
        })
        .collect();
    for required in REQUIRED_FOUNDATIONAL_THEOREMS {
        assert!(
            exported.iter().any(|t| t == required || t.ends_with(required)),
            "{required} must be an EXPORTED, axiom-free Theorem (a `def`, an `axiom`, or a \
             failed declaration would not appear here); exported: {exported:?}"
        );
    }
}

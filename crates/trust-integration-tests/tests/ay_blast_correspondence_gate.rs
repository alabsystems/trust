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
//! Opt-in: skips with a notice when no `clean` checker is discoverable.

use std::path::{Path, PathBuf};
use std::process::Command;

use trust_integration_tests::clean_test_support::clean_checker_path;

/// The reduction — everything downstream of the hypothesis. All must be real,
/// exported, axiom-free Theorems.
const REQUIRED_REDUCTION_THEOREMS: &[&str] = &[
    "G16Mul.mul_equiv",
    "G16Mul.addval",
    "G16Mul.blast_equals_ir",
    "G16Mul.blast_value_eq",
    "G16Mul.agreement_is_discriminating",
    // The faithfulness witnesses for `mul_ay`. These are `rfl`, so the kernel
    // COMPUTES both multipliers and compares words — without them the
    // decomposition could drift from ay's loop and nothing would notice.
    "G16Mul.ay_w1",
    "G16Mul.ay_w3",
    // First brick of obligation 2.
    "G16Mul.shlk_shl1",
    // Obligation 2 verified EXHAUSTIVELY at widths 1..5 — every pair of n-bit
    // words, 1_364 pairs, all carry patterns. `rfl`, so the kernel COMPUTES
    // both multipliers over the enumerated word lists.
    "G16Mul.exh1",
    "G16Mul.exh4",
    "G16Mul.exh5",
    // The negative control that makes those exhaustive theorems mean something:
    // the same harness pointed at the WRONG function reports false. Without it
    // a `checkAB` that could not distinguish anything would satisfy them
    // vacuously.
    "G16Mul.exh_negative_control",
    // The arithmetic half of ripple-adder associativity, proved from the bare
    // prelude: two words of the SAME LENGTH with the SAME VALUE are the same
    // word. This is the piece obligation 2's general proof was blocked on.
    "G16Mul.toNat_inj",
    "G16Mul.double_cancel",
    "G16Mul.parity_cons",
    // The length hypothesis of toNat_inj is load-bearing, not bookkeeping:
    // [] and [false] share a value and differ in length, so dropping it would
    // make the theorem FALSE.
    "G16Mul.toNat_len_needed",
    "G16Mul.llen_len_differs",
    // Lemma 1 of the three associativity needs: the value law at equal lengths,
    // plus the bound and uniqueness step that turn a value equation back into a
    // bit equation.
    "G16Mul.wadd_value",
    "G16Mul.toNat_lt_pow2",
    "G16Mul.carry_unique",
    "G16Mul.lt_absurd",
    "G16Mul.llen_addRec",
    "G16Mul.toNatN_eq_toNat",
    // Lemma (a): RIPPLE-ADDER ASSOCIATIVITY, and the general remainder
    // uniqueness it needs (the two carry corrections ADD, reaching 2).
    "G16Mul.wadd_assoc",
    "G16Mul.rem_unique",
    // Its non-vacuity: the two groupings genuinely produce DIFFERENT carry-outs
    // while agreeing on the result, which is why a bit-wise proof is impossible
    // and the value route was required.
    "G16Mul.assoc_carries_differ",
    "G16Mul.assoc_witness",
    // Lemma (b): the low bits of a sum depend only on the low bits of the
    // operands, and the shift distribution it yields.
    "G16Mul.droplast_addRec",
    "G16Mul.shl1_wadd",
    // Lemma (c) and the discharge of obligation 2 itself.
    "G16Mul.accRows_lemma",
    "G16Mul.addRec_zeros",
    "G16Mul.shlk_wadd",
];

/// The name a proof of OBLIGATION 2 (`mul_ay = mul_m`, pure mathematics, fully
/// inside clean) must take. Unlike `DISCHARGE_THEOREM` this one needs no
/// reference to ay at all — anyone can close it.
const MODEL_MATCH_THEOREM: &str = "G16Mul.mul_ay_matches_model";

/// The name a proof of the correspondence MUST take when it lands. Naming it in
/// advance is what lets this gate detect the transition rather than silently
/// keep passing.
const DISCHARGE_THEOREM: &str = "G16Mul.ay_blast_agrees";

/// The cap that must stay in force while `DISCHARGE_THEOREM` is absent.
const EXPECTED_MUL_WIDTH_CAP: u32 = 8;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().expect("repo root")
}

/// Read `MAX_RECHECKABLE_MUL_WIDTH` out of the bridge source, so the coupling is
/// against the value the gate ACTUALLY compiles with, not a copy of it here.
fn declared_mul_width_cap() -> u32 {
    let src = repo_root().join("crates/trust-cg-bridge/src/verify_output.rs");
    let text = std::fs::read_to_string(&src)
        .unwrap_or_else(|e| panic!("must read {}: {e}", src.display()));
    let line = text
        .lines()
        .find(|l| l.contains("const MAX_RECHECKABLE_MUL_WIDTH"))
        .unwrap_or_else(|| {
            panic!(
                "MAX_RECHECKABLE_MUL_WIDTH must still exist in {}: if the tractability guard was \
                 removed, the wide-Mul kernel grade is being claimed on an inspection-level \
                 assumption — see this file's header",
                src.display()
            )
        });
    let digits: String = line
        .rsplit('=')
        .next()
        .expect("the const must have an initialiser")
        .chars()
        .filter(|c| c.is_ascii_digit())
        .collect();
    digits.parse().unwrap_or_else(|e| panic!("unparsable cap in {line:?}: {e}"))
}

#[test]
fn ay_blast_correspondence_gate() {
    let proof = repo_root().join("proofs/codegen-equivalence/g16_multiplier_equivalence.lean");
    assert!(proof.exists(), "g16_multiplier_equivalence.lean must exist at {}", proof.display());

    let Some(bin) = clean_checker_path() else {
        eprintln!(
            "NOTICE: no `clean` checker discoverable — skipping the ay-blast correspondence \
             gate. Proof at {}.",
            proof.display()
        );
        return;
    };

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

    for required in REQUIRED_REDUCTION_THEOREMS {
        assert!(
            has(required),
            "{required} must be an EXPORTED, axiom-free Theorem — the reduction from the \
             correspondence to the headline results is what makes the remaining gap a SINGLE \
             obligation; exported: {exported:?}"
        );
    }

    // (3) THE COUPLING. The obligation is open, so the cap must be in force.
    // The bridge is decomposed into TWO obligations of different kind:
    //   1. `AyBlastAgrees` — ay's Rust emits `mul_ay` (inspection; un-closable
    //      inside clean, but now a line-by-line structural comparison);
    //   2. `AyModelMatches` — `mul_ay = mul_m` (pure mathematics, closable).
    // The cap may only be lifted when BOTH are discharged; closing one alone
    // leaves the chain broken, so the gate tracks them separately and reports
    // which remains.
    let rust_gap_closed = has(DISCHARGE_THEOREM);
    let model_gap_closed = has(MODEL_MATCH_THEOREM);
    let discharged = rust_gap_closed && model_gap_closed;
    let cap = declared_mul_width_cap();

    // Obligation 2 IS discharged (`mul_ay_matches_model`), and must stay so: it
    // is the only half of the correspondence that clean can prove, so losing it
    // would silently return the bridge to a two-obligation state.
    assert!(
        model_gap_closed,
        "{MODEL_MATCH_THEOREM} must be an EXPORTED, axiom-free Theorem — obligation 2 \
         (mul_ay = mul_m) was DISCHARGED and must not regress; exported: {exported:?}"
    );
    if !rust_gap_closed {
        eprintln!(
            "NOTE: obligation 2 (mul_ay = mul_m) is CLOSED by {MODEL_MATCH_THEOREM}. The cap \
             stays in force because {DISCHARGE_THEOREM} (ay's encoder emits mul_ay) remains \
             open — that one is an inspection obligation and cannot be discharged inside clean."
        );
    }

    if discharged {
        panic!(
            "BOTH bridge obligations are now discharged ({DISCHARGE_THEOREM} and \
             {MODEL_MATCH_THEOREM}) — the ay-blast correspondence is complete.\n\
             This gate is deliberately failing to mark the transition, not because anything is \
             broken. Next steps:\n\
               1. a wide `Mul` may now cite the structured theorem instead of re-checking a \
                per-instance SAT refutation, so MAX_RECHECKABLE_MUL_WIDTH (currently {cap}) can \
                be raised or removed;\n\
               2. rewrite this gate to assert the NEW state (correspondence proved, cap lifted) \
                rather than the gap;\n\
               3. update the honesty notes in g16_multiplier_equivalence.lean, \
                i128_mul_corner_bounds.lean and structured_multiplier_proof_gate.rs, which all \
                record wide `Mul` as [VALIDATED] pending exactly this."
        );
    }

    assert_eq!(
        cap, EXPECTED_MUL_WIDTH_CAP,
        "MAX_RECHECKABLE_MUL_WIDTH is {cap}, expected {EXPECTED_MUL_WIDTH_CAP}, while \
         the bridge is INCOMPLETE (rust_gap_closed={rust_gap_closed}, \
         model_gap_closed={model_gap_closed}).\n\
         The cap and the open obligation are the same fact: without a proof that ay's blast IS \
         the model's multiplier, a wide `Mul` re-check has no structured theorem to cite, and \
         the per-instance SAT refutation is intractable (~16x steps per +2 bits; ~2.0M at width \
         8). Raising the cap here would claim a kernel grade on an inspection-level assumption. \
         If you intend to lift it, discharge the correspondence first and name the proof \
         {DISCHARGE_THEOREM}."
    );
}

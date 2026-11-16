// R4 driver flip acceptance instrument (2026-08-20).
//
// Measures, side by side on one VC corpus:
//   Lane A — the RETIRED subprocess route (replicated here verbatim from the
//            pre-flip `TrustWpRouterBackend`: constant fold, string-contract
//            lowering, `trust_wp::verify_with_contracts` -> `CliBackend`),
//            driven only through an EXPLICIT solver path so the measurement
//            never depends on ambient env.
//   Lane B — the canonical constant folder that replaced formula-only WP
//            registration. Real body-WP has independent typed request tests.
//
// Design gate (docs/design/2026-07-09-two-language-spec-surface.md, quoted in
// docs/audits/2026-08-20-r-phase-reaudit.md R4):
//   * corpus pass-rates >= baseline on the loose axis,
//   * zero false-accepts on the current per-VC path,
//   * preserved verdicts with the `trust_wp` binary absent from PATH, plus
//     canonical folding of contract-less constant safety rows.
//
// This file asserts those properties and additionally DEMONSTRATES the channel the
// flip closes: with a binary that satisfies the old text protocol, lane A
// minted a full deductive Proved from parsed subprocess text; lane B is
// invariant to that binary's existence.

use trust_router::VerificationBackend;
use trust_router::constant_folder::ConstantFolderBackend;
use trust_types::{
    ContractMetadata, Formula, Sort, SourceSpan, VcKind, VerificationCondition, VerificationResult,
};
use trust_wp::{Contract, ContractSet, TrustWpConfig, TrustWpLibError, verify_with_contracts};

// ---------------------------------------------------------------------------
// Lane A: faithful replica of the retired subprocess route.
// ---------------------------------------------------------------------------

/// The retired backend's `verify`, reproduced for measurement only. The one
/// deliberate difference: the solver path comes from an explicit config, never
/// from `TRUST_WP_PATH`, so the baseline is deterministic under test.
fn retired_subprocess_lane(
    vc: &VerificationCondition,
    config: &TrustWpConfig,
) -> VerificationResult {
    if let Some(result) = trust_router::unsupported_mir_unknown(vc, "trust-wp", 0) {
        return result;
    }
    let can_handle = matches!(
        vc.kind,
        VcKind::Precondition { .. } | VcKind::Postcondition | VcKind::Assertion { .. }
    ) && vc.contract_metadata.as_ref().is_some_and(ContractMetadata::has_any);
    if !can_handle {
        return VerificationResult::Unknown {
            solver: "trust-wp".into(),
            time_ms: 0,
            reason: format!("trust-wp cannot handle VC kind {:?}", vc.kind),
        };
    }
    match vc.formula {
        Formula::Bool(false) => {
            return VerificationResult::Proved {
                solver: "trust-wp".into(),
                time_ms: 0,
                strength: trust_types::ProofStrength::deductive(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            };
        }
        Formula::Bool(true) => {
            return VerificationResult::Failed {
                solver: "trust-wp".into(),
                time_ms: 0,
                counterexample: None,
            };
        }
        _ => {}
    }
    let Some(contracts) = vc_to_trust_wp_contracts(vc) else {
        return VerificationResult::Unknown {
            solver: "trust-wp".into(),
            time_ms: 0,
            reason: "trust-wp cannot translate this VC formula to contracts".into(),
        };
    };
    match verify_with_contracts(vc.function.as_ref(), &contracts, config) {
        Ok(result) => result.to_verification_result(),
        Err(TrustWpLibError::Timeout { timeout_ms }) => {
            VerificationResult::Timeout { solver: "trust-wp".into(), timeout_ms }
        }
        Err(err) => VerificationResult::Unknown {
            solver: "trust-wp".into(),
            time_ms: 0,
            reason: format!("trust-wp unavailable or inconclusive: {err}"),
        },
    }
}

/// Retired string-contract lowering (verbatim from the pre-flip backend).
fn vc_to_trust_wp_contracts(vc: &VerificationCondition) -> Option<ContractSet> {
    let goal = Formula::Not(Box::new(vc.formula.clone()));
    let expr = formula_to_trust_wp_expr(&goal)?;
    let contracts = match &vc.kind {
        VcKind::Precondition { .. } => ContractSet::new().with_requires(Contract::requires(expr)),
        VcKind::Postcondition => ContractSet::new().with_ensures(Contract::ensures(expr)),
        VcKind::Assertion { message } if message.contains("[loop:invariant]") => {
            ContractSet::new().with_invariant(Contract::invariant(expr))
        }
        VcKind::Assertion { .. } => ContractSet::new().with_ensures(Contract::ensures(expr)),
        _ => return None,
    };
    Some(contracts)
}

fn formula_to_trust_wp_expr(formula: &Formula) -> Option<String> {
    let bin = |op: &str, lhs: &Formula, rhs: &Formula| -> Option<String> {
        Some(format!(
            "({}) {op} ({})",
            formula_to_trust_wp_expr(lhs)?,
            formula_to_trust_wp_expr(rhs)?
        ))
    };
    match formula {
        Formula::Bool(true) => Some("true".to_string()),
        Formula::Bool(false) => Some("false".to_string()),
        Formula::Var(name, _) => Some(name.clone()),
        Formula::Not(inner) => Some(format!("!({})", formula_to_trust_wp_expr(inner)?)),
        Formula::And(terms) => terms
            .iter()
            .map(formula_to_trust_wp_expr)
            .collect::<Option<Vec<_>>>()
            .map(|terms| terms.join(" && ")),
        Formula::Or(terms) => terms
            .iter()
            .map(formula_to_trust_wp_expr)
            .collect::<Option<Vec<_>>>()
            .map(|terms| terms.join(" || ")),
        Formula::Implies(lhs, rhs) => bin("==>", lhs, rhs),
        Formula::Eq(lhs, rhs) => bin("==", lhs, rhs),
        Formula::Lt(lhs, rhs) => bin("<", lhs, rhs),
        Formula::Le(lhs, rhs) => bin("<=", lhs, rhs),
        Formula::Gt(lhs, rhs) => bin(">", lhs, rhs),
        Formula::Ge(lhs, rhs) => bin(">=", lhs, rhs),
        Formula::Add(lhs, rhs) => bin("+", lhs, rhs),
        Formula::Sub(lhs, rhs) => bin("-", lhs, rhs),
        Formula::Mul(lhs, rhs) => bin("*", lhs, rhs),
        Formula::Int(value) => Some(value.to_string()),
        Formula::UInt(value) => Some(value.to_string()),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Corpus
// ---------------------------------------------------------------------------

fn vc(kind: VcKind, formula: Formula, with_contract: bool) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: "ab::corpus_fn".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: with_contract
            .then(|| ContractMetadata { has_ensures: true, ..ContractMetadata::default() }),
        obligation: None,
    }
}

fn int_var(name: &str) -> Formula {
    Formula::Var(name.into(), Sort::Int)
}

fn corpus() -> Vec<(&'static str, VerificationCondition)> {
    vec![
        ("post_const_holds", vc(VcKind::Postcondition, Formula::Bool(false), true)),
        ("post_const_violated", vc(VcKind::Postcondition, Formula::Bool(true), true)),
        (
            "post_bool_var",
            vc(
                VcKind::Postcondition,
                Formula::Not(Box::new(Formula::Var("ok".into(), Sort::Bool))),
                true,
            ),
        ),
        (
            "post_int_compare",
            vc(
                VcKind::Postcondition,
                Formula::Le(Box::new(int_var("x")), Box::new(Formula::Int(5))),
                true,
            ),
        ),
        (
            "post_arithmetic_byte_extent",
            vc(
                VcKind::Postcondition,
                Formula::Gt(
                    Box::new(Formula::Mul(Box::new(Formula::Int(4)), Box::new(int_var("len")))),
                    Box::new(Formula::Int(64)),
                ),
                true,
            ),
        ),
        (
            "post_implication",
            vc(
                VcKind::Postcondition,
                Formula::Implies(
                    Box::new(Formula::Var("guard".into(), Sort::Bool)),
                    Box::new(Formula::Var("bad".into(), Sort::Bool)),
                ),
                true,
            ),
        ),
        (
            "pre_call_site",
            vc(
                VcKind::Precondition { callee: "ab::callee".into() },
                Formula::Not(Box::new(Formula::Var("requires_holds".into(), Sort::Bool))),
                true,
            ),
        ),
        (
            "loop_invariant_assertion",
            vc(
                VcKind::Assertion { message: "[loop:invariant] i <= n".into() },
                Formula::Gt(Box::new(int_var("i")), Box::new(int_var("n"))),
                true,
            ),
        ),
        (
            "plain_assertion",
            vc(
                VcKind::Assertion { message: "authored assert".into() },
                Formula::Var("bad".into(), Sort::Bool),
                true,
            ),
        ),
        (
            "quantified_untranslatable",
            vc(
                VcKind::Postcondition,
                Formula::Forall(
                    vec![("k".into(), Sort::Int)],
                    Box::new(Formula::Var("bad".into(), Sort::Bool)),
                ),
                true,
            ),
        ),
        (
            "bare_assertion_no_contract",
            vc(
                VcKind::Assertion { message: "[unsafe:sep:alloc] null check".into() },
                Formula::Bool(false),
                false,
            ),
        ),
        (
            "unsupported_mir_gate",
            vc(
                VcKind::UnsupportedMir {
                    kind: "terminator".into(),
                    detail: "opaque terminator not modeled".into(),
                },
                Formula::Bool(false),
                true,
            ),
        ),
    ]
}

fn class(result: &VerificationResult) -> &'static str {
    match result {
        VerificationResult::Proved { .. } => "Proved",
        VerificationResult::Failed { .. } => "Failed",
        VerificationResult::Unknown { .. } => "Unknown",
        VerificationResult::Timeout { .. } => "Timeout",
        // `VerificationResult` is #[non_exhaustive] for dependents; any future
        // variant is classified conservatively as a non-verdict.
        _ => "Unknown",
    }
}

#[cfg(unix)]
fn write_script(name: &str, body: &str) -> std::path::PathBuf {
    use std::os::unix::fs::PermissionsExt;
    let path = std::env::temp_dir().join(format!("trust-wp-ab-{name}-{}.sh", std::process::id()));
    std::fs::write(&path, body).expect("write test script");
    let mut perms = std::fs::metadata(&path).expect("script metadata").permissions();
    perms.set_mode(0o700);
    std::fs::set_permissions(&path, perms).expect("chmod script");
    path
}

/// A binary satisfying the retired text protocol's Proved shape: wire line
/// with `verified=1`, no soundness-gap counters, exit 0.
#[cfg(unix)]
const FAKE_PROVING_SCRIPT: &str = "#!/bin/sh\n\
    echo 'TRUST_WP_RESULT:v1 verified=1 failed=0 errors=0 warnings=0 assumed=0 trusted=0 skipped=0 verified_with_axiom_deps=0' >&2\n\
    exit 0\n";

// ---------------------------------------------------------------------------
// The A/B acceptance tests
// ---------------------------------------------------------------------------

/// Design-gate axis 1 + 3: with the trust_wp binary ABSENT (the shipping
/// default — no TRUST_WP_PATH, no configured path), every corpus verdict class
/// from the current route is identical to the retired route's, except that the
/// shared folder also decides contract-less constants with canonical polarity.
#[test]
fn canonical_route_preserves_baseline_and_folds_contractless_constants() {
    let absent = TrustWpConfig::new().with_solver_path("/nonexistent/trust-wp-r4-ab-absent");
    let flipped = ConstantFolderBackend;

    let mut agreements = 0usize;
    let mut rows = Vec::new();
    for (name, vc) in corpus() {
        let a = retired_subprocess_lane(&vc, &absent);
        let b = flipped.verify(&vc);
        let agree = class(&a) == class(&b);
        agreements += usize::from(agree);
        rows.push(format!(
            "{name:32} baseline(absent)={:8} current={:8} {}",
            class(&a),
            class(&b),
            if agree { "AGREE" } else { "DIVERGE" }
        ));
        if name == "bare_assertion_no_contract" {
            // The shared folder also handles constant safety rows without
            // contract metadata. No formula-only WP claim is formed.
            assert_eq!(class(&a), "Unknown");
            assert_eq!(class(&b), "Proved");
        } else {
            assert_eq!(
                class(&a),
                class(&b),
                "retired formula route changed `{name}`: baseline {a:?} vs current {b:?}"
            );
        }
    }
    eprintln!("R4 A/B corpus (binary absent): {agreements}/{} agree", rows.len());
    for row in rows {
        eprintln!("  {row}");
    }
}

/// Design-gate axis 2: zero false-accepts on the current per-VC path. The only
/// corpus rows the current route may decide are the constant-folded ones; every
/// symbolic row stays Unknown on the bare per-VC carrier.
#[test]
fn canonical_route_mints_no_verdict_beyond_constant_folding() {
    let flipped = ConstantFolderBackend;
    for (name, vc) in corpus() {
        let b = flipped.verify(&vc);
        match name {
            "post_const_holds" | "bare_assertion_no_contract" => {
                assert_eq!(class(&b), "Proved", "{name}: {b:?}")
            }
            "post_const_violated" => assert_eq!(class(&b), "Failed", "{name}: {b:?}"),
            _ => assert_eq!(
                class(&b),
                "Unknown",
                "constant folder must not decide symbolic corpus item `{name}`: {b:?}"
            ),
        }
    }
}

/// The channel the flip closes, demonstrated: a binary that satisfies the old
/// text protocol made the RETIRED lane mint a full deductive Proved for a
/// symbolic obligation (parsed subprocess text as proof authority). The
/// flipped route on the same VC stays Unknown.
#[cfg(unix)]
#[test]
fn retired_text_protocol_cannot_authorize_current_formula_route() {
    let script = write_script("proving", FAKE_PROVING_SCRIPT);
    // macOS assesses a file's first execution, one file at a time machine-wide,
    // and a push lane queues freshly linked test binaries ahead of it. Pay that
    // here, so the first corpus row's run is not charged it against trust-wp's
    // timeout.
    let warm_up = std::process::Command::new(&script)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .expect("run the fresh proving script once before the retired lane times it");
    assert!(warm_up.success(), "proving script warm-up failed: {warm_up:?}");
    let present = TrustWpConfig::new().with_solver_path(script.to_string_lossy().as_ref());
    let flipped = ConstantFolderBackend;

    let mut retired_proved = 0usize;
    let mut rows = Vec::new();
    for (name, vc) in corpus() {
        let a = retired_subprocess_lane(&vc, &present);
        let b = flipped.verify(&vc);
        if matches!(a, VerificationResult::Proved { .. }) && !matches!(vc.formula, Formula::Bool(_))
        {
            retired_proved += 1;
            assert!(
                !matches!(b, VerificationResult::Proved { .. }),
                "corpus item `{name}`: the current route must not reproduce the \
                 text-protocol Proved: {b:?}"
            );
        }
        rows.push(format!("{name:32} baseline(present)={:8} current={:8}", class(&a), class(&b)));
    }
    let _ = std::fs::remove_file(script);

    eprintln!("R4 A/B corpus (fake proving binary configured):");
    for row in rows {
        eprintln!("  {row}");
    }
    eprintln!(
        "  -> retired lane minted {retired_proved} symbolic Proved verdict(s) from parsed \
         subprocess text; the flip removes this channel"
    );
    assert!(
        retired_proved > 0,
        "instrument self-check: the fake binary must demonstrate the retired lane's \
         text-protocol Proved channel on at least one symbolic corpus item"
    );
}

/// THE SEAL: the current route never consults TRUST_WP_PATH (or any subprocess).
/// Pointing TRUST_WP_PATH at a binary that would satisfy the old protocol
/// changes nothing — verdicts are bit-for-bit the same class on every corpus
/// item. This is the regression tripwire against reintroducing the subprocess
/// into the compiler route.
#[cfg(unix)]
#[test]
fn route_is_invariant_to_trust_wp_path_env() {
    let script = write_script("seal", FAKE_PROVING_SCRIPT);
    let flipped = ConstantFolderBackend;

    let without_env: Vec<(String, &'static str)> = corpus()
        .into_iter()
        .map(|(name, vc)| (name.to_string(), class(&flipped.verify(&vc))))
        .collect();

    // SAFETY (edition 2024 set_var contract): this test is the only code in
    // this test binary that mutates TRUST_WP_PATH, and the current route under
    // test must not read it — that is the property being pinned.
    unsafe { std::env::set_var("TRUST_WP_PATH", &script) };
    let with_env: Vec<(String, &'static str)> = corpus()
        .into_iter()
        .map(|(name, vc)| (name.to_string(), class(&flipped.verify(&vc))))
        .collect();
    unsafe { std::env::remove_var("TRUST_WP_PATH") };
    let _ = std::fs::remove_file(script);

    assert_eq!(
        without_env, with_env,
        "the compiler route must be invariant to TRUST_WP_PATH: the flip retired the \
         subprocess lane and nothing may quietly re-engage it"
    );
}

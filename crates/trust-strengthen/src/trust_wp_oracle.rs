// trust-strengthen/trust_wp_oracle.rs: trust-wp-direct verification oracle for CEGIS loop
//
// Retained compatibility surface for the old TrustWP CEGIS oracle, plus
// StdlibSpecs import as seed specs. TrustWP currently owns no proof-producing
// obligation kind, so the oracle refuses every non-empty candidate set instead
// of spawning and parsing the compatibility CLI.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_vcgen::{FnContract, StdlibSpecs};

use crate::spec_proposal::{SpecKind, SpecProposal};

/// Outcome of verifying a set of inferred specs.
#[derive(Debug, Clone)]
pub enum VerifyOutcome {
    /// All VCs passed: specs are valid.
    AllPassed,
    /// Some VCs failed, with counterexample text for refinement.
    Failed {
        /// Human-readable counterexample from the solver.
        counterexample: String,
        /// Which specs failed.
        failed_specs: Vec<SpecProposal>,
    },
    /// Verification encountered an error (timeout, solver crash, etc.).
    Error {
        /// Error description.
        message: String,
    },
}

/// Trait for a verification oracle over proposed specs.
///
/// Abstracted so tests can use a mock verifier. In production, this calls
/// trust_vcgen -> trust-router -> solver tools.
pub trait VerificationOracle: Send + Sync {
    /// Check whether a set of spec proposals are valid for the given function.
    ///
    /// Returns `AllPassed` if the specs make all VCs provable,
    /// `Failed` with a counterexample if not, or `Error` on infrastructure failure.
    fn verify_specs(&self, function_path: &str, specs: &[SpecProposal]) -> VerifyOutcome;
}

/// Fail-closed compatibility shim for the retired direct TrustWP oracle.
///
/// The type remains source-compatible for CEGIS callers, but it cannot validate
/// proposals: TrustWP advertises zero owned obligation kinds and the formula-less
/// RustHorn give-back record is not a dischargeable proof obligation.
/// Callers must submit body-aware contracts to the compiler's typed TrustMC
/// route (or refinement to TrustVC) instead of treating a parsed subprocess
/// verdict as authority. Like the compiler's per-VC route after the R4 flip,
/// this oracle never spawns the `trust_wp` subprocess, never reads
/// `TRUST_WP_PATH`, and never parses the `TRUST_WP_RESULT:v1` text protocol.
#[derive(Debug, Clone, Copy, Default)]
pub struct TrustWpDirectOracle;

impl TrustWpDirectOracle {
    /// Create a new oracle with default trust_wp timeout.
    #[must_use]
    pub fn new() -> Self {
        Self
    }

    /// Preserve the historical constructor without enabling the retired path.
    #[must_use]
    pub fn with_timeout(_timeout_ms: u64) -> Self {
        Self
    }
}

impl VerificationOracle for TrustWpDirectOracle {
    fn verify_specs(&self, function_path: &str, specs: &[SpecProposal]) -> VerifyOutcome {
        if specs.is_empty() {
            return VerifyOutcome::AllPassed;
        }
        VerifyOutcome::Failed {
            counterexample: format!(
                "TrustWP direct validation is unsupported for `{function_path}`: the engine owns no dischargeable obligation kind; submit body-aware contracts through the compiler TrustMC route and refinement through TrustVC"
            ),
            failed_specs: specs.to_vec(),
        }
    }
}

// ---------------------------------------------------------------------------
// Stdlib specs seed importer
// ---------------------------------------------------------------------------

/// Import standard library specs as seed `SpecProposal`s for the strengthen loop.
///
/// Converts `FnContract` entries from the stdlib registry into `SpecProposal`
/// format suitable for the CEGIS feedback loop. These serve as ground truth
/// for standard library functions (Vec, Option, Result, Iterator).
#[must_use]
pub fn import_stdlib_seed_specs() -> Vec<SpecProposal> {
    let registry = StdlibSpecs::new();
    let mut seeds = Vec::new();

    for contract in registry.all() {
        seeds.extend(contract_to_proposals(contract));
    }

    seeds
}

/// Convert a single `FnContract` into `SpecProposal`s.
fn contract_to_proposals(contract: &FnContract) -> Vec<SpecProposal> {
    let mut proposals = Vec::new();

    // Extract the short function name from the fully-qualified path
    let fn_name = contract.fn_path.rsplit("::").next().unwrap_or(&contract.fn_path).to_string();

    for (i, pre) in contract.preconditions.iter().enumerate() {
        proposals.push(SpecProposal {
            function_path: contract.fn_path.clone(),
            function_name: fn_name.clone(),
            kind: SpecKind::Requires,
            spec_body: format!("{pre:?}"),
            confidence: 1.0, // stdlib specs are ground truth
            rationale: format!(
                "Standard library contract: precondition {} for {}",
                i + 1,
                contract.fn_path
            ),
            iteration: 0, // seed, not inferred
            validated: true,
            validation_errors: Vec::new(),
        });
    }

    for (i, post) in contract.postconditions.iter().enumerate() {
        proposals.push(SpecProposal {
            function_path: contract.fn_path.clone(),
            function_name: fn_name.clone(),
            kind: SpecKind::Ensures,
            spec_body: format!("{post:?}"),
            confidence: 1.0, // stdlib specs are ground truth
            rationale: format!(
                "Standard library contract: postcondition {} for {}",
                i + 1,
                contract.fn_path
            ),
            iteration: 0,
            validated: true,
            validation_errors: Vec::new(),
        });
    }

    proposals
}

#[cfg(test)]
mod tests {
    use trust_types::Formula;

    use super::*;

    // -----------------------------------------------------------------------
    // TrustWpDirectOracle basic tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_trust_wp_oracle_default() {
        let _oracle = TrustWpDirectOracle;
    }

    #[test]
    fn test_trust_wp_oracle_with_timeout() {
        let _oracle = TrustWpDirectOracle::with_timeout(5_000);
    }

    #[test]
    fn test_trust_wp_oracle_empty_specs_passes() {
        let oracle = TrustWpDirectOracle::new();
        let outcome = oracle.verify_specs("test::f", &[]);
        assert!(matches!(outcome, VerifyOutcome::AllPassed));
    }

    #[test]
    fn test_trust_wp_oracle_rejects_even_trivial_true_without_owned_claim() {
        let oracle = TrustWpDirectOracle::new();
        let spec = SpecProposal {
            function_path: "test::f".into(),
            function_name: "f".into(),
            kind: SpecKind::Ensures,
            spec_body: "true".into(),
            confidence: 0.9,
            rationale: "must not become a synthetic proof".into(),
            iteration: 1,
            validated: true,
            validation_errors: vec![],
        };
        let outcome = oracle.verify_specs("test::f", &[spec]);
        let VerifyOutcome::Failed { counterexample, failed_specs } = outcome else {
            panic!("a non-empty retired TrustWP request must fail closed");
        };
        assert_eq!(failed_specs.len(), 1);
        assert!(counterexample.contains("owns no dischargeable obligation kind"));
        assert!(counterexample.contains("TrustMC"));
        assert!(counterexample.contains("TrustVC"));
    }

    #[test]
    fn test_trust_wp_oracle_binary_absent_from_path_still_fails_closed() {
        const CHILD: &str = "TRUST_R4_TRUST_WP_PATH_CHILD";
        if std::env::var_os(CHILD).is_some() {
            let oracle = TrustWpDirectOracle::new();
            let spec = SpecProposal {
                function_path: "test::f".into(),
                function_name: "f".into(),
                kind: SpecKind::Ensures,
                spec_body: "true".into(),
                confidence: 0.9,
                rationale: "PATH-absent control".into(),
                iteration: 1,
                validated: true,
                validation_errors: vec![],
            };
            assert!(matches!(
                oracle.verify_specs("test::f", &[spec]),
                VerifyOutcome::Failed { .. }
            ));
            eprintln!("R4_PATH_ABSENT_CHILD_EXECUTED");
            return;
        }

        let output = std::process::Command::new(
            std::env::current_exe().expect("current test executable path"),
        )
        .args([
            "--exact",
            "trust_wp_oracle::tests::test_trust_wp_oracle_binary_absent_from_path_still_fails_closed",
            "--nocapture",
        ])
        .env(CHILD, "1")
        .env("PATH", "/definitely/no/trust-wp/binary")
        .env_remove("TRUST_WP_PATH")
        .output()
        .expect("spawn isolated PATH-absent control");
        assert!(
            output.status.success(),
            "PATH-absent child failed:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
        assert!(
            String::from_utf8_lossy(&output.stderr).contains("R4_PATH_ABSENT_CHILD_EXECUTED"),
            "PATH-absent child filter ran no test:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
    }

    #[test]
    fn test_trust_wp_oracle_nontrivial_spec_is_unsupported() {
        let oracle = TrustWpDirectOracle::new();
        let spec = SpecProposal {
            function_path: "test::f".into(),
            function_name: "f".into(),
            kind: SpecKind::Ensures,
            spec_body: "x > 0".into(),
            confidence: 0.8,
            rationale: "nontrivial".into(),
            iteration: 1,
            validated: true,
            validation_errors: vec![],
        };
        let outcome = oracle.verify_specs("test::f", &[spec]);
        assert!(
            matches!(outcome, VerifyOutcome::Failed { .. }),
            "nontrivial spec must remain unsupported: {outcome:?}"
        );
    }

    // -----------------------------------------------------------------------
    // Stdlib seed import tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_import_stdlib_seed_specs_nonempty() {
        let seeds = import_stdlib_seed_specs();
        assert!(!seeds.is_empty(), "stdlib should have seed specs");
    }

    #[test]
    fn test_import_stdlib_seed_specs_have_full_confidence() {
        let seeds = import_stdlib_seed_specs();
        for spec in &seeds {
            assert!(
                (spec.confidence - 1.0).abs() < f64::EPSILON,
                "stdlib seed spec should have confidence 1.0: {}",
                spec.function_path
            );
        }
    }

    #[test]
    fn test_import_stdlib_seed_specs_are_validated() {
        let seeds = import_stdlib_seed_specs();
        for spec in &seeds {
            assert!(spec.validated, "stdlib seeds should be pre-validated");
            assert!(
                spec.validation_errors.is_empty(),
                "stdlib seeds should have no validation errors"
            );
        }
    }

    #[test]
    fn test_import_stdlib_seed_specs_iteration_zero() {
        let seeds = import_stdlib_seed_specs();
        for spec in &seeds {
            assert_eq!(spec.iteration, 0, "stdlib seeds should have iteration 0 (not inferred)");
        }
    }

    #[test]
    fn test_import_stdlib_seed_specs_have_correct_kinds() {
        let seeds = import_stdlib_seed_specs();
        let has_requires = seeds.iter().any(|s| s.kind == SpecKind::Requires);
        let has_ensures = seeds.iter().any(|s| s.kind == SpecKind::Ensures);
        assert!(
            has_requires || has_ensures,
            "stdlib seeds should have at least one requires or ensures"
        );
    }

    #[test]
    fn test_contract_to_proposals() {
        let contract = FnContract::new("std::vec::Vec::push")
            .pre(Formula::Bool(true))
            .post(Formula::Bool(true));
        let proposals = contract_to_proposals(&contract);
        assert_eq!(proposals.len(), 2);
        assert_eq!(proposals[0].kind, SpecKind::Requires);
        assert_eq!(proposals[1].kind, SpecKind::Ensures);
        assert_eq!(proposals[0].function_name, "push");
        assert_eq!(proposals[0].function_path, "std::vec::Vec::push");
    }

    // -----------------------------------------------------------------------
    // Integration: TrustWpDirectOracle with real spec through feedback loop
    // -----------------------------------------------------------------------

    #[test]
    fn test_trust_wp_oracle_integration_mixed_specs() {
        let oracle = TrustWpDirectOracle::new();
        let specs = vec![
            SpecProposal {
                function_path: "math::add".into(),
                function_name: "add".into(),
                kind: SpecKind::Ensures,
                spec_body: "true".into(),
                confidence: 0.9,
                rationale: "trivially valid".into(),
                iteration: 1,
                validated: true,
                validation_errors: vec![],
            },
            SpecProposal {
                function_path: "math::add".into(),
                function_name: "add".into(),
                kind: SpecKind::Ensures,
                spec_body: "false".into(),
                confidence: 0.5,
                rationale: "trivially invalid".into(),
                iteration: 1,
                validated: true,
                validation_errors: vec![],
            },
        ];
        let outcome = oracle.verify_specs("math::add", &specs);
        // No spec is accepted through the retired direct TrustWP authority,
        // including the syntactically trivial one.
        assert!(
            matches!(outcome, VerifyOutcome::Failed { .. }),
            "mixed specs with a false one should fail: {outcome:?}"
        );
        if let VerifyOutcome::Failed { failed_specs, .. } = &outcome {
            assert_eq!(failed_specs.len(), 2, "both specs must remain unvalidated");
            assert_eq!(failed_specs[0].spec_body, "true");
            assert_eq!(failed_specs[1].spec_body, "false");
        }
    }
}

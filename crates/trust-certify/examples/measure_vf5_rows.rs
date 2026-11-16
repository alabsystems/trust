// Copyright 2026 Andrew Yates | Apache-2.0 OR MIT
//! Observe actual artifact judgments through the production check, without
//! admitting a production base, returning a token or selecting compiler rows.

use std::collections::BTreeSet;
use std::path::PathBuf;
use std::process::ExitCode;

use serde_json::{Value, json};
use clean_kernel::{ReferenceRefusal, env::EnvError, tc::TypeError};
use trust_certify::calculus_row::{CalculusRowClaim, CalculusRowMiss};
use trust_certify::calculus_row::base::measurement::{
    Vf5JudgmentInput, Vf5JudgmentObservation, Vf5TargetTypeMeasurement,
    measure_package_with_judgments,
};
use trust_certify::calculus_row::hints::Vf5HintMiss;

struct Input {
    artifact_path: PathBuf,
    proposal_path: PathBuf,
    claim: CalculusRowClaim,
    proposal: Vec<u8>,
}

fn main() -> ExitCode {
    match run() {
        Ok(value) => { println!("{value}"); ExitCode::SUCCESS }
        Err(error) => {
            eprintln!("VF5 row observation refused (no production authority): {error}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<Value, String> {
    let args = std::env::args_os().skip(1).collect::<Vec<_>>();
    if args.len() < 6 || (args.len() - 2) % 4 != 0 {
        return Err("usage: measure_vf5_rows PACKAGE_ROOT INDEPENDENT_TYPE_BOOK ARTIFACT HINTS FID SYMBOL [ARTIFACT HINTS FID SYMBOL ...]".into());
    }
    let root = PathBuf::from(&args[0]);
    let expected = read(&PathBuf::from(&args[1]))?;
    let expected: Vec<Vf5TargetTypeMeasurement> = serde_json::from_slice(&expected)
        .map_err(|error| format!("independent target-type book: {error}"))?;
    let mut inputs = Vec::new();
    for group in args[2..].chunks_exact(4) {
        ensure_current()?;
        let artifact_path = PathBuf::from(&group[0]);
        let proposal_path = PathBuf::from(&group[1]);
        let raw_fid = group[2].to_str().ok_or("non-UTF8 function id")?;
        let fid = raw_fid.parse::<u64>().map_err(|error| format!("function id: {error}"))?;
        if fid.to_string() != raw_fid { return Err("noncanonical function id".into()); }
        let symbol = group[3].to_str().ok_or("non-UTF8 claimed symbol")?.as_bytes().to_vec();
        inputs.push(Input {
            claim: CalculusRowClaim { artifact: read(&artifact_path)?, fid, symbol },
            proposal: read(&proposal_path)?, artifact_path, proposal_path,
        });
    }
    let borrowed = inputs.iter().map(|input| Vf5JudgmentInput {
        claim: &input.claim, proposal: &input.proposal,
    }).collect::<Vec<_>>();
    let measured = measure_package_with_judgments(&root, &borrowed)
        .map_err(|error| format!("completed base/row observation: {error:?}"))?;
    if expected.len() != 7 || expected != measured.base.target_types {
        return Err("actual seven target types differ from the independent book".into());
    }
    if measured.rows.len() != inputs.len() {
        return Err("incomplete requested row population".into());
    }
    let mut rows = Vec::new();
    for (index, (input, row)) in inputs.iter().zip(&measured.rows).enumerate() {
        ensure_current()?;
        let decoded = decoded_module(&input.claim);
        ensure_current()?;
        rows.push(json!({
        "index": index,
        "artifact": input.artifact_path,
        "proposal": input.proposal_path,
        "claimed_fid": input.claim.fid,
        "claimed_symbol": input.claim.symbol,
        "decoded_module": decoded,
        "judgment": observation(row),
        }));
    }
    ensure_current()?;
    let report = measured.base.report;
    Ok(json!({
        "kind": "vf5-shared-judgment-observation-v1",
        "production_admission": false,
        "manifest_sha256": hex(&report.manifest_sha256),
        "environment_sha256": hex(&report.environment.0),
        "replay": report.replay,
        "target_types": measured.base.target_types,
        "all_requested_judgments_observed": true,
        "rows": rows,
    }))
}

fn ensure_current() -> Result<(), String> {
    match trust_certify::calculus_row::base::preparation_stop() {
        Some(cause) => Err(format!("inherited stop during DATA observation: {cause:?}")),
        None => Ok(()),
    }
}

fn read(path: &std::path::Path) -> Result<Vec<u8>, String> {
    trust_proof_session::storage::read_bounded(path)
        .map_err(|error| format!("{}: {error}", path.display()))
}

/// The maintained decoder and validator observe full module/SSA and declared
/// wire provenance. They do not establish the compiler's HIR/source binding or
/// make a kernel refusal disappear. Wrong claims still reach the row checker.
fn decoded_module(claim: &CalculusRowClaim) -> Value {
    match trust_ir::binary::deserialize_module_with_wire_version(&claim.artifact) {
        Err(error) => json!({ "state": "decode_refused", "detail": format!("{error:?}") }),
        Ok((module, wire)) => {
            let errors = trust_ir_build::validate_module_as_decoded(&module, wire);
            json!({
                "state": "decoded",
                "wire_version": wire.get(),
                "module": module.name,
                "validation_errors": errors.iter().map(|error| format!("{error:?}")).collect::<Vec<_>>(),
                "functions": module.functions.iter().map(|function| json!({
                    "fid": function.id.index(), "symbol": function.name,
                })).collect::<Vec<_>>(),
                "unique_reciprocal_claim_binding": binding_matches(&module, claim),
                "compiler_source_binding_recreated": false,
            })
        }
    }
}

fn binding_matches(module: &trust_ir::Module, claim: &CalculusRowClaim) -> bool {
    let mut ids = BTreeSet::new();
    let mut names = BTreeSet::new();
    for function in &module.functions {
        if function.name.is_empty() || !ids.insert(function.id) || !names.insert(&function.name) {
            return false;
        }
    }
    module.functions.iter().any(|function| {
        u64::from(function.id.index()) == claim.fid && function.name.as_bytes() == claim.symbol
    })
}

fn observation(row: &Vf5JudgmentObservation) -> Value {
    match row {
        Vf5JudgmentObservation::AcceptedData(data) => json!({
            "state": "accepted_observation",
            "artifact_sha256": hex(&data.artifact_sha256),
            "fid": data.fid, "symbol": data.symbol,
            "environment_sha256": hex(&data.environment_sha256),
            // Closed goal/proof commitment, distinct from target TYPE hashes.
            "statement_sha256": hex(&data.statement_sha256),
        }),
        Vf5JudgmentObservation::Refused(error) => {
            let class = match error {
                Vf5HintMiss::Row(CalculusRowMiss::Refused(_)) => "kernel_refused",
                Vf5HintMiss::Row(CalculusRowMiss::EmptyClaim) => "empty_claim",
                Vf5HintMiss::Row(_) => "base_admission_refused",
                Vf5HintMiss::NoHint => "no_hint",
                Vf5HintMiss::Io(_) => "io_refused",
                Vf5HintMiss::Envelope(_) => "envelope_refused",
                Vf5HintMiss::Invalid(_) => "identity_or_schema_refused",
                Vf5HintMiss::SnapshotRefused(_) => "snapshot_refused",
                Vf5HintMiss::Term(_) => "term_codec_refused",
                Vf5HintMiss::Stopped(_) => "stopped",
            };
            let reference_kind = match error {
                Vf5HintMiss::Row(CalculusRowMiss::Refused(error)) => Some(reference_refusal_kind(error)),
                _ => None,
            };
            json!({
                "state": class,
                "reference_refusal_kind": reference_kind,
                "semantic_negative_credit": false,
                "detail": format!("{error:?}"),
            })
        }
    }
}

/// Match typed errors, never their diagnostic text. Even a type mismatch is
/// only DATA: a semantic control still needs its actual supported judgment and
/// independently established false premise/counterexample, plus paired positives.
fn reference_refusal_kind(error: &ReferenceRefusal) -> &'static str {
    match error {
        ReferenceRefusal::Kernel(EnvError::TypeCheckFailed { source, .. }) => match source {
            TypeError::TypeMismatch { .. } => "type_mismatch",
            TypeError::UnknownConst(_) => "unknown_constant",
            TypeError::HeartbeatExceeded { .. } => "heartbeat_exhausted",
            TypeError::DeclarationBudgetExhausted { .. } => "declaration_budget_exhausted",
            TypeError::ExcessiveMemory => "excessive_memory",
            TypeError::DeepRecursion => "deep_recursion",
            TypeError::SortDepthExceeded { .. } => "sort_depth_exceeded",
            _ => "other_type_error",
        },
        ReferenceRefusal::Kernel(_) => "other_environment_refusal",
        ReferenceRefusal::TheoryExclusion(_) => "theory_exclusion",
        ReferenceRefusal::BaseRecheck { .. } => "base_recheck",
        ReferenceRefusal::StructuralProvenance { .. } => "structural_provenance",
        _ => "other_reference_refusal",
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    // Existing actual retained producer Module, not a synthetic RowProved base
    // or evidence that the current compiler/row/kernel integration succeeded.
    const ORIGINAL: &[u8] = include_bytes!(
        "../../trust-cg-bridge/tests/fixtures/direct_ir_observation/original-module.bin"
    );

    fn original() -> (trust_ir::Module, CalculusRowClaim) {
        let (module, wire) = trust_ir::binary::deserialize_module_with_wire_version(ORIGINAL).unwrap();
        assert!(trust_ir_build::validate_module_as_decoded(&module, wire).is_empty());
        let first = module.functions.first().unwrap();
        let claim = CalculusRowClaim {
            artifact: ORIGINAL.to_vec(), fid: u64::from(first.id.index()),
            symbol: first.name.as_bytes().to_vec(),
        };
        (module, claim)
    }

    #[test]
    fn actual_decoded_module_joins_the_exact_function_id_and_symbol() {
        let (module, mut claim) = original();
        assert!(binding_matches(&module, &claim));
        assert_eq!(decoded_module(&claim)["unique_reciprocal_claim_binding"], true);
        claim.fid = u64::MAX;
        assert!(!binding_matches(&module, &claim));
        let (_, mut claim) = original(); claim.symbol.push(0);
        assert!(!binding_matches(&module, &claim));
    }

    #[test]
    fn duplicate_decoded_identity_never_yields_a_reciprocal_binding() {
        let (mut module, claim) = original();
        module.functions.push(module.functions[0].clone());
        assert!(!binding_matches(&module, &claim));
    }

    #[test]
    fn truncated_original_is_decode_refusal_not_a_semantic_counterexample() {
        let (_, mut claim) = original();
        claim.artifact.truncate(claim.artifact.len() / 2);
        let value = decoded_module(&claim);
        assert_eq!(value["state"], "decode_refused");
        assert!(value.get("unique_reciprocal_claim_binding").is_none());
    }

    #[test]
    fn typed_refusal_tags_do_not_count_resource_or_unknown_constant_errors_as_semantic_negatives() {
        use clean_kernel::{Expr, name::Name};
        // Construct error DATA only, never a kernel token or favorable verdict.
        let errors = [
            (TypeError::TypeMismatch {
                expected: Box::new(Expr::nat_lit(0)), inferred: Box::new(Expr::nat_lit(1)),
                location: None,
            }, "type_mismatch"),
            (TypeError::HeartbeatExceeded { limit: 1, profile: None }, "heartbeat_exhausted"),
            (TypeError::UnknownConst(Name::from_string("missing")), "unknown_constant"),
        ];
        for (source, expected) in errors {
            let row = Vf5JudgmentObservation::Refused(Vf5HintMiss::Row(CalculusRowMiss::Refused(
                ReferenceRefusal::Kernel(EnvError::TypeCheckFailed {
                    name: Name::from_string("observation"), source,
                }),
            )));
            let value = observation(&row);
            assert_eq!(value["reference_refusal_kind"], expected);
            assert_eq!(value["semantic_negative_credit"], false);
        }
    }
}

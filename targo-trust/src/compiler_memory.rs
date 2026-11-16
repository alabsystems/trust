// Compiler memory-lifecycle observations retained beside a verification report.
// These counters are diagnostic data, never proof or resource-admission authority.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fs::File;
use std::io::{self, Write};
use std::path::Path;

use serde::Serialize;
use sha2::{Digest, Sha256};
use trust_types::{CoverageTransportSummary, MemorySummary};

use crate::pipeline::transport::CargoTargetIdentity;

pub(crate) const FILE_NAME: &str = "compiler-memory.json";
const SCHEMA: &str = "trust.compiler-memory-observations.v1";

/// One compiler coverage summary, retaining the Cargo envelope that named it.
/// A direct compiler run has no Cargo target; absence is explicit, not inferred
/// from a crate name shared by several compilation units.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct CompilerMemoryObservation {
    cargo_target: Option<CargoTargetIdentity>,
    crate_name: String,
    package_name: String,
    memory: MemorySummary,
}

impl CompilerMemoryObservation {
    pub(crate) fn cargo(target: &CargoTargetIdentity, coverage: &CoverageTransportSummary) -> Self {
        Self { cargo_target: Some(target.clone()), ..Self::direct(coverage) }
    }

    pub(crate) fn direct(coverage: &CoverageTransportSummary) -> Self {
        Self {
            cargo_target: None,
            crate_name: coverage.crate_name.clone(),
            package_name: coverage.package_name.clone(),
            memory: coverage.memory.clone(),
        }
    }
}

#[derive(Serialize)]
struct CompilerMemorySidecar<'a> {
    schema: &'static str,
    authority: &'static str,
    scope: &'static str,
    proof_report_hash: String,
    units: &'a [CompilerMemoryObservation],
}

/// Write into the report's private staging directory. The bundle transaction
/// installs this file with the report it names, and retires it when a later
/// producer supplies no observations. Missing counters remain missing in the
/// original MemorySummary; no zero filling or aggregation occurs here.
pub(crate) fn write_sidecar(
    staged_root: &Path,
    canonical_report: &[u8],
    units: &[CompilerMemoryObservation],
) -> io::Result<()> {
    let sidecar = CompilerMemorySidecar {
        schema: SCHEMA,
        authority: "observational_only_no_proof_credit",
        scope: "compiler_coverage_summaries_not_process_memory_or_admission",
        proof_report_hash: format!(
            "sha256:{}",
            trust_types::digest::lowercase_hex(&Sha256::digest(canonical_report))
        ),
        units,
    };
    let mut file = File::create(staged_root.join(FILE_NAME))?;
    serde_json::to_writer_pretty(&mut file, &sidecar).map_err(io::Error::other)?;
    file.write_all(b"\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn coverage() -> CoverageTransportSummary {
        CoverageTransportSummary {
            crate_name: "same_name".to_string(),
            package_name: "same-name".to_string(),
            primary_package: true,
            verification_session: "private-session-must-not-leak".to_string(),
            eligible: 3,
            processed: 3,
            function_identities: None,
            noted_stops: Vec::new(),
            degraded_anchors: 0,
            memory: MemorySummary::new([
                (MemorySummary::SLOTS_COMPACTED.to_string(), 3),
                ("future_allocator_counter".to_string(), 9),
            ]),
        }
    }

    fn target(kind: &str, index: u64) -> CargoTargetIdentity {
        CargoTargetIdentity {
            package_id: "path+file:///fixture#same-name@0.1.0".to_string(),
            package_name: "same-name".to_string(),
            target_name: "same_name".to_string(),
            target_kinds: vec![kind.to_string()],
            compile_target: "aarch64-apple-darwin".to_string(),
            compile_mode: "check".to_string(),
            compile_kind: "host".to_string(),
            unit_identity_sha256: format!("{index:064x}"),
            compile_target_spec_sha256: None,
            proof_unit_index: index,
            proof_unit_mode: "check".to_string(),
            proof_unit_role: "primary".to_string(),
            semantics_sha256: format!("{:064x}", index + 10),
        }
    }

    #[test]
    fn same_named_cargo_units_keep_their_distinct_identities() {
        let coverage = coverage();
        let units = [
            CompilerMemoryObservation::cargo(&target("lib", 1), &coverage),
            CompilerMemoryObservation::cargo(&target("bin", 2), &coverage),
        ];
        let value = serde_json::to_value(&units).expect("serialize observations");
        assert_eq!(value.as_array().unwrap().len(), 2);
        assert_eq!(value[0]["cargo_target"]["target_kinds"][0], "lib");
        assert_eq!(value[1]["cargo_target"]["target_kinds"][0], "bin");
        assert_ne!(
            value[0]["cargo_target"]["unit_identity_sha256"],
            value[1]["cargo_target"]["unit_identity_sha256"]
        );
        assert_ne!(
            value[0]["cargo_target"]["semantics_sha256"],
            value[1]["cargo_target"]["semantics_sha256"]
        );
    }

    #[test]
    fn missing_and_future_counters_survive_without_zero_filling() {
        let value = serde_json::to_value(CompilerMemoryObservation::direct(&coverage()))
            .expect("serialize direct observation");
        assert!(value["cargo_target"].is_null());
        assert_eq!(value["memory"]["schema"], trust_types::MEMORY_SUMMARY_SCHEMA_V1);
        let counters = value["memory"]["counters"].as_object().unwrap();
        assert_eq!(counters[MemorySummary::SLOTS_COMPACTED], 3);
        assert_eq!(counters["future_allocator_counter"], 9);
        assert!(!counters.contains_key(MemorySummary::CONTEXTS_RELEASED));
        assert!(!value.to_string().contains("private-session-must-not-leak"));
    }

    #[test]
    fn sidecar_names_exact_report_bytes_and_claims_no_proof_authority() {
        let temp = tempfile::tempdir().expect("staging directory");
        let report = b"{\"authority\":\"untrusted_observational_only_no_proof_credit\"}\n";
        write_sidecar(temp.path(), report, &[CompilerMemoryObservation::direct(&coverage())])
            .expect("write sidecar");
        let value: serde_json::Value = serde_json::from_slice(
            &std::fs::read(temp.path().join(FILE_NAME)).expect("read sidecar"),
        )
        .expect("parse sidecar");
        assert_eq!(value["schema"], SCHEMA);
        assert_eq!(value["authority"], "observational_only_no_proof_credit");
        assert_eq!(
            value["proof_report_hash"],
            format!("sha256:{}", trust_types::digest::lowercase_hex(&Sha256::digest(report)))
        );
        assert_ne!(
            value["proof_report_hash"],
            format!("sha256:{}", trust_types::digest::lowercase_hex(&Sha256::digest(b"changed")))
        );
        assert_eq!(value["units"].as_array().unwrap().len(), 1);
    }
}

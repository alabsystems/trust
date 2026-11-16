// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Explicit legacy candidate intake, never historical identity reconstruction.

use super::super::identity::LegacyCompilerIdentity;
use super::*;

const CASE_V1: &str = "trust.source-case-set/v1";
const PROPERTY_V1: &str = "trust.source-property-set/v1";

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct LegacyInputs {
    source: PathBuf,
    source_sha256: String,
    compiler: LegacyCompilerIdentity,
    source_path_policy: String,
    extraction_flags: Vec<String>,
    suite: Suite,
    module_sha256: String,
    function_id: u32,
}

impl From<&CaseInputs> for LegacyInputs {
    fn from(current: &CaseInputs) -> Self {
        Self {
            source: current.source.clone(),
            source_sha256: current.source_sha256.clone(),
            compiler: current.compiler.legacy_keys(),
            source_path_policy: current.source_path_policy.clone(),
            extraction_flags: current.extraction_flags.clone(),
            suite: current.suite.clone(),
            module_sha256: current.module_sha256.clone(),
            function_id: current.function_id,
        }
    }
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct LegacyManifest {
    schema: String,
    inputs: LegacyInputs,
    certificates: Vec<CaseArtifact>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct LegacyPropertyManifest {
    schema: String,
    api_schema: String,
    inputs: LegacyInputs,
    certificates: Vec<CaseArtifact>,
}

/// Only complete known-v1 inventories enter this explicit route. Every old
/// input key must match; omitted target-library history is never filled in.
pub(in super::super) struct ImportedProofCandidates {
    directory: PathBuf,
    cases: LegacyManifest,
    properties: LegacyPropertyManifest,
    case_manifest: Vec<u8>,
    property_manifest: Vec<u8>,
    case_digest: String,
    property_digest: String,
}

impl ImportedProofCandidates {
    pub(in super::super) fn load(
        directory: &Path,
        current: &CaseInputs,
    ) -> Result<Self, Box<dyn Error>> {
        let case_manifest = read_regular(&directory.join("case-set.json"), MANIFEST_LIMIT)?;
        let property_manifest =
            read_regular(&directory.join("source-property-set.json"), MANIFEST_LIMIT)?;
        let cases: LegacyManifest = serde_json::from_slice(&case_manifest)?;
        let properties: LegacyPropertyManifest = serde_json::from_slice(&property_manifest)?;
        let expected = LegacyInputs::from(current);
        if cases.schema != CASE_V1
            || properties.schema != PROPERTY_V1
            || properties.api_schema
                != trust_spec_temporal::INVARIANT_MODEL_PROGRAM_PROPERTY_SCHEMA_V1
            || cases.inputs != expected
            || properties.inputs != expected
        {
            return Err(failure(
                "legacy proof candidates differ in schema, API or a recorded source/compiler/recipe/suite/module key",
            ));
        }
        inventory(&cases.certificates, current.suite.cases.len())?;
        inventory(&properties.certificates, current.suite.cases.len())?;
        Ok(Self {
            directory: directory.to_owned(),
            cases,
            properties,
            case_digest: sha256(&case_manifest),
            property_digest: sha256(&property_manifest),
            case_manifest,
            property_manifest,
        })
    }

    pub(in super::super) fn case_manifest_sha256(&self) -> &str {
        &self.case_digest
    }
    pub(in super::super) fn property_manifest_sha256(&self) -> &str {
        &self.property_digest
    }

    /// Preserve exactly the admitted old manifests before any kernel call.
    pub(in super::super) fn capture_provenance(&self, output: &Path) -> Result<(), Box<dyn Error>> {
        write_new(&output.join("imported-case-set.v1.json"), &self.case_manifest)?;
        write_new(&output.join("imported-source-property-set.v1.json"), &self.property_manifest)?;
        write_new(
            &output.join("import-provenance.json"),
            &serde_json::to_vec_pretty(&serde_json::json!({
                "schema": "trust.source-proof-candidate-import/v1",
                "prior_directory": self.directory,
                "case_manifest_sha256": self.case_digest,
                "source_property_manifest_sha256": self.property_digest,
                "authority": "untrusted-candidate-data",
                "fresh_current_kernel_replay_required": true,
                "historical_target_library_inventory": "unavailable"
            }))?,
        )
    }

    pub(in super::super) fn read_case(&self, index: usize) -> Result<Vec<u8>, Box<dyn Error>> {
        self.read(index, false)
    }

    pub(in super::super) fn read_property(&self, index: usize) -> Result<Vec<u8>, Box<dyn Error>> {
        self.read(index, true)
    }

    fn read(&self, index: usize, property: bool) -> Result<Vec<u8>, Box<dyn Error>> {
        let descriptors =
            if property { &self.properties.certificates } else { &self.cases.certificates };
        let descriptor = descriptors.get(index).ok_or("import candidate index absent")?;
        let name = if property {
            format!("source-refinement-{index}.json")
        } else {
            format!("case-{index}.json")
        };
        let bytes = read_regular(&self.directory.join(&name), CERTIFICATE_LIMIT)?;
        if sha256(&bytes) != descriptor.sha256 {
            return Err(failure(format!("imported {name} differs from its recorded digest")));
        }
        Ok(bytes)
    }
}

#[cfg(all(test, unix))]
#[path = "import/tests.rs"]
mod tests;

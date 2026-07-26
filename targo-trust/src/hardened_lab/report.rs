use std::path::PathBuf;

use serde::Serialize;

use crate::source_analysis::{StandaloneVc, VcKind};

pub(super) const SCHEMA_VERSION: &str = "trust.hardened_lab.v1";

#[derive(Debug, Serialize)]
pub(super) struct LabReport {
    pub(super) schema_version: &'static str,
    pub(super) analyzer: &'static str,
    pub(super) manifest_path: String,
    pub(super) raw_analyzer_command: String,
    pub(super) summary: LabSummary,
    pub(super) claims_passed: bool,
    pub(super) claims: Vec<ClaimResult>,
    pub(super) walkthroughs_passed: bool,
    pub(super) walkthroughs: Vec<WalkthroughExecution>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(super) vcs: Option<Vec<StandaloneVc>>,
}

#[derive(Debug, Serialize)]
pub(super) struct LabSummary {
    pub(super) files_analyzed: usize,
    pub(super) functions_found: usize,
    pub(super) total_vcs: usize,
    pub(super) failed: usize,
    pub(super) hardened_vcs: usize,
    pub(super) claims_total: usize,
    pub(super) claims_passed: usize,
    pub(super) claims_failed: usize,
    pub(super) walkthroughs_total: usize,
    pub(super) walkthroughs_passed: usize,
    pub(super) walkthroughs_failed: usize,
}

#[derive(Debug, Serialize)]
pub(super) struct ClaimResult {
    pub(super) id: &'static str,
    pub(super) category: &'static str,
    pub(super) report_label: &'static str,
    pub(super) title: &'static str,
    pub(super) kind: VcKind,
    pub(super) standalone_binding: String,
    pub(super) required_fragment: Option<&'static str>,
    pub(super) source_example: &'static str,
    pub(super) source_reference: &'static str,
    pub(super) passed: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(super) failure_message: Option<String>,
    pub(super) matches: Vec<ClaimMatch>,
    pub(super) walkthrough_evidence: Vec<ClaimWalkthroughEvidence>,
}

#[derive(Debug, Serialize)]
pub(super) struct ClaimMatch {
    pub(super) function: String,
    pub(super) file: String,
    pub(super) description: String,
}

#[derive(Debug, Serialize)]
pub(super) struct ClaimWalkthroughEvidence {
    pub(super) bin: &'static str,
    pub(super) requirements: Vec<ClaimTranscriptRequirement>,
    pub(super) passed: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(super) failure_message: Option<String>,
}

#[derive(Debug, Serialize)]
pub(super) struct ClaimTranscriptRequirement {
    pub(super) key: &'static str,
    pub(super) value: &'static str,
    pub(super) found: bool,
}

#[derive(Debug, Clone)]
pub(super) struct WalkthroughBin {
    pub(super) name: String,
    pub(super) source: PathBuf,
}

#[derive(Debug, Serialize)]
pub(super) struct WalkthroughExecution {
    pub(super) bin: String,
    pub(super) source: String,
    pub(super) command: String,
    pub(super) working_directory: String,
    pub(super) success: bool,
    pub(super) process_success: bool,
    pub(super) transcript_passed: bool,
    pub(super) status: String,
    pub(super) status_code: Option<i32>,
    pub(super) stdout: String,
    pub(super) stderr: String,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub(super) transcript_errors: Vec<String>,
}

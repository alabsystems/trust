use serde::{Deserialize, Serialize};
use serde_json::Value;
use trust_release::{EvidenceProfile, ExitCodeKind, GateReport, GateStatus};
use trust_version::{BoundTools, TrustVersionIdentity};

pub(super) const RELEASE_REPORT_SCHEMA: &str = "trust.release-report.v1";
pub(super) const CANDIDATE_COMMAND_VERSION: u32 = 1;
pub(super) const PRODUCT_COMPONENT_TRUSTC: &str = "trustc compiler";
pub(super) const PRODUCT_COMPONENT_TARGO: &str = "targo frontend";
pub(super) const PRODUCT_COMPONENT_TARGO_TRUST: &str = "targo-trust subcommand implementation";

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub(super) enum ReleaseProfile {
    Metadata,
    Publication,
    ProductProof,
}

impl ReleaseProfile {
    pub(super) fn parse(value: &str) -> Option<Self> {
        match value {
            "metadata" => Some(Self::Metadata),
            "publication" => Some(Self::Publication),
            "product-proof" => Some(Self::ProductProof),
            _ => None,
        }
    }

    pub(super) fn label(self) -> &'static str {
        match self {
            Self::Metadata => "metadata",
            Self::Publication => "publication",
            Self::ProductProof => "product-proof",
        }
    }

    pub(super) fn evidence_profile(self, visibility: ReleaseVisibility) -> EvidenceProfile {
        match visibility {
            ReleaseVisibility::Private => EvidenceProfile::Local,
            ReleaseVisibility::Public => match self {
                Self::Metadata => EvidenceProfile::Metadata,
                Self::Publication | Self::ProductProof => EvidenceProfile::Public,
            },
        }
    }

    pub(super) fn requires_bound_tools(self) -> bool {
        matches!(self, Self::Publication | Self::ProductProof)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub(super) enum ReleaseVisibility {
    Private,
    Public,
}

impl ReleaseVisibility {
    pub(super) fn parse(value: &str) -> Option<Self> {
        match value {
            "private" => Some(Self::Private),
            "public" => Some(Self::Public),
            _ => None,
        }
    }

    pub(super) fn label(self) -> &'static str {
        match self {
            Self::Private => "private",
            Self::Public => "public",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub(super) enum ReleaseEvidenceMode {
    DiagnosticOnly,
    GoldenPath,
}

impl ReleaseEvidenceMode {
    pub(super) fn for_release_check(
        profile: ReleaseProfile,
        visibility: ReleaseVisibility,
    ) -> Self {
        if profile == ReleaseProfile::ProductProof && visibility == ReleaseVisibility::Public {
            Self::GoldenPath
        } else {
            Self::DiagnosticOnly
        }
    }

    pub(super) fn label(self) -> &'static str {
        match self {
            Self::DiagnosticOnly => "diagnostic-only",
            Self::GoldenPath => "golden-path",
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub(super) struct ReleaseEvidenceSemantics {
    pub(super) golden_path: bool,
    pub(super) claim: &'static str,
    pub(super) reason: &'static str,
}

impl ReleaseEvidenceSemantics {
    pub(super) fn for_mode(mode: ReleaseEvidenceMode) -> Self {
        match mode {
            ReleaseEvidenceMode::DiagnosticOnly => Self {
                golden_path: false,
                claim: "diagnostic-only",
                reason: "release check output is local metadata diagnostics, not golden-path release evidence",
            },
            ReleaseEvidenceMode::GoldenPath => Self {
                golden_path: true,
                claim: "golden-path",
                reason: "public product-proof release check output is eligible to carry golden-path release evidence",
            },
        }
    }
}

#[derive(Debug, Serialize)]
pub(super) struct ReleaseCheckOutput {
    pub(super) schema_version: &'static str,
    pub(super) generated_at: u64,
    pub(super) profile: ReleaseProfile,
    pub(super) visibility: ReleaseVisibility,
    pub(super) evidence_mode: ReleaseEvidenceMode,
    pub(super) release_evidence: ReleaseEvidenceSemantics,
    pub(super) status: GateStatus,
    pub(super) exit_code_kind: ExitCodeKind,
    pub(super) candidate_commit: Option<String>,
    pub(super) repo_root: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(super) gate_filter: Option<String>,
    pub(super) repo_dirty: bool,
    pub(super) repo_dirty_metadata: Value,
    pub(super) runner: ReleaseRunner,
    pub(super) runner_kind: String,
    pub(super) candidate_command: &'static str,
    pub(super) candidate_command_version: u32,
    pub(super) tools: BoundTools,
    pub(super) toolchain_surface_proof: ToolchainSurfaceProof,
    pub(super) version_identity: TrustVersionIdentity,
    pub(super) reports: Vec<GateReport>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub(super) product_proof_evidence_classes: Vec<ProductProofEvidenceClass>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub(super) product_proof_components: Vec<ProductProofComponent>,
}

#[derive(Debug, Clone, Serialize)]
pub(super) struct ReleaseRunner {
    pub(super) implementation: &'static str,
    pub(super) entrypoint: &'static str,
    pub(super) python_used: bool,
    pub(super) tool: &'static str,
    pub(super) kind: String,
}

#[derive(Debug, Serialize)]
pub(super) struct ProductProofEvidenceClass {
    pub(super) class: &'static str,
    pub(super) status: String,
    pub(super) release_claim: &'static str,
    pub(super) gates: &'static [&'static str],
    pub(super) required_evidence: &'static [&'static str],
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(super) reason: Option<String>,
}

#[derive(Debug, Serialize)]
pub(super) struct ProductProofComponent {
    pub(super) component: &'static str,
    pub(super) status: String,
    pub(super) required_evidence: &'static [&'static str],
}

#[derive(Debug, Clone, Serialize)]
pub(super) struct ToolchainSurfaceProof {
    pub(super) schema: &'static str,
    pub(super) status: &'static str,
    pub(super) same_sysroot: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(super) sysroot: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(super) bin_dir: Option<String>,
    pub(super) stage1_alias_evidence: bool,
    pub(super) required_tools: Vec<ToolchainSurfaceProofTool>,
    pub(super) optional_tools: Vec<ToolchainSurfaceProofTool>,
}

#[derive(Debug, Clone, Serialize)]
pub(super) struct ToolchainSurfaceProofTool {
    pub(super) name: String,
    pub(super) required: bool,
    pub(super) canonical_name: bool,
    pub(super) present: bool,
    pub(super) same_sysroot: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(super) path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(super) sysroot: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(super) bin_dir: Option<String>,
    pub(super) resolution: Option<String>,
    pub(super) compatibility_aliases: Vec<ToolchainSurfaceProofAlias>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(super) detail: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub(super) struct ToolchainSurfaceProofAlias {
    pub(super) name: String,
    pub(super) present: bool,
    pub(super) same_sysroot: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(super) path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(super) detail: Option<String>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ProductProofManifest {
    #[serde(default)]
    pub(super) schema_version: Option<String>,
    #[serde(default)]
    pub(super) status: Option<String>,
    #[serde(default)]
    pub(super) reason: Option<String>,
    #[serde(default, rename = "release_artifact_binding")]
    pub(super) _release_artifact_binding: Option<toml::Value>,
    #[serde(default)]
    pub(super) evidence_classes: Vec<ProductProofManifestEvidenceClass>,
    #[serde(default)]
    pub(super) components: Vec<ProductProofManifestComponent>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ProductProofManifestEvidenceClass {
    pub(super) class: String,
    pub(super) status: String,
    #[serde(default)]
    pub(super) reason: Option<String>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ProductProofManifestComponent {
    pub(super) component: String,
    pub(super) status: String,
    #[serde(default)]
    pub(super) reason: Option<String>,
    #[serde(default)]
    pub(super) evidence: Vec<String>,
}

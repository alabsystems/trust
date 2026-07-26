use std::path::{Path, PathBuf};

use cargo_util::Sha256;
use cargo_util_schemas::core::PackageIdSpec;
use serde::Serialize;
use serde::ser;
use serde_json::value::RawValue;

use crate::core::Target;

// Trust: this file defines Cargo's public JSON schema, so the Trust extension
// is additive and every added field is `skip_serializing_if = "Option::is_none"`
// — plain Cargo emits byte-identical output, which is what lets unmodified
// ecosystem tooling keep parsing it.
//
// The additions exist because Cargo's envelope names a *package target*, while
// evidence has to name an exact compilation: the same target is compiled for
// several triples, modes, feature sets, and profiles within one run, and those
// artifacts are indistinguishable in upstream's schema. Schema constants are
// versioned rather than implicit so a consumer can refuse an envelope it does
// not understand instead of silently reading a renamed field.
pub const TRUST_PROOF_UNIT_SCHEMA_V1: &str = "targo.trust-proof-unit.v1";
pub const TRUST_PROOF_INVENTORY_SCHEMA_V1: &str = "targo.trust-proof-inventory.v1";
pub const TRUST_PROOF_UNIT_SCHEMA_V2: &str = "targo.trust-proof-unit.v2";
pub const TRUST_PROOF_INVENTORY_SCHEMA_V2: &str = "targo.trust-proof-inventory.v2";
pub const TRUST_UNIT_SEMANTICS_SCHEMA_V1: &str = "targo.trust-unit-semantics.v1";
pub const TRUST_EXCLUSION_DEPENDENCY_POLICY: &str = "dependency-policy-excluded";
pub const TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION: &str = "build-script-execution";
pub const TRUST_EXCLUSION_DEFERRED_DOCTEST: &str = "deferred-doctest-execution";
pub const TRUST_EXCLUSION_COMPILE_TIME_DEPS_FILTERED: &str = "compile-time-deps-filtered";
pub const TRUST_EXCLUSION_DOCUMENTATION: &str = "documentation-generation";

/// Cargo-owned identity for one exact compiler unit admitted to Targo's proof
/// subject. This is omitted by ordinary Cargo and by verified Targo units that
/// are neither resolved roots, test-graph execution subjects, nor dependency
/// subjects explicitly requested by `--trust-include-dependencies`.
#[derive(Clone, Debug, Serialize)]
pub struct TrustProofUnit {
    pub schema: &'static str,
    pub index: u64,
    pub mode: &'static str,
    pub role: &'static str,
    pub package_name: String,
    /// SHA-256 of the canonical closed-schema [`TrustUnitSemantics`] attached
    /// to this Unit in the invocation inventory. Repeating the digest in every
    /// compiler-message and artifact envelope prevents an artifact from being
    /// replayed under a different feature/profile/compiler configuration.
    pub semantics_sha256: String,
}

/// Closed, compilation-relevant Cargo profile projection. This intentionally
/// does not serialize `Profile` directly: adding an upstream Cargo field must
/// be an explicit Trust schema decision instead of silently changing an
/// authoritative digest.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct TrustUnitProfileSemantics {
    pub opt_level: String,
    /// The requested profile LTO value (`off`, `false`, `true`, or a named
    /// rustc value), before Cargo's graph-wide effective-LTO calculation.
    pub requested_lto: String,
    /// Cargo's graph-resolved LTO action for this exact Unit.
    pub effective_lto: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub codegen_backend: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub codegen_units: Option<u32>,
    pub debuginfo: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub split_debuginfo: Option<String>,
    pub debug_assertions: bool,
    pub overflow_checks: bool,
    pub rpath: bool,
    pub incremental: bool,
    pub panic: String,
    pub strip: String,
    /// Ordered profile-level rustflags; order and duplicates are preserved
    /// because rustc option precedence is order-sensitive.
    pub rustflags: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trim_paths: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub hint_mostly_unused: Option<bool>,
}

/// Identity of the compiler frontend/backend whose semantics were selected by
/// Cargo for one Unit. The version digest binds the complete canonical `-vV`
/// response without making a multiline implementation string part of every
/// inventory record.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct TrustUnitCompilerSemantics {
    /// `rustc`, `rustdoc`, or `cargo-control` for a non-compiler queue entry.
    pub frontend: &'static str,
    /// Canonical effective codegen backend, or `not-applicable` for a Cargo
    /// control entry. `rustc-default` is explicit rather than represented by
    /// a missing field.
    pub codegen_backend: String,
    pub rustc_release: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rustc_commit_hash: Option<String>,
    pub rustc_host: String,
    pub rustc_verbose_version_sha256: String,
}

/// Canonical, closed projection of one Cargo-resolved Unit configuration.
///
/// Set-like fields are strictly sorted and duplicate-free. Argument vectors
/// retain their exact order. The latter must not be sorted: later rustc flags
/// can override earlier ones, so ordering is part of compilation semantics.
/// This descriptor deliberately does not claim to bind source bytes,
/// dependency adjacency or `--extern` artifact identities, late build-script
/// output, or proc-macro behavior. Those require separate authorities.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct TrustUnitSemantics {
    pub schema: &'static str,
    pub features: Vec<String>,
    pub target_cfg: Vec<String>,
    pub cfg_test: bool,
    pub target_edition: String,
    pub target_crate_types: Vec<String>,
    pub target_harness: bool,
    pub target_proc_macro: bool,
    pub profile: TrustUnitProfileSemantics,
    pub compiler: TrustUnitCompilerSemantics,
    /// Ordered target/config/environment rustflags after removing only Trust
    /// transport nonces and output locations. Compilation and verification
    /// policy flags remain exact.
    pub unit_rustflags: Vec<String>,
    /// Ordered manifest lint arguments that Cargo will actually pass.
    pub manifest_lint_rustflags: Vec<String>,
    /// Ordered `cargo rustc`/`cargo rustdoc` trailing arguments.
    pub extra_compiler_args: Vec<String>,
}

impl TrustUnitSemantics {
    pub fn validate_canonical(&self) -> Result<(), String> {
        if self.schema != TRUST_UNIT_SEMANTICS_SCHEMA_V1 {
            return Err(format!(
                "unsupported Trust Unit semantics schema {:?}",
                self.schema
            ));
        }
        require_strictly_sorted("features", &self.features)?;
        require_strictly_sorted("target_cfg", &self.target_cfg)?;
        require_strictly_sorted("target_crate_types", &self.target_crate_types)?;
        Ok(())
    }

    pub fn sha256(&self) -> Result<String, String> {
        self.validate_canonical()?;
        let canonical = serde_json::to_vec(self)
            .map_err(|error| format!("cannot serialize Trust Unit semantics: {error}"))?;
        Ok(Sha256::new().update(&canonical).finish_hex())
    }
}

fn require_strictly_sorted(label: &str, values: &[String]) -> Result<(), String> {
    if let Some(pair) = values.windows(2).find(|pair| pair[0] >= pair[1]) {
        return Err(format!(
            "Trust Unit semantics {label} must be strictly sorted and duplicate-free; found {:?} before {:?}",
            pair[0], pair[1]
        ));
    }
    Ok(())
}

/// One exact Cargo graph unit in the invocation-wide Trust proof inventory.
/// The target fields are deliberately repeated outside compiler diagnostics so
/// the proof consumer can require set equality even when a compiler never
/// starts, crashes before its first diagnostic, or replays a fresh artifact.
#[derive(Debug, Serialize)]
pub struct TrustProofInventoryUnit {
    pub trust_proof_unit: TrustProofUnit,
    pub semantics: TrustUnitSemantics,
    pub package_id: PackageIdSpec,
    pub target_name: String,
    pub target_kinds: Vec<String>,
    pub compile_target: String,
    /// Exact legacy Cargo compile-mode identity, repeated outside the nested
    /// proof-unit descriptor so consumers can cross-bind both authenticated
    /// identity lanes before admitting compiler evidence.
    pub trust_compile_mode: &'static str,
    /// Exact host-vs-target Cargo compile context.
    pub trust_compile_kind: &'static str,
    /// SHA-256 of Cargo's complete semantic unit identity, including
    /// dependency and artifact context not represented by target metadata.
    pub trust_unit_identity_sha256: String,
    /// Exact SHA-256 of custom JSON target bytes. Built-in target tuples omit
    /// this because their semantics are supplied by the authenticated rustc.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub compile_target_spec_sha256: Option<String>,
}

/// One resolved Cargo unit deliberately outside the invocation's proof
/// subject. This lets dependency-TCB reporting identify exact excluded units
/// instead of inferring them from package names or Cargo.lock.
#[derive(Debug, Serialize)]
pub struct TrustExcludedUnit {
    pub index: u64,
    pub mode: &'static str,
    /// Cargo-owned relationship to the requested execution graph. This keeps
    /// an excluded requested root distinguishable from an optional dependency
    /// and prevents package-level siblings from masking it.
    pub graph_role: &'static str,
    pub package_id: PackageIdSpec,
    pub package_name: String,
    pub target_name: String,
    pub target_kinds: Vec<String>,
    pub compile_target: String,
    pub trust_compile_mode: &'static str,
    pub trust_compile_kind: &'static str,
    pub trust_unit_identity_sha256: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub compile_target_spec_sha256: Option<String>,
    /// Why this resolved graph unit cannot or must not emit compiler proof.
    /// Policy exclusions are conditional dependency-TCB inputs; execution-only
    /// reasons identify Cargo control jobs that do not invoke rustc/rustdoc on
    /// this queue entry and therefore cannot appear in compiler transport.
    pub exclusion_reason: &'static str,
    pub semantics_sha256: String,
    /// Excluded graph entries still affect the build and dependency-TCB
    /// boundary. Preserve their exact feature/profile/compiler configuration
    /// instead of reducing them to a package name and reason.
    pub semantics: TrustUnitSemantics,
}

/// Targo-owned, invocation-wide declaration of the complete proof subject.
/// Cargo emits this exactly once before executing any unit in a verified JSON
/// invocation. Per-compiler envelopes must be an exact subset during the run
/// and an exact match after a successful build.
#[derive(Debug, Serialize)]
pub struct TrustProofInventory {
    pub schema: &'static str,
    pub include_dependencies: bool,
    pub units: Vec<TrustProofInventoryUnit>,
    pub excluded_units: Vec<TrustExcludedUnit>,
}

impl Message for TrustProofInventory {
    fn reason(&self) -> &str {
        "trust-proof-inventory"
    }
}

pub trait Message: ser::Serialize {
    fn reason(&self) -> &str;

    fn to_json_string(&self) -> String {
        #[derive(Serialize)]
        struct WithReason<'a, S: Serialize> {
            reason: &'a str,
            #[serde(flatten)]
            msg: &'a S,
        }
        let with_reason = WithReason {
            reason: self.reason(),
            msg: &self,
        };
        serde_json::to_string(&with_reason).unwrap()
    }
}

#[derive(Serialize)]
pub struct FromCompiler<'a> {
    pub package_id: PackageIdSpec,
    pub manifest_path: &'a Path,
    pub target: &'a Target,
    /// Targo-only Trust extension: the exact target string passed to rustc for
    /// this unit, or the selected compiler's host triple for a host unit. Plain
    /// Cargo omits it to preserve Cargo's public JSON schema byte-for-shape.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trust_compile_target: Option<&'a str>,
    /// Exact SHA-256 of a custom JSON target specification's bytes. Built-in
    /// target tuples omit this field because their semantics are supplied by
    /// the already-authenticated compiler binary.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trust_compile_target_spec_sha256: Option<&'a str>,
    /// Targo-only exact Cargo unit mode. Target metadata alone does not
    /// distinguish (for example) a normal library from its `cfg(test)` view.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trust_compile_mode: Option<&'a str>,
    /// Targo-only Cargo compile context (`host` or `target`). A target unit for
    /// the host triple is still semantically distinct from a host unit.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trust_compile_kind: Option<&'a str>,
    /// Targo-only SHA-256 over Cargo's semantic unit context (package,
    /// target, mode, profile, features, dependency hash, and rustflags).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trust_unit_identity_sha256: Option<&'a str>,
    /// Exact resolved Cargo unit and its proof-subject role.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trust_proof_unit: Option<&'a TrustProofUnit>,
    pub message: Box<RawValue>,
}

impl<'a> Message for FromCompiler<'a> {
    fn reason(&self) -> &str {
        "compiler-message"
    }
}

#[derive(Serialize)]
pub struct Artifact<'a> {
    pub package_id: PackageIdSpec,
    pub manifest_path: PathBuf,
    pub target: &'a Target,
    /// Targo-only Trust extension paired with compiler-message envelopes so
    /// evidence can distinguish otherwise identical targets compiled for two
    /// triples. Plain Cargo omits it.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trust_compile_target: Option<&'a str>,
    /// Post-compile byte identity for a custom JSON target specification. The
    /// proof consumer requires it to equal every compiler-message snapshot for
    /// this Cargo target, detecting persistent same-path spec mutation.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trust_compile_target_spec_sha256: Option<&'a str>,
    /// Targo-only exact Cargo unit mode, paired with compiler-message
    /// envelopes so proof completion cannot be borrowed across fresh contexts.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trust_compile_mode: Option<&'a str>,
    /// Targo-only Cargo compile context (`host` or `target`).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trust_compile_kind: Option<&'a str>,
    /// Targo-only semantic Cargo unit identity paired with compiler messages.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trust_unit_identity_sha256: Option<&'a str>,
    /// Targo-only byte identity captured while Cargo still owns the build
    /// lifecycle for this executable.  The outer verifier compares this with
    /// its post-phase-A hash before it can authorize test execution.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trust_executable_sha256: Option<String>,
    /// Same proof-unit identity carried by every compiler-message envelope for
    /// this artifact. Targo requires exact equality before publication.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trust_proof_unit: Option<&'a TrustProofUnit>,
    pub profile: ArtifactProfile,
    pub features: Vec<String>,
    pub filenames: Vec<PathBuf>,
    pub executable: Option<PathBuf>,
    pub fresh: bool,
}

impl<'a> Message for Artifact<'a> {
    fn reason(&self) -> &str {
        "compiler-artifact"
    }
}

/// This is different from the regular `Profile` to maintain backwards
/// compatibility (in particular, `test` is no longer in `Profile`, but we
/// still want it to be included here).
#[derive(Serialize)]
pub struct ArtifactProfile {
    pub opt_level: &'static str,
    pub debuginfo: Option<ArtifactDebuginfo>,
    pub debug_assertions: bool,
    pub overflow_checks: bool,
    pub test: bool,
}

/// Internally this is an enum with different variants, but keep using 0/1/2 as integers for compatibility.
#[derive(Serialize)]
#[serde(untagged)]
pub enum ArtifactDebuginfo {
    Int(u32),
    Named(&'static str),
}

#[derive(Serialize)]
pub struct BuildScript<'a> {
    pub package_id: PackageIdSpec,
    pub linked_libs: &'a [String],
    pub linked_paths: &'a [String],
    pub cfgs: &'a [String],
    pub env: &'a [(String, String)],
    pub out_dir: &'a Path,
}

impl<'a> Message for BuildScript<'a> {
    fn reason(&self) -> &str {
        "build-script-executed"
    }
}

#[derive(Serialize)]
pub struct BuildFinished {
    pub success: bool,
}

impl Message for BuildFinished {
    fn reason(&self) -> &str {
        "build-finished"
    }
}

// Trust: pins the wire shape of the additions above — that plain-Cargo
// envelopes stay free of them, and that a semantics digest fails closed on
// noncanonical input rather than hashing whatever order it was handed.
#[cfg(test)]
mod tests {
    use super::{
        Message, TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION, TRUST_PROOF_INVENTORY_SCHEMA_V2,
        TRUST_PROOF_UNIT_SCHEMA_V2, TRUST_UNIT_SEMANTICS_SCHEMA_V1, TrustExcludedUnit,
        TrustProofInventory, TrustProofInventoryUnit, TrustProofUnit, TrustUnitCompilerSemantics,
        TrustUnitProfileSemantics, TrustUnitSemantics,
    };
    use cargo_util_schemas::core::PackageIdSpec;
    use serde_json::json;

    fn semantics(features: &[&str]) -> TrustUnitSemantics {
        TrustUnitSemantics {
            schema: TRUST_UNIT_SEMANTICS_SCHEMA_V1,
            features: features.iter().map(|value| (*value).to_string()).collect(),
            target_cfg: vec!["target_arch = \"x86_64\"".to_string(), "unix".to_string()],
            cfg_test: false,
            target_edition: "2024".to_string(),
            target_crate_types: vec!["rlib".to_string()],
            target_harness: true,
            target_proc_macro: false,
            profile: TrustUnitProfileSemantics {
                opt_level: "3".to_string(),
                requested_lto: "false".to_string(),
                effective_lto: "only-object".to_string(),
                codegen_backend: None,
                codegen_units: Some(1),
                debuginfo: "0".to_string(),
                split_debuginfo: None,
                debug_assertions: false,
                overflow_checks: true,
                rpath: false,
                incremental: false,
                panic: "abort".to_string(),
                strip: "none".to_string(),
                rustflags: Vec::new(),
                trim_paths: None,
                hint_mostly_unused: None,
            },
            compiler: TrustUnitCompilerSemantics {
                frontend: "rustc",
                codegen_backend: "trust-cg".to_string(),
                rustc_release: "1.99.0-nightly".to_string(),
                rustc_commit_hash: Some("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".to_string()),
                rustc_host: "x86_64-unknown-linux-gnu".to_string(),
                rustc_verbose_version_sha256:
                    "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc".to_string(),
            },
            unit_rustflags: vec!["-Zcodegen-backend=trust-cg".to_string()],
            manifest_lint_rustflags: Vec::new(),
            extra_compiler_args: Vec::new(),
        }
    }

    #[test]
    fn trust_proof_inventory_v2_has_a_stable_machine_schema() {
        let included_semantics = semantics(&["default", "serde"]);
        let included_semantics_sha256 = included_semantics.sha256().unwrap();
        let excluded_semantics = semantics(&[]);
        let excluded_semantics_sha256 = excluded_semantics.sha256().unwrap();
        let message = TrustProofInventory {
            schema: TRUST_PROOF_INVENTORY_SCHEMA_V2,
            include_dependencies: false,
            units: vec![TrustProofInventoryUnit {
                trust_proof_unit: TrustProofUnit {
                    schema: TRUST_PROOF_UNIT_SCHEMA_V2,
                    index: 7,
                    mode: "build",
                    role: "primary",
                    package_name: "selected".to_string(),
                    semantics_sha256: included_semantics_sha256.clone(),
                },
                semantics: included_semantics.clone(),
                package_id: PackageIdSpec::new("selected".to_string()),
                target_name: "selected".to_string(),
                target_kinds: vec!["lib".to_string(), "rlib".to_string()],
                compile_target: "/targets/custom.json".to_string(),
                trust_compile_mode: "build",
                trust_compile_kind: "target",
                trust_unit_identity_sha256:
                    "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"
                        .to_string(),
                compile_target_spec_sha256: Some(
                    "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".to_string(),
                ),
            }],
            excluded_units: vec![TrustExcludedUnit {
                index: 9,
                mode: "run-custom-build",
                graph_role: "control",
                package_id: PackageIdSpec::new("excluded".to_string()),
                package_name: "excluded".to_string(),
                target_name: "build-script-build".to_string(),
                target_kinds: vec!["custom-build".to_string()],
                compile_target: "x86_64-unknown-linux-gnu".to_string(),
                trust_compile_mode: "run-custom-build",
                trust_compile_kind: "host",
                trust_unit_identity_sha256:
                    "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee"
                        .to_string(),
                compile_target_spec_sha256: None,
                exclusion_reason: TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION,
                semantics_sha256: excluded_semantics_sha256.clone(),
                semantics: excluded_semantics.clone(),
            }],
        };

        assert_eq!(
            serde_json::from_str::<serde_json::Value>(&message.to_json_string()).unwrap(),
            json!({
                "reason": "trust-proof-inventory",
                "schema": "targo.trust-proof-inventory.v2",
                "include_dependencies": false,
                "units": [{
                    "trust_proof_unit": {
                        "schema": "targo.trust-proof-unit.v2",
                        "index": 7,
                        "mode": "build",
                        "role": "primary",
                        "package_name": "selected",
                        "semantics_sha256": included_semantics_sha256,
                    },
                    "semantics": serde_json::to_value(included_semantics).unwrap(),
                    "package_id": "selected",
                    "target_name": "selected",
                    "target_kinds": ["lib", "rlib"],
                    "compile_target": "/targets/custom.json",
                    "trust_compile_mode": "build",
                    "trust_compile_kind": "target",
                    "trust_unit_identity_sha256":
                        "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd",
                    "compile_target_spec_sha256":
                        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                }],
                "excluded_units": [{
                    "index": 9,
                    "mode": "run-custom-build",
                    "graph_role": "control",
                    "package_id": "excluded",
                    "package_name": "excluded",
                    "target_name": "build-script-build",
                    "target_kinds": ["custom-build"],
                    "compile_target": "x86_64-unknown-linux-gnu",
                    "trust_compile_mode": "run-custom-build",
                    "trust_compile_kind": "host",
                    "trust_unit_identity_sha256":
                        "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee",
                    "exclusion_reason": "build-script-execution",
                    "semantics_sha256": excluded_semantics_sha256,
                    "semantics": serde_json::to_value(excluded_semantics).unwrap(),
                }],
            })
        );
    }

    #[test]
    fn unit_semantics_digest_is_canonical_and_rejects_set_duplicates() {
        let left = semantics(&["default", "serde"]);
        let mut right = left.clone();
        assert_eq!(left.sha256().unwrap(), right.sha256().unwrap());

        right.profile.overflow_checks = false;
        assert_ne!(left.sha256().unwrap(), right.sha256().unwrap());

        let mut duplicate = left.clone();
        duplicate.features = vec!["serde".to_string(), "serde".to_string()];
        let error = duplicate
            .sha256()
            .expect_err("duplicate features must fail closed");
        assert!(
            error.contains("strictly sorted and duplicate-free"),
            "{error}"
        );

        let mut noncanonical = left;
        noncanonical.target_cfg.reverse();
        let error = noncanonical
            .sha256()
            .expect_err("noncanonical cfg ordering must fail closed");
        assert!(error.contains("target_cfg"), "{error}");
    }
}

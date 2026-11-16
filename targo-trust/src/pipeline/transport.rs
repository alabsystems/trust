// ignore-tidy-file-filelength -- pre-existing size, recorded 2026-08-21; do not grow casually
// stderr parsing: drive the compiler's JSON transport (trust_types::TRANSPORT_PREFIX)
// out of stderr lines and into VerificationResult records, with a lossy fallback for
// schema drift and a small diagnostic-level classifier for non-transport lines.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::io::{BufRead, Cursor};
use std::path::PathBuf;

use sha2::{Digest, Sha256};
use trust_types::{Counterexample, SourceSpan};

use crate::input_limits::{
    MAX_CARGO_JSON_LINE_BYTES, MAX_COMPILER_STDERR_LINE_BYTES,
    max_authenticated_cargo_transport_bytes, read_bounded_utf8_line,
};
use crate::report::CompilerDiagnostic;
use crate::types::{
    VerificationOutcome, VerificationResult, parse_trust_note, transport_to_verification_result,
};

#[cfg(unix)]
pub(crate) mod paired;

// Independent resource allowance: exhaustion withholds only resource availability.
// The pre-existing proof transport aggregate and outer framing limits are unchanged.
const MAX_NATIVE_ADMISSION_TRANSPORT_BYTES: usize = 64 * 1024 * 1024;

fn charge_native_admission_bytes(
    total: &mut usize,
    amount: usize,
    limit: usize,
) -> Result<(), String> {
    *total = total.saturating_add(amount);
    if *total > limit {
        Err("native admission transport exceeded its resource evidence allowance".into())
    } else {
        Ok(())
    }
}

fn is_native_admission_payload(json: &str) -> bool {
    // Classification observes each root tag, including duplicate tags and a
    // tag before truncation. It does not accept or normalize the payload: the
    // later direct typed parse still rejects all duplicate and unknown fields.
    // A malformed resource message must not consume the proof byte allowance.
    struct Tags<'a>(&'a mut bool);
    impl<'de> serde::de::Visitor<'de> for Tags<'_> {
        type Value = ();

        fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            formatter.write_str("a transport object")
        }

        fn visit_map<A: serde::de::MapAccess<'de>>(self, mut map: A) -> Result<(), A::Error> {
            while let Some(key) = map.next_key::<String>()? {
                if key == "type" {
                    if map.next_value::<serde_json::Value>()?.as_str()
                        == Some("native_admission_census")
                    {
                        *self.0 = true;
                    }
                } else {
                    map.next_value::<serde::de::IgnoredAny>()?;
                }
            }
            Ok(())
        }
    }
    let mut native = false;
    let _ = serde::Deserializer::deserialize_map(
        &mut serde_json::Deserializer::from_str(json),
        Tags(&mut native),
    );
    native
}

const TARGO_TRUST_PROOF_UNIT_SCHEMA_V2: &str = "targo.trust-proof-unit.v2";
const TARGO_TRUST_PROOF_INVENTORY_SCHEMA_V2: &str = "targo.trust-proof-inventory.v2";
const TARGO_TRUST_UNIT_SEMANTICS_SCHEMA_V1: &str = "targo.trust-unit-semantics.v1";
pub(crate) const TARGO_TRUST_EXCLUSION_DEPENDENCY_POLICY: &str = "dependency-policy-excluded";
pub(crate) const TARGO_TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION: &str = "build-script-execution";
pub(crate) const TARGO_TRUST_EXCLUSION_DEFERRED_DOCTEST: &str = "deferred-doctest-execution";
pub(crate) const TARGO_TRUST_EXCLUSION_COMPILE_TIME_DEPS_FILTERED: &str =
    "compile-time-deps-filtered";
pub(crate) const TARGO_TRUST_EXCLUSION_DOCUMENTATION: &str = "documentation-generation";
// Retired compiler-unit exclusions are recognized only to fail closed on an
// older producer. Include-dependencies requires these units' ordinary evidence.
pub(crate) const TARGO_TRUST_EXCLUSION_BUILD_SUPPORT_ONLY: &str = "build-support-only";
pub(crate) const TARGO_TRUST_EXCLUSION_AUDITED_TRUST_SPEC: &str = "audited-trust-spec";
/// Trust (D2d, 2026-09-28): a doctest Unit that Targo's authenticated doctest
/// census showed to contain ZERO doctests. `targo trust test` never executes
/// doctests (phase B selects `--tests`), so such a Unit defers nothing, and the
/// proof frontier must not read INCOMPLETE because of it.
///
/// Targo's inventory never DECLARES this reason — it declares every doctest
/// Unit `deferred-doctest-execution`, and a declared `empty-doctest-unit` is
/// refused. Only [`apply_doctest_census`] assigns it, to the exact declared
/// Unit a complete census names, and only for a count of zero: a Unit holding a
/// real doctest, or one whose census failed, stays deferred and disclosed.
pub(crate) const TARGO_TRUST_EXCLUSION_EMPTY_DOCTEST: &str = "empty-doctest-unit";
const TARGO_TRUST_DOCTEST_CENSUS_SCHEMA_V1: &str = "targo.trust-doctest-census.v1";

#[derive(Default)]
pub(crate) struct ParsedCompilerOutput {
    pub(crate) verification_results: Vec<VerificationResult>,
    pub(crate) compiler_diagnostics: Vec<CompilerDiagnostic>,
    /// Trust (verify-cache): total obligations replayed from the persistent proof
    /// cache across all per-function transport records (sum of
    /// `FunctionTransportResult::cached`). Informational only — the per-obligation
    /// rows stay conservatively `unknown` (no proof credit); this surfaces the
    /// honest replay count for a report-level cache hit-rate.
    pub(crate) cached_obligations: usize,
    /// Trust (assertion-grade coverage, roadmap §4.1): every `coverage_summary`
    /// transport row seen on stderr — one per verified crate/session (a
    /// multi-target run can emit several). Empty = the compiler emitted no
    /// coverage row (an OLDER toolchain): coverage UNKNOWN. The result gate
    /// rejects this absence for strict policy and permits it only in explicit
    /// compatibility/advisory lanes.
    pub(crate) coverage_rows: Vec<trust_types::CoverageTransportSummary>,
    /// Diagnostic memory counters paired with the exact authenticated Cargo
    /// envelope. Crate names alone cannot distinguish lib/bin or feature units.
    pub(crate) compiler_memory_observations: Vec<crate::compiler_memory::CompilerMemoryObservation>,
    pub(crate) native_admission_observations: Vec<crate::compiler_admission::Observation>,
    pub(crate) native_admission_problems: Vec<String>,
    /// Coverage rows the compiler DID emit that an advisory lane dropped, each
    /// with the defect that dropped it (2026-10-17). Without this record a dropped
    /// row was reported exactly like an absent one — "compiler emitted no
    /// coverage_summary transport row; older toolchain?" — which sent aterm-serde's
    /// identity defect (seven uncallable bodies credited without an envelope)
    /// looking for an old toolchain.
    pub(crate) dropped_coverage: Vec<String>,
    /// Exact per-function envelopes retained before obligation rows are
    /// flattened. Coverage authentication reconciles these identities against
    /// the compiler's versioned eligible/processed sets.
    function_envelopes: Vec<FunctionEnvelopeIdentity>,
    /// Verification nonces carried by every direct compiler function row.
    /// Normalization discards the typed wrapper, so retain this inventory until
    /// the direct-rustc channel is authenticated.
    raw_function_sessions: Vec<String>,
    /// Verification nonces carried by every direct compiler terminal summary.
    raw_crate_summary_sessions: Vec<String>,
    /// Raw compiler transport lifecycle violations retained separately from
    /// normalized obligation rows. A terminal summary cannot authorize a
    /// stream whose rows were reordered around its coverage/terminal boundary.
    raw_transport_ordering_defects: Vec<String>,
    /// End-of-compile inventories for every Cargo-owned proof unit: selected
    /// roots, test-execution subjects, and explicitly included dependencies.
    /// Function rows alone cannot prove an exact rustc unit actually finished.
    pub(crate) completed_proof_targets: BTreeSet<CargoTargetIdentity>,
    /// Proof units whose authenticated compiler channel carried a coverage
    /// inventory. Keeping exact identity prevents one complete unit's row from
    /// masking another unit's missing inventory.
    pub(crate) coverage_proof_targets: BTreeSet<CargoTargetIdentity>,
    /// Exact proof units whose authenticated coverage inventory is valid but
    /// empty. Self-verification requires a nonempty selected root while still
    /// allowing legitimate empty dependency and marker units.
    pub(crate) zero_eligible_coverage_targets: BTreeSet<CargoTargetIdentity>,
    /// Proof units authenticated by at least one compiler-owned transport
    /// envelope, including units that failed before artifact/summary emission.
    pub(crate) observed_proof_targets: BTreeSet<CargoTargetIdentity>,
    saw_structured_transport: bool,
    missing_crate_summary_scopes: Vec<TransportScopeKey>,
    /// Payload-declared summary scopes before a Cargo envelope authenticates
    /// them. This remains private and is consumed while merging one envelope
    /// target group into the final Cargo evidence.
    completed_primary_transport_scopes: BTreeSet<TransportScopeKey>,
}

/// Cargo-authenticated identity for one proof-subject rustc unit. Package names
/// and normalized crate names are not unique: package IDs distinguish package
/// instances, while target kind distinguishes same-name lib/bin targets.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, serde::Serialize)]
pub(crate) struct CargoTargetIdentity {
    pub(crate) package_id: String,
    pub(crate) package_name: String,
    pub(crate) target_name: String,
    pub(crate) target_kinds: Vec<String>,
    /// Exact Targo-authenticated rustc compile target. Unlike Cargo target
    /// name/kind, this distinguishes the same target built for two triples.
    pub(crate) compile_target: String,
    /// Exact Cargo unit mode (`build`, `test`, ...). A package target can have
    /// multiple semantically distinct views in one Cargo invocation, notably
    /// a normal library linked by integration tests and its `cfg(test)` view.
    pub(crate) compile_mode: String,
    /// Cargo host-vs-target compile context. `target(host-triple)` must not
    /// borrow proof completion from a semantically different host unit.
    pub(crate) compile_kind: String,
    /// SHA-256 over Cargo's full semantic unit context. This closes aliases
    /// between same-target/same-mode feature, profile, or dependency views.
    pub(crate) unit_identity_sha256: String,
    /// Exact SHA-256 of custom JSON target-spec bytes. Built-in target tuples
    /// have no separate digest because their semantics come from the pinned
    /// compiler binary. This prevents a stable target path from hiding changed
    /// custom-target semantics across Cargo evidence envelopes.
    pub(crate) compile_target_spec_sha256: Option<String>,
    /// Cargo-owned exact Unit index. This disambiguates the same package
    /// target compiled under cfg(test) and cfg(not(test)) in one invocation.
    pub(crate) proof_unit_index: u64,
    /// Exact Cargo CompileMode serialized by authenticated Targo.
    pub(crate) proof_unit_mode: String,
    /// `primary` for a resolved root, `test-execution` for a distinct Build-mode
    /// library or binary that a test/doctest/bench root can execute, or
    /// `dependency` for an explicitly requested dependency proof subject.
    pub(crate) proof_unit_role: String,
    /// Digest of the closed Cargo-resolved Unit configuration descriptor
    /// declared before compilation and repeated in every Cargo-owned compiler
    /// envelope. Source/dependency/dynamic-code identities are separate
    /// authorities, not implied by this digest.
    pub(crate) semantics_sha256: String,
}

impl CargoTargetIdentity {
    pub(crate) fn report_label(&self) -> String {
        format!(
            "cargo-target(package_id={:?},package={:?},kind={:?},target={:?},compile_target={:?},compile_mode={:?},compile_kind={:?},unit_identity_sha256={:?},compile_target_spec_sha256={:?},proof_unit_index={},proof_unit_mode={:?},proof_unit_role={:?},semantics_sha256={:?})",
            self.package_id,
            self.package_name,
            self.target_kinds,
            self.target_name,
            self.compile_target,
            self.compile_mode,
            self.compile_kind,
            self.unit_identity_sha256,
            self.compile_target_spec_sha256,
            self.proof_unit_index,
            self.proof_unit_mode,
            self.proof_unit_role,
            self.semantics_sha256,
        )
    }

    pub(crate) fn crate_name(&self) -> String {
        normalize_cargo_crate_name(&self.target_name)
    }

    fn scope_function(&self, function: &str) -> String {
        format!("{}::{function}", self.report_label())
    }
}

/// Cargo-owned declaration of the resolved proof frontier. `proof_targets`
/// are expected to emit compiler evidence; `excluded_targets` are active graph
/// units intentionally outside the proof and therefore exact dependency-TCB
/// inputs rather than Cargo.lock approximations.
#[derive(Debug, Clone)]
pub(crate) struct CargoProofInventory {
    pub(crate) include_dependencies: bool,
    pub(crate) proof_targets: BTreeSet<CargoTargetIdentity>,
    pub(crate) excluded_targets: BTreeSet<CargoTargetIdentity>,
    /// Exact closed-set reason authenticated alongside each excluded Unit.
    /// Keeping the complete identity as the key prevents one package-level
    /// label from masking different modes or versions in the active graph.
    pub(crate) excluded_reasons: BTreeMap<CargoTargetIdentity, String>,
    /// Cargo graph role retained before exclusion from the proof frontier.
    pub(crate) excluded_graph_roles: BTreeMap<CargoTargetIdentity, String>,
    /// Canonical closed Cargo-resolved configuration for every proof and
    /// excluded Unit. Keys
    /// include the descriptor digest, so a same-index configuration change is
    /// an identity change rather than report metadata drift.
    pub(crate) unit_semantics: BTreeMap<CargoTargetIdentity, trust_types::CargoUnitSemanticsReport>,
}

/// Build the serialized, observational projection of Cargo's exact proof-unit
/// frontier. The returned DTO is report data only; it does not carry or mint
/// live transport authority.
pub(crate) fn cargo_proof_inventory_report(
    inventory: Option<&CargoProofInventory>,
    completed_targets: &BTreeSet<CargoTargetIdentity>,
    coverage_targets: &BTreeSet<CargoTargetIdentity>,
) -> Result<Option<trust_types::CargoProofInventoryReport>, String> {
    let Some(inventory) = inventory else {
        if completed_targets.is_empty() && coverage_targets.is_empty() {
            return Ok(None);
        }
        return Err(
            "Cargo compiler evidence completed or covered proof units without a declared proof inventory"
                .to_string(),
        );
    };

    let mut declared_indices = BTreeMap::new();
    for target in inventory.proof_targets.iter().chain(&inventory.excluded_targets) {
        if let Some(previous) = declared_indices.insert(target.proof_unit_index, target) {
            return Err(format!(
                "Cargo proof report reused Unit index {} for `{}` and `{}`",
                target.proof_unit_index,
                previous.report_label(),
                target.report_label()
            ));
        }
    }
    for target in &inventory.proof_targets {
        if !cargo_unit_mode_emits_queued_compiler_evidence(&target.proof_unit_mode) {
            return Err(format!(
                "Cargo proof report declared a Unit without authenticated per-Unit compiler protocol: {}",
                target.report_label()
            ));
        }
        if target.proof_unit_role == "dependency" && !inventory.include_dependencies {
            return Err(format!(
                "Cargo proof report declared dependency Unit despite include-dependencies=false: {}",
                target.report_label()
            ));
        }
    }

    if let Some(target) = completed_targets.difference(&inventory.proof_targets).next() {
        return Err(format!(
            "completed Cargo proof unit was absent from the declared inventory: {}",
            target.report_label()
        ));
    }
    if let Some(target) = coverage_targets.difference(&inventory.proof_targets).next() {
        return Err(format!(
            "covered Cargo proof unit was absent from the declared inventory: {}",
            target.report_label()
        ));
    }

    let declared =
        cargo_proof_unit_partitions(&inventory.proof_targets, &inventory.unit_semantics)?;
    let completed = cargo_proof_unit_partitions(completed_targets, &inventory.unit_semantics)?;
    let covered = cargo_proof_unit_partitions(coverage_targets, &inventory.unit_semantics)?;
    let excluded_active_units = inventory
        .excluded_targets
        .iter()
        .map(|target| {
            if target.proof_unit_role != "excluded" {
                return Err(format!(
                    "excluded Cargo unit carried unexpected role {:?}",
                    target.proof_unit_role
                ));
            }
            let reason = inventory.excluded_reasons.get(target).ok_or_else(|| {
                format!(
                    "excluded Cargo unit omitted its authenticated exclusion reason: {}",
                    target.report_label()
                )
            })?;
            let graph_role = inventory.excluded_graph_roles.get(target).ok_or_else(|| {
                format!(
                    "excluded Cargo unit omitted its authenticated graph role: {}",
                    target.report_label()
                )
            })?;
            validate_cargo_exclusion_reason(
                inventory.include_dependencies,
                target,
                reason,
                graph_role,
            )?;
            let mut unit = cargo_proof_unit_report(target, &inventory.unit_semantics)?;
            unit.graph_role = graph_role.clone();
            unit.exclusion_reason = Some(reason.clone());
            Ok(unit)
        })
        .collect::<Result<Vec<_>, _>>()?;
    if let Some(target) = inventory
        .excluded_reasons
        .keys()
        .find(|target| !inventory.excluded_targets.contains(*target))
    {
        return Err(format!(
            "Cargo proof inventory carried an exclusion reason for an undeclared Unit: {}",
            target.report_label()
        ));
    }
    let declared_targets =
        inventory.proof_targets.union(&inventory.excluded_targets).collect::<BTreeSet<_>>();
    if let Some(target) =
        inventory.unit_semantics.keys().find(|target| !declared_targets.contains(target))
    {
        return Err(format!(
            "Cargo proof inventory carried semantics for an undeclared Unit: {}",
            target.report_label()
        ));
    }
    if let Some(target) =
        declared_targets.iter().find(|target| !inventory.unit_semantics.contains_key(**target))
    {
        return Err(format!(
            "Cargo proof inventory omitted semantics for a declared Unit: {}",
            target.report_label()
        ));
    }
    if let Some(target) = inventory
        .excluded_graph_roles
        .keys()
        .find(|target| !inventory.excluded_targets.contains(*target))
    {
        return Err(format!(
            "Cargo proof inventory carried a graph role for an undeclared excluded Unit: {}",
            target.report_label()
        ));
    }
    let excluded_active_units = sorted_cargo_proof_unit_reports(excluded_active_units)?;

    Ok(Some(trust_types::CargoProofInventoryReport {
        schema: trust_types::CARGO_PROOF_INVENTORY_REPORT_SCHEMA_V2.to_string(),
        include_dependencies: inventory.include_dependencies,
        declared,
        completed,
        covered,
        excluded_active_units,
    }))
}

fn cargo_proof_unit_partitions(
    targets: &BTreeSet<CargoTargetIdentity>,
    semantics: &BTreeMap<CargoTargetIdentity, trust_types::CargoUnitSemanticsReport>,
) -> Result<trust_types::CargoProofUnitPartitions, String> {
    let mut primary_roots = Vec::new();
    let mut test_execution_units = Vec::new();
    let mut dependency_units = Vec::new();
    for target in targets {
        let unit = cargo_proof_unit_report(target, semantics)?;
        let role = match target.proof_unit_role.as_str() {
            "primary" => &mut primary_roots,
            "test-execution" => &mut test_execution_units,
            "dependency" => &mut dependency_units,
            role => {
                return Err(format!(
                    "Cargo proof unit carried unsupported report role {role:?}: {}",
                    target.report_label()
                ));
            }
        };
        role.push(unit);
    }
    Ok(trust_types::CargoProofUnitPartitions {
        primary_roots: sorted_cargo_proof_unit_reports(primary_roots)?,
        test_execution_units: sorted_cargo_proof_unit_reports(test_execution_units)?,
        dependency_units: sorted_cargo_proof_unit_reports(dependency_units)?,
    })
}

fn sorted_cargo_proof_unit_reports(
    mut units: Vec<trust_types::CargoProofUnitReport>,
) -> Result<Vec<trust_types::CargoProofUnitReport>, String> {
    units.sort_by(|left, right| {
        left.proof_unit_index.cmp(&right.proof_unit_index).then_with(|| left.cmp(right))
    });
    if let Some(pair) = units
        .windows(2)
        .find(|pair| pair[0].proof_unit_index == pair[1].proof_unit_index && pair[0] != pair[1])
    {
        return Err(format!(
            "Cargo proof report reused Unit index {} for distinct identities",
            pair[0].proof_unit_index
        ));
    }
    Ok(units)
}

fn cargo_proof_unit_report(
    target: &CargoTargetIdentity,
    semantics: &BTreeMap<CargoTargetIdentity, trust_types::CargoUnitSemanticsReport>,
) -> Result<trust_types::CargoProofUnitReport, String> {
    let semantics = semantics.get(target).ok_or_else(|| {
        format!("Cargo proof report omitted semantic descriptor for {}", target.report_label())
    })?;
    Ok(trust_types::CargoProofUnitReport {
        package_id: target.package_id.clone(),
        package_name: target.package_name.clone(),
        target_name: target.target_name.clone(),
        target_kinds: target.target_kinds.clone(),
        compile_target: target.compile_target.clone(),
        compile_target_spec_sha256: target.compile_target_spec_sha256.clone(),
        proof_unit_index: target.proof_unit_index,
        proof_unit_mode: target.proof_unit_mode.clone(),
        proof_unit_role: target.proof_unit_role.clone(),
        graph_role: target.proof_unit_role.clone(),
        exclusion_reason: None,
        semantics_sha256: Some(target.semantics_sha256.clone()),
        semantics: Some(semantics.clone()),
    })
}

pub(crate) fn cargo_report_subject(
    compiled_targets: &BTreeSet<CargoTargetIdentity>,
    observed_targets: &BTreeSet<CargoTargetIdentity>,
    completed_targets: &BTreeSet<CargoTargetIdentity>,
) -> String {
    let targets = compiled_targets
        .union(observed_targets)
        .chain(completed_targets)
        .cloned()
        .collect::<BTreeSet<_>>();
    match targets.len() {
        0 => "cargo-targets[]".to_string(),
        1 => targets.iter().next().expect("length checked").report_label(),
        _ => format!(
            "cargo-targets[{}]",
            targets.iter().map(CargoTargetIdentity::report_label).collect::<Vec<_>>().join(",")
        ),
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct TransportScopeKey {
    package_name: Option<String>,
    crate_name: String,
    cargo_target: Option<CargoTargetIdentity>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct FunctionEnvelopeIdentity {
    scope: TransportScopeKey,
    function: String,
    primary_package: bool,
    verification_session: String,
}

impl ParsedCompilerOutput {
    /// Whether a direct compiler stream carried one authenticated terminal
    /// crate inventory after all function envelopes were observed.  A partial
    /// stream can contain an early Proved row before an ICE or signal; such a
    /// prefix is useful diagnostic evidence, but it is not a complete run that
    /// same-process proof consumers may act on.
    pub(crate) fn raw_terminal_inventory_complete(&self) -> bool {
        self.saw_structured_transport
            && self.raw_crate_summary_sessions.len() == 1
            && self.raw_transport_ordering_defects.is_empty()
            && self.missing_crate_summary_scopes.is_empty()
    }

    pub(crate) fn require_structured_json_transport(mut self, required: bool) -> Self {
        if required && !self.saw_structured_transport {
            self.verification_results = vec![missing_structured_transport_result()];
        } else if required {
            self.verification_results
                .extend(self.missing_crate_summary_scopes.iter().map(missing_crate_summary_result));
        }
        self
    }

    /// Authenticate direct-rustc coverage against this invocation's freshness
    /// nonce. Raw compiler runs are deliberately unscoped (no Cargo package,
    /// never primary); a Cargo-scoped or legacy/sessionless row cannot carry
    /// proof-grade coverage credit on this channel.
    pub(crate) fn require_raw_coverage_authentication(
        mut self,
        expected_session: &str,
        required: bool,
    ) -> Result<Self, String> {
        if let Some(defect) = self.raw_transport_ordering_defects.first() {
            if required {
                return Err(format!("raw Trust compiler transport lifecycle violation: {defect}"));
            }
            let defect = format!("raw Trust compiler transport lifecycle violation: {defect}");
            self.drop_coverage(defect);
        }
        if let Some(session) =
            self.raw_function_sessions.iter().find(|session| session.as_str() != expected_session)
        {
            return Err(format!(
                "raw Trust function result carried stale or missing verification session {session:?}; expected {expected_session:?}"
            ));
        }
        if let Some(session) = self
            .raw_crate_summary_sessions
            .iter()
            .find(|session| session.as_str() != expected_session)
        {
            return Err(format!(
                "raw Trust terminal summary carried stale or missing verification session {session:?}; expected {expected_session:?}"
            ));
        }
        if self.coverage_rows.len() > 1 {
            let defect = format!(
                "raw Trust compiler carried {} coverage summaries; exactly one compiler-unit coverage inventory is required",
                self.coverage_rows.len()
            );
            if required {
                return Err(defect);
            }
            self.drop_coverage(defect);
            return Ok(self);
        }
        if let Some(row) = self.coverage_rows.iter().find(|row| {
            !row.package_name.is_empty()
                || row.primary_package
                || row.verification_session != expected_session
        }) {
            let defect = format!(
                "raw Trust coverage row carried unauthenticated scope/session for crate {:?}",
                row.crate_name
            );
            if required {
                return Err(defect);
            }
            self.drop_coverage(defect);
        }
        self.require_coverage_function_identity_authentication(required)
    }

    /// Authenticate the coverage cardinalities as exact function sets. Equal
    /// counts alone permit substitution, duplicate rows, and inflated totals.
    /// Every processed identity must therefore equal the authenticated function
    /// envelope inventory for this exact package/crate/session scope. The
    /// eligible set may be a strict superset only when the row honestly reports
    /// a shortfall; a claimed-complete row must make all three sets equal.
    fn require_coverage_function_identity_authentication(
        mut self,
        required: bool,
    ) -> Result<Self, String> {
        let Some(defect) = self.coverage_function_identity_defect() else {
            return Ok(self);
        };
        let defect = format!("Trust coverage function identity authentication failed: {defect}");
        if required {
            return Err(defect);
        }
        // Advisory compatibility may retain the function outcomes, but the
        // defective/legacy coverage row becomes coverage-unknown and earns no
        // whole-target completeness credit. It is recorded as DROPPED, with its
        // defect, so the report never calls it absent.
        self.drop_coverage(defect);
        Ok(self)
    }

    /// Drop every coverage row of this compiler output for `defect`, keeping the
    /// record that rows were emitted and why they earn no credit. A drop with no
    /// row to drop records nothing: there was nothing emitted to misreport.
    fn drop_coverage(&mut self, defect: String) {
        if !self.coverage_rows.is_empty() {
            self.coverage_rows.clear();
            self.dropped_coverage.push(defect);
        }
    }

    fn coverage_function_identity_defect(&self) -> Option<String> {
        if self.coverage_rows.is_empty() {
            return None;
        }
        if self.coverage_rows.len() != 1 {
            return Some(format!(
                "compiler unit carried {} coverage inventories; exactly one is required",
                self.coverage_rows.len()
            ));
        }
        let coverage = &self.coverage_rows[0];
        let Some(identities) = coverage.function_identities.as_ref() else {
            return Some(
                "count-only/legacy coverage omitted the versioned exact function identity inventory"
                    .to_string(),
            );
        };
        if identities.schema != trust_types::COVERAGE_FUNCTION_IDENTITY_SCHEMA_V1 {
            return Some(format!(
                "unsupported coverage function identity schema {:?}; expected {:?}",
                identities.schema,
                trust_types::COVERAGE_FUNCTION_IDENTITY_SCHEMA_V1,
            ));
        }
        if identities.eligible_functions.len() != coverage.eligible
            || identities.processed_functions.len() != coverage.processed
        {
            return Some(format!(
                "coverage counts did not equal identity cardinalities (eligible count={} identities={}; processed count={} identities={})",
                coverage.eligible,
                identities.eligible_functions.len(),
                coverage.processed,
                identities.processed_functions.len(),
            ));
        }
        if !canonical_function_identity_set(&identities.eligible_functions) {
            return Some(
                "eligible function identities were empty, duplicated, or not canonically sorted"
                    .to_string(),
            );
        }
        if !canonical_function_identity_set(&identities.processed_functions) {
            return Some(
                "processed function identities were empty, duplicated, or not canonically sorted"
                    .to_string(),
            );
        }
        if identities
            .processed_functions
            .iter()
            .any(|function| identities.eligible_functions.binary_search(function).is_err())
        {
            return Some(
                "processed function identity inventory was not a subset of the eligible inventory"
                    .to_string(),
            );
        }

        let expected_scope = TransportScopeKey {
            package_name: (!coverage.package_name.is_empty())
                .then(|| coverage.package_name.clone()),
            crate_name: coverage.crate_name.clone(),
            cargo_target: None,
        };
        let mut envelope_functions = Vec::with_capacity(self.function_envelopes.len());
        for envelope in &self.function_envelopes {
            if envelope.scope != expected_scope {
                return Some(format!(
                    "function envelope {:?} belonged to a different package/crate scope than coverage {:?}:{:?}",
                    envelope.function, coverage.package_name, coverage.crate_name,
                ));
            }
            if envelope.primary_package != coverage.primary_package
                || envelope.verification_session != coverage.verification_session
            {
                return Some(format!(
                    "function envelope {:?} did not share the coverage primary/session binding",
                    envelope.function,
                ));
            }
            envelope_functions.push(envelope.function.clone());
        }
        envelope_functions.sort();
        if envelope_functions.windows(2).any(|pair| pair[0] == pair[1]) {
            return Some(
                "authenticated compiler channel emitted duplicate function envelopes".to_string(),
            );
        }
        if identities.processed_functions != envelope_functions {
            return Some(exact_function_set_mismatch(
                "processed coverage identities",
                &identities.processed_functions,
                &envelope_functions,
            ));
        }
        if coverage.is_complete() && identities.eligible_functions != envelope_functions {
            return Some(exact_function_set_mismatch(
                "eligible coverage identities",
                &identities.eligible_functions,
                &envelope_functions,
            ));
        }
        None
    }

    fn merge_cargo_target(
        &mut self,
        mut target_output: Self,
        target: &CargoTargetIdentity,
    ) -> Result<(), String> {
        let expected_scope = TransportScopeKey {
            package_name: Some(target.package_name.clone()),
            crate_name: target.crate_name(),
            cargo_target: None,
        };
        if target_output.completed_primary_transport_scopes.remove(&expected_scope) {
            self.completed_proof_targets.insert(target.clone());
        }
        if let Some(unexpected) = target_output.completed_primary_transport_scopes.iter().next() {
            return Err(format!(
                "authenticated Cargo target `{}` carried an unexpected terminal summary scope `{}:{}`",
                target.report_label(),
                unexpected.package_name.as_deref().unwrap_or("<unknown-package>"),
                unexpected.crate_name
            ));
        }

        for result in &mut target_output.verification_results {
            result.function = target.scope_function(&result.function);
        }
        for envelope in &mut target_output.function_envelopes {
            envelope.function = target.scope_function(&envelope.function);
            envelope.scope.cargo_target = Some(target.clone());
        }
        for coverage in &mut target_output.coverage_rows {
            if let Some(identities) = &mut coverage.function_identities {
                for function in &mut identities.eligible_functions {
                    *function = target.scope_function(function);
                }
                for function in &mut identities.processed_functions {
                    *function = target.scope_function(function);
                }
            }
        }
        for scope in &mut target_output.missing_crate_summary_scopes {
            scope.cargo_target = Some(target.clone());
        }

        self.verification_results.extend(target_output.verification_results);
        self.compiler_diagnostics.extend(target_output.compiler_diagnostics);
        self.cached_obligations =
            self.cached_obligations.saturating_add(target_output.cached_obligations);
        match target_output.coverage_rows.len() {
            0 => {}
            1 => {
                self.coverage_proof_targets.insert(target.clone());
                self.compiler_memory_observations.push(
                    crate::compiler_memory::CompilerMemoryObservation::cargo(
                        target,
                        &target_output.coverage_rows[0],
                    ),
                );
                if target_output.coverage_rows[0].eligible == 0 {
                    self.zero_eligible_coverage_targets.insert(target.clone());
                }
            }
            count => {
                return Err(format!(
                    "authenticated Cargo target `{}` carried {count} coverage summaries; exactly one compiler-unit coverage inventory is required",
                    target.report_label()
                ));
            }
        }
        self.coverage_rows.extend(target_output.coverage_rows);
        self.dropped_coverage.extend(
            target_output
                .dropped_coverage
                .into_iter()
                .map(|defect| format!("{}: {defect}", target.report_label())),
        );
        self.function_envelopes.extend(target_output.function_envelopes);
        self.raw_transport_ordering_defects.extend(target_output.raw_transport_ordering_defects);
        self.saw_structured_transport |= target_output.saw_structured_transport;
        self.observed_proof_targets.insert(target.clone());
        self.missing_crate_summary_scopes.extend(target_output.missing_crate_summary_scopes);
        Ok(())
    }
}

fn canonical_function_identity_set(functions: &[String]) -> bool {
    functions.iter().all(|function| !function.is_empty() && function.trim() == function)
        && functions.windows(2).all(|pair| pair[0] < pair[1])
}

fn exact_function_set_mismatch(label: &str, claimed: &[String], envelopes: &[String]) -> String {
    let claimed = claimed.iter().cloned().collect::<BTreeSet<_>>();
    let envelopes = envelopes.iter().cloned().collect::<BTreeSet<_>>();
    let missing = envelopes.difference(&claimed).take(4).cloned().collect::<Vec<_>>();
    let substituted = claimed.difference(&envelopes).take(4).cloned().collect::<Vec<_>>();
    format!(
        "{label} did not exactly equal authenticated function envelopes (missing from coverage={missing:?}; not emitted as envelopes={substituted:?})"
    )
}

/// Authenticated Cargo proof rows form a per-rustc-unit protocol, not an
/// unordered bag. Cargo may interleave independent compiler units, so the
/// cursor is keyed by the complete Cargo-owned identity rather than package or
/// crate display names.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
enum CargoProofUnitPhase {
    #[default]
    FunctionRows,
    Coverage,
    CrateSummary,
    Artifact,
}

impl CargoProofUnitPhase {
    fn admit_transport(
        &mut self,
        target: &CargoTargetIdentity,
        message: &trust_types::TransportMessage,
        require_authenticated_coverage: bool,
    ) -> Result<(), String> {
        let label = target.report_label();
        match message {
            trust_types::TransportMessage::FunctionResult(_) => match self {
                Self::FunctionRows => Ok(()),
                Self::Coverage => Err(format!(
                    "Cargo proof unit emitted a function row after its coverage summary: {label}"
                )),
                Self::CrateSummary => Err(format!(
                    "Cargo proof unit emitted transport after its terminal crate summary: {label}"
                )),
                Self::Artifact => Err(format!(
                    "Cargo proof unit emitted transport after its compiler-artifact: {label}"
                )),
            },
            trust_types::TransportMessage::CoverageSummary(_) => match self {
                Self::FunctionRows => {
                    *self = Self::Coverage;
                    Ok(())
                }
                Self::Coverage => {
                    Err(format!("Cargo proof unit emitted duplicate coverage summaries: {label}"))
                }
                Self::CrateSummary => Err(format!(
                    "Cargo proof unit emitted coverage after its terminal crate summary: {label}"
                )),
                Self::Artifact => Err(format!(
                    "Cargo proof unit emitted transport after its compiler-artifact: {label}"
                )),
            },
            trust_types::TransportMessage::CrateSummary(_) => match self {
                Self::FunctionRows if require_authenticated_coverage => Err(format!(
                    "Cargo proof unit emitted its terminal crate summary before the required coverage summary: {label}"
                )),
                Self::FunctionRows | Self::Coverage => {
                    *self = Self::CrateSummary;
                    Ok(())
                }
                Self::CrateSummary => Err(format!(
                    "Cargo proof unit emitted duplicate terminal crate summaries: {label}"
                )),
                Self::Artifact => Err(format!(
                    "Cargo proof unit emitted transport after its compiler-artifact: {label}"
                )),
            },
            _ => Err(format!("Cargo proof unit emitted an unsupported lifecycle message: {label}")),
        }
    }

    fn admit_artifact(&mut self, target: &CargoTargetIdentity) -> Result<(), String> {
        let label = target.report_label();
        match self {
            Self::CrateSummary => {
                *self = Self::Artifact;
                Ok(())
            }
            Self::FunctionRows => Err(format!(
                "Cargo proof unit emitted compiler-artifact before its terminal crate summary: {label}"
            )),
            Self::Coverage => Err(format!(
                "Cargo proof unit emitted compiler-artifact before its terminal crate summary: {label}"
            )),
            Self::Artifact => Err(format!(
                "Cargo emitted duplicate compiler-artifact records for proof unit `{label}`"
            )),
        }
    }

    fn require_complete(
        self,
        target: &CargoTargetIdentity,
        require_authenticated_coverage: bool,
    ) -> Result<(), String> {
        if self == Self::Artifact {
            return Ok(());
        }
        let missing = match self {
            Self::FunctionRows if require_authenticated_coverage => {
                "coverage summary, terminal crate summary, and compiler-artifact"
            }
            Self::FunctionRows => "terminal crate summary and compiler-artifact",
            Self::Coverage => "terminal crate summary and compiler-artifact",
            Self::CrateSummary => "compiler-artifact",
            Self::Artifact => unreachable!(),
        };
        Err(format!(
            "Cargo proof unit ended before its required {missing}: {}",
            target.report_label()
        ))
    }
}

fn require_complete_cargo_proof_unit_lifecycles(
    inventory: Option<&CargoProofInventory>,
    lifecycles: &BTreeMap<CargoTargetIdentity, CargoProofUnitPhase>,
    require_authenticated_coverage: bool,
) -> Result<(), String> {
    let Some(inventory) = inventory else {
        return Ok(());
    };
    for target in &inventory.proof_targets {
        lifecycles
            .get(target)
            .copied()
            .unwrap_or_default()
            .require_complete(target, require_authenticated_coverage)?;
    }
    Ok(())
}

pub(crate) struct CargoCompilerEvidence {
    pub(crate) parsed: ParsedCompilerOutput,
    pub(crate) compiled_targets: BTreeSet<CargoTargetIdentity>,
    /// Selected-package test executables emitted by Cargo during the
    /// authenticated compile-only phase.  The outer driver hashes these bytes
    /// before authorizing a separate fresh-only execution phase.
    pub(crate) test_executables: BTreeSet<CargoTestExecutable>,
    pub(crate) prepared_tests: Option<trust_test_execution::PreparedTestsReceipt>,
    /// Cargo's terminal status as declared by its unique `build-finished`
    /// machine message. A successful process without this boundary is not a
    /// complete canonical evidence stream.
    pub(crate) build_succeeded: Option<bool>,
    /// Unique invocation-wide proof inventory emitted by authenticated Targo
    /// before it starts any compiler unit.
    pub(crate) declared_inventory: Option<CargoProofInventory>,
    /// Structured messages that passed the Cargo envelope, diagnostic-tag,
    /// primary-unit, package/crate, compile-target, and session checks above.
    /// Consumers such as the self-verification harness must use these values,
    /// never rescan Cargo/build-script stderr for transport-looking text.
    pub(crate) authenticated_transport_messages:
        Vec<(CargoTargetIdentity, trust_types::TransportMessage)>,
    /// Every `compiler-message` of level `error` Cargo reported, in the
    /// package its `package_id` names (`crate::obligations::CompileError`).
    /// Disclosure for the records and the changed-only view: no verdict,
    /// gate or exit reads it, and a failed build is judged by
    /// `build_succeeded` and the compiler's exit as before.
    pub(crate) compile_errors: Vec<crate::obligations::CompileError>,
    /// The island rows each proof unit published
    /// (`trust_types::clean_island_rows`), validated and bound to the unit's
    /// Cargo envelope ([`admit_clean_island_rows`]). Disclosure for the
    /// records and the changed-only view only: no verdict, count, gate,
    /// coverage or exit reads it.
    pub(crate) clean_island_rows:
        BTreeMap<CargoTargetIdentity, trust_types::clean_island_rows::CleanIslandRowsTransport>,
}

/// Admit one unit's island rows: at most one message per unit, published
/// before its coverage summary (the compiler emits them inside its JSON
/// block, before `CoverageSummary`; on a front-end error the unit publishes
/// no coverage at all), that validates
/// (`CleanIslandRowsTransport::validate`) and whose every key names a
/// declaration of the unit's own crate. Anything else is a transport
/// violation that fails the run, as a malformed proof message does: a row is
/// never read from a message that could not have been written honestly.
fn admit_clean_island_rows(
    admitted: &mut BTreeMap<
        CargoTargetIdentity,
        trust_types::clean_island_rows::CleanIslandRowsTransport,
    >,
    phase: Option<CargoProofUnitPhase>,
    target: CargoTargetIdentity,
    rows: trust_types::clean_island_rows::CleanIslandRowsTransport,
) -> Result<(), String> {
    let label = target.report_label();
    if !matches!(phase, None | Some(CargoProofUnitPhase::FunctionRows)) {
        return Err(format!(
            "Cargo proof unit emitted its island rows after its coverage summary: {label}"
        ));
    }
    if admitted.contains_key(&target) {
        return Err(format!("Cargo proof unit emitted island rows twice: {label}"));
    }
    rows.validate().map_err(|error| format!("invalid island rows from `{label}`: {error}"))?;
    let prefix = format!("{}::", target.crate_name());
    if let Some(row) = rows.rows.iter().find(|row| !row.key.starts_with(&prefix)) {
        return Err(format!(
            "island row `{}` does not name a declaration of `{label}`'s crate",
            row.key
        ));
    }
    admitted.insert(target, rows);
    Ok(())
}

/// The package name a Cargo package ID names: the selected package's own
/// name when the run selected it; otherwise read from the ID, in either of
/// Cargo's spellings — `<name> <version> (<source>)`, or
/// `<source>#[<name>@]<version>`, where a missing `<name>@` means the name is
/// the source path's last segment.
fn cargo_package_name(package_id: &str, selected_packages: &BTreeMap<String, String>) -> String {
    if let Some(name) = selected_packages.get(package_id) {
        return name.clone();
    }
    if let Some((name, _)) = package_id.split_once(' ') {
        return name.to_string();
    }
    match package_id.rsplit_once('#') {
        Some((_, fragment)) if fragment.contains('@') => {
            fragment.split_once('@').map(|(name, _)| name.to_string()).unwrap_or_default()
        }
        Some((source, _)) => source
            .split('?')
            .next()
            .unwrap_or(source)
            .trim_end_matches('/')
            .rsplit('/')
            .next()
            .unwrap_or(source)
            .to_string(),
        None => package_id.to_string(),
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct CargoTestExecutable {
    pub(crate) target: CargoTargetIdentity,
    pub(crate) path: PathBuf,
    /// Byte identity emitted by native Targo from its post-link artifact work,
    /// before Cargo releases the phase-A build lifecycle.
    pub(crate) phase_a_sha256: String,
}

impl CargoCompilerEvidence {
    /// Validate the complete successful Cargo proof frontier before any report
    /// or live consumer can treat compiler rows as selected-root evidence.
    ///
    /// Aggregate target sets intentionally contain all authenticated roles.
    /// This method partitions them and independently proves that every exact
    /// selected package has a real `primary` root. A dependency or
    /// test-execution unit can therefore never stand in for an omitted root.
    /// Empty library companions are accepted only when the same selected
    /// package also completed at least one nonempty primary root. Executable
    /// roots are stricter: each bin/test/bench/example or native test-harness
    /// Unit must independently contain a coverage-eligible body, so a nonempty
    /// library can never mask an empty executable selected by Cargo.
    pub(crate) fn require_successful_selected_roots(
        &self,
        selected_packages: &BTreeMap<String, String>,
        require_authenticated_coverage: bool,
    ) -> Result<(), String> {
        if self.build_succeeded != Some(true) {
            return Err(match self.build_succeeded {
                Some(false) => {
                    "Cargo proof stream declared an unsuccessful build-finished status".to_string()
                }
                None => {
                    "successful Cargo process omitted its authenticated build-finished boundary"
                        .to_string()
                }
                Some(true) => unreachable!(),
            });
        }
        if selected_packages.is_empty() {
            return Err("Cargo proof selection resolved no primary packages".to_string());
        }
        let inventory = self.declared_inventory.as_ref().ok_or_else(|| {
            "successful Cargo process omitted Targo's invocation-wide proof inventory".to_string()
        })?;

        require_exact_target_set(
            "declared proof-inventory",
            &inventory.proof_targets,
            "terminal compiler",
            &self.parsed.completed_proof_targets,
        )?;

        require_exact_target_set(
            "compiler-artifact",
            &self.compiled_targets,
            "terminal compiler",
            &self.parsed.completed_proof_targets,
        )?;
        require_exact_target_set(
            "observed compiler",
            &self.parsed.observed_proof_targets,
            "terminal compiler",
            &self.parsed.completed_proof_targets,
        )?;
        if require_authenticated_coverage {
            require_exact_target_set(
                "coverage",
                &self.parsed.coverage_proof_targets,
                "terminal compiler",
                &self.parsed.completed_proof_targets,
            )?;
        }

        for (package_id, package_name) in selected_packages {
            let primary_roots = self
                .parsed
                .completed_proof_targets
                .iter()
                .filter(|target| {
                    target.proof_unit_role == "primary"
                        && target.package_id == *package_id
                        && target.package_name == *package_name
                })
                .collect::<Vec<_>>();
            if primary_roots.is_empty() {
                return Err(format!(
                    "successful Cargo proof stream omitted an authenticated primary proof unit for selected package {package_name:?} ({package_id})"
                ));
            }
            if require_authenticated_coverage
                && primary_roots
                    .iter()
                    .all(|target| self.parsed.zero_eligible_coverage_targets.contains(*target))
            {
                return Err(format!(
                    "successful Cargo proof stream declared zero coverage-eligible bodies across every primary proof unit for selected package {package_name:?} ({package_id})"
                ));
            }
            if require_authenticated_coverage {
                for target in self.parsed.completed_proof_targets.iter().filter(|target| {
                    target.package_id == *package_id
                        && target.package_name == *package_name
                        && matches!(target.proof_unit_role.as_str(), "primary" | "test-execution")
                        && cargo_root_requires_nonempty_coverage(target)
                }) {
                    if self.parsed.zero_eligible_coverage_targets.contains(target) {
                        return Err(format!(
                            "successful Cargo proof stream declared zero coverage-eligible bodies for executable selected root `{}`",
                            target.report_label()
                        ));
                    }
                }
            }
        }
        Ok(())
    }
}

fn cargo_root_requires_nonempty_coverage(target: &CargoTargetIdentity) -> bool {
    target.proof_unit_mode == "test"
        || target
            .target_kinds
            .iter()
            .any(|kind| matches!(kind.as_str(), "bin" | "test" | "bench" | "example"))
}

fn require_exact_target_set(
    actual_label: &str,
    actual: &BTreeSet<CargoTargetIdentity>,
    expected_label: &str,
    expected: &BTreeSet<CargoTargetIdentity>,
) -> Result<(), String> {
    if actual == expected {
        return Ok(());
    }
    let missing = expected
        .difference(actual)
        .take(4)
        .map(CargoTargetIdentity::report_label)
        .collect::<Vec<_>>();
    let unexpected = actual
        .difference(expected)
        .take(4)
        .map(CargoTargetIdentity::report_label)
        .collect::<Vec<_>>();
    Err(format!(
        "Cargo proof inventory mismatch: {actual_label} targets did not exactly equal {expected_label} targets (missing={missing:?}; unexpected={unexpected:?})"
    ))
}

/// Parse Cargo's authenticated compiler-message/artifact envelope. Raw Cargo
/// stderr is deliberately not proof transport: build scripts share it.
pub(crate) fn parse_cargo_json_stdout<R: BufRead>(
    reader: R,
    selected_packages: &BTreeMap<String, String>,
    expected_session: &str,
    require_authenticated_coverage: bool,
) -> Result<CargoCompilerEvidence, String> {
    parse_cargo_json_stdout_impl(CargoJsonParseInput {
        reader,
        selected_packages,
        expected_session,
        require_authenticated_coverage,
        retain_authenticated_messages: false,
        allow_post_build_test_output: false,
        require_prepared_tests: false,
        max_line_bytes: MAX_CARGO_JSON_LINE_BYTES,
        max_authenticated_transport_bytes: max_authenticated_cargo_transport_bytes(),
    })
}

/// Parse Cargo's authenticated compile-time evidence while passing through
/// the test harness's ordinary stdout after Cargo's authenticated
/// `build-finished` boundary. Before that boundary parsing remains exactly as
/// strict as [`parse_cargo_json_stdout`]; post-boundary output is never parsed
/// as evidence, even if a test prints JSON-looking text.
pub(crate) fn parse_cargo_json_stdout_for_test<R: BufRead>(
    reader: R,
    selected_packages: &BTreeMap<String, String>,
    expected_session: &str,
    require_authenticated_coverage: bool,
) -> Result<CargoCompilerEvidence, String> {
    parse_cargo_json_stdout_impl(CargoJsonParseInput {
        reader,
        selected_packages,
        expected_session,
        require_authenticated_coverage,
        retain_authenticated_messages: false,
        allow_post_build_test_output: true,
        require_prepared_tests: false,
        max_line_bytes: MAX_CARGO_JSON_LINE_BYTES,
        max_authenticated_transport_bytes: max_authenticated_cargo_transport_bytes(),
    })
}

fn parse_prepared_tests_receipt(
    line: &str,
    session: &str,
) -> Result<trust_test_execution::PreparedTestsReceipt, String> {
    use trust_test_execution::{PreparedTestsReceipt, RECEIPT_SCHEMA};
    let mut value: serde_json::Value = serde_json::from_str(line)
        .map_err(|_| "invalid prepared-test receipt after build completion")?;
    if value
        .as_object_mut()
        .and_then(|object| object.remove("reason"))
        .and_then(|value| value.as_str().map(str::to_owned))
        .as_deref()
        != Some("trust-test-execution-plan")
    {
        return Err("expected native prepared-test receipt after build completion".into());
    }
    let receipt: PreparedTestsReceipt = serde_json::from_value(value)
        .map_err(|error| format!("invalid prepared-test receipt: {error}"))?;
    if receipt.schema != RECEIPT_SCHEMA
        || receipt.session != session
        || !std::path::Path::new(&receipt.path).is_absolute()
        || receipt.sha256.len() != 64
        || !receipt
            .sha256
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err("mismatched native prepared-test receipt".into());
    }
    Ok(receipt)
}

pub(crate) fn parse_cargo_json_stdout_for_prepared_tests<R: BufRead>(
    reader: R,
    selected_packages: &BTreeMap<String, String>,
    expected_session: &str,
    require_authenticated_coverage: bool,
) -> Result<CargoCompilerEvidence, String> {
    parse_cargo_json_stdout_impl(CargoJsonParseInput {
        reader,
        selected_packages,
        expected_session,
        require_authenticated_coverage,
        retain_authenticated_messages: false,
        allow_post_build_test_output: false,
        require_prepared_tests: true,
        max_line_bytes: MAX_CARGO_JSON_LINE_BYTES,
        max_authenticated_transport_bytes: max_authenticated_cargo_transport_bytes(),
    })
}

/// Self-verification additionally needs the original typed messages to build
/// its artifact-binding report. Ordinary Targo runs deliberately use
/// [`parse_cargo_json_stdout`] so they do not retain a second copy of every
/// compiler transport payload after it has been normalized.
pub(crate) fn parse_cargo_json_stdout_with_authenticated_messages<R: BufRead>(
    reader: R,
    selected_packages: &BTreeMap<String, String>,
    expected_session: &str,
    require_authenticated_coverage: bool,
) -> Result<CargoCompilerEvidence, String> {
    parse_cargo_json_stdout_impl(CargoJsonParseInput {
        reader,
        selected_packages,
        expected_session,
        require_authenticated_coverage,
        retain_authenticated_messages: true,
        allow_post_build_test_output: false,
        require_prepared_tests: false,
        max_line_bytes: MAX_CARGO_JSON_LINE_BYTES,
        max_authenticated_transport_bytes: max_authenticated_cargo_transport_bytes(),
    })
}

struct CargoJsonParseInput<'a, R: BufRead> {
    reader: R,
    selected_packages: &'a BTreeMap<String, String>,
    expected_session: &'a str,
    require_authenticated_coverage: bool,
    retain_authenticated_messages: bool,
    allow_post_build_test_output: bool,
    require_prepared_tests: bool,
    max_line_bytes: usize,
    max_authenticated_transport_bytes: usize,
}

fn parse_cargo_json_stdout_impl<R: BufRead>(
    input: CargoJsonParseInput<'_, R>,
) -> Result<CargoCompilerEvidence, String> {
    let CargoJsonParseInput {
        mut reader,
        selected_packages,
        expected_session,
        require_authenticated_coverage,
        retain_authenticated_messages,
        allow_post_build_test_output,
        require_prepared_tests,
        max_line_bytes,
        max_authenticated_transport_bytes,
    } = input;
    let mut transport_lines = BTreeMap::<CargoTargetIdentity, Vec<String>>::new();
    let mut proof_unit_lifecycles = BTreeMap::<CargoTargetIdentity, CargoProofUnitPhase>::new();
    let mut compiled_targets = BTreeSet::new();
    let mut test_executables = BTreeSet::new();
    let mut prepared_tests = None;
    let mut primary_compile_targets = BTreeSet::new();
    let mut proof_unit_identities = BTreeMap::<u64, CargoTargetIdentity>::new();
    let mut authenticated_transport_messages = Vec::new();
    let mut native_admission_observations = Vec::new();
    let mut native_admission_problems = Vec::new();
    let mut native_admission_seen = BTreeSet::new();
    let mut native_admission_bytes = 0;
    let mut authenticated_transport_bytes = 0usize;
    let mut line_index = 0usize;
    let mut build_succeeded = None;
    let mut declared_inventory = None;
    let mut censused_doctest_units = BTreeSet::<u64>::new();
    let mut compile_errors = Vec::new();
    let mut clean_island_rows = BTreeMap::<
        CargoTargetIdentity,
        trust_types::clean_island_rows::CleanIslandRowsTransport,
    >::new();

    while let Some(line) = read_bounded_utf8_line(&mut reader, max_line_bytes).map_err(|error| {
        format!("could not safely read Cargo JSON output line {}: {error}", line_index + 1)
    })? {
        line_index += 1;
        if build_succeeded.is_some() {
            if require_prepared_tests {
                if prepared_tests.is_some() {
                    return Err("duplicate native prepared-test receipt".into());
                }
                prepared_tests = Some(parse_prepared_tests_receipt(&line, expected_session)?);
                continue;
            }
            if allow_post_build_test_output {
                // Cargo test harness output is an untrusted user stream.
                // Preserve it for normal test UX, but never feed it back into
                // the proof envelope parser (including JSON-looking output).
                println!("{line}");
                continue;
            }
            return Err(format!(
                "canonical Targo emitted output after its terminal Cargo build-finished boundary at line {line_index}"
            ));
        }
        let value: serde_json::Value = serde_json::from_str(&line)
            .map_err(|error| format!("canonical Targo emitted non-JSON message output: {error}"))?;
        match value.get("reason").and_then(serde_json::Value::as_str) {
            Some("trust-proof-inventory") => {
                if line_index != 1 {
                    return Err("Targo proof inventory was not the first canonical Cargo message"
                        .to_string());
                }
                let inventory = parse_cargo_proof_inventory(&value, selected_packages)?;
                proof_unit_lifecycles.extend(
                    inventory
                        .proof_targets
                        .iter()
                        .cloned()
                        .map(|target| (target, CargoProofUnitPhase::default())),
                );
                if declared_inventory.replace(inventory).is_some() {
                    return Err("Targo emitted more than one proof inventory".to_string());
                }
            }
            Some("compiler-artifact") => {
                let Some(package_id) = value.get("package_id").and_then(serde_json::Value::as_str)
                else {
                    return Err("Cargo compiler-artifact omitted package_id".to_string());
                };
                let Some(target_identity) =
                    cargo_target_identity(&value, package_id, selected_packages)?
                else {
                    continue;
                };
                match value.get("fresh") {
                    Some(serde_json::Value::Bool(false)) => {}
                    Some(serde_json::Value::Bool(true)) => {
                        return Err(
                            "Cargo proof-unit compiler-artifact was fresh despite the unique verification-session rustflag; no fresh verifier run can be claimed"
                                .to_string(),
                        );
                    }
                    _ => {
                        return Err(
                            "Cargo proof-unit compiler-artifact omitted its required fresh=false observation"
                                .to_string(),
                        );
                    }
                }
                let is_test_profile = value
                    .get("profile")
                    .and_then(|profile| profile.get("test"))
                    .and_then(serde_json::Value::as_bool)
                    == Some(true);
                if is_test_profile && target_identity.proof_unit_role == "primary" {
                    if let Some(executable) =
                        value.get("executable").and_then(serde_json::Value::as_str)
                    {
                        if executable.is_empty() {
                            return Err(format!(
                                "selected test target `{}` emitted an empty executable path",
                                target_identity.report_label()
                            ));
                        }
                        let phase_a_sha256 = value
                            .get("trust_executable_sha256")
                            .and_then(serde_json::Value::as_str)
                            .filter(|digest| {
                                digest.len() == 64
                                    && digest.bytes().all(|byte| {
                                        byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)
                                    })
                            })
                            .ok_or_else(|| {
                                format!(
                                    "selected test target `{}` omitted its canonical Targo executable SHA-256",
                                    target_identity.report_label()
                                )
                            })?;
                        test_executables.insert(CargoTestExecutable {
                            target: target_identity.clone(),
                            path: PathBuf::from(executable),
                            phase_a_sha256: phase_a_sha256.to_string(),
                        });
                    }
                }
                admit_proof_unit_identity(&mut proof_unit_identities, &target_identity)?;
                admit_primary_compile_target(&mut primary_compile_targets, &target_identity)?;
                require_declared_proof_target(declared_inventory.as_ref(), &target_identity)?;
                validate_cargo_artifact_semantics(
                    &value,
                    declared_inventory.as_ref(),
                    &target_identity,
                )?;
                proof_unit_lifecycles
                    .entry(target_identity.clone())
                    .or_default()
                    .admit_artifact(&target_identity)?;
                let inserted = compiled_targets.insert(target_identity);
                debug_assert!(inserted, "lifecycle rejects duplicate compiler-artifacts");
            }
            Some("compiler-message") => {
                let message = value
                    .get("message")
                    .ok_or_else(|| "Cargo compiler-message omitted message".to_string())?;
                let text =
                    message.get("message").and_then(serde_json::Value::as_str).unwrap_or_default();
                if let Some(json) = text.strip_prefix(trust_types::TRANSPORT_PREFIX) {
                    // Resource transport is authenticated against the same envelope,
                    // but defects invalidate only resource availability, never proof rows.
                    if is_native_admission_payload(json) {
                        let checked = (|| {
                            charge_native_admission_bytes(
                                &mut native_admission_bytes,
                                text.len(),
                                MAX_NATIVE_ADMISSION_TRANSPORT_BYTES,
                            )?;
                            validate_transport_diagnostic_tag(message)?;
                            let package = value
                                .get("package_id")
                                .and_then(serde_json::Value::as_str)
                                .ok_or("native admission envelope omitted package_id")?;
                            let target = cargo_target_identity(&value, package, selected_packages)?
                                .ok_or("native admission unit is outside the proof inventory")?;
                            require_declared_proof_target(declared_inventory.as_ref(), &target)?;
                            if !matches!(
                                proof_unit_lifecycles.get(&target),
                                None | Some(CargoProofUnitPhase::FunctionRows)
                            ) {
                                return Err(
                                    "native admission census arrived after coverage/terminal"
                                        .into(),
                                );
                            }
                            if !native_admission_seen.insert(target.clone()) {
                                return Err("duplicate native admission census".into());
                            }
                            let trust_types::TransportMessage::NativeAdmissionCensus(census) =
                                trust_types::parse_transport_payload(json)
                                    .map_err(|e| e.to_string())?
                            else {
                                return Err("invalid native admission payload".into());
                            };
                            crate::compiler_admission::authenticate(
                                &census,
                                &target,
                                expected_session,
                            )?;
                            native_admission_observations.push(
                                crate::compiler_admission::Observation {
                                    cargo_target: target,
                                    census,
                                },
                            );
                            Ok::<(), String>(())
                        })();
                        if let Err(error) = checked {
                            native_admission_problems.push(error);
                        }
                        continue;
                    }
                    authenticated_transport_bytes = authenticated_transport_bytes
                        .checked_add(text.len())
                        .filter(|bytes| *bytes <= max_authenticated_transport_bytes)
                        .ok_or_else(|| format!("authenticated Cargo Trust transport exceeds the {}-byte aggregate safety limit", max_authenticated_transport_bytes))?;
                    validate_transport_diagnostic_tag(message)?;
                    let Some((target, authenticated_message)) = validate_cargo_transport_envelope(
                        &value,
                        json,
                        selected_packages,
                        expected_session,
                        require_authenticated_coverage,
                    )?
                    else {
                        continue;
                    };
                    if native_admission_seen.contains(&target)
                        && matches!(
                            &authenticated_message,
                            trust_types::TransportMessage::FunctionResult(_)
                        )
                    {
                        native_admission_problems
                            .push("function transport followed native admission census".into());
                    }
                    admit_proof_unit_identity(&mut proof_unit_identities, &target)?;
                    admit_primary_compile_target(&mut primary_compile_targets, &target)?;
                    require_declared_proof_target(declared_inventory.as_ref(), &target)?;
                    // Island rows are disclosure (`crate::obligations`, CLEAN
                    // ISLANDS): admitted once the envelope's scope and session
                    // are checked, only before the unit's coverage, and never
                    // a proof row, a proof count or a lifecycle step.
                    if let trust_types::TransportMessage::CleanIslandRows(rows) =
                        authenticated_message
                    {
                        admit_clean_island_rows(
                            &mut clean_island_rows,
                            proof_unit_lifecycles.get(&target).copied(),
                            target,
                            rows,
                        )?;
                        continue;
                    }
                    proof_unit_lifecycles.entry(target.clone()).or_default().admit_transport(
                        &target,
                        &authenticated_message,
                        require_authenticated_coverage,
                    )?;
                    let authenticated_json = serde_json::to_string(&authenticated_message)
                        .map_err(|error| {
                            format!("could not retain authenticated Trust transport: {error}")
                        })?;
                    if retain_authenticated_messages {
                        authenticated_transport_messages
                            .push((target.clone(), authenticated_message));
                    }
                    transport_lines
                        .entry(target)
                        .or_default()
                        .push(format!("{}{authenticated_json}", trust_types::TRANSPORT_PREFIX));
                } else {
                    if let Some(package_id) =
                        value.get("package_id").and_then(serde_json::Value::as_str)
                    {
                        compile_errors.extend(
                            crate::obligations::CompileError::of_cargo_diagnostic(
                                &cargo_package_name(package_id, selected_packages),
                                message,
                            ),
                        );
                    }
                    if let Some(rendered) =
                        message.get("rendered").and_then(serde_json::Value::as_str)
                    {
                        eprint!("{rendered}");
                    }
                }
            }
            Some("trust-doctest-census") => {
                apply_doctest_census(
                    declared_inventory.as_mut(),
                    &value,
                    &mut censused_doctest_units,
                )?;
            }
            Some("build-finished") => {
                let Some(success) = value.get("success").and_then(serde_json::Value::as_bool)
                else {
                    return Err("Cargo build-finished message omitted boolean success".to_string());
                };
                if build_succeeded.replace(success).is_some() {
                    return Err("Cargo emitted more than one build-finished message".to_string());
                }
                if success {
                    require_complete_cargo_proof_unit_lifecycles(
                        declared_inventory.as_ref(),
                        &proof_unit_lifecycles,
                        require_authenticated_coverage,
                    )?;
                }
            }
            Some(_) => {}
            None => return Err("Cargo JSON message omitted reason".to_string()),
        }
    }

    // A canonical successful Cargo stream normally carries `build-finished`.
    // Still validate at EOF so truncating that boundary cannot turn a partial
    // declared proof frontier into apparently complete evidence. A declared
    // failed build may stop a compiler unit at any point and carries no proof
    // authority, so retain its human diagnostics instead of replacing the
    // underlying compiler failure with a protocol-completion error.
    if build_succeeded != Some(false) {
        require_complete_cargo_proof_unit_lifecycles(
            declared_inventory.as_ref(),
            &proof_unit_lifecycles,
            require_authenticated_coverage,
        )?;
    }

    if build_succeeded != Some(true) {
        native_admission_problems
            .push("Cargo run has no successful build-finished boundary".into());
    }
    let mut parsed = ParsedCompilerOutput::default();
    for (target, lines) in transport_lines {
        let target_output = parse_compiler_stderr(Cursor::new(lines.join("\n")), false)
            .require_coverage_function_identity_authentication(require_authenticated_coverage)?;
        if let Some(resource) =
            native_admission_observations.iter().find(|resource| resource.cargo_target == target)
        {
            let mut functions: Vec<_> =
                resource.census.bodies.iter().map(|b| b.function.clone()).collect();
            functions.sort();
            let expected = target_output
                .coverage_rows
                .first()
                .and_then(|c| c.function_identities.as_ref())
                .map(|i| &i.eligible_functions);
            if expected != Some(&functions) {
                native_admission_problems.push(format!(
                    "native admission body inventory differs from coverage: {}",
                    target.report_label()
                ));
            }
        }
        parsed.merge_cargo_target(target_output, &target)?;
    }
    parsed.native_admission_observations = native_admission_observations;
    parsed.native_admission_problems = native_admission_problems;
    if require_prepared_tests && build_succeeded == Some(true) && prepared_tests.is_none() {
        return Err("native Targo omitted the prepared-test receipt".into());
    }
    let evidence = CargoCompilerEvidence {
        prepared_tests,
        parsed,
        compiled_targets,
        test_executables,
        build_succeeded,
        declared_inventory,
        authenticated_transport_messages,
        compile_errors,
        clean_island_rows,
    };
    if evidence.build_succeeded == Some(true) {
        evidence
            .require_successful_selected_roots(selected_packages, require_authenticated_coverage)?;
    }
    Ok(evidence)
}

/// Trust (D2d): bind one `trust-doctest-census` message to the exact excluded
/// doctest Unit the declared inventory names by index AND identity digest, and
/// refine that Unit to [`TARGO_TRUST_EXCLUSION_EMPTY_DOCTEST`] only when the
/// census counted zero doctests. Anything else about the message — a census
/// before the inventory, an unknown field, a second census for one Unit, a
/// Unit that is not a deferred doctest — is a transport violation.
fn apply_doctest_census(
    inventory: Option<&mut CargoProofInventory>,
    census: &serde_json::Value,
    censused: &mut BTreeSet<u64>,
) -> Result<(), String> {
    let inventory = inventory.ok_or_else(|| {
        "Targo doctest census appeared before its declared proof inventory".to_string()
    })?;
    let fields = census
        .as_object()
        .ok_or_else(|| "Targo doctest census was not a JSON object".to_string())?;
    if let Some(field) = fields.keys().find(|field| {
        !matches!(
            field.as_str(),
            "reason" | "schema" | "index" | "trust_unit_identity_sha256" | "doctests"
        )
    }) {
        return Err(format!("Targo doctest census carried unexpected field {field:?}"));
    }
    if census.get("schema").and_then(serde_json::Value::as_str)
        != Some(TARGO_TRUST_DOCTEST_CENSUS_SCHEMA_V1)
    {
        return Err("Targo doctest census omitted its exact schema".to_string());
    }
    let index = census
        .get("index")
        .and_then(serde_json::Value::as_u64)
        .ok_or_else(|| "Targo doctest census omitted its Cargo Unit index".to_string())?;
    let identity = census
        .get("trust_unit_identity_sha256")
        .and_then(serde_json::Value::as_str)
        .filter(|digest| canonical_sha256_hex(digest))
        .ok_or_else(|| {
            "Targo doctest census omitted a canonical Trust unit-identity SHA-256".to_string()
        })?;
    let doctests = census
        .get("doctests")
        .and_then(serde_json::Value::as_u64)
        .ok_or_else(|| "Targo doctest census omitted its doctest count".to_string())?;
    if !censused.insert(index) {
        return Err(format!("Targo emitted more than one doctest census for Cargo Unit {index}"));
    }
    let target = inventory
        .excluded_targets
        .iter()
        .find(|target| target.proof_unit_index == index)
        .cloned()
        .ok_or_else(|| {
            format!("Targo doctest census named Cargo Unit {index}, which is not a declared excluded Unit")
        })?;
    if target.unit_identity_sha256 != identity {
        return Err(format!(
            "Targo doctest census identity did not match the declared Unit: {}",
            target.report_label()
        ));
    }
    if target.proof_unit_mode != "doctest"
        || inventory.excluded_reasons.get(&target).map(String::as_str)
            != Some(TARGO_TRUST_EXCLUSION_DEFERRED_DOCTEST)
    {
        return Err(format!(
            "Targo doctest census named a Unit that is not a declared deferred doctest: {}",
            target.report_label()
        ));
    }
    if doctests == 0 {
        inventory.excluded_reasons.insert(target, TARGO_TRUST_EXCLUSION_EMPTY_DOCTEST.to_string());
    }
    Ok(())
}

fn validate_cargo_artifact_semantics(
    artifact: &serde_json::Value,
    inventory: Option<&CargoProofInventory>,
    target: &CargoTargetIdentity,
) -> Result<(), String> {
    let inventory = inventory.ok_or_else(|| {
        "Cargo compiler-artifact appeared before the declared proof inventory".to_string()
    })?;
    let semantics = inventory.unit_semantics.get(target).ok_or_else(|| {
        format!(
            "Cargo compiler-artifact had no declared semantic descriptor: {}",
            target.report_label()
        )
    })?;
    let features = artifact
        .get("features")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| {
            format!(
                "Cargo compiler-artifact omitted its enabled feature set: {}",
                target.report_label()
            )
        })?
        .iter()
        .map(|feature| {
            feature.as_str().map(str::to_string).ok_or_else(|| {
                format!(
                    "Cargo compiler-artifact carried a non-string feature: {}",
                    target.report_label()
                )
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    if features != semantics.features {
        return Err(format!(
            "Cargo compiler-artifact enabled features did not exactly match the declared Unit semantics: {}",
            target.report_label()
        ));
    }
    let profile =
        artifact.get("profile").and_then(serde_json::Value::as_object).ok_or_else(|| {
            format!(
                "Cargo compiler-artifact omitted its profile projection: {}",
                target.report_label()
            )
        })?;
    let expected_debuginfo = match semantics.profile.debuginfo.as_str() {
        "0" => serde_json::json!(0),
        "1" => serde_json::json!(1),
        "2" => serde_json::json!(2),
        value => serde_json::Value::String(value.to_string()),
    };
    for (field, expected) in [
        ("opt_level", serde_json::Value::String(semantics.profile.opt_level.clone())),
        ("debuginfo", expected_debuginfo),
        ("debug_assertions", serde_json::Value::Bool(semantics.profile.debug_assertions)),
        ("overflow_checks", serde_json::Value::Bool(semantics.profile.overflow_checks)),
        ("test", serde_json::Value::Bool(semantics.cfg_test)),
    ] {
        if profile.get(field) != Some(&expected) {
            return Err(format!(
                "Cargo compiler-artifact profile field {field:?} did not match the declared Unit semantics: {}",
                target.report_label()
            ));
        }
    }
    Ok(())
}

fn parse_cargo_proof_inventory(
    value: &serde_json::Value,
    selected_packages: &BTreeMap<String, String>,
) -> Result<CargoProofInventory, String> {
    if value.get("schema").and_then(serde_json::Value::as_str)
        != Some(TARGO_TRUST_PROOF_INVENTORY_SCHEMA_V2)
    {
        return Err("Targo proof inventory had an unsupported schema".to_string());
    }
    let include_dependencies = value
        .get("include_dependencies")
        .and_then(serde_json::Value::as_bool)
        .ok_or_else(|| "Targo proof inventory omitted its boolean dependency policy".to_string())?;
    let units = value
        .get("units")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "Targo proof inventory omitted its proof-unit array".to_string())?;
    let mut proof_targets = BTreeSet::new();
    let mut proof_unit_identities = BTreeMap::new();
    let mut primary_compile_targets = BTreeSet::new();
    let mut unit_semantics = BTreeMap::new();
    let mut previous_index = None;
    for (position, unit) in units.iter().enumerate() {
        if unit.get("exclusion_reason").is_some() {
            return Err(format!(
                "Targo proof inventory unit {position} carried an exclusion reason despite being in the proof frontier"
            ));
        }
        let package_id = unit
            .get("package_id")
            .and_then(serde_json::Value::as_str)
            .filter(|package_id| !package_id.is_empty() && package_id.trim() == *package_id)
            .ok_or_else(|| {
                format!("Targo proof inventory unit {position} omitted its package ID")
            })?;
        let target_name = unit
            .get("target_name")
            .and_then(serde_json::Value::as_str)
            .filter(|target| !target.is_empty() && target.trim() == *target)
            .ok_or_else(|| {
                format!("Targo proof inventory unit {position} omitted its target name")
            })?;
        let target_kinds =
            unit.get("target_kinds").and_then(serde_json::Value::as_array).ok_or_else(|| {
                format!("Targo proof inventory unit {position} omitted its target-kind array")
            })?;
        let compile_target = unit
            .get("compile_target")
            .and_then(serde_json::Value::as_str)
            .filter(|target| !target.is_empty())
            .ok_or_else(|| {
                format!("Targo proof inventory unit {position} omitted its compile target")
            })?;
        let proof_unit = unit.get("trust_proof_unit").ok_or_else(|| {
            format!("Targo proof inventory unit {position} omitted its proof identity")
        })?;
        let semantics_sha256 = proof_unit
            .get("semantics_sha256")
            .and_then(serde_json::Value::as_str)
            .ok_or_else(|| {
                format!(
                    "Targo proof inventory unit {position} omitted its semantic descriptor digest"
                )
            })?;
        let semantics = parse_cargo_unit_semantics(
            unit.get("semantics"),
            semantics_sha256,
            &format!("Targo proof inventory unit {position}"),
        )?;
        let envelope = serde_json::json!({
            "target": {"name": target_name, "kind": target_kinds},
            "trust_compile_target": compile_target,
            "trust_compile_mode": unit.get("trust_compile_mode"),
            "trust_compile_kind": unit.get("trust_compile_kind"),
            "trust_unit_identity_sha256": unit.get("trust_unit_identity_sha256"),
            "trust_compile_target_spec_sha256": unit.get("compile_target_spec_sha256"),
            "trust_proof_unit": proof_unit,
        });
        let target = cargo_target_identity(&envelope, package_id, selected_packages)?
            .ok_or_else(|| "Targo proof inventory contained a null proof identity".to_string())?;
        if !cargo_unit_mode_emits_queued_compiler_evidence(&target.proof_unit_mode) {
            return Err(format!(
                "Targo proof inventory declared a Cargo Unit without authenticated per-Unit compiler protocol `{}` as a proof target",
                target.report_label()
            ));
        }
        validate_cargo_unit_semantics_for_target(&semantics, &target)?;
        if target.proof_unit_role == "dependency" && !include_dependencies {
            return Err(format!(
                "Targo proof inventory declared dependency unit `{}` while its dependency policy was false",
                target.report_label()
            ));
        }
        if previous_index.is_some_and(|previous| previous >= target.proof_unit_index) {
            return Err(format!(
                "Targo proof inventory units were not strictly sorted by unique unit index at {}",
                target.proof_unit_index
            ));
        }
        previous_index = Some(target.proof_unit_index);
        admit_proof_unit_identity(&mut proof_unit_identities, &target)?;
        admit_primary_compile_target(&mut primary_compile_targets, &target)?;
        if !proof_targets.insert(target.clone()) {
            return Err(format!(
                "Targo proof inventory duplicated target `{}`",
                target.report_label()
            ));
        }
        if unit_semantics.insert(target.clone(), semantics).is_some() {
            return Err(format!(
                "Targo proof inventory duplicated semantics for `{}`",
                target.report_label()
            ));
        }
    }

    let excluded_units = value
        .get("excluded_units")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "Targo proof inventory omitted its excluded-unit array".to_string())?;
    let mut excluded_targets = BTreeSet::new();
    let mut excluded_reasons = BTreeMap::new();
    let mut excluded_graph_roles = BTreeMap::new();
    let mut previous_excluded_index = None;
    for (position, unit) in excluded_units.iter().enumerate() {
        let index = unit.get("index").and_then(serde_json::Value::as_u64).ok_or_else(|| {
            format!("Targo excluded inventory unit {position} omitted its integer index")
        })?;
        let mode = unit.get("mode").and_then(serde_json::Value::as_str).ok_or_else(|| {
            format!("Targo excluded inventory unit {position} omitted its compile mode")
        })?;
        let exclusion_reason = unit
            .get("exclusion_reason")
            .and_then(serde_json::Value::as_str)
            .filter(|reason| !reason.is_empty() && reason.trim() == *reason)
            .ok_or_else(|| {
                format!(
                    "Targo excluded inventory unit {position} omitted its canonical exclusion reason"
                )
            })?;
        let semantics_sha256 = unit
            .get("semantics_sha256")
            .and_then(serde_json::Value::as_str)
            .ok_or_else(|| {
                format!(
                    "Targo excluded inventory unit {position} omitted its semantic descriptor digest"
                )
            })?;
        let semantics = parse_cargo_unit_semantics(
            unit.get("semantics"),
            semantics_sha256,
            &format!("Targo excluded inventory unit {position}"),
        )?;
        let graph_role = unit
            .get("graph_role")
            .and_then(serde_json::Value::as_str)
            .filter(|role| matches!(*role, "primary" | "test-execution" | "dependency" | "control"))
            .ok_or_else(|| {
                format!(
                    "Targo excluded inventory unit {position} omitted its closed-set Cargo graph role"
                )
            })?;
        let package_id = unit
            .get("package_id")
            .and_then(serde_json::Value::as_str)
            .filter(|package_id| !package_id.is_empty() && package_id.trim() == *package_id)
            .ok_or_else(|| {
                format!("Targo excluded inventory unit {position} omitted its package ID")
            })?;
        let package_name = unit
            .get("package_name")
            .and_then(serde_json::Value::as_str)
            .filter(|name| !name.is_empty() && name.trim() == *name)
            .ok_or_else(|| {
                format!("Targo excluded inventory unit {position} omitted its package name")
            })?;
        let target_name = unit
            .get("target_name")
            .and_then(serde_json::Value::as_str)
            .filter(|target| !target.is_empty() && target.trim() == *target)
            .ok_or_else(|| {
                format!("Targo excluded inventory unit {position} omitted its target name")
            })?;
        let target_kinds =
            unit.get("target_kinds").and_then(serde_json::Value::as_array).ok_or_else(|| {
                format!("Targo excluded inventory unit {position} omitted its target-kind array")
            })?;
        let compile_target = unit
            .get("compile_target")
            .and_then(serde_json::Value::as_str)
            .filter(|target| !target.is_empty())
            .ok_or_else(|| {
                format!("Targo excluded inventory unit {position} omitted its compile target")
            })?;
        let synthetic_envelope = serde_json::json!({
            "target": {"name": target_name, "kind": target_kinds},
            "trust_compile_target": compile_target,
            "trust_compile_mode": unit.get("trust_compile_mode"),
            "trust_compile_kind": unit.get("trust_compile_kind"),
            "trust_unit_identity_sha256": unit.get("trust_unit_identity_sha256"),
            "trust_compile_target_spec_sha256": unit.get("compile_target_spec_sha256"),
            "trust_proof_unit": {
                "schema": TARGO_TRUST_PROOF_UNIT_SCHEMA_V2,
                "index": index,
                "mode": mode,
                "role": "excluded",
                "package_name": package_name,
                "semantics_sha256": semantics_sha256,
            },
        });
        let target =
            cargo_excluded_target_identity(&synthetic_envelope, package_id, selected_packages)?
                .ok_or_else(|| {
                    "Targo excluded inventory synthesized a null unit identity".to_string()
                })?;
        validate_cargo_unit_semantics_for_target(&semantics, &target)?;
        validate_cargo_excluded_graph_role_scope(&target, graph_role, selected_packages)?;
        if exclusion_reason == TARGO_TRUST_EXCLUSION_EMPTY_DOCTEST {
            return Err(format!(
                "Targo inventory declared doctest Unit `{}` empty; only its authenticated doctest census can establish that",
                target.report_label()
            ));
        }
        validate_cargo_exclusion_reason(
            include_dependencies,
            &target,
            exclusion_reason,
            graph_role,
        )?;
        if previous_excluded_index.is_some_and(|previous| previous >= index) {
            return Err(format!(
                "Targo excluded inventory units were not strictly sorted by unique unit index at {index}"
            ));
        }
        previous_excluded_index = Some(index);
        if proof_unit_identities.contains_key(&index) {
            return Err(format!(
                "Cargo Unit index {index} appeared in both proof and excluded inventories"
            ));
        }
        if !excluded_targets.insert(target.clone()) {
            return Err(format!(
                "Targo excluded inventory duplicated target `{}`",
                target.report_label()
            ));
        }
        if excluded_reasons.insert(target.clone(), exclusion_reason.to_string()).is_some() {
            return Err(format!(
                "Targo excluded inventory duplicated exclusion reason for `{}`",
                target.report_label()
            ));
        }
        if excluded_graph_roles.insert(target.clone(), graph_role.to_string()).is_some() {
            return Err(format!(
                "Targo excluded inventory duplicated graph role for `{}`",
                target.report_label()
            ));
        }
        if unit_semantics.insert(target.clone(), semantics).is_some() {
            return Err(format!(
                "Targo excluded inventory duplicated semantics for `{}`",
                target.report_label()
            ));
        }
    }

    let mut all_indices = proof_targets
        .iter()
        .map(|target| target.proof_unit_index)
        .chain(excluded_targets.iter().map(|target| target.proof_unit_index))
        .collect::<Vec<_>>();
    all_indices.sort_unstable();
    let count = u64::try_from(all_indices.len()).map_err(|_| {
        "Targo proof inventory contained more units than its index domain can represent".to_string()
    })?;
    let expected_indices = (0..count).collect::<Vec<_>>();
    if all_indices != expected_indices {
        return Err(format!(
            "Targo proof and excluded inventories did not form one complete Cargo Unit index domain (expected={expected_indices:?}, actual={all_indices:?})"
        ));
    }
    validate_dependency_policy_never_scopes_out_a_selected_package(
        &proof_targets,
        &excluded_targets,
        &excluded_reasons,
        selected_packages,
    )?;
    Ok(CargoProofInventory {
        include_dependencies,
        proof_targets,
        excluded_targets,
        excluded_reasons,
        excluded_graph_roles,
        unit_semantics,
    })
}

/// The dependency off-switch must never be the reason a package the user
/// explicitly selected went unverified.
///
/// Targo scopes verification per compilation Unit: a resolved root Unit is
/// compiled with verification on, and every other graph Unit gets the explicit
/// `-Ztrust-verify=off` compiler off-switch plus a `dependency-policy`
/// exclusion row. A selected package can legitimately own such rows — the same
/// package is frequently built twice (host proc-macro/build-dependency copy
/// beside the target copy), and only the root copy is a proof unit — so a
/// per-Unit rule would over-reject. The invariant that actually protects the
/// user is per PACKAGE: if the dependency policy scoped out a Unit of a
/// selected package, that package must still have contributed at least one Unit
/// to the proof frontier.
///
/// Without this, an inventory that labels a selected package's own root Unit
/// `graph_role="dependency"` passes every other check (the graph-role scope
/// check only rejects the converse, an *unselected* package claiming a selected
/// role), and `dep_tcb` then blesses it as an ordinary `dependency-scope`
/// assumption — so the crate the user asked to verify is silently reported as a
/// trusted third-party dependency instead. Fail closed instead.
///
/// Deliberately keyed on `dependency-policy` alone: the doc, doctest and
/// `--compile-time-deps` exclusion reasons legitimately empty a selected
/// package's proof frontier and are gated separately (they are never
/// dep-TCB-admitted).
fn validate_dependency_policy_never_scopes_out_a_selected_package(
    proof_targets: &BTreeSet<CargoTargetIdentity>,
    excluded_targets: &BTreeSet<CargoTargetIdentity>,
    excluded_reasons: &BTreeMap<CargoTargetIdentity, String>,
    selected_packages: &BTreeMap<String, String>,
) -> Result<(), String> {
    for target in excluded_targets {
        if excluded_reasons.get(target).map(String::as_str)
            != Some(TARGO_TRUST_EXCLUSION_DEPENDENCY_POLICY)
        {
            continue;
        }
        if selected_packages.get(&target.package_id) != Some(&target.package_name) {
            continue;
        }
        if proof_targets.iter().any(|proof| proof.package_id == target.package_id) {
            continue;
        }
        return Err(format!(
            "Targo dependency policy scoped out selected package {:?} without leaving any of its Units in the proof frontier: {}",
            target.package_name,
            target.report_label()
        ));
    }
    Ok(())
}

fn parse_cargo_unit_semantics(
    value: Option<&serde_json::Value>,
    claimed_sha256: &str,
    context: &str,
) -> Result<trust_types::CargoUnitSemanticsReport, String> {
    if !canonical_sha256_hex(claimed_sha256) {
        return Err(format!("{context} carried a non-canonical semantic descriptor SHA-256"));
    }
    let value = value.ok_or_else(|| format!("{context} omitted its semantic descriptor"))?;
    let semantics = serde_json::from_value::<trust_types::CargoUnitSemanticsReport>(value.clone())
        .map_err(|error| format!("{context} semantic descriptor was invalid: {error}"))?;
    let canonical = serde_json::to_value(&semantics).map_err(|error| {
        format!("{context} semantic descriptor could not be serialized: {error}")
    })?;
    if canonical != *value {
        return Err(format!(
            "{context} semantic descriptor was not in canonical closed-schema form"
        ));
    }
    validate_cargo_unit_semantics(&semantics, context)?;
    let actual_sha256 =
        cargo_unit_semantics_sha256(&semantics).map_err(|error| format!("{context} {error}"))?;
    if actual_sha256 != claimed_sha256 {
        return Err(format!("{context} semantic descriptor did not match its Cargo-owned SHA-256"));
    }
    Ok(semantics)
}

pub(crate) fn cargo_unit_semantics_sha256(
    semantics: &trust_types::CargoUnitSemanticsReport,
) -> Result<String, String> {
    let bytes = serde_json::to_vec(semantics)
        .map_err(|error| format!("semantic descriptor could not be hashed: {error}"))?;
    Ok(format!("{:x}", Sha256::digest(bytes)))
}

pub(crate) fn validate_cargo_unit_semantics(
    semantics: &trust_types::CargoUnitSemanticsReport,
    context: &str,
) -> Result<(), String> {
    if semantics.schema != TARGO_TRUST_UNIT_SEMANTICS_SCHEMA_V1 {
        return Err(format!(
            "{context} semantic descriptor used unsupported schema {:?}",
            semantics.schema
        ));
    }
    for (label, values, allow_empty) in [
        ("features", semantics.features.as_slice(), true),
        ("target_cfg", semantics.target_cfg.as_slice(), true),
        ("target_crate_types", semantics.target_crate_types.as_slice(), false),
    ] {
        if !allow_empty && values.is_empty() {
            return Err(format!("{context} semantic descriptor {label} was empty"));
        }
        if let Some(value) =
            values.iter().find(|value| value.is_empty() || value.trim() != value.as_str())
        {
            return Err(format!(
                "{context} semantic descriptor {label} contained a non-canonical value {value:?}"
            ));
        }
        if let Some(pair) = values.windows(2).find(|pair| pair[0] >= pair[1]) {
            return Err(format!(
                "{context} semantic descriptor {label} was not strictly sorted and duplicate-free at {:?}, {:?}",
                pair[0], pair[1]
            ));
        }
    }
    if let Some(crate_type) = semantics.target_crate_types.iter().find(|crate_type| {
        !matches!(
            crate_type.as_str(),
            "bin" | "lib" | "rlib" | "dylib" | "cdylib" | "staticlib" | "proc-macro"
        )
    }) {
        return Err(format!(
            "{context} Cargo-resolved Unit configuration had unsupported target crate type {crate_type:?}"
        ));
    }
    if !matches!(semantics.target_edition.as_str(), "2015" | "2018" | "2021" | "2024") {
        return Err(format!(
            "{context} semantic descriptor had unsupported target edition {:?}",
            semantics.target_edition
        ));
    }
    let compiler = &semantics.compiler;
    if !matches!(compiler.frontend.as_str(), "rustc" | "rustdoc" | "cargo-control") {
        return Err(format!(
            "{context} semantic descriptor had unsupported frontend {:?}",
            compiler.frontend
        ));
    }
    if !matches!(
        compiler.codegen_backend.as_str(),
        "trust-cg" | "llvm" | "rustc-default" | "not-applicable"
    ) {
        return Err(format!(
            "{context} semantic descriptor had unsupported codegen backend {:?}",
            compiler.codegen_backend
        ));
    }
    if (compiler.frontend == "cargo-control") != (compiler.codegen_backend == "not-applicable") {
        return Err(format!(
            "{context} semantic descriptor frontend/backend pairing was inconsistent"
        ));
    }
    if compiler.rustc_release.is_empty()
        || compiler.rustc_release.trim() != compiler.rustc_release
        || compiler.rustc_host.is_empty()
        || compiler.rustc_host.trim() != compiler.rustc_host
        || !canonical_sha256_hex(&compiler.rustc_verbose_version_sha256)
    {
        return Err(format!(
            "{context} semantic descriptor carried a non-canonical compiler identity"
        ));
    }
    if compiler.rustc_commit_hash.as_deref().is_some_and(|hash| {
        hash != "unknown"
            && !((hash.len() == 40 || hash.len() == 64)
                && hash.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)))
    }) {
        return Err(format!(
            "{context} semantic descriptor carried a non-canonical rustc commit hash"
        ));
    }
    let profile = &semantics.profile;
    for (label, value) in [
        ("opt_level", profile.opt_level.as_str()),
        ("requested_lto", profile.requested_lto.as_str()),
        ("effective_lto", profile.effective_lto.as_str()),
        ("debuginfo", profile.debuginfo.as_str()),
        ("panic", profile.panic.as_str()),
        ("strip", profile.strip.as_str()),
    ] {
        if value.is_empty() || value.trim() != value {
            return Err(format!("{context} semantic descriptor profile {label} was non-canonical"));
        }
    }
    if !matches!(profile.opt_level.as_str(), "0" | "1" | "2" | "3" | "s" | "z") {
        return Err(format!(
            "{context} Cargo-resolved Unit configuration profile optimization level was unsupported"
        ));
    }
    if !matches!(profile.requested_lto.as_str(), "false" | "true" | "off" | "thin" | "fat") {
        return Err(format!(
            "{context} Cargo-resolved Unit configuration profile requested LTO was unsupported"
        ));
    }
    if !matches!(profile.panic.as_str(), "unwind" | "abort" | "immediate-abort") {
        return Err(format!(
            "{context} semantic descriptor profile panic strategy was unsupported"
        ));
    }
    if !matches!(
        profile.effective_lto.as_str(),
        "fat"
            | "run:thin"
            | "run:fat"
            | "off"
            | "only-bitcode"
            | "object-and-bitcode"
            | "only-object"
    ) {
        return Err(format!("{context} semantic descriptor profile effective LTO was unsupported"));
    }
    if !matches!(
        profile.debuginfo.as_str(),
        "0" | "1" | "2" | "line-directives-only" | "line-tables-only"
    ) {
        return Err(format!("{context} semantic descriptor profile debuginfo was unsupported"));
    }
    if profile
        .split_debuginfo
        .as_deref()
        .is_some_and(|value| !matches!(value, "off" | "packed" | "unpacked"))
    {
        return Err(format!(
            "{context} Cargo-resolved Unit configuration profile split debuginfo was unsupported"
        ));
    }
    if !matches!(profile.strip.as_str(), "none" | "debuginfo" | "symbols") {
        return Err(format!(
            "{context} Cargo-resolved Unit configuration profile strip setting was unsupported"
        ));
    }
    if profile.codegen_units == Some(0) {
        return Err(format!(
            "{context} Cargo-resolved Unit configuration profile codegen-units was zero"
        ));
    }
    if profile
        .codegen_backend
        .as_deref()
        .is_some_and(|backend| !matches!(backend, "trust-cg" | "llvm"))
    {
        return Err(format!(
            "{context} semantic descriptor profile codegen backend was unsupported"
        ));
    }
    if let Some(trim_paths) = profile.trim_paths.as_deref() {
        let valid = if matches!(trim_paths, "all" | "none") {
            true
        } else {
            let mut seen = BTreeSet::new();
            trim_paths.split(',').all(|scope| {
                matches!(scope, "diagnostics" | "macro" | "object") && seen.insert(scope)
            })
        };
        if !valid {
            return Err(format!(
                "{context} Cargo-resolved Unit configuration profile trim-paths setting was unsupported or duplicated"
            ));
        }
    }
    Ok(())
}

fn validate_cargo_unit_semantics_for_target(
    semantics: &trust_types::CargoUnitSemanticsReport,
    target: &CargoTargetIdentity,
) -> Result<(), String> {
    let expected_frontend = match target.proof_unit_mode.as_str() {
        "test" | "build" | "check-test" | "check" => "rustc",
        "doc" | "doctest" | "docscrape" => "rustdoc",
        "run-custom-build" => "cargo-control",
        _ => {
            return Err(format!(
                "Cargo Unit semantic descriptor was attached to an unsupported mode: {}",
                target.report_label()
            ));
        }
    };
    if semantics.compiler.frontend != expected_frontend {
        return Err(format!(
            "Cargo Unit semantic descriptor frontend {:?} did not match mode {:?}: {}",
            semantics.compiler.frontend,
            target.proof_unit_mode,
            target.report_label()
        ));
    }
    let expected_cfg_test =
        matches!(target.proof_unit_mode.as_str(), "test" | "check-test" | "doctest");
    if semantics.cfg_test != expected_cfg_test {
        return Err(format!(
            "Cargo Unit semantic descriptor cfg_test did not match mode {:?}: {}",
            target.proof_unit_mode,
            target.report_label()
        ));
    }
    Ok(())
}

fn cargo_unit_mode_emits_queued_compiler_evidence(mode: &str) -> bool {
    matches!(mode, "test" | "build" | "check-test" | "check")
}

fn validate_cargo_excluded_graph_role_scope(
    target: &CargoTargetIdentity,
    graph_role: &str,
    selected_packages: &BTreeMap<String, String>,
) -> Result<(), String> {
    if matches!(graph_role, "primary" | "test-execution")
        && selected_packages.get(&target.package_id) != Some(&target.package_name)
    {
        return Err(format!(
            "Targo excluded Cargo Unit claimed selected graph role {graph_role:?} outside the exact selected package set: {}",
            target.report_label()
        ));
    }
    if matches!(graph_role, "primary" | "test-execution")
        && target.target_kinds.iter().any(|kind| kind == "custom-build")
    {
        return Err(format!(
            "Targo excluded custom-build Unit claimed selected graph role {graph_role:?}: {}",
            target.report_label()
        ));
    }
    if graph_role == "test-execution"
        && (target.proof_unit_mode != "build"
            || !target
                .target_kinds
                .iter()
                .any(|kind| matches!(kind.as_str(), "lib" | "rlib" | "dylib" | "bin")))
    {
        return Err(format!(
            "Targo excluded test-execution graph Unit was not a Build-mode library or binary: {}",
            target.report_label()
        ));
    }
    Ok(())
}

fn validate_cargo_exclusion_reason(
    include_dependencies: bool,
    target: &CargoTargetIdentity,
    reason: &str,
    graph_role: &str,
) -> Result<(), String> {
    match reason {
        TARGO_TRUST_EXCLUSION_DEPENDENCY_POLICY => {
            if include_dependencies {
                return Err(format!(
                    "Targo excluded Cargo unit `{}` for dependency policy despite include-dependencies=true",
                    target.report_label()
                ));
            }
            if !cargo_unit_mode_emits_queued_compiler_evidence(&target.proof_unit_mode) {
                return Err(format!(
                    "Targo excluded non-compiler Cargo control unit `{}` with the dependency-policy reason",
                    target.report_label()
                ));
            }
            if graph_role != "dependency" {
                return Err(format!(
                    "Targo dependency-policy exclusion carried Cargo graph role {graph_role:?} instead of dependency: {}",
                    target.report_label()
                ));
            }
        }
        TARGO_TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION => {
            if target.proof_unit_mode != "run-custom-build"
                || target.target_kinds.as_slice() != ["custom-build"]
            {
                return Err(format!(
                    "Targo build-script execution exclusion did not name a run-custom-build/custom-build Unit: {}",
                    target.report_label()
                ));
            }
            if graph_role != "control" {
                return Err(format!(
                    "Targo build-script execution exclusion carried Cargo graph role {graph_role:?} instead of control: {}",
                    target.report_label()
                ));
            }
        }
        TARGO_TRUST_EXCLUSION_DEFERRED_DOCTEST | TARGO_TRUST_EXCLUSION_EMPTY_DOCTEST => {
            if target.proof_unit_mode != "doctest"
                || target.target_kinds.iter().any(|kind| kind == "custom-build")
            {
                return Err(format!(
                    "Targo deferred-doctest exclusion did not name a doctest Unit: {}",
                    target.report_label()
                ));
            }
            if !matches!(graph_role, "primary" | "dependency") {
                return Err(format!(
                    "Targo deferred-doctest exclusion carried invalid Cargo graph role {graph_role:?}: {}",
                    target.report_label()
                ));
            }
        }
        TARGO_TRUST_EXCLUSION_DOCUMENTATION => {
            if !matches!(target.proof_unit_mode.as_str(), "doc" | "docscrape") {
                return Err(format!(
                    "Targo documentation exclusion did not name a doc/docscrape Unit: {}",
                    target.report_label()
                ));
            }
            if !matches!(graph_role, "primary" | "dependency") {
                return Err(format!(
                    "Targo documentation exclusion carried invalid Cargo graph role {graph_role:?}: {}",
                    target.report_label()
                ));
            }
        }
        TARGO_TRUST_EXCLUSION_BUILD_SUPPORT_ONLY | TARGO_TRUST_EXCLUSION_AUDITED_TRUST_SPEC => {
            return Err(format!(
                "Targo excluded compiler unit `{}` using retired exclusion reason {reason:?}; compiler dependencies require ordinary proof evidence when include-dependencies=true",
                target.report_label()
            ));
        }
        TARGO_TRUST_EXCLUSION_COMPILE_TIME_DEPS_FILTERED => {
            if !cargo_unit_mode_emits_queued_compiler_evidence(&target.proof_unit_mode) {
                return Err(format!(
                    "Targo compile-time-deps filter exclusion redundantly named a non-proof Cargo mode: {}",
                    target.report_label()
                ));
            }
            if !matches!(graph_role, "primary" | "test-execution" | "dependency") {
                return Err(format!(
                    "Targo compile-time-deps filter exclusion carried invalid Cargo graph role {graph_role:?}: {}",
                    target.report_label()
                ));
            }
        }
        _ => {
            return Err(format!(
                "Targo excluded Cargo unit `{}` carried unsupported exclusion reason {reason:?}",
                target.report_label()
            ));
        }
    }
    Ok(())
}

fn require_declared_proof_target(
    inventory: Option<&CargoProofInventory>,
    target: &CargoTargetIdentity,
) -> Result<(), String> {
    if inventory.is_some_and(|inventory| !inventory.proof_targets.contains(target)) {
        return Err(format!(
            "Cargo compiler evidence named proof unit `{}` outside Targo's declared proof inventory",
            target.report_label()
        ));
    }
    Ok(())
}

fn admit_proof_unit_identity(
    identities: &mut BTreeMap<u64, CargoTargetIdentity>,
    identity: &CargoTargetIdentity,
) -> Result<(), String> {
    if let Some(previous) = identities.insert(identity.proof_unit_index, identity.clone()) {
        if previous != *identity {
            return Err(format!(
                "Cargo proof-unit index {} changed identity within one invocation: before `{}`, after `{}`",
                identity.proof_unit_index,
                previous.report_label(),
                identity.report_label(),
            ));
        }
    }
    Ok(())
}

fn admit_primary_compile_target(
    compile_targets: &mut BTreeSet<(String, Option<String>)>,
    identity: &CargoTargetIdentity,
) -> Result<(), String> {
    // Cross-target builds legitimately verify host build scripts/proc macros
    // in addition to target code when include-dependencies is enabled. Keep
    // the single-target invariant on primary and executed test subjects; every
    // dependency Unit remains separately bound by its Cargo identity above.
    if identity.proof_unit_role == "dependency" {
        return Ok(());
    }
    compile_targets
        .insert((identity.compile_target.clone(), identity.compile_target_spec_sha256.clone()));
    if compile_targets.len() > 1 {
        return Err(format!(
            "evidence-grade Targo invocation compiled selected targets for multiple effective compile targets/semantic identities [{}]; run one exact --target/build.target value and immutable custom target specification per verification invocation",
            compile_targets
                .iter()
                .map(|(target, digest)| format!("target={target:?},spec_sha256={digest:?}"))
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    Ok(())
}

fn cargo_target_identity(
    envelope: &serde_json::Value,
    package_id: &str,
    selected_packages: &BTreeMap<String, String>,
) -> Result<Option<CargoTargetIdentity>, String> {
    cargo_target_identity_impl(envelope, package_id, selected_packages, false)
}

fn cargo_excluded_target_identity(
    envelope: &serde_json::Value,
    package_id: &str,
    selected_packages: &BTreeMap<String, String>,
) -> Result<Option<CargoTargetIdentity>, String> {
    cargo_target_identity_impl(envelope, package_id, selected_packages, true)
}

fn cargo_target_identity_impl(
    envelope: &serde_json::Value,
    package_id: &str,
    selected_packages: &BTreeMap<String, String>,
    allow_excluded_role: bool,
) -> Result<Option<CargoTargetIdentity>, String> {
    let target = envelope
        .get("target")
        .ok_or_else(|| "Cargo evidence envelope omitted target".to_string())?;
    let target_name = target
        .get("name")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| "Cargo evidence target omitted name".to_string())?;
    let compile_target = envelope
        .get("trust_compile_target")
        .and_then(serde_json::Value::as_str)
        .filter(|target| !target.is_empty())
        .ok_or_else(|| {
            "Cargo evidence envelope omitted nonempty Trust compile-target identity".to_string()
        })?;
    let compile_mode = envelope
        .get("trust_compile_mode")
        .and_then(serde_json::Value::as_str)
        .filter(|mode| {
            matches!(
                *mode,
                "build"
                    | "test"
                    | "check"
                    | "check-test"
                    | "doc"
                    | "doctest"
                    | "docscrape"
                    | "run-custom-build"
            )
        })
        .ok_or_else(|| {
            "Cargo evidence envelope omitted a recognized Trust compile-mode identity".to_string()
        })?;
    let unit_identity_sha256 = envelope
        .get("trust_unit_identity_sha256")
        .and_then(serde_json::Value::as_str)
        .filter(|digest| canonical_sha256_hex(digest))
        .ok_or_else(|| {
            "Cargo evidence envelope omitted a canonical Trust unit-identity SHA-256".to_string()
        })?;
    let compile_kind = envelope
        .get("trust_compile_kind")
        .and_then(serde_json::Value::as_str)
        .filter(|kind| matches!(*kind, "host" | "target"))
        .ok_or_else(|| {
            "Cargo evidence envelope omitted a recognized Trust compile-kind identity".to_string()
        })?;
    let compile_target_spec_sha256 = match envelope.get("trust_compile_target_spec_sha256") {
        None | Some(serde_json::Value::Null) => None,
        Some(serde_json::Value::String(digest)) if canonical_sha256_hex(digest) => {
            Some(digest.clone())
        }
        Some(serde_json::Value::String(_)) => {
            return Err(
                "Cargo evidence envelope carried a non-canonical custom target-spec SHA-256"
                    .to_string(),
            );
        }
        Some(_) => {
            return Err(
                "Cargo evidence envelope target-spec SHA-256 was not a string or null".to_string()
            );
        }
    };
    let custom_target = compile_target.ends_with(".json");
    if custom_target != compile_target_spec_sha256.is_some() {
        return Err(if custom_target {
            "Cargo evidence envelope omitted the exact custom JSON target-spec SHA-256".to_string()
        } else {
            "Cargo evidence envelope attached a target-spec SHA-256 to a built-in target tuple"
                .to_string()
        });
    }
    let kinds = target
        .get("kind")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "Cargo evidence target omitted kind array".to_string())?;
    if kinds.is_empty() {
        return Err("Cargo evidence target kind array was empty".to_string());
    }
    let mut target_kinds = kinds
        .iter()
        .map(|kind| {
            kind.as_str()
                .filter(|kind| !kind.is_empty())
                .map(str::to_string)
                .ok_or_else(|| "Cargo evidence target kind was not a nonempty string".to_string())
        })
        .collect::<Result<Vec<_>, _>>()?;
    target_kinds.sort();
    target_kinds.dedup();
    let proof_unit = match envelope.get("trust_proof_unit") {
        None | Some(serde_json::Value::Null) => return Ok(None),
        Some(serde_json::Value::Object(unit)) => unit,
        Some(_) => return Err("Cargo Trust proof-unit identity was not an object".to_string()),
    };
    if proof_unit.get("schema").and_then(serde_json::Value::as_str)
        != Some(TARGO_TRUST_PROOF_UNIT_SCHEMA_V2)
    {
        return Err("Cargo Trust proof-unit identity had an unsupported schema".to_string());
    }
    let proof_unit_index = proof_unit
        .get("index")
        .and_then(serde_json::Value::as_u64)
        .ok_or_else(|| "Cargo Trust proof-unit identity omitted its integer index".to_string())?;
    let proof_unit_mode = proof_unit
        .get("mode")
        .and_then(serde_json::Value::as_str)
        .filter(|mode| {
            matches!(
                *mode,
                "test"
                    | "build"
                    | "check-test"
                    | "check"
                    | "doc"
                    | "doctest"
                    | "docscrape"
                    | "run-custom-build"
            )
        })
        .ok_or_else(|| "Cargo Trust proof-unit identity had an invalid compile mode".to_string())?
        .to_string();
    if proof_unit_mode != compile_mode {
        return Err(format!(
            "Cargo evidence envelope disagreed about its compile mode: trust_compile_mode={compile_mode:?}, proof_unit_mode={proof_unit_mode:?}"
        ));
    }
    let proof_unit_role = proof_unit
        .get("role")
        .and_then(serde_json::Value::as_str)
        .filter(|role| {
            matches!(*role, "primary" | "test-execution" | "dependency")
                || (allow_excluded_role && *role == "excluded")
        })
        .ok_or_else(|| "Cargo Trust proof-unit identity had an invalid role".to_string())?
        .to_string();
    let package_name = proof_unit
        .get("package_name")
        .and_then(serde_json::Value::as_str)
        .filter(|name| !name.is_empty() && name.trim() == *name)
        .ok_or_else(|| "Cargo Trust proof-unit identity omitted its package name".to_string())?
        .to_string();
    let semantics_sha256 = proof_unit
        .get("semantics_sha256")
        .and_then(serde_json::Value::as_str)
        .filter(|digest| canonical_sha256_hex(digest))
        .ok_or_else(|| {
            "Cargo Trust proof-unit identity omitted its canonical semantic descriptor SHA-256"
                .to_string()
        })?
        .to_string();
    if matches!(proof_unit_role.as_str(), "primary" | "test-execution")
        && selected_packages.get(package_id) != Some(&package_name)
    {
        return Err(format!(
            "Cargo Trust {:?} proof unit was not one of the selected packages",
            proof_unit_role
        ));
    }
    if matches!(proof_unit_role.as_str(), "primary" | "test-execution")
        && target_kinds.iter().any(|kind| kind == "custom-build")
    {
        return Err(
            "custom-build target attempted to claim a Trust proof-unit identity".to_string()
        );
    }
    if proof_unit_role == "test-execution"
        && (proof_unit_mode != "build"
            || !target_kinds
                .iter()
                .any(|kind| matches!(kind.as_str(), "lib" | "rlib" | "dylib" | "bin")))
    {
        return Err(
            "Cargo test-execution proof unit was not a Build-mode library or binary execution target"
                .to_string()
        );
    }
    Ok(Some(CargoTargetIdentity {
        package_id: package_id.to_string(),
        package_name,
        target_name: target_name.to_string(),
        target_kinds,
        compile_target: compile_target.to_string(),
        compile_mode: compile_mode.to_string(),
        compile_kind: compile_kind.to_string(),
        unit_identity_sha256: unit_identity_sha256.to_string(),
        compile_target_spec_sha256,
        proof_unit_index,
        proof_unit_mode,
        proof_unit_role,
        semantics_sha256,
    }))
}

fn canonical_sha256_hex(value: &str) -> bool {
    value.len() == 64
        && value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn validate_transport_diagnostic_tag(message: &serde_json::Value) -> Result<(), String> {
    let level = message.get("level").and_then(serde_json::Value::as_str);
    let code =
        message.get("code").and_then(|code| code.get("code")).and_then(serde_json::Value::as_str);
    if level != Some("note") || code != Some(trust_types::TRANSPORT_DIAGNOSTIC_CODE) {
        return Err(
            "TRUST_JSON compiler-message lacked the compiler-owned transport diagnostic tag"
                .to_string(),
        );
    }
    Ok(())
}

fn validate_cargo_transport_envelope(
    envelope: &serde_json::Value,
    json: &str,
    selected_packages: &BTreeMap<String, String>,
    expected_session: &str,
    require_authenticated_coverage: bool,
) -> Result<Option<(CargoTargetIdentity, trust_types::TransportMessage)>, String> {
    let package_id = envelope
        .get("package_id")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| "transport compiler-message omitted package_id".to_string())?;
    let target = cargo_target_identity(envelope, package_id, selected_packages)?.ok_or_else(|| {
        "compiler unit outside Cargo's authenticated proof-subject inventory attempted to emit Trust proof transport"
            .to_string()
    })?;
    let package_name = &target.package_name;
    let crate_name = target.crate_name();
    let mut message = trust_types::parse_transport_payload(json)
        .map_err(|error| format!("compiler-message carried malformed Trust transport: {error}"))?;
    let expected_payload_primary = target.proof_unit_role == "primary";
    let (claimed_package, claimed_crate, claimed_session, primary, coverage) = match &message {
        trust_types::TransportMessage::FunctionResult(result) => (
            result.package_name.as_deref(),
            result.crate_name.as_deref(),
            result.verification_session.as_str(),
            result.primary_package,
            false,
        ),
        trust_types::TransportMessage::CrateSummary(summary) => (
            summary.package_name.as_deref(),
            Some(summary.crate_name.as_str()),
            summary.verification_session.as_str(),
            summary.primary_package,
            false,
        ),
        trust_types::TransportMessage::CoverageSummary(summary) => (
            Some(summary.package_name.as_str()),
            Some(summary.crate_name.as_str()),
            summary.verification_session.as_str(),
            summary.primary_package,
            true,
        ),
        trust_types::TransportMessage::CleanIslandRows(rows) => (
            Some(rows.package_name.as_str()),
            Some(rows.crate_name.as_str()),
            rows.verification_session.as_str(),
            rows.primary_package,
            false,
        ),
        _ => return Err("unsupported Trust transport message in Cargo envelope".to_string()),
    };
    if primary != expected_payload_primary
        || claimed_package != Some(package_name.as_str())
        || claimed_crate.map(normalize_cargo_crate_name).as_deref() != Some(crate_name.as_str())
        || claimed_session != expected_session
    {
        if coverage && !require_authenticated_coverage {
            return Ok(None);
        }
        return Err(format!(
            "Trust transport scope/session does not match Cargo envelope for `{}`",
            target.report_label()
        ));
    }
    // The compiler payload honestly reports its Cargo role: test-execution and
    // dependency units remain non-primary. Once the outer Cargo envelope proves
    // the exact resolved Unit and its graph-derived role, normalize every
    // authenticated proof subject into the aggregate lane. This promotion is
    // impossible from rustc text alone; exact Unit identities keep cfg variants,
    // host dependencies, and target dependencies separate.
    match &mut message {
        trust_types::TransportMessage::FunctionResult(result) => result.primary_package = true,
        trust_types::TransportMessage::CrateSummary(summary) => summary.primary_package = true,
        trust_types::TransportMessage::CoverageSummary(summary) => summary.primary_package = true,
        trust_types::TransportMessage::CleanIslandRows(rows) => rows.primary_package = true,
        _ => unreachable!("supported variants matched above"),
    }
    Ok(Some((target, message)))
}

fn normalize_cargo_crate_name(name: &str) -> String {
    name.chars().map(|character| if character == '-' { '_' } else { character }).collect()
}

pub(crate) fn parse_untrusted_cargo_stderr<R: BufRead>(
    mut reader: R,
    echo: bool,
) -> Vec<CompilerDiagnostic> {
    let mut diagnostics = Vec::new();
    let mut total_bytes = 0usize;
    loop {
        let line = match read_bounded_utf8_line(&mut reader, MAX_COMPILER_STDERR_LINE_BYTES) {
            Ok(Some(line)) => line,
            Ok(None) => break,
            Err(error) => {
                diagnostics.push(CompilerDiagnostic {
                    level: "error".to_string(),
                    message: format!("Cargo stderr input safety limit rejected a line: {error}"),
                });
                break;
            }
        };
        total_bytes = total_bytes.saturating_add(line.len().saturating_add(1));
        let stderr_ceiling = max_authenticated_cargo_transport_bytes();
        if total_bytes > stderr_ceiling {
            diagnostics.push(CompilerDiagnostic {
                level: "error".to_string(),
                message: format!(
                    "Cargo stderr exceeded the {stderr_ceiling}-byte invocation limit"
                ),
            });
            break;
        }
        // Build scripts and other project-controlled children share Cargo's raw
        // stderr. Never interpret a transport-looking line from this channel.
        if line.starts_with(trust_types::TRANSPORT_PREFIX) {
            continue;
        }
        if echo {
            eprintln!("{line}");
        }
        if let Some(level) = compiler_diagnostic_level(&line) {
            diagnostics.push(CompilerDiagnostic { level: level.to_string(), message: line });
        }
    }
    diagnostics
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
enum RawCompilerTransportPhase {
    #[default]
    FunctionRows,
    Coverage,
    CrateSummary,
}

fn raw_transport_scope(message: &trust_types::TransportMessage) -> Option<TransportScopeKey> {
    match message {
        trust_types::TransportMessage::FunctionResult(result) => {
            Some(function_transport_scope(result))
        }
        trust_types::TransportMessage::CoverageSummary(summary) => Some(TransportScopeKey {
            package_name: (!summary.package_name.is_empty()).then(|| summary.package_name.clone()),
            crate_name: summary.crate_name.clone(),
            cargo_target: None,
        }),
        trust_types::TransportMessage::CrateSummary(summary) => Some(TransportScopeKey {
            package_name: summary.package_name.clone(),
            crate_name: summary.crate_name.clone(),
            cargo_target: None,
        }),
        _ => None,
    }
}

fn admit_raw_transport(
    lifecycles: &mut BTreeMap<TransportScopeKey, RawCompilerTransportPhase>,
    message: &trust_types::TransportMessage,
) -> Result<(), String> {
    let Some(scope) = raw_transport_scope(message) else {
        return Ok(());
    };
    let phase = lifecycles.entry(scope.clone()).or_default();
    let scope_label = format!(
        "package={:?},crate={:?}",
        scope.package_name.as_deref().unwrap_or("<unknown-package>"),
        scope.crate_name
    );
    match message {
        trust_types::TransportMessage::FunctionResult(_) => match phase {
            RawCompilerTransportPhase::FunctionRows => Ok(()),
            RawCompilerTransportPhase::Coverage => {
                Err(format!("raw compiler emitted a function row after coverage ({scope_label})"))
            }
            RawCompilerTransportPhase::CrateSummary => Err(format!(
                "raw compiler emitted transport after its terminal crate summary ({scope_label})"
            )),
        },
        trust_types::TransportMessage::CoverageSummary(_) => match phase {
            RawCompilerTransportPhase::FunctionRows => {
                *phase = RawCompilerTransportPhase::Coverage;
                Ok(())
            }
            RawCompilerTransportPhase::Coverage => {
                Err(format!("raw compiler emitted duplicate coverage summaries ({scope_label})"))
            }
            RawCompilerTransportPhase::CrateSummary => Err(format!(
                "raw compiler emitted coverage after its terminal crate summary ({scope_label})"
            )),
        },
        trust_types::TransportMessage::CrateSummary(_) => match phase {
            // Direct compiler parsing retains explicit legacy/advisory support
            // for toolchains predating coverage inventories. Strict coverage
            // policy is enforced later by `require_raw_coverage_authentication`.
            RawCompilerTransportPhase::FunctionRows | RawCompilerTransportPhase::Coverage => {
                *phase = RawCompilerTransportPhase::CrateSummary;
                Ok(())
            }
            RawCompilerTransportPhase::CrateSummary => Err(format!(
                "raw compiler emitted duplicate terminal crate summaries ({scope_label})"
            )),
        },
        _ => Ok(()),
    }
}

pub(crate) fn parse_compiler_stderr<R: BufRead>(reader: R, echo: bool) -> ParsedCompilerOutput {
    let mut reader = reader;
    let mut verification_results = Vec::new();
    let mut structured_results = Vec::new();
    let mut crate_summaries = Vec::new();
    let mut coverage_rows = Vec::new();
    let mut function_envelopes = Vec::new();
    let mut raw_function_sessions = Vec::new();
    let mut raw_crate_summary_sessions = Vec::new();
    let mut raw_transport_ordering_defects = Vec::new();
    let mut crate_observed = BTreeMap::<TransportScopeKey, CrateTransportCounts>::new();
    let mut transport_lifecycles = BTreeMap::<TransportScopeKey, RawCompilerTransportPhase>::new();
    let mut compiler_diagnostics = Vec::new();
    let mut has_structured = false;
    let mut cached_obligations = 0usize;
    let mut total_bytes = 0usize;

    loop {
        let line = match read_bounded_utf8_line(&mut reader, MAX_COMPILER_STDERR_LINE_BYTES) {
            Ok(Some(line)) => line,
            Ok(None) => break,
            Err(error) => {
                has_structured = true;
                structured_results.push(malformed_transport_result(&format!(
                    "targo-trust-bounded-input-rejection: {error}"
                )));
                break;
            }
        };

        total_bytes = total_bytes.saturating_add(line.len().saturating_add(1));
        let stderr_ceiling = max_authenticated_cargo_transport_bytes();
        if total_bytes > stderr_ceiling {
            has_structured = true;
            structured_results.push(malformed_transport_result(&format!(
                "targo-trust-total-input-rejection: compiler stderr exceeded the {}-byte invocation limit",
                stderr_ceiling
            )));
            break;
        }

        if line.starts_with(trust_types::TRANSPORT_PREFIX) {
            if let Some(msg) = trust_types::parse_transport_line(&line) {
                has_structured = true;
                if let Err(reason) = admit_raw_transport(&mut transport_lifecycles, &msg) {
                    raw_transport_ordering_defects.push(reason.clone());
                    structured_results.push(transport_ordering_result(reason));
                }
                match msg {
                    trust_types::TransportMessage::FunctionResult(func_result) => {
                        raw_function_sessions.push(func_result.verification_session.clone());
                        let mut function_results = Vec::new();
                        let identities = crate::types::envelope_identities(&func_result);
                        for (r, identity) in func_result.results.iter().zip(identities) {
                            function_results.push(transport_to_verification_result(
                                &func_result.function,
                                r,
                                func_result.runtime_checks,
                                identity,
                            ));
                        }
                        refuse_shared_test_harness_exclusion_envelope(&mut function_results);
                        let scope = function_transport_scope(&func_result);
                        function_envelopes.push(FunctionEnvelopeIdentity {
                            scope: scope.clone(),
                            function: func_result.function.clone(),
                            primary_package: func_result.primary_package,
                            verification_session: func_result.verification_session.clone(),
                        });
                        let observed = crate_observed.entry(scope).or_default();
                        observed.functions_analyzed += 1;
                        if func_result.total > 0 && func_result.proved == func_result.total {
                            observed.functions_verified += 1;
                        }
                        cached_obligations = cached_obligations.saturating_add(func_result.cached);
                        // The compiler's terminal crate summary accumulates the RAW
                        // transport outcomes from each function envelope. Targo may
                        // conservatively normalize those same rows for its report
                        // (`proved`/`failed`/`runtime_checked` can move buckets when
                        // full-verifier evidence is absent or contradictory), but that
                        // report projection must not manufacture a terminal accounting
                        // mismatch. Function-summary validation below independently
                        // checks each declared counter against its rows; aggregate the
                        // crate comparison from those rows' raw outcome spelling too.
                        add_raw_transport_result_counts(
                            &mut observed.obligations,
                            &func_result.results,
                        );
                        // Trust (TRANSPORT-LINE-BUDGET-1): the compiler's statement that
                        // it fitted this report under the transport line budget must
                        // agree with the rows it travels with. A disagreeing one makes
                        // the whole report malformed: none of its rows is admitted, and
                        // the function is one genuine unknown that says why.
                        if let Some(reason) = func_result
                            .transport_budget
                            .as_ref()
                            .and_then(|disclosure| disclosure.defect(&func_result.results))
                        {
                            function_results =
                                vec![transport_budget_defect_result(&func_result.function, reason)];
                        } else if let Some(reason) =
                            function_transport_summary_defect(&func_result, &function_results)
                        {
                            function_results
                                .push(transport_summary_result(&func_result.function, reason));
                        }
                        structured_results.extend(function_results);
                    }
                    trust_types::TransportMessage::CrateSummary(summary) => {
                        raw_crate_summary_sessions.push(summary.verification_session.clone());
                        crate_summaries.push(summary);
                    }
                    // Trust (assertion-grade coverage): collect the crate-level
                    // coverage accounting; `run_compiler` fail-closes the gate on
                    // any shortfall (`processed < eligible`).
                    trust_types::TransportMessage::CoverageSummary(coverage) => {
                        coverage_rows.push(coverage);
                    }
                    // Island rows are disclosure, read only from an
                    // authenticated Cargo envelope (`admit_clean_island_rows`):
                    // never a proof row here, and no unknown row either.
                    trust_types::TransportMessage::CleanIslandRows(_) => {}
                    _ => {
                        structured_results.push(unsupported_transport_message_result());
                    }
                }
            } else {
                has_structured = true;
                match parse_transport_line_lossy(&line) {
                    Some(results) if !results.is_empty() => structured_results.extend(results),
                    _ => structured_results.push(malformed_transport_result(&line)),
                }
            }
            continue;
        }

        if echo {
            eprintln!("{line}");
        }

        if let Some(result) = parse_trust_note(&line) {
            verification_results.push(result);
        } else if let Some(level) = compiler_diagnostic_level(&line) {
            compiler_diagnostics
                .push(CompilerDiagnostic { level: level.to_string(), message: line });
        }
    }

    let completed_primary_transport_scopes = crate_summaries
        .iter()
        .filter(|summary| summary.primary_package)
        .filter_map(|summary| {
            summary.package_name.as_ref().map(|package| TransportScopeKey {
                package_name: Some(package.clone()),
                crate_name: summary.crate_name.clone(),
                cargo_target: None,
            })
        })
        .collect::<BTreeSet<_>>();

    if has_structured {
        let mut declared = BTreeMap::<TransportScopeKey, trust_types::CrateTransportSummary>::new();
        for summary in crate_summaries.iter().cloned() {
            aggregate_crate_summary(&mut declared, summary);
        }
        for (scope, summary) in &declared {
            let observed = crate_observed.get(scope).cloned().unwrap_or_default();
            if let Some(reason) = crate_transport_summary_defect(summary, &observed) {
                structured_results.push(crate_summary_result(summary, reason));
            }
        }
        verification_results = structured_results;
    }
    let missing_crate_summary_scopes = crate_observed
        .keys()
        .filter(|scope| {
            !crate_summaries.iter().any(|summary| {
                summary.package_name == scope.package_name && summary.crate_name == scope.crate_name
            })
        })
        .cloned()
        .collect();

    ParsedCompilerOutput {
        verification_results,
        compiler_diagnostics,
        cached_obligations,
        coverage_rows,
        compiler_memory_observations: Vec::new(),
        native_admission_observations: Vec::new(),
        native_admission_problems: Vec::new(),
        dropped_coverage: Vec::new(),
        function_envelopes,
        raw_function_sessions,
        raw_crate_summary_sessions,
        raw_transport_ordering_defects,
        completed_proof_targets: BTreeSet::new(),
        coverage_proof_targets: BTreeSet::new(),
        zero_eligible_coverage_targets: BTreeSet::new(),
        observed_proof_targets: BTreeSet::new(),
        saw_structured_transport: has_structured,
        missing_crate_summary_scopes,
        completed_primary_transport_scopes,
    }
}

fn parse_transport_line_lossy(line: &str) -> Option<Vec<VerificationResult>> {
    let json = line.strip_prefix(trust_types::TRANSPORT_PREFIX)?;
    let value: serde_json::Value = serde_json::from_str(json).ok()?;
    if value.get("type").and_then(serde_json::Value::as_str)? != "function_result" {
        return Some(Vec::new());
    }

    let function = value.get("function").and_then(serde_json::Value::as_str)?.to_string();
    let results = value.get("results").and_then(serde_json::Value::as_array)?;
    let parsed = results
        .iter()
        .map(|result| {
            let kind = result
                .get("kind")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("unknown")
                .to_string();
            let message = result
                .get("description")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("")
                .to_string();
            let raw_outcome = result
                .get("outcome")
                .and_then(serde_json::Value::as_str)
                .and_then(trust_types::Outcome::parse);
            // The canonical typed parse already failed, so this row reached us
            // through a lane with no authenticated producer identity. Every
            // unfavorable outcome is carried through unchanged, but a `proved`
            // claim is demoted: a lossy re-read is not a verifier capability and
            // may not mint proof credit.
            let (outcome, fallback_reason) = match raw_outcome {
                Some(trust_types::Outcome::Proved) => (
                    VerificationOutcome::Unknown,
                    Some(
                        "canonical Trust JSON transport parse failed; lossy transport cannot \
                         prove obligations"
                            .to_string(),
                    ),
                ),
                Some(outcome) => (VerificationOutcome::from(outcome), None),
                None => (VerificationOutcome::Unknown, None),
            };
            let backend = result
                .get("solver")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("unknown")
                .to_string();
            let time_ms = result.get("time_ms").and_then(serde_json::Value::as_u64);
            let location = result
                .get("location")
                .cloned()
                .and_then(|location| serde_json::from_value::<SourceSpan>(location).ok());
            let counterexample =
                result.get("counterexample_model").cloned().and_then(|counterexample| {
                    serde_json::from_value::<Counterexample>(counterexample).ok()
                });
            let reason = result
                .get("reason")
                .and_then(serde_json::Value::as_str)
                .map(str::to_string)
                .or(fallback_reason);

            VerificationResult {
                function: function.clone(),
                kind,
                message,
                outcome,
                backend,
                time_ms,
                location,
                counterexample,
                reason,
                raw_line: "targo-trust-lossy-transport".to_string(),
            }
        })
        .collect();
    Some(parsed)
}

#[derive(Clone, Default)]
struct FunctionTransportCounts {
    proved: usize,
    failed: usize,
    unknown: usize,
    timed_out: usize,
    skipped: usize,
    runtime_checked: usize,
    total: usize,
    /// Trust (OD-1 phase 1): how many of the rows in `skipped` are `proved`
    /// instance-discharge rows — the compiler's `assumed_discharge`
    /// ([`compiler_tallies_row_as_assumed_discharge`]). No summary declares
    /// this number and nothing is compared with it. It only says that the
    /// summary beside these rows is no legacy summary
    /// ([`push_legacy_unknown_subset_count_defect`]).
    assumed_discharge: usize,
}

#[derive(Clone, Default)]
struct CrateTransportCounts {
    functions_analyzed: usize,
    functions_verified: usize,
    obligations: FunctionTransportCounts,
}

fn function_transport_scope(result: &trust_types::FunctionTransportResult) -> TransportScopeKey {
    let crate_name = result.crate_name.clone().unwrap_or_else(|| {
        result
            .function
            .split("::")
            .next()
            .filter(|name| !name.is_empty())
            .unwrap_or("<unknown>")
            .to_string()
    });
    TransportScopeKey { package_name: result.package_name.clone(), crate_name, cargo_target: None }
}

fn aggregate_crate_summary(
    summaries: &mut BTreeMap<TransportScopeKey, trust_types::CrateTransportSummary>,
    incoming: trust_types::CrateTransportSummary,
) {
    let key = TransportScopeKey {
        package_name: incoming.package_name.clone(),
        crate_name: incoming.crate_name.clone(),
        cargo_target: None,
    };
    if let Some(summary) = summaries.get_mut(&key) {
        summary.primary_package |= incoming.primary_package;
        summary.functions_analyzed += incoming.functions_analyzed;
        summary.functions_verified += incoming.functions_verified;
        summary.total_proved += incoming.total_proved;
        summary.total_failed += incoming.total_failed;
        summary.total_unknown += incoming.total_unknown;
        summary.total_timed_out += incoming.total_timed_out;
        summary.total_skipped += incoming.total_skipped;
        summary.total_runtime_checked += incoming.total_runtime_checked;
        summary.total_obligations += incoming.total_obligations;
    } else {
        summaries.insert(key, incoming);
    }
}

/// Trust (OD-1 phase 1): whether the compiler's summary counts this RAW row in
/// `skipped` — and so, by the JSON's legacy aggregate, in `unknown` — and in no
/// other bucket.
///
/// Two shapes, exactly the compiler's (`PublishedRowTally::of` and
/// `json_counts`, compiler/rustc_mir_transform/src/trust_verify.rs): a row whose
/// outcome is `skipped`, and a `proved` instance-DISCHARGE row
/// ([`trust_types::assumption::is_instance_hypothesis_discharge_row`], the one
/// predicate the compiler's tally and this crate's gate partition read). A
/// discharge row reports the resolved callee's verdict and carries no proof of
/// its own, so the compiler tallies a `proved` one "assumed (instance
/// discharge)", JSON `skipped`, never `proved` — while the row itself still
/// travels with outcome `proved`. Counting it by that outcome disagreed with
/// the compiler by one row per proved discharge row: every function carrying
/// one, and its crate, got an accounting row (`proved rows=N+1 summary=N,
/// unknown rows=M summary=M+1, skipped rows=K summary=K+1`), an accounting row
/// has no stable key, and a keyless row makes the unit could-not-run (T9): every
/// crate with a proved discharge row was refused.
///
/// Nothing else is admitted, so the cross-check is as closed as it was: the
/// same kind from another solver, a discharge row with any other outcome, and
/// every other `proved` row are counted by their outcome, as the compiler
/// counts them. An envelope that counts a `proved` discharge row `proved` is
/// now the accounting defect: its producer credits the callee's proof twice.
fn compiler_summary_counts_row_as_skipped(row: &trust_types::TransportObligationResult) -> bool {
    row.outcome.is_skipped() || compiler_tallies_row_as_assumed_discharge(row)
}

/// Trust (OD-1 phase 1): the second shape of
/// [`compiler_summary_counts_row_as_skipped`] by itself — the row the
/// compiler's tally files under `assumed_discharge`: outcome `proved`, and the
/// shared predicate for an instance-discharge row.
fn compiler_tallies_row_as_assumed_discharge(row: &trust_types::TransportObligationResult) -> bool {
    row.outcome.is_proved()
        && trust_types::assumption::is_instance_hypothesis_discharge_row(&row.kind, &row.solver)
}

/// Tally one row that [`compiler_summary_counts_row_as_skipped`] names, as the
/// compiler's summary does: `skipped`, and so `unknown`.
fn add_summary_skipped_row(
    counts: &mut FunctionTransportCounts,
    row: &trust_types::TransportObligationResult,
) {
    counts.unknown += 1;
    counts.skipped += 1;
    if compiler_tallies_row_as_assumed_discharge(row) {
        counts.assumed_discharge += 1;
    }
}

fn add_transport_result_counts(
    counts: &mut FunctionTransportCounts,
    transport_rows: &[trust_types::TransportObligationResult],
    rows: &[VerificationResult],
) {
    counts.total += rows.len();
    for (index, result) in rows.iter().enumerate() {
        if let Some(transport) = transport_rows
            .get(index)
            .filter(|transport| compiler_summary_counts_row_as_skipped(transport))
        {
            add_summary_skipped_row(counts, transport);
            continue;
        }
        add_verification_result_count(counts, result);
    }
}

/// Count the compiler's raw outcome buckets for terminal crate-summary
/// reconciliation. This deliberately differs from [`add_transport_result_counts`],
/// which counts Targo's conservative report projection. The terminal producer
/// sums these raw buckets, so comparing it with normalized report buckets would
/// flag Targo's own demotion as counterfeit compiler drift.
fn add_raw_transport_result_counts(
    counts: &mut FunctionTransportCounts,
    transport_rows: &[trust_types::TransportObligationResult],
) {
    counts.total += transport_rows.len();
    for result in transport_rows {
        let Some(bucket) = raw_transport_bucket(result) else {
            add_summary_skipped_row(counts, result);
            continue;
        };
        add_summary_count(counts, bucket);
    }
}

fn add_verification_result_count(
    counts: &mut FunctionTransportCounts,
    result: &VerificationResult,
) {
    match result.outcome {
        VerificationOutcome::Proved => counts.proved += 1,
        VerificationOutcome::Failed => counts.failed += 1,
        VerificationOutcome::RuntimeChecked => counts.runtime_checked += 1,
        VerificationOutcome::Unknown => counts.unknown += 1,
        VerificationOutcome::Timeout => {
            counts.unknown += 1;
            counts.timed_out += 1;
        }
    }
}

/// Map a compiler-emitted transport row to the `VerificationOutcome` bucket
/// the compiler's summary counted it in. Returns `None` for the rows that
/// summary counts `skipped` ([`compiler_summary_counts_row_as_skipped`]: a
/// `skipped` row, and a `proved` instance-discharge row), which
/// `add_transport_result_counts` already accounts for identically from the raw
/// row on both sides, so they never contribute a normalization shift.
fn raw_transport_bucket(
    row: &trust_types::TransportObligationResult,
) -> Option<VerificationOutcome> {
    if compiler_summary_counts_row_as_skipped(row) {
        return None;
    }
    Some(row.outcome.into())
}

/// Remove one obligation of `bucket` from `counts`, the inverse of
/// `add_verification_result_count`. Returns `false` (leaving `counts` untouched)
/// when the bucket has no budget — the floor that keeps a genuine compiler
/// miscount detectable instead of silently rebalancing it away.
fn try_remove_summary_count(
    counts: &mut FunctionTransportCounts,
    bucket: VerificationOutcome,
) -> bool {
    match bucket {
        VerificationOutcome::Proved if counts.proved > 0 => counts.proved -= 1,
        VerificationOutcome::Failed if counts.failed > 0 => counts.failed -= 1,
        VerificationOutcome::RuntimeChecked if counts.runtime_checked > 0 => {
            counts.runtime_checked -= 1
        }
        VerificationOutcome::Unknown if counts.unknown > 0 => counts.unknown -= 1,
        VerificationOutcome::Timeout if counts.unknown > 0 && counts.timed_out > 0 => {
            counts.unknown -= 1;
            counts.timed_out -= 1;
        }
        _ => return false,
    }
    true
}

/// Add one obligation of `bucket` to `counts`, matching the field effects of
/// `add_verification_result_count` (Timeout is a subset of Unknown).
fn add_summary_count(counts: &mut FunctionTransportCounts, bucket: VerificationOutcome) {
    match bucket {
        VerificationOutcome::Proved => counts.proved += 1,
        VerificationOutcome::Failed => counts.failed += 1,
        VerificationOutcome::RuntimeChecked => counts.runtime_checked += 1,
        VerificationOutcome::Unknown => counts.unknown += 1,
        VerificationOutcome::Timeout => {
            counts.unknown += 1;
            counts.timed_out += 1;
        }
    }
}

/// The compiler derives each function's transport SUMMARY from the RAW obligation
/// outcomes, but `add_transport_result_counts` derives the OBSERVED counts from
/// targo's normalized rows (`normalize_transport_outcome` downgrades full-verifier
/// rows without publishable proof evidence: e.g. `proved`/`runtime_checked`/`failed`
/// -> `Unknown`/`Failed`/`Timeout`). Comparing normalized observed against the
/// un-normalized summary flags targo's own normalization as a phantom mismatch.
/// Fold the same per-row reclassification into the expected summary so the check
/// compares like with like across ALL raw->normalized transitions, while the
/// per-bucket floor still surfaces a genuine compiler miscount the normalization
/// cannot explain.
fn normalization_adjusted_expected(
    func_result: &trust_types::FunctionTransportResult,
    rows: &[VerificationResult],
) -> FunctionTransportCounts {
    let mut expected = FunctionTransportCounts {
        proved: func_result.proved,
        failed: func_result.failed,
        unknown: func_result.unknown,
        timed_out: func_result.timed_out,
        skipped: func_result.skipped,
        runtime_checked: func_result.runtime_checked,
        total: func_result.total,
        assumed_discharge: 0,
    };
    for (transport, result) in func_result.results.iter().zip(rows) {
        let Some(raw_bucket) = raw_transport_bucket(transport) else {
            continue;
        };
        let normalized_bucket = result.outcome;
        if raw_bucket == normalized_bucket {
            continue;
        }
        if try_remove_summary_count(&mut expected, raw_bucket) {
            add_summary_count(&mut expected, normalized_bucket);
        }
    }
    expected
}

/// Trust (CB4): the reason written onto a test-harness exclusion row that
/// arrived in an envelope together with any other row.
const SHARED_EXCLUSION_ENVELOPE_DEFECT: &str = "transport defect: a test-harness exclusion row \
     shared its function envelope with another row; an excluded body is excluded whole (the \
     compiler writes exactly one row for it), so this exclusion is refused";

/// Trust (CB4, defense in depth): an exclusion names a WHOLE body. The compiler
/// writes exactly one row for an excluded body — the exclusion — so an
/// envelope that carries an exclusion row beside anything else is not one the
/// compiler produces. Every exclusion row in it loses the compiler's exact
/// reason, so it fails the exact-shape check
/// (`crate::types::test_harness_exclusion_of`) and the gate's partition counts
/// it as a genuine unknown instead of excluding it. The sibling rows are left
/// exactly as they are.
fn refuse_shared_test_harness_exclusion_envelope(rows: &mut [VerificationResult]) {
    if rows.len() <= 1 {
        return;
    }
    for row in rows.iter_mut() {
        if trust_types::exclusion::is_test_harness_exclusion_row_kind(&row.kind) {
            row.reason = Some(SHARED_EXCLUSION_ENVELOPE_DEFECT.to_string());
        }
    }
}

fn function_transport_summary_defect(
    func_result: &trust_types::FunctionTransportResult,
    rows: &[VerificationResult],
) -> Option<String> {
    let mut observed = FunctionTransportCounts::default();
    add_transport_result_counts(&mut observed, &func_result.results, rows);

    let expected = normalization_adjusted_expected(func_result, rows);
    let mut defects = Vec::new();
    push_count_defect(&mut defects, "total", observed.total, expected.total);
    push_count_defect(&mut defects, "proved", observed.proved, expected.proved);
    push_count_defect(&mut defects, "failed", observed.failed, expected.failed);
    push_count_defect(&mut defects, "unknown", observed.unknown, expected.unknown);
    push_legacy_unknown_subset_count_defect(
        &mut defects,
        "timed_out",
        observed.timed_out,
        expected.timed_out,
        observed.unknown,
        expected.unknown,
        observed.assumed_discharge == 0,
    );
    push_legacy_unknown_subset_count_defect(
        &mut defects,
        "skipped",
        observed.skipped,
        expected.skipped,
        observed.unknown,
        expected.unknown,
        observed.assumed_discharge == 0,
    );
    push_count_defect(
        &mut defects,
        "runtime_checked",
        observed.runtime_checked,
        expected.runtime_checked,
    );

    (!defects.is_empty()).then(|| {
        format!(
            "function transport summary for `{}` does not match result rows: {}",
            func_result.function,
            defects.join(", ")
        )
    })
}

fn crate_transport_summary_defect(
    summary: &trust_types::CrateTransportSummary,
    observed: &CrateTransportCounts,
) -> Option<String> {
    let mut defects = Vec::new();
    push_count_defect(
        &mut defects,
        "functions_analyzed",
        observed.functions_analyzed,
        summary.functions_analyzed,
    );
    push_count_defect(
        &mut defects,
        "functions_verified",
        observed.functions_verified,
        summary.functions_verified,
    );
    push_count_defect(&mut defects, "total", observed.obligations.total, summary.total_obligations);
    push_count_defect(&mut defects, "proved", observed.obligations.proved, summary.total_proved);
    push_count_defect(&mut defects, "failed", observed.obligations.failed, summary.total_failed);
    push_count_defect(&mut defects, "unknown", observed.obligations.unknown, summary.total_unknown);
    push_legacy_unknown_subset_count_defect(
        &mut defects,
        "timed_out",
        observed.obligations.timed_out,
        summary.total_timed_out,
        observed.obligations.unknown,
        summary.total_unknown,
        observed.obligations.assumed_discharge == 0,
    );
    push_legacy_unknown_subset_count_defect(
        &mut defects,
        "skipped",
        observed.obligations.skipped,
        summary.total_skipped,
        observed.obligations.unknown,
        summary.total_unknown,
        observed.obligations.assumed_discharge == 0,
    );
    push_count_defect(
        &mut defects,
        "runtime_checked",
        observed.obligations.runtime_checked,
        summary.total_runtime_checked,
    );

    (!defects.is_empty()).then(|| {
        format!(
            "crate transport summary for `{}` does not match function result rows: {}",
            summary.crate_name,
            defects.join(", ")
        )
    })
}

fn push_count_defect(defects: &mut Vec<String>, label: &str, observed: usize, expected: usize) {
    if observed != expected {
        defects.push(format!("{label} rows={observed} summary={expected}"));
    }
}

/// A split of `unknown` (`timed_out`, `skipped`). A summary that declares none
/// (`0`) under an agreeing `unknown` is the JSON's legacy aggregate, written
/// before the split existed, and is not held to it — while
/// `legacy_summary_possible`.
///
/// Trust (OD-1 phase 1): it is not possible once a `proved` instance-discharge
/// row is among the rows (`FunctionTransportCounts::assumed_discharge`). The
/// compiler that publishes that row writes both splits into every summary
/// (`PublishedRowTally::json_counts`), and `skipped` is where its tally counts
/// the row (`unknown` only as the aggregate over it), so a zero beside it is a
/// miscount, not an old format.
/// Without this, tallying the row as the compiler does would have let more
/// through than the compiler's own counters: a summary that counts the row
/// `unknown` and nowhere else, or one that drops a timeout beside it. No
/// compiler writes either, and this check refused both while it still counted
/// the row `proved`.
fn push_legacy_unknown_subset_count_defect(
    defects: &mut Vec<String>,
    label: &str,
    observed: usize,
    expected: usize,
    observed_unknown: usize,
    expected_unknown: usize,
    legacy_summary_possible: bool,
) {
    if legacy_summary_possible && expected == 0 && expected_unknown == observed_unknown {
        return;
    }
    push_count_defect(defects, label, observed, expected);
}

fn transport_summary_result(function: &str, reason: String) -> VerificationResult {
    VerificationResult {
        function: function.to_string(),
        kind: "transport:summary-accounting".to_string(),
        message: "function transport summary does not match result rows".to_string(),
        outcome: VerificationOutcome::Unknown,
        backend: "targo-trust".to_string(),
        time_ms: None,
        location: None,
        counterexample: None,
        reason: Some(reason),
        raw_line: "targo-trust-transport-summary-accounting".to_string(),
    }
}

/// Trust (TRANSPORT-LINE-BUDGET-1): the one row a function's report becomes when its
/// transport budget disclosure disagrees with its rows
/// (`trust_types::transport_budget::TransportBudgetDisclosure::defect`).
fn transport_budget_defect_result(function: &str, reason: String) -> VerificationResult {
    VerificationResult {
        function: function.to_string(),
        kind: "transport:line-budget-disclosure".to_string(),
        message: "function transport budget disclosure does not match its result rows".to_string(),
        outcome: VerificationOutcome::Unknown,
        backend: "targo-trust".to_string(),
        time_ms: None,
        location: None,
        counterexample: None,
        reason: Some(reason),
        raw_line: "targo-trust-transport-line-budget-disclosure".to_string(),
    }
}

fn crate_summary_result(
    summary: &trust_types::CrateTransportSummary,
    reason: String,
) -> VerificationResult {
    VerificationResult {
        function: format!("<crate:{}>", summary.crate_name),
        kind: "transport:crate-summary-accounting".to_string(),
        message: "crate transport summary does not match function result rows".to_string(),
        outcome: VerificationOutcome::Unknown,
        backend: "targo-trust".to_string(),
        time_ms: None,
        location: None,
        counterexample: None,
        reason: Some(reason),
        raw_line: "targo-trust-crate-transport-summary-accounting".to_string(),
    }
}

fn missing_crate_summary_result(scope: &TransportScopeKey) -> VerificationResult {
    let package = scope.package_name.as_deref().unwrap_or("<unknown-package>");
    let function = scope.cargo_target.as_ref().map_or_else(
        || format!("<crate:{}:{}>", package, scope.crate_name),
        |target| format!("<missing-summary:{}>", target.report_label()),
    );
    VerificationResult {
        function,
        kind: "transport:missing-crate-summary".to_string(),
        message: "compiler emitted function rows without an end-of-compile target inventory"
            .to_string(),
        outcome: VerificationOutcome::Unknown,
        backend: "targo-trust".to_string(),
        time_ms: None,
        location: None,
        counterexample: None,
        reason: Some(
            "missing crate_summary transport prevents proof that this rustc target completed"
                .to_string(),
        ),
        raw_line: "targo-trust-missing-crate-summary".to_string(),
    }
}

fn transport_ordering_result(reason: String) -> VerificationResult {
    VerificationResult {
        function: "<transport>".to_string(),
        kind: "transport:ordering".to_string(),
        message: "Trust compiler transport violated its lifecycle ordering".to_string(),
        outcome: VerificationOutcome::Unknown,
        backend: "targo-trust".to_string(),
        time_ms: None,
        location: None,
        counterexample: None,
        reason: Some(reason),
        raw_line: "targo-trust-transport-ordering".to_string(),
    }
}

fn unsupported_transport_message_result() -> VerificationResult {
    VerificationResult {
        function: "<transport>".to_string(),
        kind: "transport:unsupported-message".to_string(),
        message: "unsupported TRUST_JSON transport message variant".to_string(),
        outcome: VerificationOutcome::Unknown,
        backend: "targo-trust".to_string(),
        time_ms: None,
        location: None,
        counterexample: None,
        reason: Some(
            "Trust JSON transport message variant is unsupported by this targo parser".to_string(),
        ),
        raw_line: "targo-trust-unsupported-transport-message".to_string(),
    }
}

fn malformed_transport_result(line: &str) -> VerificationResult {
    VerificationResult {
        function: "<transport>".to_string(),
        kind: "transport:malformed".to_string(),
        message: "malformed TRUST_JSON transport line".to_string(),
        outcome: VerificationOutcome::Unknown,
        backend: "targo-trust".to_string(),
        time_ms: None,
        location: None,
        counterexample: None,
        reason: Some(
            "canonical Trust JSON transport parse failed and no safe lossy rows were recoverable"
                .to_string(),
        ),
        raw_line: line.to_string(),
    }
}

fn missing_structured_transport_result() -> VerificationResult {
    VerificationResult {
        function: "<transport>".to_string(),
        kind: "transport:missing-json".to_string(),
        message: "missing structured Trust JSON transport".to_string(),
        outcome: VerificationOutcome::Unknown,
        backend: "targo-trust".to_string(),
        time_ms: None,
        location: None,
        counterexample: None,
        reason: Some(
            "native verification requested -Z trust-verify-output=json but the compiler emitted no \
             TRUST_JSON transport rows; human-readable Trust diagnostics cannot prove obligations"
                .to_string(),
        ),
        raw_line: "targo-trust-missing-json-transport".to_string(),
    }
}

fn compiler_diagnostic_level(line: &str) -> Option<&'static str> {
    if line.contains("error") {
        Some("error")
    } else if line.contains("warning") {
        Some("warning")
    } else if is_native_full_verifier_diagnostic_line(line) {
        Some("note")
    } else {
        None
    }
}

fn is_native_full_verifier_diagnostic_line(line: &str) -> bool {
    let line = line.to_ascii_lowercase();
    line.contains("native full verifier")
        || line.contains("trust-full-verifier")
        || line.contains("trust full verification failed")
        || line.contains("trust-verify-full")
}

#[cfg(test)]
mod tests {
    mod compiler_scope;
    mod line_budget;

    use super::*;

    /// A compile error's package is the selected package's name, or the name
    /// an unselected package's ID spells in either of Cargo's forms.
    #[test]
    fn a_compile_errors_package_is_named_from_its_cargo_package_id() {
        let selected: BTreeMap<String, String> =
            [("path+file:///w/app#0.1.0".to_string(), "app".to_string())].into_iter().collect();
        for (id, name) in [
            ("path+file:///w/app#0.1.0", "app"),
            ("path+file:///w/crates/helper#0.2.0", "helper"),
            ("path+file:///w/crates/dir#helper@0.2.0", "helper"),
            ("registry+https://github.com/rust-lang/crates.io-index#serde@1.0.0", "serde"),
            ("git+https://example.com/x/tool?branch=main#0.3.0", "tool"),
            ("helper 0.2.0 (path+file:///w/crates/helper)", "helper"),
        ] {
            assert_eq!(cargo_package_name(id, &selected), name, "{id}");
        }
    }

    const TEST_SESSION: &str = "transport-test-session";
    const TEST_COMPILE_TARGET: &str = "x86_64-unknown-linux-gnu";
    const TEST_UNIT_IDENTITY_SHA256: &str =
        "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";

    fn fixture_package_name(package_id: &str) -> &str {
        package_id
            .rsplit('#')
            .next()
            .and_then(|identity| identity.split('@').next())
            .filter(|name| !name.is_empty())
            .expect("fixture package ID must use Cargo's canonical name@version suffix")
    }

    fn fixture_unit_index(package_id: &str, target: &str, target_kind: &str) -> u64 {
        use std::hash::{Hash, Hasher};

        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        (package_id, target, target_kind).hash(&mut hasher);
        hasher.finish()
    }

    fn fixture_unit_semantics(mode: &str) -> trust_types::CargoUnitSemanticsReport {
        let frontend = match mode {
            "test" | "build" | "check-test" | "check" => "rustc",
            "doc" | "doctest" | "docscrape" => "rustdoc",
            "run-custom-build" => "cargo-control",
            other => panic!("unsupported fixture mode {other:?}"),
        };
        trust_types::CargoUnitSemanticsReport {
            schema: TARGO_TRUST_UNIT_SEMANTICS_SCHEMA_V1.to_string(),
            features: Vec::new(),
            target_cfg: vec!["target_arch = \"x86_64\"".to_string(), "unix".to_string()],
            cfg_test: matches!(mode, "test" | "check-test" | "doctest"),
            target_edition: "2024".to_string(),
            target_crate_types: vec!["rlib".to_string()],
            target_harness: true,
            target_proc_macro: false,
            profile: trust_types::CargoUnitProfileSemanticsReport {
                opt_level: "0".to_string(),
                requested_lto: "false".to_string(),
                effective_lto: "only-object".to_string(),
                codegen_backend: None,
                codegen_units: None,
                debuginfo: "0".to_string(),
                split_debuginfo: None,
                debug_assertions: false,
                overflow_checks: false,
                rpath: false,
                incremental: false,
                panic: "unwind".to_string(),
                strip: "none".to_string(),
                rustflags: Vec::new(),
                trim_paths: None,
                hint_mostly_unused: None,
            },
            compiler: trust_types::CargoUnitCompilerSemanticsReport {
                frontend: frontend.to_string(),
                codegen_backend: if frontend == "cargo-control" {
                    "not-applicable"
                } else {
                    "trust-cg"
                }
                .to_string(),
                rustc_release: "1.99.0-nightly".to_string(),
                rustc_commit_hash: Some("a".repeat(40)),
                rustc_host: TEST_COMPILE_TARGET.to_string(),
                rustc_verbose_version_sha256: "b".repeat(64),
            },
            unit_rustflags: vec!["-Zcodegen-backend=trust-cg".to_string()],
            manifest_lint_rustflags: Vec::new(),
            extra_compiler_args: Vec::new(),
        }
    }

    fn fixture_semantics_sha256(semantics: &trust_types::CargoUnitSemanticsReport) -> String {
        format!(
            "{:x}",
            Sha256::digest(serde_json::to_vec(semantics).expect("serialize fixture semantics"))
        )
    }

    fn set_excluded_unit_semantics(unit: &mut serde_json::Value, mode: &str) {
        let semantics = fixture_unit_semantics(mode);
        unit["trust_compile_mode"] = serde_json::json!(mode);
        unit["trust_compile_kind"] = serde_json::json!("target");
        unit["trust_unit_identity_sha256"] = serde_json::json!(TEST_UNIT_IDENTITY_SHA256);
        unit["semantics_sha256"] = serde_json::json!(fixture_semantics_sha256(&semantics));
        unit["semantics"] = serde_json::to_value(semantics).expect("serialize fixture semantics");
    }

    fn cargo_transport_envelope(
        package_id: &str,
        target: &str,
        message: &trust_types::TransportMessage,
    ) -> serde_json::Value {
        cargo_transport_envelope_with_kind(package_id, target, "lib", message)
    }

    fn cargo_transport_envelope_with_kind(
        package_id: &str,
        target: &str,
        target_kind: &str,
        message: &trust_types::TransportMessage,
    ) -> serde_json::Value {
        cargo_transport_envelope_with_kind_and_compile_target(
            package_id,
            target,
            target_kind,
            TEST_COMPILE_TARGET,
            message,
        )
    }

    fn cargo_transport_envelope_with_kind_and_compile_target(
        package_id: &str,
        target: &str,
        target_kind: &str,
        compile_target: &str,
        message: &trust_types::TransportMessage,
    ) -> serde_json::Value {
        cargo_transport_envelope_with_target_identity(
            package_id,
            target,
            target_kind,
            compile_target,
            None,
            message,
        )
    }

    fn cargo_transport_envelope_with_target_identity(
        package_id: &str,
        target: &str,
        target_kind: &str,
        compile_target: &str,
        compile_target_spec_sha256: Option<&str>,
        message: &trust_types::TransportMessage,
    ) -> serde_json::Value {
        let payload = format!(
            "{}{}",
            trust_types::TRANSPORT_PREFIX,
            serde_json::to_string(message).expect("serialize transport")
        );
        let semantics = fixture_unit_semantics("test");
        let semantics_sha256 = fixture_semantics_sha256(&semantics);
        serde_json::json!({
            "reason": "compiler-message",
            "package_id": package_id,
            "trust_compile_target": compile_target,
            "trust_compile_mode": "test",
            "trust_compile_kind": "target",
            "trust_unit_identity_sha256": TEST_UNIT_IDENTITY_SHA256,
            "trust_compile_target_spec_sha256": compile_target_spec_sha256,
            "trust_proof_unit": {
                "schema": TARGO_TRUST_PROOF_UNIT_SCHEMA_V2,
                "index": fixture_unit_index(package_id, target, target_kind),
                "mode": "test",
                "role": "primary",
                "package_name": fixture_package_name(package_id),
                "semantics_sha256": semantics_sha256,
            },
            "target": { "name": target, "kind": [target_kind] },
            "message": {
                "message": payload,
                "level": "note",
                "code": {
                    "code": trust_types::TRANSPORT_DIAGNOSTIC_CODE,
                    "explanation": null
                },
                "rendered": null,
                "spans": [],
                "children": []
            }
        })
    }

    fn cargo_artifact(package_id: &str, target: &str, fresh: bool) -> serde_json::Value {
        cargo_artifact_with_kind(package_id, target, "lib", fresh)
    }

    fn cargo_artifact_with_kind(
        package_id: &str,
        target: &str,
        target_kind: &str,
        fresh: bool,
    ) -> serde_json::Value {
        cargo_artifact_with_kind_and_compile_target(
            package_id,
            target,
            target_kind,
            TEST_COMPILE_TARGET,
            fresh,
        )
    }

    fn cargo_artifact_with_kind_and_compile_target(
        package_id: &str,
        target: &str,
        target_kind: &str,
        compile_target: &str,
        fresh: bool,
    ) -> serde_json::Value {
        cargo_artifact_with_target_identity(
            package_id,
            target,
            target_kind,
            compile_target,
            None,
            fresh,
        )
    }

    fn cargo_artifact_with_target_identity(
        package_id: &str,
        target: &str,
        target_kind: &str,
        compile_target: &str,
        compile_target_spec_sha256: Option<&str>,
        fresh: bool,
    ) -> serde_json::Value {
        let semantics = fixture_unit_semantics("test");
        let semantics_sha256 = fixture_semantics_sha256(&semantics);
        serde_json::json!({
            "reason": "compiler-artifact",
            "package_id": package_id,
            "trust_compile_target": compile_target,
            "trust_compile_mode": "test",
            "trust_compile_kind": "target",
            "trust_unit_identity_sha256": TEST_UNIT_IDENTITY_SHA256,
            "trust_compile_target_spec_sha256": compile_target_spec_sha256,
            "trust_proof_unit": {
                "schema": TARGO_TRUST_PROOF_UNIT_SCHEMA_V2,
                "index": fixture_unit_index(package_id, target, target_kind),
                "mode": "test",
                "role": "primary",
                "package_name": fixture_package_name(package_id),
                "semantics_sha256": semantics_sha256,
            },
            "target": { "name": target, "kind": [target_kind] },
            "profile": {
                "opt_level": "0",
                "debuginfo": 0,
                "debug_assertions": false,
                "overflow_checks": false,
                "test": true,
            },
            "features": [],
            "fresh": fresh
        })
    }

    fn cargo_identity(
        package_id: &str,
        package_name: &str,
        target: &str,
        target_kind: &str,
    ) -> CargoTargetIdentity {
        CargoTargetIdentity {
            package_id: package_id.to_string(),
            package_name: package_name.to_string(),
            target_name: target.to_string(),
            target_kinds: vec![target_kind.to_string()],
            compile_target: TEST_COMPILE_TARGET.to_string(),
            compile_mode: "test".to_string(),
            compile_kind: "target".to_string(),
            unit_identity_sha256: TEST_UNIT_IDENTITY_SHA256.to_string(),
            compile_target_spec_sha256: None,
            proof_unit_index: fixture_unit_index(package_id, target, target_kind),
            proof_unit_mode: "test".to_string(),
            proof_unit_role: "primary".to_string(),
            semantics_sha256: fixture_semantics_sha256(&fixture_unit_semantics("test")),
        }
    }

    fn cargo_identity_with_unit(
        package_id: &str,
        package_name: &str,
        target: &str,
        index: u64,
        role: &str,
    ) -> CargoTargetIdentity {
        let mut identity = cargo_identity(package_id, package_name, target, "lib");
        identity.proof_unit_index = index;
        identity.proof_unit_mode = if role == "test-execution" { "build" } else { "test" }.into();
        identity.compile_mode = identity.proof_unit_mode.clone();
        identity.proof_unit_role = role.to_string();
        identity.semantics_sha256 =
            fixture_semantics_sha256(&fixture_unit_semantics(&identity.proof_unit_mode));
        identity
    }

    fn fixture_semantics_map(
        targets: impl IntoIterator<Item = CargoTargetIdentity>,
    ) -> BTreeMap<CargoTargetIdentity, trust_types::CargoUnitSemanticsReport> {
        targets
            .into_iter()
            .map(|target| {
                let semantics = fixture_unit_semantics(&target.proof_unit_mode);
                assert_eq!(target.semantics_sha256, fixture_semantics_sha256(&semantics));
                (target, semantics)
            })
            .collect()
    }

    #[test]
    fn proof_inventory_report_partitions_sorted_exact_multi_version_units() {
        let primary = cargo_identity_with_unit(
            "path+file:///workspace#root@0.1.0",
            "root",
            "root",
            0,
            "primary",
        );
        let test_execution = cargo_identity_with_unit(
            "path+file:///workspace#root@0.1.0",
            "root",
            "root",
            1,
            "test-execution",
        );
        let mut dependency_v2 = cargo_identity_with_unit(
            "registry+https://example.invalid#index#shared@2.0.0",
            "shared",
            "shared",
            3,
            "dependency",
        );
        dependency_v2.compile_target = "/workspace/targets/custom.json".to_string();
        dependency_v2.compile_target_spec_sha256 = Some("ab".repeat(32));
        let dependency_v1 = cargo_identity_with_unit(
            "registry+https://example.invalid#index#shared@1.0.0",
            "shared",
            "shared",
            2,
            "dependency",
        );
        let proof_targets: BTreeSet<CargoTargetIdentity> =
            [dependency_v2.clone(), primary.clone(), dependency_v1.clone(), test_execution.clone()]
                .into_iter()
                .collect();
        let unit_semantics = fixture_semantics_map(
            proof_targets.iter().cloned().collect::<Vec<CargoTargetIdentity>>(),
        );
        let inventory = CargoProofInventory {
            include_dependencies: true,
            proof_targets,
            excluded_targets: BTreeSet::new(),
            excluded_reasons: BTreeMap::new(),
            excluded_graph_roles: BTreeMap::new(),
            unit_semantics,
        };
        let completed = inventory.proof_targets.clone();
        let covered = [primary, dependency_v2, dependency_v1].into_iter().collect();

        let report = cargo_proof_inventory_report(Some(&inventory), &completed, &covered)
            .expect("build report projection")
            .expect("inventory present");

        assert_eq!(report.schema, trust_types::CARGO_PROOF_INVENTORY_REPORT_SCHEMA_V2);
        assert!(report.include_dependencies);
        assert_eq!(report.declared.primary_roots.len(), 1);
        assert_eq!(report.declared.test_execution_units.len(), 1);
        assert_eq!(report.declared.dependency_units.len(), 2);
        assert_eq!(report.completed, report.declared);
        assert!(report.covered.test_execution_units.is_empty());
        let dependencies = &report.declared.dependency_units;
        assert!(
            dependencies.windows(2).all(|pair| pair[0].proof_unit_index < pair[1].proof_unit_index)
        );
        assert_eq!(dependencies[0].package_name, dependencies[1].package_name);
        assert_eq!(dependencies[0].target_name, dependencies[1].target_name);
        assert_ne!(dependencies[0].package_id, dependencies[1].package_id);
        for unit in report
            .declared
            .primary_roots
            .iter()
            .chain(&report.declared.test_execution_units)
            .chain(&report.declared.dependency_units)
        {
            let semantics = unit.semantics.as_ref().expect("v2 report semantics");
            assert_eq!(
                unit.semantics_sha256.as_deref(),
                Some(fixture_semantics_sha256(semantics).as_str())
            );
        }
        let custom = dependencies
            .iter()
            .find(|unit| unit.package_id.ends_with("shared@2.0.0"))
            .expect("custom-target dependency retained");
        assert_eq!(custom.compile_target, "/workspace/targets/custom.json");
        assert_eq!(
            custom.compile_target_spec_sha256.as_deref(),
            Some("abababababababababababababababababababababababababababababababab")
        );
    }

    #[test]
    fn proof_inventory_report_records_sorted_excluded_active_units() {
        let primary = cargo_identity_with_unit(
            "path+file:///workspace#root@0.1.0",
            "root",
            "root",
            0,
            "primary",
        );
        let mut excluded_v2 = cargo_identity_with_unit(
            "registry+https://example.invalid#index#shared@2.0.0",
            "shared",
            "shared",
            2,
            "dependency",
        );
        excluded_v2.proof_unit_role = "excluded".to_string();
        let mut excluded_v1 = cargo_identity_with_unit(
            "registry+https://example.invalid#index#shared@1.0.0",
            "shared",
            "shared",
            1,
            "dependency",
        );
        excluded_v1.proof_unit_role = "excluded".to_string();
        let unit_semantics =
            fixture_semantics_map([primary.clone(), excluded_v2.clone(), excluded_v1.clone()]);
        let inventory = CargoProofInventory {
            include_dependencies: false,
            proof_targets: [primary].into_iter().collect(),
            excluded_targets: [excluded_v2.clone(), excluded_v1.clone()].into_iter().collect(),
            excluded_reasons: [excluded_v2.clone(), excluded_v1.clone()]
                .into_iter()
                .map(|target| (target, TARGO_TRUST_EXCLUSION_DEPENDENCY_POLICY.to_string()))
                .collect(),
            excluded_graph_roles: [excluded_v2, excluded_v1]
                .into_iter()
                .map(|target| (target, "dependency".to_string()))
                .collect(),
            unit_semantics,
        };

        let report =
            cargo_proof_inventory_report(Some(&inventory), &BTreeSet::new(), &BTreeSet::new())
                .expect("build report projection")
                .expect("inventory present");
        assert_eq!(report.excluded_active_units.len(), 2);
        assert!(
            report
                .excluded_active_units
                .windows(2)
                .all(|pair| { pair[0].proof_unit_index < pair[1].proof_unit_index })
        );
        assert!(report.excluded_active_units.iter().all(|unit| unit.proof_unit_role == "excluded"));
        assert!(report.excluded_active_units.iter().all(|unit| {
            unit.exclusion_reason.as_deref() == Some(TARGO_TRUST_EXCLUSION_DEPENDENCY_POLICY)
        }));
        assert!(report.excluded_active_units.iter().all(|unit| unit.graph_role == "dependency"));
    }

    fn set_envelope_proof_unit(
        envelope: &mut serde_json::Value,
        index: u64,
        mode: &str,
        role: &str,
        package_name: &str,
    ) {
        let semantics = fixture_unit_semantics(mode);
        let semantics_sha256 = fixture_semantics_sha256(&semantics);
        envelope["trust_proof_unit"] = serde_json::json!({
            "schema": TARGO_TRUST_PROOF_UNIT_SCHEMA_V2,
            "index": index,
            "mode": mode,
            "role": role,
            "package_name": package_name,
            "semantics_sha256": semantics_sha256,
        });
        envelope["trust_compile_mode"] = serde_json::json!(mode);
        if envelope.get("reason").and_then(serde_json::Value::as_str) == Some("compiler-artifact") {
            envelope["profile"]["test"] = serde_json::Value::Bool(semantics.cfg_test);
        }
    }

    fn set_transport_primary(message: &mut trust_types::TransportMessage, primary: bool) {
        match message {
            trust_types::TransportMessage::FunctionResult(result) => {
                result.primary_package = primary;
            }
            trust_types::TransportMessage::CrateSummary(summary) => {
                summary.primary_package = primary;
            }
            trust_types::TransportMessage::CoverageSummary(summary) => {
                summary.primary_package = primary;
            }
            _ => panic!("fixture must be a compiler-unit transport message"),
        }
    }

    fn empty_primary_summary(package: &str, krate: &str) -> trust_types::TransportMessage {
        trust_types::TransportMessage::CrateSummary(trust_types::CrateTransportSummary {
            crate_name: krate.to_string(),
            package_name: Some(package.to_string()),
            primary_package: true,
            verification_session: TEST_SESSION.to_string(),
            functions_analyzed: 0,
            functions_verified: 0,
            total_proved: 0,
            total_failed: 0,
            total_unknown: 0,
            total_timed_out: 0,
            total_skipped: 0,
            total_runtime_checked: 0,
            total_obligations: 0,
        })
    }

    fn one_unknown_primary_summary(package: &str, krate: &str) -> trust_types::TransportMessage {
        trust_types::TransportMessage::CrateSummary(trust_types::CrateTransportSummary {
            crate_name: krate.to_string(),
            package_name: Some(package.to_string()),
            primary_package: true,
            verification_session: TEST_SESSION.to_string(),
            functions_analyzed: 1,
            functions_verified: 0,
            total_proved: 0,
            total_failed: 0,
            total_unknown: 1,
            total_timed_out: 0,
            total_skipped: 0,
            total_runtime_checked: 0,
            total_obligations: 1,
        })
    }

    fn complete_coverage(package: &str, krate: &str) -> trust_types::TransportMessage {
        complete_coverage_for(package, krate, &format!("{krate}::f"))
    }

    fn complete_coverage_for(
        package: &str,
        krate: &str,
        function: &str,
    ) -> trust_types::TransportMessage {
        trust_types::TransportMessage::CoverageSummary(trust_types::CoverageTransportSummary {
            crate_name: krate.to_string(),
            package_name: package.to_string(),
            primary_package: true,
            verification_session: TEST_SESSION.to_string(),
            eligible: 1,
            processed: 1,
            noted_stops: Vec::new(),
            degraded_anchors: 0,
            function_identities: Some(trust_types::CoverageFunctionIdentityInventory {
                schema: trust_types::COVERAGE_FUNCTION_IDENTITY_SCHEMA_V1.to_string(),
                eligible_functions: vec![function.to_string()],
                processed_functions: vec![function.to_string()],
            }),
            memory: trust_types::MemorySummary::default(),
        })
    }

    fn empty_complete_coverage(package: &str, krate: &str) -> trust_types::TransportMessage {
        trust_types::TransportMessage::CoverageSummary(trust_types::CoverageTransportSummary {
            crate_name: krate.to_string(),
            package_name: package.to_string(),
            primary_package: true,
            verification_session: TEST_SESSION.to_string(),
            eligible: 0,
            processed: 0,
            noted_stops: Vec::new(),
            degraded_anchors: 0,
            function_identities: Some(trust_types::CoverageFunctionIdentityInventory {
                schema: trust_types::COVERAGE_FUNCTION_IDENTITY_SCHEMA_V1.to_string(),
                eligible_functions: Vec::new(),
                processed_functions: Vec::new(),
            }),
            memory: trust_types::MemorySummary::default(),
        })
    }

    fn one_unknown_primary_function(
        package: &str,
        krate: &str,
        function: &str,
    ) -> trust_types::TransportMessage {
        trust_types::TransportMessage::FunctionResult(trust_types::FunctionTransportResult {
            stable_ids: Vec::new(),
            source_sha256: None,
            expanded_function_identity: None,
            modeled_facts: Vec::new(),
            function: function.to_string(),
            package_name: Some(package.to_string()),
            crate_name: Some(krate.to_string()),
            primary_package: true,
            verification_session: TEST_SESSION.to_string(),
            runtime_checks: None,
            results: vec![transport_row(trust_types::Outcome::Unknown)],
            proved: 0,
            failed: 0,
            unknown: 1,
            timed_out: 0,
            skipped: 0,
            runtime_checked: 0,
            cached: 0,
            total: 1,
            transport_budget: None,
        })
    }

    fn raw_unknown_function(function: &str) -> trust_types::TransportMessage {
        let mut message = one_unknown_primary_function("demo", "demo", function);
        let trust_types::TransportMessage::FunctionResult(result) = &mut message else {
            unreachable!()
        };
        result.package_name = None;
        result.primary_package = false;
        message
    }

    fn raw_exact_coverage(
        eligible_functions: Vec<String>,
        processed_functions: Vec<String>,
    ) -> trust_types::TransportMessage {
        trust_types::TransportMessage::CoverageSummary(trust_types::CoverageTransportSummary {
            crate_name: "demo".to_string(),
            package_name: String::new(),
            primary_package: false,
            verification_session: TEST_SESSION.to_string(),
            eligible: eligible_functions.len(),
            processed: processed_functions.len(),
            noted_stops: Vec::new(),
            degraded_anchors: 0,
            function_identities: Some(trust_types::CoverageFunctionIdentityInventory {
                schema: trust_types::COVERAGE_FUNCTION_IDENTITY_SCHEMA_V1.to_string(),
                eligible_functions,
                processed_functions,
            }),
            memory: trust_types::MemorySummary::default(),
        })
    }

    fn parse_raw_messages(
        messages: impl IntoIterator<Item = trust_types::TransportMessage>,
    ) -> ParsedCompilerOutput {
        let input = messages
            .into_iter()
            .map(|message| {
                format!(
                    "{}{}",
                    trust_types::TRANSPORT_PREFIX,
                    serde_json::to_string(&message).expect("serialize raw transport")
                )
            })
            .collect::<Vec<_>>()
            .join("\n");
        parse_compiler_stderr(Cursor::new(input), false)
    }

    #[allow(clippy::too_many_arguments)]
    fn append_complete_proof_unit(
        lines: &mut Vec<serde_json::Value>,
        package_id: &str,
        package_name: &str,
        target_name: &str,
        target_kind: &str,
        unit_index: u64,
        unit_mode: &str,
        unit_role: &str,
        nonempty: bool,
    ) {
        let krate = target_name.replace('-', "_");
        let primary = unit_role == "primary";
        let mut messages = Vec::new();
        if nonempty {
            messages.push(one_unknown_primary_function(
                package_name,
                &krate,
                &format!("{krate}::f"),
            ));
            messages.push(complete_coverage(package_name, &krate));
            messages.push(one_unknown_primary_summary(package_name, &krate));
        } else {
            messages.push(empty_complete_coverage(package_name, &krate));
            messages.push(empty_primary_summary(package_name, &krate));
        }
        for mut message in messages {
            set_transport_primary(&mut message, primary);
            let mut envelope =
                cargo_transport_envelope_with_kind(package_id, target_name, target_kind, &message);
            set_envelope_proof_unit(&mut envelope, unit_index, unit_mode, unit_role, package_name);
            lines.push(envelope);
        }
        let mut artifact = cargo_artifact_with_kind(package_id, target_name, target_kind, false);
        set_envelope_proof_unit(&mut artifact, unit_index, unit_mode, unit_role, package_name);
        lines.push(artifact);
    }

    fn cargo_input_with_inventory(
        mut lines: Vec<serde_json::Value>,
        include_build_finished: bool,
    ) -> String {
        let original_indices = lines
            .iter()
            .filter_map(|line| line.pointer("/trust_proof_unit/index"))
            .filter_map(serde_json::Value::as_u64)
            .collect::<BTreeSet<_>>();
        let compact_indices = original_indices
            .into_iter()
            .enumerate()
            .map(|(compact, original)| (original, u64::try_from(compact).unwrap()))
            .collect::<BTreeMap<_, _>>();
        for line in &mut lines {
            if let Some(index) = line.pointer_mut("/trust_proof_unit/index") {
                let original = index.as_u64().expect("fixture proof-unit index");
                *index = serde_json::json!(compact_indices[&original]);
            }
        }
        let mut units = BTreeMap::new();
        for line in &lines {
            let Some(proof_unit) = line.get("trust_proof_unit") else {
                continue;
            };
            let index = proof_unit
                .get("index")
                .and_then(serde_json::Value::as_u64)
                .expect("fixture proof-unit index");
            let mode = proof_unit
                .get("mode")
                .and_then(serde_json::Value::as_str)
                .expect("fixture proof-unit mode");
            let semantics = fixture_unit_semantics(mode);
            assert_eq!(
                proof_unit.get("semantics_sha256").and_then(serde_json::Value::as_str),
                Some(fixture_semantics_sha256(&semantics).as_str()),
                "fixture proof identity must bind its semantic descriptor"
            );
            let entry = serde_json::json!({
                "trust_proof_unit": proof_unit,
                "semantics": semantics,
                "package_id": line.get("package_id").expect("fixture package ID"),
                "target_name": line.pointer("/target/name").expect("fixture target name"),
                "target_kinds": line.pointer("/target/kind").expect("fixture target kinds"),
                "compile_target": line.get("trust_compile_target").expect("fixture compile target"),
                "trust_compile_mode": line.get("trust_compile_mode").expect("fixture compile mode"),
                "trust_compile_kind": line.get("trust_compile_kind").expect("fixture compile kind"),
                "trust_unit_identity_sha256": line.get("trust_unit_identity_sha256").expect("fixture unit identity"),
                "compile_target_spec_sha256": line.get("trust_compile_target_spec_sha256"),
            });
            if let Some(previous) = units.insert(index, entry.clone()) {
                assert_eq!(previous, entry, "fixture unit identity changed");
            }
        }
        let include_dependencies = units.values().any(|unit| {
            unit.pointer("/trust_proof_unit/role").and_then(serde_json::Value::as_str)
                == Some("dependency")
        });
        let inventory = serde_json::json!({
            "reason": "trust-proof-inventory",
            "schema": TARGO_TRUST_PROOF_INVENTORY_SCHEMA_V2,
            "include_dependencies": include_dependencies,
            "units": units.into_values().collect::<Vec<_>>(),
            "excluded_units": [],
        });
        lines.insert(0, inventory);
        if include_build_finished {
            lines.push(serde_json::json!({"reason": "build-finished", "success": true}));
        }
        lines.into_iter().map(|line| format!("{line}\n")).collect()
    }

    fn successful_cargo_input(lines: Vec<serde_json::Value>) -> String {
        cargo_input_with_inventory(lines, true)
    }

    fn native_resource_fixture() -> (BTreeMap<String, String>, Vec<serde_json::Value>) {
        use trust_types::native_admission::*;
        let package = "path+file:///fixture#demo@0.1.0";
        let binding = NativeAdmissionBinding {
            run_digest: run_digest(TEST_SESSION),
            unit_digest: TEST_UNIT_IDENTITY_SHA256.into(),
            semantics_digest: fixture_semantics_sha256(&fixture_unit_semantics("test")),
            role: "primary".into(),
            target: TEST_COMPILE_TARGET.into(),
        };
        let body = NativeAdmissionBody { function: "demo::f".into(), body_digest: "c".repeat(64) };
        let census = NativeAdmissionCensus {
            transport_type: None,
            schema: SCHEMA.into(),
            package_name: "demo".into(),
            crate_name: "demo".into(),
            bodies: vec![body.clone()],
            auxiliary_bodies: vec![],
            attempts: vec![NativeAdmissionAttempt {
                work_digest: work_digest(&binding, &body),
                request_digest: body.body_digest.clone(),
                body,
                attempt: 1,
                outcome: NativeAdmissionOutcome::CacheReuse,
                terminal: true,
            }],
            binding,
            complete: true,
            problems: vec![],
        };
        let messages = [
            one_unknown_primary_function("demo", "demo", "demo::f"),
            trust_types::TransportMessage::NativeAdmissionCensus(census),
            complete_coverage("demo", "demo"),
            one_unknown_primary_summary("demo", "demo"),
        ];
        let mut lines: Vec<_> =
            messages.iter().map(|m| cargo_transport_envelope(package, "demo", m)).collect();
        lines.push(cargo_artifact_with_kind(package, "demo", "lib", false));
        ([(package.into(), "demo".into())].into_iter().collect(), lines)
    }

    #[test]
    fn native_census_joins_the_full_cargo_unit_without_changing_proof_rows() {
        let (selected, lines) = native_resource_fixture();
        let evidence = parse_cargo_json_stdout(
            Cursor::new(successful_cargo_input(lines)),
            &selected,
            TEST_SESSION,
            true,
        )
        .unwrap();
        assert_eq!(evidence.parsed.native_admission_observations.len(), 1);
        assert!(evidence.parsed.native_admission_problems.is_empty());
        assert_eq!(evidence.parsed.verification_results.len(), 1);
    }

    /// One unit's island rows: `rows` are `(name, status, stop, basis)`, keyed
    /// `<krate>::<name>#<16 hex>`.
    fn island_rows_message(
        package: &str,
        krate: &str,
        phase: trust_types::clean_island_rows::CleanIslandPhase,
        complete: bool,
        rows: &[(&str, &str, &str, Option<&str>)],
    ) -> trust_types::TransportMessage {
        let mut rows: Vec<trust_types::clean_island_rows::CleanIslandRow> = rows
            .iter()
            .enumerate()
            .map(|(index, (name, status, stop, basis))| {
                trust_types::clean_island_rows::CleanIslandRow {
                    key: format!("{krate}::{name}#{:016x}", index + 1),
                    kind: "lean:theorem".to_string(),
                    status: (*status).to_string(),
                    stop: (*stop).to_string(),
                    basis: basis.map(str::to_string),
                    file: "src/lib.rs".to_string(),
                    line: u32::try_from(10 + index).unwrap(),
                    col: 5,
                    source: Some(format!("{:064x}", index + 1)),
                }
            })
            .collect();
        rows.sort();
        trust_types::TransportMessage::CleanIslandRows(
            trust_types::clean_island_rows::CleanIslandRowsTransport {
                schema: trust_types::clean_island_rows::CLEAN_ISLAND_ROWS_SCHEMA_V1.to_string(),
                crate_name: krate.to_string(),
                package_name: package.to_string(),
                verification_session: TEST_SESSION.to_string(),
                primary_package: true,
                phase,
                islands: 1,
                complete,
                problems: if complete {
                    Vec::new()
                } else {
                    vec!["island 1 was not enumerated".to_string()]
                },
                rows,
            },
        )
    }

    const PROVED: (&str, &str, Option<&str>) = ("proved", "solved", None);

    /// A successful unit of `demo` whose island rows precede its coverage.
    fn island_unit_lines(
        island_rows: Option<trust_types::TransportMessage>,
    ) -> (BTreeMap<String, String>, Vec<serde_json::Value>) {
        let package = "path+file:///fixture#demo@0.1.0";
        let mut messages = vec![one_unknown_primary_function("demo", "demo", "demo::f")];
        messages.extend(island_rows);
        messages.push(complete_coverage("demo", "demo"));
        messages.push(one_unknown_primary_summary("demo", "demo"));
        let mut lines: Vec<_> =
            messages.iter().map(|m| cargo_transport_envelope(package, "demo", m)).collect();
        lines.push(cargo_artifact_with_kind(package, "demo", "lib", false));
        ([(package.into(), "demo".into())].into_iter().collect(), lines)
    }

    fn two_island_rows() -> trust_types::TransportMessage {
        let (status, stop, basis) = PROVED;
        island_rows_message(
            "demo",
            "demo",
            trust_types::clean_island_rows::CleanIslandPhase::Verified,
            true,
            &[("Demo.t", status, stop, basis), ("Demo.u", status, stop, basis)],
        )
    }

    #[test]
    fn island_rows_are_admitted_before_coverage_and_are_never_a_proof_row() {
        let (selected, without) = island_unit_lines(None);
        let baseline = parse_cargo_json_stdout(
            Cursor::new(successful_cargo_input(without)),
            &selected,
            TEST_SESSION,
            true,
        )
        .unwrap();
        let (selected, lines) = island_unit_lines(Some(two_island_rows()));
        let evidence = parse_cargo_json_stdout(
            Cursor::new(successful_cargo_input(lines)),
            &selected,
            TEST_SESSION,
            true,
        )
        .unwrap();
        let [(target, rows)] = evidence.clean_island_rows.iter().collect::<Vec<_>>()[..] else {
            panic!("{:?}", evidence.clean_island_rows)
        };
        assert_eq!(target.crate_name(), "demo");
        assert_eq!(rows.rows.len(), 2);
        // The proof rows, counts and coverage are exactly the run's without them.
        assert_eq!(
            serde_json::to_value(&evidence.parsed.verification_results).unwrap(),
            serde_json::to_value(&baseline.parsed.verification_results).unwrap(),
        );
        assert_eq!(evidence.parsed.coverage_rows.len(), baseline.parsed.coverage_rows.len());
        assert_eq!(
            evidence.parsed.completed_proof_targets,
            baseline.parsed.completed_proof_targets
        );
    }

    #[test]
    fn island_rows_out_of_place_twice_or_of_another_scope_fail_the_run() {
        let refused = |lines: Vec<serde_json::Value>, selected: &BTreeMap<String, String>| {
            parse_cargo_json_stdout(
                Cursor::new(successful_cargo_input(lines)),
                selected,
                TEST_SESSION,
                true,
            )
            .err()
            .expect("refused")
        };
        let package = "path+file:///fixture#demo@0.1.0";
        let (selected, mut lines) = island_unit_lines(Some(two_island_rows()));
        // After the unit's coverage summary.
        let mut after = lines.clone();
        after.swap(1, 2);
        let error = refused(after, &selected);
        assert!(error.contains("island rows after its coverage summary"), "{error}");
        // Twice.
        let mut twice = lines.clone();
        twice.insert(1, lines[1].clone());
        let error = refused(twice, &selected);
        assert!(error.contains("island rows twice"), "{error}");
        // Another session, another crate.
        let trust_types::TransportMessage::CleanIslandRows(mut other) = two_island_rows() else {
            unreachable!()
        };
        other.verification_session = "another-session".to_string();
        lines[1] = cargo_transport_envelope(
            package,
            "demo",
            &trust_types::TransportMessage::CleanIslandRows(other.clone()),
        );
        let error = refused(lines.clone(), &selected);
        assert!(error.contains("scope/session does not match"), "{error}");
        other.verification_session = TEST_SESSION.to_string();
        other.crate_name = "other".to_string();
        for row in &mut other.rows {
            row.key = row.key.replacen("demo::", "other::", 1);
        }
        lines[1] = cargo_transport_envelope(
            package,
            "demo",
            &trust_types::TransportMessage::CleanIslandRows(other),
        );
        let error = refused(lines.clone(), &selected);
        assert!(error.contains("scope/session does not match"), "{error}");
        // A proved row in a payload that is not verified and complete.
        let (status, stop, basis) = PROVED;
        lines[1] = cargo_transport_envelope(
            package,
            "demo",
            &island_rows_message(
                "demo",
                "demo",
                trust_types::clean_island_rows::CleanIslandPhase::FrontEndError,
                true,
                &[("Demo.t", status, stop, basis)],
            ),
        );
        let error = refused(lines, &selected);
        assert!(error.contains("invalid island rows"), "{error}");
        assert!(error.contains("is proved in a payload that is front-end-error"), "{error}");
    }

    #[test]
    fn island_rows_of_a_unit_stopped_by_a_front_end_error_are_admitted_without_coverage() {
        let package = "path+file:///fixture#demo@0.1.0";
        let selected: BTreeMap<String, String> =
            [(package.into(), "demo".into())].into_iter().collect();
        let rows = island_rows_message(
            "demo",
            "demo",
            trust_types::clean_island_rows::CleanIslandPhase::FrontEndError,
            true,
            &[
                ("Demo.t", "failed", "solver-incomplete", Some("unproved_fail_closed")),
                ("Demo.u", "unknown", "not-dispatched", None),
            ],
        );
        let lines = vec![cargo_transport_envelope(package, "demo", &rows)];
        let mut stream = cargo_input_with_inventory(lines, false);
        stream.push_str("{\"reason\":\"build-finished\",\"success\":false}\n");
        let evidence =
            parse_cargo_json_stdout(Cursor::new(stream), &selected, TEST_SESSION, true).unwrap();
        assert_eq!(evidence.build_succeeded, Some(false));
        assert_eq!(evidence.clean_island_rows.len(), 1);
        assert!(evidence.parsed.coverage_rows.is_empty());
        assert!(evidence.parsed.verification_results.is_empty());
    }

    /// The frontend end to end over recorded island-row payloads, as the
    /// compiler emitter will publish them: Cargo's stream through
    /// `parse_cargo_json_stdout`, the records of the run, their snapshot and
    /// the changed-only view. The emitter itself is not here (it needs a
    /// stage-1 compiler); its payload's shape is the transport's.
    #[test]
    fn recorded_island_payloads_reach_the_record_and_the_changed_only_view() {
        use trust_types::clean_island_rows::CleanIslandPhase;
        let package = "path+file:///fixture#demo@0.1.0";
        let refused = ("failed", "solver-incomplete", Some("unproved_fail_closed"));
        let unchecked: (&str, &str, Option<&str>) = ("unknown", "not-dispatched", None);
        let rows_of = |phase: CleanIslandPhase, t: (&str, &str, Option<&str>)| {
            island_rows_message(
                "demo",
                "demo",
                phase,
                true,
                &[
                    ("Demo.t", t.0, t.1, t.2),
                    (
                        "Demo.u",
                        if phase == CleanIslandPhase::Verified { "proved" } else { unchecked.0 },
                        if phase == CleanIslandPhase::Verified { "solved" } else { unchecked.1 },
                        None,
                    ),
                ],
            )
        };
        let record = |message: trust_types::TransportMessage, built: bool| {
            let (selected, lines) = island_unit_lines(Some(message.clone()));
            let evidence = if built {
                parse_cargo_json_stdout(
                    Cursor::new(successful_cargo_input(lines)),
                    &selected,
                    TEST_SESSION,
                    true,
                )
                .unwrap()
            } else {
                let lines = vec![cargo_transport_envelope(package, "demo", &message)];
                let mut stream = cargo_input_with_inventory(lines, false);
                stream.push_str("{\"reason\":\"build-finished\",\"success\":false}\n");
                parse_cargo_json_stdout(Cursor::new(stream), &selected, TEST_SESSION, true).unwrap()
            };
            let records = crate::obligations::ObligationRecords::of_rows(
                &[],
                &crate::obligations::FunctionInventory::default(),
                crate::obligations::RunFacts {
                    lane: "strict".to_string(),
                    policy: "strict".to_string(),
                    selection: "default".to_string(),
                    targo_trust_commit: "0".repeat(40),
                    profile: "a".repeat(64),
                    worker_threads: 0,
                    outcome: trust_types::determinism::UnitOutcome::Measured,
                    vector: "b".repeat(64),
                    coverage_complete: built,
                    degraded_anchors: 0,
                },
                crate::obligations::RunScope {
                    selected: ["demo".to_string()].into_iter().collect(),
                    resolved: BTreeSet::new(),
                },
                &crate::package_record::RunCoverage {
                    rows: &evidence.parsed.coverage_rows,
                    missing: BTreeSet::new(),
                    publication_stops: &[],
                    compile_errors: &evidence.compile_errors,
                },
            )
            .with_clean_islands(
                evidence
                    .declared_inventory
                    .as_ref()
                    .map(|inventory| {
                        inventory
                            .proof_targets
                            .iter()
                            .map(|target| target.package_name.as_str())
                            .collect::<Vec<_>>()
                    })
                    .as_deref(),
                evidence
                    .clean_island_rows
                    .iter()
                    .map(|(target, rows)| (target.package_name.as_str(), rows)),
            );
            vec![("demo".to_string(), records.package_ndjson("demo").unwrap())]
        };
        let target = tempfile::tempdir().unwrap();
        let request = crate::agent_delta::DeltaRequest::default();
        let publish = |records: &[(String, String)]| {
            crate::agent_delta::publish_shown(target.path(), records, &request, Some("me"), false)
                .lines()
        };
        let proved = rows_of(CleanIslandPhase::Verified, PROVED);
        // First run: no base, both rows proved, so only the summary line.
        let first = publish(&record(proved.clone(), true));
        assert_eq!(first.len(), 1, "{first:#?}");
        assert!(first[0].contains("; 2 island declaration(s)  (now "), "{first:#?}");
        // A rerun with no edit: one line.
        let again = publish(&record(proved.clone(), true));
        assert_eq!(again.len(), 1, "{again:#?}");
        assert!(again[0].contains("; 0 of 2 island declaration(s) changed"), "{again:#?}");
        // A broken proof under a front-end error: the refused row and one
        // count line, never every island row.
        let broken = publish(&record(rows_of(CleanIslandPhase::FrontEndError, refused), false));
        // The build failed, so the package's own header facts moved too: its
        // `RUN` lines are the obligations' view, unchanged by islands.
        let broken: Vec<&String> = broken.iter().filter(|line| !line.starts_with("RUN ")).collect();
        assert_eq!(broken.len(), 3, "{broken:#?}");
        assert!(
            broken[0].starts_with(
                "LOST        [FAILED: unproved, no counterexample; failed closed]  demo::Demo.t#"
            ),
            "{broken:#?}"
        );
        assert!(
            broken[1].starts_with("NOT CHECKED  1 island declaration(s) of `demo` not checked"),
            "{broken:#?}"
        );
        assert!(broken[2].contains("; 1 of 2 island declaration(s) changed"), "{broken:#?}");
        // Fixed: compared with the last run that measured the islands.
        let fixed = publish(&record(proved, true));
        assert_eq!(fixed.len(), 1, "{fixed:#?}");
        assert!(fixed[0].contains("; 0 of 2 island declaration(s) changed"), "{fixed:#?}");
    }

    #[test]
    fn well_formed_native_root_mismatch_is_incomplete_without_changing_proof_rows() {
        let (selected, mut lines) = native_resource_fixture();
        let baseline = parse_cargo_json_stdout(
            Cursor::new(successful_cargo_input(lines.clone())),
            &selected,
            TEST_SESSION,
            true,
        )
        .unwrap();
        assert_eq!(baseline.parsed.verification_results.len(), 1);
        assert!(baseline.parsed.native_admission_problems.is_empty());

        let payload = lines[1]["message"]["message"].as_str().unwrap();
        let trust_types::TransportMessage::NativeAdmissionCensus(mut census) =
            trust_types::parse_transport_payload(
                payload.strip_prefix(trust_types::TRANSPORT_PREFIX).unwrap(),
            )
            .unwrap()
        else {
            unreachable!()
        };
        // Keep the census internally consistent and its run/unit binding intact.
        // Only the claimed root population differs from the authenticated proof
        // coverage, which still names demo::f.
        census.bodies[0].function = "demo::other".into();
        census.attempts[0].body = census.bodies[0].clone();
        census.attempts[0].work_digest = trust_types::native_admission::request_work_digest(
            &census.binding,
            &census.attempts[0].body,
            &census.attempts[0].request_digest,
        );
        census.validate().unwrap();
        lines[1] = cargo_transport_envelope(
            selected.keys().next().unwrap(),
            "demo",
            &trust_types::TransportMessage::NativeAdmissionCensus(census),
        );
        let evidence = parse_cargo_json_stdout(
            Cursor::new(successful_cargo_input(lines)),
            &selected,
            TEST_SESSION,
            true,
        )
        .unwrap();
        assert_eq!(evidence.parsed.native_admission_observations.len(), 1);
        assert_eq!(evidence.parsed.native_admission_problems.len(), 1);
        assert!(
            evidence.parsed.native_admission_problems[0]
                .contains("native admission body inventory differs from coverage")
        );
        assert_eq!(
            serde_json::to_value(&evidence.parsed.verification_results).unwrap(),
            serde_json::to_value(&baseline.parsed.verification_results).unwrap(),
            "resource population mismatch must not change proof rows"
        );
        let resources = crate::compiler_admission::Report::new(
            &evidence.declared_inventory.as_ref().unwrap().proof_targets,
            &evidence.compiled_targets,
            evidence.parsed.native_admission_observations,
            evidence.parsed.native_admission_problems,
        );
        assert_eq!(serde_json::to_value(resources).unwrap()["availability"], "incomplete");
    }

    #[test]
    fn empty_native_unit_can_close_before_its_first_proof_message() {
        let (selected, mut lines) = native_resource_fixture();
        let package = selected.keys().next().unwrap();
        let payload = lines[1]["message"]["message"].as_str().unwrap();
        let trust_types::TransportMessage::NativeAdmissionCensus(mut census) =
            trust_types::parse_transport_payload(
                payload.strip_prefix(trust_types::TRANSPORT_PREFIX).unwrap(),
            )
            .unwrap()
        else {
            unreachable!()
        };
        census.bodies.clear();
        census.attempts.clear();
        // An empty library may accompany a nonempty selected root, but an
        // executable test harness must independently cover a body.
        census.binding.semantics_digest =
            fixture_semantics_sha256(&fixture_unit_semantics("build"));
        lines[1] = cargo_transport_envelope(
            package,
            "demo",
            &trust_types::TransportMessage::NativeAdmissionCensus(census),
        );
        lines[2] =
            cargo_transport_envelope(package, "demo", &empty_complete_coverage("demo", "demo"));
        lines[3] =
            cargo_transport_envelope(package, "demo", &empty_primary_summary("demo", "demo"));
        lines.remove(0);
        for line in &mut lines {
            set_envelope_proof_unit(line, 0, "build", "primary", "demo");
        }
        let error = parse_cargo_json_stdout(
            Cursor::new(successful_cargo_input(lines.clone())),
            &selected,
            TEST_SESSION,
            true,
        )
        .err()
        .expect("an empty library alone cannot satisfy selected-package coverage");
        assert!(error.contains("zero coverage-eligible bodies across every primary"), "{error}");

        let companion_start = lines.len();
        append_complete_proof_unit(
            &mut lines,
            package,
            "demo",
            "companion",
            "bin",
            1,
            "build",
            "primary",
            true,
        );
        let companion_digest = "d".repeat(64);
        assert_ne!(companion_digest, TEST_UNIT_IDENTITY_SHA256);
        for line in &mut lines[companion_start..] {
            line["trust_unit_identity_sha256"] = serde_json::json!(companion_digest);
        }
        let evidence = parse_cargo_json_stdout(
            Cursor::new(successful_cargo_input(lines)),
            &selected,
            TEST_SESSION,
            true,
        )
        .unwrap();
        assert_eq!(evidence.parsed.native_admission_observations.len(), 1);
        assert!(evidence.parsed.native_admission_problems.is_empty());
        let empty = &evidence.parsed.native_admission_observations[0];
        assert_eq!(empty.cargo_target.target_name, "demo");
        assert_eq!(empty.cargo_target.proof_unit_index, 0);
        assert_eq!(empty.cargo_target.proof_unit_mode, "build");
        assert!(empty.census.bodies.is_empty());
        assert!(empty.census.auxiliary_bodies.is_empty());
        assert!(empty.census.attempts.is_empty());
        assert_eq!(evidence.parsed.verification_results.len(), 1);
        assert!(
            evidence.parsed.verification_results[0].function.ends_with("::companion::f"),
            "only the nonempty companion contributes a proof row: {:?}",
            evidence.parsed.verification_results
        );
    }

    #[test]
    fn native_resource_defects_only_withhold_resource_completeness() {
        for variant in 0..5 {
            let (selected, mut lines) = native_resource_fixture();
            match variant {
                0 => {
                    lines.insert(2, lines[1].clone());
                }
                1 => {
                    lines.swap(1, 2);
                } // census after coverage
                2 => {
                    lines.remove(1);
                } // missing census
                3 | 4 => {
                    let payload = lines[1]["message"]["message"].as_str().unwrap();
                    let mut value: serde_json::Value = serde_json::from_str(
                        payload.strip_prefix(trust_types::TRANSPORT_PREFIX).unwrap(),
                    )
                    .unwrap();
                    value["binding"][if variant == 3 { "unit_digest" } else { "run_digest" }] =
                        serde_json::json!("0".repeat(64));
                    lines[1]["message"]["message"] =
                        serde_json::json!(format!("{}{}", trust_types::TRANSPORT_PREFIX, value));
                }
                _ => unreachable!(),
            }
            let evidence = parse_cargo_json_stdout(
                Cursor::new(successful_cargo_input(lines)),
                &selected,
                TEST_SESSION,
                true,
            )
            .unwrap();
            let resources = crate::compiler_admission::Report::new(
                &evidence.declared_inventory.as_ref().unwrap().proof_targets,
                &evidence.compiled_targets,
                evidence.parsed.native_admission_observations,
                evidence.parsed.native_admission_problems,
            );
            let value = serde_json::to_value(resources).unwrap();
            assert_eq!(value["availability"], "incomplete", "variant {variant}");
            assert_eq!(
                evidence.parsed.verification_results.len(),
                1,
                "resource errors cannot rewrite proof rows"
            );
        }
    }

    #[test]
    fn absent_cargo_terminal_boundary_withholds_native_resource_completeness() {
        let (selected, lines) = native_resource_fixture();
        let evidence = parse_cargo_json_stdout(
            Cursor::new(cargo_input_with_inventory(lines, false)),
            &selected,
            TEST_SESSION,
            true,
        )
        .unwrap();
        assert!(!evidence.parsed.native_admission_problems.is_empty());
    }

    #[test]
    fn native_bytes_do_not_spend_the_unchanged_proof_transport_budget() {
        let (selected, lines) = native_resource_fixture();
        let proof_bytes = lines
            .iter()
            .filter_map(|line| line.pointer("/message/message")?.as_str())
            .filter(|text| {
                !is_native_admission_payload(
                    text.strip_prefix(trust_types::TRANSPORT_PREFIX).unwrap(),
                )
            })
            .map(str::len)
            .sum();
        let input = successful_cargo_input(lines);
        let evidence = parse_cargo_json_stdout_impl(CargoJsonParseInput {
            reader: Cursor::new(input),
            selected_packages: &selected,
            expected_session: TEST_SESSION,
            require_authenticated_coverage: true,
            retain_authenticated_messages: false,
            allow_post_build_test_output: false,
            require_prepared_tests: false,
            max_line_bytes: MAX_CARGO_JSON_LINE_BYTES,
            max_authenticated_transport_bytes: proof_bytes,
        })
        .unwrap();
        assert!(evidence.parsed.native_admission_problems.is_empty());
        assert_eq!(evidence.parsed.verification_results.len(), 1);
        let mut resource_bytes = 0;
        assert!(charge_native_admission_bytes(&mut resource_bytes, 10, 10).is_ok());
        assert!(charge_native_admission_bytes(&mut resource_bytes, 1, 10).is_err());
    }

    #[test]
    fn truncated_inner_resource_is_incomplete_but_outer_framing_stays_strict() {
        let (selected, mut lines) = native_resource_fixture();
        let mut text = lines[1]["message"]["message"].as_str().unwrap().to_string();
        text.pop();
        lines[1]["message"]["message"] = serde_json::json!(text);
        let input = successful_cargo_input(lines);
        let evidence =
            parse_cargo_json_stdout(Cursor::new(&input), &selected, TEST_SESSION, true).unwrap();
        assert!(!evidence.parsed.native_admission_problems.is_empty());
        assert_eq!(evidence.parsed.verification_results.len(), 1);
        // An unparseable outer Cargo frame has no safely recoverable boundary.
        // It is a transport failure; no unchanged-proof claim is made for it.
        assert!(
            parse_cargo_json_stdout(
                Cursor::new(&input[..input.len() / 2]),
                &selected,
                TEST_SESSION,
                true
            )
            .is_err()
        );
    }

    #[test]
    fn nonleading_duplicate_native_tags_are_resource_defects_not_proof_failures() {
        for duplicate in ["native_admission_census", "crate_summary"] {
            let (selected, mut lines) = native_resource_fixture();
            let original = lines[1]["message"]["message"].as_str().unwrap();
            let json = original.strip_prefix(trust_types::TRANSPORT_PREFIX).unwrap();
            let prefix = format!(
                r#"{{"type":"native_admission_census","schema":"{}","#,
                trust_types::native_admission::SCHEMA
            );
            let rest = json.strip_prefix(&prefix).unwrap();
            // Keep every original field. Adding a leading field makes the native
            // tag non-leading, and duplicate tags must reach the typed rejection.
            let malformed = format!(
                r#"{{"schema":"{}","type":"native_admission_census","type":"{}",{}"#,
                trust_types::native_admission::SCHEMA,
                duplicate,
                rest
            );
            assert!(is_native_admission_payload(&malformed));
            lines[1]["message"]["message"] =
                serde_json::json!(format!("{}{}", trust_types::TRANSPORT_PREFIX, malformed));
            let evidence = parse_cargo_json_stdout(
                Cursor::new(successful_cargo_input(lines)),
                &selected,
                TEST_SESSION,
                true,
            )
            .unwrap();
            assert!(evidence.parsed.native_admission_observations.is_empty());
            assert!(!evidence.parsed.native_admission_problems.is_empty());
            assert_eq!(evidence.parsed.verification_results.len(), 1);
        }
    }

    #[test]
    fn cargo_semantic_descriptor_digest_and_canonical_sets_fail_closed() {
        let semantics = fixture_unit_semantics("build");
        let claimed_sha256 = fixture_semantics_sha256(&semantics);
        let mut drifted = serde_json::to_value(&semantics).unwrap();
        drifted["profile"]["overflow_checks"] = serde_json::json!(true);
        let error = parse_cargo_unit_semantics(Some(&drifted), &claimed_sha256, "fixture")
            .expect_err("semantic profile drift must invalidate the Cargo-owned digest");
        assert!(error.contains("did not match its Cargo-owned SHA-256"), "{error}");

        for features in [vec!["z".to_string(), "a".to_string()], vec!["a".to_string(); 2]] {
            let mut noncanonical = semantics.clone();
            noncanonical.features = features;
            let digest = fixture_semantics_sha256(&noncanonical);
            let value = serde_json::to_value(noncanonical).unwrap();
            let error = parse_cargo_unit_semantics(Some(&value), &digest, "fixture")
                .expect_err("semantic sets must be strictly sorted and duplicate-free");
            assert!(error.contains("not strictly sorted and duplicate-free"), "{error}");
        }

        let mut extended = serde_json::to_value(&semantics).unwrap();
        extended["compiler"]["unwired_future_field"] = serde_json::json!(true);
        let error = parse_cargo_unit_semantics(Some(&extended), &claimed_sha256, "fixture")
            .expect_err("unknown semantic fields must not silently escape the digest schema");
        assert!(error.contains("unknown field"), "{error}");
    }

    #[test]
    fn cargo_unit_configuration_rejects_every_closed_enum_escape() {
        let mut cases = Vec::new();
        macro_rules! invalid_case {
            ($label:literal, $mutation:expr) => {{
                let mut semantics = fixture_unit_semantics("build");
                $mutation(&mut semantics);
                cases.push(($label, semantics));
            }};
        }
        invalid_case!("crate type", |value: &mut trust_types::CargoUnitSemanticsReport| {
            value.target_crate_types = vec!["future-crate".to_string()]
        });
        invalid_case!("edition", |value: &mut trust_types::CargoUnitSemanticsReport| {
            value.target_edition = "future".to_string()
        });
        invalid_case!("frontend", |value: &mut trust_types::CargoUnitSemanticsReport| {
            value.compiler.frontend = "future".to_string()
        });
        invalid_case!("effective backend", |value: &mut trust_types::CargoUnitSemanticsReport| {
            value.compiler.codegen_backend = "future".to_string()
        });
        invalid_case!("opt level", |value: &mut trust_types::CargoUnitSemanticsReport| {
            value.profile.opt_level = "4".to_string()
        });
        invalid_case!("requested LTO", |value: &mut trust_types::CargoUnitSemanticsReport| {
            value.profile.requested_lto = "future".to_string()
        });
        invalid_case!("effective LTO", |value: &mut trust_types::CargoUnitSemanticsReport| {
            value.profile.effective_lto = "future".to_string()
        });
        invalid_case!("debuginfo", |value: &mut trust_types::CargoUnitSemanticsReport| {
            value.profile.debuginfo = "3".to_string()
        });
        invalid_case!("split debuginfo", |value: &mut trust_types::CargoUnitSemanticsReport| {
            value.profile.split_debuginfo = Some("future".to_string())
        });
        invalid_case!("panic", |value: &mut trust_types::CargoUnitSemanticsReport| {
            value.profile.panic = "future".to_string()
        });
        invalid_case!("strip", |value: &mut trust_types::CargoUnitSemanticsReport| {
            value.profile.strip = "future".to_string()
        });
        invalid_case!("profile backend", |value: &mut trust_types::CargoUnitSemanticsReport| {
            value.profile.codegen_backend = Some("future".to_string())
        });
        invalid_case!("codegen units", |value: &mut trust_types::CargoUnitSemanticsReport| {
            value.profile.codegen_units = Some(0)
        });
        invalid_case!("trim paths", |value: &mut trust_types::CargoUnitSemanticsReport| {
            value.profile.trim_paths = Some("object,object".to_string())
        });

        for (label, semantics) in cases {
            assert!(
                validate_cargo_unit_semantics(&semantics, "fixture").is_err(),
                "{label} escaped its closed Cargo-resolved Unit configuration domain"
            );
        }
    }

    #[test]
    fn live_cargo_proof_authority_rejects_v1_schemas() {
        let selected = BTreeMap::new();
        let inventory = serde_json::json!({
            "schema": "targo.trust-proof-inventory.v1",
        });
        let error = parse_cargo_proof_inventory(&inventory, &selected)
            .expect_err("legacy proof inventory must remain observational only");
        assert!(error.contains("unsupported schema"), "{error}");

        let package_id = "path+file:///fixture#demo@0.1.0";
        let mut envelope = cargo_artifact(package_id, "demo", false);
        envelope["trust_proof_unit"]["schema"] = serde_json::json!("targo.trust-proof-unit.v1");
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let error = cargo_target_identity(&envelope, package_id, &selected)
            .expect_err("legacy proof identity must not authenticate a live compiler envelope");
        assert!(error.contains("unsupported schema"), "{error}");
    }

    #[test]
    fn cargo_inventory_semantics_bind_digest_envelopes_features_and_profile() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let fixture_values = || {
            let mut lines = Vec::new();
            append_complete_proof_unit(
                &mut lines, package_id, "demo", "demo", "lib", 0, "build", "primary", true,
            );
            successful_cargo_input(lines)
                .lines()
                .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
                .collect::<Vec<_>>()
        };
        let render = |values: &[serde_json::Value]| {
            values.iter().map(|line| format!("{line}\n")).collect::<String>()
        };

        let mut values = fixture_values();
        values[0]["units"][0]["semantics"]["profile"]["overflow_checks"] = serde_json::json!(true);
        let error =
            parse_cargo_json_stdout(Cursor::new(render(&values)), &selected, TEST_SESSION, true)
                .err()
                .expect("inventory descriptor drift must invalidate its digest");
        assert!(error.contains("did not match its Cargo-owned SHA-256"), "{error}");

        let mut values = fixture_values();
        let message = values
            .iter_mut()
            .find(|line| {
                line.get("reason").and_then(serde_json::Value::as_str) == Some("compiler-message")
            })
            .expect("fixture compiler message");
        message["trust_proof_unit"]["semantics_sha256"] = serde_json::json!("c".repeat(64));
        let error =
            parse_cargo_json_stdout(Cursor::new(render(&values)), &selected, TEST_SESSION, true)
                .err()
                .expect("compiler envelopes must repeat the inventory semantic digest");
        assert!(error.contains("declared proof inventory"), "{error}");

        let mut values = fixture_values();
        let artifact = values
            .iter_mut()
            .find(|line| {
                line.get("reason").and_then(serde_json::Value::as_str) == Some("compiler-artifact")
            })
            .expect("fixture compiler artifact");
        artifact["features"] = serde_json::json!(["forged-feature"]);
        let error =
            parse_cargo_json_stdout(Cursor::new(render(&values)), &selected, TEST_SESSION, true)
                .err()
                .expect("artifact feature set must match the declared descriptor");
        assert!(error.contains("enabled features did not exactly match"), "{error}");

        let mut values = fixture_values();
        let artifact = values
            .iter_mut()
            .find(|line| {
                line.get("reason").and_then(serde_json::Value::as_str) == Some("compiler-artifact")
            })
            .expect("fixture compiler artifact");
        artifact["profile"]["overflow_checks"] = serde_json::json!(true);
        let error =
            parse_cargo_json_stdout(Cursor::new(render(&values)), &selected, TEST_SESSION, true)
                .err()
                .expect("artifact profile must match the declared descriptor");
        assert!(error.contains("profile field \"overflow_checks\""), "{error}");
    }

    #[test]
    fn cargo_json_parser_caps_escaped_wire_line_before_serde() {
        let input = format!("{{\"reason\":\"{}\"}}\n", "\\u0061".repeat(16));
        let error = match parse_cargo_json_stdout_impl(CargoJsonParseInput {
            reader: Cursor::new(input),
            selected_packages: &BTreeMap::new(),
            expected_session: TEST_SESSION,
            require_authenticated_coverage: true,
            retain_authenticated_messages: false,
            allow_post_build_test_output: false,
            require_prepared_tests: false,
            max_line_bytes: 32,
            max_authenticated_transport_bytes: 1024,
        }) {
            Ok(_) => panic!("raw escaped Cargo JSON must be capped before deserialization"),
            Err(error) => error,
        };

        assert!(error.contains("line 1"), "{error}");
        assert!(error.contains("32-byte safety limit"), "{error}");
    }

    #[test]
    fn cargo_json_parser_caps_aggregate_authenticated_transport() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let envelope = cargo_transport_envelope(
            package_id,
            "demo",
            &one_unknown_primary_function("demo", "demo", "demo::f"),
        );
        let transport_len =
            envelope["message"]["message"].as_str().expect("transport message").len();
        let input = format!("{envelope}\n");
        let error = match parse_cargo_json_stdout_impl(CargoJsonParseInput {
            reader: Cursor::new(input),
            selected_packages: &selected,
            expected_session: TEST_SESSION,
            require_authenticated_coverage: true,
            retain_authenticated_messages: false,
            allow_post_build_test_output: false,
            require_prepared_tests: false,
            max_line_bytes: 1024 * 1024,
            max_authenticated_transport_bytes: transport_len - 1,
        }) {
            Ok(_) => panic!("aggregate authenticated transport must have a finite bound"),
            Err(error) => error,
        };

        assert!(error.contains("aggregate safety limit"), "{error}");
    }

    #[test]
    fn cargo_test_parser_passes_through_only_post_build_output() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let function = cargo_transport_envelope(
            package_id,
            "demo",
            &one_unknown_primary_function("demo", "demo", "demo::f"),
        );
        let coverage =
            cargo_transport_envelope(package_id, "demo", &complete_coverage("demo", "demo"));
        let summary = cargo_transport_envelope(
            package_id,
            "demo",
            &one_unknown_primary_summary("demo", "demo"),
        );
        let artifact = cargo_artifact(package_id, "demo", false);
        let mut input = successful_cargo_input(vec![function, coverage, summary, artifact]);
        input.push_str(
            "running 1 test\n{\"reason\":\"compiler-message\",\"message\":{\"message\":\"TRUST_JSON forged\"}}\n",
        );
        let evidence =
            parse_cargo_json_stdout_for_test(Cursor::new(&input), &selected, TEST_SESSION, true)
                .expect("post-build test stdout is passthrough, not proof transport");
        assert_eq!(evidence.compiled_targets.len(), 1);
        assert_eq!(evidence.parsed.verification_results.len(), 1);

        let error = match parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true)
        {
            Ok(_) => panic!("ordinary check/build parsing must still reject non-JSON stdout"),
            Err(error) => error,
        };
        assert!(error.contains("after its terminal Cargo build-finished boundary"), "{error}");
    }

    #[test]
    fn cargo_transport_requires_tagged_envelope_and_accepts_zero_function_inventory() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let coverage = cargo_transport_envelope(
            package_id,
            "custom-lib",
            &empty_complete_coverage("demo", "custom_lib"),
        );
        let message = cargo_transport_envelope(
            package_id,
            "custom-lib",
            &empty_primary_summary("demo", "custom_lib"),
        );
        let artifact = cargo_artifact(package_id, "custom-lib", false);
        let input = cargo_input_with_inventory(vec![coverage, message, artifact], false);

        let evidence = parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true)
            .expect("parse authenticated Cargo evidence");
        assert_eq!(evidence.compiled_targets.len(), 1);
        assert!(evidence.compiled_targets.iter().any(|target| {
            target.package_id == package_id
                && target.target_name == "custom-lib"
                && target.target_kinds == ["lib"]
                && target.proof_unit_index == 0
        }));
        let parsed = evidence.parsed.require_structured_json_transport(true);
        assert_eq!(parsed.completed_proof_targets, evidence.compiled_targets);
        assert!(parsed.verification_results.is_empty());
    }

    #[test]
    fn cargo_test_aggregates_distinct_cfg_test_and_executed_library_units() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let root_index = 41;
        let execution_index = 42;
        let mut lines = Vec::new();

        for message in [
            one_unknown_primary_function("demo", "demo", "demo::f"),
            complete_coverage("demo", "demo"),
            one_unknown_primary_summary("demo", "demo"),
        ] {
            let mut envelope = cargo_transport_envelope(package_id, "demo", &message);
            set_envelope_proof_unit(&mut envelope, root_index, "test", "primary", "demo");
            lines.push(envelope);
        }
        let mut root_artifact = cargo_artifact(package_id, "demo", false);
        set_envelope_proof_unit(&mut root_artifact, root_index, "test", "primary", "demo");
        lines.push(root_artifact);

        for mut message in [
            one_unknown_primary_function("demo", "demo", "demo::f"),
            complete_coverage("demo", "demo"),
            one_unknown_primary_summary("demo", "demo"),
        ] {
            set_transport_primary(&mut message, false);
            let mut envelope = cargo_transport_envelope(package_id, "demo", &message);
            set_envelope_proof_unit(
                &mut envelope,
                execution_index,
                "build",
                "test-execution",
                "demo",
            );
            lines.push(envelope);
        }
        let mut execution_artifact = cargo_artifact(package_id, "demo", false);
        set_envelope_proof_unit(
            &mut execution_artifact,
            execution_index,
            "build",
            "test-execution",
            "demo",
        );
        lines.push(execution_artifact);

        let input = cargo_input_with_inventory(lines, false);
        let evidence = parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true)
            .expect("both exact Cargo test execution units are authenticated separately");

        assert_eq!(evidence.compiled_targets.len(), 2);
        assert_eq!(evidence.parsed.completed_proof_targets.len(), 2);
        assert_eq!(evidence.parsed.coverage_proof_targets.len(), 2);
        assert!(evidence.compiled_targets.iter().any(|target| {
            target.proof_unit_index == 0
                && target.proof_unit_mode == "test"
                && target.proof_unit_role == "primary"
        }));
        assert!(evidence.compiled_targets.iter().any(|target| {
            target.proof_unit_index == 1
                && target.proof_unit_mode == "build"
                && target.proof_unit_role == "test-execution"
        }));
    }

    #[test]
    fn prepared_plan_receipt_is_confined_to_the_compile_only_boundary() {
        let package = "path+file:///fixture#demo@0.1.0";
        let selected = [(package.to_owned(), "demo".to_owned())].into_iter().collect();
        let mut lines = Vec::new();
        append_complete_proof_unit(
            &mut lines,
            package,
            "demo",
            "integration",
            "test",
            43,
            "test",
            "primary",
            true,
        );
        let artifact = lines.last_mut().unwrap();
        artifact["executable"] = serde_json::json!("/workspace/target/integration");
        artifact["trust_executable_sha256"] = serde_json::json!("a".repeat(64));
        let input = successful_cargo_input(lines);
        let receipt = serde_json::json!({
            "reason": "trust-test-execution-plan", "schema": trust_test_execution::RECEIPT_SCHEMA,
            "session": TEST_SESSION, "path": "/private/prepared-tests.json", "sha256": "b".repeat(64)
        });
        let with_plan = format!("{input}{receipt}\n");
        let parsed = parse_cargo_json_stdout_for_prepared_tests(
            Cursor::new(&with_plan),
            &selected,
            TEST_SESSION,
            true,
        )
        .unwrap();
        assert_eq!(parsed.prepared_tests.unwrap().path, "/private/prepared-tests.json");
        assert!(
            parse_cargo_json_stdout_for_prepared_tests(
                Cursor::new(&input),
                &selected,
                TEST_SESSION,
                true
            )
            .is_err()
        );
        assert!(
            parse_cargo_json_stdout_for_prepared_tests(
                Cursor::new(format!("{with_plan}{receipt}\n")),
                &selected,
                TEST_SESSION,
                true
            )
            .is_err()
        );
        let mut wrong = receipt.clone();
        wrong["session"] = serde_json::json!("another-session");
        assert!(
            parse_cargo_json_stdout_for_prepared_tests(
                Cursor::new(format!("{input}{wrong}\n")),
                &selected,
                TEST_SESSION,
                true
            )
            .is_err()
        );
        let runtime = parse_cargo_json_stdout_for_test(
            Cursor::new(&with_plan),
            &selected,
            TEST_SESSION,
            true,
        )
        .unwrap();
        assert!(
            runtime.prepared_tests.is_none(),
            "runtime stdout must never authorize an execution plan"
        );
    }

    #[test]
    fn cargo_test_artifact_retains_selected_executable_authority() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let mut lines = Vec::new();
        append_complete_proof_unit(
            &mut lines,
            package_id,
            "demo",
            "integration",
            "test",
            43,
            "test",
            "primary",
            true,
        );
        let artifact = lines.last_mut().expect("compiler artifact");
        artifact["executable"] = serde_json::json!("/workspace/target/debug/integration-deadbeef");

        let missing_digest = parse_cargo_json_stdout(
            Cursor::new(successful_cargo_input(lines.clone())),
            &selected,
            TEST_SESSION,
            true,
        )
        .err()
        .expect("selected test artifact needs Targo's in-lifecycle byte identity");
        assert!(missing_digest.contains("executable SHA-256"), "{missing_digest}");

        lines.last_mut().expect("compiler artifact")["trust_executable_sha256"] =
            serde_json::json!("a".repeat(64));
        let evidence = parse_cargo_json_stdout(
            Cursor::new(successful_cargo_input(lines)),
            &selected,
            TEST_SESSION,
            true,
        )
        .expect("parse selected test artifact with complete proof lifecycle");
        let executable = evidence.test_executables.iter().next().expect("test executable");
        assert_eq!(
            executable.path,
            std::path::Path::new("/workspace/target/debug/integration-deadbeef")
        );
        assert_eq!(executable.target.target_name, "integration");
        assert_eq!(executable.target.target_kinds, ["test"]);
        assert_eq!(executable.phase_a_sha256, "a".repeat(64));
    }

    #[test]
    fn cargo_proof_unit_role_must_match_compiler_primary_claim() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();

        let primary_payload = empty_primary_summary("demo", "demo");
        let mut forged_execution = cargo_transport_envelope(package_id, "demo", &primary_payload);
        set_envelope_proof_unit(&mut forged_execution, 7, "build", "test-execution", "demo");
        let error = parse_cargo_json_stdout(
            Cursor::new(format!("{forged_execution}\n")),
            &selected,
            TEST_SESSION,
            true,
        )
        .err()
        .expect("a compiler payload cannot promote itself into an execution subject");
        assert!(error.contains("scope/session does not match"), "{error}");

        let mut non_primary_payload = empty_primary_summary("demo", "demo");
        set_transport_primary(&mut non_primary_payload, false);
        let forged_primary = cargo_transport_envelope(package_id, "demo", &non_primary_payload);
        let error = parse_cargo_json_stdout(
            Cursor::new(format!("{forged_primary}\n")),
            &selected,
            TEST_SESSION,
            true,
        )
        .err()
        .expect("a primary Cargo unit requires the compiler's primary claim");
        assert!(error.contains("scope/session does not match"), "{error}");
    }

    #[test]
    fn cargo_proof_unit_identity_is_exact_and_fail_closed() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();

        let mut message =
            cargo_transport_envelope(package_id, "demo", &empty_primary_summary("demo", "demo"));
        message.as_object_mut().expect("envelope object").remove("trust_proof_unit");
        let error = parse_cargo_json_stdout(
            Cursor::new(format!("{message}\n")),
            &selected,
            TEST_SESSION,
            true,
        )
        .err()
        .expect("TRUST_JSON without a Cargo proof-unit identity is unauthenticated");
        assert!(error.contains("outside Cargo's authenticated proof-subject"), "{error}");

        let mut artifact = cargo_artifact(package_id, "demo", false);
        artifact.as_object_mut().expect("artifact object").remove("trust_proof_unit");
        let evidence = parse_cargo_json_stdout(
            Cursor::new(format!("{artifact}\n")),
            &selected,
            TEST_SESSION,
            true,
        )
        .expect("an ordinary non-proof artifact is ignored");
        assert!(evidence.compiled_targets.is_empty());

        let mut terminal =
            cargo_transport_envelope(package_id, "demo", &empty_primary_summary("demo", "demo"));
        set_envelope_proof_unit(&mut terminal, 9, "test", "primary", "demo");
        let mut coverage =
            cargo_transport_envelope(package_id, "demo", &empty_complete_coverage("demo", "demo"));
        set_envelope_proof_unit(&mut coverage, 9, "test", "primary", "demo");
        let mut conflicting_artifact = cargo_artifact(package_id, "demo", false);
        set_envelope_proof_unit(&mut conflicting_artifact, 9, "build", "test-execution", "demo");
        let error = parse_cargo_json_stdout(
            Cursor::new(format!("{coverage}\n{terminal}\n{conflicting_artifact}\n")),
            &selected,
            TEST_SESSION,
            true,
        )
        .err()
        .expect("one Cargo Unit index cannot change role or mode");
        assert!(error.contains("changed identity"), "{error}");
    }

    #[test]
    fn cargo_test_execution_identity_requires_build_mode_library_or_binary() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let mut payload = empty_primary_summary("demo", "demo");
        set_transport_primary(&mut payload, false);

        for (mode, kind) in [("test", "lib"), ("build", "test")] {
            let mut envelope =
                cargo_transport_envelope_with_kind(package_id, "demo", kind, &payload);
            set_envelope_proof_unit(&mut envelope, 11, mode, "test-execution", "demo");
            let error = parse_cargo_json_stdout(
                Cursor::new(format!("{envelope}\n")),
                &selected,
                TEST_SESSION,
                true,
            )
            .err()
            .expect("invalid test execution subject must fail closed");
            assert!(error.contains("Build-mode library or binary execution target"), "{error}");
        }

        for (index, kind) in [(12, "lib"), (13, "bin")] {
            let mut envelope =
                cargo_transport_envelope_with_kind(package_id, "demo", kind, &payload);
            set_envelope_proof_unit(&mut envelope, index, "build", "test-execution", "demo");
            let evidence = parse_cargo_json_stdout(
                Cursor::new(format!("{envelope}\n")),
                &selected,
                TEST_SESSION,
                false,
            )
            .expect("Build-mode library and binary execution subjects must be admitted");
            assert_eq!(evidence.parsed.completed_proof_targets.len(), 1);
        }
    }

    #[test]
    fn include_dependencies_authenticates_unselected_host_units_separately() {
        let root_id = "path+file:///fixture#demo@0.1.0";
        let dependency_id = "path+file:///fixture#dep@0.1.0";
        let selected = [(root_id.to_string(), "demo".to_string())].into_iter().collect();
        let root_index = 21;
        let dependency_index = 22;
        let mut lines = Vec::new();

        for message in
            [empty_complete_coverage("demo", "demo"), empty_primary_summary("demo", "demo")]
        {
            let mut envelope = cargo_transport_envelope_with_kind_and_compile_target(
                root_id,
                "demo",
                "lib",
                "wasm32-unknown-unknown",
                &message,
            );
            set_envelope_proof_unit(&mut envelope, root_index, "test", "primary", "demo");
            lines.push(envelope);
        }
        let mut root_artifact = cargo_artifact_with_kind_and_compile_target(
            root_id,
            "demo",
            "lib",
            "wasm32-unknown-unknown",
            false,
        );
        set_envelope_proof_unit(&mut root_artifact, root_index, "test", "primary", "demo");
        lines.push(root_artifact);

        let mut dependency_coverage = empty_complete_coverage("dep", "build_script_build");
        let mut dependency_summary = empty_primary_summary("dep", "build_script_build");
        set_transport_primary(&mut dependency_coverage, false);
        set_transport_primary(&mut dependency_summary, false);
        for message in [dependency_coverage, dependency_summary] {
            let mut envelope = cargo_transport_envelope_with_kind(
                dependency_id,
                "build-script-build",
                "custom-build",
                &message,
            );
            set_envelope_proof_unit(&mut envelope, dependency_index, "build", "dependency", "dep");
            lines.push(envelope);
        }
        let mut dependency_artifact =
            cargo_artifact_with_kind(dependency_id, "build-script-build", "custom-build", false);
        set_envelope_proof_unit(
            &mut dependency_artifact,
            dependency_index,
            "build",
            "dependency",
            "dep",
        );
        lines.push(dependency_artifact);

        let input = cargo_input_with_inventory(lines, false);
        let evidence = parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true)
            .expect("include-dependencies accepts exact unselected host proof units");
        assert_eq!(evidence.compiled_targets.len(), 2);
        assert_eq!(evidence.parsed.completed_proof_targets.len(), 2);
        assert!(evidence.compiled_targets.iter().any(|target| {
            target.package_name == "dep"
                && target.proof_unit_role == "dependency"
                && target.compile_target == TEST_COMPILE_TARGET
        }));
    }

    #[test]
    fn successful_inventory_rejects_dependency_or_test_execution_only_streams() {
        let root_id = "path+file:///fixture#demo@0.1.0";
        let dependency_id = "path+file:///fixture#dep@0.1.0";
        let selected = [(root_id.to_string(), "demo".to_string())].into_iter().collect();

        for (name, package_id, package_name, role) in [
            ("dependency-only", dependency_id, "dep", "dependency"),
            ("test-execution-only", root_id, "demo", "test-execution"),
        ] {
            let mut lines = Vec::new();
            append_complete_proof_unit(
                &mut lines,
                package_id,
                package_name,
                package_name,
                "lib",
                71,
                "build",
                role,
                true,
            );
            let error = parse_cargo_json_stdout(
                Cursor::new(successful_cargo_input(lines)),
                &selected,
                TEST_SESSION,
                true,
            )
            .err()
            .unwrap_or_else(|| panic!("{name} stream must not satisfy selected-root authority"));
            assert!(
                error.contains("omitted an authenticated primary proof unit"),
                "{name}: {error}"
            );
        }
    }

    /// T7c-5: one `--workspace` call over two members publishes their units in
    /// one canonical order (their Cargo unit identity), whichever order Cargo
    /// finished them in: the same rows, coverage rows and completed targets,
    /// in the same order, either way.
    #[test]
    fn a_workspace_streams_units_in_one_order_whatever_order_they_finish() {
        let alpha_id = "path+file:///fixture/alpha#0.1.0";
        let beta_id = "path+file:///fixture/beta#0.1.0";
        let selected = [
            (alpha_id.to_string(), "alpha".to_string()),
            (beta_id.to_string(), "beta".to_string()),
        ]
        .into_iter()
        .collect();
        let parse = |finished: [(&str, &str, u64); 2]| {
            let mut lines = Vec::new();
            for (package_id, name, index) in finished {
                append_complete_proof_unit(
                    &mut lines, package_id, name, name, "lib", index, "build", "primary", true,
                );
            }
            parse_cargo_json_stdout(
                Cursor::new(successful_cargo_input(lines)),
                &selected,
                TEST_SESSION,
                true,
            )
            .expect("two complete workspace members")
        };
        let alpha_first = parse([(alpha_id, "alpha", 1), (beta_id, "beta", 2)]);
        let beta_first = parse([(beta_id, "beta", 2), (alpha_id, "alpha", 1)]);

        let rows = |evidence: &CargoCompilerEvidence| {
            evidence
                .parsed
                .verification_results
                .iter()
                .map(|row| row.function.clone())
                .collect::<Vec<_>>()
        };
        let coverage = |evidence: &CargoCompilerEvidence| {
            evidence
                .parsed
                .coverage_rows
                .iter()
                .map(|row| row.package_name.clone())
                .collect::<Vec<_>>()
        };
        assert_eq!(rows(&alpha_first), rows(&beta_first));
        assert_eq!(rows(&alpha_first).len(), 2);
        assert!(rows(&alpha_first)[0].ends_with("::alpha::f"), "{:?}", rows(&alpha_first));
        assert!(rows(&alpha_first)[1].ends_with("::beta::f"), "{:?}", rows(&alpha_first));
        assert_eq!(coverage(&alpha_first), ["alpha", "beta"]);
        assert_eq!(coverage(&beta_first), ["alpha", "beta"]);
        assert_eq!(
            alpha_first.parsed.completed_proof_targets,
            beta_first.parsed.completed_proof_targets
        );
    }

    #[test]
    fn successful_inventory_requires_a_primary_for_every_selected_package() {
        let first_id = "path+file:///fixture#first@0.1.0";
        let second_id = "path+file:///fixture#second@0.1.0";
        let selected = [
            (first_id.to_string(), "first".to_string()),
            (second_id.to_string(), "second".to_string()),
        ]
        .into_iter()
        .collect();
        let mut lines = Vec::new();
        append_complete_proof_unit(
            &mut lines, first_id, "first", "first", "lib", 72, "build", "primary", true,
        );

        let error = parse_cargo_json_stdout(
            Cursor::new(successful_cargo_input(lines)),
            &selected,
            TEST_SESSION,
            true,
        )
        .err()
        .expect("one selected package cannot stand in for another");
        assert!(error.contains("second"), "{error}");
        assert!(error.contains(second_id), "{error}");
    }

    #[test]
    fn successful_process_requires_unique_build_finished_boundary() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let mut lines = Vec::new();
        append_complete_proof_unit(
            &mut lines, package_id, "demo", "demo", "lib", 79, "build", "primary", true,
        );
        let input = cargo_input_with_inventory(lines, false);
        let evidence = parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true)
            .expect("parsing partial evidence remains useful for a failed process diagnostic");
        let error = evidence
            .require_successful_selected_roots(&selected, true)
            .expect_err("a successful caller must require Cargo's terminal boundary");
        assert!(error.contains("omitted its authenticated build-finished boundary"), "{error}");
    }

    #[test]
    fn declared_inventory_detects_a_wholly_invisible_proof_unit() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let mut lines = Vec::new();
        append_complete_proof_unit(
            &mut lines, package_id, "demo", "demo", "lib", 80, "build", "primary", true,
        );
        append_complete_proof_unit(
            &mut lines, package_id, "demo", "hidden", "bin", 81, "build", "primary", true,
        );
        let input = successful_cargo_input(lines)
            .lines()
            .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
            .filter(|line| {
                line.get("reason").and_then(serde_json::Value::as_str)
                    == Some("trust-proof-inventory")
                    || line.get("reason").and_then(serde_json::Value::as_str)
                        == Some("build-finished")
                    || line.pointer("/trust_proof_unit/index").and_then(serde_json::Value::as_u64)
                        != Some(1)
            })
            .map(|line| format!("{line}\n"))
            .collect::<String>();

        let error = parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true)
            .err()
            .expect("a declared proof unit with no compiler evidence must fail closed");
        assert!(error.contains("ended before its required"), "{error}");
        assert!(error.contains("hidden"), "{error}");
    }

    #[test]
    fn excluded_inventory_is_exact_reasoned_and_dependency_policy_bound() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let mut lines = Vec::new();
        append_complete_proof_unit(
            &mut lines, package_id, "demo", "demo", "lib", 82, "build", "primary", true,
        );
        let mut values = successful_cargo_input(lines)
            .lines()
            .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
            .collect::<Vec<_>>();
        let mut excluded = serde_json::json!({
            "index": 1,
            "mode": "run-custom-build",
            "package_id": "registry+https://example.invalid/index#dep@1.2.3",
            "package_name": "dep",
            "target_name": "build-script-build",
            "target_kinds": ["custom-build"],
            "compile_target": TEST_COMPILE_TARGET,
            "exclusion_reason": TARGO_TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION,
            "graph_role": "control",
        });
        set_excluded_unit_semantics(&mut excluded, "run-custom-build");
        values[0]["excluded_units"] = serde_json::json!([excluded.clone()]);
        let input = values.iter().map(|line| format!("{line}\n")).collect::<String>();
        let evidence = parse_cargo_json_stdout(Cursor::new(&input), &selected, TEST_SESSION, true)
            .expect("false dependency policy retains exact excluded active units");
        let inventory = evidence.declared_inventory.expect("declared inventory");
        assert!(!inventory.include_dependencies);
        assert_eq!(inventory.excluded_targets.len(), 1);
        let target = inventory.excluded_targets.iter().next().unwrap();
        assert_eq!(target.package_name, "dep");
        assert_eq!(target.proof_unit_role, "excluded");
        assert_eq!(
            inventory.excluded_reasons.get(target).map(String::as_str),
            Some(TARGO_TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION)
        );
        assert_eq!(inventory.excluded_graph_roles.get(target).map(String::as_str), Some("control"));

        values[0]["include_dependencies"] = serde_json::json!(true);
        let input = values.iter().map(|line| format!("{line}\n")).collect::<String>();
        parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true).expect(
            "include-dependencies does not turn Cargo control jobs into compiler proof units",
        );

        values[0]["include_dependencies"] = serde_json::json!(false);
        values[0]["excluded_units"][0]["mode"] = serde_json::json!("build");
        set_excluded_unit_semantics(&mut values[0]["excluded_units"][0], "build");
        values[0]["excluded_units"][0]["target_name"] = serde_json::json!("dep");
        values[0]["excluded_units"][0]["target_kinds"] = serde_json::json!(["lib"]);
        values[0]["excluded_units"][0]["exclusion_reason"] =
            serde_json::json!(TARGO_TRUST_EXCLUSION_DEPENDENCY_POLICY);
        values[0]["excluded_units"][0]["graph_role"] = serde_json::json!("dependency");
        let input = values.iter().map(|line| format!("{line}\n")).collect::<String>();
        parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true).expect(
            "false dependency policy may explicitly exclude compiler-capable dependency units",
        );

        values[0]["excluded_units"][0]["graph_role"] = serde_json::json!("primary");
        values[0]["excluded_units"][0]["package_id"] = serde_json::json!(package_id);
        values[0]["excluded_units"][0]["package_name"] = serde_json::json!("demo");
        let input = values.iter().map(|line| format!("{line}\n")).collect::<String>();
        let error = parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true)
            .err()
            .expect("dependency policy cannot exclude a selected primary by relabeling it");
        assert!(error.contains("instead of dependency"), "{error}");

        values[0]["excluded_units"][0]["graph_role"] = serde_json::json!("dependency");
        values[0]["include_dependencies"] = serde_json::json!(true);
        let input = values.iter().map(|line| format!("{line}\n")).collect::<String>();
        let error = parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true)
            .err()
            .expect("include-dependencies=true cannot retain a policy-excluded compiler unit");
        assert!(error.contains("despite include-dependencies=true"), "{error}");
    }

    /// The per-compilation-unit scoping contract, as observed from a real
    /// stage2 `targo` run (workspace lib, third-party dependency lib, build
    /// script, proc macro):
    ///
    /// * the selected workspace unit is a PROOF unit — Targo appended no
    ///   `-Ztrust-verify=off`, and its transport rows must carry this run's
    ///   session nonce (any other session is rejected by the parser);
    /// * the third-party dependency lib, the build-script compile unit, and the
    ///   proc-macro lib are all EXCLUDED with the `dependency-policy` reason,
    ///   which is exactly the partition Targo compiles with the off-switch;
    /// * a selected package may own `dependency-policy` rows (its own build
    ///   script always does), but it must still have left a Unit in the proof
    ///   frontier — otherwise the off-switch silently unverified the crate the
    ///   user asked about, and the run fails closed.
    #[test]
    fn dependency_policy_scopes_off_deps_and_host_units_but_never_the_selected_package() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected: BTreeMap<String, String> =
            [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let mut lines = Vec::new();
        append_complete_proof_unit(
            &mut lines, package_id, "demo", "demo", "lib", 0, "build", "primary", true,
        );
        let mut values = successful_cargo_input(lines)
            .lines()
            .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
            .collect::<Vec<_>>();

        let scoped_off = |index: u64,
                          package_id: &str,
                          package_name: &str,
                          target_name: &str,
                          target_kind: &str| {
            let mut unit = serde_json::json!({
                "index": index,
                "mode": "build",
                "package_id": package_id,
                "package_name": package_name,
                "target_name": target_name,
                "target_kinds": [target_kind],
                "compile_target": TEST_COMPILE_TARGET,
                "exclusion_reason": TARGO_TRUST_EXCLUSION_DEPENDENCY_POLICY,
                "graph_role": "dependency",
            });
            set_excluded_unit_semantics(&mut unit, "build");
            unit
        };
        let dependency_lib = scoped_off(
            1,
            "registry+https://example.invalid/index#thirdparty@1.2.3",
            "thirdparty",
            "thirdparty",
            "lib",
        );
        // Targo's own graph role for a build-script COMPILE unit is
        // `dependency`, and it belongs to the SELECTED package.
        let build_script = scoped_off(2, package_id, "demo", "build-script-build", "custom-build");
        let proc_macro = scoped_off(
            3,
            "registry+https://example.invalid/index#fixture-pm@0.1.0",
            "fixture-pm",
            "fixture-pm",
            "lib",
        );
        values[0]["excluded_units"] =
            serde_json::json!([dependency_lib, build_script.clone(), proc_macro]);
        let input = values.iter().map(|line| format!("{line}\n")).collect::<String>();
        let evidence = parse_cargo_json_stdout(Cursor::new(&input), &selected, TEST_SESSION, true)
            .expect("scoped-off dependency, build-script and proc-macro units are admitted");
        let inventory = evidence.declared_inventory.expect("declared inventory");

        // Workspace unit: verification ON.
        assert_eq!(inventory.proof_targets.len(), 1);
        let verified = inventory.proof_targets.iter().next().unwrap();
        assert_eq!(verified.package_name, "demo");
        assert_eq!(verified.proof_unit_role, "primary");
        assert!(
            !inventory.excluded_targets.iter().any(|target| target.target_name == "demo"),
            "the selected workspace lib must never carry an exclusion row"
        );

        // Dependency / host units: verification OFF via the dependency policy.
        let mut scoped_out = inventory
            .excluded_targets
            .iter()
            .map(|target| {
                (
                    target.target_name.as_str(),
                    inventory.excluded_reasons.get(target).map(String::as_str),
                    inventory.excluded_graph_roles.get(target).map(String::as_str),
                )
            })
            .collect::<Vec<_>>();
        scoped_out.sort_unstable();
        assert_eq!(
            scoped_out,
            [
                (
                    "build-script-build",
                    Some(TARGO_TRUST_EXCLUSION_DEPENDENCY_POLICY),
                    Some("dependency")
                ),
                ("fixture-pm", Some(TARGO_TRUST_EXCLUSION_DEPENDENCY_POLICY), Some("dependency")),
                ("thirdparty", Some(TARGO_TRUST_EXCLUSION_DEPENDENCY_POLICY), Some("dependency")),
            ]
        );

        // The session nonce reached the authenticated primary target: the
        // parser accepts only `TEST_SESSION`, so re-parsing under a different
        // expected session must reject this same authenticated stream.
        let stale = parse_cargo_json_stdout(Cursor::new(&input), &selected, "other-session", true)
            .err()
            .expect("primary-target evidence is bound to this run's session nonce");
        assert!(stale.contains("session"), "{stale}");

        // Fail closed: the dependency off-switch must not be the reason the
        // selected package itself went unverified.
        let mut orphaned = values.clone();
        let mut selected_lib = build_script;
        selected_lib["target_name"] = serde_json::json!("demo");
        selected_lib["target_kinds"] = serde_json::json!(["lib"]);
        orphaned[0]["excluded_units"] = serde_json::json!([selected_lib]);
        orphaned[0]["units"] = serde_json::json!([]);
        orphaned.retain(|line| line.get("trust_proof_unit").is_none());
        orphaned[0]["excluded_units"][0]["index"] = serde_json::json!(0);
        let input = orphaned.iter().map(|line| format!("{line}\n")).collect::<String>();
        let error = parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true)
            .err()
            .expect("dependency policy cannot leave a selected package unverified");
        assert!(
            error.contains("scoped out selected package \"demo\"")
                && error.contains("without leaving any of its Units in the proof frontier"),
            "{error}"
        );
    }

    #[test]
    fn excluded_inventory_reasons_are_required_and_mode_bound() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let mut lines = Vec::new();
        append_complete_proof_unit(
            &mut lines, package_id, "demo", "demo", "lib", 83, "build", "primary", true,
        );
        let mut values = successful_cargo_input(lines)
            .lines()
            .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
            .collect::<Vec<_>>();
        let mut excluded = serde_json::json!({
            "index": 1,
            "mode": "doctest",
            "package_id": package_id,
            "package_name": "demo",
            "target_name": "demo",
            "target_kinds": ["lib"],
            "compile_target": TEST_COMPILE_TARGET,
            "exclusion_reason": TARGO_TRUST_EXCLUSION_DEFERRED_DOCTEST,
            "graph_role": "primary",
        });
        set_excluded_unit_semantics(&mut excluded, "doctest");
        values[0]["excluded_units"] = serde_json::json!([excluded]);
        parse_cargo_json_stdout(
            Cursor::new(values.iter().map(|line| format!("{line}\n")).collect::<String>()),
            &selected,
            TEST_SESSION,
            true,
        )
        .expect("deferred doctest has an exact non-compiler exclusion");

        let mutations = [
            (serde_json::Value::Null, "omitted its canonical exclusion reason"),
            (serde_json::json!("invented-reason"), "unsupported exclusion reason"),
            (
                serde_json::json!(TARGO_TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION),
                "did not name a run-custom-build/custom-build Unit",
            ),
            (
                serde_json::json!(TARGO_TRUST_EXCLUSION_DOCUMENTATION),
                "did not name a doc/docscrape Unit",
            ),
            (
                serde_json::json!(TARGO_TRUST_EXCLUSION_COMPILE_TIME_DEPS_FILTERED),
                "redundantly named a non-proof Cargo mode",
            ),
            // Retired producer exemptions are never accepted, even when the
            // current dependency policy could exclude the same compiler unit.
            (
                serde_json::json!(TARGO_TRUST_EXCLUSION_BUILD_SUPPORT_ONLY),
                "retired exclusion reason",
            ),
            // Macro admission is not an exemption from compiler-unit proof.
            (
                serde_json::json!(TARGO_TRUST_EXCLUSION_AUDITED_TRUST_SPEC),
                "retired exclusion reason",
            ),
        ];
        for (reason, expected) in mutations {
            values[0]["excluded_units"][0]["exclusion_reason"] = reason;
            let input = values.iter().map(|line| format!("{line}\n")).collect::<String>();
            let error = parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true)
                .err()
                .expect("reason/mode mismatch must fail closed");
            assert!(error.contains(expected), "expected {expected:?}, got {error:?}");
        }

        values[0]["excluded_units"][0]["exclusion_reason"] =
            serde_json::json!(TARGO_TRUST_EXCLUSION_DEFERRED_DOCTEST);
        for (role, expected) in [
            (serde_json::Value::Null, "omitted its closed-set Cargo graph role"),
            (serde_json::json!("control"), "invalid Cargo graph role"),
            (serde_json::json!("test-execution"), "was not a Build-mode library or binary"),
        ] {
            values[0]["excluded_units"][0]["graph_role"] = role;
            let input = values.iter().map(|line| format!("{line}\n")).collect::<String>();
            let error = parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true)
                .err()
                .expect("excluded graph role is required and reason-bound");
            assert!(error.contains(expected), "expected {expected:?}, got {error:?}");
        }
    }

    /// D2d (2026-09-28): Targo's doctest census refines EXACTLY the declared
    /// deferred doctest Unit it names (index and identity digest), and only for
    /// a zero count. A Unit holding a doctest, or with no census at all, stays
    /// `deferred-doctest-execution`; a census that names anything else, repeats,
    /// or carries extra fields is a transport violation, and the inventory can
    /// never declare the census-only reason itself.
    #[test]
    fn doctest_census_refines_only_the_declared_empty_doctest_unit() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let mut lines = Vec::new();
        append_complete_proof_unit(
            &mut lines, package_id, "demo", "demo", "lib", 85, "build", "primary", true,
        );
        let mut values = successful_cargo_input(lines)
            .lines()
            .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
            .collect::<Vec<_>>();
        let mut excluded = serde_json::json!({
            "index": 1,
            "mode": "doctest",
            "package_id": package_id,
            "package_name": "demo",
            "target_name": "demo",
            "target_kinds": ["lib"],
            "compile_target": TEST_COMPILE_TARGET,
            "exclusion_reason": TARGO_TRUST_EXCLUSION_DEFERRED_DOCTEST,
            "graph_role": "primary",
        });
        set_excluded_unit_semantics(&mut excluded, "doctest");
        values[0]["excluded_units"] = serde_json::json!([excluded]);
        let census = |index: u64, identity: &str, doctests: u64| {
            serde_json::json!({
                "reason": "trust-doctest-census",
                "schema": TARGO_TRUST_DOCTEST_CENSUS_SCHEMA_V1,
                "index": index,
                "trust_unit_identity_sha256": identity,
                "doctests": doctests,
            })
        };
        // The census is emitted inside the job queue: after the inventory,
        // before Cargo's terminal `build-finished`.
        let stream_of = |values: &[serde_json::Value], censuses: &[serde_json::Value]| {
            let mut lines = values.to_vec();
            let finished = lines.pop().expect("build-finished");
            lines.extend(censuses.iter().cloned());
            lines.push(finished);
            lines.iter().map(|line| format!("{line}\n")).collect::<String>()
        };
        let stream = |censuses: &[serde_json::Value]| stream_of(&values, censuses);
        let doctest_reason = |censuses: &[serde_json::Value]| {
            let evidence = parse_cargo_json_stdout(
                Cursor::new(stream(censuses)),
                &selected,
                TEST_SESSION,
                true,
            )
            .expect("census stream parses");
            let inventory = evidence.declared_inventory.expect("declared inventory");
            let reason = inventory
                .excluded_reasons
                .iter()
                .find(|(target, _)| target.proof_unit_index == 1)
                .map(|(_, reason)| reason.clone())
                .expect("doctest Unit keeps a reason");
            // The refined inventory must still project into a valid report.
            cargo_proof_inventory_report(Some(&inventory), &BTreeSet::new(), &BTreeSet::new())
                .expect("refined inventory projects into the report");
            reason
        };

        assert_eq!(doctest_reason(&[]), TARGO_TRUST_EXCLUSION_DEFERRED_DOCTEST);
        assert_eq!(
            doctest_reason(&[census(1, TEST_UNIT_IDENTITY_SHA256, 0)]),
            TARGO_TRUST_EXCLUSION_EMPTY_DOCTEST,
            "a doctest Unit with zero doctests defers nothing"
        );
        assert_eq!(
            doctest_reason(&[census(1, TEST_UNIT_IDENTITY_SHA256, 1)]),
            TARGO_TRUST_EXCLUSION_DEFERRED_DOCTEST,
            "a real doctest keeps its Unit deferred and disclosed"
        );

        let mut extra_field = census(1, TEST_UNIT_IDENTITY_SHA256, 0);
        extra_field["exclusion_reason"] = serde_json::json!(TARGO_TRUST_EXCLUSION_EMPTY_DOCTEST);
        let mut wrong_schema = census(1, TEST_UNIT_IDENTITY_SHA256, 0);
        wrong_schema["schema"] = serde_json::json!("targo.trust-doctest-census.v0");
        for (censuses, expected) in [
            (vec![census(1, &"d".repeat(64), 0)], "identity did not match the declared Unit"),
            (vec![census(0, TEST_UNIT_IDENTITY_SHA256, 0)], "not a declared excluded Unit"),
            (vec![census(7, TEST_UNIT_IDENTITY_SHA256, 0)], "not a declared excluded Unit"),
            (
                vec![
                    census(1, TEST_UNIT_IDENTITY_SHA256, 1),
                    census(1, TEST_UNIT_IDENTITY_SHA256, 0),
                ],
                "more than one doctest census",
            ),
            (vec![extra_field], "unexpected field"),
            (vec![wrong_schema], "exact schema"),
        ] {
            let error = parse_cargo_json_stdout(
                Cursor::new(stream(&censuses)),
                &selected,
                TEST_SESSION,
                true,
            )
            .err()
            .expect("a mis-bound census must fail closed");
            assert!(error.contains(expected), "expected {expected:?}, got {error:?}");
        }

        let mut censused = BTreeSet::new();
        let error =
            apply_doctest_census(None, &census(1, TEST_UNIT_IDENTITY_SHA256, 0), &mut censused)
                .expect_err("no inventory, nothing to refine");
        assert!(error.contains("before its declared proof inventory"), "{error}");

        let mut declared_empty = values.clone();
        declared_empty[0]["excluded_units"][0]["exclusion_reason"] =
            serde_json::json!(TARGO_TRUST_EXCLUSION_EMPTY_DOCTEST);
        let error = parse_cargo_json_stdout(
            Cursor::new(stream_of(&declared_empty, &[])),
            &selected,
            TEST_SESSION,
            true,
        )
        .err()
        .expect("the inventory cannot declare the census-only reason");
        assert!(error.contains("only its authenticated doctest census"), "{error}");
    }

    #[test]
    fn documentation_and_compile_time_filter_exclusions_are_closed_set() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let mut lines = Vec::new();
        append_complete_proof_unit(
            &mut lines, package_id, "demo", "demo", "lib", 84, "build", "primary", true,
        );
        let mut values = successful_cargo_input(lines)
            .lines()
            .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
            .collect::<Vec<_>>();
        let mut documentation = serde_json::json!({
            "index": 1,
            "mode": "doc",
            "package_id": package_id,
            "package_name": "demo",
            "target_name": "demo",
            "target_kinds": ["lib"],
            "compile_target": TEST_COMPILE_TARGET,
            "exclusion_reason": TARGO_TRUST_EXCLUSION_DOCUMENTATION,
            "graph_role": "primary",
        });
        set_excluded_unit_semantics(&mut documentation, "doc");
        let mut compile_time_filtered = serde_json::json!({
            "index": 2,
            "mode": "check",
            "package_id": "registry+https://example.invalid/index#filtered@1.0.0",
            "package_name": "filtered",
            "target_name": "filtered",
            "target_kinds": ["lib"],
            "compile_target": TEST_COMPILE_TARGET,
            "exclusion_reason": TARGO_TRUST_EXCLUSION_COMPILE_TIME_DEPS_FILTERED,
            "graph_role": "dependency",
        });
        set_excluded_unit_semantics(&mut compile_time_filtered, "check");
        values[0]["excluded_units"] = serde_json::json!([documentation, compile_time_filtered,]);
        values[0]["include_dependencies"] = serde_json::json!(true);
        let evidence = parse_cargo_json_stdout(
            Cursor::new(values.iter().map(|line| format!("{line}\n")).collect::<String>()),
            &selected,
            TEST_SESSION,
            true,
        )
        .expect("reasoned non-proof Units remain explicit with include-dependencies enabled");
        let inventory = evidence.declared_inventory.expect("inventory");
        assert_eq!(inventory.excluded_targets.len(), 2);
        assert_eq!(inventory.excluded_reasons.len(), 2);

        let mut forged_primary = values.clone();
        forged_primary[0]["excluded_units"][0]["package_id"] =
            serde_json::json!("registry+https://example.invalid/index#other@1.0.0");
        forged_primary[0]["excluded_units"][0]["package_name"] = serde_json::json!("other");
        let input = forged_primary.iter().map(|line| format!("{line}\n")).collect::<String>();
        let error = parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true)
            .err()
            .expect("excluded primary role must remain bound to selected package identity");
        assert!(error.contains("outside the exact selected package set"), "{error}");

        let mut malformed_test_execution = values;
        malformed_test_execution[0]["excluded_units"][1]["package_id"] =
            serde_json::json!(package_id);
        malformed_test_execution[0]["excluded_units"][1]["package_name"] =
            serde_json::json!("demo");
        malformed_test_execution[0]["excluded_units"][1]["graph_role"] =
            serde_json::json!("test-execution");
        let input =
            malformed_test_execution.iter().map(|line| format!("{line}\n")).collect::<String>();
        let error = parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true)
            .err()
            .expect("test-execution graph role requires exact executable Build unit shape");
        assert!(error.contains("was not a Build-mode library or binary"), "{error}");
    }

    #[test]
    fn retired_compiler_exclusions_are_rejected_in_every_dependency_policy() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let mut lines = Vec::new();
        append_complete_proof_unit(
            &mut lines, package_id, "demo", "demo", "lib", 86, "build", "primary", true,
        );
        let mut values = successful_cargo_input(lines)
            .lines()
            .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
            .collect::<Vec<_>>();
        for include_dependencies in [false, true] {
            for (kind, reason) in [
                ("custom-build", TARGO_TRUST_EXCLUSION_BUILD_SUPPORT_ONLY),
                ("lib", TARGO_TRUST_EXCLUSION_BUILD_SUPPORT_ONLY),
                ("proc-macro", TARGO_TRUST_EXCLUSION_AUDITED_TRUST_SPEC),
            ] {
                let mut excluded = serde_json::json!({
                    "index": 1,
                    "mode": "build",
                    "package_id": "path+file:///fixture/support#support@1.0.0",
                    "package_name": "support",
                    "target_name": "support",
                    "target_kinds": [kind],
                    "compile_target": TEST_COMPILE_TARGET,
                    "exclusion_reason": reason,
                    "graph_role": "dependency",
                });
                set_excluded_unit_semantics(&mut excluded, "build");
                values[0]["excluded_units"] = serde_json::json!([excluded]);
                values[0]["include_dependencies"] = serde_json::json!(include_dependencies);
                let input = values.iter().map(|line| format!("{line}\n")).collect::<String>();
                let error =
                    parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true)
                        .err()
                        .expect("retired compiler exemptions must not shrink the proof frontier");
                assert!(error.contains("retired exclusion reason"), "{error}");
            }
        }
    }

    #[test]
    fn proof_frontier_rejects_modes_without_authenticated_unit_protocol() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let mut lines = Vec::new();
        append_complete_proof_unit(
            &mut lines, package_id, "demo", "demo", "lib", 85, "build", "primary", true,
        );
        let baseline = successful_cargo_input(lines)
            .lines()
            .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
            .collect::<Vec<_>>();
        for mode in ["run-custom-build", "doctest", "doc", "docscrape"] {
            let mut values = baseline.clone();
            let semantics = fixture_unit_semantics(mode);
            let semantics_sha256 = fixture_semantics_sha256(&semantics);
            values[0]["units"][0]["trust_proof_unit"]["mode"] = serde_json::json!(mode);
            values[0]["units"][0]["trust_proof_unit"]["semantics_sha256"] =
                serde_json::json!(semantics_sha256);
            values[0]["units"][0]["trust_compile_mode"] = serde_json::json!(mode);
            values[0]["units"][0]["semantics"] = serde_json::to_value(semantics).unwrap();
            let input = values.iter().map(|line| format!("{line}\n")).collect::<String>();
            let error = parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true)
                .err()
                .expect("a mode without authenticated Unit protocol cannot enter proof frontier");
            assert!(
                error.contains("without authenticated per-Unit compiler protocol"),
                "mode={mode}: {error}"
            );
        }
    }

    #[test]
    fn successful_inventory_nonempty_policy_is_per_selected_package() {
        let root_id = "path+file:///fixture#demo@0.1.0";
        let dependency_id = "path+file:///fixture#dep@0.1.0";
        let selected = [(root_id.to_string(), "demo".to_string())].into_iter().collect();

        let mut masked = Vec::new();
        append_complete_proof_unit(
            &mut masked,
            root_id,
            "demo",
            "demo",
            "lib",
            73,
            "build",
            "primary",
            false,
        );
        append_complete_proof_unit(
            &mut masked,
            dependency_id,
            "dep",
            "dep",
            "lib",
            74,
            "build",
            "dependency",
            true,
        );
        let error = parse_cargo_json_stdout(
            Cursor::new(successful_cargo_input(masked)),
            &selected,
            TEST_SESSION,
            true,
        )
        .err()
        .expect("a proved dependency cannot mask an all-empty selected root");
        assert!(error.contains("zero coverage-eligible bodies across every primary"), "{error}");

        let mut zero_dependency = Vec::new();
        append_complete_proof_unit(
            &mut zero_dependency,
            root_id,
            "demo",
            "demo",
            "lib",
            75,
            "build",
            "primary",
            true,
        );
        append_complete_proof_unit(
            &mut zero_dependency,
            dependency_id,
            "dep",
            "dep",
            "lib",
            76,
            "build",
            "dependency",
            false,
        );
        parse_cargo_json_stdout(
            Cursor::new(successful_cargo_input(zero_dependency)),
            &selected,
            TEST_SESSION,
            true,
        )
        .expect("an empty dependency does not weaken a nonempty selected root");

        let mut mixed_primary = Vec::new();
        append_complete_proof_unit(
            &mut mixed_primary,
            root_id,
            "demo",
            "demo",
            "bin",
            77,
            "build",
            "primary",
            true,
        );
        append_complete_proof_unit(
            &mut mixed_primary,
            root_id,
            "demo",
            "marker",
            "lib",
            78,
            "build",
            "primary",
            false,
        );
        parse_cargo_json_stdout(
            Cursor::new(successful_cargo_input(mixed_primary)),
            &selected,
            TEST_SESSION,
            true,
        )
        .expect("a nonempty executable permits an empty marker-library companion");

        let mut masked_executable = Vec::new();
        append_complete_proof_unit(
            &mut masked_executable,
            root_id,
            "demo",
            "library",
            "lib",
            79,
            "build",
            "primary",
            true,
        );
        append_complete_proof_unit(
            &mut masked_executable,
            root_id,
            "demo",
            "empty-bin",
            "bin",
            80,
            "build",
            "primary",
            false,
        );
        let error = parse_cargo_json_stdout(
            Cursor::new(successful_cargo_input(masked_executable)),
            &selected,
            TEST_SESSION,
            true,
        )
        .err()
        .expect("a nonempty library must not mask an empty selected executable");
        assert!(error.contains("zero coverage-eligible bodies for executable selected root"));
        assert!(error.contains("empty-bin"), "{error}");

        let mut masked_native_harness = Vec::new();
        append_complete_proof_unit(
            &mut masked_native_harness,
            root_id,
            "demo",
            "library",
            "lib",
            81,
            "build",
            "primary",
            true,
        );
        append_complete_proof_unit(
            &mut masked_native_harness,
            root_id,
            "demo",
            "library",
            "lib",
            82,
            "test",
            "primary",
            false,
        );
        let error = parse_cargo_json_stdout(
            Cursor::new(successful_cargo_input(masked_native_harness)),
            &selected,
            TEST_SESSION,
            true,
        )
        .err()
        .expect("a native Test-mode harness must independently contain an eligible body");
        assert!(error.contains("zero coverage-eligible bodies for executable selected root"));
        assert!(error.contains("proof_unit_mode=\"test\""), "{error}");
    }

    #[test]
    fn same_name_lib_summary_cannot_complete_bin_target() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let lib_coverage = cargo_transport_envelope_with_kind(
            package_id,
            "demo",
            "lib",
            &empty_complete_coverage("demo", "demo"),
        );
        let lib_summary = cargo_transport_envelope_with_kind(
            package_id,
            "demo",
            "lib",
            &empty_primary_summary("demo", "demo"),
        );
        let lib_artifact = cargo_artifact_with_kind(package_id, "demo", "lib", false);
        let bin_artifact = cargo_artifact_with_kind(package_id, "demo", "bin", false);
        let input = cargo_input_with_inventory(
            vec![lib_coverage, lib_summary, lib_artifact, bin_artifact],
            false,
        );

        let error = parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true)
            .err()
            .expect("a bin artifact cannot borrow the same-name lib terminal summary");
        assert!(error.contains("compiler-artifact before its terminal crate summary"), "{error}");
        assert!(error.contains("kind=[\"bin\"]"), "{error}");
    }

    #[test]
    fn selected_targets_for_two_effective_compile_triples_fail_closed() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let host = cargo_artifact_with_kind_and_compile_target(
            package_id,
            "demo",
            "lib",
            "x86_64-unknown-linux-gnu",
            false,
        );
        let mut cross = cargo_artifact_with_kind_and_compile_target(
            package_id,
            "demo",
            "lib",
            "aarch64-unknown-linux-gnu",
            false,
        );
        // Distinct Cargo compile kinds are distinct exact units even when the
        // package and Rust target are otherwise identical.
        cross["trust_proof_unit"]["index"] =
            serde_json::json!(fixture_unit_index(package_id, "demo", "lib").wrapping_add(1));
        let error = parse_cargo_json_stdout(
            Cursor::new(cargo_input_with_inventory(vec![host, cross], false)),
            &selected,
            TEST_SESSION,
            true,
        )
        .err()
        .expect("mixed effective compile targets must reject");
        assert!(error.contains("multiple effective compile targets"), "{error}");
        assert!(error.contains("aarch64-unknown-linux-gnu"), "{error}");
        assert!(error.contains("x86_64-unknown-linux-gnu"), "{error}");
    }

    #[test]
    fn cargo_evidence_requires_compile_target_identity() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let mut artifact = cargo_artifact(package_id, "demo", false);
        artifact.as_object_mut().expect("artifact object").remove("trust_compile_target");
        let error = parse_cargo_json_stdout(
            Cursor::new(format!("{artifact}\n")),
            &selected,
            TEST_SESSION,
            true,
        )
        .err()
        .expect("missing compile target identity must reject");
        assert!(error.contains("compile-target identity"), "{error}");
    }

    #[test]
    fn cargo_evidence_requires_compile_mode_identity() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let mut artifact = cargo_artifact(package_id, "demo", false);
        artifact.as_object_mut().expect("artifact object").remove("trust_compile_mode");
        let error = parse_cargo_json_stdout(
            Cursor::new(format!("{artifact}\n")),
            &selected,
            TEST_SESSION,
            true,
        )
        .err()
        .expect("missing compile mode identity must reject");
        assert!(error.contains("compile-mode identity"), "{error}");
    }

    #[test]
    fn cargo_evidence_cross_binds_compile_mode_to_proof_unit_mode() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let mut artifact = cargo_artifact(package_id, "demo", false);
        artifact
            .as_object_mut()
            .expect("artifact object")
            .insert("trust_compile_mode".to_string(), serde_json::json!("build"));
        let error = parse_cargo_json_stdout(
            Cursor::new(format!("{artifact}\n")),
            &selected,
            TEST_SESSION,
            true,
        )
        .err()
        .expect("disagreeing Cargo mode identities must reject");
        assert!(error.contains("disagreed about its compile mode"), "{error}");
    }

    #[test]
    fn cargo_evidence_requires_compile_kind_identity() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let mut artifact = cargo_artifact(package_id, "demo", false);
        artifact.as_object_mut().expect("artifact object").remove("trust_compile_kind");
        let error = parse_cargo_json_stdout(
            Cursor::new(format!("{artifact}\n")),
            &selected,
            TEST_SESSION,
            true,
        )
        .err()
        .expect("missing compile kind identity must reject");
        assert!(error.contains("compile-kind identity"), "{error}");
    }

    #[test]
    fn host_and_target_host_triple_units_do_not_alias() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let mut target = cargo_artifact(package_id, "demo", false);
        set_envelope_proof_unit(&mut target, 0, "test", "primary", "demo");
        let mut host = target.clone();
        {
            let object = host.as_object_mut().expect("artifact object");
            object.insert("trust_compile_kind".to_string(), serde_json::json!("host"));
            object.insert(
                "trust_unit_identity_sha256".to_string(),
                serde_json::json!(
                    "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee"
                ),
            );
        }
        set_envelope_proof_unit(&mut host, 1, "test", "primary", "demo");
        let target = cargo_target_identity(&target, package_id, &selected)
            .expect("target identity")
            .expect("authenticated target identity");
        let host = cargo_target_identity(&host, package_id, &selected)
            .expect("host identity")
            .expect("authenticated host identity");
        let identities = BTreeSet::from([target, host]);
        assert_eq!(identities.len(), 2);
        assert_eq!(
            identities.iter().map(|target| target.compile_kind.as_str()).collect::<BTreeSet<_>>(),
            BTreeSet::from(["host", "target"])
        );
    }

    #[test]
    fn build_and_test_views_are_distinct_authenticated_targets() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let mut build = cargo_artifact(package_id, "demo", false);
        set_envelope_proof_unit(&mut build, 0, "build", "primary", "demo");
        let mut test = build.clone();
        set_envelope_proof_unit(&mut test, 1, "test", "primary", "demo");
        {
            let object = test.as_object_mut().expect("artifact object");
            object.insert(
                "trust_unit_identity_sha256".to_string(),
                serde_json::json!(
                    "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"
                ),
            );
        }

        let build = cargo_target_identity(&build, package_id, &selected)
            .expect("build identity")
            .expect("authenticated build identity");
        let test = cargo_target_identity(&test, package_id, &selected)
            .expect("test identity")
            .expect("authenticated test identity");
        let identities = BTreeSet::from([build, test]);
        assert_eq!(identities.len(), 2);
        assert_eq!(
            identities.iter().map(|target| target.compile_mode.as_str()).collect::<BTreeSet<_>>(),
            BTreeSet::from(["build", "test"])
        );
    }

    #[test]
    fn cargo_evidence_requires_canonical_semantic_unit_identity() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        for replacement in [None, Some(serde_json::json!("not-a-sha256"))] {
            let mut artifact = cargo_artifact(package_id, "demo", false);
            let object = artifact.as_object_mut().expect("artifact object");
            match replacement.clone() {
                Some(value) => {
                    object.insert("trust_unit_identity_sha256".to_string(), value);
                }
                None => {
                    object.remove("trust_unit_identity_sha256");
                }
            }
            let error = parse_cargo_json_stdout(
                Cursor::new(format!("{artifact}\n")),
                &selected,
                TEST_SESSION,
                true,
            )
            .err()
            .expect("missing or malformed unit identity must reject");
            assert!(error.contains("unit-identity SHA-256"), "{error}");
        }
    }

    #[test]
    fn custom_target_evidence_requires_canonical_spec_digest() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let custom_target = "/workspace/targets/custom.json";

        let missing = cargo_artifact_with_target_identity(
            package_id,
            "demo",
            "lib",
            custom_target,
            None,
            false,
        );
        let error = parse_cargo_json_stdout(
            Cursor::new(format!("{missing}\n")),
            &selected,
            TEST_SESSION,
            true,
        )
        .err()
        .expect("custom target without byte identity must reject");
        assert!(error.contains("omitted the exact custom JSON target-spec SHA-256"), "{error}");

        let malformed = cargo_artifact_with_target_identity(
            package_id,
            "demo",
            "lib",
            custom_target,
            Some("AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"),
            false,
        );
        let error = parse_cargo_json_stdout(
            Cursor::new(format!("{malformed}\n")),
            &selected,
            TEST_SESSION,
            true,
        )
        .err()
        .expect("noncanonical target digest must reject");
        assert!(error.contains("non-canonical custom target-spec SHA-256"), "{error}");
    }

    #[test]
    fn same_custom_target_path_cannot_hide_spec_mutation_between_envelopes() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let custom_target = "/workspace/targets/custom.json";
        let before = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        let after = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
        let coverage = cargo_transport_envelope_with_target_identity(
            package_id,
            "demo",
            "lib",
            custom_target,
            Some(before),
            &empty_complete_coverage("demo", "demo"),
        );
        let terminal = cargo_transport_envelope_with_target_identity(
            package_id,
            "demo",
            "lib",
            custom_target,
            Some(before),
            &empty_primary_summary("demo", "demo"),
        );
        let artifact = cargo_artifact_with_target_identity(
            package_id,
            "demo",
            "lib",
            custom_target,
            Some(after),
            false,
        );
        let error = parse_cargo_json_stdout(
            Cursor::new(format!("{coverage}\n{terminal}\n{artifact}\n")),
            &selected,
            TEST_SESSION,
            true,
        )
        .err()
        .expect("same-path custom target mutation must reject");
        assert!(error.contains("proof-unit index"), "{error}");
        assert!(error.contains("changed identity"), "{error}");
        assert!(error.contains(before), "{error}");
        assert!(error.contains(after), "{error}");
    }

    #[test]
    fn custom_target_identity_preserves_exact_spec_digest() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let custom_target = "/workspace/targets/custom.json";
        let digest = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        let coverage = cargo_transport_envelope_with_target_identity(
            package_id,
            "demo",
            "lib",
            custom_target,
            Some(digest),
            &empty_complete_coverage("demo", "demo"),
        );
        let terminal = cargo_transport_envelope_with_target_identity(
            package_id,
            "demo",
            "lib",
            custom_target,
            Some(digest),
            &empty_primary_summary("demo", "demo"),
        );
        let artifact = cargo_artifact_with_target_identity(
            package_id,
            "demo",
            "lib",
            custom_target,
            Some(digest),
            false,
        );
        let evidence = parse_cargo_json_stdout(
            Cursor::new(cargo_input_with_inventory(vec![coverage, terminal, artifact], false)),
            &selected,
            TEST_SESSION,
            true,
        )
        .expect("stable custom target identity should authenticate");
        let identity = evidence.compiled_targets.iter().next().expect("compiled target");
        assert_eq!(identity.compile_target, custom_target);
        assert_eq!(identity.compile_target_spec_sha256.as_deref(), Some(digest));
        assert!(identity.report_label().contains(digest));
    }

    #[test]
    fn coverage_inventory_remains_bound_to_each_cargo_target() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let input = cargo_input_with_inventory(
            vec![
                cargo_transport_envelope_with_kind(
                    package_id,
                    "demo",
                    "lib",
                    &empty_complete_coverage("demo", "demo"),
                ),
                cargo_transport_envelope_with_kind(
                    package_id,
                    "demo",
                    "lib",
                    &empty_primary_summary("demo", "demo"),
                ),
                cargo_transport_envelope_with_kind(
                    package_id,
                    "demo",
                    "bin",
                    &empty_primary_summary("demo", "demo"),
                ),
                cargo_artifact_with_kind(package_id, "demo", "lib", false),
                cargo_artifact_with_kind(package_id, "demo", "bin", false),
            ],
            false,
        );

        let evidence = parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, false)
            .expect("advisory coverage remains target-bound without borrowing across units");
        assert_eq!(evidence.parsed.completed_proof_targets.len(), 2);
        assert_eq!(evidence.parsed.coverage_proof_targets.len(), 1);
        assert!(
            evidence
                .parsed
                .coverage_proof_targets
                .iter()
                .all(|target| target.target_kinds == ["lib"])
        );
    }

    #[test]
    fn non_primary_unauthenticated_and_wrong_session_coverage_cannot_fill_root_target() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();

        let non_primary =
            trust_types::TransportMessage::CoverageSummary(trust_types::CoverageTransportSummary {
                crate_name: "demo".to_string(),
                package_name: "demo".to_string(),
                primary_package: false,
                verification_session: TEST_SESSION.to_string(),
                eligible: 1,
                processed: 1,
                noted_stops: Vec::new(),
                degraded_anchors: 0,
                function_identities: None,
                memory: trust_types::MemorySummary::default(),
            });
        let non_primary = cargo_transport_envelope(package_id, "demo", &non_primary);
        assert!(
            parse_cargo_json_stdout(
                Cursor::new(format!("{non_primary}\n")),
                &selected,
                TEST_SESSION,
                true,
            )
            .is_err(),
            "a host/dependency unit must not satisfy root-target coverage"
        );
        let advisory = parse_cargo_json_stdout(
            Cursor::new(format!("{non_primary}\n")),
            &selected,
            TEST_SESSION,
            false,
        )
        .expect("advisory mode should discard unauthenticated coverage");
        assert!(advisory.parsed.coverage_rows.is_empty());

        // Trust (T3 L4, C09w): a row with no `memory` summary is refused at the parse; one
        // that carries it but no package, session or identities parses and stays
        // unauthenticated.
        assert!(
            trust_types::parse_transport_payload(
                r#"{"type":"coverage_summary","crate_name":"demo","eligible":1,"processed":1}"#,
            )
            .is_err()
        );
        let unauthenticated = trust_types::parse_transport_payload(
            r#"{"type":"coverage_summary","crate_name":"demo","eligible":1,"processed":1,"memory":{"schema":"trust-memory-summary/v1","counters":{}}}"#,
        )
        .expect("an unauthenticated coverage row parses");
        let unauthenticated = cargo_transport_envelope(package_id, "demo", &unauthenticated);
        assert!(
            parse_cargo_json_stdout(
                Cursor::new(format!("{unauthenticated}\n")),
                &selected,
                TEST_SESSION,
                true,
            )
            .is_err(),
            "an unauthenticated coverage row must carry no proof-grade credit"
        );
        let advisory = parse_cargo_json_stdout(
            Cursor::new(format!("{unauthenticated}\n")),
            &selected,
            TEST_SESSION,
            false,
        )
        .expect("unauthenticated JSON remains usable as advisory transport");
        assert!(advisory.parsed.coverage_rows.is_empty());

        let wrong_session =
            trust_types::TransportMessage::CoverageSummary(trust_types::CoverageTransportSummary {
                crate_name: "demo".to_string(),
                package_name: "demo".to_string(),
                primary_package: true,
                verification_session: "another-session".to_string(),
                eligible: 1,
                processed: 1,
                noted_stops: Vec::new(),
                degraded_anchors: 0,
                function_identities: None,
                memory: trust_types::MemorySummary::default(),
            });
        let wrong_session = cargo_transport_envelope(package_id, "demo", &wrong_session);
        assert!(
            parse_cargo_json_stdout(
                Cursor::new(format!("{wrong_session}\n")),
                &selected,
                TEST_SESSION,
                true,
            )
            .is_err(),
            "coverage from another proof invocation must not be replayed"
        );
        let advisory = parse_cargo_json_stdout(
            Cursor::new(format!("{wrong_session}\n")),
            &selected,
            TEST_SESSION,
            false,
        )
        .expect("advisory mode should treat mismatched coverage as unknown");
        assert!(advisory.parsed.coverage_rows.is_empty());
    }

    #[test]
    fn cargo_rejects_stale_function_and_terminal_rows_even_with_current_coverage() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();

        for stale_variant in ["function", "terminal"] {
            let mut function = one_unknown_primary_function("demo", "demo", "demo::f");
            let mut terminal = one_unknown_primary_summary("demo", "demo");
            match stale_variant {
                "function" => {
                    let trust_types::TransportMessage::FunctionResult(row) = &mut function else {
                        unreachable!()
                    };
                    row.verification_session = "stale-session".to_string();
                }
                "terminal" => {
                    let trust_types::TransportMessage::CrateSummary(row) = &mut terminal else {
                        unreachable!()
                    };
                    row.verification_session = "stale-session".to_string();
                }
                _ => unreachable!(),
            }
            let input = [
                cargo_transport_envelope(package_id, "demo", &function),
                cargo_transport_envelope(package_id, "demo", &complete_coverage("demo", "demo")),
                cargo_transport_envelope(package_id, "demo", &terminal),
                cargo_artifact(package_id, "demo", false),
            ]
            .into_iter()
            .map(|value| value.to_string())
            .collect::<Vec<_>>()
            .join("\n");

            let error = parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true)
                .err()
                .unwrap_or_else(|| panic!("stale {stale_variant} row must reject"));
            assert!(error.contains("scope/session"), "{stale_variant}: {error}");
        }
    }

    #[test]
    fn duplicate_primary_coverage_for_one_target_fails_closed() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let coverage =
            cargo_transport_envelope(package_id, "demo", &complete_coverage("demo", "demo"));
        let input = format!("{coverage}\n{coverage}\n");

        let error = parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true)
            .err()
            .expect("duplicate coverage inventories must be rejected");
        assert!(error.contains("duplicate coverage summaries"), "{error}");
    }

    #[test]
    fn raw_coverage_requires_unscoped_current_session_identity() {
        let current = trust_types::CoverageTransportSummary {
            crate_name: "demo".to_string(),
            package_name: String::new(),
            primary_package: false,
            verification_session: TEST_SESSION.to_string(),
            eligible: 1,
            processed: 1,
            noted_stops: Vec::new(),
            degraded_anchors: 0,
            function_identities: Some(trust_types::CoverageFunctionIdentityInventory {
                schema: trust_types::COVERAGE_FUNCTION_IDENTITY_SCHEMA_V1.to_string(),
                eligible_functions: vec!["demo::f".to_string()],
                processed_functions: vec!["demo::f".to_string()],
            }),
            memory: trust_types::MemorySummary::default(),
        };
        let current =
            serde_json::to_string(&trust_types::TransportMessage::CoverageSummary(current))
                .unwrap();
        let mut function = one_unknown_primary_function("demo", "demo", "demo::f");
        let trust_types::TransportMessage::FunctionResult(function_row) = &mut function else {
            unreachable!()
        };
        function_row.package_name = None;
        function_row.primary_package = false;
        let function = serde_json::to_string(&function).unwrap();
        let parsed = parse_compiler_stderr(
            Cursor::new(format!(
                "{}{function}\n{}{current}\n",
                trust_types::TRANSPORT_PREFIX,
                trust_types::TRANSPORT_PREFIX,
            )),
            false,
        );
        assert!(parsed.require_raw_coverage_authentication(TEST_SESSION, true).is_ok());

        let parsed = parse_compiler_stderr(
            Cursor::new(format!(
                "{}{current}\n{}{current}\n",
                trust_types::TRANSPORT_PREFIX,
                trust_types::TRANSPORT_PREFIX,
            )),
            false,
        );
        let error = parsed
            .require_raw_coverage_authentication(TEST_SESSION, true)
            .err()
            .expect("duplicate raw coverage inventories must be rejected");
        assert!(error.contains("duplicate coverage summaries"), "{error}");

        let parsed = parse_compiler_stderr(
            Cursor::new(format!(
                "{}{current}\n{}{current}\n",
                trust_types::TRANSPORT_PREFIX,
                trust_types::TRANSPORT_PREFIX,
            )),
            false,
        )
        .require_raw_coverage_authentication(TEST_SESSION, false)
        .expect("advisory mode should discard ambiguous raw coverage");
        assert!(parsed.coverage_rows.is_empty());

        let legacy = trust_types::parse_transport_payload(
            r#"{"type":"coverage_summary","crate_name":"demo","eligible":1,"processed":1,"memory":{"schema":"trust-memory-summary/v1","counters":{}}}"#,
        )
        .unwrap();
        let legacy = serde_json::to_string(&legacy).unwrap();
        let parsed = parse_compiler_stderr(
            Cursor::new(format!("{}{legacy}\n", trust_types::TRANSPORT_PREFIX)),
            false,
        );
        assert!(
            parsed.require_raw_coverage_authentication(TEST_SESSION, true).is_err(),
            "legacy raw coverage must fail closed rather than satisfy a strict gate"
        );
        let parsed = parse_compiler_stderr(
            Cursor::new(format!("{}{legacy}\n", trust_types::TRANSPORT_PREFIX)),
            false,
        )
        .require_raw_coverage_authentication(TEST_SESSION, false)
        .expect("legacy raw JSON remains advisory-compatible");
        assert!(parsed.coverage_rows.is_empty());
    }

    #[test]
    fn raw_coverage_requires_exact_function_identity_equality() {
        let exact = parse_raw_messages([
            raw_unknown_function("demo::f"),
            raw_exact_coverage(vec!["demo::f".into()], vec!["demo::f".into()]),
        ])
        .require_raw_coverage_authentication(TEST_SESSION, true)
        .expect("exact function identity inventory must authenticate");
        assert_eq!(exact.coverage_rows.len(), 1);
        assert_eq!(exact.function_envelopes.len(), 1);

        let cases = [
            (
                "substitution",
                vec![raw_unknown_function("demo::f")],
                raw_exact_coverage(vec!["demo::g".into()], vec!["demo::g".into()]),
                "did not exactly equal",
            ),
            (
                "omitted envelope identity",
                vec![raw_unknown_function("demo::f"), raw_unknown_function("demo::g")],
                raw_exact_coverage(vec!["demo::f".into()], vec!["demo::f".into()]),
                "did not exactly equal",
            ),
            (
                "duplicate function envelope",
                vec![raw_unknown_function("demo::f"), raw_unknown_function("demo::f")],
                raw_exact_coverage(vec!["demo::f".into()], vec!["demo::f".into()]),
                "duplicate function envelopes",
            ),
            (
                "duplicate coverage identity",
                vec![raw_unknown_function("demo::f")],
                raw_exact_coverage(
                    vec!["demo::f".into(), "demo::f".into()],
                    vec!["demo::f".into(), "demo::f".into()],
                ),
                "duplicated, or not canonically sorted",
            ),
        ];
        for (name, mut functions, coverage, expected) in cases {
            functions.push(coverage);
            let error = parse_raw_messages(functions)
                .require_raw_coverage_authentication(TEST_SESSION, true)
                .err()
                .unwrap_or_else(|| panic!("{name} must fail exact coverage authentication"));
            assert!(error.contains(expected), "{name}: {error}");
        }
    }

    /// 2026-10-17: the shape aterm-serde reached on the 2026-10-16 candidate gate
    /// — a body the compiler credited as processed (an uncallable
    /// `Impossible::end(self)`) with no function envelope. Strict refuses it, and
    /// advisory drops the row but RECORDS that it was emitted and why, so the
    /// report says "dropped" instead of "compiler emitted no coverage_summary".
    #[test]
    fn a_dropped_coverage_row_keeps_its_defect() {
        let messages = || {
            [
                raw_unknown_function("demo::f"),
                raw_exact_coverage(
                    vec!["demo::end".into(), "demo::f".into()],
                    vec!["demo::end".into(), "demo::f".into()],
                ),
            ]
        };
        let strict = parse_raw_messages(messages())
            .require_raw_coverage_authentication(TEST_SESSION, true)
            .err()
            .expect("a credited body without an envelope must fail strict authentication");
        assert!(strict.contains(r#"not emitted as envelopes=["demo::end"]"#), "{strict}");

        let advisory = parse_raw_messages(messages())
            .require_raw_coverage_authentication(TEST_SESSION, false)
            .expect("advisory keeps the function rows");
        assert!(advisory.coverage_rows.is_empty(), "no completeness credit");
        assert_eq!(advisory.dropped_coverage.len(), 1, "{:?}", advisory.dropped_coverage);
        assert!(
            advisory.dropped_coverage[0].contains("identity authentication failed")
                && advisory.dropped_coverage[0].contains("demo::end"),
            "{:?}",
            advisory.dropped_coverage
        );

        // NEGATIVE CONTROL: an exact inventory drops nothing, and a stream with no
        // coverage row at all records no drop (absence stays absence).
        let exact = parse_raw_messages([
            raw_unknown_function("demo::f"),
            raw_exact_coverage(vec!["demo::f".into()], vec!["demo::f".into()]),
        ])
        .require_raw_coverage_authentication(TEST_SESSION, false)
        .expect("exact inventory");
        assert_eq!(exact.coverage_rows.len(), 1);
        assert!(exact.dropped_coverage.is_empty());
        let absent = parse_raw_messages([raw_unknown_function("demo::f")])
            .require_raw_coverage_authentication(TEST_SESSION, false)
            .expect("no coverage row");
        assert!(absent.coverage_rows.is_empty() && absent.dropped_coverage.is_empty());
    }

    /// 2026-10-17: the same defect on the channel a `targo trust` run actually
    /// reads — Cargo's compiler-message envelopes, authenticated per Cargo target
    /// before the targets merge. The record survives the merge and names the
    /// target it was dropped from.
    #[test]
    fn a_dropped_cargo_target_coverage_row_keeps_its_defect_and_its_target() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected: BTreeMap<String, String> =
            [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let input = |coverage: &trust_types::TransportMessage| {
            successful_cargo_input(vec![
                cargo_transport_envelope(
                    package_id,
                    "demo",
                    &one_unknown_primary_function("demo", "demo", "demo::f"),
                ),
                cargo_transport_envelope(package_id, "demo", coverage),
                cargo_transport_envelope(
                    package_id,
                    "demo",
                    &one_unknown_primary_summary("demo", "demo"),
                ),
                cargo_artifact(package_id, "demo", false),
            ])
        };
        // `demo::end` is credited as processed and has no envelope: the shape of
        // aterm-serde's seven `Impossible::end(self)` bodies on the candidate.
        let credited_without_envelope =
            trust_types::TransportMessage::CoverageSummary(trust_types::CoverageTransportSummary {
                crate_name: "demo".to_string(),
                package_name: "demo".to_string(),
                primary_package: true,
                verification_session: TEST_SESSION.to_string(),
                eligible: 2,
                processed: 2,
                noted_stops: Vec::new(),
                degraded_anchors: 0,
                function_identities: Some(trust_types::CoverageFunctionIdentityInventory {
                    schema: trust_types::COVERAGE_FUNCTION_IDENTITY_SCHEMA_V1.to_string(),
                    eligible_functions: vec!["demo::end".to_string(), "demo::f".to_string()],
                    processed_functions: vec!["demo::end".to_string(), "demo::f".to_string()],
                }),
                memory: trust_types::MemorySummary::default(),
            });

        let strict = parse_cargo_json_stdout(
            Cursor::new(input(&credited_without_envelope)),
            &selected,
            TEST_SESSION,
            true,
        )
        .err()
        .expect("strict refuses a credited body without an envelope");
        assert!(strict.contains("identity authentication failed"), "{strict}");

        let advisory = parse_cargo_json_stdout(
            Cursor::new(input(&credited_without_envelope)),
            &selected,
            TEST_SESSION,
            false,
        )
        .expect("advisory keeps the function rows")
        .parsed;
        assert!(advisory.coverage_rows.is_empty(), "no completeness credit");
        assert_eq!(advisory.dropped_coverage.len(), 1, "{:?}", advisory.dropped_coverage);
        let dropped = &advisory.dropped_coverage[0];
        assert!(
            dropped.contains(": Trust coverage function identity authentication failed")
                && dropped.contains("demo::end")
                && !dropped.starts_with("Trust coverage"),
            "the record carries its defect behind the Cargo target's label: {dropped}"
        );

        // NEGATIVE CONTROL: the exact inventory on the same channel keeps its row
        // and records no drop.
        let exact = parse_cargo_json_stdout(
            Cursor::new(input(&complete_coverage("demo", "demo"))),
            &selected,
            TEST_SESSION,
            false,
        )
        .expect("exact inventory")
        .parsed;
        assert_eq!(exact.coverage_rows.len(), 1);
        assert!(exact.dropped_coverage.is_empty(), "{:?}", exact.dropped_coverage);
    }

    #[test]
    fn raw_coverage_rejects_inflated_counts_and_legacy_identity_schema() {
        let mut inflated = raw_exact_coverage(vec!["demo::f".into()], vec!["demo::f".into()]);
        let trust_types::TransportMessage::CoverageSummary(inflated_summary) = &mut inflated else {
            unreachable!()
        };
        inflated_summary.eligible = 100;
        inflated_summary.processed = 100;
        let error = parse_raw_messages([raw_unknown_function("demo::f"), inflated.clone()])
            .require_raw_coverage_authentication(TEST_SESSION, true)
            .err()
            .expect("one envelope plus inflated 100/100 coverage must fail");
        assert!(error.contains("counts did not equal identity cardinalities"), "{error}");

        let trust_types::TransportMessage::CoverageSummary(legacy) = &mut inflated else {
            unreachable!()
        };
        legacy.eligible = 1;
        legacy.processed = 1;
        legacy.function_identities = None;
        let strict = parse_raw_messages([raw_unknown_function("demo::f"), inflated.clone()])
            .require_raw_coverage_authentication(TEST_SESSION, true)
            .err()
            .expect("count-only current-session coverage must not satisfy strict proof coverage");
        assert!(strict.contains("count-only/legacy"), "{strict}");

        let advisory = parse_raw_messages([raw_unknown_function("demo::f"), inflated])
            .require_raw_coverage_authentication(TEST_SESSION, false)
            .expect("advisory mode may retain rows without granting coverage credit");
        assert!(advisory.coverage_rows.is_empty());
        assert_eq!(advisory.function_envelopes.len(), 1);
    }

    #[test]
    fn advisory_retains_authenticated_current_schema_coverage_shortfall() {
        let parsed = parse_raw_messages([
            raw_unknown_function("demo::f"),
            raw_exact_coverage(
                vec!["demo::f".into(), "demo::missing".into()],
                vec!["demo::f".into()],
            ),
        ])
        .require_raw_coverage_authentication(TEST_SESSION, false)
        .expect("an exact processed set plus an explicit eligible shortfall is authentic");

        assert_eq!(parsed.coverage_rows.len(), 1);
        let coverage = &parsed.coverage_rows[0];
        assert_eq!(coverage.eligible, 2);
        assert_eq!(coverage.processed, 1);
        assert!(!coverage.is_complete());
        assert_eq!(parsed.function_envelopes.len(), 1);
    }

    #[test]
    fn raw_transport_rejects_stale_function_and_terminal_rows() {
        for stale_variant in ["function", "terminal"] {
            let mut function = one_unknown_primary_function("demo", "demo", "demo::f");
            let mut terminal = one_unknown_primary_summary("demo", "demo");
            match stale_variant {
                "function" => {
                    let trust_types::TransportMessage::FunctionResult(row) = &mut function else {
                        unreachable!()
                    };
                    row.verification_session = "stale-session".to_string();
                }
                "terminal" => {
                    let trust_types::TransportMessage::CrateSummary(row) = &mut terminal else {
                        unreachable!()
                    };
                    row.verification_session = "stale-session".to_string();
                }
                _ => unreachable!(),
            }
            let input = [function, complete_coverage("demo", "demo"), terminal]
                .into_iter()
                .map(|message| {
                    format!(
                        "{}{}",
                        trust_types::TRANSPORT_PREFIX,
                        serde_json::to_string(&message).expect("serialize transport")
                    )
                })
                .collect::<Vec<_>>()
                .join("\n");

            let error = parse_compiler_stderr(Cursor::new(input), false)
                .require_raw_coverage_authentication(TEST_SESSION, true)
                .err()
                .unwrap_or_else(|| panic!("stale raw {stale_variant} row must reject"));
            assert!(error.contains(stale_variant), "{stale_variant}: {error}");
        }
    }

    #[test]
    fn same_function_path_in_same_name_lib_and_bin_keeps_target_scope() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let function = one_unknown_primary_function("demo", "demo", "demo::same");
        let summary = one_unknown_primary_summary("demo", "demo");
        let input = cargo_input_with_inventory(
            vec![
                cargo_transport_envelope_with_kind(package_id, "demo", "lib", &function),
                cargo_transport_envelope_with_kind(
                    package_id,
                    "demo",
                    "lib",
                    &complete_coverage_for("demo", "demo", "demo::same"),
                ),
                cargo_transport_envelope_with_kind(package_id, "demo", "lib", &summary),
                cargo_transport_envelope_with_kind(package_id, "demo", "bin", &function),
                cargo_transport_envelope_with_kind(
                    package_id,
                    "demo",
                    "bin",
                    &complete_coverage_for("demo", "demo", "demo::same"),
                ),
                cargo_transport_envelope_with_kind(package_id, "demo", "bin", &summary),
                cargo_artifact_with_kind(package_id, "demo", "lib", false),
                cargo_artifact_with_kind(package_id, "demo", "bin", false),
            ],
            false,
        );

        let evidence = parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true)
            .expect("parse scoped same-function Cargo evidence");
        assert_eq!(evidence.parsed.verification_results.len(), 2);
        let functions = evidence
            .parsed
            .verification_results
            .iter()
            .map(|result| result.function.as_str())
            .collect::<BTreeSet<_>>();
        assert_eq!(functions.len(), 2);
        assert!(functions.iter().any(|function| function.contains("kind=[\"lib\"]")));
        assert!(functions.iter().any(|function| function.contains("kind=[\"bin\"]")));
    }

    #[test]
    fn exact_coverage_identities_remain_isolated_across_same_name_lib_and_bin() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let function = one_unknown_primary_function("demo", "demo", "demo::f");
        let mut lib_coverage = complete_coverage("demo", "demo");
        let mut bin_coverage = complete_coverage("demo", "demo");
        for (coverage, count) in [(&mut lib_coverage, 7), (&mut bin_coverage, 11)] {
            let trust_types::TransportMessage::CoverageSummary(coverage) = coverage else {
                panic!("fixture must carry a compiler coverage summary");
            };
            coverage.memory = trust_types::MemorySummary::new([(
                trust_types::MemorySummary::SLOTS_COMPACTED.to_string(),
                count,
            )]);
        }
        let summary = one_unknown_primary_summary("demo", "demo");
        let input = cargo_input_with_inventory(
            vec![
                cargo_transport_envelope_with_kind(package_id, "demo", "lib", &function),
                cargo_transport_envelope_with_kind(package_id, "demo", "lib", &lib_coverage),
                cargo_transport_envelope_with_kind(package_id, "demo", "lib", &summary),
                cargo_transport_envelope_with_kind(package_id, "demo", "bin", &function),
                cargo_transport_envelope_with_kind(package_id, "demo", "bin", &bin_coverage),
                cargo_transport_envelope_with_kind(package_id, "demo", "bin", &summary),
                cargo_artifact_with_kind(package_id, "demo", "lib", false),
                cargo_artifact_with_kind(package_id, "demo", "bin", false),
            ],
            false,
        );

        let evidence = parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true)
            .expect("both target-local exact identity inventories must authenticate");
        assert_eq!(evidence.parsed.coverage_rows.len(), 2);
        assert_eq!(evidence.parsed.function_envelopes.len(), 2);
        let memory = serde_json::to_value(&evidence.parsed.compiler_memory_observations)
            .expect("serialize per-unit memory observations");
        let memory_by_kind = memory
            .as_array()
            .unwrap()
            .iter()
            .map(|unit| {
                (
                    unit["cargo_target"]["target_kinds"][0].as_str().unwrap(),
                    unit["memory"]["counters"][trust_types::MemorySummary::SLOTS_COMPACTED]
                        .as_u64()
                        .unwrap(),
                )
            })
            .collect::<BTreeMap<_, _>>();
        assert_eq!(memory_by_kind, [("bin", 11), ("lib", 7)].into_iter().collect());
        assert!(!memory.to_string().contains(TEST_SESSION));

        let envelope_functions = evidence
            .parsed
            .function_envelopes
            .iter()
            .map(|envelope| envelope.function.clone())
            .collect::<BTreeSet<_>>();
        let eligible_functions = evidence
            .parsed
            .coverage_rows
            .iter()
            .flat_map(|coverage| {
                coverage
                    .function_identities
                    .as_ref()
                    .expect("current exact coverage schema")
                    .eligible_functions
                    .iter()
                    .cloned()
            })
            .collect::<BTreeSet<_>>();
        let processed_functions = evidence
            .parsed
            .coverage_rows
            .iter()
            .flat_map(|coverage| {
                coverage
                    .function_identities
                    .as_ref()
                    .expect("current exact coverage schema")
                    .processed_functions
                    .iter()
                    .cloned()
            })
            .collect::<BTreeSet<_>>();
        assert_eq!(eligible_functions, envelope_functions);
        assert_eq!(processed_functions, envelope_functions);
        assert_eq!(envelope_functions.len(), 2);
        assert!(envelope_functions.iter().any(|function| function.contains("kind=[\"lib\"]")));
        assert!(envelope_functions.iter().any(|function| function.contains("kind=[\"bin\"]")));
    }

    #[test]
    fn coverage_cannot_borrow_same_named_function_envelope_from_another_target() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let function = one_unknown_primary_function("demo", "demo", "demo::f");
        let coverage = complete_coverage("demo", "demo");
        let summary = one_unknown_primary_summary("demo", "demo");
        let input = cargo_input_with_inventory(
            vec![
                // The lib emitted the only function envelope. The same textual def
                // path in the bin's coverage row must not be reconciled globally.
                cargo_transport_envelope_with_kind(package_id, "demo", "lib", &function),
                cargo_transport_envelope_with_kind(package_id, "demo", "lib", &coverage),
                cargo_transport_envelope_with_kind(package_id, "demo", "lib", &summary),
                cargo_transport_envelope_with_kind(package_id, "demo", "bin", &coverage),
                cargo_transport_envelope_with_kind(package_id, "demo", "bin", &summary),
                cargo_artifact_with_kind(package_id, "demo", "lib", false),
                cargo_artifact_with_kind(package_id, "demo", "bin", false),
            ],
            false,
        );

        let error = parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true)
            .err()
            .expect("one Cargo target must not borrow another target's function envelope");
        assert!(error.contains("did not exactly equal"), "{error}");
    }

    #[test]
    fn same_named_targets_in_distinct_package_ids_do_not_share_completion() {
        let package_id_a = "path+file:///workspace/a#demo@0.1.0";
        let package_id_b = "path+file:///workspace/b#demo@0.1.0";
        let selected = [
            (package_id_a.to_string(), "demo".to_string()),
            (package_id_b.to_string(), "demo".to_string()),
        ]
        .into_iter()
        .collect();
        let coverage_a = cargo_transport_envelope(
            package_id_a,
            "demo",
            &empty_complete_coverage("demo", "demo"),
        );
        let summary_a =
            cargo_transport_envelope(package_id_a, "demo", &empty_primary_summary("demo", "demo"));
        let artifact_a = cargo_artifact(package_id_a, "demo", false);
        let artifact_b = cargo_artifact(package_id_b, "demo", false);
        let input =
            cargo_input_with_inventory(vec![coverage_a, summary_a, artifact_a, artifact_b], false);

        let error = parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true)
            .err()
            .expect("one package's terminal summary cannot authorize another package artifact");
        assert!(error.contains("compiler-artifact before its terminal crate summary"), "{error}");
        assert!(error.contains(package_id_b), "{error}");
    }

    #[test]
    fn duplicate_artifacts_and_duplicate_root_summaries_fail() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let artifact = cargo_artifact(package_id, "demo", false);
        let coverage =
            cargo_transport_envelope(package_id, "demo", &empty_complete_coverage("demo", "demo"));
        let summary =
            cargo_transport_envelope(package_id, "demo", &empty_primary_summary("demo", "demo"));

        let duplicate_artifacts = cargo_input_with_inventory(
            vec![coverage.clone(), summary.clone(), artifact.clone(), artifact.clone()],
            false,
        );
        let artifact_error = parse_cargo_json_stdout(
            Cursor::new(duplicate_artifacts),
            &selected,
            TEST_SESSION,
            true,
        )
        .err()
        .expect("one exact proof Unit must emit exactly one compiler artifact");
        assert!(artifact_error.contains("duplicate compiler-artifact records"), "{artifact_error}");

        let duplicate_summaries =
            cargo_input_with_inventory(vec![coverage, summary.clone(), summary, artifact], false);
        let summary_error = parse_cargo_json_stdout(
            Cursor::new(duplicate_summaries),
            &selected,
            TEST_SESSION,
            true,
        )
        .err()
        .expect("two terminal summaries for one identity must fail closed");
        assert!(summary_error.contains("duplicate terminal crate summaries"), "{summary_error}");
    }

    #[test]
    fn cargo_proof_unit_lifecycles_allow_only_ordered_interleaving() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let function = one_unknown_primary_function("demo", "demo", "demo::f");
        let coverage = complete_coverage("demo", "demo");
        let summary = one_unknown_primary_summary("demo", "demo");
        let input = cargo_input_with_inventory(
            vec![
                cargo_transport_envelope_with_kind(package_id, "demo", "lib", &function),
                cargo_transport_envelope_with_kind(package_id, "demo", "bin", &function),
                cargo_transport_envelope_with_kind(package_id, "demo", "lib", &coverage),
                cargo_transport_envelope_with_kind(package_id, "demo", "bin", &coverage),
                cargo_transport_envelope_with_kind(package_id, "demo", "lib", &summary),
                cargo_transport_envelope_with_kind(package_id, "demo", "bin", &summary),
                cargo_artifact_with_kind(package_id, "demo", "lib", false),
                cargo_artifact_with_kind(package_id, "demo", "bin", false),
            ],
            true,
        );

        let evidence = parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true)
            .expect("independent Cargo proof-unit lifecycle cursors may interleave");
        assert_eq!(evidence.compiled_targets.len(), 2);
        assert_eq!(evidence.parsed.completed_proof_targets.len(), 2);
        assert_eq!(evidence.parsed.coverage_proof_targets.len(), 2);
    }

    #[test]
    fn cargo_proof_unit_lifecycle_rejects_reordering_and_post_terminal_injection() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let function = one_unknown_primary_function("demo", "demo", "demo::f");
        let coverage = complete_coverage("demo", "demo");
        let summary = one_unknown_primary_summary("demo", "demo");
        let envelope = |message: &trust_types::TransportMessage| {
            cargo_transport_envelope(package_id, "demo", message)
        };
        let artifact = cargo_artifact(package_id, "demo", false);
        let cases = [
            (
                "summary before coverage",
                vec![envelope(&summary)],
                "before the required coverage summary",
            ),
            (
                "function after coverage",
                vec![envelope(&function), envelope(&coverage), envelope(&function)],
                "function row after its coverage summary",
            ),
            (
                "duplicate coverage",
                vec![envelope(&coverage), envelope(&coverage)],
                "duplicate coverage summaries",
            ),
            (
                "coverage after summary",
                vec![envelope(&coverage), envelope(&summary), envelope(&coverage)],
                "coverage after its terminal crate summary",
            ),
            (
                "duplicate summary",
                vec![envelope(&coverage), envelope(&summary), envelope(&summary)],
                "duplicate terminal crate summaries",
            ),
            (
                "artifact before summary",
                vec![envelope(&coverage), artifact.clone()],
                "compiler-artifact before its terminal crate summary",
            ),
            (
                "transport after artifact",
                vec![envelope(&coverage), envelope(&summary), artifact, envelope(&function)],
                "transport after its compiler-artifact",
            ),
        ];

        for (label, lines, expected) in cases {
            let error = parse_cargo_json_stdout(
                Cursor::new(cargo_input_with_inventory(lines, false)),
                &selected,
                TEST_SESSION,
                true,
            )
            .err()
            .unwrap_or_else(|| panic!("{label} must fail closed"));
            assert!(error.contains(expected), "{label}: {error}");
        }
    }

    #[test]
    fn cargo_lifecycle_completion_preserves_only_explicit_advisory_and_failed_build_lanes() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let summary =
            cargo_transport_envelope(package_id, "demo", &empty_primary_summary("demo", "demo"));
        let artifact = cargo_artifact(package_id, "demo", false);

        let advisory_input =
            cargo_input_with_inventory(vec![summary.clone(), artifact.clone()], false);
        parse_cargo_json_stdout(Cursor::new(&advisory_input), &selected, TEST_SESSION, false)
            .expect("the existing advisory lane may omit an authenticated coverage inventory");
        let error =
            parse_cargo_json_stdout(Cursor::new(advisory_input), &selected, TEST_SESSION, true)
                .err()
                .expect("proof mode must require coverage even for a zero-function unit");
        assert!(error.contains("before the required coverage summary"), "{error}");

        let mut failed = cargo_input_with_inventory(
            vec![cargo_transport_envelope(
                package_id,
                "demo",
                &empty_complete_coverage("demo", "demo"),
            )],
            false,
        );
        failed.push_str("{\"reason\":\"build-finished\",\"success\":false}\n");
        let evidence = parse_cargo_json_stdout(Cursor::new(failed), &selected, TEST_SESSION, true)
            .expect("a failed build may end mid-unit so its compiler diagnostic remains primary");
        assert_eq!(evidence.build_succeeded, Some(false));
        assert!(evidence.compiled_targets.is_empty());
    }

    #[test]
    fn failed_cargo_build_retains_complete_fail_closed_terminal_protocol() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let mut input = cargo_input_with_inventory(
            vec![
                cargo_transport_envelope(
                    package_id,
                    "demo",
                    &one_unknown_primary_function("demo", "demo", "demo::f"),
                ),
                cargo_transport_envelope(package_id, "demo", &complete_coverage("demo", "demo")),
                cargo_transport_envelope(
                    package_id,
                    "demo",
                    &one_unknown_primary_summary("demo", "demo"),
                ),
            ],
            false,
        );
        input.push_str("{\"reason\":\"build-finished\",\"success\":false}\n");

        let evidence = parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true)
            .expect("a failed compiler may publish its completed diagnostic inventory");

        assert_eq!(evidence.build_succeeded, Some(false));
        assert!(evidence.compiled_targets.is_empty(), "a failed unit emits no artifact");
        assert_eq!(evidence.parsed.completed_proof_targets.len(), 1);
        assert_eq!(evidence.parsed.coverage_proof_targets.len(), 1);
        assert_eq!(evidence.parsed.verification_results.len(), 1);
        assert_eq!(evidence.parsed.verification_results[0].outcome, VerificationOutcome::Unknown);
        assert!(
            evidence
                .parsed
                .verification_results
                .iter()
                .all(|row| !row.kind.starts_with("transport:"))
        );
        let error = evidence
            .require_successful_selected_roots(&selected, true)
            .expect_err("diagnostic transport must not convert a failed build into proof success");
        assert!(error.contains("unsuccessful build-finished status"), "{error}");
    }

    #[test]
    fn raw_compiler_transport_ordering_is_reported_without_losing_human_diagnostics() {
        let function = one_unknown_primary_function("demo", "demo", "demo::f");
        let coverage = complete_coverage("demo", "demo");
        let summary = one_unknown_primary_summary("demo", "demo");
        let input = format!(
            "{}{}\n{}{}\nwarning: keep this diagnostic\n{}{}\n{}{}\n",
            trust_types::TRANSPORT_PREFIX,
            serde_json::to_string(&function).unwrap(),
            trust_types::TRANSPORT_PREFIX,
            serde_json::to_string(&coverage).unwrap(),
            trust_types::TRANSPORT_PREFIX,
            serde_json::to_string(&function).unwrap(),
            trust_types::TRANSPORT_PREFIX,
            serde_json::to_string(&summary).unwrap(),
        );

        let parsed = parse_compiler_stderr(Cursor::new(input), false);
        assert!(!parsed.raw_terminal_inventory_complete());
        assert!(parsed.verification_results.iter().any(|row| {
            row.kind == "transport:ordering"
                && row
                    .reason
                    .as_deref()
                    .is_some_and(|reason| reason.contains("function row after coverage"))
        }));
        assert_eq!(parsed.compiler_diagnostics.len(), 1);
        assert!(parsed.compiler_diagnostics[0].message.contains("keep this diagnostic"));
        let error = parsed
            .require_raw_coverage_authentication(TEST_SESSION, true)
            .err()
            .expect("raw proof authentication must reject lifecycle defects");
        assert!(error.contains("lifecycle violation"), "{error}");
    }

    #[test]
    fn cargo_transport_rejects_untagged_scope_mismatch_and_fresh_artifacts() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();

        let mut untagged =
            cargo_transport_envelope(package_id, "demo", &empty_primary_summary("demo", "demo"));
        untagged["message"]["code"] = serde_json::Value::Null;
        assert!(
            parse_cargo_json_stdout(
                Cursor::new(format!("{untagged}\n")),
                &selected,
                TEST_SESSION,
                true,
            )
            .is_err()
        );

        let wrong_scope = cargo_transport_envelope(
            package_id,
            "demo",
            &empty_primary_summary("another-package", "demo"),
        );
        assert!(
            parse_cargo_json_stdout(
                Cursor::new(format!("{wrong_scope}\n")),
                &selected,
                TEST_SESSION,
                true,
            )
            .is_err()
        );
        assert!(
            parse_cargo_json_stdout(
                Cursor::new(format!("{wrong_scope}\n")),
                &selected,
                TEST_SESSION,
                false,
            )
            .is_err(),
            "advisory coverage compatibility must not weaken function/crate envelope authentication"
        );

        let fresh = cargo_artifact(package_id, "demo", true);
        let error = parse_cargo_json_stdout(
            Cursor::new(format!("{fresh}\n")),
            &selected,
            TEST_SESSION,
            true,
        )
        .err()
        .expect("fresh=true cannot authenticate a verifier run");
        assert!(error.contains("was fresh"), "{error}");

        for invalid_fresh in [None, Some(serde_json::Value::Null), Some(serde_json::json!("false"))]
        {
            let mut artifact = cargo_artifact(package_id, "demo", false);
            match invalid_fresh {
                Some(value) => artifact["fresh"] = value,
                None => {
                    artifact.as_object_mut().unwrap().remove("fresh");
                }
            }
            let error = parse_cargo_json_stdout(
                Cursor::new(format!("{artifact}\n")),
                &selected,
                TEST_SESSION,
                true,
            )
            .err()
            .expect("compiler-artifact freshness must be explicit false");
            assert!(error.contains("required fresh=false observation"), "{error}");
        }
    }

    #[test]
    fn excluded_artifact_freshness_is_not_misclassified_as_proof_freshness() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let mut lines = Vec::new();
        append_complete_proof_unit(
            &mut lines, package_id, "demo", "demo", "lib", 91, "build", "primary", true,
        );
        let mut values = successful_cargo_input(lines)
            .lines()
            .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
            .collect::<Vec<_>>();
        let mut excluded = serde_json::json!({
            "index": 1,
            "mode": "doc",
            "package_id": package_id,
            "package_name": "demo",
            "target_name": "demo-doc",
            "target_kinds": ["lib"],
            "compile_target": TEST_COMPILE_TARGET,
            "exclusion_reason": TARGO_TRUST_EXCLUSION_DOCUMENTATION,
            "graph_role": "primary",
        });
        set_excluded_unit_semantics(&mut excluded, "doc");
        values[0]["excluded_units"] = serde_json::json!([excluded]);
        let mut excluded_artifact = cargo_artifact(package_id, "demo-doc", true);
        excluded_artifact.as_object_mut().unwrap().remove("trust_proof_unit");
        values.insert(values.len() - 1, excluded_artifact);

        parse_cargo_json_stdout(
            Cursor::new(values.iter().map(|line| format!("{line}\n")).collect::<String>()),
            &selected,
            TEST_SESSION,
            true,
        )
        .expect("fresh excluded rustdoc artifacts carry no proof-unit freshness claim");
    }

    #[test]
    fn duplicate_proof_unit_compiler_artifact_is_rejected() {
        let package_id = "path+file:///fixture#demo@0.1.0";
        let selected = [(package_id.to_string(), "demo".to_string())].into_iter().collect();
        let mut lines = Vec::new();
        append_complete_proof_unit(
            &mut lines, package_id, "demo", "demo", "lib", 92, "build", "primary", true,
        );
        let mut values = successful_cargo_input(lines)
            .lines()
            .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
            .collect::<Vec<_>>();
        let artifact = values
            .iter()
            .find(|line| {
                line.get("reason").and_then(serde_json::Value::as_str) == Some("compiler-artifact")
            })
            .expect("fixture artifact")
            .clone();
        values.insert(values.len() - 1, artifact);
        let input = values.iter().map(|line| format!("{line}\n")).collect::<String>();
        let error = parse_cargo_json_stdout(Cursor::new(input), &selected, TEST_SESSION, true)
            .err()
            .expect("artifact multiplicity must remain authenticated");
        assert!(error.contains("duplicate compiler-artifact records"), "{error}");
    }

    #[test]
    fn raw_cargo_stderr_cannot_forge_transport() {
        let forged = format!(
            "{}{}\nwarning: ordinary diagnostic\n",
            trust_types::TRANSPORT_PREFIX,
            serde_json::to_string(&empty_primary_summary("demo", "demo")).unwrap()
        );
        let diagnostics = parse_untrusted_cargo_stderr(Cursor::new(forged), false);
        assert_eq!(diagnostics.len(), 1);
        assert!(!diagnostics[0].message.contains(trust_types::TRANSPORT_PREFIX));
    }

    fn transport_row(outcome: trust_types::Outcome) -> trust_types::TransportObligationResult {
        trust_types::TransportObligationResult {
            assumes: Vec::new(),
            gap_class: None,
            obligation_id: None,
            claim_digest_sha256: None,
            kind: "assertion".to_string(),
            original_vc_snapshot: None,
            typed_kind: None,
            description: "assertion holds".to_string(),
            location: None,
            outcome,
            solver: "ay-smtlib".to_string(),
            time_ms: 10,
            counterexample: None,
            counterexample_model: None,
            reason: None,
            design_mandate: false,
            native_trust_ir: None,
            proof_evidence: None,
            monitor: None,
            grade: None,
        }
    }

    fn verification_rows(
        function: &str,
        transport_rows: &[trust_types::TransportObligationResult],
    ) -> Vec<VerificationResult> {
        transport_rows
            .iter()
            .map(|row| transport_to_verification_result(function, row, None, None))
            .collect()
    }

    /// Trust (CB4): the one row the compiler writes for an excluded harness
    /// body, as it crosses the wire.
    fn exclusion_transport_row() -> trust_types::TransportObligationResult {
        trust_types::TransportObligationResult {
            assumes: Vec::new(),
            kind: trust_types::exclusion::TEST_HARNESS_ROW_KIND.to_string(),
            description: trust_types::exclusion::TEST_HARNESS_ROW_DESCRIPTION.to_string(),
            solver: trust_types::exclusion::TEST_HARNESS_ROW_SOLVER.to_string(),
            time_ms: 0,
            reason: trust_types::exclusion::test_harness_exclusion_reason(
                trust_types::exclusion::TestHarnessExclusionItem::HarnessMain,
                None,
            ),
            ..transport_row(trust_types::Outcome::Skipped)
        }
    }

    #[test]
    fn a_lone_exclusion_row_keeps_its_exact_reason() {
        let mut rows = verification_rows("crate::main", &[exclusion_transport_row()]);
        let before = rows[0].reason.clone();
        refuse_shared_test_harness_exclusion_envelope(&mut rows);
        assert_eq!(rows[0].reason, before);
        assert!(trust_types::exclusion::is_exact_test_harness_exclusion_row(
            &rows[0].kind,
            &rows[0].backend,
            &rows[0].message,
            rows[0].reason.as_deref(),
        ));
    }

    #[test]
    fn an_exclusion_row_sharing_its_envelope_is_refused() {
        let mut rows = verification_rows(
            "crate::main",
            &[exclusion_transport_row(), transport_row(trust_types::Outcome::Proved)],
        );
        let sibling = serde_json::to_string(&rows[1]).expect("row serializes");
        refuse_shared_test_harness_exclusion_envelope(&mut rows);
        assert_eq!(rows[0].reason.as_deref(), Some(SHARED_EXCLUSION_ENVELOPE_DEFECT));
        assert!(!trust_types::exclusion::is_exact_test_harness_exclusion_row(
            &rows[0].kind,
            &rows[0].backend,
            &rows[0].message,
            rows[0].reason.as_deref(),
        ));
        assert_eq!(
            serde_json::to_string(&rows[1]).expect("row serializes"),
            sibling,
            "the sibling row is left exactly as it arrived"
        );
    }

    #[test]
    fn function_summary_accepts_legacy_timeout_in_unknown_aggregate() {
        let func_result = trust_types::FunctionTransportResult {
            stable_ids: Vec::new(),
            source_sha256: None,
            expanded_function_identity: None,
            modeled_facts: Vec::new(),
            function: "crate::timeout_case".to_string(),
            package_name: None,
            crate_name: None,
            primary_package: false,
            verification_session: String::new(),
            runtime_checks: None,
            results: vec![transport_row(trust_types::Outcome::Timeout)],
            proved: 0,
            failed: 0,
            unknown: 1,
            timed_out: 0,
            skipped: 0,
            runtime_checked: 0,
            cached: 0,
            total: 1,
            transport_budget: None,
        };
        let rows = verification_rows(&func_result.function, &func_result.results);

        assert_eq!(function_transport_summary_defect(&func_result, &rows), None);
    }

    #[test]
    fn function_summary_defect_compares_timeout_and_skipped_splits() {
        let func_result = trust_types::FunctionTransportResult {
            stable_ids: Vec::new(),
            source_sha256: None,
            expanded_function_identity: None,
            modeled_facts: Vec::new(),
            function: "crate::split_case".to_string(),
            package_name: None,
            crate_name: None,
            primary_package: false,
            verification_session: String::new(),
            runtime_checks: None,
            results: vec![
                transport_row(trust_types::Outcome::Timeout),
                transport_row(trust_types::Outcome::Skipped),
            ],
            proved: 0,
            failed: 0,
            unknown: 2,
            timed_out: 2,
            skipped: 2,
            runtime_checked: 0,
            cached: 0,
            total: 2,
            transport_budget: None,
        };
        let rows = verification_rows(&func_result.function, &func_result.results);

        let reason =
            function_transport_summary_defect(&func_result, &rows).expect("split mismatch");

        assert!(reason.contains("timed_out rows=1 summary=2"), "{reason}");
        assert!(reason.contains("skipped rows=1 summary=2"), "{reason}");
        assert!(!reason.contains("unknown rows="), "{reason}");
    }

    fn normalized_row(outcome: VerificationOutcome) -> VerificationResult {
        VerificationResult {
            function: "crate::reclassified".to_string(),
            kind: "assertion".to_string(),
            message: "assertion".to_string(),
            outcome,
            backend: "trust-full-verifier".to_string(),
            time_ms: None,
            location: None,
            counterexample: None,
            reason: None,
            raw_line: String::new(),
        }
    }

    #[test]
    fn function_summary_accepts_full_verifier_failed_and_proved_reclassification() {
        // The compiler summary counts the RAW outcomes (`failed`, `proved`), but
        // targo normalizes full-verifier rows lacking proof evidence: `failed` ->
        // Unknown and `proved` (with failed/unsupported evidence) -> Failed. The
        // accounting check must treat both as targo's own normalization, not a
        // phantom mismatch. Regression for the narrow `proved`/`runtime_checked`
        // -> Unknown fix that missed `failed` -> Unknown and `proved` -> Failed
        // (observed live on examples/midpoint.rs and full_verifier_three_suite.rs).
        let func_result = trust_types::FunctionTransportResult {
            stable_ids: Vec::new(),
            source_sha256: None,
            expanded_function_identity: None,
            modeled_facts: Vec::new(),
            function: "crate::reclassified".to_string(),
            package_name: None,
            crate_name: None,
            primary_package: false,
            verification_session: String::new(),
            runtime_checks: None,
            results: vec![
                transport_row(trust_types::Outcome::Failed),
                transport_row(trust_types::Outcome::Proved),
            ],
            proved: 1,
            failed: 1,
            unknown: 0,
            timed_out: 0,
            skipped: 0,
            runtime_checked: 0,
            cached: 0,
            total: 2,
            transport_budget: None,
        };
        let rows = vec![
            normalized_row(VerificationOutcome::Unknown),
            normalized_row(VerificationOutcome::Failed),
        ];

        assert_eq!(function_transport_summary_defect(&func_result, &rows), None);
    }

    #[test]
    fn function_summary_still_flags_genuine_miscount_under_reclassification() {
        // The reclassification floor must not mask a real compiler miscount: here
        // the summary claims two `proved` but only one row exists, and that row
        // normalizes to Unknown. The single proved->Unknown shift is absorbed, yet
        // the leftover `proved` over-count still surfaces a defect.
        let func_result = trust_types::FunctionTransportResult {
            stable_ids: Vec::new(),
            source_sha256: None,
            expanded_function_identity: None,
            modeled_facts: Vec::new(),
            function: "crate::miscount".to_string(),
            package_name: None,
            crate_name: None,
            primary_package: false,
            verification_session: String::new(),
            runtime_checks: None,
            results: vec![transport_row(trust_types::Outcome::Proved)],
            proved: 2,
            failed: 0,
            unknown: 0,
            timed_out: 0,
            skipped: 0,
            runtime_checked: 0,
            cached: 0,
            total: 1,
            transport_budget: None,
        };
        let rows = vec![normalized_row(VerificationOutcome::Unknown)];

        let reason = function_transport_summary_defect(&func_result, &rows)
            .expect("genuine miscount must still be flagged");
        assert!(reason.contains("proved rows=0 summary=1"), "{reason}");
    }

    #[test]
    fn crate_summary_uses_raw_failed_and_unknown_buckets_across_normalization() {
        let full_verifier_row =
            |outcome: trust_types::Outcome, status: trust_types::TransportProofStatus| {
                let mut row = transport_row(outcome);
                row.solver = "trust-full-verifier".to_string();
                row.proof_evidence = Some(trust_types::TransportProofEvidence {
                    suite: "trust-wp".to_string(),
                    backend: "trust-full-verifier".to_string(),
                    request_id: Some(format!("request-{outcome}")),
                    proof_id: Some(format!("proof-{outcome}")),
                    native_id: None,
                    status,
                    strength: None,
                    evidence: None,
                    artifacts: Vec::new(),
                    diagnostics: Vec::new(),
                });
                row
            };
        // These intentionally cross buckets in Targo's report projection:
        // raw failed + Proved evidence is conservatively Unknown, while raw
        // proved + Failed evidence is Failed. The compiler terminal summary
        // still (correctly) reports its raw proved=1, failed=1, unknown=0.
        let function =
            trust_types::TransportMessage::FunctionResult(trust_types::FunctionTransportResult {
                stable_ids: Vec::new(),
                source_sha256: None,
                expanded_function_identity: None,
                modeled_facts: Vec::new(),
                function: "demo::reclassified".to_string(),
                package_name: Some("demo".to_string()),
                crate_name: Some("demo".to_string()),
                primary_package: true,
                verification_session: TEST_SESSION.to_string(),
                runtime_checks: None,
                results: vec![
                    full_verifier_row(
                        trust_types::Outcome::Failed,
                        trust_types::TransportProofStatus::Proved,
                    ),
                    full_verifier_row(
                        trust_types::Outcome::Proved,
                        trust_types::TransportProofStatus::Failed,
                    ),
                ],
                proved: 1,
                failed: 1,
                unknown: 0,
                timed_out: 0,
                skipped: 0,
                runtime_checked: 0,
                cached: 0,
                total: 2,
                transport_budget: None,
            });
        let summary = trust_types::CrateTransportSummary {
            crate_name: "demo".to_string(),
            package_name: Some("demo".to_string()),
            primary_package: true,
            verification_session: TEST_SESSION.to_string(),
            functions_analyzed: 1,
            functions_verified: 0,
            total_proved: 1,
            total_failed: 1,
            total_unknown: 0,
            total_timed_out: 0,
            total_skipped: 0,
            total_runtime_checked: 0,
            total_obligations: 2,
        };

        let parsed = parse_raw_messages([
            function.clone(),
            trust_types::TransportMessage::CrateSummary(summary.clone()),
        ]);
        assert_eq!(
            parsed.verification_results.iter().map(|row| row.outcome).collect::<Vec<_>>(),
            [VerificationOutcome::Unknown, VerificationOutcome::Failed]
        );
        assert!(
            parsed.verification_results.iter().all(|row| !row.kind.starts_with("transport:")),
            "Targo's own normalization must not create an accounting defect: {:?}",
            parsed.verification_results
        );

        let mut normalized_counts_forgery = summary;
        normalized_counts_forgery.total_proved = 0;
        normalized_counts_forgery.total_unknown = 1;
        let parsed = parse_raw_messages([
            function,
            trust_types::TransportMessage::CrateSummary(normalized_counts_forgery),
        ]);
        let defect = parsed
            .verification_results
            .iter()
            .find(|row| row.kind == "transport:crate-summary-accounting")
            .expect("genuine raw terminal counter drift must remain fail-closed");
        let reason = defect.reason.as_deref().expect("accounting defect reason");
        assert!(reason.contains("proved rows=1 summary=0"), "{reason}");
        assert!(reason.contains("unknown rows=0 summary=1"), "{reason}");
    }

    #[test]
    fn crate_summary_defect_compares_timeout_and_skipped_splits() {
        let observed = CrateTransportCounts {
            functions_analyzed: 1,
            functions_verified: 0,
            obligations: FunctionTransportCounts {
                unknown: 2,
                timed_out: 1,
                skipped: 1,
                total: 2,
                ..FunctionTransportCounts::default()
            },
        };
        let summary = trust_types::CrateTransportSummary {
            crate_name: "demo".to_string(),
            package_name: None,
            primary_package: false,
            verification_session: String::new(),
            functions_analyzed: 1,
            functions_verified: 0,
            total_proved: 0,
            total_failed: 0,
            total_unknown: 2,
            total_timed_out: 2,
            total_skipped: 2,
            total_runtime_checked: 0,
            total_obligations: 2,
        };

        let reason = crate_transport_summary_defect(&summary, &observed).expect("split mismatch");

        assert!(reason.contains("timed_out rows=1 summary=2"), "{reason}");
        assert!(reason.contains("skipped rows=1 summary=2"), "{reason}");
        assert!(!reason.contains("unknown rows="), "{reason}");
    }

    #[test]
    fn crate_summary_distinguishes_analyzed_from_fully_verified_functions() {
        let observed = CrateTransportCounts {
            functions_analyzed: 1,
            functions_verified: 0,
            obligations: FunctionTransportCounts {
                unknown: 1,
                total: 1,
                ..FunctionTransportCounts::default()
            },
        };
        let mut summary = trust_types::CrateTransportSummary {
            crate_name: "demo".to_string(),
            package_name: None,
            primary_package: false,
            verification_session: String::new(),
            functions_analyzed: 1,
            functions_verified: 1,
            total_proved: 0,
            total_failed: 0,
            total_unknown: 1,
            total_timed_out: 0,
            total_skipped: 0,
            total_runtime_checked: 0,
            total_obligations: 1,
        };

        let reason = crate_transport_summary_defect(&summary, &observed)
            .expect("unknown function cannot be declared verified");
        assert!(reason.contains("functions_verified rows=0 summary=1"), "{reason}");

        summary.functions_verified = 0;
        summary.functions_analyzed = 0;
        let reason = crate_transport_summary_defect(&summary, &observed)
            .expect("every emitted function row must be counted as analyzed");
        assert!(reason.contains("functions_analyzed rows=1 summary=0"), "{reason}");
    }

    // -----------------------------------------------------------------------
    // Trust (OD-1 phase 1; 2026-10-12): the compiler counts a `proved`
    // instance-discharge row `skipped`, and this reconciler must count it the
    // same way. The three tests below read the compiler's own bytes.
    // -----------------------------------------------------------------------

    /// Verbatim transport of bare `trustc` — the stage 1 of the T3 L4 merge `fd4cee44ece`
    /// (recaptured 2026-10-21; first captured on trust main `5a2d23c537`), run in
    /// `tests/fixtures/instance-discharge` as `trustc
    /// --edition 2024 --crate-type=lib --crate-name
    /// trust_instance_discharge_fixture --emit=metadata -Ztrust-verify=on
    /// -Ztrust-verify-output=both -Ztrust-policy=advisory src/lib.rs` (the flags
    /// of `tests/ui/trust/instance_hypothesis/discharge_row_per_instance.rs`,
    /// advisory revision) — reduced to the `TRUST_JSON:` lines of its stderr:
    /// three function envelopes, the coverage summary (with its `memory` summary), the crate
    /// summary.
    ///
    /// `use_good` names the instance `f::<Good>`. Its envelope carries two rows,
    /// BOTH with outcome `proved` — its panic-freedom assertion and the
    /// instance-discharge row — and declares `proved: 1, unknown: 1, skipped: 1,
    /// total: 2`: the compiler's tally (`PublishedRowTally::of`) counts a
    /// `proved` discharge row "assumed (instance discharge)", which
    /// `json_counts` folds into `skipped` and so into `unknown`, never into
    /// `proved`. The crate summary sums the same counters.
    const INSTANCE_DISCHARGE_PROVED_TRANSPORT: &str =
        include_str!("../fixtures/instance_discharge_proved_transport.jsonl");

    fn instance_discharge_messages() -> Vec<trust_types::TransportMessage> {
        let messages: Vec<_> = INSTANCE_DISCHARGE_PROVED_TRANSPORT
            .lines()
            .map(|line| {
                trust_types::parse_transport_line(line)
                    .unwrap_or_else(|| panic!("the pinned transport line must parse: {line:.120}"))
            })
            .collect();
        assert_eq!(messages.len(), 5, "three functions, one coverage summary, one crate summary");
        messages
    }

    fn instance_discharge_envelopes() -> Vec<trust_types::FunctionTransportResult> {
        instance_discharge_messages()
            .into_iter()
            .filter_map(|message| match message {
                trust_types::TransportMessage::FunctionResult(envelope) => Some(envelope),
                _ => None,
            })
            .collect()
    }

    fn instance_discharge_crate_summary() -> trust_types::CrateTransportSummary {
        instance_discharge_messages()
            .into_iter()
            .find_map(|message| match message {
                trust_types::TransportMessage::CrateSummary(summary) => Some(summary),
                _ => None,
            })
            .expect("the pinned transport ends with its crate summary")
    }

    /// The compiler's own test for the row its tally sets aside.
    fn is_proved_instance_discharge(row: &trust_types::TransportObligationResult) -> bool {
        row.outcome.is_proved()
            && trust_types::assumption::is_instance_hypothesis_discharge_row(&row.kind, &row.solver)
    }

    /// `use_good`'s envelope and the index of its discharge row.
    fn proved_instance_discharge_envelope() -> (trust_types::FunctionTransportResult, usize) {
        let mut carriers = instance_discharge_envelopes()
            .into_iter()
            .filter(|envelope| envelope.results.iter().any(is_proved_instance_discharge));
        let envelope = carriers.next().expect("the pinned transport has a proved discharge row");
        assert!(carriers.next().is_none(), "one instance, so one discharge row");
        let index = envelope
            .results
            .iter()
            .position(is_proved_instance_discharge)
            .expect("the carrier has the row");
        (envelope, index)
    }

    /// The report rows `parse_compiler_stderr` builds for one envelope.
    fn pipeline_rows(envelope: &trust_types::FunctionTransportResult) -> Vec<VerificationResult> {
        let identities = crate::types::envelope_identities(envelope);
        envelope
            .results
            .iter()
            .zip(identities)
            .map(|(row, identity)| {
                transport_to_verification_result(
                    &envelope.function,
                    row,
                    envelope.runtime_checks,
                    identity,
                )
            })
            .collect()
    }

    /// `[proved, failed, unknown, timed_out, skipped, runtime_checked, total]`.
    fn tally(counts: &FunctionTransportCounts) -> [usize; 7] {
        [
            counts.proved,
            counts.failed,
            counts.unknown,
            counts.timed_out,
            counts.skipped,
            counts.runtime_checked,
            counts.total,
        ]
    }

    /// The envelope's declared counters, in [`tally`]'s order.
    fn declared(envelope: &trust_types::FunctionTransportResult) -> [usize; 7] {
        [
            envelope.proved,
            envelope.failed,
            envelope.unknown,
            envelope.timed_out,
            envelope.skipped,
            envelope.runtime_checked,
            envelope.total,
        ]
    }

    fn with_declared(
        envelope: &trust_types::FunctionTransportResult,
        counters: [usize; 7],
    ) -> trust_types::FunctionTransportResult {
        let [proved, failed, unknown, timed_out, skipped, runtime_checked, total] = counters;
        trust_types::FunctionTransportResult {
            proved,
            failed,
            unknown,
            timed_out,
            skipped,
            runtime_checked,
            total,
            ..envelope.clone()
        }
    }

    /// The accounting rows of a parsed transport: `(kind, reason)`.
    fn accounting_rows(parsed: &ParsedCompilerOutput) -> Vec<(String, String)> {
        parsed
            .verification_results
            .iter()
            .filter(|row| row.kind.starts_with("transport:"))
            .map(|row| (row.kind.clone(), row.reason.clone().unwrap_or_default()))
            .collect()
    }

    /// What the compiler declares for `use_good`: the discharge row is in
    /// `skipped` and `unknown`, the assertion alone is `proved`.
    const DISCHARGE_TALLY: [usize; 7] = [1, 0, 1, 0, 1, 0, 2];

    /// `add_transport_result_counts` and the per-function check it feeds: the
    /// compiler's real envelope reconciles; every lookalike is counted by its
    /// outcome, as before and as the compiler counts it; a real miscount is
    /// still a defect.
    #[test]
    fn function_summary_counts_a_proved_instance_discharge_row_as_the_compiler_does() {
        let (envelope, discharge) = proved_instance_discharge_envelope();
        // The case, exactly as the compiler wrote it.
        assert_eq!(envelope.results.len(), 2);
        assert!(envelope.results.iter().all(|row| row.outcome.is_proved()), "both travel proved");
        assert_eq!(declared(&envelope), DISCHARGE_TALLY);

        let rows = pipeline_rows(&envelope);
        let mut observed = FunctionTransportCounts::default();
        add_transport_result_counts(&mut observed, &envelope.results, &rows);
        assert_eq!(
            tally(&observed),
            DISCHARGE_TALLY,
            "a proved instance-discharge row is tallied unknown + skipped, never proved"
        );
        assert_eq!(function_transport_summary_defect(&envelope, &rows), None);
        // Every envelope of the pinned transport reconciles.
        for envelope in instance_discharge_envelopes() {
            assert_eq!(
                function_transport_summary_defect(&envelope, &pipeline_rows(&envelope)),
                None,
                "{}",
                envelope.function
            );
        }

        // Lookalikes: the discharge row with one thing changed. The third field
        // is what the compiler's tally declares for the assertion plus that row.
        let lookalike = |edit: &dyn Fn(&mut trust_types::TransportObligationResult)| {
            let mut envelope = envelope.clone();
            edit(&mut envelope.results[discharge]);
            assert!(!is_proved_instance_discharge(&envelope.results[discharge]));
            envelope
        };
        let cases: [(&str, trust_types::FunctionTransportResult, [usize; 7]); 9] = [
            (
                "the kind from the SMT solver",
                lookalike(&|row| row.solver = "ay-smtlib".to_string()),
                [2, 0, 0, 0, 0, 0, 2],
            ),
            (
                "the kind from the full verifier",
                lookalike(&|row| row.solver = "trust-full-verifier".to_string()),
                [2, 0, 0, 0, 0, 0, 2],
            ),
            (
                "another kind from the classifier",
                lookalike(&|row| row.kind = "assert".to_string()),
                [2, 0, 0, 0, 0, 0, 2],
            ),
            (
                "the hypothesis kind claiming proof",
                lookalike(&|row| row.kind = "assumption:instance-hypothesis".to_string()),
                [2, 0, 0, 0, 0, 0, 2],
            ),
            (
                "a failed discharge",
                lookalike(&|row| row.outcome = trust_types::Outcome::Failed),
                [1, 1, 0, 0, 0, 0, 2],
            ),
            (
                "an unknown discharge",
                lookalike(&|row| row.outcome = trust_types::Outcome::Unknown),
                [1, 0, 1, 0, 0, 0, 2],
            ),
            (
                "a runtime-checked discharge",
                lookalike(&|row| row.outcome = trust_types::Outcome::RuntimeChecked),
                [1, 0, 0, 0, 0, 1, 2],
            ),
            (
                "a timed-out discharge",
                lookalike(&|row| row.outcome = trust_types::Outcome::Timeout),
                [1, 0, 1, 1, 0, 0, 2],
            ),
            (
                "a skipped discharge",
                lookalike(&|row| row.outcome = trust_types::Outcome::Skipped),
                DISCHARGE_TALLY,
            ),
        ];
        for (name, case, counted) in &cases {
            let rows = pipeline_rows(case);
            // Accepted under the counters the compiler would declare for it.
            assert_eq!(
                function_transport_summary_defect(&with_declared(case, *counted), &rows),
                None,
                "{name}"
            );
            let mut observed = FunctionTransportCounts::default();
            add_transport_result_counts(&mut observed, &case.results, &rows);
            if *counted == DISCHARGE_TALLY {
                // A raw `skipped` row: unknown + skipped, as it always was.
                assert_eq!(tally(&observed), DISCHARGE_TALLY, "{name}");
                continue;
            }
            // Counted by its report outcome, as every row but a raw `skipped`
            // one was before; never as a skipped row, and never accepted
            // under the proved-discharge tally.
            let mut by_outcome =
                FunctionTransportCounts { total: rows.len(), ..FunctionTransportCounts::default() };
            for row in &rows {
                add_verification_result_count(&mut by_outcome, row);
            }
            assert_eq!(tally(&observed), tally(&by_outcome), "{name}: counted by its outcome");
            assert_eq!(observed.skipped, 0, "{name}");
            assert!(
                function_transport_summary_defect(case, &rows).is_some(),
                "{name}: must not be counted as a proved instance discharge"
            );
        }

        // Real miscounts over the compiler's real rows are still defects. A
        // producer that counts the discharge row as proof (the compiler's tally
        // before 79212a4c78, and the only one this reconciler used to accept):
        let reason = function_transport_summary_defect(
            &with_declared(&envelope, [2, 0, 0, 0, 0, 0, 2]),
            &rows,
        )
        .expect("a discharge row counted as proof is a miscount");
        assert!(reason.contains("proved rows=1 summary=2"), "{reason}");
        assert!(reason.contains("unknown rows=1 summary=0"), "{reason}");
        assert!(reason.contains("skipped rows=1 summary=0"), "{reason}");
        // One proof too many, one row too many, a failure nobody published, a
        // skip nobody published:
        for (counters, expected) in [
            ([2, 0, 1, 0, 1, 0, 2], "proved rows=1 summary=2"),
            ([1, 0, 1, 0, 1, 0, 3], "total rows=2 summary=3"),
            ([1, 1, 1, 0, 1, 0, 2], "failed rows=0 summary=1"),
            ([1, 0, 2, 0, 2, 0, 2], "skipped rows=1 summary=2"),
        ] {
            let reason =
                function_transport_summary_defect(&with_declared(&envelope, counters), &rows)
                    .unwrap_or_else(|| panic!("{counters:?} is a miscount"));
            assert!(reason.contains(expected), "{counters:?}: {reason}");
        }
        // The discharge row withheld while the counters still count it:
        let mut withheld = envelope.clone();
        withheld.results.remove(discharge);
        withheld.stable_ids.remove(discharge);
        let reason = function_transport_summary_defect(&withheld, &pipeline_rows(&withheld))
            .expect("a counted row that was not published is a miscount");
        assert!(reason.contains("total rows=1 summary=2"), "{reason}");
        assert!(reason.contains("unknown rows=0 summary=1"), "{reason}");
    }

    /// `add_raw_transport_result_counts` (through `raw_transport_bucket`) and
    /// the crate-summary check it feeds, over the whole pinned transport as
    /// `parse_compiler_stderr` reads it: no accounting row, every row keyed, a
    /// unit that is not could-not-run.
    #[test]
    fn crate_summary_counts_a_proved_instance_discharge_row_as_the_compiler_does() {
        let summary = instance_discharge_crate_summary();
        let declared_totals = [
            summary.total_proved,
            summary.total_failed,
            summary.total_unknown,
            summary.total_timed_out,
            summary.total_skipped,
            summary.total_runtime_checked,
            summary.total_obligations,
        ];
        assert_eq!(declared_totals, [2, 0, 4, 0, 4, 0, 6], "the compiler's own crate summary");
        let mut observed = FunctionTransportCounts::default();
        for envelope in instance_discharge_envelopes() {
            add_raw_transport_result_counts(&mut observed, &envelope.results);
        }
        assert_eq!(tally(&observed), declared_totals);

        let parsed = parse_compiler_stderr(Cursor::new(INSTANCE_DISCHARGE_PROVED_TRANSPORT), false);
        let defects = accounting_rows(&parsed);
        assert!(defects.is_empty(), "the compiler's real transport is no defect: {defects:?}");
        assert_eq!(parsed.verification_results.len(), 6, "the six rows the compiler published");
        // T9: a keyless row makes the unit could-not-run. Every compiler row is
        // keyed, and no synthesized row is left to be keyless.
        let unit =
            crate::determinism_report::UnitDeterminism::of_rows(&parsed.verification_results, &[]);
        assert_eq!(unit.unkeyed_functions, Vec::<String>::new());
        assert_eq!(unit.could_not_run_line(), None);

        // The pinned transport with one thing changed, re-read whole.
        let reread = |edit: &dyn Fn(&mut trust_types::TransportMessage)| {
            let mut messages = instance_discharge_messages();
            for message in &mut messages {
                edit(message);
            }
            parse_raw_messages(messages)
        };
        // A lookalike (the kind from another solver) under the compiler's
        // counters: a raw `proved` row those counters do not count `proved`, in
        // its function and in its crate.
        let other_solver = |message: &mut trust_types::TransportMessage| {
            if let trust_types::TransportMessage::FunctionResult(envelope) = message {
                for row in &mut envelope.results {
                    if is_proved_instance_discharge(row) {
                        row.solver = "ay-smtlib".to_string();
                    }
                }
            }
        };
        let defects = accounting_rows(&reread(&other_solver));
        assert_eq!(
            defects.iter().map(|(kind, _)| kind.as_str()).collect::<Vec<_>>(),
            ["transport:summary-accounting", "transport:crate-summary-accounting"],
            "{defects:?}"
        );
        assert!(defects[0].1.contains("skipped rows=0 summary=1"), "{defects:?}");
        assert!(defects[1].1.contains("proved rows=3 summary=2"), "{defects:?}");
        assert!(defects[1].1.contains("unknown rows=3 summary=4"), "{defects:?}");
        assert!(defects[1].1.contains("skipped rows=3 summary=4"), "{defects:?}");
        // The same lookalike under counters that count it `proved`, as the
        // compiler would: accepted, exactly as before.
        let defects = accounting_rows(&reread(&|message| {
            let carrier = matches!(
                message,
                trust_types::TransportMessage::FunctionResult(envelope)
                    if envelope.results.iter().any(is_proved_instance_discharge)
            );
            other_solver(message);
            match message {
                trust_types::TransportMessage::FunctionResult(envelope) if carrier => {
                    (envelope.proved, envelope.unknown, envelope.skipped) = (2, 0, 0);
                }
                trust_types::TransportMessage::CrateSummary(summary) => {
                    summary.functions_verified = 2;
                    (summary.total_proved, summary.total_unknown, summary.total_skipped) =
                        (3, 3, 3);
                }
                _ => {}
            }
        }));
        assert!(defects.is_empty(), "a lookalike counted by its outcome reconciles: {defects:?}");

        // Real drift in the terminal counters is still a defect: a crate
        // summary that counts the discharge row as proof.
        let defects = accounting_rows(&reread(&|message| {
            if let trust_types::TransportMessage::CrateSummary(summary) = message {
                (summary.total_proved, summary.total_unknown, summary.total_skipped) = (3, 3, 3);
            }
        }));
        assert_eq!(defects.len(), 1, "{defects:?}");
        assert_eq!(defects[0].0, "transport:crate-summary-accounting");
        assert!(defects[0].1.contains("proved rows=2 summary=3"), "{defects:?}");
        assert!(defects[0].1.contains("unknown rows=4 summary=3"), "{defects:?}");
        assert!(defects[0].1.contains("skipped rows=4 summary=3"), "{defects:?}");
        // And an accounting row still makes the unit could-not-run (T9).
        let drifted = reread(&|message| {
            if let trust_types::TransportMessage::CrateSummary(summary) = message {
                summary.total_obligations += 1;
            }
        });
        let unit =
            crate::determinism_report::UnitDeterminism::of_rows(&drifted.verification_results, &[]);
        assert_eq!(unit.unkeyed_functions, ["<crate:trust_instance_discharge_fixture>"]);
        assert!(unit.could_not_run_line().is_some());
    }

    /// `normalization_adjusted_expected` (through `raw_transport_bucket`): the
    /// compiler never counted the discharge row `proved`, so whatever its
    /// report row becomes, no `proved` budget is moved on its account — it is
    /// tallied from its raw outcome on both sides, like a `skipped` row.
    #[test]
    fn normalization_leaves_a_proved_instance_discharge_row_where_the_compiler_counted_it() {
        let (envelope, discharge) = proved_instance_discharge_envelope();
        let assertion = 1 - discharge;
        let rows = pipeline_rows(&envelope);
        assert_eq!(tally(&normalization_adjusted_expected(&envelope, &rows)), DISCHARGE_TALLY);

        for outcome in [
            VerificationOutcome::Unknown,
            VerificationOutcome::Failed,
            VerificationOutcome::RuntimeChecked,
            VerificationOutcome::Timeout,
        ] {
            let mut reclassified = rows.clone();
            reclassified[discharge].outcome = outcome;
            assert_eq!(
                tally(&normalization_adjusted_expected(&envelope, &reclassified)),
                DISCHARGE_TALLY,
                "{outcome:?}: the assertion's `proved` is not the discharge row's to move"
            );
            assert_eq!(
                function_transport_summary_defect(&envelope, &reclassified),
                None,
                "{outcome:?}"
            );
        }

        // Control: the existing normalization is untouched. The sibling
        // assertion's report row demoted to unknown still moves its own bucket.
        let mut reclassified = rows.clone();
        reclassified[assertion].outcome = VerificationOutcome::Unknown;
        assert_eq!(
            tally(&normalization_adjusted_expected(&envelope, &reclassified)),
            [0, 0, 2, 0, 1, 0, 2]
        );
        assert_eq!(function_transport_summary_defect(&envelope, &reclassified), None);
        // And a lookalike is an ordinary `proved` row to it: counted `proved` by
        // the compiler, demoted here, its bucket moves.
        let mut lookalike = with_declared(&envelope, [2, 0, 0, 0, 0, 0, 2]);
        lookalike.results[discharge].solver = "ay-smtlib".to_string();
        let mut reclassified = pipeline_rows(&lookalike);
        reclassified[discharge].outcome = VerificationOutcome::Unknown;
        assert_eq!(
            tally(&normalization_adjusted_expected(&lookalike, &reclassified)),
            [1, 0, 1, 0, 0, 0, 2]
        );
        assert_eq!(function_transport_summary_defect(&lookalike, &reclassified), None);
    }

    /// The two sites that read `raw_transport_bucket` — the crate tally
    /// (`add_raw_transport_result_counts`) and
    /// `normalization_adjusted_expected` — set aside the `proved` discharge row
    /// and no other. A discharge row with any other outcome is counted, and
    /// moved when its report row is reclassified, by that outcome: as before,
    /// and as the compiler counts it. (The per-function site is held to the
    /// same nine lookalikes by
    /// `function_summary_counts_a_proved_instance_discharge_row_as_the_compiler_does`.)
    #[test]
    fn crate_summary_and_normalization_count_an_unproved_instance_discharge_row_by_its_outcome() {
        let (carrier, discharge) = proved_instance_discharge_envelope();
        // Where the compiler's own tally stands: `use_good`, then the crate.
        const CRATE_TALLY: [usize; 7] = [2, 0, 4, 0, 4, 0, 6];
        assert_eq!(declared(&carrier), DISCHARGE_TALLY);

        // The discharge row's outcome; what the compiler's tally declares for
        // `use_good` and for the crate with that row in place; the outcome its
        // report row is reclassified to below; and where that moves the
        // function's expected counters.
        struct Case {
            outcome: trust_types::Outcome,
            function: [usize; 7],
            krate: [usize; 7],
            reclassified: VerificationOutcome,
            moved: [usize; 7],
        }
        let cases = [
            Case {
                outcome: trust_types::Outcome::Failed,
                function: [1, 1, 0, 0, 0, 0, 2],
                krate: [2, 1, 3, 0, 3, 0, 6],
                reclassified: VerificationOutcome::Unknown,
                moved: [1, 0, 1, 0, 0, 0, 2],
            },
            Case {
                outcome: trust_types::Outcome::Unknown,
                function: [1, 0, 1, 0, 0, 0, 2],
                krate: [2, 0, 4, 0, 3, 0, 6],
                reclassified: VerificationOutcome::Failed,
                moved: [1, 1, 0, 0, 0, 0, 2],
            },
            Case {
                outcome: trust_types::Outcome::RuntimeChecked,
                function: [1, 0, 0, 0, 0, 1, 2],
                krate: [2, 0, 3, 0, 3, 1, 6],
                reclassified: VerificationOutcome::Unknown,
                moved: [1, 0, 1, 0, 0, 0, 2],
            },
            Case {
                outcome: trust_types::Outcome::Timeout,
                function: [1, 0, 1, 1, 0, 0, 2],
                krate: [2, 0, 4, 1, 3, 0, 6],
                reclassified: VerificationOutcome::Unknown,
                moved: [1, 0, 1, 0, 0, 0, 2],
            },
            // A raw `skipped` row: set aside like the `proved` discharge row,
            // as it always was, so nothing moves on its account.
            Case {
                outcome: trust_types::Outcome::Skipped,
                function: DISCHARGE_TALLY,
                krate: CRATE_TALLY,
                reclassified: VerificationOutcome::Failed,
                moved: DISCHARGE_TALLY,
            },
        ];

        for case in &cases {
            let name = format!("a discharge row with outcome {:?}", case.outcome);
            let outcome = case.outcome;
            // The pinned transport with that one outcome changed. `counted`
            // says whether the counters are moved to what the compiler would
            // declare for it, or left at the `proved` discharge row's tally.
            let transport = |counted: bool| {
                let mut messages = instance_discharge_messages();
                for message in &mut messages {
                    match message {
                        trust_types::TransportMessage::FunctionResult(envelope)
                            if envelope.results.iter().any(is_proved_instance_discharge) =>
                        {
                            for row in &mut envelope.results {
                                if is_proved_instance_discharge(row) {
                                    row.outcome = outcome;
                                }
                            }
                            if counted {
                                *envelope = with_declared(envelope, case.function);
                            }
                        }
                        trust_types::TransportMessage::CrateSummary(summary) if counted => {
                            [
                                summary.total_proved,
                                summary.total_failed,
                                summary.total_unknown,
                                summary.total_timed_out,
                                summary.total_skipped,
                                summary.total_runtime_checked,
                                summary.total_obligations,
                            ] = case.krate;
                        }
                        _ => {}
                    }
                }
                messages
            };

            // The crate tally counts the row by its outcome.
            let mut observed = FunctionTransportCounts::default();
            for message in transport(true) {
                if let trust_types::TransportMessage::FunctionResult(envelope) = message {
                    add_raw_transport_result_counts(&mut observed, &envelope.results);
                }
            }
            assert_eq!(tally(&observed), case.krate, "{name}: the crate tally");

            // Counted by its outcome in the function and in the crate, the
            // whole transport reconciles; under the `proved` discharge row's
            // counters it is the accounting defect in both.
            let defects = accounting_rows(&parse_raw_messages(transport(true)));
            assert!(defects.is_empty(), "{name}: counted by its outcome: {defects:?}");
            let defects = accounting_rows(&parse_raw_messages(transport(false)));
            if case.krate == CRATE_TALLY {
                assert!(defects.is_empty(), "{name}: the same tally: {defects:?}");
            } else {
                assert_eq!(
                    defects.iter().map(|(kind, _)| kind.as_str()).collect::<Vec<_>>(),
                    ["transport:summary-accounting", "transport:crate-summary-accounting"],
                    "{name}: must not be counted as a proved instance discharge: {defects:?}"
                );
            }

            // The normalization moves the row's own bucket when its report row
            // is reclassified, and only a set-aside row's bucket stays.
            let mut envelope = with_declared(&carrier, case.function);
            envelope.results[discharge].outcome = outcome;
            let mut reclassified = pipeline_rows(&envelope);
            reclassified[discharge].outcome = case.reclassified;
            assert_eq!(
                tally(&normalization_adjusted_expected(&envelope, &reclassified)),
                case.moved,
                "{name}: reclassified to {:?}",
                case.reclassified
            );
            assert_eq!(
                function_transport_summary_defect(&envelope, &reclassified),
                None,
                "{name}: reclassified to {:?}",
                case.reclassified
            );
        }
    }

    /// No split of `unknown` is excused as a legacy summary's once a `proved`
    /// instance-discharge row is among the rows: the compiler that publishes
    /// that row declares `skipped` and `timed_out` (its tally counts the row
    /// `skipped`, and `unknown` only as the aggregate over it). So tallying
    /// the row as the compiler does lets exactly the compiler's counters
    /// through, and not also a summary that counts the row `unknown` and
    /// nowhere else — a shape this check refused while it counted the row
    /// `proved`. Where the excuse applied before, it still does.
    #[test]
    fn a_legacy_split_is_not_excused_beside_a_proved_instance_discharge_row() {
        let (envelope, discharge) = proved_instance_discharge_envelope();
        let assertion = 1 - discharge;
        let rows = pipeline_rows(&envelope);
        let mut observed = FunctionTransportCounts::default();
        add_transport_result_counts(&mut observed, &envelope.results, &rows);
        assert_eq!(observed.assumed_discharge, 1, "the function tally knows the row");

        // `skipped: 0` under an agreeing `unknown`, in the function.
        let reason = function_transport_summary_defect(
            &with_declared(&envelope, [1, 0, 1, 0, 0, 0, 2]),
            &rows,
        )
        .expect("a proved discharge row counted `unknown` and not `skipped` is a miscount");
        assert!(
            reason.ends_with("does not match result rows: skipped rows=1 summary=0"),
            "{reason}"
        );

        // `timed_out: 0` under an agreeing `unknown`, in a function that also
        // carries the row: the assertion timed out. The compiler's counters
        // reconcile; the legacy aggregate does not.
        let mut timed_out = envelope.clone();
        timed_out.results[assertion].outcome = trust_types::Outcome::Timeout;
        let timed_out_rows = pipeline_rows(&timed_out);
        assert_eq!(
            function_transport_summary_defect(
                &with_declared(&timed_out, [0, 0, 2, 1, 1, 0, 2]),
                &timed_out_rows
            ),
            None
        );
        let reason = function_transport_summary_defect(
            &with_declared(&timed_out, [0, 0, 2, 0, 1, 0, 2]),
            &timed_out_rows,
        )
        .expect("the compiler that publishes a discharge row declares its timeouts");
        assert!(
            reason.ends_with("does not match result rows: timed_out rows=1 summary=0"),
            "{reason}"
        );

        // The same two shapes in the crate summary, the transport re-read whole.
        let reread = |edit: &dyn Fn(&mut trust_types::TransportMessage)| {
            let mut messages = instance_discharge_messages();
            for message in &mut messages {
                edit(message);
            }
            parse_raw_messages(messages)
        };
        let mut crate_observed = FunctionTransportCounts::default();
        for envelope in instance_discharge_envelopes() {
            add_raw_transport_result_counts(&mut crate_observed, &envelope.results);
        }
        assert_eq!(crate_observed.assumed_discharge, 1, "the crate tally knows the row");
        let defects = accounting_rows(&reread(&|message| {
            if let trust_types::TransportMessage::CrateSummary(summary) = message {
                summary.total_skipped = 0;
            }
        }));
        assert_eq!(defects.len(), 1, "{defects:?}");
        assert_eq!(defects[0].0, "transport:crate-summary-accounting");
        assert!(
            defects[0].1.ends_with("does not match function result rows: skipped rows=4 summary=0"),
            "{defects:?}"
        );
        let assertion_times_out = |message: &mut trust_types::TransportMessage| match message {
            trust_types::TransportMessage::FunctionResult(envelope)
                if envelope.results.iter().any(is_proved_instance_discharge) =>
            {
                for row in &mut envelope.results {
                    if !is_proved_instance_discharge(row) {
                        row.outcome = trust_types::Outcome::Timeout;
                    }
                }
                *envelope = with_declared(envelope, [0, 0, 2, 1, 1, 0, 2]);
            }
            trust_types::TransportMessage::CrateSummary(summary) => {
                (summary.total_proved, summary.total_unknown, summary.total_timed_out) = (1, 5, 1);
            }
            _ => {}
        };
        let defects = accounting_rows(&reread(&assertion_times_out));
        assert!(defects.is_empty(), "the compiler's counters for it reconcile: {defects:?}");
        let defects = accounting_rows(&reread(&|message| {
            assertion_times_out(message);
            if let trust_types::TransportMessage::CrateSummary(summary) = message {
                summary.total_timed_out = 0;
            }
        }));
        assert_eq!(defects.len(), 1, "{defects:?}");
        assert_eq!(defects[0].0, "transport:crate-summary-accounting");
        assert!(
            defects[0]
                .1
                .ends_with("does not match function result rows: timed_out rows=1 summary=0"),
            "{defects:?}"
        );
        // And an accounting row still makes the unit could-not-run (T9).
        let refused = reread(&|message| {
            if let trust_types::TransportMessage::CrateSummary(summary) = message {
                summary.total_skipped = 0;
            }
        });
        let unit =
            crate::determinism_report::UnitDeterminism::of_rows(&refused.verification_results, &[]);
        assert!(unit.could_not_run_line().is_some());

        // Controls: the excuse is where it was. A raw `skipped` row in the
        // discharge row's place is no `proved` discharge row, and a summary
        // without the split is excused for it, in the function and the crate.
        let skipped_instead = |message: &mut trust_types::TransportMessage| {
            if let trust_types::TransportMessage::FunctionResult(envelope) = message {
                let carrier = envelope.results.iter().any(is_proved_instance_discharge);
                for row in &mut envelope.results {
                    if is_proved_instance_discharge(row) {
                        row.outcome = trust_types::Outcome::Skipped;
                    }
                }
                if carrier {
                    envelope.skipped = 0;
                }
            }
        };
        let mut legacy = with_declared(&envelope, [1, 0, 1, 0, 0, 0, 2]);
        legacy.results[discharge].outcome = trust_types::Outcome::Skipped;
        let legacy_rows = pipeline_rows(&legacy);
        let mut observed = FunctionTransportCounts::default();
        add_transport_result_counts(&mut observed, &legacy.results, &legacy_rows);
        assert_eq!((observed.skipped, observed.assumed_discharge), (1, 0));
        assert_eq!(function_transport_summary_defect(&legacy, &legacy_rows), None);
        let defects = accounting_rows(&reread(&|message| {
            skipped_instead(message);
            if let trust_types::TransportMessage::CrateSummary(summary) = message {
                summary.total_skipped = 0;
            }
        }));
        assert!(
            defects.is_empty(),
            "a summary without the split, and no discharge row: {defects:?}"
        );
        // A timeout in a function with no discharge row, likewise.
        let mut plain = with_declared(&envelope, [1, 0, 1, 0, 0, 0, 2]);
        plain.results[discharge].outcome = trust_types::Outcome::Timeout;
        assert_eq!(function_transport_summary_defect(&plain, &pipeline_rows(&plain)), None);
    }
}

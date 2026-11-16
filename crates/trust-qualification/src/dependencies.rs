//! Complete locked/offline resolver observations under the original paired owner.
//!
//! The producer must own actual native execution/admission separately. Neither a
//! resolver capture nor this consistency result supplies that authority. All
//! package objects and the entire resolve object are retained for comparison;
//! binding package bytes does not authenticate registry or Git provenance.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use serde::Serialize;
use serde_json::{Value, json};

use crate::pair::{FileIdentity, Snapshot, file_identity};
use crate::receipts::ReceiptCheckedPair;
use crate::source::{self, DependencyIdentity, SourceIdentity};
use crate::{Git, Result, canonical_hex, refusal, tree};

pub const MAX_STDOUT_BYTES: usize = 64 * 1024 * 1024;
pub const MAX_STDERR_BYTES: usize = 1024 * 1024;
pub const MAX_PACKAGES: usize = 16_384;
pub const MAX_EDGES: usize = 1_048_576;
const ARGUMENTS: &[&str] = &["metadata", "--locked", "--offline", "--format-version", "1"];
mod json;
use json::Json;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Side {
    Control,
    Candidate,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Subject {
    Ay,
    TrustVc,
}

impl Subject {
    fn source_key(self) -> &'static str {
        match self {
            Self::Ay => "ay",
            Self::TrustVc => "trust_vc",
        }
    }
}

/// Constructed from the retained original pair, never from captured metadata.
/// A request specifies no CPU/memory grant and cannot widen a host purpose.
#[derive(Clone, Debug, Serialize)]
pub struct ResolverRequest {
    pub side: Side,
    pub subject: Subject,
    pub sdk_root: PathBuf,
    pub program: FileIdentity,
    pub compiler: FileIdentity,
    pub cwd: PathBuf,
    pub cargo_home: PathBuf,
}

impl ResolverRequest {
    pub fn arguments(&self) -> &'static [&'static str] {
        ARGUMENTS
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ResolverOutcome {
    Exit(i32),
    Signal(i32),
    NotStarted,
    Unknown,
}

/// Retained observations, including failed/partial bytes. The concrete runner
/// must report its native lifetime/resource facts separately in execution.
#[derive(Debug)]
pub struct ResolverCapture {
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub outcome: ResolverOutcome,
    pub cleanup_confirmed: bool,
    pub output_limit_exceeded: bool,
    pub failure: Option<String>,
    pub execution: Option<Value>,
}

/// The concrete native frontend supplies execution; saved data/test runners
/// satisfy the same diagnostic interface without creating an execution grant.
pub trait DependencyResolver {
    fn resolve(&mut self, request: &ResolverRequest) -> Result<ResolverCapture>;
    /// Retain preparation/admission/transport failures even when no capture can
    /// be returned. This remains descriptive, never execution authority.
    fn execution_observation(&self) -> Option<Value> {
        None
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct Resolution {
    packages: Vec<Json>,
    resolve: Json,
    workspace_members: Vec<String>,
}

#[derive(Serialize)]
struct PackageInput {
    ids: BTreeSet<String>,
    manifest: PathBuf,
    sha256: String,
    selections: BTreeSet<PathBuf>,
    source: Option<String>,
    frozen_path_root: Option<PathBuf>,
    dependency_root: Option<PathBuf>,
}

struct BoundDependency {
    content: DependencyIdentity,
    git: Option<SourceIdentity>,
    stats: tree::TreeStats,
}

#[derive(Default)]
struct Bindings {
    dependencies: BTreeMap<PathBuf, BoundDependency>,
    packages: BTreeMap<PathBuf, PackageInput>,
    selections: BTreeMap<PathBuf, FileIdentity>,
}

impl Bindings {
    /// Continue checking independent inputs after one refuses. A failed parse,
    /// runner, or earlier dependency check must not skip the other bindings.
    fn check(&self, git: &impl Git) -> Vec<String> {
        let mut errors = Vec::new();
        for (path, original) in &self.dependencies {
            let checked = (|| -> Result<()> {
                if tree::stats(path, true, &[])? != original.stats
                    || source::dependency_identity(path)? != original.content
                {
                    return Err(refusal(format!("dependency source changed: {}", path.display())));
                }
                Ok(())
            })();
            if let Err(error) = checked {
                errors.push(error.to_string());
            }
            if let Some(original) = &original.git {
                match source::identity(git, path, false, true) {
                    Ok(current) if &current == original => {}
                    Ok(_) => {
                        errors.push(format!("Git dependency source changed: {}", path.display()))
                    }
                    Err(error) => errors.push(format!("Git dependency rebinding: {error}")),
                }
            }
        }
        for selection in self.selections.values() {
            match file_identity(&selection.path) {
                Ok(current) if &current == selection => {}
                Ok(_) => errors.push(format!(
                    "package manifest selection changed: {}",
                    selection.path.display()
                )),
                Err(error) => errors.push(format!("package manifest rebinding: {error}")),
            }
        }
        for package in self.packages.values() {
            if let Some(root) = &package.frozen_path_root {
                if let Err(error) = source::path_package_bound(git, &package.manifest, root) {
                    errors.push(error.to_string());
                }
            }
        }
        errors
    }

    fn bind_package(
        &mut self,
        git: &impl Git,
        snapshot: &Snapshot,
        package: &Json,
    ) -> Result<PathBuf> {
        let id = string(package, "id")?;
        let name = string(package, "name")?;
        let source = match package.get("source") {
            Some(Json::Null) => None,
            Some(Json::String(text)) if !text.is_empty() => Some(text.clone()),
            _ => return Err(refusal("package source must be an explicit null or nonempty string")),
        };
        let path = Path::new(string(package, "manifest_path")?);
        if !path.is_absolute() {
            return Err(refusal("package manifest path is not absolute"));
        }
        let manifest = file_identity(path)?;
        if self.selections.get(path).is_some_and(|original| original != &manifest) {
            return Err(refusal(
                "package manifest selection changed between resolver observations",
            ));
        }
        let mut input = PackageInput {
            ids: BTreeSet::from([id.into()]),
            manifest: manifest.resolved_path.clone(),
            sha256: manifest.sha256.clone(),
            selections: BTreeSet::from([manifest.path.clone()]),
            source: source.clone(),
            frozen_path_root: None,
            dependency_root: None,
        };
        if source.is_none() {
            let root = snapshot
                .sources
                .values()
                .find(|root| input.manifest.starts_with(&root.path))
                .ok_or_else(|| refusal(format!("unfrozen path dependency: {}", path.display())))?;
            if name.starts_with("ay") && !input.manifest.starts_with(&snapshot.sources["ay"].path) {
                return Err(refusal("consumer resolved a different AY source"));
            }
            if !self.packages.contains_key(&input.manifest) {
                source::path_package_bound(git, &input.manifest, &root.path)?;
            }
            input.frozen_path_root = Some(root.path.clone());
        } else {
            if name.starts_with("ay") {
                return Err(refusal(
                    "AY dependency resolved from a Git/registry source instead of frozen AY",
                ));
            }
            let mut root = input
                .manifest
                .parent()
                .ok_or_else(|| refusal("dependency manifest has no parent"))?
                .to_path_buf();
            let revision = if source.as_ref().is_some_and(|source| source.starts_with("git+")) {
                // Resolve each actual package, even when another package in
                // the same workspace was bound. A cached path/prefix cannot
                // establish its repository root or source kind.
                let bytes = git.probe(&root, &["rev-parse", "--show-toplevel"])?;
                let text = std::str::from_utf8(&bytes)
                    .map_err(|_| refusal("Git dependency root is not UTF8"))?;
                let text = text.strip_suffix('\n').unwrap_or(text);
                root = fs::canonicalize(text)?;
                if !input.manifest.starts_with(&root) {
                    return Err(refusal(
                        "Git dependency manifest is outside its actual repository root",
                    ));
                }
                let revision = source
                    .as_deref()
                    .and_then(|source| source.rsplit_once('#'))
                    .map(|(_, revision)| revision)
                    .ok_or_else(|| refusal("Git dependency source has no resolved revision"))?;
                if !canonical_hex(revision, 40) {
                    return Err(refusal(
                        "Git dependency source has no canonical resolved revision",
                    ));
                }
                Some(revision)
            } else {
                None
            };
            if let Some(original) = self.dependencies.get(&root) {
                match (&original.git, revision) {
                    (Some(identity), Some(revision)) if identity.commit == revision => {}
                    (None, None) => {}
                    (Some(_), Some(_)) => {
                        return Err(refusal(
                            "Git dependency checkout differs from resolved revision",
                        ));
                    }
                    _ => {
                        return Err(refusal(
                            "dependency source kind conflicts with the original bound root",
                        ));
                    }
                }
            } else {
                let git_identity = if let Some(revision) = revision {
                    let identity = source::identity(git, &root, false, true)?;
                    if identity.commit != revision {
                        return Err(refusal(
                            "Git dependency checkout differs from resolved revision",
                        ));
                    }
                    Some(identity)
                } else {
                    None
                };
                // A retained root is initially hashed exactly once. Reusing
                // it never refreshes the original observation: the complete
                // before/after-outcome and handoff checks below still rebind it.
                self.dependencies.insert(
                    root.clone(),
                    BoundDependency {
                        content: source::dependency_identity(&root)?,
                        git: git_identity,
                        stats: tree::stats(&root, true, &[])?,
                    },
                );
            }
            input.dependency_root = Some(root);
        }
        let canonical = input.manifest.clone();
        if let Some(original) = self.packages.get_mut(&canonical) {
            if original.sha256 != input.sha256 {
                return Err(refusal(
                    "package manifest content changed between resolver observations",
                ));
            }
            if original.source != input.source
                || original.frozen_path_root != input.frozen_path_root
                || original.dependency_root != input.dependency_root
            {
                return Err(refusal("package source conflicts with the original manifest binding"));
            }
            original.ids.extend(input.ids);
            original.selections.extend(input.selections);
        } else {
            self.packages.insert(canonical.clone(), input);
        }
        self.selections.entry(manifest.path.clone()).or_insert(manifest);
        Ok(canonical)
    }
}

fn string<'a>(value: &'a Json, field: &str) -> Result<&'a str> {
    value
        .get(field)
        .and_then(Json::as_str)
        .filter(|s| !s.is_empty())
        .ok_or_else(|| refusal(format!("metadata {field} is missing or not a nonempty string")))
}

fn strings(value: &Json, context: &str, bound: usize) -> Result<Vec<String>> {
    let array = value
        .as_array()
        .filter(|array| array.len() <= bound)
        .ok_or_else(|| refusal(format!("metadata {context} is not a bounded array")))?;
    let mut seen = BTreeSet::new();
    for value in array {
        let value = value.as_str().filter(|s| !s.is_empty()).ok_or_else(|| {
            refusal(format!("metadata {context} contains a non-string/empty identity"))
        })?;
        if !seen.insert(value.to_owned()) {
            return Err(refusal(format!("metadata {context} repeats an identity")));
        }
    }
    Ok(seen.into_iter().collect())
}

fn resolution(bytes: &[u8]) -> Result<Resolution> {
    if bytes.len() > MAX_STDOUT_BYTES {
        return Err(refusal("metadata exceeds the finite stdout limit"));
    }
    // Exact number lexemes and duplicate-free objects preserve complete JSON
    // identity without changing serde_json semantics in unrelated validators.
    let document = Json::parse(bytes)?;
    if document.get("version").and_then(Json::as_u64) != Some(1) {
        return Err(refusal("metadata version is not the integer 1"));
    }
    let mut packages = document
        .get("packages")
        .and_then(Json::as_array)
        .filter(|packages| !packages.is_empty() && packages.len() <= MAX_PACKAGES)
        .ok_or_else(|| refusal("metadata packages are missing, empty or oversized"))?
        .clone();
    let mut ids = BTreeSet::new();
    for package in &packages {
        if !package.is_object() || !ids.insert(string(package, "id")?.to_owned()) {
            return Err(refusal("metadata packages repeat an identity or contain a non-object"));
        }
        string(package, "name")?;
        string(package, "manifest_path")?;
        if !matches!(package.get("source"), Some(Json::Null | Json::String(_))) {
            return Err(refusal("metadata package has no source field"));
        }
    }
    packages.sort_by(|a, b| {
        a.get("id").and_then(Json::as_str).cmp(&b.get("id").and_then(Json::as_str))
    });
    let workspace_members = strings(
        document
            .get("workspace_members")
            .ok_or_else(|| refusal("metadata workspace_members missing"))?,
        "workspace_members",
        MAX_PACKAGES,
    )?;
    if workspace_members.is_empty() || workspace_members.iter().any(|id| !ids.contains(id)) {
        return Err(refusal("metadata workspace member is absent from complete packages"));
    }
    let resolve = document
        .get("resolve")
        .filter(|resolve| resolve.is_object())
        .ok_or_else(|| refusal("metadata resolve graph is missing or null"))?;
    let nodes = resolve
        .get("nodes")
        .and_then(Json::as_array)
        .filter(|nodes| nodes.len() <= MAX_PACKAGES)
        .ok_or_else(|| refusal("metadata resolve nodes are missing or oversized"))?;
    let mut node_ids = BTreeSet::new();
    let mut edge_count = 0usize;
    for node in nodes {
        if !node_ids.insert(string(node, "id")?.to_owned()) {
            return Err(refusal("metadata resolve graph repeats a node"));
        }
        let edges = strings(
            node.get("dependencies")
                .ok_or_else(|| refusal("metadata resolve node dependencies missing"))?,
            "resolve dependencies",
            MAX_EDGES,
        )?;
        edge_count = edge_count
            .checked_add(edges.len())
            .filter(|count| *count <= MAX_EDGES)
            .ok_or_else(|| refusal("metadata resolve graph has too many edges"))?;
        if edges.iter().any(|id| !ids.contains(id)) {
            return Err(refusal("metadata resolve graph refers to an absent package"));
        }
        let deps = node
            .get("deps")
            .and_then(Json::as_array)
            .filter(|deps| deps.len() <= MAX_EDGES)
            .ok_or_else(|| refusal("metadata resolve node deps missing"))?;
        let referenced = deps
            .iter()
            .map(|dep| string(dep, "pkg").map(str::to_owned))
            .collect::<Result<BTreeSet<_>>>()?;
        if referenced != edges.into_iter().collect() {
            return Err(refusal("metadata resolve deps disagree with dependency identities"));
        }
        strings(
            node.get("features")
                .ok_or_else(|| refusal("metadata resolve node features missing"))?,
            "resolve features",
            MAX_EDGES,
        )?;
    }
    if node_ids != ids {
        return Err(refusal(
            "metadata resolve graph does not cover the complete package population",
        ));
    }
    match resolve.get("root") {
        Some(Json::Null) => {}
        Some(Json::String(id)) if ids.contains(id) => {}
        _ => return Err(refusal("metadata resolve root is missing or absent from packages")),
    }
    Ok(Resolution { packages, resolve: resolve.clone(), workspace_members })
}

struct ResolverRecord {
    request: ResolverRequest,
    attempted: bool,
    capture: Option<ResolverCapture>,
    execution: Option<Value>,
    resolution: Option<Resolution>,
    package_bindings: BTreeMap<String, PathBuf>,
    errors: Vec<String>,
}

/// Keeps the original pair, compiler-probe evidence, every attempted outcome,
/// and discovered dependency owners. It has no constructor from saved bytes.
pub struct DependencyAttempt {
    pair: ReceiptCheckedPair,
    probes: Value,
    probes_consistent: bool,
    records: Vec<ResolverRecord>,
    bindings: Bindings,
    errors: Vec<String>,
}

impl DependencyAttempt {
    pub(crate) fn run(
        pair: ReceiptCheckedPair,
        probes: Value,
        probes_consistent: bool,
        git: &impl Git,
        runner: &mut impl DependencyResolver,
    ) -> Self {
        let mut attempt = Self {
            pair,
            probes,
            probes_consistent,
            records: Vec::new(),
            bindings: Bindings::default(),
            errors: Vec::new(),
        };
        if !probes_consistent {
            attempt.errors.push(
                "compiler identity probes did not succeed; dependency resolver not called".into(),
            );
        }
        let requests = (|| -> Result<Vec<ResolverRequest>> {
            let snapshot = attempt.pair.snapshot();
            let mut requests = Vec::new();
            for (side, sdk) in
                [(Side::Control, &snapshot.control), (Side::Candidate, &snapshot.candidate)]
            {
                for subject in [Subject::Ay, Subject::TrustVc] {
                    requests.push(ResolverRequest {
                        side,
                        subject,
                        sdk_root: sdk.path.clone(),
                        program: sdk
                            .executables
                            .get("targo")
                            .ok_or_else(|| refusal("sealed native Targo absent"))?
                            .clone(),
                        compiler: sdk
                            .executables
                            .get("trustc")
                            .ok_or_else(|| refusal("sealed native compiler absent"))?
                            .clone(),
                        cwd: snapshot
                            .sources
                            .get(subject.source_key())
                            .ok_or_else(|| refusal("frozen metadata source absent"))?
                            .path
                            .clone(),
                        cargo_home: attempt.pair.report().requested_inputs.cargo_home.clone(),
                    });
                }
            }
            Ok(requests)
        })();
        match requests {
            Ok(requests) => {
                attempt.records = requests
                    .into_iter()
                    .map(|request| ResolverRecord {
                        request,
                        attempted: false,
                        capture: None,
                        execution: None,
                        resolution: None,
                        package_bindings: BTreeMap::new(),
                        errors: Vec::new(),
                    })
                    .collect()
            }
            Err(error) => attempt.errors.push(error.to_string()),
        }
        for index in 0..attempt.records.len() {
            let before = attempt.check_inputs(git);
            attempt.errors.extend(before);
            if !attempt.errors.is_empty() {
                break;
            }
            attempt.records[index].attempted = true;
            let capture = runner.resolve(&attempt.records[index].request);
            attempt.records[index].execution = runner.execution_observation();
            let run = (|| -> Result<Resolution> {
                attempt.records[index].capture = Some(capture?);
                let capture =
                    attempt.records[index].capture.as_ref().expect("stored resolver capture");
                if capture.stdout.len() > MAX_STDOUT_BYTES
                    || capture.stderr.len() > MAX_STDERR_BYTES
                {
                    return Err(refusal("resolver capture exceeds finite output bounds"));
                }
                if capture.output_limit_exceeded
                    || !capture.cleanup_confirmed
                    || capture.outcome != ResolverOutcome::Exit(0)
                    || capture.failure.is_some()
                {
                    return Err(refusal(
                        "resolver did not finish successfully within its limits and confirmed cleanup",
                    ));
                }
                let data = resolution(&capture.stdout)?;
                for package in &data.packages {
                    let manifest =
                        attempt.bindings.bind_package(git, attempt.pair.snapshot(), package)?;
                    attempt.records[index]
                        .package_bindings
                        .insert(string(package, "id")?.into(), manifest);
                }
                Ok(data)
            })();
            match run {
                Ok(data) => attempt.records[index].resolution = Some(data),
                Err(error) => attempt.records[index].errors.push(error.to_string()),
            }
            let after = attempt.check_inputs(git);
            attempt.errors.extend(after);
            // Malformed/inconsistent metadata or uncertain cleanup cannot
            // authorize another phase. Retain all remaining planned records.
            if !attempt.records[index].errors.is_empty() {
                break;
            }
        }
        for subject in [Subject::Ay, Subject::TrustVc] {
            let selected = attempt
                .records
                .iter()
                .filter(|record| record.request.subject == subject)
                .collect::<Vec<_>>();
            if selected.len() != 2
                || selected[0].resolution.is_none()
                || selected[0].resolution != selected[1].resolution
            {
                attempt.errors.push(format!(
                    "{} control/candidate dependency identities are missing or differ",
                    subject.source_key()
                ));
            }
        }
        let final_checks = attempt.check_inputs(git);
        attempt.errors.extend(final_checks);
        attempt
    }

    fn check_inputs(&self, git: &impl Git) -> Vec<String> {
        let mut errors = self.bindings.check(git);
        if let Err(error) = self.pair.check_unchanged(git) {
            errors.push(format!("original paired inputs after dependency resolution: {error}"));
        }
        errors
    }

    pub fn consistent(&self) -> bool {
        self.errors.is_empty()
            && self.records.len() == 4
            && self
                .records
                .iter()
                .all(|record| record.errors.is_empty() && record.resolution.is_some())
    }

    pub fn snapshot(&self) -> &Snapshot {
        self.pair.snapshot()
    }

    /// Original requested input observations retained by this live attempt.
    /// This exposes no execution owner, source authentication or new grant.
    pub fn requested_inputs(&self) -> &crate::pair::Request {
        self.pair.report().requested_inputs
    }

    /// Original bound root observations for a later native stage's disjoint
    /// output check. Paths cannot reconstruct the retained dependency owner.
    pub fn dependency_input_roots(&self) -> impl Iterator<Item = &Path> {
        self.bindings.dependencies.keys().map(PathBuf::as_path).chain(
            self.pair.snapshot().supplied_dependencies.iter().map(|input| input.path.as_path()),
        )
    }

    /// Rebind again before a later stage consumes the live owner. Persistent
    /// drift refuses even when an earlier saved report compared equal.
    pub fn check_unchanged(&self, git: &impl Git) -> Result<()> {
        let errors = self.check_inputs(git);
        if errors.is_empty() { Ok(()) } else { Err(refusal(errors.join("; "))) }
    }

    pub fn report(&self) -> Value {
        let records = self.records.iter().map(|record| {
            let capture = record.capture.as_ref().map(|capture| json!({
                "stdout_hex":hex(&capture.stdout), "stdout_sha256":tree::hash_bytes(&capture.stdout),
                "stderr_hex":hex(&capture.stderr), "stderr_sha256":tree::hash_bytes(&capture.stderr),
                "outcome":capture.outcome, "cleanup_confirmed":capture.cleanup_confirmed,
                "output_limit_exceeded":capture.output_limit_exceeded, "failure":capture.failure,
                "execution":capture.execution,
            }));
            // Preserve exact numbers even when the caller's serde_json Value
            // representation cannot represent them without rounding.
            let identity = record.resolution.as_ref().and_then(|data| serde_json::to_string(data).ok());
            json!({"request":record.request, "arguments":record.request.arguments(),
                "status":if !record.attempted {"not_attempted"} else if record.capture.is_none() {"runner_refused"} else if record.errors.is_empty() {"bound"} else {"refused"},
                "attempted":record.attempted, "execution":record.execution,
                "capture":capture, "identity_json":identity, "package_bindings":record.package_bindings,
                "errors":record.errors})
        }).collect::<Vec<_>>();
        let dependencies = self
            .bindings
            .dependencies
            .values()
            .map(|binding| {
                json!({
                    "content":binding.content,"git":binding.git,
                })
            })
            .collect::<Vec<_>>();
        json!({
            "schema":"trust.paired-qualification.v1",
            "stage":"locked-offline-dependency-resolution",
            "status":if self.consistent() {"dependency-observations-checked"} else {"refused"},
            "claim_scope":"complete resolver-byte and frozen dependency consistency only; producer admission and actual execution facts are separate observations; no source/build authentication, proof, workload qualification or publication authority",
            "pending_stages":if self.probes_consistent {crate::probes::PENDING_STAGES} else {crate::receipts::PENDING_STAGES},
            "compiler_probes":self.probes,
            "receipts":self.pair.report(),
            "records":records, "dependency_sources":dependencies,
            "package_inputs":self.bindings.packages.values().collect::<Vec<_>>(),
            "manifest_selections":self.bindings.selections.values().collect::<Vec<_>>(),
            "errors":self.errors,
        })
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

#[cfg(test)]
mod tests;

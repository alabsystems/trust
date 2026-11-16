//! Input inspection is the first stage of the native paired runner, not a
//! successful experiment. The next stages must consume this same snapshot.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};

use serde::Serialize;

use crate::source::{self, DependencyIdentity, SourceIdentity};
use crate::{Git, Result, canonical_hex, refusal, seal, tree};

const TOOLS: &[&str] = &["trustc", "targo", "targo-trust", "trustd", "ay"];
const FIXTURES: &[&str] = &[
    "crates/ay-pb/proofs/trust_vc/refutation_step_realbody.rs",
    "crates/ay-pb/proofs/trust_vc/refutation_loop_realbody.rs",
];

#[derive(Clone, Debug, Serialize)]
pub struct Request {
    pub control: PathBuf,
    pub candidate: PathBuf,
    pub candidate_commit: String,
    pub candidate_receipt: PathBuf,
    pub ay: PathBuf,
    pub trust_vc: PathBuf,
    pub trust_spec_source: PathBuf,
    pub cargo_home: PathBuf,
    /// Actual resolved package roots, when a later metadata stage supplies them.
    /// An empty list makes no dependency-resolution claim.
    pub dependency_roots: Vec<PathBuf>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct FileIdentity {
    pub path: PathBuf,
    pub resolved_path: PathBuf,
    pub sha256: String,
    pub link_text: Option<PathBuf>,
}

/// Observe exact file/link bytes for diagnostic drift detection. This is not
/// authentication of a running image, a receipt writer or an execution grant.
pub fn file_identity(path: &Path) -> Result<FileIdentity> {
    let metadata = fs::symlink_metadata(path)?;
    let stamp = tree::Fingerprint::of(&metadata);
    let link_text =
        if metadata.file_type().is_symlink() { Some(tree::read_link(path)?) } else { None };
    let resolved_path = fs::canonicalize(path)?;
    let sha256 = tree::hash_file(&resolved_path)?;
    if link_text.as_ref().map(|_| tree::read_link(path)).transpose()? != link_text {
        return Err(refusal("input file link changed while binding"));
    }
    if tree::Fingerprint::of(&fs::symlink_metadata(path)?) != stamp {
        return Err(refusal("input file changed kind or metadata while binding"));
    }
    Ok(FileIdentity { path: path.into(), resolved_path, sha256, link_text })
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ToolchainIdentity {
    pub path: PathBuf,
    pub reported_commit: String,
    pub content: seal::Identity,
    pub provenance: FileIdentity,
    pub executables: BTreeMap<String, FileIdentity>,
    /// Additional selection binding; never changes the compatible seal digest.
    pub resolved_links: BTreeMap<PathBuf, PathBuf>,
    /// Promotion records are outside seal-content-v1, but remain frozen inputs.
    pub seal_records: BTreeMap<String, Option<FileIdentity>>,
}

fn properties(bytes: &[u8]) -> Result<BTreeMap<String, String>> {
    let text = std::str::from_utf8(bytes).map_err(|_| refusal("PROVENANCE is not UTF8"))?;
    let mut result = BTreeMap::new();
    for line in text.lines().filter(|line| !line.is_empty() && !line.starts_with('#')) {
        let (key, value) =
            line.split_once('=').ok_or_else(|| refusal("malformed PROVENANCE line"))?;
        if result.insert(key.into(), value.into()).is_some() {
            return Err(refusal(format!("duplicate PROVENANCE key: {key}")));
        }
    }
    Ok(result)
}

fn toolchain_identity(root: &Path, expected: Option<&str>) -> Result<ToolchainIdentity> {
    if !root.is_absolute()
        || root != fs::canonicalize(root)?
        || root.components().any(|component| component.as_os_str() == "build")
        || fs::symlink_metadata(root)?.file_type().is_symlink()
    {
        return Err(refusal(format!(
            "toolchain must be a canonical immutable seal outside build/: {}",
            root.display()
        )));
    }
    let provenance_path = root.join("PROVENANCE");
    let properties = properties(&tree::read_file(&provenance_path)?)?;
    let commit =
        properties.get("reported_commit").ok_or_else(|| refusal("seal has no reported commit"))?;
    if !canonical_hex(commit, 40) || expected.is_some_and(|expected| expected != commit) {
        return Err(refusal("sealed compiler commit differs from requested candidate"));
    }
    if properties.get("sealed_by").map(String::as_str) != Some("scripts/promote-toolchain.sh")
        || properties.get("artifact_content_scope").map(String::as_str) != Some(seal::SCOPE)
    {
        return Err(refusal("toolchain lacks the complete promoter seal-content record"));
    }
    let content = seal::identity(root)?;
    if properties.get("artifact_content_sha256") != Some(&content.sha256) {
        return Err(refusal("toolchain content differs from sealed PROVENANCE"));
    }
    let mut resolved_links = BTreeMap::new();
    for relative in tree::entries(root, false, &[])? {
        let path = root.join(&relative);
        if fs::symlink_metadata(&path)?.file_type().is_symlink() {
            let target = fs::canonicalize(&path)?;
            let selected = target.strip_prefix(root).map_err(|_| {
                refusal(format!("toolchain link escapes its immutable root: {}", path.display()))
            })?;
            if selected.components().next().is_some_and(|component| {
                seal::RECORDS.iter().any(|record| component.as_os_str() == *record)
            }) {
                return Err(refusal("toolchain link selects excluded record content"));
            }
            resolved_links.insert(relative, selected.into());
        }
    }
    let mut executables = BTreeMap::new();
    for name in TOOLS {
        let path = root.join("bin").join(name);
        let metadata = fs::symlink_metadata(&path)?;
        if !metadata.file_type().is_file() || metadata.mode() & 0o111 == 0 {
            return Err(refusal(format!("missing exact executable: {}", path.display())));
        }
        executables.insert((*name).into(), file_identity(&path)?);
    }
    let provenance = file_identity(&provenance_path)?;
    let mut seal_records = BTreeMap::new();
    for name in seal::RECORDS {
        let path = root.join(name);
        let identity = match fs::symlink_metadata(&path) {
            Ok(_) => Some(file_identity(&path)?),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(error) => return Err(error.into()),
        };
        seal_records.insert((*name).into(), identity);
    }
    if properties != self::properties(&tree::read_file(&provenance_path)?)? {
        return Err(refusal("seal PROVENANCE changed while binding"));
    }
    Ok(ToolchainIdentity {
        path: root.into(),
        reported_commit: commit.clone(),
        content,
        provenance,
        executables,
        resolved_links,
        seal_records,
    })
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Snapshot {
    pub control: ToolchainIdentity,
    pub candidate: ToolchainIdentity,
    pub candidate_receipt: FileIdentity,
    pub sources: BTreeMap<String, SourceIdentity>,
    pub proof_fixtures: BTreeMap<String, FileIdentity>,
    pub trust_spec_source: FileIdentity,
    /// Absence is part of the identity. Contents and credentials are never emitted.
    pub cargo_configs: BTreeMap<PathBuf, Option<FileIdentity>>,
    pub supplied_dependencies: Vec<DependencyIdentity>,
}

/// This owner has no grant/execute/publish methods. A later runner stage must
/// establish all missing predicates before it can obtain such a capability.
#[derive(Debug)]
pub struct InspectedPair {
    request: Request,
    snapshot: Snapshot,
}

#[derive(Serialize)]
pub struct InspectionReport<'a> {
    pub schema: &'static str,
    pub stage: &'static str,
    pub status: &'static str,
    pub claim_scope: &'static str,
    pub pending_stages: &'static [&'static str],
    pub inputs: &'a Snapshot,
    pub requested_inputs: &'a Request,
}

pub const PENDING_STAGES: &[&str] = &[
    "completed-stage-receipt-validation",
    "actual-compiler-identity-probes",
    "paired-locked-offline-dependency-resolution",
    "admitted-supervised-execution",
    "complete-source-bound-ay-census",
    "paired-native-inventories-and-resource-samples",
    "identity-aware-proof-comparison",
    "candidate-decision-and-landing",
];

impl InspectedPair {
    pub fn report(&self) -> InspectionReport<'_> {
        InspectionReport {
            schema: "trust.paired-qualification.v1",
            stage: "input-inspection",
            status: "inspected",
            claim_scope: "diagnostic input binding only; no execution, proof, candidate qualification or publication authority",
            pending_stages: PENDING_STAGES,
            inputs: &self.snapshot,
            requested_inputs: &self.request,
        }
    }

    pub fn check_unchanged(&self, git: &impl Git) -> Result<()> {
        if inspect_snapshot(git, &self.request)? != self.snapshot {
            return Err(refusal("paired qualification input changed since inspection"));
        }
        Ok(())
    }

    pub fn snapshot(&self) -> &Snapshot {
        &self.snapshot
    }
}

/// The native runner's first supported stage. Later receipt/probe/run stages
/// are explicitly pending, so inspection cannot masquerade as measurement.
pub fn inspect(git: &impl Git, request: Request) -> Result<InspectedPair> {
    let snapshot = inspect_snapshot(git, &request)?;
    let pair = InspectedPair { request, snapshot };
    pair.check_unchanged(git)?;
    Ok(pair)
}

fn inspect_snapshot(git: &impl Git, request: &Request) -> Result<Snapshot> {
    if !canonical_hex(&request.candidate_commit, 40) {
        return Err(refusal("candidate commit must be a full lowercase Git object ID"));
    }
    if !request.cargo_home.is_absolute() {
        return Err(refusal("CARGO_HOME must be absolute"));
    }
    let ay = fs::canonicalize(&request.ay)?;
    let trust_vc = fs::canonicalize(&request.trust_vc)?;
    if ay == trust_vc {
        return Err(refusal("AY and trust-vc must be distinct source repositories"));
    }
    // Candidate first: a missing/rejected build must precede workload activity.
    let candidate_receipt = file_identity(&request.candidate_receipt)?;
    let candidate = toolchain_identity(&request.candidate, Some(&request.candidate_commit))?;
    let control = toolchain_identity(&request.control, None)?;
    let sealed_receipt = file_identity(&request.candidate.join("tool-provenance.json"))?;
    if sealed_receipt.sha256 != candidate_receipt.sha256 {
        return Err(refusal("explicit candidate receipt differs from the sealed receipt"));
    }
    let sources = BTreeMap::from([
        ("ay".into(), source::identity(git, &ay, true, false)?),
        ("trust_vc".into(), source::identity(git, &trust_vc, true, false)?),
    ]);
    let mut proof_fixtures = BTreeMap::new();
    let tracked = git.probe(&ay, &["ls-files", "-z"])?;
    for fixture in FIXTURES {
        if !tracked.split(|b| *b == 0).any(|row| row == fixture.as_bytes()) {
            return Err(refusal(format!("missing or unbound AY proof fixture: {fixture}")));
        }
        proof_fixtures.insert((*fixture).into(), file_identity(&ay.join(fixture))?);
    }
    let mut configs = BTreeSet::new();
    for root in [&ay, &trust_vc] {
        for ancestor in root.ancestors() {
            for name in ["config", "config.toml"] {
                configs.insert(ancestor.join(".cargo").join(name));
            }
        }
    }
    for name in ["config", "config.toml"] {
        configs.insert(request.cargo_home.join(name));
    }
    let mut cargo_configs = BTreeMap::new();
    for path in configs {
        let identity = match fs::symlink_metadata(&path) {
            Ok(_) => Some(file_identity(&path)?),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(error) => return Err(error.into()),
        };
        cargo_configs.insert(path, identity);
    }
    let supplied_dependencies = request
        .dependency_roots
        .iter()
        .map(|path| source::dependency_identity(path))
        .collect::<Result<Vec<_>>>()?;
    Ok(Snapshot {
        control,
        candidate,
        candidate_receipt,
        sources,
        proof_fixtures,
        trust_spec_source: file_identity(&request.trust_spec_source)?,
        cargo_configs,
        supplied_dependencies,
    })
}

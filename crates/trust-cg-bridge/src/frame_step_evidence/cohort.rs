// Copyright 2026 Andrew Yates | Apache-2.0
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use clean_kernel::{Environment, Name, ReferenceKernel};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::{
    CapturedModuleBytes, ImportError, ReferenceBase, load_modules_with_deps_checked,
    reference_base_closed,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

pub(super) const ROOT: &str = "SemRFrameStep";
pub(super) const THEOREM: &str = "SemR.MemoryEmbedding.FrameStep.save_step";
const MANIFEST: &str = include_str!("cohort.json");

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Parts {
    pub base: String,
    pub server: Option<String>,
    pub private: Option<String>,
    pub ir: Option<String>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Manifest {
    pub schema: String,
    pub ir_commit: String,
    pub lean_version: String,
    pub lean_githash: String,
    pub source_sha256: BTreeMap<String, String>,
    pub modules: BTreeMap<String, Parts>,
}
pub(super) fn hash(data: &[u8]) -> String {
    format!("{:x}", Sha256::digest(data))
}
pub(super) fn parts(bytes: CapturedModuleBytes<'_>) -> Parts {
    Parts {
        base: hash(bytes.base),
        server: bytes.server.map(hash),
        private: bytes.private.map(hash),
        ir: bytes.ir.map(hash),
    }
}
fn refusal(name: &Name, why: &str) -> ImportError {
    ImportError::UnsupportedModule { module: name.to_string(), reason: why.into() }
}

pub struct FrameTheoremEnvironment {
    pub(super) kernel: ReferenceKernel,
    pub(super) cohort: String,
}
impl FrameTheoremEnvironment {
    pub fn open(directory: &Path) -> Result<Self, String> {
        let (kernel, cohort) = open_unit(directory, MANIFEST, ROOT, THEOREM)?;
        Ok(Self { kernel, cohort })
    }
    pub fn cohort_digest(&self) -> &str {
        &self.cohort
    }
}

/// Internal fixed-manifest loader shared by the two conditional proof cones.
/// Public constructors pass compiled-in module/theorem/cohort identities only.
pub(super) fn open_unit(
    directory: &Path,
    manifest: &str,
    root_module: &str,
    theorem: &str,
) -> Result<(ReferenceKernel, String), String> {
    let (replay, digest) =
        open_replay(directory, manifest, "trust.frame-step-cohort.v1", &[root_module], &[theorem])?;
    let kernel = replay.into_kernel().map_err(|r| r.verdict_sentence())?;
    Ok((kernel, digest))
}

/// Crate-private fixed-cohort primitive. Runtime public constructors supply
/// COMPILED manifests and root sets only; packet/context data cannot select
/// any of these parameters. Existing frame constructors use the same exact
/// one-module/one-theorem wrapper above. Completion remains sealed by Clean.
pub(crate) fn open_replay(
    directory: &Path,
    manifest: &str,
    schema: &str,
    root_modules: &[&str],
    theorems: &[&str],
) -> Result<(ReferenceBase, String), String> {
    let expected: Manifest = serde_json::from_str(manifest).map_err(|e| e.to_string())?;
    let roots = theorems.iter().map(|name| Name::from_string(name)).collect::<BTreeSet<_>>();
    if expected.schema != schema
        || expected.lean_version != "4.30.0-rc2"
        || expected.modules.is_empty()
        || root_modules.is_empty()
        || roots.is_empty()
        || roots.len() != theorems.len()
    {
        return Err("invalid compiled frame theorem cohort".into());
    }
    let root = directory.canonicalize().map_err(|e| e.to_string())?;
    let mut env = Environment::for_lean_replay();
    let mut seen = BTreeSet::new();
    let mut before = |name: &Name, path: &Path, index: usize| {
        let name_s = name.to_string();
        if index != 0
            || !expected.modules.contains_key(&name_s)
            || name_s
                .split('.')
                .any(|p| p.is_empty() || !p.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_'))
        {
            return Err(refusal(name, "module is outside compiled frame cohort"));
        }
        let exact = root.join(name_s.replace('.', "/") + ".olean");
        if path != exact || path.canonicalize().ok().as_ref() != Some(&exact) {
            return Err(refusal(name, "frame cohort path or symlink differs"));
        }
        Ok(())
    };
    let mut captured = |name: &Name, _path: &Path, bytes: CapturedModuleBytes<'_>| {
        let key = name.to_string();
        let actual = parts(bytes);
        let wanted =
            expected.modules.get(&key).ok_or_else(|| refusal(name, "unmanifested module"))?;
        if actual.base != wanted.base
            || actual.server != wanted.server
            || actual.private != wanted.private
            || actual.ir != wanted.ir
        {
            return Err(refusal(name, "captured frame module bytes differ"));
        }
        if !seen.insert(key) {
            return Err(refusal(name, "duplicate module capture"));
        }
        Ok(())
    };
    load_modules_with_deps_checked(
        &mut env,
        &root_modules.iter().map(|name| (*name).into()).collect::<Vec<_>>(),
        &[root.clone()],
        &mut before,
        &mut captured,
    )
    .map_err(|e| e.to_string())?;
    if seen != expected.modules.keys().cloned().collect() {
        return Err("compiled frame cohort has missing or extra module rows".into());
    }
    let mut options = ClosedRecheckOptions::default();
    options.max_closure = Some(100_000);
    let replay = reference_base_closed(&env, &roots, &options).map_err(|e| e.to_string())?;
    if !replay.entry_refusals.is_empty()
        || !replay.report.passed()
        || !replay.report.extension_bindings_pinned
        || !roots.is_subset(&replay.admitted)
    {
        return Err(format!(
            "frame theorem dependency replay refused: {} {:?}",
            replay.report.verdict_sentence(),
            replay.entry_refusals
        ));
    }
    Ok((replay, hash(manifest.as_bytes())))
}

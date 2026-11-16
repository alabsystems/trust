// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Production VF5 base intake. Packages, imported declarations and reports are
//! data: this package entry returns a `Vf5Reference` only after a completed
//! EMPTY-start replay and BOTH fixed package/environment pins. The existing
//! `Vf5Reference::new` separately retains its environment-pin contract.
//!
//! This module does not run Lean, search for a proof, import generated row
//! proofs into the base, register a row or select a verification grade.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Component, Path, PathBuf};
use std::time::Instant;

use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_kernel::{EnvDigest, ReferenceRefusal};
use clean_olean::{
    CapturedModuleBytes, ClosedRecheckOptions, ClosedRecheckReport, ImportError, ModuleCaptureLimits,
    load_modules_with_deps_checked_with_limits, reference_base_closed,
};
use serde::Deserialize;
use sha2::{Digest, Sha256};
use trust_types::determinism::StopCause;

use super::{CalculusRowMiss, Vf5Reference};

const CLEAN_REVISION: &str = "24861300fea40294bb485bb630eb216756dc558d";
const LEAN_WORLD: &str = "v4.30.0-rc2";

/// Source identity of the fixed mathematical input this consumer accepts.
/// The compiler's selected Clean source may advance independently. This is
/// descriptive DATA only: it cannot pin a package or admit a reference.
#[must_use]
pub const fn fixed_source_identity() -> (&'static str, &'static str) {
    (CLEAN_REVISION, LEAN_WORLD)
}

const MANIFEST: &str = "vf5-base-v1.json";
const MAX_MODULES: usize = 4096;
// Intake/decoder resource bounds, not a larger kernel heartbeat budget.
const MAX_PART_BYTES: u64 = 256 * 1024 * 1024;
const MAX_CAPTURE_BYTES: usize = 1024 * 1024 * 1024;
// Each import-array slot occupies eight serialized bytes. All three mathematical
// roots may borrow a prior part's array, so charge every root, including duplicate
// rows. This preserves the old byte-admitted population; it does not bound total
// parser or kernel resident memory.
const MAX_CAPTURE_IMPORTS: usize = 3 * (MAX_CAPTURE_BYTES / 8);

/// Fixed VF5 intake policy, also used by the untrusted input preparer.
/// These limits grant no reference, environment pin, proof or kernel budget.
#[must_use]
pub const fn vf5_capture_limits() -> ModuleCaptureLimits {
    ModuleCaptureLimits::new(
        MAX_PART_BYTES as usize,
        MAX_CAPTURE_BYTES,
        MAX_MODULES,
        MAX_CAPTURE_IMPORTS,
    )
}

// The original theorem cone, never generated VF5Rows/Spec fixture proofs.
const ROOT_MODULE: &str = "VF5Check";
const TARGETS: &[&str] = &[
    "VF5.RowProved",
    "VF5.row_of",
    "VF5.checkBlob",
    "VF5.rowShape",
    "VF5.vc_sound_F1",
    "VF5.compose_F1",
    "VF5.rootsSafe_of",
];
const AX0: &[&str] = &["Classical.choice", "Quot.sound", "propext"];

/// A reviewed association of actual package bytes with the completed kernel
/// environment. No caller can supply this table or append a runtime pin.
struct BasePin {
    manifest_sha256: [u8; 32],
    environment_sha256: [u8; 32],
}

// Deliberately empty until an independent genuine replay supplies the exact
// manifest/environment pair. An all-zero placeholder would be a false pin.
const PINNED_BASES: &[BasePin] = &[];

/// Build-host resource DATA uses the same immutable associations as runtime intake.
/// Copying a package never creates a reference kernel or licenses a new pin.
pub mod resource;

/// Descriptive target-type observations from the completed production replay.
pub mod measurement;

/// Whether this compiled source licenses any production package. A consumer
/// uses this only to avoid setup/retention work when admission is closed.
/// It is not a runtime switch, package check or reference certificate.
#[must_use]
pub fn has_production_pin() -> bool {
    !PINNED_BASES.is_empty() && !super::PINNED_VF5_ENV_DIGESTS.is_empty()
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
    schema: u32,
    clean_revision: String,
    lean_world: String,
    // Source identity is part of the statically pinned raw manifest. It is
    // reviewed against the original source producer; these labels alone
    // authenticate neither an import nor a theorem.
    source_files: BTreeMap<String, String>,
    modules: Vec<Module>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Module {
    path: String,
    base_sha256: String,
    server_sha256: Option<String>,
    private_sha256: Option<String>,
    ir_sha256: Option<String>,
}

/// Refusal to construct a production reference base. A diagnostic report is
/// retained on replay failure and never substituted for original completion.
#[derive(Debug)]
pub enum Vf5BaseMiss {
    Stopped(StopCause),
    Io(std::io::Error),
    Manifest(serde_json::Error),
    InvalidPackage(&'static str),
    UnpinnedPackage([u8; 32]),
    Import(ImportError),
    Entry(ReferenceRefusal),
    Replay {
        report: Box<ClosedRecheckReport>,
        entry_refusals: Vec<(String, ReferenceRefusal)>,
    },
    Axioms(Vec<String>),
    Admission(CalculusRowMiss),
}

/// Measured intake information, never a completion token or row certificate.
#[derive(Debug)]
pub struct Vf5BaseReport {
    pub manifest_sha256: [u8; 32],
    pub environment: EnvDigest,
    pub captured_modules: usize,
    pub replay: ClosedRecheckReport,
}

impl Vf5Reference {
    /// The compiler's once-per-crate entry. It preserves an earlier ambient
    /// kernel deadline and existing stopped scope; it grants no function
    /// clock credit and cannot return a completed reference after a stop.
    pub fn load_package_until(
        root: &Path,
        deadline: Option<Instant>,
    ) -> Result<(Self, Vf5BaseReport), Vf5BaseMiss> {
        if let Some(stop) = crate::RUN_STOP.with(std::cell::Cell::get)
            .or_else(trust_types::verify_budget::exhaustion_cause)
        {
            return Err(Vf5BaseMiss::Stopped(stop));
        }
        let (result, stop) = crate::with_stop_scope(|| {
            let result = clean_kernel::tc::run_until(deadline, || {
                check_deadline()?;
                let reference = Self::load_package(root)?;
                check_deadline()?;
                Ok(reference)
            })
            .unwrap_or(Err(Vf5BaseMiss::Stopped(StopCause::WallBackstop)));
            if let Err(Vf5BaseMiss::Stopped(stop)) = &result {
                crate::note_certify_stop(*stop);
            }
            result
        });
        match stop {
            Some(stop) => Err(Vf5BaseMiss::Stopped(stop)),
            None => result,
        }
    }

    /// Load the fixed VF5 theorem cone from a reviewed package. The package
    /// layout has one `modules` root, so no ambient Lean path or fallback
    /// search root can supply an unlisted dependency. Missing pins refuse
    /// before decoding/replaying untrusted module data.
    pub fn load_package(root: &Path) -> Result<(Self, Vf5BaseReport), Vf5BaseMiss> {
        let (root, bytes) = manifest_bytes(root)?;
        let digest = Sha256::digest(&bytes).into();
        let pin = PINNED_BASES
            .iter()
            .find(|pin| pin.manifest_sha256 == digest)
            .ok_or(Vf5BaseMiss::UnpinnedPackage(digest))?;
        let manifest: Manifest = serde_json::from_slice(&bytes).map_err(Vf5BaseMiss::Manifest)?;
        validate_manifest(&manifest)?;
        let (kernel, report) = replay(&root, &manifest, digest)?;
        if kernel.env_digest().0 != pin.environment_sha256 {
            return Err(Vf5BaseMiss::Admission(CalculusRowMiss::UnpinnedBase(
                kernel.env_digest(),
            )));
        }
        let reference = Self::new(kernel).map_err(Vf5BaseMiss::Admission)?;
        Ok((reference, report))
    }
}

fn check_deadline() -> Result<(), Vf5BaseMiss> {
    if let Some(stop) = preparation_stop() {
        return Err(Vf5BaseMiss::Stopped(stop));
    }
    Ok(())
}

/// Non-charging observation for the compiler's input-sized preparation
/// census. It neither installs a new budget nor suspends/renews an inherited
/// deadline. An already stopped scope or zero remaining steps is unavailable.
#[must_use]
pub fn preparation_stop() -> Option<StopCause> {
    if let Some(stop) = crate::RUN_STOP.with(std::cell::Cell::get) {
        return Some(stop);
    }
    if trust_types::verify_budget::exhausted_readonly() {
        return Some(trust_types::verify_budget::exhaustion_cause()
            .unwrap_or(StopCause::Unclassified));
    }
    // Force an entry/exit poll even for a cached or immediately refused
    // package. run_until(None) keeps an earlier inherited absolute limit.
    if clean_kernel::tc::run_until(None, clean_kernel::tc::poll_deadline).is_none() {
        Some(StopCause::WallBackstop)
    } else {
        None
    }
}

/// Independently measurable preparation, not admission. This performs the
/// same capture/replay/audit as production, then DROPS the completed kernel.
/// It returns no `Vf5Reference`, certificate, registry entry or runtime pin.
/// A later source change may license this manifest/environment pair only
/// after independent review of the actual producer, sources and measurement.
pub fn measure_package(root: &Path) -> Result<Vf5BaseReport, Vf5BaseMiss> {
    let (root, bytes) = manifest_bytes(root)?;
    let manifest: Manifest = serde_json::from_slice(&bytes).map_err(Vf5BaseMiss::Manifest)?;
    validate_manifest(&manifest)?;
    let (_, report) = replay(&root, &manifest, Sha256::digest(&bytes).into())?;
    Ok(report)
}

fn manifest_bytes(root: &Path) -> Result<(PathBuf, Vec<u8>), Vf5BaseMiss> {
    let root = plain_root(root)?;
    let path = root.join(MANIFEST);
    regular_path(&root, &path).map_err(Vf5BaseMiss::InvalidPackage)?;
    let bytes = trust_proof_session::storage::read_bounded(&path).map_err(Vf5BaseMiss::Io)?;
    Ok((root, bytes))
}

fn replay(
    root: &Path,
    manifest: &Manifest,
    manifest_sha256: [u8; 32],
) -> Result<(clean_kernel::ReferenceKernel, Vf5BaseReport), Vf5BaseMiss> {
    let modules_root = root.join("modules");
    regular_path(root, &modules_root).map_err(Vf5BaseMiss::InvalidPackage)?;
    let (imported, captured_modules) = import(&modules_root, manifest)?;
    let targets = TARGETS.iter().map(|name| Name::from_string(name)).collect();
    let mut built = reference_base_closed(&imported, &targets, &ClosedRecheckOptions::default())
        .map_err(Vf5BaseMiss::Entry)?;
    let replay = built.report.clone();
    if !built.entry_refusals.is_empty() {
        return Err(Vf5BaseMiss::Replay {
            report: Box::new(replay),
            entry_refusals: std::mem::take(&mut built.entry_refusals),
        });
    }
    let kernel = built.into_kernel().map_err(|report| Vf5BaseMiss::Replay {
        report: Box::new(report),
        entry_refusals: Vec::new(),
    })?;
    // Row-of's original closure uses exactly Ax0. No extra axiom is licensed
    // by a successful replay or a producer-supplied manifest.
    if replay.axioms_admitted.iter().map(String::as_str).collect::<Vec<_>>() != AX0 {
        return Err(Vf5BaseMiss::Axioms(replay.axioms_admitted));
    }
    let report = Vf5BaseReport {
        manifest_sha256,
        environment: kernel.env_digest(),
        captured_modules,
        replay,
    };
    Ok((kernel, report))
}

fn valid_digest(text: &str) -> bool {
    text.len() == 64
        && text.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn validate_manifest(manifest: &Manifest) -> Result<(), Vf5BaseMiss> {
    if manifest.schema != 1
        || manifest.clean_revision != CLEAN_REVISION
        || manifest.lean_world != LEAN_WORLD
        || manifest.source_files.is_empty()
        || manifest.source_files.values().any(|digest| !valid_digest(digest))
        || manifest.modules.is_empty()
        || manifest.modules.len() > MAX_MODULES
    {
        return Err(Vf5BaseMiss::InvalidPackage("unsupported or incomplete VF5 manifest"));
    }
    let mut names = BTreeSet::new();
    for module in &manifest.modules {
        let name = module_name(&module.path)?;
        if !names.insert(name)
            || !valid_digest(&module.base_sha256)
            || [&module.server_sha256, &module.private_sha256, &module.ir_sha256]
                .into_iter()
                .flatten()
                .any(|digest| !valid_digest(digest))
        {
            return Err(Vf5BaseMiss::InvalidPackage("duplicate module or invalid part digest"));
        }
    }
    Ok(())
}

// Structural Name construction avoids display/reparse collisions, numeric
// components, path traversal and platform-dependent filename normalization.
fn module_name(path: &str) -> Result<Name, Vf5BaseMiss> {
    let stem = path
        .strip_suffix(".olean")
        .ok_or(Vf5BaseMiss::InvalidPackage("module must end in .olean"))?;
    let mut name = Name::anon();
    for part in stem.split('/') {
        if part.is_empty()
            || !part.bytes().all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
            || part.as_bytes()[0].is_ascii_digit()
        {
            return Err(Vf5BaseMiss::InvalidPackage("noncanonical module path"));
        }
        name = name.str(part);
    }
    Ok(name)
}

fn plain_root(root: &Path) -> Result<PathBuf, Vf5BaseMiss> {
    let meta = std::fs::symlink_metadata(root).map_err(Vf5BaseMiss::Io)?;
    if !meta.is_dir() || meta.file_type().is_symlink() {
        return Err(Vf5BaseMiss::InvalidPackage("package root is not a plain directory"));
    }
    std::fs::canonicalize(root).map_err(Vf5BaseMiss::Io)
}

fn regular_path(root: &Path, path: &Path) -> Result<PathBuf, &'static str> {
    let relative = path.strip_prefix(root).map_err(|_| "path leaves package root")?;
    let mut current = root.to_owned();
    for part in relative.components() {
        let Component::Normal(part) = part else { return Err("non-normal package path") };
        current.push(part);
        let meta = std::fs::symlink_metadata(&current).map_err(|_| "package path unreadable")?;
        if meta.file_type().is_symlink() || (!meta.is_file() && !meta.is_dir()) {
            return Err("symlink or nonregular package input");
        }
    }
    std::fs::canonicalize(path).map_err(|_| "package path cannot be canonicalized")
}

fn import(root: &Path, manifest: &Manifest) -> Result<(Environment, usize), Vf5BaseMiss> {
    import_with_limits(root, manifest, vf5_capture_limits())
}

fn import_with_limits(
    root: &Path,
    manifest: &Manifest,
    limits: ModuleCaptureLimits,
) -> Result<(Environment, usize), Vf5BaseMiss> {
    let mut inventory = BTreeMap::new();
    for module in &manifest.modules {
        inventory.insert(module_name(&module.path)?, module);
    }
    let refuse = |module: &Name, reason: &str| ImportError::UnsupportedModule {
        module: format!("{module:?}"),
        reason: format!("VF5 package: {reason}"),
    };
    let mut before = |name: &Name, path: &Path, index: usize| {
        let module = inventory.get(name).ok_or_else(|| refuse(name, "unlisted dependency"))?;
        if index != 0 || path != root.join(&module.path) {
            return Err(refuse(name, "module selection differs from inventory"));
        }
        regular_path(root, path).map_err(|reason| refuse(name, reason))?;
        for (path, required) in [
            (path.to_owned(), true),
            (path.with_extension("olean.server"), false),
            (path.with_extension("olean.private"), false),
            (path.with_extension("ir"), false),
        ] {
            check_part_path(root, &path, required).map_err(|reason| refuse(name, reason))?;
        }
        Ok(())
    };
    let mut captured = BTreeSet::new();
    let mut physical = BTreeSet::new();
    let mut capture_bytes = 0_usize;
    let mut check = |name: &Name, path: &Path, bytes: CapturedModuleBytes<'_>| {
        let module = inventory.get(name).ok_or_else(|| refuse(name, "unlisted capture"))?;
        if path != root.join(&module.path)
            || bytes.canonical_path != regular_path(root, path).map_err(|r| refuse(name, r))?
            || !parts_match(module, bytes)
        {
            return Err(refuse(name, "captured identity or part bytes differ from inventory"));
        }
        if !physical.insert(bytes.canonical_path.to_owned()) {
            return Err(refuse(name, "canonical module path has multiple structural names"));
        }
        for part in [Some(bytes.base), bytes.server, bytes.private, bytes.ir].into_iter().flatten() {
            capture_bytes = capture_bytes
                .checked_add(part.len())
                .filter(|size| *size <= MAX_CAPTURE_BYTES)
                .ok_or_else(|| refuse(name, "captured graph exceeds resource bound"))?;
        }
        captured.insert(name.clone());
        Ok(())
    };
    // A new context is owned here; no unchecked preexisting declaration can
    // survive the importer's insert-only duplicate behavior.
    let mut env = Environment::for_lean_replay();
    load_modules_with_deps_checked_with_limits(
        &mut env,
        &[ROOT_MODULE.to_owned()],
        &[root.to_owned()],
        limits,
        &mut before,
        &mut check,
    )
    .map_err(Vf5BaseMiss::Import)?;
    if captured.len() != inventory.len() {
        return Err(Vf5BaseMiss::InvalidPackage("inventory contains modules outside fixed root cone"));
    }
    Ok((env, captured.len()))
}

fn parts_match(module: &Module, bytes: CapturedModuleBytes<'_>) -> bool {
    let matches = |expected: Option<&str>, actual: Option<&[u8]>| match (expected, actual) {
        (None, None) => true,
        (Some(expected), Some(actual)) => {
            actual.len() as u64 <= MAX_PART_BYTES
                && format!("{:x}", Sha256::digest(actual)) == expected
        }
        _ => false,
    };
    matches(Some(&module.base_sha256), Some(bytes.base))
        && matches(module.server_sha256.as_deref(), bytes.server)
        && matches(module.private_sha256.as_deref(), bytes.private)
        && matches(module.ir_sha256.as_deref(), bytes.ir)
}

fn check_part_path(root: &Path, path: &Path, required: bool) -> Result<(), &'static str> {
    match std::fs::symlink_metadata(path) {
        Err(error) if !required && error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(_) => Err("module part unreadable"),
        Ok(meta) => {
            if !meta.is_file() || meta.file_type().is_symlink() || meta.len() > MAX_PART_BYTES {
                return Err("module part is nonregular, symlinked or oversized");
            }
            regular_path(root, path)?;
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn module(base: &[u8]) -> Module {
        Module {
            path: "VF5Check.olean".into(),
            base_sha256: format!("{:x}", Sha256::digest(base)),
            server_sha256: None,
            private_sha256: None,
            ir_sha256: None,
        }
    }

    fn manifest(module: Module) -> Manifest {
        Manifest {
            schema: 1,
            clean_revision: CLEAN_REVISION.into(),
            lean_world: LEAN_WORLD.into(),
            source_files: BTreeMap::from([("VF5Check.lean".into(), "a".repeat(64))]),
            modules: vec![module],
        }
    }

    #[test]
    fn structural_inventory_rejects_aliases_and_duplicate_names() {
        for path in ["../Init.olean", "Init//Core.olean", "Init\\Core.olean", "A.B.olean", "1.olean"] {
            assert!(module_name(path).is_err(), "{path}");
        }
        assert_ne!(module_name("A_B.olean").unwrap(), module_name("A/B.olean").unwrap());
        let mut duplicate = manifest(module(b"input"));
        duplicate.modules.push(module(b"input"));
        assert!(matches!(validate_manifest(&duplicate), Err(Vf5BaseMiss::InvalidPackage(_))));
    }

    #[test]
    fn capture_binds_all_parts_and_absence() {
        let expected = Module {
            server_sha256: Some(format!("{:x}", Sha256::digest(b"server"))),
            private_sha256: Some(format!("{:x}", Sha256::digest(b"private"))),
            ir_sha256: Some(format!("{:x}", Sha256::digest(b"ir"))),
            ..module(b"base")
        };
        let good = CapturedModuleBytes {
            canonical_path: Path::new("/data/VF5Check.olean"),
            base: b"base",
            server: Some(b"server"),
            private: Some(b"private"),
            ir: Some(b"ir"),
        };
        assert!(parts_match(&expected, good));
        for bad in [
            CapturedModuleBytes { base: b"other", ..good },
            CapturedModuleBytes { server: None, ..good },
            CapturedModuleBytes { server: Some(b"changed"), ..good },
            CapturedModuleBytes { private: None, ..good },
            CapturedModuleBytes { private: Some(b"changed"), ..good },
            CapturedModuleBytes { ir: None, ..good },
            CapturedModuleBytes { ir: Some(b"changed"), ..good },
        ] {
            assert!(!parts_match(&expected, bad));
        }
        assert!(!parts_match(&module(b"base"), good), "unlisted present parts are not absence");
    }

    #[test]
    fn real_intake_refuses_changed_bytes_and_unlisted_companion_before_decode() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("VF5Check.olean");
        // Not a Lean file: these controls must fail at the captured-input
        // guard, not be confused with semantic/theorem rejection.
        std::fs::write(&path, b"actual bytes").unwrap();
        let input = manifest(module(b"different bytes"));
        let refused = import(directory.path(), &input).unwrap_err();
        assert!(matches!(refused, Vf5BaseMiss::Import(ImportError::UnsupportedModule { .. })));
        let input = manifest(module(b"actual bytes"));
        std::fs::write(path.with_extension("olean.server"), b"unlisted").unwrap();
        let refused = import(directory.path(), &input).unwrap_err();
        assert!(matches!(refused, Vf5BaseMiss::Import(ImportError::UnsupportedModule { .. })));
    }

    #[test]
    fn real_intake_refuses_oversize_and_symlink_before_capture() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("VF5Check.olean");
        let file = std::fs::File::create(&path).unwrap();
        file.set_len(MAX_PART_BYTES + 1).unwrap();
        assert!(check_part_path(directory.path(), &path, true).is_err());
        #[cfg(unix)]
        {
            let link = directory.path().join("VF5Check.ir");
            std::os::unix::fs::symlink(&path, &link).unwrap();
            assert!(check_part_path(directory.path(), &link, false).is_err());
        }
    }

    #[test]
    fn production_intake_has_no_runtime_pin_door() {
        let directory = tempfile::tempdir().unwrap();
        std::fs::write(directory.path().join(MANIFEST), b"{}").unwrap();
        assert!(matches!(Vf5Reference::load_package(directory.path()), Err(Vf5BaseMiss::UnpinnedPackage(_))));
    }

    #[test]
    fn compiler_setup_respects_earlier_inherited_deadline_before_input_io() {
        let missing = Path::new("/missing-vf5-base-deadline-control");
        let mut stopped = false;
        let _outer = clean_kernel::tc::run_until(Some(Instant::now()), || {
            stopped = matches!(
                Vf5Reference::load_package_until(missing, None),
                Err(Vf5BaseMiss::Stopped(StopCause::WallBackstop)),
            );
        });
        assert!(stopped, "setup must stop before observing the missing package path");
    }

    #[test]
    fn compiler_setup_preserves_an_existing_stopped_scope() {
        let (_, stop) = crate::with_stop_scope(|| {
            crate::note_certify_stop(StopCause::WallBackstop);
            assert!(matches!(
                Vf5Reference::load_package_until(Path::new("/missing-vf5-base-stop-control"), None),
                Err(Vf5BaseMiss::Stopped(StopCause::WallBackstop)),
            ));
        });
        assert_eq!(stop, Some(StopCause::WallBackstop));
    }

    #[test]
    fn preparation_checkpoints_do_not_spend_steps_but_observe_a_spent_scope() {
        let _guard = trust_types::verify_budget::VerifyBudgetGuard::install(None, 1);
        for _ in 0..1024 {
            assert_eq!(preparation_stop(), None);
        }
        assert!(!trust_types::verify_budget::budget_exhausted(),
            "the first real charge still has its original step");
        assert_eq!(preparation_stop(), Some(StopCause::Steps));
    }

    #[test]
    fn preparation_observes_an_earlier_clock_stop_arriving_during_a_walk() {
        assert_eq!(preparation_stop(), None, "paired unstopped preparation");
        let mut stopped = None;
        let _outer = clean_kernel::tc::run_until(Some(Instant::now()), || {
            stopped = preparation_stop();
        });
        assert_eq!(stopped, Some(StopCause::WallBackstop));
        // This checks the shared actual ambient-clock checkpoint, not a
        // source-generated HIR census or an independently enabled VF5 base.
    }
}

#[cfg(test)]
mod capture_limits_tests;

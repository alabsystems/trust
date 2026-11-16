//! Trust: per-user storage for confined dependencies with stable source paths.

use std::fs;
use std::path::{Path, PathBuf};

use anyhow::bail;
use cargo_util::Sha256;

use super::{CompileMode, CrateType, Unit, unit_graph::UnitGraph};
use crate::CargoResult;
use crate::util::data_structures::HashSet;
use crate::util::log_message::SharedDependencyExclusion;
use crate::workspace::{GitReference, SourceId};

/// Git checkout paths use abbreviated object names and ordinary SourceId
/// hashing omits the precise revision. Shared actions require the resolved,
/// full object name independently of both of those lookup accelerators.
pub(super) fn resolved_git_commit(source: SourceId) -> Option<&'static str> {
    if !source.is_git() {
        return None;
    }
    let revision = source.precise_git_fragment()?;
    (revision.len() == 40 && revision.bytes().all(|byte| byte.is_ascii_hexdigit()))
        .then_some(revision)
}

pub(super) fn git_source_identity(source: SourceId) -> Option<String> {
    let revision = resolved_git_commit(source)?;
    let (kind, selector) = match source.git_reference()? {
        GitReference::Tag(value) => ("tag", value.as_str()),
        GitReference::Branch(value) => ("branch", value.as_str()),
        GitReference::Rev(value) => ("rev", value.as_str()),
        GitReference::DefaultBranch => ("default", ""),
    };
    let mut hash = Sha256::new();
    for field in [
        "targo-shared-git-source-v1",
        source.url().as_str(),
        kind,
        selector,
        revision,
    ] {
        hash.update(&(field.len() as u64).to_le_bytes());
        hash.update(field.as_bytes());
    }
    Some(hash.finish_hex())
}

pub(super) fn eligible_units(graph: &UnitGraph, roots: &[Unit], workspace: &Path) -> HashSet<Unit> {
    let candidates: Vec<_> = graph
        .keys()
        .filter(|unit| direct_exclusion(unit, roots, workspace).is_none())
        .cloned()
        .collect();
    let mut selected = HashSet::default();
    loop {
        let previous = selected.len();
        for unit in &candidates {
            if graph[unit].iter().all(|dep| selected.contains(&dep.unit)) {
                selected.insert(unit.clone());
            }
        }
        if selected.len() == previous {
            return selected;
        }
    }
}

/// Use the SAME predicate for selection and diagnostic exclusion reasons.
/// The selected set still requires the dependency closure above.
pub(super) fn direct_exclusion(
    unit: &Unit,
    roots: &[Unit],
    workspace: &Path,
) -> Option<SharedDependencyExclusion> {
    use SharedDependencyExclusion::*;
    let source = unit.pkg.package_id().source_id();
    if !(source.is_registry()
        || resolved_git_commit(source).is_some()
        || (source.is_path() && !unit.pkg.root().starts_with(workspace)))
    {
        return Some(SourceNotShareable);
    }
    if roots
        .iter()
        .any(|root| root.pkg.package_id() == unit.pkg.package_id())
    {
        return Some(RequestedPackage);
    }
    if !unit.target.is_lib() || unit.target.is_custom_build() {
        return Some(NonLibrary);
    }
    if unit.artifact.is_true() {
        return Some(ArtifactDependency);
    }
    if unit.target.proc_macro() {
        return Some(ProceduralMacro);
    }
    if unit
        .pkg
        .targets()
        .iter()
        .any(|target| target.is_custom_build())
    {
        return Some(BuildScriptPackage);
    }
    if unit.mode.is_any_test() || !(unit.mode.is_check() || unit.mode == CompileMode::Build) {
        return Some(UnsupportedMode);
    }
    if !unit
        .target
        .rustc_crate_types()
        .iter()
        .all(|kind| matches!(kind, CrateType::Lib | CrateType::Rlib))
    {
        return Some(UnsupportedCrateType);
    }
    None
}

pub(super) fn log_policy(build: &super::BuildContext<'_, '_>) {
    use crate::util::log_message::{
        LogMessage, SHARED_DEPENDENCY_POLICY_VERSION, SharedDependencyDecision,
    };
    let Some(logger) = build.logger else { return };
    let enabled = build.shared_dependency_root.is_some();
    logger.log(LogMessage::SharedDependencyPolicy {
        version: SHARED_DEPENDENCY_POLICY_VERSION,
        enabled,
    });
    if !enabled {
        return;
    }
    // Stable native indices preserve duplicate package labels and edge identity.
    let mut units: Vec<_> = build.unit_to_index.iter().collect();
    units.sort_by_key(|(_, index)| **index);
    for (unit, index) in units {
        let decision = if build.shared_dependency_units.contains(unit) {
            SharedDependencyDecision::Eligible {}
        } else if let Some(reason) = direct_exclusion(unit, &build.roots, build.ws.root()) {
            SharedDependencyDecision::Excluded { reason }
        } else {
            let mut dependencies: Vec<_> = build.unit_graph[unit]
                .iter()
                .filter(|dep| !build.shared_dependency_units.contains(&dep.unit))
                .map(|dep| build.unit_to_index[&dep.unit])
                .collect();
            dependencies.sort_unstable();
            dependencies.dedup();
            SharedDependencyDecision::DependencyBlocked { dependencies }
        };
        logger.log(LogMessage::SharedDependencyDecision {
            index: *index,
            decision,
        });
    }
}

pub(super) fn storage_root(home: &Path) -> CargoResult<PathBuf> {
    let mut root = home.canonicalize()?;
    private_parent(&root)?;
    for name in ["trust", "native-dependencies-v1"] {
        root.push(name);
        match fs::symlink_metadata(&root) {
            Ok(_) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                let mut builder = fs::DirBuilder::new();
                #[cfg(unix)]
                {
                    use std::os::unix::fs::DirBuilderExt;
                    builder.mode(0o700);
                }
                match builder.create(&root) {
                    Ok(()) => {}
                    Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
                    Err(error) => return Err(error.into()),
                }
            }
            Err(error) => return Err(error.into()),
        }
        private_parent(&root)?;
    }
    Ok(root)
}

fn private_parent(path: &Path) -> CargoResult<()> {
    let metadata = fs::symlink_metadata(path)?;
    if !metadata.is_dir() || metadata.file_type().is_symlink() {
        bail!(
            "shared dependency storage requires a plain directory: {}",
            path.display()
        );
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        if metadata.uid() != unsafe { libc::geteuid() } || metadata.mode() & 0o022 != 0 {
            bail!(
                "shared dependency storage must be owned by this user and not writable by other users: {}",
                path.display()
            );
        }
        crate::util::process_authority::validate_user_cache_directory(path)?;
    }
    #[cfg(target_os = "macos")]
    {
        use std::os::unix::ffi::OsStrExt;
        let path = std::ffi::CString::new(path.as_os_str().as_bytes())?;
        let mut mount = std::mem::MaybeUninit::<libc::statfs>::zeroed();
        // SAFETY: the path is NUL-terminated and statfs writes one full struct.
        if unsafe { libc::statfs(path.as_ptr(), mount.as_mut_ptr()) } != 0 {
            return Err(std::io::Error::last_os_error().into());
        }
        let mount = unsafe { mount.assume_init() };
        if mount.f_flags & libc::MNT_LOCAL as u32 == 0 {
            bail!("shared dependency storage requires a local filesystem with kernel file locks");
        }
    }
    Ok(())
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::os::unix::fs::{MetadataExt, PermissionsExt};

    #[test]
    fn git_identity_requires_and_binds_the_full_resolved_revision() {
        let source = SourceId::for_git(
            &"https://example.invalid/library".parse().unwrap(),
            GitReference::DefaultBranch,
        )
        .unwrap();
        assert!(git_source_identity(source).is_none());
        assert!(git_source_identity(source.with_git_precise(Some("abcdef0".into()))).is_none());
        assert!(git_source_identity(source.with_git_precise(Some("z".repeat(40)))).is_none());
        let first = source.with_git_precise(Some("1".repeat(40)));
        let second = source.with_git_precise(Some("2".repeat(40)));
        // Ordinary package/source equality deliberately cannot distinguish these.
        assert_eq!(first, second);
        assert_ne!(git_source_identity(first), git_source_identity(second));
    }

    #[test]
    fn git_identity_separates_url_query_and_reference_selector() {
        let query = SourceId::for_git(
            &"https://example.invalid/library?branch=next"
                .parse()
                .unwrap(),
            GitReference::DefaultBranch,
        )
        .unwrap()
        .with_git_precise(Some("1".repeat(40)));
        let branch = SourceId::for_git(
            &"https://example.invalid/library".parse().unwrap(),
            GitReference::Branch("next".into()),
        )
        .unwrap()
        .with_git_precise(Some("1".repeat(40)));
        assert_ne!(git_source_identity(query), git_source_identity(branch));
    }

    #[test]
    fn storage_uses_one_owned_private_namespace() {
        let home = tempfile::tempdir().unwrap();
        let root = storage_root(home.path()).unwrap();
        assert_eq!(
            root,
            home.path()
                .canonicalize()
                .unwrap()
                .join("trust/native-dependencies-v1")
        );
        assert_eq!(fs::metadata(&root).unwrap().mode() & 0o077, 0);
        assert_eq!(storage_root(home.path()).unwrap(), root);
    }

    #[test]
    fn redirected_or_shared_writable_storage_is_refused() {
        let home = tempfile::tempdir().unwrap();
        let outside = tempfile::tempdir().unwrap();
        std::os::unix::fs::symlink(outside.path(), home.path().join("trust")).unwrap();
        assert!(storage_root(home.path()).is_err());
        assert!(!outside.path().join("native-dependencies-v1").exists());
        fs::remove_file(home.path().join("trust")).unwrap();
        fs::set_permissions(home.path(), fs::Permissions::from_mode(0o777)).unwrap();
        assert!(storage_root(home.path()).is_err());
    }
}

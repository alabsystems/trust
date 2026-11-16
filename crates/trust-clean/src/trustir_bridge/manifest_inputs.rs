//! Manifest-selected module identity at both resolution and captured-byte use.
//! This authenticates imported-context inputs, never a proof/kernel grade.
use clean_olean::{CapturedModuleBytes, ImportError, LoadSummary};

use super::*;

#[derive(Debug)]
pub(super) struct SelectedModule {
    root: PathBuf,
    path: PathBuf,
    canonical: PathBuf,
    sha256: String,
}
fn invalid(detail: impl Into<String>) -> BridgeGateError {
    BridgeGateError::Import { detail: format!("verified manifest selection: {}", detail.into()) }
}
fn refused(module: &Name, detail: impl Into<String>) -> ImportError {
    ImportError::UnsupportedModule {
        module: format!("{module:?}"),
        reason: format!("verified manifest selection: {}", detail.into()),
    }
}
/// Structural module identity, never Name display/reparse or path normalization.
pub(super) fn module_key(rel: &str) -> Result<Name, BridgeGateError> {
    if rel.contains(['\\', '\0', ':']) || !rel.ends_with(".olean") {
        return Err(invalid(format!("unsafe or unsupported module inventory key {rel:?}")));
    }
    let mut parts = rel.split('/').collect::<Vec<_>>();
    if parts
        .iter()
        .any(|part| part.is_empty() || matches!(*part, "." | "..") || part.ends_with(['.', ' ']))
    {
        return Err(invalid(format!("unsafe module inventory key {rel:?}")));
    }
    let last = parts.pop().ok_or_else(|| invalid("empty module key"))?;
    let stem = last.strip_suffix(".olean").ok_or_else(|| invalid("module suffix absent"))?;
    if stem.is_empty() {
        return Err(invalid("empty module basename"));
    }
    parts.push(stem);
    Ok(parts.into_iter().fold(Name::anon(), |parent, part| parent.str(part)))
}
/// Refuse symlinks in the entire selected root/relative path before file reads.
fn regular_path(root: &Path, path: &Path) -> Result<PathBuf, String> {
    let relative =
        path.strip_prefix(root).map_err(|_| "selected path leaves its verified root".to_owned())?;
    let meta = std::fs::symlink_metadata(root).map_err(|e| format!("root metadata: {e}"))?;
    if meta.file_type().is_symlink() || !meta.is_dir() {
        return Err("verified root is not a plain directory".into());
    }
    let mut current = root.to_owned();
    let parts = relative.components().collect::<Vec<_>>();
    if parts.is_empty() {
        return Err("module path is the root".into());
    }
    for (i, part) in parts.iter().enumerate() {
        let std::path::Component::Normal(name) = part else {
            return Err("non-normal module path".into());
        };
        current.push(name);
        let meta = std::fs::symlink_metadata(&current)
            .map_err(|e| format!("selected metadata {}: {e}", current.display()))?;
        if meta.file_type().is_symlink()
            || (i + 1 == parts.len() && !meta.is_file())
            || (i + 1 < parts.len() && !meta.is_dir())
        {
            return Err(format!("selected path is symlink/nonregular: {}", current.display()));
        }
    }
    std::fs::canonicalize(path).map_err(|e| format!("selected canonical path: {e}"))
}
pub(super) fn require_unambiguous_paths(
    selected: &BTreeMap<Name, SelectedModule>,
) -> Result<(), BridgeGateError> {
    let mut names = BTreeMap::new();
    for (name, entry) in selected {
        if let Some(previous) = names.insert(&entry.canonical, name) {
            if previous != name {
                return Err(invalid(format!(
                    "ambiguous physical module aliases: {previous:?} and {name:?}"
                )));
            }
        }
    }
    Ok(())
}
pub(super) fn select(
    root: &Path,
    path: PathBuf,
    digest: &str,
) -> Result<SelectedModule, BridgeGateError> {
    let canonical = regular_path(root, &path).map_err(invalid)?;
    Ok(SelectedModule { root: root.to_owned(), path, canonical, sha256: digest.into() })
}
/// A manifest root itself is ordinary package data, never an allowed redirect.
pub(super) fn canonical_root(dir: &Path) -> Result<PathBuf, BridgeGateError> {
    let meta = std::fs::symlink_metadata(dir).map_err(|e| invalid(format!("package root: {e}")))?;
    if meta.file_type().is_symlink() || !meta.is_dir() {
        return Err(invalid("package root is symlink/non-directory"));
    }
    let root = std::fs::canonicalize(dir).map_err(|e| invalid(e.to_string()))?;
    let manifest = root.join("MANIFEST.toml");
    // Preserve the old ManifestUnreadable diagnostic for absence/I/O failure;
    // a PRESENT symlink or nonregular manifest is an explicit new refusal.
    if std::fs::symlink_metadata(&manifest).is_ok() {
        regular_path(&root, &manifest).map_err(invalid)?;
    }
    Ok(root)
}
fn check_sidecar_paths(module: &Name, selected: &SelectedModule) -> Result<(), ImportError> {
    for extension in ["olean.server", "olean.private", "ir"] {
        let path = selected.path.with_extension(extension);
        match std::fs::symlink_metadata(&path) {
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => return Err(refused(module, format!("companion metadata: {error}"))),
            Ok(_) => {
                regular_path(&selected.root, &path).map_err(|e| refused(module, e))?;
            }
        }
    }
    Ok(())
}
pub(super) fn load(
    env: &mut Environment,
    roots: &[String],
    trustir: &VerifiedTree,
    core: &VerifiedTree,
) -> Result<Vec<LoadSummary>, BridgeGateError> {
    // Importing into a previously populated context can preserve unchecked
    // declarations through insert-only duplicate skipping. The bridge owns a
    // fresh imported context; no old environment/cache name is authority.
    if env.constants().next().is_some()
        || env.inductives().next().is_some()
        || env.constructors().next().is_some()
        || env.recursors().next().is_some()
        || env.quotients().next().is_some()
    {
        return Err(invalid("manifest import requires the actual fresh bridge environment"));
    }
    let mut inventory: BTreeMap<Name, &SelectedModule> = BTreeMap::new();
    for tree in [trustir, core] {
        for (name, selected) in &tree.selected {
            if inventory.insert((*name).clone(), selected).is_some() {
                return Err(invalid(format!("ambiguous module across manifests: {name:?}")));
            }
        }
    }
    let mut paths = trustir.search_dirs();
    paths.extend(core.search_dirs());
    let mut before = |module: &Name, path: &Path, _index: usize| {
        let selected = inventory
            .get(module)
            .ok_or_else(|| refused(module, "module absent from verified inventory"))?;
        if path != selected.path.as_path() {
            return Err(refused(
                module,
                format!(
                    "actual selected path {} differs from manifest-selected {}",
                    path.display(),
                    selected.path.display()
                ),
            ));
        }
        if regular_path(&selected.root, path).map_err(|e| refused(module, e))? != selected.canonical
        {
            return Err(refused(module, "selected canonical path changed"));
        }
        check_sidecar_paths(module, selected)
    };
    let mut captured = |module: &Name, path: &Path, bytes: CapturedModuleBytes<'_>| {
        let selected = inventory
            .get(module)
            .ok_or_else(|| refused(module, "captured module absent from inventory"))?;
        if path != selected.path.as_path() || bytes.canonical_path != selected.canonical.as_path() {
            return Err(refused(module, "captured module path differs from verified selection"));
        }
        regular_path(&selected.root, path).map_err(|e| refused(module, e))?;
        if bytes.server.is_some() || bytes.private.is_some() || bytes.ir.is_some() {
            return Err(refused(module, "unmanifested captured companion/IR bytes"));
        }
        let mut digest = Sha256::new();
        digest.update(bytes.base);
        let digest = format!("{:x}", digest.finalize());
        if digest != selected.sha256 {
            return Err(refused(module, "captured base sha256 differs from verified manifest"));
        }
        Ok(())
    };
    clean_olean::load_modules_with_deps_checked(env, roots, &paths, &mut before, &mut captured)
        .map_err(|error| BridgeGateError::Import { detail: format!("{error:?}") })
}

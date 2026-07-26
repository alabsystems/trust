// targo-trust project-root resolution.
//
// Normal crate-mode flows should anchor config/cache/diff/init behavior to the
// intended crate root, not whatever directory the user happened to launch from.

use std::env;
use std::path::{Path, PathBuf};

use crate::cli::SubcommandArgs;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ResolvedProjectRoot {
    pub(crate) root: PathBuf,
    pub(crate) manifest_path: Option<PathBuf>,
    pub(crate) single_file_path: Option<PathBuf>,
}

pub(crate) fn resolve_project_root(sub_args: &SubcommandArgs) -> ResolvedProjectRoot {
    resolve_project_root_from(sub_args, &current_dir_or_dot())
}

pub(crate) fn resolve_project_root_from(
    sub_args: &SubcommandArgs,
    cwd: &Path,
) -> ResolvedProjectRoot {
    if let Some(manifest_path) = sub_args.manifest_path.as_deref() {
        let manifest_path = absolutize_from(Path::new(manifest_path), cwd);
        let root =
            manifest_path.parent().map(Path::to_path_buf).unwrap_or_else(|| cwd.to_path_buf());
        return ResolvedProjectRoot {
            root,
            manifest_path: Some(manifest_path),
            single_file_path: None,
        };
    }

    if let Some(single_file_path) = sub_args.single_file_path() {
        let single_file_path = absolutize_from(Path::new(single_file_path), cwd);
        let root =
            single_file_path.parent().map(Path::to_path_buf).unwrap_or_else(|| cwd.to_path_buf());
        return ResolvedProjectRoot {
            root,
            manifest_path: None,
            single_file_path: Some(single_file_path),
        };
    }

    if let Some(manifest_path) = find_manifest_in_ancestors(cwd) {
        let root =
            manifest_path.parent().map(Path::to_path_buf).unwrap_or_else(|| cwd.to_path_buf());
        return ResolvedProjectRoot {
            root,
            manifest_path: Some(manifest_path),
            single_file_path: None,
        };
    }

    ResolvedProjectRoot { root: cwd.to_path_buf(), manifest_path: None, single_file_path: None }
}

fn current_dir_or_dot() -> PathBuf {
    env::current_dir().unwrap_or_else(|_| PathBuf::from("."))
}

fn absolutize_from(path: &Path, cwd: &Path) -> PathBuf {
    if path.is_absolute() { path.to_path_buf() } else { cwd.join(path) }
}

/// Walk up for the manifest that governs `path`, preferring the native
/// `Targo.toml` over the compatibility `Cargo.toml` in the same directory —
/// the same order targo's own root-manifest discovery uses. A project that
/// ships only a native manifest is otherwise invisible here, which would
/// silently anchor its config, cache, and reports to the launch directory.
fn find_manifest_in_ancestors(path: &Path) -> Option<PathBuf> {
    let start = if path.is_file() { path.parent()? } else { path };
    start.ancestors().find_map(|ancestor| {
        crate::config::MANIFEST_NAMES
            .iter()
            .map(|name| ancestor.join(name))
            .find(|candidate| candidate.is_file())
    })
}

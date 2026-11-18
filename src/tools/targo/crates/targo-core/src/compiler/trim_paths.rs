//! Path prefix remapping for [RFC 3127] `trim-paths`.
//!
//! [RFC 3127]: https://rust-lang.github.io/rfcs/3127-trim-paths.html

use std::collections::BTreeMap;
use std::collections::btree_map::Entry;
use std::ffi::OsString;
use std::io::Write;
use std::path::Path;
use std::path::PathBuf;

use cargo_util::ProcessBuilder;
use cargo_util_schemas::manifest::TomlTrimPaths;
use serde::Serialize;
use tracing::debug;

use super::Unit;
use super::{BuildContext, BuildRunner};
use crate::util::data_structures::HashSet;
use crate::util::errors::CargoResult;
use crate::util::hex;
use crate::util::path_args;

/// The current version of the unremap file.
const CURRENT_UNREMAP_VERSION: u8 = 1;

/// Filename suffix of the unremap file.
pub(crate) const UNREMAP_SUFFIX: &str = ".trim-paths.json";

/// This is an internal contract with rustc bootstrap,
/// which needs workspace sources remapped to `/rust{c,-dev}/<sha>`.
///
/// See <https://github.com/rust-lang/cargo/issues/17309>.
pub(crate) const WS_REMAP_ENV: &str = "__CARGO_RUSTC_BOOTSTRAP_WS_REMAP";

/// A single `<from>=<to>` remap rule.
type RemapPair = (PathBuf, String);

// Trust: carry the actual package-rule classification with its emitted rules,
// so fingerprinting cannot invent a different workspace-applicability test.
enum PackageRemap {
    Dependency(Vec<RemapPair>),
    Workspace(Vec<RemapPair>),
}

impl PackageRemap {
    fn into_pairs(self) -> Vec<RemapPair> {
        match self {
            Self::Dependency(pairs) | Self::Workspace(pairs) => pairs,
        }
    }
}

// Trust: command generation, build-script environment and fingerprinting use
// the same scope decision. Rustdoc supports only diagnostics (the all scope).
pub(crate) fn remap_enabled(trim_paths: &TomlTrimPaths, rustdoc: bool) -> bool {
    !trim_paths.is_none() && (!rustdoc || matches!(trim_paths, TomlTrimPaths::All))
}

// Trust: key only the workspace rules this unit actually receives. Registry
// and git packages usually receive their own rules, independent of WS_REMAP_ENV;
// vendored/abnormal locations still follow the production package classifier.
// Preserve relative rules and every destination. Absolute local source roots
// remain relocatable, as the existing fingerprint/source-path keys require.
pub(crate) fn workspace_remap_fingerprint(
    build_runner: &BuildRunner<'_, '_>,
    unit: &Unit,
) -> Option<Vec<(Option<PathBuf>, String)>> {
    workspace_remap_fingerprint_context(build_runner.bcx, unit)
}

pub(crate) fn workspace_remap_fingerprint_context(
    bcx: &BuildContext<'_, '_>,
    unit: &Unit,
) -> Option<Vec<(Option<PathBuf>, String)>> {
    let rustdoc = unit.mode.is_doc() || unit.mode.is_doc_scrape();
    if !remap_enabled(&unit.profile.trim_paths, rustdoc) {
        return None;
    }
    match package_remap(bcx, unit) {
        PackageRemap::Dependency(_) => None,
        PackageRemap::Workspace(pairs) => Some(
            pairs
                .into_iter()
                .map(|(from, to)| (from.is_relative().then_some(from), to))
                .collect(),
        ),
    }
}

/// Like [`trim_paths_args`] but for rustdoc invocations.
pub(crate) fn trim_paths_args_rustdoc(
    cmd: &mut ProcessBuilder,
    build_runner: &BuildRunner<'_, '_>,
    unit: &Unit,
    trim_paths: &TomlTrimPaths,
) -> CargoResult<()> {
    // rustdoc supports diagnostics trimming only.
    if !remap_enabled(trim_paths, true) {
        return Ok(());
    }

    for pair in trim_paths_remap(build_runner, unit) {
        let mut arg = OsString::from("--remap-path-prefix=");
        arg.push(pair);
        cmd.arg(arg);
    }

    Ok(())
}

/// Generates the `--remap-path-scope` and `--remap-path-prefix` for [RFC 3127].
/// See also the [`trim-paths`] profile option.
///
/// [RFC 3127]: https://rust-lang.github.io/rfcs/3127-trim-paths.html
/// [`trim-paths`]: https://doc.rust-lang.org/cargo/reference/profiles.html#trim-paths
pub(crate) fn trim_paths_args(
    cmd: &mut ProcessBuilder,
    bcx: &BuildContext<'_, '_>,
    unit: &Unit,
    trim_paths: &TomlTrimPaths,
) -> CargoResult<()> {
    if !remap_enabled(trim_paths, false) {
        return Ok(());
    }

    cmd.arg(format!("--remap-path-scope={trim_paths}"));

    for pair in trim_paths_remap_context(bcx, unit) {
        let mut arg = OsString::from("--remap-path-prefix=");
        arg.push(pair);
        cmd.arg(arg);
    }

    Ok(())
}

/// Trust (DC-18b): a shared member's path arguments, whatever its profile's
/// `trim-paths`: every scope remaps the workspace directory to `.` and the
/// sysroot as trim-paths does, and `-Ztrust-path-free` refuses metadata that
/// still names a host path. The build directory is not remapped: a shared
/// member reads only the store, and its command must not name the checkout's
/// build directory (`action_command::CommandInputs::capture_relocated`).
pub(crate) fn shared_member_args(
    cmd: &mut ProcessBuilder,
    bcx: &BuildContext<'_, '_>,
    unit: &Unit,
) {
    cmd.arg("--remap-path-scope=all");
    for pair in package_remap(bcx, unit)
        .into_pairs()
        .into_iter()
        .chain([sysroot_remap(bcx, unit)])
    {
        let mut arg = OsString::from("--remap-path-prefix=");
        arg.push(join_remap(pair));
        cmd.arg(arg);
    }
    cmd.arg("-Ztrust-path-free");
}

/// Computes the `<from>=<to>` path remap pairs for [RFC 3127] trim-paths.
///
/// Order of `--remap-path-prefix` flags is important for `-Zbuild-std`.
/// We want to show `/rustc/<hash>/library/std` instead of `std-0.0.0`.
///
/// | Category     | From                                             | To                                 |
/// |--------------|--------------------------------------------------|------------------------------------|
/// | Sysroot      | `<sysroot>/lib/rustlib/src/rust`                 | `/rustc/<commit-hash>`             |
/// | Registry dep | `$CARGO_HOME/registry/src/<registry-dir>`        | `/cargo/registry/<registry-id>`    |
/// | Git dep      | `$CARGO_HOME/git/checkouts/<repo-dir>/<rev-dir>` | `/cargo/git/<git-source-id>/<rev>` |
/// | Workspace    | `<workspace-root>`                               | `.` (workspace-relative)           |
/// | Path dep†    | `<pkg-root>`                                     | `/cargo/deps/<name>-<version>`     |
/// | Vendored     | `<pkg-root>` (by file location)                  | workspace or path rules above      |
/// | Build dir    | `<build-dir>`                                    | `/cargo/build-dir`                 |
///
/// **†**: path dependencies outside the workspace and other uncategorized dependencies.
///
/// [RFC 3127]: https://rust-lang.github.io/rfcs/3127-trim-paths.html
pub(crate) fn trim_paths_remap(build_runner: &BuildRunner<'_, '_>, unit: &Unit) -> Vec<OsString> {
    trim_paths_remap_context(build_runner.bcx, unit)
}

fn trim_paths_remap_context(bcx: &BuildContext<'_, '_>, unit: &Unit) -> Vec<OsString> {
    let mut remaps = Vec::with_capacity(4);
    remaps.extend(
        package_remap(bcx, unit)
            .into_pairs()
            .into_iter()
            .map(join_remap),
    );
    remaps.push(join_remap(build_dir_remap(bcx)));
    remaps.push(join_remap(sysroot_remap(bcx, unit)));
    remaps
}

fn join_remap((from, to): RemapPair) -> OsString {
    let mut remap = OsString::with_capacity(from.as_os_str().len() + 1 + to.len());
    remap.push(from);
    remap.push("=");
    remap.push(to);
    remap
}

/// Path prefix remap rules for sysroot.
///
/// This remap logic aligns with rustc:
/// <https://github.com/rust-lang/rust/blob/c2ef3516/src/bootstrap/src/lib.rs#L1113-L1116>
fn sysroot_remap(bcx: &BuildContext<'_, '_>, unit: &Unit) -> RemapPair {
    // See also `detect_sysroot_src_path()`.
    let mut sysroot = bcx.target_data.info(unit.kind).sysroot.clone();
    sysroot.push("lib");
    sysroot.push("rustlib");
    sysroot.push("src");
    sysroot.push("rust");

    let rustc = bcx.rustc();
    let to = match rustc.commit_hash.as_ref() {
        Some(commit_hash) => format!("/rustc/{commit_hash}"),
        None => format!("/rustc/{}", rustc.version),
    };
    (sysroot, to)
}

/// Path prefix remap rules for dependencies.
fn package_remap(bcx: &BuildContext<'_, '_>, unit: &Unit) -> PackageRemap {
    let pkg_root = unit.pkg.root();
    let ws_root = bcx.ws.root();
    let source_id = unit.pkg.package_id().source_id();

    if source_id.is_git() {
        if let Some((from, rev)) = git_checkout(bcx, pkg_root) {
            const GIT_OID_LEN: usize = 7; // This matches MIN_ABBREV_LEN in git source
            let repo = hex::short_hash(source_id.canonical_url());
            let rev = &rev[..rev.len().min(GIT_OID_LEN)];
            return PackageRemap::Dependency(vec![(
                from.to_path_buf(),
                format!("/cargo/git/{repo}/{rev}"),
            )]);
        }
    } else if source_id.is_registry() {
        let registry_src = bcx.gctx.registry_source_path();
        let registry_src = registry_src.as_path_unlocked();
        let from = pkg_root.parent().unwrap();
        if from.starts_with(registry_src) {
            let registry = hex::short_hash(&source_id);
            return PackageRemap::Dependency(vec![(
                from.to_path_buf(),
                format!("/cargo/registry/{registry}"),
            )]);
        }
    }

    // Handle path local dependencies and abnormal reg/git deps source location.
    if pkg_root.strip_prefix(ws_root).is_ok() {
        PackageRemap::Workspace(workspace_remap(bcx, unit))
    } else {
        let from = pkg_root.to_path_buf();
        let to = format!("/cargo/deps/{}-{}", unit.pkg.name(), unit.pkg.version());
        PackageRemap::Dependency(vec![(from, to)])
    }
}

/// Path prefix remap rules for dependencies within workspaces.
fn workspace_remap(bcx: &BuildContext<'_, '_>, unit: &Unit) -> Vec<RemapPair> {
    let ws_root = bcx.ws.root();
    // rustc working directory is usually workspace root.
    // However, when `-Zroot-dir` is set, it may not be.
    // We may need to remap to that otherwise debuginfo like `DW_AT_comp_dir`
    // would point to rustc working directory,
    // and won't be remapped by workspace root.
    let (src, rustc_workdir) = path_args(bcx.ws, unit);

    let custom_prefix = bcx
        .gctx
        .get_env(WS_REMAP_ENV)
        .ok()
        .filter(|prefix| !prefix.is_empty());

    // When custom prefix for workspace remap is set via `WS_REMAP_ENV`,
    // an extra remap rule for relative member paths is required
    // for correctly adding prefix to member paths.
    //
    // For more, see <https://github.com/rust-lang/cargo/pull/17366>
    let relative_remap = if let Some(prefix) = custom_prefix
        && src.is_relative()
        && let Ok(rel) = unit.pkg.root().strip_prefix(&rustc_workdir)
        && !rel.is_empty()
    {
        let mut rel_to = prefix.to_owned();
        for comp in rel.components() {
            // e.g., library -> <custom-prefix>/library
            rel_to.push('/');
            rel_to.push_str(&comp.as_os_str().to_string_lossy());
        }
        Some((rel.to_path_buf(), rel_to))
    } else {
        None
    };

    let from = if ws_root.starts_with(&rustc_workdir) {
        rustc_workdir
    } else {
        ws_root.to_path_buf()
    };

    let absolute_remap = (from, custom_prefix.unwrap_or(".").to_owned());

    let mut remaps = vec![absolute_remap];
    remaps.extend(relative_remap);
    remaps
}

/// Finds the checkout root and revision directory name of a git dependency.
///
/// This is built under this layout: `$CARGO_HOME/git/checkouts/<repo>-<hash>[-shallow]/<rev>`.
///
/// `None` when the package does not live under the global git checkouts directory,
/// for example a vendored git dependency.
fn git_checkout<'a>(bcx: &BuildContext<'_, '_>, pkg_root: &'a Path) -> Option<(&'a Path, &'a str)> {
    let checkouts = bcx.gctx.git_checkouts_path();
    let checkouts = checkouts.as_path_unlocked();
    let rel = pkg_root.strip_prefix(checkouts).ok()?;
    let mut components = rel.components();
    let (_repo, rev) = (components.next()?, components.next()?);
    let rev = rev.as_os_str().to_str()?;
    let checkout_root = pkg_root.ancestors().nth(components.count())?;
    Some((checkout_root, rev))
}

/// Remap all paths pointing to `build.build-dir`,
/// i.e., `[BUILD_DIR]/debug/deps/foo-[HASH].dwo` would be remapped to
/// `/cargo/build-dir/debug/deps/foo-[HASH].dwo`
/// (note the `/cargo/build-dir` prefix).
///
/// This covers scenarios like:
///
/// * Build script generated code. For example, a build script may call `file!`
///   macros, and the associated crate uses [`include!`] to include the expanded
///   [`file!`] macro in-place via the `OUT_DIR` environment.
/// * On Linux, `DW_AT_GNU_dwo_name` that contains paths to split debuginfo
///   files (dwp and dwo).
fn build_dir_remap(bcx: &BuildContext<'_, '_>) -> RemapPair {
    let from = bcx.ws.build_dir().into_path_unlocked();
    let to = "/cargo/build-dir".to_owned();
    (from, to)
}

/// On-disk schema of the unremap file.
#[derive(Serialize)]
#[serde(rename_all = "snake_case")]
struct UnremapFile<'a> {
    v: u8,
    rust_version: &'a str,
    workspace_root: &'a Path,
    remaps: Vec<Remap<'a>>,
}

#[derive(Serialize)]
#[serde(rename_all = "snake_case")]
struct Remap<'a> {
    from: &'a str,
    to: &'a Path,
}

/// Whether an unremap file is worth emitting beside its artifacts.
pub(crate) fn should_emit_unremap_file(unit: &Unit) -> bool {
    // The unremap file is a debug companion like a dSYM or PDB.
    // Without debuginfo there is nothing worth unmapping.
    if !unit.profile.debuginfo.is_turned_on() {
        return false;
    }

    match unit.profile.trim_paths {
        TomlTrimPaths::None => false,
        TomlTrimPaths::Object | TomlTrimPaths::All => true,
    }
}

/// Writes the unremap file for a unit's final artifacts.
pub(crate) fn write_unremap_file(
    mut out: impl Write,
    build_runner: &BuildRunner<'_, '_>,
    unit: &Unit,
) -> CargoResult<()> {
    let mut remaps = BTreeMap::new();

    let mut insert = |(from, to): RemapPair| match remaps.entry(to) {
        Entry::Vacant(entry) => {
            entry.insert(from);
        }
        Entry::Occupied(entry) if *entry.get() != from => {
            debug!(
                "conflicting unremap records for `{}`: `{}` and `{}`",
                entry.key(),
                entry.get().display(),
                from.display(),
            );
        }
        Entry::Occupied(_) => {}
    };

    insert(sysroot_remap(build_runner.bcx, unit));
    insert(build_dir_remap(build_runner.bcx));

    let mut seen = HashSet::default();
    let mut stack = vec![unit.clone()];
    while let Some(unit) = stack.pop() {
        if !seen.insert(unit.clone()) {
            continue;
        }
        for dep in build_runner.unit_deps(&unit) {
            stack.push(dep.unit.clone());
        }
        for (from, to) in package_remap(build_runner.bcx, &unit).into_pairs() {
            // No need to emit records for relative rules as
            // the absolute workspace record already covers their prefixes.
            if from.is_relative() {
                continue;
            }
            insert((from, to));
        }
    }

    let rust_version = build_runner.bcx.rustc().version.to_string();
    let file = UnremapFile {
        v: CURRENT_UNREMAP_VERSION,
        rust_version: &rust_version,
        workspace_root: build_runner.bcx.ws.root(),
        remaps: remaps.iter().map(|(from, to)| Remap { from, to }).collect(),
    };
    serde_json::to_writer(&mut out, &file)?;
    out.write_all(b"\n")?;

    Ok(())
}

/// Appends the unremap file suffix to an artifact path.
pub(crate) fn append_unremap_suffix(link: &PathBuf) -> PathBuf {
    let mut link_buf = link.clone().into_os_string();
    link_buf.push(UNREMAP_SUFFIX);
    PathBuf::from(link_buf)
}

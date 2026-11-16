//! Trust: refuse to build when a version mirror disagrees with the authority.
//!
//! Trust's version has ONE authority: the root `Cargo.toml`
//! `[workspace.package] version`, the key `pub bump` edits. Bootstrap reads
//! `src/version` — a mirror of it — for `CFG_TRUST_VERSION` (the `trust:` line of
//! `trustc -Vv`) and the dist archive names, and the crate manifests below are
//! mirrors whose `CARGO_PKG_VERSION` is compiled into the tools bootstrap ships
//! (`targo-trust --version` prints its own). A drifted mirror would therefore
//! build a toolchain that names a version the release line does not carry, so
//! bootstrap stops instead. `scripts/trust_version_sync.py --write` is the only
//! writer of the mirrors; `crates/trust-version`'s
//! `every_version_mirror_agrees_with_the_authority` test and the script's
//! `--check` cover the same list (plus lockfiles and
//! `release/trust-version.toml`, which a source tarball does not carry).
//!
//! The scheme is `publication/VERSIONING.md`'s: `MAJOR.MINOR.0`, the patch slot
//! always 0; dev builds are identified by build metadata, never a patch counter.

use std::path::Path;

/// The one command that rewrites every mirror from the authority.
const SYNC_COMMAND: &str = "python3 scripts/trust_version_sync.py --write";

/// The authority: this file's `[workspace.package] version`.
const AUTHORITY: &str = "Cargo.toml";

/// `(file, TOML table path)` of each crate-manifest mirror bootstrap builds from.
const MANIFEST_MIRRORS: &[(&str, &[&str])] = &[("targo-trust/Cargo.toml", &["package"])];

/// Exit the build unless `src/version` (already read, trimmed) and every crate
/// manifest mirror state the authority's `MAJOR.MINOR.0`.
pub(crate) fn check_version_mirrors(src: &Path, src_version: &str) {
    let problems = version_mirror_problems(src, src_version);
    if problems.is_empty() {
        return;
    }
    eprintln!("ERROR: Trust's version mirrors disagree with the one version authority.");
    for problem in &problems {
        eprintln!("  {problem}");
    }
    eprintln!(
        "HELP: `{AUTHORITY}` `[workspace.package] version` is the only place the version is \
         decided (`pub bump` edits it). Run `{SYNC_COMMAND}` to rewrite every mirror from it, \
         then rebuild."
    );
    crate::exit!(1);
}

/// Every disagreement, in words; empty when the mirrors agree.
fn version_mirror_problems(src: &Path, src_version: &str) -> Vec<String> {
    let authority = match read_manifest_string(src, AUTHORITY, &["workspace", "package"]) {
        Ok(version) => version,
        Err(problem) => return vec![problem],
    };
    if !is_release_line(&authority) {
        return vec![format!(
            "{AUTHORITY} [workspace.package] version {authority:?} is not MAJOR.MINOR.0 — the \
             patch slot is always 0 (publication/VERSIONING.md); bump MINOR with `pub bump`"
        )];
    }
    let mut problems = Vec::new();
    if src_version != authority {
        problems.push(format!("src/version is {src_version:?}, the authority says {authority:?}"));
    }
    for (file, table) in MANIFEST_MIRRORS {
        match read_manifest_string(src, file, table) {
            Ok(version) if version == authority => {}
            Ok(version) => problems.push(format!(
                "{file} [{}] version is {version:?}, the authority says {authority:?}",
                table.join(".")
            )),
            Err(problem) => problems.push(problem),
        }
    }
    problems
}

/// `version` from the TOML table at `table` in `src/<file>`.
fn read_manifest_string(src: &Path, file: &str, table: &[&str]) -> Result<String, String> {
    let text = std::fs::read_to_string(src.join(file))
        .map_err(|err| format!("cannot read {file}: {err}"))?;
    let manifest: toml::Value =
        toml::from_str(&text).map_err(|err| format!("cannot parse {file}: {err}"))?;
    let mut node = &manifest;
    for part in table {
        node = node.get(*part).ok_or_else(|| format!("{file} has no [{}]", table.join(".")))?;
    }
    node.get("version")
        .and_then(toml::Value::as_str)
        .map(str::to_owned)
        .ok_or_else(|| format!("{file} [{}] has no version string", table.join(".")))
}

/// `MAJOR.MINOR.0`: three canonical numbers (no leading zeros), the last `0`.
fn is_release_line(version: &str) -> bool {
    let parts: Vec<&str> = version.split('.').collect();
    parts.len() == 3
        && parts.iter().all(|part| {
            !part.is_empty()
                && part.bytes().all(|byte| byte.is_ascii_digit())
                && (*part == "0" || !part.starts_with('0'))
        })
        && parts[2] == "0"
}

#[cfg(test)]
mod tests;

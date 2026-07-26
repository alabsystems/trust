// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates
//! Build-time Creusot-manifest evidence boundary (fail-closed).
//!
//! A package that declares a dependency on the Creusot contract family
//! (`creusot-contracts`, `creusot-std`, and their satellite crates) is opting
//! into a Creusot spec surface (`#[requires]` / `#[ensures]` / `#[logic]`).
//! Outside the Creusot toolchain those attributes expand to no-ops, and Trust
//! does not import that legacy attribute surface: trustc's contract lane never
//! sees the specs. Letting such a package flow through `targo trust build`
//! would therefore be a false green: every declared Creusot spec would be
//! silently unverified while the build reports success. Selected packages that
//! opt into Creusot fail with an explicit unverified-spec setup error;
//! non-Creusot packages remain a no-op pass-through.
//!
//! This is the same boundary shape as the Kani gate (`kani_gate::gate_build`),
//! applied to the Creusot dependency family.

use std::collections::BTreeSet;
use std::io;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

const UNVERIFIED_CREUSOT_SPECS: &str = "unbound spec/build evidence: outside the Creusot toolchain the `creusot-contracts` attribute surface (`#[requires]` / `#[ensures]` / `#[logic]`) expands to no-ops and trustc does not import it, so this crate's Creusot specs would be silently UNVERIFIED while the build reports green; port the specs to Trust's native surface — first-class `requires`/`ensures` signature clauses and `clean { .. }` Lean islands — before building with `targo trust`";

/// Cargo package names that constitute the Creusot spec-surface opt-in. A
/// dependency on any of them (directly, renamed via `package = "..."`, in a
/// target-specific section, or through a workspace-inherited alias) means the
/// crate carries Creusot attributes that Trust would silently ignore.
const CREUSOT_FAMILY: [&str; 4] =
    ["creusot-contracts", "creusot-std", "creusot-contracts-proc", "creusot-contracts-dummy"];

fn is_creusot_family_package(name: &str) -> bool {
    CREUSOT_FAMILY.contains(&name)
}

/// Post-build gate folded into `targo trust build`.
///
/// A failed build is returned immediately without resolving packages. On a
/// successful build, every selected package manifest is inspected; a package
/// that declares a Creusot-family dependency (directly, renamed via
/// `package = "creusot-contracts"`, in a target-specific section, or through a
/// workspace-inherited alias) is rejected with an explicit unverified-spec
/// setup error. Once a crate opts in, ambient process state cannot disable the
/// gate.
pub(crate) fn gate_build(build_result: ExitCode, args: &[String]) -> ExitCode {
    if build_result != ExitCode::SUCCESS {
        return build_result;
    }

    let package_roots = match super::resolve_cargo_gate_package_roots(args) {
        Ok(Some(roots)) => roots,
        Ok(None) => return build_result,
        Err(error) => {
            eprintln!(
                "targo trust build: Creusot gate could not resolve selected packages: {error}"
            );
            return ExitCode::from(2);
        }
    };

    for root in package_roots {
        match manifest_declares_creusot_dependency(&root) {
            Ok(false) => {}
            Ok(true) => {
                eprintln!(
                    "targo trust build: Creusot spec surface for {} rejected: {UNVERIFIED_CREUSOT_SPECS}",
                    root.display()
                );
                return ExitCode::from(2);
            }
            Err(error) => {
                eprintln!(
                    "targo trust build: Creusot gate could not inspect {} before applying the \
                     unverified-spec boundary: {error}",
                    root.display()
                );
                return ExitCode::from(2);
            }
        }
    }
    build_result
}

fn dependency_table_declares_creusot(value: &toml::Value) -> bool {
    let Some(table) = value.as_table() else {
        return false;
    };
    table.iter().any(|(name, dependency)| {
        is_creusot_family_package(name)
            || dependency
                .as_table()
                .and_then(|detail| detail.get("package"))
                .and_then(toml::Value::as_str)
                .is_some_and(is_creusot_family_package)
    })
}

fn dependency_table_workspace_aliases(value: &toml::Value, aliases: &mut BTreeSet<String>) {
    let Some(table) = value.as_table() else {
        return;
    };
    for (name, dependency) in table {
        if dependency
            .as_table()
            .and_then(|detail| detail.get("workspace"))
            .and_then(toml::Value::as_bool)
            == Some(true)
        {
            aliases.insert(name.clone());
        }
    }
}

fn workspace_manifest_for_package(
    manifest_dir: &Path,
    package_manifest: &toml::Value,
) -> Result<Option<PathBuf>, String> {
    if let Some(workspace) = package_manifest
        .get("package")
        .and_then(toml::Value::as_table)
        .and_then(|package| package.get("workspace"))
        .and_then(toml::Value::as_str)
    {
        let path = manifest_dir.join(workspace).join("Cargo.toml");
        return path
            .canonicalize()
            .map(Some)
            .map_err(|error| format!("could not resolve inherited workspace manifest: {error}"));
    }

    for ancestor in manifest_dir.ancestors() {
        let candidate = ancestor.join("Cargo.toml");
        let text = match crate::input_limits::read_bounded_utf8_file(
            &candidate,
            crate::input_limits::MAX_RELEASE_METADATA_BYTES,
        ) {
            Ok(text) => text,
            Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
            Err(error) => {
                return Err(format!(
                    "could not inspect ancestor manifest {}: {error}",
                    candidate.display()
                ));
            }
        };
        let value = text.parse::<toml::Value>().map_err(|error| {
            format!("could not parse ancestor manifest {}: {error}", candidate.display())
        })?;
        if value.get("workspace").and_then(toml::Value::as_table).is_some() {
            return Ok(Some(candidate.canonicalize().map_err(|error| {
                format!(
                    "could not canonicalize workspace manifest {}: {error}",
                    candidate.display()
                )
            })?));
        }
    }
    Ok(None)
}

fn manifest_declares_creusot_dependency(manifest_dir: &Path) -> Result<bool, String> {
    let manifest_path = manifest_dir.join("Cargo.toml");
    let text = crate::input_limits::read_bounded_utf8_file(
        &manifest_path,
        crate::input_limits::MAX_RELEASE_METADATA_BYTES,
    )
    .map_err(|error| format!("could not read {}: {error}", manifest_path.display()))?;
    let manifest = text
        .parse::<toml::Value>()
        .map_err(|error| format!("could not parse {}: {error}", manifest_path.display()))?;
    let Some(root) = manifest.as_table() else {
        return Err(format!("{} is not a TOML table", manifest_path.display()));
    };

    const DEPENDENCY_SECTIONS: [&str; 3] =
        ["dependencies", "dev-dependencies", "build-dependencies"];
    let mut tables =
        DEPENDENCY_SECTIONS.iter().filter_map(|section| root.get(*section)).collect::<Vec<_>>();

    if let Some(targets) = root.get("target").and_then(toml::Value::as_table) {
        for target in targets.values().filter_map(toml::Value::as_table) {
            tables.extend(DEPENDENCY_SECTIONS.iter().filter_map(|section| target.get(*section)));
        }
    }
    if tables.iter().copied().any(dependency_table_declares_creusot) {
        return Ok(true);
    }

    let mut inherited_aliases = BTreeSet::new();
    for table in tables {
        dependency_table_workspace_aliases(table, &mut inherited_aliases);
    }
    if inherited_aliases.is_empty() {
        return Ok(false);
    }
    let workspace_manifest =
        workspace_manifest_for_package(manifest_dir, &manifest)?.ok_or_else(|| {
            format!(
                "{} inherits workspace dependencies {:?}, but no workspace manifest was found",
                manifest_path.display(),
                inherited_aliases
            )
        })?;
    let workspace_text = crate::input_limits::read_bounded_utf8_file(
        &workspace_manifest,
        crate::input_limits::MAX_RELEASE_METADATA_BYTES,
    )
    .map_err(|error| format!("could not read {}: {error}", workspace_manifest.display()))?;
    let workspace = workspace_text
        .parse::<toml::Value>()
        .map_err(|error| format!("could not parse {}: {error}", workspace_manifest.display()))?;
    let workspace_dependencies = workspace
        .get("workspace")
        .and_then(toml::Value::as_table)
        .and_then(|workspace| workspace.get("dependencies"))
        .and_then(toml::Value::as_table)
        .ok_or_else(|| {
            format!(
                "{} has no [workspace.dependencies] table for inherited aliases {:?}",
                workspace_manifest.display(),
                inherited_aliases
            )
        })?;
    Ok(inherited_aliases.into_iter().any(|alias| {
        workspace_dependencies.get(&alias).is_some_and(|dependency| {
            is_creusot_family_package(&alias)
                || dependency
                    .as_table()
                    .and_then(|detail| detail.get("package"))
                    .and_then(toml::Value::as_str)
                    .is_some_and(is_creusot_family_package)
        })
    }))
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn creusot_dependency_detection_covers_aliases_and_target_sections() {
        for manifest in [
            "[package]\nname='p'\nversion='0.1.0'\n[dev-dependencies]\ncreusot-contracts='0.4'\n",
            "[package]\nname='p'\nversion='0.1.0'\n[dependencies]\ncreusot-std='0.4'\n",
            "[package]\nname='p'\nversion='0.1.0'\n[build-dependencies]\ncreusot-contracts-proc='0.4'\n",
            "[package]\nname='p'\nversion='0.1.0'\n[dependencies]\ncreusot-contracts-dummy='0.1'\n",
            "[package]\nname='p'\nversion='0.1.0'\n[dependencies.contracts]\npackage='creusot-contracts'\nversion='0.4'\n",
            "[package]\nname='p'\nversion='0.1.0'\n[target.'cfg(unix)'.dependencies]\ncreusot-contracts={ workspace=true }\n",
        ] {
            let temp = tempfile::tempdir().expect("temp package");
            fs::write(temp.path().join("Cargo.toml"), manifest).expect("write manifest");
            assert!(
                manifest_declares_creusot_dependency(temp.path()).expect("inspect manifest"),
                "missed Creusot declaration in {manifest}"
            );
        }

        let temp = tempfile::tempdir().expect("temp package");
        fs::write(
            temp.path().join("Cargo.toml"),
            "[package]\nname='p'\nversion='0.1.0'\n[dependencies]\nserde='1'\n",
        )
        .expect("write manifest");
        assert!(!manifest_declares_creusot_dependency(temp.path()).expect("inspect manifest"));
    }

    #[test]
    fn creusot_dependency_detection_resolves_workspace_inherited_aliases() {
        let temp = tempfile::tempdir().expect("workspace fixture");
        let member = temp.path().join("member");
        fs::create_dir_all(&member).expect("member directory");
        fs::write(
            temp.path().join("Cargo.toml"),
            "[workspace]\nmembers=['member']\n[workspace.dependencies]\ncontracts={ package='creusot-contracts', version='0.4' }\n",
        )
        .expect("workspace manifest");
        fs::write(
            member.join("Cargo.toml"),
            "[package]\nname='p'\nversion='0.1.0'\n[target.'cfg(unix)'.dev-dependencies]\ncontracts={ workspace=true }\n",
        )
        .expect("member manifest");
        assert!(manifest_declares_creusot_dependency(&member).expect("resolve inherited alias"));
    }

    #[test]
    fn creusot_gate_preserves_a_failed_build_without_resolving_packages() {
        assert_eq!(
            gate_build(ExitCode::from(9), &["-p".to_string(), "missing".to_string()]),
            ExitCode::from(9)
        );
    }
}

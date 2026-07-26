// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates
//! Build-time Kani-manifest evidence boundary (fail-closed).
//!
//! A package that declares a `kani` dependency is opting into a Kani harness
//! surface (`#[kani::proof]` / `#[kani::proof_for_contract]`). Trust does not
//! import that legacy attribute surface (R2 deletion D-B) and trustc does not
//! yet publish the authenticated semantic-input/output manifest that would let
//! any post-build re-run certify the artifact just built. Letting such a
//! package flow through `targo trust build` would therefore be a false green:
//! its declared proof surface would be silently unexamined. Selected packages
//! that opt into Kani fail with `unbound input/build evidence`; non-Kani
//! packages remain a no-op pass-through.
//!
//! This boundary was previously provided by `kani_cli::gate_build`; the
//! `targo trust kani` Route-2 shim around it is deleted (R2 deletion D-A), but
//! the rejection itself is preserved here as the pipeline's own gate.

use std::collections::BTreeSet;
use std::io;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

const UNBOUND_KANI_EVIDENCE: &str = "unbound input/build evidence: the canonical compiler does not yet emit an authenticated semantic-input digest and output-artifact binding, and the legacy Kani attribute surface is not imported by Trust; a `kani` dependency opt-in cannot certify either the current source identity or a prior/final build";

/// Post-build gate folded into `targo trust build`.
///
/// A failed build is returned immediately without resolving packages. On a
/// successful build, every selected package manifest is inspected; a package
/// that declares a `kani` dependency (directly, renamed via `package = "kani"`,
/// in a target-specific section, or through a workspace-inherited alias) is
/// rejected with an explicit unbound-evidence setup error. Once a crate opts
/// in, ambient process state cannot disable the gate.
pub(crate) fn gate_build(build_result: ExitCode, args: &[String]) -> ExitCode {
    if build_result != ExitCode::SUCCESS {
        return build_result;
    }

    let package_roots = match super::resolve_cargo_gate_package_roots(args) {
        Ok(Some(roots)) => roots,
        Ok(None) => return build_result,
        Err(error) => {
            eprintln!("targo trust build: Kani gate could not resolve selected packages: {error}");
            return ExitCode::from(2);
        }
    };

    for root in package_roots {
        match manifest_declares_kani_dependency(&root) {
            Ok(false) => {}
            Ok(true) => {
                eprintln!(
                    "targo trust build: Kani certification for {} rejected: {UNBOUND_KANI_EVIDENCE}",
                    root.display()
                );
                return ExitCode::from(2);
            }
            Err(error) => {
                eprintln!(
                    "targo trust build: Kani gate could not inspect {} before applying the \
                     authenticated-input boundary: {error}",
                    root.display()
                );
                return ExitCode::from(2);
            }
        }
    }
    build_result
}

fn dependency_table_declares_kani(value: &toml::Value) -> bool {
    let Some(table) = value.as_table() else {
        return false;
    };
    table.iter().any(|(name, dependency)| {
        name == "kani"
            || dependency
                .as_table()
                .and_then(|detail| detail.get("package"))
                .and_then(toml::Value::as_str)
                == Some("kani")
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

fn manifest_declares_kani_dependency(manifest_dir: &Path) -> Result<bool, String> {
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
    if tables.iter().copied().any(dependency_table_declares_kani) {
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
            alias == "kani"
                || dependency
                    .as_table()
                    .and_then(|detail| detail.get("package"))
                    .and_then(toml::Value::as_str)
                    == Some("kani")
        })
    }))
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn kani_dependency_detection_covers_aliases_and_target_sections() {
        for manifest in [
            "[package]\nname='p'\nversion='0.1.0'\n[dev-dependencies]\nkani='1'\n",
            "[package]\nname='p'\nversion='0.1.0'\n[dependencies.mc]\npackage='kani'\nversion='1'\n",
            "[package]\nname='p'\nversion='0.1.0'\n[target.'cfg(unix)'.dependencies]\nkani={ workspace=true }\n",
        ] {
            let temp = tempfile::tempdir().expect("temp package");
            fs::write(temp.path().join("Cargo.toml"), manifest).expect("write manifest");
            assert!(
                manifest_declares_kani_dependency(temp.path()).expect("inspect manifest"),
                "missed Kani declaration in {manifest}"
            );
        }

        let temp = tempfile::tempdir().expect("temp package");
        fs::write(
            temp.path().join("Cargo.toml"),
            "[package]\nname='p'\nversion='0.1.0'\n[dependencies]\nserde='1'\n",
        )
        .expect("write manifest");
        assert!(!manifest_declares_kani_dependency(temp.path()).expect("inspect manifest"));
    }

    #[test]
    fn kani_dependency_detection_resolves_workspace_inherited_aliases() {
        let temp = tempfile::tempdir().expect("workspace fixture");
        let member = temp.path().join("member");
        fs::create_dir_all(&member).expect("member directory");
        fs::write(
            temp.path().join("Cargo.toml"),
            "[workspace]\nmembers=['member']\n[workspace.dependencies]\nmc={ package='kani', version='1' }\n",
        )
        .expect("workspace manifest");
        fs::write(
            member.join("Cargo.toml"),
            "[package]\nname='p'\nversion='0.1.0'\n[target.'cfg(unix)'.dev-dependencies]\nmc={ workspace=true }\n",
        )
        .expect("member manifest");
        assert!(manifest_declares_kani_dependency(&member).expect("resolve inherited alias"));
    }

    #[test]
    fn kani_gate_preserves_a_failed_build_without_resolving_packages() {
        assert_eq!(
            gate_build(ExitCode::from(9), &["-p".to_string(), "missing".to_string()]),
            ExitCode::from(9)
        );
    }
}

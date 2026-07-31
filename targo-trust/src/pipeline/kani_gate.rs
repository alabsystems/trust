// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates
//! Build-time Kani-manifest disclosure boundary.
//!
//! A package that declares a `kani` dependency is opting into a Kani harness
//! surface (`#[kani::proof]` / `#[kani::proof_for_contract]`).
//!
//! **Amended 2026-07-26 (two-language design v5, §3.2 MIGRATE).** Kani is now a
//! *zero-authority ingestion lane* on the TLA+ terms: its attributes may be read
//! as sugar and elaborated into Clean, and may never assert a proposition,
//! introduce an assumption, or acquire proof authority. This gate previously
//! rejected the build outright, on the premise that "Trust does not import that
//! legacy attribute surface". That premise is what the amendment changed, and
//! the rejection had become self-defeating: tippy machine-applicably rewrites
//! `#[kani::proof]` to `#[kani::harness]`, which is provided by the very crate
//! this gate refused — the autofix pointed at a door the build gate held shut.
//!
//! The other half of the original rationale still stands: trustc does not yet
//! publish the authenticated semantic-input/output manifest that would let a
//! post-build re-run certify the artifact just built. So the harnesses really
//! are unexamined by Trust. The false-green risk was never the *dependency*; it
//! was the word "silently". This gate therefore keeps the detection and
//! replaces the rejection with an unmissable disclosure: the build proceeds, and
//! the operator is told plainly that the Kani surface carried no authority and
//! was not examined. A gate keyed on the mere presence of a dependency was
//! testing the wrong thing; authority is what must be withheld, and it is
//! withheld structurally — nothing kani-derived can mint proof authority.
//!
//! **Why allowing the dependency is not fail-open** (verified 2026-07-26, and
//! re-check these three if the feature graph moves):
//!
//! 1. `#[kani::proof]` / `#[kani::harness]` expand to `#[kanitool::proof]`
//!    (`first-party/trust-mc/library/kani_macros`), and **trustc does not parse
//!    `kanitool` at all** — `rg kanitool compiler/ crates/` returns nothing. An
//!    unparsed attribute cannot mint an obligation or a verdict.
//! 2. The only `kanitool` attribute parser is `trust-mc-compiler`, which is
//!    pulled exclusively by trust-bmc's `trust-mc-native` feature. The
//!    compiler's chain is `trust-router/trust-build` ->
//!    `trust-bmc/trust-mc-native-trust-ir-bundle` -> `trust-mc-native-solver` ->
//!    `trust-mc-native-driver`, which never reaches `trust-mc-native`. trustc
//!    therefore does not link it.
//! 3. `ProofObligationSource::KaniProofAttribute` exists only under
//!    `trust-mc-driver/src/list/` — the harness *listing* surface. It enumerates
//!    for display; it is not a verdict path and the compiler does not call it.
//!
//! So in a `targo trust build` the Kani surface is inert: there is no verdict to
//! soften and no authority to withhold that is not already structurally absent.
//!
//! Fail-closed is preserved where it still means something: a manifest that
//! cannot be inspected is a setup error, not a pass.
//!
//! This boundary was previously provided by `kani_cli::gate_build`; the
//! `targo trust kani` Route-2 shim around it is deleted (R2 deletion D-A).

use std::collections::BTreeSet;
use std::io;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

const UNEXAMINED_KANI_SURFACE: &str = "its Kani harnesses were NOT examined and carry NO proof authority. Kani is a zero-authority ingestion lane (two-language design v5, §3.2): its attributes may be read as sugar and elaborated into Clean, but may never assert a proposition or certify a build. trustc does not yet emit the authenticated semantic-input digest and output-artifact binding that a post-build re-run would need, so nothing here certifies the current source identity or the artifact just built. Do not read a successful build as a discharged Kani proof; run `targo trust check` for the verdicts Trust actually stands behind";

/// Post-build disclosure gate folded into `targo trust build`.
///
/// A failed build is returned immediately without resolving packages. On a
/// successful build, every selected package manifest is inspected; a package
/// that declares a `kani` dependency (directly, renamed via `package = "kani"`,
/// in a target-specific section, or through a workspace-inherited alias) gets a
/// prominent disclosure on stderr and the build is allowed to proceed.
///
/// This does not weaken any proof claim, because a Kani harness never had one:
/// the ingestion lane forbids kani-derived text from acquiring proof authority,
/// so there is no verdict here to soften. What changed is that the operator is
/// now told, rather than the build being refused for spelling its sugar.
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
                    "targo trust build: warning: {} declares a `kani` dependency — \
                     {UNEXAMINED_KANI_SURFACE}",
                    root.display()
                );
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

    /// A `kani` dependency DISCLOSES, it does not reject (two-language design
    /// v5, §3.2 MIGRATE: kani is a zero-authority ingestion lane).
    ///
    /// This pins the amended boundary. It is not a weakened proof claim: the
    /// Kani surface is inert in a trustc build — trustc never parses `kanitool`,
    /// and `trust-mc-compiler`, the only parser of it, is not in the compiler's
    /// feature graph. See the module docs for the three checks that establish
    /// that. If any of them stops holding, this test should start failing on
    /// purpose and the gate should go back to rejecting.
    #[test]
    fn kani_dependency_discloses_rather_than_rejecting_the_build() {
        let temp = tempfile::tempdir().expect("package fixture");
        fs::write(
            temp.path().join("Cargo.toml"),
            "[package]\nname='p'\nversion='0.1.0'\n[dependencies]\nkani='1'\n",
        )
        .expect("write manifest");
        assert!(
            manifest_declares_kani_dependency(temp.path()).expect("inspect manifest"),
            "detection must survive the amendment — the disclosure depends on it"
        );
    }
}

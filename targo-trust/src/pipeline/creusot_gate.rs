// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates
//! Build-time Creusot-manifest disclosure boundary.
//!
//! A package that declares a dependency on the Creusot contract family
//! (`creusot-contracts`, `creusot-std`, and their satellite crates) is opting
//! into a Creusot spec surface (`#[requires]` / `#[ensures]` / `#[logic]`).
//! Outside the Creusot toolchain those attributes expand to no-ops, and trustc's
//! contract lane never sees the specs.
//!
//! **Amended 2026-07-26 (two-language design v5, §3.2 MIGRATE)**, in lockstep
//! with the Kani gate — v5 reclassifies the Creusot attribute surface as a
//! *zero-authority ingestion lane* on the same terms, and this gate is
//! explicitly the same boundary shape, so the two must not desynchronize.
//! (Until 2026-08-21 this file's detection arm still REJECTED while the doc
//! above claimed disclosure; the flip below closes that desynchronization.)
//!
//! A reader now exists for the supported subset: tippy's
//! `trust_creusot_spec_sugar` lint machine-applicably rewrites boolean,
//! comparison and machine-arithmetic clauses (plus `old()` on immutable
//! by-value parameters and `result`) into native `requires`/`ensures`
//! signature clauses, and discloses every unsupported attribute with its
//! blocker. The false-green risk was never the *dependency*, it was the word
//! "silently". Rejecting the build for declaring the dependency also blocks
//! the migration the amendment authorizes — you cannot port specs you are not
//! allowed to compile alongside, and the reader's own rewrite target is a
//! crate this gate would refuse. So detection is kept and the rejection is
//! replaced with an unmissable disclosure: the build proceeds, and the
//! operator is told plainly that the Creusot specs carried no authority and
//! were not examined, and where the migration path is (v7/D3: the refusal —
//! now disclosure — carries the fix).
//!
//! **Why allowing the dependency is not fail-open** (verified 2026-08-21;
//! re-check these three if the macro transport or the router vocabulary
//! moves):
//!
//! 1. The `creusot-contracts` surface Trust ships is the trust-wp shim
//!    (`first-party/trust-wp/crates/creusot-contracts` re-exporting
//!    `trust-wp-macros`), whose proc macros "validate contract syntax at
//!    compile time and pass through the item unchanged" — they assert
//!    nothing into the build. Upstream `creusot-contracts` outside the
//!    Creusot toolchain expands to no-ops.
//! 2. The shim's only spec transport is `#[doc = "trust-wp:..."]` attributes,
//!    and that transport has no consumer in trustc:
//!    `rg 'doc = "trust-wp:' compiler/ crates/` is empty (the bare
//!    `"trust-wp:` strings in `crates/trust-wp/src/verifier_api.rs` are
//!    evidence-id spellings, not the doc transport — target the real
//!    transport when re-checking, not the substring).
//! 3. No obligation kind or verdict path keys on creusot vocabulary:
//!    `rg -i 'creusot|pearlite' compiler/` is empty. An unparsed attribute
//!    cannot mint an obligation or a verdict.
//!
//! So there is no verdict here to soften and no authority to withhold that is
//! not already structurally absent. See `kani_gate` for the equivalent
//! three-point argument on the Kani side.
//!
//! Fail-closed is preserved where it still means something: a manifest that
//! cannot be inspected is a setup error, not a pass.
//!
//! This is the same boundary shape as the Kani gate
//! (`kani_gate::disclose_after_compile`), applied to the Creusot dependency
//! family. Both `check` and `build` run it, through
//! `pipeline::disclose_zero_authority_ingestion_lanes` (TRUST-26).

use std::collections::BTreeSet;
use std::io;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

const UNVERIFIED_CREUSOT_SPECS: &str = "its Creusot/pearlite specs were NOT examined and carry NO proof authority. Creusot is a zero-authority ingestion lane (two-language design v5, §3.2): outside the Creusot toolchain the attribute surface (`#[requires]` / `#[ensures]` / `#[logic]`) expands to no-ops and trustc does not import it. A reader now exists for the supported subset: run tippy — lint `trust_creusot_spec_sugar` — for machine-applicable rewrites of boolean/comparison/machine-arithmetic clauses (plus `old()` on immutable by-value parameters and `result`) into native `requires`/`ensures` signature clauses; every unsupported attribute is disclosed per attribute with its blocker (Int-relaxed quantifiers stay DEFERRED per the R4 §2 doctrine).";

/// What `build` adds after [`UNVERIFIED_CREUSOT_SPECS`].
const UNVERIFIED_CREUSOT_SPECS_BUILD_TAIL: &str = "Do not read a successful build as a discharged Creusot proof; run `targo trust check` for the verdicts Trust actually stands behind";

/// What `check` adds after [`UNVERIFIED_CREUSOT_SPECS`].
const UNVERIFIED_CREUSOT_SPECS_CHECK_TAIL: &str = "A PASS from this check covers only the obligations trustc itself verified; it is not a Creusot verdict";

/// Cargo package names that constitute the Creusot spec-surface opt-in. A
/// dependency on any of them (directly, renamed via `package = "..."`, in a
/// target-specific section, or through a workspace-inherited alias) means the
/// crate carries Creusot attributes that Trust would silently ignore.
const CREUSOT_FAMILY: [&str; 4] =
    ["creusot-contracts", "creusot-std", "creusot-contracts-proc", "creusot-contracts-dummy"];

fn is_creusot_family_package(name: &str) -> bool {
    CREUSOT_FAMILY.contains(&name)
}

/// Post-compile disclosure gate run by both `targo trust check` and
/// `targo trust build` (via `pipeline::disclose_zero_authority_ingestion_lanes`).
///
/// A failed run is returned immediately without resolving packages. On a
/// successful run, every selected package manifest is inspected; a package
/// that declares a Creusot-family dependency (directly, renamed via
/// `package = "creusot-contracts"`, in a target-specific section, or through a
/// workspace-inherited alias) gets a prominent disclosure on stderr — naming
/// the tippy reader as the migration path (v7/D3) — and the build proceeds.
/// Once a crate opts in, ambient process state cannot disable the disclosure.
///
/// This does not weaken any proof claim, because a Creusot spec never had one
/// here: the ingestion lane forbids creusot-derived text from acquiring proof
/// authority, so there is no verdict to soften. What changed is that the
/// operator is now told, rather than the build being refused for spelling its
/// sugar (the module docs carry the verified three-point inertness argument).
pub(crate) fn disclose_after_compile(
    verb: super::CompileVerb,
    result: ExitCode,
    args: &[String],
) -> ExitCode {
    if result != ExitCode::SUCCESS {
        return result;
    }
    let verb_name = verb.as_str();

    let package_roots = match super::resolve_cargo_gate_package_roots(args) {
        Ok(Some(roots)) => roots,
        Ok(None) => return result,
        Err(error) => {
            eprintln!(
                "targo trust {verb_name}: Creusot gate could not resolve selected packages: {error}"
            );
            return ExitCode::from(2);
        }
    };

    for root in package_roots {
        match boundary_disclosure_for(verb, &root) {
            Ok(None) => {}
            Ok(Some(disclosure)) => {
                eprintln!("{disclosure}");
            }
            Err(error) => {
                eprintln!(
                    "targo trust {verb_name}: Creusot gate could not inspect {} before applying \
                     the unverified-spec boundary: {error}",
                    root.display()
                );
                return ExitCode::from(2);
            }
        }
    }
    result
}

/// The per-package boundary outcome: detection DISCLOSES (returns the line to
/// print) rather than rejecting; an uninspectable manifest is still an error
/// (fail-closed where it still means something). Extracted from `disclose_after_compile`
/// so the disclose-not-reject flip is pinnable by test.
fn boundary_disclosure_for(
    verb: super::CompileVerb,
    root: &Path,
) -> Result<Option<String>, String> {
    let tail = match verb {
        super::CompileVerb::Check => UNVERIFIED_CREUSOT_SPECS_CHECK_TAIL,
        super::CompileVerb::Build => UNVERIFIED_CREUSOT_SPECS_BUILD_TAIL,
    };
    match manifest_declares_creusot_dependency(root) {
        Ok(false) => Ok(None),
        Ok(true) => Ok(Some(format!(
            "targo trust {}: warning: {} declares a Creusot-family dependency — \
             {UNVERIFIED_CREUSOT_SPECS} {tail}",
            verb.as_str(),
            root.display()
        ))),
        Err(error) => Err(error),
    }
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
            disclose_after_compile(
                super::super::CompileVerb::Build,
                ExitCode::from(9),
                &["-p".to_string(), "missing".to_string()]
            ),
            ExitCode::from(9)
        );
    }

    /// A Creusot-family dependency DISCLOSES, it does not reject (two-language
    /// design v5, §3.2 MIGRATE: creusot is a zero-authority ingestion lane).
    /// Mirror of `kani_dependency_discloses_rather_than_rejecting_the_build`,
    /// per this module's declared lockstep with the Kani gate.
    ///
    /// This pins the amended boundary. It is not a weakened proof claim: the
    /// Creusot surface is inert in a trustc build — the shim macros pass items
    /// through, the `doc = "trust-wp:"` transport has no consumer in trustc,
    /// and no verdict path keys on creusot vocabulary. See the module docs for
    /// the three checks that establish that. If any of them stops holding,
    /// this test should start failing on purpose and the gate should go back
    /// to rejecting.
    #[test]
    fn creusot_dependency_discloses_rather_than_rejecting_the_build() {
        let temp = tempfile::tempdir().expect("package fixture");
        fs::write(
            temp.path().join("Cargo.toml"),
            "[package]\nname='p'\nversion='0.1.0'\n[dependencies]\ncreusot-contracts='0.4'\n",
        )
        .expect("write manifest");
        for verb in [super::super::CompileVerb::Check, super::super::CompileVerb::Build] {
            let disclosure = boundary_disclosure_for(verb, temp.path())
                .expect("inspect manifest")
                .expect("detection must survive the amendment — the disclosure depends on it");
            assert!(disclosure.contains("warning"), "a disclosure, not a rejection: {disclosure}");
            assert!(
                !disclosure.contains("rejected"),
                "the reject wording must not survive the flip: {disclosure}"
            );
            // TRUST-26: the disclosure names the verb that actually ran and
            // carries the shared lane statement either way.
            assert!(
                disclosure.starts_with(&format!("targo trust {}: warning:", verb.as_str())),
                "{disclosure}"
            );
            assert!(disclosure.contains(UNVERIFIED_CREUSOT_SPECS), "{disclosure}");
        }
    }

    /// v7/D3: the disclosure must carry the fix. A reader now exists, so the
    /// disclosure names the tippy lint (the machine-applicable migration
    /// path), the deferred quantifier doctrine, and the verified lane.
    #[test]
    fn creusot_disclosure_points_at_the_tippy_reader() {
        assert!(
            UNVERIFIED_CREUSOT_SPECS.contains("trust_creusot_spec_sugar"),
            "the disclosure must name the lint: {UNVERIFIED_CREUSOT_SPECS}"
        );
        assert!(
            UNVERIFIED_CREUSOT_SPECS.contains("machine-applicable"),
            "the disclosure must say what the reader can do: {UNVERIFIED_CREUSOT_SPECS}"
        );
        assert!(
            UNVERIFIED_CREUSOT_SPECS.contains("DEFERRED"),
            "the disclosure must not oversell the reader past the R4 §2 deferral: \
             {UNVERIFIED_CREUSOT_SPECS}"
        );
        assert!(
            UNVERIFIED_CREUSOT_SPECS_BUILD_TAIL.contains("targo trust check"),
            "the build disclosure must point at the verified lane: \
             {UNVERIFIED_CREUSOT_SPECS_BUILD_TAIL}"
        );
    }

    /// A manifest that cannot be inspected is still a setup error, not a pass:
    /// the flip converts detection to disclosure, never inspection failure.
    #[test]
    fn an_uninspectable_manifest_still_fails_closed() {
        let temp = tempfile::tempdir().expect("empty dir");
        assert!(
            boundary_disclosure_for(super::super::CompileVerb::Check, temp.path()).is_err(),
            "a missing manifest must be an error, not a silent pass"
        );
    }
}

//! Downstream diagnostic gate for the R5 compatibility macros.
//!
//! Under the D1+ ratchet (owner policy flip 2026-07-21) BOTH macros emit the
//! advisory deprecation: every capability either macro exercises is
//! `FullyReplaced` (the Clean lane's admission-domain and interner gaps closed
//! with positive near-cap certified vectors), so per the PRIME RULE the nudge
//! points users at a replacement that reproduces the macro's verdict. This
//! gate proves it end-to-end through the patched first-party graph: under
//! `#![deny(deprecated)]` every public invocation path FAILS with rustc's
//! genuine `deprecated`-coded diagnostic, an `#![allow(deprecated)]` consumer
//! still compiles cleanly (the nudge is advisory, not removal), and the path
//! consumer still fails closed on split semantic universes.

use std::fs;
use std::path::Path;
use std::process::{Command, Output};

fn cargo_check(cargo: &std::ffi::OsStr, root: &Path, locked: bool) -> Output {
    let mut command = Command::new(cargo);
    command.arg("check").arg("--offline");
    if locked {
        command.arg("--locked");
    }
    command
        .arg("--target-dir")
        .arg(root.join("target"))
        .current_dir(root)
        .output()
        .expect("invoke Cargo for downstream R5 fixture")
}

fn cargo_check_json(cargo: &std::ffi::OsStr, root: &Path) -> Output {
    Command::new(cargo)
        .arg("check")
        .arg("--offline")
        .arg("--locked")
        .arg("--message-format=json")
        .arg("--target-dir")
        .arg(root.join("target"))
        .current_dir(root)
        .output()
        .expect("invoke Cargo JSON diagnostic check for downstream R5 fixture")
}

fn canonical_patch_closure(repository_root: &Path) -> String {
    let root = repository_root.display().to_string().replace('\\', "\\\\").replace('"', "\\\"");
    format!(
        r#"
[patch."https://github.com/alabsystems/trust-ir.git"]
trust-ir = {{ path = "{root}/first-party/trust-ir/crates/trust-ir" }}
trust-ir-build = {{ path = "{root}/first-party/trust-ir/crates/trust-ir-build" }}

[patch."https://github.com/alabsystems/clean.git"]
clean-ck0 = {{ path = "{root}/first-party/clean/crates/clean-ck0" }}
clean-kernel = {{ path = "{root}/first-party/clean/crates/clean-kernel" }}

[patch."https://github.com/alabsystems/ay.git"]
ay = {{ path = "{root}/first-party/ay/crates/ay" }}
ay-dpll = {{ path = "{root}/first-party/ay/crates/ay-dpll" }}
ay-core = {{ path = "{root}/first-party/ay/crates/ay-core" }}
ay-proof = {{ path = "{root}/first-party/ay/crates/ay-proof" }}
ay-allsat = {{ path = "{root}/first-party/ay/crates/ay-allsat" }}
ay-chc = {{ path = "{root}/first-party/ay/crates/ay-chc" }}
ay-sat = {{ path = "{root}/first-party/ay/crates/ay-sat" }}
ay-frontend = {{ path = "{root}/first-party/ay/crates/ay-frontend" }}
ay-encode = {{ path = "{root}/first-party/ay/crates/ay-encode" }}

[patch."https://github.com/alabsystems/trust-cg.git"]
trust-cg-codegen = {{ path = "{root}/first-party/trust-cg/crates/trust-cg-codegen" }}
trust-cg-ir = {{ path = "{root}/first-party/trust-cg/crates/trust-cg-ir" }}
trust-cg-lower = {{ path = "{root}/first-party/trust-cg/crates/trust-cg-lower" }}
trust-cg-opt = {{ path = "{root}/first-party/trust-cg/crates/trust-cg-opt" }}
trust-cg-jit-matrix = {{ path = "{root}/first-party/trust-cg/crates/trust-cg-jit-matrix" }}

[patch.crates-io]
rustc-hash = {{ path = "{root}/first-party/ty/crates/tla-hash-fx" }}
num-bigint = {{ path = "{root}/first-party/ty/crates/tla-bignum/bigint" }}
num-integer = {{ path = "{root}/first-party/ty/crates/tla-bignum/integer" }}
num-traits = {{ path = "{root}/first-party/ty/crates/tla-bignum/traits" }}
"#,
    )
}

fn assert_one_repository_package(metadata: &serde_json::Value, name: &str, manifest: &Path) {
    let packages = metadata["packages"].as_array().expect("Cargo metadata packages");
    let matches = packages
        .iter()
        .filter(|package| package["name"].as_str() == Some(name))
        .collect::<Vec<_>>();
    assert_eq!(matches.len(), 1, "expected one {name} package instance: {matches:#?}");
    assert!(matches[0]["source"].is_null(), "{name} did not resolve to a path package");
    let actual = Path::new(matches[0]["manifest_path"].as_str().expect("package manifest path"))
        .canonicalize()
        .expect("canonical package manifest path");
    assert_eq!(actual, manifest.canonicalize().expect("canonical expected manifest"));
}

fn assert_no_remote_sibling_sources(metadata: &serde_json::Value) {
    const REPOSITORY_SOURCES: &[&str] = &[
        "github.com/alabsystems/clean.git",
        "github.com/alabsystems/trust-ir.git",
        "github.com/alabsystems/ay.git",
        "github.com/alabsystems/trust-cg.git",
    ];
    let escaped = metadata["packages"]
        .as_array()
        .expect("Cargo metadata packages")
        .iter()
        .filter_map(|package| {
            let source = package["source"].as_str()?;
            REPOSITORY_SOURCES
                .iter()
                .any(|repository| source.contains(repository))
                .then(|| format!("{}: {source}", package["name"].as_str().unwrap_or("<unnamed>")))
        })
        .collect::<Vec<_>>();
    assert!(
        escaped.is_empty(),
        "repository sibling packages escaped the downstream patch closure: {escaped:#?}",
    );
}

fn is_explicit_split_universe_failure(stderr: &str) -> bool {
    let temporal_sentinels = stderr.contains("RepositoryCleanKernelUniverse")
        && stderr.contains("RepositoryTrustIrUniverse");
    let rustc_type_universe = stderr.contains(
        "there are multiple different versions of crate `trust_ir` in the dependency graph",
    ) && stderr
        .contains("expected `trust_cg_lower::trust_ir_compat::Module`, found `trust_ir::Module`");
    temporal_sentinels || rustc_type_universe
}

/// D1+ ratchet gate: both macro surfaces exercise only `FullyReplaced`
/// capabilities (owner policy flip 2026-07-21), so every public invocation
/// path must emit rustc's genuine `deprecated`-coded diagnostic — which the
/// fixture's `#![deny(deprecated)]` escalates to a compile FAILURE.
fn assert_macro_deprecation_fires(output: &Output, invocation_form: &str) {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    for unrelated in [
        "RepositoryCleanKernelUniverse",
        "RepositoryTrustIrUniverse",
        "there are multiple different versions of crate `trust_ir`",
        "failed to get",
        "failed to load source",
        "failed to resolve",
        "no matching package named",
    ] {
        assert!(
            !stderr.contains(unrelated) && !stdout.contains(unrelated),
            "{invocation_form} hit an unrelated dependency/coherence failure `{unrelated}`:\n{stderr}",
        );
    }
    let deprecations = stdout
        .lines()
        .filter(|line| !line.trim().is_empty())
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
        .filter(|message| message["reason"].as_str() == Some("compiler-message"))
        .filter(|message| message["message"]["code"]["code"].as_str() == Some("deprecated"))
        .collect::<Vec<_>>();
    assert!(
        !deprecations.is_empty(),
        "{invocation_form} must emit the advisory deprecation for its FullyReplaced \
         capability:\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );
    assert!(
        !output.status.success(),
        "{invocation_form} must FAIL under deny(deprecated) now that the nudge \
         fires:\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );
}

#[test]
fn split_universe_diagnostic_predicate_rejects_unrelated_failures() {
    assert!(is_explicit_split_universe_failure(
        "RepositoryCleanKernelUniverse RepositoryTrustIrUniverse"
    ));
    assert!(is_explicit_split_universe_failure(
        "expected `trust_cg_lower::trust_ir_compat::Module`, found `trust_ir::Module`; \
         there are multiple different versions of crate `trust_ir` in the dependency graph"
    ));
    for unrelated in [
        "error: could not compile dependency",
        "there are multiple different versions of crate `trust_ir` in the dependency graph",
        "expected `trust_cg_lower::trust_ir_compat::Module`, found `trust_ir::Module`",
        "RepositoryTrustIrUniverse",
    ] {
        assert!(
            !is_explicit_split_universe_failure(unrelated),
            "unrelated or incomplete diagnostic was accepted: {unrelated}"
        );
    }
}

// Resurrected 2026-07-20 after a compile error had silently kept this file's
// integration coverage dead. This remains a normal live gate: the repository's
// committed submodule tuple and Cargo.lock must be coherent enough for a real
// downstream path consumer, and dependency drift is a failure rather than a
// reason to skip the public deprecation contract.
#[test]
fn path_consumer_fails_on_split_universes_then_warns_deprecated_when_patched() {
    // Precondition for this gate: under the D1+ ratchet (owner policy flip
    // 2026-07-21) the scorecard requires the `#[deprecated]` attribute on BOTH
    // macros — every capability either macro exercises is FullyReplaced. This
    // test proves the nudge fires end-to-end through the patched graph.
    use trust_spec_temporal::{R5MacroSurface, macro_surface_emits_deprecation};
    assert!(
        macro_surface_emits_deprecation(R5MacroSurface::TrustModel)
            && macro_surface_emits_deprecation(R5MacroSurface::TemporalModel),
        "D1+ ratchet: both compatibility macros must emit the advisory deprecation nudge",
    );

    let temp = tempfile::Builder::new()
        .prefix("trust-r5-deprecation-consumer-")
        .tempdir()
        .expect("temporary consumer crate");
    let manifest_path = Path::new(env!("CARGO_MANIFEST_DIR"));
    let repository_root =
        manifest_path.join("../..").canonicalize().expect("canonical repository root");
    let manifest_dir =
        manifest_path.display().to_string().replace('\\', "\\\\").replace('"', "\\\"");
    let macro_manifest_dir = manifest_path
        .join("../trust-spec-temporal-macros")
        .canonicalize()
        .expect("canonical temporal macro manifest directory")
        .display()
        .to_string()
        .replace('\\', "\\\\")
        .replace('"', "\\\"");
    fs::write(
        temp.path().join("Cargo.toml"),
        format!(
            r#"[package]
name = "trust-r5-deprecation-consumer"
version = "0.0.0"
edition = "2021"

[dependencies]
trust-spec-temporal = {{ path = "{manifest_dir}" }}
"#,
        ),
    )
    .expect("write downstream consumer manifest");
    fs::create_dir(temp.path().join("src")).expect("create downstream source directory");
    let source = temp.path().join("src/lib.rs");
    fs::write(&source, "pub fn dependency_graph_reached() {}\n")
        .expect("write unpatched coherence fixture");

    // A dependency crate's `[patch]` tables are not transitive. Without the
    // canonical root patch closure, tla-check brings separate git TrustIR/Clean
    // instances into this path consumer. The temporal crate's compile-time
    // carrier checks must reject that split graph before it can verify anything.
    let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
    let unpatched = cargo_check(&cargo, temp.path(), false);
    let unpatched_stderr = String::from_utf8_lossy(&unpatched.stderr).into_owned();
    assert!(
        !unpatched.status.success() && is_explicit_split_universe_failure(&unpatched_stderr),
        "unpatched path consumer did not fail closed on split semantic universes:\n{unpatched_stderr}",
    );

    // A supported path consumer owns the Cargo root, so it must repeat the
    // repository patch closure. Prove resolution has exactly one local
    // instance of both Clean checkers and TrustIR before checking the user
    // diagnostic.
    fs::write(
        temp.path().join("Cargo.toml"),
        format!(
            r#"[package]
name = "trust-r5-deprecation-consumer"
version = "0.0.0"
edition = "2021"

[dependencies]
trust-spec-temporal = {{ path = "{manifest_dir}" }}
trust-spec-temporal-macros = {{ path = "{macro_manifest_dir}" }}
{}
"#,
            canonical_patch_closure(&repository_root),
        ),
    )
    .expect("write patched downstream consumer manifest");
    fs::copy(manifest_path.join("Cargo.lock"), temp.path().join("Cargo.lock"))
        .expect("seed patched downstream consumer with the committed temporal lockfile");

    let metadata_output = Command::new(&cargo)
        .arg("metadata")
        .arg("--offline")
        .arg("--format-version=1")
        .current_dir(temp.path())
        .output()
        .expect("resolve patched downstream dependency graph");
    assert!(
        metadata_output.status.success(),
        "patched downstream metadata failed:\n{}",
        String::from_utf8_lossy(&metadata_output.stderr),
    );
    let metadata: serde_json::Value =
        serde_json::from_slice(&metadata_output.stdout).expect("parse Cargo metadata");
    assert_one_repository_package(
        &metadata,
        "clean-ck0",
        &repository_root.join("first-party/clean/crates/clean-ck0/Cargo.toml"),
    );
    assert_one_repository_package(
        &metadata,
        "clean-kernel",
        &repository_root.join("first-party/clean/crates/clean-kernel/Cargo.toml"),
    );
    assert_one_repository_package(
        &metadata,
        "trust-ir",
        &repository_root.join("first-party/trust-ir/crates/trust-ir/Cargo.toml"),
    );
    assert_no_remote_sibling_sources(&metadata);

    fs::write(
        &source,
        r#"#![deny(deprecated)]
use trust_spec_temporal::{temporal_model, trust_model, Model};

fn legacy_function_model() -> Model {
    trust_model! {
        LegacyFunction {
            const Buggy = 0;
            var x = 0;
            action Step { x = x; }
            invariant Stable: x == x;
        }
    }
}

temporal_model! {
    LegacyItem {
        const Buggy = 0;
        var x = 0;
        action Step { x = x; }
        invariant Stable: x == x;
    }
}
"#,
    )
    .expect("write downstream deprecation fixture");

    // Reuse the isolated target from the negative graph check. Selecting a
    // deps-directory rlib by timestamp would be racy when parallel worktrees
    // build the same crate on this machine.
    //
    // D1+ ratchet: under `#![deny(deprecated)]` the fixture (both macros
    // co-located) must FAIL with rustc's genuine deprecation diagnostic —
    // "use of deprecated <kind> `X`", matched by that exact phrasing rather
    // than a bare "deprecated" substring (which a fresh full-graph check trips
    // on via unrelated sibling `elided-lifetimes-in-paths` lint text). The
    // per-macro JSON checks below assert the same thing precisely by code.
    let output = cargo_check(&cargo, temp.path(), true);
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(
        !output.status.success()
            && stderr.contains("use of deprecated")
            && !stderr.contains("RepositoryCleanKernelUniverse")
            && !stderr.contains("RepositoryTrustIrUniverse"),
        "coherent path consumer did not fail on the advisory deprecation under \
         deny(deprecated):\n{stderr}",
    );

    // The nudge is advisory, not removal: the same co-located fixture with the
    // nudge acknowledged must compile cleanly — every existing use keeps
    // working identically.
    fs::write(
        &source,
        r#"#![allow(deprecated)]
use trust_spec_temporal::{temporal_model, trust_model, Model};

fn legacy_function_model() -> Model {
    trust_model! {
        LegacyFunction {
            const Buggy = 0;
            var x = 0;
            action Step { x = x; }
            invariant Stable: x == x;
        }
    }
}

temporal_model! {
    LegacyItem {
        const Buggy = 0;
        var x = 0;
        action Step { x = x; }
        invariant Stable: x == x;
    }
}
"#,
    )
    .expect("write acknowledged downstream deprecation fixture");
    let acknowledged = cargo_check(&cargo, temp.path(), true);
    let acknowledged_stderr = String::from_utf8_lossy(&acknowledged.stderr).into_owned();
    assert!(
        acknowledged.status.success() && !acknowledged_stderr.contains("use of deprecated"),
        "allow(deprecated) consumer must compile cleanly — the macros keep \
         working:\n{acknowledged_stderr}",
    );

    // Cover every public invocation path one macro at a time. JSON diagnostics
    // let us assert precisely that the `deprecated`-coded message IS emitted
    // while distinguishing it from any source/path/coherence failure. Under the
    // D1+ ratchet every path — both macros, both spellings — must fire the
    // advisory nudge (escalated to an error by the fixture's deny).
    const FUNCTION_CONSUMER: &str = r#"#![deny(deprecated)]

fn legacy_function_model() -> trust_spec_temporal::Model {
    $MACRO! {
        $MODEL {
            const Buggy = 0;
            var x = 0;
            action Step { x = x; }
            invariant Stable: x == x;
        }
    }
}
"#;
    const ITEM_CONSUMER: &str = r#"#![deny(deprecated)]

$MACRO! {
    $MODEL {
        const Buggy = 0;
        var x = 0;
        action Step { x = x; }
        invariant Stable: x == x;
    }
}
"#;
    for (invocation_form, model_name, template) in [
        (
            "fully qualified trust_spec_temporal::trust_model!",
            "RootQualifiedFunction",
            FUNCTION_CONSUMER,
        ),
        (
            "fully qualified trust_spec_temporal::temporal_model!",
            "RootQualifiedItem",
            ITEM_CONSUMER,
        ),
        (
            "direct trust_spec_temporal_macros::trust_model!",
            "DirectMacroFunction",
            FUNCTION_CONSUMER,
        ),
        ("direct trust_spec_temporal_macros::temporal_model!", "DirectMacroItem", ITEM_CONSUMER),
    ] {
        let macro_path = invocation_form
            .strip_prefix("fully qualified ")
            .or_else(|| invocation_form.strip_prefix("direct "))
            .and_then(|path| path.strip_suffix('!'))
            .expect("invocation label contains the public macro path");
        fs::write(&source, template.replace("$MACRO", macro_path).replace("$MODEL", model_name))
            .unwrap_or_else(|error| panic!("write {invocation_form} consumer: {error}"));
        let output = cargo_check_json(&cargo, temp.path());
        // Every public invocation path exercises only FullyReplaced
        // capabilities, so each must fire the advisory nudge (2026-07-21 flip).
        assert_macro_deprecation_fires(&output, invocation_form);
    }
}

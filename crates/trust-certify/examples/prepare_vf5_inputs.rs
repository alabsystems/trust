// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! UNTRUSTED mathematical input preparation. None of these commands constructs a
//! reference kernel, pins a digest, checks a theorem or registers a row.
//! `package` copies the fixed VF5Check graph's ACTUAL importer captures;
//! `proposal` extracts only two expression values from a separate untrusted
//! generated module. The consumer still checks the original current judgment.
//! Resource policy/staging expose the fixed runtime policy and copy validated
//! mathematical DATA only, without importing or certifying that DATA.

use std::collections::BTreeMap;
use std::fs::OpenOptions;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_olean::{CapturedModuleBytes, ImportError, load_modules_with_deps_checked_with_limits};
use sha2::{Digest, Sha256};

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct SourceBook {
    clean_revision: String,
    lean_world: String,
    source_files: BTreeMap<String, String>,
}

fn main() -> ExitCode {
    let args = std::env::args_os().skip(1).map(PathBuf::from).collect::<Vec<_>>();
    let result = match args.as_slice() {
        [mode, family, lean_lib, source_book, output, options @ ..]
            if mode == Path::new("package") => {
            dependency_roots(options)
                .and_then(|dependencies| package(family, lean_lib, source_book, output, &dependencies))
        }
        [mode, generated, family, lean_lib, artifact, output, options @ ..]
            if mode == Path::new("proposal") => {
            dependency_roots(options).and_then(|dependencies| {
                proposal(generated, family, lean_lib, artifact, output, &dependencies)
            })
        }
        [mode] if mode == Path::new("resource-policy") => {
            trust_certify::calculus_row::base::resource::resource_policy()
                .and_then(|policy| print_resource_json(&policy))
        }
        [mode] if mode == Path::new("source-identity") => {
            let (clean_revision, lean_world) =
                trust_certify::calculus_row::base::fixed_source_identity();
            print_resource_json(&serde_json::json!({
                "schema": 1,
                "kind": "vf5-fixed-source-identity-v1",
                "clean_revision": clean_revision,
                "lean_world": lean_world,
                "production_admission": false,
            }))
        }
        [mode, package, digest, sysroot] if mode == Path::new("stage-sysroot-resource") => {
            match digest.to_str() {
                Some(digest) => trust_certify::calculus_row::base::resource::stage_sysroot_resource(
                    package, digest, sysroot,
                ).and_then(|output| print_resource_json(&output)),
                None => Err("VF5 manifest digest is not UTF-8".into()),
            }
        }
        _ => {
            eprintln!("usage: prepare_vf5_inputs package FAMILY LEAN_LIB SOURCE_BOOK NEW_OUTPUT_DIR");
            eprintln!("       [--dependency-root DIRECTORY]...");
            eprintln!("   or: prepare_vf5_inputs proposal GENERATED FAMILY LEAN_LIB ARTIFACT NEW_OUTPUT_FILE");
            eprintln!("       [--dependency-root DIRECTORY]...");
            eprintln!("   or: prepare_vf5_inputs resource-policy");
            eprintln!("   or: prepare_vf5_inputs source-identity");
            eprintln!("   or: prepare_vf5_inputs stage-sysroot-resource PACKAGE MANIFEST_SHA256 OWNED_SYSROOT");
            return ExitCode::from(2);
        }
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("VF5 input preparation failed (no proof authority): {error}");
            ExitCode::FAILURE
        }
    }
}

fn print_resource_json(value: &impl serde::Serialize) -> Result<(), String> {
    let mut stdout = std::io::stdout().lock();
    serde_json::to_writer(&mut stdout, value).map_err(|error| error.to_string())?;
    stdout.write_all(b"\n").map_err(|error| error.to_string())
}

fn dependency_roots(options: &[PathBuf]) -> Result<Vec<PathBuf>, String> {
    let mut roots = Vec::new();
    roots.try_reserve(options.len() / 2).map_err(|error| error.to_string())?;
    let mut pairs = options.chunks_exact(2);
    for pair in &mut pairs {
        if pair[0] != Path::new("--dependency-root") || pair[1].as_os_str().is_empty() {
            return Err("expected --dependency-root DIRECTORY".into());
        }
        roots.push(pair[1].clone());
    }
    if !pairs.remainder().is_empty() {
        return Err("expected --dependency-root DIRECTORY".into());
    }
    Ok(roots)
}

fn package(
    family: &Path,
    lean_lib: &Path,
    source_book: &Path,
    output: &Path,
    dependencies: &[PathBuf],
) -> Result<(), String> {
    let book = trust_proof_session::storage::read_bounded(source_book).map_err(|e| e.to_string())?;
    let sources: SourceBook = serde_json::from_slice(&book).map_err(|e| e.to_string())?;
    if sources.source_files.is_empty() {
        return Err("empty source book".into());
    }
    // A failed preparation keeps its partial output; never overwrite a prior
    // package, successful or failed, in order to obtain a new result.
    std::fs::create_dir(output).map_err(|e| e.to_string())?;
    let modules = output.join("modules");
    std::fs::create_dir(&modules).map_err(|e| e.to_string())?;
    let mut inventory = BTreeMap::new();
    // Changed roots are compiled in `family`; explicitly borrowed unchanged
    // mathematical dependencies remain in place. Never find VF5Check itself
    // in an older dependency directory when the primary build is missing.
    let root = Name::from_string("VF5Check");
    let mut before = |name: &Name, _path: &Path, index: usize| {
        if name == &root && index != 0 {
            return Err(ImportError::UnsupportedModule {
                module: format!("{name:?}"),
                reason: "VF5Check must resolve from the primary family directory".into(),
            });
        }
        Ok(())
    };
    let mut capture = |name: &Name, _path: &Path, bytes: CapturedModuleBytes<'_>| {
        let relative = clean_olean::typed_module_rel_path(name)?;
        let refused = |reason: String| ImportError::UnsupportedModule {
            module: format!("{name:?}"),
            reason: format!("VF5 untrusted package preparation: {reason}"),
        };
        let destination = modules.join(&relative);
        if let Some(parent) = destination.parent() {
            std::fs::create_dir_all(parent).map_err(|e| refused(e.to_string()))?;
        }
        for (extension, data) in [
            ("olean", Some(bytes.base)),
            ("olean.server", bytes.server),
            ("olean.private", bytes.private),
            ("ir", bytes.ir),
        ] {
            if let Some(data) = data {
                write_new(&destination.with_extension(extension), data).map_err(refused)?;
            }
        }
        let path = relative.to_str().ok_or_else(|| refused("non-UTF8 module path".into()))?;
        if inventory.insert(path.to_owned(), serde_json::json!({
            "path": path,
            "base_sha256": hash(bytes.base),
            "server_sha256": bytes.server.map(hash),
            "private_sha256": bytes.private.map(hash),
            "ir_sha256": bytes.ir.map(hash),
        })).is_some() {
            return Err(refused("duplicate structural module capture".into()));
        }
        Ok(())
    };
    let mut search_paths = Vec::new();
    search_paths.try_reserve(dependencies.len() + 2).map_err(|error| error.to_string())?;
    search_paths.push(family.to_owned());
    search_paths.extend_from_slice(dependencies);
    search_paths.push(lean_lib.to_owned());
    let mut env = Environment::for_lean_replay();
    load_modules_with_deps_checked_with_limits(
        &mut env,
        &["VF5Check".to_owned()],
        &search_paths,
        trust_certify::calculus_row::base::vf5_capture_limits(),
        &mut before,
        &mut capture,
    ).map_err(|e| format!("untrusted import: {e:?}"))?;
    let manifest = serde_json::json!({
        "schema": 1,
        "clean_revision": sources.clean_revision,
        "lean_world": sources.lean_world,
        "source_files": sources.source_files,
        "modules": inventory.into_values().collect::<Vec<_>>(),
    });
    write_new(&output.join("vf5-base-v1.json"), &serde_json::to_vec_pretty(&manifest).map_err(|e| e.to_string())?)
}

fn proposal(
    generated: &Path,
    family: &Path,
    lean_lib: &Path,
    artifact: &Path,
    output: &Path,
    dependencies: &[PathBuf],
) -> Result<(), String> {
    let mut env = Environment::for_lean_replay();
    let root = Name::from_string("VF5Check");
    let generated_root = Name::from_string("TrustVF5Proposal");
    // The maintained producer puts both modules in one work directory. Keep
    // that layout and ordinary directory aliases, while refusing a root found
    // only in an explicitly borrowed dependency context.
    let shared_primary = match (generated.canonicalize(), family.canonicalize()) {
        (Ok(generated), Ok(family)) => generated == family,
        _ => false,
    };
    let mut before = |name: &Name, _path: &Path, index: usize| {
        let family_root = index == 1 || (index == 0 && shared_primary);
        if (name == &root && !family_root) || (name == &generated_root && index != 0) {
            return Err(ImportError::UnsupportedModule {
                module: format!("{name:?}"),
                reason: "proposal roots must resolve from their declared primary directories".into(),
            });
        }
        Ok(())
    };
    let mut capture = |_name: &Name, _path: &Path, _bytes: CapturedModuleBytes<'_>| Ok(());
    let mut search_paths = Vec::new();
    search_paths.try_reserve(dependencies.len() + 3).map_err(|error| error.to_string())?;
    search_paths.extend_from_slice(&[generated.to_owned(), family.to_owned()]);
    search_paths.extend_from_slice(dependencies);
    search_paths.push(lean_lib.to_owned());
    load_modules_with_deps_checked_with_limits(
        &mut env,
        &["TrustVF5Proposal".to_owned()],
        &search_paths,
        trust_certify::calculus_row::base::vf5_capture_limits(),
        &mut before,
        &mut capture,
    ).map_err(|e| format!("untrusted proposal import: {e:?}"))?;
    let value = |name: &str| {
        env.get_const(&Name::from_string(name))
            .and_then(|info| info.value.clone())
            .ok_or_else(|| format!("proposal expression absent: {name}"))
    };
    let artifact = trust_proof_session::storage::read_bounded(artifact).map_err(|e| e.to_string())?;
    let bytes = trust_certify::calculus_row::hints::encode(
        &artifact,
        &value("TrustVF5Proposal.annotation")?,
        &value("TrustVF5Proposal.certificates")?,
    ).map_err(|e| format!("proposal codec: {e:?}"))?;
    write_new(output, &bytes)?;
    println!("{}", serde_json::json!({
        "kind": "vf5-untrusted-proposal-v1",
        "artifact_sha256": hash(&artifact),
        "hint_sha256": hash(&bytes),
        "hint_filename": trust_certify::calculus_row::hints::filename(&artifact),
        "production_admission": false,
    }));
    Ok(())
}

fn hash(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn write_new(path: &Path, bytes: &[u8]) -> Result<(), String> {
    let mut file = OpenOptions::new().write(true).create_new(true).open(path)
        .map_err(|e| format!("create {}: {e}", path.display()))?;
    file.write_all(bytes).map_err(|e| e.to_string())?;
    file.sync_all().map_err(|e| e.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    // These are actual checked-loader/capture tests of untrusted container
    // DATA, not mathematical VF5 bases or kernel/admission positives.
    fn module(directory: &Path, name: &str, imports: &[(&str, bool)]) -> Vec<u8> {
        let bytes = clean_olean::OleanExporter::export_with_env(
            &Environment::default(), imports, &[],
            "0000000000000000000000000000000000000000",
        ).expect("export a real import-graph container");
        std::fs::write(directory.join(format!("{name}.olean")), &bytes).expect("write container");
        bytes
    }

    fn source_book(root: &Path) -> PathBuf {
        let path = root.join("sources.json");
        std::fs::write(&path, br#"{"clean_revision":"untrusted-container-data","lean_world":"not-a-math-world","source_files":{"container":"0000000000000000000000000000000000000000000000000000000000000000"}}"#)
            .expect("write explicitly non-admissible metadata");
        path
    }

    #[test]
    fn explicit_dependency_roots_capture_the_actual_transitive_parts_without_admission() {
        let root = tempfile::tempdir().expect("root");
        let family = tempfile::tempdir().expect("family");
        let first = tempfile::tempdir().expect("first dependency");
        let second = tempfile::tempdir().expect("second dependency");
        let library = tempfile::tempdir().expect("library");
        let a = module(family.path(), "VF5Check", &[("Shared", false)]);
        let b = module(first.path(), "Shared", &[("Leaf", false)]);
        let c = module(second.path(), "Leaf", &[]);
        let dependencies = dependency_roots(&[
            "--dependency-root".into(), first.path().to_owned(),
            "--dependency-root".into(), second.path().to_owned(),
        ]).expect("explicit ordered roots");
        let output = root.path().join("package");
        package(family.path(), library.path(), &source_book(root.path()), &output, &dependencies)
            .expect("capture the real graph across three roots");
        let manifest: serde_json::Value = serde_json::from_slice(
            &std::fs::read(output.join("vf5-base-v1.json")).expect("manifest"),
        ).expect("manifest JSON");
        let modules = manifest["modules"].as_array().expect("actual population");
        assert_eq!(modules.len(), 3);
        for (name, bytes) in [("VF5Check", a), ("Shared", b), ("Leaf", c)] {
            let relative = format!("{name}.olean");
            let row = modules.iter().find(|row| row["path"] == relative).expect("captured member");
            assert_eq!(row["base_sha256"], hash(&bytes));
            assert_eq!(std::fs::read(output.join("modules").join(relative)).expect("part"), bytes);
        }
        assert!(matches!(
            trust_certify::calculus_row::base::measure_package(&output),
            Err(trust_certify::calculus_row::base::Vf5BaseMiss::InvalidPackage(_)),
        ), "captured test containers never become a mathematical base");
    }

    #[test]
    fn missing_dependency_refuses_and_keeps_failed_output_instead_of_overwriting_it() {
        let root = tempfile::tempdir().expect("root");
        let family = tempfile::tempdir().expect("family");
        let dependency = tempfile::tempdir().expect("dependency");
        let library = tempfile::tempdir().expect("library");
        module(family.path(), "VF5Check", &[("Shared", false)]);
        module(dependency.path(), "Shared", &[]);
        let book = source_book(root.path());
        let output = root.path().join("failed");
        let error = package(family.path(), library.path(), &book, &output, &[])
            .expect_err("a missing import is a refusal");
        assert!(error.contains("untrusted import"));
        assert!(output.is_dir());
        assert!(!output.join("vf5-base-v1.json").exists());
        std::fs::write(output.join("keep-original-failure"), b"original").expect("failure marker");
        assert!(package(
            family.path(), library.path(), &book, &output, &[dependency.path().to_owned()],
        ).is_err(), "a retry must use a new output");
        assert_eq!(std::fs::read(output.join("keep-original-failure")).expect("marker"), b"original");
    }

    #[test]
    fn dependency_root_cannot_supply_the_required_primary_vf5check() {
        let root = tempfile::tempdir().expect("root");
        let family = tempfile::tempdir().expect("empty primary family");
        let dependency = tempfile::tempdir().expect("old dependency");
        let library = tempfile::tempdir().expect("library");
        module(dependency.path(), "VF5Check", &[]);
        let output = root.path().join("refused");
        let error = package(
            family.path(), library.path(), &source_book(root.path()), &output,
            &[dependency.path().to_owned()],
        ).expect_err("do not substitute the old root");
        assert!(error.contains("primary family directory"), "{error}");
        assert!(!output.join("modules/VF5Check.olean").exists());
        assert!(!output.join("vf5-base-v1.json").exists());
    }

    #[test]
    fn an_invalid_first_dependency_is_not_replaced_by_a_later_valid_alias() {
        let root = tempfile::tempdir().expect("root");
        let family = tempfile::tempdir().expect("family");
        let first = tempfile::tempdir().expect("first dependency");
        let second = tempfile::tempdir().expect("second dependency");
        let library = tempfile::tempdir().expect("library");
        module(family.path(), "VF5Check", &[("Shared", false)]);
        std::fs::write(first.path().join("Shared.olean"), b"not an olean").expect("malformed part");
        module(second.path(), "Shared", &[]);
        let output = root.path().join("refused");
        assert!(package(
            family.path(), library.path(), &source_book(root.path()), &output,
            &[first.path().to_owned(), second.path().to_owned()],
        ).is_err(), "the first resolved malformed part is a refusal, not fallback");
        assert!(!output.join("vf5-base-v1.json").exists());
    }

    #[test]
    fn proposal_dependencies_cannot_replace_the_missing_repaired_family_root() {
        let root = tempfile::tempdir().expect("root");
        let generated = tempfile::tempdir().expect("generated");
        let family = tempfile::tempdir().expect("empty repaired family");
        let dependency = tempfile::tempdir().expect("old context");
        let library = tempfile::tempdir().expect("library");
        module(generated.path(), "TrustVF5Proposal", &[("VF5Check", false)]);
        module(dependency.path(), "VF5Check", &[]);
        let output = root.path().join("must-not-be-written.hint");
        let error = proposal(
            generated.path(), family.path(), library.path(), &root.path().join("absent-artifact"),
            &output, &[dependency.path().to_owned()],
        ).expect_err("the old family is not the new primary root");
        assert!(error.contains("declared primary directories"), "{error}");
        assert!(!output.exists());
    }

    #[test]
    fn colocated_primary_modules_reach_proposal_value_validation() {
        let root = tempfile::tempdir().expect("root");
        let work = tempfile::tempdir().expect("the maintained producer's shared work directory");
        let library = tempfile::tempdir().expect("library");
        module(work.path(), "TrustVF5Proposal", &[("VF5Check", false)]);
        module(work.path(), "VF5Check", &[]);
        let artifact = root.path().join("artifact");
        std::fs::write(&artifact, b"untrusted-container-data").expect("untrusted input");
        let output = root.path().join("no-mathematical-proposal.hint");
        let error = proposal(
            work.path(), work.path(), library.path(), &artifact, &output, &[],
        ).expect_err("empty containers have no mathematical proposal expressions");
        assert!(error.contains("proposal expression absent: TrustVF5Proposal.annotation"), "{error}");
        assert!(!output.exists());
    }
}

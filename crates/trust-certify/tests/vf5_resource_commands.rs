// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Actual host executable controls. Build this source's prepare_vf5_inputs
//! binary, bind TRUST_VF5_RESOURCE_TOOL to Cargo's emitted executable, then
//! select this required-feature target. Missing executable input fails.
//! Arbitrary fixture bytes test DATA transport, never theorem admission.

#![cfg(any(target_os = "macos", target_os = "linux"))]

use std::ffi::OsStr;
use std::path::PathBuf;
use std::process::{Command, Output};

use serde_json::Value;
use sha2::{Digest, Sha256};

fn tool() -> PathBuf {
    let path = PathBuf::from(std::env::var_os("TRUST_VF5_RESOURCE_TOOL")
        .expect("selected actual VF5 command controls require TRUST_VF5_RESOURCE_TOOL"));
    let metadata = std::fs::symlink_metadata(&path).expect("actual VF5 binary input must exist");
    assert!(metadata.is_file() && !metadata.file_type().is_symlink(), "actual binary must be a regular file");
    path
}

fn run(args: &[&OsStr]) -> Output {
    Command::new(tool()).args(args).output().expect("execute the actual declared VF5 resource binary")
}
fn success(output: Output) -> Value {
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    serde_json::from_slice(&output.stdout).expect("one complete actual host JSON response")
}

struct Fixture { _temporary: tempfile::TempDir, root: PathBuf, package: PathBuf, output: PathBuf, digest: String }
impl Fixture {
    fn new() -> Self {
        let temporary = tempfile::tempdir().unwrap();
        let root = temporary.path().canonicalize().unwrap();
        let package = root.join("package");
        let output = root.join("sysroot");
        std::fs::create_dir_all(package.join("modules")).unwrap();
        std::fs::create_dir(&output).unwrap();
        let hash = |bytes: &[u8]| format!("{:x}", Sha256::digest(bytes));
        std::fs::write(package.join("modules/VF5Check.olean"), b"raw DATA").unwrap();
        let manifest = serde_json::to_vec(&serde_json::json!({
            "schema":1,"clean_revision":"24861300fea40294bb485bb630eb216756dc558d",
            "lean_world":"v4.30.0-rc2","source_files":{"VF5Check.lean":hash(b"source DATA")},
            "modules":[{"path":"VF5Check.olean","base_sha256":hash(b"raw DATA"),
                "server_sha256":null,"private_sha256":null,"ir_sha256":null}],
        })).unwrap();
        std::fs::write(package.join("vf5-base-v1.json"), &manifest).unwrap();
        Self { _temporary: temporary, root, package, output, digest: hash(&manifest) }
    }
    fn stage(&self) -> Output {
        run(&[OsStr::new("stage-sysroot-resource"), self.package.as_os_str(),
            OsStr::new(&self.digest), self.output.as_os_str()])
    }
    fn installed(&self) -> PathBuf { self.output.join("lib/trust/vf5-base-v1") }
}

#[test]
fn actual_pin_off_policy_without_any_input_has_the_exact_runtime_source_contract() {
    let response = success(run(&[OsStr::new("resource-policy")]));
    let expected = serde_json::to_value(
        trust_certify::calculus_row::base::resource::resource_policy().unwrap(),
    ).unwrap();
    assert_eq!(response, expected);
    assert_eq!(response["schema"], 1);
    assert_eq!(response["kind"], "vf5-resource-policy-v1");
    assert_eq!(response["production_admission"], false);
    // This source has no independently admitted production package. A future
    // reviewed pin train must supply genuine package fixtures to requalify it.
    assert_eq!(response["production_pin_required"], false);
    assert_eq!(response["allowed_packages"], serde_json::json!([]));
}

#[test]
fn actual_fixed_source_identity_is_the_consumers_input_not_a_package_pin() {
    let response = success(run(&[OsStr::new("source-identity")]));
    let (revision, world) = trust_certify::calculus_row::base::fixed_source_identity();
    assert_eq!(response, serde_json::json!({
        "schema": 1,
        "kind": "vf5-fixed-source-identity-v1",
        "clean_revision": revision,
        "lean_world": world,
        "production_admission": false,
    }));
    assert!(!trust_certify::calculus_row::base::has_production_pin());
    let extra = run(&[OsStr::new("source-identity"), OsStr::new("extra")]);
    assert_eq!(extra.status.code(), Some(2));
    assert!(extra.stdout.is_empty());
}

#[test]
fn actual_stage_command_publishes_exact_data_and_only_reuses_an_identical_resource() {
    let fixture = Fixture::new();
    let first = success(fixture.stage());
    assert_eq!(first["kind"], "vf5-resource-staging-v1");
    assert_eq!(first["schema"], 1);
    assert_eq!(first["production_admission"], false);
    assert_eq!(first["report"]["manifest_sha256"], fixture.digest);
    assert_eq!(first["report"]["modules"], 1);
    assert_eq!(first["report"]["files"], 2);
    assert_eq!(first["report"]["reused"], false);
    assert_eq!(std::fs::read(fixture.installed().join("modules/VF5Check.olean")).unwrap(), b"raw DATA");
    assert_eq!(success(fixture.stage())["report"]["reused"], true);
    // Distribution's input is the actual installed resource, not the original
    // package. Exercise that same exact command against another owned image.
    let image = fixture.root.join("dist-image");
    std::fs::create_dir(&image).unwrap();
    success(run(&[OsStr::new("stage-sysroot-resource"), fixture.installed().as_os_str(),
        OsStr::new(&fixture.digest), image.as_os_str()]));
    assert_eq!(std::fs::read(image.join("lib/trust/vf5-base-v1/modules/VF5Check.olean")).unwrap(), b"raw DATA");
}

#[test]
fn actual_command_refuses_the_previous_clean_cohort_even_with_its_exact_manifest_hash() {
    let mut fixture = Fixture::new();
    let path = fixture.package.join("vf5-base-v1.json");
    let mut manifest: Value = serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
    manifest["clean_revision"] = Value::String("4f1ed6705576dbfed6b02a6ed8baa2f5a73b041a".into());
    let bytes = serde_json::to_vec(&manifest).unwrap();
    fixture.digest = format!("{:x}", Sha256::digest(&bytes));
    std::fs::write(path, bytes).unwrap();
    let output = fixture.stage();
    assert!(!output.status.success(), "the old cohort is not this compiled consumer's input");
    assert!(!fixture.output.join("lib").exists(), "refusal must precede output parents");
}

#[test]
fn actual_command_refuses_malformed_changed_absent_and_unlisted_inputs_without_parents() {
    for mutation in 0..5 {
        let fixture = Fixture::new();
        match mutation {
            0 => std::fs::write(fixture.package.join("vf5-base-v1.json"), b"{}").unwrap(),
            1 => std::fs::write(fixture.package.join("modules/VF5Check.olean"), b"changed").unwrap(),
            2 => std::fs::remove_file(fixture.package.join("modules/VF5Check.olean")).unwrap(),
            3 => std::fs::write(fixture.package.join("modules/VF5Check.ir"), b"not absent").unwrap(),
            4 => std::fs::write(fixture.package.join("unknown"), b"extra").unwrap(),
            _ => unreachable!(),
        }
        let response = fixture.stage();
        assert!(!response.status.success(), "mutation {mutation}");
        assert!(response.stdout.is_empty());
        assert!(!fixture.output.join("lib").exists());
    }
}

#[test]
fn actual_command_refuses_a_correctly_hashed_invalid_manifest_and_malformed_requested_digest() {
    let mut fixture = Fixture::new();
    let invalid = b"{\"schema\":2}";
    std::fs::write(fixture.package.join("vf5-base-v1.json"), invalid).unwrap();
    fixture.digest = format!("{:x}", Sha256::digest(invalid));
    assert!(!fixture.stage().status.success());
    assert!(!fixture.output.join("lib").exists());
    let fixture = Fixture::new();
    for digest in ["short".to_owned(), "A0".repeat(32), "00".repeat(32)] {
        assert!(!run(&[OsStr::new("stage-sysroot-resource"), fixture.package.as_os_str(),
            OsStr::new(&digest), fixture.output.as_os_str()]).status.success());
        assert!(!fixture.output.join("lib").exists());
    }
}

#[test]
fn actual_command_refuses_both_overlap_directions_and_unknown_existing_resource() {
    let fixture = Fixture::new();
    let nested = fixture.package.join("modules");
    for output in [&nested, &fixture.root] {
        assert!(!run(&[OsStr::new("stage-sysroot-resource"), fixture.package.as_os_str(),
            OsStr::new(&fixture.digest), output.as_os_str()]).status.success());
        assert!(!output.join("lib").exists());
    }
    let fixture = Fixture::new();
    std::fs::create_dir_all(fixture.installed()).unwrap();
    std::fs::write(fixture.installed().join("keep"), b"unknown existing resource").unwrap();
    assert!(!fixture.stage().status.success());
    assert_eq!(std::fs::read(fixture.installed().join("keep")).unwrap(), b"unknown existing resource");
}

#[test]
fn actual_command_refuses_input_and_output_aliases_and_bad_command_shapes() {
    let fixture = Fixture::new();
    let alias = fixture.root.join("package-alias");
    std::os::unix::fs::symlink(&fixture.package, &alias).unwrap();
    assert!(!run(&[OsStr::new("stage-sysroot-resource"), alias.as_os_str(),
        OsStr::new(&fixture.digest), fixture.output.as_os_str()]).status.success());
    let outside = fixture.root.join("outside");
    std::fs::create_dir(&outside).unwrap();
    std::os::unix::fs::symlink(&outside, fixture.output.join("lib")).unwrap();
    assert!(!fixture.stage().status.success());
    assert_eq!(std::fs::read_dir(&outside).unwrap().count(), 0);
    for args in [vec!["resource-policy", "extra"], vec!["stage-sysroot-resource"], vec!["unknown"]] {
        let output = run(&args.iter().map(|arg| OsStr::new(*arg)).collect::<Vec<_>>());
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
    }
}

#[test]
fn actual_command_refuses_every_publicly_writable_parent_before_output_mutation() {
    use std::os::unix::fs::{MetadataExt, PermissionsExt};
    for mode in [0o775, 0o777] {
        for role in 0..3 {
            let fixture = Fixture::new();
            let parent = match role {
                0 => fixture.output.clone(),
                1 => fixture.output.join("lib"),
                2 => fixture.output.join("lib/trust"),
                _ => unreachable!(),
            };
            std::fs::create_dir_all(&parent).unwrap();
            std::fs::set_permissions(&parent, std::fs::Permissions::from_mode(mode)).unwrap();
            let response = fixture.stage();
            assert!(!response.status.success(), "role {role}, mode {mode:o}");
            assert!(response.stdout.is_empty());
            assert_eq!(std::fs::read_dir(&parent).unwrap().count(), 0);
            assert_eq!(std::fs::metadata(&parent).unwrap().mode() & 0o7777, mode);
        }
    }
}

#[cfg(target_os = "macos")]
#[test]
fn actual_command_refuses_acl_parent_grants_before_output_mutation() {
    use std::os::unix::fs::MetadataExt;
    for role in 0..3 {
        let fixture = Fixture::new();
        let parent = match role {
            0 => fixture.output.clone(),
            1 => fixture.output.join("lib"),
            2 => fixture.output.join("lib/trust"),
            _ => unreachable!(),
        };
        std::fs::create_dir_all(&parent).unwrap();
        let output = Command::new("/bin/chmod").arg("+a")
            .arg("everyone allow add_file,add_subdirectory,delete_child")
            .arg(&parent).output().unwrap();
        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
        assert_eq!(std::fs::metadata(&parent).unwrap().mode() & 0o022, 0);
        let response = fixture.stage();
        assert!(!response.status.success());
        assert!(response.stdout.is_empty());
        assert_eq!(std::fs::read_dir(&parent).unwrap().count(), 0);
    }
}

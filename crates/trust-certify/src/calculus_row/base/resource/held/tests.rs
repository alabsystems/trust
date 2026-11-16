// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use std::os::unix::fs::symlink;
use std::os::unix::fs::PermissionsExt;
use super::super::super::{CLEAN_REVISION, LEAN_WORLD};

struct Fixture { _temporary: tempfile::TempDir, root: PathBuf, package: PathBuf, output: PathBuf, digest: String }
impl Fixture {
    fn new(companions: bool) -> Self {
        let temporary = tempfile::tempdir().unwrap();
        let root = temporary.path().canonicalize().unwrap();
        let package = root.join("package");
        let output = root.join("sysroot");
        std::fs::create_dir_all(package.join("modules")).unwrap();
        std::fs::create_dir(&output).unwrap();
        std::fs::write(package.join("modules/VF5Check.olean"), b"base data").unwrap();
        let hash = |bytes: &[u8]| format!("{:x}", Sha256::digest(bytes));
        let mut module = serde_json::json!({"path":"VF5Check.olean", "base_sha256":hash(b"base data"),
            "server_sha256":null,"private_sha256":null,"ir_sha256":null});
        if companions {
            for (field, file, contents) in [
                ("server_sha256", "VF5Check.olean.server", &b"server"[..]),
                ("private_sha256", "VF5Check.olean.private", &b"private"[..]),
                ("ir_sha256", "VF5Check.ir", &b"ir"[..]),
            ] {
                module[field] = hash(contents).into();
                std::fs::write(package.join("modules").join(file), contents).unwrap();
            }
        }
        let manifest = serde_json::to_vec(&serde_json::json!({
            "schema":1,"clean_revision":CLEAN_REVISION,
            "lean_world":LEAN_WORLD,
            "source_files":{"VF5Check.lean":hash(b"source identity data")},"modules":[module],
        })).unwrap();
        std::fs::write(package.join(MANIFEST), &manifest).unwrap();
        Self { _temporary: temporary, root, package, output, digest: hash(&manifest) }
    }
    fn stage(&self) -> Result<StageReport, String> { stage(&self.package, &self.digest, &self.output) }
    fn installed(&self) -> PathBuf { self.output.join("lib/trust").join(RESOURCE) }
}

#[test]
fn real_descriptor_staging_copies_all_parts_and_reuses_only_identical_data() {
    let fixture = Fixture::new(true);
    let report = fixture.stage().unwrap();
    assert_eq!((report.modules, report.files, report.reused), (1, 5, false));
    assert_eq!(report.bytes, [MANIFEST, "modules/VF5Check.olean", "modules/VF5Check.olean.server",
        "modules/VF5Check.olean.private", "modules/VF5Check.ir"].iter()
        .map(|path| std::fs::metadata(fixture.package.join(path)).unwrap().len()).sum::<u64>());
    assert_eq!(std::fs::read(fixture.installed().join("modules/VF5Check.olean.private")).unwrap(), b"private");
    assert!(fixture.stage().unwrap().reused);
    std::fs::write(fixture.installed().join("modules/VF5Check.ir"), b"changed").unwrap();
    assert!(fixture.stage().is_err());
    assert_eq!(std::fs::read(fixture.installed().join("modules/VF5Check.ir")).unwrap(), b"changed");
}

#[test]
fn complete_inventory_and_hash_failures_precede_any_output_parent_creation() {
    for mutation in 0..7 {
        let fixture = Fixture::new(false);
        match mutation {
            0 => std::fs::write(fixture.package.join(MANIFEST), b"{}").unwrap(),
            1 => std::fs::write(fixture.package.join("modules/VF5Check.olean"), b"changed").unwrap(),
            2 => std::fs::write(fixture.package.join("modules/VF5Check.ir"), b"unexpected companion").unwrap(),
            3 => std::fs::write(fixture.package.join("unlisted"), b"unknown").unwrap(),
            4 => std::fs::remove_file(fixture.package.join("modules/VF5Check.olean")).unwrap(),
            5 => std::fs::create_dir(fixture.package.join("unused")).unwrap(),
            6 => File::create(fixture.package.join("modules/VF5Check.olean")).unwrap().set_len(MAX_PART_BYTES + 1).unwrap(),
            _ => unreachable!(),
        }
        assert!(fixture.stage().is_err(), "mutation {mutation}");
        assert!(!fixture.output.join("lib").exists(), "mutation {mutation} made a parent");
    }
}

#[test]
fn correctly_hashed_malformed_manifests_refuse_at_the_shared_runtime_validator() {
    for mutation in 0..8 {
        let mut fixture = Fixture::new(false);
        let path = fixture.package.join(MANIFEST);
        let mut manifest: serde_json::Value = serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
        match mutation {
            0 => manifest["schema"] = 2.into(),
            1 => manifest["clean_revision"] = "unknown".into(),
            2 => manifest["lean_world"] = "unknown".into(),
            3 => manifest["source_files"] = serde_json::json!({}),
            4 => manifest["modules"] = serde_json::json!([]),
            5 => manifest["modules"][0]["path"] = "../VF5Check.olean".into(),
            6 => manifest["modules"][0]["base_sha256"] = "short".into(),
            7 => manifest["unknown"] = true.into(),
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec(&manifest).unwrap();
        fixture.digest = format!("{:x}", Sha256::digest(&bytes));
        std::fs::write(path, bytes).unwrap();
        assert!(fixture.stage().is_err(), "manifest mutation {mutation}");
        assert!(!fixture.output.join("lib").exists());
    }
}

#[test]
fn both_ancestry_overlaps_refuse_before_mutating_source_or_output() {
    let fixture = Fixture::new(false);
    // This existing directory is already valid in the package inventory, so
    // an unrelated unknown-member refusal cannot conceal a missing overlap guard.
    let nested_output = fixture.package.join("modules");
    assert!(stage(&fixture.package, &fixture.digest, &nested_output).is_err());
    assert!(!nested_output.join("lib").exists());
    assert!(stage(&fixture.package, &fixture.digest, &fixture.root).is_err());
    assert!(!fixture.root.join("lib").exists());
    assert!(stage(&fixture.package, &fixture.digest, &fixture.package).is_err());
    assert!(!fixture.package.join("lib").exists());
}

#[test]
fn input_and_output_aliases_never_supply_missing_or_outside_data() {
    let fixture = Fixture::new(false);
    let alias = fixture.root.join("package-alias");
    symlink(&fixture.package, &alias).unwrap();
    assert!(stage(&alias, &fixture.digest, &fixture.output).is_err());
    std::fs::remove_file(fixture.package.join("modules/VF5Check.olean")).unwrap();
    let outside_file = fixture.root.join("outside.olean");
    std::fs::write(&outside_file, b"base data").unwrap();
    symlink(&outside_file, fixture.package.join("modules/VF5Check.olean")).unwrap();
    assert!(fixture.stage().is_err());
    assert!(!fixture.output.join("lib").exists());
    let fixture = Fixture::new(false);
    let outside = fixture.root.join("outside");
    std::fs::create_dir(&outside).unwrap();
    symlink(&outside, fixture.output.join("lib")).unwrap();
    assert!(fixture.stage().is_err());
    assert_eq!(std::fs::read_dir(&outside).unwrap().count(), 0);
}

#[test]
fn sanctioned_literal_build_alias_works_but_chained_or_dot_aliases_refuse() {
    for target in ["build.noindex", "./build.noindex", "chain"] {
        let fixture = Fixture::new(false);
        let physical = fixture.root.join("build.noindex");
        std::fs::create_dir(&physical).unwrap();
        std::fs::create_dir(physical.join("stage1")).unwrap();
        symlink("build.noindex", fixture.root.join("chain")).unwrap();
        symlink(target, fixture.root.join("build")).unwrap();
        let result = stage(&fixture.package, &fixture.digest, &fixture.root.join("build/stage1"));
        assert_eq!(result.is_ok(), target == "build.noindex", "{target}");
    }
}

#[test]
fn unknown_existing_resource_is_never_overwritten_even_if_empty() {
    for populated in [false, true] {
        let fixture = Fixture::new(false);
        std::fs::create_dir_all(fixture.installed()).unwrap();
        if populated { std::fs::write(fixture.installed().join("unknown"), b"keep").unwrap(); }
        assert!(fixture.stage().is_err());
        assert_eq!(std::fs::read_dir(fixture.installed()).unwrap().count(), usize::from(populated));
    }
}

#[test]
fn parent_name_swap_cannot_redirect_staged_writes_outside_the_held_tree() {
    for swap_lib in [false, true] {
        let fixture = Fixture::new(false);
        let outside = fixture.root.join("outside");
        std::fs::create_dir(&outside).unwrap();
        let result = stage_with_hook(&fixture.package, &fixture.digest, &fixture.output, || {
            let path = fixture.output.join(if swap_lib { "lib" } else { "lib/trust" });
            std::fs::rename(&path, fixture.root.join("old-parent")).unwrap();
            symlink(&outside, &path).unwrap();
        });
        assert!(result.is_err());
        assert_eq!(std::fs::read_dir(&outside).unwrap().count(), 0);
        assert!(!fixture.root.join("old-parent").join(RESOURCE).exists());
    }
}

#[test]
fn output_root_or_source_swap_refuses_before_any_payload_is_copied() {
    for swap_source in [false, true] {
        let fixture = Fixture::new(false);
        let result = stage_with_hook(&fixture.package, &fixture.digest, &fixture.output, || {
            let selected = if swap_source { &fixture.package } else { &fixture.output };
            std::fs::rename(selected, fixture.root.join("old-root")).unwrap();
            std::fs::create_dir(selected).unwrap();
        });
        assert!(result.is_err());
        assert!(!fixture.installed().exists());
        assert!(!fixture.root.join("old-root/lib/trust").join(RESOURCE).exists());
    }
}

#[test]
fn source_change_and_racing_destination_refuse_without_replacing_a_resource() {
    for destination_race in [false, true] {
        let fixture = Fixture::new(false);
        let result = stage_with_hook(&fixture.package, &fixture.digest, &fixture.output, || {
            if destination_race { std::fs::create_dir(fixture.installed()).unwrap(); }
            else { std::fs::write(fixture.package.join("modules/VF5Check.olean"), b"changed").unwrap(); }
        });
        assert!(result.is_err());
        assert_eq!(fixture.installed().exists(), destination_race);
        if destination_race { assert_eq!(std::fs::read_dir(fixture.installed()).unwrap().count(), 0); }
    }
}

#[test]
fn every_unsafe_existing_mutation_parent_refuses_before_new_parent_or_stage_creation() {
    for mode in [0o775, 0o777, 0o1777] {
        for role in 0..3 {
            let fixture = Fixture::new(false);
            let selected = match role {
                0 => fixture.output.clone(),
                1 => fixture.output.join("lib"),
                2 => fixture.output.join("lib/trust"),
                _ => unreachable!(),
            };
            std::fs::create_dir_all(&selected).unwrap();
            std::fs::set_permissions(&selected, std::fs::Permissions::from_mode(mode)).unwrap();
            assert!(fixture.stage().is_err(), "role {role}, mode {mode:o}");
            assert_eq!(std::fs::read_dir(&selected).unwrap().count(), 0);
            assert_eq!(std::fs::metadata(&selected).unwrap().mode() & 0o7777, mode);
            assert!(!fixture.installed().exists());
        }
    }
}

#[test]
fn unsafe_nonsticky_output_namespace_refuses_but_sticky_owned_child_is_protected() {
    for mode in [0o777, 0o1777] {
        let fixture = Fixture::new(false);
        std::fs::set_permissions(&fixture.root, std::fs::Permissions::from_mode(mode)).unwrap();
        let result = fixture.stage();
        assert_eq!(result.is_ok(), mode == 0o1777);
        if mode == 0o777 { assert!(!fixture.output.join("lib").exists()); }
    }
}

#[test]
fn actual_staging_source_name_swap_at_final_publication_window_never_installs_replacement() {
    for reopen_parent in [false, true] {
        let fixture = Fixture::new(false);
        let parent = fixture.output.join("lib/trust");
        let result = stage_with_hooks(&fixture.package, &fixture.digest, &fixture.output, || {}, |_, temporary| {
            // This executes after the old final same_child check and fsync.
            // It deliberately uses current-UID authority to inject the exact
            // old source-name race; the primitive must detect it before rename.
            if reopen_parent {
                std::fs::set_permissions(&parent, std::fs::Permissions::from_mode(0o777)).unwrap();
            }
            std::fs::rename(parent.join(temporary), parent.join("saved-original")).unwrap();
            assert!(parent.join("saved-original").join(MANIFEST).is_file());
            std::fs::create_dir(parent.join(temporary)).unwrap();
            std::fs::write(parent.join(temporary).join("unvalidated"), b"wrong DATA").unwrap();
        });
        assert!(result.is_err());
        assert!(!fixture.installed().exists());
        assert!(parent.join("saved-original").join(MANIFEST).is_file());
        assert!(std::fs::read_dir(&parent).unwrap().any(|entry| {
            entry.unwrap().path().join("unvalidated").is_file()
        }));
    }
}

#[cfg(target_os = "macos")]
#[test]
fn actual_acl_grant_on_each_mutation_parent_refuses_before_new_output_creation() {
    for role in 0..3 {
        let fixture = Fixture::new(false);
        let selected = match role {
            0 => fixture.output.clone(),
            1 => fixture.output.join("lib"),
            2 => fixture.output.join("lib/trust"),
            _ => unreachable!(),
        };
        std::fs::create_dir_all(&selected).unwrap();
        let output = std::process::Command::new("/bin/chmod").arg("+a")
            .arg("everyone allow add_file,add_subdirectory,delete_child")
            .arg(&selected).output().unwrap();
        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
        assert_eq!(std::fs::metadata(&selected).unwrap().mode() & 0o022, 0);
        assert!(fixture.stage().is_err());
        assert_eq!(std::fs::read_dir(&selected).unwrap().count(), 0);
    }
}

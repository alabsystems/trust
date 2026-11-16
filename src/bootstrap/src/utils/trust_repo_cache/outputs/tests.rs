#![cfg(unix)]

use std::cell::Cell;
use std::fs;
use std::path::PathBuf;

use super::{InputSnapshot, OutputNamespace, RepositorySnapshot};
use crate::utils::trust_repo_cache::{Reuse, ReusePolicy, run, tree_digest};

// Trust: the WP wrapper's generated namespace is separate from the host sysroot.
#[test]
fn wp_outputs_are_bound_and_receipts_cannot_claim_ui_or_reuse() {
    let fixture = Fixture::new();
    fs::write(fixture.source.join(".gitignore"), "build/\nfirst-party/trust-wp/target/\n").unwrap();
    let target = fixture.source.join("first-party/trust-wp/target");
    fs::create_dir_all(&target).unwrap();
    let artifact = target.join("driver");
    fs::write(&artifact, b"first driver").unwrap();
    let outputs = OutputNamespace::TrustWp { repository: &fixture.source };
    let before = outputs.digest(&fixture.snapshot().unwrap(), &fixture.controls).unwrap();
    fs::write(&artifact, b"other driver").unwrap();
    assert_ne!(outputs.digest(&fixture.snapshot().unwrap(), &fixture.controls).unwrap(), before);
    let executions = Cell::new(0);
    for expected in [1, 2] {
        assert_eq!(
            super::super::run_wp(
                &fixture.controls,
                outputs,
                || fixture.snapshot(),
                || {
                    executions.set(executions.get() + 1);
                    Ok(())
                }
            )
            .unwrap(),
            Reuse::Executed,
        );
        assert_eq!(executions.get(), expected);
        let record: super::super::Success =
            serde_json::from_slice(&fs::read(fixture.controls.join("success.json")).unwrap())
                .unwrap();
        assert_ne!(record.authority, super::super::AUTHORITY);
        assert!(record.authority.contains("unverified WP workspace"));
    }
    assert!(
        super::super::run_wp(
            &fixture.controls,
            outputs,
            || fixture.snapshot(),
            || { Err("failed WP test".into()) }
        )
        .is_err()
    );
    assert!(!fixture.controls.join("success.json").exists());
    fs::rename(&target, fixture.source.join("build/moved-wp-target")).unwrap();
    std::os::unix::fs::symlink(fixture.source.join("build/moved-wp-target"), &target).unwrap();
    assert!(outputs.digest(&fixture.snapshot().unwrap(), &fixture.controls).is_err());
}

// Independently describe the actual local stage0/stage1 Sysroot layout.
const SOURCE_ALIAS: &str = "stage1/lib/rustlib/src/rust";
const SOURCE_ALIASES: [&str; 3] = [
    "stage0-sysroot/lib/rustlib/rustc-src/rust",
    "stage1/lib/rustlib/rustc-src/rust",
    SOURCE_ALIAS,
];

#[cfg(unix)]
struct Fixture {
    _temporary: tempfile::TempDir,
    source: PathBuf,
    host: PathBuf,
    controls: PathBuf,
    source_aliases: Vec<PathBuf>,
}

#[cfg(unix)]
impl Fixture {
    fn new() -> Self {
        let temporary = tempfile::tempdir().unwrap();
        let source = fs::canonicalize(temporary.path()).unwrap().join("repo");
        fs::create_dir(&source).unwrap();
        fs::write(source.join(".gitignore"), "build/\n").unwrap();
        fs::write(source.join("input.rs"), b"fn original() {}\n").unwrap();
        let host = source.join("build/host");
        let controls = source.join("build/trust-repo/task");
        let source_aliases = SOURCE_ALIASES.map(|relative| host.join(relative)).to_vec();
        for alias in &source_aliases {
            fs::create_dir_all(alias.parent().unwrap()).unwrap();
            std::os::unix::fs::symlink(&source, alias).unwrap();
        }
        fs::create_dir_all(&controls).unwrap();
        fs::write(controls.join("lock"), b"").unwrap();
        fs::create_dir(host.join("bin")).unwrap();
        fs::write(host.join("bin/trustc"), b"compiler bytes").unwrap();
        super::super::git(&source, &["init"]).unwrap();
        super::super::git(&source, &["add", "."]).unwrap();
        super::super::git(
            &source,
            &[
                "-c",
                "user.name=Native output test",
                "-c",
                "user.email=output@example.invalid",
                "-c",
                "commit.gpgsign=false",
                "commit",
                "-m",
                "fixture",
            ],
        )
        .unwrap();
        Self { _temporary: temporary, source, host, controls, source_aliases }
    }

    fn snapshot(&self) -> Result<InputSnapshot, String> {
        let repository = RepositorySnapshot::observe(&self.source, 2)?;
        Ok(InputSnapshot::new(repository.digest().to_owned(), repository))
    }

    fn outputs(&self) -> OutputNamespace<'_> {
        OutputNamespace::GeneratedHost {
            root: &self.host,
            repository: &self.source,
            source_aliases: &self.source_aliases,
        }
    }

    fn digest(&self) -> Result<String, String> {
        self.outputs().digest(&self.snapshot()?, &self.controls)
    }
}

#[cfg(unix)]
#[test]
fn all_declared_sysroot_source_aliases_do_not_overread_ignored_cache_files_or_fifos() {
    let fixture = Fixture::new();
    let cache = fixture.source.join("build/unrelated-cache");
    fs::create_dir(&cache).unwrap();
    fs::write(cache.join("artifact"), b"unrelated cached bytes").unwrap();
    let before = fixture.digest().unwrap();
    let fifo = cache.join("fifo");
    let encoded = std::ffi::CString::new(fifo.as_os_str().as_encoded_bytes()).unwrap();
    assert_eq!(unsafe { libc::mkfifo(encoded.as_ptr(), 0o600) }, 0);
    assert!(
        tree_digest(&fixture.host).unwrap_err().contains("unsupported"),
        "the previous recursive output reader enters this ignored tree"
    );
    assert_eq!(fixture.digest().unwrap(), before);
    fs::write(cache.join("artifact"), b"changed unrelated bytes").unwrap();
    assert_eq!(fixture.digest().unwrap(), before);
}

#[test]
fn undeclared_repository_root_alias_refuses_before_traversing_source_or_controls() {
    let fixture = Fixture::new();
    std::os::unix::fs::symlink(&fixture.source, fixture.host.join("unexpected-source")).unwrap();
    let fifo = fixture.source.join("build/unrelated-fifo");
    let encoded = std::ffi::CString::new(fifo.as_os_str().as_encoded_bytes()).unwrap();
    assert_eq!(unsafe { libc::mkfifo(encoded.as_ptr(), 0o600) }, 0);
    let error = fixture.digest().unwrap_err();
    assert!(error.contains("undeclared source-root route"), "{error}");
    assert!(!error.contains("unsupported"), "source contents must not be traversed: {error}");
}

#[test]
fn every_declared_alias_must_exist_and_retain_its_identity_between_output_hashes() {
    for relative in SOURCE_ALIASES {
        let fixture = Fixture::new();
        let alias = fixture.host.join(relative);
        fs::remove_file(&alias).unwrap();
        assert!(fixture.digest().is_err(), "missing alias {relative}");

        let fixture = Fixture::new();
        let alias = fixture.host.join(relative);
        let snapshots = Cell::new(0);
        let result = run(
            ReusePolicy::RecordOnly,
            &fixture.controls,
            fixture.outputs(),
            || {
                snapshots.set(snapshots.get() + 1);
                if snapshots.get() == 2 {
                    let preserved = alias.with_file_name("preserved-rust");
                    fs::rename(&alias, preserved).unwrap();
                    std::os::unix::fs::symlink(&fixture.source, &alias).unwrap();
                }
                fixture.snapshot()
            },
            || Ok(()),
        );
        let error = result.unwrap_err();
        assert!(error.contains("moved"), "replaced alias {relative}: {error}");
        assert!(!fixture.controls.join("success.json").exists());
    }
}

#[test]
fn alias_declarations_are_nonempty_distinct_and_confined_to_the_host_namespace() {
    let fixture = Fixture::new();
    let observe = |aliases: &[PathBuf]| {
        OutputNamespace::GeneratedHost {
            root: &fixture.host,
            repository: &fixture.source,
            source_aliases: aliases,
        }
        .digest(&fixture.snapshot().unwrap(), &fixture.controls)
    };
    assert!(observe(&[]).is_err());
    let alias = fixture.host.join(SOURCE_ALIAS);
    assert!(observe(&[alias.clone(), alias]).is_err());
    assert!(observe(&[fixture.source.join("outside")]).is_err());
    assert!(observe(&[fixture.host.join("stage1/../source")]).is_err());
}

#[cfg(unix)]
#[test]
fn saved_record_is_outside_its_own_generated_artifact_identity() {
    let fixture = Fixture::new();
    let recursive = tree_digest(&fixture.host).unwrap();
    let expected = fixture.digest().unwrap();
    let executions = Cell::new(0);
    for expected_executions in [1, 2] {
        assert_eq!(
            run(
                ReusePolicy::RecordOnly,
                &fixture.controls,
                fixture.outputs(),
                || fixture.snapshot(),
                || {
                    executions.set(executions.get() + 1);
                    Ok(())
                },
            )
            .unwrap(),
            Reuse::Executed
        );
        assert_eq!(executions.get(), expected_executions);
        let record: super::super::Success =
            serde_json::from_slice(&fs::read(fixture.controls.join("success.json")).unwrap())
                .unwrap();
        assert_eq!(record.outputs, expected);
        assert_eq!(
            fixture.digest().unwrap(),
            expected,
            "publication must not invalidate the artifact identity it records"
        );
    }
    assert_ne!(
        tree_digest(&fixture.host).unwrap(),
        recursive,
        "the previous recursive namespace includes its own new success record"
    );
}

#[cfg(unix)]
#[test]
fn generated_bytes_git_named_artifacts_and_observed_source_bytes_all_remain_bound() {
    let fixture = Fixture::new();
    fs::create_dir(fixture.host.join(".git")).unwrap();
    fs::write(fixture.host.join(".git/generated"), b"first").unwrap();
    let before = fixture.digest().unwrap();
    let artifact = fixture.host.join("bin/trustc");
    let modified = fs::metadata(&artifact).unwrap().modified().unwrap();
    fs::write(&artifact, b"mutated! bytes").unwrap();
    fs::File::open(&artifact).unwrap().set_modified(modified).unwrap();
    assert_ne!(fixture.digest().unwrap(), before);
    fs::write(&artifact, b"compiler bytes").unwrap();
    assert_eq!(fixture.digest().unwrap(), before);
    fs::write(fixture.host.join(".git/generated"), b"other").unwrap();
    assert_ne!(fixture.digest().unwrap(), before, "artifact names do not exempt bytes");
    fs::write(fixture.host.join(".git/generated"), b"first").unwrap();
    fs::write(fixture.source.join("input.rs"), b"fn changed_() {}\n").unwrap();
    assert_ne!(
        fixture.digest().unwrap(),
        before,
        "the declared alias binds the actual observed repository source digest"
    );
}

#[cfg(unix)]
#[test]
fn tracked_source_changes_during_execution_cannot_publish_success() {
    let fixture = Fixture::new();
    let result = run(
        ReusePolicy::RecordOnly,
        &fixture.controls,
        fixture.outputs(),
        || fixture.snapshot(),
        || {
            fs::write(fixture.source.join("input.rs"), b"fn changed_() {}\n").unwrap();
            Ok(())
        },
    );
    assert!(result.unwrap_err().contains("inputs moved"));
    assert!(!fixture.controls.join("success.json").exists());
}

#[cfg(unix)]
#[test]
fn generated_artifacts_are_rechecked_after_the_final_input_snapshot() {
    let fixture = Fixture::new();
    let snapshots = Cell::new(0);
    let result = run(
        ReusePolicy::RecordOnly,
        &fixture.controls,
        fixture.outputs(),
        || {
            snapshots.set(snapshots.get() + 1);
            if snapshots.get() == 2 {
                fs::write(fixture.host.join("bin/trustc"), b"tampered bytes").unwrap();
            }
            fixture.snapshot()
        },
        || Ok(()),
    );
    assert!(result.unwrap_err().contains("outputs moved"));
    assert!(!fixture.controls.join("success.json").exists());
}

#[test]
fn alias_namespace_identity_survives_the_intervening_input_observation() {
    for replacement in ["alias", "parent", "route"] {
        let fixture = Fixture::new();
        let alias = fixture.host.join(SOURCE_ALIAS);
        let route = fixture.source.join("build/route");
        if replacement == "route" {
            std::os::unix::fs::symlink(&fixture.source, &route).unwrap();
            fs::remove_file(&alias).unwrap();
            std::os::unix::fs::symlink(&route, &alias).unwrap();
        }
        let snapshots = Cell::new(0);
        let original_inputs = fixture.snapshot().unwrap();
        let result = run(
            ReusePolicy::RecordOnly,
            &fixture.controls,
            fixture.outputs(),
            || {
                snapshots.set(snapshots.get() + 1);
                if snapshots.get() == 2 {
                    let preserved = fixture.source.join("build/preserved");
                    match replacement {
                        "alias" => {
                            fs::rename(&alias, preserved).unwrap();
                            std::os::unix::fs::symlink(&fixture.source, &alias).unwrap();
                        }
                        "parent" => {
                            let parent = alias.parent().unwrap();
                            fs::rename(parent, preserved).unwrap();
                            fs::create_dir(parent).unwrap();
                            std::os::unix::fs::symlink(&fixture.source, &alias).unwrap();
                        }
                        "route" => {
                            fs::rename(&route, preserved).unwrap();
                            std::os::unix::fs::symlink(&fixture.source, &route).unwrap();
                        }
                        _ => unreachable!(),
                    }
                }
                let current = fixture.snapshot()?;
                assert_eq!(
                    current, original_inputs,
                    "these replacements are outside source inputs"
                );
                Ok(current)
            },
            || Ok(()),
        );
        assert!(result.unwrap_err().contains("namespace"), "{replacement}");
        assert!(!fixture.controls.join("success.json").exists());
    }
}

#[cfg(unix)]
#[test]
fn ordinary_artifact_links_keep_required_target_bytes_and_dangling_refusal() {
    let fixture = Fixture::new();
    let external = fixture.source.join("build/required-tool");
    fs::write(&external, b"first required tool").unwrap();
    std::os::unix::fs::symlink(&external, fixture.host.join("tool")).unwrap();
    let before = fixture.digest().unwrap();
    fs::write(&external, b"other required tool").unwrap();
    assert_ne!(fixture.digest().unwrap(), before);
    fs::remove_file(&external).unwrap();
    assert!(fixture.digest().unwrap_err().contains("tool"));
}

#[cfg(unix)]
#[test]
fn wrong_missing_dangling_and_nonsymlink_source_aliases_refuse() {
    for kind in ["wrong", "missing", "dangling", "directory"] {
        let fixture = Fixture::new();
        let alias = fixture.host.join(SOURCE_ALIAS);
        fs::remove_file(&alias).unwrap();
        match kind {
            "wrong" => std::os::unix::fs::symlink(&fixture.host, &alias).unwrap(),
            "dangling" => {
                std::os::unix::fs::symlink(fixture.source.join("absent"), &alias).unwrap()
            }
            "directory" => fs::create_dir(&alias).unwrap(),
            "missing" => (),
            _ => unreachable!(),
        }
        assert!(fixture.digest().is_err(), "{kind} source alias must refuse");
    }
}

#[cfg(unix)]
#[test]
fn source_alias_and_parent_replacement_are_detected_through_open_descriptors() {
    for replace_parent in [false, true] {
        let fixture = Fixture::new();
        let snapshot = fixture.snapshot().unwrap();
        let alias = fixture.host.join(SOURCE_ALIAS);
        let result = fixture.outputs().digest_with_hook(&snapshot, &fixture.controls, || {
            if replace_parent {
                let parent = alias.parent().unwrap();
                let moved = parent.with_file_name("preserved-src");
                fs::rename(parent, &moved).unwrap();
                std::os::unix::fs::symlink(&moved, parent).unwrap();
            } else {
                fs::rename(&alias, alias.with_file_name("preserved-rust")).unwrap();
                std::os::unix::fs::symlink(&fixture.source, &alias).unwrap();
            }
        });
        assert!(result.is_err(), "same-target alias/parent replacement must refuse");
    }
}

#[cfg(unix)]
#[test]
fn source_alias_route_replacement_with_the_same_canonical_target_refuses() {
    for suffix in ["", "/", "/."] {
        let fixture = Fixture::new();
        let route = fixture.source.join("build/route");
        std::os::unix::fs::symlink(&fixture.source, &route).unwrap();
        let alias = fixture.host.join(SOURCE_ALIAS);
        fs::remove_file(&alias).unwrap();
        std::os::unix::fs::symlink(format!("{}{suffix}", route.display()), &alias).unwrap();
        let snapshot = fixture.snapshot().unwrap();
        let result = fixture.outputs().digest_with_hook(&snapshot, &fixture.controls, || {
            fs::rename(&route, route.with_file_name("preserved-route")).unwrap();
            std::os::unix::fs::symlink(&fixture.source, &route).unwrap();
        });
        assert!(result.unwrap_err().contains("route moved"), "suffix {suffix:?}");
    }
}

#[cfg(unix)]
#[test]
fn source_namespace_replacement_and_control_namespace_overlap_refuse() {
    let fixture = Fixture::new();
    let snapshot = fixture.snapshot().unwrap();
    let moved = fixture.source.with_file_name("preserved-repo");
    fs::rename(&fixture.source, &moved).unwrap();
    fs::create_dir(&fixture.source).unwrap();
    assert!(fixture.outputs().digest(&snapshot, &fixture.controls).is_err());

    let fixture = Fixture::new();
    std::os::unix::fs::symlink(&fixture.controls, fixture.host.join("execution-control")).unwrap();
    assert!(fixture.digest().unwrap_err().contains("execution controls"));
    assert!(fixture.outputs().digest(&fixture.snapshot().unwrap(), &fixture.host).is_err());
    assert!(
        fixture
            .outputs()
            .digest(&InputSnapshot::from("asserted source"), &fixture.controls)
            .unwrap_err()
            .contains("observed repository")
    );
}

#[cfg(unix)]
#[test]
fn typed_output_namespace_retains_ignored_input_reexecution_refusal() {
    let fixture = Fixture::new();
    let runtime = fixture.source.join("build/runtime-input");
    fs::write(&runtime, b"passes").unwrap();
    let before = fixture.snapshot().unwrap();
    let executions = Cell::new(0);
    let execute = || {
        executions.set(executions.get() + 1);
        let reached = fixture.host.join(SOURCE_ALIAS).join("build/runtime-input");
        if fs::read(reached).unwrap() == b"passes" {
            Ok(())
        } else {
            Err("selected UI test failed on an ignored input".into())
        }
    };
    assert_eq!(
        run(
            ReusePolicy::RecordOnly,
            &fixture.controls,
            fixture.outputs(),
            || fixture.snapshot(),
            execute
        )
        .unwrap(),
        Reuse::Executed
    );
    fs::write(&runtime, b"fails!").unwrap();
    assert_eq!(fixture.snapshot().unwrap(), before, "this remains an incomplete read closure");
    let result = run(
        ReusePolicy::RecordOnly,
        &fixture.controls,
        fixture.outputs(),
        || fixture.snapshot(),
        execute,
    );
    assert!(result.unwrap_err().contains("ignored input"));
    assert_eq!(executions.get(), 2);
    assert!(!fixture.controls.join("success.json").exists());
}

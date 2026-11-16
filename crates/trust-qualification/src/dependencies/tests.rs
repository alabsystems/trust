use std::cell::Cell;
use std::os::unix::fs::symlink;

use super::*;
use crate::tests::{TestGit, receipt_pair_fixture};

fn checked(request: crate::pair::Request) -> ReceiptCheckedPair {
    crate::pair::inspect(&TestGit, request).unwrap().check_receipts(&TestGit).unwrap()
}

fn document(root: &Path, name: &str) -> Value {
    json!({
        "version":1,
        "packages":[{"id":name,"name":name,"source":null,"manifest_path":root.join("Cargo.toml"),
            "targets":[{"name":name,"kind":["lib"]}],"features":{"a":[]},"metadata":{"retained":true}}],
        "workspace_members":[name],
        "resolve":{"root":name,"nodes":[{"id":name,"dependencies":[],"deps":[],"features":[]}]}
    })
}

fn append(document: &mut Value, package: Value) {
    let id = package["id"].as_str().unwrap().to_owned();
    document["packages"].as_array_mut().unwrap().push(package);
    document["resolve"]["nodes"].as_array_mut().unwrap().push(json!({
        "id":id,"dependencies":[],"deps":[],"features":[],
    }));
}

fn capture(bytes: Vec<u8>) -> ResolverCapture {
    ResolverCapture {
        stdout: bytes,
        stderr: b"retained diagnostic".to_vec(),
        outcome: ResolverOutcome::Exit(0),
        cleanup_confirmed: true,
        output_limit_exceeded: false,
        failure: None,
        execution: Some(json!({"fixture":"data-only; no native admission"})),
    }
}

struct Resolver<F> {
    calls: Cell<usize>,
    modify: F,
}
impl<F: FnMut(usize, &ResolverRequest, &mut Value)> DependencyResolver for Resolver<F> {
    fn resolve(&mut self, request: &ResolverRequest) -> Result<ResolverCapture> {
        let index = self.calls.get();
        self.calls.set(index + 1);
        assert_eq!(
            request.arguments(),
            ["metadata", "--locked", "--offline", "--format-version", "1"]
        );
        assert_eq!(request.program.path, request.sdk_root.join("bin/targo"));
        assert!(request.cargo_home.is_absolute());
        let mut value = document(
            &request.cwd,
            match request.subject {
                Subject::Ay => "ay-fixture",
                Subject::TrustVc => "vc-fixture",
            },
        );
        (self.modify)(index, request, &mut value);
        Ok(capture(serde_json::to_vec(&value).unwrap()))
    }
}

/// The lower-level fixture supplies observations only; it never constructs a
/// successful production ProbeAttempt, runs a sealed tool, or authenticates a
/// receipt producer. Public chaining failure is exercised separately below.
fn diagnostic(pair: ReceiptCheckedPair, runner: &mut impl DependencyResolver) -> DependencyAttempt {
    DependencyAttempt::run(
        pair,
        json!({"fixture":"saved compiler consistency only"}),
        true,
        &TestGit,
        runner,
    )
}

#[test]
fn complete_paired_metadata_binds_all_four_requests_and_keeps_execution_pending() {
    let dir = tempfile::tempdir().unwrap();
    let request = receipt_pair_fixture(&dir);
    let mut runner =
        Resolver { calls: Cell::new(0), modify: |_, _: &ResolverRequest, _: &mut Value| {} };
    let attempt = diagnostic(checked(request), &mut runner);
    assert_eq!(runner.calls.get(), 4);
    assert!(attempt.consistent(), "{:?}", attempt.report());
    attempt.check_unchanged(&TestGit).unwrap();
    let report = attempt.report();
    assert_eq!(report["records"].as_array().unwrap().len(), 4);
    assert_eq!(report["package_inputs"].as_array().unwrap().len(), 2);
    assert_eq!(report["manifest_selections"].as_array().unwrap().len(), 2);
    for record in report["records"].as_array().unwrap() {
        assert_eq!(record["package_bindings"].as_object().unwrap().len(), 1);
    }
    assert!(report["claim_scope"].as_str().unwrap().contains("no source/build authentication"));
    assert!(
        report["pending_stages"]
            .as_array()
            .unwrap()
            .iter()
            .any(|v| v == "admitted-supervised-execution")
    );
    assert!(
        report["pending_stages"]
            .as_array()
            .unwrap()
            .iter()
            .any(|v| v == "paired-locked-offline-dependency-resolution")
    );
    assert!(report["compiler_probes"]["fixture"].as_str().unwrap().contains("saved"));
}

#[test]
fn comparison_preserves_complete_package_objects_and_the_entire_resolve_graph() {
    for mutation in 0..3 {
        let dir = tempfile::tempdir().unwrap();
        let request = receipt_pair_fixture(&dir);
        let mut runner = Resolver {
            calls: Cell::new(0),
            modify: move |_, request: &ResolverRequest, value: &mut Value| {
                if request.side == Side::Candidate {
                    match mutation {
                        0 => value["packages"][0]["targets"][0]["kind"] = json!(["bin"]),
                        1 => value["packages"][0]["metadata"]["retained"] = json!(false),
                        2 => value["resolve"]["nodes"][0]["features"] = json!(["different"]),
                        _ => unreachable!(),
                    }
                }
            },
        };
        let attempt = diagnostic(checked(request), &mut runner);
        assert!(!attempt.consistent(), "mutation {mutation}");
        assert!(
            attempt.report()["errors"]
                .as_array()
                .unwrap()
                .iter()
                .any(|e| e.as_str().unwrap().contains("differ"))
        );
    }
}

#[test]
fn duplicate_and_missing_populations_or_inconsistent_edges_refuse() {
    let original = document(Path::new("/frozen"), "fixture");
    for mutation in 0..7 {
        let mut value = original.clone();
        match mutation {
            0 => value["packages"].as_array_mut().unwrap().push(original["packages"][0].clone()),
            1 => value["workspace_members"] = json!(["not-present"]),
            2 => value["resolve"]["nodes"] = json!([]),
            3 => value["resolve"] = Value::Null,
            4 => value["resolve"]["nodes"][0]["dependencies"] = json!(["absent"]),
            5 => {
                value["resolve"]["nodes"][0]["deps"] =
                    json!([{"name":"ghost","pkg":"fixture","dep_kinds":[]}])
            }
            6 => value["resolve"]["nodes"][0]["features"] = json!(["a", "a"]),
            _ => unreachable!(),
        }
        assert!(resolution(&serde_json::to_vec(&value).unwrap()).is_err(), "mutation {mutation}");
    }
}

#[test]
fn package_and_workspace_order_normalize_but_workspace_membership_remains_complete() {
    let mut first = document(Path::new("/frozen"), "first");
    append(
        &mut first,
        json!({"id":"second","name":"second","source":null,"manifest_path":"/frozen/second/Cargo.toml"}),
    );
    first["workspace_members"] = json!(["first", "second"]);
    let mut reordered = first.clone();
    reordered["packages"].as_array_mut().unwrap().reverse();
    reordered["workspace_members"].as_array_mut().unwrap().reverse();
    assert_eq!(
        resolution(&serde_json::to_vec(&first).unwrap()).unwrap(),
        resolution(&serde_json::to_vec(&reordered).unwrap()).unwrap()
    );
    reordered["workspace_members"] = json!(["first"]);
    assert_ne!(
        resolution(&serde_json::to_vec(&first).unwrap()).unwrap(),
        resolution(&serde_json::to_vec(&reordered).unwrap()).unwrap()
    );
}

#[test]
fn ay_substitution_from_other_frozen_path_git_and_registry_refuses() {
    for kind in 0..3 {
        let dir = tempfile::tempdir().unwrap();
        let request = receipt_pair_fixture(&dir);
        let other = request.trust_vc.join("Cargo.toml");
        let mut runner = Resolver {
            calls: Cell::new(0),
            modify: move |_, _: &ResolverRequest, value: &mut Value| {
                value["packages"][0]["name"] = json!("ay-substitute");
                match kind {
                    0 => value["packages"][0]["manifest_path"] = json!(other),
                    1 => {
                        value["packages"][0]["source"] = json!(
                            "git+https://example.invalid/ay#0000000000000000000000000000000000000000"
                        )
                    }
                    2 => value["packages"][0]["source"] = json!("registry+https://example.invalid"),
                    _ => unreachable!(),
                }
            },
        };
        let attempt = diagnostic(checked(request), &mut runner);
        assert!(!attempt.consistent(), "kind {kind}");
        assert!(
            attempt.report()["records"][0]["errors"].to_string().contains("AY source")
                || attempt.report()["records"][0]["errors"].to_string().contains("frozen AY")
        );
    }
}

#[test]
fn unbound_external_and_ignored_path_packages_refuse() {
    for ignored in [false, true] {
        let dir = tempfile::tempdir().unwrap();
        let request = receipt_pair_fixture(&dir);
        let package =
            if ignored { request.ay.join("ignored/package") } else { dir.path().join("external") };
        fs::create_dir_all(&package).unwrap();
        fs::write(package.join("Cargo.toml"), "[package]\nname='unbound'\nversion='0.1.0'\n")
            .unwrap();
        let mut runner = Resolver {
            calls: Cell::new(0),
            modify: move |_, _: &ResolverRequest, value: &mut Value| {
                value["packages"][0]["name"] = json!("unbound");
                value["packages"][0]["manifest_path"] = json!(package.join("Cargo.toml"));
            },
        };
        let attempt = diagnostic(checked(request), &mut runner);
        assert!(!attempt.consistent());
        let errors = attempt.report()["records"][0]["errors"].to_string();
        assert!(
            errors.contains(if ignored {
                "unbound path-package manifest"
            } else {
                "unfrozen path dependency"
            }),
            "{errors}"
        );
    }
}

#[test]
fn newly_ignored_path_inputs_refuse_between_resolver_outcomes() {
    let dir = tempfile::tempdir().unwrap();
    let request = receipt_pair_fixture(&dir);
    let ignored = request.ay.join("ignored/new.rs");
    let mut runner = Resolver {
        calls: Cell::new(0),
        modify: move |index, _: &ResolverRequest, _: &mut Value| {
            if index == 1 {
                fs::create_dir_all(ignored.parent().unwrap()).unwrap();
                fs::write(&ignored, "ignored new input").unwrap();
            }
        },
    };
    let attempt = diagnostic(checked(request), &mut runner);
    assert!(!attempt.consistent());
    assert_eq!(runner.calls.get(), 2);
    assert!(attempt.report()["errors"].to_string().contains("unbound ignored path-package input"));
}

fn registry(root: &Path) -> Value {
    fs::create_dir_all(root).unwrap();
    fs::write(root.join("Cargo.toml"), "[package]\nname='helper'\nversion='0.1.0'\n").unwrap();
    fs::write(root.join("ignored-input"), "original bytes").unwrap();
    json!({"id":"helper-registry","name":"helper","source":"registry+https://example.invalid/index",
        "manifest_path":root.join("Cargo.toml")})
}

#[test]
fn registry_content_and_manifest_selection_are_rebound_without_git_exclusions() {
    let dir = tempfile::tempdir().unwrap();
    let request = receipt_pair_fixture(&dir);
    let root = dir.path().join("registry");
    let package = registry(&root);
    let mut runner = Resolver {
        calls: Cell::new(0),
        modify: move |_, _: &ResolverRequest, value: &mut Value| {
            append(value, package.clone());
        },
    };
    let attempt = diagnostic(checked(request), &mut runner);
    assert!(attempt.consistent(), "{:?}", attempt.report());
    fs::write(root.join("ignored-input"), "changed ignored bytes").unwrap();
    assert!(attempt.check_unchanged(&TestGit).unwrap_err().0.contains("dependency source changed"));
}

fn git_dependency(root: &Path) -> Value {
    let package = root.join("crates/helper");
    fs::create_dir_all(&package).unwrap();
    fs::write(root.join("Cargo.toml"), "[workspace]\nmembers=['crates/helper']\n").unwrap();
    fs::write(package.join("Cargo.toml"), "[package]\nname='helper'\nversion='0.1.0'\n").unwrap();
    fs::write(root.join("shared.rs"), "pub fn shared() {}\n").unwrap();
    TestGit::run(root, &["init", "-q"]);
    TestGit::run(root, &["add", "."]);
    TestGit::run(root, &["commit", "-qm", "shared dependency closure"]);
    let revision = String::from_utf8(TestGit.probe(root, &["rev-parse", "HEAD"]).unwrap())
        .unwrap()
        .trim()
        .to_owned();
    fs::write(root.join(".cargo-ok"), "").unwrap();
    json!({"id":"helper-git","name":"helper","source":format!("git+file://{}#{revision}",root.display()),
        "manifest_path":package.join("Cargo.toml")})
}

fn two_package_git_workspace(root: &Path) -> [Value; 2] {
    let mut first = git_dependency(root);
    fs::create_dir_all(root.join("crates/peer")).unwrap();
    fs::write(root.join("crates/peer/Cargo.toml"), "[package]\nname='peer'\nversion='0.1.0'\n")
        .unwrap();
    fs::write(root.join("Cargo.toml"), "[workspace]\nmembers=['crates/helper','crates/peer']\n")
        .unwrap();
    TestGit::run(root, &["add", "Cargo.toml", "crates/peer"]);
    TestGit::run(root, &["commit", "-qm", "two packages in the original workspace"]);
    let revision = String::from_utf8(TestGit.probe(root, &["rev-parse", "HEAD"]).unwrap())
        .unwrap()
        .trim()
        .to_owned();
    first["source"] = json!(format!("git+file://{}#{revision}", root.display()));
    let second = json!({"id":"peer-git","name":"peer","source":first["source"],
        "manifest_path":root.join("crates/peer/Cargo.toml")});
    [first, second]
}

struct CountingGit {
    root: PathBuf,
    inventories: Cell<usize>,
    validations: Cell<usize>,
    package_top_levels: Cell<usize>,
}
impl CountingGit {
    fn new(root: &Path) -> Self {
        Self {
            root: root.canonicalize().unwrap(),
            inventories: Cell::new(0),
            validations: Cell::new(0),
            package_top_levels: Cell::new(0),
        }
    }
}
impl Git for CountingGit {
    fn probe(&self, root: &Path, args: &[&str]) -> Result<Vec<u8>> {
        if root == self.root && args == ["ls-tree", "-r", "-z", "HEAD"] {
            self.inventories.set(self.inventories.get() + 1);
        }
        if [self.root.join("crates/helper"), self.root.join("crates/peer")]
            .contains(&root.to_path_buf())
            && args == ["rev-parse", "--show-toplevel"]
        {
            self.package_top_levels.set(self.package_top_levels.get() + 1);
        }
        TestGit.probe(root, args)
    }
    fn validate_repository(&self, root: &Path) -> Result<()> {
        if root == self.root {
            self.validations.set(self.validations.get() + 1);
        }
        TestGit.validate_repository(root)
    }
}

#[test]
fn shared_git_workspace_gets_one_initial_full_source_bind_for_both_packages() {
    let dir = tempfile::tempdir().unwrap();
    let request = receipt_pair_fixture(&dir);
    let pair = checked(request);
    let root = dir.path().join("git-workspace");
    let packages = two_package_git_workspace(&root);
    let git = CountingGit::new(&root);
    let mut bindings = Bindings::default();
    for _ in 0..4 {
        for package in &packages {
            let package = Json::parse(&serde_json::to_vec(package).unwrap()).unwrap();
            bindings.bind_package(&git, pair.snapshot(), &package).unwrap();
        }
    }
    assert_eq!(
        git.inventories.get(),
        1,
        "same workspace was fully bound again for another package"
    );
    assert_eq!(git.validations.get(), 1, "initial source identity was reconstructed");
    assert_eq!(
        git.package_top_levels.get(),
        8,
        "every original package must still resolve its actual Git root"
    );
    assert_eq!(bindings.dependencies.len(), 1);
    assert_eq!(bindings.packages.len(), 2, "four observations must share two manifest bindings");
    assert!(bindings.check(&git).is_empty());
    assert_eq!(git.inventories.get(), 2, "final handoff must rebind the complete Git source");
}

#[test]
fn shared_git_workspace_reuses_initial_binding_but_keeps_every_outcome_recheck() {
    let dir = tempfile::tempdir().unwrap();
    let request = receipt_pair_fixture(&dir);
    let pair = checked(request);
    let root = dir.path().join("git-workspace");
    let packages = two_package_git_workspace(&root);
    let git = CountingGit::new(&root);
    let mut runner = Resolver {
        calls: Cell::new(0),
        modify: move |_, _: &ResolverRequest, value: &mut Value| {
            for package in &packages {
                append(value, package.clone());
            }
        },
    };
    let attempt =
        DependencyAttempt::run(pair, json!({"fixture":"data only"}), true, &git, &mut runner);
    assert!(attempt.consistent(), "{:?}", attempt.report());
    // One initial source bind, four post-outcome rechecks, three later
    // pre-outcome checks, and the final handoff check. Package count adds none.
    assert_eq!(git.inventories.get(), 9);
    assert_eq!(git.package_top_levels.get(), 8);
    assert_eq!(attempt.bindings.dependencies.len(), 1);
    assert_eq!(attempt.bindings.packages.len(), 4);
    let report = attempt.report();
    for record in report["records"].as_array().unwrap() {
        assert_eq!(record["package_bindings"].as_object().unwrap().len(), 3);
        let identity: Value =
            serde_json::from_str(record["identity_json"].as_str().unwrap()).unwrap();
        assert_eq!(identity["packages"].as_array().unwrap().len(), 3);
    }
    attempt.check_unchanged(&git).unwrap();
    assert_eq!(git.inventories.get(), 10, "later native consumption must rebind again");
}

#[test]
fn shared_git_workspace_drift_does_not_refresh_the_original_cached_identity() {
    let dir = tempfile::tempdir().unwrap();
    let request = receipt_pair_fixture(&dir);
    let pair = checked(request);
    let root = dir.path().join("git-workspace");
    let packages = two_package_git_workspace(&root);
    let git = CountingGit::new(&root);
    let mut bindings = Bindings::default();
    bindings
        .bind_package(
            &git,
            pair.snapshot(),
            &Json::parse(&serde_json::to_vec(&packages[0]).unwrap()).unwrap(),
        )
        .unwrap();
    let original = bindings.dependencies[&git.root].content.clone();
    fs::write(root.join("shared.rs"), "shared input changed after the original binding").unwrap();
    bindings
        .bind_package(
            &git,
            pair.snapshot(),
            &Json::parse(&serde_json::to_vec(&packages[1]).unwrap()).unwrap(),
        )
        .unwrap();
    assert_eq!(git.inventories.get(), 1);
    assert_eq!(bindings.dependencies[&git.root].content, original);
    let errors = bindings.check(&git).join("; ");
    assert!(errors.contains("dependency source changed"), "{errors}");
    assert!(errors.contains("Git dependency"), "{errors}");
    assert_eq!(
        git.validations.get(),
        2,
        "failed content checks must not skip independent Git rebinding"
    );
}

#[test]
fn shared_git_root_refuses_revision_and_source_kind_conflicts() {
    for conflict in 0..3 {
        let dir = tempfile::tempdir().unwrap();
        let request = receipt_pair_fixture(&dir);
        let pair = checked(request);
        let root = dir.path().join("git-workspace");
        let packages = two_package_git_workspace(&root);
        let git = CountingGit::new(&root);
        let registry = json!({"id":"workspace-registry","name":"workspace",
            "source":"registry+https://example.invalid/index","manifest_path":root.join("Cargo.toml")});
        let mut wrong_revision = packages[1].clone();
        wrong_revision["source"] =
            json!(format!("git+file://{}#{}", root.display(), "a".repeat(40)));
        let (first, second, expected) = match conflict {
            0 => (packages[0].clone(), wrong_revision, "resolved revision"),
            1 => (packages[0].clone(), registry.clone(), "source kind"),
            2 => (registry, packages[1].clone(), "source kind"),
            _ => unreachable!(),
        };
        let mut bindings = Bindings::default();
        bindings
            .bind_package(
                &git,
                pair.snapshot(),
                &Json::parse(&serde_json::to_vec(&first).unwrap()).unwrap(),
            )
            .unwrap();
        let original = bindings.dependencies[&git.root].content.clone();
        let error = bindings
            .bind_package(
                &git,
                pair.snapshot(),
                &Json::parse(&serde_json::to_vec(&second).unwrap()).unwrap(),
            )
            .unwrap_err();
        assert!(error.0.contains(expected), "{error}");
        assert_eq!(bindings.dependencies[&git.root].content, original);
        assert_eq!(bindings.dependencies.len(), 1);
        assert!(
            bindings.check(&git).is_empty(),
            "a conflicting record must not replace the original owner"
        );
    }
}

#[test]
fn repeated_manifest_aliases_share_one_binding_without_accepting_source_or_selection_changes() {
    let dir = tempfile::tempdir().unwrap();
    let request = receipt_pair_fixture(&dir);
    let pair = checked(request);
    let root = dir.path().join("registry");
    let package = registry(&root);
    let other = dir.path().join("other-registry");
    registry(&other);
    let alias = dir.path().join("manifest-alias");
    symlink(root.join("Cargo.toml"), &alias).unwrap();
    let mut alias_package = package.clone();
    alias_package["manifest_path"] = json!(alias);
    let mut bindings = Bindings::default();
    for package in [&package, &alias_package, &package, &alias_package] {
        bindings
            .bind_package(
                &TestGit,
                pair.snapshot(),
                &Json::parse(&serde_json::to_vec(package).unwrap()).unwrap(),
            )
            .unwrap();
    }
    assert_eq!(bindings.packages.len(), 1);
    assert_eq!(bindings.selections.len(), 2);
    let original = &bindings.packages[&root.join("Cargo.toml").canonicalize().unwrap()];
    assert_eq!(original.ids.len(), 1);
    assert_eq!(original.selections.len(), 2);
    let mut different_source = alias_package.clone();
    different_source["source"] = json!("registry+https://different.invalid/index");
    let error = bindings
        .bind_package(
            &TestGit,
            pair.snapshot(),
            &Json::parse(&serde_json::to_vec(&different_source).unwrap()).unwrap(),
        )
        .unwrap_err();
    assert!(error.0.contains("package source conflicts"), "{error}");
    assert!(bindings.check(&TestGit).is_empty());
    fs::remove_file(&alias).unwrap();
    symlink(other.join("Cargo.toml"), &alias).unwrap();
    let error = bindings
        .bind_package(
            &TestGit,
            pair.snapshot(),
            &Json::parse(&serde_json::to_vec(&alias_package).unwrap()).unwrap(),
        )
        .unwrap_err();
    assert!(error.0.contains("manifest selection changed"), "{error}");
    assert_eq!(bindings.packages.len(), 1);
    assert!(bindings.check(&TestGit).join("; ").contains("manifest selection changed"));
}

#[test]
fn git_dependency_binds_enclosing_workspace_shared_inputs_and_empty_checkout_marker() {
    for mutate_marker in [false, true] {
        let dir = tempfile::tempdir().unwrap();
        let request = receipt_pair_fixture(&dir);
        let root = dir.path().join("git-dependency");
        let package = git_dependency(&root);
        let mut runner = Resolver {
            calls: Cell::new(0),
            modify: move |_, _: &ResolverRequest, value: &mut Value| {
                append(value, package.clone());
            },
        };
        let attempt = diagnostic(checked(request), &mut runner);
        assert!(attempt.consistent(), "{:?}", attempt.report());
        assert_eq!(attempt.bindings.dependencies.len(), 1);
        assert!(attempt.bindings.dependencies.contains_key(&root.canonicalize().unwrap()));
        if mutate_marker {
            fs::remove_file(root.join(".cargo-ok")).unwrap();
        } else {
            fs::write(root.join("shared.rs"), "changed shared source").unwrap();
        }
        let error = attempt.check_unchanged(&TestGit).unwrap_err().0;
        assert!(error.contains("dependency source changed"), "{error}");
        assert!(error.contains("Git dependency"), "{error}");
    }
}

#[test]
fn mismatched_git_revision_and_nonempty_checkout_marker_refuse() {
    for wrong_revision in [false, true] {
        let dir = tempfile::tempdir().unwrap();
        let request = receipt_pair_fixture(&dir);
        let root = dir.path().join("git-dependency");
        let mut package = git_dependency(&root);
        if wrong_revision {
            package["source"] = json!(format!("git+file://{}#{}", root.display(), "a".repeat(40)));
        } else {
            fs::write(root.join(".cargo-ok"), "not empty").unwrap();
        }
        let mut runner = Resolver {
            calls: Cell::new(0),
            modify: move |_, _: &ResolverRequest, value: &mut Value| {
                append(value, package.clone());
            },
        };
        let attempt = diagnostic(checked(request), &mut runner);
        assert!(!attempt.consistent());
        assert!(attempt.report()["records"][0]["errors"].to_string().contains(if wrong_revision {
            "resolved revision"
        } else {
            "checkout marker"
        }));
    }
}

#[test]
fn manifest_alias_retargeting_cannot_reuse_a_bound_package_observation() {
    let dir = tempfile::tempdir().unwrap();
    let request = receipt_pair_fixture(&dir);
    let alias = dir.path().join("manifest-alias");
    symlink(request.ay.join("Cargo.toml"), &alias).unwrap();
    let selected = alias.clone();
    let replacement = request.trust_vc.join("Cargo.toml");
    let mut runner = Resolver {
        calls: Cell::new(0),
        modify: move |_, _: &ResolverRequest, value: &mut Value| {
            value["packages"][0]["name"] = json!("non-ay");
            value["packages"][0]["manifest_path"] = json!(selected);
        },
    };
    let attempt = diagnostic(checked(request), &mut runner);
    assert!(attempt.consistent(), "{:?}", attempt.report());
    fs::remove_file(&alias).unwrap();
    symlink(replacement, &alias).unwrap();
    assert!(
        attempt.check_unchanged(&TestGit).unwrap_err().0.contains("manifest selection changed")
    );
}

#[test]
fn strict_json_rejects_nested_and_escaped_duplicates_and_noninteger_versions() {
    for bytes in [
        br#"{"version":1,"version":1}"#.as_slice(),
        br#"{"unknown":{"a":1,"\u0061":2}}"#.as_slice(),
        br#"{"unknown":{"array":[{"a":1,"a":2}]}}"#.as_slice(),
        br#"{"version":1.0}"#.as_slice(),
        br#"{"version":true}"#.as_slice(),
        br#"{"version":18446744073709551616}"#.as_slice(),
        br#"{"version":1}{}"#.as_slice(),
    ] {
        assert!(resolution(bytes).is_err(), "{:?}", String::from_utf8_lossy(bytes));
    }
    let original = document(Path::new("/frozen"), "fixture");
    let text = serde_json::to_string(&original).unwrap();
    let first = text.replacen("\"retained\":true", "\"retained\":18446744073709551616", 1);
    let second = text.replacen("\"retained\":true", "\"retained\":18446744073709551617", 1);
    assert_ne!(resolution(first.as_bytes()).unwrap(), resolution(second.as_bytes()).unwrap());
    let private = text.replacen(
        "\"retained\":true",
        "\"retained\":{\"$serde_json::private::Number\":\"2\"}",
        1,
    );
    assert_ne!(resolution(private.as_bytes()).unwrap(), resolution(text.as_bytes()).unwrap());
}

#[test]
fn preflight_drift_never_calls_resolver_and_preserves_original_inputs() {
    let dir = tempfile::tempdir().unwrap();
    let request = receipt_pair_fixture(&dir);
    let pair = checked(request.clone());
    let original = serde_json::to_value(pair.snapshot()).unwrap();
    fs::write(request.ay.join("Cargo.lock"), "changed source").unwrap();
    let mut runner = Resolver {
        calls: Cell::new(0),
        modify: |_, _: &ResolverRequest, _: &mut Value| panic!("must not execute"),
    };
    let attempt = diagnostic(pair, &mut runner);
    assert_eq!(runner.calls.get(), 0);
    assert!(!attempt.consistent());
    assert_eq!(attempt.report()["receipts"]["inputs"], original);
}

#[test]
fn failed_public_probe_chain_preserves_original_probe_evidence_without_resolver_calls() {
    use trust_resource_controller::{MetadataBatch, MetadataBatchReport};

    use crate::probes::MetadataRunner;
    struct RefusedProbe {
        image: FileIdentity,
    }
    impl MetadataRunner for RefusedProbe {
        fn service_image(&self) -> Result<FileIdentity> {
            Ok(self.image.clone())
        }
        fn collect(&mut self, _: &MetadataBatch) -> Result<MetadataBatchReport> {
            Err(refusal("original native probe failure"))
        }
        fn execution_observation(&self) -> Option<Value> {
            Some(json!({"native_failure":"retained"}))
        }
    }
    let dir = tempfile::tempdir().unwrap();
    let request = receipt_pair_fixture(&dir);
    let mut probe =
        RefusedProbe { image: file_identity(&request.control.join("bin/targo")).unwrap() };
    let probes = checked(request).probe_compilers(&TestGit, &mut probe);
    let original = probes.report();
    let mut runner = Resolver {
        calls: Cell::new(0),
        modify: |_, _: &ResolverRequest, _: &mut Value| panic!("must not execute"),
    };
    let attempt = probes.resolve_dependencies(&TestGit, &mut runner);
    assert_eq!(runner.calls.get(), 0);
    assert!(!attempt.consistent());
    assert_eq!(attempt.report()["compiler_probes"], original);
    assert!(
        attempt.report()["errors"].to_string().contains("compiler identity probes did not succeed")
    );
    assert!(
        attempt.report()["pending_stages"]
            .as_array()
            .unwrap()
            .iter()
            .any(|stage| stage == "actual-compiler-identity-probes")
    );
}

#[test]
fn partial_failure_retains_raw_bytes_and_rebinds_both_pair_and_discovered_dependencies() {
    let dir = tempfile::tempdir().unwrap();
    let request = receipt_pair_fixture(&dir);
    let root = dir.path().join("registry");
    let package = registry(&root);
    struct Fail {
        calls: usize,
        package: Value,
        dependency: PathBuf,
        source: PathBuf,
    }
    impl DependencyResolver for Fail {
        fn resolve(&mut self, request: &ResolverRequest) -> Result<ResolverCapture> {
            self.calls += 1;
            if self.calls == 1 {
                let mut value = document(&request.cwd, "ay-fixture");
                append(&mut value, self.package.clone());
                Ok(capture(serde_json::to_vec(&value).unwrap()))
            } else {
                fs::write(&self.dependency, "mutated dependency").unwrap();
                fs::write(&self.source, "mutated source").unwrap();
                let mut failed = capture(b"partial stdout retained".to_vec());
                failed.outcome = ResolverOutcome::Unknown;
                failed.cleanup_confirmed = false;
                failed.failure = Some("native transport lost".into());
                Ok(failed)
            }
        }
    }
    let pair = checked(request.clone());
    let mut runner = Fail {
        calls: 0,
        package,
        dependency: root.join("ignored-input"),
        source: request.ay.join("Cargo.lock"),
    };
    let attempt = diagnostic(pair, &mut runner);
    assert_eq!(runner.calls, 2);
    assert!(!attempt.consistent());
    let report = attempt.report();
    assert_eq!(report["records"][1]["capture"]["stdout_hex"], hex(b"partial stdout retained"));
    assert_eq!(report["records"][1]["capture"]["failure"], "native transport lost");
    let errors = report["errors"].to_string();
    assert!(errors.contains("dependency source changed"), "{errors}");
    assert!(errors.contains("original paired inputs"), "{errors}");
}

#[test]
fn malformed_metadata_stops_further_phases_and_retains_the_exact_capture() {
    let dir = tempfile::tempdir().unwrap();
    let request = receipt_pair_fixture(&dir);
    struct Malformed {
        calls: usize,
    }
    impl DependencyResolver for Malformed {
        fn resolve(&mut self, _: &ResolverRequest) -> Result<ResolverCapture> {
            self.calls += 1;
            Ok(capture(b"{\"packages\":".to_vec()))
        }
    }
    let mut runner = Malformed { calls: 0 };
    let attempt = diagnostic(checked(request), &mut runner);
    assert!(!attempt.consistent());
    assert_eq!(runner.calls, 1);
    let report = attempt.report();
    assert_eq!(report["records"][0]["capture"]["stdout_hex"], hex(b"{\"packages\":"));
    assert_eq!(report["records"][1]["status"], "not_attempted");
}

#[test]
fn admission_failure_retains_native_attempt_observation_and_finite_capture_refusals() {
    let dir = tempfile::tempdir().unwrap();
    let request = receipt_pair_fixture(&dir);
    struct Refused;
    impl DependencyResolver for Refused {
        fn resolve(&mut self, _: &ResolverRequest) -> Result<ResolverCapture> {
            Err(refusal("actual native preparation refused"))
        }
        fn execution_observation(&self) -> Option<Value> {
            Some(json!({"original_attempt":"retained","cause":"native preparation refused"}))
        }
    }
    let attempt = diagnostic(checked(request), &mut Refused);
    assert!(!attempt.consistent());
    assert_eq!(attempt.report()["records"][0]["status"], "runner_refused");
    assert_eq!(attempt.report()["records"][0]["execution"]["original_attempt"], "retained");
    assert_eq!(attempt.report()["records"][1]["status"], "not_attempted");
    let dir = tempfile::tempdir().unwrap();
    let request = receipt_pair_fixture(&dir);
    struct Oversized;
    impl DependencyResolver for Oversized {
        fn resolve(&mut self, _: &ResolverRequest) -> Result<ResolverCapture> {
            let mut result = capture(Vec::new());
            result.stderr = vec![b'x'; MAX_STDERR_BYTES + 1];
            Ok(result)
        }
    }
    let attempt = diagnostic(checked(request), &mut Oversized);
    assert!(!attempt.consistent());
    assert!(attempt.report()["records"][0]["errors"].to_string().contains("finite output bounds"));
}

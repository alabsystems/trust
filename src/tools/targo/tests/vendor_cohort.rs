//! Actual native vendor cohort planning and source checking.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use serde_json::Value;

#[expect(
    clippy::disallowed_methods,
    reason = "the isolated fixture selects the actual newly built Targo before project configuration"
)]
fn command(world: &Path) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_targo"));
    command
        .current_dir(world.join("project"))
        .env_clear()
        .env("HOME", world)
        .env("CARGO_HOME", world.join("home"))
        .env("CARGO_TARGET_DIR", world.join("target"))
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env(
            "RUSTC",
            std::env::var_os("RUSTC").expect("original compiler"),
        )
        .env(
            "RUSTDOC",
            std::env::var_os("RUSTDOC").expect("matching original rustdoc"),
        );
    command
}

fn run(world: &Path, label: &str, args: &[&str]) -> Output {
    let mut process = command(world);
    process.args(args);
    let evidence = world.join(label);
    fs::create_dir(&evidence).unwrap();
    fs::write(
        evidence.join("command.json"),
        serde_json::to_vec_pretty(&serde_json::json!({
            "program":process.get_program(), "args":process.get_args().collect::<Vec<_>>(),
            "cwd":process.get_current_dir(), "environment":process.get_envs().collect::<Vec<_>>()
        }))
        .unwrap(),
    )
    .unwrap();
    let output = process.output().unwrap();
    fs::write(evidence.join("stdout"), &output.stdout).unwrap();
    fs::write(evidence.join("stderr"), &output.stderr).unwrap();
    fs::write(evidence.join("status"), output.status.to_string()).unwrap();
    output
}

fn success(world: &Path, output: &Output) {
    assert!(
        output.status.success(),
        "world={} status={}\n{}",
        world.display(),
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
}

fn put(project: &Path, relative: &str, contents: &str) {
    let file = project.join(relative);
    fs::create_dir_all(file.parent().unwrap()).unwrap();
    fs::write(file, contents).unwrap();
}

fn commit(project: &Path) {
    let repo = git2::Repository::open(project).unwrap();
    let mut index = repo.index().unwrap();
    index.update_all(["*"], None).unwrap();
    index
        .add_all(["*"], git2::IndexAddOption::DEFAULT, None)
        .unwrap();
    index.write().unwrap();
    let tree = repo.find_tree(index.write_tree().unwrap()).unwrap();
    let signature = git2::Signature::now("Cohort fixture", "cohort@example.invalid").unwrap();
    let parent = repo.head().ok().map(|head| head.peel_to_commit().unwrap());
    let parents = parent.iter().collect::<Vec<_>>();
    repo.commit(
        Some("HEAD"),
        &signature,
        &signature,
        "Native cohort source",
        &tree,
        &parents,
    )
    .unwrap();
}

fn fixture() -> PathBuf {
    let base = Path::new(env!("CARGO_MANIFEST_DIR")).join(".ubd/native-vendor-cohort.noindex");
    fs::create_dir_all(&base).unwrap();
    let world = tempfile::Builder::new()
        .prefix("cohort-")
        .tempdir_in(base)
        .unwrap()
        .keep();
    let project = world.join("project");
    fs::create_dir(&project).unwrap();
    git2::Repository::init(&project).unwrap();
    put(
        &project,
        "Cargo.toml",
        r#"
[workspace]
resolver = "2"
members = ["parts/*"]

[workspace.package]
version = "0.1.0"
edition = "2024"

[patch.crates-io]
jobserver = { path = "parts/jobserver" }
"#,
    );
    put(
        &project,
        "parts/app/Cargo.toml",
        r#"
[package]
name = "cohort-root"
version.workspace = true
edition.workspace = true

[features]
extra = ["dep:optional"]

[dependencies]
optional = { package = "cohort-optional", path = "../optional", optional = true }
jobserver = "0.1.35"

[target.'cfg(windows)'.dependencies]
target = { package = "cohort-target", path = "../target" }

[dev-dependencies]
dev = { package = "cohort-dev", path = "../dev" }

[build-dependencies]
build = { package = "cohort-build", path = "../build" }

[[example]]
name = "declared"
path = "examples/declared.rs"
"#,
    );
    put(
        &project,
        "parts/app/src/lib.rs",
        "pub fn value() -> u32 { 7 }\n",
    );
    put(&project, "parts/app/examples/declared.rs", "fn main() {}\n");
    for (directory, name, version) in [
        ("optional", "cohort-optional", "0.1.0"),
        ("target", "cohort-target", "0.1.0"),
        ("dev", "cohort-dev", "0.1.0"),
        ("build", "cohort-build", "0.1.0"),
        ("jobserver", "jobserver", "0.1.35"),
        ("unrelated", "cohort-unrelated", "0.1.0"),
    ] {
        put(
            &project,
            &format!("parts/{directory}/Cargo.toml"),
            &format!("[package]\nname = \"{name}\"\nversion = \"{version}\"\nedition = \"2024\"\n"),
        );
        put(
            &project,
            &format!("parts/{directory}/src/lib.rs"),
            "pub fn value() -> u32 { 1 }\n",
        );
    }
    put(
        &project,
        "parts/optional/data/fixture.txt",
        "complete tracked component data\n",
    );
    let locked = run(&world, "lock", &["generate-lockfile", "--offline"]);
    success(&world, &locked);
    commit(&project);
    world
}

fn plan(world: &Path, label: &str) -> Output {
    run(
        world,
        label,
        &[
            "vendor",
            "--cohort-plan",
            "-p",
            "cohort-root",
            "--locked",
            "--offline",
        ],
    )
}

fn saved_record(world: &Path) -> PathBuf {
    let output = plan(world, "plan");
    success(world, &output);
    let record = world.join("cohort.json");
    fs::write(&record, output.stdout).unwrap();
    record
}

#[test]
fn vendor_cohort_captures_optional_target_dev_paths_and_repeats_identically() {
    let world = fixture();
    let first = plan(&world, "plan-first");
    success(&world, &first);
    let second = plan(&world, "plan-second");
    success(&world, &second);
    assert_eq!(first.stdout, second.stdout);
    let value: Value = serde_json::from_slice(&first.stdout).unwrap();
    let packages = value["workspaces"][0]["packages"].as_array().unwrap();
    let names = packages
        .iter()
        .map(|p| p["identity"]["name"].as_str().unwrap())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        names,
        BTreeSet::from([
            "cohort-root",
            "cohort-optional",
            "cohort-target",
            "cohort-dev",
            "cohort-build",
            "jobserver"
        ])
    );
    let root = packages
        .iter()
        .find(|p| p["identity"]["name"] == "cohort-root")
        .unwrap();
    let edges = root["dependencies"].as_array().unwrap();
    assert!(edges.iter().any(|e| e["optional"] == true));
    assert!(edges.iter().any(|e| e["target"] == "cfg(windows)"));
    assert!(edges.iter().any(|e| e["kind"] == "dev-dependencies"));
    assert!(edges.iter().any(|e| e["kind"] == "build-dependencies"));
    let patched = edges.iter().find(|e| e["name"] == "jobserver").unwrap();
    assert!(
        patched["declared_source"]
            .as_str()
            .unwrap()
            .starts_with("registry+")
    );
    assert_eq!(patched["resolved"]["source"], "path:parts/jobserver");
    assert!(
        root["normalized_manifest"]
            .as_str()
            .unwrap()
            .contains("version = \"0.1.0\"")
    );
    assert!(
        value["files"]
            .as_array()
            .unwrap()
            .iter()
            .any(|f| f["path"] == "parts/optional/data/fixture.txt")
    );
    let record = world.join("cohort.json");
    fs::write(&record, &first.stdout).unwrap();
    let checked = run(
        &world,
        "check",
        &[
            "vendor",
            "--cohort-check",
            record.to_str().unwrap(),
            "--locked",
            "--offline",
        ],
    );
    success(&world, &checked);
    assert!(!world.join("project/vendor").exists());
}

#[test]
fn vendor_cohort_check_refuses_a_stale_committed_component() {
    let world = fixture();
    let record = saved_record(&world);
    put(
        &world.join("project"),
        "parts/optional/data/fixture.txt",
        "new committed source\n",
    );
    commit(&world.join("project"));
    let checked = run(
        &world,
        "stale-check",
        &[
            "vendor",
            "--cohort-check",
            record.to_str().unwrap(),
            "--locked",
            "--offline",
        ],
    );
    assert!(!checked.status.success(), "world={}", world.display());
    assert!(String::from_utf8_lossy(&checked.stderr).contains("source cohort does not match"));
}

#[test]
fn vendor_cohort_check_refuses_a_missing_component_input() {
    let world = fixture();
    let record = saved_record(&world);
    fs::remove_file(world.join("project/parts/optional/data/fixture.txt")).unwrap();
    let checked = run(
        &world,
        "missing-check",
        &[
            "vendor",
            "--cohort-check",
            record.to_str().unwrap(),
            "--locked",
            "--offline",
        ],
    );
    assert!(!checked.status.success(), "world={}", world.display());
    assert!(String::from_utf8_lossy(&checked.stderr).contains("source cohort file is absent"));
}

#[test]
fn vendor_cohort_plan_refuses_an_omitted_declared_target() {
    let world = fixture();
    fs::remove_file(world.join("project/parts/app/examples/declared.rs")).unwrap();
    commit(&world.join("project"));
    let output = plan(&world, "omitted-target-plan");
    assert!(!output.status.success(), "world={}", world.display());
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("declared source cohort target is absent")
    );
}

fn foreign_fixture() -> PathBuf {
    let world = fixture();
    let project = world.join("project");
    let root = fs::read_to_string(project.join("Cargo.toml")).unwrap();
    put(
        &project,
        "Cargo.toml",
        &root.replace(
            "members = [\"parts/*\"]",
            "members = [\"parts/*\"]\nexclude = [\"foreign\"]",
        ),
    );
    let app = fs::read_to_string(project.join("parts/app/Cargo.toml")).unwrap();
    put(
        &project,
        "parts/app/Cargo.toml",
        &format!(
            "{app}\n[dependencies.foreign]\npackage = 'foreign-leaf'\npath = '../../foreign/leaf'\n"
        ),
    );
    put(
        &project,
        "foreign/Cargo.toml",
        "[workspace]\nresolver = '2'\nmembers = ['leaf', 'optional', 'dev', 'jobserver']\n[workspace.package]\nedition = '2024'\n[patch.crates-io]\njobserver = { path = 'jobserver' }\n",
    );
    put(
        &project,
        "foreign/leaf/Cargo.toml",
        "[package]\nname = 'foreign-leaf'\nversion = '0.1.0'\nedition.workspace = true\n[features]\nextra = ['dep:optional']\n[dependencies]\noptional = { package = 'foreign-optional', path = '../optional', optional = true }\njobserver = '0.1.35'\n[dev-dependencies]\ndev = { package = 'foreign-dev', path = '../dev' }\n",
    );
    put(
        &project,
        "foreign/leaf/src/lib.rs",
        "pub fn value() -> u32 { 2 }\n",
    );
    for (directory, name, version) in [
        ("optional", "foreign-optional", "0.1.0"),
        ("dev", "foreign-dev", "0.1.0"),
        ("jobserver", "jobserver", "0.1.35"),
    ] {
        put(
            &project,
            &format!("foreign/{directory}/Cargo.toml"),
            &format!("[package]\nname = '{name}'\nversion = '{version}'\nedition = '2024'\n"),
        );
        put(
            &project,
            &format!("foreign/{directory}/src/lib.rs"),
            "pub fn value() -> u32 { 2 }\n",
        );
    }
    let lock = run(
        &world,
        "foreign-lock",
        &[
            "generate-lockfile",
            "--manifest-path",
            "foreign/Cargo.toml",
            "--offline",
        ],
    );
    success(&world, &lock);
    let lock = run(&world, "root-relock", &["generate-lockfile", "--offline"]);
    success(&world, &lock);
    commit(&project);
    world
}

#[test]
fn vendor_cohort_resolves_excluded_owning_workspaces_without_flattening_contexts() {
    let world = foreign_fixture();
    let first = plan(&world, "foreign-plan-first");
    success(&world, &first);
    let second = plan(&world, "foreign-plan-second");
    success(&world, &second);
    assert_eq!(first.stdout, second.stdout);
    let value: Value = serde_json::from_slice(&first.stdout).unwrap();
    let frames = value["workspaces"].as_array().unwrap();
    assert_eq!(frames.len(), 2);
    let foreign = frames
        .iter()
        .find(|frame| frame["manifest"] == "foreign/Cargo.toml")
        .unwrap();
    let names = foreign["packages"]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| p["identity"]["name"].as_str().unwrap())
        .collect::<BTreeSet<_>>();
    assert!(names.is_superset(&BTreeSet::from([
        "foreign-leaf",
        "foreign-optional",
        "foreign-dev"
    ])));
    let jobservers = frames
        .iter()
        .flat_map(|f| f["packages"].as_array().unwrap())
        .filter(|p| p["identity"]["name"] == "jobserver")
        .map(|p| p["identity"]["source"].as_str().unwrap())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        jobservers,
        BTreeSet::from(["path:parts/jobserver", "path:foreign/jobserver"])
    );
    let files = value["files"].as_array().unwrap();
    assert!(files.iter().any(|f| f["path"] == "foreign/Cargo.toml"));
    assert!(files.iter().any(|f| f["path"] == "foreign/Cargo.lock"));
}

#[test]
fn vendor_cohort_refuses_dirty_foreign_workspace_inheritance() {
    let world = foreign_fixture();
    let record = saved_record(&world);
    let root = world.join("project/foreign/Cargo.toml");
    fs::write(
        &root,
        fs::read_to_string(&root)
            .unwrap()
            .replace("edition = '2024'", "edition = '2021'"),
    )
    .unwrap();
    let checked = run(
        &world,
        "foreign-dirty-check",
        &[
            "vendor",
            "--cohort-check",
            record.to_str().unwrap(),
            "--locked",
            "--offline",
        ],
    );
    assert!(!checked.status.success(), "world={}", world.display());
    assert!(String::from_utf8_lossy(&checked.stderr).contains("differs from Git"));
}

#[test]
fn vendor_cohort_refuses_staged_only_changes_in_literal_bracket_directory() {
    let world = fixture();
    let project = world.join("project");
    fs::rename(
        project.join("parts/optional"),
        project.join("parts/optional[leaf]"),
    )
    .unwrap();
    let manifest = project.join("parts/app/Cargo.toml");
    fs::write(
        &manifest,
        fs::read_to_string(&manifest)
            .unwrap()
            .replace("../optional\"", "../optional[leaf]\""),
    )
    .unwrap();
    let locked = run(&world, "bracket-lock", &["generate-lockfile", "--offline"]);
    success(&world, &locked);
    commit(&project);
    let record = saved_record(&world);
    let relative = Path::new("parts/optional[leaf]/data/fixture.txt");
    let original = fs::read(project.join(relative)).unwrap();
    fs::write(project.join(relative), "staged changed bytes\n").unwrap();
    let repo = git2::Repository::open(&project).unwrap();
    let mut index = repo.index().unwrap();
    index.add_path(relative).unwrap();
    index.write().unwrap();
    fs::write(project.join(relative), original).unwrap();
    let checked = run(
        &world,
        "bracket-staged-check",
        &[
            "vendor",
            "--cohort-check",
            record.to_str().unwrap(),
            "--locked",
            "--offline",
        ],
    );
    assert!(!checked.status.success(), "world={}", world.display());
    assert!(String::from_utf8_lossy(&checked.stderr).contains("staged, modified or untracked"));
}

#[test]
fn vendor_cohort_refuses_configured_paths_overrides() {
    let world = fixture();
    put(
        &world.join("project"),
        ".cargo/config.toml",
        "paths = ['../override']\n",
    );
    let output = plan(&world, "paths-override-plan");
    assert!(!output.status.success(), "world={}", world.display());
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("does not support configured paths overrides")
    );
}

#[test]
fn vendor_cohort_refuses_configured_patch_inputs() {
    let world = fixture();
    put(
        &world.join("project"),
        ".cargo/config.toml",
        "[patch.crates-io]\njobserver = { path = '../project/parts/jobserver' }\n",
    );
    let output = plan(&world, "configured-patch-plan");
    assert!(!output.status.success(), "world={}", world.display());
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("does not support configured patches")
    );
}

#[test]
fn vendor_cohort_binds_unselected_workspace_summary_inputs() {
    let world = fixture();
    let record = saved_record(&world);
    let value: Value = serde_json::from_slice(&fs::read(&record).unwrap()).unwrap();
    assert!(
        value["files"]
            .as_array()
            .unwrap()
            .iter()
            .any(|f| f["path"] == "parts/unrelated/Cargo.toml")
    );
    assert!(
        !value["files"]
            .as_array()
            .unwrap()
            .iter()
            .any(|f| f["path"] == "parts/unrelated/src/lib.rs")
    );
    let manifest = world.join("project/parts/unrelated/Cargo.toml");
    fs::write(
        &manifest,
        fs::read_to_string(&manifest)
            .unwrap()
            .replace("edition = \"2024\"", "edition = \"2021\""),
    )
    .unwrap();
    let output = plan(&world, "unselected-dirty-plan");
    assert!(!output.status.success(), "world={}", world.display());
    assert!(String::from_utf8_lossy(&output.stderr).contains("differs from Git"));
}

fn gitlink_fixture() -> PathBuf {
    let world = fixture();
    let project = world.join("project");
    let root_manifest = project.join("Cargo.toml");
    fs::write(
        &root_manifest,
        fs::read_to_string(&root_manifest).unwrap().replace(
            "members = [\"parts/*\"]",
            "members = [\"parts/*\"]\nexclude = [\"linked\"]",
        ),
    )
    .unwrap();
    let parent = git2::Repository::open(&project).unwrap();
    let mut linked = parent
        .submodule(
            "https://example.invalid/cohort-linked",
            Path::new("linked"),
            true,
        )
        .unwrap();
    linked.open().unwrap();
    put(
        &project,
        "linked/Cargo.toml",
        "[package]\nname = 'linked-dep'\nversion = '0.1.0'\nedition = '2024'\n[workspace]\n",
    );
    put(
        &project,
        "linked/Cargo.lock",
        "version = 4\n\n[[package]]\nname = 'linked-dep'\nversion = '0.1.0'\n",
    );
    put(&project, "linked/src/lib.rs", "pub fn linked() {}\n");
    commit(&project.join("linked"));
    linked.add_to_index(true).unwrap();
    let manifest = project.join("parts/app/Cargo.toml");
    let app = fs::read_to_string(&manifest).unwrap();
    fs::write(
        manifest,
        format!("{app}\n[dependencies.linked]\npackage = 'linked-dep'\npath = '../../linked'\n"),
    )
    .unwrap();
    let lock = run(&world, "gitlink-lock", &["generate-lockfile", "--offline"]);
    success(&world, &lock);
    commit(&project);
    world
}

#[test]
fn vendor_cohort_captures_exact_gitlinks_and_refuses_dirty_child_source() {
    let world = gitlink_fixture();
    let record = saved_record(&world);
    let value: Value = serde_json::from_slice(&fs::read(&record).unwrap()).unwrap();
    let child = git2::Repository::open(world.join("project/linked")).unwrap();
    assert_eq!(value["gitlinks"].as_array().unwrap().len(), 1);
    assert_eq!(value["gitlinks"][0]["path"], "linked");
    assert_eq!(
        value["gitlinks"][0]["commit"],
        child
            .head()
            .unwrap()
            .peel_to_commit()
            .unwrap()
            .id()
            .to_string()
    );
    assert!(
        value["files"]
            .as_array()
            .unwrap()
            .iter()
            .any(|f| f["path"] == "linked/src/lib.rs")
    );
    let checked = run(
        &world,
        "gitlink-check",
        &[
            "vendor",
            "--cohort-check",
            record.to_str().unwrap(),
            "--locked",
            "--offline",
        ],
    );
    success(&world, &checked);
    put(
        &world.join("project"),
        "linked/src/lib.rs",
        "pub fn changed() {}\n",
    );
    let output = plan(&world, "dirty-gitlink-plan");
    assert!(!output.status.success(), "world={}", world.display());
    assert!(String::from_utf8_lossy(&output.stderr).contains("differs from Git"));
}

#[test]
fn vendor_cohort_refuses_changed_or_staged_gitlink_identity() {
    let world = gitlink_fixture();
    let project = world.join("project");
    let child = git2::Repository::open(project.join("linked")).unwrap();
    let original = child.head().unwrap().peel_to_commit().unwrap().id();
    put(&project, "linked/src/lib.rs", "pub fn new_commit() {}\n");
    commit(&project.join("linked"));
    let replacement = child.head().unwrap().peel_to_commit().unwrap().id();
    let output = plan(&world, "changed-gitlink-plan");
    assert!(!output.status.success(), "world={}", world.display());
    assert!(String::from_utf8_lossy(&output.stderr).contains("not at its pinned commit"));
    child.set_head_detached(original).unwrap();
    put(&project, "linked/src/lib.rs", "pub fn linked() {}\n");
    let parent = git2::Repository::open(&project).unwrap();
    let mut index = parent.index().unwrap();
    let mut entry = index.get_path(Path::new("linked"), 0).unwrap();
    entry.id = replacement;
    index.add(&entry).unwrap();
    index.write().unwrap();
    let output = plan(&world, "staged-gitlink-plan");
    assert!(!output.status.success(), "world={}", world.display());
    assert!(String::from_utf8_lossy(&output.stderr).contains("staged gitlink differs from Git"));
}

#[test]
fn ordinary_vendor_materializes_and_repeats_without_cohort_flags() {
    let world = fixture();
    let registry = world.join("registry");
    fs::create_dir_all(registry.join("index/ve/nd")).unwrap();
    let mut archive = tar::Builder::new(flate2::write::GzEncoder::new(
        Vec::new(),
        flate2::Compression::default(),
    ));
    let manifest = "[package]\nname = 'vendor-leaf'\nversion = '0.1.0'\nedition = '2024'\n";
    let source = "pub fn value() -> u32 { 7 }\n";
    for (relative, contents) in [("Cargo.toml", manifest), ("src/lib.rs", source)] {
        let mut header = tar::Header::new_gnu();
        header.set_size(contents.len() as u64);
        header.set_mode(0o644);
        header.set_mtime(0);
        header.set_cksum();
        archive
            .append_data(
                &mut header,
                format!("vendor-leaf-0.1.0/{relative}"),
                contents.as_bytes(),
            )
            .unwrap();
    }
    let archive = archive.into_inner().unwrap().finish().unwrap();
    let checksum = cargo_test_support::registry::cksum(&archive);
    fs::write(registry.join("vendor-leaf-0.1.0.crate"), archive).unwrap();
    fs::write(registry.join("index/ve/nd/vendor-leaf"), serde_json::json!({"name":"vendor-leaf","vers":"0.1.0","deps":[],"cksum":checksum,"features":{},"yanked":false}).to_string() + "\n").unwrap();
    let project = world.join("project");
    put(
        &project,
        ".cargo/config.toml",
        &format!(
            "[source.crates-io]\nreplace-with = 'fixture'\n[source.fixture]\nlocal-registry = {:?}\n",
            registry.to_str().unwrap()
        ),
    );
    let app = project.join("parts/app/Cargo.toml");
    fs::write(
        &app,
        fs::read_to_string(&app).unwrap()
            + "\n[dependencies.vendored]\npackage = 'vendor-leaf'\nversion = '0.1.0'\n",
    )
    .unwrap();
    let locked = run(&world, "ordinary-lock", &["generate-lockfile", "--offline"]);
    success(&world, &locked);
    let args = ["vendor", "--respect-source-config", "--locked", "--offline"];
    let first = run(&world, "ordinary-vendor-first", &args);
    success(&world, &first);
    assert!(!String::from_utf8_lossy(&first.stdout).contains("targo-vendor-cohort"));
    assert!(cohort_phases(&first).is_empty());
    let files = ["Cargo.toml", "src/lib.rs", ".cargo-checksum.json"];
    let before = files.map(|name| fs::read(project.join("vendor/vendor-leaf").join(name)).unwrap());
    assert_eq!(before[1], source.as_bytes());
    let second = run(&world, "ordinary-vendor-second", &args);
    success(&world, &second);
    assert!(cohort_phases(&second).is_empty());
    assert_eq!(first.stdout, second.stdout);
    for (name, expected) in files.into_iter().zip(before) {
        assert_eq!(
            fs::read(project.join("vendor/vendor-leaf").join(name)).unwrap(),
            expected
        );
    }
    fs::write(project.join(".cargo/config.toml"), &second.stdout).unwrap();
    let consumed = run(
        &world,
        "ordinary-vendored-metadata",
        &["metadata", "--locked", "--offline", "--format-version", "1"],
    );
    success(&world, &consumed);
    let value: Value = serde_json::from_slice(&consumed.stdout).unwrap();
    let package = value["packages"]
        .as_array()
        .unwrap()
        .iter()
        .find(|p| p["name"] == "vendor-leaf")
        .unwrap();
    assert!(
        package["manifest_path"]
            .as_str()
            .unwrap()
            .ends_with("vendor/vendor-leaf/Cargo.toml")
    );
}

fn repository_root_fixture() -> PathBuf {
    let world = fixture();
    let project = world.join("project");
    let manifest = project.join("Cargo.toml");
    fs::write(
        &manifest,
        fs::read_to_string(&manifest).unwrap()
            + "\n[package]\nname = 'repository-root'\nversion = '0.1.0'\nedition = '2024'\n",
    )
    .unwrap();
    put(&project, "src/lib.rs", "pub fn value() -> u32 { 7 }\n");
    let lock = run(
        &world,
        "repository-root-lock",
        &["generate-lockfile", "--offline"],
    );
    success(&world, &lock);
    commit(&project);
    world
}

fn plan_repository_root(world: &Path, label: &str) -> Output {
    run(
        world,
        label,
        &[
            "vendor",
            "--cohort-plan",
            "-p",
            "repository-root",
            "--locked",
            "--offline",
        ],
    )
}

fn checked_repository_root_record(world: &Path) -> PathBuf {
    let output = plan_repository_root(world, "repository-root-clean-plan");
    success(world, &output);
    let record = world.join("repository-root-record.json");
    fs::write(&record, &output.stdout).unwrap();
    let repo = git2::Repository::open(world.join("project")).unwrap();
    assert!(repo.statuses(None).unwrap().is_empty());
    let checked = run(
        world,
        "repository-root-clean-check",
        &[
            "vendor",
            "--cohort-check",
            record.to_str().unwrap(),
            "--locked",
            "--offline",
        ],
    );
    success(world, &checked);
    assert!(String::from_utf8_lossy(&checked.stdout).contains("Source cohort matches"));
    record
}

fn refuse_dirty_repository_root(world: &Path, record: &Path) {
    let checked = run(
        world,
        "repository-root-dirty-check",
        &[
            "vendor",
            "--cohort-check",
            record.to_str().unwrap(),
            "--locked",
            "--offline",
        ],
    );
    let planned = plan_repository_root(world, "repository-root-dirty-plan");
    for output in [&checked, &planned] {
        assert!(!output.status.success(), "world={}", world.display());
        assert!(output.stdout.is_empty(), "world={}", world.display());
        assert!(
            String::from_utf8_lossy(&output.stderr)
                .contains("staged, modified or untracked source inputs"),
            "world={}\n{}",
            world.display(),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
fn vendor_cohort_repository_root_refuses_staged_source_after_working_bytes_restore() {
    let world = repository_root_fixture();
    let record = checked_repository_root_record(&world);
    let project = world.join("project");
    let relative = Path::new("src/lib.rs");
    let original = fs::read(project.join(relative)).unwrap();
    fs::write(project.join(relative), "pub fn value() -> u32 { 9 }\n").unwrap();
    let repo = git2::Repository::open(&project).unwrap();
    let mut index = repo.index().unwrap();
    index.add_path(relative).unwrap();
    index.write().unwrap();
    fs::write(project.join(relative), &original).unwrap();
    assert_eq!(fs::read(project.join(relative)).unwrap(), original);
    let statuses = repo.statuses(None).unwrap();
    assert!(statuses.iter().any(|entry| {
        matches!(entry.path(), Ok("src/lib.rs"))
            && entry
                .status()
                .contains(git2::Status::INDEX_MODIFIED | git2::Status::WT_MODIFIED)
    }));
    refuse_dirty_repository_root(&world, &record);
}

#[test]
fn vendor_cohort_repository_root_refuses_untracked_source() {
    let world = repository_root_fixture();
    let record = checked_repository_root_record(&world);
    let project = world.join("project");
    put(&project, "extra.txt", "untracked source data\n");
    let repo = git2::Repository::open(&project).unwrap();
    assert!(repo.statuses(None).unwrap().iter().any(|entry| matches!(
        entry.path(),
        Ok("extra.txt")
    )
        && entry.status().contains(git2::Status::WT_NEW)));
    refuse_dirty_repository_root(&world, &record);
}

fn cohort_phases(output: &Output) -> Vec<String> {
    String::from_utf8_lossy(&output.stderr)
        .lines()
        .map(str::trim_start)
        .filter(|line| {
            [
                "Resolving source cohort ",
                "Inspecting source cohort ",
                "Checking source cohort ",
            ]
            .iter()
            .any(|prefix| line.starts_with(prefix))
        })
        .map(str::to_owned)
        .collect()
}

#[test]
fn vendor_cohort_phase_status_is_stderr_only_and_quiet_preserves_data() {
    let world = fixture();
    let planned = plan(&world, "phase-plan");
    success(&world, &planned);
    let _: Value = serde_json::from_slice(&planned.stdout).unwrap();
    let expected = [
        "Resolving source cohort workspace Cargo.toml",
        "Inspecting source cohort inputs and package files",
        "Checking source cohort Git state (repository count 1)",
    ];
    assert_eq!(cohort_phases(&planned), expected);
    let quiet = run(
        &world,
        "phase-quiet-plan",
        &[
            "--quiet",
            "vendor",
            "--cohort-plan",
            "-p",
            "cohort-root",
            "--locked",
            "--offline",
        ],
    );
    success(&world, &quiet);
    assert!(quiet.stderr.is_empty());
    assert_eq!(planned.stdout, quiet.stdout);
    let record = world.join("phase-record.json");
    fs::write(&record, &planned.stdout).unwrap();
    let checked = run(
        &world,
        "phase-check",
        &[
            "vendor",
            "--cohort-check",
            record.to_str().unwrap(),
            "--locked",
            "--offline",
        ],
    );
    success(&world, &checked);
    assert_eq!(cohort_phases(&checked), expected);
    let quiet_checked = run(
        &world,
        "phase-quiet-check",
        &[
            "--quiet",
            "vendor",
            "--cohort-check",
            record.to_str().unwrap(),
            "--locked",
            "--offline",
        ],
    );
    success(&world, &quiet_checked);
    assert!(quiet_checked.stderr.is_empty());
    assert_eq!(checked.stdout, quiet_checked.stdout);
}

#[test]
fn vendor_cohort_phase_status_preserves_empty_failure_stdout_and_quiet_errors() {
    let world = fixture();
    let record = saved_record(&world);
    put(
        &world.join("project"),
        "parts/optional/data/fixture.txt",
        "dirty source input\n",
    );
    let planned = plan(&world, "phase-failed-plan");
    let checked = run(
        &world,
        "phase-failed-check",
        &[
            "vendor",
            "--cohort-check",
            record.to_str().unwrap(),
            "--locked",
            "--offline",
        ],
    );
    for output in [&planned, &checked] {
        assert!(!output.status.success(), "world={}", world.display());
        assert!(output.stdout.is_empty());
        assert!(!cohort_phases(output).is_empty());
        assert!(String::from_utf8_lossy(&output.stderr).contains("differs from Git"));
    }
    let quiet = run(
        &world,
        "phase-quiet-failed-plan",
        &[
            "--quiet",
            "vendor",
            "--cohort-plan",
            "-p",
            "cohort-root",
            "--locked",
            "--offline",
        ],
    );
    let quiet_checked = run(
        &world,
        "phase-quiet-failed-check",
        &[
            "--quiet",
            "vendor",
            "--cohort-check",
            record.to_str().unwrap(),
            "--locked",
            "--offline",
        ],
    );
    for output in [&quiet, &quiet_checked] {
        assert!(!output.status.success(), "world={}", world.display());
        assert!(output.stdout.is_empty());
        assert!(cohort_phases(output).is_empty());
        assert!(String::from_utf8_lossy(&output.stderr).contains("differs from Git"));
    }
}

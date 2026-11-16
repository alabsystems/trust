#![cfg(target_os = "macos")]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use cargo_test_support::{cargo_test, git, paths, registry::Package};

struct ObservedBuild {
    artifacts: Vec<serde_json::Value>,
    execution: serde_json::Value,
}

fn project(root: &Path, name: &str, dependency: &str) -> PathBuf {
    let path = root.join(name);
    fs::create_dir_all(path.join("src")).unwrap();
    fs::create_dir(path.join(".cargo")).unwrap();
    fs::write(
        path.join(".cargo/config.toml"),
        format!(
            "[source.crates-io]\nreplace-with='local'\n[source.local]\nlocal-registry={:?}\n",
            root.join("registry")
        ),
    )
    .unwrap();
    fs::write(path.join("Cargo.toml"), format!(
        "[package]\nname={name:?}\nversion='0.0.0'\nedition='2021'\n[workspace]\n[dependencies]\n{dependency}='1.0.0'\n"
    )).unwrap();
    // This script remains private while its pure registry dependency is shared.
    fs::write(
        path.join("build.rs"),
        "fn main() { println!(\"cargo:rustc-env=ROOT_ONLY=private\"); }\n",
    )
    .unwrap();
    fs::write(path.join("src/lib.rs"), format!(
        "pub const ROOT: &str = env!(\"ROOT_ONLY\");\npub fn value() -> u32 {{ {dependency}::value() }}\n"
    )).unwrap();
    path
}

fn build(project: &Path, home: &Path) -> ObservedBuild {
    build_with_source_trace(project, home).0
}

fn targo(project: &Path, home: &Path) -> Command {
    let executable = std::env::var_os("TARGO_SHARED_TEST_BINARY")
        .unwrap_or_else(|| env!("CARGO_BIN_EXE_targo").into());
    let mut command = Command::new(executable);
    command
        .current_dir(project)
        .env_clear()
        .env("HOME", home)
        .env("CARGO_HOME", home.join(".cargo"))
        .env("CARGO_TARGET_DIR", project.join("target"))
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env("RUSTC", std::env::var_os("RUSTC").unwrap())
        .env("CARGO_LOG", "targo_core::compiler::action_inputs=trace")
        .env("__CARGO_TEST_CHANNEL_OVERRIDE_DO_NOT_USE_THIS", "nightly");
    command
}

fn build_with_source_trace(project: &Path, home: &Path) -> (ObservedBuild, String) {
    observe(project, home, false)
}

fn observe(project: &Path, home: &Path, plan_only: bool) -> (ObservedBuild, String) {
    let mut command = targo(project, home);
    command.args([
        "--unverified",
        "build",
        "--offline",
        "--lib",
        "-Zbuild-analysis",
        "-Zmem-stats",
        "-Zbuild-dir-new-layout",
        "-Zfine-grain-locking",
        "--config",
        "build.analysis.enabled=true",
        "--config",
        "build.shared-dependency-cache=true",
        "--message-format=json",
    ]);
    if plan_only {
        command.args(["--unit-graph", "-Zunstable-options"]);
    }
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let rows: Vec<serde_json::Value> = String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
        .collect();
    let sessions: Vec<_> = rows
        .iter()
        .filter(|row| row["reason"] == "build-analysis-session")
        .collect();
    assert_eq!(sessions.len(), 1, "{rows:?}");
    let id = sessions[0]["run_id"].as_str().unwrap();
    let report = targo(project, home)
        .args([
            "-Zbuild-analysis",
            "report",
            "execution",
            "--id",
            id,
            "--json",
        ])
        .output()
        .unwrap();
    assert!(
        report.status.success(),
        "{}",
        String::from_utf8_lossy(&report.stderr)
    );
    let execution: serde_json::Value = serde_json::from_slice(&report.stdout).unwrap();
    assert_eq!(execution["run_id"], id);
    if plan_only {
        assert!(execution["graph_outcome"].is_null());
        assert!(execution["execution"].is_null());
        assert!(execution["compiler_activity"]["successful_primary_processes"].is_null());
    } else {
        assert_eq!(execution["graph_outcome"], "succeeded");
        assert_eq!(execution["compiler_activity"]["availability"], "complete");
    }
    assert_eq!(
        execution["shared_dependency_frontier"]["availability"],
        "complete"
    );
    let artifacts = rows
        .into_iter()
        .filter(|row| row["reason"] == "compiler-artifact")
        .collect();
    (
        ObservedBuild {
            artifacts,
            execution,
        },
        String::from_utf8(output.stderr).unwrap(),
    )
}

fn fetch(project: &Path, home: &Path) {
    let output = targo(project, home).arg("fetch").output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

fn pin_git_dependency(project: &Path, name: &str, url: &str, revision: &str, variant: bool) {
    let manifest = project.join("Cargo.toml");
    let contents = fs::read_to_string(&manifest).unwrap();
    let declaration = format!(
        "{name}={{git={url:?},rev={revision:?},features={}}}",
        if variant { "['variant']" } else { "[]" },
    );
    let (before, _) = contents.rsplit_once(&format!("{name}=")).unwrap();
    fs::write(manifest, format!("{before}{declaration}\n")).unwrap();
}

fn dependency<'a>(build: &'a ObservedBuild, name: &str) -> &'a serde_json::Value {
    build
        .artifacts
        .iter()
        .find(|row| row["target"]["name"] == name)
        .unwrap()
}

fn compiler_processes(build: &ObservedBuild, name: &str) -> u64 {
    let units: Vec<_> = build.execution["units"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|unit| unit["target"]["name"] == name && unit["target"]["kind"] == "lib")
        .collect();
    assert_eq!(units.len(), 1, "{name}: {}", build.execution);
    let process = &units[0]["process"];
    if process["command_started_seconds"].is_null() {
        assert!(process["owning_wait_cpu"].is_null());
        assert!(process["peak_rss_bytes"].is_null());
        0
    } else {
        assert!(process["finished_seconds"].is_number());
        assert!(process["owning_wait_cpu"]["user_ns"].is_u64());
        assert!(process["owning_wait_cpu"]["system_ns"].is_u64());
        assert!(process["peak_rss_bytes"].is_u64());
        assert_eq!(units[0]["outcome"], "succeeded");
        1
    }
}

fn shared_status<'a>(build: &'a ObservedBuild, name: &str) -> &'a serde_json::Value {
    let units: Vec<_> = build.execution["units"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|unit| unit["target"]["name"] == name && unit["target"]["kind"] == "lib")
        .collect();
    assert_eq!(units.len(), 1);
    &units[0]["shared_dependency"]["status"]
}

#[cargo_test]
fn planned_frontier_is_available_without_preparing_compilation_jobs() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    Package::new("shared_leaf", "1.0.0")
        .local(true)
        .file("src/lib.rs", "pub fn value() -> u32 {42}\n")
        .publish();
    let project = project(&root, "planner", "shared_leaf");
    let (planned, _) = observe(&project, &home, true);
    assert!(planned.artifacts.is_empty());
    assert_eq!(
        planned.execution["shared_dependency_frontier"]["eligible_units"],
        1
    );
    assert_eq!(shared_status(&planned, "shared_leaf"), "eligible");
    assert!(
        planned.execution["shared_dependency_frontier"]["measured_compiler_commands"].is_null()
    );
    for unit in planned.execution["units"].as_array().unwrap() {
        assert!(unit["scheduled_fresh"].is_null());
        assert!(unit["process"]["command_started_seconds"].is_null());
    }
    assert!(
        !home
            .join(".cargo/trust/native-dependencies-v1/build")
            .exists()
    );
}

#[cargo_test]
fn warm_shared_dependency_reads_its_source_once_per_preparation() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    Package::new("shared_leaf", "1.0.0")
        .local(true)
        .file("src/lib.rs", "pub fn value() -> u32 { 42 }\n")
        .publish();
    let first = project(&root, "first", "shared_leaf");
    let second = project(&root, "second", "shared_leaf");
    assert_eq!(
        dependency(&build(&first, &home), "shared_leaf")["fresh"],
        false
    );
    let (rows, trace) = build_with_source_trace(&second, &home);
    assert_eq!(dependency(&rows, "shared_leaf")["fresh"], true);
    assert_eq!(
        trace
            .lines()
            .filter(|line| line.contains("capturing confined source inputs"))
            .count(),
        1,
        "one preparation must share its source capture between command and fingerprint: {trace}"
    );
}

#[cargo_test]
fn pinned_git_reuse_binds_commit_source_features_and_executable_extensions() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    let repository = git::repo(&root.join("origin"))
        .file("Cargo.toml", "[package]\nname='git_leaf'\nversion='1.0.0'\nedition='2021'\n[workspace]\nmembers=['git_macro','git_scripted','git_wrapper']\n[features]\nvariant=[]\n")
        .file("src/lib.rs", "pub fn value() -> u32 { 42 }\n")
        .file("git_macro/Cargo.toml", "[package]\nname='git_macro'\nversion='1.0.0'\nedition='2021'\n[lib]\nproc-macro=true\n")
        .file("git_macro/src/lib.rs", "extern crate proc_macro; #[proc_macro] pub fn pass(input: proc_macro::TokenStream) -> proc_macro::TokenStream { input }\n")
        .file("git_scripted/Cargo.toml", "[package]\nname='git_scripted'\nversion='1.0.0'\nedition='2021'\n[dependencies]\ngit_macro={path='../git_macro'}\n")
        .file("git_scripted/build.rs", "fn main() { println!(\"cargo:rustc-env=GIT_PRIVATE=private\"); }\n")
        .file("git_scripted/src/lib.rs", "pub fn value() -> u32 { assert_eq!(env!(\"GIT_PRIVATE\"), \"private\"); git_macro::pass!(42) }\n")
        .file("git_wrapper/Cargo.toml", "[package]\nname='git_wrapper'\nversion='1.0.0'\nedition='2021'\n[dependencies]\ngit_scripted={path='../git_scripted'}\n")
        .file("git_wrapper/src/lib.rs", "pub fn value() -> u32 { git_scripted::value() }\n")
        .build();
    let url = repository.url().to_string();
    let first_commit = repository.revparse_head();
    let first = project(&root, "first", "git_leaf");
    let second = project(&root, "second", "git_leaf");
    for project in [&first, &second] {
        pin_git_dependency(project, "git_leaf", &url, &first_commit, false);
    }
    fetch(&first, &home);
    assert_eq!(
        dependency(&build(&first, &home), "git_leaf")["fresh"],
        false
    );
    fetch(&second, &home);
    let warm = build(&second, &home);
    let shared = dependency(&warm, "git_leaf");
    assert_eq!(shared["fresh"], true);
    let archive = shared["filenames"][0].as_str().unwrap().to_owned();
    assert!(archive.contains(&format!("/build/git/{first_commit}/")));

    pin_git_dependency(&second, "git_leaf", &url, &first_commit, true);
    let variant = build(&second, &home);
    assert_eq!(dependency(&variant, "git_leaf")["fresh"], false);
    assert_ne!(dependency(&variant, "git_leaf")["filenames"][0], archive);
    pin_git_dependency(&second, "git_leaf", &url, &first_commit, false);
    assert_eq!(
        dependency(&build(&second, &home), "git_leaf")["fresh"],
        true
    );

    // HEAD and .cargo-ok alone do not prove a cached checkout is unchanged.
    let source = Path::new(shared["manifest_path"].as_str().unwrap())
        .parent()
        .unwrap()
        .join("src/lib.rs");
    let stamp = filetime::FileTime::from_last_modification_time(&fs::metadata(&source).unwrap());
    fs::write(&source, "pub fn value() -> u32 { 43 }\n").unwrap();
    filetime::set_file_mtime(&source, stamp).unwrap();
    assert_eq!(
        dependency(&build(&second, &home), "git_leaf")["fresh"],
        false
    );
    fs::write(&source, "pub fn value() -> u32 { 42 }\n").unwrap();
    filetime::set_file_mtime(&source, stamp).unwrap();
    assert_eq!(
        dependency(&build(&second, &home), "git_leaf")["fresh"],
        false
    );

    fs::write(
        repository.root().join("src/lib.rs"),
        "pub fn value() -> u32 { 44 }\n",
    )
    .unwrap();
    let git = git2::Repository::open(repository.root()).unwrap();
    git::add(&git);
    let next_commit = git::commit(&git).to_string();
    pin_git_dependency(&second, "git_leaf", &url, &next_commit, false);
    fetch(&second, &home);
    let changed = build(&second, &home);
    let changed = dependency(&changed, "git_leaf");
    assert_eq!(changed["fresh"], false);
    assert!(
        changed["filenames"][0]
            .as_str()
            .unwrap()
            .contains(&format!("/build/git/{next_commit}/"))
    );
    pin_git_dependency(&second, "git_leaf", &url, &first_commit, false);
    fetch(&second, &home);
    assert_eq!(
        dependency(&build(&second, &home), "git_leaf")["fresh"],
        true
    );

    let private = project(&root, "private", "git_wrapper");
    pin_git_dependency(&private, "git_wrapper", &url, &next_commit, false);
    fetch(&private, &home);
    let private_rows = build(&private, &home);
    assert_eq!(
        shared_status(&private_rows, "git_wrapper"),
        "dependency-blocked"
    );
    assert_eq!(shared_status(&private_rows, "git_scripted"), "excluded");
    assert_eq!(shared_status(&private_rows, "git_macro"), "excluded");
    for name in ["git_wrapper", "git_scripted", "git_macro"] {
        assert!(
            dependency(&private_rows, name)["filenames"]
                .as_array()
                .unwrap()
                .iter()
                .filter_map(serde_json::Value::as_str)
                .all(|file| Path::new(file).starts_with(private.join("target"))),
            "Git build-script and proc-macro units and their dependents must remain private"
        );
    }
}

#[cargo_test]
fn unchanged_git_parent_retains_variants_of_a_floating_git_dependency() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    let leaf = git::repo(&root.join("leaf"))
        .file(
            "Cargo.toml",
            "[package]\nname='git_leaf'\nversion='1.0.0'\nedition='2021'\n",
        )
        .file("src/lib.rs", "pub fn value() -> u32 { 41 }\n")
        .build();
    let parent = git::repo(&root.join("parent"))
        .file("Cargo.toml", &format!(
            "[package]\nname='git_parent'\nversion='1.0.0'\nedition='2021'\n[dependencies]\ngit_leaf={{git={:?}}}\n",
            leaf.url().as_str(),
        ))
        .file("src/lib.rs", "pub fn value() -> u32 { git_leaf::value() }\n")
        .build();
    let first = project(&root, "first", "git_parent");
    let second = project(&root, "second", "git_parent");
    for project in [&first, &second] {
        pin_git_dependency(
            project,
            "git_parent",
            parent.url().as_str(),
            &parent.revparse_head(),
            false,
        );
    }
    fetch(&first, &home);
    let first_rows = build(&first, &home);
    assert_eq!(dependency(&first_rows, "git_parent")["fresh"], false);

    fs::write(
        leaf.root().join("src/lib.rs"),
        "pub fn value() -> u32 { 42 }\n",
    )
    .unwrap();
    let repository = git2::Repository::open(leaf.root()).unwrap();
    git::add(&repository);
    git::commit(&repository);
    fetch(&second, &home);
    let second_rows = build(&second, &home);
    assert_eq!(dependency(&second_rows, "git_parent")["fresh"], false);
    assert_ne!(
        dependency(&first_rows, "git_parent")["filenames"],
        dependency(&second_rows, "git_parent")["filenames"],
        "an unchanged parent must retain separate output slots for resolved child commits"
    );
    assert_eq!(
        dependency(&build(&first, &home), "git_parent")["fresh"],
        true,
        "returning to the first lockfile must reuse its original parent compilation"
    );

    let first_home = home.clone();
    let worker = std::thread::spawn(move || build(&first, &first_home));
    let second_rows = build(&second, &home);
    let first_rows = worker.join().unwrap();
    for rows in [&first_rows, &second_rows] {
        assert_eq!(
            dependency(rows, "git_parent")["fresh"],
            true,
            "concurrent consumers of different child commits must not overwrite each other"
        );
    }
}

#[cargo_test]
fn independent_projects_share_registry_output_and_one_concurrent_producer() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    for name in ["shared_leaf", "race_leaf"] {
        Package::new(name, "1.0.0")
            .local(true)
            .feature("variant", &[])
            .file("src/lib.rs", "pub fn value() -> u32 { 42 }\n")
            .publish();
    }
    Package::new("passthrough", "1.0.0").local(true).proc_macro(true)
        .file("src/lib.rs", "extern crate proc_macro; #[proc_macro] pub fn pass(input: proc_macro::TokenStream) -> proc_macro::TokenStream { input }\n")
        .publish();
    Package::new("scripted_dep", "1.0.0").local(true).dep("passthrough", "1.0.0")
        .file("build.rs", "fn main() { println!(\"cargo:rustc-env=DEPENDENCY_ONLY=private\"); }\n")
        .file("src/lib.rs", "extern crate passthrough; pub fn value() -> u32 { assert_eq!(env!(\"DEPENDENCY_ONLY\"), \"private\"); passthrough::pass!(42) }\n")
        .publish();
    let first = project(&root, "first", "shared_leaf");
    let second = project(&root, "second", "shared_leaf");
    let cold = build(&first, &home);
    assert_eq!(shared_status(&cold, "shared_leaf"), "eligible");
    assert_eq!(dependency(&cold, "shared_leaf")["fresh"], false);
    assert_eq!(compiler_processes(&cold, "shared_leaf"), 1);
    let warm = build(&second, &home);
    assert_eq!(shared_status(&warm, "shared_leaf"), "eligible");
    assert_eq!(compiler_processes(&warm, "shared_leaf"), 0);
    let shared = dependency(&warm, "shared_leaf");
    assert_eq!(
        shared["fresh"], true,
        "the second project recompiled the same dependency"
    );
    let archive = shared["filenames"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(serde_json::Value::as_str)
        .find(|path| path.ends_with(".rlib"))
        .unwrap();
    assert!(Path::new(archive).starts_with(home.join(".cargo/trust/native-dependencies-v1")));
    let archive = PathBuf::from(archive);
    let time = filetime::FileTime::from_last_modification_time(&fs::metadata(&archive).unwrap());
    let mut bytes = fs::read(&archive).unwrap();
    bytes[..8].copy_from_slice(b"BROKEN!!");
    fs::write(&archive, bytes).unwrap();
    filetime::set_file_mtime(&archive, time).unwrap();
    let repaired = build(&second, &home);
    assert_eq!(dependency(&repaired, "shared_leaf")["fresh"], false);
    assert_eq!(compiler_processes(&repaired, "shared_leaf"), 1);
    assert!(fs::read(&archive).unwrap().starts_with(b"!<arch>\n"));

    let manifest = second.join("Cargo.toml");
    let original_manifest = fs::read_to_string(&manifest).unwrap();
    fs::write(
        &manifest,
        original_manifest.replace(
            "shared_leaf='1.0.0'",
            "shared_leaf={version='1.0.0',features=['variant']}",
        ),
    )
    .unwrap();
    let variant = build(&second, &home);
    assert_eq!(dependency(&variant, "shared_leaf")["fresh"], false);
    assert_eq!(compiler_processes(&variant, "shared_leaf"), 1);
    fs::write(&manifest, original_manifest).unwrap();
    let restored = build(&second, &home);
    assert_eq!(compiler_processes(&restored, "shared_leaf"), 0);
    assert_eq!(
        dependency(&restored, "shared_leaf")["fresh"],
        true,
        "returning to the original feature set must reuse its existing artifact"
    );

    let private = project(&root, "private", "scripted_dep");
    let private_rows = build(&private, &home);
    for name in ["scripted_dep", "passthrough"] {
        assert!(
            dependency(&private_rows, name)["filenames"]
                .as_array()
                .unwrap()
                .iter()
                .filter_map(serde_json::Value::as_str)
                .all(|file| Path::new(file).starts_with(private.join("target"))),
            "build-script and proc-macro units must remain private"
        );
    }

    let external = root.join("external_leaf");
    fs::create_dir_all(external.join("src")).unwrap();
    fs::write(
        external.join("Cargo.toml"),
        "[package]\nname='external_leaf'\nversion='1.0.0'\nedition='2021'\n[workspace]\n",
    )
    .unwrap();
    fs::write(
        external.join("src/lib.rs"),
        "pub fn value() -> u32 { 42 }\n",
    )
    .unwrap();
    let path_first = project(&root, "path_first", "external_leaf");
    let path_second = project(&root, "path_second", "external_leaf");
    for path in [&path_first, &path_second] {
        let manifest = path.join("Cargo.toml");
        let contents = fs::read_to_string(&manifest).unwrap();
        fs::write(
            manifest,
            contents.replace(
                "external_leaf='1.0.0'",
                &format!("external_leaf={{path={external:?}}}"),
            ),
        )
        .unwrap();
    }
    assert_eq!(
        dependency(&build(&path_first, &home), "external_leaf")["fresh"],
        false
    );
    assert_eq!(
        dependency(&build(&path_second, &home), "external_leaf")["fresh"],
        true,
        "two projects using the same external source directory must share its compilation"
    );
    let source = external.join("src/lib.rs");
    let stamp = filetime::FileTime::from_last_modification_time(&fs::metadata(&source).unwrap());
    fs::write(&source, "pub fn value() -> u32 { 43 }\n").unwrap();
    filetime::set_file_mtime(&source, stamp).unwrap();
    let changed = build(&path_first, &home);
    assert_eq!(compiler_processes(&changed, "external_leaf"), 1);
    assert_eq!(
        dependency(&changed, "external_leaf")["fresh"],
        false,
        "same-size source edits with a preserved mtime must invalidate shared output"
    );
    let replacement = build(&path_second, &home);
    assert_eq!(compiler_processes(&replacement, "external_leaf"), 0);
    assert_eq!(
        dependency(&replacement, "external_leaf")["fresh"],
        true,
        "the second consumer must reuse the replacement compilation"
    );

    let left = project(&root, "left", "race_leaf");
    let right = project(&root, "right", "race_leaf");
    let other_home = home.clone();
    let worker = std::thread::spawn(move || build(&left, &other_home));
    let right = build(&right, &home);
    let left = worker.join().unwrap();
    assert_eq!(
        compiler_processes(&left, "race_leaf") + compiler_processes(&right, "race_leaf"),
        1,
        "concurrent consumers must have exactly one measured compiler process, irrespective of initial dirty dispatch"
    );
    let fresh = [&left, &right]
        .into_iter()
        .filter(|rows| dependency(rows, "race_leaf")["fresh"] == true)
        .count();
    assert_eq!(
        fresh, 1,
        "two concurrent projects must run exactly one dependency compilation"
    );
}

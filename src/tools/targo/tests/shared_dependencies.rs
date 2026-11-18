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
    // Only Targo asks a unit source (DC-24a): a build script never sees it.
    fs::write(
        path.join("build.rs"),
        "fn main() {\n\
         assert_eq!(std::env::var_os(\"TRUST_TARGO_UNIT_SOURCE\"), None, \"a build script sees the unit source\");\n\
         println!(\"cargo:rustc-env=ROOT_ONLY=private\");\n\
         }\n",
    )
    .unwrap();
    fs::write(path.join("src/lib.rs"), format!(
        "pub const ROOT: &str = env!(\"ROOT_ONLY\");\npub fn value() -> u32 {{ {dependency}::value() }}\n"
    )).unwrap();
    path
}

/// A project that checks `build.shared-dependency-cache` in, as a repository
/// does (DC-17a).
fn keyed_project(root: &Path, name: &str, dependency: &str) -> PathBuf {
    let path = project(root, name, dependency);
    let config = path.join(".cargo/config.toml");
    let mut contents = fs::read_to_string(&config).unwrap();
    contents.push_str("[build]\nshared-dependency-cache = true\n");
    fs::write(config, contents).unwrap();
    path
}

/// Fine-grain locking keeps a `.lock` in each private unit's build directory
/// (`build/<package>/<hash>/.lock`); a whole-directory lock does not.
fn unit_locks(project: &Path) -> usize {
    fs::read_dir(project.join("target/debug/build"))
        .unwrap()
        .flat_map(|package| fs::read_dir(package.unwrap().path()).unwrap())
        .filter(|unit| unit.as_ref().unwrap().path().join(".lock").is_file())
        .count()
}

fn build(project: &Path, home: &Path) -> ObservedBuild {
    build_with_source_trace(project, home).0
}

fn targo(project: &Path, home: &Path) -> Command {
    let executable = std::env::var_os("TARGO_SHARED_TEST_BINARY")
        .unwrap_or_else(|| env!("CARGO_BIN_EXE_targo").into());
    // Under `x.py test src/tools/targo` the inherited RUSTC is bootstrap's own
    // tool-build shim, which needs the bootstrap env `env_clear` removes, and
    // whose fixture copy reads a sidecar the shared producer's deny-default
    // action sandbox does not admit. The step names the compiler it tests
    // instead (TRUST_TARGO_TEST_TESTED_RUSTC). A direct run keeps its RUSTC.
    let rustc = std::env::var_os("TRUST_TARGO_TEST_TESTED_RUSTC")
        .or_else(|| std::env::var_os("RUSTC"))
        .expect("test requires an explicit compiler or bootstrap's tested compiler");
    let mut command = Command::new(executable);
    command
        .current_dir(project)
        .env_clear()
        .env("HOME", home)
        .env("CARGO_HOME", home.join(".cargo"))
        .env("CARGO_TARGET_DIR", project.join("target"))
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env("RUSTC", rustc)
        .env("CARGO_LOG", "targo_core::compiler::action_inputs=trace")
        .env("__CARGO_TEST_CHANNEL_OVERRIDE_DO_NOT_USE_THIS", "nightly");
    command
}

fn build_with_source_trace(project: &Path, home: &Path) -> (ObservedBuild, String) {
    observe(project, home, false)
}

fn observe(project: &Path, home: &Path, plan_only: bool) -> (ObservedBuild, String) {
    observe_with(project, home, plan_only, |_| {})
}

fn observe_with(
    project: &Path,
    home: &Path,
    plan_only: bool,
    configure: impl FnOnce(&mut Command),
) -> (ObservedBuild, String) {
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
    // Environment, and arguments after the build's own.
    configure(&mut command);
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
    let execution = execution_report(project, home, id);
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

/// The execution report of one analysis session (one attempt of a build).
fn execution_report(project: &Path, home: &Path, id: &str) -> serde_json::Value {
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
    execution
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
fn remapped_semantic_flags_retain_independent_shared_slots() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    Package::new("slot_leaf", "1.0.0")
        .local(true)
        .file(
            "src/lib.rs",
            "pub const fn value() -> u32 { if cfg!(debug_assertions) { 11 } else { 22 } }\n",
        )
        .publish();
    Package::new("slot_middle", "1.0.0")
        .local(true)
        .dep("slot_leaf", "1.0.0")
        .file(
            "src/lib.rs",
            "pub const fn value() -> u32 { slot_leaf::value() }\n",
        )
        .publish();
    let first = keyed_project(&root, "assertions_on", "slot_middle");
    let second = keyed_project(&root, "assertions_off", "slot_middle");
    for (project, expected) in [(&first, 11), (&second, 22)] {
        // Trust: compilation itself checks the actual dependency's semantic value;
        // a Fresh report or a different directory cannot substitute for correct bytes.
        fs::write(
            project.join("src/lib.rs"),
            format!(
                "pub const ROOT: &str = env!(\"ROOT_ONLY\");\n\
                 const _: [(); {expected}] = [(); slot_middle::value() as usize];\n\
                 pub fn value() -> u32 {{ slot_middle::value() }}\n"
            ),
        )
        .unwrap();
    }
    let build_variant = |project: &Path, enabled: bool| {
        observe_with(project, &home, false, |command| {
            command.env(
                "RUSTFLAGS",
                format!(
                    "--remap-path-prefix={}=/fixture -Cdebug-assertions={}",
                    root.display(),
                    if enabled { "yes" } else { "no" }
                ),
            );
            if let Some(sdk) = std::env::var_os("SDKROOT") {
                command.env("SDKROOT", sdk);
            }
        })
        .0
    };
    let a = build_variant(&first, true);
    let b = build_variant(&second, false);
    for name in ["slot_leaf", "slot_middle"] {
        assert_eq!(compiler_processes(&a, name), 1);
        assert_eq!(compiler_processes(&b, name), 1);
        let (left, right) = (rlib(&a, name), rlib(&b, name));
        assert_ne!(left.parent(), right.parent());
        assert_eq!(
            left.file_name(),
            right.file_name(),
            "reproducible metadata changed"
        );
        assert_ne!(fs::read(&left).unwrap(), fs::read(&right).unwrap());
    }
    // Trust: alternate back to both producers. Neither may evict the other's
    // leaf or downstream shared unit, even though their artifact names agree.
    for (project, enabled, original) in [(&first, true, &a), (&second, false, &b)] {
        let warm = build_variant(project, enabled);
        for name in ["slot_leaf", "slot_middle"] {
            assert_eq!(shared_status(&warm, name), "eligible");
            assert_eq!(dependency(&warm, name)["fresh"], true);
            assert_eq!(compiler_processes(&warm, name), 0);
            assert_eq!(rlib(&warm, name), rlib(original, name));
        }
    }
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

/// DC-17a: a repository checks the key in under `[build]` in its
/// `.cargo/config.toml`, and a native `targo --unverified build` with no `-Z`
/// flag on its command line shares the eligible dependency: the second project
/// compiles nothing for it and links the store's archive. A project without
/// the key keeps its own private compilation of the same dependency.
#[cargo_test]
fn cache_key_shares_without_an_unstable_flag() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    Package::new("checked_in_leaf", "1.0.0")
        .local(true)
        .file("src/lib.rs", "pub fn value() -> u32 { 42 }\n")
        .publish();
    let store = home.join(".cargo/trust/native-dependencies-v1");
    let plain_build = |project: &Path| -> serde_json::Value {
        let output = targo(project, &home)
            .args([
                "--unverified",
                "build",
                "--offline",
                "--lib",
                "--message-format=json",
            ])
            .output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "{stderr}");
        String::from_utf8(output.stdout)
            .unwrap()
            .lines()
            .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
            .find(|row| {
                row["reason"] == "compiler-artifact" && row["target"]["name"] == "checked_in_leaf"
            })
            .unwrap()
    };
    let archive = |row: &serde_json::Value| -> PathBuf {
        row["filenames"]
            .as_array()
            .unwrap()
            .iter()
            .filter_map(serde_json::Value::as_str)
            .find(|path| path.ends_with(".rlib"))
            .map(PathBuf::from)
            .unwrap()
    };
    let checked_in = |name: &str| keyed_project(&root, name, "checked_in_leaf");

    let private = project(&root, "unkeyed", "checked_in_leaf");
    let unkeyed = plain_build(&private);
    assert_eq!(unkeyed["fresh"], false);
    assert!(archive(&unkeyed).starts_with(private.join("target")));
    assert!(!store.exists(), "a build without the key touched the store");
    assert_eq!(
        unit_locks(&private),
        0,
        "no -Z flag asked for fine-grain locking"
    );

    let first = checked_in("first");
    let cold = plain_build(&first);
    assert_eq!(cold["fresh"], false);
    assert!(archive(&cold).starts_with(&store), "{cold}");
    assert!(
        unit_locks(&first) > 0,
        "the key turns on the fine-grain locking its store needs"
    );

    let second = checked_in("second");
    let warm = plain_build(&second);
    assert_eq!(
        warm["fresh"], true,
        "the second project recompiled the dependency the first one shared"
    );
    assert_eq!(archive(&warm), archive(&cold));
}

/// DC-17a: a compiler wrapper is a lane where the key does not apply. A keyed
/// project built under `RUSTC_WRAPPER`, or under `RUSTC_WORKSPACE_WRAPPER` (the
/// one `targo tippy` sets), builds as with the key unset: its dependency
/// compiles privately, no store exists afterwards, and no per-unit lock shows
/// fine-grain locking. The build succeeds, where before it was refused.
#[cargo_test]
fn wrapped_keyed_builds_run_as_with_the_key_unset() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    Package::new("wrapped_leaf", "1.0.0")
        .local(true)
        .file("src/lib.rs", "pub fn value() -> u32 { 7 }\n")
        .publish();
    let store = home.join(".cargo/trust/native-dependencies-v1");
    for wrapper in ["RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER"] {
        let path = keyed_project(&root, &wrapper.to_lowercase(), "wrapped_leaf");
        let output = targo(&path, &home)
            .env(wrapper, "/usr/bin/env")
            .args([
                "--unverified",
                "build",
                "--offline",
                "--lib",
                "--message-format=json",
            ])
            .output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "{wrapper}: {stderr}");
        let leaf = String::from_utf8(output.stdout)
            .unwrap()
            .lines()
            .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
            .find(|row| {
                row["reason"] == "compiler-artifact" && row["target"]["name"] == "wrapped_leaf"
            })
            .unwrap();
        assert_eq!(leaf["fresh"], false, "{wrapper}");
        assert!(
            leaf["filenames"]
                .as_array()
                .unwrap()
                .iter()
                .filter_map(serde_json::Value::as_str)
                .all(|file| Path::new(file).starts_with(path.join("target"))),
            "{wrapper}: {leaf}"
        );
        assert!(
            !store.exists(),
            "{wrapper}: a wrapped build touched the store"
        );
        assert_eq!(
            unit_locks(&path),
            0,
            "{wrapper}: the key turned fine-grain locking on"
        );
    }
}

/// DC-17a: `targo trust`'s trust-cg preflight is a plan-only unverified child
/// that resolves the verified build's graph, and a plan-only build applies the
/// key. The preflight passes `--config build.shared-dependency-cache=false`
/// last (targo-trust's
/// `trust_cg_preflight_runs_as_with_the_shared_dependency_cache_key_unset`), and
/// a keyed project's store stays absent under it. Without that option the same
/// plan creates the store, so the option is what keeps it out.
#[cargo_test]
fn the_trust_preflight_override_leaves_the_store_untouched() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    Package::new("planned_leaf", "1.0.0")
        .local(true)
        .file("src/lib.rs", "pub fn value() -> u32 { 9 }\n")
        .publish();
    let store = home.join(".cargo/trust/native-dependencies-v1");
    let path = keyed_project(&root, "planned", "planned_leaf");
    let plan = |extra: &[&str]| {
        let output = targo(&path, &home)
            .args([
                "--unverified",
                "-Z",
                "unstable-options",
                "build",
                "--offline",
                "--lib",
            ])
            .args([
                "--unit-graph",
                "--config",
                "build.shared-dependency-cache=true",
            ])
            .args(extra)
            .output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "{stderr}");
    };

    plan(&["--config", "build.shared-dependency-cache=false"]);
    assert!(
        !store.exists(),
        "the preflight's override left the key applied"
    );

    plan(&[]);
    assert!(
        store.is_dir(),
        "a keyed plan-only build no longer applies the key"
    );
}

/// DC-24a: the variable that names a unit source.
const UNIT_SOURCE: &str = "TRUST_TARGO_UNIT_SOURCE";

/// DC-24a: what a unit source holds for `name`, as another machine with the
/// same cargo home path would: `producer` builds the unit into the store, its
/// directory's `fingerprint/` and `out/` are copied out, and the store's copy
/// is removed, so the consumer's build misses it. Returns the held copy and
/// the unit's directory in the store.
fn hold(
    root: &Path,
    home: &Path,
    producer: &Path,
    name: &str,
    configure: impl FnOnce(&mut Command),
) -> (PathBuf, PathBuf) {
    let produced = observe_with(producer, home, false, configure).0;
    assert_eq!(compiler_processes(&produced, name), 1);
    let archive = dependency(&produced, name)["filenames"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(serde_json::Value::as_str)
        .find(|path| path.ends_with(".rlib"))
        .map(PathBuf::from)
        .unwrap();
    let unit = archive.parent().unwrap().parent().unwrap().to_path_buf();
    assert!(unit.starts_with(home.join(".cargo/trust/native-dependencies-v1/build")));
    let held = root.join(format!("held-{name}"));
    for folder in ["fingerprint", "out"] {
        fs::create_dir_all(held.join(folder)).unwrap();
        for entry in fs::read_dir(unit.join(folder)).unwrap() {
            let entry = entry.unwrap();
            if entry.file_type().unwrap().is_file() {
                fs::copy(entry.path(), held.join(folder).join(entry.file_name())).unwrap();
            }
        }
    }
    fs::remove_dir_all(&unit).unwrap();
    (held, unit)
}

/// DC-24a: a stand-in unit source. It logs its process when it starts, and
/// for every ask logs the line it was sent, stages everything it holds in the
/// folder the line names read-only (as a content-addressed cache keeps its
/// files), and answers `staged`.
fn stand_in(root: &Path, held: &Path) -> (PathBuf, PathBuf) {
    let program = root.join("unit-source");
    let log = root.join("unit-source.log");
    fs::write(
        &program,
        format!(
            "#!/bin/sh\n\
             echo $$ >> '{started}'\n\
             while IFS= read -r line; do\n\
             printf '%s\\n' \"$line\" >> '{log}'\n\
             staging=$(printf '%s\\n' \"$line\" | sed -e 's/.*\"staging\":\"//' -e 's/\".*//')\n\
             cp -Rp '{held}'/. \"$staging\"/ || exit 1\n\
             find \"$staging\" -type f -exec chmod 0444 {{}} + || exit 1\n\
             echo staged\n\
             done\n",
            started = started(root).display(),
            log = log.display(),
            held = held.display(),
        ),
    )
    .unwrap();
    use std::os::unix::fs::PermissionsExt;
    fs::set_permissions(&program, fs::Permissions::from_mode(0o755)).unwrap();
    (program, log)
}

/// Where the stand-in logs each process of it that starts.
fn started(root: &Path) -> PathBuf {
    root.join("unit-source.started")
}

/// How many processes of the stand-in started.
fn starts(root: &Path) -> usize {
    fs::read_to_string(started(root))
        .unwrap_or_default()
        .lines()
        .count()
}

/// The keys the stand-in was asked for, in order.
fn asked(log: &Path) -> Vec<String> {
    fs::read_to_string(log)
        .unwrap_or_default()
        .lines()
        .map(|line| {
            let ask: serde_json::Value = serde_json::from_str(line).unwrap();
            assert_eq!(ask["version"], 1, "{line}");
            ask["key"].as_str().unwrap().to_owned()
        })
        .collect()
}

/// The key of a held unit: the SHA-256 of its fingerprint record.
fn held_key(held: &Path, name: &str) -> String {
    let mut hash = cargo_util::Sha256::new();
    hash.update(&fs::read(held.join(format!("fingerprint/lib-{name}.json"))).unwrap());
    hash.finish_hex()
}

fn unit_source<'a>(build: &'a ObservedBuild, name: &str) -> &'a serde_json::Value {
    let units: Vec<_> = build.execution["units"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|unit| unit["target"]["name"] == name && unit["target"]["kind"] == "lib")
        .collect();
    assert_eq!(units.len(), 1);
    &units[0]["unit_source"]
}

fn rlib(build: &ObservedBuild, name: &str) -> PathBuf {
    dependency(build, name)["filenames"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(serde_json::Value::as_str)
        .find(|path| path.ends_with(".rlib"))
        .map(PathBuf::from)
        .unwrap()
}

/// DC-24a: a unit a source stages whose fingerprint record is the one this
/// build computes is taken: the source was asked for exactly that key, the
/// unit starts no compiler, and the store now holds the staged archive.
/// Without the ask the unit compiles (one process), and the stand-in's log is
/// empty.
#[cargo_test]
fn unit_source_staged_unit_with_the_computed_fingerprint_starts_no_compiler() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    Package::new("held_leaf", "1.0.0")
        .local(true)
        .file("src/lib.rs", "pub fn value() -> u32 { 42 }\n")
        .publish();
    let producer = project(&root, "producer", "held_leaf");
    let (held, unit) = hold(&root, &home, &producer, "held_leaf", |_| {});
    let (source, log) = stand_in(&root, &held);
    let consumer = project(&root, "consumer", "held_leaf");
    let consumed = observe_with(&consumer, &home, false, |command| {
        command.env(UNIT_SOURCE, &source);
    })
    .0;
    assert_eq!(asked(&log), [held_key(&held, "held_leaf")]);
    assert_eq!(starts(&root), 1, "one source process per build");
    assert_eq!(
        unit_source(&consumed, "held_leaf"),
        &serde_json::json!({"status": "taken"})
    );
    assert_eq!(compiler_processes(&consumed, "held_leaf"), 0);
    let archive = rlib(&consumed, "held_leaf");
    assert!(archive.starts_with(&unit), "{}", archive.display());
    assert_eq!(
        fs::read(&archive).unwrap(),
        fs::read(held.join("out").join(archive.file_name().unwrap())).unwrap()
    );
    // Staged read-only, placed with the store's mode.
    use std::os::unix::fs::PermissionsExt;
    assert_eq!(
        fs::metadata(&archive).unwrap().permissions().mode() & 0o777,
        0o644
    );
    // The build's staging folder is emptied when it ends.
    let staging = home.join(".cargo/trust/native-dependencies-v1/staging");
    assert_eq!(fs::read_dir(&staging).unwrap().count(), 0);
}

/// DC-24a: the held unit was built with another LANG, which is in the keyed
/// environment but not in the unit's file names, so the stand-in's files land
/// on exactly the names this build plans. The source is asked for this
/// build's key, which is not the held record's, and the build refuses what it
/// staged and compiles the unit itself.
#[cargo_test]
fn unit_source_staged_unit_recorded_for_other_inputs_is_compiled() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    Package::new("held_leaf", "1.0.0")
        .local(true)
        .file("src/lib.rs", "pub fn value() -> u32 { 42 }\n")
        .publish();
    let producer = project(&root, "producer", "held_leaf");
    let (held, unit) = hold(&root, &home, &producer, "held_leaf", |command| {
        command.env("LANG", "fr_FR.UTF-8");
    });
    let (source, log) = stand_in(&root, &held);
    let consumer = project(&root, "consumer", "held_leaf");
    let consumed = observe_with(&consumer, &home, false, |command| {
        command.env(UNIT_SOURCE, &source).env("LANG", "en_US.UTF-8");
    })
    .0;
    let keys = asked(&log);
    assert_eq!(keys.len(), 1, "{keys:?}");
    assert_eq!(starts(&root), 1, "one source process per build");
    assert_ne!(keys[0], held_key(&held, "held_leaf"));
    assert_eq!(
        unit_source(&consumed, "held_leaf"),
        &serde_json::json!({"status": "refused", "reason": "fingerprint-differs"})
    );
    assert_eq!(compiler_processes(&consumed, "held_leaf"), 1);
    let archive = rlib(&consumed, "held_leaf");
    assert!(archive.starts_with(&unit), "{}", archive.display());
    assert!(
        held.join("out")
            .join(archive.file_name().unwrap())
            .is_file(),
        "the held unit's file names are the ones this build plans"
    );
    // The key the source was asked for is the record the build published.
    assert_eq!(
        keys[0],
        held_key(&unit, "held_leaf"),
        "the asked key is not this build's fingerprint record"
    );
}

/// DC-24a: the held unit's fingerprint record is this build's, but its
/// archive's bytes no longer match the receipt recorded with it. The build
/// places it, its check under the lock fails the receipt, and it refuses the
/// unit and compiles it, replacing the damaged archive.
#[cargo_test]
fn unit_source_staged_unit_whose_bytes_differ_from_its_receipt_is_compiled() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    Package::new("held_leaf", "1.0.0")
        .local(true)
        .file("src/lib.rs", "pub fn value() -> u32 { 42 }\n")
        .publish();
    let producer = project(&root, "producer", "held_leaf");
    let (held, unit) = hold(&root, &home, &producer, "held_leaf", |_| {});
    let damaged = fs::read_dir(held.join("out"))
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .find(|path| {
            path.extension()
                .is_some_and(|extension| extension == "rlib")
        })
        .unwrap();
    let mut bytes = fs::read(&damaged).unwrap();
    bytes[..8].copy_from_slice(b"BROKEN!!");
    fs::write(&damaged, bytes).unwrap();
    let (source, log) = stand_in(&root, &held);
    let consumer = project(&root, "consumer", "held_leaf");
    let consumed = observe_with(&consumer, &home, false, |command| {
        command.env(UNIT_SOURCE, &source);
    })
    .0;
    assert_eq!(asked(&log), [held_key(&held, "held_leaf")]);
    assert_eq!(starts(&root), 1, "one source process per build");
    assert_eq!(
        unit_source(&consumed, "held_leaf"),
        &serde_json::json!({"status": "refused", "reason": "output-integrity"})
    );
    assert_eq!(compiler_processes(&consumed, "held_leaf"), 1);
    let archive = rlib(&consumed, "held_leaf");
    assert!(archive.starts_with(&unit), "{}", archive.display());
    assert!(fs::read(&archive).unwrap().starts_with(b"!<arch>\n"));
}

/// DC-18b: a virtual workspace whose members `leaf` and `mid` (which depends
/// on `leaf`) are plain libraries: no build script, no proc macro. `extra`
/// names more members, each `(name, lib.rs)`; it is a member like the others.
fn member_workspace(root: &Path, name: &str, extra: &[(&str, &str, &[&str])]) -> PathBuf {
    let path = root.join(name);
    let mut members = vec![
        ("leaf", "pub fn value() -> u32 { 42 }\n", &[][..]),
        (
            "mid",
            "pub fn value() -> u32 { leaf::value() + 1 }\n",
            &["leaf"][..],
        ),
    ];
    members.extend_from_slice(extra);
    for (member, source, dependencies) in &members {
        let crate_dir = path.join("crates").join(member);
        fs::create_dir_all(crate_dir.join("src")).unwrap();
        let mut manifest = format!(
            "[package]\nname={member:?}\nversion='0.1.0'\nedition='2021'\n[dependencies]\n"
        );
        for dependency in *dependencies {
            manifest.push_str(&format!("{dependency}={{path='../{dependency}'}}\n"));
        }
        fs::write(crate_dir.join("Cargo.toml"), manifest).unwrap();
        fs::write(crate_dir.join("src/lib.rs"), source).unwrap();
    }
    fs::write(
        path.join("Cargo.toml"),
        "[workspace]\nmembers=['crates/*']\nresolver='2'\n",
    )
    .unwrap();
    path
}

/// DC-18b: the slots the store holds for a member package.
fn member_slots(home: &Path, member: &str) -> Vec<PathBuf> {
    let dir = home.join(format!(
        ".cargo/trust/native-dependencies-v1/build/members/{member}"
    ));
    let Ok(entries) = fs::read_dir(dir) else {
        return Vec::new();
    };
    let mut slots: Vec<_> = entries.map(|entry| entry.unwrap().path()).collect();
    slots.sort();
    slots
}

/// DC-18b: a member's archive in one store slot.
fn slot_archive(slot: &Path, member: &str) -> PathBuf {
    fs::read_dir(slot.join("out"))
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .find(|path| {
            let name = path.file_name().unwrap().to_str().unwrap();
            name.starts_with(&format!("lib{member}-")) && name.ends_with(".rlib")
        })
        .unwrap()
}

/// DC-18b: every regular file below `dir` whose name starts with `prefix`.
fn files_named(dir: &Path, prefix: &str) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let mut pending = vec![dir.to_path_buf()];
    while let Some(dir) = pending.pop() {
        let Ok(entries) = fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries {
            let path = entry.unwrap().path();
            let metadata = fs::symlink_metadata(&path).unwrap();
            if metadata.is_dir() {
                pending.push(path);
            } else if metadata.is_file()
                && path
                    .file_name()
                    .unwrap()
                    .to_str()
                    .unwrap()
                    .starts_with(prefix)
            {
                found.push(path);
            }
        }
    }
    found
}

fn sha256(path: &Path) -> String {
    let mut hash = cargo_util::Sha256::new();
    hash.update(&fs::read(path).unwrap());
    hash.finish_hex()
}

/// DC-18b: a second checkout of the same workspace compiles nothing for its
/// members' libraries: the first checkout compiled each once, path-free, into
/// one store slot, and the second reads them there in place. Its build
/// directory holds no unit of theirs: only the uplift of the requested
/// library, whose bytes are the store's archive, and its dep-info.
#[cargo_test]
fn member_units_of_a_second_checkout_start_no_compiler() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    let first = member_workspace(&root, "first", &[]);
    let second = member_workspace(&root, "second", &[]);
    let cold = build(&first, &home);
    for member in ["leaf", "mid"] {
        assert_eq!(shared_status(&cold, member), "eligible", "{member}");
        assert_eq!(compiler_processes(&cold, member), 1, "{member}");
        assert_eq!(member_slots(&home, member).len(), 1, "{member}");
    }
    let warm = build(&second, &home);
    for member in ["leaf", "mid"] {
        assert_eq!(shared_status(&warm, member), "eligible", "{member}");
        assert_eq!(
            compiler_processes(&warm, member),
            0,
            "the second checkout compiled `{member}`"
        );
        assert_eq!(dependency(&warm, member)["fresh"], true, "{member}");
        let slots = member_slots(&home, member);
        assert_eq!(slots.len(), 1, "{member}: {slots:?}");
        // No file of the slot names either checkout.
        for file in files_named(&slots[0], "") {
            let bytes = fs::read(&file).unwrap();
            for checkout in [&first, &second] {
                for spelling in [checkout.clone(), checkout.canonicalize().unwrap()] {
                    let spelling = spelling.to_str().unwrap().as_bytes();
                    assert!(
                        !bytes
                            .windows(spelling.len())
                            .any(|window| window == spelling),
                        "{} names {}",
                        file.display(),
                        checkout.display()
                    );
                }
            }
        }
        let archive = slot_archive(&slots[0], member);
        let uplifted = format!("lib{member}.rlib");
        for copy in files_named(&second.join("target"), &format!("lib{member}")) {
            if copy.file_name().unwrap() == uplifted.as_str() {
                // The requested library's uplift is the store's archive.
                assert_eq!(
                    fs::read(&copy).unwrap(),
                    fs::read(&archive).unwrap(),
                    "{} is not {}",
                    copy.display(),
                    archive.display()
                );
            } else {
                assert!(
                    copy.extension().is_some_and(|extension| extension == "d"),
                    "the second checkout holds {}",
                    copy.display()
                );
            }
        }
    }
}

/// DC-18b: a member that reads its own directory through
/// `env!("CARGO_MANIFEST_DIR")` needs its real path. The compiler refuses its
/// path-free metadata, and the build, which succeeds, compiles it privately
/// in the checkout's build directory with the path written as it is; its
/// dependent compiles privately too, and the store holds no slot of either.
/// The checkout records the refusal, so its next build excludes the member
/// as path-bound and compiles nothing.
#[cargo_test]
fn member_unit_with_a_manifest_dir_literal_stays_private() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    let workspace = member_workspace(
        &root,
        "located",
        &[
            (
                "located",
                "pub const DIR: &str = env!(\"CARGO_MANIFEST_DIR\");\n",
                &[],
            ),
            (
                "user",
                "pub fn dir() -> &'static str { located::DIR }\n",
                &["located"],
            ),
        ],
    );
    let output = targo(&workspace, &home)
        .args([
            "--unverified",
            "build",
            "--offline",
            "--lib",
            "--config",
            "build.shared-dependency-cache=true",
            "--message-format=json",
        ])
        .output()
        .unwrap();
    let store = home.join(".cargo/trust/native-dependencies-v1");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stderr}");
    assert!(
        !stderr.contains("trust-path-free-v1"),
        "the refused attempt was reported: {stderr}"
    );
    let rows: Vec<serde_json::Value> = String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .filter_map(|line| serde_json::from_str(line).ok())
        .collect();
    let finished: Vec<_> = rows
        .iter()
        .filter(|row| row["reason"] == "build-finished")
        .collect();
    assert_eq!(finished.len(), 1, "{finished:?}");
    assert_eq!(finished[0]["success"], true);
    for member in ["located", "user"] {
        let artifact = rows
            .iter()
            .find(|row| row["reason"] == "compiler-artifact" && row["target"]["name"] == member)
            .unwrap_or_else(|| panic!("no artifact for {member}: {rows:?}"));
        assert_eq!(artifact["fresh"], false, "{member}");
        assert!(
            files_named(&store, &format!("lib{member}-")).is_empty(),
            "the store holds a unit of `{member}`"
        );
        assert!(
            !files_named(&workspace.join("target"), &format!("lib{member}-")).is_empty(),
            "`{member}` was not compiled in the checkout"
        );
    }
    // The private metadata holds the member's real directory, as it does today.
    let archive = files_named(&workspace.join("target"), "liblocated-")
        .into_iter()
        .find(|path| {
            path.extension()
                .is_some_and(|extension| extension == "rmeta")
        })
        .unwrap();
    let real = workspace.join("crates/located");
    let real = real.to_str().unwrap().as_bytes();
    assert!(
        fs::read(&archive)
            .unwrap()
            .windows(real.len())
            .any(|window| window == real),
        "the private metadata lost its real path"
    );
    // The plain members are still shared.
    for member in ["leaf", "mid"] {
        assert_eq!(member_slots(&home, member).len(), 1, "{member}");
    }

    let again = build(&workspace, &home);
    for member in ["located", "user"] {
        assert_eq!(compiler_processes(&again, member), 0, "{member}");
    }
    let located = again.execution["units"]
        .as_array()
        .unwrap()
        .iter()
        .find(|unit| unit["target"]["name"] == "located" && unit["target"]["kind"] == "lib")
        .unwrap();
    assert_eq!(
        located["shared_dependency"],
        serde_json::json!({"status": "excluded", "reason": "path-bound"})
    );
    assert!(files_named(&store, "liblocated-").is_empty());
}

/// DC-18b: a dependent is keyed on the bytes it consumed. Two checkouts whose
/// `leaf` differs build two `leaf`s, so each checkout's `mid`, from the same
/// source, is compiled against its own `leaf` into its own slot, and records
/// the SHA-256 of the `leaf` it read. Neither checkout's `mid` is ever taken
/// with the other's `leaf`: both rebuild nothing afterwards, in either order.
#[cargo_test]
fn member_unit_dependent_never_mixes_two_builds() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    let first = member_workspace(&root, "first", &[]);
    let second = member_workspace(&root, "second", &[]);
    fs::write(
        second.join("crates/leaf/src/lib.rs"),
        "pub fn value() -> u32 { 7 }\n",
    )
    .unwrap();
    let a = build(&first, &home);
    let b = build(&second, &home);
    for member in ["leaf", "mid"] {
        assert_eq!(compiler_processes(&a, member), 1, "{member}");
        assert_eq!(compiler_processes(&b, member), 1, "{member}");
        assert_eq!(shared_status(&b, member), "eligible", "{member}");
        assert_eq!(
            member_slots(&home, member).len(),
            2,
            "two builds of `{member}` share one slot"
        );
    }
    // Each `mid` names the bytes of the `leaf` it consumed, and they are the
    // bytes of a `leaf` slot, a different one for each.
    let mut consumed = Vec::new();
    for slot in member_slots(&home, "mid") {
        let record = fs::read_to_string(slot.join("fingerprint/lib-mid.externs")).unwrap();
        let lines: Vec<_> = record.lines().collect();
        assert_eq!(lines.len(), 1, "{record}");
        let (checksum, path) = lines[0].split_once(' ').unwrap();
        let file = home.join(".cargo/trust/native-dependencies-v1").join(path);
        assert_eq!(checksum, format!("sha256={}", sha256(&file)), "{record}");
        consumed.push(file);
    }
    assert_ne!(consumed[0].parent(), consumed[1].parent());
    for (project, name) in [(&first, "first"), (&second, "second"), (&first, "first")] {
        let again = build(project, &home);
        for member in ["leaf", "mid"] {
            assert_eq!(
                compiler_processes(&again, member),
                0,
                "{name} rebuilt `{member}`"
            );
        }
    }
    for member in ["leaf", "mid"] {
        assert_eq!(member_slots(&home, member).len(), 2, "{member}");
    }
}

/// DC-18b: an edit in one checkout is rebuilt in that checkout only. Two
/// checkouts share `leaf` and `mid`; one edits `leaf` (same size, its mtime
/// kept). That checkout compiles `leaf` and `mid` into new slots; the other
/// compiles nothing and its slots keep their bytes. When the edit is undone,
/// the editing checkout is back on the first slots and compiles nothing.
#[cargo_test]
fn member_unit_edited_in_one_checkout_is_rebuilt_there_only() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    let first = member_workspace(&root, "first", &[]);
    let second = member_workspace(&root, "second", &[]);
    build(&first, &home);
    let shared = build(&second, &home);
    assert_eq!(compiler_processes(&shared, "leaf"), 0);
    let original: Vec<_> = ["leaf", "mid"]
        .iter()
        .map(|member| {
            let slots = member_slots(&home, member);
            assert_eq!(slots.len(), 1, "{member}");
            let archive = slot_archive(&slots[0], member);
            (archive.clone(), sha256(&archive))
        })
        .collect();

    let source = second.join("crates/leaf/src/lib.rs");
    let stamp = filetime::FileTime::from_last_modification_time(&fs::metadata(&source).unwrap());
    let before = fs::read_to_string(&source).unwrap();
    fs::write(&source, before.replace("42", "43")).unwrap();
    filetime::set_file_mtime(&source, stamp).unwrap();
    let edited = build(&second, &home);
    for member in ["leaf", "mid"] {
        assert_eq!(compiler_processes(&edited, member), 1, "{member}");
        assert_eq!(shared_status(&edited, member), "eligible", "{member}");
        assert_eq!(member_slots(&home, member).len(), 2, "{member}");
    }
    let untouched = build(&first, &home);
    for (member, (archive, digest)) in ["leaf", "mid"].iter().zip(&original) {
        assert_eq!(
            compiler_processes(&untouched, member),
            0,
            "the other checkout rebuilt `{member}`"
        );
        assert_eq!(&sha256(archive), digest, "{member}'s first slot changed");
    }

    fs::write(&source, before).unwrap();
    filetime::set_file_mtime(&source, stamp).unwrap();
    let undone = build(&second, &home);
    for member in ["leaf", "mid"] {
        assert_eq!(compiler_processes(&undone, member), 0, "{member}");
    }
}

/// DC-18b: a shared member's compiler does not see an ambient deployment
/// target, so a checkout built with `MACOSX_DEPLOYMENT_TARGET` set reads the
/// same slots as one built without it, compiles nothing, and the archive's
/// bytes are what they were.
#[cargo_test]
fn member_unit_ignores_an_ambient_deployment_target() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    let first = member_workspace(&root, "first", &[]);
    let second = member_workspace(&root, "second", &[]);
    build(&first, &home);
    let slots = member_slots(&home, "leaf");
    assert_eq!(slots.len(), 1);
    let archive = slot_archive(&slots[0], "leaf");
    let digest = sha256(&archive);
    let (targeted, _) = observe_with(&second, &home, false, |command| {
        command.env("MACOSX_DEPLOYMENT_TARGET", "14.0");
    });
    for member in ["leaf", "mid"] {
        assert_eq!(
            compiler_processes(&targeted, member),
            0,
            "an ambient deployment target recompiled `{member}`"
        );
        assert_eq!(member_slots(&home, member).len(), 1, "{member}");
    }
    assert_eq!(sha256(&archive), digest);
}

/// DC-18b: a member unit's whole shared-dependency decision.
fn shared_decision<'a>(build: &'a ObservedBuild, name: &str) -> &'a serde_json::Value {
    build.execution["units"]
        .as_array()
        .unwrap()
        .iter()
        .find(|unit| unit["target"]["name"] == name && unit["target"]["kind"] == "lib")
        .map(|unit| &unit["shared_dependency"])
        .unwrap()
}

fn excluded(reason: &str) -> serde_json::Value {
    serde_json::json!({"status": "excluded", "reason": reason})
}

/// DC-18b: a member whose package tree holds a link (a `LICENSE` linked to
/// the workspace's, as many repositories do) cannot be captured, so it is
/// compiled privately; the build succeeds and the plain members are shared.
#[cargo_test]
fn shared_member_holding_a_symlinked_license_stays_private() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    let workspace = member_workspace(
        &root,
        "linked",
        &[("linked", "pub fn value() -> u32 { 1 }\n", &[])],
    );
    fs::write(workspace.join("LICENSE"), "MIT\n").unwrap();
    std::os::unix::fs::symlink("../../LICENSE", workspace.join("crates/linked/LICENSE")).unwrap();
    let built = build(&workspace, &home);
    assert_eq!(
        shared_decision(&built, "linked"),
        &excluded("member-source-uncaptured")
    );
    assert_eq!(compiler_processes(&built, "linked"), 1);
    assert!(member_slots(&home, "linked").is_empty());
    for member in ["leaf", "mid"] {
        assert_eq!(shared_status(&built, member), "eligible", "{member}");
        assert_eq!(member_slots(&home, member).len(), 1, "{member}");
    }
}

/// DC-18b: a member that includes a file outside its package (the
/// workspace's README) cannot read it inside its confinement. Its shared
/// compile fails unseen, the build is planned again with it (and its
/// dependent) private, and succeeds, reporting no error. The checkout records
/// the failure, so its next build plans the member private at once and
/// compiles nothing; the store holds no unit of either.
#[cargo_test]
fn shared_member_reading_a_workspace_file_compiles_privately() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    let workspace = member_workspace(
        &root,
        "documented",
        &[
            (
                "documented",
                "#![doc = include_str!(\"../../../README.md\")]\npub fn value() -> u32 { 2 }\n",
                &[],
            ),
            (
                "reader",
                "pub fn value() -> u32 { documented::value() }\n",
                &["documented"],
            ),
        ],
    );
    fs::write(workspace.join("README.md"), "The workspace.\n").unwrap();
    let output = targo(&workspace, &home)
        .args([
            "--unverified",
            "build",
            "--offline",
            "--lib",
            "--config",
            "build.shared-dependency-cache=true",
            "--message-format=json",
        ])
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stderr}");
    let rows: Vec<serde_json::Value> = String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .filter_map(|line| serde_json::from_str(line).ok())
        .collect();
    assert!(
        !rows
            .iter()
            .any(|row| row["reason"] == "compiler-message" && row["message"]["level"] == "error"),
        "the refused attempt was reported: {rows:?}"
    );
    let finished: Vec<_> = rows
        .iter()
        .filter(|row| row["reason"] == "build-finished")
        .collect();
    assert_eq!(finished.len(), 1, "{finished:?}");
    assert_eq!(finished[0]["success"], true);
    let store = home.join(".cargo/trust/native-dependencies-v1");
    for member in ["documented", "reader"] {
        assert!(
            files_named(&store, &format!("lib{member}-")).is_empty(),
            "the store holds a unit of `{member}`"
        );
        assert!(
            !files_named(&workspace.join("target"), &format!("lib{member}-")).is_empty(),
            "`{member}` was not compiled in the checkout"
        );
    }
    for member in ["leaf", "mid"] {
        assert_eq!(member_slots(&home, member).len(), 1, "{member}");
    }
    let again = build(&workspace, &home);
    for member in ["documented", "reader"] {
        assert_eq!(compiler_processes(&again, member), 0, "{member}");
    }
    assert_eq!(
        shared_decision(&again, "documented"),
        &excluded("member-compile-failed")
    );
}

/// DC-18b: a slot is named by the member's command, so the same member
/// built as a requested package (`targo build`) and as a dependency only
/// (`targo build -p mid`), whose commands differ, takes two slots, and each
/// build afterwards compiles nothing. No build is refused and planned again.
#[cargo_test]
fn shared_member_slot_holds_across_primary_and_dependency_builds() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    let workspace = member_workspace(&root, "alternating", &[]);
    let only_mid = |command: &mut Command| {
        command.args(["-p", "mid"]);
    };
    let all = build(&workspace, &home);
    let (mid, _) = observe_with(&workspace, &home, false, only_mid);
    for member in ["leaf", "mid"] {
        assert_eq!(compiler_processes(&all, member), 1, "{member}");
        assert_eq!(compiler_processes(&mid, member), 1, "{member}");
        assert_eq!(shared_status(&mid, member), "eligible", "{member}");
        assert_eq!(member_slots(&home, member).len(), 2, "{member}");
    }
    let all = build(&workspace, &home);
    let (mid, _) = observe_with(&workspace, &home, false, only_mid);
    for member in ["leaf", "mid"] {
        assert_eq!(compiler_processes(&all, member), 0, "{member}");
        assert_eq!(compiler_processes(&mid, member), 0, "{member}");
        assert_eq!(member_slots(&home, member).len(), 2, "{member}");
    }
}

/// DC-18b: a path remap of the caller's (here in `RUSTFLAGS`) names no
/// checkout in the command, yet could write one into the bytes, so no member
/// is shared under it.
#[cargo_test]
fn shared_member_under_a_caller_path_remap_stays_private() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    let workspace = member_workspace(&root, "remapped", &[]);
    let (built, _) = observe_with(&workspace, &home, false, |command| {
        command.env(
            "RUSTFLAGS",
            format!("--remap-path-prefix={}=~", root.display()),
        );
    });
    for member in ["leaf", "mid"] {
        assert_eq!(
            shared_decision(&built, member),
            &excluded("member-not-confined"),
            "{member}"
        );
        assert!(member_slots(&home, member).is_empty(), "{member}");
    }
}

/// DC-18b: only committed sources are shared. In a git work tree, a member
/// with an uncommitted edit is compiled privately (its dependent too), and
/// its committed slots stay as they were; once the edit is committed, both
/// are shared again from new slots.
#[cargo_test]
fn shared_member_with_uncommitted_changes_stays_private() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    let workspace = member_workspace(&root, "tracked", &[]);
    fs::write(workspace.join(".gitignore"), "/target\n").unwrap();
    let repository = git::init(&workspace);
    git::add(&repository);
    git::commit(&repository);
    let committed = build(&workspace, &home);
    for member in ["leaf", "mid"] {
        assert_eq!(shared_status(&committed, member), "eligible", "{member}");
        assert_eq!(member_slots(&home, member).len(), 1, "{member}");
    }
    fs::write(
        workspace.join("crates/leaf/src/lib.rs"),
        "pub fn value() -> u32 { 43 }\n",
    )
    .unwrap();
    let edited = build(&workspace, &home);
    assert_eq!(
        shared_decision(&edited, "leaf"),
        &excluded("member-uncommitted")
    );
    assert_eq!(shared_status(&edited, "mid"), "dependency-blocked");
    for member in ["leaf", "mid"] {
        assert_eq!(compiler_processes(&edited, member), 1, "{member}");
        assert_eq!(member_slots(&home, member).len(), 1, "{member}");
    }
    git::add(&repository);
    git::commit(&repository);
    let recommitted = build(&workspace, &home);
    for member in ["leaf", "mid"] {
        assert_eq!(shared_status(&recommitted, member), "eligible", "{member}");
        assert_eq!(compiler_processes(&recommitted, member), 1, "{member}");
        assert_eq!(member_slots(&home, member).len(), 2, "{member}");
    }
}

/// DC-18b: `targo fix` rewrites its packages' sources through a proxy
/// compiler, which no store slot may confine or stand in for: under the key
/// it succeeds and shares no member.
#[cargo_test]
fn shared_member_is_not_shared_under_fix() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    let workspace = member_workspace(&root, "fixed", &[]);
    let output = targo(&workspace, &home)
        .args([
            "--unverified",
            "fix",
            "--offline",
            "--lib",
            "--allow-no-vcs",
            "--config",
            "build.shared-dependency-cache=true",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    for member in ["leaf", "mid"] {
        assert!(member_slots(&home, member).is_empty(), "{member}");
    }
}

/// DC-18c: one build that may be planned more than once in its invocation:
/// a shared member keyed on a build script or proc macro that has not yet
/// run in its checkout waits for it, and the build is planned again once it
/// has. Each attempt's report and artifacts, in order; the last succeeded.
fn attempts(
    project: &Path,
    home: &Path,
    configure: impl FnOnce(&mut Command),
) -> Vec<ObservedBuild> {
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
    configure(&mut command);
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let mut sessions: Vec<(String, Vec<serde_json::Value>)> = Vec::new();
    let mut finished = Vec::new();
    for line in String::from_utf8(output.stdout).unwrap().lines() {
        let Ok(row) = serde_json::from_str::<serde_json::Value>(line) else {
            continue;
        };
        match row["reason"].as_str() {
            Some("build-analysis-session") => {
                sessions.push((row["run_id"].as_str().unwrap().to_owned(), Vec::new()))
            }
            Some("compiler-artifact") => sessions.last_mut().unwrap().1.push(row),
            Some("build-finished") => finished.push(row),
            _ => {}
        }
    }
    // Only the last attempt reports the build's end.
    assert_eq!(finished.len(), 1, "{finished:?}");
    assert_eq!(finished[0]["success"], true);
    let last = sessions.len() - 1;
    sessions
        .into_iter()
        .enumerate()
        .map(|(attempt, (id, artifacts))| {
            let execution = execution_report(project, home, &id);
            if attempt == last {
                assert_eq!(execution["graph_outcome"], "succeeded");
            }
            assert_eq!(
                execution["shared_dependency_frontier"]["availability"],
                "complete"
            );
            ObservedBuild {
                artifacts,
                execution,
            }
        })
        .collect()
}

/// DC-18c: compiler processes a library unit started over every attempt. An
/// attempt that was planned again stops at its refusal, so a compile that
/// started in it counts whether or not the report saw it finish.
fn compiled(attempts: &[ObservedBuild], name: &str) -> u64 {
    let (last, earlier) = attempts.split_last().unwrap();
    let started = |attempt: &ObservedBuild| -> u64 {
        let units: Vec<_> = attempt.execution["units"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|unit| unit["target"]["name"] == name && unit["target"]["kind"] == "lib")
            .collect();
        assert!(units.len() <= 1, "{name}: {}", attempt.execution);
        units
            .iter()
            .filter(|unit| !unit["process"]["command_started_seconds"].is_null())
            .count() as u64
    };
    earlier.iter().map(started).sum::<u64>() + compiler_processes(last, name)
}

/// DC-18c: the bytes of a file contain `text`.
fn holds(path: &Path, text: &str) -> bool {
    fs::read(path)
        .unwrap()
        .windows(text.len())
        .any(|window| window == text.as_bytes())
}

/// DC-18c: the requested library a checkout uplifted.
fn uplifted(project: &Path, member: &str) -> PathBuf {
    let name = format!("lib{member}.rlib");
    files_named(&project.join("target"), &name)
        .into_iter()
        .find(|path| path.file_name().unwrap() == name.as_str())
        .unwrap_or_else(|| panic!("{} has no {name}", project.display()))
}

/// DC-18c: a workspace whose member `scripted` has a build script, which
/// leaves a file in its `OUT_DIR` and prints a cfg and a `rustc-env` value
/// the library embeds (the value of `SCRIPTED_FLAVOR` where the build sets
/// it) in its code, and whose member `user` calls it.
fn scripted_workspace(root: &Path, name: &str) -> PathBuf {
    let workspace = member_workspace(
        root,
        name,
        &[
            (
                "scripted",
                "#[cfg(scripted)]\npub fn greeting() -> &'static str { env!(\"SCRIPTED_GREETING\") }\n\
                 pub fn value() -> u32 { leaf::value() }\n",
                &["leaf"],
            ),
            (
                "user",
                "pub fn greeting() -> &'static str { scripted::greeting() }\n",
                &["scripted"],
            ),
        ],
    );
    fs::write(
        workspace.join("crates/scripted/build.rs"),
        "fn main() {\n\
         let out = std::path::PathBuf::from(std::env::var_os(\"OUT_DIR\").unwrap());\n\
         std::fs::write(out.join(\"script-ran\"), b\"ran\").unwrap();\n\
         let flavor = std::env::var(\"SCRIPTED_FLAVOR\").unwrap_or_else(|_| \"plain\".into());\n\
         println!(\"cargo::rustc-check-cfg=cfg(scripted)\");\n\
         println!(\"cargo::rustc-cfg=scripted\");\n\
         println!(\"cargo::rustc-env=SCRIPTED_GREETING=greeting-{flavor}-flavor\");\n\
         println!(\"cargo::rerun-if-changed=build.rs\");\n\
         println!(\"cargo::rerun-if-env-changed=SCRIPTED_FLAVOR\");\n\
         }\n",
    )
    .unwrap();
    workspace
}

/// DC-18c: a member with a build script runs the script in every checkout,
/// as before, and shares its library, keyed on what the script printed and
/// left in its `OUT_DIR`. A second checkout at the same commit runs its own
/// script, which prints the same, and compiles neither that member nor the
/// member that depends on it: their slots, which name neither checkout, are
/// read in place, and the second checkout's requested library is their
/// bytes. Its next build plans once and compiles nothing.
#[cargo_test]
fn member_with_a_build_script_runs_it_locally_and_shares_its_library() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    let first = scripted_workspace(&root, "first");
    let second = scripted_workspace(&root, "second");
    let cold = attempts(&first, &home, |_| {});
    for member in ["scripted", "user"] {
        assert_eq!(compiled(&cold, member), 1, "{member}");
        assert_eq!(
            shared_status(cold.last().unwrap(), member),
            "eligible",
            "{member}"
        );
        assert_eq!(member_slots(&home, member).len(), 1, "{member}");
    }
    assert!(files_named(&second.join("target"), "script-ran").is_empty());
    let warm = attempts(&second, &home, |_| {});
    assert_eq!(
        files_named(&second.join("target"), "script-ran").len(),
        1,
        "the second checkout did not run its build script"
    );
    for member in ["scripted", "user"] {
        assert_eq!(
            compiled(&warm, member),
            0,
            "the second checkout compiled `{member}`"
        );
        assert_eq!(
            shared_status(warm.last().unwrap(), member),
            "eligible",
            "{member}"
        );
        let slots = member_slots(&home, member);
        assert_eq!(slots.len(), 1, "{member}: {slots:?}");
        for file in files_named(&slots[0], "") {
            for checkout in [&first, &second] {
                for spelling in [checkout.clone(), checkout.canonicalize().unwrap()] {
                    assert!(
                        !holds(&file, spelling.to_str().unwrap()),
                        "{} names {}",
                        file.display(),
                        checkout.display()
                    );
                }
            }
        }
        assert_eq!(
            fs::read(uplifted(&second, member)).unwrap(),
            fs::read(slot_archive(&slots[0], member)).unwrap(),
            "{member}"
        );
    }
    assert!(holds(
        &uplifted(&second, "scripted"),
        "greeting-plain-flavor"
    ));
    let again = attempts(&second, &home, |_| {});
    assert_eq!(again.len(), 1, "a built checkout planned its build again");
    for member in ["scripted", "user"] {
        assert_eq!(compiled(&again, member), 0, "{member}");
    }
}

/// DC-18c: two checkouts at one commit whose build scripts print different
/// directives (here a value from the environment the script reads) do not
/// share the member's library or its dependent's: each checkout compiles
/// them into its own slots, each library holds its own checkout's value, and
/// neither slot is written over. Each checkout then builds nothing.
#[cargo_test]
fn member_with_a_differing_script_output_is_not_shared() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    let first = scripted_workspace(&root, "first");
    let second = scripted_workspace(&root, "second");
    let flavored = |command: &mut Command| {
        command.env("SCRIPTED_FLAVOR", "other");
    };
    attempts(&first, &home, |_| {});
    let original: Vec<_> = ["scripted", "user"]
        .iter()
        .map(|member| {
            let slots = member_slots(&home, member);
            assert_eq!(slots.len(), 1, "{member}");
            sha256(&slot_archive(&slots[0], member))
        })
        .collect();
    let differing = attempts(&second, &home, flavored);
    for member in ["scripted", "user"] {
        assert_eq!(
            compiled(&differing, member),
            1,
            "`{member}` was taken from a slot another script output named"
        );
        assert_eq!(
            shared_status(differing.last().unwrap(), member),
            "eligible",
            "{member}"
        );
        assert_eq!(member_slots(&home, member).len(), 2, "{member}");
    }
    assert!(holds(
        &uplifted(&second, "scripted"),
        "greeting-other-flavor"
    ));
    assert!(!holds(
        &uplifted(&second, "scripted"),
        "greeting-plain-flavor"
    ));
    assert!(holds(
        &uplifted(&first, "scripted"),
        "greeting-plain-flavor"
    ));
    for (project, configure) in [(&first, None), (&second, Some(flavored)), (&first, None)] {
        let again = attempts(project, &home, |command| {
            if let Some(configure) = configure {
                configure(command);
            }
        });
        for member in ["scripted", "user"] {
            assert_eq!(compiled(&again, member), 0, "{member}");
        }
    }
    for (member, digest) in ["scripted", "user"].iter().zip(&original) {
        let slots = member_slots(&home, member);
        assert_eq!(slots.len(), 2, "{member}");
        assert!(
            slots
                .iter()
                .any(|slot| &sha256(&slot_archive(slot, member)) == digest),
            "the first checkout's `{member}` slot was written over"
        );
    }
    assert!(holds(
        &uplifted(&first, "scripted"),
        "greeting-plain-flavor"
    ));
}

/// DC-18c: a proc macro outside the workspaces, used by the member
/// `expanded`; its source is `answer` with the macro's output string.
fn write_macro(root: &Path, answer: &str) {
    let path = root.join("macros");
    fs::create_dir_all(path.join("src")).unwrap();
    fs::write(
        path.join("Cargo.toml"),
        "[package]\nname='macros'\nversion='0.1.0'\nedition='2021'\n[lib]\nproc-macro=true\n",
    )
    .unwrap();
    fs::write(
        path.join("src/lib.rs"),
        format!(
            "use proc_macro::TokenStream;\n\
             #[proc_macro]\n\
             pub fn answer(_: TokenStream) -> TokenStream {{\n\
             \"pub fn answer() -> &'static str {{ \\\"{answer}\\\" }}\".parse().unwrap()\n\
             }}\n"
        ),
    )
    .unwrap();
}

fn macro_workspace(root: &Path, name: &str) -> PathBuf {
    let workspace = member_workspace(
        root,
        name,
        &[(
            "expanded",
            "macros::answer!();\npub fn value() -> u32 { leaf::value() }\n",
            &["leaf"],
        )],
    );
    let manifest = workspace.join("crates/expanded/Cargo.toml");
    let mut contents = fs::read_to_string(&manifest).unwrap();
    contents.push_str("macros={path='../../../macros'}\n");
    fs::write(manifest, contents).unwrap();
    workspace
}

/// DC-18c: a member that loads a proc macro is keyed on the bytes of the
/// macro's library, which each checkout builds. Two checkouts whose macro is
/// the same bytes share the member; once the macro expands to something
/// else, the checkout that rebuilt it compiles the member into a new slot
/// and holds the new expansion, the other takes that slot when its macro is
/// the same bytes again, and when the macro is put back, the first slot
/// serves again. No checkout ever reads a member expanded by another macro.
#[cargo_test]
fn member_with_a_proc_macro_dependency_is_keyed_on_the_macros_bytes() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    write_macro(&root, "answer-forty");
    let first = macro_workspace(&root, "first");
    let second = macro_workspace(&root, "second");
    let cold = attempts(&first, &home, |_| {});
    assert_eq!(compiled(&cold, "expanded"), 1);
    assert_eq!(shared_status(cold.last().unwrap(), "expanded"), "eligible");
    assert_eq!(member_slots(&home, "expanded").len(), 1);
    let warm = attempts(&second, &home, |_| {});
    assert_eq!(
        compiled(&warm, "expanded"),
        0,
        "the second checkout compiled `expanded` against the same macro"
    );
    assert_eq!(member_slots(&home, "expanded").len(), 1);
    assert!(holds(&uplifted(&second, "expanded"), "answer-forty"));
    store_names_no_checkout(&home, &[&first, &second]);

    write_macro(&root, "answer-forty-one");
    let changed = attempts(&second, &home, |_| {});
    assert_eq!(
        compiled(&changed, "expanded"),
        1,
        "`expanded` was read from the slot of another macro"
    );
    assert_eq!(member_slots(&home, "expanded").len(), 2);
    assert!(holds(&uplifted(&second, "expanded"), "answer-forty-one"));
    let followed = attempts(&first, &home, |_| {});
    assert_eq!(compiled(&followed, "expanded"), 0);
    assert_eq!(member_slots(&home, "expanded").len(), 2);
    assert!(holds(&uplifted(&first, "expanded"), "answer-forty-one"));

    write_macro(&root, "answer-forty");
    let restored = attempts(&first, &home, |_| {});
    assert_eq!(compiled(&restored, "expanded"), 0);
    assert_eq!(member_slots(&home, "expanded").len(), 2);
    assert!(holds(&uplifted(&first, "expanded"), "answer-forty"));
    assert!(!holds(&uplifted(&first, "expanded"), "answer-forty-one"));
}

/// DC-18c: no file of the store names a checkout, as spelled or canonical.
fn store_names_no_checkout(home: &Path, checkouts: &[&Path]) {
    let store = home.join(".cargo/trust/native-dependencies-v1");
    // The compiler's dep-info names what the compile read (a macro's
    // library) at the compiling checkout's path; the key binds those bytes.
    for file in files_named(&store, "")
        .into_iter()
        .filter(|file| file.extension().is_none_or(|extension| extension != "d"))
    {
        for checkout in checkouts {
            for spelling in [checkout.to_path_buf(), checkout.canonicalize().unwrap()] {
                assert!(
                    !holds(&file, spelling.to_str().unwrap()),
                    "{} names {}",
                    file.display(),
                    checkout.display()
                );
            }
        }
    }
}

/// DC-18c: a proc macro outside the workspace that expands to a function
/// returning the manifest directory it read with `std::env::var`, a read the
/// compiler does not track: the path reaches only the object code.
fn write_locating_macro(root: &Path) {
    let path = root.join("whereabouts");
    fs::create_dir_all(path.join("src")).unwrap();
    fs::write(
        path.join("Cargo.toml"),
        "[package]\nname='whereabouts'\nversion='0.1.0'\nedition='2021'\n[lib]\nproc-macro=true\n",
    )
    .unwrap();
    fs::write(
        path.join("src/lib.rs"),
        "use proc_macro::TokenStream;\n\
         #[proc_macro]\n\
         pub fn whereabouts(_: TokenStream) -> TokenStream {\n\
         let dir = std::env::var(\"CARGO_MANIFEST_DIR\").unwrap();\n\
         format!(\"pub fn whereabouts() -> &'static str {{ {dir:?} }}\").parse().unwrap()\n\
         }\n",
    )
    .unwrap();
}

/// DC-18c: a member whose proc macro writes its checkout's path into the
/// member's code is never shared: `-Ztrust-path-free` judges metadata, and
/// the path is in the object code only. Its outputs are searched before its
/// job ends, it is recorded as path-bound and compiled privately, holding its
/// own checkout's path, as is the member that depends on it; no file of the
/// store names the checkout, and the store holds no library of either. The
/// next build excludes it as path-bound and compiles nothing.
#[cargo_test]
fn shared_member_expanding_its_checkout_path_stays_private() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    write_locating_macro(&root);
    let workspace = member_workspace(
        &root,
        "first",
        &[
            ("located", "whereabouts::whereabouts!();\n", &[]),
            (
                "user",
                "pub fn dir() -> &'static str { located::whereabouts() }\n",
                &["located"],
            ),
        ],
    );
    let manifest = workspace.join("crates/located/Cargo.toml");
    let mut contents = fs::read_to_string(&manifest).unwrap();
    contents.push_str("whereabouts={path='../../../whereabouts'}\n");
    fs::write(manifest, contents).unwrap();

    let cold = attempts(&workspace, &home, |_| {});
    let last = cold.last().unwrap();
    assert_eq!(shared_decision(last, "located"), &excluded("path-bound"));
    assert_eq!(shared_status(last, "user"), "excluded");
    let store = home.join(".cargo/trust/native-dependencies-v1");
    let libraries = |member: &str| {
        files_named(&store, &format!("lib{member}-"))
            .into_iter()
            .filter(|file| file.extension().unwrap() != "rmeta")
            .count()
    };
    for member in ["located", "user"] {
        assert_eq!(
            libraries(member),
            0,
            "the store holds a library of `{member}`"
        );
    }
    store_names_no_checkout(&home, &[&workspace]);
    let real = workspace.join("crates/located");
    assert!(holds(
        &uplifted(&workspace, "located"),
        real.to_str().unwrap()
    ));
    for member in ["leaf", "mid"] {
        assert_eq!(member_slots(&home, member).len(), 1, "{member}");
    }

    // The checkout's record plans `located` private at once: no shared
    // compile is tried again. (Under the stage-1 compiler the macro is
    // compiled on every build, so its private dependents are too.)
    let again = attempts(&workspace, &home, |_| {});
    assert_eq!(again.len(), 1, "a built checkout planned its build again");
    let last = again.last().unwrap();
    assert_eq!(shared_decision(last, "located"), &excluded("path-bound"));
    for member in ["located", "user"] {
        assert_eq!(libraries(member), 0, "`{member}` was compiled shared again");
    }
}

/// DC-18c: a member's own build script's `OUT_DIR` names its slot beside
/// what the script printed. Two checkouts whose scripts print the same
/// directives but leave different files in `OUT_DIR` (a native library the
/// member would bundle, say) do not share the member or its dependent.
#[cargo_test]
fn keyed_member_is_named_by_its_out_dir() {
    let root = paths::root();
    let home = root.join("home");
    fs::create_dir_all(home.join(".cargo")).unwrap();
    let workspaces: Vec<_> = ["first", "second"]
        .into_iter()
        .map(|name| {
            let workspace = scripted_workspace(&root, name);
            // The script leaves its flavor in `OUT_DIR` and prints the same
            // whatever the flavor.
            fs::write(
                workspace.join("crates/scripted/build.rs"),
                "fn main() {\n\
                 let out = std::path::PathBuf::from(std::env::var_os(\"OUT_DIR\").unwrap());\n\
                 let flavor = std::env::var(\"SCRIPTED_FLAVOR\").unwrap_or_else(|_| \"plain\".into());\n\
                 std::fs::write(out.join(\"flavor\"), flavor).unwrap();\n\
                 println!(\"cargo::rustc-check-cfg=cfg(scripted)\");\n\
                 println!(\"cargo::rustc-cfg=scripted\");\n\
                 println!(\"cargo::rustc-env=SCRIPTED_GREETING=greeting\");\n\
                 println!(\"cargo::rerun-if-changed=build.rs\");\n\
                 println!(\"cargo::rerun-if-env-changed=SCRIPTED_FLAVOR\");\n\
                 }\n",
            )
            .unwrap();
            workspace
        })
        .collect();
    attempts(&workspaces[0], &home, |_| {});
    for member in ["scripted", "user"] {
        assert_eq!(member_slots(&home, member).len(), 1, "{member}");
    }
    let differing = attempts(&workspaces[1], &home, |command| {
        command.env("SCRIPTED_FLAVOR", "other");
    });
    let stdout = |workspace: &Path| -> Vec<u8> {
        let files: Vec<_> = files_named(&workspace.join("target"), "stdout")
            .into_iter()
            .filter(|file| holds(file, "cargo::rustc-cfg=scripted"))
            .collect();
        assert_eq!(files.len(), 1, "{files:?}");
        fs::read(&files[0]).unwrap()
    };
    assert_eq!(
        stdout(&workspaces[0]),
        stdout(&workspaces[1]),
        "the two scripts printed different directives"
    );
    for member in ["scripted", "user"] {
        assert_eq!(
            compiled(&differing, member),
            1,
            "`{member}` was taken from a slot another `OUT_DIR` named"
        );
        assert_eq!(member_slots(&home, member).len(), 2, "{member}");
    }
}

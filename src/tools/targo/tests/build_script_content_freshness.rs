// Trust: actual content-mode build scripts must observe restored-mtime input edits.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

#![cfg(unix)]

use std::fs;
use std::os::unix::process::CommandExt as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use filetime::FileTime;

struct World(Option<tempfile::TempDir>);
impl World {
    fn new() -> Self {
        Self(Some(
            tempfile::Builder::new()
                .prefix("targo-build-input-content-")
                .suffix(".noindex")
                .tempdir()
                .unwrap(),
        ))
    }
    fn path(&self) -> &Path {
        self.0.as_ref().unwrap().path()
    }
    fn passed(mut self) {
        drop(self.0.take());
    }
}
impl Drop for World {
    fn drop(&mut self) {
        if let Some(world) = self.0.take() {
            eprintln!(
                "kept failed input-content world: {}",
                world.keep().display()
            );
        }
    }
}

fn write(path: &Path, text: impl AsRef<[u8]>) {
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, text).unwrap();
}
fn control(world: &Path, name: &str) -> PathBuf {
    world.join("control").join(name)
}
fn success(output: Output) -> Output {
    assert!(
        output.status.success(),
        "status={}\nstdout={}\nstderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    output
}
fn git(root: &Path, words: &[&str]) {
    success(
        Command::new("git")
            .current_dir(root)
            .args(words)
            .output()
            .unwrap(),
    );
}
fn targo_command(root: &Path, mode: &str, version: &str) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_targo"));
    command
        .arg0("targo")
        .current_dir(root)
        .args(["--unverified", "-Zchecksum-freshness", "--config"])
        .arg(format!("build.fingerprint=\"{mode}\""))
        .args(["build", "--offline", "-j", "2"])
        .env("ALAB_HARNESS_VERSION", version)
        .env(
            "CARGO_TARGET_DIR",
            root.parent().unwrap().join("target.noindex"),
        );
    for name in [
        "CARGO_MAKEFLAGS",
        "MAKEFLAGS",
        "MFLAGS",
        "RUSTC_WRAPPER",
        "RUSTC_WORKSPACE_WRAPPER",
    ] {
        command.env_remove(name);
    }
    command
}
fn targo(root: &Path, mode: &str, version: &str) -> Output {
    success(targo_command(root, mode, version).output().unwrap())
}
fn execute(root: &Path) -> Vec<u8> {
    success(
        Command::new(
            root.parent()
                .unwrap()
                .join("target.noindex/debug/input-root"),
        )
        .output()
        .unwrap(),
    )
    .stdout
}

struct Paused {
    child: std::process::Child,
    world: PathBuf,
    temporary: PathBuf,
}
impl Paused {
    fn spawn(world: &Path, root: &Path) -> Self {
        let mut command = targo_command(root, "content", "root-2");
        command
            .arg("--message-format=json")
            .stdout(fs::File::create(world.join("paused.stdout")).unwrap())
            .stderr(fs::File::create(world.join("paused.stderr")).unwrap());
        Self {
            child: command.spawn().unwrap(),
            world: world.to_owned(),
            temporary: root.join("generated/schema/temporary"),
        }
    }
    fn marker(&mut self, name: &str) -> Vec<u8> {
        let marker = control(&self.world, name);
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(60);
        while !marker.exists() {
            assert!(
                self.child.try_wait().unwrap().is_none(),
                "driver exited before {name}"
            );
            assert!(
                std::time::Instant::now() < deadline,
                "no actual build-script {name} barrier"
            );
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
        fs::read(marker).unwrap()
    }
    fn finish(&mut self) -> Output {
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(60);
        loop {
            if let Some(status) = self.child.try_wait().unwrap() {
                return success(Output {
                    status,
                    stdout: fs::read(self.world.join("paused.stdout")).unwrap(),
                    stderr: fs::read(self.world.join("paused.stderr")).unwrap(),
                });
            }
            assert!(
                std::time::Instant::now() < deadline,
                "actual paused driver failed to finish"
            );
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
    }
}
impl Drop for Paused {
    fn drop(&mut self) {
        // Release our actual fixture before reaping it, including on assertion
        // failure. Only the original owned Child may be killed on timeout.
        let _ = fs::write(control(&self.world, "release"), b"cleanup");
        let _ = fs::write(control(&self.world, "symlink-finish"), b"cleanup");
        let _ = fs::remove_file(&self.temporary);
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
        while self.child.try_wait().is_ok_and(|status| status.is_none()) {
            if std::time::Instant::now() >= deadline {
                let _ = self.child.kill();
                let _ = self.child.wait();
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
    }
}

fn fixture(world: &Path, declared: Option<&str>) -> (PathBuf, PathBuf) {
    // Instrumentation must not create new siblings of the source while its
    // original ancestor stamps are held through the script action.
    write(&world.join("generated.count"), b"0\n");
    write(&world.join("unchanged.count"), b"0\n");
    // Handshake publications mutate only this pre-existing sibling directory,
    // never an ancestor whose stamp protects the actual input traversal.
    fs::create_dir(world.join("control")).unwrap();
    let root = world.join("source");
    write(
        &root.join("Cargo.toml"),
        "[package]\nname='input-root'\nversion='0.1.0'\nedition='2024'\n[dependencies]\ngenerated={path='generated'}\nunchanged={path='unchanged'}\n[workspace]\n",
    );
    write(
        &root.join("src/main.rs"),
        "fn main(){println!(\"{} {} {}\",env!(\"ALAB_HARNESS_VERSION\"),generated::VALUE,unchanged::KEEP);}\n",
    );
    write(
        &root.join("generated/Cargo.toml"),
        "[package]\nname='generated'\nversion='0.1.0'\nedition='2024'\n",
    );
    write(
        &root.join("generated/src/lib.rs"),
        "include!(concat!(env!(\"OUT_DIR\"),\"/generated.rs\"));\n",
    );
    let declaration = declared.map_or(String::new(), |path| {
        format!("println!(\"cargo:rerun-if-changed={path}\");")
    });
    write(
        &root.join("generated/build.rs"),
        format!(
            r#"
fn main() {{
    {declaration}
    let count=std::path::Path::new({count:?});
    let old=std::fs::read_to_string(count).unwrap_or_default().trim().parse::<u32>().unwrap_or(0);
    std::fs::write(count,format!("{{}}\n",old+1)).unwrap();
    let mut value=std::fs::read_to_string("schema/value").unwrap();
    let pause=std::path::Path::new({pause:?});
    if pause.exists() {{
        let ready=std::path::Path::new({ready:?});
        std::fs::write(ready.with_extension("pending"),&value).unwrap();
        std::fs::rename(ready.with_extension("pending"),ready).unwrap();
        let deadline=std::time::Instant::now()+std::time::Duration::from_secs(90);
        while !std::path::Path::new({release:?}).exists() {{
            assert!(std::time::Instant::now()<deadline,"fixture input barrier timed out");
            std::thread::sleep(std::time::Duration::from_millis(10));
        }}
    }}
    if std::path::Path::new({transient_mode:?}).exists() {{
        let temporary=std::path::Path::new("schema/temporary");
        value=std::fs::read_to_string(temporary).unwrap();
        let observed=std::path::Path::new({observed:?});
        std::fs::write(observed.with_extension("pending"),&value).unwrap();
        std::fs::rename(observed.with_extension("pending"),observed).unwrap();
        let deadline=std::time::Instant::now()+std::time::Duration::from_secs(90);
        while temporary.exists() {{
            assert!(std::time::Instant::now()<deadline,"fixture transient removal timed out");
            std::thread::sleep(std::time::Duration::from_millis(10));
        }}
    }}
    if std::path::Path::new({symlink_mode:?}).exists() {{
        value=std::fs::read_to_string("schema/value").unwrap();
        let observed=std::path::Path::new({observed:?});
        std::fs::write(observed.with_extension("pending"),&value).unwrap();
        std::fs::rename(observed.with_extension("pending"),observed).unwrap();
        let deadline=std::time::Instant::now()+std::time::Duration::from_secs(60);
        while !std::path::Path::new({symlink_finish:?}).exists() {{
            assert!(std::time::Instant::now()<deadline,"fixture symlink restoration timed out");
            std::thread::sleep(std::time::Duration::from_millis(10));
        }}
    }}
    std::fs::write(std::path::PathBuf::from(std::env::var_os("OUT_DIR").unwrap()).join("generated.rs"),
        format!("pub const VALUE:u32={{}};",value.trim())).unwrap();
}}
"#,
            count = world.join("generated.count"),
            pause = control(world, "pause"),
            ready = control(world, "ready"),
            transient_mode = control(world, "transient-mode"),
            symlink_mode = control(world, "symlink-mode"),
            symlink_finish = control(world, "symlink-finish"),
            observed = control(world, "observed"),
            release = control(world, "release")
        ),
    );
    let input = root.join("generated/schema/value");
    write(&input, b"111\n");
    write(
        &root.join("unchanged/Cargo.toml"),
        "[package]\nname='unchanged'\nversion='0.1.0'\nedition='2024'\n",
    );
    write(
        &root.join("unchanged/src/lib.rs"),
        "pub const KEEP:u32=77;\n",
    );
    write(
        &root.join("unchanged/build.rs"),
        format!(
            r#"
fn main() {{
    println!("cargo:rerun-if-changed=build.rs");
    let count=std::path::Path::new({count:?});
    let old=std::fs::read_to_string(count).unwrap_or_default().trim().parse::<u32>().unwrap_or(0);
    std::fs::write(count,format!("{{}}\n",old+1)).unwrap();
}}
"#,
            count = world.join("unchanged.count")
        ),
    );
    git(&root, &["init", "-q", "-b", "main"]);
    git(&root, &["config", "user.name", "Input content fixture"]);
    git(
        &root,
        &["config", "user.email", "input-content@example.invalid"],
    );
    git(&root, &["add", "."]);
    git(&root, &["commit", "-qm", "first schema"]);
    (root, input)
}

fn run(declared: Option<&str>, mode: &str, expected: &[u8]) {
    let world = World::new();
    let (root, input) = fixture(world.path(), declared);
    let first = targo(&root, mode, "root-1");
    write(&world.path().join("first.stderr"), &first.stderr);
    assert_eq!(execute(&root), b"root-1 111 77\n");
    let modified = FileTime::from_last_modification_time(&fs::metadata(&input).unwrap());
    write(&input, b"222\n");
    git(&root, &["add", "generated/schema/value"]);
    git(&root, &["commit", "-qm", "same-size schema edit"]);
    filetime::set_file_mtime(&input, modified).unwrap();
    assert_eq!(
        FileTime::from_last_modification_time(&fs::metadata(&input).unwrap()),
        modified
    );
    let second = targo(&root, mode, "root-2");
    write(&world.path().join("second.stderr"), &second.stderr);
    assert_eq!(execute(&root), expected);
    assert_eq!(
        fs::read(world.path().join("unchanged.count")).unwrap(),
        b"1\n"
    );
    assert_eq!(
        fs::read(world.path().join("generated.count")).unwrap(),
        if mode == "content" {
            &b"2\n"[..]
        } else {
            &b"1\n"[..]
        }
    );
    // A warm repeat must retain both completed build-script facts.
    targo(&root, mode, "root-2");
    assert_eq!(
        fs::read(world.path().join("unchanged.count")).unwrap(),
        b"1\n"
    );
    assert_eq!(execute(&root), expected);
    world.passed();
}

#[test]
fn content_tracks_declared_file_directory_and_implicit_package_inputs() {
    for path in [Some("schema/value"), Some("schema"), None] {
        run(path, "content", b"root-2 222 77\n");
    }
}

#[test]
fn explicit_mtime_keeps_its_named_timestamp_semantics() {
    run(Some("schema/value"), "mtime", b"root-2 111 77\n");
}

#[test]
fn an_edit_during_script_execution_cannot_bless_new_inputs_with_old_output() {
    let world = World::new();
    let (root, input) = fixture(world.path(), Some("schema/value"));
    targo(&root, "content", "root-1");
    let original_time = FileTime::from_last_modification_time(&fs::metadata(&input).unwrap());
    write(&input, b"222\n");
    filetime::set_file_mtime(&input, original_time).unwrap();
    write(&control(world.path(), "pause"), b"pause after reading");
    let mut paused = Paused::spawn(world.path(), &root);
    assert_eq!(paused.marker("ready"), b"222\n");
    write(&input, b"333\n");
    filetime::set_file_mtime(&input, original_time).unwrap();
    assert_eq!(
        FileTime::from_last_modification_time(&fs::metadata(&input).unwrap()),
        original_time
    );
    write(&control(world.path(), "release"), b"finish original read");
    assert!(paused.child.wait().unwrap().success());
    drop(paused);
    assert_eq!(execute(&root), b"root-2 222 77\n");
    fs::remove_file(control(world.path(), "pause")).unwrap();
    targo(&root, "content", "root-3");
    assert_eq!(execute(&root), b"root-3 333 77\n");
    assert_eq!(
        fs::read(world.path().join("generated.count")).unwrap(),
        b"3\n"
    );
    assert_eq!(
        fs::read(world.path().join("unchanged.count")).unwrap(),
        b"1\n"
    );
    world.passed();
}

#[test]
fn implicit_package_inventory_cannot_accept_temporary_directory_membership() {
    let world = World::new();
    let (root, input) = fixture(world.path(), None);
    targo(&root, "content", "root-1");
    write(&input, b"222\n");
    write(
        &control(world.path(), "pause"),
        b"pause after original read",
    );
    write(
        &control(world.path(), "transient-mode"),
        b"read temporary input",
    );
    let mut paused = Paused::spawn(world.path(), &root);
    assert_eq!(paused.marker("ready"), b"222\n");
    let temporary = root.join("generated/schema/temporary");
    write(&temporary, b"999\n");
    write(&control(world.path(), "release"), b"read temporary file");
    assert_eq!(paused.marker("observed"), b"999\n");
    fs::remove_file(&temporary).unwrap();
    assert!(paused.child.wait().unwrap().success());
    drop(paused);
    assert_eq!(execute(&root), b"root-2 999 77\n");
    fs::remove_file(control(world.path(), "pause")).unwrap();
    fs::remove_file(control(world.path(), "transient-mode")).unwrap();
    targo(&root, "content", "root-3");
    assert_eq!(execute(&root), b"root-3 222 77\n");
    assert_eq!(
        fs::read(world.path().join("generated.count")).unwrap(),
        b"3\n"
    );
    assert_eq!(
        fs::read(world.path().join("unchanged.count")).unwrap(),
        b"1\n"
    );
    world.passed();
}

fn symlink_input_fixture(world: &Path) -> (PathBuf, PathBuf) {
    let (root, _) = fixture(world, Some("schema/value"));
    let generated = root.join("generated");
    fs::rename(generated.join("schema"), generated.join("real-schema")).unwrap();
    std::os::unix::fs::symlink("real-schema", generated.join("schema")).unwrap();
    git(&root, &["add", "-A"]);
    git(
        &root,
        &[
            "commit",
            "-qm",
            "declared input through a directory symlink",
        ],
    );
    let input = generated.join("real-schema/value");
    (root, input)
}

#[test]
fn declared_input_symlink_ancestor_reuses_content_and_tracks_target_edits() {
    let world = World::new();
    let (root, input) = symlink_input_fixture(world.path());
    let initial = traced_build(world.path(), &root, "symlink-initial", "1", "root-1");
    assert_eq!(execute(&root), b"root-1 111 77\n");
    assert_eq!(
        fs::read(world.path().join("generated.count")).unwrap(),
        b"1\n"
    );
    let unrelated = unrelated_artifact(&root, &initial.stdout);
    let warm = traced_build(world.path(), &root, "symlink-warm", "1", "root-1");
    assert_eq!(execute(&root), b"root-1 111 77\n");
    assert_eq!(
        fs::read(world.path().join("generated.count")).unwrap(),
        b"1\n"
    );
    assert_eq!(unrelated_artifact(&root, &warm.stdout), unrelated);

    let metadata = fs::metadata(&input).unwrap();
    let modified = FileTime::from_last_modification_time(&metadata);
    write(&input, b"222\n");
    git(&root, &["add", "generated/real-schema/value"]);
    git(&root, &["commit", "-qm", "same-size real target edit"]);
    filetime::set_file_mtime(&input, modified).unwrap();
    assert_eq!(fs::metadata(&input).unwrap().len(), metadata.len());
    assert_eq!(
        FileTime::from_last_modification_time(&fs::metadata(&input).unwrap()),
        modified
    );
    let changed = traced_build(world.path(), &root, "symlink-changed", "1", "root-2");
    assert_eq!(execute(&root), b"root-2 222 77\n");
    assert_eq!(
        fs::read(world.path().join("generated.count")).unwrap(),
        b"2\n"
    );
    assert_eq!(unrelated_artifact(&root, &changed.stdout), unrelated);
    let warm_changed = traced_build(world.path(), &root, "symlink-changed-warm", "1", "root-2");
    assert_eq!(execute(&root), b"root-2 222 77\n");
    assert_eq!(
        fs::read(world.path().join("generated.count")).unwrap(),
        b"2\n"
    );
    assert_eq!(
        fs::read(world.path().join("unchanged.count")).unwrap(),
        b"1\n"
    );
    assert_eq!(unrelated_artifact(&root, &warm_changed.stdout), unrelated);
    world.passed();
}

#[test]
fn declared_input_symlink_control_handshake_alone_preserves_warm_fact() {
    let world = World::new();
    let (root, _) = symlink_input_fixture(world.path());
    write(
        &control(world.path(), "pause"),
        b"pause without changing inputs",
    );
    let mut paused = Paused::spawn(world.path(), &root);
    assert_eq!(paused.marker("ready"), b"111\n");
    write(&control(world.path(), "release"), b"finish unchanged read");
    let initial = paused.finish();
    drop(paused);
    assert_eq!(execute(&root), b"root-2 111 77\n");
    assert_eq!(
        fs::read(world.path().join("generated.count")).unwrap(),
        b"1\n"
    );
    let unrelated = unrelated_artifact(&root, &initial.stdout);
    fs::remove_file(control(world.path(), "pause")).unwrap();
    let warm = traced_build(world.path(), &root, "symlink-control-warm", "1", "root-2");
    assert_eq!(execute(&root), b"root-2 111 77\n");
    assert_eq!(
        fs::read(world.path().join("generated.count")).unwrap(),
        b"1\n"
    );
    assert_eq!(
        fs::read(world.path().join("unchanged.count")).unwrap(),
        b"1\n"
    );
    assert_eq!(unrelated_artifact(&root, &warm.stdout), unrelated);
    world.passed();
}

struct RetargetedInput {
    link: PathBuf,
    original: Option<PathBuf>,
}
impl RetargetedInput {
    fn new(link: PathBuf) -> Self {
        let original = link.with_file_name("schema.original");
        fs::rename(&link, &original).unwrap();
        let result = Self {
            link,
            original: Some(original),
        };
        std::os::unix::fs::symlink("alternate-schema", &result.link).unwrap();
        result
    }
    fn restore(mut self) {
        fs::remove_file(&self.link).unwrap();
        fs::rename(self.original.as_ref().unwrap(), &self.link).unwrap();
        self.original = None;
    }
}
impl Drop for RetargetedInput {
    fn drop(&mut self) {
        if let Some(original) = self.original.take() {
            let _ = fs::remove_file(&self.link);
            let _ = fs::rename(original, &self.link);
        }
    }
}

#[test]
fn declared_input_symlink_retarget_and_restore_cannot_bless_transient_reads() {
    use std::os::unix::fs::MetadataExt as _;
    let world = World::new();
    let (root, input) = symlink_input_fixture(world.path());
    write(&root.join("generated/alternate-schema/value"), b"999\n");
    git(&root, &["add", "generated/alternate-schema/value"]);
    git(&root, &["commit", "-qm", "alternate symlink input target"]);
    let initial = traced_build(world.path(), &root, "symlink-aba-initial", "1", "root-1");
    assert_eq!(execute(&root), b"root-1 111 77\n");
    let unrelated = unrelated_artifact(&root, &initial.stdout);
    let modified = FileTime::from_last_modification_time(&fs::metadata(&input).unwrap());
    write(&input, b"222\n");
    filetime::set_file_mtime(&input, modified).unwrap();
    write(
        &control(world.path(), "pause"),
        b"pause before alternate read",
    );
    write(
        &control(world.path(), "symlink-mode"),
        b"read through retargeted ancestor",
    );
    let mut paused = Paused::spawn(world.path(), &root);
    assert_eq!(paused.marker("ready"), b"222\n");
    let link = root.join("generated/schema");
    let original = fs::symlink_metadata(&link).unwrap();
    let original_target = fs::read_link(&link).unwrap();
    let retargeted = RetargetedInput::new(link.clone());
    write(
        &control(world.path(), "release"),
        b"read alternate target now",
    );
    assert_eq!(paused.marker("observed"), b"999\n");
    retargeted.restore();
    let restored = fs::symlink_metadata(&link).unwrap();
    assert_eq!(
        (restored.dev(), restored.ino()),
        (original.dev(), original.ino())
    );
    assert_eq!(fs::read_link(&link).unwrap(), original_target);
    write(
        &control(world.path(), "symlink-finish"),
        b"original link restored before completion",
    );
    paused.finish();
    drop(paused);
    assert_eq!(execute(&root), b"root-2 999 77\n");
    assert_eq!(
        fs::read(world.path().join("generated.count")).unwrap(),
        b"2\n"
    );
    fs::remove_file(control(world.path(), "pause")).unwrap();
    fs::remove_file(control(world.path(), "symlink-mode")).unwrap();
    // Same driver version and restored link bytes: only the rejected execution
    // window can prevent this transient result from becoming a warm fact.
    let corrected = traced_build(world.path(), &root, "symlink-aba-corrected", "1", "root-2");
    assert_eq!(execute(&root), b"root-2 222 77\n");
    assert_eq!(
        fs::read(world.path().join("generated.count")).unwrap(),
        b"3\n"
    );
    assert_eq!(unrelated_artifact(&root, &corrected.stdout), unrelated);
    let warm = traced_build(world.path(), &root, "symlink-aba-warm", "1", "root-2");
    assert_eq!(execute(&root), b"root-2 222 77\n");
    assert_eq!(
        fs::read(world.path().join("generated.count")).unwrap(),
        b"3\n"
    );
    assert_eq!(
        fs::read(world.path().join("unchanged.count")).unwrap(),
        b"1\n"
    );
    assert_eq!(unrelated_artifact(&root, &warm.stdout), unrelated);
    world.passed();
}

const INPUT_TRACE: &str = "targo::compiler::fingerprint::build_script_inputs";
const LARGE_INPUT_BYTES: u64 = 256 * 1024 * 1024;

#[derive(Debug)]
struct InputRead {
    kind: String,
    input_bytes: u64,
    bytes_hashed: u64,
}

fn input_reads(stderr: &[u8]) -> Vec<InputRead> {
    String::from_utf8_lossy(stderr)
        .lines()
        .filter(|line| line.contains(INPUT_TRACE) && line.contains("observed build-script inputs"))
        .map(|line| {
            let field = |name: &str| {
                line.split_whitespace()
                    .find_map(|word| word.strip_prefix(name))
                    .unwrap_or_else(|| panic!("missing {name} in actual input trace: {line}"))
                    .trim_matches('"')
            };
            InputRead {
                kind: field("capture_kind=").to_owned(),
                input_bytes: field("input_bytes=").parse().unwrap(),
                bytes_hashed: field("bytes_hashed=").parse().unwrap(),
            }
        })
        .collect()
}

#[derive(Debug, serde::Serialize)]
struct InputMetadataWork {
    entries: u64,
    input_bytes: u64,
    bytes_hashed: u64,
    metadata_reads: u64,
    resolution_steps: u64,
    link_reads: u64,
    observations: u64,
    revalidations: u64,
}

fn directory_metadata_work(stderr: &[u8], entries: u64, bytes: u64) -> Vec<InputMetadataWork> {
    String::from_utf8_lossy(stderr)
        .lines()
        .filter(|line| line.contains(INPUT_TRACE) && line.contains("observed build-script inputs"))
        .filter_map(|line| {
            let field = |name: &str| {
                line.split_whitespace()
                    .find_map(|word| word.strip_prefix(name))
                    .unwrap_or_else(|| panic!("missing {name} in actual metadata trace: {line}"))
                    .trim_matches('"')
            };
            if field("capture_kind=") != "content"
                || field("entries=").parse::<u64>().unwrap() != entries
                || field("bytes_hashed=").parse::<u64>().unwrap() != bytes
            {
                return None;
            }
            Some(InputMetadataWork {
                entries,
                input_bytes: field("input_bytes=").parse().unwrap(),
                bytes_hashed: bytes,
                metadata_reads: field("metadata_reads=").parse().unwrap(),
                resolution_steps: field("resolution_steps=").parse().unwrap(),
                link_reads: field("link_reads=").parse().unwrap(),
                observations: field("observations=").parse().unwrap(),
                revalidations: field("revalidations=").parse().unwrap(),
            })
        })
        .collect()
}

fn traced_build(world: &Path, root: &Path, phase: &str, force: &str, version: &str) -> Output {
    let mut command = targo_command(root, "content", version);
    command
        .arg("--message-format=json")
        .env("CARGO_LOG", format!("{INPUT_TRACE}=debug"))
        .env("CONTENT_WINDOW_FORCE", force);
    recorded_command(world, phase, command)
}

fn recorded_command(world: &Path, phase: &str, mut command: Command) -> Output {
    use std::process::Stdio;
    use std::time::{Duration, Instant};
    let stdout = world.join(format!("{phase}.stdout"));
    let stderr = world.join(format!("{phase}.stderr"));
    command
        .stdin(Stdio::null())
        .stdout(fs::File::create(&stdout).unwrap())
        .stderr(fs::File::create(&stderr).unwrap());
    let mut child = command.spawn().unwrap();
    drop(command);
    let deadline = Instant::now() + Duration::from_secs(60);
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if Instant::now() >= deadline {
            // Only this original owned driver is signalled. The failed world's
            // source and any executing compiled fixture remain preserved.
            let _ = child.kill();
            let _ = child.wait();
            panic!("actual {phase} driver exceeded its hang detector");
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    success(Output {
        status,
        stdout: fs::read(stdout).unwrap(),
        stderr: fs::read(stderr).unwrap(),
    })
}

struct CacheWorkPhase {
    build: Output,
    events: Vec<serde_json::Value>,
    report: serde_json::Value,
    run_id: String,
}

fn cache_work_phase(world: &Path, root: &Path, phase: &str, version: &str) -> CacheWorkPhase {
    let home = world.join("analysis-home");
    let log_paths = || {
        fs::read_dir(home.join("log"))
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .collect::<std::collections::BTreeSet<_>>()
    };
    let before = log_paths();
    let mut build = targo_command(root, "content", version);
    build
        .args([
            "-Zbuild-analysis",
            "--config",
            "build.analysis.enabled=true",
            "--message-format=json",
        ])
        .env("CARGO_HOME", &home)
        .env_remove("CARGO_LOG");
    // The original build has actually exited, including its logger's join,
    // before identifying or querying the newly produced session.
    let build = recorded_command(world, phase, build);
    let after = log_paths();
    let added: Vec<_> = after.difference(&before).collect();
    let [log] = added.as_slice() else {
        panic!("expected one actual new analysis session: {added:?}");
    };
    let events: Vec<serde_json::Value> = fs::read_to_string(log)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    let started: Vec<_> = events
        .iter()
        .filter(|event| event["reason"] == "build-started")
        .collect();
    let [started] = started.as_slice() else {
        panic!("missing unique original build-started envelope: {started:?}");
    };
    let run_id = started["run_id"].as_str().unwrap().to_owned();
    assert_eq!(log.file_stem().unwrap(), run_id.as_str());
    assert!(events.iter().all(|event| event["run_id"] == run_id));

    // The exact session comes from the original child's JSON stream as well
    // as its closed log, without choosing a newest file in a shared cache.
    let stdout_rows: Vec<serde_json::Value> = String::from_utf8_lossy(&build.stdout)
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    let sessions: Vec<_> = stdout_rows
        .iter()
        .filter(|row| row["reason"] == "build-analysis-session")
        .collect();
    let [session] = sessions.as_slice() else {
        panic!("expected one original analysis identity: {sessions:?}");
    };
    assert_eq!(session["schema"], 1);
    assert_eq!(session["scope"], "build-script-inputs-v1");
    assert_eq!(session["run_id"], run_id);

    let mut report = Command::new(env!("CARGO_BIN_EXE_targo"));
    report
        .arg0("targo")
        .current_dir(root)
        .args([
            "-Zbuild-analysis",
            "report",
            "cache-work",
            "--id",
            &run_id,
            "--json",
            "--manifest-path",
        ])
        .arg(root.join("Cargo.toml"))
        .env("CARGO_HOME", &home)
        .env("CARGO_TARGET_DIR", world.join("target.noindex"))
        .env_remove("CARGO_LOG");
    let output = recorded_command(world, &format!("{phase}-report"), report);
    CacheWorkPhase {
        build,
        events,
        report: serde_json::from_slice(&output.stdout).unwrap(),
        run_id,
    }
}

const INPUT_WORK_FIELDS: [&str; 8] = [
    "entries",
    "input_bytes",
    "bytes_hashed",
    "metadata_reads",
    "resolution_steps",
    "link_reads",
    "observations",
    "revalidations",
];

fn work_number(value: &serde_json::Value, field: &str) -> u64 {
    value[field]
        .as_u64()
        .unwrap_or_else(|| panic!("missing measured {field}: {value}"))
}

fn checked_cache_work_report(phase: &CacheWorkPhase) {
    let report = &phase.report;
    assert_eq!(report["schema"], "targo-cache-work-report-v1");
    assert_eq!(report["scope"], "build-script-inputs-v1");
    assert_eq!(report["run_id"], phase.run_id);
    assert_eq!(report["availability"], "complete");
    assert!(report["unavailable_reason"].is_null());
    assert_eq!(report["build_outcome"], "not-recorded");
    let registered: Vec<_> = phase
        .events
        .iter()
        .filter(|event| event["reason"] == "unit-registered")
        .collect();
    // Two build-script compiles, two script runs, two libraries and the binary.
    assert_eq!(registered.len(), 7);
    let units = report["units"].as_array().unwrap();
    assert_eq!(units.len(), registered.len());
    let mut indices = std::collections::BTreeSet::new();
    let mut observed_units = 0;
    let mut script_units = 0;
    let mut attempts = 0;
    let mut captured = 0;
    let mut uncacheable = 0;
    let mut totals = [0u64; 8];
    for unit in units {
        assert!(indices.insert(work_number(unit, "index")));
        let original = registered
            .iter()
            .find(|event| event["index"] == unit["index"])
            .unwrap();
        for field in ["package_id", "target", "mode"] {
            assert_eq!(unit[field], original[field], "wrong original unit: {unit}");
        }
        if unit["mode"] == "run-custom-build" {
            script_units += 1;
            assert_eq!(unit["target"]["kind"], "build-script");
        }
        let n = work_number(unit, "attempts");
        let c = work_number(unit, "captured_attempts");
        let u = work_number(unit, "uncacheable_attempts");
        assert_eq!(n, c + u);
        attempts += n;
        captured += c;
        uncacheable += u;
        let phases = unit["phases"].as_array().unwrap();
        if n == 0 {
            assert!(unit["work"].is_null());
            assert!(phases.is_empty());
            continue;
        }
        observed_units += 1;
        assert_eq!(unit["mode"], "run-custom-build");
        let mut names = std::collections::BTreeSet::new();
        let mut phase_attempts = 0;
        let mut phase_captured = 0;
        let mut phase_uncacheable = 0;
        let mut phase_work = [0u64; 8];
        for cost in phases {
            let name = cost["phase"].as_str().unwrap();
            assert!(matches!(
                name,
                "execution-window" | "freshness" | "publication"
            ));
            assert!(names.insert(name));
            let n = work_number(cost, "attempts");
            let c = work_number(cost, "captured_attempts");
            let u = work_number(cost, "uncacheable_attempts");
            assert!(n > 0);
            assert_eq!(n, c + u);
            phase_attempts += n;
            phase_captured += c;
            phase_uncacheable += u;
            for (index, field) in INPUT_WORK_FIELDS.iter().enumerate() {
                phase_work[index] = phase_work[index]
                    .checked_add(work_number(&cost["work"], field))
                    .unwrap();
            }
        }
        assert_eq!(
            (phase_attempts, phase_captured, phase_uncacheable),
            (n, c, u)
        );
        for (index, field) in INPUT_WORK_FIELDS.iter().enumerate() {
            assert_eq!(phase_work[index], work_number(&unit["work"], field));
            totals[index] = totals[index].checked_add(phase_work[index]).unwrap();
        }
    }
    let denominator = &report["denominators"];
    for (field, expected) in [
        ("registered_units", registered.len() as u64),
        ("run_script_units", script_units),
        ("observed_units", observed_units),
        ("attempts_started", attempts),
        ("attempts_finished", attempts),
        ("captured_attempts", captured),
        ("uncacheable_attempts", uncacheable),
    ] {
        assert_eq!(work_number(denominator, field), expected);
    }
    assert_eq!(script_units, 2);
    assert_eq!(observed_units, 2);
    assert!(attempts > 0);
    for reason in ["input-work-started", "input-work-finished"] {
        assert_eq!(
            phase
                .events
                .iter()
                .filter(|event| event["reason"] == reason)
                .count() as u64,
            attempts
        );
    }
    for (index, field) in INPUT_WORK_FIELDS.iter().enumerate() {
        assert_eq!(work_number(&report["totals"], field), totals[index]);
    }
}

fn script_work<'a>(phase: &'a CacheWorkPhase, root: &Path, package: &str) -> &'a serde_json::Value {
    let rows: Vec<_> = phase.report["units"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|unit| {
            unit["mode"] == "run-custom-build"
                && targo::workspace::PackageIdSpec::parse(unit["package_id"].as_str().unwrap())
                    .unwrap()
                    .name()
                    == package
        })
        .collect();
    let [unit] = rows.as_slice() else {
        panic!("expected one original {package} run unit: {rows:?}");
    };
    let identity =
        targo::workspace::PackageIdSpec::parse(unit["package_id"].as_str().unwrap()).unwrap();
    assert_eq!(
        identity
            .url()
            .unwrap()
            .to_file_path()
            .unwrap()
            .canonicalize()
            .unwrap(),
        root.join(package).canonicalize().unwrap()
    );
    unit
}

fn unrelated_artifact(
    root: &Path,
    output: &[u8],
) -> (PathBuf, u64, u64, std::time::SystemTime, Vec<u8>) {
    use std::os::unix::fs::MetadataExt as _;
    let target = root
        .parent()
        .unwrap()
        .join("target.noindex")
        .canonicalize()
        .unwrap();
    let package = root.join("unchanged").canonicalize().unwrap();
    let manifest = package.join("Cargo.toml");
    let mut paths = std::collections::BTreeSet::new();
    for line in String::from_utf8_lossy(output).lines() {
        let Ok(row) = serde_json::from_str::<serde_json::Value>(line) else {
            continue;
        };
        if row["reason"] != "compiler-artifact"
            || row["target"]["name"] != "unchanged"
            || row["target"]["kind"] != serde_json::json!(["lib"])
            || row["profile"]["test"] != false
        {
            continue;
        }
        let identity = targo::workspace::PackageIdSpec::parse(
            row["package_id"]
                .as_str()
                .expect("actual artifact package ID"),
        )
        .unwrap();
        assert_eq!(identity.name(), "unchanged");
        assert_eq!(identity.version(), Some(semver::Version::new(0, 1, 0)));
        assert_eq!(
            identity
                .url()
                .unwrap()
                .to_file_path()
                .unwrap()
                .canonicalize()
                .unwrap(),
            package
        );
        assert_eq!(
            Path::new(
                row["manifest_path"]
                    .as_str()
                    .expect("actual artifact manifest")
            )
            .canonicalize()
            .unwrap(),
            manifest
        );
        for filename in row["filenames"]
            .as_array()
            .expect("actual artifact filenames")
        {
            let path = Path::new(filename.as_str().expect("actual artifact filename"));
            if path
                .extension()
                .is_some_and(|extension| extension == "rlib")
            {
                let path = path.canonicalize().unwrap();
                assert!(
                    path.starts_with(&target),
                    "actual unrelated artifact left target: {path:?}"
                );
                paths.insert(path);
            }
        }
    }
    let paths: Vec<_> = paths.into_iter().collect();
    let [path] = paths.as_slice() else {
        panic!("expected one actual unrelated dependency rlib: {paths:?}");
    };
    let metadata = fs::symlink_metadata(path).unwrap();
    assert!(metadata.is_file());
    (
        path.clone(),
        metadata.dev(),
        metadata.ino(),
        metadata.modified().unwrap(),
        fs::read(path).unwrap(),
    )
}

#[test]
fn dirty_execution_window_reads_no_large_input_content() {
    use std::io::{Seek as _, SeekFrom, Write as _};
    let world = World::new();
    let (root, _) = fixture(world.path(), Some("schema/blob"));
    let blob = root.join("generated/schema/blob");
    let mut file = fs::OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(&blob)
        .unwrap();
    // The sparse middle avoids allocating a 256 MiB fixture buffer. Content
    // observations still read/hash every byte returned by the actual file.
    file.set_len(LARGE_INPUT_BYTES).unwrap();
    file.write_all(&[10]).unwrap();
    file.seek(SeekFrom::End(-1)).unwrap();
    file.write_all(&[20]).unwrap();
    drop(file);
    write(
        &root.join("generated/build.rs"),
        format!(
            r#"
use std::io::{{Read as _, Seek as _, SeekFrom}};
fn main() {{
 println!("cargo:rerun-if-changed=build.rs");
 println!("cargo:rerun-if-changed=schema/blob");
 println!("cargo:rerun-if-env-changed=CONTENT_WINDOW_FORCE");
 let count=std::path::PathBuf::from({count:?});
 let previous=std::fs::read_to_string(&count).unwrap_or_default().trim().parse::<u32>().unwrap_or(0);
 std::fs::write(count,format!("{{}}\n",previous+1)).unwrap();
 let force=std::env::var("CONTENT_WINDOW_FORCE").unwrap().parse::<u32>().unwrap();
 let mut file=std::fs::File::open("schema/blob").unwrap();
 assert_eq!(file.metadata().unwrap().len(),{LARGE_INPUT_BYTES});
 let mut first=[0];let mut last=[0];
 file.read_exact(&mut first).unwrap();file.seek(SeekFrom::End(-1)).unwrap();file.read_exact(&mut last).unwrap();
 let value=u32::from(first[0])+u32::from(last[0])+force;
 std::fs::write(std::path::PathBuf::from(std::env::var_os("OUT_DIR").unwrap()).join("generated.rs"),format!("pub const VALUE:u32={{value}};")).unwrap();
}}
"#,
            count = world.path().join("generated.count")
        ),
    );
    git(
        &root,
        &["add", "generated/build.rs", "generated/schema/blob"],
    );
    git(
        &root,
        &[
            "commit",
            "-qm",
            "declared large input with one environment-triggered rerun",
        ],
    );

    let initial = traced_build(world.path(), &root, "window-initial", "1", "root-1");
    assert_eq!(execute(&root), b"root-1 31 77\n");
    assert_eq!(
        fs::read(world.path().join("generated.count")).unwrap(),
        b"1\n"
    );
    let unrelated = unrelated_artifact(&root, &initial.stdout);
    let warm = traced_build(world.path(), &root, "window-warm", "1", "root-1");
    assert_eq!(execute(&root), b"root-1 31 77\n");
    assert_eq!(
        fs::read(world.path().join("generated.count")).unwrap(),
        b"1\n"
    );
    assert_eq!(unrelated_artifact(&root, &warm.stdout), unrelated);
    let dirty = traced_build(world.path(), &root, "window-dirty", "2", "root-2");
    assert_eq!(execute(&root), b"root-2 32 77\n");
    assert_eq!(
        fs::read(world.path().join("generated.count")).unwrap(),
        b"2\n"
    );
    assert_eq!(
        fs::read(world.path().join("unchanged.count")).unwrap(),
        b"1\n"
    );
    assert_eq!(unrelated_artifact(&root, &dirty.stdout), unrelated);
    assert_eq!(fs::metadata(&blob).unwrap().len(), LARGE_INPUT_BYTES);

    let initial_reads = input_reads(&initial.stderr);
    let warm_reads = input_reads(&warm.stderr);
    let dirty_reads = input_reads(&dirty.stderr);
    let large_windows: Vec<_> = dirty_reads
        .iter()
        .filter(|row| row.kind == "window" && row.input_bytes >= LARGE_INPUT_BYTES)
        .collect();
    assert!(
        !large_windows.is_empty(),
        "no actual dirty execution window: {dirty_reads:?}"
    );
    assert!(
        large_windows.iter().all(|row| row.bytes_hashed == 0),
        "pre-execution window read content: {large_windows:?}"
    );
    for (phase, reads) in [
        ("initial", &initial_reads),
        ("warm", &warm_reads),
        ("dirty", &dirty_reads),
    ] {
        assert!(
            reads.iter().any(|row| row.kind == "content"
                && row.input_bytes >= LARGE_INPUT_BYTES
                && row.bytes_hashed >= LARGE_INPUT_BYTES),
            "{phase} omitted full content hashing: {reads:?}"
        );
    }
    assert!(
        !warm_reads
            .iter()
            .any(|row| row.kind == "window" && row.input_bytes >= LARGE_INPUT_BYTES),
        "warm replay executed a large-input window: {warm_reads:?}"
    );
    let evidence = serde_json::json!({
        "declared_blob_bytes":LARGE_INPUT_BYTES,"script_runs_after_initial":1,"script_runs_after_warm":1,"script_runs_after_forced_rerun":2,
        "dirty_window_rows":large_windows.len(),"dirty_window_nominal_bytes":large_windows.iter().map(|row|row.input_bytes).sum::<u64>(),
        "dirty_window_bytes_hashed":large_windows.iter().map(|row|row.bytes_hashed).sum::<u64>(),
        "dirty_content_bytes_hashed":dirty_reads.iter().filter(|row|row.kind=="content").map(|row|row.bytes_hashed).sum::<u64>(),
        "warm_content_bytes_hashed":warm_reads.iter().filter(|row|row.kind=="content").map(|row|row.bytes_hashed).sum::<u64>(),
        "unrelated_script_runs":1,"unrelated_rlib_identity_and_bytes_preserved":true
    });
    write(
        &world.path().join("window-input-bytes.json"),
        serde_json::to_vec_pretty(&evidence).unwrap(),
    );
    eprintln!("actual build-script input byte observations: {evidence}");
    world.passed();
}

#[test]
fn declared_directory_warm_capture_reports_metadata_work() {
    const FILES: u64 = 256;
    const DIRECTORIES: u64 = 8;
    const ENTRIES: u64 = 1 + DIRECTORIES + FILES;
    const INPUT_BYTES: u64 = FILES * 4;
    let world = World::new();
    let (root, _) = fixture(world.path(), Some("schema/many"));
    let tree = root.join("generated/schema/many");
    for index in 0..FILES {
        write(
            &tree.join(format!("d{:02}/v{:02}", index / 32, index % 32)),
            b"111\n",
        );
    }
    write(
        &root.join("generated/build.rs"),
        format!(
            r#"
fn main() {{
    println!("cargo:rerun-if-changed=schema/many");
    let count=std::path::PathBuf::from({count:?});
    let previous=std::fs::read_to_string(&count).unwrap().trim().parse::<u32>().unwrap();
    std::fs::write(count,format!("{{}}\n",previous+1)).unwrap();
    let mut files=Vec::new();
    let directories=std::fs::read_dir("schema/many").unwrap().map(|entry|entry.unwrap().path()).collect::<Vec<_>>();
    assert_eq!(directories.len(),{DIRECTORIES});
    for directory in directories {{
        assert!(directory.is_dir());
        files.extend(std::fs::read_dir(directory).unwrap().map(|entry|entry.unwrap().path()));
    }}
    files.sort();
    assert_eq!(files.len(),{FILES});
    let value=files.iter().map(|path|std::fs::read_to_string(path).unwrap().trim().parse::<u32>().unwrap()).sum::<u32>();
    std::fs::write(std::path::PathBuf::from(std::env::var_os("OUT_DIR").unwrap()).join("generated.rs"),format!("pub const VALUE:u32={{value}};")).unwrap();
}}
"#,
            count = world.path().join("generated.count")
        ),
    );
    git(
        &root,
        &["add", "generated/build.rs", "generated/schema/many"],
    );
    git(
        &root,
        &[
            "commit",
            "-qm",
            "declared tracked directory metadata fixture",
        ],
    );

    let initial = traced_build(world.path(), &root, "metadata-initial", "1", "root-1");
    assert_eq!(execute(&root), b"root-1 28416 77\n");
    assert_eq!(
        fs::read(world.path().join("generated.count")).unwrap(),
        b"1\n"
    );
    let unrelated = unrelated_artifact(&root, &initial.stdout);
    let warm = traced_build(world.path(), &root, "metadata-warm", "1", "root-1");
    assert_eq!(execute(&root), b"root-1 28416 77\n");
    assert_eq!(
        fs::read(world.path().join("generated.count")).unwrap(),
        b"1\n"
    );
    assert_eq!(unrelated_artifact(&root, &warm.stdout), unrelated);

    let edited = tree.join("d00/v00");
    let metadata = fs::metadata(&edited).unwrap();
    let modified = FileTime::from_last_modification_time(&metadata);
    write(&edited, b"222\n");
    git(&root, &["add", "generated/schema/many/d00/v00"]);
    git(&root, &["commit", "-qm", "same-size directory member edit"]);
    filetime::set_file_mtime(&edited, modified).unwrap();
    assert_eq!(fs::metadata(&edited).unwrap().len(), metadata.len());
    assert_eq!(
        FileTime::from_last_modification_time(&fs::metadata(&edited).unwrap()),
        modified
    );
    let changed = traced_build(world.path(), &root, "metadata-changed", "1", "root-2");
    assert_eq!(execute(&root), b"root-2 28527 77\n");
    assert_eq!(
        fs::read(world.path().join("generated.count")).unwrap(),
        b"2\n"
    );
    assert_eq!(unrelated_artifact(&root, &changed.stdout), unrelated);
    let warm_changed = traced_build(world.path(), &root, "metadata-changed-warm", "1", "root-2");
    assert_eq!(execute(&root), b"root-2 28527 77\n");
    assert_eq!(
        fs::read(world.path().join("generated.count")).unwrap(),
        b"2\n"
    );
    assert_eq!(
        fs::read(world.path().join("unchanged.count")).unwrap(),
        b"1\n"
    );
    assert_eq!(unrelated_artifact(&root, &warm_changed.stdout), unrelated);

    // Scope every work row to the first unchanged warm driver's exact declared
    // directory: one root, eight directories, 256 files and 1,024 data bytes.
    // Cold, dirty, implicit-package and unrelated captures are not aggregated.
    let work = directory_metadata_work(&warm.stderr, ENTRIES, INPUT_BYTES);
    let evidence = serde_json::json!({
        "tracked_files":FILES,"directory_entries":ENTRIES,"declared_file_bytes":INPUT_BYTES,
        "phase":"metadata-warm","capture_kind":"content","warm_directory_capture_count":work.len(),
        "warm_directory_captures":work,
        "metadata_reads_scope":"scanner symlink_metadata attempts; excludes open/fstat/readdir",
        "script_runs_after_initial":1,"script_runs_after_warm":1,"script_runs_after_edit":2,"script_runs_after_edited_warm":2,
        "unrelated_script_runs":1,"unrelated_rlib_identity_and_bytes_preserved":true
    });
    write(
        &world.path().join("directory-metadata-work.json"),
        serde_json::to_vec_pretty(&evidence).unwrap(),
    );
    eprintln!("actual warm declared-directory metadata work: {evidence}");
    assert!(
        !work.is_empty(),
        "no exact warm directory capture in actual trace"
    );
    for row in &work {
        // Nominal bytes can also include link spelling in a parent alias.
        assert!(row.input_bytes >= INPUT_BYTES);
        assert_eq!(
            row.bytes_hashed, INPUT_BYTES,
            "warm capture must still hash full content"
        );
        assert!(
            row.metadata_reads > 0
                && row.resolution_steps > 0
                && row.observations > 0
                && row.revalidations > 0,
            "missing actual scanner work: {row:?}"
        );
        // The measured baseline used 6,340 reads and 3,170 revalidations.
        // Shared ancestry must leave work proportional to distinct input nodes;
        // preserve the actual receipt above before either budget can fail.
        assert!(
            row.metadata_reads <= 4 * row.entries + 64,
            "warm directory metadata work exceeds budget: {row:?}"
        );
        assert!(
            row.revalidations <= row.entries + 32,
            "warm directory revalidation work exceeds budget: {row:?}"
        );
    }
    world.passed();
}

#[test]
fn cache_work_report_attributes_native_cold_warm_edit_and_uncacheable_inputs() {
    let world = World::new();
    let (root, input) = fixture(world.path(), Some("schema/value"));
    // Both future declarations are known to the original cold inventory.
    // A missing newly printed path could legitimately prevent enrollment.
    let cycle = root.join("generated/schema/cycle");
    write(&cycle, b"000\n");
    write(
        &root.join("generated/build.rs"),
        format!(
            r#"
fn main() {{
    println!("cargo:rerun-if-changed=schema/value");
    println!("cargo:rerun-if-changed=schema/cycle");
    let count=std::path::PathBuf::from({count:?});
    let previous=std::fs::read_to_string(&count).unwrap().trim().parse::<u32>().unwrap();
    std::fs::write(count,format!("{{}}\n",previous+1)).unwrap();
    // The scanner must report the declared cycle without this script trying
    // to read it. Successful compilation is independent of cacheability.
    let value=std::fs::read_to_string("schema/value").unwrap().trim().parse::<u32>().unwrap();
    std::fs::write(std::path::PathBuf::from(std::env::var_os("OUT_DIR").unwrap()).join("generated.rs"),format!("pub const VALUE:u32={{value}};")).unwrap();
}}
"#,
            count = world.path().join("generated.count")
        ),
    );
    git(
        &root,
        &["add", "generated/build.rs", "generated/schema/cycle"],
    );
    git(&root, &["commit", "-qm", "native cache-work report inputs"]);
    fs::create_dir_all(world.path().join("analysis-home/log")).unwrap();

    let cold = cache_work_phase(world.path(), &root, "analysis-cold", "root-1");
    assert_eq!(execute(&root), b"root-1 111 77\n");
    assert_eq!(
        fs::read(world.path().join("generated.count")).unwrap(),
        b"1\n"
    );
    let unrelated = unrelated_artifact(&root, &cold.build.stdout);
    let warm = cache_work_phase(world.path(), &root, "analysis-warm", "root-1");
    assert_eq!(execute(&root), b"root-1 111 77\n");
    assert_eq!(
        fs::read(world.path().join("generated.count")).unwrap(),
        b"1\n"
    );
    assert_eq!(unrelated_artifact(&root, &warm.build.stdout), unrelated);

    let metadata = fs::metadata(&input).unwrap();
    let modified = FileTime::from_last_modification_time(&metadata);
    write(&input, b"222\n");
    git(&root, &["add", "generated/schema/value"]);
    git(&root, &["commit", "-qm", "same-size reported input edit"]);
    filetime::set_file_mtime(&input, modified).unwrap();
    assert_eq!(fs::metadata(&input).unwrap().len(), metadata.len());
    assert_eq!(
        FileTime::from_last_modification_time(&fs::metadata(&input).unwrap()),
        modified
    );
    let edit = cache_work_phase(world.path(), &root, "analysis-edit", "root-2");
    assert_eq!(execute(&root), b"root-2 222 77\n");
    assert_eq!(
        fs::read(world.path().join("generated.count")).unwrap(),
        b"2\n"
    );
    assert_eq!(unrelated_artifact(&root, &edit.build.stdout), unrelated);

    fs::remove_file(&cycle).unwrap();
    std::os::unix::fs::symlink("cycle", &cycle).unwrap();
    git(&root, &["add", "generated/schema/cycle"]);
    git(
        &root,
        &["commit", "-qm", "uncacheable declared input cycle"],
    );
    let loop_first = cache_work_phase(world.path(), &root, "analysis-cycle-first", "root-2");
    assert_eq!(execute(&root), b"root-2 222 77\n");
    assert_eq!(
        fs::read(world.path().join("generated.count")).unwrap(),
        b"3\n"
    );
    assert_eq!(
        unrelated_artifact(&root, &loop_first.build.stdout),
        unrelated
    );
    let loop_repeat = cache_work_phase(world.path(), &root, "analysis-cycle-repeat", "root-2");
    assert_eq!(execute(&root), b"root-2 222 77\n");
    assert_eq!(
        fs::read(world.path().join("generated.count")).unwrap(),
        b"4\n"
    );
    assert_eq!(
        fs::read(world.path().join("unchanged.count")).unwrap(),
        b"1\n"
    );
    assert_eq!(
        unrelated_artifact(&root, &loop_repeat.build.stdout),
        unrelated
    );

    let phases = [
        ("cold", &cold),
        ("warm", &warm),
        ("edit", &edit),
        ("cycle-first", &loop_first),
        ("cycle-repeat", &loop_repeat),
    ];
    let evidence: Vec<_> = phases
        .iter()
        .map(|(name, phase)| serde_json::json!({"phase":name,"report":phase.report}))
        .collect();
    write(
        &world.path().join("native-cache-work-reports.json"),
        serde_json::to_vec_pretty(&evidence).unwrap(),
    );
    // Native runtime/counter/artifact observations above remain independent of
    // these informational costs. Reports carry no compilation proof authority.
    for (_, phase) in phases {
        checked_cache_work_report(phase);
        assert_eq!(
            work_number(
                script_work(phase, &root, "unchanged"),
                "uncacheable_attempts"
            ),
            0
        );
    }
    for phase in [&cold, &edit] {
        let generated = script_work(phase, &root, "generated");
        for name in ["execution-window", "publication"] {
            assert!(
                generated["phases"].as_array().unwrap().iter().any(|cost| {
                    cost["phase"] == name && work_number(cost, "captured_attempts") > 0
                }),
                "missing actual {name} cost: {generated}"
            );
        }
    }
    let generated = script_work(&warm, &root, "generated");
    let warm_costs = generated["phases"].as_array().unwrap();
    assert!(
        warm_costs
            .iter()
            .all(|cost| cost["phase"] != "execution-window")
    );
    assert!(
        warm_costs
            .iter()
            .any(|cost| cost["phase"] == "freshness" && work_number(cost, "captured_attempts") > 0)
    );
    assert!(work_number(&generated["work"], "bytes_hashed") >= 8);
    for phase in [&loop_first, &loop_repeat] {
        let generated = script_work(phase, &root, "generated");
        assert!(work_number(generated, "uncacheable_attempts") > 0);
        for field in ["metadata_reads", "resolution_steps", "link_reads"] {
            assert!(
                work_number(&generated["work"], field) > 0,
                "lost attempted work for cycle: {generated}"
            );
        }
    }
    eprintln!(
        "actual cache-work reports: {}",
        serde_json::to_string(&evidence).unwrap()
    );
    world.passed();
}

#[test]
fn genuine_verbose_capability_is_unique_and_not_a_nonverbose_claim() {
    let version = |verbose| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_targo"));
        command.arg0("targo").args(["--unverified", "--version"]);
        if verbose {
            command.arg("--verbose");
        }
        success(command.output().unwrap()).stdout
    };
    let verbose = String::from_utf8(version(true)).unwrap();
    assert!(verbose.starts_with("targo "));
    // Trust: the same internal codec is used by native and Cargo-compatible modes.
    let codec = format!(
        "encoded-dep-info-version: {}",
        targo::encoded_dep_info_version()
    );
    assert_eq!(verbose.lines().filter(|line| *line == codec).count(), 1);
    assert!(
        !String::from_utf8(version(false))
            .unwrap()
            .contains("encoded-dep-info-version:")
    );
    assert_eq!(
        verbose
            .lines()
            .filter(|line| *line == "freshness: rust-and-build-input-content-v1")
            .count(),
        1
    );
    assert_eq!(
        verbose
            .lines()
            .filter(|line| *line == "analysis-session: build-json-v1")
            .count(),
        1
    );
    assert!(
        !String::from_utf8(version(false))
            .unwrap()
            .contains("freshness:")
    );
    assert!(
        !String::from_utf8(version(false))
            .unwrap()
            .contains("analysis-session:")
    );
    // Trust: a bare argv[0] resolves through PATH, so give the identity guard
    // a real compatibility alias to this exact executable.
    let world = World::new();
    let alias = world.path().join("cargo");
    std::os::unix::fs::symlink(env!("CARGO_BIN_EXE_targo"), &alias).unwrap();
    let mut compatibility = Command::new(&alias);
    compatibility.args(["--version", "--verbose"]);
    let compatibility = String::from_utf8(success(compatibility.output().unwrap()).stdout).unwrap();
    assert!(compatibility.starts_with("cargo "));
    assert!(!compatibility.contains("analysis-session:"));
    assert_eq!(
        compatibility.lines().filter(|line| *line == codec).count(),
        1
    );
    let mut terse_compatibility = Command::new(&alias);
    terse_compatibility.arg("--version");
    assert!(
        !String::from_utf8(success(terse_compatibility.output().unwrap()).stdout)
            .unwrap()
            .contains("encoded-dep-info-version:")
    );
    world.passed();
}

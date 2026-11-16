// Trust: generated build-script data must remain a reusable producer fact.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

#![cfg(unix)]

use std::fs;
use std::os::unix::process::CommandExt as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use filetime::FileTime;
use serde_json::Value;

struct World(Option<tempfile::TempDir>);
impl World {
    fn new() -> Self {
        Self(Some(
            tempfile::Builder::new()
                .prefix("targo-generated-output-")
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
                "kept failed generated-output world: {}",
                world.keep().display()
            );
        }
    }
}
fn write(path: &Path, bytes: impl AsRef<[u8]>) {
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, bytes).unwrap();
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
fn main_source(root: &Path, phase: &str) {
    write(
        &root.join("src/main.rs"),
        format!(
            "include!(concat!(env!(\"OUT_DIR\"),\"/generated.rs\"));\nfn main(){{println!(\"{phase} {{}}\",VALUE);}}\n"
        ),
    );
}
fn fixture(world: &Path, conditional: bool, unsupported_link: bool) -> PathBuf {
    let root = world.join("source");
    // Instrumentation must not create a new sibling during the observed
    // action: that changes an input ancestor's stamp and correctly prevents
    // first-run reuse even without any generated-output corruption.
    write(&world.join("producer.count"), b"0\n");
    write(
        &root.join("Cargo.toml"),
        "[package]\nname='generated-output'\nversion='0.1.0'\nedition='2024'\n[workspace]\n",
    );
    write(&root.join("schema"), b"111\n");
    write(
        &root.join("build.rs"),
        format!(
            r#"
fn main() {{
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=schema");
    let value:u32=std::fs::read_to_string("schema").unwrap().trim().parse().unwrap();
    let out=std::path::PathBuf::from(std::env::var_os("OUT_DIR").unwrap());
    let generated=out.join("generated.rs");
    if !{conditional} || !generated.exists() {{
        std::fs::write(&generated,format!("pub const VALUE:u32={{}};\n",value)).unwrap();
    }}
    std::fs::write(out.join("member"),b"producer-owned").unwrap();
    if {unsupported_link} && !out.join("unsupported-link").exists() {{
        std::os::unix::fs::symlink({victim:?},out.join("unsupported-link")).unwrap();
    }}
    let counter=std::path::Path::new({counter:?});
    let old=std::fs::read_to_string(counter).unwrap_or_default().trim().parse::<u32>().unwrap_or(0);
    std::fs::write(counter,format!("{{}}\n",old+1)).unwrap();
}}
"#,
            counter = world.join("producer.count"),
            victim = world.join("foreign-victim")
        ),
    );
    main_source(&root, "phase-1");
    root
}
struct Built {
    main: PathBuf,
    out_dir: PathBuf,
}
fn build(world: &Path, root: &Path, label: &str) -> Built {
    let mut command = Command::new(env!("CARGO_BIN_EXE_targo"));
    command
        .arg0("targo")
        .current_dir(root)
        .args([
            "--unverified",
            "-Zchecksum-freshness",
            "--config",
            "build.fingerprint=\"content\"",
            "build",
            "--offline",
            "--message-format=json",
            "-j",
            "2",
        ])
        .env("CARGO_TARGET_DIR", world.join("target.noindex"));
    for name in [
        "CARGO_MAKEFLAGS",
        "MAKEFLAGS",
        "MFLAGS",
        "RUSTC_WRAPPER",
        "RUSTC_WORKSPACE_WRAPPER",
    ] {
        command.env_remove(name);
    }
    let output = command.output().unwrap();
    write(&world.join(format!("{label}.stdout")), &output.stdout);
    write(&world.join(format!("{label}.stderr")), &output.stderr);
    let output = success(output);
    let mut mains = Vec::new();
    let mut out_dirs = Vec::new();
    for line in output
        .stdout
        .split(|byte| *byte == b'\n')
        .filter(|line| !line.is_empty())
    {
        let message: Value = serde_json::from_slice(line).unwrap();
        if message["reason"] == "build-script-executed" {
            out_dirs.push(PathBuf::from(message["out_dir"].as_str().unwrap()));
        }
        if message["reason"] == "compiler-artifact"
            && message["target"]["kind"]
                .as_array()
                .unwrap()
                .iter()
                .any(|kind| kind == "bin")
        {
            mains.push(PathBuf::from(message["executable"].as_str().unwrap()));
        }
    }
    assert_eq!(mains.len(), 1, "expected actual emitted program JSON");
    assert_eq!(out_dirs.len(), 1, "expected compiler-selected OUT_DIR JSON");
    Built {
        main: mains.remove(0),
        out_dir: out_dirs.remove(0),
    }
}
fn execute(built: &Built) -> Vec<u8> {
    success(Command::new(&built.main).output().unwrap()).stdout
}

fn run_poison(conditional: bool) {
    let world = World::new();
    let root = fixture(world.path(), conditional, false);
    let first = build(world.path(), &root, "first");
    assert_eq!(execute(&first), b"phase-1 111\n");
    assert_eq!(
        fs::read(world.path().join("producer.count")).unwrap(),
        b"1\n"
    );
    let warm = build(world.path(), &root, "warm");
    assert_eq!(execute(&warm), b"phase-1 111\n");
    assert_eq!(warm.out_dir, first.out_dir);
    assert_eq!(
        fs::read(world.path().join("producer.count")).unwrap(),
        b"1\n"
    );

    let generated = first.out_dir.join("generated.rs");
    let original = fs::read_to_string(&generated).unwrap();
    let changed = original.replace("VALUE:u32=111", "VALUE:u32=222");
    assert_ne!(original, changed);
    assert_eq!(original.len(), changed.len());
    let modified = FileTime::from_last_modification_time(&fs::metadata(&generated).unwrap());
    fs::write(&generated, changed).unwrap();
    filetime::set_file_mtime(&generated, modified).unwrap();
    assert_eq!(
        FileTime::from_last_modification_time(&fs::metadata(&generated).unwrap()),
        modified
    );
    main_source(&root, "phase-2");
    let after = build(world.path(), &root, "altered-generated");
    assert_eq!(after.out_dir, first.out_dir);
    let actual = execute(&after);
    let count = fs::read(world.path().join("producer.count")).unwrap();
    assert_eq!(
        (actual, count),
        (b"phase-2 111\n".to_vec(), b"2\n".to_vec()),
        "altered generated data reached consuming compilation without rerunning its actual producer"
    );
    let warm = build(world.path(), &root, "restored-warm");
    assert_eq!(execute(&warm), b"phase-2 111\n");
    assert_eq!(
        fs::read(world.path().join("producer.count")).unwrap(),
        b"2\n"
    );
    world.passed();
}

#[test]
fn changed_generated_rust_is_recomputed_before_consuming_compilation() {
    run_poison(false);
}

#[test]
fn conditional_producer_cannot_reuse_a_poisoned_generation() {
    run_poison(true);
}

#[test]
fn ordinary_input_driven_reexecution_preserves_a_valid_prior_generation() {
    let world = World::new();
    let root = fixture(world.path(), true, false);
    let first = build(world.path(), &root, "first");
    assert_eq!(execute(&first), b"phase-1 111\n");
    assert_eq!(
        fs::read(world.path().join("producer.count")).unwrap(),
        b"1\n"
    );
    // This producer intentionally retains an existing generated value. Normal
    // input-driven dirty execution must preserve Cargo's persistent OUT_DIR.
    write(&root.join("schema"), b"222\n");
    main_source(&root, "phase-2");
    let after = build(world.path(), &root, "input-driven");
    assert_eq!(execute(&after), b"phase-2 111\n");
    assert_eq!(
        fs::read(world.path().join("producer.count")).unwrap(),
        b"2\n"
    );
    let warm = build(world.path(), &root, "warm");
    assert_eq!(execute(&warm), b"phase-2 111\n");
    assert_eq!(
        fs::read(world.path().join("producer.count")).unwrap(),
        b"2\n"
    );
    world.passed();
}

#[test]
fn generated_directory_membership_is_checked_independently_of_source_changes() {
    let world = World::new();
    let root = fixture(world.path(), false, false);
    let first = build(world.path(), &root, "first");
    assert_eq!(execute(&first), b"phase-1 111\n");
    let warm = build(world.path(), &root, "warm");
    assert_eq!(
        fs::read(world.path().join("producer.count")).unwrap(),
        b"1\n"
    );
    let unexpected = warm.out_dir.join("unexpected");
    write(&unexpected, b"not a recorded generation member");
    let added = build(world.path(), &root, "added-member");
    assert_eq!(execute(&added), b"phase-1 111\n");
    assert_eq!(
        fs::read(world.path().join("producer.count")).unwrap(),
        b"2\n"
    );
    assert!(
        !unexpected.exists(),
        "unrecorded members must not be re-blessed into a repaired generation"
    );
    fs::remove_file(added.out_dir.join("member")).unwrap();
    let removed = build(world.path(), &root, "missing-member");
    assert_eq!(execute(&removed), b"phase-1 111\n");
    assert_eq!(
        fs::read(world.path().join("producer.count")).unwrap(),
        b"3\n"
    );
    assert_eq!(
        fs::read(removed.out_dir.join("member")).unwrap(),
        b"producer-owned"
    );
    let warm = build(world.path(), &root, "restored-warm");
    assert_eq!(execute(&warm), b"phase-1 111\n");
    assert_eq!(
        fs::read(world.path().join("producer.count")).unwrap(),
        b"3\n"
    );
    world.passed();
}

#[test]
fn unsupported_generated_link_keeps_actual_builds_working_without_touching_its_victim() {
    use std::os::unix::fs::MetadataExt as _;
    let world = World::new();
    let victim = world.path().join("foreign-victim");
    write(&victim, b"untouched");
    let original = fs::metadata(&victim).unwrap();
    let root = fixture(world.path(), false, true);
    let first = build(world.path(), &root, "first");
    assert_eq!(execute(&first), b"phase-1 111\n");
    assert_eq!(
        fs::read(world.path().join("producer.count")).unwrap(),
        b"1\n"
    );
    let next = build(world.path(), &root, "uncacheable-repeat");
    assert_eq!(execute(&next), b"phase-1 111\n");
    assert_eq!(
        fs::read(world.path().join("producer.count")).unwrap(),
        b"2\n"
    );
    let current = fs::metadata(&victim).unwrap();
    assert_eq!(
        (original.dev(), original.ino()),
        (current.dev(), current.ino())
    );
    assert_eq!(fs::read(&victim).unwrap(), b"untouched");
    world.passed();
}

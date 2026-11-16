// Trust: cached build-script directives must remain the actual successful output.
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
                .prefix("targo-script-output-")
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
                "kept failed script-output world: {}",
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
        format!("fn main(){{println!(\"{phase} {{}}\",env!(\"VALUE\"));}}\n"),
    );
}
fn build(root: &Path, label: &str) {
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
            "-j",
            "2",
        ])
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
    let output = command.output().unwrap();
    write(
        &root.parent().unwrap().join(format!("{label}.stdout")),
        &output.stdout,
    );
    write(
        &root.parent().unwrap().join(format!("{label}.stderr")),
        &output.stderr,
    );
    success(output);
}
fn execute(world: &Path) -> Vec<u8> {
    success(
        Command::new(world.join("target.noindex/debug/cache-directives"))
            .output()
            .unwrap(),
    )
    .stdout
}
fn find_output(path: &Path, depth: usize) -> Vec<PathBuf> {
    assert!(depth < 20, "unexpected target directory depth");
    let mut found = Vec::new();
    for entry in fs::read_dir(path).unwrap() {
        let entry = entry.unwrap();
        let kind = entry.file_type().unwrap();
        if kind.is_dir() {
            found.extend(find_output(&entry.path(), depth + 1));
        } else if kind.is_file() && matches!(entry.file_name().to_str(), Some("output" | "stdout"))
        {
            let bytes = fs::read(entry.path()).unwrap();
            if bytes
                .windows(b"rustc-env=VALUE=111".len())
                .any(|w| w == b"rustc-env=VALUE=111")
            {
                found.push(entry.path());
            }
        }
    }
    found
}

fn fixture(world: &Path, declared: bool) -> PathBuf {
    let root = world.join("source");
    // Keep instrumentation from changing an input ancestor during execution.
    // A newly created sibling correctly prevents first-run cache reuse.
    write(&world.join("script.count"), b"0\n");
    write(
        &root.join("Cargo.toml"),
        "[package]\nname='cache-directives'\nversion='0.1.0'\nedition='2024'\n[workspace]\n",
    );
    write(
        &root.join("build.rs"),
        format!(
            r#"
fn main() {{
    {declaration}
    println!("cargo:rustc-env=VALUE=111");
    let counter=std::path::Path::new({counter:?});
    let old=std::fs::read_to_string(counter).unwrap_or_default().trim().parse::<u32>().unwrap_or(0);
    std::fs::write(counter,format!("{{}}\n",old+1)).unwrap();
}}
"#,
            counter = world.join("script.count"),
            declaration = if declared {
                "println!(\"cargo:rerun-if-changed=build.rs\");"
            } else {
                ""
            },
        ),
    );
    main_source(&root, "phase-1");
    root
}

#[test]
fn altered_cached_directives_are_recomputed_before_the_compiler_can_use_them() {
    let world = World::new();
    let root = fixture(world.path(), true);
    build(&root, "first");
    assert_eq!(execute(world.path()), b"phase-1 111\n");
    build(&root, "warm");
    assert_eq!(fs::read(world.path().join("script.count")).unwrap(), b"1\n");
    let outputs = find_output(&world.path().join("target.noindex"), 0);
    assert_eq!(
        outputs.len(),
        1,
        "expected one actual build-script output: {outputs:?}"
    );
    let output = &outputs[0];
    let modified = FileTime::from_last_modification_time(&fs::metadata(output).unwrap());
    let original = fs::read_to_string(output).unwrap();
    let changed = original.replace("rustc-env=VALUE=111", "rustc-env=VALUE=222");
    assert_ne!(changed, original);
    assert_eq!(changed.len(), original.len());
    fs::write(output, changed).unwrap();
    filetime::set_file_mtime(output, modified).unwrap();
    assert_eq!(
        FileTime::from_last_modification_time(&fs::metadata(output).unwrap()),
        modified
    );
    main_source(&root, "phase-2");
    build(&root, "altered-output");
    let actual = execute(world.path());
    let count = fs::read(world.path().join("script.count")).unwrap();
    assert_eq!(
        (actual, count),
        (b"phase-2 111\n".to_vec(), b"2\n".to_vec()),
        "altered directives reached a compiler without rerunning the actual script"
    );
    build(&root, "restored-warm");
    assert_eq!(execute(world.path()), b"phase-2 111\n");
    assert_eq!(fs::read(world.path().join("script.count")).unwrap(), b"2\n");

    let root_output = output.parent().unwrap().join("root-output");
    let modified = FileTime::from_last_modification_time(&fs::metadata(&root_output).unwrap());
    let mut bytes = fs::read(&root_output).unwrap();
    *bytes.last_mut().unwrap() = b'x';
    fs::write(&root_output, bytes).unwrap();
    filetime::set_file_mtime(&root_output, modified).unwrap();
    main_source(&root, "phase-3");
    build(&root, "altered-relocation");
    assert_eq!(execute(world.path()), b"phase-3 111\n");
    assert_eq!(fs::read(world.path().join("script.count")).unwrap(), b"3\n");

    let victim = world.path().join("foreign-victim");
    let foreign = fs::read_to_string(output)
        .unwrap()
        .replace("rustc-env=VALUE=111", "rustc-env=VALUE=222");
    write(&victim, &foreign);
    fs::remove_file(output).unwrap();
    std::os::unix::fs::symlink(&victim, output).unwrap();
    main_source(&root, "phase-4");
    build(&root, "linked-output");
    assert_eq!(execute(world.path()), b"phase-4 111\n");
    assert_eq!(fs::read(world.path().join("script.count")).unwrap(), b"4\n");
    assert_eq!(fs::read(&victim).unwrap(), foreign.as_bytes());
    world.passed();
}

#[test]
fn an_implicit_script_with_unchanged_inputs_still_requires_a_valid_output_receipt() {
    let world = World::new();
    let root = fixture(world.path(), false);
    build(&root, "first");
    assert_eq!(execute(world.path()), b"phase-1 111\n");
    build(&root, "warm");
    assert_eq!(fs::read(world.path().join("script.count")).unwrap(), b"1\n");
    let outputs = find_output(&world.path().join("target.noindex"), 0);
    assert_eq!(outputs.len(), 1);
    let receipt = outputs[0]
        .parent()
        .unwrap()
        .join("output-integrity-v2.json");
    fs::remove_file(&receipt).unwrap();
    build(&root, "missing-receipt");
    assert_eq!(fs::read(world.path().join("script.count")).unwrap(), b"2\n");
    fs::write(&receipt, b"{}").unwrap();
    build(&root, "malformed-receipt");
    assert_eq!(fs::read(world.path().join("script.count")).unwrap(), b"3\n");
    let mut old: serde_json::Value = serde_json::from_slice(&fs::read(&receipt).unwrap()).unwrap();
    old["schema"] = 0.into();
    fs::write(&receipt, serde_json::to_vec(&old).unwrap()).unwrap();
    build(&root, "old-receipt");
    assert_eq!(fs::read(world.path().join("script.count")).unwrap(), b"4\n");
    build(&root, "repaired-warm");
    assert_eq!(fs::read(world.path().join("script.count")).unwrap(), b"4\n");
    assert_eq!(execute(world.path()), b"phase-1 111\n");
    world.passed();
}

#[test]
fn genuine_verbose_output_integrity_capability_is_unique_and_absent_from_nonverbose() {
    let version = |verbose| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_targo"));
        command.arg0("targo").args(["--unverified", "--version"]);
        if verbose {
            command.arg("--verbose");
        }
        String::from_utf8(success(command.output().unwrap()).stdout).unwrap()
    };
    let verbose = version(true);
    assert!(verbose.starts_with("targo "));
    for capability in [
        "freshness: rust-and-build-input-content-v1",
        "cache-integrity: build-script-control-output-v1",
        "cache-integrity: compiled-build-script-executable-v1",
        "cache-integrity: build-script-generated-tree-v1",
    ] {
        assert_eq!(
            verbose.lines().filter(|line| *line == capability).count(),
            1
        );
        assert!(!version(false).contains(capability));
    }
}

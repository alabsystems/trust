// Trust: compiler output integrity also applies to the executable build.rs unit.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

#![cfg(unix)]

use std::fs;
use std::io::Read as _;
use std::os::unix::{fs::MetadataExt as _, process::CommandExt as _};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use cargo_util::Sha256;
use filetime::FileTime;
use serde_json::Value;

struct World(Option<tempfile::TempDir>);
impl World {
    fn new() -> Self {
        Self(Some(
            tempfile::Builder::new()
                .prefix("targo-script-executable-")
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
                "kept failed script-executable world: {}",
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
fn fixture(world: &Path, name: &str, base: u32) -> PathBuf {
    let root = world.join(name);
    write(
        &root.join("Cargo.toml"),
        format!("[package]\nname='{name}'\nversion='0.1.0'\nedition='2024'\n[workspace]\n"),
    );
    write(
        &root.join("build.rs"),
        format!(
            r#"
fn main() {{
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=trigger");
    let trigger:u32=std::fs::read_to_string("trigger").unwrap().trim().parse().unwrap();
    println!("cargo:rustc-env=VALUE={{}}",{base}+trigger);
    let counter=std::path::Path::new({counter:?});
    let old=std::fs::read_to_string(counter).unwrap_or_default().trim().parse::<u32>().unwrap_or(0);
    std::fs::write(counter,format!("{{}}\n",old+1)).unwrap();
}}
"#,
            counter = world.join("script.count")
        ),
    );
    write(&root.join("trigger"), b"0\n");
    main_source(&root, "phase-1");
    root
}
struct Built {
    main: PathBuf,
    script: PathBuf,
    script_fresh: bool,
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
        .env(
            "CARGO_TARGET_DIR",
            world.join(format!(
                "{}-target.noindex",
                root.file_name().unwrap().to_str().unwrap()
            )),
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
    write(&world.join(format!("{label}.stdout")), &output.stdout);
    write(&world.join(format!("{label}.stderr")), &output.stderr);
    let output = success(output);
    let mut mains = Vec::new();
    let mut scripts = Vec::new();
    for line in output
        .stdout
        .split(|byte| *byte == b'\n')
        .filter(|line| !line.is_empty())
    {
        let message: Value = serde_json::from_slice(line).unwrap();
        if message["reason"] != "compiler-artifact" {
            continue;
        }
        let kinds = message["target"]["kind"].as_array().unwrap();
        if kinds.iter().any(|kind| kind == "bin") {
            mains.push(PathBuf::from(message["executable"].as_str().unwrap()));
        }
        if kinds.iter().any(|kind| kind == "custom-build") {
            let paths = message["filenames"]
                .as_array()
                .unwrap()
                .iter()
                .map(|value| PathBuf::from(value.as_str().unwrap()))
                .filter(|path| {
                    fs::metadata(path)
                        .is_ok_and(|metadata| metadata.is_file() && metadata.mode() & 0o111 != 0)
                })
                .collect::<Vec<_>>();
            assert_eq!(
                paths.len(),
                1,
                "actual compiler artifact executable inventory: {message}"
            );
            scripts.push((paths[0].clone(), message["fresh"].as_bool().unwrap()));
        }
    }
    assert_eq!(mains.len(), 1, "actual emitted main artifact missing");
    assert_eq!(scripts.len(), 1, "actual compiled script artifact missing");
    Built {
        main: mains.remove(0),
        script: scripts[0].0.clone(),
        script_fresh: scripts[0].1,
    }
}
fn execute(built: &Built) -> Vec<u8> {
    success(Command::new(&built.main).output().unwrap()).stdout
}
fn digest(path: &Path) -> String {
    let mut file = fs::File::open(path).unwrap();
    assert!(
        file.metadata().unwrap().len() <= 64 * 1024 * 1024,
        "unexpected fixture executable size"
    );
    let mut hash = Sha256::new();
    let mut buffer = [0; 64 * 1024];
    loop {
        let n = file.read(&mut buffer).unwrap();
        if n == 0 {
            break;
        }
        hash.update(&buffer[..n]);
    }
    hash.finish_hex()
}

#[test]
fn a_replaced_compiled_build_script_is_rebuilt_before_its_next_real_execution() {
    let world = World::new();
    let a = fixture(world.path(), "script-original", 111);
    let b = fixture(world.path(), "script-replacement", 222);
    // The execution window retains ancestor namespace stamps. Creating this
    // counter during the first script run would invalidate the input snapshot
    // and legitimately rerun it on the next build. Keep that unrelated setup
    // outside the window; the warm execution and replacement controls stay exact.
    write(&world.path().join("script.count"), b"0\n");
    let first = build(world.path(), &a, "a-first");
    assert!(!first.script_fresh);
    assert_eq!(execute(&first), b"phase-1 111\n");
    assert_eq!(fs::read(world.path().join("script.count")).unwrap(), b"1\n");
    let warm = build(world.path(), &a, "a-warm");
    assert!(warm.script_fresh);
    assert_eq!(execute(&warm), b"phase-1 111\n");
    assert_eq!(fs::read(world.path().join("script.count")).unwrap(), b"1\n");

    let replacement = build(world.path(), &b, "b-first");
    assert!(!replacement.script_fresh);
    assert_eq!(execute(&replacement), b"phase-1 222\n");
    assert_eq!(fs::read(world.path().join("script.count")).unwrap(), b"2\n");
    let original = fs::metadata(&first.script).unwrap();
    let replacement_identity = fs::metadata(&replacement.script).unwrap();
    let replacement_digest = digest(&replacement.script);
    assert_ne!(digest(&first.script), replacement_digest);
    assert_ne!(
        (original.dev(), original.ino()),
        (replacement_identity.dev(), replacement_identity.ino())
    );

    // Both actual builds and their actual emitted programs have exited. Move
    // the original, already-executed replacement inode; never edit a live
    // executable in place or manufacture a copied Mach-O fixture.
    filetime::set_file_mtime(
        &replacement.script,
        FileTime::from_last_modification_time(&original),
    )
    .unwrap();
    fs::rename(&replacement.script, &first.script).unwrap();
    let selected = fs::metadata(&first.script).unwrap();
    assert_eq!(
        (selected.dev(), selected.ino()),
        (replacement_identity.dev(), replacement_identity.ino())
    );
    assert_eq!(
        FileTime::from_last_modification_time(&selected),
        FileTime::from_last_modification_time(&original)
    );
    assert_eq!(digest(&first.script), replacement_digest);
    write(&a.join("trigger"), b"1\n");
    main_source(&a, "phase-2");
    let after = build(world.path(), &a, "a-replaced");
    let actual = execute(&after);
    let count = fs::read(world.path().join("script.count")).unwrap();
    assert_eq!(
        (actual, count, after.script_fresh),
        (b"phase-2 112\n".to_vec(), b"3\n".to_vec(), false),
        "replaced compiler output was treated as a fresh executable"
    );
    let warm = build(world.path(), &a, "a-restored-warm");
    assert!(warm.script_fresh);
    assert_eq!(execute(&warm), b"phase-2 112\n");
    assert_eq!(fs::read(world.path().join("script.count")).unwrap(), b"3\n");
    world.passed();
}

// Trust: count generated-output hashing work without weakening byte validation.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

#![cfg(unix)]

use std::fs;
use std::io::Read as _;
use std::os::unix::{fs::MetadataExt as _, process::CommandExt as _};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::SystemTime;

use cargo_util::Sha256;
use filetime::FileTime;
use serde_json::Value;

const OUTPUT_TRACE: &str = "targo::compiler::fingerprint::build_script_output";
const BLOB_BYTES: u64 = 256 * 1024 * 1024;

struct World(Option<tempfile::TempDir>);
impl World {
    fn new() -> Self {
        Self(Some(
            tempfile::Builder::new()
                .prefix("targo-generated-reads-")
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
                "kept generated-read measurement world: {}",
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
fn fixture(world: &Path) -> PathBuf {
    let root = world.join("source");
    write(
        &root.join("Cargo.toml"),
        "[package]\nname='generated-reads'\nversion='0.1.0'\nedition='2024'\n[workspace]\n",
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
    std::fs::write(out.join("generated.rs"),format!("pub const VALUE:u32={{}};\n",value)).unwrap();
    std::fs::File::create(out.join("sparse-blob")).unwrap().set_len({BLOB_BYTES}).unwrap();
    let counter=std::path::Path::new({counter:?});
    let old=std::fs::read_to_string(counter).unwrap_or_default().trim().parse::<u32>().unwrap_or(0);
    std::fs::write(counter,format!("{{}}\n",old+1)).unwrap();
}}
"#,
            counter = world.join("producer.count")
        ),
    );
    main_source(&root, "phase-1");
    root
}

#[derive(Debug)]
struct Read {
    output_bytes: u64,
    bytes_hashed: u64,
    entries: u64,
}
fn reads(stderr: &[u8]) -> Vec<Read> {
    String::from_utf8_lossy(stderr)
        .lines()
        .filter(|line| {
            line.contains(OUTPUT_TRACE) && line.contains("observed generated output tree")
        })
        .map(|line| {
            let field = |name: &str| {
                line.split_whitespace()
                    .find_map(|word| word.strip_prefix(name))
                    .unwrap_or_else(|| panic!("missing {name} in actual output trace: {line}"))
                    .trim_matches('"')
                    .parse::<u64>()
                    .unwrap()
            };
            Read {
                output_bytes: field("output_bytes="),
                bytes_hashed: field("bytes_hashed="),
                entries: field("entries="),
            }
        })
        .collect()
}
struct Built {
    main: PathBuf,
    out_dir: PathBuf,
    reads: Vec<Read>,
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
        .env("CARGO_TARGET_DIR", world.join("target.noindex"))
        .env("CARGO_LOG", format!("{OUTPUT_TRACE}=debug"));
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
    assert_eq!(
        out_dirs.len(),
        1,
        "expected exactly one compiler-selected OUT_DIR unit"
    );
    Built {
        main: mains.remove(0),
        out_dir: out_dirs.remove(0),
        reads: reads(&output.stderr),
    }
}
fn execute(built: &Built) -> Vec<u8> {
    success(Command::new(&built.main).output().unwrap()).stdout
}
fn artifact(path: &Path) -> (u64, u64, u64, SystemTime, String) {
    let mut file = fs::File::open(path).unwrap();
    let metadata = file.metadata().unwrap();
    assert!(
        metadata.len() <= 64 * 1024 * 1024,
        "unexpected emitted fixture size"
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
    (
        metadata.dev(),
        metadata.ino(),
        metadata.len(),
        metadata.modified().unwrap(),
        hash.finish_hex(),
    )
}

#[test]
fn unchanged_warm_generated_output_is_fully_hashed_at_most_once_and_tampering_still_recovers() {
    let world = World::new();
    let root = fixture(world.path());
    let cold = build(world.path(), &root, "cold");
    assert_eq!(execute(&cold), b"phase-1 111\n");
    assert_eq!(
        fs::read(world.path().join("producer.count")).unwrap(),
        b"1\n"
    );
    assert_eq!(
        fs::metadata(cold.out_dir.join("sparse-blob"))
            .unwrap()
            .len(),
        BLOB_BYTES
    );
    let original_artifact = artifact(&cold.main);
    let warm = build(world.path(), &root, "warm");
    assert_eq!(execute(&warm), b"phase-1 111\n");
    assert_eq!(warm.main, cold.main);
    assert_eq!(warm.out_dir, cold.out_dir);
    assert_eq!(
        artifact(&warm.main),
        original_artifact,
        "unchanged native artifact must stay intact"
    );
    assert_eq!(
        fs::read(world.path().join("producer.count")).unwrap(),
        b"1\n"
    );
    assert!(
        !warm.reads.is_empty(),
        "actual generated-tree trace must remain observable"
    );
    let inventory = warm
        .reads
        .iter()
        .map(|read| read.output_bytes)
        .max()
        .unwrap();
    assert!(inventory >= BLOB_BYTES);
    assert!(
        warm.reads
            .iter()
            .all(|read| read.output_bytes == inventory && read.entries >= 3)
    );
    let full_captures = warm
        .reads
        .iter()
        .filter(|read| read.bytes_hashed > 0)
        .count();
    let bytes_hashed: u64 = warm.reads.iter().map(|read| read.bytes_hashed).sum();
    let measurement = format!(
        "warm rows={:?}\nfull_captures={full_captures}\nbytes_hashed={bytes_hashed}\noutput_bytes={inventory}\n",
        warm.reads
    );
    eprintln!("{measurement}");
    write(&world.path().join("measurement.txt"), &measurement);

    // Preserve this safety control even on a failing baseline measurement:
    // make the performance assertion only after recovery actually executes.
    let generated = warm.out_dir.join("generated.rs");
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
    let repaired = build(world.path(), &root, "restored-mtime-mutation");
    assert_eq!(execute(&repaired), b"phase-2 111\n");
    assert_eq!(
        fs::read(world.path().join("producer.count")).unwrap(),
        b"2\n"
    );
    assert!(
        repaired
            .reads
            .iter()
            .any(|read| read.bytes_hashed >= BLOB_BYTES),
        "mutation must still receive full content validation"
    );
    eprintln!(
        "mutation recovery rows={:?}; actual producer count=2; native=phase-2 111",
        repaired.reads
    );
    assert!(
        full_captures <= 1 && bytes_hashed <= inventory,
        "one unchanged generated unit must not be fully hashed repeatedly in one warm invocation: {measurement}"
    );
    world.passed();
}

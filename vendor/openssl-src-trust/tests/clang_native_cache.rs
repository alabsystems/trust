//! Qualify the existing native compiler's actual C-action cache mechanics.
//! These controls are not Trust proof or compiler/runtime admission authority.

#![cfg(target_os = "macos")]

use sha2::{Digest, Sha256};
use std::fs;
use std::path::Path;
use std::process::Command;

fn compile(root: &Path, extra: &[&str]) -> (Vec<u8>, String) {
    let output = Command::new("/usr/bin/clang")
        .current_dir(root)
        .args([
            "-fdepscan=inline",
            "-Xclang",
            "-fcache-compile-job",
            "-Xclang",
            "-fcas-path",
            "-Xclang",
            "cas",
            "-Rcompile-job-cache",
            "-O2",
            "-g",
            "-c",
            "input.c",
            "-o",
            "output.o",
        ])
        .args(extra)
        .output()
        .unwrap();
    let diagnostics = String::from_utf8(output.stderr).unwrap();
    assert!(
        output.status.success(),
        "native compile failed: {diagnostics}"
    );
    (fs::read(root.join("output.o")).unwrap(), diagnostics)
}

#[test]
fn actual_clang_cas_replays_identical_objects_and_invalidates_header_bytes() {
    let temporary = tempfile::tempdir().unwrap();
    let root = temporary.path().canonicalize().unwrap();
    fs::write(root.join("input.h"), "#define NATIVE_VALUE 17\n").unwrap();
    fs::write(
        root.join("input.c"),
        "#include \"input.h\"\nint native_value(void) { return NATIVE_VALUE; }\n",
    )
    .unwrap();
    let (cold, cold_diagnostics) = compile(&root, &[]);
    eprintln!("native cold: {cold_diagnostics}");
    assert!(
        cold_diagnostics.contains("cache miss"),
        "{cold_diagnostics}"
    );
    fs::remove_file(root.join("output.o")).unwrap();
    let (warm, warm_diagnostics) = compile(&root, &[]);
    eprintln!("native warm: {warm_diagnostics}");
    assert!(warm_diagnostics.contains("cache hit"), "{warm_diagnostics}");
    assert_eq!(Sha256::digest(&cold), Sha256::digest(&warm));
    assert_eq!(
        cold, warm,
        "actual replayed machine-code object bytes changed"
    );
    fs::write(root.join("input.h"), "#define NATIVE_VALUE 29\n").unwrap();
    let (changed, changed_diagnostics) = compile(&root, &[]);
    eprintln!("native changed header: {changed_diagnostics}");
    assert!(
        changed_diagnostics.contains("cache miss"),
        "{changed_diagnostics}"
    );
    assert_ne!(
        cold, changed,
        "a changed included macro reused old machine code"
    );
    let (flags_changed, diagnostics) = compile(&root, &["-O0"]);
    assert!(diagnostics.contains("cache miss"), "{diagnostics}");
    assert_ne!(
        changed, flags_changed,
        "changed effective native optimization flags reused old code"
    );
    fs::write(root.join("input.c"),
        "#if __has_include(\"optional.h\")\n#include \"optional.h\"\n#else\n#define OPTIONAL_VALUE 7\n#endif\nint native_value(void) { return OPTIONAL_VALUE; }\n").unwrap();
    let (absent, diagnostics) = compile(&root, &[]);
    assert!(diagnostics.contains("cache miss"), "{diagnostics}");
    fs::write(root.join("optional.h"), "#define OPTIONAL_VALUE 19\n").unwrap();
    let (present, diagnostics) = compile(&root, &[]);
    assert!(
        diagnostics.contains("cache miss"),
        "newly present native input reused absent-path fact: {diagnostics}"
    );
    assert_ne!(absent, present);
    fs::remove_file(root.join("optional.h")).unwrap();
    let (absent_again, diagnostics) = compile(&root, &[]);
    assert!(diagnostics.contains("cache hit"), "{diagnostics}");
    assert_eq!(absent, absent_again);
    for entry in fs::read_dir(root.join("cas")).unwrap() {
        let entry = entry.unwrap();
        eprintln!(
            "native CAS layout: {:?} bytes={}",
            entry.file_name(),
            entry.metadata().unwrap().len()
        );
    }
}

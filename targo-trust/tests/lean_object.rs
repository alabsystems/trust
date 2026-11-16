//! Exercise the actual source-built command, original source gate, strict CG
//! checker, exact object publication and a separately linked execution oracle.
use std::path::Path;
use std::process::{Command, Output};
fn build(root: &Path, input: &Path, output: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_targo-trust"))
        .current_dir(root)
        .args(["build"])
        .arg(input)
        .args(["--emit=object", "--out"])
        .arg(output)
        .output()
        .expect("actual source-built Lean object frontdoor")
}
#[test]
fn actual_cli_strict_object_is_runnable_and_unsupported_siblings_leave_no_object() {
    if !matches!((std::env::consts::ARCH, std::env::consts::OS), ("aarch64", "macos" | "linux")) {
        return;
    }
    let directory = tempfile::tempdir().unwrap();
    let root = directory.path();
    let input = root.join("Main.lean");
    let output = root.join("Main.o");
    std::fs::write(
        &input,
        "def add64 (a b : UInt64) : UInt64 := a + b\ndef project64 (a b : UInt64) : UInt64 := b\n",
    )
    .unwrap();
    let result = build(root, &input, &output);
    assert!(
        result.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );
    let bytes = std::fs::read(&output).unwrap();
    assert!(
        bytes.starts_with(&[0xcf, 0xfa, 0xed, 0xfe]) || bytes.starts_with(b"\x7fELF"),
        "actual object, not JSON"
    );
    let stdout = String::from_utf8(result.stdout).unwrap();
    assert!(stdout.contains("object gate: 2/2 functions closed [PROVED], 0 unclosed"), "{stdout}");
    use sha2::{Digest, Sha256};
    assert!(stdout.contains(&format!("object sha256 {:x}", Sha256::digest(&bytes))), "{stdout}");
    let caller = root.join("caller.c");
    let binary = root.join("caller");
    // C is an independent execution oracle, not the product emitter or a
    // general cross-language ABI theorem. Product object bytes are trust-cg's.
    std::fs::write(&caller,"#include <stdint.h>\nextern uint64_t add64(uint64_t,uint64_t);\nextern uint64_t project64(uint64_t,uint64_t);\nint main(void){return !(add64(UINT64_MAX,1)==0 && add64(11,17)==28 && project64(11,17)==17);}\n").unwrap();
    let link = Command::new("cc")
        .arg(&caller)
        .arg(&output)
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("system C linker oracle required");
    assert!(link.status.success(), "{}", String::from_utf8_lossy(&link.stderr));
    assert!(Command::new(&binary).status().unwrap().success());
    std::fs::remove_file(&output).unwrap();
    std::fs::write(
        &input,
        "def add64 (a b : UInt64) : UInt64 := a + b\ndef sibling (a : Nat) : Nat := a + 1\n",
    )
    .unwrap();
    let result = build(root, &input, &output);
    assert!(!result.status.success());
    assert!(!output.exists());
    let diagnostic = String::from_utf8(result.stderr).unwrap();
    assert!(
        diagnostic.contains("sibling"),
        "complete denominator refusal must name sibling: {diagnostic}"
    );
}

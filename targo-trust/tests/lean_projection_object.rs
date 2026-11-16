//! Pure constructor elimination through the original kernel and strict object
//! gate. The C caller is an execution oracle, not a foreign-ABI theorem.
#![cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]

use std::path::Path;
use std::process::{Command, Output};

const SOURCE: &str = r#"def scalarOfNat (payload : UInt64) : UInt64 :=
  @OfNat.ofNat UInt64 7 (@OfNat.mk UInt64 7 payload)
def chooseOfNat (left payload : UInt64) : UInt64 :=
  @OfNat.ofNat UInt64 7 (@OfNat.mk UInt64 7 payload)
def computedOfNat (payload : UInt64) : UInt64 :=
  @OfNat.ofNat UInt64 7 (@OfNat.mk UInt64 7 (payload + 1))
def scalarPair (left payload : UInt64) : UInt64 :=
  @Prod.snd UInt64 UInt64 (@Prod.mk UInt64 UInt64 left payload)
"#;

fn build(root: &Path, source: &str) -> (Output, std::path::PathBuf) {
    let input = root.join("Main.lean");
    let object = root.join("Main.o");
    std::fs::write(&input, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_targo-trust"))
        .current_dir(root)
        .arg("build")
        .arg(&input)
        .args(["--emit=object", "--out"])
        .arg(&object)
        .output()
        .expect("the actual source-built Lean frontdoor");
    (output, object)
}

#[test]
fn constructor_payloads_emit_a_complete_strict_object_and_match_an_execution_oracle() {
    let directory = tempfile::tempdir().unwrap();
    let root = directory.path();
    let (output, object) = build(root, SOURCE);
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let bytes = std::fs::read(&object).unwrap();
    assert!(bytes.starts_with(&[0xcf, 0xfa, 0xed, 0xfe]) || bytes.starts_with(b"\x7fELF"));
    let report = String::from_utf8(output.stdout).unwrap();
    assert!(report.contains("object gate: 4/4 functions closed [PROVED], 0 unclosed"), "{report}");
    use sha2::{Digest, Sha256};
    assert!(report.contains(&format!("object sha256 {:x}", Sha256::digest(&bytes))), "{report}");

    let caller = root.join("caller.c");
    let executable = root.join("caller");
    std::fs::write(
        &caller,
        r#"#include <stdint.h>
extern uint64_t scalarOfNat(uint64_t);
extern uint64_t chooseOfNat(uint64_t, uint64_t);
extern uint64_t computedOfNat(uint64_t);
extern uint64_t scalarPair(uint64_t, uint64_t);
int main(void) {
  const uint64_t values[] = {0, 1, 7, UINT64_MAX, UINT64_MAX - 1, UINT64_C(0x8000000000000000)};
  for (unsigned i = 0; i < sizeof(values) / sizeof(values[0]); ++i) {
    uint64_t payload = values[i], left = payload ^ UINT64_C(0x5a5a5a5a5a5a5a5a);
    if (scalarOfNat(payload) != payload || chooseOfNat(left, payload) != payload ||
        computedOfNat(payload) != payload + 1 || scalarPair(left, payload) != payload)
      return 1;
  }
  return 0;
}
"#,
    )
    .unwrap();
    let linked = Command::new("cc")
        .arg(&caller)
        .arg(&object)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("system C compiler for the independent execution oracle");
    assert!(linked.status.success(), "{}", String::from_utf8_lossy(&linked.stderr));
    assert!(Command::new(&executable).status().unwrap().success());
}

#[test]
fn a_mismatched_source_index_cannot_emit_an_object() {
    let directory = tempfile::tempdir().unwrap();
    let (output, object) = build(
        directory.path(),
        "def wrongIndex (payload : UInt64) : UInt64 :=\n  \
         @OfNat.ofNat UInt64 7 (@OfNat.mk UInt64 8 payload)",
    );
    assert!(!output.status.success());
    assert!(!object.exists());
    assert!(String::from_utf8_lossy(&output.stderr).contains("wrongIndex"));
}

#[test]
fn a_runtime_family_sibling_stays_in_the_complete_owned_denominator() {
    let directory = tempfile::tempdir().unwrap();
    let source = format!(
        "{SOURCE}\ndef makeOfNat (payload : UInt64) : OfNat UInt64 7 := \
         @OfNat.mk UInt64 7 payload\n"
    );
    let (output, object) = build(directory.path(), &source);
    assert!(!output.status.success());
    let refusal = String::from_utf8_lossy(&output.stderr);
    assert!(refusal.contains("makeOfNat") && refusal.contains("of 5 computational"), "{refusal}");
    assert!(!object.exists(), "scalar elimination cannot omit an uncarried runtime-family sibling");
}

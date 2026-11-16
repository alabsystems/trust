//! Real Lean applications to a strict object, followed by a differential caller.
//! No first-class closure carrier or general foreign-ABI theorem is implied.
#![cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]

use std::path::Path;
use std::process::{Command, Output};

fn build(root: &Path, input: &Path, output: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_targo-trust"))
        .current_dir(root)
        .arg("build")
        .arg(input)
        .args(["--emit=object", "--out"])
        .arg(output)
        .output()
        .expect("the actual source-built Lean frontdoor")
}

#[test]
fn original_named_and_anonymous_applications_emit_complete_strict_objects() {
    let directory = tempfile::tempdir().unwrap();
    let root = directory.path();
    let source = root.join("Main.lean");
    let object = root.join("Main.o");
    std::fs::write(
        &source,
        r#"def inc (x : UInt64) : UInt64 := x + 1
def twice (x : UInt64) : UInt64 := inc (inc x)
def beta_inc (x : UInt64) : UInt64 := (fun y : UInt64 => y + 1) x
def capturing_beta (x : UInt64) : UInt64 := (fun y : UInt64 => x + y) 3
def nested_beta (x : UInt64) : UInt64 := (fun y : UInt64 => y + 1) ((fun z : UInt64 => z + 1) x)
def local_closure (x : UInt64) : UInt64 :=
  let f := fun y : UInt64 => x + y
  f 3
"#,
    )
    .unwrap();
    let output = build(root, &source, &object);
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let bytes = std::fs::read(&object).unwrap();
    assert!(bytes.starts_with(&[0xcf, 0xfa, 0xed, 0xfe]) || bytes.starts_with(b"\x7fELF"));
    let report = String::from_utf8(output.stdout).unwrap();
    assert!(report.contains("object gate: 6/6 functions closed [PROVED], 0 unclosed"), "{report}");
    use sha2::{Digest, Sha256};
    assert!(report.contains(&format!("object sha256 {:x}", Sha256::digest(&bytes))), "{report}");

    // A separately compiled C caller is an execution oracle only. All product
    // object bytes above came from Trust's unchanged strict output gate.
    let caller = root.join("caller.c");
    let executable = root.join("caller");
    std::fs::write(
        &caller,
        r#"#include <stdint.h>
extern uint64_t inc(uint64_t);
extern uint64_t twice(uint64_t);
extern uint64_t beta_inc(uint64_t);
extern uint64_t capturing_beta(uint64_t);
extern uint64_t nested_beta(uint64_t);
extern uint64_t local_closure(uint64_t);
int main(void) {
  const uint64_t values[] = {0, 1, UINT64_MAX, UINT64_MAX - 1, UINT64_C(0x8000000000000000)};
  for (unsigned i = 0; i < sizeof(values) / sizeof(values[0]); ++i) {
    uint64_t x = values[i];
    if (inc(x) != x + 1 || twice(x) != x + 2 || beta_inc(x) != x + 1 ||
        capturing_beta(x) != x + 3 || nested_beta(x) != x + 2 || local_closure(x) != x + 3)
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
        .expect("the system C compiler is required for the separate execution oracle");
    assert!(linked.status.success(), "{}", String::from_utf8_lossy(&linked.stderr));
    assert!(Command::new(&executable).status().unwrap().success());
}

#[test]
fn an_inlineable_caller_cannot_omit_its_unsupported_higher_order_sibling() {
    let directory = tempfile::tempdir().unwrap();
    let root = directory.path();
    let source = root.join("Main.lean");
    let object = root.join("Main.o");
    std::fs::write(
        &source,
        "def apply64 (f : UInt64 -> UInt64) (x : UInt64) : UInt64 := f x\n\
         def use_apply64 (x : UInt64) : UInt64 := apply64 (fun y : UInt64 => y + 1) x\n",
    )
    .unwrap();
    let output = build(root, &source, &object);
    assert!(!output.status.success());
    let refused = String::from_utf8(output.stderr).unwrap();
    assert!(refused.contains("apply64") && refused.contains("of 2 computational"), "{refused}");
    assert!(!object.exists(), "the complete source population must remain the denominator");
}

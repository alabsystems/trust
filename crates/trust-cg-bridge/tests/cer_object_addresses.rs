//! Object offsets are not placed executable addresses.
#![cfg(all(feature = "kernel-recheck", target_arch = "aarch64", target_os = "macos"))]

mod cer_common;

use std::process::Command;

use cer_common::{DARWIN, Fixture, ModBuilder, explain, function_words, patch_word};
use trust_cg_bridge::verify_output::{EmitPolicy, OutputVerdict};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{Linkage, Ty};

fn zero() -> Fixture {
    let mut builder = ModBuilder::new("object_address_model");
    let signature = builder.sig(&[], Some(Ty::U64));
    builder.define("object_zero", signature, Linkage::External, |body| {
        let value = body.konst(Ty::U64, 0);
        body.ret(value);
    });
    Fixture::new(builder.finish(), DARWIN, OptLevel::O0)
}

fn execute(object: &[u8]) -> u64 {
    let temp = tempfile::tempdir().unwrap();
    std::fs::write(temp.path().join("subject.o"), object).unwrap();
    std::fs::write(
        temp.path().join("driver.c"),
        r#"#include <stdint.h>
#include <stdio.h>
extern uint64_t object_zero(void);
int main(void) { printf("%llu\n", (unsigned long long)object_zero()); return 0; }
"#,
    )
    .unwrap();
    let output = Command::new("/usr/bin/cc")
        .current_dir(temp.path())
        .args(["driver.c", "subject.o", "-o", "driver"])
        .output()
        .unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    let output = Command::new(temp.path().join("driver")).output().unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    String::from_utf8(output.stdout).unwrap().trim().parse().unwrap()
}

#[test]
fn executable_address_data_is_not_a_source_zero() {
    let fixture = zero();
    let original = fixture.report();
    assert!(
        original.certificate("object_zero").unwrap().is_kernel_proved(),
        "{}",
        explain(&original)
    );
    assert!(original.ships(EmitPolicy::StrictProvenOnly).is_ok());
    assert_eq!(execute(&fixture.object), 0);
    let words = function_words(&fixture.object, "object_zero");
    assert_eq!(words[0].0, 0, "this actual first function starts at section offset zero");
    assert_eq!(words[0].1, 0xd280_0000, "actual MOV X0,#0");
    for (name, word) in [("adr", 0x1000_0000), ("adrp", 0x9000_0000)] {
        let other = fixture.patched(|object| patch_word(object, words[0].0, word));
        assert!(cer_common::text_relocs(&other.object).is_empty());
        let report = other.report();
        let native = execute(&other.object);
        assert_ne!(native, 0, "{name} materializes a loaded executable address");
        if let Some(path) = std::env::var_os("TRUST_OBJECT_ADDRESS_EVIDENCE") {
            let path = std::path::PathBuf::from(path).join(name);
            std::fs::create_dir_all(&path).unwrap();
            std::fs::write(path.join("subject.o"), &other.object).unwrap();
            std::fs::write(path.join("certificates.json"), report.to_json()).unwrap();
            std::fs::write(path.join("native-return.txt"), format!("{native}\n")).unwrap();
        }
        assert_unknown_placement(&report);

        // The trap-tail inspector must use the same admission frontier before
        // consulting instruction effects. Do not execute this trapping object.
        let trapping = other.patched(|object| {
            patch_word(object, words.last().unwrap().0, 0xd420_0000);
        });
        let trap_report = trapping.report();
        assert_unknown_placement(&trap_report);
        if let Some(path) = std::env::var_os("TRUST_OBJECT_ADDRESS_EVIDENCE") {
            let path = std::path::PathBuf::from(path).join(format!("{name}-trap-tail"));
            std::fs::create_dir_all(&path).unwrap();
            std::fs::write(path.join("subject.o"), &trapping.object).unwrap();
            std::fs::write(path.join("certificates.json"), trap_report.to_json()).unwrap();
        }
    }
}

fn assert_unknown_placement(report: &trust_cg_bridge::call_event::CerReport) {
    let certificate = report.certificate("object_zero").unwrap();
    assert!(
        matches!(&certificate.verdict, OutputVerdict::Unknown { reason }
            if reason.contains("runtime placement witness")),
        "{}",
        explain(report)
    );
    assert!(!certificate.is_kernel_proved());
    assert!(report.ships(EmitPolicy::StrictProvenOnly).is_err());
}

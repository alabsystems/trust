//! The legacy and direct-IR output readers must not turn object offsets into data.
#![cfg(all(feature = "kernel-recheck", target_arch = "aarch64", target_os = "macos"))]

mod cer_common;

use std::process::Command;

use cer_common::{DARWIN, Fixture, ModBuilder, function_words, patch_word};
use trust_cg_bridge::codegen_backend::TrustCgTargetArch;
use trust_cg_bridge::verify_output::OutputVerdict;
use trust_cg_bridge::verify_output_trust_ir::{
    TrustIrGateSource, probe_machine_only, verify_trust_ir_bytes,
};
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
fn every_output_reader_requires_runtime_placement_for_address_data() {
    let fixture = zero();
    let source = TrustIrGateSource {
        symbol: "object_zero".into(),
        module: fixture.m_cg.clone(),
        func_id: fixture.m_cg.functions[0].id,
        abi_cross_check: None,
    };
    let original = verify_trust_ir_bytes(&source, &fixture.object, TrustCgTargetArch::AArch64);
    assert!(original.is_kernel_proved(), "{original:?}");
    assert_eq!(execute(&fixture.object), 0);
    let words = function_words(&fixture.object, "object_zero");
    assert_eq!(words[0], (0, 0xd280_0000));
    for (label, word) in [("adr", 0x1000_0000), ("adrp", 0x9000_0000)] {
        let mutant = fixture.patched(|object| patch_word(object, words[0].0, word));
        assert!(cer_common::text_relocs(&mutant.object).is_empty());
        let native = execute(&mutant.object);
        assert_ne!(native, 0);
        let verdict = verify_trust_ir_bytes(&source, &mutant.object, TrustCgTargetArch::AArch64);
        let machine = probe_machine_only(&mutant.object, 64);
        if let Some(out) = std::env::var_os("TRUST_VOT_ADDRESS_EVIDENCE") {
            let out = std::path::PathBuf::from(out).join(label);
            std::fs::create_dir_all(&out).unwrap();
            std::fs::write(out.join("object.o"), &mutant.object).unwrap();
            std::fs::write(out.join("verdict.txt"), format!("{verdict:?}\n{machine:?}\n")).unwrap();
            std::fs::write(out.join("native-return.txt"), format!("{native}\n")).unwrap();
        }
        assert_unknown_placement(&verdict);
        assert!(
            matches!(&machine, Err(reason) if reason.contains("runtime placement witness")),
            "{machine:?}"
        );

        // The divergent-tail reader must reject the same unplaced address
        // before its effect scan. This object is deliberately not executed.
        let trapping = mutant.patched(|object| {
            patch_word(object, words.last().unwrap().0, 0xd420_0000);
        });
        let trap_verdict =
            verify_trust_ir_bytes(&source, &trapping.object, TrustCgTargetArch::AArch64);
        assert_unknown_placement(&trap_verdict);
        let trap_machine = probe_machine_only(&trapping.object, 64);
        assert!(
            matches!(&trap_machine, Err(reason)
            if reason.contains("runtime placement witness")),
            "{trap_machine:?}"
        );
    }
}

fn assert_unknown_placement(verdict: &OutputVerdict) {
    assert!(
        matches!(verdict, OutputVerdict::Unknown { reason }
        if reason.contains("runtime placement witness")),
        "{verdict:?}"
    );
    assert!(!verdict.is_kernel_proved());
}

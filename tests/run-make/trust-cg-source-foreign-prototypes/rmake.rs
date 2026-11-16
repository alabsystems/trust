//! Original-source prototypes through the actual F1 Compiler::compile lane.
//! The LLVM build is an executable oracle. Verification is explicitly off and
//! the existing allow-unknown output policy remains visible: ABI placement
//! supplies no proof of an external callee's body or contract.
//@ needs-trust-cg-backend
//@ only-aarch64
//@ ignore-cross-compile

use run_make_support::{cc, cmd, rfs, rustc};

fn main() {
    let mut expected = None;
    for (label, native) in [("oracle", false), ("native", true)] {
        let object = format!("{label}.o");
        let mut compile = rustc();
        compile.input("subject.rs").crate_name("foreign_prototypes").crate_type("lib")
            .edition("2024").arg("--emit=obj").arg("-Cpanic=abort")
            .arg("-Ccodegen-units=1").arg("-Copt-level=0")
            .arg("-Ztrust-verify=off").arg("-Ztrust-ir-lower=on")
            .arg(format!("-Ztrust-dump=ir:{label}-ir")).output(&object)
            .env_remove("TRUST_NO_VERIFY");
        if native {
            compile.arg("-Zunstable-options").arg("-Zcodegen-backend=trust-cg")
                .arg("-Ztrust-cg-frontend=trust-ir").arg("-Ztrust-cg-f1-backend=compiler")
                .arg("-Ztrust-cg-output-gate=allow-unknown");
        }
        compile.run();
        let text = rfs::read_to_string(format!("{label}-ir/foreign_prototypes.trust-ir.txt"));
        assert!(text.contains("(i32, ...) -> (i32)"), "the fixed variadic prefix must survive: {text}");
        assert!(!text.contains(" = (...) -> (i32)"), "an unknown prototype must not replace it: {text}");
        let exe = format!("{label}-driver");
        cc().arg("-O2").arg("-Wall").arg("-Wextra").arg("-Werror")
            .input("driver.c").input(&object).out_exe(&exe).run();
        let got = cmd(format!("./{exe}")).run().stdout_utf8();
        if let Some(expected) = &expected { assert_eq!(&got, expected); }
        else { expected = Some(got); }
    }
}

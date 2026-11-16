//! Trust (R-8 fail-open item 3, 2026-10-01): trust-cg refuses `-Zcodegen-emit-retag`.
//!
//! The flag asks codegen to emit Tree Borrows retag calls. trust-cg emits none, on
//! either frontend, and used to ship the object without them and without a
//! diagnostic (docs/audits/2026-09-29-r8-trust-ir-vs-mir.md, "Fails OPEN" item 3).
//! Until it emits them it must refuse the flag: a build must never believe it is
//! instrumented when it is not.
//!
//! * The control: without the flag the same crate compiles on both trust-cg
//!   frontends, so the refusal below is about the flag and nothing else.
//! * The refusal: with the flag, both frontends exit non-zero, name the flag, and
//!   write no object.
//! * The LLVM backend still accepts the flag (it does emit the retags).

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{path, rfs, rustc};

fn trust_cg(out: &str) -> rustc::Rustc {
    let mut rustc = rustc();
    rustc
        .input("retag.rs")
        .crate_type("lib")
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-verify=off")
        .out_dir(out);
    rustc
}

fn main() {
    rfs::write("retag.rs", "#![crate_name = \"retag\"]\npub fn masked(x: u32) -> u8 { (x & 0xff) as u8 }\n");

    // The control, on both frontends.
    trust_cg("out_mir_ok").run();
    trust_cg("out_f1_ok").arg("-Ztrust-ir-lower").arg("-Ztrust-cg-frontend=trust-ir").run();

    // The refusal, on both frontends: named, and no object written.
    for (out, f1) in [("out_mir_retag", false), ("out_f1_retag", true)] {
        let mut cmd = trust_cg(out);
        if f1 {
            cmd.arg("-Ztrust-ir-lower").arg("-Ztrust-cg-frontend=trust-ir");
        }
        let refused = cmd.arg("-Zcodegen-emit-retag").run_fail();
        refused.assert_stderr_contains("trust-cg does not emit the retag calls `-Zcodegen-emit-retag` asks for");
        assert!(!path(out).join("libretag.rlib").exists(), "{out}: an rlib was written despite the refusal");
    }

    // The LLVM backend emits the retags, so it keeps accepting the flag.
    rustc()
        .input("retag.rs")
        .crate_type("lib")
        .edition("2021")
        .arg("-Zcodegen-emit-retag")
        .arg("-Ztrust-verify=off")
        .out_dir("out_llvm_retag")
        .run();
}

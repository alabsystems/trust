//! Trust (plan 2026-09-29, step 2): `#[custom_mir]` bodies are refused on the
//! trust-ir path with a named diagnostic.
//!
//! A `#[custom_mir]` body's THIR is a script of calls into the
//! `core::intrinsics::mir` dialect that rustc's MIR builder interprets; it is not
//! Rust to run. The producer used to lower it like any fn, into calls to
//! `Return()` and friends, and F1 refused it only because its converter did not
//! yet admit `Call` (`[converter-refused]`), which real call edges (increment 5)
//! would have removed. Now the producer declines it and F1 names it, on both
//! lanes, before any module lookup.
//!
//! * The control: an ordinary fn in the same shape of crate compiles on F1.
//! * The refusal: the custom_mir crate fails under `[producer-declined]` with the
//!   `#[custom_mir]` reason, on the default lane and on `-Ztrust-ir-crate-module`.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{path, rfs, rustc};

fn f1(input: &str, out: &str) -> rustc::Rustc {
    let mut rustc = rustc();
    rustc
        .input(input)
        .crate_type("lib")
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-cg-frontend=trust-ir")
        .out_dir(out);
    rustc
}

fn main() {
    rfs::write("ok.rs", "#![crate_name = \"ok\"]\npub fn id(x: u32) -> u32 { x }\n");
    f1("ok.rs", "out_ok").run();

    rfs::write(
        "c.rs",
        "#![feature(custom_mir, core_intrinsics)]\n\
         #![allow(internal_features)]\n\
         #![crate_name = \"c\"]\n\
         use core::intrinsics::mir::*;\n\
         #[custom_mir(dialect = \"built\")]\n\
         pub fn id(x: u32) -> u32 {\n    mir! {\n        {\n            RET = x;\n            Return()\n        }\n    }\n}\n",
    );
    for (out, crate_module) in [("out_default", false), ("out_crate_module", true)] {
        let mut cmd = f1("c.rs", out);
        if crate_module {
            cmd.arg("-Ztrust-ir-crate-module");
        }
        let refused = cmd.run_fail();
        refused.assert_stderr_contains("[producer-declined]");
        refused.assert_stderr_contains("a `#[custom_mir]` dialect body, not Rust");
        assert!(!path(out).join("libc.rlib").exists(), "{out}: an rlib was written");
    }
}

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64
//! Source FnOnce -> assembled Trust-IR -> Compiler::compile preserves external pointer identity.
//! Explicit allow-unknown exercises runtime behavior without claiming a closed proof.
use run_make_support::{cmd, rfs, rustc};

fn main() {
    for opt in ["0", "3"] {
        let name = format!("fn_once_o{opt}");
        rfs::create_dir(&name);
        let result = rustc()
            .input("subject.rs")
            .crate_name("fn_once")
            .crate_type("rlib")
            .edition("2024")
            .arg("-Cpanic=abort")
            .arg("-Coverflow-checks=off")
            .arg("-Ccodegen-units=1")
            .arg(format!("-Copt-level={opt}"))
            .arg("-Ztrust-verify=off")
            .arg("-Zcodegen-backend=trust-cg")
            .arg("-Ztrust-cg-frontend=trust-ir")
            .arg("-Ztrust-cg-f1-backend=compiler")
            .arg("-Ztrust-cg-output-gate=allow-unknown")
            .arg("-Ztrust-ir-lower")
            .out_dir(&name)
            .run();
        result.assert_stderr_contains("source -> trust_ir_of -> codegen_module");
        let executable = format!("{name}/driver");
        cmd("cc")
            .args(["driver.c", &format!("{name}/libfn_once.rlib"), "-o", &executable])
            .run();
        cmd(&executable).run().assert_stdout_equals("fn_once pointer and store preserved\n");
    }
}

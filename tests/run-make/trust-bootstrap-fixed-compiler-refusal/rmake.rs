//! Trust: the private compiler routing flag never creates original Fixed custody.
//@ only-aarch64-apple-darwin

use run_make_support::{rustc, rustc_path};

fn main() {
    let base = || {
        let mut compiler=rustc();
        compiler.input("lib.rs").crate_type("rlib").emit("metadata")
            .arg("--resource-bootstrap-fixed-v1");
        compiler
    };
    // Keep actual inherited admission/SDK/GNU claims. Removing only this private
    // routing locator must cause refusal, never manufacture another Root/credit.
    let mut arbitrary=base();
    arbitrary.env_remove("ATERM_RESOURCE_JOB_V3");
    arbitrary.run_fail().assert_stderr_contains("private Fixed compiler");
    for conflict in [
        &["--resource-worker-v2"][..],
        &["--resource-worker-v3","--resource-subgroups-v3"],
    ] {
        let mut compiler=base();
        compiler.args(conflict).run_fail()
            .assert_stderr_contains("private Bootstrap Fixed compiler excludes other worker protocols");
    }
    for early in ["--help","-V","-vV","-Zhelp","-Chelp","-Cpasses=list","-Wall","-Whelp","--explain=E0001"] {
        base().arg(early).run_fail().assert_stderr_contains("private Fixed compiler");
    }
    // The real image must recognize the closed flag, rather than passing these
    // negatives merely because an older compiler rejected an unknown option.
    assert!(rustc_path().is_file());
    base().arg("-Zcodegen-backend=foreign-private-backend").run_fail()
        .assert_stderr_contains("private Bootstrap Fixed compiler cannot execute an unqualified target/backend phase");
}

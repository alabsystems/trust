//! Actual-session declaration installation in a handoff closure. The std
//! producer is required; no missing-metadata or unknown-gate skip is accepted.
//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64
use run_make_support::{rfs, run, rustc};

fn main() {
    rfs::create_dir("native");
    let output = rustc().input("handoff.rs").crate_type("rlib").out_dir("native")
        .arg("-Cpanic=abort").arg("-Coverflow-checks=on")
        .arg("-Ztrust-verify=on").arg("-Ztrust-ir-lower=on")
        .arg("-Zcodegen-backend=trust-cg").arg("-Ztrust-cg-frontend=trust-ir")
        .arg("-Ztrust-cg-f1-backend=compiler").arg("-Ztrust-cg-output-gate=strict")
        .env_remove("TRUST_NO_VERIFY").run();
    assert!(output.stderr_utf8().contains(
        "`clean_origin_mir` reached: codegen 0, inventory 0, recorder 0"),
        "{}", output.stderr_utf8());
    let coverage = rfs::read_to_string("native/handoff_case.trust-instance-coverage.json");
    for expected in ["\"kind\": \"upstream-entry\"", "content SHA256",
                     "rebound module SHA256", "conservation re-derived", "handoff"] {
        assert!(coverage.contains(expected), "missing {expected}: {coverage}");
    }
    rfs::write("driver.rs", r#"
extern crate handoff_case;
fn main() {
    for (x, y) in [(0, 0), (1, 2), (u64::MAX, 1), (u64::MAX, u64::MAX),
                   (1 << 63, 1 << 63), (12345, 67890)] {
        assert_eq!(handoff_case::handoff(x, y), x.wrapping_add(y));
    }
    println!("handoff-declaration-ok");
}
"#);
    let driver = rustc().input("driver.rs").output("driver")
        .arg("-Cpanic=abort").arg("-Ztrust-verify=off").arg("-Zprint-mono-items=yes")
        .arg("--extern").arg("handoff_case=native/libhandoff_case.rlib").run();
    assert!(!driver.stdout_utf8().contains("MONO_ITEM fn handoff_case::"),
        "LLVM driver rebuilt a subject body: {}", driver.stdout_utf8());
    run("driver").assert_stdout_equals("handoff-declaration-ok\n");
}

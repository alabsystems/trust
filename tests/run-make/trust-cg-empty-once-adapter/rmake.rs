//! Retain real rustc ClosureOnce inventory rows and execute their typed native adapters.
//! MIR optimization stays off so CG O3 cannot hide the synthetic instance obligation.
//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64
//@ ignore-cross-compile
use run_make_support::{cc, cmd, rfs, rustc_path, serde_json};
use std::collections::BTreeSet;

fn main() {
    let output = cmd(rustc_path())
        .args([
            "subject.rs",
            "--edition=2024",
            "--crate-type=lib",
            "--crate-name=empty_once_adapter",
            "--emit=obj",
            "-Cpanic=abort",
            "-Ccodegen-units=1",
            "-Coverflow-checks=off",
            "-Copt-level=3",
            "-Zmir-opt-level=0",
            "-Zunstable-options",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-ir-flip=no",
            "-Zcodegen-backend=trust-cg",
            "-Ztrust-cg-frontend=trust-ir",
            "-Ztrust-cg-f1-backend=compiler",
            "-Ztrust-instance-flip-probe=*",
            "-o",
            "native.o",
        ])
        .run();
    let stderr = output.stderr_utf8();
    let shims: BTreeSet<String> = stderr
        .lines()
        .filter_map(|line| {
            let row = line.strip_prefix("TRUST-WALLA-PROBE C sym=")?;
            let (symbol, rest) = row.split_once(" kind=")?;
            rest.starts_with("shim-closure-once ")
                .then(|| symbol.to_string())
        })
        .collect();
    assert!(
        !shims.is_empty(),
        "the real retained ClosureOnce inventory must be observed: {stderr}"
    );
    let report: serde_json::Value =
        serde_json::from_str(&rfs::read_to_string("native.trust-cg-certificates.json")).unwrap();
    let certificates = report["certificates"].as_array().unwrap();
    let symbols: BTreeSet<String> = certificates
        .iter()
        .map(|row| {
            assert_eq!(row["grade"], "[PROVED]", "{row}");
            row["symbol"].as_str().unwrap().to_string()
        })
        .collect();
    assert!(
        shims.is_subset(&symbols),
        "every original shim remains certified: {shims:?} vs {symbols:?}"
    );
    assert!(
        report["closure"]["unclosed"].as_array().unwrap().is_empty(),
        "{report}"
    );
    let closed: BTreeSet<String> = report["closure"]["closed_kernel"]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| row.as_str().unwrap().to_string())
        .collect();
    assert_eq!(
        symbols, closed,
        "no incomplete certificate counts as a native result"
    );
    cc().arg("-Wall")
        .arg("-Wextra")
        .arg("-Werror")
        .input("driver.c")
        .input("native.o")
        .out_exe("driver")
        .run();
    cmd("./driver").run();
}

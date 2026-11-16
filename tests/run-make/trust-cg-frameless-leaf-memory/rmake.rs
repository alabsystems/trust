//! Prepared genuine closure-free source memory proof regression for a matching SDK.
//! All emitted functions must close under default Strict at O0/O3; preserve
//! the original pointer closure as a separate complete three-function control.
//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64
//@ ignore-cross-compile

use run_make_support::object::{
    Architecture, BinaryFormat, Object, ObjectKind, ObjectSection, ObjectSymbol, SymbolKind,
};
use run_make_support::{cc, cmd, object, rfs, rustc_path, serde_json};
use std::collections::BTreeSet;
use std::path::Path;

fn compile(
    source: &str,
    crate_name: &str,
    opt: &str,
    output: &str,
    gate: Option<&str>,
    succeeds: bool,
) {
    let mut compiler = cmd(rustc_path());
    compiler
        .args([
            source,
            "--edition=2024",
            "--crate-type=lib",
            "--emit=obj",
            "-Cpanic=abort",
            "-Ccodegen-units=1",
            "-Coverflow-checks=off",
            "-Zunstable-options",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-ir-flip=no",
            "-Zcodegen-backend=trust-cg",
            "-Ztrust-cg-frontend=trust-ir",
            "-Ztrust-cg-f1-backend=compiler",
        ])
        .arg(format!("--crate-name={crate_name}"))
        .arg(format!("-Copt-level={opt}"))
        .arg("-o")
        .arg(output);
    if let Some(gate) = gate {
        compiler.arg(format!("-Ztrust-cg-output-gate={gate}"));
    }
    if succeeds {
        compiler.run().assert_stderr_contains("0 refuted");
    } else {
        compiler
            .run_fail()
            .assert_stderr_contains("not closed-[PROVED]");
    }
}
/// Read every defined text symbol, independently of the certificate names.
fn emitted_functions(output: &str) -> BTreeSet<String> {
    let bytes = rfs::read(output);
    let file = object::File::parse(bytes.as_slice()).unwrap();
    assert_eq!(file.format(), BinaryFormat::MachO);
    assert_eq!(file.architecture(), Architecture::Aarch64);
    assert_eq!(file.kind(), ObjectKind::Relocatable);
    let symbols: Vec<_> = file
        .symbols()
        .filter(|s| s.is_definition() && s.kind() == SymbolKind::Text)
        .map(|symbol| {
            let section = file
                .section_by_index(symbol.section_index().unwrap())
                .unwrap();
            assert_eq!(section.name().unwrap(), "__text");
            symbol
                .name()
                .unwrap()
                .strip_prefix('_')
                .expect("Mach-O function prefix")
                .to_owned()
        })
        .collect();
    let names: BTreeSet<_> = symbols.iter().cloned().collect();
    assert_eq!(
        symbols.len(),
        names.len(),
        "duplicate raw text symbol: {symbols:?}"
    );
    names
}
/// `__LD,__compact_unwind` is verified only when every actual record has a checked ZERO-FRAME
/// prefix certificate (995113adee); a framed record keeps the section disclosed as unverified.
/// `framed` names the objects whose functions all keep an FP/LR frame record.
fn report(output: &str, framed: bool) -> serde_json::Value {
    let stem = Path::new(output).file_stem().unwrap().to_str().unwrap();
    let report: serde_json::Value = serde_json::from_str(&rfs::read_to_string(format!(
        "{stem}.trust-cg-certificates.json"
    )))
    .unwrap();
    let checksum = cmd("/usr/bin/shasum")
        .args(["-a", "256", output])
        .run()
        .stdout_utf8();
    let checksum = checksum.split_whitespace().next().unwrap();
    assert_eq!(checksum.len(), 64);
    assert_eq!(
        report["object_sha256"], checksum,
        "actual object/report hash: {output}"
    );
    let rows = report["certificates"].as_array().unwrap();
    let names: BTreeSet<String> = rows
        .iter()
        .map(|r| r["symbol"].as_str().unwrap().to_owned())
        .collect();
    assert_eq!(rows.len(), names.len(), "duplicate certificate: {report}");
    assert_eq!(
        emitted_functions(output),
        names,
        "complete object/certificate denominator: {report}"
    );
    if framed {
        // Every record is an actual FRAME-mode record (UNWIND_ARM64_MODE_FRAME), none is
        // checked, and they cover exactly the certificate population.
        let records = report["compact_unwind"]["records"].as_array().unwrap();
        let covered: BTreeSet<String> = records
            .iter()
            .map(|r| r["record"]["symbol"].as_str().unwrap().to_owned())
            .collect();
        assert_eq!(covered, names, "{report}");
        for row in records {
            assert_eq!(row["checked"], false, "{row}");
            let encoding = row["record"]["encoding"].as_u64().unwrap();
            assert_eq!(encoding & 0x0f00_0000, 0x0400_0000, "{row}");
        }
        assert_eq!(
            report["unverified_sections"].as_array().unwrap(),
            &vec![serde_json::Value::from("__LD,__compact_unwind")],
            "{report}"
        );
    } else {
        assert!(
            report["unverified_sections"].as_array().unwrap().is_empty(),
            "{report}"
        );
    }
    report
}
fn all_kernel(report: &serde_json::Value, expected: &BTreeSet<String>) {
    let rows = report["certificates"].as_array().unwrap();
    let names: BTreeSet<String> = rows
        .iter()
        .map(|r| r["symbol"].as_str().unwrap().to_owned())
        .collect();
    assert_eq!(&names, expected, "{report}");
    assert!(rows.iter().all(|r| r["grade"] == "[PROVED]"), "{report}");
    assert_eq!(
        report["closure"]["closed_kernel"].as_array().unwrap().len(),
        expected.len(),
        "{report}"
    );
    for row in rows {
        assert!(
            row["obligations"]
                .as_object()
                .unwrap()
                .values()
                .all(|o| o["grade"] == "Proven"),
            "{row}"
        );
    }
    let closed: BTreeSet<String> = report["closure"]["closed_kernel"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| v.as_str().unwrap().to_owned())
        .collect();
    assert_eq!(&closed, expected, "{report}");
    assert!(
        report["closure"]["unclosed"].as_array().unwrap().is_empty(),
        "{report}"
    );
}
fn main() {
    let expected: BTreeSet<String> = ["leaf_store", "leaf_load", "leaf_copy", "leaf_gep"]
        .into_iter()
        .map(str::to_owned)
        .collect();
    for opt in ["0", "3"] {
        let output = format!("native-{opt}.o");
        // The default Strict compile itself must succeed. No diagnostic-only
        // object or four-name certificate filter can satisfy this positive.
        compile("subject.rs", "source_leaf_memory", opt, &output, None, true);
        let report = report(&output, false);
        all_kernel(&report, &expected);
        assert_eq!(report["certificates"].as_array().unwrap().len(), 4);
        for row in report["certificates"].as_array().unwrap() {
            assert!(row["assumptions"].as_array().unwrap().is_empty(), "{row}");
            assert!(
                row["obligations"]["o4_return"]["detail"]
                    .as_str()
                    .unwrap()
                    .contains("one original-statement kernel conjunction"),
                "{row}"
            );
        }
        let driver = format!("driver-{opt}");
        cc().arg("-O2")
            .arg("-Wall")
            .arg("-Wextra")
            .arg("-Werror")
            .input("driver.c")
            .input(&output)
            .out_exe(&driver)
            .run();
        cmd(format!("./{driver}")).run();
        assignment_order(opt);
        anchor_control(opt);
    }
}
fn assignment_order(opt: &str) {
    let output = format!("assignment-order-{opt}.o");
    compile("assignment_order.rs", "raw_entry_assignment_order", opt, &output, None, true);
    let report = report(&output, false);
    let expected = BTreeSet::from([
        "raw_store_rhs_order".to_owned(),
        "raw_field_rhs_order".to_owned(),
    ]);
    all_kernel(&report, &expected);
    let driver = format!("assignment-order-driver-{opt}");
    cc().arg("-O2")
        .arg("-Wall")
        .arg("-Wextra")
        .arg("-Werror")
        .input("assignment_order_driver.c")
        .input(&output)
        .out_exe(&driver)
        .run();
    cmd(format!("./{driver}")).run();
}
fn anchor_control(opt: &str) {
    let output = format!("anchor-{opt}.o");
    compile(
        "anchor_control.rs",
        "source_leaf_anchor",
        opt,
        &output,
        if opt == "0" {
            Some("allow-unknown")
        } else {
            None
        },
        true,
    );
    // At O0 the owner and adapter keep their framed O5 Unknowns (and the body its slot frame),
    // so their compact-unwind records cannot carry a zero-frame certificate.
    let report = report(&output, opt == "0");
    let rows = report["certificates"].as_array().unwrap();
    assert_eq!(rows.len(), 3, "{report}");
    let owner = rows
        .iter()
        .find(|r| r["symbol"] == "leaf_source_anchor")
        .unwrap();
    let adapters: Vec<_> = rows
        .iter()
        .filter(|r| {
            r["symbol"]
                .as_str()
                .unwrap()
                .starts_with("leaf_source_anchor__trust_closure_adapter_")
        })
        .collect();
    assert_eq!(adapters.len(), 1, "{report}");
    let adapter = adapters[0];
    assert_eq!(adapter["linkage"], "Internal");
    let adapter_name = adapter["symbol"].as_str().unwrap();
    let body_name = adapter["call_sites"][0]["symbol"].as_str().unwrap();
    let body = rows.iter().find(|r| r["symbol"] == body_name).unwrap();
    assert_eq!(body["linkage"], "Internal");
    let expected = BTreeSet::from([
        "leaf_source_anchor".to_owned(),
        adapter_name.to_owned(),
        body_name.to_owned(),
    ]);
    let actual: BTreeSet<String> = rows
        .iter()
        .map(|r| r["symbol"].as_str().unwrap().to_owned())
        .collect();
    assert_eq!(actual, expected, "{report}");
    let target = owner["call_sites"][0]["symbol"].as_str().unwrap();
    assert!(target == adapter_name || target == body_name, "{owner}");
    if opt == "0" {
        assert_eq!(body["grade"], "[PROVED]", "{body}");
        for row in [owner, adapter] {
            assert_eq!(row["grade"], "Unknown", "{row}");
            for obligation in ["o3_events", "o4_return"] {
                assert_eq!(row["obligations"][obligation]["grade"], "Proven", "{row}");
            }
            assert_eq!(row["obligations"]["o5_frame"]["grade"], "Unknown", "{row}");
        }
        let strict = "anchor-strict-0.o";
        assert!(!Path::new(strict).exists());
        compile(
            "anchor_control.rs",
            "source_leaf_anchor",
            "0",
            strict,
            None, // The same default Strict policy must reject the two Unknown rows.
            false,
        );
        assert!(!Path::new(strict).exists());
    } else {
        all_kernel(&report, &expected);
    }
    let driver = format!("anchor-driver-{opt}");
    cc().arg("-O2")
        .arg("-Wall")
        .arg("-Wextra")
        .arg("-Werror")
        .input("anchor_driver.c")
        .input(&output)
        .out_exe(&driver)
        .run();
    cmd(format!("./{driver}")).run();
}

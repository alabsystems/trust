//! Genuine source FnAbi + native compiler transport with full W0 CER proofs.
//! Primitive source needs no artificial closure. A separate anchor control
//! preserves all three original protocol functions and their O0 frame debt.
//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64
//@ ignore-cross-compile

use run_make_support::{cc, cmd, rfs, rustc, rustc_path, serde_json};
use std::collections::BTreeSet;
use std::path::Path;

fn abi<'a>(stderr: &'a str, name: &str) -> &'a str {
    let head = format!("error: fn_abi_of({name})");
    let start = stderr.find(&head).unwrap_or_else(|| panic!("missing {head}: {stderr}"));
    let rest = &stderr[start + head.len()..];
    let end = rest.find("error: fn_abi_of(").map_or(stderr.len(), |i| start + head.len() + i);
    &stderr[start..end]
}

fn main() {
    let observed = rustc().input("abi_probe.rs").edition("2024")
        .arg("-Cpanic=abort").arg("-Ztrust-verify=off").run_fail().stderr_utf8();
    for (name, extension) in [("c_u8", "Zext"), ("rust_u8", "None"), ("c_i8", "Sext"), ("c_u16", "Zext")] {
        let row = abi(&observed, name).split_whitespace().collect::<String>();
        assert_eq!(row.matches("mode:Direct(").count(), 2, "{name}: {row}");
        assert_eq!(row.matches(&format!("arg_ext:{extension}")).count(), 2, "{name}: {row}");
    }
    for opt in ["0", "3"] {
        let object = format!("native-{opt}.o");
        let args = [
            "subject.rs", "--edition=2024", "--crate-type=lib", "--crate-name=source_c_u8",
            "--emit=obj", "-Cpanic=abort", "-Ccodegen-units=1", "-Coverflow-checks=off",
            "-Zunstable-options", "-Ztrust-verify=off", "-Ztrust-ir-lower=on",
            "-Ztrust-ir-flip=no", "-Zcodegen-backend=trust-cg", "-Ztrust-cg-frontend=trust-ir",
            "-Ztrust-cg-f1-backend=compiler",
        ];
        let emitted = cmd(rustc_path()).args(args).arg(format!("-Copt-level={opt}"))
            .arg("-o").arg(&object).run();
        emitted.assert_stderr_contains("0 refuted");
        let report: serde_json::Value = serde_json::from_str(&rfs::read_to_string(
            format!("native-{opt}.trust-cg-certificates.json"))).unwrap();
        let certificates = report["certificates"].as_array().unwrap();
        let expected: BTreeSet<String> = ["id", "not", "xor", "constant", "trunc", "rust_typed_not"]
            .into_iter().map(|name| format!("trust_c_u8_{name}")).collect();
        let actual: BTreeSet<String> = certificates.iter()
            .map(|c| c["symbol"].as_str().unwrap().to_owned()).collect();
        assert_eq!(certificates.len(), 6, "{report}");
        assert_eq!(actual, expected, "{report}");
        let closed: BTreeSet<String> = report["closure"]["closed_kernel"].as_array().unwrap()
            .iter().map(|s| s.as_str().unwrap().to_owned()).collect();
        assert_eq!(closed, expected, "{report}");
        assert!(report["closure"]["unclosed"].as_array().unwrap().is_empty(), "{report}");
        for name in ["id", "not", "xor", "constant", "trunc", "rust_typed_not"] {
            let symbol = format!("trust_c_u8_{name}");
            let certificate = certificates.iter().find(|c| c["symbol"] == symbol).unwrap();
            assert_eq!(certificate["grade"], "[PROVED]", "{certificate}");
            assert_eq!(certificate["abi_contracts"][&symbol]["schema"],
                "trust-cg-bridge.darwin-c-u8-extension.v1", "{certificate}");
            // Canonical P digest pins declared width8 plus Zext on the real
            // result and (except trunc's u32) parameter. Erasing an extension
            // or changing the logical width cannot keep either digest.
            let expected = if name == "trunc" { "d3df5de477cebb3d26a08785abcb0e25d3e871a85586758808c15789c07a29af" }
                else { "7e2f4e71c701a4e1e00732f67298ffb4594c3759eb6f41a457ce13cc6ebb8eec" };
            assert_eq!(certificate["placement_sha256"][&symbol], expected, "{certificate}");
        }
        let driver = format!("driver-{opt}");
        cc().arg("-O2").arg("-Wall").arg("-Wextra").arg("-Werror")
            .input("driver.c").input("observe.S").input(&object).out_exe(&driver).run();
        cmd(format!("./{driver}")).run();
        // Default Strict covered all six real byte functions. Keep the old
        // closure's entire three-function denominator in its own control.
        anchor_control(opt);
    }
}

fn anchor_control(opt: &str) {
    let object = format!("anchor-{opt}.o");
    let args = [
        "anchor_control.rs", "--edition=2024", "--crate-type=lib", "--crate-name=source_c_u8_anchor",
        "--emit=obj", "-Cpanic=abort", "-Ccodegen-units=1", "-Coverflow-checks=off",
        "-Zunstable-options", "-Ztrust-verify=off", "-Ztrust-ir-lower=on",
        "-Ztrust-ir-flip=no", "-Zcodegen-backend=trust-cg", "-Ztrust-cg-frontend=trust-ir",
        "-Ztrust-cg-f1-backend=compiler",
    ];
    let mut compile = cmd(rustc_path());
    compile.args(args).arg(format!("-Copt-level={opt}"));
    if opt == "0" {
        // Diagnostic artifact only. Both existing O5 Unknowns must remain,
        // and the same source below must still fail under Strict.
        compile.arg("-Ztrust-cg-output-gate=allow-unknown");
    }
    compile.arg("-o").arg(&object).run().assert_stderr_contains("0 refuted");
    let report: serde_json::Value = serde_json::from_str(&rfs::read_to_string(
        format!("anchor-{opt}.trust-cg-certificates.json"))).unwrap();
    let rows = report["certificates"].as_array().unwrap();
    assert_eq!(rows.len(), 3, "{report}");
    let owner = rows.iter().find(|r| r["symbol"] == "trust_c_u8_source_anchor").unwrap();
    let adapter = rows.iter().find(|r| r["symbol"].as_str().unwrap()
        .starts_with("trust_c_u8_source_anchor__trust_closure_adapter_")).unwrap();
    let adapter_name = adapter["symbol"].as_str().unwrap();
    assert_eq!(adapter["linkage"], "Internal", "{adapter}");
    let body_name = adapter["call_sites"][0]["symbol"].as_str().unwrap();
    let body = rows.iter().find(|r| r["symbol"] == body_name).unwrap();
    assert_eq!(body["linkage"], "Internal", "{body}");
    let owner_target = owner["call_sites"][0]["symbol"].as_str().unwrap();
    assert!(owner_target == adapter_name || owner_target == body_name, "{owner}");
    let actual: BTreeSet<&str> = rows.iter().map(|r| r["symbol"].as_str().unwrap()).collect();
    assert_eq!(actual, BTreeSet::from(["trust_c_u8_source_anchor", adapter_name, body_name]));
    if opt == "0" {
        assert_eq!(body["grade"], "[PROVED]", "{body}");
        for row in [owner, adapter] {
            assert_eq!(row["grade"], "Unknown", "{row}");
            assert_eq!(row["obligations"]["o3_events"]["grade"], "Proven", "{row}");
            assert_eq!(row["obligations"]["o4_return"]["grade"], "Proven", "{row}");
            assert_eq!(row["obligations"]["o5_frame"]["grade"], "Unknown", "{row}");
        }
        let strict_object = "anchor-strict-0.o";
        assert!(!Path::new(strict_object).exists());
        cmd(rustc_path()).args(args).arg("-Copt-level=0")
            .arg("-Ztrust-cg-output-gate=strict").arg("-o").arg(strict_object).run_fail()
            .assert_stderr_contains("not closed-[PROVED]");
        assert!(!Path::new(strict_object).exists());
    } else {
        // The preserved source anchor has its own default-Strict positive
        // at O3. No Unknown is admitted as a passing shipping result.
        assert!(rows.iter().all(|r| r["grade"] == "[PROVED]"), "{report}");
        assert_eq!(report["closure"]["closed_kernel"].as_array().unwrap().len(), 3, "{report}");
        assert!(report["closure"]["unclosed"].as_array().unwrap().is_empty(), "{report}");
    }
}

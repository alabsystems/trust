//! Genuine source FnAbi + native compiler transport with full W0 CER proofs.
//! Prepared for the next matching source compiler; no synthetic instance or anchor.
//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64
//@ ignore-cross-compile

use run_make_support::{cc, cmd, rfs, rustc, rustc_path, serde_json};
use std::collections::BTreeSet;

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
    for (name, extension) in [("c_u16", "Zext"), ("rust_u16", "None"), ("c_i16", "Sext")] {
        let row = abi(&observed, name).split_whitespace().collect::<String>();
        assert_eq!(row.matches("mode:Direct(").count(), 2, "{name}: {row}");
        assert_eq!(row.matches(&format!("arg_ext:{extension}")).count(), 2, "{name}: {row}");
    }
    for opt in ["0", "3"] {
        let object = format!("native-{opt}.o");
        let args = [
            "subject.rs", "--edition=2024", "--crate-type=lib", "--crate-name=source_c_u16",
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
            .into_iter().map(|name| format!("trust_c_u16_{name}")).collect();
        let actual: BTreeSet<String> = certificates.iter()
            .map(|c| c["symbol"].as_str().unwrap().to_owned()).collect();
        assert_eq!(certificates.len(), 6, "{report}");
        assert_eq!(actual, expected, "{report}");
        let closed: BTreeSet<String> = report["closure"]["closed_kernel"].as_array().unwrap()
            .iter().map(|s| s.as_str().unwrap().to_owned()).collect();
        assert_eq!(closed, expected, "{report}");
        assert!(report["closure"]["unclosed"].as_array().unwrap().is_empty(), "{report}");
        for name in ["id", "not", "xor", "constant", "trunc", "rust_typed_not"] {
            let symbol = format!("trust_c_u16_{name}");
            let certificate = certificates.iter().find(|c| c["symbol"] == symbol).unwrap();
            assert_eq!(certificate["grade"], "[PROVED]", "{certificate}");
            assert_eq!(certificate["abi_contracts"][&symbol]["schema"],
                "trust-cg-bridge.darwin-c-u16-extension.v1", "{certificate}");
            assert_eq!(certificate["abi_contracts"][&symbol]["placement_sha256"],
                certificate["placement_sha256"][&symbol], "{certificate}");
            for slot in certificate["abi_contracts"][&symbol]["slots"].as_array().unwrap() {
                assert_eq!(slot["declared_width"],16,"{slot}");
                assert_eq!(slot["required_width"],32,"{slot}");
                assert_eq!(slot["extension"],"Zext","{slot}");
            }

        }
        let driver = format!("driver-{opt}");
        cc().arg("-O2").arg("-Wall").arg("-Wextra").arg("-Werror")
            .input("driver.c").input("observe.S").input(&object).out_exe(&driver).run();
        cmd(format!("./{driver}")).run();
    }
}

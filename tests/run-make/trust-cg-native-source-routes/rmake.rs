//! Real closure-free source -> native fullCompiler -> strict object regression.
//!
//! No positive compile names an output-gate policy: default Strict must close
//! the COMPLETE independently re-read object/function denominator in the kernel.
//! Rust source contract verification is off as in the compiler-lane recipe;
//! this does not disable the independent strict output-refinement gate.
//! Runtime C/assembly observers also read all64 scalar bits and all32 W0 bits.
//! This fixture is a requirement, not a claimed pass before a matching SDK runs it.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64
//@ ignore-cross-compile

use std::collections::BTreeSet;
use std::path::Path;

use run_make_support::object::{Architecture, Object, ObjectSection, ObjectSymbol, SymbolKind};
use run_make_support::serde_json::Value;
use run_make_support::{cc, cmd, rfs, rustc, serde_json};

const SCHEMA: &str = "trust-cg-bridge.call-refinement.v1";
// FnPlacement's canonical derived JSON preserves declared widths/extensions.
// params=[], return Scalar(Gpr0,width64,None).
const CONST_P: &str = "12f6eb711fc9cac9ef56f674ecb7e166e4435ca8e6a507ca9de5d20f48378796";
// params=[Scalar(Gpr0,width64,None)], same return; C and Rust both carry full64.
const U64_P: &str = "fa7c74b229b731ae66dbc378df626d1ccd174e928ededf252cad250645e22fa7";
// params=[Scalar(Gpr0,width8,Zext)], return Scalar(Gpr0,width8,Zext).
const C_U8_P: &str = "7e2f4e71c701a4e1e00732f67298ffb4594c3759eb6f41a457ce13cc6ebb8eec";
// params=[Scalar(Gpr0,width16,Zext)], return Scalar(Gpr0,width16,Zext).
const C_U16_P: &str = "919b96a3505561775833746dbee2e56a11d25df79449bb00291b96968acc1631";
// Exact signed8 source parameter/result widths with Sext flags retained.
const C_I8_P: &str = "e27876ff684bbd2e8021cf44a1f3b7b697dafac859e3911b74caf83329b19071";

struct Subject {
    source: &'static str,
    stem: &'static str,
    exported: &'static str,
    functions: usize,
    placement: &'static str,
}

const SUBJECTS: &[Subject] = &[
    Subject { source: "constant.rs", stem: "constant", exported: "ordinary_constant", functions: 1, placement: CONST_P },
    Subject { source: "identity.rs", stem: "identity", exported: "ordinary_identity", functions: 1, placement: U64_P },
    Subject { source: "local_helper.rs", stem: "local_helper", exported: "ordinary_helper_call", functions: 2, placement: U64_P },
    Subject { source: "c_u8.rs", stem: "c_u8", exported: "ordinary_c_byte", functions: 1, placement: C_U8_P },
    Subject { source: "wide_byte.rs", stem: "wide_byte", exported: "ordinary_wide_byte", functions: 1, placement: C_U16_P },
    Subject { source: "raw_pointer.rs", stem: "raw_pointer", exported: "ordinary_raw_pointer", functions: 1, placement: U64_P },
    Subject { source: "signed_byte.rs", stem: "signed_byte", exported: "ordinary_signed_byte", functions: 1, placement: C_I8_P },
];

fn compiler(source: &str, name: &str, opt: &str, object: &str) -> run_make_support::Rustc {
    let mut command = rustc();
    command.input(source).crate_name(name).crate_type("lib").edition("2024")
        .arg("--emit=obj")
        .arg("-Cpanic=abort").arg("-Ccodegen-units=1")
        .arg("-Coverflow-checks=off").arg(format!("-Copt-level={opt}"))
        .arg("-Zunstable-options").arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower=on").arg("-Ztrust-ir-flip=no")
        .arg("-Zcodegen-backend=trust-cg").arg("-Ztrust-cg-frontend=trust-ir")
        .arg("-Ztrust-cg-f1-backend=compiler")
        .arg("-o").arg(object)
        .env_remove("TRUST_NO_VERIFY");
    command
}

fn certificate_path(object: &str) -> String {
    Path::new(object).with_extension("trust-cg-certificates.json").to_str().unwrap().into()
}

fn clear_owned_outputs(object: &str) {
    for file in [object.to_string(), certificate_path(object)] {
        if Path::new(&file).exists() { rfs::remove_file(file); }
    }
}

fn sha256(path: &str) -> String {
    cmd("shasum").args(["-a", "256", path]).run().stdout_utf8()
        .split_whitespace().next().expect("SHA256 digest").to_owned()
}

fn strings(value: &Value) -> BTreeSet<String> {
    value.as_array().expect("complete JSON array").iter()
        .map(|value| value.as_str().expect("symbol").to_owned()).collect()
}

fn check_contract(certificate: &Value, symbol: &str, width: u64, placement: &str, signed: bool) {
    let contracts = certificate["abi_contracts"].as_object().expect("physical ABI contracts");
    assert_eq!(contracts.len(), 1, "only this real C boundary: {certificate}");
    let contract = &contracts[symbol];
    let kind = if signed { "i" } else { "u" };
    assert_eq!(contract["schema"], format!("trust-cg-bridge.darwin-c-{kind}{width}-extension.v1"));
    assert_eq!(contract["calling_convention"], "C");
    assert_eq!(contract["placement_sha256"], placement);
    assert!(matches!(contract["target"].as_str(), Some("arm64-apple-macosx" | "aarch64-apple-darwin")));
    let slots = contract["slots"].as_array().expect("argument and result contracts");
    assert_eq!(slots.len(), 2, "full exact u{width} parameter/result contract: {contract}");
    for (index, slot) in slots.iter().enumerate() {
        assert_eq!(slot["parameter"], if index == 0 { serde_json::json!(0) } else { Value::Null });
        assert_eq!(slot["slot"], serde_json::json!({"Gpr": 0}));
        assert_eq!(slot["declared_width"], width, "never reforge a width32 source value");
        assert_eq!(slot["required_width"], 32);
        assert_eq!(slot["extension"], if signed { "Sext" } else { "Zext" }, "never erase real FnAbi flags");
    }
}

/// Re-read the actual object, not a producer-reported expected body list.
fn check_certificates(subject: &Subject, object: &str, directory: &str) -> Value {
    let data = rfs::read(object);
    let parsed = run_make_support::object::File::parse(&*data).expect("actual object");
    assert_eq!(parsed.architecture(), Architecture::Aarch64);
    assert!(parsed.is_little_endian());
    let defined_rows: Vec<String> = parsed.symbols()
        .filter(|symbol| symbol.is_definition() && symbol.kind() == SymbolKind::Text)
        .map(|symbol| symbol.name().unwrap().strip_prefix('_').expect("Mach-O symbol prefix").to_owned())
        .collect();
    let defined: BTreeSet<String> = defined_rows.iter().cloned().collect();
    assert_eq!(defined_rows.len(), defined.len(), "no duplicate/aliased function names");
    assert_eq!(defined.len(), subject.functions, "whole actual object denominator for {object}: {defined:?}");
    assert!(defined.contains(subject.exported), "real source export: {defined:?}");
    let text = parsed.section_by_name("__text").expect("the actual code section").data().unwrap();
    let report: Value = serde_json::from_str(&rfs::read_to_string(certificate_path(object))).unwrap();
    assert_eq!(report["schema"], SCHEMA);
    assert_eq!(report["object_sha256"], sha256(object), "certificate binds the actual linked object");
    let certificates = report["certificates"].as_array().expect("whole certificate denominator");
    let certified: BTreeSet<String> = certificates.iter().map(|c| c["symbol"].as_str().unwrap().into()).collect();
    assert_eq!(certificates.len(), certified.len(), "no duplicate certificates");
    assert_eq!(certified, defined, "no dropped/added body or artificial closure anchor: {report}");
    let closed = report["closure"]["closed_kernel"].as_array().unwrap();
    assert_eq!(closed.len(), certificates.len(), "EVERY actual function is kernel-closed: {report}");
    assert_eq!(strings(&report["closure"]["closed_kernel"]), certified);
    // closed_proven is the legacy all-Proven superset, including kernel rows;
    // strict authority above comes specifically from closed_kernel.
    assert_eq!(strings(&report["closure"]["closed_proven"]), certified);
    assert!(report["closure"]["unclosed"].as_array().unwrap().is_empty(), "{report}");

    for (index, certificate) in certificates.iter().enumerate() {
        let symbol = certificate["symbol"].as_str().unwrap();
        assert_eq!(certificate["schema"], SCHEMA);
        assert_eq!(certificate["grade"], "[PROVED]", "default strict must prove every row: {certificate}");
        assert_eq!(certificate["section"], "__TEXT,__text");
        let extent = certificate["extent"].as_array().unwrap();
        let start = usize::try_from(extent[0].as_u64().unwrap()).unwrap();
        let end = usize::try_from(extent[1].as_u64().unwrap()).unwrap();
        assert!(start < end && end <= text.len());
        let bytes = format!("{directory}/{}-function-{index}.bin", subject.stem);
        rfs::write(&bytes, &text[start..end]);
        assert_eq!(certificate["text_sha256"], sha256(&bytes), "exact emitted function bytes");
        let placements = certificate["placement_sha256"].as_object().unwrap();
        assert_eq!(placements[symbol], subject.placement, "exact source FnAbi P: {certificate}");
        let mut expected_p = BTreeSet::from([symbol.to_owned()]);
        for site in certificate["call_sites"].as_array().unwrap() {
            expected_p.insert(site["symbol"].as_str().unwrap().to_owned());
        }
        assert_eq!(placements.keys().cloned().collect::<BTreeSet<_>>(), expected_p,
            "no missing or invented placement row: {certificate}");
        for digest in placements.values() { assert_eq!(digest, subject.placement, "full actual P denominator: {certificate}"); }
        for assumption in certificate["assumptions"].as_array().unwrap() {
            assert_eq!(assumption["kind"], "CoEmitted", "no external ABI escape: {certificate}");
            assert!(certified.contains(assumption["symbol"].as_str().unwrap()), "callee premise must have its own certificate");
        }
        match subject.stem {
            "c_u8" => check_contract(certificate, symbol, 8, C_U8_P, false),
            "wide_byte" => check_contract(certificate, symbol, 16, C_U16_P, false),
            "signed_byte" => check_contract(certificate, symbol, 8, C_I8_P, true),
            _ => {}
        }
    }

    if subject.stem == "local_helper" {
        let helper: Vec<_> = certified.iter().filter(|symbol| symbol.contains("local_adjust")).collect();
        assert_eq!(helper.len(), 1, "exact real typed helper, not a generated adapter: {certified:?}");
        let helper = helper[0].as_str();
        let caller = certificates.iter().find(|c| c["symbol"] == subject.exported).unwrap();
        let calls = caller["call_sites"].as_array().unwrap();
        assert_eq!(calls.len(), 1, "the non-inlined typed source call remains real: {caller}");
        assert_eq!(calls[0]["symbol"], helper);
        let pc = usize::try_from(calls[0]["offset"].as_u64().unwrap()).unwrap();
        let word = u32::from_le_bytes(text[pc..pc + 4].try_into().unwrap());
        match calls[0]["kind"].as_str().unwrap() {
            "Direct" => assert_eq!(word & 0xfc00_0000, 0x9400_0000, "actual BL"),
            "Tail" => assert_eq!(word & 0xfc00_0000, 0x1400_0000, "actual tail B"),
            other => panic!("typed helper may not disappear into {other}"),
        }
        assert_eq!(caller["placement_sha256"].as_object().unwrap().len(), 2);
    }
    report
}

fn main() {
    for opt in ["0", "3"] {
        let directory = format!("native-o{opt}");
        rfs::create_dir_all(&directory);
        let mut objects = Vec::new();
        let mut actual_certificates = 0;
        for subject in SUBJECTS {
            let object = format!("{directory}/{}.o", subject.stem);
            clear_owned_outputs(&object);
            // Intentionally NO output-gate flag and no AllowUnknown fallback.
            let emitted = compiler(subject.source, &format!("native_routes_{}", subject.stem), opt, &object).run();
            emitted.assert_stderr_contains("source -> trust_ir_of -> codegen_module (the compiler lane");
            emitted.assert_stderr_contains("policy: strict (certified-fragment: only [PROVED] ships)");
            emitted.assert_stderr_not_contains("lower_module_to_lir");
            emitted.assert_stderr_not_contains("policy: allow-unknown");
            let report = check_certificates(subject, &object, &directory);
            actual_certificates += report["certificates"].as_array().unwrap().len();
            objects.push(object);
        }
        assert_eq!(actual_certificates, 8, "all seven source cases plus the actual helper");
        let driver = format!("{directory}/driver");
        let mut native = cc();
        native.arg("-O2").arg("-Wall").arg("-Wextra").arg("-Werror")
            .input("driver.c").input("observe.S");
        for object in &objects { native.input(object); }
        native.out_exe(&driver).run();
        let observed = cmd(format!("./{driver}")).run();
        observed.assert_stdout_contains("native source routes: full64 and all 256 C-u8 W0 cases PASS");
        observed.assert_stdout_contains("C-u16 W0 boundary cases PASS");
        observed.assert_stdout_contains("raw pointer full64/null transport PASS");
    }

    // Retain the original signed_byte source as a positive with its exact
    // actual Sext/W32 contract. Weaker flags/padding remain explicit negative
    // controls in the ABI suite; gate-off remains independently refused below.
    let object = "native-o0/gate-off.o";
    clear_owned_outputs(object);
    compiler("constant.rs", "native_gate_off_control", "0", object)
        .arg("-Ztrust-cg-output-gate=off").run_fail()
        .assert_stderr_contains("call-event gate is the compiler lane's only shipping authority");
    assert!(!Path::new(object).exists() && !Path::new(&certificate_path(object)).exists());
}

//@ ignore-cross-compile
//! Execute real source calls, preserve callee/argument effects, refuse wide
//! substitution, and retain the named source-effect comparison accounting.
//! The supported source also executes through strict TrustIR -> TrustCG objects.
//! The exact-source core model remains a versioned frontend/TCB premise: an IR
//! native certificate does not establish Rust refinement or grant a proof license.
use run_make_support::{cc, cmd, rfs, rustc_path, serde_json, trust_ir};
use std::collections::BTreeSet;
use trust_ir::reference::{Inst, Ty, binary::deserialize_module,
    interpret::{InterpretValue, Interpreter}};

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() { return; }
    rfs::write("native.rs", format!("{}\nfn main() {{ assert!(same_home()); \
        assert!(!different_homes()); assert_eq!(effect_order(), 1231); \
        assert!(!unrelated_eq()); }}", rfs::read_to_string("subject.rs")));
    cmd(rustc_path()).args(["native.rs", "--edition=2024", "-Ztrust-verify=off",
        "-Ztrust-ir-lower=off", "-Coverflow-checks=on", "-Copt-level=0", "-o", "native"]).run();
    cmd("./native").run();
    cmd(rustc_path()).args(["subject.rs", "--edition=2024", "--crate-type=lib",
        "--crate-name=thin_ptr_eq", "--emit=metadata", "-Coverflow-checks=on",
        "-Copt-level=0", "-Zthreads=1", "-Ztrust-verify=off", "-Ztrust-ir-lower=on",
        "-Ztrust-ir-flip=no", "-Ztrust-dump=ir:ir", "-o", "subject.rmeta"]).run();
    let module = deserialize_module(&rfs::read("ir/thin_ptr_eq.trust-ir.bin")).unwrap();
    let interpreter = Interpreter::with_module(&module);
    let effects: serde_json::Value = serde_json::from_slice(
        &rfs::read("ir/thin_ptr_eq.effect-conservation.json")).unwrap();
    for (name, expected) in [
        ("same_home", InterpretValue::bool(true)),
        ("different_homes", InterpretValue::bool(false)),
        ("effect_order", InterpretValue::int(Ty::U32, 1231).unwrap()),
        ("unrelated_eq", InterpretValue::bool(false)),
    ] {
        let function = module.functions.iter()
            .find(|function| function.display_path.as_deref() == Some(name)).unwrap();
        let result = interpreter.execute_func(function.id, []).unwrap();
        assert_eq!(result.host_calls, 0, "{name}: no host substitution");
        assert_eq!(result.returns, vec![expected], "{name}");
        let row = effects["functions"].as_array().unwrap().iter()
            .find(|row| row["def_path"] == name).unwrap();
        assert_eq!(row["verdict"], "conserved", "{name}: {row}");
        assert!(row["tags"].as_array().unwrap().is_empty(), "{name}: {row}");
        if name != "unrelated_eq" {
            let comparisons = function.blocks.iter().flat_map(|block| &block.body)
                .filter(|node| matches!(&node.inst, Inst::ICmp { ty: Ty::Ptr, .. })).count();
            assert_eq!(comparisons, 1, "{name}: actual pointer operation");
        }
    }
    assert!(!module.functions.iter()
        .any(|function| function.display_path.as_deref() == Some("wide")),
        "a metadata-sensitive refused body must not enter the assembled module");
    let coverage: serde_json::Value = serde_json::from_slice(
        &rfs::read("ir/thin_ptr_eq.coverage.json")).unwrap();
    let wide = coverage["bodies"].as_array().unwrap().iter()
        .find(|row| row["def_path"] == "wide").expect("explicit wide source coverage row");
    assert_eq!(wide["lowered"], false);
    assert_eq!(wide["spliced"], false);
    assert!(wide["func_id"].is_null());
    assert!(wide["unsupported"].as_array().unwrap().iter().any(|row|
        row[0].as_str().is_some_and(|reason|
            reason.starts_with("UnsignableRustAbiDeclaration(std::ptr::eq)"))),
        "wide: exact original refusal must remain recorded: {wide}");
    assert!(!effects["functions"].as_array().unwrap().iter()
        .any(|row| row["def_path"] == "wide"),
        "a refused wide body gets no thin comparison effect equivalence");
    cmd(rustc_path()).args(["subject.rs", "--edition=2024", "--crate-type=lib",
        "--crate-name=thin_ptr_eq_strict", "--emit=metadata", "-Coverflow-checks=on",
        "-Copt-level=0", "-Zthreads=1", "-Ztrust-verify=off", "-Ztrust-ir-lower=strict",
        "-Ztrust-ir-flip=no", "-o", "strict.rmeta"]).run();
    // Verification-off is the master switch: Strict deliberately degrades to
    // diagnostic On there. Request verification for the strict body refusal.
    // Advisory obligation policy keeps this a lowering control, not a proof claim.
    cmd(rustc_path()).args(["subject.rs", "--edition=2024", "--crate-type=lib",
        "--crate-name=thin_ptr_eq_strict_on", "--emit=metadata", "-Coverflow-checks=on",
        "-Copt-level=0", "-Zthreads=1", "-Ztrust-verify=on", "-Ztrust-policy=advisory",
        "-Ztrust-ir-lower=strict", "-Ztrust-ir-flip=no", "-o", "strict-on.rmeta"])
        .run_fail().assert_stderr_contains("UnsignableRustAbiDeclaration(std::ptr::eq)");
    // Keep the existing diagnostic controls on other targets. Native execution
    // is qualified here only where this fixture runs the actual Apple ARM64 route.
    if cfg!(all(target_arch = "aarch64", target_os = "macos")) {
        execute_trust_cg();
    }
}

/// Use the existing compiler frontend/backend and strict output gate. No MIR
/// fallback, host-call interpreter, edited IR or permissive native gate enters
/// this route. The source model's disclosed TCB grade is unchanged.
fn execute_trust_cg() {
    for opt in ["0", "3"] {
        let object = format!("cg-{opt}.o");
        let ir = format!("ir-cg-{opt}");
        let output = cmd(rustc_path()).args([
            "cg_native.rs", "--edition=2024", "--crate-type=lib",
            "--crate-name=thin_ptr_eq_native", "--emit=obj", "--cfg=trust_cg_native",
            "-Cpanic=abort", "-Ccodegen-units=1", "-Coverflow-checks=off",
            &format!("-Copt-level={opt}"), "-Zmir-opt-level=0", "-Zthreads=1",
            "-Zunstable-options", "-Ztrust-verify=off", "-Ztrust-ir-lower=on",
            "-Ztrust-ir-flip=no", "-Zcodegen-backend=trust-cg",
            "-Ztrust-cg-frontend=trust-ir", "-Ztrust-cg-f1-backend=compiler",
            &format!("-Ztrust-dump=ir:{ir}"), "-o", &object,
        ]).run();
        output.assert_stderr_contains("trust-cg trust-ir frontend:");
        let report: serde_json::Value = serde_json::from_slice(
            &rfs::read(format!("cg-{opt}.trust-cg-certificates.json"))).unwrap();
        let certificates = report["certificates"].as_array().unwrap();
        assert!(!certificates.is_empty(), "O{opt}: actual native certificates required");
        let symbols: BTreeSet<_> = certificates.iter().map(|row| {
            assert_eq!(row["grade"], "[PROVED]", "O{opt}: {row}");
            row["symbol"].as_str().unwrap().to_owned()
        }).collect();
        assert_eq!(symbols.len(), certificates.len(), "O{opt}: duplicate certificate rows");
        for export in ["thin_same_home", "thin_different_homes", "thin_effect_order",
            "thin_unrelated_eq"] {
            assert!(symbols.contains(export), "O{opt}: missing actual exported caller {export}: {report}");
        }
        assert!(report["closure"]["unclosed"].as_array().unwrap().is_empty(), "O{opt}: {report}");
        let closed: BTreeSet<_> = report["closure"]["closed_kernel"].as_array().unwrap()
            .iter().map(|row| row.as_str().unwrap().to_owned()).collect();
        assert_eq!(symbols, closed, "O{opt}: every emitted row must close independently");
        let module = deserialize_module(&rfs::read(
            format!("{ir}/thin_ptr_eq_native.trust-ir.bin"))).unwrap();
        for name in ["same_home", "different_homes", "effect_order", "unrelated_eq"] {
            let functions: Vec<_> = module.functions.iter().filter(|function|
                function.display_path.as_deref() == Some(name)).collect();
            assert_eq!(functions.len(), 1, "O{opt}: actual original source row {name}");
            let comparisons = functions[0].blocks.iter().flat_map(|block| &block.body)
                .filter(|node| matches!(&node.inst, Inst::ICmp { ty: Ty::Ptr, .. })).count();
            assert_eq!(comparisons, usize::from(name != "unrelated_eq"),
                "O{opt}: the exact thin model cannot capture an unrelated equal-spelling function");
        }
        assert!(!module.functions.iter().any(|function|
            function.display_path.as_deref() == Some("wide")),
            "O{opt}: wide source was deliberately excluded from this supported native unit");
        let executable = format!("cg-driver-{opt}");
        cc().arg("-Wall").arg("-Wextra").arg("-Werror")
            .input("driver.c").input(&object).out_exe(&executable).run();
        cmd(format!("./{executable}")).run();
    }
    // Compile the unchanged full subject WITHOUT the native-only cfg: the
    // metadata-sensitive function must still refuse on this real frontend.
    cmd(rustc_path()).args([
        "subject.rs", "--edition=2024", "--crate-type=lib",
        "--crate-name=thin_ptr_eq_native_wide_refused", "--emit=obj",
        "-Cpanic=abort", "-Ccodegen-units=1", "-Copt-level=0",
        "-Zmir-opt-level=0", "-Zunstable-options", "-Ztrust-verify=off",
        "-Ztrust-ir-lower=on", "-Ztrust-ir-flip=no", "-Zcodegen-backend=trust-cg",
        "-Ztrust-cg-frontend=trust-ir", "-Ztrust-cg-f1-backend=compiler",
        "-o", "wide-refused.o",
    ]).run_fail().assert_stderr_contains("UnsignableRustAbiDeclaration(std::ptr::eq)");
}

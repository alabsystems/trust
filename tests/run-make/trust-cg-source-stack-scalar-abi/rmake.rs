//! Actual source-produced F1 scalar stack transport and LLVM executable oracle.
//! Stack/FP has no call-event placement P or proof model: every certificate stays
//! Unknown and Strict must refuse. AllowUnknown is explicit for runtime tests.
//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64
//@ ignore-cross-compile

use run_make_support::{cc, cmd, llvm_objdump, regex, rfs, rustc, serde_json};
use std::collections::BTreeSet;
use std::path::Path;

// Count only a decoded AArch64 call/tail-branch operand or its immediately
// associated BRANCH26 relocation, never a symbol-table/header mention.
fn calls_symbol(disassembly: &str, symbol: &str) -> bool {
    let instruction = regex::Regex::new(r"^\s*[0-9a-fA-F]+:\s+(\S+)\s*(.*)$").unwrap();
    let direct = [symbol.to_owned(), format!("_{symbol}"), format!("<{symbol}>"), format!("<_{symbol}>")];
    let mut branch = false;
    for line in disassembly.lines() {
        if line.contains("ARM64_RELOC_BRANCH26") {
            let matched = branch && line.split_whitespace().last().is_some_and(|target| direct[..2].contains(&target.to_owned()));
            branch = false;
            if matched { return true; }
            continue;
        }
        if let Some(decoded) = instruction.captures(line) {
            branch = matches!(&decoded[1], "b" | "bl");
            if branch && decoded[2].split_whitespace().any(|target| direct.contains(&target.to_owned())) { return true; }
        } else if !line.trim().is_empty() {
            branch = false;
        }
    }
    false
}

fn observe_calls(object: &str, opt: &str) {
    let disassembly = llvm_objdump().disassemble().arg("-r").arg("--no-show-raw-insn").input(object).run().stdout_utf8();
    rfs::write(format!("native-{opt}.disassembly.txt"), &disassembly);
    for symbol in ["original_stack_mixed"] {
        assert!(calls_symbol(&disassembly, symbol), "no actual external C branch to {symbol}: {disassembly}");
    }
    // O3 may transform local calls. Only O0 claims physical Rust helper calls;
    // both levels still execute the complete C/LLVM differential population.
    if opt == "0" {
        for symbol in ["rust_stack_helper"] {
            assert!(calls_symbol(&disassembly, symbol), "no actual O0 local Rust branch to {symbol}: {disassembly}");
        }
    }
}

fn main() {
    assert!(!calls_symbol("0000000000000000 <_rust_stack_helper>:\n  0: ret\n", "rust_stack_helper"));
    assert!(!calls_symbol("  0: adr x0, _rust_stack_helper\n  0: ARM64_RELOC_UNSIGNED _rust_stack_helper\n", "rust_stack_helper"));
    assert!(calls_symbol("  0: bl 0x0\n  0: ARM64_RELOC_BRANCH26 _rust_stack_helper\n", "rust_stack_helper"));
    let expected: BTreeSet<_> = ["trust_stack_int", "trust_stack_f32", "trust_stack_f64", "trust_stack_mixed", "trust_stack_outgoing", "trust_stack_local", "rust_stack_helper"].into_iter().collect();
    for opt in ["0", "3"] {
        let mut oracle = None;
        for native in [false, true] {
            let label = if native { "native" } else { "oracle" };
            let object = format!("{label}-{opt}.o");
            let mut compile = rustc();
            compile.input("subject.rs").crate_name("source_stack_scalar").crate_type("lib").edition("2024")
                .arg("--emit=obj").arg("-Cpanic=abort").arg("-Ccodegen-units=1")
                .arg(format!("-Copt-level={opt}")).arg("-Ztrust-verify=off")
                .arg("-Ztrust-ir-lower=on").arg("-Ztrust-ir-flip=no").output(&object)
                .env_remove("TRUST_NO_VERIFY");
            if native {
                compile.arg("-Zunstable-options").arg("-Zcodegen-backend=trust-cg")
                    .arg("-Ztrust-cg-frontend=trust-ir").arg("-Ztrust-cg-f1-backend=compiler")
                    .arg("-Ztrust-cg-output-gate=allow-unknown");
            }
            let emitted = compile.run();
            if native {
                emitted.assert_stderr_contains("0 refuted");
                observe_calls(&object, opt);
                let report: serde_json::Value = serde_json::from_str(&rfs::read_to_string(format!("native-{opt}.trust-cg-certificates.json"))).unwrap();
                let rows = report["certificates"].as_array().unwrap();
                let names: BTreeSet<_> = rows.iter().map(|r| r["symbol"].as_str().unwrap()).collect();
                assert!(expected.is_subset(&names), "{report}");
                assert!(rows.iter().all(|r| r["grade"] == "Unknown"), "{report}");
                assert!(report["closure"]["closed_kernel"].as_array().unwrap().is_empty(), "{report}");
                for row in rows {
                    let placements = row["placement_sha256"].as_object().expect("certificate placement_sha256 schema must be an object");
                    let own = row["symbol"].as_str().expect("certificate symbol schema");
                    if own != "trust_stack_local" {
                        assert!(!placements.contains_key(own), "stack/FP must not invent register P: {row}");
                    }
                    for call in row["call_sites"].as_array().expect("certificate call_sites schema") {
                        let callee = call["symbol"].as_str().expect("call symbol schema");
                        assert!(!placements.contains_key(callee), "stack/FP callee must not invent register P: {row}");
                    }
                }
            }
            let driver = format!("{label}-driver-{opt}");
            cc().arg("-O2").arg("-Wall").arg("-Wextra").arg("-Werror").input("driver.c").input(&object).out_exe(&driver).run();
            let got = cmd(format!("./{driver}")).run().stdout_utf8();
            if let Some(expected) = &oracle { assert_eq!(&got, expected); } else { oracle = Some(got); }
        }
        let object = format!("strict-{opt}.o");
        assert!(!Path::new(&object).exists());
        rustc().input("subject.rs").crate_name("source_stack_scalar_strict").crate_type("lib").edition("2024")
            .arg("--emit=obj").arg("-Cpanic=abort").arg("-Ccodegen-units=1").arg(format!("-Copt-level={opt}"))
            .arg("-Ztrust-verify=off").arg("-Ztrust-ir-lower=on").arg("-Ztrust-ir-flip=no")
            .arg("-Zunstable-options").arg("-Zcodegen-backend=trust-cg").arg("-Ztrust-cg-frontend=trust-ir")
            .arg("-Ztrust-cg-f1-backend=compiler").arg("-Ztrust-cg-output-gate=strict").output(&object)
            .run_fail().assert_stderr_contains("not closed-[PROVED]");
        assert!(!Path::new(&object).exists());
    }
}

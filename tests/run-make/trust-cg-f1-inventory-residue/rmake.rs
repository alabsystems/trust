//! Trust (step 2 increment 5, sub-step 5.4.2; design `docs/design/2026-10-01-step2-inc5-real-calls-
//! retarget.md` §3.1 rule 2): INVENTORY RESIDUE on F1's compiler lane.
//!
//! At `-Copt-level=2` the MIR inliner folds a small local helper into its caller and rustc's
//! mono-item inventory no longer names the helper. The trust-ir producer is THIR-based, so the
//! caller's trust-ir still CALLS the helper. On the compiler lane (`-Ztrust-cg-f1-backend=compiler`)
//! that helper is inventory residue: a local, non-generic handoff body, emitted with `Internal`
//! linkage under its own symbol, verified by the call-event gate like every other body, and
//! disclosed per function as `inventory-residue-local` in the coverage artifact.
//!
//! Pinned: the helper is a LOCAL text symbol (`t` in `nm`), the coverage artifact carries its row,
//! the stderr note names it, and the executed output equals the LLVM build's. At `-Copt-level=0`
//! the helper is in the inventory, so it is an ordinary work-list item and no residue row exists.
//!
//! Pinned since the 5.4.2 review: the row says WHERE the helper's code ships. At `-O2` trust-cg's
//! OPT-4 inlines it into `r0` (r0's certificate records an `InterpretedInline` site naming it, and
//! `r0`'s bytes make no call), so the row's `inlined_into` must name `r0` and the note must say
//! "inlined into `r0`"; the row's `inlined_into` must equal exactly the certificates whose
//! `InterpretedInline` sites name the helper. Before the fix the lane wrote `inlined_into: []`.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::object::read::archive::ArchiveFile;
use run_make_support::serde_json::Value;
use run_make_support::{cc, cmd, rfs, run, rust_lib_name, rustc, serde_json};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";

const SOURCE: &str = r#"fn residue_helper(x: u64) -> u64 { x ^ 0x77 }
#[unsafe(no_mangle)] pub extern "C" fn r0(x: u64) -> u64 { residue_helper(x) | 1 }
"#;

const INPUTS: &[&str] = &["0", "1", "119", "120", "255", "65535", "18446744073709551615"];

fn compile(out: &str, f1: bool, opt: &str) -> run_make_support::Rustc {
    rfs::create_dir_all(out);
    let mut cmd = rustc();
    cmd.input("residue.rs")
        .crate_name("residue")
        .crate_type("rlib")
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Ccodegen-units=1")
        .arg("-Coverflow-checks=off")
        .arg(format!("-Copt-level={opt}"))
        .arg("-Ztrust-verify=off")
        .out_dir(out)
        .env_remove(TRUST_NO_VERIFY_ENV);
    if f1 {
        cmd.arg("-Zunstable-options")
            .arg("-Zcodegen-backend=trust-cg")
            .arg("-Ztrust-cg-frontend=trust-ir")
            .arg("-Ztrust-ir-lower")
            .arg("-Ztrust-cg-f1-backend=compiler")
            .arg("-Ztrust-cg-output-gate=allow-unknown");
    }
    cmd
}

fn object_member(rlib: &str) -> Vec<u8> {
    let data = rfs::read(rlib);
    let archive = ArchiveFile::parse(&*data).expect("rlib is an archive");
    let mut objects = Vec::new();
    for member in archive.members() {
        let member = member.expect("archive member");
        if member.name().ends_with(b".o") {
            objects.push(member.data(&*data).expect("member data").to_vec());
        }
    }
    assert_eq!(objects.len(), 1, "one codegen unit, one object");
    objects.pop().unwrap()
}

fn run_lane(tag: &str, object: &[u8]) -> String {
    rfs::write(format!("{tag}.o"), object);
    let calls = INPUTS
        .iter()
        .map(|x| format!("printf(\"%llu \", (unsigned long long)r0({x}ULL));"))
        .collect::<String>();
    rfs::write(
        format!("{tag}.c"),
        format!(
            "#include <stdint.h>\n#include <stdio.h>\nextern uint64_t r0(uint64_t);\n\
             int main(void) {{ {calls} printf(\"\\n\"); return 0; }}\n"
        ),
    );
    cc().input(format!("{tag}.c")).input(format!("{tag}.o")).out_exe(tag).run();
    run(tag).stdout_utf8()
}

fn main() {
    rfs::write("residue.rs", SOURCE);
    let lib = rust_lib_name("residue");
    for (opt, residue) in [("2", true), ("0", false)] {
        let llvm = format!("out_llvm_o{opt}");
        compile(&llvm, false, opt).run();
        let oracle = run_lane(&format!("llvm_o{opt}"), &object_member(&format!("{llvm}/{lib}")));

        let out = format!("out_f1_o{opt}");
        let stderr = compile(&out, true, opt).run().stderr_utf8();
        assert!(!stderr.contains("internal compiler error"), "-O{opt}: {stderr}");
        let object = object_member(&format!("{out}/{lib}"));
        let f1 = run_lane(&format!("f1_o{opt}"), &object);
        assert_eq!(f1, oracle, "-O{opt}: the compiler lane and LLVM disagree on executed output");

        rfs::write(format!("f1_o{opt}.nm.o"), &object);
        let symbols = cmd("nm").arg(format!("f1_o{opt}.nm.o")).run().stdout_utf8();
        let helper = symbols
            .lines()
            .find(|l| l.contains("residue_helper"))
            .unwrap_or_else(|| panic!("-O{opt}: no helper symbol:\n{symbols}"));
        let coverage_path = format!("{out}/residue.trust-instance-coverage.json");
        if residue {
            assert!(
                helper.contains(" t "),
                "-O{opt}: the residue is a LOCAL text symbol: {helper}"
            );
            assert!(stderr.contains("inventory-residue-local"), "-O{opt}: the note:\n{stderr}");
            let coverage = rfs::read_to_string(&coverage_path);
            let row = coverage
                .lines()
                .find(|l| l.contains("residue_helper"))
                .unwrap_or_else(|| panic!("-O{opt}: no coverage row:\n{coverage}"));
            assert!(row.contains("\"kind\": \"inventory-residue-local\""), "{row}");
            assert!(row.contains("\"emitted_as_own_symbol\": true"), "{row}");
            // WHERE the helper's code ships: exactly the functions whose certificates record an
            // `InterpretedInline` site naming it, and (measured) `r0` among them at -O2.
            let certificates: Value = serde_json::from_str(&rfs::read_to_string(format!(
                "{out}/residue.trust-cg-certificates.json"
            )))
            .expect("the certificates file is JSON");
            let mut inliners: Vec<String> = certificates["certificates"]
                .as_array()
                .expect("certificates")
                .iter()
                .filter(|c| {
                    c["call_sites"].as_array().expect("call_sites").iter().any(|s| {
                        s["kind"] == "InterpretedInline"
                            && s["symbol"].as_str().is_some_and(|s| s.contains("residue_helper"))
                    })
                })
                .map(|c| c["symbol"].as_str().expect("symbol").to_string())
                .collect();
            inliners.sort();
            assert_eq!(inliners, ["r0"], "-O{opt}: OPT-4 inlines the helper into r0 (measured)");
            let rows: Value = serde_json::from_str(&coverage).expect("the coverage file is JSON");
            let row = rows["rows"]
                .as_array()
                .expect("rows")
                .iter()
                .find(|r| r["symbol"].as_str().is_some_and(|s| s.contains("residue_helper")))
                .expect("the helper's row");
            let mut inlined_into: Vec<String> = row["inlined_into"]
                .as_array()
                .expect("inlined_into")
                .iter()
                .map(|s| s.as_str().expect("a symbol").to_string())
                .collect();
            inlined_into.sort();
            assert_eq!(
                inlined_into, inliners,
                "-O{opt}: the coverage row must name every function its code is inlined into"
            );
            assert!(
                stderr.contains("inventory-residue-local")
                    && stderr.lines().any(|l| l.contains("inventory-residue-local")
                        && l.contains("inlined into `r0`")),
                "-O{opt}: the note says where the helper's code ships:\n{stderr}"
            );
        } else {
            assert!(!stderr.contains("inventory-residue-local"), "-O{opt}: no residue:\n{stderr}");
            assert!(
                !std::path::Path::new(&coverage_path).exists()
                    || !rfs::read_to_string(&coverage_path).contains("inventory-residue-local"),
                "-O{opt}: no residue row"
            );
        }
    }
}

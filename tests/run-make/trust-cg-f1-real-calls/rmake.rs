//! Trust (step 2 increment 5, sub-step 5.4.2; plan
//! `docs/design/2026-10-08-step2-inc5-step4-compiler-lane-plan.md` §2, critique H1): REAL CALLS
//! on F1's compiler lane, `-Ztrust-cg-f1-backend=compiler`.
//!
//! On the default (`lir`) lane F1 has no call: the converter splices a callee's body into its
//! caller or refuses. On the compiler lane one codegen module per crate is compiled by trust-cg's
//! `Compiler::compile`, so an `#[inline(never)]` callee is a real `bl` to its own symbol, and the
//! call-event refinement gate verifies each function's bytes against its producer IR with every
//! call an abstract event. This fixture pins, per subject:
//!
//! * ALLOW-UNKNOWN (at `-Copt-level=0` and `2`): the crate compiles; the object calls each
//!   helper by its symbol (`bl`, or a relocated tail `b`); the certificates file lists the paired
//!   call sites; and the executed output equals the LLVM build's on every input.
//! * STRICT (the default policy): `p03` and `p03b` ship (predicted from step 5.2's measurement of
//!   the same shapes; a failure would be a finding, never a reason to weaken anything); `p45` is
//!   refused naming its loop helper as the blocker; `p33` and `p33b` are refused, their recursive
//!   functions graded below `[PROVED]` (a conditional call site grades `[VALIDATED]`; strict
//!   recursion is step 5.8's exit), and the grade is pinned.
//! * FRAME RECORDS (critique L4, INC5.4-FRAME): every function that contains a `bl` saves a frame
//!   record (`stp x29, x30` and `x29` pointed at the pair: `mov x29, sp`, or `add x29, sp, #k`
//!   when the pair is stored at `[sp, #k]`), the targets' `NonLeaf` frame-pointer policy.
//! * CONTROL: without the flag the default lane's `lower_module_to_lir` note appears and no
//!   certificates file is written; a compile on the default lane removes one an earlier
//!   compiler-lane compile left under the same output stem.
//!
//! The R-8 probe corpus is not in this repository (`docs/audits/2026-09-29-r8-trust-ir-vs-mir.md`):
//! `p03`, `p03b`, `p45`, `p33` and `p33b` here are RECREATIONS of the shapes the plan names (an
//! unconditional wrapper, two ordered calls, a helper with a loop, self recursion with a base case,
//! mutual recursion with a base case), not the originals. `-Coverflow-checks=off`, and no indexing
//! or division, so no body carries a runtime check F1 refuses (`[unfaithful-panic]`).

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::object::read::archive::ArchiveFile;
use run_make_support::{cc, cmd, rfs, run, rust_lib_name, rustc, serde_json};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";

const INPUTS: &[&str] = &["0", "1", "2", "3", "7", "15", "16", "63", "64", "255", "256", "4097"];

#[derive(Clone, Copy)]
enum Strict {
    /// Ships under the default strict policy, every function closed-[PROVED].
    Ships,
    /// Refused by the gate's policy; every needle appears in the refusal.
    Refused(&'static [&'static str]),
}

struct Subject {
    name: &'static str,
    source: &'static str,
    /// The exported entry points (`extern "C" fn(u64) -> u64`).
    exported: &'static [&'static str],
    /// `(caller, callee fragment)`: the caller must call the callee by symbol.
    calls: &'static [(&'static str, &'static str)],
    strict: Strict,
}

const SUBJECTS: &[Subject] = &[
    Subject {
        name: "p03",
        source: r#"#[inline(never)] fn p03_helper_g(x: u64) -> u64 { x ^ 0x5a }
#[unsafe(no_mangle)] pub extern "C" fn p03(x: u64) -> u64 { p03_helper_g(x) + 1 }
"#,
        exported: &["p03"],
        calls: &[("p03", "p03_helper_g")],
        strict: Strict::Ships,
    },
    Subject {
        name: "p03b",
        source: r#"#[inline(never)] fn p03b_first(x: u64) -> u64 { x ^ 3 }
#[inline(never)] fn p03b_second(x: u64) -> u64 { x | 0x100 }
#[unsafe(no_mangle)] pub extern "C" fn p03b(x: u64) -> u64 { p03b_second(p03b_first(x)) + 2 }
"#,
        exported: &["p03b"],
        calls: &[("p03b", "p03b_first"), ("p03b", "p03b_second")],
        strict: Strict::Ships,
    },
    Subject {
        name: "p45",
        source: r#"#[inline(never)] fn p45_sum_to(n: u64) -> u64 {
    let mut s = 0;
    let mut i = 0;
    while i < n {
        s += i;
        i += 1;
    }
    s
}
#[unsafe(no_mangle)] pub extern "C" fn p45(x: u64) -> u64 { p45_sum_to(x & 0xff) ^ 7 }
"#,
        exported: &["p45"],
        calls: &[("p45", "p45_sum_to")],
        strict: Strict::Refused(&["[f1-output-gate:policy]", "blocked by [", "p45_sum_to"]),
    },
    Subject {
        name: "p33",
        source: r#"#[inline(never)] fn p33_fib(n: u64) -> u64 { if n < 2 { n } else { p33_fib(n - 1) + p33_fib(n - 2) } }
#[unsafe(no_mangle)] pub extern "C" fn p33(x: u64) -> u64 { p33_fib(x & 15) }
"#,
        exported: &["p33"],
        calls: &[("p33", "p33_fib"), ("p33_fib", "p33_fib")],
        strict: Strict::Refused(&["[f1-output-gate:policy]", "p33_fib", "[VALIDATED]"]),
    },
    Subject {
        name: "p33b",
        source: r#"#[inline(never)] fn p33b_even(n: u64) -> u64 { if n == 0 { 1 } else { p33b_odd(n - 1) } }
#[inline(never)] fn p33b_odd(n: u64) -> u64 { if n == 0 { 0 } else { p33b_even(n - 1) } }
#[unsafe(no_mangle)] pub extern "C" fn p33b(x: u64) -> u64 { p33b_even(x & 63) }
"#,
        exported: &["p33b"],
        calls: &[("p33b", "p33b_even"), ("p33b_even", "p33b_odd"), ("p33b_odd", "p33b_even")],
        strict: Strict::Refused(&[
            "[f1-output-gate:policy]",
            "p33b_even",
            "p33b_odd",
            "[VALIDATED]",
        ]),
    },
];

/// An rlib of `source` in `out`: F1's compiler lane (`flags` added), or LLVM (the oracle).
fn compile(source: &str, krate: &str, out: &str, f1: bool, opt: &str) -> run_make_support::Rustc {
    rfs::create_dir_all(out);
    let mut cmd = rustc();
    cmd.input(source)
        .crate_name(krate)
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
            .arg("-Ztrust-ir-lower");
    }
    cmd
}

/// The one `.o` member of `rlib`.
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

/// A C driver that runs every function on every input, each call in a forked child.
fn driver(functions: &[&str]) -> String {
    let mut c = String::from(
        "#include <stdint.h>\n#include <stdio.h>\n#include <unistd.h>\n#include <sys/wait.h>\n",
    );
    for f in functions {
        c.push_str(&format!("extern uint64_t {f}(uint64_t);\n"));
    }
    c.push_str("typedef uint64_t (*F)(uint64_t);\n");
    c.push_str(&format!("F fs[] = {{{}}};\n", functions.join(", ")));
    c.push_str(&format!(
        "const char *names[] = {{{}}};\n",
        functions.iter().map(|f| format!("\"{f}\"")).collect::<Vec<_>>().join(", ")
    ));
    c.push_str(&format!(
        "uint64_t xs[] = {{{}}};\n",
        INPUTS.iter().map(|x| format!("{x}ULL")).collect::<Vec<_>>().join(", ")
    ));
    c.push_str(
        "int main(void) {\n\
         for (unsigned j = 0; j < sizeof(fs) / sizeof(fs[0]); j++) {\n\
         printf(\"%s:\", names[j]);\n\
         for (unsigned i = 0; i < sizeof(xs) / sizeof(xs[0]); i++) {\n\
         fflush(stdout);\n\
         pid_t p = fork();\n\
         if (p == 0) { uint64_t r = fs[j](xs[i]); printf(\" %llu\", (unsigned long long)r); fflush(stdout); _exit(0); }\n\
         int st; waitpid(p, &st, 0);\n\
         if (WIFSIGNALED(st)) printf(\" SIG%d\", WTERMSIG(st)); else if (WEXITSTATUS(st)) printf(\" EXIT%d\", WEXITSTATUS(st));\n\
         }\n\
         printf(\"\\n\");\n\
         }\n\
         return 0;\n\
         }\n",
    );
    c
}

fn run_lane(tag: &str, object: &[u8], functions: &[&str]) -> String {
    rfs::write(format!("{tag}.o"), object);
    rfs::write(format!("{tag}.c"), driver(functions));
    cc().input(format!("{tag}.c")).input(format!("{tag}.o")).out_exe(tag).run();
    run(tag).stdout_utf8()
}

/// `objdump -d -r` of `object` (relocations shown under the instruction they patch), split
/// into `(function, body lines)`.
fn disassembly(tag: &str, object: &[u8]) -> Vec<(String, Vec<String>)> {
    let path = format!("{tag}.dis.o");
    rfs::write(&path, object);
    let text = cmd("objdump").arg("-d").arg("-r").arg(&path).run().stdout_utf8();
    let mut functions: Vec<(String, Vec<String>)> = Vec::new();
    for line in text.lines() {
        // `000000000000000c <_p03>:`
        if let Some(rest) = line.strip_suffix(">:")
            && let Some((address, name)) = rest.split_once(" <")
            && address.chars().all(|c| c.is_ascii_hexdigit())
        {
            functions.push((name.to_string(), Vec::new()));
            continue;
        }
        if let Some((_, body)) = functions.last_mut() {
            body.push(line.to_string());
        }
    }
    functions
}

/// The body of the function `fragment` names: an exported `extern "C"` name exactly (Mach-O
/// prefixes `_`), otherwise the one mangled symbol that contains it.
fn function<'a>(dis: &'a [(String, Vec<String>)], fragment: &str) -> &'a [String] {
    let exported = format!("_{fragment}");
    let mut found: Vec<_> = dis.iter().filter(|(name, _)| *name == exported).collect();
    if found.is_empty() {
        found = dis.iter().filter(|(name, _)| name.contains(fragment)).collect();
    }
    assert_eq!(found.len(), 1, "one function named like `{fragment}`: {dis:#?}");
    &found[0].1
}

/// The mnemonic of an instruction line (`      14: 94000000     \tbl\t0x14 <_p03+0x8>`).
fn mnemonic(line: &str) -> Option<&str> {
    line.split('\t').nth(1).map(str::trim)
}

/// Whether `body` stores the frame record (`x29`, `x30`) and points `x29` at it.
fn has_frame_record(body: &[String]) -> bool {
    body.iter().any(|line| {
        let Some(operands) = line.split('\t').nth(2) else { return false };
        if mnemonic(line) != Some("stp") || !operands.starts_with("x29, x30, [sp") {
            return false;
        }
        if operands.ends_with("]!") {
            // Pre-indexed: the pair is at the new `sp`.
            return body.iter().any(|l| l.contains("\tmov\tx29, sp"));
        }
        // `[sp, #k]`: the pair is at `sp + k`.
        let offset = operands.trim_start_matches("x29, x30, [sp").trim_end_matches(']');
        let offset = offset.trim_start_matches(", ");
        if offset.is_empty() {
            return body.iter().any(|l| l.contains("\tmov\tx29, sp"));
        }
        body.iter().any(|l| l.contains(&format!("\tadd\tx29, sp, {offset}")))
    })
}

/// Whether `body` calls `fragment` by symbol: a `bl` (or a tail `b`) whose own text, or the
/// relocation line under it, names the callee.
fn calls(body: &[String], fragment: &str) -> bool {
    body.iter().enumerate().any(|(i, line)| {
        matches!(mnemonic(line), Some("bl" | "b"))
            && (line.contains(fragment)
                || body.get(i + 1).is_some_and(|next| {
                    next.contains("ARM64_RELOC_BRANCH26") && next.contains(fragment)
                }))
    })
}

fn main() {
    let mut strict_ships = Vec::new();
    for subject in SUBJECTS {
        let krate = format!("rc_{}", subject.name);
        let source = format!("{krate}.rs");
        rfs::write(&source, subject.source);
        for opt in ["0", "2"] {
            let tag = format!("{}_o{opt}", subject.name);
            let lib = rust_lib_name(&krate);

            // ---- the oracle -----------------------------------------------------------------
            let llvm_out = format!("out_{tag}_llvm");
            compile(&source, &krate, &llvm_out, false, opt).run();
            let oracle = run_lane(
                &format!("{tag}_llvm"),
                &object_member(&format!("{llvm_out}/{lib}")),
                subject.exported,
            );
            assert!(!oracle.contains("SIG"), "{tag}: the oracle must not trap: {oracle}");

            // ---- allow-unknown: compiles, calls by symbol, runs like LLVM ---------------
            let out = format!("out_{tag}_au");
            let built = compile(&source, &krate, &out, true, opt)
                .arg("-Ztrust-cg-f1-backend=compiler")
                .arg("-Ztrust-cg-output-gate=allow-unknown")
                .run();
            let stderr = built.stderr_utf8();
            assert!(!stderr.contains("internal compiler error"), "{tag}: {stderr}");
            assert!(
                stderr.contains(
                    "reachable function(s) completed source -> trust_ir_of -> codegen_module"
                ),
                "{tag}: the compiler lane compiled the crate:\n{stderr}"
            );
            assert!(!stderr.contains("lower_module_to_lir"), "{tag}: no LIR lane:\n{stderr}");
            assert!(stderr.contains(" 0 refuted"), "{tag}:\n{stderr}");
            let object = object_member(&format!("{out}/{lib}"));
            let dis = disassembly(&format!("{tag}_au"), &object);
            for (caller, callee) in subject.calls {
                assert!(
                    calls(function(&dis, caller), callee),
                    "{tag}: `{caller}` does not call `{callee}` by symbol: {:#?}",
                    function(&dis, caller)
                );
            }
            // INC5.4-FRAME: a function that calls saves a frame record — `x29, x30` stored as a
            // pair and `x29` pointed at it (`mov x29, sp` after a pre-indexed store, `add x29, sp,
            // #k` after a store at `[sp, #k]`).
            for (name, body) in &dis {
                if body.iter().any(|l| mnemonic(l) == Some("bl")) {
                    assert!(
                        has_frame_record(body),
                        "{tag}: `{name}` calls without a frame record (INC5.4-FRAME):\n{}",
                        body.join("\n")
                    );
                }
            }
            // The certificates: one per function, the call sites paired by symbol.
            let certificates =
                rfs::read_to_string(format!("{out}/{krate}.trust-cg-certificates.json"));
            let json: serde_json::Value =
                serde_json::from_str(&certificates).expect("certificates JSON");
            let certs = json["certificates"].as_array().expect("certificates");
            assert_eq!(
                certs.len(),
                dis.len(),
                "{tag}: one certificate per function: {certificates}"
            );
            for (caller, callee) in subject.calls {
                let named = |c: &&serde_json::Value| c["symbol"].as_str() == Some(*caller);
                let cert = certs
                    .iter()
                    .find(named)
                    .or_else(|| {
                        certs
                            .iter()
                            .find(|c| c["symbol"].as_str().is_some_and(|s| s.contains(caller)))
                    })
                    .unwrap_or_else(|| panic!("{tag}: no certificate for `{caller}`"));
                let sites = cert["call_sites"].as_array().expect("call sites");
                assert!(
                    sites.iter().any(|s| s["symbol"].as_str().is_some_and(|s| s.contains(callee))),
                    "{tag}: `{caller}`'s certificate pairs no site with `{callee}`: {cert}"
                );
            }
            let f1 = run_lane(&format!("{tag}_f1"), &object, subject.exported);
            assert_eq!(f1, oracle, "{tag}: the compiler lane and LLVM disagree on executed output");

            // ---- strict, the default policy ---------------------------------------------
            let out = format!("out_{tag}_strict");
            let mut strict = compile(&source, &krate, &out, true, opt);
            strict.arg("-Ztrust-cg-f1-backend=compiler");
            match subject.strict {
                Strict::Ships => {
                    let stderr = strict.run().stderr_utf8();
                    assert!(stderr.contains(" 0 not closed, 0 refuted"), "{tag}:\n{stderr}");
                    let f1 = run_lane(
                        &format!("{tag}_strict"),
                        &object_member(&format!("{out}/{lib}")),
                        subject.exported,
                    );
                    assert_eq!(f1, oracle, "{tag}: strict output differs from LLVM");
                    strict_ships.push(tag);
                }
                Strict::Refused(needles) => {
                    let stderr = strict.run_fail().stderr_utf8();
                    assert!(!stderr.contains("internal compiler error"), "{tag}: {stderr}");
                    for needle in needles {
                        assert!(stderr.contains(needle), "{tag}: missing `{needle}`:\n{stderr}");
                    }
                    assert!(
                        !std::path::Path::new(&out).join(&lib).exists(),
                        "{tag}: a refused crate writes no rlib"
                    );
                }
            }
        }
    }
    assert_eq!(strict_ships, ["p03_o0", "p03_o2", "p03b_o0", "p03b_o2"], "the strict ship set");
    control();
}

/// Without the flag the default lane compiles, says so, writes no certificates, and removes the
/// file an earlier compiler-lane compile left under the same output stem.
fn control() {
    let out = "out_control";
    let source = "rc_p03.rs";
    let certificates = format!("{out}/rc_p03.trust-cg-certificates.json");
    compile(source, "rc_p03", out, true, "2")
        .arg("-Ztrust-cg-f1-backend=compiler")
        .arg("-Ztrust-cg-output-gate=allow-unknown")
        .run();
    assert!(std::path::Path::new(&certificates).exists(), "the compiler lane wrote its file");
    let stderr = compile(source, "rc_p03", out, true, "2")
        .arg("-Ztrust-cg-output-gate=allow-unknown")
        .run()
        .stderr_utf8();
    assert!(
        stderr.contains(
            "reachable function(s) completed source -> trust_ir_of -> lower_module_to_lir"
        ),
        "the default lane:\n{stderr}"
    );
    assert!(!stderr.contains("codegen_module"), "the default lane is not the compiler lane");
    assert!(
        !std::path::Path::new(&certificates).exists(),
        "a default-lane compile must not leave the compiler lane's certificates beside its object"
    );
}

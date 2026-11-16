//! Trust WS7.13 (F-114, scout-f1.8 "bool ABI"): a `bool` PARAMETER reaches the
//! trust-ir (F1) codegen frontend and is VALIDATED by the in-compiler
//! proven-output gate under the caller-owed zero-extension precondition — and
//! nowhere else.
//!
//! PROVENANCE. Before WS7.13 the ABI filter refused every `bool` argument slot
//! (`arg_ext: Zext` is not `None`), and the gate's own `signature_reg_width`
//! refused `Ty::Bool` in parameter position independently, recording that an
//! unconstrained 32-bit model of the incoming register had "fabricated six
//! Refuted verdicts once already". The fix is a PRECONDITION, not a wider
//! model: rustc marks the slot `Zext`, Apple's ARM64 ABI makes the CALLER
//! extend a sub-32-bit argument, so the gate assumes `W{k}[31:1] == 0` on both
//! sides, reads bit 0 as the value, and — because that is a trust assumption on
//! every caller the gate cannot see — caps the verdict at [VALIDATED].
//!
//! Pins:
//!  * SUBJECT, allow-unknown — `fn pick(b: bool, x: u32) -> u32` compiles through
//!    the F1 frontend; the ABI filter's refusal and the gate's PARAMETER-position
//!    refusal are both ABSENT; the certification report says exactly
//!    `1 [VALIDATED] (ay-only)` and `0 uncertified` — the function shipped on
//!    the gate's verdict, not on the policy's tolerance of `Unknown`;
//!  * STRICT (the default gate) — the same crate is REFUSED, and the refusal
//!    names the [VALIDATED] grade cap, not the ABI and not `Unknown`: the
//!    ambient precondition is never laundered into kernel-[PROVED];
//!  * MIR LANE — the same crate on the default frontend is still refused at the
//!    ABI filter (`arg_ext: Zext`): the admission is F1-only, because only the
//!    F1 gate models the precondition;
//!  * THE OBJECT IS REAL — the allow-unknown rlib links into an executable
//!    whose LLVM-compiled caller passes `true` and `false`, and it answers
//!    `7 0`.
//!
//! APPLE-ONLY, and not for hygiene: the caller-side extension promise is a
//! Darwin ABI fact (`caller_small_arg_extension_bits`); on generic AAPCS64 the
//! callee may not assume the caller extended, and the gate stays `Unknown`.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, rustc};

/// Flags every compilation here shares: trust-cg selected explicitly, the full
/// verifier OFF so the configured `-Ztrust-cg-output-gate` is the effective
/// policy (batteries-on strict verification rewrites it to strict), and
/// `panic=abort` because trust-cg refuses `panic=unwind`.
fn base(input: &str, out: &str) -> rustc::Rustc {
    rfs::create_dir(out);
    let mut rustc = rustc();
    rustc
        .input(input)
        .crate_type("lib")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-verify=off")
        .out_dir(out);
    rustc
}

/// The same compilation driven through the trust-ir codegen frontend.
fn trust_ir_frontend(input: &str, out: &str) -> rustc::Rustc {
    let mut rustc = base(input, out);
    rustc.arg("-Ztrust-ir-lower").arg("-Ztrust-cg-frontend=trust-ir");
    rustc
}

const ABI_REFUSAL: &str = "unsupported ABI type/pass mode";
const GATE_PARAM_REFUSAL: &str = "`bool` in PARAMETER position";

fn main() {
    rfs::write(
        "bool_param.rs",
        "#![crate_name = \"bool_param\"]\n\
         pub fn pick(b: bool, x: u32) -> u32 { if b { x } else { 0 } }\n",
    );

    // ── SUBJECT: allow-unknown ships the function VALIDATED ──────────────
    let validated = trust_ir_frontend("bool_param.rs", "out_f1_validated")
        .arg("-Ztrust-cg-output-gate=allow-unknown")
        .run();
    validated.assert_stderr_contains("1/1 reachable function(s) completed");
    validated.assert_stderr_not_contains(ABI_REFUSAL);
    validated.assert_stderr_not_contains(GATE_PARAM_REFUSAL);
    validated.assert_stderr_contains("TRUST-IR certification report");
    // The verdict, not the policy, shipped it: [VALIDATED], never uncertified.
    validated.assert_stderr_contains("1 [VALIDATED] (ay-only)");
    validated.assert_stderr_contains("0 uncertified");
    validated.assert_stderr_contains("0 refuted");
    assert!(
        std::path::Path::new("out_f1_validated").join("libbool_param.rlib").exists(),
        "allow-unknown must ship the rlib the gate validated"
    );

    // ── STRICT: the grade cap is honoured, and it is the ONLY refusal ─────
    let refused = trust_ir_frontend("bool_param.rs", "out_f1_strict").run_fail();
    refused.assert_stderr_contains("REFUSING to emit trust-ir module");
    refused.assert_stderr_contains("function is [VALIDATED] (ay-only authority)");
    refused.assert_stderr_not_contains(ABI_REFUSAL);
    refused.assert_stderr_not_contains(GATE_PARAM_REFUSAL);
    assert!(
        !rfs::read_dir("out_f1_strict").any(|entry| {
            entry.expect("read strict output dir").file_name().to_string_lossy().ends_with(".rlib")
        }),
        "the strict gate let an ay-only [VALIDATED] module reach an rlib"
    );

    // ── MIR LANE: the admission is F1-only ────────────────────────────────
    let mir = base("bool_param.rs", "out_mir").run_fail();
    mir.assert_stderr_contains(ABI_REFUSAL);
    mir.assert_stderr_contains("arg_ext: Zext");
    mir.assert_stderr_contains("`bool`");

    // ── THE OBJECT IS REAL ────────────────────────────────────────────────
    rfs::write(
        "driver.rs",
        "extern crate bool_param;\n\
         fn main() {\n\
             let t = std::hint::black_box(true);\n\
             let f = std::hint::black_box(false);\n\
             println!(\"{} {}\", bool_param::pick(t, 7), bool_param::pick(f, 7));\n\
         }\n",
    );
    let mut link = rustc();
    link.input("driver.rs")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Zunstable-options")
        .arg("-Ztrust-verify=off")
        .extern_("bool_param", "out_f1_validated/libbool_param.rlib")
        .library_search_path("out_f1_validated")
        .output("driver");
    link.run();
    let ran = run_make_support::cmd("./driver").run();
    assert_eq!(
        ran.stdout_utf8().trim(),
        "7 0",
        "the F1-emitted bool-parameter function returned the wrong value when executed"
    );
}

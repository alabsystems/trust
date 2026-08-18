//! Trust (F1 / M-POS): the INTEGER-EXTENSION clause of trust-cg's definition-ABI
//! filter, and the trust-ir codegen frontend, pinned end to end.
//!
//! WHY THIS TEST EXISTS. `scalar_register_abi_ty_supported`
//! (`compiler/rustc_codegen_trust_cg/src/lib.rs`) refuses any argument or return
//! slot whose `ArgAttributes::arg_ext` is not `ArgExtension::None`. That one
//! clause is the sole reason the proven-output gate's NARROW obligation is
//! sound: the gate discharges an 8- or 16-bit return at its DECLARED width and
//! asserts nothing about the register bits above it, which is exactly what a
//! Rust-ABI narrow slot licenses (`arg_ext: None` — the callee owes the caller
//! nothing up there) and exactly what an `extern "C"` slot does NOT
//! (`arg_ext: Zext` — the callee owes a zero-extended value across the whole
//! register). If the clause were deleted, `extern "C"` narrow functions would
//! start reaching a gate that cannot see their extension contract, and the gate
//! would report `Proven` for emissions that violate it. Nothing pinned it.
//!
//! Nothing pinned `-Ztrust-cg-frontend=trust-ir` either — the flag that routes
//! source -> `trust_ir_of` -> `lower_module_to_lir` -> object — so this test
//! also compiles, links and RUNS through it.
//!
//! THE CONTRAST IS THE POINT. `fn(u32) -> u8` and `extern "C" fn(u32) -> u8`
//! have the same types and the same narrowness; only the ABI differs. The first
//! must compile, the second must be refused, and the refusal message must name
//! `arg_ext` — otherwise a future reader cannot tell whether the refusal is
//! about the extension contract or merely about being 8 bits wide.
//!
//! APPLE-ONLY, and not for portability hygiene: `arg_ext` is written for AArch64
//! only under `AbiKind::DarwinPCS` (`rustc_target/src/callconv/aarch64.rs`), so
//! on `aarch64-unknown-linux-gnu` the `extern "C"` case carries
//! `arg_ext: None` and is legitimately ACCEPTED. The refusal asserted here is a
//! Darwin fact.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, rustc};

/// Flags every compilation here shares: trust-cg selected explicitly (LLVM stays
/// the default backend), the full verifier off so the only diagnostics are the
/// backend's, and `panic=abort` because trust-cg refuses `panic=unwind`
/// outright — unwind edges are dropped before codegen and the proven-output gate
/// proves only the normal-return path.
fn base(input: &str, out: &str) -> rustc::Rustc {
    let mut rustc = rustc();
    rustc
        .input(input)
        .crate_type("lib")
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-verify=off")
        .out_dir(out);
    rustc
}

/// The same compilation driven through the trust-ir codegen frontend: the
/// producer (`-Ztrust-ir-lower`) must be on, because that frontend consumes
/// `trust_ir_of` and never falls back to MIR.
fn trust_ir_frontend(input: &str, out: &str) -> rustc::Rustc {
    let mut rustc = base(input, out);
    rustc.arg("-Ztrust-ir-lower").arg("-Ztrust-cg-frontend=trust-ir");
    rustc
}

fn main() {
    // ---------------------------------------------------------------------
    // (1) THE CONTROL. A Rust-ABI narrow return is `arg_ext: None`, so it DOES
    //     reach trust-cg — on both frontends — and the gate proves it. Without
    //     this line the refusals below would be consistent with "trust-cg
    //     refuses all narrow integers", which is not what is being asserted.
    // ---------------------------------------------------------------------
    rfs::write(
        "rust_abi_narrow.rs",
        "#![crate_name = \"rust_abi_narrow\"]\n\
         pub fn masked(x: u32) -> u8 { (x & 0xff) as u8 }\n",
    );

    let mir = base("rust_abi_narrow.rs", "out_mir_ok").run();
    mir.assert_stderr_contains("[PROVED]");

    let f1 = trust_ir_frontend("rust_abi_narrow.rs", "out_f1_ok").run();
    // The frontend actually ran (not silently the MIR path), every reachable
    // body went through `trust_ir_of`, and the gate certified the emission.
    f1.assert_stderr_contains("trust-cg trust-ir frontend: 1/1 reachable function(s) completed");
    f1.assert_stderr_contains("TRUST-IR certification report");
    f1.assert_stderr_contains("1 [PROVED]");
    f1.assert_stderr_contains("0 refuted");

    // ---------------------------------------------------------------------
    // (2) `extern "C" fn(u32) -> u8` — the SAME narrow return, refused, and the
    //     message must name `arg_ext` so the reason is auditable.
    // ---------------------------------------------------------------------
    rfs::write(
        "c_abi_narrow.rs",
        "#![crate_name = \"c_abi_narrow\"]\n\
         #[unsafe(no_mangle)]\n\
         pub extern \"C\" fn masked(x: u32) -> u8 { (x & 0xff) as u8 }\n",
    );

    for (label, out) in [("mir", "out_mir_c"), ("f1", "out_f1_c")] {
        let failed = if label == "mir" {
            base("c_abi_narrow.rs", out).run_fail()
        } else {
            trust_ir_frontend("c_abi_narrow.rs", out).run_fail()
        };
        failed.assert_stderr_contains("unsupported ABI type/pass mode");
        failed.assert_stderr_contains("arg_ext: Zext");
        // Naming the type keeps the message attached to the slot it refused.
        failed.assert_stderr_contains("`u8`");
    }

    // ---------------------------------------------------------------------
    // (3) `-> bool` — refused on BOTH frontends, on the RUST ABI. rustc marks
    //     every bool slot `arg_ext: Zext` in `arg_attrs_for_rust_scalar`
    //     ("Booleans are always a noundef i1 that needs to be zero-extended"),
    //     which is why this needs no `extern "C"` to be refused. The gate's own
    //     `signature_reg_width` refuses a bool PARAMETER independently; this
    //     pins that the compiler never even offers it one.
    // ---------------------------------------------------------------------
    rfs::write(
        "bool_sig.rs",
        "#![crate_name = \"bool_sig\"]\n\
         pub fn is_set(x: u32) -> bool { x & 8 == 8 }\n",
    );

    for (label, out) in [("mir", "out_mir_bool"), ("f1", "out_f1_bool")] {
        let failed = if label == "mir" {
            base("bool_sig.rs", out).run_fail()
        } else {
            trust_ir_frontend("bool_sig.rs", out).run_fail()
        };
        failed.assert_stderr_contains("unsupported ABI type/pass mode");
        failed.assert_stderr_contains("arg_ext: Zext");
        failed.assert_stderr_contains("`bool`");
    }

    // ---------------------------------------------------------------------
    // (4) THE STRICT GATE HAS TEETH AT THE COMPILER LEVEL. A body the gate
    //     cannot decide must not reach the linker under the default strict
    //     policy — "emitted anyway with a note" would make every [PROVED] count
    //     above meaningless. `x + 1` lowers to a checked-overflow instruction
    //     that is outside the gate's modeled fragment.
    // ---------------------------------------------------------------------
    rfs::write(
        "undecidable.rs",
        "#![crate_name = \"undecidable\"]\n\
         pub fn bump(x: u32) -> u32 { x + 1 }\n",
    );
    rfs::create_dir("out_f1_strict");
    let refused = trust_ir_frontend("undecidable.rs", "out_f1_strict").run_fail();
    refused.assert_stderr_contains("REFUSING to emit trust-ir module");
    refused.assert_stderr_contains("could not be proven output-preserving");
    assert!(
        !rfs::read_dir("out_f1_strict").any(|entry| {
            entry
                .expect("read strict-policy output dir")
                .file_name()
                .to_string_lossy()
                .ends_with(".rlib")
        }),
        "the strict gate let an undecided module reach an rlib"
    );

    // ---------------------------------------------------------------------
    // (5) THE OBJECT IS REAL. An F1-compiled library links into an executable
    //     and RUNS with the right answer. A gate verdict about bytes nobody
    //     executes proves the gate agrees with itself and nothing else.
    // ---------------------------------------------------------------------
    rfs::write(
        "driver.rs",
        "extern crate rust_abi_narrow;\n\
         fn main() { println!(\"{}\", rust_abi_narrow::masked(0x1234)); }\n",
    );
    let mut link = rustc();
    link.input("driver.rs")
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Zunstable-options")
        .arg("-Ztrust-verify=off")
        .extern_("rust_abi_narrow", "out_f1_ok/librust_abi_narrow.rlib")
        .library_search_path("out_f1_ok")
        .output("driver");
    link.run();

    let ran = run_make_support::cmd("./driver").run();
    // 0x1234 & 0xff == 0x34 == 52.
    assert_eq!(
        ran.stdout_utf8().trim(),
        "52",
        "the F1-emitted narrow function returned the wrong value when actually executed"
    );
}

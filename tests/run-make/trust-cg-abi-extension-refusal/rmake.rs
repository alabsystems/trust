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
    //     which is why this needs no `extern "C"` to be refused. (A bool
    //     PARAMETER is a separate story: since WS7.13 the F1 lane admits it and
    //     the gate models it under an attested caller-owed precondition, capped
    //     at [VALIDATED] — pinned by `trust-cg-f1-bool-param-validated`.)
    // ---------------------------------------------------------------------
    rfs::write(
        "bool_sig.rs",
        "#![crate_name = \"bool_sig\"]\n\
         pub fn is_set(x: u32) -> bool { x & 8 == 8 }\n",
    );

    // MIR lane: the Zext `bool` return is still refused at the ABI gate — that
    // path carries no bool-return model.
    let mir_bool = base("bool_sig.rs", "out_mir_bool").run_fail();
    mir_bool.assert_stderr_contains("unsupported ABI type/pass mode");
    mir_bool.assert_stderr_contains("arg_ext: Zext");
    mir_bool.assert_stderr_contains("`bool`");

    // trust-ir (F1) lane: the Zext `bool` RETURN is ADMITTED at the ABI gate and
    // discharged per function by the gate's 32-bit byte-proof
    // (`zext_bool_return_abi_supported`, commit f3e8779213). The ABI validator runs
    // DURING lowering, so "1/1 reachable function(s) completed" is the witness that
    // the bool return passed it.
    //
    // RE-PINNED 2026-09-15 (ay advanced 075a482ae -> cb310b9b21, 51 commits). This
    // lane used to STOP here: the body reached the proven-output gate only as
    // [VALIDATED] (ay-only) and was refused. ay's new shared-prefix unsigned
    // comparison lowering (`BvExpr::Ult`) makes `x & 8 == 8` kernel-re-checkable, so
    // the same body now reports 1 [PROVED] and the module COMPILES. That is a
    // strictly stronger verdict — a kernel-re-checkable proof where there was a
    // solver-only validation — so the test follows it rather than pinning the weaker
    // state. The refusal ARM of this file is not weakened: `masked` on the same lane
    // still fails at the ABI gate below, and section (4) still proves the strict gate
    // refuses an undecidable body.
    let f1_bool = trust_ir_frontend("bool_sig.rs", "out_f1_bool").run();
    f1_bool.assert_stderr_contains("1/1 reachable function(s) completed");
    f1_bool.assert_stderr_not_contains("unsupported ABI type/pass mode");
    f1_bool.assert_stderr_not_contains("could not be proven output-preserving");
    f1_bool.assert_stderr_contains("1 [PROVED] (kernel-re-checkable)");
    f1_bool.assert_stderr_contains("0 [VALIDATED] (ay-only)");

    // ---------------------------------------------------------------------
    // (4) THE STRICT GATE HAS TEETH AT THE COMPILER LEVEL. A body the gate
    //     cannot decide must not reach the linker under the default strict
    //     policy — "emitted anyway with a note" would make every [PROVED] count
    //     above meaningless. A read of a promoted `&'static u64` lowers to
    //     `GlobalAddr` + `Load`, which is outside the gate's modeled fragment.
    //
    //     RE-PINNED 2026-09-29 (R-8 ledger item 1, plan §5): this row used
    //     `x + 1`, whose checked-overflow `Assert` the gate could not decide.
    //     That body now never reaches the gate: F1 lowers a failed `Assert` to a
    //     bare trap, so the frontend refuses it `[unfaithful-panic]` under every
    //     gate policy — pinned as (4b). The gate's own teeth move to a body with
    //     no runtime check. main's 9eb52da524 re-pinned this row independently to a
    //     loop under `-Coverflow-checks=off`; it is the same leg (an `Assert`-free body
    //     outside the gate's modeled fragment, refused by the gate), so one subject
    //     carries it here, and main's other claim — with the checks off `x + 1` has no
    //     `Assert` and the gate PROVES it — is the control row in (4b).
    // ---------------------------------------------------------------------
    rfs::write(
        "undecidable.rs",
        "#![crate_name = \"undecidable\"]\n\
         #[inline(never)]\n\
         pub fn read_promoted() -> u64 {\n\
             let value: &'static u64 = &0x1122_3344_5566_7788_u64;\n\
             *value | *value\n\
         }\n",
    );
    rfs::create_dir("out_f1_strict");
    let refused = trust_ir_frontend("undecidable.rs", "out_f1_strict").run_fail();
    refused.assert_stderr_contains("1/1 reachable function(s) completed");
    refused.assert_stderr_contains("REFUSING to emit trust-ir module");
    refused.assert_stderr_contains("could not be proven output-preserving");
    refused.assert_stderr_not_contains("[unfaithful-panic]");
    // Trust (2026-09-30): nor the bridge converter's by-name `Assert` refusal.
    refused.assert_stderr_not_contains("[implicit-panic-unfaithful]");
    let no_rlib = |dir: &str| {
        !rfs::read_dir(dir).any(|entry| {
            entry.expect("read output dir").file_name().to_string_lossy().ends_with(".rlib")
        })
    };
    assert!(no_rlib("out_f1_strict"), "the strict gate let an undecided module reach an rlib");

    // (4b) `x + 1`: refused by the FRONTEND, before the gate, under the strict, the
    //      allow-unknown AND the off policy — a trap standing in for Rust's panic never
    //      ships, not even with no gate behind the frontend.
    rfs::write(
        "checked.rs",
        "#![crate_name = \"checked\"]\n\
         pub fn bump(x: u32) -> u32 { x + 1 }\n",
    );
    for policy in ["strict", "allow-unknown", "off"] {
        let out = format!("out_f1_checked_{policy}");
        rfs::create_dir(&out);
        let refused = trust_ir_frontend("checked.rs", &out)
            .arg(format!("-Ztrust-cg-output-gate={policy}"))
            .run_fail();
        refused.assert_stderr_contains("[unfaithful-panic]");
        refused.assert_stderr_contains("reaches a runtime check (`Assert` NoOverflow)");
        refused.assert_stderr_not_contains("REFUSING to emit trust-ir module");
        assert!(no_rlib(&out), "{policy}: a function that can reach a trap reached an rlib");
    }
    //      The control: the refusal is about the CHECK. Under `-Ztrust-verify=off`,
    //      `-Coverflow-checks=off` removes it, and the same body ships PROVED under the
    //      default strict policy.
    rfs::create_dir("out_f1_unchecked");
    let shipped = trust_ir_frontend("checked.rs", "out_f1_unchecked")
        .arg("-Coverflow-checks=off")
        .run();
    shipped.assert_stderr_contains("1/1 reachable function(s) completed");
    shipped.assert_stderr_contains("1 [PROVED] (kernel-re-checkable)");
    shipped.assert_stderr_not_contains("[unfaithful-panic]");
    assert!(!no_rlib("out_f1_unchecked"), "the check-free `x + 1` ships under strict");

    // (4c) The strict gate's OTHER leg: a check-free body the gate decides only as
    //      [VALIDATED] (ay-only authority) is refused under the default strict policy, and
    //      ships under allow-unknown with that grade reported. `x + 1` used to reach this leg
    //      (on the baseline its refusal was this one, not the outside-fragment one); now that
    //      [unfaithful-panic] refuses it first, a comparison-and-bitwise body carries the pin.
    rfs::write(
        "validated.rs",
        "#![crate_name = \"validated\"]\n\
         pub fn f(x: u32, y: u32) -> u32 { if x > y { x ^ y } else { x | y } }\n",
    );
    rfs::create_dir("out_f1_validated_strict");
    let refused = trust_ir_frontend("validated.rs", "out_f1_validated_strict").run_fail();
    refused.assert_stderr_contains("1/1 reachable function(s) completed");
    refused.assert_stderr_contains("REFUSING to emit trust-ir module");
    refused.assert_stderr_contains("[VALIDATED] (ay-only authority)");
    refused.assert_stderr_not_contains("[unfaithful-panic]");
    assert!(no_rlib("out_f1_validated_strict"), "a [VALIDATED] body shipped under strict");
    rfs::create_dir("out_f1_validated_au");
    let shipped = trust_ir_frontend("validated.rs", "out_f1_validated_au")
        .arg("-Ztrust-cg-output-gate=allow-unknown")
        .run();
    shipped.assert_stderr_contains("1 [VALIDATED]");
    shipped.assert_stderr_contains("0 refuted");
    assert!(!no_rlib("out_f1_validated_au"), "allow-unknown ships the [VALIDATED] body");
    //      Trust (step 2 increment 5, sub-step 5.4.2; plan critique M3): the same leg on F1's
    //      COMPILER LANE (`-Ztrust-cg-f1-backend=compiler`), where the call-event gate grades the
    //      object and `CerReport::ships` decides. MEASURED first, per the plan: the subject grades [VALIDATED] (ay-only) there too, so the leg keeps it: strict refuses the object by `CerReport::ships` policy and allow-unknown ships it, named.
    rfs::create_dir("out_cl_validated_strict");
    let refused = trust_ir_frontend("validated.rs", "out_cl_validated_strict")
        .arg("-Ztrust-cg-f1-backend=compiler")
        .run_fail();
    refused.assert_stderr_contains("1/1 reachable function(s) completed");
    refused.assert_stderr_contains("[f1-output-gate:policy]");
    refused.assert_stderr_contains("[VALIDATED]");
    refused.assert_stderr_not_contains("[unfaithful-panic]");
    assert!(no_rlib("out_cl_validated_strict"), "a [VALIDATED] body shipped under strict");
    rfs::create_dir("out_cl_validated_au");
    let shipped = trust_ir_frontend("validated.rs", "out_cl_validated_au")
        .arg("-Ztrust-cg-f1-backend=compiler")
        .arg("-Ztrust-cg-output-gate=allow-unknown")
        .run();
    shipped.assert_stderr_contains("0 closed-[PROVED], 1 not closed, 0 refuted");
    shipped.assert_stderr_contains("[VALIDATED]");
    assert!(!no_rlib("out_cl_validated_au"), "allow-unknown ships the [VALIDATED] body");

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

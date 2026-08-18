//! Trust (F1 / M-POS): the `char`, FIELDLESS-ENUM and LIFETIME-ONLY-GENERIC
//! admissions, pinned on BOTH frontends — including the default one.
//!
//! WHY THIS TEST EXISTS. `scalar_register_abi_ty_supported`
//! (`compiler/rustc_codegen_trust_cg/src/lib.rs`) is SHARED: the trust-ir
//! frontend consults it, and so does the MIR path (`lib.rs`, the
//! `definition_abi_supported` call). Widening it therefore widens admission on
//! the DEFAULT SHIPPING PATH, not only under `-Ztrust-cg-frontend=trust-ir`.
//! The crate sweeps behind these arms were run with that flag ON, so the MIR
//! path was never swept. Everything below is asserted on BOTH paths for exactly
//! that reason, and the MEASURED asymmetry is recorded rather than assumed:
//!
//! * `char` reaches the emitter and ships `[PROVED]` on BOTH paths. This is a
//!   real widening of the default backend's surface.
//! * a FIELDLESS enum ships `[PROVED]` on the trust-ir frontend and is REFUSED
//!   AT THE ABI FILTER on the MIR path, because the enum arm is gated on
//!   `EnumAbi::Admit` and only the trust-ir frontend supplies it. The MIR path
//!   has no access to the producer's declared enum layout, so admitting an enum
//!   there would put three disagreeing carrier widths in play; the gate is what
//!   keeps the widening confined to the frontend that models the shape.
//!
//! THE SAFETY BOUNDARY. A two-variant fieldless enum whose tags are 0 and 1 is
//! `Scalar::is_bool()` to rustc, which marks it `arg_ext: Zext` — an extension
//! promise this backend does not carry into LIR, exactly like `bool`. It must
//! stay REFUSED, and the refusal must NAME `arg_ext: Zext`, so that a future
//! widening past the extension contract fails here rather than being mistaken
//! for "enums are not supported yet".
//!
//! THE GENERIC CLAUSE. `trust_ir_of` lowers a body PRE-monomorphization, so an
//! instance carrying type or const arguments is refused. A REGION argument
//! substitutes nothing that exists at runtime — codegen erases regions, and
//! rustc mangles one symbol for the whole family — so a lifetime-only instance
//! is that body's only IR and is admitted. One type argument and the refusal is
//! back.
//!
//! APPLE-ONLY / AARCH64-ONLY for the same reason as
//! `trust-cg-abi-extension-refusal`: `arg_ext` is written for AArch64 only under
//! `AbiKind::DarwinPCS`, and trust-cg's native emitter is the AArch64 one.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, rustc};

/// Flags every compilation here shares: trust-cg selected explicitly, the full
/// verifier off so the only diagnostics are the backend's, and `panic=abort`
/// because trust-cg refuses `panic=unwind`.
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

/// The same compilation driven through the trust-ir codegen frontend.
fn trust_ir_frontend(input: &str, out: &str) -> rustc::Rustc {
    let mut rustc = base(input, out);
    rustc.arg("-Ztrust-ir-lower").arg("-Ztrust-cg-frontend=trust-ir");
    rustc
}

fn main() {
    // ---------------------------------------------------------------------
    // (1) `char` IS ADMITTED, AND ON THE DEFAULT PATH TOO.
    //
    //     `char` is one 32-bit unsigned register with `arg_ext: None`, in both
    //     argument and return position. The default (MIR) compilation carries
    //     no `-Ztrust-cg-frontend` at all, so this line is the one that pins the
    //     shipping-path widening.
    // ---------------------------------------------------------------------
    rfs::write(
        "charm.rs",
        "#![crate_name = \"charm\"]\n\
         pub fn cval(c: char) -> u32 { c as u32 }\n\
         pub fn cid(c: char) -> char { c }\n",
    );

    let mir = base("charm.rs", "out_char_mir").run();
    mir.assert_stderr_contains("2 [PROVED]");
    mir.assert_stderr_contains("0 refuted");

    let f1 = trust_ir_frontend("charm.rs", "out_char_f1").run();
    f1.assert_stderr_contains("trust-cg trust-ir frontend: 2/2 reachable function(s) completed");
    f1.assert_stderr_contains("2 [PROVED]");
    f1.assert_stderr_contains("0 refuted");

    // ---------------------------------------------------------------------
    // (2) A FIELDLESS ENUM WITH THREE VARIANTS IS ADMITTED on the trust-ir
    //     frontend — both as a PARAMETER (`three_id`) and as a RETURNED
    //     CONSTANT (`three_z`, whose value is a declared discriminant).
    // ---------------------------------------------------------------------
    rfs::write(
        "three.rs",
        "#![crate_name = \"three\"]\n\
         #[derive(Clone, Copy)]\n\
         pub enum Three { X, Y, Z }\n\
         pub fn three_id(t: Three) -> Three { t }\n\
         pub fn three_z() -> Three { Three::Z }\n",
    );

    let f1 = trust_ir_frontend("three.rs", "out_three_f1").run();
    f1.assert_stderr_contains("trust-cg trust-ir frontend: 2/2 reachable function(s) completed");
    f1.assert_stderr_contains("2 [PROVED]");
    f1.assert_stderr_contains("0 refuted");

    // ... and on the MIR path it is refused AT THE ABI FILTER, by construction:
    // the enum arm is gated on `EnumAbi::Admit`, which only the trust-ir
    // frontend supplies. This is the direct pin. The MIR path derives a
    // fieldless enum's carrier width in three places and reads NONE of them
    // from the producer's `EnumLayoutDescriptor` — `ty_convert::lower_enum_adt`
    // hardcodes a 64-bit signed `__tag`, `mapping::map_type` discards
    // `enum_layout`, and `verify_output::reg_width` has no ADT arm and falls
    // through to 32 — so for `Three` the live widths would be rustc 8 / LIR 64 /
    // gate 32. A separate barrier in `trust_mir_extract` ("layout-erased ADT")
    // also stops it today, but that barrier belongs to another crate and is
    // maintained for layout fidelity, not for this; depending on it would make
    // the widening unreachable rather than sound. If this assertion ever flips
    // to `layout-erased ADT`, the `EnumAbi` gate has been lost and the default
    // path is one distant invariant away from three disagreeing widths.
    let mir = base("three.rs", "out_three_mir").run_fail();
    mir.assert_stderr_contains("unsupported ABI type/pass mode");
    mir.assert_stderr_contains("Three");

    // ---------------------------------------------------------------------
    // (3) THE SAFETY BOUNDARY. `enum Two { A, B }` has tags 0 and 1, which
    //     rustc classifies `Scalar::is_bool()` and marks `arg_ext: Zext`. It
    //     stays REFUSED on BOTH frontends, and the refusal names `arg_ext:
    //     Zext` — so widening past the extension contract fails HERE.
    // ---------------------------------------------------------------------
    rfs::write(
        "two.rs",
        "#![crate_name = \"two\"]\n\
         #[derive(Clone, Copy)]\n\
         pub enum Two { A, B }\n\
         pub fn two_id(t: Two) -> Two { t }\n",
    );

    for (label, out) in [("mir", "out_two_mir"), ("f1", "out_two_f1")] {
        let failed = if label == "mir" {
            base("two.rs", out).run_fail()
        } else {
            trust_ir_frontend("two.rs", out).run_fail()
        };
        failed.assert_stderr_contains("unsupported ABI type/pass mode");
        failed.assert_stderr_contains("arg_ext: Zext");
        failed.assert_stderr_contains("`Two`");
    }

    // The CONTRAST is what makes (3) a statement about the 0/1 tag rather than
    // about enums: `Three` and `Two` differ only in variant count, and only
    // `Two` carries the extension promise.

    // ---------------------------------------------------------------------
    // (4) A LIFETIME-ONLY INSTANTIATION IS NOT A MONOMORPHIZATION.
    //
    //     THE SHAPE MATTERS, and picking it wrong is the easy way to write a
    //     test that proves nothing. A free `fn pick<'a>(_x: &'a u32)` reaches
    //     codegen with `args = []` — a LATE-bound lifetime is not an `Instance`
    //     argument at all — so it is admitted with or without this clause and
    //     witnesses nothing. MEASURED, not reasoned: at HEAD it compiles to
    //     `1 [PROVED]`.
    //
    //     An EARLY-bound lifetime does arrive as an argument: an inherent
    //     method on `S<'a>` reaches codegen as `args = ['{erased}]`, which is
    //     precisely what HEAD refused ("instance carries generic arguments
    //     `['{erased}]`") and what this clause admits.
    // ---------------------------------------------------------------------
    rfs::write(
        "lt.rs",
        "#![crate_name = \"lt\"]\n\
         pub struct S<'a>(pub &'a u32);\n\
         impl<'a> S<'a> {\n\
         \x20   pub fn tag(&self) -> u32 { 7 }\n\
         }\n",
    );

    let f1 = trust_ir_frontend("lt.rs", "out_lt_f1").run();
    f1.assert_stderr_contains("trust-cg trust-ir frontend: 1/1 reachable function(s) completed");
    f1.assert_stderr_contains("1 [PROVED]");
    f1.assert_stderr_contains("0 refuted");

    // ... while ONE TYPE ARGUMENT, on the SAME shape, is a real
    // monomorphization again and stays refused for the pre-monomorphization
    // reason and nothing vaguer. `S<'a>` and `G<T>` differ only in what the
    // parameter is, so this contrast isolates region-vs-type.
    rfs::write(
        "gt.rs",
        "#![crate_name = \"gt\"]\n\
         pub struct G<T>(pub T);\n\
         impl<T> G<T> {\n\
         \x20   pub fn tag(&self) -> u32 { 7 }\n\
         }\n\
         pub fn force(g: &G<u32>) -> u32 { g.tag() }\n",
    );

    let refused = trust_ir_frontend("gt.rs", "out_gt_f1").run_fail();
    refused.assert_stderr_contains("instance carries generic arguments `[u32]`");
    refused.assert_stderr_contains("lowers the body pre-monomorphization");

    // ---------------------------------------------------------------------
    // (5) THE OBJECTS ARE REAL. A gate verdict about bytes nobody executes
    //     proves the gate agrees with itself and nothing else. Link the
    //     F1-emitted char library and the F1-emitted enum library into one
    //     executable and RUN it.
    // ---------------------------------------------------------------------
    rfs::write(
        "driver.rs",
        "extern crate charm;\n\
         extern crate three;\n\
         fn main() {\n\
         \x20   println!(\"{}\", charm::cval('A'));\n\
         \x20   println!(\"{}\", charm::cid('\\u{1f600}') as u32);\n\
         \x20   println!(\"{}\", three::three_z() as u32);\n\
         \x20   println!(\"{}\", three::three_id(three::Three::Y) as u32);\n\
         }\n",
    );
    let mut link = rustc();
    link.input("driver.rs")
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Zunstable-options")
        .arg("-Ztrust-verify=off")
        .extern_("charm", "out_char_f1/libcharm.rlib")
        .extern_("three", "out_three_f1/libthree.rlib")
        .library_search_path("out_char_f1")
        .library_search_path("out_three_f1")
        .output("driver");
    link.run();

    let ran = run_make_support::cmd("./driver").run();
    assert_eq!(
        ran.stdout_utf8().lines().collect::<Vec<_>>(),
        // 'A' == 65; U+1F600 == 128512; Three::Z == 2; Three::Y == 1.
        vec!["65", "128512", "2", "1"],
        "the F1-emitted char/enum functions returned the wrong values when actually executed"
    );
}

//! F1-FIELD-POINTER-AGREEMENT-1: a field pointer into a promoted struct local, through the
//! whole F1 lane (`-Ztrust-cg-frontend=trust-ir`, the default `lir` backend).
//!
//! The F1 producer spells `&mut s.f` / `&s.f` on a promoted struct local as
//! `%c = const i64 <offset>; %p = gep i8 %slot, %c`, then a scalar Load/Store through `%p`.
//! Until this change the converter refused every such GEP ("aggregate slot N is used by `GEP`
//! ..."). It now admits one exactly when the constant starts one field of the slot's layout
//! (the interpreter's own, CG-DECLARED-LAYOUT-1) and every use is a Load/Store at that field's
//! type. `fields.rs`'s `M` is declared `tag, wide, half` and laid out `wide @ 0, half @ 4,
//! tag @ 6`, so a declaration-order offset would name another field.
//!
//!  1. STRICT (the default gate): all three functions convert, and the in-compiler
//!     proven-output gate, which models no memory yet, refuses them as Unknown, fail-closed,
//!     never as a refutation. A RATCHET: when that gate models slot memory this compile
//!     succeeds and the leg fails; replace it then with the grade the gate reports and link
//!     that object below, never by loosening the expected refusal.
//!  2. EMITTED: the same compile under `-Ztrust-cg-output-gate=allow-unknown` emits all three
//!     with `0 refuted`.
//!  3. ORACLE: the same source on the LLVM lane.
//!  4. Both objects are linked against the same C `main`, and each output must equal the
//!     values this recipe computes itself (a shared wrong answer is not accepted).

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{cc, extra_c_flags, rfs, run, rustc};

/// `main.c`'s vectors, in its order.
const INTS: [i32; 9] = [0, 1, -1, 7, 9, i32::MIN, i32::MAX, 0x1234_5678, -0x0f0f_0f0f];
const TAGS: [u32; 6] = [0, 1, 0x7f, 0x80, 0xff, 0x1ff];
const WIDES: [u32; 5] = [0, 1, 0xdead_beef, 0xffff_ffff, 0x8000_0000];
const HALVES: [u32; 6] = [0, 1, 0x7fff, 0x8000, 0xffff, 0x1_ffff];

/// The source semantics (overflow checks off), computed here rather than read from a binary.
fn expected() -> String {
    let mut out = String::new();
    for x in INTS {
        for y in INTS {
            let d = x.wrapping_sub(y);
            out.push_str(&format!("fill {x} {y} {d}\nread {x} {y} {d}\n"));
        }
    }
    for t in TAGS {
        for v in WIDES {
            for h in HALVES {
                let tag = u32::from(t as u8);
                let r = v.wrapping_sub(u32::from(h as u16)).wrapping_sub(tag).wrapping_sub(tag);
                out.push_str(&format!("mixed {t} {v} {h} {r}\n"));
            }
        }
    }
    out
}

fn f1(out: &str, gate: Option<&str>) -> run_make_support::Rustc {
    rfs::create_dir(out);
    let mut cmd = rustc();
    cmd.input("fields.rs")
        .crate_type("lib")
        .edition("2024")
        .emit("obj")
        .codegen_units(1)
        .arg("-Cpanic=abort")
        .arg("-Coverflow-checks=off")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        // The subject is the converter and the codegen gate, not the source verifier.
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-cg-frontend=trust-ir")
        .out_dir(out);
    if let Some(gate) = gate {
        cmd.arg(format!("-Ztrust-cg-output-gate={gate}"));
    }
    cmd
}

fn assert_converted_never_refuted(stderr: &str) {
    assert!(
        stderr.contains("trust-cg trust-ir frontend: 3/3 reachable function(s) completed"),
        "every field-pointer function must convert:\n{stderr}"
    );
    for forbidden in [
        "is used by `GEP`",
        "field pointer",
        "MISCOMPILE",
        "(Refuted",
        "internal compiler error",
        "panicked at",
    ] {
        assert!(!stderr.contains(forbidden), "`{forbidden}` in:\n{stderr}");
    }
}

fn link_and_run(obj: &str, exe: &str) -> String {
    cc().input("main.c").input(obj).out_exe(exe).args(extra_c_flags()).run();
    run(exe).stdout_utf8()
}

fn main() {
    // (1) STRICT: converted, then refused by the output gate as Unknown, never refuted.
    let strict = f1("out_strict", None).run_fail().stderr_utf8();
    assert_converted_never_refuted(&strict);
    assert!(
        strict.contains("could not be proven output-preserving (Unknown, fail-closed"),
        "the strict refusal must be the gate's Unknown:\n{strict}"
    );
    assert!(!std::path::Path::new("out_strict/fields.o").exists(), "strict wrote no object");

    // (2) EMITTED under allow-unknown.
    let emitted = f1("out_f1", Some("allow-unknown")).run().stderr_utf8();
    assert_converted_never_refuted(&emitted);
    assert!(emitted.contains("0 refuted (never emitted)"), "{emitted}");

    // (3) ORACLE: the LLVM lane, verification off.
    rfs::create_dir("out_llvm");
    rustc()
        .input("fields.rs")
        .crate_type("lib")
        .edition("2024")
        .emit("obj")
        .codegen_units(1)
        .arg("-Cpanic=abort")
        .arg("-Coverflow-checks=off")
        .arg("-Ztrust-verify=off")
        .out_dir("out_llvm")
        .run();

    // (4) the same C main over both objects, against computed truth.
    let want = expected();
    assert_eq!(
        want.lines().count(),
        2 * INTS.len() * INTS.len() + TAGS.len() * WIDES.len() * HALVES.len()
    );
    assert_eq!(link_and_run("out_f1/fields.o", "f1_main"), want, "the F1 object");
    assert_eq!(link_and_run("out_llvm/fields.o", "llvm_main"), want, "the LLVM object");
}

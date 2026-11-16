//! WS7.11 (F-114): the CondBr-diamond refutation class, pinned NATIVELY.
//!
//! WHY THIS TEST EXISTS. The F1 scout probe `sel` —
//! `extern "C" fn sel(a: u64, b: u64) -> u64 { if a == b { a ^ 1 } else { b } }`,
//! an `Eq` diamond whose then-arm COMPUTES before the merge — was REFUSED by
//! the in-compiler proven-output gate on stale stage1 `06ce3dd35` (2026-08-30):
//! "function `sel` is a MISCOMPILE (Refuted)". The probe lived in a session
//! scratchpad, so nothing pinned the shape; a later stage1 (`5b45b83b8a`)
//! reported it `[VALIDATED]` and still refused it under the strict gate. The
//! crate-level fixture (`crates/trust-cg-bridge/tests/trust_ir_gate_diamond_shapes.rs`)
//! pins the GATE's verdict on the IR; this recipe pins the whole lane:
//!
//!  1. STRICT — `sel.rs` through the trust-ir codegen frontend under the
//!     DEFAULT output gate (no `-Ztrust-cg-output-gate` flag: strict, only a
//!     kernel-re-checkable `[PROVED]` function ships). MEASURED 2026-09-19 on
//!     `4020807a91`: the gate's verdict is `Proven`, but at the `[VALIDATED]`
//!     (ay-only) grade — the kernel re-check covers no integer comparison yet
//!     (`(a == b) as u64` alone is `[VALIDATED]` too; `a ^ 1` alone is
//!     `[PROVED]`) — so strict REFUSES it, fail-closed, and writes no object.
//!     This leg pins exactly that: the named `[VALIDATED]` refusal, and never
//!     the `MISCOMPILE (Refuted)` of 2026-08-30. It is a RATCHET: when the
//!     kernel frontier covers the compare, this compile SUCCEEDS and the leg
//!     fails — replace it then with the `[PROVED]` assertions and link THAT
//!     object below, never by loosening the expected refusal.
//!  2. EMITTED — the same compile under `-Ztrust-cg-output-gate=allow-unknown`,
//!     whose report must still say `1 [VALIDATED]` and `0 refuted`: the gate
//!     proved the bytes (ay-only); only the evidence grade keeps them off the
//!     strict lane.
//!  3. ORACLE — the SAME source compiled on the LLVM lane (the default backend,
//!     verification off: an oracle must be vanilla).
//!  4. Both objects are linked against the SAME C `main`, run over the boundary
//!     vectors (`a == b`, `a == b == u64::MAX`, `a != b`, and the bit-0 /
//!     above-32-bit near misses), and each output must equal the values this
//!     recipe computes itself. Comparing only the two binaries would accept a
//!     shared wrong answer.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{cc, extra_c_flags, rfs, run, rustc};

/// The vectors `main.c` drives, in its order. Kept in step by the line-count
/// assertion below: a vector added to one side only fails the comparison.
const VECTORS: [(u64, u64); 10] = [
    (5, 5),
    (0, 0),
    (u64::MAX, u64::MAX),
    (0x8000_0000_0000_0000, 0x8000_0000_0000_0000),
    (1, 2),
    (7, 6),
    (u64::MAX, 0),
    (0, u64::MAX),
    (4, 5),
    (0x1_0000_0005, 5),
];

/// The source semantics, computed here rather than read from either binary.
fn sel(a: u64, b: u64) -> u64 {
    if a == b { a ^ 1 } else { b }
}

fn expected() -> String {
    VECTORS.iter().map(|&(a, b)| format!("{a} {b} {}\n", sel(a, b))).collect()
}

fn link_and_run(obj: &str, exe: &str) -> String {
    cc().input("main.c").input(obj).out_exe(exe).args(extra_c_flags()).run();
    run(exe).stdout_utf8()
}

/// The trust-ir codegen frontend on `sel.rs`, one object, under the output
/// gate `gate` (`None` = the default, strict).
fn f1(out: &str, gate: Option<&str>) -> run_make_support::Rustc {
    rfs::create_dir(out);
    let mut cmd = rustc();
    cmd.input("sel.rs")
        .crate_type("lib")
        .edition("2024")
        .emit("obj")
        .codegen_units(1)
        .arg("-Cpanic=abort")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        // The subject is the codegen gate's verdict, not the source verifier's.
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-cg-frontend=trust-ir")
        .out_dir(out);
    if let Some(gate) = gate {
        cmd.arg(format!("-Ztrust-cg-output-gate={gate}"));
    }
    cmd
}

fn assert_never_refuted(stderr: &str) {
    for forbidden in ["MISCOMPILE", "(Refuted", "internal compiler error", "panicked at"] {
        assert!(
            !stderr.contains(forbidden),
            "`sel` is correct code — the F-114 refutation class is back (`{forbidden}`):\n{stderr}"
        );
    }
}

fn main() {
    // ── (1) STRICT: the default gate refuses on GRADE, never on refutation ──
    let strict = f1("out_strict", None).run_fail();
    let stderr = strict.stderr_utf8();
    assert_never_refuted(&stderr);
    for expected in [
        "trust-cg trust-ir frontend: 1/1 reachable function(s) completed",
        "REFUSED: function `sel` could not be proven output-preserving",
        "function is [VALIDATED] (ay-only authority) but StrictProvenOnly ships ONLY \
         kernel-re-checkable [PROVED] functions",
    ] {
        assert!(stderr.contains(expected), "missing `{expected}` in:\n{stderr}");
    }
    assert!(
        !std::path::Path::new("out_strict/sel.o").exists(),
        "the strict gate refused `sel`, so no object may be written"
    );

    // ── (2) EMITTED: the same bytes, proven at the ay-only grade ────────────
    let emitted = f1("out_f1", Some("allow-unknown")).run();
    let stderr = emitted.stderr_utf8();
    assert_never_refuted(&stderr);
    for expected in [
        "trust-cg trust-ir frontend: 1/1 reachable function(s) completed",
        "0 [PROVED] (kernel-re-checkable), 1 [VALIDATED] (ay-only), 0 uncertified",
        "0 refuted (never emitted)",
    ] {
        assert!(stderr.contains(expected), "missing `{expected}` in:\n{stderr}");
    }

    // ── (3) ORACLE: the same source on the LLVM lane ────────────────────────
    rfs::create_dir("out_llvm");
    rustc()
        .input("sel.rs")
        .crate_type("lib")
        .edition("2024")
        .emit("obj")
        .codegen_units(1)
        .arg("-Cpanic=abort")
        .arg("-Ztrust-verify=off")
        .out_dir("out_llvm")
        .run();

    // ── (4) the same C main over both objects, against computed truth ───────
    let want = expected();
    assert_eq!(want.lines().count(), VECTORS.len());
    let f1_out = link_and_run("out_f1/sel.o", "sel_f1");
    let llvm_out = link_and_run("out_llvm/sel.o", "sel_llvm");
    assert_eq!(llvm_out, want, "the LLVM-lane oracle disagrees with the source semantics");
    assert_eq!(
        f1_out, want,
        "the trust-cg object the gate proved (ay-only grade) computes a different `sel` \
         than the source (the LLVM lane agrees with the source)"
    );
}

//! Trust (owner ruling D38, 2026-10-02, "sanction and record"; docs/DECISION_QUEUE.md D38,
//! docs/issues/2026-09-28-clean-origin-bodies-reach-trust-cg-outside-both-licenses.md): the
//! POSITIVE fixture for Lean bodies on trust-cg's MIR frontend.
//!
//! On `-Zcodegen-backend=trust-cg -Ztrust-cg-frontend=mir` a Clean-origin `def` is compiled from
//! the MIR `clean_origin_mir` builds, with no Clean-specific check on the bytes. D38 sanctions
//! that route as a COMPOSITION (docs/TCB.md, "Clean-origin body on trust-cg's MIR frontend"):
//! the I5 kernel gate identifies the MIR body with the kernel-checked declaration at the carrier
//! (fatal, every lane, no verification switch disables it), and the strict proven-output gate
//! ships only functions whose bytes carry a kernel-re-checkable `[PROVED]` certificate against
//! the IR derived from that MIR. Neither half sees the other's object, and nothing composes them
//! into one certificate; the route leaves with the MIR frontend (R-2). docs/KNOWN_HAZARDS.md
//! records it.
//!
//! Pins, measured on a stage 1 of `a6807aa6f0` before this fixture existed (the route was live
//! and unpinned in either polarity):
//!  * SUBJECT — the call-free Lean leaf `cleanXor := a ^^^ b`, called from a Rust `extern "C"`
//!    wrapper, compiles under the DEFAULT (strict) output gate with verification off and on:
//!    `2 [PROVED]`, both functions byte-preserved, the Clean def's own symbol defined in the
//!    trust-cg object (compiled there, not inlined away), and a binary linked against it prints
//!    the LLVM lane's value (`xorf(47) = 40`);
//!  * CONTROL — the same wrapper around `cleanWsum := a + b`, whose MIR calls
//!    `u64::wrapping_add`, is REFUSED by that gate and writes no rlib: the route ships a unit
//!    only when every function in it is `[PROVED]`. The function refused is the RUST wrapper
//!    `wsumf`, not the Lean body. The gate proves `cleanWsum` and `wrapping_add` themselves
//!    (with verification off under `allow-unknown`: `2 [PROVED]`, `1 uncertified`, and strict
//!    names `wsumf`), and refuses `wsumf` because the gate composes a call only into a
//!    CALL-FREE proven callee (PHASE 0, `build_callee_env` in
//!    crates/trust-cg-bridge/src/verify_output.rs) and `cleanWsum` calls `wrapping_add`;
//!  * TWIN — a pure-Rust body of the same call shape (`#[inline(never)] fn rsum(a, b) {
//!    a.wrapping_add(b) }` behind the same wrapper) gets the identical refusal and the identical
//!    `allow-unknown` report. The refusal is the one-level composition limit, nothing about the
//!    Lean body: the gate never inspects provenance, so a Lean body ships exactly when a Rust
//!    body of the same MIR would. (Corrected by the step-3 review, 2026-10-05: the control was
//!    first described as a Lean body the strict gate cannot certify; measured on the stage 1
//!    of `f129af4800`, it is not.)
//!  * AT `-O` (KERNEL-MIR-PARITY-1) — everything above is the route WITHOUT MIR inlining:
//!    `-Copt-level=0`, every verifying session, whose default `-Zmir-opt-level` is capped at 1
//!    (`trust_default_mir_opt_level_by_flags`), and, since 67eb4a8950 ("pins the off lane's MIR
//!    level"), every verification-off build of a crate that carries a kernel obligation, which an
//!    island is: "a body the session's level would decide now runs level 1"
//!    (`trust_session_mir_opt_level`; docs/DECISION_QUEUE.md KERNEL-MIR-PARITY-1). So a plain
//!    `-Copt-level=2` with verification off keeps the `-O0` results: the SUBJECT ships
//!    `2 [PROVED]` with `xorf` still calling the compiled `cleanXor`, and the CONTROL is refused
//!    with no rlib (before 67eb4a8950 the inliner ran there and the CONTROL shipped).
//!  * WHERE THE MIR INLINER RUNS (step-3 review, 2026-10-07): with an explicit
//!    `-Zmir-opt-level=2`, which 67eb4a8950 keeps as the author's choice, and verification off,
//!    the inliner copies the gated Clean body into the Rust wrapper and later MIR passes rewrite
//!    the copy, so the backend reads, and the strict gate proves, the wrapper's post-inlining MIR:
//!    SUBJECT and CONTROL both ship, the private Clean def is not compiled at all, and the
//!    binaries print the LLVM lane's values (`xorf(47) = 40`; `wsumf(41) = 42` and
//!    `wsumf(u64::MAX) = 0`). SUBJECT ships `1 [PROVED]`. Since TG14 (487d051249, "preserve
//!    authenticated arithmetic calls in ordinary optimized builds") the inliner keeps
//!    `cleanWsum`'s authenticated `u64::wrapping_add` a call in every build, so the CONTROL's
//!    wrapper calls it and ships `2 [PROVED]`: `wsumf` and the `wrapping_add` instance (before
//!    TG14 it was inlined in turn and lowered to `Add`: `1 [PROVED]`). Verification on at
//!    `-Copt-level=2` keeps the `-O0` results (no inliner). The I5 gate's body is then not the
//!    body the backend read; docs/TCB.md lists caller-side inlining and those passes as trusted.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::object::read::archive::ArchiveFile;
use run_make_support::object::{File, Object, ObjectSymbol};
use run_make_support::{bin_name, rfs, run, rust_lib_name, rustc};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";

const LEAF: &str = r#"#![crate_name = "leaf"]
clean {
    def cleanXor (a : UInt64) (b : UInt64) : UInt64 := a ^^^ b
}
#[unsafe(no_mangle)]
pub extern "C" fn xorf(x: u64) -> u64 {
    cleanXor(x, 7)
}
"#;

const WSUM: &str = r#"#![crate_name = "wsum"]
clean {
    def cleanWsum (a : UInt64) (b : UInt64) : UInt64 := a + b
}
#[unsafe(no_mangle)]
pub extern "C" fn wsumf(x: u64) -> u64 {
    cleanWsum(x, 1)
}
"#;

/// The CONTROL's pure-Rust twin: the same call shape with no Clean body anywhere.
const RSUM: &str = r#"#![crate_name = "rsum"]
#[inline(never)]
fn rsum(a: u64, b: u64) -> u64 {
    a.wrapping_add(b)
}
#[unsafe(no_mangle)]
pub extern "C" fn rsumf(x: u64) -> u64 {
    rsum(x, 1)
}
"#;

const MAIN: &str = r#"fn main() {
    println!("xorf(47) = {}", leaf::xorf(47));
}
"#;

const MAIN_WSUM: &str = r#"fn main() {
    println!("wsumf(41) = {}", wsum::wsumf(41));
    println!("wsumf(u64::MAX) = {}", wsum::wsumf(u64::MAX));
}
"#;

fn mir_frontend(input: &str, out: &str, verify: &[&str]) -> run_make_support::Rustc {
    rfs::create_dir_all(out);
    let mut cmd = rustc();
    cmd.input(input)
        .crate_type("rlib")
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Ccodegen-units=1")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-cg-frontend=mir")
        .args(verify)
        .out_dir(out)
        .env_remove(TRUST_NO_VERIFY_ENV);
    cmd
}

/// The symbols `rlib`'s one object defines.
fn defined_symbols(rlib: &str) -> Vec<String> {
    let object = object_member(rlib);
    let object = File::parse(&*object).expect("the trust-cg object");
    object
        .symbols()
        .filter(|symbol| symbol.is_definition())
        .filter_map(|symbol| symbol.name().ok().map(str::to_string))
        .collect()
}

/// Links `main_src` against `krate`'s rlib on the LLVM lane and returns the binary's stdout.
fn run_linked(main_src: &str, krate: &str, rlib: &str, exe: &str) -> String {
    let main_file = format!("{exe}.rs");
    rfs::write(&main_file, main_src);
    rustc()
        .input(&main_file)
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Ztrust-verify=off")
        .extern_(krate, rlib)
        .output(bin_name(exe))
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run();
    run(exe).stdout_utf8()
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

fn main() {
    rfs::write("leaf.rs", LEAF);
    rfs::write("wsum.rs", WSUM);
    rfs::write("rsum.rs", RSUM);
    rfs::write("main.rs", MAIN);

    for (lane, verify) in [
        ("off", &["-Ztrust-verify=off"][..]),
        ("on", &["-Ztrust-verify=on", "-Ztrust-policy=strict"][..]),
    ] {
        // ── SUBJECT: the certifiable Lean leaf ships `[PROVED]` under the strict gate ────
        let out = format!("out-leaf-{lane}");
        let built = mir_frontend("leaf.rs", &out, verify).run();
        let stderr = built.stderr_utf8();
        for expected in [
            "2 [PROVED] (kernel-re-checkable), 0 [VALIDATED] (ay-only), 0 uncertified",
            "policy: strict (certified-fragment: only [PROVED] ships)",
            "2 function(s) byte-preserved into one object",
        ] {
            assert!(stderr.contains(expected), "{lane}: missing `{expected}` in:\n{stderr}");
        }
        for forbidden in ["internal compiler error", "[clean-below-gate]", "refused"] {
            assert!(!stderr.contains(forbidden), "{lane}: `{forbidden}` in:\n{stderr}");
        }
        if lane == "on" {
            assert!(stderr.contains("Trust verification: 1 proved, 0 failed"), "{stderr}");
        }
        let rlib = format!("{out}/{}", rust_lib_name("leaf"));
        let defined = defined_symbols(&rlib);
        assert!(defined.iter().any(|s| s.contains("xorf")), "{lane}: `xorf` defined: {defined:?}");
        assert!(
            defined.iter().any(|s| s.contains("cleanXor")),
            "{lane}: the Clean def is compiled into the trust-cg object: {defined:?}"
        );

        // The bytes compute the LLVM lane's value.
        let exe = format!("main-{lane}");
        rustc()
            .input("main.rs")
            .edition("2021")
            .arg("-Cpanic=abort")
            .arg("-Ztrust-verify=off")
            .extern_("leaf", &rlib)
            .output(bin_name(&exe))
            .env_remove(TRUST_NO_VERIFY_ENV)
            .run();
        assert_eq!(run(&exe).stdout_utf8(), "xorf(47) = 40\n", "{lane}");

        // ── CONTROL and TWIN: the strict gate refuses the RUST wrapper of a callee that calls
        // (one-level composition), whether that callee is the Lean body or a Rust one ─────────
        for (krate, wrapper, callee) in [("wsum", "wsumf", "cleanWsum"), ("rsum", "rsumf", "rsum")]
        {
            let out = format!("out-{krate}-{lane}");
            let refused = mir_frontend(&format!("{krate}.rs"), &out, verify).run_fail();
            let stderr = refused.stderr_utf8();
            let named = format!(
                "REFUSED: function `{wrapper}` could not be proven output-preserving (Unknown, \
                 fail-closed under StrictProvenOnly)"
            );
            for expected in [
                "the in-compiler proven-output gate rejected it",
                named.as_str(),
                "is not a known local pure Proven callee",
            ] {
                assert!(stderr.contains(expected), "{lane} {krate}: missing `{expected}` in:\n{stderr}");
            }
            // The callee named in the refusal is the one the wrapper calls (its mangled symbol).
            let callee_line = stderr
                .lines()
                .find(|line| line.contains("is not a known local pure Proven callee"))
                .unwrap_or_default();
            assert!(callee_line.contains(callee), "{lane} {krate}: callee `{callee}` in:\n{stderr}");
            assert!(!stderr.contains("internal compiler error"), "{stderr}");
            assert!(
                !std::path::Path::new(&out).join(rust_lib_name(krate)).exists(),
                "{lane} {krate}: a refused unit writes no rlib"
            );
        }
    }

    // ── -Copt-level=2, verification off, no explicit MIR level: no inliner ─────────────────
    // KERNEL-MIR-PARITY-1 (67eb4a8950): a crate with an island runs MIR level 1 at every
    // `-Copt-level`, so the `-O0` results hold. The SUBJECT ships with `xorf` still calling the
    // compiled Clean def, and the CONTROL is refused with no rlib. Either half failing means the
    // inliner rewrote the gated Clean body in a default `-O` build again.
    let built = mir_frontend("leaf.rs", "out-leaf-o2-off", &["-Ztrust-verify=off"])
        .arg("-Copt-level=2")
        .arg("--emit=mir,link")
        .run();
    let stderr = built.stderr_utf8();
    for expected in [
        "note: trust-cg certification report for module `leaf.codegen_unit.0`: 2 [PROVED] \
         (kernel-re-checkable), 0 [VALIDATED] (ay-only), 0 uncertified",
        "policy: strict (certified-fragment: only [PROVED] ships)",
        "2 function(s) byte-preserved into one object",
    ] {
        assert!(stderr.contains(expected), "leaf -O2 off: missing `{expected}` in:\n{stderr}");
    }
    for forbidden in ["internal compiler error", "refused", "REFUSED"] {
        assert!(!stderr.contains(forbidden), "leaf -O2 off: `{forbidden}` in:\n{stderr}");
    }
    let mir = rfs::read_to_string("out-leaf-o2-off/leaf.mir");
    let wrapper_mir =
        mir.split("\nfn ").find(|item| item.starts_with("xorf(")).unwrap_or_default();
    assert!(wrapper_mir.contains("= cleanXor("), "leaf -O2 off: `xorf` calls `cleanXor`:\n{mir}");
    assert!(
        !wrapper_mir.contains("(inlined cleanXor)"),
        "leaf -O2 off: `xorf` does not inline `cleanXor`:\n{mir}"
    );
    let rlib = format!("out-leaf-o2-off/{}", rust_lib_name("leaf"));
    let defined = defined_symbols(&rlib);
    assert!(defined.iter().any(|s| s.contains("xorf")), "leaf -O2 off: {defined:?}");
    assert!(defined.iter().any(|s| s.contains("cleanXor")), "leaf -O2 off: {defined:?}");
    assert_eq!(run_linked(MAIN, "leaf", &rlib, "main-leaf-o2"), "xorf(47) = 40\n", "leaf -O2 off");
    let refused = mir_frontend("wsum.rs", "out-wsum-o2-off", &["-Ztrust-verify=off"])
        .arg("-Copt-level=2")
        .run_fail();
    let stderr = refused.stderr_utf8();
    for expected in [
        "REFUSED: function `wsumf` could not be proven output-preserving (Unknown, fail-closed \
         under StrictProvenOnly)",
        "is not a known local pure Proven callee",
    ] {
        assert!(stderr.contains(expected), "wsum -O2 off: missing `{expected}` in:\n{stderr}");
    }
    let callee_line = stderr
        .lines()
        .find(|line| line.contains("is not a known local pure Proven callee"))
        .unwrap_or_default();
    assert!(callee_line.contains("cleanWsum"), "wsum -O2 off: callee `cleanWsum` in:\n{stderr}");
    assert!(!stderr.contains("internal compiler error"), "{stderr}");
    assert!(
        !std::path::Path::new("out-wsum-o2-off").join(rust_lib_name("wsum")).exists(),
        "wsum -O2 off: a refused unit writes no rlib"
    );

    // ── -Copt-level=2 -Zmir-opt-level=2: the MIR inliner runs only with verification off ───
    // An explicit level is the author's and is kept (67eb4a8950; a proof session refuses it).
    // Verification off: the inliner copies the gated Clean body into the wrapper and later MIR
    // passes rewrite the copy, so the gate proves the wrapper's post-inlining MIR, the Clean def
    // is not compiled, and the CONTROL ships too (docs/TCB.md, D38 row: caller-side inlining and
    // those passes are trusted). The bytes still compute the LLVM lane's values.
    // TG14 (487d051249) keeps the authenticated `u64::wrapping_add` that `cleanWsum` calls a call
    // through MIR inlining, so the CONTROL compiles it as a second [PROVED] function.
    for (krate, wrapper, clean, main_src, expected, shipped) in [
        ("leaf", "xorf", "cleanXor", MAIN, "xorf(47) = 40\n", 1),
        ("wsum", "wsumf", "cleanWsum", MAIN_WSUM, "wsumf(41) = 42\nwsumf(u64::MAX) = 0\n", 2),
    ] {
        let out = format!("out-{krate}-o2-mir2-off");
        let built = mir_frontend(&format!("{krate}.rs"), &out, &["-Ztrust-verify=off"])
            .arg("-Copt-level=2")
            .arg("-Zmir-opt-level=2")
            .arg("--emit=mir,link")
            .run();
        let stderr = built.stderr_utf8();
        for expected in [
            format!(
                "note: trust-cg certification report for module `{krate}.codegen_unit.0`: \
                 {shipped} [PROVED] (kernel-re-checkable), 0 [VALIDATED] (ay-only), 0 uncertified"
            ),
            "policy: strict (certified-fragment: only [PROVED] ships)".to_string(),
            format!("{shipped} function(s) byte-preserved into one object"),
        ] {
            assert!(stderr.contains(&expected), "{krate} -O2 mir2: missing `{expected}` in:\n{stderr}");
        }
        for forbidden in ["internal compiler error", "refused", "REFUSED"] {
            assert!(!stderr.contains(forbidden), "{krate} -O2 mir2: `{forbidden}` in:\n{stderr}");
        }
        // The wrapper's optimized MIR carries the inlined Clean body, and no call to it.
        let mir = rfs::read_to_string(format!("{out}/{krate}.mir"));
        let wrapper_mir = mir
            .split("\nfn ")
            .find(|item| item.starts_with(&format!("{wrapper}(")))
            .unwrap_or_default();
        assert!(
            wrapper_mir.contains(&format!("(inlined {clean})")),
            "{krate} -O2 mir2: `{wrapper}` inlines `{clean}`:\n{mir}"
        );
        assert!(
            !wrapper_mir.contains(&format!("= {clean}(")),
            "{krate} -O2 mir2: no call to `{clean}` left in `{wrapper}`:\n{mir}"
        );
        let rlib = format!("{out}/{}", rust_lib_name(krate));
        let defined = defined_symbols(&rlib);
        assert!(defined.iter().any(|s| s.contains(wrapper)), "{krate}: `{wrapper}` defined: {defined:?}");
        assert!(
            !defined.iter().any(|s| s.contains(clean)),
            "{krate} -O2 mir2: the private Clean def is not compiled: {defined:?}"
        );
        // The second shipped function is exactly the preserved `wrapping_add` call's instance.
        assert_eq!(
            defined.iter().any(|s| s.contains("wrapping_add")),
            shipped == 2,
            "{krate} -O2 mir2: the preserved `wrapping_add` instance: {defined:?}"
        );
        assert_eq!(
            wrapper_mir.contains("core::num::<impl u64>::wrapping_add("),
            shipped == 2,
            "{krate} -O2 mir2: TG14 keeps the authenticated `wrapping_add` a call:\n{mir}"
        );
        assert_eq!(run_linked(main_src, krate, &rlib, &format!("main-{krate}-o2-mir2")), expected, "{krate}");
    }
    // Verification on: the default MIR opt level is capped at 1, the inliner does not run, and the
    // `-O0` results hold (the SUBJECT ships with its Clean def compiled; the CONTROL is refused).
    let verify_on = &["-Ztrust-verify=on", "-Ztrust-policy=strict"][..];
    let built = mir_frontend("leaf.rs", "out-leaf-o2-on", verify_on).arg("-Copt-level=2").run();
    let stderr = built.stderr_utf8();
    assert!(
        stderr.contains("2 [PROVED] (kernel-re-checkable), 0 [VALIDATED] (ay-only), 0 uncertified"),
        "leaf -O2 on:\n{stderr}"
    );
    let defined = defined_symbols(&format!("out-leaf-o2-on/{}", rust_lib_name("leaf")));
    assert!(defined.iter().any(|s| s.contains("cleanXor")), "leaf -O2 on: {defined:?}");
    let refused = mir_frontend("wsum.rs", "out-wsum-o2-on", verify_on).arg("-Copt-level=2").run_fail();
    refused.assert_stderr_contains("REFUSED: function `wsumf` could not be proven output-preserving");
    assert!(!std::path::Path::new("out-wsum-o2-on").join(rust_lib_name("wsum")).exists());

    // What the gate proves in the CONTROL (verification off is the lane that accepts
    // `allow-unknown`): the Lean body and `wrapping_add` are `[PROVED]` and the ONE uncertified
    // function is the wrapper strict names above; the pure-Rust twin reports the same.
    for krate in ["wsum", "rsum"] {
        let out = format!("out-{krate}-allow-unknown");
        let built = mir_frontend(&format!("{krate}.rs"), &out, &["-Ztrust-verify=off"])
            .arg("-Ztrust-cg-output-gate=allow-unknown")
            .run();
        let stderr = built.stderr_utf8();
        for expected in [
            "2 [PROVED] (kernel-re-checkable), 0 [VALIDATED] (ay-only), 1 uncertified",
            "3 function(s) byte-preserved into one object",
        ] {
            assert!(stderr.contains(expected), "{krate} allow-unknown: missing `{expected}` in:\n{stderr}");
        }
    }
}

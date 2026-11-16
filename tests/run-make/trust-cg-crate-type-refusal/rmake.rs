//! Trust (WS7.10 / F-114): a crate type trust-cg cannot emit FAILS LOUDLY.
//! Proof-program row `scout-f1.7` (`--crate-type=bin|staticlib|cdylib` exited 0
//! with no artifact) is the negative twins in (2) below.
//!
//! THE HOLE. With native machine output requested, trust-cg advertises
//! `[Rlib]` only (`supported_crate_types_for_outputs`). rustc's upstream
//! response to any other requested crate type is `collect_crate_types`'
//! "dropping unsupported crate type" WARNING, so a plain `rustc main.rs` (whose
//! default crate type is `bin`) under `-Zcodegen-backend=trust-cg` exited 0 and
//! produced nothing. The backend's own `codegen_crate` refusal was unreachable,
//! because `tcx.crate_types()` had already been filtered to empty.
//!
//! THE FIX. The backend hook `CodegenBackend::unsupported_crate_type_is_fatal`
//! turns the drop into a named error for every session that requests native
//! output AND will run codegen. It stays `false` for a print-only invocation, so
//! Cargo's capability probe keeps its warn-and-omit contract: Cargo reads the
//! "unsupported crate type `<ty>`" warning and a missing `file-names` line as
//! "unsupported", and an error there would fail every Cargo build under
//! trust-cg, rlib-only ones included. Both command lines Cargo sends are pinned
//! below as measured from cargo 1.97.0 on 2026-09-18 (a `RUSTC_WRAPPER` log);
//! (3c) and (3d) say which bytes, if any, differ.
//!
//! THE RLIB LANES ON AN x86_64 HOST. The crate-type rule is target-independent,
//! but whether a supported `rlib` is then EMITTED is the strict proven-output
//! gate's call, and that gate decides AArch64 machine code only
//! (`decode_emitted_object_env`, trust-cg-bridge `verify_output.rs`): on any
//! other target it refuses every emitted function, fail-closed. Measured on an
//! x86_64-apple-darwin host (Rosetta, 2026-10-22): the rlib lanes that emit
//! `masked` ((1) and (3a''), at the default opt-level) were refused by that gate
//! ("REFUSING to emit module ... emitted X86_64 code is undecided"), never by the
//! crate-type rule. So [`assert_rlib_lane`] requires the rlib where the gate
//! decides the target, and elsewhere requires that the gate, not the crate-type
//! rule, refused it and that nothing was left behind. The day the gate decides
//! x86-64 code that arm fails, and the rlib is required there too. (3d) emits no
//! machine code at all, so it needs its rlib on every target.
// trust-cg output is calibrated only for the built-in host target.
//@ ignore-cross-compile

//@ needs-trust-cg-backend

use run_make_support::{
    CompletedProcess, bare_rustc, bin_name, dynamic_lib_name, rfs, rust_lib_name, rustc,
    static_lib_name, target,
};

/// What the strict proven-output gate says for machine code it cannot decide.
const OUTPUT_GATE_UNDECIDED: &str =
    "byte-level output preservation is wired for AArch64 machine semantics only";

/// Whether the strict proven-output gate decides this target's machine code.
fn output_gate_decides_target() -> bool {
    target().starts_with("aarch64-")
}

/// A supported-crate-type compilation: the crate-type rule admits it everywhere;
/// it produces `rlib` in `dir` where the output gate decides the target, and is
/// refused by that gate, leaving nothing behind, where it does not.
fn assert_rlib_lane(compiled: CompletedProcess, dir: &str, rlib: &str, label: &str) {
    compiled.assert_stderr_not_contains("cannot emit crate type");
    compiled.assert_stderr_not_contains("dropping unsupported crate type");
    if output_gate_decides_target() {
        assert!(
            compiled.status().success(),
            "{label}: the supported lane failed:\n{}",
            compiled.stderr_utf8()
        );
        assert!(
            dir_names(dir).contains(&rlib.to_string()),
            "{label}: no {rlib} in {dir}: {:?}",
            dir_names(dir)
        );
    } else {
        assert!(
            !compiled.status().success(),
            "{label}: the output gate cannot decide {} code, yet the lane succeeded",
            target()
        );
        compiled.assert_stderr_contains("REFUSING to emit module");
        compiled.assert_stderr_contains(OUTPUT_GATE_UNDECIDED);
        assert_no_artifacts(dir, label);
    }
}

/// The named refusal. Asserted by substring so the error stays attached to the
/// crate type it refused and to the backend that refused it.
fn refusal(crate_type: &str) -> String {
    format!("codegen backend `trust-cg` cannot emit crate type `{crate_type}`")
}

const REFUSED_NOT_DROPPED: &str = "the crate type is refused rather than dropped";

/// Flags every trust-cg compilation here shares: the backend selected explicitly
/// (LLVM stays the default), the full verifier off so the only diagnostics are
/// the backend's and rustc_interface's, and `panic=abort` because trust-cg
/// refuses `panic=unwind` outright.
fn trust_cg(input: &str, out: &str) -> run_make_support::Rustc {
    let mut rustc = rustc();
    rustc
        .input(input)
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-verify=off")
        .out_dir(out);
    rustc
}

fn dir_names(dir: &str) -> Vec<String> {
    rfs::read_dir(dir)
        .map(|entry| entry.expect("read output dir").file_name().to_string_lossy().into_owned())
        .collect()
}

/// A refused compilation must leave NO artifact behind: not the refused type,
/// and not a partial rlib from a mixed request.
fn assert_no_artifacts(dir: &str, label: &str) {
    let left = dir_names(dir);
    assert!(
        left.iter().all(|name| {
            !(name.ends_with(".rlib")
                || name.ends_with(".a")
                || name.ends_with(".lib")
                || name.ends_with(".o")
                || name.ends_with(".obj")
                || name.ends_with(".dylib")
                || name.ends_with(".so")
                || name.ends_with(".dll")
                || name.ends_with(".exe")
                || name == "crate_types")
        }),
        "{label}: a refused compilation left artifacts behind: {left:?}"
    );
}

fn main() {
    // The body is the proven scalar-register shape (`masked` is [PROVED] by the
    // strict output gate on the MIR lane; see trust-cg-abi-extension-refusal),
    // so the POSITIVE case below fails only if the crate-type policy is wrong.
    rfs::write(
        "crate_types.rs",
        "#![crate_name = \"crate_types\"]\n\
         pub fn masked(x: u32) -> u8 { (x & 0xff) as u8 }\n\
         #[allow(dead_code)]\n\
         fn main() {}\n",
    );

    // ---------------------------------------------------------------------
    // (1) POSITIVE. `--crate-type=rlib` is the supported lane: no crate-type
    //     refusal and no drop; it produces the rlib wherever the output gate
    //     decides the target (`assert_rlib_lane`).
    // ---------------------------------------------------------------------
    rfs::create_dir("out_rlib");
    let ok = trust_cg("crate_types.rs", "out_rlib").crate_type("rlib").run_unchecked();
    assert_rlib_lane(ok, "out_rlib", &rust_lib_name("crate_types"), "--crate-type=rlib");

    // ---------------------------------------------------------------------
    // (2) NEGATIVE TWINS. Each differs from (1) by the crate type alone, and
    //     each must exit non-zero with the NAMED refusal and no artifact.
    //     Before WS7.10 every one of these exited 0 with a warning.
    // ---------------------------------------------------------------------
    for crate_type in ["bin", "staticlib", "cdylib"] {
        let out = format!("out_{crate_type}");
        rfs::create_dir(&out);
        let refused = trust_cg("crate_types.rs", &out).crate_type(crate_type).run_fail();
        refused.assert_stderr_contains(refusal(crate_type));
        refused.assert_stderr_contains(REFUSED_NOT_DROPPED);
        refused.assert_stderr_contains("supports only the crate type(s) `rlib`");
        refused.assert_stderr_not_contains("dropping unsupported crate type");
        assert_no_artifacts(&out, crate_type);
    }
    // Belt and braces for the names above: the specific artifacts are absent.
    assert!(!dir_names("out_bin").contains(&bin_name("crate_types")));
    assert!(!dir_names("out_staticlib").contains(&static_lib_name("crate_types")));
    assert!(!dir_names("out_cdylib").contains(&dynamic_lib_name("crate_types")));

    // No `--crate-type` at all: rustc's default for an executable-capable
    // target is `bin`. This is the literal F-114 reproduction (`rustc main.rs`).
    rfs::create_dir("out_default");
    let default = trust_cg("crate_types.rs", "out_default").run_fail();
    default.assert_stderr_contains(refusal("bin"));
    default.assert_stderr_contains(REFUSED_NOT_DROPPED);
    assert_no_artifacts("out_default", "default crate type");

    // A mixed request refuses as a whole: the unsupported `bin` is named, and
    // the supported `rlib` is NOT left behind as a partial result.
    rfs::create_dir("out_mixed");
    let mixed = trust_cg("crate_types.rs", "out_mixed").crate_type("bin,rlib").run_fail();
    mixed.assert_stderr_contains(refusal("bin"));
    mixed.assert_stderr_not_contains(refusal("rlib"));
    assert_no_artifacts("out_mixed", "bin,rlib");

    // The object lane is native output too (`native_machine_output_requested`
    // covers `--emit=obj`), so it cannot be a side door around the refusal.
    rfs::create_dir("out_obj_bin");
    let obj = trust_cg("crate_types.rs", "out_obj_bin").crate_type("bin").emit("obj").run_fail();
    obj.assert_stderr_contains(refusal("bin"));
    assert_no_artifacts("out_obj_bin", "--emit=obj --crate-type=bin");

    // ---------------------------------------------------------------------
    // (2b) REVIEW TWINS (WS7.10 adversarial review): side doors the first
    //      cut did not exercise. Each must be refused with the named error.
    // ---------------------------------------------------------------------

    // The remaining two unadvertised command-line types.
    for crate_type in ["dylib", "proc-macro"] {
        let out = format!("out_{crate_type}");
        rfs::create_dir(&out);
        let refused = trust_cg("crate_types.rs", &out).crate_type(crate_type).run_fail();
        refused.assert_stderr_contains(refusal(crate_type));
        refused.assert_stderr_not_contains("dropping unsupported crate type");
        assert_no_artifacts(&out, crate_type);
    }

    // A crate type named by a SOURCE ATTRIBUTE, not the command line: the
    // attribute path through `collect_crate_types` is refused too, and a
    // supported `rlib` beside it is not left behind as a partial result.
    rfs::write(
        "attr_types.rs",
        "#![crate_type = \"staticlib\"]\n\
         #![crate_type = \"rlib\"]\n\
         pub fn masked(x: u32) -> u8 { (x & 0xff) as u8 }\n",
    );
    rfs::create_dir("out_attr");
    let attr = trust_cg("attr_types.rs", "out_attr").run_fail();
    attr.assert_stderr_contains(refusal("staticlib"));
    attr.assert_stderr_not_contains(refusal("rlib"));
    assert_no_artifacts("out_attr", "#![crate_type = \"staticlib\"] + rlib");

    // A print request that does NOT stop before codegen is not an exemption:
    // `--print=native-static-libs` needs a completed link, so the session
    // still runs native codegen and the drop would still be silent.
    rfs::create_dir("out_nsl_bin");
    let nsl = trust_cg("crate_types.rs", "out_nsl_bin")
        .crate_type("bin")
        .print("native-static-libs")
        .run_fail();
    nsl.assert_stderr_contains(refusal("bin"));
    assert_no_artifacts("out_nsl_bin", "--print=native-static-libs --crate-type=bin");

    // `-Zno-codegen` skips `codegen_crate` but still runs the link step, which
    // publishes the other requested types (rustc writes an object-less
    // staticlib archive there); dropping one is still a missing artifact.
    rfs::create_dir("out_nocg_staticlib");
    let nocg = trust_cg("crate_types.rs", "out_nocg_staticlib")
        .crate_type("staticlib")
        .arg("-Zno-codegen")
        .run_fail();
    nocg.assert_stderr_contains(refusal("staticlib"));
    assert_no_artifacts("out_nocg_staticlib", "-Zno-codegen --crate-type=staticlib");

    // ---------------------------------------------------------------------
    // (3) CONTROLS — the new rule caused the refusals above, and it does not
    //     over-refuse.
    // ---------------------------------------------------------------------

    // (3a) Frontend-only output is unaffected: `--emit=metadata` with `bin`
    //      runs no native codegen, trust-cg advertises every crate type for it,
    //      and it neither refuses nor drops.
    rfs::create_dir("out_meta");
    let meta = trust_cg("crate_types.rs", "out_meta").crate_type("bin").emit("metadata").run();
    meta.assert_stderr_not_contains("cannot emit crate type");
    meta.assert_stderr_not_contains("dropping unsupported crate type");
    assert!(
        dir_names("out_meta").iter().any(|name| name.ends_with(".rmeta")),
        "--emit=metadata --crate-type=bin produced no .rmeta: {:?}",
        dir_names("out_meta")
    );

    // (3a') Driver modes that build the global context but exit before
    //       codegen and link emit no artifact of ANY crate type, so the
    //       default `bin` of a `main.rs` must not be refused there (WS7.10
    //       review: the first cut made `rustc -Zunpretty=mir main.rs` under
    //       trust-cg an error). Each keeps the upstream warning and exits 0.
    for (mode, label) in [
        ("-Zunpretty=mir", "unpretty-mir"),
        ("-Zunpretty=thir-tree", "unpretty-thir-tree"),
        ("-Zno-analysis", "no-analysis"),
    ] {
        let out = format!("out_{label}");
        rfs::create_dir(&out);
        let early = trust_cg("crate_types.rs", &out).arg(mode).run();
        early.assert_stderr_not_contains("cannot emit crate type");
        early.assert_stderr_contains("dropping unsupported crate type `bin`");
        assert_no_artifacts(&out, label);
        if mode == "-Zunpretty=mir" {
            early.assert_stdout_contains("fn masked(");
        }
    }

    // (3a'') `--crate-type=lib` is rustc's spelling of the default library
    //        type, which is `rlib`: it is the supported lane, not a refusal.
    rfs::create_dir("out_lib");
    let lib = trust_cg("crate_types.rs", "out_lib").crate_type("lib").run_unchecked();
    assert_rlib_lane(lib, "out_lib", &rust_lib_name("crate_types"), "--crate-type=lib");

    // (3b) The rule is trust-cg's, not rustc's: the default backend still
    //      builds the SAME source as `bin`. A refusal that fired for every
    //      backend would pass (2) for the wrong reason.
    rfs::create_dir("out_default_backend");
    let llvm = rustc()
        .input("crate_types.rs")
        .edition("2021")
        .crate_type("bin")
        .arg("-Ztrust-verify=off")
        .out_dir("out_default_backend")
        .run();
    llvm.assert_stderr_not_contains("cannot emit crate type");
    assert!(
        dir_names("out_default_backend").contains(&bin_name("crate_types")),
        "the default backend no longer builds a bin: {:?}",
        dir_names("out_default_backend")
    );

    // (3c) CARGO'S CAPABILITY PROBE, pinned exactly (cargo 1.97.0,
    //      `TargetInfo::new`): stdin input, `--print=file-names`, then
    //      RUSTFLAGS, then the six KNOWN_CRATE_TYPES, then four more prints and
    //      `-Wwarnings`. It is print-only, so it must exit 0, list ONLY the rlib
    //      file name, and keep the per-type warning Cargo parses for "unsupported".
    let probe = bare_rustc()
        .arg("-")
        .args(["--crate-name", "___", "--print=file-names"])
        // RUSTFLAGS position.
        .args(["-Cpanic=abort", "-Zunstable-options", "-Zcodegen-backend=trust-cg"])
        .args(["--crate-type", "bin", "--crate-type", "rlib", "--crate-type", "dylib"])
        .args(["--crate-type", "cdylib", "--crate-type", "staticlib"])
        .args(["--crate-type", "proc-macro"])
        .args(["--print=sysroot", "--print=split-debuginfo", "--print=crate-name"])
        .args(["--print=cfg", "-Wwarnings"])
        .stdin_buf("")
        .run();
    probe.assert_stderr_not_contains("cannot emit crate type");
    for dropped in ["bin", "dylib", "cdylib", "staticlib", "proc-macro"] {
        // Cargo's `parse_crate_type` keys on exactly this substring.
        probe.assert_stderr_contains(format!("unsupported crate type `{dropped}`"));
    }
    let stdout = probe.stdout_utf8();
    let mut lines = stdout.lines();
    assert_eq!(
        lines.next(),
        Some(rust_lib_name("___").as_str()),
        "the probe's file-names block must list the rlib first:\n{stdout}"
    );
    // The next line is `--print=sysroot`'s answer, so the file-names block held
    // exactly one line: no bin/dylib/cdylib/staticlib/proc-macro file name.
    let sysroot = lines.next().unwrap_or_default();
    assert!(
        std::path::Path::new(sysroot).is_absolute(),
        "the probe listed more than the rlib under file-names:\n{stdout}"
    );
    for absent in [dynamic_lib_name("___"), static_lib_name("___")] {
        assert!(!stdout.lines().any(|line| line == absent), "probe advertised {absent}:\n{stdout}");
    }

    // (3d) THE COMPILATION CARGO SENDS FOR AN RLIB CRATE (`cargo build
    //      --release`, lib target, cargo 1.97.0), pinned except for
    //      `--error-format=json`, which only changes how diagnostics render.
    //      The release profile is the one a trust-cg Cargo build can use at all:
    //      the dev profile's `-C debuginfo=2` is refused by trust-cg on its own
    //      ("-Cdebuginfo is not supported by trust-cg"), independently of the
    //      crate type. `--crate-type lib` must still succeed.
    rfs::create_dir("out_cargo_lib");
    let cargo_lib = bare_rustc()
        .args(["--crate-name", "crate_types", "--edition=2021", "crate_types.rs"])
        .args(["--crate-type", "lib", "--emit=dep-info,metadata,link"])
        .args(["-C", "opt-level=3", "-C", "embed-bitcode=no"])
        .args(["--check-cfg", "cfg(docsrs,test)", "--check-cfg", "cfg(feature, values())"])
        .args(["-C", "metadata=7f2df92d8eb762d5", "-C", "extra-filename=-44534ec1fbb75ac1"])
        .args(["--out-dir", "out_cargo_lib", "-C", "strip=debuginfo"])
        .args(["-L", "dependency=out_cargo_lib"])
        // RUSTFLAGS a trust-cg Cargo build carries.
        .args(["-Cpanic=abort", "-Zunstable-options", "-Zcodegen-backend=trust-cg"])
        .arg("-Ztrust-verify=off")
        .run();
    // Every target: at `-C opt-level=3` rustc makes the small leaf `masked`
    // cross-crate-inlinable, so this lane emits no machine code ("compiled 0
    // function(s)"), leaving the output gate nothing to decide (measured on the
    // x86_64 host, 2026-10-22).
    cargo_lib.assert_stderr_not_contains("cannot emit crate type");
    assert!(
        dir_names("out_cargo_lib").contains(&rust_lib_name("crate_types-44534ec1fbb75ac1")),
        "the Cargo-shaped rlib compilation did not produce its rlib: {:?}",
        dir_names("out_cargo_lib")
    );
}

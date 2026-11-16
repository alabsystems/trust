//! Trust (platform protocols, plan L1a = design PR 8): the `-Ztrust-platform-*` controls change
//! no emitted byte.
//!
//! They are `[TRACKED_NO_CRATE_HASH]`: a change invalidates incremental reuse (the pass adds
//! diagnostics) and leaves the crate hash alone, because the pass never changes what is emitted.
//! The unit test `trust_platform_options_invalidate_incremental_reuse_but_not_the_crate_hash`
//! pins the hash half; this recipe pins the bytes themselves. The same crate is compiled with
//! verification on three times: twice plain (a determinism CONTROL: if two plain compiles differ,
//! a byte comparison proves nothing and the recipe says so) and once with every platform control
//! moved off its default. The rlib and the object file must be byte-identical to the plain ones.
//!
//! Two pins hold for L1a only, and plan L1d changes them on purpose: the flags add no diagnostic
//! at all (from L1d the pass prints its crate summary note), and the `-Ztrust-platform-dump-facts`
//! sink is not written (from L1d it is).
//@ ignore-cross-compile

use std::path::{Path, PathBuf};

use run_make_support::{CompletedProcess, bin_name, cmd, rfs, rustc_path, serde_json};

/// Set by compiletest's `--trust-vanilla` replay, which runs the stock rustc: no Trust options,
/// nothing to pin (the opt-out `//@ needs-trust-verify` gives a ui test).
const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";

const FACTS: &str = "platform.facts";

const ARTIFACTS: [&str; 2] = ["libplatform_inert.rlib", "platform_inert.o"];

fn compile(trustc: &Path, out: &str, platform: bool) -> CompletedProcess {
    rfs::create_dir(out);
    let mut compiler = cmd(trustc);
    compiler.arg("lib.rs").args([
        "--crate-type=rlib",
        "--crate-name=platform_inert",
        "--edition=2021",
        "--emit=link,obj",
        "--error-format=json",
        "-Copt-level=0",
        "-Ccodegen-units=1",
        "-Cdebuginfo=0",
        "-Ztrust-verify=on",
        "-Ztrust-policy=advisory",
        "--out-dir",
        out,
    ]);
    if platform {
        let facts = format!("-Ztrust-platform-dump-facts={FACTS}");
        compiler.args([
            "-Ztrust-platform-properties=fd-inherit",
            "-Ztrust-platform-unanalysed=deny",
            "-Ztrust-platform-budget=1",
            "-Ztrust-platform-report=verbose",
            facts.as_str(),
        ]);
    }
    compiler.run()
}

/// The compiler's diagnostics, as (level, message) in emission order. Only the JSON rows: the
/// verification report the compiler also prints to stderr is not a diagnostic.
fn diagnostics(output: &CompletedProcess) -> Vec<(String, String)> {
    output
        .stderr_utf8()
        .lines()
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
        .filter(|row| row["$message_type"] == "diagnostic")
        .map(|row| {
            (
                row["level"].as_str().unwrap_or_default().to_string(),
                row["message"].as_str().unwrap_or_default().to_string(),
            )
        })
        .collect()
}

fn main() {
    if std::env::var_os(TRUST_VANILLA_REAL_RUSTC_ENV).is_some() {
        return;
    }
    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };

    let plain = compile(&trustc, "plain", false);
    let control = compile(&trustc, "control", false);
    let flagged = compile(&trustc, "flagged", true);

    for artifact in ARTIFACTS {
        let bytes = rfs::read(Path::new("plain").join(artifact));
        assert!(!bytes.is_empty(), "{artifact}: nothing emitted");
        assert!(
            bytes == rfs::read(Path::new("control").join(artifact)),
            "CONTROL: two plain compiles emitted different {artifact}; a byte comparison with the \
             flagged compile would prove nothing",
        );
        assert!(
            bytes == rfs::read(Path::new("flagged").join(artifact)),
            "-Ztrust-platform-* changed the emitted {artifact}",
        );
    }

    assert_eq!(diagnostics(&plain), diagnostics(&control), "CONTROL: diagnostics differ");
    // L1a only (the pass is not wired; L1d adds its summary note here).
    assert_eq!(diagnostics(&plain), diagnostics(&flagged), "the platform flags added diagnostics");
    assert!(!flagged.stderr_utf8().contains("[platform"), "{}", flagged.stderr_utf8());
    // L1a only (L1d writes the sink).
    assert!(!Path::new(FACTS).exists(), "the facts sink was written with no pass to fill it");
}

use std::path::PathBuf;

use run_make_support::{bin_name, cmd, rfs, run, rustc_path};

const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";

fn main() {
    if std::env::var_os(TRUST_VANILLA_REAL_RUSTC_ENV).is_some() {
        return;
    }

    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };

    let report = cmd(&trustc)
        .env("TRUST_MONITOR_REPORT", "1")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .arg("--test")
        .arg("--emit=mir")
        .arg("-Awarnings")
        .arg("loop.rs")
        .arg("-o")
        .arg("loop.mir")
        .run()
        .stderr_utf8();

    assert_exactly_one(
        &report,
        "(LoopInvariant) is unmonitored (runtime placement for compiler contract kind \
         LoopInvariant is not certified)",
    );
    assert_exactly_one(
        &report,
        "(Decreases) is unmonitored (runtime placement for compiler contract kind Decreases is \
         not certified)",
    );

    let optimized_mir = rfs::read_to_string("loop.mir");
    assert!(
        optimized_mir.contains("fn unmonitored_loop"),
        "the emitted optimized MIR did not contain the loop under test:\n{optimized_mir}"
    );
    assert!(
        !optimized_mir.contains("certified_monitor_check"),
        "an unmonitored loop clause inserted a certified-monitor call or block:\n{optimized_mir}"
    );
    assert!(
        !optimized_mir.contains("kernel-certified Trust monitor failed"),
        "an unmonitored loop clause inserted a certified-monitor failure path:\n{optimized_mir}"
    );

    let executable = bin_name("loop-monitors");
    cmd(&trustc)
        .env("TRUST_MONITOR_REPORT", "1")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .arg("--test")
        .arg("-Awarnings")
        .arg("loop.rs")
        .arg("-o")
        .arg(&executable)
        .run();
    run(&executable);
}

fn assert_exactly_one(output: &str, needle: &str) {
    assert_eq!(
        output.matches(needle).count(),
        1,
        "expected exactly one `{needle}` monitor record:\n{output}"
    );
}

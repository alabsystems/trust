use std::path::PathBuf;

use run_make_support::{bin_name, cmd, rfs, run, run_fail, rustc_path};

const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";

fn main() {
    if std::env::var_os(TRUST_VANILLA_REAL_RUSTC_ENV).is_some() {
        return;
    }

    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };

    // Ordinary production MIR must preserve the authored TailCall.
    cmd(&trustc)
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .arg("--crate-type=lib")
        .arg("--emit=mir")
        .arg("-Awarnings")
        .arg("tail.rs")
        .arg("-o")
        .arg("tail-production.mir")
        .run();
    let production = rfs::read_to_string("tail-production.mir");
    assert!(
        production.contains("tailcall identity("),
        "production compilation erased the explicit TailCall:\n{production}"
    );
    assert!(
        production.contains("tailcall tail_countdown("),
        "production compilation erased the recursive explicit TailCall:\n{production}"
    );

    // Only the authenticated test artifact expands it into
    // Call -> ensures monitor -> Return.
    cmd(&trustc)
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .arg("--test")
        .arg("--emit=mir")
        .arg("-Awarnings")
        .arg("tail.rs")
        .arg("-o")
        .arg("tail-test.mir")
        .run();
    let test_mir = rfs::read_to_string("tail-test.mir");
    assert!(
        !test_mir.contains("tailcall identity("),
        "monitor-enabled test MIR retained a TailCall that bypasses ensures:\n{test_mir}"
    );
    assert!(
        !test_mir.contains("tailcall tail_countdown("),
        "monitor-enabled test MIR retained a recursive TailCall that bypasses monitors:\n{test_mir}"
    );
    assert!(
        test_mir.contains("certified_monitor_check"),
        "monitor-enabled TailCall expansion contains no certified check:\n{test_mir}"
    );

    // This fixture has a function-level measure but deliberately has no
    // postcondition. Its finite, non-decreasing tail recursion would return
    // normally if the recursive-edge E5 check disappeared, so the runtime
    // failure below cannot be supplied by an ensures-only helper.
    let bad_tail_report = cmd(&trustc)
        .env("TRUST_MONITOR_REPORT", "1")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .arg("--test")
        .arg("--emit=mir")
        .arg("-Awarnings")
        .arg("tail_decrease_fail.rs")
        .arg("-o")
        .arg("tail-decrease-fail.mir")
        .run()
        .stderr_utf8();
    assert_exactly_one(
        &bad_tail_report,
        "(Decreases) is measured: a kernel-certified scalar evaluator is bound to the exact E5 \
         measure",
    );
    assert!(
        !bad_tail_report.contains("(Ensures) is monitored"),
        "the ensures-free E5 canary unexpectedly acquired a postcondition monitor:\n\
         {bad_tail_report}"
    );

    let bad_tail_mir = rfs::read_to_string("tail-decrease-fail.mir");
    let bad_tail_fn = mir_function(&bad_tail_mir, "tail_stalls");
    assert_eq!(
        bad_tail_fn.matches("certified_monitor_check").count(),
        1,
        "the ensures-free recursive function must contain exactly its one E5 edge check:\n\
         {bad_tail_fn}"
    );
    assert_eq!(
        bad_tail_fn.matches("tailcall tail_stalls(").count(),
        1,
        "the E5 check must guard the one exact recursive TailCall without erasing it:\n\
         {bad_tail_fn}"
    );

    let executable = bin_name("tail-monitor");
    cmd(&trustc)
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .arg("--test")
        .arg("-Awarnings")
        .arg("tail.rs")
        .arg("-o")
        .arg(&executable)
        .run();
    run(&executable);

    let bad_executable = bin_name("tail-decrease-fail");
    cmd(&trustc)
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .arg("--test")
        .arg("-Awarnings")
        .arg("tail_decrease_fail.rs")
        .arg("-o")
        .arg(&bad_executable)
        .run();
    run_fail(&bad_executable).assert_stderr_contains("kernel-certified Trust monitor failed");
}

fn mir_function<'a>(mir: &'a str, name: &str) -> &'a str {
    let signature = format!("fn {name}(");
    let start = mir
        .find(&signature)
        .unwrap_or_else(|| panic!("emitted MIR contains no `{name}` function:\n{mir}"));
    let rest = &mir[start..];
    let end = rest
        .find("\n}\n")
        .unwrap_or_else(|| panic!("emitted MIR has no end for `{name}`:\n{rest}"));
    &rest[..end + 3]
}

fn assert_exactly_one(output: &str, needle: &str) {
    assert_eq!(
        output.matches(needle).count(),
        1,
        "expected exactly one `{needle}` report row:\n{output}"
    );
}

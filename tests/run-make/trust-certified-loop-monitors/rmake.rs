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

    let report = cmd(&trustc)
        .env("TRUST_MONITOR_REPORT", "1")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .arg("--test")
        .arg("--emit=mir")
        .arg("-Awarnings")
        .arg("loop_pass.rs")
        .arg("-o")
        .arg("loop.mir")
        .run()
        .stderr_utf8();

    assert_exactly_one(
        &report,
        "(LoopInvariant) is monitored: a kernel-certified runtime monitor exists",
    );
    assert_exactly_one(
        &report,
        "(Decreases) is measured: a kernel-certified scalar evaluator is bound to the exact E5 \
         measure",
    );

    let optimized_mir = rfs::read_to_string("loop.mir");
    assert!(
        optimized_mir.contains("fn monitored_loop"),
        "the emitted optimized MIR did not contain the loop under test:\n{optimized_mir}"
    );
    assert!(
        optimized_mir.contains("certified_monitor_check"),
        "certified E4/E5 clauses did not insert monitor calls:\n{optimized_mir}"
    );

    // Kernel certification is only a provisional evaluator. A non-self call
    // prevents exact function-recursion topology, and an optimized-away loop
    // has no authenticated header. Neither may be reported as executable.
    let unavailable = cmd(&trustc)
        .env("TRUST_MONITOR_REPORT", "1")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .arg("--crate-type=lib")
        .arg("--emit=mir")
        .arg("-Awarnings")
        .arg("placement_unavailable.rs")
        .arg("-o")
        .arg("placement-unavailable.mir")
        .run_fail()
        .stderr_utf8();
    assert_exactly_one(&unavailable, "(Decreases) is unmonitored");
    assert_exactly_one(&unavailable, "(LoopInvariant) is unmonitored");
    assert_exactly_one(
        &unavailable,
        "invalid authored loop contract provenance: e45.loop-source.no-mir-header",
    );
    assert!(
        !unavailable.contains("(Decreases) is measured")
            && !unavailable.contains("(LoopInvariant) is monitored"),
        "provisional evaluator certification escaped as placement-backed authority:\n{unavailable}"
    );

    // A contracted inner loop optimized away inside a surviving outer loop
    // must not reuse a residual one-sided source stamp to nominate the outer
    // natural header. The outer clauses retain their own exact authority while
    // the missing inner topology fails closed as an authored-spec error.
    let nested_unavailable = cmd(&trustc)
        .env("TRUST_MONITOR_REPORT", "1")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .arg("--crate-type=lib")
        .arg("--emit=mir")
        .arg("-Awarnings")
        .arg("nested_placement_unavailable.rs")
        .arg("-o")
        .arg("nested-placement-unavailable.mir")
        .run_fail()
        .stderr_utf8();
    assert_exactly_one(
        &nested_unavailable,
        "(LoopInvariant) is monitored: a kernel-certified runtime monitor exists",
    );
    assert_exactly_one(
        &nested_unavailable,
        "(Decreases) is measured: a kernel-certified scalar evaluator is bound to the exact E5 \
         measure",
    );
    assert_exactly_one(&nested_unavailable, "(LoopInvariant) is unmonitored");
    assert_exactly_one(
        &nested_unavailable,
        "invalid authored loop contract provenance: e45.loop-source.no-mir-header",
    );
    assert!(
        !nested_unavailable.contains("e45.loop-source.ambiguous-mir-header")
            && !nested_unavailable.contains("e45.loop-source.non-injective-mir-header"),
        "the optimized-away inner loop contaminated surviving outer-loop authority:\n\
         {nested_unavailable}"
    );

    compile_test(&trustc, "loop_pass.rs", "loop-pass");
    run(&bin_name("loop-pass"));

    compile_test(&trustc, "loop_invariant_fail.rs", "loop-invariant-fail");
    run_fail(&bin_name("loop-invariant-fail"))
        .assert_stderr_contains("kernel-certified Trust monitor failed");

    // The initial state satisfies the invariant. This control can fail only
    // if the same authenticated header is checked after a completed
    // iteration, rather than just on the entry edge.
    compile_test(
        &trustc,
        "loop_invariant_backedge_fail.rs",
        "loop-invariant-backedge-fail",
    );
    run_fail(&bin_name("loop-invariant-backedge-fail"))
        .assert_stderr_contains("kernel-certified Trust monitor failed");

    compile_test(&trustc, "loop_decrease_fail.rs", "loop-decrease-fail");
    run_fail(&bin_name("loop-decrease-fail"))
        .assert_stderr_contains("kernel-certified Trust monitor failed");

    // A two-latch loop needs independent checks on its explicit-continue and
    // fallthrough backedges. Each control makes only the named edge violate
    // descent, so neither edge can pass merely because the other is covered.
    compile_test(
        &trustc,
        "loop_continue_latch_fail.rs",
        "loop-continue-latch-fail",
    );
    run_fail(&bin_name("loop-continue-latch-fail"))
        .assert_stderr_contains("kernel-certified Trust monitor failed");
    compile_test(
        &trustc,
        "loop_fallthrough_latch_fail.rs",
        "loop-fallthrough-latch-fail",
    );
    run_fail(&bin_name("loop-fallthrough-latch-fail"))
        .assert_stderr_contains("kernel-certified Trust monitor failed");

    // Exercises two latches plus an inner-loop snapshot that must reset on
    // every outer iteration.
    compile_test(&trustc, "loop_multi_nested.rs", "loop-multi-nested");
    run(&bin_name("loop-multi-nested"));

    // Every compile_test invocation uses -Cdebuginfo=0. Keep two same-named,
    // same-typed locals live across the monitored loop so only compiler-owned
    // HIR-local provenance can select the inner binding.
    compile_test(&trustc, "loop_shadow.rs", "loop-shadow");
    run(&bin_name("loop-shadow"));
}

fn compile_test(trustc: &PathBuf, input: &str, output: &str) {
    cmd(trustc)
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .arg("--test")
        .arg("-Cdebuginfo=0")
        .arg("-Awarnings")
        .arg(input)
        .arg("-o")
        .arg(bin_name(output))
        .run();
}

fn assert_exactly_one(output: &str, needle: &str) {
    assert_eq!(
        output.matches(needle).count(),
        1,
        "expected exactly one `{needle}` monitor record:\n{output}"
    );
}

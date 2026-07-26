use super::*;

#[test]
fn run_bounded_captures_output_without_timeout() {
    let mut cmd = Command::new("/bin/sh");
    cmd.arg("-c").arg("echo out-marker; echo err-marker >&2");
    let run = run_bounded(cmd, Duration::from_secs(60)).unwrap();
    assert!(!run.timed_out);
    assert!(run.status.success());
    assert!(String::from_utf8_lossy(&run.stdout).contains("out-marker"));
    assert!(String::from_utf8_lossy(&run.stderr).contains("err-marker"));
}

#[test]
fn run_bounded_kills_wedged_process_group() {
    // A child that spawns its own grandchild and then blocks forever,
    // like lldb + debugserver + suspended debuggee. Both hold the stdout
    // pipe, so this also verifies the group kill releases the readers.
    let mut cmd = Command::new("/bin/sh");
    cmd.arg("-c").arg("sleep 300 & sleep 300");
    let start = Instant::now();
    let run = run_bounded(cmd, Duration::from_secs(2)).unwrap();
    assert!(run.timed_out);
    assert!(!run.status.success());
    // Bounded: far below the 300s the children wanted to sleep.
    assert!(start.elapsed() < Duration::from_secs(60));
}

#[test]
fn lldb_gate_rejects_binary_without_python_scripting() {
    // `/usr/bin/true` exits 0 but never evaluates the Python probe, like
    // an LLDB built without scripting support that ignores `-o script`.
    let err = lldb_can_run_batch_driver(Utf8Path::new("/usr/bin/true")).unwrap_err();
    assert!(err.contains("without evaluating Python"), "unexpected reason: {err}");

    // A binary that fails outright.
    let err = lldb_can_run_batch_driver(Utf8Path::new("/usr/bin/false")).unwrap_err();
    assert!(err.contains("without evaluating Python"), "unexpected reason: {err}");

    // A missing binary must gate, not panic.
    let err =
        lldb_can_run_batch_driver(Utf8Path::new("/nonexistent/lldb-does-not-exist"))
            .unwrap_err();
    assert!(err.contains("failed to spawn"), "unexpected reason: {err}");
}

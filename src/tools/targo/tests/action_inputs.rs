#![cfg(target_os = "macos")]

use std::fs;
use std::path::Path;
use std::process::{Command, Output};

fn command(root: &Path, state: &Path) -> Command {
    let executable = std::env::var_os("TARGO_ACTION_INPUT_TEST_BINARY")
        .unwrap_or_else(|| env!("CARGO_BIN_EXE_targo").into());
    let mut command = Command::new(executable);
    command
        .current_dir(root)
        .env_clear()
        .env("HOME", state)
        .env("CARGO_HOME", state.join("home"))
        .env("CARGO_TARGET_DIR", state.join("target"))
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env("RUSTC", std::env::var_os("RUSTC").unwrap())
        .env("__CARGO_TEST_CHANNEL_OVERRIDE_DO_NOT_USE_THIS", "nightly")
        .args([
            "--unverified",
            "build",
            "--offline",
            "--lib",
            "-Zbuild-dir-new-layout",
            "-Zfine-grain-locking",
            "--config",
            "build.action-sandbox=true",
            "--message-format=json",
        ]);
    command
}

fn build(root: &Path, state: &Path) -> Output {
    command(root, state).output().unwrap()
}

fn fresh(output: Output) -> bool {
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let artifacts: Vec<serde_json::Value> = String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| serde_json::from_str(line).ok())
        .filter(|row: &serde_json::Value| row["reason"] == "compiler-artifact")
        .collect();
    assert_eq!(artifacts.len(), 1);
    artifacts[0]["fresh"] == true
}

#[test]
fn a_new_module_candidate_is_not_hidden_by_old_dep_info() {
    let temp = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
    let root = temp.path().join("source");
    let state = temp.path().join("state");
    fs::create_dir_all(root.join("src")).unwrap();
    fs::create_dir(&state).unwrap();
    fs::write(
        root.join("Cargo.toml"),
        "[package]\nname='source_inputs'\nversion='0.0.0'\nedition='2021'\n[workspace]\n",
    )
    .unwrap();
    fs::write(root.join("src/lib.rs"), "pub mod selected;\n").unwrap();
    let selected = root.join("src/selected.rs");
    fs::write(&selected, "pub fn value() -> u32 { 42 }\n").unwrap();
    assert!(!fresh(build(&root, &state)));
    assert!(fresh(build(&root, &state)));
    filetime::set_file_mtime(&selected, filetime::FileTime::from_unix_time(1, 0)).unwrap();
    assert!(
        fresh(build(&root, &state)),
        "unchanged source bytes still reuse"
    );

    // No previously read file changes. This new directory member changes
    // module resolution and must cause the compiler to diagnose ambiguity.
    fs::create_dir(root.join("src/selected")).unwrap();
    fs::write(
        root.join("src/selected/mod.rs"),
        "pub fn value() -> u32 { 7 }\n",
    )
    .unwrap();
    let changed = build(&root, &state);
    assert!(
        !changed.status.success(),
        "stale cache hid an ambiguous module:\n{}",
        String::from_utf8_lossy(&changed.stdout)
    );
    assert!(
        String::from_utf8_lossy(&changed.stdout).contains("E0761"),
        "expected module ambiguity diagnostic:\n{}\n{}",
        String::from_utf8_lossy(&changed.stdout),
        String::from_utf8_lossy(&changed.stderr)
    );

    fs::remove_file(root.join("src/selected/mod.rs")).unwrap();
    fs::remove_dir(root.join("src/selected")).unwrap();
    fresh(build(&root, &state));
    assert!(fresh(build(&root, &state)));
}

#[test]
fn source_snapshot_is_rechecked_after_waiting_for_a_producer() {
    use std::io::{BufRead, BufReader, Read};
    use std::process::{Child, Stdio};
    use std::time::{Duration, Instant};
    use targo::util::{Filesystem, GlobalContext};

    struct OwnedChild(Child);
    impl Drop for OwnedChild {
        fn drop(&mut self) {
            if self.0.try_wait().ok().flatten().is_none() {
                unsafe {
                    libc::kill(-(self.0.id() as i32), libc::SIGKILL);
                }
                let _ = self.0.wait();
            }
        }
    }
    let temp = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
    let root = temp.path().join("source");
    let state = temp.path().join("state");
    fs::create_dir_all(root.join("src")).unwrap();
    fs::create_dir(&state).unwrap();
    fs::write(
        root.join("Cargo.toml"),
        "[package]\nname='source_inputs'\nversion='0.0.0'\nedition='2021'\n[workspace]\n",
    )
    .unwrap();
    fs::write(root.join("src/lib.rs"), "pub mod selected;\n").unwrap();
    fs::write(
        root.join("src/selected.rs"),
        "pub fn value() -> u32 { 42 }\n",
    )
    .unwrap();
    assert!(!fresh(build(&root, &state)));
    let unit_dir = fs::read_dir(state.join("target/debug/build/source_inputs"))
        .unwrap()
        .next()
        .unwrap()
        .unwrap()
        .path();
    let fingerprint = unit_dir.join("fingerprint/lib-source_inputs");
    let prior = fs::read(&fingerprint).unwrap();
    let gctx = GlobalContext::default().unwrap();
    let held = Filesystem::new(unit_dir.clone())
        .open_ro_shared(&unit_dir.join(".lock"), &gctx, "source input barrier")
        .unwrap();
    fs::remove_file(&fingerprint).unwrap();
    let mut cmd = command(&root, &state);
    use std::os::unix::process::CommandExt;
    cmd.process_group(0)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = OwnedChild(cmd.spawn().unwrap());
    let mut stdout = child.0.stdout.take().unwrap();
    let stderr = child.0.stderr.take().unwrap();
    let output = std::thread::spawn(move || {
        let mut bytes = Vec::new();
        stdout.read_to_end(&mut bytes).unwrap();
        bytes
    });
    let (send, recv) = std::sync::mpsc::channel();
    let error = std::thread::spawn(move || {
        let mut text = String::new();
        for line in BufReader::new(stderr).lines() {
            let line = line.unwrap();
            if line.contains("Compiling source_inputs") {
                let _ = send.send(());
            }
            text.push_str(&line);
            text.push('\n');
        }
        text
    });
    recv.recv_timeout(Duration::from_secs(60))
        .expect("build reached its unit lock");
    fs::create_dir(root.join("src/selected")).unwrap();
    fs::write(
        root.join("src/selected/mod.rs"),
        "pub fn value() -> u32 { 7 }\n",
    )
    .unwrap();
    // Simulate a producer publishing the old artifact while this waiter still
    // holds its earlier source snapshot. Neither can authorize a fresh hit.
    fs::write(&fingerprint, prior).unwrap();
    drop(held);
    let deadline = Instant::now() + Duration::from_secs(60);
    let status = loop {
        if let Some(status) = child.0.try_wait().unwrap() {
            break status;
        }
        assert!(
            Instant::now() < deadline,
            "source-input waiter did not terminate"
        );
        std::thread::sleep(Duration::from_millis(10));
    };
    let stdout = output.join().unwrap();
    let stderr = error.join().unwrap();
    assert!(!status.success(), "{}", String::from_utf8_lossy(&stdout));
    assert!(stderr.contains("source inputs changed"), "{stderr}");
}

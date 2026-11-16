#![cfg(any(target_os = "linux", target_os = "macos"))]

use std::fs;
use std::io::Read;
use std::path::Path;
use std::process::{Command, Output};
use std::time::{Duration, Instant};

// Trust: shared native fixture accounting covers both compiler-wrapper work
// and actual test bodies. The directory transaction serializes observations;
// it neither admits work nor substitutes for Targo's real jobserver tokens.
const GRAPH_TRACKING: &str = r#"
fn control() -> std::path::PathBuf {
    std::env::var_os("TEST_GRAPH_CONTROL").unwrap().into()
}
fn wait(name: &str) {
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(25);
    while !control().join(name).exists() {
        assert!(std::time::Instant::now() < deadline, "native graph prerequisite timed out: {name}");
        std::thread::sleep(std::time::Duration::from_millis(5));
    }
}
fn change(delta: i32) {
    let root = control();
    let lock = root.join("accounting-lock");
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(25);
    loop {
        match std::fs::create_dir(&lock) {
            Ok(()) => break,
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
                assert!(std::time::Instant::now() < deadline, "accounting lock timed out");
                std::thread::sleep(std::time::Duration::from_millis(1));
            }
            Err(error) => panic!("accounting: {error}"),
        }
    }
    let read = |name| std::fs::read_to_string(root.join(name)).unwrap_or_else(|_| "0".into()).parse::<i32>().unwrap();
    let active = read("active") + delta;
    let peak = read("peak").max(active);
    std::fs::write(root.join("active"), active.to_string()).unwrap();
    std::fs::write(root.join("peak"), peak.to_string()).unwrap();
    std::fs::remove_dir(lock).unwrap();
    assert!((0..=2).contains(&active), "joint compiler/test admission exceeded two slots: {active}");
}
struct Active;
impl Active { fn enter() -> Self { change(1); Self } }
impl Drop for Active { fn drop(&mut self) { change(-1); } }
"#;

// Trust: under x.py the test process's RUSTC is bootstrap's wrapper, which
// needs bootstrap's environment; `env_clear` drops it. Bootstrap names a
// self-contained fixture shim directory for exactly this.
fn fixture_rustc() -> std::ffi::OsString {
    std::env::var_os("TEST_TRUST_SHIM_DIR")
        .map(|dir| Path::new(&dir).join("rustc").into_os_string())
        .or_else(|| std::env::var_os("RUSTC"))
        .expect("test requires an explicit compiler or bootstrap fixture shim")
}

// Trust: rustc's parallel frontend, which Targo enables with `-Zthreads`, can
// exit still holding a jobserver token, and a pipe never gets it back
// (RUSTC-FRONTEND-TOKEN-LEAK-1 in docs/DECISION_QUEUE.md). These fixtures
// count the pool's tokens exactly, so they compile with a serial frontend; an
// explicit `-Zthreads` replaces the one Targo would add.
const SERIAL_FRONTEND: &str = "-Zthreads=1";

// Trust: Targo reuses a linked output only where the compiler reported which
// native tools it read (`-Ztrust-tool-inputs`, tool_inputs.rs) or the linker is
// configured; a compiler without the flag gives a default-linker harness no
// cache authority, so a warm run must link it again. The 0.13.0 seed predates
// the flag. Both answers are asserted, each against the compiler that ran.
fn compiler_reports_tool_inputs() -> bool {
    Command::new(fixture_rustc())
        .args(["-Ztrust-tool-inputs", "--print=cfg"])
        .output()
        .unwrap()
        .status
        .success()
}

fn graph_driver() -> std::ffi::OsString {
    std::env::var_os("TRUST_TEST_ACTION_TARGO")
        .unwrap_or_else(|| env!("CARGO_BIN_EXE_targo").into())
}

fn graph_command(root: &Path) -> Command {
    let mut command = Command::new(graph_driver());
    command
        .current_dir(root)
        .env_clear()
        .env("HOME", root)
        .env("CARGO_HOME", root.join("home"))
        .env("CARGO_TARGET_DIR", root.join("target.noindex"))
        .env("RUSTC", fixture_rustc())
        .env("RUSTFLAGS", SERIAL_FRONTEND)
        .env("PATH", std::env::var_os("PATH").unwrap());
    // Trust: on macOS the compiler finds the SDK with `xcrun` unless SDKROOT
    // names it, and that discovery is outside the tool inputs it reports: a
    // link that depended on it is reported `unavailable` and linked again
    // (rustc_codegen_ssa back/apple.rs, get_sdk_root). `env_clear` dropped
    // the caller's SDKROOT, so the fixture names the SDK itself; without this
    // the reuse these tests assert never happens on macOS.
    if let Some(sdk) = apple_sdk_root() {
        command.env("SDKROOT", sdk);
    }
    command
}

// Trust: the SDK the system's `xcrun` selects, as an absolute directory; None
// off macOS.
fn apple_sdk_root() -> Option<std::ffi::OsString> {
    if !cfg!(target_os = "macos") {
        return None;
    }
    let output = Command::new("/usr/bin/xcrun")
        .arg("--show-sdk-path")
        .output()
        .expect("xcrun names the SDK");
    assert!(output.status.success(), "xcrun --show-sdk-path failed");
    let path = String::from_utf8(output.stdout).unwrap().trim().to_owned();
    assert!(Path::new(&path).is_dir(), "xcrun named no SDK directory: {path}");
    Some(path.into())
}

// Trust: the fixture's compiler, a shim that execs the real one named by
// GRAPH_REAL_RUSTC. It is set as RUSTC, not as RUSTC_WRAPPER: under a wrapper
// Targo takes no tool-input facts at all (validate_tool_input_profile requires
// `wrapper.is_none()`), so every linked harness would be linked again on a
// warm run whatever the compiler reports, and the reuse the warm half of the
// test asserts could never be observed.
fn compile_graph_wrapper(root: &Path) -> std::path::PathBuf {
    let source = root.join("wrapper");
    fs::create_dir_all(source.join("src")).unwrap();
    fs::write(
        source.join("Cargo.toml"),
        "[package]\nname='graph_wrapper'\nversion='0.0.0'\nedition='2024'\n[workspace]\n",
    )
    .unwrap();
    let body = r#"
fn main() {
    let compiler = std::env::var_os("GRAPH_REAL_RUSTC").unwrap();
    let words = std::env::args_os().skip(1).collect::<Vec<_>>();
    let name = words.windows(2).find(|pair| pair[0] == "--crate-name")
        .and_then(|pair| pair[1].to_str());
    let tracked = matches!(name, Some("graph_a" | "graph_b"));
    let guard = tracked.then(Active::enter);
    if name == Some("graph_b") {
        std::fs::write(control().join("b.compiling"), b"actual compiler job").unwrap();
        // A phase barrier cannot satisfy this: the only producer of this
        // marker is the already-linked independent A test body.
        wait("a.ran");
    }
    let status = std::process::Command::new(compiler).args(words).status().unwrap();
    drop(guard);
    std::process::exit(status.code().unwrap_or(101));
}
"#;
    fs::write(
        source.join("src/main.rs"),
        format!("{GRAPH_TRACKING}\n{body}"),
    )
    .unwrap();
    let output = graph_command(&source)
        .args([
            "--unverified",
            "build",
            "--offline",
            "--message-format=json",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
        .find(|row| {
            row["reason"] == "compiler-artifact" && row["target"]["name"] == "graph_wrapper"
        })
        .and_then(|row| row["executable"].as_str().map(std::path::PathBuf::from))
        .unwrap()
}

#[test]
fn native_action_graph_overlaps_compile_and_test_and_reexecutes_warm_harnesses() {
    let base = std::env::current_dir()
        .unwrap()
        .join(".ubd/native-action-graph.noindex");
    fs::create_dir_all(&base).unwrap();
    let world = tempfile::tempdir_in(base).unwrap().keep();
    let root = world.as_path();
    eprintln!(
        "native action graph qualification inputs: {}",
        root.display()
    );
    let wrapper = compile_graph_wrapper(root);
    fs::write(
        root.join("Cargo.toml"),
        "[workspace]\nmembers=['a','b']\nresolver='2'\n",
    )
    .unwrap();
    for name in ["a", "b"] {
        fs::create_dir_all(root.join(name).join("src")).unwrap();
        fs::write(
            root.join(name).join("Cargo.toml"),
            format!("[package]\nname='graph_{name}'\nversion='0.0.0'\nedition='2024'\n"),
        )
        .unwrap();
        let body = if name == "a" {
            r#"#[test] fn run() {
                let _active = Active::enter();
                assert_eq!(std::env::var("RUST_TEST_THREADS").unwrap(), "1");
                std::fs::write(control().join("a.ran"), b"actual A test").unwrap();
                wait("b.ran");
            }"#
        } else {
            r#"#[test] fn run() {
                let _active = Active::enter();
                assert_eq!(std::env::var("RUST_TEST_THREADS").unwrap(), "1");
                std::fs::write(control().join("b.ran"), b"actual B test").unwrap();
                wait("a.ran");
            }"#
        };
        fs::write(
            root.join(name).join("src/lib.rs"),
            format!("{GRAPH_TRACKING}\n{body}"),
        )
        .unwrap();
    }
    let reuses_linked = compiler_reports_tool_inputs();
    for warm in [false, true] {
        for marker in ["a.ran", "b.ran", "b.compiling", "active", "peak"] {
            let _ = fs::remove_file(root.join(marker));
        }
        let output = graph_command(root)
            .env("RUSTC", &wrapper)
            .env("GRAPH_REAL_RUSTC", fixture_rustc())
            .env("TEST_GRAPH_CONTROL", root)
            .args([
                "--unverified",
                "test",
                "--offline",
                "--workspace",
                "--lib",
                "-j2",
                "--config",
                "build.test-jobs=2",
                "--message-format=json",
            ])
            .output()
            .unwrap();
        fs::write(
            root.join(if warm { "warm.stdout" } else { "cold.stdout" }),
            &output.stdout,
        )
        .unwrap();
        fs::write(
            root.join(if warm { "warm.stderr" } else { "cold.stderr" }),
            &output.stderr,
        )
        .unwrap();
        let rows = events(&output);
        assert!(
            output.status.success(),
            "warm={warm}\n{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            rows.iter().filter(|row| row["state"] == "passed").count(),
            2
        );
        assert_eq!(fs::read_to_string(root.join("active")).unwrap(), "0");
        assert_eq!(fs::read_to_string(root.join("peak")).unwrap(), "2");
        let reused = warm && reuses_linked;
        assert_eq!(
            root.join("b.compiling").exists(),
            !reused,
            "warm={warm}: a harness is compiled again exactly where the compiler \
             reported no tool inputs (reported: {reuses_linked})"
        );
        let artifacts = String::from_utf8_lossy(&output.stdout)
            .lines()
            .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
            .filter(|row| row["reason"] == "compiler-artifact")
            .collect::<Vec<_>>();
        assert_eq!(artifacts.len(), 2);
        assert!(artifacts.iter().all(|row| row["fresh"] == reused));
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn native_action_graph_retains_runtime_binary_and_build_script_environment() {
    let root = managed_fixture();
    fs::write(
        root.path().join("Cargo.toml"),
        "[package]\nname='runtime_graph'\nversion='0.0.0'\nedition='2024'\n[workspace]\n",
    )
    .unwrap();
    fs::remove_file(root.path().join("src/lib.rs")).unwrap();
    fs::create_dir(root.path().join("tests")).unwrap();
    fs::write(root.path().join("build.rs"), r#"fn main() {
        println!("cargo::rustc-env=RUNTIME_VALUE=from-build-script");
        std::fs::write(std::path::Path::new(&std::env::var("OUT_DIR").unwrap()).join("runtime-data"), b"built").unwrap();
    }"#).unwrap();
    fs::write(
        root.path().join("src/main.rs"),
        "fn main() { print!(\"runtime artifact\"); }\n",
    )
    .unwrap();
    fs::write(root.path().join("tests/runtime.rs"), r#"
        #[test] fn runtime_inputs() {
            assert_eq!(std::env::var("RUNTIME_VALUE").unwrap(), "from-build-script");
            // Cargo exposes OUT_DIR to the compiler; ordinary target processes
            // deliberately do not inherit it as an ambient runtime variable.
            assert!(std::env::var_os("OUT_DIR").is_none());
            let out = std::path::PathBuf::from(env!("OUT_DIR"));
            assert_eq!(std::fs::read(out.join("runtime-data")).unwrap(), b"built");
            let output = std::process::Command::new(env!("CARGO_BIN_EXE_runtime_graph")).output().unwrap();
            assert!(output.status.success());
            assert_eq!(output.stdout, b"runtime artifact");
        }
    "#).unwrap();
    successful(
        native_command(root.path())
            .args(["--test", "runtime", "--config", "build.test-jobs=2"])
            .output()
            .unwrap(),
    );
}

#[test]
fn native_action_graph_nested_same_target_build_releases_compile_leases() {
    let root = managed_fixture();
    fs::remove_file(root.path().join("src/lib.rs")).unwrap();
    fs::create_dir(root.path().join("tests")).unwrap();
    fs::write(root.path().join("tests/nested.rs"), r#"
        #[test] fn nested_build() {
            let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
            let mut command = std::process::Command::new(std::env::var_os("NESTED_TARGO").unwrap());
            command.arg("--unverified");
            if std::env::var_os("NESTED_FINE").is_some() {
                command.args(["-Zfine-grain-locking", "-Zbuild-dir-new-layout"]);
            }
            command.args(["test", "--offline", "--test", "nested", "--no-run",
                "--config", "build.test-jobs=1", "--message-format=json"])
                .stdout(std::fs::File::create(root.join("nested.stdout")).unwrap())
                .stderr(std::fs::File::create(root.join("nested.stderr")).unwrap());
            let mut child = command.spawn().unwrap();
            let deadline = std::time::Instant::now() + std::time::Duration::from_secs(45);
            let status = loop {
                if let Some(status) = child.try_wait().unwrap() { break status; }
                if std::time::Instant::now() >= deadline {
                    let _ = child.kill();
                    let _ = child.wait();
                    panic!("nested build waited on this test's parent compile leases");
                }
                std::thread::sleep(std::time::Duration::from_millis(10));
            };
            assert!(status.success(), "{}", std::fs::read_to_string(root.join("nested.stderr")).unwrap());
            std::fs::write(root.join("nested.returned"), b"same target nested build completed").unwrap();
        }
    "#).unwrap();
    let reuses_linked = compiler_reports_tool_inputs();
    for fine in [false, true] {
        for _warm in [false, true] {
            let _ = fs::remove_file(root.path().join("nested.returned"));
            let mut command = graph_command(root.path());
            command.arg("--unverified");
            if fine {
                command
                    .args(["-Zfine-grain-locking", "-Zbuild-dir-new-layout"])
                    .env("NESTED_FINE", "1");
            }
            let output = command
                .env("NESTED_TARGO", graph_driver())
                .env(
                    "CARGO_TARGET_DIR",
                    root.path().join(if fine {
                        "fine.noindex"
                    } else {
                        "default.noindex"
                    }),
                )
                .args([
                    "test",
                    "--offline",
                    "--test",
                    "nested",
                    "-j2",
                    "--config",
                    "build.test-jobs=2",
                ])
                .output()
                .unwrap();
            successful(output);
            assert!(root.path().join("nested.returned").exists());
            let rows = fs::read_to_string(root.path().join("nested.stdout"))
                .unwrap()
                .lines()
                .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
                .filter(|row| row["reason"] == "compiler-artifact")
                .collect::<Vec<_>>();
            assert_eq!(rows.len(), 1);
            assert_eq!(
                rows[0]["fresh"], reuses_linked,
                "a nested request reuses the parent's compiled harness exactly \
                 where the compiler reported its tool inputs"
            );
        }
    }
}

#[test]
fn native_action_graph_denied_transitive_warnings_block_tests_under_keep_going() {
    denied_transitive_warnings_block_tests(&["-j2", "--config", "build.test-jobs=2"]);
    // Trust: a weighted harness is blocked by a failed prerequisite exactly
    // as a weight-one harness is.
    denied_transitive_warnings_block_tests(&[
        "-j3",
        "--config",
        "build.test-jobs=3",
        "--config",
        "build.test-weight=2",
    ]);
}

fn denied_transitive_warnings_block_tests(admission: &[&str]) {
    let root = managed_fixture();
    fs::remove_file(root.path().join("src/lib.rs")).unwrap();
    fs::write(
        root.path().join("Cargo.toml"),
        "[workspace]\nmembers=['dep','middle','app']\nresolver='2'\n",
    )
    .unwrap();
    for name in ["dep", "middle", "app"] {
        fs::create_dir_all(root.path().join(name).join("src")).unwrap();
        let dependencies = match name {
            "middle" => "[dependencies]\ndep={path='../dep'}\n",
            "app" => "[dependencies]\nmiddle={path='../middle'}\n",
            _ => "",
        };
        fs::write(
            root.path().join(name).join("Cargo.toml"),
            format!("[package]\nname='{name}'\nversion='0.0.0'\nedition='2024'\n{dependencies}"),
        )
        .unwrap();
    }
    fs::write(
        root.path().join("dep/src/lib.rs"),
        "fn unused_warning() {}\npub fn value() -> u32 { 1 }\n",
    )
    .unwrap();
    fs::write(
        root.path().join("middle/src/lib.rs"),
        "pub fn value() -> u32 { dep::value() }\n",
    )
    .unwrap();
    fs::write(
        root.path().join("app/src/lib.rs"),
        r#"
        #[test] fn must_stay_blocked() {
            assert_eq!(middle::value(), 1);
            std::fs::write(concat!(env!("CARGO_MANIFEST_DIR"), "/ran"), b"bad").unwrap();
        }
    "#,
    )
    .unwrap();
    let output = graph_command(root.path())
        .args([
            "--unverified",
            "test",
            "--offline",
            "--workspace",
            "--lib",
            "--keep-going",
            "--config",
            "build.warnings=\"deny\"",
            "--message-format=json",
        ])
        .args(admission)
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(
        !root.path().join("app/ran").exists(),
        "a transitive failed prerequisite admitted user code"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("warnings are denied"), "{stderr}");
    assert!(
        !stderr.contains("compilation finalization previously failed"),
        "{stderr}"
    );
    assert!(
        events(&output)
            .iter()
            .any(|row| row["target"] == "app" && row["state"] == "blocked")
    );
}

// Trust: direct native CLI controls for the admitted standard-harness ceiling.
const MANAGED_LIBTEST: &str = r#"
use std::sync::atomic::{AtomicUsize, Ordering};
static ACTIVE: AtomicUsize = AtomicUsize::new(0);
fn work() {
    let limit: usize = std::env::var("EXPECT_WORKERS").unwrap().parse().unwrap();
    let expected = std::env::var("EXPECT_THREAD_ENV").unwrap();
    assert_eq!(std::env::var("RUST_TEST_THREADS").unwrap(), expected);
    let active = ACTIVE.fetch_add(1, Ordering::SeqCst) + 1;
    assert!(active <= limit, "{active} workers exceeded {limit}");
    std::fs::write(concat!(env!("CARGO_MANIFEST_DIR"), "/ran"), b"actual test body").unwrap();
    // Deliberate fixture work exposes overlapping harness workers; there is no
    // assertion about how fast the host schedules them.
    std::thread::sleep(std::time::Duration::from_millis(20));
    ACTIVE.fetch_sub(1, Ordering::SeqCst);
}
#[test] fn a() { work(); }
#[test] fn b() { work(); }
#[test] fn c() { work(); }
#[test] fn d() { work(); }
"#;

fn managed_fixture() -> tempfile::TempDir {
    let base = std::env::current_dir()
        .unwrap()
        .join(".ubd/managed-test-budget.noindex");
    fs::create_dir_all(&base).unwrap();
    let root = tempfile::tempdir_in(base).unwrap();
    fs::create_dir(root.path().join("src")).unwrap();
    fs::write(
        root.path().join("Cargo.toml"),
        "[package]\nname='managed_workers'\nversion='0.0.0'\nedition='2024'\n[workspace]\n",
    )
    .unwrap();
    fs::write(root.path().join("src/lib.rs"), MANAGED_LIBTEST).unwrap();
    root
}

fn native_command(root: &Path) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_targo"));
    command
        .current_dir(root)
        .env_clear()
        .env("HOME", root)
        .env("CARGO_HOME", root.join("home"))
        .env("CARGO_TARGET_DIR", root.join("target.noindex"))
        .env("RUSTC", fixture_rustc())
        .env("PATH", std::env::var_os("PATH").unwrap())
        .args(["--unverified", "test", "--offline", "-j", "2"]);
    command
}

fn admitted_command(root: &Path, limit: usize) -> Command {
    let mut command = native_command(root);
    command
        .env("BUILD_SLOT_HELD", "1")
        .env("CARGO_BUILD_JOBS", limit.to_string())
        .env("EXPECT_WORKERS", limit.to_string())
        .env("EXPECT_THREAD_ENV", limit.to_string());
    command
}

fn successful(output: Output) {
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn admitted_standard_harness_bounds_workers_and_preserves_smaller_preferences() {
    let root = managed_fixture();
    successful(
        admitted_command(root.path(), 2)
            .arg("--lib")
            .output()
            .unwrap(),
    );
    successful(
        admitted_command(root.path(), 2)
            .arg("--lib")
            .env("RUST_TEST_THREADS", "1")
            .env("EXPECT_WORKERS", "1")
            .env("EXPECT_THREAD_ENV", "1")
            .output()
            .unwrap(),
    );
    successful(
        admitted_command(root.path(), 2)
            .arg("--lib")
            .env("RUST_TEST_THREADS", "8")
            .output()
            .unwrap(),
    );

    // A build-script target environment has precedence over ambient defaults.
    fs::write(
        root.path().join("build.rs"),
        "fn main() { println!(\"cargo::rustc-env=RUST_TEST_THREADS=1\"); }\n",
    )
    .unwrap();
    successful(
        admitted_command(root.path(), 2)
            .arg("--lib")
            .env("RUST_TEST_THREADS", "8")
            .env("EXPECT_WORKERS", "1")
            .env("EXPECT_THREAD_ENV", "1")
            .output()
            .unwrap(),
    );
}

#[test]
fn admitted_libtest_flags_are_bounded_without_parsing_opaque_filter_values() {
    let root = managed_fixture();
    for args in [vec!["--test-threads=1"], vec!["--test-threads", "1"]] {
        successful(
            admitted_command(root.path(), 2)
                .args(["--lib", "--"])
                .args(args)
                .env("EXPECT_WORKERS", "1")
                .output()
                .unwrap(),
        );
    }
    successful(
        admitted_command(root.path(), 2)
            .args(["--lib", "--", "--skip", "--test-threads=99"])
            .output()
            .unwrap(),
    );
    for args in [vec!["--test-threads=3"], vec!["--test-threads", "3"]] {
        fs::remove_file(root.path().join("ran")).unwrap();
        let output = admitted_command(root.path(), 2)
            .args(["--lib", "--"])
            .args(args)
            .output()
            .unwrap();
        assert!(!output.status.success());
        assert!(
            String::from_utf8_lossy(&output.stderr).contains("exceeding the admitted ceiling 2")
        );
        assert!(
            !root.path().join("ran").exists(),
            "refused flag launched a test body"
        );
        // Restore a marker so the next case also proves its own removal.
        fs::write(root.path().join("ran"), b"case boundary").unwrap();
    }
}

#[test]
fn malformed_managed_admission_refuses_before_a_standard_test_body() {
    let root = managed_fixture();
    for held in ["", "0", "true", " 1", "1 "] {
        let output = admitted_command(root.path(), 2)
            .arg("--lib")
            .env("BUILD_SLOT_HELD", held)
            .output()
            .unwrap();
        assert!(!output.status.success());
        assert!(String::from_utf8_lossy(&output.stderr).contains("BUILD_SLOT_HELD=1"));
        assert!(!root.path().join("ran").exists());
    }
    for jobs in [
        None,
        Some(""),
        Some("0"),
        Some("-1"),
        Some("+2"),
        Some(" 2"),
        Some("2 "),
        Some("999999999999999999999999999999999999999999"),
    ] {
        let mut command = admitted_command(root.path(), 2);
        command.arg("--lib");
        if let Some(jobs) = jobs {
            command.env("CARGO_BUILD_JOBS", jobs);
        } else {
            command.env_remove("CARGO_BUILD_JOBS");
        }
        let output = command.output().unwrap();
        assert!(!output.status.success());
        assert!(String::from_utf8_lossy(&output.stderr).contains("CARGO_BUILD_JOBS"));
        assert!(!root.path().join("ran").exists());
    }
    for preference in ["", "0", "-1", "not-a-count"] {
        let output = admitted_command(root.path(), 2)
            .arg("--lib")
            .env("RUST_TEST_THREADS", preference)
            .output()
            .unwrap();
        assert!(!output.status.success());
        assert!(String::from_utf8_lossy(&output.stderr).contains("RUST_TEST_THREADS"));
        assert!(!root.path().join("ran").exists());
    }
}

#[test]
fn unmanaged_and_custom_harness_execution_keep_their_existing_inputs() {
    let root = managed_fixture();
    successful(
        native_command(root.path())
            .arg("--lib")
            .env("CARGO_BUILD_JOBS", "2")
            .env("RUST_TEST_THREADS", "3")
            .env("EXPECT_WORKERS", "3")
            .env("EXPECT_THREAD_ENV", "3")
            .output()
            .unwrap(),
    );
    fs::remove_file(root.path().join("src/lib.rs")).unwrap();
    fs::create_dir(root.path().join("tests")).unwrap();
    fs::write(root.path().join("Cargo.toml"),
        "[package]\nname='managed_workers'\nversion='0.0.0'\nedition='2024'\n[workspace]\n[[test]]\nname='custom'\nharness=false\n").unwrap();
    fs::write(
        root.path().join("tests/custom.rs"),
        r#"
fn main() {
    assert_eq!(std::env::args().skip(1).collect::<Vec<_>>(), ["--test-threads=99"]);
    assert_eq!(std::env::var("RUST_TEST_THREADS").unwrap(), "9");
    println!("custom-inputs-preserved");
}
"#,
    )
    .unwrap();
    successful(
        admitted_command(root.path(), 1)
            .env("RUST_TEST_THREADS", "9")
            .args(["--test", "custom", "--", "--test-threads=99"])
            .output()
            .unwrap(),
    );
}

#[test]
fn admitted_parallel_scheduler_caps_processes_and_keeps_one_thread_per_token() {
    let root = managed_fixture();
    fs::create_dir(root.path().join("tests")).unwrap();
    for name in ["a", "b"] {
        fs::write(
            root.path().join(format!("tests/{name}.rs")),
            format!(
                r#"
#[test] fn run() {{
    assert_eq!(std::env::var("RUST_TEST_THREADS").unwrap(), "1");
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let held = root.join("active-harness");
    let _guard = std::fs::OpenOptions::new().write(true).create_new(true).open(&held)
        .expect("admission allowed concurrent test bodies");
    std::thread::sleep(std::time::Duration::from_millis(100));
    std::fs::write(root.join("{name}.finished"), b"actual completion").unwrap();
    std::fs::remove_file(held).unwrap();
}}
"#
            ),
        )
        .unwrap();
    }
    let output = admitted_command(root.path(), 1)
        .args([
            "--test",
            "a",
            "--test",
            "b",
            "--config",
            "build.test-jobs=2",
            "--message-format=json",
        ])
        .output()
        .unwrap();
    let rows = events(&output);
    successful(output);
    // Readiness follows real compiler completion; either independent target
    // may be first. A single admitted slot must retire before its next start.
    let mut active = 0;
    for row in &rows {
        match row["state"].as_str() {
            Some("running") => {
                active += 1;
                assert_eq!(active, 1);
            }
            Some("passed") => {
                assert_eq!(active, 1);
                active -= 1;
            }
            _ => {}
        }
    }
    assert_eq!(active, 0);
    assert_eq!(
        rows.iter().filter(|row| row["state"] == "passed").count(),
        2
    );
    assert_eq!(
        rows.iter().filter(|row| row["state"] == "running").count(),
        2
    );
    for name in ["a", "b"] {
        assert!(root.path().join(format!("{name}.finished")).exists());
    }
}

// Trust: failed worlds survive, and one controller owns waiting and cancellation.
struct LiveExecution {
    world: Option<tempfile::TempDir>,
    child: Option<std::process::Child>,
    passed: bool,
}

impl Drop for LiveExecution {
    fn drop(&mut self) {
        let root = self.world.as_ref().expect("fixture world").path();
        if let Some(child) = self.child.as_mut() {
            let _ = fs::write(root.join("abort-fixture"), b"parent cleanup");
            let _ = fs::write(root.join("release-b"), b"parent cleanup");
            if matches!(child.try_wait(), Ok(None)) {
                // SAFETY: this controller owns the still-unreaped direct child;
                // its PID cannot be reused before our sole wait owner reaps it.
                unsafe { libc::kill(child.id() as libc::pid_t, libc::SIGTERM) };
                let deadline = Instant::now() + Duration::from_secs(60);
                while matches!(child.try_wait(), Ok(None)) {
                    if Instant::now() >= deadline {
                        let _ = child.kill();
                        let _ = child.wait();
                        break;
                    }
                    std::thread::sleep(Duration::from_millis(10));
                }
            }
        }
        if !self.passed {
            eprintln!(
                "kept failed live-execution world: {}",
                self.world.take().unwrap().keep().display()
            );
        }
    }
}

#[test]
fn terminal_events_arrive_while_an_independent_peer_is_still_running() -> anyhow::Result<()> {
    for first_fails in [false, true] {
        live_terminal_before_peer_release(first_fails)?;
    }
    Ok(())
}

fn live_terminal_before_peer_release(first_fails: bool) -> anyhow::Result<()> {
    let base = std::env::current_dir()?.join(".ubd/live-test-events.noindex");
    fs::create_dir_all(&base)?;
    let world = tempfile::tempdir_in(base)?;
    let root = world.path().to_path_buf();
    let mut execution = LiveExecution {
        world: Some(world),
        child: None,
        passed: false,
    };
    fs::create_dir(root.join("tests"))?;
    fs::write(
        root.join("Cargo.toml"),
        "[package]\nname='live_execution'\nversion='0.0.0'\nedition='2024'\n[workspace]\n",
    )?;
    let wait = r#"
fn wait(name: &str) {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(60);
    while !root.join(name).exists() {
        assert!(!root.join("abort-fixture").exists(), "fixture parent aborted");
        assert!(std::time::Instant::now() < deadline, "fixture release did not arrive");
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
}
"#;
    fs::write(
        root.join("tests/a.rs"),
        format!(
            "{wait}\n{}",
            r#"
#[test] fn run() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    std::fs::write(root.join("a.started"), b"actual A execution").unwrap();
    wait("b.started");
    std::fs::write(root.join("a.finished"), b"actual A completion").unwrap();
    assert!(std::env::var_os("FAIL_FIRST").is_none(), "intentional first harness failure");
}
"#
        ),
    )?;
    fs::write(
        root.join("tests/b.rs"),
        format!(
            "{wait}\n{}",
            r#"
#[test] fn run() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    std::fs::write(root.join("b.started"), b"actual B execution").unwrap();
    wait("release-b");
    assert!(!root.join("abort-fixture").exists(), "fixture parent aborted");
    std::fs::write(root.join("b.finished"), b"actual B completion").unwrap();
}
"#
        ),
    )?;
    let mut cmd = command(&root, 2);
    cmd.env("CARGO_TARGET_DIR", root.join("target.noindex"))
        .stdout(fs::File::create(root.join("stdout.log"))?)
        .stderr(fs::File::create(root.join("stderr.log"))?);
    if first_fails {
        cmd.arg("--no-fail-fast").env("FAIL_FIRST", "1");
    }
    execution.child = Some(cmd.spawn()?);
    let mut stdout = fs::File::open(root.join("stdout.log"))?;
    let mut pending = Vec::new();
    let mut terminals = std::collections::BTreeMap::new();
    let mut status = None;
    let deadline = Instant::now() + Duration::from_secs(60);
    loop {
        anyhow::ensure!(
            stdout.metadata()?.len() <= 16 * 1024 * 1024,
            "unexpected fixture output volume"
        );
        anyhow::ensure!(
            fs::metadata(root.join("stderr.log"))?.len() <= 16 * 1024 * 1024,
            "unexpected fixture stderr volume"
        );
        (&mut stdout)
            .take(1024 * 1024 + 1)
            .read_to_end(&mut pending)?;
        while let Some(end) = pending.iter().position(|&byte| byte == b'\n') {
            let line: Vec<_> = pending.drain(..=end).collect();
            let Ok(row) = serde_json::from_slice::<serde_json::Value>(&line) else {
                continue;
            };
            if row["reason"] != "test-execution"
                || !matches!(row["state"].as_str(), Some("passed" | "failed"))
            {
                continue;
            }
            let target = row["target"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing target"))?
                .to_owned();
            anyhow::ensure!(
                row["schema"] == "targo.test-execution.v2" && row["total"] == 2,
                "wrong execution inventory: {row}"
            );
            anyhow::ensure!(
                row["elapsed_ms"].as_u64().is_some(),
                "missing execution time"
            );
            let index = row["index"]
                .as_u64()
                .ok_or_else(|| anyhow::anyhow!("missing index"))?;
            anyhow::ensure!(index < 2, "foreign execution index");
            let artifact = row["prerequisite_artifact"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing artifact"))?;
            anyhow::ensure!(
                Path::new(artifact).starts_with(root.join("target.noindex"))
                    && Path::new(artifact).is_file(),
                "foreign prerequisite artifact"
            );
            anyhow::ensure!(
                terminals.insert(target.clone(), row.clone()).is_none(),
                "duplicate terminal record for {target}"
            );
            if target == "a" {
                anyhow::ensure!(
                    row["state"] == if first_fails { "failed" } else { "passed" },
                    "wrong first outcome"
                );
                anyhow::ensure!(
                    fs::read(root.join("a.finished"))? == b"actual A completion"
                        && fs::read(root.join("b.started"))? == b"actual B execution",
                    "missing actual execution acknowledgements"
                );
                anyhow::ensure!(
                    !root.join("release-b").exists() && !root.join("b.finished").exists(),
                    "terminal event arrived only after the peer finished"
                );
                fs::write(root.join("release-b"), b"first terminal event observed")?;
            }
        }
        anyhow::ensure!(
            pending.len() <= 1024 * 1024,
            "oversized fixture output line"
        );
        if status.is_some() {
            break;
        }
        if let Some(done) = execution.child.as_mut().unwrap().try_wait()? {
            status = Some(done);
            continue;
        }
        anyhow::ensure!(
            Instant::now() < deadline,
            "terminal event did not arrive before peer release; stderr: {}",
            fs::read_to_string(root.join("stderr.log"))?
        );
        std::thread::sleep(Duration::from_millis(10));
    }
    execution.child.take();
    anyhow::ensure!(
        status.unwrap().success() != first_fails,
        "incorrect aggregate exit; stderr: {}",
        fs::read_to_string(root.join("stderr.log"))?
    );
    anyhow::ensure!(
        terminals.len() == 2
            && terminals
                .get("b")
                .is_some_and(|row| row["state"] == "passed"),
        "missing final outcomes: {terminals:?}"
    );
    anyhow::ensure!(
        fs::read(root.join("b.finished"))? == b"actual B completion",
        "peer did not finish after release"
    );
    anyhow::ensure!(
        terminals["a"]["index"] != terminals["b"]["index"]
            && terminals["a"]["prerequisite_artifact"] != terminals["b"]["prerequisite_artifact"],
        "terminal identities were conflated"
    );
    execution.passed = true;
    Ok(())
}

fn command(root: &Path, jobs: usize) -> Command {
    command_with(root, jobs, 2)
}

fn command_with(root: &Path, jobs: usize, test_jobs: usize) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_targo"));
    command
        .current_dir(root)
        .env_clear()
        .env("HOME", root)
        .env("CARGO_HOME", root.join("home"))
        .env("CARGO_TARGET_DIR", root.join("target"))
        .env("RUSTC", fixture_rustc())
        .env("RUSTFLAGS", SERIAL_FRONTEND)
        .env("PATH", std::env::var_os("PATH").unwrap())
        .env("SCHEDULE_FORCE", "caller")
        .env("SCHEDULE_DEFAULT", "caller")
        .args([
            "--unverified",
            "test",
            "--offline",
            "--test",
            "a",
            "--test",
            "b",
            "--message-format=json",
            "--config",
        ])
        .arg(format!("build.test-jobs={test_jobs}"))
        .arg("-j")
        .arg(jobs.to_string());
    command
}

fn events(output: &Output) -> Vec<serde_json::Value> {
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
        .filter(|row| row["reason"] == "test-execution")
        .collect()
}

#[test]
fn native_tests_share_build_prerequisites_and_schedule_owned_processes() {
    let root = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
    let root = root.path();
    fs::create_dir_all(root.join("src")).unwrap();
    fs::create_dir(root.join("tests")).unwrap();
    fs::write(
        root.join("Cargo.toml"),
        "[package]\nname='scheduled_tests'\nversion='0.0.0'\nedition='2021'\n[workspace]\n",
    )
    .unwrap();
    fs::write(root.join("src/lib.rs"), "pub fn value() -> u8 { 42 }\n").unwrap();
    // Trust: native scheduling must keep Cargo's resolved runtime environment,
    // including repository stack settings and relative/forced config values.
    fs::create_dir(root.join(".cargo")).unwrap();
    fs::write(
        root.join(".cargo/config.toml"),
        r#"
[env]
RUST_MIN_STACK = "16777216"
SCHEDULE_FORCE = { value = "configured", force = true }
SCHEDULE_RELATIVE = { value = "runtime-input", relative = true }
SCHEDULE_DEFAULT = { value = "configured", force = false }
"#,
    )
    .unwrap();
    for (name, other) in [("a", "b"), ("b", "a")] {
        fs::write(
            root.join(format!("tests/{name}.rs")),
            format!(
                r#"
#[test] fn run() {{
    assert_eq!(scheduled_tests::value(), 42);
    assert_eq!(std::env::var("RUST_TEST_THREADS").unwrap(), "1");
    assert_eq!(std::env::var("RUST_MIN_STACK").unwrap(), "16777216");
    assert_eq!(std::env::var("SCHEDULE_FORCE").unwrap(), "configured");
    assert_eq!(std::env::var("SCHEDULE_DEFAULT").unwrap(), "caller");
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    assert_eq!(std::env::current_dir().unwrap(), root);
    assert_eq!(std::path::PathBuf::from(std::env::var_os("SCHEDULE_RELATIVE").unwrap()), root.join("runtime-input"));
    std::fs::write(root.join("{name}.started"), b"started").unwrap();
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(10);
    while !root.join("{other}.started").exists() {{
        assert!(std::time::Instant::now() < deadline, "harnesses did not overlap");
        std::thread::sleep(std::time::Duration::from_millis(10));
    }}
}}
"#
            ),
        )
        .unwrap();
    }
    let output = command(root, 2).output().unwrap();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let rows = events(&output);
    assert_eq!(
        rows.iter().filter(|row| row["state"] == "passed").count(),
        2
    );
    for row in &rows {
        assert!(
            row["prerequisite_artifact"]
                .as_str()
                .unwrap()
                .contains("target")
        );
    }
    let artifacts: Vec<serde_json::Value> = String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
        .filter(|row| {
            row["reason"] == "compiler-artifact" && row["target"]["name"] == "scheduled_tests"
        })
        .collect();
    assert_eq!(
        artifacts.len(),
        1,
        "shared library prerequisite must compile once"
    );

    fs::write(
        root.join("tests/a.rs"),
        "#[test] fn run() { panic!(\"required failure\"); }\n",
    )
    .unwrap();
    fs::write(root.join("tests/b.rs"), "#[test] fn run() { std::fs::write(concat!(env!(\"CARGO_MANIFEST_DIR\"), \"/must-not-run\"), b\"bad\").unwrap(); }\n").unwrap();
    let output = command(root, 1).output().unwrap();
    assert!(!output.status.success());
    assert!(!root.join("must-not-run").exists());
    assert!(
        events(&output)
            .iter()
            .any(|row| row["target"] == "b" && row["state"] == "blocked")
    );

    let output = command(root, 1).arg("--no-fail-fast").output().unwrap();
    assert!(!output.status.success());
    assert!(
        root.join("must-not-run").exists(),
        "no-fail-fast must execute the independent second harness"
    );
    assert!(
        events(&output)
            .iter()
            .any(|row| row["target"] == "b" && row["state"] == "passed")
    );
    fs::remove_file(root.join("must-not-run")).unwrap();

    fs::write(root.join("src/lib.rs"), "invalid Rust source\n").unwrap();
    let output = command(root, 2).output().unwrap();
    assert!(!output.status.success());
    assert!(
        events(&output).iter().all(|row| row["state"] == "blocked"),
        "failed prerequisites may report blocked actions but cannot admit harnesses"
    );
    assert!(!root.join("must-not-run").exists());
}

#[test]
fn interrupted_scheduler_reaps_each_owned_process_group() {
    interrupted_scheduler_reaps(2, 2, &[]);
    // Trust: a harness holding two credits runs beside a one-credit peer,
    // and both groups are still reaped.
    interrupted_scheduler_reaps(
        3,
        3,
        &[
            "--config",
            "build.test-harnesses.cancel_tests.test.a.weight=2",
        ],
    );
}

fn interrupted_scheduler_reaps(jobs: usize, test_jobs: usize, admission: &[&str]) {
    let root = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
    let root = root.path();
    fs::create_dir_all(root.join("tests")).unwrap();
    fs::write(
        root.join("Cargo.toml"),
        "[package]\nname='cancel_tests'\nversion='0.0.0'\nedition='2021'\n[workspace]\n",
    )
    .unwrap();
    for name in ["a", "b"] {
        fs::write(root.join(format!("tests/{name}.rs")), format!(r#"
#[test] fn run() {{
    std::process::Command::new(std::env::current_exe().unwrap()).args(["--exact", "grandchild"]).spawn().unwrap();
    std::fs::write(concat!(env!("CARGO_MANIFEST_DIR"), "/{name}.started"), b"ready").unwrap();
    std::thread::sleep(std::time::Duration::from_secs(60));
}}
#[test] fn grandchild() {{
    while !std::path::Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/release-grandchildren")).exists() {{ std::thread::sleep(std::time::Duration::from_millis(10)); }}
    std::fs::write(concat!(env!("CARGO_MANIFEST_DIR"), "/escaped-{name}"), b"bad").unwrap();
}}
"#)).unwrap();
    }
    let log = fs::File::create(root.join("execution.log")).unwrap();
    let mut child = command_with(root, jobs, test_jobs)
        .args(admission)
        .args(["--", "run"])
        .stdout(log.try_clone().unwrap())
        .stderr(log)
        .spawn()
        .unwrap();
    let deadline = Instant::now() + Duration::from_secs(30);
    while !(root.join("a.started").exists() && root.join("b.started").exists()) {
        if Instant::now() >= deadline || child.try_wait().unwrap().is_some() {
            let _ = child.kill();
            let _ = child.wait();
            panic!(
                "scheduler did not start: {}",
                fs::read_to_string(root.join("execution.log")).unwrap()
            );
        }
        std::thread::sleep(Duration::from_millis(10));
    }
    assert_eq!(
        unsafe { libc::kill(child.id() as libc::pid_t, libc::SIGTERM) },
        0
    );
    let deadline = Instant::now() + Duration::from_secs(10);
    loop {
        if let Some(status) = child.try_wait().unwrap() {
            assert!(!status.success());
            break;
        }
        if Instant::now() >= deadline {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("cancelled scheduler did not exit");
        }
        std::thread::sleep(Duration::from_millis(10));
    }
    fs::write(root.join("release-grandchildren"), b"release").unwrap();
    std::thread::sleep(Duration::from_millis(500));
    assert!(!root.join("escaped-a").exists());
    assert!(!root.join("escaped-b").exists());
}

// Trust: weighted, exclusive, attributed and unharnessed test actions.
// Fixture threads account for themselves under a directory lock; the counts
// are observations of real libtest threads, not of Targo's own bookkeeping.
const THREAD_ACCOUNTING: &str = r#"
fn root() -> std::path::PathBuf {
    std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}
fn wait_for(name: &str) {
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(60);
    while !root().join(name).exists() {
        assert!(std::time::Instant::now() < deadline, "fixture peer never arrived: {name}");
        std::thread::sleep(std::time::Duration::from_millis(5));
    }
}
fn change(delta: i32) -> i32 {
    let lock = root().join("accounting-lock");
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(60);
    loop {
        match std::fs::create_dir(&lock) {
            Ok(()) => break,
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
                assert!(std::time::Instant::now() < deadline, "accounting lock timed out");
                std::thread::sleep(std::time::Duration::from_millis(1));
            }
            Err(error) => panic!("accounting: {error}"),
        }
    }
    let read = |name: &str| std::fs::read_to_string(root().join(name))
        .unwrap_or_else(|_| "0".into()).parse::<i32>().unwrap();
    let active = read("active") + delta;
    let peak = read("peak").max(active);
    std::fs::write(root().join("active"), active.to_string()).unwrap();
    std::fs::write(root().join("peak"), peak.to_string()).unwrap();
    std::fs::remove_dir(lock).unwrap();
    let limit: i32 = std::env::var("EXPECT_LIMIT").unwrap().parse().unwrap();
    assert!((0..=limit).contains(&active), "running test threads {active} exceeded the bound {limit}");
    active
}
struct Thread;
impl Thread { fn enter() -> Self { change(1); Self } }
impl Drop for Thread { fn drop(&mut self) { change(-1); } }
"#;

fn action_fixture(name: &str) -> tempfile::TempDir {
    let base = std::env::current_dir()
        .unwrap()
        .join(".ubd/weighted-test-actions.noindex");
    fs::create_dir_all(&base).unwrap();
    let root = tempfile::tempdir_in(base).unwrap();
    fs::create_dir_all(root.path().join("tests")).unwrap();
    fs::create_dir_all(root.path().join("src")).unwrap();
    fs::write(root.path().join("src/lib.rs"), "").unwrap();
    fs::write(
        root.path().join("Cargo.toml"),
        format!("[package]\nname='{name}'\nversion='0.0.0'\nedition='2024'\n[workspace]\n"),
    )
    .unwrap();
    root
}

fn action_command(root: &Path, jobs: usize, test_jobs: usize) -> Command {
    let mut command = graph_command(root);
    command
        .args([
            "--unverified",
            "test",
            "--offline",
            "--tests",
            "--message-format=json",
        ])
        .arg(format!("-j{jobs}"))
        .arg("--config")
        .arg(format!("build.test-jobs={test_jobs}"))
        .env("EXPECT_LIMIT", test_jobs.to_string());
    command
}

fn json_rows(output: &Output) -> Vec<serde_json::Value> {
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .map(|line| {
            serde_json::from_str::<serde_json::Value>(line)
                .unwrap_or_else(|_| panic!("a raw line reached JSON stdout: {line:?}"))
        })
        .collect()
}

fn executions(rows: &[serde_json::Value]) -> Vec<&serde_json::Value> {
    rows.iter()
        .filter(|row| row["reason"] == "test-execution")
        .collect()
}

fn terminal<'a>(rows: &'a [serde_json::Value], target: &str) -> &'a serde_json::Value {
    let terminals: Vec<_> = executions(rows)
        .into_iter()
        .filter(|row| {
            row["target"] == target && matches!(row["state"].as_str(), Some("passed" | "failed"))
        })
        .collect();
    assert_eq!(
        terminals.len(),
        1,
        "terminal records of {target}: {terminals:?}"
    );
    terminals[0]
}

/// Replay `running` and terminal records in coordinator order: the weights
/// of running actions never exceed the bound, and an exclusive action never
/// runs beside another.
fn replay_admission(rows: &[serde_json::Value], limit: u64) -> u64 {
    let mut running = std::collections::BTreeMap::new();
    let mut peak = 0;
    for row in executions(rows) {
        let index = row["index"].as_u64().unwrap();
        match row["state"].as_str().unwrap() {
            "running" => {
                assert!(running.insert(index, row).is_none());
                let credits: u64 = running
                    .values()
                    .map(|row| row["weight"].as_u64().unwrap())
                    .sum();
                assert!(
                    credits <= limit,
                    "{credits} credits running beyond {limit}: {running:?}"
                );
                if running.values().any(|row| row["exclusive"] == true) {
                    assert_eq!(
                        running.len(),
                        1,
                        "an exclusive action ran beside another: {running:?}"
                    );
                }
                peak = peak.max(credits);
            }
            "passed" | "failed" => {
                running.remove(&index);
            }
            _ => {}
        }
    }
    assert!(running.is_empty());
    peak
}

#[test]
fn weighted_harnesses_hold_their_credits_and_threads() {
    let root = action_fixture("weighted_tests");
    // heavy's three test threads meet, so libtest really runs as many
    // threads as credits it holds, and wait for light_a; light_a waits for
    // them. Together they fill the bound of four. light_b waits for no one.
    fs::write(
        root.path().join("tests/heavy.rs"),
        format!(
            "{THREAD_ACCOUNTING}\n{}",
            r#"
static MET: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
fn work() {
    let _thread = Thread::enter();
    assert_eq!(std::env::var("RUST_TEST_THREADS").unwrap(), std::env::var("EXPECT_HEAVY").unwrap());
    if std::env::var_os("NO_WAIT").is_some() { return; }
    MET.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(60);
    while MET.load(std::sync::atomic::Ordering::SeqCst) < 3 {
        assert!(std::time::Instant::now() < deadline, "libtest did not run three threads");
        std::thread::sleep(std::time::Duration::from_millis(5));
    }
    std::fs::write(root().join("heavy.met"), b"three threads").unwrap();
    wait_for("light_a.started");
    wait_for("light_a.observed");
}
#[test] fn one() { work(); }
#[test] fn two() { work(); }
#[test] fn three() { work(); }
"#
        ),
    )
    .unwrap();
    for (name, waits) in [("light_a", true), ("light_b", false)] {
        fs::write(
            root.path().join(format!("tests/{name}.rs")),
            format!(
                "{THREAD_ACCOUNTING}\n{}",
                format!(
                    r#"
#[test] fn run() {{
    let _thread = Thread::enter();
    assert_eq!(std::env::var("RUST_TEST_THREADS").unwrap(), "1");
    std::fs::write(root().join("{name}.started"), b"started").unwrap();
    if {waits} && std::env::var_os("NO_WAIT").is_none() {{
        wait_for("heavy.met");
        std::fs::write(root().join("{name}.observed"), b"overlap").unwrap();
    }}
}}
"#
                )
            ),
        )
        .unwrap();
    }
    let output = action_command(root.path(), 5, 4)
        .env("EXPECT_HEAVY", "3")
        .args([
            "--config",
            "build.test-harnesses.weighted_tests.test.heavy.weight=3",
        ])
        .output()
        .unwrap();
    let rows = json_rows(&output);
    successful(output);
    assert_eq!(replay_admission(&rows, 4), 4);
    assert_eq!(fs::read_to_string(root.path().join("peak")).unwrap(), "4");
    assert_eq!(fs::read_to_string(root.path().join("active")).unwrap(), "0");
    for (target, weight) in [("heavy", 3), ("light_a", 1), ("light_b", 1)] {
        let row = terminal(&rows, target);
        assert_eq!(row["schema"], "targo.test-execution.v2");
        assert_eq!(row["state"], "passed");
        assert_eq!(row["weight"], weight);
        assert_eq!(row["exit_code"], 0);
        assert!(row["signal"].is_null());
        assert_eq!(row["package"], "weighted_tests");
        assert_eq!(row["kind"], "test");
        assert_eq!(row["harness"], true);
        assert!(
            row["package_id"]
                .as_str()
                .unwrap()
                .contains("weighted_tests")
        );
    }
    // A weight above the bound is clamped to it: threads still equal the
    // credits held, and the clamped harness runs with nothing beside it.
    for marker in [
        "active",
        "peak",
        "heavy.met",
        "light_a.started",
        "light_b.started",
    ] {
        let _ = fs::remove_file(root.path().join(marker));
    }
    let output = action_command(root.path(), 5, 4)
        .env("EXPECT_HEAVY", "4")
        .env("NO_WAIT", "1")
        .args([
            "--config",
            "build.test-harnesses.weighted_tests.test.heavy.weight=9",
        ])
        .output()
        .unwrap();
    let rows = json_rows(&output);
    successful(output);
    replay_admission(&rows, 4);
    assert_eq!(terminal(&rows, "heavy")["weight"], 4);
    let heavy = executions(&rows)
        .iter()
        .find(|row| row["target"] == "heavy" && row["state"] == "running")
        .unwrap()["index"]
        .clone();
    let mut alone = false;
    for row in executions(&rows) {
        match (row["index"] == heavy, row["state"].as_str().unwrap()) {
            (true, "running") => alone = true,
            (true, "passed") => alone = false,
            (false, "running") => assert!(!alone, "a harness ran beside a full-weight one"),
            _ => {}
        }
    }
}

#[test]
fn an_exclusive_harness_runs_alone_after_compilation() {
    let root = action_fixture("exclusive_tests");
    for (name, other) in [("a", "b"), ("b", "a")] {
        fs::write(
            root.path().join(format!("tests/{name}.rs")),
            format!(
                "{THREAD_ACCOUNTING}\n{}",
                format!(
                    r#"
#[test] fn run() {{
    let _thread = Thread::enter();
    assert!(!root().join("alone.running").exists(), "ran beside the exclusive harness");
    std::fs::write(root().join("{name}.started"), b"started").unwrap();
    wait_for("{other}.started");
    assert!(!root().join("alone.running").exists(), "ran beside the exclusive harness");
}}
"#
                )
            ),
        )
        .unwrap();
    }
    fs::write(
        root.path().join("tests/alone.rs"),
        format!(
            "{THREAD_ACCOUNTING}\n{}",
            r#"
#[test] fn run() {
    let _thread = Thread::enter();
    assert_eq!(change(0), 1, "the exclusive harness started beside another test thread");
    std::fs::write(root().join("alone.running"), b"running").unwrap();
    std::thread::sleep(std::time::Duration::from_millis(200));
    assert_eq!(change(0), 1, "a test thread started beside the exclusive harness");
    std::fs::remove_file(root().join("alone.running")).unwrap();
}
"#
        ),
    )
    .unwrap();
    // a and b must overlap, so the queue had room beside the exclusive
    // harness; it chose to leave that room empty.
    let output = action_command(root.path(), 3, 2)
        .args([
            "--config",
            "build.test-harnesses.exclusive_tests.test.alone.exclusive=true",
        ])
        .output()
        .unwrap();
    let rows = json_rows(&output);
    successful(output);
    assert_eq!(replay_admission(&rows, 2), 2);
    let start = rows
        .iter()
        .position(|row| row["target"] == "alone" && row["state"] == "running")
        .unwrap();
    let end = rows
        .iter()
        .position(|row| row["target"] == "alone" && row["state"] == "passed")
        .unwrap();
    assert_eq!(rows[start]["exclusive"], true);
    for row in &rows[start + 1..end] {
        assert!(
            row["reason"] != "compiler-artifact" && row["state"] != "running",
            "work ran beside the exclusive harness: {row}"
        );
    }
    // It ran after every compilation and after the other harnesses.
    assert!(
        rows[start..]
            .iter()
            .all(|row| row["reason"] != "compiler-artifact")
    );
    for target in ["a", "b"] {
        let done = rows
            .iter()
            .position(|row| row["target"] == target && row["state"] == "passed")
            .unwrap();
        assert!(
            done < start,
            "{target} finished after the exclusive harness started"
        );
    }
}

#[test]
fn concurrent_failing_harnesses_keep_their_own_output_and_exit() {
    let root = action_fixture("attributed_tests");
    for (name, other, fail) in [
        ("a", "b", "panic!(\"a fails\")"),
        ("b", "a", "std::process::exit(7)"),
    ] {
        fs::write(
            root.path().join(format!("tests/{name}.rs")),
            format!(
                "{THREAD_ACCOUNTING}\n{}",
                format!(
                    r#"
#[test] fn run() {{
    use std::io::Write;
    std::fs::write(root().join("{name}.started"), b"started").unwrap();
    wait_for("{other}.started");
    // Written past libtest's capture, interleaved with the peer's lines.
    for i in 0..50 {{
        writeln!(std::io::stdout().lock(), "{name}-out-{{i}}").unwrap();
        writeln!(std::io::stderr().lock(), "{name}-err-{{i}}").unwrap();
        std::thread::sleep(std::time::Duration::from_millis(1));
    }}
    std::io::stdout().flush().unwrap();
    {fail};
}}
"#
                )
            ),
        )
        .unwrap();
    }
    let output = action_command(root.path(), 3, 2)
        .arg("--no-fail-fast")
        .output()
        .unwrap();
    assert!(!output.status.success());
    let rows = json_rows(&output);
    let mut owner = std::collections::BTreeMap::new();
    for row in executions(&rows) {
        owner.insert(
            row["index"].as_u64().unwrap(),
            row["target"].as_str().unwrap().to_owned(),
        );
    }
    let mut seen = std::collections::BTreeMap::<(String, &str), Vec<usize>>::new();
    for row in rows.iter().filter(|row| row["reason"] == "test-output") {
        assert_eq!(row["schema"], "targo.test-output.v1");
        let line = row["line"].as_str().unwrap();
        let stream = row["stream"].as_str().unwrap();
        let target = &owner[&row["index"].as_u64().unwrap()];
        for name in ["a", "b"] {
            for (tag, expected) in [("out", "stdout"), ("err", "stderr")] {
                // libtest's own partial `test run ... ` line may carry the
                // first token, so a token may follow other text on its line.
                let token = format!("{name}-{tag}-");
                if let Some(number) = line.find(&token).map(|at| &line[at + token.len()..]) {
                    assert_eq!(target, name, "{line} attributed to {target}");
                    assert_eq!(stream, expected, "{line} attributed to {stream}");
                    seen.entry((name.to_owned(), expected))
                        .or_default()
                        .push(number.parse().unwrap());
                }
            }
        }
    }
    for name in ["a", "b"] {
        for stream in ["stdout", "stderr"] {
            assert_eq!(
                seen[&(name.to_owned(), stream)],
                (0..50).collect::<Vec<_>>(),
                "{name} {stream} lines lost or reordered"
            );
        }
    }
    let a = terminal(&rows, "a");
    assert_eq!(
        (&a["state"], &a["exit_code"]),
        (&"failed".into(), &101.into())
    );
    assert!(a["signal"].is_null());
    let b = terminal(&rows, "b");
    assert_eq!(
        (&b["state"], &b["exit_code"]),
        (&"failed".into(), &7.into())
    );
    assert!(b["signal"].is_null());
    assert_eq!(replay_admission(&rows, 2), 2);
}

#[test]
fn unharnessed_targets_pass_and_fail_by_exit_status() {
    let root = action_fixture("unharnessed_tests");
    fs::write(
        root.path().join("Cargo.toml"),
        "[package]\nname='unharnessed_tests'\nversion='0.0.0'\nedition='2024'\n[workspace]\n\
         [[test]]\nname='pass'\nharness=false\n\
         [[test]]\nname='exit3'\nharness=false\n\
         [[test]]\nname='abort'\nharness=false\n",
    )
    .unwrap();
    fs::write(
        root.path().join("tests/pass.rs"),
        r#"fn main() {
    assert_eq!(std::env::var("RUST_TEST_THREADS").unwrap(), "1");
    println!("unharnessed pass");
    std::fs::write(concat!(env!("CARGO_MANIFEST_DIR"), "/pass.ran"), b"ran").unwrap();
}"#,
    )
    .unwrap();
    fs::write(
        root.path().join("tests/exit3.rs"),
        "fn main() { std::process::exit(3); }",
    )
    .unwrap();
    fs::write(
        root.path().join("tests/abort.rs"),
        "fn main() { std::process::abort(); }",
    )
    .unwrap();
    fs::write(
        root.path().join("tests/libtest.rs"),
        r#"#[test] fn run() { assert_eq!(std::env::var("RUST_TEST_THREADS").unwrap(), "2"); }"#,
    )
    .unwrap();
    // The default weight shapes libtest harnesses only.
    let output = action_command(root.path(), 3, 2)
        .args(["--no-fail-fast", "--config", "build.test-weight=2"])
        .output()
        .unwrap();
    assert!(!output.status.success());
    let rows = json_rows(&output);
    replay_admission(&rows, 2);
    let pass = terminal(&rows, "pass");
    assert_eq!(
        (&pass["state"], &pass["exit_code"]),
        (&"passed".into(), &0.into())
    );
    assert_eq!(
        (&pass["harness"], &pass["weight"]),
        (&false.into(), &1.into())
    );
    assert!(rows.iter().any(|row| {
        row["reason"] == "test-output"
            && row["index"] == pass["index"]
            && row["stream"] == "stdout"
            && row["line"] == "unharnessed pass"
    }));
    let exit3 = terminal(&rows, "exit3");
    assert_eq!(
        (&exit3["state"], &exit3["exit_code"]),
        (&"failed".into(), &3.into())
    );
    assert!(exit3["signal"].is_null());
    let abort = terminal(&rows, "abort");
    assert_eq!(
        (&abort["state"], &abort["signal"]),
        (&"failed".into(), &6.into())
    );
    assert!(abort["exit_code"].is_null());
    let libtest = terminal(&rows, "libtest");
    assert_eq!(
        (&libtest["state"], &libtest["weight"]),
        (&"passed".into(), &2.into())
    );
    assert!(root.path().join("pass.ran").exists());
    // A weight cannot be given to a target libtest does not run.
    fs::remove_file(root.path().join("pass.ran")).unwrap();
    let output = action_command(root.path(), 3, 2)
        .args([
            "--config",
            "build.test-harnesses.unharnessed_tests.test.pass.weight=2",
        ])
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("harness = false"));
    assert!(!root.path().join("pass.ran").exists());
}

#[test]
fn harness_policy_typos_are_refused_before_any_test_body() {
    let root = action_fixture("policy_tests");
    fs::write(
        root.path().join("tests/only.rs"),
        r#"#[test] fn run() { std::fs::write(concat!(env!("CARGO_MANIFEST_DIR"), "/ran"), b"bad").unwrap(); }"#,
    )
    .unwrap();
    for (config, refusal) in [
        (
            "build.test-harnesses.policy_tests.test.missing.weight=2",
            "names no test target",
        ),
        (
            "build.test-harnesses.policy_tests.tests.only.weight=2",
            "is not a target kind",
        ),
        (
            "build.test-harnesses.policy_tests.test.only.wieght=2",
            "is not a harness setting",
        ),
        (
            "build.test-harnesses.policy_tests.test.only.weight=0",
            "must be positive",
        ),
        ("build.test-weight=0", "must be positive"),
    ] {
        let output = action_command(root.path(), 3, 2)
            .args(["--config", config])
            .output()
            .unwrap();
        assert!(!output.status.success(), "{config} was accepted");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains(refusal), "{config}: {stderr}");
        assert!(
            !root.path().join("ran").exists(),
            "{config} admitted a test body"
        );
    }
    // The environment cannot spell the map: refused, not silently ignored.
    for (name, value, refusal) in [
        (
            "CARGO_BUILD_TEST_HARNESSES_POLICY_TESTS_TEST_ONLY_WEIGHT",
            "2",
            "cannot set build.test-harnesses",
        ),
        ("CARGO_BUILD_TEST_WEIGHT", "0", "must be positive"),
    ] {
        let output = action_command(root.path(), 3, 2)
            .env(name, value)
            .output()
            .unwrap();
        assert!(!output.status.success(), "{name} was accepted");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains(refusal), "{name}: {stderr}");
        assert!(
            !root.path().join("ran").exists(),
            "{name} admitted a test body"
        );
    }
}

#[test]
fn harness_policy_for_a_package_outside_the_workspace_is_checked_when_tested() {
    let root = action_fixture("policy_host");
    // A path dependency outside the workspace's directory is not a member,
    // but `-p` can still test it.
    let helper = root.path().join("outside/helper");
    fs::create_dir_all(helper.join("tests")).unwrap();
    fs::create_dir_all(helper.join("src")).unwrap();
    fs::write(
        helper.join("src/lib.rs"),
        "/// ```\n/// std::fs::write(concat!(env!(\"CARGO_MANIFEST_DIR\"), \"/doc-ran\"), b\"ran\").unwrap();\n/// ```\npub fn documented() {}\n",
    )
    .unwrap();
    fs::write(
        helper.join("Cargo.toml"),
        "[package]\nname='helper'\nversion='0.0.0'\nedition='2024'\n",
    )
    .unwrap();
    fs::write(
        helper.join("tests/only.rs"),
        r#"#[test] fn run() { std::fs::write(concat!(env!("CARGO_MANIFEST_DIR"), "/ran"), b"ran").unwrap(); }"#,
    )
    .unwrap();
    fs::write(
        root.path().join("Cargo.toml"),
        "[package]\nname='policy_host'\nversion='0.0.0'\nedition='2024'\n\
         [dependencies]\nhelper={path='outside/helper'}\n\
         [workspace]\nexclude=['outside']\n",
    )
    .unwrap();
    // On the test graph and on the sequential route alike.
    for test_jobs in [2, 1] {
        let output = action_command(root.path(), 3, test_jobs)
            .args(["-p", "helper"])
            .args([
                "--config",
                "build.test-harnesses.helper.test.missing.weight=2",
            ])
            .output()
            .unwrap();
        assert!(
            !output.status.success(),
            "a missing target of a tested package was accepted with build.test-jobs={test_jobs}"
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains("names no test target of package `helper`"),
            "{stderr}"
        );
        assert!(!helper.join("ran").exists());
    }
    // An entry for a package this run does not test is reported, not refused.
    let output = action_command(root.path(), 3, 2)
        .args(["-p", "helper"])
        .args(["--config", "build.test-harnesses.elsewhere.test.x.weight=2"])
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    successful(output);
    assert!(
        stderr.contains("build.test-harnesses.elsewhere names no package this run tests"),
        "{stderr}"
    );
    assert!(helper.join("ran").exists());
    // The sequential runner applies none of the policy, so it says nothing
    // about such an entry: a shared configuration file would otherwise warn
    // on every plain `targo test`.
    let output = action_command(root.path(), 3, 1)
        .args(["-p", "helper"])
        .args(["--config", "build.test-harnesses.elsewhere.test.x.weight=2"])
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    successful(output);
    assert!(
        !stderr.contains("names no package this run tests"),
        "{stderr}"
    );
    // A package tested only through its doctests is tested: its entries are
    // checked before any doctest runs, on both routes.
    let doctests = |test_jobs: usize| {
        let mut command = graph_command(root.path());
        command
            .args([
                "--unverified",
                "test",
                "--offline",
                "--doc",
                "-p",
                "helper",
                "-j3",
            ])
            .arg("--config")
            .arg(format!("build.test-jobs={test_jobs}"));
        command
    };
    for test_jobs in [2, 1] {
        let output = doctests(test_jobs)
            .args([
                "--config",
                "build.test-harnesses.helper.test.missing.weight=2",
            ])
            .output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            !output.status.success(),
            "a doctested package's missing target was accepted with build.test-jobs={test_jobs}: {stderr}"
        );
        assert!(
            stderr.contains("names no test target of package `helper`"),
            "{stderr}"
        );
        assert!(!helper.join("doc-ran").exists());
    }
    let output = doctests(1).output().unwrap();
    successful(output);
    assert!(helper.join("doc-ran").exists(), "the doctest itself runs");
}

#[test]
fn harness_policy_checks_every_tested_version_of_a_package() {
    let root = action_fixture("policy_versions");
    let versions = [("helper", "0.0.0"), ("helper2", "2.0.0")];
    for (dir, version) in versions {
        let helper = root.path().join("outside").join(dir);
        fs::create_dir_all(helper.join("tests")).unwrap();
        fs::create_dir_all(helper.join("src")).unwrap();
        fs::write(helper.join("src/lib.rs"), "").unwrap();
        fs::write(
            helper.join("Cargo.toml"),
            format!("[package]\nname='helper'\nversion='{version}'\nedition='2024'\n"),
        )
        .unwrap();
    }
    fs::write(
        root.path().join("Cargo.toml"),
        "[package]\nname='policy_versions'\nversion='0.0.0'\nedition='2024'\n\
         [dependencies]\nhelper={path='outside/helper'}\n\
         helper2={package='helper',path='outside/helper2'}\n\
         [workspace]\nexclude=['outside']\n",
    )
    .unwrap();
    let only = r#"#[test] fn run() { std::fs::write(concat!(env!("CARGO_MANIFEST_DIR"), "/ran"), b"ran").unwrap(); }"#;
    // Whichever version has the target, the one without it is refused.
    for (with, without) in [(0, 1), (1, 0)] {
        let dir = |index: usize| root.path().join("outside").join(versions[index].0);
        fs::write(dir(with).join("tests/only.rs"), only).unwrap();
        let _ = fs::remove_file(dir(without).join("tests/only.rs"));
        for test_jobs in [2, 1] {
            let output = action_command(root.path(), 3, test_jobs)
                .args(["-p", "helper@0.0.0", "-p", "helper@2.0.0"])
                .args(["--config", "build.test-harnesses.helper.test.only.weight=2"])
                .output()
                .unwrap();
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(
                !output.status.success(),
                "helper {} lacks `only` but was accepted with build.test-jobs={test_jobs}: {stderr}",
                versions[without].1
            );
            assert!(
                stderr.contains("names no test target of package `helper`"),
                "{stderr}"
            );
            assert!(!dir(with).join("ran").exists());
        }
    }
    // With both versions carrying it, the entry is accepted and both run.
    for index in [0, 1] {
        let helper = root.path().join("outside").join(versions[index].0);
        fs::write(helper.join("tests/only.rs"), only).unwrap();
    }
    let output = action_command(root.path(), 3, 2)
        .args(["-p", "helper@0.0.0", "-p", "helper@2.0.0"])
        .args(["--config", "build.test-harnesses.helper.test.only.weight=2"])
        .output()
        .unwrap();
    successful(output);
    for (dir, _) in versions {
        assert!(root.path().join("outside").join(dir).join("ran").exists());
    }
}

#[test]
fn a_weighted_harness_fails_instead_of_waiting_forever_for_lost_tokens() {
    let root = action_fixture("lost_tokens");
    // The build script reads two of the pool's tokens and exits holding
    // them, as a client killed mid-build would; a pipe jobserver never gets
    // them back.
    fs::write(
        root.path().join("build.rs"),
        r#"
use std::io::Read;
fn main() {
    let flags = std::env::var("CARGO_MAKEFLAGS").expect("the build script has the jobserver");
    let auth = flags
        .split_whitespace()
        .rev()
        .find_map(|word| word.strip_prefix("--jobserver-auth=").or_else(|| word.strip_prefix("--jobserver-fds=")))
        .expect("jobserver auth");
    let mut pipe = match auth.strip_prefix("fifo:") {
        Some(path) => std::fs::File::open(path).unwrap(),
        None => {
            use std::os::fd::FromRawFd;
            let read: i32 = auth.split_once(',').unwrap().0.parse().unwrap();
            unsafe { std::fs::File::from_raw_fd(read) }
        }
    };
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(60);
    let mut stolen = 0;
    while stolen < 2 {
        let mut token = [0u8; 1];
        match pipe.read(&mut token) {
            Ok(1) => stolen += 1,
            Ok(_) => panic!("jobserver closed"),
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                assert!(std::time::Instant::now() < deadline, "no tokens to take");
                std::thread::sleep(std::time::Duration::from_millis(10));
            }
            Err(error) => panic!("jobserver read: {error}"),
        }
    }
    std::mem::forget(pipe);
    let root = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    std::fs::write(format!("{root}/stolen"), b"2").unwrap();
}
"#,
    )
    .unwrap();
    fs::write(
        root.path().join("tests/heavy.rs"),
        r#"#[test] fn run() { std::fs::write(concat!(env!("CARGO_MANIFEST_DIR"), "/ran"), b"ran").unwrap(); }"#,
    )
    .unwrap();
    let mut child = action_command(root.path(), 3, 3)
        .args(["--test", "heavy"])
        .args([
            "--config",
            "build.test-harnesses.lost_tokens.test.heavy.weight=3",
        ])
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    let mut stdout = child.stdout.take().unwrap();
    let mut stderr = child.stderr.take().unwrap();
    let out = std::thread::spawn(move || {
        let mut text = String::new();
        stdout.read_to_string(&mut text).unwrap();
        text
    });
    let err = std::thread::spawn(move || {
        let mut text = String::new();
        stderr.read_to_string(&mut text).unwrap();
        text
    });
    let deadline = Instant::now() + Duration::from_secs(180);
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if Instant::now() > deadline {
            child.kill().unwrap();
            child.wait().unwrap();
            // A descendant can still hold the pipes open; report what the
            // driver wrote without waiting on it.
            let stderr = if err.is_finished() {
                err.join().unwrap()
            } else {
                "<stderr still held open by a descendant>".to_owned()
            };
            panic!(
                "the queue waited forever for tokens the pool lost; stolen={}\n{stderr}",
                root.path().join("stolen").exists()
            );
        }
        std::thread::sleep(Duration::from_millis(100));
    };
    let (stdout, stderr) = (out.join().unwrap(), err.join().unwrap());
    assert!(root.path().join("stolen").exists(), "{stderr}");
    assert!(!status.success());
    // It names the test short of credits and what Targo holds: the implicit
    // token of the three, the build script having taken the other two.
    assert!(
        stderr.contains(
            "test target `heavy` of `lost_tokens` needs 3 jobserver credits, but with nothing \
             running for 30s Targo holds only 1: the pool's other tokens were lost"
        ),
        "{stderr}"
    );
    assert!(!root.path().join("ran").exists());
    let blocked = stdout
        .lines()
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
        .any(|row| row["target"] == "heavy" && row["state"] == "blocked");
    assert!(blocked, "{stdout}");
}

#[test]
fn a_waiting_weighted_harness_leaves_a_running_compiler_its_tokens() {
    let root = action_fixture("hoard");
    let control = root.path().join("control");
    fs::create_dir_all(&control).unwrap();
    // The wrapper marks `heavy` built, then, while `slow` compiles beside a
    // weight-3 `heavy` that cannot start before it ends, asks the pool for one
    // token, as a rustc's parallel codegen would.
    let source = root.path().join("wrapper");
    fs::create_dir_all(source.join("src")).unwrap();
    fs::write(
        source.join("Cargo.toml"),
        "[package]\nname='hoard_wrapper'\nversion='0.0.0'\nedition='2024'\n[workspace]\n",
    )
    .unwrap();
    fs::write(
        source.join("src/main.rs"),
        r#"
use std::io::{Read, Write};
use std::time::{Duration, Instant};
fn main() {
    let mut words = std::env::args_os().skip(1);
    let compiler = words.next().unwrap();
    let words: Vec<_> = words.collect();
    let name = words.windows(2).find(|pair| pair[0] == "--crate-name").and_then(|pair| pair[1].to_str().map(str::to_owned));
    let test = words.iter().any(|word| word == "--test");
    let control = std::path::PathBuf::from(std::env::var_os("HOARD_CONTROL").unwrap());
    if name.as_deref() == Some("slow") && test {
        let deadline = Instant::now() + Duration::from_secs(60);
        while !control.join("heavy.built").exists() {
            assert!(Instant::now() < deadline, "heavy never built");
            std::thread::sleep(Duration::from_millis(5));
        }
        // Long enough for the coordinator to settle on heavy's admission.
        std::thread::sleep(Duration::from_millis(1500));
        let flags = std::env::var("CARGO_MAKEFLAGS").expect("the compiler has the jobserver");
        let auth = flags.split_whitespace().rev()
            .find_map(|word| word.strip_prefix("--jobserver-auth=").or_else(|| word.strip_prefix("--jobserver-fds=")))
            .unwrap().to_owned();
        let (sender, receiver) = std::sync::mpsc::channel();
        std::thread::spawn(move || {
            let (mut read, mut write): (std::fs::File, std::fs::File) = match auth.strip_prefix("fifo:") {
                Some(path) => (std::fs::File::open(path).unwrap(), std::fs::OpenOptions::new().write(true).open(path).unwrap()),
                None => {
                    use std::os::fd::FromRawFd;
                    let (r, w) = auth.split_once(',').unwrap();
                    unsafe { (std::fs::File::from_raw_fd(r.parse().unwrap()), std::fs::File::from_raw_fd(w.parse().unwrap())) }
                }
            };
            let mut token = [0u8; 1];
            loop {
                match read.read(&mut token) {
                    Ok(1) => {
                        write.write_all(&token).unwrap();
                        let _ = sender.send(());
                        break;
                    }
                    Ok(_) => break,
                    Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                        std::thread::sleep(Duration::from_millis(5));
                    }
                    Err(error) => panic!("jobserver read: {error}"),
                }
            }
            std::mem::forget(read);
            std::mem::forget(write);
        });
        let got = receiver.recv_timeout(Duration::from_secs(5)).is_ok();
        std::fs::write(control.join("probe"), if got { "got a token" } else { "no token in 5s" }).unwrap();
    }
    let status = std::process::Command::new(compiler).args(&words).status().unwrap();
    if name.as_deref() == Some("heavy") && test {
        std::fs::write(control.join("heavy.built"), b"").unwrap();
    }
    std::process::exit(status.code().unwrap_or(101));
}
"#,
    )
    .unwrap();
    let built = graph_command(&source)
        .args([
            "--unverified",
            "build",
            "--offline",
            "--message-format=json",
        ])
        .output()
        .unwrap();
    assert!(
        built.status.success(),
        "{}",
        String::from_utf8_lossy(&built.stderr)
    );
    let wrapper = String::from_utf8_lossy(&built.stdout)
        .lines()
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
        .find(|row| {
            row["reason"] == "compiler-artifact" && row["target"]["name"] == "hoard_wrapper"
        })
        .and_then(|row| row["executable"].as_str().map(std::path::PathBuf::from))
        .unwrap();
    fs::write(root.path().join("tests/heavy.rs"), "#[test] fn run() {}").unwrap();
    fs::write(root.path().join("tests/slow.rs"), "#[test] fn run() {}").unwrap();
    let output = action_command(root.path(), 3, 3)
        .env("RUSTC_WRAPPER", &wrapper)
        .env("HOARD_CONTROL", &control)
        .args(["--config", "build.test-harnesses.hoard.test.heavy.weight=3"])
        .output()
        .unwrap();
    let rows = json_rows(&output);
    successful(output);
    assert_eq!(
        fs::read_to_string(control.join("probe")).unwrap(),
        "got a token",
        "the waiting weight-3 harness held the pool's free tokens idle beside a running compiler"
    );
    assert_eq!(terminal(&rows, "heavy")["weight"], 3);
    assert_eq!(terminal(&rows, "heavy")["state"], "passed");
}

#[test]
fn a_required_binary_judged_failed_keeps_its_own_exit() {
    let root = action_fixture("required_exit");
    fs::create_dir_all(root.path().join("src/bin")).unwrap();
    fs::write(
        root.path().join("src/bin/reqbin.rs"),
        "fn main() {}\n#[test] fn run() {}\n",
    )
    .unwrap();
    // The filter leaves the required harness no passing test: it exits 0
    // by itself and Targo judges it failed.
    let output = graph_command(root.path())
        .args([
            "--unverified",
            "test",
            "--offline",
            "--bins",
            "--message-format=json",
            "-j2",
            "--config",
            "build.test-jobs=2",
            "--require-test-bin",
            "reqbin",
            "--",
            "no_such_filter",
        ])
        .output()
        .unwrap();
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(
        stderr.contains("required test binary `reqbin` reported no passing tests"),
        "{stderr}"
    );
    let rows = json_rows(&output);
    let record = terminal(&rows, "reqbin");
    assert_eq!(record["state"], "failed");
    assert_eq!(record["exit_code"], 0, "{record}");
    assert_eq!(record["signal"], serde_json::Value::Null, "{record}");
}

//! Opt-in actual canonical admission and runnable Targo configuration.
//! Run this system harness outside a retained build-slot epoch after
//! compiling it under the ordinary build gate. It acquires real existing slots;
//! it creates no private machine pool or SDK/Host/provenance authority.

#![cfg(any(target_os = "linux", target_os = "macos"))]

use std::io::{self, Read as _};
use std::num::NonZeroU32;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use trust_build_tree::admission::{
    Attempt, Coordinator, FixedClaim, Requirements, RunningFixedCommand, RunningFixedGroup,
};

// Shared admission may legitimately wait behind an earlier compiler epoch.
// This is finite queue patience, not a larger CPU grant or execution timeout;
// use the documented shared-machine 30-minute admission window.
const ADMISSION_QUEUE_PATIENCE: Duration = Duration::from_secs(30 * 60);

fn actual_claim(budget: u32) -> FixedClaim {
    actual_claim_mode(budget, false)
}

fn actual_claim_mode(budget: u32, exclusive: bool) -> FixedClaim {
    assert!(
        std::env::var_os("BUILD_SLOT_HELD").is_none(),
        "run the planning test outside its compiler's retained admission"
    );
    assert!(
        std::env::var_os("CARGO_MAKEFLAGS").is_none(),
        "this qualification does not supply the pending inherited-GNU bridge"
    );
    let cpus = std::thread::available_parallelism().unwrap().get() as u32;
    assert!(
        cpus >= budget,
        "canonical fixture needs its actual CPU budget"
    );
    let slots = match std::env::var("BUILD_SLOTS") {
        Ok(value) => value.parse::<u32>().unwrap(),
        Err(_) => (cpus / 6).max(1),
    };
    let needed = u32::try_from((u64::from(budget) * u64::from(slots)).div_ceil(u64::from(cpus)))
        .unwrap()
        .max(1);
    let required =
        Requirements::new(None, slots, needed, exclusive, 8 * 1024 * 1024 * 1024).unwrap();
    let mut coordinator = Coordinator::for_current_user(required).unwrap();
    let deadline = Instant::now() + ADMISSION_QUEUE_PATIENCE;
    loop {
        match coordinator
            .attempt_fixed(
                trust_build_cpu::available_memory(),
                needed,
                NonZeroU32::new(budget).unwrap(),
            )
            .unwrap()
        {
            Attempt::Admitted(claim) => return claim,
            Attempt::Waiting(reason) => {
                assert!(
                    Instant::now() < deadline,
                    "actual original admission remains {reason:?}"
                );
                std::thread::sleep(Duration::from_millis(50));
            }
        }
    }
}

fn plan(root: &std::path::Path, jobs: u32) -> (std::process::ExitStatus, String, String) {
    let claim = actual_claim(1);
    let mut command = Command::new(env!("CARGO_BIN_EXE_targo"));
    command
        .current_dir(root)
        .args([
            "--unverified",
            "check",
            "--offline",
            "--unit-graph",
            "-Z",
            "unstable-options",
            "-j",
        ])
        .arg(jobs.to_string())
        .env("CARGO_BUILD_JOBS", "1")
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    capture(claim.prepare_command(command).unwrap().spawn().unwrap())
}

fn capture(mut child: RunningFixedCommand) -> (std::process::ExitStatus, String, String) {
    let stdout = child.take_stdout().unwrap();
    let stderr = child.take_stderr().unwrap();
    capture_io(stdout, stderr, || child.wait())
}

fn capture_group(mut child: RunningFixedGroup) -> (std::process::ExitStatus, String, String) {
    let stdout = child.take_stdout().unwrap();
    let stderr = child.take_stderr().unwrap();
    capture_io(stdout, stderr, || child.wait())
}

fn capture_io(
    output: std::process::ChildStdout,
    diagnostics: std::process::ChildStderr,
    wait: impl FnOnce() -> io::Result<std::process::ExitStatus>,
) -> (std::process::ExitStatus, String, String) {
    fn drain(stream: impl io::Read + Send + 'static) -> std::thread::JoinHandle<String> {
        std::thread::spawn(move || {
            let mut bytes = Vec::new();
            stream
                .take(1024 * 1024 + 1)
                .read_to_end(&mut bytes)
                .unwrap();
            assert!(
                bytes.len() <= 1024 * 1024,
                "planning output exceeded its bound"
            );
            String::from_utf8(bytes).unwrap()
        })
    }
    let stdout = drain(output);
    let stderr = drain(diagnostics);
    let status = wait().unwrap();
    (status, stdout.join().unwrap(), stderr.join().unwrap())
}

#[test]
fn actual_canonical_handoff_drives_native_targo_and_refuses_job_widening() -> io::Result<()> {
    let root = tempfile::tempdir()?;
    std::fs::create_dir(root.path().join("src"))?;
    std::fs::write(
        root.path().join("Cargo.toml"),
        "[package]\nname='fixed-custody-plan'\nversion='0.0.0'\nedition='2021'\n[workspace]\n",
    )?;
    std::fs::write(
        root.path().join("src/lib.rs"),
        "pub fn fixed() -> u32 { 1 }\n",
    )?;
    let (status, stdout, stderr) = plan(root.path(), 1);
    assert!(
        status.success(),
        "actual Targo planning failed: {status}\n{stderr}"
    );
    let graph: serde_json::Value = serde_json::from_str(&stdout).unwrap();
    assert!(
        graph["units"]
            .as_array()
            .is_some_and(|units| !units.is_empty())
    );
    assert!(
        !root.path().join("target/debug").exists(),
        "planning compiled fixture units"
    );
    let (status, _, stderr) = plan(root.path(), 2);
    assert!(!status.success());
    assert!(
        stderr.contains("configured jobs exceed the original fixed command CPU ceiling 1"),
        "wrong refusal: {stderr}"
    );
    Ok(())
}

#[test]
fn real_compilation_restricts_and_returns_actual_inherited_anonymous_gnu_credits() -> io::Result<()>
{
    compile_gnu(Launch::Direct)
}

#[test]
fn actual_group_compilation_retires_its_original_group_and_returns_inherited_gnu_credits()
-> io::Result<()> {
    compile_gnu(Launch::Group)
}

#[test]
fn actual_native_fixed_entry_compiles_without_an_external_admission_script() -> io::Result<()> {
    compile_gnu(Launch::NativeEntry)
}

#[test]
fn actual_fixed_serial_fail_fast_keeps_target_order() -> io::Result<()> {
    let root = tempfile::tempdir()?;
    git2::Repository::init(root.path()).unwrap();
    let tests = root.path().join("tests");
    std::fs::create_dir(&tests)?;
    std::fs::write(
        root.path().join("Cargo.toml"),
        "[package]\nname='fixed-serial-tests'\nversion='0.0.0'\nedition='2021'\n[workspace]\n",
    )?;
    for (name, result) in [
        ("alpha", ""),
        ("failure", "panic!(\"selected failure\");"),
        ("zz_after", ""),
    ] {
        std::fs::write(
            tests.join(format!("{name}.rs")),
            format!(
                r#"
#[test]
fn selected() {{
    use std::io::Write as _;
    let mut log = std::fs::OpenOptions::new()
        .append(true).create(true).open("executed").unwrap();
    writeln!(log, "{name}").unwrap();
    {result}
}}
#[test]
fn excluded() {{ panic!("test filter was lost"); }}
"#
            ),
        )?;
    }
    let run = |args: &[&str]| {
        Command::new(env!("CARGO_BIN_EXE_targo"))
            .current_dir(root.path())
            .args([
                "--unverified",
                "resource",
                "fixed",
                "--cpus",
                "2",
                "--",
                "test",
                "--offline",
            ])
            .args(args)
            .output()
    };
    let warm = run(&["--test", "zz_after", "--no-run"])?;
    assert!(
        warm.status.success(),
        "{}",
        String::from_utf8_lossy(&warm.stderr)
    );
    let targets = ["--test", "alpha", "--test", "failure", "--test", "zz_after"];
    let output = run(&[&targets[..], &["selected"]].concat())?;
    assert!(!output.status.success());
    let executed = root.path().join("executed");
    assert_eq!(
        std::fs::read_to_string(&executed)?,
        "alpha\nfailure\n",
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );

    std::fs::remove_file(&executed)?;
    let output = run(&[&targets[..], &["--no-fail-fast", "selected"]].concat())?;
    assert!(!output.status.success());
    let actual = std::fs::read_to_string(executed)?;
    let mut lines = actual.lines().collect::<Vec<_>>();
    lines.sort_unstable();
    assert_eq!(lines, ["alpha", "failure", "zz_after"]);
    Ok(())
}

#[test]
fn actual_nested_targo_recovers_original_fixed_claim_and_refuses_widening() -> io::Result<()> {
    nested_targo(false)
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn actual_nested_fixed_frontdoor_reuses_the_parent_without_second_admission() -> io::Result<()> {
    nested_targo(true)
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn actual_selected_tool_root_uses_authenticated_fixed_continuation() -> io::Result<()> {
    let root = tempfile::tempdir()?;
    let frontend = env!("CARGO_BIN_EXE_targo");
    let mut command = Command::new(frontend);
    command
        .current_dir(root.path())
        .args([
            "--unverified",
            "resource",
            "fixed",
            "--cpus",
            "1",
            "--wait-seconds",
        ])
        .arg(ADMISSION_QUEUE_PATIENCE.as_secs().to_string())
        .args(["--", "fixed-tool", "--"])
        .arg(frontend)
        .args(["--unverified", "resource", "budget", "measure"])
        .stdin(Stdio::null());
    // The selected fixture is the known system-only frontend. Exercise that
    // declared environment without Cargo's test-image loader search input;
    // production retains/refuses every caller-supplied override instead.
    #[expect(
        clippy::disallowed_methods,
        reason = "the real system-only fixture deliberately excludes its test runner's loader search input without changing parent environment or original scheduling custody"
    )]
    for (name, _) in std::env::vars_os() {
        if name.as_encoded_bytes().starts_with(b"DYLD_")
            || name.as_encoded_bytes().starts_with(b"LD_")
        {
            command.env_remove(name);
        }
    }
    let output = command.output()?;
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report: serde_json::Value =
        serde_json::from_slice(&output.stdout).map_err(io::Error::other)?;
    assert_eq!(report["cpu_scope"]["kind"], "original_fixed");
    assert_eq!(report["cpu_scope"]["ceiling"], 1);
    // No unmanaged budget fallback can impersonate the original fixed reader.
    assert_eq!(report["authority"], "policy_data_only_no_admission");
    Ok(())
}

fn nested_targo(frontdoor: bool) -> io::Result<()> {
    use std::os::fd::AsRawFd;
    let root = tempfile::tempdir()?;
    git2::Repository::init(root.path()).unwrap();
    std::fs::create_dir(root.path().join("src"))?;
    std::fs::create_dir_all(root.path().join("nested/src"))?;
    for (at, name) in [
        (root.path().to_owned(), "native-fixed-parent"),
        (root.path().join("nested"), "native-fixed-child"),
    ] {
        std::fs::write(
            at.join("Cargo.toml"),
            format!("[package]\nname='{name}'\nversion='0.0.0'\nedition='2021'\n[workspace]\n"),
        )?;
        std::fs::write(at.join("src/lib.rs"), "pub fn value()->u32{1}\n")?;
    }
    std::fs::write(
        root.path().join("build.rs"),
        r#"
fn main() {
    let frontdoor=std::env::var_os("ACTUAL_NESTED_FIXED_FRONTDOOR").is_some();
    let invoke=|jobs:&str,exclusive:bool|{
        let mut command=std::process::Command::new(std::env::var_os("CARGO").unwrap());
        command.arg("--unverified");
        if frontdoor {
            command.args(["resource","fixed","--cpus","1"]);
            if exclusive {command.arg("--exclusive");}
            command.arg("--");
        }
        command.args(["check","--offline","--manifest-path","nested/Cargo.toml",
            "--target-dir","nested/target",jobs]).output().unwrap()
    };
    let original_record=std::fs::read(".git/build-slot.lock").unwrap();
    // A build-script descendant has the real authenticated fixed courier.
    // Exercise the actual native budget frontdoor before any nested build;
    // stale or incomplete advertisements must never become unmanaged data.
    assert!(std::env::var_os("TRUST_FIXED_CLAIM_HANDOFF_V1").is_some());
    let observe=|mode:u8| {
        let mut command=std::process::Command::new(std::env::var_os("CARGO").unwrap());
        command.args(["--unverified","resource","budget","measure"]);
        if mode==1 { command.env_remove("TRUST_FIXED_ADMISSION_FD_V1"); }
        if mode==2 { command.env("TRUST_FIXED_CLAIM_HANDOFF_V1","stale-or-malformed"); }
        command.output().unwrap()
    };
    let measured=observe(0);
    assert!(measured.status.success(),"{}",String::from_utf8_lossy(&measured.stderr));
    let measured=String::from_utf8(measured.stdout).unwrap();
    assert!(measured.contains("\"kind\":\"original_fixed\""),"{measured}");
    assert!(measured.contains("\"authority\":\"policy_data_only_no_admission\""),"{measured}");
    if frontdoor {
        // The selected native image must execute under this SAME courier and
        // GNU continuation. A std Command in this build script closes direct
        // packet FDs, so only the authenticated original importer can work.
        let frontend=std::env::var_os("CARGO").unwrap();
        let mut selected=std::process::Command::new(&frontend);
        selected.args(["--unverified","resource","fixed-tool","--"])
            .arg(&frontend)
            .args(["--unverified","resource","budget","measure"]);
        // Only this known system-only fixture's generated loader search is
        // excluded. Original GNU/fixed/SDK transport is never cleared.
        for (name,_) in std::env::vars_os() {
            if name.as_encoded_bytes().starts_with(b"DYLD_") || name.as_encoded_bytes().starts_with(b"LD_") {
                selected.env_remove(name);
            }
        }
        let selected=selected.output().unwrap();
        assert!(selected.status.success(),"{}",String::from_utf8_lossy(&selected.stderr));
        let selected=String::from_utf8(selected.stdout).unwrap();
        assert!(selected.contains("\"kind\":\"original_fixed\""),"{selected}");
        let refused=std::process::Command::new(&frontend)
            .args(["--unverified","resource","fixed-tool","--"])
            .arg(&frontend)
            .args(["--unverified","resource","budget","measure"])
            .env("DYLD_LIBRARY_PATH","/missing-selected-tool-loader")
            .output().unwrap();
        assert!(!refused.status.success());
        assert!(String::from_utf8_lossy(&refused.stderr).contains("nested command refuses loader overrides"),
            "{}",String::from_utf8_lossy(&refused.stderr));
        assert!(refused.stdout.is_empty(),"a selected tool ran under a refused loader override");
        assert_eq!(std::fs::read(".git/build-slot.lock").unwrap(),original_record);
    }
    for mode in [1,2] {
        let refused=observe(mode);
        assert!(!refused.status.success(),"uncaptured courier became successful policy data");
        assert!(!String::from_utf8_lossy(&refused.stdout).contains("unmanaged_policy"));
    }
    assert_eq!(std::fs::read(".git/build-slot.lock").unwrap(),original_record);
    if frontdoor {
        let upgrade=invoke("-j1",true);
        assert!(!upgrade.status.success());
        assert!(String::from_utf8_lossy(&upgrade.stderr)
            .contains("cannot upgrade shared original admission"),"{}",
            String::from_utf8_lossy(&upgrade.stderr));
        assert!(!std::path::Path::new("nested/target/debug").exists());
    }
    let widened=invoke("-j2",false);
    assert!(!widened.status.success());
    assert!(String::from_utf8_lossy(&widened.stderr)
        .contains("configured jobs exceed the original fixed command CPU ceiling 1"),"{}",
        String::from_utf8_lossy(&widened.stderr));
    assert!(!std::path::Path::new("nested/target/debug").exists());
    let inherited=invoke("-j1",false);
    assert!(inherited.status.success(),"{}",String::from_utf8_lossy(&inherited.stderr));
    assert!(std::path::Path::new("nested/target/debug").is_dir());
    assert_eq!(std::fs::read(".git/build-slot.lock").unwrap(),original_record,
        "nested frontdoor republished its parent's original worktree record");
    println!("cargo:warning=ACTUAL-NESTED-FIXED-TARGO-PASS");
}
"#,
    )?;
    let original = cargo_util::Jobserver::new(6)?;
    original.client().acquire_raw()?;
    let descriptor = original.pipe_descriptors().unwrap()[0].as_raw_fd();
    let flags = unsafe { libc::fcntl(descriptor, libc::F_GETFL) };
    let mut command = Command::new(env!("CARGO_BIN_EXE_targo"));
    command
        .current_dir(root.path())
        .args([
            "--unverified",
            "resource",
            "fixed",
            "--cpus",
            if frontdoor { "2" } else { "1" },
            "--wait-seconds",
        ])
        .arg(ADMISSION_QUEUE_PATIENCE.as_secs().to_string())
        .args([
            "--",
            "check",
            "--offline",
            if frontdoor { "-j2" } else { "-j1" },
        ])
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if frontdoor {
        command.env("ACTUAL_NESTED_FIXED_FRONTDOOR", "1");
    }
    original.configure_make(&mut command);
    let mut child = command.spawn()?;
    let stdout = child.stdout.take().unwrap();
    let stderr = child.stderr.take().unwrap();
    let (status, _, stderr) = capture_io(stdout, stderr, || child.wait());
    assert!(status.success(), "{status}: {stderr}");
    assert!(
        stderr.contains("ACTUAL-NESTED-FIXED-TARGO-PASS"),
        "{stderr}"
    );
    assert_eq!(original.client().available()?, 5);
    assert_eq!(unsafe { libc::fcntl(descriptor, libc::F_GETFL) }, flags);
    std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .open(root.path().join(".git/build-slot.lock"))?
        .try_lock()
        .unwrap();
    Ok(())
}

#[derive(Clone, Copy)]
enum Launch {
    Direct,
    Group,
    NativeEntry,
}

fn compile_gnu(launch: Launch) -> io::Result<()> {
    use std::os::fd::AsRawFd;
    let root = tempfile::tempdir()?;
    if matches!(launch, Launch::NativeEntry) {
        git2::Repository::init(root.path()).unwrap();
    }
    std::fs::create_dir(root.path().join("src"))?;
    std::fs::write(
        root.path().join("Cargo.toml"),
        "[package]\nname='fixed-gnu-compilation'\nversion='0.0.0'\nedition='2021'\n[workspace]\n",
    )?;
    std::fs::write(
        root.path().join("src/lib.rs"),
        "pub fn value() -> u32 { 7 }\n",
    )?;
    std::fs::write(
        root.path().join("build.rs"),
        r#"
use std::io::{Read, Write};
use std::os::unix::fs::OpenOptionsExt;
use std::time::{Duration, Instant};
fn main() {
    if std::env::var_os("NATIVE_FIXED_WORKTREE_CONTROL").is_some() {
        use std::os::fd::AsRawFd;
        extern "C" { fn flock(fd: i32, operation: i32) -> i32; }
        let lock = std::fs::OpenOptions::new().read(true).write(true)
            .open(".git/build-slot.lock").expect("native original worktree lock");
        assert_eq!(unsafe { flock(lock.as_raw_fd(), 2 | 4) }, -1,
            "native admission released its worktree before the actual build script");
        assert_eq!(std::io::Error::last_os_error().kind(), std::io::ErrorKind::WouldBlock);
        println!("cargo:warning=ACTUAL-NATIVE-WORKTREE-HELD");
    }
    let flags = std::env::var("CARGO_MAKEFLAGS").unwrap();
    assert_eq!(std::env::var("MAKEFLAGS").unwrap(), flags, "MAKEFLAGS escaped the restricted GNU server");
    assert_eq!(std::env::var("MFLAGS").unwrap(), flags, "MFLAGS escaped the restricted GNU server");
    let path = flags.split_whitespace().find_map(|v| v.strip_prefix("--jobserver-auth=fifo:")).expect("restricted native FIFO");
    #[cfg(target_os="macos")] let nonblock = 4;
    #[cfg(target_os="linux")] let nonblock = 2048;
    let mut read = std::fs::OpenOptions::new().read(true).custom_flags(nonblock).open(path).unwrap();
    let mut write = std::fs::OpenOptions::new().write(true).custom_flags(nonblock).open(path).unwrap();
    let deadline = Instant::now() + Duration::from_secs(10);
    let mut actual = Vec::new();
    while actual.is_empty() {
        let mut byte = [0];
        match read.read(&mut byte) {
            Ok(1) => actual.push(byte[0]),
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                assert!(Instant::now() < deadline, "real inherited credits unavailable");
                std::thread::sleep(Duration::from_millis(1));
            }
            other => panic!("unexpected GNU read {other:?}"),
        }
    }
    // The script may itself own one supplementary credit. It cannot demand
    // every credit while retaining its own; sample all further available ones.
    let until = Instant::now() + Duration::from_millis(100);
    while Instant::now() < until {
        let mut byte = [0];
        match read.read(&mut byte) {
            Ok(1) => { actual.push(byte[0]); assert!(actual.len() <= 2, "fixed ceiling widened"); }
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => std::thread::sleep(Duration::from_millis(1)),
            other => panic!("unexpected GNU read {other:?}"),
        }
    }
    write.write_all(&actual).unwrap();
    println!("cargo:warning=ACTUAL-GNU-RESTRICTED-{}", actual.len());
}
"#,
    )?;
    let original = cargo_util::Jobserver::new(6)?;
    original.client().acquire_raw()?;
    assert_eq!(original.client().available()?, 5);
    let descriptor = original.pipe_descriptors().unwrap()[0].as_raw_fd();
    let original_flags = unsafe { libc::fcntl(descriptor, libc::F_GETFL) };
    assert_ne!(original_flags, -1);
    let mut command = Command::new(env!("CARGO_BIN_EXE_targo"));
    command
        .current_dir(root.path())
        .env("CARGO_BUILD_JOBS", "3")
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if matches!(launch, Launch::NativeEntry) {
        command.env("NATIVE_FIXED_WORKTREE_CONTROL", "1");
        command.args([
            "--unverified",
            "resource",
            "fixed",
            "--cpus",
            "3",
            "--",
            "check",
            "--offline",
            "-j3",
        ]);
    } else {
        command.args(["--unverified", "check", "--offline", "-j3"]);
    }
    original.configure_make(&mut command);
    let (status, _stdout, stderr) = match launch {
        Launch::Direct => capture(actual_claim(3).prepare_command(command)?.spawn()?),
        Launch::Group => capture_group(
            actual_claim(3)
                .prepare_command(command)?
                .spawn_group_with_signal_forwarding()?,
        ),
        Launch::NativeEntry => {
            let mut child = command.spawn()?;
            let stdout = child.stdout.take().unwrap();
            let stderr = child.stderr.take().unwrap();
            capture_io(stdout, stderr, || child.wait())
        }
    };
    assert!(
        status.success(),
        "actual GNU compilation failed: {status}\n{stderr}"
    );
    assert!(
        stderr.contains("ACTUAL-GNU-RESTRICTED-1") || stderr.contains("ACTUAL-GNU-RESTRICTED-2"),
        "actual script did not acquire bounded credits: {stderr}"
    );
    assert!(
        root.path().join("target/debug").is_dir(),
        "actual fixture never compiled"
    );
    if matches!(launch, Launch::NativeEntry) {
        assert!(stderr.contains("ACTUAL-NATIVE-WORKTREE-HELD"), "{stderr}");
        std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .open(root.path().join(".git/build-slot.lock"))?
            .try_lock()
            .unwrap();
    }
    assert_eq!(
        original.client().available()?,
        5,
        "actual originals not returned"
    );
    assert_eq!(
        unsafe { libc::fcntl(descriptor, libc::F_GETFL) },
        original_flags
    );
    Ok(())
}

#[test]
fn actual_exclusive_quiet_claim_drives_native_targo_planning() -> io::Result<()> {
    let root = tempfile::tempdir()?;
    std::fs::create_dir(root.path().join("src"))?;
    std::fs::write(
        root.path().join("Cargo.toml"),
        "[package]\nname='exclusive-fixed-planning'\nversion='0.0.0'\nedition='2021'\n[workspace]\n",
    )?;
    std::fs::write(
        root.path().join("src/lib.rs"),
        "pub fn value() -> u32 { 7 }\n",
    )?;
    let claim = actual_claim_mode(1, true);
    let mut command = Command::new(env!("CARGO_BIN_EXE_targo"));
    command
        .current_dir(root.path())
        .args([
            "--unverified",
            "check",
            "--offline",
            "--unit-graph",
            "-Zunstable-options",
            "-j1",
        ])
        .env("CARGO_BUILD_JOBS", "1")
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let before = Instant::now();
    let prepared = claim.prepare_exclusive_command(command, Duration::from_secs(60))?;
    assert!(
        before.elapsed() >= Duration::from_secs(10),
        "quiet interval was skipped"
    );
    let (status, stdout, stderr) = capture(prepared.spawn()?);
    assert!(
        status.success(),
        "exclusive actual Targo refused: {status}\n{stderr}"
    );
    assert!(
        stdout.contains("exclusive-fixed-planning"),
        "original unit graph absent: {stdout}"
    );
    assert!(
        !root.path().join("target/debug/deps").exists(),
        "planning case compiled units"
    );
    Ok(())
}

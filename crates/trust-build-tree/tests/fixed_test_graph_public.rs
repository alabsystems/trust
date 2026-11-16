//! Actual ordinary test compilation and harnesses under the original fixed
//! owner. Compile under admission, then run outside it against a SHA-bound
//! immutable normal Targo. No private CPU domain or marker-based admission.

#![cfg(all(
    target_os = "macos",
    target_arch = "aarch64",
    feature = "native-cli-tests",
    feature = "native-exec"
))]

use std::io;
use std::os::fd::AsRawFd as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

// One real libtest unit, compiled from these retained Rust inputs by the
// selected genuine compiler. Positional scheduler observations grant nothing.
const LIBRARY: &str = r#"
#[cfg(test)] mod tests {
    use std::io::{Read,Write};
    use std::os::fd::{FromRawFd,AsRawFd};
    use std::os::unix::fs::{OpenOptionsExt,MetadataExt};
    #[repr(C)] struct PollFd { fd:i32, events:i16, revents:i16 }
    unsafe extern "C" { fn poll(fds:*mut PollFd,n:u32,timeout:i32)->i32; fn fcntl(fd:i32,cmd:i32,...)->i32; }
    #[test] fn original_fixed_harness() {
        assert_eq!(env!("ORIGINAL_COMPILED_INPUT"),"real-build-script-prerequisite");
        let root=std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
        assert_eq!(std::fs::read(root.join("compiled-prerequisite")).unwrap(),b"actual build input");
        let mode=std::env::var("NATIVE_FIXED_TEST_CASE").unwrap_or_else(|_|"cap2".into());
        let flags=std::env::var("CARGO_MAKEFLAGS").unwrap();
        let make=std::env::var("MAKEFLAGS").ok();
        let mflags=std::env::var("MFLAGS").ok();
        let threads=std::env::var("RUST_TEST_THREADS").ok();
        let cap=std::env::var("NATIVE_FIXED_TEST_CEILING").unwrap().parse::<usize>().unwrap();
        let auth=flags.split_whitespace().find_map(|s|s.strip_prefix("--jobserver-auth=")).unwrap();
        let (mut read,mut write)=if let Some(path)=auth.strip_prefix("fifo:") {
            (std::fs::OpenOptions::new().read(true).custom_flags(4).open(path).unwrap(),
             std::fs::OpenOptions::new().write(true).custom_flags(4).open(path).unwrap())
        } else {
            let mut fds=auth.split(',').map(|s|s.parse::<i32>().unwrap());
            unsafe{(std::fs::File::from_raw_fd(fds.next().unwrap()),std::fs::File::from_raw_fd(fds.next().unwrap()))}
        };
        if mode=="cancel" {
            // The existing queue cancels its owned target with SIGKILL. Hold
            // only this actual action's implicit credit, not an unreturnable
            // supplementary byte whose loss would correctly retain debt.
            assert_eq!(threads.as_deref(),Some("1"));
            assert_eq!(make.as_deref(),Some(flags.as_str()));
            assert_eq!(mflags.as_deref(),Some(flags.as_str()));
            assert!(auth.starts_with("fifo:"));
            let meta=read.metadata().unwrap();
            std::fs::write(root.join("harness-observed"),format!("credits=not-borrowed\nthreads={threads:?}\ncargo={flags:?}\nmake={make:?}\nmflags={mflags:?}\nread_device={}\nread_inode={}\n",meta.dev(),meta.ino())).unwrap();
            std::fs::write(root.join("harness-ready"),b"original queue action active").unwrap();
            let until=std::time::Instant::now()+std::time::Duration::from_secs(45);
            while std::time::Instant::now()<until {std::thread::sleep(std::time::Duration::from_millis(2));}
            std::fs::write(root.join("harness-cancel-expired"),b"actual target survived cancellation").unwrap();
            panic!("original queue failed to cancel its actual target");
        }
        let mut credits=Vec::new();
        let sampling_deadline=std::time::Instant::now()+std::time::Duration::from_secs(10);
        let sample=std::time::Duration::from_millis(150);
        let mut last=std::time::Instant::now();
        loop {
            let mut p=PollFd{fd:read.as_raw_fd(),events:1,revents:0};
            if unsafe{poll(&mut p,1,1)}>0 {
                let mut byte=[0];
                match read.read(&mut byte) {
                    Ok(1)=>{credits.push(byte[0]); last=std::time::Instant::now();},
                    Err(error) if matches!(error.kind(),std::io::ErrorKind::WouldBlock|std::io::ErrorKind::Interrupted)=>{},
                    other=>panic!("unexpected actual GNU read {other:?}"),
                }
            }
            if last.elapsed()>=sample || std::time::Instant::now()>=sampling_deadline {break;}
        }
        let sampling_expired=std::time::Instant::now()>=sampling_deadline;
        let meta=read.metadata().unwrap();
        let observation=format!("credits={}\nthreads={threads:?}\ncargo={flags:?}\nmake={make:?}\nmflags={mflags:?}\nread_device={}\nread_inode={}\nread_flags={}\n",credits.len(),meta.dev(),meta.ino(),unsafe{fcntl(read.as_raw_fd(),3)});
        std::fs::write(root.join("harness-observed"),&observation).unwrap();
        // Return every actual byte BEFORE any semantic assertion can fail.
        write.write_all(&credits).unwrap();
        println!("ACTUAL_FIXED_TEST_OBSERVED\n{observation}");
        assert!(!sampling_expired,"original GNU sampling deadline expired");
        assert!(credits.len()<=cap-1,"test escaped its original fixed GNU ceiling");
        assert_eq!(threads.as_deref(),Some("1"),"one default test action must own exactly one libtest thread");
        assert_eq!(make.as_deref(),Some(flags.as_str()),"MAKEFLAGS selected another pool");
        assert_eq!(mflags.as_deref(),Some(flags.as_str()),"MFLAGS selected another pool");
        assert!(auth.starts_with("fifo:"),"the actual fixed bridge was not retained");
        std::fs::write(root.join("harness-passed"),b"actual restricted harness").unwrap();
    }
}
"#;

fn selected_image() -> io::Result<trust_resource_provenance::program::HeldSystemCommand> {
    let path = PathBuf::from(
        std::env::var_os("TRUST_BUILD_TREE_TARGO").expect("select immutable actual normal Targo"),
    );
    let image = trust_resource_provenance::program::HeldSystemCommand::open(
        &path,
        Instant::now() + Duration::from_secs(30),
    )?;
    assert_eq!(
        image.observation().executable.sha256,
        std::env::var("TRUST_BUILD_TREE_TARGO_SHA256").unwrap()
    );
    Ok(image)
}

fn world(case: &str) -> io::Result<PathBuf> {
    let parent = std::env::var_os("TRUST_FIXED_TEST_ARTIFACT_ROOT")
        .expect("retain actual public qualification inputs");
    std::fs::create_dir_all(&parent)?;
    let root = tempfile::Builder::new().prefix("fixed-test-graph-").tempdir_in(parent)?.keep();
    let root = root.canonicalize()?;
    assert!(Command::new("/usr/bin/git").args(["init", "--quiet"]).arg(&root).status()?.success());
    std::fs::create_dir(root.join("src"))?;
    std::fs::write(
        root.join("Cargo.toml"),
        "[package]\nname='actual-fixed-test-graph'\nversion='0.0.0'\nedition='2021'\n[workspace]\n",
    )?;
    let library = if case == "failed-prerequisite" {
        "compile_error!(\"actual failed producing unit\");\n".to_owned()
    } else if case == "docs" {
        format!(
            "/// ```\n/// panic!(\"selected documentation must not disappear\");\n/// ```\npub fn documented() {{}}\n{LIBRARY}"
        )
    } else {
        LIBRARY.to_owned()
    };
    std::fs::write(root.join("src/lib.rs"), library)?;
    if case == "custom-runner" {
        std::fs::create_dir(root.join(".cargo"))?;
        std::fs::write(
            root.join(".cargo/config.toml"),
            "[target.aarch64-apple-darwin]\nrunner=['/usr/bin/false']\n",
        )?;
    }
    std::fs::write(
        root.join("build.rs"),
        "fn main(){std::fs::write(\"compiled-prerequisite\",b\"actual build input\").unwrap();println!(\"cargo:rustc-env=ORIGINAL_COMPILED_INPUT=real-build-script-prerequisite\");}\n",
    )?;
    Ok(root)
}

struct Capture {
    bytes: Vec<u8>,
    eof: bool,
    failure: Option<String>,
}
fn drain(
    mut stream: impl io::Read + std::os::fd::AsRawFd + Send + 'static,
    deadline: Instant,
) -> std::thread::JoinHandle<Capture> {
    std::thread::spawn(move || {
        let mut capture = Capture { bytes: Vec::new(), eof: false, failure: None };
        // Only this freshly created private output pipe's read description is
        // changed. Original GNU descriptors and flags are never touched.
        let flags = unsafe { libc::fcntl(stream.as_raw_fd(), libc::F_GETFL) };
        if flags < 0
            || unsafe { libc::fcntl(stream.as_raw_fd(), libc::F_SETFL, flags | libc::O_NONBLOCK) }
                < 0
        {
            capture.failure = Some(io::Error::last_os_error().to_string());
            return capture;
        }
        let mut buffer = [0; 65536];
        loop {
            if Instant::now() >= deadline {
                capture.failure = Some("original output drain deadline; EOF unavailable".into());
                return capture;
            }
            match stream.read(&mut buffer) {
                Ok(0) => {
                    capture.eof = true;
                    return capture;
                }
                Ok(size) => {
                    capture.bytes.extend_from_slice(&buffer[..size]);
                    if capture.bytes.len() > 4 * 1024 * 1024 {
                        capture.failure = Some("actual output exceeded its bound".into());
                        return capture;
                    }
                }
                Err(error)
                    if matches!(
                        error.kind(),
                        io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted
                    ) =>
                {
                    std::thread::sleep(Duration::from_millis(2))
                }
                Err(error) => {
                    capture.failure = Some(error.to_string());
                    return capture;
                }
            }
        }
    })
}

#[test]
fn actual_fixed_tests_share_the_compile_graph_and_original_restricted_gnu() -> io::Result<()> {
    run_actual_case()
        .inspect_err(|error| eprintln!("actual fixed-test fixture IO failure: {error:?}"))
}

fn run_actual_case() -> io::Result<()> {
    assert!(std::env::var_os("BUILD_SLOT_HELD").is_none(), "run after compiler admission ends");
    for key in ["CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS", "RUST_TEST_THREADS"] {
        assert!(std::env::var_os(key).is_none(), "fixture must own original {key}");
    }
    for key in [
        "CARGO_TARGET_DIR",
        "CARGO_BUILD_TARGET",
        "RUSTFLAGS",
        "CARGO_ENCODED_RUSTFLAGS",
        "RUSTC_WRAPPER",
        "RUSTC_WORKSPACE_WRAPPER",
        "CARGO_BUILD_RUSTC_WRAPPER",
        "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
    ] {
        assert!(
            std::env::var_os(key).is_none(),
            "actual compiler/output qualification refuses {key}"
        );
    }
    let case = std::env::var("TRUST_FIXED_TEST_CASE").unwrap_or_else(|_| "cap2".into());
    assert!(
        matches!(
            case.as_str(),
            "cap1"
                | "cap2"
                | "failed-prerequisite"
                | "cancel"
                | "docs"
                | "custom-runner"
                | "required-missing"
                | "no-run"
                | "thread-widen"
        ),
        "unsupported actual case"
    );
    let cap = if case == "cap1" { "1" } else { "2" };
    let image = selected_image()?;
    let root = world(&case)?;
    let original = jobserver_utils::Jobserver::new(6)?;
    original.client().acquire_raw()?;
    assert_eq!(original.client().available()?, 5);
    let descriptors = original.pipe_descriptors().unwrap();
    let flags =
        descriptors.each_ref().map(|fd| unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFL) });
    assert!(flags.iter().all(|&flag| flag >= 0));
    let mut command = Command::new(image.program());
    command
        .current_dir(&root)
        .args([
            "--unverified",
            "resource",
            "fixed",
            "--cpus",
            cap,
            "--wait-seconds",
            "60",
            "--",
            "test",
            "--offline",
            "--message-format=json",
        ])
        .arg(format!("-j{cap}"))
        .env("CARGO_BUILD_JOBS", cap)
        .env("NATIVE_FIXED_TEST_CEILING", cap)
        .env("NATIVE_FIXED_TEST_CASE", &case)
        .env(
            "RUSTC",
            std::env::var_os("TRUST_FIXED_TEST_COMPILER").expect("select genuine compiler"),
        )
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if case != "docs" {
        command.arg("--lib");
    }
    match case.as_str() {
        "required-missing" => {
            command.args(["--require-test-bin", "missing-selected-binary"]);
        }
        "no-run" => {
            command.arg("--no-run");
        }
        "thread-widen" => {
            command.args(["--", "--test-threads=32"]);
        }
        _ => {}
    }
    // No test-jobs override: the actual default of one is the regression.
    original.configure_make(&mut command);
    let mut child = command.spawn()?;
    let deadline = Instant::now() + Duration::from_secs(120);
    let drain_deadline = deadline + Duration::from_secs(15);
    let stdout = drain(child.stdout.take().unwrap(), drain_deadline);
    let stderr = drain(child.stderr.take().unwrap(), drain_deadline);
    let mut cancelled = false;
    let mut watchdog = 0;
    let mut wait_deadline = deadline;
    let waited = (|| -> io::Result<std::process::ExitStatus> {
        loop {
            if let Some(status) = child.try_wait()? {
                break Ok(status);
            }
            if case == "cancel" && !cancelled && root.join("harness-ready").is_file() {
                if std::fs::read(root.join("harness-ready"))? != b"original queue action active" {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "unexpected native readiness bytes",
                    ));
                }
                if unsafe { libc::kill(child.id() as i32, libc::SIGTERM) } != 0 {
                    return Err(io::Error::last_os_error());
                }
                cancelled = true;
            }
            if Instant::now() >= wait_deadline {
                // Address only this actual unreaped child. Do not reconstruct its
                // separately owned group's cancellation authority from PID data.
                let signal = if watchdog == 0 { libc::SIGTERM } else { libc::SIGKILL };
                if watchdog >= 2 {
                    return Err(io::Error::new(
                        io::ErrorKind::TimedOut,
                        format!(
                            "owned root wait remains unknown; retained world {}",
                            root.display()
                        ),
                    ));
                }
                let rc = unsafe { libc::kill(child.id() as i32, signal) };
                if rc != 0 && io::Error::last_os_error().raw_os_error() != Some(libc::ESRCH) {
                    return Err(io::Error::last_os_error());
                }
                watchdog += 1;
                wait_deadline = Instant::now() + Duration::from_secs(5);
            }
            std::thread::sleep(Duration::from_millis(2));
        }
    })();
    let out = stdout.join().unwrap();
    let err = stderr.join().unwrap();
    // Observe BEFORE any fallible archival write. Shared ENOSPC must not
    // replace the real child's captured status/output with a silent fixture Err.
    println!("retained fixed-test world={} wait={waited:?}", root.display());
    println!(
        "stdout={}\nstderr={}",
        String::from_utf8_lossy(&out.bytes),
        String::from_utf8_lossy(&err.bytes)
    );
    let lifecycle = format!(
        "wait={waited:?}\nwatchdog={watchdog}\nstdout_eof={} failure={:?}\nstderr_eof={} failure={:?}\n",
        out.eof, out.failure, err.eof, err.failure
    );
    for (name, bytes) in [
        ("actual-stdout", out.bytes.as_slice()),
        ("actual-stderr", err.bytes.as_slice()),
        ("actual-lifecycle", lifecycle.as_bytes()),
    ] {
        std::fs::write(root.join(name), bytes).inspect_err(|error| {
            eprintln!(
                "actual fixed-test archival stage={name} world={} error={error:?}",
                root.display()
            )
        })?;
    }
    let stdout = out.bytes;
    let stderr = err.bytes;
    let status = match waited {
        Ok(status) => status,
        Err(error) => {
            // Unknown is not owning reap/group closure. Keep the actual child
            // observation; no successful settlement or retry follows it.
            std::mem::forget(child);
            return Err(error);
        }
    };
    assert_eq!(
        watchdog, 0,
        "fixture watchdog intervened; actual status alone is not successful custody"
    );
    assert!(
        out.eof && err.eof && out.failure.is_none() && err.failure.is_none(),
        "actual output did not close; observations retained"
    );
    assert_eq!(original.client().available()?, 5, "original GNU bytes were not returned");
    assert_eq!(
        descriptors.each_ref().map(|fd| unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFL) }),
        flags
    );
    image.validate(Instant::now() + Duration::from_secs(30))?;
    let rows = json_rows(&stdout);
    let running =
        rows.iter().filter(|r| r["reason"] == "test-execution" && r["state"] == "running").count();
    match case.as_str() {
        "failed-prerequisite" => {
            assert!(!status.success());
            // --message-format=json sends the real compiler diagnostic to
            // stdout; stderr contains only Cargo's aggregate failure line.
            let source = root.join("src/lib.rs");
            assert!(
                rows.iter().any(|row| row["reason"] == "compiler-message"
                    && row["trust_compile_mode"] == "test"
                    && row["target"]["src_path"].as_str() == source.to_str()
                    && row["message"]["level"] == "error"
                    && row["message"]["message"] == "actual failed producing unit"),
                "missing this actual producing unit's native compiler error"
            );
            assert!(!root.join("harness-observed").exists());
            assert_eq!(running, 0, "failed compiler admitted its dependent harness");
            assert!(rows.iter().any(|r| r["reason"] == "test-execution"
                && r["state"] == "blocked"
                && r["total"] == 1));
            return Ok(());
        }
        "docs" | "custom-runner" | "required-missing" | "thread-widen" => {
            assert!(!status.success());
            let reason = match case.as_str() {
                "docs" => "documentation tests is unavailable",
                "custom-runner" => "does not support custom target runners",
                "required-missing" => "must select exactly one native harness",
                "thread-widen" => "owns libtest's thread budget",
                _ => unreachable!(),
            };
            assert!(String::from_utf8_lossy(&stderr).contains(reason), "wrong refusal");
            assert!(
                !root.join("compiled-prerequisite").exists(),
                "unsupported population dispatched a compiler/build script"
            );
            assert!(!root.join("harness-observed").exists());
            assert_eq!(running, 0);
            return Ok(());
        }
        "no-run" => {
            assert!(status.success());
            assert!(root.join("compiled-prerequisite").is_file());
            assert!(!root.join("harness-observed").exists());
            assert_eq!(running, 0);
            assert!(rows.iter().any(|r| r["reason"] == "compiler-artifact"
                && r["profile"]["test"] == true
                && r["executable"].as_str().is_some_and(|p| Path::new(p).is_file())));
            return Ok(());
        }
        "cancel" => {
            assert!(cancelled, "original harness never reached actual cancellation");
            assert!(!status.success(), "actual cancellation became successful root completion");
            assert!(
                !root.join("harness-cancel-expired").exists(),
                "actual target outlived cancellation"
            );
            assert!(!root.join("harness-passed").exists());
            assert_eq!(running, 1);
            check_graph(&root, &stdout, true);
            return Ok(());
        }
        _ => {}
    }
    assert!(root.join("harness-observed").is_file(), "actual compiled harness never observed GNU");
    println!("{}", std::fs::read_to_string(root.join("harness-observed"))?);
    assert!(status.success(), "actual fixed test failed; original observations retained");
    assert_eq!(std::fs::read(root.join("harness-passed"))?, b"actual restricted harness");
    check_graph(&root, &stdout, false);
    Ok(())
}

fn check_graph(root: &Path, stdout: &[u8], cancelled: bool) {
    let rows = json_rows(stdout);
    let (compiled, artifact) = rows
        .iter()
        .enumerate()
        .find_map(|(index, row)| {
            (row["reason"] == "compiler-artifact" && row["profile"]["test"] == true)
                .then(|| row["executable"].as_str().map(|path| (index, path)))
                .flatten()
        })
        .expect("missing actual producing test artifact");
    assert_eq!(rows[compiled]["fresh"], false, "fresh private world did not execute its producer");
    let events = rows
        .iter()
        .enumerate()
        .filter(|(_, row)| row["reason"] == "test-execution")
        .collect::<Vec<_>>();
    let running = events
        .iter()
        .find(|(_, row)| row["state"] == "running")
        .expect("test did not use original compiler queue");
    assert!(compiled < running.0, "test ran before actual producing compiler artifact");
    for (_, event) in &events {
        assert_eq!(event["total"], 1);
        assert_eq!(event["index"], 0);
        assert_eq!(event["weight"], 1);
        assert_eq!(event["prerequisite_artifact"], artifact);
    }
    assert_eq!(
        events.iter().filter(|(_, r)| r["state"] == "running").count(),
        1,
        "action dispatched more than once"
    );
    let terminal = events
        .iter()
        .filter(|(_, r)| {
            r["state"] == "passed" || r["state"] == "failed" || r["state"] == "blocked"
        })
        .collect::<Vec<_>>();
    assert_eq!(terminal.len(), 1, "missing or repeated action terminal");
    if cancelled {
        assert_eq!(terminal[0].1["state"], "failed");
    } else {
        assert_eq!(terminal[0].1["state"], "passed");
        assert_eq!(terminal[0].1["exit_code"], 0);
    }
    assert!(Path::new(artifact).starts_with(root.join("target")));
}

fn json_rows(stdout: &[u8]) -> Vec<serde_json::Value> {
    String::from_utf8_lossy(stdout)
        .lines()
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
        .collect()
}

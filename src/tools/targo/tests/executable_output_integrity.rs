//! Native validity and reuse of compiler-declared executable outputs.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

#![cfg(unix)]

use std::fs;

use cargo_test_support::prelude::*;
use cargo_test_support::{basic_manifest, project, rustc_host};

// Trust: reproduce a successful native compiler whose linker leaves a damaged
// executable. The fixture runs the real host C linker; it does not fake rustc,
// compiler messages, native owners or proof/evidence outcomes.
#[cfg(unix)]
fn native_executable_damage_linker() -> cargo_test_support::Project {
    let linker = project()
        .at("executable-damage-linker")
        .file("Cargo.toml", &basic_manifest("executable-damage-linker", "0.1.0"))
        .file(
            "src/main.rs",
            r#"
use std::env;
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::os::unix::ffi::OsStrExt;
use std::path::PathBuf;
use std::process::{Command, exit};
fn main() {
    let args = env::args_os().skip(1).collect::<Vec<_>>();
    let status = Command::new("cc").args(&args).status().unwrap();
    if !status.success() { exit(status.code().unwrap_or(1)); }
    let output = PathBuf::from(args.windows(2).find(|pair| pair[0] == "-o").unwrap()[1].clone());
    let output = if output.is_absolute() { output } else { env::current_dir().unwrap().join(output) };
    let record = PathBuf::from(env::var_os("TARGO_TEST_LINK_OUTPUT").unwrap());
    fs::write(&record, output.as_os_str().as_bytes()).unwrap();
    let mut count = OpenOptions::new().create(true).append(true).open(record.with_extension("count")).unwrap();
    count.write_all(b"linked\n").unwrap();
    match env::var("TARGO_TEST_LINK_DAMAGE").unwrap_or_default().as_str() {
        "empty" => { OpenOptions::new().write(true).truncate(true).open(&output).unwrap(); }
        "directory" => { fs::remove_file(&output).unwrap(); fs::create_dir(&output).unwrap(); }
        "" => {}
        other => panic!("unknown fixture damage {other}"),
    }
}
"#,
        )
        .build();
    linker
        .process(&snapbox::cmd::cargo_bin!("targo"))
        .args(&["--unverified", "build"])
        .run();
    linker
}

#[cfg(unix)]
fn native_executable_project(
    linker: &cargo_test_support::Project,
    name: &str,
) -> cargo_test_support::Project {
    project()
        .at(name)
        .file(
            "Cargo.toml",
            &format!(
                "{}\n[profile.dev]\ndebug = 0\nstrip = \"none\"\n",
                basic_manifest("foo", "0.1.0")
            ),
        )
        .file(
            "src/main.rs",
            "fn main() { println!(\"actual executable\"); }",
        )
        .file(
            ".cargo/config.toml",
            &format!(
                "[target.{}]\nlinker = {:?}\n",
                rustc_host(),
                linker.bin("executable-damage-linker")
            ),
        )
        .build()
}

#[cfg(unix)]
fn native_artifact(stdout: &[u8]) -> serde_json::Value {
    stdout
        .split(|byte| *byte == b'\n')
        .filter_map(|line| serde_json::from_slice::<serde_json::Value>(line).ok())
        .find(|row| row["reason"] == "compiler-artifact" && row["target"]["name"] == "foo")
        .expect("actual foo artifact message")
}

#[cargo_test]
#[cfg(unix)]
fn native_successful_compiler_cannot_publish_empty_or_nonregular_executable() {
    use std::os::unix::ffi::OsStrExt;
    let linker = native_executable_damage_linker();
    for damage in ["empty", "directory"] {
        let p = native_executable_project(&linker, damage);
        let record = p.root().join("actual-link-output");
        let output = p
            .process(&snapbox::cmd::cargo_bin!("targo"))
            .args(&["--unverified", "build", "--message-format=json"])
            .env("TARGO_TEST_LINK_OUTPUT", &record)
            .env("TARGO_TEST_LINK_DAMAGE", damage)
            .with_status(101)
            .with_stderr_contains(if damage == "empty" {
                "[ERROR] declared executable output is empty: [..]"
            } else {
                "[ERROR] declared executable output is not a regular file: [..]"
            })
            .run();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains(if damage == "empty" {
                "declared executable output is empty"
            } else {
                "declared executable output is not a regular file"
            }),
            "compiler must succeed before Targo refuses actual output: {stderr}"
        );
        let declared = fs::read(&record).unwrap();
        let declared = std::path::Path::new(std::ffi::OsStr::from_bytes(&declared));
        let actual = fs::symlink_metadata(declared).unwrap();
        if damage == "empty" {
            assert!(actual.is_file());
            assert_eq!(actual.len(), 0);
        } else {
            assert!(actual.is_dir());
        }
        assert!(
            !p.bin("foo").exists(),
            "invalid output must not become a public executable"
        );
        assert!(
            !output.stdout.split(|b| *b == b'\n').any(|line| {
                serde_json::from_slice::<serde_json::Value>(line).is_ok_and(|row| {
                    row["reason"] == "compiler-artifact" && row["target"]["name"] == "foo"
                })
            }),
            "invalid executable must not receive a successful artifact message"
        );
    }
}

// Trust: this is deliberately an old internally matching damaged-cache case,
// not only an ordinary byte mismatch already caught by output receipts. The
// cache JSON is DATA: editing its hash must never admit an invalid executable.
#[cfg(unix)]
fn match_cached_zero_receipt(root: &std::path::Path, executable: &std::path::Path) -> usize {
    let key = cargo_util::Sha256::new()
        .update(executable.as_os_str().as_encoded_bytes())
        .finish_hex();
    let empty = cargo_util::Sha256::new().finish_hex();
    let mut changed = 0;
    for entry in fs::read_dir(root).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_dir() {
            changed += match_cached_zero_receipt(&entry.path(), executable);
        } else if entry
            .file_name()
            .to_str()
            .is_some_and(|name| name.starts_with("outputs-") && name.ends_with(".json"))
        {
            let path = entry.path();
            let mut receipt: serde_json::Value =
                serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
            let mut matched = false;
            for output in receipt["outputs"].as_array_mut().unwrap() {
                if output["path_sha256"] == key {
                    output["size"] = 0.into();
                    output["sha256"] = empty.clone().into();
                    matched = true;
                }
            }
            if matched {
                fs::write(path, serde_json::to_vec(&receipt).unwrap()).unwrap();
                changed += 1;
            }
        }
    }
    changed
}

#[cargo_test]
#[cfg(unix)]
fn native_matching_cached_zero_executable_is_rebuilt_then_reused_warm() {
    use std::os::unix::ffi::OsStrExt;
    let linker = native_executable_damage_linker();
    let p = native_executable_project(&linker, "cached-executable");
    let record = p.root().join("actual-link-output");
    let run = || {
        let mut cmd = p.process(&snapbox::cmd::cargo_bin!("targo"));
        cmd.args(&["--unverified", "build", "--message-format=json"])
            .env("TARGO_TEST_LINK_OUTPUT", &record);
        cmd
    };
    let first = run().run();
    assert_eq!(native_artifact(&first.stdout)["fresh"], false);
    let declared = fs::read(&record).unwrap();
    let declared = std::path::Path::new(std::ffi::OsStr::from_bytes(&declared));
    assert!(fs::metadata(declared).unwrap().len() > 0);
    fs::OpenOptions::new()
        .write(true)
        .truncate(true)
        .open(declared)
        .unwrap();
    assert_eq!(fs::metadata(declared).unwrap().len(), 0);
    assert_eq!(match_cached_zero_receipt(&p.build_dir(), declared), 1);
    let repaired = run().run();
    assert_eq!(
        native_artifact(&repaired.stdout)["fresh"],
        false,
        "matching zero receipt cannot authorize freshness"
    );
    assert!(fs::metadata(declared).unwrap().len() > 0);
    p.process(&p.bin("foo"))
        .with_stdout_data("actual executable\n".raw())
        .run();
    assert_eq!(
        fs::read_to_string(record.with_extension("count"))
            .unwrap()
            .lines()
            .count(),
        2
    );
    let warm = run().run();
    assert_eq!(native_artifact(&warm.stdout)["fresh"], true);
    assert_eq!(
        fs::read_to_string(record.with_extension("count"))
            .unwrap()
            .lines()
            .count(),
        2,
        "valid warm reuse must avoid relinking"
    );
}

#[cargo_test]
#[cfg(unix)]
fn native_check_metadata_does_not_require_a_linked_executable() {
    let linker = native_executable_damage_linker();
    let p = native_executable_project(&linker, "metadata-only");
    let record = p.root().join("actual-link-output");
    let result = p
        .process(&snapbox::cmd::cargo_bin!("targo"))
        .args(&["--unverified", "check", "--message-format=json"])
        .env("TARGO_TEST_LINK_OUTPUT", &record)
        .env("TARGO_TEST_LINK_DAMAGE", "empty")
        .run();
    assert!(native_artifact(&result.stdout)["executable"].is_null());
    assert!(
        !record.exists(),
        "metadata-only compilation must not invoke the linker"
    );
}

#[cargo_test]
#[cfg(unix)]
fn native_build_script_executable_is_checked_before_it_can_run() {
    let linker = native_executable_damage_linker();
    let p = native_executable_project(&linker, "build-script-executable");
    p.change_file(
        "build.rs",
        "fn main() { std::fs::write(\"build-script-ran\", b\"ran\").unwrap(); }",
    );
    let record = p.root().join("actual-link-output");
    let result = p
        .process(&snapbox::cmd::cargo_bin!("targo"))
        .args(&["--unverified", "build"])
        .env("TARGO_TEST_LINK_OUTPUT", &record)
        .env("TARGO_TEST_LINK_DAMAGE", "empty")
        .with_status(101)
        .with_stderr_contains("[ERROR] declared executable output is empty: [..]")
        .run();
    let stderr = String::from_utf8_lossy(&result.stderr);
    assert!(
        stderr.contains("declared executable output is empty"),
        "invalid build-script output must be refused at compilation: {stderr}"
    );
    assert!(!p.root().join("build-script-ran").exists());
    assert!(!p.bin("foo").exists());
}

#[cargo_test]
#[cfg(unix)]
fn native_compiler_query_and_explicit_emit_keep_their_actual_output_routes() {
    let linker = native_executable_damage_linker();
    let p = native_executable_project(&linker, "query-output");
    let record = p.root().join("actual-link-output");
    let result = p
        .process(&snapbox::cmd::cargo_bin!("targo"))
        .args(&[
            "--unverified",
            "rustc",
            "--bin",
            "foo",
            "--",
            "--print",
            "cfg",
        ])
        .env("TARGO_TEST_LINK_OUTPUT", &record)
        .env("TARGO_TEST_LINK_DAMAGE", "empty")
        .run();
    assert!(String::from_utf8_lossy(&result.stdout).contains("target_arch="));
    assert!(!record.exists(), "a real cfg query must not link a binary");
    assert!(!p.bin("foo").exists());
    let metadata = p.root().join("explicit-metadata.rmeta");
    p.process(&snapbox::cmd::cargo_bin!("targo"))
        .args(&["--unverified", "rustc", "--bin", "foo", "--"])
        .arg(format!("--emit=metadata={}", metadata.display()))
        .env("TARGO_TEST_LINK_OUTPUT", &record)
        .run();
    assert!(metadata.is_file());
    // Cargo also supplies its ordinary link emission. An added --emit selects
    // metadata in addition to that output; it does not promise a metadata-only
    // compiler invocation. Zero-length bin metadata remains legitimate.
    p.process(&p.bin("foo"))
        .with_stdout_data("actual executable\n".raw())
        .run();
    let renamed_project = native_executable_project(&linker, "renamed-output");
    let renamed_record = renamed_project.root().join("actual-link-output");
    renamed_project
        .process(&snapbox::cmd::cargo_bin!("targo"))
        .args(&[
            "--unverified",
            "rustc",
            "--bin",
            "foo",
            "--",
            "-C",
            "extra-filename=-caller",
        ])
        .env("TARGO_TEST_LINK_OUTPUT", &renamed_record)
        .run();
    use std::os::unix::ffi::OsStrExt;
    let renamed = fs::read(&renamed_record).unwrap();
    let renamed = std::path::Path::new(std::ffi::OsStr::from_bytes(&renamed));
    assert!(
        renamed
            .file_name()
            .unwrap()
            .to_string_lossy()
            .contains("-caller")
    );
    renamed_project
        .process(renamed)
        .with_stdout_data("actual executable\n".raw())
        .run();
}

/// A real native Unit lock holds both clients after dirty planning but before
/// either can repair the same damaged cache entry. Public artifact directories
/// differ so the test cannot pass by serializing on their outer directory lock.
#[cargo_test]
#[cfg(unix)]
fn native_concurrent_damaged_executable_has_one_repair_producer_and_warm_reuse() {
    use std::io::{BufRead as _, BufReader, Read as _};
    use std::os::unix::{ffi::OsStrExt as _, process::CommandExt as _};
    use std::process::{Child, Command, Output, Stdio};
    use std::sync::mpsc;
    use std::thread::{self, JoinHandle};
    use std::time::{Duration, Instant};
    use targo::util::{Filesystem, GlobalContext};

    struct RunningNative {
        child: Child,
        stdout: Option<JoinHandle<Vec<u8>>>,
        stderr: Option<JoinHandle<Vec<u8>>>,
        evidence: std::path::PathBuf,
    }
    impl RunningNative {
        fn start(
            mut command: Command,
            which: usize,
            ready: mpsc::Sender<usize>,
            evidence: std::path::PathBuf,
        ) -> Self {
            fs::create_dir_all(&evidence).unwrap();
            // Every cancellation below names only this actual owned process group.
            command.process_group(0);
            let mut child = command
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .unwrap();
            let mut stdout = child.stdout.take().unwrap();
            let stderr = child.stderr.take().unwrap();
            let stdout = thread::spawn(move || {
                let mut bytes = Vec::new();
                stdout.read_to_end(&mut bytes).unwrap();
                bytes
            });
            let stderr = thread::spawn(move || {
                let mut bytes = Vec::new();
                let mut announced = false;
                for line in BufReader::new(stderr).split(b'\n') {
                    let line = line.unwrap();
                    if !announced && String::from_utf8_lossy(&line).contains("Compiling foo ") {
                        // The native dirty Work was selected before its exclusive
                        // Unit lock can be acquired. This is observed process output,
                        // never elapsed time or a fabricated completion.
                        let _ = ready.send(which);
                        announced = true;
                    }
                    bytes.extend_from_slice(&line);
                    bytes.push(b'\n');
                }
                bytes
            });
            Self {
                child,
                stdout: Some(stdout),
                stderr: Some(stderr),
                evidence,
            }
        }
        fn finish(mut self) -> Output {
            let output = Output {
                status: self.child.wait().unwrap(),
                stdout: self.stdout.take().unwrap().join().unwrap(),
                stderr: self.stderr.take().unwrap().join().unwrap(),
            };
            fs::write(self.evidence.join("stdout"), &output.stdout).unwrap();
            fs::write(self.evidence.join("stderr"), &output.stderr).unwrap();
            output
        }
    }
    impl Drop for RunningNative {
        fn drop(&mut self) {
            if self.child.try_wait().ok().flatten().is_none() {
                // The unreaped owned leader cannot have its PID reused. Its
                // group was created by start(), never selected from a path/report.
                unsafe {
                    libc::kill(-(self.child.id() as i32), libc::SIGKILL);
                }
                let _ = self.child.wait();
            }
            if let Some(reader) = self.stdout.take() {
                if let Ok(bytes) = reader.join() {
                    let _ = fs::write(self.evidence.join("stdout"), bytes);
                }
            }
            if let Some(reader) = self.stderr.take() {
                if let Ok(bytes) = reader.join() {
                    let _ = fs::write(self.evidence.join("stderr"), bytes);
                }
            }
            if thread::panicking() {
                eprintln!(
                    "retained actual native client evidence: {}",
                    self.evidence.display()
                );
            }
        }
    }

    let linker = native_executable_damage_linker();
    let p = native_executable_project(&linker, "concurrent-executable");
    p.change_file(
        ".cargo/config.toml",
        &format!(
            "[build]\nbuild-dir = 'shared-build'\n[target.{}]\nlinker = {:?}\n",
            rustc_host(),
            linker.bin("executable-damage-linker")
        ),
    );
    let record = p.root().join("actual-link-output");
    let command = |target: &str| {
        let mut cmd = p.process(&snapbox::cmd::cargo_bin!("targo"));
        cmd.args(&[
            "--unverified",
            "build",
            "-Zfine-grain-locking",
            "-Zbuild-analysis",
            "-Zmem-stats",
            "--config",
            "build.analysis.enabled=true",
            "--message-format=json",
            "--target-dir",
            target,
        ])
        // Use the genuine engineering binary's own dev/nightly support.
        // Do not manufacture a toolchain/channel to bypass this feature gate.
        .env_remove("__CARGO_TEST_CHANNEL_OVERRIDE_DO_NOT_USE_THIS")
        .env("TARGO_TEST_LINK_OUTPUT", &record);
        cmd
    };
    let compiler_starts = |stdout: &[u8]| {
        let sessions = stdout
            .split(|byte| *byte == b'\n')
            .filter_map(|line| serde_json::from_slice::<serde_json::Value>(line).ok())
            .filter(|row| row["reason"] == "build-analysis-session")
            .collect::<Vec<_>>();
        assert_eq!(sessions.len(), 1, "one actual build-analysis run identity");
        let id = sessions[0]["run_id"].as_str().unwrap();
        let output = p
            .process(&snapbox::cmd::cargo_bin!("targo"))
            .args(&[
                "-Zbuild-analysis",
                "report",
                "execution",
                "--id",
                id,
                "--json",
            ])
            .env_remove("__CARGO_TEST_CHANNEL_OVERRIDE_DO_NOT_USE_THIS")
            .run();
        let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(report["run_id"], id);
        assert_eq!(report["schema"], "targo-execution-report-v1");
        assert_eq!(report["graph_outcome"], "succeeded");
        assert_eq!(
            report["compiler_activity"]["availability"], "complete",
            "unavailable accounting must not be interpreted as zero processes"
        );
        report["compiler_activity"]["successful_primary_processes"]
            .as_u64()
            .unwrap()
    };
    let first = command("initial-target").run();
    assert_eq!(compiler_starts(&first.stdout), 1);
    assert_eq!(native_artifact(&first.stdout)["fresh"], false);
    let declared = fs::read(&record).unwrap();
    let declared = std::path::Path::new(std::ffi::OsStr::from_bytes(&declared));
    assert!(fs::metadata(declared).unwrap().len() > 0);
    let fingerprints = p
        .glob("shared-build/debug/build/foo/*/fingerprint/bin-foo")
        .map(Result::unwrap)
        .collect::<Vec<_>>();
    assert_eq!(fingerprints.len(), 1, "one real native executable Unit");
    let unit_lock = fingerprints[0]
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join(".lock");
    let gctx = GlobalContext::default().unwrap();
    let held = Filesystem::new(p.root())
        .open_ro_shared(
            &unit_lock,
            &gctx,
            "actual damaged executable repair barrier",
        )
        .unwrap();
    fs::OpenOptions::new()
        .write(true)
        .truncate(true)
        .open(declared)
        .unwrap();
    assert_eq!(fs::metadata(declared).unwrap().len(), 0);
    assert_eq!(
        match_cached_zero_receipt(&p.root().join("shared-build"), declared),
        1
    );
    assert_eq!(
        fs::read_to_string(record.with_extension("count"))
            .unwrap()
            .lines()
            .count(),
        1
    );

    let (ready, observed) = mpsc::channel();
    let mut children = vec![
        RunningNative::start(
            command("target-a").build_command(),
            0,
            ready.clone(),
            linker.root().join("concurrent-evidence/client-a"),
        ),
        RunningNative::start(
            command("target-b").build_command(),
            1,
            ready,
            linker.root().join("concurrent-evidence/client-b"),
        ),
    ];
    let mut dirty = [false; 2];
    for _ in 0..2 {
        let which = observed
            .recv_timeout(cargo_test_support::slow_cpu_multiplier(60))
            .expect("both actual clients must plan the damaged Unit before lock release");
        assert!(!dirty[which], "each original client announces once");
        dirty[which] = true;
    }
    assert_eq!(dirty, [true, true]);
    assert!(
        children
            .iter_mut()
            .all(|client| client.child.try_wait().unwrap().is_none())
    );
    assert_eq!(
        fs::read_to_string(record.with_extension("count"))
            .unwrap()
            .lines()
            .count(),
        1,
        "actual shared Unit lock prevents a repairing linker before release"
    );
    assert_eq!(fs::metadata(declared).unwrap().len(), 0);
    drop(held);

    let deadline = Instant::now() + cargo_test_support::slow_cpu_multiplier(60);
    while children
        .iter_mut()
        .any(|client| client.child.try_wait().unwrap().is_none())
    {
        assert!(
            Instant::now() < deadline,
            "actual concurrent repair did not finish"
        );
        // Only pace observation of owned Child states. Contention and ordering
        // above are established by the actual lock and process messages.
        thread::sleep(Duration::from_millis(10));
    }
    let results = children
        .into_iter()
        .map(RunningNative::finish)
        .collect::<Vec<_>>();
    for result in &results {
        assert!(
            result.status.success(),
            "native repair client failed: {}",
            String::from_utf8_lossy(&result.stderr)
        );
    }
    let mut fresh = results
        .iter()
        .map(|result| native_artifact(&result.stdout)["fresh"].as_bool().unwrap())
        .collect::<Vec<_>>();
    fresh.sort();
    let mut starts = results
        .iter()
        .map(|result| compiler_starts(&result.stdout))
        .collect::<Vec<_>>();
    starts.sort();
    assert_eq!(
        starts,
        [0, 1],
        "one actual compiler-unit process, with complete owning-wait accounting"
    );
    assert_eq!(
        fresh,
        [false, true],
        "one actual repair and one post-lock reuse"
    );
    assert!(fs::metadata(declared).unwrap().len() > 0);
    assert_eq!(
        fs::read_to_string(record.with_extension("count"))
            .unwrap()
            .lines()
            .count(),
        2,
        "the shared damaged executable has exactly one actual repairing linker"
    );
    for target in ["target-a", "target-b"] {
        p.process(&p.root().join(target).join("debug/foo"))
            .with_stdout_data("actual executable\n".raw())
            .run();
    }
    for target in ["target-a", "target-b"] {
        let warm = command(target).run();
        assert_eq!(native_artifact(&warm.stdout)["fresh"], true);
        assert_eq!(
            compiler_starts(&warm.stdout),
            0,
            "warm reuse starts no compiler-unit process"
        );
    }
    assert_eq!(
        fs::read_to_string(record.with_extension("count"))
            .unwrap()
            .lines()
            .count(),
        2,
        "subsequent valid warm uses perform no linker execution"
    );
}

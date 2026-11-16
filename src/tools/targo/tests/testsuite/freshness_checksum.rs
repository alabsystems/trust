//! Tests for checksum-based fingerprinting (rebuild detection).
//!
//! This must be kept in-sync with `freshness_mtime.rs`

use std::fs::{self, OpenOptions};
use std::io;
use std::io::prelude::*;
use std::net::TcpListener;
use std::path::{Path, PathBuf};
use std::thread;
use std::time::SystemTime;

use crate::prelude::*;
use cargo_test_support::assert_deps_contains;
use cargo_test_support::paths;
use cargo_test_support::registry::Package;
use cargo_test_support::{
    basic_lib_manifest, basic_manifest, is_coarse_mtime, project, rustc_host, sleep_ms, str,
};
use filetime::FileTime;

// Trust: replay the exact native session, including a typed cache rejection;
// damaged evidence must never become a successful partial rebuild summary.
#[cargo_test]
fn encoded_dep_info_recorded_rebuild_timing_round_trip() {
    recorded_rebuild_replay(false, true);
}

#[cargo_test]
fn encoded_dep_info_recorded_rebuild_timing_guarded() {
    recorded_rebuild_replay(true, false);
}

// Trust: live timing observations have no file-only envelope or closing marker,
// including when the real compiler fails. Strict replay must preserve that path.
#[cargo_test]
fn native_live_timing_without_file_analysis() {
    let p = project().file("src/main.rs", "fn main() {}\n").build();
    let home = p.root().join("live-home");
    let run = |label: &str| {
        let output = p
            .process(snapbox::cmd::cargo_bin!("targo"))
            .args(&[
                "--unverified",
                "build",
                "--timings",
                "--message-format=json",
            ])
            .env("CARGO_HOME", &home)
            .env_remove("__CARGO_TEST_CHANNEL_OVERRIDE_DO_NOT_USE_THIS")
            .build_command()
            .output()
            .unwrap();
        fs::write(p.root().join(format!("{label}.stdout")), &output.stdout).unwrap();
        fs::write(p.root().join(format!("{label}.stderr")), &output.stderr).unwrap();
        assert!(!String::from_utf8_lossy(&output.stdout).contains("build-analysis-session"));
        assert!(
            String::from_utf8_lossy(&output.stderr).contains("report saved"),
            "{output:?}"
        );
        output
    };
    let html = p.root().join("target/cargo-timings/cargo-timing.html");
    let success = run("live-success");
    assert!(success.status.success(), "{success:?}");
    let contents = fs::read_to_string(&html).unwrap();
    assert!(contents.contains("Total units:</td><td>1"));
    fs::write(p.root().join("live-success.html"), contents).unwrap();
    fs::write(&html, "old owned timing report\n").unwrap();
    p.change_file("src/main.rs", "fn main() { let _: u8 = true; }\n");
    let failed = run("live-failure");
    assert_eq!(failed.status.code(), Some(101), "{failed:?}");
    let rows: Vec<serde_json::Value> = String::from_utf8_lossy(&failed.stdout)
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    assert!(
        rows.iter()
            .any(|row| row["reason"] == "compiler-message"
                && row["message"]["code"]["code"] == "E0308"),
        "{rows:?}"
    );
    let contents = fs::read_to_string(&html).unwrap();
    assert!(contents.contains("Total units:</td><td>1"), "{contents}");
    fs::write(p.root().join("live-failure.html"), contents).unwrap();
    assert!(
        !home.join("log").exists(),
        "live-only run created a file-analysis log"
    );
}

fn recorded_rebuild_replay(check_faults: bool, fine_grain: bool) {
    let p = project().file("src/main.rs", "fn main() {}\n").build();
    let home = p.root().join("analysis-home");
    fs::create_dir_all(home.join("log")).unwrap();
    let command = |args: &[&str]| {
        let mut command = p.process(snapbox::cmd::cargo_bin!("targo"));
        command
            .args(args)
            .env("CARGO_HOME", &home)
            .env_remove("__CARGO_TEST_CHANNEL_OVERRIDE_DO_NOT_USE_THIS");
        command
    };
    let record = |label: &str, output: std::process::Output| {
        fs::write(p.root().join(format!("{label}.stdout")), &output.stdout).unwrap();
        fs::write(p.root().join(format!("{label}.stderr")), &output.stderr).unwrap();
        output
    };
    let build = |label: &str| {
        let mut args = vec![
            "--unverified",
            "build",
            "-v",
            "--message-format=json",
            "-Zbuild-analysis",
            "--config",
            "build.analysis.enabled=true",
        ];
        if fine_grain {
            args.push("-Zfine-grain-locking");
            args.push("--timings");
        }
        let output = record(label, command(&args).exec_with_output().unwrap());
        assert!(output.status.success(), "{label}: {output:?}");
        output
    };
    let report = |id: &str, label: &str| {
        record(
            label,
            command(&["report", "rebuilds", "-Zbuild-analysis", "--id", id])
                .build_command()
                .output()
                .unwrap(),
        )
    };
    let timing_report = |id: &str, label: &str| {
        record(
            label,
            command(&["report", "timings", "-Zbuild-analysis", "--id", id])
                .build_command()
                .output()
                .unwrap(),
        )
    };
    build("cold");
    let warm = build("warm");
    assert!(String::from_utf8_lossy(&warm.stderr).contains("Fresh foo"));
    let files = p
        .glob("target/debug/build/foo/*/fingerprint/dep-bin-foo")
        .map(|file| file.unwrap())
        .collect::<Vec<_>>();
    assert_eq!(files.len(), 1);
    let original_dep_info = fs::read(&files[0]).unwrap();
    assert_eq!(&original_dep_info[..5], &[1, 0, 0, 0, 255]);
    let current = original_dep_info[5];
    assert_eq!(current, targo::encoded_dep_info_version());
    let recorded = current.checked_sub(1).unwrap();
    let mut injected = original_dep_info.clone();
    injected[5] = recorded;
    fs::write(p.root().join("original-dep-info.bin"), original_dep_info).unwrap();
    fs::write(p.root().join("injected-dep-info.bin"), &injected).unwrap();
    fs::write(&files[0], injected).unwrap();
    let dirty = build("migration");
    let stdout: Vec<serde_json::Value> = String::from_utf8_lossy(&dirty.stdout)
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    let identities: Vec<_> = stdout
        .iter()
        .filter(|row| row["reason"] == "build-analysis-session")
        .collect();
    let [identity] = identities.as_slice() else {
        panic!("{identities:?}")
    };
    assert_eq!(identity["schema"], 1);
    assert_eq!(identity["scope"], "build-script-inputs-v1");
    let id = identity["run_id"].as_str().unwrap();
    let timing_path = p
        .root()
        .join("target/cargo-timings")
        .join(format!("cargo-timing-{id}.html"));
    let check_timing = |label: &str| {
        let html = fs::read_to_string(&timing_path).unwrap();
        fs::write(p.root().join(format!("{label}.html")), &html).unwrap();
        for row in [
            "Fresh units:</td><td>0",
            "Dirty units:</td><td>1",
            "Total units:</td><td>1",
        ] {
            assert!(html.contains(row), "{label} lacks {row}");
        }
    };
    if fine_grain {
        check_timing("live-migration-timing");
    }
    let log = home.join("log").join(format!("{id}.jsonl"));
    let original_log = fs::read(&log).unwrap();
    fs::write(p.root().join("original-migration.jsonl"), &original_log).unwrap();
    let events: Vec<serde_json::Value> = String::from_utf8_lossy(&original_log)
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    assert!(events.iter().all(|row| row["run_id"] == id));
    let started: Vec<_> = events
        .iter()
        .filter(|row| row["reason"] == "build-started")
        .collect();
    let [started] = started.as_slice() else {
        panic!("{started:?}")
    };
    assert_eq!(
        started["workspace_root"].as_str().unwrap(),
        p.root().to_str().unwrap()
    );
    let mismatches: Vec<_> = events
        .iter()
        .enumerate()
        .filter(|(_, row)| {
            row["reason"] == "unit-fingerprint"
                && row["cause"]["stale_item"] == "dep-info-unavailable"
                && row["recheck"] != true
        })
        .collect();
    let [(fault_index, mismatch)] = mismatches.as_slice() else {
        panic!("{mismatches:?}")
    };
    assert_eq!(mismatch["status"], "dirty");
    assert_eq!(mismatch["cause"]["dirty_reason"], "fs-status-outdated");
    assert_eq!(mismatch["cause"]["fs_status"], "stale-item");
    assert_eq!(
        mismatch["cause"]["path"].as_str().unwrap(),
        files[0].to_str().unwrap()
    );
    let registered: Vec<_> = events
        .iter()
        .filter(|row| row["reason"] == "unit-registered" && row["index"] == mismatch["index"])
        .collect();
    let [registered] = registered.as_slice() else {
        panic!("{registered:?}")
    };
    assert_eq!(
        registered["target"],
        serde_json::json!({"name": "foo", "kind": "bin"})
    );
    assert_eq!(registered["mode"], "build");
    let rechecks = events
        .iter()
        .filter(|row| row["reason"] == "unit-fingerprint" && row["recheck"] == true)
        .count();
    assert_eq!(rechecks, usize::from(fine_grain));
    assert_eq!(
        mismatch["cause"]["reason"],
        serde_json::json!({
            "kind": "format-mismatch", "recorded": recorded, "current": current,
        })
    );
    // A later warm session must not replace the explicitly selected migration.
    assert_eq!(fs::read(&files[0]).unwrap()[5], current);
    let warm = build("warm-after-migration");
    let stderr = String::from_utf8_lossy(&warm.stderr);
    assert!(
        stderr.contains("Fresh foo") && !stderr.contains("Compiling foo"),
        "{stderr}"
    );
    let replay = report(id, "replay");
    assert!(replay.status.success(), "{replay:?}");
    let diagnostic = String::from_utf8_lossy(&replay.stderr);
    assert!(
        diagnostic.contains("Status: 1 unit rebuilt, 0 cached, 0 new"),
        "{diagnostic}"
    );
    assert!(
        diagnostic.contains(&format!(
            "encoded dep-info format mismatch (recorded {recorded}, current {current})"
        )),
        "{diagnostic}"
    );
    let timing = timing_report(id, "replay-timing");
    assert!(timing.status.success(), "{timing:?}");
    check_timing("replayed-migration-timing");
    if !check_faults {
        return;
    }
    let invalid_manifest = record(
        "invalid-manifest",
        command(&[
            "report",
            "rebuilds",
            "-Zbuild-analysis",
            "--id",
            id,
            "--manifest-path",
            "absent/Cargo.toml",
        ])
        .build_command()
        .output()
        .unwrap(),
    );
    assert_eq!(
        invalid_manifest.status.code(),
        Some(101),
        "{invalid_manifest:?}"
    );
    assert!(!String::from_utf8_lossy(&invalid_manifest.stderr).contains("Status:"));
    let invalid_manifest = record(
        "invalid-timing-manifest",
        command(&[
            "report",
            "timings",
            "-Zbuild-analysis",
            "--id",
            id,
            "--manifest-path",
            "absent/Cargo.toml",
        ])
        .build_command()
        .output()
        .unwrap(),
    );
    assert_eq!(
        invalid_manifest.status.code(),
        Some(101),
        "{invalid_manifest:?}"
    );
    assert!(!String::from_utf8_lossy(&invalid_manifest.stderr).contains("report saved"));
    // Each control starts from the immutable original, never another control.
    // Only the owned analysis log is damaged; no output or integrity receipt is changed.
    for fault in [
        "missing-current",
        "unknown-nested-field",
        "unknown-cause-field",
        "unknown-cause-kind",
        "wrong-run",
        "wrong-workspace",
        "duplicate-fingerprint",
        "missing-fingerprint",
        "wrong-denominator",
        "missing-finalization",
        "missing-close",
    ] {
        let mut damaged = events.clone();
        match fault {
            "missing-current" => {
                damaged[*fault_index]["cause"]["reason"]
                    .as_object_mut()
                    .unwrap()
                    .remove("current");
            }
            "unknown-nested-field" => {
                damaged[*fault_index]["cause"]["reason"]["extra"] = true.into();
            }
            "unknown-cause-field" => {
                damaged[*fault_index]["cause"]["extra"] = true.into();
            }
            "unknown-cause-kind" => {
                damaged[*fault_index]["cause"]["reason"]["kind"] = "unknown".into();
            }
            "wrong-run" => {
                damaged[*fault_index]["run_id"] = "another-run".into();
            }
            "wrong-workspace" => {
                for row in &mut damaged {
                    if row["reason"] == "build-started" {
                        row["workspace_root"] = home.to_str().unwrap().into();
                    }
                }
            }
            "duplicate-fingerprint" => {
                damaged.insert(*fault_index + 1, damaged[*fault_index].clone());
            }
            "missing-fingerprint" => {
                damaged.remove(*fault_index);
            }
            "wrong-denominator" => {
                for row in &mut damaged {
                    if row["reason"] == "execution-graph-finished" {
                        row["scheduled"] = (row["scheduled"].as_u64().unwrap() + 1).into();
                    }
                }
            }
            "missing-finalization" => {
                damaged.retain(|row| row["reason"] != "input-work-finalized");
            }
            "missing-close" => {
                damaged.retain(|row| row["reason"] != "input-work-closed");
            }
            _ => unreachable!(),
        }
        let bytes = damaged
            .iter()
            .map(|row| format!("{}\n", serde_json::to_string(row).unwrap()))
            .collect::<String>();
        fs::write(p.root().join(format!("{fault}.jsonl")), &bytes).unwrap();
        fs::write(&log, bytes).unwrap();
        let rejected = report(id, fault);
        assert_eq!(rejected.status.code(), Some(101), "{fault}: {rejected:?}");
        let diagnostic = String::from_utf8_lossy(&rejected.stderr);
        let expected = if fault == "wrong-workspace" {
            "build-analysis session belongs to a different workspace"
        } else {
            "failed to analyze log"
        };
        assert!(diagnostic.contains(expected), "{fault}: {diagnostic}");
        assert!(!diagnostic.contains("Status:"), "{fault}: {rejected:?}");
    }
    // A damaged recording must fail before opening/truncating an existing report.
    // Every fault starts from the original actual session, never another fault.
    for fault in [
        "missing-current",
        "unknown-nested-field",
        "wrong-run",
        "wrong-workspace",
        "missing-fingerprint",
        "missing-close",
        "duplicate-registration",
        "unknown-started-unit",
        "negative-elapsed",
        "trailing-garbage",
        "truncated-tail",
    ] {
        let mut damaged = events.clone();
        match fault {
            "missing-current" => {
                damaged[*fault_index]["cause"]["reason"]
                    .as_object_mut()
                    .unwrap()
                    .remove("current");
            }
            "unknown-nested-field" => {
                damaged[*fault_index]["cause"]["reason"]["extra"] = true.into();
            }
            "wrong-run" => {
                damaged[*fault_index]["run_id"] = "another-run".into();
            }
            "wrong-workspace" => {
                for row in &mut damaged {
                    if row["reason"] == "build-started" {
                        row["workspace_root"] = home.to_str().unwrap().into();
                    }
                }
            }
            "missing-fingerprint" => {
                damaged.remove(*fault_index);
            }
            "missing-close" => {
                damaged.retain(|row| row["reason"] != "input-work-closed");
            }
            "duplicate-registration" => {
                let index = damaged
                    .iter()
                    .position(|row| row["reason"] == "unit-registered")
                    .unwrap();
                damaged.insert(index + 1, damaged[index].clone());
            }
            "unknown-started-unit" => {
                for row in &mut damaged {
                    if row["reason"] == "unit-started" {
                        row["index"] = 999.into();
                    }
                }
            }
            "negative-elapsed" => {
                for row in &mut damaged {
                    if row["reason"] == "unit-started" {
                        row["elapsed"] = (-1).into();
                    }
                }
            }
            "trailing-garbage" | "truncated-tail" => {}
            _ => unreachable!(),
        }
        let mut bytes = damaged
            .iter()
            .map(|row| format!("{row}\n"))
            .collect::<String>();
        if fault == "trailing-garbage" {
            bytes.push_str("{broken}\n");
        }
        if fault == "truncated-tail" {
            assert_eq!(bytes.pop(), Some('\n'));
        }
        fs::write(p.root().join(format!("timing-{fault}.jsonl")), &bytes).unwrap();
        fs::write(&log, bytes).unwrap();
        let sentinel = format!("unchanged owned report: {fault}\n");
        fs::write(&timing_path, &sentinel).unwrap();
        let rejected = timing_report(id, &format!("timing-{fault}"));
        assert_eq!(rejected.status.code(), Some(101), "{fault}: {rejected:?}");
        let diagnostic = String::from_utf8_lossy(&rejected.stderr);
        assert!(
            !diagnostic.contains("report saved"),
            "{fault}: {diagnostic}"
        );
        assert_eq!(
            fs::read_to_string(&timing_path).unwrap(),
            sentinel,
            "{fault}"
        );
    }
    fs::write(&log, original_log).unwrap();
    assert!(timing_report(id, "restored-timing").status.success());
    check_timing("restored-timing");

    // A genuine unsuccessful compile has a closed execution log but no input
    // finalization acknowledgement. Keep its diagnostic report available and
    // disclose that distinction rather than inventing completed input work.
    p.change_file("src/main.rs", "fn main() { let _: u8 = true; }\n");
    let failed = record(
        "failed-compile",
        command(&[
            "--unverified",
            "build",
            "--message-format=json",
            "-Zbuild-analysis",
            "--config",
            "build.analysis.enabled=true",
        ])
        .build_command()
        .output()
        .unwrap(),
    );
    assert_eq!(failed.status.code(), Some(101), "{failed:?}");
    let rows: Vec<serde_json::Value> = String::from_utf8_lossy(&failed.stdout)
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    assert!(
        rows.iter()
            .any(|row| row["reason"] == "compiler-message"
                && row["message"]["code"]["code"] == "E0308"),
        "{rows:?}"
    );
    let identities: Vec<_> = rows
        .iter()
        .filter(|row| row["reason"] == "build-analysis-session")
        .collect();
    let [identity] = identities.as_slice() else {
        panic!("{identities:?}")
    };
    let failed_id = identity["run_id"].as_str().unwrap();
    let failed_log =
        fs::read_to_string(home.join("log").join(format!("{failed_id}.jsonl"))).unwrap();
    fs::write(p.root().join("original-failed-compile.jsonl"), &failed_log).unwrap();
    let events: Vec<serde_json::Value> = failed_log
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    assert!(events.iter().all(|row| row["run_id"] == failed_id));
    assert!(
        events
            .iter()
            .any(|row| row["reason"] == "execution-graph-finished" && row["outcome"] == "failed")
    );
    assert_eq!(events.last().unwrap()["reason"], "input-work-closed");
    assert!(
        !events
            .iter()
            .any(|row| row["reason"] == "input-work-finalized")
    );
    let replay = report(failed_id, "failed-compile-replay");
    assert!(replay.status.success(), "{replay:?}");
    assert!(
        String::from_utf8_lossy(&replay.stderr)
            .contains("Input accounting: unavailable after unsuccessful execution"),
        "{replay:?}"
    );
    let replay = timing_report(failed_id, "failed-compile-timing");
    assert!(replay.status.success(), "{replay:?}");
}

// Trust: controlled version fault injection changes only an emitted internal
// read-set, never a compiled output, fingerprint key or integrity receipt.
#[cargo_test]
fn encoded_dep_info_version_rebuild_reason_reported() {
    let p = project().file("src/main.rs", "fn main() {}\n").build();
    let run = || {
        let mut command = p.process(snapbox::cmd::cargo_bin!("targo"));
        command.args(&["--unverified", "build", "-v", "--message-format=json"]);
        command
    };
    run().run();
    run()
        .with_stderr_contains("[FRESH] foo v0.0.1 [..]")
        .with_stderr_does_not_contain("[COMPILING] foo v0.0.1 [..]")
        .run();
    let files = p
        .glob("target/debug/build/foo/*/fingerprint/dep-bin-foo")
        .map(|file| file.unwrap())
        .collect::<Vec<_>>();
    assert_eq!(files.len(), 1, "expected one actually emitted read-set");
    let original = fs::read(&files[0]).unwrap();
    assert_eq!(&original[..5], &[1, 0, 0, 0, 255]);
    let current = original[5];
    assert!(current > 1, "no historical version for this control");
    let recorded = current - 1;
    let mut injected = original.clone();
    injected[5] = recorded;
    fs::write(p.root().join("original-dep-info.bin"), &original).unwrap();
    fs::write(p.root().join("injected-dep-info.bin"), &injected).unwrap();
    fs::write(&files[0], &injected).unwrap();
    run()
        .with_stderr_contains(format!(
            "[DIRTY] foo v0.0.1 [..]: [..]encoded dep-info format mismatch (recorded {recorded}, current {current})"
        ))
        .with_stderr_contains("[COMPILING] foo v0.0.1 [..]")
        .with_stderr_does_not_contain("[..]cached output integrity failed[..]")
        .with_stdout_contains("[..]\"dirty_reason\":\"dep-info-format-mismatch\"[..]")
        .run();
    assert_eq!(fs::read(&files[0]).unwrap()[5], current);
    run()
        .with_stderr_contains("[FRESH] foo v0.0.1 [..]")
        .with_stderr_does_not_contain("[COMPILING] foo v0.0.1 [..]")
        .run();
}

// Trust: checksum comments must attach to the same unescaped source paths as
// dependency rules, without losing literal backslashes or adjacent spaces.
#[cargo_test]
fn checksum_dep_info_spaced_source_round_trip() {
    let first = "src/module with  spaces.rs";
    let second = if cfg!(unix) {
        "src/Unicode Ω\\ file.rs"
    } else {
        "src/Unicode Ω file.rs"
    };
    checksum_dep_info_source_paths(first, second, None);
}

// Trust: Unix preserves leading/trailing filename spaces rather than normalizing them.
#[cfg(unix)]
#[cargo_test]
fn checksum_dep_info_space_boundaries_round_trip() {
    checksum_dep_info_source_paths("src/trailing space.rs ", "src/ leading space.rs", None);
}

// Trust: both the real terminal-backslash input and a misleading merged-name
// decoy exist; filename boundaries cannot be chosen by filesystem existence.
#[cfg(unix)]
#[cargo_test]
fn checksum_dep_info_terminal_backslash_round_trip() {
    checksum_dep_info_source_paths(
        "src/terminal\\",
        "src/other.rs",
        Some("src/terminal src/other.rs"),
    );
}

// Trust: both fixtures check actual emitted checksums, content invalidation and reuse.
fn checksum_dep_info_source_paths(first: &str, second: &str, decoy: Option<&str>) {
    let original = "pub const VALUE: &str = \"first\";\n";
    let changed = "pub const VALUE: &str = \"other\";\n";
    assert_eq!(original.len(), changed.len());
    let source = format!(
        "#[path = {:?}] mod first;\n#[path = {:?}] mod second;\n\
         fn main() {{ println!(\"{{}} {{}}\", first::VALUE, second::VALUE); }}\n",
        first.strip_prefix("src/").unwrap(),
        second.strip_prefix("src/").unwrap(),
    );
    let mut builder = project()
        .file("src/main.rs", &source)
        .file(first, original)
        .file(second, original);
    if let Some(path) = decoy {
        builder = builder.file(path, "pub const VALUE: &str = \"decoy\";\n");
    }
    let p = builder.build();
    let run = |expected: &str| {
        let mut cmd = p.process(snapbox::cmd::cargo_bin!("targo"));
        cmd.args(&["--unverified", "run", "-v"])
            .with_stdout_data(format!("{expected}\n").raw());
        cmd
    };
    run("first first").run();
    // Trust: isolate consumer decoding from an older compiler omitting hashes.
    let dep_info = p
        .glob("target/debug/build/foo/*/out/*.d")
        .map(|file| file.unwrap())
        .collect::<Vec<_>>();
    assert!(!dep_info.is_empty(), "missing actual compiler dep-info");
    for path in [first, second] {
        let suffix = format!(" {}", path.replace(' ', "\\ "));
        assert!(
            dep_info.iter().any(|file| {
                fs::read_to_string(file)
                    .unwrap()
                    .lines()
                    .any(|line| line.starts_with("# checksum:") && line.ends_with(&suffix))
            }),
            "compiler omitted checksum for {path:?}"
        );
        let phony = format!("{}:", path.replace(' ', "\\ "));
        assert!(
            dep_info.iter().any(|file| {
                fs::read_to_string(file)
                    .unwrap()
                    .lines()
                    .any(|line| line == phony)
            }),
            "compiler omitted separate dependency record for {path:?}"
        );
    }
    run("first first")
        .with_stderr_contains("[FRESH] foo v0.0.1 [..]")
        .with_stderr_does_not_contain("[COMPILING] foo v0.0.1 [..]")
        .run();
    let path = p.root().join(first);
    let modified = FileTime::from_last_modification_time(&fs::metadata(&path).unwrap());
    p.change_file(first, changed);
    filetime::set_file_mtime(&path, modified).unwrap();
    run("other first")
        .with_stderr_contains("[COMPILING] foo v0.0.1 [..]")
        .run();
    run("other first")
        .with_stderr_contains("[FRESH] foo v0.0.1 [..]")
        .with_stderr_does_not_contain("[COMPILING] foo v0.0.1 [..]")
        .run();
}

#[cargo_test]
fn non_nightly_fails() {
    // Trust: retain the channel refusal and exact current Trust guidance.
    let p = project().file("src/main.rs", "fn main() {}").build();
    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .with_stderr_data(str![[r#"
[ERROR] the `-Z` flag is only accepted on Trust/nightly-capable Cargo channels, but this is the `stable` channel
Use the Trust `trust` channel, or another Cargo channel with explicit unstable-feature support, for these flags.

"#]])
        .with_status(101)
        .run();
}

#[cargo_test]
fn warn_on_missing_feature() {
    let p = project().file("src/main.rs", "fn main() {}").build();
    p.cargo("check")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .with_stderr_data(str![[r#"
[WARNING] ignoring `build.fingerprint = "content"` without `-Zchecksum-freshness`
[CHECKING] foo v0.0.1 ([ROOT]/foo)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
    p.cargo("check")
        .env("CARGO_BUILD_FINGERPRINT", "mtime")
        .with_stderr_data(str![[r#"
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test(nightly, reason = "requires -Zchecksum-hash-algorithm")]
fn checksum_actually_uses_checksum() {
    let p = project()
        .file("src/main.rs", "mod a; fn main() {}")
        .file("src/a.rs", "")
        .build();

    p.cargo("check")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_stderr_data(str![[r#"
[CHECKING] foo v0.0.1 ([ROOT]/foo)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
    p.root().move_into_the_future();

    p.cargo("check")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_stderr_data(str![[r#"
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test(nightly, reason = "requires -Zchecksum-hash-algorithm")]
fn same_size_different_content() {
    let p = project()
        .file("src/main.rs", "mod a; fn main() {}")
        .file("src/a.rs", "")
        .build();

    p.cargo("check")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_stderr_data(str![[r#"
[CHECKING] foo v0.0.1 ([ROOT]/foo)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
    p.change_file("src/main.rs", "mod a;fn main() { }");

    p.cargo("check -v")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_stderr_data(str![[r#"
[DIRTY] foo v0.0.1 ([ROOT]/foo): the file `src/main.rs` has changed (checksum didn't match, blake3=26aa07e1adab787246f9d333be65d2eb78dd5fd0fee834ba7a769098b4b651bc != blake3=fc1a42e376d9c148227c13de41b77143f6b5b8132d2b204b63cdbc9326848894)
[CHECKING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustc --crate-name foo [..]
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();

    p.cargo("check")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_stderr_data(str![[r#"
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test(
    nightly,
    reason = "-Zbinary-dep-depinfo is unstable, also requires -Zchecksum-hash-algorithm"
)]
fn binary_depinfo_correctly_encoded() {
    Package::new("regdep", "0.1.0")
        .file("src/lib.rs", "pub fn f() {}")
        .publish();

    let p = project()
        .file(
            "Cargo.toml",
            r#"
            [package]
            name = "foo"
            version = "0.1.0"
            edition = "2018"

            [dependencies]
            regdep = "0.1"
            bar = {path = "./bar"}
            "#,
        )
        .file(
            "src/main.rs",
            r#"
            fn main() {
                regdep::f();
                bar::f();
            }
            "#,
        )
        /*********** Path Dependency `bar` ***********/
        .file("bar/Cargo.toml", &basic_manifest("bar", "0.1.0"))
        .file("bar/src/lib.rs", "pub fn f() {}")
        .build();

    let host = rustc_host();
    p.cargo("build --target")
        .arg(&host)
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zbinary-dep-depinfo")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["binary-dep-depinfo", "checksum-freshness"])
        .with_stderr_data(str![[r#"
...
[COMPILING] foo v0.1.0 ([ROOT]/foo)
...

"#]])
        .run();

    assert_deps_contains(
        &p,
        &format!("target/{}/debug/build/foo/*/fingerprint/dep-bin-foo", host),
        &[
            (0, "src/main.rs"),
            (1, &format!("{}/debug/build/bar/*/out/libbar-*.rlib", host)),
            (
                1,
                &format!("{}/debug/build/regdep/*/out/libregdep-*.rlib", host),
            ),
        ],
    );

    // Make sure it stays fresh.
    p.cargo("build --target")
        .arg(&host)
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zbinary-dep-depinfo")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["binary-dep-depinfo", "checksum-freshness"])
        .with_stderr_data(str![[r#"
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test(nightly, reason = "requires -Zchecksum-hash-algorithm")]
fn modifying_and_moving() {
    let p = project()
        .file("src/main.rs", "mod a; fn main() {}")
        .file("src/a.rs", "")
        .build();

    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_stderr_data(str![[r#"
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();

    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_stderr_data(str![[r#"
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
    p.root().move_into_the_past();
    p.root().join("target").move_into_the_past();

    p.change_file("src/a.rs", "#[allow(unused)]fn main() {}");
    p.cargo("build -v")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_stderr_data(str![[r#"
[DIRTY] foo v0.0.1 ([ROOT]/foo): file size changed (0 != 28) for `src/a.rs`
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustc --crate-name foo [..]
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();

    fs::rename(&p.root().join("src/a.rs"), &p.root().join("src/b.rs")).unwrap();
    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_status(101)
        .with_stderr_data(str![[r#"
[COMPILING] foo v0.0.1 ([ROOT]/foo)
error[E0583]: file not found for module `a`
...
[ERROR] could not compile `foo` (bin "foo") due to 1 previous error

"#]])
        .run();
}

#[cargo_test(nightly, reason = "requires -Zchecksum-hash-algorithm")]
fn modify_only_some_files() {
    let p = project()
        .file("src/lib.rs", "mod a;")
        .file("src/a.rs", "")
        .file("src/main.rs", "mod b; fn main() {}")
        .file("src/b.rs", "")
        .file("tests/test.rs", "")
        .build();

    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_stderr_data(str![[r#"
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
    p.cargo("test")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .run();

    assert!(p.bin("foo").is_file());

    let lib = p.root().join("src/lib.rs");
    p.change_file("src/lib.rs", "invalid rust code");
    p.change_file("src/b.rs", "#[allow(unused)]fn foo() {}");
    lib.move_into_the_past();

    // Despite mtime change, lib rebuilds and fails
    p.cargo("build -v")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_status(101)
        .with_stderr_data("...")
        .run();
}

#[cargo_test(nightly, reason = "requires -Zchecksum-hash-algorithm")]
fn rebuild_sub_package_then_while_package() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                authors = []
                version = "0.0.1"
                edition = "2015"

                [dependencies.a]
                path = "a"
                [dependencies.b]
                path = "b"
            "#,
        )
        .file("src/lib.rs", "extern crate a; extern crate b;")
        .file(
            "a/Cargo.toml",
            r#"
                [package]
                name = "a"
                authors = []
                version = "0.0.1"
                edition = "2015"
                [dependencies.b]
                path = "../b"
            "#,
        )
        .file("a/src/lib.rs", "extern crate b;")
        .file("b/Cargo.toml", &basic_manifest("b", "0.0.1"))
        .file("b/src/lib.rs", "")
        .build();

    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_stderr_data(str![[r#"
[LOCKING] 2 packages to highest compatible versions
[COMPILING] b v0.0.1 ([ROOT]/foo/b)
[COMPILING] a v0.0.1 ([ROOT]/foo/a)
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();

    p.change_file("b/src/lib.rs", "pub fn b() {}");

    p.cargo("build -pb -v")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_stderr_data(str![[r#"
[DIRTY] b v0.0.1 ([ROOT]/foo/b): file size changed (0 != 13) for `b/src/lib.rs`
[COMPILING] b v0.0.1 ([ROOT]/foo/b)
[RUNNING] `rustc --crate-name b [..]
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();

    p.change_file(
        "src/lib.rs",
        "extern crate a; extern crate b; pub fn toplevel() {}",
    );

    p.cargo("build -v")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_stderr_data(str![[r#"
[FRESH] b v0.0.1 ([ROOT]/foo/b)
[DIRTY] a v0.0.1 ([ROOT]/foo/a): the dependency `b` was rebuilt ([TIME_DIFF_AFTER_LAST_BUILD])
[COMPILING] a v0.0.1 ([ROOT]/foo/a)
[RUNNING] `rustc --crate-name a [..]
[DIRTY] foo v0.0.1 ([ROOT]/foo): the dependency `b` was rebuilt ([TIME_DIFF_AFTER_LAST_BUILD])
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustc --crate-name foo [..] src/lib.rs [..]
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test(nightly, reason = "requires -Zchecksum-hash-algorithm")]
fn rebuild_tests_if_lib_changes() {
    let p = project()
        .file("src/lib.rs", "pub fn foo() {}")
        .file("tests/foo-test.rs", "extern crate foo;")
        .build();

    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .run();
    p.cargo("test")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .run();

    p.change_file("src/lib.rs", "");

    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .run();
    p.cargo("test -v --test foo-test")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_stderr_data(str![[r#"
[DIRTY] foo v0.0.1 ([ROOT]/foo): the dependency `foo` was rebuilt ([TIME_DIFF_AFTER_LAST_BUILD])
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustc --crate-name foo_test [..]`
[FINISHED] `test` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s
[RUNNING] `[ROOT]/foo/target/debug/build/foo/[HASH]/out/foo_test-[HASH][EXE]`

"#]])
        .run();
}

#[cargo_test(nightly, reason = "requires -Zchecksum-hash-algorithm")]
fn no_rebuild_if_build_artifacts_move_backwards_in_time() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                edition = "2015"
                authors = []

                [dependencies]
                a = { path = "a" }

                [lints.cargo]
                default = "allow"
            "#,
        )
        .file("src/lib.rs", "")
        .file("a/Cargo.toml", &basic_manifest("a", "0.0.1"))
        .file("a/src/lib.rs", "")
        .build();

    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .run();

    p.root().move_into_the_past();

    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_stdout_data(str![])
        .with_stderr_data(str![[r#"
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test(nightly, reason = "requires -Zchecksum-hash-algorithm")]
fn no_rebuild_if_build_artifacts_move_forward_in_time() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                edition = "2015"
                authors = []

                [dependencies]
                a = { path = "a" }

                [lints.cargo]
                default = "allow"
            "#,
        )
        .file("src/lib.rs", "")
        .file("a/Cargo.toml", &basic_manifest("a", "0.0.1"))
        .file("a/src/lib.rs", "")
        .build();

    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .run();

    p.root().move_into_the_future();

    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .env("CARGO_LOG", "")
        .with_stdout_data(str![])
        .with_stderr_data(str![[r#"
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test(nightly, reason = "requires -Zchecksum-hash-algorithm")]
fn no_rebuild_when_rename_dir() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "bar"
                version = "0.0.1"
                edition = "2015"
                authors = []

                [workspace]

                [dependencies]
                foo = { path = "foo" }

                [lints.cargo]
                default = "allow"
            "#,
        )
        .file("src/_unused.rs", "")
        .file("build.rs", "fn main() {}")
        .file("foo/Cargo.toml", &basic_manifest("foo", "0.0.1"))
        .file("foo/src/lib.rs", "")
        .file("foo/build.rs", "fn main() {}")
        .build();

    // make sure the most recently modified file is `src/lib.rs`, not
    // `Cargo.toml`, to expose a historical bug where we forgot to strip the
    // `Cargo.toml` path from looking for the package root.
    fs::write(p.root().join("src/lib.rs"), "").unwrap();

    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .run();
    let mut new = p.root();
    new.pop();
    new.push("bar");
    fs::rename(p.root(), &new).unwrap();

    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .cwd(&new)
        .with_stderr_data(str![[r#"
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test(nightly, reason = "requires -Zchecksum-hash-algorithm")]
fn update_dependency_mtime_does_not_rebuild() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                edition = "2015"

                [dependencies]
                bar = { path = "bar" }

                [lints.cargo]
                default = "allow"
            "#,
        )
        .file("src/lib.rs", "")
        .file("bar/Cargo.toml", &basic_manifest("bar", "0.0.1"))
        .file("bar/src/lib.rs", "")
        .build();

    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zmtime-on-use")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["mtime-on-use", "checksum-freshness"])
        .env("RUSTFLAGS", "-C linker=cc")
        .with_stderr_data(str![[r#"
[LOCKING] 1 package to highest compatible version
[COMPILING] bar v0.0.1 ([ROOT]/foo/bar)
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
    // This does not make new files, but it does update the mtime of the dependency.
    p.cargo("build -p bar")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zmtime-on-use")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["mtime-on-use", "checksum-freshness"])
        .env("RUSTFLAGS", "-C linker=cc")
        .with_stderr_data(str![[r#"
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
    // This should not recompile!
    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zmtime-on-use")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["mtime-on-use", "checksum-freshness"])
        .env("RUSTFLAGS", "-C linker=cc")
        .with_stderr_data(str![[r#"
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

fn fingerprint_cleaner(mut dir: PathBuf, timestamp: filetime::FileTime) {
    // Cargo is experimenting with letting outside projects develop some
    // limited forms of GC for target_dir. This is one of the forms.
    // Specifically, Cargo is updating the mtime of a file in
    // target/profile/.fingerprint each time it uses the fingerprint.
    // So a cleaner can remove files associated with a fingerprint
    // if all the files in the fingerprint's folder are older then a time stamp without
    // effecting any builds that happened since that time stamp.
    let mut cleaned = false;
    dir.push("build");
    let outdated = |f: io::Result<fs::DirEntry>| {
        filetime::FileTime::from_last_modification_time(&f.unwrap().metadata().unwrap())
            <= timestamp
    };
    for build_unit in fs::read_dir(&dir).unwrap() {
        let build_unit = build_unit.unwrap();
        for hash_dir in fs::read_dir(&build_unit.path()).unwrap() {
            let hash_dir = hash_dir.unwrap();
            let fingerprint = hash_dir.path().join("fingerprint");
            if fs::read_dir(fingerprint).unwrap().all(outdated) {
                fs::remove_dir_all(hash_dir.path()).unwrap();
                println!("remove: {:?}", hash_dir.path());
                // a real cleaner would remove the big files in deps and build as well
                // but fingerprint is sufficient for our tests
                cleaned = true;
            }
        }
    }
    assert!(
        cleaned,
        "called fingerprint_cleaner, but there was nothing to remove"
    );
}

#[cargo_test(nightly, reason = "requires -Zchecksum-hash-algorithm")]
fn fingerprint_cleaner_does_not_rebuild() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                edition = "2015"

                [dependencies]
                bar = { path = "bar" }

                [features]
                a = []

                [lints.cargo]
                default = "allow"
            "#,
        )
        .file("src/lib.rs", "")
        .file("bar/Cargo.toml", &basic_manifest("bar", "0.0.1"))
        .file("bar/src/lib.rs", "")
        .build();

    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zmtime-on-use")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["mtime-on-use", "checksum-freshness"])
        .run();
    p.cargo("build --features a")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zmtime-on-use")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["mtime-on-use", "checksum-freshness"])
        .with_stderr_data(str![[r#"
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
    if is_coarse_mtime() {
        sleep_ms(1000);
    }
    let timestamp = filetime::FileTime::from_system_time(SystemTime::now());
    if is_coarse_mtime() {
        sleep_ms(1000);
    }
    // This does not make new files, but it does update the mtime.
    p.cargo("build --features a")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zmtime-on-use")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["mtime-on-use", "checksum-freshness"])
        .with_stderr_data(str![[r#"
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
    fingerprint_cleaner(p.target_debug_dir(), timestamp);
    // This should not recompile!
    p.cargo("build --features a")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zmtime-on-use")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["mtime-on-use", "checksum-freshness"])
        .with_stderr_data(str![[r#"
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
    // But this should be cleaned and so need a rebuild
    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zmtime-on-use")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["mtime-on-use", "checksum-freshness"])
        .with_stderr_data(str![[r#"
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test(nightly, reason = "requires -Zchecksum-hash-algorithm")]
fn bust_patched_dep() {
    Package::new("registry1", "0.1.0").publish();
    Package::new("registry2", "0.1.0")
        .dep("registry1", "0.1.0")
        .publish();

    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                edition = "2015"

                [dependencies]
                registry2 = "0.1.0"

                [patch.crates-io]
                registry1 = { path = "reg1new" }

                [lints.cargo]
                default = "allow"
            "#,
        )
        .file("src/lib.rs", "")
        .file("reg1new/Cargo.toml", &basic_manifest("registry1", "0.1.0"))
        .file("reg1new/src/lib.rs", "")
        .build();

    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .run();

    p.change_file("reg1new/src/lib.rs", "// modified");

    p.cargo("build -v")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_stderr_data(str![[r#"
[DIRTY] registry1 v0.1.0 ([ROOT]/foo/reg1new): file size changed (0 != 11) for `reg1new/src/lib.rs`
[COMPILING] registry1 v0.1.0 ([ROOT]/foo/reg1new)
[RUNNING] `rustc --crate-name registry1 [..]
[DIRTY] registry2 v0.1.0: the dependency `registry1` was rebuilt
[COMPILING] registry2 v0.1.0
[RUNNING] `rustc --crate-name registry2 [..]
[DIRTY] foo v0.0.1 ([ROOT]/foo): the dependency `registry2` was rebuilt
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustc --crate-name foo [..]
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();

    p.cargo("build -v")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_stderr_data(str![[r#"
[FRESH] registry1 v0.1.0 ([ROOT]/foo/reg1new)
[FRESH] registry2 v0.1.0
[FRESH] foo v0.0.1 ([ROOT]/foo)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test(nightly, reason = "requires -Zchecksum-hash-algorithm")]
fn rebuild_on_mid_build_file_modification() {
    let server = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = server.local_addr().unwrap();

    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [workspace]
                members = ["root", "proc_macro_dep"]
            "#,
        )
        .file(
            "root/Cargo.toml",
            r#"
                [package]
                name = "root"
                version = "0.1.0"
                edition = "2015"
                authors = []

                [dependencies]
                proc_macro_dep = { path = "../proc_macro_dep" }
            "#,
        )
        .file(
            "root/src/lib.rs",
            r#"
                #[macro_use]
                extern crate proc_macro_dep;

                #[derive(Noop)]
                pub struct X;
            "#,
        )
        .file(
            "proc_macro_dep/Cargo.toml",
            r#"
                [package]
                name = "proc_macro_dep"
                version = "0.1.0"
                edition = "2015"
                authors = []

                [lib]
                proc-macro = true
            "#,
        )
        .file(
            "proc_macro_dep/src/lib.rs",
            &format!(
                r#"
                    extern crate proc_macro;

                    use std::io::Read;
                    use std::net::TcpStream;
                    use proc_macro::TokenStream;

                    #[proc_macro_derive(Noop)]
                    pub fn noop(_input: TokenStream) -> TokenStream {{
                        let mut stream = TcpStream::connect("{}").unwrap();
                        let mut v = Vec::new();
                        stream.read_to_end(&mut v).unwrap();
                        "".parse().unwrap()
                    }}
                "#,
                addr
            ),
        )
        .build();
    let root = p.root();

    let t = thread::spawn(move || {
        let socket = server.accept().unwrap().0;
        let mut file = OpenOptions::new()
            .write(true)
            .append(true)
            .open(root.join("root/src/lib.rs"))
            .unwrap();
        writeln!(file, "// modified").expect("Failed to append to root sources");
        drop(file);
        drop(socket);
        drop(server.accept().unwrap());
    });

    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_stderr_data(str![[r#"
[COMPILING] proc_macro_dep v0.1.0 ([ROOT]/foo/proc_macro_dep)
[COMPILING] root v0.1.0 ([ROOT]/foo/root)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();

    p.cargo("build -v")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_stderr_data(str![[r#"
[FRESH] proc_macro_dep v0.1.0 ([ROOT]/foo/proc_macro_dep)
[DIRTY] root v0.1.0 ([ROOT]/foo/root): file size changed (150 != 162) for `root/src/lib.rs`
[COMPILING] root v0.1.0 ([ROOT]/foo/root)
[RUNNING] `rustc --crate-name root [..]
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();

    t.join().ok().unwrap();
}

#[cargo_test(nightly, reason = "requires -Zchecksum-hash-algorithm")]
fn dirty_both_lib_and_test() {
    // This tests that all artifacts that depend on the results of a build
    // script will get rebuilt when the build script reruns, even for separate
    // commands. It does the following:
    //
    // 1. Project "foo" has a build script which will compile a small
    //    staticlib to link against. Normally this would use the `cc` crate,
    //    but here we just use rustc to avoid the `cc` dependency.
    // 2. Build the library.
    // 3. Build the unit test. The staticlib intentionally has a bad value.
    // 4. Rewrite the staticlib with the correct value.
    // 5. Build the library again.
    // 6. Build the unit test. This should recompile.

    let slib = |n| {
        format!(
            r#"
                #[no_mangle]
                pub extern "C" fn doit() -> i32 {{
                    return {};
                }}
            "#,
            n
        )
    };

    let p = project()
        .file(
            "Cargo.toml",
            &format!(
                "{}{}",
                basic_manifest("foo", "0.0.1"),
                crate::utils::tools::jobserver_build_dependency()
            ),
        )
        .file(
            "src/lib.rs",
            r#"
                extern "C" {
                    fn doit() -> i32;
                }

                #[test]
                fn t1() {
                    assert_eq!(unsafe { doit() }, 1, "doit assert failure");
                }
            "#,
        )
        .file(
            "build.rs",
            r#"
                use std::env;
                use std::path::PathBuf;
                use std::process::Command;

                fn main() {
                    // Trust: import at startup, before opening files can reuse an endpoint.
                    let jobserver = unsafe { jobserver_utils::InheritedJobserver::from_env() }
                        .expect("inherit build-script jobserver");
                    let rustc = env::var_os("RUSTC").unwrap();
                    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
                    let mut command = Command::new(rustc);
                    command.args(&[
                        "--crate-type=staticlib", "--out-dir", out_dir.to_str().unwrap(), "slib.rs"
                    ]);
                    jobserver.configure(&mut command);
                    assert!(command.status().unwrap().success(), "slib build failed");
                    println!("cargo::rustc-link-lib=slib");
                    println!("cargo::rustc-link-search={}", out_dir.display());
                }
            "#,
        )
        .file("slib.rs", &slib(2))
        .build();

    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .run();

    // 2 != 1
    p.cargo("test --lib")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_status(101)
        .with_stdout_data("...\n[..]doit assert failure[..]\n...")
        .run();

    // Fix the mistake.
    p.change_file("slib.rs", &slib(1));

    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .run();
    // This should recompile with the new static lib, and the test should pass.
    p.cargo("test --lib")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .run();
}

#[cargo_test(nightly, reason = "requires -Zchecksum-hash-algorithm")]
fn script_fails_stay_dirty() {
    // Check if a script is aborted (such as hitting Ctrl-C) that it will re-run.
    // Steps:
    // 1. Build to establish fingerprints.
    // 2. Make a change that triggers the build script to re-run. Abort the
    //    script while it is running.
    // 3. Run the build again and make sure it re-runs the script.
    let p = project()
        .file(
            "build.rs",
            r#"
                mod helper;
                fn main() {
                    println!("cargo::rerun-if-changed=build.rs");
                    helper::doit();
                }
            "#,
        )
        .file("helper.rs", "pub fn doit() {}")
        .file("src/lib.rs", "")
        .build();

    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .run();
    p.change_file("helper.rs", r#"pub fn doit() {panic!("Crash!");}"#);
    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_stderr_data("...\n[..]Crash![..]\n...")
        .with_status(101)
        .run();
    // There was a bug where this second call would be "fresh".
    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_stderr_data("...\n[..]Crash![..]\n...")
        .with_status(101)
        .run();
}

#[cargo_test(nightly, reason = "requires -Zchecksum-hash-algorithm")]
fn simulated_docker_deps_stay_cached() {
    // Test what happens in docker where the nanoseconds are zeroed out.
    Package::new("regdep", "1.0.0").publish();
    Package::new("regdep_old_style", "1.0.0")
        .file("build.rs", "fn main() {}")
        .file("src/lib.rs", "")
        .publish();
    Package::new("regdep_env", "1.0.0")
        .file(
            "build.rs",
            r#"
            fn main() {
                println!("cargo::rerun-if-env-changed=SOMEVAR");
            }
            "#,
        )
        .file("src/lib.rs", "")
        .publish();
    Package::new("regdep_rerun", "1.0.0")
        .file(
            "build.rs",
            r#"
            fn main() {
                println!("cargo::rerun-if-changed=build.rs");
            }
            "#,
        )
        .file("src/lib.rs", "")
        .publish();

    let p = project()
        .file(
            "Cargo.toml",
            r#"
            [package]
            name = "foo"
            version = "0.1.0"
            edition = "2015"

            [dependencies]
            pathdep = { path = "pathdep" }
            regdep = "1.0"
            regdep_old_style = "1.0"
            regdep_env = "1.0"
            regdep_rerun = "1.0"
            "#,
        )
        .file(
            "src/lib.rs",
            "
            extern crate pathdep;
            extern crate regdep;
            extern crate regdep_old_style;
            extern crate regdep_env;
            extern crate regdep_rerun;
            ",
        )
        .file("build.rs", "fn main() {}")
        .file("pathdep/Cargo.toml", &basic_manifest("pathdep", "1.0.0"))
        .file("pathdep/src/lib.rs", "")
        .build();

    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .run();

    let already_zero = {
        // This happens on HFS with 1-second timestamp resolution,
        // or other filesystems where it just so happens to write exactly on a
        // 1-second boundary.
        let metadata = fs::metadata(p.root().join("src/lib.rs")).unwrap();
        let mtime = FileTime::from_last_modification_time(&metadata);
        mtime.nanoseconds() == 0
    };

    // Recursively remove `nanoseconds` from every path.
    fn zeropath(path: &Path) {
        for entry in walkdir::WalkDir::new(path)
            .into_iter()
            .filter_map(|e| e.ok())
        {
            let metadata = fs::metadata(entry.path()).unwrap();
            let mtime = metadata.modified().unwrap();
            let mtime_duration = mtime.duration_since(SystemTime::UNIX_EPOCH).unwrap();
            let trunc_mtime = FileTime::from_unix_time(mtime_duration.as_secs() as i64, 0);
            let atime = metadata.accessed().unwrap();
            let atime_duration = atime.duration_since(SystemTime::UNIX_EPOCH).unwrap();
            let trunc_atime = FileTime::from_unix_time(atime_duration.as_secs() as i64, 0);
            // Trust: retain this timestamp regression on the early 1.99 seed.
            if let Err(e) = filetime::set_file_times(entry.path(), trunc_atime, trunc_mtime) {
                // Windows doesn't allow changing filetimes on some things
                // (directories, other random things I'm not sure why). Just
                // ignore them.
                if e.kind() == std::io::ErrorKind::PermissionDenied {
                    println!("PermissionDenied filetime on {:?}", entry.path());
                } else {
                    panic!("FileTime error on {:?}: {:?}", entry.path(), e);
                }
            }
        }
    }
    zeropath(&p.root());
    zeropath(&paths::home());

    if already_zero {
        println!("already zero");
        // If it was already truncated, then everything stays fresh.
        p.cargo("build -v")
            .env("CARGO_BUILD_FINGERPRINT", "content")
            .arg("-Zchecksum-freshness")
            .masquerade_as_nightly_cargo(&["checksum-freshness"])
            .with_stderr_data(
                str![[r#"
[FRESH] pathdep [..]
[FRESH] regdep [..]
[FRESH] regdep_env [..]
[FRESH] regdep_old_style [..]
[FRESH] regdep_rerun [..]
[FRESH] foo [..]
[FINISHED] [..]

"#]]
                .unordered(),
            )
            .run();
    } else {
        println!("not already zero");
        // It is not ideal that `foo` gets recompiled, but that is the current
        // behavior. Currently mtimes are ignored for registry deps.
        //
        // Note that this behavior is due to the fact that `foo` has a build
        // script in "old" mode where it doesn't print `rerun-if-*`. In this
        // mode we use `Precalculated` to fingerprint a path dependency, where
        // `Precalculated` is an opaque string which has the most recent mtime
        // in it. It differs between builds because one has nsec=0 and the other
        // likely has a nonzero nsec. Hence, the rebuild.
        p.cargo("build -v")
            .env("CARGO_BUILD_FINGERPRINT", "content")
            .arg("-Zchecksum-freshness")
            .masquerade_as_nightly_cargo(&["checksum-freshness"])
            .with_stderr_data(
                str![[r#"
[FRESH] regdep [..]
[FRESH] pathdep [..]
[FRESH] regdep_env [..]
[DIRTY] foo v0.1.0 ([ROOT]/foo): the precalculated components changed
[COMPILING] foo v0.1.0 ([ROOT]/foo)
[FRESH] regdep_rerun [..]
[FRESH] regdep_old_style [..]
[RUNNING] `[ROOT]/foo/target/debug/build/foo/[HASH]/out/build_script_build`
[RUNNING] `rustc --crate-name foo [..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]]
                .unordered(),
            )
            .run();
    }
}

#[cargo_test(nightly, reason = "requires -Zchecksum-hash-algorithm")]
fn rename_with_path_deps() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.5.0"
                edition = "2015"
                authors = []

                [dependencies]
                a = { path = 'a' }
            "#,
        )
        .file("src/lib.rs", "extern crate a; pub fn foo() { a::foo(); }")
        .file(
            "a/Cargo.toml",
            r#"
                [package]
                name = "a"
                version = "0.5.0"
                edition = "2015"
                authors = []

                [dependencies]
                b = { path = 'b' }
            "#,
        )
        .file("a/src/lib.rs", "extern crate b; pub fn foo() { b::foo() }")
        .file(
            "a/b/Cargo.toml",
            r#"
                [package]
                name = "b"
                version = "0.5.0"
                edition = "2015"
                authors = []
            "#,
        )
        .file("a/b/src/lib.rs", "pub fn foo() { }");
    let p = p.build();

    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .run();

    // Now rename the root directory and rerun `cargo run`. Not only should we
    // not build anything but we also shouldn't crash.
    let mut new = p.root();
    new.pop();
    new.push("foo2");

    fs::rename(p.root(), &new).unwrap();

    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .cwd(&new)
        .with_stderr_data(str![[r#"
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test(nightly, reason = "requires -Zchecksum-hash-algorithm")]
fn move_target_directory_with_path_deps() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.5.0"
                edition = "2015"
                authors = []

                [dependencies]
                a = { path = "a" }
            "#,
        )
        .file(
            "a/Cargo.toml",
            r#"
                [package]
                name = "a"
                version = "0.5.0"
                edition = "2015"
                authors = []
            "#,
        )
        .file("src/lib.rs", "extern crate a; pub use a::print_msg;")
        .file(
            "a/build.rs",
            r###"
                use std::env;
                use std::fs;
                use std::path::Path;

                fn main() {
                    println!("cargo::rerun-if-changed=build.rs");
                    let out_dir = env::var("OUT_DIR").unwrap();
                    let dest_path = Path::new(&out_dir).join("hello.rs");
                    fs::write(&dest_path, r#"
                        pub fn message() -> &'static str {
                            "Hello, World!"
                        }
                    "#).unwrap();
                }
            "###,
        )
        .file(
            "a/src/lib.rs",
            r#"
            include!(concat!(env!("OUT_DIR"), "/hello.rs"));
            pub fn print_msg() { message(); }
            "#,
        );
    let p = p.build();

    let mut parent = p.root();
    parent.pop();

    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .run();

    let new_target = p.root().join("target2");
    fs::rename(p.root().join("target"), &new_target).unwrap();

    p.cargo("build")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .env("CARGO_TARGET_DIR", &new_target)
        .with_stderr_data(str![[r#"
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test(nightly, reason = "requires -Zchecksum-hash-algorithm")]
fn verify_source_before_recompile() {
    Package::new("bar", "0.1.0")
        .file("src/lib.rs", "")
        .publish();
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.1.0"
                edition = "2015"

                [dependencies]
                bar = "0.1.0"

                [lints.cargo]
                default = "allow"
            "#,
        )
        .file("src/lib.rs", "")
        .build();

    p.cargo("vendor --respect-source-config").run();
    p.change_file(
        ".cargo/config.toml",
        r#"
            [source.crates-io]
            replace-with = 'vendor'

            [source.vendor]
            directory = 'vendor'
        "#,
    );
    // Sanity check: vendoring works correctly.
    p.cargo("check --verbose")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_stderr_data(str![[r#"
[CHECKING] bar v0.1.0
[RUNNING] `rustc --crate-name bar [..] [ROOT]/foo/vendor/bar/src/lib.rs [..]
[CHECKING] foo v0.1.0 ([ROOT]/foo)
[RUNNING] `rustc --crate-name foo [..] src/lib.rs [..]
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
    // Now modify vendored crate.
    p.change_file(
        "vendor/bar/src/lib.rs",
        r#"compile_error!("You shall not pass!");"#,
    );
    // Should ignore modified sources without any recompile.
    p.cargo("check --verbose")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_stderr_data(str![[r#"
[FRESH] bar v0.1.0
[FRESH] foo v0.1.0 ([ROOT]/foo)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();

    // Add a `RUSTFLAGS` to trigger a recompile.
    //
    // Cargo should refuse to build because of checksum verification failure.
    // Cargo shouldn't recompile dependency `bar`.
    p.cargo("check --verbose")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .env("RUSTFLAGS", "-W warnings")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] the listed checksum of `[ROOT]/foo/vendor/bar/src/lib.rs` has changed:
expected: e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
actual:   66e843918c1d4ea8231af814f9f958958808249d4407de01114acb730ecd9bdf

directory sources are not intended to be edited, if modifications are required then it is recommended that `[patch]` is used with a forked copy of the source

"#]])
        .run();
}

#[cargo_test(nightly, reason = "requires -Zchecksum-hash-algorithm")]
fn skip_checksum_check_in_selected_cargo_home_subdirs() {
    let p = project()
        .at("cargo_home/registry/foo")
        .file("Cargo.toml", &basic_lib_manifest("foo"))
        .file("src/lib.rs", "")
        .build();
    let project_root = p.root();
    let cargo_home = project_root.parent().unwrap().parent().unwrap();
    p.cargo("check -v")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .env("CARGO_HOME", &cargo_home)
        .with_stderr_data(str![[r#"
[CHECKING] foo v0.5.0 ([ROOT]/cargo_home/registry/foo)
[RUNNING] `rustc --crate-name foo [..] src/lib.rs [..]
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
    p.change_file("src/lib.rs", "illegal syntax");
    p.cargo("check -v")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .env("CARGO_HOME", &cargo_home)
        .with_stderr_data(str![[r#"
[FRESH] foo v0.5.0 ([ROOT]/cargo_home/registry/foo)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test(nightly, reason = "requires -Zchecksum-hash-algorithm")]
fn use_checksum_cache_in_cargo_home() {
    let p = project()
        .at("cargo_home/foo")
        .file("Cargo.toml", &basic_lib_manifest("foo"))
        .file("src/lib.rs", "")
        .build();
    let project_root = p.root();
    let cargo_home = project_root.parent().unwrap();
    p.cargo("check -v")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .env("CARGO_HOME", &cargo_home)
        .with_stderr_data(str![[r#"
[CHECKING] foo v0.5.0 ([ROOT]/cargo_home/foo)
[RUNNING] `rustc --crate-name foo [..] src/lib.rs [..] src/lib.rs [..]
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
    p.change_file("src/lib.rs", "illegal syntax");
    p.cargo("check -v")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .env("CARGO_HOME", &cargo_home)
        .with_status(101)
        .with_stderr_data(str![[r#"
[DIRTY] foo v0.5.0 ([ROOT]/cargo_home/foo): file size changed (0 != 14) for `src/lib.rs`
[CHECKING] foo v0.5.0 ([ROOT]/cargo_home/foo)
[RUNNING] `rustc --crate-name foo [..] src/lib.rs [..]
...
[ERROR] could not compile `foo` (lib) due to 1 previous error
...
"#]])
        .run();
}

#[cargo_test(nightly, reason = "requires -Zchecksum-hash-algorithm")]
fn incremental_build_script_execution_got_new_mtime_and_cargo_check() {
    // See https://github.com/rust-lang/cargo/issues/16104
    let p = project()
        .file("src/lib.rs", "")
        .file("touch-me", "")
        .file(
            "build.rs",
            r#"fn main() { println!("cargo::rerun-if-changed=touch-me") }"#,
        )
        .build();

    p.cargo("check")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .env("CARGO_INCREMENTAL", "1")
        .with_stderr_data(str![[r#"
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();

    p.change_file("touch-me", "oops");

    // The first one is expected to rerun build script
    p.cargo("check -v")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .env("CARGO_INCREMENTAL", "1")
        .with_stderr_data(str![[r#"
[DIRTY] foo v0.0.1 ([ROOT]/foo): the file `touch-me` has changed ([TIME_DIFF_AFTER_LAST_BUILD])
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `[ROOT]/foo/target/debug/build/foo/[HASH]/out/build_script_build`
[RUNNING] `rustc --crate-name foo [..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();

    // subsequent cargo check gets stuck...
    p.cargo("check -v")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .env("CARGO_INCREMENTAL", "1")
        .with_stderr_data(str![[r#"
[FRESH] foo v0.0.1 ([ROOT]/foo)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();

    p.cargo("check -v")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .env("CARGO_INCREMENTAL", "1")
        .with_stderr_data(str![[r#"
[FRESH] foo v0.0.1 ([ROOT]/foo)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test(nightly, reason = "requires -Zchecksum-hash-algorithm")]
fn symlink_to_package() {
    // Illustrates what happens when the path is a symlink, and the symlink
    // target changes.
    if !cargo_test_support::symlink_supported() {
        return;
    }
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                edition = "2015"

                [dependencies]
                bar = { path = "bar" }
            "#,
        )
        .file(
            "src/main.rs",
            r#"
                fn main() {
                    bar::bar();
                }
            "#,
        )
        .file("bar1/Cargo.toml", &basic_manifest("bar", "1.0.0"))
        .file(
            "bar1/src/lib.rs",
            r#"
                pub fn bar() {
                    println!("one");
                }
            "#,
        )
        .file("bar2/Cargo.toml", &basic_manifest("bar", "1.0.0"))
        .file(
            "bar2/src/lib.rs",
            r#"
                pub fn bar() {
                    println!("two");
                }
            "#,
        )
        .symlink_dir("bar1", "bar")
        .build();
    p.cargo("check")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_stderr_data(str![[r#"
[LOCKING] 1 package to highest compatible version
[CHECKING] bar v1.0.0 ([ROOT]/foo/bar)
[CHECKING] foo v0.0.0 ([ROOT]/foo)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
    let bar_path = p.root().join("bar");
    cargo_util::paths::remove_file(&bar_path).unwrap();
    p.symlink("bar2", "bar");
    // Checksums detect the changed source behind the symlink.
    p.cargo("check")
        .env("CARGO_BUILD_FINGERPRINT", "content")
        .arg("-Zchecksum-freshness")
        .masquerade_as_nightly_cargo(&["checksum-freshness"])
        .with_stderr_data(str![[r#"
[CHECKING] bar v1.0.0 ([ROOT]/foo/bar)
[CHECKING] foo v0.0.0 ([ROOT]/foo)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

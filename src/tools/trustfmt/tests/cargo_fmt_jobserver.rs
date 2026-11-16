// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Execute the real frontend with a real zero-supplemental GNU fixture owner.
//! Probe children inspect inherited pipes; they never insert or acquire tokens.

#![cfg(unix)]

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::thread;
use std::time::{Duration, Instant};

use jobserver_utils::Jobserver;

struct Fixture {
    _temp: tempfile::TempDir,
    root: PathBuf,
    cargo: PathBuf,
    formatter: PathBuf,
    log: PathBuf,
}

impl Fixture {
    fn new(cargo_body: &str) -> Self {
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path().to_owned();
        let cargo = root.join("cargo-probe");
        let formatter = root.join("formatter-probe");
        let log = root.join("calls");
        let check = r#"#!/bin/sh
set -eu
auth=
for option in ${CARGO_MAKEFLAGS-}; do
  case "$option" in --jobserver-auth=*,*) auth=${option#--jobserver-auth=} ;; esac
done
if test -z "$auth"; then echo missing-gnu-auth >&2; exit 91; fi
read_fd=${auth%,*}
write_fd=${auth#*,}
if ! test -p "/dev/fd/$read_fd" || ! test -p "/dev/fd/$write_fd"; then
  echo closed-gnu-pipe >&2; exit 92
fi
"#;
        script(&cargo, &format!("{check}{cargo_body}\n"));
        script(
            &formatter,
            &format!(
                "{check}{}",
                r#"printf 'formatter:%s\n' "$*" >> "$FMT_TEST_LOG"
"#
            ),
        );
        Self {
            _temp: temp,
            root,
            cargo,
            formatter,
            log,
        }
    }

    fn real_cargo() -> &'static str {
        r#"printf 'cargo:%s\n' "$*" >> "$FMT_TEST_LOG"
exec "$FMT_TEST_REAL_TARGO" "$@""#
    }

    fn command(&self) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_cargo-fmt"));
        command
            .current_dir(&self.root)
            .env("CARGO", &self.cargo)
            .env("TRUSTFMT", &self.formatter)
            .env("FMT_TEST_REAL_TARGO", env!("CARGO"))
            .env("FMT_TEST_LOG", &self.log);
        command
    }

    fn run(&self, args: &[&str]) -> Output {
        let scheduler = Jobserver::new(0).expect("real zero-supplemental GNU fixture");
        let mut command = self.command();
        command.args(args);
        scheduler.configure(&mut command);
        bounded_output(command)
    }

    fn calls(&self) -> Vec<String> {
        fs::read_to_string(&self.log)
            .unwrap_or_default()
            .lines()
            .map(str::to_owned)
            .collect()
    }
}

fn script(path: &Path, contents: &str) {
    fs::write(path, contents).unwrap();
    fs::set_permissions(path, fs::Permissions::from_mode(0o700)).unwrap();
}

fn package(root: &Path, name: &str, dependency: Option<(&str, &str)>) {
    fs::create_dir_all(root.join("src")).unwrap();
    let mut manifest = format!("[package]\nname={name:?}\nversion=\"0.0.0\"\nedition=\"2021\"\n");
    if let Some((name, path)) = dependency {
        manifest.push_str(&format!("[dependencies]\n{name}={{path={path:?}}}\n"));
    }
    fs::write(root.join("Cargo.toml"), manifest).unwrap();
    fs::write(root.join("src/lib.rs"), "pub fn marker() {}\n").unwrap();
}

fn bounded_output(mut command: Command) -> Output {
    // Own a process group so timeout cleanup also reaps our probe descendants.
    command
        .process_group(0)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = command.spawn().expect("spawn actual frontend");
    let deadline = Instant::now() + Duration::from_secs(60);
    loop {
        if child.try_wait().unwrap().is_some() {
            return child.wait_with_output().unwrap();
        }
        if Instant::now() >= deadline {
            let group = format!("-{}", child.id());
            let status = Command::new("/bin/kill")
                .args(["-KILL", "--", &group])
                .status();
            if !status.is_ok_and(|status| status.success()) {
                let _ = child.kill();
            }
            let output = child.wait_with_output().unwrap();
            panic!(
                "frontend fixture timed out: {}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
        thread::sleep(Duration::from_millis(10));
    }
}

#[test]
fn formatter_version_child_receives_the_real_zero_budget_pipe() {
    let fixture = Fixture::new(Fixture::real_cargo());
    let output = fixture.run(&["--version"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(fixture.calls(), ["formatter:--version"]);
}

#[test]
fn recursive_metadata_workspace_lookup_and_formatter_keep_the_same_scheduler() {
    let fixture = Fixture::new(Fixture::real_cargo());
    let member = fixture.root.join("workspace/member");
    let outside = fixture.root.join("outside");
    package(&member, "member", Some(("outside", "../../outside")));
    package(&outside, "outside", None);
    fs::write(
        fixture.root.join("workspace/Cargo.toml"),
        "[workspace]\nmembers=[\"member\"]\nresolver=\"2\"\n",
    )
    .unwrap();
    // An explicit root prevents an unrelated ancestor workspace from owning it.
    let outside_manifest = outside.join("Cargo.toml");
    let manifest = fs::read_to_string(&outside_manifest).unwrap() + "\n[workspace]\n";
    fs::write(outside_manifest, manifest).unwrap();
    let manifest = fixture.root.join("workspace/Cargo.toml");
    let output = fixture.run(&["--all", "--manifest-path", manifest.to_str().unwrap()]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let calls = fixture.calls();
    assert!(
        calls.iter().any(|s| s.starts_with("cargo:metadata ")),
        "{calls:?}"
    );
    assert!(
        calls.iter().any(|s| s.starts_with("cargo:locate-project ")),
        "{calls:?}"
    );
    assert!(
        calls.iter().any(|s| s.starts_with("formatter:")),
        "{calls:?}"
    );
}

#[test]
fn metadata_retry_preserves_scheduler_and_terminal_stderr() {
    let fixture = Fixture::new(
        r#"printf 'cargo:%s\n' "$*" >> "$FMT_TEST_LOG"
case " $* " in *" --offline "*) echo offline-fixture-refusal >&2; exit 23 ;; esac
echo terminal-online-fixture-refusal >&2
exit 24"#,
    );
    let output = fixture.run(&[]);
    assert!(!output.status.success());
    let error = String::from_utf8_lossy(&output.stderr);
    assert!(error.contains("terminal-online-fixture-refusal"), "{error}");
    let calls = fixture.calls();
    assert_eq!(calls.len(), 2, "{calls:?}");
    assert!(calls[0].contains("--offline"));
    assert!(!calls[1].contains("--offline"));
}

#[test]
fn malformed_scheduler_refuses_before_any_formatter_or_metadata_child() {
    let fixture = Fixture::new(Fixture::real_cargo());
    let mut command = fixture.command();
    command.env("CARGO_MAKEFLAGS", "--jobserver-auth=not-a-descriptor");
    command.arg("--version");
    let output = bounded_output(command);
    assert!(!output.status.success());
    let error = String::from_utf8_lossy(&output.stderr);
    assert!(
        error.contains("cannot inherit formatter jobserver"),
        "{error}"
    );
    assert!(fixture.calls().is_empty());
}

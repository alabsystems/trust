// Copyright 2026 Andrew Yates
use std::io::{Read, Seek};

use super::*;

struct Actor(std::process::Child);
impl Drop for Actor {
    fn drop(&mut self) {
        if !matches!(self.0.try_wait(), Ok(Some(_))) {
            let _ = self.0.kill();
            if self.0.wait().is_err() {
                std::process::abort();
            }
        }
    }
}

fn output(command: &mut Command) -> std::process::Output {
    let mut stdout = tempfile::tempfile().unwrap();
    let mut stderr = tempfile::tempfile().unwrap();
    command.stdout(stdout.try_clone().unwrap()).stderr(stderr.try_clone().unwrap());
    let mut actor = Actor(command.spawn().unwrap());
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(60);
    let status = loop {
        match actor.0.try_wait() {
            Ok(Some(status)) => break Some(status),
            Ok(None) if std::time::Instant::now() < deadline => {
                std::thread::sleep(std::time::Duration::from_millis(2))
            }
            _ => break None,
        }
    };
    drop(actor); // Kill/reap only this owned fixture before any assertion or capture error.
    stdout.rewind().unwrap();
    stderr.rewind().unwrap();
    let mut out = Vec::new();
    let mut err = Vec::new();
    stdout.read_to_end(&mut out).unwrap();
    stderr.read_to_end(&mut err).unwrap();
    let status = status.unwrap_or_else(|| {
        panic!("entry fixture failed to retire: {}", String::from_utf8_lossy(&err))
    });
    std::process::Output { status, stdout: out, stderr: err }
}

const ROLE: &str = "TRUST_BOOTSTRAP_ENTRY_CONTROL";

#[test]
fn uncaptured_actor_consumes_its_marker_and_cannot_dispatch_a_seed_probe() {
    const NAME: &str =
        "test_entry::tests::uncaptured_actor_consumes_its_marker_and_cannot_dispatch_a_seed_probe";
    if std::env::var_os(ROLE).is_some() {
        assert!(std::env::var_os(UNCAPTURED_ACTOR).is_none());
        let mut command = Command::new("/no/such/seed-probe");
        let error = crate::utils::metadata_scheduler::output(&mut command, true, true).unwrap_err();
        assert_eq!(error.kind(), std::io::ErrorKind::Other);
        return;
    }
    let output = output(
        uncaptured_actor(Command::new(std::env::current_exe().unwrap()))
            .args(["--exact", NAME])
            .env(ROLE, "child"),
    );
    assert!(output.status.success(), "{output:?}");
}

#[test]
fn uncaptured_actor_refuses_every_native_advertisement_before_libtest() {
    const NAME: &str =
        "test_entry::tests::uncaptured_actor_refuses_every_native_advertisement_before_libtest";
    if std::env::var_os(ROLE).is_some() {
        panic!("native advertisement reached an uncaptured test body");
    }
    for key in native_advertisements() {
        let output = output(
            uncaptured_actor(Command::new(std::env::current_exe().unwrap()))
                .args(["--exact", NAME])
                .env(ROLE, "child")
                .env(key, ""),
        );
        assert_eq!(output.status.code(), Some(75), "{key}: {output:?}");
    }
}

#[test]
fn normal_entry_refuses_malformed_transport_before_libtest() {
    const NAME: &str = "test_entry::tests::normal_entry_refuses_malformed_transport_before_libtest";
    if std::env::var_os(ROLE).is_some() {
        panic!("malformed scheduler reached a test body");
    }
    // Clear outer custody only to construct a negative process fixture, then
    // advertise a deliberately invalid GNU descriptor pair at its actual entry.
    let mut command = uncaptured_actor(Command::new(std::env::current_exe().unwrap()));
    command.env_remove(UNCAPTURED_ACTOR);
    let output = output(
        command
            .args(["--exact", NAME])
            .env(ROLE, "child")
            .env("CARGO_MAKEFLAGS", "--jobserver-auth=999998,999999 -j"),
    );
    assert_eq!(output.status.code(), Some(75), "{output:?}");
}

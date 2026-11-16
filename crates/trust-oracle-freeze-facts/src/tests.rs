// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

use super::*;

static NEXT: AtomicU64 = AtomicU64::new(0);

struct World(PathBuf);

impl World {
    fn new() -> Self {
        let parent = std::env::temp_dir().join(".ubd/oracle-freeze-facts-tests");
        fs::create_dir_all(&parent).unwrap();
        let nonce =
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
        let path = parent.join(format!(
            "{}-{nonce}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        let world = Self(path);
        world.git(&["init", "-q"]);
        world
    }

    fn command(&self) -> Command {
        let mut command = Command::new("git");
        command.args(["-c", "commit.gpgsign=false", "-C"]).arg(&self.0);
        command
            .env("GIT_AUTHOR_NAME", "Oracle fact fixture")
            .env("GIT_AUTHOR_EMAIL", "fixture@example.invalid")
            .env("GIT_COMMITTER_NAME", "Oracle fact fixture")
            .env("GIT_COMMITTER_EMAIL", "fixture@example.invalid");
        command
    }

    fn git(&self, args: &[&str]) -> String {
        let output = self.command().args(args).output().unwrap();
        assert!(
            output.status.success(),
            "git {args:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8(output.stdout).unwrap().trim().into()
    }

    fn write(&self, path: &str, bytes: &[u8]) {
        let path = self.0.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, bytes).unwrap();
    }

    fn commit(&self) -> String {
        self.git(&["add", "."]);
        self.git(&["commit", "-q", "-m", "owned fixture"]);
        self.git(&["rev-parse", "HEAD"])
    }
}

impl Drop for World {
    fn drop(&mut self) {
        if std::thread::panicking() {
            eprintln!("failed oracle-fact world retained: {}", self.0.display());
        } else {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }
}

fn request(path: &str, function: &str) -> Request {
    Request { path: path.into(), function: function.into() }
}

#[test]
fn repeated_citations_share_blob_facts_without_losing_order_or_counts() {
    let world = World::new();
    let source = b"#[test]\nfn cited() {}\nfn ordinary() {}\n";
    world.write("a.rs", source);
    world.write("alias.rs", source);
    world.write("src/nested.rs", source);
    let commit = world.commit();
    let requests = vec![
        request("a.rs", "cited"),
        request("a.rs", "ordinary"),
        request("missing.rs", "cited"),
        request("src", "cited"),
        request("src/nested.rs", "cited"),
        request("alias.rs", "cited"),
        request("a.rs", "cited"),
    ];
    let observed = committed_facts(&world.0, &commit, &requests).unwrap();
    assert_eq!(
        observed.facts,
        [
            Fact::Test,
            Fact::MissingTest,
            Fact::NotFile,
            Fact::NotFile,
            Fact::Test,
            Fact::Test,
            Fact::Test
        ]
    );
    assert_eq!(observed.parsed_blobs, 1);
}

#[test]
fn source_and_destination_are_fresh_independent_observations() {
    let world = World::new();
    world.write("source.rs", b"#[test]\nfn witness() {}\n");
    let destination = world.commit();
    world.write("source.rs", b"fn witness() {}\n");
    let pushed = world.commit();
    let requests = [request("source.rs", "witness")];
    assert_eq!(committed_facts(&world.0, &pushed, &requests).unwrap().facts, [Fact::MissingTest]);
    assert_eq!(committed_facts(&world.0, &destination, &requests).unwrap().facts, [Fact::Test]);
    assert_eq!(committed_facts(&world.0, &pushed, &requests).unwrap().facts, [Fact::MissingTest]);
}

#[cfg(unix)]
#[test]
fn committed_symlink_blob_is_read_as_data_without_following_its_target() {
    let world = World::new();
    std::os::unix::fs::symlink("#[test]\nfn linked() {}\n", world.0.join("link.rs")).unwrap();
    let commit = world.commit();
    let observed = committed_facts(&world.0, &commit, &[request("link.rs", "linked")]).unwrap();
    assert_eq!(observed.facts, [Fact::Test]);
}

#[test]
fn missing_blob_is_a_git_error_rather_than_an_absent_path() {
    let world = World::new();
    let mut child = world
        .command()
        .args(["mktree", "-z", "--missing"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(b"100644 blob 1111111111111111111111111111111111111111\tmissing.rs\0")
        .unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success());
    let tree = String::from_utf8(output.stdout).unwrap();
    let commit = world.git(&["commit-tree", tree.trim(), "-m", "missing blob fixture"]);
    let observed = committed_facts(&world.0, &commit, &[request("missing.rs", "cited")]).unwrap();
    assert_eq!(observed.facts, [Fact::GitError]);
}

#[test]
fn replacement_namespace_requires_the_original_reader() {
    let world = World::new();
    world.write("a.rs", b"#[test]\nfn cited() {}\n");
    world.write("b.rs", b"fn cited() {}\n");
    let commit = world.commit();
    let original = world.git(&["rev-parse", &format!("{commit}:a.rs")]);
    let replacement = world.git(&["rev-parse", &format!("{commit}:b.rs")]);
    world.git(&["replace", &original, &replacement]);
    assert!(matches!(
        committed_facts(&world.0, &commit, &[request("a.rs", "cited")]),
        Err(Error::Unsupported(_))
    ));
}

#[test]
fn malformed_path_does_not_change_other_requests_failure_categories() {
    let world = World::new();
    world.write("a.rs", b"#[test]\nfn cited() {}\n");
    let commit = world.commit();
    let paths = ["a.rs", "../a.rs", "./a.rs", "missing.rs"];
    let observed =
        committed_facts(&world.0, &commit, &paths.map(|path| request(path, "cited"))).unwrap();
    for (path, fact) in paths.into_iter().zip(observed.facts) {
        let output = world
            .command()
            .args(["ls-tree", "-z", "--full-tree", &commit, "--", path])
            .output()
            .unwrap();
        let expected = if !output.status.success() {
            Fact::GitError
        } else if output.stdout.is_empty() {
            Fact::NotFile
        } else {
            let first = output.stdout.split(|byte| *byte == 0).next().unwrap();
            let name = first.splitn(2, |byte| *byte == b'\t').nth(1).unwrap();
            if name == path.as_bytes() { Fact::Test } else { Fact::NotFile }
        };
        assert_eq!(fact, expected, "{path}");
    }
}

#[test]
fn request_protocol_rejects_partial_or_injected_fields() {
    assert_eq!(
        read_requests(&b"a.rs\0test_1\0a.rs\0test_1\0"[..]).unwrap(),
        [request("a.rs", "test_1"), request("a.rs", "test_1")]
    );
    for bytes in [
        &b"a.rs\0"[..],
        &b"a.rs\0name"[..],
        &b"a.rs\0name\nother\0"[..],
        &b"a b.rs\0name\0"[..],
        &b"\0name\0"[..],
    ] {
        assert!(read_requests(bytes).is_err(), "{bytes:?}");
    }
    assert!(committed_facts(Path::new("missing-repo"), "bad", &[]).is_err());
    assert!(read_requests(vec![0; MAX_REQUEST_BYTES as usize].as_slice()).is_err());
    assert!(matches!(
        read_requests(b"a\0b\0".repeat(MAX_REQUESTS + 1).as_slice()),
        Err(Error::Unsupported(_))
    ));
}

#[test]
fn aggregate_fact_limits_refuse_without_publishing_partial_facts() {
    let world = World::new();
    world.write("a.rs", b"#[test]\nfn first() {}\n");
    world.write("b.rs", b"#[test]\nfn second() {}\n");
    let commit = world.commit();
    let requests = [request("a.rs", "first"), request("b.rs", "second")];
    for budget in [
        Budget { blob_bytes: 30, names: 100, name_bytes: 100 },
        Budget { blob_bytes: 100, names: 1, name_bytes: 100 },
        Budget { blob_bytes: 100, names: 100, name_bytes: 6 },
    ] {
        assert!(matches!(
            committed_facts_with_budget(&world.0, &commit, &requests, budget),
            Err(Error::Unsupported(_))
        ));
    }
    assert_eq!(
        committed_facts(&world.0, &commit, &requests).unwrap().facts,
        [Fact::Test, Fact::Test]
    );
}

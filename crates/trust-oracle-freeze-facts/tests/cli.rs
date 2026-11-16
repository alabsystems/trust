// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};

struct World(PathBuf);

impl World {
    fn new() -> Self {
        let nonce =
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
        let root =
            std::env::temp_dir().join(format!("oracle-freeze-cli-{}-{nonce}", std::process::id()));
        fs::create_dir(&root).unwrap();
        let world = Self(root);
        world.git(&["init", "-q", "--object-format=sha1"], b"");
        world
    }

    fn git(&self, args: &[&str], input: &[u8]) -> Vec<u8> {
        let mut child = Command::new("git")
            .arg("-C")
            .arg(&self.0)
            .args(args)
            .env("GIT_AUTHOR_NAME", "Owned fact fixture")
            .env("GIT_AUTHOR_EMAIL", "fixture@example.invalid")
            .env("GIT_COMMITTER_NAME", "Owned fact fixture")
            .env("GIT_COMMITTER_EMAIL", "fixture@example.invalid")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child.stdin.take().unwrap().write_all(input).unwrap();
        let output = child.wait_with_output().unwrap();
        assert!(
            output.status.success(),
            "git {args:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        output.stdout
    }

    fn observe(&self, commit: &str, icase: bool) -> Output {
        let mut command = Command::new(env!("CARGO_BIN_EXE_trust-oracle-freeze-facts"));
        command.arg("--repo").arg(&self.0).args(["--commit", commit]);
        if icase {
            command.env("GIT_ICASE_PATHSPECS", "1");
        }
        let mut child = command
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child.stdin.take().unwrap().write_all(b"a.rs\0cited\0a.rs\0cited\0").unwrap();
        child.wait_with_output().unwrap()
    }
}

impl Drop for World {
    fn drop(&mut self) {
        if std::thread::panicking() {
            eprintln!("failed native fact world retained: {}", self.0.display());
        } else {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }
}

fn oid(bytes: Vec<u8>) -> String {
    String::from_utf8(bytes).unwrap().trim().into()
}

#[test]
fn actual_cli_preserves_duplicates_and_refuses_case_insensitive_pathspec_profile() {
    let world = World::new();
    let blob = oid(world.git(&["hash-object", "-w", "--stdin"], b"#[test]\nfn cited() {}\n"));
    // Git objects can carry both names even on a case-insensitive filesystem.
    let tree = oid(world.git(
        &["mktree"],
        format!("100644 blob {blob}\tA.rs\n100644 blob {blob}\ta.rs\n").as_bytes(),
    ));
    let commit = oid(world.git(&["commit-tree", &tree, "-m", "owned fixture"], b""));
    let positive = world.observe(&commit, false);
    assert!(positive.status.success(), "{}", String::from_utf8_lossy(&positive.stderr));
    assert_eq!(positive.stdout, b"trust-oracle-freeze-facts-v1 2\ntest\ntest\n");
    let output = Command::new("git")
        .arg("-C")
        .arg(&world.0)
        .args(["ls-tree", "-z", "--full-tree", &commit, "--", "a.rs"])
        .env("GIT_ICASE_PATHSPECS", "1")
        .output()
        .unwrap();
    if output.status.success() {
        let first = output.stdout.split(|byte| *byte == 0).next().unwrap();
        assert!(first.ends_with(b"\tA.rs")); // Legacy first-entry rule says NotFile.
    } else {
        // Some Git versions reject icase for ls-tree. The legacy path must
        // retain that actual GitError rather than invent an exact-path Test.
        let diagnostic = String::from_utf8_lossy(&output.stderr);
        assert!(
            diagnostic.contains("pathspec magic not supported") && diagnostic.contains("icase"),
            "{diagnostic}"
        );
    }
    let unavailable = world.observe(&commit, true);
    assert_eq!(unavailable.status.code(), Some(3));
    assert!(unavailable.stdout.is_empty());
    assert!(String::from_utf8_lossy(&unavailable.stderr).contains("GIT_ICASE_PATHSPECS"));
}

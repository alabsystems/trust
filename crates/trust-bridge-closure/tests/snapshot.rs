//! Real Git regressions for exact producer inputs, independent of live files.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT: AtomicUsize = AtomicUsize::new(0);
const PREFIX: &str = "lean/trust_ir-semantics";

struct Repo(PathBuf);

impl Repo {
    fn new() -> Self {
        Self::with_format("sha1")
    }

    fn with_format(format: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "bridge-snapshot-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        fs::write(path.join("empty-config"), "").unwrap();
        fs::create_dir(path.join("repo")).unwrap();
        let repo = Self(path);
        repo.git(&["init", "-q", "-b", "main", &format!("--object-format={format}")]);
        repo.write("lean-toolchain", b"leanprover/lean4:v4.8.0\n");
        repo.write("lakefile.lean", b"import Lake\nopen Lake DSL\npackage snapshot\n");
        repo.write("Module.lean", b"def answer := 42\n");
        repo.commit();
        repo
    }

    fn root(&self) -> PathBuf {
        self.0.join("repo")
    }
    fn source(&self) -> PathBuf {
        self.root().join(PREFIX)
    }
    fn dest(&self) -> PathBuf {
        self.0.join("export")
    }

    fn write(&self, path: &str, bytes: &[u8]) {
        let path = self.source().join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, bytes).unwrap();
    }

    fn git(&self, args: &[&str]) -> String {
        let vars = Command::new("git").args(["rev-parse", "--local-env-vars"]).output().unwrap();
        assert!(vars.status.success());
        let mut command = Command::new("git");
        for key in std::str::from_utf8(&vars.stdout).unwrap().lines() {
            command.env_remove(key);
        }
        let output = command
            .arg("-C")
            .arg(self.root())
            .args(args)
            .env("GIT_CONFIG_GLOBAL", self.0.join("empty-config"))
            .env("GIT_CONFIG_NOSYSTEM", "1")
            .env("GIT_AUTHOR_NAME", "snapshot fixture")
            .env("GIT_AUTHOR_EMAIL", "fixture@example.invalid")
            .env("GIT_COMMITTER_NAME", "snapshot fixture")
            .env("GIT_COMMITTER_EMAIL", "fixture@example.invalid")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "git {args:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8(output.stdout).unwrap().trim().to_owned()
    }

    fn commit(&self) -> String {
        self.git(&["add", "-A"]);
        self.git(&["commit", "-q", "-m", "fixture"]);
        self.git(&["rev-parse", "HEAD"])
    }

    fn command(&self, commit: &str, dest: &Path) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_bridge_closure"));
        command.arg("--snapshot-lean").arg(self.root()).arg(commit).arg(dest);
        command
    }

    fn export(&self, commit: &str) -> Output {
        self.command(commit, &self.dest()).output().unwrap()
    }
}

impl Drop for Repo {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

fn succeeds(output: &Output) {
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert!(String::from_utf8_lossy(&output.stdout).starts_with("snapshot:"));
}

fn refuses(output: &Output) {
    assert_eq!(output.status.code(), Some(1), "{}", String::from_utf8_lossy(&output.stderr));
    assert!(output.stdout.is_empty());
    assert!(
        String::from_utf8_lossy(&output.stderr).starts_with("bridge_closure: snapshot failed:")
    );
}

#[test]
fn fixed_revision_excludes_live_edits_index_changes_and_ignored_files() {
    let repo = Repo::new();
    repo.write(".gitignore", b"Ignored.lean\n.lake/\n");
    let original = repo.commit();
    repo.write("Module.lean", b"def answer := 0\n");
    repo.commit();
    repo.write("Module.lean", b"def answer := 1\n");
    repo.git(&["add", "."]);
    repo.write("Module.lean", b"def answer := 2\n");
    repo.write("Ignored.lean", b"injected ignored source\n");
    repo.write(".lake/build/lib/forged.olean", b"not producer output");
    let status = repo.git(&["status", "--porcelain=v1", "--untracked-files=all"]);
    succeeds(&repo.export(&original));
    assert_eq!(fs::read(repo.dest().join("Module.lean")).unwrap(), b"def answer := 42\n");
    assert!(!repo.dest().join("Ignored.lean").exists());
    assert!(!repo.dest().join(".lake").exists());
    assert_eq!(repo.git(&["status", "--porcelain=v1", "--untracked-files=all"]), status);
    assert_eq!(fs::read(repo.source().join("Module.lean")).unwrap(), b"def answer := 2\n");
}

#[test]
fn raw_blobs_ignore_archive_attributes_checkout_filters_and_binary_framing() {
    let repo = Repo::new();
    repo.write(".gitattributes", b"Module.lean export-ignore\nRaw.txt export-subst\n*.bin -text\n*.lean filter=deny text eol=crlf ident\n");
    repo.write("Raw.txt", b"$Format:%H$\r\n");
    repo.write("Filtered.lean", b"-- $Id$\ndef raw := 1\n");
    let bytes =
        b"\0\xff\n0123456789012345678901234567890123456789 blob 123\nwith\0binary\r\n".repeat(4096);
    repo.write("odd name.bin", &bytes);
    let commit = repo.commit();
    repo.git(&["config", "core.autocrlf", "true"]);
    repo.git(&["config", "filter.deny.smudge", "false"]);
    repo.git(&["config", "filter.deny.required", "true"]);
    succeeds(&repo.export(&commit));
    assert_eq!(fs::read(repo.dest().join("Module.lean")).unwrap(), b"def answer := 42\n");
    assert_eq!(fs::read(repo.dest().join("Raw.txt")).unwrap(), b"$Format:%H$\r\n");
    assert_eq!(fs::read(repo.dest().join("odd name.bin")).unwrap(), bytes);
    assert_eq!(fs::read(repo.dest().join("Filtered.lean")).unwrap(), b"-- $Id$\ndef raw := 1\n");
}

#[test]
fn replacement_refs_cannot_change_the_exported_commit_or_blob() {
    let repo = Repo::new();
    let original = repo.git(&["rev-parse", "HEAD"]);
    let old_blob = repo.git(&["rev-parse", "HEAD:lean/trust_ir-semantics/Module.lean"]);
    repo.write("Module.lean", b"def answer := 999\n");
    let replacement = repo.commit();
    let new_blob = repo.git(&["rev-parse", "HEAD:lean/trust_ir-semantics/Module.lean"]);
    repo.git(&["replace", &old_blob, &new_blob]);
    repo.git(&["replace", &original, &replacement]);
    succeeds(&repo.export(&original));
    assert_eq!(fs::read(repo.dest().join("Module.lean")).unwrap(), b"def answer := 42\n");
}

#[test]
fn inherited_repository_and_index_do_not_redirect_snapshot() {
    let repo = Repo::new();
    let foreign = Repo::new();
    repo.write("OnlyHere.lean", b"def localOnly := 1\n");
    let commit = repo.commit();
    let output = repo
        .command(&commit, &repo.dest())
        .env("GIT_DIR", foreign.root().join(".git"))
        .env("GIT_COMMON_DIR", foreign.root().join(".git"))
        .env("GIT_WORK_TREE", foreign.root())
        .env("GIT_INDEX_FILE", foreign.root().join(".git/index"))
        .env("GIT_OBJECT_DIRECTORY", foreign.root().join(".git/objects"))
        .output()
        .unwrap();
    succeeds(&output);
    assert_eq!(fs::read(repo.dest().join("Module.lean")).unwrap(), b"def answer := 42\n");
}

#[test]
fn unreadable_blob_removes_partial_output_without_touching_source() {
    let repo = Repo::new();
    let commit = repo.git(&["rev-parse", "HEAD"]);
    let blob = repo.git(&["rev-parse", "HEAD:lean/trust_ir-semantics/lean-toolchain"]);
    let mirror = repo.0.join("mirror.git");
    repo.git(&["clone", "-q", "--bare", "--no-hardlinks", ".", mirror.to_str().unwrap()]);
    repo.git(&["config", "remote.origin.url", mirror.to_str().unwrap()]);
    repo.git(&["config", "remote.origin.promisor", "true"]);
    repo.git(&["config", "extensions.partialClone", "origin"]);
    fs::remove_file(repo.root().join(".git/objects").join(&blob[..2]).join(&blob[2..])).unwrap();
    refuses(&repo.export(&commit));
    assert!(!repo.dest().exists());
    assert_eq!(
        fs::read(repo.source().join("lean-toolchain")).unwrap(),
        b"leanprover/lean4:v4.8.0\n"
    );
    // The promisor has this blob; only an explicit later read may fetch it.
    repo.git(&["-c", "protocol.file.allow=always", "cat-file", "-e", &blob]);
}

#[test]
fn existing_destination_and_noncommit_revisions_are_preserved_and_refused() {
    let repo = Repo::new();
    let commit = repo.git(&["rev-parse", "HEAD"]);
    fs::create_dir(repo.dest()).unwrap();
    fs::write(repo.dest().join("keep"), b"owned elsewhere").unwrap();
    refuses(&repo.export(&commit));
    assert_eq!(fs::read(repo.dest().join("keep")).unwrap(), b"owned elsewhere");
    fs::remove_dir_all(repo.dest()).unwrap();
    repo.git(&["tag", "-a", "-m", "tag", "annotated", &commit]);
    let tag = repo.git(&["rev-parse", "annotated"]);
    for bad in ["HEAD", "--help", &commit[..12], &tag] {
        refuses(&repo.export(bad));
        assert!(!repo.dest().exists());
    }
}

#[test]
fn missing_toolchain_and_gitlinks_refuse_before_creating_destination() {
    let repo = Repo::new();
    repo.git(&["rm", "lean/trust_ir-semantics/lean-toolchain"]);
    let missing = repo.commit();
    refuses(&repo.export(&missing));
    assert!(!repo.dest().exists());
    repo.write("lean-toolchain", b"leanprover/lean4:v4.8.0\n");
    repo.git(&["add", "."]);
    repo.git(&[
        "update-index",
        "--add",
        "--cacheinfo",
        &format!("160000,{missing},{PREFIX}/external"),
    ]);
    repo.git(&["commit", "-q", "-m", "gitlink"]);
    let gitlink = repo.git(&["rev-parse", "HEAD"]);
    refuses(&repo.export(&gitlink));
    assert!(!repo.dest().exists());
}

#[test]
fn exact_prefix_and_sha256_commits_are_supported() {
    let repo = Repo::with_format("sha256");
    repo.write("nested/with space.lean", b"def nested := 7\n");
    fs::write(repo.root().join("root.txt"), "outside prefix").unwrap();
    fs::create_dir_all(repo.root().join("lean/trust_ir-semantics-other")).unwrap();
    fs::write(repo.root().join("lean/trust_ir-semantics-other/Wrong.lean"), "wrong prefix")
        .unwrap();
    let commit = repo.commit();
    assert_eq!(commit.len(), 64);
    succeeds(&repo.export(&commit));
    assert_eq!(fs::read(repo.dest().join("nested/with space.lean")).unwrap(), b"def nested := 7\n");
    assert!(!repo.dest().join("root.txt").exists());
    assert!(!repo.dest().join("Wrong.lean").exists());
}

#[test]
fn committed_build_caches_and_source_destinations_refuse() {
    let repo = Repo::new();
    let commit = repo.git(&["rev-parse", "HEAD"]);
    let inside = repo.root().join("snapshot");
    refuses(&repo.command(&commit, &inside).output().unwrap());
    assert!(!inside.exists());
    let missing_parent = repo.0.join("missing/out");
    refuses(&repo.command(&commit, &missing_parent).output().unwrap());
    assert!(!repo.0.join("missing").exists());
    repo.write(".lake/build/lib/cache.olean", b"committed build output");
    let cached = repo.commit();
    refuses(&repo.export(&cached));
    assert!(!repo.dest().exists());
}

#[test]
fn bare_stores_work_but_nonroot_paths_and_separate_metadata_destinations_refuse() {
    let repo = Repo::new();
    let commit = repo.git(&["rev-parse", "HEAD"]);
    let mirror = repo.0.join("bare-store");
    repo.git(&["clone", "-q", "--bare", "--no-hardlinks", ".", mirror.to_str().unwrap()]);
    let output = Command::new(env!("CARGO_BIN_EXE_bridge_closure"))
        .arg("--snapshot-lean")
        .arg(&mirror)
        .arg(&commit)
        .arg(repo.dest())
        .output()
        .unwrap();
    succeeds(&output);
    fs::remove_dir_all(repo.dest()).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_bridge_closure"))
        .arg("--snapshot-lean")
        .arg(repo.source())
        .arg(&commit)
        .arg(repo.dest())
        .output()
        .unwrap();
    refuses(&output);
    assert!(!repo.dest().exists());

    let metadata = repo.0.join("separate-metadata");
    fs::rename(repo.root().join(".git"), &metadata).unwrap();
    fs::write(repo.root().join(".git"), format!("gitdir: {}\n", metadata.display())).unwrap();
    let output = repo.command(&commit, &metadata.join("new-snapshot")).output().unwrap();
    refuses(&output);
    assert!(!metadata.join("new-snapshot").exists());
}

#[cfg(unix)]
#[test]
fn executable_mode_is_preserved_in_a_private_snapshot() {
    use std::os::unix::fs::PermissionsExt;
    let repo = Repo::new();
    repo.write("build-tool", b"#!/bin/sh\nexit 0\n");
    fs::set_permissions(repo.source().join("build-tool"), fs::Permissions::from_mode(0o755))
        .unwrap();
    let commit = repo.commit();
    succeeds(&repo.export(&commit));
    assert_eq!(
        fs::metadata(repo.dest().join("build-tool")).unwrap().permissions().mode() & 0o777,
        0o755
    );
    assert_eq!(fs::metadata(repo.dest()).unwrap().permissions().mode() & 0o777, 0o700);
}

#[cfg(unix)]
#[test]
fn symlink_sources_and_symlink_destinations_never_follow_external_paths() {
    use std::os::unix::fs::symlink;
    let repo = Repo::new();
    let commit = repo.git(&["rev-parse", "HEAD"]);
    let outside = repo.0.join("outside");
    fs::create_dir(&outside).unwrap();
    fs::write(outside.join("keep"), b"unchanged").unwrap();
    symlink(&outside, repo.dest()).unwrap();
    refuses(&repo.export(&commit));
    assert_eq!(fs::read(outside.join("keep")).unwrap(), b"unchanged");
    fs::remove_file(repo.dest()).unwrap();
    symlink(outside.join("keep"), repo.source().join("link")).unwrap();
    let linked = repo.commit();
    refuses(&repo.export(&linked));
    assert!(!repo.dest().exists());
    assert_eq!(fs::read(outside.join("keep")).unwrap(), b"unchanged");
}

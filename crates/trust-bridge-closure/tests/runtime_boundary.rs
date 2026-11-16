//! The crate-root runtime-boundary reader: what it reads, and everything it refuses.
//!
//! ORACLE-FREEZE-MAIN-1 (docs/DECISION_QUEUE.md, 2026-11-09). `src/lib.rs` and
//! `src/snapshot.rs` are blob-frozen (scripts/frozen-files.txt). 76ce622c11 moved both: lib.rs
//! re-exports one new function, `read_runtime_boundary_input`, which snapshot.rs adds beside
//! `export`. The waiver rows claim the move SAMPLES MORE and REFUSES MORE and admits nothing
//! new: the reader returns exactly the regular blob at `lean/trust_ir-semantics/
//! runtime-boundary.json` in the named commit's own tree (or `None` when that tree has no
//! entry there), through the same hardened `Git` wrapper `export` uses, and refuses every other
//! shape. These tests go through the CRATE ROOT, so they exercise lib.rs's re-export as well as
//! the reader; the two `#[test]`s inside snapshot.rs cover absence, worktree substitution, a
//! non-full revision, a missing object and a committed symlink, and are not repeated here.
//!
//! The independent review of that move found that a full-length hex string of the OTHER object
//! format passed `object_id` and was then resolved by Git as a REF NAME (or a unique prefix), in
//! the reader and, from the pin on, in `export`: bytes chosen by a mutable ref. Both now require
//! the string to name itself (`names_itself`); `an_id_git_resolves_by_name_refuses_in_both_readers`
//! is that regression.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use trust_bridge_closure::{
    BRIDGE_ROOT_MODULE, BRIDGE_ROOT_MODULES, export_snapshot, read_runtime_boundary_input,
};

static NEXT: AtomicUsize = AtomicUsize::new(0);
const LEDGER: &str = "lean/trust_ir-semantics/runtime-boundary.json";

struct Repo(PathBuf);

impl Repo {
    fn new() -> Self {
        Self::with_format("sha1")
    }

    fn with_format(format: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "bridge-runtime-boundary-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        fs::write(path.join("empty-config"), "").unwrap();
        fs::create_dir(path.join("repo")).unwrap();
        let repo = Self(path);
        repo.git(&["init", "-q", "-b", "main", &format!("--object-format={format}")]);
        repo.write("lean/trust_ir-semantics/lean-toolchain", b"leanprover/lean4:v4.8.0\n");
        repo
    }

    fn root(&self) -> PathBuf {
        self.0.join("repo")
    }

    fn write(&self, path: &str, bytes: &[u8]) {
        let path = self.root().join(path);
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
            .env("GIT_AUTHOR_NAME", "runtime boundary fixture")
            .env("GIT_AUTHOR_EMAIL", "fixture@example.invalid")
            .env("GIT_COMMITTER_NAME", "runtime boundary fixture")
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
        self.git(&["commit", "-q", "--allow-empty", "-m", "fixture"]);
        self.git(&["rev-parse", "HEAD"])
    }

    fn read(&self, commit: &str) -> std::io::Result<Option<Vec<u8>>> {
        read_runtime_boundary_input(&self.root(), commit)
    }
}

impl Drop for Repo {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

#[test]
fn crate_root_exports_the_snapshot_pair_and_the_unchanged_bridge_roots() {
    // The re-export population lib.rs gained is exactly the reader; `export_snapshot` keeps
    // its signature, and the root-module selector is byte-for-byte the pinned one.
    let _: fn(&Path, &str, &Path) -> std::io::Result<usize> = export_snapshot;
    let _: fn(&Path, &str) -> std::io::Result<Option<Vec<u8>>> = read_runtime_boundary_input;
    assert_eq!(BRIDGE_ROOT_MODULE, "TrustIr.Semantics.Compare");
    assert_eq!(
        BRIDGE_ROOT_MODULES,
        [
            "TrustIr.Semantics.Compare",
            "TrustIr.Semantics.Cast",
            "TrustIr.Semantics.Step",
            "TrustIr.Semantics.Eval",
            "TrustIr.Proofs.ByteMemory",
        ]
    );
}

#[test]
fn reads_the_committed_blob_not_the_index_and_ignores_replacement_refs() {
    let repo = Repo::new();
    repo.write(LEDGER, b"committed ledger\n");
    let original = repo.commit();
    let old_blob = repo.git(&["rev-parse", &format!("HEAD:{LEDGER}")]);
    // A later commit, a replacement ref aimed at it and a staged-but-uncommitted edit: none of
    // them may change what the ORIGINAL commit's entry reads as.
    repo.write(LEDGER, b"replacement ledger\n");
    let replacement = repo.commit();
    let new_blob = repo.git(&["rev-parse", &format!("HEAD:{LEDGER}")]);
    repo.git(&["replace", &old_blob, &new_blob]);
    repo.git(&["replace", &original, &replacement]);
    repo.write(LEDGER, b"staged substitution\n");
    repo.git(&["add", "-A"]);
    assert_eq!(repo.read(&original).unwrap(), Some(b"committed ledger\n".to_vec()));
}

#[test]
fn an_executable_regular_blob_and_a_sha256_commit_are_read_exactly() {
    // Positive controls: the reader is not vacuous on the two regular modes `export` also
    // accepts, nor on a SHA-256 object format.
    let repo = Repo::new();
    repo.write(LEDGER, b"\0binary\r\nledger\xff");
    repo.git(&["add", "-A"]);
    repo.git(&["update-index", "--chmod=+x", LEDGER]);
    let commit = repo.commit();
    assert_eq!(repo.read(&commit).unwrap(), Some(b"\0binary\r\nledger\xff".to_vec()));

    let sha256 = Repo::with_format("sha256");
    sha256.write(LEDGER, b"sha256 ledger\n");
    let commit = sha256.commit();
    assert_eq!(commit.len(), 64);
    assert_eq!(sha256.read(&commit).unwrap(), Some(b"sha256 ledger\n".to_vec()));
}

#[test]
fn a_tree_or_a_gitlink_at_the_ledger_path_refuses() {
    let tree = Repo::new();
    tree.write(&format!("{LEDGER}/inner.json"), b"nested\n");
    let commit = tree.commit();
    assert!(tree.read(&commit).is_err(), "a directory named like the ledger is not the ledger");

    let gitlink = Repo::new();
    let target = gitlink.commit();
    gitlink.git(&["update-index", "--add", "--cacheinfo", &format!("160000,{target},{LEDGER}")]);
    gitlink.git(&["commit", "-q", "-m", "gitlink"]);
    let commit = gitlink.git(&["rev-parse", "HEAD"]);
    assert!(gitlink.read(&commit).is_err(), "a gitlink at the ledger path is not a blob");
}

#[test]
fn only_a_full_lowercase_commit_id_is_a_revision() {
    let repo = Repo::new();
    repo.write(LEDGER, b"ledger\n");
    let commit = repo.commit();
    let tree = repo.git(&["rev-parse", "HEAD^{tree}"]);
    let blob = repo.git(&["rev-parse", &format!("HEAD:{LEDGER}")]);
    repo.git(&["tag", "-a", "-m", "annotated", "v1"]);
    let tag = repo.git(&["rev-parse", "v1"]);
    assert!(repo.read(&commit).unwrap().is_some(), "control: the full commit id reads");
    for refused in [
        commit.to_uppercase(),
        commit[..12].to_owned(),
        format!("{commit}^{{tree}}"),
        "main".to_owned(),
        tree,
        blob,
        tag,
    ] {
        assert!(repo.read(&refused).is_err(), "{refused} must not select a revision");
    }
}

#[test]
fn an_id_git_resolves_by_name_refuses_in_both_readers() {
    // SHA-1 repository: a 64-hex string is not an object ID there, so Git looks it up as a ref.
    let repo = Repo::new();
    repo.write(LEDGER, b"pinned ledger\n");
    let pinned = repo.commit();
    repo.write(LEDGER, b"ref-selected ledger\n");
    let moved = repo.commit();
    let by_name = "f".repeat(64);
    repo.git(&["update-ref", &format!("refs/heads/{by_name}"), &moved]);
    // Control: the attack is live — Git really resolves the name to a commit.
    assert_eq!(repo.git(&["rev-parse", &format!("{by_name}^{{commit}}")]), moved);
    assert!(repo.read(&by_name).is_err(), "a 64-hex ref name must not select a SHA-1 revision");
    let dest = repo.0.join("export-by-name");
    assert!(export_snapshot(&repo.root(), &by_name, &dest).is_err());
    assert!(!dest.exists(), "a refused export creates no destination");
    let dest = repo.0.join("export-exact");
    assert!(export_snapshot(&repo.root(), &moved, &dest).is_ok(), "control: the exact id exports");
    // No over-refusal: an EXACT id keeps reading its own commit even when refs of the same name
    // point elsewhere (Git warns that the name is ambiguous and uses the object).
    for namespace in ["refs/heads", "refs/tags"] {
        repo.git(&["update-ref", &format!("{namespace}/{pinned}"), &moved]);
    }
    assert_eq!(repo.read(&pinned).unwrap(), Some(b"pinned ledger\n".to_vec()));
    let dest = repo.0.join("export-shadowed");
    assert!(export_snapshot(&repo.root(), &pinned, &dest).is_ok());
    assert_eq!(fs::read(dest.join("runtime-boundary.json")).unwrap(), b"pinned ledger\n");

    // SHA-256 repository: a 40-hex string is a unique PREFIX of the commit to Git.
    let sha256 = Repo::with_format("sha256");
    sha256.write(LEDGER, b"sha256 ledger\n");
    let commit = sha256.commit();
    let prefix = &commit[..40];
    assert_eq!(sha256.git(&["rev-parse", &format!("{prefix}^{{commit}}")]), commit);
    assert!(sha256.read(prefix).is_err(), "a 40-hex prefix must not select a SHA-256 revision");
    let dest = sha256.0.join("export-prefix");
    assert!(export_snapshot(&sha256.root(), prefix, &dest).is_err());
    assert!(!dest.exists());
    // And a 40-hex TAG name there, which Git also resolves by name.
    let tag_name = "e".repeat(40);
    sha256.git(&["update-ref", &format!("refs/tags/{tag_name}"), &commit]);
    assert_eq!(sha256.git(&["rev-parse", &format!("{tag_name}^{{commit}}")]), commit);
    assert!(sha256.read(&tag_name).is_err(), "a 40-hex tag name must not select a revision");
    assert!(sha256.read(&commit).unwrap().is_some(), "control: the exact id reads");
}

const CHILD_ROOT: &str = "TRUST_RUNTIME_BOUNDARY_CHILD_ROOT";
const CHILD_COMMIT: &str = "TRUST_RUNTIME_BOUNDARY_CHILD_COMMIT";
const CHILD_MARKER: &str = "runtime-boundary child read the local ledger";

#[test]
fn inherited_git_environment_does_not_redirect_the_reader() {
    // The child half: this same test, re-run in a process whose environment names a FOREIGN
    // repository, object store, index and work tree. The reader must still read the local one.
    if let Some(root) = std::env::var_os(CHILD_ROOT) {
        let commit = std::env::var(CHILD_COMMIT).unwrap();
        let bytes = read_runtime_boundary_input(Path::new(&root), &commit).unwrap();
        assert_eq!(bytes, Some(b"local ledger\n".to_vec()));
        println!("{CHILD_MARKER}");
        return;
    }
    let repo = Repo::new();
    repo.write(LEDGER, b"local ledger\n");
    let commit = repo.commit();
    let foreign = Repo::new();
    foreign.write(LEDGER, b"foreign ledger\n");
    foreign.commit();
    let output = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "inherited_git_environment_does_not_redirect_the_reader"])
        .args(["--nocapture", "--test-threads=1"])
        .env(CHILD_ROOT, repo.root())
        .env(CHILD_COMMIT, &commit)
        .env("GIT_DIR", foreign.root().join(".git"))
        .env("GIT_COMMON_DIR", foreign.root().join(".git"))
        .env("GIT_WORK_TREE", foreign.root())
        .env("GIT_INDEX_FILE", foreign.root().join(".git/index"))
        .env("GIT_OBJECT_DIRECTORY", foreign.root().join(".git/objects"))
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(output.status.success(), "{stdout}{}", String::from_utf8_lossy(&output.stderr));
    // Positive control: the child ran the read (a filter matching no test would also exit 0).
    assert!(stdout.contains(CHILD_MARKER), "the child did not run the read:\n{stdout}");
}

#[test]
fn a_path_below_the_worktree_root_refuses() {
    let repo = Repo::new();
    repo.write(LEDGER, b"ledger\n");
    let commit = repo.commit();
    let below = repo.root().join("lean");
    assert!(read_runtime_boundary_input(&below, &commit).is_err());
}

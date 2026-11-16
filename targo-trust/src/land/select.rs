//! Which rows a change selects, and what the change is.
//!
//! Selection is `land_select.validation_test_modules`, row id for module: the
//! rows whose `selects_on` names a changed path, the rows of the table's
//! reader when the table itself changed, and one row for any changed
//! `Cargo.toml`. `targo-trust/tests/fixtures/land_select_cases.json` holds this
//! and the Python selector to the same answers.

use std::collections::BTreeSet;
use std::path::Path;
use std::time::Duration;

use super::table::{READER, TABLE, Table};
use crate::controlled_git;

/// The row a changed `Cargo.toml` selects, whatever its directory or letter
/// case: a manifest moves the feature graph that row resolves.
pub(crate) const MANIFEST_ROW: &str = "validation.mir_test_oracle_feature_test";

const GIT_TIMEOUT: Duration = Duration::from_secs(300);
/// A name is at most a few hundred bytes; this is room for a commit id's line.
const MAX_REV_BYTES: usize = 64 * 1024;
/// `ls-files -z` over this repository is about 27 MiB (`controlled_git`).
const MAX_LISTING_BYTES: usize = 128 * 1024 * 1024;

/// The ids of the rows a change to `changed` selects, sorted. An id is
/// selected whether or not the table has its row: the selector names
/// [`MANIFEST_ROW`] for a changed manifest without looking for it, as the
/// Python selector does, and a selected id with no row is not judged.
pub(crate) fn selected(table: &Table, changed: &[String]) -> BTreeSet<String> {
    let mut ids = BTreeSet::new();
    for path in changed {
        // A validation program reports the rows it lists; the table reports
        // its reader's. Both are the rows whose selects_on names the program.
        let program = if path == TABLE { READER } else { path.as_str() };
        if let Some(listed) = table.programs.get(program) {
            ids.extend(listed.iter().cloned());
        }
        // Every other selecting path is a subject.
        if !table.programs.contains_key(path) {
            ids.extend(table.selected_by(path).map(str::to_owned));
        }
    }
    if changed.iter().any(|path| names_a_manifest(path)) {
        ids.insert(MANIFEST_ROW.to_owned());
    }
    ids
}

/// Whether `path`'s last component is `Cargo.toml` as the landing host's file
/// system compares names. The Python selector folds the path (NFD, then
/// `str.casefold`) and compares the result with `cargo.toml`. No character
/// outside ASCII folds to a letter of that name or to its dot, so the fold
/// accepts exactly its ASCII spellings in either case
/// (`scripts/tests/land_gate_test.py` checks every code point).
pub(crate) fn names_a_manifest(path: &str) -> bool {
    path.rsplit('/').next().is_some_and(|name| name.eq_ignore_ascii_case("cargo.toml"))
}

/// What changed between a base and the checkout as it stands.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Change {
    /// The base's commit.
    pub(crate) base: String,
    /// The merge base of that commit and `HEAD`.
    pub(crate) merge_base: String,
    pub(crate) head: String,
    /// Paths that differ between the merge base and `HEAD`.
    pub(crate) committed: BTreeSet<String>,
    /// Paths staged, changed in the working tree, or untracked.
    pub(crate) working: BTreeSet<String>,
}

impl Change {
    /// Every changed path, once, sorted.
    pub(crate) fn paths(&self) -> Vec<String> {
        self.committed.union(&self.working).cloned().collect()
    }
}

/// What the verb asks of the checkout. The verb's is [`GitCheckout`]; its
/// tests stand in one that answers from memory (`land/tests.rs`).
pub(crate) trait Checkout {
    /// Every tracked path.
    fn tracked(&mut self, root: &Path) -> Result<BTreeSet<String>, String>;
    /// The change from `base` to the checkout as it stands. An `Err` is a
    /// change that could not be read, never an empty one.
    fn change(&mut self, root: &Path, base: &str) -> Result<Change, String>;
}

/// The checkout through `controlled_git`: the fixed system git, a closed
/// environment, and no configuration but the repository's own.
pub(crate) struct GitCheckout;

impl Checkout for GitCheckout {
    fn tracked(&mut self, root: &Path) -> Result<BTreeSet<String>, String> {
        listing(root, &["ls-files", "-z"], "git ls-files")
    }

    fn change(&mut self, root: &Path, base: &str) -> Result<Change, String> {
        let commit = |rev: &str, what: &str| {
            let spelled = format!("{rev}^{{commit}}");
            controlled_git::text(
                root,
                &["rev-parse", "--verify", "--quiet", "--end-of-options", &spelled],
                what,
                MAX_REV_BYTES,
                GIT_TIMEOUT,
            )
        };
        let head = commit("HEAD", "git rev-parse HEAD")
            .map_err(|error| format!("HEAD does not resolve to a commit ({error})"))?;
        let base_commit = commit(base, "git rev-parse of the base").map_err(|error| {
            format!(
                "the base {base:?} does not resolve to a commit ({error}); nothing was compared \
                 (fetch it, or name another with --base)"
            )
        })?;
        let merge_base = controlled_git::text(
            root,
            &["merge-base", &base_commit, &head],
            "git merge-base",
            MAX_REV_BYTES,
            GIT_TIMEOUT,
        )
        .map_err(|error| {
            format!("the base {base:?} ({base_commit}) and HEAD have no merge base ({error})")
        })?;
        // Git compares no such path with the working tree, so the diffs below
        // would leave a change to one out and the change would read smaller
        // than it is. (`controlled_git::validate_status_authority` refuses
        // these entries too, and with them every checkout that has a local
        // exclude file, as this repository's own have: the listing of
        // untracked files below is not held to that.)
        let hidden = hidden_paths(&listing(root, &INDEX_MARKS, "git ls-files of the index")?)?;
        if let Some(first) = hidden.first() {
            return Err(format!(
                "{} index entr{} marked assume-unchanged or skip-worktree ({first}{}): git \
                 reports no change to such a path, so the change cannot be read; clear the mark \
                 (git update-index --no-assume-unchanged --no-skip-worktree -- <path>) and run \
                 again",
                hidden.len(),
                if hidden.len() == 1 { "y is" } else { "ies are" },
                if hidden.len() == 1 { "" } else { ", ..." }
            ));
        }
        // As land_select.changed_paths asks: no rename pairing, so a move is
        // both of its paths, and a moved gitlink is a path whatever
        // diff.ignoreSubmodules says.
        const DIFF: [&str; 7] = [
            "-c",
            "diff.renames=false",
            "diff",
            "--no-renames",
            "--ignore-submodules=none",
            "--name-only",
            "-z",
        ];
        let diff = |rest: &[&str], what: &str| {
            let args: Vec<&str> = DIFF.iter().copied().chain(rest.iter().copied()).collect();
            listing(root, &args, what)
        };
        let committed = diff(&[&merge_base, &head], "git diff of the merge base and HEAD")?;
        let mut working = diff(&["--cached", &head], "git diff of HEAD and the index")?;
        working.extend(diff(&[], "git diff of the index and the working tree")?);
        working.extend(listing(
            root,
            &["ls-files", "-z", "--others", "--exclude-standard"],
            "git ls-files of untracked files",
        )?);
        Ok(Change { base: base_commit, merge_base, head, committed, working })
    }
}

/// `git ls-files -v`: every index entry as its one-letter tag, a space and
/// its path.
const INDEX_MARKS: [&str; 3] = ["ls-files", "-v", "-z"];

/// The paths, of `git ls-files -v`'s entries, that git does not compare with
/// the working tree: a lower-case tag is an entry marked assume-unchanged, and
/// `S` one marked skip-worktree (`s` is both). An entry that is not a tag, a
/// space and a path is an error, never a visible path. Sorted by path.
pub(crate) fn hidden_paths(entries: &BTreeSet<String>) -> Result<Vec<String>, String> {
    let mut hidden = Vec::new();
    for entry in entries {
        let mut characters = entry.chars();
        let (Some(tag), Some(' ')) = (characters.next(), characters.next()) else {
            return Err(format!("git ls-files -v printed an entry that has no tag: {entry:?}"));
        };
        if tag.is_ascii_lowercase() || tag == 'S' {
            hidden.push(characters.as_str().to_owned());
        }
    }
    hidden.sort();
    Ok(hidden)
}

/// The NUL-separated entries a git command prints. A command that fails, or
/// that says anything on stderr, listed nothing that can be relied on.
fn listing(root: &Path, args: &[&str], what: &str) -> Result<BTreeSet<String>, String> {
    let output = controlled_git::output(root, args, what, MAX_LISTING_BYTES, GIT_TIMEOUT)?;
    let said = String::from_utf8_lossy(&output.stderr);
    if !output.status.success() {
        return Err(format!("{what} exited {}: {}", output.status, said.trim()));
    }
    if !said.trim().is_empty() {
        return Err(format!("{what} wrote to stderr: {}", said.trim()));
    }
    // A path that is not UTF-8 is decoded with U+FFFD for each bad sequence,
    // and its last component is `Cargo.toml` decoded or not. Such a path can
    // then equal a selects_on path that itself holds U+FFFD, which the Python
    // selector does not match: the verb selects that row and the selector does
    // not. Never fewer rows, and no row of the table names such a path.
    Ok(output
        .stdout
        .split(|byte| *byte == 0)
        .filter(|name| !name.is_empty())
        .map(|name| String::from_utf8_lossy(name).into_owned())
        .collect())
}

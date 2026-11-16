//! Trust: what a git range changed, for a test plan's selection.
//!
//! `targo test --plan <FILE> --changed-range <RANGE>` asks git itself which
//! paths a range changes, so the caller of a plan needs no script that runs
//! `git diff` and hands the list over. Each range is diffed exactly as
//! `git diff <RANGE>` reads it: `A..B` is the tree of `A` against the tree of
//! `B`, and `A...B` is what `B` changed since its merge base with `A`.
//!
//! The diff is spelled so that no configuration can hide a path:
//!
//! * `--no-renames` (and `diff.renames=false`): with rename detection a file
//!   moved out of a member's directory is listed only under its new path, so
//!   the member it left would not be selected. Without it the old path is a
//!   deletion and still selects its member.
//! * `-z`: without it git quotes a path that holds a special byte, and the
//!   quoted text lies under no member's directory.
//! * `--ignore-submodules=none`: a moved gitlink is a changed path whatever
//!   `diff.ignoreSubmodules` or a `.gitmodules` `ignore` says.
//! * `--relative`: paths are written from the workspace root, as a plan's
//!   changed paths are, and a path outside it is left out: no plan path can
//!   name it.
//!
//! A range git cannot diff (an object this clone lacks, no merge base, an
//! unknown name) is an error and never an empty change.

use std::collections::BTreeSet;
use std::path::Path;

use anyhow::Context as _;
use cargo_util::ProcessBuilder;

use crate::util::CargoResult;

/// How every range is diffed; the range and a closing `--` follow.
const DIFF: [&str; 8] = [
    "-c",
    "diff.renames=false",
    "diff",
    "--no-renames",
    "--ignore-submodules=none",
    "--name-only",
    "-z",
    "--relative",
];

/// Checks the spelling of one `--changed-range` value: two revisions joined
/// by `..` or `...`, neither empty, and nothing git would read as an option.
pub fn check_range(range: &str) -> CargoResult<()> {
    let (base, head) = range
        .split_once("...")
        .or_else(|| range.split_once(".."))
        .ok_or_else(|| {
            anyhow::anyhow!(
                "--changed-range `{range}` is not a range: write `<rev>..<rev>` (the two \
                 trees) or `<rev>...<rev>` (the changes since the merge base)"
            )
        })?;
    anyhow::ensure!(
        !base.is_empty() && !head.is_empty(),
        "--changed-range `{range}` leaves a side out: name both revisions"
    );
    for side in [base, head] {
        anyhow::ensure!(
            !side.starts_with(['-', '.'])
                && !side.ends_with('.')
                && !side.contains("..")
                && !side.contains(char::is_whitespace),
            "--changed-range `{range}`: `{side}` is not a revision"
        );
    }
    Ok(())
}

/// The union of the paths the ranges change, sorted, each written from
/// `root` with `/`.
pub fn range_paths(root: &Path, ranges: &[String]) -> CargoResult<Vec<String>> {
    let mut paths = BTreeSet::new();
    for range in ranges {
        check_range(range)?;
        let mut git = ProcessBuilder::new("git");
        git.cwd(root).args(&DIFF).arg(range).arg("--");
        let output = git.exec_with_output().with_context(|| {
            format!(
                "--changed-range `{range}`: git could not diff the range, so nothing says \
                 what changed (an unfetched commit, no merge base, or an unknown name)"
            )
        })?;
        for path in output.stdout.split(|byte| *byte == 0) {
            if path.is_empty() {
                continue;
            }
            let path = std::str::from_utf8(path).map_err(|_| {
                anyhow::anyhow!(
                    "--changed-range `{range}`: git names a changed path that is not UTF-8 \
                     (`{}`), which no plan path can match",
                    String::from_utf8_lossy(path)
                )
            })?;
            paths.insert(path.to_owned());
        }
    }
    Ok(paths.into_iter().collect())
}

/// The ranges a push changes, from the lines git hands a `pre-push` hook on
/// standard input: `<local ref> <local sha> <remote ref> <remote sha>`.
///
/// An update is the remote tree against the pushed tree (`remote..local`),
/// so a push that drops commits is judged on what it removes too. A new
/// branch has no remote tree and is what it adds since `base`
/// (`base...local`). A deletion pushes no tree. Lines of another shape are
/// refused: a hook that passed something else would select nothing.
///
/// Input that names no pushed tree at all (no line, or deletions only) is
/// judged as the standing change, `base...HEAD`, and never as a change of
/// nothing: a hook that lost its standard input must not read as a push
/// that changes nothing, which exits 0. The script lane fell back the same
/// way (`resolve_ranges`).
pub fn pushed_ranges(text: &str, base: &str) -> CargoResult<Vec<String>> {
    let zero = |sha: &str| sha.bytes().all(|byte| byte == b'0');
    let mut ranges = Vec::new();
    for line in text.lines().filter(|line| !line.trim().is_empty()) {
        let fields = line.split_whitespace().collect::<Vec<_>>();
        let [_, local, _, remote] = fields[..] else {
            anyhow::bail!(
                "--changed-pushed-refs: `{line}` is not `<local ref> <local sha> <remote ref> \
                 <remote sha>`, the line git gives a pre-push hook"
            );
        };
        if zero(local) {
            continue;
        }
        ranges.push(if zero(remote) {
            format!("{base}...{local}")
        } else {
            format!("{remote}..{local}")
        });
    }
    if ranges.is_empty() {
        ranges.push(format!("{base}...HEAD"));
    }
    for range in &ranges {
        check_range(range)?;
    }
    Ok(ranges)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_range_names_two_revisions_and_no_option() {
        for good in [
            "a..b",
            "origin/main...HEAD",
            "HEAD~3..HEAD",
            "v1^{tree}..v2",
        ] {
            check_range(good).unwrap();
        }
        for bad in [
            "a",
            "..b",
            "a..",
            "a....b",
            "-x..b",
            "a..--output=x",
            "a b..c",
            "...",
        ] {
            assert!(check_range(bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn a_push_is_each_update_and_each_new_branch_and_no_deletion() {
        let zero = "0".repeat(40);
        let text = format!(
            "refs/heads/a 1111 refs/heads/a 2222\n\
             refs/heads/new 3333 refs/heads/new {zero}\n\
             (delete) {zero} refs/heads/gone 4444\n\n"
        );
        assert_eq!(
            pushed_ranges(&text, "origin/main").unwrap(),
            ["2222..1111", "origin/main...3333"]
        );
        // No pushed tree is the standing change, never a change of nothing:
        // no line at all (a hook that lost its input), or deletions only.
        assert_eq!(
            pushed_ranges("", "origin/main").unwrap(),
            ["origin/main...HEAD"]
        );
        assert_eq!(
            pushed_ranges(
                &format!("(delete) {zero} refs/heads/gone 4444\n"),
                "origin/main"
            )
            .unwrap(),
            ["origin/main...HEAD"]
        );
        assert!(pushed_ranges("refs/heads/a 1111 refs/heads/a", "origin/main").is_err());
    }
}

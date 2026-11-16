//! Trust: a test plan's `[expect] known-red` file: the tests a plan run
//! expects to fail.
//!
//! The file is a ratchet, not a mask. Each row is one test, keyed
//! `<test binary>::<test path>`: the test target's crate name (its
//! executable's file name without Cargo's hash) and the name libtest prints.
//! A `#` starts a comment; a comment containing `[flaky]` marks a row whose
//! test may pass or fail.
//!
//! A key names its binary by crate name alone, so a row whose binary name
//! two test targets of the plan's workspace carry (two packages with a
//! `tests/it.rs`, or a lib and an integration test of its name) would excuse
//! the same-named test of each. Such a row is refused when the plan is
//! loaded (`KnownRed::require_one_binary`), on every route.
//!
//! * A harness that failed only in tests the file lists is excused: its
//!   action is still recorded `failed`, and it does not fail the run.
//! * A failure the file does not list is a new failure and fails the run.
//! * A listed test that passed is a stale row and fails the run until the
//!   row is deleted, unless the row is `[flaky]`.
//!
//! Only a failure libtest itself reported is excused: the harness exited
//! with a code, closed the run it announced with `test result: FAILED.`, and
//! printed as many `test <name> ... FAILED` and `... ok` lines as that line
//! counts (`plan_judge::Reading`). A crash, a signal, a harness that exited 0
//! and was judged failed, and a target with `harness = false` name no failed
//! test, so nothing excuses them.
//!
//! A row is judged only by result lines that are read. Where a binary has
//! rows and its harness's lines are not read, the result says so
//! (`unjudged`): for a failed harness that is why no row excused it, and for
//! a harness that passed it is an unmet requirement, since a listed test
//! that passed there would be a stale row nobody saw.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Component, Path};

use anyhow::Context as _;
use serde::Serialize;

use super::plan_judge::Ran;
use crate::util::CargoResult;

/// The rows of a known-red file.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct KnownRed {
    /// The file as the plan names it, relative to the workspace root.
    pub file: String,
    /// SHA-256 of the file's bytes, in hex.
    pub sha256: String,
    /// Each key with whether its row is `[flaky]`.
    rows: BTreeMap<String, bool>,
}

/// What the known-red file says of one failed action.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Failure {
    /// The failed tests the file lists.
    pub known: Vec<String>,
    /// The failed tests it does not list.
    pub new: Vec<String>,
    /// The action failed only in tests the file lists.
    pub excused: bool,
}

/// A test binary with rows whose harness's result lines were not read.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub(crate) struct Unjudged {
    pub package: String,
    pub binary: String,
    /// The harness failed: its rows excused nothing. Otherwise it passed,
    /// and its rows were not checked for staleness.
    pub failed: bool,
    pub why: String,
}

impl Unjudged {
    /// The unmet requirement, for a harness that passed.
    pub(crate) fn unmet(&self, file: &str) -> String {
        format!(
            "known-red rows of test binary `{}` (package `{}`) in `{file}` could not be \
             judged, so a listed test that passed would go unseen: {}",
            self.binary, self.package, self.why
        )
    }
}

/// The known-red part of a plan's verdict.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize)]
pub(crate) struct KnownRedResult {
    pub file: String,
    pub sha256: String,
    /// Listed tests that failed in a harness the file excused: one that
    /// failed only in listed tests.
    pub excused: Vec<String>,
    /// Listed tests that failed in a harness the file did not excuse,
    /// because a test it does not list failed there too.
    pub not_excused: Vec<String>,
    /// Failed tests it does not list.
    pub new_failures: Vec<String>,
    /// Rows, not `[flaky]`, whose test passed.
    pub stale: Vec<String>,
    /// Binaries with rows whose result lines were not read.
    pub unjudged: Vec<Unjudged>,
}

impl KnownRed {
    /// Reads the file `file` names under the workspace root. A plan that
    /// names a file which is not there has lost its ratchet, so that is an
    /// error and not an empty list.
    pub(super) fn load(root: &Path, file: &str) -> CargoResult<KnownRed> {
        let relative = Path::new(file);
        anyhow::ensure!(
            !file.is_empty()
                && relative
                    .components()
                    .all(|component| matches!(component, Component::Normal(_))),
            "`[expect] known-red = \"{file}\"` is not a path under the workspace root (no \
             leading `/`, no `.` or `..` component)"
        );
        let path = root.join(relative);
        let unreadable = || {
            format!(
                "failed to read `[expect] known-red` file `{}`",
                path.display()
            )
        };
        // The check above is of the path as written. A symlink on the way
        // can still lead out of the workspace.
        let real = path.canonicalize().with_context(unreadable)?;
        let real_root = root.canonicalize().with_context(unreadable)?;
        anyhow::ensure!(
            real.starts_with(&real_root),
            "`[expect] known-red = \"{file}\"` resolves to `{}`, which is not under the \
             workspace root",
            real.display()
        );
        let text = std::fs::read_to_string(&path).with_context(unreadable)?;
        let mut known = Self::parse(&text)
            .with_context(|| format!("invalid `[expect] known-red` file `{}`", path.display()))?;
        known.file = file.to_owned();
        known.sha256 = cargo_util::Sha256::new()
            .update(text.as_bytes())
            .finish_hex();
        Ok(known)
    }

    /// Parses the rows. A row that could never match a test, or a key
    /// written twice, is a row its author believes is in force.
    pub(crate) fn parse(text: &str) -> CargoResult<KnownRed> {
        let mut rows = BTreeMap::new();
        // A byte-order mark is no part of the first row or its comment.
        let text = text.strip_prefix('\u{feff}').unwrap_or(text);
        for (index, raw) in text.lines().enumerate() {
            let (body, comment) = raw.split_once('#').unwrap_or((raw, ""));
            let key = body.trim();
            if key.is_empty() {
                continue;
            }
            let line = index + 1;
            anyhow::ensure!(
                !key.contains(char::is_whitespace)
                    && key
                        .split_once("::")
                        .is_some_and(|(binary, test)| !binary.is_empty() && !test.is_empty()),
                "line {line}: `{key}` is not `<test binary>::<test path>`"
            );
            anyhow::ensure!(
                rows.insert(key.to_owned(), comment.contains("[flaky]"))
                    .is_none(),
                "line {line}: `{key}` is listed twice"
            );
        }
        Ok(KnownRed {
            rows,
            ..KnownRed::default()
        })
    }

    /// Refuses a row whose binary name more than one test target carries.
    /// `carriers` maps a crate name to the targets of that name which a run
    /// of the plan may test.
    pub(super) fn require_one_binary(
        &self,
        carriers: &BTreeMap<String, Vec<String>>,
    ) -> CargoResult<()> {
        for key in self.rows.keys() {
            let binary = key
                .split_once("::")
                .map_or(key.as_str(), |(binary, _)| binary);
            let Some(targets) = carriers.get(binary).filter(|targets| targets.len() > 1) else {
                continue;
            };
            anyhow::bail!(
                "`[expect] known-red` file `{}`: row `{key}` names the test binary `{binary}`, \
                 and {} test targets have that crate name: {}. The row would excuse the test \
                 in each of them; a known-red row needs a test binary name that one target \
                 carries",
                self.file,
                targets.len(),
                targets.join(", ")
            );
        }
        Ok(())
    }

    /// Why the result lines of `ran`, a binary with rows, were not read;
    /// `None` when they were, or when the binary has no row.
    fn unjudged(&self, ran: &Ran) -> Option<Unjudged> {
        self.tests_of(&ran.binary).next()?;
        let why = match &ran.observed {
            None => "its harness was not watched".to_owned(),
            Some(observed) if ran.failed => {
                if observed.failed.is_some() {
                    return None;
                }
                observed.unreported.clone().unwrap_or_else(|| {
                    "the harness failed without libtest reporting a failed test".to_owned()
                })
            }
            Some(observed) => observed.void.clone()?,
        };
        Some(Unjudged {
            package: ran.package.clone(),
            binary: ran.binary.clone(),
            failed: ran.failed,
            why,
        })
    }

    /// The test binaries the rows name.
    #[cfg(test)]
    pub(crate) fn binaries(&self) -> BTreeSet<&str> {
        self.rows
            .keys()
            .map(|key| {
                key.split_once("::")
                    .map_or(key.as_str(), |(binary, _)| binary)
            })
            .collect()
    }

    /// The names of the listed tests of the test binary `binary`: the tests
    /// whose result lines its harness is watched for.
    pub(crate) fn tests_of(&self, binary: &str) -> impl Iterator<Item = &str> {
        self.rows.keys().filter_map(move |key| {
            key.strip_prefix(binary)
                .and_then(|rest| rest.strip_prefix("::"))
        })
    }

    /// What the file says of the failed action `ran`.
    pub(crate) fn judge(&self, ran: &Ran) -> Failure {
        let Some(failed) = ran
            .observed
            .as_ref()
            .and_then(|observed| observed.failed.as_ref())
            .filter(|_| ran.failed)
        else {
            // Not a failure libtest reported test by test.
            return Failure::default();
        };
        let (known, new): (Vec<String>, Vec<String>) = failed
            .iter()
            .map(|name| format!("{}::{name}", ran.binary))
            .partition(|key| self.rows.contains_key(key));
        Failure {
            excused: !known.is_empty() && new.is_empty(),
            known,
            new,
        }
    }

    /// The file's verdict on a run's finished actions.
    pub(crate) fn result(&self, ran: &[Ran]) -> KnownRedResult {
        let mut excused = BTreeSet::new();
        let mut not_excused = BTreeSet::new();
        let mut unjudged = BTreeSet::new();
        let mut new_failures = BTreeSet::new();
        let mut stale = BTreeSet::new();
        for ran in ran {
            let failure = self.judge(ran);
            if failure.excused {
                excused.extend(failure.known);
            } else {
                not_excused.extend(failure.known);
            }
            unjudged.extend(self.unjudged(ran));
            new_failures.extend(failure.new);
            // A listed test that printed `ok`, in a failed harness or a
            // passing one. `passed` holds only watched names, and this
            // binary's watch may also hold an instrument's `require-pass`.
            let passed = ran.observed.iter().flat_map(|observed| &observed.passed);
            stale.extend(
                passed
                    .map(|name| format!("{}::{name}", ran.binary))
                    .filter(|key| self.rows.get(key) == Some(&false)),
            );
        }
        KnownRedResult {
            file: self.file.clone(),
            sha256: self.sha256.clone(),
            excused: excused.into_iter().collect(),
            not_excused: not_excused.into_iter().collect(),
            unjudged: unjudged.into_iter().collect(),
            new_failures: new_failures.into_iter().collect(),
            stale: stale.into_iter().collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ops::cargo_test::plan_judge::Observed;

    const FILE: &str = "\
# a comment, then a blank line

host::m::red  # why it is red
host::m::shaky   # under load [flaky]
other::m::red
";

    fn known() -> KnownRed {
        KnownRed::parse(FILE).unwrap()
    }

    fn ran(binary: &str, failed: Option<&[&str]>, passed: &[&str]) -> Ran {
        let names = |names: &[&str]| names.iter().map(|name| (*name).to_owned()).collect();
        Ran {
            package: "host".to_owned(),
            binary: binary.to_owned(),
            requests: vec!["default".to_owned()],
            failed: failed.is_some(),
            observed: Some(Observed {
                failed: failed.map(names),
                passed: names(passed),
                ..Observed::default()
            }),
        }
    }

    #[test]
    fn rows_are_keys_with_a_flaky_mark_in_the_comment() {
        let known = known();
        assert_eq!(
            known.rows,
            BTreeMap::from([
                ("host::m::red".to_owned(), false),
                ("host::m::shaky".to_owned(), true),
                ("other::m::red".to_owned(), false),
            ])
        );
        assert_eq!(
            known.tests_of("host").collect::<Vec<_>>(),
            ["m::red", "m::shaky"]
        );
        // A binary is matched by its whole name.
        assert_eq!(known.tests_of("hos").count(), 0);
        // A byte-order mark before the first line is not a row.
        for text in ["\u{feff}# why\nhost::m::red\n", "\u{feff}host::m::red\n"] {
            let marked = KnownRed::parse(text).unwrap();
            assert_eq!(
                marked.rows,
                BTreeMap::from([("host::m::red".to_owned(), false)])
            );
        }
        for (text, expected) in [
            (
                "host::m::red\nhost::m::red # again\n",
                "line 2: `host::m::red` is listed twice",
            ),
            (
                "\nm_red\n",
                "line 2: `m_red` is not `<test binary>::<test path>`",
            ),
            ("host::m red\n", "line 1: `host::m red` is not"),
            ("::red\n", "line 1: `::red` is not"),
            ("host::\n", "line 1: `host::` is not"),
        ] {
            let error = KnownRed::parse(text).unwrap_err().to_string();
            assert!(error.contains(expected), "{error}");
        }
    }

    #[test]
    fn only_a_failure_in_listed_tests_alone_is_excused() {
        let known = known();
        let excused = known.judge(&ran("host", Some(&["m::red", "m::shaky"]), &[]));
        assert!(excused.excused);
        assert_eq!(excused.known, ["host::m::red", "host::m::shaky"]);
        // One unlisted failure beside a listed one.
        let mixed = known.judge(&ran("host", Some(&["m::red", "m::new"]), &[]));
        assert!(!mixed.excused);
        assert_eq!(mixed.known, ["host::m::red"]);
        assert_eq!(mixed.new, ["host::m::new"]);
        // The row is another binary's.
        let elsewhere = known.judge(&ran("third", Some(&["m::red"]), &[]));
        assert!(!elsewhere.excused);
        assert_eq!(elsewhere.new, ["third::m::red"]);
        // A failure with no test libtest reported failed: a crash, a signal,
        // a judged exit 0.
        let mut crashed = ran("host", Some(&[]), &[]);
        assert_eq!(known.judge(&crashed), Failure::default());
        crashed.observed.as_mut().unwrap().failed = None;
        assert_eq!(known.judge(&crashed), Failure::default());
        crashed.observed = None;
        assert_eq!(known.judge(&crashed), Failure::default());
        // An action that passed is not a failure to excuse.
        let mut passed = ran("host", Some(&["m::red"]), &[]);
        passed.failed = false;
        assert_eq!(known.judge(&passed), Failure::default());
    }

    #[test]
    fn a_listed_test_that_passed_is_stale_unless_its_row_is_flaky() {
        let known = known();
        let result = known.result(&[
            ran("host", None, &["m::red", "m::shaky", "m::required"]),
            ran("other", Some(&["m::red", "m::new"]), &[]),
            // In a failed harness too.
            ran("other", Some(&["m::new"]), &["m::red"]),
        ]);
        assert_eq!(result.stale, ["host::m::red", "other::m::red"]);
        // `other::m::red` failed beside a new failure: listed, not excused.
        assert!(result.excused.is_empty(), "{result:?}");
        assert_eq!(result.not_excused, ["other::m::red"]);
        assert_eq!(result.new_failures, ["other::m::new"]);
        // Only a harness that failed in listed tests alone has excused ones.
        let result = known.result(&[ran("host", Some(&["m::red"]), &[])]);
        assert_eq!(result.excused, ["host::m::red"]);
        assert!(result.not_excused.is_empty(), "{result:?}");
    }

    /// A key names a binary by crate name, so it must be one target's.
    #[test]
    fn a_row_whose_binary_name_two_targets_carry_is_refused() {
        let mut known = KnownRed::parse("it::m::red # a only\nhost::m::red\n").unwrap();
        known.file = "red.txt".to_owned();
        let carriers = |it: &[&str]| {
            BTreeMap::from([
                (
                    "it".to_owned(),
                    it.iter().map(|target| (*target).to_owned()).collect(),
                ),
                ("host".to_owned(), vec!["lib `host` of `host`".to_owned()]),
                // Shared, and no row names it.
                (
                    "cli".to_owned(),
                    vec![
                        "test `cli` of `a`".to_owned(),
                        "bin `cli` of `a`".to_owned(),
                    ],
                ),
            ])
        };
        known
            .require_one_binary(&carriers(&["test `it` of `a`"]))
            .unwrap();
        // A binary no target carries is a row that matches nothing.
        known.require_one_binary(&BTreeMap::new()).unwrap();
        let error = known
            .require_one_binary(&carriers(&["test `it` of `a`", "test `it` of `b`"]))
            .unwrap_err()
            .to_string();
        assert_eq!(
            error,
            "`[expect] known-red` file `red.txt`: row `it::m::red` names the test binary `it`, \
             and 2 test targets have that crate name: test `it` of `a`, test `it` of `b`. The \
             row would excuse the test in each of them; a known-red row needs a test binary \
             name that one target carries"
        );
    }

    /// The path is held under the workspace root as the file system
    /// resolves it, not only as it is written.
    #[cfg(unix)]
    #[test]
    fn a_path_that_a_symlink_leads_out_of_the_workspace_is_refused() {
        let outside = tempfile::tempdir().unwrap();
        let world = tempfile::tempdir().unwrap();
        let root = world.path();
        std::fs::write(outside.path().join("red.txt"), "host::m::red\n").unwrap();
        std::fs::create_dir(root.join("expect")).unwrap();
        std::fs::write(root.join("expect/red.txt"), "host::m::red\n").unwrap();
        std::os::unix::fs::symlink(outside.path(), root.join("expect/out")).unwrap();
        std::os::unix::fs::symlink("red.txt", root.join("expect/alias.txt")).unwrap();
        // A file under the root, by its name or by a link that stays inside.
        for file in ["expect/red.txt", "expect/alias.txt"] {
            let known = KnownRed::load(root, file).unwrap();
            assert_eq!(known.file, file);
            assert_eq!(known.rows.len(), 1);
        }
        let error = format!(
            "{:#}",
            KnownRed::load(root, "expect/out/red.txt").unwrap_err()
        );
        assert!(
            error.contains("`[expect] known-red = \"expect/out/red.txt\"` resolves to `")
                && error.contains("which is not under the workspace root"),
            "{error}"
        );
        let error = format!("{:#}", KnownRed::load(root, "expect/none.txt").unwrap_err());
        assert!(
            error.contains("failed to read `[expect] known-red` file"),
            "{error}"
        );
    }
}

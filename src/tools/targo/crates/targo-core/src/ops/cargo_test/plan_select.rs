//! Trust: which requests of a test plan one run performs.
//!
//! A run is told what changed, never asked to find out: `--changed-paths`
//! names a file of paths relative to the workspace root, and `-p` names
//! members the change reaches without touching. Targo runs no version
//! control command.
//!
//! * A member is *touched* when it owns a changed path: its directory is the
//!   longest member directory the path lies under, so a nested member never
//!   loses a path to its parent.
//! * A member is *selected* when it is touched or reached. `[default]` tests
//!   the selected members, and a variant runs iff its package is selected.
//! * An instrument runs iff a changed path meets its `when-changed`
//!   conditions, unless its host is touched and the default run performs
//!   everything the instrument would judge.
//! * A member is *selected* too when a changed path lies in the directory of
//!   a `[[tool]]` whose `needed-by` names it: its tests run that tool, so
//!   they are the tests of that change.
//! * A changed path under `select.attribute-under` that no request of the
//!   plan tests, and no `select.elsewhere` lane is named for, is
//!   *unattributed*: the run is refused, because its exit would be read as
//!   having tested that path.
//!
//! With neither input every request runs.

use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;

use super::plan::Instrument;
use crate::util::CargoResult;

/// The schema of the `test-plan` record.
pub const TEST_PLAN_SELECTION_SCHEMA_V1: &str = "targo.test-plan-selection.v1";

/// What the invocation says changed.
#[derive(Clone, Debug, Default)]
pub struct Input {
    /// The paths of `--changed-paths`; `None` without the flag.
    pub changed_paths: Option<Vec<String>>,
    /// The `-p` values, as typed.
    pub packages: Vec<String>,
    /// The `--reached` values, as typed: directories, each of a plan member
    /// or of a `[[workspace]]`.
    pub reached: Vec<String>,
    /// The git ranges whose changes are among `changed_paths`
    /// (`--changed-range`, and those `--changed-pushed-refs` stands for).
    pub ranges: Vec<String>,
}

impl Input {
    /// No input was given: the run is the whole plan. The command line
    /// asks for that with `--whole-plan` and refuses an invocation that
    /// names neither a change nor the whole plan (`plan::select`).
    pub fn is_whole_plan(&self) -> bool {
        self.changed_paths.is_none() && self.packages.is_empty() && self.reached.is_empty()
    }
}

/// Splits the bytes of a `--changed-paths` file. With a NUL anywhere the
/// separator is NUL (a path may then hold a newline), otherwise a newline.
/// Each path is relative to the workspace root and already normal: an
/// absolute path, or one with a `.`, `..` or empty component, could name a
/// file under a member's directory without lying under it as text.
///
/// A newline-separated list is text some tool printed, so a line that tool
/// may have altered is refused, never matched as written: a quoted name
/// (git quotes a name with a special byte unless asked for NUL), a control
/// character (the `\r` of a CRLF file), or white space at either end. Such a
/// line would own nothing, meet no condition and leave the run green.
pub fn parse_paths(bytes: &[u8]) -> CargoResult<Vec<String>> {
    let lines = !bytes.contains(&0);
    let separator = if lines { b'\n' } else { 0 };
    let mut paths = BTreeSet::new();
    for raw in bytes.split(|byte| *byte == separator) {
        if raw.is_empty() {
            continue;
        }
        let path = std::str::from_utf8(raw).map_err(|_| {
            anyhow::anyhow!(
                "changed path `{}` is not UTF-8",
                String::from_utf8_lossy(raw)
            )
        })?;
        anyhow::ensure!(
            path.split('/')
                .all(|part| !part.is_empty() && part != "." && part != ".."),
            "changed path `{path}` is not a normal path relative to the workspace root"
        );
        let altered = lines
            && (path.starts_with('"') || path.contains(char::is_control) || path.trim() != path);
        anyhow::ensure!(
            !altered,
            "changed path {path:?} is quoted, holds a control character, or starts or ends \
             with white space; a newline-separated list cannot name such a path, so pass the \
             paths NUL-separated"
        );
        paths.insert(path.to_owned());
    }
    Ok(paths.into_iter().collect())
}

/// What a directory of the workspace is to the plan.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Owner {
    /// A member some request of the plan tests: any plan member under a
    /// `[default]`, otherwise one a variant names.
    Member,
    /// A plan member no request tests: the plan has no `[default]` and no
    /// variant names it.
    Untested,
    /// A member `select.elsewhere` leaves to the command named.
    Elsewhere(String),
    /// A workspace member no request of the plan tests.
    Outside,
    /// The directory of a `[[workspace]]` manifest.
    OwnWorkspace,
}

/// The directories that own paths: each as written from the workspace root
/// with `/` (the root itself is the empty string), its name, and its role.
#[derive(Clone, Debug, Default)]
pub struct Layout {
    pub owners: Vec<(String, String, Owner)>,
    /// The `[[tool]]` entries, each as its directory (written as an owner's
    /// is), its manifest and its `needed-by`. A tool's directory takes no
    /// path from the member that owns it: a tool may be a member too.
    pub tools: Vec<(String, String, Vec<String>)>,
}

impl Layout {
    /// The owner of `path`: the longest directory it lies under.
    fn owner(&self, path: &str) -> Option<&(String, String, Owner)> {
        self.owners
            .iter()
            .filter(|(dir, _, _)| {
                dir.is_empty()
                    || path
                        .strip_prefix(dir.as_str())
                        .is_some_and(|rest| rest.is_empty() || rest.starts_with('/'))
            })
            .max_by_key(|(dir, _, _)| dir.len())
    }
}

/// Whether `path` lies in the directory `dir` (the root is the empty
/// string), by whole directory names.
fn lies_in(path: &str, dir: &str) -> bool {
    dir.is_empty()
        || path
            .strip_prefix(dir)
            .is_some_and(|rest| rest.is_empty() || rest.starts_with('/'))
}

/// A `[[tool]]` in whose directory a path changed: the tests of `members`
/// run it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ChangedTool {
    pub manifest: String,
    /// The tool's `needed-by`.
    pub members: Vec<String>,
    pub paths: Vec<String>,
}

/// A member another lane tests, and the changed paths it owns.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Elsewhere {
    pub member: String,
    pub command: String,
    pub paths: Vec<String>,
}

/// A changed path the plan must account for and does not.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Unattributed {
    pub path: String,
    pub why: String,
}

/// Whether a request runs, and the reason either way.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Decision {
    pub active: bool,
    pub why: String,
}

impl Decision {
    fn of(active: bool, why: String) -> Decision {
        Decision { active, why }
    }
}

/// The changed paths attributed to the plan's members.
#[derive(Clone, Debug, Default)]
pub struct Selection {
    /// Every request runs: `--whole-plan`, or a changed path that
    /// `select.whole-plan-when-changed` names.
    pub whole_plan: bool,
    /// The changed path that made this the whole plan, and the prefix of
    /// `select.whole-plan-when-changed` it lies under; `None` for
    /// `--whole-plan`.
    pub whole_because: Option<(String, String)>,
    pub changed_paths: Vec<String>,
    /// Members that own a changed path.
    pub touched: BTreeSet<String>,
    /// Members `-p` names.
    pub reached: BTreeSet<String>,
    /// The members `[default]` tests in this run: every plan member for the
    /// whole plan, otherwise the touched and the reached.
    pub selected: BTreeSet<String>,
    pub elsewhere: Vec<Elsewhere>,
    /// The `[[workspace]]` manifests whose directory holds a changed path;
    /// every one of the plan for the whole plan.
    pub workspaces: BTreeSet<String>,
    /// The `[[tool]]`s in whose directory a path changed.
    pub tools: Vec<ChangedTool>,
    pub unattributed: Vec<Unattributed>,
}

impl Selection {
    /// The changed tool `package` runs, if it runs one.
    fn changed_tool(&self, package: &str) -> Option<&str> {
        self.tools
            .iter()
            .find(|tool| tool.members.iter().any(|name| name == package))
            .map(|tool| tool.manifest.as_str())
    }

    /// Attributes each changed path of `input` to its owner in `layout`.
    /// `members` holds every plan member, `reached` the ones `-p` names;
    /// `attribute_under` the prefixes under which every path must be
    /// accounted for; `whole_when` the prefixes of the lane's own policy
    /// (`select.whole-plan-when-changed`): a change to what decides every
    /// request's verdict (the plan file, the known-red file) is judged by
    /// every request, never by whichever instrument its path happens to
    /// meet.
    pub fn attribute(
        layout: &Layout,
        attribute_under: &[String],
        whole_when: &[String],
        input: &Input,
        members: &BTreeSet<&str>,
        reached: BTreeSet<String>,
    ) -> Selection {
        let own = |role: Owner| {
            layout
                .owners
                .iter()
                .filter(move |(_, _, owner)| *owner == role)
                .map(|(_, name, _)| name.clone())
        };
        if input.is_whole_plan() {
            return Selection {
                whole_plan: true,
                // Every plan member, not every directory of the layout: a
                // member outside the workspace root owns no path and is
                // still tested.
                selected: members.iter().map(|name| (*name).to_owned()).collect(),
                workspaces: own(Owner::OwnWorkspace).collect(),
                ..Selection::default()
            };
        }
        let mut selection = Selection {
            changed_paths: input.changed_paths.clone().unwrap_or_default(),
            reached,
            ..Selection::default()
        };
        let mut elsewhere: BTreeMap<&str, Elsewhere> = BTreeMap::new();
        for path in &selection.changed_paths {
            let must = attribute_under
                .iter()
                .any(|prefix| path.starts_with(prefix.as_str()));
            // A change to a tool is tested by the members that run it,
            // whoever owns the path.
            let mut tool_changed = false;
            for (dir, manifest, needed_by) in &layout.tools {
                if !lies_in(path, dir) {
                    continue;
                }
                tool_changed = true;
                match selection
                    .tools
                    .iter_mut()
                    .find(|tool| tool.manifest == *manifest)
                {
                    Some(tool) => tool.paths.push(path.clone()),
                    None => selection.tools.push(ChangedTool {
                        manifest: manifest.clone(),
                        members: needed_by.clone(),
                        paths: vec![path.clone()],
                    }),
                }
            }
            let why = match layout.owner(path) {
                Some((_, name, Owner::Member)) => {
                    selection.touched.insert(name.clone());
                    continue;
                }
                Some((_, name, Owner::OwnWorkspace)) => {
                    selection.workspaces.insert(name.clone());
                    continue;
                }
                Some((_, name, Owner::Elsewhere(command))) => {
                    elsewhere
                        .entry(name)
                        .or_insert_with(|| Elsewhere {
                            member: name.clone(),
                            command: command.clone(),
                            paths: Vec::new(),
                        })
                        .paths
                        .push(path.clone());
                    continue;
                }
                Some((_, name, Owner::Untested)) => format!(
                    "its owner `{name}` is a plan member that no request tests: the plan has \
                     no `[default]` and no variant names `{name}`"
                ),
                Some((_, name, Owner::Outside)) => format!(
                    "its owner `{name}` is a workspace member that is neither a plan member \
                     nor in `select.elsewhere`"
                ),
                // No member owns the tool's directory; the members that
                // run the tool test the change (`ResolvedPlan::resolve`
                // refuses a tool change none of them tests).
                None if tool_changed => continue,
                None => "no workspace member owns it".to_owned(),
            };
            if must {
                selection.unattributed.push(Unattributed {
                    path: path.clone(),
                    why,
                });
            }
        }
        selection.elsewhere = elsewhere.into_values().collect();
        selection.selected = selection
            .touched
            .union(&selection.reached)
            .cloned()
            .collect();
        // Only a plan member is one `[default]` tests; a tool's other
        // consumers are hosts of instruments (`instrument`).
        let running = selection
            .tools
            .iter()
            .flat_map(|tool| &tool.members)
            .filter(|name| members.contains(name.as_str()))
            .cloned()
            .collect::<Vec<_>>();
        selection.selected.extend(running);
        let policy = selection.changed_paths.iter().find_map(|path| {
            whole_when
                .iter()
                .find(|prefix| path.starts_with(prefix.as_str()))
                .map(|prefix| (path.clone(), prefix.clone()))
        });
        if let Some(policy) = policy {
            // What the paths touch and what is unattributed stays as read;
            // what runs is everything.
            selection.whole_plan = true;
            selection.whole_because = Some(policy);
            selection.selected = members.iter().map(|name| (*name).to_owned()).collect();
            selection.workspaces = own(Owner::OwnWorkspace).collect();
        }
        selection
    }

    /// Whether `[default]` runs: it tests the selected members.
    pub fn default_run(&self) -> Decision {
        if self.whole_plan {
            return self.everything();
        }
        let (touched, reached) = (self.touched.len(), self.reached.len());
        if self.selected.is_empty() {
            Decision::of(false, "no plan member is touched or reached".to_owned())
        } else {
            let mut why = format!(
                "{} member{} selected ({touched} touched, {reached} reached)",
                self.selected.len(),
                if self.selected.len() == 1 { "" } else { "s" }
            );
            for tool in &self.tools {
                let running = tool
                    .members
                    .iter()
                    .filter(|name| self.selected.contains(*name))
                    .map(String::as_str)
                    .collect::<Vec<_>>();
                if !running.is_empty() {
                    why.push_str(&format!(
                        "; tool `{}` changed, which the tests of {} run",
                        tool.manifest,
                        running.join(", ")
                    ));
                }
            }
            Decision::of(true, why)
        }
    }

    /// Whether a variant of `package` runs: iff its package is selected.
    pub fn variant(&self, package: &str) -> Decision {
        if self.whole_plan {
            return self.everything();
        }
        let how = match (
            self.touched.contains(package),
            self.reached.contains(package),
        ) {
            (true, _) => "touched",
            (false, true) => "reached",
            (false, false) => {
                if let Some(tool) = self.changed_tool(package) {
                    return Decision::of(
                        true,
                        format!("package `{package}` runs tool `{tool}`, which changed"),
                    );
                }
                return Decision::of(false, format!("package `{package}` is not selected"));
            }
        };
        Decision::of(true, format!("package `{package}` is {how}"))
    }

    /// Whether an instrument runs: iff a changed path meets its conditions,
    /// unless its host is touched and the default run covers it. `covered`
    /// is `Ok` when the plan's default run of the host performs everything
    /// the instrument would judge, and otherwise says what it leaves out. A
    /// host that is only reached keeps its instrument.
    pub fn instrument(&self, run: &Instrument, covered: &Result<(), String>) -> Decision {
        if self.whole_plan {
            return self.everything();
        }
        let conditional = !run.when_changed.is_empty() || run.when_changed_suffix.is_some();
        let moved = if conditional {
            self.changed_paths
                .iter()
                .filter(|path| {
                    !run.not_under
                        .iter()
                        .any(|dir| path.starts_with(dir.as_str()))
                })
                .find_map(|path| {
                    let under = run
                        .when_changed
                        .iter()
                        .find(|prefix| path.starts_with(prefix.as_str()))
                        .map(|prefix| format!("changed path `{path}` is under `{prefix}`"));
                    under.or_else(|| {
                        run.when_changed_suffix
                            .as_ref()
                            .filter(|suffix| path.ends_with(suffix.as_str()))
                            .map(|suffix| format!("changed path `{path}` ends with `{suffix}`"))
                    })
                })
        } else {
            // No condition can only mean every selection: an instrument a
            // narrowed run never reached would be one nothing ever asks for.
            Some("it names no `when-changed` condition, so every selection runs it".to_owned())
        };
        let Some(moved) = moved else {
            // Its host runs a tool that changed, and the default run does
            // not perform what the instrument judges: nothing else of this
            // run would test the change through it.
            if let (Some(tool), Err(left_out)) = (self.changed_tool(&run.package), covered) {
                return Decision::of(
                    true,
                    format!(
                        "its host `{}` runs tool `{tool}`, which changed, and {left_out}",
                        run.package
                    ),
                );
            }
            return Decision::of(
                false,
                "no changed path meets its `when-changed` conditions".to_owned(),
            );
        };
        if !self.touched.contains(&run.package) {
            return Decision::of(true, moved);
        }
        match covered {
            Ok(()) => Decision::of(
                false,
                format!(
                    "its host `{}` is touched, so the default run tests it",
                    run.package
                ),
            ),
            Err(left_out) => Decision::of(
                true,
                format!(
                    "{moved}; its host `{}` is touched, but {left_out}",
                    run.package
                ),
            ),
        }
    }

    fn everything(&self) -> Decision {
        Decision::of(
            true,
            match &self.whole_because {
                Some((path, prefix)) => format!(
                    "changed path `{path}` is under `{prefix}`, which \
                     `select.whole-plan-when-changed` names: every request runs"
                ),
                None => "--whole-plan: every request runs".to_owned(),
            },
        )
    }
}

/// The paths a refused run names, for a caller that maps the refusal to its
/// own exit status.
#[derive(Debug)]
pub struct UnattributedPaths {
    pub plan: String,
    pub paths: Vec<Unattributed>,
}

impl std::fmt::Display for UnattributedPaths {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "test plan `{}`: {} changed path{} under `select.attribute-under` {} tested by no \
             request and named for no other lane; this run would be read as having tested {}:",
            self.plan,
            self.paths.len(),
            if self.paths.len() == 1 { "" } else { "s" },
            if self.paths.len() == 1 { "is" } else { "are" },
            if self.paths.len() == 1 { "it" } else { "them" },
        )?;
        for unattributed in &self.paths {
            write!(f, "\n    {}: {}", unattributed.path, unattributed.why)?;
        }
        Ok(())
    }
}

impl std::error::Error for UnattributedPaths {}

/// One request of the plan in the `test-plan` record.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RequestRow {
    pub id: String,
    /// `default`, `variant` or `instrument`.
    pub role: &'static str,
    /// The names of the packages the request tests when it runs.
    pub packages: Vec<String>,
    pub active: bool,
    pub why: String,
}

/// The `test-plan` record: the first line of a plan invocation's JSON. It
/// says which file was read, what the invocation said changed, and for every
/// request of the file whether this run performs it and why.
#[derive(Debug, Serialize)]
pub(super) struct TestPlanRecord<'a> {
    pub schema: &'static str,
    pub plan: String,
    /// SHA-256 of the plan file's bytes, in hex.
    pub sha256: &'a str,
    pub selection: Inputs<'a>,
    pub members: Members<'a>,
    pub requests: &'a [RequestRow],
    pub elsewhere: &'a [Elsewhere],
    pub workspaces: &'a BTreeSet<String>,
    /// The `[[tool]]`s in whose directory a path changed (`manifest`,
    /// `members`, `paths`).
    pub tools: &'a [ChangedTool],
    pub unattributed: &'a [Unattributed],
    /// In a `--select-only` listing only: what a run of this selection
    /// would do with each `[[tool]]` and `[[workspace]]` entry
    /// (`plan_phases::describe`). A run's own record has no such key; its
    /// phases are reported as they end.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub phases: Option<&'a [super::plan_phases::PhaseRow]>,
}

/// The selection inputs as given.
#[derive(Debug, Serialize)]
pub(super) struct Inputs<'a> {
    /// `null` when the invocation named no change: neither
    /// `--changed-paths` nor a range. Otherwise the union of both.
    pub changed_paths: Option<&'a [String]>,
    /// The git ranges that were diffed, as given to git.
    pub changed_ranges: &'a [String],
    pub packages: &'a [String],
    /// The `--reached` directories, as typed.
    pub reached: &'a [String],
    /// `--whole-plan`: every request, by request and not by default.
    pub whole_plan: bool,
    pub requests: &'a [String],
}

#[derive(Debug, Serialize)]
pub(super) struct Members<'a> {
    pub touched: &'a BTreeSet<String>,
    pub reached: &'a BTreeSet<String>,
    pub selected: &'a BTreeSet<String>,
}

impl crate::util::machine_message::Message for TestPlanRecord<'_> {
    fn reason(&self) -> &str {
        "test-plan"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ops::cargo_test::plan::TestPlan;

    fn set(names: &[&str]) -> BTreeSet<String> {
        names.iter().map(|name| (*name).to_owned()).collect()
    }

    fn layout() -> Layout {
        let owner = |dir: &str, name: &str, owner: Owner| (dir.to_owned(), name.to_owned(), owner);
        Layout {
            owners: vec![
                owner("crates/own", "crates/own/Cargo.toml", Owner::OwnWorkspace),
                owner("crates/outer", "outer", Owner::Member),
                owner("crates/outer/inner", "inner", Owner::Member),
                owner("crates/host", "host", Owner::Member),
                owner(
                    "crates/far",
                    "far",
                    Owner::Elsewhere("the far lane".to_owned()),
                ),
                owner("crates/stray", "stray", Owner::Outside),
                owner("crates/idle", "idle", Owner::Untested),
                owner("tools/aside", "aside", Owner::Outside),
            ],
            // `kit` has no member's directory; the other two lie in the
            // directories of the members `inner` and `stray`. `lone` is no plan member.
            tools: vec![
                (
                    "crates/kit".to_owned(),
                    "crates/kit/Cargo.toml".to_owned(),
                    vec!["host".to_owned(), "lone".to_owned()],
                ),
                (
                    "crates/outer/inner/tool".to_owned(),
                    "crates/outer/inner/tool/Cargo.toml".to_owned(),
                    vec!["outer".to_owned()],
                ),
                (
                    "crates/stray/tool".to_owned(),
                    "crates/stray/tool/Cargo.toml".to_owned(),
                    vec!["host".to_owned()],
                ),
            ],
        }
    }

    fn attribute(paths: &[&str], reached: &[&str]) -> Selection {
        let input = Input {
            changed_paths: Some(paths.iter().map(|path| (*path).to_owned()).collect()),
            packages: reached.iter().map(|name| (*name).to_owned()).collect(),
            ..Input::default()
        };
        Selection::attribute(
            &layout(),
            &["crates/".to_owned()],
            &["policy/".to_owned()],
            &input,
            &MEMBERS.into(),
            set(reached),
        )
    }

    /// The plan's members; `afar` lies outside the workspace root, so the
    /// layout has no directory for it.
    const MEMBERS: [&str; 4] = ["afar", "host", "inner", "outer"];

    fn whole() -> Selection {
        Selection::attribute(
            &layout(),
            &[],
            &[],
            &Input::default(),
            &MEMBERS.into(),
            BTreeSet::new(),
        )
    }

    #[test]
    fn paths_are_split_on_nul_when_there_is_one_and_held_to_normal_form() {
        let paths = |bytes: &[u8]| parse_paths(bytes).map_err(|error| error.to_string());
        assert_eq!(paths(b""), Ok(vec![]));
        assert_eq!(paths(b"\n\n"), Ok(vec![]));
        // Sorted, each once, with or without a final separator.
        assert_eq!(
            paths(b"b/c\na\nb/c"),
            Ok(vec!["a".to_owned(), "b/c".to_owned()])
        );
        // With a NUL, a newline is part of a name.
        assert_eq!(
            paths(b"a\nb\0c\0"),
            Ok(vec!["a\nb".to_owned(), "c".to_owned()])
        );
        for wrong in [
            &b"/a"[..],
            b"a/../b",
            b"./a",
            b"a//b",
            b"a/",
            b"..",
            b"a\0\0/b\0",
        ] {
            let refused = paths(wrong).unwrap_err();
            assert!(refused.contains("is not a normal path"), "{refused}");
        }
        // A line some tool altered names no file: a CRLF file's `\r`, git's
        // quoting of a special byte, a tab, white space at either end.
        for altered in [
            &b"docs/a.json\r\nb\r\n"[..],
            b"\"crates/b/src/caf\\303\\251.rs\"\n",
            b"a\tb\n",
            b"docs/a.json \n",
            b" docs/a.json\n",
        ] {
            let refused = paths(altered).unwrap_err();
            assert!(
                refused.contains("pass the paths NUL-separated"),
                "{refused}"
            );
        }
        // NUL-separated paths are taken as written.
        assert_eq!(
            paths(b"a \0\"b\"\0c\r\0"),
            Ok(vec!["\"b\"".to_owned(), "a ".to_owned(), "c\r".to_owned()])
        );
        assert!(paths(b"a\xff").unwrap_err().contains("is not UTF-8"));
    }

    #[test]
    fn a_path_belongs_to_the_longest_member_directory_it_lies_under() {
        // (path, touched members, own workspaces, elsewhere, unattributed)
        type Row<'a> = (
            &'a str,
            &'a [&'a str],
            &'a [&'a str],
            &'a [&'a str],
            Option<&'a str>,
        );
        let table: [Row<'_>; 14] = [
            ("crates/outer/src/lib.rs", &["outer"], &[], &[], None),
            ("crates/outer/inner/src/lib.rs", &["inner"], &[], &[], None),
            ("crates/outer/inner", &["inner"], &[], &[], None),
            ("crates/outer/innermost/x", &["outer"], &[], &[], None),
            (
                "crates/own/src/lib.rs",
                &[],
                &["crates/own/Cargo.toml"],
                &[],
                None,
            ),
            ("crates/far/src/lib.rs", &[], &[], &["far"], None),
            (
                "crates/stray/src/lib.rs",
                &[],
                &[],
                &[],
                Some(
                    "its owner `stray` is a workspace member that is neither a plan member nor \
                     in `select.elsewhere`",
                ),
            ),
            (
                "crates/idle/src/lib.rs",
                &[],
                &[],
                &[],
                Some(
                    "its owner `idle` is a plan member that no request tests: the plan has no \
                     `[default]` and no variant names `idle`",
                ),
            ),
            (
                "crates/nobody/x",
                &[],
                &[],
                &[],
                Some("no workspace member owns it"),
            ),
            (
                "crates/outer.md",
                &[],
                &[],
                &[],
                Some("no workspace member owns it"),
            ),
            (
                "crates/hostile/x",
                &[],
                &[],
                &[],
                Some("no workspace member owns it"),
            ),
            // Outside `attribute-under` nothing has to be accounted for.
            ("tools/aside/src/lib.rs", &[], &[], &[], None),
            ("README.md", &[], &[], &[], None),
            ("xcrates/outer/src/lib.rs", &[], &[], &[], None),
        ];
        for (path, touched, workspaces, elsewhere, unattributed) in table {
            let selection = attribute(&[path], &[]);
            assert_eq!(selection.touched, set(touched), "{path}");
            assert_eq!(selection.selected, set(touched), "{path}");
            assert_eq!(selection.workspaces, set(workspaces), "{path}");
            assert_eq!(
                selection
                    .elsewhere
                    .iter()
                    .map(|elsewhere| elsewhere.member.as_str())
                    .collect::<Vec<_>>(),
                elsewhere,
                "{path}"
            );
            assert_eq!(
                selection
                    .unattributed
                    .iter()
                    .map(|unattributed| (unattributed.path.as_str(), unattributed.why.as_str()))
                    .collect::<Vec<_>>(),
                unattributed
                    .map(|why| (path, why))
                    .into_iter()
                    .collect::<Vec<_>>(),
                "{path}"
            );
        }
        // A package at the workspace root owns what no other member does.
        let mut rooted = layout();
        rooted
            .owners
            .push((String::new(), "root".to_owned(), Owner::Member));
        let input = Input {
            changed_paths: Some(vec![
                "README.md".to_owned(),
                "crates/nobody/x".to_owned(),
                "crates/host/x".to_owned(),
            ]),
            ..Input::default()
        };
        let selection = Selection::attribute(
            &rooted,
            &["crates/".to_owned()],
            &[],
            &input,
            &MEMBERS.into(),
            BTreeSet::new(),
        );
        assert_eq!(selection.touched, set(&["host", "root"]));
        assert_eq!(selection.unattributed, []);
    }

    #[test]
    fn the_whole_plan_runs_when_nothing_says_what_changed() {
        let whole = whole();
        assert!(whole.whole_plan);
        // Every plan member, with a directory under the root or not.
        assert_eq!(whole.selected, set(&MEMBERS));
        assert_eq!(whole.workspaces, set(&["crates/own/Cargo.toml"]));
        assert!(whole.default_run().active && whole.variant("anything").active);
        // An empty list of changed paths is a selection of nothing, not the
        // absence of one.
        let nothing = attribute(&[], &[]);
        assert!(!nothing.whole_plan);
        assert_eq!(
            nothing.default_run(),
            Decision::of(false, "no plan member is touched or reached".to_owned())
        );
        assert!(nothing.workspaces.is_empty());
    }

    // The lane's own policy (its plan file, its known-red file) decides
    // what every request's result means, so a change to it runs every
    // request, whatever else its path would have selected.
    #[test]
    fn a_change_to_the_lanes_policy_runs_the_whole_plan() {
        let policy = attribute(&["policy/known-red.txt", "crates/far/src/lib.rs"], &[]);
        assert!(policy.whole_plan);
        assert_eq!(policy.selected, set(&MEMBERS));
        assert_eq!(policy.workspaces, set(&["crates/own/Cargo.toml"]));
        let why = "changed path `policy/known-red.txt` is under `policy/`, which \
                   `select.whole-plan-when-changed` names: every request runs";
        assert_eq!(policy.default_run(), Decision::of(true, why.to_owned()));
        assert_eq!(policy.variant("outer"), Decision::of(true, why.to_owned()));
        // What the paths themselves say is kept: the other lane is named,
        // and an unowned path is still refused.
        assert_eq!(policy.elsewhere.len(), 1);
        let unowned = attribute(&["policy/plan.toml", "crates/nobody/a.rs"], &[]);
        assert!(unowned.whole_plan);
        assert_eq!(unowned.unattributed.len(), 1);
        // A path beside the policy directory is no policy.
        let beside = attribute(&["policies/known-red.txt"], &[]);
        assert!(!beside.whole_plan);
        assert!(beside.selected.is_empty());
    }

    #[test]
    fn a_variant_runs_iff_its_package_is_touched_or_reached() {
        let selection = attribute(&["crates/outer/src/lib.rs"], &["host"]);
        assert_eq!(selection.selected, set(&["host", "outer"]));
        assert_eq!(
            selection.default_run(),
            Decision::of(true, "2 members selected (1 touched, 1 reached)".to_owned())
        );
        assert_eq!(
            selection.variant("outer"),
            Decision::of(true, "package `outer` is touched".to_owned())
        );
        assert_eq!(
            selection.variant("host"),
            Decision::of(true, "package `host` is reached".to_owned())
        );
        assert_eq!(
            selection.variant("inner"),
            Decision::of(false, "package `inner` is not selected".to_owned())
        );
    }

    #[test]
    fn an_instrument_runs_iff_a_path_meets_it_and_its_touched_host_is_not_already_tested() {
        let plan = TestPlan::parse(
            r#"
schema = "targo.test-plan.v1"
[select]
members = "default-members"
[[instrument]]
id = "prefix"
package = "host"
lib = true
when-changed = ["fixtures/", "crates/outer/src/gen"]
not-under = ["fixtures/skipped/"]
[[instrument]]
id = "suffix"
package = "host"
lib = true
when-changed-suffix = ".json"
not-under = ["first-party/", "vendor/"]
[[instrument]]
id = "always"
package = "host"
lib = true
"#,
        )
        .unwrap();
        let [prefix, suffix, always] = &plan.instrument[..] else {
            panic!()
        };
        // (paths, reached, instrument, default run tests the host, active)
        type Row<'a> = (&'a [&'a str], &'a [&'a str], &'a Instrument, bool, bool);
        let table: [Row<'_>; 16] = [
            (&["fixtures/a"], &[], prefix, true, true),
            (&["fixtures"], &[], prefix, true, false),
            (&["other/fixtures/a"], &[], prefix, true, false),
            (&["crates/outer/src/generated.rs"], &[], prefix, true, true),
            (&["fixtures/skipped/a"], &[], prefix, true, false),
            (
                &["fixtures/skipped/a", "fixtures/b"],
                &[],
                prefix,
                true,
                true,
            ),
            // The host is touched and the default run tests it.
            (&["fixtures/a", "crates/host/x"], &[], prefix, true, false),
            // The host is touched and no default run tests it.
            (&["fixtures/a", "crates/host/x"], &[], prefix, false, true),
            // The host is only reached.
            (&["fixtures/a"], &["host"], prefix, true, true),
            (&[], &["host"], prefix, true, false),
            (&["a/b.json"], &[], suffix, true, true),
            (&["a/b.json5"], &[], suffix, true, false),
            (&["vendor/b.json"], &[], suffix, true, false),
            (&["crates/host/b.json"], &[], suffix, true, false),
            // No condition: every selection runs it, unless the default run
            // tests its touched host.
            (&[], &["outer"], always, true, true),
            (&["crates/host/x"], &[], always, true, false),
        ];
        for (paths, reached, instrument, covered, active) in table {
            let covered = if covered {
                Ok(())
            } else {
                Err("the default run leaves it out".to_owned())
            };
            let decision = attribute(paths, reached).instrument(instrument, &covered);
            assert_eq!(
                decision.active, active,
                "{paths:?} {reached:?} `{}` covered={covered:?}: {}",
                instrument.id, decision.why
            );
        }
        assert_eq!(
            attribute(&["x", "a/b.json"], &[])
                .instrument(suffix, &Ok(()))
                .why,
            "changed path `a/b.json` ends with `.json`"
        );
        assert_eq!(
            attribute(&["fixtures/a", "crates/host/x"], &[])
                .instrument(prefix, &Ok(()))
                .why,
            "its host `host` is touched, so the default run tests it"
        );
        assert_eq!(
            attribute(&["fixtures/a", "crates/host/x"], &[])
                .instrument(prefix, &Err("the default run leaves it out".to_owned()))
                .why,
            "changed path `fixtures/a` is under `fixtures/`; its host `host` is touched, but \
             the default run leaves it out"
        );
        assert!(whole().instrument(prefix, &Ok(())).active);
    }

    #[test]
    fn a_changed_tool_selects_the_members_that_run_it() {
        let plan = TestPlan::parse(
            "schema = \"targo.test-plan.v1\"\n[select]\nmembers = \"default-members\"\n\
             [[instrument]]\nid = \"lone-check\"\npackage = \"lone\"\nlib = true\n\
             when-changed = [\"fixtures/\"]\n",
        )
        .unwrap();
        let lone = &plan.instrument[0];
        let uncovered = Err("no default run tests it".to_owned());

        // A tool no member owns: the path is accounted for by the plan
        // members that run the tool, which are selected though untouched.
        let selection = attribute(&["crates/kit/src/main.rs"], &[]);
        assert_eq!(selection.unattributed, []);
        assert_eq!(selection.touched, set(&[]));
        assert_eq!(selection.selected, set(&["host"]));
        assert_eq!(
            selection.tools,
            [ChangedTool {
                manifest: "crates/kit/Cargo.toml".to_owned(),
                members: vec!["host".to_owned(), "lone".to_owned()],
                paths: vec!["crates/kit/src/main.rs".to_owned()],
            }]
        );
        assert_eq!(
            selection.default_run(),
            Decision::of(
                true,
                "1 member selected (0 touched, 0 reached); tool `crates/kit/Cargo.toml` \
                 changed, which the tests of host run"
                    .to_owned()
            )
        );
        assert_eq!(
            selection.variant("host"),
            Decision::of(
                true,
                "package `host` runs tool `crates/kit/Cargo.toml`, which changed".to_owned()
            )
        );
        assert!(!selection.variant("outer").active);
        // A consumer no default run tests keeps its instrument; one the
        // default run covers is tested by it.
        assert_eq!(
            selection.instrument(lone, &uncovered),
            Decision::of(
                true,
                "its host `lone` runs tool `crates/kit/Cargo.toml`, which changed, and no \
                 default run tests it"
                    .to_owned()
            )
        );
        assert!(!selection.instrument(lone, &Ok(())).active);
        // By whole directory names, and the manifest itself counts.
        assert_eq!(attribute(&["crates/kit/Cargo.toml"], &[]).tools.len(), 1);
        let beside = attribute(&["crates/kitchen/x"], &[]);
        assert_eq!(beside.tools, []);
        assert_eq!(beside.selected, set(&[]));
        assert_eq!(beside.unattributed.len(), 1);
        assert!(!beside.instrument(lone, &uncovered).active);

        // A tool inside a member's directory: the member is touched, and
        // the members that run the tool are selected with it.
        let selection = attribute(&["crates/outer/inner/tool/src/main.rs"], &[]);
        assert_eq!(selection.touched, set(&["inner"]));
        assert_eq!(selection.selected, set(&["inner", "outer"]));
        // A tool that is a member no request tests: its consumers run, and
        // its own tests are still tested by nothing.
        let selection = attribute(&["crates/stray/tool/src/main.rs"], &[]);
        assert_eq!(selection.selected, set(&["host"]));
        assert_eq!(selection.unattributed.len(), 1);
        // The whole plan names no change.
        assert_eq!(whole().tools, []);
    }

    #[test]
    fn the_refusal_lists_each_unattributed_path_with_its_reason() {
        let selection = attribute(&["crates/nobody/x", "crates/stray/y"], &[]);
        let refusal = UnattributedPaths {
            plan: "plan.toml".to_owned(),
            paths: selection.unattributed,
        }
        .to_string();
        assert!(
            refusal.starts_with(
                "test plan `plan.toml`: 2 changed paths under `select.attribute-under` are \
                 tested by no request"
            ) && refusal.contains("\n    crates/nobody/x: no workspace member owns it")
                && refusal.contains("\n    crates/stray/y: its owner `stray`"),
            "{refusal}"
        );
    }
}

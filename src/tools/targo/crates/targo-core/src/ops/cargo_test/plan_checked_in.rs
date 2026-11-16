//! Trust: holds the repository's checked-in test plan,
//! `tests/test-plans/crates.toml`, to the tree it is checked into.
//!
//! A plan names packages, features, targets, manifests, test paths and
//! directories as text. One that no longer exists is not always an error
//! where the plan is read: a harness filter that matches nothing selects no
//! test, a `when-changed` prefix that names nothing never fires, and a
//! crate that became its own workspace is tested only if the plan lists
//! it. These tests fail on each such name, so a rename is found here and
//! not as a run that tested less.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use cargo_util_terminal::Shell;

use super::plan::{Instrument, ResolvedPlan};
use super::plan_select::Input;
use crate::util::GlobalContext;
use crate::workspace::{Package, Target, Workspace};

/// The plan, from the repository root.
const PLAN: &str = "tests/test-plans/crates.toml";

/// The repository this Targo is a tool of: `src/tools/targo/crates/targo-core`
/// is five directories below its root.
fn repository() -> PathBuf {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(5)
        .expect("targo-core is five directories below the repository root")
        .to_path_buf();
    assert!(
        root.join(PLAN).is_file(),
        "`{PLAN}` is not in `{}`: the lane's plan must be checked in beside the Targo that \
         reads it",
        root.display()
    );
    root
}

/// Loads the root workspace and the plan as a whole-plan run does, with no
/// configuration from a home directory.
fn with_plan(check: impl FnOnce(&Path, &Workspace<'_>, &ResolvedPlan)) {
    with_plan_for(Input::default(), check);
}

/// As [`with_plan`], for a run told that `input` changed.
fn with_plan_for(input: Input, check: impl FnOnce(&Path, &Workspace<'_>, &ResolvedPlan)) {
    let root = repository();
    let home = tempfile::tempdir().unwrap();
    let mut gctx = GlobalContext::new(Shell::new(), root.clone(), home.path().to_path_buf());
    gctx.set_search_stop_path(&root);
    gctx.set_env(Default::default());
    // Quiet: the root workspace's manifest warnings are not this test's.
    gctx.configure(0, true, None, false, false, true, &None, &[], &[])
        .unwrap();
    let ws = Workspace::new(&root.join("Cargo.toml"), &gctx).unwrap();
    let plan = ResolvedPlan::load(&ws, &root.join(PLAN), &[], input)
        .unwrap_or_else(|error| panic!("`{PLAN}` does not load: {error:?}"));
    check(&root, &ws, &plan);
}

fn member<'a>(ws: &'a Workspace<'_>, name: &str) -> &'a Package {
    ws.members()
        .find(|package| package.name().as_str() == name)
        .unwrap_or_else(|| panic!("`{name}` is not a workspace member"))
}

fn read(path: &Path) -> String {
    std::fs::read_to_string(path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()))
}

/// The targets a request with `lib` and `test` selects, each a target the
/// package has and tests.
fn require_targets(what: &str, package: &Package, lib: bool, tests: &[String]) {
    let name = package.name();
    if lib {
        assert!(
            package
                .targets()
                .iter()
                .any(|target| target.is_lib() && target.tested()),
            "{what}: package `{name}` has no lib target that is tested"
        );
    }
    for test in tests {
        assert!(
            package
                .targets()
                .iter()
                .any(|target| target.is_test() && target.name() == test && target.tested()),
            "{what}: package `{name}` has no test target `{test}`"
        );
    }
}

/// Where the block ends whose `{` was just read: the index of its `}` in
/// `text`. A brace in a comment, a string or a character is not one of the
/// block's.
fn block_end(text: &str) -> Option<usize> {
    let bytes = text.as_bytes();
    let mut depth = 1usize;
    let mut at = 0;
    while at < bytes.len() {
        let rest = &bytes[at..];
        match bytes[at] {
            b'/' if rest.starts_with(b"//") => {
                at += memchr::memchr(b'\n', rest).unwrap_or(rest.len());
            }
            b'/' if rest.starts_with(b"/*") => {
                // Block comments nest.
                let mut open = 1usize;
                at += 2;
                while open > 0 && at < bytes.len() {
                    if bytes[at..].starts_with(b"/*") {
                        open += 1;
                        at += 2;
                    } else if bytes[at..].starts_with(b"*/") {
                        open -= 1;
                        at += 2;
                    } else {
                        at += 1;
                    }
                }
            }
            b'"' => {
                // `r"..."`, `r#"..."#`: no escapes, closed by as many `#`.
                let hashes = bytes[..at]
                    .iter()
                    .rev()
                    .take_while(|byte| **byte == b'#')
                    .count();
                let raw = at > hashes && bytes[at - 1 - hashes] == b'r';
                at += 1;
                if raw {
                    let mut close = vec![b'"'];
                    close.resize(1 + hashes, b'#');
                    at += memchr::memmem::find(&bytes[at..], &close)? + close.len();
                } else {
                    while *bytes.get(at)? != b'"' {
                        at += if bytes[at] == b'\\' { 2 } else { 1 };
                    }
                    at += 1;
                }
            }
            b'\'' if rest.get(1) == Some(&b'\\') => {
                // An escaped character: the quote, the backslash and what
                // it escapes, then on to the closing quote.
                at += 3;
                at += memchr::memchr(b'\'', bytes.get(at..)?)? + 1;
            }
            b'\'' => {
                // A character, or else a lifetime, which opens nothing.
                let width = text[at + 1..].chars().next().map_or(0, char::len_utf8);
                if width > 0 && bytes.get(at + 1 + width) == Some(&b'\'') {
                    at += width + 2;
                } else {
                    at += 1;
                }
            }
            b'{' => {
                depth += 1;
                at += 1;
            }
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    return Some(at);
                }
                at += 1;
            }
            _ => at += 1,
        }
    }
    None
}

/// The block of the module `module` that `text` opens inline, braces left
/// out: what the module holds, and nothing a later sibling does.
fn inline_module<'a>(text: &'a str, module: &str) -> Option<&'a str> {
    let opening = format!("mod {module} {{");
    let body = &text[text.find(&opening)? + opening.len()..];
    Some(&body[..block_end(body)?])
}

/// The source text in which the tests of the module path `modules` are
/// written: `src/<first>.rs` (or `src/<first>/mod.rs`), narrowed to the block
/// of each further module, which is opened inline.
fn module_text(what: &str, package: &Package, modules: &[&str]) -> String {
    let (first, inner) = modules
        .split_first()
        .unwrap_or_else(|| panic!("{what}: names no module"));
    let src = package.root().join("src");
    let file = [
        src.join(format!("{first}.rs")),
        src.join(first).join("mod.rs"),
    ]
    .into_iter()
    .find(|file| file.is_file())
    .unwrap_or_else(|| {
        panic!(
            "{what}: package `{}` has no `src/{first}.rs` and no `src/{first}/mod.rs`",
            package.name()
        )
    });
    let mut text = read(&file);
    for module in inner {
        text = inline_module(&text, module)
            .unwrap_or_else(|| {
                panic!(
                    "{what}: `{}` opens no `mod {module} {{ .. }}` where the path expects it",
                    file.display()
                )
            })
            .to_owned();
    }
    text
}

/// The libtest options whose value is the next argument.
const VALUED_OPTIONS: [&str; 7] = [
    "--skip",
    "--test-threads",
    "--logfile",
    "--color",
    "--format",
    "--shuffle-seed",
    "-Z",
];

/// The harness arguments `args` that are test-name filters: not an option,
/// and not the value of one (`--skip <name>` names what is left out).
fn filters(args: &[String]) -> Vec<&str> {
    let mut filters = Vec::new();
    let mut args = args.iter().map(String::as_str);
    while let Some(argument) = args.next() {
        if VALUED_OPTIONS.contains(&argument) {
            args.next();
        } else if !argument.starts_with('-') {
            filters.push(argument);
        }
    }
    filters
}

/// What makes a run that tested nothing fail is each one key of the file.
/// Without it the plan still loads, and every other name in it still exists.
#[test]
fn the_plan_keeps_each_requirement_that_fails_a_run_that_tested_too_little() {
    with_plan(|_, _, plan| {
        let rows: Vec<(&str, bool)> = plan
            .rows
            .iter()
            .map(|row| (row.id.as_str(), row.active))
            .collect();
        let requests = 1 + plan.plan.variant.len() + plan.plan.instrument.len();
        assert_eq!(rows.len(), requests, "{rows:?}");
        assert!(rows.iter().all(|(_, active)| *active), "{rows:?}");
        // An unowned change under `crates/` is refused, not read as tested.
        assert_eq!(plan.plan.select.attribute_under, ["crates/"]);
        // The zero-test rule: a member that reports no test fails.
        let default = plan
            .plan
            .default
            .as_ref()
            .expect("the plan has a `[default]` run");
        assert_eq!(
            default.min_tests,
            Some(1),
            "`[default] min-tests = 1` is the lane's zero-test rule"
        );
        // The ratchet: without it every failure is a new one, and with
        // another file the rows of this one excuse nothing.
        let expect = plan
            .plan
            .expect
            .as_ref()
            .and_then(|expect| expect.known_red.as_deref());
        assert_eq!(expect, Some("tests/known-red/crates-tests.txt"));
        // A change to the lane's own policy is judged by every request: the
        // plan names itself and its known-red file.
        for policy in [PLAN, "tests/known-red/crates-tests.txt"] {
            assert!(
                plan.plan
                    .select
                    .whole_plan_when_changed
                    .iter()
                    .any(|prefix| policy.starts_with(prefix.as_str())),
                "`[select] whole-plan-when-changed` names `{policy}`"
            );
        }
        // The harness that misses its own deadline beside others runs alone.
        let alone = plan
            .plan
            .harness
            .get("trust-clean")
            .and_then(|targets| targets.test.get("clean_pipeline_integration"))
            .and_then(|harness| harness.exclusive);
        assert_eq!(
            alone,
            Some(true),
            "`[harness.trust-clean.test.clean_pipeline_integration] exclusive = true`"
        );
        // The digest test must itself run and pass: the ignored re-bless
        // printer beside it reports a passing run without it.
        let digest = plan
            .plan
            .instrument
            .iter()
            .find(|run| run.id == "prelude-digest")
            .expect("the plan has the `prelude-digest` instrument");
        assert_eq!(
            digest.require_pass,
            ["tests::digest::source_digest_matches"]
        );
    });
}

/// What the plan selects for a change: the members it touches, the
/// `[[workspace]]` manifests it moves, and the variants and instruments the
/// run performs.
fn selected_for(
    paths: &[&str],
    reached: &[&str],
) -> (BTreeSet<String>, BTreeSet<String>, BTreeSet<String>) {
    let input = Input {
        changed_paths: Some(paths.iter().map(|path| (*path).to_owned()).collect()),
        reached: reached.iter().map(|dir| (*dir).to_owned()).collect(),
        ..Input::default()
    };
    let mut selected = Default::default();
    with_plan_for(input, |_, _, plan| {
        assert!(
            plan.selection.unattributed.is_empty(),
            "{paths:?}: {:?}",
            plan.selection.unattributed
        );
        let active = plan
            .rows
            .iter()
            .filter(|row| row.active && row.role != "default")
            .map(|row| row.id.clone())
            .collect();
        selected = (
            plan.selection.touched.clone(),
            plan.selection.workspaces.clone(),
            active,
        );
    });
    selected
}

fn set(items: &[&str]) -> BTreeSet<String> {
    items.iter().map(|item| (*item).to_owned()).collect()
}

/// The changes that each once reached main untested (or that a review found
/// would) select the request that tests them. These are the plan's data, not
/// Targo's rules (`plan_select`'s tests hold the rules on fixtures): a row
/// that loses a `when-changed` prefix, a suffix or an exclusion still loads,
/// and only this says that the change it was written for now runs nothing.
/// They are the script lane's planning tests, kept against the plan that
/// replaced its tables (CRATES-LANE-NATIVE-1).
#[test]
fn each_change_a_lane_was_written_for_selects_the_request_that_tests_it() {
    let none = BTreeSet::new();
    // 1f3b181649 (2026-09-30) changed trust-vcgen alone and left the ratchet,
    // a trust-ir-bridge test whose subject is trust-vcgen's output, red on
    // main: the push tested only trust-vcgen.
    let (touched, _, active) = selected_for(&["crates/trust-vcgen/src/generate/numeric_panic.rs"], &[]);
    assert_eq!(touched, set(&["trust-vcgen"]));
    assert_eq!(active, set(&["missing-obligation-ratchet"]));
    // A fixture-only change moves the ratchet's corpus, and, being a JSON
    // document, trust-json's corpus gate.
    let (_, _, active) = selected_for(&["crates/trust-clean/fixtures/x/dump.json"], &[]);
    assert_eq!(active, set(&["json-corpus", "missing-obligation-ratchet"]));
    // B1A-D35 (2026-10-09): PRELUDE_DIGEST covers the Trust/*.lean files that
    // trust-spec-temporal owns, so an edit of one of them alone runs the
    // digest check. A Rust change of that crate does not move its subject.
    for lean in ["Temporal.lean", "FiniteModel.lean", "Model/Value.lean"] {
        let path = format!("crates/trust-spec-temporal/clean/Trust/{lean}");
        let (touched, workspaces, active) = selected_for(&[&path], &[]);
        assert_eq!(touched, none, "{lean}");
        assert_eq!(workspaces, set(&["crates/trust-spec-temporal/Cargo.toml"]), "{lean}");
        assert_eq!(active, set(&["prelude-digest"]), "{lean}");
    }
    let (_, workspaces, active) = selected_for(&["crates/trust-spec-temporal/src/lib.rs"], &[]);
    assert_eq!(workspaces, set(&["crates/trust-spec-temporal/Cargo.toml"]));
    assert_eq!(active, none);
    // 2026-10-08: a push with no `crates/` path reached no gate, so a JSON or
    // TOML document anywhere went unmeasured by its corpus gate.
    for path in ["reports/source-integrations/r.json", "x.json"] {
        assert_eq!(selected_for(&[path], &[]), (none.clone(), none.clone(), set(&["json-corpus"])), "{path}");
    }
    assert_eq!(
        selected_for(&["library/core/Cargo.toml"], &[]),
        (none.clone(), none.clone(), set(&["toml-corpus"]))
    );
    // The corpora's own exclusions, another suffix, and a suffix that is only
    // a substring select nothing.
    let outside = [
        "first-party/clean/x.json",
        "vendor/serde/Cargo.toml",
        "docs/a.jsonl",
        "docs/b.json.md",
        "docs/toml.md",
    ];
    assert_eq!(selected_for(&outside, &[]), (none.clone(), none.clone(), none.clone()));
    // TRUST-16: a trust-router change, or a run that reaches trust-router
    // without changing it, performs every one of its feature lanes, the
    // setter lane's integration target among them. A change elsewhere
    // performs none of them.
    let router = set(&["router-ay-backend", "router-certify", "router-setter"]);
    for (paths, reached) in [
        (&["crates/trust-router/src/lib.rs"][..], &[][..]),
        (&["crates/trust-router/tests/setter_assert_refute_lane.rs"][..], &[][..]),
        (&["docs/changed.md"][..], &["crates/trust-router"][..]),
    ] {
        let (_, _, active) = selected_for(paths, reached);
        assert_eq!(active, router, "{paths:?} {reached:?}");
    }
    let (touched, _, active) = selected_for(&["crates/trust-clean/src/lib.rs"], &[]);
    assert_eq!(touched, set(&["trust-clean"]));
    assert_eq!(active, none);
    // A change of the binary-decompilation fixtures alone runs their consumer,
    // which needs the targo-trust the `[[tool]]` builds for it.
    for path in [
        "tests/fixtures/binary_decomp/x86_64-load-elf.hex",
        "tests/fixtures/binary_decomp/regenerate_exec_entry_elf.sh",
    ] {
        assert_eq!(
            selected_for(&[path], &[]),
            (none.clone(), none.clone(), set(&["binary-to-trust-ir-e2e"])),
            "{path}"
        );
    }
    with_plan(|_, _, plan| {
        let consumer = plan
            .plan
            .instrument
            .iter()
            .find(|run| run.id == "binary-to-trust-ir-e2e")
            .expect("the plan has the `binary-to-trust-ir-e2e` instrument");
        assert!(
            plan.plan
                .tool
                .iter()
                .any(|tool| tool.bin == "targo-trust" && tool.needed_by.contains(&consumer.package)),
            "the targo-trust `[[tool]]` is built for `{}`",
            consumer.package
        );
    });
    // The proofs whose theorems the clean-proof-obligations tests re-check,
    // and the checker they judge with (a path prefix, not a directory).
    for (path, touched) in [
        ("proofs/codegen-equivalence/g16_bitvec_equivalence.lean", none.clone()),
        ("crates/trust-certify/src/clean_island_batch.rs", set(&["trust-certify"])),
    ] {
        let (now, _, active) = selected_for(&[path], &[]);
        assert_eq!((now, active), (touched, set(&["clean-proof-obligations"])), "{path}");
    }
}

/// The files of the tree under `prefix`, a directory written from the root
/// with a closing `/`, each written the same way: those git tracks, or
/// where the tree is no checkout, those a walk finds.
fn tree_files(root: &Path, prefix: &str) -> Vec<String> {
    assert!(
        prefix.ends_with('/') && root.join(prefix).is_dir(),
        "`{prefix}` is not a directory of the tree"
    );
    let mut files = Vec::new();
    if root.join(".git").exists() {
        let listed = std::process::Command::new("git")
            .arg("-C")
            .arg(root)
            .args(["ls-files", "-z", "--", prefix])
            .output()
            .expect("failed to run `git ls-files`");
        assert!(listed.status.success(), "`git ls-files` failed: {listed:?}");
        let listed = String::from_utf8(listed.stdout).expect("a tracked path is not UTF-8");
        files.extend(listed.split_terminator('\0').map(str::to_owned));
        // A gitlink or a symlink is no file of the tree, and a file deleted
        // in the worktree is not there to read.
        files.retain(|file| {
            std::fs::symlink_metadata(root.join(file)).is_ok_and(|found| found.is_file())
        });
    } else {
        walk(root, prefix.trim_end_matches('/'), &mut files);
    }
    files.sort();
    files
}

/// Every regular file under `root/directory`, written from `root`. A
/// symlink is not followed, and neither a directory git would not list
/// (`.name`) nor one a build wrote (it holds a `CACHEDIR.TAG`) is entered.
/// A source directory is entered whatever its name: `src/target_spec/` is
/// no build directory.
fn walk(root: &Path, directory: &str, found: &mut Vec<String>) {
    let Ok(entries) = std::fs::read_dir(root.join(directory)) else {
        return;
    };
    for entry in entries.flatten() {
        let Ok(kind) = entry.file_type() else {
            continue;
        };
        let name = entry.file_name();
        let name = name.to_str().expect("a file name is not UTF-8");
        let path = format!("{directory}/{name}");
        if kind.is_file() {
            found.push(path);
        } else if kind.is_dir()
            && !name.starts_with('.')
            && !entry.path().join("CACHEDIR.TAG").exists()
        {
            walk(root, &path, found);
        }
    }
}

/// The files of `files` (from `root`) that hold the text `needle`.
fn holding<'a>(root: &Path, files: &'a [String], needle: &str) -> Vec<&'a str> {
    let finder = memchr::memmem::Finder::new(needle);
    files
        .iter()
        .filter(|file| {
            std::fs::read(root.join(file)).is_ok_and(|bytes| finder.find(&bytes).is_some())
        })
        .map(String::as_str)
        .collect()
}

/// `attribute-under` refuses a changed path the plan cannot account for.
/// Every file there is must therefore have an owner the plan names: a
/// member, an `elsewhere` member, a `[[workspace]]` or a `[[tool]]`. One that
/// has none would stop every run a change to it reaches.
#[test]
fn every_file_under_an_attributed_directory_has_an_owner_the_plan_names() {
    let root = repository();
    let mut prefixes = Vec::new();
    with_plan(|_, _, plan| prefixes.clone_from(&plan.plan.select.attribute_under));
    assert!(!prefixes.is_empty());
    let files: Vec<String> = prefixes
        .iter()
        .flat_map(|prefix| tree_files(&root, prefix))
        .collect();
    assert!(!files.is_empty());
    let input = Input {
        changed_paths: Some(files),
        ..Input::default()
    };
    with_plan_for(input, |_, _, plan| {
        // One line per reason, with how many paths and the first of them.
        let mut reasons = BTreeMap::<&str, (usize, &str)>::new();
        for unattributed in &plan.selection.unattributed {
            reasons
                .entry(unattributed.why.as_str())
                .or_insert((0, unattributed.path.as_str()))
                .0 += 1;
        }
        assert!(
            reasons.is_empty(),
            "`{PLAN}` refuses a change to files of the tree; give each owner a \
             `select.elsewhere` row naming the command that tests it, or make it a member: \
             {reasons:#?}"
        );
    });
}

#[test]
fn every_variant_names_features_and_targets_its_package_has() {
    with_plan(|_, ws, plan| {
        assert!(!plan.plan.variant.is_empty());
        for run in &plan.plan.variant {
            let what = format!("variant `{}`", run.id);
            let package = member(ws, &run.package);
            // A variant without a feature is the default run again.
            assert!(!run.features.is_empty(), "{what} names no feature");
            let features = package.summary().features();
            for feature in &run.features {
                assert!(
                    features.contains_key(feature.as_str()),
                    "{what}: package `{}` defines no feature `{feature}`",
                    run.package
                );
            }
            require_targets(&what, package, run.lib, &run.test);
            // A named integration target must be one its features build.
            for test in &run.test {
                let target: &Target = package
                    .targets()
                    .iter()
                    .find(|target| target.is_test() && target.name() == test)
                    .unwrap();
                for required in target.required_features().into_iter().flatten() {
                    assert!(
                        run.features.contains(required)
                            || features
                                .get("default")
                                .is_some_and(|on| on.iter().any(|f| f.to_string() == *required)),
                        "{what}: test target `{test}` requires feature `{required}`, which \
                         the variant does not name"
                    );
                }
            }
        }
    });
}

#[test]
fn every_instrument_selects_tests_that_exist_and_watches_paths_that_exist() {
    with_plan(|root, ws, plan| {
        assert!(!plan.plan.instrument.is_empty());
        for run in &plan.plan.instrument {
            let what = format!("instrument `{}`", run.id);
            let package = member(ws, &run.package);
            require_targets(&what, package, run.lib, &run.test);
            for test in &run.test {
                let target = package
                    .targets()
                    .iter()
                    .find(|target| target.is_test() && target.name() == test)
                    .unwrap();
                let source = read(target.src_path().path().unwrap());
                assert!(
                    source.contains("#[test]"),
                    "{what}: test target `{test}` holds no `#[test]`"
                );
            }
            // A filter that matches nothing runs zero tests. Each names a
            // module path of the lib, written `<file>::<module>::`.
            for filter in filters(&run.args) {
                assert!(run.lib, "{what}: a filter is held to the lib's modules");
                let path = filter.strip_suffix("::").unwrap_or_else(|| {
                    panic!("{what}: filter `{filter}` is not a module path ending in `::`")
                });
                let modules: Vec<&str> = path.split("::").collect();
                assert!(
                    module_text(&what, package, &modules).contains("#[test]"),
                    "{what}: filter `{filter}` selects no `#[test]`"
                );
            }
            // A required test is a `#[test]` that runs by default, under
            // one of the instrument's filters.
            for required in &run.require_pass {
                assert!(
                    filters(&run.args)
                        .iter()
                        .any(|filter| required.contains(filter)),
                    "{what}: no filter of its `args` selects `{required}`"
                );
                let (modules, function) = required.rsplit_once("::").unwrap_or_else(|| {
                    panic!("{what}: `require-pass` `{required}` names no module")
                });
                let modules: Vec<&str> = modules.split("::").collect();
                let text = module_text(&what, package, &modules);
                let at = text
                    .find(&format!("fn {function}()"))
                    .unwrap_or_else(|| panic!("{what}: `require-pass` test `{required}` is gone"));
                // Its attributes: what stands between the item before it
                // and the function.
                let attributes = text[..at].rsplit('}').next().unwrap();
                assert!(
                    attributes.contains("#[test]"),
                    "{what}: `{required}` is not a `#[test]`"
                );
                // Any `ignore`: `#[cfg_attr(debug_assertions, ignore)]`
                // skips it as silently as `#[ignore]`.
                assert!(
                    !attributes.contains("ignore"),
                    "{what}: `{required}` must run by default, and is ignored"
                );
            }
            // A prefix ending in `/` is a directory; any other is the
            // start of a name in its directory.
            for prefix in &run.when_changed {
                let exists = if prefix.ends_with('/') {
                    root.join(prefix).is_dir()
                } else {
                    let path = root.join(prefix);
                    let start = path.file_name().unwrap().to_str().unwrap().to_owned();
                    std::fs::read_dir(path.parent().unwrap()).is_ok_and(|entries| {
                        entries
                            .flatten()
                            .any(|entry| entry.file_name().to_string_lossy().starts_with(&start))
                    })
                };
                assert!(
                    exists,
                    "{what}: `when-changed` `{prefix}` names nothing in the tree"
                );
            }
            for prefix in &run.not_under {
                assert!(
                    prefix.ends_with('/') && root.join(prefix).is_dir(),
                    "{what}: `not-under` `{prefix}` is not a directory of the tree"
                );
            }
            assert!(
                !run.when_changed.is_empty() || run.when_changed_suffix.is_some(),
                "{what} names no path that selects it"
            );
        }
    });
}

/// An instrument selected by a path suffix judges every checked-in document
/// of one format, which its host pins in `tests/corpus_manifest.txt`.
#[test]
fn a_corpus_instrument_names_every_test_target_that_reads_the_corpus_manifest() {
    with_plan(|_, ws, plan| {
        let corpora: Vec<&Instrument> = plan
            .plan
            .instrument
            .iter()
            .filter(|run| run.when_changed_suffix.is_some())
            .collect();
        assert!(!corpora.is_empty());
        for run in corpora {
            let what = format!("instrument `{}`", run.id);
            let suffix = run.when_changed_suffix.as_deref().unwrap();
            let package = member(ws, &run.package);
            let sources: BTreeMap<&str, String> = package
                .targets()
                .iter()
                .filter(|target| target.is_test())
                .map(|target| (target.name(), read(target.src_path().path().unwrap())))
                .collect();
            let readers: BTreeSet<&str> = sources
                .iter()
                .filter(|(_, source)| source.contains("corpus_manifest.txt"))
                .map(|(name, _)| *name)
                .collect();
            let named: BTreeSet<&str> = run.test.iter().map(String::as_str).collect();
            assert!(
                !readers.is_empty(),
                "{what}: no test target reads the manifest"
            );
            assert_eq!(
                named, readers,
                "{what}: `test` must name every reader of the manifest"
            );
            // The suffix and the exclusions are the ones the host's own
            // rule spells.
            let rules = || named.iter().map(|name| &sources[name]);
            assert!(
                rules().any(|rule| rule.contains(&format!("\"*{suffix}\""))),
                "{what}: no reader lists `*{suffix}`"
            );
            for prefix in &run.not_under {
                assert!(
                    rules().any(|rule| rule.contains(&format!("\"{prefix}\""))),
                    "{what}: no reader excludes `{prefix}`"
                );
            }
            // An integration-test build would rebuild a bin of the host
            // beside the default run's.
            assert!(
                !package.targets().iter().any(Target::is_bin),
                "{what}: its host `{}` has a bin target",
                run.package
            );
        }
    });
}

/// The search `TRUST_TARGO_TRUST_BIN` replaced: a test that looked for the
/// binary in build directories ran whichever copy it found.
const RETIRED_TOOL_SEARCH: &str = "find_targo_trust_binary";

#[test]
fn every_tool_is_a_bin_of_its_manifest_and_every_reader_of_its_variable_is_named() {
    with_plan(|root, ws, plan| {
        assert!(!plan.plan.tool.is_empty());
        // Every file, not only Rust sources: a script or a fixture a test
        // runs reads the variable as a test does.
        let files = tree_files(root, "crates/");
        // A file belongs to the member whose directory is its longest
        // prefix; one of no member, to itself.
        let mut members: Vec<(&Path, &str)> = ws
            .members()
            .map(|package| (package.root(), package.name().as_str()))
            .collect();
        members.sort_by_key(|(directory, _)| std::cmp::Reverse(directory.as_os_str().len()));
        for tool in &plan.plan.tool {
            let what = format!("`[[tool]]` `{}`", tool.manifest);
            let own = Workspace::new(&root.join(&tool.manifest), ws.gctx())
                .unwrap_or_else(|error| panic!("{what} does not load: {error:?}"));
            let package = own
                .current()
                .unwrap_or_else(|error| panic!("{what} is no package: {error:?}"));
            assert!(
                package
                    .targets()
                    .iter()
                    .any(|target| target.is_bin() && target.name() == tool.bin),
                "{what}: its package `{}` has no bin target `{}`",
                package.name(),
                tool.bin
            );
            // A member whose tests read the variable and is not named
            // gets no build, and fails wherever it is tested.
            let readers: BTreeSet<String> = holding(root, &files, &tool.env)
                .into_iter()
                .map(|file| {
                    let path = root.join(file);
                    members
                        .iter()
                        .find(|(directory, _)| path.starts_with(directory))
                        .map_or_else(|| file.to_owned(), |(_, name)| (*name).to_owned())
                })
                .collect();
            let named: BTreeSet<String> = tool.needed_by.iter().cloned().collect();
            assert_eq!(
                named, readers,
                "{what}: `needed-by` must name exactly the members whose files read `{}`",
                tool.env
            );
        }
        // Gone, not merely unused.
        assert_eq!(
            holding(root, &files, RETIRED_TOOL_SEARCH),
            [""; 0],
            "`{RETIRED_TOOL_SEARCH}` is back: a tool is named to a test by the plan's `env`"
        );
    });
}

/// The crate-level `#![cfg(target_os = "..")]` of the library source `text`,
/// as the plan's `cfg` would spell it. What follows the attribute on its
/// line (a comment saying why) does not hide it.
fn os_cfg(text: &str) -> Option<String> {
    text.lines().find_map(|line| {
        let (os, rest) = line
            .strip_prefix("#![cfg(target_os")?
            .trim_start()
            .strip_prefix('=')?
            .trim_start()
            .strip_prefix('"')?
            .split_once('"')?;
        rest.starts_with(")]")
            .then(|| format!("target_os = \"{os}\""))
    })
}

/// [`os_cfg`] of the library in `directory`.
fn library_cfg(directory: &Path) -> Option<String> {
    os_cfg(&std::fs::read_to_string(directory.join("src/lib.rs")).ok()?)
}

#[test]
fn the_workspaces_are_exactly_the_crates_that_are_their_own_and_gated_as_their_libraries() {
    with_plan(|root, ws, plan| {
        // `crates/<dir>` one level deep whose manifest has its own
        // `[workspace]` line. One nested deeper is its parent's data.
        let mut own = BTreeMap::new();
        for entry in std::fs::read_dir(root.join("crates")).unwrap().flatten() {
            let directory = entry.path();
            let Ok(manifest) = std::fs::read_to_string(directory.join("Cargo.toml")) else {
                continue;
            };
            if manifest.lines().any(|line| line.trim() == "[workspace]") {
                own.insert(
                    format!("crates/{}/Cargo.toml", entry.file_name().to_string_lossy()),
                    library_cfg(&directory),
                );
            }
        }
        let listed: BTreeMap<String, Option<String>> = plan
            .plan
            .workspace
            .iter()
            .map(|own| (own.manifest.clone(), own.cfg.clone()))
            .collect();
        assert!(!own.is_empty());
        assert_eq!(
            listed, own,
            "`[[workspace]]` must list every own-workspace crate under `crates/`, each with \
             the `cfg` its library is compiled under"
        );
        // A member's tests are in the one graph and cannot be gated: one
        // whose library another host compiles out could only fail here.
        for package in ws.default_members() {
            if plan
                .plan
                .select
                .elsewhere
                .contains_key(package.name().as_str())
            {
                continue;
            }
            assert_eq!(
                library_cfg(package.root()),
                None,
                "plan member `{}` is compiled for one OS only; the plan cannot gate a member",
                package.name()
            );
        }
    });
}

#[test]
fn every_known_red_row_names_a_test_binary_the_plan_runs() {
    with_plan(|_, ws, plan| {
        let known = plan
            .known_red
            .as_ref()
            .expect("the plan names a known-red file");
        // What a run of the plan can test: every tested target of a
        // member, and of an instrument's host the targets it names. A
        // `[[workspace]]` phase is not judged by the file, and a workspace
        // member the plan does not test (a compiler or tool crate) runs
        // nothing a row could be read against.
        let elsewhere = &plan.plan.select.elsewhere;
        let mut carried = BTreeSet::new();
        for package in ws.default_members() {
            if elsewhere.contains_key(package.name().as_str()) {
                continue;
            }
            carried.extend(
                package
                    .targets()
                    .iter()
                    .filter(|target| target.tested())
                    .map(Target::crate_name),
            );
        }
        for run in &plan.plan.instrument {
            carried.extend(
                member(ws, &run.package)
                    .targets()
                    .iter()
                    .filter(|target| {
                        (run.lib && target.is_lib())
                            || (target.is_test()
                                && run.test.iter().any(|test| test == target.name()))
                    })
                    .map(Target::crate_name),
            );
        }
        for binary in known.binaries() {
            assert!(
                carried.contains(binary),
                "`{}`: a row names the test binary `{binary}`, which no target the plan \
                 tests carries; the row can never be judged",
                known.file
            );
        }
    });
}

#[test]
fn a_module_ends_where_its_block_does() {
    let text = r##"
mod first {
    // an unmatched } in a comment, and /* one { in /* a nested */ one */
    const OPEN: &str = "{";
    const RAW: &str = r#"}"} "#;
    const QUOTE: char = '\'';
    const BRACE: char = '}';
    fn borrowed<'a>(text: &'a str) -> &'a str { text }
    fn early() {}
}
mod second {
    #[test]
    fn late() {}
}
"##;
    let first = inline_module(text, "first").unwrap();
    assert!(first.contains("fn early() {}"), "{first}");
    assert!(!first.contains("fn late()"), "{first}");
    assert!(!first.contains("#[test]"), "{first}");
    let second = inline_module(text, "second").unwrap();
    assert!(second.contains("#[test]") && second.contains("fn late() {}"));
    assert_eq!(inline_module(text, "third"), None);
    // A block that never closes is no module.
    assert_eq!(inline_module("mod open { fn f() {}", "open"), None);
}

#[test]
fn the_value_of_an_option_is_no_filter() {
    let args = |args: &[&str]| args.iter().map(|arg| (*arg).to_owned()).collect::<Vec<_>>();
    assert_eq!(
        filters(&args(&["--skip", "tests::digest::", "tests::other::"])),
        ["tests::other::"]
    );
    assert_eq!(filters(&args(&["--skip", "tests::digest::"])), [""; 0]);
    assert_eq!(
        filters(&args(&["--ignored", "tests::digest::", "--skip=x"])),
        ["tests::digest::"]
    );
}

#[test]
fn a_walk_enters_every_source_directory_and_no_build_directory() {
    let tree = tempfile::tempdir().unwrap();
    let write = |path: &str| {
        let path = tree.path().join(path);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, "TRUST_TARGO_TRUST_BIN").unwrap();
    };
    write("crates/m/src/ok/a.rs");
    write("crates/m/src/target_spec/reader.rs");
    write("crates/m/src/targets/reader.rs");
    write("crates/m/src/target/reader.rs");
    write("crates/m/tests/probe.sh");
    write("crates/m/target/CACHEDIR.TAG");
    write("crates/m/target/debug/built.rs");
    write("crates/m/.cache/hidden.rs");
    write("other/elsewhere.rs");
    let files = tree_files(tree.path(), "crates/");
    assert_eq!(
        files,
        [
            "crates/m/src/ok/a.rs",
            "crates/m/src/target/reader.rs",
            "crates/m/src/target_spec/reader.rs",
            "crates/m/src/targets/reader.rs",
            "crates/m/tests/probe.sh",
        ]
    );
    assert_eq!(
        holding(tree.path(), &files, "TRUST_TARGO_TRUST_BIN").len(),
        5
    );
    assert_eq!(
        holding(tree.path(), &files, "TRUST_TARGO_TRUST_BINARY"),
        [""; 0]
    );
}

#[test]
fn a_library_cfg_is_read_whatever_follows_it_on_its_line() {
    let linux = Some("target_os = \"linux\"".to_owned());
    assert_eq!(os_cfg("//! Doc.\n#![cfg(target_os = \"linux\")]\n"), linux);
    assert_eq!(os_cfg("#![cfg(target_os = \"linux\")] // why\n"), linux);
    assert_eq!(os_cfg("#![cfg(target_os=\"linux\")]"), linux);
    // Not the crate's own gate: an item's, or one of several conditions.
    assert_eq!(os_cfg("#[cfg(target_os = \"linux\")]\nmod sys;"), None);
    assert_eq!(os_cfg("    #![cfg(target_os = \"linux\")]"), None);
    assert_eq!(os_cfg("#![cfg(target_os = \"linux\", unix)]"), None);
    assert_eq!(os_cfg("#![cfg(unix)]"), None);
}

// Tests for crate::stability: the command line, the checkouts and version
// bump, the load generator's stop, the judgements, and whole runs of the verb
// over a stand-in leg runner that writes the records a check writes, through
// the check's own writer.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use trust_types::determinism::{BudgetProfile, NotedStop, StopCause, UnitOutcome};
use trust_types::obligation_identity::{ObligationIdentity, function_source_digest, local_id};

use super::closure::{ClosurePackage, PathClosure, copy_closure, path_closure};
use super::judge::{
    AxisVerdict, ControlVerdict, KeyChange, Standing, UnitVerdict, Verdict, exit_status,
    judge_axis, judge_control,
};
use super::legs::{
    LegExit, LegRunner, LegSpec, LoadGenerator, ancestor_cargo_configs, bump_in_lock, bump_patch,
    bump_versions, copy_tree, leg_spec, set_trust_key,
};
use super::*;
use crate::obligations::{FunctionInventory, ObligationRecords, RunFacts, RunScope};
use crate::package_record::RunCoverage;
use crate::types::{StructuredTransportEvidence, VerificationOutcome, VerificationResult};

fn strings(args: &[&str]) -> Vec<String> {
    args.iter().map(ToString::to_string).collect()
}

fn parsed(args: &[&str]) -> StabilityArgs {
    match parse_args(&strings(args)) {
        Ok(Parsed::Run(args)) => args,
        other => panic!("{args:?}: {other:?}"),
    }
}

fn refused(args: &[&str]) -> String {
    match parse_args(&strings(args)) {
        Err(error) => error,
        other => panic!("{args:?} was accepted: {other:?}"),
    }
}

#[test]
fn the_default_is_the_plans_axes_this_host_can_run_and_host_comes_with_records() {
    let args = parsed(&["--lib", "--allow-l0-gaps"]);
    assert_eq!(
        args.axes,
        BTreeSet::from([
            Axis::Repetition,
            Axis::Parallelism,
            Axis::Path,
            Axis::Version,
            Axis::Load
        ]),
        "§3.8's axes; `effort` (not among them, failing until BUDGET-1 closes) only when asked for"
    );
    assert_eq!(args.check_args, strings(&["--lib", "--allow-l0-gaps"]));
    assert_eq!(args.format, Format::Terminal);
    assert!(!args.keep && args.scratch.is_none());

    let args = parsed(&["--against=other/target", "--json", "-p", "demo"]);
    assert!(args.axes.contains(&Axis::Host) && args.axes.len() == 6, "{:?}", args.axes);
    assert_eq!(args.against, Some(PathBuf::from("other/target")));
    assert_eq!(args.format, Format::Json);
    assert_eq!(args.check_args, strings(&["-p", "demo"]));

    let args = parsed(&[
        "--axes=repetition,path",
        "--keep",
        "--scratch",
        "/s",
        "--format",
        "json",
        "--",
        "--axes",
    ]);
    assert_eq!(args.axes, BTreeSet::from([Axis::Repetition, Axis::Path]));
    assert!(args.keep);
    assert_eq!(args.scratch, Some(PathBuf::from("/s")));
    assert_eq!(args.check_args, strings(&["--", "--axes"]), "after `--`, nothing is the verb's");
    assert_eq!(parse_args(&strings(&["--help"])), Ok(Parsed::Help));
    assert!(parsed(&["--axes", "effort"]).axes == BTreeSet::from([Axis::Effort]));
}

#[test]
fn what_the_verb_owns_or_a_leg_cannot_honour_is_refused_by_name() {
    assert!(refused(&["--axes", "repetition,bogus"]).contains("unknown axis `bogus`"));
    assert!(refused(&["--axes", "host"]).contains("--against"));
    assert!(refused(&["--axes", "path", "--against", "x"]).contains("add `host` to --axes"));
    assert!(refused(&["--against", "x", "--against", "y"]).contains("twice"));
    assert!(refused(&["--format", "html"]).contains("terminal or json"));
    assert!(refused(&["--axes"]).contains("--axes requires a value"));
    for (args, named) in [
        (&["--manifest-path", "Cargo.toml"][..], "--manifest-path"),
        (&["--worker-threads", "2"], "--worker-threads"),
        (&["-j", "4"], "-j/--jobs"),
        (&["-j4"], "-j/--jobs"),
        (&["--jobs=4"], "-j/--jobs"),
        (&["--target-dir", "t"], "--target-dir"),
        (&["--config", "build.jobs=4"], "build.jobs"),
        (&["--config=build.jobs = 2"], "build.jobs"),
        (&["--config", "build.target-dir=\"t\""], "build.target-dir"),
        (&["--report-dir", "r"], "--report-dir"),
        (&["--save-baseline", "b"], "--save-baseline"),
        (&["--baseline", "b"], "--baseline"),
        (&["--rewrite"], "--rewrite"),
        (&["--standalone"], "--standalone"),
        (&["lib.rs"], "single-file"),
    ] {
        let error = refused(args);
        assert!(error.contains(named) && error.contains("refused"), "{args:?}: {error}");
    }
    // The check's own parser refuses what the check refuses.
    assert!(refused(&["--memory-safe", "--allow-l0-gaps"]).starts_with("check options:"));
    // Other configuration passes; so does whatever follows `--`.
    assert_eq!(
        parsed(&["--config", "profile.dev.debug=0", "--", "--config", "build.jobs=1"]).check_args,
        strings(&["--config", "profile.dev.debug=0", "--", "--config", "build.jobs=1"])
    );
    // A --config file is read for what it sets.
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("jobs.toml");
    std::fs::write(&file, "[build]\njobs = 3\n").unwrap();
    let error = refused(&["--config", file.to_str().unwrap()]);
    assert!(error.contains("build.jobs") && error.contains("refused"), "{error}");
}

#[test]
fn every_run_has_the_control_and_each_axis_its_pair() {
    let legs = |axes: &[Axis]| legs_for(&axes.iter().copied().collect());
    assert_eq!(legs(&[Axis::Version]), BTreeSet::from([Leg::Control, Leg::Moved, Leg::Bumped]));
    assert_eq!(legs(&[Axis::Host]), BTreeSet::from([Leg::Control, Leg::Base]));
    assert_eq!(
        legs(&[Axis::Effort, Axis::Repetition]),
        BTreeSet::from([Leg::Control, Leg::Base, Leg::Repeat, Leg::Effort, Leg::EffortLoaded])
    );
    // Run order: the control first; `bumped` after the `moved` leg whose copy
    // it bumps.
    let all = legs(&Axis::ALL);
    assert_eq!(all.first(), Some(&Leg::Control));
    assert!(Leg::Moved < Leg::Bumped);
}

#[test]
fn the_serial_leg_carries_one_worker_thread_and_one_job_and_the_others_the_defaults() {
    let dir = Path::new("/scratch/legs/x");
    let args = strings(&["--lib", "--", "--nocapture"]);
    let serial = leg_spec(Leg::Serial, PathBuf::from("/w"), dir, &args);
    assert_eq!(serial.args, strings(&["--lib", "--worker-threads", "1", "--", "--nocapture"]));
    assert_eq!(serial.env, [("CARGO_BUILD_JOBS".to_string(), Some("1".to_string()))]);
    assert_eq!(serial.target_dir, dir.join("target"));
    let base = leg_spec(Leg::Base, PathBuf::from("/w"), dir, &args);
    assert_eq!(base.args, args);
    assert_eq!(base.env, [("CARGO_BUILD_JOBS".to_string(), None)]);
}

#[test]
fn a_patch_bump_is_the_smallest_version_change() {
    assert_eq!(bump_patch("0.1.0").as_deref(), Some("0.1.1"));
    assert_eq!(bump_patch("1.2.9").as_deref(), Some("1.2.10"));
    assert_eq!(bump_patch("0.3.0-alpha.1").as_deref(), Some("0.3.1-alpha.1"));
    assert_eq!(bump_patch("2.0.0+meta.7").as_deref(), Some("2.0.1+meta.7"));
    for bad in ["1.2", "1.2.3.4", "1..3", "a.b.c", "", "1.2.x"] {
        assert_eq!(bump_patch(bad), None, "{bad}");
    }
}

fn write(path: &Path, text: &str) {
    std::fs::create_dir_all(path.parent().expect("a parent")).expect("mkdir");
    std::fs::write(path, text).expect("write");
}

fn read_toml(path: &Path) -> toml::Table {
    std::fs::read_to_string(path).expect("read").parse().expect("toml")
}

fn names(packages: &[&str]) -> BTreeSet<String> {
    packages.iter().map(ToString::to_string).collect()
}

/// A two-member workspace with a vendored crate, a fixture crate, build
/// output and git state, and the `Cargo.lock` Cargo writes for it.
fn bump_fixture(root: &Path) {
    write(
        &root.join("Cargo.toml"),
        "[workspace]\nmembers = [\"a\", \"b\"]\n\n[workspace.package]\nversion = \"0.4.0\"\n",
    );
    write(
        &root.join("a/Cargo.toml"),
        concat!(
            "[package]\nname = \"a\"\nversion.workspace = true\n\n",
            "[dependencies]\nb = { path = \"../b\" }\n",
        ),
    );
    write(&root.join("b/Cargo.toml"), "[package]\nname = \"b\"\nversion = \"1.0.7\"\n# kept\n");
    write(&root.join("vendor/v/Cargo.toml"), "[package]\nname = \"v\"\nversion = \"2.0.0\"\n");
    write(&root.join("vendor/v/.cargo-checksum.json"), "{}\n");
    write(
        &root.join("tests/fixtures/f/Cargo.toml"),
        "[package]\nname = \"f\"\nversion = \"3.0.0\"\n",
    );
    write(&root.join("tests/fixtures/broken/Cargo.toml"), "[package\n");
    write(&root.join("target/CACHEDIR.TAG"), "Signature: 8a477f597d28d172789f06886806bc55\n");
    write(
        &root.join("target/package/b/Cargo.toml"),
        "[package]\nname = \"b\"\nversion = \"9.9.9\"\n",
    );
    write(&root.join(".git/x/Cargo.toml"), "[package]\nname = \"b\"\nversion = \"9.9.9\"\n");
    write(&root.join("Cargo.lock"), LOCK);
}

/// A lock file as Cargo writes it: two path members (one depending on the
/// other) and a registry package of the same name as a member.
const LOCK: &str = "\
# This file is automatically @generated by Cargo.
# It is not intended for manual editing.
version = 4

[[package]]
name = \"a\"
version = \"0.4.0\"
dependencies = [
 \"b 1.0.7\",
 \"b 1.0.7 (registry+https://github.com/rust-lang/crates.io-index)\",
]

[[package]]
name = \"b\"
version = \"1.0.7\"

[[package]]
name = \"b\"
version = \"1.0.7\"
source = \"registry+https://github.com/rust-lang/crates.io-index\"
checksum = \"0000000000000000000000000000000000000000000000000000000000000000\"
";

#[test]
fn the_version_bump_moves_each_recorded_package_its_lock_entry_and_nothing_else() {
    let root = tempfile::tempdir().expect("tempdir");
    let root = root.path();
    bump_fixture(root);

    let closure = path_closure(root).expect("a closure");
    let changed = bump_versions(root, &closure, &names(&["a", "b"])).expect("bumped");
    let summary: Vec<(String, String, String)> = changed
        .iter()
        .map(|(path, old, new)| {
            (path.strip_prefix(root).unwrap().display().to_string(), old.clone(), new.clone())
        })
        .collect();
    let row =
        |file: &str, old: &str, new: &str| (file.to_string(), old.to_string(), new.to_string());
    assert_eq!(
        summary,
        [
            row("Cargo.toml", "0.4.0", "0.4.1"),
            row("b/Cargo.toml", "1.0.7", "1.0.8"),
            row("Cargo.lock", "a 0.4.0", "a 0.4.1"),
            row("Cargo.lock", "b 1.0.7", "b 1.0.8"),
        ]
    );
    assert_eq!(
        read_toml(&root.join("Cargo.toml"))["workspace"]["package"]["version"].as_str(),
        Some("0.4.1")
    );
    let a = read_toml(&root.join("a/Cargo.toml"));
    assert_eq!(a["package"]["version"]["workspace"].as_bool(), Some(true), "inherited, untouched");
    assert_eq!(
        a["dependencies"]["b"]["path"].as_str(),
        Some("../b"),
        "the rest of a manifest stays"
    );
    assert_eq!(
        std::fs::read_to_string(root.join("Cargo.lock")).unwrap(),
        LOCK.replace("version = \"0.4.0\"", "version = \"0.4.1\"")
            .replacen("\"b 1.0.7\",", "\"b 1.0.8\",", 1)
            .replacen(
                "name = \"b\"\nversion = \"1.0.7\"\n\n",
                "name = \"b\"\nversion = \"1.0.8\"\n\n",
                1
            ),
        "the path packages' lines move; the registry package of the same name does not"
    );
    for (untouched, version) in [
        ("vendor/v/Cargo.toml", "2.0.0"),
        ("tests/fixtures/f/Cargo.toml", "3.0.0"),
        ("target/package/b/Cargo.toml", "9.9.9"),
        (".git/x/Cargo.toml", "9.9.9"),
    ] {
        assert!(
            std::fs::read_to_string(root.join(untouched)).unwrap().contains(version),
            "{untouched}: a crate the legs did not record keeps its version"
        );
    }
}

#[test]
fn a_package_whose_version_cannot_move_fails_the_bump() {
    let root = tempfile::tempdir().expect("tempdir");
    let root = root.path();
    bump_fixture(root);
    // Versionless: Cargo reads 0.0.0, and nothing would move. Two packages
    // of one name the resolve reads, neither a member (`vendor` is excluded).
    write(
        &root.join("Cargo.toml"),
        "[workspace]\nmembers = [\"a\", \"b\", \"c\"]\nexclude = [\"vendor\"]\n\n\
         [workspace.package]\nversion = \"0.4.0\"\n",
    );
    write(&root.join("c/Cargo.toml"), "[package]\nname = \"c\"\n");
    write(
        &root.join("b/Cargo.toml"),
        "[package]\nname = \"b\"\nversion = \"1.0.7\"\n\n[dependencies]\n\
         d1 = { path = \"../vendor/d1\", package = \"dup\" }\n\
         d2 = { path = \"../vendor/d2\", package = \"dup\" }\n",
    );
    for (dir, version) in [("d1", "1.0.0"), ("d2", "2.0.0")] {
        write(
            &root.join(format!("vendor/{dir}/Cargo.toml")),
            &format!("[package]\nname = \"dup\"\nversion = \"{version}\"\n"),
        );
    }
    // A manifest the resolve does not read shares a recorded package's name.
    write(
        &root.join("tests/fixtures/b2/Cargo.toml"),
        "[package]\nname = \"b\"\nversion = \"1.0.0\"\n",
    );
    let closure = path_closure(root).expect("a closure");
    let error = bump_versions(root, &closure, &names(&["a", "c"])).unwrap_err();
    assert!(error.contains("`c`") && error.contains("declares no version"), "{error}");
    // No package of the closure has the name; two non-members have it.
    let error = bump_versions(root, &closure, &names(&["ghost"])).unwrap_err();
    assert!(error.contains("is named `ghost`"), "{error}");
    let error = bump_versions(root, &closure, &names(&["dup"])).unwrap_err();
    assert!(error.contains("2 packages") && error.contains("vendor/d2/Cargo.toml"), "{error}");
    assert!(
        bump_versions(root, &closure, &BTreeSet::new())
            .unwrap_err()
            .contains("recorded no package")
    );
    // The fixture of the same name is no package of the resolve.
    bump_versions(root, &closure, &names(&["b"])).expect("bumped");
    assert!(
        std::fs::read_to_string(root.join("tests/fixtures/b2/Cargo.toml"))
            .unwrap()
            .contains("1.0.0")
    );
}

// T4.7-17: a recorded name that a workspace member and a package outside the
// workspace share (crates/'s `sha2`) is the member, the package the legs
// build.
#[test]
fn a_recorded_name_two_packages_share_is_the_workspace_members() {
    let dir = tempfile::tempdir().expect("tempdir");
    let root = dir.path();
    write(&root.join("ws/Cargo.toml"), "[workspace]\nmembers = [\"compat\"]\n");
    write(
        &root.join("ws/compat/Cargo.toml"),
        "[package]\nname = \"sha2\"\nversion = \"0.10.0\"\n\n\
         [dependencies]\nother = { path = \"../../ty/sha2\", package = \"sha2\" }\n",
    );
    write(&root.join("ty/sha2/Cargo.toml"), "[package]\nname = \"sha2\"\nversion = \"0.9.0\"\n");
    let lock = "version = 4\n\n[[package]]\nname = \"sha2\"\nversion = \"0.9.0\"\n\n\
                [[package]]\nname = \"sha2\"\nversion = \"0.10.0\"\n";
    write(&root.join("ws/Cargo.lock"), lock);
    let closure = path_closure(&root.join("ws")).expect("a closure");
    bump_versions(root, &closure, &names(&["sha2"])).expect("bumped");
    assert_eq!(
        std::fs::read_to_string(root.join("ws/Cargo.lock")).unwrap(),
        lock.replace("0.10.0", "0.10.1")
    );
    assert!(std::fs::read_to_string(root.join("ty/sha2/Cargo.toml")).unwrap().contains("0.9.0"));
}

// T4.7-16: in a copy of a path closure the version axis edits the copy alone.
// A recorded package outside the workspace has its entry moved in the lock
// the legs resolve with (the workspace's); one whose version Cargo's search
// would take from a workspace root ABOVE the copy is refused, and that file
// is left as it was.
#[test]
fn the_version_bump_edits_the_copy_and_the_lock_its_legs_read_and_nothing_outside() {
    let dir = tempfile::tempdir().expect("tempdir");
    let copy = dir.path().join("copy");
    write(
        &copy.join("ws/Cargo.toml"),
        "[workspace]\nmembers = [\"a\"]\n\n[workspace.package]\nversion = \"0.4.0\"\n",
    );
    write(
        &copy.join("ws/a/Cargo.toml"),
        "[package]\nname = \"a\"\nversion.workspace = true\n\n\
         [dependencies]\ndep = { path = \"../../dep\" }\n",
    );
    write(&copy.join("dep/Cargo.toml"), "[package]\nname = \"dep\"\nversion = \"0.2.0\"\n");
    let lock = "version = 4\n\n[[package]]\nname = \"a\"\nversion = \"0.4.0\"\n\
                dependencies = [\n \"dep\",\n]\n\n[[package]]\nname = \"dep\"\nversion = \"0.2.0\"\n";
    write(&copy.join("ws/Cargo.lock"), lock);
    let closure = path_closure(&copy.join("ws")).expect("a closure");
    let changed = bump_versions(&copy, &closure, &names(&["dep"])).expect("bumped");
    assert_eq!(changed.len(), 2, "{changed:?}");
    assert_eq!(
        std::fs::read_to_string(copy.join("ws/Cargo.lock")).unwrap(),
        lock.replace("version = \"0.2.0\"", "version = \"0.2.1\""),
        "the workspace's lock, the one its legs resolve with"
    );

    // Above the copy, a workspace root the copy's own search would reach.
    let outer = dir.path().join("outer");
    let above = "[workspace]\n\n[workspace.package]\nversion = \"9.0.0\"\n";
    write(&outer.join("Cargo.toml"), above);
    let inner = outer.join("copy");
    write(
        &inner.join("orphan/Cargo.toml"),
        "[package]\nname = \"orphan\"\nversion.workspace = true\n",
    );
    let closure = PathClosure {
        root: inner.clone(),
        workspace: PathBuf::from("orphan"),
        trees: vec![PathBuf::from("orphan")],
        files: Vec::new(),
        packages: vec![ClosurePackage {
            name: "orphan".to_string(),
            manifest: PathBuf::from("orphan/Cargo.toml"),
            member: true,
        }],
        reached_through: Vec::new(),
    };
    let error = bump_versions(&inner, &closure, &names(&["orphan"])).unwrap_err();
    assert!(error.contains("outside the copy"), "{error}");
    assert_eq!(std::fs::read_to_string(outer.join("Cargo.toml")).unwrap(), above);
}

#[test]
fn a_lock_entry_moves_only_for_a_path_package_of_that_version() {
    let (text, found) = bump_in_lock(LOCK, "a", "0.4.0", "0.4.1");
    assert!(found);
    assert_eq!(text, LOCK.replace("version = \"0.4.0\"", "version = \"0.4.1\""));
    let (text, found) = bump_in_lock(LOCK, "a", "0.3.0", "0.3.1");
    assert!(!found);
    assert_eq!(text, LOCK, "another version is another package");
    let crlf = LOCK.replace('\n', "\r\n");
    let (text, found) = bump_in_lock(&crlf, "b", "1.0.7", "1.0.8");
    assert!(found);
    assert!(
        text.contains("version = \"1.0.8\"\r\n") && text.contains(" \"b 1.0.8\",\r\n"),
        "{text}"
    );
}

#[test]
fn a_moved_workspace_version_moves_the_lock_entry_of_every_member_that_inherits_it() {
    let root = tempfile::tempdir().expect("tempdir");
    let root = root.path();
    write(
        &root.join("Cargo.toml"),
        "[workspace]\nmembers = [\"a\", \"c\", \"d\"]\n\n[workspace.package]\nversion = \"0.4.0\"\n",
    );
    for member in ["a", "c"] {
        write(
            &root.join(format!("{member}/Cargo.toml")),
            &format!("[package]\nname = \"{member}\"\nversion.workspace = true\n"),
        );
    }
    write(&root.join("d/Cargo.toml"), "[package]\nname = \"d\"\nversion = \"0.4.0\"\n");
    let lock = "version = 4\n\n[[package]]\nname = \"a\"\nversion = \"0.4.0\"\n\n\
                [[package]]\nname = \"c\"\nversion = \"0.4.0\"\n\n\
                [[package]]\nname = \"d\"\nversion = \"0.4.0\"\n";
    write(&root.join("Cargo.lock"), lock);

    // Only `a` was recorded (`-p a`), but `c` inherits the version that moved.
    let closure = path_closure(root).expect("a closure");
    let changed = bump_versions(root, &closure, &names(&["a"])).expect("bumped");
    let files: Vec<(String, String)> = changed
        .iter()
        .map(|(path, old, _)| (path.strip_prefix(root).unwrap().display().to_string(), old.clone()))
        .collect();
    assert_eq!(
        files,
        [
            ("Cargo.toml".to_string(), "0.4.0".to_string()),
            ("Cargo.lock".to_string(), "a 0.4.0".to_string()),
            ("Cargo.lock".to_string(), "c 0.4.0".to_string()),
        ]
    );
    assert_eq!(
        std::fs::read_to_string(root.join("Cargo.lock")).unwrap(),
        lock.replacen("version = \"0.4.0\"", "version = \"0.4.1\"", 2),
        "`d` declares its own version, which did not move"
    );
}

#[test]
fn a_trust_key_joins_the_root_table_the_manifest_already_has() {
    let dir = tempfile::tempdir().expect("tempdir");
    let manifest = dir.path().join("Cargo.toml");
    write(
        &manifest,
        concat!(
            "[package]\nname = \"p\"\nversion = \"0.1.0\"\n\n",
            "[trust]\nlevel = \"L1\"\nbackstop = 2000\n",
        ),
    );
    set_trust_key(&manifest, "backstop", 1).expect("set");
    let table = read_toml(&manifest);
    assert_eq!(table["trust"]["backstop"].as_integer(), Some(1));
    assert_eq!(table["trust"]["level"].as_str(), Some("L1"));
    assert_eq!(table["package"]["name"].as_str(), Some("p"));

    write(&manifest, "[package]\nname = \"p\"\nversion = \"0.1.0\"\n");
    set_trust_key(&manifest, "effort", 1).expect("set");
    assert_eq!(read_toml(&manifest)["trust"]["effort"].as_integer(), Some(1));

    write(&manifest, "trust = 3\n");
    assert!(set_trust_key(&manifest, "effort", 1).unwrap_err().contains("not a table"));
}

#[test]
fn a_tree_copy_leaves_out_build_output_git_and_the_scratch() {
    let dir = tempfile::tempdir().expect("tempdir");
    let from = dir.path().join("ws");
    write(&from.join("Cargo.toml"), "[package]\nname = \"p\"\nversion = \"0.1.0\"\n");
    write(&from.join("src/lib.rs"), "pub fn f() {}\n");
    write(&from.join(".cargo/config.toml"), "[build]\n");
    write(&from.join("target/CACHEDIR.TAG"), "tag\n");
    write(&from.join("target/debug/x"), "built\n");
    write(&from.join("member/target/CACHEDIR.TAG"), "tag\n");
    write(&from.join("member/src/lib.rs"), "\n");
    write(&from.join(".git/HEAD"), "ref\n");
    write(&from.join("sub/.git"), "gitdir: elsewhere\n");
    write(&from.join("scratch/leftover"), "\n");
    #[cfg(unix)]
    std::os::unix::fs::symlink("src/lib.rs", from.join("link.rs")).expect("symlink");
    // An absolute link outside the tree a copy is made of reads the same file
    // from every copy, as a system file is.
    #[cfg(unix)]
    std::os::unix::fs::symlink(dir.path().join("system"), from.join("system")).expect("symlink");

    let to = dir.path().join("copies/ws");
    copy_tree(&from, &to, &[from.join("scratch").as_path()], &from).expect("copy");
    for kept in ["Cargo.toml", "src/lib.rs", ".cargo/config.toml", "member/src/lib.rs"] {
        assert!(to.join(kept).is_file(), "{kept}");
    }
    for left in ["target", "member/target", ".git", "sub/.git", "scratch"] {
        assert!(!to.join(left).exists(), "{left}");
    }
    #[cfg(unix)]
    assert_eq!(std::fs::read_link(to.join("link.rs")).expect("a symlink"), Path::new("src/lib.rs"));

    // An absolute link into the tree would read the original from every copy.
    #[cfg(unix)]
    {
        let canonical = from.canonicalize().unwrap();
        std::os::unix::fs::symlink(canonical.join("src/lib.rs"), from.join("abs.rs")).unwrap();
        let error = copy_tree(&from, &dir.path().join("copies/2"), &[], &from).unwrap_err();
        assert_eq!(error.kind(), std::io::ErrorKind::InvalidInput);
        assert!(error.to_string().contains("abs.rs` is a symlink to the absolute path"), "{error}");
    }
}

/// Every file under `dir` (but `.git` and build output), with its bytes.
fn tree_bytes(dir: &Path) -> BTreeMap<PathBuf, Vec<u8>> {
    let mut files = BTreeMap::new();
    let mut pending = vec![dir.to_path_buf()];
    while let Some(next) = pending.pop() {
        for entry in std::fs::read_dir(&next).expect("read_dir") {
            let path = entry.expect("entry").path();
            if path.is_dir() {
                pending.push(path);
            } else {
                let bytes = std::fs::read(&path).expect("read");
                files.insert(path.strip_prefix(dir).unwrap().to_path_buf(), bytes);
            }
        }
    }
    files
}

/// A workspace at `<dir>/repo/ws` that reads outside its root by every route
/// Cargo takes, and what it must not carry:
/// * members by glob (`m*`), one of them excluded (`m-skipped`), whose own
///   path dependency (`libs/never`) is therefore read by nothing;
/// * a direct path dependency (`libs/direct`), and ITS path dependency
///   (`libs/nested`), which inherits its version from `libs/Cargo.toml`;
/// * a `workspace = true` dependency through `[workspace.dependencies]`
///   (`libs/shared`), beside a workspace dependency nothing inherits
///   (`libs/unused`);
/// * the root package's own `workspace = true` dependency through its own
///   `[workspace.dependencies]` (`libs/own`), which no other member inherits;
/// * a target-specific build dependency (`libs/bdep`), and a dev dependency
///   that names nothing (`libs/gone`);
/// * a dev dependency inside the workspace's directory (`ws/helper`, so a
///   member though no `members` entry names it), whose own dev dependency
///   (`libs/htool`) is therefore read;
/// * a path dependency that is its own workspace root (`libs/direct`), which
///   inherits a dependency outside its directory (`far`) through its own
///   `[workspace.dependencies]`, and whose dev dependencies, those of a
///   package outside the workspace, the resolve never reads (`libs/devonly`,
///   and an absolute `/opt/tool` that is therefore not refused);
/// * a `[patch]` entry (`patches/patched`), read whether or not it is used;
/// * build output and git state inside the trees, a `.cargo/config.toml`, a
///   `rust-toolchain.toml` and a `Cargo.toml` above the workspace, and a
///   sibling (`unrelated`) the resolve never reads.
fn closure_fixture(dir: &Path) -> PathBuf {
    let repo = dir.join("repo");
    let package = |name: &str| format!("[package]\nname = \"{name}\"\nversion = \"0.1.0\"\n");
    write(&repo.join("Cargo.toml"), "[workspace]\nmembers = []\nexclude = [\"ws\", \"libs\"]\n");
    write(&repo.join(".cargo/config.toml"), "[build]\njobs = 4\n");
    write(&repo.join("rust-toolchain.toml"), "[toolchain]\nchannel = \"trust\"\n");
    write(
        &repo.join("ws/Cargo.toml"),
        &format!(
            "{}\n[dependencies]\ndirect = {{ path = \"../libs/direct\" }}\n\
             own = {{ workspace = true }}\n\n\
             [workspace]\nmembers = [\"m*\"]\nexclude = [\"m-skipped\"]\n\n\
             [workspace.dependencies]\nshared = {{ path = \"../libs/shared\" }}\n\
             unused = {{ path = \"../libs/unused\" }}\nown = {{ path = \"../libs/own\" }}\n\n\
             [patch.crates-io]\npatched = {{ path = \"../patches/patched\" }}\n",
            package("root-pkg")
        ),
    );
    write(&repo.join("ws/src/lib.rs"), "pub fn f() {}\n");
    write(&repo.join("ws/Cargo.lock"), "version = 4\n");
    write(&repo.join("ws/target/CACHEDIR.TAG"), "Signature: 8a477f597d28d172789f06886806bc55\n");
    write(&repo.join("ws/target/debug/out"), "built\n");
    write(
        &repo.join("ws/m1/Cargo.toml"),
        &format!(
            "{}\n[dependencies]\nshared = {{ workspace = true }}\n\n\
             [dev-dependencies]\ngone = {{ path = \"../../libs/gone\" }}\n\
             helper = {{ path = \"../helper\" }}\n\n\
             [target.'cfg(unix)'.build-dependencies]\nbdep = {{ path = \"../../libs/bdep\" }}\n",
            package("m1")
        ),
    );
    write(
        &repo.join("ws/helper/Cargo.toml"),
        &format!(
            "{}\n[dev-dependencies]\nhtool = {{ path = \"../../libs/htool\" }}\n",
            package("helper")
        ),
    );
    write(
        &repo.join("ws/m-skipped/Cargo.toml"),
        &format!(
            "{}\n[dependencies]\nnever = {{ path = \"../../libs/never\" }}\n",
            package("skipped")
        ),
    );
    write(
        &repo.join("libs/Cargo.toml"),
        "[workspace]\nmembers = [\"nested\"]\n\n[workspace.package]\nversion = \"0.7.0\"\n",
    );
    write(
        &repo.join("libs/direct/Cargo.toml"),
        &format!(
            "{}\n[dependencies]\nnested = {{ path = \"../nested\" }}\nfar = {{ workspace = true }}\n\n\
             [dev-dependencies]\ndevonly = {{ path = \"../devonly\" }}\n\
             tool = {{ path = \"/opt/tool\" }}\n\n\
             [workspace]\n\n[workspace.dependencies]\nfar = {{ path = \"../../far\" }}\n",
            package("direct")
        ),
    );
    write(&repo.join("libs/direct/src/lib.rs"), "pub fn d() {}\n");
    write(&repo.join("libs/direct/.git"), "gitdir: elsewhere\n");
    write(&repo.join("libs/direct/target/CACHEDIR.TAG"), "tag\n");
    write(
        &repo.join("libs/nested/Cargo.toml"),
        "[package]\nname = \"nested\"\nversion.workspace = true\n",
    );
    for name in ["shared", "unused", "bdep", "never", "own", "htool", "devonly"] {
        write(&repo.join(format!("libs/{name}/Cargo.toml")), &package(name));
    }
    write(&repo.join("far/Cargo.toml"), &package("far"));
    write(&repo.join("patches/patched/Cargo.toml"), &package("patched"));
    write(&repo.join("patches/patched/data.bin"), "\u{0}\u{1}bytes\n");
    write(&repo.join("unrelated/big.bin"), "never read\n");
    repo.join("ws").canonicalize().unwrap()
}

// STABILITY-COPY-1 / T4.7-16: a copy carries every package directory the
// workspace's resolve reads by path, at its position below their common root,
// and the manifests and configuration Cargo reads on the way; nothing the
// resolve does not read, and no build output or git state.
#[test]
fn a_copy_carries_the_workspaces_path_closure_and_nothing_else() {
    let dir = tempfile::tempdir().expect("tempdir");
    let workspace = closure_fixture(dir.path());
    let repo = workspace.parent().unwrap().to_path_buf();
    let closure = path_closure(&workspace).expect("a closure");
    let paths = |paths: &[&str]| paths.iter().map(PathBuf::from).collect::<Vec<_>>();
    assert_eq!((&closure.root, &closure.workspace), (&repo, &PathBuf::from("ws")));
    assert_eq!(
        closure.trees,
        paths(&[
            "far",
            "libs/bdep",
            "libs/direct",
            "libs/htool",
            "libs/nested",
            "libs/own",
            "libs/shared",
            "patches/patched",
            "ws"
        ])
    );
    assert_eq!(
        closure.files,
        paths(&[".cargo/config.toml", "Cargo.toml", "libs/Cargo.toml", "rust-toolchain.toml"])
    );
    let members: Vec<(&str, bool)> =
        closure.packages.iter().map(|package| (package.name.as_str(), package.member)).collect();
    assert_eq!(
        members,
        [
            ("far", false),
            ("bdep", false),
            ("direct", false),
            ("htool", false),
            ("nested", false),
            ("own", false),
            ("shared", false),
            ("patched", false),
            ("root-pkg", true),
            ("helper", true),
            ("m1", true),
        ]
    );
    for (read, why) in [
        ("far", "the path dependency `far` of `{repo}/libs/direct/Cargo.toml`"),
        ("libs/own", "the path dependency `own` of `{repo}/ws/Cargo.toml`"),
        ("libs/Cargo.toml", "the workspace root `{repo}/libs/nested/Cargo.toml` inherits from"),
    ] {
        let repo = repo.display().to_string();
        let entry = format!("`{}/{read}` ({})", repo, why.replace("{repo}", &repo));
        assert!(closure.reached_through.contains(&entry), "{entry}: {:?}", closure.reached_through);
    }
    assert!(!closure.is_self_contained());

    let before = tree_bytes(&repo);
    let to = dir.path().join("copies/elsewhere/repo");
    copy_closure(&closure, &to, &[]).expect("copied");
    let copied = tree_bytes(&to);
    for (path, bytes) in &copied {
        assert_eq!(before.get(path), Some(bytes), "{}: the original's bytes", path.display());
    }
    let carried: BTreeSet<String> = copied.keys().map(|path| path.display().to_string()).collect();
    let expected: BTreeSet<String> = [
        ".cargo/config.toml",
        "Cargo.toml",
        "far/Cargo.toml",
        "libs/Cargo.toml",
        "libs/bdep/Cargo.toml",
        "libs/direct/Cargo.toml",
        "libs/direct/src/lib.rs",
        "libs/htool/Cargo.toml",
        "libs/nested/Cargo.toml",
        "libs/own/Cargo.toml",
        "libs/shared/Cargo.toml",
        "patches/patched/Cargo.toml",
        "patches/patched/data.bin",
        "rust-toolchain.toml",
        "ws/Cargo.lock",
        "ws/Cargo.toml",
        "ws/helper/Cargo.toml",
        "ws/m-skipped/Cargo.toml",
        "ws/m1/Cargo.toml",
        "ws/src/lib.rs",
    ]
    .into_iter()
    .map(str::to_string)
    .collect();
    assert_eq!(carried, expected, "build output, git state and unread packages stay behind");
    assert_eq!(tree_bytes(&repo), before, "the original is only read");
    let error = copy_closure(&closure, &to, &[]).unwrap_err();
    assert_eq!(error.kind(), std::io::ErrorKind::AlreadyExists);

    // A workspace that reads nothing outside its root is copied as before.
    let lone = fixture_workspace(dir.path()).canonicalize().unwrap();
    let closure = path_closure(&lone).expect("a closure");
    assert!(closure.is_self_contained(), "{closure:?}");
    assert_eq!((closure.root, closure.workspace), (lone.clone(), PathBuf::new()));

    // One inside a package directory it reads (a path dependency on `..`)
    // is not self-contained: the copy's root is that directory.
    write(
        &lone.join("Cargo.toml"),
        "[package]\nname = \"stability-demo\"\nversion = \"0.1.0\"\n\n\
         [dependencies]\nup = { path = \"..\" }\n\n[workspace]\n",
    );
    write(
        &lone.parent().unwrap().join("Cargo.toml"),
        "[package]\nname = \"up\"\nversion = \"0.1.0\"\n",
    );
    let closure = path_closure(&lone).expect("a closure");
    assert_eq!(
        (&closure.workspace, &closure.trees),
        (&PathBuf::from("demo"), &vec![PathBuf::new()])
    );
    assert!(!closure.is_self_contained(), "{closure:?}");
}

#[test]
fn a_path_dependency_that_cannot_be_placed_is_refused_by_name() {
    let dir = tempfile::tempdir().expect("tempdir");
    let workspace = closure_fixture(dir.path());
    write(
        &workspace.join("m2/Cargo.toml"),
        "[package]\nname = \"m2\"\nversion = \"0.1.0\"\n\n\
         [dependencies]\npinned = { path = \"/opt/pinned\" }\n",
    );
    let error = path_closure(&workspace).unwrap_err();
    assert!(error.contains("`pinned`") && error.contains("absolute path `/opt/pinned`"), "{error}");
    assert!(error.contains(&workspace.join("m2/Cargo.toml").display().to_string()), "{error}");
    // The verb refuses it as usage, before any leg or scratch directory.
    let scratch = dir.path().join("scratch");
    std::fs::create_dir_all(&scratch).unwrap();
    let mut args = parsed(&["--axes", "repetition"]);
    args.scratch = Some(scratch.clone());
    let mut runner = RecordingRunner::default();
    assert_eq!(super::run(&args, &workspace, &mut runner), EXIT_USAGE);
    assert!(runner.seen.is_empty(), "no leg ran");
    assert_eq!(std::fs::read_dir(&scratch).unwrap().count(), 0, "nothing was created there");
}

#[test]
fn the_workspace_root_is_the_policy_root_above_the_caller() {
    let dir = tempfile::tempdir().expect("tempdir");
    let root = dir.path().join("ws");
    write(&root.join("Cargo.toml"), "[workspace]\nmembers = [\"m\"]\n");
    write(&root.join("m/Cargo.toml"), "[package]\nname = \"m\"\nversion = \"0.1.0\"\n");
    write(&root.join("m/src/lib.rs"), "\n");
    let root = root.canonicalize().unwrap();
    assert_eq!(super::workspace_root(&root.join("m/src")).expect("found"), root);
    assert_eq!(super::workspace_root(&root.join("m")).expect("found"), root);
    assert_eq!(
        super::locate(&root.join("m/src")).expect("located"),
        (root.clone(), PathBuf::from("m/src")),
        "each leg runs where the caller stands, so Cargo selects the same package"
    );
    let lone = dir.path().join("lone");
    std::fs::create_dir_all(&lone).unwrap();
    assert!(super::workspace_root(&lone).unwrap_err().contains("no Cargo manifest"));
}

/// The running members of `pid`'s process group, but `pid`.
#[cfg(unix)]
fn group_members(pid: u32) -> Vec<(u32, u64)> {
    let mut members = Vec::new();
    assert!(crate::process_lifecycle::tree::collect_process_group(pid, &mut members));
    members
        .into_iter()
        .filter(|&member| member != pid)
        .filter_map(|member| {
            crate::process_lifecycle::tree::identity(member)
                .filter(|identity| !identity.zombie)
                .map(|identity| (member, identity.start))
        })
        .collect()
}

#[cfg(unix)]
#[test]
fn the_load_generator_is_stopped_through_the_stop_path_and_reaped() {
    let generator = LoadGenerator::start(2).expect("start the load generator");
    assert!(generator.await_ready(), "two busy loops run");
    assert_eq!(generator.running(), 2);
    let pid = generator.pid_for_test();
    let members = group_members(pid);
    assert_eq!(members.len(), 2, "{members:?}");

    generator.stop().expect("a clean stop");
    for (member, start) in members {
        assert!(
            !crate::process_lifecycle::tree::still_running(member, Some(start)),
            "busy loop {member} outlived the stop"
        );
    }
    assert!(
        crate::process_lifecycle::tree::identity(pid).is_none(),
        "the generator's shell was reaped, not left a zombie"
    );
    assert!(
        crate::process_lifecycle::recorded_stops().iter().any(|record| {
            record.root == pid && record.cause == crate::process_lifecycle::StopCause::Released
        }),
        "the stop went through the one stop path, recorded as released"
    );

    // A generator its owner lets go of is stopped and reaped as well.
    let generator = LoadGenerator::start(1).expect("start");
    assert!(generator.await_ready());
    let pid = generator.pid_for_test();
    let members = group_members(pid);
    drop(generator);
    assert!(members.iter().all(|&(member, start)| {
        !crate::process_lifecycle::tree::still_running(member, Some(start))
    }));
    assert!(crate::process_lifecycle::tree::identity(pid).is_none());
}

/// A leg whose `check` leaves a helper in its process group and exits: the
/// helper is stopped (`leader-exited`) before the leader is reaped, so nothing
/// of the leg outlives it. The stand-in `check` is a shell script by that name,
/// which `CheckProcess` runs as `<exe> check`.
#[cfg(unix)]
#[test]
fn what_a_leg_leaves_in_its_process_group_is_stopped_before_its_leader_is_reaped() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (helper_file, leader_file) = (dir.path().join("helper.pid"), dir.path().join("leader.pid"));
    write(
        &dir.path().join("check"),
        &format!(
            "sleep 600 &\necho $! > '{}'\necho $$ > '{}'\nexit 0\n",
            helper_file.display(),
            leader_file.display()
        ),
    );
    let mut runner = CheckProcess { exe: PathBuf::from("/bin/sh") };
    let exit = runner.run(&LegSpec {
        leg: Leg::Base,
        cwd: dir.path().to_path_buf(),
        target_dir: dir.path().join("target"),
        args: Vec::new(),
        env: Vec::new(),
        stdout: dir.path().join("stdout.log"),
        stderr: dir.path().join("stderr.log"),
    });
    assert_eq!(exit, LegExit::Exited(0));
    let pid = |path: &Path| -> u32 {
        std::fs::read_to_string(path).expect("a pid").trim().parse().expect("a pid")
    };
    let (helper, leader) = (pid(&helper_file), pid(&leader_file));
    assert!(
        !crate::process_lifecycle::tree::still_running(helper, None),
        "the helper {helper} outlived its leg"
    );
    assert!(
        crate::process_lifecycle::recorded_stops().iter().any(|record| {
            record.root == leader
                && record.cause == crate::process_lifecycle::StopCause::LeaderExited
                && record.outcome.terminated > 0
        }),
        "the leader's group was stopped through the one stop path"
    );
}

// ---------------------------------------------------------------------------
// Judgements over hand-made records.

fn unit(package: &str, vector: &str, verdicts: &[(&str, &str, &str)]) -> UnitFacts {
    UnitFacts {
        package: package.to_string(),
        lane: "advisory".to_string(),
        policy: "strict".to_string(),
        selection: "--lib".to_string(),
        targo_trust_commit: COMMIT.to_string(),
        profile: "p".repeat(64),
        outcome: UnitOutcome::Measured,
        vector: vector.to_string(),
        coverage_complete: true,
        worker_threads: 0,
        stop_causes: Default::default(),
        noted_stops: Vec::new(),
        conflicting_def_paths: 0,
        verdicts: verdicts
            .iter()
            .map(|(key, status, stop)| {
                (key.to_string(), Verdict { status: status.to_string(), stop: stop.to_string() })
            })
            .collect(),
    }
}

/// The targo-trust commit the hand-made and stand-in records name.
const COMMIT: &str = "0123456789abcdef0123456789abcdef01234567";

fn side(label: &str, units: Vec<UnitFacts>) -> Side {
    Side {
        label: label.to_string(),
        failure: None,
        units: units.into_iter().map(|unit| (unit.package.clone(), unit)).collect(),
        cargo_configs: Some(Vec::new()),
    }
}

#[test]
fn equal_vectors_are_equal_and_a_moved_key_is_named() {
    let a = unit(
        "p",
        &"1".repeat(64),
        &[("p::f#01", "proved", "solved"), ("p::g#02", "unknown", "effort")],
    );
    let same = judge_axis(
        Axis::Repetition,
        &side("base", vec![a.clone()]),
        &side("repeat", vec![a.clone()]),
        None,
    );
    assert_eq!(same.verdict, AxisVerdict::Equal);
    assert!(matches!(&same.units[..], [(p, UnitVerdict::Equal { keys: 2, .. })] if p == "p"));

    let mut b = unit(
        "p",
        &"2".repeat(64),
        &[
            ("p::f#01", "proved", "solved"),
            ("p::g#02", "unknown", "solver-incomplete"),
            ("p::h#03", "proved", "solved"),
        ],
    );
    b.package = "p".to_string();
    let moved =
        judge_axis(Axis::Repetition, &side("base", vec![a]), &side("repeat", vec![b]), None);
    assert_eq!(moved.verdict, AxisVerdict::Differing);
    let [(_, UnitVerdict::Differing { keys, .. })] = &moved.units[..] else { panic!("{moved:?}") };
    assert_eq!(
        keys,
        &[
            KeyChange {
                key: "p::g#02".to_string(),
                left: Some(Verdict { status: "unknown".into(), stop: "effort".into() }),
                right: Some(Verdict { status: "unknown".into(), stop: "solver-incomplete".into() }),
            },
            KeyChange {
                key: "p::h#03".to_string(),
                left: None,
                right: Some(Verdict { status: "proved".into(), stop: "solved".into() }),
            },
        ]
    );
}

#[test]
fn a_record_that_is_no_measurement_passes_no_axis() {
    let a = unit("p", &"1".repeat(64), &[]);
    let mut backstop = a.clone();
    backstop.outcome = UnitOutcome::NotReproducible;
    backstop.noted_stops =
        vec![NotedStop { lane: "ay".into(), cause: StopCause::WallBackstop, item: None, count: 3 }];
    let result = judge_axis(
        Axis::Load,
        &side("base", vec![a.clone()]),
        &side("loaded", vec![backstop]),
        Some((4, 4)),
    );
    assert_eq!(result.verdict, AxisVerdict::CouldNotRun, "a backstop is the host's limit");
    let [(_, UnitVerdict::CouldNotRun { reason, seen: Some(seen) })] = &result.units[..] else {
        panic!("{result:?}")
    };
    assert!(reason.contains("not-reproducible") && reason.contains("wall-backstop"), "{reason}");
    assert_eq!(seen.vectors.0, seen.vectors.1, "both vectors are carried, compared or not");
    assert!(
        result.notes.iter().any(|note| note.contains("4 of 4 busy loops")),
        "{:?}",
        result.notes
    );

    let mut incomplete = a.clone();
    incomplete.coverage_complete = false;
    let result = judge_axis(
        Axis::Path,
        &side("base", vec![a.clone()]),
        &side("moved", vec![incomplete]),
        None,
    );
    assert_eq!(result.verdict, AxisVerdict::CouldNotRun);
    // Two functions under one def path: their keys cannot be told apart.
    let mut conflicting = a.clone();
    conflicting.conflicting_def_paths = 1;
    let result = judge_axis(
        Axis::Path,
        &side("base", vec![a.clone()]),
        &side("moved", vec![conflicting]),
        None,
    );
    assert!(
        matches!(
            &result.units[..],
            [(_, UnitVerdict::CouldNotRun { reason, .. })] if reason.contains("two source digests")
        ),
        "{result:?}"
    );

    // A package one leg wrote no record of, and a leg that did not run.
    let result =
        judge_axis(Axis::Path, &side("base", vec![a.clone()]), &side("moved", vec![]), None);
    assert!(matches!(
        &result.units[..],
        [(_, UnitVerdict::CouldNotRun { reason, seen: None })]
            if reason.contains("moved wrote no record")
    ));
    let mut failed = side("moved", vec![]);
    failed.failure = Some("the check exited 2 (usage or setup)".into());
    let result = judge_axis(Axis::Path, &side("base", vec![a.clone()]), &failed, None);
    assert_eq!(result.verdict, AxisVerdict::CouldNotRun);
    let result = judge_axis(Axis::Path, &side("base", vec![]), &side("moved", vec![]), None);
    assert_eq!(result.verdict, AxisVerdict::CouldNotRun, "no package at all passes nothing");
}

#[test]
fn a_solver_fault_is_a_defect_the_axis_names_and_fails_on() {
    let a = unit("p", &"1".repeat(64), &[("p::f#01", "proved", "solved")]);
    let mut faulted = a.clone();
    faulted.outcome = UnitOutcome::NotReproducible;
    faulted.vector = "2".repeat(64);
    faulted.stop_causes.record(StopCause::SolverFault);
    faulted.noted_stops =
        vec![NotedStop { lane: "ay".into(), cause: StopCause::WallBackstop, item: None, count: 1 }];
    assert!(matches!(faulted.standing(), Standing::NotReproducible(_)));
    let result = judge_axis(
        Axis::Repetition,
        &side("base", vec![a.clone()]),
        &side("repeat", vec![faulted.clone()]),
        None,
    );
    assert_eq!(result.verdict, AxisVerdict::NotReproducible);
    let [(_, UnitVerdict::NotReproducible { reason, seen: Some(seen) })] = &result.units[..] else {
        panic!("{result:?}")
    };
    assert!(
        reason.contains("repeat:") && reason.contains("solver-fault=1"),
        "the side and its cause are named: {reason}"
    );
    assert_ne!(seen.vectors.0, seen.vectors.1);
    assert_eq!(
        exit_status(&caught(), std::slice::from_ref(&result)),
        EXIT_DIFFERING,
        "a defect exits 1"
    );
    // It outranks a leg that could not run, as a difference does.
    let mut unrun = side("moved", vec![]);
    unrun.failure = Some("x".into());
    let path = judge_axis(Axis::Path, &side("base", vec![a.clone()]), &unrun, None);
    assert_eq!(exit_status(&caught(), &[path, result]), EXIT_DIFFERING);

    // An unexplained stop, in the ledger alone, is a defect too.
    let mut unexplained = a.clone();
    unexplained.outcome = UnitOutcome::NotReproducible;
    unexplained.noted_stops =
        vec![NotedStop { lane: "s1".into(), cause: StopCause::Unclassified, item: None, count: 2 }];
    assert!(
        matches!(unexplained.standing(), Standing::NotReproducible(r) if r.contains("unclassified"))
    );
    // So is an outcome no stated stop explains, and a measured outcome its own
    // stops contradict.
    let mut silent = a.clone();
    silent.outcome = UnitOutcome::NotReproducible;
    assert!(matches!(silent.standing(), Standing::NotReproducible(r) if r.contains("explains")));
    let mut contradicted = a.clone();
    contradicted.stop_causes.record(StopCause::WallBackstop);
    assert!(matches!(contradicted.standing(), Standing::NotReproducible(_)));
    // A run that could not run, or did not cover the package, is the host's
    // limit whatever its stops say.
    let mut uncovered = faulted.clone();
    uncovered.coverage_complete = false;
    assert!(matches!(uncovered.standing(), Standing::CouldNotRun(_)));
    let mut refused = faulted;
    refused.outcome = UnitOutcome::CouldNotRun;
    assert!(matches!(refused.standing(), Standing::CouldNotRun(_)));
    // Backstops alone, with or without admission refused, are the host's limit.
    let mut rss = a.clone();
    rss.outcome = UnitOutcome::NotReproducible;
    rss.stop_causes.record(StopCause::RssBackstop);
    assert!(matches!(rss.standing(), Standing::CouldNotRun(_)));
    assert_eq!(a.standing(), Standing::Measured);
}

#[test]
fn legs_that_read_different_cargo_configuration_compare_nothing() {
    let a = unit("p", &"1".repeat(64), &[]);
    let base = side("base", vec![a.clone()]);
    let mut moved = side("moved", vec![a]);
    let config = PathBuf::from("/work/.cargo/config.toml");
    let mut base_with = base.clone();
    base_with.cargo_configs = Some(vec![config.clone()]);
    let result = judge_axis(Axis::Path, &base_with, &moved, None);
    assert_eq!(result.verdict, AxisVerdict::CouldNotRun);
    assert!(
        matches!(
            &result.units[..],
            [(_, UnitVerdict::CouldNotRun { reason, seen: Some(_) })]
                if reason.contains("/work/.cargo/config.toml") && reason.contains("--scratch")
        ),
        "{result:?}"
    );
    moved.cargo_configs = Some(vec![config]);
    assert_eq!(judge_axis(Axis::Path, &base_with, &moved, None).verdict, AxisVerdict::Equal);
}

#[test]
fn the_cargo_configuration_above_a_directory_is_every_ancestors_but_cargo_homes() {
    let dir = tempfile::tempdir().expect("tempdir");
    let root = dir.path().canonicalize().unwrap();
    write(&root.join("a/.cargo/config.toml"), "[build]\njobs = 4\n");
    write(&root.join("a/b/.cargo/config"), "[build]\n");
    write(&root.join("a/b/c/.cargo/config.toml"), "[build]\n");
    std::fs::create_dir_all(root.join("a/b/c/d")).unwrap();
    let found = ancestor_cargo_configs(&root.join("a/b/c"));
    let ours: Vec<&PathBuf> = found.iter().filter(|path| path.starts_with(&root)).collect();
    assert_eq!(
        ours,
        [&root.join("a/b/.cargo/config"), &root.join("a/.cargo/config.toml")],
        "nearest first; the directory's own `.cargo` is the checkout's"
    );
}

#[test]
fn the_instrument_checks_fail_an_axis_that_did_not_run_what_it_names() {
    let a = unit("p", &"1".repeat(64), &[]);
    // The serial leg's record must state one worker thread.
    let unserial = judge_axis(
        Axis::Parallelism,
        &side("base", vec![a.clone()]),
        &side("serial", vec![a.clone()]),
        None,
    );
    assert_eq!(unserial.verdict, AxisVerdict::Failed);
    let mut serial = a.clone();
    serial.worker_threads = 1;
    let ok = judge_axis(
        Axis::Parallelism,
        &side("base", vec![a.clone()]),
        &side("serial", vec![serial]),
        None,
    );
    assert_eq!(ok.verdict, AxisVerdict::Equal);

    // At effort 1, something must stop on the count, in a row or the ledger.
    let vacuous = judge_axis(
        Axis::Effort,
        &side("effort", vec![a.clone()]),
        &side("effort-loaded", vec![a.clone()]),
        Some((2, 2)),
    );
    assert_eq!(vacuous.verdict, AxisVerdict::Failed);
    let mut counted = a.clone();
    counted.noted_stops =
        vec![NotedStop { lane: "ay".into(), cause: StopCause::Effort, item: None, count: 2 }];
    let ok = judge_axis(
        Axis::Effort,
        &side("effort", vec![counted.clone()]),
        &side("effort-loaded", vec![counted]),
        Some((2, 2)),
    );
    assert_eq!(ok.verdict, AxisVerdict::Equal, "{:?}", ok.notes);
}

#[test]
fn another_hosts_record_of_another_run_is_not_comparable() {
    let here = unit("p", &"1".repeat(64), &[]);
    let mut there = here.clone();
    let ok = judge_axis(
        Axis::Host,
        &side("base", vec![here.clone(), unit("q", &"3".repeat(64), &[])]),
        &side("another host", vec![there.clone()]),
        None,
    );
    assert_eq!(ok.verdict, AxisVerdict::Equal, "only the packages the other host's records name");
    assert_eq!(ok.units.len(), 1);
    there.selection = "--lib --profile=release".into();
    let other =
        judge_axis(Axis::Host, &side("base", vec![here]), &side("another host", vec![there]), None);
    assert_eq!(other.verdict, AxisVerdict::NotComparable);
    assert_eq!(exit_status(&caught(), &[other]), EXIT_USAGE);
}

fn caught() -> ControlResult {
    ControlResult { verdict: ControlVerdict::Caught, units: Vec::new() }
}

#[test]
fn the_control_is_caught_only_by_a_package_a_clock_kept_from_a_measurement() {
    let measured = unit("p", &"1".repeat(64), &[]);
    let mut clocked = unit("q", &"2".repeat(64), &[]);
    clocked.outcome = UnitOutcome::NotReproducible;
    clocked.stop_causes.record(StopCause::WallBackstop);
    assert_eq!(
        judge_control(&side("control", vec![measured.clone(), clocked])).verdict,
        ControlVerdict::Caught
    );
    assert!(matches!(
        judge_control(&side("control", vec![measured.clone()])).verdict,
        ControlVerdict::Failed(_)
    ));
    assert!(matches!(
        judge_control(&side("control", vec![])).verdict,
        ControlVerdict::CouldNotRun(_)
    ));
    // A control none of whose packages ran (no coverage; a row with no key)
    // shows nothing about a clock: could not run, not failed.
    let mut uncovered = unit("p", &"1".repeat(64), &[]);
    uncovered.coverage_complete = false;
    let mut unkeyed = unit("q", &"2".repeat(64), &[]);
    unkeyed.outcome = UnitOutcome::CouldNotRun;
    assert!(matches!(
        judge_control(&side("control", vec![uncovered.clone(), unkeyed])).verdict,
        ControlVerdict::CouldNotRun(reason) if reason.contains("ran to a complete coverage")
    ));
    // One that ran and read as a measurement is the instrument's failure.
    assert!(matches!(
        judge_control(&side("control", vec![uncovered, measured])).verdict,
        ControlVerdict::Failed(_)
    ));
}

#[test]
fn a_difference_outranks_a_leg_that_could_not_run() {
    let result = |verdict| AxisResult {
        axis: Axis::Repetition,
        left: "a".into(),
        right: "b".into(),
        verdict,
        units: Vec::new(),
        notes: Vec::new(),
    };
    let failed_control =
        ControlResult { verdict: ControlVerdict::Failed("x".into()), units: vec![] };
    let unrun_control =
        ControlResult { verdict: ControlVerdict::CouldNotRun("x".into()), units: vec![] };
    assert_eq!(exit_status(&caught(), &[result(AxisVerdict::Equal)]), EXIT_EQUAL);
    assert_eq!(
        exit_status(&caught(), &[result(AxisVerdict::Equal), result(AxisVerdict::CouldNotRun)]),
        EXIT_COULD_NOT_RUN
    );
    assert_eq!(
        exit_status(&caught(), &[result(AxisVerdict::Differing), result(AxisVerdict::CouldNotRun)]),
        EXIT_DIFFERING
    );
    assert_eq!(exit_status(&caught(), &[result(AxisVerdict::Failed)]), EXIT_DIFFERING);
    assert_eq!(exit_status(&failed_control, &[result(AxisVerdict::Equal)]), EXIT_DIFFERING);
    assert_eq!(exit_status(&unrun_control, &[result(AxisVerdict::Equal)]), EXIT_COULD_NOT_RUN);
}

// ---------------------------------------------------------------------------
// Whole runs, over a stand-in for the leg's `targo trust check`.

/// A published row of `package`'s function `name`, keyed as the compiler keys
/// it, with the function label a Cargo run gives it (which embeds the
/// checkout's path and the package version: no record may carry either).
fn row(
    package: &str,
    checkout: &Path,
    version: &str,
    name: &str,
    outcome: VerificationOutcome,
    reason: Option<String>,
) -> VerificationResult {
    let function = format!("{}::{name}", package.replace('-', "_"));
    let mut row = VerificationResult {
        function: format!(
            "cargo-target(package_id=\"path+file://{}#{package}@{version}\")::{function}",
            checkout.display()
        ),
        kind: "overflow:add".to_string(),
        message: "arithmetic overflow (Add)".to_string(),
        outcome,
        backend: "ay".to_string(),
        time_ms: Some(3),
        location: Some(trust_types::SourceSpan {
            file: "src/lib.rs".to_string(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 2,
        }),
        counterexample: None,
        reason,
        raw_line: String::new(),
    };
    let evidence = StructuredTransportEvidence {
        assumes: Vec::new(),
        obligation_id: Some(format!("vc:{function}:arithmetic_safety:0")),
        claim_digest_sha256: None,
        original_vc_snapshot: None,
        typed_kind: None,
        design_mandate: false,
        runtime_checks: None,
        native_trust_ir: None,
        proof_evidence: None,
        monitor: None,
        identity: Some(ObligationIdentity {
            key: trust_types::obligation_identity::obligation_key(
                &function,
                &local_id("overflow:add", "stmt:0123456789abcdef", 0),
            ),
            package: package.to_string(),
            function_source_sha256: Some(function_source_digest(&function)),
            expanded_function_identity: None,
        }),
        grade: None,
    };
    crate::types::replace_structured_transport_evidence(&mut row, &evidence).expect("serializes");
    row
}

/// What one stand-in check saw.
#[derive(Debug, Clone)]
struct Seen {
    spec: LegSpec,
    version: String,
}

/// The stand-in: reads the manifest of the checkout it runs in, and writes the
/// records a check of that package writes, through the check's own writer
/// (`ObligationRecords::write_records`). Its verdicts are a function of what
/// it reads (the `[trust]` table), never of the path, the version or the
/// call — except through the TEST SEAM below.
#[derive(Default)]
struct RecordingRunner {
    seen: Vec<Seen>,
    /// TEST SEAM, a deliberately nondeterministic input that exists only in
    /// this test: on this call (0-based), the second obligation stops on
    /// `effort` instead of `solver-incomplete`.
    flip_on_call: Option<usize>,
    /// The targo-trust commit the records name (default [`COMMIT`]).
    commit: Option<String>,
}

impl LegRunner for RecordingRunner {
    fn run(&mut self, spec: &LegSpec) -> LegExit {
        let call = self.seen.len();
        let manifest = read_toml(&spec.cwd.join("Cargo.toml"));
        let package = manifest["package"]["name"].as_str().expect("a package").to_string();
        let version = manifest["package"]["version"].as_str().expect("a version").to_string();
        self.seen.push(Seen { spec: spec.clone(), version: version.clone() });
        // What Cargo does before anything else: read each path dependency's
        // manifest. A copy that left one behind fails here, as Cargo fails.
        // A `workspace = true` one through the manifest's own
        // `[workspace.dependencies]`, as Cargo reads a root package's.
        let dependencies = manifest.get("dependencies").and_then(toml::Value::as_table);
        let inherited =
            manifest.get("workspace").and_then(|workspace| workspace.get("dependencies"));
        for spec_path in dependencies.into_iter().flat_map(|table| table.iter()).filter_map(
            |(name, dependency)| match dependency.get("workspace") {
                Some(toml::Value::Boolean(true)) => inherited?.get(name)?.get("path")?.as_str(),
                _ => dependency.get("path")?.as_str(),
            },
        ) {
            let dependency = spec.cwd.join(spec_path).join("Cargo.toml");
            if !dependency.is_file() {
                let error = format!("error: failed to read `{}`\n", dependency.display());
                std::fs::write(&spec.stderr, error).expect("write stderr");
                return LegExit::Exited(101);
            }
        }
        let trust = manifest.get("trust").and_then(toml::Value::as_table);
        let key =
            |name: &str| trust.and_then(|table| table.get(name)).and_then(toml::Value::as_integer);
        let worker_threads = spec
            .args
            .windows(2)
            .find(|pair| pair[0] == "--worker-threads")
            .map_or(0, |pair| pair[1].parse().expect("a count"));
        let second = if key("backstop") == Some(1) {
            (VerificationOutcome::Timeout, None)
        } else if key("effort") == Some(1) {
            (VerificationOutcome::Unknown, Some("search ended [stop:effort]".to_string()))
        } else {
            let stop = if self.flip_on_call == Some(call) { "effort" } else { "solver-incomplete" };
            (VerificationOutcome::Unknown, Some(format!("search ended [stop:{stop}]")))
        };
        let rows = [
            row(&package, &spec.cwd, &version, "f", VerificationOutcome::Proved, None),
            row(&package, &spec.cwd, &version, "g", second.0, second.1),
        ];
        let coverage = [trust_types::CoverageTransportSummary {
            crate_name: package.replace('-', "_"),
            package_name: package.clone(),
            primary_package: true,
            verification_session: "session".to_string(),
            eligible: 2,
            processed: 2,
            function_identities: None,
            noted_stops: Vec::new(),
            degraded_anchors: 0,
            memory: trust_types::MemorySummary::default(),
        }];
        let determinism = crate::determinism_report::UnitDeterminism::of_rows(&rows, &[]);
        let profile = BudgetProfile::new(
            key("effort").map_or(trust_types::determinism::EffortScale::BUILTIN, |k| {
                trust_types::determinism::EffortScale::parse(&k.to_string()).expect("an effort")
            }),
            key("backstop").map_or(trust_types::determinism::Backstop::BUILTIN, |b| {
                trust_types::determinism::Backstop::parse(&b.to_string()).expect("a backstop")
            }),
            worker_threads,
        );
        let records = ObligationRecords::of_rows(
            &rows,
            &FunctionInventory::of_rows(&rows),
            RunFacts {
                lane: "advisory".to_string(),
                policy: "strict".to_string(),
                selection: crate::obligations::canonical_selection(&spec.args),
                targo_trust_commit: self.commit.clone().unwrap_or_else(|| COMMIT.to_string()),
                profile: profile.id(),
                worker_threads,
                outcome: determinism.outcome,
                vector: determinism.vector.digest(),
                coverage_complete: true,
                degraded_anchors: 0,
            },
            RunScope { selected: BTreeSet::from([package.clone()]), resolved: BTreeSet::new() },
            &RunCoverage {
                rows: &coverage,
                missing: BTreeSet::new(),
                publication_stops: &[],
                compile_errors: &[],
            },
        );
        records.write_records(&spec.target_dir).expect("write the records");
        let not_measured = determinism.outcome != UnitOutcome::Measured;
        LegExit::Exited(if not_measured { 3 } else { 0 })
    }
}

/// A one-package workspace at `<dir>/ws/demo`, with build output and git
/// state a copy must leave behind.
fn fixture_workspace(dir: &Path) -> PathBuf {
    let root = dir.join("ws").join("demo");
    write(
        &root.join("Cargo.toml"),
        concat!(
            "[package]\nname = \"stability-demo\"\nversion = \"0.1.0\"\n",
            "edition = \"2021\"\n\n[workspace]\n",
        ),
    );
    write(&root.join("src/lib.rs"), "pub fn f(a: u8) -> u8 { a }\n");
    write(&root.join("target/CACHEDIR.TAG"), "tag\n");
    write(&root.join(".git/HEAD"), "ref: refs/heads/main\n");
    root
}

fn plan_for(root: &Path, scratch: &Path, args: &StabilityArgs) -> Plan {
    Plan {
        closure: path_closure(root).expect("a path closure"),
        relative_cwd: PathBuf::new(),
        scratch: scratch.to_path_buf(),
        legs: legs_for(&args.axes),
        check_args: args.check_args.clone(),
        load_loops: 2,
    }
}

#[test]
fn a_deterministic_package_is_equal_on_every_axis_and_the_control_is_caught() {
    let dir = tempfile::tempdir().expect("tempdir");
    let root = fixture_workspace(dir.path());
    let scratch = dir.path().join("scratch");
    std::fs::create_dir_all(&scratch).unwrap();
    let args = parsed(&[
        "--axes",
        "repetition,parallelism,path,version,load,effort",
        "--lib",
        "--allow-l0-gaps",
    ]);
    let mut runner = RecordingRunner::default();
    let report = execute(&args, &plan_for(&root, &scratch, &args), BTreeMap::new(), &mut runner);

    let text = report.render_terminal();
    assert_eq!(report.exit, EXIT_EQUAL, "{text}");
    assert_eq!(report.control.verdict, ControlVerdict::Caught, "{text}");
    let verdicts: Vec<(&str, AxisVerdict)> =
        report.axes.iter().map(|axis| (axis.axis.name(), axis.verdict)).collect();
    assert_eq!(
        verdicts,
        [
            ("repetition", AxisVerdict::Equal),
            ("parallelism", AxisVerdict::Equal),
            ("path", AxisVerdict::Equal),
            ("version", AxisVerdict::Equal),
            ("load", AxisVerdict::Equal),
            ("effort", AxisVerdict::Equal),
        ],
        "{text}"
    );
    // The legs ran in order, each in the checkout its condition names.
    let order: Vec<&str> = runner.seen.iter().map(|seen| seen.spec.leg.label()).collect();
    assert_eq!(
        order,
        [
            "control",
            "base",
            "repeat",
            "serial",
            "moved",
            "bumped",
            "loaded",
            "effort",
            "effort-loaded"
        ]
    );
    let seen = |leg: Leg| runner.seen.iter().find(|seen| seen.spec.leg == leg).expect("ran");
    assert_eq!(seen(Leg::Base).spec.cwd, root);
    assert_eq!(seen(Leg::Repeat).spec.cwd, root);
    let moved = &seen(Leg::Moved).spec.cwd;
    assert!(moved.starts_with(&scratch) && moved.ends_with("elsewhere/deeper/demo"), "{moved:?}");
    assert_eq!(&seen(Leg::Bumped).spec.cwd, moved, "the version axis changes the version only");
    assert_eq!(seen(Leg::Moved).version, "0.1.0");
    assert_eq!(seen(Leg::Bumped).version, "0.1.1");
    assert!(!moved.join("target").exists() && !moved.join(".git").exists());
    assert!(seen(Leg::Serial).spec.args.windows(2).any(|pair| pair == ["--worker-threads", "1"]));
    // Every leg has its own target directory, removed once its records are read.
    let targets: BTreeSet<&PathBuf> =
        runner.seen.iter().map(|seen| &seen.spec.target_dir).collect();
    assert_eq!(targets.len(), runner.seen.len());
    assert!(targets.iter().all(|target| !target.exists()));
    // Under load, the generator held every busy loop through the leg.
    for run in report.legs.iter().filter(|run| run.leg.loaded()) {
        assert_eq!(run.load, Some((2, 2)), "{text}");
    }
    let effort = report.axes.iter().find(|axis| axis.axis == Axis::Effort).unwrap();
    assert!(effort.notes.iter().any(|note| note.contains("1 row(s) state `effort`")), "{text}");
    assert!(text.contains("Negative control ([trust] backstop = 1): CAUGHT"), "{text}");
    assert!(text.contains("stability-demo: equal over 2 obligation key(s) (vector "), "{text}");
    assert!(text.contains("Result: exit 0"), "{text}");
    let json = report.render_json();
    assert_eq!(json["schema"], STABILITY_SCHEMA);
    assert_eq!(json["exit"], 0);
    assert_eq!(json["control"]["verdict"], "caught");
    assert_eq!(json["axes"][0]["units"][0]["verdict"], "equal");
    assert_eq!(json["axes"][0]["units"][0]["keys"], 2);
    assert_eq!(json["legs"][1]["packages"][0]["outcome"], "measured");
    assert_eq!(json["legs"][1]["packages"][0]["keys"], 2);
}

#[test]
fn a_nondeterministic_input_makes_the_repetition_axis_differ_and_names_the_key() {
    let dir = tempfile::tempdir().expect("tempdir");
    let root = fixture_workspace(dir.path());
    let scratch = dir.path().join("scratch");
    std::fs::create_dir_all(&scratch).unwrap();
    let args = parsed(&["--axes", "repetition", "--lib"]);
    // Calls: 0 control, 1 base, 2 repeat. The seam moves the repeat's verdict.
    let mut runner = RecordingRunner { flip_on_call: Some(2), ..Default::default() };
    let report = execute(&args, &plan_for(&root, &scratch, &args), BTreeMap::new(), &mut runner);

    let text = report.render_terminal();
    assert_eq!(report.exit, EXIT_DIFFERING, "{text}");
    let [axis] = &report.axes[..] else { panic!("{text}") };
    assert_eq!(axis.verdict, AxisVerdict::Differing, "{text}");
    let [(package, UnitVerdict::Differing { keys, seen })] = &axis.units[..] else {
        panic!("{text}")
    };
    assert_eq!(package, "stability-demo");
    assert_eq!(seen.profiles.0, seen.profiles.1, "the same profile: only the verdict moved");
    assert_ne!(seen.vectors.0, seen.vectors.1);
    assert_eq!(seen.keys, (2, 2));
    let [change] = &keys[..] else { panic!("{text}") };
    assert!(change.key.starts_with("stability_demo::g#"), "{change:?}");
    assert_eq!(change.left.as_ref().map(|v| v.stop.as_str()), Some("solver-incomplete"));
    assert_eq!(change.right.as_ref().map(|v| v.stop.as_str()), Some("effort"));
    assert!(text.contains("Axis repetition (base / repeat): DIFFERING"), "{text}");
    assert!(
        text.contains(&format!(
            "{}: base unknown/solver-incomplete, repeat unknown/effort",
            change.key
        )),
        "{text}"
    );
    let json = report.render_json();
    assert_eq!(json["exit"], 1);
    assert_eq!(json["axes"][0]["units"][0]["differing_keys"][0]["key"], change.key.as_str());

    // Without the seam the same run is equal: the difference was the input's.
    let mut runner = RecordingRunner::default();
    let scratch = dir.path().join("scratch-2");
    std::fs::create_dir_all(&scratch).unwrap();
    let report = execute(&args, &plan_for(&root, &scratch, &args), BTreeMap::new(), &mut runner);
    assert_eq!(report.exit, EXIT_EQUAL, "{}", report.render_terminal());
}

// STABILITY-COPY-1 / T4.7-16: a workspace whose manifests read outside its
// root (here by every route Cargo takes) is copied with its path closure, so
// every copied leg resolves at the workspace's relative position, the control
// is caught, every axis compares, and nothing outside the scratch is written.
#[test]
fn a_workspace_that_reads_outside_its_root_is_copied_with_what_it_reads() {
    let dir = tempfile::tempdir().expect("tempdir");
    let workspace = closure_fixture(dir.path());
    let repo = workspace.parent().unwrap().to_path_buf();
    let scratch = dir.path().join("scratch");
    std::fs::create_dir_all(&scratch).unwrap();
    let before = tree_bytes(&repo);
    let args = parsed(&["--axes", "repetition,path,version", "--lib"]);
    let mut runner = RecordingRunner::default();
    let report =
        execute(&args, &plan_for(&workspace, &scratch, &args), BTreeMap::new(), &mut runner);

    let text = report.render_terminal();
    assert_eq!(report.exit, EXIT_EQUAL, "{text}");
    assert_eq!(report.control.verdict, ControlVerdict::Caught, "{text}");
    assert!(report.axes.iter().all(|axis| axis.verdict == AxisVerdict::Equal), "{text}");
    let seen = |leg: Leg| runner.seen.iter().find(|seen| seen.spec.leg == leg).expect("ran");
    assert_eq!(seen(Leg::Base).spec.cwd, workspace, "the caller's own checkout");
    let moved = &seen(Leg::Moved).spec.cwd;
    assert!(
        moved.starts_with(&scratch) && moved.ends_with("elsewhere/deeper/repo/ws"),
        "{moved:?}"
    );
    assert!(seen(Leg::Control).spec.cwd.ends_with("checkouts/control/repo/ws"));
    for dependency in
        ["../libs/direct", "../libs/nested", "../libs/own", "../far", "../patches/patched"]
    {
        assert!(moved.join(dependency).join("Cargo.toml").is_file(), "{dependency}");
    }
    assert_eq!(seen(Leg::Bumped).version, "0.1.1", "the recorded package's version moved");
    let copy_root = moved.parent().unwrap();
    assert!(
        read_toml(&copy_root.join("libs/direct/Cargo.toml"))["package"]["version"].as_str()
            == Some("0.1.0"),
        "a dependency nobody recorded keeps its version"
    );
    assert_eq!(tree_bytes(&repo), before, "nothing outside the scratch is written");
    assert!(
        text.contains(&format!(
            "copies carry `{}`'s path closure: the workspace at `ws`, 8 package directories \
             outside it and 4 file(s) on the way to them",
            repo.display()
        )),
        "{text}"
    );
    let json = report.render_json();
    assert_eq!(json["copy"]["workspace"], "ws");
    assert_eq!(json["copy"]["trees"].as_array().map(Vec::len), Some(9));

    // Without the closure (the root alone, as before), the copy reads nothing
    // there: each copied leg fails as Cargo does, and nothing compares.
    let mut alone = plan_for(&workspace, &dir.path().join("scratch-alone"), &args);
    std::fs::create_dir_all(&alone.scratch).unwrap();
    alone.closure = PathClosure {
        root: workspace.clone(),
        workspace: PathBuf::new(),
        trees: vec![PathBuf::new()],
        files: Vec::new(),
        packages: Vec::new(),
        reached_through: Vec::new(),
    };
    let report = execute(&args, &alone, BTreeMap::new(), &mut RecordingRunner::default());
    let text = report.render_terminal();
    assert_eq!(report.exit, EXIT_COULD_NOT_RUN, "{text}");
    assert!(text.contains("libs/direct/Cargo.toml`"), "{text}");
}

/// "Another host": the same check, its records written to a target
/// directory of its own, as a second machine's would be and then carried here.
fn other_host_records(dir: &Path, root: &Path, commit: Option<&str>) -> PathBuf {
    let mut other = RecordingRunner { commit: commit.map(str::to_string), ..Default::default() };
    let target = dir.join("other-host").join("target");
    other.run(&LegSpec {
        leg: Leg::Base,
        cwd: root.to_path_buf(),
        target_dir: target.clone(),
        args: strings(&["--lib"]),
        env: Vec::new(),
        stdout: dir.join("o.log"),
        stderr: dir.join("e.log"),
    });
    target
}

fn run_host_axis(dir: &Path, root: &Path, against: &Path, scratch: &str) -> Report {
    let args = parsed(&["--against", against.to_str().unwrap(), "--axes", "host", "--lib"]);
    let scratch = dir.join(scratch);
    std::fs::create_dir_all(&scratch).unwrap();
    let units = super::read_against(against).expect("another host's records");
    execute(&args, &plan_for(root, &scratch, &args), units, &mut RecordingRunner::default())
}

/// Rewrite one of another host's records in place.
fn edit_record(path: &Path, edit: impl Fn(String) -> String) {
    let text = std::fs::read_to_string(path).expect("a record");
    std::fs::write(path, edit(text)).expect("rewrite");
}

#[test]
fn another_hosts_records_are_compared_with_this_hosts_base_leg() {
    let dir = tempfile::tempdir().expect("tempdir");
    let root = fixture_workspace(dir.path());
    let target = other_host_records(dir.path(), &root, None);
    let report = run_host_axis(dir.path(), &root, &target, "s1");
    assert_eq!(report.exit, EXIT_EQUAL, "{}", report.render_terminal());
    assert_eq!(report.axes[0].right, "another host");
    assert!(
        report.axes[0].notes.iter().any(|note| note.contains("name no toolchain")),
        "the axis says what it could not check: {:?}",
        report.axes[0].notes
    );

    // The other host's verdict moved: named, exit 1.
    let package = crate::package_record::package_record_path(
        &crate::package_record::package_records_dir(&target),
        "stability-demo",
    );
    let obligations = crate::obligations::obligation_record_path(
        &crate::obligations::records_dir(&target),
        "stability-demo",
    );
    let vector = super::read_against(&target).unwrap()["stability-demo"].vector.clone();
    let moved = format!("\"vector\":\"{}\"", "f".repeat(64));
    edit_record(&obligations, |text| {
        text.replace("\"stop\":\"solver-incomplete\"", "\"stop\":\"effort\"")
            .replace(&format!("\"vector\":\"{vector}\""), &moved)
    });
    edit_record(&package, |text| text.replace(&format!("\"vector\":\"{vector}\""), &moved));
    let report = run_host_axis(dir.path(), &root, &target, "s2");
    assert_eq!(report.exit, EXIT_DIFFERING, "{}", report.render_terminal());
    assert!(matches!(
        &report.axes[0].units[..],
        [(_, UnitVerdict::Differing { keys, .. })] if keys.len() == 1
    ));

    // Two functions under one def path there: the record is no measurement,
    // whatever its vector says, as it is here.
    edit_record(&package, |text| {
        text.replace("\"conflicting_def_paths\":0", "\"conflicting_def_paths\":1")
    });
    let report = run_host_axis(dir.path(), &root, &target, "s3");
    assert_eq!(report.exit, EXIT_COULD_NOT_RUN, "{}", report.render_terminal());
    assert!(matches!(
        &report.axes[0].units[..],
        [(_, UnitVerdict::CouldNotRun { reason, .. })] if reason.contains("two source digests")
    ));
}

#[test]
fn another_host_of_a_build_that_names_no_commit_is_not_comparable() {
    let dir = tempfile::tempdir().expect("tempdir");
    let root = fixture_workspace(dir.path());
    let target = other_host_records(dir.path(), &root, Some("unbound"));
    let report = run_host_axis(dir.path(), &root, &target, "s");
    assert_eq!(report.exit, EXIT_USAGE, "{}", report.render_terminal());
    assert!(matches!(
        &report.axes[0].units[..],
        [(_, UnitVerdict::NotComparable(reason))] if reason.contains("embedded no commit")
    ));
    // A directory with no package record names nothing to compare.
    let empty = dir.path().join("empty");
    std::fs::create_dir_all(&empty).unwrap();
    assert!(super::read_against(&empty).unwrap_err().contains("no package record"));
}

#[test]
fn record_contents_reach_the_terminal_escaped() {
    let mut a = unit("p\u{1b}[2Jq", &"1".repeat(64), &[("k\nResult: exit 0", "proved", "solved")]);
    let mut b = a.clone();
    b.vector = "2".repeat(64);
    b.verdicts.values_mut().for_each(|verdict| verdict.stop = "effort".into());
    a.package = b.package.clone();
    let axis = judge_axis(Axis::Repetition, &side("base", vec![a]), &side("repeat", vec![b]), None);
    let report = Report {
        scratch: None,
        copy: PathClosure {
            root: PathBuf::from("/ws"),
            workspace: PathBuf::new(),
            trees: vec![PathBuf::new()],
            files: Vec::new(),
            packages: Vec::new(),
            reached_through: Vec::new(),
        },
        legs: Vec::new(),
        control: caught(),
        axes: vec![axis],
        exit: EXIT_DIFFERING,
    };
    let text = report.render_terminal();
    assert!(!text.contains('\u{1b}'), "{text:?}");
    assert!(text.contains("p\\u{1b}[2Jq: DIFFERING"), "{text}");
    assert!(text.contains("k\\nResult: exit 0: base proved/solved"), "{text}");
    assert_eq!(
        text.matches("Result: exit").count(),
        2,
        "one is the key, escaped on its line: {text}"
    );
    assert!(text.lines().filter(|line| line.starts_with("Result: exit")).count() == 1, "{text}");
}

#[test]
fn a_scratch_directory_inside_the_tree_a_copy_is_made_of_is_refused() {
    let dir = tempfile::tempdir().expect("tempdir");
    let root = fixture_workspace(dir.path());
    // Inside the workspace; and, for a workspace that reads outside its root,
    // inside the closure's root, though outside the workspace.
    let reaching = closure_fixture(dir.path());
    for (workspace, inside) in [
        (root.clone(), root.join("scratch")),
        (reaching.clone(), reaching.parent().unwrap().join("scratch")),
    ] {
        std::fs::create_dir_all(&inside).unwrap();
        let mut args = parsed(&["--axes", "repetition"]);
        args.scratch = Some(inside.clone());
        let mut runner = RecordingRunner::default();
        assert_eq!(super::run(&args, &workspace, &mut runner), EXIT_USAGE);
        assert!(runner.seen.is_empty(), "no leg ran");
        assert_eq!(std::fs::read_dir(&inside).unwrap().count(), 0, "nothing was created there");
    }
}

#[test]
fn a_leg_that_could_not_run_is_named_with_its_stderr_and_passes_nothing() {
    struct Refusing;
    impl LegRunner for Refusing {
        fn run(&mut self, spec: &LegSpec) -> LegExit {
            std::fs::write(&spec.stderr, "targo trust: no canonical trustc\n").unwrap();
            LegExit::Exited(2)
        }
    }
    let dir = tempfile::tempdir().expect("tempdir");
    let root = fixture_workspace(dir.path());
    let scratch = dir.path().join("scratch");
    std::fs::create_dir_all(&scratch).unwrap();
    let args = parsed(&["--axes", "repetition,path"]);
    let report = execute(&args, &plan_for(&root, &scratch, &args), BTreeMap::new(), &mut Refusing);
    let text = report.render_terminal();
    assert_eq!(report.exit, EXIT_COULD_NOT_RUN, "{text}");
    assert!(matches!(report.control.verdict, ControlVerdict::CouldNotRun(_)), "{text}");
    assert!(report.axes.iter().all(|axis| axis.verdict == AxisVerdict::CouldNotRun), "{text}");
    assert!(text.contains("COULD NOT RUN: the check exited 2 (usage or setup)"), "{text}");
    assert!(text.contains("| targo trust: no canonical trustc"), "{text}");
}

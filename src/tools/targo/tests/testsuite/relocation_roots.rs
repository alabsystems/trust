//! Trust: tests for `-Ztrust-relocation-roots` and `-Ztrust-carried-times`
//! (EW-9).
//!
//! A tree's build directory seeded by copying another tree's green build must
//! be fresh exactly when its inputs match after re-rooting, and must watch,
//! link and include the copy's own files, never the original's. The seeder
//! copies the build directory with its times; the copy's sources are a fresh
//! checkout, newer than every copied output, and for each one whose bytes are
//! the original's it records the original's time in a carried-times table
//! instead of setting it on the file. `relocate` does the same. Sources of the
//! original are backdated an hour so that its build is newer than them and
//! every later edit is newer than its build.

use std::fs;
use std::path::{Path, PathBuf};

use crate::prelude::*;
use cargo_test_support::{Execs, Project, is_coarse_mtime, paths, project, sleep_ms, str};
use filetime::FileTime;

const FEATURE: &str = "trust-relocation-roots";
const CARRIED: &str = "trust-carried-times";

/// A workspace whose build script watches a file outside its package and a
/// file in a second root outside the tree (as a linked worktree's git dir
/// is), reads an env var naming a tool in the tree, adds a link search path
/// in the tree, and hands the library a file in the second root to include
/// (an absolute dep-info path outside the package, workspace and build root).
fn seed(flag: bool) -> Project {
    let p = project()
        .at("a")
        .file(
            "Cargo.toml",
            r#"
                [workspace]
                members = ["pkg"]
                resolver = "2"
            "#,
        )
        .file(
            "pkg/Cargo.toml",
            r#"
                [package]
                name = "pkg"
                version = "0.1.0"
                edition = "2021"
            "#,
        )
        .file(
            "pkg/build.rs",
            r#"
                use std::env;
                use std::path::PathBuf;

                fn main() {
                    let manifest = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
                    let ws = manifest.parent().unwrap();
                    let git = env::var("RELOC_GIT_DIR").unwrap();
                    println!("cargo::rerun-if-changed=build.rs");
                    println!("cargo::rerun-if-changed={}", ws.join("shared/watched.txt").display());
                    println!("cargo::rerun-if-changed={git}/HEAD");
                    println!("cargo::rerun-if-env-changed=RELOC_TOOL");
                    println!("cargo::rerun-if-env-changed=RELOC_GIT_DIR");
                    println!("cargo::rustc-link-search=native={}", ws.join("native/lib").display());
                    println!("cargo::rustc-env=RELOC_GIT_HEAD={git}/HEAD");
                }
            "#,
        )
        .file(
            "pkg/src/lib.rs",
            r#"pub const HEAD: &str = include_str!(env!("RELOC_GIT_HEAD"));"#,
        )
        .file("shared/watched.txt", "watched")
        .file("tools/bin/tool", "")
        .file("native/lib/.keep", "")
        .build();
    let git = git_dir("a");
    fs::create_dir_all(&git).unwrap();
    fs::write(git.join("HEAD"), "ref: refs/heads/main\n").unwrap();
    let sources = ago(3600);
    for root in [tree("a"), git] {
        for entry in walkdir::WalkDir::new(root) {
            let entry = entry.unwrap();
            if entry.file_type().is_file() {
                filetime::set_file_times(entry.path(), sources, sources).unwrap();
            }
        }
    }
    build(&p, "a", flag).run();
    p
}

fn ago(seconds: i64) -> FileTime {
    FileTime::from_unix_time(FileTime::now().unix_seconds() - seconds, 0)
}

fn tree(name: &str) -> PathBuf {
    paths::root().join(name)
}

fn git_dir(name: &str) -> PathBuf {
    paths::root().join(format!("{name}-git"))
}

/// `cargo build -v` in tree `name` with that tree's environment and its
/// carried-times table when it has one, and with the tree and its git dir as
/// relocation roots when `flag` is set.
fn build(p: &Project, name: &str, flag: bool) -> Execs {
    let mut execs = p.cargo("build -v");
    execs
        .cwd(tree(name))
        .env("RELOC_TOOL", tree(name).join("tools/bin/tool"))
        .env("RELOC_GIT_DIR", git_dir(name));
    if flag {
        execs.arg(format!(
            "-Z{FEATURE}={},{}",
            tree(name).display(),
            git_dir(name).display()
        ));
    }
    if carried_times(name).exists() {
        execs.arg(format!("-Z{CARRIED}={}", carried_times(name).display()));
    }
    execs.masquerade_as_nightly_cargo(&[FEATURE, CARRIED]);
    execs
}

fn carried_times(name: &str) -> PathBuf {
    paths::root().join(format!("{name}-carried-times"))
}

/// What the EW-9 seeder does: copy tree `a`'s build directory to `name` with
/// its times, check out `a`'s sources and git dir afresh (every file newer
/// than the copied build), and record in a carried-times table the original's
/// time for each copied source whose bytes are the original's.
fn relocate(name: &str) {
    copy_tree(&tree("a"), &tree(name));
    copy_tree(&git_dir("a"), &git_dir(name));
    let mut table = String::from("trust-carried-times/v1\n");
    for (from_root, to_root) in [(tree("a"), tree(name)), (git_dir("a"), git_dir(name))] {
        for entry in walkdir::WalkDir::new(&to_root) {
            let entry = entry.unwrap();
            let rest = entry.path().strip_prefix(&to_root).unwrap();
            if !entry.file_type().is_file() || rest.starts_with("target") {
                continue;
            }
            let original = from_root.join(rest);
            if fs::read(&original).unwrap() == fs::read(entry.path()).unwrap() {
                let time = FileTime::from_last_modification_time(&fs::metadata(&original).unwrap());
                table.push_str(&carried_entry(entry.path(), time));
            }
        }
    }
    fs::write(carried_times(name), table).unwrap();
}

/// One line of a carried-times table: `path` as it is now, carrying `time`.
#[cfg(unix)]
fn carried_entry(path: &Path, time: FileTime) -> String {
    use std::os::unix::fs::MetadataExt;
    let meta = fs::metadata(path).unwrap();
    format!(
        "{} {} {} {} {} {} {} {} {}\n",
        meta.dev(),
        meta.ino(),
        meta.len(),
        meta.mtime(),
        meta.mtime_nsec(),
        meta.ctime(),
        meta.ctime_nsec(),
        time.unix_seconds(),
        time.nanoseconds()
    )
}

#[cfg(not(unix))]
fn carried_entry(_path: &Path, _time: FileTime) -> String {
    String::new()
}

/// Copies `from` to `to`: the build directory (`target`) with its times, as
/// a clone keeps them, and every other file as a checkout writes it, now.
fn copy_tree(from: &Path, to: &Path) {
    for entry in walkdir::WalkDir::new(from) {
        let entry = entry.unwrap();
        let rest = entry.path().strip_prefix(from).unwrap();
        let dst = to.join(rest);
        if entry.file_type().is_dir() {
            fs::create_dir_all(&dst).unwrap();
        } else {
            fs::copy(entry.path(), &dst).unwrap();
            let mtime = if rest.starts_with("target") {
                FileTime::from_last_modification_time(&entry.metadata().unwrap())
            } else {
                FileTime::now()
            };
            filetime::set_file_times(&dst, mtime, mtime).unwrap();
        }
    }
}

/// Edits `path`, newer than the seeded build directory.
fn edit(path: &Path, contents: &str) {
    fs::write(path, contents).unwrap();
}

#[cargo_test]
fn relocated_tree_is_fresh_and_names_its_own_files() {
    let p = seed(true);
    relocate("b");

    // The original's watched files no longer matter to the copy.
    edit(&tree("a").join("shared/watched.txt"), "edited");
    edit(&git_dir("a").join("HEAD"), "edited");
    build(&p, "b", true)
        .with_stderr_data(str![[r#"
[FRESH] pkg v0.1.0 ([ROOT]/b/pkg)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();

    // The replayed directives name the copy: recompiling the library links
    // the copy's search path, and the build script does not run.
    edit(
        &tree("b").join("pkg/src/lib.rs"),
        r#"pub const HEAD: &str = include_str!(env!("RELOC_GIT_HEAD")); pub fn f() {}"#,
    );
    build(&p, "b", true)
        .with_stderr_data(str![[r#"
[DIRTY] pkg v0.1.0 ([ROOT]/b/pkg): the file `pkg/src/lib.rs` has changed ([TIME_DIFF_AFTER_LAST_BUILD])
[COMPILING] pkg v0.1.0 ([ROOT]/b/pkg)
[RUNNING] `rustc --crate-name pkg [..] -L native=[ROOT]/b/native/lib`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .with_stderr_does_not_contain("[ROOT]/a")
        .run();
}

#[cargo_test]
fn relocated_tree_without_the_flag_reruns() {
    // Seeded with the flag, rebuilt without it.
    let p = seed(true);
    relocate("b");
    build(&p, "b", false)
        .with_stderr_data(str![[r#"
[DIRTY] pkg v0.1.0 ([ROOT]/b/pkg): the rerun-if-changed instructions changed
[COMPILING] pkg v0.1.0 ([ROOT]/b/pkg)
[RUNNING] `[ROOT]/b/target/debug/build/pkg/[HASH]/out/build_script_build`
[RUNNING] `rustc --crate-name pkg [..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test]
fn relocated_tree_built_without_the_flag_reruns() {
    // The baseline the flag fixes: neither build used it.
    let p = seed(false);
    relocate("b");
    build(&p, "b", false)
        .with_stderr_data(str![[r#"
[DIRTY] pkg v0.1.0 ([ROOT]/b/pkg): the env variable RELOC_TOOL changed
[COMPILING] pkg v0.1.0 ([ROOT]/b/pkg)
[RUNNING] `[ROOT]/b/target/debug/build/pkg/[HASH]/out/build_script_build`
[RUNNING] `rustc --crate-name pkg [..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test]
fn relocated_tree_reruns_when_its_watched_file_changes() {
    let p = seed(true);
    relocate("b");
    edit(&tree("b").join("shared/watched.txt"), "edited");
    build(&p, "b", true)
        .with_stderr_data(str![[r#"
[DIRTY] pkg v0.1.0 ([ROOT]/b/pkg): the file `shared/watched.txt` has changed ([TIME_DIFF_AFTER_LAST_BUILD])
[COMPILING] pkg v0.1.0 ([ROOT]/b/pkg)
[RUNNING] `[ROOT]/b/target/debug/build/pkg/[HASH]/out/build_script_build`
[RUNNING] `rustc --crate-name pkg [..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test]
fn relocated_tree_reruns_when_its_second_root_file_changes() {
    let p = seed(true);
    relocate("b");
    edit(&git_dir("b").join("HEAD"), "edited");
    build(&p, "b", true)
        .with_stderr_data(str![[r#"
[DIRTY] pkg v0.1.0 ([ROOT]/b/pkg): the file `[ROOT]/b-git/HEAD` has changed ([TIME_DIFF_AFTER_LAST_BUILD])
[COMPILING] pkg v0.1.0 ([ROOT]/b/pkg)
[RUNNING] `[ROOT]/b/target/debug/build/pkg/[HASH]/out/build_script_build`
[RUNNING] `rustc --crate-name pkg [..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test]
fn relocated_tree_reruns_when_an_env_value_differs_beyond_the_root() {
    let p = seed(true);
    relocate("b");
    build(&p, "b", true)
        .env("RELOC_TOOL", tree("b").join("tools/bin/tool2"))
        .with_stderr_data(str![[r#"
[DIRTY] pkg v0.1.0 ([ROOT]/b/pkg): the env variable RELOC_TOOL changed
[COMPILING] pkg v0.1.0 ([ROOT]/b/pkg)
[RUNNING] `[ROOT]/b/target/debug/build/pkg/[HASH]/out/build_script_build`
[RUNNING] `rustc --crate-name pkg [..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test]
fn in_place_with_the_flag_keeps_every_rerun() {
    let p = seed(true);
    build(&p, "a", true)
        .with_stderr_data(str![[r#"
[FRESH] pkg v0.1.0 ([ROOT]/a/pkg)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();

    if is_coarse_mtime() {
        sleep_ms(1000);
    }
    p.change_file("shared/watched.txt", "edited");
    build(&p, "a", true)
        .with_stderr_data(str![[r#"
[DIRTY] pkg v0.1.0 ([ROOT]/a/pkg): the file `shared/watched.txt` has changed ([TIME_DIFF_AFTER_LAST_BUILD])
[COMPILING] pkg v0.1.0 ([ROOT]/a/pkg)
[RUNNING] `[ROOT]/a/target/debug/build/pkg/[HASH]/out/build_script_build`
[RUNNING] `rustc --crate-name pkg [..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();

    build(&p, "a", true)
        .env("RELOC_TOOL", tree("a").join("tools/bin/tool2"))
        .with_stderr_data(str![[r#"
[DIRTY] pkg v0.1.0 ([ROOT]/a/pkg): the env variable RELOC_TOOL changed
[COMPILING] pkg v0.1.0 ([ROOT]/a/pkg)
[RUNNING] `[ROOT]/a/target/debug/build/pkg/[HASH]/out/build_script_build`
[RUNNING] `rustc --crate-name pkg [..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test]
fn malformed_roots_are_refused() {
    let p = project().file("src/lib.rs", "").build();
    p.cargo("build -Ztrust-relocation-roots=relative/path")
        .masquerade_as_nightly_cargo(&[FEATURE])
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] `-Ztrust-relocation-roots` root `relative/path` is not an absolute path

"#]])
        .run();
    p.cargo("build -Ztrust-relocation-roots=/a,,/b")
        .masquerade_as_nightly_cargo(&[FEATURE])
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] `-Ztrust-relocation-roots` has an empty root; expected comma-separated absolute paths

"#]])
        .run();
}

#[cfg(unix)]
#[cargo_test]
fn relocated_tree_without_its_carried_times_rebuilds() {
    // The copy's checkout is newer than its copied build: without the table
    // every unit is stale.
    let p = seed(true);
    relocate("b");
    fs::remove_file(carried_times("b")).unwrap();
    build(&p, "b", true)
        .with_stderr_data(str![[r#"
[DIRTY] pkg v0.1.0 ([ROOT]/b/pkg): the file `[..]` has changed ([TIME_DIFF_AFTER_LAST_BUILD])
[COMPILING] pkg v0.1.0 ([ROOT]/b/pkg)
[RUNNING] `rustc --crate-name build_script_build [..]`
[RUNNING] `[ROOT]/b/target/debug/build/pkg/[HASH]/out/build_script_build`
[RUNNING] `rustc --crate-name pkg [..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .with_stderr_does_not_contain("[ROOT]/a")
        .run();
}

#[cfg(unix)]
#[cargo_test]
fn a_carried_time_ends_when_its_file_is_touched() {
    // Same bytes, rewritten: the carried entry no longer holds, and the file's
    // own (newer) time makes the script run again.
    let p = seed(true);
    relocate("b");
    let watched = tree("b").join("shared/watched.txt");
    let bytes = fs::read(&watched).unwrap();
    fs::write(&watched, bytes).unwrap();
    build(&p, "b", true)
        .with_stderr_data(str![[r#"
[DIRTY] pkg v0.1.0 ([ROOT]/b/pkg): the file `shared/watched.txt` has changed ([TIME_DIFF_AFTER_LAST_BUILD])
[COMPILING] pkg v0.1.0 ([ROOT]/b/pkg)
[RUNNING] `[ROOT]/b/target/debug/build/pkg/[HASH]/out/build_script_build`
[RUNNING] `rustc --crate-name pkg [..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cfg(unix)]
#[cargo_test]
fn output_beside_an_unusable_relocation_record_is_never_replayed() {
    // A record that names another number of roots (or is damaged) cannot say
    // how to re-root the output beside it: the script runs again in the copy.
    let p = seed(true);
    relocate("b");
    let mut records = 0;
    for entry in walkdir::WalkDir::new(tree("b").join("target")) {
        let entry = entry.unwrap();
        if entry.file_name() == "root-relocation" {
            fs::write(entry.path(), b"trust-relocation-roots-v1\0/elsewhere\0\0").unwrap();
            records += 1;
        }
    }
    assert_eq!(records, 1);
    build(&p, "b", true)
        .with_stderr_data(str![[r#"
[DIRTY] pkg v0.1.0 ([ROOT]/b/pkg): [..]
[NOTE] this could happen because of added/removed `cargo::rerun-if` instructions in the build script
[COMPILING] pkg v0.1.0 ([ROOT]/b/pkg)
[RUNNING] `[ROOT]/b/target/debug/build/pkg/[HASH]/out/build_script_build`
[RUNNING] `rustc --crate-name pkg [..] -L native=[ROOT]/b/native/lib`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .with_stderr_does_not_contain("[ROOT]/a")
        .run();
}

#[cargo_test]
fn a_malformed_carried_times_table_is_refused() {
    let p = project().file("src/lib.rs", "").build();
    let table = paths::root().join("carried");
    fs::write(&table, "trust-carried-times/v1\n1 2 3\n").unwrap();
    p.cargo(&format!("build -Z{CARRIED}={}", table.display()))
        .masquerade_as_nightly_cargo(&[CARRIED])
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] -Ztrust-carried-times: [ROOT]/carried line 2 is malformed: `1 2 3`

"#]])
        .run();
}

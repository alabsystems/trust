use std::cell::Cell;
use std::collections::BTreeMap;
use std::process::Command;

use tempfile::TempDir;

use super::*;
use crate::core::build_steps::tool::{SourceType, prepare_tool_cargo};
use crate::core::builder::Builder;
use crate::core::compiler::Compiler;
use crate::core::session::{Mode, RemapScheme, Session};
use crate::utils::tests::TestCtx;
use crate::utils::tests::git::{GitCtx, git_test};

// Trust: exercise the exact native metadata reader used by the Targo build script.
// Its owning Targo formatter configuration applies to the shared source file.
#[rustfmt::skip]
#[path = "../../../../tools/targo/build_commit_info.rs"]
mod targo_commit_info;

fn real_run() -> ExecutionContext {
    ExecutionContext::new(0, false)
}

/// HEAD of the scratch checkout, as `GitInfo::new` reads it.
fn head(ctx: &GitCtx) -> Info {
    let sha = ctx.get_current_commit();
    let commit_date = ctx.run_git(&["log", "-1", "--date=short", "--pretty=format:%cd"]);
    Info { short_sha: sha[..9].to_owned(), sha, commit_date }
}

/// What [`of_sources`] names the scratch checkout's sources now, with the configuration
/// digest `config`. Each call asks git afresh: bootstrap caches git's answers for the
/// life of an execution context.
fn sources_with(ctx: &GitCtx, config: &str) -> Sources {
    of_sources(&real_run(), ctx.get_path(), config, &head(ctx)).expect("git names the sources")
}

fn sources(ctx: &GitCtx) -> Sources {
    sources_with(ctx, "config-a")
}

fn identity(ctx: &GitCtx) -> Info {
    sources(ctx).info
}

fn sha(ctx: &GitCtx) -> String {
    identity(ctx).sha
}

/// A scratch checkout with a compiler, a library, each inert tree, and a build input
/// under one of them.
fn with_checkout(test: impl FnOnce(&mut GitCtx)) {
    git_test(|ctx| {
        ctx.write("compiler/rustc/src/main.rs", "fn main() {}");
        ctx.write("library/core/src/lib.rs", "#![no_core]");
        ctx.write("docs/DECISION_QUEUE.md", "# Decisions");
        ctx.write("reports/run.md", "measured");
        ctx.write("scripts/frozen-files.txt", "compiler/rustc/src/main.rs");
        ctx.write("scripts/check.py", "print()");
        ctx.write("tests/ui/a.rs", "fn main() {}");
        ctx.write("tests/upstream-rust/targo-witness-layout.json", "{}");
        ctx.commit();
        test(ctx);
    });
}

/// Commits everything in the scratch checkout with author and committer date `date`.
fn commit_on(ctx: &GitCtx, date: &str) {
    ctx.run_git(&["add", "."]);
    let status = Command::new("git")
        .current_dir(ctx.get_path())
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("GIT_CONFIG_GLOBAL", "/tmp/nonexistent")
        .env("GIT_AUTHOR_DATE", date)
        .env("GIT_COMMITTER_DATE", date)
        .args(["commit", "-q", "-m", "dated"])
        .status()
        .unwrap();
    assert!(status.success());
}

/// Makes the directory `path` of the scratch checkout a repository with one commit.
fn init_repository(ctx: &GitCtx, path: &str, file: &str) {
    fs::create_dir_all(ctx.get_path().join(path)).unwrap();
    ctx.run_git(&["-C", path, "init"]);
    ctx.run_git(&["-C", path, "config", "user.name", "Tester"]);
    ctx.run_git(&["-C", path, "config", "user.email", "tester@rust-lang.org"]);
    ctx.write(&format!("{path}/{file}"), "pub fn solve() {}");
    ctx.run_git(&["-C", path, "add", "."]);
    ctx.run_git(&["-C", path, "commit", "-m", "first"]);
}

#[test]
fn an_identity_has_a_commits_shape() {
    with_checkout(|ctx| {
        let Info { sha, short_sha, commit_date } = identity(ctx);
        assert_eq!(sha.len(), 40);
        assert!(sha.bytes().all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase()));
        assert_eq!(short_sha, &sha[..9]);
        assert_eq!(commit_date, head(ctx).commit_date);
        assert_eq!(commit_date.len(), "2026-10-16".len());
        assert_ne!(sha, ctx.get_current_commit(), "the identity is not HEAD");
        assert_eq!(identity(ctx).sha, sha, "the same sources give the same identity");
    });
}

// Trust: this key observes source compatibility inputs only. It never replaces
// the full TB1 identity or authorizes a retained runtime from a saved digest.
fn frontend_runtime_key(ctx: &GitCtx, configuration: &str) -> String {
    frontend_runtime_sources(&real_run(), ctx.get_path(), configuration, &head(ctx)).unwrap()
}

#[test]
fn frontend_runtime_sources_allow_only_existing_regular_frontend_rust_contents() {
    with_checkout(|ctx| {
        ctx.write("targo-trust/Cargo.toml", "[package]\nname='frontend'\n");
        ctx.write("targo-trust/src/main.rs", "fn main() {}\n");
        ctx.commit();
        let full = sha(ctx);
        let before = frontend_runtime_key(ctx, "config-a");
        ctx.modify("targo-trust/src/main.rs");
        assert_eq!(before, frontend_runtime_key(ctx, "config-a"));
        assert_ne!(full, sha(ctx), "ordinary TB1 still names changed frontend content");
        ctx.commit();
        assert_eq!(before, frontend_runtime_key(ctx, "config-a"));
        ctx.modify("targo-trust/src/new.rs");
        assert_ne!(
            before,
            frontend_runtime_key(ctx, "config-a"),
            "new source/module graph refuses"
        );
        ctx.commit();
        assert_ne!(before, frontend_runtime_key(ctx, "config-a"));
    });
}

#[test]
fn frontend_runtime_sources_bind_shared_inputs_manifests_configuration_and_data() {
    for changed in [
        "targo-trust/Cargo.toml",
        "targo-trust/build.rs",
        "targo-trust/src/embedded.json",
        "compiler/rustc/src/main.rs",
        "crates/shared/src/lib.rs",
        "Cargo.lock",
        "scripts/frozen-files.txt",
    ] {
        with_checkout(|ctx| {
            ctx.write("targo-trust/src/main.rs", "fn main() {}\n");
            ctx.commit();
            let before = frontend_runtime_key(ctx, "config-a");
            assert_ne!(before, frontend_runtime_key(ctx, "config-b"));
            ctx.modify(changed);
            assert_ne!(before, frontend_runtime_key(ctx, "config-a"), "uncommitted {changed}");
            ctx.commit();
            assert_ne!(before, frontend_runtime_key(ctx, "config-a"), "committed {changed}");
        });
    }
}

#[cfg(unix)]
#[test]
fn frontend_runtime_sources_do_not_mask_removed_retargeted_or_mode_changed_files() {
    use std::os::unix::fs::{PermissionsExt, symlink};
    for variant in 0..3 {
        with_checkout(|ctx| {
            let file = ctx.get_path().join("targo-trust/src/main.rs");
            ctx.write("targo-trust/src/main.rs", "fn main() {}\n");
            ctx.commit();
            let before = frontend_runtime_key(ctx, "config-a");
            match variant {
                0 => fs::remove_file(&file).unwrap(),
                1 => {
                    fs::remove_file(&file).unwrap();
                    symlink("../../Cargo.toml", &file).unwrap();
                }
                2 => fs::set_permissions(&file, fs::Permissions::from_mode(0o755)).unwrap(),
                _ => unreachable!(),
            }
            assert_ne!(before, frontend_runtime_key(ctx, "config-a"));
            ctx.commit();
            assert_ne!(before, frontend_runtime_key(ctx, "config-a"));
        });
    }
}

#[test]
fn a_commit_to_inert_paths_only_keeps_the_identity() {
    with_checkout(|ctx| {
        let before = identity(ctx);
        let commit = ctx.get_current_commit();
        ctx.modify("docs/DECISION_QUEUE.md");
        ctx.modify("docs/design/new-plan.md");
        ctx.modify("reports/run.md");
        ctx.modify("scripts/check.py");
        ctx.modify("tests/ui/a.rs");
        ctx.modify("README.md");
        ctx.modify("AGENTS.md");
        assert_ne!(ctx.commit(), commit);
        let after = identity(ctx);
        assert_eq!(after.sha, before.sha);
        assert_eq!(after.short_sha, before.short_sha);
        assert_eq!(after.commit_date, before.commit_date);
    });
}

#[test]
fn the_date_is_the_newest_source_commits() {
    // Dates after the checkout's first commit, which is made today and touches sources.
    with_checkout(|ctx| {
        ctx.modify("compiler/rustc/src/main.rs");
        commit_on(ctx, "2040-01-01T12:00:00+0000");
        let dated = identity(ctx);
        assert_eq!(dated.commit_date, "2040-01-01");

        // A later commit to inert paths only moves neither the hash nor the date.
        ctx.modify("docs/DECISION_QUEUE.md");
        ctx.modify("README.md");
        commit_on(ctx, "2040-03-01T12:00:00+0000");
        let after = identity(ctx);
        assert_eq!(after.sha, dated.sha);
        assert_eq!(after.commit_date, "2040-01-01");

        // A commit to a build input under an inert tree dates the sources.
        ctx.modify("scripts/frozen-files.txt");
        commit_on(ctx, "2040-04-01T12:00:00+0000");
        assert_eq!(identity(ctx).commit_date, "2040-04-01");
    });
}

#[test]
fn a_commit_under_compiler_or_library_moves_the_identity() {
    with_checkout(|ctx| {
        let first = sha(ctx);
        ctx.modify("compiler/rustc/src/main.rs");
        ctx.commit();
        let second = sha(ctx);
        assert_ne!(second, first);
        ctx.modify("library/core/src/lib.rs");
        ctx.commit();
        assert_ne!(sha(ctx), second);
    });
}

#[test]
fn a_commit_to_a_build_input_under_an_inert_tree_moves_the_identity() {
    with_checkout(|ctx| {
        // Trust: cover every actual embedded input, including additions to the
        // list, without weakening the separate completeness scanner.
        let mut before = sha(ctx);
        for input in BUILD_INPUTS_IN_INERT_TREES {
            ctx.modify(input);
            ctx.commit();
            let after = sha(ctx);
            assert_ne!(after, before, "changing {input} must change the source identity");
            before = after;
        }
    });
}

#[test]
fn a_new_top_level_entry_moves_the_identity() {
    with_checkout(|ctx| {
        let before = sha(ctx);
        ctx.modify("Cargo.lock");
        ctx.commit();
        let lock = sha(ctx);
        assert_ne!(lock, before);
        ctx.modify("data/table.json");
        ctx.commit();
        assert_ne!(sha(ctx), lock);
    });
}

#[test]
fn an_uncommitted_edit_is_named_apart_from_the_clean_tree() {
    with_checkout(|ctx| {
        let clean = sha(ctx);
        ctx.modify("compiler/rustc/src/main.rs");
        let dirty = sha(ctx);
        assert_ne!(dirty, clean);
        ctx.modify("compiler/rustc/src/main.rs");
        let dirtier = sha(ctx);
        assert_ne!(dirtier, dirty, "each state of the edit has its own identity");
        ctx.run_git(&["checkout", "--", "compiler/rustc/src/main.rs"]);
        assert_eq!(sha(ctx), clean, "the reverted tree is the clean tree again");
        ctx.modify("compiler/rustc/src/main.rs");
        ctx.run_git(&["add", "compiler/rustc/src/main.rs"]);
        assert_eq!(sha(ctx), dirty, "staged or not, the worktree is what is named");
    });
}

#[test]
fn source_identity_changes_with_edits_and_source_commits() {
    with_checkout(|ctx| {
        let clean = sources(ctx);
        ctx.modify("library/core/src/lib.rs");
        let dirty = sources(ctx);
        assert_ne!(dirty.info.sha, clean.info.sha);

        ctx.run_git(&["checkout", "--", "library/core/src/lib.rs"]);
        ctx.modify("docs/DECISION_QUEUE.md");
        ctx.commit();
        assert_eq!(sources(ctx).info.sha, clean.info.sha, "inert commits keep it");
        ctx.modify("compiler/rustc/src/main.rs");
        ctx.commit();
        assert_ne!(sources(ctx).info.sha, clean.info.sha, "source commits move it");
    });
}

#[test]
fn a_path_with_spaces_or_bytes_that_are_not_utf8_is_named() {
    with_checkout(|ctx| {
        ctx.write("compiler/a b/c d.rs", "pub fn f() {}");
        ctx.commit();
        let clean = sha(ctx);
        ctx.modify("compiler/a b/c d.rs");
        assert_ne!(sha(ctx), clean);
        ctx.run_git(&["checkout", "--", "compiler/a b/c d.rs"]);
        assert_eq!(sha(ctx), clean);

        // macOS file systems refuse a name that is not UTF-8; Linux ones take any bytes.
        #[cfg(target_os = "linux")]
        {
            use std::ffi::OsStr;
            use std::os::unix::ffi::OsStrExt;
            let name = |dir: &str| ctx.get_path().join(dir).join(OsStr::from_bytes(b"x\xff.rs"));
            fs::write(name("docs"), "draft").unwrap();
            assert_eq!(sha(ctx), clean, "an inert path need not be UTF-8");
            fs::write(name("compiler"), "pub fn g() {}").unwrap();
            let named = sha(ctx);
            assert_ne!(named, clean, "nor a path in the identity");
            fs::write(name("compiler"), "pub fn h() {}").unwrap();
            assert_ne!(sha(ctx), named);
        }
    });
}

#[test]
fn an_uncommitted_edit_of_an_inert_path_keeps_the_identity() {
    with_checkout(|ctx| {
        let clean = sha(ctx);
        ctx.modify("docs/DECISION_QUEUE.md");
        ctx.modify("README.md");
        ctx.modify("scripts/check.py");
        assert_eq!(sha(ctx), clean);
        ctx.modify("scripts/frozen-files.txt");
        assert_ne!(sha(ctx), clean);
        let frozen = sha(ctx);
        ctx.modify("tests/upstream-rust/targo-witness-layout.json");
        assert_ne!(sha(ctx), frozen);
    });
}

#[test]
fn an_untracked_file_counts_outside_the_inert_trees() {
    with_checkout(|ctx| {
        let clean = sha(ctx);
        ctx.write("tests/ui/new.rs", "fn main() {}");
        ctx.write("docs/notes.md", "draft");
        ctx.write("NOTES.md", "draft");
        assert_eq!(sha(ctx), clean);
        ctx.write("compiler/rustc/src/new.rs", "pub fn f() {}");
        let untracked = sha(ctx);
        assert_ne!(untracked, clean);
        fs::remove_file(ctx.get_path().join("compiler/rustc/src/new.rs")).unwrap();
        assert_eq!(sha(ctx), clean);
    });
}

#[test]
fn an_ignored_file_is_not_part_of_the_identity() {
    with_checkout(|ctx| {
        ctx.write(".gitignore", "/build/");
        ctx.commit();
        let clean = sha(ctx);
        ctx.write("build/host/stage1/bin/trustc", "binary");
        assert_eq!(sha(ctx), clean);
    });
}

#[test]
fn only_the_repositorys_own_ignore_rules_hide_a_file() {
    with_checkout(|ctx| {
        let clean = sha(ctx);
        let excludes = TempDir::new().unwrap();
        let file = excludes.path().join("ignore");
        fs::write(&file, "compiler/rustc/src/secret.rs\n").unwrap();
        ctx.run_git(&["config", "core.excludesFile", file.to_str().unwrap()]);
        ctx.write("compiler/rustc/src/secret.rs", "pub fn compiled() {}");
        assert_ne!(sha(ctx), clean, "an excludes file of the user's does not hide it");
    });
}

#[test]
fn a_deleted_file_is_named_apart_from_the_clean_tree() {
    with_checkout(|ctx| {
        let clean = sha(ctx);
        fs::remove_file(ctx.get_path().join("library/core/src/lib.rs")).unwrap();
        assert_ne!(sha(ctx), clean);
    });
}

#[cfg(unix)]
#[test]
fn a_fifo_in_a_directory_that_replaced_a_file_is_named_by_its_kind() {
    with_checkout(|ctx| {
        let clean = sha(ctx);
        // git lists the deleted file, whose path is now a directory that is read whole.
        let path = ctx.get_path().join("library/core/src/lib.rs");
        fs::remove_file(&path).unwrap();
        fs::create_dir(&path).unwrap();
        assert!(Command::new("mkfifo").arg(path.join("pipe")).status().unwrap().success());
        let named = sources(ctx).info.sha;
        assert_ne!(named, clean);
        fs::write(path.join("lib.rs"), "#![no_core]").unwrap();
        assert_ne!(sha(ctx), named);
    });
}

#[test]
fn a_submodule_is_named_by_its_checkout() {
    with_checkout(|ctx| {
        let engine = "first-party/engine";
        init_repository(ctx, engine, "src/lib.rs");
        // The checkout records the engine's commit as a gitlink.
        ctx.commit();
        let pinned = sha(ctx);

        ctx.modify(&format!("{engine}/src/lib.rs"));
        let edited = sha(ctx);
        assert_ne!(edited, pinned, "an edit inside the submodule moves the identity");

        ctx.run_git(&["-C", engine, "commit", "-am", "engine moves"]);
        let moved = sha(ctx);
        assert_ne!(moved, pinned, "a submodule checked out at another commit moves it");
        assert_ne!(moved, edited);

        ctx.commit();
        let repinned = sha(ctx);
        assert_ne!(repinned, pinned, "a new pin moves it");
        assert_ne!(repinned, moved, "a committed pin is named by the tree, not the worktree");
    });
}

#[test]
fn an_untracked_repository_is_named_by_its_head_and_departures() {
    with_checkout(|ctx| {
        let clean = sha(ctx);
        let probe = "crates/probe";
        init_repository(ctx, probe, "src/lib.rs");
        ctx.write(&format!("{probe}/.gitignore"), "/target/");
        ctx.run_git(&["-C", probe, "add", ".gitignore"]);
        ctx.run_git(&["-C", probe, "commit", "-m", "ignore"]);
        let named = sources(ctx);
        assert_ne!(named.info.sha, clean);
        let head = ctx.run_git(&["-C", probe, "rev-parse", "HEAD"]);
        assert!(named.record.contains(&format!("repo {head}\tcrates/probe/\n")));

        // Its own ignore rules hold: its build output is never read.
        ctx.write(&format!("{probe}/target/debug/out"), "built");
        assert_eq!(sha(ctx), named.info.sha);

        ctx.modify(&format!("{probe}/src/lib.rs"));
        assert_ne!(sha(ctx), named.info.sha, "an edit inside it moves the identity");
    });
}

#[test]
fn a_checkout_git_cannot_read_is_refused() {
    let dir = TempDir::new().unwrap();
    let head = Info {
        commit_date: "2026-10-16".to_owned(),
        sha: "3a1cb55f0712c4f1f5b2f1a5d3c3e0f6b0a1c2d3".to_owned(),
        short_sha: "3a1cb55f0".to_owned(),
    };
    let refused = of_sources(&real_run(), dir.path(), "config-a", &head);
    assert!(refused.is_err(), "a directory that is no repository has no name");

    let out = TempDir::new().unwrap();
    assert!(of_build(&real_run(), dir.path(), out.path(), None, &head).is_err());
    assert!(!out.path().join(RECORD_FILE).exists(), "a refused naming records nothing");
}

#[test]
fn sources_named_at_another_head_are_refused() {
    with_checkout(|ctx| {
        let mut stale = head(ctx);
        ctx.modify("compiler/rustc/src/main.rs");
        ctx.commit();
        let error = of_sources(&real_run(), ctx.get_path(), "config-a", &stale)
            .err()
            .expect("HEAD moved since it was read");
        assert!(error.contains("HEAD moved"), "{error}");
        stale = head(ctx);
        assert!(of_sources(&real_run(), ctx.get_path(), "config-a", &stale).is_ok());
    });
}

#[test]
fn the_configuration_is_part_of_the_identity() {
    with_checkout(|ctx| {
        let a = sources_with(ctx, "config-a");
        let b = sources_with(ctx, "config-b");
        assert_ne!(a.info.sha, b.info.sha);
    });
}

#[test]
fn the_configuration_digest_covers_the_file_and_its_includes() {
    let dir = TempDir::new().unwrap();
    let config = dir.path().join("bootstrap.toml");
    let include = dir.path().join("local.toml");
    fs::write(&config, "include = [\"local.toml\"]\n[rust]\nchannel = \"trust\"\n").unwrap();
    fs::write(&include, "[build]\nverbose = 1\n").unwrap();

    let first = config_digest(Some(&config), dir.path());
    assert_eq!(config_digest(Some(&config), dir.path()), first);
    assert_ne!(config_digest(None, dir.path()), first);

    fs::write(&include, "[build]\nverbose = 2\n").unwrap();
    let included = config_digest(Some(&config), dir.path());
    assert_ne!(included, first, "an edit of an included file moves the digest");

    fs::remove_file(&include).unwrap();
    assert_ne!(config_digest(Some(&config), dir.path()), included, "so does its absence");

    fs::write(&config, "[rust]\nchannel = \"trust\"\n").unwrap();
    assert_ne!(config_digest(Some(&config), dir.path()), included);
}

#[test]
fn the_configuration_digest_names_the_checkout_root_by_a_token() {
    // EW-9: the same configuration relative to each worktree's own root names one
    // configuration, so two worktrees of one commit carry one identity.
    let one = TempDir::new().unwrap();
    let two = TempDir::new().unwrap();
    let write = |root: &Path, text: &str| {
        let config = root.join("bootstrap.toml");
        fs::write(&config, text).unwrap();
        config
    };
    let own = |root: &Path| {
        format!(
            "[build]\nrustfmt = \"{0}/build/host/stage0/bin/trustfmt\"\n[install]\nprefix = \"{0}\"\n",
            root.display()
        )
    };
    let a = write(one.path(), &own(one.path()));
    let b = write(two.path(), &own(two.path()));
    assert_eq!(config_digest(Some(&a), one.path()), config_digest(Some(&b), two.path()));

    // A path into the other worktree is not this checkout's root: it is kept.
    let foreign = write(two.path(), &own(one.path()));
    assert_ne!(config_digest(Some(&foreign), two.path()), config_digest(Some(&a), one.path()));

    // Anything else that differs still moves the digest.
    let edited = write(two.path(), &format!("{}[rust]\ndebug = true\n", own(two.path())));
    assert_ne!(config_digest(Some(&edited), two.path()), config_digest(Some(&a), one.path()));
}

#[test]
fn a_root_is_replaced_only_at_a_path_boundary() {
    let roots = vec![b"/a/root".to_vec()];
    assert_eq!(root_normalized(b"\"/a/root/x\"", &roots), b"\"\0root\0/x\"".to_vec());
    assert_eq!(root_normalized(b"\"/a/root\"", &roots), b"\"\0root\0\"".to_vec());
    assert_eq!(root_normalized(b"/a/root", &roots), b"\0root\0".to_vec());
    assert_eq!(root_normalized(b"\"/a/rootx\"", &roots), b"\"/a/rootx\"".to_vec());
    assert_eq!(root_normalized(b"\"/b/a/root\"", &roots), b"\"/b/a/root\"".to_vec());
    assert_eq!(root_normalized(b"/x.y/a/root/z", &roots), b"/x.y/a/root/z".to_vec());
    assert_eq!(root_normalized(b"-L/a/root/lib", &roots), b"-L\0root\0/lib".to_vec());
    assert_eq!(root_normalized(b"dir=/a/root;", &roots), b"dir=\0root\0;".to_vec());
    assert_eq!(
        root_normalized(b"[/a/root:/a/root.old]", &roots),
        b"[\0root\0:/a/root.old]".to_vec()
    );
    // The longest spelling wins when one root contains another.
    let nested = vec![b"/a/root/inner".to_vec(), b"/a/root".to_vec()];
    assert_eq!(root_normalized(b"/a/root/inner/x", &nested), b"\0root\0/x".to_vec());
}

#[test]
fn roots_are_replaced_in_one_pass_the_longest_first() {
    // A main checkout's `.git` lies inside it, and a linked worktree's git directory lies
    // inside the main checkout's: the git directory's replacement is never replaced again.
    let pairs: Vec<(&[u8], &[u8])> = vec![(b"/m", b"/w"), (b"/m/.git", b"/m/.git/worktrees/w")];
    assert_eq!(
        replace_roots(b"/m/.git/modules/x /m/src \"/m\"", &pairs),
        b"/m/.git/worktrees/w/modules/x /w/src \"/w\"".to_vec()
    );
    assert_eq!(replace_roots(b"/m.old /mx /x/m", &pairs), b"/m.old /mx /x/m".to_vec());
}

#[test]
fn the_configuration_digest_follows_nested_includes() {
    let dir = TempDir::new().unwrap();
    let config = dir.path().join("bootstrap.toml");
    fs::create_dir_all(dir.path().join("profiles")).unwrap();
    let middle = dir.path().join("profiles/middle.toml");
    // Resolved beside the file that names it, as bootstrap resolves it.
    let nested = dir.path().join("profiles/nested.toml");
    fs::write(&config, "include = [\"profiles/middle.toml\"]\n").unwrap();
    fs::write(&middle, "include = [\"nested.toml\"]\n[build]\nverbose = 1\n").unwrap();
    fs::write(&nested, "[rust]\ndebug-assertions = false\n").unwrap();

    let first = config_digest(Some(&config), dir.path());
    fs::write(&nested, "[rust]\ndebug-assertions = true\n").unwrap();
    let edited = config_digest(Some(&config), dir.path());
    assert_ne!(edited, first, "an edit two includes down moves the digest");

    // A cycle ends the walk, as bootstrap refuses it.
    fs::write(&nested, "include = [\"middle.toml\"]\n").unwrap();
    let cyclic = config_digest(Some(&config), dir.path());
    assert_ne!(cyclic, edited);
    assert_eq!(config_digest(Some(&config), dir.path()), cyclic);
}

#[test]
fn the_record_file_maps_the_identity_back_to_its_sources() {
    with_checkout(|ctx| {
        let sources = sources(ctx);
        let out = TempDir::new().unwrap();
        write_record(out.path(), &head(ctx), &sources).unwrap();
        let text = fs::read_to_string(out.path().join(RECORD_FILE)).unwrap();
        let mut lines = text.splitn(4, '\n');
        assert_eq!(lines.next().unwrap(), format!("head {}", ctx.get_current_commit()));
        assert_eq!(lines.next().unwrap(), format!("identity {}", sources.info.sha));
        assert_eq!(lines.next().unwrap(), format!("date {}", sources.info.commit_date));
        let record = lines.next().unwrap();
        assert!(record.starts_with(SCHEMA));
        assert_eq!(&digest(record.as_bytes())[..40], sources.info.sha);
        let leftovers: Vec<_> = fs::read_dir(out.path()).unwrap().collect();
        assert_eq!(leftovers.len(), 1, "the record replaces itself whole");
    });
}

#[test]
fn status_records_of_every_shape() {
    let hash = "0".repeat(40);
    let status = [
        "# branch.oid (initial)".to_owned(),
        format!("1 .M N... 100644 100644 100644 {hash} {hash} compiler/a b.rs"),
        format!("1 .M SC.. 160000 160000 160000 {hash} {hash} first-party/engine"),
        format!("2 R. N... 100644 100644 100644 {hash} {hash} R100 library/new name.rs"),
        "library/old name.rs".to_owned(),
        format!("u UU N... 100644 100644 100644 100644 {hash} {hash} {hash} src/x y.rs"),
        "? crates/probe/".to_owned(),
        "! build/".to_owned(),
    ]
    .join("\0");
    let records = status_records(status.as_bytes()).unwrap();
    let paths = |record: &StatusRecord<'_>| -> Vec<String> {
        record.paths.iter().map(|path| quoted(path)).collect()
    };
    assert_eq!(records.len(), 5);
    assert_eq!(paths(&records[0]), ["compiler/a b.rs"]);
    assert!(!records[0].submodule && !records[0].untracked);
    assert_eq!(paths(&records[1]), ["first-party/engine"]);
    assert!(records[1].submodule);
    assert_eq!(paths(&records[2]), ["library/new name.rs", "library/old name.rs"]);
    assert_eq!(paths(&records[3]), ["src/x y.rs"]);
    assert_eq!(paths(&records[4]), ["crates/probe/"]);
    assert!(records[4].untracked);

    assert!(status_records(b"3 what").is_err());
    assert!(status_records(format!("1 .M N... 100644 {hash} x").as_bytes()).is_err());
}

#[test]
fn quoted_names_are_never_shared() {
    assert_eq!(quoted(b"compiler/a b.rs"), "compiler/a b.rs");
    assert_eq!(quoted(b"a\tb"), "a\\tb");
    assert_eq!(quoted(b"a\nb"), "a\\nb");
    assert_eq!(quoted(b"a\\tb"), "a\\\\tb");
    assert_eq!(quoted(b"x\xff.rs"), "x\\xff.rs");
    assert_ne!(quoted(b"x\xff.rs"), quoted("x\u{fffd}.rs".as_bytes()));
}

#[test]
fn inert_paths() {
    for path in [
        "docs",
        "docs/",
        "docs/DECISION_QUEUE.md",
        "reports/a/b.json",
        "scripts/check.py",
        "tests/ui/a.rs",
        "tests/ui",
        "tests/ui/attributes/doc_examples_elsewhere/a.rs",
        "tests/ui/attributes/a.rs",
        "README.md",
        "AGENTS.md",
    ] {
        assert!(is_inert(path), "{path} is inert");
    }
    for path in [
        "scripts/frozen-files.txt",
        "tests/ui/README.md",
        "tests/ui/attributes/doc_examples",
        "tests/ui/attributes/doc_examples/rustc_dump_clauses.rs",
        "compiler/rustc/src/main.rs",
        "library",
        "first-party/engine",
        "crates/trust-router/README.md",
        "src/version",
        "Cargo.lock",
        "bootstrap.example.toml",
        "docsite/index.md",
        "tests.rs",
    ] {
        assert!(!is_inert(path), "{path} is part of the identity");
    }
}

#[test]
fn only_a_dev_stage_1_build_is_named_by_its_sources() {
    assert!(applies("trust", Kind::Build, 1, false));
    assert!(applies("trust", Kind::Check, 1, false));
    assert!(applies("trust", Kind::Test, 1, false));
    assert!(applies("trust", Kind::Build, 0, false));
    assert!(applies("dev", Kind::Build, 1, false));
    assert!(applies("nightly", Kind::Doc, 1, false));

    // What scripts/promote-toolchain.sh seals, and what recreate_bootstrap.py's sealed
    // mode builds, is stage 2.
    assert!(!applies("trust", Kind::Build, 2, false));
    assert!(!applies("trust", Kind::Test, 2, false));
    assert!(!applies("trust", Kind::Dist, 1, false));
    assert!(!applies("trust", Kind::Dist, 2, false));
    assert!(!applies("trust", Kind::Install, 1, false));
    assert!(!applies("stable", Kind::Build, 1, false));
    assert!(!applies("beta", Kind::Build, 1, false));
    assert!(!applies("trust", Kind::Build, 1, true));
}

/// Whether an invocation of bootstrap with these arguments is named by its sources,
/// asked as a run, not a dry run, unless `dry_run`.
fn invocation_names_sources(args: &[&str], dry_run: bool) -> bool {
    let mut config = TestCtx::new().config(args[0]).args(&args[1..]).create_config();
    if !dry_run {
        config.set_dry_run(DryRun::Disabled);
    }
    names_sources(&config)
}

#[test]
fn the_invocation_decides_what_names_a_build() {
    assert!(invocation_names_sources(&["build", "--stage", "1"], false));
    assert!(invocation_names_sources(&["check", "--stage", "1"], false));
    assert!(invocation_names_sources(&["test", "--stage", "1"], false));

    assert!(!invocation_names_sources(&["build", "--stage", "2"], false));
    assert!(!invocation_names_sources(&["dist", "--stage", "1"], false));
    assert!(!invocation_names_sources(&["install", "--stage", "1"], false));
    assert!(!invocation_names_sources(
        &["build", "--stage", "1", "--set", "rust.trust-source-identity=false"],
        false
    ));
    assert!(!invocation_names_sources(
        &["build", "--stage", "1", "--set", "rust.channel=stable"],
        false
    ));
    assert!(!invocation_names_sources(&["build", "--stage", "1"], true), "a --dry-run");
}

fn commit_named_config(kind: &str, stage: u32) -> Config {
    let context = TestCtx::new();
    let builder = context.config(kind).stage(stage).args(&[
        "--set",
        "rust.trust-source-identity=false",
        "--set",
        "rust.remap-debuginfo=true",
    ]);
    // Preserve native admission: stage-0 build/check needs local rebuild,
    // whereas stage-0 tests require their separate explicit permission.
    let builder = if stage == 0 && kind == "test" {
        builder.args(&["--set", "build.compiletest-allow-stage0=true"])
    } else if stage == 0 {
        builder.args(&["--set", "build.local-rebuild=true"])
    } else {
        builder
    };
    let mut config = builder.create_config();
    config.set_dry_run(DryRun::Disabled);
    config
}

#[test]
fn commit_named_private_development_paths_keep_the_exact_head_tuple() {
    let info = Info {
        commit_date: "2026-11-05".into(),
        sha: "0123456789abcdef0123456789abcdef01234567".into(),
        short_sha: "012345678".into(),
    };
    for stage in [0, 1] {
        for kind in ["build", "check", "test"] {
            let mut config = commit_named_config(kind, stage);
            config.rust_info = GitInfo::Present(Some(info.clone()));
            assert!(!names_sources(&config));
            let commit = config.rust_info.clone();
            let naming = select_for_build(&config, &commit, |_| panic!("must keep HEAD")).unwrap();
            assert_eq!(naming.version.sha(), Some(info.sha.as_str()));
            assert_eq!(naming.version.sha_short(), Some(info.short_sha.as_str()));
            assert_eq!(naming.version.commit_date(), Some(info.commit_date.as_str()));
            assert_eq!(naming.remap.as_deref(), Some("trust-dev"), "{kind} stage {stage}");
        }
    }

    // Trust: retain the Session API integration through a real selected request,
    // without asking an unrelated full-envelope readiness check to name HEAD.
    let context = TestCtx::new();
    let selected_config = || {
        let mut config = context
            .config("build")
            .stage(1)
            .path("library/std")
            .args(&[
                "--set",
                "rust.trust-source-identity=false",
                "--set",
                "rust.remap-debuginfo=true",
            ])
            .create_config();
        config.set_dry_run(DryRun::Disabled);
        assert_eq!(
            crate::utils::trust_preparation::PreparationScope::for_config(&config),
            crate::utils::trust_preparation::PreparationScope::RequestSources
        );
        config.rust_info = GitInfo::Present(Some(info.clone()));
        config
    };
    {
        let session = Session::new(selected_config());
        assert_eq!(session.version_info().sha(), Some(info.sha.as_str()));
        assert_eq!(session.version_info().sha_short(), Some(info.short_sha.as_str()));
        assert_eq!(session.version_info().commit_date(), Some(info.commit_date.as_str()));
        assert_eq!(
            session.debuginfo_map_to(RemapScheme::NonCompiler).as_deref(),
            Some("/rustc/trust-dev"),
        );
        assert_eq!(
            session.debuginfo_map_to(RemapScheme::Compiler).as_deref(),
            Some("/rustc-dev/trust-dev"),
        );
    }
    let mut config = selected_config();
    config.rust_remap_debuginfo = false;
    let session = Session::new(config);
    assert_eq!(session.rust_sha(), Some(info.sha.as_str()));
    assert!(session.debuginfo_map_to(RemapScheme::NonCompiler).is_none());
    assert!(session.debuginfo_map_to(RemapScheme::Compiler).is_none());
}

#[test]
fn commit_named_nonprivate_paths_keep_the_commit() {
    let info = Info {
        commit_date: "2026-11-05".into(),
        sha: "0123456789abcdef0123456789abcdef01234567".into(),
        short_sha: "012345678".into(),
    };
    let commit = GitInfo::Present(Some(info.clone()));
    for kind in ["dist", "install", "doc", "bench", "run", "vendor"] {
        let config = commit_named_config(kind, 1);
        let naming = select_for_build(&config, &commit, |_| panic!("must keep HEAD")).unwrap();
        assert_eq!(naming.version.sha(), Some(info.sha.as_str()));
        assert_eq!(naming.remap, None, "{kind}");
    }
    for stage in [2, 3] {
        let config = commit_named_config("build", stage);
        assert!(select_for_build(&config, &commit, |_| panic!()).unwrap().remap.is_none());
    }
    for channel in ["stable", "beta"] {
        let mut config = commit_named_config("build", 1);
        config.channel = channel.into();
        assert!(select_for_build(&config, &commit, |_| panic!()).unwrap().remap.is_none());
    }
    let mut config = commit_named_config("build", 1);
    config.set_dry_run(DryRun::UserSelected);
    assert!(select_for_build(&config, &commit, |_| panic!()).unwrap().remap.is_none());
    // Selecting paths reads the configured request, never the CI downloader's
    // process-global result. This must neither fetch nor grant private paths.
    let mut config = commit_named_config("build", 1);
    config.download_rustc_commit = Some(info.sha.clone());
    let naming = select_for_build(&config, &commit, |_| panic!()).unwrap();
    assert_eq!(naming.version.sha(), Some(info.sha.as_str()));
    assert!(naming.remap.is_none());

    let config = commit_named_config("build", 1);
    for info in [GitInfo::Absent, GitInfo::Present(None), GitInfo::RecordedForTarball(info.clone())]
    {
        let naming = select_for_build(&config, &info, |_| panic!()).unwrap();
        assert_eq!(naming.version.sha(), info.sha());
        assert!(naming.remap.is_none());
    }

    let mut config = commit_named_config("doc", 1);
    config.trust_source_identity = true;
    assert!(
        select_for_build(&config, &commit, |_| {
            Ok(Sources { info: info.clone(), record: String::new() })
        })
        .unwrap()
        .remap
        .is_some(),
        "existing source-named documentation behavior stays intact"
    );
}

mod private_build_cache;

#[test]
fn a_sealed_build_keeps_its_commit() {
    let head = Info {
        commit_date: "2026-10-16".to_owned(),
        sha: "3a1cb55f0712c4f1f5b2f1a5d3c3e0f6b0a1c2d3".to_owned(),
        short_sha: "3a1cb55f0".to_owned(),
    };
    let named = Info {
        commit_date: "2026-10-15".to_owned(),
        sha: "0123456789abcdef0123456789abcdef01234567".to_owned(),
        short_sha: "012345678".to_owned(),
    };
    let asked = Cell::new(0);
    let sources = |_: &Info| {
        asked.set(asked.get() + 1);
        Ok(Sources { info: named.clone(), record: String::new() })
    };

    let commit = GitInfo::Present(Some(head.clone()));
    let sealed = select(&commit, false, sources).unwrap();
    assert_eq!(sealed.version.sha(), Some(head.sha.as_str()));
    assert_eq!(sealed.version.sha_short(), Some(head.short_sha.as_str()));
    assert_eq!(sealed.version.commit_date(), Some(head.commit_date.as_str()));
    assert_eq!(sealed.remap, None, "its debuginfo prefix keeps the commit too");
    assert_eq!(asked.get(), 0, "a sealed build never asks for its sources");

    // A build with no commit to name keeps what it has, dev or not.
    for info in [GitInfo::Absent, GitInfo::Present(None), GitInfo::RecordedForTarball(head.clone())]
    {
        let kept = select(&info, true, sources).unwrap();
        assert_eq!(kept.version.sha(), info.sha());
        assert_eq!(kept.version.commit_date(), info.commit_date());
        assert_eq!(kept.remap, None);
    }
    assert_eq!(asked.get(), 0);

    let dev = select(&commit, true, sources).unwrap();
    assert_eq!(dev.version.sha(), Some(named.sha.as_str()));
    assert_eq!(dev.version.sha_short(), Some(named.short_sha.as_str()));
    assert_eq!(dev.version.commit_date(), Some(named.commit_date.as_str()));
    assert_eq!(dev.remap.as_deref(), Some(DEVELOPMENT_REMAP_LABEL));
    assert_eq!(asked.get(), 1);

    let unnamed = select(&commit, true, |_: &Info| Err("git failed".to_owned()));
    assert_eq!(unnamed.err().as_deref(), Some("git failed"), "unnamed sources never name HEAD");
}

fn named_build_debuginfo_maps(naming: Naming, enabled: bool) -> (Option<String>, Option<String>) {
    use crate::core::session::RemapScheme;

    let context = TestCtx::new();
    let mut config = context.config("build").stage(1).create_config();
    config.rust_remap_debuginfo = enabled;
    let session = Session::new(config);
    assert!(session.name_for_test(naming));
    (
        session.debuginfo_map_to(RemapScheme::Compiler),
        session.debuginfo_map_to(RemapScheme::NonCompiler),
    )
}

#[test]
fn edited_and_committed_dev_builds_keep_paths_but_change_source_identity() {
    with_checkout(|ctx| {
        let initial = sources(ctx).info.sha;
        ctx.modify("docs/DECISION_QUEUE.md");
        ctx.commit();
        assert_eq!(sources(ctx).info.sha, initial, "documentation does not rename sources");

        let mut identities = Vec::new();
        for body in ["fn main() { let _ = 1; }", "fn main() { let _ = 2; }"] {
            let before = sources(ctx).info.sha;
            ctx.write("compiler/rustc/src/main.rs", body);
            let source = sources(ctx);
            assert_ne!(source.info.sha, before, "an edit changes the full source identity");
            identities.push(source.info.sha.clone());
            let naming = select(&GitInfo::Present(Some(head(ctx))), true, |_| Ok(source)).unwrap();
            assert_eq!(
                named_build_debuginfo_maps(naming, true),
                (
                    Some(format!("/rustc-dev/{DEVELOPMENT_REMAP_LABEL}")),
                    Some(format!("/rustc/{DEVELOPMENT_REMAP_LABEL}")),
                ),
                "both production remap schemes must keep paths stable across edits and commits",
            );
            ctx.commit();
            let source = sources(ctx);
            let naming = select(&GitInfo::Present(Some(head(ctx))), true, |_| Ok(source)).unwrap();
            assert_eq!(
                named_build_debuginfo_maps(naming, true),
                (
                    Some(format!("/rustc-dev/{DEVELOPMENT_REMAP_LABEL}")),
                    Some(format!("/rustc/{DEVELOPMENT_REMAP_LABEL}")),
                ),
                "committing an edit must not invalidate an unrelated crate's path flags",
            );
        }
        assert_ne!(identities[0], identities[1], "the compiler versions still identify each edit");
    });
}

#[test]
fn commit_named_and_disabled_debuginfo_maps_keep_their_existing_behavior() {
    let info = Info {
        commit_date: "2026-10-24".to_owned(),
        sha: "0123456789abcdef0123456789abcdef01234567".to_owned(),
        short_sha: "012345678".to_owned(),
    };
    let commit = GitInfo::Present(Some(info.clone()));
    let naming =
        select(&commit, false, |_| panic!("a sealed build must not ask for sources")).unwrap();
    assert_eq!(
        named_build_debuginfo_maps(naming, true),
        (Some(format!("/rustc-dev/{}", info.sha)), Some(format!("/rustc/{}", info.sha))),
    );
    assert_eq!(
        named_build_debuginfo_maps(Naming { version: commit, remap: Some("unused".into()) }, false),
        (None, None),
    );
}

// Trust: exercise the production Session consumer of Naming, rather than
// checking only select's stored field. Dirty sources still change -vV's name;
// only the documented virtual source path stays on the development label.
#[test]
fn session_remap_keeps_development_paths_without_relabeling_the_compiler() {
    for (stage, remap, expected) in
        [(1, Some(DEVELOPMENT_REMAP_LABEL), DEVELOPMENT_REMAP_LABEL), (2, None, "head")]
    {
        for version in ["dirty-source-one", "dirty-source-two"] {
            let identity = Info {
                commit_date: "2026-10-27".into(),
                sha: if stage == 2 { "head".into() } else { version.into() },
                short_sha: "123456789".into(),
            };
            let context = TestCtx::new();
            let config = context
                .config("build")
                .stage(stage)
                .args(&["--set", "rust.remap-debuginfo=true"])
                .create_config();
            let session = Session::new(config);
            assert!(session.name_for_test(Naming {
                version: GitInfo::Present(Some(identity.clone())),
                remap: remap.map(str::to_owned),
            }));
            assert_eq!(session.rust_sha(), Some(identity.sha.as_str()));
            assert_eq!(
                session.debuginfo_map_to(RemapScheme::NonCompiler).as_deref(),
                Some(format!("/rustc/{expected}").as_str())
            );
            assert_eq!(
                session.debuginfo_map_to(RemapScheme::Compiler).as_deref(),
                Some(format!("/rustc-dev/{expected}").as_str())
            );
        }
    }
}

/// The directories `prepare_tool_cargo` is handed by the tool steps whose build scripts
/// read the commit tuple instead of asking git (`core/build_steps/tool.rs`): targo, tippy,
/// targo-miri, trust-analyzer, its proc-macro server and trustfmt.
const TOOLS_THAT_READ_THE_TUPLE: [&str; 6] = [
    "src/tools/targo",
    "src/tools/tippy",
    "src/tools/miri/cargo-miri",
    "src/tools/rust-analyzer",
    "src/tools/rust-analyzer/crates/proc-macro-srv-cli",
    "src/tools/trustfmt",
];

/// The directory of a tool step inside a submodule: the `ay` battery's.
const A_SUBMODULES_TOOL: &str = "first-party/ay/crates/ay";

#[test]
fn a_tool_built_from_the_checkout_is_named_as_the_build_is() {
    let identity = Info {
        commit_date: "2026-10-17".to_owned(),
        sha: "0123456789abcdef0123456789abcdef01234567".to_owned(),
        short_sha: "012345678".to_owned(),
    };
    let version = GitInfo::Present(Some(identity.clone()));
    let submodules = ["first-party/ay".to_owned(), "first-party/ty".to_owned()];
    let asked = Cell::new(0);
    let own = || {
        asked.set(asked.get() + 1);
        GitInfo::Absent
    };
    for tool in TOOLS_THAT_READ_THE_TUPLE {
        let named = tool_commit(Path::new(tool), &submodules, &version, own);
        assert_eq!(named.sha(), Some(identity.sha.as_str()), "{tool}");
        assert_eq!(named.sha_short(), Some(identity.short_sha.as_str()), "{tool}");
        assert_eq!(named.commit_date(), Some(identity.commit_date.as_str()), "{tool}");
    }
    assert_eq!(asked.get(), 0, "a tool of the checkout never asks git about its own directory");

    let theirs = tool_commit(Path::new(A_SUBMODULES_TOOL), &submodules, &version, own);
    assert_eq!(theirs.sha(), None, "a submodule's tool is named by its own repository");
    assert_eq!(asked.get(), 1);
    // A submodule is a path's leading components, never a prefix of a name.
    let next_door = Path::new("first-party/ay-next/crates/x");
    let beside = tool_commit(next_door, &submodules, &version, own);
    assert_eq!(beside.sha(), Some(identity.sha.as_str()));
    assert_eq!(asked.get(), 1);
}

/// The environment `prepare_tool_cargo` gives the cargo of the tool step in each of
/// `paths`, in a build that `version` names and nothing has asked the name of yet, and the
/// checkout that build reads (`Builder::src`, whose `.gitmodules` `prepare_tool_cargo` reads).
fn tool_step_environments(
    version: GitInfo,
    paths: &[&str],
) -> (PathBuf, Vec<BTreeMap<String, String>>) {
    let context = TestCtx::new();
    let build = Session::new(context.config("check").stage(1).create_config());
    let remap = version.sha().map(str::to_owned);
    assert!(build.name_for_test(Naming { version, remap }), "the build is named once");
    let builder = Builder::new(&build);
    let target = builder.config.host_target;
    let environments = paths
        .iter()
        .map(|path| {
            let cargo = prepare_tool_cargo(
                &builder,
                Compiler::new(0, target),
                Mode::ToolRustcPrivate,
                target,
                Kind::Check,
                path,
                SourceType::InTree,
                &[],
            );
            let mut command = cargo.into_cmd();
            command.mark_as_executed(); // Inspect the command without running Cargo.
            command
                .get_envs()
                .filter_map(|(key, value)| {
                    Some((key.to_str()?.to_owned(), value?.to_str()?.to_owned()))
                })
                .collect()
        })
        .collect();
    (builder.src.clone(), environments)
}

/// Each tool step whose build script asked git for HEAD (tippy, targo-miri, trust-analyzer,
/// its proc-macro server, trustfmt) and targo is handed the identity the compiler's version
/// carries, so that a commit which keeps the identity reruns none of their build scripts,
/// and each prints what `trustc -vV` prints. Before Inc 6b only targo was: the others were
/// handed no tuple, ran git, and printed HEAD (or, trustfmt, a stale HEAD).
#[test]
fn every_tool_step_is_handed_the_name_the_compiler_carries() {
    let identity = Info {
        commit_date: "2026-10-17".to_owned(),
        sha: "0123456789abcdef0123456789abcdef01234567".to_owned(),
        short_sha: "012345678".to_owned(),
    };
    let mut tools = TOOLS_THAT_READ_THE_TUPLE.to_vec();
    tools.push(A_SUBMODULES_TOOL);
    let (checkout, named) =
        tool_step_environments(GitInfo::Present(Some(identity.clone())), &tools);
    let (submodules_tool, checkout_tools) = named.split_last().expect("one per tool");
    for (tool, env) in TOOLS_THAT_READ_THE_TUPLE.iter().zip(checkout_tools) {
        let var = |name: &str| env.get(name).map(String::as_str);
        assert_eq!(var("CFG_COMMIT_HASH"), Some(identity.sha.as_str()), "{tool}");
        assert_eq!(var("CFG_SHORT_COMMIT_HASH"), Some(identity.short_sha.as_str()), "{tool}");
        assert_eq!(var("CFG_COMMIT_DATE"), Some(identity.commit_date.as_str()), "{tool}");
        // What the compiler's version carries, that is.
        assert_eq!(var("CFG_COMMIT_HASH"), var("CFG_VER_HASH"), "{tool}");
        assert_eq!(var("CFG_COMMIT_DATE"), var("CFG_VER_DATE"), "{tool}");
    }
    // A submodule's tool is handed what `git_info` of its own directory names. The `ay`
    // battery's crate directory holds neither a `.git` nor a `git-commit-info`, so that is no
    // tuple at all, in any checkout. This case reads the checkout's own `.gitmodules`, as
    // `prepare_tool_cargo` does: without one the `ay` step is a tool of the checkout.
    assert!(
        build_helper::util::parse_gitmodules(&checkout).iter().any(|path| path == "first-party/ay"),
        "the checkout's .gitmodules lists the ay battery, which this case needs"
    );
    for name in ["CFG_COMMIT_HASH", "CFG_SHORT_COMMIT_HASH", "CFG_COMMIT_DATE"] {
        assert_eq!(submodules_tool.get(name), None, "{A_SUBMODULES_TOOL}: {name}");
    }

    // A build whose naming holds HEAD's commit hands each of them that commit, which is
    // what their own git asked for before. That stage 2, dist, install and the off switch
    // are named by HEAD's commit is for `names_sources`' and `select`'s own cases to show
    // (`a_sealed_build_keeps_its_commit`), not this one.
    let head = Info {
        commit_date: "2026-10-16".to_owned(),
        sha: "3a1cb55f0712c4f1f5b2f1a5d3c3e0f6b0a1c2d3".to_owned(),
        short_sha: "3a1cb55f0".to_owned(),
    };
    let (_, sealed) =
        tool_step_environments(GitInfo::Present(Some(head.clone())), &TOOLS_THAT_READ_THE_TUPLE);
    for (tool, env) in TOOLS_THAT_READ_THE_TUPLE.iter().zip(&sealed) {
        assert_eq!(env.get("CFG_COMMIT_HASH"), Some(&head.sha), "{tool}");
        assert_eq!(env.get("CFG_SHORT_COMMIT_HASH"), Some(&head.short_sha), "{tool}");
        assert_eq!(env.get("CFG_COMMIT_DATE"), Some(&head.commit_date), "{tool}");
    }

    // A build that omits its git information hands no tuple, and the tools ask git as before.
    let (_, omitted) = tool_step_environments(GitInfo::Present(None), &TOOLS_THAT_READ_THE_TUPLE);
    for (tool, env) in TOOLS_THAT_READ_THE_TUPLE.iter().zip(&omitted) {
        for name in ["CFG_COMMIT_HASH", "CFG_SHORT_COMMIT_HASH", "CFG_COMMIT_DATE"] {
            assert_eq!(env.get(name), None, "{tool}: {name}");
        }
    }
}

/// Every file under an inert tree that a build reads is listed in
/// [`BUILD_INPUTS_IN_INERT_TREES`]. A build reads what code that is not a test includes
/// (`include!`, `include_str!`, `include_bytes!`, beside the file or, through
/// `concat!(env!("CARGO_MANIFEST_DIR"), ..)`, beside its manifest), an existing path a
/// build script's string literal names, and a manifest's `path`, `build` and `members`
/// values. Test code is a file under a `tests`, `benches`, `examples` or `fixtures`
/// directory, a `tests.rs`, and an inline `#[cfg(test)]` module; comment lines are not
/// code. The checkout is the one this bootstrap was built from, read through git's index.
#[test]
fn every_build_input_under_an_inert_tree_is_listed() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let listing = Command::new("git")
        .current_dir(&root)
        .args(["ls-files", "-z", "--", "*.rs", "*Cargo.toml"])
        .output()
        .unwrap();
    assert!(listing.status.success(), "git ls-files in {}", root.display());
    let mut unlisted = Vec::new();
    for file in listing.stdout.split(|&byte| byte == 0).filter(|file| !file.is_empty()) {
        let file = std::str::from_utf8(file).expect("the checkout's code has UTF-8 names");
        if is_inert(file) || scan::is_test_path(file) {
            continue;
        }
        // A file the worktree no longer holds, or one that is not text, reads nothing.
        let Ok(text) = fs::read_to_string(root.join(file)) else { continue };
        let dir = file.rsplit_once('/').map_or("", |(dir, _)| dir);
        let mut reads = Vec::new();
        if file.ends_with("Cargo.toml") {
            reads.extend(scan::manifest_values(&text).into_iter().map(|value| (dir, value)));
        } else {
            let code = scan::production_code(&text);
            for (beside_manifest, literal) in scan::includes(&code) {
                let base =
                    if beside_manifest { scan::manifest_dir(&root, file) } else { Some(dir) };
                let Some(base) = base else { continue };
                reads.push((base, literal.trim_start_matches('/').to_owned()));
            }
            if file == "build.rs" || file.ends_with("/build.rs") {
                let named = scan::literals(&code).into_iter().filter(|literal| {
                    literal.contains('/')
                        && scan::resolve(dir, literal).is_some_and(|path| root.join(path).exists())
                });
                reads.extend(named.map(|literal| (dir, literal)));
            }
        }
        for (base, read) in reads {
            if let Some(path) = scan::resolve(base, &read)
                && is_inert(&path)
            {
                unlisted.push(format!("{file} reads {path}"));
            }
        }
    }
    assert!(
        unlisted.is_empty(),
        "a build reads these files under an inert tree; list each in \
         BUILD_INPUTS_IN_INERT_TREES, or the identity does not change when they do:\n{}",
        unlisted.join("\n")
    );
}

/// What [`every_build_input_under_an_inert_tree_is_listed`] reads of the checkout.
mod scan {
    use std::path::Path;

    /// Whether `file` is test code by its path alone.
    pub(super) fn is_test_path(file: &str) -> bool {
        let mut components: Vec<&str> = file.split('/').collect();
        let name = components.pop().unwrap_or_default();
        name == "tests.rs"
            || components.iter().any(|component| {
                matches!(*component, "tests" | "benches" | "examples" | "fixtures")
            })
    }

    /// `text` without its comment lines and its inline `#[cfg(test)]` modules, which
    /// end at the closing brace indented as their `mod` line is (the code is formatted).
    pub(super) fn production_code(text: &str) -> String {
        let lines: Vec<&str> = text.lines().collect();
        let mut code = String::new();
        let mut index = 0;
        while index < lines.len() {
            let line = lines[index];
            if line.trim() == "#[cfg(test)]" {
                let mut next = index + 1;
                while next < lines.len() && lines[next].trim_start().starts_with("#[") {
                    next += 1;
                }
                if let Some(module) = lines.get(next) {
                    let item = module.trim_start();
                    let inline = ["mod ", "pub mod ", "pub(crate) mod ", "pub(super) mod "]
                        .iter()
                        .any(|start| item.starts_with(start))
                        && item.ends_with('{');
                    if inline {
                        let close = format!("{}}}", &module[..module.len() - item.len()]);
                        let mut end = next + 1;
                        while end < lines.len() && lines[end] != close {
                            end += 1;
                        }
                        index = end + 1;
                        continue;
                    }
                }
            }
            if !line.trim_start().starts_with("//") {
                code.push_str(line);
                code.push('\n');
            }
            index += 1;
        }
        code
    }

    fn skip_space(text: &str, at: usize) -> usize {
        at + (text[at..].len() - text[at..].trim_start().len())
    }

    /// The string literal (plain or raw) at `at`, and where it ends.
    fn literal_at(text: &str, at: usize) -> Option<(String, usize)> {
        let rest = &text[at..];
        if let Some(body) = rest.strip_prefix('"') {
            let end = body.find('"')?;
            return Some((body[..end].to_owned(), at + 1 + end + 1));
        }
        let raw = rest.strip_prefix('r')?;
        let hashes = raw.len() - raw.trim_start_matches('#').len();
        let body = raw[hashes..].strip_prefix('"')?;
        let close = format!("\"{}", "#".repeat(hashes));
        let end = body.find(&close)?;
        Some((body[..end].to_owned(), at + 1 + hashes + 1 + end + close.len()))
    }

    /// The paths `code` includes, each with whether it is relative to the manifest
    /// directory (`concat!(env!("CARGO_MANIFEST_DIR"), ..)`) rather than the file.
    pub(super) fn includes(code: &str) -> Vec<(bool, String)> {
        let mut found = Vec::new();
        for name in ["include_str!", "include_bytes!", "include!"] {
            let mut from = 0;
            while let Some(offset) = code[from..].find(name) {
                let start = from + offset;
                from = start + name.len();
                let joined = code[..start]
                    .chars()
                    .next_back()
                    .is_some_and(|before| before.is_alphanumeric() || before == '_');
                if joined {
                    continue;
                }
                let mut at = skip_space(code, from);
                let Some(rest) = code[at..].strip_prefix('(') else { continue };
                at = skip_space(code, code.len() - rest.len());
                let mut beside_manifest = false;
                if code[at..].starts_with("concat!") {
                    let manifest =
                        ["concat!", "(", "env!", "(", "\"CARGO_MANIFEST_DIR\"", ")", ","];
                    let mut matched = true;
                    for token in manifest {
                        at = skip_space(code, at);
                        if !code[at..].starts_with(token) {
                            matched = false;
                            break;
                        }
                        at += token.len();
                    }
                    if !matched {
                        continue;
                    }
                    at = skip_space(code, at);
                    beside_manifest = true;
                }
                if let Some((literal, _)) = literal_at(code, at) {
                    found.push((beside_manifest, literal));
                }
            }
        }
        found
    }

    /// Every plain string literal of `code`.
    pub(super) fn literals(code: &str) -> Vec<String> {
        let mut found = Vec::new();
        let mut from = 0;
        while let Some(offset) = code[from..].find('"') {
            let start = from + offset;
            match literal_at(code, start) {
                Some((literal, end)) => {
                    found.push(literal);
                    from = end;
                }
                None => break,
            }
        }
        found
    }

    /// The `path`, `build` and `members` values of a manifest.
    pub(super) fn manifest_values(text: &str) -> Vec<String> {
        let mut found = Vec::new();
        let mut in_members = false;
        for line in text.lines() {
            let line = if line.trim_start().starts_with('#') { "" } else { line };
            if in_members {
                found.extend(literals(line));
                in_members = !line.contains(']');
                continue;
            }
            let trimmed = line.trim_start();
            if let Some(rest) = trimmed.strip_prefix("members")
                && let Some(rest) = rest.trim_start().strip_prefix('=')
            {
                found.extend(literals(rest));
                in_members = !rest.contains(']');
                continue;
            }
            for key in ["path", "build"] {
                let mut from = 0;
                while let Some(offset) = line[from..].find(key) {
                    let start = from + offset;
                    from = start + key.len();
                    let joined = line[..start].chars().next_back().is_some_and(|before| {
                        before.is_alphanumeric() || matches!(before, '_' | '-' | '.')
                    });
                    let at = skip_space(line, from);
                    if joined || !line[at..].starts_with('=') {
                        continue;
                    }
                    if let Some((literal, _)) = literal_at(line, skip_space(line, at + 1)) {
                        found.push(literal);
                    }
                }
            }
        }
        found
    }

    /// The directory of the manifest nearest above `file`, relative to `root`.
    pub(super) fn manifest_dir<'a>(root: &Path, file: &'a str) -> Option<&'a str> {
        let mut dir = file.rsplit_once('/').map_or("", |(dir, _)| dir);
        loop {
            if root.join(dir).join("Cargo.toml").exists() {
                return Some(dir);
            }
            dir = dir
                .rsplit_once('/')
                .map(|(parent, _)| parent)
                .or_else(|| (!dir.is_empty()).then_some(""))?;
        }
    }

    /// `relative` resolved against the directory `base` of the checkout, `None` when it
    /// leaves the checkout or names its root.
    pub(super) fn resolve(base: &str, relative: &str) -> Option<String> {
        let mut parts: Vec<&str> = base.split('/').filter(|part| !part.is_empty()).collect();
        for part in relative.split('/') {
            match part {
                "" | "." => {}
                ".." => {
                    parts.pop()?;
                }
                part => parts.push(part),
            }
        }
        (!parts.is_empty()).then(|| parts.join("/"))
    }
}

#[test]
fn independent_tool_remap_uses_exact_component_boundary() {
    let components = [
        (IndependentToolComponent::Ay, "first-party/ay/crates/ay"),
        (IndependentToolComponent::Ty, "first-party/ty/crates/tla-cli"),
        (IndependentToolComponent::Clean, "first-party/clean/crates/clean"),
    ];
    let submodules: Vec<_> = components.iter().map(|(c, _)| c.root().to_owned()).collect();
    for (component, recipe) in components {
        assert_eq!(independent_tool_component(Path::new(recipe), &submodules), Some(component));
        assert_eq!(independent_tool_component(Path::new(recipe), &[]), None);
        let wrong = [format!("{}-neighbor", component.root())];
        assert_eq!(independent_tool_component(Path::new(recipe), &wrong), None);
        assert_eq!(
            independent_tool_component(Path::new(&format!("{recipe}-other")), &submodules),
            None
        );
    }
    for path in [
        "src/tools/targo",
        "targo-trust",
        "compiler/rustc",
        "first-party/ay-next/crates/ay",
        "first-party/ty/crates/tla-core",
        "first-party/clean/crates/clean-cli",
    ] {
        assert_eq!(independent_tool_component(Path::new(path), &submodules), None, "{path}");
    }
}

#[test]
fn independent_component_remap_tracks_all_dirty_inputs() {
    for component in [
        IndependentToolComponent::Ay,
        IndependentToolComponent::Ty,
        IndependentToolComponent::Clean,
    ] {
        with_checkout(|ctx| {
            let original = GitInfo::Present(Some(head(ctx)));
            let label =
                |info: &GitInfo| component_remap(&real_run(), ctx.get_path(), info, component);
            let clean = label(&original).unwrap().unwrap();
            assert_eq!(
                clean,
                format!("/rustc/{}/{}", component.namespace(), ctx.get_current_commit())
            );
            for path in [
                "compiler/rustc/src/main.rs",
                "README.md",
                "scripts/check.py",
                "tests/ui/a.rs",
                "docs/DECISION_QUEUE.md",
                "untracked-input",
            ] {
                let previous = label(&original).unwrap();
                ctx.write(path, "changed component input");
                let dirty = label(&original).unwrap();
                assert_ne!(
                    dirty, previous,
                    "{path} must be named even where Trust considers it inert"
                );
                assert_ne!(dirty.as_deref(), Some(clean.as_str()));
                assert_eq!(label(&original).unwrap(), dirty);
            }
            ctx.commit();
            assert!(label(&original).is_err(), "stale own commit must refuse");
        });
        assert_eq!(
            component_remap(&real_run(), Path::new("absent"), &GitInfo::Absent, component).unwrap(),
            None
        );
        assert_eq!(
            component_remap(&real_run(), Path::new("absent"), &GitInfo::Present(None), component)
                .unwrap(),
            None
        );
    }
}

#[test]
fn independent_component_remap_uses_nested_repository_not_parent_commit() {
    for (component, recipe, file) in [
        (IndependentToolComponent::Ay, "first-party/ay/crates/ay", "crates/ay/src/lib.rs"),
        (
            IndependentToolComponent::Ty,
            "first-party/ty/crates/tla-cli",
            "crates/tla-cli/src/lib.rs",
        ),
        (
            IndependentToolComponent::Clean,
            "first-party/clean/crates/clean",
            "crates/clean/src/lib.rs",
        ),
    ] {
        with_checkout(|ctx| {
            init_repository(ctx, component.root(), file);
            let submodules = [component.root().to_owned()];
            assert_eq!(independent_tool_component(Path::new(recipe), &submodules), Some(component));
            let root = ctx.get_path().join(component.root());
            let own = || GitInfo::new(false, &root, &real_run());
            let info = tool_commit(
                Path::new(recipe),
                &submodules,
                &GitInfo::Present(Some(head(ctx))),
                own,
            );
            let label = |info: &GitInfo| component_remap(&real_run(), &root, info, component);
            let original = label(&info).unwrap().unwrap();
            assert_eq!(
                original,
                format!("/rustc/{}/{}", component.namespace(), info.sha().unwrap())
            );
            assert_ne!(info.sha(), Some(head(ctx).sha.as_str()));
            ctx.write("src/tools/targo/main.rs", "unrelated parent change");
            ctx.commit();
            let after_parent = tool_commit(
                Path::new(recipe),
                &submodules,
                &GitInfo::Present(Some(head(ctx))),
                own,
            );
            assert_eq!(label(&after_parent).unwrap().as_deref(), Some(original.as_str()));
            let mut previous = original;
            for path in [file, "README.md", "docs/new.md", "scripts/new.py", "untracked.rs"] {
                ctx.write(&format!("{}/{path}", component.root()), "new component input");
                let dirty = label(&info).unwrap().unwrap();
                assert_ne!(dirty, previous, "{path}");
                previous = dirty;
            }
            assert_eq!(label(&GitInfo::new(true, &root, &real_run())).unwrap(), None);
            assert_eq!(
                label(&GitInfo::new(false, &root.join(file).parent().unwrap(), &real_run()))
                    .unwrap(),
                None
            );
        });
    }
}

#[test]
fn independent_component_namespaces_do_not_alias_the_same_commit() {
    with_checkout(|ctx| {
        let info = GitInfo::Present(Some(head(ctx)));
        let labels: std::collections::BTreeSet<_> = [
            IndependentToolComponent::Ay,
            IndependentToolComponent::Ty,
            IndependentToolComponent::Clean,
        ]
        .into_iter()
        .map(|component| {
            component_remap(&real_run(), ctx.get_path(), &info, component).unwrap().unwrap()
        })
        .collect();
        assert_eq!(labels.len(), 3);
    });
}

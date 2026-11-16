//! Tests for displaying the cargo version.

use crate::prelude::*;
use crate::utils::cargo_process;
use cargo_test_support::{Execs, Project, git, project};
use std::fs;

const LABEL_FIRST: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\naaaaaaaaa\n2026-10-24\n";
const LABEL_SECOND: &str = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\nbbbbbbbbb\n2026-10-24\n";

// Trust: exercise the real discovery helper through Cargo's build-script
// freshness owner. The trace lives inside the package, and Cargo also writes
// target/OUT_DIR, so a recursive package-root watch would invalidate itself.
fn diagnostic_label_fixture() -> Project {
    project()
        .no_manifest()
        .file("git-commit-info", LABEL_FIRST)
        .file("x.py", "fixture\n")
        .file("src/ci/channel", "fixture\n")
        .file("compiler/rustc/fixture", "fixture\n")
        .file("targo-trust/Cargo.toml", "fixture\n")
        .file(
            "src/tools/targo/Cargo.toml",
            r#"
            [package]
            name = "label_fixture"
            version = "0.1.0"
            edition = "2024"
        "#,
        )
        .file("src/tools/targo/src/lib.rs", "pub fn fixture() {}\n")
        .file(
            "src/tools/targo/build_commit_info.rs",
            include_str!("../../build_commit_info.rs"),
        )
        .file(
            "src/tools/targo/build.rs",
            r#"
            #[allow(dead_code)]
            mod build_commit_info;
            fn main() {
                println!("cargo:rerun-if-changed=build.rs");
                for name in build_commit_info::BOOTSTRAP_COMMIT_ENV {
                    println!("cargo:rerun-if-env-changed={name}");
                }
                println!("cargo:rerun-if-env-changed=CFG_OMIT_GIT_HASH");
                let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
                let found = build_commit_info::discover(root, false).unwrap();
                for path in found.rerun_if_changed {
                    println!("cargo:rerun-if-changed={}", path.display());
                }
                let label = found.info.map(|info| info.hash).unwrap_or("unbound".into());
                let trace = root.join("observed-label");
                let count = std::fs::read_to_string(&trace).ok()
                    .and_then(|prior| prior.lines().nth(1)?.parse::<u32>().ok())
                    .unwrap_or(0) + 1;
                std::fs::write(trace, format!("{label}\n{count}\n")).unwrap();
                // Include an ordinary generated build output in the fixture.
                std::fs::write(std::path::Path::new(&std::env::var_os("OUT_DIR").unwrap())
                    .join("generated"), "generated\n").unwrap();
            }
        "#,
        )
        .build()
}

fn diagnostic_label_command(p: &Project, command: &str) -> Execs {
    let mut command = p.cargo(&format!(
        "{command} --manifest-path src/tools/targo/Cargo.toml"
    ));
    for name in [
        "CFG_COMMIT_HASH",
        "CFG_SHORT_COMMIT_HASH",
        "CFG_COMMIT_DATE",
        "CFG_OMIT_GIT_HASH",
    ] {
        command.env_remove(name);
    }
    command
}

fn assert_diagnostic_label_fresh(p: &Project) {
    // Trust: the native fixture shim also discloses its unverified lane.
    // Require Cargo's freshness and completion rows; each caller separately
    // checks the build-script execution counter and selected label.
    diagnostic_label_command(p, "check -v")
        .with_stderr_contains("[FRESH] label_fixture v0.1.0 ([ROOT]/foo/src/tools/targo)")
        .with_stderr_contains(
            "[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s",
        )
        .run();
}

fn label_trace(p: &Project) -> String {
    p.read_file("src/tools/targo/observed-label")
}

fn label_repository(root: &std::path::Path, contents: &str) -> String {
    let fixture = git::repo(root).file("fixture-source", contents).build();
    let hash = fixture.revparse_head();
    let repository = git2::Repository::open(root).unwrap();
    repository
        .reference("refs/heads/main", hash.parse().unwrap(), true, "fixture")
        .unwrap();
    repository.set_head("refs/heads/main").unwrap();
    hash
}

#[cargo_test]
fn diagnostic_archive_label_is_fresh_and_selected_record_edits_rerun() {
    let p = diagnostic_label_fixture();
    diagnostic_label_command(&p, "check -v").run();
    assert_eq!(
        label_trace(&p),
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n1\n"
    );
    assert_diagnostic_label_fresh(&p);
    assert_diagnostic_label_fresh(&p);
    assert_eq!(
        label_trace(&p),
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n1\n"
    );

    p.root().move_into_the_past();
    p.change_file("git-commit-info", LABEL_SECOND);
    diagnostic_label_command(&p, "check -v").run();
    assert_eq!(
        label_trace(&p),
        "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n2\n"
    );
    assert_diagnostic_label_fresh(&p);

    // A newly created higher-priority origin is outside the cached diagnostic
    // contract until clean, unless another watched input independently moves.
    p.root().move_into_the_past();
    p.change_file("src/tools/targo/git-commit-info", LABEL_FIRST);
    assert_diagnostic_label_fresh(&p);
    assert_eq!(
        label_trace(&p),
        "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n2\n"
    );
    diagnostic_label_command(&p, "clean -p label_fixture").run();
    diagnostic_label_command(&p, "check -v").run();
    assert_eq!(
        label_trace(&p),
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n3\n"
    );
    assert_diagnostic_label_fresh(&p);

    p.root().move_into_the_past();
    p.change_file("src/tools/targo/git-commit-info", "malformed\n");
    diagnostic_label_command(&p, "check -v")
        .with_status(101)
        .with_stderr_contains(
            "[..][ROOT]/foo/src/tools/targo/git-commit-info omitted the short hash[..]",
        )
        .run();
    assert_eq!(
        label_trace(&p),
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n3\n",
        "a malformed selected record must refuse without falling back to the valid root record"
    );
}

#[cargo_test]
fn diagnostic_native_label_tracks_actual_branch_advances() {
    let p = diagnostic_label_fixture();
    let first = label_repository(&p.root(), "first");
    diagnostic_label_command(&p, "check -v").run();
    assert_eq!(label_trace(&p), format!("{first}\n1\n"));
    assert_diagnostic_label_fresh(&p);
    let head = fs::read(p.root().join(".git/HEAD")).unwrap();
    p.root().move_into_the_past();
    let repository = git2::Repository::open(p.root()).unwrap();
    let parent = repository.head().unwrap().peel_to_commit().unwrap();
    let tree = parent.tree().unwrap();
    let signature = repository.signature().unwrap();
    let second = repository
        .commit(
            Some("HEAD"),
            &signature,
            &signature,
            "second",
            &tree,
            &[&parent],
        )
        .unwrap();
    assert_eq!(
        fs::read(p.root().join(".git/HEAD")).unwrap(),
        head,
        "the shared branch ref, rather than HEAD bytes, must trigger rerun"
    );
    diagnostic_label_command(&p, "check -v").run();
    assert_eq!(label_trace(&p), format!("{second}\n2\n"));
    assert_diagnostic_label_fresh(&p);
}

#[cargo_test]
fn diagnostic_commondir_creation_requires_clean_reselection() {
    let p = diagnostic_label_fixture();
    let first = label_repository(&p.root(), "first");
    let alternative = p.root().join("alternative");
    let second = label_repository(&alternative, "second");
    assert_ne!(first, second);
    diagnostic_label_command(&p, "check -v").run();
    assert_eq!(label_trace(&p), format!("{first}\n1\n"));
    assert_diagnostic_label_fresh(&p);
    p.root().move_into_the_past();
    let head = fs::read(p.root().join(".git/HEAD")).unwrap();
    let branch = fs::read(p.root().join(".git/refs/heads/main")).unwrap();
    let config = fs::read(p.root().join(".git/config")).unwrap();
    p.change_file(
        ".git/commondir",
        &format!("{}\n", alternative.join(".git").display()),
    );
    assert_diagnostic_label_fresh(&p);
    assert_eq!(label_trace(&p), format!("{first}\n1\n"));
    assert_eq!(fs::read(p.root().join(".git/HEAD")).unwrap(), head);
    assert_eq!(
        fs::read(p.root().join(".git/refs/heads/main")).unwrap(),
        branch
    );
    assert_eq!(fs::read(p.root().join(".git/config")).unwrap(), config);
    diagnostic_label_command(&p, "clean -p label_fixture").run();
    diagnostic_label_command(&p, "check -v").run();
    assert_eq!(label_trace(&p), format!("{second}\n2\n"));
    assert_diagnostic_label_fresh(&p);
}

// Trust: HEAD can remain a symlink while its binding changes. The selected
// ref targets predate the build, so only the link entry can invalidate it.
#[cfg(unix)]
#[cargo_test]
fn diagnostic_native_symlinked_head_retarget_rebuilds_with_older_targets() {
    let p = diagnostic_label_fixture();
    let first = label_repository(&p.root(), "first");
    let second = {
        let repository = git2::Repository::open(p.root()).unwrap();
        let parent = repository.head().unwrap().peel_to_commit().unwrap();
        let tree = parent.tree().unwrap();
        let signature = repository.signature().unwrap();
        let second = repository
            .commit(None, &signature, &signature, "second", &tree, &[&parent])
            .unwrap();
        repository
            .reference("refs/heads/topic", second, true, "fixture")
            .unwrap();
        second.to_string()
    };
    assert_ne!(first, second);
    let head = p.root().join(".git/HEAD");
    let main_ref = p.root().join(".git/refs/heads/main");
    let topic_ref = p.root().join(".git/refs/heads/topic");
    let config = p.root().join(".git/config");
    let old = filetime::FileTime::from_unix_time(1_153_704_088, 0);
    for target in [&main_ref, &topic_ref] {
        filetime::set_file_mtime(target, old).unwrap();
    }
    fs::remove_file(&head).unwrap();
    std::os::unix::fs::symlink("refs/heads/main", &head).unwrap();
    diagnostic_label_command(&p, "check -v").run();
    assert_eq!(label_trace(&p), format!("{first}\n1\n"));
    assert_diagnostic_label_fresh(&p);

    // Use the maintained timestamp helper to separate the new link from the
    // prior output without sleeping or touching either target during retarget.
    p.root().move_into_the_past();
    filetime::set_symlink_file_times(&head, old, old).unwrap();
    assert_diagnostic_label_fresh(&p);
    assert_eq!(label_trace(&p), format!("{first}\n1\n"));
    let before = [&main_ref, &topic_ref, &config].map(|path| {
        (
            fs::read(path).unwrap(),
            fs::metadata(path).unwrap().modified().unwrap(),
        )
    });
    fs::remove_file(&head).unwrap();
    std::os::unix::fs::symlink("refs/heads/topic", &head).unwrap();
    assert_eq!(
        fs::read_link(&head).unwrap(),
        std::path::Path::new("refs/heads/topic")
    );
    for (path, (bytes, modified)) in [&main_ref, &topic_ref, &config].into_iter().zip(before) {
        assert_eq!(fs::read(path).unwrap(), bytes);
        assert_eq!(fs::metadata(path).unwrap().modified().unwrap(), modified);
    }
    diagnostic_label_command(&p, "check -v").run();
    assert_eq!(label_trace(&p), format!("{second}\n2\n"));
    assert_diagnostic_label_fresh(&p);
    assert_eq!(label_trace(&p), format!("{second}\n2\n"));
}

#[cargo_test]
fn simple() {
    let p = project().build();

    p.cargo("version")
        .with_stdout_data(&format!("cargo {}\n", targo::version()))
        .run();

    p.cargo("--version")
        .with_stdout_data(&format!("cargo {}\n", targo::version()))
        .run();

    p.cargo("-V")
        .with_stdout_data(&format!("cargo {}\n", targo::version()))
        .run();
}

#[cargo_test]
fn version_works_without_rustc() {
    let p = project().build();
    p.cargo("version").env("PATH", "").run();
}

#[cargo_test]
fn version_works_with_bad_config() {
    let p = project()
        .file(".cargo/config.toml", "this is not toml")
        .build();
    p.cargo("version").run();
}

#[cargo_test]
fn version_works_with_bad_target_dir() {
    let p = project()
        .file(
            ".cargo/config.toml",
            r#"
                [build]
                target-dir = 4
            "#,
        )
        .build();
    p.cargo("version").run();
}

#[cargo_test]
fn verbose() {
    // This is mainly to check that it doesn't explode.
    // Trust: the expectation below also pins the `trust-repo-commit-hash`
    // provenance line, which is part of the verbose banner's contract.
    //
    // It pins `trust:` for the same reason, and pins it BESIDE `release:` rather than
    // instead of it. `release:` is the Rust COMPAT line that build scripts parse;
    // `trust:` is Trust's own product version. A change that ever made these one field
    // would break this expectation, which is the point of listing both.
    //
    // No parenthetical brand on this line: `cargo_process` invokes the `cargo`
    // frontend, and the brand is emitted only for the `targo` name (see
    // `get_version_string`). The `targo`-invoked shape is covered by the unit tests in
    // `bin/cargo/cli.rs`.
    cargo_process("-vV")
        .with_stdout_data(format!(
            "\
cargo {}
encoded-dep-info-version: {}
release: [..]
trust: [..]
commit-hash: [..]
commit-date: [..]
trust-repo-commit-hash: [..]
host: [HOST_TARGET]
libgit2: [..] (sys:[..] [..])
libcurl: [..] (sys:[..] [..])
...
os: [..]
",
            targo::version(),
            targo::encoded_dep_info_version()
        ))
        .run();
}

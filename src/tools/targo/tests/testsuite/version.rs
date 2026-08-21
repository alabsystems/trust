//! Tests for displaying the cargo version.

use crate::prelude::*;
use crate::utils::cargo_process;
use cargo_test_support::project;

#[cargo_test]
fn simple() {
    let p = project().build();

    p.cargo("version")
        .with_stdout_data(&format!("cargo {}\n", cargo::version()))
        .run();

    p.cargo("--version")
        .with_stdout_data(&format!("cargo {}\n", cargo::version()))
        .run();

    p.cargo("-V")
        .with_stdout_data(&format!("cargo {}\n", cargo::version()))
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
            cargo::version()
        ))
        .run();
}

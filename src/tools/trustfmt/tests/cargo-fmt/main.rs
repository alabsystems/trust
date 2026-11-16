// Integration tests for cargo-fmt.

use std::env;
use std::path::Path;
use std::process::Command;

use rustfmt_config_proc_macro::rustfmt_only_ci_test;

/// Run the cargo-fmt executable and return its output.
fn cargo_fmt(args: &[&str]) -> (String, String) {
    let mut bin_dir = env::current_exe().unwrap();
    bin_dir.pop(); // chop off test exe name

    // Handle Cargo's old and new filesystem layouts
    // * v1: `target/<profile>/deps/test-bin-[HASH][EXE]`
    // * v2: `target/<profile>/build/<pkgname>/[HASH]/out/test-bin-[HASH][EXE]`
    if bin_dir.ends_with("deps") {
        bin_dir.pop();
    } else if bin_dir.ends_with("out") {
        bin_dir.pop(); // chop off `out`
        bin_dir.pop(); // chop off `<hash>`
        bin_dir.pop(); // chop off `<pkgname>`
        bin_dir.pop(); // chop off `build`
    }
    let cmd = bin_dir.join(format!("cargo-fmt{}", env::consts::EXE_SUFFIX));

    // Ensure cargo-fmt runs the rustfmt binary from the local target dir.
    let path = env::var_os("PATH").unwrap_or_default();
    let mut paths = env::split_paths(&path).collect::<Vec<_>>();
    paths.insert(0, bin_dir);
    let new_path = env::join_paths(paths).unwrap();

    match Command::new(&cmd).args(args).env("PATH", new_path).output() {
        Ok(output) => (
            String::from_utf8(output.stdout).expect("utf-8"),
            String::from_utf8(output.stderr).expect("utf-8"),
        ),
        Err(e) => panic!("failed to run `{cmd:?} {args:?}`: {e}"),
    }
}

macro_rules! assert_that {
    ($args:expr, $check:ident $check_args:tt) => {
        let (stdout, stderr) = cargo_fmt($args);
        if !stdout.$check$check_args {
            panic!(
                "Output not expected for cargo-fmt {:?}\n\
                 expected: {}{}\n\
                 actual stdout:\n{}\n\
                 actual stderr:\n{}",
                $args,
                stringify!($check),
                stringify!($check_args),
                stdout,
                stderr
            );
        }
    };
}

#[rustfmt_only_ci_test]
#[test]
fn version() {
    assert_that!(&["--version"], starts_with("rustfmt "));
    assert_that!(&["--version"], starts_with("rustfmt "));
    assert_that!(&["--", "-V"], starts_with("rustfmt "));
    assert_that!(&["--", "--version"], starts_with("rustfmt "));
}

#[rustfmt_only_ci_test]
#[test]
fn print_config() {
    assert_that!(
        &["--", "--print-config", "current", "."],
        contains("max_width = ")
    );
}

#[rustfmt_only_ci_test]
#[test]
fn rustfmt_help() {
    assert_that!(&["--", "--help"], contains("Format Rust code"));
    assert_that!(&["--", "-h"], contains("Format Rust code"));
    assert_that!(&["--", "--help=config"], contains("Configuration Options:"));
}

#[rustfmt_only_ci_test]
#[test]
fn cargo_fmt_out_of_line_test_modules() {
    // See also https://github.com/rust-lang/rustfmt/issues/5119
    let expected_modified_files = [
        "tests/mod-resolver/test-submodule-issue-5119/src/lib.rs",
        "tests/mod-resolver/test-submodule-issue-5119/tests/test1.rs",
        "tests/mod-resolver/test-submodule-issue-5119/tests/test1/sub1.rs",
        "tests/mod-resolver/test-submodule-issue-5119/tests/test1/sub2.rs",
        "tests/mod-resolver/test-submodule-issue-5119/tests/test1/sub3/sub4.rs",
    ];
    let args = [
        "-v",
        "--check",
        "--manifest-path",
        "tests/mod-resolver/test-submodule-issue-5119/Cargo.toml",
    ];
    let (stdout, _) = cargo_fmt(&args);
    for file in expected_modified_files {
        let path = Path::new(file).canonicalize().unwrap();
        assert!(stdout.contains(&format!("Diff in {}", path.display())));
    }
}

#[rustfmt_only_ci_test]
#[test]
fn cargo_fmt_emits_error_on_line_overflow_true() {
    // See also https://github.com/rust-lang/rustfmt/issues/3164
    let args = [
        "--check",
        "--manifest-path",
        "tests/cargo-fmt/source/issue_3164/Cargo.toml",
        "--",
        "--config",
        "error_on_line_overflow=true",
    ];

    let (_stdout, stderr) = cargo_fmt(&args);
    assert!(stderr.contains(
        "line formatted, but exceeded maximum width (maximum: 100 (see `max_width` option)"
    ))
}

// Trust (T14d, DECISION_QUEUE T14-FMT-1): `targo fmt` formats the file an
// item-position `include!("<literal>")` names, and names every `include!` it
// cannot follow as not formatted, never as checked.
#[test]
fn literal_includes_are_checked_and_other_includes_are_named() {
    let mut bin_dir = env::current_exe().unwrap();
    bin_dir.pop();
    if bin_dir.ends_with("deps") {
        bin_dir.pop();
    }
    let cmd = bin_dir.join(format!("cargo-fmt{}", env::consts::EXE_SUFFIX));
    // The formatter this crate built (it is `rustfmt` here, `trustfmt` once
    // installed), not whatever `trustfmt` PATH names.
    let formatter = bin_dir.join(format!("rustfmt{}", env::consts::EXE_SUFFIX));
    let path = env::var_os("PATH").unwrap_or_default();
    let mut paths = env::split_paths(&path).collect::<Vec<_>>();
    paths.insert(0, bin_dir);
    let new_path = env::join_paths(paths).unwrap();

    let dir = tempfile::tempdir().unwrap();
    let root = dir.path().canonicalize().unwrap();
    std::fs::create_dir_all(root.join("src")).unwrap();
    std::fs::write(
        root.join("Cargo.toml"),
        "[package]\nname = \"includes\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[workspace]\n",
    )
    .unwrap();
    std::fs::write(
        root.join("src/lib.rs"),
        "include!(\"generated.rs\");\ninclude!(concat!(\"computed\", \".rs\"));\n",
    )
    .unwrap();
    std::fs::write(root.join("src/generated.rs"), "pub fn generated( )  {}\n").unwrap();
    std::fs::write(root.join("src/computed.rs"), "pub fn computed() {}\n").unwrap();

    let manifest = root.join("Cargo.toml");
    let output = Command::new(&cmd)
        .args(["--check", "--manifest-path", manifest.to_str().unwrap()])
        .env("PATH", new_path)
        .env("TRUSTFMT", &formatter)
        .output()
        .expect("run cargo-fmt");
    let stdout = String::from_utf8(output.stdout).expect("utf-8");
    let stderr = String::from_utf8(output.stderr).expect("utf-8");
    assert_eq!(
        output.status.code(),
        Some(1),
        "stdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stdout.contains("generated.rs"),
        "the literal include! file was not checked:\n{stdout}"
    );
    assert!(
        stderr.contains("not formatted") && stderr.contains("lib.rs:2"),
        "the computed include! was not named:\n{stderr}"
    );
}

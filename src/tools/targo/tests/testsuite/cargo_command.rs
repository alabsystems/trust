//! Tests for custom cargo commands and other global command features.

use std::env;
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::Stdio;
use std::str;

use crate::prelude::*;
use crate::utils::cargo_exe;
use crate::utils::cargo_process;
use crate::utils::tools::echo_subcommand;
use cargo_test_support::basic_manifest;
use cargo_test_support::registry::Package;
use cargo_test_support::rustc_host;
use cargo_test_support::str;
use cargo_test_support::{basic_bin_manifest, paths, project, project_in_home};
use cargo_util::paths::join_paths;

fn path() -> Vec<PathBuf> {
    env::split_paths(&env::var_os("PATH").unwrap_or_default()).collect()
}

#[cargo_test]
fn list_commands_with_descriptions() {
    let p = project().build();
    p.cargo("--list")
        .with_stdout_data(
            "\
...
    b                    alias: build
...
    build                Compile a local package and all of its dependencies
...
    c                    alias: check
...
    r                    alias: run
...
    read-manifest        DEPRECATED: Print a JSON representation of a Cargo.toml manifest.
...
    t                    alias: test
...
",
        )
        .run();
}

#[cargo_test]
fn list_custom_aliases_with_descriptions() {
    let p = project_in_home("proj")
        .file(
            &paths::home().join(".cargo").join("config"),
            r#"
            [alias]
            myaliasstr = "foo --bar"
            myaliasvec = ["foo", "--bar"]
        "#,
        )
        .build();

    p.cargo("--list")
        .with_stdout_data(str![[r#"
...
    myaliasstr           alias: foo --bar
    myaliasvec           alias: foo --bar
...
"#]])
        .run();
}

#[cargo_test]
fn list_dedupe() {
    let p = project()
        .executable(Path::new("path-test-1").join("cargo-dupe"), "")
        .executable(Path::new("path-test-2").join("cargo-dupe"), "")
        .build();

    let mut path = path();
    path.push(p.root().join("path-test-1"));
    path.push(p.root().join("path-test-2"));
    let path = env::join_paths(path.iter()).unwrap();

    p.cargo("--list")
        .env("PATH", &path)
        .with_stdout_data(str![[r#"
...
    dupe
...
"#]])
        .run();
}

#[cargo_test]
fn list_command_looks_at_path() {
    let proj = project()
        .executable(Path::new("path-test").join("cargo-1"), "")
        .build();

    let mut path = path();
    path.push(proj.root().join("path-test"));
    let path = env::join_paths(path.iter()).unwrap();
    let output = cargo_process("-v --list").env("PATH", &path).run();
    let output = str::from_utf8(&output.stdout).unwrap();
    assert!(
        output.contains("\n    1                   "),
        "missing 1: {}",
        output
    );
}

#[cfg(windows)]
#[cargo_test]
fn list_command_looks_at_path_case_mismatch() {
    let proj = project()
        .executable(Path::new("path-test").join("cargo-1"), "")
        .build();

    let mut path = path();
    path.push(proj.root().join("path-test"));
    let path = env::join_paths(path.iter()).unwrap();

    // See issue #11814: Environment variable names are case-insensitive on Windows.
    // We need to check that having "Path" instead of "PATH" is okay.
    let output = cargo_process("-v --list")
        .env("Path", &path)
        .env_remove("PATH")
        .run();
    let output = str::from_utf8(&output.stdout).unwrap();
    assert!(
        output.contains("\n    1                   "),
        "missing 1: {}",
        output
    );
}

#[cargo_test]
fn list_command_handles_known_external_commands() {
    let p = project()
        .executable(Path::new("path-test").join("cargo-fmt"), "")
        .build();

    let fmt_desc = "    fmt                  Formats all bin and lib files of the current crate using rustfmt.";

    // Without path - fmt isn't there
    p.cargo("--list")
        .env("PATH", "")
        .with_stdout_does_not_contain(fmt_desc)
        .run();

    // With path - fmt is there with known description
    let mut path = path();
    path.push(p.root().join("path-test"));
    let path = env::join_paths(path.iter()).unwrap();

    p.cargo("--list")
        .env("PATH", &path)
        .with_stdout_data(str![[r#"
...
    fmt                  Formats all bin and lib files of the current crate using rustfmt.
..."#]])
        .run();
}

#[cargo_test]
fn list_command_resolves_symlinks() {
    let proj = project()
        .symlink(cargo_exe(), Path::new("path-test").join("cargo-2"))
        .build();

    let mut path = path();
    path.push(proj.root().join("path-test"));
    let path = env::join_paths(path.iter()).unwrap();
    let output = cargo_process("-v --list").env("PATH", &path).run();
    let output = str::from_utf8(&output.stdout).unwrap();
    assert!(
        output.contains("\n    2                   "),
        "missing 2: {}",
        output
    );
}

#[cargo_test]
fn find_closest_capital_c_to_c() {
    cargo_process("C")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] no such command: `C`

[HELP] a command with a similar name exists: `c`

[HELP] view all installed commands with `cargo --list`
[HELP] find a package to install `C` with `cargo search cargo-C`

"#]])
        .run();
}

#[cargo_test]
fn find_closest_capital_b_to_b() {
    cargo_process("B")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] no such command: `B`

[HELP] a command with a similar name exists: `b`

[HELP] view all installed commands with `cargo --list`
[HELP] find a package to install `B` with `cargo search cargo-B`

"#]])
        .run();
}

#[cargo_test]
fn cargo_rustfmt_suggestion() {
    cargo_process("rustfmt")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] no such command: `rustfmt`

[HELP] a command with a similar name exists: `fmt`

[HELP] view all installed commands with `cargo --list`
[HELP] find a package to install `rustfmt` with `cargo search cargo-rustfmt`

"#]])
        .run();
}

#[cargo_test]
fn find_closest_biuld_to_build() {
    cargo_process("biuld")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] no such command: `biuld`

[HELP] a command with a similar name exists: `build`

[HELP] view all installed commands with `cargo --list`
[HELP] find a package to install `biuld` with `cargo search cargo-biuld`

"#]])
        .run();

    // But, if we actually have `biuld`, it must work!
    // https://github.com/rust-lang/cargo/issues/5201
    Package::new("cargo-biuld", "1.0.0")
        .file(
            "src/main.rs",
            r#"
                fn main() {
                    println!("Similar, but not identical to, build");
                }
            "#,
        )
        .publish();

    cargo_process("install cargo-biuld").run();
    cargo_process("biuld")
        .with_stdout_data(str![[r#"
Similar, but not identical to, build

"#]])
        .run();
    cargo_process("--list")
        .with_stdout_data(str![[r#"
...
    biuld
...
    build                Compile a local package and all of its dependencies
..."#]])
        .run();
}

#[cargo_test]
fn find_closest_alias() {
    let root = paths::root();
    let my_home = root.join("my_home");
    fs::create_dir(&my_home).unwrap();
    fs::write(
        &my_home.join("config.toml"),
        r#"
            [alias]
            myalias = "build"
        "#,
    )
    .unwrap();

    cargo_process("myalais")
        .env("CARGO_HOME", &my_home)
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] no such command: `myalais`

[HELP] a command with a similar name exists: `myalias`

[HELP] view all installed commands with `cargo --list`
[HELP] find a package to install `myalais` with `cargo search cargo-myalais`

"#]])
        .run();

    // But, if no alias is defined, it must not suggest one!
    cargo_process("myalais")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] no such command: `myalais`

[HELP] view all installed commands with `cargo --list`
[HELP] find a package to install `myalais` with `cargo search cargo-myalais`

"#]])
        .run();
}

// If a subcommand is more than an edit distance of 3 away, we don't make a suggestion.
#[cargo_test]
fn find_closest_dont_correct_nonsense() {
    cargo_process("there-is-no-way-that-there-is-a-command-close-to-this")
		.cwd(&paths::root())
		.with_status(101)
		.with_stderr_data(str![[r#"
[ERROR] no such command: `there-is-no-way-that-there-is-a-command-close-to-this`

[HELP] view all installed commands with `cargo --list`
[HELP] find a package to install `there-is-no-way-that-there-is-a-command-close-to-this` with `cargo search cargo-there-is-no-way-that-there-is-a-command-close-to-this`

"#]])
        .run();
}

#[cargo_test]
fn displays_subcommand_on_error() {
    cargo_process("invalid-command")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] no such command: `invalid-command`

[HELP] view all installed commands with `cargo --list`
[HELP] find a package to install `invalid-command` with `cargo search cargo-invalid-command`

"#]])
        .run();
}

#[cargo_test]
fn override_cargo_home() {
    let root = paths::root();
    let my_home = root.join("my_home");
    fs::create_dir(&my_home).unwrap();
    fs::write(
        &my_home.join("config"),
        r#"
            [cargo-new]
            vcs = "none"
        "#,
    )
    .unwrap();

    cargo_process("new foo").env("CARGO_HOME", &my_home).run();

    assert!(!paths::root().join("foo/.git").is_dir());

    cargo_process("new foo2").run();

    assert!(paths::root().join("foo2/.git").is_dir());
}

#[cargo_test]
fn cargo_subcommand_env() {
    let src = format!(
        r#"
        use std::env;

        fn main() {{
            println!("{{}}", env::var("{}").unwrap());
        }}
        "#,
        cargo::CARGO_ENV
    );

    let p = project()
        .at("cargo-envtest")
        .file("Cargo.toml", &basic_bin_manifest("cargo-envtest"))
        .file("src/main.rs", &src)
        .build();

    let target_dir = p.target_debug_dir();

    p.cargo("build").run();
    assert!(p.bin("cargo-envtest").is_file());

    let cargo = cargo_exe();
    let mut path = path();
    path.push(target_dir.clone());
    let path = env::join_paths(path.iter()).unwrap();

    cargo_process("envtest")
        .env("PATH", &path)
        .with_stdout_data(format!("{}\n", cargo.to_str().unwrap()).raw())
        .run();

    // Check that subcommands inherit an overridden $CARGO
    let envtest_bin = target_dir
        .join("cargo-envtest")
        .with_extension(std::env::consts::EXE_EXTENSION);
    let envtest_bin = envtest_bin.to_str().unwrap();
    // Previously, `$CARGO` would be left at `envtest_bin`. However, with the
    // fix for #15099, `$CARGO` is now overwritten with the path to the current
    // exe when it is detected to be a cargo binary.
    cargo_process("envtest")
        .env("PATH", &path)
        .env(cargo::CARGO_ENV, &envtest_bin)
        .with_stdout_data(format!("{}\n", cargo.display()).raw())
        .run();
}

#[cargo_test]
fn cargo_cmd_bins_vs_explicit_path() {
    // Set up `cargo-foo` binary in two places: inside `$HOME/.cargo/bin` and outside of it
    //
    // Return paths to both places
    fn set_up_cargo_foo() -> (PathBuf, PathBuf) {
        let p = project()
            .at("cargo-foo")
            .file("Cargo.toml", &basic_manifest("cargo-foo", "1.0.0"))
            .file(
                "src/bin/cargo-foo.rs",
                r#"fn main() { println!("INSIDE"); }"#,
            )
            .file(
                "src/bin/cargo-foo2.rs",
                r#"fn main() { println!("OUTSIDE"); }"#,
            )
            .build();
        p.cargo("build").run();
        let cargo_bin_dir = paths::home().join(".cargo/bin");
        cargo_bin_dir.mkdir_p();
        let root_bin_dir = paths::root().join("bin");
        root_bin_dir.mkdir_p();
        let exe_name = format!("cargo-foo{}", env::consts::EXE_SUFFIX);
        fs::rename(p.bin("cargo-foo"), cargo_bin_dir.join(&exe_name)).unwrap();
        fs::rename(p.bin("cargo-foo2"), root_bin_dir.join(&exe_name)).unwrap();

        (root_bin_dir, cargo_bin_dir)
    }

    let (outside_dir, inside_dir) = set_up_cargo_foo();

    // If `$CARGO_HOME/bin` is not in a path, prefer it over anything in `$PATH`.
    //
    // This is the historical behavior we don't want to break.
    cargo_process("foo")
        .with_stdout_data(str![[r#"
INSIDE

"#]])
        .run();

    // When `$CARGO_HOME/bin` is in the `$PATH`
    // use only `$PATH` so the user-defined ordering is respected.
    {
        cargo_process("foo")
            .env(
                "PATH",
                join_paths(&[&inside_dir, &outside_dir], "PATH").unwrap(),
            )
            .with_stdout_data(str![[r#"
INSIDE

"#]])
            .run();

        cargo_process("foo")
            // Note: trailing slash
            .env(
                "PATH",
                join_paths(&[inside_dir.join(""), outside_dir.join("")], "PATH").unwrap(),
            )
            .with_stdout_data(str![[r#"
INSIDE

"#]])
            .run();

        cargo_process("foo")
            .env(
                "PATH",
                join_paths(&[&outside_dir, &inside_dir], "PATH").unwrap(),
            )
            .with_stdout_data(str![[r#"
OUTSIDE

"#]])
            .run();

        cargo_process("foo")
            // Note: trailing slash
            .env(
                "PATH",
                join_paths(&[outside_dir.join(""), inside_dir.join("")], "PATH").unwrap(),
            )
            .with_stdout_data(str![[r#"
OUTSIDE

"#]])
            .run();
    }
}

#[cargo_test]
fn cargo_subcommand_args() {
    let p = echo_subcommand();
    let cargo_foo_bin = p.bin("cargo-echo");
    assert!(cargo_foo_bin.is_file());

    let mut path = path();
    path.push(p.target_debug_dir());
    let path = env::join_paths(path.iter()).unwrap();

    cargo_process("echo bar -v --help")
        .env("PATH", &path)
        .with_stdout_data(str![[r#"
echo bar -v --help

"#]])
        .run();
}

// Trust: from here to the end of the file is Trust-authored. It covers the
// consequences of shipping one executable under two names — which prefix an
// external subcommand resolves by, which frontend a nested `$CARGO` names, and
// that the `cargo` alias keeps upstream semantics exactly. All of it needs real
// processes, because the property under test is what the OS reports about the
// running image.
#[cargo_test]
fn targo_external_subcommands_prefer_trust_prefix_then_cargo_compat() {
    let p = project()
        .at("targo-external-subcommands")
        .file(
            "Cargo.toml",
            &basic_manifest("targo-external-subcommands", "0.0.1"),
        )
        .file(
            "src/bin/targo-foo.rs",
            r#"fn main() { println!("TRUST"); }"#,
        )
        .file(
            "src/bin/cargo-foo.rs",
            r#"fn main() { println!("CARGO"); }"#,
        )
        .file(
            "src/bin/targo-env-probe.rs",
            r#"fn main() { println!("{}", std::env::var("CARGO").unwrap()); }"#,
        )
        .build();
    p.cargo("build").run();

    let cargo_exe = cargo_exe();
    let targo_exe = p.root().join(format!("targo{}", env::consts::EXE_SUFFIX));
    fs::hard_link(&cargo_exe, &targo_exe).unwrap();

    let mut path = path();
    path.push(p.target_debug_dir());
    let path = env::join_paths(path.iter()).unwrap();

    p.process(&targo_exe)
        .arg("foo")
        .env("PATH", &path)
        .env(cargo::CARGO_ENV, &targo_exe)
        .with_stdout_data(str![[r#"
TRUST

"#]])
        .run();

    // An inherited $CARGO must not make a targo-launched subcommand recurse
    // through the compatibility alias. The running canonical frontend wins.
    p.process(&targo_exe)
        .arg("env-probe")
        .env("PATH", &path)
        .env(cargo::CARGO_ENV, &cargo_exe)
        .with_stdout_data(format!("{}\n", targo_exe.display()).raw())
        .run();

    fs::remove_file(p.bin("targo-foo")).unwrap();

    p.process(&targo_exe)
        .arg("foo")
        .env("PATH", &path)
        .env(cargo::CARGO_ENV, &targo_exe)
        .with_stdout_data(str![[r#"
CARGO

"#]])
        .run();
}

#[cfg(unix)]
#[cargo_test]
fn plain_cargo_symlink_keeps_upstream_frontend_semantics() {
    let p = project()
        .at("cargo-targo-symlink-identity")
        .file(
            "Cargo.toml",
            &basic_manifest("cargo-targo-symlink-identity", "0.0.1"),
        )
        .file(
            "src/bin/cargo-identity-probe.rs",
            r#"
                use std::path::Path;
                use std::process::Command;

                fn main() {
                    let frontend = std::env::var_os("CARGO").expect("CARGO");
                    let name = Path::new(&frontend)
                        .file_stem()
                        .and_then(|name| name.to_str())
                        .expect("frontend name");
                    let output = Command::new(&frontend)
                        .arg("--help")
                        .output()
                        .expect("recursive frontend help");
                    assert!(output.status.success());
                    let help = String::from_utf8(output.stdout).expect("UTF-8 help");
                    println!("CARGO={name}");
                    println!("RUST_HELP={}", help.contains("Rust's package manager"));
                    println!(
                        "TRUST_HELP={}",
                        help.contains("Trust's Cargo-compatible package manager")
                    );
                }
            "#,
        )
        .build();
    p.cargo("build --bin cargo-identity-probe").run();
    let toolchain_bin = p.root().join("toolchain/bin");
    fs::create_dir_all(&toolchain_bin).unwrap();
    let targo = toolchain_bin.join("targo");
    let cargo = toolchain_bin.join("cargo");
    fs::hard_link(cargo_exe(), &targo).unwrap();
    std::os::unix::fs::symlink(&targo, &cargo).unwrap();

    p.process(&cargo)
        .arg("--help")
        .with_stdout_contains("Rust's package manager")
        .run();

    let mut command_path = path();
    command_path.push(p.target_debug_dir());
    p.process(&cargo)
        .arg("identity-probe")
        .env("PATH", env::join_paths(command_path).unwrap())
        .env(cargo::CARGO_ENV, cargo_exe())
        .with_stdout_data(str![[r#"
CARGO=cargo
RUST_HELP=true
TRUST_HELP=false

"#]])
        .run();

    p.process(&targo)
        .arg("--help")
        .with_stdout_contains("Trust's Cargo-compatible package manager")
        .run();
}

#[cfg(unix)]
#[cargo_test]
fn forged_argv0_cannot_promote_or_demote_frontend_brand() {
    use std::os::unix::fs::PermissionsExt as _;
    use std::os::unix::process::CommandExt as _;

    let p = project().at("cargo-targo-forged-argv0").build();
    let cargo = cargo_exe();
    let targo = p.root().join("targo");
    fs::hard_link(&cargo, &targo).unwrap();
    let forged_cargo = p.root().join("cargo");
    fs::write(&forged_cargo, "#!/bin/sh\nexit 99\n").unwrap();
    fs::set_permissions(&forged_cargo, fs::Permissions::from_mode(0o755)).unwrap();

    let mut command_path = vec![p.root().to_path_buf()];
    command_path.extend(path());
    let command_path = env::join_paths(command_path).unwrap();

    let demotion = std::process::Command::new(&targo)
        .arg0("cargo")
        .arg("--help")
        .env("PATH", &command_path)
        .env(cargo::CARGO_ENV, &cargo)
        .output()
        .expect("run Targo with forged Cargo argv0");
    assert!(!demotion.status.success(), "{demotion:?}");
    let demotion_stderr = String::from_utf8(demotion.stderr).expect("UTF-8 Targo error");
    assert!(
        demotion_stderr.contains("could not authenticate Cargo/Targo frontend identity"),
        "forged Cargo argv0 did not fail closed:\n{demotion_stderr}"
    );

    let promotion = std::process::Command::new(&cargo)
        .arg0("targo")
        .arg("--help")
        .env("PATH", &command_path)
        .env(cargo::CARGO_ENV, &targo)
        .output()
        .expect("run Cargo with forged Targo argv0");
    assert!(promotion.status.success(), "{promotion:?}");
    let promotion_stdout = String::from_utf8(promotion.stdout).expect("UTF-8 Cargo help");
    assert!(
        promotion_stdout.contains("Rust's package manager")
            && !promotion_stdout.contains("Trust's Cargo-compatible package manager"),
        "forged Targo argv0 promoted plain Cargo:\n{promotion_stdout}"
    );
}

#[cargo_test]
fn targo_help_uses_canonical_frontend_name() {
    let p = project().at("targo-help-name").build();
    let targo_exe = p.root().join(format!("targo{}", env::consts::EXE_SUFFIX));
    fs::hard_link(cargo_exe(), &targo_exe).unwrap();

    p.process(&targo_exe)
        .arg("--help")
        .with_stdout_contains("Trust's Cargo-compatible package manager")
        .with_stdout_contains("Usage: targo [..]")
        .with_stdout_contains("[..]Change to DIRECTORY before doing anything (Trust/nightly-only)")
        .with_stdout_contains("[..]Unstable flags to Targo, see 'targo -Z help' for details")
        .with_stdout_contains("See 'targo help <command>'[..]")
        .with_stdout_does_not_contain("Usage: cargo [OPTIONS] [COMMAND]")
        .run();

    p.process(&targo_exe)
        .arg("--list")
        .with_stdout_contains("[..]help[..]Displays help for a targo command[..]")
        .with_stdout_does_not_contain("[..]Displays help for a cargo command[..]")
        .run();

    p.process(cargo_exe())
        .arg("--help")
        .with_stdout_contains("Rust's package manager")
        .with_stdout_contains("[..]Change to DIRECTORY before doing anything (nightly-only)")
        .with_stdout_contains("[..]Unstable (nightly-only) flags to Cargo[..]")
        .with_stdout_does_not_contain("Trust's Cargo-compatible package manager")
        .with_stdout_does_not_contain("Trust/nightly-only")
        .run();

    p.process(cargo_exe())
        .arg("--list")
        .with_stdout_contains("[..]help[..]Displays help for a cargo command[..]")
        .with_stdout_does_not_contain("[..]Displays help for a targo command[..]")
        .run();
}

#[cargo_test]
fn targo_requires_explicit_unverified_authority_and_cargo_rejects_the_flag() {
    let p = project()
        .at("targo-explicit-unverified-policy")
        .file("Cargo.toml", &basic_manifest("policy-subject", "1.0.0"))
        .file("src/lib.rs", "pub fn subject() {}")
        .build();
    let targo = p.root().join(format!("targo{}", env::consts::EXE_SUFFIX));
    fs::hard_link(cargo_exe(), &targo).unwrap();

    p.process(&targo)
        .arg("build")
        .env_remove("TRUST_TARGO_VERIFY")
        .env_remove("TRUST_BOOTSTRAP_SHIM_NO_VERIFY")
        .env_remove("TRUST_BOOTSTRAP_SHIM_NO_VERIFY_TARGET_ONLY")
        .env_remove("TRUST_BOOTSTRAP_NO_VERIFY")
        .env_remove("TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY")
        .with_status(101)
        .with_stderr_contains("[..]refuses to create an implicitly unverified artifact[..]")
        .run();
    assert!(
        !p.build_dir().exists(),
        "authorization must fail before Cargo creates build artifacts"
    );
    p.process(&targo)
        .arg("b")
        .env_remove("TRUST_TARGO_VERIFY")
        .env_remove("TRUST_BOOTSTRAP_NO_VERIFY")
        .env_remove("TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY")
        .with_status(101)
        .with_stderr_contains("[..]refuses to create an implicitly unverified artifact[..]")
        .run();
    assert!(
        !p.build_dir().exists(),
        "alias expansion must not bypass native lane authorization"
    );

    for args in [vec!["miri"], vec!["miri", "setup"], vec!["miri", "clean"]] {
        p.process(&targo)
            .args(&args)
            .env_remove("TRUST_TARGO_VERIFY")
            .env_remove("TRUST_BOOTSTRAP_NO_VERIFY")
            .env_remove("TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY")
            .with_status(101)
            .with_stderr_contains(
                "[..]`targo miri` refuses to create an implicitly unverified artifact[..]",
            )
            .run();
    }
    assert!(
        !p.build_dir().exists(),
        "the complete protected Miri front door must require a lane before materialization"
    );

    for (marker, value) in [
        ("TRUST_BOOTSTRAP_NO_VERIFY", "0"),
        ("TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY", "1"),
    ] {
        p.process(&targo)
            .arg("metadata")
            .env_remove("TRUST_TARGO_VERIFY")
            .env_remove("TRUST_BOOTSTRAP_SHIM_NO_VERIFY")
            .env_remove("TRUST_BOOTSTRAP_SHIM_NO_VERIFY_TARGET_ONLY")
            .env(marker, value)
            .with_status(101)
            .with_stderr_contains(
                "[..]legacy TRUST_BOOTSTRAP_NO_VERIFY markers do not authorize branded Targo[..]",
            )
            .run();
    }
    assert!(
        !p.build_dir().exists(),
        "legacy ambient markers must fail before Cargo creates build artifacts"
    );

    p.cargo("--unverified build")
        .with_status(1)
        .with_stderr_contains("[..]unexpected argument '--unverified'[..]")
        .run();
    assert!(
        !p.build_dir().exists(),
        "ordinary Cargo must reject Targo's opt-in without compiling"
    );

    for args in [["--unverified", "b"], ["b", "--unverified"]] {
        p.process(&targo)
            .args(&args)
            .env("RUSTC", p.root().join("deliberately-missing-rustc"))
            .env_remove("TRUST_TARGO_VERIFY")
            .env_remove("TRUST_BOOTSTRAP_SHIM_NO_VERIFY")
            .env_remove("TRUST_BOOTSTRAP_SHIM_NO_VERIFY_TARGET_ONLY")
            .env_remove("TRUST_BOOTSTRAP_NO_VERIFY")
            .env_remove("TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY")
            .with_status(101)
            .with_stderr_contains("[..]UNVERIFIED:[..]")
            .with_stderr_does_not_contain("[..]implicitly unverified artifact[..]")
            .run();
    }
    for args in [["--unverified", "miri"], ["miri", "--unverified"]] {
        p.process(&targo)
            .args(&args)
            .env_remove("TRUST_TARGO_VERIFY")
            .env_remove("TRUST_BOOTSTRAP_NO_VERIFY")
            .env_remove("TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY")
            .with_status(101)
            .with_stderr_contains("[..]UNVERIFIED: `targo miri`[..]")
            .with_stderr_does_not_contain("[..]implicitly unverified artifact[..]")
            .run();
    }
}

#[cargo_test]
fn targo_aliases_cannot_mint_unverified_authority() {
    let p = project()
        .at("targo-alias-unverified-origin")
        .file(
            "Cargo.toml",
            &basic_manifest("alias-policy-subject", "1.0.0"),
        )
        .file("src/lib.rs", "pub fn subject() {}")
        .file(
            ".cargo/config.toml",
            r#"
                [alias]
                repo-fast = "build --unverified"
                repo-chain = "repo-fast"
                repo-plain = "build"
                repo-miri-fast = "miri --unverified"
                repo-miri-fast-chain = "repo-miri-fast"
                repo-miri = "miri"
                repo-miri-chain = "repo-miri"
            "#,
        )
        .build();
    let targo = p.root().join(format!("targo{}", env::consts::EXE_SUFFIX));
    fs::hard_link(cargo_exe(), &targo).unwrap();

    for alias in ["repo-fast", "repo-chain"] {
        p.process(&targo)
            .arg(alias)
            .env_remove("TRUST_TARGO_VERIFY")
            .env_remove("TRUST_BOOTSTRAP_NO_VERIFY")
            .env_remove("TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY")
            .with_status(101)
            .with_stderr_contains(
                "[..]alias attempted to inject `--unverified`[..]configuration cannot grant verification bypass authority[..]",
            )
            .with_stderr_does_not_contain("[..]UNVERIFIED:[..]")
            .run();
    }
    // External-subcommand arguments are intentionally opaque to Cargo's global
    // parser, so the alias-injected flag is not classified as a Targo flag.
    // The stronger front-door rule still fails closed before Miri executes:
    // without original-argv consent the protected command has no lane.
    for alias in ["repo-miri-fast", "repo-miri-fast-chain"] {
        p.process(&targo)
            .arg(alias)
            .env_remove("TRUST_TARGO_VERIFY")
            .env_remove("TRUST_BOOTSTRAP_NO_VERIFY")
            .env_remove("TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY")
            .with_status(101)
            .with_stderr_contains(
                "[..]`targo miri` refuses to create an implicitly unverified artifact[..]",
            )
            .with_stderr_does_not_contain("[..]UNVERIFIED:[..]")
            .run();
    }
    assert!(
        !p.build_dir().exists(),
        "repository aliases and alias chains must fail before creating build artifacts"
    );

    for alias in ["repo-miri", "repo-miri-chain"] {
        p.process(&targo)
            .arg(alias)
            .env_remove("TRUST_TARGO_VERIFY")
            .env_remove("TRUST_BOOTSTRAP_NO_VERIFY")
            .env_remove("TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY")
            .with_status(101)
            .with_stderr_contains(
                "[..]`targo miri` refuses to create an implicitly unverified artifact[..]",
            )
            .with_stderr_does_not_contain("[..]UNVERIFIED:[..]")
            .run();
    }

    // Consent on the original logical invocation remains valid even when the
    // command name itself is an alias.
    p.process(&targo)
        .args(&["repo-plain", "--unverified"])
        .env("RUSTC", p.root().join("deliberately-missing-rustc"))
        .env_remove("TRUST_TARGO_VERIFY")
        .env_remove("TRUST_BOOTSTRAP_NO_VERIFY")
        .env_remove("TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY")
        .with_status(101)
        .with_stderr_contains("[..]UNVERIFIED:[..]")
        .with_stderr_does_not_contain("[..]alias attempted to inject[..]")
        .run();

    let global_home = p.root().join("attacker-cargo-home");
    fs::create_dir_all(&global_home).unwrap();
    fs::write(
        global_home.join("config.toml"),
        r#"
            [alias]
            global-fast = ["build", "--unverified"]
            global-chain = "global-fast"
        "#,
    )
    .unwrap();
    for alias in ["global-fast", "global-chain"] {
        p.process(&targo)
            .arg(alias)
            .env("CARGO_HOME", &global_home)
            .env_remove("TRUST_TARGO_VERIFY")
            .env_remove("TRUST_BOOTSTRAP_NO_VERIFY")
            .env_remove("TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY")
            .with_status(101)
            .with_stderr_contains(
                "[..]alias attempted to inject `--unverified`[..]configuration cannot grant verification bypass authority[..]",
            )
            .with_stderr_does_not_contain("[..]UNVERIFIED:[..]")
            .run();
    }
}

#[cargo_test(nightly, reason = "-Zscript is unstable")]
fn targo_script_requires_a_lane_before_creating_its_target_directory() {
    let p = project()
        .at("targo-script-lane-policy")
        .file(
            "script.rs",
            "fn main() { println!(\"args={:?}\", std::env::args().skip(1).collect::<Vec<_>>()); }",
        )
        .build();
    let targo = p.root().join(format!("targo{}", env::consts::EXE_SUFFIX));
    fs::hard_link(cargo_exe(), &targo).unwrap();
    let target = p.root().join("script-target-must-not-exist");

    p.process(&targo)
        .args(&["-Zscript", "./script.rs"])
        .masquerade_as_nightly_cargo(&["script"])
        .env("CARGO_TARGET_DIR", &target)
        .env_remove("TRUST_TARGO_VERIFY")
        .env_remove("TRUST_BOOTSTRAP_NO_VERIFY")
        .env_remove("TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY")
        .with_status(101)
        .with_stderr_contains(
            "[..]`targo -Zscript ./script.rs` refuses to create an implicitly unverified artifact[..]",
        )
        .run();
    assert!(
        !target.exists(),
        "implicit Targo script authorization must fail before target materialization"
    );

    p.process(&targo)
        .args(&["-Zscript", "./script.rs", "--unverified"])
        .masquerade_as_nightly_cargo(&["script"])
        .env("CARGO_TARGET_DIR", &target)
        .env_remove("TRUST_TARGO_VERIFY")
        .with_status(101)
        .with_stderr_contains("[..]refuses to create an implicitly unverified artifact[..]")
        .run();
    assert!(
        !target.exists(),
        "a program argument named --unverified is not Targo lane consent"
    );

    for args in [
        vec!["--unverified", "-Zscript", "./script.rs"],
        vec!["-Zscript", "--unverified", "./script.rs"],
    ] {
        p.process(&targo)
            .args(&args)
            .masquerade_as_nightly_cargo(&["script"])
            .env("CARGO_TARGET_DIR", &target)
            .env("RUSTC", p.root().join("deliberately-missing-rustc"))
            .env_remove("TRUST_TARGO_VERIFY")
            .env_remove("TRUST_BOOTSTRAP_NO_VERIFY")
            .env_remove("TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY")
            .with_status(101)
            .with_stderr_contains("[..]UNVERIFIED: `targo -Zscript ./script.rs`[..]")
            .with_stderr_does_not_contain("[..]implicitly unverified artifact[..]")
            .run();
    }

    let cargo_target = p.root().join("ordinary-cargo-script-target");
    let mut ordinary = p.cargo("-Zscript ./script.rs --unverified");
    ordinary
        .masquerade_as_nightly_cargo(&["script"])
        .env("CARGO_TARGET_DIR", &cargo_target)
        // Cargo's fixture environment deliberately removes the outer compiler
        // and flags. Restore the exact driver inputs used to compile this test
        // so this behavioral control exercises a real script compiler rather
        // than the bootstrap fixture shim.
        .env(
            "RUSTC",
            env::var_os("RUSTC").unwrap_or_else(|| "rustc".into()),
        )
        .with_stdout_contains("[..]args=[\"--unverified\"][..]");
    if let Some(rustflags) = env::var_os("RUSTFLAGS") {
        ordinary.env("RUSTFLAGS", rustflags);
    }
    ordinary.run();
}

#[cfg(target_os = "linux")]
#[cargo_test]
fn ambient_nested_unverified_broker_address_cannot_mint_targo_authority() {
    let p = project()
        .at("targo-forged-nested-unverified")
        .file(
            "Cargo.toml",
            &basic_manifest("nested-unverified-subject", "1.0.0"),
        )
        .file("src/lib.rs", "pub fn subject() {}")
        .build();
    let targo = p.root().join(format!("targo{}", env::consts::EXE_SUFFIX));
    fs::hard_link(cargo_exe(), &targo).unwrap();

    for address in [
        "nonexistent",
        "trust-targo-unverified-forged",
        "trust-targo-unverified-stale",
    ] {
        p.process(&targo)
            .arg("check")
            .env("TRUST_TARGO_NESTED_UNVERIFIED_BROKER", address)
            .env_remove("TRUST_TARGO_VERIFY")
            .env_remove("TRUST_BOOTSTRAP_NO_VERIFY")
            .env_remove("TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY")
            .with_status(101)
            .with_stderr_contains(
                "[..]could not authenticate nested-unverified Targo authority[..]",
            )
            .with_stderr_does_not_contain("[..]UNVERIFIED:[..]")
            .run();
    }
    assert!(
        !p.build_dir().exists(),
        "forged ambient broker addresses must fail before build materialization"
    );
}

#[cfg(target_os = "linux")]
#[cargo_test]
fn explicit_unverified_targo_propagates_to_nested_cargo_compile_without_rustflags() {
    let p = project()
        .at("targo-authenticated-nested-unverified")
        .file("Cargo.toml", &basic_bin_manifest("nested-launcher"))
        .file(
            "src/main.rs",
            r#"
                use std::process::Command;

                fn main() {
                    if std::env::args().nth(1).as_deref() == Some("exit-42") {
                        std::process::exit(42);
                    }
                    if std::env::args().nth(1).as_deref() == Some("signal-wait") {
                        let path = std::env::var_os("SIGNAL_TARGET_PID_FILE")
                            .expect("SIGNAL_TARGET_PID_FILE");
                        std::fs::write(path, std::process::id().to_string())
                            .expect("write target pid");
                        loop {
                            std::thread::park();
                        }
                    }
                    let cargo = std::env::var_os("CARGO").expect("CARGO");
                    let manifest = std::path::PathBuf::from(
                        std::env::var_os("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"),
                    );
                    let output = Command::new(cargo)
                        .args([
                            "--offline",
                            "-vv",
                            "--config=build.rustflags=[]",
                            "check",
                        ])
                        .current_dir(manifest.join("nested"))
                        .env_remove("RUSTFLAGS")
                        .env_remove("CARGO_ENCODED_RUSTFLAGS")
                        .env_remove("TRUST_TARGO_VERIFY")
                        .env("CARGO_TARGET_DIR", manifest.join("nested-target"))
                        .output()
                        .expect("run nested Targo");
                    let stderr = String::from_utf8(output.stderr).expect("UTF-8 nested stderr");
                    assert!(output.status.success(), "nested Targo failed:\n{}", stderr);
                    assert!(
                        stderr.contains(
                            "inherited live broker-authenticated explicit-unverified authority",
                        ),
                        "nested Targo did not report inherited authority:\n{}",
                        stderr,
                    );
                    assert!(
                        stderr.contains("-Zno-trust-verify"),
                        "trybuild-style rustflag stripping lost the unverified compiler lane:\n{}",
                        stderr,
                    );
                    println!("nested-unverified-broker-ok");
                }
            "#,
        )
        .file(
            "nested/Cargo.toml",
            r#"
                [package]
                name = "nested-subject"
                version = "0.1.0"
                edition = "2021"

                [workspace]
            "#,
        )
        .file("nested/src/lib.rs", "pub fn nested_subject() {}")
        .build();
    let targo = p.root().join(format!("targo{}", env::consts::EXE_SUFFIX));
    fs::hard_link(cargo_exe(), &targo).unwrap();

    let mut run = p.process(&targo);
    run.args(&["--unverified", "run"])
        .env(
            "RUSTC",
            env::var_os("RUSTC").unwrap_or_else(|| "rustc".into()),
        )
        .env_remove("TRUST_TARGO_VERIFY")
        .env_remove("TRUST_BOOTSTRAP_NO_VERIFY")
        .env_remove("TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY")
        .env_remove("TRUST_TARGO_NESTED_UNVERIFIED_BROKER")
        .with_stdout_contains("nested-unverified-broker-ok")
        .with_stderr_contains("[..]UNVERIFIED: `targo run`[..]");
    if let Some(rustflags) = env::var_os("RUSTFLAGS") {
        run.env("RUSTFLAGS", rustflags);
    }
    run.run();

    p.process(&targo)
        .args(&["--unverified", "run", "--", "exit-42"])
        .env(
            "RUSTC",
            env::var_os("RUSTC").unwrap_or_else(|| "rustc".into()),
        )
        .env_remove("TRUST_TARGO_VERIFY")
        .env_remove("TRUST_BOOTSTRAP_NO_VERIFY")
        .env_remove("TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY")
        .env_remove("TRUST_TARGO_NESTED_UNVERIFIED_BROKER")
        .with_status(42)
        .with_stderr_contains("[..]UNVERIFIED: `targo run`[..]")
        .with_stderr_does_not_contain("[..]process didn't exit successfully[..]")
        .run();

    let target_pid_file = p.root().join("signal-target.pid");
    let mut signal_command = std::process::Command::new(&targo);
    signal_command
        .args(["--unverified", "run", "--", "signal-wait"])
        .current_dir(p.root())
        .env("SIGNAL_TARGET_PID_FILE", &target_pid_file)
        .env(
            "RUSTC",
            env::var_os("RUSTC").unwrap_or_else(|| "rustc".into()),
        )
        .env_remove("TRUST_TARGO_VERIFY")
        .env_remove("TRUST_BOOTSTRAP_NO_VERIFY")
        .env_remove("TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY")
        .env_remove("TRUST_TARGO_NESTED_UNVERIFIED_BROKER")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if let Some(rustflags) = env::var_os("RUSTFLAGS") {
        signal_command.env("RUSTFLAGS", rustflags);
    }
    use std::os::unix::process::CommandExt as _;
    // SAFETY: the post-fork callback uses only sigemptyset/sigaction and
    // constructs an error from thread-local errno on failure.
    unsafe {
        signal_command.pre_exec(|| {
            let mut action: libc::sigaction = std::mem::zeroed();
            action.sa_sigaction = libc::SIG_IGN;
            if libc::sigemptyset(&mut action.sa_mask) != 0
                || libc::sigaction(libc::SIGHUP, &action, std::ptr::null_mut()) != 0
            {
                Err(std::io::Error::last_os_error())
            } else {
                Ok(())
            }
        });
    }
    let mut signal_targo = signal_command
        .spawn()
        .expect("spawn signal-supervised Targo");
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(30);
    while !target_pid_file.is_file() {
        if signal_targo
            .try_wait()
            .expect("inspect signal-supervised Targo")
            .is_some()
        {
            let output = signal_targo
                .wait_with_output()
                .expect("collect early Targo exit");
            panic!(
                "signal-supervised Targo exited before its target was ready:\n{}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
        if std::time::Instant::now() >= deadline {
            signal_targo.kill().expect("terminate timed-out Targo");
            let output = signal_targo
                .wait_with_output()
                .expect("collect timed-out Targo");
            panic!(
                "signal-supervised Targo did not start its target:\n{}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
    let target_pid = fs::read_to_string(&target_pid_file)
        .unwrap()
        .parse::<u32>()
        .unwrap();
    let targo_pid = libc::pid_t::try_from(signal_targo.id()).unwrap();
    assert_eq!(
        unsafe { libc::kill(targo_pid, libc::SIGHUP) },
        0,
        "send SIGHUP to Targo launched with inherited nohup semantics"
    );
    std::thread::sleep(std::time::Duration::from_millis(100));
    if signal_targo
        .try_wait()
        .expect("inspect Targo after ignored SIGHUP")
        .is_some()
    {
        let output = signal_targo
            .wait_with_output()
            .expect("collect Targo after ignored SIGHUP");
        panic!(
            "supervision failed to preserve inherited SIGHUP ignore semantics:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    assert!(
        Path::new(&format!("/proc/{target_pid}")).exists(),
        "forwarded SIGHUP killed a target which inherited nohup-style SIG_IGN"
    );
    assert_eq!(
        unsafe { libc::kill(targo_pid, libc::SIGTERM) },
        0,
        "send SIGTERM directly to the broker-owning Targo pid"
    );
    let output = signal_targo
        .wait_with_output()
        .expect("wait for signal-supervised Targo");
    use std::os::unix::process::ExitStatusExt as _;
    assert_eq!(
        output.status.signal(),
        Some(libc::SIGTERM),
        "Targo must reproduce its target's terminating signal:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        !Path::new(&format!("/proc/{target_pid}")).exists(),
        "SIGTERM sent to the Targo pid left target pid {target_pid} orphaned"
    );
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
#[cargo_test]
fn forged_targo_fix_proxy_environment_cannot_select_a_compiler() {
    use std::os::unix::fs::PermissionsExt as _;

    let p = project()
        .at("targo-forged-fix-proxy")
        .file("Cargo.toml", &basic_manifest("fix-proxy-subject", "1.0.0"))
        .file("src/lib.rs", "pub fn subject() {}")
        .file(
            "forged-rustc",
            "#!/bin/sh\nprintf 'executed\\n' > \"$FORGED_FIX_PROXY_MARKER\"\nexit 0\n",
        )
        .build();
    let targo = p.root().join(format!("targo{}", env::consts::EXE_SUFFIX));
    fs::hard_link(cargo_exe(), &targo).unwrap();
    let forged_rustc = p.root().join("forged-rustc");
    let mut permissions = fs::metadata(&forged_rustc).unwrap().permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(&forged_rustc, permissions).unwrap();
    let marker = p.root().join("forged-compiler-executed");

    p.process(&targo)
        .arg(&forged_rustc)
        .arg(p.root().join("src/lib.rs"))
        .env("__CARGO_FIX_PLZ", "127.0.0.1:1")
        .env(
            "__CARGO_FIX_TARGO_PARENT_PID",
            std::process::id().to_string(),
        )
        .env("__CARGO_FIX_TARGO_EXPECTED_RUSTC", &forged_rustc)
        .env("__CARGO_FIX_TARGO_EXPECTED_RUSTC_ID", "forged")
        .env("__CARGO_FIX_TARGO_LANE_V1", "explicit-unverified")
        .env("__CARGO_FIX_TARGO_CAPABILITY_FD", "3")
        .env("FORGED_FIX_PROXY_MARKER", &marker)
        .env_remove("TRUST_TARGO_VERIFY")
        .with_status(101)
        .with_stderr_contains("[..]refusing forged branded Targo fix-proxy marker[..]")
        .run();
    assert!(
        !marker.exists(),
        "ambient proxy controls must be rejected before the argv-selected compiler executes"
    );
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
#[cargo_test]
fn authenticated_targo_fix_proxy_completes_a_real_fix() {
    let p = project()
        .at("targo-authenticated-fix-proxy")
        .file("Cargo.toml", &basic_manifest("fix-proxy-subject", "1.0.0"))
        .file(
            "src/lib.rs",
            "pub fn answer() -> i32 { let mut value = 42; value }\n",
        )
        .build();
    let targo = p.root().join(format!("targo{}", env::consts::EXE_SUFFIX));
    fs::hard_link(cargo_exe(), &targo).unwrap();

    let mut fix = p.process(&targo);
    fix.args(&["--unverified", "fix", "--allow-no-vcs"])
        // The Cargo test fixture normally substitutes a rustc shim. Exercise
        // the real proxy/compiler handoff with the same compiler and flags
        // that built this test binary.
        .env(
            "RUSTC",
            env::var_os("RUSTC").unwrap_or_else(|| "rustc".into()),
        )
        .env_remove("TRUST_TARGO_VERIFY")
        .env_remove("TRUST_BOOTSTRAP_NO_VERIFY")
        .env_remove("TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY")
        .with_stderr_contains("[..]UNVERIFIED: `targo fix`[..]");
    if let Some(rustflags) = env::var_os("RUSTFLAGS") {
        fix.env("RUSTFLAGS", rustflags);
    }
    fix.run();

    assert_eq!(
        fs::read_to_string(p.root().join("src/lib.rs")).unwrap(),
        "pub fn answer() -> i32 { let value = 42; value }\n",
        "authenticated Targo fix must reach the selected compiler and apply its machine suggestion"
    );
}

#[cargo_test]
fn snapbox_source_paths_use_the_nested_targo_workspace_root() {
    let source_dir = snapbox::utils::current_dir!();
    let expected = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/testsuite");

    assert_eq!(source_dir, expected);
    assert!(
        source_dir.join("cargo/help/stdout.term.svg").is_file(),
        "the source-relative snapshot root must resolve Targo's tracked fixtures"
    );
}

#[cargo_test]
fn targo_subcommand_help_uses_canonical_frontend_name() {
    let p = project().at("targo-subcommand-help-name").build();
    let targo_exe = p.root().join(format!("targo{}", env::consts::EXE_SUFFIX));
    fs::hard_link(cargo_exe(), &targo_exe).unwrap();

    let commands_with_footers = [
        "add",
        "bench",
        "build",
        "check",
        "clean",
        "doc",
        "fetch",
        "fix",
        "generate-lockfile",
        "info",
        "init",
        "install",
        "locate-project",
        "login",
        "logout",
        "metadata",
        "new",
        "owner",
        "package",
        "pkgid",
        "publish",
        "remove",
        "report",
        "run",
        "rustc",
        "rustdoc",
        "search",
        "test",
        "tree",
        "uninstall",
        "update",
        "vendor",
        "version",
        "yank",
    ];
    for command in commands_with_footers {
        p.process(&targo_exe)
            .args(&[command, "--help"])
            .with_stdout_contains(format!("[..]Run `targo help {command}`[..]"))
            .with_stdout_does_not_contain(format!("[..]Run `cargo help {command}`[..]"))
            .run();
    }

    p.process(&targo_exe)
        .args(&["build", "--help"])
        .with_stdout_contains("[..]targo help build[..]")
        .with_stdout_contains("[..]targo help pkgid[..]")
        .with_stdout_does_not_contain("[..]Run `cargo help build`[..]")
        .with_stdout_does_not_contain("[..]see `cargo help pkgid`[..]")
        .run();

    p.process(&targo_exe)
        .args(&["test", "--help"])
        .with_stdout_contains("[..]targo help test[..]")
        .with_stdout_contains("[..]targo test -- --help[..]")
        .with_stdout_does_not_contain("[..]Run `cargo help test`[..]")
        .with_stdout_does_not_contain("[..]Run `cargo test -- --help`[..]")
        .run();

    p.process(&targo_exe)
        .args(&["report", "future-incompatibilities", "--help"])
        .with_stdout_contains("[..]targo help report future-incompatibilities[..]")
        .with_stdout_does_not_contain("[..]Run `cargo help report future-incompatibilities`[..]")
        .run();

    p.process(&targo_exe)
        .args(&["add", "--help"])
        .with_stdout_contains("[..]Usage: targo add[..]")
        .with_stdout_contains("[..]`targo add serde`[..]")
        .with_stdout_contains("[..]Run `targo help add`[..]")
        .with_stdout_does_not_contain("[..]cargo add[..]")
        .with_stdout_does_not_contain("[..]Run `cargo help add`[..]")
        .run();

    p.process(cargo_exe())
        .args(&["build", "--help"])
        .with_stdout_contains("[..]cargo help build[..]")
        .with_stdout_contains("[..]cargo help pkgid[..]")
        .with_stdout_does_not_contain("[..]Run `targo help build`[..]")
        .run();

    p.process(cargo_exe())
        .args(&["add", "--help"])
        .with_stdout_contains("[..]Usage: cargo add[..]")
        .with_stdout_contains("[..]`cargo add serde`[..]")
        .with_stdout_contains("[..]Run `cargo help add`[..]")
        .with_stdout_does_not_contain("[..]targo add[..]")
        .run();
}

#[cargo_test]
fn targo_external_subcommands_prefer_selected_toolchain_sibling() {
    let p = project()
        .at("targo-sibling-subcommand")
        .file(
            "Cargo.toml",
            &basic_manifest("targo-sibling-subcommand", "0.0.1"),
        )
        .file(
            "src/bin/sibling-probe.rs",
            r#"fn main() { println!("SIBLING"); }"#,
        )
        .file(
            "src/bin/home-probe.rs",
            r#"fn main() { println!("HOME"); }"#,
        )
        .build();
    p.cargo("build").run();

    let toolchain_bin = p.root().join("toolchain/bin");
    fs::create_dir_all(&toolchain_bin).unwrap();
    let targo_exe = toolchain_bin.join(format!("targo{}", env::consts::EXE_SUFFIX));
    fs::hard_link(cargo_exe(), &targo_exe).unwrap();

    let command_name = format!("targo-priority-probe{}", env::consts::EXE_SUFFIX);
    fs::hard_link(p.bin("sibling-probe"), toolchain_bin.join(&command_name)).unwrap();

    let home_bin = paths::home().join(".cargo/bin");
    fs::create_dir_all(&home_bin).unwrap();
    fs::hard_link(p.bin("home-probe"), home_bin.join(&command_name)).unwrap();

    p.process(&targo_exe)
        .arg("priority-probe")
        .env("PATH", env::join_paths(path()).unwrap())
        .env(cargo::CARGO_ENV, cargo_exe())
        .with_stdout_data(str![[r#"
SIBLING

"#]])
        .run();
}

#[cargo_test]
fn direct_cargo_compat_frontend_uses_sibling_rustc() {
    let p = project()
        .at("cargo-sibling-rustc")
        .file(
            "Cargo.toml",
            &basic_manifest("cargo-sibling-rustc", "0.0.1"),
        )
        .file("src/main.rs", "fn main() {}")
        .file(
            "src/bin/rustc-proxy.rs",
            r#"
                use std::fs::OpenOptions;
                use std::io::Write as _;
                use std::process::{Command, exit};

                fn main() {
                    let marker = std::env::var_os("SIBLING_RUSTC_MARKER").unwrap();
                    writeln!(
                        OpenOptions::new().create(true).append(true).open(marker).unwrap(),
                        "invoked"
                    ).unwrap();
                    let real = std::env::var_os("REAL_RUSTC").unwrap();
                    let status = Command::new(real)
                        .args(std::env::args_os().skip(1))
                        .status()
                        .unwrap();
                    exit(status.code().unwrap_or(1));
                }
            "#,
        )
        .build();
    p.cargo("build --bin rustc-proxy").run();

    let toolchain_bin = p.root().join("toolchain/bin");
    fs::create_dir_all(&toolchain_bin).unwrap();
    let cargo = toolchain_bin.join(format!("cargo{}", env::consts::EXE_SUFFIX));
    let rustc = toolchain_bin.join(format!("rustc{}", env::consts::EXE_SUFFIX));
    fs::hard_link(cargo_exe(), &cargo).unwrap();
    fs::hard_link(p.bin("rustc-proxy"), &rustc).unwrap();

    let marker = p.root().join("sibling-rustc.marker");
    let real_rustc = env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
    p.process(&cargo)
        .arg("check")
        .env_remove("RUSTC")
        .env_remove("RUSTDOC")
        .env("REAL_RUSTC", real_rustc)
        .env("SIBLING_RUSTC_MARKER", &marker)
        .env(cargo::CARGO_ENV, cargo_exe())
        .run();

    assert!(marker.is_file(), "sibling rustc was not invoked");
}

#[cargo_test]
fn targo_honors_canonical_compiler_overrides_then_uses_trust_siblings() {
    let proxy = project()
        .at("targo-compiler-selection-proxy")
        .file(
            "Cargo.toml",
            &basic_manifest("targo-compiler-selection-proxy", "1.0.0"),
        )
        .file(
            "src/main.rs",
            r#"
                use std::ffi::{OsStr, OsString};
                use std::fs::OpenOptions;
                use std::io::Write as _;
                use std::path::Path;
                use std::process::{Command, exit};

                fn is_trust_option(option: &OsStr) -> bool {
                    let Some(option) = option.to_str() else { return false };
                    let name = option.split_once('=').map_or(option, |(name, _)| name);
                    name == "trust-verify=off" || name.starts_with("trust-")
                }

                fn main() {
                    let current = std::env::current_exe().unwrap();
                    let stem = current.file_stem().and_then(OsStr::to_str).unwrap();
                    let is_rustdoc = stem.contains("rustdoc") || stem.contains("trustdoc");
                    let real = std::env::var_os(if is_rustdoc {
                        "REAL_RUSTDOC"
                    } else {
                        "REAL_RUSTC"
                    })
                    .unwrap();
                    let marker = std::env::var_os("TARGO_TOOL_SELECTION_MARKER").unwrap();
                    writeln!(
                        OpenOptions::new().create(true).append(true).open(marker).unwrap(),
                        "{stem}"
                    )
                    .unwrap();

                    // Native targo adds its tracked Trust off-switch. The
                    // testsuite compiler is ordinary rustc/rustdoc, so remove
                    // only Trust-owned -Z options after recording selection.
                    let args = std::env::args_os().skip(1).collect::<Vec<_>>();
                    let mut forwarded: Vec<OsString> = Vec::with_capacity(args.len());
                    let mut index = 0;
                    while index < args.len() {
                        if args[index] == "-Z"
                            && args.get(index + 1).is_some_and(|arg| is_trust_option(arg))
                        {
                            index += 2;
                            continue;
                        }
                        if args[index]
                            .to_str()
                            .and_then(|arg| arg.strip_prefix("-Z"))
                            .is_some_and(|option| {
                                !option.is_empty() && is_trust_option(OsStr::new(option))
                            })
                        {
                            index += 1;
                            continue;
                        }
                        forwarded.push(args[index].clone());
                        index += 1;
                    }

                    let status = Command::new(Path::new(&real))
                        .args(forwarded)
                        // The proxy has recorded and removed Targo's protocol;
                        // keep the downstream Cargo-test shim on its ordinary
                        // compiler path rather than reactivating Trust policy.
                        .env_remove("TRUST_TARGO_FRONTEND")
                        .status()
                        .unwrap();
                    exit(status.code().unwrap_or(1));
                }
            "#,
        )
        .build();
    proxy.cargo("build").run();

    let p = project()
        .at("targo-compiler-selection")
        .file("Cargo.toml", &basic_manifest("selection-subject", "1.0.0"))
        .file("src/lib.rs", "pub fn selected() {}")
        .file(
            "build.rs",
            r#"
                fn main() {
                    if let Some(capture) = std::env::var_os("TARGO_BUILD_SCRIPT_RUSTC_CAPTURE") {
                        let rustc = std::env::var_os("RUSTC").expect("build-script RUSTC");
                        std::fs::write(capture, std::path::PathBuf::from(rustc).display().to_string())
                            .expect("record build-script RUSTC");
                    }
                }
            "#,
        )
        .build();
    let bin_dir = p.root().join("toolchain/bin");
    fs::create_dir_all(&bin_dir).unwrap();
    let executable = |name: &str| bin_dir.join(format!("{name}{}", env::consts::EXE_SUFFIX));
    let targo = executable("targo");
    fs::hard_link(cargo_exe(), &targo).unwrap();

    let proxy_bin = proxy.bin("targo-compiler-selection-proxy");
    let sibling_rustc = executable("trustc");
    let sibling_rustdoc = executable("trustdoc");
    let override_rustc = executable("rustc-override");
    let override_rustdoc = executable("rustdoc-override");
    let ambient_trustc = executable("ambient-trustc");
    let ambient_trustdoc = executable("ambient-trustdoc");
    for destination in [
        &sibling_rustc,
        &sibling_rustdoc,
        &override_rustc,
        &override_rustdoc,
        &ambient_trustc,
        &ambient_trustdoc,
    ] {
        fs::hard_link(&proxy_bin, destination).unwrap();
    }

    let marker = p.root().join("tool-selection.log");
    let build_script_rustc = p.root().join("build-script-rustc.txt");
    // Use cargo-test-support's isolated PATH. The ambient RUSTC/RUSTDOC values
    // may be bootstrap shims whose private control environment is deliberately
    // withheld from fixture subprocesses.
    let real_rustc = "rustc";
    let real_rustdoc = "rustdoc";
    let command = |subcommand: &str| {
        let mut command = p.process(&targo);
        command
            .arg("--unverified")
            .arg(subcommand)
            .env("REAL_RUSTC", &real_rustc)
            .env("REAL_RUSTDOC", &real_rustdoc)
            .env("TARGO_TOOL_SELECTION_MARKER", &marker)
            .env("TARGO_BUILD_SCRIPT_RUSTC_CAPTURE", &build_script_rustc)
            .env(cargo::CARGO_ENV, cargo_exe());
        command
    };
    let selections = || fs::read_to_string(&marker).unwrap_or_default();

    // Without an explicit Cargo-compatible override, branded Targo selects
    // the Trust compiler executables adjacent to its own binary.
    command("check")
        .env_remove("RUSTC")
        .env_remove("RUSTDOC")
        .env_remove("TRUSTC")
        .env_remove("TRUSTDOC")
        .run();
    command("doc")
        .arg("--no-deps")
        .env_remove("RUSTC")
        .env_remove("RUSTDOC")
        .env_remove("TRUSTC")
        .env_remove("TRUSTDOC")
        .run();
    let defaults = selections();
    assert!(defaults.lines().any(|line| line == "trustc"), "{defaults}");
    assert!(
        defaults.lines().any(|line| line == "trustdoc"),
        "{defaults}"
    );
    let recorded_build_script_rustc = fs::read_to_string(&build_script_rustc).unwrap();
    assert_eq!(
        Path::new(&recorded_build_script_rustc),
        sibling_rustc,
        "Targo build scripts must receive the exact selected trustc path"
    );
    assert!(
        !recorded_build_script_rustc.contains(".trust-internal"),
        "Targo retained a generated build-script compiler wrapper: {recorded_build_script_rustc}"
    );

    // RUSTC/RUSTDOC are the public Cargo override protocol. Legacy-looking
    // TRUSTC/TRUSTDOC ambient variables must neither win nor shadow them.
    p.build_dir().rm_rf();
    fs::write(&marker, "").unwrap();
    command("doc")
        .arg("--no-deps")
        .env("RUSTC", &override_rustc)
        .env("RUSTDOC", &override_rustdoc)
        .env("TRUSTC", &ambient_trustc)
        .env("TRUSTDOC", &ambient_trustdoc)
        .run();
    let overrides = selections();
    assert!(
        overrides.lines().any(|line| line == "rustc-override"),
        "{overrides}"
    );
    assert!(
        overrides.lines().any(|line| line == "rustdoc-override"),
        "{overrides}"
    );
    for forbidden in ["trustc", "trustdoc", "ambient-trustc", "ambient-trustdoc"] {
        assert!(
            !overrides.lines().any(|line| line == forbidden),
            "selected {forbidden}: {overrides}"
        );
    }

    // The same canonical identity owns the existing build.rustc/build.rustdoc
    // config seam; ambient TRUSTC/TRUSTDOC must not shadow it either.
    let toml_path = |path: &Path| {
        path.to_string_lossy()
            .replace('\\', "\\\\")
            .replace('"', "\\\"")
    };
    fs::create_dir_all(p.root().join(".cargo")).unwrap();
    fs::write(
        p.root().join(".cargo/config.toml"),
        format!(
            "[build]\nrustc = \"{}\"\nrustdoc = \"{}\"\n",
            toml_path(&override_rustc),
            toml_path(&override_rustdoc),
        ),
    )
    .unwrap();
    p.build_dir().rm_rf();
    fs::write(&marker, "").unwrap();
    command("doc")
        .arg("--no-deps")
        .env_remove("RUSTC")
        .env_remove("RUSTDOC")
        .env("TRUSTC", &ambient_trustc)
        .env("TRUSTDOC", &ambient_trustdoc)
        .run();
    let configured = selections();
    assert!(
        configured.lines().any(|line| line == "rustc-override"),
        "{configured}"
    );
    assert!(
        configured.lines().any(|line| line == "rustdoc-override"),
        "{configured}"
    );
    assert!(
        !configured
            .lines()
            .any(|line| matches!(line, "ambient-trustc" | "ambient-trustdoc")),
        "ambient branded variables shadowed config: {configured}"
    );
}

#[cargo_test]
fn explain() {
    cargo_process("--explain E0001")
        .with_stdout_data(str![[r#"
...
This error suggests that the expression arm corresponding to the noted pattern[..]
...
"#]])
        .run();
}

#[cargo_test]
fn closed_output_ok() {
    // Checks that closed output doesn't cause an error.
    let mut p = cargo_process("--list").build_command();
    p.stdout(Stdio::piped()).stderr(Stdio::piped());
    let mut child = p.spawn().unwrap();
    // Close stdout
    drop(child.stdout.take());
    // Read stderr
    let mut s = String::new();
    child
        .stderr
        .as_mut()
        .unwrap()
        .read_to_string(&mut s)
        .unwrap();
    let status = child.wait().unwrap();
    assert!(status.success());
    assert!(s.is_empty(), "{}", s);
}

#[cargo_test]
fn subcommand_leading_plus_output_contains() {
    cargo_process("+nightly")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] no such command: `+nightly`

[HELP] invoke `cargo` through `rustup` to handle `+toolchain` directives

"#]])
        .run();
}

#[cargo_test]
fn full_did_you_mean() {
    cargo_process("bluid")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] no such command: `bluid`

[HELP] a command with a similar name exists: `build`

[HELP] view all installed commands with `cargo --list`
[HELP] find a package to install `bluid` with `cargo search cargo-bluid`

"#]])
        .run();
}

#[cargo_test]
fn overwrite_cargo_environment_variable() {
    let rustc_host = rustc_host();
    // If passed arguments `arg1 arg2 ...`, this program runs them as a command.
    // If passed no arguments, this program simply prints `$CARGO`.
    let p = project()
        .file("Cargo.toml", &basic_manifest("foo", "1.0.0"))
        .file(
            "src/main.rs",
            r#"
                fn main() {
                    let mut args = std::env::args().skip(1);
                    if let Some(arg1) = args.next() {
                        let status = std::process::Command::new(arg1)
                            .args(args)
                            .status()
                            .unwrap();
                        assert!(status.success());
                    } else {
                        eprintln!("{}", std::env::var("CARGO").unwrap());
                    }
                }
            "#,
        )
        .build();

    // Create two other cargo binaries in the project root, one with the wrong
    // name and one with the right name.
    let cargo_exe = crate::utils::cargo_exe();
    let wrong_name_path = p
        .root()
        .join(format!("wrong_name{}", env::consts::EXE_SUFFIX));
    let other_cargo_path = p.root().join(cargo_exe.file_name().unwrap());
    std::fs::hard_link(&cargo_exe, &wrong_name_path).unwrap();
    std::fs::hard_link(&cargo_exe, &other_cargo_path).unwrap();

    // The output of each of the following commands should be `path-to-cargo`:
    // ```
    // cargo run
    // cargo run -- cargo run
    // cargo run -- wrong_name run
    // ```

    let cargo = cargo_exe.display().to_string();
    let wrong_name = wrong_name_path.display().to_string();
    let stderr_cargo = format!(
        "{}[EXE]\n",
        cargo_exe
            .with_extension("")
            .to_str()
            .unwrap()
            .replace(rustc_host, "[HOST_TARGET]")
    );

    for cmd in [
        "run",
        &format!("run -- {cargo} run"),
        &format!("run -- {wrong_name} run"),
    ] {
        p.cargo(cmd).with_stderr_contains(&stderr_cargo).run();
    }

    // The output of the following command should be `path-to-other-cargo`:
    // ```
    // cargo run -- other_cargo run
    // ```

    let other_cargo = other_cargo_path.display().to_string();
    let stderr_other_cargo = format!(
        "{}[EXE]\n",
        other_cargo_path
            .with_extension("")
            .to_str()
            .unwrap()
            .replace(p.root().parent().unwrap().to_str().unwrap(), "[ROOT]")
    );

    p.cargo(&format!("run -- {other_cargo} run"))
        .with_stderr_contains(stderr_other_cargo)
        .run();
}

//! Tests for `[env]` config.

use std::{env, fs};

use crate::prelude::*;
use cargo_test_support::basic_manifest;
use cargo_test_support::str;
use cargo_test_support::{basic_bin_manifest, project};

// Trust: `[env]` is workspace-controlled, so for the branded frontend it is an
// input an untrusted checkout supplies. These tests build a real proxy compiler
// to observe what actually reaches rustc, which is the only way to tell a
// refusal from a value that was merely not applied yet.
fn targo_compat_rustc_proxy(name: &str) -> cargo_test_support::Project {
    let compiler = project()
        .at(name)
        .file("Cargo.toml", &basic_manifest(name, "1.0.0"))
        .file(
            "src/main.rs",
            r#"
                use std::ffi::{OsStr, OsString};
                use std::process::Command;

                fn is_trust_option(option: &OsStr) -> bool {
                    let Some(option) = option.to_str() else { return false };
                    let name = option.split_once('=').map_or(option, |(name, _)| name);
                    name == "trust-verify=off" || name.starts_with("trust-")
                }

                fn main() {
                    let args = std::env::args_os().skip(1).collect::<Vec<_>>();
                    if args.windows(2).any(|pair| {
                        pair[0] == "--crate-name" && pair[1] == "foo"
                    }) {
                        std::fs::write(
                            std::env::var_os("ROOT_COMPILER_SENTINEL").unwrap(),
                            b"root compiler launched",
                        )
                        .unwrap();
                    }

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

                    let status = Command::new(std::env::var_os("REAL_RUSTC").unwrap())
                        .args(forwarded)
                        .status()
                        .unwrap();
                    std::process::exit(status.code().unwrap_or(1));
                }
            "#,
        )
        .build();
    compiler.cargo("build").run();
    compiler
}

#[cargo_test]
fn env_basic() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file(
            "src/main.rs",
            r#"
        use std::env;
        fn main() {
            println!( "compile-time:{}", env!("ENV_TEST_1233") );
            println!( "run-time:{}", env::var("ENV_TEST_1233").unwrap());
        }
        "#,
        )
        .file(
            ".cargo/config.toml",
            r#"
                [env]
                ENV_TEST_1233 = "Hello"
            "#,
        )
        .build();

    p.cargo("run")
        .with_stdout_data(str![[r#"
compile-time:Hello
run-time:Hello

"#]])
        .run();
}

#[cargo_test]
fn env_invalid() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file(
            "src/main.rs",
            r#"
        fn main() {
        }
        "#,
        )
        .file(
            ".cargo/config.toml",
            r#"
                [env]
                ENV_TEST_BOOL = false
            "#,
        )
        .build();

    p.cargo("check")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] error in [ROOT]/foo/.cargo/config.toml: could not load config key `env.ENV_TEST_BOOL`

Caused by:
  invalid type: boolean `false`, expected a string or map

"#]])
        .run();
}

#[cargo_test]
fn env_no_disallowed() {
    // Checks for keys that are not allowed in the [env] table.
    let p = project()
        .file("Cargo.toml", &basic_manifest("foo", "1.0.0"))
        .file("src/lib.rs", "")
        .build();

    for disallowed in &["CARGO_HOME", "RUSTUP_HOME", "RUSTUP_TOOLCHAIN"] {
        p.change_file(
            ".cargo/config.toml",
            &format!(
                r#"
                    [env]
                    {disallowed} = "foo"
                "#
            ),
        );
        p.cargo("check")
            .with_status(101)
            .with_stderr_data(format!(
                "\
[ERROR] setting the `{disallowed}` environment variable \
is not supported in the `[env]` configuration table
"
            ))
            .run();
    }
}

#[cargo_test]
fn authenticated_targo_rejects_reserved_env_authority_even_when_forced() {
    let p = project()
        .file("Cargo.toml", &basic_manifest("foo", "1.0.0"))
        .file("src/lib.rs", "")
        .file(".cargo/config.toml", "")
        .build();
    let targo = p
        .root()
        .join(format!("targo{}", std::env::consts::EXE_SUFFIX));
    fs::hard_link(crate::utils::cargo_exe(), &targo).unwrap();

    // Cover the Trust namespace, executable search/home authority, compiler
    // and flag selection (including Bootstrap-private spellings), wrappers,
    // and both fixed and prefix-based loader channels. Lower-case and Unicode
    // rows prove the boundary does not depend on the current host's
    // environment-name comparison rules.
    for key in [
        "TRUST_NO_VERIFY",
        "trust_no_verify",
        "TRUST_TARGO_NESTED_UNVERIFIED_BROKER",
        "TRUSTC",
        "CARGO_TRUST_BIN",
        "CARGO",
        "cargo",
        "CARGO_HOME",
        "cargo_home",
        "RUSTUP_HOME",
        "rustup_home",
        "RUSTUP_TOOLCHAIN",
        "rustup_toolchain",
        "PATH",
        "path",
        "PATHEXT",
        "pathext",
        "RUSTC",
        "RUSTC_OVERRIDE_VERSION_STRING",
        "rustc_override_version_string",
        "RUSTC_FORCE_RUSTC_VERSION",
        "rustc_force_rustc_version",
        "RUSTFLAGS",
        "RUSTFLAGS_BOOTSTRAP",
        "rustflags_not_bootstrap",
        "RUSTDOCFLAGS_BOOTSTRAP",
        "rustdocflags_not_bootstrap",
        "MAGIC_EXTRA_RUSTFLAGS",
        "magic_extra_rustflags",
        "RUSTC_WRAPPER",
        "RUSTC_WORKSPACE_WRAPPER",
        "CARGO_ENCODED_RUSTFLAGS",
        "CARGO_ENCODED_RUSTDOCFLAGS",
        "CARGO_BUILD_RUSTC_WRAPPER",
        "CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS",
        "TIPPY_ENCODED_ARGS",
        "tippy_encoded_args",
        "CLIPPY_ARGS",
        "clippy_args",
        "CARGO_PRIMARY_PACKAGE",
        "cargo_primary_package",
        "__CARGO_FIX_YOLO",
        "__cargo_fix_yolo",
        "__CARGO_FIX_BROKEN_CODE",
        "__cargo_fix_broken_code",
        "CARGO_FIX_MAX_RETRIES",
        "cargo_fix_max_retries",
        "LD_PRELOAD",
        "ld_preload",
        "DYLD_INSERT_LIBRARIES",
        "LIBPATH",
        "SHLIB_PATH",
        "LDR_PRELOAD",
        "RUSTC_BOOTSTRAP",
        "rustc_bootstrap",
        "SAFE_λ",
    ] {
        p.change_file(
            ".cargo/config.toml",
            &format!(
                r#"
                    [env]
                    "{key}" = {{ value = "hostile", force = true }}
                "#
            ),
        );
        p.process(&targo)
            .arg("--unverified")
            .arg("check")
            .with_status(101)
            .with_stderr_contains(format!(
                "[..]setting reserved authority environment variable `{key}` is not supported \
                 in the `[env]` configuration table for authenticated Targo[..]"
            ))
            .run();
    }
}

#[cargo_test]
fn ordinary_cargo_preserves_reserved_env_config_compatibility() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file(
            "src/main.rs",
            r#"
                fn main() {
                    println!("TRUST_NO_VERIFY={}", env!("TRUST_NO_VERIFY"));
                    println!("LD_PRELOAD={}", env!("LD_PRELOAD"));
                    println!(
                        "DYLD_INSERT_LIBRARIES={}",
                        env!("DYLD_INSERT_LIBRARIES")
                    );
                    println!("RUSTC_BOOTSTRAP={}", env!("RUSTC_BOOTSTRAP"));
                    println!(
                        "TRUST_TARGO_TEST_NO_VERIFY={}",
                        option_env!("TRUST_TARGO_TEST_NO_VERIFY").unwrap_or("<unset>")
                    );
                    println!(
                        "TEST_TRUST_SHIM_DIR={}",
                        option_env!("TEST_TRUST_SHIM_DIR").unwrap_or("<unset>")
                    );
                    println!(
                        "RUSTC_ALLOW_FEATURES={}",
                        option_env!("RUSTC_ALLOW_FEATURES").unwrap_or("<unset>")
                    );
                }
            "#,
        )
        .file(
            ".cargo/config.toml",
            r#"
                [env]
                TRUST_NO_VERIFY = { value = "ordinary-compat", force = true }
                LD_PRELOAD = { value = "", force = true }
                DYLD_INSERT_LIBRARIES = { value = "", force = true }
                RUSTC_BOOTSTRAP = { value = "-1", force = true }
                CARGO = { value = "ordinary-cargo-config", force = true }
            "#,
        )
        .build();

    p.cargo("run")
        .with_stdout_data(str![[r#"
TRUST_NO_VERIFY=ordinary-compat
LD_PRELOAD=
DYLD_INSERT_LIBRARIES=
RUSTC_BOOTSTRAP=-1
TRUST_TARGO_TEST_NO_VERIFY=<unset>
TEST_TRUST_SHIM_DIR=<unset>
RUSTC_ALLOW_FEATURES=<unset>

"#]])
        .run();
}

#[cargo_test]
fn authenticated_targo_rejects_late_build_script_process_authority() {
    let compiler = targo_compat_rustc_proxy("late-build-script-env-rustc-proxy");
    let p = project()
        .file("Cargo.toml", &basic_manifest("foo", "1.0.0"))
        .file(
            "build.rs",
            r#"
                fn main() {
                    println!("cargo::rustc-env=LD_PRELOAD=/attacker/not-loaded.so");
                }
            "#,
        )
        .file("src/lib.rs", "pub fn selected() {}")
        .build();
    let targo = p
        .root()
        .join(format!("targo{}", std::env::consts::EXE_SUFFIX));
    fs::hard_link(crate::utils::cargo_exe(), &targo).unwrap();
    let sentinel = p.root().join("root-compiler-launched");
    let real_rustc = env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());

    p.process(&targo)
        .arg("--unverified")
        .arg("check")
        .env("RUSTC", compiler.bin("late-build-script-env-rustc-proxy"))
        .env("REAL_RUSTC", real_rustc)
        .env("ROOT_COMPILER_SENTINEL", &sentinel)
        .env_remove("RUSTC_WRAPPER")
        .with_status(101)
        .with_stderr_contains(
            "[..]authenticated Targo refuses build-script `cargo::rustc-env` authority variable `LD_PRELOAD`[..]",
        )
        .run();
    assert!(
        !sentinel.exists(),
        "authority rejection must happen before launching the package compiler"
    );
}

#[cargo_test]
fn ordinary_cargo_preserves_late_build_script_env_compatibility() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file(
            "build.rs",
            r#"
                fn main() {
                    println!("cargo::rustc-env=CARGO_PRIMARY_PACKAGE=ordinary-build-script");
                    println!("cargo::rustc-env=CLIPPY_ARGS=ordinary-clippy-compat");
                    println!("cargo::rustc-env=CARGO=ordinary-cargo-compat");
                }
            "#,
        )
        .file(
            "src/main.rs",
            r#"
                fn main() {
                    println!("primary={}", env!("CARGO_PRIMARY_PACKAGE"));
                    println!("clippy={}", env!("CLIPPY_ARGS"));
                    println!("cargo={}", env!("CARGO"));
                }
            "#,
        )
        .build();

    p.cargo("run")
        .with_stdout_data(str![[r#"
primary=ordinary-build-script
clippy=ordinary-clippy-compat
cargo=ordinary-cargo-compat

"#]])
        .run();
}

#[cargo_test]
fn env_force() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file(
            "src/main.rs",
            r#"
        use std::env;
        fn main() {
            println!( "ENV_TEST_FORCED:{}", env!("ENV_TEST_FORCED") );
            println!( "ENV_TEST_UNFORCED:{}", env!("ENV_TEST_UNFORCED") );
            println!( "ENV_TEST_UNFORCED_DEFAULT:{}", env!("ENV_TEST_UNFORCED_DEFAULT") );
        }
        "#,
        )
        .file(
            ".cargo/config.toml",
            r#"
                [env]
                ENV_TEST_UNFORCED_DEFAULT = "from-config"
                ENV_TEST_UNFORCED = { value = "from-config", force = false }
                ENV_TEST_FORCED = { value = "from-config", force = true }
            "#,
        )
        .build();

    p.cargo("run")
        .env("ENV_TEST_FORCED", "from-env")
        .env("ENV_TEST_UNFORCED", "from-env")
        .env("ENV_TEST_UNFORCED_DEFAULT", "from-env")
        .with_stdout_data(str![[r#"
ENV_TEST_FORCED:from-config
ENV_TEST_UNFORCED:from-env
ENV_TEST_UNFORCED_DEFAULT:from-env

"#]])
        .run();
}

#[cargo_test]
fn env_relative() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo2"))
        .file(
            "src/main.rs",
            r#"
        use std::env;
        use std::path::Path;
        fn main() {
            println!( "ENV_TEST_REGULAR:{}", env!("ENV_TEST_REGULAR") );
            println!( "ENV_TEST_REGULAR_DEFAULT:{}", env!("ENV_TEST_REGULAR_DEFAULT") );
            println!( "ENV_TEST_RELATIVE:{}", env!("ENV_TEST_RELATIVE") );

            assert!( Path::new(env!("ENV_TEST_RELATIVE")).is_absolute() );
            assert!( !Path::new(env!("ENV_TEST_REGULAR")).is_absolute() );
            assert!( !Path::new(env!("ENV_TEST_REGULAR_DEFAULT")).is_absolute() );
        }
        "#,
        )
        .file(
            ".cargo/config.toml",
            r#"
                [env]
                ENV_TEST_REGULAR = { value = "Cargo.toml", relative = false }
                ENV_TEST_REGULAR_DEFAULT = "Cargo.toml"
                ENV_TEST_RELATIVE = { value = "Cargo.toml", relative = true }
            "#,
        )
        .build();

    p.cargo("run").run();
}

#[cargo_test]
fn env_no_override() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("unchanged"))
        .file(
            "src/main.rs",
            r#"
        use std::env;
        fn main() {
            println!( "CARGO_PKG_NAME:{}", env!("CARGO_PKG_NAME") );
        }
        "#,
        )
        .file(
            ".cargo/config.toml",
            r#"
                [env]
                CARGO_PKG_NAME = { value = "from-config", force = true }
            "#,
        )
        .build();

    p.cargo("run")
        .with_stdout_data(str![[r#"
CARGO_PKG_NAME:unchanged

"#]])
        .run();
}

#[cargo_test]
fn env_applied_to_target_info_discovery_rustc() {
    let wrapper = project()
        .at("wrapper")
        .file("Cargo.toml", &basic_manifest("wrapper", "1.0.0"))
        .file(
            "src/main.rs",
            r#"
            fn main() {
                let mut cmd = std::env::args().skip(1).collect::<Vec<_>>();
                // This will be invoked twice (with `-vV` and with all the `--print`),
                // make sure the environment variable exists each time.
                let env_test = std::env::var("ENV_TEST").unwrap();
                eprintln!("WRAPPER ENV_TEST:{env_test}");
                let (prog, args) = cmd.split_first().unwrap();
                let status = std::process::Command::new(prog)
                    .args(args).status().unwrap();
                std::process::exit(status.code().unwrap_or(1));
            }
            "#,
        )
        .build();
    wrapper.cargo("build").run();
    let wrapper = &wrapper.bin("wrapper");

    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file(
            "src/main.rs",
            r#"
            fn main() {
                eprintln!( "MAIN ENV_TEST:{}", std::env!("ENV_TEST") );
            }
            "#,
        )
        .file(
            ".cargo/config.toml",
            r#"
                [env]
                ENV_TEST = "from-config"
            "#,
        )
        .build();

    p.cargo("run")
        .env("RUSTC_WORKSPACE_WRAPPER", wrapper)
        .with_stderr_data(str![[r#"
[COMPILING] foo v0.5.0 ([ROOT]/foo)
WRAPPER ENV_TEST:from-config
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s
[RUNNING] `target/debug/foo[EXE]`
MAIN ENV_TEST:from-config

"#]])
        .run();

    // Ensure wrapper also maintains the same overridden priority for envs.
    p.cargo("clean").run();
    p.cargo("run")
        .env("ENV_TEST", "from-env")
        .env("RUSTC_WORKSPACE_WRAPPER", wrapper)
        .with_stderr_data(str![[r#"
[COMPILING] foo v0.5.0 ([ROOT]/foo)
WRAPPER ENV_TEST:from-env
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s
[RUNNING] `target/debug/foo[EXE]`
MAIN ENV_TEST:from-env

"#]])
        .run();
}

#[cargo_test]
fn env_changed_defined_in_config_toml() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file(
            "src/main.rs",
            r#"
        use std::env;
        fn main() {
            println!( "{}", env!("ENV_TEST") );
        }
        "#,
        )
        .file(
            ".cargo/config.toml",
            r#"
                [env]
                ENV_TEST = "from-config"
            "#,
        )
        .build();

    p.cargo("run")
        .with_stdout_data(str![[r#"
from-config

"#]])
        .with_stderr_data(str![[r#"
[COMPILING] foo v0.5.0 ([ROOT]/foo)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s
[RUNNING] `target/debug/foo[EXE]`

"#]])
        .run();

    p.cargo("run")
        .env("ENV_TEST", "from-env")
        .with_stdout_data(str![[r#"
from-env

"#]])
        .with_stderr_data(str![[r#"
[COMPILING] foo v0.5.0 ([ROOT]/foo)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s
[RUNNING] `target/debug/foo[EXE]`

"#]])
        .run();
    // This identical cargo invocation is to ensure no rebuild happen.
    p.cargo("run")
        .env("ENV_TEST", "from-env")
        .with_stdout_data(str![[r#"
from-env

"#]])
        .with_stderr_data(str![[r#"
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s
[RUNNING] `target/debug/foo[EXE]`

"#]])
        .run();
}

#[cargo_test]
fn forced_env_changed_defined_in_config_toml() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file(
            "src/main.rs",
            r#"
        use std::env;
        fn main() {
            println!( "{}", env!("ENV_TEST") );
        }
        "#,
        )
        .file(
            ".cargo/config.toml",
            r#"
                [env]
                ENV_TEST = {value = "from-config", force = true}
            "#,
        )
        .build();

    p.cargo("run")
        .with_stdout_data(str![[r#"
from-config

"#]])
        .with_stderr_data(str![[r#"
[COMPILING] foo v0.5.0 ([ROOT]/foo)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s
[RUNNING] `target/debug/foo[EXE]`

"#]])
        .run();

    p.cargo("run")
        .env("ENV_TEST", "from-env")
        .with_stdout_data(str![[r#"
from-config

"#]])
        .with_stderr_data(str![[r#"
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s
[RUNNING] `target/debug/foo[EXE]`

"#]])
        .run();
}

#[cargo_test]
fn env_changed_defined_in_config_args() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file(
            "src/main.rs",
            r#"
        use std::env;
        fn main() {
            println!( "{}", env!("ENV_TEST") );
        }
        "#,
        )
        .build();
    p.cargo(r#"run --config 'env.ENV_TEST="one"'"#)
        .with_stdout_data(str![[r#"
one

"#]])
        .with_stderr_data(str![[r#"
[COMPILING] foo v0.5.0 ([ROOT]/foo)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s
[RUNNING] `target/debug/foo[EXE]`

"#]])
        .run();

    p.cargo(r#"run --config 'env.ENV_TEST="two"'"#)
        .with_stdout_data(str![[r#"
two

"#]])
        .with_stderr_data(str![[r#"
[COMPILING] foo v0.5.0 ([ROOT]/foo)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s
[RUNNING] `target/debug/foo[EXE]`

"#]])
        .run();
    // This identical cargo invocation is to ensure no rebuild happen.
    p.cargo(r#"run --config 'env.ENV_TEST="two"'"#)
        .with_stdout_data(str![[r#"
two

"#]])
        .with_stderr_data(str![[r#"
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s
[RUNNING] `target/debug/foo[EXE]`

"#]])
        .run();
}

//! Tests for setting custom rustc flags.

use std::env;
use std::fs;

use crate::prelude::*;
use cargo_test_support::registry::Package;
use cargo_test_support::{
    RawOutput, basic_manifest, paths, project, project_in_home, rustc_host, str, target_spec_json,
};
use snapbox::assert_data_eq;

const AUDITED_TRUST_SPEC_MANIFEST: &str =
    include_str!("../../../../../crates/trust-spec/Cargo.toml");
const AUDITED_TRUST_SPEC_LIB: &str = include_str!("../../../../../crates/trust-spec/src/lib.rs");

trait VerifiedTargoTestEnvironment {
    fn verified_targo_environment(&mut self) -> &mut Self;
}

impl VerifiedTargoTestEnvironment for cargo_test_support::Execs {
    fn verified_targo_environment(&mut self) -> &mut Self {
        self.env("TRUST_TARGO_VERIFY", "1");
        let mut loader_variables = std::env::vars_os()
            .filter_map(|(name, _)| {
                let name_str = name.to_str()?;
                let upper = name_str.to_ascii_uppercase();
                (upper.starts_with("LD_")
                    || upper.starts_with("DYLD_")
                    || upper.starts_with("LDR_")
                    || upper.starts_with("_RLD")
                    || matches!(upper.as_str(), "LIBPATH" | "SHLIB_PATH"))
                .then_some(name_str.to_owned())
            })
            .collect::<Vec<_>>();
        loader_variables.extend(
            [
                "LD_LIBRARY_PATH",
                "LD_PRELOAD",
                "LD_AUDIT",
                "DYLD_LIBRARY_PATH",
                "DYLD_FALLBACK_LIBRARY_PATH",
                "DYLD_INSERT_LIBRARIES",
                "LIBPATH",
                "SHLIB_PATH",
                "LDR_PRELOAD",
                "LDR_AUDIT",
                "_RLD_LIST",
                "_RLDN32_LIST",
                "_RLD64_LIST",
            ]
            .into_iter()
            .map(str::to_owned),
        );
        for variable in loader_variables {
            self.env_remove(&variable);
        }
        self
    }
}

fn verified_targo_tool_proxy(name: &str) -> cargo_test_support::Project {
    let compiler = project()
        .at(name)
        .file("Cargo.toml", &basic_manifest(name, "1.0.0"))
        .file(
            "src/main.rs",
            r#"
                use std::ffi::{OsStr, OsString};
                use std::fs::OpenOptions;
                use std::io::Write;
                use std::process::Command;

                fn is_trust_option(option: &OsStr) -> bool {
                    let Some(option) = option.to_str() else { return false };
                    let name = option.split_once('=').map_or(option, |(name, _)| name);
                    name.starts_with("trust-")
                }

                fn main() {
                    let mut process_args = std::env::args_os();
                    let _proxy = process_args.next().unwrap();
                    let args = process_args.collect::<Vec<_>>();
                    let current = std::env::current_exe().unwrap();
                    let stem = current.file_stem().and_then(OsStr::to_str).unwrap();
                    let is_rustdoc = stem.contains("rustdoc") || stem.contains("trustdoc");
                    let real = std::env::var_os(if is_rustdoc {
                        "REAL_RUSTDOC"
                    } else {
                        "REAL_RUSTC"
                    })
                    .unwrap();

                    // Trust: model the exact native documentation identity on
                    // its version query; a rustdoc-named alias stays rustdoc.
                    if is_rustdoc && args.len() == 1
                        && (args[0] == "-vV" || args[0] == "-Vv")
                    {
                        let output = Command::new(&real).args(&args).output().unwrap();
                        assert!(output.status.success());
                        let text = String::from_utf8(output.stdout).unwrap();
                        if stem == "trustdoc" {
                            print!("{}", text.replace("binary: rustdoc\n", "binary: trustdoc\n"));
                        } else {
                            print!("{text}");
                        }
                        return;
                    }
                    let capture = std::env::var_os(if is_rustdoc {
                        "TRUST_RUSTDOC_ARG_CAPTURE"
                    } else {
                        "TRUST_RUSTC_ARG_CAPTURE"
                    })
                    .unwrap();
                    let mut output = OpenOptions::new()
                        .create(true)
                        .append(true)
                        .open(capture)
                        .unwrap();
                    let rendered = args
                        .iter()
                        .map(|arg| arg.to_string_lossy())
                        .collect::<Vec<_>>()
                        .join("\x1f");
                    let target_path_state =
                        if std::env::var_os("TRUST_CAPTURE_TARGET_SEARCH_ENV").is_some() {
                            if std::env::var_os("RUST_TARGET_PATH").is_some() {
                                "\x1fRUST_TARGET_PATH=present"
                            } else {
                                "\x1fRUST_TARGET_PATH=absent"
                            }
                        } else {
                            ""
                        };
                    let record = format!("{rendered}{target_path_state}\n");
                    output.write_all(record.as_bytes()).unwrap();

                    if args.iter().any(|arg| {
                        arg.to_str().is_some_and(|arg| {
                            arg.contains("trust-verify-session=")
                        })
                    }) {
                        if let Some(forgery) = std::env::var_os("TRUST_RUSTC_STDOUT_FORGERY") {
                            println!("{}", forgery.to_string_lossy());
                        }
                    }

                    let mut forwarded: Vec<OsString> = Vec::with_capacity(args.len());
                    let mut index = 0;
                    while index < args.len() {
                        if args[index].to_str() == Some("@plain-cargo-boundary.args") {
                            index += 1;
                            continue;
                        }
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

                    let mut command = Command::new(real);
                    command.args(forwarded)
                        // This proxy has deliberately stripped Targo's verified
                        // protocol. Do not let the downstream Cargo-test shim
                        // mistake the demoted compile for an authenticated edge.
                        .env_remove("TRUST_TARGO_FRONTEND");
                    // Trust: forward the inherited compiler handoff by replacing
                    // this transparent proxy, rather than spawning a new child.
                    #[cfg(unix)] {
                        use std::os::unix::process::CommandExt;
                        panic!("failed to exec compiler: {}", command.exec());
                    }
                    #[cfg(not(unix))] {
                        std::process::exit(command.status().unwrap().code().unwrap_or(1));
                    }
                }
            "#,
        )
        .build();
    compiler.cargo("build").run();
    compiler
}

fn install_verified_targo_with_trustc_proxy(
    p: &cargo_test_support::Project,
    compiler: &cargo_test_support::Project,
    proxy_name: &str,
) -> std::path::PathBuf {
    let toolchain_bin = p.root().join("verified-toolchain/bin");
    fs::create_dir_all(&toolchain_bin).unwrap();
    let targo = toolchain_bin.join(format!("targo{}", env::consts::EXE_SUFFIX));
    fs::hard_link(crate::utils::cargo_exe(), &targo).unwrap();
    fs::hard_link(
        compiler.bin(proxy_name),
        toolchain_bin.join(format!("trustc{}", env::consts::EXE_SUFFIX)),
    )
    .unwrap();
    targo
}

#[cargo_test]
fn verified_targo_rejects_compiler_stdout_on_canonical_json_channel() {
    let compiler = verified_targo_tool_proxy("verified-targo-stdout-forgery-proxy");
    let p = project()
        .at("verified-targo-stdout-forgery")
        .file("src/lib.rs", "pub fn selected() {}")
        .build();
    let targo = install_verified_targo_with_trustc_proxy(
        &p,
        &compiler,
        "verified-targo-stdout-forgery-proxy",
    );
    let capture = p.root().join("rustc-args.log");
    let proof_root = p.root().join("private-proof-artifacts");
    fs::create_dir_all(&proof_root).unwrap();

    p.process(&targo)
        .arg("check")
        .verified_targo_environment()
        .env(
            "TRUST_TARGO_LANE_RUSTFLAGS",
            [
                "-Ztrust-verify-session=stdout-forgery-session".to_string(),
                format!("-Ztrust-proof-artifact-root={}", proof_root.display()),
            ]
            .join("\x1f"),
        )
        .env_remove("RUSTC")
        .env_remove("CARGO_BUILD_RUSTC")
        .env("REAL_RUSTC", "rustc")
        .env("TRUST_RUSTC_ARG_CAPTURE", capture)
        .env(
            "TRUST_RUSTC_STDOUT_FORGERY",
            r#"{"reason":"build-finished","success":true}"#,
        )
        .env_remove("RUSTC_WRAPPER")
        .with_status(101)
        .with_stderr_contains(
            "[..]emitted unexpected stdout; the canonical Cargo JSON stdout channel is reserved for Targo-owned envelopes[..]",
        )
        .run();
}

#[cargo_test]
fn verified_targo_rejects_external_compiler_and_wrapper_before_execution() {
    let compiler = verified_targo_tool_proxy("verified-targo-compiler-authority-proxy");
    let p = project()
        .at("verified-targo-compiler-authority")
        .file("src/lib.rs", "pub fn selected() {}")
        .build();
    let targo = install_verified_targo_with_trustc_proxy(
        &p,
        &compiler,
        "verified-targo-compiler-authority-proxy",
    );
    let external_proxy = compiler.bin("verified-targo-compiler-authority-proxy");
    let capture = p.root().join("rustc-args.log");
    let proof_root = p.root().join("private-proof-artifacts");
    fs::create_dir_all(&proof_root).unwrap();
    let rustflags = [
        "-Ztrust-verify-session=compiler-authority-session".to_string(),
        format!("-Ztrust-proof-artifact-root={}", proof_root.display()),
    ]
    .join("\x1f");
    let assert_proxy_did_not_run = |boundary: &str| {
        let invocations = fs::read_to_string(&capture).unwrap_or_default();
        assert!(
            invocations.is_empty(),
            "{boundary} reached an unauthenticated compiler process: {invocations}"
        );
    };

    // The source of the sibling hard link has the same opened-file identity
    // as `trustc`, but its out-of-directory path is not an authenticated
    // frontend sibling and must not be normalized into authority.
    for compiler_variable in ["RUSTC", "CARGO_BUILD_RUSTC"] {
        p.process(&targo)
            .arg("check")
            .verified_targo_environment()
            .env("TRUST_TARGO_LANE_RUSTFLAGS", &rustflags)
            .env_remove("RUSTC")
            .env_remove("CARGO_BUILD_RUSTC")
            .env(compiler_variable, &external_proxy)
            .env_remove("RUSTC_WRAPPER")
            .env_remove("CARGO_BUILD_RUSTC_WRAPPER")
            .env_remove("RUSTC_WORKSPACE_WRAPPER")
            .env_remove("CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER")
            .env("REAL_RUSTC", "rustc")
            .env("TRUST_RUSTC_ARG_CAPTURE", &capture)
            .with_status(101)
            .with_stderr_contains(
                "[..]verified Targo requires the authenticated sibling compiler[..]",
            )
            .run();
        assert_proxy_did_not_run(compiler_variable);
    }

    for wrapper_variable in ["RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER"] {
        p.process(&targo)
            .arg("check")
            .verified_targo_environment()
            .env("TRUST_TARGO_LANE_RUSTFLAGS", &rustflags)
            .env_remove("RUSTC")
            .env_remove("CARGO_BUILD_RUSTC")
            .env_remove("RUSTC_WRAPPER")
            .env_remove("CARGO_BUILD_RUSTC_WRAPPER")
            .env_remove("RUSTC_WORKSPACE_WRAPPER")
            .env_remove("CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER")
            .env(wrapper_variable, &external_proxy)
            .env("REAL_RUSTC", "rustc")
            .env("TRUST_RUSTC_ARG_CAPTURE", &capture)
            .with_status(101)
            .with_stderr_contains("[..]verified Targo refuses[..]compiler wrapper[..]")
            .run();
        assert_proxy_did_not_run(wrapper_variable);
    }

    fs::create_dir_all(p.root().join(".cargo")).unwrap();
    fs::write(
        p.root().join(".cargo/config.toml"),
        format!("[build]\nrustc = {:?}\n", external_proxy),
    )
    .unwrap();
    p.process(&targo)
        .arg("check")
        .verified_targo_environment()
        .env("TRUST_TARGO_LANE_RUSTFLAGS", rustflags)
        .env_remove("RUSTC")
        .env_remove("CARGO_BUILD_RUSTC")
        .env_remove("RUSTC_WRAPPER")
        .env_remove("CARGO_BUILD_RUSTC_WRAPPER")
        .env_remove("RUSTC_WORKSPACE_WRAPPER")
        .env_remove("CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER")
        .env("REAL_RUSTC", "rustc")
        .env("TRUST_RUSTC_ARG_CAPTURE", &capture)
        .with_status(101)
        .with_stderr_contains("[..]verified Targo requires the authenticated sibling compiler[..]")
        .run();
    assert_proxy_did_not_run("build.rustc configuration");
}

#[cargo_test]
fn verified_targo_requires_exact_sibling_trustdoc_before_execution() {
    let compiler = verified_targo_tool_proxy("verified-targo-rustdoc-authority-proxy");
    let p = project()
        .at("verified-targo-rustdoc-authority")
        .file("src/lib.rs", "pub fn documented() {}")
        .file(
            "build.rs",
            r#"
                fn main() {
                    let capture = std::env::var_os("TARGO_BUILD_SCRIPT_RUSTDOC_CAPTURE")
                        .expect("build-script RUSTDOC capture");
                    let rustdoc = std::env::var_os("RUSTDOC").expect("build-script RUSTDOC");
                    std::fs::write(capture, std::path::PathBuf::from(rustdoc).display().to_string())
                        .expect("record build-script RUSTDOC");
                }
            "#,
        )
        .build();
    let proxy_name = "verified-targo-rustdoc-authority-proxy";
    let targo = install_verified_targo_with_trustc_proxy(&p, &compiler, proxy_name);
    let sibling_trustdoc = targo
        .parent()
        .unwrap()
        .join(format!("trustdoc{}", env::consts::EXE_SUFFIX));
    fs::hard_link(compiler.bin(proxy_name), &sibling_trustdoc).unwrap();

    let external_proxy = compiler.bin(proxy_name);
    let sibling_rustdoc = p.root().join(format!("rustdoc{}", env::consts::EXE_SUFFIX));
    fs::hard_link(&sibling_trustdoc, &sibling_rustdoc).unwrap();
    let rustc_capture = p.root().join("rustc-args.log");
    let rustdoc_capture = p.root().join("rustdoc-args.log");
    let build_script_capture = p.root().join("build-script-rustdoc.txt");
    let proof_root = p.root().join("private-proof-artifacts");
    fs::create_dir_all(&proof_root).unwrap();
    let rustflags = [
        "-Ztrust-verify-session=rustdoc-authority-session".to_string(),
        format!("-Ztrust-proof-artifact-root={}", proof_root.display()),
    ]
    .join("\x1f");
    let real_rustc = crate::utils::tools::rustc_executable();
    let real_rustdoc = crate::utils::tools::rustdoc_executable();
    let configure = |command: &mut cargo_test_support::Execs| {
        command
            .verified_targo_environment()
            .env("TRUST_TARGO_LANE_RUSTFLAGS", &rustflags)
            .env_remove("RUSTC")
            .env_remove("CARGO_BUILD_RUSTC")
            .env_remove("RUSTDOC")
            .env_remove("CARGO_BUILD_RUSTDOC")
            .env_remove("RUSTC_WRAPPER")
            .env_remove("CARGO_BUILD_RUSTC_WRAPPER")
            .env_remove("RUSTC_WORKSPACE_WRAPPER")
            .env_remove("CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER")
            .env("REAL_RUSTC", &real_rustc)
            .env("REAL_RUSTDOC", &real_rustdoc)
            .env("TRUST_RUSTC_ARG_CAPTURE", &rustc_capture)
            .env("TRUST_RUSTDOC_ARG_CAPTURE", &rustdoc_capture)
            .env("TARGO_BUILD_SCRIPT_RUSTDOC_CAPTURE", &build_script_capture);
    };

    // Trust: exercise both short spellings directly; verified Targo's actual
    // identity query below uses -Vv. The compatibility alias must stay distinct.
    for option in ["-vV", "-Vv"] {
        for (launcher, binary) in [
            (&sibling_trustdoc, "trustdoc"),
            (&sibling_rustdoc, "rustdoc"),
        ] {
            p.process(launcher)
                .arg(option)
                .env("REAL_RUSTDOC", &real_rustdoc)
                .with_stdout_contains(format!("binary: {binary}"))
                .run();
        }
    }

    // The default verified path must document successfully and build scripts
    // must receive the canonical `trustdoc` spelling, not a mutable wrapper or
    // a Cargo-compatible `rustdoc` alias.
    let mut success = p.process(&targo);
    success.arg("doc").arg("--no-deps");
    configure(&mut success);
    success.run();
    assert_eq!(
        std::path::Path::new(&fs::read_to_string(&build_script_capture).unwrap()),
        sibling_trustdoc,
        "verified Targo build scripts must receive exact sibling trustdoc"
    );
    assert!(
        !fs::read_to_string(&rustdoc_capture)
            .unwrap_or_default()
            .is_empty(),
        "canonical sibling trustdoc was not executed"
    );

    let assert_rejected_before_rustdoc = |boundary: &str| {
        let invocations = fs::read_to_string(&rustdoc_capture).unwrap_or_default();
        assert!(
            invocations.is_empty(),
            "{boundary} reached an unauthenticated documentation process: {invocations}"
        );
    };
    for (variable, selected) in [
        ("RUSTDOC", external_proxy.as_path()),
        ("CARGO_BUILD_RUSTDOC", external_proxy.as_path()),
        ("RUSTDOC", sibling_rustdoc.as_path()),
    ] {
        p.build_dir().rm_rf();
        fs::write(&rustdoc_capture, "").unwrap();
        let mut rejected = p.process(&targo);
        rejected.arg("doc").arg("--no-deps");
        configure(&mut rejected);
        rejected
            .env(variable, selected)
            .with_status(101)
            .with_stderr_contains(
                "[..]verified Targo requires the authenticated sibling documentation generator[..]",
            )
            .run();
        assert_rejected_before_rustdoc(variable);
    }

    fs::create_dir_all(p.root().join(".cargo")).unwrap();
    fs::write(
        p.root().join(".cargo/config.toml"),
        format!("[build]\nrustdoc = {:?}\n", external_proxy),
    )
    .unwrap();
    p.build_dir().rm_rf();
    fs::write(&rustdoc_capture, "").unwrap();
    let mut configured_rejection = p.process(&targo);
    configured_rejection.arg("doc").arg("--no-deps");
    configure(&mut configured_rejection);
    configured_rejection
        .with_status(101)
        .with_stderr_contains(
            "[..]verified Targo requires the authenticated sibling documentation generator[..]",
        )
        .run();
    assert_rejected_before_rustdoc("build.rustdoc configuration");
}

#[cargo_test(
    nightly,
    reason = "named custom targets require unstable rustc options"
)]
fn verified_targo_rejects_named_custom_target_before_rustc_search() {
    let compiler = verified_targo_tool_proxy("verified-targo-named-target-proxy");
    let p = project()
        .at("verified-targo-named-target")
        .file("src/lib.rs", "pub fn selected() {}")
        .file("targets/workspace-shadow-target.json", target_spec_json())
        .build();
    let target_path = p.root().join("targets");

    // Preserve upstream Cargo's named-target compatibility domain. This is
    // also a regression guard that the rejection is keyed to authenticated
    // verified Targo, not merely to the spelling of --target.
    p.cargo("rustc -Z unstable-options --target workspace-shadow-target --print cfg")
        .masquerade_as_nightly_cargo(&["print"])
        .env("RUSTFLAGS", "-Z unstable-options")
        .env("RUST_TARGET_PATH", &target_path)
        .with_stdout_data(str!["..."].unordered())
        .run();

    let targo = install_verified_targo_with_trustc_proxy(
        &p,
        &compiler,
        "verified-targo-named-target-proxy",
    );
    let capture = p.root().join("rustc-args.log");
    let proof_root = p.root().join("private-proof-artifacts");
    fs::create_dir_all(&proof_root).unwrap();

    p.process(&targo)
        .arg("check")
        .arg("--target")
        .arg("workspace-shadow-target")
        .verified_targo_environment()
        .env(
            "TRUST_TARGO_LANE_RUSTFLAGS",
            [
                "-Ztrust-verify-session=named-target-session".to_string(),
                format!("-Ztrust-proof-artifact-root={}", proof_root.display()),
                "-Zunstable-options".to_string(),
            ]
            .join("\x1f"),
        )
        .env("RUST_TARGET_PATH", &target_path)
        .env_remove("RUSTC")
        .env_remove("CARGO_BUILD_RUSTC")
        .env("REAL_RUSTC", "rustc")
        .env("TRUST_RUSTC_ARG_CAPTURE", &capture)
        .env("TRUST_CAPTURE_TARGET_SEARCH_ENV", "1")
        .env_remove("RUSTC_WRAPPER")
        .with_status(101)
        .with_stderr_contains(
            "[..]verified Targo rejects named non-built-in target `workspace-shadow-target`[..]RUST_TARGET_PATH[..]pass an explicit .json --target[..]",
        )
        .run();

    let invocations = fs::read_to_string(capture).unwrap();
    assert!(
        invocations
            .lines()
            .any(|line| line.contains("--print=target-list")
                && line.contains("RUST_TARGET_PATH=absent")),
        "verified Targo must query the exact selected compiler's built-in set: {invocations}"
    );
    assert!(
        !invocations
            .lines()
            .any(|line| { line.contains("--target") && line.contains("workspace-shadow-target") }),
        "named custom target reached rustc target search before rejection: {invocations}"
    );
}

#[cargo_test]
fn env_rustflags_normal_source() {
    let p = project()
        .file("src/lib.rs", "")
        .file("src/bin/a.rs", "fn main() {}")
        .file("examples/b.rs", "fn main() {}")
        .file("tests/c.rs", "#[test] fn f() { }")
        .file(
            "benches/d.rs",
            r#"
            #![feature(test)]
            extern crate test;
            #[bench] fn run1(_ben: &mut test::Bencher) { }
            "#,
        )
        .build();

    // Use RUSTFLAGS to pass an argument that will generate an error
    p.cargo("check --lib")
        .env("RUSTFLAGS", "-Z bogus")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
    p.cargo("check --bin=a")
        .env("RUSTFLAGS", "-Z bogus")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
    p.cargo("check --example=b")
        .env("RUSTFLAGS", "-Z bogus")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
    p.cargo("test")
        .env("RUSTFLAGS", "-Z bogus")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
    p.cargo("bench")
        .env("RUSTFLAGS", "-Z bogus")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
}

#[cargo_test]
fn env_rustflags_build_script() {
    // RUSTFLAGS should be passed to rustc for build scripts
    // when --target is not specified.
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                build = "build.rs"
            "#,
        )
        .file("src/lib.rs", "")
        .file(
            "build.rs",
            r#"
                fn main() { assert!(cfg!(foo)); }
            "#,
        )
        .build();

    p.cargo("check").env("RUSTFLAGS", "--cfg foo").run();
}

#[cargo_test]
fn env_rustflags_build_script_dep() {
    // RUSTFLAGS should be passed to rustc for build scripts
    // when --target is not specified.
    // In this test if --cfg foo is not passed the build will fail.
    let foo = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                build = "build.rs"

                [build-dependencies.bar]
                path = "../bar"
            "#,
        )
        .file("src/lib.rs", "")
        .file("build.rs", "fn main() {}")
        .build();
    let _bar = project()
        .at("bar")
        .file("Cargo.toml", &basic_manifest("bar", "0.0.1"))
        .file(
            "src/lib.rs",
            r#"
                fn bar() { }
                #[cfg(not(foo))]
                fn bar() { }
            "#,
        )
        .build();

    foo.cargo("check").env("RUSTFLAGS", "--cfg foo").run();
}

#[cargo_test]
fn env_rustflags_normal_source_with_target() {
    let p = project()
        .file("src/lib.rs", "")
        .file("src/bin/a.rs", "fn main() {}")
        .file("examples/b.rs", "fn main() {}")
        .file("tests/c.rs", "#[test] fn f() { }")
        .file(
            "benches/d.rs",
            r#"
            #![feature(test)]
            extern crate test;
            #[bench] fn run1(_ben: &mut test::Bencher) { }
            "#,
        )
        .build();

    let host = &rustc_host();

    // Use RUSTFLAGS to pass an argument that will generate an error
    p.cargo("check --lib --target")
        .arg(host)
        .env("RUSTFLAGS", "-Z bogus")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
    p.cargo("check --bin=a --target")
        .arg(host)
        .env("RUSTFLAGS", "-Z bogus")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
    p.cargo("check --example=b --target")
        .arg(host)
        .env("RUSTFLAGS", "-Z bogus")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
    p.cargo("test --target")
        .arg(host)
        .env("RUSTFLAGS", "-Z bogus")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
    p.cargo("bench --target")
        .arg(host)
        .env("RUSTFLAGS", "-Z bogus")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
}

#[cargo_test]
fn env_rustflags_build_script_with_target() {
    // RUSTFLAGS should not be passed to rustc for build scripts
    // when --target is specified.
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                build = "build.rs"
            "#,
        )
        .file("src/lib.rs", "")
        .file(
            "build.rs",
            r#"
                fn main() { assert!(!cfg!(foo)); }
            "#,
        )
        .build();

    let host = rustc_host();
    p.cargo("check --target")
        .arg(host)
        .env("RUSTFLAGS", "--cfg foo")
        .run();
}

#[cargo_test]
fn env_rustflags_build_script_with_target_doesnt_apply_to_host_kind() {
    // RUSTFLAGS should *not* be passed to rustc for build scripts when --target is specified as the
    // host tuple even if target-applies-to-host-kind is enabled, to match legacy Cargo behavior.
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                build = "build.rs"
            "#,
        )
        .file("src/lib.rs", "")
        .file(
            "build.rs",
            r#"
                fn main() { assert!(!cfg!(foo)); }
            "#,
        )
        .file(
            ".cargo/config.toml",
            r#"
                target-applies-to-host = true
            "#,
        )
        .build();

    let host = rustc_host();
    p.cargo("check --target")
        .masquerade_as_nightly_cargo(&["target-applies-to-host"])
        .arg(host)
        .arg("-Ztarget-applies-to-host")
        .env("RUSTFLAGS", "--cfg foo")
        .run();
}

#[cargo_test]
fn verified_targo_cross_target_proc_macro_policy_is_tracked_and_cargo_stays_isolated() {
    // Exercise the real frontend -> TargetInfo -> Unit -> fingerprint -> rustc
    // path. The authenticated sibling compiler proxy records the invocation before removing
    // Trust-only -Z options that the testsuite's ordinary rustc does not
    // understand. Verified Targo deliberately rejects RUSTC_WRAPPER, so the
    // test exercises its direct authenticated-compiler seam.
    let compiler = verified_targo_tool_proxy("verified-targo-rustc-proxy");

    let p = project()
        .at("verified-targo-cross-target-proc-macro")
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "selected-macro"
                version = "0.1.0"
                edition = "2024"

                [lib]
                proc-macro = true
            "#,
        )
        .file(
            "src/lib.rs",
            r#"
                extern crate proc_macro;
                use proc_macro::TokenStream;

                #[proc_macro]
                pub fn passthrough(input: TokenStream) -> TokenStream { input }
            "#,
        )
        .build();

    let targo =
        install_verified_targo_with_trustc_proxy(&p, &compiler, "verified-targo-rustc-proxy");
    let capture = p.root().join("rustc-args.log");
    let compiler_bin = compiler.bin("verified-targo-rustc-proxy");
    let real_rustc = "rustc";
    let host = rustc_host();
    // A space-bearing value keeps the encoded transport honest now that the
    // retired solver path no longer carries one.
    let proof_artifact_root = p.root().join("private proof artifacts");
    fs::create_dir_all(&proof_artifact_root).unwrap();

    let policy = |session: &str| {
        [
            "--cfg".to_string(),
            "must_not_cross_host_boundary".to_string(),
            "-Ztrust-cg-output-gate=strict".to_string(),
            "-Z".to_string(),
            "trust-policy=advisory".to_string(),
            "-Ztrust-verify-function-budget-ms=120000".to_string(),
            "-Ztrust-verify-include-dependencies=yes".to_string(),
            "-Ztrust-verify-level=2".to_string(),
            "-Ztrust-verify-output=json".to_string(),
            "-Ztrust-verify-profile=hardened".to_string(),
            format!("-Ztrust-verify-session={session}"),
            format!(
                "-Ztrust-proof-artifact-root={}",
                proof_artifact_root.display()
            ),
            "-Ztrust-verify-timeout-ms=5000".to_string(),
            "-Ztrust-verify-worker-threads=8".to_string(),
        ]
        .join("\x1f")
    };
    let selected_invocations = || {
        fs::read_to_string(&capture)
            .unwrap_or_default()
            .lines()
            .filter(|line| line.contains("--crate-name\x1fselected_macro"))
            .map(str::to_owned)
            .collect::<Vec<_>>()
    };
    let run = |frontend: &std::path::Path, session: &str| {
        let mut process = p.process(frontend);
        process
            .arg("check")
            .arg("--target")
            .arg(&host)
            .verified_targo_environment()
            .env("TRUST_TARGO_LANE_RUSTFLAGS", policy(session))
            .env("REAL_RUSTC", &real_rustc)
            // TRUSTC was never Cargo's override contract. Keep a poisoned
            // ambient value to prove branded Targo ignores it.
            .env("TRUSTC", p.root().join("ambient-trustc-must-not-run"))
            .env_remove("RUSTC_WRAPPER")
            .env("TRUST_RUSTC_ARG_CAPTURE", &capture);
        if frontend == targo {
            process.env_remove("RUSTC").env_remove("CARGO_BUILD_RUSTC");
        } else {
            // Preserve ordinary Cargo's existing direct proxy seam. It does
            // not derive or authenticate a sibling `trustc`.
            process.env("RUSTC", &compiler_bin);
        }
        process.run();
    };

    run(&targo, "proof-session-one");
    let first = selected_invocations();
    assert_eq!(
        first.len(),
        1,
        "expected one selected proc-macro invocation: {first:#?}"
    );
    let first = &first[0];
    for option in [
        "trust-cg-output-gate=strict",
        "trust-policy=advisory",
        "trust-verify-function-budget-ms=120000",
        "trust-verify-include-dependencies=yes",
        "trust-verify-level=2",
        "trust-verify-output=json",
        "trust-verify-profile=hardened",
        "trust-verify-session=proof-session-one",
        "trust-verify-timeout-ms=5000",
        "trust-verify-worker-threads=8",
        "trust-verify-crate-role=primary",
        "trust-verify-package-name=selected-macro",
    ] {
        assert!(
            first
                .split('\x1f')
                .any(|arg| arg == option || arg.strip_prefix("-Z") == Some(option)),
            "missing {option:?}: {first}"
        );
    }
    let proof_root_option = format!(
        "trust-proof-artifact-root={}",
        proof_artifact_root.display()
    );
    assert!(
        first.split('\x1f').any(|arg| {
            arg == proof_root_option.as_str()
                || arg.strip_prefix("-Z") == Some(proof_root_option.as_str())
        }),
        "missing private proof artifact root: {first}"
    );
    assert!(
        !first.contains("must_not_cross_host_boundary"),
        "unrelated target flag leaked: {first}"
    );

    // An identical proof session is fingerprint-fresh.
    fs::write(&capture, "").unwrap();
    run(&targo, "proof-session-one");
    assert!(
        selected_invocations().is_empty(),
        "identical session rebuilt the proc macro"
    );

    // The nonce is in Unit::rustflags before fingerprinting, so a new proof
    // session must rebuild even though source and all other policy are equal.
    fs::write(&capture, "").unwrap();
    run(&targo, "proof-session-two");
    let second = selected_invocations();
    assert_eq!(
        second.len(),
        1,
        "new proof session did not rebuild: {second:#?}"
    );
    assert!(second[0].contains("trust-verify-session=proof-session-two"));

    // Even with the internal marker present, a binary named `cargo` preserves
    // upstream explicit-target host isolation and injects no Targo metadata.
    fs::write(&capture, "").unwrap();
    run(&crate::utils::cargo_exe(), "plain-cargo-session");
    let ordinary = selected_invocations();
    assert_eq!(
        ordinary.len(),
        1,
        "policy removal should invalidate the Targo artifact"
    );
    // Trust: inspect option tokens, not paths such as a trust-main checkout.
    let has_trust_option = |record: &str| {
        let mut arguments = record.split('\x1f');
        while let Some(argument) = arguments.next() {
            let option = if argument == "-Z" {
                arguments.next()
            } else {
                argument.strip_prefix("-Z")
            };
            if option.is_some_and(|option| option.replace('_', "-").starts_with("trust-")) {
                return true;
            }
        }
        false
    };
    for record in [
        "-Ztrust-policy=advisory",
        "-Z\x1ftrust-policy=advisory",
        "-Ztrust_policy=advisory",
        "-Z\x1ftrust_policy=advisory",
    ] {
        assert!(has_trust_option(record), "missed Trust option: {record}");
    }
    for record in [
        "--out-dir\x1f/tmp/trust-main/target",
        "-L\x1fdependency=/tmp/trust-main/target",
        "-Z\x1funrelated=trust-policy",
    ] {
        assert!(!has_trust_option(record), "not a Trust option: {record}");
    }
    assert!(
        !has_trust_option(&ordinary[0]),
        "ordinary Cargo imported Trust policy: {}",
        ordinary[0]
    );
    assert!(!ordinary[0].contains("must_not_cross_host_boundary"));

    // A proof-looking ambient session is still just an ordinary rustc flag in
    // the Cargo compatibility domain. It must not activate Targo's per-unit
    // metadata, off-switch, fingerprint parsing, or response-file boundary
    // rejection. The wrapper records then removes the synthetic argfile before
    // invoking the testsuite's explicitly unverified Trust fixture compiler.
    fs::write(&capture, "").unwrap();
    p.process(crate::utils::cargo_exe())
        .arg("check")
        .verified_targo_environment()
        .env(
            "CARGO_ENCODED_RUSTFLAGS",
            "-Ztrust-verify-session=ambient-plain-cargo\x1f@plain-cargo-boundary.args",
        )
        .env("RUSTC", &compiler_bin)
        .env("REAL_RUSTC", &real_rustc)
        .env_remove("RUSTC_WRAPPER")
        .env("TRUST_RUSTC_ARG_CAPTURE", &capture)
        .run();
    let plain_boundary = fs::read_to_string(&capture).unwrap();
    assert!(
        plain_boundary.contains("@plain-cargo-boundary.args"),
        "plain Cargo rejected or lost the ambient argfile before rustc: {plain_boundary}"
    );
    assert!(!plain_boundary.contains("trust-verify-crate-role"));
    assert!(!plain_boundary.contains("trust-verify-package-name"));
    assert!(!plain_boundary.contains("trust-verify=off"));
}

// Trust: test the owning frontend/Unit/cache path with the existing compiler
// proxy. The proxy supplies no proof evidence: these are admission/argv tests.
#[cargo_test]
fn verified_targo_host_policy_assertions_preserve_unit_identity() {
    let proxy_name = "verified-host-assertion-proxy";
    let compiler = verified_targo_tool_proxy(proxy_name);
    let p = project()
        .at("verified-host-assertions")
        .file(
            "Cargo.toml",
            r#"
            [package]
            name = "selected-macro"
            version = "0.1.0"
            edition = "2024"
            [lib]
            proc-macro = true
            [dependencies]
            shared = { path = "shared" }
            [workspace]
            members = ["normal"]
            exclude = ["shared"]
            [profile.dev]
            debug = 0
        "#,
        )
        .file(
            "src/lib.rs",
            r#"
            extern crate proc_macro;
            #[proc_macro]
            pub fn passthrough(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
                shared::value();
                input
            }
        "#,
        )
        .file(
            "normal/Cargo.toml",
            r#"
            [package]
            name = "normal"
            version = "0.1.0"
            edition = "2024"
            [dependencies]
            shared = { path = "../shared" }
        "#,
        )
        .file(
            "normal/src/lib.rs",
            "pub fn value() -> u32 { shared::value() }",
        )
        .file("shared/Cargo.toml", &basic_manifest("shared", "0.1.0"))
        .file("shared/src/lib.rs", "pub fn value() -> u32 { 1 }")
        .build();
    let targo = install_verified_targo_with_trustc_proxy(&p, &compiler, proxy_name);
    let capture = p.root().join("rustc-args.log");
    let proof_root = p.root().join("private-proof-artifacts");
    fs::create_dir_all(&proof_root).unwrap();
    let host_policy = [
        "-Ztrust-verify=on",
        "-Ztrust-policy=certify",
        "-Ztrust-verify-level=2",
        "-Ztrust-verify-profile=unix_hardened",
        "-Ztrust-verify-include-dependencies=yes",
        "-Ztrust-ir-lower=strict",
    ];
    let run = |host_flags: &[&str],
               session: &str,
               explicit_target: bool,
               compile_time_only: bool,
               diagnostic: Option<&str>| {
        let mut policy = host_policy[1..]
            .iter()
            .map(|flag| flag.to_string())
            .collect::<Vec<_>>();
        policy.extend([
            format!("-Ztrust-verify-session={session}"),
            format!("-Ztrust-proof-artifact-root={}", proof_root.display()),
        ]);
        fs::write(&capture, "").unwrap();
        let mut process = p.process(&targo);
        process
            .arg("check")
            .arg("--workspace")
            .masquerade_as_nightly_cargo(&[
                "host-config",
                "target-applies-to-host",
                "compile-time-deps",
            ])
            .arg("-Zhost-config")
            .arg("-Ztarget-applies-to-host")
            .arg("--config")
            .arg("target-applies-to-host=false")
            .arg("--config")
            .arg(format!(
                "host.rustflags={}",
                serde_json::to_string(host_flags).unwrap()
            ))
            .verified_targo_environment()
            .env("TRUST_TARGO_LANE_RUSTFLAGS", policy.join("\x1f"))
            .env_remove("RUSTFLAGS")
            .env_remove("RUSTC")
            .env_remove("CARGO_BUILD_RUSTC")
            .env_remove("RUSTC_WRAPPER")
            .env_remove("RUSTC_WORKSPACE_WRAPPER")
            .env("REAL_RUSTC", "rustc")
            .env("TRUST_RUSTC_ARG_CAPTURE", &capture);
        if explicit_target {
            process.arg("--target").arg(rustc_host());
        }
        if compile_time_only {
            process.arg("-Zunstable-options").arg("--compile-time-deps");
        }
        if let Some(diagnostic) = diagnostic {
            process.with_status(101).with_stderr_contains(diagnostic);
        }
        process.run();
        fs::read_to_string(&capture).unwrap_or_default()
    };
    let compiled = |output: &str, name: &str| {
        output
            .lines()
            .filter(|line| line.contains(&format!("--crate-name\x1f{name}\x1f")))
            .count()
    };
    for explicit_target in [false, true] {
        let session = if explicit_target {
            "assertion-explicit"
        } else {
            "assertion-native"
        };
        let output = run(&host_policy, session, explicit_target, false, None);
        assert_eq!(compiled(&output, "selected_macro"), 1);
        // Native graph canonicalization maps both shared units to Host. They
        // must stay distinct because only one carries the host requirement.
        assert_eq!(compiled(&output, "shared"), 2, "{output}");
        assert!(
            !output.contains("trust-verify=on"),
            "assertion reached compiler argv: {output}"
        );
        assert!(
            !output.contains("trust-verify=off"),
            "eligible units were scoped out: {output}"
        );
        let selected = output
            .lines()
            .find(|line| line.contains("--crate-name\x1fselected_macro\x1f"))
            .unwrap();
        for option in &host_policy[1..] {
            assert_eq!(
                selected
                    .split('\x1f')
                    .filter(|argument| argument == option)
                    .count(),
                1,
                "{selected}"
            );
        }
        let warm = run(&host_policy, session, explicit_target, false, None);
        assert_eq!(compiled(&warm, "selected_macro"), 0);
        assert_eq!(compiled(&warm, "shared"), 0);
    }
    for (host_flags, diagnostic) in [
        (
            vec!["-Ztrust-verify=on", "-Ztrust-ir-lower=off"],
            "[..]does not match imported[..]",
        ),
        (
            vec!["-Ztrust-verify=on", "-Ztrust-ir-lower"],
            "[..]requires an explicit value[..]",
        ),
        (
            vec![
                "-Ztrust-verify=on",
                "-Ztrust-ir-lower=strict",
                "-Ztrust_ir_lower=strict",
            ],
            "[..]duplicate [host] policy assertion[..]",
        ),
        (
            vec!["-Ztrust-verify=on", "-Ztrust_verify=on"],
            "[..]duplicate -Ztrust-verify assertions[..]",
        ),
        (
            vec!["-Ztrust-verify=on", "-Ztrust-verify-crate-role=primary"],
            "[..][host] rustflags cannot set[..]",
        ),
        (
            vec!["-Ztrust-verify=on", "-Ztrust-verify-session=forged"],
            "[..][host] rustflags cannot set[..]",
        ),
    ] {
        let output = run(
            &host_flags,
            "assertion-negative",
            false,
            false,
            Some(diagnostic),
        );
        assert_eq!(compiled(&output, "selected_macro"), 0, "{output}");
        assert_eq!(compiled(&output, "shared"), 0, "{output}");
    }
    // This root is skipped before prepare_rustc, so its refusal specifically
    // pins compile()'s early guard, independently of the final-argv recheck.
    let skipped = run(
        &host_policy,
        "assertion-filtered",
        true,
        true,
        Some("[..]required verification is unavailable: compile-time-deps-filtered[..]"),
    );
    assert_eq!(compiled(&skipped, "selected_macro"), 0, "{skipped}");
    assert_eq!(compiled(&skipped, "shared"), 0, "{skipped}");
}

// Trust: an already-cached excluded unit cannot discharge a new assertion.
// Dependency inclusion must instead compile the complete host support closure
// with verification enabled, including when prior scoped artifacts are warm.
#[cargo_test]
fn verified_targo_host_policy_assertion_covers_warm_build_support_when_included() {
    let proxy_name = "verified-host-assertion-cache-proxy";
    let compiler = verified_targo_tool_proxy(proxy_name);
    let p = project()
        .at("verified-host-assertion-cache")
        .file(
            "Cargo.toml",
            r#"
            [package]
            name = "foo"
            version = "0.1.0"
            edition = "2024"
            [build-dependencies]
            support = { path = "support" }
        "#,
        )
        .file(
            "support/Cargo.toml",
            r#"
            [package]
            name = "support"
            version = "0.1.0"
            edition = "2024"
            [dependencies]
            transitive = { path = "../transitive" }
        "#,
        )
        .file(
            "support/src/lib.rs",
            "pub fn value() -> u32 { transitive::value() }",
        )
        .file(
            "transitive/Cargo.toml",
            r#"
            [package]
            name = "transitive"
            version = "0.1.0"
            edition = "2024"
        "#,
        )
        .file("transitive/src/lib.rs", "pub fn value() -> u32 { 1 }")
        .file("src/lib.rs", "pub fn value() -> u32 { 1 }")
        .file("build.rs", "fn main() { let _ = support::value(); }")
        .build();
    let targo = install_verified_targo_with_trustc_proxy(&p, &compiler, proxy_name);
    // Trust: build scripts receive the authenticated sibling trustdoc even
    // during check. Its real version and compiler route remain harness-owned.
    fs::hard_link(
        compiler.bin(proxy_name),
        targo
            .parent()
            .unwrap()
            .join(format!("trustdoc{}", env::consts::EXE_SUFFIX)),
    )
    .unwrap();
    let capture = p.root().join("rustc-args.log");
    let rustdoc_capture = p.root().join("rustdoc-args.log");
    let proof_root = p.root().join("private-proof-artifacts");
    fs::create_dir_all(&proof_root).unwrap();
    let policy = |include_dependencies: bool| {
        [
            "-Ztrust-policy=certify".to_string(),
            "-Ztrust-verify-level=2".to_string(),
            "-Ztrust-verify-profile=unix_hardened".to_string(),
            format!("-Ztrust-verify-include-dependencies={include_dependencies}"),
            "-Ztrust-ir-lower=strict".to_string(),
            "-Ztrust-verify-session=warm-host-assertion".to_string(),
            format!("-Ztrust-proof-artifact-root={}", proof_root.display()),
        ]
        .join("\x1f")
    };
    let run = |include_dependencies: bool, required: bool, json: bool| {
        fs::write(&capture, "").unwrap();
        let mut process = p.process(&targo);
        process
            .arg("check")
            .masquerade_as_nightly_cargo(&["host-config", "target-applies-to-host"])
            .arg("-Zhost-config")
            .arg("-Ztarget-applies-to-host")
            .arg("--config")
            .arg("target-applies-to-host=false")
            .arg("--config")
            .arg(if required {
                "host.rustflags=['-Ztrust-verify=on']"
            } else {
                "host.rustflags=[]"
            })
            .verified_targo_environment()
            .env("TRUST_TARGO_LANE_RUSTFLAGS", policy(include_dependencies))
            .env_remove("RUSTFLAGS")
            .env_remove("RUSTC")
            .env_remove("CARGO_BUILD_RUSTC")
            .env_remove("RUSTDOC")
            .env_remove("CARGO_BUILD_RUSTDOC")
            .env_remove("RUSTC_WRAPPER")
            .env_remove("RUSTC_WORKSPACE_WRAPPER")
            .env("REAL_RUSTC", "rustc")
            .env("REAL_RUSTDOC", "rustdoc")
            .env("TRUST_RUSTC_ARG_CAPTURE", &capture)
            .env("TRUST_RUSTDOC_ARG_CAPTURE", &rustdoc_capture);
        if json {
            process.arg("--message-format=json");
        }
        if required && !include_dependencies {
            process
                .with_status(101)
                .with_stderr_contains("[..]cannot satisfy -Ztrust-verify=on assertion[..]")
                .with_stderr_contains("[..]required verification is unavailable[..]");
        }
        process.run();
        fs::read_to_string(&capture).unwrap_or_default()
    };
    let initial = run(false, false, false);
    assert!(
        initial.contains("--crate-name\x1fbuild_script_build\x1f"),
        "{initial}"
    );
    for name in ["build_script_build", "support", "transitive"] {
        let invocation = initial
            .lines()
            .find(|line| line.contains(&format!("--crate-name\x1f{name}\x1f")))
            .unwrap();
        assert!(invocation.contains("trust-verify=off"), "{invocation}");
    }
    assert!(!run(false, false, false).contains("--crate-name\x1fbuild_script_build\x1f"));
    for json in [false, true] {
        let refused = run(false, true, json);
        for line in refused
            .lines()
            .filter(|line| line.contains("--crate-name\x1f"))
        {
            assert!(
                line.contains("--crate-name\x1f___\x1f"),
                "queued compiler ran before refusal: {line}"
            );
        }
    }
    for json in [false, true] {
        let included = run(true, true, json);
        assert!(!included.contains("trust-verify=off"), "{included}");
        if !json {
            let build_script = included
                .lines()
                .find(|line| line.contains("--crate-name\x1fbuild_script_build\x1f"))
                .unwrap();
            assert!(
                build_script.contains("trust-verify-crate-role=build-script"),
                "{build_script}"
            );
            for name in ["build_script_build", "support", "transitive"] {
                assert!(
                    included.contains(&format!("--crate-name\x1f{name}\x1f")),
                    "previously unverified host unit was reused: {name}: {included}"
                );
            }
        }
    }
}

#[cargo_test]
fn verified_targo_test_authorizes_the_linked_library_execution_subject_only() {
    let compiler = verified_targo_tool_proxy("verified-targo-test-monitor-rustc-proxy");
    let p = project()
        .at("verified-targo-test-monitor-scope")
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "selected-monitor-subject"
                version = "0.1.0"
                edition = "2024"
                build = "build.rs"

                [dependencies]
                unrelated-dep = { path = "unrelated-dep" }
                selected-runtime = { path = "selected-runtime" }

                [workspace]
                members = [".", "selected-runtime"]
                default-members = ["."]
                exclude = ["unrelated-dep"]
                resolver = "3"

                [[test]]
                name = "harnessless_execution"
                harness = false

                [[bench]]
                name = "linked_execution"
                harness = false
            "#,
        )
        .file(
            "src/lib.rs",
            r#"
                /// Adds one.
                ///
                /// ```
                /// assert_eq!(selected_monitor_subject::add_one(1), 2);
                /// ```
                pub fn add_one(value: u32) -> u32 {
                    unrelated_dep::identity(value) + 1
                }

                #[cfg(test)]
                mod tests {
                    #[test]
                    fn unit_root_uses_the_library() {
                        assert_eq!(super::add_one(2), 3);
                    }
                }
            "#,
        )
        .file(
            "tests/integration.rs",
            r#"
                #[test]
                fn integration_root_uses_the_linked_library() {
                    assert_eq!(selected_monitor_subject::add_one(3), 4);
                    assert_eq!(selected_runtime::identity(4), 4);
                    let binary = env!("CARGO_BIN_EXE_fixture-tool");
                    assert!(!binary.is_empty());
                }
            "#,
        )
        .file(
            "tests/harnessless_execution.rs",
            r#"
                fn main() {
                    assert_eq!(selected_monitor_subject::add_one(5), 6);
                }
            "#,
        )
        .file("src/bin/fixture-tool.rs", "fn main() {}")
        .file(
            "benches/linked_execution.rs",
            r#"
                fn main() {
                    assert_eq!(selected_monitor_subject::add_one(4), 5);
                }
            "#,
        )
        .file("build.rs", "fn main() {}")
        .file(
            "unrelated-dep/Cargo.toml",
            &basic_manifest("unrelated-dep", "0.1.0"),
        )
        .file(
            "unrelated-dep/src/lib.rs",
            "pub fn identity(value: u32) -> u32 { value }",
        )
        .file(
            "selected-runtime/Cargo.toml",
            &basic_manifest("selected-runtime", "0.1.0"),
        )
        .file(
            "selected-runtime/src/lib.rs",
            r#"
                pub fn identity(value: u32) -> u32 { value }

                #[cfg(test)]
                mod tests {
                    #[test]
                    fn selected_workspace_root() {
                        assert_eq!(super::identity(5), 5);
                    }
                }
            "#,
        )
        .build();

    let targo = install_verified_targo_with_trustc_proxy(
        &p,
        &compiler,
        "verified-targo-test-monitor-rustc-proxy",
    );
    fs::hard_link(
        compiler.bin("verified-targo-test-monitor-rustc-proxy"),
        targo
            .parent()
            .unwrap()
            .join(format!("trustdoc{}", env::consts::EXE_SUFFIX)),
    )
    .unwrap();
    let capture = p.root().join("rustc-args.log");
    let rustdoc_capture = p.root().join("rustdoc-args.log");
    let real_rustc = "rustc";
    let real_rustdoc = "rustdoc";
    let proof_root = p.root().join("private-proof-artifacts");
    fs::create_dir_all(&proof_root).unwrap();

    let verified_flags = |session: &str| {
        [
            "-Coverflow-checks=yes".to_string(),
            "-Cdebug-assertions=yes".to_string(),
            format!("-Ztrust-verify-session={session}"),
            format!("-Ztrust-proof-artifact-root={}", proof_root.display()),
        ]
        .join("\x1f")
    };
    let command = |command: &str, session: &str, args: &[&str]| {
        let mut process = p.process(&targo);
        process
            .arg(command)
            .verified_targo_environment()
            .env("TRUST_TARGO_LANE_RUSTFLAGS", verified_flags(session))
            .env_remove("RUSTC")
            .env_remove("CARGO_BUILD_RUSTC")
            .env_remove("RUSTDOC")
            .env_remove("CARGO_BUILD_RUSTDOC")
            .env("REAL_RUSTC", &real_rustc)
            .env("REAL_RUSTDOC", &real_rustdoc)
            .env_remove("RUSTC_WRAPPER")
            .env("TRUST_RUSTC_ARG_CAPTURE", &capture)
            .env("TRUST_RUSTDOC_ARG_CAPTURE", &rustdoc_capture);
        for arg in args {
            process.arg(arg);
        }
        process
    };
    let run = |verb: &str, session: &str, args: &[&str]| {
        command(verb, session, args).run();
    };
    let invocations = || {
        fs::read_to_string(&capture)
            .unwrap_or_default()
            .lines()
            .map(|line| line.split('\x1f').map(str::to_owned).collect::<Vec<_>>())
            .collect::<Vec<_>>()
    };
    let has_pair = |args: &[String], option: &str, value: &str| {
        args.windows(2)
            .any(|pair| pair[0] == option && pair[1] == value)
    };
    let has_z_option = |args: &[String], expected: &str| {
        args.iter().enumerate().any(|(index, arg)| {
            (arg == "-Z" && args.get(index + 1).is_some_and(|arg| arg == expected))
                || arg.strip_prefix("-Z") == Some(expected)
        })
    };
    let z_option_count = |args: &[String], expected: &str| {
        args.iter()
            .enumerate()
            .filter(|(index, arg)| {
                (*arg == "-Z" && args.get(index + 1).is_some_and(|arg| arg == expected))
                    || arg.strip_prefix("-Z") == Some(expected)
            })
            .count()
    };

    // Trust: a build script needs the authenticated documentation sibling even
    // for --no-run. First retain that refusal, then complete the real-delegating
    // fixture toolchain instead of weakening the production launcher boundary.
    command("test", "missing-rustdoc-session", &["--no-run"])
        .with_status(101)
        .with_stderr_contains(
            "[..]verified Targo requires the authenticated sibling documentation generator[..]",
        )
        .run();
    assert!(
        invocations().iter().all(|args| {
            !args
                .iter()
                .any(|arg| arg == "--emit" || arg.starts_with("--emit="))
        }),
        "missing authenticated trustdoc reached a crate compilation"
    );
    assert!(
        fs::read_to_string(&rustdoc_capture)
            .unwrap_or_default()
            .is_empty(),
        "missing authenticated trustdoc reached a documentation process"
    );
    fs::hard_link(
        compiler.bin("verified-targo-test-monitor-rustc-proxy"),
        targo
            .parent()
            .unwrap()
            .join(format!("trustdoc{}", env::consts::EXE_SUFFIX)),
    )
    .unwrap();
    fs::write(&capture, "").unwrap();

    run("test", "test-monitor-session", &["--no-run"]);
    let test_invocations = invocations();
    let linked_libraries = test_invocations
        .iter()
        .filter(|args| {
            has_pair(args, "--crate-name", "selected_monitor_subject")
                && has_pair(args, "--crate-type", "lib")
                && !args.iter().any(|arg| arg == "--test")
        })
        .collect::<Vec<_>>();
    assert_eq!(
        linked_libraries.len(),
        1,
        "expected exactly one non-test library linked by the integration test: {test_invocations:#?}"
    );
    let linked_library = linked_libraries[0];
    assert!(
        has_z_option(linked_library, "trust-certified-test-monitors"),
        "the linked Build-mode library lacked monitor authorization: {linked_library:?}"
    );
    assert!(
        !has_z_option(linked_library, "trust-verify=off"),
        "the linked Build-mode library was disabled: {linked_library:?}"
    );
    let scope_decisions = linked_library
        .iter()
        .enumerate()
        .filter_map(|(index, arg)| {
            let option = if arg == "-Z" {
                linked_library.get(index + 1).map(String::as_str)
            } else {
                arg.strip_prefix("-Z")
            }?;
            matches!(option, "trust-verify=off" | "trust-certified-test-monitors").then_some(option)
        })
        .collect::<Vec<_>>();
    assert_eq!(scope_decisions, ["trust-certified-test-monitors"]);

    let primary_roots = test_invocations
        .iter()
        .filter(|args| {
            args.iter().any(|arg| arg == "--test")
                && (has_pair(args, "--crate-name", "selected_monitor_subject")
                    || has_pair(args, "--crate-name", "integration"))
        })
        .collect::<Vec<_>>();
    assert_eq!(
        primary_roots.len(),
        2,
        "expected the selected unit-test and integration roots: {test_invocations:#?}"
    );
    for root in primary_roots {
        assert!(has_z_option(root, "trust-verify-crate-role=primary"));
        assert!(!has_z_option(root, "trust-verify=off"));
        assert!(!has_z_option(root, "trust-certified-test-monitors"));
    }

    // A harness-free `[[test]]` remains a selected Test-mode root, but Cargo
    // executes its ordinary `main` and therefore does not pass rustc's native
    // `--test` switch. The exact root still owns primary proof authority, and
    // must receive the certified-monitor bit exactly once to cover execution.
    let harnessless_test_roots = test_invocations
        .iter()
        .filter(|args| {
            has_pair(args, "--crate-name", "harnessless_execution")
                && !args.iter().any(|arg| arg == "--test")
        })
        .collect::<Vec<_>>();
    assert_eq!(
        harnessless_test_roots.len(),
        1,
        "expected one harness-free Test root: {test_invocations:#?}"
    );
    let harnessless_test_root = harnessless_test_roots[0];
    assert_eq!(
        z_option_count(harnessless_test_root, "trust-certified-test-monitors"),
        1,
        "harness-free Test root must receive exactly one monitor authorization: {harnessless_test_root:?}"
    );
    assert!(has_z_option(
        harnessless_test_root,
        "trust-verify-crate-role=primary"
    ));
    assert!(!has_z_option(harnessless_test_root, "trust-verify=off"));

    let unrelated_dependencies = test_invocations
        .iter()
        .filter(|args| has_pair(args, "--crate-name", "unrelated_dep"))
        .collect::<Vec<_>>();
    assert_eq!(unrelated_dependencies.len(), 1);
    for dependency in unrelated_dependencies {
        assert!(has_z_option(dependency, "trust-verify=off"));
        assert!(!has_z_option(dependency, "trust-certified-test-monitors"));
    }
    let build_scripts = test_invocations
        .iter()
        .filter(|args| has_pair(args, "--crate-name", "build_script_build"))
        .collect::<Vec<_>>();
    assert_eq!(build_scripts.len(), 1);
    for build_script in build_scripts {
        assert!(has_z_option(build_script, "trust-verify=off"));
        assert!(!has_z_option(build_script, "trust-certified-test-monitors"));
    }

    // Integration tests can directly execute same-package binaries through
    // Cargo's authenticated CARGO_BIN_EXE_* graph edge. The ordinary Build
    // unit is a distinct execution subject from the binary's `--test` root.
    let linked_binary = test_invocations
        .iter()
        .filter(|args| {
            has_pair(args, "--crate-name", "fixture_tool")
                && has_pair(args, "--crate-type", "bin")
                && !args.iter().any(|arg| arg == "--test")
        })
        .collect::<Vec<_>>();
    assert_eq!(
        linked_binary.len(),
        1,
        "expected one Build-mode CARGO_BIN_EXE_* subject: {test_invocations:#?}"
    );
    assert!(has_z_option(
        linked_binary[0],
        "trust-certified-test-monitors"
    ));
    assert!(!has_z_option(linked_binary[0], "trust-verify=off"));

    // Cargo bench has a separate UserIntent even though its harness links the
    // same cfg(not(test)) library execution unit as an integration test.
    fs::write(&capture, "").unwrap();
    run("bench", "bench-monitor-session", &["--no-run"]);
    let bench_invocations = invocations();
    let bench_linked_library = bench_invocations
        .iter()
        .filter(|args| {
            has_pair(args, "--crate-name", "selected_monitor_subject")
                && has_pair(args, "--crate-type", "lib")
                && !args.iter().any(|arg| arg == "--test")
        })
        .collect::<Vec<_>>();
    assert_eq!(
        bench_linked_library.len(),
        1,
        "expected one library execution subject for `cargo bench --no-run`: {bench_invocations:#?}"
    );
    assert!(has_z_option(
        bench_linked_library[0],
        "trust-certified-test-monitors"
    ));
    assert!(!has_z_option(bench_linked_library[0], "trust-verify=off"));

    // The same boundary applies to an explicit harness-free `[[bench]]` root:
    // Cargo will execute it, but rustc sees no native `--test` harness marker.
    let harnessless_bench_roots = bench_invocations
        .iter()
        .filter(|args| {
            has_pair(args, "--crate-name", "linked_execution")
                && !args.iter().any(|arg| arg == "--test")
        })
        .collect::<Vec<_>>();
    assert_eq!(
        harnessless_bench_roots.len(),
        1,
        "expected one harness-free Bench root: {bench_invocations:#?}"
    );
    let harnessless_bench_root = harnessless_bench_roots[0];
    assert_eq!(
        z_option_count(harnessless_bench_root, "trust-certified-test-monitors"),
        1,
        "harness-free Bench root must receive exactly one monitor authorization: {harnessless_bench_root:?}"
    );
    assert!(has_z_option(
        harnessless_bench_root,
        "trust-verify-crate-role=primary"
    ));
    assert!(!has_z_option(harnessless_bench_root, "trust-verify=off"));

    // Selection and execution reachability can be proven by different roots.
    // Here selected-runtime is a selected workspace package and its ordinary
    // Build library is a direct dependency of the other package's integration
    // root; neither fact alone is sufficient to grant monitor authority.
    fs::write(&capture, "").unwrap();
    run(
        "test",
        "workspace-monitor-session",
        &["--workspace", "--no-run"],
    );
    let workspace_invocations = invocations();
    let cross_package_library = workspace_invocations
        .iter()
        .filter(|args| {
            has_pair(args, "--crate-name", "selected_runtime")
                && has_pair(args, "--crate-type", "lib")
                && !args.iter().any(|arg| arg == "--test")
        })
        .collect::<Vec<_>>();
    assert_eq!(
        cross_package_library.len(),
        1,
        "expected one cross-package Build execution subject: {workspace_invocations:#?}"
    );
    assert!(has_z_option(
        cross_package_library[0],
        "trust-certified-test-monitors"
    ));
    assert!(!has_z_option(cross_package_library[0], "trust-verify=off"));

    // A build has no test execution graph, even for the same selected package.
    fs::write(&capture, "").unwrap();
    run("build", "build-without-monitor-session", &[]);
    let build_invocations = invocations();
    assert!(
        build_invocations
            .iter()
            .all(|args| !has_z_option(args, "trust-certified-test-monitors")),
        "verified `targo build` authorized test monitors: {build_invocations:#?}"
    );

    // The monitor bit is a Cargo graph decision, not a caller-selectable rustc
    // option. Authenticated compiler-discovery probes may run, but reject the
    // bit before any crate compilation reaches the proxy.
    fs::write(&capture, "").unwrap();
    p.process(&targo)
        .arg("test")
        .arg("--no-run")
        .verified_targo_environment()
        .env(
            "TRUST_TARGO_LANE_RUSTFLAGS",
            format!(
                "{}\x1f-Ztrust-certified-test-monitors",
                verified_flags("caller-spoof-session")
            ),
        )
        .env_remove("RUSTC")
        .env_remove("CARGO_BUILD_RUSTC")
        .env_remove("RUSTDOC")
        .env_remove("CARGO_BUILD_RUSTDOC")
        .env("REAL_RUSTC", &real_rustc)
        .env("REAL_RUSTDOC", &real_rustdoc)
        .env_remove("RUSTC_WRAPPER")
        .env("TRUST_RUSTC_ARG_CAPTURE", &capture)
        .env("TRUST_RUSTDOC_ARG_CAPTURE", &rustdoc_capture)
        .with_status(101)
        .with_stderr_contains(
            "[..]-Ztrust_certified_test_monitors is not part of the verified Targo host-policy protocol[..]",
        )
        .run();
    let spoof_invocations = invocations();
    assert!(
        spoof_invocations.iter().all(|args| {
            !args
                .iter()
                .any(|arg| arg == "--emit" || arg.starts_with("--emit="))
                && !has_z_option(args, "trust-certified-test-monitors")
        }),
        "caller-supplied monitor authority reached a crate compilation: {spoof_invocations:#?}"
    );
}

#[cargo_test]
fn verified_targo_rejects_name_only_trust_proc_macro_shadow() {
    let compiler = verified_targo_tool_proxy("verified-targo-hostile-shadow-rustc-proxy");
    let p = project()
        .at("verified-targo-hostile-trust-shadow")
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "selected"
                version = "0.1.0"
                edition = "2024"

                [dependencies]
                trust = { package = "hostile-shadow", path = "trust-shadow" }
            "#,
        )
        .file(
            "src/lib.rs",
            "#[trust::passthrough]\npub fn selected() {}\n",
        )
        .file(
            "trust-shadow/Cargo.toml",
            r#"
                [package]
                name = "hostile-shadow"
                version = "0.1.1"
                edition = "2024"

                [lib]
                name = "trust"
                proc-macro = true
            "#,
        )
        .file(
            "trust-shadow/src/lib.rs",
            r#"
                extern crate proc_macro;
                use proc_macro::TokenStream;

                #[proc_macro_attribute]
                pub fn passthrough(_attr: TokenStream, item: TokenStream) -> TokenStream {
                    item
                }
            "#,
        )
        .build();

    let targo = install_verified_targo_with_trustc_proxy(
        &p,
        &compiler,
        "verified-targo-hostile-shadow-rustc-proxy",
    );
    let capture = p.root().join("rustc-args.log");
    let proof_root = p.root().join("private-proof-artifacts");
    fs::create_dir_all(&proof_root).unwrap();
    let rustflags = [
        "-Coverflow-checks=yes".to_string(),
        "-Cdebug-assertions=yes".to_string(),
        "-Ztrust-verify-session=hostile-shadow-regression".to_string(),
        format!("-Ztrust-proof-artifact-root={}", proof_root.display()),
    ]
    .join("\x1f");

    p.process(&targo)
        .arg("check")
        .verified_targo_environment()
        .env("TRUST_TARGO_LANE_RUSTFLAGS", rustflags)
        .env_remove("RUSTC")
        .env_remove("CARGO_BUILD_RUSTC")
        .env("REAL_RUSTC", "rustc")
        .env("TRUST_RUSTC_ARG_CAPTURE", capture)
        .env_remove("RUSTC_WRAPPER")
        .with_status(101)
        .with_stderr_contains("[..]hostile-shadow[..]trust[..]")
        .with_stderr_contains("[..]no-proc-macro TCB boundary[..]")
        .run();
}

#[cargo_test]
fn verified_targo_rebuilds_and_rechecks_audited_trust_spec_proc_macro() {
    let compiler = verified_targo_tool_proxy("verified-targo-audited-spec-rustc-proxy");
    let p = project()
        .at("verified-targo-audited-spec-rebuild")
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "selected"
                version = "0.1.0"
                edition = "2024"

                [dependencies]
                trust = { package = "trust-spec", path = "trust-spec" }

                [workspace]
                members = ["trust-spec"]
                resolver = "3"

                [workspace.package]
                # The REAL crates/trust-spec/Cargo.toml is included below, and
                # it inherits `version`, `edition`, `license`, `authors` and
                # `lints` from its workspace (`version.workspace = true` since
                # c9a8f1f481; `[lints] workspace = true` since 1b3cd53a15), so
                # this fixture workspace must define each of them or the audited
                # manifest cannot even load.
                version = "0.10.0"
                edition = "2024"
                license = "Apache-2.0"
                authors = ["Trust audit"]

                [workspace.lints.rust]
                warnings = "warn"
            "#,
        )
        .file(
            "src/lib.rs",
            "#[trust::requires(true)]\npub fn selected() {}\n",
        )
        .file("trust-spec/Cargo.toml", AUDITED_TRUST_SPEC_MANIFEST)
        .file("trust-spec/src/lib.rs", AUDITED_TRUST_SPEC_LIB)
        .build();

    let targo = install_verified_targo_with_trustc_proxy(
        &p,
        &compiler,
        "verified-targo-audited-spec-rustc-proxy",
    );
    let capture = p.root().join("rustc-args.log");
    let real_rustc = "rustc";
    let proof_root = p.root().join("private-proof-artifacts");
    fs::create_dir_all(&proof_root).unwrap();
    let rustflags = |session: &str, include_dependencies: bool| {
        [
            format!("-Ztrust-verify-include-dependencies={include_dependencies}"),
            "-Coverflow-checks=yes".to_string(),
            "-Cdebug-assertions=yes".to_string(),
            format!("-Ztrust-verify-session={session}"),
            format!("-Ztrust-proof-artifact-root={}", proof_root.display()),
        ]
        .join("\x1f")
    };
    let run = |session: &str, include_dependencies: bool| {
        p.process(&targo)
            .arg("check")
            .verified_targo_environment()
            .env(
                "TRUST_TARGO_LANE_RUSTFLAGS",
                rustflags(session, include_dependencies),
            )
            .env_remove("RUSTC")
            .env_remove("CARGO_BUILD_RUSTC")
            .env("REAL_RUSTC", &real_rustc)
            .env_remove("RUSTC_WRAPPER")
            .env("TRUST_RUSTC_ARG_CAPTURE", &capture)
            .run();
    };
    let spec_invocations = || {
        fs::read_to_string(&capture)
            .unwrap_or_default()
            .lines()
            .filter(|line| {
                line.contains("--crate-name\x1ftrust")
                    && line.contains("--crate-type\x1fproc-macro")
            })
            .map(str::to_owned)
            .collect::<Vec<_>>()
    };

    fs::write(&capture, "").unwrap();
    run("audited-spec-first", false);
    assert_eq!(
        spec_invocations().len(),
        1,
        "the first verified run must compile the audited spec provider"
    );

    fs::write(&capture, "").unwrap();
    run("audited-spec-second", true);
    assert_eq!(
        spec_invocations().len(),
        1,
        "a verified run must rebuild the audited provider instead of reusing an ordinary/stale dylib"
    );

    assert!(
        spec_invocations()
            .iter()
            .all(|line| !line.contains("trust-verify=off")),
        "an audited provider must remain in the full compiler proof frontier"
    );

    fs::write(
        p.root().join("trust-spec/src/lib.rs"),
        format!("{AUDITED_TRUST_SPEC_LIB}\n"),
    )
    .unwrap();
    p.process(&targo)
        .arg("check")
        .verified_targo_environment()
        .env(
            "TRUST_TARGO_LANE_RUSTFLAGS",
            rustflags("audited-spec-mutated", true),
        )
        .env_remove("RUSTC")
        .env_remove("CARGO_BUILD_RUSTC")
        .env("REAL_RUSTC", &real_rustc)
        .env_remove("RUSTC_WRAPPER")
        .env("TRUST_RUSTC_ARG_CAPTURE", &capture)
        .with_status(101)
        .with_stderr_contains("[..]does not match its audited source identity[..]")
        .run();
}

#[cargo_test]
fn verified_targo_session_nonce_reruns_only_the_units_that_verify() {
    // The per-run session nonce and proof-artifact root authenticate the
    // evidence stream; they do not change any compiler output. A unit that
    // Targo scopes out with `-Ztrust-verify=off` emits no evidence at all, so
    // pinning it to the session would rebuild the whole dependency graph on
    // every verified invocation to reprove nothing. The units that do verify
    // must still recompile, because a warm artifact carries no observation
    // that the verifier ran under this session's authority.
    //
    // Freshness alone is not enough: Cargo names a unit's artifacts and its
    // fingerprint directory with its `unit_id`, so a nonce in THAT key leaves
    // the stored fingerprint unfound and compiles a second copy of every
    // dependency, build script included (`trust_unit_id`). Count the files.
    let proxy_name = "verified-targo-session-freshness-proxy";
    let compiler = verified_targo_tool_proxy(proxy_name);
    let p = project()
        .at("verified-targo-session-freshness")
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "selected"
                version = "0.1.0"
                edition = "2024"

                [dependencies]
                helper = { path = "helper" }

                [workspace]
                members = ["helper"]
                resolver = "3"
            "#,
        )
        .file("src/lib.rs", "pub fn selected() { helper::helped() }\n")
        .file(
            "helper/Cargo.toml",
            r#"
                [package]
                name = "helper"
                version = "0.1.0"
                edition = "2024"
            "#,
        )
        .file("helper/build.rs", "fn main() {}\n")
        .file("helper/src/lib.rs", "pub fn helped() {}\n")
        .build();

    let targo = install_verified_targo_with_trustc_proxy(&p, &compiler, proxy_name);
    // Verified build scripts receive the authenticated sibling trustdoc.
    fs::hard_link(
        compiler.bin(proxy_name),
        targo
            .parent()
            .unwrap()
            .join(format!("trustdoc{}", env::consts::EXE_SUFFIX)),
    )
    .unwrap();
    let capture = p.root().join("rustc-args.log");
    let proof_root = p.root().join("private-proof-artifacts");
    fs::create_dir_all(&proof_root).unwrap();
    let rustflags = |session: &str, level: &str, include_dependencies: bool| {
        [
            "-Coverflow-checks=yes".to_string(),
            "-Cdebug-assertions=yes".to_string(),
            format!("-Ztrust-verify-level={level}"),
            format!("-Ztrust-verify-include-dependencies={include_dependencies}"),
            format!("-Ztrust-verify-session={session}"),
            format!(
                "-Ztrust-proof-artifact-root={}/{session}",
                proof_root.display()
            ),
        ]
        .join("\x1f")
    };
    let run = |session: &str, level: &str, include_dependencies: bool| {
        fs::create_dir_all(proof_root.join(session)).unwrap();
        fs::write(&capture, "").unwrap();
        p.process(&targo)
            .arg("check")
            .verified_targo_environment()
            .env(
                "TRUST_TARGO_LANE_RUSTFLAGS",
                rustflags(session, level, include_dependencies),
            )
            .env_remove("RUSTC")
            .env_remove("CARGO_BUILD_RUSTC")
            .env_remove("RUSTDOC")
            .env_remove("CARGO_BUILD_RUSTDOC")
            .env("REAL_RUSTC", "rustc")
            .env("REAL_RUSTDOC", "rustdoc")
            .env_remove("RUSTC_WRAPPER")
            .env("TRUST_RUSTC_ARG_CAPTURE", &capture)
            .env(
                "TRUST_RUSTDOC_ARG_CAPTURE",
                p.root().join("rustdoc-args.log"),
            )
            .run();
    };
    let compiled = |crate_name: &str| {
        fs::read_to_string(&capture)
            .unwrap_or_default()
            .lines()
            .filter(|line| line.contains(&format!("--crate-name\x1f{crate_name}\x1f")))
            .count()
    };
    // Trust: the current build-dir layout stores output and fingerprints under
    // package/unit directories. Count those actual identities, retaining the
    // original cold/warm artifact census instead of forcing the legacy layout.
    let identities = |package: &str, entry: &str| {
        p.glob(format!("target/debug/build/{package}/*/{entry}"))
            .map(|path| {
                let path = path.unwrap();
                assert!(fs::symlink_metadata(&path).unwrap().is_file());
                let role_dir = path.parent().unwrap();
                let unit_dir = role_dir.parent().unwrap();
                assert!(fs::symlink_metadata(role_dir).unwrap().is_dir());
                assert!(fs::symlink_metadata(unit_dir).unwrap().is_dir());
                let unit = unit_dir.file_name().unwrap().to_str().unwrap();
                assert_eq!(unit.len(), 16, "invalid unit identity: {path:?}");
                assert!(
                    unit.bytes()
                        .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
                    "invalid unit identity: {path:?}"
                );
                if path.extension().is_some_and(|ext| ext == "rmeta") {
                    assert_eq!(
                        path.file_name().unwrap().to_str().unwrap(),
                        format!("lib{package}-{unit}.rmeta"),
                        "artifact and unit identities disagree"
                    );
                }
                unit.to_owned()
            })
            .collect::<std::collections::BTreeSet<_>>()
    };

    run("freshness-first", "1", false);
    assert_eq!(
        compiled("helper"),
        1,
        "the first run compiles the dependency"
    );
    assert_eq!(compiled("build_script_build"), 1, "and its build script");
    assert_eq!(compiled("selected"), 1, "the first run compiles the root");

    run("freshness-second", "1", false);
    assert_eq!(
        compiled("helper"),
        0,
        "a scoped-out dependency proves nothing, so a new session must not rebuild it"
    );
    assert_eq!(
        compiled("build_script_build"),
        0,
        "nor its scoped-out build script"
    );
    assert_eq!(
        compiled("selected"),
        1,
        "the verifying root must recompile so its evidence belongs to this session"
    );
    assert_eq!(
        identities("helper", "out/libhelper-*.rmeta").len(),
        1,
        "a scoped-out dependency keeps one identity across sessions"
    );
    let script_compilations = identities("helper", "fingerprint/build-script-build-script-build");
    let script_runs = identities("helper", "fingerprint/run-build-script-build-script-build");
    assert_eq!(script_compilations.len(), 1);
    assert_eq!(script_runs.len(), 1);
    assert!(script_compilations.is_disjoint(&script_runs));
    assert_eq!(
        script_compilations.union(&script_runs).count(),
        2,
        "one build-script compile and one execution directory across sessions"
    );
    assert_eq!(
        identities("selected", "out/libselected-*.rmeta").len(),
        2,
        "each session's verified artifact keeps an identity of its own"
    );

    // Everything that is not a per-run nonce still decides freshness: a changed
    // verification policy has to reach the whole graph, or a scoped-out
    // dependency could be reused across incompatible verifier configurations.
    run("freshness-third", "2", false);
    assert_eq!(
        compiled("helper"),
        1,
        "a changed verification level must still invalidate the dependency"
    );
    assert_eq!(compiled("selected"), 1);
    assert_eq!(
        identities("helper", "out/libhelper-*.rmeta").len(),
        2,
        "a changed policy is a new identity, not an overwrite"
    );

    // An included dependency verifies, so it keeps its session: every session
    // rebuilds it and its build script.
    for session in ["included-first", "included-second"] {
        run(session, "2", true);
        assert_eq!(compiled("helper"), 1, "{session}: included dependency");
        assert_eq!(
            compiled("build_script_build"),
            1,
            "{session}: included build script"
        );
        assert_eq!(compiled("selected"), 1, "{session}: root");
    }
}

/// The compiler proxy for
/// `verified_targo_build_script_probe_sees_the_canonical_off_switch`.
///
/// A build script's compiler probe is the one compilation in a verified run
/// that Cargo does not drive: the script runs `$RUSTC` (trustc) itself, with
/// `CARGO_ENCODED_RUSTFLAGS`. For that compile (crate `probe`) this proxy
/// models trustc's bare default: unless the LAST verification switch it
/// receives is off, it verifies, and the strict default refutes the probe's
/// `a / b`. Measured on the installed trustc 321aaeda7 (atpkg pack 9192) with
/// every `TRUST_*` and flag variable removed: `-Zcodegen-backend=llvm
/// -Coverflow-checks=yes -Cdebug-assertions=yes`, the view a verified build
/// script was given, exits 1 (`[divzero] FAILED`, "Trust Level 0 safety
/// verification incomplete for `probe::div`"), and the same flags with
/// `-Z trust-verify=off` appended exit 0. The probe's Trust options are
/// appended, one line per probe compile, to `PROBE_TRUST_OPTION_CAPTURE`: a
/// verified build script never sees a `TRUST_*` variable, so the capture
/// cannot be named like one. Every other compile is Cargo's own and goes to
/// `REAL_RUSTC`/`REAL_RUSTDOC` with its Trust options removed, as
/// `verified_targo_tool_proxy` does.
fn verified_targo_probe_refuting_proxy(name: &str) -> cargo_test_support::Project {
    let compiler = project()
        .at(name)
        .file("Cargo.toml", &basic_manifest(name, "1.0.0"))
        .file(
            "src/main.rs",
            r#"
                use std::ffi::{OsStr, OsString};
                use std::fs::OpenOptions;
                use std::io::Write;
                use std::process::Command;

                /// rustc's reading of a `-Z` option: the key with `-` and `_`
                /// equivalent, and the value after the first `=`.
                fn key_value(option: &str) -> (String, Option<&str>) {
                    let (key, value) = option
                        .split_once('=')
                        .map_or((option, None), |(key, value)| (key, Some(value)));
                    (key.replace('-', "_"), value)
                }

                fn main() {
                    let args = std::env::args_os().skip(1).collect::<Vec<OsString>>();
                    let mut trust_options = Vec::new();
                    let mut forwarded = Vec::new();
                    let mut index = 0;
                    while index < args.len() {
                        let (option, width) = match args[index].to_str() {
                            Some("-Z") => (args.get(index + 1).and_then(|arg| arg.to_str()), 2),
                            Some(arg) => (arg.strip_prefix("-Z").filter(|o| !o.is_empty()), 1),
                            None => (None, 1),
                        };
                        let end = (index + width).min(args.len());
                        match option {
                            Some(option) if key_value(option).0.starts_with("trust_") => {
                                trust_options.push(option.to_string());
                            }
                            _ => forwarded.extend(args[index..end].iter().cloned()),
                        }
                        index = end;
                    }

                    let is_probe = args
                        .windows(2)
                        .any(|pair| pair[0] == "--crate-name" && pair[1] == "probe");
                    if is_probe {
                        if let Some(capture) = std::env::var_os("PROBE_TRUST_OPTION_CAPTURE") {
                            let mut output = OpenOptions::new()
                                .create(true)
                                .append(true)
                                .open(capture)
                                .unwrap();
                            writeln!(output, "{}", trust_options.join("\x1f")).unwrap();
                        }
                        let verification_off = trust_options
                            .iter()
                            .rev()
                            .map(|option| key_value(option))
                            .find(|(key, _)| key == "trust_verify")
                            .is_some_and(|(_, value)| {
                                matches!(value, Some("n" | "no" | "off" | "false"))
                            });
                        if !verification_off {
                            eprintln!(
                                "error: Trust Level 0 safety verification incomplete for \
                                 `probe::div`: 1 obligation(s) were not proved \
                                 (modeled trustc default: verification on)"
                            );
                            std::process::exit(1);
                        }
                    }

                    let current = std::env::current_exe().unwrap();
                    let stem = current.file_stem().and_then(OsStr::to_str).unwrap();
                    let is_rustdoc = stem.contains("rustdoc") || stem.contains("trustdoc");
                    let real = std::env::var_os(if is_rustdoc {
                        "REAL_RUSTDOC"
                    } else {
                        "REAL_RUSTC"
                    })
                    .unwrap();
                    let mut command = Command::new(real);
                    command.args(forwarded)
                        // This proxy has deliberately stripped Targo's verified
                        // protocol. Do not let the downstream Cargo-test shim
                        // mistake the demoted compile for an authenticated edge.
                        .env_remove("TRUST_TARGO_FRONTEND");
                    // Trust: forward the inherited compiler handoff by replacing
                    // this transparent proxy, rather than spawning a new child.
                    #[cfg(unix)] {
                        use std::os::unix::process::CommandExt;
                        panic!("failed to exec compiler: {}", command.exec());
                    }
                    #[cfg(not(unix))] {
                        std::process::exit(command.status().unwrap().code().unwrap_or(1));
                    }
                }
            "#,
        )
        .build();
    compiler.cargo("build").run();
    compiler
}

/// B5 step A. A build script that probes the compiler (anyhow, thiserror,
/// proc-macro2 and rustix directly, num-traits through autocfg) compiles a
/// probe with `$RUSTC` plus `CARGO_ENCODED_RUSTFLAGS` and emits a cfg when it
/// compiles. The verified lanes withheld every Trust control from that
/// variable, the off-switch included, so the probe compiled under trustc's
/// verifying default, the strict default refuted it, and the cfg went missing
/// with no error: a verified build compiled other code than `targo
/// --unverified` (whose build scripts see `-Ztrust-verify=off`). The runtime
/// view now ends in Targo's one canonical off-switch, so the probe compiles
/// as it does unverified. The probe body is `a / b`, which the strict default
/// REFUTES; a body it proves would pass with or without the fix. The library
/// refuses to compile without the probe's cfg, so the build itself is the
/// assertion, and the capture pins what the probe saw.
#[cargo_test]
fn verified_targo_build_script_probe_sees_the_canonical_off_switch() {
    let proxy_name = "verified-targo-probe-refuting-proxy";
    let compiler = verified_targo_probe_refuting_proxy(proxy_name);
    let p = project()
        .at("verified-targo-build-script-probe")
        .file(
            "Cargo.toml",
            &format!(
                r#"
                [package]
                name = "probed"
                version = "0.1.0"
                edition = "2024"

                [build-dependencies]
                jobserver_utils = {{ path = {:?} }}
                "#,
                std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../jobserver_utils")
            ),
        )
        .file(
            "build.rs",
            r#"
                use std::process::Command;

                fn main() {
                    // Trust: capture before opening the probe file and retain the same
                    // scheduler while this nontransparent build script waits for rustc.
                    let jobserver = unsafe { jobserver_utils::InheritedJobserver::from_env() }
                        .expect("inherit build-script jobserver");
                    println!("cargo::rustc-check-cfg=cfg(probe_ok)");
                    let out_dir = std::env::var_os("OUT_DIR").unwrap();
                    let probe = std::path::Path::new(&out_dir).join("probe.rs");
                    std::fs::write(&probe, "pub fn div(a: u32, b: u32) -> u32 { a / b }\n")
                        .unwrap();
                    let mut cmd = Command::new(std::env::var_os("RUSTC").unwrap());
                    cmd.args(["--crate-type=lib", "--emit=metadata", "--crate-name", "probe"])
                        .arg("--out-dir")
                        .arg(&out_dir)
                        .arg(&probe);
                    if let Ok(rustflags) = std::env::var("CARGO_ENCODED_RUSTFLAGS") {
                        cmd.args(rustflags.split('\x1f').filter(|flag| !flag.is_empty()));
                    }
                    jobserver.configure(&mut cmd);
                    if cmd.status().unwrap().success() {
                        println!("cargo::rustc-cfg=probe_ok");
                    }
                }
            "#,
        )
        .file(
            "src/lib.rs",
            r#"
                #[cfg(not(probe_ok))]
                compile_error!("the build script's compiler probe failed in the verified lane");

                pub fn probed() -> u32 {
                    1
                }
            "#,
        )
        .build();

    let targo = install_verified_targo_with_trustc_proxy(&p, &compiler, proxy_name);
    // Verified build scripts receive the authenticated sibling trustdoc.
    fs::hard_link(
        compiler.bin(proxy_name),
        targo
            .parent()
            .unwrap()
            .join(format!("trustdoc{}", env::consts::EXE_SUFFIX)),
    )
    .unwrap();
    let proof_root = p.root().join("private-proof-artifacts/probe-session");
    fs::create_dir_all(&proof_root).unwrap();
    let probe_capture = p.root().join("probe-trust-options.log");
    let rustflags = [
        "-Coverflow-checks=yes".to_string(),
        "-Cdebug-assertions=yes".to_string(),
        "-Ztrust-verify-level=1".to_string(),
        "-Ztrust-verify-include-dependencies=false".to_string(),
        "-Ztrust-verify-session=build-script-probe-session".to_string(),
        format!("-Ztrust-proof-artifact-root={}", proof_root.display()),
    ]
    .join("\x1f");

    p.process(&targo)
        .arg("check")
        .verified_targo_environment()
        .env("TRUST_TARGO_LANE_RUSTFLAGS", rustflags)
        .env_remove("RUSTC")
        .env_remove("CARGO_BUILD_RUSTC")
        .env_remove("RUSTDOC")
        .env_remove("CARGO_BUILD_RUSTDOC")
        .env("REAL_RUSTC", "rustc")
        .env("REAL_RUSTDOC", "rustdoc")
        .env_remove("RUSTC_WRAPPER")
        .env("PROBE_TRUST_OPTION_CAPTURE", &probe_capture)
        .run();

    let probes = fs::read_to_string(&probe_capture).unwrap();
    assert_eq!(
        probes.lines().collect::<Vec<_>>(),
        ["trust-verify=off"],
        "one probe compile, and its only Trust option is the canonical off-switch: never the \
         session, the proof root or the unit's own switch"
    );
}

#[cargo_test]
fn verified_targo_rejects_retired_valtree_limit_from_all_compiler_argument_sources() {
    // Target-info probes run before Targo assembles a compilation unit. Use a
    // direct compiler proxy that removes Trust-only options before invoking
    // the testsuite's stock rustc, while leaving Targo's final-argv policy as
    // the rejection authority under test. Verified Targo rejects wrappers.
    let compiler = project()
        .at("retired-valtree-rustc-proxy")
        .file(
            "Cargo.toml",
            &basic_manifest("retired-valtree-rustc-proxy", "1.0.0"),
        )
        .file(
            "src/main.rs",
            r#"
                use std::ffi::{OsStr, OsString};
                use std::process::Command;

                fn is_test_only_option(option: &OsStr) -> bool {
                    let Some(option) = option.to_str() else { return false };
                    let name = option
                        .split_once('=')
                        .map_or(option, |(name, _)| name)
                        .replace('-', "_");
                    name == "valtree_node_limit" || name.starts_with("trust_")
                }

                fn main() {
                    let mut process_args = std::env::args_os();
                    let _proxy = process_args.next().unwrap();
                    let args = process_args.collect::<Vec<_>>();
                    let rustc = std::env::var_os("REAL_RUSTC").unwrap();
                    let mut forwarded: Vec<OsString> = Vec::with_capacity(args.len());
                    let mut index = 0;
                    while index < args.len() {
                        if args[index] == "-Z"
                            && args.get(index + 1).is_some_and(|arg| is_test_only_option(arg))
                        {
                            index += 2;
                            continue;
                        }
                        if args[index]
                            .to_str()
                            .and_then(|arg| arg.strip_prefix("-Z"))
                            .is_some_and(|option| {
                                !option.is_empty() && is_test_only_option(OsStr::new(option))
                            })
                        {
                            index += 1;
                            continue;
                        }
                        forwarded.push(args[index].clone());
                        index += 1;
                    }
                    let mut command = Command::new(rustc);
                    command.args(forwarded).env_remove("TRUST_TARGO_FRONTEND");
                    // Trust: preserve the existing scheduling handoff.
                    #[cfg(unix)] {
                        use std::os::unix::process::CommandExt;
                        panic!("failed to exec compiler: {}", command.exec());
                    }
                    #[cfg(not(unix))] {
                        std::process::exit(command.status().unwrap().code().unwrap_or(1));
                    }
                }
            "#,
        )
        .build();
    compiler.cargo("build").run();

    // The package deliberately forges the historical first-party name while
    // also being the selected workspace root and primary package. None of
    // those caller-controlled identities authorize the retired resource-cap
    // escape hatch.
    let p = project()
        .at("retired-valtree-all-sources")
        .file(
            "Cargo.toml",
            r#"
                [workspace]

                [package]
                name = "trust-ir"
                version = "0.2.0"
                edition = "2024"
            "#,
        )
        .file("src/lib.rs", "pub fn selected_primary() {}")
        .file(".cargo/config.toml", "")
        .build();
    let targo =
        install_verified_targo_with_trustc_proxy(&p, &compiler, "retired-valtree-rustc-proxy");
    // Resolve through cargo-test-support's isolated PATH. Under `x test`, the
    // ambient RUSTC is bootstrap's internal shim and cannot be relaunched by a
    // fixture after the harness intentionally removes RUSTC_STAGE and related
    // bootstrap authority from child environments.
    let real_rustc = "rustc";
    let proof_root = p.root().join("private-proof-artifacts");
    fs::create_dir_all(&proof_root).unwrap();
    let proof_root_flag = format!("-Ztrust-proof-artifact-root={}", proof_root.display());
    // T14a: the session and proof root travel in the lane; each source below
    // carries only the retired option.
    let lane = format!("-Ztrust-verify-session=valtree-all-sources\x1f{proof_root_flag}");
    let configure = |command: &mut cargo_test_support::Execs| {
        command
            .verified_targo_environment()
            .env("TRUST_TARGO_LANE_RUSTFLAGS", &lane)
            .env_remove("RUSTC")
            .env_remove("CARGO_BUILD_RUSTC")
            .env("REAL_RUSTC", &real_rustc)
            .env_remove("RUSTC_WRAPPER")
            .with_status(101)
            .with_stderr_contains("[..]retired `-Zvaltree-node-limit`[..]")
            .with_stderr_contains("[..]fixed valtree resource limit[..]");
    };

    let mut plain = p.process(&targo);
    plain
        .arg("check")
        .env("RUSTFLAGS", "-Z valtree_node-limit=200000")
        .env_remove("CARGO_ENCODED_RUSTFLAGS");
    configure(&mut plain);
    plain.run();

    let mut encoded = p.process(&targo);
    encoded
        .arg("check")
        .env_remove("RUSTFLAGS")
        .env("CARGO_ENCODED_RUSTFLAGS", "-Zvaltree_node_limit=200000");
    configure(&mut encoded);
    encoded.run();

    p.change_file(
        ".cargo/config.toml",
        r#"
            [build]
            rustflags = [
                "-Z",
                "valtree_node-limit=200000",
            ]
        "#,
    );
    let mut config = p.process(&targo);
    config
        .arg("check")
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS");
    configure(&mut config);
    config.run();

    p.change_file(".cargo/config.toml", "");
    p.change_file(
        "Cargo.toml",
        r#"
            cargo-features = ["profile-rustflags"]

            [workspace]

            [package]
            name = "trust-ir"
            version = "0.2.0"
            edition = "2024"

            [profile.dev.package."trust-ir"]
            rustflags = ["-Zvaltree_node_limit=200000"]
        "#,
    );
    let mut profile = p.process(&targo);
    profile
        .arg("check")
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .masquerade_as_nightly_cargo(&["profile-rustflags"]);
    configure(&mut profile);
    profile.run();

    p.change_file(
        "Cargo.toml",
        r#"
            [workspace]

            [package]
            name = "trust-ir"
            version = "0.2.0"
            edition = "2024"
        "#,
    );
    let mut extra = p.process(&targo);
    extra
        .args(&["rustc", "--lib", "--", "-Z", "valtree_node-limit=200000"])
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS");
    configure(&mut extra);
    extra.run();

    p.change_file(
        "Cargo.toml",
        r#"
            cargo-features = ["profile-rustflags"]

            [workspace]

            [package]
            name = "trust-ir"
            version = "0.2.0"
            edition = "2024"

            [profile.dev.package."trust-ir"]
            rustflags = ["--codegen=overflow_checks=no"]
        "#,
    );
    let mut profile_authority = p.process(&targo);
    profile_authority
        .arg("check")
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .verified_targo_environment()
        .env(
            "TRUST_TARGO_LANE_RUSTFLAGS",
            format!(
                "-Ztrust-verify-session=profile-authority\x1f{proof_root_flag}\x1f-Coverflow-checks=yes\x1f-Cdebug-assertions=yes"
            ),
        )
        .env_remove("RUSTC")
        .env_remove("CARGO_BUILD_RUSTC")
        .env("REAL_RUSTC", &real_rustc)
        .env_remove("RUSTC_WRAPPER")
        .masquerade_as_nightly_cargo(&["profile-rustflags"])
        .with_status(101)
        .with_stderr_contains(
            "[..]profile rustflags cannot override authenticated `-Coverflow_checks`[..]",
        );
    profile_authority.run();

    p.change_file(
        "Cargo.toml",
        r#"
            [workspace]

            [package]
            name = "trust-ir"
            version = "0.2.0"
            edition = "2024"
        "#,
    );
    let mut extra_authority = p.process(&targo);
    extra_authority
        .args(&["rustc", "--lib", "--", "--codegen", "overflow_checks=no"])
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .verified_targo_environment()
        .env(
            "TRUST_TARGO_LANE_RUSTFLAGS",
            format!(
                "-Ztrust-verify-session=extra-authority\x1f{proof_root_flag}\x1f-Coverflow-checks=yes\x1f-Cdebug-assertions=yes"
            ),
        )
        .env_remove("RUSTC")
        .env_remove("CARGO_BUILD_RUSTC")
        .env("REAL_RUSTC", &real_rustc)
        .env_remove("RUSTC_WRAPPER")
        .with_status(101)
        .with_stderr_contains(
            "[..]cargo rustc extra compiler arguments cannot override authenticated `-Coverflow_checks`[..]",
        );
    extra_authority.run();
}

#[cargo_test]
fn env_rustflags_build_script_dep_with_target() {
    // RUSTFLAGS should not be passed to rustc for build scripts
    // when --target is specified.
    // In this test if --cfg foo is passed the build will fail.
    let foo = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                build = "build.rs"

                [build-dependencies.bar]
                path = "../bar"
            "#,
        )
        .file("src/lib.rs", "")
        .file("build.rs", "fn main() {}")
        .build();
    let _bar = project()
        .at("bar")
        .file("Cargo.toml", &basic_manifest("bar", "0.0.1"))
        .file(
            "src/lib.rs",
            r#"
                fn bar() { }
                #[cfg(foo)]
                fn bar() { }
            "#,
        )
        .build();

    let host = rustc_host();
    foo.cargo("check --target")
        .arg(host)
        .env("RUSTFLAGS", "--cfg foo")
        .run();
}

#[cargo_test]
fn env_rustflags_recompile() {
    let p = project().file("src/lib.rs", "").build();

    p.cargo("check").run();
    // Setting RUSTFLAGS forces a recompile
    p.cargo("check")
        .env("RUSTFLAGS", "-Z bogus")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
}

#[cargo_test]
fn env_rustflags_recompile2() {
    let p = project().file("src/lib.rs", "").build();

    p.cargo("check").env("RUSTFLAGS", "--cfg foo").run();
    // Setting RUSTFLAGS forces a recompile
    p.cargo("check")
        .env("RUSTFLAGS", "-Z bogus")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
}

#[cargo_test]
fn env_rustflags_no_recompile() {
    let p = project().file("src/lib.rs", "").build();

    p.cargo("check").env("RUSTFLAGS", "--cfg foo").run();
    p.cargo("check")
        .env("RUSTFLAGS", "--cfg foo")
        .with_stderr_data(str![[r#"
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test]
fn build_rustflags_normal_source() {
    let p = project()
        .file("src/lib.rs", "")
        .file("src/bin/a.rs", "fn main() {}")
        .file("examples/b.rs", "fn main() {}")
        .file("tests/c.rs", "#[test] fn f() { }")
        .file(
            "benches/d.rs",
            r#"
            #![feature(test)]
            extern crate test;
            #[bench] fn run1(_ben: &mut test::Bencher) { }
            "#,
        )
        .file(
            ".cargo/config.toml",
            r#"
            [build]
            rustflags = ["-Z", "bogus"]
            "#,
        )
        .build();

    p.cargo("check --lib")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
    p.cargo("check --bin=a")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
    p.cargo("check --example=b")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
    p.cargo("test")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
    p.cargo("bench")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
}

#[cargo_test]
fn build_rustflags_build_script() {
    // RUSTFLAGS should be passed to rustc for build scripts
    // when --target is not specified.
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                build = "build.rs"
            "#,
        )
        .file("src/lib.rs", "")
        .file(
            "build.rs",
            r#"
                fn main() { assert!(cfg!(foo)); }
            "#,
        )
        .file(
            ".cargo/config.toml",
            r#"
            [build]
            rustflags = ["--cfg", "foo"]
            "#,
        )
        .build();

    p.cargo("check").run();
}

#[cargo_test]
fn build_rustflags_build_script_dep() {
    // RUSTFLAGS should be passed to rustc for build scripts
    // when --target is not specified.
    // In this test if --cfg foo is not passed the build will fail.
    let foo = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                build = "build.rs"

                [build-dependencies.bar]
                path = "../bar"
            "#,
        )
        .file("src/lib.rs", "")
        .file("build.rs", "fn main() {}")
        .file(
            ".cargo/config.toml",
            r#"
            [build]
            rustflags = ["--cfg", "foo"]
            "#,
        )
        .build();
    let _bar = project()
        .at("bar")
        .file("Cargo.toml", &basic_manifest("bar", "0.0.1"))
        .file(
            "src/lib.rs",
            r#"
                fn bar() { }
                #[cfg(not(foo))]
                fn bar() { }
            "#,
        )
        .build();

    foo.cargo("check").run();
}

#[cargo_test]
fn build_rustflags_normal_source_with_target() {
    let p = project()
        .file("src/lib.rs", "")
        .file("src/bin/a.rs", "fn main() {}")
        .file("examples/b.rs", "fn main() {}")
        .file("tests/c.rs", "#[test] fn f() { }")
        .file(
            "benches/d.rs",
            r#"
            #![feature(test)]
            extern crate test;
            #[bench] fn run1(_ben: &mut test::Bencher) { }
            "#,
        )
        .file(
            ".cargo/config.toml",
            r#"
            [build]
            rustflags = ["-Z", "bogus"]
            "#,
        )
        .build();

    let host = &rustc_host();

    // Use build.rustflags to pass an argument that will generate an error
    p.cargo("check --lib --target")
        .arg(host)
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
    p.cargo("check --bin=a --target")
        .arg(host)
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
    p.cargo("check --example=b --target")
        .arg(host)
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
    p.cargo("test --target")
        .arg(host)
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
    p.cargo("bench --target")
        .arg(host)
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
}

#[cargo_test]
fn build_rustflags_build_script_with_target() {
    // RUSTFLAGS should not be passed to rustc for build scripts
    // when --target is specified.
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                build = "build.rs"
            "#,
        )
        .file("src/lib.rs", "")
        .file(
            "build.rs",
            r#"
                fn main() { assert!(!cfg!(foo)); }
            "#,
        )
        .file(
            ".cargo/config.toml",
            r#"
            [build]
            rustflags = ["--cfg", "foo"]
            "#,
        )
        .build();

    let host = rustc_host();
    p.cargo("check --target").arg(host).run();
}

#[cargo_test]
fn build_rustflags_build_script_dep_with_target() {
    // RUSTFLAGS should not be passed to rustc for build scripts
    // when --target is specified.
    // In this test if --cfg foo is passed the build will fail.
    let foo = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                build = "build.rs"

                [build-dependencies.bar]
                path = "../bar"
            "#,
        )
        .file("src/lib.rs", "")
        .file("build.rs", "fn main() {}")
        .file(
            ".cargo/config.toml",
            r#"
            [build]
            rustflags = ["--cfg", "foo"]
            "#,
        )
        .build();
    let _bar = project()
        .at("bar")
        .file("Cargo.toml", &basic_manifest("bar", "0.0.1"))
        .file(
            "src/lib.rs",
            r#"
                fn bar() { }
                #[cfg(foo)]
                fn bar() { }
            "#,
        )
        .build();

    let host = rustc_host();
    foo.cargo("check --target").arg(host).run();
}

#[cargo_test]
fn build_rustflags_recompile() {
    let p = project().file("src/lib.rs", "").build();

    p.cargo("check").run();

    // Setting RUSTFLAGS forces a recompile
    let config = r#"
        [build]
        rustflags = ["-Z", "bogus"]
        "#;
    let config_file = paths::root().join("foo/.cargo/config.toml");
    fs::create_dir_all(config_file.parent().unwrap()).unwrap();
    fs::write(config_file, config).unwrap();

    p.cargo("check")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
}

#[cargo_test]
fn build_rustflags_recompile2() {
    let p = project().file("src/lib.rs", "").build();

    p.cargo("check").env("RUSTFLAGS", "--cfg foo").run();

    // Setting RUSTFLAGS forces a recompile
    let config = r#"
        [build]
        rustflags = ["-Z", "bogus"]
        "#;
    let config_file = paths::root().join("foo/.cargo/config.toml");
    fs::create_dir_all(config_file.parent().unwrap()).unwrap();
    fs::write(config_file, config).unwrap();

    p.cargo("check")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
}

#[cargo_test]
fn build_rustflags_no_recompile() {
    let p = project()
        .file("src/lib.rs", "")
        .file(
            ".cargo/config.toml",
            r#"
            [build]
            rustflags = ["--cfg", "foo"]
            "#,
        )
        .build();

    p.cargo("check").env("RUSTFLAGS", "--cfg foo").run();
    p.cargo("check")
        .env("RUSTFLAGS", "--cfg foo")
        .with_stderr_data(str![[r#"
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test]
fn build_rustflags_with_home_config() {
    // We need a config file inside the home directory
    let home = paths::home();
    let home_config = home.join(".cargo");
    fs::create_dir(&home_config).unwrap();
    fs::write(
        &home_config.join("config"),
        r#"
            [build]
            rustflags = ["-Cllvm-args=-x86-asm-syntax=intel"]
        "#,
    )
    .unwrap();

    // And we need the project to be inside the home directory
    // so the walking process finds the home project twice.
    let p = project_in_home("foo").file("src/lib.rs", "").build();

    p.cargo("check -v").run();
}

#[cargo_test]
fn target_rustflags_normal_source() {
    let p = project()
        .file("src/lib.rs", "")
        .file("src/bin/a.rs", "fn main() {}")
        .file("examples/b.rs", "fn main() {}")
        .file("tests/c.rs", "#[test] fn f() { }")
        .file(
            "benches/d.rs",
            r#"
            #![feature(test)]
            extern crate test;
            #[bench] fn run1(_ben: &mut test::Bencher) { }
            "#,
        )
        .file(
            ".cargo/config.toml",
            &format!(
                "
            [target.{}]
            rustflags = [\"-Z\", \"bogus\"]
            ",
                rustc_host()
            ),
        )
        .build();

    p.cargo("check --lib")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
    p.cargo("check --bin=a")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
    p.cargo("check --example=b")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
    p.cargo("test")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
    p.cargo("bench")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
}

#[cargo_test]
fn target_rustflags_also_for_build_scripts() {
    let p = project()
        .file("src/lib.rs", "")
        .file(
            "build.rs",
            r#"
                fn main() { assert!(cfg!(foo)); }
            "#,
        )
        .file(
            ".cargo/config.toml",
            &format!(
                "
            [target.{}]
            rustflags = [\"--cfg=foo\"]
            ",
                rustc_host()
            ),
        )
        .build();

    p.cargo("check").run();
}

#[cargo_test]
fn target_rustflags_not_for_build_scripts_with_target() {
    let host = rustc_host();
    let p = project()
        .file("src/lib.rs", "")
        .file(
            "build.rs",
            r#"
                fn main() { assert!(!cfg!(foo)); }
            "#,
        )
        .file(
            ".cargo/config.toml",
            &format!(
                "
            [target.{}]
            rustflags = [\"--cfg=foo\"]
            ",
                host
            ),
        )
        .build();

    p.cargo("check --target").arg(host).run();

    // Enabling -Ztarget-applies-to-host should not make a difference without the config setting
    p.cargo("check --target")
        .arg(host)
        .masquerade_as_nightly_cargo(&["target-applies-to-host"])
        .arg("-Ztarget-applies-to-host")
        .run();

    // Even with the setting, the rustflags from `target.` should not apply, to match the legacy
    // Cargo behavior.
    p.change_file(
        ".cargo/config.toml",
        &format!(
            "
        target-applies-to-host = true

        [target.{}]
        rustflags = [\"--cfg=foo\"]
        ",
            host
        ),
    );
    p.cargo("check --target")
        .arg(host)
        .masquerade_as_nightly_cargo(&["target-applies-to-host"])
        .arg("-Ztarget-applies-to-host")
        .run();
}

#[cargo_test]
fn build_rustflags_for_build_scripts() {
    let host = rustc_host();
    let p = project()
        .file("src/lib.rs", "")
        .file(
            "build.rs",
            r#"
                fn main() { assert!(cfg!(foo), "CFG FOO!"); }
            "#,
        )
        .file(
            ".cargo/config.toml",
            "
            [build]
            rustflags = [\"--cfg=foo\"]
            ",
        )
        .build();

    // With "legacy" behavior, build.rustflags should apply to build scripts without --target
    p.cargo("check").run();

    // But should _not_ apply _with_ --target
    p.cargo("check --target")
        .arg(host)
        .with_status(101)
        .with_stderr_data("...\n[..]CFG FOO![..]\n...")
        .run();

    // Enabling -Ztarget-applies-to-host should not make a difference without the config setting
    p.cargo("check")
        .masquerade_as_nightly_cargo(&["target-applies-to-host"])
        .arg("-Ztarget-applies-to-host")
        .run();
    p.cargo("check --target")
        .arg(host)
        .masquerade_as_nightly_cargo(&["target-applies-to-host"])
        .arg("-Ztarget-applies-to-host")
        .with_status(101)
        .with_stderr_data("...\n[..]CFG FOO![..]\n...")
        .run();

    // When set to false though, the "proper" behavior where host artifacts _only_ pick up on
    // [host] should be applied.
    p.change_file(
        ".cargo/config.toml",
        "
        target-applies-to-host = false

        [build]
        rustflags = [\"--cfg=foo\"]
        ",
    );
    p.cargo("check")
        .masquerade_as_nightly_cargo(&["target-applies-to-host"])
        .arg("-Ztarget-applies-to-host")
        .with_status(101)
        .with_stderr_data("...\n[..]CFG FOO![..]\n...")
        .run();
    p.cargo("check --target")
        .arg(host)
        .masquerade_as_nightly_cargo(&["target-applies-to-host"])
        .arg("-Ztarget-applies-to-host")
        .with_status(101)
        .with_stderr_data("...\n[..]CFG FOO![..]\n...")
        .run();
}

#[cargo_test]
fn host_rustflags_for_build_scripts() {
    let host = rustc_host();
    let p = project()
        .file("src/lib.rs", "")
        .file(
            "build.rs",
            r#"
                // Ensure that --cfg=foo is passed.
                fn main() { assert!(cfg!(foo)); }
            "#,
        )
        .file(
            ".cargo/config.toml",
            &format!(
                "
                target-applies-to-host = false

                [host.{}]
                rustflags = [\"--cfg=foo\"]
                ",
                host
            ),
        )
        .build();

    p.cargo("check --target")
        .arg(host)
        .masquerade_as_nightly_cargo(&["target-applies-to-host", "host-config"])
        .arg("-Ztarget-applies-to-host")
        .arg("-Zhost-config")
        .run();
}

// target.{}.rustflags takes precedence over build.rustflags
#[cargo_test]
fn target_rustflags_precedence() {
    let p = project()
        .file("src/lib.rs", "")
        .file("src/bin/a.rs", "fn main() {}")
        .file("examples/b.rs", "fn main() {}")
        .file("tests/c.rs", "#[test] fn f() { }")
        .file(
            ".cargo/config.toml",
            &format!(
                "
            [build]
            rustflags = [\"--cfg\", \"foo\"]

            [target.{}]
            rustflags = [\"-Z\", \"bogus\"]
            ",
                rustc_host()
            ),
        )
        .build();

    p.cargo("check --lib")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
    p.cargo("check --bin=a")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
    p.cargo("check --example=b")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
    p.cargo("test")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
    p.cargo("bench")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] failed to run `rustc` to learn about target-specific information

Caused by:
  [..]bogus[..]
...
"#]])
        .run();
}

#[cargo_test]
fn cfg_rustflags_normal_source() {
    let p = project()
        .file("src/lib.rs", "pub fn t() {}")
        .file("src/bin/a.rs", "fn main() {}")
        .file("examples/b.rs", "fn main() {}")
        .file("tests/c.rs", "#[test] fn f() { }")
        .file(
            ".cargo/config.toml",
            &format!(
                r#"
                [target.'cfg({})']
                rustflags = ["--cfg", "bar"]
                "#,
                if rustc_host().contains("-windows-") {
                    "windows"
                } else {
                    "not(windows)"
                }
            ),
        )
        .build();

    p.cargo("build --lib -v")
        .with_stderr_data(str![[r#"
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustc --crate-name foo [..] --cfg bar[..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();

    p.cargo("build --bin=a -v")
        .with_stderr_data(str![[r#"
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustc --crate-name a [..] --cfg bar[..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();

    p.cargo("build --example=b -v")
        .with_stderr_data(str![[r#"
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustc --crate-name b [..] --cfg bar[..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();

    p.cargo("test --no-run -v")
        .with_stderr_data(str![[r#"
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustc [..] --cfg bar[..]`
[RUNNING] `rustc [..] --cfg bar[..]`
[RUNNING] `rustc [..] --cfg bar[..]`
[FINISHED] `test` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s
[EXECUTABLE] `[ROOT]/foo/target/debug/build/foo/[HASH]/out/foo-[HASH][EXE]`
[EXECUTABLE] `[ROOT]/foo/target/debug/build/foo/[HASH]/out/a-[HASH][EXE]`
[EXECUTABLE] `[ROOT]/foo/target/debug/build/foo/[HASH]/out/c-[HASH][EXE]`

"#]])
        .run();

    p.cargo("bench --no-run -v")
        .with_stderr_data(str![[r#"
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustc [..] --cfg bar[..]`
[RUNNING] `rustc [..] --cfg bar[..]`
[RUNNING] `rustc [..] --cfg bar[..]`
[FINISHED] `bench` profile [optimized] target(s) in [ELAPSED]s
[EXECUTABLE] `[ROOT]/foo/target/release/build/foo/[HASH]/out/foo-[HASH][EXE]`
[EXECUTABLE] `[ROOT]/foo/target/release/build/foo/[HASH]/out/a-[HASH][EXE]`

"#]])
        .run();
}

// target.'cfg(...)'.rustflags takes precedence over build.rustflags
#[cargo_test]
fn cfg_rustflags_precedence() {
    let p = project()
        .file("src/lib.rs", "pub fn t() {}")
        .file("src/bin/a.rs", "fn main() {}")
        .file("examples/b.rs", "fn main() {}")
        .file("tests/c.rs", "#[test] fn f() { }")
        .file(
            ".cargo/config.toml",
            &format!(
                r#"
                [build]
                rustflags = ["--cfg", "foo"]

                [target.'cfg({})']
                rustflags = ["--cfg", "bar"]
                "#,
                if rustc_host().contains("-windows-") {
                    "windows"
                } else {
                    "not(windows)"
                }
            ),
        )
        .build();

    p.cargo("build --lib -v")
        .with_stderr_data(str![[r#"
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustc --crate-name foo [..] --cfg bar[..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();

    p.cargo("build --bin=a -v")
        .with_stderr_data(str![[r#"
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustc --crate-name a [..] --cfg bar[..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();

    p.cargo("build --example=b -v")
        .with_stderr_data(str![[r#"
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustc --crate-name b [..] --cfg bar[..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();

    p.cargo("test --no-run -v")
        .with_stderr_data(str![[r#"
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustc [..] --cfg bar[..]`
[RUNNING] `rustc [..] --cfg bar[..]`
[RUNNING] `rustc [..] --cfg bar[..]`
[FINISHED] `test` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s
[EXECUTABLE] `[ROOT]/foo/target/debug/build/foo/[HASH]/out/foo-[HASH][EXE]`
[EXECUTABLE] `[ROOT]/foo/target/debug/build/foo/[HASH]/out/a-[HASH][EXE]`
[EXECUTABLE] `[ROOT]/foo/target/debug/build/foo/[HASH]/out/c-[HASH][EXE]`

"#]])
        .run();

    p.cargo("bench --no-run -v")
        .with_stderr_data(str![[r#"
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustc [..] --cfg bar[..]`
[RUNNING] `rustc [..] --cfg bar[..]`
[RUNNING] `rustc [..] --cfg bar[..]`
[FINISHED] `bench` profile [optimized] target(s) in [ELAPSED]s
[EXECUTABLE] `[ROOT]/foo/target/release/build/foo/[HASH]/out/foo-[HASH][EXE]`
[EXECUTABLE] `[ROOT]/foo/target/release/build/foo/[HASH]/out/a-[HASH][EXE]`

"#]])
        .run();
}

#[cargo_test]
fn target_rustflags_string_and_array_form1() {
    let p1 = project()
        .file("src/lib.rs", "")
        .file(
            ".cargo/config.toml",
            r#"
            [build]
            rustflags = ["--cfg", "foo"]
            "#,
        )
        .build();

    p1.cargo("check -v")
        .with_stderr_data(str![[r#"
[CHECKING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustc --crate-name foo [..] --cfg foo[..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();

    let p2 = project()
        .file("src/lib.rs", "")
        .file(
            ".cargo/config.toml",
            r#"
            [build]
            rustflags = "--cfg foo"
            "#,
        )
        .build();

    p2.cargo("check -v")
        .with_stderr_data(str![[r#"
[CHECKING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustc --crate-name foo [..] --cfg foo[..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test]
fn target_rustflags_string_and_array_form2() {
    let p1 = project()
        .file(
            ".cargo/config.toml",
            &format!(
                r#"
                    [target.{}]
                    rustflags = ["--cfg", "foo"]
                "#,
                rustc_host()
            ),
        )
        .file("src/lib.rs", "")
        .build();

    p1.cargo("check -v")
        .with_stderr_data(str![[r#"
[CHECKING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustc --crate-name foo [..] --cfg foo[..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();

    let p2 = project()
        .file(
            ".cargo/config.toml",
            &format!(
                r#"
                    [target.{}]
                    rustflags = "--cfg foo"
                "#,
                rustc_host()
            ),
        )
        .file("src/lib.rs", "")
        .build();

    p2.cargo("check -v")
        .with_stderr_data(str![[r#"
[CHECKING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustc --crate-name foo [..] --cfg foo[..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test]
fn two_matching_in_config() {
    let p1 = project()
        .file(
            ".cargo/config.toml",
            r#"
                [target.'cfg(unix)']
                rustflags = ["--cfg", 'foo="a"']
                [target.'cfg(windows)']
                rustflags = ["--cfg", 'foo="a"']
                [target.'cfg(target_pointer_width = "32")']
                rustflags = ["--cfg", 'foo="b"']
                [target.'cfg(target_pointer_width = "64")']
                rustflags = ["--cfg", 'foo="b"']
            "#,
        )
        .file(
            "src/main.rs",
            r#"
                #![allow(unexpected_cfgs)]
                fn main() {
                    if cfg!(foo = "a") {
                        println!("a");
                    } else if cfg!(foo = "b") {
                        println!("b");
                    } else {
                        panic!()
                    }
                }
            "#,
        )
        .build();

    p1.cargo("run").run();
    p1.cargo("build")
        .with_stderr_data(str![[r#"
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test]
fn env_rustflags_misspelled() {
    let p = project().file("src/main.rs", "fn main() { }").build();

    for cmd in &["check", "build", "run", "test", "bench"] {
        p.cargo(cmd)
            .env("RUST_FLAGS", "foo")
            .with_stderr_data(str![[r#"
[WARNING] ignoring environment variable `RUST_FLAGS`
  |
  = [HELP] rust flags are passed via `RUSTFLAGS`
...
"#]])
            .run();
    }
}

#[cargo_test]
fn env_rustflags_misspelled_build_script() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                edition = "2021"
                build = "build.rs"
            "#,
        )
        .file("src/lib.rs", "")
        .file("build.rs", "fn main() { }")
        .build();

    p.cargo("check")
        .env("RUST_FLAGS", "foo")
        .with_stderr_data(str![[r#"
[WARNING] ignoring environment variable `RUST_FLAGS`
  |
  = [HELP] rust flags are passed via `RUSTFLAGS`
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test]
fn remap_path_prefix_works() {
    // Check that remap-path-prefix works.
    Package::new("bar", "0.1.0")
        .file("src/lib.rs", "pub fn f() -> &'static str { file!() }")
        .publish();

    let p = project()
        .file(
            "Cargo.toml",
            r#"
            [package]
            name = "foo"
            version = "0.1.0"

            [dependencies]
            bar = "0.1"
            "#,
        )
        .file(
            "src/main.rs",
            r#"
            fn main() {
                println!("{}", bar::f());
            }
            "#,
        )
        .build();

    p.cargo("run")
        .env(
            "RUSTFLAGS",
            format!("--remap-path-prefix={}=/foo", paths::root().display()),
        )
        .with_stdout_data(str![[r#"
/foo/home/.cargo/registry/src/-[HASH]/bar-0.1.0/src/lib.rs

"#]])
        .run();
}

#[cargo_test]
fn rustflags_remap_path_prefix_ignored_for_c_metadata() {
    let p = project().file("src/lib.rs", "").build();

    let build_output = p
        .cargo("build -v")
        .env(
            "RUSTFLAGS",
            "--remap-path-prefix=/abc=/zoo --remap-path-prefix /spaced=/zoo",
        )
        .run();
    let first_c_metadata = dbg!(get_c_metadata(build_output));

    p.cargo("clean").run();

    let build_output = p
        .cargo("build -v")
        .env(
            "RUSTFLAGS",
            "--remap-path-prefix=/def=/zoo --remap-path-prefix /earth=/zoo",
        )
        .run();
    let second_c_metadata = dbg!(get_c_metadata(build_output));

    assert_data_eq!(first_c_metadata, second_c_metadata);
}

#[cargo_test]
fn rustc_remap_path_prefix_ignored_for_c_metadata() {
    let p = project().file("src/lib.rs", "").build();

    let build_output = p
        .cargo("rustc -v -- --remap-path-prefix=/abc=/zoo --remap-path-prefix /spaced=/zoo")
        .run();
    let first_c_metadata = dbg!(get_c_metadata(build_output));

    p.cargo("clean").run();

    let build_output = p
        .cargo("rustc -v -- --remap-path-prefix=/def=/zoo --remap-path-prefix /earth=/zoo")
        .run();
    let second_c_metadata = dbg!(get_c_metadata(build_output));

    assert_data_eq!(first_c_metadata, second_c_metadata);
}

// `--remap-path-prefix` is meant to take two different binaries and make them the same but the
// rlib name, including `-Cextra-filename`, can still end up in the binary so it can't change
#[cargo_test]
fn rustflags_remap_path_prefix_ignored_for_c_extra_filename() {
    let p = project().file("src/lib.rs", "").build();

    let build_output = p
        .cargo("build -v")
        .env(
            "RUSTFLAGS",
            "--remap-path-prefix=/abc=/zoo --remap-path-prefix /spaced=/zoo",
        )
        .run();
    let first_c_extra_filename = dbg!(get_c_extra_filename(build_output));

    p.cargo("clean").run();

    let build_output = p
        .cargo("build -v")
        .env(
            "RUSTFLAGS",
            "--remap-path-prefix=/def=/zoo --remap-path-prefix /earth=/zoo",
        )
        .run();
    let second_c_extra_filename = dbg!(get_c_extra_filename(build_output));

    assert_data_eq!(first_c_extra_filename, second_c_extra_filename);
}

// `--remap-path-prefix` is meant to take two different binaries and make them the same but the
// rlib name, including `-Cextra-filename`, can still end up in the binary so it can't change
#[cargo_test]
fn rustc_remap_path_prefix_ignored_for_c_extra_filename() {
    let p = project().file("src/lib.rs", "").build();

    let build_output = p
        .cargo("rustc -v -- --remap-path-prefix=/abc=/zoo --remap-path-prefix /spaced=/zoo")
        .run();
    let first_c_extra_filename = dbg!(get_c_extra_filename(build_output));

    p.cargo("clean").run();

    let build_output = p
        .cargo("rustc -v -- --remap-path-prefix=/def=/zoo --remap-path-prefix /earth=/zoo")
        .run();
    let second_c_extra_filename = dbg!(get_c_extra_filename(build_output));

    assert_data_eq!(first_c_extra_filename, second_c_extra_filename);
}

fn get_c_metadata(output: RawOutput) -> String {
    let get_c_metadata_re =
        regex::Regex::new(r".* (--crate-name [^ ]+).* (-C ?metadata=[^ ]+).*").unwrap();

    let stderr = String::from_utf8(output.stderr).unwrap();
    let mut c_metadata = get_c_metadata_re
        .captures_iter(&stderr)
        .map(|c| {
            let (_, [name, c_metadata]) = c.extract();
            format!("{name} {c_metadata}")
        })
        .collect::<Vec<_>>();
    assert!(
        !c_metadata.is_empty(),
        "`{get_c_metadata_re:?}` did not match:\n```\n{stderr}\n```"
    );
    c_metadata.sort();
    c_metadata.join("\n")
}

fn get_c_extra_filename(output: RawOutput) -> String {
    let get_c_extra_filename_re =
        regex::Regex::new(r".* (--crate-name [^ ]+).* (-C ?extra-filename=[^ ]+).*").unwrap();

    let stderr = String::from_utf8(output.stderr).unwrap();
    let mut c_extra_filename = get_c_extra_filename_re
        .captures_iter(&stderr)
        .map(|c| {
            let (_, [name, c_extra_filename]) = c.extract();
            format!("{name} {c_extra_filename}")
        })
        .collect::<Vec<_>>();
    assert!(
        !c_extra_filename.is_empty(),
        "`{get_c_extra_filename_re:?}` did not match:\n```\n{stderr}\n```"
    );
    c_extra_filename.sort();
    c_extra_filename.join("\n")
}

#[cargo_test]
fn host_config_rustflags_with_target() {
    // regression test for https://github.com/rust-lang/cargo/issues/10206
    let p = project()
        .file("src/lib.rs", "")
        .file("build.rs", "fn main() { assert!(cfg!(foo)); }")
        .file(".cargo/config.toml", "target-applies-to-host = false")
        .build();

    p.cargo("check")
        .masquerade_as_nightly_cargo(&["target-applies-to-host", "host-config"])
        .arg("-Zhost-config")
        .arg("-Ztarget-applies-to-host")
        .arg("-Zunstable-options")
        .arg("--config")
        .arg("host.rustflags=[\"--cfg=foo\"]")
        .run();
}

#[cargo_test]
fn target_applies_to_host_rustflags_works() {
    // Ensures that rustflags are passed to the target when
    // target_applies_to_host=false
    let p = project()
        .file(
            "src/lib.rs",
            r#"#[cfg(feature = "flag")] compile_error!("flag passed");"#,
        )
        .build();

    // Use RUSTFLAGS to pass an argument that will generate an error.
    p.cargo("check")
        .masquerade_as_nightly_cargo(&["target-applies-to-host"])
        .arg("-Ztarget-applies-to-host")
        .env("CARGO_TARGET_APPLIES_TO_HOST", "false")
        .env("RUSTFLAGS", r#"--cfg feature="flag""#)
        .with_status(101)
        .with_stderr_data(
            "[CHECKING] foo v0.0.1 ([ROOT]/foo)
[ERROR] flag passed
...",
        )
        .run();
}

#[cargo_test]
fn target_applies_to_host_rustdocflags_works() {
    // Ensures that rustflags are passed to the target when
    // target_applies_to_host=false
    let p = project()
        .file(
            "src/lib.rs",
            r#"#[cfg(feature = "flag")] compile_error!("flag passed");"#,
        )
        .build();

    // Use RUSTFLAGS to pass an argument that would generate an error
    // but it is ignored.
    p.cargo("doc")
        .masquerade_as_nightly_cargo(&["target-applies-to-host"])
        .arg("-Ztarget-applies-to-host")
        .env("CARGO_TARGET_APPLIES_TO_HOST", "false")
        .env("RUSTDOCFLAGS", r#"--cfg feature="flag""#)
        .with_status(101)
        .with_stderr_data(
            "[DOCUMENTING] foo v0.0.1 ([ROOT]/foo)
[ERROR] flag passed
...",
        )
        .run();
}

#[cargo_test]
fn host_config_shared_build_dep() {
    // rust-lang/cargo#14253
    Package::new("cc", "1.0.0").publish();
    let p = project()
        .file(
            "Cargo.toml",
            r#"
            [package]
            name = "bootstrap"
            edition = "2021"

            [dependencies]
            cc = "1.0.0"

            [build-dependencies]
            cc = "1.0.0"

            [profile.dev]
            debug = 0

            [lints.cargo]
            default = "allow"
            "#,
        )
        .file("src/lib.rs", "")
        .file("build.rs", "fn main() {}")
        .file(
            ".cargo/config.toml",
            "
            target-applies-to-host=false

            [host]
            rustflags = ['--cfg', 'from_host']

            [build]
            rustflags = ['--cfg', 'from_target']
            ",
        )
        .build();

    p.cargo("build -v")
        .masquerade_as_nightly_cargo(&["target-applies-to-host"])
        .arg("-Ztarget-applies-to-host")
        .arg("-Zhost-config")
        .with_stderr_data(
            str![[r#"
[UPDATING] `dummy-registry` index
[RUNNING] `git [..] fetch [..]`
From [ROOTURL]/registry
 * [new ref]         HEAD       -> origin/HEAD
[LOCKING] 1 package to highest compatible version
[DOWNLOADING] crates ...
[DOWNLOADED] cc v1.0.0 (registry `dummy-registry`)
[COMPILING] cc v1.0.0
[RUNNING] `rustc --crate-name cc [..]--cfg from_host[..]`
[RUNNING] `rustc --crate-name cc [..]--cfg from_target[..]`
[COMPILING] bootstrap v0.0.0 ([ROOT]/foo)
[RUNNING] `rustc --crate-name build_script_build [..]--cfg from_host[..]`
[RUNNING] `[ROOT]/foo/target/debug/build/bootstrap/[HASH]/out/build_script_build`
[RUNNING] `rustc --crate-name bootstrap[..]--cfg from_target[..]`
[FINISHED] `dev` profile [unoptimized] target(s) in [ELAPSED]s

"#]]
            .unordered(),
        )
        .run();
}

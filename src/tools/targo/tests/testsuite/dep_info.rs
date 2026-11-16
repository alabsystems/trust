//! Tests for dep-info files. This includes the dep-info file Cargo creates in
//! the output directory, and the ones stored in the fingerprint.

use std::path::Path;

use crate::prelude::*;
use cargo_test_support::compare::assert_e2e;
use cargo_test_support::paths;
use cargo_test_support::registry::Package;
use cargo_test_support::str;
use cargo_test_support::{assert_deps, assert_deps_contains};
use cargo_test_support::{basic_bin_manifest, basic_manifest, main_file, project, rustc_host};
use filetime::FileTime;

// Trust: an unannounced ordinary compile must retain its exact per-crate note
// on reuse. Canonical bootstrap fixtures already announce the lane in the parent.
fn fresh_dep_info_stderr(expect_disclosure: bool) -> snapbox::Data {
    if expect_disclosure {
        str![[r#"
[NOTE] compiled WITHOUT Trust verification — 0 obligations checked

[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]]
        .into()
    } else {
        str![[r#"
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]]
        .into()
    }
}

#[cargo_test]
// Trust: the retained off note describes cached bytes, not a new compilation.
fn fresh_dep_info_replays_fixture_disclosure_without_compiler_invocations() {
    let counter = project()
        .at("compiler-counter")
        .file("Cargo.toml", &basic_bin_manifest("compiler-counter"))
        .file(
            "src/main.rs",
            r#"
            use std::io::Write;
            fn main() {
                // Count every compiler invocation, including information queries.
                // The file is closed before replacing this process with rustc.
                if let Some(path) = std::env::var_os("DEP_INFO_RUSTC_INVOCATIONS") {
                    let mut file = std::fs::OpenOptions::new()
                        .create(true).append(true).open(path).unwrap();
                    file.write_all(b"x").unwrap();
                }
                let mut args = std::env::args_os().skip(1);
                let mut command = std::process::Command::new(args.next().unwrap());
                command.args(args);
                #[cfg(unix)] {
                    // exec preserves the parent's valid jobserver transport;
                    // a second spawn would introduce another FD custody boundary.
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
    counter.cargo("build").run();
    // Trust: keep the canonical announced fixture as an absence control. Test
    // mandatory per-crate replay with the SAME selected real compiler, removing
    // only the fixture announcement transport and explicitly choosing no proof.
    let mut contexts = vec![("canonical-fixture", None, false)];
    if std::env::var_os("TRUST_TARGO_TEST_NO_VERIFY").is_some() {
        let mut selected = cargo_test_support::rustc_fixture_command()
            .expect("complete canonical compiler fixture context");
        let sysroot = selected.args(["--print", "sysroot"]).output().unwrap();
        assert!(sysroot.status.success(), "{sysroot:?}");
        let sysroot = std::str::from_utf8(&sysroot.stdout).unwrap();
        let sysroot = sysroot
            .strip_suffix("\r\n")
            .or_else(|| sysroot.strip_suffix('\n'))
            .expect("one selected compiler sysroot line");
        assert!(!sysroot.contains('\n'));
        // Public sysroots name the real driver `trustc`; bootstrap sysroots
        // may still name it `rustc`. Stay inside the selected sysroot and require
        // its complete verbose identity to match through the shim's documented
        // compatibility spelling below, never an ambient RUSTC guess.
        let bin = std::path::PathBuf::from(sysroot).join("bin");
        let public_driver = bin.join(format!("trustc{}", std::env::consts::EXE_SUFFIX));
        let driver = if public_driver.is_file() {
            public_driver
        } else {
            bin.join(format!("rustc{}", std::env::consts::EXE_SUFFIX))
        };
        assert!(
            driver.is_file(),
            "selected compiler driver: {}",
            driver.display()
        );
        let mut version = cargo_test_support::rustc_fixture_command().unwrap();
        let selected_version = version.arg("-vV").output().unwrap();
        assert!(selected_version.status.success(), "{selected_version:?}");
        assert!(
            std::str::from_utf8(&selected_version.stdout)
                .unwrap()
                .contains("\ntrust: ")
        );
        let mut direct = std::process::Command::new(&driver);
        for (key, value) in version.get_envs() {
            match value {
                Some(value) => {
                    direct.env(key, value);
                }
                None => {
                    direct.env_remove(key);
                }
            }
        }
        let direct_version = direct.arg("-vV").output().unwrap();
        assert!(direct_version.status.success(), "{direct_version:?}");
        // Exactly bootstrap rustc.rs::run_version_query's compatibility
        // spelling. Do not normalize any commit/version/host/Trust/LLVM content
        // or any compiler diagnostic emitted by the actual fixture builds.
        let mut comparable = String::from_utf8(direct_version.stdout).unwrap();
        comparable = comparable.replace("binary: trustc\n", "binary: rustc\n");
        if let Some(rest) = comparable.strip_prefix("trustc ") {
            comparable = format!("rustc {rest}");
        }
        assert_eq!(comparable.as_bytes(), selected_version.stdout);
        contexts.push(("announced-driver", Some((driver.clone(), true)), false));
        contexts.push(("unannounced-driver", Some((driver, false)), true));
    }
    for (context, direct_driver, expect_disclosure) in contexts {
        let p = project()
            .at(context)
            .file("Cargo.toml", &basic_bin_manifest("fresh-dep-info"))
            .file("src/main.rs", "fn main() {}")
            .build();
        let log = p.root().join("compiler-invocations");
        let compiler = counter.bin("compiler-counter");
        let configure = |command: &mut cargo_test_support::Execs| {
            command
                .env("RUSTC_WRAPPER", &compiler)
                .env("DEP_INFO_RUSTC_INVOCATIONS", &log);
            if let Some((driver, announced)) = &direct_driver {
                command.env("RUSTC", driver).env("TRUST_NO_VERIFY", "1");
                if *announced {
                    command.env("TRUST_VANILLA_ANNOUNCED", "1");
                } else {
                    command.env_remove("TRUST_VANILLA_ANNOUNCED");
                }
            }
        };
        let mut cold_command = p.cargo("build --message-format=json");
        configure(&mut cold_command);
        let cold = cold_command.run();
        let cold_calls = std::fs::read(&log).unwrap();
        assert!(
            !cold_calls.is_empty(),
            "compiler counter must observe the cold build"
        );
        let dep_info = p.bin("fresh-dep-info").with_extension("d");
        let cold_dep_info = std::fs::read(&dep_info).unwrap();
        let mut warm_command = p.cargo("build --message-format=json");
        configure(&mut warm_command);
        let warm = warm_command.run();
        assert_eq!(std::fs::read(&log).unwrap(), cold_calls);
        assert_eq!(std::fs::read(&dep_info).unwrap(), cold_dep_info);

        for (output, fresh) in [(&cold, false), (&warm, true)] {
            let messages = std::str::from_utf8(&output.stdout)
                .unwrap()
                .lines()
                .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
                .collect::<Vec<_>>();
            let artifacts = messages
                .iter()
                .filter(|message| message["reason"] == "compiler-artifact")
                .collect::<Vec<_>>();
            assert_eq!(artifacts.len(), 1);
            assert_eq!(artifacts[0]["target"]["name"], "fresh-dep-info");
            assert_eq!(artifacts[0]["fresh"], fresh);
            let notes = messages
                .iter()
                .filter(|message| {
                    message["reason"] == "compiler-message"
                        && message["message"]["message"]
                            == "compiled WITHOUT Trust verification — 0 obligations checked"
                })
                .collect::<Vec<_>>();
            assert_eq!(notes.len(), usize::from(expect_disclosure));
            for note in notes {
                assert_eq!(note["message"]["level"], "note");
                assert!(note["message"]["code"].is_null());
                assert_eq!(note["target"]["name"], "fresh-dep-info");
            }
        }

        let mut text_command = p.cargo("build");
        configure(&mut text_command);
        text_command
            .with_stderr_data(fresh_dep_info_stderr(expect_disclosure))
            .run();
        assert_eq!(std::fs::read(&log).unwrap(), cold_calls);
        assert_eq!(std::fs::read(&dep_info).unwrap(), cold_dep_info);
    }
}

#[cargo_test]
fn build_dep_info() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file("src/foo.rs", &main_file(r#""i am foo""#, &[]))
        .build();

    p.cargo("build").run();

    let depinfo_bin_path = &p.bin("foo").with_extension("d");

    assert!(depinfo_bin_path.is_file());

    let depinfo = p.read_file(depinfo_bin_path);

    let bin_path = p.bin("foo");
    let src_path = p.root().join("src").join("foo.rs");
    if !depinfo.lines().any(|line| {
        line.starts_with(&format!("{}:", bin_path.display()))
            && line.contains(src_path.to_str().unwrap())
    }) {
        panic!(
            "Could not find {:?}: {:?} in {:?}",
            bin_path, src_path, depinfo_bin_path
        );
    }
}

#[cargo_test]
fn build_dep_info_lib() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                authors = []

                [[example]]
                name = "ex"
                crate-type = ["lib"]
            "#,
        )
        .file("build.rs", "fn main() {}")
        .file("src/lib.rs", "")
        .file("examples/ex.rs", "")
        .build();

    p.cargo("build --example=ex").run();
    assert!(p.example_lib("ex", "lib").with_extension("d").is_file());
}

#[cargo_test]
fn build_dep_info_rlib() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                authors = []

                [[example]]
                name = "ex"
                crate-type = ["rlib"]
            "#,
        )
        .file("src/lib.rs", "")
        .file("examples/ex.rs", "")
        .build();

    p.cargo("build --example=ex").run();
    assert!(p.example_lib("ex", "rlib").with_extension("d").is_file());
}

#[cargo_test]
fn build_dep_info_dylib() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                authors = []

                [[example]]
                name = "ex"
                crate-type = ["dylib"]
            "#,
        )
        .file("src/lib.rs", "")
        .file("examples/ex.rs", "")
        .build();

    p.cargo("build --example=ex").run();
    assert!(p.example_lib("ex", "dylib").with_extension("d").is_file());
}

#[cargo_test]
fn dep_path_inside_target_has_correct_path() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("a"))
        .file("target/debug/blah", "")
        .file(
            "src/main.rs",
            r#"
                fn main() {
                    let x = include_bytes!(concat!(env!("CARGO_MANIFEST_DIR"), "/target/debug/blah"));
                }
            "#,
        )
        .build();

    p.cargo("build").run();

    let depinfo_path = &p.bin("a").with_extension("d");

    assert!(depinfo_path.is_file(), "{:?}", depinfo_path);

    let depinfo = p.read_file(depinfo_path);

    let bin_path = p.bin("a");
    let target_debug_blah = Path::new("target").join("debug").join("blah");
    if !depinfo.lines().any(|line| {
        line.starts_with(&format!("{}:", bin_path.display()))
            && line.contains(target_debug_blah.to_str().unwrap())
    }) {
        panic!(
            "Could not find {:?}: {:?} in {:?}",
            bin_path, target_debug_blah, depinfo_path
        );
    }
}

#[cargo_test]
fn external_path_dependency_with_shared_target_dir() {
    let p = project()
        .no_manifest()
        .file(
            ".cargo/config.toml",
            r#"
                [build]
                target-dir = "./target"
            "#,
        )
        .file("external/Cargo.toml", &basic_manifest("external", "0.1.0"))
        .file(
            "external/src/lib.rs",
            r#"
                pub fn value() -> &'static str {
                    include_str!("../../a/shared.txt")
                }
            "#,
        )
        .file(
            "a/Cargo.toml",
            r#"
                [package]
                name = "a"
                version = "0.1.0"
                edition = "2021"

                [workspace]

                [dependencies]
                external = { path = "../external" }
            "#,
        )
        .file(
            "a/src/main.rs",
            r#"fn main() { println!("{}", external::value()); }"#,
        )
        .file("a/shared.txt", "before")
        .file(
            "b/Cargo.toml",
            r#"
                [package]
                name = "b"
                version = "0.1.0"
                edition = "2021"

                [workspace]

                [dependencies]
                external = { path = "../external" }
            "#,
        )
        .file(
            "b/src/main.rs",
            r#"fn main() { println!("{}", external::value()); }"#,
        )
        .file("b/shared.txt", "unrelated")
        .build();

    p.cargo("run")
        .cwd("a")
        .with_stdout_data(str![[r#"
before

"#]])
        .run();

    p.root().move_into_the_past();
    p.root().join("target").move_into_the_past();
    p.change_file("a/shared.txt", "after");

    p.cargo("run")
        .cwd("b")
        .with_stdout_data(str![[r#"
after

"#]])
        .run();
}

#[cargo_test]
fn no_rewrite_if_no_change() {
    let p = project().file("src/lib.rs", "").build();

    p.cargo("build").run();
    let dep_info = p.root().join("target/debug/libfoo.d");
    let metadata1 = dep_info.metadata().unwrap();
    // Trust: checking every target must leave the prior uplifted Build dep-info intact.
    let contents = p.read_file(&dep_info);
    p.cargo("check --all-targets").run();
    assert_eq!(p.read_file(&dep_info), contents);
    assert_eq!(
        FileTime::from_last_modification_time(&metadata1),
        FileTime::from_last_modification_time(&dep_info.metadata().unwrap()),
    );
    p.cargo("build").run();
    let metadata2 = dep_info.metadata().unwrap();

    assert_eq!(
        FileTime::from_last_modification_time(&metadata1),
        FileTime::from_last_modification_time(&metadata2),
    );
}

#[cargo_test(nightly, reason = "-Z binary-dep-depinfo is unstable")]
fn relative_depinfo_paths_ws() {
    // Test relative dep-info paths in a workspace with --target with
    // proc-macros and other dependency kinds.
    Package::new("regdep", "0.1.0")
        .file("src/lib.rs", "pub fn f() {}")
        .publish();
    Package::new("pmdep", "0.1.0")
        .file("src/lib.rs", "pub fn f() {}")
        .publish();
    Package::new("bdep", "0.1.0")
        .file("src/lib.rs", "pub fn f() {}")
        .publish();

    let p = project()
        /*********** Workspace ***********/
        .file(
            "Cargo.toml",
            r#"
            [workspace]
            members = ["foo"]
            "#,
        )
        /*********** Main Project ***********/
        .file(
            "foo/Cargo.toml",
            r#"
            [package]
            name = "foo"
            version = "0.1.0"
            edition = "2018"

            [dependencies]
            pm = {path = "../pm"}
            bar = {path = "../bar"}
            regdep = "0.1"

            [build-dependencies]
            bdep = "0.1"
            bar = {path = "../bar"}

            [lints.cargo]
            default = "allow"
            "#,
        )
        .file(
            "foo/src/main.rs",
            r#"
            pm::noop!{}

            fn main() {
                bar::f();
                regdep::f();
            }
            "#,
        )
        .file("foo/build.rs", "fn main() { bdep::f(); }")
        /*********** Proc Macro ***********/
        .file(
            "pm/Cargo.toml",
            r#"
            [package]
            name = "pm"
            version = "0.1.0"
            edition = "2018"

            [lib]
            proc-macro = true

            [dependencies]
            pmdep = "0.1"

            [lints.cargo]
            default = "allow"
            "#,
        )
        .file(
            "pm/src/lib.rs",
            r#"
            extern crate proc_macro;
            use proc_macro::TokenStream;

            #[proc_macro]
            pub fn noop(_item: TokenStream) -> TokenStream {
                pmdep::f();
                "".parse().unwrap()
            }
            "#,
        )
        /*********** Path Dependency `bar` ***********/
        .file("bar/Cargo.toml", &basic_manifest("bar", "0.1.0"))
        .file("bar/src/lib.rs", "pub fn f() {}")
        .build();

    let host = rustc_host();
    p.cargo("build --target")
        .arg(&host)
        .arg("-Zbinary-dep-depinfo")
        .masquerade_as_nightly_cargo(&["binary-dep-depinfo"])
        .with_stderr_data(str![[r#"
...
[COMPILING] foo v0.1.0 ([ROOT]/foo/foo)
...
"#]])
        .run();

    assert_deps_contains(
        &p,
        "target/debug/build/pm/*/fingerprint/dep-lib-pm",
        &[
            (0, "src/lib.rs"),
            (1, "debug/build/pmdep/*/out/libpmdep-*.rlib"),
        ],
    );

    assert_deps_contains(
        &p,
        &format!("target/{}/debug/build/foo/*/fingerprint/dep-bin-foo", host),
        &[
            (0, "src/main.rs"),
            (
                1,
                &format!(
                    "debug/build/pm/*/out/{}pm-*.{}",
                    paths::get_lib_prefix("proc-macro"),
                    paths::get_lib_extension("proc-macro")
                ),
            ),
            (1, &format!("{}/debug/build/bar/*/out/libbar-*.rlib", host)),
            (
                1,
                &format!("{}/debug/build/regdep/*/out/libregdep-*.rlib", host),
            ),
        ],
    );

    assert_deps_contains(
        &p,
        "target/debug/build/foo/*/fingerprint/dep-build-script-build-script-build",
        &[
            (0, "build.rs"),
            (1, "debug/build/bdep/*/out/libbdep-*.rlib"),
        ],
    );

    // Make sure it stays fresh.
    p.cargo("build --target")
        .arg(&host)
        .arg("-Zbinary-dep-depinfo")
        .masquerade_as_nightly_cargo(&["binary-dep-depinfo"])
        .with_stderr_data(fresh_dep_info_stderr(false))
        .run();
}

#[cargo_test(nightly, reason = "-Z binary-dep-depinfo is unstable")]
fn relative_depinfo_paths_no_ws() {
    // Test relative dep-info paths without a workspace with proc-macros and
    // other dependency kinds.
    Package::new("regdep", "0.1.0")
        .file("src/lib.rs", "pub fn f() {}")
        .publish();
    Package::new("pmdep", "0.1.0")
        .file("src/lib.rs", "pub fn f() {}")
        .publish();
    Package::new("bdep", "0.1.0")
        .file("src/lib.rs", "pub fn f() {}")
        .publish();

    let p = project()
        /*********** Main Project ***********/
        .file(
            "Cargo.toml",
            r#"
            [package]
            name = "foo"
            version = "0.1.0"
            edition = "2018"

            [dependencies]
            pm = {path = "pm"}
            bar = {path = "bar"}
            regdep = "0.1"

            [build-dependencies]
            bdep = "0.1"
            bar = {path = "bar"}

            [lints.cargo]
            default = "allow"
            "#,
        )
        .file(
            "src/main.rs",
            r#"
            pm::noop!{}

            fn main() {
                bar::f();
                regdep::f();
            }
            "#,
        )
        .file("build.rs", "fn main() { bdep::f(); }")
        /*********** Proc Macro ***********/
        .file(
            "pm/Cargo.toml",
            r#"
            [package]
            name = "pm"
            version = "0.1.0"
            edition = "2018"

            [lib]
            proc-macro = true

            [dependencies]
            pmdep = "0.1"

            [lints.cargo]
            default = "allow"
            "#,
        )
        .file(
            "pm/src/lib.rs",
            r#"
            extern crate proc_macro;
            use proc_macro::TokenStream;

            #[proc_macro]
            pub fn noop(_item: TokenStream) -> TokenStream {
                pmdep::f();
                "".parse().unwrap()
            }
            "#,
        )
        /*********** Path Dependency `bar` ***********/
        .file("bar/Cargo.toml", &basic_manifest("bar", "0.1.0"))
        .file("bar/src/lib.rs", "pub fn f() {}")
        .build();

    p.cargo("build")
        .arg("-Zbinary-dep-depinfo")
        .masquerade_as_nightly_cargo(&["binary-dep-depinfo"])
        .with_stderr_data(str![[r#"
...
[COMPILING] foo v0.1.0 ([ROOT]/foo)
...
"#]])
        .run();

    assert_deps_contains(
        &p,
        "target/debug/build/pm/*/fingerprint/dep-lib-pm",
        &[
            (0, "src/lib.rs"),
            (1, "debug/build/pmdep/*/out/libpmdep-*.rlib"),
        ],
    );

    assert_deps_contains(
        &p,
        "target/debug/build/foo/*/fingerprint/dep-bin-foo",
        &[
            (0, "src/main.rs"),
            (
                1,
                &format!(
                    "debug/build/pm/*/out/{}pm-*.{}",
                    paths::get_lib_prefix("proc-macro"),
                    paths::get_lib_extension("proc-macro")
                ),
            ),
            (1, "debug/build/bar/*/out/libbar-*.rlib"),
            (1, "debug/build/regdep/*/out/libregdep-*.rlib"),
        ],
    );

    assert_deps_contains(
        &p,
        "target/debug/build/foo/*/fingerprint/dep-build-script-build-script-build",
        &[
            (0, "build.rs"),
            (1, "debug/build/bdep/*/out/libbdep-*.rlib"),
        ],
    );

    // Make sure it stays fresh.
    p.cargo("build")
        .arg("-Zbinary-dep-depinfo")
        .masquerade_as_nightly_cargo(&["binary-dep-depinfo"])
        .with_stderr_data(fresh_dep_info_stderr(false))
        .run();
}

#[cargo_test]
fn reg_dep_source_not_tracked() {
    // Make sure source files in dep-info file are not tracked for registry dependencies.
    Package::new("regdep", "0.1.0")
        .file("src/lib.rs", "pub fn f() {}")
        .publish();

    let p = project()
        .file(
            "Cargo.toml",
            r#"
            [package]
            name = "foo"
            version = "0.1.0"

            [dependencies]
            regdep = "0.1"
            "#,
        )
        .file("src/lib.rs", "pub fn f() { regdep::f(); }")
        .build();

    p.cargo("check").run();

    assert_deps(
        &p,
        "target/debug/build/regdep/*/fingerprint/dep-lib-regdep",
        |info_path, entries| {
            for (kind, path) in entries {
                if *kind == 1 {
                    panic!(
                        "Did not expect package root relative path type: {:?} in {:?}",
                        path, info_path
                    );
                }
            }
        },
    );
}

#[cargo_test(nightly, reason = "-Z binary-dep-depinfo is unstable")]
fn canonical_path() {
    if !cargo_test_support::symlink_supported() {
        return;
    }
    Package::new("regdep", "0.1.0")
        .file("src/lib.rs", "pub fn f() {}")
        .publish();

    let p = project()
        .file(
            "Cargo.toml",
            r#"
            [package]
            name = "foo"
            version = "0.1.0"

            [dependencies]
            regdep = "0.1"
            "#,
        )
        .file("src/lib.rs", "pub fn f() { regdep::f(); }")
        .build();

    let real = p.root().join("real_target");
    real.mkdir_p();
    p.symlink(real, "target");

    p.cargo("check")
        .arg("-Zbinary-dep-depinfo")
        .masquerade_as_nightly_cargo(&["binary-dep-depinfo"])
        .run();

    assert_deps_contains(
        &p,
        "target/debug/build/foo/*/fingerprint/dep-lib-foo",
        &[
            (0, "src/lib.rs"),
            (1, "debug/build/regdep/*/out/libregdep-*.rmeta"),
        ],
    );
}

#[cargo_test]
fn non_local_build_script() {
    // Non-local build script information is not included.
    Package::new("bar", "1.0.0")
        .file(
            "build.rs",
            r#"
                fn main() {
                    println!("cargo::rerun-if-changed=build.rs");
                }
            "#,
        )
        .file("src/lib.rs", "")
        .publish();
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.1.0"

                [dependencies]
                bar = "1.0"
            "#,
        )
        .file("src/main.rs", "fn main() {}")
        .build();

    p.cargo("build").run();
    let contents = p.read_file("target/debug/foo.d");
    assert_e2e().eq(
        &contents,
        str![[r#"
[ROOT]/foo/target/debug/foo[EXE]: [ROOT]/foo/src/main.rs

"#]],
    );
}

#[cargo_test]
fn no_trailing_separator_after_package_root_build_script() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
            [package]
            name = "foo"
            version = "0.0.1"
            authors = []
            "#,
        )
        .file("src/main.rs", "fn main() {}")
        .file(
            "build.rs",
            r#"
            fn main() {
                println!("cargo::rerun-if-changed=");
            }
            "#,
        )
        .build();

    p.cargo("build").run();
    let contents = p.read_file("target/debug/foo.d");

    assert_e2e().eq(
        &contents,
        str![[r#"
[ROOT]/foo/target/debug/foo[EXE]: [ROOT]/foo [ROOT]/foo/build.rs [ROOT]/foo/src/main.rs

"#]],
    );
}

#[cargo_test(nightly, reason = "proc_macro::tracked::path is unstable")]
fn no_trailing_separator_after_package_root_proc_macro() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
            [package]
            name = "foo"
            version = "0.0.1"
            authors = []
            edition = "2018"

            [dependencies]
            pm = { path = "pm" }
            "#,
        )
        .file(
            "src/main.rs",
            "
            pm::noop!{}
            fn main() {}
            ",
        )
        .file(
            "pm/Cargo.toml",
            r#"
            [package]
            name = "pm"
            version = "0.1.0"
            edition = "2018"

            [lib]
            proc-macro = true
            "#,
        )
        .file(
            "pm/src/lib.rs",
            r#"
            #![feature(proc_macro_tracked_path)]
            extern crate proc_macro;
            use proc_macro::TokenStream;

            #[proc_macro]
            pub fn noop(_item: TokenStream) -> TokenStream {
                proc_macro::tracked::path(
                    std::env::current_dir().unwrap().to_str().unwrap()
                );
                "".parse().unwrap()
            }
            "#,
        )
        .build();

    p.cargo("build").run();
    let contents = p.read_file("target/debug/foo.d");

    assert_e2e().eq(
        &contents,
        str![[r#"
[ROOT]/foo/target/debug/foo[EXE]: [ROOT]/foo [ROOT]/foo/pm/src/lib.rs [ROOT]/foo/src/main.rs

"#]],
    );
}

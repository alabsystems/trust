//! Workspace-only compiler observations must not invalidate external Build units.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn build(
    root: &Path,
    compiler: &Path,
    wrapper: Option<&Path>,
    workspace_wrapper: Option<&Path>,
    extra: &[&str],
) -> Vec<serde_json::Value> {
    let output = build_output(root, compiler, wrapper, workspace_wrapper, extra);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let rows: Vec<_> = String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
        .filter(|row| row["reason"] == "compiler-artifact")
        .collect();
    assert!(!rows.is_empty());
    rows
}

#[expect(
    clippy::disallowed_methods,
    reason = "native fixture selects the caller's genuine compiler and PATH and records the exact test binary used"
)]
fn build_output(
    root: &Path,
    compiler: &Path,
    wrapper: Option<&Path>,
    workspace_wrapper: Option<&Path>,
    extra: &[&str],
) -> Output {
    let executable = std::env::var_os("TARGO_COMPILER_IDENTITY_TEST_BINARY")
        .unwrap_or_else(|| env!("CARGO_BIN_EXE_targo").into());
    let mut command = Command::new(executable);
    command
        .current_dir(root)
        .env_clear()
        .env("HOME", root)
        .env("CARGO_HOME", root.join("home"))
        .env("CARGO_TARGET_DIR", root.join("target"))
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env("RUSTC", compiler)
        .env("REAL_COMPILER", std::env::var_os("RUSTC").unwrap())
        .env("TEST_SYSROOT", root.join("sysroot"))
        .env("CARGO_LOG", "targo_core::compiler::fingerprint=trace")
        .env("__CARGO_TEST_CHANNEL_OVERRIDE_DO_NOT_USE_THIS", "nightly")
        .args([
            "--unverified",
            "build",
            "--offline",
            "-j1",
            "--message-format=json",
        ])
        .args(extra);
    if let Some(wrapper) = wrapper {
        command.env("RUSTC_WRAPPER", wrapper);
    }
    if let Some(wrapper) = workspace_wrapper {
        command.env("RUSTC_WORKSPACE_WRAPPER", wrapper);
    }
    let logs = root
        .parent()
        .unwrap()
        .join("observations")
        .join(root.file_name().unwrap());
    fs::create_dir_all(&logs).unwrap();
    let invocation = fs::read_dir(&logs).unwrap().count();
    let prefix = logs.join(format!("{invocation:03}"));
    fs::write(prefix.with_extension("command.json"), serde_json::to_vec(&serde_json::json!({
        "targo": command.get_program().to_string_lossy(), "compiler": compiler, "wrapper": wrapper,
        "workspace_wrapper": workspace_wrapper, "root": root, "extra": extra
    })).unwrap()).unwrap();
    let output = command.output().unwrap();
    fs::write(prefix.with_extension("stdout"), &output.stdout).unwrap();
    fs::write(prefix.with_extension("stderr"), &output.stderr).unwrap();
    fs::write(prefix.with_extension("status"), output.status.to_string()).unwrap();
    output
}

fn binary(root: &Path, name: &str) -> PathBuf {
    root.join("target/debug")
        .join(format!("{name}{}", std::env::consts::EXE_SUFFIX))
}

fn artifact<'a>(rows: &'a [serde_json::Value], name: &str) -> &'a serde_json::Value {
    rows.iter()
        .find(|row| row["target"]["name"] == name)
        .unwrap_or_else(|| panic!("missing {name} artifact: {rows:?}"))
}

fn freshness(rows: &[serde_json::Value], external: bool, workspace: bool) {
    assert_eq!(artifact(rows, "external")["fresh"], external, "{rows:?}");
    assert_eq!(artifact(rows, "consumer")["fresh"], workspace, "{rows:?}");
}

#[test]
fn compiler_version_observations_follow_the_unit_wrapper_scope() {
    compiler_version_scope(&[], "banner");
}

#[test]
fn build_script_version_observations_follow_the_unit_wrapper_scope() {
    compiler_version_scope(&[], "build-script");
}

#[test]
fn separate_nightlies_build_script_observations_follow_the_unit_wrapper_scope() {
    compiler_version_scope(&["-Zseparate-nightlies"], "build-script");
}

#[test]
fn separate_nightlies_layout_observations_follow_the_unit_wrapper_scope() {
    compiler_version_scope(&["-Zseparate-nightlies"], "banner");
}

#[test]
fn workspace_channel_observation_does_not_invalidate_external_units() {
    compiler_version_scope(&[], "channel");
}
#[test]
fn workspace_host_observation_does_not_invalidate_external_units() {
    compiler_version_scope(&[], "host");
}
#[test]
fn separate_nightlies_channel_observation_does_not_invalidate_external_units() {
    compiler_version_scope(&["-Zseparate-nightlies"], "channel");
}
#[test]
fn separate_nightlies_host_observation_does_not_invalidate_external_units() {
    compiler_version_scope(&["-Zseparate-nightlies"], "host");
}
#[test]
fn unavailable_global_version_is_required_only_for_external_units() {
    compiler_version_scope(&[], "missing");
}
#[test]
fn separate_nightlies_unavailable_global_version_is_required_only_for_external_units() {
    compiler_version_scope(&["-Zseparate-nightlies"], "missing");
}

#[expect(
    clippy::disallowed_methods,
    reason = "fixture builds named actors with the explicitly selected genuine compiler"
)]
fn compiler_version_scope(layout_options: &[&str], selection: &str) {
    let base = std::env::current_dir()
        .unwrap()
        .join(".ubd/compiler-version-scope.noindex");
    fs::create_dir_all(&base).unwrap();
    let temp = tempfile::Builder::new()
        .prefix(selection)
        .tempdir_in(base)
        .unwrap()
        .keep();
    let fixture = temp.join("fixture");
    fs::create_dir_all(fixture.join("src")).unwrap();
    let roles: &[&str] = match selection {
        "banner" | "build-script" => &["compiler", "global-wrapper", "workspace-wrapper"],
        "channel" => &["compiler", "workspace-channel-wrapper"],
        "host" => &["compiler", "workspace-host-wrapper"],
        "missing" => &["placeholder", "workspace-wrapper"],
        _ => unreachable!(),
    };
    let mut manifest = "[package]\nname='scope_actors'\nversion='0.0.0'\nedition='2021'\nautobins=false\n[workspace]\n[features]\ntwo=[]\n[profile.dev]\ndebug=0\nincremental=false\n".to_string();
    for role in roles {
        manifest.push_str(&format!("[[bin]]\nname='{role}'\npath='src/main.rs'\n"));
    }
    fs::write(fixture.join("Cargo.toml"), manifest).unwrap();
    fs::write(
        fixture.join("src/main.rs"),
        r#"
        fn main() {
            let role = env!("CARGO_BIN_NAME");
            let mut args: Vec<_> = std::env::args_os().skip(1).collect();
            let version_query = args.len() == 1 && args[0] == "-vV";
            if role == "placeholder" && version_query {
                eprintln!("global version observation is unavailable");
                std::process::exit(71);
            }
            let program = if role.contains("wrapper") {
                let selected = args.remove(0);
                if role == "workspace-wrapper"
                    && args.len() == 1 && args[0] == "-vV"
                    && std::path::Path::new(&selected).file_stem().unwrap() == "placeholder"
                {
                    std::env::var_os("REAL_COMPILER").unwrap()
                } else {
                    selected
                }
            } else {
                let sysroot = std::path::PathBuf::from(std::env::var_os("TEST_SYSROOT").unwrap());
                if sysroot.is_dir() && args.len() == 1 && args[0] == "--print=sysroot" {
                    println!("{}", sysroot.display());
                    return;
                }
                std::env::var_os("REAL_COMPILER").unwrap()
            };
            let mut command = std::process::Command::new(program);
            command.args(&args).env_remove("CARGO_MAKEFLAGS").env_remove("MAKEFLAGS")
                .env_remove("MFLAGS").env_remove("CARGO_JOBSERVER_HANDOFF");
            if args.len() == 1 && args[0] == "-vV" {
                let output = command.output().unwrap();
                assert!(output.status.success());
                let output = String::from_utf8(output.stdout).unwrap();
                for line in output.lines() {
                    if role == "workspace-channel-wrapper" && line.starts_with("release: ") {
                        println!("release: 1.101.0-beta");
                    } else if role == "workspace-host-wrapper" && line.starts_with("host: ") {
                        let host = line.strip_prefix("host: ").unwrap();
                        let (_, platform) = host.split_once('-').unwrap();
                        let arch = if host.starts_with("aarch64-") { "x86_64" } else { "aarch64" };
                        println!("host: {arch}-{platform}");
                    } else {
                        println!("{line}");
                    }
                }
                let choice = if cfg!(feature="two") { "two" } else { "one" };
                println!("scope-observation: {role}-{choice}");
                return;
            }
            let status = command.status().unwrap();
            std::process::exit(status.code().unwrap_or(1));
        }
        "#,
    )
    .unwrap();
    let real = PathBuf::from(std::env::var_os("RUSTC").unwrap());
    build(&fixture, &real, None, None, &[]);
    let first: Vec<_> = roles
        .iter()
        .map(|name| (*name, fs::read(binary(&fixture, name)).unwrap()))
        .collect();
    let second = if matches!(selection, "banner" | "build-script") {
        build(&fixture, &real, None, None, &["--features", "two"]);
        let second: Vec<_> = roles
            .iter()
            .map(|name| (*name, fs::read(binary(&fixture, name)).unwrap()))
            .collect();
        for ((name, first), (_, second)) in first.iter().zip(&second) {
            assert_ne!(first, second);
            fs::write(binary(&fixture, name), first).unwrap();
        }
        second
    } else {
        Vec::new()
    };
    let bytes = |versions: &[(&str, Vec<u8>)], name: &str| {
        versions
            .iter()
            .find(|(role, _)| *role == name)
            .unwrap()
            .1
            .clone()
    };

    let external = temp.join("external");
    fs::create_dir_all(external.join("src")).unwrap();
    fs::write(
        external.join("Cargo.toml"),
        "[package]\nname='external'\nversion='0.0.0'\nedition='2021'\n[workspace]\n",
    )
    .unwrap();
    fs::write(external.join("src/lib.rs"), "pub const VALUE: u32 = 7;\n").unwrap();
    let root = temp.join("consumer");
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(
        root.join("Cargo.toml"),
        "[package]\nname='consumer'\nversion='0.0.0'\nedition='2021'\n[workspace]\n[dependencies]\nexternal={path='../external'}\n",
    )
    .unwrap();
    fs::write(
        root.join("src/lib.rs"),
        "pub const VALUE: u32 = external::VALUE;\n",
    )
    .unwrap();
    if selection == "build-script" {
        for package in [&external, &root] {
            fs::write(package.join("watched.txt"), "ok").unwrap();
            fs::write(
                package.join("build.rs"),
                r#"
                fn main() {
                    println!("cargo:rerun-if-changed=watched.txt");
                    println!("cargo:rustc-check-cfg=cfg(scope_changed)");
                    if std::fs::read_to_string("watched.txt").unwrap() == "reject" {
                        println!("cargo:rustc-cfg=scope_changed");
                    }
                }
            "#,
            )
            .unwrap();
            let source = package.join("src/lib.rs");
            let previous = fs::read_to_string(&source).unwrap();
            fs::write(source, format!("#[cfg(scope_changed)] compile_error!(\"build script watched input changed\");\n{previous}")).unwrap();
        }
    }
    let libraries = root.join("sysroot/lib/rustlib/native/lib");
    fs::create_dir_all(&libraries).unwrap();
    fs::write(libraries.join("libcore.rlib"), b"fixture sysroot identity").unwrap();
    let compiler = binary(&fixture, "compiler");
    let wrapper = binary(&fixture, "global-wrapper");
    let selected_role = match selection {
        "channel" => "workspace-channel-wrapper",
        "host" => "workspace-host-wrapper",
        _ => "workspace-wrapper",
    };
    let workspace_wrapper = binary(&fixture, selected_role);
    if selection != "missing" {
        let run = |global, workspace| build(&root, &compiler, global, workspace, layout_options);
        let initial = run(None, None);
        freshness(&initial, false, false);
        freshness(&run(None, None), true, true);

        // Both units remain CompileMode::Build. Only the workspace command gains
        // a wrapper and a different real -vV observation. The external artifact
        // must remain reusable, including its existing compiler output receipt.
        let wrapped = run(None, Some(workspace_wrapper.as_path()));
        if selection == "host" {
            let report = Command::new(&workspace_wrapper)
                .args([compiler.as_os_str(), "-vV".as_ref()])
                .env_clear()
                .env("REAL_COMPILER", &real)
                .env("TEST_SYSROOT", root.join("sysroot"))
                .output()
                .unwrap();
            fs::write(temp.join("host-wrapper-version.stdout"), &report.stdout).unwrap();
            fs::write(temp.join("host-wrapper-version.stderr"), &report.stderr).unwrap();
            fs::write(
                temp.join("host-wrapper-version.status"),
                report.status.to_string(),
            )
            .unwrap();
            assert!(report.status.success());
            let version = String::from_utf8(report.stdout).unwrap();
            let hosts: Vec<_> = version
                .lines()
                .filter_map(|line| line.strip_prefix("host: "))
                .collect();
            assert_eq!(hosts.len(), 1, "{version}");
            let declared_host = hosts[0];
            let before = artifact(&initial, "external");
            let after = artifact(&wrapped, "external");
            let consumer = artifact(&wrapped, "consumer");
            let observed = serde_json::json!({
                "initial_external": before,
                "wrapped_external": after,
                "wrapped_consumer": consumer,
                "declared_workspace_host": declared_host,
                "external_target_unchanged": before["trust_compile_target"] == after["trust_compile_target"],
                "external_exact_unit_unchanged": before["trust_unit_identity_sha256"] == after["trust_unit_identity_sha256"],
            });
            // Preserve both observations before either comparison can fail.
            fs::write(
                temp.join("host-scope-observation.json"),
                serde_json::to_vec_pretty(&observed).unwrap(),
            )
            .unwrap();
            for external in [before, after] {
                assert_eq!(external["trust_compile_kind"], "host", "{observed}");
                assert_eq!(external["trust_compile_mode"], "build", "{observed}");
                let identity = external["trust_unit_identity_sha256"].as_str().unwrap();
                assert_eq!(identity.len(), 64, "{observed}");
                assert!(identity.bytes().all(|byte| byte.is_ascii_hexdigit()));
            }
            assert_ne!(before["trust_compile_target"], declared_host, "{observed}");
            assert_eq!(
                before["trust_compile_target"], after["trust_compile_target"],
                "{observed}"
            );
            assert_eq!(
                before["trust_unit_identity_sha256"], after["trust_unit_identity_sha256"],
                "{observed}"
            );
            // This is the wrapper's observation, not emitted-machine-byte evidence.
            assert_eq!(
                consumer["trust_compile_target"], declared_host,
                "{observed}"
            );
        }
        freshness(&wrapped, true, false);
        assert_eq!(
            artifact(&initial, "external")["filenames"],
            artifact(&wrapped, "external")["filenames"]
        );
        assert_ne!(
            artifact(&initial, "consumer")["filenames"],
            artifact(&wrapped, "consumer")["filenames"]
        );
        freshness(&run(None, Some(workspace_wrapper.as_path())), true, true);
        if selection == "build-script" {
            // Content inputs remain authoritative: an unchanged compiler
            // observation must not make a changed script input fresh.
            fs::write(external.join("watched.txt"), "reject").unwrap();
            let refused = build_output(
                &root,
                &compiler,
                None,
                Some(&workspace_wrapper),
                layout_options,
            );
            assert!(!refused.status.success());
            assert!(
                String::from_utf8_lossy(&refused.stdout)
                    .lines()
                    .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
                    .any(|row| row["reason"] == "compiler-message"
                        && row["message"]["level"] == "error"
                        && row["message"]["message"] == "build script watched input changed")
            );
            fs::write(external.join("watched.txt"), "ok").unwrap();
            run(None, Some(workspace_wrapper.as_path()));
            freshness(&run(None, Some(workspace_wrapper.as_path())), true, true);
        }
        if !matches!(selection, "banner" | "build-script") {
            return;
        }
        fs::write(&workspace_wrapper, bytes(&second, "workspace-wrapper")).unwrap();
        let changed = run(None, Some(workspace_wrapper.as_path()));
        freshness(&changed, true, false);
        assert_eq!(
            artifact(&initial, "external")["filenames"],
            artifact(&changed, "external")["filenames"]
        );

        // The outer wrapper participates in both actual compiler commands. Its
        // introduction and content replacement must invalidate both scopes.
        freshness(
            &run(Some(wrapper.as_path()), Some(workspace_wrapper.as_path())),
            false,
            false,
        );
        freshness(
            &run(Some(wrapper.as_path()), Some(workspace_wrapper.as_path())),
            true,
            true,
        );
        fs::write(&wrapper, bytes(&second, "global-wrapper")).unwrap();
        freshness(
            &run(Some(wrapper.as_path()), Some(workspace_wrapper.as_path())),
            false,
            false,
        );
        freshness(&run(None, Some(workspace_wrapper.as_path())), true, true);

        // An actual selected compiler change remains an input in both scopes.
        fs::write(&compiler, bytes(&second, "compiler")).unwrap();
        freshness(&run(None, Some(workspace_wrapper.as_path())), false, false);
        fs::write(&compiler, bytes(&first, "compiler")).unwrap();
        freshness(&run(None, None), true, true);
        return;
    }

    // A workspace wrapper may supply a working compiler version when the
    // configured compiler cannot answer -vV by itself. Refuse that missing
    // observation only once an external unit actually needs the global key.
    let workspace_only = temp.join("workspace-only");
    fs::create_dir_all(workspace_only.join("src")).unwrap();
    let manifest = workspace_only.join("Cargo.toml");
    let package =
        "[package]\nname='workspace_only'\nversion='0.0.0'\nedition='2021'\n[workspace]\n";
    fs::write(&manifest, package).unwrap();
    fs::write(
        workspace_only.join("src/lib.rs"),
        "pub const VALUE: u32 = 7;\n",
    )
    .unwrap();
    let libraries = workspace_only.join("sysroot/lib/rustlib/native/lib");
    fs::create_dir_all(&libraries).unwrap();
    fs::write(libraries.join("libcore.rlib"), b"fixture sysroot identity").unwrap();
    let placeholder = binary(&fixture, "placeholder");
    let output = build_output(
        &workspace_only,
        &placeholder,
        None,
        Some(&workspace_wrapper),
        layout_options,
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    fs::write(
        &manifest,
        format!("{package}[dependencies]\nexternal={{path='../external'}}\n"),
    )
    .unwrap();
    let output = build_output(
        &workspace_only,
        &placeholder,
        None,
        Some(&workspace_wrapper),
        layout_options,
    );
    assert!(
        !output.status.success(),
        "a workspace version must not answer the global request"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("global version observation is unavailable"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[expect(
    clippy::disallowed_methods,
    reason = "native custody fixture uses the explicitly selected genuine compiler"
)]
fn build_script_window_starts_after_prerequisites_and_covers_execution() {
    let base = std::env::current_dir()
        .unwrap()
        .join(".ubd/build-script-window.noindex");
    fs::create_dir_all(&base).unwrap();
    let temp = tempfile::Builder::new().tempdir_in(base).unwrap().keep();
    for name in ["consumer", "watched", "blocker"] {
        fs::create_dir_all(temp.join(name).join("src")).unwrap();
    }
    let root = temp.join("consumer");
    fs::write(root.join("Cargo.toml"), "[workspace]\n[package]\nname='consumer'\nversion='0.0.0'\nedition='2021'\n[dependencies]\nwatched={path='../watched'}\n").unwrap();
    fs::write(
        root.join("src/lib.rs"),
        "pub fn value()->u8 { watched::value() }\n",
    )
    .unwrap();
    let watched = temp.join("watched");
    fs::write(watched.join("Cargo.toml"), "[package]\nname='watched'\nversion='0.0.0'\nedition='2021'\n[build-dependencies]\nblocker={path='../blocker'}\n").unwrap();
    fs::write(watched.join("src/lib.rs"), "pub fn value()->u8 { 1 }\n").unwrap();
    fs::write(watched.join("watched.txt"), "stable").unwrap();
    fs::write(
        watched.join("build.rs"),
        r#"
fn main() {
    blocker::noop();
    println!("cargo:rerun-if-changed=watched.txt");
    assert_eq!(std::fs::read_to_string("watched.txt").unwrap(), "stable", "changed watched input");
}
"#,
    )
    .unwrap();
    let blocker = temp.join("blocker");
    fs::write(
        blocker.join("Cargo.toml"),
        "[package]\nname='blocker'\nversion='0.0.0'\nedition='2021'\n",
    )
    .unwrap();
    fs::write(blocker.join("src/lib.rs"), "pub fn noop() {}\n").unwrap();
    // This prerequisite changes an ancestor directory stamp before watched's
    // actual script starts, without changing any watched input.
    fs::write(
        blocker.join("build.rs"),
        r#"
fn main() {
    let root = std::path::PathBuf::from(std::env::var_os("CARGO_MANIFEST_DIR").unwrap());
    std::fs::write(root.parent().unwrap().join("unrelated-generated-file"), "unrelated").unwrap();
    println!("cargo:rerun-if-env-changed=WINDOW_CONTROL");
}
"#,
    )
    .unwrap();
    let compiler = PathBuf::from(std::env::var_os("RUSTC").unwrap());
    let first = build(&root, &compiler, None, None, &[]);
    assert_eq!(artifact(&first, "watched")["fresh"], false);
    let second = build(&root, &compiler, None, None, &[]);
    assert_eq!(artifact(&second, "watched")["fresh"], true);
    assert_eq!(artifact(&second, "consumer")["fresh"], true);

    fs::write(watched.join("watched.txt"), "changed").unwrap();
    let changed = build_output(&root, &compiler, None, None, &[]);
    assert!(!changed.status.success());
    assert!(String::from_utf8_lossy(&changed.stderr).contains("changed watched input"));
    fs::write(watched.join("watched.txt"), "stable").unwrap();
    build(&root, &compiler, None, None, &[]);
    assert_eq!(
        artifact(&build(&root, &compiler, None, None, &[]), "watched")["fresh"],
        true
    );

    // An edit-and-restore DURING the script must still prevent publication of
    // a reusable content fingerprint, even though final bytes are unchanged.
    fs::write(
        watched.join("build.rs"),
        r#"
fn main() {
    blocker::noop();
    println!("cargo:rerun-if-changed=watched.txt");
    let original = std::fs::read("watched.txt").unwrap();
    std::fs::write("watched.txt", "transient").unwrap();
    std::fs::write("watched.txt", original).unwrap();
}
"#,
    )
    .unwrap();
    build(&root, &compiler, None, None, &[]);
    let after_restore = build(&root, &compiler, None, None, &[]);
    assert_eq!(artifact(&after_restore, "watched")["fresh"], false);
}

//! Native reuse must notice changed linker bytes and default-tool selection.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

#![cfg(any(target_os = "linux", target_os = "macos"))]

use std::ffi::OsString;
use std::fs;
use std::os::unix::process::ExitStatusExt as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use serde_json::{Value, json};

#[expect(
    clippy::disallowed_methods,
    reason = "the isolated native fixture selects its actual CLI and explicit original compiler tools before project configuration exists"
)]
fn command(project: &Path, world: &Path, target: &Path) -> Command {
    let executable = std::env::var_os("TARGO_NATIVE_CACHE_REUSE_TEST_BINARY")
        .unwrap_or_else(|| env!("CARGO_BIN_EXE_targo").into());
    let mut command = Command::new(executable);
    command
        .current_dir(project)
        .env_clear()
        .env("HOME", world)
        .env("CARGO_HOME", world.join("home"))
        .env("CARGO_TARGET_DIR", target)
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env(
            "RUSTC",
            std::env::var_os("RUSTC").expect("explicit original compiler"),
        );
    // These fixtures build and run native artifacts; none invokes rustdoc.
    // Preserve an explicit matching tool when supplied, without requiring a
    // documentation producer to exercise compiler cache reuse.
    if let Some(rustdoc) = std::env::var_os("RUSTDOC") {
        command.env("RUSTDOC", rustdoc);
    }
    #[cfg(target_os = "macos")]
    command.env("SDKROOT", sdk_root(world));
    command
}

#[cfg(target_os = "macos")]
fn sdk_root(world: &Path) -> PathBuf {
    use std::os::unix::ffi::OsStringExt as _;

    // Select genuine fixture input once, then keep its exact value through
    // cold/warm/mutation/rewarm and independent-target commands. Discovery is
    // a separate producer control; these cases require the reusable profile.
    let input = world.join("evidence/sdkroot-input");
    let bytes = match fs::read(&input) {
        Ok(bytes) => bytes,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            let query = record(
                Command::new("/usr/bin/xcrun")
                    .args(["--sdk", "macosx", "--show-sdk-path"])
                    .env("PATH", "/usr/bin:/bin:/usr/sbin:/sbin")
                    .env_remove("SDKROOT"),
                world,
                "sdk-query",
            );
            assert!(query.status.success(), "world={}", world.display());
            let mut bytes = query.stdout;
            assert_eq!(bytes.pop(), Some(b'\n'), "complete real SDK path");
            fs::write(&input, &bytes).unwrap();
            bytes
        }
        Err(error) => panic!("cannot read fixed SDK input: {error}"),
    };
    let sdk = PathBuf::from(OsString::from_vec(bytes));
    assert!(
        sdk.is_absolute()
            && sdk != Path::new("/")
            && sdk.join("SDKSettings.plist").is_file()
            && sdk.to_str().is_some(),
        "real UTF-8 SDK required: world={} sdk={sdk:?}",
        world.display(),
    );
    sdk
}

fn record(command: &mut Command, world: &Path, label: &str) -> Output {
    fs::write(
        world.join("evidence").join(format!("{label}.command.json")),
        serde_json::to_vec_pretty(&json!({
            "program":command.get_program(), "args":command.get_args().collect::<Vec<_>>(),
            "cwd":command.get_current_dir(),
            "environment":command.get_envs().collect::<Vec<_>>(),
        }))
        .unwrap(),
    )
    .unwrap();
    let result = command.output();
    let status = match &result {
        Ok(output) => json!({"success":output.status.success(), "code":output.status.code(),
            "signal":output.status.signal(), "display":output.status.to_string()}),
        Err(error) => json!({"spawn_error":error.to_string()}),
    };
    fs::write(
        world.join("evidence").join(format!("{label}.status.json")),
        serde_json::to_vec_pretty(&status).unwrap(),
    )
    .unwrap();
    let output = result.expect("launch recorded native fixture command");
    fs::write(
        world.join("evidence").join(format!("{label}.stdout")),
        &output.stdout,
    )
    .unwrap();
    fs::write(
        world.join("evidence").join(format!("{label}.stderr")),
        &output.stderr,
    )
    .unwrap();
    output
}

fn digest(path: &Path) -> String {
    cargo_util::Sha256::new()
        .update_path(path)
        .unwrap()
        .finish_hex()
}

fn artifacts(output: &Output) -> Vec<Value> {
    output
        .stdout
        .split(|byte| *byte == b'\n')
        .filter_map(|line| serde_json::from_slice::<Value>(line).ok())
        .filter(|row| row["reason"] == "compiler-artifact")
        .collect()
}

fn build_command(project: &Path, world: &Path, target: &Path) -> Command {
    let mut command = command(project, world, target);
    command.args([
        "--unverified",
        "build",
        "--offline",
        "-vv",
        "-j1",
        "--message-format=json",
    ]);
    command
}

fn executable(output: &Output, name: &str) -> PathBuf {
    artifacts(output)
        .into_iter()
        .find(|row| row["target"]["name"] == name)
        .and_then(|row| row["executable"].as_str().map(PathBuf::from))
        .expect("actual compiler-artifact executable path")
}

fn snapshot_cache(target: &Path) -> Value {
    let mut directories = Vec::new();
    // Both maintained layouts are bounded here to this one-package fixture.
    // New layout: debug/build/<package>/<unit>/fingerprint.
    // Legacy layout: debug/.fingerprint/<package>-<unit>.
    for (root, new_layout) in [
        (target.join("debug/build/linker_consumer"), true),
        (target.join("debug/.fingerprint"), false),
    ] {
        if !root.is_dir() {
            continue;
        }
        for (index, entry) in fs::read_dir(root).unwrap().enumerate() {
            assert!(index < 32, "unexpected fixture unit inventory");
            let entry = entry.unwrap();
            if new_layout {
                directories.push(entry.path().join("fingerprint"));
            } else if entry
                .file_name()
                .as_encoded_bytes()
                .starts_with(b"linker_consumer-")
            {
                directories.push(entry.path());
            }
        }
    }
    let mut records = Vec::new();
    for directory in directories {
        for name in [
            "bin-linker_consumer",
            "bin-linker_consumer.json",
            "dep-bin-linker_consumer",
            "outputs-bin-linker_consumer.json",
        ] {
            let path = directory.join(name);
            if path.is_file() {
                let bytes = fs::read(&path).unwrap();
                records.push(json!({"path":path, "sha256":digest(&path), "bytes":bytes}));
            }
        }
    }
    records.sort_by(|a, b| a["path"].as_str().cmp(&b["path"].as_str()));
    json!(records)
}

fn app_stage(project: &Path, world: &Path, target: &Path, linker: &Path, label: &str) -> Value {
    app_stage_on_path(project, world, target, linker, label, None)
}

fn app_stage_on_path(
    project: &Path,
    world: &Path,
    target: &Path,
    linker: &Path,
    label: &str,
    search_path: Option<&std::ffi::OsStr>,
) -> Value {
    let mut command = build_command(project, world, target);
    command.arg("--locked");
    if let Some(search_path) = search_path {
        command.env("PATH", search_path);
    }
    let search_path = command
        .get_envs()
        .find(|(name, _)| *name == "PATH")
        .and_then(|(_, value)| value)
        .map(OsString::from);
    let args = command.get_args().map(OsString::from).collect::<Vec<_>>();
    let output = record(&mut command, world, label);
    let binary = target.join("debug/linker_consumer");
    let execution = binary.is_file().then(|| {
        record(
            &mut Command::new(&binary),
            world,
            &format!("{label}-program"),
        )
    });
    let observed = json!({
        "success":output.status.success(), "args":args, "search_path":search_path,
        "artifacts":artifacts(&output),
        "source_sha256":digest(&project.join("src/main.rs")),
        "manifest_sha256":digest(&project.join("Cargo.toml")),
        "config_sha256":digest(&project.join(".cargo/config.toml")),
        "lock_sha256":digest(&project.join("Cargo.lock")), "linker_sha256":digest(linker),
        "binary_sha256":binary.is_file().then(|| digest(&binary)),
        "program_success":execution.as_ref().map(|output| output.status.success()),
        "program_stdout":execution.as_ref().map(|output| &output.stdout),
        "linker_trace":fs::read(world.join("control/linker.trace")).unwrap(),
        "cache":snapshot_cache(target),
    });
    fs::write(
        world
            .join("evidence")
            .join(format!("{label}.observed.json")),
        serde_json::to_vec_pretty(&observed).unwrap(),
    )
    .unwrap();
    observed
}

fn all_fresh(stage: &Value, fresh: bool) -> bool {
    stage["artifacts"].as_array().is_some_and(|rows| {
        rows.len() == 1
            && rows[0]["target"]["name"] == "linker_consumer"
            && rows[0]["fresh"] == fresh
    })
}

#[test]
fn symlinked_source_directory_reuses_real_build_script_outputs() {
    use std::os::unix::fs::symlink;

    let base = std::env::current_dir()
        .unwrap()
        .join(".ubd/native-cache-reuse.noindex");
    fs::create_dir_all(&base).unwrap();
    let world = tempfile::Builder::new()
        .prefix("source-alias")
        .tempdir_in(base)
        .unwrap()
        .keep();
    fs::create_dir_all(world.join("evidence")).unwrap();
    let target = world.join("target");
    let alias = world.join("source-alias");
    for name in ["first", "second"] {
        let project = world.join(name);
        fs::create_dir_all(project.join("src")).unwrap();
        fs::write(project.join("Cargo.toml"), "[package]\nname='alias_consumer'\nversion='0.0.0'\nedition='2021'\n[workspace]\n[profile.dev]\ndebug=0\nincremental=false\n").unwrap();
        fs::write(project.join("build.rs"), "fn main() { println!(\"cargo:rerun-if-changed=build.rs\"); println!(\"cargo:rustc-env=ALIAS_VALUE=alias-ok\"); }\n").unwrap();
        fs::write(
            project.join("src/main.rs"),
            "fn main() { println!(\"{}\", env!(\"ALIAS_VALUE\")); }\n",
        )
        .unwrap();
    }
    symlink(world.join("first"), &alias).unwrap();
    let lock = record(
        command(&world.join("first"), &world, &target).args(["generate-lockfile", "--offline"]),
        &world,
        "lock",
    );
    assert!(lock.status.success(), "world={}", world.display());
    fs::copy(
        world.join("first/Cargo.lock"),
        world.join("second/Cargo.lock"),
    )
    .unwrap();
    for (label, expected_fresh) in [
        ("cold", false),
        ("warm", true),
        ("retargeted", false),
        ("rewarm", true),
    ] {
        if label == "retargeted" {
            // Identical source bytes and manifest spelling, different actual
            // cwd: the old compiler context must not authorize this target.
            fs::remove_file(&alias).unwrap();
            symlink(world.join("second"), &alias).unwrap();
        }
        let output = record(
            build_command(&world.join("first"), &world, &target)
                .arg("--manifest-path")
                .arg(alias.join("Cargo.toml")),
            &world,
            label,
        );
        assert!(
            output.status.success(),
            "world={} stage={label}",
            world.display()
        );
        let rows = artifacts(&output);
        assert_eq!(rows.len(), 2, "world={} stage={label}", world.display());
        assert!(
            rows.iter().all(|row| row["fresh"] == expected_fresh),
            "world={} stage={label} rows={rows:?}",
            world.display()
        );
        assert!(
            rows.iter()
                .any(|row| row["target"]["kind"] == json!(["custom-build"]))
        );
        let run = record(
            &mut Command::new(executable(&output, "alias_consumer")),
            &world,
            &format!("{label}-program"),
        );
        assert!(run.status.success());
        assert_eq!(run.stdout, b"alias-ok\n");
    }
}

#[expect(
    clippy::disallowed_methods,
    reason = "the fixture selects and records its original native linker driver, without project Config"
)]
fn linker_driver() -> PathBuf {
    let selected = std::env::var_os("TARGO_NATIVE_CACHE_REUSE_LINKER_DRIVER")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            cargo_util::paths::resolve_executable(Path::new("cc"))
                .expect("original C linker driver")
        });
    assert!(
        selected.is_absolute(),
        "linker driver must have an absolute original path"
    );
    selected
}

#[test]
fn same_path_configured_linker_replacement_invalidates_native_reuse() {
    let base = std::env::current_dir()
        .unwrap()
        .join(".ubd/native-cache-reuse.noindex");
    fs::create_dir_all(&base).unwrap();
    let world = tempfile::Builder::new()
        .prefix("linker-identity")
        .tempdir_in(base)
        .unwrap()
        .keep();
    for path in [
        "app/src",
        "app/.cargo",
        "wrapper/src",
        "object-one/src",
        "object-two/src",
        "objects",
        "control",
        "home",
        "wrapper-target",
        "object-one-target",
        "object-two-target",
        "app-target",
        "witness-target",
        "evidence",
    ] {
        fs::create_dir_all(world.join(path)).unwrap();
    }
    fs::write(world.join("control/linker.trace"), []).unwrap();
    let driver = linker_driver();
    fs::write(
        world.join("evidence/driver.json"),
        serde_json::to_vec_pretty(&json!({"path":driver,"sha256":digest(&driver)})).unwrap(),
    )
    .unwrap();
    let mut host_command = cargo_test_support::rustc_fixture_command().unwrap();
    let host_query = record(host_command.arg("-vV"), &world, "host-query");
    assert!(host_query.status.success(), "world={}", world.display());
    let version = String::from_utf8(host_query.stdout).unwrap();
    let hosts = version
        .lines()
        .filter_map(|line| line.strip_prefix("host: "))
        .collect::<Vec<_>>();
    assert_eq!(hosts.len(), 1, "world={}", world.display());
    let objects = [world.join("objects/one.o"), world.join("objects/two.o")];
    for (index, (name, object)) in ["one", "two"].into_iter().zip(&objects).enumerate() {
        let project = world.join(format!("object-{name}"));
        fs::write(project.join("Cargo.toml"), format!("[package]\nname='linker_object_{name}'\nversion='0.0.0'\nedition='2021'\n[workspace]\n[profile.dev]\npanic='abort'\ndebug=0\nincremental=false\ncodegen-units=1\n")).unwrap();
        fs::write(project.join("src/lib.rs"), format!("#![no_std]\n#[no_mangle]\npub extern \"C\" fn linker_fixture_value() -> u32 {{ {} }}\n", index+1)).unwrap();
        let mut command = command(
            &project,
            &world,
            &world.join(format!("object-{name}-target")),
        );
        command
            .args([
                "--unverified",
                "rustc",
                "--lib",
                "--offline",
                "-j1",
                "--message-format=json",
                "--",
            ])
            .arg(format!("--emit=obj={}", object.display()));
        let output = record(&mut command, &world, &format!("object-{name}"));
        assert!(
            output.status.success() && object.is_file(),
            "world={} object={name}",
            world.display()
        );
    }
    let wrapper = world.join("wrapper");
    fs::write(wrapper.join("Cargo.toml"), "[package]\nname='native_linker_wrapper'\nversion='0.0.0'\nedition='2021'\n[workspace]\n[features]\ntwo=[]\n[profile.dev]\ndebug=0\nincremental=false\n").unwrap();
    let wrapper_source = format!(
        r#"
use std::io::Write;
use std::os::unix::process::CommandExt;
fn main() {{
    let object = if cfg!(feature="two") {{ {two:?} }} else {{ {one:?} }};
    let args = std::env::args_os().skip(1).collect::<Vec<_>>();
    let mut trace = std::fs::OpenOptions::new().append(true).open({trace:?}).unwrap();
    writeln!(trace, "object={{object}} args={{args:?}}").unwrap();
    trace.flush().unwrap();
    let error = std::process::Command::new({driver:?}).args(args).arg(object)
        .env_remove("CARGO_MAKEFLAGS").env_remove("MAKEFLAGS").env_remove("MFLAGS")
        .env_remove("CARGO_JOBSERVER_HANDOFF").exec();
    panic!("actual linker driver could not execute: {{error}}");
}}
"#,
        one = objects[0],
        two = objects[1],
        trace = world.join("control/linker.trace")
    );
    fs::write(wrapper.join("src/main.rs"), &wrapper_source).unwrap();
    let wrapper_target = world.join("wrapper-target");
    let first_wrapper = record(
        &mut build_command(&wrapper, &world, &wrapper_target),
        &world,
        "wrapper-one",
    );
    assert!(first_wrapper.status.success(), "world={}", world.display());
    // Use the executable's actual produced path. Rebuilding this Cargo project
    // replaces that same linker; no executable copies or alternate roles exist.
    let linker = executable(&first_wrapper, "native_linker_wrapper");
    let first_linker_hash = digest(&linker);
    let app = world.join("app");
    fs::write(app.join("Cargo.toml"), "[package]\nname='linker_consumer'\nversion='0.0.0'\nedition='2021'\n[workspace]\n[profile.dev]\ndebug=0\nincremental=false\n").unwrap();
    fs::write(app.join("src/main.rs"), "extern \"C\" { fn linker_fixture_value() -> u32; }\nfn main() { println!(\"{}\", unsafe { linker_fixture_value() }); }\n").unwrap();
    fs::write(
        app.join(".cargo/config.toml"),
        format!(
            "[target.{}]\nlinker={}\n",
            serde_json::to_string(hosts[0]).unwrap(),
            serde_json::to_string(&linker).unwrap()
        ),
    )
    .unwrap();
    let app_target = world.join("app-target");
    let lock = record(
        command(&app, &world, &app_target).args(["generate-lockfile", "--offline"]),
        &world,
        "app-lock",
    );
    assert!(lock.status.success(), "world={}", world.display());
    let cold = app_stage(&app, &world, &app_target, &linker, "cold");
    let warm = app_stage(&app, &world, &app_target, &linker, "warm");
    let second_wrapper = record(
        build_command(&wrapper, &world, &wrapper_target).args(["--features", "two"]),
        &world,
        "wrapper-two",
    );
    assert!(second_wrapper.status.success(), "world={}", world.display());
    let second_linker = executable(&second_wrapper, "native_linker_wrapper");
    let second_linker_hash = digest(&linker);
    let changed = app_stage(&app, &world, &app_target, &linker, "changed");
    let rewarm = app_stage(&app, &world, &app_target, &linker, "rewarm");
    // An independent target proves the new linker/object works. Never alter the
    // warmed target, its short fingerprint, receipts or failed result afterward.
    let witness = app_stage(
        &app,
        &world,
        &world.join("witness-target"),
        &linker,
        "witness",
    );
    #[cfg(target_os = "macos")]
    let access_control = {
        use std::os::unix::fs::PermissionsExt as _;

        let mode = fs::metadata(&linker).unwrap().permissions().mode();
        let acl = "everyone deny execute";
        let denial = record(
            Command::new("/bin/chmod").args(["+a", acl]).arg(&linker),
            &world,
            "access-deny",
        );
        assert!(denial.status.success(), "world={}", world.display());
        let denied = app_stage(&app, &world, &app_target, &linker, "access-denied");
        let denied_mode = fs::metadata(&linker).unwrap().permissions().mode();
        let permission_denied = fs::read(world.join("evidence/access-denied.stdout"))
            .unwrap()
            .split(|byte| *byte == b'\n')
            .filter_map(|line| serde_json::from_slice::<Value>(line).ok())
            .any(|message| {
                message["reason"] == "compiler-message"
                    && message["message"]["rendered"].as_str().is_some_and(|text| {
                        text.contains("could not exec the linker")
                            && text.contains(linker.to_str().unwrap())
                            && text.contains("Permission denied (os error 13)")
                    })
            });
        let restoration = record(
            Command::new("/bin/chmod").args(["-a", acl]).arg(&linker),
            &world,
            "access-restore",
        );
        assert!(restoration.status.success(), "world={}", world.display());
        let recovered = app_stage(&app, &world, &app_target, &linker, "access-recovered");
        let rewarm = app_stage(&app, &world, &app_target, &linker, "access-rewarm");
        json!({"original_mode":mode, "denied_mode":denied_mode, "permission_denied":permission_denied,
            "denied":denied, "recovered":recovered, "rewarm":rewarm})
    };
    #[cfg(not(target_os = "macos"))]
    let access_control = Value::Null;
    let observed = json!({"world":world, "linker":linker, "second_linker":second_linker,
        "first_linker_sha256":first_linker_hash, "second_linker_sha256":second_linker_hash,
        "objects":objects.iter().map(|path| json!({"path":path,"sha256":digest(path)})).collect::<Vec<_>>(),
        "cold":cold, "warm":warm, "changed":changed, "rewarm":rewarm, "witness":witness,
        "access_control":access_control});
    fs::write(
        world.join("observed.json"),
        serde_json::to_vec_pretty(&observed).unwrap(),
    )
    .unwrap();
    assert_eq!(linker, second_linker, "wrapper path changed: {observed}");
    assert_ne!(
        first_linker_hash, second_linker_hash,
        "linker bytes unchanged: {observed}"
    );
    for stage in [&cold, &warm, &changed, &rewarm, &witness] {
        assert_eq!(stage["success"], true, "native compile failed: {observed}");
        assert_eq!(
            stage["program_success"], true,
            "native program failed: {observed}"
        );
        for key in [
            "source_sha256",
            "manifest_sha256",
            "config_sha256",
            "lock_sha256",
            "args",
        ] {
            assert_eq!(
                cold[key], stage[key],
                "app input changed ({key}): {observed}"
            );
        }
    }
    assert!(
        all_fresh(&cold, false) && all_fresh(&warm, true),
        "cold/warm control: {observed}"
    );
    for stage in [&cold, &warm] {
        for name in [
            "bin-linker_consumer",
            "bin-linker_consumer.json",
            "dep-bin-linker_consumer",
            "outputs-bin-linker_consumer.json",
        ] {
            assert!(
                stage["cache"].as_array().unwrap().iter().any(|record| {
                    record["path"].as_str().is_some_and(|path| {
                        Path::new(path).file_name() == Some(std::ffi::OsStr::new(name))
                    })
                }),
                "missing actual {name} evidence: {observed}"
            );
        }
    }
    assert_eq!(cold["program_stdout"], json!(b"1\n"), "{observed}");
    assert_eq!(warm["program_stdout"], json!(b"1\n"), "{observed}");
    assert_eq!(
        cold["linker_trace"], warm["linker_trace"],
        "warm unexpectedly linked: {observed}"
    );
    assert!(
        all_fresh(&witness, false),
        "fresh target did not compile: {observed}"
    );
    assert_eq!(
        witness["program_stdout"],
        json!(b"2\n"),
        "new linker is invalid: {observed}"
    );
    assert_ne!(
        witness["linker_trace"], changed["linker_trace"],
        "fresh witness did not invoke the actual linker: {observed}"
    );
    assert!(
        all_fresh(&changed, false),
        "same-path linker replacement reused old output: {observed}"
    );
    assert_eq!(
        changed["program_stdout"],
        json!(b"2\n"),
        "changed linker was not used: {observed}"
    );
    assert!(
        all_fresh(&rewarm, true),
        "unchanged replacement must reuse: {observed}"
    );
    assert_eq!(rewarm["program_stdout"], json!(b"2\n"), "{observed}");
    assert_eq!(
        rewarm["linker_trace"], changed["linker_trace"],
        "{observed}"
    );
    #[cfg(target_os = "macos")]
    {
        let denied = &access_control["denied"];
        assert_eq!(
            access_control["original_mode"], access_control["denied_mode"],
            "{observed}"
        );
        assert_eq!(denied["linker_sha256"], second_linker_hash, "{observed}");
        assert_eq!(
            denied["success"], false,
            "ACL-denied linker was reused: {observed}"
        );
        assert!(
            !all_fresh(denied, true),
            "denied linker reported Fresh: {observed}"
        );
        assert_eq!(
            access_control["permission_denied"], true,
            "failed build must diagnose denied execution of the original linker: {observed}"
        );
        let recovered = &access_control["recovered"];
        assert_eq!(recovered["success"], true, "{observed}");
        assert_eq!(recovered["program_stdout"], json!(b"2\n"), "{observed}");
        assert!(all_fresh(&access_control["rewarm"], true), "{observed}");
        assert_eq!(
            access_control["rewarm"]["linker_trace"], recovered["linker_trace"],
            "{observed}"
        );
    }
}

#[test]
fn metadata_check_preserves_success_when_configured_linker_is_unavailable() {
    let base = std::env::current_dir()
        .unwrap()
        .join(".ubd/native-cache-reuse.noindex");
    fs::create_dir_all(&base).unwrap();
    let world = tempfile::Builder::new()
        .prefix("unused-linker")
        .tempdir_in(base)
        .unwrap()
        .keep();
    for path in [
        "evidence",
        "home",
        "default/src",
        "missing/src",
        "missing/.cargo",
    ] {
        fs::create_dir_all(world.join(path)).unwrap();
    }
    let missing = world.join("absent-linker");
    fs::write(
        world.join("missing/.cargo/config.toml"),
        format!(
            "[target.'cfg(all())']\nlinker={}\n",
            serde_json::to_string(&missing).unwrap()
        ),
    )
    .unwrap();
    let mut facts = Vec::new();
    for name in ["default", "missing"] {
        let project = world.join(name);
        let target = world.join(format!("{name}-target"));
        fs::write(project.join("Cargo.toml"), "[package]\nname='cache_metadata'\nversion='0.0.0'\nedition='2021'\n[workspace]\n[profile.dev]\ndebug=0\nincremental=false\n").unwrap();
        fs::write(project.join("src/lib.rs"), "pub fn value() -> u32 { 7 }\n").unwrap();
        for stage in ["cold", "warm"] {
            let label = format!("{name}-{stage}");
            let output = record(
                command(&project, &world, &target).args([
                    "--unverified",
                    "check",
                    "--offline",
                    "-vv",
                    "-j1",
                    "--message-format=json",
                ]),
                &world,
                &label,
            );
            facts.push(json!({"name":name,"stage":stage,"success":output.status.success(),"artifacts":artifacts(&output)}));
        }
    }
    fs::write(
        world.join("observed.json"),
        serde_json::to_vec_pretty(&facts).unwrap(),
    )
    .unwrap();
    assert!(
        !missing.exists(),
        "fixture unexpectedly created a linker: {}",
        world.display()
    );
    for fact in &facts {
        assert_eq!(
            fact["success"],
            true,
            "world={} facts={facts:?}",
            world.display()
        );
        let rows = fact["artifacts"].as_array().unwrap();
        assert_eq!(rows.len(), 1, "world={} facts={facts:?}", world.display());
        let expected_fresh = fact["name"] == "default" && fact["stage"] == "warm";
        assert_eq!(
            rows[0]["fresh"],
            expected_fresh,
            "world={} facts={facts:?}",
            world.display()
        );
    }
}

#[derive(Clone, Copy)]
enum DefaultLinkerChange {
    Replace,
    Shadow,
}

#[expect(
    clippy::disallowed_methods,
    reason = "the fixture captures the original PATH once and adds its genuine default linker tools without changing process environment"
)]
fn default_linker_search_path(shadow: &Path, initial: &Path) -> OsString {
    let original = std::env::var_os("PATH").unwrap_or_default();
    std::env::join_paths(
        [shadow.to_owned(), initial.to_owned()]
            .into_iter()
            .chain(std::env::split_paths(&original)),
    )
    .expect("fixture tool directories form a native PATH")
}

fn default_linker_objects(world: &Path) -> [PathBuf; 2] {
    let objects = [world.join("objects/one.o"), world.join("objects/two.o")];
    for (index, (name, object)) in ["one", "two"].into_iter().zip(&objects).enumerate() {
        let project = world.join(format!("object-{name}"));
        fs::write(project.join("Cargo.toml"), format!("[package]\nname='default_linker_object_{name}'\nversion='0.0.0'\nedition='2021'\n[workspace]\n[profile.dev]\npanic='abort'\ndebug=0\nincremental=false\ncodegen-units=1\n")).unwrap();
        fs::write(project.join("src/lib.rs"), format!("#![no_std]\n#[no_mangle]\npub extern \"C\" fn linker_fixture_value() -> u32 {{ {} }}\n", index+1)).unwrap();
        let output = record(
            command(
                &project,
                world,
                &world.join(format!("object-{name}-target")),
            )
            .args([
                "--unverified",
                "rustc",
                "--lib",
                "--offline",
                "-j1",
                "--message-format=json",
                "--",
            ])
            .arg(format!("--emit=obj={}", object.display())),
            world,
            &format!("object-{name}"),
        );
        assert!(
            output.status.success() && object.is_file(),
            "default-linker fixture object setup failed: world={} object={name}",
            world.display()
        );
    }
    objects
}

fn write_default_linker_wrapper(world: &Path, name: &str, driver: &Path, objects: &[PathBuf; 2]) {
    let project = world.join(format!("{name}-wrapper"));
    fs::write(project.join("Cargo.toml"), format!("[package]\nname='default_{name}_wrapper'\nversion='0.0.0'\nedition='2021'\n[workspace]\n[features]\ntwo=[]\n[[bin]]\nname='cc'\npath='src/main.rs'\n[profile.dev]\ndebug=0\nincremental=false\n")).unwrap();
    fs::write(
        project.join("src/main.rs"),
        format!(
            r#"
use std::io::Write;
use std::os::unix::process::CommandExt;
fn main() {{
    let object = if cfg!(feature="two") {{ {two:?} }} else {{ {one:?} }};
    let args = std::env::args_os().skip(1).collect::<Vec<_>>();
    let mut trace = std::fs::OpenOptions::new().append(true).open({trace:?}).unwrap();
    writeln!(trace, "name={name} object={{object}} executable={{:?}} args={{args:?}}", std::env::current_exe().unwrap()).unwrap();
    trace.flush().unwrap();
    let error = std::process::Command::new({driver:?}).args(args).arg(object)
        .env_remove("CARGO_MAKEFLAGS").env_remove("MAKEFLAGS").env_remove("MFLAGS")
        .env_remove("CARGO_JOBSERVER_HANDOFF").exec();
    panic!("original native linker driver could not execute: {{error}}");
}}
"#,
            one = objects[0],
            two = objects[1],
            trace = world.join("control/linker.trace"),
        ),
    )
    .unwrap();
}

fn default_linker_mutation(change: DefaultLinkerChange) {
    let label = match change {
        DefaultLinkerChange::Replace => "default-replace",
        DefaultLinkerChange::Shadow => "default-shadow",
    };
    let base = std::env::current_dir()
        .unwrap()
        .join(".ubd/native-cache-reuse.noindex");
    fs::create_dir_all(&base).unwrap();
    let world = tempfile::Builder::new()
        .prefix(label)
        .tempdir_in(base)
        .unwrap()
        .keep();
    // Every source, tool directory and output root exists before consumer cold
    // compilation. The shadow target's actual `cc` leaf remains absent.
    for path in [
        "app/src",
        "app/.cargo",
        "initial-wrapper/src",
        "shadow-wrapper/src",
        "object-one/src",
        "object-two/src",
        "objects",
        "control",
        "home",
        "initial-target/debug",
        "shadow-target/debug",
        "object-one-target",
        "object-two-target",
        "app-target",
        "witness-target",
        "evidence",
    ] {
        fs::create_dir_all(world.join(path)).unwrap();
    }
    fs::write(world.join("control/linker.trace"), []).unwrap();
    let driver = linker_driver();
    let objects = default_linker_objects(&world);
    for name in ["initial", "shadow"] {
        write_default_linker_wrapper(&world, name, &driver, &objects);
    }
    let initial_project = world.join("initial-wrapper");
    let initial_target = world.join("initial-target");
    // These tool builds retain the test process's original PATH. Only consumer
    // commands receive the fixture PATH, so building `cc` cannot recurse into it.
    let first_wrapper = record(
        &mut build_command(&initial_project, &world, &initial_target),
        &world,
        "initial-wrapper-one",
    );
    assert!(
        first_wrapper.status.success(),
        "default driver setup failed: world={}",
        world.display()
    );
    let initial_linker = executable(&first_wrapper, "cc");
    let shadow_linker = world.join("shadow-target/debug/cc");
    assert_eq!(initial_linker, initial_target.join("debug/cc"));
    assert!(
        fs::symlink_metadata(&shadow_linker)
            .is_err_and(|error| error.kind() == std::io::ErrorKind::NotFound),
        "shadow candidate must initially be absent: world={}",
        world.display()
    );
    let initial_linker_hash = digest(&initial_linker);
    let search_path = default_linker_search_path(
        shadow_linker.parent().unwrap(),
        initial_linker.parent().unwrap(),
    );
    let app = world.join("app");
    let target = world.join("app-target");
    fs::write(app.join("Cargo.toml"), "[package]\nname='linker_consumer'\nversion='0.0.0'\nedition='2021'\n[workspace]\n[profile.dev]\ndebug=0\nincremental=false\n").unwrap();
    fs::write(app.join("src/main.rs"), "extern \"C\" { fn linker_fixture_value() -> u32; }\nfn main() { println!(\"{}\", unsafe { linker_fixture_value() }); }\n").unwrap();
    // No linker config or caller linker flag selects these default tools.
    fs::write(app.join(".cargo/config.toml"), "[build]\n").unwrap();
    let lock = record(
        command(&app, &world, &target)
            .args(["generate-lockfile", "--offline"])
            .env("PATH", &search_path),
        &world,
        "app-lock",
    );
    assert!(lock.status.success(), "world={}", world.display());
    let probe = command(&app, &world, &target);
    let mut tools = vec![
        json!({"role":"targo","path":probe.get_program(),"sha256":digest(Path::new(probe.get_program()))}),
    ];
    for name in ["RUSTC", "RUSTDOC"] {
        let path = probe
            .get_envs()
            .find(|(key, _)| *key == name)
            .and_then(|(_, value)| value);
        if name == "RUSTC" {
            assert!(path.is_some(), "explicit original compiler tool");
        }
        // No fixture invokes rustdoc. Bookend it when supplied, just as the
        // build-only command preserves it, without inventing a tool identity.
        if let Some(path) = path {
            tools.push(json!({"role":name,"path":path,"sha256":digest(Path::new(path))}));
        }
    }
    tools.push(json!({"role":"original-driver","path":driver,"sha256":digest(&driver)}));
    let wrapper_sources = ["initial", "shadow"].map(|name| {
        json!({
            "name":name,"manifest_sha256":digest(&world.join(format!("{name}-wrapper/Cargo.toml"))),
            "source_sha256":digest(&world.join(format!("{name}-wrapper/src/main.rs"))),
        })
    });
    fs::write(
        world.join("evidence/inputs.json"),
        serde_json::to_vec_pretty(&json!({
            "tools":tools,"search_path":search_path,"shadow_initially_absent":shadow_linker,
            "initial_linker":initial_linker,"initial_linker_sha256":initial_linker_hash,
            "objects":objects.iter().map(|path| json!({"path":path,"sha256":digest(path)})).collect::<Vec<_>>(),
            "wrapper_sources":wrapper_sources,
        })).unwrap(),
    ).unwrap();
    let cold = app_stage_on_path(
        &app,
        &world,
        &target,
        &initial_linker,
        "cold",
        Some(&search_path),
    );
    let trace = String::from_utf8(fs::read(world.join("control/linker.trace")).unwrap()).unwrap();
    // Establish this compiler's actual default profile before a cache assertion.
    // A paired absolute linker or other non-PATH profile is a fixture setup
    // refusal, never evidence of false Fresh.
    assert!(
        cold["success"] == true
            && cold["program_success"] == true
            && cold["program_stdout"] == json!(b"1\n")
            && trace.contains("name=initial ")
            && trace.contains(objects[0].to_str().unwrap()),
        "fixture profile did not execute the original PATH cc: world={}",
        world.display()
    );
    let warm = app_stage_on_path(
        &app,
        &world,
        &target,
        &initial_linker,
        "warm",
        Some(&search_path),
    );
    let (replacement, expected_linker) = match change {
        DefaultLinkerChange::Replace => (
            record(
                build_command(&initial_project, &world, &initial_target)
                    .args(["--features", "two"]),
                &world,
                "initial-wrapper-two",
            ),
            initial_linker.clone(),
        ),
        DefaultLinkerChange::Shadow => (
            record(
                build_command(
                    &world.join("shadow-wrapper"),
                    &world,
                    &world.join("shadow-target"),
                )
                .args(["--features", "two"]),
                &world,
                "shadow-wrapper-two",
            ),
            shadow_linker.clone(),
        ),
    };
    assert!(
        replacement.status.success(),
        "replacement setup failed: world={}",
        world.display()
    );
    assert_eq!(
        executable(&replacement, "cc"),
        expected_linker,
        "world={}",
        world.display()
    );
    let initial_after_hash = digest(&initial_linker);
    let changed = app_stage_on_path(
        &app,
        &world,
        &target,
        &expected_linker,
        "changed",
        Some(&search_path),
    );
    let rewarm = app_stage_on_path(
        &app,
        &world,
        &target,
        &expected_linker,
        "rewarm",
        Some(&search_path),
    );
    // Independent target proves the actual new default selection produces 2.
    // Never edit the warmed target or its old fingerprints after a failure.
    let witness = app_stage_on_path(
        &app,
        &world,
        &world.join("witness-target"),
        &expected_linker,
        "witness",
        Some(&search_path),
    );
    let observed = json!({
        "world":world,"case":label,"search_path":search_path,
        "initial_linker":initial_linker,"initial_linker_before_sha256":initial_linker_hash,
        "initial_linker_after_sha256":initial_after_hash,"expected_linker":expected_linker,
        "expected_linker_sha256":digest(&expected_linker),
        "cold":cold,"warm":warm,"changed":changed,"rewarm":rewarm,"witness":witness,
    });
    fs::write(
        world.join("observed.json"),
        serde_json::to_vec_pretty(&observed).unwrap(),
    )
    .unwrap();
    match change {
        DefaultLinkerChange::Replace => assert_ne!(
            initial_linker_hash,
            initial_after_hash,
            "world={}",
            world.display()
        ),
        DefaultLinkerChange::Shadow => assert_eq!(
            initial_linker_hash,
            initial_after_hash,
            "old selected tool changed: world={}",
            world.display()
        ),
    }
    for stage in [&cold, &warm, &changed, &rewarm, &witness] {
        assert_eq!(
            stage["success"],
            true,
            "world={} compile failed",
            world.display()
        );
        assert_eq!(
            stage["program_success"],
            true,
            "world={} program failed",
            world.display()
        );
        for key in [
            "source_sha256",
            "manifest_sha256",
            "config_sha256",
            "lock_sha256",
            "args",
            "search_path",
        ] {
            assert_eq!(
                cold[key],
                stage[key],
                "app input {key} changed: world={}",
                world.display()
            );
        }
    }
    assert!(
        all_fresh(&cold, false) && all_fresh(&warm, true),
        "cold/warm control failed: world={}",
        world.display()
    );
    assert_eq!(
        cold["linker_trace"],
        warm["linker_trace"],
        "warm invoked linker: world={}",
        world.display()
    );
    for stage in [&cold, &warm] {
        for name in [
            "bin-linker_consumer",
            "bin-linker_consumer.json",
            "dep-bin-linker_consumer",
            "outputs-bin-linker_consumer.json",
        ] {
            assert!(
                stage["cache"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(
                        |record| record["path"]
                            .as_str()
                            .is_some_and(|path| Path::new(path).file_name()
                                == Some(std::ffi::OsStr::new(name)))
                    ),
                "missing {name}: world={}",
                world.display()
            );
        }
    }
    assert!(
        all_fresh(&witness, false),
        "fresh witness did not compile: world={}",
        world.display()
    );
    assert_eq!(
        witness["program_stdout"],
        json!(b"2\n"),
        "new default linker witness failed: world={}",
        world.display()
    );
    assert_ne!(
        witness["linker_trace"],
        rewarm["linker_trace"],
        "fresh witness did not invoke actual linker: world={}",
        world.display()
    );
    let witness_trace =
        String::from_utf8(fs::read(world.join("control/linker.trace")).unwrap()).unwrap();
    let expected_name = match change {
        DefaultLinkerChange::Replace => "initial",
        DefaultLinkerChange::Shadow => "shadow",
    };
    assert!(
        witness_trace.contains(&format!(
            "name={expected_name} object={}",
            objects[1].display()
        )),
        "witness did not select replacement tool: world={}",
        world.display()
    );
    assert!(
        all_fresh(&changed, false),
        "default linker change reused old output: world={}",
        world.display()
    );
    assert_eq!(
        changed["program_stdout"],
        json!(b"2\n"),
        "old program reused: world={}",
        world.display()
    );
    assert!(
        all_fresh(&rewarm, true),
        "unchanged replacement did not reuse: world={}",
        world.display()
    );
    assert_eq!(
        rewarm["program_stdout"],
        json!(b"2\n"),
        "world={}",
        world.display()
    );
    assert_eq!(
        rewarm["linker_trace"],
        changed["linker_trace"],
        "rewarm invoked linker: world={}",
        world.display()
    );
}

#[test]
fn same_path_default_linker_replacement_invalidates_native_reuse() {
    default_linker_mutation(DefaultLinkerChange::Replace);
}

#[test]
fn default_linker_path_shadow_invalidates_native_reuse() {
    default_linker_mutation(DefaultLinkerChange::Shadow);
}

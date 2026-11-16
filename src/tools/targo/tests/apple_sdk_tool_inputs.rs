//! Native Apple SDK discovery withholds reuse without rejecting compilation.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

#![cfg(target_os = "macos")]

use std::ffi::OsString;
use std::fs;
use std::os::unix::ffi::OsStringExt;
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use serde_json::json;
use trust_fs_observation::tool_lookup::{DEP_INFO_PREFIX, ToolInputs, UNAVAILABLE};

// Use only real system discovery and linker programs, with no helper aliases.
const SYSTEM_PATH: &str = "/usr/bin:/bin:/usr/sbin:/sbin";

fn record(command: &mut Command, world: &Path, label: &str) -> Output {
    let evidence = world.join("evidence");
    fs::write(
        evidence.join(format!("{label}.command.txt")),
        format!("{command:?}\n"),
    )
    .unwrap();
    let result = command.output();
    let status = match &result {
        Ok(output) => json!({
            "success":output.status.success(), "code":output.status.code(),
            "signal":output.status.signal(), "display":output.status.to_string(),
        }),
        Err(error) => json!({"spawn_error":error.to_string()}),
    };
    fs::write(
        evidence.join(format!("{label}.status.json")),
        serde_json::to_vec_pretty(&status).unwrap(),
    )
    .unwrap();
    let output = result.expect("launch recorded actual native command");
    fs::write(evidence.join(format!("{label}.stdout")), &output.stdout).unwrap();
    fs::write(evidence.join(format!("{label}.stderr")), &output.stderr).unwrap();
    output
}

fn terminal(world: &Path, case: &str) -> String {
    let dep_info = fs::read_to_string(world.join(case).join("subject.d")).unwrap();
    let markers: Vec<_> = dep_info
        .lines()
        .filter_map(|line| line.strip_prefix(DEP_INFO_PREFIX))
        .collect();
    assert_eq!(
        markers.len(),
        1,
        "world={} dep-info={dep_info}",
        world.display()
    );
    markers[0].to_owned()
}

#[test]
fn actual_sdk_discovery_withholds_tool_inputs_and_explicit_sdk_preserves_them() {
    let base = std::env::current_dir()
        .unwrap()
        .join(".ubd/native-apple-sdk-inputs.noindex");
    fs::create_dir_all(&base).unwrap();
    let world = tempfile::Builder::new()
        .prefix("sdk-discovery")
        .tempdir_in(base)
        .unwrap()
        .keep();
    eprintln!("retained Apple tool-input world: {}", world.display());
    for directory in ["evidence", "explicit", "discovery"] {
        fs::create_dir(world.join(directory)).unwrap();
    }

    // This real system query selects fixture input DATA. The compiler's second
    // call must independently discover it, without replacing any SDK or helper.
    let sdk_query = record(
        Command::new("/usr/bin/xcrun")
            .args(["--sdk", "macosx", "--show-sdk-path"])
            .env("PATH", SYSTEM_PATH)
            .env_remove("SDKROOT"),
        &world,
        "sdk-query",
    );
    assert!(sdk_query.status.success(), "world={}", world.display());
    let mut sdk_bytes = sdk_query.stdout;
    assert_eq!(
        sdk_bytes.pop(),
        Some(b'\n'),
        "complete SDK path: world={}",
        world.display()
    );
    let sdk = PathBuf::from(OsString::from_vec(sdk_bytes));
    assert!(
        sdk.is_absolute() && sdk != Path::new("/") && sdk.join("SDKSettings.plist").is_file(),
        "real system SDK required: world={} sdk={sdk:?}",
        world.display(),
    );
    assert!(
        sdk.to_str().is_some(),
        "the compiler's explicit SDKROOT interface requires UTF-8"
    );

    let source = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../compiler/rustc_driver_impl/src/tests/tool_inputs_subject.rs");
    assert!(source.is_file(), "maintained original compiler subject");
    let mut version = cargo_test_support::rustc_fixture_command().unwrap();
    let version = record(version.arg("-vV"), &world, "compiler-version");
    assert!(version.status.success(), "world={}", world.display());

    let mut outcomes = Vec::new();
    for (case, explicit) in [("explicit", true), ("discovery", false)] {
        let directory = world.join(case);
        let mut compiler = cargo_test_support::rustc_fixture_command().unwrap();
        compiler
            .current_dir(&world)
            .env("PATH", SYSTEM_PATH)
            .env_remove("SDKROOT")
            .arg(&source)
            .args([
                "--edition=2024",
                "--crate-name=subject",
                "--emit=dep-info,link",
                "-Ztrust-verify=off",
                "-Ztrust-ir-lower=no",
                "-Ztrust-tool-inputs",
                "-Cdebuginfo=0",
                "-Csplit-debuginfo=off",
            ])
            .arg("--out-dir")
            .arg(&directory);
        if explicit {
            compiler.env("SDKROOT", &sdk);
        }
        let compile = record(&mut compiler, &world, &format!("{case}-compile"));
        let run = compile.status.success().then(|| {
            record(
                Command::new(directory.join("subject")).current_dir(&world),
                &world,
                &format!("{case}-run"),
            )
        });
        outcomes.push((case, compile, run));
    }

    // Retain both real outcomes and both actual dep-info files before checking
    // the availability distinction, including the old-producer counterexample.
    for (case, compile, run) in outcomes {
        assert!(
            compile.status.success(),
            "world={} case={case}",
            world.display()
        );
        let run = run.expect("successful compile must run its original produced image");
        assert!(
            run.status.success(),
            "world={} case={case}",
            world.display()
        );
        assert_eq!(run.stdout, b"7\n", "world={} case={case}", world.display());
    }
    let explicit = ToolInputs::decode(terminal(&world, "explicit").as_bytes())
        .expect("actual explicit-root compiler must publish a strict available record");
    assert!(
        !explicit.records().is_empty(),
        "an actual explicit-root native link must not report an empty inventory: world={}",
        world.display(),
    );
    assert_eq!(
        terminal(&world, "discovery"),
        UNAVAILABLE,
        "world={}",
        world.display()
    );
}

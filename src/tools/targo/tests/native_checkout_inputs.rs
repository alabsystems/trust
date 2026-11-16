//! Genuine original native tracked-input reader and maintained landing adapter.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

#[cfg(all(target_os = "macos", target_arch = "aarch64", feature = "all-static"))]
#[test]
#[expect(
    clippy::disallowed_methods,
    reason = "the fixture selects the actual newly built native Targo image before project configuration"
)]
fn checkout_inputs_runtime_and_original_landing_adapter() {
    use std::fs;
    use std::path::Path;
    use std::process::Command;

    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let base = manifest.join(".ubd/native-checkout-inputs.noindex");
    fs::create_dir_all(&base).unwrap();
    let world = tempfile::Builder::new()
        .prefix("checkout-")
        .tempdir_in(base)
        .unwrap()
        .keep();
    let test = manifest
        .join("../../../scripts/tests/native_checkout_test.py")
        .canonicalize()
        .unwrap();
    let builder =
        std::env::var_os("TARGO_NATIVE_CHECKOUT_BUILDER").unwrap_or_else(|| env!("CARGO").into());
    // The native reader's custody contract requires the executable directly
    // inside `<root>/bin` (trust-resource-provenance `open`). Stage the newly
    // built image into that layout; the copy is byte-identical, so the
    // python side's image hash and bookends bind the staged file.
    let staged_root = world.join("root");
    let staged_bin = staged_root.join("bin");
    fs::create_dir_all(&staged_bin).unwrap();
    let staged = staged_bin.join("targo");
    fs::copy(env!("CARGO_BIN_EXE_targo"), &staged).unwrap();
    let mut command = Command::new("python3");
    command
        .arg("-B")
        .arg(&test)
        .arg("--native")
        .arg(&staged)
        .arg(&world)
        .arg(&builder);
    fs::write(
        world.join("command.json"),
        serde_json::to_vec_pretty(&serde_json::json!({
            "program":command.get_program(), "args":command.get_args().collect::<Vec<_>>(),
            "compiler":std::env::var_os("RUSTC"), "builder":builder,
            "scope":"all-static unverified engineering recipe; no package adoption or source-to-binary proof"
        }))
        .unwrap(),
    )
    .unwrap();
    let output = command.output().unwrap();
    fs::write(world.join("stdout"), &output.stdout).unwrap();
    fs::write(world.join("stderr"), &output.stderr).unwrap();
    fs::write(world.join("status"), output.status.to_string()).unwrap();
    assert!(
        output.status.success(),
        "world={} status={}\n{}",
        world.display(),
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    let result: serde_json::Value =
        serde_json::from_slice(&fs::read(world.join("result.json")).unwrap()).unwrap();
    assert_eq!(result["tests"], 5);
    assert_eq!(result["failures"], 0);
    assert_eq!(result["errors"], 0);
    assert_eq!(result["skipped"], 0);
}

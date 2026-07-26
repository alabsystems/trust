use std::ffi::OsString;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

#[cfg(unix)]
use std::os::unix::process::CommandExt as _;

// Trust: `CARGO_BIN_EXE_*` is defined only when cargo BUILDS an integration
// test target. `cargo check` type-checks this file without linking the bins, so
// a compile-time `env!` here made `x.py check` fail on a target it never runs.
// Resolve through `option_env!` and fail at run time instead, where the variable
// is always present.
const CARGO_TIPPY_BIN: &str = match option_env!("CARGO_BIN_EXE_cargo-clippy") {
    Some(path) => path,
    None => "CARGO_BIN_EXE_cargo-clippy was unset: this test target was checked, not built",
};
const TIPPY_DRIVER_BIN: &str = match option_env!("CARGO_BIN_EXE_clippy-driver") {
    Some(path) => path,
    None => "CARGO_BIN_EXE_clippy-driver was unset: this test target was checked, not built",
};

static FIXTURE_PARENT_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

fn lock_fixture_parent() -> std::sync::MutexGuard<'static, ()> {
    // Hard-link fixtures must share the Cargo-built executable's directory.
    // Branded Tippy watches that ancestor for mutations, so serialize fixture
    // changes instead of making parallel tests look like a toolchain attack.
    FIXTURE_PARENT_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

fn unique_temp_dir(label: &str) -> std::path::PathBuf {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    // Several boundary probes deliberately use hard links so the OS reports a
    // public Tippy executable name for the exact Cargo-built binary. Hard links
    // cannot cross filesystems: Docker keeps `/checkout/obj` on a separate
    // volume from `/tmp`, and Windows TEMP may be on another drive. Keep every
    // fixture beside the Cargo-built executable so these tests exercise the
    // identity boundary instead of failing early with EXDEV.
    std::path::Path::new(CARGO_TIPPY_BIN)
        .parent()
        .expect("Cargo-built Tippy frontend has a parent directory")
        .join(format!(".tippy-{label}-{}-{nonce}", std::process::id()))
}

fn encode_tippy_compiler_args(args: &[&str]) -> String {
    let mut encoded = "tippy-args-v2;no-deps=0;".to_string();
    for arg in args {
        encoded.push_str(&format!("{}:", arg.len()));
        encoded.push_str(arg);
    }
    encoded
}

#[cfg(unix)]
fn write_executable(path: &std::path::Path, body: &[u8]) {
    use std::os::unix::fs::PermissionsExt as _;

    std::fs::write(path, body).expect("write executable fixture");
    let mut permissions = std::fs::metadata(path)
        .expect("executable fixture metadata")
        .permissions();
    permissions.set_mode(0o700);
    std::fs::set_permissions(path, permissions).expect("make fixture executable");
}

#[cfg(unix)]
fn non_unicode_os_string() -> OsString {
    use std::os::unix::ffi::OsStringExt as _;

    OsString::from_vec(vec![0xff])
}

#[cfg(windows)]
fn non_unicode_os_string() -> OsString {
    use std::os::windows::ffi::OsStringExt as _;

    // An unpaired UTF-16 surrogate cannot be represented by `String`, but is
    // a valid Windows process/environment boundary value.
    OsString::from_wide(&[0xd800])
}

#[test]
fn frontend_reports_non_unicode_argv_without_panicking() {
    let output = Command::new(CARGO_TIPPY_BIN)
        .arg(non_unicode_os_string())
        .output()
        .expect("run cargo-clippy boundary fixture");
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(!output.status.success());
    assert!(stderr.contains("argument 1 is not valid Unicode"), "{stderr}");
    assert!(!stderr.contains("panicked at"), "{stderr}");
}

#[test]
fn driver_rejects_non_unicode_legacy_argument_channel() {
    let output = Command::new(TIPPY_DRIVER_BIN)
        .arg("definitely-missing-tippy-boundary-input.rs")
        .env_remove("TIPPY_ENCODED_ARGS")
        .env("CLIPPY_ARGS", non_unicode_os_string())
        .output()
        .expect("run clippy-driver boundary fixture");
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(!output.status.success());
    assert!(stderr.contains("CLIPPY_ARGS is not valid UTF-8"), "{stderr}");
    assert!(!stderr.contains("panicked at"), "{stderr}");
}

#[test]
fn decoded_compiler_args_drive_policy_and_reach_the_same_rustc_invocation() {
    let _fixture_parent_guard = lock_fixture_parent();

    let printed = Command::new(TIPPY_DRIVER_BIN)
        .arg("--crate-name=tippy_internal_print")
        .env("TIPPY_ENCODED_ARGS", encode_tippy_compiler_args(&["--print=cfg"]))
        .env_remove("CLIPPY_ARGS")
        .output()
        .expect("run decoded compiler info query");
    let printed_stdout = String::from_utf8_lossy(&printed.stdout);
    let printed_stderr = String::from_utf8_lossy(&printed.stderr);
    assert!(
        printed.status.success(),
        "decoded --print did not execute:\n{printed_stdout}\n{printed_stderr}"
    );
    assert!(printed_stdout.contains("target_arch="), "{printed_stdout}");

    let root = unique_temp_dir("decoded-compiler-args");
    std::fs::create_dir(&root).expect("create decoded-argument fixture");
    let callbacks_off_source = root.join("callbacks_off.rs");
    std::fs::write(
        &callbacks_off_source,
        "#[cfg(clippy)] compile_error!(\"internal cap-lints did not disable Clippy callbacks\");\n\
         #[cfg(not(tippy_internal_forwarded))] compile_error!(\"decoded cfg was not forwarded\");\n\
         pub fn callbacks_off() {}\n",
    )
    .expect("write callbacks-off fixture");
    let mut callbacks_off = Command::new(TIPPY_DRIVER_BIN);
    callbacks_off.args(["--crate-name=callbacks_off", "--crate-type=lib", "--emit=metadata"]);
    if let Some(sysroot) = option_env!("TEST_SYSROOT") {
        callbacks_off.args(["--sysroot", sysroot]);
    }
    let callbacks_off = callbacks_off
        .arg("-o")
        .arg(root.join("callbacks_off.rmeta"))
        .arg(&callbacks_off_source)
        .env(
            "TIPPY_ENCODED_ARGS",
            encode_tippy_compiler_args(&["--cap-lints=allow", "--cfg=tippy_internal_forwarded"]),
        )
        .env_remove("CLIPPY_ARGS")
        .output()
        .expect("run decoded cap-lints compilation");
    assert!(
        callbacks_off.status.success(),
        "{}",
        String::from_utf8_lossy(&callbacks_off.stderr)
    );

    let callbacks_on_source = root.join("callbacks_on.rs");
    std::fs::write(
        &callbacks_on_source,
        "#[cfg(not(clippy))] compile_error!(\"decoded force-warn did not retain Clippy callbacks\");\n\
         #[cfg(not(tippy_force_forwarded))] compile_error!(\"decoded force-warn argv was omitted\");\n\
         pub fn callbacks_on() {}\n",
    )
    .expect("write callbacks-on fixture");
    let mut callbacks_on = Command::new(TIPPY_DRIVER_BIN);
    callbacks_on.args([
        "--crate-name=callbacks_on",
        "--crate-type=lib",
        "--emit=metadata",
        "--cap-lints=allow",
    ]);
    if let Some(sysroot) = option_env!("TEST_SYSROOT") {
        callbacks_on.args(["--sysroot", sysroot]);
    }
    let callbacks_on = callbacks_on
        .arg("-o")
        .arg(root.join("callbacks_on.rmeta"))
        .arg(&callbacks_on_source)
        .env(
            "TIPPY_ENCODED_ARGS",
            encode_tippy_compiler_args(&["--force-warn=clippy::all", "--cfg=tippy_force_forwarded"]),
        )
        .env_remove("CLIPPY_ARGS")
        .output()
        .expect("run decoded force-warn compilation");
    assert!(
        callbacks_on.status.success(),
        "{}",
        String::from_utf8_lossy(&callbacks_on.stderr)
    );
    std::fs::remove_dir_all(root).expect("remove decoded-argument fixture");
}

#[test]
fn branded_hard_link_without_required_siblings_fails_closed() {
    let _fixture_parent_guard = lock_fixture_parent();

    let root = unique_temp_dir("missing-branded-siblings");
    std::fs::create_dir(&root).expect("create missing-siblings fixture");
    let public_tippy = root.join(format!("tippy{}", std::env::consts::EXE_SUFFIX));
    std::fs::hard_link(CARGO_TIPPY_BIN, &public_tippy)
        .expect("install hard-linked public Tippy fixture");

    let output = Command::new(&public_tippy)
        .env("CARGO", root.join("ambient-cargo-must-not-run"))
        .arg("--workspace")
        .output()
        .expect("run public Tippy missing-siblings fixture");
    std::fs::remove_dir_all(root).expect("remove missing-siblings fixture");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success());
    assert!(stderr.contains("required sibling `targo`"), "{stderr}");
    assert!(stderr.contains("repair or reinstall"), "{stderr}");
    assert!(!stderr.contains("ambient-cargo-must-not-run"), "{stderr}");
}

#[cfg(unix)]
#[test]
fn raw_argv0_cannot_promote_the_development_frontend_to_branded_mode() {
    let _fixture_parent_guard = lock_fixture_parent();

    let root = unique_temp_dir("forged-argv0");
    std::fs::create_dir(&root).expect("create forged-argv0 fixture");
    let selected_cargo = root.join("selected-cargo");
    write_executable(&selected_cargo, b"#!/bin/sh\nexit 42\n");

    let mut command = Command::new(CARGO_TIPPY_BIN);
    command.arg0("tippy").env("CARGO", &selected_cargo).arg("--workspace");
    let output = command.output().expect("run forged-argv0 frontend fixture");
    std::fs::remove_dir_all(root).expect("remove forged-argv0 fixture");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success());
    assert_ne!(output.status.code(), Some(42));
    assert!(
        stderr.contains("conflicts with the running Tippy executable"),
        "{stderr}"
    );
}

#[cfg(unix)]
#[test]
fn raw_symlink_directory_cannot_relocate_the_selected_toolchain() {
    use std::os::unix::fs::symlink;

    let _fixture_parent_guard = lock_fixture_parent();

    let root = unique_temp_dir("symlink-toolchain-relocation");
    let selected_bin = root.join("selected/bin");
    let attacker_bin = root.join("attacker/bin");
    std::fs::create_dir_all(&selected_bin).expect("create selected bin directory");
    std::fs::create_dir_all(&attacker_bin).expect("create attacker bin directory");

    let selected_tippy = selected_bin.join("tippy");
    std::fs::hard_link(CARGO_TIPPY_BIN, &selected_tippy)
        .expect("install hard-linked public Tippy fixture");
    write_executable(&selected_bin.join("targo"), b"#!/bin/sh\nexit 42\n");
    write_executable(&selected_bin.join("tippy-driver"), b"#!/bin/sh\nexit 70\n");
    write_executable(&selected_bin.join("trustc"), b"#!/bin/sh\nexit 71\n");

    let forged_argv0 = attacker_bin.join("tippy");
    symlink(&selected_tippy, &forged_argv0).expect("create forged argv[0] symlink");
    write_executable(&attacker_bin.join("targo"), b"#!/bin/sh\nexit 43\n");
    write_executable(&attacker_bin.join("tippy-driver"), b"#!/bin/sh\nexit 72\n");
    write_executable(&attacker_bin.join("trustc"), b"#!/bin/sh\nexit 73\n");

    // Execute the forged path itself. Merely overriding argv[0] would not test
    // whether this platform's current_exe implementation reports the symlink
    // or its target.
    let output = Command::new(&forged_argv0)
        .arg("--workspace")
        .output()
        .expect("run symlink relocation fixture");
    std::fs::remove_dir_all(root).expect("remove symlink relocation fixture");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_ne!(
        output.status.code(),
        Some(43),
        "the forged symlink directory selected attacker-controlled siblings: {stderr}"
    );
    assert!(
        output.status.code() == Some(42) || stderr.contains("cannot authenticate branded Tippy invocation"),
        "the resolved toolchain must run or the symlink path must fail closed: {stderr}"
    );
}

#[cfg(unix)]
#[test]
fn branded_frontend_rejects_targo_rewritten_during_child_lifetime() {
    let _fixture_parent_guard = lock_fixture_parent();

    let root = unique_temp_dir("targo-in-place-rewrite");
    let bin = root.join("toolchain/bin");
    std::fs::create_dir_all(&bin).expect("create selected bin directory");

    let tippy = bin.join("tippy");
    std::fs::hard_link(CARGO_TIPPY_BIN, &tippy).expect("install hard-linked public Tippy fixture");
    let targo = bin.join("targo");
    write_executable(&targo, b"#!/bin/sh\nprintf '#!/bin/sh\\nexit 0\\n' > \"$0\"\nexit 0\n");
    write_executable(&bin.join("tippy-driver"), b"#!/bin/sh\nexit 70\n");
    write_executable(&bin.join("trustc"), b"#!/bin/sh\nexit 71\n");

    let output = Command::new(&tippy)
        .arg("--workspace")
        .output()
        .expect("run public Tippy executable-rewrite fixture");
    std::fs::remove_dir_all(root).expect("remove executable-rewrite fixture");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "a rewritten Targo executable was accepted: {stderr}"
    );
    assert!(
        stderr.contains("targo identity changed while Targo was running"),
        "{stderr}"
    );
}

#[cfg(unix)]
#[test]
fn raw_driver_symlink_directory_cannot_relocate_the_selected_sysroot() {
    use std::os::unix::fs::symlink;

    let _fixture_parent_guard = lock_fixture_parent();

    let root = unique_temp_dir("driver-symlink-toolchain-relocation");
    let selected_bin = root.join("selected/bin");
    let attacker_bin = root.join("attacker/bin");
    std::fs::create_dir_all(&selected_bin).expect("create selected driver bin directory");
    std::fs::create_dir_all(&attacker_bin).expect("create attacker driver bin directory");

    let selected_driver = selected_bin.join("tippy-driver");
    std::fs::hard_link(TIPPY_DRIVER_BIN, &selected_driver)
        .expect("install hard-linked public driver fixture");
    let forged_driver = attacker_bin.join("tippy-driver");
    symlink(&selected_driver, &forged_driver).expect("create forged driver symlink");

    let output = Command::new(&forged_driver)
        .arg("--print=sysroot")
        .output()
        .expect("run driver symlink relocation fixture");
    std::fs::remove_dir_all(root).expect("remove driver symlink relocation fixture");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let selected_sysroot = selected_bin.parent().expect("selected sysroot").display().to_string();
    let attacker_sysroot = attacker_bin.parent().expect("attacker sysroot").display().to_string();
    assert!(
        !stdout.lines().any(|line| line == attacker_sysroot),
        "{stdout}\n{stderr}"
    );
    assert!(
        stdout.lines().any(|line| line == selected_sysroot)
            || stderr.contains("cannot authenticate the running Tippy driver executable"),
        "the resolved driver sysroot must win or the symlink path must fail closed: {stdout}\n{stderr}"
    );
}

#[cfg(unix)]
#[test]
fn tippy_driver_is_vanilla_and_has_no_trust_evidence_escape_route() {
    let _fixture_parent_guard = lock_fixture_parent();

    fn assert_cfg_policy(output: std::process::Output, label: &str, trust_verify: bool) {
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "{label}:\n{stdout}\n{stderr}");
        assert_eq!(
            stdout.lines().any(|line| line == "trust_verify"),
            trust_verify,
            "{label} reported the wrong compiler policy:\n{stdout}\n{stderr}"
        );
    }

    let unbranded_normal = Command::new(TIPPY_DRIVER_BIN)
        .arg("--print=cfg")
        .env_remove("TRUST_NO_VERIFY")
        .output()
        .expect("run unbranded normal lint driver cfg query");
    let unbranded_override = Command::new(TIPPY_DRIVER_BIN)
        .args(["-Ztrust-verify=on", "--print=cfg"])
        .env_remove("TRUST_NO_VERIFY")
        .output()
        .expect("run unbranded normal lint driver override probe");

    let root = unique_temp_dir("driver-verification-off-switch");
    let bin = root.join("toolchain/bin");
    std::fs::create_dir_all(&bin).expect("create selected driver bin directory");
    let driver = bin.join("tippy-driver");
    std::fs::hard_link(TIPPY_DRIVER_BIN, &driver)
        .expect("install hard-linked public driver fixture");
    let trustc = bin.join("trustc");
    write_executable(&trustc, b"#!/bin/sh\nexit 0\n");

    let joined_args = root.join("joined.args");
    std::fs::write(&joined_args, "-Ztrust-verify=on\n--print=cfg\n")
        .expect("write joined response-file arguments");
    let split_args = root.join("split.args");
    std::fs::write(&split_args, "-Z\ntrust-verify=on\n--print\ncfg\n")
        .expect("write split response-file arguments");

    let normal = Command::new(&driver)
        .arg("--print=cfg")
        .env_remove("TRUST_NO_VERIFY")
        .output()
        .expect("run branded normal lint driver cfg query");
    let normal_override = Command::new(&driver)
        .args(["-Ztrust-verify=on", "--print=cfg"])
        .env_remove("TRUST_NO_VERIFY")
        .output()
        .expect("run branded normal lint driver override probe");
    let wrapped_override = Command::new(&driver)
        .arg(&trustc)
        .args(["-Ztrust-verify=on", "--print=cfg"])
        .env_remove("TRUST_NO_VERIFY")
        .output()
        .expect("run wrapped normal lint driver override probe");
    let joined_response_override = Command::new(&driver)
        .arg(format!("@{}", joined_args.display()))
        .env_remove("TRUST_NO_VERIFY")
        .output()
        .expect("run joined response-file override probe");
    let split_response_override = Command::new(&driver)
        .arg(format!("@{}", split_args.display()))
        .env_remove("TRUST_NO_VERIFY")
        .output()
        .expect("run split response-file override probe");
    let consumed_double_dash = Command::new(&driver)
        .args(["--crate-name", "--", "-Ztrust-verify=on", "--print=cfg"])
        .env_remove("TRUST_NO_VERIFY")
        .output()
        .expect("run consumed double-dash argument-boundary probe");
    let rejected_passthrough = Command::new(&driver)
        .args(["--trustc", "-Ztrust-verify=on", "--print=cfg"])
        .env_remove("TRUST_NO_VERIFY")
        .output()
        .expect("run rejected raw trustc cfg query");

    assert_cfg_policy(unbranded_normal, "unbranded normal route", false);
    assert_cfg_policy(unbranded_override, "unbranded false override", false);
    assert_cfg_policy(normal, "branded normal route", false);
    assert_cfg_policy(normal_override, "branded false override", false);
    assert_cfg_policy(wrapped_override, "wrapped false override", false);
    assert_cfg_policy(joined_response_override, "joined response-file false override", false);
    assert_cfg_policy(split_response_override, "split response-file false override", false);
    assert_cfg_policy(
        consumed_double_dash,
        "double dash consumed as the crate-name value",
        false,
    );
    assert!(!rejected_passthrough.status.success());
    let rejected_stderr = String::from_utf8_lossy(&rejected_passthrough.stderr);
    assert!(
        rejected_stderr.contains("no longer exposes raw `--trustc` passthrough"),
        "unexpected direct-passthrough rejection: {rejected_stderr}"
    );

    for forbidden_control in [
        "-Ztrust-ir-lower",
        "-Ztrust-dump=ir:/tmp/tippy-must-not-publish-ir",
        "-Ztrust-verify-session=tippy-must-not-prove",
        "-Ztrust-proof-artifact-root=/tmp/tippy-must-not-publish-proof",
        "-Ztrust-verify-output=json",
        "-Zcodegen-backend=trust-cg",
        "-Zllvm-plugins=/tmp/tippy-must-not-load-plugin",
        "-Cllvm-args=-load=/tmp/tippy-must-not-load-plugin",
        "-Zautodiff=Enable",
        "-Zautodiff-post-passes=default<O2>",
    ] {
        let rejected = Command::new(TIPPY_DRIVER_BIN)
            .args([forbidden_control, "--print=cfg"])
            .env_remove("TRUST_NO_VERIFY")
            .output()
            .expect("run no-evidence Trust-control rejection probe");
        let stderr = String::from_utf8_lossy(&rejected.stderr);
        assert!(
            !rejected.status.success(),
            "Tippy accepted forbidden compiler control {forbidden_control}: {stderr}"
        );
        assert!(stderr.contains("NoTrustEvidence compiler frontend rejects"), "{stderr}");
    }
    for backend_control in [
        "-Zcodegen-backend=trust-cg",
        "-Zllvm-plugins=/tmp/tippy-must-not-load-plugin",
        "-Cllvm-args=-load=/tmp/tippy-must-not-load-plugin",
        "-Zautodiff=Enable",
    ] {
        for early_backend_mode in ["-vV", "-Cpasses=list"] {
            let rejected = Command::new(TIPPY_DRIVER_BIN)
                .args([backend_control, early_backend_mode])
                .env_remove("TRUST_NO_VERIFY")
                .output()
                .expect("run early backend-selection rejection probe");
            let stderr = String::from_utf8_lossy(&rejected.stderr);
            assert!(
                !rejected.status.success(),
                "{early_backend_mode} executed forbidden {backend_control} before rejection: {stderr}"
            );
            assert!(stderr.contains("NoTrustEvidence compiler frontend rejects"), "{stderr}");
        }
    }
    let host_target = Command::new(TIPPY_DRIVER_BIN)
        .args(["-Zunstable-options", "--print=target-spec-json"])
        .env_remove("TRUST_NO_VERIFY")
        .output()
        .expect("export host target specification");
    assert!(
        host_target.status.success(),
        "failed to export target fixture: {}",
        String::from_utf8_lossy(&host_target.stderr)
    );
    let mut proof_backend_target =
        String::from_utf8(host_target.stdout.clone()).expect("target specification is UTF-8 JSON");
    assert!(!proof_backend_target.contains("\"default-codegen-backend\""));
    let closing_brace = proof_backend_target
        .rfind('}')
        .expect("target specification has a root object");
    proof_backend_target.insert_str(closing_brace, ",\n  \"default-codegen-backend\": \"trust-cg\"\n");
    let proof_backend_target_path = root.join("proof-backend-target.json");
    std::fs::write(&proof_backend_target_path, proof_backend_target)
        .expect("write target-default proof-backend fixture");
    let target_rejected = Command::new(TIPPY_DRIVER_BIN)
        .arg("-Zunstable-options")
        .arg("--target")
        .arg(&proof_backend_target_path)
        .arg("--print=cfg")
        .env_remove("TRUST_NO_VERIFY")
        .output()
        .expect("run target-default proof-backend rejection probe");
    let target_stderr = String::from_utf8_lossy(&target_rejected.stderr);
    assert!(!target_rejected.status.success(), "{target_stderr}");
    assert!(
        target_stderr.contains("rejects effective codegen backend `trust-cg`"),
        "{target_stderr}"
    );

    let mut llvm_args_target = String::from_utf8(host_target.stdout.clone())
        .expect("target specification is UTF-8 JSON");
    assert!(!llvm_args_target.contains("\"llvm-args\""));
    let closing_brace = llvm_args_target
        .rfind('}')
        .expect("target specification has a root object");
    llvm_args_target.insert_str(
        closing_brace,
        ",\n  \"llvm-args\": [\"-load=/tmp/tippy-must-not-load-plugin\"]\n",
    );
    let llvm_args_target_path = root.join("llvm-args-target.json");
    std::fs::write(&llvm_args_target_path, llvm_args_target)
        .expect("write target LLVM-argument fixture");
    let target_llvm_args_rejected = Command::new(TIPPY_DRIVER_BIN)
        .arg("-Zunstable-options")
        .arg("--target")
        .arg(&llvm_args_target_path)
        .arg("--print=cfg")
        .env_remove("TRUST_NO_VERIFY")
        .output()
        .expect("run target LLVM-argument rejection probe");
    let target_llvm_args_stderr =
        String::from_utf8_lossy(&target_llvm_args_rejected.stderr);
    assert!(!target_llvm_args_rejected.status.success(), "{target_llvm_args_stderr}");
    assert!(
        target_llvm_args_stderr.contains("rejects LLVM arguments from custom target"),
        "{target_llvm_args_stderr}"
    );
    for early_backend_mode in ["-vV", "-Cpasses=list"] {
        let rejected = Command::new(TIPPY_DRIVER_BIN)
            .arg("-Zunstable-options")
            .arg("--target")
            .arg(&llvm_args_target_path)
            .arg(early_backend_mode)
            .env_remove("TRUST_NO_VERIFY")
            .output()
            .expect("run custom-target LLVM-argument early rejection probe");
        let stderr = String::from_utf8_lossy(&rejected.stderr);
        assert!(!rejected.status.success(), "{early_backend_mode}: {stderr}");
        assert!(
            stderr.contains("rejects LLVM arguments from custom target"),
            "{early_backend_mode}: {stderr}"
        );
    }
    for early_backend_mode in ["-vV", "-Cpasses=list"] {
        let rejected = Command::new(TIPPY_DRIVER_BIN)
            .arg("-Zunstable-options")
            .arg("--target")
            .arg(&proof_backend_target_path)
            .arg(early_backend_mode)
            .env_remove("TRUST_NO_VERIFY")
            .output()
            .expect("run target-default early backend rejection probe");
        let stderr = String::from_utf8_lossy(&rejected.stderr);
        assert!(!rejected.status.success(), "{early_backend_mode}: {stderr}");
        assert!(
            stderr.contains("rejects effective codegen backend `trust-cg`"),
            "{early_backend_mode}: {stderr}"
        );
    }
    for environment_control in ["TCG_NO_DECODE_CHECK", "TRUST_CG_DISABLE_PASSES"] {
        let rejected = Command::new(TIPPY_DRIVER_BIN)
            .arg("--print=cfg")
            .env(environment_control, "1")
            .env_remove("TRUST_NO_VERIFY")
            .output()
            .expect("run no-evidence codegen-environment rejection probe");
        let stderr = String::from_utf8_lossy(&rejected.stderr);
        assert!(!rejected.status.success(), "accepted {environment_control}: {stderr}");
        assert!(stderr.contains("untracked Trust semantic/codegen control"), "{stderr}");
    }

    // A real compilation reaches `ClippyCallbacks::config`, whose MIR and lint
    // mutations make verification semantics unsound. The typed driver boundary
    // must already have disabled verification before those callbacks run.
    let source = root.join("lint_subject.rs");
    let metadata = root.join("lint_subject.rmeta");
    std::fs::write(
        &source,
        "#![cfg_attr(trust_verify, allow(dead_code))]\n\
         #[cfg(trust_verify)] compile_error!(\"Tippy compilation retained verification semantics\");\n\
         pub fn lint_subject() { let unused = 1; }\n",
    )
    .expect("write real Tippy compilation fixture");
    let mut compile_command = Command::new(TIPPY_DRIVER_BIN);
    compile_command.args(["--crate-name", "lint_subject", "--crate-type=lib", "--emit=metadata"]);
    if let Some(sysroot) = option_env!("TEST_SYSROOT") {
        // Bootstrap builds rustc-private tools with one compiler and tests the
        // linked-in target compiler against another. Its ambient SYSROOT names
        // the build compiler, while TEST_SYSROOT is ABI-compatible here.
        compile_command.args(["--sysroot", sysroot]);
    }
    let compiled = compile_command
        .arg("-o")
        .arg(&metadata)
        .arg(&source)
        .env_remove("TRUST_NO_VERIFY")
        .env_remove("CLIPPY_ARGS")
        .env_remove("TIPPY_ENCODED_ARGS")
        .output()
        .expect("run a real Tippy lint compilation");
    let compiled_stdout = String::from_utf8_lossy(&compiled.stdout);
    let compiled_stderr = String::from_utf8_lossy(&compiled.stderr);
    assert!(
        compiled.status.success(),
        "real Tippy compilation retained verification semantics:\n{compiled_stdout}\n{compiled_stderr}"
    );
    assert!(metadata.is_file(), "real Tippy compilation did not emit metadata");

    let precedence_metadata = root.join("lint_precedence.rmeta");
    let mut precedence_command = Command::new(TIPPY_DRIVER_BIN);
    precedence_command.args([
        "--crate-name",
        "lint_precedence",
        "--crate-type=lib",
        "--emit=metadata",
        "-Awarnings",
    ]);
    if let Some(sysroot) = option_env!("TEST_SYSROOT") {
        precedence_command.args(["--sysroot", sysroot]);
    }
    let precedence = precedence_command
        .arg("-o")
        .arg(&precedence_metadata)
        .arg(&source)
        .env_remove("TRUST_NO_VERIFY")
        .env("CLIPPY_ARGS", "-Dwarnings")
        .env_remove("TIPPY_ENCODED_ARGS")
        .output()
        .expect("run conflicting lint-precedence compilation");
    let precedence_stderr = String::from_utf8_lossy(&precedence.stderr);
    assert!(
        !precedence.status.success(),
        "Tippy's later `-Dwarnings` was overridden by the caller's earlier `-Awarnings`: {precedence_stderr}"
    );
    assert!(precedence_stderr.contains("unused variable"), "{precedence_stderr}");

    std::fs::remove_dir_all(root).expect("remove driver verification fixture");
}

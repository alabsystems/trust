use super::*;

#[test]
fn engineering_outputs_cannot_alias_retained_initial_inputs() {
    let context = crate::utils::tests::TestCtx::new();
    let root = context.dir().join("initial");
    fs::create_dir(&root).unwrap();
    let root = root.canonicalize().unwrap();
    assert!(separate_output(&root, &root.join("new-tools")).is_err());
    assert!(separate_output(&root, context.dir()).is_err());
    let alias = context.dir().join("alias");
    std::os::unix::fs::symlink(&root, &alias).unwrap();
    assert!(separate_output(&root, &alias.join("new-cache")).is_err());
    assert!(separate_output(&root, &context.dir().join("own-output/tools")).is_ok());
}

// Trust: Seed and the retained frontend have distinct actual cache domains.
#[test]
fn retained_frontend_guards_its_actual_cache_domain_before_compiler_work() {
    let context = crate::utils::tests::TestCtx::new();
    let config = context.config("build").stage(1).create_config();
    let build = crate::core::session::Session::new(config);
    let builder = Builder::new(&build);
    let compiler = Compiler::new(0, builder.host_target);
    let root = context.dir().join("retained-input");
    fs::create_dir(&root).unwrap();
    let root = root.canonicalize().unwrap();
    let seed_input = CargoInput::Seed.for_original(builder.sess);
    let frontend_input = CargoInput::CurrentBuildToolSnapshotStd;
    let seed =
        builder.cargo_out_for_input(compiler, Mode::ToolTarget, builder.host_target, seed_input);
    let frontend = builder.cargo_out_for_input(
        compiler,
        Mode::ToolTarget,
        builder.host_target,
        frontend_input,
    );
    assert_ne!(seed, frontend);
    for (aliased, input, other) in
        [(&frontend, frontend_input, seed_input), (&seed, seed_input, frontend_input)]
    {
        fs::create_dir_all(aliased.parent().unwrap()).unwrap();
        std::os::unix::fs::symlink(&root, aliased).unwrap();
        assert!(validate_output_domains(&builder, &root, input).is_err());
        assert!(validate_output_domains(&builder, &root, other).is_ok());
        fs::remove_file(aliased).unwrap();
    }
}

#[test]
fn helper_absence_is_explicit_and_appearance_or_malformed_inputs_refuse() {
    use std::os::unix::fs::{PermissionsExt as _, symlink};

    let context = crate::utils::tests::TestCtx::new();
    let path = context.dir().join("absent-helper");
    let absent = HelperInput::capture(&path, false, deadline()).unwrap();
    assert!(matches!(&absent, HelperInput::Absent(_)));
    assert_eq!(absent.record()["availability"], "absent");
    assert!(absent.record().get("sha256").is_none());
    absent.validate(deadline()).unwrap();

    fs::write(&path, b"malformed input DATA; never a helper image").unwrap();
    fs::set_permissions(&path, fs::Permissions::from_mode(0o400)).unwrap();
    assert!(absent.validate(deadline()).is_err());
    assert!(HelperInput::capture(&path, false, deadline()).is_err());
    fs::set_permissions(&path, fs::Permissions::from_mode(0o500)).unwrap();
    assert!(HelperInput::capture(&path, false, deadline()).is_err());
    fs::remove_file(&path).unwrap();
    symlink(std::env::current_exe().unwrap(), &path).unwrap();
    assert!(HelperInput::capture(&path, false, deadline()).is_err());
    fs::remove_file(&path).unwrap();
    fs::create_dir(&path).unwrap();
    assert!(HelperInput::capture(&path, true, deadline()).is_err());
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
#[ignore = "requires an actual thin native system-command input path"]
fn actual_native_command_is_held_and_drift_refuses_without_sdk_authority() {
    use std::os::unix::fs::PermissionsExt as _;

    let context = crate::utils::tests::TestCtx::new();
    let root = context.dir().join("held-native-input");
    fs::create_dir(&root).unwrap();
    let root = root.canonicalize().unwrap();
    let path = root.join("actual-native-test-image");
    // Trust: explicit actual native command DATA, not this Bootstrap image
    // (which may load a foreign dylib), a fabricated helper or an SDK receipt.
    // Absence is never a passing positive; qualification executes this opt-in.
    let original = std::env::var_os("TARGO_TEST_ENGINEERING_HELD_COMMAND")
        .expect("actual thin arm64 system-command input path");
    fs::copy(original, &path).unwrap();
    fs::set_permissions(&path, fs::Permissions::from_mode(0o500)).unwrap();
    for system_imports in [false, true] {
        let held = HelperInput::capture(&path, system_imports, deadline()).unwrap();
        assert!(matches!(&held, HelperInput::Held(_)));
        let record = held.record();
        assert_eq!(record["availability"], "held");
        assert_eq!(record["sha256"].as_str().unwrap().len(), 64);
        held.validate(deadline()).unwrap();
    }
    let held = HelperInput::capture(&path, false, deadline()).unwrap();
    fs::set_permissions(&path, fs::Permissions::from_mode(0o400)).unwrap();
    assert!(held.validate(deadline()).is_err());
}

// Trust: metadata binding cannot recover either identity from a version label.
#[test]
fn retained_frontend_identity_requires_unique_native_compiler_fields() {
    const HOST: &str = "aarch64-apple-darwin";
    const COMMIT: &str = "14f3e31b2fc41dc47f0e841c28fd313e31aefe64";
    let reply =
        format!("binary: trustc\nhost: {HOST}\ncommit-hash: {COMMIT}\nrelease: 1.101.0-dev\n");
    assert_eq!(
        retained_identity(&reply, HOST).unwrap(),
        RetainedIdentity { commit: COMMIT.into(), release: "1.101.0-dev".into() }
    );
    for changed in [
        reply.replace("binary: trustc", "binary: rustc"),
        reply.replace(HOST, "x86_64-apple-darwin"),
        reply.replace(COMMIT, "unknown"),
        reply.replace("1.101.0-dev", "../release"),
        reply.replace("release: 1.101.0-dev\n", ""),
        format!("{reply}commit-hash: {COMMIT}\n"),
        format!("{reply}release: 1.101.0-dev\n"),
        format!("{reply}binary: trustc\n"),
        format!("{reply}host: {HOST}\n"),
    ] {
        assert!(retained_identity(&changed, HOST).is_err(), "{changed}");
    }
}

// Trust: opt-in real provider; absence never counts as a passing admission.
#[test]
#[ignore = "requires explicit retained Trust compiler input; execute with --include-ignored"]
fn retained_frontend_observes_actual_held_compiler_identity() {
    let path = std::env::var_os("TRUST_ENGINEERING_RETAINED_COMPILER")
        .map(PathBuf::from)
        .expect("explicit actual retained Trust compiler required");
    let expected_sha = std::env::var("TRUST_ENGINEERING_RETAINED_COMPILER_SHA256")
        .expect("explicit input SHA required");
    assert!(path.is_absolute());
    let root = path.parent().unwrap().parent().unwrap().canonicalize().unwrap();
    let observed_sha = digest(&path, deadline()).unwrap();
    assert_eq!(observed_sha.iter().map(|b| format!("{b:02x}")).collect::<String>(), expected_sha);
    let held = Arc::new(HeldProgram::open(&root, &path, &observed_sha, deadline()).unwrap());
    let target = HeldRustTargetSysroot::capture(Arc::clone(&held), deadline()).unwrap();
    let before = String::from_utf8(query(&held, "-vV", deadline()).unwrap()).unwrap();
    let identity = retained_identity(&before, "aarch64-apple-darwin").unwrap();
    assert_eq!(identity.commit, "14f3e31b2fc41dc47f0e841c28fd313e31aefe64");
    assert_eq!(identity.release, "1.101.0-dev");
    assert!(retained_identity(&before, "x86_64-apple-darwin").is_err());
    held.validate(deadline()).unwrap();
    target.validate(deadline()).unwrap();
    let after = String::from_utf8(query(&held, "-vV", deadline()).unwrap()).unwrap();
    assert_eq!(before, after);
}

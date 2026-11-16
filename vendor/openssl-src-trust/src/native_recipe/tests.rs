use super::*;

#[test]
fn source_copy_refuses_deep_changed_tree_before_stack_or_census_escape() {
    let root = tempfile::tempdir().unwrap();
    let source = root.path().join("source");
    let destination = root.path().join("destination");
    fs::create_dir(&source).unwrap();
    fs::create_dir(&destination).unwrap();
    let mut path = source.clone();
    for _ in 0..66 {
        path.push("nested");
        fs::create_dir(&path).unwrap();
    }
    fs::write(path.join("leaf"), b"changed native bundle").unwrap();
    assert!(copy_source(&source, &destination)
        .unwrap_err()
        .contains("depth exceeds64"));
}

fn environment() -> BTreeMap<OsString, OsString> {
    [
        ("SOURCE_DATE_EPOCH".into(), "1800000000".into()),
        ("PATH".into(), "/usr/bin:/bin".into()),
    ]
    .into_iter()
    .collect()
}

fn observe(environment: BTreeMap<OsString, OsString>, prefix: &str) -> NativeRecipeObservation {
    let mut invocation = Invocation::from_environment("host", "host", "source".into(), environment);
    let mut command = Command::new("perl");
    command
        .arg("Configure")
        .arg(format!("--prefix={prefix}"))
        .current_dir("/owned/native/src");
    invocation.freeze(&mut command);
    invocation.finish()
}

#[test]
fn reproducible_epoch_does_not_claim_an_unowned_toolchain_or_prefix() {
    let observed = observe(environment(), "/first");
    assert_eq!(observed.commands, 1);
    assert_eq!(
        observed.reuse_blockers,
        [
            ReuseBlocker::UnownedNativeToolchain,
            ReuseBlocker::WrapperOwnedOutputRoot
        ]
    );
    assert_eq!(observed, observe(environment(), "/first"));
    assert_ne!(
        observed.invocation_sha256,
        observe(environment(), "/second").invocation_sha256
    );
    let mut changed = environment();
    changed.insert("CFLAGS".into(), "-DCHANGED_NATIVE_SEMANTICS".into());
    assert_ne!(
        observed.invocation_sha256,
        observe(changed, "/first").invocation_sha256
    );
}

#[test]
fn live_or_invalid_build_date_remains_an_explicit_reuse_blocker() {
    let mut env = environment();
    env.remove(OsStr::new("SOURCE_DATE_EPOCH"));
    assert!(observe(env.clone(), "/first")
        .reuse_blockers
        .contains(&ReuseBlocker::LiveBuildClock));
    for value in ["", "-1", "0.5", "18446744073709551616", "yesterday"] {
        env.insert("SOURCE_DATE_EPOCH".into(), value.into());
        assert!(observe(env.clone(), "/first")
            .reuse_blockers
            .contains(&ReuseBlocker::InvalidBuildEpoch));
    }
}

#[test]
fn actual_native_child_gets_the_frozen_environment_and_explicit_overrides() {
    let mut invocation =
        Invocation::from_environment("host", "host", "source".into(), environment());
    let mut command = Command::new("/bin/sh");
    command.args(["-c", "printf '%s|%s|%s' \"$SOURCE_DATE_EPOCH\" \"$NATIVE_RECIPE_OVERRIDE\" \"${PATH-unset}\""])
        .env("NATIVE_RECIPE_OVERRIDE", "actual-override").env_remove("PATH");
    invocation.freeze(&mut command);
    let output = command.output().unwrap();
    assert!(output.status.success());
    // POSIX sh supplies its own default PATH after exec when PATH is absent.
    // Its explicit environment is still checked before launch, without relying
    // on a shell's startup policy as native recipe identity.
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.starts_with("1800000000|actual-override|"));
    let supplied = command.get_envs().collect::<BTreeMap<_, _>>();
    assert!(!supplied.contains_key(OsStr::new("PATH")));
    assert_eq!(
        supplied[OsStr::new("NATIVE_RECIPE_OVERRIDE")],
        Some(OsStr::new("actual-override"))
    );
}

#[test]
fn source_identity_binds_exact_copied_bytes_paths_and_permissions() {
    let root = tempfile::tempdir().unwrap();
    let source = root.path().join("source");
    fs::create_dir(&source).unwrap();
    fs::create_dir(source.join("subdir")).unwrap();
    fs::write(source.join("subdir/input.c"), b"int native_value = 1;\n").unwrap();
    let copy = |name: &str| {
        let destination = root.path().join(name);
        fs::create_dir(&destination).unwrap();
        let identity = copy_source(&source, &destination).unwrap();
        assert_eq!(
            fs::read(destination.join("subdir/input.c")).unwrap(),
            fs::read(source.join("subdir/input.c")).unwrap()
        );
        identity
    };
    let first = copy("first");
    assert_eq!(first, copy("unchanged"));
    fs::write(source.join("subdir/input.c"), b"int native_value = 2;\n").unwrap();
    assert_ne!(first, copy("changed"));
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let before = copy("before-mode-change");
        fs::set_permissions(
            source.join("subdir/input.c"),
            fs::Permissions::from_mode(0o700),
        )
        .unwrap();
        assert_ne!(before, copy("after-mode-change"));
    }
}

#[cfg(unix)]
#[test]
fn source_copy_refuses_redirected_and_special_leaves_without_following_them() {
    use std::os::unix::{ffi::OsStrExt, fs::symlink};
    let root = tempfile::tempdir().unwrap();
    let source = root.path().join("source");
    fs::create_dir(&source).unwrap();
    fs::write(root.path().join("outside.c"), b"outside").unwrap();
    symlink(root.path().join("outside.c"), source.join("input.c")).unwrap();
    let destination = root.path().join("destination");
    fs::create_dir(&destination).unwrap();
    assert!(copy_source(&source, &destination)
        .unwrap_err()
        .contains("not a regular file"));
    fs::remove_file(source.join("input.c")).unwrap();
    let fifo = std::ffi::CString::new(source.join("fifo").as_os_str().as_bytes()).unwrap();
    assert_eq!(unsafe { libc::mkfifo(fifo.as_ptr(), 0o600) }, 0);
    assert!(copy_source(&source, &destination)
        .unwrap_err()
        .contains("not a regular file"));
}

#[test]
fn pinned_openssl_source_can_cross_the_actual_checked_copy_boundary() {
    let root = tempfile::tempdir().unwrap();
    let destination = root.path().join("openssl");
    fs::create_dir(&destination).unwrap();
    let identity = copy_source(&crate::source_dir(), &destination).unwrap();
    assert_eq!(identity.len(), 64);
    assert!(destination.join("Configure").is_file());
    assert!(destination.join("crypto/sha/sha256.c").is_file());
    assert_eq!(
        fs::read(crate::source_dir().join("VERSION.dat")).unwrap(),
        fs::read(destination.join("VERSION.dat")).unwrap()
    );
}

#[test]
fn source_replacement_and_mutation_during_copy_cannot_publish_a_source_identity() {
    let root = tempfile::tempdir().unwrap();
    let source = root.path().join("source.c");
    let replacement = root.path().join("replacement.c");
    fs::write(&source, b"int native_value = 1;\n").unwrap();
    fs::write(&replacement, b"int native_value = 2;\n").unwrap();
    let before = fs::symlink_metadata(&source).unwrap();
    let mut hash = Sha256::new();
    let result = copy_leaf_with_hooks(
        &source,
        &root.path().join("substituted-copy"),
        &before,
        &mut hash,
        || fs::rename(&replacement, &source).unwrap(),
        || {},
    );
    assert!(result.unwrap_err().contains("substituted"));
    let before = fs::symlink_metadata(&source).unwrap();
    let result = copy_leaf_with_hooks(
        &source,
        &root.path().join("mutated-copy"),
        &before,
        &mut hash,
        || {},
        || fs::write(&source, b"int native_value = 3;\n").unwrap(),
    );
    assert!(result.unwrap_err().contains("changed during copy"));
}

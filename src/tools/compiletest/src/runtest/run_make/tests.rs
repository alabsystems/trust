use super::*;

#[test]
fn trust_vanilla_wrapper_passes_real_rustc_and_flag() {
    let script = trust_vanilla_rustc_wrapper_script();
    assert!(script.contains(TRUST_VANILLA_REAL_RUSTC_ENV));
    assert!(script.contains(TRUST_VANILLA_RUSTC_FLAG));
    assert!(
        script.contains("if [ \"$#\" -eq 0 ]") || script.contains("if \"%~1\"==\"\""),
        "wrapper must preserve zero-argument compiler behavior"
    );
    assert!(!script.contains("RUSTC_BOOTSTRAP"));
}

#[test]
fn trust_vanilla_wrapper_path_is_under_run_make_output() {
    let base_dir = Utf8Path::new("run-make-output");
    let wrapper = trust_vanilla_rustc_wrapper_path(base_dir);
    assert!(wrapper.starts_with(base_dir));
    assert_eq!(
        wrapper.file_name(),
        Some(if cfg!(windows) { "rustc-trust-vanilla.cmd" } else { "rustc-trust-vanilla" })
    );
}

#[test]
fn writes_trust_vanilla_wrapper() {
    let base_dir = Utf8PathBuf::try_from(env::temp_dir().join(format!(
        "compiletest-trust-vanilla-wrapper-{}-{}",
        std::process::id(),
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
    )))
    .unwrap();

    ignore_not_found(|| recursive_remove(&base_dir)).unwrap();
    fs::create_dir_all(&base_dir).unwrap();

    let wrapper = write_trust_vanilla_rustc_wrapper(&base_dir);
    assert_eq!(fs::read_to_string(&wrapper).unwrap(), trust_vanilla_rustc_wrapper_script());

    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;

        assert_ne!(fs::metadata(&wrapper).unwrap().permissions().mode() & 0o111, 0);
    }

    ignore_not_found(|| recursive_remove(&base_dir)).unwrap();
}

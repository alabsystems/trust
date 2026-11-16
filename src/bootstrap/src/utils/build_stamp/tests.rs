use tempfile::TempDir;

use crate::utils::build_stamp::BuildStamp;

// Trust: legacy timestamp-only stamps cannot authorize reuse by a new runtime.
#[test]
fn std_cache_legacy_stamp_clears_old_metadata_and_compiler_query() {
    let temp = TempDir::new().unwrap();
    let output = temp.path().join("std");
    std::fs::create_dir(&output).unwrap();
    std::fs::write(output.join(".stamp"), b"").unwrap();
    std::fs::write(output.join("old-core.rmeta"), b"old compiler").unwrap();
    std::fs::write(output.join(".rustc_info.json"), b"old version query").unwrap();

    assert!(super::clear_if_identity_changed(&output, "runtime-one").unwrap());
    assert!(!output.join("old-core.rmeta").exists());
    assert!(!output.join(".rustc_info.json").exists());
    std::fs::write(output.join("current-core.rmeta"), b"current compiler").unwrap();
    assert!(!super::clear_if_identity_changed(&output, "runtime-one").unwrap());
    assert!(output.join("current-core.rmeta").exists());

    assert!(super::clear_if_identity_changed(&output, "runtime-two").unwrap());
    assert!(!output.join("current-core.rmeta").exists());
    assert_eq!(std::fs::read(output.join(".stamp")).unwrap(), b"runtime-two");
}

// Trust: a failed stamp read must neither erase evidence nor publish freshness.
#[test]
fn std_cache_invalid_stamp_refuses_without_replacing_it() {
    let temp = TempDir::new().unwrap();
    let output = temp.path().join("std");
    std::fs::create_dir_all(output.join(".stamp")).unwrap();
    std::fs::write(output.join("old-core.rmeta"), b"old compiler").unwrap();
    assert!(super::clear_if_identity_changed(&output, "new-runtime").is_err());
    assert!(output.join(".stamp").is_dir());
    assert!(output.join("old-core.rmeta").exists());
}

#[test]
fn std_cache_output_file_and_empty_identity_refuse() {
    let temp = TempDir::new().unwrap();
    let output = temp.path().join("std");
    std::fs::write(&output, b"not a cache directory").unwrap();
    assert!(super::clear_if_identity_changed(&output, "runtime").is_err());
    assert_eq!(std::fs::read(&output).unwrap(), b"not a cache directory");
    assert!(super::clear_if_identity_changed(&temp.path().join("absent"), "").is_err());
    assert!(!temp.path().join("absent").exists());
}

#[cfg(unix)]
#[test]
fn std_cache_output_symlink_does_not_touch_its_target() {
    let temp = TempDir::new().unwrap();
    let retained = temp.path().join("retained");
    let output = temp.path().join("std");
    std::fs::create_dir(&retained).unwrap();
    std::fs::write(retained.join("core.rmeta"), b"retained").unwrap();
    std::os::unix::fs::symlink(&retained, &output).unwrap();
    assert!(super::clear_if_identity_changed(&output, "runtime").is_err());
    assert_eq!(std::fs::read(retained.join("core.rmeta")).unwrap(), b"retained");
}

#[test]
#[should_panic(expected = "prefix can not start or end with '.'")]
fn test_with_invalid_prefix() {
    let dir = TempDir::new().unwrap();
    BuildStamp::new(dir.path()).with_prefix(".invalid");
}

#[test]
#[should_panic(expected = "prefix can not start or end with '.'")]
fn test_with_invalid_prefix2() {
    let dir = TempDir::new().unwrap();
    BuildStamp::new(dir.path()).with_prefix("invalid.");
}

#[test]
fn test_is_up_to_date() {
    let dir = TempDir::new().unwrap();

    let mut build_stamp = BuildStamp::new(dir.path()).add_stamp("v1.0.0");
    build_stamp.write().unwrap();

    assert!(
        build_stamp.is_up_to_date(),
        "Expected stamp file to be up-to-date, but contents do not match the expected value."
    );

    build_stamp.stamp = "dummy value".to_owned();
    assert!(
        !build_stamp.is_up_to_date(),
        "Stamp should no longer be up-to-date as we changed its content right above."
    );

    build_stamp.remove().unwrap();
}

#[test]
fn test_with_prefix() {
    let dir = TempDir::new().unwrap();

    let stamp = BuildStamp::new(dir.path()).add_stamp("v1.0.0");
    assert_eq!(stamp.path.file_name().unwrap(), ".stamp");

    let stamp = stamp.with_prefix("test");
    let expected_filename = ".test-stamp";
    assert_eq!(stamp.path.file_name().unwrap(), expected_filename);

    let stamp = stamp.with_prefix("extra-prefix");
    let expected_filename = ".extra-prefix-test-stamp";
    assert_eq!(stamp.path.file_name().unwrap(), expected_filename);
}

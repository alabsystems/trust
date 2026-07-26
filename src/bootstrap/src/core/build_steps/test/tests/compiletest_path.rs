use std::path::{Path, PathBuf};

use super::{CompiletestRustdocPath, compiletest_rustc_path, compiletest_rustdoc_path};

#[test]
fn normal_trust_tests_select_the_branded_sibling() {
    let rustc = PathBuf::from("sysroot/bin/rustc");
    let trustc = PathBuf::from("sysroot/bin/trustc");
    assert_eq!(
        compiletest_rustc_path(rustc.clone(), true, false, "rustc", "trustc"),
        Path::new("sysroot/bin/trustc")
    );
    assert_eq!(
        compiletest_rustc_path(trustc.clone(), true, true, "rustc", "trustc"),
        Path::new("sysroot/bin/rustc")
    );
    assert_eq!(compiletest_rustc_path(rustc.clone(), false, false, "rustc", "trustc"), rustc);
    assert_eq!(compiletest_rustc_path(trustc.clone(), false, true, "rustc", "trustc"), trustc);
}

#[test]
fn rustdoc_identity_respects_stage_and_install_policy() {
    let rustdoc = PathBuf::from("sysroot/bin/rustdoc");
    let trustdoc = PathBuf::from("sysroot/bin/trustdoc");
    let private = PathBuf::from("test-private/rustdoc");

    assert_eq!(
        compiletest_rustdoc_path(
            rustdoc.clone(),
            true,
            false,
            1,
            "rustdoc",
            "trustdoc",
            private.clone(),
        ),
        CompiletestRustdocPath::Direct(trustdoc.clone())
    );
    assert_eq!(
        compiletest_rustdoc_path(
            trustdoc.clone(),
            true,
            true,
            1,
            "rustdoc",
            "trustdoc",
            private.clone(),
        ),
        CompiletestRustdocPath::Direct(rustdoc.clone())
    );
    assert_eq!(
        compiletest_rustdoc_path(
            trustdoc.clone(),
            true,
            false,
            2,
            "rustdoc",
            "trustdoc",
            private.clone(),
        ),
        CompiletestRustdocPath::Direct(trustdoc.clone())
    );
    assert_eq!(
        compiletest_rustdoc_path(
            trustdoc.clone(),
            true,
            true,
            2,
            "rustdoc",
            "trustdoc",
            private.clone(),
        ),
        CompiletestRustdocPath::PrivateAlias { source: trustdoc.clone(), destination: private }
    );
    assert_eq!(
        compiletest_rustdoc_path(
            rustdoc.clone(),
            false,
            true,
            2,
            "rustdoc",
            "trustdoc",
            PathBuf::from("unused"),
        ),
        CompiletestRustdocPath::Direct(rustdoc)
    );
}

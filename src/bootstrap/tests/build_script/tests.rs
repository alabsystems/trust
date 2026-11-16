use super::test_build_rustc;

#[test]
fn bootstrap_binding_selects_the_underlying_compiler() {
    let shim = "/checkout with spaces/build/bootstrap/debug/rustc";
    let real = "/seed with spaces/bin/trustc";
    for stage in ["0", "1", "2"] {
        assert_eq!(
            test_build_rustc(Some(shim), Some(shim), Some(stage), Some(real)),
            Ok(Some(real))
        );
    }
}

#[test]
fn direct_compiler_ignores_ambient_bootstrap_driver() {
    let direct = "/native/bin/trustc";
    for wrapper in [None, Some("/unrelated/bin/rustc"), Some("/tools/sccache")] {
        assert_eq!(
            test_build_rustc(Some(direct), wrapper, Some("1"), Some("/unrelated/bin/trustc")),
            Ok(Some(direct)),
        );
    }
}

#[test]
fn wrapper_identity_without_bootstrap_stage_cannot_select_another_driver() {
    for stage in [None, Some(""), Some("not-a-stage"), Some("-1")] {
        assert_eq!(
            test_build_rustc(Some("rustc"), Some("rustc"), stage, Some("unrelated")),
            Ok(Some("rustc")),
        );
    }
}

#[test]
fn bootstrap_binding_refuses_missing_empty_or_recursive_driver() {
    for real in [None, Some(""), Some("shim")] {
        let error = test_build_rustc(Some("shim"), Some("shim"), Some("0"), real).unwrap_err();
        assert!(error.contains("RUSTC_REAL"), "{error}");
    }
}

#[test]
fn absent_cargo_compiler_does_not_select_an_ambient_driver() {
    assert_eq!(test_build_rustc(None, Some("shim"), Some("0"), Some("unrelated")), Ok(None));
}

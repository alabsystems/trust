use std::ffi::OsString;

mod test_utils;

use test_utils::{
    INHERITED_UNVERIFIED_NOTICE, bootstrap_dependency_builder_env, cargo_notice_normalizer_if_unasserted,
    inherited_unverified_notice_regex, reject_trust_frontend_controls,
};

#[test]
fn only_the_exact_inherited_unverified_notice_is_normalized() {
    let normalizer = inherited_unverified_notice_regex();
    assert_eq!(
        normalizer
            .replace_all(format!("{INHERITED_UNVERIFIED_NOTICE}\n").as_bytes(), &b""[..])
            .as_ref(),
        b"",
    );
    assert_eq!(
        normalizer
            .replace_all(INHERITED_UNVERIFIED_NOTICE.as_bytes(), &b""[..])
            .as_ref(),
        b"",
    );
}

#[test]
fn cargo_cases_that_assert_the_inherited_disclosure_keep_that_assertion() {
    let asserted = format!("{INHERITED_UNVERIFIED_NOTICE}\nerror: proof rejected\n");
    assert!(cargo_notice_normalizer_if_unasserted(asserted.as_bytes()).is_none());
    let expected = b"warning: another warning\nverdict: Unknown\nerror: proof rejected\n";
    let normalizer = cargo_notice_normalizer_if_unasserted(expected).unwrap();
    let actual = [format!("{INHERITED_UNVERIFIED_NOTICE}\n").as_bytes(), expected].concat();
    assert_eq!(normalizer.replace_all(&actual, &b""[..]).as_ref(), expected);
}

#[test]
fn cargo_normalization_preserves_warnings_proof_verdict_and_error_lines() {
    let normalizer = inherited_unverified_notice_regex();
    for diagnostic in [
        "warning: a real Cargo or compiler warning\n",
        "warning: UNVERIFIED: another unverified route\n",
        "warning: UNVERIFIED: `targo check` inherited untrusted caller text\n",
        "note: compiled WITHOUT Trust verification — 0 obligations checked\n",
        "proof: Certified\n",
        "verdict: Unknown\n",
        "error: proof rejected\n",
    ] {
        let input = format!("{INHERITED_UNVERIFIED_NOTICE}\n{diagnostic}");
        assert_eq!(
            normalizer.replace_all(input.as_bytes(), &b""[..]).as_ref(),
            diagnostic.as_bytes(),
        );
    }
}

#[test]
fn inherited_unverified_normalization_requires_a_complete_exact_line() {
    let normalizer = inherited_unverified_notice_regex();
    for diagnostic in [
        format!("error: {INHERITED_UNVERIFIED_NOTICE}\n"),
        format!(" {INHERITED_UNVERIFIED_NOTICE}\n"),
        format!("{INHERITED_UNVERIFIED_NOTICE}; future field\n"),
        format!("{INHERITED_UNVERIFIED_NOTICE} extra\n"),
    ] {
        assert_eq!(
            normalizer.replace_all(diagnostic.as_bytes(), &b""[..]).as_ref(),
            diagnostic.as_bytes(),
        );
    }
}

#[test]
fn ordinary_diagnostic_arguments_reach_the_driver_untouched() {
    reject_trust_frontend_controls(&[
        OsString::from("-Dwarnings"),
        OsString::from("--emit=metadata"),
        OsString::from("-Zui-testing"),
    ]);
}

#[test]
#[should_panic(expected = "no-evidence lint frontend rejects it")]
fn a_trust_control_in_the_driver_arguments_fails_the_harness() {
    reject_trust_frontend_controls(&[OsString::from("-Dwarnings"), OsString::from("-Ztrust-verify=off")]);
}

#[test]
fn dependency_builder_restores_supplemental_shim_context_and_isolates_all_units() {
    assert_eq!(
        bootstrap_dependency_builder_env("1", "aarch64-apple-darwin", "1"),
        [
            (OsString::from("RUSTC_STAGE"), Some(OsString::from("1"))),
            (
                OsString::from("CFG_COMPILER_BUILD_TRIPLE"),
                Some(OsString::from("aarch64-apple-darwin")),
            ),
            (
                OsString::from("RUSTC_LINK_STD_INTO_RUSTC_DRIVER"),
                Some(OsString::from("1")),
            ),
            (
                OsString::from("TRUST_BOOTSTRAP_SHIM_NO_VERIFY"),
                Some(OsString::from("1")),
            ),
            (OsString::from("TRUST_BOOTSTRAP_SHIM_NO_VERIFY_TARGET_ONLY"), None),
        ]
    );
}

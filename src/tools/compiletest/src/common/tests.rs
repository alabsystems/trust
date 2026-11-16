use std::ffi::OsStr;
use std::process::Command;

use super::{
    Config, TRUST_VANILLA_RUSTC_FLAG, TRUST_VANILLA_SENTINEL, TRUST_VERIFIED_SENTINEL,
    TrustVerificationLane, configure_trust_verification_isolation,
};

fn args(command: &Command) -> Vec<&OsStr> {
    command.get_args().collect()
}

#[test]
fn trust_isolation_is_capability_scoped_and_overridable() {
    let mut upstream = Command::new("rustc");
    configure_trust_verification_isolation(&mut upstream, TrustVerificationLane::Unsupported);
    assert!(args(&upstream).is_empty());
    // A stage-0 Trust seed still verifies by default; the lane turns it off by
    // the spelling-independent environment switch, which a non-Trust driver
    // ignores.
    assert!(
        upstream
            .get_envs()
            .any(|(key, value)| key == "TRUST_NO_VERIFY" && value == Some(OsStr::new("1"))),
        "the unsupported arm must set the seed's environment off-switch"
    );

    let mut trust = Command::new("rustc");
    configure_trust_verification_isolation(&mut trust, TrustVerificationLane::IsolatedOff);
    trust.arg("-Ztrust-verify=on");
    assert_eq!(
        args(&trust),
        [OsStr::new(TRUST_VANILLA_RUSTC_FLAG), OsStr::new("-Ztrust-verify=on")]
    );

    // An auxiliary boundary must override a primary test's opt-in. Any
    // dedicated auxiliary flags are appended after this and can opt in
    // deliberately rather than inheriting verification accidentally.
    configure_trust_verification_isolation(&mut trust, TrustVerificationLane::IsolatedOff);
    assert_eq!(
        args(&trust),
        [
            OsStr::new(TRUST_VANILLA_RUSTC_FLAG),
            OsStr::new("-Ztrust-verify=on"),
            OsStr::new(TRUST_VANILLA_RUSTC_FLAG),
        ]
    );
}

/// The verified lane is OPT-IN, and the default lane's flag vector is unchanged.
///
/// This is the risk the whole change turns on: silently flipping the default
/// would turn every existing green run into an unwitnessed one. So the identity
/// is asserted directly, on the resulting argv, for both arms of the historical
/// boolean — `IsolatedOff` must be byte-identical to the old `supported = true`,
/// `Unsupported` to the old `supported = false`.
#[test]
fn trust_verified_lane_is_opt_in_and_default_is_unchanged() {
    // --- the default lane, both arms of the historical boolean ---------------
    let mut unsupported = Command::new("rustc");
    configure_trust_verification_isolation(&mut unsupported, TrustVerificationLane::Unsupported);
    assert!(args(&unsupported).is_empty(), "the unsupported arm must state nothing");

    let mut isolated = Command::new("rustc");
    configure_trust_verification_isolation(&mut isolated, TrustVerificationLane::IsolatedOff);
    assert_eq!(
        args(&isolated),
        [OsStr::new(TRUST_VANILLA_RUSTC_FLAG)],
        "the default/vanilla lane must still append exactly -Ztrust-verify=off"
    );

    // --- the verified lane ---------------------------------------------------
    let mut verified = Command::new("rustc");
    configure_trust_verification_isolation(&mut verified, TrustVerificationLane::Verified);
    assert_eq!(
        args(&verified),
        [OsStr::new("-Ztrust-verify=on"), OsStr::new("-Ztrust-policy=strict")],
        "the verified lane must state the shipping default in argv"
    );
    assert!(
        !args(&verified).contains(&OsStr::new(TRUST_VANILLA_RUSTC_FLAG)),
        "the verified lane must never append the isolation flag -- that is the whole point"
    );

    // An auxiliary boundary re-applies the lane, exactly as the vanilla lane
    // does, so an aux crate cannot inherit a primary test's `-Ztrust-verify=off`.
    verified.arg(TRUST_VANILLA_RUSTC_FLAG);
    configure_trust_verification_isolation(&mut verified, TrustVerificationLane::Verified);
    assert_eq!(
        args(&verified),
        [
            OsStr::new("-Ztrust-verify=on"),
            OsStr::new("-Ztrust-policy=strict"),
            OsStr::new(TRUST_VANILLA_RUSTC_FLAG),
            OsStr::new("-Ztrust-verify=on"),
            OsStr::new("-Ztrust-policy=strict"),
        ],
        "the aux boundary must re-state the verified lane last"
    );
}

/// `Config::trust_verification_lane` reduces to the historical disjunction
/// whenever `--trust-verified` is absent.
///
/// The lane decision is a pure function of three booleans, so it is asserted as
/// one here rather than through a `Config` (which needs ~80 unrelated fields).
/// `common.rs` must keep this shape; if it drifts, the truth table below is the
/// thing that notices.
#[test]
fn trust_lane_selection_truth_table_preserves_the_default() {
    fn lane(verified: bool, supports: bool, vanilla: bool) -> TrustVerificationLane {
        // Mirror of `Config::trust_verification_lane`.
        if verified {
            TrustVerificationLane::Verified
        } else if supports || vanilla {
            TrustVerificationLane::IsolatedOff
        } else {
            TrustVerificationLane::Unsupported
        }
    }

    for &supports in &[false, true] {
        for &vanilla in &[false, true] {
            // Historical behaviour: append the isolation flag iff the disjunction held.
            let historical_appended_off = supports || vanilla;
            let actual = lane(false, supports, vanilla);
            assert_eq!(
                actual == TrustVerificationLane::IsolatedOff,
                historical_appended_off,
                "default lane changed for supports={supports} vanilla={vanilla}"
            );
            // ...and the verified opt-in is the ONLY thing that can change it.
            assert_eq!(lane(true, supports, vanilla), TrustVerificationLane::Verified);
        }
    }
}

/// Both sentinels are internal: neither may leak into a test's rustc argv.
#[test]
fn trust_lane_sentinels_are_internal_rustcflags() {
    assert!(Config::is_internal_rustcflag(TRUST_VANILLA_SENTINEL));
    assert!(Config::is_internal_rustcflag(TRUST_VERIFIED_SENTINEL));
    assert!(!Config::is_internal_rustcflag("-Ztrust-verify=on"));
    assert!(!Config::is_internal_rustcflag("--edition=2021"));
}

/// End-to-end through a REAL `Config`: argv in, rustc flag vector out.
///
/// The tests above exercise `configure_trust_verification_isolation` and a
/// MIRROR of the lane-selection rule. This one runs the real
/// `Config::trust_verification_lane` on a config parsed from real argv, so a
/// drift between the mirror and the production selector cannot hide.
pub(crate) fn trust_lane_config_from(extra: &[&str]) -> Config {
    let mut args: Vec<String> = [
        "compiletest",
        "--mode=ui",
        "--suite=ui",
        "--compile-lib-path=",
        "--run-lib-path=",
        "--python=",
        "--jsondocck-path=",
        "--src-root=",
        "--src-test-suite-root=",
        "--build-root=",
        "--build-test-suite-root=",
        "--sysroot-base=",
        "--cc=c",
        "--cxx=c++",
        "--cflags=",
        "--cxxflags=",
        "--llvm-components=",
        "--android-cross-path=",
        "--stage=2",
        "--stage-id=stage2-x86_64-unknown-linux-gnu",
        "--channel=nightly",
        "--host=x86_64-unknown-linux-gnu",
        "--target=x86_64-unknown-linux-gnu",
        "--nightly-branch=",
        "--git-merge-commit-email=",
        "--minicore-path=",
        "--jobs=0",
        "--rustc-path=/nonexistent/trustc",
    ]
    .iter()
    .map(ToString::to_string)
    .collect();
    args.extend(extra.iter().map(ToString::to_string));
    // Trust: consume the parser through its current CLI owner.
    crate::cli::parse_config(args)
}

/// End-to-end through a REAL `Config`: argv in, rustc flag vector out.
///
/// The tests above exercise `configure_trust_verification_isolation` and a
/// MIRROR of the lane-selection rule. This one runs the real
/// `Config::trust_verification_lane` on a config parsed from real argv, so a
/// drift between the mirror and the production selector cannot hide.
#[test]
fn trust_lane_reaches_rustc_argv_from_the_command_line() {
    // --- the DEFAULT (branded) lane, unchanged -------------------------------
    let default_lane = trust_lane_config_from(&["--rustc-supports-trust-verification"]);
    assert!(!default_lane.trust_verified());
    assert!(!default_lane.trust_vanilla());
    assert_eq!(default_lane.trust_verification_lane(), TrustVerificationLane::IsolatedOff);
    assert_eq!(
        args(&default_lane.rustc_command()),
        [OsStr::new(TRUST_VANILLA_RUSTC_FLAG)],
        "the default lane's flag vector must be unchanged"
    );

    // --- the vanilla lane ----------------------------------------------------
    let vanilla =
        trust_lane_config_from(&["--rustc-supports-trust-verification", "--trust-vanilla"]);
    assert!(vanilla.trust_vanilla() && !vanilla.trust_verified());
    assert_eq!(vanilla.trust_verification_lane(), TrustVerificationLane::IsolatedOff);
    assert_eq!(args(&vanilla.rustc_command()), [OsStr::new(TRUST_VANILLA_RUSTC_FLAG)]);

    // --- the verified lane ---------------------------------------------------
    let verified =
        trust_lane_config_from(&["--rustc-supports-trust-verification", "--trust-verified"]);
    assert!(verified.trust_verified() && !verified.trust_vanilla());
    assert_eq!(verified.trust_verification_lane(), TrustVerificationLane::Verified);
    assert_eq!(
        args(&verified.rustc_command()),
        [OsStr::new("-Ztrust-verify=on"), OsStr::new("-Ztrust-policy=strict")],
        "the verified lane must reach rustc argv from the command line"
    );

    // `needs-trust-verify` is gated on exactly `!config.trust_vanilla()`
    // (directives/needs.rs). On the verified lane that is TRUE, so those tests
    // RUN -- they are this lane's positive control.
    assert!(!verified.trust_vanilla(), "needs-trust-verify must RUN on the verified lane");
    assert!(vanilla.trust_vanilla(), "needs-trust-verify must be ignored on the vanilla lane");

    // Neither sentinel may leak into a test's own rustc flags.
    let mut leak = Command::new("rustc");
    verified.add_rustcflags(&mut leak, &verified.target_rustcflags);
    assert!(args(&leak).is_empty(), "the verified sentinel leaked into rustc argv");
    let mut leak_vanilla = Command::new("rustc");
    vanilla.add_rustcflags(&mut leak_vanilla, &vanilla.target_rustcflags);
    assert!(args(&leak_vanilla).is_empty(), "the vanilla sentinel leaked into rustc argv");

    // The unsupported arm still states nothing.
    let upstream = trust_lane_config_from(&[]);
    assert_eq!(upstream.trust_verification_lane(), TrustVerificationLane::Unsupported);
    assert!(args(&upstream.rustc_command()).is_empty());
}

/// Asking for both lanes is REFUSED, not resolved.
///
/// Bootstrap's clap definition also declares the conflict, but compiletest is
/// invoked directly too (and by other harnesses), so the refusal lives here as
/// well: a run that quietly picked one lane would mislabel every exception row
/// it produced.
#[test]
#[should_panic(expected = "fatal error")]
fn trust_vanilla_and_trust_verified_are_refused_together() {
    trust_lane_config_from(&[
        "--rustc-supports-trust-verification",
        "--trust-vanilla",
        "--trust-verified",
    ]);
}

/// The verified lane on a driver with no verifier is REFUSED, not downgraded.
///
/// A silent downgrade is the dangerous outcome: an upstream `download-rustc`
/// compiler ignoring `-Ztrust-verify=on` would produce VANILLA evidence under a
/// VERIFIED label.
#[test]
#[should_panic(expected = "fatal error")]
fn trust_verified_without_a_capable_driver_is_refused() {
    trust_lane_config_from(&["--trust-verified"]);
}

/// The verified lane gets its OWN stamp, and the two old lanes keep theirs.
///
/// `compute_stamp_hash` decides whether a previous result can be reused. The
/// verified lane compiles with a different flag vector, so sharing a stamp with
/// a verification-off run would let a verified run find every test "current",
/// skip it, and report green having verified nothing -- the silent no-op this
/// lane must not have. The two pre-existing lanes' stamps must be UNCHANGED, so
/// landing this lane does not invalidate anyone's cache.
#[test]
fn trust_verified_lane_has_a_distinct_stamp() {
    let default_lane = trust_lane_config_from(&["--rustc-supports-trust-verification"]);
    let vanilla =
        trust_lane_config_from(&["--rustc-supports-trust-verification", "--trust-vanilla"]);
    let verified =
        trust_lane_config_from(&["--rustc-supports-trust-verification", "--trust-verified"]);

    // Trust: debugger selection now belongs to the test variant.
    let variant = crate::executor::TestVariant { revision: None, debugger: None };
    let stamp = |config: &Config| crate::runtest::compute_stamp_hash(config, &variant);
    assert_ne!(
        stamp(&default_lane),
        stamp(&verified),
        "the verified lane must not reuse the default lane's stamps"
    );
    assert_ne!(
        stamp(&vanilla),
        stamp(&verified),
        "the verified lane must not reuse the vanilla lane's stamps"
    );
    // The pre-existing separation is untouched...
    assert_ne!(stamp(&default_lane), stamp(&vanilla));

    // ...and the two pre-existing lanes' stamp VALUES are bit-identical to the
    // formula that predates this lane, reproduced here in full for a `Ui` config
    // with no debugger. The new lane contributes to the hash only when selected,
    // so landing it invalidates nobody's cache.
    fn pre_lane_stamp(config: &Config, variant: &crate::executor::TestVariant) -> String {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut hash = DefaultHasher::new();
        config.stage_id.hash(&mut hash);
        config.run.hash(&mut hash);
        config.edition.hash(&mut hash);
        config.trust_vanilla().hash(&mut hash);
        assert!(variant.debugger.is_none(), "this reproduction covers the no-debugger shape");
        assert_eq!(config.mode, crate::common::TestMode::Ui);
        config.force_pass_mode.hash(&mut hash);
        format!("{:x}", hash.finish())
    }

    assert_eq!(
        stamp(&default_lane),
        pre_lane_stamp(&default_lane, &variant),
        "the DEFAULT lane's stamp changed -- every cached result would be invalidated"
    );
    assert_eq!(
        stamp(&vanilla),
        pre_lane_stamp(&vanilla, &variant),
        "the VANILLA lane's stamp changed -- every cached result would be invalidated"
    );
    assert_ne!(
        stamp(&verified),
        pre_lane_stamp(&verified, &variant),
        "the verified lane must perturb the stamp; otherwise it collides with the default lane"
    );
}

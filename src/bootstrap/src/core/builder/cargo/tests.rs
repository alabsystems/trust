use std::ffi::OsStr;

use super::{
    RETIRED_TRUST_BOOTSTRAP_SHIM_TARGET_ONLY_ENV, Rustflags, TRUST_BOOTSTRAP_NO_VERIFY_FLAG,
    TRUST_BOOTSTRAP_NO_VERIFY_OPTION, TRUST_BOOTSTRAP_VERIFY_LIBRARY_ENV,
    TRUST_VERIFIABLE_LIBRARY_UNITS, apply_bootstrap_trust_verification_default,
    bootstrap_disables_default_trust_verification, bootstrap_verification_request_refusal,
    effective_codegen_units, effective_debuginfo_level, flags_env,
    parse_trust_verify_library_request, refuse_bootstrap_verification_request,
    retired_trust_bootstrap_shim_target_only_refusal, rustflags_request_bootstrap_verification,
    std_out_dir_needs_clear, trust_cg_codegen_flags, trust_cg_codegen_is_active,
    trust_verifier_controls, trust_verify_library_units_authorized,
};
use crate::core::builder::Kind;
use crate::core::config::DebuginfoLevel;
use crate::{CodegenBackendKind, Mode, TargetSelection};

/// Every `Mode` bootstrap can drive a cargo invocation with. Spelled out rather
/// than derived so a new variant makes these tests fail to compile and forces a
/// decision about which side of the library/self-proof line it falls on.
const ALL_MODES: &[Mode] = &[
    Mode::Std,
    Mode::Rustc,
    Mode::Codegen,
    Mode::ToolBootstrap,
    Mode::ToolTarget,
    Mode::ToolStd,
    Mode::ToolRustcPrivate,
];

/// Every rustflags string the two verifier questions are asked about, so both
/// answers are always taken over the SAME set of tokens.
const VERIFIER_CONTROL_RUSTFLAGS: &[&str] = &[
    "-Ztrust-verify-full",
    "-Ztrust-verify=on",
    "-Ztrust-policy=advisory",
    "-Z trust-verify-output=json",
    "-Ztrust-verify-function-budget-ms=60000",
    "-Ztrust-policy=memory-safe",
];

#[test]
fn trust_verifier_control_detection_accepts_combined_and_split_flags() {
    for rustflags in VERIFIER_CONTROL_RUSTFLAGS {
        assert!(
            !trust_verifier_controls(rustflags).is_empty(),
            "{rustflags} is a verifier control"
        );
    }
    assert!(trust_verifier_controls("-Zrandomize-layout -Cdebuginfo=2").is_empty());
    assert!(trust_verifier_controls("-Ztrustworthy-layout").is_empty());
    // Both token shapes yield the option WITHOUT the `-Z`, which is the form
    // the off-switch comparison is made against.
    assert_eq!(trust_verifier_controls("-Ztrust-verify=off"), vec!["trust-verify=off"]);
    assert_eq!(trust_verifier_controls("-Z trust-verify=off"), vec!["trust-verify=off"]);
    assert_eq!(
        trust_verifier_controls("-Wrust_2018_idioms -Ztrust-verify=off -Ztrust-policy=advisory"),
        vec!["trust-verify=off", "trust-policy=advisory"]
    );
}

#[test]
fn no_verify_option_and_flag_are_the_same_switch() {
    assert_eq!(TRUST_BOOTSTRAP_NO_VERIFY_FLAG, format!("-Z{TRUST_BOOTSTRAP_NO_VERIFY_OPTION}"));
}

#[test]
fn non_stage0_bootstrap_uses_no_verify_env_by_default() {
    assert!(bootstrap_disables_default_trust_verification(1, ""));
}

#[test]
fn stage0_bootstrap_does_not_use_no_verify_env() {
    assert!(!bootstrap_disables_default_trust_verification(0, ""));
}

/// FAIL-OPEN REGRESSION. The suppression used to admit ANY verifier control,
/// while the self-proof panic refuses everything except the exact off-switch —
/// so the residual cases were unreachable only by accident of ordering, and the
/// two functions shared no assertion. Narrowing the panic later would silently
/// have produced units with no off-switch and verification default-ON.
///
/// This pins the coupling as a property of the SUPPRESSION alone, so it holds
/// whatever the panic does: a verifier control that is not bootstrap's own
/// off-switch never suppresses the default, and the composed rustflags still
/// end with the off-switch.
#[test]
fn only_the_exact_off_switch_suppresses_the_bootstrap_default() {
    for rustflags in VERIFIER_CONTROL_RUSTFLAGS {
        assert!(
            bootstrap_disables_default_trust_verification(1, rustflags),
            "{rustflags} must not suppress bootstrap's off-switch default"
        );
        let (_, value) = bootstrap_rustflags_env(1, &rustflags.split(' ').collect::<Vec<_>>());
        assert!(
            value.split(['\x1f', ' ']).any(|flag| flag == TRUST_BOOTSTRAP_NO_VERIFY_FLAG),
            "{rustflags} must still be handed the off-switch, got {value:?}"
        );
    }

    // The one case that legitimately suppresses it: the flag is already there,
    // in either token shape, so it is not duplicated.
    assert!(!bootstrap_disables_default_trust_verification(1, "-Ztrust-verify=off"));
    assert!(!bootstrap_disables_default_trust_verification(1, "-Z trust-verify=off"));
    assert!(!bootstrap_disables_default_trust_verification(
        1,
        "-Wrust_2018_idioms -Ztrust-verify=off"
    ));

    // Mixed: bootstrap's off-switch plus a control the refusal rejects. The
    // refusal is what stops this reaching a compiler today; the suppression
    // answer stays consistent either way.
    assert!(rustflags_request_bootstrap_verification("-Ztrust-verify=off -Ztrust-policy=advisory"));
}

#[test]
fn bootstrap_allows_only_the_exact_off_switch() {
    assert!(!rustflags_request_bootstrap_verification("-Ztrust-verify=off"));
    assert!(!rustflags_request_bootstrap_verification("-Z trust-verify=off"));
    assert!(rustflags_request_bootstrap_verification("-Ztrust-verify=on"));
    assert!(rustflags_request_bootstrap_verification("-Ztrust-verify-full"));
    assert!(rustflags_request_bootstrap_verification("-Z trust-policy=advisory"));
}

/// Reproduce `Cargo::from`'s composition: bootstrap's own flags, then the
/// verification default, then the env pair Cargo is handed.
fn bootstrap_rustflags_env(
    build_compiler_stage: u32,
    bootstrap_flags: &[&str],
) -> (String, String) {
    let mut rustflags = Rustflags::new(TargetSelection::from_user("aarch64-apple-darwin"));
    for flag in bootstrap_flags {
        rustflags.arg(flag);
    }
    apply_bootstrap_trust_verification_default(&mut rustflags, build_compiler_stage);
    let (var, value) = flags_env("RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", &rustflags.0);
    (var.to_string(), value)
}

/// The regression this pins: Cargo honours exactly ONE rustflags source, so the
/// off-switch has to be in the same payload as bootstrap's other flags. Deliver
/// it through `CARGO_TARGET_<TRIPLE>_RUSTFLAGS` instead and Cargo drops it on
/// the floor, silently verifying the whole third-party dependency graph.
#[test]
fn bootstrap_off_switch_rides_the_same_lane_as_bootstrap_s_other_flags() {
    // `-Wrust_2018_idioms` is unconditional in bootstrap, so the competing
    // `RUSTFLAGS`/`CARGO_ENCODED_RUSTFLAGS` lane always exists in practice.
    let (var, value) = bootstrap_rustflags_env(1, &["-Wrust_2018_idioms", "-Wunused_lifetimes"]);

    assert!(matches!(var.as_str(), "RUSTFLAGS" | "CARGO_ENCODED_RUSTFLAGS"), "{var}");
    assert!(value.contains(TRUST_BOOTSTRAP_NO_VERIFY_FLAG), "{var}={value:?}");
    assert!(value.contains("-Wrust_2018_idioms"), "{var}={value:?}");
}

#[test]
fn bootstrap_off_switch_survives_when_bootstrap_has_no_other_flags() {
    let (var, value) = bootstrap_rustflags_env(1, &[]);

    assert_eq!(var, "RUSTFLAGS");
    assert_eq!(value, TRUST_BOOTSTRAP_NO_VERIFY_FLAG);
}

#[test]
fn stage0_units_keep_the_seed_default() {
    let (_, value) = bootstrap_rustflags_env(0, &["-Wrust_2018_idioms"]);

    assert!(!value.contains("trust-verify"), "{value:?}");
}

#[test]
fn an_explicit_off_switch_is_not_duplicated() {
    let (_, value) = bootstrap_rustflags_env(1, &["-Ztrust-verify=off"]);

    assert_eq!(value.matches(TRUST_BOOTSTRAP_NO_VERIFY_FLAG).count(), 1, "{value:?}");
}

/// A developer control that is NOT bootstrap's off-switch no longer takes
/// ownership of the verifier surface. It is refused before it can reach a
/// compiler (`refuse_bootstrap_verification_request`), and if that refusal is
/// ever narrowed, the unit still gets the off-switch rather than defaulting to
/// verification ON. The control itself is preserved, so nothing is lost.
#[test]
fn a_deliberate_verifier_control_does_not_strip_the_default() {
    let mut rustflags = Rustflags::new(TargetSelection::from_user("aarch64-apple-darwin"));
    rustflags.arg("-Ztrust-verify-output=json");
    apply_bootstrap_trust_verification_default(&mut rustflags, 1);

    assert!(rustflags.0.contains("-Ztrust-verify-output=json"), "{:?}", rustflags.0);
    assert!(rustflags.0.contains(TRUST_BOOTSTRAP_NO_VERIFY_FLAG), "{:?}", rustflags.0);
}

#[test]
fn trust_cg_abort_policy_starts_with_the_staged_compiler() {
    assert!(!trust_cg_codegen_is_active(0, &CodegenBackendKind::TrustCg));
    assert!(trust_cg_codegen_is_active(1, &CodegenBackendKind::TrustCg));
    assert!(trust_cg_codegen_is_active(2, &CodegenBackendKind::TrustCg));
    assert!(!trust_cg_codegen_is_active(1, &CodegenBackendKind::Llvm));
    assert!(!trust_cg_codegen_is_active(1, &CodegenBackendKind::Custom("other".into())));
}

#[test]
fn trust_cg_profiles_disable_unimplemented_debuginfo() {
    assert_eq!(effective_debuginfo_level(true, DebuginfoLevel::Full), DebuginfoLevel::None);
    assert_eq!(
        effective_debuginfo_level(true, DebuginfoLevel::LineTablesOnly),
        DebuginfoLevel::None
    );
    assert_eq!(
        effective_debuginfo_level(false, DebuginfoLevel::LineTablesOnly),
        DebuginfoLevel::LineTablesOnly
    );
}

#[test]
fn trust_cg_profiles_force_the_single_supported_codegen_unit() {
    assert_eq!(effective_codegen_units(true, None), Some(1));
    assert_eq!(effective_codegen_units(true, Some(16)), Some(1));
    assert_eq!(effective_codegen_units(false, Some(16)), Some(16));
    assert_eq!(effective_codegen_units(false, None), None);
}

#[test]
fn trust_cg_panic_flags_cover_normal_and_test_units() {
    assert_eq!(trust_cg_codegen_flags(false, false), &[] as &[&str]);
    assert_eq!(trust_cg_codegen_flags(false, true), &[] as &[&str]);
    assert_eq!(trust_cg_codegen_flags(true, false), &["-Cpanic=abort"]);
    assert_eq!(trust_cg_codegen_flags(true, true), &["-Cpanic=abort", "-Zpanic-abort-tests"]);
}

// ---------------------------------------------------------------------------
// The self-proof refusal, and the per-unit `library/` opt-in that does NOT
// relax it. Two different claims, two different switches.
// ---------------------------------------------------------------------------

/// (A) "bootstrap verified ITSELF" stays blocked. The refusal is not narrowed by
/// the library opt-in, and it does not care which `Mode` asked: a verifier
/// control in bootstrap's own rustflags is invocation-wide, so honouring one for
/// a `Mode::Std` invocation would verify std's entire third-party dependency
/// graph with no unit named anywhere.
#[test]
fn the_self_proof_refusal_still_fires_for_every_mode() {
    for mode in ALL_MODES {
        for rustflags in [
            "-Ztrust-verify=on",
            "-Z trust-verify=on",
            "-Ztrust-verify-full",
            "-Wrust_2018_idioms -Ztrust-policy=certify",
        ] {
            let refusal = bootstrap_verification_request_refusal(*mode, rustflags);
            let refusal = refusal.unwrap_or_else(|| {
                panic!("{mode:?} accepted bootstrap verification {rustflags:?}")
            });
            assert!(
                refusal.starts_with(
                    "bootstrap compiler verification flags are unsupported without an \
                     authenticated artifact-bound bootstrap protocol; \
                     use scripts/stage2_verify_self_build.sh instead"
                ),
                "{refusal}"
            );
        }
    }
}

#[test]
fn the_self_proof_refusal_leaves_the_off_switch_and_ordinary_flags_alone() {
    for mode in ALL_MODES {
        assert!(bootstrap_verification_request_refusal(*mode, "").is_none());
        assert!(bootstrap_verification_request_refusal(*mode, "-Ztrust-verify=off").is_none());
        assert!(bootstrap_verification_request_refusal(*mode, "-Z trust-verify=off").is_none());
        assert!(
            bootstrap_verification_request_refusal(*mode, "-Wrust_2018_idioms -Cdebuginfo=2")
                .is_none()
        );
    }
}

#[test]
#[should_panic(expected = "bootstrap compiler verification flags are unsupported")]
fn compiler_units_still_panic_on_a_bootstrap_verification_request() {
    refuse_bootstrap_verification_request(Mode::Rustc, "-Wrust_2018_idioms -Ztrust-verify=on");
}

#[test]
#[should_panic(expected = "bootstrap compiler verification flags are unsupported")]
fn bootstrap_tool_units_still_panic_on_a_bootstrap_verification_request() {
    refuse_bootstrap_verification_request(Mode::ToolBootstrap, "-Ztrust-policy=certify");
}

/// The opt-in is not a way into the rustflags lane: a library invocation that
/// asks for verification through RUSTFLAGS is refused exactly like a compiler
/// one.
#[test]
#[should_panic(expected = "bootstrap compiler verification flags are unsupported")]
fn library_units_still_panic_on_a_bootstrap_verification_request() {
    refuse_bootstrap_verification_request(Mode::Std, "-Ztrust-verify=on");
}

/// (B) the per-unit opt-in is honoured for library invocations and refused
/// everywhere else. `Mode::Std` is the only mode whose units are `library/`
/// crates; every other mode is the compiler, bootstrap, or a tool.
#[test]
fn the_library_opt_in_is_refused_for_compiler_bootstrap_and_tool_units() {
    for mode in ALL_MODES {
        for stage in [1, 2, 3] {
            assert_eq!(
                trust_verify_library_units_authorized(*mode, stage),
                *mode == Mode::Std,
                "{mode:?} at stage {stage}"
            );
        }
    }
}

/// The stage0 build compiler is the SEED, whose vintage is the pin's and not
/// this tree's. It is never the "already-built stage2 trustc" this lane means.
#[test]
fn the_library_opt_in_never_runs_on_the_stage0_seed() {
    for mode in ALL_MODES {
        assert!(!trust_verify_library_units_authorized(*mode, 0), "{mode:?}");
    }
}

#[test]
fn an_unset_opt_in_is_the_only_silent_outcome() {
    assert_eq!(parse_trust_verify_library_request(None), Ok(None));
}

#[test]
fn the_opt_in_accepts_the_named_library_units() {
    assert_eq!(
        parse_trust_verify_library_request(Some(OsStr::new("core"))),
        Ok(Some(vec!["core".to_string()]))
    );
    assert_eq!(
        parse_trust_verify_library_request(Some(OsStr::new(" core , alloc "))),
        Ok(Some(vec!["core".to_string(), "alloc".to_string()]))
    );
    // Cargo spells crate names with underscores; accept either spelling and
    // canonicalize, so `panic-abort` and `panic_abort` cannot disagree.
    assert_eq!(
        parse_trust_verify_library_request(Some(OsStr::new("panic-abort,panic_abort"))),
        Ok(Some(vec!["panic_abort".to_string()]))
    );
    for unit in TRUST_VERIFIABLE_LIBRARY_UNITS {
        assert!(
            parse_trust_verify_library_request(Some(OsStr::new(unit))).is_ok(),
            "allowlisted unit {unit} was rejected"
        );
    }
}

/// A control that is silently ignored is indistinguishable from one that
/// worked. Every degenerate input is an error, not a no-op.
#[test]
fn a_malformed_opt_in_is_an_error_rather_than_a_silent_no_op() {
    for raw in ["", " ", "core,", ",core", "core,,alloc"] {
        assert!(
            parse_trust_verify_library_request(Some(OsStr::new(raw))).is_err(),
            "{raw:?} was accepted"
        );
    }
}

/// The names this must refuse are the whole point of the lane: compiler crates,
/// bootstrap itself, tools, and the third-party crates that the SAME `Mode::Std`
/// cargo invocation compiles alongside `core`.
#[test]
fn the_opt_in_refuses_compiler_bootstrap_tool_and_third_party_units() {
    for raw in [
        "rustc_middle",
        "rustc_driver",
        "bootstrap",
        "compiletest",
        "tidy",
        "compiler_builtins",
        "libc",
        "hashbrown",
        "memchr",
        "rustc_std_workspace_core",
        "all",
        "*",
    ] {
        let error = parse_trust_verify_library_request(Some(OsStr::new(raw)))
            .expect_err(&format!("{raw:?} was accepted as a library unit"));
        assert!(error.contains("not an in-tree `library/` unit"), "{error}");
    }
}

/// SILENT NO-OP REGRESSION. `TRUST_BOOTSTRAP_SHIM_NO_VERIFY_TARGET_ONLY` is
/// retired but still scrubbed in six places, so setting it produced neither an
/// error nor an effect — indistinguishable from a control that worked. It is now
/// refused by name, like `TRUST_FLYWHEEL`, and the message names what to use
/// instead.
#[test]
fn the_retired_target_only_shim_marker_is_refused_not_ignored() {
    assert_eq!(retired_trust_bootstrap_shim_target_only_refusal(None), None);

    // Presence is the trigger: no value can have the effect the name promises.
    for value in ["1", "0", "", "true", "no"] {
        let message = retired_trust_bootstrap_shim_target_only_refusal(Some(OsStr::new(value)))
            .unwrap_or_else(|| panic!("{value:?} was ignored"));
        assert!(message.contains(RETIRED_TRUST_BOOTSTRAP_SHIM_TARGET_ONLY_ENV), "{message}");
        assert!(message.contains("retired"), "{message}");
        // Names the replacements, so the error is a one-line fix.
        assert!(message.contains("TRUST_BOOTSTRAP_SHIM_NO_VERIFY=1"), "{message}");
        assert!(message.contains(TRUST_BOOTSTRAP_VERIFY_LIBRARY_ENV), "{message}");
    }
}

/// The compiler's retired-name wall, read from source. Bootstrap cannot link
/// `rustc_session`, and the point of the pin is the NAMES, which are literal
/// text in that list.
const RUSTC_SESSION_CONFIG_RS: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../compiler/rustc_session/src/config.rs"
));

fn legacy_trust_semantic_env_vars() -> Vec<String> {
    let (_, rest) = RUSTC_SESSION_CONFIG_RS
        .split_once("pub const LEGACY_TRUST_SEMANTIC_ENV_VARS: &[&str] = &[")
        .expect("LEGACY_TRUST_SEMANTIC_ENV_VARS moved or was renamed");
    let (list, _) = rest.split_once("\n];").expect("unterminated LEGACY_TRUST_SEMANTIC_ENV_VARS");
    let names = list
        .lines()
        .filter_map(|line| line.trim().strip_prefix('"'))
        .filter_map(|line| line.split_once('"').map(|(name, _)| name.to_string()))
        .collect::<Vec<_>>();
    assert!(names.len() > 50, "parsed only {} names; the parse broke", names.len());
    names
}

/// `LEGACY_TRUST_SEMANTIC_ENV_VARS` is an EXACT-NAME wall that only fires once
/// Trust IR lowering is on. That makes a collision invisible: a live control
/// whose name is on the list is inert on every bootstrap unit today and turns
/// into an `early_fatal` the first time someone enables verification — i.e.
/// exactly when the new library lane is first used, and nowhere near the change
/// that caused it.
///
/// A PREFIX rule for the retired family would be the fuller fix, but it lives in
/// the compiler and cannot be validated without a stage rebuild. This pins the
/// property that matters and can be measured here: no name bootstrap uses as a
/// LIVE control is on the retired list.
#[test]
fn no_live_bootstrap_control_collides_with_the_retired_trust_env_wall() {
    let retired = legacy_trust_semantic_env_vars();

    for live in [
        // Bootstrap -> shim IPC and the user-facing opt-in.
        "TRUST_BOOTSTRAP_SHIM_NO_VERIFY",
        "TRUST_BOOTSTRAP_SHIM_VERIFY_UNITS",
        TRUST_BOOTSTRAP_VERIFY_LIBRARY_ENV,
        // The version-invariant transport for stage0 seeds, and the quiet-note
        // marker that rides with it.
        "TRUST_NO_VERIFY",
        "TRUST_VANILLA_ANNOUNCED",
        // Frontend authority, and the std lowerability switch.
        "TRUST_TARGO_FRONTEND",
        "TRUST_STD_ENCODE_MIR",
    ] {
        assert!(
            !retired.iter().any(|name| name == live),
            "{live} is a LIVE bootstrap control but is on the compiler's retired-name wall; \
             setting it would become an early_fatal the moment Trust IR lowering is enabled"
        );
    }

    // And the wall really does still contain retired names, so a passing test
    // is evidence about the list rather than about an empty parse.
    assert!(retired.iter().any(|name| name == "TRUST_VERIFY_POLICY"), "{retired:?}");
    assert!(retired.iter().any(|name| name == "TRUST_DISABLE_TV"), "{retired:?}");
}

/// Every `Kind` bootstrap can drive a cargo invocation with. Spelled out rather than derived so
/// a new variant fails to compile here and forces a decision about whether it writes into a std
/// output directory.
const ALL_KINDS: &[Kind] = &[
    Kind::Build,
    Kind::Check,
    Kind::Clippy,
    Kind::Fix,
    Kind::Format,
    Kind::Test,
    Kind::Miri,
    Kind::MiriSetup,
    Kind::MiriTest,
    Kind::Bench,
    Kind::Doc,
    Kind::Clean,
    Kind::Dist,
    Kind::Install,
    Kind::Run,
    Kind::Setup,
    Kind::Vendor,
];

/// Regression test for the never-cleared `build/<host>/stage2-std`.
///
/// `x.py test --stage 2` builds std units into `stage2-std`, but stage-2 std is UPLIFTED from
/// stage 1 (`Std::should_be_uplifted_from_stage_1`), so a `Mode::Std` + `Kind::Build` cargo is
/// never constructed for that directory. Gating the clear on `Kind::Build` alone therefore left
/// it never cleared, and since Trust's `CFG_VERSION` embeds the git short sha, every commit
/// changed compiler identity and stranded artifacts there. Measured 2026-08-24: the release
/// gate's log carried 16x `E0514: found crate 'core' compiled by an incompatible version of
/// rustc`, each followed by `cannot resolve a prelude import`.
#[test]
fn std_out_dir_is_cleared_for_test_not_only_build() {
    // The bug: `Kind::Test` used to answer `false` here, so `stage2-std` was never cleared.
    assert!(
        std_out_dir_needs_clear(Mode::Std, Kind::Test),
        "x.py test --stage 2 builds std units into stage2-std, which no Kind::Build cargo ever \
         targets (stage-2 std is uplifted); not clearing strands artifacts built by a rustc with \
         a different CFG_VERSION and yields E0514 on core"
    );
    assert!(std_out_dir_needs_clear(Mode::Std, Kind::Build), "upstream's original case");
}

#[test]
fn std_out_dir_clear_is_confined_to_std_and_to_building_kinds() {
    // Non-std modes are Cargo's business: it can see those dependencies via depdep info.
    for &mode in ALL_MODES {
        for &kind in ALL_KINDS {
            if mode == Mode::Std {
                continue;
            }
            assert!(
                !std_out_dir_needs_clear(mode, kind),
                "{mode:?} + {kind:?} must not clear a std out dir; only Mode::Std has the \
                 rustc-identity problem bootstrap has to solve on Cargo's behalf"
            );
        }
    }

    // Within Mode::Std, only the kinds that actually compile std units clear. Widening this
    // would delete artifacts a read-only kind is about to report on.
    for &kind in ALL_KINDS {
        let expected = matches!(kind, Kind::Build | Kind::Test);
        assert_eq!(
            std_out_dir_needs_clear(Mode::Std, kind),
            expected,
            "Mode::Std + {kind:?}: a kind that writes std units must clear, one that does not \
             must leave the directory alone"
        );
    }
}

/// Trust: `trust_verifier_controls` must parse the `\x1f`-JOINED form, not only
/// the whitespace form.
///
/// `Rustflags::arg` joins with the ASCII unit separator — it asserts no argument
/// contains one, precisely because that byte IS the separator. `split_whitespace`
/// does not treat `\x1f` as whitespace (U+001F is not in Unicode's White_Space
/// set), so the old implementation collapsed an entire `Rustflags` value into a
/// single unrecognizable token and returned an EMPTY control list no matter what
/// the flags actually said.
///
/// This survived because every existing test fed it the whitespace form, which
/// parsed correctly. The production callers feed it `Rustflags.0`, which does not.
///
/// Two things were blind as a result, and both are asserted below:
///   * the already-present check, which then added a SECOND `-Ztrust-verify=off`
///     — a repeated rustflag forks the cargo unit, because rustflags feed cargo's
///     `unit_id` but not its `c_metadata`;
///   * `rustflags_request_bootstrap_verification`, the self-proof refusal, whose
///     whole job is to notice a verifier control in bootstrap's own rustflags.
#[test]
fn trust_verifier_controls_parses_the_unit_separator_form() {
    // Exactly how `Rustflags` stores it.
    let joined = "-Zannotate-moves\u{1f}--check-cfg=cfg(bootstrap)\u{1f}-Ztrust-verify=off";
    assert_eq!(
        trust_verifier_controls(joined),
        vec![TRUST_BOOTSTRAP_NO_VERIFY_OPTION],
        "a \\x1f-joined Rustflags value must parse; returning [] here is what made the \
         already-present check add a duplicate flag and fork the std unit"
    );

    // The whitespace form (an inherited `RUSTFLAGS`) must keep working.
    let spaced = "-Zannotate-moves --check-cfg=cfg(bootstrap) -Ztrust-verify=off";
    assert_eq!(trust_verifier_controls(spaced), vec![TRUST_BOOTSTRAP_NO_VERIFY_OPTION]);

    // The consequence that mattered: with the flag already present, the default
    // must NOT add a second copy.
    assert!(
        !bootstrap_disables_default_trust_verification(1, joined),
        "the flag is already in these rustflags, so the default must not re-add it — \
         observed as `stage=1 present=1 add=true` before this fix"
    );
    // ...and with it absent, it still must.
    assert!(bootstrap_disables_default_trust_verification(
        1,
        "-Zannotate-moves\u{1f}--check-cfg=cfg(bootstrap)"
    ));

    // The self-proof refusal must see a REAL verifier request in the joined form.
    assert!(
        rustflags_request_bootstrap_verification("-Zannotate-moves\u{1f}-Ztrust-verify=on"),
        "the refusal exists to notice exactly this, and could not"
    );
    assert!(!rustflags_request_bootstrap_verification(joined), "the off-switch is not a request");
}

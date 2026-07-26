//! Driver-level admission of the Trust option surface: which `-Z` domains
//! are self-consistent, which require an authenticated channel, and which
//! a frontend embedding the driver may never assert. Each case names a way
//! a caller could otherwise acquire evidence authority it was not granted.

use std::ffi::{OsStr, OsString};
use std::path::PathBuf;

use rustc_session::config;
use rustc_session::config::{LEGACY_TRUST_SEMANTIC_ENV_VARS, TrustFrontendAuthoritySnapshot};
use rustc_session::getopts;

use super::{
    FrontendTrustPolicy, apply_trust_verify_override,
    authenticated_pre_analysis_exit_message, authenticated_pre_session_early_exit,
    canonicalize_trust_options, compiler_arguments, direct_ir_pre_typed_options_early_exit,
    frontend_forbidden_option, no_trust_evidence_callback_backend_error,
    trust_verify_override_requested, raw_outer_direct_ir_publication_identity,
    should_preflight_direct_ir_publication, trust_callback_changed_contract_checks,
    trust_dump_domain_error, trust_ir_lower_is_active, trust_option_domain_error,
    trust_semantics_are_active, trust_strict_policy_is_active, trust_strict_policy_option_error,
    trust_targo_test_monitor_domain_error, trust_targo_test_monitor_sysroot_error,
};

#[test]
#[allow(rustc::bad_opt_access)]
fn targo_test_monitor_option_requires_its_startup_nonce_channel() {
    let mut opts = rustc_session::config::Options::default();
    opts.unstable_opts.trust_verify_session = Some("monitor-session".to_string());
    opts.unstable_opts.trust_targo_test_monitor = true;
    assert!(
        trust_targo_test_monitor_domain_error(&opts, None)
            .expect("direct option use must fail")
            .contains("cannot be selected directly")
    );
    assert_eq!(
        trust_targo_test_monitor_domain_error(&opts, Some(OsStr::new("monitor-session")),),
        None
    );
    assert!(
        trust_targo_test_monitor_domain_error(&opts, Some(OsStr::new("stale-session")))
            .expect("stale marker must fail")
            .contains("does not match")
    );
    assert!(
        trust_targo_test_monitor_domain_error(&opts, Some(OsStr::new(" monitor-session")))
            .expect("padded marker must fail")
            .contains("padded")
    );
}

#[test]
#[allow(rustc::bad_opt_access)]
fn targo_test_monitor_pins_the_running_compiler_sysroot() {
    let mut opts = rustc_session::config::Options::default();
    opts.unstable_opts.trust_targo_test_monitor = true;
    assert_eq!(trust_targo_test_monitor_sysroot_error(&opts), None);

    opts.sysroot.explicit = Some(PathBuf::from("/attacker/fake-sysroot"));
    assert!(
        trust_targo_test_monitor_sysroot_error(&opts)
            .expect("a caller sysroot must not become monitor TCB")
            .contains("authenticated sysroot")
    );

    opts.sysroot.explicit = Some(opts.sysroot.default.clone());
    assert_eq!(
        trust_targo_test_monitor_sysroot_error(&opts),
        None,
        "bootstrap may spell the compiler's exact default sysroot explicitly"
    );
}

fn parsed_matches(args: &[&str]) -> (Vec<String>, getopts::Matches) {
    let args = args.iter().map(|arg| (*arg).to_string()).collect::<Vec<_>>();
    let mut options = getopts::Options::new();
    for option in rustc_session::config::rustc_optgroups() {
        option.apply(&mut options);
    }
    let matches = options.parse(&args).expect("test compiler arguments must parse");
    (args, matches)
}

#[test]
fn authenticated_session_rejects_every_pre_session_success_exit_before_printing() {
    const CASES: &[(&str, &[&str])] = &[
        ("short help", &["-Ztrust-verify-session=s", "-h"]),
        ("long help", &["-Ztrust-verify-session=s", "--help"]),
        ("unstable help", &["-Ztrust-verify-session=s", "-Zhelp"]),
        ("codegen help", &["-Ztrust-verify-session=s", "-Chelp"]),
        ("pass listing", &["-Ztrust-verify-session=s", "-Cpasses=list"]),
        ("short version", &["-Ztrust-verify-session=s", "-V"]),
        ("verbose version", &["-Ztrust-verify-session=s", "-vV"]),
        ("long version", &["-Ztrust-verify-session=s", "--version"]),
        ("wall help", &["-Ztrust-verify-session=s", "-Wall"]),
        ("lint help", &["-Ztrust-verify-session=s", "-Whelp"]),
        ("allow-lint help", &["-Ztrust-verify-session=s", "-Ahelp"]),
        ("deny-lint help", &["-Ztrust-verify-session=s", "-Dhelp"]),
        ("forbid-lint help", &["-Ztrust-verify-session=s", "-Fhelp"]),
        ("force-warn lint help", &["-Ztrust-verify-session=s", "--force-warn=help"]),
        ("error explanation", &["-Ztrust-verify-session=s", "--explain", "E0001"]),
    ];

    for &(label, args) in CASES {
        let (args, matches) = parsed_matches(args);
        assert!(
            authenticated_pre_session_early_exit(&matches, &args).is_some(),
            "authenticated {label} escaped the pre-print guard"
        );
    }

    let (normal_args, normal) =
        parsed_matches(&["-Ztrust_verify_session=s", "input.rs", "--crate-type=lib"]);
    assert_eq!(authenticated_pre_session_early_exit(&normal, &normal_args), None);

    let (ordinary_args, ordinary) = parsed_matches(&["--help"]);
    assert_eq!(
        authenticated_pre_session_early_exit(&ordinary, &ordinary_args),
        None,
        "ordinary rustc help must retain upstream behavior"
    );
}

#[test]
fn direct_ir_publication_rejects_only_exits_before_typed_target_validation() {
    const UNTYPED_CASES: &[(&str, &[&str])] = &[
        ("short help", &["-Ztrust-dump=ir:ir", "-h"]),
        ("long help", &["-Ztrust-dump=ir:ir", "--help"]),
        ("unstable help", &["-Ztrust-dump=ir:ir", "-Zhelp"]),
        ("codegen help", &["-Ztrust-dump=ir:ir", "-Chelp"]),
        ("pass listing", &["-Ztrust-dump=ir:ir", "-Cpasses=list"]),
        ("version", &["-Ztrust-dump=ir:ir", "--version"]),
        ("wall help", &["-Ztrust-dump=ir:ir", "-Wall"]),
    ];

    for &(label, args) in UNTYPED_CASES {
        let (args, matches) = parsed_matches(args);
        assert!(
            direct_ir_pre_typed_options_early_exit(&matches, &args).is_some(),
            "direct-TrustIR {label} escaped the raw pre-typed guard"
        );
    }

    for args in [
        &["-Ztrust-dump=ir:ir", "-Whelp"][..],
        &["-Ztrust-dump=ir:ir", "--explain=E0001"][..],
        &["-Ztrust-dump=ir:ir", "input.rs"][..],
    ] {
        let (args, matches) = parsed_matches(args);
        assert_eq!(
            direct_ir_pre_typed_options_early_exit(&matches, &args),
            None,
            "typed publication mode must reach target invalidation"
        );
    }

    let (ordinary_args, ordinary) = parsed_matches(&["--version"]);
    assert_eq!(
        direct_ir_pre_typed_options_early_exit(&ordinary, &ordinary_args),
        None,
        "ordinary rustc version output must retain upstream behavior"
    );
}

#[test]
fn direct_ir_publication_identity_is_known_before_response_file_io() {
    let args = [
        "trustc",
        "-Ztrust-verify=off",
        "-Ztrust-ir-lower",
        "-Ztrust-dump=ir:publication",
        "--crate-name",
        "publication_probe",
        "@definitely-missing.args",
    ]
    .map(str::to_string);
    let identity = raw_outer_direct_ir_publication_identity(&args)
        .expect("outer publication authority must parse")
        .expect("complete outer authority must be discovered");
    assert_eq!(identity.directory, std::path::PathBuf::from("publication"));
    assert_eq!(identity.crate_name, "publication_probe");

    let clustered = [
        "trustc",
        "-vZtrust-dump=ir:clustered-publication",
        "--crate-name=clustered_probe",
        "@definitely-missing.args",
    ]
    .map(str::to_string);
    let identity = raw_outer_direct_ir_publication_identity(&clustered)
        .expect("clustered outer publication authority must parse")
        .expect("clustered -Z authority must be discovered");
    assert_eq!(identity.directory, std::path::PathBuf::from("clustered-publication"));
    assert_eq!(identity.crate_name, "clustered_probe");
}

#[test]
fn response_files_cannot_own_direct_ir_publication_identity() {
    let response_only = ["trustc", "@publication.args"].map(str::to_string);
    assert_eq!(
        raw_outer_direct_ir_publication_identity(&response_only)
            .expect("an opaque response file is not outer authority"),
        None,
    );

    let response_crate_name =
        ["trustc", "-Ztrust-dump=ir:publication", "--crate-name", "@crate-name.args"]
            .map(str::to_string);
    let error = raw_outer_direct_ir_publication_identity(&response_crate_name)
        .expect_err("crate identity in a response file must be rejected");
    assert!(error.contains("literal outer argument"));
}

#[test]
fn semantic_separator_hides_direct_ir_publication_controls() {
    let args = [
        "trustc",
        "input.rs",
        "--",
        "-Ztrust-dump=ir:publication",
        "--crate-name=publication_probe",
    ]
    .map(str::to_string);
    assert_eq!(
        raw_outer_direct_ir_publication_identity(&args)
            .expect("free arguments after -- must parse"),
        None,
    );
}

#[test]
fn publication_preflight_is_scoped_to_evidence_capable_response_file_expansion() {
    let args = [
        "trustc",
        "-Ztrust-dump=ir:publication",
        "--crate-name=publication_probe",
        "@arguments",
    ]
    .map(str::to_string);
    assert!(should_preflight_direct_ir_publication(
        FrontendTrustPolicy::CanonicalTrustc,
        true,
        &args,
    ));
    assert!(!should_preflight_direct_ir_publication(
        FrontendTrustPolicy::EmbeddedNoOfficialEvidence,
        true,
        &args,
    ));
    assert!(!should_preflight_direct_ir_publication(
        FrontendTrustPolicy::EvidenceInert,
        true,
        &args,
    ));
    assert!(!should_preflight_direct_ir_publication(
        FrontendTrustPolicy::CanonicalTrustc,
        false,
        &args,
    ));
}

#[test]
fn ordinary_invalid_arguments_never_enter_publication_preflight() {
    let args = ["trustc", "--definitely-not-a-rustc-option", "@arguments"].map(str::to_string);
    assert_eq!(
        raw_outer_direct_ir_publication_identity(&args)
            .expect("ordinary arguments must bypass publication parsing"),
        None,
    );
}

#[test]
fn authenticated_session_rejects_both_pre_analysis_callback_stop_stages() {
    for stage in ["Callbacks::after_crate_root_parsing", "Callbacks::after_expansion"] {
        let message = authenticated_pre_analysis_exit_message(Some("session"), stage)
            .expect("authenticated callback stop must be rejected");
        assert!(message.contains(stage));
    }
    assert_eq!(
        authenticated_pre_analysis_exit_message(None, "Callbacks::after_crate_root_parsing"),
        None,
        "ordinary callback-based frontends retain upstream Stop behavior"
    );
}

#[test]
#[allow(rustc::bad_opt_access)]
fn callback_authority_preserves_legitimate_unrelated_configuration() {
    let baseline = rustc_session::config::Options::default();
    let authority = TrustFrontendAuthoritySnapshot::capture(&baseline);
    let mut configured = baseline;
    // Tippy legitimately owns these non-Trust MIR/lint-facing controls.
    configured.unstable_opts.mir_opt_level = Some(0);
    configured.unstable_opts.mir_enable_passes =
        vec![("CheckNull".to_string(), false), ("CheckAlignment".to_string(), false)];
    configured.unstable_opts.flatten_format_args = false;
    // This inherited upstream field is not unconditionally callback
    // authority. The conditional seam below rejects changes only while
    // Trust semantics are active, preserving vanilla compatibility.
    configured.unstable_opts.contract_checks = Some(true);
    configured.trimmed_def_paths = true;
    assert_eq!(authority.changed_option(&configured), None);
}

#[test]
#[allow(rustc::bad_opt_access)]
fn callback_cannot_set_or_erase_retired_contract_checks_in_trust_mode() {
    let mut trust_set = rustc_session::config::Options::default();
    assert!(trust_semantics_are_active(&trust_set));
    trust_set.unstable_opts.contract_checks = Some(true);
    assert!(trust_callback_changed_contract_checks(None, &trust_set));

    let mut trust_clear = rustc_session::config::Options::default();
    trust_clear.unstable_opts.contract_checks = Some(false);
    let command_line_value = trust_clear.unstable_opts.contract_checks;
    trust_clear.unstable_opts.contract_checks = None;
    assert!(trust_callback_changed_contract_checks(command_line_value, &trust_clear));

    for (command_line_value, callback_value) in
        [(None, Some(true)), (Some(false), None), (Some(true), Some(false))]
    {
        let mut vanilla = rustc_session::config::Options::default();
        vanilla.unstable_opts.trust_verify = config::TrustVerify::Off;
        vanilla.unstable_opts.contract_checks = callback_value;
        assert!(!trust_semantics_are_active(&vanilla));
        assert!(
            !trust_callback_changed_contract_checks(command_line_value, &vanilla),
            "explicit vanilla frontends retain upstream contract-checks callback compatibility"
        );
    }
}

#[test]
#[allow(rustc::bad_opt_access)]
fn callback_injected_trust_option_domains_fail_closed() {
    let valid = rustc_session::config::Options::default();
    assert_eq!(trust_option_domain_error(&valid), None);

    let mut invalid = valid.clone();
    invalid.unstable_opts.trust_verify_timeout_ms = 0;
    assert!(trust_option_domain_error(&invalid).is_some());
    invalid = valid.clone();
    invalid.unstable_opts.trust_verify_worker_threads = 257;
    assert!(trust_option_domain_error(&invalid).is_some());
    invalid = valid.clone();
    invalid.unstable_opts.trust_verify_level = 3;
    assert!(trust_option_domain_error(&invalid).is_some());
    invalid = valid.clone();
    invalid.unstable_opts.trust_cg_output_gate = "bogus".to_string();
    assert!(trust_option_domain_error(&invalid).is_some());
    invalid = valid.clone();
    invalid.unstable_opts.trust_verify_output = "jsonl".to_string();
    assert!(trust_option_domain_error(&invalid).is_some());
    invalid = valid.clone();
    invalid.unstable_opts.trust_certified_test_monitors = true;
    assert_eq!(
        trust_option_domain_error(&invalid),
        Some(
            "-Ztrust-certified-test-monitors requires Targo's authenticated tracked -Ztrust-targo-test-monitor selection"
        )
    );
    invalid.unstable_opts.trust_verify = config::TrustVerify::Off;
    assert_eq!(
        trust_option_domain_error(&invalid),
        Some(
            "-Ztrust-certified-test-monitors requires full Trust verification; it cannot be combined with -Ztrust-verify=off"
        )
    );
    let mut monitor_subject = valid.clone();
    monitor_subject.unstable_opts.trust_certified_test_monitors = true;
    monitor_subject.unstable_opts.trust_verify_session = Some("session".to_string());
    monitor_subject.unstable_opts.trust_verify_package_name = Some("pkg".to_string());
    monitor_subject.unstable_opts.trust_verify_crate_role = "dependency".to_string();
    assert_eq!(
        trust_option_domain_error(&monitor_subject),
        Some(
            "-Ztrust-certified-test-monitors requires Targo's authenticated tracked -Ztrust-targo-test-monitor selection"
        )
    );
    monitor_subject.unstable_opts.trust_targo_test_monitor = true;
    assert_eq!(trust_option_domain_error(&monitor_subject), None);
    let mut harnessless_root = monitor_subject.clone();
    harnessless_root.unstable_opts.trust_verify_crate_role = "primary".to_string();
    assert_eq!(trust_option_domain_error(&harnessless_root), None);
    monitor_subject.test = true;
    assert_eq!(
        trust_option_domain_error(&monitor_subject),
        Some(
            "-Ztrust-certified-test-monitors is redundant for a native --test unit, which already enables certified monitors"
        )
    );
    invalid = valid.clone();
    invalid.unstable_opts.trust_verify_crate_role = "workspace".to_string();
    assert!(trust_option_domain_error(&invalid).is_some());
    for role in ["primary", "dependency", "build-script"] {
        invalid = valid.clone();
        invalid.unstable_opts.trust_verify_crate_role = role.to_string();
        assert_eq!(
            trust_option_domain_error(&invalid),
            Some(
                "non-unscoped -Ztrust-verify-crate-role requires both \
                 -Ztrust-verify-package-name and -Ztrust-verify-session"
            )
        );
    }
    invalid = valid.clone();
    invalid.unstable_opts.trust_verify_package_name = Some("pkg".to_string());
    assert_eq!(
        trust_option_domain_error(&invalid),
        Some("-Ztrust-verify-package-name requires -Ztrust-verify-session")
    );
    let mut raw_fresh = valid.clone();
    raw_fresh.unstable_opts.trust_verify_session = Some("session".to_string());
    assert_eq!(
        trust_option_domain_error(&raw_fresh),
        None,
        "an unscoped raw compile may carry only a freshness session"
    );
    for role in ["primary", "dependency", "build-script"] {
        let mut authenticated = valid.clone();
        authenticated.unstable_opts.trust_verify_crate_role = role.to_string();
        authenticated.unstable_opts.trust_verify_package_name = Some("pkg".to_string());
        authenticated.unstable_opts.trust_verify_session = Some("session".to_string());
        assert_eq!(trust_option_domain_error(&authenticated), None, "role={role}");
    }
    invalid = valid.clone();
    invalid.unstable_opts.trust_verify_package_name = Some(" padded ".to_string());
    assert!(trust_option_domain_error(&invalid).is_some());
    invalid = valid;
    invalid.unstable_opts.trust_verify_ay_path = Some(std::path::PathBuf::new());
    assert!(trust_option_domain_error(&invalid).is_some());
}

#[test]
#[allow(rustc::bad_opt_access)]
fn trust_compilations_reject_the_legacy_contract_checks_projection() {
    for requested in [false, true] {
        let mut enabled = rustc_session::config::Options::default();
        enabled.unstable_opts.contract_checks = Some(requested);
        let error = trust_option_domain_error(&enabled)
            .expect("an explicit legacy contract-checks projection must be rejected");
        assert!(error.contains("certified-monitor lane"), "{error}");

        let mut direct_ir = enabled.clone();
        direct_ir.unstable_opts.trust_verify = config::TrustVerify::Off;
        direct_ir.unstable_opts.trust_ir_lower = Some(config::TrustIrLower::On);
        assert!(
            trust_option_domain_error(&direct_ir).is_some(),
            "direct Trust-IR semantics must not regain the legacy exec projection"
        );

        // Keep the inherited upstream option implementation available to
        // the explicit vanilla-compatibility lane. Its syntax/typechecking
        // machinery is not a Trust runtime authority in that mode.
        let mut vanilla = enabled;
        vanilla.unstable_opts.trust_verify = config::TrustVerify::Off;
        assert_eq!(trust_option_domain_error(&vanilla), None);
    }
}

#[test]
#[allow(rustc::bad_opt_access)]
fn link_only_requires_all_trust_semantics_to_be_disabled() {
    let mut opts = rustc_session::config::Options::default();
    opts.unstable_opts.link_only = true;
    assert_eq!(
        trust_option_domain_error(&opts),
        Some(
            "-Zlink-only skips Trust analysis and cannot be combined with batteries-on \
             verification or -Ztrust-ir-lower; rebuild from source or disable all Trust \
             semantics with -Ztrust-verify=off"
        )
    );

    opts.unstable_opts.trust_verify = config::TrustVerify::Off;
    assert_eq!(trust_option_domain_error(&opts), None);

    opts.unstable_opts.trust_ir_lower = Some(config::TrustIrLower::On);
    assert!(
        trust_option_domain_error(&opts).is_some(),
        "-Ztrust-ir-lower remains an analysis request even when verification is disabled"
    );
}

#[test]
#[allow(rustc::bad_opt_access)]
fn authenticated_coverage_session_rejects_compiler_early_exits() {
    let mut opts = rustc_session::config::Options::default();
    opts.unstable_opts.trust_verify_session = Some("authenticated-session".to_string());

    let mut excluded_targo_unit = opts.clone();
    excluded_targo_unit.unstable_opts.trust_verify_crate_role = "dependency".to_string();
    excluded_targo_unit.unstable_opts.trust_verify_package_name = Some("selected".to_string());
    excluded_targo_unit.unstable_opts.trust_verify = config::TrustVerify::Off;
    assert_eq!(
        trust_option_domain_error(&excluded_targo_unit),
        None,
        "Targo-owned non-root units retain the session tuple while the explicit off-switch excludes them from proof scope"
    );

    let mut no_analysis = opts.clone();
    no_analysis.unstable_opts.no_analysis = true;
    assert!(trust_option_domain_error(&no_analysis).is_some());

    let mut parse_only = opts.clone();
    parse_only.unstable_opts.parse_crate_root_only = true;
    assert!(trust_option_domain_error(&parse_only).is_some());

    let mut dump_only = opts.clone();
    dump_only.unstable_opts.trust_dump.mir_only = true;
    dump_only.unstable_opts.trust_dump.mir = Some("authenticated-dump".into());
    dump_only.unstable_opts.trust_policy = config::TrustPolicy::Advisory;
    assert!(trust_option_domain_error(&dump_only).is_some());

    dump_only.unstable_opts.trust_verify_session = None;
    assert_eq!(
        trust_option_domain_error(&dump_only),
        None,
        "raw nonfatal dump-only workflows remain available without authenticated coverage"
    );

    let mut pretty = opts.clone();
    pretty.pretty = Some(rustc_session::config::PpMode::Source(
        rustc_session::config::PpSourceMode::Normal,
    ));
    assert!(trust_option_domain_error(&pretty).is_some());

    let mut lint_help = opts.clone();
    lint_help.describe_lints = true;
    assert!(trust_option_domain_error(&lint_help).is_some());

    let mut print = opts.clone();
    print.prints.push(rustc_session::config::PrintRequest {
        kind: rustc_session::config::PrintKind::Sysroot,
        out: rustc_session::config::OutFileName::Stdout,
        arg: None,
    });
    assert!(trust_option_domain_error(&print).is_some());

    let mut metadata_list = opts.clone();
    metadata_list.unstable_opts.ls.push("crate.rlib".to_string());
    assert!(trust_option_domain_error(&metadata_list).is_some());

    opts.output_types = rustc_session::config::OutputTypes::new(&[(
        rustc_session::config::OutputType::DepInfo,
        None,
    )]);
    assert!(trust_option_domain_error(&opts).is_some());

    let mut unauthenticated = opts;
    unauthenticated.unstable_opts.trust_verify_session = None;
    assert_eq!(
        trust_option_domain_error(&unauthenticated),
        None,
        "ordinary rustc dep-info-only requests retain upstream semantics"
    );
}

#[test]
fn already_expanded_arguments_do_not_expand_a_literal_nested_argfile() {
    let unique = format!(
        "trustc-expanded-args-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("clock must be after the Unix epoch")
            .as_nanos()
    );
    let dir = std::env::temp_dir().join(unique);
    std::fs::create_dir_all(&dir).expect("create argfile test directory");
    let inner = dir.join("inner.args");
    let outer = dir.join("outer.args");
    std::fs::write(&inner, "--crate-name\nincorrectly_expanded_twice\n")
        .expect("write inner argfile");
    let literal_inner = format!("@{}", inner.display());
    std::fs::write(&outer, format!("{literal_inner}\n")).expect("write outer argfile");

    let early_dcx =
        rustc_session::EarlyDiagCtxt::new(rustc_session::config::ErrorOutputType::default());
    let raw = vec!["trustc".to_string(), format!("@{}", outer.display())];
    let expanded_once = compiler_arguments(&early_dcx, &raw, true);
    let mut immutable_snapshot = vec!["trustc".to_string()];
    immutable_snapshot.extend(expanded_once.clone());
    let arguments_executed = compiler_arguments(&early_dcx, &immutable_snapshot, false);
    std::fs::remove_dir_all(&dir).expect("remove argfile test directory");

    assert_eq!(expanded_once, vec![literal_inner]);
    assert_eq!(arguments_executed, expanded_once);
}

#[test]
fn no_verify_deauthorization_never_rewrites_compiler_arguments() {
    let early_dcx =
        rustc_session::EarlyDiagCtxt::new(rustc_session::config::ErrorOutputType::default());
    let raw = ["trustc", "--crate-name", "--", "-Ztrust-verify=on", "--print=cfg"]
        .map(str::to_string);
    let snapshot = compiler_arguments(&early_dcx, &raw, false);
    assert_eq!(
        snapshot,
        raw[1..],
        "a literal `--` consumed as `--crate-name`'s value must not be mistaken for a semantic separator"
    );

    let (_, matches) =
        parsed_matches(&["--crate-name", "--", "-Ztrust-verify=on", "--print=cfg"]);
    let mut typed_dcx =
        rustc_session::EarlyDiagCtxt::new(rustc_session::config::ErrorOutputType::default());
    let mut options = rustc_session::config::build_session_options(&mut typed_dcx, &matches);
    assert!(options.unstable_opts.trust_verify.is_on());
    apply_trust_verify_override(&mut options, true);
    assert_eq!(
        options.unstable_opts.trust_verify,
        config::TrustVerify::Off,
        "the deauthorization-only entry point must override a parsed caller `=on` without changing argv"
    );
}

#[test]
fn inherited_and_frontend_no_verify_requests_are_typed_and_exact() {
    assert!(!trust_verify_override_requested(FrontendTrustPolicy::CanonicalTrustc, None,));
    assert!(!trust_verify_override_requested(
        FrontendTrustPolicy::CanonicalTrustc,
        Some(OsStr::new("true"))
    ));
    assert!(trust_verify_override_requested(
        FrontendTrustPolicy::CanonicalTrustc,
        Some(OsStr::new("1"))
    ));
    for policy in
        [FrontendTrustPolicy::EmbeddedNoOfficialEvidence, FrontendTrustPolicy::EvidenceInert]
    {
        assert!(
            trust_verify_override_requested(policy, None),
            "a deauthorization-only frontend must not depend on ambient state",
        );
    }
}

#[test]
fn deauthorized_frontends_reject_trust_controls_but_only_tippy_rejects_backends() {
    for option in [
        "trust-ir-lower",
        "trust-dump=ir:/tmp/ir",
        "trust-verify-session=proof",
        "trust-verify-output=json",
        "trust-proof-artifact-root=/tmp/proof",
        "trust-dump=mir:/tmp/mir",
        "trust-policy=advisory",
        "trust-cg-output-gate=off",
    ] {
        let (_, matches) = parsed_matches(&["-Z", option]);
        for policy in [
            FrontendTrustPolicy::EmbeddedNoOfficialEvidence,
            FrontendTrustPolicy::EvidenceInert,
        ] {
            assert!(
                frontend_forbidden_option(policy, &matches).is_some(),
                "{} accepted -Z{option}",
                policy.diagnostic_name(),
            );
        }
        assert_eq!(
            frontend_forbidden_option(FrontendTrustPolicy::CanonicalTrustc, &matches),
            None,
        );
    }

    for option in ["codegen-backend=trust-cg", "codegen_backend=llvm"] {
        let (_, matches) = parsed_matches(&["-Z", option]);
        assert_eq!(
            frontend_forbidden_option(
                FrontendTrustPolicy::EmbeddedNoOfficialEvidence,
                &matches,
            ),
            None,
            "embedded tools retain custom-backend compatibility",
        );
        assert!(
            frontend_forbidden_option(FrontendTrustPolicy::EvidenceInert, &matches).is_some(),
            "Tippy's EvidenceInert route must reject -Z{option}",
        );
    }

    for (switch, option, expected) in [
        ("-Z", "llvm-plugins=/tmp/plugin", "-Zllvm-plugins"),
        ("-Z", "llvm_plugins=/tmp/plugin", "-Zllvm-plugins"),
        ("-Z", "autodiff=Enable", "-Zautodiff"),
        ("-Z", "autodiff-post-passes=default<O2>", "-Zautodiff-post-passes"),
        ("-Z", "autodiff_post_passes=default<O2>", "-Zautodiff-post-passes"),
        ("-C", "llvm-args=-load=/tmp/plugin", "-Cllvm-args"),
        ("-C", "llvm_args=-load=/tmp/plugin", "-Cllvm-args"),
    ] {
        let (_, matches) = parsed_matches(&[switch, option]);
        for compatible_policy in [
            FrontendTrustPolicy::CanonicalTrustc,
            FrontendTrustPolicy::EmbeddedNoOfficialEvidence,
        ] {
            assert_eq!(
                frontend_forbidden_option(compatible_policy, &matches),
                None,
                "{} must retain ordinary LLVM-control compatibility",
                compatible_policy.diagnostic_name(),
            );
        }
        assert_eq!(
            frontend_forbidden_option(FrontendTrustPolicy::EvidenceInert, &matches).as_deref(),
            Some(expected),
            "Tippy's EvidenceInert route accepted {switch}{option}",
        );
    }

    // An ordinary command line carries no Trust option at all, and must pass both deauthorized
    // policies.
    let (_, ordinary) = parsed_matches(&["--crate-type=lib", "input.rs"]);
    assert_eq!(
        frontend_forbidden_option(FrontendTrustPolicy::EmbeddedNoOfficialEvidence, &ordinary),
        None,
    );
    assert_eq!(frontend_forbidden_option(FrontendTrustPolicy::EvidenceInert, &ordinary), None,);

    // Trust: `-Ztrust-verify=on` is NOT an ordinary line for a deauthorized frontend. This test
    // asserted that it was, and never ran to find out otherwise: the module did not compile (it
    // used bare `config::` paths with no `use rustc_session::config;`), so the expectation froze
    // at whatever was true when it was written while `frontend_forbidden_option` tightened to a
    // blanket ban on every `-Ztrust-*`. The blanket ban is the correct behaviour — letting a
    // frontend that was stripped of evidence authority turn verification back on is exactly what
    // deauthorization exists to prevent — so the ASSERTION was corrected, not the code.
    let (_, verify_on) = parsed_matches(&["-Ztrust-verify=on", "--crate-type=lib", "input.rs"]);
    assert_eq!(
        frontend_forbidden_option(FrontendTrustPolicy::EmbeddedNoOfficialEvidence, &verify_on)
            .as_deref(),
        Some("-Ztrust-verify"),
    );
    assert_eq!(
        frontend_forbidden_option(FrontendTrustPolicy::EvidenceInert, &verify_on).as_deref(),
        Some("-Ztrust-verify"),
    );

    assert_eq!(
        no_trust_evidence_callback_backend_error(FrontendTrustPolicy::EvidenceInert, true),
        Some(
            "NoTrustEvidence compiler frontend rejects callback-provided codegen backend factories"
        )
    );
    assert_eq!(
        no_trust_evidence_callback_backend_error(
            FrontendTrustPolicy::EmbeddedNoOfficialEvidence,
            true,
        ),
        None,
    );
    assert_eq!(
        no_trust_evidence_callback_backend_error(FrontendTrustPolicy::CanonicalTrustc, true),
        None
    );
}

#[test]
fn non_unicode_inherited_no_verify_is_inert() {
    #[cfg(unix)]
    let value = {
        use std::os::unix::ffi::OsStringExt;
        OsString::from_vec(vec![0xff])
    };
    #[cfg(windows)]
    let value = {
        use std::os::windows::ffi::OsStringExt;
        OsString::from_wide(&[0xd800])
    };
    #[cfg(not(any(unix, windows)))]
    let value = OsString::from("not-1");

    assert!(!trust_verify_override_requested(
        FrontendTrustPolicy::CanonicalTrustc,
        Some(value.as_os_str())
    ));
}

#[test]
#[allow(rustc::bad_opt_access)]
fn raw_default_policy_normalizes_to_the_same_tracked_hash_as_explicit_strict_policy() {
    let mut raw_default = rustc_session::config::Options::default();
    raw_default.cg.overflow_checks = Some(false);
    raw_default.cg.debug_assertions = Some(false);
    raw_default.debug_assertions = false;
    assert_eq!(raw_default.unstable_opts.trust_verify_crate_role, "unscoped");
    assert_eq!(raw_default.unstable_opts.trust_cg_output_gate, "strict");
    canonicalize_trust_options(&mut raw_default);
    assert_eq!(raw_default.unstable_opts.trust_cg_output_gate, "strict");
    assert_eq!(raw_default.unstable_opts.trust_ir_lower, Some(config::TrustIrLower::On));
    assert_eq!(raw_default.cg.overflow_checks, Some(true));
    assert_eq!(raw_default.cg.debug_assertions, Some(true));
    assert!(raw_default.debug_assertions);

    let mut explicit_strict = rustc_session::config::Options::default();
    explicit_strict.unstable_opts.trust_cg_output_gate = "strict".to_string();
    explicit_strict.unstable_opts.trust_ir_lower = Some(config::TrustIrLower::On);
    explicit_strict.cg.overflow_checks = Some(true);
    explicit_strict.cg.debug_assertions = Some(true);
    explicit_strict.debug_assertions = true;
    assert_eq!(raw_default.dep_tracking_hash(true), explicit_strict.dep_tracking_hash(true));

    // trust-cg enforces the strict gate under strict verification whatever the
    // option says, so a looser spelling must not survive into a second hash.
    let mut loosened = rustc_session::config::Options::default();
    loosened.unstable_opts.trust_cg_output_gate = "allow-unknown".to_string();
    canonicalize_trust_options(&mut loosened);
    assert_eq!(loosened.unstable_opts.trust_cg_output_gate, "strict");
    assert_eq!(loosened.dep_tracking_hash(true), explicit_strict.dep_tracking_hash(true));

    // Outside the strict lane the configured gate is the effective gate.
    let mut survey = rustc_session::config::Options::default();
    survey.unstable_opts.trust_policy = config::TrustPolicy::Advisory;
    survey.unstable_opts.trust_cg_output_gate = "allow-unknown".to_string();
    canonicalize_trust_options(&mut survey);
    assert_eq!(survey.unstable_opts.trust_cg_output_gate, "allow-unknown");
}

/// Every combination of `-Ztrust-verify=off` and `-Ztrust-ir-lower`, pinned
/// to the direct frontend it must actually select.
///
/// Two of these carry load: `-Ztrust-verify=off` alone must leave the direct
/// frontend off, because bootstrap and the vanilla-comparison lanes depend
/// on it not running; and `-Ztrust-verify=off -Ztrust-ir-lower` must turn it
/// on, because that pair is the only route to the SAT-perturbation burn-in
/// and to dumping TrustIR without verifying.
#[test]
#[allow(rustc::bad_opt_access)]
fn every_direct_frontend_lane_resolves_to_its_pinned_value() {
    use config::TrustIrLower::{Off as IrOff, On as IrOn, Strict as IrStrict};
    use config::TrustVerify::{Off, On};
    const LANES: &[(config::TrustVerify, Option<config::TrustIrLower>, bool)] = &[
        // verification, requested, direct frontend runs
        (On, None, true),
        (On, Some(IrOn), true),
        // Verification does not make the frontend optional, so an explicit
        // `off` here is inert rather than an off-switch.
        (On, Some(IrOff), true),
        (Off, None, false),
        (Off, Some(IrOn), true),
        (Off, Some(IrOff), false),
        // Trust (A2): `strict` is `on` plus fail-closed reporting, so it runs the frontend in
        // both lanes.
        (On, Some(IrStrict), true),
        (Off, Some(IrStrict), true),
    ];

    for &(verify, requested, expected) in LANES {
        let mut opts = rustc_session::config::Options::default();
        opts.unstable_opts.trust_verify = verify;
        opts.unstable_opts.trust_ir_lower = requested;
        assert_eq!(
            trust_ir_lower_is_active(&opts),
            expected,
            "raw lane trust_verify={verify:?} requested={requested:?}",
        );

        // A `strict` request survives canonicalization; everything else collapses to the
        // resolved on/off answer. Stamping `On` for a strict request would silently drop the
        // fail-closed half while leaving the mode looking enabled.
        let stamped = if requested == Some(IrStrict) {
            IrStrict
        } else if expected {
            IrOn
        } else {
            IrOff
        };
        canonicalize_trust_options(&mut opts);
        assert_eq!(
            opts.unstable_opts.trust_ir_lower,
            Some(stamped),
            "canonicalization must stamp the resolved value, not the request",
        );
        // Canonicalization is what the tracked hash sees, so it has to be a
        // fixed point: a second pass may not move the lane.
        assert_eq!(trust_ir_lower_is_active(&opts), expected);
        canonicalize_trust_options(&mut opts);
        assert_eq!(opts.unstable_opts.trust_ir_lower, Some(stamped));
    }
}

/// A TrustIR dump has a producer in exactly the lanes the direct frontend
/// runs in, and the check must give the same answer before and after
/// canonicalization — it runs on both sides of it.
#[test]
#[allow(rustc::bad_opt_access)]
fn ir_dump_is_accepted_exactly_where_the_direct_frontend_produces_one() {
    for verify in [config::TrustVerify::On, config::TrustVerify::Off] {
        for requested in
            [None, Some(config::TrustIrLower::On), Some(config::TrustIrLower::Off)]
        {
            let mut opts = rustc_session::config::Options::default();
            opts.unstable_opts.trust_verify = verify;
            opts.unstable_opts.trust_ir_lower = requested;
            opts.unstable_opts.trust_dump.ir = Some(std::path::PathBuf::from("ir-dump"));

            let accepted = trust_ir_lower_is_active(&opts);
            assert_eq!(
                trust_dump_domain_error(&opts).is_none(),
                accepted,
                "raw lane trust_verify={verify:?} requested={requested:?}",
            );
            if !accepted {
                continue;
            }
            canonicalize_trust_options(&mut opts);
            assert_eq!(trust_dump_domain_error(&opts), None);
        }
    }
}

/// The spellings that mean one compilation must produce one tracked hash;
/// the ones that mean different compilations must not collide.
#[test]
#[allow(rustc::bad_opt_access)]
fn direct_frontend_spellings_collapse_to_one_tracked_hash_per_compilation() {
    let canonical = |verify: config::TrustVerify, requested: Option<config::TrustIrLower>| {
        let mut opts = rustc_session::config::Options::default();
        opts.unstable_opts.trust_verify = verify;
        opts.unstable_opts.trust_ir_lower = requested;
        canonicalize_trust_options(&mut opts);
        opts.dep_tracking_hash(true)
    };
    use config::TrustIrLower::{Off as IrOff, On as IrOn, Strict as IrStrict};
    use config::TrustVerify::{Off, On};

    let verifying = canonical(On, None);
    assert_eq!(verifying, canonical(On, Some(IrOn)));
    assert_eq!(verifying, canonical(On, Some(IrOff)));
    // Trust (A2): `strict` is a DIFFERENT compilation, not a spelling of the same one — it
    // changes which programs compile, so it must not collapse into the verifying hash.
    assert_ne!(verifying, canonical(On, Some(IrStrict)));

    let vanilla = canonical(Off, None);
    assert_eq!(vanilla, canonical(Off, Some(IrOff)));

    let burn_in = canonical(Off, Some(IrOn));
    assert_ne!(vanilla, burn_in);
    assert_ne!(verifying, vanilla);
    assert_ne!(verifying, burn_in);
}

#[test]
#[allow(rustc::bad_opt_access)]
fn sat_perturbation_requires_an_exact_class_and_the_direct_ir_burn_in_lane() {
    let mut strict = rustc_session::config::Options::default();
    strict.unstable_opts.trust_sat_perturb = Some("enum-reshape".to_string());
    assert_eq!(
        trust_option_domain_error(&strict),
        Some(
            "-Ztrust-sat-perturb is a burn-in-only control and requires \
             -Ztrust-verify=off -Ztrust-ir-lower"
        )
    );

    let mut burn_in = strict.clone();
    burn_in.unstable_opts.trust_verify = config::TrustVerify::Off;
    burn_in.unstable_opts.trust_ir_lower = Some(config::TrustIrLower::On);
    assert_eq!(trust_option_domain_error(&burn_in), None);

    let mut no_direct_ir = burn_in.clone();
    no_direct_ir.unstable_opts.trust_ir_lower = Some(config::TrustIrLower::Off);
    assert!(trust_option_domain_error(&no_direct_ir).is_some());

    let mut evidence_policy = strict.clone();
    evidence_policy.unstable_opts.trust_ir_lower = Some(config::TrustIrLower::On);
    evidence_policy.unstable_opts.trust_policy = config::TrustPolicy::Advisory;
    assert!(trust_option_domain_error(&evidence_policy).is_some());

    for class in [
        "enum-reshape",
        "enum-case-value",
        "enum-ctor",
        "enum-disc-index",
        "switch-map",
        "enum-payload",
    ] {
        let mut valid_class = burn_in.clone();
        valid_class.unstable_opts.trust_sat_perturb = Some(class.to_string());
        assert_eq!(trust_option_domain_error(&valid_class), None, "class={class}");
    }

    let mut unknown = burn_in;
    unknown.unstable_opts.trust_sat_perturb = Some("unknown".to_string());
    assert_eq!(
        trust_option_domain_error(&unknown),
        Some(
            "invalid -Ztrust-sat-perturb value: expected enum-reshape, \
             enum-case-value, enum-ctor, enum-disc-index, switch-map, or enum-payload"
        )
    );
}

#[test]
#[allow(rustc::bad_opt_access)]
fn strict_policy_rejects_disabling_the_codegen_output_gate() {
    let mut strict = rustc_session::config::Options::default();
    strict.unstable_opts.trust_cg_output_gate = "off".to_string();
    assert!(trust_strict_policy_option_error(&strict).is_some());

    strict.unstable_opts.trust_verify = config::TrustVerify::Off;
    assert_eq!(trust_strict_policy_option_error(&strict), None);
}

#[test]
#[allow(rustc::bad_opt_access)]
fn raw_role_metadata_cannot_weaken_batteries_on_scope() {
    for role in ["unscoped", "primary", "dependency", "build-script"] {
        let mut opts = rustc_session::config::Options::default();
        opts.unstable_opts.trust_verify_crate_role = role.to_string();
        opts.unstable_opts.trust_verify_package_name =
            (role != "unscoped").then(|| "pkg".to_string());
        opts.unstable_opts.trust_verify_session =
            (role != "unscoped").then(|| "session".to_string());
        assert!(trust_strict_policy_is_active(&opts), "role={role}");
    }

    let mut explicit_off = rustc_session::config::Options::default();
    explicit_off.unstable_opts.trust_verify_crate_role = "dependency".to_string();
    explicit_off.unstable_opts.trust_verify = config::TrustVerify::Off;
    assert!(!trust_strict_policy_is_active(&explicit_off));
}

#[test]
#[allow(rustc::bad_opt_access)]
fn disabled_verification_preserves_requested_codegen_safety_policy() {
    let mut opts = rustc_session::config::Options::default();
    opts.unstable_opts.trust_verify = config::TrustVerify::Off;
    opts.cg.overflow_checks = Some(false);
    opts.cg.debug_assertions = Some(false);
    opts.debug_assertions = false;

    canonicalize_trust_options(&mut opts);

    assert_eq!(opts.unstable_opts.trust_ir_lower, Some(config::TrustIrLower::Off));
    assert_eq!(opts.cg.overflow_checks, Some(false));
    assert_eq!(opts.cg.debug_assertions, Some(false));
    assert!(!opts.debug_assertions);
}

#[test]
fn legacy_semantic_env_denylist_covers_verdict_and_codegen_inputs() {
    for required in [
        "AY_PATH",
        "TRUST_BACKING_INVARIANTS",
        "TRUST_DUMP_ONLY",
        "TRUST_ELIDE_CERTIFIED_CHECKS",
        "TRUST_IR_FLIP",
        "TRUST_NATIVE_UNIVERSAL",
        "TRUST_SOLVER",
        "TRUST_TEMPORAL_SINGLE_WRITER",
        "TRUST_VERIFY_MEMORY_SAFE",
        "TRUST_VERIFY_POLICY",
        "TRUST_VERIFY_TIMEOUT_MS",
        "TRUST_WP_PATH",
        "TY_PATH",
    ] {
        assert!(
            LEGACY_TRUST_SEMANTIC_ENV_VARS.contains(&required),
            "missing legacy semantic input {required}"
        );
    }
}

#[test]
fn diagnostic_only_env_remains_available() {
    for diagnostic in
        ["TRUST_ASSERT_DEBUG", "TRUST_NATIVE_DEBUG", "TRUST_VERIFY_TRACE_CERTIFIED"]
    {
        assert!(!LEGACY_TRUST_SEMANTIC_ENV_VARS.contains(&diagnostic));
    }
}

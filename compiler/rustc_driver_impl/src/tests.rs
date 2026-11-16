//! Driver-level admission of the Trust option surface: which `-Z` domains
//! are self-consistent, which require an authenticated channel, and which
//! a frontend embedding the driver may never assert. Each case names a way
//! a caller could otherwise acquire evidence authority it was not granted.

// Trust: use the maintained compiletest native-entry pattern before libtest setup.
#[cfg(any(target_os = "linux", target_os = "macos"))]
extern crate test;

/// Trust: generated main constructs only static test references before this call;
/// capture must precede libtest argument handling, file opens and worker threads.
/// These tests run the compiler in process, so under `build-slot` protocol 1 the
/// binary lends it its own execution (CUSTODY-EMBEDDED-TEST-LOAN-1).
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(super) fn native_test_main(tests: &[&test::TestDescAndFn]) {
    // SAFETY: first generated native-entry operation, before arbitrary callbacks.
    if let Err(error) =
        unsafe { rustc_data_structures::jobserver::capture_early_for_test_harness() }
    {
        eprintln!("driver unit entry: inherited compiler scheduler refused: {error}");
        std::process::exit(75);
    }
    #[cfg(panic = "unwind")]
    let result = test::test_main_env_args(tests);
    #[cfg(not(panic = "unwind"))]
    let result = test::test_main_env_args_abort(tests);
    // Trust: custom runners return unit; preserve libtest's actual exit code.
    result.exit_process();
}

/// Trust (CUSTODY-EMBEDDED-TEST-LOAN-1): this binary's native entry lends its
/// in-process compiles its own execution exactly when it is owed one (a bare
/// `build-slot` protocol-1 run), and then one test at a time.
#[cfg(any(target_os = "linux", target_os = "macos"))]
#[test]
fn the_native_entry_lends_its_own_execution_exactly_when_owed() {
    use rustc_data_structures::jobserver;
    if jobserver::own_execution_owed() {
        assert!(jobserver::lends_own_execution(), "an owed run captured no loan");
        assert_eq!(std::env::var("RUST_TEST_THREADS").as_deref(), Ok("1"));
    } else {
        assert!(!jobserver::lends_own_execution(), "a run that is not owed one was lent");
    }
}

// Trust: real source Freeze controls use the canonical in-process compiler owner.
mod shared_receiver_freeze;
// Trust: real constructor source admission must retain transient extraction metadata.
mod constructor_return_admission;
// Trust: actual compiler phases, terminal dep-info and native-link controls.
mod tool_inputs;

use std::ffi::{OsStr, OsString};
use std::path::PathBuf;

use rustc_session::config::{LEGACY_TRUST_SEMANTIC_ENV_VARS, TrustFrontendAuthoritySnapshot};
use rustc_session::{config, getopts};

use super::{
    FrontendTrustPolicy, apply_trust_verify_override, authenticated_pre_analysis_exit_message,
    authenticated_pre_session_early_exit, canonicalize_trust_options, compiler_arguments,
    direct_ir_pre_typed_options_early_exit, frontend_forbidden_option,
    no_trust_evidence_callback_backend_error, private_fixed_pre_session_exit,
    raw_outer_direct_ir_publication_identity, should_preflight_direct_ir_publication,
    trust_callback_changed_contract_checks, trust_dump_domain_error, trust_ir_lower_is_active,
    trust_option_domain_error, trust_semantics_are_active, trust_strict_policy_is_active,
    trust_strict_policy_option_error, trust_targo_test_monitor_domain_error,
    trust_targo_test_monitor_sysroot_error, trust_verify_override_requested,
};

// Trust: even callback-written resource metadata must be a complete canonical binding.
#[test]
#[allow(rustc::bad_opt_access)]
fn native_admission_context_is_all_or_none_and_cargo_scoped() {
    let mut valid = config::Options::default();
    valid.unstable_opts.trust_verify_session = Some("session".into());
    valid.unstable_opts.trust_verify_package_name = Some("demo".into());
    valid.unstable_opts.trust_verify_crate_role = "primary".into();
    valid.unstable_opts.trust_admission_run_digest = Some("a".repeat(64));
    valid.unstable_opts.trust_admission_unit_digest = Some("b".repeat(64));
    valid.unstable_opts.trust_admission_semantics_digest = Some("c".repeat(64));
    valid.unstable_opts.trust_admission_unit_role = Some("primary".into());
    valid.unstable_opts.trust_admission_compile_target = Some("aarch64-apple-darwin".into());
    assert_eq!(trust_option_domain_error(&valid), None);
    for mutation in 0..9 {
        let mut invalid = valid.clone();
        match mutation {
            0 => invalid.unstable_opts.trust_admission_run_digest = None,
            1 => invalid.unstable_opts.trust_admission_unit_digest = Some("B".repeat(64)),
            2 => invalid.unstable_opts.trust_admission_semantics_digest = Some("bad".into()),
            3 => invalid.unstable_opts.trust_admission_unit_role = Some("excluded".into()),
            4 => invalid.unstable_opts.trust_verify_session = None,
            5 => invalid.unstable_opts.trust_verify_crate_role = "unscoped".into(),
            6 => invalid.unstable_opts.trust_admission_compile_target = None,
            7 => invalid.unstable_opts.trust_admission_compile_target = Some(String::new()),
            _ => invalid.unstable_opts.trust_admission_compile_target = Some("x".repeat(4097)),
        }
        assert!(trust_option_domain_error(&invalid).is_some(), "mutation {mutation}");
    }
}

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

/// `frontend_forbidden_option` exactly as the pre-backend check runs it: on the
/// effective configuration the option table's own parser resolves from `matches`.
fn forbidden_in(policy: FrontendTrustPolicy, matches: &getopts::Matches) -> Option<String> {
    let early_dcx =
        rustc_session::EarlyDiagCtxt::new(rustc_session::config::ErrorOutputType::default());
    frontend_forbidden_option(&early_dcx, policy, matches)
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
    let args =
        ["trustc", "-Ztrust-dump=ir:publication", "--crate-name=publication_probe", "@arguments"]
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

/// Trust (T6): every unit of a proof session — verifying, or a
/// verification-off dependency carrying `-Ztrust-verify-session` — refuses each
/// MIR-pipeline option BY NAME, and the vanilla lane (no verification, no
/// session; the direct-trustc UI fixtures' `-Ztrust-verify=off` revisions and
/// every upstream suite) keeps upstream's options.
#[test]
#[allow(rustc::bad_opt_access)]
fn a_proof_session_refuses_each_mir_pipeline_option_by_name() {
    type Set = fn(&mut config::UnstableOptions);
    let cases: [(&str, Set); 9] = [
        ("-Zmir-opt-level", |u| u.mir_opt_level = Some(2)),
        ("-Zinline-mir", |u| u.inline_mir = Some(true)),
        ("-Zinline-mir-threshold", |u| u.inline_mir_threshold = Some(50)),
        ("-Zinline-mir-hint-threshold", |u| u.inline_mir_hint_threshold = Some(100)),
        ("-Zinline-mir-forwarder-threshold", |u| u.inline_mir_forwarder_threshold = Some(30)),
        ("-Zmir-enable-passes", |u| u.mir_enable_passes = vec![("GVN".to_string(), true)]),
        ("-Zmir-opt-bisect-limit", |u| u.mir_opt_bisect_limit = Some(0)),
        ("-Zmir-preserve-ub", |u| u.mir_preserve_ub = true),
        ("-Zmir-strip-debuginfo", |u| u.mir_strip_debuginfo = config::MirStripDebugInfo::AllLocals),
    ];
    for (flag, set) in cases {
        let named = format!("; {flag} would make the verified MIR");
        let mut verifying = rustc_session::config::Options::default();
        assert!(verifying.unstable_opts.trust_verify.is_on(), "verification is the default");
        set(&mut verifying.unstable_opts);
        let error = trust_option_domain_error(&verifying).unwrap_or_else(|| panic!("{flag}"));
        assert!(error.contains(&named) && error.contains("-O0 MIR pipeline"), "{error}");

        let mut dependency = rustc_session::config::Options::default();
        dependency.unstable_opts.trust_verify = config::TrustVerify::Off;
        dependency.unstable_opts.trust_verify_session = Some("proof-session".to_string());
        set(&mut dependency.unstable_opts);
        let error = trust_option_domain_error(&dependency).unwrap_or_else(|| panic!("{flag}"));
        assert!(error.contains(&named), "{error}");

        let mut vanilla = rustc_session::config::Options::default();
        vanilla.unstable_opts.trust_verify = config::TrustVerify::Off;
        set(&mut vanilla.unstable_opts);
        assert_eq!(trust_option_domain_error(&vanilla), None, "vanilla keeps {flag}");
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
    invalid.unstable_opts.trust_verify_effort = 0;
    assert!(trust_option_domain_error(&invalid).is_some());
    invalid = valid.clone();
    invalid.unstable_opts.trust_verify_effort = 100_001;
    assert!(trust_option_domain_error(&invalid).is_some());
    invalid = valid.clone();
    invalid.unstable_opts.trust_verify_function_budget_steps = 0;
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
    invalid.unstable_opts.trust_cg_frontend = "bogus".to_string();
    assert!(trust_option_domain_error(&invalid).is_some());
    invalid = valid.clone();
    // The two admitted spellings must both survive the domain check; `mir` is
    // also the declared default, which `valid` above already exercises.
    invalid.unstable_opts.trust_cg_frontend = "trust-ir".to_string();
    assert_eq!(trust_option_domain_error(&invalid), None);
    // Trust (step 2 increment 5, sub-step 5.4.2): F1's consumer is a closed domain too; both
    // admitted spellings survive (`lir`, the default, through `valid`).
    invalid = valid.clone();
    invalid.unstable_opts.trust_cg_f1_backend = "Compiler".to_string();
    assert_eq!(
        trust_option_domain_error(&invalid),
        Some("invalid callback-injected -Ztrust-cg-f1-backend value")
    );
    invalid = valid.clone();
    invalid.unstable_opts.trust_cg_f1_backend = "compiler".to_string();
    assert_eq!(trust_option_domain_error(&invalid), None);
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
    invalid.unstable_opts.trust_proof_artifact_root = Some(std::path::PathBuf::new());
    assert!(trust_option_domain_error(&invalid).is_some());
}

// Trust (2026-10-03, docs/DECISION_QUEUE.md "L0-CERTIFY"): certify at level 0
// built `pub fn spin() { spin() }` exit 0 (the D9 charge is an L1 obligation the
// level filter dropped). The combination is refused before any session exists;
// certify at levels 1 and 2, and level 0 on every other policy or with
// verification off, stay accepted.
#[test]
#[allow(rustc::bad_opt_access)]
fn certify_is_refused_at_verification_level_zero() {
    let valid = rustc_session::config::Options::default();
    let refusal = "-Ztrust-policy=certify requires -Ztrust-verify-level=1 or 2";

    let mut certify_l0 = valid.clone();
    certify_l0.unstable_opts.trust_policy = config::TrustPolicy::Certify;
    certify_l0.unstable_opts.trust_verify_level = 0;
    let error = trust_option_domain_error(&certify_l0).expect("certify at level 0 is refused");
    assert!(error.starts_with(refusal), "{error}");
    assert!(error.contains("termination"), "the refusal names what level 0 drops: {error}");
    assert!(error.contains("[trust] level"), "the refusal names the targo spelling: {error}");

    for level in [1, 2] {
        let mut certify = valid.clone();
        certify.unstable_opts.trust_policy = config::TrustPolicy::Certify;
        certify.unstable_opts.trust_verify_level = level;
        assert_eq!(trust_option_domain_error(&certify), None, "certify at level {level}");
    }
    for policy in [
        config::TrustPolicy::Strict,
        config::TrustPolicy::Advisory,
        config::TrustPolicy::MemorySafe,
    ] {
        let mut level0 = valid.clone();
        level0.unstable_opts.trust_policy = policy;
        level0.unstable_opts.trust_verify_level = 0;
        assert_eq!(trust_option_domain_error(&level0), None, "{policy:?} at level 0");
    }
    let mut vanilla = certify_l0;
    vanilla.unstable_opts.trust_verify = config::TrustVerify::Off;
    assert_eq!(
        trust_option_domain_error(&vanilla),
        None,
        "with verification off there is no certify verdict to refuse"
    );
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
    pretty.pretty =
        Some(rustc_session::config::PpMode::Source(rustc_session::config::PpSourceMode::Normal));
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
    let raw =
        ["trustc", "--crate-name", "--", "-Ztrust-verify=on", "--print=cfg"].map(str::to_string);
    let snapshot = compiler_arguments(&early_dcx, &raw, false);
    assert_eq!(
        snapshot,
        raw[1..],
        "a literal `--` consumed as `--crate-name`'s value must not be mistaken for a semantic separator"
    );

    let (_, matches) = parsed_matches(&["--crate-name", "--", "-Ztrust-verify=on", "--print=cfg"]);
    let mut typed_dcx =
        rustc_session::EarlyDiagCtxt::new(rustc_session::config::ErrorOutputType::default());
    let mut options = rustc_session::config::build_session_options(&mut typed_dcx, &matches, false);
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
    // Evidence controls: a frontend that produces no evidence can neither honour nor
    // silently drop them (`TrustAuthorityClass::EvidenceControl`).
    for option in [
        "trust-dump=ir:/tmp/ir",
        "trust-verify-session=proof",
        "trust-dump=mir:/tmp/mir",
        "trust-cg-output-gate=off",
        "trust-body-census=/tmp/census",
        "trust-sat-perturb=enum-reshape",
        "trust-targo-test-monitor=yes",
        "trust-witness=off",
    ] {
        let (_, matches) = parsed_matches(&["-Z", option]);
        for policy in
            [FrontendTrustPolicy::EmbeddedNoOfficialEvidence, FrontendTrustPolicy::EvidenceInert]
        {
            assert!(
                forbidden_in(policy, &matches).is_some(),
                "{} accepted -Z{option}",
                policy.diagnostic_name(),
            );
        }
        assert_eq!(forbidden_in(FrontendTrustPolicy::CanonicalTrustc, &matches), None,);
    }

    // `-Ztrust-policy` is a verification selector a deauthorized frontend ACCEPTS: it
    // decides what an ACTIVE verification does with a refutation, and these frontends force
    // `trust_verify = Off` and reset every selector to its default before anything can read
    // it (`TrustFrontendAuthoritySnapshot::deauthorize`; the rest of the selectors are
    // `deauthorized_frontends_accept_a_posture_whose_effective_verification_is_off`).
    // Refusing it made `targo tippy` impossible in every repo
    // that commits the policy in `.cargo/config.toml` rustflags — the sanctioned place for
    // it — which is how the fleet's lint gates died before their first lint (2026-09-11).
    for option in ["trust-policy=advisory", "trust-policy=certify", "trust-policy=strict"] {
        let (_, matches) = parsed_matches(&["-Z", option]);
        for policy in [
            FrontendTrustPolicy::CanonicalTrustc,
            FrontendTrustPolicy::EmbeddedNoOfficialEvidence,
            FrontendTrustPolicy::EvidenceInert,
        ] {
            assert_eq!(
                forbidden_in(policy, &matches),
                None,
                "{} must accept the inert -Z{option}",
                policy.diagnostic_name(),
            );
        }
    }

    // ... and accepting it may never let the caller's value survive.
    for option in ["-Ztrust-policy=advisory", "-Ztrust-policy=certify"] {
        let (_, matches) = parsed_matches(&[option]);
        let mut typed_dcx =
            rustc_session::EarlyDiagCtxt::new(rustc_session::config::ErrorOutputType::default());
        let mut options =
            rustc_session::config::build_session_options(&mut typed_dcx, &matches, false);
        let selected = options.unstable_opts.trust_policy;
        apply_trust_verify_override(&mut options, true);
        assert_eq!(
            options.unstable_opts.trust_verify,
            config::TrustVerify::Off,
            "a deauthorized frontend forces verification off",
        );
        assert_eq!(
            options.unstable_opts.trust_policy,
            config::TrustPolicy::default(),
            "a deauthorized frontend must neutralize the caller's {option} (parsed as {selected:?})",
        );
    }

    for option in ["codegen-backend=trust-cg", "codegen_backend=llvm"] {
        let (_, matches) = parsed_matches(&["-Z", option]);
        assert_eq!(
            forbidden_in(FrontendTrustPolicy::EmbeddedNoOfficialEvidence, &matches,),
            None,
            "embedded tools retain custom-backend compatibility",
        );
        assert!(
            forbidden_in(FrontendTrustPolicy::EvidenceInert, &matches).is_some(),
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
        for compatible_policy in
            [FrontendTrustPolicy::CanonicalTrustc, FrontendTrustPolicy::EmbeddedNoOfficialEvidence]
        {
            assert_eq!(
                forbidden_in(compatible_policy, &matches),
                None,
                "{} must retain ordinary LLVM-control compatibility",
                compatible_policy.diagnostic_name(),
            );
        }
        assert_eq!(
            forbidden_in(FrontendTrustPolicy::EvidenceInert, &matches).as_deref(),
            Some(expected),
            "Tippy's EvidenceInert route accepted {switch}{option}",
        );
    }

    // An ordinary command line carries no Trust option at all, and must pass both deauthorized
    // policies.
    let (_, ordinary) = parsed_matches(&["--crate-type=lib", "input.rs"]);
    assert_eq!(forbidden_in(FrontendTrustPolicy::EmbeddedNoOfficialEvidence, &ordinary), None,);
    assert_eq!(forbidden_in(FrontendTrustPolicy::EvidenceInert, &ordinary), None,);

    // `-Ztrust-verify=on` is not an ordinary line for a deauthorized frontend. Letting a frontend
    // that was stripped of evidence authority turn verification back on is exactly what
    // deauthorization exists to prevent.
    let (_, verify_on) = parsed_matches(&["-Ztrust-verify=on", "--crate-type=lib", "input.rs"]);
    assert_eq!(
        forbidden_in(FrontendTrustPolicy::EmbeddedNoOfficialEvidence, &verify_on).as_deref(),
        Some("-Ztrust-verify"),
    );
    assert_eq!(
        forbidden_in(FrontendTrustPolicy::EvidenceInert, &verify_on).as_deref(),
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

const DEAUTHORIZED_POLICIES: [FrontendTrustPolicy; 2] =
    [FrontendTrustPolicy::EmbeddedNoOfficialEvidence, FrontendTrustPolicy::EvidenceInert];

/// ay's committed verification posture (its `.cargo/config.toml` rustflags), which
/// Cargo hands every unit — including the ones a deauthorized frontend compiles.
const AY_POSTURE: [&str; 6] = [
    "-Ztrust-verify=on",
    "-Ztrust-policy=certify",
    "-Ztrust-verify-level=2",
    "-Ztrust-verify-profile=unix_hardened",
    "-Ztrust-verify-include-dependencies=yes",
    "-Ztrust-ir-lower=strict",
];

fn with_input<'a>(args: &[&'a str]) -> Vec<&'a str> {
    let mut argv = args.to_vec();
    argv.extend(["--crate-type=lib", "input.rs"]);
    argv
}

#[test]
fn deauthorized_frontends_decide_trust_verify_on_its_effective_explicit_value() {
    // The one activation control is judged on its last-wins value. An effective `off`
    // — however it was reached — is what these frontends force anyway, so every
    // spelling of it is accepted; this is what lets a committed `-Ztrust-verify=on`
    // be followed by the `-Ztrust-verify=off` Targo appends for lint and doc passes.
    for args in [
        &["-Ztrust-verify=off"][..],
        &["-Z", "trust-verify=off"][..],
        &["-Z", "trust_verify=off"][..],
        &["-Ztrust-verify=on", "-Ztrust-verify=off"][..],
        &["-Z", "trust-verify=on", "-Z", "trust_verify=off"][..],
        &["-Ztrust-verify=off", "-Ztrust-verify=off"][..],
    ] {
        let (_, matches) = parsed_matches(&with_input(args));
        for policy in DEAUTHORIZED_POLICIES {
            assert_eq!(
                forbidden_in(policy, &matches),
                None,
                "{} refused effective-off {args:?}",
                policy.diagnostic_name(),
            );
        }
    }

    // An EXPLICIT, EFFECTIVE `on` demands verification from a frontend that cannot
    // verify: refused, never silently turned into an unverified compile. (A bare or
    // malformed value never reaches this decision: the option table's parser refuses
    // it first, as `build_session_options` would.)
    for args in [
        &["-Ztrust-verify=on"][..],
        &["-Ztrust-verify=off", "-Ztrust-verify=on"][..],
        &["-Ztrust-verify=on", "-Ztrust-policy=certify"][..],
        &AY_POSTURE[..],
    ] {
        let (_, matches) = parsed_matches(&with_input(args));
        for policy in DEAUTHORIZED_POLICIES {
            assert_eq!(
                forbidden_in(policy, &matches).as_deref(),
                Some("-Ztrust-verify"),
                "{} accepted an effective explicit verification request {args:?}",
                policy.diagnostic_name(),
            );
        }
        assert_eq!(forbidden_in(FrontendTrustPolicy::CanonicalTrustc, &matches), None);
    }
}

/// The effective decision parses the classified Trust controls ONLY. Any other `-Z`
/// value — `help`, whose early mode `handle_help` answers after this check, or an
/// option the full parse would warn about — is left to the one full parse the
/// compilation runs, so interleaving it with a posture changes nothing here (a parse
/// of the whole `-Z` list would die on `help` as an unknown option).
#[test]
fn the_effective_decision_parses_only_the_trust_authority_controls() {
    for args in [
        &["-Ztrust-verify=on", "-Zhelp", "-Ztrust-verify=off"][..],
        &["-Zhelp", "-Ztrust-policy=certify"][..],
        &["-Z", "help", "-Z", "trust-ir-lower=strict", "-Z", "trust-verify=off"][..],
    ] {
        let (_, matches) = parsed_matches(args);
        for policy in DEAUTHORIZED_POLICIES {
            assert_eq!(forbidden_in(policy, &matches), None, "{args:?}");
        }
    }
    let (_, matches) = parsed_matches(&["-Ztrust-verify=off", "-Zhelp", "-Ztrust-verify=on"]);
    for policy in DEAUTHORIZED_POLICIES {
        assert_eq!(forbidden_in(policy, &matches).as_deref(), Some("-Ztrust-verify"));
    }

    // The parser reports exactly the classified fields it met, once each.
    let (_, matches) = parsed_matches(&[
        "-Ztrust-verify=on",
        "-Zhelp",
        "-Ztrust_policy=certify",
        "-Ztrust-verify=off",
        "-Zcodegen-backend=llvm",
    ]);
    let early_dcx =
        rustc_session::EarlyDiagCtxt::new(rustc_session::config::ErrorOutputType::default());
    let (effective, spelled) =
        rustc_session::config::UnstableOptions::build_trust_authority_controls(
            &early_dcx, &matches,
        );
    assert_eq!(spelled, ["trust_verify", "trust_policy", "codegen_backend"]);
    assert_eq!(effective.trust_verify, config::TrustVerify::Off);
    assert_eq!(effective.trust_policy, config::TrustPolicy::Certify);
}

/// The bootstrap-only `-Zno-trust-verify` alias (compiled only into a stage0-built
/// compiler) is a spelling of `trust_verify` with the retired option's INVERTED
/// meaning, resolved by the same parser: `=no` asks for verification and must be
/// refused like `-Ztrust-verify=on`, while bare `-Zno-trust-verify` is an off-switch.
#[cfg(bootstrap)]
#[test]
fn the_bootstrap_no_trust_verify_alias_is_judged_by_its_resolved_value() {
    for (args, expected) in [
        (&["-Zno-trust-verify=no"][..], Some("-Ztrust-verify")),
        (&["-Ztrust-verify=off", "-Zno-trust-verify=off"][..], Some("-Ztrust-verify")),
        (&["-Zno-trust-verify"][..], None),
        (&["-Zno-trust-verify=no", "-Ztrust-verify=off"][..], None),
        (&["-Ztrust-verify=on", "-Zno-trust-verify=yes"][..], None),
    ] {
        let (_, matches) = parsed_matches(&with_input(args));
        for policy in DEAUTHORIZED_POLICIES {
            assert_eq!(forbidden_in(policy, &matches).as_deref(), expected, "{args:?}");
        }
    }
}

/// The shapes measured refused on seal 7d5533b2 (tippy-driver and trustdoc alike),
/// ay's exact posture followed by the off-switch, and every verification selector at
/// a non-default value: all resolve to verification off and carry no evidence
/// control, so both deauthorized routes accept them.
#[test]
fn deauthorized_frontends_accept_a_posture_whose_effective_verification_is_off() {
    let mut ay_then_off = AY_POSTURE.to_vec();
    ay_then_off.push("-Ztrust-verify=off");
    let accepted: Vec<Vec<&str>> = vec![
        vec!["-Ztrust-verify=on", "-Ztrust-verify=off"],
        vec!["-Ztrust-policy=certify", "-Ztrust-verify=off"],
        vec!["-Ztrust-verify-level=2", "-Ztrust-verify=off"],
        vec!["-Ztrust-verify-level=0", "-Ztrust-verify=off"],
        vec!["-Ztrust-ir-lower=strict", "-Ztrust-verify=off"],
        vec!["-Ztrust-ir-lower", "-Ztrust-verify=off"],
        vec!["-Ztrust-verify-profile=unix_hardened", "-Ztrust-verify=off"],
        vec!["-Ztrust-verify-include-dependencies=yes", "-Ztrust-verify=off"],
        vec!["-Ztrust-verify-timeout-ms=1", "-Ztrust-verify=off"],
        vec!["-Ztrust-verify-worker-threads=1", "-Ztrust-verify=off"],
        vec!["-Ztrust-verify-function-budget-ms=1", "-Ztrust-verify=off"],
        vec!["-Ztrust-verify-function-budget-steps=1", "-Ztrust-verify=off"],
        vec!["-Ztrust-verify-effort=1", "-Ztrust-verify=off"],
        vec!["-Ztrust-verify-output=json", "-Ztrust-verify=off"],
        vec!["-Ztrust-no-adapter-yield", "-Ztrust-verify=off"],
        vec!["-Ztrust-no-r1", "-Ztrust-verify=off"],
        vec!["-Ztrust-bundle-foreign-crate=dep", "-Ztrust-verify=off"],
        vec!["-Ztrust-proof-artifact-root=/tmp/proof", "-Ztrust-verify=off"],
        vec!["-Ztrust-ir-flip=no", "-Ztrust-verify=off"],
        vec!["-Ztrust-instance-flip=no", "-Ztrust-verify=off"],
        // Evidence controls AT their declared default carry no authority.
        vec!["-Ztrust-cg-output-gate=strict", "-Ztrust-verify-crate-role=unscoped"],
        ay_then_off,
    ];
    for args in &accepted {
        let (_, matches) = parsed_matches(&with_input(args));
        for policy in DEAUTHORIZED_POLICIES {
            assert_eq!(
                forbidden_in(policy, &matches),
                None,
                "{} refused {args:?}, whose effective verification is off",
                policy.diagnostic_name(),
            );
        }
    }
}

#[test]
fn deauthorized_frontends_still_refuse_evidence_controls_under_the_off_switch() {
    for (control, expected) in [
        ("-Ztrust-dump=ir:/tmp/ir", "-Ztrust-dump"),
        ("-Ztrust-dump=spec-clean:/tmp/spec", "-Ztrust-dump"),
        ("-Ztrust-body-census=/tmp/census", "-Ztrust-body-census"),
        ("-Ztrust-instance-census=/tmp/census", "-Ztrust-instance-census"),
        ("-Ztrust-lean-census=/tmp/census", "-Ztrust-lean-census"),
        ("-Ztrust-verify-session=proof", "-Ztrust-verify-session"),
        ("-Ztrust-verify-package-name=pkg", "-Ztrust-verify-package-name"),
        ("-Ztrust-verify-crate-role=primary", "-Ztrust-verify-crate-role"),
        ("-Ztrust-proc-macro-boundary", "-Ztrust-proc-macro-boundary"),
        ("-Ztrust-proc-macro-isolation", "-Ztrust-proc-macro-isolation"),
        ("-Ztrust-audited-proc-macro=/tmp/libaudited.dylib", "-Ztrust-audited-proc-macro"),
        ("-Ztrust-targo-test-monitor", "-Ztrust-targo-test-monitor"),
        ("-Ztrust-certified-test-monitors", "-Ztrust-certified-test-monitors"),
        ("-Ztrust-cg-frontend=trust-ir", "-Ztrust-cg-frontend"),
        ("-Ztrust-cg-output-gate=off", "-Ztrust-cg-output-gate"),
        ("-Ztrust-ir-cg-args=no-proof-certs", "-Ztrust-ir-cg-args"),
        // Trust: `-Ztrust-ir-upstream-mir` is gone (a4e15ca586 removed the option and its
        // frontend_authority row); an unknown `-Z` is not an evidence control to classify.
        ("-Ztrust-ir-crate-module", "-Ztrust-ir-crate-module"),
        ("-Ztrust-sat-perturb=enum-reshape", "-Ztrust-sat-perturb"),
        ("-Ztrust-instance-flip-mutate=abi-swap", "-Ztrust-instance-flip-mutate"),
        ("-Ztrust-instance-flip-probe=*", "-Ztrust-instance-flip-probe"),
        ("-Ztrust-clean-origin-mutate-emitter", "-Ztrust-clean-origin-mutate-emitter"),
        ("-Ztrust-ir-lower-mutate-finalization", "-Ztrust-ir-lower-mutate-finalization"),
        ("-Ztrust-test-mutate-derived-assert-msg", "-Ztrust-test-mutate-derived-assert-msg"),
        ("-Ztrust-ctfe-trivial-probe", "-Ztrust-ctfe-trivial-probe"),
        ("-Ztrust-witness=off", "-Ztrust-witness"),
        ("-Ztrust-witness-precise", "-Ztrust-witness-precise"),
        ("-Ztrust-spawn-census-shadow=report", "-Ztrust-spawn-census-shadow"),
        ("-Ztrust-send-census", "-Ztrust-send-census"),
        ("-Ztrust-writer-census=config.harness", "-Ztrust-writer-census"),
        ("-Ztrust-no-str-byte-position", "-Ztrust-no-str-byte-position"),
        ("-Ztrust-tinv", "-Ztrust-tinv"),
        ("-Ztrust-ir-lower-mutate-rhs-effects", "-Ztrust-ir-lower-mutate-rhs-effects"),
        ("-Ztrust-ir-seam-reference=/tmp/seam", "-Ztrust-ir-seam-reference"),
        // Trust (step 2 increment 6, step 6.5.1): the TEST-ONLY template lane switch.
        ("-Ztrust-ir-lower-templates=yes", "-Ztrust-ir-lower-templates"),
    ] {
        let mut argv = AY_POSTURE.to_vec();
        argv.extend(["-Ztrust-verify=off", control]);
        let (_, matches) = parsed_matches(&with_input(&argv));
        for policy in DEAUTHORIZED_POLICIES {
            assert_eq!(
                forbidden_in(policy, &matches).as_deref(),
                Some(expected),
                "{} accepted evidence control {control} under the off-switch",
                policy.diagnostic_name(),
            );
        }
    }
    // The session-bound custom-target digest needs a 64-hex value to parse at all.
    let target_digest = format!("-Ztrust-verify-target-spec-sha256={}", "a".repeat(64));
    let (_, matches) = parsed_matches(&with_input(&["-Ztrust-verify=off", target_digest.as_str()]));
    for policy in DEAUTHORIZED_POLICIES {
        assert_eq!(
            forbidden_in(policy, &matches).as_deref(),
            Some("-Ztrust-verify-target-spec-sha256"),
        );
    }
}

/// Accepting a posture must add NO behaviour: after the driver's own neutralization
/// sequence (typed parse, the verification override, deauthorization), ay's posture
/// followed by the off-switch is the same tracked configuration as a plain
/// `-Ztrust-verify=off` — up to the SIGPIPE disposition its `unix_hardened` profile
/// declares for `main` in every lane, which survives as `-Zon-broken-pipe=kill`.
#[test]
#[allow(rustc::bad_opt_access)]
fn an_accepted_posture_neutralizes_to_the_plain_off_configuration() {
    fn neutralized(args: &[&str]) -> config::Options {
        let (_, matches) = parsed_matches(args);
        let mut typed_dcx =
            rustc_session::EarlyDiagCtxt::new(rustc_session::config::ErrorOutputType::default());
        let mut options =
            rustc_session::config::build_session_options(&mut typed_dcx, &matches, false);
        apply_trust_verify_override(&mut options, true);
        TrustFrontendAuthoritySnapshot::deauthorize(&mut options);
        options
    }

    let mut ay_then_off = AY_POSTURE.to_vec();
    ay_then_off.push("-Ztrust-verify=off");
    let posture = neutralized(&with_input(&ay_then_off));
    let plain = neutralized(&with_input(&["-Ztrust-verify=off", "-Zon-broken-pipe=kill"]));
    assert_eq!(posture.unstable_opts.trust_verify, config::TrustVerify::Off);
    assert_eq!(posture.unstable_opts.trust_policy, config::TrustPolicy::default());
    assert_eq!(posture.unstable_opts.trust_verify_profile, None);
    assert_eq!(posture.unstable_opts.trust_ir_lower, Some(config::TrustIrLower::Off));
    assert_eq!(TrustFrontendAuthoritySnapshot::first_live_verification_selector(&posture), None);
    for for_crate_hash in [false, true] {
        assert_eq!(
            posture.dep_tracking_hash(for_crate_hash),
            plain.dep_tracking_hash(for_crate_hash),
            "the neutralized posture differs from plain `-Ztrust-verify=off` \
             (for_crate_hash={for_crate_hash})",
        );
    }
    // Pinned, so the equality cannot hold by the profile's SIGPIPE declaration
    // having been dropped on both sides.
    assert_ne!(
        neutralized(&with_input(&["-Ztrust-verify=off"])).dep_tracking_hash(true),
        posture.dep_tracking_hash(true),
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
        // both lanes. The fail-closed half is honoured only under verification: with
        // `-Ztrust-verify=off` the request degrades to a plain `on` (see the stamp below and
        // `trust_ir_lower_strict_by_flags`), because the off-switch is the master switch.
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

        // A `strict` request survives canonicalization only under verification; everything
        // else collapses to the resolved on/off answer. Stamping `On` for a verified strict
        // request would silently drop the fail-closed half while leaving the mode looking
        // enabled; stamping `Strict` for an UNVERIFIED one would record a strictness the
        // compile does not enforce — two hashes for one compilation.
        let strict = verify == On && requested == Some(IrStrict);
        assert_eq!(
            rustc_session::trust_ir_lower_strict_by_flags(verify, requested),
            strict,
            "strict lane trust_verify={verify:?} requested={requested:?}",
        );
        let stamped = if strict {
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
        for requested in [None, Some(config::TrustIrLower::On), Some(config::TrustIrLower::Off)] {
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
    // `-Ztrust-verify=off` is the master switch: a strict request in the off lane is the same
    // compilation as the plain burn-in lane, and its tracked identity must say so. This is the
    // assertion that would have caught strict lowering firing on unverified units.
    assert_eq!(burn_in, canonical(Off, Some(IrStrict)));
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
        "marker-order",
        "marker-drop",
        "agg-field-order",
        "marker-arm",
        "payload-tramp",
        "dr-tramp",
        "dr-retire",
        "mc-plan",
        "cf-lit-order",
        "chain-ret-order",
        "cf-field-drop",
        "cf-unit-late",
        "cf-pair-order",
        "cf-ret-late",
        "cf-post-late",
        "sw-tramp",
        "swr-tramp",
        "g25-hoist",
        "seq-unit-late",
        "g21-ret-order",
        "uc-unit-late",
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
             enum-case-value, enum-ctor, enum-disc-index, switch-map, enum-payload, \
             marker-order, marker-drop, agg-field-order, marker-arm, payload-tramp, \
             dr-tramp, dr-retire, mc-plan, cf-lit-order, chain-ret-order, cf-field-drop, \
             cf-unit-late, cf-pair-order, cf-ret-late, cf-post-late, sw-tramp, \
             swr-tramp, g25-hoist, seq-unit-late, g21-ret-order, or uc-unit-late"
        )
    );
}

#[test]
#[allow(rustc::bad_opt_access)]
fn derived_assert_msg_mutation_is_fenced_to_the_burn_in_lane_with_no_flip_and_no_dump() {
    let mut verifying = rustc_session::config::Options::default();
    verifying.unstable_opts.trust_test_mutate_derived_assert_msg = true;
    let lane = Some(
        "-Ztrust-test-mutate-derived-assert-msg is a test-only control and requires \
         -Ztrust-verify=off -Ztrust-ir-lower",
    );
    // Batteries-on verification (the default) refuses it.
    assert_eq!(trust_option_domain_error(&verifying), lane);
    // So does the off lane without direct lowering.
    let mut no_lower = verifying.clone();
    no_lower.unstable_opts.trust_verify = config::TrustVerify::Off;
    assert_eq!(trust_option_domain_error(&no_lower), lane);
    let mut lower_off = no_lower.clone();
    lower_off.unstable_opts.trust_ir_lower = Some(config::TrustIrLower::Off);
    assert_eq!(trust_option_domain_error(&lower_off), lane);
    // Verification on with lowering on is still an evidence lane.
    let mut evidence = verifying.clone();
    evidence.unstable_opts.trust_ir_lower = Some(config::TrustIrLower::On);
    assert_eq!(trust_option_domain_error(&evidence), lane);

    // The burn-in lane with the flip on (its default): inert, so refused.
    let mut flip_on = no_lower.clone();
    flip_on.unstable_opts.trust_ir_lower = Some(config::TrustIrLower::On);
    assert!(flip_on.unstable_opts.trust_ir_flip, "the flip defaults on");
    assert_eq!(
        trust_option_domain_error(&flip_on),
        Some(
            "-Ztrust-test-mutate-derived-assert-msg is inert while the Trust-IR flip is on \
             and requires -Ztrust-ir-flip=no"
        )
    );

    // The one admitted posture: verification off, lowering on, flip off, no artifact sink.
    let mut admitted = flip_on.clone();
    admitted.unstable_opts.trust_ir_flip = false;
    assert_eq!(trust_option_domain_error(&admitted), None);

    // Every -Ztrust-dump sink is refused alongside it, the coverage report (`ir`) included.
    let dump = Some(
        "-Ztrust-test-mutate-derived-assert-msg mutates the derived MIR the differential \
         compares and cannot be combined with any -Ztrust-dump artifact sink",
    );
    for what in ["ir", "mir", "native-bundle", "spec-clean"] {
        let mut sink = admitted.clone();
        let path = Some(PathBuf::from(what));
        let d = &mut sink.unstable_opts.trust_dump;
        match what {
            "ir" => d.ir = path,
            "mir" => d.mir = path,
            "native-bundle" => d.native_bundle = path,
            _ => d.spec_clean = path,
        }
        assert_eq!(trust_option_domain_error(&sink), dump, "sink={what}");
    }

    // Unset, the same postures are untouched by this fence.
    let mut unset = flip_on;
    unset.unstable_opts.trust_test_mutate_derived_assert_msg = false;
    assert_eq!(trust_option_domain_error(&unset), None);
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
    for diagnostic in ["TRUST_ASSERT_DEBUG", "TRUST_NATIVE_DEBUG", "TRUST_VERIFY_TRACE_CERTIFIED"] {
        assert!(!LEGACY_TRUST_SEMANTIC_ENV_VARS.contains(&diagnostic));
    }
}

/// Trust (D21): `-Ztrust-proc-macro-isolation` is refused on a host without the
/// worker's sandbox and admitted on one with it; off, it refuses nowhere. The rule
/// is pure, so both hosts' answers are pinned here whichever host runs the test,
/// and the driver's admission applies it to the host it was built for.
#[test]
#[allow(rustc::bad_opt_access)]
fn proc_macro_isolation_is_refused_on_a_host_without_the_sandbox() {
    use rustc_session::{
        TRUST_PROC_MACRO_ISOLATION_HOST, trust_proc_macro_isolation_refusal_by_flags,
    };
    let refusal = trust_proc_macro_isolation_refusal_by_flags(true, false)
        .expect("a host without the sandbox refuses the option");
    assert!(refusal.starts_with("-Ztrust-proc-macro-isolation is refused on this host"));
    assert!(refusal.contains("does not fall back"));
    assert_eq!(trust_proc_macro_isolation_refusal_by_flags(true, true), None);
    assert_eq!(trust_proc_macro_isolation_refusal_by_flags(false, false), None);
    assert_eq!(trust_proc_macro_isolation_refusal_by_flags(false, true), None);

    let mut opts = rustc_session::config::Options::default();
    assert_eq!(trust_option_domain_error(&opts), None);
    opts.unstable_opts.trust_proc_macro_isolation = true;
    assert_eq!(
        trust_option_domain_error(&opts),
        trust_proc_macro_isolation_refusal_by_flags(true, TRUST_PROC_MACRO_ISOLATION_HOST)
    );
    assert_eq!(TRUST_PROC_MACRO_ISOLATION_HOST, cfg!(target_os = "macos"));
}

// Trust (PM-1): the crate-loader proc-macro boundary is Targo's per-unit control.
#[test]
#[allow(rustc::bad_opt_access)]
fn proc_macro_boundary_options_require_their_session_and_boundary() {
    let mut opts = rustc_session::config::Options::default();
    opts.unstable_opts.trust_proc_macro_boundary = true;
    assert_eq!(
        trust_option_domain_error(&opts),
        Some("-Ztrust-proc-macro-boundary requires -Ztrust-verify-session")
    );
    opts.unstable_opts.trust_verify_session = Some("session".to_string());
    assert_eq!(trust_option_domain_error(&opts), None);

    let mut audited_only = rustc_session::config::Options::default();
    audited_only.unstable_opts.trust_verify_session = Some("session".to_string());
    audited_only.unstable_opts.trust_audited_proc_macro = vec!["libaudited.dylib".to_string()];
    assert_eq!(
        trust_option_domain_error(&audited_only),
        Some("-Ztrust-audited-proc-macro requires -Ztrust-proc-macro-boundary")
    );

    opts.unstable_opts.trust_audited_proc_macro = vec![String::new()];
    assert_eq!(
        trust_option_domain_error(&opts),
        Some("-Ztrust-audited-proc-macro requires a non-empty dylib path")
    );
}

#[test]
#[allow(rustc::bad_opt_access)]
fn instance_seam_test_is_default_off_and_fenced_to_diagnostic_frontend() {
    let mut opts = rustc_session::config::Options::default();
    assert!(!opts.unstable_opts.trust_ir_instance_seam_test);
    opts.unstable_opts.trust_ir_instance_seam_test = true;
    assert!(trust_option_domain_error(&opts).is_some());
    opts.unstable_opts.trust_verify = config::TrustVerify::Off;
    assert!(trust_option_domain_error(&opts).is_some());
    opts.unstable_opts.trust_ir_lower = Some(config::TrustIrLower::On);
    assert!(trust_option_domain_error(&opts).is_some());
    opts.unstable_opts.trust_cg_frontend = "trust-ir".into();
    assert!(trust_option_domain_error(&opts).is_some(), "default backend is not F1");
    opts.unstable_opts.codegen_backend = Some("trust-cg".into());
    opts.output_types = config::OutputTypes::new(&[(config::OutputType::Object, None)]);
    assert_eq!(trust_option_domain_error(&opts), None);
    for backend in [None, Some("llvm"), Some("dummy")] {
        let mut wrong = opts.clone();
        wrong.unstable_opts.codegen_backend = backend.map(str::to_string);
        assert!(trust_option_domain_error(&wrong).is_some(), "backend={backend:?}");
    }
    for kind in [config::OutputType::Metadata, config::OutputType::DepInfo, config::OutputType::Mir]
    {
        let mut wrong = opts.clone();
        wrong.output_types = config::OutputTypes::new(&[(kind, None)]);
        assert!(trust_option_domain_error(&wrong).is_some(), "output={kind:?}");
    }
    for mode in 0..3 {
        let mut wrong = opts.clone();
        match mode {
            0 => wrong.unstable_opts.no_codegen = true,
            1 => wrong.unstable_opts.no_analysis = true,
            _ => wrong.unstable_opts.parse_crate_root_only = true,
        }
        assert!(trust_option_domain_error(&wrong).is_some(), "early mode={mode}");
    }
    for sink in ["ir", "mir", "native-bundle", "spec-clean"] {
        let mut forbidden = opts.clone();
        let path = Some(PathBuf::from(sink));
        match sink {
            "ir" => forbidden.unstable_opts.trust_dump.ir = path,
            "mir" => forbidden.unstable_opts.trust_dump.mir = path,
            "native-bundle" => forbidden.unstable_opts.trust_dump.native_bundle = path,
            _ => forbidden.unstable_opts.trust_dump.spec_clean = path,
        }
        assert!(trust_option_domain_error(&forbidden).is_some(), "{sink}");
    }
    for mode in ["bool-constant", "undef-constant"] {
        opts.unstable_opts.trust_test_instance_seam_mutation = Some(mode.into());
        assert_eq!(trust_option_domain_error(&opts), None);
    }
    opts.unstable_opts.trust_test_instance_seam_mutation = Some("unknown".into());
    assert!(trust_option_domain_error(&opts).is_some());
    opts.unstable_opts.trust_test_instance_seam_mutation = Some("bool-constant".into());
    opts.unstable_opts.trust_ir_instance_seam_test = false;
    assert!(trust_option_domain_error(&opts).is_some());
}

/// Trust (PKG-C2d2 slice 1): the template-instance TEST-ORACLE is default off, rides only on the
/// accepted D17 seam-test lane with the template producer, and its negative controls require it.
#[test]
#[allow(rustc::bad_opt_access)]
fn template_instance_oracle_is_default_off_and_fenced_to_the_seam_test_lane() {
    const NEEDS_LANE: Option<&str> = Some(
        "-Ztrust-ir-template-instance-oracle requires -Ztrust-ir-instance-seam-test \
                     and -Ztrust-ir-lower-templates",
    );
    let mut opts = rustc_session::config::Options::default();
    assert!(!opts.unstable_opts.trust_ir_template_instance_oracle);
    assert!(opts.unstable_opts.trust_test_template_oracle_mutation.is_none());
    opts.unstable_opts.trust_verify = config::TrustVerify::Off;
    opts.unstable_opts.trust_ir_lower = Some(config::TrustIrLower::On);
    opts.unstable_opts.trust_cg_frontend = "trust-ir".into();
    opts.unstable_opts.codegen_backend = Some("trust-cg".into());
    opts.output_types = config::OutputTypes::new(&[(config::OutputType::Object, None)]);
    opts.unstable_opts.trust_ir_instance_seam_test = true;
    assert_eq!(trust_option_domain_error(&opts), None, "the seam-test lane alone");
    opts.unstable_opts.trust_ir_template_instance_oracle = true;
    assert_eq!(trust_option_domain_error(&opts), NEEDS_LANE, "no template producer");
    opts.unstable_opts.trust_ir_lower_templates = true;
    assert_eq!(trust_option_domain_error(&opts), None);
    let mut no_seam = opts.clone();
    no_seam.unstable_opts.trust_ir_instance_seam_test = false;
    assert_eq!(trust_option_domain_error(&no_seam), NEEDS_LANE, "no seam-test lane");
    let mut llvm = opts.clone();
    llvm.unstable_opts.codegen_backend = Some("llvm".into());
    assert!(trust_option_domain_error(&llvm).is_some(), "the seam fence still binds");
    for mode in ["int-constant", "envelope-byte"] {
        opts.unstable_opts.trust_test_template_oracle_mutation = Some(mode.into());
        assert_eq!(trust_option_domain_error(&opts), None, "{mode}");
    }
    opts.unstable_opts.trust_test_template_oracle_mutation = Some("bool-constant".into());
    assert_eq!(
        trust_option_domain_error(&opts),
        Some(
            "invalid -Ztrust-test-template-oracle-mutation: expected \
                         int-constant or envelope-byte"
        )
    );
    opts.unstable_opts.trust_test_template_oracle_mutation = Some("int-constant".into());
    opts.unstable_opts.trust_ir_template_instance_oracle = false;
    assert_eq!(
        trust_option_domain_error(&opts),
        Some(
            "-Ztrust-test-template-oracle-mutation requires \
                         -Ztrust-ir-template-instance-oracle"
        )
    );
}

// Trust: use actual rustc option parsing; no alternate custody/argv classifier.
#[test]
fn private_fixed_routing_rejects_every_pre_adoption_early_exit() {
    for arguments in [
        &["--help"][..],
        &["-V"],
        &["-vV"],
        &["-Zhelp"],
        &["-Chelp"],
        &["-Cpasses=list"],
        &["-Wall"],
        &["-Whelp"],
        &["--explain=E0001"],
    ] {
        let mut private = vec!["--resource-bootstrap-fixed-v1"];
        private.extend_from_slice(arguments);
        let (args, matches) = parsed_matches(&private);
        assert!(private_fixed_pre_session_exit(&matches, &args).is_some(), "{arguments:?}");
        let (args, matches) = parsed_matches(arguments);
        assert_eq!(private_fixed_pre_session_exit(&matches, &args), None);
    }
    let (args, matches) =
        parsed_matches(&["--resource-bootstrap-fixed-v1", "lib.rs", "--crate-type=rlib"]);
    assert_eq!(private_fixed_pre_session_exit(&matches, &args), None);
}

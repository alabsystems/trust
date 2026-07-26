use std::ffi::{OsStr, OsString};
use std::panic::catch_unwind;
use std::sync::Mutex;
use std::thread;

use super::{
    AutoDiff, BACKEND_AFTER_EVIDENCE_INERT, CG_OPTIONS, CodegenOptions, CompilerBackendRoute,
    CompilerBackendRouteState, EVIDENCE_INERT_AFTER_BACKEND, EVIDENCE_INERT_PROCESS_REUSE,
    LEGACY_TRUST_SEMANTIC_ENV_VARS, Options, TrustAuthorityClass, TrustFrontendAuthoritySnapshot,
    TrustVerify, UNTRACKED_TRUST_CODEGEN_ENV_PREFIXES, UnstableOptions, Z_OPTIONS,
    enter_compiler_backend_route_with_state, evidence_inert_llvm_control,
    forbidden_no_official_evidence_environment_key, forbidden_trust_environment_key,
    is_legacy_trust_semantic_env_with_windows_semantics,
    is_untracked_trust_codegen_env_with_windows_semantics,
};

fn isolated_compiler_backend_route_state() -> &'static Mutex<CompilerBackendRouteState> {
    Box::leak(Box::new(Mutex::new(CompilerBackendRouteState::Pristine)))
}

#[test]
fn authority_inventory_covers_the_complete_trust_option_table() {
    // The inventory is generated from the option table, so the interesting
    // question is no longer "did someone update the second list" but "does the
    // generated inventory still cover the whole Trust surface" — a
    // `-Ztrust-*` option missing its class is a compile error, and this pins
    // the two facts that a `const` assertion cannot see: that `codegen_backend`
    // is still classified, and that no `-Ctrust-*` control has appeared in a
    // table whose authority nobody reads.
    let declared = UnstableOptions::TRUST_AUTHORITY_CONTROLS
        .iter()
        .map(|control| control.field)
        .collect::<Vec<_>>();
    let table = Z_OPTIONS.iter().map(|option| option.name()).collect::<Vec<_>>();
    for field in &declared {
        assert!(table.contains(field), "classified option `{field}` is not in the -Z table");
    }
    for field in table.iter().filter(|field| field.starts_with("trust_")) {
        assert!(declared.contains(field), "`{field}` declares no TRUST_AUTHORITY class");
    }
    assert!(
        declared.contains(&"codegen_backend"),
        "explicit backend selection is immutable callback authority",
    );

    assert!(
        CodegenOptions::TRUST_AUTHORITY_CONTROLS.is_empty()
            && CG_OPTIONS.iter().all(|option| !option.name().starts_with("trust_")),
        "-C is not a Trust option class; a Trust control there would sit outside every \
         authority boundary that reads the -Z table",
    );

    // Path is relative to this file (src/config/tests/), so reach back up to
    // `src/options.rs`. Top-level `Options` fields are not part of any option
    // table and so cannot be classified there; the snapshot carries the one
    // that exists by hand.
    let option_source = include_str!("../../options.rs");
    let options_body = option_source
        .rsplit_once("pub struct Options {")
        .expect("Options declaration")
        .1
        .split_once("\n    }\n);")
        .expect("Options declaration end")
        .0;
    let top_level_trust_fields = options_body
        .lines()
        .filter_map(|line| {
            let (field, _) = line.trim_start().split_once(':')?;
            field.starts_with("trust_").then_some(field)
        })
        .collect::<Vec<_>>();
    assert_eq!(
        top_level_trust_fields,
        ["trust_solver_content_fingerprint"],
        "new top-level Trust state must be added to TrustFrontendAuthoritySnapshot",
    );
}

/// Every classified control must actually be observed by both boundaries. The
/// generated code cannot be wrong per-field, but it can be wired to the wrong
/// struct or shadowed by a stale clone, and this is what would catch that.
#[test]
#[allow(rustc::bad_opt_access)]
fn every_classified_control_is_observed_at_both_boundaries() {
    let baseline = Options::default();
    let authority = TrustFrontendAuthoritySnapshot::capture(&baseline);

    let mut solver = baseline.clone();
    solver.trust_solver_content_fingerprint = "ay:sha256:callback".to_string();
    assert_eq!(
        authority.changed_option(&solver).as_deref(),
        Some(super::COMPILER_POPULATED_SOLVER_IDENTITY),
    );

    for control in UnstableOptions::TRUST_AUTHORITY_CONTROLS {
        let mut changed = baseline.clone();
        mutate_trust_control(&mut changed.unstable_opts, control.field);
        assert_eq!(
            authority.changed_option(&changed),
            Some(control.spelling()),
            "callback mutation of `{}` escaped the authority snapshot",
            control.field,
        );
        if control.class == TrustAuthorityClass::EvidenceControl {
            assert_eq!(
                TrustFrontendAuthoritySnapshot::first_nondefault_evidence_control(&changed),
                Some(control.spelling()),
                "typed embedded configuration of `{}` escaped rejection",
                control.field,
            );
        }
    }
}

/// Move one classified control off its declared default. Exhaustive over the
/// inventory: an unhandled field fails the loop above rather than silently
/// testing nothing.
#[allow(rustc::bad_opt_access)]
fn mutate_trust_control(opts: &mut UnstableOptions, field: &str) {
    use std::path::PathBuf;

    use super::{TrustDump, TrustPolicy, TrustWitness};
    match field {
        "codegen_backend" => opts.codegen_backend = Some("llvm".to_string()),
        "trust_cg_output_gate" => opts.trust_cg_output_gate = "allow-unknown".to_string(),
        "trust_certified_test_monitors" => opts.trust_certified_test_monitors = true,
        "trust_dump" => {
            opts.trust_dump = TrustDump {
                mir: Some(PathBuf::from("callback-dump-mir")),
                mir_only: true,
                native_bundle: Some(PathBuf::from("callback-dump-native")),
                ir: Some(PathBuf::from("callback-ir-dump")),
            }
        }
        "trust_ir_flip" => opts.trust_ir_flip = false,
        "trust_ir_lower" => opts.trust_ir_lower = Some(crate::config::TrustIrLower::On),
        "trust_no_r1" => opts.trust_no_r1 = true,
        "trust_policy" => opts.trust_policy = TrustPolicy::Advisory,
        "trust_proof_artifact_root" => {
            opts.trust_proof_artifact_root = Some(PathBuf::from("callback-proof-artifact-root"))
        }
        "trust_sat_perturb" => opts.trust_sat_perturb = Some("enum-reshape".to_string()),
        "trust_targo_test_monitor" => opts.trust_targo_test_monitor = true,
        "trust_verify" => opts.trust_verify = super::TrustVerify::Off,
        "trust_verify_ay_path" => opts.trust_verify_ay_path = Some(PathBuf::from("callback-ay")),
        "trust_verify_crate_role" => opts.trust_verify_crate_role = "primary".to_string(),
        "trust_verify_function_budget_ms" => opts.trust_verify_function_budget_ms = 1,
        "trust_verify_function_budget_steps" => opts.trust_verify_function_budget_steps = 1,
        "trust_verify_include_dependencies" => opts.trust_verify_include_dependencies = true,
        "trust_verify_level" => opts.trust_verify_level = 1,
        "trust_verify_output" => opts.trust_verify_output = "json".to_string(),
        "trust_verify_package_name" => {
            opts.trust_verify_package_name = Some("callback-package".to_string())
        }
        "trust_verify_profile" => {
            opts.trust_verify_profile = Some("callback-profile".to_string())
        }
        "trust_verify_session" => {
            opts.trust_verify_session = Some("callback-session".to_string())
        }
        "trust_verify_target_spec_sha256" => {
            opts.trust_verify_target_spec_sha256 = Some("a".repeat(64))
        }
        "trust_verify_timeout_ms" => opts.trust_verify_timeout_ms = 1,
        "trust_verify_worker_threads" => opts.trust_verify_worker_threads = 1,
        "trust_witness" => opts.trust_witness = TrustWitness::Off,
        "trust_witness_precise" => opts.trust_witness_precise = true,
        other => panic!("no authority probe for classified control `{other}`"),
    }
}

#[test]
#[allow(rustc::bad_opt_access)]
fn deauthorization_is_monotonic_and_clears_internal_solver_identity() {
    for incoming_verify in [TrustVerify::On, TrustVerify::Off] {
        // Both the unset request and the canonicalized "resolved off" spelling
        // are states a deauthorized frontend inherits without complaint; only
        // an actual request for lowering is caller-populated authority.
        for incoming_lowering in [None, Some(crate::config::TrustIrLower::Off)] {
            let mut opts = Options::default();
            opts.unstable_opts.trust_verify = incoming_verify;
            opts.unstable_opts.trust_ir_lower = incoming_lowering;
            assert_eq!(
                TrustFrontendAuthoritySnapshot::first_nondefault_evidence_control(&opts),
                None,
            );
            TrustFrontendAuthoritySnapshot::deauthorize(&mut opts);
            assert_eq!(opts.unstable_opts.trust_verify, TrustVerify::Off);
            assert_eq!(opts.unstable_opts.trust_ir_lower, Some(crate::config::TrustIrLower::Off));
            assert!(!crate::trust_ir_lower_enabled_by_flags(
                opts.unstable_opts.trust_verify,
                opts.unstable_opts.trust_ir_lower,
            ));
            assert!(opts.trust_solver_content_fingerprint.is_empty());
        }
    }

    let mut lowering = Options::default();
    lowering.unstable_opts.trust_ir_lower = Some(crate::config::TrustIrLower::On);
    assert_eq!(
        TrustFrontendAuthoritySnapshot::first_nondefault_evidence_control(&lowering).as_deref(),
        Some("-Ztrust-ir-lower"),
    );

    let mut solver = Options::default();
    solver.trust_solver_content_fingerprint = "ay:sha256:caller".to_string();
    assert_eq!(
        TrustFrontendAuthoritySnapshot::first_nondefault_evidence_control(&solver).as_deref(),
        Some(super::COMPILER_POPULATED_SOLVER_IDENTITY),
    );
}

#[test]
#[allow(rustc::bad_opt_access)]
fn evidence_inert_policy_rejects_dynamic_llvm_controls() {
    let mut opts = Options::default();
    assert_eq!(evidence_inert_llvm_control(&opts), None);

    opts.unstable_opts.llvm_plugins.push("/tmp/plugin".to_string());
    assert_eq!(evidence_inert_llvm_control(&opts), Some("-Zllvm-plugins"));

    opts.unstable_opts.llvm_plugins.clear();
    opts.unstable_opts.autodiff.push(AutoDiff::Enable);
    assert_eq!(evidence_inert_llvm_control(&opts), Some("-Zautodiff"));

    opts.unstable_opts.autodiff.clear();
    opts.unstable_opts.autodiff_post_passes = Some("default<O2>".to_string());
    assert_eq!(evidence_inert_llvm_control(&opts), Some("-Zautodiff-post-passes"),);

    opts.unstable_opts.autodiff_post_passes = None;
    opts.cg.llvm_args.push("-load=/tmp/plugin".to_string());
    assert_eq!(evidence_inert_llvm_control(&opts), Some("-Cllvm-args"));
}

#[test]
fn backend_capable_routes_repeat_and_permanently_exclude_evidence_inert() {
    let mut state = CompilerBackendRouteState::Pristine;
    assert_eq!(state.enter(CompilerBackendRoute::BackendCapable), Ok(()));
    assert_eq!(state.enter(CompilerBackendRoute::BackendCapable), Ok(()));
    assert_eq!(
        state.enter(CompilerBackendRoute::EvidenceInert),
        Err(EVIDENCE_INERT_AFTER_BACKEND),
    );
}

#[test]
fn evidence_inert_route_is_a_process_dedication_not_a_reentrant_lock() {
    let mut state = CompilerBackendRouteState::Pristine;
    assert_eq!(state.enter(CompilerBackendRoute::EvidenceInert), Ok(()));
    assert_eq!(
        state.enter(CompilerBackendRoute::EvidenceInert),
        Err(EVIDENCE_INERT_PROCESS_REUSE),
    );
    assert_eq!(
        state.enter(CompilerBackendRoute::BackendCapable),
        Err(BACKEND_AFTER_EVIDENCE_INERT),
    );
}

#[test]
fn evidence_inert_guard_is_structural_and_blocks_concurrent_backend_routes() {
    let state = isolated_compiler_backend_route_state();
    let guard =
        enter_compiler_backend_route_with_state(CompilerBackendRoute::EvidenceInert, state)
            .expect("first evidence-inert route must dedicate a pristine process");
    assert!(guard.validates(CompilerBackendRoute::EvidenceInert));
    assert!(!guard.validates(CompilerBackendRoute::BackendCapable));

    let error = thread::spawn(move || {
        enter_compiler_backend_route_with_state(CompilerBackendRoute::BackendCapable, state)
            .err()
    })
    .join()
    .expect("route-checking thread must not panic");
    assert_eq!(error, Some(BACKEND_AFTER_EVIDENCE_INERT));
}

#[test]
fn fatal_unwind_does_not_release_evidence_inert_process_dedication() {
    let state = isolated_compiler_backend_route_state();
    assert!(
        catch_unwind(|| {
            let _guard = enter_compiler_backend_route_with_state(
                CompilerBackendRoute::EvidenceInert,
                state,
            )
            .expect("first evidence-inert route must dedicate a pristine process");
            panic!("model a fatal diagnostic unwind");
        })
        .is_err()
    );
    assert_eq!(
        *state.lock().unwrap_or_else(|poisoned| poisoned.into_inner()),
        CompilerBackendRouteState::EvidenceInertDedicated,
    );
    assert_eq!(
        enter_compiler_backend_route_with_state(CompilerBackendRoute::EvidenceInert, state)
            .err(),
        Some(EVIDENCE_INERT_PROCESS_REUSE),
    );
}

#[test]
fn legacy_semantic_environment_inventory_is_sorted_and_unique() {
    assert!(LEGACY_TRUST_SEMANTIC_ENV_VARS.windows(2).all(|pair| pair[0] < pair[1]));
}

#[test]
#[allow(rustc::bad_opt_access)]
fn codegen_environment_is_rejected_even_after_verification_is_disabled() {
    let mut opts = Options::default();
    opts.unstable_opts.trust_verify = TrustVerify::Off;
    for key in [
        "TCG_NO_DECODE_CHECK",
        "TCG_POST_RA_RECHECK",
        "TCG_NO_MACHO_REPARSE",
        "TRUST_CG_DISABLE_PASSES",
        "TRUST_CG_ENABLE_PASSES",
    ] {
        assert_eq!(
            forbidden_trust_environment_key(&opts, [OsString::from(key)]),
            Some(OsString::from(key)),
        );
        assert_eq!(
            forbidden_no_official_evidence_environment_key([OsString::from(key)]),
            Some(OsString::from(key)),
        );
    }
}

#[test]
#[allow(rustc::bad_opt_access)]
fn legacy_semantic_environment_matters_only_while_trust_is_active() {
    let enabled = Options::default();
    assert_eq!(
        forbidden_trust_environment_key(&enabled, [OsString::from("TRUST_VERIFY_POLICY")],),
        Some(OsString::from("TRUST_VERIFY_POLICY")),
    );

    let mut disabled = enabled;
    disabled.unstable_opts.trust_verify = TrustVerify::Off;
    assert_eq!(
        forbidden_trust_environment_key(&disabled, [OsString::from("TRUST_VERIFY_POLICY")],),
        None,
    );
}

#[test]
fn codegen_prefix_inventory_is_future_proof() {
    assert_eq!(UNTRACKED_TRUST_CODEGEN_ENV_PREFIXES, &["TCG_", "TRUST_CG_"]);
    for key in ["TCG_FUTURE_SEMANTIC_GATE", "TRUST_CG_FUTURE_BYTE_REWRITE"] {
        assert!(is_untracked_trust_codegen_env_with_windows_semantics(OsStr::new(key), false,));
    }
}

#[test]
fn windows_environment_case_folding_cannot_bypass_rejection() {
    for key in ["tcg_future_semantic_gate", "TrUsT_cG_FUTURE_BYTE_REWRITE"] {
        assert!(is_untracked_trust_codegen_env_with_windows_semantics(OsStr::new(key), true,));
        assert!(
            !is_untracked_trust_codegen_env_with_windows_semantics(OsStr::new(key), false,)
        );
    }
    assert!(is_legacy_trust_semantic_env_with_windows_semantics(
        OsStr::new("trust_verify_policy"),
        true,
    ));
    assert!(!is_legacy_trust_semantic_env_with_windows_semantics(
        OsStr::new("trust_verify_policy"),
        false,
    ));
}


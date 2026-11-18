use std::ffi::{OsStr, OsString};
use std::panic::catch_unwind;
use std::sync::Mutex;
use std::thread;

use super::{
    AutoDiff, BACKEND_AFTER_EVIDENCE_INERT, CG_OPTIONS, CodegenOptions, CompilerBackendRoute,
    CompilerBackendRouteState, EVIDENCE_INERT_AFTER_BACKEND, EVIDENCE_INERT_PROCESS_REUSE,
    LEGACY_TRUST_SEMANTIC_ENV_VARS, Options, TargetTuple, TrustAuthorityClass,
    TrustFrontendAuthoritySnapshot, TrustVerify, UNTRACKED_TRUST_CODEGEN_ENV_PREFIXES,
    UnstableOptions, Z_OPTIONS, authenticated_target_llvm_args_error,
    enter_compiler_backend_route_with_state, evidence_inert_llvm_control,
    evidence_inert_target_llvm_args_error, forbidden_no_official_evidence_environment_key,
    forbidden_trust_environment_key, is_legacy_trust_semantic_env_with_windows_semantics,
    is_untracked_trust_codegen_env_with_windows_semantics, target_is_exact_builtin,
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
        // Trust: `trust_verify_explicit_off` (added f64af71895b) belongs here, and
        // its presence is NOT missing authority coverage — checked rather than
        // assumed, because that is exactly what this test exists to catch.
        //
        // Its ONLY consumer is a `dcx().note("compiled WITHOUT Trust verification
        // — 0 obligations checked")` (rustc_mir_transform/src/trust_verify.rs), so
        // it can alter a message and nothing else: no obligation, no verdict, no
        // routing. And `TrustFrontendAuthoritySnapshot::deauthorize` already
        // clears it (config.rs), so a deauthorized frontend cannot use it to claim
        // the explicit off-switch spelling.
        //
        // A future `trust_*` field that DOES carry authority must not simply be
        // appended here. The question this list asks is "is this state covered by
        // the snapshot"; answer it, then extend.
        //
        // `trust_solver_content_fingerprint` left this list with plan P4 / T4.1
        // (2026-10-10): trustc links its ay, so no solver identity is populated.
        ["trust_verify_explicit_off"],
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
        if control.class == TrustAuthorityClass::VerificationSelector {
            // Accepted by the embedded boundary, visible as live posture until
            // deauthorized, and afterwards indistinguishable — in every classified
            // field — from deauthorizing a configuration that never set it.
            assert_eq!(
                TrustFrontendAuthoritySnapshot::first_nondefault_evidence_control(&changed),
                None,
                "verification selector `{}` was refused instead of neutralized",
                control.field,
            );
            assert_eq!(
                TrustFrontendAuthoritySnapshot::first_live_verification_selector(&changed),
                Some(control.spelling()),
                "live verification selector `{}` is invisible to the post-session check",
                control.field,
            );
            let mut neutralized = changed.clone();
            TrustFrontendAuthoritySnapshot::deauthorize(&mut neutralized);
            let mut neutral_baseline = baseline.clone();
            TrustFrontendAuthoritySnapshot::deauthorize(&mut neutral_baseline);
            assert_eq!(
                TrustFrontendAuthoritySnapshot::first_live_verification_selector(&neutralized),
                None,
            );
            assert_eq!(
                TrustFrontendAuthoritySnapshot::capture(&neutral_baseline)
                    .changed_option(&neutralized),
                None,
                "deauthorization left the caller's `{}` observable",
                control.field,
            );
        }
    }
}

/// The frontend disposition of every Trust option, stated once per option. A
/// reclassification must edit this table — and say why — rather than slip in
/// through the option declaration alone.
///
/// `VerificationSelector` — accepted by an evidence-deauthorized frontend
/// (tippy-driver, trustdoc and its doctest collection, Miri, any
/// `rustc_driver::run_compiler` embedder) at any valid value and reset to its
/// default, because every effect it has is conditional on an active
/// verification run or on the direct lowering that run drives, and such a
/// frontend runs neither:
///   policy / level / profile / include-dependencies / no-adapter-yield / no-r1 /
///   bundle-foreign-crate — which obligations an active run generates, which
///   premises it may use, and which verdicts fail it;
///   timeout / worker-threads / function-budget-{ms,steps} / effort / ay-path —
///   the resources and solver an active run dispatches to (the one effort
///   count's scale is read only by the verification pass, which hands each ay
///   query its count as `:rlimit`);
///   verify-output / proof-artifact-root / memory-notes — how and where an
///   active run reports and stores what it proved, and what it retained in
///   memory while proving it;
///   ir-flip / instance-flip — whether a RUNNING lowering may install its derived
///   MIR (`flip_session_enabled` requires `trust_ir_lower_enabled`);
///   option-flag-lanes — the Bool/Unit representation of declined Option lanes
///   during active direct lowering; no lowering runs after deauthorization.
///   `profile` also declares a SIGPIPE disposition for `main` that holds without
///   verification; deauthorization materializes it into `-Zon-broken-pipe` first
///   (`deauthorization_preserves_the_profile_declared_sigpipe_disposition`).
///
/// `EvidenceControl` — still refused whenever it is not at its default,
/// because its effect does not depend on verification running:
///   dump / body-census / instance-census / lean-census — publish artifacts;
///   send-census / writer-census — diagnostic notes, in either lane;
///   verify-session / verify-package-name / verify-crate-role /
///   verify-target-spec-sha256 — authenticated-session identity a frontend would
///   otherwise present as coverage;
///   proc-macro-boundary / audited-proc-macro — Targo's per-unit crate-loader
///   boundary (PM-1): it is valid only with `-Ztrust-verify-session`, so it
///   travels with an authenticated session identity and is refused alongside it;
///   proc-macro-isolation — moves every proc-macro expansion into a sandboxed
///   worker (D21) whether or not verification runs; the worker is the `trustc`
///   executable's own role, which an embedded frontend's executable does not
///   have, so such a frontend could only drop it and expand in process;
///   targo-test-monitor / certified-test-monitors — install certified runtime
///   monitors (emitted code) under a session;
///   cg-frontend / cg-output-gate / cg-f1-backend / ir-cg-args /
///   ir-upstream-mir / ir-crate-module — select what and how the trust-cg
///   backend emits;
///   sat-perturb / instance-flip-mutate / instance-flip-probe /
///   clean-origin-mutate-emitter / ir-lower-mutate-finalization /
///   ir-lower-mutate-rhs-effects / ir-seam-reference / spawn-census-shadow /
///   test-mutate-derived-assert-msg / ctfe-trivial-probe / path-free — adversarial and
///   measurement controls: each exists to
///   produce an observable outcome (a refusal, a warning, a probe line, a
///   report) or to perturb emitted MIR, and a frontend that dropped one would
///   pass a negative control vacuously;
///   ir-lower-templates — the step 6.5 template lane (TEST-ONLY): it changes
///   what rmeta's trust-ir header records for a generic definition whether or
///   not verification runs, so a frontend that dropped it would publish a
///   header the caller did not ask for;
///   witness / witness-precise — the typeck-witness lane mints and replays in
///   every lane, verified or not;
///   no-str-byte-position / tinv — read only by an active run (a modeled-fact
///   negative control like no-adapter-yield, and an opt-in pre-pass), so they
///   would qualify as selectors; they keep the class their authors declared
///   and stay refused, the fail-closed reading, until a committed posture needs
///   one;
///   platform-properties / platform-unanalysed / platform-budget /
///   platform-report / platform-dump-facts — the platform-protocol pass's policy
///   (plan L1a). The pass runs only under verification, so they too would qualify
///   as selectors; they are declared evidence controls so that a deauthorized
///   frontend refuses a requested property instead of resetting it without a
///   word (FC-7).
///
/// `AuthorityOnly` — overwritten outright: `trust_verify` (forced off; an
/// explicit, effective `on` is refused at the argv boundary), `trust_ir_lower`
/// (forced off; see `first_nondefault_evidence_control`),
/// `trust_drop_rlib_objects` (reset to upstream's keep-the-objects default;
/// EW18-DROPIN-1), `codegen_backend`.
#[test]
fn every_trust_option_declares_its_deauthorized_frontend_disposition() {
    use TrustAuthorityClass::{AuthorityOnly, EvidenceControl, VerificationSelector};
    const EXPECTED: &[(&str, TrustAuthorityClass)] = &[
        ("codegen_backend", AuthorityOnly),
        ("trust_bundle_foreign_crate", VerificationSelector),
        ("trust_cg_frontend", EvidenceControl),
        ("trust_audited_proc_macro", EvidenceControl),
        ("trust_admission_run_digest", EvidenceControl),
        ("trust_admission_unit_digest", EvidenceControl),
        ("trust_admission_semantics_digest", EvidenceControl),
        ("trust_admission_unit_role", EvidenceControl),
        ("trust_admission_compile_target", EvidenceControl),
        ("trust_proc_macro_boundary", EvidenceControl),
        // Trust (D21): where proc macros run. Not verification-conditional.
        ("trust_proc_macro_isolation", EvidenceControl),
        ("trust_ir_crate_module", EvidenceControl),
        ("trust_cg_output_gate", EvidenceControl),
        // Trust (step 2 increment 5, sub-step 5.4.2): which F1 lane ships the bytes.
        ("trust_cg_f1_backend", EvidenceControl),
        ("trust_ir_cg_args", EvidenceControl),
        ("trust_certified_test_monitors", EvidenceControl),
        ("trust_body_census", EvidenceControl),
        // Trust: diagnostic call observations have no proof authority.
        ("trust_body_census_calls", EvidenceControl),
        ("trust_instance_census", EvidenceControl),
        ("trust_lean_census", EvidenceControl),
        ("trust_memory_notes", VerificationSelector),
        ("trust_ctfe_trivial_probe", EvidenceControl),
        // Trust: EW18-DROPIN-1, only which temporaries a link leaves; see options.rs.
        ("trust_drop_rlib_objects", AuthorityOnly),
        ("trust_dump", EvidenceControl),
        ("trust_instance_flip", VerificationSelector),
        ("trust_instance_flip_mutate", EvidenceControl),
        ("trust_ir_flip", VerificationSelector),
        ("trust_instance_flip_probe", EvidenceControl),
        ("trust_sat_perturb", EvidenceControl),
        ("trust_ir_lower", AuthorityOnly),
        ("trust_no_adapter_yield", VerificationSelector),
        ("trust_no_r1", VerificationSelector),
        ("trust_option_flag_lanes", VerificationSelector),
        // Trust (DC-18a): a refusal, observable and independent of verification.
        ("trust_path_free", EvidenceControl),
        ("trust_policy", VerificationSelector),
        ("trust_proof_artifact_root", VerificationSelector),
        ("trust_clean_origin_mutate_emitter", EvidenceControl),
        ("trust_ir_lower_mutate_finalization", EvidenceControl),
        ("trust_targo_test_monitor", EvidenceControl),
        ("trust_test_mutate_derived_assert_msg", EvidenceControl),
        // e631a578dc declared it EvidenceControl without a row here or a probe arm below.
        ("trust_tool_inputs", EvidenceControl),
        ("trust_verify", AuthorityOnly),
        ("trust_verify_crate_role", EvidenceControl),
        ("trust_verify_effort", VerificationSelector),
        ("trust_verify_function_budget_ms", VerificationSelector),
        ("trust_verify_function_budget_steps", VerificationSelector),
        ("trust_verify_include_dependencies", VerificationSelector),
        ("trust_verify_level", VerificationSelector),
        ("trust_verify_output", VerificationSelector),
        ("trust_verify_package_name", EvidenceControl),
        ("trust_verify_profile", VerificationSelector),
        ("trust_verify_session", EvidenceControl),
        ("trust_verify_target_spec_sha256", EvidenceControl),
        ("trust_verify_timeout_ms", VerificationSelector),
        ("trust_verify_worker_threads", VerificationSelector),
        ("trust_witness", EvidenceControl),
        ("trust_witness_precise", EvidenceControl),
        ("trust_spawn_census_shadow", EvidenceControl),
        ("trust_send_census", EvidenceControl),
        ("trust_writer_census", EvidenceControl),
        ("trust_no_str_byte_position", EvidenceControl),
        ("trust_tinv", EvidenceControl),
        ("trust_ir_lower_mutate_rhs_effects", EvidenceControl),
        ("trust_ir_instance_seam_test", EvidenceControl),
        ("trust_test_instance_seam_mutation", EvidenceControl),
        ("trust_ir_template_instance_oracle", EvidenceControl),
        ("trust_test_template_oracle_mutation", EvidenceControl),
        ("trust_ir_seam_reference", EvidenceControl),
        ("trust_platform_properties", EvidenceControl),
        ("trust_platform_unanalysed", EvidenceControl),
        ("trust_platform_budget", EvidenceControl),
        ("trust_platform_report", EvidenceControl),
        ("trust_platform_dump_facts", EvidenceControl),
        ("trust_ir_lower_templates", EvidenceControl),
    ];
    let declared = UnstableOptions::TRUST_AUTHORITY_CONTROLS
        .iter()
        .map(|control| (control.field, control.class))
        .collect::<Vec<_>>();
    for (field, class) in EXPECTED {
        assert!(
            declared.contains(&(*field, *class)),
            "`{field}` is not declared {class:?}; declared: {:?}",
            declared.iter().find(|(declared, _)| declared == field),
        );
    }
    assert_eq!(
        declared.len(),
        EXPECTED.len(),
        "a classified option has no stated frontend disposition: {:?}",
        declared.iter().filter(|entry| !EXPECTED.contains(entry)).collect::<Vec<_>>(),
    );
}

/// The one selector effect that is NOT conditional on verification: a Unix-tool
/// verification profile declares the SIGPIPE disposition `main` installs, in every
/// lane (`Session::trust_effective_on_broken_pipe`, consumed by `rustc_passes`'
/// entry-point collector). Deauthorization must neutralize the profile without
/// changing that answer, or a deauthorized frontend that emits a binary would emit
/// a different one than the caller's configuration asked for.
#[test]
#[allow(rustc::bad_opt_access)]
fn deauthorization_preserves_the_profile_declared_sigpipe_disposition() {
    use rustc_target::spec::OnBrokenPipe;
    for profile in [
        None,
        Some("unix_hardened"),
        Some("coreutils_hardened"),
        Some("Unix-Hardened"),
        Some("hardened"),
        Some("not_a_registered_profile"),
    ] {
        for explicit in
            [OnBrokenPipe::Default, OnBrokenPipe::Kill, OnBrokenPipe::Error, OnBrokenPipe::Inherit]
        {
            let mut opts = Options::default();
            opts.unstable_opts.trust_verify_profile = profile.map(str::to_string);
            opts.unstable_opts.on_broken_pipe = explicit;
            let before = crate::trust_effective_on_broken_pipe_by_flags(explicit, profile);
            TrustFrontendAuthoritySnapshot::deauthorize(&mut opts);
            assert_eq!(opts.unstable_opts.trust_verify_profile, None);
            assert_eq!(
                crate::trust_effective_on_broken_pipe_by_flags(
                    opts.unstable_opts.on_broken_pipe,
                    opts.unstable_opts.trust_verify_profile.as_deref(),
                ),
                before,
                "profile={profile:?} on_broken_pipe={explicit:?}",
            );
        }
    }
    // Pinned, so the equality above cannot pass by both sides being `Default`.
    assert_eq!(
        crate::trust_effective_on_broken_pipe_by_flags(
            OnBrokenPipe::Default,
            Some("unix_hardened")
        ),
        OnBrokenPipe::Kill,
    );
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
        "trust_cg_frontend" => opts.trust_cg_frontend = "trust-ir".to_string(),
        // Trust (step 2 increment 5, sub-step 5.4.2): F1's consumer.
        "trust_cg_f1_backend" => opts.trust_cg_f1_backend = "compiler".to_string(),
        "trust_cg_output_gate" => opts.trust_cg_output_gate = "allow-unknown".to_string(),
        "trust_certified_test_monitors" => opts.trust_certified_test_monitors = true,
        "trust_ctfe_trivial_probe" => opts.trust_ctfe_trivial_probe = true,
        "trust_drop_rlib_objects" => opts.trust_drop_rlib_objects = true,
        // Trust: both carry `{ TRUST_AUTHORITY: EvidenceControl }`, which auto-enrols
        // them in `UnstableOptions::TRUST_AUTHORITY_CONTROLS`, so this match must
        // observe them or the probe below panics. Added here together on purpose:
        // 31 options carry the marker and this match had 29 arms, so fixing only
        // the one a failure log names just re-reds on the other.
        "trust_clean_origin_mutate_emitter" => opts.trust_clean_origin_mutate_emitter = true,
        "trust_instance_flip_probe" => {
            opts.trust_instance_flip_probe = Some("callback-probe".to_string())
        }
        "trust_dump" => {
            opts.trust_dump = TrustDump {
                mir: Some(PathBuf::from("callback-dump-mir")),
                mir_only: true,
                native_bundle: Some(PathBuf::from("callback-dump-native")),
                ir: Some(PathBuf::from("callback-ir-dump")),
                spec_clean: Some(PathBuf::from("callback-spec-clean-dump")),
            }
        }
        // Trust (wall A): the instance-flip lane's three controls. `trust_instance_flip_probe`
        // was left unwired when the MEASUREMENT probe landed (5e99e9a47b), which makes
        // `every_classified_control_is_observed_at_both_boundaries` panic on `no authority probe
        // for classified control` — a pre-existing RED at this base, repaired here alongside the
        // two controls the production seam adds.
        "trust_instance_flip" => opts.trust_instance_flip = false,
        "trust_instance_flip_mutate" => {
            opts.trust_instance_flip_mutate = Some("abi-swap".to_string())
        }
        "trust_ir_flip" => opts.trust_ir_flip = false,
        "trust_ir_lower" => opts.trust_ir_lower = Some(crate::config::TrustIrLower::On),
        "trust_ir_lower_mutate_finalization" => opts.trust_ir_lower_mutate_finalization = true,
        "trust_ir_lower_mutate_rhs_effects" => opts.trust_ir_lower_mutate_rhs_effects = true,
        // Trust (step 6.5.1, INC6.5-SWITCH): the level-S template lane's test-only switch.
        "trust_ir_lower_templates" => opts.trust_ir_lower_templates = true,
        // Trust (R8-SEAM): the crate-seam differential's cross-check hook.
        "trust_ir_instance_seam_test" => opts.trust_ir_instance_seam_test = true,
        "trust_test_instance_seam_mutation" => {
            opts.trust_test_instance_seam_mutation = Some("bool-constant".to_string())
        }
        // Trust (PKG-C2d2 slice 1): the template-instance TEST-ORACLE and its negative control.
        "trust_ir_template_instance_oracle" => opts.trust_ir_template_instance_oracle = true,
        "trust_test_template_oracle_mutation" => {
            opts.trust_test_template_oracle_mutation = Some("int-constant".to_string())
        }
        "trust_ir_seam_reference" => {
            opts.trust_ir_seam_reference = Some(PathBuf::from("callback-seam-reference"))
        }
        // Trust (v41 codegen license): the crate-module lane's selector, added
        // with the two trust-ir controls that were already enrolled and already
        // unobserved. All three carry `{ TRUST_AUTHORITY: EvidenceControl }`, so
        // `TRUST_AUTHORITY_CONTROLS` enrols them from the table itself and this
        // match panics on any it does not name — the same trap the wall-A
        // comment above records. Naming only the new one would leave the probe
        // red on the other two.
        "trust_ir_crate_module" => opts.trust_ir_crate_module = true,
        "trust_bundle_foreign_crate" => {
            opts.trust_bundle_foreign_crate = vec!["callback-crate".to_string()]
        }
        "trust_body_census" => opts.trust_body_census = Some(PathBuf::from("callback-body-census")),
        "trust_body_census_calls" => opts.trust_body_census_calls = true,
        "trust_audited_proc_macro" => {
            opts.trust_audited_proc_macro = vec!["callback-audited-proc-macro".to_string()]
        }
        "trust_proc_macro_boundary" => opts.trust_proc_macro_boundary = true,
        "trust_proc_macro_isolation" => opts.trust_proc_macro_isolation = true,
        "trust_instance_census" => {
            opts.trust_instance_census = Some(PathBuf::from("callback-instance-census"))
        }
        "trust_lean_census" => opts.trust_lean_census = Some(PathBuf::from("callback-lean-census")),
        "trust_memory_notes" => opts.trust_memory_notes = true,
        "trust_ir_cg_args" => opts.trust_ir_cg_args = vec!["callback-knob".to_string()],
        // Trust (D2 tier 1)
        "trust_no_adapter_yield" => opts.trust_no_adapter_yield = true,
        "trust_no_r1" => opts.trust_no_r1 = true,
        "trust_option_flag_lanes" => opts.trust_option_flag_lanes = false,
        "trust_path_free" => opts.trust_path_free = true,
        // Trust: classified by fd10e2b6ee (STR_BYTE_POSITION) without an arm here, which made
        // the loop above panic on it; found when R8-SEAM's option was added behind it.
        "trust_no_str_byte_position" => opts.trust_no_str_byte_position = true,
        // Trust (TINV step 10.0)
        "trust_tinv" => opts.trust_tinv = true,
        // Trust (platform protocols, plan L1a): the five controls of the platform-protocol
        // pass. Each moves to a value that parses, so the probe exercises a state a caller
        // could really set (`platform_protocol_controls_are_evidence_controls` below pins
        // that all five are here and classified as evidence).
        "trust_platform_properties" => {
            opts.trust_platform_properties =
                [super::TrustPlatformProperty::FdInherit].into_iter().collect()
        }
        "trust_platform_unanalysed" => {
            opts.trust_platform_unanalysed = super::TrustPlatformUnanalysed::Deny
        }
        "trust_platform_budget" => opts.trust_platform_budget = 1,
        "trust_platform_report" => opts.trust_platform_report = super::TrustPlatformReport::Verbose,
        "trust_platform_dump_facts" => {
            opts.trust_platform_dump_facts = Some(PathBuf::from("callback-platform-facts"))
        }
        "trust_policy" => opts.trust_policy = TrustPolicy::Advisory,
        "trust_proof_artifact_root" => {
            opts.trust_proof_artifact_root = Some(PathBuf::from("callback-proof-artifact-root"))
        }
        "trust_sat_perturb" => opts.trust_sat_perturb = Some("enum-reshape".to_string()),
        "trust_send_census" => opts.trust_send_census = true,
        "trust_spawn_census_shadow" => {
            opts.trust_spawn_census_shadow = super::TrustSpawnCensusShadow::Check
        }
        "trust_targo_test_monitor" => opts.trust_targo_test_monitor = true,
        "trust_test_mutate_derived_assert_msg" => opts.trust_test_mutate_derived_assert_msg = true,
        "trust_tool_inputs" => opts.trust_tool_inputs = true,
        "trust_verify" => opts.trust_verify = super::TrustVerify::Off,
        "trust_verify_crate_role" => opts.trust_verify_crate_role = "primary".to_string(),
        "trust_verify_effort" => opts.trust_verify_effort = 1,
        "trust_verify_function_budget_ms" => opts.trust_verify_function_budget_ms = 1,
        "trust_verify_function_budget_steps" => opts.trust_verify_function_budget_steps = 1,
        "trust_verify_include_dependencies" => opts.trust_verify_include_dependencies = true,
        "trust_verify_level" => opts.trust_verify_level = 1,
        "trust_verify_output" => opts.trust_verify_output = "json".to_string(),
        "trust_verify_package_name" => {
            opts.trust_verify_package_name = Some("callback-package".to_string())
        }
        "trust_verify_profile" => opts.trust_verify_profile = Some("callback-profile".to_string()),
        "trust_verify_session" => opts.trust_verify_session = Some("callback-session".to_string()),
        "trust_admission_run_digest" => opts.trust_admission_run_digest = Some("a".repeat(64)),
        "trust_admission_unit_digest" => opts.trust_admission_unit_digest = Some("b".repeat(64)),
        "trust_admission_semantics_digest" => {
            opts.trust_admission_semantics_digest = Some("c".repeat(64))
        }
        "trust_admission_unit_role" => opts.trust_admission_unit_role = Some("primary".into()),
        "trust_admission_compile_target" => {
            opts.trust_admission_compile_target = Some("aarch64-apple-darwin".into())
        }
        "trust_verify_target_spec_sha256" => {
            opts.trust_verify_target_spec_sha256 = Some("a".repeat(64))
        }
        "trust_verify_timeout_ms" => opts.trust_verify_timeout_ms = 1,
        "trust_verify_worker_threads" => opts.trust_verify_worker_threads = 1,
        "trust_witness" => opts.trust_witness = TrustWitness::Off,
        "trust_witness_precise" => opts.trust_witness_precise = true,
        "trust_writer_census" => opts.trust_writer_census = Some("callback-field".to_string()),
        other => panic!("no authority probe for classified control `{other}`"),
    }
}

/// Trust (platform protocols, plan L1a): the platform pass's controls decide which platform
/// verdicts a compilation can produce, so each must be an EVIDENCE control (a deauthorized
/// embedded frontend may not inherit a non-default value) and must have its own probe arm
/// above. Pinned by name, so dropping one from the table or reclassifying it fails here and not
/// only in the generic loop.
#[test]
#[allow(rustc::bad_opt_access)]
fn platform_protocol_controls_are_evidence_controls() {
    const PLATFORM_CONTROLS: [&str; 5] = [
        "trust_platform_properties",
        "trust_platform_unanalysed",
        "trust_platform_budget",
        "trust_platform_report",
        "trust_platform_dump_facts",
    ];
    let baseline = Options::default();
    assert_eq!(TrustFrontendAuthoritySnapshot::first_nondefault_evidence_control(&baseline), None);
    let authority = TrustFrontendAuthoritySnapshot::capture(&baseline);
    for field in PLATFORM_CONTROLS {
        let control = UnstableOptions::TRUST_AUTHORITY_CONTROLS
            .iter()
            .find(|control| control.field == field)
            .unwrap_or_else(|| panic!("`{field}` declares no TRUST_AUTHORITY class"));
        assert_eq!(control.class, TrustAuthorityClass::EvidenceControl, "{field}");
        assert_eq!(control.spelling(), format!("-Z{}", field.replace('_', "-")));

        let mut changed = baseline.clone();
        mutate_trust_control(&mut changed.unstable_opts, field);
        assert_eq!(authority.changed_option(&changed), Some(control.spelling()), "{field}");
        assert_eq!(
            TrustFrontendAuthoritySnapshot::first_nondefault_evidence_control(&changed),
            Some(control.spelling()),
            "{field}",
        );
    }
}

/// Trust (platform protocols, plan L1a; OD-1, PD-4): the platform pass runs, and may fail the
/// build, exactly when verification is on and a property is requested. The policy is not an
/// input: under `advisory` a refutation is still an error, while `-Ztrust-verify=off` never runs
/// the pass. Pinned pure, without a `Session`.
#[test]
fn platform_errors_require_verification_and_a_property() {
    use crate::config::{TrustPlatformProperties, TrustPlatformProperty};
    let none = TrustPlatformProperties::default();
    let fd_inherit: TrustPlatformProperties =
        [TrustPlatformProperty::FdInherit].into_iter().collect();
    assert!(crate::trust_platform_errors_enabled_by_flags(TrustVerify::On, &fd_inherit));
    assert!(!crate::trust_platform_errors_enabled_by_flags(TrustVerify::Off, &fd_inherit));
    assert!(!crate::trust_platform_errors_enabled_by_flags(TrustVerify::On, &none));
    assert!(!crate::trust_platform_errors_enabled_by_flags(TrustVerify::Off, &none));
    // The second deliberate exception to "only a proof claim may fail the build": advisory
    // makes no proof claim, and the platform pass may still fail it.
    assert!(!crate::trust_proof_claimed_by_flags(
        TrustVerify::On,
        crate::config::TrustPolicy::Advisory
    ));
}

/// `-Ztrust-verify=off` is the single master off-switch. Strict lowering is a
/// verification-quality property, so it is honoured in exactly one lane:
/// verification on AND `strict` requested. Every other combination — including
/// an explicit `strict` request with verification off — is non-strict, and the
/// frontend either runs as plain `on` or not at all per
/// `trust_ir_lower_enabled_by_flags`. Pinned pure, without a `Session`, so the
/// rule cannot drift from its stated form.
#[test]
fn strict_lowering_requires_verification() {
    use crate::config::TrustIrLower::{Off as IrOff, On as IrOn, Strict as IrStrict};
    for verify in [TrustVerify::On, TrustVerify::Off] {
        for requested in [None, Some(IrOff), Some(IrOn), Some(IrStrict)] {
            let expected = verify == TrustVerify::On && requested == Some(IrStrict);
            assert_eq!(
                crate::trust_ir_lower_strict_by_flags(verify, requested),
                expected,
                "verify={verify:?} requested={requested:?}",
            );
            // Strict never runs the frontend where `on` would not: a strict
            // answer implies the frontend is active in that lane.
            if crate::trust_ir_lower_strict_by_flags(verify, requested) {
                assert!(crate::trust_ir_lower_enabled_by_flags(verify, requested));
            }
        }
    }
}

#[test]
#[allow(rustc::bad_opt_access)]
fn deauthorization_is_monotonic_and_turns_off_verification_and_lowering() {
    for incoming_verify in [TrustVerify::On, TrustVerify::Off] {
        // Both the unset request and the canonicalized "resolved off" spelling
        // are states a deauthorized frontend inherits without complaint (and so,
        // below, is an explicit request: it is overwritten, never inherited).
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
            // A deauthorized frontend is non-strict for the same reason it is
            // non-verifying: strictness is a verification-quality property.
            assert!(!crate::trust_ir_lower_strict_by_flags(
                opts.unstable_opts.trust_verify,
                opts.unstable_opts.trust_ir_lower,
            ));
        }
    }

    // A lowering REQUEST — `on`, or ay's committed `strict` — is overwritten, not
    // inherited: a deauthorized frontend runs no lowering, so nothing the request
    // selects can reach the compilation, in either verification lane.
    for incoming_verify in [TrustVerify::On, TrustVerify::Off] {
        for requested in [crate::config::TrustIrLower::On, crate::config::TrustIrLower::Strict] {
            let mut lowering = Options::default();
            lowering.unstable_opts.trust_verify = incoming_verify;
            lowering.unstable_opts.trust_ir_lower = Some(requested);
            assert_eq!(
                TrustFrontendAuthoritySnapshot::first_nondefault_evidence_control(&lowering),
                None,
            );
            TrustFrontendAuthoritySnapshot::deauthorize(&mut lowering);
            assert_eq!(
                lowering.unstable_opts.trust_ir_lower,
                Some(crate::config::TrustIrLower::Off)
            );
            assert!(!crate::trust_ir_lower_enabled_by_flags(
                lowering.unstable_opts.trust_verify,
                lowering.unstable_opts.trust_ir_lower,
            ));
        }
    }
}

// Trust: EW18-DROPIN-1 (2026-11-05). The Darwin rlib-object deletion is a
// caller's own opt-in: a deauthorized frontend holds upstream's default, so the
// objects its link leaves are the ones upstream rustc's would leave.
#[test]
#[allow(rustc::bad_opt_access)]
fn deauthorization_resets_the_rlib_object_deletion_to_upstreams_default() {
    let mut opts = Options::default();
    opts.unstable_opts.trust_drop_rlib_objects = true;
    assert_eq!(TrustFrontendAuthoritySnapshot::first_nondefault_evidence_control(&opts), None);
    TrustFrontendAuthoritySnapshot::deauthorize(&mut opts);
    assert!(!opts.unstable_opts.trust_drop_rlib_objects);
    assert_eq!(
        opts.unstable_opts.trust_drop_rlib_objects,
        Options::default().unstable_opts.trust_drop_rlib_objects
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
    assert_eq!(state.enter(CompilerBackendRoute::EvidenceInert), Err(EVIDENCE_INERT_AFTER_BACKEND),);
}

#[test]
fn evidence_inert_route_is_a_process_dedication_not_a_reentrant_lock() {
    let mut state = CompilerBackendRouteState::Pristine;
    assert_eq!(state.enter(CompilerBackendRoute::EvidenceInert), Ok(()));
    assert_eq!(state.enter(CompilerBackendRoute::EvidenceInert), Err(EVIDENCE_INERT_PROCESS_REUSE),);
    assert_eq!(
        state.enter(CompilerBackendRoute::BackendCapable),
        Err(BACKEND_AFTER_EVIDENCE_INERT),
    );
}

#[test]
fn evidence_inert_guard_is_structural_and_blocks_concurrent_backend_routes() {
    let state = isolated_compiler_backend_route_state();
    let guard = enter_compiler_backend_route_with_state(CompilerBackendRoute::EvidenceInert, state)
        .expect("first evidence-inert route must dedicate a pristine process");
    assert!(guard.validates(CompilerBackendRoute::EvidenceInert));
    assert!(!guard.validates(CompilerBackendRoute::BackendCapable));

    let error = thread::spawn(move || {
        enter_compiler_backend_route_with_state(CompilerBackendRoute::BackendCapable, state).err()
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
            let _guard =
                enter_compiler_backend_route_with_state(CompilerBackendRoute::EvidenceInert, state)
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
        enter_compiler_backend_route_with_state(CompilerBackendRoute::EvidenceInert, state).err(),
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

// Trust: ambient switches that alter obligation emission or producer output
// must have the same refusal boundary as the existing semantic controls.
#[test]
#[allow(rustc::bad_opt_access)]
fn ambient_producer_and_std_discharge_controls_are_rejected() {
    use crate::config::TrustIrLower::{Off as IrOff, On as IrOn, Strict as IrStrict};
    for (verify, lower, reject) in [
        (TrustVerify::On, None, true),
        (TrustVerify::On, Some(IrOff), true),
        (TrustVerify::Off, None, false),
        (TrustVerify::Off, Some(IrOff), false),
        (TrustVerify::Off, Some(IrOn), true),
        (TrustVerify::Off, Some(IrStrict), true),
    ] {
        let mut opts = Options::default();
        opts.unstable_opts.trust_verify = verify;
        opts.unstable_opts.trust_ir_lower = lower;
        for key in [
            "TRUST_STD_UNSAFE_CALL_SKIP",
            "TRUST_OPTION_FLAG_LANES",
            "TRUST_SHARED_RECV_PLACE",
            "TRUST_NSA",
        ] {
            assert_eq!(
                forbidden_trust_environment_key(&opts, [OsString::from(key)]),
                reject.then(|| OsString::from(key)),
                "{key}: verify={verify:?} lower={lower:?}",
            );
            let lowercase = key.to_ascii_lowercase();
            assert!(is_legacy_trust_semantic_env_with_windows_semantics(
                OsStr::new(&lowercase),
                true,
            ));
            assert!(!is_legacy_trust_semantic_env_with_windows_semantics(
                OsStr::new(&lowercase),
                false,
            ));
        }
        // This adjacent switch only prints diagnostics; it must not become a
        // semantic input merely because it shares the unsafe-call prefix.
        assert_eq!(
            forbidden_trust_environment_key(&opts, [OsString::from("TRUST_UNSAFE_CALL_DEBUG")]),
            None,
        );
    }
}

// Trust: bundle composition, closure limits, and CHC encoding are semantic
// inputs even when a supplied value would leave their default unchanged.
#[test]
#[allow(rustc::bad_opt_access)]
fn ambient_composition_bundle_and_chc_controls_are_rejected() {
    use crate::config::TrustIrLower::{Off as IrOff, On as IrOn, Strict as IrStrict};
    for (verify, lower, reject) in [
        (TrustVerify::On, None, true),
        (TrustVerify::On, Some(IrOff), true),
        (TrustVerify::Off, None, false),
        (TrustVerify::Off, Some(IrOff), false),
        (TrustVerify::Off, Some(IrOn), true),
        (TrustVerify::Off, Some(IrStrict), true),
    ] {
        let mut opts = Options::default();
        opts.unstable_opts.trust_verify = verify;
        opts.unstable_opts.trust_ir_lower = lower;
        for key in [
            "TRUST_COMPOSE_NO_SCOPE",
            "TRUST_BUNDLE_CAP",
            "TRUST_MAX_BUNDLE_FUNCTIONS",
            "TRUST_NO_BUNDLE_DECLARED",
            "TRUST_MC_DATAFLOW_CHC",
        ] {
            assert_eq!(
                forbidden_trust_environment_key(&opts, [OsString::from(key)]),
                reject.then(|| OsString::from(key)),
                "{key}: verify={verify:?} lower={lower:?}",
            );
            let lowercase = key.to_ascii_lowercase();
            assert!(is_legacy_trust_semantic_env_with_windows_semantics(
                OsStr::new(&lowercase),
                true,
            ));
            assert!(!is_legacy_trust_semantic_env_with_windows_semantics(
                OsStr::new(&lowercase),
                false,
            ));
        }
        // This classifier must not reinterpret diagnostic, typed-off,
        // bootstrap, or machine-admission transports as these five controls.
        // Their own handlers retain responsibility for validating their values.
        for key in [
            "TRUST_COMPOSE_DEBUG",
            "TRUST_BUNDLE_TRACE",
            "TRUST_MC_DATAFLOW_CHC_DEBUG",
            "TRUST_MC_STAGE_TIMINGS",
            "TRUST_MC_CHC_ROW_EXPORT_DIR",
            "TRUST_NO_VERIFY",
            "TRUST_BOOTSTRAP_SHIM_VERIFY_UNITS",
            "BUILD_SLOT_HELD",
            "BUILD_SLOT_ATERM_CLI",
            "CARGO_BUILD_JOBS",
        ] {
            assert_eq!(
                forbidden_trust_environment_key(&opts, [OsString::from(key)]),
                None,
                "{key} must retain its separate transport contract",
            );
        }
    }
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
        assert!(!is_untracked_trust_codegen_env_with_windows_semantics(OsStr::new(key), false,));
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

#[test]
fn builtin_target_llvm_args_survive_the_authenticated_lane() {
    // Regression: the authenticated-session check rejected ANY non-empty
    // `llvm_args` while its diagnostic said "custom-target". Built-in wasm
    // targets carry a compiler-owned `-wasm-use-legacy-eh=false`, so every wasm
    // target was unbuildable under `targo trust build` — it failed before crate
    // resolution, on `core` itself. iOS and Android passed only because their
    // specs happen to carry no `llvm_args` at all.
    //
    // Rejecting a built-in target's own options rejects the linked compiler's
    // target table, not anything the invoker supplied, so it cannot be what the
    // proof TCB is protecting.
    let wasm = TargetTuple::from_tuple("wasm32-unknown-unknown");
    assert!(target_is_exact_builtin(&wasm));
    assert_eq!(authenticated_target_llvm_args_error(&wasm, true), None);
    assert_eq!(evidence_inert_target_llvm_args_error(&wasm, true), None);
}

#[test]
fn custom_target_llvm_args_are_still_refused_in_the_authenticated_lane() {
    // The actual threat the check exists for: a JSON target the invoker wrote
    // can smuggle LLVM plugin loading into a session that claims a proof.
    let custom = TargetTuple::TargetJson {
        path_for_rustdoc: std::path::PathBuf::new(),
        tuple: "my-evil-target".to_string(),
        contents: "{}".to_string(),
    };
    assert!(!target_is_exact_builtin(&custom));
    let err = authenticated_target_llvm_args_error(&custom, true)
        .expect("a custom target with llvm_args must be refused");
    assert!(err.contains("my-evil-target"), "the diagnostic must name the target: {err}");
    assert!(evidence_inert_target_llvm_args_error(&custom, true).is_some());
}

#[test]
fn no_llvm_args_is_never_an_error_either_way() {
    let wasm = TargetTuple::from_tuple("wasm32-unknown-unknown");
    assert_eq!(authenticated_target_llvm_args_error(&wasm, false), None);
    assert_eq!(evidence_inert_target_llvm_args_error(&wasm, false), None);
}

/// A Trust finding may FAIL a build only when a proof is being CLAIMED:
/// verification on AND a fail-closed policy. `-Ztrust-verify=off` claims
/// nothing whatever the policy says — including the default `strict` — and
/// `advisory` reports without enforcing. Pinned pure, over every policy, so
/// the finalizer's routing (`rustc_mir_build::trust_ir_crate_finalize`) cannot
/// drift from the rule.
#[test]
fn proof_claim_requires_verification_and_a_fail_closed_policy() {
    use super::TrustPolicy;
    for verify in [TrustVerify::On, TrustVerify::Off] {
        for policy in [
            TrustPolicy::Strict,
            TrustPolicy::Certify,
            TrustPolicy::Advisory,
            TrustPolicy::MemorySafe,
        ] {
            let expected = verify == TrustVerify::On && policy != TrustPolicy::Advisory;
            assert_eq!(
                crate::trust_proof_claimed_by_flags(verify, policy),
                expected,
                "verify={verify:?} policy={policy:?}"
            );
        }
    }
    assert!(
        !crate::trust_proof_claimed_by_flags(TrustVerify::Off, TrustPolicy::Strict),
        "the off-switch must win over the default fail-closed policy"
    );
}

#![allow(rustc::bad_opt_access)]
use std::collections::BTreeMap;
use std::num::NonZero;
use std::path::PathBuf;
use std::sync::atomic::AtomicBool;

use rustc_abi::Align;
use rustc_codegen_ssa::traits::CodegenBackend;
use rustc_data_structures::profiling::TimePassesFormat;
use rustc_errors::ColorConfig;
use rustc_errors::emitter::HumanReadableErrorType;
use rustc_hir::attrs::{CollapseMacroDebuginfo, NativeLibKind};
use rustc_session::config::{
    AnnotateMoves, AutoDiff, BranchProtection, CFGuard, Cfg, CodegenRetagOptions, CoverageLevel,
    CoverageOptions, CrateType, DebugInfo, DumpMonoStatsFormat, ErrorOutputType, ExternEntry,
    ExternLocation, Externs, FmtDebug, FunctionReturn, IncrementalStateAssertion,
    InliningThreshold, Input, InstrumentCoverage, InstrumentMcount, InstrumentXRay,
    LinkSelfContained, LinkerPluginLto, LocationDetail, LtoCli, MirIncludeSpans, NextSolverConfig,
    Offload, Options, OutFileName, OutputType, OutputTypes, PAuthKey, PacRet, Passes,
    PatchableFunctionEntry, Polonius, ProcMacroExecutionStrategy, Strip, SwitchWithOptPath,
    SymbolManglingVersion, TrustIrLower, TrustPolicy, TrustVerify, TrustWitness, WasiExecModel,
    build_configuration, build_session_options, rustc_optgroups,
};
use rustc_session::lint::Level;
use rustc_session::search_paths::SearchPath;
use rustc_session::utils::{CanonicalizedPath, NativeLib};
use rustc_session::{CompilerIO, EarlyDiagCtxt, Session, build_session, getopts};
use rustc_span::edition::{DEFAULT_EDITION, Edition};
use rustc_span::source_map::{RealFileLoader, SourceMapInputs};
use rustc_span::{FileName, RealFileName, RemapPathScopeComponents, SourceFileHashAlgorithm, sym};
use rustc_target::spec::{
    CodeModel, FramePointer, LinkerFlavorCli, MergeFunctions, OnBrokenPipe, PanicStrategy,
    RelocModel, RelroLevel, SanitizerSet, SplitDebuginfo, StackProtector, TlsModel,
};

use crate::interface::{
    apply_no_trust_evidence_typed_policy, callback_codegen_backend_factory_conflicts,
    expected_explicit_codegen_backend_name, explicit_codegen_backend_name_mismatch,
    finalize_untracked_session_state, initialize_checked_jobserver,
    no_trust_evidence_codegen_backend_error, no_trust_evidence_typed_backend_control, parse_cfg,
};
use crate::util::DummyCodegenBackend;

#[test]
fn explicit_codegen_backend_identity_is_not_callback_spoofable() {
    assert_eq!(expected_explicit_codegen_backend_name("llvm"), Some("llvm"));
    assert_eq!(expected_explicit_codegen_backend_name("trust-cg"), Some("trust-cg"));
    assert_eq!(expected_explicit_codegen_backend_name("trust_cg"), Some("trust-cg"));
    assert_eq!(
        expected_explicit_codegen_backend_name("/tmp/librustc_codegen_custom.so"),
        None,
        "an explicit dylib is authenticated by the loader's exact path"
    );

    assert_eq!(explicit_codegen_backend_name_mismatch("llvm", "llvm"), None);
    assert_eq!(explicit_codegen_backend_name_mismatch("trust_cg", "trust-cg"), None);
    assert_eq!(explicit_codegen_backend_name_mismatch("trust-cg", "llvm"), Some("trust-cg"));
    assert_eq!(explicit_codegen_backend_name_mismatch("llvm", "trust-cg"), Some("llvm"));

    assert!(callback_codegen_backend_factory_conflicts(Some("trust-cg"), true, false, false));
    assert!(callback_codegen_backend_factory_conflicts(Some("llvm"), true, false, false));
    assert!(callback_codegen_backend_factory_conflicts(None, true, true, false));
    assert!(callback_codegen_backend_factory_conflicts(None, true, false, true));
    assert!(!callback_codegen_backend_factory_conflicts(None, true, false, false));
    assert!(!callback_codegen_backend_factory_conflicts(Some("trust-cg"), false, true, true));
}

#[test]
fn no_trust_evidence_accepts_only_builtin_non_evidence_backend_routes() {
    assert_eq!(no_trust_evidence_codegen_backend_error(None, "llvm", false, true), None);
    assert_eq!(no_trust_evidence_codegen_backend_error(None, "dummy", false, true), None);

    for target_default in ["trust-cg", "trust_cg", "/tmp/librustc_codegen_custom.so"] {
        let error = no_trust_evidence_codegen_backend_error(None, target_default, false, false)
            .expect("target-selected backend must fail closed");
        assert!(error.contains(target_default), "{error}");
    }

    assert!(
        no_trust_evidence_codegen_backend_error(Some("llvm"), "llvm", false, true)
            .unwrap()
            .contains("explicit -Zcodegen-backend")
    );
    assert!(
        no_trust_evidence_codegen_backend_error(None, "llvm", true, true)
            .unwrap()
            .contains("callback-provided")
    );
    assert!(
        no_trust_evidence_codegen_backend_error(None, "llvm", false, false)
            .unwrap()
            .contains("already-linked")
    );
}

#[test]
fn direct_interface_no_trust_evidence_policy_forces_off_and_rejects_outputs() {
    let mut opts = Options::default();
    opts.unstable_opts.trust_verify = TrustVerify::On;
    apply_no_trust_evidence_typed_policy(&mut opts).unwrap();
    assert_eq!(opts.unstable_opts.trust_verify, TrustVerify::Off);
    assert_eq!(opts.unstable_opts.trust_ir_lower, Some(TrustIrLower::Off));

    let mut custom_backend = Options::default();
    custom_backend.unstable_opts.codegen_backend = Some("custom-embedded-backend".to_string());
    apply_no_trust_evidence_typed_policy(&mut custom_backend).unwrap();
    assert_eq!(
        custom_backend.unstable_opts.codegen_backend.as_deref(),
        Some("custom-embedded-backend"),
    );
    assert_eq!(custom_backend.unstable_opts.trust_verify, TrustVerify::Off);
    assert_eq!(custom_backend.unstable_opts.trust_ir_lower, Some(TrustIrLower::Off),);

    let mut llvm_plugin = Options::default();
    llvm_plugin.unstable_opts.llvm_plugins.push("/tmp/plugin".to_string());
    assert_eq!(no_trust_evidence_typed_backend_control(&llvm_plugin), Some("-Zllvm-plugins"),);

    let mut autodiff = Options::default();
    autodiff.unstable_opts.autodiff.push(AutoDiff::Enable);
    assert_eq!(no_trust_evidence_typed_backend_control(&autodiff), Some("-Zautodiff"),);

    let mut autodiff_passes = Options::default();
    autodiff_passes.unstable_opts.autodiff_post_passes = Some("default<O2>".to_string());
    assert_eq!(
        no_trust_evidence_typed_backend_control(&autodiff_passes),
        Some("-Zautodiff-post-passes"),
    );

    let mut llvm_args = Options::default();
    llvm_args.cg.llvm_args.push("-load=/tmp/plugin".to_string());
    assert_eq!(no_trust_evidence_typed_backend_control(&llvm_args), Some("-Cllvm-args"),);

    let mut lowering = Options::default();
    lowering.unstable_opts.trust_ir_lower = Some(TrustIrLower::On);
    assert_eq!(
        apply_no_trust_evidence_typed_policy(&mut lowering),
        Err("-Ztrust-ir-lower".to_string()),
    );

    let mut output = Options::default();
    output.unstable_opts.trust_dump.ir = Some(PathBuf::from("must-not-publish"));
    assert_eq!(apply_no_trust_evidence_typed_policy(&mut output), Err("-Ztrust-dump".to_string()),);

    let mut session = Options::default();
    session.unstable_opts.trust_verify_session = Some("must-not-prove".to_string());
    assert_eq!(
        apply_no_trust_evidence_typed_policy(&mut session),
        Err("-Ztrust-verify-session".to_string()),
    );

    let mut artifact = Options::default();
    artifact.unstable_opts.trust_proof_artifact_root = Some(PathBuf::from("/must-not-publish"));
    assert_eq!(
        apply_no_trust_evidence_typed_policy(&mut artifact),
        Err("-Ztrust-proof-artifact-root".to_string()),
    );

    let mut internal_identity = Options::default();
    internal_identity.trust_solver_content_fingerprint = "ay:sha256:caller".to_string();
    assert_eq!(
        apply_no_trust_evidence_typed_policy(&mut internal_identity),
        Err("compiler-populated Trust solver content fingerprint".to_string()),
    );
}

#[test]
fn dummy_backend_does_not_advertise_frontend_only_binary_support_as_linkable() {
    sess_and_cfg(&[], |sess, _cfg| {
        let backend = DummyCodegenBackend { target_config_override: None };
        assert!(backend.supported_crate_types(&sess).contains(&CrateType::Executable));
        assert_eq!(backend.supported_link_crate_types(&sess), vec![CrateType::Rlib]);
    });
}

fn sess_and_cfg<F>(args: &[&'static str], f: F)
where
    F: FnOnce(Session, Cfg),
{
    let mut early_dcx = EarlyDiagCtxt::new(ErrorOutputType::default());
    initialize_checked_jobserver(&early_dcx);

    let matches = optgroups().parse(args).unwrap();
    let sessopts = build_session_options(&mut early_dcx, &matches);
    let target = rustc_session::config::build_target_config(
        &early_dcx,
        &sessopts.target_triple,
        sessopts.sysroot.path(),
        sessopts.unstable_opts.unstable_options,
    );
    let hash_kind = sessopts.unstable_opts.src_hash_algorithm(&target);
    let checksum_hash_kind = sessopts.unstable_opts.checksum_hash_algorithm();
    let sm_inputs = Some(SourceMapInputs {
        file_loader: Box::new(RealFileLoader) as _,
        path_mapping: sessopts.file_path_mapping(),
        hash_kind,
        checksum_hash_kind,
    });

    rustc_span::create_session_globals_then(DEFAULT_EDITION, &[], sm_inputs, || {
        let temps_dir = sessopts.unstable_opts.temps_dir.as_deref().map(PathBuf::from);
        let io = CompilerIO {
            input: Input::Str { name: FileName::Custom(String::new()), input: String::new() },
            output_dir: None,
            output_file: None,
            temps_dir,
        };

        static USING_INTERNAL_FEATURES: AtomicBool = AtomicBool::new(false);

        let sess = build_session(
            sessopts,
            io,
            Default::default(),
            target,
            "",
            None,
            &USING_INTERNAL_FEATURES,
        );
        let cfg = parse_cfg(sess.dcx(), matches.opt_strs("cfg"));
        let cfg = build_configuration(&sess, cfg);
        f(sess, cfg)
    });
}

fn new_public_extern_entry<S, I>(locations: I) -> ExternEntry
where
    S: Into<String>,
    I: IntoIterator<Item = S>,
{
    let locations =
        locations.into_iter().map(|s| CanonicalizedPath::new(PathBuf::from(s.into()))).collect();

    ExternEntry {
        location: ExternLocation::ExactPaths(locations),
        is_private_dep: false,
        add_prelude: true,
        nounused_dep: false,
        force: false,
    }
}

fn optgroups() -> getopts::Options {
    let mut opts = getopts::Options::new();
    for group in rustc_optgroups() {
        group.apply(&mut opts);
    }
    return opts;
}

fn mk_map<K: Ord, V>(entries: Vec<(K, V)>) -> BTreeMap<K, V> {
    BTreeMap::from_iter(entries.into_iter())
}

fn assert_same_clone(x: &Options) {
    assert_eq!(x.dep_tracking_hash(true), x.clone().dep_tracking_hash(true));
    assert_eq!(x.dep_tracking_hash(false), x.clone().dep_tracking_hash(false));
}

fn assert_same_hash(x: &Options, y: &Options) {
    assert_eq!(x.dep_tracking_hash(true), y.dep_tracking_hash(true));
    assert_eq!(x.dep_tracking_hash(false), y.dep_tracking_hash(false));
    // Check clone
    assert_same_clone(x);
    assert_same_clone(y);
}

#[track_caller]
fn assert_different_hash(x: &Options, y: &Options) {
    assert_ne!(x.dep_tracking_hash(true), y.dep_tracking_hash(true));
    assert_ne!(x.dep_tracking_hash(false), y.dep_tracking_hash(false));
    // Check clone
    assert_same_clone(x);
    assert_same_clone(y);
}

fn assert_non_crate_hash_different(x: &Options, y: &Options) {
    assert_eq!(x.dep_tracking_hash(true), y.dep_tracking_hash(true));
    assert_ne!(x.dep_tracking_hash(false), y.dep_tracking_hash(false));
    // Check clone
    assert_same_clone(x);
    assert_same_clone(y);
}

// When the user supplies --test we should implicitly supply --cfg test
#[test]
fn test_switch_implies_cfg_test() {
    sess_and_cfg(&["--test"], |_sess, cfg| {
        assert!(cfg.contains(&(sym::test, None)));
    })
}

// When the user supplies --test and --cfg test, don't implicitly add another --cfg test
#[test]
fn test_switch_implies_cfg_test_unless_cfg_test() {
    sess_and_cfg(&["--test", "--cfg=test"], |_sess, cfg| {
        let mut test_items = cfg.iter().filter(|&&(name, _)| name == sym::test);
        assert!(test_items.next().is_some());
        assert!(test_items.next().is_none());
    });
}

// Trust: the public cfg must use exactly the same batteries-on activation
// predicate as the MIR pass. `-Ztrust-verify=off` is the sole off-switch.
#[test]
fn trust_verify_cfg_matches_activation_flags() {
    let cases: &[(&[&str], bool)] = &[
        (&[], true),
        (&["-Ztrust-verify=off"], false),
        (&["-Ztrust-verify=on"], true),
        (&["-Ztrust-policy=advisory"], true),
        (&["-Ztrust-policy=advisory", "-Ztrust-verify=off"], false),
    ];

    for &(args, expected) in cases {
        sess_and_cfg(args, |sess, cfg| {
            assert_eq!(sess.trust_verification_enabled(), expected, "arguments: {args:?}");
            assert_eq!(cfg.contains(&(sym::trust_verify, None)), expected, "arguments: {args:?}");
        });
    }
}

#[test]
fn trust_verification_gets_fresh_non_crate_incremental_identity() {
    let mut first = None;
    sess_and_cfg(&[], |mut sess, _cfg| {
        finalize_untracked_session_state(&mut sess, None);
        first = Some((sess.opts.dep_tracking_hash(true), sess.opts.dep_tracking_hash(false)));
    });

    let mut second = None;
    sess_and_cfg(&[], |mut sess, _cfg| {
        finalize_untracked_session_state(&mut sess, None);
        second = Some((sess.opts.dep_tracking_hash(true), sess.opts.dep_tracking_hash(false)));
    });

    let (first_crate, first_full) = first.expect("first session hash");
    let (second_crate, second_full) = second.expect("second session hash");
    assert_eq!(first_crate, second_crate, "freshness must not perturb downstream crate hashes");
    assert_ne!(first_full, second_full, "each proof invocation must invalidate query reuse");

    let mut vanilla_first = None;
    sess_and_cfg(&["-Ztrust-verify=off"], |mut sess, _cfg| {
        finalize_untracked_session_state(&mut sess, None);
        vanilla_first = Some(sess.opts.dep_tracking_hash(false));
    });
    let mut vanilla_second = None;
    sess_and_cfg(&["-Ztrust-verify=off"], |mut sess, _cfg| {
        finalize_untracked_session_state(&mut sess, None);
        vanilla_second = Some(sess.opts.dep_tracking_hash(false));
    });
    assert_eq!(vanilla_first, vanilla_second, "explicit vanilla rustc stays deterministic");
}

#[test]
fn trust_crate_roles_are_reporting_only_and_cannot_weaken_strict_scope() {
    const CASES: &[(&str, &[&str])] = &[
        ("unscoped", &["-Ztrust-verify-crate-role=unscoped"]),
        ("primary", &["-Ztrust-verify-crate-role=primary"]),
        ("dependency", &["-Ztrust-verify-crate-role=dependency"]),
        (
            "dependency+include-dependencies",
            &["-Ztrust-verify-crate-role=dependency", "-Ztrust-verify-include-dependencies"],
        ),
        (
            "build-script+include-dependencies",
            &["-Ztrust-verify-crate-role=build-script", "-Ztrust-verify-include-dependencies"],
        ),
    ];

    for &(role, args) in CASES {
        sess_and_cfg(args, |sess, _cfg| {
            assert!(sess.trust_verification_enabled());
            assert!(sess.trust_strict_verification_enabled(), "role={role}");
        });
    }
}

#[test]
fn trust_solver_content_fingerprint_changes_the_crate_hash() {
    let reference = Options::default();
    let mut changed = reference.clone();
    changed.trust_solver_content_fingerprint = "ay:sha256:test-content".to_string();

    assert_ne!(
        reference.dep_tracking_hash(true),
        changed.dep_tracking_hash(true),
        "the exact solver content identity can affect emitted MIR and must be crate-tracked"
    );
    assert_ne!(reference.dep_tracking_hash(false), changed.dep_tracking_hash(false));
}

// Trust: proof/certificate extension state belongs to one compiler invocation;
// a rustc_driver process may construct multiple Sessions sequentially.
#[test]
fn trust_compiler_state_is_isolated_between_sessions() {
    #[derive(Default)]
    struct Probe(u32);

    sess_and_cfg(&[], |sess, _cfg| {
        sess.with_trust_compiler_state::<Probe, _>(|probe| probe.0 = 41);
        assert_eq!(sess.with_trust_compiler_state::<Probe, _>(|probe| probe.0), 41);
    });
    sess_and_cfg(&[], |sess, _cfg| {
        assert_eq!(sess.with_trust_compiler_state::<Probe, _>(|probe| probe.0), 0);
    });
}

#[test]
fn test_can_print_warnings() {
    sess_and_cfg(&["-Awarnings"], |sess, _cfg| {
        assert!(!sess.dcx().can_emit_warnings());
    });

    sess_and_cfg(&["-Awarnings", "-Dwarnings"], |sess, _cfg| {
        assert!(sess.dcx().can_emit_warnings());
    });

    sess_and_cfg(&["-Adead_code"], |sess, _cfg| {
        assert!(sess.dcx().can_emit_warnings());
    });
}

// `-Zremap-cwd-prefix` must not be merged into the tracked `remap_path_prefix` option:
// storing the absolute cwd there invalidates the incremental cache across build
// directories (see #132132). It must instead be applied via `file_path_mapping`.
#[test]
fn test_remap_cwd_prefix_not_in_remap_path_prefix() {
    sess_and_cfg(
        &["--remap-path-prefix=/explicit=mapped", "-Zremap-cwd-prefix=cwd-mapped"],
        |sess, _cfg| {
            // The tracked option holds only the explicit `--remap-path-prefix` entry.
            assert_eq!(
                sess.opts.remap_path_prefix,
                vec![(PathBuf::from("/explicit"), PathBuf::from("mapped"))],
            );

            // ... but the cwd remapping is still applied via `file_path_mapping`.
            let cwd = std::env::current_dir().unwrap();
            let remapped = sess
                .opts
                .file_path_mapping()
                .to_real_filename(&RealFileName::empty(), cwd.join("foo.rs"))
                .path(RemapPathScopeComponents::DEBUGINFO)
                .to_path_buf();
            assert_eq!(remapped, PathBuf::from("cwd-mapped/foo.rs"));
        },
    );
}

#[test]
fn test_output_types_tracking_hash_different_paths() {
    let mut v1 = Options::default();
    let mut v2 = Options::default();
    let mut v3 = Options::default();

    v1.output_types = OutputTypes::new(&[(
        OutputType::Exe,
        Some(OutFileName::Real(PathBuf::from("./some/thing"))),
    )]);
    v2.output_types = OutputTypes::new(&[(
        OutputType::Exe,
        Some(OutFileName::Real(PathBuf::from("/some/thing"))),
    )]);
    v3.output_types = OutputTypes::new(&[(OutputType::Exe, None)]);

    assert_non_crate_hash_different(&v1, &v2);
    assert_non_crate_hash_different(&v1, &v3);
    assert_non_crate_hash_different(&v2, &v3);
}

#[test]
fn test_output_types_tracking_hash_different_construction_order() {
    let mut v1 = Options::default();
    let mut v2 = Options::default();

    v1.output_types = OutputTypes::new(&[
        (OutputType::Exe, Some(OutFileName::Real(PathBuf::from("./some/thing")))),
        (OutputType::Bitcode, Some(OutFileName::Real(PathBuf::from("./some/thing.bc")))),
    ]);

    v2.output_types = OutputTypes::new(&[
        (OutputType::Bitcode, Some(OutFileName::Real(PathBuf::from("./some/thing.bc")))),
        (OutputType::Exe, Some(OutFileName::Real(PathBuf::from("./some/thing")))),
    ]);

    assert_same_hash(&v1, &v2);
}

#[test]
fn test_externs_tracking_hash_different_construction_order() {
    let mut v1 = Options::default();
    let mut v2 = Options::default();
    let mut v3 = Options::default();

    v1.externs = Externs::new(mk_map(vec![
        (String::from("a"), new_public_extern_entry(vec!["b", "c"])),
        (String::from("d"), new_public_extern_entry(vec!["e", "f"])),
    ]));

    v2.externs = Externs::new(mk_map(vec![
        (String::from("d"), new_public_extern_entry(vec!["e", "f"])),
        (String::from("a"), new_public_extern_entry(vec!["b", "c"])),
    ]));

    v3.externs = Externs::new(mk_map(vec![
        (String::from("a"), new_public_extern_entry(vec!["b", "c"])),
        (String::from("d"), new_public_extern_entry(vec!["f", "e"])),
    ]));

    assert_same_hash(&v1, &v2);
    assert_same_hash(&v1, &v3);
    assert_same_hash(&v2, &v3);
}

#[test]
fn test_lints_tracking_hash_different_values() {
    let mut v1 = Options::default();
    let mut v2 = Options::default();
    let mut v3 = Options::default();

    v1.lint_opts = vec![
        (String::from("a"), Level::Allow),
        (String::from("b"), Level::Warn),
        (String::from("c"), Level::Deny),
        (String::from("d"), Level::Forbid),
    ];

    v2.lint_opts = vec![
        (String::from("a"), Level::Allow),
        (String::from("b"), Level::Warn),
        (String::from("X"), Level::Deny),
        (String::from("d"), Level::Forbid),
    ];

    v3.lint_opts = vec![
        (String::from("a"), Level::Allow),
        (String::from("b"), Level::Warn),
        (String::from("c"), Level::Forbid),
        (String::from("d"), Level::Deny),
    ];

    assert_non_crate_hash_different(&v1, &v2);
    assert_non_crate_hash_different(&v1, &v3);
    assert_non_crate_hash_different(&v2, &v3);
}

#[test]
fn test_lints_tracking_hash_different_construction_order() {
    let mut v1 = Options::default();
    let mut v2 = Options::default();

    v1.lint_opts = vec![
        (String::from("a"), Level::Allow),
        (String::from("b"), Level::Warn),
        (String::from("c"), Level::Deny),
        (String::from("d"), Level::Forbid),
    ];

    v2.lint_opts = vec![
        (String::from("a"), Level::Allow),
        (String::from("c"), Level::Deny),
        (String::from("b"), Level::Warn),
        (String::from("d"), Level::Forbid),
    ];

    // The hash should be order-dependent
    assert_non_crate_hash_different(&v1, &v2);
}

#[test]
fn test_lint_cap_hash_different() {
    let mut v1 = Options::default();
    let mut v2 = Options::default();
    let v3 = Options::default();

    v1.lint_cap = Some(Level::Forbid);
    v2.lint_cap = Some(Level::Allow);

    assert_non_crate_hash_different(&v1, &v2);
    assert_non_crate_hash_different(&v1, &v3);
    assert_non_crate_hash_different(&v2, &v3);
}

#[test]
fn test_search_paths_tracking_hash_different_order() {
    let mut v1 = Options::default();
    let mut v2 = Options::default();
    let mut v3 = Options::default();
    let mut v4 = Options::default();

    let early_dcx = EarlyDiagCtxt::new(JSON);
    const JSON: ErrorOutputType = ErrorOutputType::Json {
        pretty: false,
        json_rendered: HumanReadableErrorType { short: false, unicode: false },
        color_config: ColorConfig::Never,
    };

    let push = |opts: &mut Options, search_path| {
        opts.search_paths.push(SearchPath::from_cli_opt(
            "not-a-sysroot".as_ref(),
            &opts.target_triple,
            &early_dcx,
            search_path,
            false,
        ));
    };

    // Reference
    push(&mut v1, "native=abc");
    push(&mut v1, "crate=def");
    push(&mut v1, "dependency=ghi");
    push(&mut v1, "framework=jkl");
    push(&mut v1, "all=mno");

    push(&mut v2, "native=abc");
    push(&mut v2, "dependency=ghi");
    push(&mut v2, "crate=def");
    push(&mut v2, "framework=jkl");
    push(&mut v2, "all=mno");

    push(&mut v3, "crate=def");
    push(&mut v3, "framework=jkl");
    push(&mut v3, "native=abc");
    push(&mut v3, "dependency=ghi");
    push(&mut v3, "all=mno");

    push(&mut v4, "all=mno");
    push(&mut v4, "native=abc");
    push(&mut v4, "crate=def");
    push(&mut v4, "dependency=ghi");
    push(&mut v4, "framework=jkl");

    assert_same_hash(&v1, &v2);
    assert_same_hash(&v1, &v3);
    assert_same_hash(&v1, &v4);
}

#[test]
fn test_native_libs_tracking_hash_different_values() {
    let mut v1 = Options::default();
    let mut v2 = Options::default();
    let mut v3 = Options::default();
    let mut v4 = Options::default();
    let mut v5 = Options::default();

    // Reference
    v1.libs = vec![
        NativeLib {
            name: String::from("a"),
            new_name: None,
            kind: NativeLibKind::Static { bundle: None, whole_archive: None, export_symbols: None },
            verbatim: None,
        },
        NativeLib {
            name: String::from("b"),
            new_name: None,
            kind: NativeLibKind::Framework { as_needed: None },
            verbatim: None,
        },
        NativeLib {
            name: String::from("c"),
            new_name: None,
            kind: NativeLibKind::Unspecified,
            verbatim: None,
        },
    ];

    // Change label
    v2.libs = vec![
        NativeLib {
            name: String::from("a"),
            new_name: None,
            kind: NativeLibKind::Static { bundle: None, whole_archive: None, export_symbols: None },
            verbatim: None,
        },
        NativeLib {
            name: String::from("X"),
            new_name: None,
            kind: NativeLibKind::Framework { as_needed: None },
            verbatim: None,
        },
        NativeLib {
            name: String::from("c"),
            new_name: None,
            kind: NativeLibKind::Unspecified,
            verbatim: None,
        },
    ];

    // Change kind
    v3.libs = vec![
        NativeLib {
            name: String::from("a"),
            new_name: None,
            kind: NativeLibKind::Static { bundle: None, whole_archive: None, export_symbols: None },
            verbatim: None,
        },
        NativeLib {
            name: String::from("b"),
            new_name: None,
            kind: NativeLibKind::Static { bundle: None, whole_archive: None, export_symbols: None },
            verbatim: None,
        },
        NativeLib {
            name: String::from("c"),
            new_name: None,
            kind: NativeLibKind::Unspecified,
            verbatim: None,
        },
    ];

    // Change new-name
    v4.libs = vec![
        NativeLib {
            name: String::from("a"),
            new_name: None,
            kind: NativeLibKind::Static { bundle: None, whole_archive: None, export_symbols: None },
            verbatim: None,
        },
        NativeLib {
            name: String::from("b"),
            new_name: Some(String::from("X")),
            kind: NativeLibKind::Framework { as_needed: None },
            verbatim: None,
        },
        NativeLib {
            name: String::from("c"),
            new_name: None,
            kind: NativeLibKind::Unspecified,
            verbatim: None,
        },
    ];

    // Change verbatim
    v5.libs = vec![
        NativeLib {
            name: String::from("a"),
            new_name: None,
            kind: NativeLibKind::Static { bundle: None, whole_archive: None, export_symbols: None },
            verbatim: None,
        },
        NativeLib {
            name: String::from("b"),
            new_name: None,
            kind: NativeLibKind::Framework { as_needed: None },
            verbatim: Some(true),
        },
        NativeLib {
            name: String::from("c"),
            new_name: None,
            kind: NativeLibKind::Unspecified,
            verbatim: None,
        },
    ];

    assert_different_hash(&v1, &v2);
    assert_different_hash(&v1, &v3);
    assert_different_hash(&v1, &v4);
    assert_different_hash(&v1, &v5);
}

#[test]
fn test_native_libs_tracking_hash_different_order() {
    let mut v1 = Options::default();
    let mut v2 = Options::default();
    let mut v3 = Options::default();

    // Reference
    v1.libs = vec![
        NativeLib {
            name: String::from("a"),
            new_name: None,
            kind: NativeLibKind::Static { bundle: None, whole_archive: None, export_symbols: None },
            verbatim: None,
        },
        NativeLib {
            name: String::from("b"),
            new_name: None,
            kind: NativeLibKind::Framework { as_needed: None },
            verbatim: None,
        },
        NativeLib {
            name: String::from("c"),
            new_name: None,
            kind: NativeLibKind::Unspecified,
            verbatim: None,
        },
    ];

    v2.libs = vec![
        NativeLib {
            name: String::from("b"),
            new_name: None,
            kind: NativeLibKind::Framework { as_needed: None },
            verbatim: None,
        },
        NativeLib {
            name: String::from("a"),
            new_name: None,
            kind: NativeLibKind::Static { bundle: None, whole_archive: None, export_symbols: None },
            verbatim: None,
        },
        NativeLib {
            name: String::from("c"),
            new_name: None,
            kind: NativeLibKind::Unspecified,
            verbatim: None,
        },
    ];

    v3.libs = vec![
        NativeLib {
            name: String::from("c"),
            new_name: None,
            kind: NativeLibKind::Unspecified,
            verbatim: None,
        },
        NativeLib {
            name: String::from("a"),
            new_name: None,
            kind: NativeLibKind::Static { bundle: None, whole_archive: None, export_symbols: None },
            verbatim: None,
        },
        NativeLib {
            name: String::from("b"),
            new_name: None,
            kind: NativeLibKind::Framework { as_needed: None },
            verbatim: None,
        },
    ];

    // The hash should be order-dependent
    assert_different_hash(&v1, &v2);
    assert_different_hash(&v1, &v3);
    assert_different_hash(&v2, &v3);
}

#[test]
fn test_codegen_options_tracking_hash() {
    let reference = Options::default();
    let mut opts = Options::default();

    macro_rules! untracked {
        ($name: ident, $non_default_value: expr) => {
            assert_ne!(opts.cg.$name, $non_default_value);
            opts.cg.$name = $non_default_value;
            assert_same_hash(&reference, &opts);
        };
    }

    // Make sure that changing an [UNTRACKED] option leaves the hash unchanged.
    // tidy-alphabetical-start
    untracked!(codegen_units, Some(42));
    untracked!(default_linker_libraries, true);
    untracked!(dlltool, Some(PathBuf::from("custom_dlltool.exe")));
    untracked!(extra_filename, String::from("extra-filename"));
    untracked!(incremental, Some(String::from("abc")));
    // `link_arg` is omitted because it just forwards to `link_args`.
    untracked!(link_args, vec![String::from("abc"), String::from("def")]);
    untracked!(link_self_contained, LinkSelfContained::on());
    untracked!(linker, Some(PathBuf::from("linker")));
    untracked!(linker_flavor, Some(LinkerFlavorCli::Gcc));
    untracked!(remark, Passes::Some(vec![String::from("pass1"), String::from("pass2")]));
    untracked!(rpath, true);
    untracked!(save_temps, true);
    untracked!(strip, Strip::Debuginfo);
    // tidy-alphabetical-end

    macro_rules! tracked {
        ($name: ident, $non_default_value: expr) => {
            opts = reference.clone();
            assert_ne!(opts.cg.$name, $non_default_value);
            opts.cg.$name = $non_default_value;
            assert_different_hash(&reference, &opts);
        };
    }

    // Make sure that changing a [TRACKED] option changes the hash.
    // tidy-alphabetical-start
    tracked!(code_model, Some(CodeModel::Large));
    tracked!(collapse_macro_debuginfo, CollapseMacroDebuginfo::Yes);
    tracked!(control_flow_guard, CFGuard::Checks);
    tracked!(debug_assertions, Some(true));
    tracked!(debuginfo, DebugInfo::Limited);
    tracked!(dwarf_version, Some(5));
    tracked!(embed_bitcode, false);
    tracked!(force_frame_pointers, FramePointer::Always);
    tracked!(force_unwind_tables, Some(true));
    tracked!(instrument_coverage, InstrumentCoverage::Yes);
    tracked!(jump_tables, false);
    tracked!(link_dead_code, Some(true));
    tracked!(linker_plugin_lto, LinkerPluginLto::LinkerPluginAuto);
    tracked!(llvm_args, vec![String::from("1"), String::from("2")]);
    tracked!(lto, LtoCli::Fat);
    tracked!(metadata, vec![String::from("A"), String::from("B")]);
    tracked!(no_prepopulate_passes, true);
    tracked!(no_redzone, Some(true));
    tracked!(no_vectorize_loops, true);
    tracked!(no_vectorize_slp, true);
    tracked!(opt_level, "3".to_string());
    tracked!(overflow_checks, Some(true));
    tracked!(panic, Some(PanicStrategy::Abort));
    tracked!(passes, vec![String::from("1"), String::from("2")]);
    tracked!(prefer_dynamic, true);
    tracked!(profile_generate, SwitchWithOptPath::Enabled(None));
    tracked!(profile_use, Some(PathBuf::from("abc")));
    tracked!(relocation_model, Some(RelocModel::Pic));
    tracked!(relro_level, Some(RelroLevel::Full));
    tracked!(split_debuginfo, Some(SplitDebuginfo::Packed));
    tracked!(symbol_mangling_version, Some(SymbolManglingVersion::V0));
    tracked!(target_cpu, Some(String::from("abc")));
    tracked!(target_feature, String::from("all the features, all of them"));
    // tidy-alphabetical-end
}

#[test]
fn test_top_level_options_tracked_no_crate() {
    let reference = Options::default();
    let mut opts;

    macro_rules! tracked {
        ($name: ident, $non_default_value: expr) => {
            opts = reference.clone();
            assert_ne!(opts.$name, $non_default_value);
            opts.$name = $non_default_value;
            // The crate hash should be the same
            assert_eq!(reference.dep_tracking_hash(true), opts.dep_tracking_hash(true));
            // The incremental hash should be different
            assert_ne!(reference.dep_tracking_hash(false), opts.dep_tracking_hash(false));
        };
    }

    // Make sure that changing a [TRACKED_NO_CRATE_HASH] option leaves the crate hash unchanged but changes the incremental hash.
    // tidy-alphabetical-start
    tracked!(
        real_rust_source_base_dir,
        Some("/home/bors/rust/.rustup/toolchains/nightly/lib/rustlib/src/rust".into())
    );
    tracked!(remap_path_prefix, vec![("/home/bors/rust".into(), "src".into())]);
    // tidy-alphabetical-end
}

#[test]
fn test_unstable_options_tracking_hash() {
    let reference = Options::default();
    let mut opts = Options::default();

    macro_rules! untracked {
        ($name: ident, $non_default_value: expr) => {
            assert_ne!(opts.unstable_opts.$name, $non_default_value);
            opts.unstable_opts.$name = $non_default_value;
            assert_same_hash(&reference, &opts);
        };
    }

    // Make sure that changing an [UNTRACKED] option leaves the hash unchanged.
    // tidy-alphabetical-start
    untracked!(assert_incr_state, Some(IncrementalStateAssertion::Loaded));
    untracked!(codegen_source_order, true);
    untracked!(deduplicate_diagnostics, false);
    untracked!(dump_dep_graph, true);
    untracked!(dump_mir, Some(String::from("abc")));
    untracked!(dump_mir_dataflow, true);
    untracked!(dump_mir_dir, String::from("abc"));
    untracked!(dump_mir_exclude_alloc_bytes, true);
    untracked!(dump_mir_exclude_pass_number, true);
    untracked!(dump_mir_graphviz, true);
    untracked!(dump_mono_stats, SwitchWithOptPath::Enabled(Some("mono-items-dir/".into())));
    untracked!(dump_mono_stats_format, DumpMonoStatsFormat::Json);
    untracked!(dylib_lto, true);
    untracked!(emit_stack_sizes, true);
    untracked!(future_incompat_test, true);
    untracked!(identify_regions, true);
    untracked!(incremental_info, true);
    untracked!(incremental_verify_ich, true);
    untracked!(input_stats, true);
    untracked!(link_native_libraries, false);
    untracked!(llvm_time_trace, true);
    untracked!(ls, vec!["all".to_owned()]);
    untracked!(macro_backtrace, true);
    untracked!(macro_stats, true);
    untracked!(meta_stats, true);
    untracked!(mir_include_spans, MirIncludeSpans::On);
    untracked!(nll_facts, true);
    untracked!(no_analysis, true);
    untracked!(no_leak_check, true);
    untracked!(no_parallel_backend, true);
    untracked!(no_steal_thir, true);
    untracked!(parse_crate_root_only, true);
    // `pre_link_arg` is omitted because it just forwards to `pre_link_args`.
    untracked!(pre_link_args, vec![String::from("abc"), String::from("def")]);
    untracked!(print_codegen_stats, true);
    untracked!(print_llvm_passes, true);
    untracked!(print_mono_items, true);
    untracked!(print_type_sizes, true);
    untracked!(proc_macro_backtrace, true);
    untracked!(proc_macro_execution_strategy, ProcMacroExecutionStrategy::CrossThread);
    untracked!(profile_closures, true);
    untracked!(query_dep_graph, true);
    untracked!(self_profile, SwitchWithOptPath::Enabled(None));
    untracked!(self_profile_events, Some(vec![String::new()]));
    untracked!(shell_argfiles, true);
    untracked!(span_debug, true);
    untracked!(span_free_formats, true);
    untracked!(temps_dir, Some(String::from("abc")));
    untracked!(threads, Some(99));
    untracked!(time_llvm_passes, true);
    untracked!(time_passes, true);
    untracked!(time_passes_format, TimePassesFormat::Json);
    untracked!(trace_macros, true);
    untracked!(track_diagnostics, true);
    untracked!(trim_diagnostic_paths, false);
    untracked!(trust_proof_artifact_root, Some(PathBuf::from("/tmp/trust-proof-root")));
    untracked!(trust_verify_ay_path, Some(PathBuf::from("/tmp/ay")));
    untracked!(trust_witness, TrustWitness::Off);
    untracked!(trust_witness_precise, true);
    untracked!(ui_testing, true);
    untracked!(unpretty, Some("expanded".to_string()));
    untracked!(unstable_options, true);
    untracked!(validate_mir, true);
    untracked!(write_long_types_to_disk, false);
    // tidy-alphabetical-end

    macro_rules! tracked {
        ($name: ident, $non_default_value: expr) => {
            opts = reference.clone();
            assert_ne!(opts.unstable_opts.$name, $non_default_value);
            opts.unstable_opts.$name = $non_default_value;
            assert_different_hash(&reference, &opts);
        };
    }

    // Make sure that changing a [TRACKED] option changes the hash.
    // tidy-alphabetical-start
    tracked!(allow_features, Some(vec![String::from("lang_items")]));
    tracked!(always_encode_mir, true);
    tracked!(annotate_moves, AnnotateMoves::Enabled(Some(1234)));
    tracked!(assume_incomplete_release, true);
    tracked!(autodiff, vec![AutoDiff::Enable, AutoDiff::NoTT]);
    tracked!(autodiff_post_passes, Some("function(mem2reg,instsimplify,simplifycfg)".to_string()));
    tracked!(binary_dep_depinfo, true);
    tracked!(box_noalias, false);
    tracked!(
        branch_protection,
        Some(BranchProtection {
            bti: true,
            pac_ret: Some(PacRet { leaf: true, pc: true, key: PAuthKey::B }),
            gcs: true,
        })
    );
    tracked!(codegen_backend, Some("abc".to_string()));
    tracked!(codegen_emit_retag, Some(CodegenRetagOptions::default()));
    tracked!(
        coverage_options,
        CoverageOptions {
            level: CoverageLevel::Branch,
            // (don't collapse test-only options onto the same line)
            discard_all_spans_in_codegen: true,
        }
    );
    tracked!(crate_attr, vec!["abc".to_string()]);
    tracked!(cross_crate_inline_threshold, InliningThreshold::Always);
    tracked!(debug_info_type_line_numbers, true);
    tracked!(debuginfo_for_profiling, true);
    tracked!(default_visibility, Some(rustc_target::spec::SymbolVisibility::Hidden));
    tracked!(dep_info_omit_d_target, true);
    tracked!(direct_access_external_data, Some(true));
    tracked!(dual_proc_macros, true);
    tracked!(dwarf_version, Some(5));
    tracked!(embed_metadata, false);
    tracked!(embed_source, true);
    tracked!(export_executable_symbols, true);
    tracked!(fewer_names, Some(true));
    tracked!(fixed_x18, true);
    tracked!(flatten_format_args, false);
    tracked!(fmt_debug, FmtDebug::Shallow);
    tracked!(force_unstable_if_unmarked, true);
    tracked!(function_return, FunctionReturn::ThunkExtern);
    tracked!(function_sections, Some(false));
    tracked!(hint_mostly_unused, true);
    tracked!(human_readable_cgu_names, true);
    tracked!(incremental_ignore_spans, true);
    tracked!(indirect_branch_cs_prefix, true);
    tracked!(inline_mir, Some(true));
    tracked!(inline_mir_hint_threshold, Some(123));
    tracked!(inline_mir_threshold, Some(123));
    tracked!(instrument_mcount, InstrumentMcount::Mcount);
    tracked!(instrument_xray, Some(InstrumentXRay::default()));
    tracked!(link_directives, false);
    tracked!(link_only, true);
    tracked!(lint_llvm_ir, true);
    tracked!(llvm_module_flag, vec![("bar".to_string(), 123, "max".to_string())]);
    tracked!(llvm_plugins, vec![String::from("plugin_name")]);
    tracked!(llvm_writable, true);
    tracked!(location_detail, LocationDetail { file: true, line: false, column: false });
    tracked!(maximal_hir_to_mir_coverage, true);
    tracked!(merge_functions, Some(MergeFunctions::Disabled));
    tracked!(min_function_alignment, Some(Align::EIGHT));
    tracked!(min_recursion_limit, Some(256));
    tracked!(mir_enable_passes, vec![("DestProp".to_string(), false)]);
    tracked!(mir_opt_level, Some(4));
    tracked!(mir_preserve_ub, true);
    tracked!(move_size_limit, Some(4096));
    tracked!(mutable_noalias, false);
    tracked!(next_solver, NextSolverConfig { coherence: true, globally: true });
    tracked!(no_generate_arange_section, true);
    tracked!(no_link, true);
    tracked!(no_profiler_runtime, true);
    tracked!(no_trait_vptr, true);

    tracked!(no_unique_section_names, true);
    tracked!(offload, vec![Offload::Device]);
    tracked!(on_broken_pipe, OnBrokenPipe::Kill);
    tracked!(osx_rpath_install_name, true);
    tracked!(packed_bundled_libs, true);
    tracked!(panic_abort_tests, true);
    tracked!(panic_in_drop, PanicStrategy::Abort);
    tracked!(
        patchable_function_entry,
        PatchableFunctionEntry::from_parts(10, 5, None)
            .expect("total must be greater than or equal to prefix")
    );
    tracked!(plt, Some(true));
    tracked!(polonius, Polonius::Legacy);
    tracked!(precise_enum_drop_elaboration, false);
    tracked!(profile_sample_use, Some(PathBuf::from("abc")));
    tracked!(profiler_runtime, "abc".to_string());
    tracked!(reg_struct_return, true);
    tracked!(regparm, Some(3));
    tracked!(relax_elf_relocations, Some(true));
    tracked!(remap_cwd_prefix, Some(PathBuf::from("abc")));
    tracked!(sanitizer, SanitizerSet::ADDRESS);
    tracked!(sanitizer_cfi_canonical_jump_tables, None);
    tracked!(sanitizer_cfi_generalize_pointers, Some(true));
    tracked!(sanitizer_cfi_normalize_integers, Some(true));
    tracked!(sanitizer_dataflow_abilist, vec![String::from("/rustc/abc")]);
    tracked!(sanitizer_kcfi_arity, Some(true));
    tracked!(sanitizer_memory_track_origins, 2);
    tracked!(sanitizer_recover, SanitizerSet::ADDRESS);
    tracked!(saturating_float_casts, Some(true));
    tracked!(share_generics, Some(true));
    tracked!(simulate_remapped_rust_src_base, Some(PathBuf::from("/rustc/abc")));
    tracked!(small_data_threshold, Some(16));
    tracked!(split_lto_unit, Some(true));
    tracked!(src_hash_algorithm, Some(SourceFileHashAlgorithm::Sha1));
    tracked!(stack_protector, StackProtector::All);
    tracked!(staticlib_hide_internal_symbols, true);
    tracked!(staticlib_rename_internal_symbols, true);
    tracked!(teach, true);
    tracked!(thinlto, Some(true));
    tracked!(tiny_const_eval_limit, true);
    tracked!(tls_model, Some(TlsModel::GeneralDynamic));
    tracked!(translate_remapped_path_to_local_path, false);
    tracked!(trap_unreachable, Some(false));
    tracked!(treat_err_as_bug, NonZero::new(1));
    tracked!(trust_certified_test_monitors, true);
    tracked!(trust_cg_output_gate, "allow-unknown".to_string());
    tracked!(trust_ir_flip, false);
    tracked!(trust_ir_lower, Some(TrustIrLower::On));
    tracked!(trust_no_r1, true);
    tracked!(trust_policy, TrustPolicy::Advisory);
    tracked!(trust_targo_test_monitor, true);
    tracked!(trust_verify, TrustVerify::Off);
    tracked!(trust_verify_crate_role, "dependency".to_string());
    tracked!(trust_verify_function_budget_ms, 1);

    tracked!(trust_verify_include_dependencies, true);
    tracked!(trust_verify_level, 1);
    tracked!(trust_verify_profile, Some("hardened".to_string()));
    tracked!(trust_verify_timeout_ms, 1);
    tracked!(trust_verify_worker_threads, 2);
    tracked!(tune_cpu, Some(String::from("abc")));
    tracked!(ub_checks, Some(false));
    tracked!(uninit_const_chunk_threshold, 123);
    tracked!(unleash_the_miri_inside_of_you, true);
    tracked!(use_ctors_section, Some(true));
    tracked!(verbose_asm, true);
    tracked!(verify_llvm_ir, true);
    tracked!(virtual_function_elimination, true);
    tracked!(wasi_exec_model, Some(WasiExecModel::Reactor));
    // tidy-alphabetical-end

    macro_rules! tracked_no_crate_hash {
        ($name: ident, $non_default_value: expr) => {
            opts = reference.clone();
            assert_ne!(opts.unstable_opts.$name, $non_default_value);
            opts.unstable_opts.$name = $non_default_value;
            assert_non_crate_hash_different(&reference, &opts);
        };
    }
    tracked_no_crate_hash!(no_codegen, true);
    tracked_no_crate_hash!(
        trust_dump,
        rustc_session::config::TrustDump {
            mir: Some(PathBuf::from("/tmp/trust-mir")),
            mir_only: true,
            native_bundle: Some(PathBuf::from("/tmp/trust-native")),
            ir: Some(PathBuf::from("/tmp/trust-ir")),
        }
    );

    tracked_no_crate_hash!(trust_verify_output, "json".to_string());
    tracked_no_crate_hash!(trust_verify_package_name, Some("example-package".to_string()));
    tracked_no_crate_hash!(trust_verify_session, Some("proof-session-1".to_string()));
    tracked_no_crate_hash!(verbose_internals, true);
}

#[test]
fn test_edition_parsing() {
    // test default edition
    let options = Options::default();
    assert!(options.edition == DEFAULT_EDITION);

    let mut early_dcx = EarlyDiagCtxt::new(ErrorOutputType::default());

    let matches = optgroups().parse(&["--edition=2018".to_string()]).unwrap();
    let sessopts = build_session_options(&mut early_dcx, &matches);
    assert!(sessopts.edition == Edition::Edition2018)
}

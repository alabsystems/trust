// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Real std atomic calls through compiler-owned extraction and public lowering.
//! One closed sequential ByteV1 replay consumes the untouched lowered U64 module.
//! This does not prove Rust/MIR refinement or concurrency; obligations stay pending.

#![feature(rustc_private)]
// Trust (CUSTODY-EMBEDDED-TEST-LOAN-1): these tests run the compiler in process;
// their binary captures its scheduler at native entry (tests/support/native_test_entry.rs).
#![cfg_attr(
    any(target_os = "linux", target_os = "macos"),
    feature(test, custom_test_frameworks, exitcode_exit_method)
)]
#![cfg_attr(any(target_os = "linux", target_os = "macos"), test_runner(native_test_entry::main))]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

use std::io;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use rustc_driver::Compilation;
use rustc_interface::interface::{Compiler, Config};
use rustc_middle::ty::{self, TyCtxt};
use trust_ir::inst::{AtomicRMWOp, CastOp, Ordering};
use trust_ir::{
    BlockId, CallingConv, Constant, Endianness, FieldDef, FuncId, FuncTy, FuncTyId, Inst, Linkage,
    Module, ObligationKind, ObligationSite, Producer, ProofStatus, StructDef, StructId,
    StructPassingPolicy, StructRepr, Ty, ValueId, Visibility,
};
use trust_ir_bridge::{lower_compiler_relaxed_xadd_u64_body, lower_to_trust_ir};
use trust_mir_extract::atomic_callsite::{
    AtomicCallsiteError, AtomicXaddIntegerType, capture_relaxed_xadd_u64_body,
};
use trust_types::{ConstValue, Operand, Terminator};

#[path = "compiler_atomic_bridge/replay.rs"]
mod replay;

const FIXTURE_PATH: &str = "compiler_atomic_bridge_fixture.rs";
const FIXTURE_SOURCE: &str = r#"
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
pub fn relaxed_u64(counter: &AtomicU64) -> u64 {
    counter.fetch_add(7, Ordering::Relaxed)
}
pub fn relaxed_usize(counter: &AtomicUsize) -> usize {
    counter.fetch_add(11, Ordering::Relaxed)
}
pub fn seqcst(counter: &AtomicU64) -> u64 {
    counter.fetch_add(13, Ordering::SeqCst)
}
"#;

struct FixtureFileLoader;

impl rustc_span::source_map::FileLoader for FixtureFileLoader {
    fn file_exists(&self, path: &Path) -> bool {
        path == Path::new(FIXTURE_PATH)
    }

    fn read_file(&self, path: &Path) -> io::Result<String> {
        if self.file_exists(path) {
            Ok(FIXTURE_SOURCE.into())
        } else {
            Err(io::Error::other("unexpected compiler atomic bridge fixture path"))
        }
    }

    fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
        Err(io::Error::other("binary source reads are unsupported for this fixture"))
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

// This integration target cannot call the library's private cfg(test) helper.
// Use the same explicit Trust sysroot overrides and reject a proven driver
// version mismatch before rustc tries to load incompatible core/std metadata.
fn compiler_sysroot() -> String {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().parent().unwrap();
    // Bootstrap exports RUSTC_SYSROOT (and a tool build SYSROOT) for the compiler
    // BUILD, i.e. `stage0-sysroot` while this stage 1 test embeds a newer rustc_driver, and
    // the version check below cannot tell them apart (both print `1.99.0-dev`). So the
    // ambient values come LAST, after the local stage sysroots, as in the library's own
    // `compiler_sysroot`; TRUST_TEST_SYSROOT and TEST_SYSROOT stay explicit overrides.
    let env_sysroot = |key: &str| std::env::var_os(key).map(PathBuf::from);
    let mut candidates = ["TRUST_TEST_SYSROOT", "TEST_SYSROOT"]
        .into_iter()
        .filter_map(env_sysroot)
        .collect::<Vec<_>>();
    for host in
        ["host", "aarch64-apple-darwin", "aarch64-unknown-linux-gnu", "x86_64-unknown-linux-gnu"]
    {
        for stage in ["stage2", "stage1"] {
            candidates.push(root.join("build").join(host).join(stage));
        }
    }
    candidates.extend(["RUSTC_SYSROOT", "SYSROOT"].into_iter().filter_map(env_sysroot));
    for candidate in candidates {
        let compiler = candidate.join("bin/trustc");
        if !compiler.is_file() {
            continue;
        }
        let has_std = candidate.join("lib/rustlib").read_dir().is_ok_and(|entries| {
            entries.flatten().any(|entry| {
                let names = entry
                    .path()
                    .join("lib")
                    .read_dir()
                    .map(|files| {
                        files
                            .flatten()
                            .map(|file| file.file_name().to_string_lossy().into_owned())
                            .collect::<Vec<_>>()
                    })
                    .unwrap_or_default();
                ["libcore-", "libstd-"].iter().all(|prefix| {
                    names.iter().any(|name| name.starts_with(prefix) && name.ends_with(".rmeta"))
                })
            })
        });
        if !has_std {
            continue;
        }
        if let Some(version) = rustc_interface::util::rustc_version_str() {
            let output = std::process::Command::new(compiler)
                .arg("--version")
                .output()
                .expect("query selected compiler identity");
            if !output.status.success()
                || !String::from_utf8_lossy(&output.stdout).contains(version.trim())
            {
                continue;
            }
        }
        return candidate
            .canonicalize()
            .expect("canonical compiler sysroot")
            .to_string_lossy()
            .into_owned();
    }
    panic!(
        "set TRUST_TEST_SYSROOT to the Trust sysroot matching this embedded rustc_driver (bin/trustc and host core/std metadata required)"
    );
}

fn refuses_public_model(function: &trust_types::VerifiableFunction) {
    let error = lower_to_trust_ir(function).expect_err("public metadata has no compiler authority");
    assert!(
        error.to_string().contains("compiler-authenticated operation and ordering evidence"),
        "unexpected refusal: {error}"
    );
}

/// Regression census measured from the real compiler fixture, not an admission
/// rule. Exact SSA numbering is deliberate: drift requires inspecting a new
/// complete diagnostic capture, never silently normalizing the emitted module.
fn measured_module_census(
    module: &Module,
    expected_name: &str,
    integer: Ty,
    increment: i128,
    llvm_triple: &str,
    source_span: &trust_types::SourceSpan,
) -> Result<(), &'static str> {
    macro_rules! require {
        ($condition:expr) => {
            if !$condition {
                return Err(stringify!($condition));
            }
        };
    }
    // No `..`: a newly added module field must receive an explicit census rule.
    let Module {
        name,
        functions,
        structs,
        enums,
        records,
        closure_types,
        globals,
        func_types,
        types,
        proof_obligations,
        proof_certificates,
        target_info,
        files,
        obligation_diagnostics,
        spec_modules,
        universes,
        predicates,
        global_asm,
        imports,
        tuple_layouts,
        completeness,
        drop_glue,
        closure_layouts,
        blobs,
    } = module;
    require!(name == expected_name);
    require!(enums.is_empty() && records.is_empty() && closure_types.is_empty());
    require!(globals.is_empty() && global_asm.is_empty() && imports.is_empty());
    require!(spec_modules.is_empty() && universes.is_empty() && predicates.is_empty());
    require!(tuple_layouts.is_empty() && obligation_diagnostics.is_empty());
    require!(proof_certificates.is_empty());
    require!(completeness.is_none());
    // trust-ir v55: the atomic bridge drops nothing, so it registers no glue.
    require!(drop_glue.is_empty());
    // trust-ir v58: the atomic bridge builds no closure, so it declares no closure frame.
    require!(closure_layouts.is_empty());
    // trust-ir v70: the atomic bridge reads no tensor weight, so it carries no blob table.
    require!(blobs.is_empty());
    require!(types == &[Ty::U8]);
    require!(files == &[source_span.file.clone()]);
    require!(
        target_info.as_ref()
            == Some(&trust_ir::TargetInfo {
                triple: llvm_triple.to_owned(),
                pointer_size: 8,
                endianness: Endianness::Little,
                abi: None,
                struct_passing: StructPassingPolicy::Unclassified,
            })
    );
    require!(
        func_types
            == &[FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![integer.clone()],
                is_vararg: false,
                abi: None,
            }]
    );
    let expected_structs = [
        ("core::sync::atomic::private::Align8", "0", integer.clone(), StructRepr::C),
        ("core::cell::UnsafeCell", "value", Ty::Struct(StructId::new(0)), StructRepr::Transparent),
        ("core::sync::atomic::Atomic", "v", Ty::Struct(StructId::new(1)), StructRepr::C),
    ];
    require!(structs.len() == expected_structs.len());
    for (id, (actual, (name, field, ty, repr))) in structs.iter().zip(expected_structs).enumerate()
    {
        require!(
            actual
                == &StructDef {
                    id: StructId::new(id as u32),
                    name: name.into(),
                    fields: vec![FieldDef { name: field.into(), ty, offset: Some(0) }],
                    size: Some(8),
                    align: Some(8),
                    repr,
                    origin: None,
                }
        );
    }
    let [function] = functions.as_slice() else { return Err("one function, no declarations") };
    let trust_ir::Function {
        id,
        name,
        ty,
        entry,
        blocks,
        proofs,
        calling_conv,
        linkage,
        attrs,
        summary,
        producer,
        value_names,
        scopes,
        source_provenance,
        body_gate,
        display_path,
        section,
        visibility,
        retained,
    } = function;
    require!(*id == FuncId::new(0) && name == expected_name && *ty == FuncTyId::new(0));
    require!(*entry == BlockId::new(0));
    require!(proofs.is_empty());
    require!(*calling_conv == CallingConv::C && *linkage == Linkage::External);
    require!(*attrs == trust_ir::FuncAttrs::default());
    require!(summary.is_none() && source_provenance.is_none() && body_gate.is_none());
    require!(*producer == Some(Producer::TrustIr));
    require!(value_names.is_none() && scopes.is_none() && display_path.is_none());
    require!(section.is_none() && *visibility == Visibility::Default && !retained);
    let [first, last] = blocks.as_slice() else { return Err("exactly two emitted blocks") };
    require!(first.id == BlockId::new(0) && last.id == BlockId::new(1));
    require!(first.params == [(ValueId::new(0), Ty::Ptr)] && last.params.is_empty());
    let v = ValueId::new;
    let expected = [
        (Inst::Const { ty: Ty::I64, value: Constant::Int(0) }, vec![v(4)]),
        (
            Inst::GEP {
                pointee_ty: Ty::Struct(StructId::new(1)),
                base: v(0),
                indices: vec![v(4)],
                inbounds: false,
            },
            vec![v(5)],
        ),
        (Inst::Copy { ty: Ty::Ptr, operand: v(5) }, vec![v(6)]),
        (
            Inst::Cast { op: CastOp::Bitcast, src_ty: Ty::Ptr, dst_ty: Ty::Ptr, operand: v(6) },
            vec![v(7)],
        ),
        (Inst::Const { ty: integer.clone(), value: Constant::Int(increment) }, vec![v(8)]),
        (
            Inst::AtomicRMW {
                op: AtomicRMWOp::Add,
                ty: integer.clone(),
                ptr: v(7),
                value: v(8),
                ordering: Ordering::Relaxed,
            },
            vec![v(9)],
        ),
        (Inst::Br { target: BlockId::new(1), args: vec![] }, vec![]),
        (Inst::Return { values: vec![v(9)] }, vec![]),
    ];
    require!(first.body.len() == 7 && last.body.len() == 1);
    for (node, (inst, results)) in blocks.iter().flat_map(|block| &block.body).zip(expected) {
        let trust_ir::InstrNode {
            inst: actual,
            results: actual_results,
            proofs,
            span,
            proof_context,
            scope,
        } = node;
        require!(*actual == inst && *actual_results == results);
        require!(proofs.is_empty() && proof_context.is_none());
        require!(span.is_none() && scope.is_none());
    }
    // Count the WHOLE table, not only rows matching an atomic description.
    require!(proof_obligations.len() == 2);
    for (index, (obligation, kind)) in proof_obligations
        .iter()
        .zip([ObligationKind::MemorySafety, ObligationKind::Ownership])
        .enumerate()
    {
        let trust_ir::ProofObligation {
            id: obligation_id,
            kind: actual_kind,
            status,
            description,
            formula,
            function: owner,
            source,
            site,
            spec,
        } = obligation;
        require!(obligation_id.index() == index as u32);
        require!(*actual_kind == kind && *status == ProofStatus::Pending);
        require!(spec.is_none());
        require!(*owner == Some(*id));
        require!(*site == Some(ObligationSite::new(*id, first.id, 5)));
        let (class, requirement) = if index == 0 {
            ("memory", "a live, initialized, writable, 8-byte-aligned u64 allocation")
        } else {
            (
                "ownership",
                "compatible atomic accesses and an explicit concurrent or exclusive sequential memory invariant",
            )
        };
        let width = if integer == Ty::U64 { "u64" } else { "usize" };
        require!(
            *description
                == format!(
                    "compiler-authenticated relaxed xadd `core::intrinsics::atomic_xadd::<{width}, {width}, core::intrinsics::AtomicOrdering::Relaxed>` still requires {requirement}"
                )
        );
        let source_id = format!(
            "mir-atomic:{class}:compiler_atomic_bridge_fixture::{expected_name}:bb0:terminator"
        );
        let assertion_id = format!("trust-assertion:{source_id}");
        require!(
            source.as_ref()
                == Some(&trust_ir::ProofObligationSourceIdentity {
                    source_id: source_id.clone(),
                    assertion_id: assertion_id.clone(),
                    public: None,
                    range: Some(trust_ir::ProofObligationSourceRange {
                        file: 0,
                        start_line: source_span.line_start,
                        start_col: source_span.col_start,
                        end_line: source_span.line_end,
                        end_col: source_span.col_end,
                    }),
                })
        );
        let Some(trust_ir::ProofFormula { schema, payload, smtlib, sort, bindings }) = formula
        else {
            return Err("source-only obligation formula");
        };
        require!(schema == trust_ir_bridge::TRUST_OBLIGATION_SOURCE_SCHEMA);
        require!(smtlib.is_none() && sort.is_none() && bindings.is_empty());
        // JSON is inspected as diagnostic metadata, never deserialized as authority.
        require!(
            serde_json::from_str::<serde_json::Value>(payload).ok()
                == Some(serde_json::json!({
                    "assertion_id": assertion_id,
                    "native_assertion_id": trust_types::stable_u32_id(assertion_id.as_bytes()),
                    "source_id": source_id,
                    "span": source_span,
                }))
        );
    }
    Ok(())
}

#[derive(Default)]
struct AtomicBridgeCallbacks {
    checked: usize,
    replayed: usize,
}

impl rustc_driver::Callbacks for AtomicBridgeCallbacks {
    fn config(&mut self, config: &mut Config) {
        config.file_loader = Some(Box::new(FixtureFileLoader));
    }

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.sess.dcx().abort_if_errors();
        for owner in tcx.hir_body_owners() {
            let did = owner.to_def_id();
            if !matches!(tcx.def_kind(did), rustc_hir::def::DefKind::Fn) {
                continue;
            }
            let name = tcx.item_name(did).to_string();
            let (expected_type, expected_ir_type, increment) = match name.as_str() {
                "relaxed_u64" => (AtomicXaddIntegerType::U64, Ty::U64, 7),
                "relaxed_usize" => (AtomicXaddIntegerType::Usize, Ty::Usize, 11),
                "seqcst" => {
                    let captured = capture_relaxed_xadd_u64_body(tcx, ty::Instance::mono(tcx, did))
                        .expect("actual SeqCst body");
                    assert!(
                        captured.sites().is_empty(),
                        "non-relaxed operation grants no site authority"
                    );
                    assert_eq!(captured.refusals().len(), 1);
                    assert_eq!(captured.refusals()[0].1, AtomicCallsiteError::Ordering);
                    let error = lower_compiler_relaxed_xadd_u64_body(&captured)
                        .expect_err("non-relaxed body remains refused");
                    assert!(
                        error
                            .to_string()
                            .contains("compiler-authenticated operation and ordering evidence"),
                        "{error}"
                    );
                    self.checked += 1;
                    continue;
                }
                _ => continue,
            };
            let captured = capture_relaxed_xadd_u64_body(tcx, ty::Instance::mono(tcx, did))
                .expect("actual optimized std atomic body");
            assert!(captured.refusals().is_empty(), "{:?}", captured.refusals());
            let [site] = captured.sites() else { panic!("exactly one actual authenticated xadd") };
            assert_eq!(site.integer_type(), expected_type);
            assert!(captured.owns_site(site));
            assert!(
                matches!(site.value(), Operand::Constant(ConstValue::Uint(value, 64)) if *value == increment)
            );

            let module =
                lower_compiler_relaxed_xadd_u64_body(&captured).expect("compiler-owned lowering");
            let errors = trust_ir_build::validate_module(&module);
            assert!(errors.is_empty(), "actual compiler-owned output must validate: {errors:?}");
            // Diagnostic bytes only: retain the complete, untouched compiler-owned
            // output, including claims and unused tables. This is not serialized
            // compiler authority or a source/execution refinement certificate.
            println!(
                "ATOMIC_MODULE_CENSUS {}",
                serde_json::to_string(&serde_json::json!({
                    "schema": "trust.atomic-module-census.v1",
                    "authority": "NoOfficialEvidence",
                    "owner": captured.function().def_path,
                    "module": &module,
                }))
                .expect("serialize actual emitted module")
            );
            let census = |candidate: &Module| {
                measured_module_census(
                    candidate,
                    &name,
                    expected_ir_type.clone(),
                    increment as i128,
                    captured.target_llvm_triple(),
                    site.span(),
                )
            };
            census(&module).expect("complete measured compiler-owned module census");
            if expected_type == AtomicXaddIntegerType::U64 {
                // Direct immutable attachment to the actual lowering result.
                // Neither the census nor a serialized/manual mirror supplies
                // replay authority; the whole module is reflected unchanged.
                replay::actual_u64(&module);
                self.replayed += 1;
                // These are mutations of diagnostic clones only. They test the
                // census, never try to grant compiler authority or normalize
                // the original module for a consumer.
                let mut changed = module.clone();
                changed.types.push(Ty::U32);
                assert!(census(&changed).is_err(), "unused type rows must be counted");
                let mut changed = module.clone();
                changed.functions[0].blocks[0].body[2].inst =
                    Inst::Copy { ty: Ty::Ptr, operand: ValueId::new(0) };
                assert!(census(&changed).is_err(), "non-atomic SSA edges must be exact");
                let mut changed = module.clone();
                changed.functions[0].blocks[0].body[2].proofs.push(trust_ir::ProofAnnotation::Pure);
                assert!(census(&changed).is_err(), "non-atomic annotations must be counted");
                let mut changed = module.clone();
                changed.functions[0].calling_conv = CallingConv::Rust;
                assert!(census(&changed).is_err(), "calling convention must be exact");
                let mut changed = module.clone();
                changed.structs[1].repr = StructRepr::C;
                assert!(census(&changed).is_err(), "transparent layout must not be relabeled");
                let mut changed = module.clone();
                changed.proof_obligations.push(changed.proof_obligations[0].clone());
                assert!(census(&changed).is_err(), "all obligation rows must be counted");
                let mut changed = module.clone();
                changed.intern_blob(vec![0, 0, 0, 0]);
                assert_eq!(
                    census(&changed),
                    Err("blobs.is_empty()"),
                    "a trust-ir v70 weight-blob row must be counted"
                );
            } else {
                replay::usize_reflected(&module);
            }
            let target = module.target_info.as_ref().expect("compiler target survives lowering");
            assert_eq!(target.triple, tcx.sess.target.llvm_target.to_string());
            assert_eq!(target.pointer_size, 8);
            assert_eq!(target.endianness, Endianness::Little);
            assert_eq!(target.struct_passing, StructPassingPolicy::Unclassified);
            assert!(target.abi.is_none(), "no invented aggregate ABI classification");
            assert!(module.proof_certificates.is_empty());
            let [function] = module.functions.as_slice() else { panic!("one owned function") };
            assert!(
                !function
                    .proofs
                    .iter()
                    .any(|proof| matches!(proof, trust_ir::ProofAnnotation::Pure)),
                "compiler-owned atomic writes confer no function-level purity claim"
            );
            let rmws = function
                .blocks
                .iter()
                .flat_map(|block| {
                    block.body.iter().enumerate().filter_map(move |(index, node)| {
                        matches!(node.inst, Inst::AtomicRMW { .. }).then_some((block, index, node))
                    })
                })
                .collect::<Vec<_>>();
            let [(block, index, node)] = rmws.as_slice() else { panic!("exactly one actual RMW") };
            assert_eq!(block.id.index() as usize, site.block().0);
            let Inst::AtomicRMW { op, ty, ptr, value, ordering } = &node.inst else {
                unreachable!()
            };
            assert_eq!(*op, AtomicRMWOp::Add);
            assert_eq!(*ty, expected_ir_type);
            assert_eq!(*ordering, Ordering::Relaxed);
            assert_ne!(ptr, value);
            assert!(node.proofs.is_empty(), "operation recognition confers no safety proof");
            assert_eq!(node.results.len(), 1);
            let old = node.results[0];
            assert!(block.body[..*index].iter().any(|definition| {
                definition.results.contains(value) && matches!(&definition.inst,
                    Inst::Const { ty, value: Constant::Int(n) } if *ty == expected_ir_type && *n == increment as i128)
            }), "actual nonzero increment must reach the RMW unchanged");

            let Some(Inst::Br { target, args }) = block.body.last().map(|node| &node.inst) else {
                panic!("real normal continuation")
            };
            assert_eq!(target.index() as usize, site.target().0);
            let continuation = function
                .blocks
                .iter()
                .find(|block| block.id == *target)
                .expect("actual continuation block");
            // A dominating SSA result can flow directly; a block-parameter
            // lane must instead carry that very result. Neither may return
            // the increment or a newly computed count.
            let returned = args
                .iter()
                .position(|value| *value == old)
                .map_or(old, |lane| continuation.params[lane].0);
            assert!(
                continuation.body.iter().any(
                    |node| matches!(&node.inst, Inst::Return { values } if values == &[returned])
                ),
                "function returns the old RMW result, not the increment or updated value"
            );

            let obligations = module.proof_obligations.iter().collect::<Vec<_>>();
            assert_eq!(obligations.len(), 2);
            for (obligation, kind) in
                obligations.iter().zip([ObligationKind::MemorySafety, ObligationKind::Ownership])
            {
                assert_eq!(obligation.kind, kind);
                assert_eq!(obligation.status, ProofStatus::Pending);
                assert_eq!(obligation.function, Some(function.id));
                assert_eq!(
                    obligation.site,
                    Some(ObligationSite::new(function.id, block.id, *index as u32))
                );
                let formula = obligation.formula.as_ref().expect("exact source obligation record");
                assert_eq!(formula.schema, trust_ir_bridge::TRUST_OBLIGATION_SOURCE_SCHEMA);
                assert!(
                    formula.smtlib.is_none()
                        && formula.sort.is_none()
                        && formula.bindings.is_empty()
                );
                assert!(obligation.source.is_some());
            }

            let mut public = captured.function().clone();
            refuses_public_model(&public);
            let Terminator::Call { args, .. } = &mut public.body.blocks[site.block().0].terminator
            else {
                panic!("preserved Call")
            };
            args[1] = Operand::Constant(ConstValue::Uint(0, 64));
            refuses_public_model(&public);
            // The owner's model remains unchanged and independently lowerable.
            assert!(
                matches!(site.value(), Operand::Constant(ConstValue::Uint(value, 64)) if *value == increment)
            );
            assert!(lower_compiler_relaxed_xadd_u64_body(&captured).is_ok());
            self.checked += 1;
        }
        assert_eq!(self.checked, 3, "both widths and the wrong-ordering control executed");
        assert_eq!(self.replayed, 1, "exactly the actual U64 module received a closed replay");
        Compilation::Stop
    }
}

#[test]
fn real_std_fetch_add_reaches_exact_ir_with_pending_obligations_only() {
    let mut callbacks = AtomicBridgeCallbacks::default();
    let args = vec![
        "rustc".into(),
        FIXTURE_PATH.into(),
        "--crate-name=compiler_atomic_bridge_fixture".into(),
        "--crate-type=lib".into(),
        "--edition=2021".into(),
        "-Copt-level=3".into(),
        "-Zmir-opt-level=3".into(),
        "-Zno-codegen".into(),
        "-Zcodegen-backend=dummy".into(),
        "--sysroot".into(),
        compiler_sysroot(),
    ];
    let result = rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
        rustc_driver::run_compiler(&args, &mut callbacks);
        Ok(())
    });
    assert!(result.is_ok(), "real atomic fixture compilation must succeed");
    assert_eq!(callbacks.checked, 3);
    assert_eq!(callbacks.replayed, 1);
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
#[path = "support/native_test_entry.rs"]
mod native_test_entry;

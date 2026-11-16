// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Compiler-owned diagnostic metadata controls, not atomic execution proofs.
//! Malformed consts and the cloned TailCall below are adversarial inputs built
//! inside a real compiler session; they are never published as valid rustc MIR.

use rustc_abi::Size;
use trust_types::{AtomicOpKind, AtomicOrdering, Place, SourceSpan};

use super::*;
use crate::convert::faithful_atomic_xadd::metadata;

const FIXTURE_PATH: &str = "faithful_atomic_xadd_fixture.rs";
const FIXTURE_SOURCE: &str = r#"
#![feature(intrinsics, core_intrinsics, adt_const_params)]
#![allow(dead_code)]
use std::sync::atomic::{AtomicUsize, Ordering};
pub fn relaxed(counter: &AtomicUsize) -> usize {
    counter.fetch_add(1, Ordering::Relaxed)
}
#[inline(never)]
pub fn atomic_xadd(value: usize) -> usize { value }
pub fn lookalike(value: usize) -> usize { atomic_xadd(value) }

mod unauthorized {
    #[rustc_intrinsic]
    pub unsafe fn atomic_xadd<T: Copy, U: Copy, const ORD: std::intrinsics::AtomicOrdering>(
        dst: *mut T, value: U,
    ) -> T;
}
pub unsafe fn unauthorized_xadd(dst: *mut usize, value: usize) -> usize {
    unsafe {
        unauthorized::atomic_xadd::<usize, usize, { std::intrinsics::AtomicOrdering::Relaxed }>(
            dst, value,
        )
    }
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
            Err(io::Error::other("unexpected atomic fixture source path"))
        }
    }

    fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
        Err(io::Error::other("binary source reads are unsupported in atomic fixture"))
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

fn scalar<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>, bits: u128, bytes: u64) -> ty::Const<'tcx> {
    let scalar = ty::ScalarInt::try_from_uint(bits, Size::from_bytes(bytes)).expect("test scalar");
    ty::Const::new_value(tcx, ty::ValTree::from_scalar_int(tcx, scalar), ty)
}

fn replace_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    original: &mir::Operand<'tcx>,
    args: &[ty::GenericArg<'tcx>],
) -> mir::Operand<'tcx> {
    let (did, _) = original.const_fn_def().expect("real direct intrinsic");
    let mir::Operand::Constant(original) = original else { panic!("FnDef constant") };
    let mut constant = original.clone();
    constant.const_ =
        mir::Const::zero_sized(ty::Ty::new_fn_def(tcx, did, ty::Binder::dummy(tcx.mk_args(args))));
    mir::Operand::Constant(constant)
}

fn check_typed_controls<'tcx>(tcx: TyCtxt<'tcx>, func: &mir::Operand<'tcx>) {
    let (_, original_args) = func.const_fn_def().expect("real atomic_xadd");
    let original_ordering = original_args[2].as_const().expect("ordering const");
    let ordering_ty = original_ordering.try_to_value().expect("evaluated enum const").ty;
    let operands = [Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))];
    let dest = Place::local(3);
    let span = SourceSpan::default();
    assert!(metadata(tcx, func, &operands, &dest, &span).is_none(), "logical lane unchanged");
    let _faithful = crate::ty_convert::FaithfulScalarsGuard::enable();
    let enum_value = |fields: Vec<ty::Const<'tcx>>| {
        ty::Const::new_value(tcx, ty::ValTree::from_branches(tcx, fields), ordering_ty)
    };
    for (discriminant, expected) in [
        (0, AtomicOrdering::Relaxed),
        (1, AtomicOrdering::Release),
        (2, AtomicOrdering::Acquire),
        (3, AtomicOrdering::AcqRel),
        (4, AtomicOrdering::SeqCst),
    ] {
        let ordering = enum_value(vec![scalar(tcx, tcx.types.u32, discriminant, 4)]);
        let args = [original_args[0], original_args[1], ordering.into()];
        let changed = replace_args(tcx, func, &args);
        let op = metadata(tcx, &changed, &operands, &dest, &span)
            .expect("recognized intrinsic")
            .expect("concrete typed ordering");
        assert_eq!(op.ordering, expected);
        assert_eq!(op.op_kind, AtomicOpKind::FetchAdd);
        assert_eq!(op.place, Place::local(1));
        assert_eq!(op.dest, Some(dest.clone()));
        assert_eq!(op.failure_ordering, None);
    }
    let discriminator = scalar(tcx, tcx.types.u32, 0, 4);
    let wrong_enum =
        ty::Const::new_value(tcx, ty::ValTree::from_branches(tcx, [discriminator]), tcx.types.u32);
    let negatives = [
        ("wrong enum type", wrong_enum),
        ("unknown discriminant", enum_value(vec![scalar(tcx, tcx.types.u32, 5, 4)])),
        ("wrong width", enum_value(vec![scalar(tcx, tcx.types.u32, 0, 1)])),
        ("wrong discriminator type", enum_value(vec![scalar(tcx, tcx.types.u8, 0, 1)])),
        ("empty branch", enum_value(vec![])),
        ("extra field", enum_value(vec![discriminator, discriminator])),
        ("leaf not enum", scalar(tcx, ordering_ty, 0, 4)),
        ("branch not discriminator", enum_value(vec![enum_value(vec![])])),
        (
            "unresolved parameter",
            ty::Const::new_param(
                tcx,
                ty::ParamConst { index: 0, name: rustc_span::Symbol::intern("N") },
            ),
        ),
        ("inference variable", ty::Const::new_fresh(tcx, 0)),
    ];
    for (label, ordering) in negatives {
        let changed =
            replace_args(tcx, func, &[original_args[0], original_args[1], ordering.into()]);
        assert!(
            matches!(metadata(tcx, &changed, &operands, &dest, &span), Some(Err(_))),
            "{label}: recognized invalid inputs must not reach textual fallback"
        );
        assert!(
            crate::convert::faithful_atomic_xadd::malformed_cannot_use_legacy_fallback(
                tcx, &changed, &operands, &dest, &span,
            ),
            "{label}: adapter must not replace a typed refusal with parsed display text"
        );
    }
    for (label, args) in [
        ("bool memory", vec![tcx.types.bool.into(), tcx.types.bool.into(), original_args[2]]),
        ("unequal integers", vec![tcx.types.u64.into(), tcx.types.u32.into(), original_args[2]]),
        (
            "pointer with non-usize operand",
            vec![
                ty::Ty::new_mut_ptr(tcx, tcx.types.u8).into(),
                tcx.types.u8.into(),
                original_args[2],
            ],
        ),
    ] {
        let changed = replace_args(tcx, func, &args);
        assert!(
            matches!(metadata(tcx, &changed, &operands, &dest, &span), Some(Err(_))),
            "{label}"
        );
    }
    let pointer = replace_args(
        tcx,
        func,
        &[ty::Ty::new_mut_ptr(tcx, tcx.types.u8).into(), tcx.types.usize.into(), original_args[2]],
    );
    assert!(matches!(metadata(tcx, &pointer, &operands, &dest, &span), Some(Ok(_))));
    assert!(matches!(metadata(tcx, func, &operands[..1], &dest, &span), Some(Err(_))));
    let nonplace = [Operand::Constant(ConstValue::Bool(false)), operands[1].clone()];
    assert!(matches!(metadata(tcx, func, &nonplace, &dest, &span), Some(Err(_))));
    let _frozen = crate::ctfe_reentrancy::enter();
    assert!(
        matches!(metadata(tcx, func, &operands, &dest, &span), Some(Ok(_))),
        "reading an evaluated enum does not force CTFE under the freeze"
    );
}

#[derive(Default)]
struct AtomicCallbacks {
    checked: bool,
}

impl rustc_driver::Callbacks for AtomicCallbacks {
    fn config(&mut self, config: &mut Config) {
        config.file_loader = Some(Box::new(FixtureFileLoader));
    }

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.sess.dcx().abort_if_errors();
        let mut found = false;
        let mut checked_lookalike = false;
        let mut checked_unauthorized = false;
        for owner in tcx.hir_body_owners() {
            let did = owner.to_def_id();
            if !matches!(tcx.def_kind(did), rustc_hir::def::DefKind::Fn) {
                continue;
            }
            let name = tcx.item_name(did).to_string();
            if name != "relaxed" && name != "lookalike" && name != "unauthorized_xadd" {
                continue;
            }
            let body = tcx.optimized_mir(did);
            for (bb, data) in body.basic_blocks.iter_enumerated() {
                let mir::TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    target,
                    unwind,
                    fn_span,
                    ..
                } = &data.terminator().kind
                else {
                    continue;
                };
                let Some((callee, generic_args)) = func.const_fn_def() else { continue };
                if name == "unauthorized_xadd" {
                    assert!(callee.is_local(), "this recognized intrinsic is user-declared");
                    let intrinsic = tcx.intrinsic(callee).expect("real rustc_intrinsic attribute");
                    assert_eq!(intrinsic.name, sym::atomic_xadd);
                    assert!(intrinsic.must_be_overridden, "bodyless intrinsic declaration");
                    assert!(!crate::convert::is_real_sysroot_crate(tcx, callee.krate));
                    assert_ne!(
                        tcx.lang_items().sized_trait().map(|anchor| anchor.krate),
                        Some(callee.krate),
                        "same-named local core is not the lang-item-owning core"
                    );
                    let _faithful = crate::ty_convert::FaithfulScalarsGuard::enable();
                    let operands = [Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))];
                    let dest = Place::local(0);
                    let span = SourceSpan::default();
                    assert_eq!(
                        metadata(tcx, func, &operands, &dest, &span),
                        Some(Err("atomic_xadd is not the compiler's authenticated core intrinsic")),
                        "recognized compiler intrinsics still require sysroot authentication"
                    );
                    assert!(
                        crate::convert::faithful_atomic_xadd::malformed_cannot_use_legacy_fallback(
                            tcx, func, &operands, &dest, &span,
                        ),
                        "a legacy-looking name cannot override authentication refusal"
                    );
                    checked_unauthorized = true;
                    continue;
                }
                if name == "lookalike" && tcx.item_name(callee).as_str() == "atomic_xadd" {
                    let _faithful = crate::ty_convert::FaithfulScalarsGuard::enable();
                    assert!(
                        metadata(tcx, func, &[], &Place::local(0), &SourceSpan::default())
                            .is_none(),
                        "a same-spelled user function is not the compiler intrinsic"
                    );
                    checked_lookalike = true;
                    continue;
                }
                if tcx.intrinsic(callee).is_none_or(|intrinsic| intrinsic.name != sym::atomic_xadd)
                {
                    continue;
                }
                found = true;
                check_typed_controls(tcx, func);
                let convert = |data| {
                    crate::convert::convert_basic_block(
                        tcx,
                        bb,
                        data,
                        Some(body),
                        Some(body.typing_env(tcx)),
                        Some(body.source.def_id()),
                        crate::convert::OptionalOverflowAssertCodegen::ThisSession,
                    )
                };
                let logical_before = serde_json::to_value(convert(data)).expect("logical model");
                {
                    let _faithful = crate::ty_convert::FaithfulScalarsGuard::enable();
                    let converted = convert(data);
                    let Terminator::Call {
                        func: model_name,
                        args: model_args,
                        dest: model_dest,
                        target: model_target,
                        unwind: model_unwind,
                        atomic: Some(atomic),
                        callee_identity,
                        callee_key,
                        ..
                    } = &converted.terminator
                    else {
                        panic!("typed modern xadd stays a Call")
                    };
                    assert!(
                        model_name.contains("__trust_args@"),
                        "real duplicate-crate fingerprint regression"
                    );
                    assert_eq!(
                        *model_name,
                        crate::convert::direct_call_def_path(
                            tcx,
                            callee,
                            generic_args,
                            crate::safe_def_path_str_with_args(tcx, callee, generic_args),
                        )
                    );
                    assert_eq!(
                        *callee_identity,
                        crate::convert::callee_identity_for(tcx, callee, generic_args)
                    );
                    assert_eq!(*callee_key, Some(crate::convert::callee_key_for(tcx, callee)));
                    assert_eq!(model_dest.local, destination.local.as_usize());
                    assert_eq!(*model_target, target.map(|block| BlockId(block.as_usize())));
                    assert_eq!(model_args.len(), args.len());
                    assert_eq!(atomic.ordering, AtomicOrdering::Relaxed);
                    assert_eq!(atomic.op_kind, AtomicOpKind::FetchAdd);
                    assert_eq!(atomic.dest.as_ref(), Some(model_dest));
                    let expected_unwind = match unwind {
                        mir::UnwindAction::Continue => trust_types::UnwindEdge::Continue,
                        mir::UnwindAction::Unreachable => trust_types::UnwindEdge::Unreachable,
                        mir::UnwindAction::Terminate(_) => trust_types::UnwindEdge::Terminate,
                        mir::UnwindAction::Cleanup(block) => {
                            trust_types::UnwindEdge::Cleanup(BlockId(block.as_usize()))
                        }
                    };
                    assert_eq!(*model_unwind, expected_unwind);

                    // Controlled conversion input, not a claim rustc emitted
                    // an intrinsic TailCall for this source program.
                    let mut tail = data.clone();
                    tail.terminator_mut().kind = mir::TerminatorKind::TailCall {
                        func: func.clone(),
                        args: args.clone(),
                        fn_span: *fn_span,
                    };
                    let Terminator::TailCall {
                        func: tail_name,
                        args: tail_args,
                        atomic: Some(tail_atomic),
                        callee_identity: tail_identity,
                        callee_key: tail_key,
                        ..
                    } = crate::convert::convert_basic_block(
                        tcx,
                        bb,
                        &tail,
                        Some(body),
                        Some(body.typing_env(tcx)),
                        Some(body.source.def_id()),
                        crate::convert::OptionalOverflowAssertCodegen::ThisSession,
                    )
                    .terminator
                    else {
                        panic!("typed TailCall metadata")
                    };
                    assert_eq!(tail_name, *model_name);
                    assert_eq!(
                        serde_json::to_value(tail_args).expect("tail operands"),
                        serde_json::to_value(model_args).expect("call operands")
                    );
                    assert_eq!(tail_identity, *callee_identity);
                    assert_eq!(tail_key, *callee_key);
                    assert_eq!(tail_atomic.ordering, AtomicOrdering::Relaxed);
                    assert_eq!(tail_atomic.dest, Some(Place::local(0)));
                }
                assert!(!crate::ty_convert::faithful_scalars());
                assert_eq!(
                    serde_json::to_value(convert(data)).expect("logical model"),
                    logical_before,
                    "new metadata path cannot change the ordinary lane"
                );
            }
        }
        assert!(found, "optimized std AtomicUsize emits the actual modern xadd intrinsic");
        assert!(checked_lookalike, "user-function authentication control executed");
        assert!(checked_unauthorized, "recognized unauthorized intrinsic control executed");
        self.checked = true;
        Compilation::Stop
    }
}

#[test]
fn faithful_atomic_xadd_recovers_typed_metadata_without_rewriting_calls() {
    let mut callbacks = AtomicCallbacks::default();
    let args = vec![
        "rustc".into(),
        FIXTURE_PATH.into(),
        "--crate-name".into(),
        // A legitimate same-named local crate triggers real call fingerprinting.
        // The authenticated intrinsic remains the distinct sysroot core item.
        "core".into(),
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
    assert!(result.is_ok(), "failed to compile actual optimized atomic fixture");
    assert!(callbacks.checked, "compiler metadata and refusal controls must execute");
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Actual compiler-owned operation facts. These do not discharge pointer,
//! memory, concurrency, whole-body refinement or kernel-proof obligations.

use super::*;
use crate::atomic_callsite::{
    AtomicCallsiteError, AtomicXaddIntegerType, CompilerRelaxedXaddBody,
    capture_relaxed_xadd_u64_body,
};
use crate::instance_body::FaithfulInstanceError;

const FIXTURE_PATH: &str = "atomic_callsite_fixture.rs";
const FIXTURE_SOURCE: &str = r#"
#![feature(intrinsics, core_intrinsics, adt_const_params)]
#![allow(dead_code)]
use std::intrinsics::{atomic_xadd, AtomicOrdering};

pub unsafe fn relaxed_u64(pointer: *mut u64, value: u64) -> u64 {
    unsafe { atomic_xadd::<u64, u64, { AtomicOrdering::Relaxed }>(pointer, value) }
}
pub unsafe fn relaxed_usize(pointer: *mut usize) -> usize {
    unsafe { atomic_xadd::<usize, usize, { AtomicOrdering::Relaxed }>(pointer, 1) }
}
pub unsafe fn seqcst(pointer: *mut u64, value: u64) -> u64 {
    unsafe { atomic_xadd::<u64, u64, { AtomicOrdering::SeqCst }>(pointer, value) }
}
pub unsafe fn narrow(pointer: *mut u32, value: u32) -> u32 {
    unsafe { atomic_xadd::<u32, u32, { AtomicOrdering::Relaxed }>(pointer, value) }
}
pub unsafe fn signed(pointer: *mut i64, value: i64) -> i64 {
    unsafe { atomic_xadd::<i64, i64, { AtomicOrdering::Relaxed }>(pointer, value) }
}
pub unsafe fn pointer_arithmetic(pointer: *mut *mut u8, value: usize) -> *mut u8 {
    unsafe { atomic_xadd::<*mut u8, usize, { AtomicOrdering::Relaxed }>(pointer, value) }
}
mod unauthorized {
    #[rustc_intrinsic]
    pub unsafe fn atomic_xadd<T: Copy, U: Copy, const ORD: std::intrinsics::AtomicOrdering>(
        pointer: *mut T, value: U,
    ) -> T;
}
pub unsafe fn fake_core(pointer: *mut u64, value: u64) -> u64 {
    unsafe { unauthorized::atomic_xadd::<u64, u64, { AtomicOrdering::Relaxed }>(pointer, value) }
}
#[inline(never)]
pub unsafe fn generic<const N: usize>(pointer: *mut usize) -> usize {
    unsafe { atomic_xadd::<usize, usize, { AtomicOrdering::Relaxed }>(pointer, N) }
}
pub unsafe fn concrete_generic(pointer: *mut usize) -> usize {
    unsafe { generic::<1>(pointer).wrapping_add(generic::<2>(pointer)) }
}
pub fn plain(value: u64) -> u64 { value }
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
            Err(io::Error::other("unexpected atomic callsite fixture path"))
        }
    }
    fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
        Err(io::Error::other("binary reads are unsupported for atomic callsite fixture"))
    }
    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

fn one_site(owner: &CompilerRelaxedXaddBody<'_>, expected_type: AtomicXaddIntegerType) {
    assert!(owner.refusals().is_empty(), "valid primitive has no candidate refusals");
    let [site] = owner.sites() else { panic!("exactly one authenticated primitive") };
    assert!(owner.owns_site(site));
    assert!(std::ptr::eq(owner.site(site.block()).expect("exact block lookup"), site));
    assert_eq!(site.integer_type(), expected_type);
    let block = owner
        .function()
        .body
        .blocks
        .iter()
        .find(|block| block.id == site.block())
        .expect("owned block");
    let Terminator::Call {
        args, dest, target, span, callee_identity, atomic: Some(atomic), ..
    } = &block.terminator
    else {
        panic!("owner keeps a real Call with diagnostic metadata")
    };
    assert_eq!(
        serde_json::to_value(&args[0]).expect("pointer"),
        serde_json::to_value(site.pointer()).expect("site pointer")
    );
    assert_eq!(
        serde_json::to_value(&args[1]).expect("value"),
        serde_json::to_value(site.value()).expect("site value")
    );
    assert_eq!(dest, site.destination());
    assert_eq!(*target, Some(site.target()));
    assert_eq!(span, site.span());
    assert_eq!(*callee_identity, Some(site.callee_identity()));
    assert_eq!(atomic.ordering, trust_types::AtomicOrdering::Relaxed);
    assert_eq!(atomic.op_kind, trust_types::AtomicOpKind::FetchAdd);
    assert!(
        !owner.target_triple().is_empty()
            && !owner.target_llvm_triple().is_empty()
            && !owner.target_data_layout().is_empty()
    );
}

fn check_field_mutations<'tcx>(tcx: TyCtxt<'tcx>, owner: &CompilerRelaxedXaddBody<'tcx>) {
    let block = owner.sites()[0].block().0;
    for mutation in 0..11 {
        assert!(
            owner.rejects_model_mutation(tcx, |function| {
                let Terminator::Call {
                    args,
                    dest,
                    target,
                    span,
                    callee_identity,
                    atomic,
                    unwind,
                    ..
                } = &mut function.body.blocks[block].terminator
                else {
                    panic!("fresh Call")
                };
                match mutation {
                    0 => args[0] = Operand::Copy(Place::local(0)),
                    1 => args[1] = Operand::Constant(ConstValue::Uint(9, 64)),
                    2 => dest.local = 1,
                    3 => *target = None,
                    4 => *unwind = trust_types::UnwindEdge::Continue,
                    5 => *atomic = None,
                    6 => {
                        atomic.as_mut().expect("metadata").ordering =
                            trust_types::AtomicOrdering::SeqCst
                    }
                    7 => *callee_identity = None,
                    8 => span.file.push_str(".changed"),
                    9 => function.body.locals[1].ty = Ty::Bool,
                    10 => function.body.locals[0].ty = Ty::PtrSizedInt { signed: false },
                    _ => unreachable!("bounded mutation list"),
                }
            }),
            "exact-site control {mutation} must refuse"
        );
    }
    assert!(!owner.rejects_model_mutation(tcx, |_| {}), "unchanged snapshot is positive control");
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
        let definitions = tcx
            .hir_body_owners()
            .filter_map(|owner| {
                let did = owner.to_def_id();
                matches!(tcx.def_kind(did), rustc_hir::def::DefKind::Fn)
                    .then(|| (tcx.item_name(did).to_string(), did))
            })
            .collect::<BTreeMap<_, _>>();
        let u64_instance = ty::Instance::mono(tcx, definitions["relaxed_u64"]);
        let u64_owner = capture_relaxed_xadd_u64_body(tcx, u64_instance).expect("actual u64 body");
        one_site(&u64_owner, AtomicXaddIntegerType::U64);
        assert_eq!(u64_owner.target_llvm_triple(), tcx.sess.target.llvm_target.as_ref());
        assert_eq!(u64_owner.target_data_layout(), tcx.sess.target.data_layout.as_ref());
        check_field_mutations(tcx, &u64_owner);
        let usize_owner = capture_relaxed_xadd_u64_body(
            tcx,
            ty::Instance::mono(tcx, definitions["relaxed_usize"]),
        )
        .expect("actual usize body");
        one_site(&usize_owner, AtomicXaddIntegerType::Usize);
        assert!(
            !u64_owner.owns_site(&usize_owner.sites()[0]),
            "another instance is not this owner"
        );
        let again =
            capture_relaxed_xadd_u64_body(tcx, u64_instance).expect("fresh same-instance capture");
        assert_eq!(u64_owner.instance(), again.instance());
        assert_eq!(
            serde_json::to_value(u64_owner.function()).expect("first model"),
            serde_json::to_value(again.function()).expect("second model")
        );
        assert!(
            !u64_owner.owns_site(&again.sites()[0]),
            "even identical snapshots have distinct owner seals"
        );
        let before = serde_json::to_value(u64_owner.function()).expect("model");
        let mut detached = u64_owner.function().clone();
        detached.def_path.push_str("::forged");
        detached.body.blocks.clear();
        assert_eq!(
            serde_json::to_value(u64_owner.function()).expect("owned model"),
            before,
            "public model clones cannot edit or rebind the capability owner"
        );

        for (name, error) in [
            ("seqcst", AtomicCallsiteError::Ordering),
            ("narrow", AtomicCallsiteError::IntegerType),
            ("signed", AtomicCallsiteError::IntegerType),
            ("pointer_arithmetic", AtomicCallsiteError::IntegerType),
            (
                "fake_core",
                AtomicCallsiteError::Intrinsic(
                    "atomic_xadd is not the compiler's authenticated core intrinsic",
                ),
            ),
        ] {
            let owner =
                capture_relaxed_xadd_u64_body(tcx, ty::Instance::mono(tcx, definitions[name]))
                    .expect("negative body still captured without atomic admission");
            assert!(owner.sites().is_empty(), "{name}");
            let [(_, actual)] = owner.refusals() else { panic!("one explicit refusal for {name}") };
            assert_eq!(*actual, error, "{name}");
        }
        let generic_did = definitions["generic"];
        let unresolved = ty::Instance::new_raw(
            generic_did,
            ty::GenericArgs::identity_for_item(tcx, generic_did),
        );
        assert!(matches!(
            capture_relaxed_xadd_u64_body(tcx, unresolved),
            Err(AtomicCallsiteError::Instance(FaithfulInstanceError::NonConcrete))
        ));
        let body = tcx.optimized_mir(definitions["concrete_generic"]);
        let mut generic_owners = Vec::new();
        for block in body.basic_blocks.iter() {
            let mir::TerminatorKind::Call { func, .. } = &block.terminator().kind else { continue };
            let Some((did, _)) = func.const_fn_def() else { continue };
            if did != generic_did {
                continue;
            }
            let resolved = crate::instance_body::resolve_faithful_call(tcx, body, func)
                .expect("actual concrete generic selection");
            generic_owners.push(
                capture_relaxed_xadd_u64_body(tcx, resolved.instance)
                    .expect("concrete generic owner"),
            );
        }
        assert_eq!(generic_owners.len(), 2);
        for owner in &generic_owners {
            one_site(owner, AtomicXaddIntegerType::Usize);
        }
        assert_ne!(generic_owners[0].instance(), generic_owners[1].instance());
        assert_eq!(
            generic_owners[0].function().def_path,
            generic_owners[1].function().def_path,
            "definition labels alone cannot bind concrete instances"
        );
        assert!(!generic_owners[0].owns_site(&generic_owners[1].sites()[0]));
        let values = generic_owners
            .iter()
            .map(|owner| {
                let Operand::Constant(ConstValue::Uint(value, 64)) = owner.sites()[0].value()
                else {
                    panic!("concrete const parameter keeps exact scalar value")
                };
                *value
            })
            .collect::<BTreeSet<_>>();
        assert_eq!(values, BTreeSet::from([1, 2]));
        let plain =
            capture_relaxed_xadd_u64_body(tcx, ty::Instance::mono(tcx, definitions["plain"]))
                .expect("ordinary body remains ordinary");
        assert!(plain.sites().is_empty() && plain.refusals().is_empty());
        let _frozen = crate::ctfe_reentrancy::enter();
        assert!(matches!(
            capture_relaxed_xadd_u64_body(tcx, u64_instance),
            Err(AtomicCallsiteError::Instance(FaithfulInstanceError::Frozen))
        ));
        self.checked = true;
        Compilation::Stop
    }
}

#[test]
fn atomic_callsite_owner_binds_actual_instance_and_refuses_replay_and_modified_sites() {
    let mut callbacks = AtomicCallbacks::default();
    let args = vec![
        "rustc".into(),
        FIXTURE_PATH.into(),
        "--crate-name".into(),
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
    assert!(result.is_ok(), "compiler callsite fixture compiled and checked");
    assert!(callbacks.checked, "all real-compiler ownership controls executed");
}

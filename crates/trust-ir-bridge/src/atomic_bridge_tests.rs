//! Synthetic lowering controls. These deliberately exercise the PRIVATE seam;
//! compiler-source authentication is tested separately in trust-mir-extract.

use trust_ir::value::BlockId as IrBlockId;
use trust_types::{AtomicOperation, BasicBlock, SourceSpan, VerifiableBody};

fn lower_owned_function(
    function: &VerifiableFunction,
    blocks: &FxHashSet<BlockId>,
) -> Result<Module, BridgeError> {
    // Synthetic target is explicit; this private test seam grants no public
    // compiler capability. Real target capture is an integration-test duty.
    super::lower_owned_function(function, blocks, "aarch64-apple-darwin")
}

use super::*;

fn fixture(ty: Ty) -> VerifiableFunction {
    let span = SourceSpan::default();
    VerifiableFunction {
        name: "synthetic_atomic".into(),
        def_path: "synthetic_atomic::fetch_add".into(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(ty.clone()) },
                    name: Some("ptr".into()),
                },
                LocalDecl { index: 2, ty: ty.clone(), name: Some("delta".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "core::intrinsics::atomic_xadd::<u64,u64,Relaxed>".into(),
                        args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        atomic: Some(AtomicOperation {
                            place: Place::local(1),
                            dest: Some(Place::local(0)),
                            op_kind: AtomicOpKind::FetchAdd,
                            ordering: AtomicOrdering::Relaxed,
                            failure_ordering: None,
                            span: span.clone(),
                        }),
                        unwind: UnwindEdge::Unreachable,
                        callee_identity: None,
                        callee_key: None,
                        is_foreign: false,
                        is_unsafe_sig: true,
                        span,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn refuses(result: Result<Module, BridgeError>) {
    assert!(
        matches!(result, Err(BridgeError::UnsupportedOp(ref message))
        if message.contains("compiler-authenticated operation and ordering evidence")),
        "public data did not refuse: {result:?}"
    );
}

#[test]
fn atomic_metadata_cannot_authorize_any_data_only_entry() {
    let fixture = fixture(Ty::u64());
    refuses(lower_to_trust_ir(&fixture));
    refuses(lower_functions_to_trust_ir("synthetic", [&fixture]));
    refuses(lower_to_trust_ir_functions("synthetic", std::slice::from_ref(&fixture)));
    let encoded = serde_json::to_string(&fixture).expect("serialize fixture");
    let roundtrip = serde_json::from_str(&encoded).expect("deserialize fixture");
    refuses(lower_to_trust_ir(&roundtrip));
    let mut module = Module::new("synthetic");
    let error = lower_to_trust_ir_function(&fixture, &mut module).expect_err("no authority");
    assert!(error.to_string().contains("compiler-authenticated operation and ordering evidence"));
    refuses(lower_owned_function(&fixture, &FxHashSet::default()));
    refuses(lower_owned_function(&fixture, &[BlockId(1)].into_iter().collect()));
}

#[test]
fn atomic_private_lowering_keeps_exact_operands_old_result_and_pending_obligations() {
    for (ty, expected_ty) in
        [(Ty::u64(), TrustIrTy::U64), (Ty::PtrSizedInt { signed: false }, TrustIrTy::Usize)]
    {
        let module = lower_owned_function(&fixture(ty), &[BlockId(0)].into_iter().collect())
            .expect("private test seam");
        let errors = trust_ir_build::validate_module(&module);
        assert!(errors.is_empty(), "invalid lowering: {errors:?}");
        let function = &module.functions[0];
        assert!(
            !function.proofs.iter().any(|proof| matches!(proof, ProofAnnotation::Pure)),
            "an atomic write cannot carry a function-level purity claim"
        );
        let entry = function.blocks.iter().find(|block| block.id == function.entry).expect("entry");
        let (index, node) = entry
            .body
            .iter()
            .enumerate()
            .find(|(_, node)| matches!(node.inst, Inst::AtomicRMW { .. }))
            .expect("RMW");
        assert_eq!(node.results.len(), 1);
        let result = node.results[0];
        assert!(node.proofs.is_empty(), "operation selection grants no safety claim");
        assert!(matches!(&node.inst,
            Inst::AtomicRMW { op: AtomicRMWOp::Add, ty, ptr, value, ordering: Ordering::Relaxed }
            if *ty == expected_ty && *ptr == entry.params[0].0 && *value == entry.params[1].0));
        let Some(Inst::Br { target, args }) = entry.body.last().map(|node| &node.inst) else {
            panic!("normal continuation must remain a branch");
        };
        assert_eq!(*target, IrBlockId::new(1));
        let continuation =
            function.blocks.iter().find(|block| block.id == *target).expect("continuation");
        // The bridge may reuse a dominating SSA value directly or pass it in
        // a block-parameter lane. Both must return exactly the OLD RMW result.
        let returned = args
            .iter()
            .position(|value| *value == result)
            .map_or(result, |lane| continuation.params[lane].0);
        assert!(
            continuation
                .body
                .iter()
                .any(|node| matches!(&node.inst, Inst::Return { values } if values == &[returned])),
            "old-result data flow lost: {function:?}"
        );
        assert_eq!(module.proof_obligations.len(), 2);
        for (obligation, kind) in module
            .proof_obligations
            .iter()
            .zip([ObligationKind::MemorySafety, ObligationKind::Ownership])
        {
            assert_eq!(obligation.kind, kind);
            assert_eq!(obligation.status, ProofStatus::Pending);
            assert_eq!(obligation.function, Some(function.id));
            assert_eq!(
                obligation.site,
                Some(ObligationSite::new(function.id, entry.id, index as u32))
            );
            let formula = obligation.formula.as_ref().expect("source record");
            assert_eq!(formula.schema, TRUST_OBLIGATION_SOURCE_SCHEMA);
            assert!(formula.smtlib.is_none(), "no invented solvable predicate");
        }
        assert!(function.blocks.iter().flat_map(|block| &block.body).all(|node| !matches!(
            node.inst,
            Inst::Assume { .. } | Inst::Undef { .. } | Inst::Call { .. }
        )));
    }
}

#[test]
fn pure_scalar_identity_keeps_existing_non_atomic_annotation() {
    let mut function = fixture(Ty::u64());
    function.name = "pure_scalar_identity".into();
    function.def_path = "synthetic_atomic::pure_scalar_identity".into();
    function.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::u64(), name: None },
        LocalDecl { index: 1, ty: Ty::u64(), name: Some("value".into()) },
    ];
    function.body.arg_count = 1;
    function.body.blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
            span: SourceSpan::default(),
        }],
        terminator: Terminator::Return,
    }];
    for module in [
        lower_to_trust_ir(&function).expect("ordinary scalar identity"),
        lower_owned_function(&function, &FxHashSet::default()).expect("no atomic sites"),
    ] {
        assert!(trust_ir_build::validate_module(&module).is_empty());
        let [lowered] = module.functions.as_slice() else { panic!("one scalar function") };
        assert!(lowered.proofs.iter().any(|proof| matches!(proof, ProofAnnotation::Pure)));
        let [block] = lowered.blocks.as_slice() else { panic!("one identity block") };
        let [(value, ty)] = block.params.as_slice() else { panic!("one scalar parameter") };
        assert_eq!(*ty, TrustIrTy::U64);
        // Rvalue::Use writes a fresh SSA Copy for the return local. Follow
        // that exact typed identity edge rather than requiring ID reuse.
        let [copy, returned] = block.body.as_slice() else {
            panic!("expected identity Copy then Return: {block:?}")
        };
        assert!(matches!(&copy.inst,
            Inst::Copy { ty: TrustIrTy::U64, operand } if operand == value));
        let [copied] = copy.results.as_slice() else { panic!("one copied value") };
        assert_ne!(copied, value, "the copy defines a fresh SSA value");
        assert!(matches!(&returned.inst,
            Inst::Return { values } if values == &[*copied]));
        assert!(returned.results.is_empty());
        assert!(module.proof_obligations.is_empty());
        assert!(module.proof_certificates.is_empty());
        assert!(lowered.blocks.iter().flat_map(|block| &block.body).all(|node| {
            !matches!(node.inst, Inst::AtomicRMW { .. } | Inst::Call { .. } | Inst::Store { .. })
        }));
    }
}

#[test]
fn atomic_private_lowering_rechecks_narrow_envelope() {
    for case in 0..9 {
        let mut function = fixture(Ty::u64());
        let Terminator::Call { args, dest, target, atomic, unwind, .. } =
            &mut function.body.blocks[0].terminator
        else {
            panic!("fixture Call")
        };
        let metadata = atomic.as_mut().expect("metadata");
        match case {
            0 => metadata.ordering = AtomicOrdering::Acquire,
            1 => metadata.op_kind = AtomicOpKind::FetchSub,
            2 => metadata.failure_ordering = Some(AtomicOrdering::Relaxed),
            3 => metadata.place = Place::local(2),
            4 => metadata.dest = Some(Place::local(2)),
            5 => *unwind = UnwindEdge::Continue,
            6 => *target = None,
            7 => {
                args.pop();
            }
            8 => dest.projections.push(Projection::Deref),
            _ => unreachable!(),
        }
        assert!(
            lower_owned_function(&function, &[BlockId(0)].into_iter().collect()).is_err(),
            "case {case}"
        );
    }
    for ty in [Ty::u32(), Ty::i64()] {
        assert!(lower_owned_function(&fixture(ty), &[BlockId(0)].into_iter().collect()).is_err());
    }
}

#[test]
fn atomic_lowering_is_not_a_native_verification_bundle() {
    let module = lower_owned_function(&fixture(Ty::u64()), &[BlockId(0)].into_iter().collect())
        .expect("private lowering mechanics");
    // No compiler public-obligation identity, solvable predicate, ownership
    // request, or solver evidence was minted by operation authentication.
    let error = crate::native_request::native_verification_bundle_from_module(
        module,
        trust_ir::ProofDigest::sha256([19; 32]),
        FuncId::new(0),
    )
    .expect_err("an authenticated operation is not a proof-grade bundle");
    assert!(matches!(error,
        crate::native_request::NativeVerificationBundleBuildError::MissingPublicObligationIdentity(_)),
        "unexpected refusal: {error:?}");
}

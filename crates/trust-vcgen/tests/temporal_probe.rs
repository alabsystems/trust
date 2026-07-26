// Probe: does the production vcgen entry emit the mmap temporal VC?
use trust_types::*;

fn probe_func() -> VerifiableFunction {
    VerifiableFunction {
        name: "main".into(),
        def_path: "main".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            return_ty: Ty::Unit,
            arg_count: 0,
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("m".into()) },
                LocalDecl { index: 2, ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) }, name: Some("r".into()) },
                LocalDecl { index: 3, ty: Ty::u8(), name: Some("x".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::AddressOf(false, Place::local(3)),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Call { unwind: trust_types::UnwindEdge::Unreachable,
                        is_unsafe_sig: false, is_foreign: false,
                        func: "mmap::MmapMut::map_mut".to_string(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn probe_temporal_vc_survives_production_entry() {
    let func = probe_func();
    let vcs = trust_vcgen::generate_vcs(&func);
    let kinds: Vec<String> = vcs.iter().map(|vc| vc.kind.description()).collect();
    eprintln!("ALL KINDS: {kinds:#?}");
    let temporal = vcs.iter().any(|vc| matches!(vc.kind, VcKind::Temporal { .. }));
    let bounds = vcs
        .iter()
        .any(|vc| matches!(vc.kind, VcKind::ExternallyMutableAllocationBounds { .. }));
    eprintln!("temporal={temporal} bounds={bounds}");
    let l2 = trust_vcgen::filter_vcs_by_level(vcs, ProofLevel::L2Domain);
    let temporal_l2 = l2.iter().any(|vc| matches!(vc.kind, VcKind::Temporal { .. }));
    eprintln!("temporal after L2 filter={temporal_l2}");
    assert!(temporal && bounds && temporal_l2);
}

#[test]
fn probe_temporal_vc_survives_discharge_entry() {
    let func = probe_func();
    let db = trust_vcgen::SummaryDatabase::new();
    let (solver_vcs, discharged) =
        trust_vcgen::generate_vcs_with_discharge_and_summaries(&func, &db);
    let solver_kinds: Vec<String> =
        solver_vcs.iter().map(|vc| vc.kind.description()).collect();
    let discharged_kinds: Vec<String> =
        discharged.iter().map(|(vc, r)| format!("{} => {:?}", vc.kind.description(), std::mem::discriminant(r))).collect();
    eprintln!("SOLVER: {solver_kinds:#?}");
    eprintln!("DISCHARGED: {discharged_kinds:#?}");
    let temporal_in_solver =
        solver_vcs.iter().any(|vc| matches!(vc.kind, VcKind::Temporal { .. }));
    assert!(temporal_in_solver, "temporal VC must reach the solver lane");
}

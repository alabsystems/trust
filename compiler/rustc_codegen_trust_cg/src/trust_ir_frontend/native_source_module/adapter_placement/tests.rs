use super::*;

#[test]
fn primitive_adapter_abi_stops_before_stack_float_wide_and_variadic_carriers() {
    let mut signature = FuncTy {
        params: vec![Ty::Ptr, Ty::I8, Ty::U16, Ty::I32, Ty::U64, Ty::Isize, Ty::Usize, Ty::Char],
        returns: vec![Ty::Ptr],
        is_vararg: false,
        abi: None,
    };
    let p = flat_placement(&signature).unwrap();
    assert_eq!(p.params[0], ParamPlace::Scalar(ScalarPlace::gpr(0, 64)));
    assert_eq!(p.params[1], ParamPlace::Scalar(ScalarPlace::gpr(1, 8)));
    assert_eq!(p.params[7], ParamPlace::Scalar(ScalarPlace::gpr(7, 32)));
    signature.params.push(Ty::U8);
    assert!(flat_placement(&signature).is_none(), "ninth argument must not guess a register");
    signature.params = vec![Ty::F64];
    assert!(flat_placement(&signature).is_none());
    signature.params = vec![Ty::U64];
    signature.returns = vec![Ty::U128];
    assert!(flat_placement(&signature).is_none());
    signature.returns = vec![];
    signature.is_vararg = true;
    assert!(flat_placement(&signature).is_none());
}

fn zero_fixture() -> (Module, Vec<NativeWorkItem>) {
    use trust_ir::{Block, BlockId, InstrNode, ValueId};
    let (mut module, mut items) = super::super::tests::fixture();
    module.closure_types[0].captures.clear();
    module.closure_layouts[0].size = 0;
    module.closure_layouts[0].align = 1;
    module.closure_layouts[0].capture_offsets.clear();
    module.func_types[0].params = vec![Ty::U64];
    let source_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    module.functions[1].ty = source_ty;
    let v = ValueId::new;
    module.functions[1].blocks =
        vec![Block::new(BlockId::new(0)).with_param(v(0), Ty::Ptr).with_param(v(1), Ty::U64)];
    module.functions[1].blocks[0].body = vec![InstrNode::new(Inst::Return { values: vec![v(1)] })];
    let Inst::MakeClosure { captures, .. } = &mut module.functions[0].blocks[0].body[0].inst else {
        unreachable!()
    };
    captures.clear();
    module.functions[2].blocks = vec![Block::new(BlockId::new(0)).with_param(v(0), Ty::U64)];
    module.functions[2].blocks[0].body = vec![
        InstrNode::new(Inst::MakeClosure {
            ty: ClosureTyId::new(0),
            func: FuncId::new(2),
            captures: vec![],
        })
        .with_result(v(1)),
        InstrNode::new(Inst::Alloca {
            ty: Ty::Closure(ClosureTyId::new(0)),
            count: None,
            align: Some(1),
        })
        .with_result(v(2)),
        InstrNode::new(Inst::Store {
            ty: Ty::Closure(ClosureTyId::new(0)),
            ptr: v(2),
            value: v(1),
            volatile: false,
            align: Some(1),
        }),
        InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![v(2), v(0)] })
            .with_result(v(3)),
        InstrNode::new(Inst::Return { values: vec![v(3)] }),
    ];
    items[1].placement = Some(FnPlacement {
        params: vec![
            ParamPlace::Scalar(ScalarPlace::gpr(0, 64)),
            ParamPlace::Scalar(ScalarPlace::gpr(1, 64)),
        ],
        ret: ReturnPlace::Scalar(ScalarPlace::gpr(0, 64)),
    });
    (module, items)
}

fn zero_input<'a>(
    module: &'a Module,
    items: &'a [NativeWorkItem],
    conserved: &'a BTreeSet<FuncId>,
    source: &'a BTreeSet<FuncId>,
    foreign: &'a BTreeSet<FuncId>,
    target: &'a ExpectedTarget,
) -> NativeModuleInput<'a> {
    NativeModuleInput {
        producer: module,
        base: Some(module),
        items,
        conserved,
        source_ids: source,
        foreign_declarations: foreign,
        has_statics: false,
        target,
    }
}

fn owned_zero_fixture() -> (Module, Vec<NativeWorkItem>) {
    use trust_ir::{InstrNode, ValueId};
    let (mut module, mut items) = zero_fixture();
    let nominal = Ty::Closure(ClosureTyId::new(0));
    let source_ty = module.functions[1].ty;
    module.func_types[source_ty.as_usize()].params[0] = nominal.clone();
    module.functions[1].blocks[0].params[0].1 = nominal;
    let v = ValueId::new;
    module.functions[2].blocks[0].body = vec![
        InstrNode::new(Inst::MakeClosure {
            ty: ClosureTyId::new(0),
            func: FuncId::new(2),
            captures: vec![],
        })
        .with_result(v(1)),
        InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![v(1), v(0)] })
            .with_result(v(2)),
        InstrNode::new(Inst::Return { values: vec![v(2)] }),
    ];
    items[1].placement.as_mut().unwrap().params =
        vec![ParamPlace::Ignore, ParamPlace::Scalar(ScalarPlace::gpr(0, 64))];
    (module, items)
}

#[test]
fn owned_empty_adapter_requires_actual_ignored_environment_and_unchanged_argument_abi() {
    let (module, items) = owned_zero_fixture();
    let conserved = BTreeSet::from([FuncId::new(0), FuncId::new(1), FuncId::new(2)]);
    let source = BTreeSet::from([FuncId::new(0), FuncId::new(1)]);
    let foreign = BTreeSet::new();
    let target = ExpectedTarget { triple: "arm64-apple-macosx".into(), pointer_size: 8 };
    let observed = derive(
        &zero_input(&module, &items, &conserved, &source, &foreign, &target),
        FuncId::new(2),
    )
    .unwrap()
    .unwrap();
    assert_eq!(observed.params, vec![ParamPlace::Scalar(ScalarPlace::gpr(0, 64))]);
    assert_eq!(observed.ret, ReturnPlace::Scalar(ScalarPlace::gpr(0, 64)));
    for (index, wrong) in [
        (0, ParamPlace::Scalar(ScalarPlace::gpr(0, 64))),
        (1, ParamPlace::Scalar(ScalarPlace::gpr(1, 64))),
        (1, ParamPlace::Ignore),
    ] {
        let mut changed = owned_zero_fixture().1;
        changed[1].placement.as_mut().unwrap().params[index] = wrong;
        assert!(
            derive(
                &zero_input(&module, &changed, &conserved, &source, &foreign, &target),
                FuncId::new(2),
            )
            .is_err()
        );
    }
    let mut changed = owned_zero_fixture().1;
    changed[1].placement.as_mut().unwrap().ret = ReturnPlace::Indirect;
    assert!(
        derive(
            &zero_input(&module, &changed, &conserved, &source, &foreign, &target),
            FuncId::new(2),
        )
        .is_err()
    );
    let mut changed = module.clone();
    changed.closure_layouts[0].align = 2;
    assert!(
        derive(
            &zero_input(&changed, &items, &conserved, &source, &foreign, &target),
            FuncId::new(2),
        )
        .is_err()
    );
}

#[test]
fn borrowed_empty_adapter_checks_actual_environment_register_and_argument_shift() {
    let (module, items) = zero_fixture();
    let conserved = BTreeSet::from([FuncId::new(0), FuncId::new(1), FuncId::new(2)]);
    let source = BTreeSet::from([FuncId::new(0), FuncId::new(1)]);
    let foreign = BTreeSet::new();
    let target = ExpectedTarget { triple: "arm64-apple-macosx".into(), pointer_size: 8 };
    let flat = derive(
        &zero_input(&module, &items, &conserved, &source, &foreign, &target),
        FuncId::new(2),
    )
    .unwrap()
    .unwrap();
    assert_eq!(flat.params, vec![ParamPlace::Scalar(ScalarPlace::gpr(0, 64))]);
    let mut changed = items;
    changed[1].placement.as_mut().unwrap().params[1] = ParamPlace::Scalar(ScalarPlace::gpr(0, 64));
    assert!(
        derive(
            &zero_input(&module, &changed, &conserved, &source, &foreign, &target),
            FuncId::new(2)
        )
        .is_err()
    );
    changed[1].placement.as_mut().unwrap().params[0] = ParamPlace::Ignore;
    assert!(
        derive(
            &zero_input(&module, &changed, &conserved, &source, &foreign, &target),
            FuncId::new(2)
        )
        .unwrap()
        .is_none()
    );
}

#[test]
fn borrowed_empty_adapter_refuses_unit_seeds_and_missing_actual_source() {
    let (mut module, items) = zero_fixture();
    let conserved = BTreeSet::from([FuncId::new(0), FuncId::new(1), FuncId::new(2)]);
    let source = BTreeSet::from([FuncId::new(0), FuncId::new(1)]);
    let foreign = BTreeSet::new();
    let target = ExpectedTarget { triple: "arm64-apple-macosx".into(), pointer_size: 8 };
    let missing = BTreeSet::from([FuncId::new(0), FuncId::new(2)]);
    assert!(
        derive(&zero_input(&module, &items, &missing, &source, &foreign, &target), FuncId::new(2))
            .is_err()
    );
    let Inst::Alloca { ty, .. } = &mut module.functions[2].blocks[0].body[1].inst else {
        unreachable!()
    };
    *ty = Ty::Unit;
    assert!(
        derive(
            &zero_input(&module, &items, &conserved, &source, &foreign, &target),
            FuncId::new(2)
        )
        .is_err()
    );
}

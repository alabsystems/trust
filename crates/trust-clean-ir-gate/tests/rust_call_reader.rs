// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::sync::Arc;

use clean_kernel::{Declaration, Expr, ExprKind, Name};
use trust_certify::clean_island::CleanIslandSession;
use trust_clean_ir_gate::rust_calls::{
    CalleeInterpretation, RetainedRustCallSource, RustCallBinding, reflect_candidate,
    reflect_module_candidate,
};
use trust_clean_origin::{check_faithful, plan_clean_origin_body};
use trust_ir::node::InstrNode;
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, CallingConv, Constant, Function, Inst, Module, Producer, Ty};

fn node(inst: Inst, results: &[u32]) -> InstrNode {
    InstrNode {
        inst,
        results: results.iter().copied().map(ValueId::new).collect(),
        proofs: Vec::new(),
        span: None,
        proof_context: None,
        scope: None,
    }
}

fn call(args: &[u32], result: u32) -> InstrNode {
    node(
        Inst::Call {
            callee: FuncId::new(7),
            args: args.iter().copied().map(ValueId::new).collect(),
        },
        &[result],
    )
}

fn fixture() -> (FuncTy, Function, Vec<CalleeInterpretation>) {
    let signature = FuncTy::unrecorded(vec![Ty::U64], vec![Ty::U64], false);
    let mut function = Function::new(FuncId::new(0), "chain", FuncTyId::new(0), BlockId::new(0));
    function.calling_conv = CallingConv::Rust;
    let mut block = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::U64);
    block.body = vec![
        call(&[0], 1),
        call(&[1], 2),
        node(Inst::Return { values: vec![ValueId::new(2)] }, &[]),
    ];
    function.blocks.push(block);
    let callees = vec![CalleeInterpretation {
        id: FuncId::new(7),
        name: Name::from_string("double"),
        signature: signature.clone(),
    }];
    (signature, function, callees)
}

fn module_fixture() -> (Module, Vec<CalleeInterpretation>) {
    let mut builder = trust_ir_build::ModuleBuilder::new("actual-call-context");
    let ty = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut callee = builder.function("actual_rust_function", ty);
    let entry = callee.create_block();
    let parameter = callee.add_block_param(entry, Ty::U64);
    callee.switch_to_block(entry);
    callee.ret(vec![parameter]);
    callee.build();
    let mut module = builder.build().unwrap();
    module.functions[0].calling_conv = CallingConv::Rust;
    module.functions[0].producer = Some(Producer::TRust);
    let (_, mut root, mut interpretations) = fixture();
    root.id = FuncId::new(1);
    root.ty = ty;
    root.producer = Some(Producer::Clean);
    for node in &mut root.blocks[0].body {
        if let Inst::Call { callee, .. } = &mut node.inst {
            *callee = FuncId::new(0);
        }
    }
    interpretations[0].id = FuncId::new(0);
    // This name is only caller-supplied data. The structural module binding
    // does NOT assert that the Rust identity body implements Lean `double`.
    module.functions.push(root);
    assert!(trust_ir_build::validate_module(&module).is_empty());
    (module, interpretations)
}

fn retained_parts(
    body: &str,
) -> (Arc<clean_kernel::Environment>, Arc<trust_clean_origin::CleanOriginPlan>) {
    use trust_certify::clean_island::RustCallee;
    let declared = ["f", "g"].map(|name| RustCallee {
        clean_name: name.into(),
        params: vec![trust_types::Ty::u64()],
        result: trust_types::Ty::u64(),
    });
    let mut session = CleanIslandSession::new();
    session.declare_rust_callees(&declared).unwrap();
    assert!(!session.check(&format!("def bridge (x : UInt64) : UInt64 := {body}")).is_rejected());
    let roster = declared
        .iter()
        .map(|callee| trust_clean_origin::RustCalleeRef {
            clean_name: callee.clean_name.clone(),
            def_path: format!("rust::{}", callee.clean_name),
            params: callee.params.clone(),
            result: callee.result.clone(),
        })
        .collect::<Vec<_>>();
    let environment = Arc::new(session.environment().unwrap().clone());
    let plan = trust_clean_origin::plan_clean_origin_body_with_rust_callees(
        &environment,
        "bridge",
        &roster,
    )
    .unwrap();
    (environment, Arc::new(plan))
}

fn retained_source(body: &str) -> RetainedRustCallSource {
    let (environment, plan) = retained_parts(body);
    RetainedRustCallSource::retain(environment, plan)
}

fn retained_module() -> (Module, Vec<RustCallBinding>) {
    let mut builder = trust_ir_build::ModuleBuilder::new("retained-source");
    let ty = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    for name in ["actual_f", "actual_g"] {
        let mut function = builder.function(name, ty);
        let entry = function.create_block();
        let value = function.add_block_param(entry, Ty::U64);
        function.switch_to_block(entry);
        function.ret(vec![value]);
        function.build();
    }
    let mut module = builder.build().unwrap();
    for function in &mut module.functions {
        function.producer = Some(Producer::TRust);
        function.calling_conv = CallingConv::Rust;
    }
    let (_, mut root, _) = fixture();
    root.id = FuncId::new(2);
    root.ty = ty;
    root.producer = Some(Producer::Clean);
    if let Inst::Call { callee, .. } = &mut root.blocks[0].body[0].inst {
        *callee = FuncId::new(1);
    }
    if let Inst::Call { callee, .. } = &mut root.blocks[0].body[1].inst {
        *callee = FuncId::new(0);
    }
    module.functions.push(root);
    (
        module,
        vec![
            RustCallBinding { plan_index: 0, function: FuncId::new(0) },
            RustCallBinding { plan_index: 1, function: FuncId::new(1) },
        ],
    )
}

fn binary_call_fixture(body: &str) -> (RetainedRustCallSource, Module, Vec<RustCallBinding>) {
    use trust_certify::clean_island::RustCallee;
    let declared = [("g", 1), ("h", 2)].map(|(name, arity)| RustCallee {
        clean_name: name.into(),
        params: vec![trust_types::Ty::u64(); arity],
        result: trust_types::Ty::u64(),
    });
    let mut session = CleanIslandSession::new();
    session.declare_rust_callees(&declared).unwrap();
    assert!(!session.check(&format!("def bridge (x : UInt64) : UInt64 := {body}")).is_rejected());
    let roster = declared
        .iter()
        .map(|callee| trust_clean_origin::RustCalleeRef {
            clean_name: callee.clean_name.clone(),
            def_path: format!("rust::{}", callee.clean_name),
            params: callee.params.clone(),
            result: callee.result.clone(),
        })
        .collect::<Vec<_>>();
    let environment = Arc::new(session.environment().unwrap().clone());
    let plan = trust_clean_origin::plan_clean_origin_body_with_rust_callees(
        &environment,
        "bridge",
        &roster,
    )
    .unwrap();
    let source = RetainedRustCallSource::retain(environment, Arc::new(plan));
    let mut builder = trust_ir_build::ModuleBuilder::new("shared-call-results");
    for callee in &declared {
        let ty = builder.add_func_type(vec![Ty::U64; callee.params.len()], vec![Ty::U64]);
        let mut function = builder.function(&callee.clean_name, ty);
        let entry = function.create_block();
        let parameters = (0..callee.params.len())
            .map(|_| function.add_block_param(entry, Ty::U64))
            .collect::<Vec<_>>();
        function.switch_to_block(entry);
        function.ret(vec![parameters[0]]);
        function.build();
    }
    let ty = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut module = builder.build().unwrap();
    for function in &mut module.functions {
        function.producer = Some(Producer::TRust);
        function.calling_conv = CallingConv::Rust;
    }
    let mut root = Function::new(FuncId::new(2), "bridge", ty, BlockId::new(0));
    root.producer = Some(Producer::Clean);
    root.calling_conv = CallingConv::Rust;
    let mut block = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::U64);
    block.body = vec![
        node(Inst::Call { callee: FuncId::new(0), args: vec![ValueId::new(0)] }, &[1]),
        node(
            Inst::Call { callee: FuncId::new(1), args: vec![ValueId::new(1), ValueId::new(1)] },
            &[2],
        ),
        node(Inst::Return { values: vec![ValueId::new(2)] }, &[]),
    ];
    root.blocks.push(block);
    module.functions.push(root);
    assert!(trust_ir_build::validate_module(&module).is_empty());
    (
        source,
        module,
        vec![
            RustCallBinding { plan_index: 0, function: FuncId::new(0) },
            RustCallBinding { plan_index: 1, function: FuncId::new(1) },
        ],
    )
}

#[test]
fn shared_source_let_uses_one_physical_call_and_reuses_its_result() {
    let (source, module, bindings) = binary_call_fixture("let y := g x; h y y");
    source.check_module_call_trace(&module, FuncId::new(2), &bindings).unwrap();
}

#[test]
fn duplicated_call_can_match_the_kernel_model_but_not_the_source_trace() {
    let (source, mut module, bindings) = binary_call_fixture("let y := g x; h y y");
    module.functions[2].blocks[0].body = vec![
        node(Inst::Call { callee: FuncId::new(0), args: vec![ValueId::new(0)] }, &[1]),
        node(Inst::Call { callee: FuncId::new(0), args: vec![ValueId::new(0)] }, &[2]),
        node(
            Inst::Call { callee: FuncId::new(1), args: vec![ValueId::new(1), ValueId::new(2)] },
            &[3],
        ),
        node(Inst::Return { values: vec![ValueId::new(3)] }, &[]),
    ];
    source.check_module_model(&module, FuncId::new(2), &bindings).unwrap();
    assert!(source.check_module_call_trace(&module, FuncId::new(2), &bindings).is_err());
}

#[test]
fn equal_model_calls_still_bind_each_actual_source_result_to_its_own_ordinal() {
    let (source, mut module, bindings) = binary_call_fixture("let y := g x; let z := g x; h y z");
    module.functions[2].blocks[0].body = vec![
        node(Inst::Call { callee: FuncId::new(0), args: vec![ValueId::new(0)] }, &[1]),
        node(Inst::Call { callee: FuncId::new(0), args: vec![ValueId::new(0)] }, &[2]),
        node(
            Inst::Call { callee: FuncId::new(1), args: vec![ValueId::new(2), ValueId::new(1)] },
            &[3],
        ),
        node(Inst::Return { values: vec![ValueId::new(3)] }, &[]),
    ];
    source.check_module_model(&module, FuncId::new(2), &bindings).unwrap();
    assert!(source.check_module_call_trace(&module, FuncId::new(2), &bindings).is_err());
    if let Inst::Call { args, .. } = &mut module.functions[2].blocks[0].body[2].inst {
        args.swap(0, 1);
    }
    source.check_module_call_trace(&module, FuncId::new(2), &bindings).unwrap();
}

#[test]
fn an_unused_source_let_keeps_its_physical_call() {
    let source = retained_source("let y := f x; f (g x)");
    let (mut module, bindings) = retained_module();
    module.functions[2].blocks[0]
        .body
        .insert(0, node(Inst::Call { callee: FuncId::new(0), args: vec![ValueId::new(0)] }, &[3]));
    source.check_module_call_trace(&module, FuncId::new(2), &bindings).unwrap();
}

#[test]
fn retained_source_kernel_checks_opaque_calls_without_identifying_distinct_callees() {
    let source = retained_source("f (g x)");
    let (mut module, bindings) = retained_module();
    source.check_module_model(&module, FuncId::new(2), &bindings).unwrap();
    source.check_module_call_trace(&module, FuncId::new(2), &bindings).unwrap();
    // Both registered constants have type-correct hidden inhabitants. The
    // kernel comparison must still distinguish f(g x) from g(f x).
    if let Inst::Call { callee, .. } = &mut module.functions[2].blocks[0].body[0].inst {
        *callee = FuncId::new(0);
    }
    if let Inst::Call { callee, .. } = &mut module.functions[2].blocks[0].body[1].inst {
        *callee = FuncId::new(1);
    }
    assert!(source.check_module_model(&module, FuncId::new(2), &bindings).is_err());
}

#[test]
fn retained_snapshot_is_not_replaced_by_a_later_source_environment() {
    let first = retained_source("f (g x)");
    let retained = first.clone();
    let later = retained_source("g (f x)");
    assert_ne!(retained.environment_binding().unwrap(), later.environment_binding().unwrap());
    let (module, bindings) = retained_module();
    retained.check_module_model(&module, FuncId::new(2), &bindings).unwrap();
    assert!(later.check_module_model(&module, FuncId::new(2), &bindings).is_err());
}

#[test]
fn retained_model_refuses_incomplete_repeated_or_wrong_source_roster_bindings() {
    let source = retained_source("f (g x)");
    let (module, bindings) = retained_module();
    assert!(source.check_module_model(&module, FuncId::new(2), &bindings[..1]).is_err());
    let repeated = [bindings[0], bindings[0]];
    assert!(source.check_module_model(&module, FuncId::new(2), &repeated).is_err());
    let wrong = [
        RustCallBinding { plan_index: 0, function: FuncId::new(1) },
        RustCallBinding { plan_index: 1, function: FuncId::new(0) },
    ];
    assert!(source.check_module_model(&module, FuncId::new(2), &wrong).is_err());
}

#[test]
fn retained_model_rejects_a_mixed_plan_and_environment_even_when_the_module_matches() {
    let (_, first_plan) = retained_parts("f (g x)");
    let (later_environment, later_plan) = retained_parts("g (f x)");
    let mismatched = RetainedRustCallSource::retain(later_environment.clone(), first_plan);
    let matching = RetainedRustCallSource::retain(later_environment, later_plan);
    let (mut module, bindings) = retained_module();
    if let Inst::Call { callee, .. } = &mut module.functions[2].blocks[0].body[0].inst {
        *callee = FuncId::new(0);
    }
    if let Inst::Call { callee, .. } = &mut module.functions[2].blocks[0].body[1].inst {
        *callee = FuncId::new(1);
    }
    matching.check_module_model(&module, FuncId::new(2), &bindings).unwrap();
    assert!(mismatched.check_module_model(&module, FuncId::new(2), &bindings).is_err());
}

#[test]
fn kernel_model_equality_does_not_supply_source_call_trace_tv() {
    let source = retained_source("let y := f x; g x");
    let (mut module, mut bindings) = retained_module();
    module.functions[2].blocks[0].body = vec![
        node(Inst::Call { callee: FuncId::new(1), args: vec![ValueId::new(0)] }, &[1]),
        node(Inst::Return { values: vec![ValueId::new(1)] }, &[]),
    ];
    let trust_clean_origin::CleanOriginShape::RustCallChain { nodes } = source.plan().shape()
    else {
        panic!("fixture must retain a Rust-call model");
    };
    bindings.retain(|binding| nodes.iter().any(|node| node.callee == binding.plan_index));
    // The source explicitly binds f(x), but the IR has only g(x). Pure CIC
    // model equality can accept this: it supplies no once-evaluation, effects,
    // actual Rust purity/totality or source call-trace TV evidence.
    source.check_module_model(&module, FuncId::new(2), &bindings).unwrap();
    assert!(source.check_module_call_trace(&module, FuncId::new(2), &bindings).is_err());
    assert_eq!(
        module.functions[2].blocks[0]
            .body
            .iter()
            .filter(|node| matches!(node.inst, Inst::Call { .. }))
            .count(),
        1
    );
}

#[test]
fn source_trace_preserves_a_live_let_call_without_zeta_duplication() {
    let source = retained_source("let y := g x; f y");
    let (module, bindings) = retained_module();
    source.check_module_call_trace(&module, FuncId::new(2), &bindings).unwrap();
}

#[test]
fn source_trace_rejects_erased_let_calls_even_when_every_callee_is_still_used() {
    let (mut module, bindings) = retained_module();
    // Both source declarations are model-equal to the existing f(g x), but
    // each evaluates one additional call before evaluating that composition.
    for body in ["let y := f x; f (g x)", "let y := g x; f (g x)"] {
        let source = retained_source(body);
        source.check_module_model(&module, FuncId::new(2), &bindings).unwrap();
        assert!(source.check_module_call_trace(&module, FuncId::new(2), &bindings).is_err());
    }
    // The independent check also runs the existing kernel/module check first;
    // a matching source trace cannot bless a changed module-owned callee type.
    module.func_types[0].params[0] = Ty::U32;
    assert!(
        retained_source("f (g x)")
            .check_module_call_trace(&module, FuncId::new(2), &bindings)
            .is_err()
    );
}

#[test]
fn source_trace_reads_exact_literals_and_return_dataflow() {
    let source = retained_source("f (g 7)");
    let (mut module, bindings) = retained_module();
    module.functions[2].blocks[0]
        .body
        .insert(0, node(Inst::Const { ty: Ty::U64, value: Constant::Int(7) }, &[3]));
    if let Inst::Call { args, .. } = &mut module.functions[2].blocks[0].body[1].inst {
        args[0] = ValueId::new(3);
    }
    source.check_module_call_trace(&module, FuncId::new(2), &bindings).unwrap();
    if let Inst::Const { value, .. } = &mut module.functions[2].blocks[0].body[0].inst {
        *value = Constant::Int(8);
    }
    assert!(source.check_module_call_trace(&module, FuncId::new(2), &bindings).is_err());
}

#[test]
fn module_reader_uses_the_actual_root_type_and_rejects_invalid_context() {
    let (module, interpretations) = module_fixture();
    let root = FuncId::new(1);
    let _candidate = reflect_module_candidate(&module, root, &interpretations).unwrap();
    let original_signature = module.func_types[0].clone();
    let mut changed = module.clone();
    changed.func_types.push(FuncTy::unrecorded(vec![Ty::U32], vec![Ty::U32], false));
    changed.functions[1].ty = FuncTyId::new(1);
    // The isolated Function reader can still consume the separately supplied
    // old signature; only actual-module binding catches its real type entry.
    let _unbound =
        reflect_candidate(&original_signature, &changed.functions[1], &interpretations).unwrap();
    assert!(reflect_module_candidate(&changed, root, &interpretations).is_err());
    changed.functions[1].ty = FuncTyId::new(99);
    assert!(reflect_module_candidate(&changed, root, &interpretations).is_err());
    assert!(reflect_module_candidate(&module, FuncId::new(99), &interpretations).is_err());
    let mut changed = module.clone();
    let mut unrelated = changed.functions[0].clone();
    unrelated.id = FuncId::new(2);
    unrelated.name = "unrelated_bad_type".into();
    unrelated.ty = FuncTyId::new(99);
    changed.functions.push(unrelated);
    assert!(reflect_module_candidate(&changed, root, &interpretations).is_err());
}

#[test]
fn module_reader_requires_defined_rust_callees_and_actual_signatures() {
    for mutation in 0..7 {
        let (mut module, mut interpretations) = module_fixture();
        match mutation {
            0 => module.functions[0].blocks.clear(),
            1 => module.functions[0].calling_conv = CallingConv::C,
            2 => module.functions[0].producer = Some(Producer::Clean),
            3 => module.functions[0].producer = None,
            4 => interpretations[0].signature.params[0] = Ty::U32,
            5 => module.functions[1].producer = Some(Producer::TRust),
            _ => module.functions[1].blocks.clear(),
        }
        assert!(
            reflect_module_candidate(&module, FuncId::new(1), &interpretations).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn module_reader_accepts_a_valid_distinct_nonzero_root_type_slot() {
    let (mut module, mut interpretations) = module_fixture();
    let distinct = FuncTy::unrecorded(vec![Ty::U32], vec![Ty::U32], false);
    module.func_types.push(distinct.clone());
    for function in &mut module.functions {
        function.ty = FuncTyId::new(1);
        function.blocks[0].params[0].1 = Ty::U32;
    }
    interpretations[0].signature = distinct;
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let _candidate = reflect_module_candidate(&module, FuncId::new(1), &interpretations).unwrap();
    // A hardcoded func_types[0] would use UInt64 for this valid UInt32 root.
    assert!(
        reflect_candidate(&module.func_types[0], &module.functions[1], &interpretations).is_err()
    );
}

#[test]
fn module_reader_checks_abi_metadata_even_when_all_carriers_match() {
    use trust_ir::signature_abi::{
        AbiArgument, AbiAttributes, AbiBinding, AbiBindingPlace, AbiFrontend, AbiPassMode,
        AbiRegister, AbiRegisterClass, AbiScalar, AbiTarget, SignatureAbi,
    };
    fn argument(place: AbiBindingPlace) -> AbiArgument {
        AbiArgument {
            size: 8,
            align: 8,
            mode: AbiPassMode::Direct(AbiScalar {
                register: AbiRegister { class: AbiRegisterClass::Integer, bytes: 8 },
                source_offset: 0,
                source_bytes: 8,
                value_bits: 64,
                attributes: AbiAttributes::default(),
            }),
            bindings: vec![AbiBinding {
                place,
                source_offset: 0,
                source_bytes: 8,
                carrier_offset: 0,
                carrier_bytes: 8,
            }],
        }
    }
    let (module, mut interpretations) = module_fixture();
    let placement = SignatureAbi {
        target: AbiTarget {
            triple: "aarch64-apple-darwin".into(),
            data_layout: "e-m:o-i64:64-i128:128-n32:64-S128".into(),
            abi: "darwinpcs".into(),
            cpu: "generic".into(),
            features: vec![],
            target_spec: "c".repeat(64),
            pointer_bytes: 8,
            little_endian: true,
        },
        frontend: AbiFrontend { name: "Trust".into(), revision: "fixture".into() },
        convention: "Rust".into(),
        lowered_convention: CallingConv::Rust,
        source_abi: "Rust".into(),
        can_unwind: false,
        variadic: false,
        fixed_count: 1,
        arguments: vec![argument(AbiBindingPlace::Parameter(0))],
        result: argument(AbiBindingPlace::Result(0)),
    };
    placement.validate(&interpretations[0].signature).unwrap();
    placement.validate_encoding_limits().unwrap();
    interpretations[0].signature.abi = Some(placement);
    let root = &module.functions[1];
    let _unbound = reflect_candidate(&module.func_types[0], root, &interpretations).unwrap();
    assert!(reflect_module_candidate(&module, root.id, &interpretations).is_err());
}

#[test]
fn actual_call_ssa_kernel_checks_against_source_and_changed_target_does_not() {
    let mut session = CleanIslandSession::new();
    for source in [
        "def double (x : UInt64) : UInt64 := x + x",
        "def identity (x : UInt64) : UInt64 := x",
        "def chain (x : UInt64) : UInt64 := double (double x)",
    ] {
        assert!(!session.check(source).is_rejected());
    }
    let env = session.environment().unwrap();
    let plan = plan_clean_origin_body(env, "chain").unwrap();
    let (signature, function, mut callees) = fixture();
    let reflected = reflect_candidate(&signature, &function, &callees).unwrap();
    let mut scratch = env.clone();
    scratch
        .add_decl(Declaration::Definition {
            name: Name::from_string("checkedReflection"),
            level_params: vec![],
            type_: clean_kernel::Expr::arrow(
                clean_kernel::Expr::const_(Name::from_string("UInt64"), vec![]),
                clean_kernel::Expr::const_(Name::from_string("UInt64"), vec![]),
            ),
            value: reflected.clone(),
            is_reducible: true,
        })
        .expect("independent kernel typecheck of the entire reflected lambda");
    check_faithful(env, "chain", &reflected, plan.result_carrier()).unwrap();
    callees.push(CalleeInterpretation {
        id: FuncId::new(8),
        name: Name::from_string("identity"),
        signature: signature.clone(),
    });
    let mut changed = function.clone();
    if let Inst::Call { callee, .. } = &mut changed.blocks[0].body[1].inst {
        *callee = FuncId::new(8);
    }
    let wrong = reflect_candidate(&signature, &changed, &callees).unwrap();
    assert!(check_faithful(env, "chain", &wrong, plan.result_carrier()).is_err());
}

#[test]
fn missing_or_ambiguous_targets_and_wrong_carriers_refuse() {
    let (signature, function, mut callees) = fixture();
    assert!(reflect_candidate(&signature, &function, &[]).is_err());
    let mut missing = function.clone();
    if let Inst::Call { callee, .. } = &mut missing.blocks[0].body[0].inst {
        *callee = FuncId::new(99);
    }
    assert!(reflect_candidate(&signature, &missing, &callees).is_err());
    callees[0].signature.params[0] = Ty::U32;
    assert!(reflect_candidate(&signature, &function, &callees).is_err());
    callees[0].signature = signature.clone();
    callees.push(CalleeInterpretation {
        id: FuncId::new(8),
        name: Name::from_string("double"),
        signature: signature.clone(),
    });
    assert!(reflect_candidate(&signature, &function, &callees).is_err());
    callees[1].id = FuncId::new(7);
    callees[1].name = Name::from_string("another");
    assert!(reflect_candidate(&signature, &function, &callees).is_err());
}

#[test]
fn dead_calls_forward_references_duplicate_ssa_and_post_return_effects_refuse() {
    // A model can normalize away a dead call, but the source trace must reject
    // that extra evaluation when it is absent from the original declaration.
    let source = retained_source("f (g x)");
    let (mut module, bindings) = retained_module();
    module.functions[2].blocks[0]
        .body
        .insert(0, node(Inst::Call { callee: FuncId::new(0), args: vec![ValueId::new(0)] }, &[3]));
    source.check_module_model(&module, FuncId::new(2), &bindings).unwrap();
    assert!(source.check_module_call_trace(&module, FuncId::new(2), &bindings).is_err());
    for mutation in 1..5 {
        let (signature, mut function, callees) = fixture();
        let body = &mut function.blocks[0].body;
        match mutation {
            1 => body[0] = call(&[2], 1),
            2 => body[0] = call(&[0], 0),
            3 => body.push(call(&[0], 3)),
            _ => body.insert(0, node(Inst::Undef { ty: Ty::U64 }, &[3])),
        }
        assert!(reflect_candidate(&signature, &function, &callees).is_err(), "mutation {mutation}");
    }
}

#[test]
fn application_argument_order_cannot_reverse_executed_calls() {
    fn values(term: &Expr) -> Vec<Expr> {
        let ExprKind::Lam(_, _, mut body) = term.kind().clone() else {
            panic!("closed one-parameter fixture");
        };
        let mut values = Vec::new();
        while let ExprKind::Let(_, _, value, inner, _) = body.kind() {
            values.push(value.as_ref().clone());
            body = inner.clone();
        }
        values
    }
    let (signature, mut function, mut callees) = fixture();
    callees.push(CalleeInterpretation {
        id: FuncId::new(8),
        name: Name::from_string("join"),
        signature: FuncTy::unrecorded(vec![Ty::U64, Ty::U64], vec![Ty::U64], false),
    });
    function.blocks[0].body = vec![
        call(&[0], 1),
        call(&[0], 2),
        node(
            Inst::Call { callee: FuncId::new(8), args: vec![ValueId::new(2), ValueId::new(1)] },
            &[3],
        ),
        node(Inst::Return { values: vec![ValueId::new(3)] }, &[]),
    ];
    let lets = values(&reflect_candidate(&signature, &function, &callees).unwrap());
    assert_eq!(
        lets,
        vec![
            Expr::app(Expr::const_str("double"), Expr::bvar(0)),
            Expr::app(Expr::const_str("double"), Expr::bvar(1)),
            Expr::apps(Expr::const_str("join"), [Expr::bvar(0), Expr::bvar(1)]),
        ]
    );
    if let Inst::Call { args, .. } = &mut function.blocks[0].body[2].inst {
        args.swap(0, 1);
    }
    let lets = values(&reflect_candidate(&signature, &function, &callees).unwrap());
    assert_eq!(lets[2], Expr::apps(Expr::const_str("join"), [Expr::bvar(1), Expr::bvar(0)]));
    if let Inst::Call { args, .. } = &mut function.blocks[0].body[2].inst {
        args[1] = args[0];
    }
    let lets = values(&reflect_candidate(&signature, &function, &callees).unwrap());
    assert_eq!(lets[2], Expr::apps(Expr::const_str("join"), [Expr::bvar(1), Expr::bvar(1)]));
}

#[test]
fn literals_are_read_from_ir_and_range_checked() {
    let (mut signature, mut function, mut callees) = fixture();
    signature.params = vec![Ty::U8];
    signature.returns = vec![Ty::U8];
    callees[0].signature = signature.clone();
    function.blocks[0].params[0].1 = Ty::U8;
    function.blocks[0].body = vec![
        node(Inst::Const { ty: Ty::U8, value: Constant::Int(255) }, &[1]),
        call(&[1], 2),
        node(Inst::Return { values: vec![ValueId::new(2)] }, &[]),
    ];
    let _candidate = reflect_candidate(&signature, &function, &callees).unwrap();
    for value in [-1, 256] {
        function.blocks[0].body[0].inst = Inst::Const { ty: Ty::U8, value: Constant::Int(value) };
        assert!(reflect_candidate(&signature, &function, &callees).is_err());
    }
}

#[test]
fn return_carrier_is_checked_independently_of_call_operands() {
    let (mut signature, function, callees) = fixture();
    signature.returns[0] = Ty::U32;
    assert!(reflect_candidate(&signature, &function, &callees).is_err());
}

#[test]
fn signatures_interpretations_names_and_total_applications_are_bounded() {
    let (mut signature, function, mut callees) = fixture();
    signature.params = vec![Ty::U64; 65];
    let mut many_parameters = function.clone();
    many_parameters.blocks[0].params = std::iter::once((ValueId::new(0), Ty::U64))
        .chain((100..164).map(|id| (ValueId::new(id), Ty::U64)))
        .collect();
    assert!(reflect_candidate(&signature, &many_parameters, &callees).is_err());
    signature.params = vec![Ty::U64];
    // Keep the USED callee valid: only the unused interpretation's signature
    // exceeds the cap, so an arity mismatch cannot supply this refusal.
    callees.push(CalleeInterpretation {
        id: FuncId::new(8),
        name: Name::from_string("unused"),
        signature: FuncTy::unrecorded(vec![Ty::U64; 65], vec![Ty::U64], false),
    });
    assert!(reflect_candidate(&signature, &function, &callees).is_err());
    callees.pop();
    let mut too_many_arguments = function.clone();
    too_many_arguments.blocks[0].body[0] = call(&vec![0; 257], 1);
    assert!(reflect_candidate(&signature, &too_many_arguments, &callees).is_err());
    callees[0].name = Name::anon().str("x".repeat(4097));
    assert!(reflect_candidate(&signature, &function, &callees).is_err());
    callees[0].name = (0..65).fold(Name::anon(), |name, _| name.str("x"));
    assert!(reflect_candidate(&signature, &function, &callees).is_err());
    let roster = (0..33)
        .map(|id| CalleeInterpretation {
            id: FuncId::new(id),
            name: Name::from_string(&format!("f{id}")),
            signature: signature.clone(),
        })
        .collect::<Vec<_>>();
    assert!(reflect_candidate(&signature, &function, &roster).is_err());

    // A valid, once-used, ordered chain crosses only the TOTAL application
    // budget: each call has 64 legal arguments, and there are only five calls.
    callees[0].name = Name::from_string("manyArguments");
    callees[0].signature.params = vec![Ty::U64; 64];
    let mut large = function.clone();
    large.blocks[0].body.clear();
    for result in 1..=5 {
        let mut args = vec![0; 64];
        args[0] = result - 1;
        large.blocks[0].body.push(call(&args, result));
    }
    large.blocks[0].body.push(node(Inst::Return { values: vec![ValueId::new(5)] }, &[]));
    assert!(reflect_candidate(&signature, &large, &callees).is_err());
    large.blocks[0].body.truncate(4);
    large.blocks[0].body.push(node(Inst::Return { values: vec![ValueId::new(4)] }, &[]));
    let _at_limit = reflect_candidate(&signature, &large, &callees).unwrap();
}

#[test]
fn bool_literal_and_other_uint_carriers_kernel_check() {
    for (name, ty) in [("UInt16", Ty::U16), ("UInt32", Ty::U32), ("Bool", Ty::Bool)] {
        let mut session = CleanIslandSession::new();
        let is_bool = ty == Ty::Bool;
        let declaration = if is_bool {
            "def step (x y : Bool) : Bool := x".to_string()
        } else {
            format!("def step (x : {name}) : {name} := x + x")
        };
        assert!(!session.check(&declaration).is_rejected());
        let source = if is_bool {
            "def chain (x : Bool) : Bool := step x true".to_string()
        } else {
            format!("def chain (x : {name}) : {name} := step (step x)")
        };
        assert!(!session.check(&source).is_rejected());
        let env = session.environment().unwrap();
        let plan = plan_clean_origin_body(env, "chain").unwrap();
        let (mut signature, mut function, mut callees) = fixture();
        signature.params[0] = ty.clone();
        signature.returns[0] = ty.clone();
        function.blocks[0].params[0].1 = ty.clone();
        callees[0].name = Name::from_string("step");
        callees[0].signature = signature.clone();
        if is_bool {
            callees[0].signature.params.push(Ty::Bool);
            function.blocks[0].body = vec![
                node(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) }, &[1]),
                call(&[0, 1], 2),
                node(Inst::Return { values: vec![ValueId::new(2)] }, &[]),
            ];
        }
        let term = reflect_candidate(&signature, &function, &callees).unwrap();
        let carrier = clean_kernel::Expr::const_(Name::from_string(name), vec![]);
        let mut scratch = env.clone();
        scratch
            .add_decl(Declaration::Definition {
                name: Name::from_string("checkedReflection"),
                level_params: vec![],
                type_: clean_kernel::Expr::arrow(carrier.clone(), carrier),
                value: term.clone(),
                is_reducible: true,
            })
            .unwrap();
        check_faithful(env, "chain", &term, plan.result_carrier()).unwrap();
    }
}

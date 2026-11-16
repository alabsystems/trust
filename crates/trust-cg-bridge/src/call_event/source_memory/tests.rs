use ay::{Logic, Solver};
use trust_ir::{
    Block, BodyGate, ClosureLayoutDescriptor, ClosureTy, ClosureTyId, FuncTy, Function, InstrNode,
    TargetInfo,
};

use super::*;

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn f(n: u32) -> FuncId {
    FuncId::new(n)
}
fn node(inst: Inst, result: u32) -> InstrNode {
    InstrNode::new(inst).with_result(v(result))
}
fn constant(n: i128, result: u32, ty: IrTy) -> InstrNode {
    node(Inst::Const { ty, value: Constant::Int(n) }, result)
}
fn ret(value: u32) -> InstrNode {
    InstrNode::new(Inst::Return { values: vec![v(value)] })
}
fn store(ptr: u32, value: u32) -> InstrNode {
    InstrNode::new(Inst::Store {
        ty: IrTy::U8,
        ptr: v(ptr),
        value: v(value),
        volatile: false,
        align: Some(1),
    })
}
fn load(ptr: u32, result: u32) -> InstrNode {
    node(Inst::Load { ty: IrTy::U8, ptr: v(ptr), volatile: false, align: Some(1) }, result)
}
fn scalar(reg: u8, bits: u32) -> ParamPlace {
    ParamPlace::Scalar(ScalarPlace::gpr(reg, bits))
}
fn placement(params: Vec<ParamPlace>) -> FnPlacement {
    FnPlacement { params, ret: ReturnPlace::Scalar(ScalarPlace::gpr(0, 8)) }
}
fn module(params: Vec<IrTy>, blocks: Vec<Block>) -> Module {
    let mut m = Module::new("source_memory");
    m.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    });
    let sig = m
        .add_func_type(FuncTy { params, returns: vec![IrTy::U8], is_vararg: false, abi: None })
        .unwrap();
    let mut function = Function::new(f(0), "memory_fn", sig, BlockId::new(0));
    function.producer = Some(trust_ir::Producer::TRust);
    function.calling_conv = CallingConv::Rust;
    function.body_gate =
        Some(BodyGate::Gated { authority: "trust-direct-lane-structural".into(), evidence: None });
    function.blocks = blocks;
    m.functions.push(function);
    m
}
fn evaluate(
    m: &Module,
    place: &FnPlacement,
    decisions: &BTreeMap<SiteKey, SiteDecision>,
) -> Result<SpecResult, String> {
    let bodies = BTreeMap::new();
    let places = BTreeMap::new();
    let input = CerInput {
        m_cg: m,
        producers: &[],
        bodies: &bodies,
        placements: &places,
        object: &[],
        relocation_model: RelocationModel::Static,
    };
    let function = &m.functions[0];
    let sig = signature_of(m, function.ty)?;
    check_placement(m, &sig, function.calling_conv, place, true).map_err(|e| format!("{e:?}"))?;
    eval_spec(&input, m, function, &sig, place, decisions)
}
fn valid(formula: Formula, expected: bool) {
    // Diagnostic AY only; no kernel proof or shipping authority.
    let mut solver = Solver::try_new(Logic::QfAbv).unwrap();
    let term = crate::verify_output::formula_to_term(&mut solver, &formula).unwrap();
    let neg = solver.try_not(term).unwrap();
    solver.try_assert_term(neg).unwrap();
    let result = solver.check_sat();
    assert!(if expected { result.is_unsat() } else { result.is_sat() }, "{result:?}");
}
fn equal(a: Formula, c: Formula) -> Formula {
    Formula::Eq(b(a), b(c))
}
fn byte(n: i128) -> Formula {
    Formula::BitVec { value: n, width: 8 }
}
fn address(n: i128) -> Formula {
    Formula::BitVec { value: n, width: 64 }
}
fn write_module() -> Module {
    let mut block =
        Block::new(BlockId::new(0)).with_param(v(0), IrTy::Ptr).with_param(v(1), IrTy::U8);
    block.body = vec![store(0, 1), constant(0, 2, IrTy::U8), ret(2)];
    module(vec![IrTy::Ptr, IrTy::U8], vec![block])
}

#[test]
fn real_ir_store_is_retained_when_return_is_constant_and_dead_load_is_counted() {
    let mut m = write_module();
    m.functions[0].blocks[0].body.insert(1, load(0, 3));
    let spec =
        evaluate(&m, &placement(vec![scalar(0, 64), scalar(1, 8)]), &BTreeMap::new()).unwrap();
    assert_eq!(spec.value, byte(0));
    assert_eq!(spec.memory.accesses.len(), 2, "dead loads still contribute coverage");
    assert_eq!(spec.memory.accesses[0].site, (0, 0));
    assert_eq!(spec.memory.accesses[0].origin.argument, 0);
    assert_eq!(spec.memory.exits.len(), 1);
    let expected = crate::cer_memory::store_le(
        spec.memory.entry.clone(),
        &xn(0),
        &read_slot_spec(&ScalarPlace::gpr(1, 8)).unwrap(),
        1,
    )
    .unwrap();
    valid(equal(spec.memory.exits[0].bytes.clone(), expected), true);
    assert!(spec.memory.missing_integration().unwrap().contains("M3"));
}

#[test]
fn constant_byte_gep_and_pointer_copy_preserve_argument_origin_and_loaded_value() {
    let mut block =
        Block::new(BlockId::new(0)).with_param(v(0), IrTy::Ptr).with_param(v(1), IrTy::U8);
    block.body = vec![
        constant(3, 2, IrTy::Usize),
        node(
            Inst::GEP { pointee_ty: IrTy::U8, base: v(0), indices: vec![v(2)], inbounds: false },
            3,
        ),
        node(Inst::Copy { ty: IrTy::Ptr, operand: v(3) }, 4),
        store(4, 1),
        load(4, 5),
        ret(5),
    ];
    let m = module(vec![IrTy::Ptr, IrTy::U8], vec![block]);
    let spec =
        evaluate(&m, &placement(vec![scalar(0, 64), scalar(1, 8)]), &BTreeMap::new()).unwrap();
    assert_eq!(spec.memory.accesses[0].origin.byte_offset, 3);
    assert_eq!(spec.memory.accesses[0].origin.argument, 0);
    valid(equal(spec.value, read_slot_spec(&ScalarPlace::gpr(1, 8)).unwrap()), true);
}

#[test]
fn multibyte_integer_stores_and_loads_keep_exact_little_endian_bits() {
    for (ty, bits) in [(IrTy::U8, 8), (IrTy::I16, 16), (IrTy::U32, 32), (IrTy::I64, 64)] {
        let mut block =
            Block::new(BlockId::new(0)).with_param(v(0), IrTy::Ptr).with_param(v(1), ty.clone());
        block.body = vec![
            InstrNode::new(Inst::Store {
                ty: ty.clone(),
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: Some(1),
            }),
            node(Inst::Load { ty: ty.clone(), ptr: v(0), volatile: false, align: Some(1) }, 2),
            ret(2),
        ];
        let mut m = module(vec![IrTy::Ptr, ty.clone()], vec![block]);
        m.func_types[0].returns = vec![ty];
        let place = FnPlacement {
            params: vec![scalar(0, 64), scalar(1, bits)],
            ret: ReturnPlace::Scalar(ScalarPlace::gpr(0, bits)),
        };
        let spec = evaluate(&m, &place, &BTreeMap::new()).unwrap();
        valid(equal(spec.value, read_slot_spec(&ScalarPlace::gpr(1, bits)).unwrap()), true);
        assert_eq!(spec.memory.accesses.len(), 2);
        assert!(spec.memory.missing_integration().is_some());
    }
}

#[test]
fn branch_memory_is_path_local_and_pointer_block_arguments_keep_their_root() {
    let mut entry =
        Block::new(BlockId::new(0)).with_param(v(0), IrTy::Ptr).with_param(v(1), IrTy::U8);
    entry.body = vec![InstrNode::new(Inst::CondBr {
        cond: v(1),
        then_target: BlockId::new(1),
        then_args: vec![v(0)],
        else_target: BlockId::new(2),
        else_args: vec![v(0)],
    })];
    let mut yes = Block::new(BlockId::new(1)).with_param(v(2), IrTy::Ptr);
    yes.body = vec![constant(1, 3, IrTy::U8), store(2, 3), ret(3)];
    let mut no = Block::new(BlockId::new(2)).with_param(v(4), IrTy::Ptr);
    no.body = vec![constant(2, 5, IrTy::U8), store(4, 5), ret(5)];
    let m = module(vec![IrTy::Ptr, IrTy::U8], vec![entry, yes, no]);
    let spec =
        evaluate(&m, &placement(vec![scalar(0, 64), scalar(1, 8)]), &BTreeMap::new()).unwrap();
    assert_eq!(spec.memory.accesses.len(), 2);
    assert_eq!(spec.memory.exits.len(), 2);
    for (exit, value) in spec.memory.exits.iter().zip([1, 2]) {
        let expected =
            crate::cer_memory::store_le(spec.memory.entry.clone(), &xn(0), &byte(value), 1)
                .unwrap();
        valid(equal(exit.bytes.clone(), expected), true);
    }
    valid(
        Formula::Not(b(Formula::And(spec.memory.exits.iter().map(|e| e.path.clone()).collect()))),
        true,
    );
    assert!(spec.memory.accesses.iter().all(|a| a.origin.argument == 0));
}

#[test]
fn pointer_join_from_different_arguments_refuses_the_indirect_root() {
    let mut entry = Block::new(BlockId::new(0))
        .with_param(v(0), IrTy::Ptr)
        .with_param(v(1), IrTy::Ptr)
        .with_param(v(2), IrTy::U8);
    entry.body = vec![InstrNode::new(Inst::CondBr {
        cond: v(2),
        then_target: BlockId::new(1),
        then_args: vec![v(0)],
        else_target: BlockId::new(1),
        else_args: vec![v(1)],
    })];
    let mut join = Block::new(BlockId::new(1)).with_param(v(3), IrTy::Ptr);
    join.body = vec![load(3, 4), ret(4)];
    let m = module(vec![IrTy::Ptr, IrTy::Ptr, IrTy::U8], vec![entry, join]);
    let error = evaluate(
        &m,
        &placement(vec![scalar(0, 64), scalar(1, 64), scalar(2, 8)]),
        &BTreeMap::new(),
    )
    .err()
    .unwrap();
    assert!(error.contains("independently computed Arg root"), "{error}");
}

#[test]
fn two_capture_pointers_keep_nominal_field_identity_without_noalias() {
    let mut block =
        Block::new(BlockId::new(0)).with_param(v(0), IrTy::Closure(ClosureTyId::new(0)));
    block.body = vec![
        node(Inst::ExtractField { ty: IrTy::Ptr, aggregate: v(0), field: 0 }, 1),
        node(Inst::ExtractField { ty: IrTy::Ptr, aggregate: v(0), field: 1 }, 2),
        constant(1, 3, IrTy::U8),
        store(1, 3),
        store(2, 3),
        ret(3),
    ];
    let mut m = module(vec![IrTy::Closure(ClosureTyId::new(0))], vec![block]);
    let apparent = m
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![IrTy::U8],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    m.closure_types.push(ClosureTy { func: apparent, captures: vec![IrTy::Ptr, IrTy::Ptr] });
    m.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(0),
        size: 16,
        align: 8,
        capture_offsets: vec![0, 8],
    });
    let spec = evaluate(
        &m,
        &placement(vec![ParamPlace::Pair(ScalarPlace::gpr(0, 64), ScalarPlace::gpr(1, 64))]),
        &BTreeMap::new(),
    )
    .unwrap();
    let origins: Vec<_> = spec.memory.accesses.iter().map(|a| &a.origin).collect();
    assert_eq!(origins[0].argument, origins[1].argument);
    assert_ne!(origins[0].projection, origins[1].projection);
    assert_eq!(
        origins[0].projection,
        Some(Projection::Closure { nominal: ClosureTyId::new(0), field: 0 })
    );
    assert!(spec.side.is_empty(), "capture identity is not a noalias/separation premise");
}

#[test]
fn paired_call_memory_forgets_cached_bytes_but_records_the_required_precall_state() {
    let mut block = Block::new(BlockId::new(0)).with_param(v(0), IrTy::Ptr);
    block.body = vec![
        load(0, 1),
        InstrNode::new(Inst::Call { callee: f(1), args: vec![v(0)] }),
        load(0, 2),
        ret(2),
    ];
    let mut m = module(vec![IrTy::Ptr], vec![block]);
    let sig = m
        .add_func_type(FuncTy {
            params: vec![IrTy::Ptr],
            returns: vec![],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    m.functions.push(Function::new(f(1), "callee", sig, BlockId::new(0)));
    let decisions = BTreeMap::from([(
        (0, 1),
        SiteDecision::Called {
            symbol: "callee".into(),
            place: FnPlacement { params: vec![scalar(0, 64)], ret: ReturnPlace::Void },
            result_width: None,
        },
    )]);
    let spec = evaluate(&m, &placement(vec![scalar(0, 64)]), &decisions).unwrap();
    let call = &spec.memory.calls[&(0, 1)][0];
    assert_eq!(call.before, spec.memory.entry);
    assert_eq!(call.path, Formula::Bool(true));
    assert!(spec.memory.paired_variables(&BTreeMap::new()).is_err());
    let bindings = spec.memory.paired_variables(&BTreeMap::from([((0, 1), 0x44)])).unwrap();
    let after = paired_post_memory(0x44);
    assert_eq!(bindings[&call.after_variable], after);
    let actual = substitute(&spec.value, &bindings);
    let expected = crate::cer_memory::load_le(&after, &xn(0), 1).unwrap();
    valid(equal(actual.clone(), expected), true);
    let stale = crate::cer_memory::load_le(&spec.memory.entry, &xn(0), 1).unwrap();
    valid(equal(actual, stale), false);
    assert!(spec.memory.missing_integration().unwrap().contains("M4/M5"));
}

#[test]
fn volatile_wide_indirect_and_unapproved_geps_remain_refused() {
    let place = placement(vec![scalar(0, 64), scalar(1, 8)]);
    let mut volatile = write_module();
    if let Inst::Store { volatile, .. } = &mut volatile.functions[0].blocks[0].body[0].inst {
        *volatile = true;
    }
    assert!(evaluate(&volatile, &place, &BTreeMap::new()).err().unwrap().contains("volatile"));
    let mut wide = write_module();
    wide.functions[0].blocks[0].body[0] =
        node(Inst::Load { ty: IrTy::U128, ptr: v(0), volatile: false, align: None }, 4);
    assert!(evaluate(&wide, &place, &BTreeMap::new()).is_err());
    let mut indirect = write_module();
    indirect.functions[0].blocks[0].body = vec![
        node(Inst::Load { ty: IrTy::Ptr, ptr: v(0), volatile: false, align: None }, 3),
        load(3, 4),
        ret(4),
    ];
    assert!(evaluate(&indirect, &place, &BTreeMap::new()).err().unwrap().contains("not an entry"));
    for (ty, value) in [(IrTy::U64, 1), (IrTy::U8, -1), (IrTy::U8, i128::from(u64::MAX))] {
        let mut bad = write_module();
        bad.functions[0].blocks[0].body = vec![
            constant(value, 2, IrTy::I64),
            node(Inst::GEP { pointee_ty: ty, base: v(0), indices: vec![v(2)], inbounds: false }, 3),
            load(3, 4),
            ret(4),
        ];
        assert!(evaluate(&bad, &place, &BTreeMap::new()).is_err());
    }
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn compiler_store_has_joint_kernel_proof_and_dropped_store_stays_unknown_without_legal_witness() {
    use trust_machine_sem::{Aarch64Semantics, Effect, MachineState, Semantics};

    use crate::compiled_object::CompiledObject;
    use crate::f1_compile::{
        F1CompileConfig, F1CompileInput, F1OptLevel, F1Target, compile_and_verify_trust_ir_module,
    };
    use crate::verify_output::EmitPolicy;

    let m = write_module();
    let place = placement(vec![scalar(0, 64), scalar(1, 8)]);
    let source = evaluate(&m, &place, &BTreeMap::new()).unwrap();
    let producers = [ProducerModule {
        module: Arc::new(m.clone()),
        symbols: BTreeMap::from([(f(0), "memory_fn".into())]),
    }];
    let bodies = BTreeMap::from([("memory_fn".into(), ProducerBody { producer: 0, func: f(0) })]);
    let placements = BTreeMap::from([("memory_fn".into(), place)]);
    let config = F1CompileConfig {
        force_frame_pointers: false,
        target: F1Target::Aarch64AppleDarwin,
        opt_level: F1OptLevel::O3,
        relocation: RelocationModel::Static,
        never_inline: BTreeSet::new(),
        upstream_mir_lane: false,
    };
    let shipped = compile_and_verify_trust_ir_module(&F1CompileInput {
        m_cg: &m,
        producers: &producers,
        bodies: &bodies,
        placements: &placements,
        policy: EmitPolicy::AllowUnknown,
        config: &config,
    })
    .unwrap();
    let report = &shipped.report;
    if cfg!(feature = "kernel-recheck") {
        assert!(report.certificate("memory_fn").unwrap().is_kernel_proved());
        assert!(report.ships(EmitPolicy::StrictProvenOnly).is_ok());
        assert!(
            report
                .certificate("memory_fn")
                .unwrap()
                .obligations
                .o4_return
                .detail
                .contains("one original-statement kernel conjunction")
        );
    } else {
        assert_eq!(report.certificate("memory_fn").unwrap().grade, "Unknown");
        assert!(report.ships(EmitPolicy::StrictProvenOnly).is_err());
    }
    let parsed = CompiledObject::parse(&shipped.object).unwrap();
    let symbol = parsed.symbols.iter().find(|s| s.name == "memory_fn").unwrap();
    let section = parsed.section(symbol.section.unwrap()).unwrap();
    let code = &section.bytes[symbol.value as usize..];
    let mut good = MachineState::symbolic();
    good.memory = source.memory.entry.clone();
    let mut bad = good.clone();
    let mut removed = 0;
    let mut removed_at = None;
    let mut machine_accesses = Vec::new();
    for (index, word) in code.chunks_exact(4).enumerate() {
        let decoded = trust_disasm::decode_aarch64(word, (index * 4) as u64).unwrap();
        let effects = Aarch64Semantics.effects(&good, &decoded).unwrap();
        let store = effects.iter().any(|effect| matches!(effect, Effect::MemWrite { .. }));
        for effect in &effects {
            let access = match effect {
                Effect::MemWrite { address, width_bytes, .. } => {
                    Some((AccessKind::Write, address, width_bytes))
                }
                Effect::MemRead { address, width_bytes } => {
                    Some((AccessKind::Read, address, width_bytes))
                }
                _ => None,
            };
            if let Some((kind, address, bytes)) = access {
                machine_accesses.push(
                    PathAccess::new(kind, Formula::Bool(true), address.clone(), *bytes).unwrap(),
                );
            }
        }
        good.apply_effects(&effects).unwrap();
        if store {
            removed += 1;
            removed_at = Some(index * 4);
            let nop =
                trust_disasm::decode_aarch64(&0xd503201fu32.to_le_bytes(), (index * 4) as u64)
                    .unwrap();
            bad.apply_effects(&Aarch64Semantics.effects(&bad, &nop).unwrap()).unwrap();
        } else {
            let effects = Aarch64Semantics.effects(&bad, &decoded).unwrap();
            bad.apply_effects(&effects).unwrap();
        }
        if word == 0xd65f03c0u32.to_le_bytes() {
            break;
        }
    }
    assert_eq!(removed, 1, "drop only the compiler's actual store effect");
    assert_eq!(
        machine_accesses.len(),
        1,
        "this leaf fixture has only its actual incoming-byte store"
    );
    let source_accesses: Vec<_> = source.memory.accesses.iter().map(|a| a.term.clone()).collect();
    let coverage = crate::cer_memory::coverage(&source_accesses, &machine_accesses);
    valid(Formula::And(coverage.into_iter().map(|obligation| obligation.formula).collect()), true);
    let section_positions: Vec<_> = shipped
        .object
        .windows(section.bytes.len())
        .enumerate()
        .filter_map(|(index, bytes)| (bytes == section.bytes).then_some(index))
        .collect();
    assert_eq!(section_positions.len(), 1, "bind the mutation to the actual unique text section");
    let offset = section_positions[0] + symbol.value as usize + removed_at.unwrap();
    let mut mutant_object = shipped.object.clone();
    mutant_object[offset..offset + 4].copy_from_slice(&0xd503201fu32.to_le_bytes());
    let mutant_report = verify_compiled_module(&CerInput {
        m_cg: &m,
        producers: &producers,
        bodies: &bodies,
        placements: &placements,
        object: &mutant_object,
        relocation_model: RelocationModel::Static,
    })
    .unwrap();
    assert!(mutant_report.ships(EmitPolicy::StrictProvenOnly).is_err());
    assert_eq!(mutant_report.certificate("memory_fn").unwrap().grade, "Unknown");
    assert_ne!(mutant_report.object_sha256, report.object_sha256);
    valid(equal(good.read_gpr(0, 8), bad.read_gpr(0, 8)), true);
    let frame = crate::cer_memory::PrivateFrame::new(address(0x8000), 32).unwrap();
    let query = Formula::Var("fresh_compiler_exit_byte".into(), Sort::BitVec(64));
    for (memory, expected) in [(&good.memory, true), (&bad.memory, false)] {
        let obligation = crate::cer_memory::outside_memory_equal(
            &Formula::Bool(true),
            &source.memory.exits[0].bytes,
            memory,
            &query,
            &frame,
        )
        .unwrap();
        valid(obligation.formula, expected);
    }
    let bad_exit = crate::cer_memory::outside_memory_equal(
        &Formula::Bool(true),
        &source.memory.exits[0].bytes,
        &bad.memory,
        &query,
        &frame,
    )
    .unwrap();
    let witness = Formula::And(vec![
        equal(xn(0), address(0x1000)),
        equal(read_slot_spec(&ScalarPlace::gpr(1, 8)).unwrap(), byte(1)),
        equal(query.clone(), address(0x1000)),
        equal(Formula::Select(b(source.memory.entry.clone()), b(address(0x1000))), byte(0)),
    ]);
    valid(Formula::Or(vec![Formula::Not(b(witness)), bad_exit.formula]), false);
    // The legal-memory diagnostic above does not itself mint a Refuted grade.
    assert_eq!(mutant_report.certificate("memory_fn").unwrap().grade, "Unknown");
    if let Some(path) = std::env::var_os("TRUST_SOURCE_MEMORY_OUTPUT_DIR") {
        let path = std::path::PathBuf::from(path);
        std::fs::create_dir_all(&path).unwrap();
        std::fs::write(path.join("compiler-store.o"), &shipped.object).unwrap();
        std::fs::write(path.join("dropped-store.o"), &mutant_object).unwrap();
        std::fs::write(path.join("module.json"), serde_json::to_vec_pretty(&m).unwrap()).unwrap();
        std::fs::write(
            path.join("reports.json"),
            serde_json::to_vec_pretty(&(report, &mutant_report)).unwrap(),
        )
        .unwrap();
    }
}

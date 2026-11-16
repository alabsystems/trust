use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use ay::{Logic, Solver};
use trust_ir::{
    Block, BlockId, BodyGate, CallingConv, Constant, FuncId, FuncTy, Function, Inst, InstrNode,
    Module, TargetInfo, Ty, ValueId,
};
use trust_machine_sem::condition_to_formula;

use super::*;
use crate::call_event::{
    CerInput, FnPlacement, ParamPlace, ProducerBody, ProducerModule, ReturnPlace, ScalarPlace,
    verify_compiled_module,
};
use crate::cer_memory::CounterexampleUse;
use crate::f1_compile::{
    F1CompileConfig, F1CompileInput, F1OptLevel, F1Target, compile_and_verify_trust_ir_module,
};
use crate::verify_output::EmitPolicy;

fn b(f: Formula) -> Box<Formula> {
    Box::new(f)
}
fn bv(n: u64) -> Formula {
    Formula::BitVec { value: i128::from(n), width: 64 }
}
fn eq(a: Formula, c: Formula) -> Formula {
    Formula::Eq(b(a), b(c))
}
fn x(n: usize) -> Formula {
    Formula::Var(format!("X{n}"), Sort::BitVec(64))
}
fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn node(inst: Inst, result: u32) -> InstrNode {
    InstrNode::new(inst).with_result(v(result))
}
fn zero() -> InstrNode {
    node(Inst::Const { ty: Ty::U64, value: Constant::Int(0) }, 3)
}
fn ret(value: u32) -> InstrNode {
    InstrNode::new(Inst::Return { values: vec![v(value)] })
}
fn store(ptr: u32) -> InstrNode {
    InstrNode::new(Inst::Store {
        ty: Ty::U64,
        ptr: v(ptr),
        value: v(1),
        volatile: false,
        align: Some(8),
    })
}
fn load(ptr: u32, result: u32) -> InstrNode {
    node(Inst::Load { ty: Ty::U64, ptr: v(ptr), volatile: false, align: Some(8) }, result)
}
fn module(blocks: Vec<Block>) -> Module {
    let mut m = Module::new("machine_memory");
    m.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    });
    let ty = m
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::U64, Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let mut f = Function::new(FuncId::new(0), "memory_fn", ty, BlockId::new(0));
    f.producer = Some(trust_ir::Producer::TRust);
    f.calling_conv = CallingConv::Rust;
    f.body_gate =
        Some(BodyGate::Gated { authority: "trust-direct-lane-structural".into(), evidence: None });
    f.blocks = blocks;
    m.functions.push(f);
    m
}
fn entry() -> Block {
    Block::new(BlockId::new(0))
        .with_param(v(0), Ty::Ptr)
        .with_param(v(1), Ty::U64)
        .with_param(v(2), Ty::U64)
}
fn write_module() -> Module {
    let mut e = entry();
    e.body = vec![store(0), zero(), ret(3)];
    module(vec![e])
}
fn load_module() -> Module {
    let mut e = entry();
    e.body = vec![load(0, 3), ret(3)];
    module(vec![e])
}
fn places() -> BTreeMap<String, FnPlacement> {
    BTreeMap::from([(
        "memory_fn".into(),
        FnPlacement {
            params: (0..3).map(|r| ParamPlace::Scalar(ScalarPlace::gpr(r, 64))).collect(),
            ret: ReturnPlace::Scalar(ScalarPlace::gpr(0, 64)),
        },
    )])
}
fn producers(m: &Module) -> [ProducerModule; 1] {
    [ProducerModule {
        module: Arc::new(m.clone()),
        symbols: m.functions.iter().map(|function| (function.id, function.name.clone())).collect(),
    }]
}
fn bodies() -> BTreeMap<String, ProducerBody> {
    BTreeMap::from([("memory_fn".into(), ProducerBody { producer: 0, func: FuncId::new(0) })])
}
fn save_actual_cer(name: &str, m: &Module, object: &[u8], report: &crate::call_event::CerReport) {
    if let Some(output) = std::env::var_os("TRUST_MACHINE_MEMORY_OUTPUT_DIR") {
        let output = std::path::PathBuf::from(output).join("actual-cer").join(name);
        std::fs::create_dir_all(&output).unwrap();
        std::fs::write(output.join("object.o"), object).unwrap();
        std::fs::write(output.join("module.json"), serde_json::to_vec_pretty(m).unwrap()).unwrap();
        std::fs::write(output.join("certificates.json"), report.to_json()).unwrap();
    }
}

fn strict_refuses(m: &Module, object: &[u8]) -> ObservationDiagnostics {
    let report = verify_compiled_module(&CerInput {
        m_cg: m,
        producers: &producers(m),
        bodies: &bodies(),
        placements: &places(),
        object,
        relocation_model: RelocationModel::Static,
    })
    .unwrap();
    save_actual_cer(&format!("object-{}", report.object_sha256), m, object, &report);
    assert_eq!(report.certificate("memory_fn").unwrap().grade, "Unknown");
    assert!(report.ships(EmitPolicy::StrictProvenOnly).is_err());
    let diagnostic = report.certificate("memory_fn").unwrap().memory_observation.clone().unwrap();
    assert_eq!(diagnostic.binding.as_ref().unwrap().object_sha256, report.object_sha256);
    assert!(diagnostic.incomplete.is_empty(), "{:?}", diagnostic.incomplete);
    assert!(diagnostic.missing_integration.contains("register/SP/flag correspondence"));
    assert!(diagnostic.missing_integration.contains("complete return-path coverage"));
    diagnostic
}
fn compile(m: &Module, level: F1OptLevel) -> Vec<u8> {
    let config = F1CompileConfig {
        force_frame_pointers: false,
        target: F1Target::Aarch64AppleDarwin,
        opt_level: level,
        relocation: RelocationModel::Static,
        never_inline: BTreeSet::new(),
        upstream_mir_lane: false,
    };
    let shipped = compile_and_verify_trust_ir_module(&F1CompileInput {
        m_cg: m,
        producers: &producers(m),
        bodies: &bodies(),
        placements: &places(),
        policy: EmitPolicy::AllowUnknown,
        config: &config,
    })
    .unwrap();
    if m.functions
        .iter()
        .flat_map(|function| &function.blocks)
        .flat_map(|block| &block.body)
        .any(|node| matches!(&node.inst, Inst::Alloca { .. }))
    {
        // A source Alloca the CER spec does not admit as a block-local slot
        // (SPEC-SLOT-1; these carry an explicit alignment) is Unknown: the
        // executor is never reached. Keep that refusal explicit while the
        // standalone observer audits frames.
        let certificate = shipped.report.certificate("memory_fn").unwrap();
        assert_eq!(certificate.grade, "Unknown");
        assert!(certificate.obligations.o4_return.detail.contains("Alloca"));
        assert!(certificate.memory_observation.is_none());
        assert!(shipped.report.ships(EmitPolicy::StrictProvenOnly).is_err());
        save_actual_cer("unsupported-source-alloca", m, &shipped.object, &shipped.report);
    } else {
        strict_refuses(m, &shipped.object);
    }
    shipped.object
}
fn bound(m: &Module, object: &[u8]) -> BoundFunction {
    BoundFunction::bind(object, m, "memory_fn", RelocationModel::Static).unwrap()
}
fn initial() -> MachineState {
    let mut state = MachineState::symbolic();
    state.memory = cer_memory::shared_entry_memory("machine_memory:fn0");
    state
}
fn valid(formula: Formula, expected: bool) {
    // Diagnostic AY only. No kernel/grade authority or SAT legality claim.
    let mut s = Solver::try_new(Logic::QfAbv).unwrap();
    let term = crate::verify_output::formula_to_term(&mut s, &formula).unwrap();
    let neg = s.try_not(term).unwrap();
    s.try_assert_term(neg).unwrap();
    let result = s.check_sat();
    assert!(if expected { result.is_unsat() } else { result.is_sat() }, "{result:?}");
}
fn obligations(xs: Vec<PendingMemoryObligation>) -> Formula {
    Formula::And(xs.into_iter().map(|x| x.formula).collect())
}

/// A finite TEST driver only: actual decoder/effects/state, with both branches
/// explored. Production control/rely/ABI traversal remains solely CerExec.
fn walk(
    session: &mut ObservationSession<'_>,
    pc: u64,
    mut state: MachineState,
    path: Formula,
    mut visited: Vec<u64>,
) -> Vec<MachineState> {
    assert!(!visited.contains(&pc), "fixture unexpectedly loops");
    visited.push(pc);
    assert!(visited.len() < 100);
    let window = session.function.window();
    let i = (pc - window.start) as usize;
    let insn = decode_aarch64(&window.code[i..i + 4], pc).unwrap();
    let effects = Aarch64Semantics.effects(&state, &insn).unwrap();
    let handle = session.before_step(pc, &path, &state, &effects).unwrap();
    if effects.iter().any(|e| matches!(e, Effect::Return { .. })) {
        session.at_return(&handle, &state).unwrap();
        return vec![state];
    }
    let mut next = pc + 4;
    let mut fork = None;
    for e in &effects {
        match e {
            Effect::Branch { target } => {
                let Formula::BitVec { value, .. } = target else {
                    panic!("indirect fixture branch")
                };
                next = *value as u64;
            }
            Effect::ConditionalBranch { condition, target, .. } => {
                let Formula::BitVec { value, .. } = target else {
                    panic!("indirect fixture branch")
                };
                fork = Some((condition_to_formula(&state, *condition).unwrap(), *value as u64));
            }
            Effect::PcUpdate { value } => {
                if let Formula::Ite(cond, taken, _) = value {
                    let Formula::BitVec { value, .. } = taken.as_ref() else {
                        panic!("indirect fixture branch")
                    };
                    fork = Some((*cond.clone(), *value as u64));
                }
            }
            Effect::Call { .. } => panic!("test driver does not model calls"),
            other => state.apply_effect(other).unwrap(),
        }
    }
    session.after_step(&handle, &state).unwrap();
    if let Some((condition, target)) = fork {
        let mut out = walk(
            session,
            target,
            state.clone(),
            Formula::And(vec![path.clone(), condition.clone()]),
            visited.clone(),
        );
        out.extend(walk(
            session,
            pc + 4,
            state,
            Formula::And(vec![path, Formula::Not(b(condition))]),
            visited,
        ));
        out
    } else {
        walk(session, next, state, path, visited)
    }
}
fn observe(function: &BoundFunction) -> (PendingMachineMemory, Vec<MachineState>) {
    let state = initial();
    let mut session = function.begin(&state).unwrap();
    let exits = walk(&mut session, function.window().start, state, Formula::Bool(true), Vec::new());
    (session.into_pending(), exits)
}
fn mutate(m: &Module, object: &[u8], pc: u64, word: u32) -> Vec<u8> {
    let parsed = CompiledObject::parse(object).unwrap();
    let f = bound(m, object);
    let section = parsed.section(f.binding().section).unwrap();
    let positions: Vec<_> = object
        .windows(section.bytes.len())
        .enumerate()
        .filter_map(|(i, b)| (b == section.bytes).then_some(i))
        .collect();
    assert_eq!(positions.len(), 1);
    let mut result = object.to_vec();
    let offset = positions[0] + pc as usize;
    result[offset..offset + 4].copy_from_slice(&word.to_le_bytes());
    assert_ne!(bound(m, &result).binding().object_sha256, f.binding().object_sha256);
    result
}
fn save(name: &str, m: &Module, object: &[u8], observed: &PendingMachineMemory) {
    if let Some(out) = std::env::var_os("TRUST_MACHINE_MEMORY_OUTPUT_DIR") {
        let out = std::path::PathBuf::from(out);
        std::fs::create_dir_all(&out).unwrap();
        std::fs::write(out.join(format!("{name}.o")), object).unwrap();
        std::fs::write(
            out.join(format!("{name}.module.json")),
            serde_json::to_vec_pretty(m).unwrap(),
        )
        .unwrap();
        let record = serde_json::json!({"object_sha256":observed.binding().object_sha256,"text_sha256":observed.binding().text_sha256,
            "module_sha256":observed.binding().module_sha256,"steps":observed.steps().len(),
            "accesses":observed.steps().iter().map(|s|s.accesses.len()).sum::<usize>(),"exits":observed.exits().len(),
            "missing_integration":observed.missing_integration(),"strict_refused":true});
        std::fs::write(
            out.join(format!("{name}.json")),
            serde_json::to_vec_pretty(&record).unwrap(),
        )
        .unwrap();
    }
}

#[test]
fn actual_compiler_dropped_wrong_extra_and_narrow_store_observations_remain_pending() {
    let m = write_module();
    let object = compile(&m, F1OptLevel::O3);
    let function = bound(&m, &object);
    let (good, _) = observe(&function);
    let production_good = strict_refuses(&m, &object);
    assert_eq!(production_good.steps.iter().map(|s| s.writes).sum::<usize>(), 1);
    assert_eq!(good.steps().iter().map(|s| s.accesses.len()).sum::<usize>(), 1);
    let store_step = good
        .steps()
        .iter()
        .find(|s| s.accesses.iter().any(|a| a.kind == AccessKind::Write))
        .unwrap();
    let store_word = u32::from_le_bytes(store_step.instruction);
    let source_access = PathAccess::new(AccessKind::Write, Formula::Bool(true), x(0), 8).unwrap();
    let source = cer_memory::store_le(initial().memory, &x(0), &x(1), 8).unwrap();
    let frame = PrivateFrame::new(bv(0x8000), 32).unwrap();
    let query = Formula::Var("fresh_store_query".into(), Sort::BitVec(64));
    valid(obligations(good.coverage_unclassified(&[source_access.clone()])), true);
    valid(
        obligations(
            good.exit_memory_obligations(&Formula::Bool(true), &source, &query, &frame).unwrap(),
        ),
        true,
    );
    save("good-store", &m, &object, &good);
    for (name, word, coverage_ok, query_address) in [
        ("dropped-store", 0xd503201f, true, 0x1000),
        ("wrong-value", (store_word & !31) | 2, true, 0x1000),
        ("wrong-offset", store_word + (1 << 10), false, 0x1000),
        ("narrow-store", 0x39000001, true, 0x1001),
        // LDR XZR,[X0,#8]: its value is discarded, but its extra read is retained.
        ("extra-dead-read", 0xf940041f, false, 0x1000),
    ] {
        let mutant = mutate(&m, &object, store_step.pc, word);
        let f = bound(&m, &mutant);
        let (data, _) = observe(&f);
        let production = strict_refuses(&m, &mutant);
        assert_eq!(
            production.steps.iter().map(|s| s.reads + s.writes).sum::<usize>(),
            data.steps().iter().map(|s| s.accesses.len()).sum::<usize>(),
            "real CerExec callbacks must retain the complete official access list"
        );
        assert_eq!(production.exits.len(), data.exits().len());
        if name == "dropped-store" {
            assert_eq!(production.steps.iter().map(|s| s.writes).sum::<usize>(), 0);
            assert_ne!(production.exits[0].memory_sha256, production_good.exits[0].memory_sha256);
        }
        let coverage = data.coverage_unclassified(&[source_access.clone()]);
        assert!(coverage.iter().all(|o| o.counterexample_use == CounterexampleUse::Inconclusive));
        valid(obligations(coverage), coverage_ok);
        let o6 = obligations(
            data.exit_memory_obligations(&Formula::Bool(true), &source, &query, &frame).unwrap(),
        );
        let witness = Formula::And(vec![
            eq(x(0), bv(0x1000)),
            eq(x(1), bv(0x0102030405060708)),
            eq(x(2), bv(0)),
            eq(query.clone(), bv(query_address)),
            eq(
                Formula::Select(b(initial().memory), b(bv(query_address))),
                Formula::BitVec { value: 0, width: 8 },
            ),
        ]);
        valid(Formula::Or(vec![Formula::Not(b(witness)), o6]), false);
        if name == "extra-dead-read" {
            assert_eq!(
                data.steps()
                    .iter()
                    .flat_map(|s| &s.accesses)
                    .filter(|a| a.kind == AccessKind::Read)
                    .count(),
                1
            );
        }
        assert!(data.missing_integration().contains("Unknown"));
        save(name, &m, &mutant, &data);
    }
}

#[test]
fn actual_compiler_load_width_and_address_controls_preserve_reads_and_o4_gap() {
    let m = load_module();
    let object = compile(&m, F1OptLevel::O3);
    let f = bound(&m, &object);
    let (good, returns) = observe(&f);
    let step = good.steps().iter().find(|s| !s.accesses.is_empty()).unwrap();
    assert_eq!(step.accesses[0].kind, AccessKind::Read);
    assert_eq!(step.accesses[0].width_bytes, 8);
    let source_access = PathAccess::new(AccessKind::Read, Formula::Bool(true), x(0), 8).unwrap();
    let source_value = cer_memory::load_le(&initial().memory, &x(0), 8).unwrap();
    valid(eq(source_value.clone(), returns[0].read_gpr(0, 64)), true);
    for (name, word, coverage_ok) in [
        ("narrow-load", 0x39400000, true),
        ("wrong-load-offset", u32::from_le_bytes(step.instruction) + (1 << 10), false),
    ] {
        let mutant = mutate(&m, &object, step.pc, word);
        let mf = bound(&m, &mutant);
        let (data, returns) = observe(&mf);
        strict_refuses(&m, &mutant);
        valid(obligations(data.coverage_unclassified(&[source_access.clone()])), coverage_ok);
        valid(eq(source_value.clone(), returns[0].read_gpr(0, 64)), false);
        assert_eq!(
            data.steps()
                .iter()
                .flat_map(|s| &s.accesses)
                .filter(|a| a.kind == AccessKind::Read)
                .count(),
            1
        );
        save(name, &m, &mutant, &data);
    }
}

#[test]
fn actual_conditional_object_keeps_both_paths_and_wrong_path_is_uncovered() {
    let mut e = entry();
    e.body = vec![
        node(Inst::Const { ty: Ty::U64, value: Constant::Int(0) }, 5),
        node(Inst::ICmp { op: trust_ir::ICmpOp::Ne, ty: Ty::U64, lhs: v(2), rhs: v(5) }, 6),
        InstrNode::new(Inst::CondBr {
            cond: v(6),
            then_target: BlockId::new(1),
            then_args: vec![],
            else_target: BlockId::new(2),
            else_args: vec![],
        }),
    ];
    let mut yes = Block::new(BlockId::new(1));
    yes.body = vec![store(0), zero(), ret(3)];
    let mut no = Block::new(BlockId::new(2));
    no.body = vec![node(Inst::Const { ty: Ty::U64, value: Constant::Int(0) }, 4), ret(4)];
    let m = module(vec![e, yes, no]);
    let object = compile(&m, F1OptLevel::O3);
    let f = bound(&m, &object);
    let (good, _) = observe(&f);
    assert_eq!(good.exits().len(), 2);
    let production = strict_refuses(&m, &object);
    assert_eq!(production.exits.len(), 2);
    assert_ne!(production.exits[0].path_sha256, production.exits[1].path_sha256);
    assert!(production.exits.iter().all(|e| e.path.is_some() && e.path_sha256.is_some()));
    assert!(production.exits.iter().all(|e| e.kind == ExitKind::Return));
    assert_eq!(production.steps.iter().filter(|s| s.writes != 0).count(), 1);
    let occurrence_ids: BTreeSet<_> = production.steps.iter().map(|s| s.occurrence).collect();
    assert_eq!(occurrence_ids.len(), production.steps.len());
    let mut expected_visits = BTreeMap::new();
    for step in good.steps() {
        *expected_visits.entry(step.pc).or_insert(0usize) += 1;
    }
    let mut actual_visits = BTreeMap::new();
    for step in &production.steps {
        *actual_visits.entry(step.pc).or_insert(0usize) += 1;
    }
    assert_eq!(
        actual_visits, expected_visits,
        "shared join PCs cannot be deduplicated across paths"
    );
    let accesses: Vec<_> = good.steps().iter().flat_map(|s| &s.accesses).collect();
    assert_eq!(accesses.len(), 1);
    assert_ne!(
        good.steps().iter().find(|s| !s.accesses.is_empty()).unwrap().path,
        Formula::Bool(true)
    );
    let sources = vec![accesses[0].term.clone()];
    valid(obligations(good.coverage_unclassified(&sources)), true);
    let conditional = good.steps().iter().find(|s| s.control == Control::Conditional).unwrap();
    let word = u32::from_le_bytes(conditional.instruction);
    let flipped = if (word & 0x7e000000) == 0x34000000 || (word & 0x7e000000) == 0x36000000 {
        word ^ (1 << 24)
    } else {
        assert_eq!(word & 0xff000010, 0x54000000);
        word ^ 1
    };
    let mutant = mutate(&m, &object, conditional.pc, flipped);
    let mf = bound(&m, &mutant);
    let (data, _) = observe(&mf);
    strict_refuses(&m, &mutant);
    valid(obligations(data.coverage_unclassified(&sources)), false);
    assert_eq!(data.exits().len(), 2);
    save("wrong-store-path", &m, &mutant, &data);
}

#[test]
fn effect_subsets_wrong_pc_and_fabricated_snapshots_cannot_be_observed() {
    let m = write_module();
    let object = compile(&m, F1OptLevel::O3);
    let f = bound(&m, &object);
    let (data, _) = observe(&f);
    let pc = data.steps().iter().find(|s| !s.accesses.is_empty()).unwrap().pc;
    let state = initial();
    let insn =
        decode_aarch64(&f.window().code[(pc - f.window().start) as usize..][..4], pc).unwrap();
    let effects = Aarch64Semantics.effects(&state, &insn).unwrap();
    let subset: Vec<_> =
        effects.iter().filter(|e| !matches!(e, Effect::MemWrite { .. })).cloned().collect();
    let mut session = f.begin(&state).unwrap();
    assert!(session.before_step(pc, &Formula::Bool(true), &state, &subset).is_err());
    assert!(session.before_step(pc + 1, &Formula::Bool(true), &state, &effects).is_err());
    assert!(session.before_step(f.window().end, &Formula::Bool(true), &state, &effects).is_err());
    let handle = session.before_step(pc, &Formula::Bool(true), &state, &effects).unwrap();
    assert!(
        session.after_step(&handle, &state).is_err(),
        "dropping the actual write cannot validate its post-state"
    );
    assert!(session.at_return(&handle, &state).is_err());
    assert!(session.after_call(&handle, &state).is_err());
    assert!(session.after_tail_call(&handle, &state).is_err());
    let mut mismatched = f.window().clone();
    mismatched.successors.clear();
    assert!(f.begin_for_window(&mismatched, &state).is_err());
    let other = f.begin(&state).unwrap();
    assert!(other.step(&handle).is_err());
    let pending = session.into_pending();
    assert_eq!(pending.steps().len(), 1);
    assert!(pending.exits().is_empty());
    assert!(pending.missing_integration().contains("execution coverage"));
    assert!(
        pending
            .exit_memory_obligations(
                &Formula::Bool(true),
                &state.memory,
                &x(9),
                &PrivateFrame::new(x(10), 32).unwrap()
            )
            .is_err()
    );
}

#[test]
fn entry_parameterization_is_preserved_and_atomic_or_wide_memory_refuses() {
    let m = write_module();
    let object = compile(&m, F1OptLevel::O3);
    let f = bound(&m, &object);
    let (data, _) = observe(&f);
    let mut entry = initial();
    entry.gpr[1] = Formula::BvAnd(b(x(1)), b(bv(0xffff_ffff_0000_00ff)), 64);
    let pending = f.begin(&entry).unwrap().into_pending();
    assert_eq!(pending.entry().gpr[1], entry.gpr[1]);
    entry.gpr[30] =
        Formula::Ite(b(Formula::Var("return_choice".into(), Sort::Bool)), b(x(28)), b(x(29)));
    let ret_step = data.steps().iter().find(|s| s.control == Control::Return).unwrap();
    let ret_insn = decode_aarch64(&ret_step.instruction, ret_step.pc).unwrap();
    let mut returns = f.begin(&entry).unwrap();
    let ret_handle = returns
        .before_step(
            ret_step.pc,
            &Formula::Bool(true),
            &entry,
            &Aarch64Semantics.effects(&entry, &ret_insn).unwrap(),
        )
        .unwrap();
    returns.at_return(&ret_handle, &entry).unwrap();
    assert_eq!(returns.into_pending().exits().len(), 1);
    let pc = data.steps().iter().find(|s| !s.accesses.is_empty()).unwrap().pc;
    // STLR X1,[X0] has ordering metadata; STR Q1,[X0] transfers sixteen bytes.
    for word in [0xc89ffc01, 0x3d800001] {
        let mutant = mutate(&m, &object, pc, word);
        let mf = bound(&m, &mutant);
        let mut session = mf.begin(&initial()).unwrap();
        let insn = decode_aarch64(&word.to_le_bytes(), pc).unwrap();
        let effects = Aarch64Semantics.effects(&initial(), &insn).unwrap();
        assert!(session.before_step(pc, &Formula::Bool(true), &initial(), &effects).is_err());
        assert!(
            session.into_pending().steps().is_empty(),
            "failed instruction never leaves a partial census"
        );
    }
}

#[test]
fn actual_private_frame_accesses_are_retained_for_the_o5_owner() {
    let mut e = entry();
    e.body = vec![
        node(Inst::Alloca { ty: Ty::U64, count: None, align: Some(8) }, 4),
        store(4),
        load(4, 5),
        ret(5),
    ];
    let m = module(vec![e]);
    let object = compile(&m, F1OptLevel::O0);
    let f = bound(&m, &object);
    let (data, _) = observe(&f);
    let accesses: Vec<_> = data.steps().iter().flat_map(|s| &s.accesses).collect();
    assert!(!accesses.is_empty());
    assert!(accesses.iter().any(|a| {
        let mut found = false;
        a.address.visit(&mut |t| {
            if matches!(t,Formula::Var(n,_) if n=="SP") {
                found = true
            }
        });
        found
    }));
    let coverage = data.coverage_unclassified(&[]);
    assert!(!coverage.is_empty());
    valid(obligations(coverage), false);
    assert!(data.missing_integration().contains("O5-owned validated frame partition"));
    save("private-frame", &m, &object, &data);
}

#[test]
fn actual_named_call_snapshots_retain_both_arrays_without_forging_a_rely_proof() {
    let mut e = entry();
    e.body = vec![
        store(0),
        node(Inst::Call { callee: FuncId::new(1), args: vec![v(0), v(1), v(2)] }, 4),
        zero(),
        ret(3),
    ];
    let mut m = module(vec![e]);
    let mut declaration =
        Function::new(FuncId::new(1), "helper", m.functions[0].ty, BlockId::new(0));
    declaration.calling_conv = CallingConv::Rust;
    m.functions.push(declaration);
    let mut placements = places();
    placements.insert("helper".into(), placements["memory_fn"].clone());
    let config = F1CompileConfig {
        force_frame_pointers: false,
        target: F1Target::Aarch64AppleDarwin,
        opt_level: F1OptLevel::O0,
        relocation: RelocationModel::Static,
        never_inline: BTreeSet::from(["helper".into()]),
        upstream_mir_lane: false,
    };
    let shipped = compile_and_verify_trust_ir_module(&F1CompileInput {
        m_cg: &m,
        producers: &producers(&m),
        bodies: &bodies(),
        placements: &placements,
        policy: EmitPolicy::AllowUnknown,
        config: &config,
    })
    .unwrap();
    assert!(shipped.report.ships(EmitPolicy::StrictProvenOnly).is_err());
    let production =
        shipped.report.certificate("memory_fn").unwrap().memory_observation.as_ref().unwrap();
    assert!(production.incomplete.is_empty(), "{:?}", production.incomplete);
    assert_eq!(production.calls.len(), 1);
    assert_eq!(production.calls[0].kind, CallKind::Call);
    assert_ne!(production.calls[0].before_sha256, production.calls[0].after_sha256);
    assert_eq!(production.exits.len(), 1);
    let function = bound(&m, &shipped.object);
    let mut state = initial();
    let mut session = function.begin(&state).unwrap();
    let mut pc = function.window().start;
    for _ in 0..100 {
        let offset = (pc - function.window().start) as usize;
        let instruction = decode_aarch64(&function.window().code[offset..offset + 4], pc).unwrap();
        let effects = Aarch64Semantics.effects(&state, &instruction).unwrap();
        let handle = session.before_step(pc, &Formula::Bool(true), &state, &effects).unwrap();
        if effects.iter().any(|e| matches!(e, Effect::Call { .. })) {
            assert_eq!(function.window().site_at(pc).unwrap().callee.as_deref(), Some("helper"));
            let before = state.memory.clone();
            // A diagnostic caller-supplied post-array: this deliberately supplies
            // neither the real CER rely nor frame overlays/callee premises.
            let mut post = state.clone();
            post.memory = cer_memory::shared_post_call_memory("unproved_test_call", pc);
            assert!(session.after_step(&handle, &post).is_err());
            session.after_call(&handle, &post).unwrap();
            assert!(session.after_call(&handle, &post).is_err());
            let pending = session.into_pending();
            assert_eq!(pending.calls().len(), 1);
            assert_eq!(pending.calls()[0].before, before);
            assert_eq!(pending.calls()[0].after, post.memory);
            assert_ne!(pending.calls()[0].before, pending.calls()[0].after);
            assert!(pending.exits().is_empty());
            assert!(pending.missing_integration().contains("M3/M4/M5"));
            save("pending-call", &m, &shipped.object, &pending);
            return;
        }
        for effect in &effects {
            if !matches!(effect, Effect::PcUpdate { .. }) {
                state.apply_effect(effect).unwrap();
            }
        }
        session.after_step(&handle, &state).unwrap();
        pc += 4;
    }
    panic!("actual compiler fixture did not reach its ordinary named call");
}

#[test]
fn real_cer_tail_branch_records_call_and_exit_without_fabricated_ret() {
    let mut e = entry();
    e.body = vec![
        store(0),
        node(Inst::Call { callee: FuncId::new(1), args: vec![v(0), v(1), v(2)] }, 4),
        ret(4),
    ];
    let mut m = module(vec![e]);
    let mut declaration =
        Function::new(FuncId::new(1), "helper", m.functions[0].ty, BlockId::new(0));
    declaration.calling_conv = CallingConv::Rust;
    m.functions.push(declaration);
    let mut placements = places();
    placements.insert("helper".into(), placements["memory_fn"].clone());
    let config = F1CompileConfig {
        force_frame_pointers: false,
        target: F1Target::Aarch64AppleDarwin,
        opt_level: F1OptLevel::O3,
        relocation: RelocationModel::Static,
        never_inline: BTreeSet::from(["helper".into()]),
        upstream_mir_lane: false,
    };
    let shipped = compile_and_verify_trust_ir_module(&F1CompileInput {
        m_cg: &m,
        producers: &producers(&m),
        bodies: &bodies(),
        placements: &placements,
        policy: EmitPolicy::AllowUnknown,
        config: &config,
    })
    .unwrap();
    let original = bound(&m, &shipped.object);
    let site =
        original.window().sites.iter().find(|s| s.callee.as_deref() == Some("helper")).unwrap();
    let mut object = shipped.object.clone();
    if site.kind == MachineSiteKind::Call {
        // A genuine compiled BL relocation, mutated into a bound tail branch.
        // Padding the remainder keeps the whole object extent honest. This is
        // a byte-mutant integration fixture, not a native tail-optimization claim.
        let parsed = CompiledObject::parse(&object).unwrap();
        let section = parsed.section(original.window().section).unwrap();
        let positions: Vec<_> = object
            .windows(section.bytes.len())
            .enumerate()
            .filter_map(|(i, bytes)| (bytes == section.bytes).then_some(i))
            .collect();
        assert_eq!(positions.len(), 1);
        let base = positions[0];
        let index = base + site.offset as usize;
        let old = u32::from_le_bytes(object[index..index + 4].try_into().unwrap());
        object[index..index + 4].copy_from_slice(&(0x14000000 | (old & 0x03ffffff)).to_le_bytes());
        for pc in ((site.offset + 4)..original.window().end).step_by(4) {
            let at = base + pc as usize;
            object[at..at + 4].copy_from_slice(&0xd503201fu32.to_le_bytes());
        }
    }
    let report = verify_compiled_module(&CerInput {
        m_cg: &m,
        producers: &producers(&m),
        bodies: &bodies(),
        placements: &placements,
        object: &object,
        relocation_model: RelocationModel::Static,
    })
    .unwrap();
    save_actual_cer("tail-branch", &m, &object, &report);
    let certificate = report.certificate("memory_fn").unwrap();
    assert_eq!(certificate.grade, "Unknown");
    assert!(report.ships(EmitPolicy::StrictProvenOnly).is_err());
    let diagnostic = certificate.memory_observation.as_ref().unwrap();
    assert!(diagnostic.incomplete.is_empty(), "{:?}", diagnostic.incomplete);
    assert_eq!(diagnostic.calls.len(), 1);
    assert_eq!(diagnostic.calls[0].kind, CallKind::Tail);
    assert_eq!(diagnostic.exits.len(), 1);
    assert_eq!(diagnostic.exits[0].kind, ExitKind::TailReturn);
    assert_eq!(diagnostic.exits[0].memory_sha256, diagnostic.calls[0].after_sha256);
    let function = bound(&m, &object);
    let tail = function.window().sites.iter().find(|s| s.kind == MachineSiteKind::Tail).unwrap();
    let state = initial();
    let mut session = function.begin(&state).unwrap();
    let i = (tail.offset - function.window().start) as usize;
    let decoded = decode_aarch64(&function.window().code[i..i + 4], tail.offset).unwrap();
    let effects = Aarch64Semantics.effects(&state, &decoded).unwrap();
    let handle = session.before_step(tail.offset, &Formula::Bool(true), &state, &effects).unwrap();
    assert!(session.after_call(&handle, &state).is_err());
    assert!(session.at_return(&handle, &state).is_err());
    assert!(session.after_tail_call(&handle, &state).is_err(), "ordinary effects not checked");
    session.after_step(&handle, &state).unwrap();
    assert!(session.after_step(&handle, &state).is_err(), "duplicate ordinary callback");
    let mut post = state.clone();
    post.memory = cer_memory::shared_post_call_memory("pending_tail", tail.offset);
    session.after_tail_call(&handle, &post).unwrap();
    assert!(session.after_tail_call(&handle, &post).is_err());
    let pending = session.into_pending();
    assert_eq!(pending.calls()[0].kind, CallKind::Tail);
    assert_eq!(pending.exits()[0].kind, ExitKind::TailReturn);
    assert_eq!(pending.exits()[0].bytes, post.memory);
}

#[test]
fn real_cer_trap_shortcut_is_explicitly_incomplete_and_never_a_memory_proof() {
    let mut e = entry();
    e.body = vec![store(0), InstrNode::new(Inst::Unreachable)];
    let m = module(vec![e]);
    let config = F1CompileConfig {
        force_frame_pointers: false,
        target: F1Target::Aarch64AppleDarwin,
        opt_level: F1OptLevel::O0,
        relocation: RelocationModel::Static,
        never_inline: BTreeSet::new(),
        upstream_mir_lane: false,
    };
    let shipped = compile_and_verify_trust_ir_module(&F1CompileInput {
        m_cg: &m,
        producers: &producers(&m),
        bodies: &bodies(),
        placements: &places(),
        policy: EmitPolicy::AllowUnknown,
        config: &config,
    })
    .unwrap();
    save_actual_cer("trap-shortcut", &m, &shipped.object, &shipped.report);
    let certificate = shipped.report.certificate("memory_fn").unwrap();
    assert_eq!(certificate.grade, "Unknown");
    assert!(shipped.report.ships(EmitPolicy::StrictProvenOnly).is_err());
    let diagnostic = certificate.memory_observation.as_ref().unwrap();
    assert!(diagnostic.binding.is_some());
    assert!(diagnostic.incomplete.iter().any(|reason| reason.contains("skipped trap tail")));
    assert!(diagnostic.exits.is_empty());
    assert!(diagnostic.missing_integration.contains("execution coverage"));
}

/// A published path carries the digest of its compact JSON (the bytes `serde_json::to_vec`
/// renders); the term itself is published up to `PUBLISHED_PATH_BYTES` and withheld past it.
#[test]
fn a_long_path_is_published_by_digest_alone() {
    let digest = |f: &Formula| hex(&Sha256::digest(serde_json::to_vec(f).unwrap()));
    let p = |n: usize| Formula::Var(format!("p{n}"), Sort::Bool);
    let short = Formula::And(vec![Formula::Bool(true), Formula::Not(Box::new(p(1)))]);
    let (sha, path) = published_path(&short);
    assert_eq!(sha.as_deref(), Some(digest(&short).as_str()));
    assert_eq!(path, Some(short));
    let long = Formula::And((0..400).map(p).collect());
    let length = serde_json::to_vec(&long).unwrap().len() as u64;
    assert!(length > PUBLISHED_PATH_BYTES, "{length}");
    let (sha, path) = published_path(&long);
    assert_eq!(sha.as_deref(), Some(digest(&long).as_str()));
    assert_eq!(path, None);
}

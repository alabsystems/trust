// trust_ir_gate_loops.rs — WS7.14: the IN-COMPILER proven-output gate
// (`verify_trust_ir_output_preserved`) models LOOPS by cut-point simulation.
//
// PROVENANCE (F-114, scout-f1.8, measured on `d9ea36f376`). The Part A F1
// loop recipe (`nl4.rs`'s `count_to`) was refused under the DEFAULT strict
// gate with "loop/backedge at bb1 (fail-closed)": the spec side's per-path
// `visited` set turned every back-edge into `Err`, so the verdict was
// `Unknown` and the function shipped only under `allow-unknown`.
//
// WHAT THE FIX IS. Every loop header is a CUT POINT. The spec is cut into
// acyclic segments (entry -> header, header -> {header, return}); the machine
// is run from the header's claimed address with the header's SHARED VARIABLES
// (block params + every other live-in) in their claimed registers and
// everything else HAVOC; each segment proves `spec_reach => machine_reach AND
// agreement`. By induction over cut points that is lockstep PARTIAL
// correctness — nothing is claimed about non-termination.
//
// THE MAP IS UNTRUSTED. The header addresses are the emitted bytes' backward
// branch targets and the registers are located structurally at the first
// arrival; a wrong map can only make a segment fail, never prove — and a
// STRAY candidate (no loop header claims it) demotes a failure to `Unknown`,
// so a wrong map cannot fabricate `Refuted` either.
// `verify_trust_ir_bytes_with_claimed_cut_points` (a `test-hooks` entry) lets
// this file inject a LYING map and demand exactly that.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(all(feature = "ay-proofs", feature = "test-hooks"))]

use trust_cg_bridge::codegen_backend::{
    BridgeOptimizationLevel, TrustCgCodegenBackend, TrustCgTargetArch,
};
use trust_cg_bridge::module_to_lir::{
    lower_module_to_lir, lower_trust_ir_function_to_lir_trap_assert_oracle,
};
use trust_cg_bridge::verify_output::{OutputVerdict, ProvenEvidence};
use trust_cg_bridge::verify_output_trust_ir::{
    ClaimedCutPoint, TrustIrGateSource, emitted_text, trust_ir_function_semantics,
    trust_ir_gate_obligation, verify_trust_ir_bytes, verify_trust_ir_bytes_with_claimed_cut_points,
    verify_trust_ir_output_preserved, verify_trust_ir_output_preserved_with_lowering,
};
use trust_ir::inst::{BinOp, ICmpOp, Inst};
use trust_ir::node::InstrNode;
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, Constant, Function as IrFunction, Module, Producer, Ty};

fn backend() -> TrustCgCodegenBackend {
    TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::AArch64, "aarch64-apple-darwin")
        .with_optimization_level(BridgeOptimizationLevel::O0)
}

fn source(module: Module, symbol: &str) -> TrustIrGateSource {
    TrustIrGateSource {
        abi_cross_check: None,
        symbol: symbol.to_string(),
        module: module.into(),
        func_id: FuncId::new(0),
    }
}

fn u32_module(name: &str, params: usize) -> (Module, IrFunction) {
    let mut module = Module::new(name);
    module.func_types.push(FuncTy {
        params: vec![Ty::U32; params],
        returns: vec![Ty::U32],
        is_vararg: false,
        abi: None,
    });
    let mut f = IrFunction::new(FuncId::new(0), name, FuncTyId::new(0), BlockId::new(0));
    f.producer = Some(Producer::TRust);
    (module, f)
}

fn v(i: u32) -> ValueId {
    ValueId::new(i)
}

fn konst(ty: Ty, value: i128, out: ValueId) -> InstrNode {
    InstrNode::new(Inst::Const { ty, value: Constant::Int(value) }).with_result(out)
}

fn add(ty: Ty, lhs: ValueId, rhs: ValueId, out: ValueId) -> InstrNode {
    InstrNode::new(Inst::BinOp { op: BinOp::Add, ty, lhs, rhs }).with_result(out)
}

fn icmp(op: ICmpOp, ty: Ty, lhs: ValueId, rhs: ValueId, out: ValueId) -> InstrNode {
    InstrNode::new(Inst::ICmp { op, ty, lhs, rhs }).with_result(out)
}

fn br(target: u32, args: Vec<ValueId>) -> InstrNode {
    InstrNode::new(Inst::Br { target: BlockId::new(target), args })
}

fn condbr(cond: ValueId, then: (u32, Vec<ValueId>), els: (u32, Vec<ValueId>)) -> InstrNode {
    InstrNode::new(Inst::CondBr {
        cond,
        then_target: BlockId::new(then.0),
        then_args: then.1,
        else_target: BlockId::new(els.0),
        else_args: els.1,
    })
}

fn ret(value: ValueId) -> InstrNode {
    InstrNode::new(Inst::Return { values: vec![value] })
}

// ===========================================================================
// Positive fixtures
// ===========================================================================

/// `count_to(n) = { let mut i = 0; while i < n { i += 1 } i }` — the Part A
/// F1 loop recipe (`nl4.rs`), spelled in trust-ir:
///
/// ```text
/// bb0(%0: n):        %1 = 0;               br bb1(%1)
/// bb1(%2: i):        %3 = icmp ult %2, %0; condbr %3, bb2(), bb3()
/// bb2:               %4 = add %2, 1;       br bb1(%4)      -- the latch
/// bb3:               ret %2
/// ```
///
/// `n` is a live-in of the header that is NOT a block param — the shape the
/// roadmap's REVIEW strengthened the cut point for.
fn count_to_module() -> Module {
    let (mut module, mut f) = u32_module("count_to", 1);
    let (n, zero, i, c, one, i1) = (v(0), v(1), v(2), v(3), v(4), v(5));
    let mut bb0 = Block::new(BlockId::new(0));
    bb0.params.push((n, Ty::U32));
    bb0.body.push(konst(Ty::U32, 0, zero));
    bb0.body.push(br(1, vec![zero]));
    let mut bb1 = Block::new(BlockId::new(1));
    bb1.params.push((i, Ty::U32));
    bb1.body.push(icmp(ICmpOp::Ult, Ty::U32, i, n, c));
    bb1.body.push(condbr(c, (2, vec![]), (3, vec![])));
    let mut bb2 = Block::new(BlockId::new(2));
    bb2.body.push(konst(Ty::U32, 1, one));
    bb2.body.push(add(Ty::U32, i, one, i1));
    bb2.body.push(br(1, vec![i1]));
    let mut bb3 = Block::new(BlockId::new(3));
    bb3.body.push(ret(i));
    f.blocks.extend([bb0, bb1, bb2, bb3]);
    module.functions.push(f);
    module
}

/// `sum_to(n) = { let (mut s, mut i) = (0, 0); while i < n { s += i; i += 1 } s }`
/// — TWO loop-carried block params, both `0` at entry (so the register
/// location of each must be told apart from the other's).
fn sum_to_module() -> Module {
    let (mut module, mut f) = u32_module("sum_to", 1);
    let (n, zero, s, i, c, s1, one, i1) = (v(0), v(1), v(2), v(3), v(4), v(5), v(6), v(7));
    let mut bb0 = Block::new(BlockId::new(0));
    bb0.params.push((n, Ty::U32));
    bb0.body.push(konst(Ty::U32, 0, zero));
    bb0.body.push(br(1, vec![zero, zero]));
    let mut bb1 = Block::new(BlockId::new(1));
    bb1.params.push((s, Ty::U32));
    bb1.params.push((i, Ty::U32));
    bb1.body.push(icmp(ICmpOp::Ult, Ty::U32, i, n, c));
    bb1.body.push(condbr(c, (2, vec![]), (3, vec![])));
    let mut bb2 = Block::new(BlockId::new(2));
    bb2.body.push(add(Ty::U32, s, i, s1));
    bb2.body.push(konst(Ty::U32, 1, one));
    bb2.body.push(add(Ty::U32, i, one, i1));
    bb2.body.push(br(1, vec![s1, i1]));
    let mut bb3 = Block::new(BlockId::new(3));
    bb3.body.push(ret(s));
    f.blocks.extend([bb0, bb1, bb2, bb3]);
    module.functions.push(f);
    module
}

/// `guarded(n) = { let mut i = 0; while i < n { assert!(i != 7); i += 1 } i }`
/// — an `Inst::Assert` INSIDE the loop body, so a header segment has a
/// non-trivial `reach` and the machine side a `brk` tail.
fn guarded_loop_module() -> Module {
    let (mut module, mut f) = u32_module("guarded_loop", 1);
    let (n, zero, i, c, seven, ne, one, i1) = (v(0), v(1), v(2), v(3), v(4), v(5), v(6), v(7));
    let mut bb0 = Block::new(BlockId::new(0));
    bb0.params.push((n, Ty::U32));
    bb0.body.push(konst(Ty::U32, 0, zero));
    bb0.body.push(br(1, vec![zero]));
    let mut bb1 = Block::new(BlockId::new(1));
    bb1.params.push((i, Ty::U32));
    bb1.body.push(icmp(ICmpOp::Ult, Ty::U32, i, n, c));
    bb1.body.push(condbr(c, (2, vec![]), (3, vec![])));
    let mut bb2 = Block::new(BlockId::new(2));
    bb2.body.push(konst(Ty::U32, 7, seven));
    bb2.body.push(icmp(ICmpOp::Ne, Ty::U32, i, seven, ne));
    // trust-ir v52 (train T8): a siteless `Unspecified` assert is the pre-v52
    // `Assert { cond }` exactly; the shipping converter refuses every `Assert`.
    bb2.body.push(InstrNode::new(Inst::Assert {
        cond: ne,
        kind: trust_ir::AssertKind::Unspecified,
        site: None,
    }));
    bb2.body.push(konst(Ty::U32, 1, one));
    bb2.body.push(add(Ty::U32, i, one, i1));
    bb2.body.push(br(1, vec![i1]));
    let mut bb3 = Block::new(BlockId::new(3));
    bb3.body.push(ret(i));
    f.blocks.extend([bb0, bb1, bb2, bb3]);
    module.functions.push(f);
    module
}

fn assert_proven(name: &str, module: Module) -> Vec<u8> {
    let subject = source(module, name);
    let (verdict, obj) = verify_trust_ir_output_preserved(&subject, &backend());
    assert!(
        matches!(verdict, OutputVerdict::Proven { .. }),
        "`{name}` must be PROVED under the default strict gate: {verdict:?}"
    );
    // A loop verdict is solver authority only: the certificate does not cover
    // the cut-point induction.
    assert!(
        matches!(verdict, OutputVerdict::Proven { evidence: ProvenEvidence::AyValidated }),
        "a loop verdict must be capped at AyValidated: {verdict:?}"
    );
    obj.expect("a proven function ships its bytes")
}

/// RATCHET ROW scout-f1.8 (GAP -> PASS): the `count_to` loop, refused before
/// with "loop/backedge at bb1 (fail-closed)", is proved under strict.
#[test]
fn scout_f1_8_count_to_is_proven_under_strict() {
    let subject = source(count_to_module(), "count_to");
    let (verdict, _) = verify_trust_ir_output_preserved(&subject, &backend());
    if let OutputVerdict::Unknown { reason } = &verdict {
        assert!(!reason.contains("loop/backedge"), "the scout-f1.8 refusal is back: {reason}");
    }
    assert!(matches!(verdict, OutputVerdict::Proven { .. }), "{verdict:?}");
}

#[test]
fn while_sum_loop_is_proven() {
    assert_proven("sum_to", sum_to_module());
}

/// The TRAP ORACLE's lowering (`Assert` -> `Brif`/`Trap`), which upstream keeps
/// for exactly this use: the shipping converter refuses every `Assert`
/// (`[implicit-panic-unfaithful]`, R-8 ledger item 1), so a loop carrying one
/// reaches the gate only through the oracle.
fn lower_with_trap_oracle(
    module: &Module,
    func_id: FuncId,
) -> Result<trust_cg_lower::function::Function, String> {
    let function = module.function_by_id(func_id).ok_or("no such function")?;
    lower_trust_ir_function_to_lir_trap_assert_oracle(module, function, false)
        .map_err(|e| e.to_string())
}

/// An `Assert` INSIDE a loop: the shipping gate refuses it by name before any
/// byte is emitted (upstream's rule, reconciled here), and the gate over the
/// trap oracle's bytes PROVES it — the header segment's `reach` is non-trivial
/// and its O0 rests on the seeded ABI invariant (WS7.14 x O0).
#[test]
fn loop_with_guarded_assert_is_proven() {
    let subject = source(guarded_loop_module(), "guarded_loop");
    match verify_trust_ir_output_preserved(&subject, &backend()) {
        (OutputVerdict::Unknown { reason }, None) => assert!(
            reason.contains("[implicit-panic-unfaithful]"),
            "the shipping converter must refuse the loop's Assert by name: {reason}"
        ),
        other => panic!("the shipping gate must refuse an implicit panic, got {other:?}"),
    }
    let (verdict, obj) = verify_trust_ir_output_preserved_with_lowering(
        &subject,
        &backend(),
        lower_with_trap_oracle,
    );
    assert!(
        matches!(verdict, OutputVerdict::Proven { evidence: ProvenEvidence::AyValidated }),
        "`guarded_loop` over the trap oracle's bytes must be PROVED, capped at AyValidated: \
         {verdict:?}"
    );
    assert!(obj.is_some(), "a proven function ships its bytes");
}

/// The spec side's shape: one cut point at bb1 whose shared variables are the
/// block param `i` FIRST and the live-in `n` after it; the entry segment
/// arrives at bb1 and never returns directly; the header segment both returns
/// and arrives back at bb1.
#[test]
fn count_to_spec_is_cut_at_the_header_with_n_as_a_shared_live_in() {
    let spec =
        trust_ir_function_semantics(&count_to_module(), FuncId::new(0)).expect("in fragment");
    assert_eq!(spec.cut_points.len(), 1);
    let cut = &spec.cut_points[0];
    assert_eq!(cut.block, 1);
    let shared: Vec<(u32, u32)> = cut.shared.iter().map(|s| (s.value, s.width)).collect();
    assert_eq!(shared, vec![(2, 32), (0, 32)], "params first, then live-ins: {shared:?}");
    assert_eq!(spec.segments.len(), 2);
    let entry = &spec.segments[0];
    assert_eq!(entry.start, None);
    assert!(matches!(entry.reach, trust_types::Formula::Bool(false)), "{:?}", entry.reach);
    assert_eq!(entry.arrivals.len(), 1);
    assert_eq!(entry.arrivals[0].block, 1);
    let header = &spec.segments[1];
    assert_eq!(header.start, Some(1));
    assert_eq!(header.arrivals.len(), 1);
    assert_eq!(header.arrivals[0].block, 1);
    let rendered = format!("{:?}", header.arrivals[0].values[0]);
    assert!(rendered.contains("CUT_bb1_v2"), "the latch carries i+1 over the shared i: {rendered}");
}

// ===========================================================================
// Negative twin + mutation control: the latch argument mutated
// ===========================================================================

/// The LOWERING passes the OLD `i` (the header's param) around the latch
/// instead of `i + 1`. The spec is unchanged, so the header segment's arrival
/// obligation `machine i' == spec i + 1` has a counterexample.
fn lower_with_stale_latch(
    module: &Module,
    func_id: FuncId,
) -> Result<trust_cg_lower::function::Function, String> {
    let mut mutated = module.clone();
    for function in &mut mutated.functions {
        for block in &mut function.blocks {
            if block.id.index() != 2 {
                continue;
            }
            for node in &mut block.body {
                if let Inst::Br { args, .. } = &mut node.inst {
                    *args = vec![v(2)];
                }
            }
        }
    }
    lower_module_to_lir(&mutated, func_id).map_err(|e| e.to_string())
}

fn lower_faithfully(
    module: &Module,
    func_id: FuncId,
) -> Result<trust_cg_lower::function::Function, String> {
    lower_module_to_lir(module, func_id).map_err(|e| e.to_string())
}

#[test]
fn stale_latch_argument_is_refuted() {
    let subject = source(count_to_module(), "count_to");
    let (verdict, _) = verify_trust_ir_output_preserved_with_lowering(
        &subject,
        &backend(),
        lower_with_stale_latch,
    );
    match &verdict {
        OutputVerdict::Refuted { detail } => assert!(
            detail.contains("loop header bb1"),
            "the refutation must name the header whose state is not carried: {detail}"
        ),
        other => panic!(
            "a latch that passes the old `i` never advances the loop where the IR does; the \
             gate must REFUTE it (an Unknown would mean the loop was not modeled): {other:?}"
        ),
    }
}

#[test]
fn hook_with_the_shipping_lowering_still_proves() {
    let subject = source(count_to_module(), "count_to");
    let (verdict, _) =
        verify_trust_ir_output_preserved_with_lowering(&subject, &backend(), lower_faithfully);
    assert!(
        matches!(verdict, OutputVerdict::Proven { .. }),
        "MUTATION CONTROL: the refutation above must come from the stale latch, not the hook: \
         {verdict:?}"
    );
}

// ===========================================================================
// Adversarial shapes
// ===========================================================================

/// An IRREDUCIBLE CFG: two blocks that branch into each other, each entered
/// from the entry — neither header dominates the other's latch.
///
/// ```text
/// bb0(%0: n):  %1 = icmp ult %0, 5; condbr %1, bb1(%0), bb2(%0)
/// bb1(%2: a):  %3 = add %2, 1; %4 = icmp ult %3, %0; condbr %4, bb2(%3), bb3(%3)
/// bb2(%5: b):  %6 = add %5, 2; %7 = icmp ult %6, %0; condbr %7, bb1(%6), bb3(%6)
/// bb3(%8: r):  ret %8
/// ```
fn irreducible_module() -> Module {
    let (mut module, mut f) = u32_module("irreducible", 1);
    let (n, c0, a, a1, ca, bb_, b1, cb, r) = (v(0), v(1), v(2), v(3), v(4), v(5), v(6), v(7), v(8));
    let five = v(9);
    let one = v(10);
    let two = v(11);
    let mut bb0 = Block::new(BlockId::new(0));
    bb0.params.push((n, Ty::U32));
    bb0.body.push(konst(Ty::U32, 5, five));
    bb0.body.push(icmp(ICmpOp::Ult, Ty::U32, n, five, c0));
    bb0.body.push(condbr(c0, (1, vec![n]), (2, vec![n])));
    let mut bb1 = Block::new(BlockId::new(1));
    bb1.params.push((a, Ty::U32));
    bb1.body.push(konst(Ty::U32, 1, one));
    bb1.body.push(add(Ty::U32, a, one, a1));
    bb1.body.push(icmp(ICmpOp::Ult, Ty::U32, a1, n, ca));
    bb1.body.push(condbr(ca, (2, vec![a1]), (3, vec![a1])));
    let mut bb2 = Block::new(BlockId::new(2));
    bb2.params.push((bb_, Ty::U32));
    bb2.body.push(konst(Ty::U32, 2, two));
    bb2.body.push(add(Ty::U32, bb_, two, b1));
    bb2.body.push(icmp(ICmpOp::Ult, Ty::U32, b1, n, cb));
    bb2.body.push(condbr(cb, (1, vec![b1]), (3, vec![b1])));
    let mut bb3 = Block::new(BlockId::new(3));
    bb3.params.push((r, Ty::U32));
    bb3.body.push(ret(r));
    f.blocks.extend([bb0, bb1, bb2, bb3]);
    module.functions.push(f);
    module
}

#[test]
fn irreducible_cfg_is_unknown_by_name() {
    let err = trust_ir_function_semantics(&irreducible_module(), FuncId::new(0))
        .expect_err("an irreducible CFG has no cut points");
    assert!(err.contains("IRREDUCIBLE"), "{err}");
    let subject = source(irreducible_module(), "irreducible");
    let (verdict, _) = verify_trust_ir_output_preserved(&subject, &backend());
    match verdict {
        OutputVerdict::Unknown { reason } => assert!(reason.contains("IRREDUCIBLE"), "{reason}"),
        other => panic!("an irreducible CFG must be Unknown, never Proven or Refuted: {other:?}"),
    }
}

/// NESTED loops: `nested(n) = { let mut t = 0; let mut i = 0; while i < n {
/// let mut j = 0; while j < i { t += 1; j += 1 } i += 1 } t }`.
fn nested_module() -> Module {
    let (mut module, mut f) = u32_module("nested", 1);
    let (n, zero, t, i, c, j, t2, cj, one, t3, j1, i1) =
        (v(0), v(1), v(2), v(3), v(4), v(5), v(6), v(7), v(8), v(9), v(10), v(11));
    let mut bb0 = Block::new(BlockId::new(0));
    bb0.params.push((n, Ty::U32));
    bb0.body.push(konst(Ty::U32, 0, zero));
    bb0.body.push(br(1, vec![zero, zero]));
    // outer header
    let mut bb1 = Block::new(BlockId::new(1));
    bb1.params.push((t, Ty::U32));
    bb1.params.push((i, Ty::U32));
    bb1.body.push(icmp(ICmpOp::Ult, Ty::U32, i, n, c));
    bb1.body.push(condbr(c, (2, vec![zero, t]), (5, vec![])));
    // inner header
    let mut bb2 = Block::new(BlockId::new(2));
    bb2.params.push((j, Ty::U32));
    bb2.params.push((t2, Ty::U32));
    bb2.body.push(icmp(ICmpOp::Ult, Ty::U32, j, i, cj));
    bb2.body.push(condbr(cj, (3, vec![]), (4, vec![])));
    // inner body
    let mut bb3 = Block::new(BlockId::new(3));
    bb3.body.push(konst(Ty::U32, 1, one));
    bb3.body.push(add(Ty::U32, t2, one, t3));
    bb3.body.push(add(Ty::U32, j, one, j1));
    bb3.body.push(br(2, vec![j1, t3]));
    // outer latch
    let mut bb4 = Block::new(BlockId::new(4));
    let one_b = v(12);
    bb4.body.push(konst(Ty::U32, 1, one_b));
    bb4.body.push(add(Ty::U32, i, one_b, i1));
    bb4.body.push(br(1, vec![t2, i1]));
    let mut bb5 = Block::new(BlockId::new(5));
    bb5.body.push(ret(t));
    f.blocks.extend([bb0, bb1, bb2, bb3, bb4, bb5]);
    module.functions.push(f);
    module
}

#[test]
fn nested_loops_are_never_refuted() {
    let spec = trust_ir_function_semantics(&nested_module(), FuncId::new(0)).expect("in fragment");
    assert_eq!(spec.cut_points.len(), 2, "two headers: {:?}", spec.cut_points);
    let subject = source(nested_module(), "nested");
    let (verdict, _) = verify_trust_ir_output_preserved(&subject, &backend());
    assert!(
        !matches!(verdict, OutputVerdict::Refuted { .. }),
        "correct nested loops must never be refuted: {verdict:?}"
    );
    eprintln!("nested loops: {verdict:?}");
}

/// EARLY RETURN from inside the loop: `find(n) = { let mut i = 0; while i < n
/// { if i * 3 == 12 { return i } i += 1 } n }`.
fn early_return_module() -> Module {
    let (mut module, mut f) = u32_module("early_return", 1);
    let (n, zero, i, c, three, m, twelve, hit, one, i1) =
        (v(0), v(1), v(2), v(3), v(4), v(5), v(6), v(7), v(8), v(9));
    let mut bb0 = Block::new(BlockId::new(0));
    bb0.params.push((n, Ty::U32));
    bb0.body.push(konst(Ty::U32, 0, zero));
    bb0.body.push(br(1, vec![zero]));
    let mut bb1 = Block::new(BlockId::new(1));
    bb1.params.push((i, Ty::U32));
    bb1.body.push(icmp(ICmpOp::Ult, Ty::U32, i, n, c));
    bb1.body.push(condbr(c, (2, vec![]), (5, vec![])));
    let mut bb2 = Block::new(BlockId::new(2));
    bb2.body.push(konst(Ty::U32, 3, three));
    bb2.body.push(
        InstrNode::new(Inst::BinOp { op: BinOp::Mul, ty: Ty::U32, lhs: i, rhs: three })
            .with_result(m),
    );
    bb2.body.push(konst(Ty::U32, 12, twelve));
    bb2.body.push(icmp(ICmpOp::Eq, Ty::U32, m, twelve, hit));
    bb2.body.push(condbr(hit, (4, vec![]), (3, vec![])));
    let mut bb3 = Block::new(BlockId::new(3));
    bb3.body.push(konst(Ty::U32, 1, one));
    bb3.body.push(add(Ty::U32, i, one, i1));
    bb3.body.push(br(1, vec![i1]));
    let mut bb4 = Block::new(BlockId::new(4));
    bb4.body.push(ret(i));
    let mut bb5 = Block::new(BlockId::new(5));
    bb5.body.push(ret(n));
    f.blocks.extend([bb0, bb1, bb2, bb3, bb4, bb5]);
    module.functions.push(f);
    module
}

#[test]
fn early_return_from_inside_the_loop_is_proven() {
    assert_proven("early_return", early_return_module());
}

/// A LYING CUT-POINT MAP: the header address claimed is four bytes past the
/// real header (inside the loop's compare/branch), so the machine segment
/// starts mid-header and its arrivals carry a state the spec never predicted.
/// The verdict must be `Unknown` or `Refuted`, NEVER `Proven`.
#[test]
fn lying_cut_point_map_never_proves() {
    let subject = source(count_to_module(), "count_to");
    let obj = assert_proven("count_to", count_to_module());
    let obligation = trust_ir_gate_obligation(&subject, &obj, TrustCgTargetArch::AArch64)
        .expect("the honest map builds an obligation");
    let header = &obligation.segments[1];
    let real = header.machine_addr.expect("the header's address");
    let regs = header.locations.clone();
    // CONTROL: the honest map, claimed, proves.
    let honest = ClaimedCutPoint { block: 1, addr: real, regs: regs.clone() };
    let verdict = verify_trust_ir_bytes_with_claimed_cut_points(
        &subject,
        &obj,
        TrustCgTargetArch::AArch64,
        &[honest],
    );
    assert!(matches!(verdict, OutputVerdict::Proven { .. }), "honest claim: {verdict:?}");
    for lie in [real + 4, real + 8, real.wrapping_sub(4), 0x1_0000] {
        let claim = ClaimedCutPoint { block: 1, addr: lie, regs: regs.clone() };
        let verdict = verify_trust_ir_bytes_with_claimed_cut_points(
            &subject,
            &obj,
            TrustCgTargetArch::AArch64,
            &[claim],
        );
        assert!(
            !matches!(verdict, OutputVerdict::Proven { .. }),
            "a cut-point map claiming {lie:#x} for a header at {real:#x} must not prove: \
             {verdict:?}"
        );
    }
    // A map that swaps the two registers (i in n's register and vice versa)
    // is a lie about the LOCATIONS and must not prove either.
    let swapped = ClaimedCutPoint { block: 1, addr: real, regs: vec![regs[1], regs[0]] };
    let verdict = verify_trust_ir_bytes_with_claimed_cut_points(
        &subject,
        &obj,
        TrustCgTargetArch::AArch64,
        &[swapped],
    );
    assert!(!matches!(verdict, OutputVerdict::Proven { .. }), "swapped registers: {verdict:?}");
    // And a map with NO cut point at all is refused by name.
    let verdict = verify_trust_ir_bytes_with_claimed_cut_points(
        &subject,
        &obj,
        TrustCgTargetArch::AArch64,
        &[],
    );
    match verdict {
        OutputVerdict::Unknown { reason } => {
            assert!(reason.contains("cut-point map: none"), "{reason}")
        }
        other => panic!("{other:?}"),
    }
}

/// `add w<rd>, w<rn>, #imm` (ADD immediate, 32-bit, no shift).
fn add_w_imm(rd: u8, rn: u8, imm: u32) -> u32 {
    0x1100_0000 | (imm << 10) | (u32::from(rn) << 5) | u32::from(rd)
}

/// `movz w<rd>, #0`.
fn movz_w_zero(rd: u8) -> u32 {
    0x5280_0000 | u32::from(rd)
}

/// `nop`.
const NOP: u32 = 0xd503_201f;

/// The `count_to` loop's honest map and its LATCH in the shipping bytes: the
/// word index of the body's immediate `add #1` (the increment of `i`) and of
/// the unconditional back-branch to the header that ends the latch.
struct CountToLatch {
    subject: TrustIrGateSource,
    obj: Vec<u8>,
    claim: ClaimedCutPoint,
    i_reg: u8,
    n_reg: u8,
    text_off: usize,
    add_at: usize,
    add_word: u32,
    back_branch_at: usize,
}

fn count_to_latch() -> CountToLatch {
    let subject = source(count_to_module(), "count_to");
    let obj = assert_proven("count_to", count_to_module());
    let obligation = trust_ir_gate_obligation(&subject, &obj, TrustCgTargetArch::AArch64)
        .expect("the honest map builds an obligation");
    let header = &obligation.segments[1];
    let (i_reg, n_reg) = (header.locations[0], header.locations[1]);
    let header_addr = header.machine_addr.expect("addr");
    let (code, base) = emitted_text(&obj).expect("text");
    let text_off = obj
        .windows(code.len())
        .position(|w| w == code.as_slice())
        .expect("the text bytes are in the object");
    let word = |k: usize| u32::from_le_bytes(code[k * 4..k * 4 + 4].try_into().unwrap());
    let words = code.len() / 4;
    let start = ((header_addr - base) / 4) as usize;
    // ADD (immediate, 32-bit): sf=0 op=0 S=0 100010 sh imm12 Rn Rd, imm12 == 1.
    let add_at = (start..words)
        .find(|&k| word(k) & 0xffc0_0000 == 0x1100_0000 && (word(k) >> 10) & 0xfff == 1)
        .expect("the loop body increments i with an immediate add");
    // B (unconditional): 000101 imm26, target = pc + sext(imm26) * 4.
    let back_branch_at = (add_at..words)
        .find(|&k| {
            let w = word(k);
            let imm26 = i64::from(((w & 0x03ff_ffff) << 6) as i32 >> 6);
            let pc = base as i64 + 4 * k as i64;
            w & 0xfc00_0000 == 0x1400_0000 && pc + 4 * imm26 == header_addr as i64
        })
        .expect("the latch ends in an unconditional branch back to the header");
    let claim = ClaimedCutPoint { block: 1, addr: header_addr, regs: header.locations.clone() };
    CountToLatch {
        subject,
        obj,
        claim,
        i_reg,
        n_reg,
        text_off,
        add_at,
        add_word: word(add_at),
        back_branch_at,
    }
}

impl CountToLatch {
    /// The shipping bytes with the latch's words from the increment up to the
    /// back-branch replaced by `latch`, padded with `nop`.
    fn plant(&self, latch: &[u32]) -> Vec<u8> {
        let room = self.back_branch_at - self.add_at;
        assert!(latch.len() <= room, "the latch has {room} word(s) before its back-branch");
        let mut patched = self.obj.clone();
        for k in 0..room {
            let w = latch.get(k).copied().unwrap_or(NOP);
            let at = self.text_off + (self.add_at + k) * 4;
            patched[at..at + 4].copy_from_slice(&w.to_le_bytes());
        }
        patched
    }

    fn claimed_verdict(&self, bytes: &[u8]) -> OutputVerdict {
        verify_trust_ir_bytes_with_claimed_cut_points(
            &self.subject,
            bytes,
            TrustCgTargetArch::AArch64,
            std::slice::from_ref(&self.claim),
        )
    }
}

/// A CLOBBERED LOOP-INVARIANT LIVE-IN: the latch is replaced by one that
/// still advances `i` in its own register (`add w<i>, w<i>, #1`) and then
/// overwrites the register the map locates `n` in (`movz w<n>, #0`), and the
/// HONEST map is claimed over the patched bytes (the hook-injected map the
/// roadmap names). The patched function is a real miscompile — after one
/// iteration `n` reads as 0, so it returns 1 for every `n >= 2` — and the
/// header segment's arrival check finds `n != CUT n` over the shared variables
/// alone, so the verdict is `Refuted`.
///
/// The CONTROL plants the IR's own latch (`add w<i>, w<i>, #1`, no clobber)
/// through the same rewrite and must stay `Proven`, so the `Refuted` is the
/// clobber's and not the rewrite's.
///
/// (Until trust-cg `0d204a30` the latch incremented `i` in place and this test
/// replaced that `add` with the clobber. The shipping latch is now
/// `add w0, w1, #1; mov w1, w0`, where that same replacement leaves bytes that
/// compute `count_to` exactly; `clobber_the_result_does_not_depend_on_is_not_refuted`
/// pins that case.)
#[test]
fn clobbered_live_in_register_is_refuted() {
    let latch = count_to_latch();
    let increment = add_w_imm(latch.i_reg, latch.i_reg, 1);

    let control = latch.plant(&[increment]);
    let verdict = latch.claimed_verdict(&control);
    assert!(
        matches!(verdict, OutputVerdict::Proven { .. }),
        "the IR's own latch, planted, must stay PROVEN under the honest map: {verdict:?}"
    );

    let patched = latch.plant(&[increment, movz_w_zero(latch.n_reg)]);
    match &latch.claimed_verdict(&patched) {
        OutputVerdict::Refuted { detail } => {
            assert!(detail.contains("loop header bb1"), "{detail}");
        }
        other => {
            panic!("clobbering the live-in's register inside the loop must be REFUTED: {other:?}")
        }
    }
    // Without a claimed map the inferred one cannot locate `n` in a register
    // the loop keeps, and the verdict is a refusal — never Proven.
    let inferred = verify_trust_ir_bytes(&latch.subject, &patched, TrustCgTargetArch::AArch64);
    assert!(!matches!(inferred, OutputVerdict::Proven { .. }), "{inferred:?}");
}

/// The clobber of `n`'s register put in place of the body's `add #1` itself.
/// What that does depends on where the `add` writes, and the gate must say
/// exactly that much:
///
/// * The shipping latch since trust-cg `0d204a30` increments through a
///   temporary (`add w0, w1, #1; mov w1, w0`). Without the `add`, `i`'s
///   register is fed from `w0`, which the cut-point map does not relate to
///   the IR — and which in fact still holds `n`, so the patched function
///   returns `n` for every input (run natively over all 2^32 inputs:
///   0 mismatches; LOOP-CLOBBER-BED-1 in `docs/DECISION_QUEUE.md`). A
///   `Refuted` here would report a miscompile of bytes that compute the IR's
///   result; the verdict must be the map-naming `Unknown`.
/// * A latch that increments `i` in place loses the increment, which IS a
///   miscompile over the shared variables alone, so the verdict is `Refuted`.
///
/// Neither is ever `Proven`, under the honest map or the inferred one.
#[test]
fn clobber_the_result_does_not_depend_on_is_not_refuted() {
    let latch = count_to_latch();
    let mut patched = latch.obj.clone();
    let at = latch.text_off + latch.add_at * 4;
    patched[at..at + 4].copy_from_slice(&movz_w_zero(latch.n_reg).to_le_bytes());
    let add_rd = (latch.add_word & 0x1f) as u8;
    let verdict = latch.claimed_verdict(&patched);
    if add_rd == latch.i_reg {
        assert!(
            matches!(&verdict, OutputVerdict::Refuted { detail } if detail.contains("loop header bb1")),
            "an in-place increment replaced by the clobber is a miscompile: {verdict:?}"
        );
    } else {
        match &verdict {
            OutputVerdict::Unknown { reason } => assert!(
                reason.contains("does not relate to the IR"),
                "the Unknown must name the unrelated state: {reason}"
            ),
            other => panic!(
                "`i` fed from w{add_rd}, a register the map does not relate to the IR, must be \
                 Unknown — never Refuted (the bytes compute count_to), never Proven: {other:?}"
            ),
        }
    }
    let inferred = verify_trust_ir_bytes(&latch.subject, &patched, TrustCgTargetArch::AArch64);
    assert!(!matches!(inferred, OutputVerdict::Proven { .. }), "{inferred:?}");
}

/// A STRAY CUT CANDIDATE: the honest header claim plus a second claimed
/// address (for a block the IR has no loop header at) four bytes into the
/// header's own compare. The header segment then stops there on every path —
/// neither a return nor a matched arrival, which would read as a trap. That
/// indicts the MAP, not the bytes: the verdict is `Unknown` naming the stray,
/// never a fabricated `Refuted`, and never `Proven`.
#[test]
fn stray_cut_candidate_is_unknown_never_refuted() {
    let subject = source(count_to_module(), "count_to");
    let obj = assert_proven("count_to", count_to_module());
    let obligation = trust_ir_gate_obligation(&subject, &obj, TrustCgTargetArch::AArch64)
        .expect("the honest map builds an obligation");
    let header = &obligation.segments[1];
    let real = header.machine_addr.expect("the header's address");
    assert!(
        obligation.segments.iter().all(|s| s.stray_arrivals.is_empty()),
        "the inferred map of the shipping bytes has no strays"
    );
    let honest = ClaimedCutPoint { block: 1, addr: real, regs: header.locations.clone() };
    let stray = ClaimedCutPoint { block: 99, addr: real + 4, regs: Vec::new() };
    let verdict = verify_trust_ir_bytes_with_claimed_cut_points(
        &subject,
        &obj,
        TrustCgTargetArch::AArch64,
        &[honest, stray],
    );
    match &verdict {
        OutputVerdict::Unknown { reason } => {
            assert!(reason.contains("no loop header of the IR claims"), "{reason}");
        }
        other => panic!("a stray cut candidate must be Unknown by name: {other:?}"),
    }
}

/// A MALFORMED CUT-POINT MAP: the map is untrusted input, so every shape it
/// can have must be a NAMED refusal of the gate, never a crash OF the gate.
///
/// Measured before this guard (WS7.14 review): a claim naming `X31` — a
/// register the AArch64 file does not have, the file being `X0..=X30` — was
/// carried straight into `MachineState::gpr[31]` when the header's segment was
/// seeded, and into `MachineArrival::gpr[31]` when its arrival was read, so
/// the gate PANICKED (index out of bounds) on input the roadmap's own design
/// calls untrusted. A panic is not a verdict: an emitter that exported a
/// wrong map would take the compiler down instead of being refused by it.
///
/// Three shapes, one refusal each: a register outside the modeled file, an
/// address outside the emitted text, and an address inside it that is not an
/// instruction boundary.
#[test]
fn a_malformed_cut_point_map_is_refused_by_name_and_never_panics() {
    let subject = source(count_to_module(), "count_to");
    let obj = assert_proven("count_to", count_to_module());
    let obligation = trust_ir_gate_obligation(&subject, &obj, TrustCgTargetArch::AArch64)
        .expect("the honest map builds an obligation");
    let header = &obligation.segments[1];
    let real = header.machine_addr.expect("the header's address");
    let regs = header.locations.clone();
    assert!(!regs.is_empty(), "the header has located live-ins to mis-claim");
    let (_code, base) = emitted_text(&obj).expect("text");

    // (1) A register the file does not have. Every out-of-file number is the
    // same class; X31 is the one an `sp`/`xzr` encoding would be read as.
    for bad in [29u8, 30, 31, 200, u8::MAX] {
        let mut mangled = regs.clone();
        mangled[0] = bad;
        let claim = ClaimedCutPoint { block: 1, addr: real, regs: mangled };
        let verdict = verify_trust_ir_bytes_with_claimed_cut_points(
            &subject,
            &obj,
            TrustCgTargetArch::AArch64,
            &[claim],
        );
        match &verdict {
            OutputVerdict::Unknown { reason } => assert!(
                reason.contains(&format!("X{bad}")) && reason.contains("value registers"),
                "X{bad}: {reason}"
            ),
            other => panic!("a claim naming X{bad} must be Unknown by name: {other:?}"),
        }
    }

    // (2) An address outside the emitted text, and (3) one inside it that is
    // not a 4-byte instruction boundary.
    for bad_addr in [base.wrapping_sub(4), 0xdead_0000u64, real + 1, real + 2, real + 3] {
        let claim = ClaimedCutPoint { block: 1, addr: bad_addr, regs: regs.clone() };
        let verdict = verify_trust_ir_bytes_with_claimed_cut_points(
            &subject,
            &obj,
            TrustCgTargetArch::AArch64,
            &[claim],
        );
        match &verdict {
            OutputVerdict::Unknown { reason } => assert!(
                reason.contains("not a 4-byte-aligned instruction of the emitted text"),
                "{bad_addr:#x}: {reason}"
            ),
            other => panic!("a claim at {bad_addr:#x} must be Unknown by name: {other:?}"),
        }
    }

    // CONTROL: the honest map over the same bytes still proves, so the guard
    // above refuses malformed maps and nothing else.
    let honest = ClaimedCutPoint { block: 1, addr: real, regs };
    let verdict = verify_trust_ir_bytes_with_claimed_cut_points(
        &subject,
        &obj,
        TrustCgTargetArch::AArch64,
        &[honest],
    );
    assert!(matches!(verdict, OutputVerdict::Proven { .. }), "honest control: {verdict:?}");
}

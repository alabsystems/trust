// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Plan step 3.1, family (a) (docs/design/2026-10-02-step3-lean-through-trust-ir.md §9): the
//! carrier gate's SELECT, COMPARISON-VALUE and BOOL-VALUE families, fast-lane-first.
//!
//! Kernel probes first: every admit is a real island declaration, planned and emitted by the
//! sealed-plan emitter (or hand-spelled the way Clean's compiler at the Rust ABI emits it,
//! docs/first-party-pin-ledger.md entry (j)), read by the gate's own reader and decided by the
//! Clean kernel. Every admit is paired with refused mutations, at the structural layer here and
//! at the kernel layer in `src/family.rs`'s unit tests (which bypass the plan agreement).

use clean_kernel::Environment;
use trust_certify::clean_island::CleanIslandSession;
use trust_clean_ir_gate::{
    BoolSpelling, BranchSpelling, FAMILY_SHAPE_TAGS, GATED_SHAPE_TAGS, GatedShape, SelectForm,
    admit_clean_origin, admit_clean_origin_family, gate_reflects_family, gate_targets, read_family,
};
use trust_clean_origin::{CleanOriginPlan, CleanOriginShape, plan_clean_origin_body};
use trust_ir::inst::{ICmpOp, UnOp};
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::node::InstrNode;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{BinOp, Block, Constant, Function, Inst, Producer};

const WIDTHS: [u32; 4] = [8, 16, 32, 64];

fn island(sources: &[String]) -> Environment {
    let mut session = CleanIslandSession::new();
    for source in sources {
        let outcome = session.check(source);
        assert!(!outcome.is_rejected(), "`{source}` must kernel-check: {outcome:?}");
    }
    session.environment().expect("untainted session").clone()
}

fn emitted(env: &Environment, name: &str) -> (CleanOriginPlan, FuncTy, Function) {
    let plan = plan_clean_origin_body(env, name)
        .unwrap_or_else(|refusal| panic!("`{name}` must plan: {refusal:?}"));
    let signature = trust_clean_ir::trust_ir_func_ty(plan.signature())
        .unwrap_or_else(|refusal| panic!("`{name}` signature must lower: {refusal}"));
    let function =
        trust_clean_ir::emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
            .unwrap_or_else(|refusal| panic!("`{name}` must emit: {refusal}"));
    (plan, signature, function)
}

fn sources() -> Vec<String> {
    let mut sources = Vec::new();
    for w in WIDTHS {
        let u = format!("UInt{w}");
        sources.push(format!("def sel{w} (a b : {u}) : {u} := if a < b then a else b"));
        sources.push(format!("def sle{w} (a b : {u}) : {u} := if a <= b then b else a"));
        sources.push(format!("def slit{w} (a b : {u}) : {u} := if a < 10 then a else b"));
        sources.push(format!("def sops{w} (a b : {u}) : {u} := if a < b then a else 0"));
        sources.push(format!("def sbeq{w} (a b : {u}) : {u} := if a == b then a else b"));
        sources.push(format!("def clt{w} (a b : {u}) : Bool := a < b"));
        sources.push(format!("def cle{w} (a b : {u}) : Bool := a <= b"));
        sources.push(format!("def ceq{w} (a b : {u}) : Bool := a == b"));
        sources.push(format!("def cgt{w} (a b : {u}) : Bool := b < a"));
    }
    sources.push("def bnot (b : Bool) : Bool := not b".to_string());
    sources.push("def band (a : Bool) (b : Bool) : Bool := a && b".to_string());
    sources.push("def bor (a : Bool) (b : Bool) : Bool := a || b".to_string());
    sources
}

/// Admit, then authenticate the placeholder and the relocated published subject.
fn admit_and_authenticate(
    env: &Environment,
    name: &str,
    plan: &CleanOriginPlan,
    signature: &FuncTy,
    function: &Function,
) -> GatedShape {
    let token = admit_clean_origin_family(env, plan, 7, name, signature, function)
        .unwrap_or_else(|refusal| panic!("`{name}` family gate refused: {}", refusal.note()));
    assert_eq!(token.method_tag(), "definitional-equality");
    token
        .authenticate(name, 7, name, signature, function)
        .unwrap_or_else(|refusal| panic!("`{name}` token refused: {}", refusal.note()));
    let mut published = function.clone();
    published.id = FuncId::new(21);
    published.ty = FuncTyId::new(4);
    published.producer = Some(Producer::Clean);
    let sealed = token
        .authenticate_published(name, 7, name, signature, function, &published)
        .unwrap_or_else(|refusal| panic!("`{name}` publication: {}", refusal.note()));
    assert_eq!(sealed.shape(), token.shape());
    assert_ne!(sealed.subject_digest(), token.subject_digest());
    // The join's targeting is untouched: none of these is a carrier-gate TARGET, and the
    // original entry point keeps refusing them.
    assert!(!gate_targets(plan), "`{name}` must not become a join target");
    assert!(gate_reflects_family(plan), "`{name}` is family coverage");
    let refusal = admit_clean_origin(env, plan, 7, name, signature, function)
        .expect_err("the original entry point admits only its four target shapes");
    assert_eq!(refusal.stage(), "target-shape", "{}", refusal.note());
    token.shape()
}

#[test]
fn family_tags_are_the_collector_renderings_and_the_join_targets_did_not_move() {
    let collector = include_str!("../../../compiler/rustc_mir_transform/src/clean_origin_ir.rs");
    for tag in FAMILY_SHAPE_TAGS {
        assert!(collector.contains(&format!("=> \"{tag}\",")), "collector renders no `{tag}`");
    }
    assert_eq!(GATED_SHAPE_TAGS, &["wrapping-binop", "projection", "constant-uint", "composed"]);
    for tag in FAMILY_SHAPE_TAGS {
        assert!(!GATED_SHAPE_TAGS.contains(tag), "`{tag}` must not be a join target tag");
    }
}

/// KERNEL PROBES, sealed-plan spelling (`icmp` + `select`; `icmp` + `ret`; `not`/`and`/`or`), at
/// every width.
#[test]
fn every_family_plan_admits_in_the_emitter_spelling_at_every_width() {
    let env = island(&sources());
    let mut admitted = 0;
    for w in WIDTHS {
        let select = |form| GatedShape::Select { spelling: BranchSpelling::SelectInst, form };
        for (name, shape_matches, expected) in [
            (format!("sel{w}"), "Select", select(SelectForm::Params)),
            (format!("sle{w}"), "Select", select(SelectForm::Params)),
            (format!("slit{w}"), "SelectLiteral", select(SelectForm::Literal)),
            (format!("sops{w}"), "SelectOperands", select(SelectForm::Operands)),
            (format!("sbeq{w}"), "SelectBeq", select(SelectForm::Params)),
            (format!("clt{w}"), "DecideComparison", GatedShape::ComparisonValue),
            (format!("cle{w}"), "DecideComparison", GatedShape::ComparisonValue),
            (format!("ceq{w}"), "DecideComparison", GatedShape::ComparisonValue),
            (format!("cgt{w}"), "DecideComparison", GatedShape::ComparisonValue),
        ] {
            let (plan, signature, function) = emitted(&env, &name);
            assert!(
                format!("{:?}", plan.shape()).starts_with(&format!("{shape_matches} ")),
                "`{name}` must plan as {shape_matches}, got {:?}",
                plan.shape()
            );
            assert_eq!(admit_and_authenticate(&env, &name, &plan, &signature, &function), expected);
            admitted += 1;
        }
    }
    for (name, expected) in [
        ("bnot", GatedShape::BoolNot { spelling: BoolSpelling::Operator }),
        ("band", GatedShape::BoolConnective { spelling: BoolSpelling::Operator }),
        ("bor", GatedShape::BoolConnective { spelling: BoolSpelling::Operator }),
    ] {
        let (plan, signature, function) = emitted(&env, name);
        assert_eq!(admit_and_authenticate(&env, name, &plan, &signature, &function), expected);
        admitted += 1;
    }
    assert_eq!(admitted, 39);
}

fn node(inst: Inst, result: Option<u32>) -> InstrNode {
    let node = InstrNode::new(inst);
    match result {
        Some(id) => node.with_result(ValueId::new(id)),
        None => node,
    }
}

fn ret(value: u32) -> InstrNode {
    node(Inst::Return { values: vec![ValueId::new(value)] }, None)
}

/// `name(a, b)` as Clean's compiler at the Rust ABI spells `if a <pred> b then <t> else <e>`:
/// an `icmp` + `condbr` diamond with one `ret` per arm. An arm is `Ok(param)` or `Err(literal)`.
fn diamond(
    name: &str,
    ty: Ty,
    pred: ICmpOp,
    rhs: Result<u32, i128>,
    then_arm: Result<u32, i128>,
    else_arm: Result<u32, i128>,
) -> Function {
    let mut function = Function::new(FuncId::new(0), name, FuncTyId::new(0), BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.params = vec![(ValueId::new(0), ty.clone()), (ValueId::new(1), ty.clone())];
    let mut next = 2;
    let rhs = match rhs {
        Ok(param) => param,
        Err(literal) => {
            entry.body.push(node(
                Inst::Const { ty: ty.clone(), value: Constant::Int(literal) },
                Some(next),
            ));
            next += 1;
            next - 1
        }
    };
    let cond = next;
    next += 1;
    entry.body.push(node(
        Inst::ICmp { op: pred, ty: ty.clone(), lhs: ValueId::new(0), rhs: ValueId::new(rhs) },
        Some(cond),
    ));
    entry.body.push(node(
        Inst::CondBr {
            cond: ValueId::new(cond),
            then_target: BlockId::new(1),
            then_args: vec![],
            else_target: BlockId::new(2),
            else_args: vec![],
        },
        None,
    ));
    function.blocks.push(entry);
    for (id, arm) in [(1, then_arm), (2, else_arm)] {
        let mut block = Block::new(BlockId::new(id));
        match arm {
            Ok(param) => block.body.push(ret(param)),
            Err(literal) => {
                block.body.push(node(
                    Inst::Const { ty: ty.clone(), value: Constant::Int(literal) },
                    Some(next),
                ));
                block.body.push(ret(next));
                next += 1;
            }
        }
        function.blocks.push(block);
    }
    function
}

/// `name(a, b)` (or `name(b)`) as Clean's compiler spells a Bool operation: `select` over Bool
/// constants. `consts` are defined first (ids 2.., or 1.. for a unary op), then the select.
fn bool_select(
    name: &str,
    arity: u32,
    consts: &[bool],
    cond: u32,
    then_val: u32,
    else_val: u32,
) -> Function {
    let mut function = Function::new(FuncId::new(0), name, FuncTyId::new(0), BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.params = (0..arity).map(|i| (ValueId::new(i), Ty::Bool)).collect();
    let mut next = arity;
    for value in consts {
        entry
            .body
            .push(node(Inst::Const { ty: Ty::Bool, value: Constant::Bool(*value) }, Some(next)));
        next += 1;
    }
    entry.body.push(node(
        Inst::Select {
            ty: Ty::Bool,
            cond: ValueId::new(cond),
            then_val: ValueId::new(then_val),
            else_val: ValueId::new(else_val),
        },
        Some(next),
    ));
    entry.body.push(ret(next));
    function.blocks.push(entry);
    function
}

/// KERNEL PROBES, Clean's-compiler spelling: the `icmp` + `condbr` diamond with one `ret` per
/// branch, `==` as `icmp eq`, and the Bool operations as `select`.
#[test]
fn the_core_spellings_admit_against_the_same_declarations() {
    let env = island(&sources());
    for w in WIDTHS {
        let ty = match w {
            8 => Ty::U8,
            16 => Ty::U16,
            32 => Ty::U32,
            _ => Ty::U64,
        };
        let d = |form| GatedShape::Select { spelling: BranchSpelling::Diamond, form };
        for (name, function, expected) in [
            (
                format!("sel{w}"),
                diamond(&format!("sel{w}"), ty.clone(), ICmpOp::Ult, Ok(1), Ok(0), Ok(1)),
                d(SelectForm::Params),
            ),
            (
                format!("sle{w}"),
                diamond(&format!("sle{w}"), ty.clone(), ICmpOp::Ule, Ok(1), Ok(1), Ok(0)),
                d(SelectForm::Params),
            ),
            (
                format!("slit{w}"),
                diamond(&format!("slit{w}"), ty.clone(), ICmpOp::Ult, Err(10), Ok(0), Ok(1)),
                d(SelectForm::Literal),
            ),
            (
                format!("sops{w}"),
                diamond(&format!("sops{w}"), ty.clone(), ICmpOp::Ult, Ok(1), Ok(0), Err(0)),
                d(SelectForm::Operands),
            ),
            (
                format!("sbeq{w}"),
                diamond(&format!("sbeq{w}"), ty.clone(), ICmpOp::Eq, Ok(1), Ok(0), Ok(1)),
                d(SelectForm::Params),
            ),
        ] {
            let (plan, signature, _) = emitted(&env, &name);
            assert_eq!(admit_and_authenticate(&env, &name, &plan, &signature, &function), expected);
        }
    }
    let s = BoolSpelling::Select;
    for (name, function, expected) in [
        (
            "band",
            bool_select("band", 2, &[false], 0, 1, 2),
            GatedShape::BoolConnective { spelling: s },
        ),
        (
            "bor",
            bool_select("bor", 2, &[true], 0, 2, 1),
            GatedShape::BoolConnective { spelling: s },
        ),
        (
            "bnot",
            bool_select("bnot", 1, &[false, true], 0, 1, 2),
            GatedShape::BoolNot { spelling: s },
        ),
    ] {
        let (plan, signature, _) = emitted(&env, name);
        assert_eq!(admit_and_authenticate(&env, name, &plan, &signature, &function), expected);
    }
}

fn refuse(
    env: &Environment,
    name: &str,
    signature: &FuncTy,
    function: &Function,
    plan: &CleanOriginPlan,
    stage: &str,
) {
    let refusal = admit_clean_origin_family(env, plan, 7, name, signature, function)
        .expect_err(&format!("`{name}` mutation must be refused at `{stage}`"));
    assert_eq!(refusal.stage(), stage, "`{name}`: {}", refusal.note());
}

fn select_node(function: &mut Function) -> &mut Inst {
    function.blocks[0]
        .body
        .iter_mut()
        .map(|n| &mut n.inst)
        .find(|inst| matches!(inst, Inst::Select { .. }))
        .expect("a select")
}

fn icmp_node(function: &mut Function) -> &mut Inst {
    function.blocks[0]
        .body
        .iter_mut()
        .map(|n| &mut n.inst)
        .find(|inst| matches!(inst, Inst::ICmp { .. }))
        .expect("an icmp")
}

/// STRUCTURAL CONTROLS: every admit above has refused mutations. The plan must agree with the
/// body field for field; the reader accounts for every instruction.
#[test]
fn family_mutations_are_refused_structurally() {
    let env = island(&sources());
    // Select, emitter spelling.
    let (plan, signature, function) = emitted(&env, "sel64");
    let mut swapped = function.clone();
    if let Inst::Select { then_val, else_val, .. } = select_node(&mut swapped) {
        std::mem::swap(then_val, else_val);
    }
    refuse(&env, "sel64", &signature, &swapped, &plan, "plan-shape");
    let mut le = function.clone();
    if let Inst::ICmp { op, .. } = icmp_node(&mut le) {
        *op = ICmpOp::Ule;
    }
    refuse(&env, "sel64", &signature, &le, &plan, "plan-shape");
    let mut ugt = function.clone();
    if let Inst::ICmp { op, .. } = icmp_node(&mut ugt) {
        *op = ICmpOp::Ugt;
    }
    refuse(&env, "sel64", &signature, &ugt, &plan, "comparison");
    let mut operands = function.clone();
    if let Inst::ICmp { lhs, rhs, .. } = icmp_node(&mut operands) {
        std::mem::swap(lhs, rhs);
    }
    refuse(&env, "sel64", &signature, &operands, &plan, "plan-shape");
    let mut dead = function.clone();
    dead.blocks[0]
        .body
        .insert(0, node(Inst::Const { ty: Ty::U64, value: Constant::Int(1) }, Some(9)));
    refuse(&env, "sel64", &signature, &dead, &plan, "shape");
    let mut narrow = function.clone();
    if let Inst::Select { ty, .. } = select_node(&mut narrow) {
        *ty = Ty::U32;
    }
    refuse(&env, "sel64", &signature, &narrow, &plan, "instruction-type");
    let mut renamed = function.clone();
    renamed.name = "other".to_string();
    refuse(&env, "sel64", &signature, &renamed, &plan, "subject-name");
    // The literal is the body's: an off-by-one literal disagrees with the plan.
    let (plan, signature, function) = emitted(&env, "slit64");
    let mut off = function.clone();
    for n in &mut off.blocks[0].body {
        if let Inst::Const { value, .. } = &mut n.inst {
            *value = Constant::Int(11);
        }
    }
    refuse(&env, "slit64", &signature, &off, &plan, "plan-shape");
    // A literal shared by two uses is not the emitted vocabulary.
    let (plan, signature, function) = emitted(&env, "sops64");
    let mut shared = function.clone();
    let c = shared.blocks[0]
        .body
        .iter()
        .find(|n| matches!(n.inst, Inst::Const { .. }))
        .map(|n| n.results[0])
        .expect("a const arm");
    if let Inst::Select { then_val, .. } = select_node(&mut shared) {
        *then_val = c;
    }
    refuse(&env, "sops64", &signature, &shared, &plan, "shape");

    // Diamond controls.
    let (plan, signature, _) = emitted(&env, "sel64");
    let good = diamond("sel64", Ty::U64, ICmpOp::Ult, Ok(1), Ok(0), Ok(1));
    let mut same_target = good.clone();
    if let Inst::CondBr { else_target, .. } =
        &mut same_target.blocks[0].body.last_mut().unwrap().inst
    {
        *else_target = BlockId::new(1);
    }
    refuse(&env, "sel64", &signature, &same_target, &plan, "control-flow");
    let mut args = good.clone();
    if let Inst::CondBr { then_args, .. } = &mut args.blocks[0].body.last_mut().unwrap().inst {
        then_args.push(ValueId::new(0));
    }
    refuse(&env, "sel64", &signature, &args, &plan, "control-flow");
    let mut arm_param = good.clone();
    arm_param.blocks[1].params.push((ValueId::new(7), Ty::U64));
    refuse(&env, "sel64", &signature, &arm_param, &plan, "control-flow");
    let mut extra = good.clone();
    extra.blocks.push(Block::new(BlockId::new(3)));
    refuse(&env, "sel64", &signature, &extra, &plan, "control-flow");
    let swapped_arms = diamond("sel64", Ty::U64, ICmpOp::Ult, Ok(1), Ok(1), Ok(0));
    refuse(&env, "sel64", &signature, &swapped_arms, &plan, "plan-shape");

    // Comparison controls.
    let (plan, signature, function) = emitted(&env, "clt64");
    let mut flipped = function.clone();
    if let Inst::ICmp { op, .. } = icmp_node(&mut flipped) {
        *op = ICmpOp::Ule;
    }
    refuse(&env, "clt64", &signature, &flipped, &plan, "plan-shape");
    let mut wide = function.clone();
    if let Inst::ICmp { ty, .. } = icmp_node(&mut wide) {
        *ty = Ty::U32;
    }
    refuse(&env, "clt64", &signature, &wide, &plan, "instruction-type");

    // Bool controls.
    let (plan, signature, function) = emitted(&env, "band");
    // The emitter spells `&&` as `band` (WS5.13); `bor` in its place reads as `or` and the plan
    // disagrees.
    let mut or = function.clone();
    for n in &mut or.blocks[0].body {
        if let Inst::BinOp { op, .. } = &mut n.inst {
            assert_eq!(*op, BinOp::BAnd, "the emitter spells `&&` as `band`");
            *op = BinOp::BOr;
        }
    }
    refuse(&env, "band", &signature, &or, &plan, "plan-shape");
    // The pre-WS5.13 integer `and` at `bool` is no producer's spelling any more.
    let mut integer_and = function.clone();
    for n in &mut integer_and.blocks[0].body {
        if let Inst::BinOp { op, .. } = &mut n.inst {
            *op = BinOp::And;
        }
    }
    refuse(&env, "band", &signature, &integer_and, &plan, "instruction");
    let mut commuted = function.clone();
    for n in &mut commuted.blocks[0].body {
        if let Inst::BinOp { lhs, rhs, .. } = &mut n.inst {
            std::mem::swap(lhs, rhs);
        }
    }
    refuse(&env, "band", &signature, &commuted, &plan, "plan-shape");
    let not_a_connective = bool_select("band", 2, &[true], 0, 1, 2);
    refuse(&env, "band", &signature, &not_a_connective, &plan, "shape");
    let (plan, signature, function) = emitted(&env, "bnot");
    // The emitter spells `not b` as `bxor %b, true` (WS5.13): `Const true`, `bxor`, `ret`.
    let [truth, bxor, _] = function.blocks[0].body.as_slice() else {
        panic!("`bnot` emits three instructions: {:?}", function.blocks[0].body);
    };
    assert!(matches!(truth.inst, Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) }));
    let Inst::BinOp { op: BinOp::BXor, ty: Ty::Bool, lhs, rhs } = bxor.inst else {
        panic!("`bnot` is not `bxor`: {:?}", bxor.inst);
    };
    // A wrong operator at `bool` (the integer `xor`) is no Bool operation.
    let mut neg = function.clone();
    if let Inst::BinOp { op, .. } = &mut neg.blocks[0].body[1].inst {
        *op = BinOp::Xor;
    }
    refuse(&env, "bnot", &signature, &neg, &plan, "instruction");
    // `bxor %b, false` is the identity, not `not`.
    let mut identity = function.clone();
    if let Inst::Const { value, .. } = &mut identity.blocks[0].body[0].inst {
        *value = Constant::Bool(false);
    }
    refuse(&env, "bnot", &signature, &identity, &plan, "shape");
    // The reversed operands `bxor true, %b` are not the emitter's spelling.
    let mut reversed = function.clone();
    if let Inst::BinOp { lhs: l, rhs: r, .. } = &mut reversed.blocks[0].body[1].inst {
        (*l, *r) = (rhs, lhs);
    }
    refuse(&env, "bnot", &signature, &reversed, &plan, "shape");
    // The pre-WS5.13 `UnOp::Not` at scalar `bool` (which the trust-ir validator refuses) is
    // no producer's spelling any more.
    let mut unop_not = function.clone();
    unop_not.blocks[0].body.remove(0);
    unop_not.blocks[0].body[0].inst = Inst::UnOp { op: UnOp::Not, ty: Ty::Bool, operand: lhs };
    refuse(&env, "bnot", &signature, &unop_not, &plan, "instruction");
    // A body of one family under a plan of another.
    let (_, _, select_body) = emitted(&env, "sel64");
    let (cmp_plan, cmp_signature, _) = emitted(&env, "clt64");
    let mut renamed = select_body.clone();
    renamed.name = "clt64".to_string();
    assert!(
        admit_clean_origin_family(&env, &cmp_plan, 7, "clt64", &cmp_signature, &renamed).is_err()
    );
}

/// A plan outside the families, or at a carrier they do not cover, is not family coverage.
///
/// Family (a) is PARTIAL (step-3 review, 2026-10-05): design §9 3.1(a) also names `RawBinOp`
/// and `SelectBeqGeneral` (a `==` select over a computed operand), and neither has a family
/// reader yet. Pinned here so the coverage claim in docs/TCB.md's carrier-gate row cannot drift
/// from the code.
#[test]
fn plans_outside_the_families_are_not_covered() {
    let env = island(&[
        "def wsum (a b : UInt64) : UInt64 := a + b".to_string(),
        "def bsel (p : Bool) (a b : UInt64) : UInt64 := if p then a else b".to_string(),
        "def bandu (a b : UInt64) : UInt64 := a &&& b".to_string(),
        "def bxor (a b : UInt64) : UInt64 := a ^^^ b".to_string(),
        "def bqg (a b : UInt64) : UInt64 := if (a == b) = false then a else b".to_string(),
        "def bqgc (a b : UInt64) : UInt64 := if (a &&& 3) == 0 then a else b".to_string(),
    ]);
    let plan = plan_clean_origin_body(&env, "wsum").expect("wsum plans");
    assert!(matches!(plan.shape(), CleanOriginShape::WrappingBinOp { .. }));
    assert!(!gate_reflects_family(&plan));
    if let Ok(plan) = plan_clean_origin_body(&env, "bsel") {
        assert!(!gate_reflects_family(&plan), "a Bool-scrutinee select is outside the family");
    }
    // Spelled by the sealed-plan emitter, read by no family: the family entry mints nothing.
    for (name, tag) in [("bandu", "raw-binop"), ("bqg", "select-beq-general")] {
        let (plan, signature, function) = emitted(&env, name);
        match (name, plan.shape()) {
            ("bandu", CleanOriginShape::RawBinOp { .. })
            | ("bqg", CleanOriginShape::SelectBeqGeneral { .. }) => {}
            (_, shape) => panic!("`{name}` planned as {shape:?}"),
        }
        assert!(!gate_reflects_family(&plan), "`{name}` is not family coverage yet");
        assert!(!FAMILY_SHAPE_TAGS.contains(&tag), "`{tag}` is not a family tag yet");
        assert!(
            admit_clean_origin_family(&env, &plan, 7, name, &signature, &function).is_err(),
            "`{name}`: no family token for an uncovered shape"
        );
    }
    // Planned but not spelled by the sealed-plan emitter at all, so there is no trust-ir row to
    // gate: `a ^^^ b` (the D38 leaf's shape; the emitter's `RawBinOp` arm spells only `&&&` and
    // `|||` and refuses `^^^`, `>>>`, `/` and `%`) and a `==` select over a computed operand.
    for name in ["bxor", "bqgc"] {
        let plan = plan_clean_origin_body(&env, name).expect("plans");
        match (name, plan.shape()) {
            ("bxor", CleanOriginShape::RawBinOp { .. })
            | ("bqgc", CleanOriginShape::SelectBeqGeneral { .. }) => {}
            (_, shape) => panic!("`{name}` planned as {shape:?}"),
        }
        assert!(!gate_reflects_family(&plan));
        assert!(
            trust_clean_ir::emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
                .is_err(),
            "the emitter now spells `{name}`: give it family coverage or move this pin"
        );
    }
}

/// The admitted emitter body computes min at the edge inputs (the reference interpreter), and
/// so does the admitted diamond: the kernel verdict and the execution agree.
#[test]
fn admitted_select_bodies_execute_min_at_the_edges() {
    let env = island(&sources());
    let (plan, signature, function) = emitted(&env, "sel64");
    admit_clean_origin_family(&env, &plan, 1, "m::sel64", &signature, &function).expect("admits");
    let reading = read_family(&signature, &function).expect("reads");
    assert!(format!("{reading:?}").contains("SelectInst"));
    let core = diamond("sel64", Ty::U64, ICmpOp::Ult, Ok(1), Ok(0), Ok(1));
    admit_clean_origin_family(&env, &plan, 1, "m::sel64", &signature, &core)
        .expect("the diamond admits");
    let reading = read_family(&signature, &core).expect("reads");
    assert!(format!("{reading:?}").contains("Diamond"));
    for (spelling, body) in [("select", &function), ("diamond", &core)] {
        for (a, b) in [(0u64, 1u64), (1, 0), (u64::MAX, u64::MAX - 1), (7, 7), (0, u64::MAX)] {
            let outcome = Interpreter::new()
                .execute_function(
                    body,
                    vec![
                        InterpretValue::int(Ty::U64, i128::from(a)).expect("a"),
                        InterpretValue::int(Ty::U64, i128::from(b)).expect("b"),
                    ],
                )
                .unwrap_or_else(|error| panic!("the admitted {spelling} executes: {error:?}"));
            let got = outcome.returns[0].as_int().expect("integer").as_unsigned();
            assert_eq!(got, u128::from(a.min(b)), "{spelling} sel64({a}, {b})");
        }
    }
}

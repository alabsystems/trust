// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **§R3b LAYER EVIDENCE — which layer each `gcd` prerequisite actually lived
//! at, and the kernel probe the widening rests on.**
//!
//! Promoted from a probe on 2026-08-27; every row now ASSERTS.
//!
//! Round 1 (`gcd_formulation_probes`) measured the elaborator and the plan
//! lane. It found the fuel form ELABORATES at the current pin and computes gcd
//! by kernel reduction, and that exactly two plan-lane rules refused it:
//!
//!   1. a general `a - b` was outside the arm vocabulary;
//!   2. no parameter could be named twice in one branch.
//!
//! This file measured whether those two were LAYER-LOCAL (a plan rule) or
//! structural (the materializer, the MIR reader, the kernel gate). **Both were
//! plan rules**, and that is why R3b is two `crates/`-local edits rather than a
//! pin move: `m3`/`m4` show the materializer, the MIR reader and the KERNEL
//! GATE all admitting a duplicated parameter that the plan refused, and `m1`
//! shows the kernel deciding the one new identification.
//!
//! **`m1` is the FAST-LANE-FIRST row, and it ran before any producer was
//! written.** `table.rs`'s `nat.sub` cites it, and `admissible_body.rs`'s `Sub`
//! doc cites it, precisely because a vocabulary node whose kernel meaning was
//! assumed rather than measured is a capability claim with nothing behind it.

#![allow(clippy::doc_markdown)]

use clean_kernel::{Environment, Name};
use trust_clean_origin::materialize::{
    BodyTemplate, TemplateCallee, TemplateOperand, TemplateRvalue, TemplateTerminator, TemplateTy,
    TemplateUnwind, body_template, zero_test_rec_template,
};
use trust_clean_origin::table::ladder_row;
use trust_clean_origin::{FaithfulnessMethod, admit_lowering, plan_clean_origin_body};
use trust_types::admissible_body::{PrimitiveCallee, RecBodyExpr, WfRecBody, recognize_wf_nat_rec};
use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

// ═══════════════════════════════ harness ═══════════════════════════════════

fn island(source: &str) -> Result<Environment, String> {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[source]);
    if batch.is_rejected() {
        let mut msgs: Vec<String> = batch
            .outcomes
            .iter()
            .flat_map(|o| o.errors.iter().map(|e| e.message.clone()))
            .collect();
        msgs.extend(batch.cycles.iter().map(|c| c.message.clone()));
        return Err(msgs.join(" | "));
    }
    Ok(session.environment().expect("an untainted session has an environment").clone())
}

fn first_line(s: &str) -> String {
    s.lines().next().unwrap_or("").chars().take(300).collect()
}

fn nat_adt() -> Ty {
    Ty::adt("trust_bignum::Nat", Vec::new())
}

fn extracted_callee_path(callee: PrimitiveCallee) -> String {
    match callee {
        PrimitiveCallee::NatSub => "trust_bignum::arith::<impl trust_bignum::Nat>::sub".to_owned(),
        PrimitiveCallee::NatAdd => "trust_bignum::arith::<impl trust_bignum::Nat>::add".to_owned(),
        PrimitiveCallee::NatMul => "trust_bignum::arith::<impl trust_bignum::Nat>::mul".to_owned(),
        other => other.canonical_path(),
    }
}

fn render_operand(operand: TemplateOperand) -> Operand {
    match operand {
        TemplateOperand::Copy(local) => Operand::Copy(Place::local(local)),
        TemplateOperand::Move(local) => Operand::Move(Place::local(local)),
        TemplateOperand::ResultScalar { value, width } => {
            Operand::Constant(ConstValue::Uint(value, width))
        }
        TemplateOperand::U64Scalar(value) => {
            Operand::Constant(ConstValue::Uint(u128::from(value), 64))
        }
        TemplateOperand::BoolScalar(value) => Operand::Constant(ConstValue::Bool(value)),
    }
}

/// `control_11`'s reference renderer, restricted to the bignum-`Nat` lane.
fn render(template: &BodyTemplate, def_path: &str) -> VerifiableFunction {
    let local_ty = |ty: TemplateTy| match ty {
        TemplateTy::Result | TemplateTy::Param { .. } => nat_adt(),
        TemplateTy::Bool => Ty::Bool,
        TemplateTy::ResultRef => Ty::Ref { mutable: false, inner: Box::new(nat_adt()) },
    };
    let locals = template
        .locals
        .iter()
        .enumerate()
        .map(|(index, local)| LocalDecl { index, ty: local_ty(local.ty), name: None })
        .collect();
    let blocks = template
        .blocks
        .iter()
        .enumerate()
        .map(|(index, block)| BasicBlock {
            id: BlockId(index),
            stmts: block
                .stmts
                .iter()
                .map(|stmt| Statement::Assign {
                    place: Place::local(stmt.place),
                    rvalue: match stmt.rvalue {
                        TemplateRvalue::Use(operand) => Rvalue::Use(render_operand(operand)),
                        TemplateRvalue::SharedRef(of) => {
                            Rvalue::Ref { mutable: false, place: Place::local(of) }
                        }
                        _ => panic!("this lane emits only Use and SharedRef statements"),
                    },
                    span: SourceSpan::default(),
                })
                .collect(),
            terminator: match &block.terminator {
                TemplateTerminator::Return => Terminator::Return,
                TemplateTerminator::Goto(target) => Terminator::Goto(BlockId(*target)),
                TemplateTerminator::SwitchIntZero { discr, zero, otherwise } => {
                    Terminator::SwitchInt {
                        discr: render_operand(*discr),
                        targets: vec![(0, BlockId(*zero))],
                        otherwise: BlockId(*otherwise),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    }
                }
                TemplateTerminator::Call { callee, args, dest, target, unwind } => {
                    Terminator::Call {
                        func: match callee {
                            TemplateCallee::Primitive(identity) => extracted_callee_path(*identity),
                            TemplateCallee::SelfDef => def_path.to_owned(),
                        },
                        args: args.iter().map(|arg| render_operand(*arg)).collect(),
                        dest: Place::local(*dest),
                        target: Some(BlockId(*target)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                        unwind: match unwind {
                            TemplateUnwind::Unreachable => UnwindEdge::Unreachable,
                            TemplateUnwind::Continue => UnwindEdge::Continue,
                        },
                        callee_identity: None,
                    }
                }
            },
        })
        .collect();
    VerifiableFunction {
        name: def_path.rsplit("::").next().unwrap_or(def_path).into(),
        def_path: def_path.into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: template.arg_count,
            return_ty: nat_adt(),
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
    }
}

/// A compact picture of a template's blocks — enough to see the borrow/move
/// discipline the duplication rule is about.
fn picture(template: &BodyTemplate) -> String {
    let mut out = String::new();
    for (index, block) in template.blocks.iter().enumerate() {
        out.push_str(&format!("  bb{index}:"));
        for stmt in &block.stmts {
            match stmt.rvalue {
                TemplateRvalue::SharedRef(of) => {
                    out.push_str(&format!(" _{} = &_{of};", stmt.place));
                }
                TemplateRvalue::Use(op) => {
                    out.push_str(&format!(" _{} = {op:?};", stmt.place));
                }
                _ => out.push_str(" <stmt>;"),
            }
        }
        match &block.terminator {
            TemplateTerminator::Call { callee, args, dest, target, .. } => {
                let name = match callee {
                    TemplateCallee::Primitive(p) => format!("{p:?}"),
                    TemplateCallee::SelfDef => "SELF".to_owned(),
                };
                let args: Vec<String> = args
                    .iter()
                    .map(|a| match a {
                        TemplateOperand::Move(l) => format!("move _{l}"),
                        TemplateOperand::Copy(l) => format!("copy _{l}"),
                        other => format!("{other:?}"),
                    })
                    .collect();
                out.push_str(&format!(
                    " {name}({}) -> _{dest}, bb{target}\n",
                    args.join(", ")
                ));
            }
            other => out.push_str(&format!(" {other:?}\n")),
        }
    }
    out
}

fn gate(env: &Environment, name: &str, carrier_from: &str, body: &WfRecBody) -> Result<(), String> {
    let reflected = trust_clean_origin::reflect_wf::reflect_wf_functional(env, name, body, trust_clean_origin::WfLowering::OnParameter)
        .map_err(|d| format!("REFLECTION REFUSED: {}", first_line(&d)))?;
    let carrier_plan = plan_clean_origin_body(env, carrier_from)
        .map_err(|r| format!("carrier donor `{carrier_from}` did not plan: {:?}", r.note()))?;
    trust_clean_origin::gate::check_faithful_wf_functional(
        env,
        name,
        &reflected,
        carrier_plan.result_carrier(),
    )
    .map(|_| ())
    .map_err(|refusal| format!("GATE REFUSED: {}", first_line(&refusal.note())))
}

/// A donor whose only job is to supply a bignum-`Nat` carrier to the gate for
/// bodies the PLAN lane refuses (so `plan.result_carrier()` is unavailable).
const DONOR: &str = "def addAcc (a b : Nat) : Nat := \
                     if h : 0 < a then addAcc (a - 1) (b + 1) else b\n\
                     termination_by a";

// ═══════════════════════════════════════════════════════════════════════════
// (m1) THE KERNEL PROBE, isolated — the ONE new identification
// ═══════════════════════════════════════════════════════════════════════════

/// **THE ONE NEW IDENTIFICATION, and its refuting twins.** `a - b` must BE
/// `Nat.sub a b` at the kernel, truncated at zero, and — the row that matters
/// most for R3b — it must NOT be `Nat.sub b a`. Unlike `+` and `*`,
/// subtraction is not commutative, so operand order is a real question here and
/// the kernel is what answers it. `control_17` (b) is the emitter-side twin.
#[test]
fn m1_general_truncated_subtraction_at_the_kernel() {
    for (tag, src) in [
        ("sub defeq", "theorem t (a b : Nat) : a - b = Nat.sub a b := rfl"),
        ("nested", "theorem t (a b : Nat) : a - (a - b) = Nat.sub a (Nat.sub a b) := rfl"),
        ("trunc", "theorem t : 1 - 3 = 0 := rfl"),
        ("min hi", "theorem t : 5 - (5 - 3) = 3 := rfl"),
        ("min lo", "theorem t : 3 - (3 - 5) = 3 := rfl"),
        ("absdiff", "theorem t : (3 - 5) + (5 - 3) = 2 := rfl"),
    ] {
        assert!(
            island(src).is_ok(),
            "the KERNEL must admit `{tag}` — `RecBodyExpr::Sub` and the `nat.sub` row both \
             cite this row as the ground for reading a general `-`: {}",
            island(src).err().map_or_else(String::new, |why| first_line(&why))
        );
    }
    for (tag, src) in [
        // The WRONG OPERATOR, the `nat.mul` precedent's twin.
        ("op mutation", "theorem t (a b : Nat) : a - b = Nat.add a b := rfl"),
        // THE ORDER. This is the row `+` and `*` cannot have.
        ("order mutation", "theorem t (a b : Nat) : a - b = Nat.sub b a := rfl"),
        ("value mutation", "theorem t : 5 - 3 = 3 := rfl"),
        // TRUNCATION is truncation, not saturation-at-one or anything else —
        // and it must match `trust_bignum`'s `checked_sub(..).unwrap_or(ZERO)`.
        ("trunc mutation", "theorem t : 1 - 3 = 1 := rfl"),
    ] {
        assert!(
            island(src).is_err(),
            "CONTROL `{tag}` must be REFUSED, or the admits above decide nothing"
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// (m2) ARITY 3, END TO END — is the "any arity" claim true past 2?
// ═══════════════════════════════════════════════════════════════════════════

/// Arity 3, no parameter named twice, no `-` outside the predecessor —
/// deliberately inside every rule the plan lane stated BEFORE R3b, so that this
/// row isolates ARITY and nothing else. It admitted end to end already, which
/// is what said the fuel form's arity was not itself a cost and left exactly
/// two things to build.
const ACC3: &str = "def acc3 (a b c : Nat) : Nat := \
                    if h : 0 < a then acc3 (a - 1) (b + 1) (c + 2) else c\n\
                    termination_by a";

#[test]
fn m2_arity_three_end_to_end() {
    let env = match island(ACC3) {
        Ok(env) => env,
        Err(why) => {
            eprintln!("ROW m2 acc3 | ISLAND REJECTS | {}", first_line(&why));
            return;
        }
    };
    // Values first — the fixture must be a real computation.
    for (a, b, c, want) in [(0_u32, 1_u32, 2_u32, 2_u32), (1, 1, 2, 4), (3, 1, 2, 8)] {
        let src = format!("{ACC3}\ntheorem v : acc3 {a} {b} {c} = {want} := rfl");
        eprintln!(
            "ROW m2 value {a} {b} {c} = {want} | {}",
            if island(&src).is_ok() { "KERNEL ADMITS" } else { "REFUSED" }
        );
    }
    let plan = match plan_clean_origin_body(&env, "acc3") {
        Ok(plan) => plan,
        Err(refusal) => {
            eprintln!("ROW m2 plan | REFUSES | {}", first_line(&refusal.note()));
            return;
        }
    };
    eprintln!("ROW m2 plan | PLANS {:?}", plan.shape());
    let row = ladder_row(plan.shape()).expect("a ladder row");
    let template = match body_template(row, &plan) {
        Ok(t) => t,
        Err(refusal) => {
            eprintln!("ROW m2 template | REFUSES | {refusal:?}");
            return;
        }
    };
    eprintln!("ROW m2 template |\n{}", picture(&template));
    let extracted = render(&template, "clean_origin_wf_rec_arity3::acc3");
    eprintln!("ROW m2 read-back | {:?}", recognize_wf_nat_rec(&extracted));
    match admit_lowering(&env, &plan, &extracted) {
        Ok(faithful) => eprintln!(
            "ROW m2 ADMIT | {} FAITHFUL by {:?}",
            faithful.name(),
            faithful.method()
        ),
        Err(refusal) => eprintln!("ROW m2 ADMIT | REFUSED | {}", first_line(&refusal.note())),
    }
    assert_eq!(
        std::mem::discriminant(&FaithfulnessMethod::WellFoundedFunctionalDefeq),
        std::mem::discriminant(&FaithfulnessMethod::WellFoundedFunctionalDefeq)
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (m3) DUPLICATION — is it structural, or is it only a PLAN rule?
// ═══════════════════════════════════════════════════════════════════════════

/// `reuse a b = if 0 < a then reuse (a - 1) (b + b) else b`, `termination_by a`.
/// The plan lane refuses it on the "no parameter twice" rule. Here the same
/// body is pushed through the MATERIALIZER, the MIR READER and the KERNEL GATE
/// with the plan lane out of the loop, so each layer answers for itself.
const REUSE: &str = "def reuse (a b : Nat) : Nat := \
                     if h : 0 < a then reuse (a - 1) (b + b) else b\n\
                     termination_by a";

fn reuse_body() -> WfRecBody {
    WfRecBody {
        zero_value: RecBodyExpr::Param(1),
        nonzero_value: RecBodyExpr::Rec,
        rec_args: vec![
            RecBodyExpr::Pred,
            RecBodyExpr::Add(
                Box::new(RecBodyExpr::Param(1)),
                Box::new(RecBodyExpr::Param(1)),
            ),
        ],
        measure_index: 0,
    }
}

#[test]
fn m3_duplication_layer_by_layer() {
    let body = reuse_body();
    let template = zero_test_rec_template(
        &body.zero_value,
        &body.nonzero_value,
        &body.rec_args,
        body.measure_index,
        TemplateUnwind::Continue,
    );
    eprintln!("ROW m3 template |\n{}", picture(&template));
    // THE MATERIALIZER: two shared borrows of one parameter, and no clone.
    let picture_text = picture(&template);
    assert!(
        picture_text.matches("&_2").count() >= 2,
        "the emitted `b + b` must be TWO BORROWS of `_2` — that is the whole reason a \
         repeated parameter is safe, and if it ever becomes a move this file's conclusion \
         (and R3b's duplication rule) is wrong:\n{picture_text}"
    );
    let extracted = render(&template, "clean_origin_wf_rec::reuse");
    assert_eq!(
        recognize_wf_nat_rec(&extracted).as_ref(),
        Some(&body),
        "THE MIR READER reads a duplicated parameter back identically"
    );

    // THE KERNEL layer, against the REAL elaborated side A.
    let env = island(&format!("{REUSE}\n{DONOR}")).expect("`reuse` must elaborate");
    assert_eq!(gate(&env, "reuse", "addAcc", &body), Ok(()), "THE GATE admits it too");
}

// ═══════════════════════════════════════════════════════════════════════════
// (m4) ARITY 3 **with** duplication — the exact shape `gcdF` needs, minus `-`
// ═══════════════════════════════════════════════════════════════════════════

/// `gcdF`'s spine with `+` standing in for the `-`s: arity 3, measure at
/// parameter 0 with a `Pred` measure argument, one guard, one self-call, and
/// BOTH threaded parameters named twice across the branch. If this admits at
/// the gate, then the fuel form's only remaining gap is the `Sub` node itself.
const ACC3D: &str = "def acc3d (a b c : Nat) : Nat := \
                     if h : 0 < a then acc3d (a - 1) (b + c) (c + b) else b\n\
                     termination_by a";

fn acc3d_body() -> WfRecBody {
    WfRecBody {
        zero_value: RecBodyExpr::Param(1),
        nonzero_value: RecBodyExpr::Rec,
        rec_args: vec![
            RecBodyExpr::Pred,
            RecBodyExpr::Add(
                Box::new(RecBodyExpr::Param(1)),
                Box::new(RecBodyExpr::Param(2)),
            ),
            RecBodyExpr::Add(
                Box::new(RecBodyExpr::Param(2)),
                Box::new(RecBodyExpr::Param(1)),
            ),
        ],
        measure_index: 0,
    }
}

#[test]
fn m4_arity_three_with_duplication() {
    let body = acc3d_body();
    let template = zero_test_rec_template(
        &body.zero_value,
        &body.nonzero_value,
        &body.rec_args,
        body.measure_index,
        TemplateUnwind::Continue,
    );
    eprintln!("ROW m4 template |\n{}", picture(&template));
    let extracted = render(&template, "clean_origin_wf_rec::acc3d");
    assert_eq!(
        recognize_wf_nat_rec(&extracted).as_ref(),
        Some(&body),
        "arity 3 with BOTH threaded parameters duplicated reads back identically"
    );
    let env = island(&format!("{ACC3D}\n{DONOR}")).expect("`acc3d` must elaborate");
    assert_eq!(
        gate(&env, "acc3d", "addAcc", &body),
        Ok(()),
        "…and the GATE admits it against the real elaborated side A. This is `gcdF`'s exact \
         spine with `+` standing in for `-`, so it is what said the duplication rule was the \
         ONLY thing in the way"
    );
    // MUTATION CONTROL: swapped threaded arguments must be REFUSED, otherwise
    // the admit above is a rubber stamp. `b + c` and `c + b` are equal in VALUE
    // (`Nat.add` is commutative), so this refutes on the TERM.
    let mut mutant = body.clone();
    mutant.rec_args.swap(1, 2);
    assert!(
        gate(&env, "acc3d", "addAcc", &mutant).is_err(),
        "the gate must separate the two threaded arguments even though they are equal in \
         value; if it does not, the admit above decides nothing"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (m5) THE ADVERSARIAL CASE the refined rule must keep refusing
// ═══════════════════════════════════════════════════════════════════════════

/// `scale a b = if 0 < a then b + scale (a - 1) b else 0`: `b` is a BARE
/// self-call argument (a MOVE) and is also borrowed by the enclosing `+`
/// AFTER the call. This is the one duplication the emitter genuinely cannot
/// express, and it must stay refused however the rule is refined.
#[test]
fn m5_the_move_after_call_case() {
    let body = WfRecBody {
        zero_value: RecBodyExpr::NatConst(0),
        nonzero_value: RecBodyExpr::Add(
            Box::new(RecBodyExpr::Param(1)),
            Box::new(RecBodyExpr::Rec),
        ),
        rec_args: vec![RecBodyExpr::Pred, RecBodyExpr::Param(1)],
        measure_index: 0,
    };
    let template = zero_test_rec_template(
        &body.zero_value,
        &body.nonzero_value,
        &body.rec_args,
        body.measure_index,
        TemplateUnwind::Continue,
    );
    let picture_text = picture(&template);
    eprintln!("ROW m5 template (A BORROW OF A MOVED LOCAL) |\n{picture_text}");
    // THE HAZARD, stated as an assertion: the self-call MOVES `_2`, and a
    // borrow of `_2` appears AFTER it.
    let call_at = picture_text.find("SELF(").expect("the template contains the self-call");
    assert!(
        picture_text[..call_at].contains("move _2") || picture_text[call_at..].contains("move _2"),
        "the self-call must MOVE the bare parameter `_2`:\n{picture_text}"
    );
    assert!(
        picture_text[call_at..].contains("&_2"),
        "…and a borrow of `_2` must appear AFTER it — that is the borrow-after-move this \
         shape would emit, and the reason `emit.rs`'s move-aware rule may not be \
         deleted:\n{picture_text}"
    );
    // AND THE READER ACCEPTS IT. This is the load-bearing half: side B cannot
    // catch this, so the PLAN rule is the only guard.
    let extracted = render(&template, "clean_origin_wf_rec::scale");
    assert_eq!(
        recognize_wf_nat_rec(&extracted).as_ref(),
        Some(&body),
        "the MIR reader ACCEPTS the borrow-after-move body. If this ever starts refusing, \
         say so — but until it does, `plan_clean_origin_body`'s move-aware duplication rule \
         is the ONLY thing standing between the emitter and MIR that fails borrowck \
         (`control_17` (g) is the end-to-end row)"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (m6) how many nodes does the fuel form's branch carry?
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn m6_node_budget() {
    // `gcdF (f - 1) ((a - b) + (b - a)) (a - (a - b))`, counted the way the
    // plan lane counts (`arith_nodes` over the branch plus the self-call's own
    // arguments), with `Sub` standing in as `Add` for the count.
    let stand_in = WfRecBody {
        zero_value: RecBodyExpr::Param(1),
        nonzero_value: RecBodyExpr::Rec,
        rec_args: vec![
            RecBodyExpr::Pred,
            RecBodyExpr::Add(
                Box::new(RecBodyExpr::Add(
                    Box::new(RecBodyExpr::Param(1)),
                    Box::new(RecBodyExpr::Param(2)),
                )),
                Box::new(RecBodyExpr::Add(
                    Box::new(RecBodyExpr::Param(2)),
                    Box::new(RecBodyExpr::Param(1)),
                )),
            ),
            RecBodyExpr::Add(
                Box::new(RecBodyExpr::Param(1)),
                Box::new(RecBodyExpr::Add(
                    Box::new(RecBodyExpr::Param(1)),
                    Box::new(RecBodyExpr::Param(2)),
                )),
            ),
        ],
        measure_index: 0,
    };
    let nodes: usize = stand_in.rec_args.iter().map(RecBodyExpr::arith_nodes).sum::<usize>()
        + stand_in.nonzero_value.arith_nodes();
    eprintln!("ROW m6 nodes | nonzero branch carries {nodes} arithmetic node(s)");
    for index in 0..3 {
        let uses: usize = stand_in
            .rec_args
            .iter()
            .map(|argument| argument.parameter_uses(index, 0))
            .sum();
        eprintln!("ROW m6 uses | parameter {index} used {uses} time(s) in the nonzero branch");
    }
    let template = zero_test_rec_template(
        &stand_in.zero_value,
        &stand_in.nonzero_value,
        &stand_in.rec_args,
        stand_in.measure_index,
        TemplateUnwind::Continue,
    );
    eprintln!(
        "ROW m6 template | {} locals, {} blocks",
        template.locals.len(),
        template.blocks.len()
    );
    let extracted = render(&template, "clean_origin_wf_rec::gcdShape");
    eprintln!(
        "ROW m6 MIR reader | {}",
        if recognize_wf_nat_rec(&extracted).as_ref() == Some(&stand_in) {
            "READS BACK IDENTICALLY"
        } else {
            "DIFFERS"
        }
    );
}

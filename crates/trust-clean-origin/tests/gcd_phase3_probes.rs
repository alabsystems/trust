// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **§R3d — THE TWO-ARGUMENT `gcd`, PLANNED, EMITTED AND GATED.**
//!
//! The pin (`first-party/clean` `4f7bdab766`) carries the ratified side A:
//!
//! ```text
//! def gcdB (a b : Nat) : Nat :=
//!   if h : 0 < b then gcdB ((a-b)+(b-a)) (a-(a-b)) else a
//! termination_by a + 2*b
//! ```
//!
//! It is `first-party/clean`'s SUM-MEASURE lowering (WF phase 3): the measure
//! names both parameters, so the fix runs on the measure's VALUE. R3c taught
//! this crate's readers that shape and left the call lane refusing it. This file
//! is the measurement R3d rests on, and every row is a DECISION with a refuting
//! sibling.
//!
//! # What each probe decides
//!
//! | probe | decides |
//! |---|---|
//! | p1 | the SIZES — why the 4,096-node envelope had to move, and what actually fills it |
//! | p2 | the phase-3 de Bruijn LAYOUT, read out of the elaborated body binder by binder |
//! | p3 | the PLAN — `gcdB` plans, with the guard on parameter 1 and both legs read |
//! | p4 | the BORROW's kernel identification, and the three positions side B may not author |
//! | p5 | the WHOLE ROUTE — materialize, read back, reflect, gate — FAITHFUL |
//! | p6 | phase 2 is UNMOVED: `countdownSum`, `addAcc`, `fact` and `gcdF` still plan identically |
//!
//! # THE ONE THING THIS FILE MAY NOT BE READ AS SAYING
//!
//! It does not say `gcd` is PROVED correct. `gcd_final_probes` n1 measures that
//! `Nat.gcd` is ABSENT from the prelude, so there is no prelude gcd to state
//! agreement with. What is decided here is that the compiler emits a body the
//! KERNEL identifies with side A's own functional — and separately
//! (`tests/ui/trust/clean_origin_wf_rec_gcd_direct.rs`) that closed
//! applications of the emitted binary reduce to the numerals the kernel decides
//! for the same closed applications of side A.

#![allow(clippy::doc_markdown)]

use clean_kernel::{BinderData, Environment, Expr, ExprKind, Name, TypeChecker};
use trust_clean_origin::materialize::{
    BodyTemplate, TemplateCallee, TemplateOperand, TemplateRvalue, TemplateTerminator, TemplateTy,
    TemplateUnwind, body_template,
};
use trust_clean_origin::table::ladder_row;
use trust_clean_origin::{
    CleanOriginShape, DECREASE_SLOT_SENTINEL, FaithfulnessMethod, MEASURE_SLOT_SENTINEL,
    ReflectedWfFunctional, WfLowering, admit_lowering, check_faithful_wf_functional,
    plan_clean_origin_body, read_wf_sum_measure_anatomy,
};
use trust_types::admissible_body::{
    PrimitiveCallee, RecBodyExpr, recognize_wf_nat_rec, recognize_wf_sum_measure_rec,
};
use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

// ═══════════════════════════════════════════════════════════════════════════
// harness
// ═══════════════════════════════════════════════════════════════════════════

/// **THE RATIFIED SIDE A.** Byte-identical to the text the pin carries.
pub const GCDB: &str = "def gcdB (a b : Nat) : Nat := \
                        if h : 0 < b then gcdB ((a-b)+(b-a)) (a-(a-b)) else a\n\
                        termination_by a + 2*b";

fn island(source: &str) -> Result<Environment, String> {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[source]);
    if batch.is_rejected() {
        let mut msgs: Vec<String> = batch
            .outcomes
            .iter()
            .flat_map(|outcome| outcome.errors.iter().map(|error| error.message.clone()))
            .collect();
        msgs.extend(batch.cycles.iter().map(|cycle| cycle.message.clone()));
        return Err(msgs.join(" | "));
    }
    Ok(session.environment().expect("an untainted session has an environment").clone())
}

fn gcdb_env() -> Environment {
    island(GCDB).unwrap_or_else(|why| {
        panic!(
            "the PIN must still elaborate the ratified two-argument `gcd`; this whole lane is \
             about the shape it lowers to: {why}"
        )
    })
}

fn body_of(env: &Environment, name: &str) -> Expr {
    env.get_const(&Name::from_string(name))
        .and_then(|constant| constant.value.clone())
        .unwrap_or_else(|| panic!("`{name}` must be a definition with a value"))
}

/// Core-expression nodes, the same counting the traversal envelopes apply.
fn nodes(expr: &Expr) -> usize {
    match expr.kind() {
        ExprKind::App(function, argument) => 1 + nodes(function) + nodes(argument),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => 1 + nodes(ty) + nodes(body),
        ExprKind::Let(_, ty, value, body, _) => 1 + nodes(ty) + nodes(value) + nodes(body),
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => 1 + nodes(inner),
        _ => 1,
    }
}

/// Core-expression NESTING DEPTH — the longest root-to-leaf chain, which is the
/// number of Rust stack frames a direct recursive walk over this term consumes.
///
/// This is the number R3e's STACK rail is measured against; `nodes` above is
/// the number the R3d WORK rail is measured against, and p1's whole point is
/// that the two are not proportional.
///
/// Computed with an explicit worklist rather than recursively, so that a term
/// deep enough to defeat a recursive walk cannot also defeat the helper that
/// measures it.
fn depth(expr: &Expr) -> usize {
    let mut deepest = 0usize;
    let mut pending: Vec<(&Expr, usize)> = vec![(expr, 1)];
    while let Some((node, level)) = pending.pop() {
        deepest = deepest.max(level);
        let next = level + 1;
        match node.kind() {
            ExprKind::App(function, argument) => {
                pending.push((function, next));
                pending.push((argument, next));
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                pending.push((ty, next));
                pending.push((body, next));
            }
            ExprKind::Let(_, ty, value, body, _) => {
                pending.push((ty, next));
                pending.push((value, next));
                pending.push((body, next));
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => pending.push((inner, next)),
            _ => {}
        }
    }
    deepest
}

fn nat_adt() -> Ty {
    Ty::adt("trust_bignum::Nat", Vec::new())
}

fn nat_carrier() -> trust_clean_carrier::Carrier {
    trust_clean_carrier::carrier_for(&Expr::const_(Name::from_string("Nat"), vec![]))
        .expect("I6: Nat carries at trust_bignum::Nat")
}

const SELF_PATH: &str = "gcd_phase3::gcdB";

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

/// `control_11`'s reference renderer, restricted to the bignum-`Nat` lane. It
/// renders the MATERIALIZER's own template, so the body this file gates is the
/// body the compiler would emit and not one written here.
pub fn render(template: &BodyTemplate, def_path: &str) -> VerifiableFunction {
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

/// The body the MATERIALIZER produces for a plan, rendered into the form the
/// MIR reader consumes.
pub fn emitted(env: &Environment, name: &str) -> VerifiableFunction {
    let plan = plan_clean_origin_body(env, name).expect("the fixture plans");
    let row = ladder_row(plan.shape()).expect("its shape selects a ladder row");
    let template = body_template(row, &plan).expect("the materializer realizes it");
    render(&template, SELF_PATH)
}

/// The planned shape this file pins everywhere. `Decreasing` is the GUARDED
/// parameter — `b`, source 1 — and `Param(0)` is `a`.
pub fn planned_shape() -> CleanOriginShape {
    CleanOriginShape::WellFoundedNatRec {
        zero_value: RecBodyExpr::Param(0),
        nonzero_value: RecBodyExpr::Rec,
        rec_args: vec![
            // `(a - b) + (b - a)` — |a - b| at `Nat`'s truncated subtraction.
            RecBodyExpr::Add(
                Box::new(RecBodyExpr::Sub(
                    Box::new(RecBodyExpr::Param(0)),
                    Box::new(RecBodyExpr::Decreasing),
                )),
                Box::new(RecBodyExpr::Sub(
                    Box::new(RecBodyExpr::Decreasing),
                    Box::new(RecBodyExpr::Param(0)),
                )),
            ),
            // `a - (a - b)` — min a b at the same.
            RecBodyExpr::Sub(
                Box::new(RecBodyExpr::Param(0)),
                Box::new(RecBodyExpr::Sub(
                    Box::new(RecBodyExpr::Param(0)),
                    Box::new(RecBodyExpr::Decreasing),
                )),
            ),
        ],
        measure_index: 1,
        lowering: WfLowering::OnMeasureValue,
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// (p1) THE SIZES
// ═══════════════════════════════════════════════════════════════════════════

/// **WHY THE 4,096-NODE ENVELOPE HAD TO MOVE, stated as a measurement.**
///
/// Before R3d both functional walks — `emit::scan_sum_measure_calls` and
/// `gate::walk_functional` — refused `gcdB` on their traversal envelope, and the
/// refusal named the envelope rather than anything about the program. This row
/// says what actually fills it: the CASCADE'S DECREASE PROOF, which is the one
/// component side B never authors and the comparison is blind to.
///
/// Recorded as an assertion rather than a comment so that a future cascade which
/// outgrows the new envelope fails HERE, with its own number, instead of
/// surfacing as an opaque refusal about a term nobody wrote.
///
/// # R3e: it also measures the DEPTH, and that is a different rail
///
/// Raising the node budget to 262,144 raised the worst-case DESCENT of three
/// direct Rust recursions by the same factor of 64, because until then the node
/// budget was incidentally their stack guard. `emit::SUM_MEASURE_DEPTH_LIMIT`
/// is the explicit rail that replaced it, and it is derived from two numbers:
/// the widest measured frame, and the depth of the deepest term this lane has
/// ever been shown — which is the one measured here. The row therefore prints
/// and pins BOTH sizes: 14,283 nodes at **53 levels** is the whole argument
/// that a node budget is not a depth budget.
#[test]
fn p1_the_decrease_proof_is_what_fills_the_traversal_envelope() {
    let env = gcdb_env();
    let anatomy = read_wf_sum_measure_anatomy(&body_of(&env, "gcdB"))
        .expect("the phase-3 reader must read the ratified side A");

    let functional = nodes(anatomy.functional());
    assert_eq!(anatomy.calls().len(), 1);
    let proof = nodes(anatomy.calls()[0].decrease_proof());
    let measure = nodes(anatomy.measure());

    let functional_depth = depth(anatomy.functional());
    let proof_depth = depth(anatomy.calls()[0].decrease_proof());

    eprintln!("ROW p1 | functional {functional} nodes | decrease proof {proof} | measure {measure}");
    eprintln!(
        "ROW p1 | functional DEPTH {functional_depth} | decrease proof DEPTH {proof_depth}"
    );

    assert!(
        proof > 4_096,
        "the premise of the envelope move is that side A's decrease proof ALONE exceeds the old \
         4,096-node budget; measured {proof}. If this has become small, re-measure the envelope \
         rather than leaving it at a number nothing supports"
    );
    assert!(
        functional - proof < 512,
        "…and that everything ELSE in the functional is tiny: the guard, the two branch values \
         and the self-call's arguments come to {} nodes. That asymmetry is the whole argument \
         for raising a walk budget rather than narrowing a fragment",
        functional - proof
    );
    assert!(
        functional < 262_144,
        "the functional must fit the envelope the two walks now carry; measured {functional}"
    );
    // R3e. The STACK rail is derived from this number, so a cascade that grows
    // DEEP rather than merely LARGE has to fail here, with its measurement,
    // rather than as a depth refusal about a program nobody wrote. 256 leaves
    // room to grow well before it reaches the rail itself.
    assert!(
        functional_depth < 256,
        "the deepest real functional this lane has been shown is what \
         `emit::SUM_MEASURE_DEPTH_LIMIT` is sized against; measured {functional_depth} levels. \
         If this is climbing, re-derive the depth rail (and re-measure the frame width it \
         divides) before it starts refusing real programs"
    );
    assert!(
        proof_depth <= functional_depth,
        "the decrease proof is the deep part as well as the large part, and it sits inside the \
         functional; {proof_depth} against {functional_depth} would mean the reader handed back \
         components that do not nest"
    );
    // The decrease proof is the CASCADE's, not a `sorry` and not an axiom.
    assert!(!anatomy.calls()[0].decrease_proof().has_sorry());
    let foundational = ["propext", "Quot.sound", "Classical.choice"];
    let offending: Vec<String> = env
        .axiom_deps(&Name::from_string("gcdB"))
        .expect("the declaration has an axiom closure")
        .iter()
        .map(ToString::to_string)
        .filter(|axiom| !foundational.contains(&axiom.as_str()))
        .collect();
    assert!(
        offending.is_empty(),
        "side A's closure must be foundational-only — one assumed decrease switches the kernel's \
         own termination evidence off (r2_axiom_closure_probes c1). Got {offending:?}"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (p2) THE LAYOUT
// ═══════════════════════════════════════════════════════════════════════════

/// **THE PHASE-3 de BRUIJN LAYOUT, read out of the elaborated body.**
///
/// Every index in `emit::WfLayout`, `reflect::RecCall` and `gate::WfBorrowLayout`
/// is computed from these numbers. They are asserted against LITERALS here, read
/// from the elaborator's own term, because a layout agreed between two of this
/// crate's own functions is a crate talking to itself.
#[test]
fn p2_the_phase3_layout_is_the_elaborators_own() {
    let env = gcdb_env();
    let anatomy = read_wf_sum_measure_anatomy(&body_of(&env, "gcdB")).expect("reads");
    assert_eq!(anatomy.arity(), 2);

    // The telescope: `n, rec, a, b, hm` — FIVE binders at arity 2.
    let mut telescope: Vec<Expr> = Vec::new();
    let mut cursor = anatomy.functional().clone();
    while let ExprKind::Lam(_, ty, inner) = cursor.kind() {
        telescope.push((**ty).clone());
        cursor = (**inner).clone();
    }
    assert_eq!(telescope.len(), 5, "n, rec, a, b, hm");
    assert_eq!(telescope.len(), WfLowering::OnMeasureValue.functional_binders(2));

    // THE GUARD sits on `b` — SOURCE PARAMETER 1 — and `b` is `BVar(1)` at the
    // functional's body. That is the number `WfLayout::measure_at_body` computes
    // as `arity - measure_index` = 2 - 1.
    let ExprKind::App(..) = cursor.kind() else { panic!("the functional's body is the `dite`") };
    let (dite_head, dite_args) = uncurry(&cursor);
    assert!(is_const(dite_head, "dite"));
    assert_eq!(dite_args.len(), 5);
    let guard = dite_args[1];
    assert!(
        guard.collect_constants().contains(&Name::from_string("instLTNat")),
        "the guard arrives in the SURFACE `<` spelling through the prelude instance"
    );
    assert!(
        mentions_bvar(guard, 1),
        "the guard tests `BVar(1)` — `b`, source parameter 1, at the functional's body"
    );
    assert!(
        !mentions_bvar(guard, 4),
        "and NOT `BVar(4)`, which is `n`, the course-of-values bound. Phase 3's guard is on a \
         SOURCE PARAMETER; that is the whole difference from phase 2 at the guard"
    );

    // THE SELF-CALL, under the guard's hypothesis binder (depth 1).
    let call = &anatomy.calls()[0];
    assert_eq!(call.depth(), 1);
    assert_eq!(call.arguments().len(), 2, "one per source parameter");
    // `a` is `BVar(3)` and `b` is `BVar(2)` there — `arity + 1 - i`.
    assert!(mentions_bvar(&call.arguments()[0], 3) && mentions_bvar(&call.arguments()[0], 2));
    // The MEASURE `a + 2*b`, in the seed's own spelling (`a` = #1, `b` = #0).
    assert!(anatomy.measure().collect_constants().contains(&Name::from_string("HMul.hMul")));
    assert_eq!(
        *call.major(),
        anatomy.measure().lift(2),
        "the major premise is the measure lifted to the call site — `depth + 1`, which is 2 here"
    );

    // The four numbers every downstream layout is a function of.
    let phase3 = WfLowering::OnMeasureValue;
    assert_eq!(phase3.spine_arguments(2), 9);
    assert_eq!(phase3.functional_binders(2), 5);
    assert_eq!(phase3.rec_binder_depth(2), 3);
    assert_eq!(phase3.rec_call_arity(2), 5);
    assert_eq!(phase3.decrease_slot_position(2), 4);
}

fn uncurry(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args: Vec<&Expr> = Vec::new();
    let mut head = expr;
    while let ExprKind::App(function, argument) = head.kind() {
        args.push(argument);
        head = function;
    }
    args.reverse();
    (head, args)
}

fn is_const(expr: &Expr, name: &str) -> bool {
    matches!(expr.kind(), ExprKind::Const(n, _) if *n == Name::from_string(name))
}

fn mentions_bvar(expr: &Expr, index: u32) -> bool {
    match expr.kind() {
        &ExprKind::BVar(seen) => seen == index,
        ExprKind::App(function, argument) => {
            mentions_bvar(function, index) || mentions_bvar(argument, index)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            mentions_bvar(ty, index) || mentions_bvar(body, index + 1)
        }
        ExprKind::MData(_, inner) | ExprKind::Proj(_, _, inner) => mentions_bvar(inner, index),
        _ => false,
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// (p3) THE PLAN
// ═══════════════════════════════════════════════════════════════════════════

/// **`gcdB` PLANS.** The shape is compared against a literal written out here,
/// so a change in what the compiler reads out of side A fails visibly rather
/// than being absorbed.
#[test]
fn p3_the_two_argument_gcd_plans() {
    let env = gcdb_env();
    let plan = plan_clean_origin_body(&env, "gcdB")
        .unwrap_or_else(|refusal| panic!("`gcdB` must PLAN: {}", refusal.note()));
    assert_eq!(plan.signature().arity(), 2);
    assert_eq!(plan.shape(), &planned_shape());

    // The guard is on parameter 1, DISCOVERED rather than assumed — the whole
    // reason phase 3 needs its own planner arm.
    let CleanOriginShape::WellFoundedNatRec { measure_index, lowering, .. } = plan.shape() else {
        panic!("the shape is the well-founded one");
    };
    assert_eq!(*measure_index, 1, "`0 < b`, not `0 < a`");
    assert_eq!(*lowering, WfLowering::OnMeasureValue);

    // A CONTROL at the same layer: the same body with the guard on `a` is a
    // DIFFERENT function, and the compiler must read it as one. (It is refused
    // rather than planned, because its decrease cascade does not go through —
    // which is the honest outcome and is asserted as such.)
    let flipped = island(
        "def gcdFlip (a b : Nat) : Nat := \
         if h : 0 < a then gcdFlip ((a-b)+(b-a)) (a-(a-b)) else a\n\
         termination_by a + 2*b",
    );
    assert!(
        flipped.is_err()
            || plan_clean_origin_body(&flipped.clone().unwrap(), "gcdFlip")
                .map(|plan| plan.shape() != &planned_shape())
                .unwrap_or(true),
        "guarding the OTHER parameter must not produce this plan — the guard index is read from \
         the term, not defaulted"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (p4) THE BORROW — the kernel identification, before the producer
// ═══════════════════════════════════════════════════════════════════════════

/// Rebuild side A's functional with `edit` applied to the single self-call's
/// arguments, keeping every binder. Used to build side B and every adversarial
/// variant of it FROM SIDE A's own term, which is what makes the controls differ
/// from the admit in exactly one place.
fn side_b_from(
    functional: &Expr,
    arity: usize,
    binder_edit: &dyn Fn(usize, &Expr) -> Expr,
    arg_edit: &dyn Fn(usize, &Expr) -> Expr,
) -> Expr {
    fn go(expr: &Expr, depth: u32, edit: &dyn Fn(usize, &Expr) -> Expr) -> Expr {
        match expr.kind() {
            ExprKind::App(function, argument) => {
                let mut args: Vec<&Expr> = Vec::new();
                let mut head = expr;
                while let ExprKind::App(inner_fn, inner_arg) = head.kind() {
                    args.push(inner_arg);
                    head = inner_fn;
                }
                args.reverse();
                if matches!(head.kind(), &ExprKind::BVar(index) if index == depth) {
                    let mut rebuilt = head.clone();
                    for (position, argument) in args.iter().enumerate() {
                        rebuilt = Expr::app(rebuilt, edit(position, argument));
                    }
                    return rebuilt;
                }
                Expr::app(go(function, depth, edit), go(argument, depth, edit))
            }
            ExprKind::Lam(binder, ty, body) => {
                Expr::lam(*binder, go(ty, depth, edit), go(body, depth + 1, edit))
            }
            ExprKind::Pi(binder, ty, body) => {
                Expr::pi(*binder, go(ty, depth, edit), go(body, depth + 1, edit))
            }
            _ => expr.clone(),
        }
    }
    let mut telescope: Vec<(BinderData, Expr)> = Vec::new();
    let mut cursor = functional.clone();
    for _ in 0..WfLowering::OnMeasureValue.functional_binders(arity) {
        let ExprKind::Lam(binder, ty, inner) = cursor.kind() else {
            panic!("side A's functional binds what the lowering binds");
        };
        telescope.push((*binder, (**ty).clone()));
        cursor = (**inner).clone();
    }
    let mut rebuilt = go(&cursor, WfLowering::OnMeasureValue.rec_binder_depth(arity), arg_edit);
    for (position, (binder, ty)) in telescope.into_iter().enumerate().rev() {
        rebuilt = Expr::lam(binder, binder_edit(position, &ty), rebuilt);
    }
    rebuilt
}

fn decrease_sentinel() -> Expr {
    Expr::const_(Name::from_string(DECREASE_SLOT_SENTINEL), vec![])
}

fn measure_sentinel() -> Expr {
    Expr::const_(Name::from_string(MEASURE_SLOT_SENTINEL), vec![])
}

/// The honest side B at phase 3: side A's functional with the FOUR positions a
/// MIR-derived term cannot hold blanked to their sentinels — the `rec` and `hm`
/// binder types, the self-call's major premise, and its decrease proof.
fn honest_side_b(functional: &Expr, arity: usize) -> Expr {
    let slot = WfLowering::OnMeasureValue.decrease_slot_position(arity);
    side_b_from(
        functional,
        arity,
        &move |position, ty| {
            if position == 1 || position == arity + 2 { measure_sentinel() } else { ty.clone() }
        },
        &move |position, argument| match position {
            0 => measure_sentinel(),
            _ if position == slot => decrease_sentinel(),
            _ => argument.clone(),
        },
    )
}

/// **THE BORROW, AT THE KERNEL, BEFORE THE PRODUCER.** A side B holding nothing
/// but the guard, the two branch values and the self-call's source arguments is
/// identified with side A once the four plumbing positions are borrowed — and
/// every wrong-op twin of it is REFUSED.
///
/// This is the row the whole increment rests on, and it is deliberately not run
/// through `reflect_wf`: it asks the KERNEL whether the identification exists at
/// all, so that the producer written after it is producing something already
/// known to be admissible.
#[test]
fn p4_the_phase3_borrow_is_a_kernel_decision() {
    let env = gcdb_env();
    let anatomy = read_wf_sum_measure_anatomy(&body_of(&env, "gcdB")).expect("reads");
    let arity = anatomy.arity();

    // NON-VACUITY: side B really is different from side A before the borrow, and
    // it does not even type-check — the borrow is what makes it a term the
    // kernel can be asked about.
    let honest = honest_side_b(anatomy.functional(), arity);
    assert_ne!(honest, *anatomy.functional());
    for sentinel in [DECREASE_SLOT_SENTINEL, MEASURE_SLOT_SENTINEL] {
        assert!(
            env.get_const(&Name::from_string(sentinel)).is_none(),
            "`{sentinel}` must not resolve, or a borrowed slot could not be told apart from a \
             term someone declared"
        );
    }
    {
        let checker = TypeChecker::new(&env);
        assert!(
            checker.infer_type(&honest).is_err(),
            "before the borrow side B does not type-check at all"
        );
    }

    let faithful = check_faithful_wf_functional(
        &env,
        "gcdB",
        &ReflectedWfFunctional { functional: honest },
        &nat_carrier(),
    )
    .unwrap_or_else(|refusal| panic!("the phase-3 borrow must admit: {refusal:?}"));
    assert_eq!(faithful.method(), FaithfulnessMethod::WellFoundedFunctionalDefeq);

    // ── THE REFUSING SIBLINGS ──────────────────────────────────────────────
    let slot = WfLowering::OnMeasureValue.decrease_slot_position(arity);
    let keep_binders = |position: usize, ty: &Expr| {
        if position == 1 || position == arity + 2 { measure_sentinel() } else { ty.clone() }
    };

    // (a) side B AUTHORS the major premise instead of leaving the sentinel.
    let authored_major = side_b_from(
        anatomy.functional(),
        arity,
        &keep_binders,
        &move |position, argument| {
            if position == slot { decrease_sentinel() } else { argument.clone() }
        },
    );
    let refusal = check_faithful_wf_functional(
        &env,
        "gcdB",
        &ReflectedWfFunctional { functional: authored_major },
        &nat_carrier(),
    )
    .err()
    .expect("side B may not author the measure");
    assert!(
        format!("{refusal:?}").contains("may not author the measure"),
        "the refusal must name the measure borrow: {refusal:?}"
    );

    // (b) side B AUTHORS a binder type the lowering states in terms of the
    //     measure — here `hm`, copied verbatim from side A. Even the RIGHT
    //     term is refused, exactly as an emitter-authored decrease proof is
    //     (probe c5): "right" is what the gate would otherwise take on trust.
    let authored_hm = side_b_from(
        anatomy.functional(),
        arity,
        &|position, ty| if position == 1 { measure_sentinel() } else { ty.clone() },
        &move |position, argument| match position {
            0 => measure_sentinel(),
            _ if position == slot => decrease_sentinel(),
            _ => argument.clone(),
        },
    );
    let refusal = check_faithful_wf_functional(
        &env,
        "gcdB",
        &ReflectedWfFunctional { functional: authored_hm },
        &nat_carrier(),
    )
    .err()
    .expect("side B may not author the measure hypothesis, even correctly");
    assert!(
        format!("{refusal:?}").contains("may not author the measure"),
        "the refusal must name the measure borrow: {refusal:?}"
    );

    // (c) a measure sentinel where nothing is borrowable — binder 0 (`n`).
    let stray = side_b_from(
        anatomy.functional(),
        arity,
        &move |position, ty| {
            if position == 0 || position == 1 || position == arity + 2 {
                measure_sentinel()
            } else {
                ty.clone()
            }
        },
        &move |position, argument| match position {
            0 => measure_sentinel(),
            _ if position == slot => decrease_sentinel(),
            _ => argument.clone(),
        },
    );
    let refusal = check_faithful_wf_functional(
        &env,
        "gcdB",
        &ReflectedWfFunctional { functional: stray },
        &nat_carrier(),
    )
    .err()
    .expect("a sentinel at a position nothing is borrowed for must be refused");
    assert!(
        format!("{refusal:?}").contains("not one of the positions"),
        "the refusal must say the position is not borrowable: {refusal:?}"
    );

    // (d) THE SWAPPED LEGS. `gcdB a b` recurses on `(|a-b|, min a b)`; side B
    //     hands the same two terms the other way round. Both are well-typed
    //     `Nat`s built from the same parameters, so nothing structural
    //     separates them — only the kernel does.
    let swapped = side_b_from(
        anatomy.functional(),
        arity,
        &keep_binders,
        &move |position, argument| match position {
            0 => measure_sentinel(),
            _ if position == slot => decrease_sentinel(),
            2 | 3 => argument.clone(),
            _ => argument.clone(),
        },
    );
    // …built explicitly so the swap is visible: arguments 2 and 3 exchanged.
    let legs: Vec<Expr> = anatomy.calls()[0].arguments().to_vec();
    let swapped = replace_call_arguments(&swapped, arity, &[legs[1].clone(), legs[0].clone()]);
    let refusal = check_faithful_wf_functional(
        &env,
        "gcdB",
        &ReflectedWfFunctional { functional: swapped },
        &nat_carrier(),
    )
    .err()
    .expect("exchanging |a-b| and min a b must be REFUSED — it is a different function");
    let rendered = format!("{refusal:?}");
    assert!(
        rendered.contains("FunctionalDisagreement")
            || rendered.contains("DecreaseSlotBorrowRefused"),
        "the swap must die at the defeq or the type check: {rendered}"
    );
}

/// Replace the SOURCE arguments of the single self-call (positions
/// `2 .. 2 + arity`) with `replacements`, leaving the plumbing alone.
fn replace_call_arguments(functional: &Expr, arity: usize, replacements: &[Expr]) -> Expr {
    side_b_from(
        functional,
        arity,
        &|_, ty| ty.clone(),
        &move |position, argument| {
            if (2..2 + arity).contains(&position) {
                replacements[position - 2].clone()
            } else {
                argument.clone()
            }
        },
    )
}

// ═══════════════════════════════════════════════════════════════════════════
// (p5) THE WHOLE ROUTE
// ═══════════════════════════════════════════════════════════════════════════

/// **PLAN → MATERIALIZE → READ BACK → REFLECT → GATE, on the real elaborated
/// side A.** This is the sentence "the two-argument `gcd` is callable from
/// Rust", executed.
#[test]
fn p5_the_whole_route_admits_end_to_end() {
    let env = gcdb_env();
    let plan = plan_clean_origin_body(&env, "gcdB").expect("plans");
    let extracted = emitted(&env, "gcdB");

    // The MIR reader reads the materializer's own bytes back as the plan —
    // through the PHASE-3 door, and NOT through the phase-2 one, whose
    // predecessor belt this body does not satisfy.
    let read_back = recognize_wf_sum_measure_rec(&extracted).expect("the emitted body reads back");
    assert_eq!(read_back.measure_index, 1);
    assert_eq!(read_back.zero_value, RecBodyExpr::Param(0));
    assert_eq!(read_back.nonzero_value, RecBodyExpr::Rec);
    assert_eq!(read_back.rec_args.len(), 2);
    assert!(
        recognize_wf_nat_rec(&extracted).is_none(),
        "the PHASE-2 door must still refuse this body: its self-call's argument at the guarded \
         position is `a - (a - b)`, not the emitted predecessor. If it stopped refusing, phase \
         2's termination contract has been widened by accident"
    );

    let faithful = admit_lowering(&env, &plan, &extracted)
        .unwrap_or_else(|refusal| panic!("the emission must pass the F-layer gate: {refusal:?}"));
    assert_eq!(faithful.name(), "gcdB");
    assert_eq!(faithful.admitted_at(), &Ty::BignumNat);
    assert_eq!(faithful.method(), FaithfulnessMethod::WellFoundedFunctionalDefeq);
    eprintln!("ROW p5 | gcdB FAITHFUL by WellFoundedFunctionalDefeq, arity 2, no fuel");
}

// ═══════════════════════════════════════════════════════════════════════════
// (p6) PHASE 2 IS UNMOVED
// ═══════════════════════════════════════════════════════════════════════════

/// Every shipped phase-2 fixture still plans to the SAME shape, byte for byte.
///
/// R3d touched the shared reader (`read_wf_value`'s layout, the MIR reader's
/// guarded-argument belt, the reflector's index formulas and the gate's borrow),
/// so "phase 2 is unchanged" is a claim that has to be executed rather than
/// asserted in a comment.
#[test]
fn p6_every_phase2_fixture_still_plans_identically() {
    for (source, name, expected) in [
        (
            "def countdownSum (n : Nat) : Nat := \
             if h : 0 < n then n + countdownSum (n - 1) else 0\n\
             termination_by n",
            "countdownSum",
            "WellFoundedNatRec { zero_value: NatConst(0), nonzero_value: Add(Decreasing, Rec), \
             rec_args: [Pred], measure_index: 0, lowering: OnParameter }",
        ),
        (
            "def addAcc (n acc : Nat) : Nat := \
             if h : 0 < n then addAcc (n - 1) (acc + 1) else acc\n\
             termination_by n",
            "addAcc",
            "WellFoundedNatRec { zero_value: Param(1), nonzero_value: Rec, \
             rec_args: [Pred, Add(Param(1), NatConst(1))], measure_index: 0, \
             lowering: OnParameter }",
        ),
        (
            "def fact (n : Nat) : Nat := if h : 0 < n then n * fact (n - 1) else 1\n\
             termination_by n",
            "fact",
            "WellFoundedNatRec { zero_value: NatConst(1), nonzero_value: Mul(Decreasing, Rec), \
             rec_args: [Pred], measure_index: 0, lowering: OnParameter }",
        ),
    ] {
        let env = island(source).unwrap_or_else(|why| panic!("`{name}` must elaborate: {why}"));
        let plan = plan_clean_origin_body(&env, name)
            .unwrap_or_else(|refusal| panic!("`{name}` must still PLAN: {}", refusal.note()));
        assert_eq!(
            format!("{:?}", plan.shape()),
            expected,
            "R3d must not move `{name}`'s plan"
        );
        // …and the phase-2 MIR door still reads its emitted body.
        assert!(
            recognize_wf_nat_rec(&emitted(&env, name)).is_some(),
            "`{name}`'s emitted body must still read back through the PHASE-2 door"
        );
    }

    // The three-argument FUEL `gcd` — the thing R3d replaces at the call site —
    // must keep working, so that the fixture it backs is not silently broken by
    // the change that supersedes it.
    let env = island(
        "def gcdF (f a b : Nat) : Nat := \
         if h : 0 < f then gcdF (f - 1) ((a - b) + (b - a)) (a - (a - b)) else a\n\
         termination_by f",
    )
    .expect("the fuel form elaborates");
    let plan = plan_clean_origin_body(&env, "gcdF").expect("the fuel form must still plan");
    let CleanOriginShape::WellFoundedNatRec { measure_index, lowering, .. } = plan.shape() else {
        panic!("the fuel form is a well-founded recursion");
    };
    assert_eq!(*measure_index, 0);
    assert_eq!(*lowering, WfLowering::OnParameter, "the fuel form is PHASE 2 — its measure is `f`");
}


// ═══════════════════════════════════════════════════════════════════════════
// (p7) THE RUN-PASS FIXTURE'S OWN ROWS, DECIDED AT THE KERNEL
// ═══════════════════════════════════════════════════════════════════════════

/// **THE VALUES `tests/ui/trust/clean_origin_wf_rec_gcd_direct.rs` ASSERTS,
/// decided at the REAL kernel, each with a refuting control.**
///
/// The fixture runs the EMITTED binary and compares it to literals. A literal
/// that is not itself a kernel decision would make the fixture a tautology about
/// two copies of the same guess, so every row it uses is put to the kernel here
/// — and the WRONG value is required to be REFUSED, because a kernel that
/// admitted `gcdB 12 18 = 3` would admit anything.
///
/// `gcd_final_probes` n1 measures that `Nat.gcd` is ABSENT from the prelude,
/// which is why these are literals rather than a statement of agreement with a
/// definition somebody else wrote. That row is not repeated here; it is cited.
#[test]
fn p7_the_run_pass_fixture_rows_are_kernel_decisions() {
    for (a, b, want) in [
        (12_u32, 18_u32, 6_u32),
        (270, 192, 6),
        (7, 13, 1),
        (0, 5, 5),
        (5, 0, 5),
        (0, 0, 0),
        (6, 6, 6),
        (1, 1, 1),
        (42, 0, 42),
        (99, 33, 33),
        (100, 75, 25),
        (17, 5, 1),
        (48, 18, 6),
    ] {
        assert_eq!(want, gcd(a, b), "the fixture's expected value must be the real gcd");
        let source = format!("{GCDB}\ntheorem v : gcdB {a} {b} = {want} := rfl");
        assert!(
            island(&source).is_ok(),
            "the KERNEL must reduce `gcdB {a} {b}` to `{want}` — this is a row the run-pass \
             fixture asserts about the EMITTED binary: {}",
            island(&source).err().map_or_else(String::new, |why| why
                .lines()
                .next()
                .unwrap_or("")
                .chars()
                .take(200)
                .collect::<String>())
        );
    }
    // THE CONTROLS. Every wrong value below is a COMMON divisor of both inputs
    // (or one of the inputs), so a body that returned a common divisor rather
    // than the GREATEST one — or that returned an argument — would pass the
    // admits above and fail here.
    for (a, b, wrong) in [
        (12_u32, 18_u32, 3_u32),
        (12, 18, 18),
        (270, 192, 2),
        (270, 192, 12),
        (7, 13, 7),
        (100, 75, 5),
        (99, 33, 11),
        (42, 0, 21),
        (6, 6, 3),
    ] {
        assert!(
            island(&format!("{GCDB}\ntheorem v : gcdB {a} {b} = {wrong} := rfl")).is_err(),
            "CONTROL: `gcdB {a} {b} = {wrong}` is FALSE and the kernel must refuse it — if it \
             admits, the rows above are not decisions"
        );
    }
}

const fn gcd(mut a: u32, mut b: u32) -> u32 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **§6f LANDING 6 — the `a == b` demand SERVED, by moving the EMITTER.**
//!
//! Landing 5 measured the `==` spelling to the bottom, landed its kernel
//! producer, and then refused to serve the demand for one reason:
//!
//! > Both spellings realize the SAME MIR, so side B cannot tell them apart —
//! > while the KERNEL can, and does.
//!
//! `a == b` and `a = b` denote the same branch condition, so both emitted one
//! `BinOp::Eq` and one `SwitchInt`; side B reads only the emitted body, so its
//! reading — and therefore the term it reflects — was identical for the two.
//! But the two side-A terms are not definitionally equal, and the kernel says
//! so in its own voice outside this crate (`l5_p3`: the island rejects even
//! `theorem … := rfl` between the two `ite`s). So the gate refused a body that
//! was correct.
//!
//! Landing 5 enumerated three ways out, refused two on principle, and named the
//! third as the direction the discipline takes:
//!
//! > **Make the MIR distinguish them** — transcribe the `Bool` decision and its
//! > `= Bool.true` lift as two comparisons, so side B reads the tree it
//! > reflects. This is the fix direction the discipline fixes — the EMITTER
//! > moves to meet the reader.
//!
//! This file is that landing's measurement.
//!
//! | question | measured verdict |
//! |---|---|
//! | do the two spellings still realize the same MIR? | **no** — `l6_p1` builds both bodies through the REAL `body_template` and prints them side by side; `==` carries one extra comparison and one extra `bool` local |
//! | does `==` admit end to end? | **yes** — `l6_p2`, at u8/u16/u32/u64, over the whole operand vocabulary, through `admit_lowering` (side B's reader, side B's producer, the kernel gate) |
//! | are the two realizations interchangeable? | **no, in BOTH directions** — `l6_p3`. The one-step body is refused against the `==` side A, and the two-step body is refused against the `=` side A. If either ever passed, this landing would have re-created the ambiguity it exists to remove |
//! | did anything that planned before plan differently? | **no** — `l6_p4`, one body per shipped rung, plus the three select fixtures by name |
//! | `a != b` | **still refused**, and the blocker MOVED rather than cleared — `l6_p5` measures it absent at three layers |
//! | does the extra comparison survive optimization? | **YES, and it is a real cost** — `l6_p6` reads the wiring: `optimized_mir` returns a Clean-origin body at its very top, before `run_optimization_passes` |
//!
//! # SIDE A IS THE REAL ELABORATOR, AND THE EMITTED BODY IS THE REAL TEMPLATE
//!
//! Every side A here comes from `trust_certify::clean_island::CleanIslandSession::
//! check_all` — the pipeline `clean_origin_mir` drives — and every emitted body
//! is rendered from `trust_clean_origin::materialize::body_template` applied to
//! the row `table::ladder_row` selects, so what is measured is the EMITTER's
//! decision and not a picture this file drew. Only MUTANTS are hand-built,
//! which is what a mutant is for.
//!
//! The one thing this file cannot reach is the ~180-line translation from
//! template to `mir::Body` in `rustc_mir_transform`, which is x.py-only —
//! landing 4's stated residual risk, unchanged here except that it grew one arm
//! (`TemplateOperand::BoolScalar`).

use clean_kernel::{Environment, Expr, Name};
use trust_clean_carrier::{Carrier, carrier_at};
use trust_clean_origin::materialize::{
    BodyTemplate, TemplateCallee, TemplateOperand, TemplateRvalue, TemplateTerminator, TemplateTy,
    TemplateUnwind, body_template,
};
use trust_clean_origin::table::{MirShape, ROWS, ladder_row, row};
use trust_clean_origin::{
    CleanOriginPlan, CleanOriginShape, EmitRefusal, admit_lowering, check_faithful,
    plan_clean_origin_body,
};
use trust_spec_elab::{Domain, MachineUIntWidth, SelectOperand};
use trust_types::admissible_body::{
    ArithOperand, SelectCmp, recognize_admissible_body, recognize_select_beq,
    recognize_select_general,
};
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

// ───────────────────── side A: the REAL island elaborator ─────────────────────

/// Elaborate `sources` through the pipeline `clean_origin_mir` drives and hand
/// back the environment. A rejected batch panics: a probe that measured a
/// half-built environment would measure nothing.
fn island(sources: &[&str]) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(sources);
    assert!(!batch.is_rejected(), "the island must kernel-check: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

/// The four machine widths this lane carries.
const WIDTHS: [u32; 4] = [8, 16, 32, 64];

fn uint_ty(bits: u32) -> Expr {
    Expr::const_(Name::from_string(&format!("UInt{bits}")), vec![])
}

fn carrier_of(bits: u32) -> Carrier {
    carrier_at(&uint_ty(bits), &Ty::Int { width: bits, signed: false })
        .expect("UIntN -> uN is the exact-width carrier and must be granted")
}

fn machine(bits: u32) -> Domain {
    Domain::Machine(match bits {
        8 => MachineUIntWidth::U8,
        16 => MachineUIntWidth::U16,
        32 => MachineUIntWidth::U32,
        64 => MachineUIntWidth::U64,
        other => panic!("{other} is not a machine width this battery measures"),
    })
}

fn refusal_text(refusal: &EmitRefusal) -> String {
    match refusal {
        EmitRefusal::NotEmittable { reason, .. } => reason.clone(),
        other => panic!("expected `NotEmittable`, got {other:?}"),
    }
}

// ──────────── the EMITTED body, rendered from the REAL template ────────────

/// Render a [`BodyTemplate`] into the `trust_types` MIR vocabulary
/// `trust_mir_extract::extract_function` produces.
///
/// This is `control_11`'s renderer, restated for the shapes this landing
/// measures (there is no call and no reference in either select diamond, so
/// those arms are unreachable here and say so). It is a TEST-SIDE renderer, and
/// the same caveat control_11 states applies: what it establishes is that the
/// DESCRIPTION differs and admits, not that the x.py-only translation into
/// `mir::Body` is faithful.
fn render(template: &BodyTemplate, bits: u32) -> VerifiableFunction {
    let result_ty = Ty::Int { width: bits, signed: false };
    let local_ty = |ty: TemplateTy| match ty {
        TemplateTy::Result | TemplateTy::Param { .. } => result_ty.clone(),
        TemplateTy::Bool => Ty::Bool,
        TemplateTy::RustCalleeResult { .. } => {
            panic!("W5: this probe plans no Rust-call chain; control_23 is that lane's measurement")
        }
        TemplateTy::ResultRef => Ty::Ref { mutable: false, inner: Box::new(result_ty.clone()) },
    };
    let operand = |operand: TemplateOperand| match operand {
        TemplateOperand::Copy(local) => Operand::Copy(Place::local(local)),
        TemplateOperand::Move(local) => Operand::Move(Place::local(local)),
        TemplateOperand::ResultScalar { value, width } => {
            Operand::Constant(ConstValue::Uint(value, width))
        }
        TemplateOperand::U64Scalar(value) => {
            Operand::Constant(ConstValue::Uint(u128::from(value), 64))
        }
        // §6f landing 6. The extractor turns a `bool`-typed MIR constant into
        // `ConstValue::Bool` (`convert_const_operand`'s `TyKind::Bool` arm),
        // never into a one-byte `Uint`.
        TemplateOperand::UIntScalar { value, width } => {
            Operand::Constant(ConstValue::Uint(value, width))
        }
        TemplateOperand::BoolScalar(value) => Operand::Constant(ConstValue::Bool(value)),
    };
    let binop = |cmp: SelectCmp| match cmp {
        SelectCmp::Lt => BinOp::Lt,
        SelectCmp::Le => BinOp::Le,
        SelectCmp::Eq => BinOp::Eq,
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
                        TemplateRvalue::Use(value) => Rvalue::Use(operand(value)),
                        TemplateRvalue::Compare { cmp, left, right } => {
                            Rvalue::BinaryOp(binop(cmp), operand(left), operand(right))
                        }
                        // §6f landing 7. Unreachable from THIS file's shapes
                        // (no select realization carries a raw binop), and
                        // present because the match is wildcard-free by
                        // design — the same reason `l6_p5`'s
                        // `realization_vocabulary` below is.
                        TemplateRvalue::RawBin { op, left, right } => {
                            Rvalue::BinaryOp(op.mir_binop(), operand(left), operand(right))
                        }
                        TemplateRvalue::SharedRef(of) => {
                            Rvalue::Ref { mutable: false, place: Place::local(of) }
                        }
                        TemplateRvalue::BoolNot(_) => panic!("W6: bool negation not exercised by this probe"),
                    },
                    span: SourceSpan::default(),
                })
                .collect(),
            terminator: match &block.terminator {
                TemplateTerminator::Return => Terminator::Return,
                TemplateTerminator::Goto(target) => Terminator::Goto(BlockId(*target)),
                TemplateTerminator::SwitchIntZero { discr, zero, otherwise } => {
                    Terminator::SwitchInt {
                        discr: operand(*discr),
                        targets: vec![(0, BlockId(*zero))],
                        otherwise: BlockId(*otherwise),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    }
                }
                TemplateTerminator::Call { callee, args, dest, target, unwind } => {
                    Terminator::Call {
                        func: match callee {
                            TemplateCallee::Primitive(identity) => identity.canonical_path(),
                            TemplateCallee::RustFn { .. } => panic!("W5: this probe plans no Rust-call chain; control_23 is that lane's measurement"),
                            TemplateCallee::SelfDef => "crate::m::probe".to_owned(),
                        },
                        args: args.iter().map(|arg| operand(*arg)).collect(),
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
                        callee_key: None,
                    }
                }
            },
        })
        .collect();
    VerifiableFunction {
        name: "probe".into(),
        def_path: "crate::m::probe".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: template.arg_count,
            return_ty: result_ty,
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// Plan a declaration, select its row, build the REAL template and render it —
/// the whole side-A half of the emitter, driven exactly as `build_gated_body`
/// drives it.
fn plan_and_emit(
    env: &Environment,
    name: &str,
    bits: u32,
) -> (CleanOriginPlan, VerifiableFunction) {
    let plan = plan_clean_origin_body(env, name)
        .unwrap_or_else(|refusal| panic!("`{name}` must plan: {refusal:?}"));
    let selected = ladder_row(plan.shape())
        .unwrap_or_else(|| panic!("`{name}`'s shape selects no row: {:?}", plan.shape()));
    let template = body_template(selected, &plan)
        .unwrap_or_else(|refusal| panic!("`{name}`'s template: {refusal:?}"));
    let emitted = render(&template, bits);
    (plan, emitted)
}

/// The pretty-printed structure of a body — `control_11`'s comparison, which
/// sees every field of every local, statement, operand and terminator.
fn body_picture(func: &VerifiableFunction) -> String {
    format!(
        "arg_count = {}\nreturn_ty = {:?}\nlocals = {:#?}\nblocks = {:#?}\n",
        func.body.arg_count, func.body.return_ty, func.body.locals, func.body.blocks,
    )
}

/// Count the value-carrying statements of a body.
fn statement_count(func: &VerifiableFunction) -> usize {
    func.body.blocks.iter().map(|block| block.stmts.len()).sum()
}

// ═══════ L6-P1 — THE TWO SPELLINGS NOW REALIZE DIFFERENT MIR ═══════

/// **The measurement landing 5's refusal turned on, taken again with the fix in
/// place.**
///
/// Landing 5's blocker, in its own words, was that `a == b` and `a = b` *"both
/// realize the SAME MIR — one `BinOp::Eq`, one `SwitchInt`"*. This builds both
/// bodies through the REAL `body_template` at every width and requires them to
/// DIFFER, construct by construct:
///
/// ```text
///  a = b  (select.eq, MirShape::ComparisonBranch(Eq))
///    bb0: _4 = Eq(copy _1, copy _2)
///         switchInt(copy _4) -> [0: bb2, otherwise: bb1]
///
///  a == b (select.beq, MirShape::BoolDecisionBranch)
///    bb0: _4 = Eq(copy _1, copy _2)              // the Bool DECISION
///         _5 = Eq(copy _4, const true)           // the LIFT to a proposition
///         switchInt(copy _5) -> [0: bb2, otherwise: bb1]
/// ```
///
/// Everything below the `SwitchInt` is identical, and that is asserted too: the
/// arms and the join are ONE contract, read by one function on side B, and a
/// landing that quietly forked them would have created the second reader this
/// crate refuses everywhere else.
#[test]
fn l6_p1_the_two_spellings_now_realize_different_mir() {
    for bits in WIDTHS {
        let env = island(&[
            &format!(
                "def eqbeq (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := \
                 if a == b then a else b"
            ),
            &format!(
                "def eqprop (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := \
                 if a = b then a else b"
            ),
        ]);

        let (beq_plan, beq) = plan_and_emit(&env, "eqbeq", bits);
        let (prop_plan, prop) = plan_and_emit(&env, "eqprop", bits);

        // The PLANS are different shapes, selecting different rows with
        // different declared realizations.
        assert_eq!(
            beq_plan.shape(),
            &CleanOriginShape::SelectBeq {
                cmp_left: 0,
                cmp_right: ArithOperand::Param(1),
                then_arm: ArithOperand::Param(0),
                else_arm: ArithOperand::Param(1),
            },
            "u{bits}: `a == b` plans as the `==` shape"
        );
        assert_eq!(
            prop_plan.shape(),
            &CleanOriginShape::Select {
                cmp: SelectCmp::Eq,
                cmp_left: 0,
                cmp_right: 1,
                then_param: 0,
                else_param: 1,
            },
            "u{bits}: `a = b` still plans as the pre-landing-6 rung, byte for byte"
        );
        assert_eq!(ladder_row(beq_plan.shape()).expect("row").name, "select.beq");
        assert_eq!(ladder_row(prop_plan.shape()).expect("row").name, "select.eq");
        assert_eq!(row("select.beq").expect("row").mir, MirShape::BoolDecisionBranch);
        assert_eq!(row("select.eq").expect("row").mir, MirShape::ComparisonBranch(SelectCmp::Eq));

        // THE MEASUREMENT. The two emitted bodies are not the same body.
        assert_ne!(
            body_picture(&beq),
            body_picture(&prop),
            "u{bits}: the `==` and `=` bodies are IDENTICAL, which is exactly landing 5's \
             blocker. Side B reads only the emitted body, so an identical emission means the \
             gate is being asked to decide a question the bytes do not carry."
        );

        // …and the difference is exactly ONE statement: the lift.
        assert_eq!(
            statement_count(&beq),
            statement_count(&prop) + 1,
            "u{bits}: the two-step form must add exactly one statement — the `= Bool.true` \
             lift — and nothing else"
        );
        assert_eq!(
            beq.body.locals.len(),
            prop.body.locals.len() + 1,
            "u{bits}: …and exactly one local, the lifted bool"
        );

        // The entry block: two comparisons, branching on the SECOND.
        let entry = &beq.body.blocks[0];
        assert_eq!(entry.stmts.len(), 2, "u{bits}: the `==` entry block carries two statements");
        let Statement::Assign {
            place: decision, rvalue: Rvalue::BinaryOp(BinOp::Eq, l, r), ..
        } = &entry.stmts[0]
        else {
            panic!("u{bits}: the first statement is the bool DECISION `_d = Eq(a, b)`");
        };
        // `trust_types::Operand` derives `Debug` but not `PartialEq` (and
        // `trust-types` is not this landing's to change), so identity is taken
        // on the pretty-printed structure — `control_11`'s own rule, and the
        // stricter comparison anyway.
        assert_eq!(
            format!("{l:?}"),
            format!("{:?}", Operand::Copy(Place::local(1))),
            "u{bits}: …over the parameters"
        );
        assert_eq!(format!("{r:?}"), format!("{:?}", Operand::Copy(Place::local(2))));
        assert_eq!(
            beq.body.locals[decision.local].ty,
            Ty::Bool,
            "u{bits}: the decision is typed at `bool`, which is what makes the lift a \
             comparison of two booleans rather than of something at the carrier"
        );
        let Statement::Assign {
            place: lifted,
            rvalue: Rvalue::BinaryOp(BinOp::Eq, lift_l, lift_r),
            ..
        } = &entry.stmts[1]
        else {
            panic!("u{bits}: the second statement is the LIFT `_c = Eq(_d, const true)`");
        };
        assert_eq!(
            format!("{lift_l:?}"),
            format!("{:?}", Operand::Copy(Place::local(decision.local)))
        );
        assert!(
            matches!(lift_r, Operand::Constant(ConstValue::Bool(true))),
            "u{bits}: the scrutinee is `Bool.true` and nothing else — `false` here is the \
             COMPLEMENTARY function with every arm, index and width still right; got {lift_r:?}"
        );
        assert_eq!(beq.body.locals[lifted.local].ty, Ty::Bool);
        let Terminator::SwitchInt { discr, targets, otherwise, .. } = &entry.terminator else {
            panic!("u{bits}: the `==` entry branches");
        };
        assert_eq!(
            format!("{discr:?}"),
            format!("{:?}", Operand::Copy(Place::local(lifted.local))),
            "u{bits}: the branch reads the LIFTED bool. Reading the decision would emit the \
             one-step body wearing a dead statement, which side B refuses."
        );
        assert_eq!(targets, &vec![(0, BlockId(2))], "u{bits}: 0 (FALSE) is the ELSE arm");
        assert_eq!(*otherwise, BlockId(1), "u{bits}: …and `otherwise` is the THEN arm");

        // Everything below the switch is the diamond's contract, unchanged.
        assert_eq!(
            format!("{:#?}", &beq.body.blocks[1..]),
            format!("{:#?}", &prop.body.blocks[1..]),
            "u{bits}: the arms and the join must be IDENTICAL to the one-step diamond's. They \
             are one contract, side B reads them with one function, and forking them here \
             would create the second reader this crate refuses everywhere else."
        );

        eprintln!(
            "PROBE-ROW | if a == b (u{bits})      | emitted: 2 comparisons + switch | \
             DIFFERS from `a = b` (1 comparison + switch)"
        );
    }
}

// ═══════ L6-P2 — THE DEMAND, SERVED, END TO END ═══════

/// **`admit_lowering` ADMITS the `==` spelling** — side B's reader, side B's
/// producer and the kernel gate — at every width and across the whole operand
/// vocabulary the shape is stated over.
///
/// This is the flip landing 5 could not make. Note what is NOT here: no
/// spelling bit is passed to the gate, no producer is chosen by side A, and
/// `admit_lowering` is given the plan and the EMITTED body exactly as
/// `build_gated_body` gives them to it. The kernel decides which `ite` the
/// emitted body denotes, which is the property landing 5 refused to trade away.
#[test]
fn l6_p2_the_beq_spelling_admits_end_to_end() {
    let mut admitted = 0usize;
    for bits in WIDTHS {
        let env = island(&[
            &format!(
                "def eqbeq (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := \
                 if a == b then a else b"
            ),
            &format!(
                "def eqarm (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := \
                 if a == b then 0 else b"
            ),
            &format!(
                "def eqarms (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := \
                 if a == b then 1 else 0"
            ),
            &format!(
                "def eqlit (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := \
                 if a == 10 then a else b"
            ),
            &format!("def eqone (a : UInt{bits}) : UInt{bits} := if a == 3 then 7 else a"),
        ]);
        for (name, shape) in [
            (
                "eqbeq",
                CleanOriginShape::SelectBeq {
                    cmp_left: 0,
                    cmp_right: ArithOperand::Param(1),
                    then_arm: ArithOperand::Param(0),
                    else_arm: ArithOperand::Param(1),
                },
            ),
            (
                "eqarm",
                CleanOriginShape::SelectBeq {
                    cmp_left: 0,
                    cmp_right: ArithOperand::Param(1),
                    then_arm: ArithOperand::Const(0),
                    else_arm: ArithOperand::Param(1),
                },
            ),
            (
                "eqarms",
                CleanOriginShape::SelectBeq {
                    cmp_left: 0,
                    cmp_right: ArithOperand::Param(1),
                    then_arm: ArithOperand::Const(1),
                    else_arm: ArithOperand::Const(0),
                },
            ),
            (
                "eqlit",
                CleanOriginShape::SelectBeq {
                    cmp_left: 0,
                    cmp_right: ArithOperand::Const(10),
                    then_arm: ArithOperand::Param(0),
                    else_arm: ArithOperand::Param(1),
                },
            ),
            (
                "eqone",
                CleanOriginShape::SelectBeq {
                    cmp_left: 0,
                    cmp_right: ArithOperand::Const(3),
                    then_arm: ArithOperand::Const(7),
                    else_arm: ArithOperand::Param(0),
                },
            ),
        ] {
            let (plan, emitted) = plan_and_emit(&env, name, bits);
            assert_eq!(plan.shape(), &shape, "u{bits} `{name}`: the planned shape");

            // Side B's reader, on the EMITTED body and nothing else.
            let read = recognize_select_beq(&emitted).unwrap_or_else(|| {
                panic!("u{bits} `{name}`: side B must read the emitted two-step diamond")
            });
            assert_eq!(read.cmp_left, 0);

            // THE GATE.
            admit_lowering(&env, &plan, &emitted).unwrap_or_else(|refusal| {
                panic!("u{bits} `{name}`: the `==` round trip must ADMIT: {refusal:?}")
            });
            admitted += 1;
        }
    }
    assert_eq!(
        admitted, 20,
        "four widths by five operand vocabularies; the coverage must not shrink"
    );
    eprintln!(
        "PROBE-ROW | if a == b, all vocabularies | plan + emit + read + reflect + gate | ADMIT \
         at u8/u16/u32/u64"
    );
}

// ═══════ L6-P3 — THE TWO REALIZATIONS ARE NOT INTERCHANGEABLE ═══════

/// **The ambiguity this landing exists to remove must not come back, and that
/// is a two-directional claim.**
///
/// It is not enough that `==` now admits. If the ONE-step body still admitted
/// against the `==` side A, or the TWO-step body against the `=` side A, the
/// two realizations would be interchangeable and the emitted bytes would once
/// again fail to determine which declaration a body is for. Both directions are
/// measured here, at every width, through the REAL `admit_lowering`.
///
/// The containment halves are here too, because a reader widening is exactly
/// where the gate-free E6 kernel-import direction gets widened by accident: the
/// two-step diamond must read back as `None` from `recognize_admissible_body`
/// (the E6 chain) AND from `recognize_select_general` (the one-step CALL-lane
/// reader), and the one-step diamond must read back as `None` from
/// `recognize_select_beq`.
#[test]
fn l6_p3_the_two_realizations_are_not_interchangeable() {
    for bits in WIDTHS {
        let env = island(&[
            &format!(
                "def eqbeq (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := \
                 if a == b then a else b"
            ),
            &format!(
                "def eqprop (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := \
                 if a = b then a else b"
            ),
        ]);
        let (beq_plan, beq_body) = plan_and_emit(&env, "eqbeq", bits);
        let (prop_plan, prop_body) = plan_and_emit(&env, "eqprop", bits);

        // 1. THE ONE-STEP BODY AGAINST THE `==` PLAN — refused. (Emitting the
        //    old body for the new declaration is precisely the wrong-binary
        //    outcome landing 5 refused to risk.)
        let refusal = admit_lowering(&env, &beq_plan, &prop_body).expect_err(
            "the ONE-step body must NOT be admitted for a `==` declaration — if it is, the two \
             realizations are interchangeable again and the emitted bytes no longer determine \
             which declaration the body is for",
        );
        assert!(
            matches!(refusal, EmitRefusal::LoweringUnrecognised { .. }),
            "u{bits}: side B's `==` reader must refuse the one-step body outright, BEFORE any \
             kernel work: {refusal:?}"
        );

        // 2. THE TWO-STEP BODY AGAINST THE `=` PLAN — refused, and by the
        //    OTHER reader, which is the converse half.
        let refusal = admit_lowering(&env, &prop_plan, &beq_body)
            .expect_err("the TWO-step body must NOT be admitted for a `=` declaration");
        assert!(
            matches!(refusal, EmitRefusal::LoweringUnrecognised { .. }),
            "u{bits}: the one-step reader must refuse the two-step body: {refusal:?}"
        );

        // 3. E6 CONTAINMENT: the gate-free kernel-import direction sees
        //    neither the two-step diamond nor a constant-arm one. `l3_p2`
        //    measured the second; the first is this landing's own obligation,
        //    and it is the reason `recognize_select_beq` is a SEPARATE ENTRY
        //    POINT rather than an `AdmissibleBody` variant — that dispatch
        //    matches `AdmissibleBody` exhaustively, so a variant could not have
        //    been CALL-only.
        assert!(
            recognize_admissible_body(&beq_body).is_none(),
            "u{bits}: the E6 kernel-import direction must stay blind to the two-step diamond. \
             A variant there becomes a defining equation with NO side A and NO kernel gate."
        );
        assert!(
            recognize_select_general(&beq_body).is_none(),
            "u{bits}: the ONE-step CALL-lane reader must not read the two-step body either, or \
             the same bytes would have two readings and the gate would pick by dispatch order"
        );
        assert!(
            recognize_select_beq(&prop_body).is_none(),
            "u{bits}: …and the `==` reader must not read the ONE-step body, which is the half \
             that keeps `a = b` from being silently gated as `a == b`"
        );
        // The one-step body still reads back exactly as it did.
        assert!(
            recognize_admissible_body(&prop_body).is_some(),
            "u{bits}: `a = b`'s emission is untouched by this landing"
        );
    }
    eprintln!(
        "PROBE-ROW | one-step vs two-step       | admit_lowering in BOTH directions | REFUSED \
         both ways (side B's readers, before the kernel)"
    );
}

// ═══════ L6-P4 — NO BODY THAT PLANNED BEFORE PLANS DIFFERENTLY ═══════

/// **`control_12::half_5`'s claim, restated for the landing that actually adds
/// a recognizer that RETURNS A SHAPE.**
///
/// Landing 5's arm could only refuse, so the worst it could do was refuse
/// something that used to plan. This landing's arm PLANS, so it could also take
/// a body away from another rung. It sits after every pre-existing recognizer
/// and reads a tree all of them already declined (its proposition is stated at
/// `Bool`, not at the carrier) — and this executes that claim over one body per
/// shipped rung rather than trusting the reading of a `return`.
#[test]
fn l6_p4_no_body_that_planned_before_plans_differently_now() {
    let env = island(&[
        "def proj (a : UInt64) (b : UInt64) : UInt64 := a",
        "def sum (a : UInt64) (b : UInt64) : UInt64 := a + b",
        "def poly (a : UInt64) (b : UInt64) : UInt64 := a * b + a",
        "def konst (a : UInt64) : UInt64 := 6",
        "def lt (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b",
        "def le (a : UInt64) (b : UInt64) : UInt64 := if a <= b then a else b",
        "def eq (a : UInt64) (b : UInt64) : UInt64 := if a = b then a else b",
        "def thr (a : UInt64) (b : UInt64) : UInt64 := if a < 10 then a else b",
        "def clampz (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else 0",
    ]);
    let expected = [
        ("proj", CleanOriginShape::Projection { projected: 0 }),
        ("konst", CleanOriginShape::ConstantUint { value: 6 }),
        (
            "lt",
            CleanOriginShape::Select {
                cmp: SelectCmp::Lt,
                cmp_left: 0,
                cmp_right: 1,
                then_param: 0,
                else_param: 1,
            },
        ),
        (
            "le",
            CleanOriginShape::Select {
                cmp: SelectCmp::Le,
                cmp_left: 0,
                cmp_right: 1,
                then_param: 0,
                else_param: 1,
            },
        ),
        (
            "eq",
            CleanOriginShape::Select {
                cmp: SelectCmp::Eq,
                cmp_left: 0,
                cmp_right: 1,
                then_param: 0,
                else_param: 1,
            },
        ),
        (
            "thr",
            CleanOriginShape::SelectLiteral {
                cmp: SelectCmp::Lt,
                cmp_param: 0,
                literal: 10,
                then_param: 0,
                else_param: 1,
            },
        ),
        (
            "clampz",
            CleanOriginShape::SelectOperands {
                cmp: SelectCmp::Lt,
                cmp_left: 0,
                cmp_right: ArithOperand::Param(1),
                then_arm: ArithOperand::Param(0),
                else_arm: ArithOperand::Const(0),
            },
        ),
    ];
    for (name, shape) in expected {
        let plan = plan_clean_origin_body(&env, name)
            .unwrap_or_else(|refusal| panic!("`{name}` planned before landing 6: {refusal:?}"));
        assert_eq!(plan.shape(), &shape, "`{name}` planned a DIFFERENT shape after landing 6");
    }
    for (name, what) in [("sum", "the single wrapping op"), ("poly", "the composed tree")] {
        let plan = plan_clean_origin_body(&env, name).expect("it planned before");
        assert!(
            matches!(
                plan.shape(),
                CleanOriginShape::WrappingBinOp { .. } | CleanOriginShape::Composed { .. }
            ),
            "{what} must still plan as itself"
        );
    }

    // And the EMISSION of the three select fixtures the landing must not touch
    // — `run_select`, `run_select_literal` and `select_operands`, by their
    // shapes — is byte-identical to the one-step diamond it always was: no
    // `bool` constant anywhere, one comparison, three locals past the
    // parameters at most.
    for name in ["lt", "le", "eq", "thr", "clampz"] {
        let (_, body) = plan_and_emit(&env, name, 64);
        assert_eq!(
            body.body.blocks[0].stmts.len(),
            1,
            "`{name}`: the one-step diamond's entry block still carries ONE statement"
        );
        assert_eq!(
            body.body.locals.len(),
            5,
            "`{name}`: …and the shape still declares `_0`, two parameters, the select temp and \
             ONE bool"
        );
        assert!(
            !body_picture(&body).contains("Bool(true)"),
            "`{name}`: no `bool` CONSTANT may appear in a body that is not the `==` shape"
        );
    }
}

// ═══════ L6-P5 — `a != b`: STILL REFUSED, AND THE BLOCKER MOVED ═══════

/// **The `!=` demand, decided on its own merits after `==` was served.**
///
/// Landing 5 ranked `!=` below `==` and gave two reasons: it inherited `==`'s
/// emitted-MIR blocker in full, and it added a comparison-vocabulary one
/// (`SelectCmp` is `{Lt, Le, Eq}` and carries no `Ne`). **The first reason is
/// now paid off** — `MirShape::BoolDecisionBranch` realizes a `Bool`-level
/// decision lifted by `= Bool.true`, which is exactly the frame `!=` needs —
/// so this probe re-measures what is left, and it is one thing at three layers:
/// the `Bool.not` NODE.
///
/// 1. **the emitted vocabulary** has no unary rvalue at all
///    (`materialize::TemplateRvalue` is `{Use, Compare, SharedRef}`);
/// 2. **side B's reader** requires a two-statement entry block whose first
///    statement is a `BinOp::Eq` — there is no negation arm;
/// 3. **the producer** refuses to mint the negation deliberately: landing 5's
///    `admit_select_beq_function` documents that *"admitting the negation here
///    would let a caller mint a term whose emitted diamond would have to branch
///    the other way"*.
///
/// The tempting shortcut — emitting the `==` body and flipping the `SwitchInt`
/// polarity instead of emitting the negation — is refused in advance and the
/// refusal is measured: side B would then read the `==` tree off a body that
/// denotes its complement, which is a wrong binary with a green gate.
#[test]
fn l6_p5_the_not_equal_spelling_still_refuses_and_the_blocker_moved() {
    for bits in WIDTHS {
        let env = island(&[&format!(
            "def neqbeq (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := \
             if a != b then a else b"
        )]);
        let refusal = plan_clean_origin_body(&env, "neqbeq")
            .expect_err("`!=` still has no row and planning must refuse");
        assert!(!refusal.is_compiler_defect(), "a fragment boundary is not a compiler defect");
        let text = refusal_text(&refusal);
        assert!(text.contains("`!=`"), "u{bits}: the refusal must name the operator: {text}");
        assert!(
            text.contains("Bool.not"),
            "u{bits}: …and the construct that distinguishes it from `==`, which is where the \
             negation lives: {text}"
        );
        assert!(
            text.contains("restate the branch positively"),
            "u{bits}: …and the option that DOES work: {text}"
        );
        assert!(
            !text.contains("- restate the out-of-fragment position"),
            "u{bits}: `!=` must NOT be offered the `==` operand fix — its operators are the \
             problem, not its operands: {text}"
        );
    }

    // LAYER 1: the emitted vocabulary, pinned by an exhaustive match so a future
    // `TemplateRvalue` variant is a review event here.
    //
    // W6 UPDATE (2026-09-13): a UNARY negation rvalue now EXISTS —
    // `TemplateRvalue::BoolNot` — for the WHOLE-BODY `def f (b : Bool) : Bool :=
    // not b` shape. So the old statement "no negation in the emitted
    // vocabulary" is retired. But `!=` in a SELECT DECISION (`if a != b then …`)
    // is still not emittable, and the blocker only moved: the select-beq
    // realization is a diamond whose decision is a `Bool` COMPARISON, and there
    // is no realization that COMPOSES a `Bool.not` around that decision. A
    // standalone `BoolNot` returning `_0` is a different body from a `Bool.not`
    // wrapping a diamond's scrutinee — LAYER 3 below still measures that the
    // `==` producer cannot mint the negated select term.
    fn realization_vocabulary(rvalue: &TemplateRvalue) -> &'static str {
        match rvalue {
            TemplateRvalue::Use(_) => "use",
            TemplateRvalue::Compare { .. } => "compare",
            TemplateRvalue::RawBin { .. } => "raw-bin",
            TemplateRvalue::SharedRef(_) => "shared-ref",
            // W6: a whole-body boolean negation. Present in the vocabulary now,
            // but NOT a `Bool.not` composed into a select decision — see the
            // block comment above.
            TemplateRvalue::BoolNot(_) => "bool-not",
        }
    }
    assert_eq!(
        realization_vocabulary(&TemplateRvalue::Use(TemplateOperand::BoolScalar(true))),
        "use",
        "the emitted realization vocabulary is pinned BY TYPE: this match is exhaustive with \
         no wildcard, so a future `TemplateRvalue` variant is a review event here"
    );
    assert_eq!(
        realization_vocabulary(&TemplateRvalue::BoolNot(TemplateOperand::Copy(1))),
        "bool-not",
        "W6 added a whole-body boolean negation; `!=` in a select decision is still not \
         emittable, for the reason LAYER 3 measures"
    );

    // LAYER 2: side B has no `Ne` and no negation arm — `SelectCmp` is three
    // variants, pinned by an exhaustive match for the same reason.
    fn comparison_vocabulary(cmp: SelectCmp) -> &'static str {
        match cmp {
            SelectCmp::Lt => "<",
            SelectCmp::Le => "<=",
            SelectCmp::Eq => "==",
        }
    }
    assert_eq!(comparison_vocabulary(SelectCmp::Eq), "==");

    // LAYER 3: the producer refuses the negation by having no way to ask for
    // it — `admit_select_beq_function`'s signature carries no negation flag, so
    // a caller cannot mint the `!=` term at all. Measured as an absence of
    // capability rather than as a runtime refusal, which is the stronger form.
    let env = island(&["def neq (a : UInt64) (b : UInt64) : UInt64 := if a != b then a else b"]);
    let mut scratch = env.clone();
    trust_spec_elab::admit_select_beq_function(
        &mut scratch,
        "probe_landing6_beq",
        &[machine(64), machine(64)],
        0,
        SelectOperand::Param(1),
        SelectOperand::Param(0),
        SelectOperand::Param(1),
    )
    .expect("the `==` route mints");
    let minted = scratch
        .get_const(&Name::from_string("probe_landing6_beq"))
        .and_then(|c| c.value.clone())
        .expect("the minted term");
    assert!(
        check_faithful(&env, "neq", &minted, &carrier_of(64)).is_err(),
        "the `==` producer's term must NOT be admitted for a `!=` declaration: `Bool.not` is \
         not absorbed by anything, and if this ever passes the negation has been silently \
         identified with the positive decision"
    );

    eprintln!(
        "PROBE-ROW | if a != b                  | REFUSED — blocker MOVED: the `==` \
         emitted-MIR half is paid, the `Bool.not` node is absent at three layers"
    );
}

// ═══════ L6-P6 — THE COST: the extra comparison SURVIVES ═══════

/// **The cost this landing pays, measured rather than assumed.**
///
/// The two-step form emits one extra comparison and one extra `bool` local. The
/// obvious hope is that a MIR optimization folds `Eq(_d, const true)` back into
/// `_d`. **It does not, because no MIR pass runs on a Clean-origin body at
/// all**, and that is a property of the query wiring rather than of any pass:
/// `optimized_mir` returns the gated body at its VERY TOP, before
/// `inner_optimized_mir` and therefore before `run_optimization_passes`,
/// because — in the compiler's own words — *"the gate's subject is the body
/// this function returns, so a pass that rewrote it after the gate ran would
/// put un-gated code in the binary."* `mir_for_ctfe` does the same.
///
/// So the extra comparison **survives into codegen**, verbatim, and this
/// landing records it as a real cost in the same way landing 3 recorded
/// `l3_p3b`.
///
/// What this probe does NOT claim: anything about LLVM. Whether the backend
/// folds `%c = icmp eq i1 %d, true` is a backend question, downstream of the
/// MIR the gate covers, and this lane has no measurement of it.
///
/// The measurement is a source read, which is the only form available on a lane
/// that cannot run `x.py` — the same instrument
/// `table_controls::h_i_the_side_b_reader_cannot_name_the_table` uses, and for
/// the same reason: the fact lives in a file this crate cannot call into.
#[test]
fn l6_p6_the_extra_comparison_survives_into_the_binary() {
    let wiring = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../compiler/rustc_mir_transform/src/lib.rs"
    ))
    .expect("the MIR pipeline's query wiring is where it has always been");

    let start =
        wiring.find("fn optimized_mir(").expect("`optimized_mir` is the codegen arm's entry point");
    let end =
        wiring[start..].find("fn inner_optimized_mir(").expect("`inner_optimized_mir` follows it");
    let arm = &wiring[start..start + end];
    let gate = arm
        .find("clean_origin_mir::clean_origin_mir(tcx, did)")
        .expect("the Clean-origin gate is called from `optimized_mir`");
    assert!(
        arm[gate..].contains("return tcx.arena.alloc(body)"),
        "MEASURED: `optimized_mir` must RETURN the gated body directly. If this ever stops \
         being an early return, a MIR pass would run on a body the kernel already gated — \
         which changes both the cost this landing pays AND `docs/TCB.md`'s Clean-origin \
         runtime-body row, and must be re-measured in the same change."
    );
    // …and the whole of `optimized_mir` never CALLS the optimizer: the call
    // lives one function down, past the early return. Keyed on the call form
    // rather than the name, because the function's own doc comment says the
    // words (*"The body is returned WITHOUT `run_optimization_passes`"*) and a
    // control that matched prose would pass on a comment.
    assert!(
        !arm.contains("run_optimization_passes(tcx"),
        "nothing may optimize a Clean-origin body on the codegen arm"
    );

    // The converse, so this is not vacuous: `run_optimization_passes` DOES
    // exist and IS called — on the ordinary path, inside `inner_optimized_mir`,
    // which the early return above skips.
    assert!(
        wiring.contains("run_optimization_passes(tcx, &mut body);"),
        "the ordinary codegen path still optimizes; the Clean-origin path is the exception"
    );

    // And the CTFE arm, which is the other half of the wiring: a `const` never
    // reaches `optimized_mir`, so a claim made only about codegen would be half
    // a claim.
    let ctfe_start = wiring.find("fn inner_mir_for_ctfe(").expect("the CTFE arm");
    let ctfe = &wiring[ctfe_start..ctfe_start + 1_600];
    let ctfe_gate = ctfe
        .find("clean_origin_mir::clean_origin_mir(tcx, def)")
        .expect("the Clean-origin gate is called from the CTFE arm too");
    // The gate's `if let Some(body) = … { … }` block, read to its closing brace at the
    // function's indentation. It was a fixed 120-byte window until plan step 3.5
    // (f1eb7b1cf2f) put a comment and the reach counter `hook_ran(tcx.sess, true)`
    // between the gate and its `return`, which moved the `return` past the window
    // while the body was still returned untouched. So the block is read whole, and
    // every statement in it must be either that counter (it takes the session and a
    // flag, never the body) or the `return` itself: anything else that could rewrite
    // the gated body before it is returned turns this row red.
    let gate_block_len = ctfe[ctfe_gate..]
        .find("\n    }\n")
        .expect("the gate's `if let` block closes inside the window");
    let statements: Vec<&str> = ctfe[ctfe_gate..ctfe_gate + gate_block_len]
        .lines()
        .skip(1)
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with("//"))
        .collect();
    assert_eq!(
        statements.last(),
        Some(&"return body;"),
        "the CTFE arm must return the gated body directly as well: {statements:?}"
    );
    assert!(
        statements[..statements.len() - 1]
            .iter()
            .all(|line| line.starts_with("clean_origin_ir::clean_origin_reach::hook_ran(tcx.sess,")),
        "nothing but the reach counter may run between the CTFE gate and its return: \
         {statements:?}"
    );

    eprintln!(
        "PROBE-ROW | the extra comparison       | `optimized_mir` returns the gated body BEFORE \
         `run_optimization_passes` | SURVIVES into codegen (MIR level, measured); LLVM-level \
         folding NOT measured and NOT claimed"
    );
}

// ═══════ L6-P7 — THE ROW, and what makes it legal ═══════

/// **Landing 5 measured that this row could not exist. What changed is stated
/// precisely, and executed.**
///
/// Its words were: a `select.beq` row *"would realize `ComparisonBranch(Eq)`,
/// which `select.eq` already realizes at the same context, carrier and gate —
/// an alias with no legal separation under H-C"*. H-C admits an alias only when
/// the rows are separated BY LAYER or by disjoint side A **and** a different
/// gate, and neither escape was available.
///
/// The row is legal now because **the realization changed**, and for no other
/// reason. This asserts each half of that, so a future edit that "simplifies"
/// the row back onto `ComparisonBranch(Eq)` fails here rather than silently
/// re-creating an undeclarable alias.
#[test]
fn l6_p7_the_row_is_legal_because_the_realization_changed_and_nothing_else() {
    let beq = row("select.beq").expect("§6f landing 6 adds the row");
    let eq = row("select.eq").expect("`select.eq` must still exist");

    // The three coordinates that did NOT move — which is what makes "the
    // realization is what changed" a statement with content.
    assert_eq!(beq.context, eq.context, "the rows sit at the SAME layer");
    assert_eq!(beq.carrier, eq.carrier, "…at the SAME carrier");
    assert_eq!(beq.gate, eq.gate, "…and route to the SAME gate");

    // The one that did.
    assert_eq!(beq.mir, MirShape::BoolDecisionBranch);
    assert_eq!(eq.mir, MirShape::ComparisonBranch(SelectCmp::Eq));
    assert_ne!(
        beq.mir, eq.mir,
        "if these ever agree again, H-C has an undeclarable alias: same layer, same carrier, \
         same gate, same bytes"
    );

    // No OTHER row realizes it either, so `Unique` is truthful rather than
    // decorative.
    assert_eq!(
        ROWS.iter().filter(|candidate| candidate.mir == MirShape::BoolDecisionBranch).count(),
        1,
        "exactly one row realizes the two-step diamond"
    );

    // `select.eq` is byte for byte what landing 3 left behind: this landing
    // took nothing away from it.
    assert_eq!(eq.unwind, beq.unwind, "neither realization emits a call");
    assert_eq!(eq.side_a.len(), 1, "`select.eq` still has exactly its own side-A route");
    assert!(eq.tcb_row.is_none() && beq.tcb_row.is_none());

    // And the side-A selectors are disjoint — a KERNEL fact (l5_p3), not a
    // table convention.
    assert!(
        beq.side_a.iter().all(|selector| !eq.side_a.contains(selector)),
        "the two rows' side-A spellings must be disjoint, or which row a term selects would \
         depend on the order of the table"
    );
}

/// A structural guard on the operand vocabulary the landing added: the `bool`
/// constant is a NEW realization primitive, and every consumer of
/// `TemplateOperand` must be exhaustive over it.
///
/// It is asserted here rather than described because the whole reason landing 5
/// stopped where it did is that this variant did not exist: `ResultScalar` is
/// typed at the result carrier and `U64Scalar` at `u64`, and comparing a `bool`
/// local against either is ill-typed MIR.
#[test]
fn l6_p8_the_bool_constant_is_a_primitive_no_other_scalar_could_spell() {
    fn primitive(operand: TemplateOperand) -> &'static str {
        match operand {
            TemplateOperand::Copy(_) => "copy",
            TemplateOperand::Move(_) => "move",
            TemplateOperand::ResultScalar { .. } => "scalar at the result carrier",
            TemplateOperand::U64Scalar(_) => "scalar at u64",
            TemplateOperand::UIntScalar { .. } => "scalar at an explicit width",
            TemplateOperand::BoolScalar(_) => "scalar at bool",
        }
    }
    assert_eq!(primitive(TemplateOperand::BoolScalar(true)), "scalar at bool");
    assert_eq!(
        primitive(TemplateOperand::ResultScalar { value: 1, width: 64 }),
        "scalar at the \
        result carrier"
    );
    // The lift's constant is `true` in every emitted body: `false` is the
    // complementary function, and nothing plans it.
    let env = island(&["def eqbeq (a : UInt64) (b : UInt64) : UInt64 := if a == b then a else b"]);
    let (_, body) = plan_and_emit(&env, "eqbeq", 64);
    let constants: Vec<String> = body
        .body
        .blocks
        .iter()
        .flat_map(|block| &block.stmts)
        .filter_map(|stmt| match stmt {
            Statement::Assign { rvalue: Rvalue::BinaryOp(_, _, Operand::Constant(c)), .. } => {
                Some(format!("{c:?}"))
            }
            _ => None,
        })
        .collect();
    assert_eq!(
        constants,
        vec![format!("{:?}", ConstValue::Bool(true))],
        "the emitted `==` body carries exactly ONE constant in a comparison, and it is \
         `Bool.true`"
    );
}

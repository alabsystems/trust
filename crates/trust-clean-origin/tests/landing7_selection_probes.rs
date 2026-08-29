// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **§6f LANDING 7 — `&&&`, `|||`, `/` and `%` on the CALL lane, and the one
//! divisor this lane will not emit.**
//!
//! The clean pin `bad1fd5f8` (2026-08-23) made all four operators elaborate at
//! every `UInt{N}` width, where before they did not elaborate at any. This file
//! is the Trust half's measurement.
//!
//! | question | measured verdict |
//! |---|---|
//! | what does side A look like? | ONE spelling — the homogeneous surface class at the prelude instance, at all four widths; NO source produces the carrier method (`l7_p1`) |
//! | do `&&&`/`\|\|\|` admit end to end? | **yes** — `l7_p2`, at u8/u16/u32/u64, over the whole operand vocabulary, through `admit_lowering` |
//! | do `/`/`%` admit? | **at a strictly positive NUMERAL divisor, yes** — `l7_p3`, all four widths |
//! | is every mutation refused? | **yes, eleven of them** — `l7_p4`, including the two that emit a PANICKING division |
//! | did the E6 import direction's reach move? | **no** — `l7_p5`; the raw-binop provenance pin is intact |
//! | why is a variable divisor refused? | **a wrong binary, measured** — `l7_p6`; and the obvious guard does NOT close it |
//! | `^^^`, `<<<`, `>>>` | **do not elaborate at all** — `l7_p7`; the blocker is the clean prelude |
//! | does the planner hold the divisor rule? | **yes, on every unsafe form** — `l7_p8` |
//! | nested trees | **green at the kernel, no realization** — `l7_p9` |
//! | does anything downstream insert the div-by-zero check? | **no — no MIR pass runs at all** (`l7_p10`), so the divisor rule is the whole guarantee |
//!
//! # THE SOUNDNESS TRAP, AND WHY THIS LANDING IS NARROWER THAN THE BRIEF ASKED
//!
//! Clean's `UInt{N}.div` and `.mod` are **TOTAL**. Rust's `/` and `%` **PANIC**
//! at a zero divisor. So the naive emission — a MIR `BinOp::Div` for a
//! declaration `a / b` — computes a DIFFERENT function from the declaration,
//! on exactly the input a value-level test does not reach. That is a wrong
//! binary, which on this lane is the failure the whole faithfulness gate exists
//! to catch.
//!
//! The obvious repair is to emit the guard `if b == 0 { 0 } else { a / b }`.
//! **It does not work, and `l7_p6` is the measurement.** At an open divisor the
//! `ite` scrutinee `BEq.beq b 0` is STUCK, so the guarded term is not
//! definitionally equal to the bare `a / b` side A and `check_faithful` refuses
//! it in both directions. A recogniser that COLLAPSED the guard — read the
//! four-block diamond and mint `UInt{N}.div a b` — would make defeq hold and
//! would be the one move that must not be made: the kernel never sees the MIR,
//! so a wrong guard constant or a swapped `SwitchTargets` polarity would become
//! invisible, and the double fault `docs/TCB.md` rests on would collapse.
//!
//! What IS reachable, and what this landing serves, is the divisor the two
//! semantics AGREE on: a strictly positive numeral. The frozen producer has
//! demanded exactly that since long before this lane existed, in its own
//! words — *"A positive literal is statically nonzero, so this total division
//! matches Rust's trapping division for every input."*
//!
//! # SIDE A IS THE REAL ELABORATOR, AND THE EMITTED BODY IS THE REAL TEMPLATE
//!
//! Every side A here comes from `trust_certify::clean_island::
//! CleanIslandSession::check_all` — the pipeline `clean_origin_mir` drives —
//! and every emitted body is rendered from
//! `trust_clean_origin::materialize::body_template` applied to the row
//! `table::ladder_row` selects. Only MUTANTS are hand-built, which is what a
//! mutant is for.

#![allow(clippy::doc_markdown)]

use clean_kernel::{Environment, Expr, ExprKind, Name};
use trust_clean_carrier::{Carrier, carrier_at};
use trust_clean_origin::materialize::{
    BodyTemplate, TemplateCallee, TemplateOperand, TemplateRvalue, TemplateTerminator, TemplateTy,
    TemplateUnwind, body_template,
};
use trust_clean_origin::table::{MirShape, ROWS, ladder_row};
use trust_clean_origin::{
    CleanOriginPlan, CleanOriginShape, EmitRefusal, admit_lowering, check_faithful,
    plan_clean_origin_body,
};
use trust_spec_elab::{Domain, MachineUIntWidth};
use trust_types::admissible_body::{
    ArithOperand, RawBinOpKind, SelectCmp, recognize_admissible_body, recognize_raw_binop,
    recognize_select_beq, recognize_select_general,
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

/// The same, WITHOUT the assertion — for the probes whose subject is a
/// REJECTION. `Err` carries the batch's own diagnostics.
fn island_try(sources: &[&str]) -> Result<Environment, String> {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(sources);
    if batch.is_rejected() {
        return Err(format!("{batch:?}"));
    }
    Ok(session.environment().expect("an untainted session has an environment").clone())
}

/// The four machine widths this lane carries.
const WIDTHS: [u32; 4] = [8, 16, 32, 64];

/// The four operators, with the source token, the surface class and its
/// projection. Everything else in this file is derived from this table, so a
/// probe cannot silently measure three of the four.
const OPERATORS: [(RawBinOpKind, &str, &str, &str); 4] = [
    (RawBinOpKind::BitAnd, "&&&", "HAnd", "hAnd"),
    (RawBinOpKind::BitOr, "|||", "HOr", "hOr"),
    (RawBinOpKind::Div, "/", "HDiv", "hDiv"),
    (RawBinOpKind::Rem, "%", "HMod", "hMod"),
];

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

/// Uncurry an application spine into `(head, args)`.
fn uncurry(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args = Vec::new();
    let mut cursor = expr;
    while let ExprKind::App(f, a) = cursor.kind() {
        args.push(&**a);
        cursor = f;
    }
    args.reverse();
    (cursor, args)
}

/// Peel `n` lambdas off a term.
fn peel(expr: &Expr, n: usize) -> &Expr {
    let mut cursor = expr;
    for _ in 0..n {
        let ExprKind::Lam(_, _, body) = cursor.kind() else {
            panic!("expected {n} binders, found {cursor}");
        };
        cursor = body;
    }
    cursor
}

fn definition_value(env: &Environment, name: &str) -> Expr {
    env.get_const(&Name::from_string(name))
        .and_then(|c| c.value.clone())
        .unwrap_or_else(|| panic!("`{name}` must be a definition with a value"))
}

// ──────────── the EMITTED body, rendered from the REAL template ────────────

/// Render a [`BodyTemplate`] into the `trust_types` MIR vocabulary
/// `trust_mir_extract::extract_function` produces.
///
/// `control_11`'s renderer, restated for the shapes this landing measures. It
/// is a TEST-SIDE renderer, and control_11's caveat applies unchanged: what it
/// establishes is that the DESCRIPTION admits, not that the x.py-only
/// translation into `mir::Body` is faithful.
fn render(template: &BodyTemplate, bits: u32) -> VerifiableFunction {
    let result_ty = Ty::Int { width: bits, signed: false };
    let local_ty = |ty: TemplateTy| match ty {
        TemplateTy::Result | TemplateTy::Param { .. } => result_ty.clone(),
        TemplateTy::Bool => Ty::Bool,
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
        TemplateOperand::BoolScalar(value) => Operand::Constant(ConstValue::Bool(value)),
    };
    let cmp_binop = |cmp: SelectCmp| match cmp {
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
                            Rvalue::BinaryOp(cmp_binop(cmp), operand(left), operand(right))
                        }
                        // §6f landing 7 — THE new realization primitive. The
                        // operator comes from `RawBinOpKind::mir_binop`, which
                        // is the same function side B reads the body back
                        // through, so this renderer cannot disagree with the
                        // reader about what it built.
                        TemplateRvalue::RawBin { op, left, right } => {
                            Rvalue::BinaryOp(op.mir_binop(), operand(left), operand(right))
                        }
                        TemplateRvalue::SharedRef(of) => {
                            Rvalue::Ref { mutable: false, place: Place::local(of) }
                        }
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
        .unwrap_or_else(|refusal| panic!("`{name}` must plan: {}", refusal.note()));
    let selected = ladder_row(plan.shape())
        .unwrap_or_else(|| panic!("`{name}`'s shape selects no row: {:?}", plan.shape()));
    let template = body_template(selected, &plan)
        .unwrap_or_else(|refusal| panic!("`{name}`'s template: {refusal:?}"));
    let emitted = render(&template, bits);
    (plan, emitted)
}

/// The single value-carrying statement of a one-block body, for mutation.
fn sole_rvalue(func: &mut VerifiableFunction) -> &mut Rvalue {
    let Statement::Assign { rvalue, .. } = &mut func.body.blocks[0].stmts[0] else {
        panic!("the raw-binop body's sole statement is an assignment");
    };
    rvalue
}

// ═══════════ L7-P1 — SIDE A, PINNED NODE BY NODE, AT EVERY WIDTH ═══════════

/// **The measurement every other probe in this file rests on, and the one
/// three shipped lanes skipped.**
///
/// `control_14`'s header names the class: a lane whose side A was assembled by
/// its own test proves what the KERNEL accepts and nothing whatever about what
/// the ELABORATOR emits. So before a row exists, the four spellings are read
/// out of a real session and pinned construct by construct:
///
/// ```text
/// H{And,Or,Div,Mod}.h{And,Or,Div,Mod}.{0,0,0}
///   UInt{N} UInt{N} UInt{N} instH{…}UInt{N} #1 #0
/// ```
///
/// Six arguments, three of them the carrier constant, the fourth a BARE
/// instance constant named `inst{Class}{Carrier}`, then the two operands with
/// the de Bruijn inversion (`#1` is source parameter 0).
///
/// **And the negative half, which is why the rows carry only ONE selector.**
/// `UInt{N}.land`, `.lor`, `.div` and `.mod` are declared constants at this pin
/// — the ratchet in `fragment_widening_probes` fired on exactly that — but NO
/// source produces them, and side B renders the `toNat`/`ofNat` round trip
/// rather than the carrier method either. A `CarrierMethod` selector on these
/// rows would therefore be a reader arm for a spelling neither side emits,
/// which is precisely the defect `control_14`'s spelling grain exists to catch.
/// It is asserted here rather than assumed.
#[test]
fn l7_p1_the_four_operators_are_pinned_node_by_node_at_every_width() {
    for bits in WIDTHS {
        let carrier = format!("UInt{bits}");
        let sources: Vec<String> = OPERATORS
            .iter()
            .map(|(_, token, class, _)| {
                format!("def op{class} (a : {carrier}) (b : {carrier}) : {carrier} := a {token} b")
            })
            .collect();
        let refs: Vec<&str> = sources.iter().map(String::as_str).collect();
        let env = island(&refs);

        for (_, _, class, projection) in OPERATORS {
            let value = definition_value(&env, &format!("op{class}"));
            let body = peel(&value, 2);
            let (head, args) = uncurry(body);

            // 1. THE HEAD is the surface class projection, with three universe
            //    parameters. The carrier method is NOT what a source produces.
            let ExprKind::Const(name, levels) = head.kind() else {
                panic!("u{bits} `{class}`: the body's head is not a constant: {body}");
            };
            assert_eq!(
                *name,
                Name::from_string(&format!("{class}.{projection}")),
                "u{bits}: the elaborated head moved. Every reader in this lane is keyed on \
                 this exact name, and a lane keyed on a name no source emits is the R2 defect."
            );
            assert_eq!(levels.len(), 3, "u{bits} `{class}`: three universe parameters");

            // 2. SIX ARGUMENTS: three carrier types, the instance, two operands.
            assert_eq!(args.len(), 6, "u{bits} `{class}`: {body}");
            for (index, ty) in args[..3].iter().enumerate() {
                assert!(
                    matches!(ty.kind(), ExprKind::Const(n, _) if *n == Name::from_string(&carrier)),
                    "u{bits} `{class}`: type argument {index} is not the carrier — a \
                     HETEROGENEOUS instantiation, which this lane deliberately does not read"
                );
            }

            // 3. THE INSTANCE is a BARE constant, `inst{Class}{Carrier}`. A
            //    user instance is kernel-reducible to it and would even pass
            //    defeq; the recogniser refuses it anyway so it surfaces as a
            //    capability refusal, and this pin is what that rests on.
            assert!(
                matches!(
                    args[3].kind(),
                    ExprKind::Const(n, _)
                        if *n == Name::from_string(&format!("inst{class}{carrier}"))
                ),
                "u{bits} `{class}`: the instance is not the bare prelude constant: {}",
                args[3]
            );

            // 4. THE OPERANDS, with the de Bruijn inversion.
            assert!(
                matches!(args[4].kind(), ExprKind::BVar(1)),
                "u{bits} `{class}`: the LEFT operand is not source parameter 0"
            );
            assert!(
                matches!(args[5].kind(), ExprKind::BVar(0)),
                "u{bits} `{class}`: the RIGHT operand is not source parameter 1"
            );
        }

        // THE NEGATIVE HALF: no source produces the carrier method, so no row
        // may list it. Read the elaborated terms rather than asserting it.
        for suffix in ["land", "lor", "div", "mod"] {
            let spelling = Name::from_string(&format!("{carrier}.{suffix}"));
            for (_, _, class, _) in OPERATORS {
                let value = definition_value(&env, &format!("op{class}"));
                assert!(
                    !mentions(&value, &spelling),
                    "u{bits}: `{carrier}.{suffix}` appears in an elaborated body. The rows \
                     carry only the SURFACE selector on the strength of this measurement; if \
                     the elaborator has started producing the carrier method, add the \
                     selector AND a `control_14` witness for it in the same commit."
                );
            }
        }
    }
}

/// Whether a constant name occurs anywhere in a term.
fn mentions(expr: &Expr, name: &Name) -> bool {
    match expr.kind() {
        ExprKind::Const(candidate, _) => candidate == name,
        ExprKind::App(f, a) => mentions(f, name) || mentions(a, name),
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => mentions(t, name) || mentions(b, name),
        ExprKind::Let(_, t, v, b, _) => mentions(t, name) || mentions(v, name) || mentions(b, name),
        ExprKind::MData(_, inner) | ExprKind::Proj(_, _, inner) => mentions(inner, name),
        _ => false,
    }
}

// ═══════════ L7-P2 — `&&&` AND `|||` ADMIT END TO END ═══════════

/// **The whole pipeline for the two operators with no zero case**: plan, the
/// REAL template, the rendered body, side B's SEPARATE reader, the FROZEN
/// producer, and the kernel gate — at every width, over the whole operand
/// vocabulary.
///
/// The emitted body is asserted to be what it claims: ONE block, ONE statement,
/// `_0 = <op>(l, r)`, `Return`, no call and no branch.
#[test]
fn l7_p2_the_bitwise_rows_admit_end_to_end() {
    for bits in WIDTHS {
        let carrier = format!("UInt{bits}");
        // A literal that is in range at every width this battery covers.
        let env = island(&[
            &format!("def band (a : {carrier}) (b : {carrier}) : {carrier} := a &&& b"),
            &format!("def bor (a : {carrier}) (b : {carrier}) : {carrier} := a ||| b"),
            &format!("def bandlit (a : {carrier}) : {carrier} := a &&& 15"),
            &format!("def borlit (a : {carrier}) : {carrier} := a ||| 15"),
        ]);

        for (name, op, right) in [
            ("band", RawBinOpKind::BitAnd, ArithOperand::Param(1)),
            ("bor", RawBinOpKind::BitOr, ArithOperand::Param(1)),
            ("bandlit", RawBinOpKind::BitAnd, ArithOperand::Const(15)),
            ("borlit", RawBinOpKind::BitOr, ArithOperand::Const(15)),
        ] {
            let (plan, emitted) = plan_and_emit(&env, name, bits);
            assert_eq!(
                plan.shape(),
                &CleanOriginShape::RawBinOp { op, left: ArithOperand::Param(0), right },
                "u{bits} `{name}`: the planned shape"
            );
            assert_eq!(
                ladder_row(plan.shape()).expect("row").mir,
                MirShape::RawBinOp(op),
                "u{bits} `{name}`: the selected realization"
            );

            // The emitted body IS one statement and no control flow.
            assert_eq!(emitted.body.blocks.len(), 1, "u{bits} `{name}`: one block");
            assert_eq!(emitted.body.blocks[0].stmts.len(), 1, "u{bits} `{name}`: one statement");
            assert!(
                matches!(emitted.body.blocks[0].terminator, Terminator::Return),
                "u{bits} `{name}`: the terminator is `Return` — no call, no branch"
            );

            // Side B's SEPARATE reader agrees with the plan.
            let read = recognize_raw_binop(&emitted)
                .unwrap_or_else(|| panic!("u{bits} `{name}`: side B must read the emitted body"));
            assert_eq!(read.op, op);
            assert_eq!(read.left, ArithOperand::Param(0));
            assert_eq!(read.right, right);

            // And the gate.
            admit_lowering(&env, &plan, &emitted).unwrap_or_else(|refusal| {
                panic!("u{bits} `{name}` must admit end to end: {refusal:?}")
            });
        }
    }
}

// ═══════ L7-P3 — `/` AND `%` ADMIT AT A POSITIVE NUMERAL DIVISOR ═══════

/// **The division rows, end to end, at the only divisor the two semantics
/// agree on.**
///
/// Divisor `3` is used at every width because a literal must be in range at
/// `UInt8` too. The plan, the emitted `BinaryOp(Div)`/`BinaryOp(Rem)`, side B's
/// reader, the FROZEN producer's `p0 / 3` rendering and the kernel gate.
///
/// The emitted body carries **no `Assert`**, and that is asserted rather than
/// described: a source-level `/` acquires a div-by-zero assertion during MIR
/// building, and this body is not built from source. What makes its absence
/// safe is the divisor rule, measured in `l7_p8`.
#[test]
fn l7_p3_the_division_rows_admit_at_a_positive_literal_divisor() {
    for bits in WIDTHS {
        let carrier = format!("UInt{carrier_bits}", carrier_bits = bits);
        let env = island(&[
            &format!("def dv (a : {carrier}) : {carrier} := a / 3"),
            &format!("def md (a : {carrier}) : {carrier} := a % 3"),
        ]);

        for (name, op) in [("dv", RawBinOpKind::Div), ("md", RawBinOpKind::Rem)] {
            let (plan, emitted) = plan_and_emit(&env, name, bits);
            assert_eq!(
                plan.shape(),
                &CleanOriginShape::RawBinOp {
                    op,
                    left: ArithOperand::Param(0),
                    right: ArithOperand::Const(3),
                },
                "u{bits} `{name}`: the planned shape"
            );
            assert_eq!(emitted.body.blocks.len(), 1, "u{bits} `{name}`: one block");
            assert!(
                matches!(emitted.body.blocks[0].terminator, Terminator::Return),
                "u{bits} `{name}`: no `Assert`, no call, no branch — the terminator is `Return`"
            );
            let read = recognize_raw_binop(&emitted)
                .unwrap_or_else(|| panic!("u{bits} `{name}`: side B must read the body"));
            assert_eq!(read.op, op);
            assert_eq!(read.right, ArithOperand::Const(3));

            admit_lowering(&env, &plan, &emitted).unwrap_or_else(|refusal| {
                panic!("u{bits} `{name}` must admit end to end: {refusal:?}")
            });
        }
    }
}

// ═══════════════ L7-P4 — EVERY MUTATION IS REFUSED ═══════════════

/// **One construct changed each, and the gate must catch every one.**
///
/// The base bodies are the REAL emissions from `plan_and_emit`; each mutant
/// changes exactly one thing and goes back through the REAL `admit_lowering` —
/// side B's reader, the frozen producer, the kernel.
///
/// | # | mutation | why it must be caught |
/// |---|---|---|
/// | 1 | `&` for `\|` | the complementary function, same operands, same width |
/// | 2 | `\|` for `&` | the converse |
/// | 3 | operands SWAPPED on `/` | division is not commutative |
/// | 4 | operands SWAPPED on `&` | **commutative, and STILL refused** — defeq is intensional on the stuck `Nat.land` |
/// | 5 | wrong divisor literal (`4` for `3`) | an emitter that baked in the wrong constant |
/// | 6 | wrong bitmask literal | as above, for `&` |
/// | 7 | `/` for `%` | the two `Nat` recursions differ |
/// | 8 | width skew on the literal | a constant encoded at another width |
/// | 9 | **the PANICKING division — a VARIABLE divisor** | Rust panics where the declaration returns a value |
/// | 10 | **the PANICKING division — a literal ZERO divisor** | the same, at the reachable constant |
/// | 11 | the wrapping-CALL realization for a bitwise declaration | the other family's body |
///
/// Rows 9 and 10 are the point of the whole landing, and the probe records
/// WHICH layer catches them rather than assuming the interesting one does.
/// **Measured: the STRUCTURAL comparison fires first** — the sealed plan says
/// `Const(3)` and the mutated body says `Copy(_2)`, so `admit_lowering` refuses
/// at step 2 and the producer is never reached. That is fail-closed, but it is
/// this lane agreeing with itself, so the probe additionally measures the layer
/// that is NOT this lane: the FROZEN `admit_expr_function`, written years
/// earlier for the opposite direction, refuses to mint `p0 / p1` or `p0 / 0` at
/// all. Both layers are asserted, because a landing that reported the second
/// while the first was doing the work would be describing evidence it does not
/// have.
#[test]
fn l7_p4_every_raw_binop_mutation_is_refused() {
    let bits = 64u32;
    let env = island(&[
        "def band (a : UInt64) (b : UInt64) : UInt64 := a &&& b",
        "def bor (a : UInt64) (b : UInt64) : UInt64 := a ||| b",
        "def bandlit (a : UInt64) : UInt64 := a &&& 15",
        "def dv (a : UInt64) (b : UInt64) : UInt64 := a / 3",
        "def md (a : UInt64) : UInt64 := a % 3",
    ]);

    let mut refused = 0usize;
    let mut check = |label: &str, name: &str, mutate: &dyn Fn(&mut VerifiableFunction)| {
        let (plan, mut emitted) = plan_and_emit(&env, name, bits);
        // The UNMUTATED body admits — otherwise the mutation is not what the
        // refusal is about.
        admit_lowering(&env, &plan, &emitted)
            .unwrap_or_else(|r| panic!("`{name}` must admit before mutation: {r:?}"));
        mutate(&mut emitted);
        let refusal = admit_lowering(&env, &plan, &emitted).err().unwrap_or_else(|| {
            panic!(
                "MUTATION `{label}` ON `{name}` WAS ACCEPTED. A body that computes something \
                 else than the Clean declaration was admitted, which on this lane is a wrong \
                 binary."
            )
        });
        eprintln!("L7-P4 | {label:<44} | REFUSED: {}", short(&refusal));
        refused += 1;
    };

    // 1/2 — the operator, both directions.
    check("`|` emitted for a `&&&` declaration", "band", &|f| {
        if let Rvalue::BinaryOp(op, ..) = sole_rvalue(f) {
            *op = BinOp::BitOr;
        }
    });
    check("`&` emitted for a `|||` declaration", "bor", &|f| {
        if let Rvalue::BinaryOp(op, ..) = sole_rvalue(f) {
            *op = BinOp::BitAnd;
        }
    });

    // 3/4 — swapped operands, on a non-commutative operator and on a
    // commutative one. The second is the interesting half.
    check("operands swapped on `/`", "dv", &|f| {
        if let Rvalue::BinaryOp(_, left, right) = sole_rvalue(f) {
            std::mem::swap(left, right);
        }
    });
    check("operands swapped on `&&&` (COMMUTATIVE)", "band", &|f| {
        if let Rvalue::BinaryOp(_, left, right) = sole_rvalue(f) {
            std::mem::swap(left, right);
        }
    });

    // 5/6 — the wrong constant.
    check("divisor `4` emitted for `a / 3`", "dv", &|f| {
        if let Rvalue::BinaryOp(_, _, right) = sole_rvalue(f) {
            *right = Operand::Constant(ConstValue::Uint(4, 64));
        }
    });
    check("mask `14` emitted for `a &&& 15`", "bandlit", &|f| {
        if let Rvalue::BinaryOp(_, _, right) = sole_rvalue(f) {
            *right = Operand::Constant(ConstValue::Uint(14, 64));
        }
    });

    // 7 — the sibling operator.
    check("`/` emitted for a `%` declaration", "md", &|f| {
        if let Rvalue::BinaryOp(op, ..) = sole_rvalue(f) {
            *op = BinOp::Div;
        }
    });

    // 8 — the width skew. The constant's ENCODED width is what side B's
    // operand reader anchors on, so a u32-encoded 3 in a u64 body is a body
    // whose constant is not at the carrier.
    check("divisor encoded at u32 in a u64 body", "dv", &|f| {
        if let Rvalue::BinaryOp(_, _, right) = sole_rvalue(f) {
            *right = Operand::Constant(ConstValue::Uint(3, 32));
        }
    });

    // 9/10 — THE PANICKING DIVISION, against a TOTAL declaration. Both are
    // refused by the FROZEN producer, which will not mint a variable or zero
    // divisor at all.
    check("PANICKING: a VARIABLE divisor for `a / 3`", "dv", &|f| {
        if let Rvalue::BinaryOp(_, _, right) = sole_rvalue(f) {
            *right = Operand::Copy(Place::local(2));
        }
    });
    check("PANICKING: a literal ZERO divisor for `a / 3`", "dv", &|f| {
        if let Rvalue::BinaryOp(_, _, right) = sole_rvalue(f) {
            *right = Operand::Constant(ConstValue::Uint(0, 64));
        }
    });

    // 11 — the OTHER family's realization. A wrapping call is what `+`/`-`/`*`
    // emit; for a bitwise declaration it is a body side B's raw-binop reader
    // does not read at all.
    check("the wrapping-CALL realization for `a &&& b`", "band", &|f| {
        f.body.blocks[0].stmts.clear();
        f.body.blocks[0].terminator = Terminator::Call {
            func: "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add"
                .to_owned(),
            args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
            dest: Place::local(0),
            target: Some(BlockId(1)),
            span: SourceSpan::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            unwind: UnwindEdge::Unreachable,
            callee_identity: None,
        };
        f.body.blocks.push(BasicBlock {
            id: BlockId(1),
            stmts: Vec::new(),
            terminator: Terminator::Return,
        });
    });

    assert_eq!(refused, 11, "every mutation in the table must have run");

    // ── THE SECOND LAYER, on the two mutations that matter ─────────────────
    //
    // The eleven refusals above all came from THIS lane — nine from the
    // structural comparison against the sealed plan, two from side B's reader
    // declining the body. That is fail-closed, and it is also this lane
    // agreeing with itself. The independent layer is the FROZEN producer, and
    // it is measured directly: a panicking divisor has NO side B at all, so
    // even a plan that somehow carried one could not reach the kernel gate.
    for rendering in ["p0 / p1", "p0 % p1", "p0 / 0", "p0 % 0"] {
        let arity = if rendering.contains("p1") { 2 } else { 1 };
        let refusal = mint_expr(&env, rendering, arity, bits).err().unwrap_or_else(|| {
            panic!(
                "the FROZEN producer minted `{rendering}`. A variable or zero divisor now has \
                 a side B, which removes the independent half of this landing's divisor \
                 refusal — re-measure the whole boundary before relying on it."
            )
        });
        assert!(
            refusal.contains("divisor"),
            "the producer's refusal must name the divisor boundary: {refusal}"
        );
        eprintln!("L7-P4 | FROZEN PRODUCER refuses `{rendering:<8}` | {refusal}");
    }

    // And the CONTROL that keeps the four refusals above from passing for the
    // wrong reason: the positive-literal renderings this lane actually uses DO
    // mint, so the producer is refusing the divisor and not the operator.
    for rendering in ["p0 / 3", "p0 % 3", "p0 & p1", "p0 | p1"] {
        let arity = if rendering.contains("p1") { 2 } else { 1 };
        assert!(
            mint_expr(&env, rendering, arity, bits).is_ok(),
            "`{rendering}` must mint — if it does not, the producer refusals above measured a \
             ban on the operator rather than on the divisor"
        );
    }
}

fn short(refusal: &EmitRefusal) -> String {
    let text = format!("{refusal:?}");
    text.chars().take(96).collect::<String>().replace('\n', " ")
}

// ═══════ L7-P5 — THE E6 IMPORT DIRECTION'S REACH DID NOT MOVE ═══════

/// **The pinned provenance boundary, re-measured with the row in place.**
///
/// `trust_types`' own `binop_provenance_pins_never_admit` states it: *"the
/// raw-binop spelling is outside the recognized fragment today"*. That chain —
/// `recognize_admissible_body` — also feeds
/// `trust_certify::clean_island::admit_function_into`, where a recognized body
/// becomes a defining equation with NO side A and NO kernel gate. A widening
/// there would be strictly worse than a wrong binary.
///
/// So this landing's capability is reached through `recognize_raw_binop`, a
/// SEPARATE entry point, and this probe measures that the REAL emitted bodies
/// still read back as `None` from the chain and from the two other separate
/// entry points. It also re-measures the pin the widening was most likely to
/// break by accident: a raw `BinaryOp(Add)`, which must STILL be unrecognized
/// everywhere — the raw-binop reader deliberately does not read `Add`/`Sub`/
/// `Mul`, because their emitted realization is the marker-authenticated call.
#[test]
fn l7_p5_the_raw_binop_reading_stays_out_of_the_e6_chain() {
    let env = island(&[
        "def band (a : UInt64) (b : UInt64) : UInt64 := a &&& b",
        "def dv (a : UInt64) : UInt64 := a / 3",
    ]);
    for name in ["band", "dv"] {
        let bits = 64;
        let (_, emitted) = plan_and_emit(&env, name, bits);
        assert!(
            recognize_admissible_body(&emitted).is_none(),
            "`{name}`'s emitted body reads back through `recognize_admissible_body`. That \
             chain feeds the gate-free E6 kernel-import direction, where a recognized body \
             becomes a defining equation with no side A and no kernel gate — and it is also \
             the chain `binop_provenance_pins_never_admit` pins the raw-binop spelling OUT of."
        );
        assert!(
            recognize_select_general(&emitted).is_none(),
            "`{name}`'s body reads back as a general select"
        );
        assert!(
            recognize_select_beq(&emitted).is_none(),
            "`{name}`'s body reads back as a `==` select"
        );
        assert!(
            recognize_raw_binop(&emitted).is_some(),
            "`{name}` must be read by its OWN entry point"
        );
    }

    // The pin the widening was most likely to break by accident: a raw
    // `BinaryOp(Add)` is still outside BOTH readers.
    let mut raw_add = plan_and_emit(&env, "band", 64).1;
    if let Rvalue::BinaryOp(op, ..) = sole_rvalue(&mut raw_add) {
        *op = BinOp::Add;
    }
    assert!(
        recognize_admissible_body(&raw_add).is_none(),
        "a raw `BinaryOp(Add)` body reads back as arithmetic. `+` is emitted as a \
         marker-authenticated CALL, and admitting the raw spelling for it flips the third pin \
         of `binop_provenance_pins_never_admit` — a soundness incident, not a widening."
    );
    assert!(
        recognize_raw_binop(&raw_add).is_none(),
        "the raw-binop reader read `BinaryOp(Add)`. It reads exactly the four operators whose \
         realization IS the raw operator; `Add`/`Sub`/`Mul` are not among them."
    );
}

// ═══ L7-P6 — THE TOTAL DECLARATION AND THE PANICKING BODY, MEASURED APART ═══

/// **The soundness trap, measured at the kernel, in the kernel's own voice.**
///
/// Three findings, and the third is the one that decides this landing's shape.
///
/// 1. **Clean's `/` and `%` are TOTAL, and the zero-case VALUES are derived
///    from the kernel rather than taken from anywhere.** `theorem … := rfl` is
///    put to the island for `7 / 0 = 0`, `0 / 0 = 0`, `7 % 0 = 7`, `0 % 0 = 0`
///    and the two ordinary cases, at both u64 and u8; and the two REFUTED
///    mutants (`7 / 0 = 7`, `7 % 0 = 0`) are REJECTED. So a Rust body that
///    panicked at a zero divisor would disagree with the declaration.
///
/// 2. **`a / 0` DENOTES the constant-zero function, at an OPEN dividend.**
///    `Nat.div` recurses on the DIVISOR, so `check_faithful` ADMITS the
///    constant `0` against `def dz (a : UInt64) : UInt64 := a / 0`. That is
///    what makes an emitted `Div(a, const 0)` a WRONG BINARY rather than merely
///    an unproven one — the compiler could emit a correct body for that
///    declaration and would instead have emitted a trap. The refusal's first
///    option names exactly this.
///
///    **The analogous option is NOT available for `%`**, and the probe measures
///    that too: `a % 0` is not definitionally the identity at an open `a` (the
///    fuel-driven `Nat.modCore` sticks), so the refusal must not offer it.
///
/// 3. **THE GUARD DOES NOT CLOSE THE GAP.** `if b == 0 then 0 else a / b` is
///    NOT definitionally equal to `a / b` at an open divisor: the `ite`
///    scrutinee `BEq.beq b 0` is stuck, so the island rejects `rfl` between
///    them. At a CLOSED zero divisor it IS redundant (the same reduction as
///    finding 2), which is the measurement that makes finding 3 precise rather
///    than a guess. So the repair the brief proposed is not available on this
///    lane, and the honest outcome is the refusal.
#[test]
fn l7_p6_the_total_declaration_and_the_panicking_body_are_measured_apart() {
    // ── 1. the zero-case VALUES, from the kernel ───────────────────────────
    for bits in [64u32, 8] {
        let c = format!("UInt{bits}");
        for (label, statement) in [
            ("7 / 0 = 0", format!("(7 : {c}) / (0 : {c}) = 0")),
            ("0 / 0 = 0", format!("(0 : {c}) / (0 : {c}) = 0")),
            ("7 % 0 = 7", format!("(7 : {c}) % (0 : {c}) = 7")),
            ("0 % 0 = 0", format!("(0 : {c}) % (0 : {c}) = 0")),
            ("7 / 2 = 3", format!("(7 : {c}) / (2 : {c}) = 3")),
            ("7 % 2 = 1", format!("(7 : {c}) % (2 : {c}) = 1")),
            ("12 &&& 10 = 8", format!("(12 : {c}) &&& (10 : {c}) = 8")),
            ("12 ||| 10 = 14", format!("(12 : {c}) ||| (10 : {c}) = 14")),
        ] {
            assert!(
                island_try(&[&format!("theorem tz : {statement} := rfl")]).is_ok(),
                "u{bits}: the kernel must ACCEPT `{label}` — the total semantics of \
                 `UInt{bits}.div`/`.mod` are what this landing's divisor rule is FOR, and if \
                 they have changed the rule must be re-derived, not kept."
            );
        }
        for (label, statement) in [
            ("7 / 0 = 7", format!("(7 : {c}) / (0 : {c}) = 7")),
            ("7 % 0 = 0", format!("(7 : {c}) % (0 : {c}) = 0")),
        ] {
            assert!(
                island_try(&[&format!("theorem tz : {statement} := rfl")]).is_err(),
                "u{bits}: the kernel must REJECT `{label}`. A probe whose positive half \
                 passes and whose negative half also passes has measured nothing."
            );
        }
    }

    // ── 2. `a / 0` denotes the CONSTANT ZERO — so the naive emission is a
    //       WRONG BINARY, not an unproven one ────────────────────────────────
    let env =
        island(&["def dz (a : UInt64) : UInt64 := a / 0", "def mz (a : UInt64) : UInt64 := a % 0"]);
    let zero_body = mint_expr(&env, "0", 1, 64).expect("the constant `0` mints");
    check_faithful(&env, "dz", &zero_body, &carrier_of(64)).expect(
        "MEASURED ADMIT expected: `a / 0` reduces to `0` at an OPEN `a`, because `Nat.div` \
         recurses on the DIVISOR. This is what makes an emitted `Div(a, const 0)` a wrong \
         binary — a correct body for this declaration exists and the compiler would have \
         emitted a trap instead.",
    );
    let identity = mint_expr(&env, "p0", 1, 64).expect("the identity mints");
    assert!(
        check_faithful(&env, "mz", &identity, &carrier_of(64)).is_err(),
        "MEASURED REFUSAL expected: `a % 0` is NOT definitionally the identity at an open \
         `a` — `Nat.modCore` is fuel-driven and sticks. The `/` refusal offers \"write the \
         value directly\" on the strength of the ADMIT above; the `%` refusal must NOT, and \
         this is the measurement that keeps the two apart."
    );

    // ── 3. THE GUARD DOES NOT CLOSE THE GAP ────────────────────────────────
    //
    // At a CLOSED zero divisor the guard is definitionally redundant…
    assert!(
        island_try(&["theorem g1 (a : UInt64) : (if (0:UInt64) == 0 then (0:UInt64) else a / 0) \
             = a / 0 := rfl"])
        .is_ok(),
        "at a CLOSED zero divisor the guard must reduce away — this is finding 2 restated, \
         and it is what makes the OPEN case below a statement about the scrutinee rather \
         than about the guard"
    );
    // …and at an OPEN divisor it is NOT, in either direction.
    for (label, statement) in [
        (
            "the `/` guard",
            "theorem g2 (a : UInt64) (b : UInt64) : \
             (if b == 0 then (0:UInt64) else a / b) = a / b := rfl",
        ),
        (
            "the `%` guard",
            "theorem g3 (a : UInt64) (b : UInt64) : (if b == 0 then a else a % b) = a % b := rfl",
        ),
    ] {
        assert!(
            island_try(&[statement]).is_err(),
            "{label} must NOT be definitionally equal to the bare operator at an OPEN \
             divisor. If it now is, the whole divisor refusal must be re-measured — a \
             guarded emission would become admissible and this landing's boundary would move."
        );
    }
    // The control that keeps the two above from passing for the wrong reason:
    // the BARE identity does hold, so `rfl` at this type is not simply broken.
    assert!(
        island_try(&["theorem g4 (a : UInt64) (b : UInt64) : a / b = a / b := rfl"]).is_ok(),
        "`a / b = a / b` must hold by `rfl`; if it does not, the two refusals above measured \
         a broken `rfl` rather than a stuck `ite`"
    );

    eprintln!(
        "L7-P6 | x / 0 = 0, x % 0 = x (TOTAL) | `a / 0` == const 0 | the guard is NOT defeq \
         at an open divisor"
    );
}

/// Mint a `p{i}`-positional rendering through the FROZEN producer and hand back
/// the term, or the producer's own refusal.
fn mint_expr(env: &Environment, rendering: &str, arity: usize, bits: u32) -> Result<Expr, String> {
    let mut scratch = env.clone();
    let parameters: Vec<String> = (0..arity).map(|index| format!("p{index}")).collect();
    let refs: Vec<&str> = parameters.iter().map(String::as_str).collect();
    trust_spec_elab::admit_expr_function(
        &mut scratch,
        "trust__l7__reflected",
        rendering,
        &refs,
        &machine(bits),
    )?;
    Ok(scratch
        .get_const(&Name::from_string("trust__l7__reflected"))
        .and_then(|c| c.value.clone())
        .expect("an accepted declaration carries a value"))
}

// ═══════ L7-P7 — XOR AND THE SHIFTS DO NOT ELABORATE ═══════

/// **A measured absence one layer further out than this lane reaches.**
///
/// The row family this landing adds would serve `^^^`, `<<<` and `>>>` with one
/// row each and no new machinery — side B is already there, because the FROZEN
/// `elab_term` elaborates `^` through `Nat.xor` and both shifts through
/// multiply/divide by a literal power of two. They are absent anyway, and the
/// blocker is the clean PRELUDE: instance synthesis fails before a term exists.
///
/// Recorded as its own demand with this measurement attached, so the next
/// landing ranks it by evidence rather than by guess — and so that the day the
/// prelude gains the instances, this probe fails and says what to do.
#[test]
fn l7_p7_xor_and_the_shifts_do_not_elaborate_at_a_uint_carrier() {
    for (label, instance, source) in [
        ("^^^", "HXor", "def bx (a : UInt64) (b : UInt64) : UInt64 := a ^^^ b"),
        ("<<<", "HShiftLeft", "def sl (a : UInt64) : UInt64 := a <<< 3"),
        (">>>", "HShiftRight", "def sr (a : UInt64) : UInt64 := a >>> 3"),
    ] {
        let outcome = island_try(&[source]);
        let diagnostics = outcome.err().unwrap_or_else(|| {
            panic!(
                "`{label}` at UInt64 now ELABORATES. The clean prelude has gained the \
                 `{instance}` instance, so this demand is one row away: side B already \
                 elaborates it through the frozen producer. Add the row, a `control_14` \
                 witness and the ledger entry in the same commit, and delete this arm."
            )
        });
        assert!(
            diagnostics.contains(&format!("failed to synthesize instance `{instance}")),
            "`{label}`'s refusal must be INSTANCE SYNTHESIS at the prelude, which is what \
             locates the blocker outside this lane. Got: {diagnostics}"
        );
        eprintln!("L7-P7 | {label:<4} at UInt64 | REJECTED: no `{instance}` instance");
    }
}

// ═══════ L7-P8 — THE PLANNER REFUSES EVERY UNSAFE DIVISOR ═══════

/// **The divisor rule, from side A, on every form a user can write.**
///
/// `l7_p4` measures that a panicking BODY is refused; this measures that a
/// panicking body is never even planned. Both halves are needed: the first is
/// the gate catching an emitter, the second is the compiler declining to ask.
///
/// Every refusal must carry the v7/D3 fix WITH OPTIONS, and the `/` refusal
/// must carry the option `l7_p6` measured (`a / 0` is definitionally the
/// constant `0`) while the `%` refusal must NOT — because the analogous
/// identity does not hold.
///
/// The declarations here all ELABORATE and all kernel-check: what is being
/// measured is the compiler declining to emit for a well-formed declaration,
/// which is a capability boundary, not a rejection of the user's mathematics.
#[test]
fn l7_p8_the_planner_refuses_every_unsafe_divisor() {
    let env = island(&[
        "def dvv (a : UInt64) (b : UInt64) : UInt64 := a / b",
        "def mdv (a : UInt64) (b : UInt64) : UInt64 := a % b",
        "def dz (a : UInt64) : UInt64 := a / 0",
        "def mz (a : UInt64) : UInt64 := a % 0",
        // The CONTROL: the same operators at a positive numeral DO plan, so
        // the refusals below are about the divisor and not about `/` at all.
        "def dv (a : UInt64) : UInt64 := a / 3",
        "def md (a : UInt64) : UInt64 := a % 3",
    ]);

    for (name, offers_the_zero_rewrite) in [("dvv", false), ("mdv", false), ("dz", true)] {
        let refusal = plan_clean_origin_body(&env, name)
            .err()
            .unwrap_or_else(|| panic!("`{name}` must NOT plan — it would emit a panicking body"));
        let text = refusal_text(&refusal);
        assert!(
            text.contains("TOTAL") && text.contains("PANIC"),
            "`{name}`'s refusal must NAME the total-vs-panicking gap rather than reporting a \
             generic capability boundary: {text}"
        );
        assert!(text.contains("options:"), "v7/D3: `{name}` must carry options: {text}");
        assert!(
            text.contains("proof position"),
            "`{name}` must offer the option that always works: {text}"
        );
        assert_eq!(
            text.contains("definitionally equal to the constant `0`"),
            offers_the_zero_rewrite,
            "`{name}`: the \"write the value directly\" option is offered EXACTLY when \
             `l7_p6` measured it to hold — for `a / 0` and for nothing else: {text}"
        );
        eprintln!("L7-P8 | {name:<4} | REFUSED, with options");
    }

    // `a % 0` is refused too, and must NOT be offered a rewrite: `l7_p6`
    // measured that `a % 0` is not definitionally the identity.
    let mz = refusal_text(&plan_clean_origin_body(&env, "mz").expect_err("`mz` must not plan"));
    assert!(mz.contains("TOTAL") && mz.contains("options:"), "{mz}");
    assert!(
        !mz.contains("definitionally equal to the constant"),
        "`a % 0` must not be offered a constant rewrite — the identity does not hold: {mz}"
    );

    // THE CONTROL, so the four refusals above are not a blanket ban on `/`.
    for name in ["dv", "md"] {
        assert!(
            plan_clean_origin_body(&env, name).is_ok(),
            "`{name}` divides by a strictly positive numeral and MUST plan; if it does not, \
             the divisor rule has become a ban on the operator"
        );
    }
}

// ═══ L7-P9 — NESTED TREES: GREEN AT THE KERNEL, NO REALIZATION ═══

/// **The next landing's work item, ranked by measurement rather than by
/// guess.**
///
/// A nested raw-binop tree — and a MIXED one, with a wrapping operator in it —
/// is definitionally identified by the kernel against the frozen producer's
/// parenthesized rendering. So the kernel half and the producer half of the
/// demand are both already done, and the demand is unserved for exactly one
/// reason: the two families realize different MIR SHAPES. `+`/`-`/`*` compose
/// as a linear CALL CHAIN (one `Call` terminator per node) and `&`/`|`/`/`/`%`
/// as a single STATEMENT, so a mixed tree is a block with binop statements
/// interleaved between call terminators — a body neither reader reads.
///
/// The probe asserts BOTH halves: the kernel admits, and the planner refuses.
/// A demand recorded with only the first half would read as "nearly done".
#[test]
fn l7_p9_nested_raw_binop_trees_admit_at_the_kernel_and_have_no_realization() {
    let env = island(&[
        "def mix (a : UInt64) (b : UInt64) : UInt64 := (a &&& b) ||| a",
        "def mixarith (a : UInt64) (b : UInt64) : UInt64 := (a + b) &&& a",
        "def divmix (a : UInt64) (b : UInt64) : UInt64 := (a &&& b) / 3",
    ]);
    for (name, rendering) in [
        ("mix", "((p0 & p1) | p0)"),
        ("mixarith", "((p0 + p1) & p0)"),
        ("divmix", "((p0 & p1) / 3)"),
    ] {
        let side_b = mint_expr(&env, rendering, 2, 64).unwrap_or_else(|e| {
            panic!("`{name}`: the frozen producer must mint `{rendering}`: {e}")
        });
        check_faithful(&env, name, &side_b, &carrier_of(64)).unwrap_or_else(|refusal| {
            panic!(
                "`{name}`: the KERNEL half of the nested demand must be green — the ledger \
                 entry says so, and an entry whose measurement stopped being true ranks the \
                 next landing wrongly: {refusal:?}"
            )
        });
        assert!(
            plan_clean_origin_body(&env, name).is_err(),
            "`{name}` PLANS. The nested tree has acquired a realization; flip its ledger \
             entry from MISS to SERVED and delete this assertion in the same commit."
        );
        eprintln!("L7-P9 | {name:<9} | kernel: ADMIT | plan: refused (no realization)");
    }
}

// ═══ L7-P10 — NO PASS RUNS, SO NOTHING INSERTS THE CHECK FOR US ═══

/// **The question the brief asked as "does the guard survive optimisation",
/// answered for the body this landing actually emits.**
///
/// There is no guard: the divisor is a strictly positive numeral, so the
/// emitted body is one `BinaryOp(Div)` and a `Return`. The question that
/// matters for THAT body is the mirror image — **does anything downstream add
/// the div-by-zero check, or fold the instruction away?** — and the answer is
/// no, in both directions, which is why the well-formedness obligation rests
/// entirely on the divisor rule.
///
/// Established three ways, none of them by reading a comment:
///
/// 1. **The wiring.** `optimized_mir` calls the Clean-origin gate and RETURNS
///    the gated body immediately, before `run_optimization_passes`; the CTFE
///    arm does the same. So no MIR pass ever sees a Clean-origin body — the
///    same measurement `landing6_selection_probes::l6_p6` takes for its extra
///    comparison, restated here because the CONSEQUENCE is different: landing 6
///    pays a cost, and landing 7 loses a safety net that source-built MIR has.
/// 2. **The emitted body**, from the REAL template: one statement, a `Return`,
///    and no `Assert` anywhere.
/// 3. **The template vocabulary**, by an exhaustive match with no wildcard:
///    `TemplateTerminator` has no `Assert` variant to emit even if someone
///    wanted one. Adding one is a compile error here first.
#[test]
fn l7_p10_no_mir_pass_runs_so_the_divisor_rule_is_the_whole_guarantee() {
    // 1. THE WIRING.
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
        "MEASURED: `optimized_mir` must RETURN the gated body directly. If a pass ever ran on \
         it, this landing's accounting changes in BOTH directions — a pass could insert the \
         div-by-zero check the divisor rule currently makes unnecessary, and a pass could \
         rewrite an instruction the kernel already gated."
    );
    assert!(
        !arm.contains("run_optimization_passes(tcx"),
        "nothing may optimize a Clean-origin body on the codegen arm"
    );
    assert!(
        wiring.contains("run_optimization_passes(tcx, &mut body);"),
        "the ordinary codegen path still optimizes; the Clean-origin path is the exception — \
         without this the assertion above would pass vacuously"
    );

    // 2. THE EMITTED BODY, at every width.
    for bits in WIDTHS {
        let carrier = format!("UInt{bits}");
        let env = island(&[&format!("def dv (a : {carrier}) : {carrier} := a / 3")]);
        let (_, emitted) = plan_and_emit(&env, "dv", bits);
        assert_eq!(emitted.body.blocks.len(), 1, "u{bits}: one block");
        assert_eq!(emitted.body.blocks[0].stmts.len(), 1, "u{bits}: one statement");
        assert!(
            matches!(emitted.body.blocks[0].terminator, Terminator::Return),
            "u{bits}: the ONLY terminator is `Return` — no `Assert`, and no pass will add one"
        );
    }

    // 3. THE TEMPLATE VOCABULARY, by type. Exhaustive, no wildcard: a future
    // `Assert` variant is a compile error here before it is anything else.
    fn terminator_vocabulary(terminator: &TemplateTerminator) -> &'static str {
        match terminator {
            TemplateTerminator::Return => "return",
            TemplateTerminator::Goto(_) => "goto",
            TemplateTerminator::SwitchIntZero { .. } => "switch",
            TemplateTerminator::Call { .. } => "call",
        }
    }
    assert_eq!(terminator_vocabulary(&TemplateTerminator::Return), "return");

    eprintln!(
        "L7-P10 | `optimized_mir` returns the gated body BEFORE `run_optimization_passes` | \
         emitted `/` body: 1 statement, `Return`, NO `Assert` | the divisor rule is the whole \
         guarantee"
    );
}

// ═══════════════ the table's own integrity, for this family ═══════════════

/// The four rows are exactly the four operators, each with ONE side-A selector
/// and a realization no other row has.
///
/// Stated here rather than only in `table_controls` because the coordinates
/// that matter for THIS family are the ones a generic control cannot know: one
/// selector each (the carrier spelling is deliberately absent — `l7_p1`), and
/// four distinct `MirShape::RawBinOp` values so H-C never applies.
#[test]
fn l7_the_row_family_is_four_rows_with_one_selector_each() {
    let rows: Vec<&'static str> = ROWS
        .iter()
        .filter(|row| matches!(row.mir, MirShape::RawBinOp(_)))
        .map(|row| row.name)
        .collect();
    assert_eq!(rows, vec!["uint.and", "uint.or", "uint.div", "uint.mod"]);

    for row in ROWS.iter().filter(|row| matches!(row.mir, MirShape::RawBinOp(_))) {
        assert_eq!(
            row.side_a.len(),
            1,
            "row `{}` carries {} side-A selectors. It must carry exactly ONE — the surface \
             class — because `l7_p1` measured that no source produces the carrier method and \
             side B renders the `toNat`/`ofNat` round trip rather than the carrier method \
             either. A second selector would be a reader arm for a spelling neither side \
             emits.",
            row.name,
            row.side_a.len()
        );
    }

    let realizations: Vec<MirShape> =
        ROWS.iter().filter(|row| matches!(row.mir, MirShape::RawBinOp(_))).map(|r| r.mir).collect();
    let distinct = realizations
        .iter()
        .enumerate()
        .filter(|(index, mir)| !realizations[..*index].contains(mir))
        .count();
    assert_eq!(
        distinct, 4,
        "the four rows must realize four DISTINCT MIR values; if two collapsed, H-C would \
         apply and neither escape is available (same layer, same carrier, same gate)"
    );
}

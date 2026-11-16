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
//! | `^^^`, `<<<`, `>>>` | **all three ELABORATE since clean `bf31976f48`** (2026-09-23). `^^^` and `>>>` are now rows (`l7_p11`..`l7_p15`); `<<<` has NO row: swept over every amount at every width, the gate admits the frozen producer's reading at exactly `k = 1` (the function `uint.mul` already serves as `a * 2`) and refuses every other amount below the width — `l7_p7`, the re-armed tripwire |
//! | is the shift amount a soundness boundary? | **no** — Lean and MIR both reduce it modulo the width (`l7_p14`); it is a side-B capability boundary, refused at the planner with options |
//! | does the planner hold the divisor rule? | **yes, on every unsafe form** — `l7_p8` |
//! | nested trees | **green at the kernel, no realization** — `l7_p9` |
//! | does anything downstream insert the div-by-zero check? | **no — no MIR pass runs at all** (`l7_p10`), so the divisor rule is the whole guarantee |
//! | do the refusals name the whole family? | **yes, as lists read from `raw_binop_rows`** — the `==` boundary (`l7_p15`), the generic fall-through and the note's callable-fragment paragraph (`l7_p16`), each compared with an independently written list |
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
use trust_clean_origin::table::{
    CarrierClass, MirShape, ROWS, ladder_row, no_selection_row, raw_binop_rows,
};
use trust_clean_origin::{
    BOOL_EXPRESSION_MAX_OPS, CleanOriginPlan, CleanOriginShape, EmitRefusal, FaithfulnessMethod,
    GateRefusal, admit_lowering, check_faithful, plan_clean_origin_body,
};
use trust_spec_elab::{Domain, MachineUIntWidth};
use trust_types::admissible_body::{
    ArithOperand, BeqOperand, RawBinOpKind, SelectCmp, recognize_admissible_body,
    recognize_raw_binop, recognize_select_beq, recognize_select_beq_general,
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

/// Landing 7's four operators, with the source token, the surface class and
/// its projection. `l7_p1`..`l7_p4` are derived from this table, so those
/// probes cannot silently measure three of the four. The two rows that joined
/// on 2026-09-23 (`^^^`, `>>>`) are measured by `l7_p11`..`l7_p15` against
/// their own tables.
const OPERATORS: [(RawBinOpKind, &str, &str, &str); 4] = [
    (RawBinOpKind::BitAnd, "&&&", "HAnd", "hAnd"),
    (RawBinOpKind::BitOr, "|||", "HOr", "hOr"),
    (RawBinOpKind::Div, "/", "HDiv", "hDiv"),
    (RawBinOpKind::Rem, "%", "HMod", "hMod"),
];

/// Every raw-binop operator, in the user's surface syntax, as a refusal that
/// names the family must list it — written out HERE, independently of
/// `table::raw_binop_rows` and `table::raw_binop_surface_token`, so that a
/// derivation which drops, adds or duplicates a token is CAUGHT rather than
/// restated. Adding a row means adding its token here in the same commit.
const RAW_BINOP_TOKENS: [&str; 6] = ["&&&", "|||", "/", "%", "^^^", ">>>"];

/// The operand rules, as every list of [`RAW_BINOP_TOKENS`] must state them —
/// independently written, like the token list: the divisor rule names exactly
/// `/` and `%`, the shift-amount rule exactly `>>>`.
const RAW_BINOP_RULES: [&str; 2] = [
    "a `/` or `%` divisor must be a strictly positive numeral",
    "a `>>>` amount must be a numeral below the width",
];

/// The operator LIST that sits between `before` and the first `after`
/// following it in `text`: split on `, `, each item's backticks stripped.
///
/// Panics, naming `what`, if a delimiter is missing or an item is not ONE
/// backticked token — a list this cannot parse is a list a reader cannot
/// either. Reading the list SEGMENT, rather than counting a token's mentions
/// anywhere in the text, is the point: the rule parentheticals name `/`, `%`
/// and `>>>` again, so a mention count is satisfied with all three missing
/// from the list itself.
fn listed_operators(text: &str, before: &str, after: &str, what: &str) -> Vec<String> {
    let start = text
        .find(before)
        .unwrap_or_else(|| panic!("{what}: the list's opening `{before}` is missing:\n{text}"))
        + before.len();
    let len = text[start..].find(after).unwrap_or_else(|| {
        panic!("{what}: the list's closing `{after}` does not follow `{before}`:\n{text}")
    });
    text[start..start + len]
        .split(", ")
        .map(|item| {
            item.strip_prefix('`')
                .and_then(|token| token.strip_suffix('`'))
                .filter(|token| !token.is_empty() && !token.contains('`'))
                .unwrap_or_else(|| {
                    panic!("{what}: list item `{item}` is not one backticked operator:\n{text}")
                })
                .to_owned()
        })
        .collect()
}

/// The list between `before` and `after` is EXACTLY [`RAW_BINOP_TOKENS`]: the
/// same set, nothing missing, nothing extra, no token twice.
fn assert_lists_exactly_the_raw_binop_family(text: &str, before: &str, after: &str, what: &str) {
    let mut listed = listed_operators(text, before, after, what);
    listed.sort_unstable();
    let mut expected: Vec<String> = RAW_BINOP_TOKENS.iter().map(|t| (*t).to_owned()).collect();
    expected.sort_unstable();
    assert_eq!(
        listed, expected,
        "{what}: the operator list must be exactly the raw-binop rows' tokens, each once:\n{text}"
    );
}

/// Each of [`RAW_BINOP_RULES`] appears in `text` exactly `times` times — once
/// per operator list the text carries.
fn assert_states_the_raw_binop_rules(text: &str, times: usize, what: &str) {
    for rule in RAW_BINOP_RULES {
        assert_eq!(
            text.matches(rule).count(),
            times,
            "{what}: the rule \"{rule}\" must be stated once per operator list ({times}):\n{text}"
        );
    }
}

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
        TemplateOperand::UIntScalar { value, width } => {
            Operand::Constant(ConstValue::Uint(value, width))
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
            callee_key: None,
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
    // The reader's vocabulary, DERIVED from the rows rather than counted in
    // prose: the message said "the four operators" after it became six.
    let family: Vec<BinOp> =
        raw_binop_rows(CarrierClass::MachineUInt).map(|(_, op)| op.mir_binop()).collect();
    for wrapping in [BinOp::Add, BinOp::Sub, BinOp::Mul] {
        assert!(
            !family.contains(&wrapping),
            "a raw-binop row realizes `BinaryOp({wrapping:?})`: {family:?}"
        );
    }
    assert!(
        recognize_raw_binop(&raw_add).is_none(),
        "the raw-binop reader read `BinaryOp(Add)`. It reads exactly the {} operators whose \
         realization IS the raw operator ({family:?}, one per `raw_binop_rows` row); \
         `Add`/`Sub`/`Mul` are not among them.",
        family.len()
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

// ═══ L7-P7 — `<<<`: THE GATE ADMITS ONE AMOUNT, AND NOTHING PLANS IT ═══

/// The `<<<` amounts, in `0..N`, at which `check_faithful` ADMITS the frozen
/// producer's reading `{C}.mul a ({C}.ofNat 2^k)` against a declaration
/// `a <<< k` — measured by `l7_p7` at EVERY amount at every width, and the same
/// set at all four. Every other amount below the width is a completed
/// `Disagreement`; every amount at or above it the producer refuses to mint.
const SHL_AMOUNTS_THE_GATE_ADMITS: [u32; 1] = [1];

/// **The one operator of the three still without a row, and why — swept over
/// EVERY amount at every width, with the tripwire re-armed on each thing that
/// would change the decision.**
///
/// Until clean `bf31976f48` this probe measured that `^^^`, `<<<` and `>>>` did
/// not ELABORATE at a `UInt{N}` carrier (instance synthesis failed in the
/// prelude). That pin gave the prelude `HXor`/`HShiftLeft`/`HShiftRight`, the
/// probe fired, and the three were measured separately: `^^^` and `>>>` are
/// rows now (`l7_p11`..`l7_p15`), and their arms here were deleted in the same
/// commit, as this probe's own text demanded.
///
/// `<<<` elaborates — `HShiftLeft.hShiftLeft … instHShiftLeftUInt{N}` — and
/// the frozen producer mints a side B for every literal amount below the width,
/// spelled `{C}.mul a ({C}.ofNat 2^k)`. The gate's verdict on that reading,
/// measured at every `k` in `0..N` at u8/u16/u32/u64:
///
/// | amount | verdict |
/// |---|---|
/// | `1` | **ADMIT**, by `DefinitionalEquality` |
/// | `0`, `2..N` | REFUSE — a completed `Disagreement` (definitional equality, then the structural-induction fallback, declined), never a resource rail |
/// | `>= N`, or a variable | no side B — the producer refuses to mint |
///
/// The mechanism, measured in the kernel's own voice below: Clean's
/// `Nat.shiftLeft x (k+1)` unfolds one DOUBLING at a time, so
/// `Nat.shiftLeft x 1` IS `x * 2` (and not `2 * x`), `Nat.shiftLeft x 2` IS
/// `x * 2 * 2` (and not `x * 4`), and `Nat.shiftLeft x 0` IS `x` (and not
/// `x * 1`, which is stuck at an open `x`). The producer's single
/// multiplication by `2^k` coincides with the chain of doublings at exactly one
/// amount.
///
/// **No `uint.shl` row, by decision as well as measurement.** A row serving
/// only `k = 1` could not reuse the shift-amount rule (`k < N` would plan
/// amounts the gate refuses), so it would need its own one-amount rule, a
/// `Shl` reader arm, a compiler arm and a witness — for a function the
/// `uint.mul` row already serves: `a * 2` plans and admits at every width
/// (measured here too). The ledger says so; this probe keeps it true.
///
/// The tripwire fires if the admitted set GROWS or SHRINKS at any width, if a
/// refusal is ever anything but a completed `Disagreement`, if the planner
/// plans any `<<<`, if side B stops being `{C}.mul`, or if the producer mints
/// a variable or out-of-range amount.
#[test]
fn l7_p7_the_gate_admits_the_left_shift_only_at_amount_one_and_nothing_plans_it() {
    for bits in WIDTHS {
        let c = format!("UInt{bits}");
        let mut sources: Vec<String> =
            (0..bits).map(|k| format!("def sl{k} (a : {c}) : {c} := a <<< {k}")).collect();
        sources.push(format!("def slv (a : {c}) (b : {c}) : {c} := a <<< b"));
        sources.push(format!("def dbl (a : {c}) : {c} := a * 2"));
        let refs: Vec<&str> = sources.iter().map(String::as_str).collect();
        let env = island_try(&refs).unwrap_or_else(|diagnostics| {
            panic!(
                "`<<<` at {c} no longer ELABORATES. It did at clean `bf31976f48`; a prelude \
                 that lost `HShiftLeft` moves this demand back to `first-party/clean`, and the \
                 ledger entry must say so: {diagnostics}"
            )
        });

        let mut admitted = Vec::new();
        let mut admitted_side_b = Vec::new();
        for k in 0..bits {
            let name = format!("sl{k}");
            assert!(
                plan_clean_origin_body(&env, &name).is_err(),
                "u{bits} `a <<< {k}` PLANS. `<<<` has acquired a realization without a row — \
                 re-measure this probe before anything emits it."
            );
            let rendering = format!("p0 << {k}");
            let side_b = mint_expr(&env, &rendering, 1, bits).unwrap_or_else(|e| {
                panic!("u{bits}: the frozen producer must still mint `{rendering}`: {e}")
            });
            let (head, _) = uncurry(peel(&side_b, 1));
            assert!(
                matches!(
                    head.kind(),
                    ExprKind::Const(n, _) if *n == Name::from_string(&format!("{c}.mul"))
                ),
                "u{bits}: side B for `{rendering}` is no longer `{c}.mul …` — the mechanism \
                 recorded above has moved; re-measure: {side_b}"
            );
            match check_faithful(&env, &name, &side_b, &carrier_of(bits)) {
                Ok(faithful) => {
                    assert_eq!(
                        faithful.method(),
                        FaithfulnessMethod::DefinitionalEquality,
                        "u{bits} `a <<< {k}`: admitted, but not by definitional equality"
                    );
                    admitted.push(k);
                    admitted_side_b.push(format!("{side_b}"));
                }
                Err(GateRefusal::Disagreement { .. }) => {}
                Err(other) => panic!(
                    "u{bits} `a <<< {k}`: the gate refused as {other:?}, which is not a completed \
                     `Disagreement`. A resource rail is not a verdict on the reading, so this \
                     amount's place in `SHL_AMOUNTS_THE_GATE_ADMITS` is UNMEASURED until it \
                     completes."
                ),
            }
        }
        assert_eq!(
            admitted, SHL_AMOUNTS_THE_GATE_ADMITS,
            "u{bits}: the set of `<<<` amounts the gate admits against the frozen producer's \
             `{c}.mul` reading MOVED. If it grew toward every amount, a `uint.shl` row with the \
             shift-amount rule may now be sound — add `RawBinOpKind::Shl`, the row, the compiler \
             arm, a `control_14` witness and the ledger entry in one commit. If it shrank or \
             moved, the ledger's `<<<` entry and this constant must be re-stated."
        );

        // Beyond the width, and a variable amount: no side B at all.
        for k in [bits, bits + 1, 2 * bits + 1] {
            let refusal =
                mint_expr(&env, &format!("p0 << {k}"), 1, bits).err().unwrap_or_else(|| {
                    panic!("u{bits}: the frozen producer now mints `p0 << {k}` — re-measure")
                });
            assert!(refusal.contains("out of range"), "u{bits} `p0 << {k}`: {refusal}");
        }
        assert!(
            plan_clean_origin_body(&env, "slv").is_err(),
            "u{bits} `a <<< b` PLANS — re-measure this probe before anything emits it."
        );
        let variable = mint_expr(&env, "p0 << p1", 2, bits).err().unwrap_or_else(|| {
            panic!(
                "u{bits}: the frozen producer now mints a VARIABLE left shift. Re-measure the \
                 gate against `slv` — this may be the side B `<<<` was missing."
            )
        });
        assert!(variable.contains("literal shift amount"), "u{bits}: {variable}");

        // The one admitted amount's FUNCTION is served today, by another row.
        let (plan, emitted) = plan_and_emit(&env, "dbl", bits);
        assert_eq!(ladder_row(plan.shape()).expect("row").name, "uint.mul", "u{bits} `a * 2`");
        admit_lowering(&env, &plan, &emitted).unwrap_or_else(|refusal| {
            panic!("u{bits} `a * 2` must admit end to end through `uint.mul`: {refusal:?}")
        });

        eprintln!(
            "L7-P7 | u{bits:<2} `<<<` | 0..{bits} swept | GATE ADMITS {admitted:?} (side B \
             {admitted_side_b:?}), every other amount a completed Disagreement | nothing plans \
             | `a * 2` admits via uint.mul"
        );
    }

    // THE MECHANISM, in the kernel's own voice: `Nat.shiftLeft` unfolds one
    // doubling at a time, and the producer multiplies once by `2^k`.
    for (label, source, admitted) in [
        (
            "Nat.shiftLeft x 1 = x * 2",
            "theorem t (x : Nat) : Nat.shiftLeft x 1 = x * 2 := rfl",
            true,
        ),
        (
            "Nat.shiftLeft x 1 = 2 * x",
            "theorem t (x : Nat) : Nat.shiftLeft x 1 = 2 * x := rfl",
            false,
        ),
        (
            "Nat.shiftLeft x 2 = x * 2 * 2",
            "theorem t (x : Nat) : Nat.shiftLeft x 2 = x * 2 * 2 := rfl",
            true,
        ),
        (
            "Nat.shiftLeft x 2 = x * 4",
            "theorem t (x : Nat) : Nat.shiftLeft x 2 = x * 4 := rfl",
            false,
        ),
        (
            "Nat.shiftLeft x 3 = x * 8",
            "theorem t (x : Nat) : Nat.shiftLeft x 3 = x * 8 := rfl",
            false,
        ),
        ("Nat.shiftLeft x 0 = x", "theorem t (x : Nat) : Nat.shiftLeft x 0 = x := rfl", true),
        ("x * 1 = x", "theorem t (x : Nat) : x * 1 = x := rfl", false),
        ("a <<< 1 = a * 2 at UInt64", "theorem t (a : UInt64) : a <<< 1 = a * 2 := rfl", true),
        ("a <<< 3 = a * 8 at UInt64", "theorem t (a : UInt64) : a <<< 3 = a * 8 := rfl", false),
        // GROUND controls — the semantics are right, including Lean's
        // modulo-the-width amount, and `rfl` is not simply broken at `<<<`.
        ("(1 : UInt8) <<< 3 = 8", "theorem t : (1 : UInt8) <<< 3 = 8 := rfl", true),
        ("(1 : UInt64) <<< 65 = 2", "theorem t : (1 : UInt64) <<< 65 = 2 := rfl", true),
        ("(1 : UInt64) <<< 65 = 0", "theorem t : (1 : UInt64) <<< 65 = 0 := rfl", false),
    ] {
        assert_eq!(
            island_try(&[source]).is_ok(),
            admitted,
            "`{label}` by `rfl`: expected {}. This is the measured reason the gate admits `<<<` \
             at exactly the amounts it does; if it moved, so did the reason.",
            if admitted { "ACCEPTED" } else { "REJECTED" }
        );
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
    for (name, rendering, head, row) in [
        ("mix", "((p0 & p1) | p0)", "HOr.hOr", "uint.or"),
        ("mixarith", "((p0 + p1) & p0)", "HAnd.hAnd", "uint.and"),
        ("divmix", "((p0 & p1) / 3)", "HDiv.hDiv", "uint.div"),
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
        let refusal = plan_clean_origin_body(&env, name).err().unwrap_or_else(|| {
            panic!(
                "`{name}` PLANS. The nested tree has acquired a realization; flip its ledger \
                 entry from MISS to SERVED and delete this assertion in the same commit."
            )
        });
        // …and the refusal says WHY truthfully: the root head HAS a row, and
        // what has no realization is the nesting (`l7_p17` measures the site).
        let reason = refusal_text(&refusal);
        let cited = format!(
            "`{head}` at {} IS selected — by row `{row}`",
            CarrierClass::MachineUInt.label()
        );
        assert!(
            reason.contains(&cited) && !reason.contains("no selection row for"),
            "`{name}`: its head `{head}` is selected by `{row}`, so the refusal must say so and \
             must not claim a missing row:\n{reason}"
        );
        eprintln!(
            "L7-P9 | {name:<9} | kernel: ADMIT | plan: refused (no realization; `{row}` cited \
             as selecting `{head}`)"
        );
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

// ═══ L7-P11..P15 — `^^^` AND `>>>`, THE TWO ROWS CLEAN `bf31976f48` UNLOCKED ═══

/// The two operators the 2026-09-23 prelude made reachable, with the source
/// token, the surface class and its projection. As [`OPERATORS`] is for the
/// first four, everything in `l7_p11`..`l7_p15` is derived from this table.
const NEW_OPERATORS: [(RawBinOpKind, &str, &str, &str); 2] = [
    (RawBinOpKind::BitXor, "^^^", "HXor", "hXor"),
    (RawBinOpKind::Shr, ">>>", "HShiftRight", "hShiftRight"),
];

/// **Side A for `^^^` and `>>>`, pinned node by node at every width — `l7_p1`
/// for the two new operators, taken BEFORE the rows were trusted.**
///
/// The same six-argument spine — three carrier types, a BARE
/// `inst{Class}{Carrier}` instance constant, then the two operands with the de
/// Bruijn inversion — and the same NEGATIVE half: `UInt{N}.xor` and
/// `UInt{N}.shiftRight` are declared constants at this pin and no source
/// produces either, which is why each row carries ONE side-A selector.
///
/// The shift is pinned twice, because its right operand is the one this lane
/// constrains: at a parameter (`a >>> b`, which elaborates and is refused by
/// the planner, `l7_p14`) and at a numeral, whose spelling is `UInt{N}.ofNat
/// 3` — the carrier numeral `recognise_arith_operand` reads.
#[test]
fn l7_p11_xor_and_shr_are_pinned_node_by_node_at_every_width() {
    for bits in WIDTHS {
        let carrier = format!("UInt{bits}");
        let mut sources: Vec<String> = NEW_OPERATORS
            .iter()
            .map(|(_, token, class, _)| {
                format!("def op{class} (a : {carrier}) (b : {carrier}) : {carrier} := a {token} b")
            })
            .collect();
        sources.push(format!("def shrlit (a : {carrier}) : {carrier} := a >>> 3"));
        let refs: Vec<&str> = sources.iter().map(String::as_str).collect();
        let env = island(&refs);

        for (_, _, class, projection) in NEW_OPERATORS {
            let value = definition_value(&env, &format!("op{class}"));
            let body = peel(&value, 2);
            let (head, args) = uncurry(body);
            let ExprKind::Const(name, levels) = head.kind() else {
                panic!("u{bits} `{class}`: the body's head is not a constant: {body}");
            };
            assert_eq!(*name, Name::from_string(&format!("{class}.{projection}")), "u{bits}");
            assert_eq!(levels.len(), 3, "u{bits} `{class}`: three universe parameters");
            assert_eq!(args.len(), 6, "u{bits} `{class}`: {body}");
            for ty in &args[..3] {
                assert!(
                    matches!(ty.kind(), ExprKind::Const(n, _) if *n == Name::from_string(&carrier)),
                    "u{bits} `{class}`: a HETEROGENEOUS instantiation: {body}"
                );
            }
            assert!(
                matches!(
                    args[3].kind(),
                    ExprKind::Const(n, _)
                        if *n == Name::from_string(&format!("inst{class}{carrier}"))
                ),
                "u{bits} `{class}`: the instance is not the bare prelude constant: {}",
                args[3]
            );
            assert!(matches!(args[4].kind(), ExprKind::BVar(1)), "u{bits} `{class}`: left");
            assert!(matches!(args[5].kind(), ExprKind::BVar(0)), "u{bits} `{class}`: right");
        }

        // The numeral amount's spelling.
        let value = definition_value(&env, "shrlit");
        let (_, args) = uncurry(peel(&value, 1));
        let (numeral_head, numeral_args) = uncurry(args[5]);
        assert!(
            matches!(
                numeral_head.kind(),
                ExprKind::Const(n, _) if *n == Name::from_string(&format!("{carrier}.ofNat"))
            ) && numeral_args.len() == 1,
            "u{bits}: the shift amount `3` is not spelled `{carrier}.ofNat 3`: {}",
            args[5]
        );

        // The numeral amount's DICTIONARY. Since clean `d2d5868b7` a numeral
        // shift amount resolves through Lean's `@[default_instance]` bridge
        // over the prelude's homogeneous `ShiftRight` instance, while the
        // variable amount above keeps the direct `instHShiftRight{C}`. The
        // emitter reads both spellings (`is_prelude_homogeneous_instance`);
        // this pins that the elaborator produces exactly that bridge.
        let (bridge, bridge_args) = uncurry(args[3]);
        assert!(
            matches!(bridge.kind(), ExprKind::Const(n, levels)
                if *n == Name::from_string("instHShiftRight")
                    && levels.len() == 1
                    && levels[0].is_zero())
                && bridge_args.len() == 2
                && matches!(bridge_args[0].kind(),
                    ExprKind::Const(n, _) if *n == Name::from_string(&carrier))
                && matches!(bridge_args[1].kind(),
                    ExprKind::Const(n, _) if *n == Name::from_string(&format!("instShiftRight{carrier}"))),
            "u{bits}: the numeral shift's dictionary is not the default bridge over \
             `instShiftRight{carrier}`: {}",
            args[3]
        );

        // THE NEGATIVE HALF. The carrier methods EXIST at this pin — declared,
        // and the surface operator is definitionally the method — and no
        // source produces them, which is the whole reason the rows carry only
        // the surface selector. (`trust-clean-ir`'s `independent_reflector_a`
        // cites the first two facts for `Xor`.)
        for suffix in ["xor", "shiftRight"] {
            assert!(
                env.get_const(&Name::from_string(&format!("{carrier}.{suffix}"))).is_some(),
                "u{bits}: `{carrier}.{suffix}` is no longer a declared constant"
            );
        }
        assert!(
            island_try(&[&format!(
                "theorem t (a b : {carrier}) : a ^^^ b = {carrier}.xor a b := rfl"
            )])
            .is_ok(),
            "u{bits}: `a ^^^ b = {carrier}.xor a b` is no longer `rfl`"
        );
        for suffix in ["xor", "shiftRight"] {
            let spelling = Name::from_string(&format!("{carrier}.{suffix}"));
            for name in ["opHXor", "opHShiftRight", "shrlit"] {
                assert!(
                    !mentions(&definition_value(&env, name), &spelling),
                    "u{bits}: `{carrier}.{suffix}` appears in `{name}`'s elaborated body. The \
                     rows carry only the SURFACE selector on the strength of this measurement; \
                     add the carrier selector AND a `control_14` witness in the same commit."
                );
            }
        }
    }
}

/// **`^^^` and `>>>` end to end** — plan, the REAL template, the rendered body,
/// side B's SEPARATE reader, the FROZEN producer and the kernel gate, at every
/// width.
///
/// `^^^` over both operand kinds, with the numeral on EITHER side (`15 ^^^ a`
/// plans with the literal on the left and is emitted that way — no operand is
/// reordered) and at the carrier's ALL-ONES value (`255` at u8, `u64::MAX` at
/// u64), the numeral whose `ofNat` round trip is widest; `>>>` at three numeral
/// amounts including the two edges the shift-amount rule admits (`0` and
/// `N - 1`). Each emitted body is ONE statement and a `Return` — no `Assert`,
/// and none is needed: `^` cannot fail, and MIR's `Shr` reduces its amount
/// modulo the width exactly as Lean does (`l7_p14`), so it has no overflow case
/// either.
///
/// The emitted operator is pinned to a CONCRETE `BinOp` per row — not to
/// `op.mir_binop()`, which is the very function this file's renderer builds
/// the statement with, so comparing against it would compare the renderer with
/// itself.
#[test]
fn l7_p12_xor_and_shr_admit_end_to_end() {
    for bits in WIDTHS {
        let carrier = format!("UInt{bits}");
        let top = u128::from(bits - 1);
        let ones = (1u128 << bits) - 1;
        let env = island(&[
            &format!("def bxor (a : {carrier}) (b : {carrier}) : {carrier} := a ^^^ b"),
            &format!("def bxorlit (a : {carrier}) : {carrier} := a ^^^ 15"),
            &format!("def bxorones (a : {carrier}) : {carrier} := a ^^^ {ones}"),
            &format!("def bxorleft (a : {carrier}) : {carrier} := 15 ^^^ a"),
            &format!("def shr3 (a : {carrier}) : {carrier} := a >>> 3"),
            &format!("def shr0 (a : {carrier}) : {carrier} := a >>> 0"),
            &format!("def shrtop (a : {carrier}) : {carrier} := a >>> {top}"),
        ]);

        let (param0, param1) = (ArithOperand::Param(0), ArithOperand::Param(1));
        for (name, op, mir, left, right) in [
            ("bxor", RawBinOpKind::BitXor, BinOp::BitXor, param0, param1),
            ("bxorlit", RawBinOpKind::BitXor, BinOp::BitXor, param0, ArithOperand::Const(15)),
            ("bxorones", RawBinOpKind::BitXor, BinOp::BitXor, param0, ArithOperand::Const(ones)),
            ("bxorleft", RawBinOpKind::BitXor, BinOp::BitXor, ArithOperand::Const(15), param0),
            ("shr3", RawBinOpKind::Shr, BinOp::Shr, param0, ArithOperand::Const(3)),
            ("shr0", RawBinOpKind::Shr, BinOp::Shr, param0, ArithOperand::Const(0)),
            ("shrtop", RawBinOpKind::Shr, BinOp::Shr, param0, ArithOperand::Const(top)),
        ] {
            let (plan, emitted) = plan_and_emit(&env, name, bits);
            assert_eq!(
                plan.shape(),
                &CleanOriginShape::RawBinOp { op, left, right },
                "u{bits} `{name}`: the planned shape"
            );
            assert_eq!(
                ladder_row(plan.shape()).expect("row").mir,
                MirShape::RawBinOp(op),
                "u{bits} `{name}`: the selected realization"
            );
            assert_eq!(emitted.body.blocks.len(), 1, "u{bits} `{name}`: one block");
            assert_eq!(emitted.body.blocks[0].stmts.len(), 1, "u{bits} `{name}`: one statement");
            assert!(
                matches!(emitted.body.blocks[0].terminator, Terminator::Return),
                "u{bits} `{name}`: the terminator is `Return` — no call, no branch, no `Assert`"
            );
            let Rvalue::BinaryOp(binop, ..) = sole_rvalue(&mut emitted.clone()).clone() else {
                panic!("u{bits} `{name}`: the sole statement is not a binary op");
            };
            assert_eq!(binop, mir, "u{bits} `{name}`: the emitted operator");

            let read = recognize_raw_binop(&emitted)
                .unwrap_or_else(|| panic!("u{bits} `{name}`: side B must read the emitted body"));
            assert_eq!(read.op, op, "u{bits} `{name}`: side B's operator");
            assert_eq!(read.left, left, "u{bits} `{name}`: side B's left operand");
            assert_eq!(read.right, right, "u{bits} `{name}`: side B's right operand");

            admit_lowering(&env, &plan, &emitted).unwrap_or_else(|refusal| {
                panic!("u{bits} `{name}` must admit end to end: {refusal:?}")
            });
        }
        eprintln!(
            "L7-P12 | u{bits:<2} | `^^^` (param, 15, {ones}, literal-left), `>>>` at 0 / 3 / {top} \
             | ADMIT"
        );
    }
}

/// **One construct changed each, on the two new rows — and the gate catches
/// every one.** `l7_p4`'s method: the base bodies are REAL emissions, each
/// mutant goes back through the REAL `admit_lowering`, and the unmutated body
/// is re-admitted first so the refusal is about the mutation.
///
/// | # | mutation | why it must be caught |
/// |---|---|---|
/// | 1 | `\|` for `^` | a different function, same operands |
/// | 2 | `&` for `^` | as above |
/// | 3 | `^` for `\|` | the converse, on an EXISTING row's body |
/// | 4 | operands SWAPPED on `^` | **commutative, and STILL refused** — the plan fixes the operand order, and the real gate refuses the swapped reading too (measured below) |
/// | 5 | wrong mask (`14` for `15`) | an emitter that baked in the wrong constant |
/// | 6 | `<<` for `>>` | the operator with no row; side B does not read `Shl` at all |
/// | 7 | `/` for `>>`, same constant | `a / 3` is not `a >> 3` |
/// | 8 | `/ 8` for `>> 3` | **an EQUIVALENT body, refused anyway** — the sealed plan is the decision, and side B's reading must agree with it |
/// | 9 | amount `4` for `3` | the wrong constant |
/// | 10 | amount encoded at u32 in a u64 body | width skew |
/// | 11 | a VARIABLE amount for `a >>> 3` | the plan says a numeral |
/// | 12 | operands SWAPPED on `>>` | `3 >> a` is another function entirely |
/// | 13 | operands SWAPPED on `15 ^^^ a` | #4 with the numeral on the LEFT, where the plan keeps it |
///
/// **Measured, as in `l7_p4`: THIS lane refuses all thirteen** — eleven at the
/// structural comparison against the sealed plan, two (`<<`, and the
/// width-skewed amount) at side B's reader. That is fail-closed and it is this
/// lane agreeing with itself, so the independent layers are measured too: the
/// REAL gate for #4 and #13 — `check_faithful`, definitional equality and then
/// its structural-induction fallback, returns a completed `Disagreement` (not a
/// resource rail) for the frozen producer's reading of each swapped body — and
/// the FROZEN producer as `l7_p4` measures it for the divisor: it will not mint
/// a variable or out-of-range amount, and it does mint the forms this lane
/// emits.
#[test]
fn l7_p13_every_xor_and_shr_mutation_is_refused() {
    let bits = 64u32;
    let env = island(&[
        "def bxor (a : UInt64) (b : UInt64) : UInt64 := a ^^^ b",
        "def bxorlit (a : UInt64) : UInt64 := a ^^^ 15",
        "def bxorleft (a : UInt64) : UInt64 := 15 ^^^ a",
        "def bor (a : UInt64) (b : UInt64) : UInt64 := a ||| b",
        "def shr3 (a : UInt64) (b : UInt64) : UInt64 := a >>> 3",
    ]);

    let mut refused = 0usize;
    let mut check = |label: &str, name: &str, mutate: &dyn Fn(&mut VerifiableFunction)| {
        let (plan, mut emitted) = plan_and_emit(&env, name, bits);
        admit_lowering(&env, &plan, &emitted)
            .unwrap_or_else(|r| panic!("`{name}` must admit before mutation: {r:?}"));
        mutate(&mut emitted);
        let refusal = admit_lowering(&env, &plan, &emitted).err().unwrap_or_else(|| {
            panic!(
                "MUTATION `{label}` ON `{name}` WAS ACCEPTED. A body that is not the one the \
                 plan asked for was admitted."
            )
        });
        eprintln!("L7-P13 | {label:<44} | REFUSED: {}", short(&refusal));
        refused += 1;
    };
    let set_op = |op: BinOp| {
        move |f: &mut VerifiableFunction| {
            if let Rvalue::BinaryOp(slot, ..) = sole_rvalue(f) {
                *slot = op;
            }
        }
    };
    let set_right = |right: Operand| {
        move |f: &mut VerifiableFunction| {
            if let Rvalue::BinaryOp(_, _, slot) = sole_rvalue(f) {
                *slot = right.clone();
            }
        }
    };
    let swap = |f: &mut VerifiableFunction| {
        if let Rvalue::BinaryOp(_, left, right) = sole_rvalue(f) {
            std::mem::swap(left, right);
        }
    };

    check("`|` emitted for a `^^^` declaration", "bxor", &set_op(BinOp::BitOr));
    check("`&` emitted for a `^^^` declaration", "bxor", &set_op(BinOp::BitAnd));
    check("`^` emitted for a `|||` declaration", "bor", &set_op(BinOp::BitXor));
    check("operands swapped on `^^^` (COMMUTATIVE)", "bxor", &swap);
    check(
        "mask `14` emitted for `a ^^^ 15`",
        "bxorlit",
        &set_right(Operand::Constant(ConstValue::Uint(14, 64))),
    );
    check("`<<` emitted for a `>>>` declaration", "shr3", &set_op(BinOp::Shl));
    check("`/` emitted for `>>`, same constant", "shr3", &set_op(BinOp::Div));
    check("`/ 8` emitted for `>> 3` (EQUIVALENT)", "shr3", &|f| {
        set_op(BinOp::Div)(f);
        set_right(Operand::Constant(ConstValue::Uint(8, 64)))(f);
    });
    check(
        "amount `4` emitted for `a >>> 3`",
        "shr3",
        &set_right(Operand::Constant(ConstValue::Uint(4, 64))),
    );
    check(
        "amount encoded at u32 in a u64 body",
        "shr3",
        &set_right(Operand::Constant(ConstValue::Uint(3, 32))),
    );
    check("a VARIABLE amount for `a >>> 3`", "shr3", &set_right(Operand::Copy(Place::local(2))));
    check("operands swapped on `>>`", "shr3", &swap);
    check("operands swapped on `15 ^^^ a` (COMMUTATIVE)", "bxorleft", &swap);

    assert_eq!(refused, 13, "every mutation in the table must have run");

    // Mutations 4 and 13, through the REAL gate rather than the structural
    // comparison that refused them: the frozen producer's reading of each
    // swapped body is put to `check_faithful` against the declaration, and
    // the refusal must be a COMPLETED `Disagreement` — definitional equality
    // failed and the structural-induction fallback returned without a proof —
    // never a resource rail, which would be no verdict at all. So a gate that
    // ran past the structural comparison would not have admitted the swap
    // either. (Xor's commutativity is a theorem, not a definitional equality,
    // at open operands; the `rfl` statement below is the kernel-level reason.)
    for (name, swapped, arity) in [("bxor", "p1 ^ p0", 2), ("bxorleft", "p0 ^ 15", 1)] {
        let side_b = mint_expr(&env, swapped, arity, bits)
            .unwrap_or_else(|e| panic!("the frozen producer must mint `{swapped}`: {e}"));
        match check_faithful(&env, name, &side_b, &carrier_of(bits)) {
            Err(GateRefusal::Disagreement { .. }) => {}
            Ok(faithful) => panic!(
                "the REAL gate ADMITS `{swapped}` against `{name}` by {:?}. A swapped xor is \
                 then admissible at the kernel, and mutations 4/13 in this table must say so.",
                faithful.method()
            ),
            Err(other) => panic!(
                "`{swapped}` against `{name}`: refused as {other:?}, not a completed \
                 `Disagreement` — the swap's verdict at the gate is UNMEASURED"
            ),
        }
        eprintln!("L7-P13 | REAL GATE vs swapped `{swapped:<7}` on `{name}` | Disagreement");
    }
    assert!(
        island_try(&["theorem t (a b : UInt64) : a ^^^ b = b ^^^ a := rfl"]).is_err(),
        "`a ^^^ b = b ^^^ a` is now `rfl` at open operands; the gate measurement above must \
         then have moved as well"
    );

    // THE FROZEN PRODUCER — the independent half of the shift-amount rule.
    for rendering in ["p0 >> p1", "p0 >> 64", "p0 >> 70"] {
        let arity = if rendering.contains("p1") { 2 } else { 1 };
        let refusal = mint_expr(&env, rendering, arity, bits).err().unwrap_or_else(|| {
            panic!(
                "the FROZEN producer minted `{rendering}`. A variable or out-of-range amount \
                 now has a side B — the `>>>` MISS entry in the ledger is then one planner \
                 change away; re-measure it."
            )
        });
        assert!(
            refusal.contains("shift"),
            "the producer's refusal must name the shift boundary: {refusal}"
        );
        eprintln!("L7-P13 | FROZEN PRODUCER refuses `{rendering:<8}` | {refusal}");
    }
    for rendering in ["p0 >> 3", "p0 >> 0", "p0 >> 63", "p0 ^ p1", "p0 ^ 15"] {
        let arity = if rendering.contains("p1") { 2 } else { 1 };
        assert!(
            mint_expr(&env, rendering, arity, bits).is_ok(),
            "`{rendering}` must mint — if it does not, the refusals above measured a ban on the \
             operator rather than on the amount"
        );
    }
}

/// **The shift-amount rule, from side A, on every form a user can write — and
/// the measurement that it is a CAPABILITY boundary, not a soundness one.**
///
/// Three halves:
///
/// 1. **The semantics agree at every amount.** Lean's `UInt{N}.shiftRight`
///    shifts by the amount modulo `N` — measured at ground values and, the
///    part that matters for the refusal's option, at an OPEN operand: `a >>>
///    70 = a >>> 6` is `rfl` at `UInt64` (and `a >>> 70 = a >>> 7` is not). MIR's
///    `BinOp::Shr` takes the amount as `RHS.rem_euclid(LHS::BITS)`
///    (`rustc_middle::mir::syntax`), the same reduction. So no amount is a
///    wrong binary; this is NOT the divisor rule's situation (`l7_p6`).
/// 2. **The planner refuses every amount without a side B**, naming it a
///    capability boundary (never a PANIC) with v7/D3 options — and for an
///    out-of-range literal, the option that preserves meaning: the reduced
///    amount `k % N`, which half 1 shows is the same function.
/// 3. **The control**: the reduced amount PLANS, so the option is a real fix.
#[test]
fn l7_p14_the_planner_refuses_every_shift_amount_without_a_side_b() {
    // ── 1. the amount is reduced modulo the width, at the kernel ───────────
    for (label, source, admitted) in [
        ("(256 : UInt64) >>> 72 = 1", "theorem t : (256 : UInt64) >>> 72 = 1 := rfl", true),
        ("(256 : UInt64) >>> 72 = 0", "theorem t : (256 : UInt64) >>> 72 = 0 := rfl", false),
        ("(128 : UInt8) >>> 9 = 64", "theorem t : (128 : UInt8) >>> 9 = 64 := rfl", true),
        ("a >>> 70 = a >>> 6", "theorem t (a : UInt64) : a >>> 70 = a >>> 6 := rfl", true),
        ("a >>> 70 = a >>> 7", "theorem t (a : UInt64) : a >>> 70 = a >>> 7 := rfl", false),
        ("a >>> 64 = a >>> 0", "theorem t (a : UInt64) : a >>> 64 = a >>> 0 := rfl", true),
        ("a >>> 9 = a >>> 1 at UInt8", "theorem t (a : UInt8) : a >>> 9 = a >>> 1 := rfl", true),
    ] {
        assert_eq!(
            island_try(&[source]).is_ok(),
            admitted,
            "`{label}` by `rfl`: expected {}. The shift-amount refusal's first option rests on \
             Lean reducing the amount modulo the width; if that moved, the option is wrong.",
            if admitted { "ACCEPTED" } else { "REJECTED" }
        );
    }

    // ── 2. the planner refuses, with the right reason and options ──────────
    let env = island(&[
        "def shrv (a : UInt64) (b : UInt64) : UInt64 := a >>> b",
        "def shr64 (a : UInt64) : UInt64 := a >>> 64",
        "def shr70 (a : UInt64) : UInt64 := a >>> 70",
        "def shr8u8 (a : UInt8) : UInt8 := a >>> 8",
        "def shr9u8 (a : UInt8) : UInt8 := a >>> 9",
        // the controls: the reduced amounts
        "def shr6 (a : UInt64) : UInt64 := a >>> 6",
        "def shr1u8 (a : UInt8) : UInt8 := a >>> 1",
    ]);
    for (name, reduced) in [
        ("shrv", None),
        ("shr64", Some("a >>> 0")),
        ("shr70", Some("a >>> 6")),
        ("shr8u8", Some("a >>> 0")),
        ("shr9u8", Some("a >>> 1")),
    ] {
        let refusal = plan_clean_origin_body(&env, name)
            .err()
            .unwrap_or_else(|| panic!("`{name}` must NOT plan — it has no side B"));
        let text = refusal_text(&refusal);
        assert!(
            text.contains("capability boundary") && !text.contains("PANIC"),
            "`{name}`'s refusal must name a CAPABILITY boundary and must not claim a panic — \
             MIR's `>>` does not panic here and the semantics agree: {text}"
        );
        assert!(text.contains("options:"), "v7/D3: `{name}` must carry options: {text}");
        match reduced {
            Some(fix) => assert!(
                text.contains(&format!("`{fix}`")),
                "`{name}` must be offered the reduced amount `{fix}`: {text}"
            ),
            None => assert!(
                !text.contains("reduced amount"),
                "a VARIABLE amount has no reduced literal to offer: {text}"
            ),
        }
        eprintln!("L7-P14 | {name:<6} | REFUSED, with options");
    }

    // ── 3. the control ─────────────────────────────────────────────────────
    for name in ["shr6", "shr1u8"] {
        assert!(
            plan_clean_origin_body(&env, name).is_ok(),
            "`{name}` is the REDUCED amount the refusal offers and MUST plan; otherwise the \
             option is not a fix"
        );
    }
}

/// **The two rows reach landing 8's `==` DECISION OPERAND with no edit there,
/// and that is measured rather than inherited.**
///
/// The decision-operand vocabulary is `raw_binop_rows`, so adding a row widens
/// it. Both new operators are taken END TO END in that position at every width
/// — plan, the emitted two-step diamond with ONE computed prefix statement,
/// `recognize_select_beq_general`, and the gate — including `(15 ^^^ a) == 0`,
/// the numeral on the xor's LEFT — and the shift-amount rule is shown to hold
/// there too.
///
/// The `==` boundary's REFUSAL TEXT is measured as well: it names the
/// decision-operand vocabulary, and that list is now DERIVED from
/// `raw_binop_rows` rather than written out, because the hand-written one went
/// stale the day these two rows landed (it still said `&&&`, `|||`, `/`, `%`).
/// The expected list is spelled out HERE ([`RAW_BINOP_TOKENS`]), independently,
/// and each of the two LISTS in the text (diagnosis, first option) is parsed
/// and compared with it exactly, so the derivation is checked rather than
/// restated.
#[test]
fn l7_p15_the_new_operators_reach_the_eq_decision_operand() {
    for bits in WIDTHS {
        let carrier = format!("UInt{bits}");
        let env = island(&[
            &format!(
                "def xq (a : {carrier}) (b : {carrier}) : {carrier} := \
                 if (a ^^^ b) == 0 then a else b"
            ),
            &format!(
                "def sq (a : {carrier}) (b : {carrier}) : {carrier} := \
                 if (a >>> 3) == 0 then a else b"
            ),
            &format!(
                "def sqv (a : {carrier}) (b : {carrier}) : {carrier} := \
                 if (a >>> b) == 0 then a else b"
            ),
            &format!(
                "def xql (a : {carrier}) (b : {carrier}) : {carrier} := \
                 if (15 ^^^ a) == 0 then a else b"
            ),
            &format!(
                "def wrapq (a : {carrier}) (b : {carrier}) : {carrier} := \
                 if (a + 1) == 0 then a else b"
            ),
        ]);
        for (name, node) in [
            (
                "xq",
                BeqOperand::RawBin {
                    op: RawBinOpKind::BitXor,
                    left: ArithOperand::Param(0),
                    right: ArithOperand::Param(1),
                },
            ),
            (
                "sq",
                BeqOperand::RawBin {
                    op: RawBinOpKind::Shr,
                    left: ArithOperand::Param(0),
                    right: ArithOperand::Const(3),
                },
            ),
            (
                "xql",
                BeqOperand::RawBin {
                    op: RawBinOpKind::BitXor,
                    left: ArithOperand::Const(15),
                    right: ArithOperand::Param(0),
                },
            ),
        ] {
            let (plan, emitted) = plan_and_emit(&env, name, bits);
            assert_eq!(
                plan.shape(),
                &CleanOriginShape::SelectBeqGeneral {
                    scrutinee: true,
                    cmp_left: node,
                    cmp_right: BeqOperand::Const(0),
                    then_arm: ArithOperand::Param(0),
                    else_arm: ArithOperand::Param(1),
                },
                "u{bits} `{name}`: the planned shape"
            );
            assert_eq!(ladder_row(plan.shape()).expect("row").name, "select.beq");
            let read = recognize_select_beq_general(&emitted)
                .unwrap_or_else(|| panic!("u{bits} `{name}`: side B must read the emitted body"));
            assert_eq!(read.cmp_left, node, "u{bits} `{name}`: side B's computed operand");
            admit_lowering(&env, &plan, &emitted).unwrap_or_else(|refusal| {
                panic!("u{bits} `{name}` must admit end to end: {refusal:?}")
            });
        }
        let refusal = plan_clean_origin_body(&env, "sqv").err().unwrap_or_else(|| {
            panic!("u{bits} `sqv`: a variable amount in an operand must not plan")
        });
        assert!(
            refusal_text(&refusal).contains("capability boundary"),
            "u{bits} `sqv`: the shift-amount rule must hold in the operand position too"
        );

        // The `==` boundary names the WHOLE operand vocabulary, both in its
        // diagnosis and in its first option, and each operand rule with it.
        // Each LIST is read as a list and compared with the independent one:
        // counting mentions anywhere in the text (what this used to do) is
        // satisfied by the two rule parentheticals alone for `/`, `%` and
        // `>>>`, so it passed with all three dropped from both lists.
        let boundary = refusal_text(
            &plan_clean_origin_body(&env, "wrapq").expect_err("a wrapping operand is refused"),
        );
        assert_lists_exactly_the_raw_binop_family(
            &boundary,
            "ONE raw binary operator (",
            ") over two such leaves",
            &format!("u{bits} `==` boundary, diagnosis"),
        );
        assert_lists_exactly_the_raw_binop_family(
            &boundary,
            "single one of ",
            " over two of those",
            &format!("u{bits} `==` boundary, first option"),
        );
        assert_states_the_raw_binop_rules(&boundary, 2, &format!("u{bits} `==` boundary"));
        eprintln!(
            "L7-P15 | u{bits:<2} | `(a ^^^ b) == 0`, `(a >>> 3) == 0`, `(15 ^^^ a) == 0` ADMIT | \
             `(a >>> b) == 0` refused | boundary names all six operators"
        );
    }
}

// ═══ L7-P16 — THE GENERIC REFUSAL NAMES THE WHOLE RAW-BINOP FAMILY ═══

/// **The generic `NotEmittable` texts list every raw-binop row.**
///
/// Two texts describe the whole callable fragment to a user whose body fell
/// outside it: the fall-through sentence in `recognise_clean_shape` ("it is
/// neither a bare parameter projection, nor …") and `EmitRefusal::note`'s
/// "The callable fragment currently includes: …" paragraph, which EVERY
/// `NotEmittable` note carries. Through landing 7 and the two rows after it,
/// both omitted the raw-binop family entirely — so a user whose nested
/// `(a &&& b) ||| a` was refused was told the fragment had no `&&&` at all.
/// Both now read the family from `raw_binop_rows`; this probe compares each
/// list with [`RAW_BINOP_TOKENS`], written independently, and each rule with
/// [`RAW_BINOP_RULES`].
///
/// Two bodies reach the generic site at every width: `mix`, a NESTED
/// raw-binop tree (`l7_p9`'s kernel-green MISS — the case where naming the
/// family matters most), and `rt`, the bare `ofNat`/`toNat` round trip
/// (`landing8_selection_probes`' generic-site witness). Both heads ARE
/// selected at the carrier (`uint.or`, `uint.lit`), so both refusals cite the
/// selecting row rather than a missing one (`l7_p17` measures the rule).
#[test]
fn l7_p16_the_generic_refusal_names_every_raw_binop_row() {
    for bits in WIDTHS {
        let carrier = format!("UInt{bits}");
        let env = island(&[
            &format!("def mix (a : {carrier}) (b : {carrier}) : {carrier} := (a &&& b) ||| a"),
            &format!("def rt (n : {carrier}) : {carrier} := {carrier}.ofNat ({carrier}.toNat n)"),
        ]);
        for (name, head, row) in [
            ("mix", "HOr.hOr".to_owned(), "uint.or"),
            ("rt", format!("{carrier}.ofNat"), "uint.lit"),
        ] {
            let refusal = plan_clean_origin_body(&env, name)
                .err()
                .unwrap_or_else(|| panic!("u{bits} `{name}` must not plan"));
            let reason = refusal_text(&refusal);
            let cited = format!(
                "`{head}` at {} IS selected — by row `{row}`",
                CarrierClass::MachineUInt.label()
            );
            assert!(
                reason.contains("outside the emittable fragment")
                    && reason.contains(&cited)
                    && !reason.contains("no selection row for"),
                "u{bits} `{name}` must reach the GENERIC fall-through, the site under test, and \
                 cite `{row}` as selecting `{head}`:\n{reason}"
            );
            let what = format!("u{bits} `{name}` generic fall-through");
            assert_lists_exactly_the_raw_binop_family(
                &reason,
                "nor ONE raw binary operator — one of ",
                " — with no nested operand",
                &what,
            );
            assert_states_the_raw_binop_rules(&reason, 1, &what);

            // The note embeds the reason, so it carries TWO lists: the
            // fall-through's, and the callable-fragment paragraph's own.
            let note = refusal.note();
            assert_lists_exactly_the_raw_binop_family(
                &note,
                "ONE RAW BINARY OPERATOR — one of ",
                " — over two parameters",
                &format!("u{bits} `{name}` note, callable-fragment paragraph"),
            );
            assert_states_the_raw_binop_rules(&note, 2, &format!("u{bits} `{name}` note"));
        }
        eprintln!(
            "L7-P16 | u{bits:<2} | `mix`, `rt`: the fall-through AND the note list exactly the \
             six raw-binop operators with both rules"
        );
    }
}

// ═══ L7-P17 — THE GENERIC REFUSAL IS TRUE OF THE TABLE ═══

/// **"No selection row" is said only when no row selects the head.**
///
/// Until 2026-09-23 the generic fall-through cited `no_selection_row` for
/// every body that reached it, so `mix` — whose head `HOr.hOr` the `uint.or`
/// row selects at every machine width — was told "none of them selects this
/// head at this carrier" in a text whose own row list named `uint.or`. The site
/// now asks `rows_selecting_head` (via `whole_body_refusal`) and says one of
/// three things; this probe measures each on REAL elaborated bodies.
///
/// 1. **A whole-body row selects the head** → the head is cited as SELECTED,
///    by name, and the options fit a shape: every nested raw-binop root at
///    every width, a wrapping head over a raw operand (in both the surface and
///    the carrier-method spelling), a select with a computed arm, a conversion
///    through `{C}.ofNat`, a boolean composition past the operator bound, and a
///    `Bool` comparison outside the two-parameter shape — asked at the width it
///    COMPARES, where the `comparison.*` rows are stated.
/// 2. **Only a recursion-arm row selects it** → whole-body `Nat` `+`/`-`/`*`,
///    a `Nat` numeral behind a binder, and a whole-body `Nat.succ` (read by
///    the structural arm as the parameter, by the well-founded arm as a
///    numeral tower): no whole-body row, and the text names the arm rows and
///    where they apply.
/// 3. **No row selects it** → `Nat` division (the head `uint.div` selects at a
///    machine width, asked at the bignum carrier), a `match` on `Bool`, and
///    `<<<` (whose head is not even a constant) keep `no_selection_row`
///    BYTE-IDENTICAL.
///
/// **Each row is asked at the position IT is stated over** (`CarrierAnchor`),
/// which an adversarial review measured the first version of this probe did
/// not do: it read every `Bool`-valued body at its ARGUMENTS' width, so `if a <
/// b then true else false : Bool` was told `select.*` realizes `ite` there (no
/// select row realizes a `Bool`-valued `ite`: they are stated over a
/// machine-width RESULT); `!(a < b)`, `a != b`, `a < b && b < 10`, `a < b || b <
/// 10` were told `bool.*` selects their head "at an unsigned machine width"
/// (those rows are stated over `Bool` operands); `if h : a < b …` moved its
/// no-row label off the result; and an unused `Bool`/`UInt32` parameter flipped
/// `a < 10`'s answer. All of those are pinned below, and every true row miss
/// among them is pinned to end with `no_selection_row` at the RESULT's class —
/// the text this site produced before any row was consulted, byte for byte.
///
/// Plus the first option case 1 offers, measured rather than advised: `a &&& b`
/// alone PLANS (`uint.and`), while splitting it out through a Lean `def` or a
/// `let` arrives back at `mix`'s refusal byte-for-byte — named calls are
/// expanded and a pure `let` is zeta-reduced before selection — which is why
/// the option says to compose the pieces in the RUST caller.
#[test]
fn l7_p17_the_generic_refusal_is_true_of_the_table() {
    let machine = CarrierClass::MachineUInt.label();
    let reason_of = |env: &Environment, name: &str| {
        refusal_text(
            &plan_clean_origin_body(env, name)
                .err()
                .unwrap_or_else(|| panic!("`{name}` must not plan")),
        )
    };

    for bits in WIDTHS {
        let c = format!("UInt{bits}");
        let env = island(&[
            &format!("def mix (a : {c}) (b : {c}) : {c} := (a &&& b) ||| a"),
            &format!("def mixarith (a : {c}) (b : {c}) : {c} := (a + b) &&& a"),
            &format!("def divmix (a : {c}) (b : {c}) : {c} := (a &&& b) / 3"),
            &format!("def modmix (a : {c}) (b : {c}) : {c} := (a ||| b) % 7"),
            &format!("def xormix (a : {c}) (b : {c}) : {c} := (a ^^^ b) ^^^ a"),
            &format!("def shrmix (a : {c}) (b : {c}) : {c} := (a &&& b) >>> 3"),
            &format!("def andplus (a : {c}) (b : {c}) : {c} := (a &&& b) + a"),
            &format!("def cmeth (a : {c}) (b : {c}) : {c} := {c}.add (a &&& b) a"),
            &format!("def itecomp (a : {c}) (b : {c}) : {c} := if a < b then a + 1 else b"),
            &format!("def conv (n : Nat) : {c} := {c}.ofNat n"),
            &format!("def dlit (a : {c}) (b : {c}) : Bool := a < 10"),
            &format!("def beqlit (a : {c}) (b : {c}) : Bool := a == 10"),
            &format!("def sl (a : {c}) (b : {c}) : {c} := a <<< b"),
            // the split option's three routes
            &format!("def andab (a : {c}) (b : {c}) : {c} := a &&& b"),
            &format!("def mixh (a : {c}) (b : {c}) : {c} := andab a b ||| a"),
            &format!("def mixl (a : {c}) (b : {c}) : {c} := let y := a &&& b; y ||| a"),
        ]);

        // ── case 1: a whole-body row selects the head ──────────────────────
        let comparisons = "rows `comparison.lt`, `comparison.le`, `comparison.eq`";
        for (name, head, rows) in [
            ("mix", "HOr.hOr".to_owned(), "row `uint.or`"),
            ("mixarith", "HAnd.hAnd".to_owned(), "row `uint.and`"),
            ("divmix", "HDiv.hDiv".to_owned(), "row `uint.div`"),
            ("modmix", "HMod.hMod".to_owned(), "row `uint.mod`"),
            ("xormix", "HXor.hXor".to_owned(), "row `uint.xor`"),
            ("shrmix", "HShiftRight.hShiftRight".to_owned(), "row `uint.shr`"),
            ("andplus", "HAdd.hAdd".to_owned(), "row `uint.add`"),
            ("cmeth", format!("{c}.add"), "row `uint.add`"),
            (
                "itecomp",
                "ite".to_owned(),
                "rows `select.lt`, `select.le`, `select.eq`, `select.beq`",
            ),
            ("conv", format!("{c}.ofNat"), "row `uint.lit`"),
            ("dlit", "decide".to_owned(), comparisons),
            ("beqlit", "BEq.beq".to_owned(), "row `comparison.eq`"),
        ] {
            let reason = reason_of(&env, name);
            let cited = format!("`{head}` at {machine} IS selected — by {rows} —");
            assert!(
                reason.contains(&cited) && !reason.contains("no selection row for"),
                "u{bits} `{name}`: `{head}` is selected by {rows}, so the refusal must cite \
                 them as selecting it and must not claim a missing row:\n{reason}"
            );
            for option in [
                "options:",
                "compose them in the Rust caller",
                "Not through another Lean `def` or a `let`",
                "proof position",
                "`ensures` clause",
            ] {
                assert!(
                    reason.contains(option),
                    "u{bits} `{name}`: v7/D3 — the shape refusal must carry {option:?}:\n{reason}"
                );
            }
        }

        // ── the split option, measured ─────────────────────────────────────
        let inner = plan_clean_origin_body(&env, "andab")
            .unwrap_or_else(|refusal| panic!("u{bits} `a &&& b` alone must plan: {refusal:?}"));
        assert_eq!(ladder_row(inner.shape()).expect("row").name, "uint.and", "u{bits} `andab`");
        let mix = reason_of(&env, "mix");
        for split in ["mixh", "mixl"] {
            assert_eq!(
                reason_of(&env, split),
                mix,
                "u{bits} `{split}`: splitting INSIDE Lean must arrive back at `mix`'s refusal — \
                 which is what the option's \"not through another Lean `def` or a `let`\" claims"
            );
        }

        // ── case 3 at a machine width: `<<<` has no row and no constant head ──
        let shift = reason_of(&env, "sl");
        let row_miss =
            no_selection_row("a projection out of a structure", CarrierClass::MachineUInt);
        assert!(
            shift.ends_with(&format!("\n{row_miss}")),
            "u{bits} `a <<< b`: no row selects it, so the v7/D3 row-miss text must be kept \
             byte-identical:\n{shift}"
        );
        eprintln!(
            "L7-P17 | u{bits:<2} | 12 served heads cited as SELECTED; `andab` plans, `mixh`/`mixl` \
             == `mix`; `<<<` keeps the row-miss text"
        );
    }

    // ── widthless bodies: a nested boolean, and the `Nat` cases 2 and 3 ────
    //
    // `bo` was the case-1 nested-boolean refusal until the composed-Boolean
    // landing (`d5e4dad273`, 2026-11-06: `CleanOriginShape::BoolExpression`,
    // at most `BOOL_EXPRESSION_MAX_OPS` connectives, checked by the
    // independent E6 reader); it now PLANS under `bool.and`, which is the row
    // its refusal used to cite. The case-1 text is still asked of a nested
    // `&&` the recognizer declines: the same composition one connective past
    // the bound, whose head `and` the `bool.and` row still selects.
    // `boBound` is the same nest at exactly the bound: it must still plan, so
    // `boOver`'s refusal is the bound's and not some other decline.
    let nested = |connectives: usize| {
        (2..connectives).fold("(a || b) && c".to_owned(), |inner, _| format!("a && ({inner})"))
    };
    let at_bound = format!(
        "def boBound (a : Bool) (b : Bool) (c : Bool) : Bool := {}",
        nested(BOOL_EXPRESSION_MAX_OPS)
    );
    let over_bound = format!(
        "def boOver (a : Bool) (b : Bool) (c : Bool) : Bool := {}",
        nested(BOOL_EXPRESSION_MAX_OPS + 1)
    );
    let env = island(&[
        "def bo (a : Bool) (b : Bool) (c : Bool) : Bool := (a || b) && c",
        &at_bound,
        &over_bound,
        "def natAdd (a : Nat) (b : Nat) : Nat := a + b",
        "def natSub (a : Nat) (b : Nat) : Nat := a - b",
        "def natMul (a : Nat) (b : Nat) : Nat := a * b",
        "def natFive (a : Nat) : Nat := 5",
        "def natDiv (a : Nat) (b : Nat) : Nat := a / b",
        "def boolMatch (b : Bool) : Nat := match b with | true => 1 | false => 0",
    ]);
    let bo = plan_clean_origin_body(&env, "bo")
        .unwrap_or_else(|refusal| panic!("`bo` must plan as a composed Boolean: {refusal:?}"));
    assert!(
        matches!(bo.shape(), CleanOriginShape::BoolExpression { .. }),
        "`bo` must plan as a composed Boolean expression: {:?}",
        bo.shape()
    );
    assert_eq!(
        ladder_row(bo.shape()).expect("a composed Boolean plan selects a row").name,
        "bool.and",
        "`(a || b) && c` is realized by the row its refusal used to cite"
    );
    let bo_bound = plan_clean_origin_body(&env, "boBound")
        .unwrap_or_else(|refusal| panic!("`boBound` is at the operator bound: {refusal:?}"));
    assert!(
        matches!(bo_bound.shape(), CleanOriginShape::BoolExpression { .. }),
        "`boBound` must plan as a composed Boolean expression: {:?}",
        bo_bound.shape()
    );
    let bo_over = reason_of(&env, "boOver");
    assert!(
        bo_over.contains(&format!(
            "`and` at {} IS selected — by row `bool.and` —",
            CarrierClass::AnyExact.label()
        )) && !bo_over.contains("no selection row for"),
        "a nested `&&` over `||` past the operator bound: `bool.and` selects `and`:\n{bo_over}"
    );

    let nat = CarrierClass::BignumNat.label();
    for (name, head, row) in [
        ("natAdd", "HAdd.hAdd", "nat.add"),
        ("natSub", "HSub.hSub", "nat.sub"),
        ("natMul", "HMul.hMul", "nat.mul"),
        ("natFive", "OfNat.ofNat", "nat.lit"),
    ] {
        let reason = reason_of(&env, name);
        let cited = format!(
            "no selection row for `{head}` as a WHOLE body at {nat} — row `{row}` selects this \
             head at this carrier, but only as a node inside the arm of a recursion scheme \
             (rows `nat.rec.structural`, `nat.wf.fix`)"
        );
        assert!(
            reason.contains(&cited)
                && !reason.ends_with(&no_selection_row(head, CarrierClass::BignumNat)),
            "`{name}`: only the recursion-arm row `{row}` selects `{head}` at the bignum \
             carrier, and the refusal must say so rather than deny it:\n{reason}"
        );
    }

    for (name, head) in [("natDiv", "HDiv.hDiv"), ("boolMatch", "Bool.casesOn")] {
        let reason = reason_of(&env, name);
        assert!(
            reason.ends_with(&format!("\n{}", no_selection_row(head, CarrierClass::BignumNat))),
            "`{name}`: no row selects `{head}` at the bignum carrier, so the v7/D3 row-miss \
             text must be kept byte-identical:\n{reason}"
        );
    }
    eprintln!(
        "L7-P17 | Nat/Bool | `bo` plans under `bool.and`, `boOver` cites it; `+`/`-`/`*`/numeral \
         cite their arm rows; `/` and `match` keep the row-miss text"
    );

    // ── the SIGNATURE, not the shape, is the only obstacle ─────────────────
    // Each body applies its head in exactly a shape a row realizes; what declines
    // it is a parameter the body does not read, or one at another type. The
    // case-1 text must name that possibility (it used to say the SHAPE only).
    let env = island(&[
        "def u3 (a b x : UInt64) : Bool := a < b",
        "def pcb (a b : UInt64) (x : Bool) : Bool := a < b",
        "def bn2 (a : Bool) (x : UInt64) : Bool := !a",
    ]);
    for name in ["u3", "pcb", "bn2"] {
        let reason = reason_of(&env, name);
        assert!(
            reason.contains("IS selected")
                && reason.contains("or the body's SIGNATURE")
                && reason.contains("a parameter the body does not read, or one at another type"),
            "`{name}`: the head is applied in a shape a row realizes, so the refusal must name \
             the signature as a possible obstacle, not only the shape:\n{reason}"
        );
    }

    // ── `Nat.succ`: case 2, consistent with the two arm readers ────────────
    let env = island(&[
        "def succ1 (n : Nat) : Nat := Nat.succ n",
        "def succ2 (n : Nat) : Nat := n.succ.succ",
        "def succ5 (n : Nat) : Nat := Nat.succ 5",
    ]);
    for name in ["succ1", "succ2", "succ5"] {
        let reason = reason_of(&env, name);
        let cited = format!(
            "no selection row for `Nat.succ` as a WHOLE body at {nat} — rows `nat.param`, \
             `nat.lit` select this head at this carrier, but only as a node inside the arm of a \
             recursion scheme (rows `nat.rec.structural`, `nat.wf.fix`), each within the arm \
             reader of its own scheme, and this body applies it at the top level, where no row \
             does."
        );
        assert!(
            reason.contains(&cited),
            "`{name}`: the structural arm reads `Nat.succ k` as the parameter (`nat.param`) and \
             the well-founded arm reads a `Nat.succ` tower as a numeral (`nat.lit`), so a \
             whole-body `Nat.succ` is an arm-only head, not a row miss:\n{reason}"
        );
    }
    eprintln!(
        "L7-P17 | Nat.succ | `Nat.succ n`, `n.succ.succ`, `Nat.succ 5` cite nat.param + nat.lit"
    );

    // ── each row at ITS OWN position: the four measured refutations ────────
    //
    // The pre-2026-09-23 site named every row miss at the RESULT's class. The
    // expected class is restated HERE from the declared result type, not read
    // from the crate, so a change to the carrier the no-row text is named at
    // fails this probe.
    let result_class = |result: &str| match result {
        "UInt8" | "UInt16" | "UInt32" | "UInt64" => CarrierClass::MachineUInt,
        "Nat" => CarrierClass::BignumNat,
        _ => CarrierClass::AnyExact,
    };
    let exact = CarrierClass::AnyExact.label();
    let comparisons = "rows `comparison.lt`, `comparison.le`, `comparison.eq`";
    for bits in WIDTHS {
        let c = format!("UInt{bits}");
        let env = island(&[
            // (1) a `Bool`-valued `ite`, and the `match` that elaborates to one
            &format!("def n6 (a : {c}) (b : {c}) : Bool := if a < b then true else false"),
            &format!("def bm (a : {c}) : Bool := match a with | 0 => true | _ => false"),
            // (3) the dependent `if`
            &format!("def q1 (a : {c}) (b : {c}) : Bool := if h : a < b then true else false"),
            // …and comparisons with no compared position at a machine width
            &format!("def dne (a : {c}) (b : {c}) : Bool := decide (a ≠ b)"),
            "def nlt5 (n : Nat) : Bool := n < 5",
            "def bbeq (a : Bool) (b : Bool) : Bool := a == b",
            // (2) the `bool.*` heads over machine-width arguments
            &format!("def ne (a : {c}) (b : {c}) : Bool := a != b"),
            &format!("def nlt (a : {c}) (b : {c}) : Bool := !(a < b)"),
            &format!("def andc (a : {c}) (b : {c}) : Bool := a < b && b < 10"),
            &format!("def orc (a : {c}) (b : {c}) : Bool := a < b || b < 10"),
            // (4) `a < 10` whatever the other parameters are, and the converses
            &format!("def m1 (a : {c}) : Bool := a < 10"),
            &format!("def m2 (a : {c}) (b : Bool) : Bool := a < 10"),
            &format!("def m3 (a : {c}) (b : UInt32) : Bool := a < 10"),
            &format!("def m4 (a : {c}) (b : Nat) : Bool := a < 10"),
            &format!("def mgt (a : {c}) (b : {c}) : Bool := a > b"),
            &format!("def mge (a : {c}) (b : {c}) : Bool := a >= b"),
        ]);

        // TRUE row misses: byte-identical to the pre-2026-09-23 text, label
        // included — and never a claim that a row selects the head.
        for (name, head, result) in [
            ("n6", "ite", "Bool"),
            ("bm", "ite", "Bool"),
            ("q1", "Decidable.casesOn", "Bool"),
            ("dne", "decide", "Bool"),
            ("nlt5", "decide", "Bool"),
            ("bbeq", "BEq.beq", "Bool"),
        ] {
            let reason = reason_of(&env, name);
            let row_miss = no_selection_row(head, result_class(result));
            assert!(
                reason.ends_with(&format!("\n{row_miss}")) && !reason.contains("IS selected"),
                "u{bits} `{name}`: no row selects `{head}` at the position it is stated over, so \
                 the row-miss text must be the pre-2026-09-23 one, named at the RESULT's class \
                 ({}):\n{reason}",
                result_class(result).label()
            );
        }

        // The `bool.*` rows, cited at their `Bool` operands' class.
        for (name, head, row) in [
            ("ne", "Bool.not", "bool.not"),
            ("nlt", "Bool.not", "bool.not"),
            ("andc", "and", "bool.and"),
            ("orc", "or", "bool.or"),
        ] {
            let reason = reason_of(&env, name);
            let cited = format!("`{head}` at {exact} IS selected — by row `{row}` —");
            assert!(
                reason.contains(&cited)
                    && !reason.contains(&format!("`{head}` at {machine}"))
                    && !reason.contains("no selection row for"),
                "u{bits} `{name}`: `{row}` is stated over `Bool` operands, so it is cited at \
                 {exact}, never at a machine width:\n{reason}"
            );
        }

        // The `comparison.*` rows, cited at the COMPARED width — whatever an
        // unused parameter's type, and for the converse spellings too.
        let mut compared = Vec::new();
        for name in ["m1", "m2", "m3", "m4", "mgt", "mge"] {
            let reason = reason_of(&env, name);
            let cited = format!("`decide` at {machine} IS selected — by {comparisons} —");
            assert!(
                reason.contains(&cited) && !reason.contains("no selection row for"),
                "u{bits} `{name}`: the comparison is stated at `{c}`, where the \
                 `comparison.*` rows select `decide`:\n{reason}"
            );
            compared.push(reason);
        }
        assert!(
            compared[1..4].iter().all(|reason| *reason == compared[0]),
            "u{bits}: `a < 10` must be refused byte-identically whatever the unused parameter's \
             type (none, `Bool`, `UInt32`, `Nat`)"
        );
        eprintln!(
            "L7-P17 | u{bits:<2} | Bool `ite`/`match`/`if h`/`≠`/Nat-cmp/Bool-`==` keep the \
             result-class row miss; `!=`/`!`/`&&`/`||` cite bool.* at {exact}; `a < 10` beside \
             any parameter and `>`/`>=` cite comparison.* at {machine}"
        );
    }
}

// ═══════════════ the table's own integrity, for this family ═══════════════

/// The six rows are exactly the six operators, each with ONE side-A selector
/// and a realization no other row has. (Four at landing 7; `uint.xor` and
/// `uint.shr` joined on 2026-09-23, and `uint.shl` is absent BY MEASUREMENT —
/// `l7_p7`.)
///
/// Stated here rather than only in `table_controls` because the coordinates
/// that matter for THIS family are the ones a generic control cannot know: one
/// selector each (the carrier spelling is deliberately absent — `l7_p1`), and
/// four distinct `MirShape::RawBinOp` values so H-C never applies.
#[test]
fn l7_the_row_family_is_six_rows_with_one_selector_each() {
    let rows: Vec<&'static str> = ROWS
        .iter()
        .filter(|row| matches!(row.mir, MirShape::RawBinOp(_)))
        .map(|row| row.name)
        .collect();
    assert_eq!(rows, vec!["uint.and", "uint.or", "uint.div", "uint.mod", "uint.xor", "uint.shr"]);

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
        distinct, 6,
        "the six rows must realize six DISTINCT MIR values; if two collapsed, H-C would \
         apply and neither escape is available (same layer, same carrier, same gate)"
    );
}

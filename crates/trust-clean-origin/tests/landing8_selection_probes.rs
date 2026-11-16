// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **§6f LANDING 8 — the COMPUTED `==` operand and the `(a == b) = false`
//! polarity, and the three shapes that stay refused for a REALIZATION reason.**
//!
//! | question | measured verdict |
//! |---|---|
//! | does a computed `==` operand have an elaborator NORMAL FORM? | **no** — `l8_p1`; the operand is VERBATIM in the proposition and in `instDecidableEqBool`, at four widths and four operators, in both decision positions |
//! | what does `(a == b) = false` elaborate to? | the `==` tree with the scrutinee `false` — a BARE depth-1 constant, not `Bool.false` (`l8_p2`) |
//! | are the disequality-adjacent trees interchangeable? | **no** — `l8_p2`: `= false` is not defeq to `==`, not to `==` with SWAPPED ARMS, not to `!=`, not to `≠` |
//! | do computed operands admit end to end? | **yes** — `l8_p3`, four widths, four operators, both positions, both polarities |
//! | does `= false` admit end to end? | **yes** — `l8_p4`, four widths |
//! | did the E6 import direction's reach move? | **no** — `l8_p5`; four readers decline the new bodies |
//! | what is still refused, and why? | `l8_p6` — a NESTED operand, a WRAPPING operand and a computed ARM: all three kernel-GREEN, all three blocked on the emitted realization |
//! | is the divisor rule enforced inside an operand? | **yes, three times** — `l8_p7` |
//! | are the refusal texts TRUE of the program? | `l8_p8` — the two `probe_p9`-class defects landing 6 left behind are deleted, and the deletion is pinned |
//!
//! # THE CORRECTION THIS LANDING RESTS ON
//!
//! Landing 6's `==` refusal said a COMPUTED operand *"resolves its decidability
//! through an elaborator normal form no producer reproduces"*. That is TRUE of
//! `<` and `<=` — `if a + 1 < b` really does resolve through an
//! `instDecidableNatLt` over a `Nat.rec`-headed normal form of the modular
//! reduction, and `l8_p6` re-measures it — and it is **FALSE of `==`**, which
//! is the tree that refusal is reached on. `l8_p1` is the measurement: the
//! `==` decision is resolved at `Bool` by the uniform `instDecidableEqBool`,
//! one layer ABOVE the carrier, where the computed operand is already a
//! `UInt{N}` and nothing has to be normalized at all.
//!
//! # SIDE A IS THE REAL ELABORATOR, AND THE EMITTED BODY IS THE REAL TEMPLATE
//!
//! Every side A here comes from `trust_certify::clean_island::
//! CleanIslandSession::check_all` — the pipeline `clean_origin_mir` drives —
//! and every emitted body is rendered from
//! `trust_clean_origin::materialize::body_template` applied to the row
//! `table::ladder_row` selects. Only MUTANTS are hand-built, and they live in
//! `control_15`.

#![allow(clippy::doc_markdown)]

use clean_kernel::{Environment, Expr, ExprKind, Name};
use trust_clean_origin::materialize::{
    BodyTemplate, TemplateCallee, TemplateOperand, TemplateRvalue, TemplateTerminator, TemplateTy,
    TemplateUnwind, body_template,
};
use trust_clean_origin::table::{MirShape, ladder_row};
use trust_clean_origin::{
    CleanOriginPlan, CleanOriginShape, EmitRefusal, admit_lowering, plan_clean_origin_body,
};
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

fn island(sources: &[&str]) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(sources);
    assert!(!batch.is_rejected(), "the island must kernel-check: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

/// The same, WITHOUT the assertion — for the probes whose subject is a
/// REJECTION.
fn island_try(sources: &[&str]) -> Result<Environment, String> {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(sources);
    if batch.is_rejected() {
        return Err(format!("{batch:?}"));
    }
    Ok(session.environment().expect("an untainted session has an environment").clone())
}

const WIDTHS: [u32; 4] = [8, 16, 32, 64];

/// Landing 8's four raw operators, with the source token and the surface class.
/// A probe cannot silently measure three of the four. (`^^^` and `>>>` joined the
/// raw family later, on 2026-09-23; their `==`-operand position is measured in
/// `landing7_selection_probes::l7_p15`, since `>>>` needs a numeral amount.)
const OPERATORS: [(RawBinOpKind, &str, &str, &str); 4] = [
    (RawBinOpKind::BitAnd, "&&&", "HAnd", "hAnd"),
    (RawBinOpKind::BitOr, "|||", "HOr", "hOr"),
    (RawBinOpKind::Div, "/", "HDiv", "hDiv"),
    (RawBinOpKind::Rem, "%", "HMod", "hMod"),
];

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

fn refusal_text(refusal: &EmitRefusal) -> String {
    match refusal {
        EmitRefusal::NotEmittable { reason, .. } => reason.clone(),
        other => panic!("expected `NotEmittable`, got {other:?}"),
    }
}

// ──────────── the EMITTED body, rendered from the REAL template ────────────

/// `control_11`'s renderer, restated for the shapes this landing measures. The
/// same caveat applies: it establishes that the DESCRIPTION admits, not that
/// the x.py-only translation into `mir::Body` is faithful.
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

/// Plan a declaration, select its row, build the REAL template and render it.
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

// ═══ L8-P1 — THE COMPUTED `==` OPERAND HAS NO NORMAL FORM, AT EVERY WIDTH ═══

/// **The measurement that deleted landing 6's refusal text.**
///
/// For every unsigned machine width and every one of landing 8's four raw operators,
/// in BOTH decision positions:
///
/// * the elaborated condition is the landing-6 `ite` tree, unchanged;
/// * the computed operand is the SURFACE spelling `H{Class}.h{proj}` at the
///   prelude instance — the same one `l7_p1` pinned for a whole body;
/// * it appears VERBATIM in the proposition and again inside
///   `instDecidableEqBool`, which is the uniform `Bool`-level instance;
/// * and **`Nat.rec` appears nowhere in the term**, which is the negative half
///   and the whole point: a computed operand under `==` is decided one layer
///   ABOVE the carrier, where nothing has to be normalized.
#[test]
fn l8_p1_a_computed_equality_operand_carries_no_normal_form_at_any_width() {
    for bits in WIDTHS {
        let carrier = format!("UInt{bits}");
        // Divisor `3` so the same source is legal for `/` and `%` too, and in
        // range at UInt8.
        let sources: Vec<String> = OPERATORS
            .iter()
            .flat_map(|(_, token, class, _)| {
                [
                    format!(
                        "def l{class} (a : {carrier}) (b : {carrier}) : {carrier} := \
                         if (a {token} 3) == 0 then a else b"
                    ),
                    format!(
                        "def r{class} (a : {carrier}) (b : {carrier}) : {carrier} := \
                         if a == (b {token} 3) then a else b"
                    ),
                ]
            })
            .collect();
        let refs: Vec<&str> = sources.iter().map(String::as_str).collect();
        let env = island(&refs);

        for (_, _, class, projection) in OPERATORS {
            for (side, name) in [(0usize, format!("l{class}")), (1, format!("r{class}"))] {
                let value = definition_value(&env, &name);
                let body = peel(&value, 2);
                let (head, args) = uncurry(body);
                assert!(
                    matches!(head.kind(), ExprKind::Const(n, _) if *n == Name::from_string("ite")),
                    "u{bits} `{name}`: the head is not `ite`: {body}"
                );
                assert_eq!(args.len(), 5, "u{bits} `{name}`: {body}");

                // The proposition: `Eq.{1} Bool <decision> Bool.true`.
                let (prop_head, prop_args) = uncurry(args[1]);
                assert!(
                    matches!(prop_head.kind(), ExprKind::Const(n, _) if *n == Name::from_string("Eq")),
                    "u{bits} `{name}`: the proposition's head is not `Eq`"
                );
                assert_eq!(prop_args.len(), 3);
                assert!(
                    matches!(prop_args[0].kind(), ExprKind::Const(n, _) if *n == Name::from_string("Bool")),
                    "u{bits} `{name}`: the proposition is not stated at `Bool`"
                );
                assert!(
                    matches!(prop_args[2].kind(), ExprKind::Const(n, _) if *n == Name::from_string("Bool.true")),
                    "u{bits} `{name}`: the scrutinee is not `Bool.true`"
                );

                // The decision's operand at `side` is the SURFACE class at the
                // prelude instance — six arguments, three carriers, the bare
                // instance constant, then the leaves.
                let (_, beq_args) = uncurry(prop_args[1]);
                assert_eq!(beq_args.len(), 4, "u{bits} `{name}`: the decision spine");
                let (op_head, op_args) = uncurry(beq_args[2 + side]);
                assert!(
                    matches!(op_head.kind(), ExprKind::Const(n, _)
                        if *n == Name::from_string(&format!("{class}.{projection}"))),
                    "u{bits} `{name}`: the computed operand's head is not \
                     `{class}.{projection}`: {}",
                    beq_args[2 + side]
                );
                assert_eq!(op_args.len(), 6, "u{bits} `{name}`: the operand spine");
                assert!(
                    matches!(op_args[3].kind(), ExprKind::Const(n, _)
                        if *n == Name::from_string(&format!("inst{class}{carrier}"))),
                    "u{bits} `{name}`: the operand's instance is not the bare prelude constant"
                );

                // THE IDENTITY: the instance decides the SAME decision term.
                // This is what makes the reading one parse rather than two.
                let (inst_head, inst_args) = uncurry(args[2]);
                assert!(
                    matches!(inst_head.kind(), ExprKind::Const(n, _)
                        if *n == Name::from_string("instDecidableEqBool")),
                    "u{bits} `{name}`: the `ite`'s instance is not `instDecidableEqBool` — the \
                     UNIFORM `Bool`-level instance is the reason a computed operand is cheap here"
                );
                assert_eq!(inst_args.len(), 2);
                assert_eq!(
                    format!("{}", inst_args[0]),
                    format!("{}", prop_args[1]),
                    "u{bits} `{name}`: the instance decides a DIFFERENT term from the one the \
                     proposition states"
                );

                // THE NEGATIVE HALF. No normal form: `Nat.rec` is absent.
                assert!(
                    !mentions(&value, &Name::from_string("Nat.rec")),
                    "u{bits} `{name}`: `Nat.rec` appears in the elaborated term. Landing 6's \
                     refusal text claimed exactly this and it was FALSE of `==`; if the \
                     elaborator has started normalizing here, the computed-operand lane must \
                     be re-measured before it is trusted."
                );
                assert!(
                    !mentions(&value, &Name::from_string("instDecidableNatLt")),
                    "u{bits} `{name}`: the Nat-reduced instance appears; the `==` decision is \
                     supposed to resolve at `Bool`"
                );
            }
        }
    }
}

// ═══════ L8-P2 — THE SCRUTINEE SPELLINGS, AND THE FOUR TREES APART ═══════

/// **The polarity half, measured from both sides.**
///
/// Four scrutinee spellings reach this lane from real sources, and the pairs
/// are definitionally equal, so the reader carries a VALUE. And the four
/// disequality-adjacent trees are pairwise NOT definitionally equal — including
/// the one that computes the same function, which is the control that matters:
/// a polarity mistake cannot be laundered through defeq.
#[test]
fn l8_p2_the_scrutinee_is_a_measured_spelling_and_the_trees_stay_apart() {
    let env = island(&[
        "def s_beq (a : UInt64) (b : UInt64) : UInt64 := if a == b then a else b",
        "def s_true (a : UInt64) (b : UInt64) : UInt64 := if (a == b) = true then a else b",
        "def s_btrue (a : UInt64) (b : UInt64) : UInt64 := if (a == b) = Bool.true then a else b",
        "def s_false (a : UInt64) (b : UInt64) : UInt64 := if (a == b) = false then a else b",
        "def s_bfalse (a : UInt64) (b : UInt64) : UInt64 := if (a == b) = Bool.false then a else b",
    ]);

    // The SPELLING, read out of the term. The bare `false` a user's own token
    // resolves to is depth 1; `Bool.true` is depth 2. A reader keyed only on
    // `Bool.false` would match no real `(a == b) = false` at all — the R2/C9
    // class `control_14`'s spelling grain exists for.
    let scrutinee_of = |name: &str| -> String {
        let value = definition_value(&env, name);
        let (_, args) = uncurry(peel(&value, 2));
        let (_, prop_args) = uncurry(args[1]);
        format!("{}", prop_args[2])
    };
    assert_eq!(scrutinee_of("s_beq"), "Bool.true");
    assert_eq!(scrutinee_of("s_btrue"), "Bool.true");
    assert_eq!(scrutinee_of("s_bfalse"), "Bool.false");
    assert_eq!(
        scrutinee_of("s_true"),
        "true",
        "the explicit `= true` lift resolves to a BARE constant, not `Bool.true`"
    );
    assert_eq!(
        scrutinee_of("s_false"),
        "false",
        "THE SPELLING TRAP: `(a == b) = false` puts a BARE depth-1 `false` in the scrutinee. A \
         reader keyed on `Bool.false` would match no real source."
    );

    // The DEFEQ BRIDGES: each pair denotes one value, so carrying the value is
    // faithful and the producer may mint either spelling.
    for (label, sources) in [
        (
            "true ≡ Bool.true",
            vec![
                "def x (a : UInt64) (b : UInt64) : UInt64 := if (a == b) = true then a else b",
                "def y (a : UInt64) (b : UInt64) : UInt64 := if (a == b) = Bool.true then a else b",
                "theorem same : x = y := rfl",
            ],
        ),
        (
            "false ≡ Bool.false",
            vec![
                "def x (a : UInt64) (b : UInt64) : UInt64 := if (a == b) = false then a else b",
                "def y (a : UInt64) (b : UInt64) : UInt64 := if (a == b) = Bool.false then a else b",
                "theorem same : x = y := rfl",
            ],
        ),
        (
            "= true ≡ ==",
            vec![
                "def x (a : UInt64) (b : UInt64) : UInt64 := if (a == b) = true then a else b",
                "def y (a : UInt64) (b : UInt64) : UInt64 := if a == b then a else b",
                "theorem same : x = y := rfl",
            ],
        ),
    ] {
        assert!(
            island_try(&sources).is_ok(),
            "{label}: the two spellings must be definitionally equal, or the reader may not \
             carry a VALUE"
        );
    }

    // THE FOUR TREES, PAIRWISE APART. Every one of these is a `rfl` the island
    // REFUSES, and the third is the one that matters most: it computes the same
    // function.
    for (label, sources) in [
        (
            "`= false` vs `==`",
            vec![
                "def x (a : UInt64) (b : UInt64) : UInt64 := if (a == b) = false then a else b",
                "def y (a : UInt64) (b : UInt64) : UInt64 := if a == b then a else b",
                "theorem same : x = y := rfl",
            ],
        ),
        (
            "`= false` vs `!=`",
            vec![
                "def x (a : UInt64) (b : UInt64) : UInt64 := if (a == b) = false then a else b",
                "def y (a : UInt64) (b : UInt64) : UInt64 := if a != b then a else b",
                "theorem same : x = y := rfl",
            ],
        ),
        (
            "`= false` vs `==` WITH SWAPPED ARMS — the same function",
            vec![
                "def x (a : UInt64) (b : UInt64) : UInt64 := if (a == b) = false then b else a",
                "def y (a : UInt64) (b : UInt64) : UInt64 := if a == b then a else b",
                "theorem same : x = y := rfl",
            ],
        ),
        (
            "`= false` vs the propositional `≠`",
            vec![
                "def x (a : UInt64) (b : UInt64) : UInt64 := if (a == b) = false then a else b",
                "def y (a : UInt64) (b : UInt64) : UInt64 := if a ≠ b then a else b",
                "theorem same : x = y := rfl",
            ],
        ),
    ] {
        assert!(
            island_try(&sources).is_err(),
            "{label}: the island must REFUSE `rfl` between these two. If it stops refusing, a \
             body emitted for one could be gated against the other and the polarity would stop \
             being decided by the kernel."
        );
    }
}

// ═════════ L8-P3 — THE COMPUTED OPERAND ADMITS END TO END ═════════

/// **The whole pipeline for a computed decision operand**: plan, the REAL
/// template, the rendered body, side B's SEPARATE reader, the NEW producer
/// route and the kernel gate — at every width, for every operator, in both
/// decision positions.
///
/// The emitted body is asserted to be what it claims: the two-step diamond with
/// ONE extra statement at the head of the entry block and ONE extra local,
/// everything below the `SwitchInt` unchanged.
#[test]
fn l8_p3_a_computed_equality_operand_admits_end_to_end() {
    for bits in WIDTHS {
        let carrier = format!("UInt{bits}");
        let sources: Vec<String> = OPERATORS
            .iter()
            .flat_map(|(_, token, class, _)| {
                [
                    format!(
                        "def l{class} (a : {carrier}) (b : {carrier}) : {carrier} := \
                         if (a {token} 3) == 0 then a else b"
                    ),
                    format!(
                        "def r{class} (a : {carrier}) (b : {carrier}) : {carrier} := \
                         if a == (b {token} 3) then a else b"
                    ),
                ]
            })
            .collect();
        let refs: Vec<&str> = sources.iter().map(String::as_str).collect();
        let env = island(&refs);

        for (op, _, class, _) in OPERATORS {
            let node = BeqOperand::RawBin {
                op,
                left: ArithOperand::Param(0),
                right: ArithOperand::Const(3),
            };
            let node_right = BeqOperand::RawBin {
                op,
                left: ArithOperand::Param(1),
                right: ArithOperand::Const(3),
            };
            for (name, expected) in [
                (
                    format!("l{class}"),
                    CleanOriginShape::SelectBeqGeneral {
                        scrutinee: true,
                        cmp_left: node,
                        cmp_right: BeqOperand::Const(0),
                        then_arm: ArithOperand::Param(0),
                        else_arm: ArithOperand::Param(1),
                    },
                ),
                (
                    format!("r{class}"),
                    CleanOriginShape::SelectBeqGeneral {
                        scrutinee: true,
                        cmp_left: BeqOperand::Param(0),
                        cmp_right: node_right,
                        then_arm: ArithOperand::Param(0),
                        else_arm: ArithOperand::Param(1),
                    },
                ),
            ] {
                let (plan, emitted) = plan_and_emit(&env, &name, bits);
                assert_eq!(plan.shape(), &expected, "u{bits} `{name}`: the planned shape");
                // THE ROW DID NOT MOVE. That is this landing's structural
                // claim, asserted rather than described.
                let selected = ladder_row(plan.shape()).expect("row");
                assert_eq!(selected.name, "select.beq", "u{bits} `{name}`: the selected row");
                assert_eq!(selected.mir, MirShape::BoolDecisionBranch);

                // The emitted body: four blocks, THREE entry statements, and
                // one more local than landing 6's shape.
                assert_eq!(emitted.body.blocks.len(), 4, "u{bits} `{name}`");
                assert_eq!(
                    emitted.body.blocks[0].stmts.len(),
                    3,
                    "u{bits} `{name}`: the computed operand is ONE extra statement at the head \
                     of the entry block"
                );
                assert_eq!(
                    emitted.body.locals.len(),
                    7,
                    "u{bits} `{name}`: `_0`, two parameters, the select temp, two bools and ONE \
                     computed temp"
                );
                let Statement::Assign { place, rvalue: Rvalue::BinaryOp(binop, _, _), .. } =
                    &emitted.body.blocks[0].stmts[0]
                else {
                    panic!("u{bits} `{name}`: the first entry statement is not a binary op");
                };
                assert_eq!(*binop, op.mir_binop(), "u{bits} `{name}`: the computed operator");
                assert_eq!(
                    place.local, 6,
                    "u{bits} `{name}`: the computed temp is `_{{n+4}}` — APPENDED after landing \
                     6's select temp and two bools, which is what keeps a `SelectBeq` template \
                     byte-identical to the one landing 6 shipped"
                );

                // Side B's SEPARATE reader agrees with the plan.
                let read = recognize_select_beq_general(&emitted).unwrap_or_else(|| {
                    panic!("u{bits} `{name}`: side B must read the emitted body")
                });
                assert!(read.scrutinee, "u{bits} `{name}`: the lift is against `true`");
                let CleanOriginShape::SelectBeqGeneral { cmp_left, cmp_right, .. } = &expected
                else {
                    unreachable!()
                };
                assert_eq!(read.cmp_left, *cmp_left);
                assert_eq!(read.cmp_right, *cmp_right);

                // And the gate.
                admit_lowering(&env, &plan, &emitted).unwrap_or_else(|refusal| {
                    panic!("u{bits} `{name}` must admit end to end: {refusal:?}")
                });
            }
        }

        // BOTH operands computed, at one width per pass: two prefix statements,
        // two temps, in LEFT-then-RIGHT order.
        let env2 = island(&[&format!(
            "def two (a : {carrier}) (b : {carrier}) : {carrier} := \
             if (a &&& 3) == (b ||| 3) then a else b"
        )]);
        let (plan, emitted) = plan_and_emit(&env2, "two", bits);
        assert_eq!(
            emitted.body.blocks[0].stmts.len(),
            4,
            "u{bits} `two`: two computed operands are two extra statements"
        );
        assert_eq!(emitted.body.locals.len(), 8, "u{bits} `two`: two computed temps");
        let read = recognize_select_beq_general(&emitted).expect("u{bits} `two`: side B");
        assert_eq!(
            read.cmp_left,
            BeqOperand::RawBin {
                op: RawBinOpKind::BitAnd,
                left: ArithOperand::Param(0),
                right: ArithOperand::Const(3),
            },
            "u{bits} `two`: the LEFT operand resolves to the FIRST prefix statement"
        );
        assert_eq!(
            read.cmp_right,
            BeqOperand::RawBin {
                op: RawBinOpKind::BitOr,
                left: ArithOperand::Param(1),
                right: ArithOperand::Const(3),
            },
        );
        admit_lowering(&env2, &plan, &emitted)
            .unwrap_or_else(|refusal| panic!("u{bits} `two` must admit: {refusal:?}"));
    }
}

// ═════════ L8-P4 — `(a == b) = false` ADMITS END TO END ═════════

/// **The polarity lane, end to end at every width**, over the whole operand
/// vocabulary and with a computed operand under it as well.
///
/// The emitted body is the two-step diamond with `const false` in the lift and
/// **the arms in the order the source wrote them** — no swap, no `SwitchInt`
/// flip. That is asserted here, because the alternative is the one landing 6
/// refused in advance and the one `l8_p2` measures the kernel refusing.
#[test]
fn l8_p4_the_false_polarity_admits_end_to_end() {
    for bits in WIDTHS {
        let carrier = format!("UInt{bits}");
        let env = island(&[
            &format!(
                "def nf (a : {carrier}) (b : {carrier}) : {carrier} := \
                 if (a == b) = false then a else b"
            ),
            &format!(
                "def nfb (a : {carrier}) (b : {carrier}) : {carrier} := \
                 if (a == b) = Bool.false then a else b"
            ),
            &format!(
                "def nfl (a : {carrier}) (b : {carrier}) : {carrier} := \
                 if (a == 3) = false then 7 else b"
            ),
            &format!(
                "def nfc (a : {carrier}) (b : {carrier}) : {carrier} := \
                 if ((a &&& 3) == 0) = false then a else b"
            ),
        ]);

        for (name, expected) in [
            (
                "nf",
                CleanOriginShape::SelectBeqGeneral {
                    scrutinee: false,
                    cmp_left: BeqOperand::Param(0),
                    cmp_right: BeqOperand::Param(1),
                    then_arm: ArithOperand::Param(0),
                    else_arm: ArithOperand::Param(1),
                },
            ),
            (
                "nfb",
                CleanOriginShape::SelectBeqGeneral {
                    scrutinee: false,
                    cmp_left: BeqOperand::Param(0),
                    cmp_right: BeqOperand::Param(1),
                    then_arm: ArithOperand::Param(0),
                    else_arm: ArithOperand::Param(1),
                },
            ),
            (
                "nfl",
                CleanOriginShape::SelectBeqGeneral {
                    scrutinee: false,
                    cmp_left: BeqOperand::Param(0),
                    cmp_right: BeqOperand::Const(3),
                    then_arm: ArithOperand::Const(7),
                    else_arm: ArithOperand::Param(1),
                },
            ),
            (
                "nfc",
                CleanOriginShape::SelectBeqGeneral {
                    scrutinee: false,
                    cmp_left: BeqOperand::RawBin {
                        op: RawBinOpKind::BitAnd,
                        left: ArithOperand::Param(0),
                        right: ArithOperand::Const(3),
                    },
                    cmp_right: BeqOperand::Const(0),
                    then_arm: ArithOperand::Param(0),
                    else_arm: ArithOperand::Param(1),
                },
            ),
        ] {
            let (plan, emitted) = plan_and_emit(&env, name, bits);
            assert_eq!(plan.shape(), &expected, "u{bits} `{name}`: the planned shape");

            // THE LIFT CARRIES THE POLARITY, and the arms are untouched.
            let lift = emitted.body.blocks[0].stmts.last().expect("a lift statement");
            let Statement::Assign { rvalue: Rvalue::BinaryOp(BinOp::Eq, _, right), .. } = lift
            else {
                panic!("u{bits} `{name}`: the lift is not an `Eq`");
            };
            assert!(
                matches!(right, Operand::Constant(ConstValue::Bool(false))),
                "u{bits} `{name}`: the emitted lift must carry `const false` — the polarity is \
                 transcribed, never compensated for"
            );
            let Terminator::SwitchInt { targets, otherwise, .. } =
                &emitted.body.blocks[0].terminator
            else {
                panic!("u{bits} `{name}`: the entry block does not branch");
            };
            assert_eq!(
                (targets[0].0, targets[0].1, *otherwise),
                (0, BlockId(2), BlockId(1)),
                "u{bits} `{name}`: the `SwitchInt` polarity is landing 6's, UNCHANGED. Flipping \
                 it here instead of emitting `const false` is the move landing 6 refused in \
                 advance, because side B would then read a `==` tree off a body denoting its \
                 complement."
            );

            let read = recognize_select_beq_general(&emitted)
                .unwrap_or_else(|| panic!("u{bits} `{name}`: side B must read the body"));
            assert!(!read.scrutinee, "u{bits} `{name}`: side B must read the polarity back");

            admit_lowering(&env, &plan, &emitted).unwrap_or_else(|refusal| {
                panic!("u{bits} `{name}` must admit end to end: {refusal:?}")
            });
        }
    }
}

// ═══════ L8-P5 — THE E6 IMPORT DIRECTION'S REACH DID NOT MOVE ═══════

/// **Four readers decline the new bodies**, and the fourth is the one that
/// binds hardest: the computed body carries a raw `Rvalue::BinaryOp`, whose
/// exclusion from `recognize_admissible_body` is the PINNED provenance boundary
/// `binop_provenance_pins_never_admit` states.
#[test]
fn l8_p5_the_general_beq_reading_stays_out_of_the_e6_chain() {
    let env = island(&[
        "def gc (a : UInt64) (b : UInt64) : UInt64 := if (a &&& 3) == 0 then a else b",
        "def gf (a : UInt64) (b : UInt64) : UInt64 := if (a == b) = false then a else b",
        "def gb (a : UInt64) (b : UInt64) : UInt64 := if a == b then a else b",
    ]);
    for name in ["gc", "gf"] {
        let (_, emitted) = plan_and_emit(&env, name, 64);
        assert!(
            recognize_admissible_body(&emitted).is_none(),
            "`{name}`: the general two-step diamond must stay outside the E6 chain — a reading \
             there becomes a defining equation with NO side A and NO kernel gate"
        );
        assert!(
            recognize_select_general(&emitted).is_none(),
            "`{name}`: the ONE-step select reader must decline it"
        );
        assert!(
            recognize_select_beq(&emitted).is_none(),
            "`{name}`: landing 6's NARROW reader must decline it — that is the disjointness \
             this landing rests on, read off the bytes rather than asserted"
        );
        assert!(
            recognize_raw_binop(&emitted).is_none(),
            "`{name}`: the whole-body raw-binop reader must decline it"
        );
    }
    // And the converse: landing 6's own body is still read by landing 6's
    // reader and DECLINED by this landing's, so no body has two readings.
    let (_, narrow) = plan_and_emit(&env, "gb", 64);
    assert!(recognize_select_beq(&narrow).is_some(), "`gb`: landing 6's reader still reads it");
    assert!(
        recognize_select_beq_general(&narrow).is_none(),
        "`gb`: the general reader must DECLINE landing 6's body. Two readings of one emitted \
         body is the hazard the disjointness invariant exists for."
    );
}

// ═══ L8-P6 — WHAT STAYS REFUSED, ALL KERNEL-GREEN, ALL REALIZATION-BLOCKED ═══

/// **Three shapes that elaborate, kernel-check, and are still refused — plus
/// the `<`/`<=` half of the computed condition, which must stay refused
/// PERMANENTLY for a different reason.**
///
/// Recording them as measurements rather than as cautions is what makes the
/// MISS ledger's reasons checkable. The first three are blocked on the emitted
/// REALIZATION; the fourth is blocked on the elaborator's NORMAL FORM, which is
/// the one boundary on this list that must not be crossed.
#[test]
fn l8_p6_the_refused_neighbours_are_kernel_green_and_realization_blocked() {
    // (a) a NESTED operand, (b) a WRAPPING operand, (c) a computed ARM.
    let env = island(&[
        "def nest (a : UInt64) (b : UInt64) : UInt64 := if ((a &&& b) ||| 1) == 0 then a else b",
        "def wrap (a : UInt64) (b : UInt64) : UInt64 := if (a + 1) == 0 then a else b",
        "def carm (a : UInt64) (b : UInt64) : UInt64 := if a == b then a &&& 1 else b",
    ]);
    for (name, note) in
        [("nest", "a nested operand"), ("wrap", "a wrapping operand"), ("carm", "a computed arm")]
    {
        // KERNEL-GREEN: the island accepted the source, so the term exists and
        // is checked. It is the PLAN that refuses.
        let refusal = plan_clean_origin_body(&env, name)
            .err()
            .unwrap_or_else(|| panic!("{note} (`{name}`) must NOT plan in this landing"));
        let text = refusal_text(&refusal);
        assert!(
            text.contains("`==`"),
            "{note}: the refusal must still name the operator it found, not fall through to the \
             generic fragment prose:\n{text}"
        );
    }

    // …and each is defeq to the round-trip spelling side B would mint, which is
    // what makes them WORK ITEMS rather than wishes.
    for (label, sources) in [
        (
            "nested operand",
            vec![
                "def x (a : UInt64) (b : UInt64) : UInt64 := if ((a &&& b) ||| 1) == 0 then a else b",
                "def y (a : UInt64) (b : UInt64) : UInt64 := \
                 if (UInt64.ofNat (Nat.lor (UInt64.toNat (UInt64.ofNat (Nat.land (UInt64.toNat a) \
                 (UInt64.toNat b)))) (UInt64.toNat (UInt64.ofNat 1)))) == (UInt64.ofNat 0) \
                 then a else b",
                "theorem same : x = y := rfl",
            ],
        ),
        (
            "computed arm",
            vec![
                "def x (a : UInt64) (b : UInt64) : UInt64 := if a == b then a &&& 1 else b",
                "def y (a : UInt64) (b : UInt64) : UInt64 := \
                 if a == b then UInt64.ofNat (Nat.land (UInt64.toNat a) \
                 (UInt64.toNat (UInt64.ofNat 1))) else b",
                "theorem same : x = y := rfl",
            ],
        ),
    ] {
        assert!(
            island_try(&sources).is_ok(),
            "{label}: the KERNEL half is green and the ledger says so; if this stops holding the \
             MISS reason must be rewritten"
        );
    }

    // (d) THE `<` HALF, which must stay refused permanently. `if a + 1 < b`
    // resolves its decidability through a `Nat.rec`-headed NORMAL FORM of the
    // modular reduction — the thing landing 6's text wrongly attributed to `==`.
    let lt = island(&[
        "def lt1 (a : UInt64) (b : UInt64) : UInt64 := if a + 1 < b then a else b",
        "def lt2 (a : UInt64) (b : UInt64) : UInt64 := if a / 2 < b then a else b",
        "def lt3 (a : UInt64) (b : UInt64) : UInt64 := if (a &&& 1) < b then a else b",
    ]);
    for name in ["lt1", "lt2", "lt3"] {
        let value = definition_value(&lt, name);
        assert!(
            mentions(&value, &Name::from_string("Nat.rec")),
            "`{name}`: the `<` computed condition is supposed to carry a `Nat.rec`-headed normal \
             form. If it no longer does, the PERMANENT refusal recorded for the `<`/`<=` half of \
             the computed-condition demand must be re-measured before it is quoted again."
        );
        assert!(
            plan_clean_origin_body(&lt, name).is_err(),
            "`{name}`: a computed `<` condition must stay refused — serving it means side B \
             reproducing an elaborator's instance-synthesis output term for term"
        );
    }
}

// ═══════ L8-P7 — THE DIVISOR RULE, INSIDE AN OPERAND, THREE TIMES ═══════

/// **The one soundness boundary this landing carries into a new position.**
///
/// Clean's `{C}.div`/`.mod` are TOTAL and Rust's `/`/`%` PANIC, so a `/` or `%`
/// inside a decision operand is governed by exactly the rule landing 7 stated
/// for a whole body — and it is enforced three times, by three programs:
/// side A's recogniser, the sealed plan, and the FROZEN producer.
#[test]
fn l8_p7_the_divisor_rule_holds_inside_a_decision_operand() {
    let env = island(&[
        "def dv (a : UInt64) (b : UInt64) : UInt64 := if (a / b) == 0 then a else b",
        "def dz (a : UInt64) (b : UInt64) : UInt64 := if (a / 0) == 0 then a else b",
        "def mv (a : UInt64) (b : UInt64) : UInt64 := if (a % b) == 0 then a else b",
        "def mz (a : UInt64) (b : UInt64) : UInt64 := if (a % 0) == 0 then a else b",
        // …and the safe one, for the contrast that makes the refusal a
        // capability statement rather than a blanket ban.
        "def ok (a : UInt64) (b : UInt64) : UInt64 := if (a / 3) == 0 then a else b",
    ]);

    for name in ["dv", "dz", "mv", "mz"] {
        let refusal = plan_clean_origin_body(&env, name)
            .err()
            .unwrap_or_else(|| panic!("`{name}` must be refused: an unsafe divisor in an operand"));
        let text = refusal_text(&refusal);
        assert!(
            text.contains("TOTAL") && text.contains("PANICS"),
            "`{name}`: the refusal must state the SEMANTIC gap, not a parser limit:\n{text}"
        );
        assert!(
            text.contains("strictly positive numeral"),
            "`{name}`: the refusal must name the divisor this lane does emit:\n{text}"
        );
    }

    // The safe divisor travels the whole pipeline.
    let (plan, emitted) = plan_and_emit(&env, "ok", 64);
    admit_lowering(&env, &plan, &emitted)
        .unwrap_or_else(|refusal| panic!("`ok` must admit: {refusal:?}"));

    // AND THE THIRD REFUSAL, from the FROZEN producer, which knows nothing
    // about this lane: it will not elaborate a variable or zero divisor at all.
    let mut scratch = env.clone();
    for rendering in ["p0 / p1", "p0 / 0", "p0 % p1", "p0 % 0"] {
        let minted = trust_spec_elab::admit_select_beq_operands_function(
            &mut scratch,
            "probe_unsafe",
            &[
                trust_spec_elab::Domain::Machine(trust_spec_elab::MachineUIntWidth::U64),
                trust_spec_elab::Domain::Machine(trust_spec_elab::MachineUIntWidth::U64),
            ],
            true,
            &trust_spec_elab::SelectBeqOperand::Computed(rendering.to_owned()),
            &trust_spec_elab::SelectBeqOperand::Literal(0),
            trust_spec_elab::SelectOperand::Param(0),
            trust_spec_elab::SelectOperand::Param(1),
        );
        assert!(
            minted.is_err(),
            "the FROZEN producer must refuse `{rendering}` independently of this lane's planner \
             — that independence is the double fault, not a restatement"
        );
    }
}

// ═══════ L8-P8 — THE REFUSAL TEXTS ARE TRUE OF THE PROGRAM ═══════

/// **The `r2_session_probes::probe_p9` class, closed for this lane's two
/// worst instances.**
///
/// A refusal whose stated reason is false of the program in front of it sends
/// the reader to fix something that is not wrong. Landing 6 shipped two:
///
/// * the `==` boundary claimed a computed operand *"resolves its decidability
///   through an elaborator normal form no producer reproduces"* — measured
///   false by `l8_p1`, and it steered the next planner away from the cheapest
///   available landing;
/// * the `!=` boundary said the negation *"is not reachable by flipping
///   `Bool.true`"* and left the reader with no emitted disequality at all —
///   true then, incomplete now that `(a == b) = false` IS emitted.
///
/// Both texts are pinned here so they cannot silently drift back.
#[test]
fn l8_p8_the_beq_refusals_state_what_is_true_of_the_program() {
    let env = island(&[
        "def wrap (a : UInt64) (b : UInt64) : UInt64 := if (a + 1) == 0 then a else b",
        "def ne (a : UInt64) (b : UInt64) : UInt64 := if a != b then a else b",
    ]);

    let equal = refusal_text(&plan_clean_origin_body(&env, "wrap").expect_err("refused"));
    assert!(
        !equal.contains("normal form"),
        "THE DELETED CLAIM IS BACK. The `==` refusal must not attribute an elaborator normal \
         form to a tree that has none (`l8_p1` measures its absence at four widths):\n{equal}"
    );
    assert!(
        equal.contains("raw binary operator") && equal.contains("&&&"),
        "the `==` refusal must name the operand vocabulary that IS served:\n{equal}"
    );
    assert!(
        equal.contains("`Call` TERMINATOR"),
        "the `==` refusal must name the real blocker for a wrapping operand — a block \
         boundary, not a decidability question:\n{equal}"
    );

    let not_equal = refusal_text(&plan_clean_origin_body(&env, "ne").expect_err("refused"));
    assert!(
        not_equal.contains("(a == b) = false"),
        "the `!=` refusal must offer the disequality that IS emitted:\n{not_equal}"
    );
    assert!(
        !not_equal.contains("no emittable spelling of DISEQUALITY on this lane at all"),
        "THE SUPERSEDED CLAIM IS BACK. There IS an emittable disequality since this landing, \
         and a refusal that denies it is false of the program:\n{not_equal}"
    );
    assert!(
        not_equal.contains("Bool.not"),
        "the `!=` refusal must still name the node that blocks it:\n{not_equal}"
    );
    // …and the refusal must NOT claim the two are interchangeable. `l8_p2`
    // measures that the kernel refuses `rfl` between them, so the offered fix
    // is a RESTATEMENT the user makes, never a rewrite the compiler performs.
    assert!(
        not_equal.contains("refuses `rfl`"),
        "the `!=` refusal must say that the offered restatement is a DIFFERENT term the kernel \
         distinguishes, not an equivalent the compiler could have applied itself:\n{not_equal}"
    );
}

// ═══ L8-P9 — THE `gcd` MISS REASON WAS STALE, AND THIS IS WHAT REPLACES IT ═══

/// **The ledger's `WellFounded.fix` over TWO parameters entry recorded a
/// blocker that no longer exists, and its `measured_by` named no test
/// function at all.**
///
/// It read: *"Refused in `first-party/clean`'s own elaborator
/// (`RecursionOutsideFragment`) before this lane sees it"*. At the current pin
/// that is FALSE — the §1 demo shape elaborates AND kernel-checks — so the only
/// thing between a user's `gcd` and an emitted body is this crate's own
/// recogniser. Defence depth fell from two repositories to one and nothing
/// measured it.
///
/// This probe is what the entry's `measured_by` now points at. It asserts the
/// three facts the rewritten reason rests on:
///
/// 1. the two-parameter `WellFounded.fix` shape ELABORATES and kernel-checks;
/// 2. this crate REFUSES it, with a `WellFounded.fix`-specific note rather than
///    the generic fragment prose — so the refusal is inside this lane;
/// 3. the recursive argument is `a % b` at a VARIABLE divisor, which is the
///    ledger's one SOUNDNESS-boundary entry — so `gcd` is gated behind it and
///    serving `gcd` means serving a variable-divisor `%` first.
///
/// **It must STAY REFUSED.** The point of measuring it is that the reason in
/// the ledger has to be the reason in the program.
#[test]
fn l8_p9_two_parameter_well_founded_recursion_now_elaborates_and_is_refused_here() {
    let env =
        island_try(&["def gcd (a : Nat) (b : Nat) : Nat := if b == 0 then a else gcd b (a % b)\n\
         termination_by b"])
        .expect(
            "THE LEDGER WAS STALE AND THIS IS THE MEASUREMENT. At the current clean pin the \
         two-parameter well-founded shape ELABORATES and kernel-checks; the entry that said \
         `first-party/clean` refuses it was written against an older pin. If this ever fails \
         again, the elaborator has moved back and the entry must be re-measured rather than \
         restored from memory.",
        );

    // 2. The refusal is INSIDE this crate, and it names the spine.
    let refusal = plan_clean_origin_body(&env, "gcd").err().expect(
        "`gcd` must stay refused: a second parameter threaded through the motive is a \
                 different functional shape, and its recursive argument is a variable-divisor `%`",
    );
    let text = refusal_text(&refusal);
    assert!(
        text.contains("WellFounded.fix"),
        "the refusal must name the spine it declined, not fall through to the generic fragment \
         prose — a user sent to `first-party/clean` would be sent to fix an elaborator that \
         already works:\n{text}"
    );

    // 3. The recursive argument really is `a % b` at a VARIABLE divisor, which
    //    is what puts `gcd` behind the ledger's one soundness boundary.
    let value = definition_value(&env, "gcd");
    assert!(
        mentions(&value, &Name::from_string("HMod.hMod")),
        "`gcd`'s recursive argument is `a % b`; the entry's second half — that the \
         variable-divisor boundary sits behind the arity one — rests on this"
    );
    assert!(
        mentions(&value, &Name::from_string("WellFounded.fix")),
        "…and the shape really is a `WellFounded.fix` spine"
    );

    // The two boundaries that DO still hold, so the rewritten reason is
    // complete rather than merely corrected.
    assert!(
        island_try(&["def gcd64 (a : UInt64) (b : UInt64) : UInt64 := \
             if b == 0 then a else gcd64 b (a % b)\n\
             termination_by b",])
        .is_err(),
        "only `Nat`-valued `termination_by` measures are supported; a machine-width one is \
         still refused in the elaborator"
    );
    assert!(
        island_try(&[
            "def gcdish (a : Nat) (b : Nat) : Nat := if h : 0 < b then gcdish b (a - 1) else a\n\
             termination_by b",
        ])
        .is_err(),
        "a decrease the cascade cannot discharge is still refused — and THAT, not the arity, is \
         what `r2_session_probes::probe_p8` measures with this same subject"
    );
}

// ═══ L8-P10 — TWO MORE LEDGER REASONS, RE-POINTED AT WHAT THEY DESCRIBE ═══

/// **Two MISS entries whose reasons described a boundary the program does not
/// reach.** Neither is served here; both are re-measured so the ledger says
/// what the compiler does.
///
/// * **`Nat.rec` wrapped back to a machine width.** The recorded reason (the
///   e2 boundary: open equations at the u64 carrier are not definitional) is
///   RIGHT. The spelling a user actually writes — define the recursion at
///   `Nat` by equations and wrap it — has a NAMED CONSTANT at its head; since
///   a385c099a98 (named Lean call expansion) the call lane inlines that checked
///   helper to its `Nat.rec` body, so this spelling now reaches the same e2 arm
///   as the hand-written `Nat.rec`. (Before a385c099a98 it fell through to the
///   generic no-row message, which mentioned neither e2 nor the carrier.) The
///   bare `ofNat`/`toNat` round trip, with no recursion, still meets the
///   generic fall-through — which since 2026-09-23 cites `uint.lit` as the row
///   that selects `UInt64.ofNat` (at a literal), because it does
///   (`landing7_selection_probes::l7_p17`). And a third spelling (the equation
///   form declared at the machine width) does not elaborate at all.
/// * **A pair-valued recursion (`fib`).** The recorded reason names the missing
///   `Prod` carrier. `fib` never reaches the carrier: its own signature is
///   `Nat -> Nat`, so it refuses at the TABLE, on the `Prod` projection
///   (`Prod.fst`, inlined to a kernel projection since a385c099a98). A planner
///   who trusted the entry would build the carrier and find `fib` still
///   refusing.
#[test]
fn l8_p10_two_miss_reasons_are_re_pointed_at_the_boundary_the_program_meets() {
    // ── `Nat.rec` wrapped back to a machine width: THREE spellings ─────────
    let natural = island(&[
        "def tozero : Nat -> Nat\n  | 0 => 0\n  | n + 1 => tozero n",
        "def tz64 (n : UInt64) : UInt64 := UInt64.ofNat (tozero (UInt64.toNat n))",
        "def rt (n : UInt64) : UInt64 := UInt64.ofNat (UInt64.toNat n)",
    ]);
    let natural_text =
        refusal_text(&plan_clean_origin_body(&natural, "tz64").expect_err("must be refused"));
    // Since a385c099a98 (named Lean call expansion) the named constant
    // `tozero` is inlined to its `Nat.rec` body, so the NATURAL spelling now
    // meets the e2 boundary itself. (Before that commit this assertion was
    // negated: the named head fell through to the generic no-row message.)
    assert!(
        natural_text.contains("r1_equation_probes e2"),
        "the NATURAL spelling's named head `tozero` is expanded to its `Nat.rec` body, so it \
         must reach the e2 arm — the boundary this program actually meets:\n{natural_text}"
    );
    assert!(
        natural_text.contains("UInt64.ofNat"),
        "…and the e2 refusal names the machine-width wrapper:\n{natural_text}"
    );
    // The BARE round trip, with no recursion at all, has nothing to expand and
    // still refuses at the generic fall-through, which names the head — so the
    // bare conversion's blocker is its SHAPE (`uint.lit` selects `UInt64.ofNat`
    // only over a literal; no row realizes the conversion), while the
    // recursion's blocker is e2.
    let bare = refusal_text(&plan_clean_origin_body(&natural, "rt").expect_err("must be refused"));
    assert!(
        bare.contains("UInt64.ofNat") && !bare.contains("r1_equation_probes e2"),
        "the bare `ofNat`/`toNat` round trip refuses at the generic fall-through, not at e2:\n{bare}"
    );
    // The EXPLICIT `Nat.rec` spelling IS the one the e2 arm was written for.
    let explicit = island(&["def tzr (n : UInt64) : UInt64 := \
         UInt64.ofNat (Nat.rec (motive := fun _ => Nat) 0 (fun k ih => ih) (UInt64.toNat n))"]);
    let explicit_text =
        refusal_text(&plan_clean_origin_body(&explicit, "tzr").expect_err("must be refused"));
    assert!(
        explicit_text.contains("e2") && explicit_text.contains("Nat.mod"),
        "the EXPLICIT `Nat.rec` spelling must still get the e2 refusal, naming the mechanism:\
         \n{explicit_text}"
    );
    // The THIRD spelling — the equation form at the machine width — does not
    // elaborate, so it never reaches this crate at all.
    assert!(
        island_try(&["def cnt : UInt64 -> UInt64\n  | 0 => 0\n  | n + 1 => cnt n"]).is_err(),
        "literal patterns at a machine-width scrutinee are refused in the elaborator; the entry \
         must record that as a third, distinct blocker"
    );

    // ── the pair-valued recursion: `fib` meets the TABLE, not the carrier ──
    let fib =
        island(&["def fib : Nat -> Nat\n  | 0 => 0\n  | 1 => 1\n  | n + 2 => fib (n + 1) + fib n"]);
    let fib_refusal = plan_clean_origin_body(&fib, "fib").expect_err("must be refused");
    let fib_text = refusal_text(&fib_refusal);
    // Since a385c099a98 (named Lean call expansion) the checked helpers in
    // `fib`'s body — `Prod.fst` and `fib.cov` — are inlined before the table
    // is consulted a second time, so the head the table meets is the kernel
    // projection itself (`a projection out of a structure`) rather than the
    // named constant `Prod.fst` this assertion used to pin. The boundary is
    // unchanged: the TABLE, with no row for the projection, not the carrier.
    assert!(
        matches!(fib_refusal, EmitRefusal::NotEmittable { .. })
            && fib_text.contains("a projection out of a structure")
            && fib_text.contains("no selection row"),
        "`fib`'s own signature is `Nat -> Nat`, so the CARRIER is granted and the plan refuses \
         at the TABLE on the `Prod` projection. The entry's reason named the missing `Prod` \
         carrier, which this body never reaches:\n{fib_text}"
    );
    // …and `fib.cov`, which DOES carry a pair, is where the carrier refusal
    // lives — and it is a DIFFERENT `EmitRefusal` VARIANT, which is the sharpest
    // available statement that the two halves meet two boundaries.
    let cov = plan_clean_origin_body(&fib, "fib.cov").expect_err("must be refused");
    assert!(
        matches!(cov, EmitRefusal::NoTotalCarrier { .. }),
        "`fib.cov` is the pair-valued half and refuses at the CARRIER (`NoTotalCarrier`), while \
         `fib` itself refuses at the TABLE (`NotEmittable` on the `Prod` projection). Two halves, two \
         boundaries, two refusal variants — which the single-cause entry could not say: {cov:?}"
    );
    assert!(
        format!("{cov:?}").contains("Prod"),
        "…and the carrier refusal names the unmodeled type: {cov:?}"
    );
}

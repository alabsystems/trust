// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 27 — THE `let`-BOUND RUST CALL VALUE-TEMPORARY EMITTER MUTATION
//! FIXTURE** (W5 increment 7, battery row r24; design of record
//! `docs/design/2026-09-13-lean-calls-rust-lane.md`).
//!
//! `control_23` is the emitter-mutation discipline pointed at the Rust-call
//! chain; this file is the same discipline pointed at the chain AS A DAG —
//! `def dup (x : UInt64) : UInt64 := let y := dbl x; sub2 y y` beside
//! `fn dbl(x: u64) -> u64` and `fn sub2(a: u64, b: u64) -> u64`, where the
//! `let`-bound call is ONE node read twice, evaluated exactly once.
//!
//! Side A is the REAL elaboration (`CleanIslandSession::declare_rust_callees`,
//! exactly as `control_23`); side B is the emitted body as
//! `trust_mir_extract` would read it back, hand-built in the extracted shape,
//! and — new here — the body the shipped MATERIALIZER templates, rendered
//! through the same test-side renderer `control_11` uses, so the template is
//! pinned byte-for-byte against the hand-built expectation.
//!
//! # THE DIVISION OF LABOUR THIS CONTROL EXISTS TO PIN
//!
//! The kernel gate decides `is_def_eq(D, R)` where `D` is the declaration
//! WITH its `let`s and `R` is the reflected EMITTED dataflow, unfolded. Zeta
//! makes the kernel BLIND to multiplicity and order: it identifies
//! `let y := dbl x; sub2 y y` with `sub2 (dbl x) (dbl x)` (half_2), a dead
//! binding's body with the body that drops the call (half_3), and two
//! evaluation orders of the same term (half_4). Every one of those halves
//! puts the mutated reflection to the kernel DIRECTLY and requires it to
//! ACCEPT — that is the disclosure — and then requires the STRUCTURAL layer
//! (`admit_lowering`'s node-for-node comparison over `recognize_rust_call_chain`'s
//! reading, and `check_rust_call_chain`'s seal) to refuse the same mutant. The
//! once-evaluation claim is that chain of Rust code (`docs/TCB.md`, the
//! let-temp ONCE-EVALUATION row); the kernel adds nothing to it.
//!
//! What the kernel DOES catch, unchanged from `control_23`: a wrong temporary
//! (`sub2 x x` for `sub2 y y`, half_6), a swapped argument (half_5), a wrong
//! callee, a wrong literal — congruence on stuck `Opaque` heads.
//!
//! # SEMANTICS BEING EMITTED (Trust's definition, not Lean fidelity)
//!
//! Every `let` on the top-level spine whose value is a Rust call is evaluated
//! exactly once, in binding order, before the body, whether read 0, 1 or n
//! times; a dead binding whose callee panics PANICS; arguments evaluate
//! left-to-right. Lean's compiler DCEs dead lets and gives no order for pure
//! code; this is Trust's strict reading and the TCB row says so.
//!
//! # DO NOT "FIX" A FAILURE HERE BY EDITING SIDE B'S PRODUCERS
//!
//! `trust_types::admissible_body::recognize_rust_call_chain` and
//! `trust_clean_origin::reflect_rust_call` are frozen against this lane. If a
//! mutated chain ever passes, the defect is in the emitter, the seal or the
//! gate — never in this fixture.

#![allow(non_snake_case)]

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::{Environment, Name, TypeChecker};
use trust_certify::clean_island::{CleanIslandSession, RustCallee};
use trust_clean_origin::RustCallArg::{Literal, Node, Param};
use trust_clean_origin::materialize::{
    BodyTemplate, TemplateCallee, TemplateOperand, TemplateTerminator, TemplateTy, TemplateUnwind,
};
use trust_clean_origin::{
    CleanOriginPlan, CleanOriginShape, EmitRefusal, GateRefusal, RustCallLiteral, RustCallNode,
    RustCalleeRef, admit_lowering, body_template, check_faithful, check_rust_call_chain_for,
    plan_clean_origin_body, plan_clean_origin_body_with_rust_callees, reflect_rust_call_chain, row,
};
use trust_types::admissible_body::{
    ArithBinOp, ArithExpr, ArithOperand, RustCallChainArg, RustCallChainBody, RustCallChainNode,
    recognize_admissible_body, recognize_rust_call_chain,
};
use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, SourceSpan, Terminator, Ty,
    UnwindEdge, VerifiableBody, VerifiableFunction,
};

// ───────────────────────────── the callees ────────────────────────────────

const DBL: &str = "main::dbl";
const INC: &str = "main::inc";
const H: &str = "main::h";
const SUB2: &str = "main::sub2";

fn declared() -> Vec<RustCallee> {
    vec![
        RustCallee { clean_name: "dbl".into(), params: vec![Ty::u64()], result: Ty::u64() },
        RustCallee { clean_name: "inc".into(), params: vec![Ty::u64()], result: Ty::u64() },
        RustCallee { clean_name: "h".into(), params: vec![Ty::u64()], result: Ty::u64() },
        RustCallee {
            clean_name: "sub2".into(),
            params: vec![Ty::u64(), Ty::u64()],
            result: Ty::u64(),
        },
    ]
}

/// Callee indices into `declared()` / `table()`.
const C_DBL: usize = 0;
const C_INC: usize = 1;
const C_H: usize = 2;
const C_SUB2: usize = 3;

fn table() -> Vec<RustCalleeRef> {
    declared()
        .into_iter()
        .map(|callee| RustCalleeRef {
            def_path: format!("main::{}", callee.clean_name),
            clean_name: callee.clean_name,
            params: callee.params,
            result: callee.result,
        })
        .collect()
}

/// The mint-seam table: the SAME callees with NO rendering.
fn mint_table() -> Vec<RustCalleeRef> {
    table().into_iter().map(|c| RustCalleeRef { def_path: String::new(), ..c }).collect()
}

fn real_env(island: &str) -> Environment {
    let mut session = CleanIslandSession::new();
    session.declare_rust_callees(&declared()).expect("the callees declare");
    let batch = session.check_all(&[island]);
    assert!(
        !batch.is_rejected(),
        "side A must elaborate: {:?}",
        batch.outcomes.iter().map(|o| &o.errors).collect::<Vec<_>>()
    );
    session.environment().expect("an untainted session has an environment").clone()
}

/// Every fixture kernel-checks; the refusals below are all PLAN-time.
const ISLAND: &str = "\
def dup (x : UInt64) : UInt64 := let y := dbl x; sub2 y y
def once (x : UInt64) : UInt64 := let y := dbl x; sub2 y x
def nested (x : UInt64) : UInt64 := let a := dbl x; let b := dbl a; sub2 b a
def chainVal (x : UInt64) : UInt64 := let y := inc (dbl x); sub2 y y
def dead (x : UInt64) : UInt64 := let y := dbl x; sub2 x x
def ordered (x : UInt64) : UInt64 := let y := dbl x; sub2 (h x) y
def tailLet (x : UInt64) : UInt64 := let y := dbl x; y
def pureLet (x : UInt64) : UInt64 := let y := x; dbl y
def identityMid (x : UInt64) : UInt64 := let a := dbl x; let b := sub2 a a; b
def tempAlias (x : UInt64) : UInt64 := let a := dbl x; let b := a; sub2 b b
def opIdentity (x : UInt64) : UInt64 := sub2 (let y := dbl x; y) x
def pureSq (x : UInt64) : UInt64 := let y := x + 1; y * y
def retParam (x : UInt64) : UInt64 := let y := dbl x; x
def retLit (x : UInt64) : UInt64 := let y := dbl x; 5
def retArith (x : UInt64) : UInt64 := let y := dbl x; y + 1
def retEarlier (x : UInt64) : UInt64 := let y := dbl x; let z := dbl y; y
def opLet (x : UInt64) : UInt64 := sub2 (let y := dbl x; sub2 y y) x
def idUInt (a : UInt64) : UInt64 := a
def helperVal (x : UInt64) : UInt64 := let y := idUInt (dbl x); sub2 y y
def nestedVal (x : UInt64) : UInt64 := let y := (let z := dbl x; sub2 z z); sub2 y y
def aliasLast (x : UInt64) : UInt64 := let y := dbl x; let z := y; z
def aliasChain (x : UInt64) : UInt64 := let y := dbl x; let z := y; let w := z; w
def aliasLastDead (x : UInt64) : UInt64 := let y := dbl x; let z := h x; let w := z; w
def aliasLastNested (x : UInt64) : UInt64 := let a := dbl x; let b := sub2 a a; let c := b; c
def aliasLastVal (x : UInt64) : UInt64 := let y := inc (dbl x); let z := y; z
def aliasEarlier (x : UInt64) : UInt64 := let y := dbl x; let z := dbl y; let w := y; w
def chainMid (x : UInt64) : UInt64 := let y := dbl x; let z := inc (sub2 y y); sub2 z z
def ordered2 (x : UInt64) : UInt64 := let y := dbl x; let z := dbl y; sub2 (h x) z
def deepVal (x : UInt64) : UInt64 := let y := inc (sub2 (dbl x) (h x)); sub2 y y
";

/// `def selfdbl{L} (x) := let a0 := dbl x; let a1 := sub2 a0 a0; …; let
/// a{L-1} := sub2 a{L-2} a{L-2}; sub2 a{L-1} a{L-1}` — `L` lets, `L+1` nodes,
/// and a reflected side B of `2^(L+1) - 1` applications (every temporary
/// inlined per use). At `L = 11` that is 4095, the last value under the
/// 4096-node unfold rail; at `L = 12` it is 8191.
fn self_doubling(lets: usize) -> String {
    let mut source = format!("def selfdbl{lets} (x : UInt64) : UInt64 := let a0 := dbl x");
    for i in 1..lets {
        source.push_str(&format!("; let a{i} := sub2 a{} a{}", i - 1, i - 1));
    }
    source.push_str(&format!("; sub2 a{} a{}\n", lets - 1, lets - 1));
    source
}

fn plan(env: &Environment, name: &str) -> CleanOriginPlan {
    plan_clean_origin_body_with_rust_callees(env, name, &table())
        .unwrap_or_else(|refusal| panic!("`{name}` must plan: {}", refusal.note()))
}

fn plan_refusal(env: &Environment, name: &str) -> EmitRefusal {
    plan_clean_origin_body_with_rust_callees(env, name, &table())
        .err()
        .unwrap_or_else(|| panic!("`{name}` must be REFUSED at plan time"))
}

fn node(
    callee: usize,
    args: Vec<trust_clean_origin::RustCallArg>,
    let_binding: Option<usize>,
) -> RustCallNode {
    RustCallNode { callee, args, let_binding }
}

fn chain(nodes: Vec<RustCallNode>) -> CleanOriginShape {
    CleanOriginShape::RustCallChain { nodes }
}

// ─────────────── the emitter's chain, as extracted, and mutants ───────────────

fn locals(tys: &[Ty]) -> Vec<LocalDecl> {
    tys.iter()
        .enumerate()
        .map(|(index, ty)| LocalDecl { index, ty: ty.clone(), name: None })
        .collect()
}

fn u64_locals(n: usize) -> Vec<LocalDecl> {
    locals(&vec![Ty::u64(); n])
}

fn emitted_chain(
    name: &str,
    arg_count: usize,
    locals: Vec<LocalDecl>,
    calls: Vec<(&str, Vec<Operand>, Place)>,
) -> VerifiableFunction {
    let n = calls.len();
    let mut blocks: Vec<BasicBlock> = calls
        .into_iter()
        .enumerate()
        .map(|(k, (callee, args, dest))| BasicBlock {
            id: BlockId(k),
            stmts: Vec::new(),
            terminator: Terminator::Call {
                func: callee.into(),
                args,
                dest,
                target: Some(BlockId(k + 1)),
                span: SourceSpan::default(),
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                callee_identity: None,
                callee_key: None,
                unwind: UnwindEdge::Continue,
            },
        })
        .collect();
    blocks.push(BasicBlock { id: BlockId(n), stmts: Vec::new(), terminator: Terminator::Return });
    let return_ty = locals[0].ty.clone();
    VerifiableFunction {
        name: name.into(),
        def_path: format!("main::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count,
            return_ty,
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn copy_local(i: usize) -> Operand {
    Operand::Copy(Place::local(i))
}

/// `_2 = dbl(_1); _0 = sub2(copy _2, copy _2); return` — the faithful r24 DAG.
fn faithful_dup() -> VerifiableFunction {
    emitted_chain(
        "dup",
        1,
        u64_locals(3),
        vec![
            (DBL, vec![copy_local(1)], Place::local(2)),
            (SUB2, vec![copy_local(2), copy_local(2)], Place::local(0)),
        ],
    )
}

/// `_2 = dbl(_1); _0 = sub2(_1, _1); return` — the dead binding: a written,
/// unread temporary whose `Call` still executes.
fn faithful_dead() -> VerifiableFunction {
    emitted_chain(
        "dead",
        1,
        u64_locals(3),
        vec![
            (DBL, vec![copy_local(1)], Place::local(2)),
            (SUB2, vec![copy_local(1), copy_local(1)], Place::local(0)),
        ],
    )
}

fn allowed() -> BTreeSet<String> {
    table().into_iter().map(|c| c.def_path).collect()
}

fn names_of_paths() -> BTreeMap<String, String> {
    table().into_iter().map(|c| (c.def_path, c.clean_name)).collect()
}

fn u64_carrier() -> trust_clean_carrier::Carrier {
    trust_clean_carrier::carrier_at(
        &clean_kernel::Expr::const_(Name::from_string("UInt64"), vec![]),
        &Ty::u64(),
    )
    .expect("UInt64 -> u64 is the exact-width carrier")
}

fn b_node(callee: &str, args: Vec<RustCallChainArg>) -> RustCallChainNode {
    RustCallChainNode { callee: callee.to_owned(), args }
}

/// Reflect a hand-built RECOGNISED chain directly — the kernel half of a
/// mutation, bypassing the structural check on purpose so the KERNEL's own
/// verdict is measured.
fn reflect(
    env: &Environment,
    name: &str,
    body: &RustCallChainBody,
    extracted: &VerifiableFunction,
) -> clean_kernel::Expr {
    reflect_rust_call_chain(env, name, body, extracted, &names_of_paths())
        .unwrap_or_else(|e| panic!("the chain must reflect: {e}"))
}

/// The kernel's verdict ALONE on the emitted body `extracted`, read back by
/// side B's own recognizer and reflected — no structural comparison.
fn kernel_alone(
    env: &Environment,
    name: &str,
    extracted: &VerifiableFunction,
) -> Result<(), GateRefusal> {
    let recognised = recognize_rust_call_chain(extracted, &allowed())
        .unwrap_or_else(|| panic!("side B must read the emitted chain for `{name}`"));
    let side_b = reflect(env, name, &recognised, extracted);
    check_faithful(env, name, &side_b, &u64_carrier()).map(|_| ())
}

// ──────────────────── the shipped materializer, rendered ────────────────────

/// `control_11`'s test-side renderer, restricted to what a Rust-call chain
/// template can hold (calls and a return; no statements).
fn render_chain_template(template: &BodyTemplate, plan: &CleanOriginPlan) -> VerifiableFunction {
    let callees = plan.callees();
    let local_ty = |ty: TemplateTy| match ty {
        TemplateTy::Result => plan.return_ty().clone(),
        TemplateTy::Param { index } => plan.param_tys()[index].clone(),
        TemplateTy::RustCalleeResult { index } => callees[index].result.clone(),
        other => panic!("a Rust-call chain template holds no {other:?} local"),
    };
    let operand = |op: TemplateOperand| match op {
        TemplateOperand::Copy(local) => Operand::Copy(Place::local(local)),
        TemplateOperand::UIntScalar { value, width } => {
            Operand::Constant(ConstValue::Uint(value, width))
        }
        TemplateOperand::BoolScalar(value) => Operand::Constant(ConstValue::Bool(value)),
        other => panic!("a Rust-call chain template passes no {other:?} operand"),
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
        .map(|(index, block)| {
            assert!(block.stmts.is_empty(), "a Rust-call chain template has no statements");
            BasicBlock {
                id: BlockId(index),
                stmts: Vec::new(),
                terminator: match &block.terminator {
                    TemplateTerminator::Return => Terminator::Return,
                    TemplateTerminator::Call { callee, args, dest, target, unwind } => {
                        Terminator::Call {
                            func: match callee {
                                TemplateCallee::RustFn { index } => {
                                    callees[*index].def_path.clone()
                                }
                                other => panic!("a Rust-call chain calls no {other:?}"),
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
                    other => panic!("a Rust-call chain template ends no block with {other:?}"),
                },
            }
        })
        .collect();
    VerifiableFunction {
        name: plan.name().into(),
        def_path: format!("main::{}", plan.name()),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: template.arg_count,
            return_ty: plan.return_ty().clone(),
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// The body the shipped materializer templates for `plan`, rendered.
fn materialized(plan: &CleanOriginPlan) -> VerifiableFunction {
    let selected = row("rust.call").expect("the W5 row");
    let template = body_template(selected, plan)
        .unwrap_or_else(|refusal| panic!("`{}` must template: {refusal:?}", plan.name()));
    render_chain_template(&template, plan)
}

/// `control_11`'s comparison: identity on the pretty-printed structure.
fn body_picture(func: &VerifiableFunction) -> String {
    format!(
        "name = {}\ndef_path = {}\narg_count = {}\nreturn_ty = {:?}\nlocals = {:#?}\n\
         blocks = {:#?}\n",
        func.name,
        func.def_path,
        func.body.arg_count,
        func.body.return_ty,
        func.body.locals,
        func.body.blocks,
    )
}

// ════════════════════ §8 MEASURE-FIRST EXPERIMENTS ═══════════════════════
//
// The plan of record rests on these two; they ran before anything else in
// this file was written.

#[test]
fn exp_1_side_b_reads_the_dag_a_shared_temp_and_a_dead_temp() {
    // `recognize_rust_call_chain` records a temporary in its env at its
    // writer and lets ANY later block read it any number of times, under
    // single assignment — nothing checks that a temp is read at all.
    assert_eq!(
        recognize_rust_call_chain(&faithful_dup(), &allowed()),
        Some(RustCallChainBody {
            nodes: vec![
                b_node(DBL, vec![RustCallChainArg::Param(0)]),
                b_node(SUB2, vec![RustCallChainArg::Node(0), RustCallChainArg::Node(0)]),
            ]
        }),
        "side B must read the shared temporary as ONE node referenced twice"
    );
    assert_eq!(
        recognize_rust_call_chain(&faithful_dead(), &allowed()),
        Some(RustCallChainBody {
            nodes: vec![
                b_node(DBL, vec![RustCallChainArg::Param(0)]),
                b_node(SUB2, vec![RustCallChainArg::Param(0), RustCallChainArg::Param(0)]),
            ]
        }),
        "side B must read the dead temporary back as a node (a written, unread local)"
    );
}

#[test]
fn exp_2_the_kernel_is_blind_to_multiplicity() {
    // Side A `let y := dbl x; sub2 y y` against the DUPLICATED reflection
    // `fun x => sub2 (dbl x) (dbl x)`: zeta identifies them.
    let env = real_env(ISLAND);
    let duplicated = emitted_chain(
        "dup",
        1,
        u64_locals(4),
        vec![
            (DBL, vec![copy_local(1)], Place::local(2)),
            (DBL, vec![copy_local(1)], Place::local(3)),
            (SUB2, vec![copy_local(2), copy_local(3)], Place::local(0)),
        ],
    );
    kernel_alone(&env, "dup", &duplicated)
        .expect("the kernel identifies `let y := dbl x; sub2 y y` with `sub2 (dbl x) (dbl x)`");
    // Side A `let y := dbl x; sub2 x x` against the DROPPED reflection
    // `fun x => sub2 x x`: zeta discards the dead binding.
    let dropped = emitted_chain(
        "dead",
        1,
        u64_locals(2),
        vec![(SUB2, vec![copy_local(1), copy_local(1)], Place::local(0))],
    );
    kernel_alone(&env, "dead", &dropped)
        .expect("the kernel identifies `let y := dbl x; sub2 x x` with `sub2 x x`");
}

// ═══════════════════════════════ the halves ═══════════════════════════════

#[test]
fn half_0_the_plan_reads_every_let_spine_shape_exactly() {
    let env = real_env(ISLAND);
    let cases: Vec<(&str, CleanOriginShape)> = vec![
        (
            "dup",
            chain(vec![
                node(C_DBL, vec![Param(0)], Some(0)),
                node(C_SUB2, vec![Node(0), Node(0)], None),
            ]),
        ),
        (
            "once",
            chain(vec![
                node(C_DBL, vec![Param(0)], Some(0)),
                node(C_SUB2, vec![Node(0), Param(0)], None),
            ]),
        ),
        (
            "nested",
            chain(vec![
                node(C_DBL, vec![Param(0)], Some(0)),
                node(C_DBL, vec![Node(0)], Some(1)),
                node(C_SUB2, vec![Node(1), Node(0)], None),
            ]),
        ),
        (
            "chainVal",
            chain(vec![
                node(C_DBL, vec![Param(0)], None),
                node(C_INC, vec![Node(0)], Some(0)),
                node(C_SUB2, vec![Node(1), Node(1)], None),
            ]),
        ),
        (
            "dead",
            chain(vec![
                node(C_DBL, vec![Param(0)], Some(0)),
                node(C_SUB2, vec![Param(0), Param(0)], None),
            ]),
        ),
        (
            "ordered",
            chain(vec![
                node(C_DBL, vec![Param(0)], Some(0)),
                node(C_H, vec![Param(0)], None),
                node(C_SUB2, vec![Node(1), Node(0)], None),
            ]),
        ),
        // An identity `let` AFTER a Rust `let` is zeta'd; the bound call is
        // the root (`identityMid`), and a `let` that merely re-names a
        // temporary is pure and zeta'd (`tempAlias`).
        (
            "identityMid",
            chain(vec![
                node(C_DBL, vec![Param(0)], Some(0)),
                node(C_SUB2, vec![Node(0), Node(0)], None),
            ]),
        ),
        (
            "tempAlias",
            chain(vec![
                node(C_DBL, vec![Param(0)], Some(0)),
                node(C_SUB2, vec![Node(0), Node(0)], None),
            ]),
        ),
        // Ordinary nodes BELOW the last `let`-bound node, each a binding's
        // VALUE (review finding N3, the shapes the seal must keep admitting):
        // a value reading an earlier temporary (`chainMid`), a body call
        // minted after the last binding (`ordered2`), and two value nodes at
        // depth 2 under the binding (`deepVal`).
        (
            "chainMid",
            chain(vec![
                node(C_DBL, vec![Param(0)], Some(0)),
                node(C_SUB2, vec![Node(0), Node(0)], None),
                node(C_INC, vec![Node(1)], Some(1)),
                node(C_SUB2, vec![Node(2), Node(2)], None),
            ]),
        ),
        (
            "ordered2",
            chain(vec![
                node(C_DBL, vec![Param(0)], Some(0)),
                node(C_DBL, vec![Node(0)], Some(1)),
                node(C_H, vec![Param(0)], None),
                node(C_SUB2, vec![Node(2), Node(1)], None),
            ]),
        ),
        (
            "deepVal",
            chain(vec![
                node(C_DBL, vec![Param(0)], None),
                node(C_H, vec![Param(0)], None),
                node(C_SUB2, vec![Node(0), Node(1)], None),
                node(C_INC, vec![Node(2)], Some(0)),
                node(C_SUB2, vec![Node(3), Node(3)], None),
            ]),
        ),
    ];
    for (name, expected) in cases {
        let plan = plan(&env, name);
        assert_eq!(plan.shape(), &expected, "`{name}`: binding order, then the body's post-order");
        assert_eq!(plan.callees(), table().as_slice());
    }
}

#[test]
fn half_1_the_gate_admits_the_faithful_dag_and_the_materializer_emits_exactly_it() {
    let env = real_env(ISLAND);

    // The hand-built expectation admits…
    let dup = plan(&env, "dup");
    let admitted = admit_lowering(&env, &dup, &faithful_dup())
        .expect("one `dbl`, its result copied twice into `sub2`, IS `let y := dbl x; sub2 y y`");
    assert_eq!(admitted.name(), "dup");
    assert_eq!(admitted.admitted_at(), &Ty::u64());
    // …and the shipped materializer templates EXACTLY that body (control_11
    // discipline: byte identity on the printed structure).
    assert_eq!(
        body_picture(&materialized(&dup)),
        body_picture(&faithful_dup()),
        "the template does not describe the body this control expects; a materializer that \
         emits subtly different MIR is the wrong-binary failure the gate exists to catch"
    );

    // The dead binding: TWO `Call` blocks, the temporary written and never
    // read — the call is evaluated, never dropped.
    let dead = plan(&env, "dead");
    admit_lowering(&env, &dead, &faithful_dead()).expect("the dead binding's chain admits");
    let template = body_template(row("rust.call").unwrap(), &dead).expect("templates");
    assert_eq!(template.calls().len(), 2, "a dead binding is still a `Call`");
    assert_eq!(body_picture(&materialized(&dead)), body_picture(&faithful_dead()));

    // And every other let-spine shape the materializer templates admits.
    for name in [
        "once",
        "nested",
        "chainVal",
        "ordered",
        "identityMid",
        "tempAlias",
        "chainMid",
        "ordered2",
        "deepVal",
    ] {
        let plan = plan(&env, name);
        admit_lowering(&env, &plan, &materialized(&plan)).unwrap_or_else(|refusal| {
            panic!("`{name}`'s materialized body must admit: {refusal:?}")
        });
    }
}

#[test]
fn half_2_a_DUPLICATED_evaluation_is_refused_structurally_and_the_kernel_is_blind() {
    // `_2 = dbl(_1); _3 = dbl(_1); _0 = sub2(_2, _3)` for `let y := dbl x;
    // sub2 y y`: the call evaluated TWICE. Same value; a different program.
    let env = real_env(ISLAND);
    let dup = plan(&env, "dup");
    let duplicated = emitted_chain(
        "dup",
        1,
        u64_locals(4),
        vec![
            (DBL, vec![copy_local(1)], Place::local(2)),
            (DBL, vec![copy_local(1)], Place::local(3)),
            (SUB2, vec![copy_local(2), copy_local(3)], Place::local(0)),
        ],
    );
    let refusal = admit_lowering(&env, &dup, &duplicated).expect_err(
        "THE ONCE-EVALUATION CLAIM IS DECORATION IF THIS PASSES: two `dbl` calls were \
         accepted for a `let` that binds one",
    );
    assert!(refusal.is_compiler_defect(), "got {refusal:?}");
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");
    assert!(refusal.note().contains("3 call(s) emitted for 2 planned"), "got {}", refusal.note());
    // THE DISCLOSURE: the kernel alone accepts the duplicated body.
    kernel_alone(&env, "dup", &duplicated).expect(
        "zeta identifies the once-body with the duplicated body; only the structure refuses",
    );
}

#[test]
fn half_3_a_DROPPED_dead_binding_is_refused_structurally_and_the_kernel_is_blind() {
    // `_0 = sub2(_1, _1)` for `let y := dbl x; sub2 x x`: the dead call
    // dropped. Lean's compiler would do exactly this; Trust's definition does
    // not.
    let env = real_env(ISLAND);
    let dead = plan(&env, "dead");
    let dropped = emitted_chain(
        "dead",
        1,
        u64_locals(2),
        vec![(SUB2, vec![copy_local(1), copy_local(1)], Place::local(0))],
    );
    let refusal = admit_lowering(&env, &dead, &dropped)
        .expect_err("a dropped `let`-bound call must refuse: the binding IS evaluated");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");
    assert!(refusal.note().contains("1 call(s) emitted for 2 planned"), "got {}", refusal.note());
    kernel_alone(&env, "dead", &dropped)
        .expect("zeta drops the dead binding; only the structure refuses");
}

#[test]
fn half_4_a_REORDERED_evaluation_is_refused_structurally_and_the_kernel_is_blind() {
    // `ordered := let y := dbl x; sub2 (h x) y`: `dbl` is bound first, so it
    // is evaluated first. The mutant evaluates `h` first.
    let env = real_env(ISLAND);
    let ordered = plan(&env, "ordered");
    let reordered = emitted_chain(
        "ordered",
        1,
        u64_locals(4),
        vec![
            (H, vec![copy_local(1)], Place::local(2)),
            (DBL, vec![copy_local(1)], Place::local(3)),
            (SUB2, vec![copy_local(2), copy_local(3)], Place::local(0)),
        ],
    );
    let refusal = admit_lowering(&env, &ordered, &reordered)
        .expect_err("binding order is evaluation order; a reordered chain must refuse");
    assert!(refusal.is_compiler_defect());
    let note = refusal.note();
    assert!(
        note.contains("node 0 calls `main::h` where the plan calls `main::dbl`"),
        "the refusal must name node 0's callee mismatch: {note}"
    );
    kernel_alone(&env, "ordered", &reordered)
        .expect("the kernel sees no order; only the structure refuses");
    // The faithful order admits, so the refusal above is about ORDER alone.
    admit_lowering(&env, &ordered, &materialized(&ordered)).expect("binding order admits");
}

#[test]
fn half_5_a_SWAPPED_argument_is_refused_by_both_layers() {
    // `sub2(_1, _2)` for `once := let y := dbl x; sub2 y x`.
    let env = real_env(ISLAND);
    let once = plan(&env, "once");
    let swapped = emitted_chain(
        "once",
        1,
        u64_locals(3),
        vec![
            (DBL, vec![copy_local(1)], Place::local(2)),
            (SUB2, vec![copy_local(1), copy_local(2)], Place::local(0)),
        ],
    );
    let refusal = admit_lowering(&env, &once, &swapped).expect_err("`sub2 x y` for `sub2 y x`");
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");
    let refusal = kernel_alone(&env, "once", &swapped)
        .expect_err("the kernel separates `sub2 x (dbl x)` from `sub2 (dbl x) x` by congruence");
    assert!(matches!(refusal, GateRefusal::Disagreement { .. }), "got {refusal:?}");
}

#[test]
fn half_6_a_WRONG_temporary_is_refused_by_both_layers() {
    // `sub2(_1, _1)` for `dup := let y := dbl x; sub2 y y`: the call made,
    // its result ignored, the parameter passed instead.
    let env = real_env(ISLAND);
    let dup = plan(&env, "dup");
    let wrong_temp = emitted_chain(
        "dup",
        1,
        u64_locals(3),
        vec![
            (DBL, vec![copy_local(1)], Place::local(2)),
            (SUB2, vec![copy_local(1), copy_local(1)], Place::local(0)),
        ],
    );
    let refusal = admit_lowering(&env, &dup, &wrong_temp).expect_err("`sub2 x x` for `sub2 y y`");
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");
    let refusal = kernel_alone(&env, "dup", &wrong_temp)
        .expect_err("the kernel separates `sub2 x x` from `sub2 (dbl x) (dbl x)`");
    assert!(matches!(refusal, GateRefusal::Disagreement { .. }), "got {refusal:?}");
}

#[test]
fn half_7_E6_STAYS_BLIND_the_dag_reads_back_as_none_from_every_other_entry_point() {
    for body in [faithful_dup(), faithful_dead()] {
        assert!(
            recognize_admissible_body(&body).is_none(),
            "the Rust-call DAG has joined `recognize_admissible_body`'s chain: E6 would import a \
             call to a user `fn` as a defining equation"
        );
        assert!(
            recognize_rust_call_chain(&body, &BTreeSet::new()).is_none(),
            "no allow-list, no reading"
        );
        assert!(recognize_rust_call_chain(&body, &allowed()).is_some());
    }
}

#[test]
fn half_8_the_mint_seam_plans_the_same_dag_and_never_reaches_side_b() {
    let env = real_env(ISLAND);
    for name in ["dup", "dead", "nested"] {
        let mint_plan = plan_clean_origin_body_with_rust_callees(&env, name, &mint_table())
            .unwrap_or_else(|refusal| panic!("the mint seam must plan `{name}`: {refusal:?}"));
        assert_eq!(mint_plan.shape(), plan(&env, name).shape(), "`{name}`: one walk, two callers");
        let refusal = admit_lowering(&env, &mint_plan, &materialized(&mint_plan))
            .expect_err("a plan built at the mint seam must not reach the kernel gate");
        assert!(matches!(refusal, EmitRefusal::ReflectionRejected { .. }), "got {refusal:?}");
        assert!(refusal.note().contains("no `DefId` rendering"), "got {}", refusal.note());
    }
    // …and the NO-CALLEE entry still refuses the let-spine body outright.
    let refusal = plan_clean_origin_body(&env, "dup").expect_err("no table, no callee head");
    assert!(!refusal.is_compiler_defect());
}

#[test]
fn half_9_the_seal_rechecks_the_dag() {
    let env = real_env(ISLAND);
    let seal = |name: &str, nodes: Vec<RustCallNode>| {
        check_rust_call_chain_for(&env, name, &nodes, &table())
    };

    // The control: the planner's own vectors re-seal — including every shape
    // with an ordinary node below the last `let`-bound node (`chainVal`,
    // `chainMid`, `ordered2`, `deepVal`), which rule (h) must keep admitting.
    for name in ["dup", "dead", "nested", "chainVal", "ordered", "chainMid", "ordered2", "deepVal"]
    {
        let CleanOriginShape::RustCallChain { nodes } = plan(&env, name).shape().clone() else {
            unreachable!()
        };
        seal(name, nodes).unwrap_or_else(|refusal| panic!("`{name}` re-seals: {refusal:?}"));
    }

    // (a) a node read twice WITHOUT its `let` marker: the plain rule.
    let refusal = seal(
        "dup",
        vec![node(C_DBL, vec![Param(0)], None), node(C_SUB2, vec![Node(0), Node(0)], None)],
    )
    .expect_err("an ordinary node is read exactly once");
    assert!(matches!(refusal, EmitRefusal::NotEmittable { .. }), "got {refusal:?}");
    assert!(refusal.note().contains("read 2 time(s)"), "got {}", refusal.note());

    // (b) ordinals out of binding order.
    let refusal = seal(
        "nested",
        vec![
            node(C_DBL, vec![Param(0)], Some(1)),
            node(C_DBL, vec![Node(0)], Some(0)),
            node(C_SUB2, vec![Node(1), Node(0)], None),
        ],
    )
    .expect_err("binding order is evaluation order");
    assert!(matches!(refusal, EmitRefusal::LetSpine { defect: true, .. }), "got {refusal:?}");
    assert!(refusal.is_compiler_defect());
    assert!(refusal.note().contains("binding order"), "got {}", refusal.note());

    // (c) a forward reference.
    let refusal = seal(
        "nested",
        vec![
            node(C_DBL, vec![Node(1)], Some(0)),
            node(C_DBL, vec![Param(0)], Some(1)),
            node(C_SUB2, vec![Node(1), Node(0)], None),
        ],
    )
    .expect_err("a node reads only EARLIER nodes");
    assert!(refusal.note().contains("not an EARLIER node"), "got {}", refusal.note());

    // (d) the root marked as `let`-bound.
    let refusal = seal(
        "dup",
        vec![node(C_DBL, vec![Param(0)], Some(0)), node(C_SUB2, vec![Node(0), Node(0)], Some(1))],
    )
    .expect_err("the root is never a binding");
    assert!(matches!(refusal, EmitRefusal::LetSpine { defect: true, .. }), "got {refusal:?}");

    // (e) 33 nodes.
    let mut many: Vec<RustCallNode> =
        (0..32).map(|k| node(C_DBL, vec![Param(0)], Some(k))).collect();
    many.push(node(C_DBL, vec![Param(0)], None));
    let refusal = seal("dup", many).expect_err("past the node cap");
    assert!(refusal.note().contains("outside the measured"), "got {}", refusal.note());

    // (f) THE CROSS-CHECK, both directions: 3 nodes for a body with 2 callee
    // applications (a walk that minted two nodes for one `let`)…
    let refusal = seal(
        "dup",
        vec![
            node(C_DBL, vec![Param(0)], Some(0)),
            node(C_DBL, vec![Param(0)], Some(1)),
            node(C_SUB2, vec![Node(0), Node(1)], None),
        ],
    )
    .expect_err("the kernel-stored body applies a callee twice; three nodes is a planner defect");
    assert!(matches!(refusal, EmitRefusal::LetSpine { defect: true, .. }), "got {refusal:?}");
    assert!(refusal.note().contains("applies a Rust callee 2 time(s)"), "got {}", refusal.note());
    // …and 2 nodes for a body with 3 (a walk that dropped one).
    let refusal = seal(
        "nested",
        vec![node(C_DBL, vec![Param(0)], Some(0)), node(C_SUB2, vec![Node(0), Node(0)], None)],
    )
    .expect_err(
        "the kernel-stored body applies a callee three times; two nodes is a planner defect",
    );
    assert!(matches!(refusal, EmitRefusal::LetSpine { defect: true, .. }), "got {refusal:?}");

    // (h) BINDING ORDER OVER BODY NODES (review finding N3, 2026-09-16). The
    // walk mints `ordered := let y := dbl x; sub2 (h x) y` as `[dbl let=0, h,
    // sub2(N1, N0)]`; the hand-built `[h, dbl let=0, sub2(N0, N1)]` evaluates
    // the body call `h x` BEFORE the binding, and every OTHER rule passes it
    // (`h` read once, ordinal 0, root read never, 3 == 3 against the source)
    // — it sealed at 33e1982913d. The walk cannot mint it; the seal must
    // still refuse it.
    let refusal = seal(
        "ordered",
        vec![
            node(C_H, vec![Param(0)], None),
            node(C_DBL, vec![Param(0)], Some(0)),
            node(C_SUB2, vec![Node(0), Node(1)], None),
        ],
    )
    .expect_err(
        "a body-only node below the last `let`-bound node is a reordering the seal must refuse",
    );
    assert!(matches!(refusal, EmitRefusal::LetSpine { defect: true, .. }), "got {refusal:?}");
    assert!(refusal.is_compiler_defect());
    let note = refusal.note();
    assert!(
        note.contains("node 0 is an ordinary body call placed before node 1")
            && note.contains("binding order"),
        "got {note}"
    );
    // The same BETWEEN two bindings, with the count intact (4 == 4): the walk
    // mints `ordered2` as `[dbl let=0, dbl(N0) let=1, h, sub2(N2, N1)]`.
    let refusal = seal(
        "ordered2",
        vec![
            node(C_DBL, vec![Param(0)], Some(0)),
            node(C_H, vec![Param(0)], None),
            node(C_DBL, vec![Node(0)], Some(1)),
            node(C_SUB2, vec![Node(2), Node(1)], None),
        ],
    )
    .expect_err("a body call placed between two bindings");
    assert!(matches!(refusal, EmitRefusal::LetSpine { defect: true, .. }), "got {refusal:?}");
    assert!(
        refusal.note().contains("node 1 is an ordinary body call placed before node 2"),
        "got {}",
        refusal.note()
    );
    // …but NOT a body call that merely READS an earlier value node: a value
    // node is covered by its binding, not by who else reads it. Hand-built
    // over `deepVal` (`let y := inc (sub2 (dbl x) (h x)); sub2 y y`): the
    // walk's own vector, re-sealed — its two depth-2 value nodes sit below
    // the binding and pass by the transitive rule.
    seal(
        "deepVal",
        vec![
            node(C_DBL, vec![Param(0)], None),
            node(C_H, vec![Param(0)], None),
            node(C_SUB2, vec![Node(0), Node(1)], None),
            node(C_INC, vec![Node(2)], Some(0)),
            node(C_SUB2, vec![Node(3), Node(3)], None),
        ],
    )
    .unwrap_or_else(|refusal| {
        panic!("value nodes at depth 2 under a binding re-seal: {refusal:?}")
    });

    // (g) THE UNFOLD RAIL at the measured boundary: 11 self-doubling lets
    // (4095 unfolded applications) plan; 12 (8191) refuse with the fix.
    let env = real_env(&format!("{}{}", self_doubling(11), self_doubling(12)));
    let plan = plan(&env, "selfdbl11");
    let CleanOriginShape::RustCallChain { nodes } = plan.shape() else { unreachable!() };
    assert_eq!(nodes.len(), 12);
    assert_eq!(nodes.iter().filter(|n| n.let_binding.is_some()).count(), 11);
    let refusal = plan_refusal(&env, "selfdbl12");
    assert!(matches!(refusal, EmitRefusal::LetSpine { defect: false, .. }), "got {refusal:?}");
    assert!(!refusal.is_compiler_defect());
    let note = refusal.note();
    assert!(note.contains("8191") && note.contains("split the chain"), "got {note}");
}

#[test]
fn half_10_PURE_lets_stay_on_the_zeta_path() {
    let env = real_env(ISLAND);
    // `let y := x + 1; y * y` is control_24 half_1's `Composed`, exactly.
    let add = ArithExpr::Bin {
        op: ArithBinOp::Add,
        left: Box::new(ArithExpr::Operand(ArithOperand::Param(0))),
        right: Box::new(ArithExpr::Operand(ArithOperand::Const(1))),
    };
    assert_eq!(
        plan(&env, "pureSq").shape(),
        &CleanOriginShape::Composed {
            expr: ArithExpr::Bin {
                op: ArithBinOp::Mul,
                left: Box::new(add.clone()),
                right: Box::new(add)
            }
        }
    );
    // A pure `let` before a call and a tail `let` of a call are each ONE
    // ordinary node — today's behaviour, byte for byte.
    for name in ["pureLet", "tailLet"] {
        assert_eq!(
            plan(&env, name).shape(),
            &chain(vec![node(C_DBL, vec![Param(0)], None)]),
            "{name}"
        );
    }
    // An identity `let` in OPERAND position is admitted as two ordinary
    // nodes (today's behaviour).
    assert_eq!(
        plan(&env, "opIdentity").shape(),
        &chain(vec![
            node(C_DBL, vec![Param(0)], None),
            node(C_SUB2, vec![Node(0), Param(0)], None)
        ])
    );
}

#[test]
fn half_11_every_refusal_carries_the_fix() {
    let env = real_env(ISLAND);
    // (name, phrases the note must carry)
    let cases: [(&str, &[&str]); 8] = [
        ("retParam", &["`y`", "never used", "drop a binding"]),
        ("retLit", &["`y`", "never used"]),
        ("retArith", &["an application (`", "not an application of a Rust callee", "Rust `fn`"]),
        ("retEarlier", &["`y`", "`z`", "never used", "reorder"]),
        ("aliasEarlier", &["`y`", "bound after it by `z`", "never used", "reorder"]),
        ("opLet", &["hoist"]),
        ("helperVal", &["`y`", "value temporary", "Rust `fn`"]),
        ("nestedVal", &["`y`", "hoist"]),
    ];
    for (name, phrases) in cases {
        let refusal = plan_refusal(&env, name);
        assert!(!refusal.is_compiler_defect(), "`{name}` is the user's, not a defect: {refusal:?}");
        let note = refusal.note();
        assert!(note.contains("options"), "v7/D3: `{name}` carries options: {note}");
        for phrase in phrases {
            assert!(note.contains(phrase), "`{name}`'s note must carry `{phrase}`: {note}");
        }
    }
}

#[test]
fn half_12_the_let_spine_refusal_is_not_masked_by_a_fallback() {
    // Before increment 7 the planner's `?` at the expansion fallback replaced
    // every `let` refusal with the expansion's own generic text. The
    // `LetSpine` note is the one `plan_…` returns.
    let env = real_env(ISLAND);
    for name in ["retParam", "retLit", "retArith", "retEarlier"] {
        let refusal = plan_refusal(&env, name);
        assert!(
            matches!(refusal, EmitRefusal::LetSpine { defect: false, .. }),
            "`{name}`: {refusal:?}"
        );
        let note = refusal.note();
        assert!(
            !note.contains("substituting an argument that calls Rust")
                && !note.contains("work envelope")
                && note.contains("value temporary"),
            "`{name}`'s note was replaced by a fallback's: {note}"
        );
    }
}

#[test]
fn half_13_the_kernel_at_the_unfold_rail() {
    // 11 self-doubling lets: 12 nodes, a reflected side B of 4095
    // applications — the largest term this lane puts to the kernel. It must
    // ADMIT or exhaust the heartbeat envelope; it must never DISAGREE.
    //
    // MEASURED 2026-09-16 (stage1 `trustc 1.99.0-dev`, clean pin
    // `a1c2b17c0`): admits, and `is_def_eq` completes and AGREES under a
    // 1000-heartbeat limit — the kernel shares the unfolded subterms, so the
    // 4096-node rail is nowhere near its envelope and the `let`-rendering
    // follow-on (7b) is not needed for cost.
    let env = real_env(&self_doubling(11));
    let plan = plan(&env, "selfdbl11");
    let extracted = materialized(&plan);
    match admit_lowering(&env, &plan, &extracted) {
        Ok(admitted) => assert_eq!(admitted.name(), "selfdbl11"),
        Err(EmitRefusal::Gate(GateRefusal::ResourceExhausted { .. })) => {
            panic!(
                "MEASURED: the kernel exhausts its envelope inside the 4096-node rail; lower the rail"
            )
        }
        Err(other) => panic!("never a disagreement or a structural refusal at the rail: {other:?}"),
    }
    // The heartbeat COST, read by bisection on the limit (the counter itself
    // is crate-private): the smallest of these limits under which the
    // decision completes.
    let recognised = recognize_rust_call_chain(&extracted, &allowed()).expect("reads");
    let side_b = reflect(&env, "selfdbl11", &recognised, &extracted);
    let side_a = env
        .get_const(&Name::from_string("selfdbl11"))
        .and_then(|constant| constant.value.clone())
        .expect("the kernel-stored body");
    let mut completed_under = None;
    for limit in [1_000u32, 10_000, 100_000, 1_000_000, 2_000_000] {
        let mut checker = TypeChecker::new(&env);
        checker.set_heartbeat_limit(limit);
        let agrees = checker.is_def_eq(&side_a, &side_b);
        if !checker.heartbeat_spent() {
            assert!(agrees, "completed and DISAGREED at the rail");
            completed_under = Some(limit);
            break;
        }
    }
    let limit =
        completed_under.expect("the decision completes under the default two-million envelope");
    eprintln!(
        "half_13: selfdbl11 (4095 unfolded applications) decides under a {limit}-heartbeat limit"
    );
}

#[test]
fn half_14_a_literal_and_a_bool_operand_ride_the_temporary() {
    // `let y := inc 5; sub2 y y`: a literal operand under a `let`, and the
    // materialized body admits.
    let env = real_env("def litLet (x : UInt64) : UInt64 := let y := inc 5; sub2 y x\n");
    let plan = plan(&env, "litLet");
    assert_eq!(
        plan.shape(),
        &chain(vec![
            node(C_INC, vec![Literal(RustCallLiteral::UInt(5))], Some(0)),
            node(C_SUB2, vec![Node(0), Param(0)], None),
        ])
    );
    admit_lowering(&env, &plan, &materialized(&plan)).expect("admits");
}

#[test]
fn half_15_an_alias_of_the_LAST_temporary_is_the_identity_case_and_an_EARLIER_one_is_not() {
    // Review finding N2 (2026-09-16). `let y := dbl x; let z := y; z` denotes
    // exactly one call; at 33e1982913d it was refused, with an EMPTY binder
    // list rendered into the note ("bound after it by  are never used").
    // The alias is pure and zeta'd, so what remains is `let y := dbl x; y` —
    // the identity `let` — and the walk now un-marks that node and makes it
    // the root. The plan IS `tailLet`'s, and the emitted body is the one-call
    // body `_0 = dbl(_1)`.
    let env = real_env(ISLAND);
    let tail = plan(&env, "tailLet");
    for name in ["aliasLast", "aliasChain"] {
        let plan = plan(&env, name);
        assert_eq!(plan.shape(), tail.shape(), "`{name}` is the identity case");
        assert_eq!(plan.shape(), &chain(vec![node(C_DBL, vec![Param(0)], None)]), "`{name}`");
        let faithful = emitted_chain(
            name,
            1,
            u64_locals(2),
            vec![(DBL, vec![copy_local(1)], Place::local(0))],
        );
        admit_lowering(&env, &plan, &faithful).unwrap_or_else(|refusal| {
            panic!("`{name}`: one `dbl` call IS `let y := dbl x; let z := y; z`: {refusal:?}")
        });
        assert_eq!(body_picture(&materialized(&plan)), body_picture(&faithful), "`{name}`");
    }
    // The aliased binding may be the LAST of several: the earlier ones keep
    // their markers and their order (`aliasLastDead`, a dead `dbl` before an
    // aliased `h`; `aliasLastNested`, the alias of a call reading an earlier
    // temporary — `identityMid`'s plan exactly), and the aliased value may
    // itself be a chain (`aliasLastVal`). Each materializes and admits.
    let cases: Vec<(&str, CleanOriginShape)> = vec![
        (
            "aliasLastDead",
            chain(vec![node(C_DBL, vec![Param(0)], Some(0)), node(C_H, vec![Param(0)], None)]),
        ),
        ("aliasLastNested", plan(&env, "identityMid").shape().clone()),
        (
            "aliasLastVal",
            chain(vec![node(C_DBL, vec![Param(0)], None), node(C_INC, vec![Node(0)], None)]),
        ),
    ];
    for (name, expected) in cases {
        let plan = plan(&env, name);
        assert_eq!(plan.shape(), &expected, "`{name}`");
        admit_lowering(&env, &plan, &materialized(&plan)).unwrap_or_else(|refusal| {
            panic!("`{name}`'s materialized body must admit: {refusal:?}")
        });
    }
    // The dead binding BEFORE an aliased result is still evaluated: the
    // materialized body is two `Call`s, and the dropped mutant `_0 = h(_1)`
    // refuses structurally while the kernel alone ACCEPTS it (zeta drops the
    // dead `let`) — half_3's disclosure, on this shape.
    let dead_alias = plan(&env, "aliasLastDead");
    let faithful = emitted_chain(
        "aliasLastDead",
        1,
        u64_locals(3),
        vec![
            (DBL, vec![copy_local(1)], Place::local(2)),
            (H, vec![copy_local(1)], Place::local(0)),
        ],
    );
    assert_eq!(body_picture(&materialized(&dead_alias)), body_picture(&faithful));
    let dropped = emitted_chain(
        "aliasLastDead",
        1,
        u64_locals(2),
        vec![(H, vec![copy_local(1)], Place::local(0))],
    );
    let refusal = admit_lowering(&env, &dead_alias, &dropped).expect_err(
        "the dead binding before an aliased result IS evaluated; dropping it must refuse",
    );
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");
    assert!(refusal.note().contains("1 call(s) emitted for 2 planned"), "got {}", refusal.note());
    kernel_alone(&env, "aliasLastDead", &dropped)
        .expect("zeta drops the dead binding; only the structure refuses");
    // An alias of an EARLIER temporary stays refused — `z`'s call must still
    // run and a chain has one place for its result, the root's `Call` — and
    // the note names the later binding, never an empty list.
    for name in ["aliasEarlier", "retEarlier"] {
        let refusal = plan_refusal(&env, name);
        assert!(
            matches!(refusal, EmitRefusal::LetSpine { defect: false, .. }),
            "`{name}`: {refusal:?}"
        );
        assert!(!refusal.is_compiler_defect(), "`{name}`");
        let note = refusal.note();
        assert!(
            note.contains("temporary `y`")
                && note.contains("bound after it by `z`")
                && note.contains("reorder"),
            "`{name}`: {note}"
        );
        assert!(!note.contains("by  are"), "`{name}`: an empty binder list was rendered: {note}");
    }
}

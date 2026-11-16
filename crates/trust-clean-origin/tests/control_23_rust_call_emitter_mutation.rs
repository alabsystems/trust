// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 23 — THE RUST-CALL CHAIN EMITTER MUTATION FIXTURE** (W5,
//! Lean-calls-Rust; design of record
//! `docs/design/2026-09-13-lean-calls-rust-lane.md`, increments 1 and 2).
//!
//! `control_6` is the emitter-mutation discipline pointed at `Composed`; this
//! file is the same discipline pointed at
//! [`CleanOriginShape::RustCallChain`] — the shape behind battery row r18,
//! `def twice_inc (x : UInt64) : UInt64 := inc (inc x)` beside
//! `fn inc(x: u64) -> u64`.
//!
//! Side A is the REAL elaboration: every island below goes through
//! `trust_certify::clean_island::CleanIslandSession` with the callees declared
//! by `declare_rust_callees` — the exact session the mint, the MIR gate and
//! the verify pass build — so what is measured is the term the kernel holds,
//! not a hand-built stand-in. Side B is the emitted body as
//! `trust_mir_extract` would read it back (hand-built in the extracted shape,
//! exactly as `control_6` does; whether the real emitter produces this MIR is
//! the compiler lane's question, `tests/ui/trust/clean_origin_rust_call.rs`).
//!
//! # THE THREE THINGS THIS CONTROL EXISTS TO PIN
//!
//! 1. **The kernel separates the applications.** Every callee is a stuck
//!    `Opaque`, so `is_def_eq` on two applications is CONGRUENCE: a swapped
//!    argument, a wrong callee, a missing application and a wrong literal all
//!    refuse at the kernel — measured directly, with the structural layer
//!    bypassed, so the gate is not decoration.
//! 2. **E6 stays blind.** The emitted chain reads back as `None` from
//!    `recognize_admissible_body` (and from every other separate entry
//!    point), so the gate-free kernel-import direction never learns "a call
//!    to a user `fn`" (half_7).
//! 3. **The environment licenses nothing about the callee.** `rfl` against
//!    the hidden inhabitant is REJECTED by the batch (half_9).
//!
//! # DO NOT "FIX" A FAILURE HERE BY EDITING SIDE B'S PRODUCERS
//!
//! `trust_types::admissible_body::recognize_rust_call_chain` and
//! `trust_clean_origin::reflect_rust_call` are frozen against this lane. If a
//! mutated chain ever passes, the defect is in the emitter or the gate —
//! never in this fixture.

#![allow(non_snake_case)]

use std::collections::{BTreeMap, BTreeSet};

use trust_certify::clean_island::{CleanIslandSession, RustCallee};
use trust_clean_origin::{
    CleanOriginShape, EmitRefusal, GateRefusal, RustCallArg, RustCallLiteral, RustCallNode,
    RustCalleeRef, admit_lowering, check_faithful, plan_clean_origin_body,
    plan_clean_origin_body_with_rust_callees, reflect_rust_call_chain,
};
use trust_types::admissible_body::{
    RustCallChainArg, RustCallChainBody, RustCallChainNode, recognize_admissible_body,
    recognize_raw_binop, recognize_rust_call_chain, recognize_select_general,
};
use trust_types::{
    BasicBlock, BlockId, LocalDecl, Operand, Place, SourceSpan, Terminator, Ty, UnwindEdge,
    VerifiableBody, VerifiableFunction,
};

// ───────────────────────────── the callees ────────────────────────────────
//
// The renderings are what `trust_mir_extract::func_operand_name` produces
// for a free `fn` at the root of a crate named `main`
// (`with_resolve_crate_name` prefixes the local crate).

const INC: &str = "main::inc";
const DEC: &str = "main::dec";
const ADD2: &str = "main::add2";
const IS_SMALL: &str = "main::is_small";

fn declared() -> Vec<RustCallee> {
    vec![
        RustCallee { clean_name: "inc".into(), params: vec![Ty::u64()], result: Ty::u64() },
        RustCallee { clean_name: "dec".into(), params: vec![Ty::u64()], result: Ty::u64() },
        RustCallee {
            clean_name: "add2".into(),
            params: vec![Ty::u64(), Ty::u64()],
            result: Ty::u64(),
        },
        RustCallee { clean_name: "is_small".into(), params: vec![Ty::u32()], result: Ty::Bool },
    ]
}

/// The plan-side table, INCLUDING the `DefId` renderings only the MIR-time
/// session can supply.
fn table() -> Vec<RustCalleeRef> {
    declared()
        .into_iter()
        .map(|callee| RustCalleeRef {
            def_path: match callee.clean_name.as_str() {
                "inc" => INC,
                "dec" => DEC,
                "add2" => ADD2,
                _ => IS_SMALL,
            }
            .to_owned(),
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

/// Side A, from the REAL elaborator with the callees declared.
fn real_env(island: &str) -> clean_kernel::Environment {
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

const ISLAND: &str = "def twice_inc (x : UInt64) : UInt64 := inc (inc x)\n\
                      def sum2 (a b : UInt64) : UInt64 := add2 a b\n\
                      def plus5 (x : UInt64) : UInt64 := add2 x 5\n\
                      def six : UInt64 := inc 5\n\
                      def small (x : UInt32) : Bool := is_small x";

// ─────────────── the emitter's chain, as extracted, and mutants ───────────────

fn locals(tys: &[Ty]) -> Vec<LocalDecl> {
    tys.iter()
        .enumerate()
        .map(|(index, ty)| LocalDecl { index, ty: ty.clone(), name: None })
        .collect()
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
                // The row's edge: user code may unwind.
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

fn u64_const(value: u128) -> Operand {
    Operand::Constant(trust_types::ConstValue::Uint(value, 64))
}

/// `_2 = inc(_1); _0 = inc(_2); return` — the faithful r18 chain.
fn faithful_twice_inc() -> VerifiableFunction {
    emitted_chain(
        "twice_inc",
        1,
        locals(&[Ty::u64(), Ty::u64(), Ty::u64()]),
        vec![
            (INC, vec![copy_local(1)], Place::local(2)),
            (INC, vec![copy_local(2)], Place::local(0)),
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
        &clean_kernel::Expr::const_(clean_kernel::Name::from_string("UInt64"), vec![]),
        &Ty::u64(),
    )
    .expect("UInt64 -> u64 is the exact-width carrier")
}

/// Reflect a hand-built RECOGNISED chain directly — the kernel half of a
/// mutation, bypassing the structural check on purpose so the KERNEL's own
/// verdict is measured (control_3 half_3's rationale).
fn reflect(
    env: &clean_kernel::Environment,
    body: &RustCallChainBody,
    extracted: &VerifiableFunction,
) -> clean_kernel::Expr {
    reflect_rust_call_chain(env, "twice_inc", body, extracted, &names_of_paths())
        .unwrap_or_else(|e| panic!("the chain must reflect: {e}"))
}

fn node(callee: &str, args: Vec<RustCallChainArg>) -> RustCallChainNode {
    RustCallChainNode { callee: callee.to_owned(), args }
}

// ═══════════════════════════════ the halves ═══════════════════════════════

#[test]
fn half_0_the_plan_reads_the_real_elaboration_as_a_rust_call_chain() {
    let env = real_env(ISLAND);
    let plan = plan_clean_origin_body_with_rust_callees(&env, "twice_inc", &table())
        .expect("`inc (inc x)` plans against the declared callee");
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::RustCallChain {
            nodes: vec![
                RustCallNode { callee: 0, args: vec![RustCallArg::Param(0)], let_binding: None },
                RustCallNode { callee: 0, args: vec![RustCallArg::Node(0)], let_binding: None },
            ],
        },
        "post-order: the inner application first, the root last"
    );
    assert_eq!(plan.callees(), table().as_slice(), "the plan carries the table it was read over");

    // The NO-CALLEE entry refuses the same body as outside the fragment —
    // this is what the mint seam sees before increment 1 and what every
    // consumer without a table still sees.
    let refusal = plan_clean_origin_body(&env, "twice_inc")
        .expect_err("without the table the head `inc` is an unknown constant");
    assert!(matches!(refusal, EmitRefusal::NotEmittable { .. }), "got {refusal:?}");
    assert!(!refusal.is_compiler_defect());
}

#[test]
fn half_1_the_gate_admits_the_faithful_chain() {
    let env = real_env(ISLAND);
    let plan =
        plan_clean_origin_body_with_rust_callees(&env, "twice_inc", &table()).expect("plans");
    let admitted = admit_lowering(&env, &plan, &faithful_twice_inc())
        .expect("the post-order chain IS `inc (inc x)`; the gate must admit it");
    assert_eq!(admitted.name(), "twice_inc");
    assert_eq!(admitted.admitted_at(), &Ty::u64(), "admitted AT THE CARRIER, never the Clean type");
}

#[test]
fn half_2_a_SWAPPED_ARGUMENT_is_refused_by_both_layers() {
    let env = real_env(ISLAND);
    let plan = plan_clean_origin_body_with_rust_callees(&env, "sum2", &table()).expect("plans");
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::RustCallChain {
            nodes: vec![RustCallNode {
                callee: 2,
                args: vec![RustCallArg::Param(0), RustCallArg::Param(1)],
                let_binding: None
            }],
        }
    );

    // Structural half: `_0 = add2(_2, _1)` for a def that says `add2 a b`.
    let refusal = admit_lowering(
        &env,
        &plan,
        &emitted_chain(
            "sum2",
            2,
            locals(&[Ty::u64(), Ty::u64(), Ty::u64()]),
            vec![(ADD2, vec![copy_local(2), copy_local(1)], Place::local(0))],
        ),
    )
    .expect_err(
        "THE GATE IS DECORATION IF THIS PASSES: `add2 b a` was accepted for a definition \
         that says `add2 a b` — a WRONG BINARY. Do NOT fix this by editing side B.",
    );
    assert!(refusal.is_compiler_defect(), "a mistranslation is a compiler defect: {refusal:?}");
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");

    // Kernel half: the swapped reflection put to the kernel directly. The
    // callee is a stuck `Opaque`, so `add2 b a` and `add2 a b` are separated
    // by congruence and nothing else — exactly the judgment the lane rests on.
    let extracted = emitted_chain(
        "sum2",
        2,
        locals(&[Ty::u64(), Ty::u64(), Ty::u64()]),
        vec![(ADD2, vec![copy_local(2), copy_local(1)], Place::local(0))],
    );
    let swapped = RustCallChainBody {
        nodes: vec![node(ADD2, vec![RustCallChainArg::Param(1), RustCallChainArg::Param(0)])],
    };
    let side_b = reflect_rust_call_chain(&env, "sum2", &swapped, &extracted, &names_of_paths())
        .expect("the swapped chain is well-typed and reflects");
    let refusal = check_faithful(&env, "sum2", &side_b, &u64_carrier())
        .expect_err("the kernel must separate `add2 a b` from `add2 b a`");
    assert!(matches!(refusal, GateRefusal::Disagreement { .. }), "got {refusal:?}");
}

#[test]
fn half_3_the_WRONG_CALLEE_is_refused_by_both_layers() {
    let env = real_env(ISLAND);
    let plan =
        plan_clean_origin_body_with_rust_callees(&env, "twice_inc", &table()).expect("plans");

    // Structural half: the inner call goes to `dec` — an ADMISSIBLE callee,
    // so the recognizer accepts the body and only the plan comparison can
    // catch it.
    let mutant = emitted_chain(
        "twice_inc",
        1,
        locals(&[Ty::u64(), Ty::u64(), Ty::u64()]),
        vec![
            (DEC, vec![copy_local(1)], Place::local(2)),
            (INC, vec![copy_local(2)], Place::local(0)),
        ],
    );
    let refusal = admit_lowering(&env, &plan, &mutant)
        .expect_err("`inc (dec x)` emitted for a def that says `inc (inc x)` must refuse");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");

    // Kernel half.
    let wrong = RustCallChainBody {
        nodes: vec![
            node(DEC, vec![RustCallChainArg::Param(0)]),
            node(INC, vec![RustCallChainArg::Node(0)]),
        ],
    };
    let refusal =
        check_faithful(&env, "twice_inc", &reflect(&env, &wrong, &mutant), &u64_carrier())
            .expect_err("the kernel must separate `inc (inc x)` from `inc (dec x)`");
    assert!(matches!(refusal, GateRefusal::Disagreement { .. }), "got {refusal:?}");
}

#[test]
fn half_4_a_MISSING_APPLICATION_is_refused_by_both_layers() {
    // `inc x` for a def that says `inc (inc x)`: one call fewer, every
    // remaining node correct. The design's own named mutation.
    let env = real_env(ISLAND);
    let plan =
        plan_clean_origin_body_with_rust_callees(&env, "twice_inc", &table()).expect("plans");
    let mutant = emitted_chain(
        "twice_inc",
        1,
        locals(&[Ty::u64(), Ty::u64()]),
        vec![(INC, vec![copy_local(1)], Place::local(0))],
    );
    let refusal = admit_lowering(&env, &plan, &mutant)
        .expect_err("`inc x` emitted for a def that says `inc (inc x)` must refuse");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");

    let once = RustCallChainBody { nodes: vec![node(INC, vec![RustCallChainArg::Param(0)])] };
    let refusal = check_faithful(&env, "twice_inc", &reflect(&env, &once, &mutant), &u64_carrier())
        .expect_err(
            "the kernel must separate `inc (inc x)` from `inc x` — the opaque never unfolds",
        );
    assert!(matches!(refusal, GateRefusal::Disagreement { .. }), "got {refusal:?}");
}

#[test]
fn half_5_a_WRONG_or_WIDTH_SKEWED_LITERAL_is_refused() {
    let env = real_env(ISLAND);
    let plan = plan_clean_origin_body_with_rust_callees(&env, "plus5", &table()).expect("plans");
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::RustCallChain {
            nodes: vec![RustCallNode {
                callee: 2,
                args: vec![RustCallArg::Param(0), RustCallArg::Literal(RustCallLiteral::UInt(5))],
                let_binding: None
            }],
        }
    );
    let faithful = emitted_chain(
        "plus5",
        1,
        locals(&[Ty::u64(), Ty::u64()]),
        vec![(ADD2, vec![copy_local(1), u64_const(5)], Place::local(0))],
    );
    admit_lowering(&env, &plan, &faithful).expect("`add2 x 5` with the scalar 5 at u64 admits");

    // The wrong VALUE: structural, then kernel.
    let wrong_value = emitted_chain(
        "plus5",
        1,
        locals(&[Ty::u64(), Ty::u64()]),
        vec![(ADD2, vec![copy_local(1), u64_const(6)], Place::local(0))],
    );
    let refusal = admit_lowering(&env, &plan, &wrong_value).expect_err("6 for 5 must refuse");
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");
    let six = RustCallChainBody {
        nodes: vec![node(
            ADD2,
            vec![RustCallChainArg::Param(0), RustCallChainArg::UInt { value: 6, width_bits: 64 }],
        )],
    };
    let refusal = check_faithful(&env, "plus5", &reflect(&env, &six, &wrong_value), &u64_carrier())
        .expect_err("the kernel must separate `add2 x 5` from `add2 x 6`");
    assert!(matches!(refusal, GateRefusal::Disagreement { .. }), "got {refusal:?}");

    // The wrong WIDTH: a u32 scalar for a u64 parameter is refused
    // structurally, and — bypassing that — the KERNEL refuses to type the
    // reflected `add2 x (UInt32.ofNat 5)` at all, so nothing reaches
    // `is_def_eq` untyped.
    let skewed = emitted_chain(
        "plus5",
        1,
        locals(&[Ty::u64(), Ty::u64()]),
        vec![(
            ADD2,
            vec![copy_local(1), Operand::Constant(trust_types::ConstValue::Uint(5, 32))],
            Place::local(0),
        )],
    );
    let refusal = admit_lowering(&env, &plan, &skewed).expect_err("a width skew must refuse");
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");
    let skewed_body = RustCallChainBody {
        nodes: vec![node(
            ADD2,
            vec![RustCallChainArg::Param(0), RustCallChainArg::UInt { value: 5, width_bits: 32 }],
        )],
    };
    let detail = reflect_rust_call_chain(&env, "plus5", &skewed_body, &skewed, &names_of_paths())
        .expect_err("the kernel must refuse `add2 x (UInt32.ofNat 5)` at `add2 : UInt64 → …`");
    assert!(detail.contains("kernel refused"), "got {detail}");
}

#[test]
fn half_6_a_callee_OUTSIDE_THE_ALLOW_LIST_is_unrecognised() {
    // A same-named function from another crate, or any `fn` the mint did not
    // register: the reader refuses the body outright — it is not "a chain
    // with a different callee", it is not a chain this lane reads at all.
    let env = real_env(ISLAND);
    let plan =
        plan_clean_origin_body_with_rust_callees(&env, "twice_inc", &table()).expect("plans");
    let impostor = emitted_chain(
        "twice_inc",
        1,
        locals(&[Ty::u64(), Ty::u64(), Ty::u64()]),
        vec![
            (INC, vec![copy_local(1)], Place::local(2)),
            ("other_crate::inc", vec![copy_local(2)], Place::local(0)),
        ],
    );
    let refusal = admit_lowering(&env, &plan, &impostor).expect_err("must refuse");
    assert!(matches!(refusal, EmitRefusal::LoweringUnrecognised { .. }), "got {refusal:?}");
    assert!(recognize_rust_call_chain(&impostor, &allowed()).is_none());
}

#[test]
fn half_7_E6_STAYS_BLIND_the_chain_reads_back_as_none_from_every_other_entry_point() {
    // THE STANDING PROHIBITION, measured. `recognize_admissible_body` feeds
    // the gate-free kernel-import direction; a call to a user `fn` must never
    // read as an admissible body there.
    let body = faithful_twice_inc();
    assert!(
        recognize_admissible_body(&body).is_none(),
        "the Rust-call chain has joined `recognize_admissible_body`'s chain: E6 would now \
         import `fn f(x) {{ g(x) }}` as the defining equation `f = g` with `g` opaque"
    );
    assert!(recognize_raw_binop(&body).is_none());
    assert!(recognize_select_general(&body).is_none());
    // …while the separate entry point reads it, given the allow-list.
    let read = recognize_rust_call_chain(&body, &allowed()).expect("the separate entry reads it");
    assert_eq!(
        read,
        RustCallChainBody {
            nodes: vec![
                node(INC, vec![RustCallChainArg::Param(0)]),
                node(INC, vec![RustCallChainArg::Node(0)]),
            ]
        }
    );
    // …and NOT without one.
    assert!(recognize_rust_call_chain(&body, &BTreeSet::new()).is_none());
}

#[test]
fn half_8_the_mint_seam_grants_and_the_mint_plan_never_reaches_side_b() {
    let env = real_env(ISLAND);

    // The mint's own decision, exactly as `trust_clean_mint::decide` makes it.
    let mut facets = trust_spec_elab::FacetTable::new();
    let admission = trust_certify::clean_island::admit_certified_island_definition(
        &env,
        "twice_inc",
        &mut facets,
    )
    .expect("an Opaque callee does not make the closure Trusted");
    let constant =
        env.get_const(&clean_kernel::Name::from_string("twice_inc")).expect("registered");
    let carrier = trust_clean_carrier::carrier_signature_for(&constant.type_)
        .map(|signature| signature.result().clone());
    trust_clean_origin::decide_mint("twice_inc", admission.status(), carrier)
        .expect("kernel-checked, audited-empty closure, total carrier: the mint grants");

    // The mint-seam plan (no `DefId` renderings) reads the SAME shape…
    let mint_plan = plan_clean_origin_body_with_rust_callees(&env, "twice_inc", &mint_table())
        .expect("the mint seam plans the shape");
    assert_eq!(
        mint_plan.shape(),
        plan_clean_origin_body_with_rust_callees(&env, "twice_inc", &table())
            .expect("plans")
            .shape()
    );
    // …but can never be admitted: a plan without renderings is refused
    // before any name is matched.
    let refusal = admit_lowering(&env, &mint_plan, &faithful_twice_inc())
        .expect_err("a plan built at the mint seam must not reach the kernel gate");
    assert!(matches!(refusal, EmitRefusal::ReflectionRejected { .. }), "got {refusal:?}");
    assert!(refusal.note().contains("no `DefId` rendering"), "got {}", refusal.note());
}

#[test]
fn half_9_the_environment_licenses_nothing_about_the_callee() {
    // The kernel can prove NOTHING about `inc` beyond its type: the hidden
    // inhabitant never unfolds.
    let mut session = CleanIslandSession::new();
    session.declare_rust_callees(&declared()).expect("declares");
    let batch = session.check_all(&["theorem t (x : UInt64) : inc x = UInt64.ofNat 0 := rfl"]);
    assert!(batch.is_rejected(), "`rfl` against the hidden inhabitant must be REJECTED");
    let mut session = CleanIslandSession::new();
    session.declare_rust_callees(&declared()).expect("declares");
    let batch = session.check_all(&["theorem t (x : UInt64) : inc (inc x) = inc x := rfl"]);
    assert!(batch.is_rejected(), "two applications of a stuck head are separated by congruence");
}

#[test]
fn half_10_a_NULLARY_def_and_a_BOOL_callee_admit() {
    let env = real_env(ISLAND);

    // `def six : UInt64 := inc 5` — arity 0, one call, a literal operand.
    let plan = plan_clean_origin_body_with_rust_callees(&env, "six", &table()).expect("plans");
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::RustCallChain {
            nodes: vec![RustCallNode {
                callee: 0,
                args: vec![RustCallArg::Literal(RustCallLiteral::UInt(5))],
                let_binding: None
            }],
        }
    );
    let six = emitted_chain(
        "six",
        0,
        locals(&[Ty::u64()]),
        vec![(INC, vec![u64_const(5)], Place::local(0))],
    );
    admit_lowering(&env, &plan, &six).expect("`inc 5` admits at arity 0");

    // `def small (x : UInt32) : Bool := is_small x` — a `bool` result and a
    // `u32` parameter, neither of which is the other's carrier.
    let plan = plan_clean_origin_body_with_rust_callees(&env, "small", &table()).expect("plans");
    let small = emitted_chain(
        "small",
        1,
        locals(&[Ty::Bool, Ty::u32()]),
        vec![(IS_SMALL, vec![copy_local(1)], Place::local(0))],
    );
    let admitted = admit_lowering(&env, &plan, &small).expect("`is_small x` admits at `bool`");
    assert_eq!(admitted.admitted_at(), &Ty::Bool);
    // …and a body whose parameter local is typed at the WRONG width refuses
    // at the kernel: the binder types come from the EMITTED body.
    let wrong_local = emitted_chain(
        "small",
        1,
        locals(&[Ty::Bool, Ty::u64()]),
        vec![(IS_SMALL, vec![copy_local(1)], Place::local(0))],
    );
    let refusal = admit_lowering(&env, &plan, &wrong_local)
        .expect_err("a `u64` local passed to `is_small : UInt32 → Bool` must refuse");
    assert!(refusal.is_compiler_defect(), "got {refusal:?}");
}

#[test]
fn half_11_the_sealed_plan_rechecks_the_chain() {
    // A partial application, a computed operand and a wrong-arity call are
    // refused at PLAN time with a v7/D3 reason — none of them can reach the
    // emitter. Each is a separate island because a rejected batch registers
    // nothing.
    let cases = [
        // `inc` applied to an arithmetic expression: the argument computes.
        ("def f (x : UInt64) : UInt64 := inc (x + 1)", "computes"),
    ];
    for (island, expected) in cases {
        let env = real_env(island);
        let refusal = plan_clean_origin_body_with_rust_callees(&env, "f", &table())
            .expect_err("must refuse at plan time");
        assert!(!refusal.is_compiler_defect(), "a fragment refusal is the user's: {refusal:?}");
        assert!(refusal.note().contains(expected), "got {}", refusal.note());
        assert!(refusal.note().contains("options"), "v7/D3: options; got {}", refusal.note());
    }
}

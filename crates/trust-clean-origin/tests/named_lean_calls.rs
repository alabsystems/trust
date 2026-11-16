// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Actual island source on side A; the existing expression reflector on side B.
//! A selected source plan is never itself the permission checked in this file.
use std::sync::OnceLock;

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Name};
use trust_clean_origin::CleanOriginShape;
use trust_clean_origin::emit::plan_clean_origin_body_for_name;
use trust_clean_origin::gate::check_faithful_for_name;
use trust_types::admissible_body::{ArithBinOp, ArithOperand};

const SOURCE: &str = r#"
def A.b (a b : UInt64) : UInt64 := a
def «A.b» (a b : UInt64) : UInt64 := b + 1
def pathPick (a b : UInt64) : UInt64 := A.b a b
def quotedPick (a b : UInt64) : UInt64 := «A.b» a b
def plusOne (a : UInt64) : UInt64 := a + 1
def square (a : UInt64) : UInt64 := a * a
def nestedCall (a : UInt64) : UInt64 := square (plusOne a)
def difference (a b : UInt64) : UInt64 := a - b
def swappedCall (a b : UInt64) : UInt64 := difference b a
def aliasCall : UInt64 → UInt64 → UInt64 := difference
def pass {α : Type} (x : α) : α := x
def typedCall (a : UInt64) : UInt64 := pass a
def «UInt64.add» (a b : UInt64) : UInt64 := a - b
def primitiveAliasCall (a b : UInt64) : UInt64 := «UInt64.add» a b
def shadowCall (a b : UInt64) : UInt64 :=
  let a := plusOne b
  difference a b
def zeroHelper (a : UInt64) : UInt64 := 0
def zeroDivCall (a : UInt64) : UInt64 := a / zeroHelper a
"#;

fn island(source: &str) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let report = session.check_all(&[source]);
    assert!(!report.is_rejected(), "actual island source must kernel-check: {report:?}");
    session.environment().unwrap().clone()
}

fn env() -> &'static Environment {
    static ENV: OnceLock<Environment> = OnceLock::new();
    ENV.get_or_init(|| island(SOURCE))
}

fn reflected(env: &Environment, body: &str, arity: usize) -> Expr {
    let names = (0..arity).map(|i| format!("p{i}")).collect::<Vec<_>>();
    let refs = names.iter().map(String::as_str).collect::<Vec<_>>();
    let mut scratch = env.clone();
    let name = "named_call_mutation_reflection";
    trust_spec_elab::admit_expr_function(
        &mut scratch,
        name,
        body,
        &refs,
        &trust_spec_elab::Domain::Machine(trust_spec_elab::MachineUIntWidth::U64),
    )
    .unwrap();
    scratch.get_const(&Name::from_string(name)).unwrap().value.clone().unwrap()
}

fn gate_pair(name: &str, arity: usize, correct: &str, wrong: &str) {
    let declaration = Name::from_string(name);
    let plan = plan_clean_origin_body_for_name(env(), &declaration).unwrap();
    let good = reflected(env(), correct, arity);
    let bad = reflected(env(), wrong, arity);
    let permission =
        check_faithful_for_name(env(), &declaration, &good, plan.signature().result()).unwrap();
    assert_eq!(permission.declaration(), &declaration);
    assert!(check_faithful_for_name(env(), &declaration, &bad, plan.signature().result()).is_err());
}

#[test]
fn quoted_and_path_callees_plan_their_own_source_bodies() {
    let path = plan_clean_origin_body_for_name(env(), &Name::from_string("pathPick")).unwrap();
    let quoted = plan_clean_origin_body_for_name(env(), &Name::from_string("quotedPick")).unwrap();
    assert_eq!(path.shape(), &CleanOriginShape::Projection { projected: 0 });
    assert_eq!(
        quoted.shape(),
        &CleanOriginShape::WrappingBinOp {
            op: ArithBinOp::Add,
            left: ArithOperand::Param(1),
            right: ArithOperand::Const(1),
        }
    );
    gate_pair("pathPick", 2, "p0", "p1 + 1");
    gate_pair("quotedPick", 2, "p1 + 1", "p0");
}

#[test]
fn nested_helper_calls_preserve_repeated_arguments() {
    let plan = plan_clean_origin_body_for_name(env(), &Name::from_string("nestedCall")).unwrap();
    assert!(matches!(plan.shape(), CleanOriginShape::Composed { .. }));
    gate_pair("nestedCall", 1, "(p0 + 1) * (p0 + 1)", "(p0 + 1) * p0");
}

#[test]
fn argument_order_and_eta_contracted_aliases_keep_their_meaning() {
    let plan = plan_clean_origin_body_for_name(env(), &Name::from_string("swappedCall")).unwrap();
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::WrappingBinOp {
            op: ArithBinOp::Sub,
            left: ArithOperand::Param(1),
            right: ArithOperand::Param(0),
        }
    );
    gate_pair("swappedCall", 2, "p1 - p0", "p0 - p1");
    gate_pair("aliasCall", 2, "p0 - p1", "p1 - p0");
}

#[test]
fn polymorphic_helper_arguments_are_instantiated_including_the_type() {
    let plan = plan_clean_origin_body_for_name(env(), &Name::from_string("typedCall")).unwrap();
    assert_eq!(plan.shape(), &CleanOriginShape::Projection { projected: 0 });
    gate_pair("typedCall", 1, "p0", "p0 + 1");
}

#[test]
fn quoted_primitive_display_alias_does_not_select_the_primitive() {
    let plan =
        plan_clean_origin_body_for_name(env(), &Name::from_string("primitiveAliasCall")).unwrap();
    assert!(matches!(plan.shape(), CleanOriginShape::WrappingBinOp { op: ArithBinOp::Sub, .. }));
    gate_pair("primitiveAliasCall", 2, "p0 - p1", "p0 + p1");
}

#[test]
fn named_calls_inside_let_bindings_keep_capture_avoiding_substitution() {
    gate_pair("shadowCall", 2, "(p1 + 1) - p1", "(p0 + 1) - p1");
}

#[test]
fn expansion_cannot_hide_the_total_lean_vs_panicking_rust_divisor_boundary() {
    let refusal =
        plan_clean_origin_body_for_name(env(), &Name::from_string("zeroDivCall")).unwrap_err();
    let note = refusal.note();
    assert!(
        note.contains("divisor") && (note.contains("zero") || note.contains("positive")),
        "{note}"
    );
}

#[test]
fn a_deep_helper_chain_refuses_without_a_partial_plan() {
    let mut source = String::from("def chain0 (a : UInt64) : UInt64 := a\n");
    for i in 1..=140 {
        source.push_str(&format!("def chain{i} (a : UInt64) : UInt64 := chain{} a\n", i - 1));
    }
    let env = island(&source);
    let refusal =
        plan_clean_origin_body_for_name(&env, &Name::from_string("chain140")).unwrap_err();
    assert!(refusal.note().contains("work envelope"), "{}", refusal.note());
}

#[test]
fn a_checked_caller_cannot_expand_a_structurally_inserted_callee() {
    let mut env = Environment::new();
    env.init_uint_arith().unwrap();
    let uint = Expr::const_(Name::from_string("UInt64"), vec![]);
    let ty = Expr::arrow(uint.clone(), uint.clone());
    let callee = Name::anon().str("unsafe.helper");
    env.add_decl_structural(Declaration::Definition {
        name: callee.clone(),
        level_params: vec![],
        type_: ty.clone(),
        value: Expr::lam(BinderInfo::Default, uint.clone(), Expr::bvar(0)),
        is_reducible: true,
    })
    .unwrap();
    let caller = Name::from_string("checkedCaller");
    env.add_decl(Declaration::Definition {
        name: caller.clone(),
        level_params: vec![],
        type_: ty,
        value: Expr::lam(
            BinderInfo::Default,
            uint,
            Expr::app(Expr::const_(callee, vec![]), Expr::bvar(0)),
        ),
        is_reducible: true,
    })
    .unwrap();
    let refusal = plan_clean_origin_body_for_name(&env, &caller).unwrap_err();
    assert!(refusal.note().contains("no full kernel check"), "{}", refusal.note());
}

#[test]
fn opaque_helper_bodies_are_not_opened_by_planning() {
    let env = island(
        "opaque hidden (a : UInt64) : UInt64 := a\ndef opaqueCaller (a : UInt64) : UInt64 := hidden a",
    );
    assert!(plan_clean_origin_body_for_name(&env, &Name::from_string("opaqueCaller")).is_err());
}

fn rust_call_environment(source: &str) -> (Environment, Vec<trust_clean_origin::RustCalleeRef>) {
    use trust_certify::clean_island::{CleanIslandSession, RustCallee};
    use trust_types::Ty;
    let declarations = vec![
        RustCallee { clean_name: "tick".into(), params: vec![Ty::u64()], result: Ty::u64() },
        RustCallee {
            clean_name: "add2".into(),
            params: vec![Ty::u64(), Ty::u64()],
            result: Ty::u64(),
        },
    ];
    let mut session = CleanIslandSession::new();
    session.declare_rust_callees(&declarations).unwrap();
    let report = session.check_all(&[source]);
    assert!(!report.is_rejected(), "{report:?}");
    let table = declarations
        .into_iter()
        .map(|row| trust_clean_origin::RustCalleeRef {
            def_path: format!("test::{}", row.clean_name),
            clean_name: row.clean_name,
            params: row.params,
            result: row.result,
        })
        .collect();
    (session.environment().unwrap().clone(), table)
}

#[test]
fn named_helpers_cannot_drop_duplicate_or_reorder_rust_arguments() {
    let (env, table) = rust_call_environment(
        r#"
        def ignoreValue (a : UInt64) : UInt64 := 0
        def dropCall (a : UInt64) : UInt64 := ignoreValue (tick a)
        def addTwice (a : UInt64) : UInt64 := add2 a a
        def duplicateCall (a : UInt64) : UInt64 := addTwice (tick a)
        def swapValues (a b : UInt64) : UInt64 := add2 b a
        def reorderCall (a b : UInt64) : UInt64 := swapValues (tick a) (tick b)
    "#,
    );
    for name in ["dropCall", "duplicateCall", "reorderCall"] {
        let refusal =
            trust_clean_origin::plan_clean_origin_body_with_rust_callees(&env, name, &table)
                .unwrap_err();
        assert!(refusal.note().contains("value temporary"), "{}", refusal.note());
    }
}

/// **THE EXPLICIT VALUE TEMPORARY (2026-09-15).**
///
/// Until this landing a `let`-bound Rust call was refused outright, because
/// SUBSTITUTING it (zeta) is what the planner did with a `let`, and zeta can
/// duplicate, erase or reorder a call the kernel — a pure calculus — sees only
/// as a value. The refusal named its own fix: *"the compiler needs an explicit
/// value temporary"*. `emit::walk_let_spine` (W5 increment 7) builds exactly
/// that: the bound call becomes ONE chain node, marked
/// `RustCallNode::let_binding`, emitted at the binding's place in source
/// order, and every use of the bound name reads that node.
///
/// These probes are about the SHAPE, not about the callee: nothing here asks
/// whether `tick` is pure. Single evaluation holds by construction — one node,
/// one `Call` — so it would hold for an effectful callee too. Callee purity is
/// a separate, independent guard (`clean_origin_mir::rust_callee_is_pure`).
#[test]
fn let_bound_rust_calls_are_value_temporaries_evaluated_once() {
    // W5 increment 7: a `let` whose value is a Rust call is ONE shared
    // `RustCallChain` node, evaluated exactly once whatever its use count and
    // in binding order — the kernel's zeta cannot see either, so the claim is
    // the structural chain `control_27_clean_let_temp_emitter_mutation` pins.
    // `letDrop` below is refused because its RESULT is a literal, so the chain
    // has no root Rust call at all — not because the binding is unread. A
    // binding the result never reads but whose body still ends in a Rust call
    // (`letUnread`) is ADMITTED and its `Call` emitted, in binding order:
    // `let_substitution_cannot_erase_or_postpone_rust_calls` pins that, and
    // `docs/TCB.md`'s let-temp ONCE-EVALUATION row discloses it. Either way
    // the bound call is never silently dropped.
    use trust_clean_origin::RustCallArg::{Node, Param};
    use trust_clean_origin::{EmitRefusal, RustCallNode};
    let (env, table) = rust_call_environment(
        r#"
        def letDrop (a : UInt64) : UInt64 := let p := tick a; 0
        def letDuplicate (a : UInt64) : UInt64 := let p := tick a; add2 p p
        def letOnce (a : UInt64) : UInt64 := let p := tick a; add2 p a
        def letReorder (a b : UInt64) : UInt64 := let p := tick a; add2 (tick b) p
    "#,
    );
    let node = |callee, args, let_binding| RustCallNode { callee, args, let_binding };
    // ONE `tick` node, READ TWICE — never two calls. This is the whole claim.
    let plan =
        trust_clean_origin::plan_clean_origin_body_with_rust_callees(&env, "letDuplicate", &table)
            .expect("`let p := tick a; add2 p p` plans as one temporary read twice");
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::RustCallChain {
            nodes: vec![node(0, vec![Param(0)], Some(0)), node(1, vec![Node(0), Node(0)], None)],
        }
    );
    // A single use is the same chain with one read — no special case.
    let plan =
        trust_clean_origin::plan_clean_origin_body_with_rust_callees(&env, "letOnce", &table)
            .expect("`let p := tick a; add2 p a` plans as one temporary read once");
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::RustCallChain {
            nodes: vec![node(0, vec![Param(0)], Some(0)), node(1, vec![Node(0), Param(0)], None)],
        }
    );
    // SOURCE ORDER: `tick a` is bound first, so it is node 0 and is called
    // FIRST, even though `tick b` is the argument that appears first in the
    // body. Substitution is what could have reordered these; nothing here
    // substitutes.
    let plan =
        trust_clean_origin::plan_clean_origin_body_with_rust_callees(&env, "letReorder", &table)
            .expect("the bound call is evaluated first, then the operand call, then the root");
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::RustCallChain {
            nodes: vec![
                node(0, vec![Param(0)], Some(0)),
                node(0, vec![Param(1)], None),
                node(1, vec![Node(1), Node(0)], None),
            ],
        }
    );
    let refusal =
        trust_clean_origin::plan_clean_origin_body_with_rust_callees(&env, "letDrop", &table)
            .expect_err("a `let`-bound call the literal result never reads has no emitted form");
    assert!(matches!(refusal, EmitRefusal::LetSpine { defect: false, .. }), "{refusal:?}");
    assert!(!refusal.is_compiler_defect());
    let note = refusal.note();
    assert!(note.contains("never used") && note.contains("options"), "{note}");
}

/// The gate still decides, and the structural half is what enforces SINGLE
/// evaluation — the kernel cannot, and this measures that it does not have to.
#[test]
fn the_single_call_body_admits_and_the_duplicating_one_refuses() {
    use trust_types::{
        BasicBlock, BlockId, LocalDecl, Operand, Place, SourceSpan, Terminator, Ty, UnwindEdge,
        VerifiableBody, VerifiableFunction,
    };

    let (env, table) = rust_call_environment(
        "def letDuplicate (a : UInt64) : UInt64 := let p := tick a; add2 p p",
    );
    let plan =
        trust_clean_origin::plan_clean_origin_body_with_rust_callees(&env, "letDuplicate", &table)
            .expect("the `let`-bound call plans as a shared chain node");

    let call = |k: usize, callee: &str, args: Vec<Operand>, dest: usize| BasicBlock {
        id: BlockId(k),
        stmts: Vec::new(),
        terminator: Terminator::Call {
            func: callee.into(),
            args,
            dest: Place::local(dest),
            target: Some(BlockId(k + 1)),
            span: SourceSpan::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            callee_identity: None,
            callee_key: None,
            unwind: UnwindEdge::Continue,
        },
    };
    let body = |locals: usize, blocks: Vec<BasicBlock>| VerifiableFunction {
        name: "letDuplicate".into(),
        def_path: "test::letDuplicate".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: (0..locals)
                .map(|index| LocalDecl { index, ty: Ty::u64(), name: None })
                .collect(),
            blocks,
            arg_count: 1,
            return_ty: Ty::u64(),
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    let copy = |i: usize| Operand::Copy(Place::local(i));
    let ret =
        |k: usize| BasicBlock { id: BlockId(k), stmts: Vec::new(), terminator: Terminator::Return };

    // `_2 = tick(_1); _0 = add2(copy _2, copy _2); return` — ONE call, two
    // reads of its temporary.
    let once = body(
        3,
        vec![
            call(0, "test::tick", vec![copy(1)], 2),
            call(1, "test::add2", vec![copy(2), copy(2)], 0),
            ret(2),
        ],
    );
    trust_clean_origin::admit_lowering(&env, &plan, &once)
        .expect("one call, read twice, IS `let p := tick a; add2 p p`");

    // `_2 = tick(_1); _3 = tick(_1); _0 = add2(copy _2, copy _3)` — the body
    // zeta would have produced. The KERNEL cannot tell it apart (both reflect
    // to `add2 (tick a) (tick a)`, and `tick` is a stuck opaque head either
    // way); the STRUCTURAL half refuses it, which is why single evaluation is
    // a property of the plan and not of an argument about the callee.
    let twice = body(
        4,
        vec![
            call(0, "test::tick", vec![copy(1)], 2),
            call(1, "test::tick", vec![copy(1)], 3),
            call(2, "test::add2", vec![copy(2), copy(3)], 0),
            ret(3),
        ],
    );
    let refusal = trust_clean_origin::admit_lowering(&env, &plan, &twice)
        .expect_err("two calls where the plan has one must refuse");
    assert!(
        matches!(refusal, trust_clean_origin::EmitRefusal::LoweringShapeMismatch { .. }),
        "{refusal:?}"
    );
}

/// The boundaries the value-temporary lane does NOT cross, and the ONE that
/// moved when W5 increment 7 landed. Each refusal keeps a note that names the
/// fix (v7/D3) and says "value temporary", because that is the lane being
/// declined.
///
/// **What changed, and why this probe no longer refuses `letUnread`
/// (2026-09-16).** The 2026-09-15 recogniser refused a `let` whose value the
/// body never reads, on the grounds that a call kept for its EFFECT alone is
/// invisible to the kernel's reading of the `def`. Increment 7 decides that
/// case the other way and says so: a `let`-bound Rust call is evaluated
/// exactly once, in binding order, whatever its use count — a DEAD binding is
/// a written, unread local whose `Call` still executes (Trust's strict `let`,
/// not Lean fidelity; Lean's compiler DCEs it and the kernel's zeta cannot
/// see the difference either way). That is disclosed in `docs/TCB.md` (the
/// let-temp ONCE-EVALUATION row) and pinned from both directions by
/// `control_27_clean_let_temp_emitter_mutation`: the dead binding's chain
/// admits (half `dead`), and a lowering that DROPS the dead call is refused
/// structurally while the kernel alone stays blind to it (half_3). So the
/// shape below is asserted as ADMITTED, with its node marked.
#[test]
fn let_substitution_cannot_erase_or_postpone_rust_calls() {
    use trust_clean_origin::RustCallArg::Param;
    use trust_clean_origin::RustCallNode;
    let (env, table) = rust_call_environment(
        r#"
        def letDrop (a : UInt64) : UInt64 := let p := tick a; 0
        def letUnread (a : UInt64) : UInt64 := let p := tick a; add2 a a
        def letNotLast (a : UInt64) : UInt64 := let p := tick a; let q := tick p; p
    "#,
    );
    // Still refused: nothing carries the bound call's value to the result —
    // a literal result (`letDrop`), or a result bound BEFORE a later call
    // that must still run (`letNotLast`).
    for name in ["letDrop", "letNotLast"] {
        let refusal =
            trust_clean_origin::plan_clean_origin_body_with_rust_callees(&env, name, &table)
                .unwrap_err();
        assert!(refusal.note().contains("value temporary"), "{}", refusal.note());
        assert!(refusal.note().contains("options"), "{}", refusal.note());
        assert!(!refusal.is_compiler_defect(), "{}", refusal.note());
    }
    // ADMITTED since increment 7: the dead binding is one marked node whose
    // `Call` is emitted, in binding order, before the root — never dropped.
    let plan =
        trust_clean_origin::plan_clean_origin_body_with_rust_callees(&env, "letUnread", &table)
            .expect("a dead `let`-bound call is emitted once, not refused and not dropped");
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::RustCallChain {
            nodes: vec![
                RustCallNode { callee: 0, args: vec![Param(0)], let_binding: Some(0) },
                RustCallNode { callee: 1, args: vec![Param(0), Param(0)], let_binding: None },
            ],
        }
    );
}

#[test]
fn an_opaque_or_transitive_helper_cannot_hide_a_rust_argument_call() {
    let (env, table) = rust_call_environment(
        r#"
        def ignoreValue (a : UInt64) : UInt64 := 0
        def indirectTick (a : UInt64) : UInt64 := tick a
        opaque hiddenTick (a : UInt64) : UInt64 := tick a
        def indirectDrop (a : UInt64) : UInt64 := ignoreValue (indirectTick a)
        def opaqueDrop (a : UInt64) : UInt64 := ignoreValue (hiddenTick a)
    "#,
    );
    for name in ["indirectDrop", "opaqueDrop"] {
        let refusal =
            trust_clean_origin::plan_clean_origin_body_with_rust_callees(&env, name, &table)
                .unwrap_err();
        assert!(refusal.note().contains("value temporary"), "{}", refusal.note());
    }
}

#[test]
fn a_primitive_looking_definition_cannot_hide_a_rust_argument_call() {
    let (env, table) = rust_call_environment(
        "def UInt128.add (a : UInt64) : UInt64 := tick a\n\
         def ignoreValue (a : UInt64) : UInt64 := 0\n\
         def spoofedDrop (a : UInt64) : UInt64 := ignoreValue (UInt128.add a)",
    );
    let refusal =
        trust_clean_origin::plan_clean_origin_body_with_rust_callees(&env, "spoofedDrop", &table)
            .unwrap_err();
    assert!(refusal.note().contains("value temporary"), "{}", refusal.note());
}

#[test]
fn absent_or_incomplete_callee_metadata_cannot_authorize_effect_erasure() {
    let (env, table) = rust_call_environment(
        "def ignoreValue (a : UInt64) : UInt64 := 0\n\
         def dropCall (a : UInt64) : UInt64 := ignoreValue (tick a)\n\
         def letDrop (a : UInt64) : UInt64 := let p := tick a; 0\n\
         def addTwice (a : UInt64) : UInt64 := add2 a a\n\
         def duplicateCall (a : UInt64) : UInt64 := addTwice (tick a)\n\
         def swapValues (a b : UInt64) : UInt64 := add2 b a\n\
         def reorderCall (a b : UInt64) : UInt64 := swapValues (tick a) (tick b)",
    );
    for name in ["dropCall", "letDrop", "duplicateCall", "reorderCall"] {
        assert!(trust_clean_origin::plan_clean_origin_body(&env, name).is_err(), "{name}");
        assert!(
            trust_clean_origin::plan_clean_origin_body_with_rust_callees(&env, name, &table[1..],)
                .is_err(),
            "{name}"
        );
    }
}

#[test]
fn an_unchecked_nonprop_theorem_cannot_hide_a_rust_call() {
    let (mut env, table) = rust_call_environment("def ignoreValue (a : UInt64) : UInt64 := 0");
    let ty = Expr::const_(Name::from_string("UInt64"), vec![]);
    let hidden = Name::from_string("uncheckedTick");
    env.add_decl_structural(Declaration::Theorem {
        name: hidden.clone(),
        level_params: vec![],
        type_: Expr::arrow(ty.clone(), ty.clone()),
        value: Expr::lam(
            BinderInfo::Default,
            ty.clone(),
            Expr::app(Expr::const_(Name::from_string("tick"), vec![]), Expr::bvar(0)),
        ),
    })
    .unwrap();
    let caller = Name::from_string("uncheckedDrop");
    env.add_decl(Declaration::Definition {
        name: caller.clone(),
        level_params: vec![],
        type_: Expr::arrow(ty.clone(), ty.clone()),
        value: Expr::lam(
            BinderInfo::Default,
            ty,
            Expr::app(
                Expr::const_(Name::from_string("ignoreValue"), vec![]),
                Expr::app(Expr::const_(hidden, vec![]), Expr::bvar(0)),
            ),
        ),
        is_reducible: true,
    })
    .unwrap();
    for metadata in [&[][..], table.as_slice()] {
        let refusal = trust_clean_origin::plan_clean_origin_body_with_rust_callees(
            &env,
            "uncheckedDrop",
            metadata,
        )
        .unwrap_err();
        assert!(refusal.note().contains("unchecked theorem"), "{}", refusal.note());
    }
}

#[test]
fn pure_and_identity_substitutions_keep_the_single_rust_call() {
    let (env, table) = rust_call_environment(
        r#"
        def idUInt (a : UInt64) : UInt64 := a
        def keepCall (a : UInt64) : UInt64 := idUInt (tick a)
        def wrapTick (a : UInt64) : UInt64 := tick a
        def throughWrap (a : UInt64) : UInt64 := wrapTick a
        def withPureLet (a : UInt64) : UInt64 := let p := a; tick p
        def withTailLet (a : UInt64) : UInt64 := let p := tick a; p
        def withAliasLet (a : UInt64) : UInt64 := let p := tick a; let q := p; q
        def pureArgument (a : UInt64) : UInt64 := tick (idUInt a)
    "#,
    );
    for name in
        ["keepCall", "throughWrap", "withPureLet", "withTailLet", "withAliasLet", "pureArgument"]
    {
        let plan = trust_clean_origin::plan_clean_origin_body_with_rust_callees(&env, name, &table)
            .unwrap();
        let CleanOriginShape::RustCallChain { nodes } = plan.shape() else {
            panic!("{name}: {:?}", plan.shape())
        };
        assert_eq!(nodes.len(), 1, "{name}");
        assert_eq!(nodes[0].callee, 0);
        assert_eq!(nodes[0].args, vec![trust_clean_origin::RustCallArg::Param(0)]);
    }
}

#[test]
fn a_let_spine_refusal_keeps_its_own_note_not_the_fallbacks_advice() {
    // Review finding N1 (2026-09-16): a `NotEmittable` raised INSIDE
    // `walk_let_spine` — here the residual's argument 1 computes a helper
    // application the chain cannot read — used to fall through to the
    // expansion fallback, whose `Let` arm replaced it with "`let`-bind the
    // call at the TOP" advice the user had already followed. The walk now
    // re-tags it `LetSpine` (not a defect) and the planner returns it
    // verbatim, so the note names the argument and never the stale advice.
    let (env, table) = rust_call_environment(
        r#"
        def idU (x : UInt64) : UInt64 := x
        def viaHelper (x : UInt64) : UInt64 := let y := tick x; add2 y (idU x)
    "#,
    );
    let refusal =
        trust_clean_origin::plan_clean_origin_body_with_rust_callees(&env, "viaHelper", &table)
            .unwrap_err();
    let note = refusal.note();
    assert!(note.contains("argument 1"), "{note}");
    assert!(!note.contains("at the TOP"), "{note}");
    assert!(!refusal.is_compiler_defect(), "{note}");
}

#[test]
fn an_alias_of_the_last_let_temporary_is_the_identity_case() {
    // Review finding N2 (2026-09-16): `let p := tick a; let q := p; q`
    // denotes one call. The alias is pure and zeta'd; what remains is the
    // identity `let p := tick a; p`, and the walk plans exactly that — one
    // ordinary root, no marker (the plan `withTailLet` gets). An alias of an
    // EARLIER temporary stays refused: the later binding's call must still
    // run and a chain has one place for its result. The note used to render
    // an empty binder list for the admitted case; it now names the later
    // binding for the refused one.
    use trust_clean_origin::EmitRefusal;
    let (env, table) = rust_call_environment(
        r#"
        def withTailLet (a : UInt64) : UInt64 := let p := tick a; p
        def withAliasLet (a : UInt64) : UInt64 := let p := tick a; let q := p; q
        def withAliasChain (a : UInt64) : UInt64 := let p := tick a; let q := p; let r := q; r
        def aliasOfEarlier (a : UInt64) : UInt64 := let p := tick a; let q := tick p; let r := p; r
    "#,
    );
    let plan = |name: &str| {
        trust_clean_origin::plan_clean_origin_body_with_rust_callees(&env, name, &table)
    };
    let tail = plan("withTailLet").expect("the identity `let` plans");
    for name in ["withAliasLet", "withAliasChain"] {
        let aliased =
            plan(name).unwrap_or_else(|refusal| panic!("`{name}` is one call: {}", refusal.note()));
        assert_eq!(aliased.shape(), tail.shape(), "`{name}` plans as the identity `let`");
        let CleanOriginShape::RustCallChain { nodes } = aliased.shape() else { panic!("{name}") };
        assert_eq!(nodes.len(), 1, "{name}");
        assert_eq!(nodes[0].let_binding, None, "{name}: the root is never `let`-bound");
    }
    let refusal = plan("aliasOfEarlier")
        .expect_err("`q`'s call must run and nothing carries `p` to the result");
    assert!(matches!(refusal, EmitRefusal::LetSpine { defect: false, .. }), "{refusal:?}");
    assert!(!refusal.is_compiler_defect());
    let note = refusal.note();
    assert!(note.contains("temporary `p`") && note.contains("bound after it by `q`"), "{note}");
    assert!(note.contains("reorder") && note.contains("options"), "{note}");
    assert!(!note.contains("by  are"), "an empty binder list was rendered: {note}");
}

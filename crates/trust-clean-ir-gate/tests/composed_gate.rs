// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! G4 carrier gate, island lane: the `Composed` (nested wrapping-expression)
//! shape. The same independent SSA reader the standalone lane uses reads the
//! ACTUAL emitted body; the kernel decides whole-term defeq against the
//! island declaration. Targeting a plan makes every refusal fatal in the
//! collector, so the targeted set must be exactly what the reader can admit.

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Name};
use trust_certify::clean_island::CleanIslandSession;
use trust_clean_ir_gate::{
    GATED_SHAPE_TAGS, GatedShape, admit_clean_origin, admit_wrapping_binop, gate_targets,
    gates_shape, reflect_gated, reflect_wrapping_binop,
};
use trust_clean_origin::{
    CleanOriginPlan, CleanOriginShape, check_faithful, plan_clean_origin_body,
};
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{FuncId, FuncTyId, ValueId};
use trust_ir::{BinOp, Function, Inst, Module, Producer};

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
    let mut function =
        trust_clean_ir::emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
            .unwrap_or_else(|refusal| panic!("`{name}` must emit: {refusal}"));
    // WS5.2: the crate lane's subject is named by the Rust item's link-time symbol.
    bind_fixture_link_symbol(&mut function);
    (plan, signature, function)
}

/// The collector's WS5.2 binding, over a deterministic fixture symbol: the crate lane's gate
/// (`admit_clean_origin`) binds the plan through `display_path` and requires a link-time symbol
/// as the name (`trust_thir_lower::link_symbol::bind_clean_origin_link_symbol` does this in the
/// collector; this crate has no `tcx`, and the gate does not compute the symbol).
fn bind_fixture_link_symbol(function: &mut Function) {
    assert!(function.display_path.is_none(), "the emitter leaves display_path to the binder");
    let symbol = format!("_RNvCs0_7fixture{}", function.name.len());
    let lean = std::mem::replace(&mut function.name, symbol);
    function.name.push_str(&lean.replace('.', "_"));
    function.display_path = Some(lean);
}

/// The `index`-th BinOp of the single block, mutably.
fn nth_binop(function: &mut Function, index: usize) -> &mut Inst {
    function.blocks[0]
        .body
        .iter_mut()
        .map(|node| &mut node.inst)
        .filter(|inst| matches!(inst, Inst::BinOp { .. }))
        .nth(index)
        .expect("fixture has that many BinOps")
}

fn positive_sources() -> Vec<String> {
    let mut sources = Vec::new();
    for w in WIDTHS {
        let max = (1_u128 << w) - 1;
        sources.push(format!("def mix{w} (a b : UInt{w}) : UInt{w} := (a + b) * a"));
        sources.push(format!("def deep{w} (a b : UInt{w}) : UInt{w} := ((a + b) - a) * (b + 3)"));
        sources.push(format!("def maxleaf{w} (a b : UInt{w}) : UInt{w} := (a + {max}) - b"));
        // The carrier spelling of the same tree: the planner's second
        // measured spelling, reaching the same reader and kernel.
        sources.push(format!(
            "def carrier{w} (a b : UInt{w}) : UInt{w} := UInt{w}.mul (UInt{w}.add a b) a"
        ));
    }
    sources
}

#[test]
fn composed_is_a_gated_tag_matching_the_collector_rendering() {
    // `clean_origin_ir.rs::shape_tag` renders `CleanOriginShape::Composed` as
    // "composed"; the join refuses a token on any tag outside this list.
    assert!(gates_shape("composed"));
    assert_eq!(GATED_SHAPE_TAGS.len(), 4);
    assert_eq!(GatedShape::Composed { ops: 2 }.tag(), "composed");
    let collector = include_str!("../../../compiler/rustc_mir_transform/src/clean_origin_ir.rs");
    assert!(collector.contains("S::Composed { .. } => \"composed\","));
}

#[test]
fn composed_plans_at_every_width_are_targeted_minted_and_authenticated() {
    let env = island(&positive_sources());
    let mut admitted = 0;
    for w in WIDTHS {
        for (prefix, ops) in [("mix", 2), ("deep", 4), ("maxleaf", 2), ("carrier", 2)] {
            let name = format!("{prefix}{w}");
            let (plan, signature, function) = emitted(&env, &name);
            assert!(
                matches!(plan.shape(), CleanOriginShape::Composed { .. }),
                "`{name}` must plan as Composed, got {:?}",
                plan.shape()
            );
            assert!(gate_targets(&plan), "`{name}` must be a carrier-gate target");
            let token = admit_clean_origin(&env, &plan, 7, &name, &signature, &function)
                .unwrap_or_else(|refusal| panic!("`{name}` gate refused: {}", refusal.note()));
            assert_eq!(token.shape(), GatedShape::Composed { ops });
            assert_eq!(token.carrier_tag(), format!("UInt{w}"));
            assert_eq!(token.method_tag(), "definitional-equality");
            token
                .authenticate(&name, 7, &name, &signature, &function)
                .unwrap_or_else(|refusal| panic!("`{name}` token refused: {}", refusal.note()));
            let mut published = function.clone();
            published.id = FuncId::new(21);
            published.ty = FuncTyId::new(4);
            published.producer = Some(Producer::Clean);
            let sealed = token
                .authenticate_published(&name, 7, &name, &signature, &function, &published)
                .unwrap_or_else(|refusal| panic!("`{name}` publication: {}", refusal.note()));
            assert_eq!(sealed.shape(), GatedShape::Composed { ops });
            assert_ne!(sealed.subject_digest(), token.subject_digest());
            // The legacy single-op entry point stays exactly as narrow.
            let refusal = admit_wrapping_binop(&env, &plan, 7, &name, &signature, &function)
                .expect_err("the wrapping-binop wrapper admits only WrappingBinOp plans");
            assert_eq!(refusal.stage(), "target-shape", "{}", refusal.note());
            admitted += 1;
        }
    }
    assert_eq!(admitted, 16);
}

#[test]
fn admitted_uint64_composition_wraps_through_the_intermediate() {
    let env = island(&positive_sources());
    let (plan, signature, function) = emitted(&env, "mix64");
    admit_clean_origin(&env, &plan, 1, "m::mix64", &signature, &function).expect("gate admits");
    let run = |a: u64, b: u64| {
        let outcome = Interpreter::new()
            .execute_function(
                &function,
                vec![
                    InterpretValue::int(Ty::U64, i128::from(a)).expect("a"),
                    InterpretValue::int(Ty::U64, i128::from(b)).expect("b"),
                ],
            )
            .expect("emitted TrustIR executes");
        outcome.returns[0].as_int().expect("integer").as_unsigned()
    };
    assert_eq!(run(2, 3), 10);
    assert_eq!(run(u64::MAX, 1), 0, "(u64::MAX + 1) wraps to 0 before the multiply");
}

#[test]
fn a_thirty_two_op_chain_is_targeted_and_admitted_and_thirty_three_never_plans() {
    let chain = |ops: usize| {
        let mut body = String::from("a");
        for _ in 0..ops {
            body = format!("({body} + 1)");
        }
        body
    };
    let env = island(&[format!("def chain32 (a : UInt16) : UInt16 := {}", chain(32))]);
    let (plan, signature, function) = emitted(&env, "chain32");
    assert!(gate_targets(&plan));
    assert_eq!(function.blocks[0].body.len(), 65, "32 Const + 32 BinOp + Return");
    let token = admit_clean_origin(&env, &plan, 2, "m::chain32", &signature, &function)
        .unwrap_or_else(|refusal| panic!("32-op chain refused: {}", refusal.note()));
    assert_eq!(token.shape(), GatedShape::Composed { ops: 32 });

    let env = island(&[format!("def chain33 (a : UInt16) : UInt16 := {}", chain(33))]);
    plan_clean_origin_body(&env, "chain33")
        .expect_err("33 ops is past COMPOSED_MAX_OPS: no plan, so nothing to target");
}

#[test]
fn sub_operand_swap_is_refused_while_its_unswapped_twin_admits() {
    let env = island(&["def dsub (a b : UInt64) : UInt64 := (a - b) * a".to_owned()]);
    let (plan, signature, function) = emitted(&env, "dsub");
    // The close twin: the unmutated body admits.
    admit_clean_origin(&env, &plan, 3, "m::dsub", &signature, &function)
        .expect("the emitted body is the declaration");
    let mut swapped = function.clone();
    let Inst::BinOp { op: BinOp::Sub, lhs, rhs, .. } = nth_binop(&mut swapped, 0) else {
        panic!("post-order: the Sub node comes first")
    };
    std::mem::swap(lhs, rhs);
    let reflected = reflect_gated(&signature, &swapped).expect("still a well-formed tree");
    assert_eq!(reflected.shape(), GatedShape::Composed { ops: 2 });
    let refusal = admit_clean_origin(&env, &plan, 3, "m::dsub", &signature, &swapped)
        .expect_err("(b - a) * a is not (a - b) * a");
    assert_eq!(refusal.stage(), "kernel-disagreement", "{}", refusal.note());
}

#[test]
fn emitted_mul_where_the_declaration_says_add_is_a_kernel_disagreement() {
    let env = island(&["def dmix (a b : UInt64) : UInt64 := (a + b) * a".to_owned()]);
    let (plan, signature, function) = emitted(&env, "dmix");
    let token =
        admit_clean_origin(&env, &plan, 4, "m::dmix", &signature, &function).expect("gate admits");
    let mut wrong = function.clone();
    let Inst::BinOp { op, .. } = nth_binop(&mut wrong, 0) else { unreachable!() };
    assert_eq!(*op, BinOp::Add, "post-order: the inner Add comes first");
    *op = BinOp::Mul;
    let refusal = admit_clean_origin(&env, &plan, 4, "m::dmix", &signature, &wrong)
        .expect_err("(a * b) * a is not (a + b) * a");
    assert_eq!(refusal.stage(), "kernel-disagreement", "{}", refusal.note());
    // The reflected term alone is refused by the kernel as well.
    let reflected = reflect_gated(&signature, &wrong).expect("a well-formed tree");
    check_faithful(&env, plan.name(), reflected.term(), plan.result_carrier())
        .expect_err("kernel must not identify the mutated tree with the declaration");
    // An already-minted token is stale on the mutated body.
    let refusal = token
        .authenticate("dmix", 4, "m::dmix", &signature, &wrong)
        .expect_err("digest-bound token must be stale after mutation");
    assert_eq!(refusal.stage(), "token-digest", "{}", refusal.note());
}

#[test]
fn a_shared_computed_node_or_dead_value_is_refused_by_the_reader() {
    let env = island(&["def dmix (a b : UInt64) : UInt64 := (a + b) * a".to_owned()]);
    let (_plan, signature, function) = emitted(&env, "dmix");
    // `(a + b) * (a + b)` spelled as a DAG: the sum's value read twice.
    let mut shared = function.clone();
    let sum = shared.blocks[0].body[0].results[0];
    let Inst::BinOp { rhs, .. } = nth_binop(&mut shared, 1) else { unreachable!() };
    *rhs = sum;
    let refusal = reflect_gated(&signature, &shared).expect_err("shared computed node");
    assert_eq!(refusal.stage(), "expression-tree", "{}", refusal.note());
    // A dead extra BinOp: returned tree no longer consumes every value.
    let mut dead = function.clone();
    let mut extra = dead.blocks[0].body[0].clone();
    extra.results = vec![ValueId::new(99)];
    dead.blocks[0].body.insert(0, extra);
    let refusal = reflect_gated(&signature, &dead).expect_err("dead computed value");
    assert_eq!(refusal.stage(), "expression-tree", "{}", refusal.note());
}

#[test]
fn plan_and_body_family_disagreement_is_refused_before_the_kernel() {
    let env = island(&[
        "def dmix (a b : UInt8) : UInt8 := (a + b) * a".to_owned(),
        "def dadd (a b : UInt8) : UInt8 := a + b".to_owned(),
        "def dtri (a b : UInt8) : UInt8 := ((a + b) * a) - b".to_owned(),
    ]);
    let (mix_plan, signature, mix_body) = emitted(&env, "dmix");
    let (add_plan, _, add_body) = emitted(&env, "dadd");
    let (_, _, tri_body) = emitted(&env, "dtri");
    let renamed = |body: &Function, to: &Function| {
        let mut body = body.clone();
        body.name = to.name.clone();
        body.display_path = to.display_path.clone();
        body
    };
    // Composed plan, single-op body.
    let refusal =
        admit_clean_origin(&env, &mix_plan, 5, "m", &signature, &renamed(&add_body, &mix_body))
            .expect_err("a composed plan must not accept a single BinOp body");
    assert_eq!(refusal.stage(), "plan-shape", "{}", refusal.note());
    // Composed plan (2 ops), 3-op body: same family, node count disagrees.
    let refusal =
        admit_clean_origin(&env, &mix_plan, 5, "m", &signature, &renamed(&tri_body, &mix_body))
            .expect_err("node count is part of the plan/body belt");
    assert_eq!(refusal.stage(), "plan-shape", "{}", refusal.note());
    // Wrapping-binop plan, composed body.
    let refusal =
        admit_clean_origin(&env, &add_plan, 5, "m", &signature, &renamed(&mix_body, &add_body))
            .expect_err("a single-op plan must not accept a composed body");
    assert_eq!(refusal.stage(), "plan-shape", "{}", refusal.note());
    // The historical single-op reflector keeps refusing a composed body.
    let refusal = reflect_wrapping_binop(&signature, &mix_body).expect_err("two BinOps");
    assert_eq!(refusal.stage(), "shape", "{}", refusal.note());
}

#[test]
fn composed_subject_digest_uses_its_own_domain() {
    let env = island(&["def dmix (a b : UInt32) : UInt32 := (a + b) * a".to_owned()]);
    let (plan, signature, function) = emitted(&env, "dmix");
    let token = admit_clean_origin(&env, &plan, 7, "fixture::body", &signature, &function)
        .expect("gate admits");
    let image = |domain: &str| {
        let mut module = Module::new(format!("{domain}::def-index=7::def-path=fixture::body"));
        module.func_types.push(signature.clone());
        module.functions.push(function.clone());
        module.stable_digest()
    };
    assert_eq!(
        token.subject_digest(),
        image("@trust-internal::clean-carrier-gate-composed-subject-v1")
    );
    for other in [
        "@trust-internal::clean-carrier-gate-subject-v2",
        "@trust-internal::clean-wrapping-binop-gate-subject-v1",
    ] {
        assert_ne!(token.subject_digest(), image(other));
    }
}

/// Composed-looking island programs OUTSIDE the reflectable subset never
/// become targets, so the collector's fatal-on-refusal policy cannot reach
/// them: each either never plans as `Composed` (and keeps whatever row it
/// had) or, if it plans, is not targeted.
#[test]
fn composed_look_alikes_outside_the_subset_are_never_targeted() {
    let mut planned = Vec::new();
    for (name, source) in [
        ("mixed8", "def mixed8 (a b : UInt8) (unused : UInt64) : UInt8 := (a + b) + a"),
        ("natmix", "def natmix (a b : Nat) : Nat := (a + b) * a"),
        ("bvmix", "def bvmix (a b : BitVec 8) : BitVec 8 := (a + b) * a"),
    ] {
        let mut session = CleanIslandSession::new();
        if session.check(source).is_rejected() {
            continue;
        }
        let env = session.environment().expect("untainted session");
        let Ok(plan) = plan_clean_origin_body(env, name) else { continue };
        assert!(
            !gate_targets(&plan),
            "`{name}` is outside the reader's subset but was targeted: {:?}",
            plan.shape()
        );
        planned.push(name);
    }
    // Recorded, not asserted: which look-alikes reach a plan at all is the
    // planner's business; the claim here is only that none is targeted.
    eprintln!("look-alikes that planned (untargeted): {planned:?}");
}

/// Sources of `tests/ui/trust/clean_origin_named_lean_calls.rs`, verbatim, plus
/// the same trees written without a helper.
fn helper_sources() -> Vec<String> {
    [
        "def plusOne (a : UInt64) : UInt64 := a + 1",
        "def square (a : UInt64) : UInt64 := a * a",
        "def nestedCall (a : UInt64) : UInt64 := square (plusOne a)",
        "def leafCall (a b : UInt64) : UInt64 := plusOne a * b",
        "def directNested (a : UInt64) : UInt64 := (a + 1) * (a + 1)",
        "def directLeaf (a b : UInt64) : UInt64 := (a + 1) * b",
        "def letNested (a : UInt64) : UInt64 := let t := a + 1; t * t",
    ]
    .map(str::to_owned)
    .to_vec()
}

/// The collector mints a kernel-TV companion from the declaration's ORIGINAL
/// value (`clean_reflect::denote_source`: no delta, no metadata), and the join
/// makes a targeted row with no companion FATAL. A tree the planner reached by
/// expanding a Lean helper therefore must not be targeted: it keeps the
/// untargeted route (gate `None`, tier decided by the companion as before).
/// The helper-free twin of the same tree is targeted and admitted.
#[test]
fn a_composed_tree_reached_through_a_named_helper_is_planned_but_never_targeted() {
    let env = island(&helper_sources());
    for (name, ops) in [("nestedCall", 3), ("leafCall", 2)] {
        let (plan, signature, function) = emitted(&env, name);
        assert!(
            matches!(plan.shape(), CleanOriginShape::Composed { .. }),
            "`{name}` must still PLAN as Composed (the planner expands the helper), got {:?}",
            plan.shape()
        );
        assert!(!plan.source_is_direct(), "`{name}` is headed by a helper call");
        assert!(!gate_targets(&plan), "`{name}` must not be a carrier-gate target");
        // The body itself is inside the reader's subset — only targeting keeps
        // it off the gate, and the gate refuses to mint for an untargeted plan.
        assert_eq!(
            reflect_gated(&signature, &function).expect("reader admits the body").shape(),
            GatedShape::Composed { ops }
        );
        let refusal = admit_clean_origin(&env, &plan, 3, name, &signature, &function)
            .expect_err("an untargeted plan never gets a token");
        assert_eq!(refusal.stage(), "target-shape", "{}", refusal.note());
    }
    for (name, ops) in [("directNested", 3), ("directLeaf", 2), ("letNested", 3)] {
        let (plan, signature, function) = emitted(&env, name);
        assert!(
            matches!(plan.shape(), CleanOriginShape::Composed { .. }),
            "`{name}` must plan as Composed, got {:?}",
            plan.shape()
        );
        assert!(plan.source_is_direct(), "`{name}` is written without a helper");
        assert!(gate_targets(&plan), "`{name}` must be a carrier-gate target");
        let token = admit_clean_origin(&env, &plan, 3, name, &signature, &function)
            .unwrap_or_else(|refusal| panic!("`{name}` gate refused: {}", refusal.note()));
        assert_eq!(token.shape(), GatedShape::Composed { ops });
    }
}

/// Kernel-check a binary `UInt64` definition built by hand. No measured island
/// spelling leaves metadata in a value (type ascription and `show` elaborate
/// to the bare op), so the metadata-wrapped rows below are built here; the
/// planner strips `MData` (`strip_mdata`), the compiler's kernel-TV companion
/// (`clean_reflect::denote_source`, no `MData` arm) does not.
fn define(env: &mut Environment, name: &str, value: Expr) {
    let uint64 = Expr::const_str("UInt64");
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::arrow(uint64.clone(), Expr::arrow(uint64.clone(), uint64)),
        value,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("`{name}` must kernel-check as written: {e:?}"));
}

/// `fun (a b : UInt64) => body`, with `a = bvar 1` and `b = bvar 0`.
fn lam2(body: Expr) -> Expr {
    let uint64 = Expr::const_str("UInt64");
    Expr::lam(BinderInfo::Default, uint64.clone(), Expr::lam(BinderInfo::Default, uint64, body))
}

fn carrier_op(op: &str, left: Expr, right: Expr) -> Expr {
    Expr::apps(Expr::const_str(&format!("UInt64.{op}")), [left, right])
}

/// Single wrapping ops, each of add/sub/mul reached both through a source
/// construct the kernel-TV companion cannot read and directly.
fn wrapping_sources() -> Vec<String> {
    [
        "def helperAdd (a b : UInt64) : UInt64 := a + b",
        "def helperSub (a b : UInt64) : UInt64 := a - b",
        "def helperMul (a b : UInt64) : UInt64 := a * b",
        // Unreadable by the companion: a helper head, a prelude head, and
        // dead `let`s the planner zeta-drops but the companion denotes eagerly.
        "def chain (a b : UInt64) : UInt64 := helperAdd a b",
        "def chainSub (a b : UInt64) : UInt64 := helperSub a b",
        "def chainMul (a b : UInt64) : UInt64 := helperMul a b",
        "def viaId (a b : UInt64) : UInt64 := id (a - b)",
        "def deadHelper (a b : UInt64) : UInt64 := let t : UInt64 := helperAdd a b; a * b",
        "def deadMatch (a b : UInt64) : UInt64 := \
         let t : UInt64 := match a == b with | true => a | false => b; a - b",
        // Readable: both spellings, a `UIntW` let, a max-width literal.
        "def plain (a b : UInt64) : UInt64 := a + b",
        "def plainSub (a b : UInt64) : UInt64 := a - b",
        "def plainMul (a b : UInt64) : UInt64 := a * b",
        "def carrierSub (a b : UInt64) : UInt64 := UInt64.sub a b",
        "def letMul (a b : UInt64) : UInt64 := let t : UInt64 := a; t * b",
        "def litMul (a : UInt64) : UInt64 := a * 18446744073709551615",
    ]
    .map(str::to_owned)
    .to_vec()
}

/// Regression (was the pin `wrapping_binop_targeting_is_unchanged_including_
/// the_known_helper_exposure`): `WrappingBinOp` was targeted unconditionally,
/// so a single op the planner reached through a helper was fatal at stage1
/// with verification on — docs/audits/2026-09-28-true-state-trust-ir-to-
/// codegen.md M2d, "the expected kernel-TV companion is missing … source
/// construct headed by `helperAdd`". Such a row still PLANS and its emitted
/// body is still the reader's; it is simply not targeted, so it keeps the
/// untargeted route. Every helper-free twin stays targeted and admitted.
#[test]
fn a_wrapping_binop_the_companion_cannot_read_is_planned_but_never_targeted() {
    let mut env = island(&wrapping_sources());
    let tag = |e: Expr| Expr::mdata(Vec::new(), e);
    define(&mut env, "taggedSub", lam2(tag(carrier_op("sub", Expr::bvar(1), Expr::bvar(0)))));
    define(&mut env, "taggedLeafMul", lam2(carrier_op("mul", tag(Expr::bvar(1)), Expr::bvar(0))));
    // The metadata-free twin, built the same way, so only the tag differs.
    define(&mut env, "untaggedSub", lam2(carrier_op("sub", Expr::bvar(1), Expr::bvar(0))));

    let mut untargeted = 0;
    for name in [
        "chain",
        "chainSub",
        "chainMul",
        "viaId",
        "deadHelper",
        "deadMatch",
        "taggedSub",
        "taggedLeafMul",
    ] {
        let (plan, signature, function) = emitted(&env, name);
        assert!(
            matches!(plan.shape(), CleanOriginShape::WrappingBinOp { .. }),
            "`{name}` must still PLAN as WrappingBinOp, got {:?}",
            plan.shape()
        );
        assert!(!plan.source_is_direct(), "`{name}`'s own value is not the op");
        assert!(!gate_targets(&plan), "`{name}` must not be a carrier-gate target");
        // The body itself is inside the reader's subset — only targeting
        // keeps it off the gate, and neither entry point mints for it.
        assert_eq!(
            reflect_gated(&signature, &function).expect("reader admits the body").shape(),
            GatedShape::WrappingBinOp
        );
        for refusal in [
            admit_clean_origin(&env, &plan, 3, name, &signature, &function)
                .expect_err("an untargeted plan never gets a token"),
            admit_wrapping_binop(&env, &plan, 3, name, &signature, &function)
                .expect_err("nor through the legacy wrapping-binop entry"),
        ] {
            assert_eq!(refusal.stage(), "target-shape", "{}", refusal.note());
        }
        untargeted += 1;
    }
    assert_eq!(untargeted, 8);

    let mut targeted = 0;
    for name in ["plain", "plainSub", "plainMul", "carrierSub", "letMul", "litMul", "untaggedSub"] {
        let (plan, signature, function) = emitted(&env, name);
        assert!(
            matches!(plan.shape(), CleanOriginShape::WrappingBinOp { .. }),
            "`{name}` must plan as WrappingBinOp, got {:?}",
            plan.shape()
        );
        assert!(plan.source_is_direct(), "`{name}` is written without a helper");
        assert!(gate_targets(&plan), "`{name}` must be a carrier-gate target");
        let token = admit_clean_origin(&env, &plan, 3, name, &signature, &function)
            .unwrap_or_else(|refusal| panic!("`{name}` gate refused: {}", refusal.note()));
        assert_eq!(token.shape(), GatedShape::WrappingBinOp);
        admit_wrapping_binop(&env, &plan, 3, name, &signature, &function)
            .unwrap_or_else(|refusal| panic!("`{name}` legacy entry refused: {}", refusal.note()));
        targeted += 1;
    }
    assert_eq!(targeted, 7);
}

/// User-defined comparisons under the names the companion's Fragment-3a
/// condition recognizes (`clean_reflect::denote_source_cond` matches the head
/// by NAME), at every width, plus dead `let`s that eliminate over them in the
/// three spellings it reads. The planner zetas the dead value away, so each
/// row plans as a single wrapping op (or a composed tree); the companion
/// denotes the value eagerly, reads it, and discards it.
fn conditional_sources() -> Vec<String> {
    let mut sources = Vec::new();
    for w in WIDTHS {
        let t = format!("UInt{w}");
        for (cmp, prop) in [("blt", "a < b"), ("ble", "a ≤ b"), ("beq", "a = b")] {
            sources.push(format!("def {t}.{cmp} (a b : {t}) : Bool := decide ({prop})"));
        }
        sources.extend([
            format!(
                "def casesAdd{w} (a b : {t}) : {t} := let t : {t} := \
                 Bool.casesOn (motive := fun _ => {t}) ({t}.blt a b) a b; a + b"
            ),
            format!(
                "def matchSub{w} (a b : {t}) : {t} := let t : {t} := \
                 match {t}.blt a b with | true => a | false => b; a - b"
            ),
            format!(
                "def recMul{w} (a b : {t}) : {t} := let t : {t} := \
                 @Bool.rec (fun _ => {t}) b a ({t}.blt a b); a * b"
            ),
            format!(
                "def beqSub{w} (a b : {t}) : {t} := let t : {t} := \
                 match {t}.beq a b with | true => a | false => b; a - b"
            ),
            format!(
                "def bleAdd{w} (a b : {t}) : {t} := let t : {t} := \
                 Bool.casesOn (motive := fun _ => {t}) ({t}.ble a b) (a + 1) b; a + b"
            ),
            format!(
                "def casesTree{w} (a b : {t}) : {t} := let t : {t} := \
                 Bool.casesOn (motive := fun _ => {t}) ({t}.blt a b) a b; (a + b) * a"
            ),
        ]);
    }
    sources
}

/// Regression for the review of this narrowing: `denote_source` also reads a
/// `cond` / `Bool.rec` / `Bool.casesOn` over `UIntW.{blt,ble,beq}`, and an
/// island CAN spell those comparisons by defining them. A wrapping row with
/// such a value in a dead `let` was targeted, admitted and companion-readable
/// before the direct-source condition existed, so the condition must keep it
/// targeted — `direct_source::reads_directly` carries the same arm. The
/// composed twin, untargeted before that arm, is now targeted and admitted.
#[test]
fn a_dead_conditional_the_companion_reads_stays_targeted_and_admitted() {
    let env = island(&conditional_sources());
    let mut rows = 0;
    for w in WIDTHS {
        for (name, composed_ops) in [
            (format!("casesAdd{w}"), None),
            (format!("matchSub{w}"), None),
            (format!("recMul{w}"), None),
            (format!("beqSub{w}"), None),
            (format!("bleAdd{w}"), None),
            (format!("casesTree{w}"), Some(2)),
        ] {
            let (plan, signature, function) = emitted(&env, &name);
            let expected = match composed_ops {
                None => {
                    assert!(
                        matches!(plan.shape(), CleanOriginShape::WrappingBinOp { .. }),
                        "`{name}` must plan as WrappingBinOp, got {:?}",
                        plan.shape()
                    );
                    GatedShape::WrappingBinOp
                }
                Some(ops) => {
                    assert!(
                        matches!(plan.shape(), CleanOriginShape::Composed { .. }),
                        "`{name}` must plan as Composed, got {:?}",
                        plan.shape()
                    );
                    GatedShape::Composed { ops }
                }
            };
            assert!(plan.source_is_direct(), "`{name}`'s dead conditional is readable");
            assert!(gate_targets(&plan), "`{name}` must stay a carrier-gate target");
            let token = admit_clean_origin(&env, &plan, 3, &name, &signature, &function)
                .unwrap_or_else(|refusal| panic!("`{name}` gate refused: {}", refusal.note()));
            assert_eq!(token.shape(), expected);
            if composed_ops.is_none() {
                admit_wrapping_binop(&env, &plan, 3, &name, &signature, &function)
                    .unwrap_or_else(|r| panic!("`{name}` legacy entry refused: {}", r.note()));
            }
            rows += 1;
        }
    }
    assert_eq!(rows, 24);
}

/// The two LEAF shapes, each reached both through a source construct the
/// kernel-TV companion cannot read and directly, at every width. The
/// unreadable rows are the 2026-09-29 stage1 fatals (`pathPick`, `useK`, the
/// island of `tests/ui/trust/clean_origin_named_lean_calls.rs`) and their
/// siblings: a helper head, a prelude head, a helper in a dead `let`.
fn leaf_sources() -> Vec<String> {
    let mut sources = Vec::new();
    for w in WIDTHS {
        let t = format!("UInt{w}");
        let max = (1_u128 << w) - 1;
        sources.extend([
            format!("def pick{w} (a b : {t}) : {t} := a"),
            format!("def kFive{w} (a : {t}) : {t} := 5"),
            // Unreadable by the companion.
            format!("def pathPick{w} (a b : {t}) : {t} := pick{w} a b"),
            format!("def useK{w} (a : {t}) : {t} := kFive{w} a"),
            format!("def viaIdPick{w} (a b : {t}) : {t} := id b"),
            format!("def viaIdK{w} (a : {t}) : {t} := id 9"),
            format!("def deadPick{w} (a b : {t}) : {t} := let t : {t} := pick{w} a b; b"),
            format!("def deadK{w} (a : {t}) : {t} := let t : {t} := kFive{w} a; 3"),
            // Readable: a bare leaf, a live `UIntW` let, a readable dead
            // `let`, the max literal, a nullary constant.
            format!("def snd{w} (a b : {t}) : {t} := b"),
            format!("def letSnd{w} (a b : {t}) : {t} := let t : {t} := b; t"),
            format!("def deadSnd{w} (a b : {t}) : {t} := let t : {t} := a + 1; b"),
            format!("def kMax{w} (a b : {t}) : {t} := {max}"),
            format!("def kNull{w} : {t} := 7"),
            format!("def letK{w} (a : {t}) : {t} := let t : {t} := 11; t"),
        ]);
    }
    sources
}

/// Regression (2026-09-29, stage1 of 3c29e31164 with verification on):
/// `Projection` and `ConstantUint` were targeted on the carrier belt alone, so
/// a leaf the planner reached through a helper (`pathPick a b := pick a b`,
/// `useK a := kFive a`) was FATAL — "carrier-gated … `pathPick`: the expected
/// kernel-TV companion is missing … headed by `pick`". Such a row still PLANS
/// and its emitted body is still the reader's; it is simply not targeted. Every
/// directly written twin stays targeted and admitted.
#[test]
fn a_projection_or_constant_the_companion_cannot_read_is_planned_but_never_targeted() {
    let mut env = island(&leaf_sources());
    let tag = |e: Expr| Expr::mdata(Vec::new(), e);
    // No measured island spelling leaves metadata on a value, so the tagged
    // rows (and their untagged twin, so only the tag differs) are built here.
    define(&mut env, "taggedSnd", lam2(tag(Expr::bvar(0))));
    define(&mut env, "untaggedSnd", lam2(Expr::bvar(0)));
    // The carrier numeral spelling over a raw literal (the island writes
    // `UInt64.ofNat 13` with a `Nat` numeral argument, which does not plan),
    // tagged and bare.
    let carrier_numeral = |k: u64| Expr::apps(Expr::const_str("UInt64.ofNat"), [Expr::nat_lit(k)]);
    define(&mut env, "taggedK", lam2(tag(carrier_numeral(4))));
    define(&mut env, "carrierK", lam2(carrier_numeral(13)));

    let leaf = |plan: &CleanOriginPlan| match plan.shape() {
        CleanOriginShape::Projection { projected } => {
            GatedShape::Projection { projected: *projected }
        }
        CleanOriginShape::ConstantUint { value } => {
            GatedShape::ConstantUint { value: u64::try_from(*value).expect("in range") }
        }
        other => panic!("`{}` must plan as a leaf shape, got {other:?}", plan.name()),
    };

    let mut untargeted = Vec::new();
    for w in WIDTHS {
        for (prefix, expected) in [
            ("pathPick", GatedShape::Projection { projected: 0 }),
            ("useK", GatedShape::ConstantUint { value: 5 }),
            ("viaIdPick", GatedShape::Projection { projected: 1 }),
            ("viaIdK", GatedShape::ConstantUint { value: 9 }),
            ("deadPick", GatedShape::Projection { projected: 1 }),
            ("deadK", GatedShape::ConstantUint { value: 3 }),
        ] {
            untargeted.push((format!("{prefix}{w}"), expected));
        }
    }
    untargeted.push(("taggedSnd".into(), GatedShape::Projection { projected: 1 }));
    untargeted.push(("taggedK".into(), GatedShape::ConstantUint { value: 4 }));
    let mut refused = 0;
    for (name, expected) in &untargeted {
        let (plan, signature, function) = emitted(&env, name);
        assert_eq!(leaf(&plan), *expected, "`{name}` must still PLAN as that leaf");
        assert!(!plan.source_is_direct(), "`{name}`'s own value is not the leaf");
        assert!(!gate_targets(&plan), "`{name}` must not be a carrier-gate target");
        // The body itself is inside the reader's subset — only targeting
        // keeps it off the gate, and the gate refuses to mint for it.
        assert_eq!(
            reflect_gated(&signature, &function).expect("reader admits the body").shape(),
            *expected
        );
        let refusal = admit_clean_origin(&env, &plan, 3, name, &signature, &function)
            .expect_err("an untargeted plan never gets a token");
        assert_eq!(refusal.stage(), "target-shape", "{}", refusal.note());
        refused += 1;
    }
    assert_eq!(refused, 26);

    let mut targeted = Vec::new();
    for w in WIDTHS {
        let max = u64::try_from((1_u128 << w) - 1).expect("fits");
        for (prefix, expected) in [
            ("pick", GatedShape::Projection { projected: 0 }),
            ("kFive", GatedShape::ConstantUint { value: 5 }),
            ("snd", GatedShape::Projection { projected: 1 }),
            ("letSnd", GatedShape::Projection { projected: 1 }),
            ("deadSnd", GatedShape::Projection { projected: 1 }),
            ("kMax", GatedShape::ConstantUint { value: max }),
            ("kNull", GatedShape::ConstantUint { value: 7 }),
            ("letK", GatedShape::ConstantUint { value: 11 }),
        ] {
            targeted.push((format!("{prefix}{w}"), expected));
        }
    }
    targeted.push(("untaggedSnd".into(), GatedShape::Projection { projected: 1 }));
    targeted.push(("carrierK".into(), GatedShape::ConstantUint { value: 13 }));
    let mut admitted = 0;
    for (name, expected) in &targeted {
        let (plan, signature, function) = emitted(&env, name);
        assert_eq!(leaf(&plan), *expected, "`{name}` must plan as that leaf");
        assert!(plan.source_is_direct(), "`{name}` is written without a helper");
        assert!(gate_targets(&plan), "`{name}` must be a carrier-gate target");
        let token = admit_clean_origin(&env, &plan, 3, name, &signature, &function)
            .unwrap_or_else(|refusal| panic!("`{name}` gate refused: {}", refusal.note()));
        assert_eq!(token.shape(), *expected);
        token
            .authenticate(name, 3, name, &signature, &function)
            .unwrap_or_else(|refusal| panic!("`{name}` token refused: {}", refusal.note()));
        admitted += 1;
    }
    assert_eq!(admitted, 34);
}

/// The token-name belt compares KERNEL names, reading the append subject with
/// the parser the compiler derived the plan's declaration with. The registry
/// spells a one-component name containing a dot as `«A.b»`; the dotted
/// display reader (`Name::from_string`) named a different constant, so a
/// correctly minted token for it was refused FATALLY at the join (2026-09-29:
/// "token-name: permission names `A.b` but append subject names `«A.b»`").
/// Exactness is kept in both directions: the two-component `A.b` and the
/// one-component `«A.b»` never authenticate as each other.
#[test]
fn the_token_name_belt_reads_the_subjects_source_spelling_exactly() {
    let env = island(&[
        "def «A.b» (a b : UInt64) : UInt64 := b + 1".to_owned(),
        "def A.b (a b : UInt64) : UInt64 := a + b".to_owned(),
        "def «x.y».z (a : UInt64) : UInt64 := a".to_owned(),
    ]);
    let quoted = trust_certify::clean_island::island_source_name("«A.b»").expect("parses");
    let dotted = trust_certify::clean_island::island_source_name("A.b").expect("parses");
    let mixed = trust_certify::clean_island::island_source_name("«x.y».z").expect("parses");
    assert_ne!(quoted, dotted, "one component is not two");
    assert_ne!(Name::from_string("«A.b»"), quoted, "the display reader is not the source reader");
    for (spelling, declaration, other) in
        [("«A.b»", &quoted, "A.b"), ("A.b", &dotted, "«A.b»"), ("«x.y».z", &mixed, "x.y.z")]
    {
        assert_eq!(
            trust_certify::clean_island::island_source_spelling(declaration).as_deref(),
            Some(spelling),
            "the canonical spelling round-trips"
        );
        let plan = trust_clean_origin::plan_clean_origin_body_with_rust_callees_for_name(
            &env,
            declaration,
            &[],
        )
        .unwrap_or_else(|refusal| panic!("`{spelling}` must plan: {refusal:?}"));
        assert!(gate_targets(&plan), "`{spelling}` is direct and must be targeted");
        let signature = trust_clean_ir::trust_ir_func_ty(plan.signature()).expect("lowers");
        let mut function =
            trust_clean_ir::emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
                .expect("emits");
        bind_fixture_link_symbol(&mut function);
        let token = admit_clean_origin(&env, &plan, 5, "probe::f", &signature, &function)
            .unwrap_or_else(|refusal| panic!("`{spelling}` gate refused: {}", refusal.note()));
        token
            .authenticate(spelling, 5, "probe::f", &signature, &function)
            .unwrap_or_else(|refusal| panic!("`{spelling}` token refused: {}", refusal.note()));
        for wrong in [other, "«A.b", ""] {
            let refusal = token
                .authenticate(wrong, 5, "probe::f", &signature, &function)
                .expect_err("another constant's spelling never authenticates");
            assert_eq!(refusal.stage(), "token-name", "{}", refusal.note());
        }
        let refusal = token
            .authenticate(other, 5, "probe::f", &signature, &function)
            .expect_err("checked above");
        assert!(
            refusal.note().contains(&format!("permission names `{spelling}`")),
            "the refusal renders the permission in its source spelling: {}",
            refusal.note()
        );
    }
}

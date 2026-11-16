// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The Clean-origin call lane under `@[implemented_by]` (Clean R80; Clean
//! R151 consumer (1); `docs/DECISION_QUEUE.md` R80-CONSUMERS-1).
//!
//! Pinned Lean, and Clean's compiled lanes since R80, run a declaration's
//! IMPLEMENTATION where it carries `@[implemented_by fast]`, and
//! `clean_compiler::constant_to_decl` refuses every declaration of an
//! environment whose ORDER record is not empty. This lane plans from KERNEL
//! values: before the fix it planned `slow` as `a + 2` (and `callsSlow`
//! through the named-call expansion as `a + 2`) where compiled code runs
//! `fast`, `a + 1`: a wrong answer at exit 0. Each refusal is asserted by its
//! exact note; the controls are the unbound callee (`callsFast`), the
//! implementation itself (`fast`) and an unrelated declaration (`plain`) of
//! the same environment, which still plan.
//!
//! `@[extern]` is the sibling attribute (Clean R80 item 5; clean-compiler's
//! `has_compiler_attr`): compiled code calls the external symbol and never runs
//! the body, so before the fix this lane planned `ext` as `a + 2` where Lean
//! links `trust_r80_ext` and Clean's compiled lanes refuse the declaration
//! (`native-extern-body`). The binding walk is held beyond its first hop
//! (`callsCallsSlow`, `callsCallsExt`) and through an `instance` that carries
//! the binding (Clean R80 item 8).
//!
//! The environments are real island elaborations
//! (`trust_certify::clean_island::CleanIslandSession`, the session the
//! compiler runs), so the bindings and the order record are the ones clean-elab
//! writes.
use std::sync::OnceLock;

use clean_kernel::{Environment, Name};
use trust_clean_origin::CleanOriginShape;
use trust_clean_origin::emit::{
    plan_clean_origin_body_for_name, plan_standalone_clean_origin_body_for_name,
};
use trust_types::admissible_body::{ArithBinOp, ArithOperand};

/// The binding written on the declaration: no order record.
const ON_DECL: &str = r#"
def fast (a : UInt64) : UInt64 := a + 1
@[implemented_by fast] def slow (a : UInt64) : UInt64 := a + 2
def callsSlow (a : UInt64) : UInt64 := slow a
def callsFast (a : UInt64) : UInt64 := fast a
def plain (a : UInt64) : UInt64 := a + 3
def callsCallsSlow (a : UInt64) : UInt64 := callsSlow a
"#;

/// `@[extern]` with a body: compiled code calls `trust_r80_ext`.
const EXTERN: &str = r#"
@[extern "trust_r80_ext"] def ext (a : UInt64) : UInt64 := a + 2
def callsExt (a : UInt64) : UInt64 := ext a
def callsCallsExt (a : UInt64) : UInt64 := callsExt a
def plain (a : UInt64) : UInt64 := a + 3
"#;

/// The binding written on an `instance`: compiled code runs `fastBump`.
const ON_INSTANCE: &str = r#"
class Bump (α : Type) where
  bump : α → α
def fastBump : Bump UInt64 := ⟨fun a => a + 1⟩
@[implemented_by fastBump] instance instBumpUInt64 : Bump UInt64 := ⟨fun a => a + 2⟩
def bumped (a : UInt64) : UInt64 := Bump.bump a
"#;

/// The binding written by a command AFTER `caller`, which reaches `slow`:
/// clean-elab records `caller` in the environment's order record.
const LATE: &str = r#"
def fast (a : UInt64) : UInt64 := a + 1
def slow (a : UInt64) : UInt64 := a + 2
def caller (a : UInt64) : UInt64 := slow a
def plain (a : UInt64) : UInt64 := a + 3
attribute [implemented_by fast] slow
"#;

fn island(source: &str) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let report = session.check_all(&[source]);
    assert!(!report.is_rejected(), "actual island source must kernel-check: {report:?}");
    session.environment().unwrap().clone()
}

fn on_decl() -> &'static Environment {
    static ENV: OnceLock<Environment> = OnceLock::new();
    ENV.get_or_init(|| island(ON_DECL))
}

fn late() -> &'static Environment {
    static ENV: OnceLock<Environment> = OnceLock::new();
    ENV.get_or_init(|| island(LATE))
}

fn on_extern() -> &'static Environment {
    static ENV: OnceLock<Environment> = OnceLock::new();
    ENV.get_or_init(|| island(EXTERN))
}

fn on_instance() -> &'static Environment {
    static ENV: OnceLock<Environment> = OnceLock::new();
    ENV.get_or_init(|| island(ON_INSTANCE))
}

fn name(text: &str) -> Name {
    Name::from_string(text)
}

/// The note of the planner's refusal of `declaration`, or a panic naming the
/// shape it planned instead.
fn refusal_note(env: &Environment, declaration: &str) -> String {
    match plan_clean_origin_body_for_name(env, &name(declaration)) {
        Ok(plan) => panic!("`{declaration}` must be refused, it planned {:?}", plan.shape()),
        Err(refusal) => refusal.note(),
    }
}

const BOUND_NOTE: &str = "`slow` is kernel-checked, but Rust cannot call it through the \
    Clean-origin lane: `slow` is @[implemented_by fast]: compiled code runs the implementation, \
    and this lane would emit the kernel value of `slow` instead (implemented-by). Options: call \
    `fast` from Rust, or remove the attribute.";

const REACHED_NOTE: &str = "`callsSlow` is kernel-checked, but Rust cannot call it through the \
    Clean-origin lane: it reaches `slow` (named by `callsSlow`), which is @[implemented_by fast]: \
    compiled code runs the implementation, and this lane would emit the kernel value of `slow` \
    instead (implemented-by). Options: call `fast` in place of `slow`, or remove the attribute.";

/// `callsCallsSlow` names only `callsSlow`: the walk finds `slow` one hop on,
/// in `callsSlow`'s value.
const TWO_HOP_NOTE: &str = "`callsCallsSlow` is kernel-checked, but Rust cannot call it \
    through the Clean-origin lane: it reaches `slow` (named by `callsSlow`), which is \
    @[implemented_by fast]: compiled code runs the implementation, and this lane would emit the \
    kernel value of `slow` instead (implemented-by). Options: call `fast` in place of `slow`, or \
    remove the attribute.";

const INSTANCE_NOTE: &str = "`bumped` is kernel-checked, but Rust cannot call it through the \
    Clean-origin lane: it reaches `instBumpUInt64` (named by `bumped`), which is \
    @[implemented_by fastBump]: compiled code runs the implementation, and this lane would emit \
    the kernel value of `instBumpUInt64` instead (implemented-by). Options: call `fastBump` in \
    place of `instBumpUInt64`, or remove the attribute.";

const EXTERN_REASON: &str = "`ext` is @[extern \"trust_r80_ext\"]: compiled code calls the \
    external symbol `trust_r80_ext`, and this lane would emit the kernel value of `ext` instead \
    (extern). Options: call the function behind `trust_r80_ext` from Rust, or remove the \
    attribute.";

/// The reason a declaration that reaches `ext` through `named_by`'s value is
/// refused with.
fn extern_reached_reason(named_by: &str) -> String {
    format!(
        "it reaches `ext` (named by `{named_by}`), which is @[extern \"trust_r80_ext\"]: compiled \
         code calls the external symbol `trust_r80_ext`, and this lane would emit the kernel \
         value of `ext` instead (extern). Options: call the function behind `trust_r80_ext` in \
         place of `ext`, or remove the attribute."
    )
}

fn kernel_checked(declaration: &str, reason: &str) -> String {
    format!(
        "`{declaration}` is kernel-checked, but Rust cannot call it through the Clean-origin \
         lane: {reason}"
    )
}

fn order_note(declaration: &str) -> String {
    format!(
        "`{declaration}` is kernel-checked, but Rust cannot call it through the Clean-origin \
         lane: an `attribute [implemented_by]` command rebound `slow` after code that reaches it \
         was added (`caller` names `slow`). Pinned Lean compiled that code before the binding, \
         and which body it runs is decided by Lean's inliner, which Clean does not model, so no \
         declaration of this environment is lowered (implemented-by-order). Options: write the \
         attribute on the declaration, or before every use of it."
    )
}

#[test]
fn test_island_carries_the_binding_the_lane_must_honour() {
    // The subject exists: without the binding every assertion below would be
    // about an ordinary `def`.
    assert_eq!(on_decl().get_implemented_by(&name("slow")), Some(&name("fast")));
    assert_eq!(on_decl().get_implemented_by(&name("callsSlow")), None);
    assert_eq!(late().get_implemented_by(&name("slow")), Some(&name("fast")));
    assert_eq!(on_extern().get_extern(&name("ext")).map(String::as_str), Some("trust_r80_ext"));
    assert!(!on_extern().is_extern(&name("callsExt")));
    assert_eq!(on_extern().get_implemented_by(&name("ext")), None);
    assert_eq!(on_instance().get_implemented_by(&name("instBumpUInt64")), Some(&name("fastBump")));
    assert_eq!(on_instance().get_implemented_by(&name("bumped")), None);
}

#[test]
fn test_planner_bound_declaration_is_refused_by_name() {
    assert_eq!(refusal_note(on_decl(), "slow"), BOUND_NOTE);
}

#[test]
fn test_planner_callee_with_binding_is_refused_by_name() {
    assert_eq!(refusal_note(on_decl(), "callsSlow"), REACHED_NOTE);
}

#[test]
fn test_standalone_planner_bound_declaration_is_refused_by_name() {
    // `targo trust lean build`'s planner enters through the same definition
    // check.
    match plan_standalone_clean_origin_body_for_name(on_decl(), &name("slow")) {
        Ok(_) => panic!("the standalone planner must refuse `slow`"),
        Err(refusal) => assert_eq!(refusal.note(), BOUND_NOTE),
    }
}

#[test]
fn test_planner_unbound_callee_still_plans() {
    let expected = CleanOriginShape::WrappingBinOp {
        op: ArithBinOp::Add,
        left: ArithOperand::Param(0),
        right: ArithOperand::Const(1),
    };
    for declaration in ["callsFast", "fast"] {
        let plan = plan_clean_origin_body_for_name(on_decl(), &name(declaration))
            .unwrap_or_else(|refusal| panic!("`{declaration}` must plan: {}", refusal.note()));
        assert_eq!(plan.shape(), &expected, "{declaration}");
    }
    let plan = plan_clean_origin_body_for_name(on_decl(), &name("plain"))
        .unwrap_or_else(|refusal| panic!("`plain` must plan: {}", refusal.note()));
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::WrappingBinOp {
            op: ArithBinOp::Add,
            left: ArithOperand::Param(0),
            right: ArithOperand::Const(3),
        }
    );
}

#[test]
fn test_planner_order_record_refuses_every_declaration() {
    // As `constant_to_decl` does: one that never reaches `slow` included.
    for declaration in ["caller", "plain", "fast", "slow"] {
        assert_eq!(refusal_note(late(), declaration), order_note(declaration), "{declaration}");
    }
}

#[test]
fn test_named_call_expansion_refuses_a_bound_callee() {
    // The kernel-TV source side reads the definition through this expansion
    // (`rustc_mir_transform::clean_origin_ir::mint_kernel_tv`).
    let env = on_decl();
    let body = |declaration: &str| {
        env.get_const(&name(declaration)).unwrap().value.clone().expect("a definition body")
    };
    assert_eq!(
        trust_clean_origin::expand_named_lean_calls(env, &name("callsSlow"), &body("callsSlow")),
        Err("it reaches `slow` (named by `callsSlow`), which is @[implemented_by fast]: compiled \
             code runs the implementation, and this lane would emit the kernel value of `slow` \
             instead (implemented-by). Options: call `fast` in place of `slow`, or remove the \
             attribute."
            .to_string())
    );
    let expanded =
        trust_clean_origin::expand_named_lean_calls(env, &name("callsFast"), &body("callsFast"))
            .expect("the unbound callee expands");
    assert!(expanded.is_some(), "`callsFast` names `fast`, which the expansion unfolds");
}

#[test]
fn test_named_call_expansion_refuses_an_order_record_environment() {
    let env = late();
    let body = env.get_const(&name("caller")).unwrap().value.clone().expect("a definition body");
    let refusal = trust_clean_origin::expand_named_lean_calls(env, &name("caller"), &body)
        .expect_err("an order record refuses the expansion");
    let expected = order_note("caller");
    let (_, reason) = expected.split_once("lane: ").expect("the note's prefix");
    assert_eq!(refusal, reason);
}

#[test]
fn test_planner_binding_two_hops_away_is_refused_by_name() {
    // A walk that stopped at the constants the declaration's own value names
    // would plan this as `a + 2`.
    assert_eq!(refusal_note(on_decl(), "callsCallsSlow"), TWO_HOP_NOTE);
}

#[test]
fn test_named_call_expansion_refuses_a_binding_two_hops_away() {
    let env = on_decl();
    let body =
        env.get_const(&name("callsCallsSlow")).unwrap().value.clone().expect("a definition body");
    let refusal = trust_clean_origin::expand_named_lean_calls(env, &name("callsCallsSlow"), &body)
        .expect_err("the expansion reaches `slow` through `callsSlow`");
    let (_, reason) = TWO_HOP_NOTE.split_once("lane: ").expect("the note's prefix");
    assert_eq!(refusal, reason);
}

#[test]
fn test_planner_binding_on_an_instance_is_refused_by_name() {
    // Clean R80 item 8: the attribute binds the instance constant, which the
    // caller's value names as the class argument of `Bump.bump`.
    assert_eq!(refusal_note(on_instance(), "bumped"), INSTANCE_NOTE);
}

#[test]
fn test_planner_extern_declaration_is_refused_by_name() {
    assert_eq!(refusal_note(on_extern(), "ext"), kernel_checked("ext", EXTERN_REASON));
    match plan_standalone_clean_origin_body_for_name(on_extern(), &name("ext")) {
        Ok(_) => panic!("the standalone planner must refuse `ext`"),
        Err(refusal) => assert_eq!(refusal.note(), kernel_checked("ext", EXTERN_REASON)),
    }
}

#[test]
fn test_planner_callee_with_extern_is_refused_by_name() {
    assert_eq!(
        refusal_note(on_extern(), "callsExt"),
        kernel_checked("callsExt", &extern_reached_reason("callsExt"))
    );
    assert_eq!(
        refusal_note(on_extern(), "callsCallsExt"),
        kernel_checked("callsCallsExt", &extern_reached_reason("callsExt"))
    );
}

#[test]
fn test_named_call_expansion_refuses_an_extern_callee() {
    let env = on_extern();
    let body = env.get_const(&name("callsExt")).unwrap().value.clone().expect("a definition body");
    assert_eq!(
        trust_clean_origin::expand_named_lean_calls(env, &name("callsExt"), &body),
        Err(extern_reached_reason("callsExt"))
    );
}

#[test]
fn test_planner_extern_environment_still_plans_an_unrelated_declaration() {
    // The refusal is the binding's, not the environment's: `plain` never
    // reaches `ext`.
    let plan = plan_clean_origin_body_for_name(on_extern(), &name("plain"))
        .unwrap_or_else(|refusal| panic!("`plain` must plan: {}", refusal.note()));
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::WrappingBinOp {
            op: ArithBinOp::Add,
            left: ArithOperand::Param(0),
            right: ArithOperand::Const(3),
        }
    );
}

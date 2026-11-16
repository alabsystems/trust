// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Real Lean lambda applications, with the original source retained at the gate.
//! Candidate beta reduction is untrusted; the existing kernel must still reject
//! a reflected result with the wrong captured operand or arithmetic.

use clean_kernel::{Environment, Expr, Name};
use trust_clean_origin::emit::plan_clean_origin_body_for_name;
use trust_clean_origin::gate::check_faithful_for_name;

fn checked(source: &str) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let report = session.check_all(&[source]);
    assert!(!report.is_rejected(), "original Lean source: {report:?}");
    session.environment().unwrap().clone()
}

fn reflected(env: &Environment, body: &str) -> Expr {
    let mut scratch = env.clone();
    trust_spec_elab::admit_expr_function(
        &mut scratch,
        "anonymous_call_reflection",
        body,
        &["x"],
        &trust_spec_elab::Domain::Machine(trust_spec_elab::MachineUIntWidth::U64),
    )
    .unwrap();
    scratch
        .get_const(&Name::from_string("anonymous_call_reflection"))
        .unwrap()
        .value
        .clone()
        .unwrap()
}

fn original_source_gate(source: &str, declaration: &str, correct: &str, wrong: &str) {
    let environment = checked(source);
    let name = Name::from_string(declaration);
    let original = environment.get_const(&name).unwrap().clone();
    let plan = plan_clean_origin_body_for_name(&environment, &name)
        .expect("an immediately applied pure lambda can be proposed as scalar code");
    check_faithful_for_name(
        &environment,
        &name,
        &reflected(&environment, correct),
        plan.signature().result(),
    )
    .expect("the existing kernel checks the original declaration, not a rewritten environment");
    assert!(
        check_faithful_for_name(
            &environment,
            &name,
            &reflected(&environment, wrong),
            plan.signature().result(),
        )
        .is_err(),
        "a wrong candidate cannot borrow beta reduction as permission"
    );
    assert_eq!(environment.get_const(&name).unwrap(), &original);
}

#[test]
fn immediately_applied_lambda_is_proposed_and_checked_against_original_source() {
    original_source_gate(
        "def beta_inc (x : UInt64) : UInt64 := (fun y : UInt64 => y + 1) x",
        "beta_inc",
        "x + 1",
        "x + 2",
    );
}

#[test]
fn captured_parameter_and_nested_beta_applications_keep_their_meaning() {
    original_source_gate(
        "def captured (x : UInt64) : UInt64 := (fun y : UInt64 => x + y) 3",
        "captured",
        "x + 3",
        "3 - x",
    );
    original_source_gate(
        "def nested (x : UInt64) : UInt64 := (fun y : UInt64 => y + 1) ((fun z : UInt64 => z + 1) x)",
        "nested",
        "(x + 1) + 1",
        "x + 1",
    );
}

#[test]
fn local_capturing_lambda_is_proposed_without_erasing_the_original_declaration() {
    original_source_gate(
        "def local_capture (x : UInt64) : UInt64 :=\n  let f := fun y : UInt64 => x + y\n  f 3",
        "local_capture",
        "x + 3",
        "x - 3",
    );
}

#[test]
fn beta_candidates_cannot_discard_duplicate_or_reorder_rust_calls() {
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
    let source = r#"
def discard (x : UInt64) : UInt64 := (fun y : UInt64 => (0 : UInt64)) (tick x)
def duplicate (x : UInt64) : UInt64 := (fun y : UInt64 => add2 y y) (tick x)
def reorder (x y : UInt64) : UInt64 :=
  (fun a : UInt64 => fun b : UInt64 => add2 b a) (tick x) (tick y)
"#;
    let report = session.check_all(&[source]);
    assert!(!report.is_rejected(), "source must kernel-check: {report:?}");
    let table: Vec<_> = declarations
        .into_iter()
        .map(|row| trust_clean_origin::RustCalleeRef {
            def_path: format!("test::{}", row.clean_name),
            clean_name: row.clean_name,
            params: row.params,
            result: row.result,
        })
        .collect();
    for declaration in ["discard", "duplicate", "reorder"] {
        assert!(
            trust_clean_origin::plan_clean_origin_body_with_rust_callees(
                session.environment().unwrap(),
                declaration,
                &table,
            )
            .is_err(),
            "pure kernel equality cannot authorize changing calls in {declaration}"
        );
    }
}

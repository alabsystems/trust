// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Constructor elimination proposes scalar code; the original declaration and
//! independent kernel judgment retain all authority. No runtime layout is used.

use clean_kernel::{Environment, Expr, ExprKind, Name, TypeChecker};
use trust_clean_origin::emit::plan_clean_origin_body_for_name;
use trust_clean_origin::gate::check_faithful_for_name;

fn checked(source: &str) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let report = session.check_all(&[source]);
    assert!(!report.is_rejected(), "original source must kernel-check: {report:?}");
    session.environment().unwrap().clone()
}

fn reflected(environment: &Environment, body: &str, arity: usize) -> Expr {
    let names = (0..arity).map(|index| format!("p{index}")).collect::<Vec<_>>();
    let params = names.iter().map(String::as_str).collect::<Vec<_>>();
    let mut scratch = environment.clone();
    let name = "constructor_projection_reflection";
    trust_spec_elab::admit_expr_function(
        &mut scratch,
        name,
        body,
        &params,
        &trust_spec_elab::Domain::Machine(trust_spec_elab::MachineUIntWidth::U64),
    )
    .unwrap();
    scratch.get_const(&Name::from_string(name)).unwrap().value.clone().unwrap()
}

#[test]
fn ofnat_payload_candidates_keep_the_original_source_and_parameter_metadata() {
    let environment = checked(
        r#"
def scalarOfNat (payload : UInt64) : UInt64 :=
  @OfNat.ofNat UInt64 7 (@OfNat.mk UInt64 7 payload)
def chooseOfNat (left payload : UInt64) : UInt64 :=
  @OfNat.ofNat UInt64 7 (@OfNat.mk UInt64 7 payload)
def computedOfNat (payload : UInt64) : UInt64 :=
  @OfNat.ofNat UInt64 7 (@OfNat.mk UInt64 7 (payload + 1))
def scalarPair (left payload : UInt64) : UInt64 :=
  @Prod.snd UInt64 UInt64 (@Prod.mk UInt64 UInt64 left payload)
"#,
    );
    let constructor_name = Name::from_string("OfNat.mk");
    let original_constructor = environment.get_constructor(&constructor_name).unwrap().clone();
    assert_eq!(original_constructor.num_params, 2);
    assert_eq!(original_constructor.num_fields, 1);
    for (name, arity, correct, wrong_payload, wrong_index) in [
        ("scalarOfNat", 1, "p0", "p0 + 1", "7"),
        ("chooseOfNat", 2, "p1", "p0", "7"),
        ("computedOfNat", 1, "p0 + 1", "p0", "7"),
        ("scalarPair", 2, "p1", "p0", "7"),
    ] {
        let declaration = Name::from_string(name);
        let original = environment.get_const(&declaration).unwrap().clone();
        let plan = plan_clean_origin_body_for_name(&environment, &declaration)
            .expect("a pure constructor-headed projection can propose scalar code");
        let carrier = plan.signature().result();
        check_faithful_for_name(
            &environment,
            &declaration,
            &reflected(&environment, correct, arity),
            carrier,
        )
        .expect("the unchanged kernel must close the original source equation");
        for wrong in [wrong_payload, wrong_index] {
            assert!(
                check_faithful_for_name(
                    &environment,
                    &declaration,
                    &reflected(&environment, wrong, arity),
                    carrier,
                )
                .is_err(),
                "the kernel must refuse {name} reflected as {wrong}"
            );
        }
        assert_eq!(environment.get_const(&declaration).unwrap(), &original);
    }
    assert_eq!(environment.get_constructor(&constructor_name).unwrap(), &original_constructor);
}

#[test]
fn an_out_of_range_field_cannot_borrow_the_original_projection_authority() {
    let environment = checked(
        "def scalarOfNat (payload : UInt64) : UInt64 :=\n  \
         @OfNat.ofNat UInt64 7 (@OfNat.mk UInt64 7 payload)",
    );
    let declaration = Name::from_string("scalarOfNat");
    let original = environment.get_const(&declaration).unwrap().value.as_ref().unwrap();
    let ExprKind::Lam(binder, ty, body) = original.kind() else {
        panic!("retain the actual source lambda");
    };
    let mut body = body.as_ref();
    while let ExprKind::MData(_, inner) = body.kind() {
        body = inner;
    }
    let arguments = body.get_app_args();
    let wrong = Expr::lam(
        binder.clone(),
        ty.as_ref().clone(),
        Expr::proj(Name::from_string("OfNat"), 1, arguments[2].clone()),
    );
    assert!(TypeChecker::new(&environment).infer_type(&wrong).is_err());
    let plan = plan_clean_origin_body_for_name(&environment, &declaration).unwrap();
    assert!(
        check_faithful_for_name(&environment, &declaration, &wrong, plan.signature().result())
            .is_err()
    );
}

#[test]
fn a_mismatched_constructor_index_is_refused_by_original_source_typing() {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let report = session.check_all(&["def wrongIndex (payload : UInt64) : UInt64 :=\n  \
         @OfNat.ofNat UInt64 7 (@OfNat.mk UInt64 8 payload)"]);
    assert!(report.is_rejected(), "the index cannot be changed to fit a candidate: {report:?}");
}

#[test]
fn projection_candidates_cannot_hide_rust_calls_in_parameters_or_payloads() {
    use trust_certify::clean_island::{CleanIslandSession, RustCallee};
    use trust_types::Ty;
    let mut session = CleanIslandSession::new();
    session
        .declare_rust_callees(&[RustCallee {
            clean_name: "tick".into(),
            params: vec![Ty::u64()],
            result: Ty::u64(),
        }])
        .unwrap();
    let source = r#"
def effectParameter (x : UInt64) : UInt64 :=
  @OfNat.ofNat UInt64 (UInt64.toNat (tick x))
    (@OfNat.mk UInt64 (UInt64.toNat (tick x)) x)
def effectPayload (x : UInt64) : UInt64 :=
  @OfNat.ofNat UInt64 7 (@OfNat.mk UInt64 7 (let ignored := tick x; x))
"#;
    let report = session.check_all(&[source]);
    assert!(!report.is_rejected(), "source must kernel-check before planning: {report:?}");
    let callees = [trust_clean_origin::RustCalleeRef {
        def_path: "test::tick".into(),
        clean_name: "tick".into(),
        params: vec![Ty::u64()],
        result: Ty::u64(),
    }];
    for declaration in ["effectParameter", "effectPayload"] {
        for metadata in [callees.as_slice(), &[]] {
            let refusal = trust_clean_origin::plan_clean_origin_body_with_rust_callees(
                session.environment().unwrap(),
                declaration,
                metadata,
            )
            .expect_err("kernel erasure cannot authorize dropping a native effect");
            assert!(
                refusal.note().contains("Rust") || refusal.note().contains("tick"),
                "the effect rail must explain this refusal: {}",
                refusal.note()
            );
        }
    }
}

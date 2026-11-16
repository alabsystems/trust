//! Original typed-statement custody only; these observations grant no proof grade.
use trust_source_contract::observe_mir_bool_assignment;
use trust_types::{Operand, Place, Rvalue, Statement, Ty, VerifiableFunction};

fn original() -> VerifiableFunction {
    serde_json::from_str(include_str!("fixtures/law-entry/proof_ref_kind_is_ambiguous.json"))
        .unwrap()
}

#[test]
fn original_assignment_and_actual_lowered_three_steps_have_exact_custody() {
    let f = original();
    let q = observe_mir_bool_assignment(&f, 1, 0).unwrap();
    assert!(std::ptr::eq(q.function(), &f));
    assert_eq!(
        (q.block_ordinal(), q.statement_ordinal(), q.destination(), q.value()),
        (1, 0, 2, true)
    );
    assert_eq!(q.block_id().0, 1);
    let lean = include_str!("../lean/MirBoolAssignment.lean");
    assert!(lean.contains(
        "def originalNominalName : String := \"trust_ir::proof::obligations::ObligationKindShape\""
    ));
    assert!(lean.contains(
        "def originalAssignment : Statement := .assign ⟨2, []⟩ (.use (.constantBool true))"
    ));
    assert_eq!(f.body.arg_count, 1);
    assert_eq!(f.body.return_ty, Ty::Bool);
    let nominal = serde_json::to_value(&f.body.locals[1].ty).unwrap();
    assert_eq!(nominal["Adt"]["name"], "trust_ir::proof::obligations::ObligationKindShape");
    assert_eq!(nominal["Adt"]["fields"][0][0], "__tag");
    assert!(nominal["Adt"]["faithful_enum_repr"].is_null());
    assert!(matches!(f.body.blocks[1].terminator, trust_types::Terminator::Goto(id) if id.0 == 10));
    assert!(matches!(f.body.blocks[10].terminator, trust_types::Terminator::Return));
    assert!(
        matches!(&f.body.blocks[10].stmts[0], Statement::Assign { place, rvalue: Rvalue::Use(Operand::Copy(from)), .. }
        if place.local == 0 && place.projections.is_empty() && from.local == 2 && from.projections.is_empty())
    );
    let module = trust_ir_bridge::lower_to_trust_ir(q.function()).unwrap();
    assert_eq!(module.functions.len(), 1, "no invented callee environment");
    let body = serde_json::to_value(&module.functions[0].blocks[1].body).unwrap();
    assert_eq!(body[0]["inst"]["Const"]["value"]["Bool"], q.value());
    assert_eq!(body[0]["results"], serde_json::json!([6]));
    assert_eq!(body[1]["inst"]["Copy"]["operand"], 6);
    assert_eq!(body[1]["results"], serde_json::json!([7]));
    assert_eq!(body[2]["inst"]["Store"]["ty"], "Bool");
    assert_eq!(body[2]["inst"]["Store"]["ptr"], 4);
    assert_eq!(body[2]["inst"]["Store"]["value"], 7);
    assert_eq!(body[2]["results"], serde_json::json!([]));
}

#[test]
fn original_body_mutant_is_observed_as_false_not_reused_as_true() {
    let mut value = serde_json::to_value(original()).unwrap();
    value["body"]["blocks"][1]["stmts"][0]["Assign"]["rvalue"]["Use"]["Constant"]["Bool"] =
        false.into();
    let f = serde_json::from_value(value).unwrap();
    let q = observe_mir_bool_assignment(&f, 1, 0).unwrap();
    assert!(!q.value());
    assert_eq!(q.destination(), 2);
    let module = trust_ir_bridge::lower_to_trust_ir(q.function()).unwrap();
    let body = serde_json::to_value(&module.functions[0].blocks[1].body).unwrap();
    assert_eq!(body[0]["inst"]["Const"]["value"]["Bool"], false);
}

#[test]
fn wrong_destination_type_refuses() {
    let mut f = original();
    f.body.locals[2].ty = Ty::Bool; // baseline exact type
    assert!(observe_mir_bool_assignment(&f, 1, 0).is_some());
    f.body.locals[2].ty = f.body.locals[3].ty.clone();
    assert!(observe_mir_bool_assignment(&f, 1, 0).is_none());
}
#[test]
fn projected_destination_refuses() {
    let mut f = original();
    let Statement::Assign { place, .. } = &mut f.body.blocks[1].stmts[0] else { panic!() };
    *place = Place::field(2, 0);
    assert!(observe_mir_bool_assignment(&f, 1, 0).is_none());
}
#[test]
fn copied_operand_is_not_constant_bool() {
    let mut f = original();
    let Statement::Assign { rvalue, .. } = &mut f.body.blocks[1].stmts[0] else { panic!() };
    *rvalue = Rvalue::Use(Operand::Copy(Place::local(2)));
    assert!(observe_mir_bool_assignment(&f, 1, 0).is_none());
}
#[test]
fn duplicate_original_local_identity_refuses() {
    let mut f = original();
    f.body.locals[3].index = 2;
    assert!(observe_mir_bool_assignment(&f, 1, 0).is_none());
}
#[test]
fn duplicate_original_block_identity_refuses() {
    let mut f = original();
    f.body.blocks[2].id = f.body.blocks[1].id;
    assert!(observe_mir_bool_assignment(&f, 1, 0).is_none());
}
#[test]
fn missing_selection_and_statement_budget_refuse() {
    let mut f = original();
    assert!(observe_mir_bool_assignment(&f, 100, 0).is_none());
    assert!(observe_mir_bool_assignment(&f, 1, 100).is_none());
    f.body.blocks[1].stmts = vec![f.body.blocks[1].stmts[0].clone(); 8193];
    assert!(observe_mir_bool_assignment(&f, 1, 0).is_none());
}

#[test]
fn changed_bool_destination_and_block_id_are_not_erased() {
    let mut f = original();
    let Statement::Assign { place, .. } = &mut f.body.blocks[1].stmts[0] else { panic!() };
    *place = Place::local(0);
    f.body.blocks[1].id.0 = 100;
    let q = observe_mir_bool_assignment(&f, 1, 0).unwrap();
    assert_eq!(q.block_ordinal(), 1);
    assert_eq!(q.block_id().0, 100);
    assert_eq!(q.destination(), 0);
    // This is still an observation, but cannot match the old block1/local2 theorem.
}

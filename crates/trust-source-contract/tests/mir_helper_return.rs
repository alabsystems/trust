//! SAME-helper source-view custody only; no AST quotation or source grade.
use trust_source_contract::{observe_mir_bool_assignment, observe_mir_nominal_constructor};
use trust_types::{Operand, Rvalue, Statement, Terminator, Ty, VerifiableFunction};
fn original() -> VerifiableFunction {
    serde_json::from_str(include_str!("fixtures/law-entry/proof_ref_kind_is_ambiguous.json"))
        .unwrap()
}
fn program(body: bool) -> VerifiableFunction {
    let mut v = serde_json::to_value(original()).unwrap();
    v["body"]["blocks"][1]["stmts"][0]["Assign"]["rvalue"]["Use"]["Constant"]["Bool"] = body.into();
    serde_json::from_value(v).unwrap()
}
// Non-authoritative structural comparison with the exact reflected body. A
// successful observation here is deliberately not exported as a proof token.
fn source_shape(f: &VerifiableFunction, first: bool) -> bool {
    if f.body.arg_count != 1
        || f.body.return_ty != Ty::Bool
        || f.body.locals.len() != 4
        || f.body.blocks.len() != 11
    {
        return false;
    }
    for local in [0, 2] {
        if !f.body.locals.iter().any(|d| d.index == local && d.ty == Ty::Bool) {
            return false;
        }
    }
    if !f.body.locals.iter().any(|d| d.index == 3 && d.ty == (Ty::Int { width: 64, signed: true }))
    {
        return false;
    }
    for id in 1..=9 {
        let Some((ordinal, block)) =
            f.body.blocks.iter().enumerate().find(|(_, block)| block.id.0 == id)
        else {
            return false;
        };
        if block.stmts.len() != 1
            || !matches!(block.terminator, Terminator::Goto(target) if target.0 == 10)
        {
            return false;
        }
        let Some(q) = observe_mir_bool_assignment(f, ordinal, 0) else {
            return false;
        };
        if q.block_id().0 != id
            || q.destination() != 2
            || q.value() != (if id == 1 { first } else { id != 9 })
        {
            return false;
        }
    }
    let Some(ret) = f.body.blocks.iter().find(|block| block.id.0 == 10) else {
        return false;
    };
    if ret.stmts.len() != 1 || !matches!(ret.terminator, Terminator::Return) {
        return false;
    }
    matches!(&ret.stmts[0], Statement::Assign { place, rvalue: Rvalue::Use(Operand::Copy(from)), .. }
        if place.local == 0 && place.projections.is_empty() && from.local == 2 && from.projections.is_empty())
}
#[test]
fn every_original_branch_and_return_role_matches_actual_lowered_body() {
    for body in [true, false] {
        let f = program(body);
        assert!(source_shape(&f, body));
        let module = trust_ir_bridge::lower_to_trust_ir(&f).unwrap();
        assert_eq!(module.functions.len(), 1);
        for id in 1..=9 {
            let branch = module.functions[0].blocks.iter().find(|block| block.id.0 == id).unwrap();
            let nodes = serde_json::to_value(&branch.body).unwrap();
            let expected = if id == 1 { body } else { id != 9 };
            assert_eq!(branch.body.len(), 4);
            let value_id = 4 + 2 * id;
            assert_eq!(nodes[0]["inst"]["Const"]["value"]["Bool"], expected);
            assert_eq!(nodes[0]["results"], serde_json::json!([value_id]));
            assert_eq!(nodes[1]["inst"]["Copy"]["operand"], value_id);
            assert_eq!(nodes[1]["results"], serde_json::json!([value_id + 1]));
            assert_eq!(nodes[2]["inst"]["Store"]["ty"], "Bool");
            assert_eq!(nodes[2]["inst"]["Store"]["ptr"], 4);
            assert_eq!(nodes[2]["inst"]["Store"]["value"], value_id + 1);
            assert_eq!(nodes[3]["inst"]["Br"]["target"], 10);
            assert_eq!(nodes[3]["inst"]["Br"]["args"], serde_json::json!([]));
        }
        let ret = module.functions[0].blocks.iter().find(|block| block.id.0 == 10).unwrap();
        let nodes = serde_json::to_value(&ret.body).unwrap();
        assert_eq!(ret.body.len(), 3);
        assert_eq!(nodes[0]["inst"]["Load"]["ptr"], 4);
        assert_eq!(nodes[0]["inst"]["Load"]["ty"], "Bool");
        assert_eq!(nodes[0]["results"], serde_json::json!([24]));
        assert_eq!(nodes[1]["inst"]["Copy"]["operand"], 24);
        assert_eq!(nodes[1]["results"], serde_json::json!([25]));
        assert_eq!(nodes[2]["inst"]["Return"]["values"], serde_json::json!([25]));
    }
    let lean = include_str!("../lean/MirHelperReturn.lean");
    assert!(lean.contains("[originalBody,true,true,true,true,true,true,true,false]"));
}
#[test]
fn all_declared_constructor_returns_match_reflected_body_in_exact_ten_steps() {
    use trust_ir::interpret::{InterpretOptions, InterpretValue, InterpretValueKind, Interpreter};
    for body in [true, false] {
        let f = program(body);
        assert!(source_shape(&f, body));
        let module = trust_ir_bridge::lower_to_trust_ir(&f).unwrap();
        for ordinal in 0..16 {
            let c = observe_mir_nominal_constructor(&f, 1, ordinal).unwrap();
            let argument = InterpretValue {
                ty: module.func_types[0].params[0].clone(),
                kind: InterpretValueKind::Aggregate(vec![
                    InterpretValue::int(trust_ir::ty::Ty::I64, c.variant().discriminant).unwrap(),
                ]),
            };
            let outcome = Interpreter::with_module(&module)
                .with_options(InterpretOptions {
                    fuel: 40,
                    max_call_depth: 4,
                    ..InterpretOptions::default()
                })
                .execute_func(module.functions[0].id, [argument])
                .unwrap();
            let expected = if ordinal == 0 { body } else { matches!(ordinal, 1..=5 | 8 | 9) };
            assert_eq!(outcome.returns, vec![InterpretValue::bool(expected)]);
            assert_eq!(outcome.host_calls, 0);
            assert_eq!(outcome.steps, 10);
        }
    }
}
#[test]
fn wrong_copy_goto_return_and_nonfirst_body_mutants_do_not_fit_old_view() {
    let base = serde_json::to_value(original()).unwrap();
    for (pointer, replacement) in [
        ("/body/blocks/10/stmts/0/Assign/rvalue/Use/Copy/local", serde_json::json!(1)),
        ("/body/blocks/1/terminator/Goto", serde_json::json!(11)),
        ("/body/blocks/10/terminator", serde_json::json!({"Goto":0})),
        ("/body/blocks/2/stmts/0/Assign/rvalue/Use/Constant/Bool", serde_json::json!(false)),
        ("/body/blocks/2/stmts/0/Assign/place/local", serde_json::json!(0)),
    ] {
        let mut v = base.clone();
        *v.pointer_mut(pointer).unwrap() = replacement;
        let f = serde_json::from_value(v).unwrap();
        assert!(!source_shape(&f, true), "{pointer}");
    }
}
#[test]
fn extra_source_statement_and_wrong_temporary_type_do_not_disappear() {
    let mut f = original();
    let extra = f.body.blocks[8].stmts[0].clone();
    f.body.blocks[8].stmts.push(extra);
    assert!(!source_shape(&f, true));
    let mut f = original();
    f.body.locals[3].ty = Ty::Bool;
    assert!(!source_shape(&f, true));
}

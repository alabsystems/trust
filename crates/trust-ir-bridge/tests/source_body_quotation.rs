//! Producer custody for the canonical SemR byte fixture. These tests do not
//! certify MIR-to-IR semantic preservation or change a source proof grade.
use trust_ir_bridge::lower_to_trust_ir;
use trust_types::VerifiableFunction;

const SOURCE: &str = include_str!(
    "../../trust-source-contract/tests/fixtures/law-entry/proof_ref_kind_is_ambiguous.json"
);
const ORIGINAL: &[u8] = include_bytes!("fixtures/source-body/proof-ref-original.tmbc");
const MUTANT: &[u8] = include_bytes!("fixtures/source-body/proof-ref-mutant.tmbc");

#[test]
fn exact_original_typed_body_produces_checked_semr_fixture() {
    let function: VerifiableFunction = serde_json::from_str(SOURCE).unwrap();
    let module = lower_to_trust_ir(&function).unwrap();
    assert_eq!(module.functions.len(), 1, "no fabricated callee environment");
    assert_eq!(
        module.func_types[0].params,
        vec![trust_ir::ty::Ty::Struct(trust_ir::value::StructId::new(0))]
    );
    assert_eq!(module.structs[0].name, "trust_ir::proof::obligations::ObligationKindShape");
    assert_eq!(trust_ir::binary::serialize_module(&module).unwrap(), ORIGINAL);
}

#[test]
fn original_body_mutation_changes_exact_quotation_without_changing_formals() {
    let original: VerifiableFunction = serde_json::from_str(SOURCE).unwrap();
    let mut source: serde_json::Value = serde_json::from_str(SOURCE).unwrap();
    let value =
        &mut source["body"]["blocks"][1]["stmts"][0]["Assign"]["rvalue"]["Use"]["Constant"]["Bool"];
    assert_eq!(*value, serde_json::json!(true));
    *value = serde_json::json!(false);
    let mutant: VerifiableFunction = serde_json::from_value(source).unwrap();
    let original_module = lower_to_trust_ir(&original).unwrap();
    let mutant_module = lower_to_trust_ir(&mutant).unwrap();
    assert_eq!(original_module.func_types, mutant_module.func_types);
    assert_eq!(original_module.structs, mutant_module.structs);
    let bytes = trust_ir::binary::serialize_module(&mutant_module).unwrap();
    assert_eq!(bytes, MUTANT);
    assert_ne!(bytes, ORIGINAL);
}

#[test]
fn original_and_body_mutant_execute_the_same_checked_finite_table() {
    use trust_ir::interpret::{InterpretOptions, InterpretValue, InterpretValueKind, Interpreter};
    use trust_ir::ty::Ty;
    use trust_ir::value::{FuncId, StructId};
    let original = trust_ir::binary::deserialize_module(ORIGINAL).unwrap();
    let mutant = trust_ir::binary::deserialize_module(MUTANT).unwrap();
    let expected = [
        true, true, true, true, true, true, false, false, true, true, false, false, false, false,
        false, false,
    ];
    for (tag, result) in expected.into_iter().enumerate() {
        for (module, changed) in [(&original, false), (&mutant, true)] {
            let argument = InterpretValue {
                ty: Ty::Struct(StructId::new(0)),
                kind: InterpretValueKind::Aggregate(vec![
                    InterpretValue::int(Ty::I64, tag as i128).unwrap(),
                ]),
            };
            let outcome = Interpreter::with_module(module)
                .with_options(InterpretOptions {
                    fuel: 40,
                    max_call_depth: 4,
                    ..InterpretOptions::default()
                })
                .execute_func(FuncId::new(0), [argument])
                .unwrap();
            assert_eq!(outcome.host_calls, 0);
            assert_eq!(
                outcome.returns,
                vec![InterpretValue::bool(result && !(changed && tag == 0))]
            );
        }
    }
}

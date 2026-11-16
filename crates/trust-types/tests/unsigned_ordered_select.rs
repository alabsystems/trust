//! The original captured clamp body, read through the shared select recognizer.
use trust_types::admissible_body::{
    ArithOperand, SelectCmp, recognize_admissible_body, recognize_select_general,
    recognize_unsigned_ordered_select,
};
use trust_types::{BinOp, Rvalue, Statement, Ty, VerifiableFunction};

fn captured_clamp() -> VerifiableFunction {
    let envelope: serde_json::Value = serde_json::from_str(include_str!(
        "../../trust-source-contract/tests/fixtures/retained-clamp-width.json"
    ))
    .unwrap();
    let raw = envelope["original_function_json"].as_str().unwrap();
    assert_eq!(trust_types::stable_sha256_hex(raw.as_bytes()), envelope["function_sha256"]);
    serde_json::from_str(raw).unwrap()
}

#[test]
fn unsigned_ordered_select_complements_comparison_and_swaps_both_arms() {
    for (source, expected) in [(BinOp::Gt, SelectCmp::Le), (BinOp::Ge, SelectCmp::Lt)] {
        let mut function = captured_clamp();
        let Statement::Assign { rvalue: Rvalue::BinaryOp(op, _, _), .. } =
            &mut function.body.blocks[0].stmts[0]
        else {
            panic!()
        };
        *op = source;
        assert!(recognize_select_general(&function).is_none());
        assert!(recognize_admissible_body(&function).is_none());
        let selected = recognize_unsigned_ordered_select(&function).unwrap();
        assert_eq!(selected.cmp, expected);
        assert_eq!(selected.cmp_left, 0);
        assert_eq!(selected.cmp_right, ArithOperand::Const(64));
        assert_eq!(selected.then_arm, ArithOperand::Param(0));
        assert_eq!(selected.else_arm, ArithOperand::Const(64));
        // Equality distinguishes > from >=; zero and MAX check both ends of
        // the unsigned domain. Omitting either the complement or swap fails.
        for input in [0_u32, 63, 64, 65, u32::MAX] {
            let original = match source {
                BinOp::Gt => input > 64,
                BinOp::Ge => input >= 64,
                _ => unreachable!(),
            };
            let normalized = match selected.cmp {
                SelectCmp::Le => input <= 64,
                SelectCmp::Lt => input < 64,
                _ => unreachable!(),
            };
            assert_eq!(if original { 64 } else { input }, if normalized { input } else { 64 });
        }
    }
    for op in [BinOp::Lt, BinOp::Le, BinOp::Eq] {
        let mut function = captured_clamp();
        let Statement::Assign { rvalue: Rvalue::BinaryOp(actual, _, _), .. } =
            &mut function.body.blocks[0].stmts[0]
        else {
            panic!()
        };
        *actual = op;
        assert_eq!(
            recognize_unsigned_ordered_select(&function),
            recognize_select_general(&function)
        );
    }
}

#[test]
fn unsigned_ordered_select_refuses_signed_float_and_mixed_widths() {
    let original = captured_clamp();
    for ty in [Ty::Int { width: 32, signed: true }, Ty::Float { width: 32 }, Ty::u64()] {
        let mut function = original.clone();
        function.body.locals[1].ty = ty;
        assert!(recognize_unsigned_ordered_select(&function).is_none());
    }
    let mut function = original;
    function.body.return_ty = Ty::Int { width: 32, signed: true };
    assert!(recognize_unsigned_ordered_select(&function).is_none());
}

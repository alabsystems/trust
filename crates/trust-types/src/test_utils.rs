// trust-types/test_utils.rs: Shared test utilities for verification IR tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::{
    BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction, VerificationCondition,
};

/// Default test SourceSpan.
pub fn test_source_span() -> SourceSpan {
    SourceSpan { file: "test.rs".to_string(), line_start: 1, col_start: 1, line_end: 1, col_end: 1 }
}

/// Make a VC with kind and function name (formula defaults to Bool(true)).
pub fn make_test_vc(kind: VcKind, function: &str) -> VerificationCondition {
    make_test_vc_with_formula(kind, function, Formula::Bool(true))
}

/// Make a VC with kind, function name, and explicit formula.
pub fn make_test_vc_with_formula(
    kind: VcKind,
    function: &str,
    formula: Formula,
) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: function.into(),
        location: test_source_span(),
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

/// Make a VerifiableFunction with given name and body.
pub fn make_test_function(name: &str, body: VerifiableBody) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("test::{name}"),
        span: test_source_span(),
        body,
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Make a VerifiableBody with given locals and blocks (arg_count=0, return_ty=Unit).
pub fn make_simple_body(locals: Vec<LocalDecl>, blocks: Vec<BasicBlock>) -> VerifiableBody {
    VerifiableBody { locals, blocks, arg_count: 0, return_ty: Ty::Unit }
}

/// Make a BasicBlock.
pub fn make_basic_block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}

/// Make a LocalDecl.
pub fn make_local(idx: usize, ty: Ty) -> LocalDecl {
    LocalDecl { index: idx, ty, name: None }
}

/// Make a named LocalDecl.
pub fn make_named_local(idx: usize, name: &str, ty: Ty) -> LocalDecl {
    LocalDecl { index: idx, ty, name: Some(name.to_string()) }
}

/// Make an Assign statement.
pub fn make_assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: test_source_span() }
}

/// Make a BinaryOp Rvalue.
pub fn make_binary_op(op: BinOp, left: Operand, right: Operand) -> Rvalue {
    Rvalue::BinaryOp(op, left, right)
}

/// Make a constant i32 operand.
pub fn make_const_i32(val: i32) -> Operand {
    Operand::Constant(ConstValue::Int(i128::from(val)))
}

/// Make a constant u64 operand.
pub fn make_const_u64(val: u64) -> Operand {
    Operand::Constant(ConstValue::Uint(u128::from(val), 64))
}

/// Make a constant bool operand.
pub fn make_const_bool(val: bool) -> Operand {
    Operand::Constant(ConstValue::Bool(val))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_source_span_defaults() {
        let span = test_source_span();

        assert_eq!(span.file, "test.rs");
        assert_eq!(span.line_start, 1);
        assert_eq!(span.col_start, 1);
        assert_eq!(span.line_end, 1);
        assert_eq!(span.col_end, 1);
    }

    #[test]
    fn test_make_test_vc() {
        let vc = make_test_vc(VcKind::DivisionByZero, "divide");

        assert_eq!(vc.function, "divide");
        assert_eq!(vc.location, test_source_span());
        assert_eq!(vc.formula, Formula::Bool(true));
        assert!(matches!(&vc.kind, VcKind::DivisionByZero));
    }

    #[test]
    fn test_make_test_vc_with_formula() {
        let formula = Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]);
        let vc = make_test_vc_with_formula(
            VcKind::Assertion { message: "must hold".to_string() },
            "check",
            formula.clone(),
        );

        assert_eq!(vc.function, "check");
        assert_eq!(vc.location, test_source_span());
        assert_eq!(vc.formula, formula);
        assert!(matches!(
            &vc.kind,
            VcKind::Assertion { message } if message == "must hold"
        ));
    }

    #[test]
    fn test_make_test_function() {
        let body = make_simple_body(
            vec![make_local(0, Ty::Unit)],
            vec![make_basic_block(0, vec![], Terminator::Return)],
        );
        let func = make_test_function("sample", body);

        assert_eq!(func.name, "sample");
        assert_eq!(func.def_path, "test::sample");
        assert_eq!(func.span, test_source_span());
        assert!(func.contracts.is_empty());
        assert!(func.preconditions.is_empty());
        assert!(func.postconditions.is_empty());
        assert_eq!(func.body.locals.len(), 1);
        assert_eq!(func.body.blocks.len(), 1);
        assert!(matches!(&func.body.blocks[0].terminator, Terminator::Return));
    }

    #[test]
    fn test_make_simple_body() {
        let body = make_simple_body(
            vec![make_local(0, Ty::Unit), make_named_local(1, "flag", Ty::Bool)],
            vec![make_basic_block(0, vec![Statement::Nop], Terminator::Return)],
        );

        assert_eq!(body.locals.len(), 2);
        assert_eq!(body.blocks.len(), 1);
        assert_eq!(body.arg_count, 0);
        assert_eq!(body.return_ty, Ty::Unit);
        assert_eq!(body.blocks[0].id.0, 0);
        assert!(matches!(&body.blocks[0].stmts[0], Statement::Nop));
    }

    #[test]
    fn test_make_basic_block() {
        let block = make_basic_block(3, vec![Statement::Nop], Terminator::Goto(BlockId(4)));

        assert_eq!(block.id.0, 3);
        assert_eq!(block.stmts.len(), 1);
        assert!(matches!(&block.stmts[0], Statement::Nop));
        assert!(matches!(&block.terminator, Terminator::Goto(BlockId(4))));
    }

    #[test]
    fn test_make_local_and_named_local() {
        let local = make_local(0, Ty::Bool);
        let named = make_named_local(1, "value", Ty::Int { width: 32, signed: true });

        assert_eq!(local.index, 0);
        assert_eq!(local.ty, Ty::Bool);
        assert_eq!(local.name, None);

        assert_eq!(named.index, 1);
        assert_eq!(named.ty, Ty::Int { width: 32, signed: true });
        assert_eq!(named.name.as_deref(), Some("value"));
    }

    #[test]
    fn test_make_assign() {
        let stmt = make_assign(Place::local(1), Rvalue::Use(make_const_bool(true)));

        let Statement::Assign { place, rvalue, span } = stmt else {
            panic!("expected assign statement");
        };

        assert_eq!(place, Place::local(1));
        assert_eq!(span, test_source_span());
        assert!(matches!(rvalue, Rvalue::Use(Operand::Constant(ConstValue::Bool(true)))));
    }

    #[test]
    fn test_make_binary_op() {
        let rvalue = make_binary_op(BinOp::Add, Operand::Copy(Place::local(1)), make_const_i32(2));

        let Rvalue::BinaryOp(op, left, right) = rvalue else {
            panic!("expected binary op");
        };

        assert_eq!(op, BinOp::Add);
        assert!(matches!(left, Operand::Copy(place) if place == Place::local(1)));
        assert!(matches!(right, Operand::Constant(ConstValue::Int(2))));
    }

    #[test]
    fn test_make_const_operands() {
        let int_operand = make_const_i32(-7);
        let uint_operand = make_const_u64(99);
        let bool_operand = make_const_bool(true);

        assert!(matches!(int_operand, Operand::Constant(ConstValue::Int(-7))));
        assert!(matches!(uint_operand, Operand::Constant(ConstValue::Uint(99, 64))));
        assert!(matches!(bool_operand, Operand::Constant(ConstValue::Bool(true))));
    }
}

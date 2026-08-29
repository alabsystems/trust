use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::{append_stable_flattened_index_bound, stable_checked_result_field0_consumer};

const USIZE: Ty = Ty::Int { width: 64, signed: false };

fn extraction(local: usize) -> Statement {
    Statement::Assign {
        place: Place::local(local),
        rvalue: Rvalue::Use(Operand::Copy(Place {
            local: 2,
            projections: vec![Projection::Field(0)],
        })),
        span: SourceSpan::default(),
    }
}

fn assign(local: usize, value: u128) -> Statement {
    Statement::Assign {
        place: Place::local(local),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(value, 64))),
        span: SourceSpan::default(),
    }
}

fn extraction_func(consumer: usize, arg_count: usize, extra: Vec<Statement>) -> VerifiableFunction {
    let mut stmts = vec![extraction(consumer)];
    stmts.extend(extra);
    VerifiableFunction {
        name: "flattened_index_consumer".into(),
        def_path: "test::flattened_index_consumer".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                LocalDecl { index: 1, ty: USIZE, name: Some("param".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::Tuple(vec![USIZE, Ty::Bool]),
                    name: Some("checked".into()),
                },
                LocalDecl { index: 3, ty: USIZE, name: Some("idx".into()) },
                LocalDecl {
                    index: 4,
                    ty: Ty::Ref { mutable: true, inner: Box::new(USIZE) },
                    name: Some("idx_ref".into()),
                },
            ],
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn emitted_index_bounds(func: &VerifiableFunction) -> Vec<trust_types::Formula> {
    let mut facts = Vec::new();
    append_stable_flattened_index_bound(func, 2, 5, &mut facts);
    facts
}

#[test]
fn single_assignment_non_parameter_consumer_is_licensed() {
    let func = extraction_func(3, 1, vec![]);
    assert_eq!(stable_checked_result_field0_consumer(&func, 2), Some(3));
    assert_eq!(emitted_index_bounds(&func).len(), 1);
}

#[test]
fn merged_consumer_is_not_given_a_global_flattened_index_bound() {
    let func = extraction_func(3, 1, vec![assign(3, 99)]);
    assert_eq!(stable_checked_result_field0_consumer(&func, 2), None);
    assert!(emitted_index_bounds(&func).is_empty());
}

#[test]
fn reassigned_parameter_keeps_its_distinct_entry_value() {
    // The extraction is the parameter's only explicit definition, but its bare
    // name denotes the implicit caller-supplied entry value too.
    let func = extraction_func(1, 1, vec![]);
    assert_eq!(stable_checked_result_field0_consumer(&func, 2), None);
    assert!(emitted_index_bounds(&func).is_empty());
}

#[test]
fn mutably_escaped_consumer_is_not_treated_as_static() {
    let borrow = Statement::Assign {
        place: Place::local(4),
        rvalue: Rvalue::Ref { mutable: true, place: Place::local(3) },
        span: SourceSpan::default(),
    };
    let func = extraction_func(3, 1, vec![borrow]);
    assert_eq!(stable_checked_result_field0_consumer(&func, 2), None);
    assert!(emitted_index_bounds(&func).is_empty());
}

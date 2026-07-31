use trust_types::{
    BasicBlock, BlockId, Contract, ContractKind, LocalDecl, Operand, Place, SourceSpan,
    Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction,
};

use super::regenerate_recursion_decreases_production_variants;

fn call_span(line: u32) -> SourceSpan {
    SourceSpan {
        file: "two_calls.rs".to_string(),
        line_start: line,
        col_start: 5,
        line_end: line,
        col_end: 19,
    }
}

fn two_recursive_calls_with_decreases() -> VerifiableFunction {
    let contract_span = call_span(1);
    let recursive_call = |id, line, target| BasicBlock {
        id: BlockId(id),
        stmts: Vec::new(),
        terminator: Terminator::Call {
            unwind: trust_types::UnwindEdge::Unreachable,
            func: "test::two_calls".to_string(),
            args: vec![Operand::Copy(Place::local(1))],
            dest: Place::local(0),
            target: Some(BlockId(target)),
            span: call_span(line),
            is_unsafe_sig: false,
            is_foreign: false,
            atomic: None,
        },
    };
    VerifiableFunction {
        name: "two_calls".to_string(),
        def_path: "test::two_calls".to_string(),
        span: contract_span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".to_string()) },
            ],
            blocks: vec![
                recursive_call(0, 10, 1),
                recursive_call(1, 20, 2),
                BasicBlock {
                    id: BlockId(2),
                    stmts: Vec::new(),
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![Contract {
            kind: ContractKind::Decreases,
            span: contract_span,
            body: "__trust_lowered_compiler_contract__:n".to_string(),
        }],
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
    }
}

#[test]
fn fresh_recursion_variants_preserve_every_exact_source_bound_callsite() {
    let function = two_recursive_calls_with_decreases();
    let (raw, augmented) = regenerate_recursion_decreases_production_variants(&function)
        .expect("fresh recursion reconstruction must stay within budget");

    assert_eq!(raw.len(), 2, "both recursive call sites need an exact fresh row");
    assert_eq!(augmented.len(), raw.len());
    for (raw, augmented) in raw.iter().zip(&augmented) {
        assert!(matches!(
            &raw.kind,
            VcKind::NonTermination { context, measure }
                if context == "recursion" && measure == "n"
        ));
        assert_eq!(
            raw.contract_metadata.as_ref().and_then(|metadata| metadata.source_contract_index),
            Some(0)
        );
        assert!(matches!(
            &augmented.kind,
            VcKind::NonTermination { context, measure }
                if context == "recursion" && measure == "n"
        ));
        assert_eq!(augmented.location, raw.location);
        assert_eq!(augmented.contract_metadata, raw.contract_metadata);
    }
    assert_ne!(raw[0].location, raw[1].location, "fixture call sites must be distinct");
}

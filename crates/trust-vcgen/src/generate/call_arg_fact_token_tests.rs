use trust_types::UnwindEdge;
use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::call_arg_fact_token;

const I32: Ty = Ty::Int { width: 32, signed: true };

/// `fn f(a: i32) { <pre_call_stmts>; h = g(<subject>); _0 = h }` — the minimal
/// call-site shape the token license is judged against.
fn caller_with(pre_call_stmts: Vec<Statement>) -> VerifiableFunction {
    VerifiableFunction {
        name: "f".into(),
        def_path: "crate::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: I32, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: I32, name: Some("a".into()) },
                LocalDecl { index: 2, ty: I32, name: Some("t".into()) },
                LocalDecl { index: 3, ty: I32, name: Some("h".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: pre_call_stmts,
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: "crate::g".into(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(3),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: I32,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn assign(local: usize, k: i128) -> Statement {
    Statement::Assign {
        place: Place::local(local),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(k))),
        span: SourceSpan::default(),
    }
}

/// A never-written parameter actual is licensed: its bare name denotes the
/// one (entry = at-call) value.
#[test]
fn unwritten_param_actual_is_licensed_bare() {
    let f = caller_with(vec![]);
    assert_eq!(call_arg_fact_token(&f, &Operand::Copy(Place::local(1))).as_deref(), Some("a"));
    // Move licenses identically to Copy.
    assert_eq!(call_arg_fact_token(&f, &Operand::Move(Place::local(1))).as_deref(), Some("a"));
}

/// THE REASSIGNED-ACTUAL PIN: a parameter written in the body has NO licensed
/// spelling — its bare name denotes the ENTRY version (what the function's
/// preconditions constrain), NOT the at-call value. Minting the bare name
/// anyway is the whole-program false-hypothesis bug (trust-clean probe
/// `reassigned_actual_must_not_mint_entry_version_hypothesis`).
#[test]
fn reassigned_param_actual_is_declined() {
    let f = caller_with(vec![assign(1, 0)]); // a = 0 before the call
    assert_eq!(call_arg_fact_token(&f, &Operand::Copy(Place::local(1))), None);
}

/// A single-assignment non-parameter local is licensed (SSA collapse: every
/// version token and the bare name denote the single assigned value).
#[test]
fn single_assignment_local_actual_is_licensed_bare() {
    let f = caller_with(vec![assign(2, 5)]); // t = 5 (its only def)
    assert_eq!(call_arg_fact_token(&f, &Operand::Copy(Place::local(2))).as_deref(), Some("t"));
}

/// A REASSIGNED non-parameter local is declined (two defs ⇒ the bare name is
/// not a licensed single spelling of the at-call value).
#[test]
fn reassigned_local_actual_is_declined() {
    let f = caller_with(vec![assign(2, 5), assign(2, 6)]); // t = 5; t = 6
    assert_eq!(call_arg_fact_token(&f, &Operand::Copy(Place::local(2))), None);
}

/// A constant actual has no variable spelling at all — declined (the
/// composition lane drops clauses over that formal, fail-closed).
#[test]
fn constant_actual_is_declined() {
    let f = caller_with(vec![]);
    assert_eq!(call_arg_fact_token(&f, &Operand::Constant(ConstValue::Int(7))), None);
}

//! A path set above the split cap must still connect the checked result to
//! this predecessor's actual return value. The captured Site::admits failure
//! had fifteen paths hidden under one Or, leaving its join-version result free.
use std::collections::BTreeMap;

use trust_types::{
    BasicBlock, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Rvalue, Sort, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}
fn write_result(value: bool) -> Statement {
    Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(value))),
        span: SourceSpan::default(),
    }
}
fn member() -> Formula {
    Formula::Or(
        (0..9)
            .map(|value| {
                Formula::Eq(
                    Box::new(Formula::Var("selector".into(), Sort::Int)),
                    Box::new(Formula::Int(value)),
                )
            })
            .collect(),
    )
}
fn fixture(expected: Formula, historical_return_guard: bool) -> VerifiableFunction {
    let mut blocks = vec![block(
        0,
        if historical_return_guard { vec![write_result(false)] } else { vec![] },
        Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(1)),
            targets: (0..9).map(|n| (n as u128, BlockId(n + 1))).collect(),
            otherwise: BlockId(10),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        },
    )];
    for id in 1..=9 {
        blocks.push(block(
            id,
            vec![],
            Terminator::Goto(BlockId(if historical_return_guard { 13 } else { 11 })),
        ));
    }
    blocks.push(block(10, vec![write_result(false)], Terminator::Goto(BlockId(12))));
    blocks.push(block(11, vec![write_result(true)], Terminator::Goto(BlockId(12))));
    blocks.push(block(12, vec![], Terminator::Return));
    if historical_return_guard {
        blocks.push(block(
            13,
            vec![],
            Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(0)),
                targets: vec![(0, BlockId(11))],
                otherwise: BlockId(10),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        ));
    }
    VerifiableFunction {
        name: "wide_return_join".into(),
        def_path: "test::wide_return_join".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Bool, name: None },
                LocalDecl { index: 1, ty: Ty::i64(), name: Some("selector".into()) },
            ],
            blocks,
            arg_count: 1,
            return_ty: Ty::Bool,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![Formula::Eq(
            Box::new(Formula::Var("_0".into(), Sort::Bool)),
            Box::new(expected),
        )],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}
fn rows(expected: Formula, historical: bool) -> Vec<Formula> {
    trust_vcgen::generate_vcs(&fixture(expected, historical))
        .into_iter()
        .filter(|vc| matches!(vc.kind, trust_types::VcKind::Postcondition))
        .map(|vc| vc.formula)
        .collect()
}
#[derive(Clone, Copy, Debug, PartialEq)]
enum Value {
    Bool(bool),
    Int(i128),
}
fn eval(f: &Formula, values: &BTreeMap<String, Value>) -> Value {
    let boolean = |f| match eval(f, values) {
        Value::Bool(v) => v,
        _ => panic!("expected Bool"),
    };
    let int = |f| match eval(f, values) {
        Value::Int(v) => v,
        _ => panic!("expected Int"),
    };
    match f {
        Formula::Bool(v) => Value::Bool(*v),
        Formula::Int(v) => Value::Int(*v),
        Formula::Var(n, _) => values[n],
        Formula::And(fs) => Value::Bool(fs.iter().all(boolean)),
        Formula::Or(fs) => Value::Bool(fs.iter().any(boolean)),
        Formula::Not(f) => Value::Bool(!boolean(f)),
        Formula::Eq(a, b) => Value::Bool(eval(a, values) == eval(b, values)),
        Formula::Ge(a, b) => Value::Bool(int(a) >= int(b)),
        Formula::Le(a, b) => Value::Bool(int(a) <= int(b)),
        other => panic!("unexpected fixture formula: {other:?}"),
    }
}
fn satisfiable(f: &Formula) -> bool {
    let mut vars = BTreeMap::new();
    f.visit(&mut |node| {
        if let Formula::Var(name, sort) = node {
            vars.insert(name.clone(), sort.clone());
        }
    });
    let vars: Vec<_> = vars.into_iter().collect();
    let values: Vec<_> = vars
        .iter()
        .map(|(_, sort)| match sort {
            Sort::Bool => vec![Value::Bool(false), Value::Bool(true)],
            Sort::Int => [-1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 64, i64::MIN as i128, i64::MAX as i128]
                .into_iter()
                .map(Value::Int)
                .collect(),
            other => panic!("unexpected fixture sort: {other:?}"),
        })
        .collect();
    fn search(
        f: &Formula,
        vars: &[(String, Sort)],
        values: &[Vec<Value>],
        env: &mut BTreeMap<String, Value>,
        at: usize,
    ) -> bool {
        if at == vars.len() {
            return eval(f, env) == Value::Bool(true);
        }
        for value in &values[at] {
            env.insert(vars[at].0.clone(), *value);
            if search(f, vars, values, env, at + 1) {
                return true;
            }
        }
        false
    }
    search(f, &vars, &values, &mut BTreeMap::new(), 0)
}
#[test]
fn unsplit_wide_join_connects_true_clause_without_adding_rows() {
    let rows = rows(member(), false);
    assert_eq!(rows.len(), 2, "keep the existing path-splitting cap");
    assert!(
        rows.iter().all(|row| !satisfiable(row)),
        "a correct clause must not read an unconstrained join result"
    );
}
#[test]
fn unsplit_wide_join_keeps_false_clause_refutable() {
    let rows = rows(Formula::Bool(false), false);
    assert_eq!(rows.len(), 2);
    assert!(rows.iter().any(satisfiable), "the real true return must still refute false");
}
#[test]
fn historical_return_guard_does_not_turn_false_clause_into_proof() {
    let all = trust_vcgen::generate_vcs(&fixture(Formula::Bool(false), true));
    assert_eq!(all.len(), 2);
    assert!(all.iter().all(|vc| matches!(vc.kind, trust_types::VcKind::Postcondition)));
    assert!(
        all.iter().any(|vc| satisfiable(&vc.formula)),
        "a guard reading the old false result must not be rebound to the final true result"
    );
    assert!(all.iter().any(|vc| trust_certify::certify_vc_reporting_stop(vc).0.is_none()));
}

#[test]
fn unsplit_wide_join_correct_clause_is_kernel_certified() {
    let all = trust_vcgen::generate_vcs(&fixture(member(), false));
    assert_eq!(all.len(), 2);
    for vc in all {
        let (proof, stop) = trust_certify::certify_vc_reporting_stop(&vc);
        assert!(
            proof.is_some(),
            "correct generated row did not certify: {stop:?}; {:?}",
            vc.formula
        );
    }
}

#[test]
fn return_block_overwrite_does_not_pin_the_predecessors_old_value() {
    let mut function = fixture(Formula::Bool(false), false);
    function.body.blocks[12].stmts.push(write_result(true));
    let all = trust_vcgen::generate_vcs(&function);
    assert_eq!(all.len(), 2);
    assert!(
        all.iter().all(|vc| satisfiable(&vc.formula)),
        "every return is true after the overwrite"
    );
}

#[test]
fn return_slot_update_reads_its_previous_value() {
    let mut function = fixture(Formula::Bool(false), false);
    function.body.blocks = vec![block(
        0,
        vec![
            write_result(false),
            Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::UnaryOp(trust_types::UnOp::Not, Operand::Copy(Place::local(0))),
                span: SourceSpan::default(),
            },
        ],
        Terminator::Return,
    )];
    let all = trust_vcgen::generate_vcs(&function);
    assert_eq!(all.len(), 1);
    assert!(satisfiable(&all[0].formula), "false followed by logical not returns true");
    assert!(trust_certify::certify_vc_reporting_stop(&all[0]).0.is_none());
}

#[test]
fn missing_return_definition_is_an_explicit_refusal() {
    let mut function = fixture(Formula::Bool(false), false);
    // Deliberately malformed input: a bool return with no initialized result.
    function.body.blocks = vec![block(0, vec![], Terminator::Return)];
    let all = trust_vcgen::generate_vcs(&function);
    assert_eq!(all.len(), 1);
    assert!(matches!(&all[0].kind, trust_types::VcKind::UnsupportedMir { detail, .. }
        if detail.contains("no established return-path value")));
    assert!(trust_certify::certify_vc_reporting_stop(&all[0]).0.is_none());
}

#[test]
fn call_destination_does_not_reuse_the_pre_call_result() {
    let mut function = fixture(Formula::Bool(false), false);
    function.body.blocks = vec![
        block(
            0,
            vec![write_result(false)],
            Terminator::Call {
                func: "unknown_bool".into(),
                args: vec![],
                dest: Place::local(0),
                target: Some(BlockId(1)),
                unwind: trust_types::UnwindEdge::Unreachable,
                span: SourceSpan::default(),
                atomic: None,
                is_unsafe_sig: false,
                callee_identity: None,
                callee_key: None,
                is_foreign: false,
            },
        ),
        block(1, vec![], Terminator::Return),
    ];
    let all = trust_vcgen::generate_vcs(&function);
    assert!(!all.is_empty());
    assert!(all.iter().any(|vc| satisfiable(&vc.formula)));
    assert!(all.iter().any(|vc| trust_certify::certify_vc_reporting_stop(vc).0.is_none()));
}

#[test]
fn result_rebinding_does_not_capture_a_quantified_symbol() {
    let mut function = fixture(Formula::Bool(true), false);
    // A typed formula can already contain the spelling the result will receive.
    // Its bound occurrence must remain independent of the actual return value.
    function.postconditions[0] = Formula::And(vec![
        function.postconditions[0].clone(),
        Formula::Forall(
            vec![("_0#s11_0".into(), Sort::Bool)],
            Box::new(Formula::Var("_0#s11_0".into(), Sort::Bool)),
        ),
    ]);
    let all = trust_vcgen::generate_vcs(&function);
    let mut saw_alpha_renamed = false;
    for vc in all {
        vc.formula.visit(&mut |node| {
            if let Formula::Forall(bindings, body) = node {
                if bindings[0].0.as_str() != "_0#s11_0" {
                    saw_alpha_renamed = true;
                    assert_eq!(body.var_name(), Some(bindings[0].0.as_str()));
                }
            }
        });
    }
    assert!(saw_alpha_renamed, "the replacement must not capture an existing binder");
}

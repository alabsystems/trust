//! An opaque call still returns an inhabitant of its declared scalar type.
//! These exercise the shared body-aware postcondition lane and its real Clean
//! certificate path, including false signed/cast/wrapping controls.

use trust_types::{BasicBlock, LocalDecl, UnwindEdge, VerifiableBody};

use super::*;

fn int(name: &str) -> Formula {
    Formula::var(name, Sort::Int)
}

fn copy(local: usize) -> Operand {
    Operand::Copy(Place::local(local))
}

fn assign(local: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(local), rvalue, span: SourceSpan::default() }
}

fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}

fn ret(id: usize, value: Operand) -> BasicBlock {
    block(id, vec![assign(0, Rvalue::Use(value))], Terminator::Return)
}

fn switch(discr: usize, zero: usize, otherwise: usize) -> Terminator {
    Terminator::SwitchInt {
        discr: copy(discr),
        targets: vec![(0, BlockId(zero))],
        otherwise: BlockId(otherwise),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    }
}

fn function(ty: Ty) -> VerifiableFunction {
    let literal = |n| {
        Operand::Constant(if ty.is_signed() {
            ConstValue::Int(n)
        } else {
            ConstValue::Uint(n as u128, ty.int_width().unwrap())
        })
    };
    VerifiableFunction {
        name: "split_budget_ms".into(),
        def_path: "test::split_budget_ms".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: [
                (ty.clone(), None),
                (ty.clone(), Some("total_ms")),
                (ty.clone(), Some("parts")),
                (ty.clone(), Some("share")),
                (Ty::Bool, None),
                (Ty::Bool, None),
                (Ty::Bool, None),
            ]
            .into_iter()
            .enumerate()
            .map(|(index, (ty, name))| LocalDecl { index, ty, name: name.map(str::to_string) })
            .collect(),
            blocks: vec![
                block(
                    0,
                    vec![assign(4, Rvalue::BinaryOp(BinOp::Eq, copy(1), literal(0)))],
                    switch(4, 2, 1),
                ),
                ret(1, literal(0)),
                block(
                    2,
                    vec![],
                    Terminator::Call {
                        func: "test::raw_share".into(),
                        args: vec![copy(1), copy(2)],
                        dest: Place::local(3),
                        target: Some(BlockId(3)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                        unwind: UnwindEdge::Unreachable,
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key("test::raw_share"),
                    },
                ),
                block(
                    3,
                    vec![assign(5, Rvalue::BinaryOp(BinOp::Eq, copy(3), literal(0)))],
                    switch(5, 5, 4),
                ),
                ret(4, literal(1)),
                block(
                    5,
                    vec![assign(6, Rvalue::BinaryOp(BinOp::Gt, copy(3), copy(1)))],
                    switch(6, 7, 6),
                ),
                ret(6, copy(1)),
                ret(7, copy(3)),
            ],
            arg_count: 2,
            return_ty: ty.clone(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        // Compiler type facts, not authored restrictions on the input domain.
        preconditions: ["total_ms", "parts"]
            .into_iter()
            .map(|name| crate::range::rust_type_range_constraint(&int(name), &ty).unwrap())
            .collect(),
        postconditions: vec![
            Formula::Le(Box::new(int("_0")), Box::new(int("total_ms"))),
            Formula::Implies(
                Box::new(Formula::Gt(Box::new(int("total_ms")), Box::new(Formula::Int(0)))),
                Box::new(Formula::Gt(Box::new(int("_0")), Box::new(Formula::Int(0)))),
            ),
        ],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn rows(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    crate::validate_function(func).expect("well-formed typed fixture");
    let rows = crate::generate_vcs(func);
    assert!(
        rows.iter().all(|vc| !matches!(&vc.kind,
        VcKind::UnsupportedMir { kind, .. } if kind == crate::contracts::SPEC_UNVERIFIABLE_KIND)),
        "{rows:?}"
    );
    let posts: Vec<_> =
        rows.into_iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).collect();
    assert!(!posts.is_empty());
    posts
}

fn verify(vc: &VerificationCondition) -> VerificationResult {
    crate::test_router::shipped_vc_clock_router()
        .verify_all(std::slice::from_ref(vc))
        .pop()
        .unwrap()
        .1
}

#[test]
fn opaque_unsigned_share_and_return_prove_both_contracts_in_clean() {
    let func = function(Ty::u64());
    assert!(func.contracts.is_empty(), "no authored requires restricts the u64 domain");
    let rows = rows(&func);
    assert_eq!(rows.len(), 8, "both clauses on all four returns");
    let mut missing = Vec::new();
    let capture = std::env::var_os("TRUST_TEST_POSTCONDITION_ROWS");
    let mut measurements = Vec::new();
    for (index, vc) in rows.iter().enumerate() {
        assert!(matches!(verify(vc), VerificationResult::Proved { .. }), "row {index}: {vc:?}");
        let before = capture.as_ref().map(|_| {
            let Formula::And(parts) = &vc.formula else { panic!("missing carrier wrapper") };
            let mut before = vc.clone();
            before.formula = parts.last().unwrap().clone();
            assert_eq!(
                conjoin_postcondition_value_type_ranges(&func, before.formula.clone()),
                vc.formula
            );
            let started = std::time::Instant::now();
            let (evidence, stop) = trust_certify::certify_vc_reporting_stop(&before);
            let seconds = started.elapsed().as_secs_f64();
            let verdict = verify(&before);
            serde_json::json!({
                "nodes": crate::simplify::measure_size(&before.formula),
                "json_bytes": serde_json::to_vec(&before.formula).unwrap().len(),
                "clean": evidence.is_some(), "stop": format!("{stop:?}"),
                "clean_seconds": seconds,
                "ay_proved": matches!(verdict, VerificationResult::Proved { .. }),
                "ay_failed": matches!(verdict, VerificationResult::Failed { .. }),
            })
        });
        let started = std::time::Instant::now();
        let (evidence, stop) = trust_certify::certify_vc_reporting_stop(vc);
        let seconds = started.elapsed().as_secs_f64();
        eprintln!("unsigned budget row {index}: Clean={} stop={stop:?}", evidence.is_some());
        measurements.push(serde_json::json!({
            "row": index, "before_carriers": before,
            "nodes": crate::simplify::measure_size(&vc.formula),
            "json_bytes": serde_json::to_vec(&vc.formula).unwrap().len(),
            "clean": evidence.is_some(), "stop": format!("{stop:?}"), "clean_seconds": seconds,
        }));
        if evidence.is_none() {
            missing.push(index);
        }
    }
    if let Some(path) = capture {
        use std::io::Write;
        let mut file = std::fs::OpenOptions::new().write(true).create_new(true).open(path).unwrap();
        file.write_all(&serde_json::to_vec_pretty(&serde_json::json!({
            "schema": 1, "function": func, "rows": rows, "measurements": measurements,
            "timing_scope": "one process, original carrier input first, augmented row second; representative only",
        })).unwrap()).unwrap();
    }
    assert!(missing.is_empty(), "budget rows missing real Clean rechecks: {missing:?}");
}

#[test]
fn a_signed_opaque_share_can_be_negative() {
    let rows = rows(&function(Ty::i64()));
    let positivity = rows.last().unwrap();
    assert!(matches!(verify(positivity), VerificationResult::Failed { .. }));
    assert!(trust_certify::certify_vc(positivity).is_none());
}

#[test]
fn removing_the_zero_share_guard_keeps_the_real_counterexample() {
    let mut func = function(Ty::u64());
    func.body.blocks[3].terminator = Terminator::Goto(BlockId(5));
    let rows = rows(&func);
    assert!(rows.iter().any(|vc| matches!(verify(vc), VerificationResult::Failed { .. })));
    assert!(rows.iter().any(|vc| trust_certify::certify_vc(vc).is_none()));
}

fn straight_line(src: Ty, dst: Ty, rvalue: Rvalue, post: Formula) -> VerifiableFunction {
    let mut func = function(dst.clone());
    func.body.locals = vec![
        LocalDecl { index: 0, ty: dst.clone(), name: None },
        LocalDecl { index: 1, ty: src, name: Some("x".into()) },
        LocalDecl { index: 2, ty: dst, name: Some("value".into()) },
    ];
    func.body.arg_count = 1;
    func.preconditions =
        vec![crate::range::rust_type_range_constraint(&int("x"), &func.body.locals[1].ty).unwrap()];
    func.body.blocks = vec![block(
        0,
        vec![assign(2, rvalue), assign(0, Rvalue::Use(copy(2)))],
        Terminator::Return,
    )];
    func.postconditions = vec![post];
    func
}

#[test]
fn signed_narrowing_cast_does_not_acquire_nonnegativity() {
    let func = straight_line(
        Ty::u64(),
        Ty::i8(),
        Rvalue::Cast(copy(1), Ty::i8()),
        Formula::Ge(Box::new(int("_0")), Box::new(Formula::Int(0))),
    );
    let rows = rows(&func);
    assert_eq!(rows.len(), 1);
    assert!(matches!(verify(&rows[0]), VerificationResult::Failed { .. }));
    assert!(trust_certify::certify_vc(&rows[0]).is_none());
}

#[test]
fn signed_to_unsigned_cast_does_not_keep_the_source_upper_bound() {
    let func = straight_line(
        Ty::i64(),
        Ty::u64(),
        Rvalue::Cast(copy(1), Ty::u64()),
        Formula::Le(Box::new(int("_0")), Box::new(Formula::Int(i64::MAX.into()))),
    );
    let rows = rows(&func);
    assert_eq!(rows.len(), 1);
    assert!(matches!(verify(&rows[0]), VerificationResult::Failed { .. }));
    assert!(trust_certify::certify_vc(&rows[0]).is_none());
}

#[test]
fn wrapping_subtraction_return_still_admits_zero_minus_one() {
    let mut func = straight_line(
        Ty::u64(),
        Ty::u64(),
        Rvalue::BinaryOp(BinOp::Sub, copy(1), Operand::Constant(ConstValue::Uint(1, 64))),
        Formula::Le(Box::new(int("_0")), Box::new(int("x"))),
    );
    func.preconditions.push(Formula::Eq(Box::new(int("x")), Box::new(Formula::Int(0))));
    let rows = rows(&func);
    assert_eq!(rows.len(), 1);
    assert!(matches!(verify(&rows[0]), VerificationResult::Failed { .. }));
    assert!(trust_certify::certify_vc(&rows[0]).is_none());
}

#[test]
fn the_unsigned_maximum_remains_a_real_return_value() {
    let mut func = function(Ty::u64());
    func.postconditions =
        vec![Formula::Lt(Box::new(int("_0")), Box::new(Formula::Int(u64::MAX.into())))];
    let rows = rows(&func);
    let last = rows.last().unwrap();
    assert!(matches!(verify(last), VerificationResult::Failed { .. }));
    assert!(trust_certify::certify_vc(last).is_none());
}

#[test]
fn final_positive_row_needs_the_new_declared_carriers() {
    let func = function(Ty::u64());
    let rows = rows(&func);
    let last = rows.last().unwrap();
    assert!(matches!(verify(last), VerificationResult::Proved { .. }));
    let Formula::And(mut original_parts) = last.formula.clone() else {
        panic!("missing conjunction prefix")
    };
    let Some(Formula::And(mut bounds)) = original_parts.pop() else {
        panic!("missing carriers around the final body")
    };
    let body = bounds.pop().expect("carriers and the original final body");
    assert!(!original_parts.is_empty(), "retain every original prefix conjunct");
    original_parts.push(body);
    let original = Formula::And(original_parts);
    assert_eq!(
        bounds,
        trust_types::postcondition_integer_carrier_facts(
            &func,
            &original,
            |decl| place_to_var_name(&func, &Place::local(decl.index)),
            crate::range::rust_type_range_constraint,
        ),
        "peel exactly the added carrier occurrences, preserving the full original row"
    );
    assert_eq!(conjoin_postcondition_value_type_ranges(&func, original.clone()), last.formula);
    let mut without = last.clone();
    without.formula = original;
    assert!(
        matches!(verify(&without), VerificationResult::Failed { .. }),
        "without the stored-value carriers a negative share is admitted"
    );
}

#[test]
fn declared_carriers_cover_ssa_locals_and_return_without_narrowing_signed_or_u128() {
    for ty in [Ty::u64(), Ty::i64(), Ty::u128(), Ty::i128()] {
        let func = function(ty.clone());
        let formula = Formula::Eq(Box::new(int("_0#s7_0")), Box::new(int("share#s2_t")));
        let ranged = conjoin_postcondition_value_type_ranges(&func, formula.clone());
        let Formula::And(parts) = ranged else { panic!("missing carriers for {ty:?}") };
        for name in ["_0#s7_0", "share#s2_t"] {
            assert!(
                parts.contains(&crate::range::rust_type_range_constraint(&int(name), &ty).unwrap())
            );
        }
        assert_eq!(parts.last(), Some(&formula));
    }
}

#[test]
fn ranges_do_not_retype_bitvectors_projections_or_ambiguous_ssa_names() {
    let mut func = function(Ty::u64());
    func.body.locals.push(LocalDecl { index: 7, ty: Ty::i64(), name: Some("share#e".into()) });
    let bv = Formula::Eq(
        Box::new(Formula::var("share", Sort::BitVec(64))),
        Box::new(Formula::BitVec { value: 0, width: 64 }),
    );
    for formula in [
        bv.clone(),
        Formula::And(vec![bv, Formula::Eq(Box::new(int("share")), Box::new(Formula::Int(0)))]),
        Formula::Eq(Box::new(int("share.0")), Box::new(Formula::Int(0))),
        Formula::Eq(Box::new(int("share#e")), Box::new(Formula::Int(-1))),
    ] {
        assert_eq!(conjoin_postcondition_value_type_ranges(&func, formula.clone()), formula);
    }
}

#[test]
fn checked_result_functions_withhold_new_facts_even_for_multidefinition_return_aliases() {
    let mut func = function(Ty::u64());
    func.body.locals.push(LocalDecl {
        index: 7,
        ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]),
        name: None,
    });
    func.body.blocks[0]
        .stmts
        .insert(0, assign(7, Rvalue::CheckedBinaryOp(BinOp::Sub, copy(1), copy(2))));
    // This is a possible checked-result alias with multiple whole-local defs;
    // the existing unique-definition closure deliberately does not cover it.
    func.body.blocks[0].stmts.push(assign(
        3,
        Rvalue::Use(Operand::Copy(Place { local: 7, projections: vec![Projection::Field(0)] })),
    ));
    let formula = Formula::Eq(Box::new(int("_0#s7_0")), Box::new(int("share#s2_t")));
    assert_eq!(conjoin_postcondition_value_type_ranges(&func, formula.clone()), formula);
}

#[test]
fn aliased_callbacks_and_duplicate_indices_never_overwrite_carriers() {
    let mut func = function(Ty::u64());
    let formula = Formula::Eq(Box::new(int("total_ms")), Box::new(Formula::Int(-1)));
    let ambiguous = trust_types::conjoin_postcondition_integer_carriers(
        &func,
        formula.clone(),
        |_| "total_ms".into(),
        crate::range::rust_type_range_constraint,
    );
    assert_eq!(ambiguous, formula, "a local callback cannot range-bound a parameter alias");
    func.body.locals.push(LocalDecl { index: 3, ty: Ty::i64(), name: Some("other".into()) });
    let formula = Formula::Eq(Box::new(int("share")), Box::new(Formula::Int(-1)));
    assert_eq!(conjoin_postcondition_value_type_ranges(&func, formula.clone()), formula);
}

#[test]
fn sparse_reordered_local_tables_keep_declared_identity() {
    let mut func = function(Ty::u64());
    func.body.locals[3].index = 30;
    func.body.locals.reverse();
    let formula = Formula::Eq(Box::new(int("share#s2_t")), Box::new(Formula::Int(3)));
    let Formula::And(parts) = conjoin_postcondition_value_type_ranges(&func, formula) else {
        panic!("lost sparse local")
    };
    assert!(parts.contains(
        &crate::range::rust_type_range_constraint(&int("share#s2_t"), &Ty::u64()).unwrap()
    ));
}

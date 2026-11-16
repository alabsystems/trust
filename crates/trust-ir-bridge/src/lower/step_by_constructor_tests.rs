//! Retained compiler-extracted bodies, not a replacement StepBy model.
//!
//! These ignored controls consume an explicitly supplied, source-bound extract
//! directory. The development harness records its exact bytes before/after.
//! A passing bridge test does not establish compiler import or solver support.

use super::*;

fn retained() -> Vec<trust_types::VerifiableFunction> {
    let directory = std::path::PathBuf::from(
        std::env::var_os("TRUST_STEP_BY_CONSTRUCTOR_EXTRACTS")
            .expect("supply the retained u8_specialized/extracts directory"),
    );
    [
        "trust-mir-e04fcdb5a4e80ca6-11f3b595c55129e1.json",
        "trust-mir-a8d3b20d2ad8d04-26c4cafed7e3cfe7.json",
        "trust-mir-6c3bbfa8301979a2-e38b9c5e4e4780ed.json",
    ]
    .iter()
    .map(|file| {
        let bytes = std::fs::read(directory.join(file)).expect("read retained extract");
        let mut function: trust_types::VerifiableFunction =
            serde_json::from_slice(&bytes).expect("parse retained extract");
        // The compiler's importer makes this exact naming adjustment. Its
        // independent CalleeIdentity/source-ledger checks are not simulated here.
        function.name = function.def_path.clone();
        function
    })
    .collect()
}

fn calls(function: &TrustIrFunction, callee: FuncId) -> usize {
    function
        .blocks
        .iter()
        .flat_map(|block| &block.body)
        .filter(|node| matches!(node.inst, Inst::Call { callee: actual, .. } if actual == callee))
        .count()
}

#[test]
#[ignore = "requires source-bound retained compiler extracts"]
fn retained_constructor_closure_preserves_calls_state_and_safety_sites() {
    let functions = retained();
    let module = lower_to_trust_ir_functions("step_by_constructor", &functions)
        .expect("actual constructor closure must lower without deleting cleanup or safety");
    if let Some(output) = std::env::var_os("TRUST_STEP_BY_CONSTRUCTOR_MODULE") {
        let file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(output)
            .expect("create fresh diagnostic module");
        serde_json::to_writer_pretty(file, &module).expect("retain diagnostic module");
    }
    assert_eq!(module.functions.len(), 3);
    assert_eq!(calls(&module.functions[0], module.functions[1].id), 1);
    assert_eq!(calls(&module.functions[1], module.functions[2].id), 1);
    assert!(
        module.functions[1]
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .any(|node| matches!(node.inst, Inst::InsertField { field: 2, .. })),
        "first_take must remain actual constructed state"
    );
    assert!(
        module.functions[1]
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .any(|node| matches!(node.inst, Inst::Assert { .. })),
        "zero-step panic must remain reachable through the constructor's branch"
    );
    for member in &module.functions[1..] {
        assert!(
            module.proof_obligations.iter().any(|row| {
                row.function == Some(member.id) && row.status == ProofStatus::Pending
            }),
            "each hazardous member must own a pending safety row"
        );
    }
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "actual closure must remain well typed: {errors:?}");
}

#[test]
#[ignore = "requires source-bound retained compiler extracts"]
fn retained_setup_has_one_shared_division_guard_and_no_entry_prefix_authority() {
    let functions = retained();
    let setup = &functions[2];
    let asserts: Vec<_> = setup
        .body
        .blocks
        .iter()
        .filter_map(|block| match &block.terminator {
            Terminator::Assert { msg, target, .. } => Some((block.id, msg, *target)),
            _ => None,
        })
        .collect();
    assert_eq!(asserts.len(), 1, "do not manufacture a second remainder Assert");
    assert!(matches!(asserts[0].1, AssertMessage::DivisionByZero));
    let target = setup.body.blocks.iter().find(|block| block.id == asserts[0].2).unwrap();
    let operations: Vec<_> = target
        .stmts
        .iter()
        .filter_map(|statement| match statement {
            Statement::Assign {
                rvalue: Rvalue::BinaryOp(op @ (BinOp::Div | BinOp::Rem), _, rhs),
                ..
            } => Some((*op, rhs)),
            _ => None,
        })
        .collect();
    assert_eq!(operations.len(), 2);
    assert_eq!(
        serde_json::to_value(operations[0].1).unwrap(),
        serde_json::to_value(operations[1].1).unwrap(),
        "the shared guard checks the same step"
    );
    assert!(
        matches!(
            bundled_member_assert_admission(setup),
            BundledMemberAssertAdmission::Refused { .. }
        ),
        "the old unguarded-entry lane must not grant authority to this conditional body"
    );
}

#[test]
#[ignore = "requires source-bound retained compiler extracts"]
fn retained_constructor_without_its_body_keeps_owned_absent_obligation() {
    let functions = retained();
    let module = lower_to_trust_ir_functions("step_by_missing_constructor", &functions[..1])
        .expect("missing constructor must be a typed, explicitly pending call");
    assert_eq!(module.functions.len(), 1);
    step2b_call_boundary_controls::assert_owned_pending_absent(&module, module.functions[0].id);
}

#[test]
#[ignore = "requires source-bound retained compiler extracts"]
fn retained_setup_local_site_is_exact_and_shared_without_strengthening_guards() {
    let functions = retained();
    let setup = &functions[2];
    let sites = bundled_constructor_local_safety_sites(setup).expect("derive actual setup site");
    assert_eq!(sites.len(), 1);
    assert_eq!(sites[0].block, BlockId(3));
    assert_eq!(sites[0].guarded_operations, vec![(BlockId(7), 0), (BlockId(7), 2)]);
    let rhs = collision_safe_local_name(&setup.body.locals, 2);
    assert_eq!(
        sites[0].requirement,
        Formula::Implies(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Not(Box::new(Formula::Eq(
                Box::new(Formula::var(&rhs, Sort::Int)),
                Box::new(Formula::Int(0)),
            )))),
        )
    );
    let ctor = bundled_constructor_local_safety_sites(&functions[1])
        .expect("derive actual zero-step panic guard");
    assert_eq!(ctor.len(), 1);
    assert_eq!(ctor[0].block, BlockId(2));
    assert!(
        matches!(&ctor[0].requirement, Formula::Implies(guard, consequence)
        if **guard != Formula::Bool(true) && **consequence == Formula::Bool(false)),
        "the constructor panic must retain its conditional reachability"
    );
}

#[test]
#[ignore = "requires source-bound retained compiler extracts"]
fn retained_setup_mutated_condition_or_remainder_cannot_reuse_the_site() {
    let functions = retained();
    let mut wrong_condition = functions[2].clone();
    if let Terminator::Assert { expected, .. } = &mut wrong_condition.body.blocks[3].terminator {
        *expected = true;
    } else {
        panic!("retained assertion changed");
    }
    assert!(bundled_constructor_local_safety_sites(&wrong_condition).is_err());

    let mut wrong_remainder = functions[2].clone();
    if let Statement::Assign { rvalue: Rvalue::BinaryOp(BinOp::Rem, _, rhs), .. } =
        &mut wrong_remainder.body.blocks[7].stmts[2]
    {
        *rhs = Operand::Constant(ConstValue::Uint(0, 64));
    } else {
        panic!("retained remainder changed");
    }
    assert!(bundled_constructor_local_safety_sites(&wrong_remainder).is_err());

    let mut rewritten_step = functions[2].clone();
    rewritten_step.body.blocks[7].stmts.insert(
        0,
        Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
            span: TrustSourceSpan::default(),
        },
    );
    assert!(bundled_constructor_local_safety_sites(&rewritten_step).is_err());
}

#[test]
#[ignore = "requires source-bound retained compiler extracts"]
fn retained_setup_predicate_temporary_aliases_cannot_reuse_old_definition() {
    let functions = retained();
    let admitted: Vec<_> = (0..4)
        .map(|kind| {
            let mut setup = functions[2].clone();
            let local = setup.body.locals.iter().map(|local| local.index).max().unwrap() + 1;
            let mutable = kind % 2 == 0;
            let (ty, borrow) = if kind < 2 {
                (
                    Ty::RawPtr { mutable, pointee: Box::new(Ty::Bool) },
                    Rvalue::AddressOf(mutable, Place::local(18)),
                )
            } else {
                (
                    Ty::Ref { mutable, inner: Box::new(Ty::Bool) },
                    Rvalue::Ref { mutable, place: Place::local(18) },
                )
            };
            setup.body.locals.push(LocalDecl { index: local, ty, name: None });
            setup.body.blocks[3].stmts.push(Statement::Assign {
                place: Place::local(local),
                rvalue: borrow,
                span: TrustSourceSpan::default(),
            });
            // The mutable-pointer case changes the real asserted condition through
            // another local. Shared/raw-const address-taking are close conservative
            // refusal controls and do not contain an ill-typed direct store.
            if kind == 0 {
                setup.body.blocks[3].stmts.push(Statement::Assign {
                    place: Place { local, projections: vec![Projection::Deref] },
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(false))),
                    span: TrustSourceSpan::default(),
                });
            }
            bundled_constructor_local_safety_sites(&setup).is_ok()
        })
        .collect();
    assert_eq!(admitted, vec![false; 4], "no predicate alias may reuse its old Eq definition");
}

#[test]
#[ignore = "requires source-bound retained compiler extracts"]
fn retained_setup_bypass_and_cycle_cannot_gain_an_unconditional_charge() {
    let functions = retained();
    let mut bypass = functions[2].clone();
    bypass.body.blocks[2].terminator = Terminator::Return;
    assert!(
        bundled_constructor_local_safety_sites(&bypass).is_err(),
        "a bypass requires a faithfully represented range guard, not unconditional step!=0"
    );
    let mut cycle = functions[2].clone();
    cycle.body.blocks[2].terminator = Terminator::Goto(BlockId(2));
    assert_eq!(
        bundled_constructor_local_safety_sites(&cycle).unwrap_err(),
        "cyclic constructor CFG"
    );
}

#[test]
#[ignore = "requires source-bound retained compiler extracts"]
fn repeated_constructor_diamonds_share_guard_analysis_without_exponential_work() {
    let functions = retained();
    let mut function = functions[1].clone();
    let panic = function.body.blocks[2].terminator.clone();
    function.body.blocks = (0..30)
        .map(|index| TrustBlock {
            id: BlockId(index),
            stmts: Vec::new(),
            terminator: Terminator::SwitchInt {
                discr: Operand::Constant(ConstValue::Bool(false)),
                targets: vec![(0, BlockId(index + 1))],
                otherwise: BlockId(index + 1),
                exhaustive_enum_unreachable: false,
                span: TrustSourceSpan::default(),
            },
        })
        .collect();
    function.body.blocks.push(TrustBlock { id: BlockId(30), stmts: Vec::new(), terminator: panic });
    // The retained panic's old cleanup target (bb6) points back into this NEW
    // synthetic chain. Keep that accidental-cycle shape as a negative control,
    // then make the synthetic panic propagate out of this function.
    assert_eq!(
        bundled_constructor_local_safety_sites(&function).unwrap_err(),
        "cyclic constructor CFG"
    );
    if let Terminator::Call { unwind, .. } = &mut function.body.blocks[30].terminator {
        *unwind = trust_types::UnwindEdge::Continue;
    } else {
        unreachable!()
    }
    let sites =
        bundled_constructor_local_safety_sites(&function).expect("shared suffixes are memoized");
    assert_eq!(sites.len(), 1);
    assert_eq!(
        sites[0].requirement,
        Formula::Implies(Box::new(Formula::Bool(true)), Box::new(Formula::Bool(false)),)
    );
}

#[test]
#[ignore = "requires source-bound retained compiler extracts"]
fn retained_transitive_site_rebinds_actual_step_and_keeps_constructor_guard() {
    let mut functions = retained();
    // Name separation makes missed substitution observable; a child spelling
    // cannot accidentally alias the parent's equally named `step`.
    functions[2].body.locals.iter_mut().find(|local| local.index == 2).unwrap().name =
        Some("nested_divisor".into());
    let [step_by, constructor, setup] = functions.as_slice() else { unreachable!() };
    let setup_site = bundled_constructor_local_safety_sites(setup).unwrap().remove(0);
    let constructor_call = bundled_constructor_call_sites(constructor).unwrap().remove(0);
    assert_eq!(constructor_call.block, BlockId(1));
    assert_ne!(constructor_call.guard, Formula::Bool(true));
    let in_constructor = bundled_constructor_rebind_requirement(
        constructor,
        &constructor_call,
        setup,
        &setup_site.requirement,
    )
    .expect("bind setup's actual divisor through the guarded call");
    assert!(matches!(&in_constructor, Formula::Implies(guard, _)
        if **guard == constructor_call.guard));
    let outer_call = bundled_constructor_call_sites(step_by).unwrap().remove(0);
    let in_step_by =
        bundled_constructor_rebind_requirement(step_by, &outer_call, constructor, &in_constructor)
            .expect("bind the same source site through the actual outer call");
    let names = bundled_constructor_formal_names(step_by);
    assert_eq!(
        trust_types::collect_free_var_decls(&in_step_by).into_iter().collect::<Vec<_>>(),
        vec![(names[1].clone(), Sort::Int)]
    );

    let mut stale_call = constructor_call.clone();
    stale_call.arguments[1] = Operand::Constant(ConstValue::Uint(0, 64));
    assert!(
        bundled_constructor_rebind_requirement(
            constructor,
            &stale_call,
            setup,
            &setup_site.requirement
        )
        .is_err(),
        "stale actuals cannot be substituted under a current guard"
    );
    let mut changed_constructor = constructor.clone();
    if let Terminator::Call { args, .. } = &mut changed_constructor.body.blocks[1].terminator {
        args[1] = Operand::Constant(ConstValue::Uint(0, 64));
    } else {
        panic!("retained setup call changed");
    }
    let changed_call = bundled_constructor_call_sites(&changed_constructor).unwrap().remove(0);
    let changed = bundled_constructor_rebind_requirement(
        &changed_constructor,
        &changed_call,
        setup,
        &setup_site.requirement,
    )
    .unwrap();
    assert_ne!(
        changed, in_constructor,
        "same instance with a zero actual owes a different predicate"
    );
}

#[test]
#[ignore = "requires source-bound retained compiler extracts"]
fn actual_caller_keeps_four_required_nested_safety_charges_at_two_distinct_sites() {
    let functions = retained();
    let [entry, constructor, setup] = functions.as_slice() else { unreachable!() };
    let outer = bundled_constructor_call_sites(entry).unwrap().remove(0);
    let inner = bundled_constructor_call_sites(constructor).unwrap().remove(0);
    let panic = bundled_constructor_local_safety_sites(constructor).unwrap().remove(0);
    let division = bundled_constructor_local_safety_sites(setup).unwrap().remove(0);
    let in_constructor =
        bundled_constructor_rebind_requirement(constructor, &inner, setup, &division.requirement)
            .unwrap();
    let requirements = [
        bundled_constructor_rebind_requirement(entry, &outer, constructor, &panic.requirement)
            .unwrap(),
        bundled_constructor_rebind_requirement(entry, &outer, constructor, &in_constructor)
            .unwrap(),
    ];
    let mut summary = trust_vcgen::FunctionSummary::new(entry.name.clone())
        .with_param_names(bundled_constructor_formal_names(entry))
        .with_param_types(
            (1..=entry.body.arg_count)
                .map(|index| {
                    entry.body.locals.iter().find(|local| local.index == index).unwrap().ty.clone()
                })
                .collect(),
        );
    for requirement in requirements {
        summary = summary.with_precondition(requirement);
    }
    let mut db = trust_vcgen::SummaryDatabase::new();
    db.insert(summary);
    let mut root = entry.clone();
    root.name = "constructor_test::two_sites".into();
    root.def_path = root.name.clone();
    let mut call = root.body.blocks[0].terminator.clone();
    let directory =
        std::path::PathBuf::from(std::env::var_os("TRUST_STEP_BY_CONSTRUCTOR_EXTRACTS").unwrap());
    let incoming: trust_types::VerifiableFunction = serde_json::from_slice(
        &std::fs::read(directory.join("trust-mir-fe5b8b9e2f94644e-8f3912ea7c43c903.json")).unwrap(),
    )
    .unwrap();
    let identity = incoming
        .body
        .blocks
        .iter()
        .find_map(|block| match &block.terminator {
            Terminator::Call { func, callee_identity, .. } if func == &entry.name => {
                *callee_identity
            }
            _ => None,
        })
        .expect("actual retained incoming StepBy call identity");
    let Terminator::Call { func, callee_identity, target, span, .. } = &mut call else {
        unreachable!()
    };
    *func = entry.name.clone();
    *callee_identity = Some(identity);
    *target = Some(BlockId(3));
    span.line_start = 202;
    let mut zero = call.clone();
    let Terminator::Call { args, span, .. } = &mut zero else { unreachable!() };
    args[1] = Operand::Constant(ConstValue::Uint(0, 64));
    span.line_start = 101;
    root.body.blocks = vec![
        trust_types::BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(2)),
                targets: vec![(0, BlockId(1))],
                otherwise: BlockId(2),
                exhaustive_enum_unreachable: false,
                span: root.span.clone(),
            },
        },
        trust_types::BasicBlock { id: BlockId(1), stmts: vec![], terminator: zero },
        trust_types::BasicBlock { id: BlockId(2), stmts: vec![], terminator: call },
        trust_types::BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
    ];
    let vcs = trust_vcgen::generate_callsite_precondition_vcs(&root, &db);
    assert_eq!(
        vcs.len(),
        4,
        "only real safety checks are reported; no-drop facts are not proof credit"
    );
    assert_eq!(vcs.iter().filter(|vc| vc.location.line_start == 101).count(), 2);
    assert_eq!(vcs.iter().filter(|vc| vc.location.line_start == 202).count(), 2);
    assert_ne!(vcs[0].formula, vcs[2].formula, "zero and nonzero paths must differ");
    assert!(vcs.iter().all(|vc| matches!(&vc.kind,
        trust_types::VcKind::Precondition { callee } if callee == &entry.name)));
    if let Some(output) = std::env::var_os("TRUST_STEP_BY_CALLER_QUERIES") {
        let file = std::fs::OpenOptions::new().write(true).create_new(true).open(output).unwrap();
        serde_json::to_writer_pretty(file, &serde_json::json!({ "root": root, "vcs": vcs }))
            .unwrap();
    }
}

use super::*;

fn large(f: impl FnOnce() + Send + 'static) {
    crate::checker_core::run_on_large_stack(f).expect("MIR bridge control worker");
}
fn install(env: &mut Environment, declarations: Vec<Decl>) -> Result<(), String> {
    for declaration in declarations {
        let bytes = serialize_term(&declaration.value).unwrap();
        register(env, &declaration, &bytes)?;
    }
    Ok(())
}
fn check_eq(env: &Environment, ty: &str, actual: Expr, expected: Expr) -> Result<(), String> {
    let proof = serialize_term(&refl(c(ty), expected.clone())).unwrap();
    TypeChecker::new(env)
        .check_type(&deserialize_term(&proof).unwrap(), &eq(c(ty), actual, expected))
        .map_err(|e| format!("kernel observation: {e:?}"))
}
fn raw_observe(body: &ScalarMirBody, input: u8, fuel: u64) -> Expr {
    let body = body_term(body).unwrap();
    app(
        "rm_observe",
        [app(
            "rm_run",
            [
                n(fuel),
                body.clone(),
                app("rm_initial", [body, app("UInt8.ofNat", [n(input.into())])]),
            ],
        )],
    )
}
fn initial_frame(input: u8) -> Expr {
    frame(vec![
        (ScalarType::U16, None),
        (ScalarType::U8, Some(value_term(ScalarValue::U8(input)))),
        (ScalarType::U16, None),
        (ScalarType::CheckedU16, None),
    ])
}

fn without_retag(mut body: ScalarMirBody) -> ScalarMirBody {
    let ScalarMirStatement::Assign(_, ScalarMirRvalue::Use(_, retag)) =
        &mut body.blocks[1].statements[0]
    else {
        panic!("fixed successor must contain an explicit Use");
    };
    assert_eq!(*retag, ScalarMirRetag::Yes);
    *retag = ScalarMirRetag::No;
    body
}

#[test]
fn retag_kernel_rule_covers_both_bits_and_every_closed_scalar_carrier() {
    large(|| {
        let env = model::environment().unwrap();
        let moves =
            app("RMPlaces.cons", [place_term(&ScalarMirPlace::PairFlag(3)), c("RMPlaces.nil")]);
        for value in [
            ScalarValue::U8(0),
            ScalarValue::U8(255),
            ScalarValue::U16(0),
            ScalarValue::U16(65535),
            ScalarValue::Bool(false),
            ScalarValue::Bool(true),
            ScalarValue::CheckedU8(0, false),
            ScalarValue::CheckedU8(255, true),
            ScalarValue::CheckedU16(0, false),
            ScalarValue::CheckedU16(65535, true),
        ] {
            for retag in [ScalarMirRetag::No, ScalarMirRetag::Yes] {
                let rvalue =
                    rvalue_term(&ScalarMirRvalue::Use(ScalarMirOperand::Constant(value), retag));
                TypeChecker::new(&env).check_type(&rvalue, &c("RMRvalue")).unwrap();
                let actual = app("rm_rvalue", [c("SMFrame.nil"), moves.clone(), rvalue]);
                let expected = app("RMRead.value", [value_term(value), moves.clone()]);
                let mode = c(match retag {
                    ScalarMirRetag::No => "RMRetag.no",
                    ScalarMirRetag::Yes => "RMRetag.yes",
                });
                // Replay the universal datatype-elimination theorem, not a
                // host equality or a claim that these samples exhaust UInt16.
                let proof =
                    serialize_term(&app("rm_use_scalar_rule", [mode, expected.clone()])).unwrap();
                TypeChecker::new(&env)
                    .check_type(
                        &deserialize_term(&proof).unwrap(),
                        &eq(c("RMRead"), actual, expected),
                    )
                    .unwrap();
            }
        }
        // A changed value is not justified by the retag rule.
        assert!(
            check_eq(
                &env,
                "RMRead",
                app(
                    "rm_use",
                    [
                        c("RMRetag.yes"),
                        app("RMRead.value", [value_term(ScalarValue::U8(255)), moves.clone()])
                    ]
                ),
                app("RMRead.value", [value_term(ScalarValue::U8(0)), moves]),
            )
            .is_err()
        );
    });
}

#[test]
fn retag_preserves_successful_moves_and_all_failed_read_markers() {
    large(|| {
        let env = model::environment().unwrap();
        let checked_frame = frame(vec![(
            ScalarType::CheckedU16,
            Some(value_term(ScalarValue::CheckedU16(256, true))),
        )]);
        let flag = ScalarMirPlace::PairFlag(0);
        let moved = app("RMPlaces.cons", [place_term(&flag), c("RMPlaces.nil")]);
        for retag in [ScalarMirRetag::No, ScalarMirRetag::Yes] {
            let eval = |frame, moves, operand| {
                app("rm_rvalue", [frame, moves, rvalue_term(&ScalarMirRvalue::Use(operand, retag))])
            };
            check_eq(
                &env,
                "RMRead",
                eval(
                    checked_frame.clone(),
                    c("RMPlaces.nil"),
                    ScalarMirOperand::Move(flag.clone()),
                ),
                app("RMRead.value", [value_term(ScalarValue::Bool(true)), moved.clone()]),
            )
            .unwrap();
            for (frame, markers, operand, failure) in [
                (
                    checked_frame.clone(),
                    moved.clone(),
                    ScalarMirOperand::Copy(flag.clone()),
                    c("RMFailure.moved"),
                ),
                (
                    checked_frame.clone(),
                    moved.clone(),
                    ScalarMirOperand::Move(ScalarMirPlace::Local(0)),
                    c("RMFailure.moved"),
                ),
                (
                    initial_frame(1),
                    c("RMPlaces.nil"),
                    ScalarMirOperand::Move(ScalarMirPlace::Local(0)),
                    app("RMFailure.scalar", [c("SMFault.uninitialized")]),
                ),
                (
                    initial_frame(1),
                    moved.clone(),
                    ScalarMirOperand::Copy(ScalarMirPlace::Local(99)),
                    app("RMFailure.scalar", [c("SMFault.badLocal")]),
                ),
            ] {
                check_eq(
                    &env,
                    "RMRead",
                    eval(frame, markers.clone(), operand),
                    app("RMRead.fault", [failure, markers]),
                )
                .unwrap();
            }
            check_eq(
                &env,
                "RMRead",
                eval(
                    checked_frame.clone(),
                    moved.clone(),
                    ScalarMirOperand::Copy(ScalarMirPlace::PairValue(0)),
                ),
                app("RMRead.value", [value_term(ScalarValue::U16(256)), moved.clone()]),
            )
            .unwrap();
        }
        check_eq(
            &env,
            "RMRead",
            app(
                "rm_rvalue",
                [checked_frame, moved.clone(), rvalue_term(&ScalarMirRvalue::Unsupported)],
            ),
            app("RMRead.fault", [c("RMFailure.unsupported"), moved]),
        )
        .unwrap();
    });
}

#[test]
fn retag_equal_observations_do_not_erase_whole_body_identity() {
    large(|| {
        let base = model::environment().unwrap();
        for before in [true, false] {
            let original = if before { successor_before() } else { successor_after() };
            let changed = without_retag(original.clone());
            let original_term = body_term(&original).unwrap();
            let changed_term = body_term(&changed).unwrap();
            assert_ne!(
                serialize_term(&original_term).unwrap(),
                serialize_term(&changed_term).unwrap()
            );
            assert!(check_eq(&base, "RMBody", original_term, changed_term).is_err());
            for input in [0, 255] {
                check_eq(
                    &base,
                    "RMObservation",
                    raw_observe(&original, input, 5),
                    raw_observe(&changed, input, 5),
                )
                .unwrap();
            }
            let (left, right, name) = if before {
                (changed, successor_after(), "beforeBinding kernel proof")
            } else {
                (successor_before(), changed, "afterBinding kernel proof")
            };
            let mut env = base.clone();
            install(&mut env, fixed_definitions(&left, &right).unwrap()).unwrap();
            assert!(install(&mut env, body_bindings().unwrap()).unwrap_err().contains(name));
        }
    });
}

#[test]
fn public_construction_and_replay_refuse_changed_retag_bits_on_either_body() {
    // The existing positive test checks and replays the full canonical 266-term
    // closure. These controls also replace the public body definition bytes,
    // so merely catching a stale serialization cannot satisfy the test.
    for before in [true, false] {
        let original_before = successor_before();
        let original_after = successor_after();
        let (left, right, name, index) = if before {
            (
                without_retag(original_before.clone()),
                original_after.clone(),
                "beforeBinding kernel proof",
                0,
            )
        } else {
            (
                original_before.clone(),
                without_retag(original_after.clone()),
                "afterBinding kernel proof",
                1,
            )
        };
        let error = prove_successor_bridge(&left, &right)
            .err()
            .expect("changed retag bit must not mint a fixed-family certificate");
        assert!(error.contains(name), "{error}");
        let mut certificate = ScalarMirBridgeCertificate {
            family: ScalarMirSuccessorFamily::CopyFixture,
            before: left,
            after: right,
            terms: declarations(&original_before, &original_after)
                .unwrap()
                .into_iter()
                .map(|d| serialize_term(&d.value).unwrap())
                .collect(),
        };
        assert!(certificate.replay().unwrap_err().contains("fixed proof closure mismatch"));
        certificate.terms[index] = serialize_term(
            &body_term(if before { &certificate.before } else { &certificate.after }).unwrap(),
        )
        .unwrap();
        assert!(certificate.replay().unwrap_err().contains(name));
    }
}

#[test]
fn whole_body_kernel_bindings_refuse_latent_metadata_types_cfg_and_operands() {
    large(|| {
        let base = model::environment().unwrap();
        let original = successor_before();
        let mut mutations = Vec::new();
        let mut changed = original.clone();
        changed.abi = ScalarMirAbi::Unsupported;
        mutations.push(changed);
        let mut changed = original.clone();
        changed.argument_count = 2;
        mutations.push(changed);
        let mut changed = original.clone();
        changed.locals[0] = ScalarType::U8;
        mutations.push(changed);
        let mut changed = original.clone();
        changed.locals[1] = ScalarType::U16;
        mutations.push(changed);
        let mut changed = original.clone();
        changed.locals[3] = ScalarType::CheckedU8;
        mutations.push(changed);
        let mut changed = original.clone();
        changed.blocks[0].cleanup = true;
        mutations.push(changed);
        let mut changed = original.clone();
        changed.blocks[1].terminator = ScalarMirTerminator::Goto(0);
        mutations.push(changed);
        let mut changed = original.clone();
        changed.blocks[0].statements.swap(0, 1);
        mutations.push(changed);
        let mut changed = original.clone();
        changed.blocks[0].statements.push(ScalarMirStatement::StorageLive(3));
        mutations.push(changed);
        let mut changed = original.clone();
        changed.blocks[0].statements.push(ScalarMirStatement::StorageDead(3));
        mutations.push(changed);
        let mut changed = original.clone();
        changed.blocks[0].statements[0] = ScalarMirStatement::Unsupported;
        mutations.push(changed);
        let mut changed = original.clone();
        changed.blocks.push(changed.blocks[1].clone());
        mutations.push(changed);
        let mut changed = original.clone();
        changed.blocks[1].statements[0] = ScalarMirStatement::Assign(
            0,
            ScalarMirRvalue::Use(
                ScalarMirOperand::Copy(ScalarMirPlace::PairFlag(3)),
                ScalarMirRetag::Yes,
            ),
        );
        mutations.push(changed);
        let mut changed = original.clone();
        changed.blocks[1].statements[0] = ScalarMirStatement::Assign(
            0,
            ScalarMirRvalue::Use(
                ScalarMirOperand::Move(ScalarMirPlace::PairValue(3)),
                ScalarMirRetag::Yes,
            ),
        );
        mutations.push(changed);
        for field in 0..6 {
            let mut changed = original.clone();
            if let ScalarMirTerminator::AssertOverflowAdd {
                condition,
                expected,
                target,
                unwind,
                left,
                right,
            } = &mut changed.blocks[0].terminator
            {
                match field {
                    0 => *condition = ScalarMirOperand::Copy(ScalarMirPlace::PairFlag(3)),
                    1 => *expected = true,
                    2 => *target = 0,
                    3 => *unwind = ScalarMirUnwind::Terminate,
                    4 => *left = ScalarMirOperand::Copy(ScalarMirPlace::Local(1)),
                    _ => *right = ScalarMirOperand::Constant(ScalarValue::U16(2)),
                }
            }
            mutations.push(changed);
        }
        for (index, changed) in mutations.into_iter().enumerate() {
            let mut env = base.clone();
            install(&mut env, fixed_definitions(&changed, &successor_after()).unwrap()).unwrap();
            let error = install(&mut env, body_bindings().unwrap()).unwrap_err();
            assert!(error.contains("beforeBinding kernel proof"), "mutation {index}: {error}");
        }
        for index in 0..3 {
            let mut changed_after = successor_after();
            match index {
                0 => changed_after.blocks[0].terminator = ScalarMirTerminator::Goto(0),
                1 => {
                    changed_after.blocks[1].statements[0] = ScalarMirStatement::Assign(
                        0,
                        ScalarMirRvalue::Use(
                            ScalarMirOperand::Copy(ScalarMirPlace::PairFlag(3)),
                            ScalarMirRetag::Yes,
                        ),
                    )
                }
                _ => {
                    changed_after.blocks[1].statements[0] = ScalarMirStatement::Assign(
                        0,
                        ScalarMirRvalue::Use(
                            ScalarMirOperand::Move(ScalarMirPlace::PairValue(3)),
                            ScalarMirRetag::Yes,
                        ),
                    )
                }
            }
            let mut env = base.clone();
            install(&mut env, fixed_definitions(&original, &changed_after).unwrap()).unwrap();
            assert!(
                install(&mut env, body_bindings().unwrap())
                    .unwrap_err()
                    .contains("afterBinding kernel proof")
            );
        }
    });
}

#[test]
fn public_bridge_cannot_skip_body_binding_for_unobserved_abi_or_unwind() {
    let mut abi = successor_before();
    abi.abi = ScalarMirAbi::Unsupported;
    let error = prove_successor_bridge(&abi, &successor_after()).err().expect("wrong ABI refused");
    assert!(error.contains("beforeBinding kernel proof"), "{error}");
    let mut unwind = successor_before();
    if let ScalarMirTerminator::AssertOverflowAdd { unwind, .. } = &mut unwind.blocks[0].terminator
    {
        *unwind = ScalarMirUnwind::Unreachable;
    }
    let error =
        prove_successor_bridge(&unwind, &successor_after()).err().expect("wrong unwind refused");
    assert!(error.contains("beforeBinding kernel proof"), "{error}");
}

#[test]
fn actual_traces_move_marker_full_frame_and_fuel_are_part_of_the_kernel_goal() {
    large(|| {
        let mut env = model::environment().unwrap();
        install(&mut env, fixed_definitions(&successor_before(), &successor_after()).unwrap())
            .unwrap();
        let input = app("UInt8.ofNat", [n(255)]);
        for (raw_fuel, scalar_fuel) in [(4, 7), (5, 6)] {
            assert!(
                check_eq(
                    &env,
                    "RMBridgeObservation",
                    actual(input.clone(), raw_fuel, scalar_fuel),
                    expected(input.clone())
                )
                .is_err()
            );
        }
        check_eq(&env, "RMBridgeObservation", actual(input.clone(), 6, 8), expected(input.clone()))
            .unwrap();
        // This has the same numeric return and raw frame but the wrong trace
        // and consumed-field marker: no projection may erase those differences.
        assert!(
            check_eq(
                &env,
                "RMObservation",
                raw_observe(&successor_before(), 255, 5),
                raw_expected(input.clone(), false)
            )
            .is_err()
        );
        let wrong_frame = frame(vec![
            (ScalarType::U16, Some(value_term(ScalarValue::U16(256)))),
            (ScalarType::U8, Some(value_term(ScalarValue::U8(255)))),
            (ScalarType::U16, Some(value_term(ScalarValue::U16(0)))),
            (ScalarType::CheckedU16, Some(value_term(ScalarValue::CheckedU16(256, false)))),
        ]);
        let wrong = app(
            "RMObservation.mk",
            [
                app("RMOutcome.returned", [value_term(ScalarValue::U16(256))]),
                wrong_frame,
                c("RMPlaces.nil"),
                raw_trace(false),
            ],
        );
        assert!(
            check_eq(&env, "RMObservation", raw_observe(&successor_after(), 255, 5), wrong)
                .is_err()
        );
        // Change executable addition while keeping the canonical expectation.
        let mut changed = successor_before();
        changed.blocks[0].statements[1] = ScalarMirStatement::Assign(
            3,
            ScalarMirRvalue::CheckedAdd(
                ScalarMirOperand::Copy(ScalarMirPlace::Local(2)),
                ScalarMirOperand::Constant(ScalarValue::U16(2)),
            ),
        );
        assert!(
            check_eq(
                &env,
                "RMObservation",
                raw_observe(&changed, 255, 5),
                raw_expected(input, true)
            )
            .is_err()
        );
    });
}

#[test]
fn partial_pair_move_preserves_other_field_but_forbids_reread_and_whole_load() {
    large(|| {
        let env = model::environment().unwrap();
        let frame = frame(vec![(
            ScalarType::CheckedU16,
            Some(value_term(ScalarValue::CheckedU16(256, false))),
        )]);
        let flag = place_term(&ScalarMirPlace::PairFlag(0));
        let moves = app("RMPlaces.cons", [flag.clone(), c("RMPlaces.nil")]);
        let moved = app(
            "rm_operand",
            [frame.clone(), c("RMPlaces.nil"), app("RMOperand.move", [flag.clone()])],
        );
        check_eq(
            &env,
            "RMRead",
            moved,
            app("RMRead.value", [value_term(ScalarValue::Bool(false)), moves.clone()]),
        )
        .unwrap();
        for place in [ScalarMirPlace::PairFlag(0), ScalarMirPlace::Local(0)] {
            let read = app(
                "rm_operand",
                [frame.clone(), moves.clone(), app("RMOperand.copy", [place_term(&place)])],
            );
            check_eq(
                &env,
                "RMRead",
                read,
                app("RMRead.fault", [c("RMFailure.moved"), moves.clone()]),
            )
            .unwrap();
        }
        let read_other = app(
            "rm_operand",
            [
                frame,
                moves.clone(),
                app("RMOperand.copy", [place_term(&ScalarMirPlace::PairValue(0))]),
            ],
        );
        check_eq(
            &env,
            "RMRead",
            read_other,
            app("RMRead.value", [value_term(ScalarValue::U16(256)), moves.clone()]),
        )
        .unwrap();
        check_eq(&env, "RMPlaces", app("rm_forget_local", [moves, n(0)]), c("RMPlaces.nil"))
            .unwrap();
        // A failed load does not consume the place; validity and initialization
        // are distinct from the conservative successful-move access marker.
        let bad = app(
            "rm_operand",
            [
                initial_frame(1),
                c("RMPlaces.nil"),
                app("RMOperand.move", [place_term(&ScalarMirPlace::Local(0))]),
            ],
        );
        check_eq(
            &env,
            "RMRead",
            bad,
            app(
                "RMRead.fault",
                [app("RMFailure.scalar", [c("SMFault.uninitialized")]), c("RMPlaces.nil")],
            ),
        )
        .unwrap();
    });
}

#[test]
fn unsupported_storage_cleanup_and_bad_local_remain_explicit_faults() {
    large(|| {
        let env = model::environment().unwrap();
        for (statement, tag) in
            [(ScalarMirStatement::StorageLive(2), 4), (ScalarMirStatement::StorageDead(2), 5)]
        {
            let mut body = successor_before();
            body.blocks[0].statements.insert(0, statement);
            let expected = app(
                "RMObservation.mk",
                [
                    app("RMOutcome.fault", [c("RMFailure.managedStorage")]),
                    initial_frame(1),
                    c("RMPlaces.nil"),
                    app("RMTrace.cons", [n(0), n(0), n(tag), c("RMTrace.nil")]),
                ],
            );
            check_eq(&env, "RMObservation", raw_observe(&body, 1, 1), expected).unwrap();
        }
        let mut body = successor_before();
        body.blocks[0].cleanup = true;
        let expected = app(
            "RMObservation.mk",
            [
                app("RMOutcome.fault", [c("RMFailure.cleanup")]),
                initial_frame(1),
                c("RMPlaces.nil"),
                c("RMTrace.nil"),
            ],
        );
        check_eq(&env, "RMObservation", raw_observe(&body, 1, 1), expected).unwrap();
        let read = app(
            "rm_operand",
            [
                initial_frame(1),
                c("RMPlaces.nil"),
                app("RMOperand.copy", [place_term(&ScalarMirPlace::Local(99))]),
            ],
        );
        check_eq(
            &env,
            "RMRead",
            read,
            app(
                "RMRead.fault",
                [app("RMFailure.scalar", [c("SMFault.badLocal")]), c("RMPlaces.nil")],
            ),
        )
        .unwrap();
    });
}

#[test]
fn real_overflow_preserves_explicit_unwind_and_does_not_execute_return() {
    large(|| {
        let env = model::environment().unwrap();
        let mut body = successor_before();
        body.blocks[0].statements[1] = ScalarMirStatement::Assign(
            3,
            ScalarMirRvalue::CheckedAdd(
                ScalarMirOperand::Copy(ScalarMirPlace::Local(2)),
                ScalarMirOperand::Constant(ScalarValue::U16(65535)),
            ),
        );
        if let ScalarMirTerminator::AssertOverflowAdd { right, .. } = &mut body.blocks[0].terminator
        {
            *right = ScalarMirOperand::Constant(ScalarValue::U16(65535));
        }
        let frame = frame(vec![
            (ScalarType::U16, None),
            (ScalarType::U8, Some(value_term(ScalarValue::U8(255)))),
            (ScalarType::U16, Some(value_term(ScalarValue::U16(255)))),
            (ScalarType::CheckedU16, Some(value_term(ScalarValue::CheckedU16(254, true)))),
        ]);
        let moves =
            app("RMPlaces.cons", [place_term(&ScalarMirPlace::PairFlag(3)), c("RMPlaces.nil")]);
        let trace = [(0, 0, 0), (0, 1, 0), (0, 2, 3)]
            .into_iter()
            .fold(c("RMTrace.nil"), |rest, (bb, pc, tag)| {
                app("RMTrace.cons", [n(bb), n(pc), n(tag), rest])
            });
        let expected = app(
            "RMObservation.mk",
            [
                app("RMOutcome.unwind", [c("RMUnwind.continue")]),
                frame.clone(),
                moves.clone(),
                trace.clone(),
            ],
        );
        check_eq(&env, "RMObservation", raw_observe(&body, 255, 5), expected.clone()).unwrap();
        if let ScalarMirTerminator::AssertOverflowAdd { unwind, .. } =
            &mut body.blocks[0].terminator
        {
            *unwind = ScalarMirUnwind::Terminate;
        }
        assert!(check_eq(&env, "RMObservation", raw_observe(&body, 255, 5), expected).is_err());
        let terminate = app(
            "RMObservation.mk",
            [app("RMOutcome.unwind", [c("RMUnwind.terminate")]), frame, moves, trace],
        );
        check_eq(&env, "RMObservation", raw_observe(&body, 255, 5), terminate).unwrap();
    });
}

#[test]
fn retained_proof_closure_refuses_missing_reordered_forged_and_oversized_terms() {
    let make = || ScalarMirBridgeCertificate {
        family: ScalarMirSuccessorFamily::CopyFixture,
        before: successor_before(),
        after: successor_after(),
        terms: declarations(&successor_before(), &successor_after())
            .unwrap()
            .into_iter()
            .map(|d| serialize_term(&d.value).unwrap())
            .collect(),
    };
    for index in [0, 5, 6, 8, 130, COUNT - 1] {
        let mut certificate = make();
        certificate.terms.remove(index);
        assert!(certificate.replay().unwrap_err().contains("missing terms"));
    }
    let mut reordered = make();
    reordered.terms.swap(9, 10);
    assert!(reordered.replay().unwrap_err().contains("fixed proof closure mismatch"));
    let mut forged = make();
    *forged.terms.last_mut().unwrap() = serialize_term(&c("True.intro")).unwrap();
    assert!(forged.replay().unwrap_err().contains("fixed proof closure mismatch"));
    let mut trailing = make();
    trailing.terms[8].push(0);
    assert!(trailing.replay().unwrap_err().contains("fixed proof closure mismatch"));
    let mut oversized = make();
    oversized.terms[0] = vec![0; 512 * 1024 + 1];
    assert!(oversized.replay().unwrap_err().contains("exceeds limits"));
    let mut changed = make();
    changed.before.argument_count = 2;
    assert!(changed.replay().unwrap_err().contains("fixed proof closure mismatch"));
}

#[test]
fn typechecking_axiom_debt_cannot_be_registered_as_a_bridge_lemma() {
    large(|| {
        let mut env = model::environment().unwrap();
        install(&mut env, fixed_definitions(&successor_before(), &successor_after()).unwrap())
            .unwrap();
        let original = body_bindings().unwrap().remove(0);
        let inhabited =
            poly("Nonempty.intro", Level::zero(), [original.ty.clone(), original.value]);
        let value = poly("Classical.choice", Level::zero(), [original.ty.clone(), inhabited]);
        TypeChecker::new(&env).check_type(&value, &original.ty).unwrap();
        let declaration = theorem("MirBridge.axiomControl", original.ty, value);
        let bytes = serialize_term(&declaration.value).unwrap();
        assert!(register(&mut env, &declaration, &bytes).unwrap_err().contains("axiom debt"));
    });
}

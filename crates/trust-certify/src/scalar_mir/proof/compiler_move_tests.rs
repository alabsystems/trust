use super::*;

fn install(env: &mut Environment, rows: Vec<Decl>) -> Result<(), String> {
    for row in rows {
        register(env, &row, &serialize_term(&row.value).unwrap())?;
    }
    Ok(())
}

#[test]
fn actual_compiler_move_family_universal_closure_checks_and_replays() {
    let family = ScalarMirSuccessorFamily::CompilerMove;
    let mut certificate =
        prove_successor_bridge_for_family(family, &family.before(), &family.after()).unwrap();
    assert_eq!(certificate.family(), family);
    assert_eq!(certificate.local_declarations(), COUNT);
    certificate.replay().unwrap();
    // Same retained terms cannot be reinterpreted as the Copy fixture family.
    certificate.family = ScalarMirSuccessorFamily::CopyFixture;
    assert!(certificate.replay().unwrap_err().contains("fixed proof closure mismatch"));
}

#[test]
fn compiler_move_exact_body_bindings_refuse_mixed_families_and_diagnostic_changes() {
    crate::checker_core::run_on_large_stack(|| {
        let family = ScalarMirSuccessorFamily::CompilerMove;
        let mut changed_diagnostic = family.before();
        if let ScalarMirTerminator::AssertOverflowAdd { left, .. } =
            &mut changed_diagnostic.blocks[0].terminator
        {
            *left = ScalarMirOperand::Copy(ScalarMirPlace::Local(2));
        }
        for (before, after, binding) in [
            (successor_before(), family.after(), "beforeBinding kernel proof"),
            (family.before(), successor_after(), "afterBinding kernel proof"),
            (changed_diagnostic, family.after(), "beforeBinding kernel proof"),
        ] {
            let mut env = model::environment().unwrap();
            install(&mut env, fixed_definitions_for_family(family, &before, &after).unwrap())
                .unwrap();
            let error = install(&mut env, body_bindings_for_family(family).unwrap()).unwrap_err();
            assert!(error.contains(binding), "{error}");
        }
    })
    .expect("compiler model mixed-family worker");
    let family = ScalarMirSuccessorFamily::CompilerMove;
    assert!(prove_successor_bridge(&family.before(), &family.after()).is_err());
    assert!(
        prove_successor_bridge_for_family(family, &successor_before(), &successor_after()).is_err()
    );
}

#[test]
fn compiler_move_observation_retains_return_consumption_not_diagnostic_execution() {
    crate::checker_core::run_on_large_stack(|| {
        let family = ScalarMirSuccessorFamily::CompilerMove;
        let mut env = model::environment().unwrap();
        install(
            &mut env,
            fixed_definitions_for_family(family, &family.before(), &family.after()).unwrap(),
        )
        .unwrap();
        for value in [0, 255] {
            let input = app("UInt8.ofNat", [n(value)]);
            TypeChecker::new(&env)
                .check_type(&refl_expected(input.clone()), &proposition(input.clone()))
                .unwrap();
            // Numeric values coincide, but the full Copy-family observation
            // omits the actual return Move and cannot prove this proposition.
            let copy_observation = expected(input.clone());
            assert!(
                TypeChecker::new(&env)
                    .check_type(
                        &refl(c("RMBridgeObservation"), copy_observation.clone()),
                        &eq(c("RMBridgeObservation"), actual(input, 5, 7), copy_observation),
                    )
                    .is_err()
            );
        }
    })
    .expect("compiler move observation worker");
}

#[test]
fn compiler_move_replay_refuses_body_changes_even_with_reencoded_definitions() {
    let family = ScalarMirSuccessorFamily::CompilerMove;
    let before = family.before();
    let after = family.after();
    let terms: Vec<_> = declarations_for_family(family, &before, &after)
        .unwrap()
        .into_iter()
        .map(|row| serialize_term(&row.value).unwrap())
        .collect();
    for index in [0, 1] {
        let mut certificate = ScalarMirBridgeCertificate {
            family,
            before: before.clone(),
            after: after.clone(),
            terms: terms.clone(),
        };
        if index == 0 {
            certificate.before = successor_before();
        } else {
            certificate.after = successor_after();
        }
        assert!(certificate.replay().unwrap_err().contains("fixed proof closure mismatch"));
        certificate.terms[index] = serialize_term(
            &body_term(if index == 0 { &certificate.before } else { &certificate.after }).unwrap(),
        )
        .unwrap();
        let error = certificate.replay().unwrap_err();
        assert!(
            error.contains(if index == 0 {
                "beforeBinding kernel proof"
            } else {
                "afterBinding kernel proof"
            }),
            "{error}"
        );
    }
}

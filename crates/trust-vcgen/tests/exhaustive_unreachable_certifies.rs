// END-TO-END for the exhaustive-enum `otherwise -> unreachable` trap: build the
// `SwitchInt` the `?`/`Try` desugar produces, run the REAL `generate_vcs`, and
// require that the compiler's structural decider and the clean-CIC certificate
// producer agree on every case.
//
// This is the a3d gate's `[unreach] ... (structural-propositional-unsat, 0ms)`
// row end to end. `promote_structurally_dead_unreachable` labels the obligation
// `Proved` off `formula_is_propositionally_unsat`, but attaches no certificate,
// so `certify_all` mints no exact authority and the report demotes the row to
// `runtime-checked`. The certificate lane
// (`certify_membership_disjunction_resolution`, trust-certify) closes that; the
// lock-step asserted here is what keeps the certificate from ever being BROADER
// than the decided set.
//
// The function shape mirrors `enum_discriminant_match_function` in
// `crates/trust-vcgen/src/tests.rs`, whose doc-comment records it as "exactly
// what `trust-mir-extract`'s `enum_discriminant_range_preconditions` emits for a
// match on an enum value".
use trust_types::*;
use trust_vcgen::generate_vcs;

/// `covered_tags` are the discriminant values the `SwitchInt` branches on (the
/// match arms); `valid_tags` is the enum's full discriminant set, surfaced as the
/// always-true precondition `discr == t0 OR discr == t1 OR ...`.
fn enum_discriminant_match_function(
    covered_tags: &[u128],
    valid_tags: &[i128],
) -> VerifiableFunction {
    let span = SourceSpan::default();
    let discr = Operand::Move(Place::local(2));

    let arm_blocks: Vec<(u128, BlockId)> =
        covered_tags.iter().enumerate().map(|(i, &tag)| (tag, BlockId(1 + i))).collect();
    let unreachable_block_id = BlockId(1 + covered_tags.len());

    let mut blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![],
        terminator: Terminator::SwitchInt {
            discr,
            targets: arm_blocks.clone(),
            otherwise: unreachable_block_id,
            exhaustive_enum_unreachable: false,
            span: span.clone(),
        },
    }];
    for (_, arm) in &arm_blocks {
        blocks.push(BasicBlock { id: *arm, stmts: vec![], terminator: Terminator::Return });
    }
    blocks.push(BasicBlock {
        id: unreachable_block_id,
        stmts: vec![],
        terminator: Terminator::Unreachable,
    });

    let precondition = Formula::Or(
        valid_tags
            .iter()
            .map(|&t| {
                Formula::Eq(Box::new(Formula::var("_2", Sort::Int)), Box::new(Formula::Int(t)))
            })
            .collect(),
    );

    VerifiableFunction {
        name: "enum_discriminant_match".to_string(),
        def_path: "test::enum_discriminant_match".to_string(),
        span,
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: None },
                LocalDecl { index: 2, ty: Ty::i32(), name: None },
            ],
            blocks,
            arg_count: 1,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![precondition],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn unreachable_vcs(covered: &[u128], valid: &[i128]) -> Vec<VerificationCondition> {
    let func = enum_discriminant_match_function(covered, valid);
    generate_vcs(&func).into_iter().filter(|vc| matches!(vc.kind, VcKind::Unreachable)).collect()
}

/// The `?`-desugar shape: a fully-covered two-variant enum. The `otherwise` arm
/// is dead, and its obligation must now carry a clean-CIC certificate — not just
/// a `Proved` label from the structural recognizer.
#[test]
fn fully_covered_two_variant_trap_certifies() {
    let vcs = unreachable_vcs(&[0, 1], &[0, 1]);
    assert_eq!(vcs.len(), 1, "expected exactly one Unreachable obligation");
    let vc = &vcs[0];
    assert!(
        trust_router::constant_folder::formula_is_propositionally_unsat(&vc.formula),
        "the structural recognizer no longer decides this trap; the certificate lane's \
         premise has moved: {:?}",
        vc.formula
    );
    let Some(evidence) = trust_certify::certify_vc(vc) else {
        panic!("certify_vc declined the dead exhaustive-enum trap: {:?}", vc.formula);
    };
    assert!(
        trust_certify::replay_vc_evidence(vc, &evidence),
        "the VC-bound certificate did not replay"
    );
}

/// NEGATIVE CONTROL, end to end: a three-variant enum with two arms covered. Tag
/// 2 genuinely REACHES the trap — a real `unreachable_unchecked`, real UB — so
/// neither decider may accept it.
#[test]
fn partially_covered_trap_is_reachable_and_is_never_certified() {
    let vcs = unreachable_vcs(&[0, 1], &[0, 1, 2]);
    assert_eq!(vcs.len(), 1, "expected exactly one Unreachable obligation");
    let vc = &vcs[0];
    assert!(
        !trust_router::constant_folder::formula_is_propositionally_unsat(&vc.formula),
        "the structural recognizer decided a REACHABLE trap dead: {:?}",
        vc.formula
    );
    assert!(
        trust_certify::certify_vc(vc).is_none(),
        "a REACHABLE `unreachable` was kernel-certified dead — a false proof of UB: {:?}",
        vc.formula
    );
}

/// LOCK-STEP. Across the covered/valid grid, the compiler's structural
/// propositional-UNSAT decision and the clean-CIC certificate producer must agree
/// exactly. A `true`/`false` split in either direction is a finding: certifying
/// more than is decided would mean the certificate lane invented authority; and a
/// decided-but-uncertified row is exactly the gap this work closes.
/// REACHABILITY GUARD for `VcKind::has_runtime_fallback`. `unreachable_vcs`
/// runs the REAL `generate_vcs` over a real `SwitchInt`-with-`otherwise ->
/// Terminator::Unreachable` body, so the VC below is minted by the production
/// path at `v2_build_terminator_vc`'s bare-`Terminator::Unreachable` arm — the
/// one rustc lowers to `llvm.unreachable` with no trap emitted. Claiming a
/// runtime fallback for it asserts a monitor that does not exist, and
/// `classify_runtime_disposition` would then downgrade an unproved row from
/// `Unknown` to `RuntimeChecked`. Both covered and partially-covered shapes are
/// checked: the answer may not depend on whether the trap is provably dead.
#[test]
fn production_minted_unreachable_claims_no_runtime_fallback() {
    let grid: &[(&[u128], &[i128])] = &[(&[0, 1], &[0, 1]), (&[0, 1], &[0, 1, 2])];
    for (covered, valid) in grid {
        let vcs = unreachable_vcs(covered, valid);
        assert_eq!(vcs.len(), 1, "expected exactly one Unreachable obligation");
        for overflow_checks in [true, false] {
            assert!(
                !vcs[0].kind.has_runtime_fallback(overflow_checks),
                "a bare `Terminator::Unreachable` obligation claimed a runtime fallback \
                 (covered={covered:?} valid={valid:?} overflow_checks={overflow_checks}) — \
                 rustc emits no check for it, so this is a false safety claim"
            );
        }
    }
}

#[test]
fn certification_and_structural_decision_lock_step() {
    let grid: &[(&[u128], &[i128])] = &[
        (&[0, 1], &[0, 1]),
        (&[0, 1, 2], &[0, 1, 2]),
        (&[0], &[0]),
        (&[0, 1], &[0, 1, 2]),
        (&[0], &[0, 1]),
        (&[0, 2], &[0, 1, 2]),
    ];
    for (covered, valid) in grid {
        for vc in unreachable_vcs(covered, valid) {
            let structural =
                trust_router::constant_folder::formula_is_propositionally_unsat(&vc.formula);
            let certified = trust_certify::certify_vc(&vc).is_some();
            assert_eq!(
                structural, certified,
                "covered={covered:?} valid={valid:?}: structural says {structural}, \
                 certification says {certified} — {:?}",
                vc.formula
            );
        }
    }
}

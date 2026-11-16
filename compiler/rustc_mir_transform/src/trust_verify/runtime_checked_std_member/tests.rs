use super::*;

const NOT_DISPATCHED: StopCause = StopCause::NotDispatched;

fn member(def_path: &str, class: MemberAssertRefusalClass) -> RuntimeCheckedStdMember {
    RuntimeCheckedStdMember {
        def_path: def_path.to_string(),
        class,
        reason: "member Assert kind `Overflow(Add)` is outside the exact Div/Rem/BoundsCheck lane",
    }
}

fn proved_row() -> TransportObligationResult {
    let mut row = super::super::transport_no_obligations_row();
    row.kind = "assertion".to_string();
    row.reason = None;
    row
}

#[test]
fn a_member_row_is_runtime_checked_evidence_free_and_names_the_member() {
    let members = [member(
        "<usize as core::iter::traits::accum::Sum>::sum::{closure#0}",
        MemberAssertRefusalClass::AssertKindOutsideLane,
    )];
    let rows = rows_with_members(&[proved_row()], None, &members, NOT_DISPATCHED)
        .expect("a member is owed a row");
    assert_eq!(rows.len(), 2, "the verifier's own row is kept; the member row is appended");
    let row = &rows[1];
    assert_eq!(row.outcome, Outcome::RuntimeChecked);
    assert_eq!(row.solver, STD_MEMBER_RUNTIME_CHECK_ROW_SOLVER);
    let reason = row.reason.as_deref().expect("the row states why");
    assert!(reason.starts_with(STD_MEMBER_RUNTIME_CHECK_REASON), "{reason}");
    assert!(row.proof_evidence.is_none() && row.native_trust_ir.is_none());
    assert!(row.counterexample.is_none() && row.obligation_id.is_none());
    assert!(!row.design_mandate);
    assert!(
        row.description.contains("<usize as core::iter::traits::accum::Sum>::sum::{closure#0}")
    );
    assert!(!row.outcome.is_proved());
}

#[test]
fn one_row_per_member_and_nothing_for_none() {
    let members = [
        member("core::a", MemberAssertRefusalClass::AssertKindOutsideLane),
        member("core::b", MemberAssertRefusalClass::GuardedOrNonEntryPrefix),
    ];
    let rows = rows_with_members(&[], None, &members, NOT_DISPATCHED).unwrap();
    assert_eq!(rows.len(), 2);
    assert!(rows.iter().all(|row| row.outcome == Outcome::RuntimeChecked));
    assert!(rows_with_members(&[proved_row()], None, &[], NOT_DISPATCHED).is_none());
}

/// Only this seam mints the row: a pre-existing row claiming its reason is
/// stripped, with or without members owed.
#[test]
fn a_forged_member_row_is_stripped() {
    let mut forged = proved_row();
    forged.reason = Some(STD_MEMBER_RUNTIME_CHECK_REASON.to_string());
    forged.outcome = Outcome::Proved;
    let rows = rows_with_members(&[forged.clone(), proved_row()], None, &[], NOT_DISPATCHED)
        .expect("a forged row must be stripped even with no member");
    assert_eq!(rows, vec![proved_row()]);
    let members = [member("core::a", MemberAssertRefusalClass::AssertKindOutsideLane)];
    let rows = rows_with_members(&[forged], None, &members, NOT_DISPATCHED).expect("owed a row");
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].outcome, Outcome::RuntimeChecked);
}

/// C3 (D9 critique H3's precedent): the zero-obligation branch never mints the
/// proved `no_obligations` row beside a member row, and never drops the gap row.
#[test]
fn the_zero_obligation_branch_never_mints_no_obligations_beside_a_member_row() {
    let members = [member("core::a", MemberAssertRefusalClass::AssertKindOutsideLane)];
    let clean = zero_obligation_rows_with_members(true, &[], None, &members, NOT_DISPATCHED);
    assert_eq!(clean.len(), 1);
    assert_eq!(clean[0].outcome, Outcome::RuntimeChecked);
    assert!(clean.iter().all(|row| row.kind != "no_obligations"));
    let unclean = zero_obligation_rows_with_members(false, &[], None, &members, NOT_DISPATCHED);
    assert_eq!(unclean.len(), 2);
    assert_eq!(unclean[0].kind, super::super::NATIVE_VERIFICATION_GAP_ROW_KIND);
    assert_eq!(unclean[1].outcome, Outcome::RuntimeChecked);
    let with_rows =
        zero_obligation_rows_with_members(true, &[proved_row()], None, &members, NOT_DISPATCHED);
    assert_eq!(with_rows.len(), 2);
    assert_eq!(with_rows[1].outcome, Outcome::RuntimeChecked);
}

/// RUNTIME-CHECKED-NO-STOP-CAUSE-1: the row states its stop, so a unit whose
/// other rows are clean reads it as the stop it is (`not-dispatched` is
/// reproducible), never as `unclassified`; a deadline-declined run's row reads
/// as the clock stop it is. Both arms, so a constant cannot pass.
#[test]
fn a_member_row_states_the_stop_it_is_given() {
    use trust_types::determinism::Reproducibility;
    let members = [member("core::a", MemberAssertRefusalClass::AssertKindOutsideLane)];
    for (stop, reproducible) in [
        (StopCause::NotDispatched, Reproducibility::Deterministic),
        (StopCause::WallBackstop, Reproducibility::NotReproducible),
    ] {
        let rows = rows_with_members(&[], None, &members, stop).unwrap();
        let reason = rows[0].reason.as_deref().unwrap();
        assert!(reason.starts_with(STD_MEMBER_RUNTIME_CHECK_REASON), "{reason}");
        assert_eq!(StopCause::from_reason(reason), Some(stop), "{reason}");
        let read = StopCause::of_outcome(rows[0].outcome, Some(reason));
        assert_eq!(read, stop);
        assert_eq!(read.reproducibility(), reproducible);
        let zero = zero_obligation_rows_with_members(true, &[], None, &members, stop);
        assert_eq!(StopCause::from_reason(zero[0].reason.as_deref().unwrap()), Some(stop));
    }
}

/// A row claims the kind by the solver label or by a reason that begins with the
/// row's reason, whatever follows it: today's bare reason, a stamped one, one
/// with a different token, a suffixed one, and a label with any reason are all
/// stripped. A row that only quotes the reason later in its own is not this
/// seam's and survives.
#[test]
fn every_claim_of_the_kind_is_stripped_and_nothing_else() {
    let claim = |solver: &str, reason: String| {
        let mut row = proved_row();
        row.solver = solver.to_string();
        row.reason = Some(reason);
        row
    };
    let forgeries = [
        claim("ay", STD_MEMBER_RUNTIME_CHECK_REASON.to_string()),
        claim("ay", StopCause::NotDispatched.stamp(STD_MEMBER_RUNTIME_CHECK_REASON)),
        claim("ay", StopCause::Solved.stamp(STD_MEMBER_RUNTIME_CHECK_REASON)),
        claim("ay", format!("{STD_MEMBER_RUNTIME_CHECK_REASON}; and it proved")),
        claim(STD_MEMBER_RUNTIME_CHECK_ROW_SOLVER, "proved by the member".to_string()),
    ];
    let quoting = claim("ay", format!("a note: {STD_MEMBER_RUNTIME_CHECK_REASON}"));
    for forged in &forgeries {
        assert!(claims_std_member_runtime_check(forged), "{forged:?}");
        let rows = rows_with_members(&[forged.clone(), proved_row()], None, &[], NOT_DISPATCHED)
            .expect("a claim is stripped with no member owed");
        assert_eq!(rows, vec![proved_row()]);
    }
    assert!(!claims_std_member_runtime_check(&quoting));
    assert!(!claims_std_member_runtime_check(&proved_row()));
    assert!(rows_with_members(&[quoting, proved_row()], None, &[], NOT_DISPATCHED).is_none());
}

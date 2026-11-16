use super::*;

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
    let rows = rows_with_runtime_checked_std_members(&[proved_row()], None, &members)
        .expect("a member is owed a row");
    assert_eq!(rows.len(), 2, "the verifier's own row is kept; the member row is appended");
    let row = &rows[1];
    assert_eq!(row.outcome, Outcome::RuntimeChecked);
    assert_eq!(row.solver, STD_MEMBER_RUNTIME_CHECK_ROW_SOLVER);
    assert_eq!(row.reason.as_deref(), Some(STD_MEMBER_RUNTIME_CHECK_REASON));
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
    let rows = rows_with_runtime_checked_std_members(&[], None, &members).unwrap();
    assert_eq!(rows.len(), 2);
    assert!(rows.iter().all(|row| row.outcome == Outcome::RuntimeChecked));
    assert!(rows_with_runtime_checked_std_members(&[proved_row()], None, &[]).is_none());
}

/// Only this seam mints the row: a pre-existing row claiming its reason is
/// stripped, with or without members owed.
#[test]
fn a_forged_member_row_is_stripped() {
    let mut forged = proved_row();
    forged.reason = Some(STD_MEMBER_RUNTIME_CHECK_REASON.to_string());
    forged.outcome = Outcome::Proved;
    let rows = rows_with_runtime_checked_std_members(&[forged.clone(), proved_row()], None, &[])
        .expect("a forged row must be stripped even with no member");
    assert_eq!(rows, vec![proved_row()]);
    let members = [member("core::a", MemberAssertRefusalClass::AssertKindOutsideLane)];
    let rows =
        rows_with_runtime_checked_std_members(&[forged], None, &members).expect("owed a row");
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].outcome, Outcome::RuntimeChecked);
}

/// C3 (D9 critique H3's precedent): the zero-obligation branch never mints the
/// proved `no_obligations` row beside a member row, and never drops the gap row.
#[test]
fn the_zero_obligation_branch_never_mints_no_obligations_beside_a_member_row() {
    let members = [member("core::a", MemberAssertRefusalClass::AssertKindOutsideLane)];
    let clean = zero_obligation_rows(true, &[], None, &members);
    assert_eq!(clean.len(), 1);
    assert_eq!(clean[0].outcome, Outcome::RuntimeChecked);
    assert!(clean.iter().all(|row| row.kind != "no_obligations"));
    let unclean = zero_obligation_rows(false, &[], None, &members);
    assert_eq!(unclean.len(), 2);
    assert_eq!(unclean[0].kind, super::super::NATIVE_VERIFICATION_GAP_ROW_KIND);
    assert_eq!(unclean[1].outcome, Outcome::RuntimeChecked);
    let with_rows = zero_obligation_rows(true, &[proved_row()], None, &members);
    assert_eq!(with_rows.len(), 2);
    assert_eq!(with_rows[1].outcome, Outcome::RuntimeChecked);
}

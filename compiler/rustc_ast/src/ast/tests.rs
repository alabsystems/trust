//! The seven contract-clause lanes are stored in separate vectors, so the
//! authored order survives only in the marker table. These cases pin the
//! reconstruction, including the equal-span case where nothing else can
//! disambiguate the lanes.

use rustc_span::{BytePos, DUMMY_SP, Span};

use super::*;

fn marker(
    ordinal: u32,
    kind: FnContractClauseKind,
    lane: FnContractClauseLane,
    lane_index: u32,
) -> FnContractClauseMarker {
    FnContractClauseMarker { ordinal, kind, lane, lane_index }
}

fn native(span: Span) -> TrustNativeClause {
    TrustNativeClause { predicate: span, payload: rustc_span::sym::dummy, citation: None }
}

#[test]
fn restores_all_seven_interleaved_lanes_with_equal_spans() {
    use FnContractClauseKind::{Decreases, Ensures, Requires};
    use FnContractClauseLane::{Native, Opaque, Typed};

    let expected = [
        marker(0, Ensures, Opaque, 0),
        marker(1, Requires, Typed, 0),
        marker(2, Ensures, Native, 0),
        marker(3, Requires, Opaque, 0),
        marker(4, Ensures, Typed, 0),
        marker(5, Decreases, Native, 0),
        marker(6, Requires, Native, 0),
    ];
    let mut contract = FnContract::default();
    contract.requires_clauses.push(Box::new(Expr::dummy()));
    contract.trust_opaque_requires.push(DUMMY_SP);
    contract.trust_native_requires.push(native(DUMMY_SP));
    contract.ensures_clauses.push(Box::new(Expr::dummy()));
    contract.trust_opaque_ensures.push(DUMMY_SP);
    contract.trust_native_ensures.push(native(DUMMY_SP));
    contract.trust_native_decreases.push(native(DUMMY_SP));
    contract.clause_order.extend(expected);

    let ordered = contract.ordered_clause_refs().unwrap();
    assert_eq!(ordered.iter().map(|clause| clause.marker).collect::<Vec<_>>(), expected);
    for clause in ordered {
        assert!(matches!(
            (clause.marker.lane, clause.clause),
            (Typed, FnContractClauseRef::Typed(_))
                | (Opaque, FnContractClauseRef::Opaque(_))
                | (Native, FnContractClauseRef::Native(_))
        ));
    }
}

#[test]
fn accepts_repeated_lane_indices_and_legacy_singleton() {
    let first = Span::with_root_ctxt(BytePos(10), BytePos(11));
    let second = Span::with_root_ctxt(BytePos(20), BytePos(21));
    let mut native_contract = FnContract::default();
    native_contract.trust_native_requires.push(native(first));
    native_contract.trust_native_requires.push(native(second));
    native_contract.clause_order.push(marker(
        0,
        FnContractClauseKind::Requires,
        FnContractClauseLane::Native,
        0,
    ));
    native_contract.clause_order.push(marker(
        1,
        FnContractClauseKind::Requires,
        FnContractClauseLane::Native,
        1,
    ));
    let ordered = native_contract.ordered_clause_refs().unwrap();
    assert!(
        matches!(ordered[0].clause, FnContractClauseRef::Native(clause) if clause.predicate == first)
    );
    assert!(
        matches!(ordered[1].clause, FnContractClauseRef::Native(clause) if clause.predicate == second)
    );

    let mut legacy =
        FnContract { requires: Some(Box::new(Expr::dummy())), ..FnContract::default() };
    legacy.clause_order.push(marker(
        0,
        FnContractClauseKind::Requires,
        FnContractClauseLane::Typed,
        0,
    ));
    assert!(matches!(
        legacy.ordered_clause_refs().unwrap().as_slice(),
        [OrderedFnContractClauseRef { clause: FnContractClauseRef::Typed(_), .. }]
    ));
}

#[test]
fn rejects_ambiguous_non_dense_missing_and_unmarked_metadata() {
    use FnContractClauseKind::Requires;
    use FnContractClauseLane::Typed;

    let mut ambiguous =
        FnContract { requires: Some(Box::new(Expr::dummy())), ..FnContract::default() };
    ambiguous.requires_clauses.push(Box::new(Expr::dummy()));
    assert_eq!(
        ambiguous.ordered_clause_refs().unwrap_err(),
        FnContractClauseOrderError::AmbiguousLegacyTypedLane(Requires)
    );

    let mut invalid_lane = FnContract::default();
    invalid_lane.clause_order.push(marker(
        0,
        FnContractClauseKind::Decreases,
        FnContractClauseLane::Typed,
        0,
    ));
    assert_eq!(
        invalid_lane.ordered_clause_refs().unwrap_err(),
        FnContractClauseOrderError::InvalidLane {
            kind: FnContractClauseKind::Decreases,
            lane: FnContractClauseLane::Typed,
        }
    );

    let mut non_dense_ordinal = FnContract::default();
    non_dense_ordinal.requires_clauses.push(Box::new(Expr::dummy()));
    non_dense_ordinal.clause_order.push(marker(1, Requires, Typed, 0));
    assert_eq!(
        non_dense_ordinal.ordered_clause_refs().unwrap_err(),
        FnContractClauseOrderError::NonDenseOrdinal { position: 0, ordinal: 1 }
    );

    let mut skipped = FnContract::default();
    skipped.requires_clauses.push(Box::new(Expr::dummy()));
    skipped.clause_order.push(marker(0, Requires, Typed, 1));
    assert_eq!(
        skipped.ordered_clause_refs().unwrap_err(),
        FnContractClauseOrderError::NonDenseLaneIndex {
            kind: Requires,
            lane: Typed,
            expected: 0,
            lane_index: 1,
        }
    );

    let mut duplicate = FnContract::default();
    duplicate.requires_clauses.push(Box::new(Expr::dummy()));
    duplicate.requires_clauses.push(Box::new(Expr::dummy()));
    duplicate.clause_order.push(marker(0, Requires, Typed, 0));
    duplicate.clause_order.push(marker(1, Requires, Typed, 0));
    assert_eq!(
        duplicate.ordered_clause_refs().unwrap_err(),
        FnContractClauseOrderError::NonDenseLaneIndex {
            kind: Requires,
            lane: Typed,
            expected: 1,
            lane_index: 0,
        }
    );

    let mut missing = FnContract::default();
    missing.clause_order.push(marker(0, Requires, Typed, 0));
    assert_eq!(
        missing.ordered_clause_refs().unwrap_err(),
        FnContractClauseOrderError::MissingLaneValue {
            kind: Requires,
            lane: Typed,
            lane_index: 0,
        }
    );

    let mut unmarked = FnContract::default();
    unmarked.requires_clauses.push(Box::new(Expr::dummy()));
    assert_eq!(
        unmarked.ordered_clause_refs().unwrap_err(),
        FnContractClauseOrderError::UnmarkedLaneValue {
            kind: Requires,
            lane: Typed,
            marked: 0,
            stored: 1,
        }
    );
}

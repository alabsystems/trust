//! Authored-order restoration for the seven interleaved contract-clause
//! lanes. These assertions need the private ordering helpers, so they live
//! beside `contract.rs` rather than in an integration test.

use rustc_ast::{
    FnContractClauseKind as Kind, FnContractClauseLane as Lane, FnContractClauseMarker,
};
use rustc_span::DUMMY_SP;

use super::{ContractClauseOrderError, restore_contract_clause_authored_order};

#[test]
fn exact_markers_restore_interleaved_clauses_with_identical_spans() {
    let requires_typed = [("requires-typed", DUMMY_SP)];
    let requires_opaque = [("requires-opaque", DUMMY_SP)];
    let requires_native = [("requires-native", DUMMY_SP)];
    let ensures_typed = [("ensures-typed", DUMMY_SP)];
    let ensures_opaque = [("ensures-opaque", DUMMY_SP)];
    let ensures_native = [("ensures-native", DUMMY_SP)];
    let decreases_native = [("decreases-native", DUMMY_SP)];
    let markers = [
        FnContractClauseMarker {
            ordinal: 0,
            kind: Kind::Ensures,
            lane: Lane::Opaque,
            lane_index: 0,
        },
        FnContractClauseMarker {
            ordinal: 1,
            kind: Kind::Requires,
            lane: Lane::Typed,
            lane_index: 0,
        },
        FnContractClauseMarker {
            ordinal: 2,
            kind: Kind::Ensures,
            lane: Lane::Native,
            lane_index: 0,
        },
        FnContractClauseMarker {
            ordinal: 3,
            kind: Kind::Decreases,
            lane: Lane::Native,
            lane_index: 0,
        },
        FnContractClauseMarker {
            ordinal: 4,
            kind: Kind::Requires,
            lane: Lane::Opaque,
            lane_index: 0,
        },
        FnContractClauseMarker {
            ordinal: 5,
            kind: Kind::Ensures,
            lane: Lane::Typed,
            lane_index: 0,
        },
        FnContractClauseMarker {
            ordinal: 6,
            kind: Kind::Requires,
            lane: Lane::Native,
            lane_index: 0,
        },
    ];

    let ordered = restore_contract_clause_authored_order(
        &markers,
        [
            &requires_typed,
            &requires_opaque,
            &requires_native,
            &ensures_typed,
            &ensures_opaque,
            &ensures_native,
            &decreases_native,
        ],
    )
    .unwrap();

    assert_eq!(
        ordered.iter().map(|clause| clause.value.0).collect::<Vec<_>>(),
        [
            "ensures-opaque",
            "requires-typed",
            "ensures-native",
            "decreases-native",
            "requires-opaque",
            "ensures-typed",
            "requires-native",
        ]
    );
    assert!(ordered.iter().all(|clause| clause.value.1 == DUMMY_SP));
}

#[test]
fn inconsistent_marker_stream_is_rejected_without_span_fallback() {
    let requires_typed = ["stored clause"];
    let empty: [&str; 0] = [];
    let lanes = [
        requires_typed.as_slice(),
        empty.as_slice(),
        empty.as_slice(),
        empty.as_slice(),
        empty.as_slice(),
        empty.as_slice(),
        empty.as_slice(),
    ];

    assert_eq!(
        restore_contract_clause_authored_order::<&str>(&[], lanes),
        Err(ContractClauseOrderError::UnmarkedLaneValue {
            kind: Kind::Requires,
            lane: Lane::Typed,
            marked: 0,
            stored: 1,
        })
    );

    let bad_lane_index = [FnContractClauseMarker {
        ordinal: 0,
        kind: Kind::Requires,
        lane: Lane::Typed,
        lane_index: 1,
    }];
    assert_eq!(
        restore_contract_clause_authored_order(&bad_lane_index, lanes),
        Err(ContractClauseOrderError::NonDenseLaneIndex {
            kind: Kind::Requires,
            lane: Lane::Typed,
            expected: 0,
            lane_index: 1,
        })
    );

    let invalid_decreases_lane = [FnContractClauseMarker {
        ordinal: 0,
        kind: Kind::Decreases,
        lane: Lane::Typed,
        lane_index: 0,
    }];
    assert_eq!(
        restore_contract_clause_authored_order(&invalid_decreases_lane, lanes),
        Err(ContractClauseOrderError::InvalidLane {
            kind: Kind::Decreases,
            lane: Lane::Typed,
        })
    );
}

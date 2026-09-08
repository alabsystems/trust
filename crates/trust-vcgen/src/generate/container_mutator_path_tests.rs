// Trust (R20 Front A): the `Vec`/`String` index-panicking container-mutator
// recognizer must key on the RECEIVER type path, never on text that only
// appears inside a TURBOFISH generic-argument group.
//
// Measured defect (ny-cert gate R19, `gateR19-noenv.log`): the callee
// `serde_json::Map::<std::string::String, serde_json::Value>::insert` — a
// TOTAL map insert that returns `Option<Value>` and has no index and no
// char-boundary panic path at all — matched
// `is_index_panicking_container_mutator` because the substring
// `string::String` appears in its FIRST GENERIC ARGUMENT. The resulting
// fail-closed `Call::insert::panic-freedom-unverified` UnsupportedMir row is
// counted FAILED by strict policy, so the over-match rejected valid programs:
// 41 of ny-cert's 92 `unknown` obligations (8 functions) were this one
// mis-recognition and nothing else.
//
// The exact callee spellings pinned below were READ OFF the deployed
// toolchain (driver sha256:df4b9aaa09ca3f96) via
// `-Z trust-dump=ir:<dir>`; they are not guesses.

use super::{
    is_bounds_panicking_slice_mutator, is_index_panicking_container_mutator, method_tail,
    unsupported_mir_vcs,
};
use trust_types::UnwindEdge;
use trust_types::{
    BasicBlock, BlockId, LocalDecl, Operand, Place, SourceSpan, Terminator, Ty, VcKind,
    VerifiableBody, VerifiableFunction,
};

// ---------------------------------------------------------------------------
// Exact spellings observed on the deployed toolchain.
// ---------------------------------------------------------------------------

/// The FALSE POSITIVE: `serde_json::Map<String, Value>::insert`. Total — it
/// returns `Option<Value>`; there is no index argument to be out of range.
const SERDE_JSON_MAP_INSERT: &str =
    "serde_json::Map::<std::string::String, serde_json::Value>::insert";

/// The TRUE POSITIVES — genuinely index-panicking std mutators, exactly as the
/// compiler renders them.
const STRING_INSERT: &str = "std::string::String::insert";
const STRING_INSERT_STR: &str = "std::string::String::insert_str";
const STRING_REMOVE: &str = "std::string::String::remove";
const VEC_INSERT: &str = "std::vec::Vec::<T, A>::insert";
const VEC_REMOVE: &str = "std::vec::Vec::<T, A>::remove";
const VEC_SWAP_REMOVE: &str = "std::vec::Vec::<T, A>::swap_remove";

// ---------------------------------------------------------------------------
// (1) The defect itself.
// ---------------------------------------------------------------------------

/// FAILS on the unfixed recognizer (which returns `true` here). A total
/// map insert must NOT raise the index-panic row.
#[test]
fn serde_json_map_insert_is_not_an_index_panicking_container_mutator() {
    assert_eq!(method_tail(SERDE_JSON_MAP_INSERT), "insert", "tail must be the method, not `>`");
    assert!(
        !is_index_panicking_container_mutator(SERDE_JSON_MAP_INSERT),
        "`{SERDE_JSON_MAP_INSERT}` is a TOTAL map insert; `string::String` occurs only in its \
         generic ARGUMENT, never as the receiver path"
    );
}

/// The same defect with the monomorph tag the compiler appends (lesson: callee
/// names carry a trailing `::<__trust_args@HASH>`).
#[test]
fn serde_json_map_insert_stays_unmatched_with_the_monomorph_tag() {
    let tagged = format!("{SERDE_JSON_MAP_INSERT}::<__trust_args@0123456789abcdef>");
    assert_eq!(method_tail(&tagged), "insert");
    assert!(!is_index_panicking_container_mutator(&tagged));
}

/// The generic-argument channel is closed for the `Vec` spelling too, not just
/// `String` — a third-party container parameterised by `Vec` is still total.
#[test]
fn generic_argument_naming_vec_does_not_match_either() {
    assert!(!is_index_panicking_container_mutator(
        "some_crate::Registry::<std::vec::Vec<u8>, u32>::insert"
    ));
    assert!(!is_index_panicking_container_mutator(
        "some_crate::Registry::<std::vec::Vec<u8>, u32>::remove"
    ));
}

// ---------------------------------------------------------------------------
// (2) ANTI-CONTROLS — the genuinely unsafe siblings must STILL be flagged.
//     If any of these regress, an unguarded `s.insert(i, c)` / `v.remove(i)`
//     would compile clean: a panic-freedom hole, i.e. the exact false proof
//     this recognizer exists to prevent.
// ---------------------------------------------------------------------------

#[test]
fn real_string_and_vec_index_mutators_are_still_flagged() {
    for callee in
        [STRING_INSERT, STRING_INSERT_STR, STRING_REMOVE, VEC_INSERT, VEC_REMOVE, VEC_SWAP_REMOVE]
    {
        assert!(
            is_index_panicking_container_mutator(callee),
            "`{callee}` panics on an out-of-range index and MUST keep its fail-closed row"
        );
    }
}

#[test]
fn real_index_mutators_are_still_flagged_with_the_monomorph_tag() {
    for callee in [STRING_INSERT, VEC_INSERT, VEC_REMOVE, VEC_SWAP_REMOVE] {
        let tagged = format!("{callee}::<__trust_args@fedcba9876543210>");
        assert!(
            is_index_panicking_container_mutator(&tagged),
            "`{tagged}` must keep its fail-closed row under the monomorph tag"
        );
    }
}

/// `alloc::`-prefixed spellings (the other rendering of the same std items).
#[test]
fn alloc_prefixed_index_mutators_are_still_flagged() {
    for callee in [
        "alloc::string::String::insert",
        "alloc::string::String::insert_str",
        "alloc::string::String::remove",
        "alloc::vec::Vec::<T, A>::insert",
        "alloc::vec::Vec::<T, A>::remove",
        "alloc::vec::Vec::<T, A>::swap_remove",
    ] {
        assert!(is_index_panicking_container_mutator(callee), "`{callee}` must stay flagged");
    }
}

/// A QUALIFIED-PATH spelling (`<Recv as Trait>::m`) keeps its receiver OUTSIDE
/// any turbofish, so stripping turbofishes must not blind the recognizer to it.
#[test]
fn qualified_path_receiver_spelling_is_still_flagged() {
    assert!(is_index_panicking_container_mutator("<std::vec::Vec<u8> as SomeExt>::insert"));
    assert!(is_index_panicking_container_mutator("<std::string::String as SomeExt>::remove"));
}

/// The pre-existing TOTAL-method exclusions must survive unchanged: map/set
/// `insert`/`remove` under `collections::` return `Option`/`bool`.
#[test]
fn total_collection_methods_stay_unmatched() {
    for callee in [
        "std::collections::HashMap::<K, V, S>::insert",
        "std::collections::HashMap::<K, V, S>::remove",
        "alloc::collections::btree::map::BTreeMap::<K, V, A>::insert",
        "std::collections::VecDeque::<T, A>::remove",
    ] {
        assert!(!is_index_panicking_container_mutator(callee), "`{callee}` is total");
    }
}

/// Non-mutator tails never reach the path test at all.
#[test]
fn unrelated_method_tails_are_unmatched() {
    for callee in ["std::vec::Vec::<T, A>::push", "std::string::String::len", "my::insertion"] {
        assert!(!is_index_panicking_container_mutator(callee));
    }
}

// ---------------------------------------------------------------------------
// (3) END-TO-END through `unsupported_mir_vcs` — the predicate is not enough:
//     the LANE has to actually fire (and actually stop firing). A fixture that
//     never reaches the code under test proves nothing.
// ---------------------------------------------------------------------------

fn call_only_fn(callee: &str, argc: usize) -> VerifiableFunction {
    let args: Vec<Operand> = (1..=argc).map(|i| Operand::Move(Place::local(i))).collect();
    let locals: Vec<LocalDecl> = (0..=argc + 1)
        .map(|index| LocalDecl { index, ty: Ty::u64(), name: None })
        .collect();
    VerifiableFunction {
        name: "container_mutator_fixture".into(),
        def_path: "test::container_mutator_fixture".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: callee.into(),
                        args,
                        dest: Place::local(argc + 1),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        is_foreign: false,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: argc,
            return_ty: Ty::u64(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn insert_row_count(func: &VerifiableFunction) -> usize {
    unsupported_mir_vcs(func)
        .iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == "Call::insert::panic-freedom-unverified")
        })
        .count()
}

/// THE MUTANT / ANTI-CONTROL: a real `String::insert` call site must still emit
/// exactly one fail-closed row through the live lane. This is what proves the
/// lane is reachable at all — without it, the "no row for serde_json" assertion
/// below would pass vacuously on a lane that never runs.
#[test]
fn live_lane_still_emits_the_row_for_a_real_string_insert() {
    let func = call_only_fn(STRING_INSERT, 3);
    assert_eq!(
        insert_row_count(&func),
        1,
        "the fail-closed row for a genuinely index-panicking `String::insert` must survive"
    );
}

#[test]
fn live_lane_emits_no_row_for_serde_json_map_insert() {
    let func = call_only_fn(SERDE_JSON_MAP_INSERT, 3);
    assert_eq!(
        insert_row_count(&func),
        0,
        "a total `serde_json::Map::insert` must not carry an index-panic row"
    );
}

/// The sibling lane (`is_bounds_panicking_slice_mutator`) is UNCHANGED by this
/// fix — pinned here so a later edit to the shared helper cannot silently
/// weaken it. Its rows are Unknown (conservative) rather than FAILED, so an
/// over-match there is honest-but-imprecise, not a rejection of valid code.
#[test]
fn bounds_panicking_slice_mutator_lane_is_untouched() {
    let vec_split_off = call_only_fn("std::vec::Vec::<T, A>::split_off", 2);
    let args: Vec<Operand> = vec![Operand::Move(Place::local(1)), Operand::Move(Place::local(2))];
    assert!(
        is_bounds_panicking_slice_mutator(&vec_split_off, "std::vec::Vec::<T, A>::split_off", &args),
        "`Vec::split_off` must keep its fail-closed row"
    );
}

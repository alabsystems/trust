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

use trust_types::{
    BasicBlock, BlockId, LocalDecl, Operand, Place, SourceSpan, Terminator, Ty, UnwindEdge, VcKind,
    VerifiableBody, VerifiableFunction,
};

use super::{
    is_bounds_panicking_slice_mutator, is_index_panicking_container_mutator, method_tail,
    unsupported_mir_vcs,
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
fn method_tail_sees_through_a_fn_pointer_turbofish() {
    use super::alloc_bounds::method_tail;
    // The production spelling. rustc renders a monomorphized `str::split` with
    // the pattern's fn item in the turbofish, and that type contains an ARROW.
    // Counting the arrow's `>` as a closing bracket left the group permanently
    // unbalanced, nothing was stripped, and the tail came back as the fn item's
    // last segment.
    assert_eq!(
        method_tail(
            "core::str::<impl str>::split::<fn(char) -> bool \
             {core::char::methods::<impl char>::is_whitespace}>"
        ),
        "split"
    );
    // A closure pattern, and an `Fn`-trait spelling, carry the same arrow.
    assert_eq!(
        method_tail("core::str::<impl str>::split::<fn(char) -> bool {closure@x.rs:1:1}>"),
        "split"
    );
    assert_eq!(method_tail("core::iter::Iterator::map::<u32, fn(u32) -> u32 {f}>"), "map");
    // A collect sink whose iterator type carries the arrow must still be seen,
    // because a missed tail means NO allocation obligation at all.
    assert_eq!(
        method_tail(
            "<core::str::iter::Split<'_, fn(char) -> bool {g}> as \
             core::iter::traits::iterator::Iterator>::collect::<alloc::vec::Vec<&str>>"
        ),
        "collect"
    );
    // ISOLATING CONTROLS: the shapes the loop already handled must not move.
    assert_eq!(method_tail("std::vec::from_elem::<u8>::<__trust_elem_bytes@1>"), "from_elem");
    assert_eq!(method_tail("alloc::vec::Vec::<u8>::with_capacity"), "with_capacity");
    assert_eq!(method_tail("core::iter::Iterator::collect::<alloc::vec::Vec<u8>>"), "collect");
}

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
    let locals: Vec<LocalDecl> =
        (0..=argc + 1).map(|index| LocalDecl { index, ty: Ty::u64(), name: None }).collect();
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
                        callee_key: crate::sep_engine::tests::fixture_key(&callee.to_string()),
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
        tuple_layouts: Default::default(),
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
        is_bounds_panicking_slice_mutator(
            &vec_split_off,
            "std::vec::Vec::<T, A>::split_off",
            &args
        ),
        "`Vec::split_off` must keep its fail-closed row"
    );
}

// ── `char::encode_utf8` IS A BUFFER-PANICKING ENCODER ───────────────────────

#[test]
fn char_encoders_are_recognized_as_buffer_panicking() {
    // `core/src/char/methods.rs:2482` panics when the destination is shorter
    // than the encoding, which is a safety obligation about the CALLER's buffer.
    assert!(super::is_buffer_panicking_char_encoder("core::char::methods::encode_utf8_raw"));
    assert!(super::is_buffer_panicking_char_encoder(
        "core::char::methods::<impl char>::encode_utf8"
    ));
    // The UTF-16 twin panics the same way on a short buffer, but it is charged by its
    // own ROOT-call recognizer (`is_buffer_panicking_char_utf16_encoder`), never by
    // this one, which the bundle walk also asks: see
    // `char_utf16_encoders_are_charged_at_root_call_sites_only` below.
}

#[test]
fn a_user_encode_utf8_is_not_recognized() {
    // The whole soundness content of the family rows is that they name core's
    // known panic sets. A user method of the same name is not one.
    assert!(!super::is_buffer_panicking_char_encoder("mycrate::text::encode_utf8"));
    assert!(!super::is_buffer_panicking_char_encoder("<mycrate::Ch as mycrate::Enc>::encode_utf8"));
}

#[test]
fn unrelated_char_methods_are_not_recognized() {
    // Exact-method gated: only the two encoders, not everything under `char`.
    assert!(!super::is_buffer_panicking_char_encoder("core::char::methods::len_utf8"));
    assert!(!super::is_buffer_panicking_char_encoder(
        "core::char::methods::<impl char>::is_uppercase"
    ));
}

// ── `char::encode_utf16` IS A BUFFER-PANICKING ENCODER, AT ROOT CALL SITES ───
//
// UTF8-ENCODE-UTF16-SHORTBUF-1 (2026-10-05). Spellings READ OFF
// `TRUST_VANILLA_DEBUG=1` and `-Ztrust-dump=mir-only` on the stage 1 of
// `dc15b882f6`, where the root ledger admitted the first as `vanilla=true` and
// `c.encode_utf16(&mut [0u16; 1])` built rc=0 and panicked.

const CHAR_UTF16_ENCODERS: [&str; 3] = [
    "core::char::methods::<impl char>::encode_utf16",
    "core::char::methods::encode_utf16_raw",
    // A trailing turbofish token the producer may append.
    "core::char::methods::<impl char>::encode_utf16::<__trust_args@0123456789abcdef>",
];

#[test]
fn char_utf16_encoders_are_charged_at_root_call_sites_only() {
    for callee in CHAR_UTF16_ENCODERS {
        assert!(super::is_buffer_panicking_char_utf16_encoder(callee), "`{callee}`");
        assert!(
            super::callee_is_root_call_caller_value_panic(callee),
            "`{callee}` must reach the compiler's ROOT-call-site carve-out"
        );
        // ...and NOT the carve-out the bundle walk asks: core's `EncodeUtf16::next`
        // and `wtf8` call these with a two-unit buffer of their own.
        assert!(
            !super::callee_is_known_caller_value_panic(callee),
            "`{callee}` must stay out of the bundle-walk carve-out"
        );
        assert!(!super::is_buffer_panicking_char_encoder(callee), "`{callee}`");
        assert!(
            super::callee_has_call_site_panic_family(callee),
            "`{callee}` handed as a fn-item type argument must not be admitted"
        );
    }
}

#[test]
fn utf16_lookalikes_and_total_neighbours_are_not_charged() {
    for callee in [
        // TOTAL: the `str` iterator constructor, and the length query.
        "core::str::<impl str>::encode_utf16",
        "core::char::methods::<impl char>::len_utf16",
        "core::char::methods::len_utf16",
        "<core::str::iter::EncodeUtf16<'_> as core::iter::traits::iterator::Iterator>::next",
        // User look-alikes and an impersonator crate.
        "mycrate::encode_utf16",
        "mycrate::char::methods::<impl char>::encode_utf16",
        "<mycrate::Ch as mycrate::Enc>::encode_utf16",
        "__trust_crate@0123456789abcdef::core::char::methods::encode_utf16_raw",
        // A longer name that merely starts with the path.
        "core::char::methods::encode_utf16_raw_lookalike",
        "core::char::methods::<impl char>::encode_utf16::helper",
        // The UTF-8 encoders keep their own (bundle-walk) recognizer.
        "core::char::methods::<impl char>::encode_utf8",
    ] {
        assert!(!super::is_buffer_panicking_char_utf16_encoder(callee), "`{callee}`");
        assert!(!super::callee_is_root_call_caller_value_panic(callee), "`{callee}`");
    }
}

fn utf16_row_count(func: &VerifiableFunction) -> usize {
    unsupported_mir_vcs(func)
        .iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == "Call::encode_utf16::panic-freedom-unverified"
                    || kind == "Call::encode_utf16_raw::panic-freedom-unverified")
        })
        .count()
}

#[test]
fn a_root_encode_utf16_call_mints_the_fail_closed_row() {
    // Before the fix: no row (nothing named the method).
    for callee in &CHAR_UTF16_ENCODERS[..2] {
        assert_eq!(utf16_row_count(&call_only_fn(callee, 2)), 1, "`{callee}`");
    }
    // The total `str` constructor gets none.
    assert_eq!(utf16_row_count(&call_only_fn("core::str::<impl str>::encode_utf16", 1)), 0);
}

// ── `VecDeque`'s CALLER-VALUE MEMBERS (W4 fix round 1, 2026-09-25) ──────────
//
// Spellings READ OFF `TRUST_VANILLA_DEBUG=1` on stage 1 `0.10.0+gc2e3daed7`
// (the compiler's ledger keys), where every one of them was tolerated as
// vanilla and the unguarded call panicked at runtime.

#[test]
fn vecdeque_caller_value_members_are_recognized() {
    for callee in [
        "alloc::collections::vec_deque::VecDeque::<u32>::insert",
        "alloc::collections::vec_deque::VecDeque::<u32>::split_off",
        "alloc::collections::vec_deque::VecDeque::<u32>::rotate_left",
        "alloc::collections::vec_deque::VecDeque::<T, A>::drain::<R>",
        "std::collections::vec_deque::VecDeque::<T, A>::insert",
        // The extractor's monomorph tag trails the method.
        "alloc::collections::vec_deque::VecDeque::<u32>::insert::<__trust_args@0123456789abcdef>",
    ] {
        assert!(
            super::is_caller_value_panicking_deque_method(callee),
            "`{callee}` panics on a caller value"
        );
        assert!(
            super::callee_is_root_call_caller_value_panic(callee),
            "`{callee}` must reach the compiler's ROOT-call-site carve-out"
        );
        // ...and NOT the shared carve-out the bundle walk also asks: std calls these
        // members with its own validated arguments (`swap_remove_back` -> `swap`).
        assert!(
            !super::callee_is_known_caller_value_panic(callee),
            "`{callee}` must stay out of the bundle-walk carve-out"
        );
        assert!(
            super::callee_has_call_site_panic_family(callee),
            "`{callee}` handed as a fn-item type argument must not be admitted"
        );
    }
}

#[test]
fn vecdeque_total_members_and_lookalikes_are_not_recognized() {
    for callee in [
        // TOTAL: they return `Option`, or never panic.
        "alloc::collections::vec_deque::VecDeque::<u32>::remove",
        "alloc::collections::vec_deque::VecDeque::<u32>::swap_remove_back",
        "alloc::collections::vec_deque::VecDeque::<u32>::swap_remove_front",
        "alloc::collections::vec_deque::VecDeque::<u32>::get",
        "alloc::collections::vec_deque::VecDeque::<u32>::truncate",
        "alloc::collections::vec_deque::VecDeque::<u32>::push_back",
        // A user trait's `insert` implemented FOR `VecDeque` is not std's member.
        "<alloc::collections::vec_deque::VecDeque<u32> as mycrate::Store>::insert",
        // An `Index` over a non-`usize` index type is not the audited impl.
        "<alloc::collections::vec_deque::VecDeque<u32> as core::ops::index::Index<mycrate::Key>>::index",
        // A user type whose path merely contains the name.
        "mycrate::vec_deque::VecDeque::<u32>::insert",
        "alloc::collections::vec_deque::VecDequeExt::insert",
        "alloc::collections::vec_deque::VecDeque::<u32>::helpers::insert",
        // `Vec` and the maps stay with their own recognizers.
        "alloc::vec::Vec::<u32>::swap",
        "alloc::collections::btree::map::BTreeMap::<u32, u32>::insert",
    ] {
        assert!(
            !super::is_caller_value_panicking_deque_method(callee),
            "`{callee}` is not a deque caller-value member"
        );
        assert!(
            !super::unwrap_panic::is_deque_scalar_index_call(callee),
            "`{callee}` is not std's scalar deque index"
        );
    }
}

// ── RECONCILED WITH MAIN's `collection_range` (92e7829ca5; W4 salvage 2026-09-28) ──
//
// Main charges these members AT THE CALL SITE — precisely over a stable deque length,
// so a guard discharges them, fail-honest otherwise. Round 1 had them in the
// name-keyed carve-out, which refused them guarded or not. They must be OUT of the
// carve-out and IN main's recognizer, fn-item element types included; losing either
// half is a regression (a guarded over-refusal, or a silent unguarded call).

/// The spellings main's rows own, plain and at a sysroot fn-item element.
const DEQUE_MEMBERS_MAIN_CHARGES: [&str; 12] = [
    "alloc::collections::vec_deque::VecDeque::<u32>::swap",
    "alloc::collections::vec_deque::VecDeque::<u32>::range::<core::ops::range::Range<usize>>",
    "alloc::collections::vec_deque::VecDeque::<u32>::range_mut::<core::ops::range::Range<usize>>",
    "alloc::collections::vec_deque::VecDeque::<u32>::insert_mut",
    "<alloc::collections::vec_deque::VecDeque<u32> as core::ops::index::Index<usize>>::index",
    "<alloc::collections::vec_deque::VecDeque<u32> as core::ops::index::IndexMut<usize>>::index_mut",
    FNITEM_DEQUE_MEMBERS[1],
    FNITEM_DEQUE_MEMBERS[2],
    FNITEM_DEQUE_MEMBERS[5],
    FNITEM_DEQUE_MEMBERS[6],
    FNITEM_DEQUE_MEMBERS[7],
    FNITEM_DEQUE_MEMBERS[8],
];

#[test]
fn vecdeque_members_main_charges_are_left_to_its_rows() {
    use super::SliceMethodPanic as P;
    use super::collection_range::RangeMethodOwner;
    for callee in DEQUE_MEMBERS_MAIN_CHARGES {
        assert!(
            !super::is_caller_value_panicking_deque_method(callee),
            "`{callee}` is charged by `collection_range`; the name carve-out would refuse its guarded form"
        );
        assert!(
            !super::callee_is_root_call_caller_value_panic(callee),
            "`{callee}` must keep the vanilla tolerance at a root call: its charge row is the refusal"
        );
        let tail = super::method_tail(callee);
        let charged = super::panic_calls::slice_method_panic(callee);
        let expected = match tail {
            "swap" => matches!(charged, Some(P::DequeSwap { i_idx: 1, j_idx: 2 })),
            "range" | "range_mut" => matches!(
                charged,
                Some(P::CollectionRange { range_idx: 1, owner: RangeMethodOwner::DequeView, .. })
            ),
            "insert_mut" => matches!(charged, Some(P::ResizingIndexArg { idx: 1 })),
            "index" | "index_mut" => {
                matches!(charged, Some(P::RangeIndex))
                    && super::unwrap_panic::is_deque_scalar_index_call(callee)
            }
            other => panic!("unexpected tail `{other}` for `{callee}`"),
        };
        assert!(expected, "`{callee}` (tail `{tail}`) is not charged by main's row");
        assert!(
            super::callee_has_call_site_panic_family(callee),
            "`{callee}` handed as a fn-item type argument must not be admitted"
        );
    }
}

#[test]
fn a_deque_member_main_declines_keeps_the_carve_out() {
    // `collection_range`'s identity test refuses a rendered name that carries an
    // unauthenticated-crate stamp ANYWHERE — here inside the element type, a
    // tuple-struct constructor of a crate built `--crate-name alloc` (the compiler
    // counts a constructor foundational whoever owns it). With no charge row the call
    // would fall to the slice `swap` arm, which emits nothing for a deque; so the
    // name carve-out must keep refusing it.
    for callee in [
        "alloc::collections::vec_deque::VecDeque::<fn(u32) -> __trust_crate@0123456789abcdef::alloc::Id {__trust_crate@0123456789abcdef::alloc::Id}>::swap",
        "alloc::collections::vec_deque::VecDeque::<fn(u32) -> __trust_crate@0123456789abcdef::alloc::Id {__trust_crate@0123456789abcdef::alloc::Id}>::range::<core::ops::range::Range<usize>>",
        "alloc::collections::vec_deque::VecDeque::<fn(u32) -> __trust_crate@0123456789abcdef::alloc::Id {__trust_crate@0123456789abcdef::alloc::Id}>::range_mut::<core::ops::range::Range<usize>>",
        "alloc::collections::vec_deque::VecDeque::<fn(u32) -> __trust_crate@0123456789abcdef::alloc::Id {__trust_crate@0123456789abcdef::alloc::Id}>::insert_mut",
    ] {
        assert!(
            super::collection_range::collection_method_panic(callee).is_none(),
            "planted premise gone: `collection_range` now names `{callee}`, so this test proves nothing"
        );
        assert!(
            super::is_caller_value_panicking_deque_method(callee),
            "`{callee}` has no charge row, so the carve-out must keep it"
        );
        assert!(
            super::callee_is_root_call_caller_value_panic(callee),
            "`{callee}` must reach the compiler's ROOT-call-site carve-out"
        );
    }
}

// ── FN-ITEM ELEMENT TYPES (W4 fix round 2, 2026-09-26) ──────────────────────
//
// Spellings READ OFF `TRUST_VANILLA_DEBUG=1` on stage 1 `0.10.0+g6a3460983`, where
// each was `vanilla=true` and the unguarded program built rc=0 and panicked (probes
// d01 d02 d03 d20 d23 d24 d25 d26, and p01 p02 p04 p05 p06 p08 p15). A sysroot fn
// item's type renders as `fn(u32) -> u32 {core::num::<impl u32>::count_ones}`: an
// ARROW, whose `>` is not a bracket, and a `core::num::` path that is not the
// receiver's.

const FNITEM_DEQUE_MEMBERS: [&str; 9] = [
    "alloc::collections::vec_deque::VecDeque::<fn(u32) -> u32 {core::num::<impl u32>::count_ones}>::insert",
    "alloc::collections::vec_deque::VecDeque::<fn(u32) -> u32 {core::num::<impl u32>::count_ones}>::swap",
    "alloc::collections::vec_deque::VecDeque::<fn(u32) -> u32 {core::num::<impl u32>::count_ones}>::range::<core::ops::range::Range<usize>>",
    "alloc::collections::vec_deque::VecDeque::<core::option::Option<fn(u8) -> u32 {core::num::<impl u8>::count_zeros}>>::rotate_right",
    "alloc::collections::vec_deque::VecDeque::<fn(u64) -> u32 {core::num::<impl u64>::leading_zeros}>::insert",
    "alloc::collections::vec_deque::VecDeque::<fn(i32) -> i32 {core::num::<impl i32>::signum}>::range_mut::<core::ops::range::Range<usize>>",
    "<alloc::collections::vec_deque::VecDeque<fn(u32) -> <u32 as core::ops::bit::Not>::Output {<u32 as core::ops::bit::Not>::not}> as core::ops::index::Index<usize>>::index",
    "<alloc::collections::vec_deque::VecDeque<fn(u32) -> <u32 as core::ops::bit::Not>::Output {<u32 as core::ops::bit::Not>::not}> as core::ops::index::IndexMut<usize>>::index_mut",
    "<alloc::collections::vec_deque::VecDeque<fn(i32) -> <i32 as core::ops::arith::Neg>::Output {<i32 as core::ops::arith::Neg>::neg}> as core::ops::index::Index<usize>>::index",
];

#[test]
fn turbofish_strip_does_not_close_a_group_at_an_arrow() {
    use super::unwrap_panic::callee_without_turbofish_args;
    assert_eq!(
        callee_without_turbofish_args(FNITEM_DEQUE_MEMBERS[0]),
        "alloc::collections::vec_deque::VecDeque::::insert"
    );
    // Two arrows at different depths, and a nested turbofish inside the fn item.
    assert_eq!(
        callee_without_turbofish_args(
            "alloc::collections::vec_deque::VecDeque::<fn(u32) -> fn(u8) -> u8>::insert::<__trust_args@0123>"
        ),
        "alloc::collections::vec_deque::VecDeque::::insert::"
    );
    assert_eq!(
        callee_without_turbofish_args(
            "alloc::vec::Vec::<fn(&alloc::collections::vec_deque::VecDeque<u32>) -> usize \
             {alloc::collections::vec_deque::VecDeque::<u32>::len}>::remove"
        ),
        "alloc::vec::Vec::::remove"
    );
    // Unbalanced stays verbatim (fail-closed), arrow or not.
    assert_eq!(
        callee_without_turbofish_args("alloc::vec::Vec::<fn(u32) -> u32::remove"),
        "alloc::vec::Vec::<fn(u32) -> u32::remove"
    );
}

#[test]
fn vecdeque_members_at_a_fn_item_element_are_recognized() {
    // `insert` (x2) and `rotate_right`; the others in the table are main's rows
    // (`vecdeque_members_main_charges_are_left_to_its_rows`).
    for callee in [FNITEM_DEQUE_MEMBERS[0], FNITEM_DEQUE_MEMBERS[3], FNITEM_DEQUE_MEMBERS[4]] {
        assert!(
            super::is_caller_value_panicking_deque_method(callee),
            "`{callee}` panics on a caller value"
        );
        assert!(
            super::callee_is_root_call_caller_value_panic(callee),
            "`{callee}` must reach the compiler's ROOT-call-site carve-out"
        );
        assert!(
            !super::callee_is_known_caller_value_panic(callee),
            "`{callee}` must stay out of the bundle-walk carve-out"
        );
    }
}

#[test]
fn vecdeque_total_members_at_a_fn_item_element_stay_unrecognized() {
    for callee in [
        "alloc::collections::vec_deque::VecDeque::<fn(u32) -> u32 {core::num::<impl u32>::count_ones}>::swap_remove_back",
        "alloc::collections::vec_deque::VecDeque::<fn(u32) -> u32 {core::num::<impl u32>::count_ones}>::remove",
        "alloc::collections::vec_deque::VecDeque::<fn(u32) -> u32 {core::num::<impl u32>::count_ones}>::get",
        // A user trait's `insert`/`index` for a deque of trait-method fn items: the
        // depth-0 split finds the USER trait, not the `Not` inside the element.
        "<alloc::collections::vec_deque::VecDeque<u32> as mycrate::Ins>::insert",
        "<alloc::collections::vec_deque::VecDeque<fn(u32) -> <u32 as core::ops::bit::Not>::Output {<u32 as core::ops::bit::Not>::not}> as mycrate::Ins>::insert",
        "<alloc::collections::vec_deque::VecDeque<fn(u32) -> <u32 as core::ops::index::Index<usize>>::Output {f}> as mycrate::Store>::index",
        // A user type whose ELEMENT is the deque: the receiver is not std's.
        "<mycrate::Q<fn(u32) -> <alloc::collections::vec_deque::VecDeque<u32> as core::ops::index::Index<usize>>::Output {f}> as core::ops::index::Index<usize>>::index",
    ] {
        assert!(
            !super::is_caller_value_panicking_deque_method(callee),
            "`{callee}` is not a deque caller-value member"
        );
        assert!(
            !super::unwrap_panic::is_deque_scalar_index_call(callee),
            "`{callee}` is not std's scalar deque index"
        );
    }
}

#[test]
fn a_fn_item_element_does_not_hide_a_vec_index_mutator() {
    // `collections::` inside the ELEMENT used to survive the broken strip and trip the
    // wholesale `collections::` exclusion.
    assert!(is_index_panicking_container_mutator(
        "alloc::vec::Vec::<fn(&alloc::collections::vec_deque::VecDeque<u32>) -> usize \
         {alloc::collections::vec_deque::VecDeque::<u32>::len}>::remove"
    ));
    assert!(is_index_panicking_container_mutator(
        "alloc::vec::Vec::<fn(u32) -> u32 {core::num::<impl u32>::count_ones}>::insert"
    ));
}

#[test]
fn a_fn_item_element_does_not_make_a_container_an_integer_method() {
    for callee in [
        "alloc::vec::Vec::<fn(u32) -> u32 {core::num::<impl u32>::count_ones}>::split_off",
        "alloc::vec::Vec::<fn(u32) -> u32 {core::num::<impl u32>::count_ones}>::drain::<core::ops::range::Range<usize>>",
        "alloc::vec::Vec::<fn(u32) -> u32 {core::num::<impl u32>::count_ones}>::extend_from_within::<core::ops::range::Range<usize>>",
        "alloc::collections::vec_deque::VecDeque::<fn(u32) -> u32 {core::num::<impl u32>::count_ones}>::split_off",
        "alloc::collections::vec_deque::VecDeque::<fn(u32) -> u32 {core::num::<impl u32>::count_ones}>::drain::<core::ops::range::Range<usize>>",
        "alloc::collections::vec_deque::VecDeque::<fn(u32) -> u32 {core::num::<impl u32>::count_ones}>::rotate_left",
        "alloc::collections::vec_deque::VecDeque::<core::option::Option<fn(u8) -> u32 {core::num::<impl u8>::count_zeros}>>::rotate_right",
        // An element type from any module called `num`.
        "alloc::vec::Vec::<mycrate::num::Big>::split_off",
    ] {
        let func = call_only_fn(callee, 2);
        let args: Vec<Operand> =
            vec![Operand::Move(Place::local(1)), Operand::Move(Place::local(2))];
        assert!(
            is_bounds_panicking_slice_mutator(&func, callee, &args),
            "`{callee}` is a container's bounds-panicking mutator, not an integer method"
        );
    }
    // The TOTAL integer rotates are still excluded (spine `core::num::::rotate_left`).
    for callee in [
        "core::num::<impl u32>::rotate_left",
        "core::num::<impl i64>::rotate_right",
        "core::num::<impl u32>::rotate_left::<__trust_args@0123>",
    ] {
        let func = call_only_fn(callee, 2);
        let args: Vec<Operand> =
            vec![Operand::Move(Place::local(1)), Operand::Move(Place::local(2))];
        assert!(
            !is_bounds_panicking_slice_mutator(&func, callee, &args),
            "total integer `{callee}` must not be flagged"
        );
    }
}

/// END TO END through `unsupported_mir_vcs`: the fn-item-element deque `insert` gets
/// the fail-closed row (it got none on `0.10.0+g6a3460983`).
#[test]
fn live_lane_emits_the_row_for_a_fn_item_element_deque_insert() {
    let func = call_only_fn(FNITEM_DEQUE_MEMBERS[0], 3);
    assert_eq!(insert_row_count(&func), 1);
}

// ---------------------------------------------------------------------------
// ROTATE-ITEM-NAME-1 (2026-10-06): the fn-item deny-list's bounds-panicking
// mutator arm (`rotate_left`/`rotate_right`, `split_off`, `drain`, ...) had no owner
// check, so core's TOTAL integer rotate handed over as an item —
// `v.iter().copied().fold(1u32, u32::rotate_left)` — was withheld from the default
// policy's vanilla admission and the function refused (stage 1 of `4ccd862830`,
// `TRUST_VANILLA_DEBUG=1`: `vanilla=false callee=…fold::<u32, fn(u32, u32) -> u32
// {core::num::<impl u32>::rotate_left}>`), while `u32::wrapping_shl` on the same owner
// was admitted. The integer spellings are those `safe_def_path_str_with_args` renders
// for the items (read off that ledger).
// ---------------------------------------------------------------------------

#[test]
fn cores_integer_rotate_items_leave_the_fn_item_deny_list() {
    for callee in [
        "core::num::<impl u32>::rotate_left",
        "core::num::<impl u32>::rotate_right",
        "core::num::<impl u8>::rotate_left",
        "core::num::<impl i64>::rotate_right",
        "core::num::<impl usize>::rotate_left",
        "core::num::<impl i128>::rotate_right",
        "std::num::<impl u16>::rotate_left",
        "core::num::<impl u32>::rotate_left::<__trust_args@0123456789abcdef>",
    ] {
        assert!(
            !super::callee_has_call_site_panic_family(callee),
            "`{callee}` is total (`intrinsics::rotate_left/right`); handed over as an item \
             it must not be withheld"
        );
    }
}

#[test]
fn container_rotates_and_integer_rotate_lookalikes_stay_in_the_fn_item_deny_list() {
    for callee in [
        // The bounds-panicking members the arm exists for (`mid > len` panics).
        "core::slice::<impl [u8]>::rotate_left",
        "core::slice::<impl [T]>::rotate_right",
        "alloc::collections::vec_deque::VecDeque::<u32>::rotate_left",
        "alloc::collections::vec_deque::VecDeque::<u32>::rotate_right",
        // The arm's other names, which no integer inherent shares.
        "alloc::vec::Vec::<u32>::split_off",
        "alloc::string::String::split_off",
        "alloc::vec::Vec::<u32>::drain::<core::ops::range::Range<usize>>",
        "core::slice::<impl [u32]>::copy_within::<core::ops::range::Range<usize>>",
        "core::slice::<impl [u32]>::select_nth_unstable",
        "core::slice::<impl [u32]>::select_nth_unstable_by_key::<u8, fn(&u32) -> u8>",
        "alloc::vec::Vec::<u32>::extend_from_within::<core::ops::range::Range<usize>>",
        // Look-alikes of core's integer inherent: a stamped impersonator, a user module
        // path, a user method and a user trait. None is `int_inherent`'s.
        "__trust_crate@1973d11b2baa21fa::core::num::<impl u32>::rotate_left",
        "mycrate::num::<impl u32>::rotate_left",
        "mycrate::W::rotate_left",
        "<u32 as mycrate::Rot>::rotate_right",
        // core's other integer owners: total too, but not this fix's to admit (kept
        // as an over-refusal).
        "core::num::nonzero::NonZero::<u32>::rotate_left",
        "core::num::wrapping::Wrapping::<u32>::rotate_left",
        "core::num::saturating::Saturating::<u32>::rotate_right",
    ] {
        assert!(
            super::callee_has_call_site_panic_family(callee),
            "`{callee}` handed as a fn-item type argument must not be admitted"
        );
    }
}

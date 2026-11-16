// Trust (2026-09-25, std-range-family): the vcgen half of the std index/range/count
// false-accept fixes, pinned on REAL extracted MIR (`-Ztrust-dump=mir-only`,
// `fixtures/std_range_family/*.json`, the function named by each file). Every
// UNGUARDED shape here built rc=0 on the default lane (stage-1 `6606d3bdf`) and
// panicked at runtime on the caller's argument; the end-to-end pins are the
// `refused`/`guarded` revisions of
// `tests/ui/trust/policy_b/std_index_range_panics_charged.rs`. These tests pin the
// row each lane now MINTS and — through the in-process solver — that the precise
// rows refute the unguarded call and prove the guarded twin. Dumps are optimized
// MIR, so they do not claim the compiler path on their own.
use trust_types::*;
use trust_vcgen::generate_vcs;

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/std_range_family/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

fn router() -> trust_router::Router {
    test_router::deterministic_test_router()
}

/// The kinds of `UnsupportedMir` row this family mints.
const FAMILY_UNMODELED: &[&str] = &[
    "vecdeque-range-bounds-unmodeled",
    "vecdeque-index-unmodeled",
    "vec-range-method-bounds-unmodeled",
    "string-range-char-boundary-unmodeled",
    "string-char-boundary-unmodeled",
    "container-insert-mut-index-unmodeled",
    "slice-repeat-capacity-overflow",
    "slice-const-chunk-size-zero",
    "vec-into-flattened-len-overflow",
    "str-range-char-boundary-unmodeled",
    "slice-range-len-unresolved",
];

enum Want {
    /// A precise bounds row the solver REFUTES (the call panics for some input).
    Refuted,
    /// A fail-honest row of this kind (refused under the default policy).
    Unmodeled(&'static str),
    /// Every bounds row PROVES and no family row is fail-honest.
    Proved,
    /// No bounds row and no family row at all (the argument cannot panic).
    NoRow,
}

fn bounds_rows(vcs: &[VerificationCondition]) -> Vec<&VerificationCondition> {
    vcs.iter().filter(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck)).collect()
}

fn family_unmodeled(vcs: &[VerificationCondition]) -> Vec<String> {
    vcs.iter()
        .filter_map(|vc| match &vc.kind {
            VcKind::UnsupportedMir { kind, .. } if FAMILY_UNMODELED.contains(&kind.as_str()) => {
                Some(kind.clone())
            }
            _ => None,
        })
        .collect()
}

fn check(name: &str, want: Want) {
    let func = load(name);
    let vcs = generate_vcs(&func);
    let bounds = bounds_rows(&vcs);
    let unmodeled = family_unmodeled(&vcs);
    let router = router();
    let verdicts: Vec<VerificationResult> = bounds
        .iter()
        .map(|vc| router.verify_all(std::slice::from_ref(*vc)).into_iter().next().unwrap().1)
        .collect();
    let dbg = || {
        bounds
            .iter()
            .zip(&verdicts)
            .map(|(vc, r)| format!("{}\n  => {r:?}", vc.formula.to_smtlib()))
            .collect::<Vec<_>>()
            .join("\n")
    };
    match want {
        Want::Refuted => assert!(
            verdicts.iter().any(|r| matches!(r, VerificationResult::Failed { .. })),
            "{name}: the unguarded call must carry a REFUTED bounds row; unmodeled={unmodeled:?}\n{}",
            dbg()
        ),
        Want::Unmodeled(kind) => assert!(
            unmodeled.iter().any(|k| k == kind),
            "{name}: expected the fail-honest `{kind}` row; got {unmodeled:?}\n{}",
            dbg()
        ),
        Want::Proved => {
            assert!(!bounds.is_empty(), "{name}: the guarded call must still carry its bounds row");
            assert!(
                verdicts.iter().all(|r| matches!(r, VerificationResult::Proved { .. })),
                "{name}: the guarded bounds row must PROVE\n{}",
                dbg()
            );
            assert!(unmodeled.is_empty(), "{name}: no fail-honest row expected; got {unmodeled:?}");
        }
        Want::NoRow => assert!(
            bounds.is_empty() && unmodeled.is_empty(),
            "{name}: `..`-shaped / zero arguments cannot panic and must mint nothing; \
             unmodeled={unmodeled:?}\n{}",
            dbg()
        ),
    }
}

// ---- VecDeque: precise over a stable deque length ----

#[test]
fn a_deque_index_is_charged_and_its_guard_proves_it() {
    check("dq_index", Want::Refuted);
    check("dq_index_g", Want::Proved);
    check("dq_index_mut_g", Want::Proved);
    // `!d.is_empty()` bounds the same `coll_len(d)` the index reads.
    check("dq_index_front_g", Want::Proved);
    // A struct-field deque under `&self` keys on the field place.
    check("dq_index_field_g", Want::Proved);
}

/// SOUNDNESS DIRECTION: a length read BEFORE a resize must not discharge an index
/// AFTER it. An owned local deque that is pushed to has no stable length at all, and
/// neither, since VEC-LEN-PARAM-COPY-1 (2026-10-07), has a `&mut VecDeque` parameter
/// that `d.clear()` / `d.push_back()` receive: real MIR hands them the parameter as
/// `copy _1`, which the length-stability oracle used to miss (only the call havoc of
/// the length tie kept those rows refuted). All three are the fail-honest Unknown.
#[test]
fn a_resize_between_the_guard_and_the_index_is_never_proved() {
    for name in ["dq_index_after_clear_g", "dq_index_after_push"] {
        check(name, Want::Unmodeled("vecdeque-index-unmodeled"));
        let vcs = generate_vcs(&load(name));
        let router = router();
        assert!(
            bounds_rows(&vcs).iter().all(|vc| !matches!(
                router.verify_all(std::slice::from_ref(*vc)).into_iter().next().unwrap().1,
                VerificationResult::Proved { .. }
            )),
            "{name}: a resized deque's index must never prove"
        );
    }
    check("dq_range_owned_local", Want::Unmodeled("vecdeque-index-unmodeled"));
}

#[test]
fn a_deque_range_is_charged_precisely() {
    check("dq_range", Want::Refuted);
    check("dq_range_g", Want::Proved);
    check("dq_range_mut_g", Want::Proved);
    check("dq_range_incl_g", Want::Proved);
    check("dq_range_to_incl_g", Want::Proved);
    // `b <= len` alone leaves `a > b` open: std panics there, so must we.
    check("dq_range_half_g", Want::Refuted);
    // `..=usize::MAX`: `+1` overflows — std's "attempted to index slice up to
    // maximum usize"; the unbounded-integer end exceeds every length.
    check("dq_range_incl_max", Want::Refuted);
    check("dq_range_full", Want::NoRow);
    // Untraceable bounds fail honest: a range handed in whole, and a range local
    // mutated (`r.start = 7`) before use.
    check("dq_range_param", Want::Unmodeled("vecdeque-range-bounds-unmodeled"));
    check("dq_range_mutated", Want::Unmodeled("vecdeque-range-bounds-unmodeled"));
}

#[test]
fn a_deque_swap_is_charged_and_a_single_length_guard_proves_it() {
    check("dq_swap", Want::Refuted);
    check("dq_swap_g1", Want::Proved);
}

// ---- resizing / char-boundary / capacity: fail-honest unless trivially safe ----

#[test]
fn vec_splice_and_extract_if_fail_honest_except_on_trivial_ranges() {
    check("vec_splice", Want::Unmodeled("vec-range-method-bounds-unmodeled"));
    check("vec_extract_if", Want::Unmodeled("vec-range-method-bounds-unmodeled"));
    // `-O` inlines `Vec::extract_if` into `ExtractIf::new(vec, pred, range)`.
    check("vec_extract_if_o", Want::Unmodeled("vec-range-method-bounds-unmodeled"));
    check("vec_splice_full", Want::NoRow);
    check("vec_splice_front", Want::NoRow);
    check("vec_extract_if_full", Want::NoRow);
}

#[test]
fn insert_mut_fails_honest_on_vec_and_deque() {
    check("vec_insert_mut", Want::Unmodeled("container-insert-mut-index-unmodeled"));
    check("dq_insert_mut", Want::Unmodeled("container-insert-mut-index-unmodeled"));
}

#[test]
fn string_range_and_boundary_methods_fail_honest_except_at_zero() {
    check("st_drain", Want::Unmodeled("string-range-char-boundary-unmodeled"));
    check("st_replace_range", Want::Unmodeled("string-range-char-boundary-unmodeled"));
    check("st_extend_from_within", Want::Unmodeled("string-range-char-boundary-unmodeled"));
    check("st_split_off", Want::Unmodeled("string-char-boundary-unmodeled"));
    check("st_truncate", Want::Unmodeled("string-char-boundary-unmodeled"));
    check("st_drain_full", Want::NoRow);
    check("st_truncate_zero", Want::NoRow);
}

#[test]
fn slice_repeat_is_charged_like_str_repeat() {
    check("sl_repeat", Want::Unmodeled("slice-repeat-capacity-overflow"));
    check("sl_repeat_one", Want::NoRow);
}

// ---- slice / str / Vec index by `..=b`, `a..=b` and `(Bound, Bound)` ----

#[test]
fn inclusive_and_bound_pair_indexes_are_charged_precisely() {
    check("sl_to_incl", Want::Refuted);
    check("sl_to_incl_g", Want::Proved);
    // `-O` rewrites `s[..=b]` to `(0..=b).index(s)`.
    check("sl_to_incl_o", Want::Refuted);
    check("sl_to_incl_g_o", Want::Proved);
    check("sl_incl_g", Want::Proved);
    check("sl_bounds", Want::Refuted);
    check("sl_bounds_g", Want::Proved);
    check("sl_bounds_excl_g", Want::Proved);
    check("sl_bounds_unb", Want::Proved);
    // `str` carries the unmodeled char-boundary panic too: fail closed. Trust (2026-10-02,
    // class 10): the refusal is the declined char-boundary row (the one `str::split_at`
    // gives), no longer the always-violated `Bool(true)` as a refutable bounds row, which
    // FAILED on an arbitrary model whether or not `b` was a boundary.
    check("str_to_incl", Want::Unmodeled("str-range-char-boundary-unmodeled"));
    // An owned `Vec` receiver has no modeled length on this lane: fail closed. Trust
    // (2026-10-02, class 10): the declined row, no longer the always-violated `Bool(true)`
    // as a refutable bounds row (an arbitrary-model FAILED whatever `b` was).
    check("vec_to_incl", Want::Unmodeled("slice-range-len-unresolved"));
}

// ---- const-generic chunk size, and `into_flattened` over a zero-sized element ----

#[test]
fn a_zero_const_chunk_size_is_charged_and_a_nonzero_literal_is_not() {
    check("sl_as_chunks0", Want::Unmodeled("slice-const-chunk-size-zero"));
    check("sl_as_rchunks_mut0", Want::Unmodeled("slice-const-chunk-size-zero"));
    check("sl_array_windows0", Want::Unmodeled("slice-const-chunk-size-zero"));
    // `fn g<const N: usize>(v: &[u8]) { v.as_chunks::<N>() }` — the generic body
    // renders `::<N>`; `g::<0>` panics, so the body is charged.
    check("sl_as_chunks_generic_body", Want::Unmodeled("slice-const-chunk-size-zero"));
    check("sl_as_chunks4", Want::NoRow);
    check("sl_array_windows2", Want::NoRow);
}

#[test]
fn into_flattened_is_charged_only_for_a_zero_sized_element() {
    check("vec_into_flattened_zst", Want::Unmodeled("vec-into-flattened-len-overflow"));
    check("vec_into_flattened_zst1", Want::NoRow);
    check("vec_into_flattened_u8", Want::NoRow);
}

// ---- Vec / VecDeque `drain(range)`: no row where the range check cannot fail ----
//
// Trust (cap vec-drain, 2026-10-03). Fixtures are UNOPTIMIZED MIR from stage 1
// `5424ce87e` (`-Ztrust-dump=mir-only`), the shape clean's debug build verifies.
// The unmodeled fallback minted `Call::drain::panic-freedom-unverified` for every
// std drain, and the Level-0 summary counts that kind `failed`; for `..`, `0..`
// and `..0` std's one check (`slice::range(r, ..len)`) cannot fail, so the row was
// a false refutation. Every other shape keeps the row, exactly as before.

/// The `Call::drain::panic-freedom-unverified` rows of `name` (either fallback:
/// the slice-mutator one or the `VecDeque` caller-value one).
fn drain_refusals(name: &str) -> usize {
    generate_vcs(&load(name))
        .iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == "Call::drain::panic-freedom-unverified")
        })
        .count()
}

#[test]
fn a_std_drain_over_a_full_or_zero_anchored_range_mints_no_refusal() {
    for name in
        ["vec_drain_full", "vec_drain_from0", "vec_drain_to0", "dq_drain_full", "dq_drain_from0"]
    {
        assert_eq!(drain_refusals(name), 0, "{name}: this range cannot fail `slice::range`");
        // Nor does it reappear as another family row.
        assert!(family_unmodeled(&generate_vcs(&load(name))).is_empty(), "{name}");
    }
}

/// CONTROLS: the same call with a range that CAN panic keeps its row — a symbolic
/// end (`..n`), a symbolic or nonzero start (`n..`, `1..`), and a range handed in
/// whole. Each panics at runtime for a short enough receiver.
#[test]
fn a_std_drain_whose_range_can_panic_keeps_its_refusal() {
    for name in ["vec_drain_to", "vec_drain_from1", "vec_drain_param", "dq_drain_from"] {
        assert_eq!(drain_refusals(name), 1, "{name}: an unguarded drain must stay refused");
    }
}

// ---- review follow-up: the remaining zero-anchored spellings and the near misses ----
//
// Fixtures dumped by the same stage 1 (`-Ztrust-dump=mir-only`, unoptimized) from
// `vec-drain-adv/a.rs`; each keeps the `adv_*` name it was dumped under.

/// The other spellings whose `slice::range` check cannot fail: `0..0` on both
/// types, deque `..0`, `(Included(0), Unbounded)`, a `..` bound to a local first,
/// and `Z..` for a `const Z: usize = 0`.
#[test]
fn the_other_non_panicking_drain_spellings_mint_no_refusal() {
    for name in [
        "vec_drain_00",
        "dq_drain_00",
        "dq_drain_to0",
        "vec_drain_bound_incl0",
        "vec_drain_full_local",
        "vec_drain_const0",
    ] {
        assert_eq!(drain_refusals(name), 0, "{name}: this range cannot fail `slice::range`");
        assert!(family_unmodeled(&generate_vcs(&load(name))).is_empty(), "{name}");
    }
}

/// CONTROLS a literal-zero matcher could wrongly accept: an INCLUSIVE end of 0
/// (`0..=0`, `..=0`: panic on an empty receiver), `..=usize::MAX` (end overflow),
/// an EXCLUDED start of 0 (`(Excluded(0), Unbounded)`: panics on an empty
/// receiver), a `0..` whose start is overwritten directly or through `&mut`, a
/// `0..0` reassigned to `5..9` on one path, a drain in a loop whose start moves
/// from 0 to 1, and a USER trait method named `drain` on `Vec` over `..`.
#[test]
fn a_zero_looking_drain_that_can_still_panic_keeps_its_refusal() {
    for name in [
        "vec_drain_incl00",
        "vec_drain_toincl0",
        "vec_drain_toincl_max",
        "vec_drain_bound_excl0",
        "vec_drain_mut_field",
        "vec_drain_mut_ref",
        "vec_drain_rebind",
        "vec_drain_loop",
        "dq_drain_incl00",
        "vec_drain_user_trait",
    ] {
        assert_eq!(drain_refusals(name), 1, "{name}: this drain can panic and must stay refused");
    }
}

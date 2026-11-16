// Trust (2026-10-14, ALLOC-RECEIVER-ZST-1): every allocation sink that ADDS to a live
// receiver asks first whether memory bounds the length that receiver already holds
// (`alloc_vcs::live_receiver_length_is_bounded`), pinned on REAL extracted MIR. The
// fixtures under `fixtures/zst_receiver_growth/` are one function per file, named by
// the function, dumped from the source beside them on stage 1 of `5184affbb97`.
//
// A `Vec<()>` or `VecDeque<()>` can already hold `usize::MAX` units
// (`set_len(usize::MAX)` on a zero-sized `Vec` is sound), and ONE more element panics
// "capacity overflow". Only `extend` asked (27264a61eb1). MEASURED on that stage 1
// (the same dump, verified), this lane's rows were:
//
//   * `ci_vec_zst_counted`, `ci_vec_zst_repeat` (`collect_into`), `reserve_vec_zst`,
//     `reserve_deque_zst`, `extend_reserve_vec_zst`: ONE row, `n >= 2^28` under
//     `n < 100`, KERNEL-CERTIFIED — at stride zero the receiver charge has no byte
//     term, so the row was the element ceiling alone;
//   * `ci_vec_zst_bounded`, `ci_deque_zst_bounded` (`collect_into` from a bounded
//     slice) and `reserve_vec_zst_const` (`reserve(5)`): NO row — the bounded-source
//     grant counted a full receiver as `2^56 + 1` zero-byte items, and the constant
//     skip saw no byte term to fire;
//   * `ci_vec_zst_option`: `count-not-derivable`, an Unknown about the SOURCE.
//
// The compiler's ZST-GROWTH-1 fence (a std `Vec`/`VecDeque`/`BinaryHeap` of zero-sized
// elements is not foundational) refused each of these calls on its own, so the build
// was not fooled; this lane was. Each now keeps the visible
// `UnboundedAllocation::<sink>::receiver-length-not-bounded` Unknown. The controls —
// sized `Vec`/`VecDeque` receivers, a `String`, a `BTreeSet<()>` (one key at most) —
// keep exactly their rows: a counted row that a guard PROVES, or the bounded-source
// grant.
use trust_types::*;

#[path = "support/test_router.rs"]
mod test_router;

/// Extractions on a 64-bit host, generated as the compiler generates them there.
fn generate_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    trust_vcgen::with_target_pointer_bits(Some(64), || trust_vcgen::generate_vcs(func))
}

fn load(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture MIR must deserialize")
}

/// The allocation lane's rows: counted rows and its `UnboundedAllocation::` Unknowns.
fn alloc_rows(vcs: &[VerificationCondition]) -> Vec<&VerificationCondition> {
    vcs.iter()
        .filter(|vc| match &vc.kind {
            VcKind::UnboundedAllocation { .. } => true,
            VcKind::UnsupportedMir { kind, .. } => kind.starts_with("UnboundedAllocation::"),
            _ => false,
        })
        .collect()
}

fn solve(vc: &VerificationCondition) -> VerificationResult {
    let vc = vc.clone();
    std::thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(move || {
            let router = test_router::deterministic_test_router();
            router.verify_all(std::slice::from_ref(&vc)).into_iter().next().expect("one verdict").1
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread")
}

macro_rules! fixture {
    ($name:literal) => {
        ($name, include_str!(concat!("fixtures/zst_receiver_growth/", $name, ".json")))
    };
}

#[test]
fn every_zero_sized_live_receiver_keeps_the_receiver_unknown() {
    for ((name, json), sink) in [
        (fixture!("ci_vec_zst_counted"), "Iterator::collect_into"),
        (fixture!("ci_vec_zst_repeat"), "Iterator::collect_into"),
        (fixture!("ci_vec_zst_bounded"), "Iterator::collect_into"),
        (fixture!("ci_vec_zst_option"), "Iterator::collect_into"),
        (fixture!("ci_deque_zst_bounded"), "Iterator::collect_into"),
        (fixture!("ext_vec_zst"), "Extend::extend"),
        (fixture!("ext_deque_zst"), "Extend::extend"),
        (fixture!("ext_heap_zst"), "Extend::extend"),
        (fixture!("ext_tuple_zst"), "Extend::extend"),
        (fixture!("reserve_vec_zst"), "Vec::reserve"),
        (fixture!("reserve_vec_zst_const"), "Vec::reserve"),
        (fixture!("reserve_deque_zst"), "Vec::reserve"),
        (fixture!("extend_reserve_vec_zst"), "Vec::reserve"),
    ] {
        let func = load(json);
        assert_eq!(func.def_path, format!("zst_receiver_growth::{name}"), "fixture identity");
        let vcs = generate_vcs(&func);
        let rows = alloc_rows(&vcs);
        let [row] = rows.as_slice() else {
            panic!("{name}: expected exactly the receiver Unknown, got {rows:#?}")
        };
        let VcKind::UnsupportedMir { kind, .. } = &row.kind else {
            panic!("{name}: a counted row a guard can discharge is not a charge: {row:#?}")
        };
        assert_eq!(
            kind,
            &format!("UnboundedAllocation::{sink}::receiver-length-not-bounded"),
            "{name}"
        );
    }
}

#[test]
fn a_receiver_whose_length_memory_bounds_keeps_its_counted_row() {
    // Each guarded by `n < 100`: one counted row, PROVED on a 64-bit target.
    for (name, json) in [
        fixture!("ci_vec_u64_counted"),
        fixture!("ci_deque_u64_counted"),
        fixture!("reserve_vec_u64"),
        fixture!("reserve_deque_u64"),
        fixture!("reserve_string"),
    ] {
        let func = load(json);
        assert_eq!(func.def_path, format!("zst_receiver_growth::{name}"), "fixture identity");
        let vcs = generate_vcs(&func);
        let rows = alloc_rows(&vcs);
        let [row] = rows.as_slice() else {
            panic!("{name}: expected one counted row, got {rows:#?}")
        };
        assert!(
            matches!(row.kind, VcKind::UnboundedAllocation { .. }),
            "{name}: expected a counted row, got {row:#?}"
        );
        let r = solve(row);
        assert!(matches!(r, VerificationResult::Proved { .. }), "{name}: {r:?}");
    }
}

#[test]
fn a_keyed_destination_of_zero_sized_keys_keeps_the_bounded_source_grant() {
    // A `BTreeSet<()>` holds at most one key, and its `extend` inserts one at a time:
    // its length is bounded whatever the key, so the grant stands — no row.
    let (name, json) = fixture!("ci_btree_zst_bounded");
    let vcs = generate_vcs(&load(json));
    let rows = alloc_rows(&vcs);
    assert!(rows.is_empty(), "{name}: {rows:#?}");
}

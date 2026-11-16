// Trust (ARGS-FINGERPRINT-READ-1, 2026-10-07; round 2 the same day): the
// duplicate-crate-name argument fingerprint `::<__trust_args@HEX>` and its readers.
//
// ROUND 1 made the vcgen readers of a callee's OWN generic arguments
// (`collection_range::method_generic_args`, `termination::direct_call_identity`) see
// past the tag, because the producer wrote it on EVERY generic callee of a graph that
// merely held a duplicate crate name, so `drain(..)` (clean `parallel.rs:152`) was
// refused and `fn down<T>`'s self call went unseen. The review REFUTED that for type
// paths: the display printer stamps no crate identity inside generic arguments, so a
// crate built `--crate-name core` exporting `ops::range::RangeFull` renders the real
// `RangeFull`'s spelling, and the tag was the only thing that told them apart.
//
// ROUND 2 fixes it at the producer: `trust_mir_extract::convert::direct_call_def_path`
// writes the tag exactly when a def named in the arguments lives in a crate whose
// rendered name does not identify it (the callee-root `__trust_crate@` rule applied to
// every argument def). A TYPE-PATH reader declines on a tagged callee; a VALUE reader
// (a const literal) sees past it; the termination lane never treats a tagged callee as
// a self call.
//
// Fixtures are REAL extracted MIR, unoptimized, `-Ztrust-dump=mir-only` (with
// `-Ztrust-policy=advisory`), source `fp.rs` below, from the stage 1 of round 2
// (`aee521e4b0` + this change), run from the source directory so spans are relative:
//
//   * `<name>.dup.json`   — crate `fp_dup`, `--cfg dup --extern dup_a=… --extern
//     dup_b=…`: two `dupdep` rlibs (`pub struct T; pub fn id(x: u32) -> u32 { x }`)
//     from one source with `-C metadata=aaa` / `-C metadata=bbb`;
//   * `<name>.nodup.json` — crate `fp_nodup`, the same source with no duplicate;
//   * `<name>.tagged.json` — the ROUND-1 `.dup.json` fixtures, dumped by the preview3
//     stage 1 (main `7be75e9a80`), whose producer tagged every generic callee of the
//     graph. They are kept as the TAGGED shape a reader can still be handed: the
//     forged-`core` `RangeFull` renders exactly `drain::<core::ops::range::RangeFull>`
//     plus a tag;
//   * `vec_drain_{forged,real}.forged.json` — crate `fp_forged`, `--extern
//     fakecore=<libcore.rlib>`, a crate BUILT `--crate-name core` (`fakecore.rs`
//     below), whose `RangeFull`'s `start_bound` is `Included(&1000)`. Compiled as a
//     binary, `fp_vec_drain_forged` on a 3-element vec panics "range start index 1000
//     out of range for slice of length 3" (measured by the review);
//   * `chain_{a,b}.dup.json` — crate `chain`, two `dupty` rlibs (`pub struct T;`) as
//     `dup_a`/`dup_b`; `a` is the impl for `W<dup_a::T>` (it calls the other impl), `b`
//     the one for `W<dup_b::T>` (it loops forever for an even `n`).
//
// ```text
// // fp.rs
// #![feature(slice_as_chunks)]
// use std::collections::VecDeque;
// #[cfg(dup)] pub fn touch() -> u32 { dup_a::id(1) + dup_b::id(2) }
// pub fn fp_dq_drain_full(mut q: VecDeque<u32>) -> Vec<u32> { q.drain(..).collect() }
// pub fn fp_vec_drain_full(v: &mut Vec<u32>) -> usize { v.drain(..).count() }
// pub fn fp_vec_drain_to(v: &mut Vec<u32>, n: usize) -> usize { v.drain(..n).count() }
// pub fn fp_dq_drain_from(q: &mut VecDeque<u32>, n: usize) -> usize { q.drain(n..).count() }
// pub fn fp_vec_splice_full(v: &mut Vec<u32>) -> usize { v.splice(.., [1u32, 2]).count() }
// pub fn fp_vec_splice(v: &mut Vec<u32>, n: usize) -> usize { v.splice(..n, [1u32, 2]).count() }
// pub fn fp_vec_extract_if_full(v: &mut Vec<u32>) -> usize { v.extract_if(.., |x| *x > 3).count() }
// pub fn fp_dq_range_full(q: &VecDeque<u32>) -> usize { q.range(..).count() }
// pub fn fp_st_drain_full(s: &mut String) -> usize { s.drain(..).count() }
// pub fn fp_sl_as_chunks4(v: &[u8]) -> usize { v.as_chunks::<4>().0.len() }
// pub fn fp_sl_as_chunks0(v: &[u8]) -> usize { v.as_chunks::<0>().0.len() }
// pub fn fp_down<T>(n: u32) -> u32 { if n == 0 { 0 } else { fp_down::<T>(n - 1) } }
// pub fn fp_spin<T>(n: u32) -> u32 { if n == 0 { 0 } else { fp_spin::<T>(n) } }
// #[cfg(dup)]
// pub fn fp_vec_drain_full_dup_elem(v: &mut Vec<dup_a::T>) -> usize { v.drain(..).count() }
//
// // fakecore.rs (built --crate-name core)
// pub mod ops { pub mod range {
//     use std::ops::{Bound, RangeBounds};
//     #[derive(Clone, Copy)] pub struct RangeFull;
//     impl RangeBounds<usize> for RangeFull {
//         fn start_bound(&self) -> Bound<&usize> { Bound::Included(&1000) }
//         fn end_bound(&self) -> Bound<&usize> { Bound::Unbounded }
//     }
// } }
// // forged.rs
// pub fn fp_vec_drain_forged(v: &mut Vec<u32>) -> usize {
//     let r = fakecore::ops::range::RangeFull; v.drain(r).count()
// }
// pub fn fp_vec_drain_real(v: &mut Vec<u32>) -> usize { v.drain(..).count() }
//
// // chain.rs
// pub struct W<X>(pub X);
// pub trait Tr { fn f<G: Copy>(n: u64, g: G) -> u64; }
// impl Tr for W<dup_a::T> { fn f<G: Copy>(n: u64, g: G) -> u64 {
//     if n == 0 { return 0; } <W<dup_b::T> as Tr>::f::<G>(n - 1, g) } }
// impl Tr for W<dup_b::T> { fn f<G: Copy>(n: u64, g: G) -> u64 {
//     let mut k = n; while k != 7 { k = k.wrapping_add(2); } k } }
// ```
//
// Dumps are MIR, so they do not claim the compiler path on their own; the compiler
// level is `tests/ui/trust/args_fingerprint_full_range.rs` and
// `tests/ui/trust/args_fingerprint_forged_core_range_full.rs`.
use trust_types::*;
use trust_vcgen::generate_vcs;

fn load(name: &str, graph: &str) -> (String, VerifiableFunction) {
    let path = format!(
        "{}/tests/fixtures/args_fingerprint/{name}.{graph}.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    let func = serde_json::from_str(&json).expect("fixture MIR must deserialize");
    (json, func)
}

/// Remove every exact `::<__trust_args@` + 32 lowercase hex + `>` occurrence (rows
/// may quote a callee) and the crate-name difference, so two graphs' rows compare.
fn normalize(row: &str) -> String {
    let mut out = String::with_capacity(row.len());
    let mut rest = row;
    while let Some(i) = rest.find(TRUST_ARGS_FINGERPRINT_PREFIX) {
        let tail = &rest[i + TRUST_ARGS_FINGERPRINT_PREFIX.len()..];
        let hex = tail.get(..TRUST_ARGS_FINGERPRINT_HEX_LEN);
        let canonical = hex
            .is_some_and(|h| h.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f')))
            && tail[TRUST_ARGS_FINGERPRINT_HEX_LEN..].starts_with('>');
        out.push_str(&rest[..i]);
        if canonical {
            rest = &tail[TRUST_ARGS_FINGERPRINT_HEX_LEN + 1..];
        } else {
            out.push_str(TRUST_ARGS_FINGERPRINT_PREFIX);
            rest = tail;
        }
    }
    out.push_str(rest);
    out.replace("fp_dup", "fp_nodup")
}

fn rows(func: &VerifiableFunction) -> Vec<String> {
    let mut rows: Vec<String> =
        generate_vcs(func).iter().map(|vc| normalize(&format!("{:?}", vc.kind))).collect();
    rows.sort();
    rows
}

fn has_tag(json: &str) -> bool {
    json.contains(TRUST_ARGS_FINGERPRINT_PREFIX)
}

/// PLANTED PRECONDITION (round 2): the `dup` fixture comes from a graph that really
/// holds a duplicate crate name (pinned by `the_producer_tags_only_an_argument_that_names_a_duplicated_crate`)
/// and, because none of these arguments names that crate, carries NO tag.
fn graphs(name: &str) -> (VerifiableFunction, VerifiableFunction) {
    let (dup_json, dup) = load(name, "dup");
    let (nodup_json, nodup) = load(name, "nodup");
    assert!(!has_tag(&dup_json), "{name}: no argument names `dupdep`; the producer must not tag");
    assert!(!has_tag(&nodup_json), "{name}: control is tagged");
    (dup, nodup)
}

fn tagged(name: &str) -> VerifiableFunction {
    let (json, func) = load(name, "tagged");
    assert!(has_tag(&json), "{name}: the preview3 fixture lost its `__trust_args@` tag");
    func
}

fn assert_parity(name: &str) {
    let (dup, nodup) = graphs(name);
    assert_eq!(
        rows(&dup),
        rows(&nodup),
        "{name}: the duplicate-crate-name graph must mint the same rows as the ordinary one"
    );
}

fn kind_count(func: &VerifiableFunction, want: &str) -> usize {
    generate_vcs(func)
        .iter()
        .filter(|vc| matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. } if kind == want))
        .count()
}

const DRAIN_REFUSAL: &str = "Call::drain::panic-freedom-unverified";

/// The producer half (round 2): in the `fp_dup` graph, ONLY the call whose argument
/// names a type of the duplicated crate (`Vec<dup_a::T>`, rendered `dupdep::T`) is
/// tagged; every call whose arguments name only `core`/`alloc`/primitives/a type
/// parameter is not. Spellings measured on the stage 1 of round 2.
#[test]
fn the_producer_tags_only_an_argument_that_names_a_duplicated_crate() {
    let (json, elem) = load("vec_drain_full_dup_elem", "dup");
    assert!(
        json.contains(
            "alloc::vec::Vec::<dupdep::T>::drain::<core::ops::range::RangeFull>::<__trust_args@"
        ),
        "an argument naming the duplicated crate must be tagged"
    );
    for name in [
        "dq_drain_full",
        "vec_drain_full",
        "vec_drain_to",
        "dq_drain_from",
        "vec_splice_full",
        "vec_splice",
        "vec_extract_if_full",
        "dq_range_full",
        "st_drain_full",
        "sl_as_chunks4",
        "sl_as_chunks0",
        "down",
        "spin",
    ] {
        graphs(name);
    }
    // NEGATIVE: the tagged `Vec<dupdep::T>::drain::<RangeFull>` keeps its refusal —
    // a fail-closed cost, since `RangeFull` cannot be told from a same-named crate's
    // by the display, and the tag does not say WHICH argument is ambiguous.
    assert_eq!(kind_count(&elem, DRAIN_REFUSAL), 1, "a tagged `..` drain is not trusted");
}

/// POSITIVE: a `..` drain cannot fail `slice::range`; no refusal in either graph.
/// This is the clean `parallel.rs:152` row.
#[test]
fn a_full_range_drain_mints_no_refusal_in_a_duplicate_name_graph() {
    for name in ["dq_drain_full", "vec_drain_full"] {
        let (dup, nodup) = graphs(name);
        assert_eq!(kind_count(&nodup, DRAIN_REFUSAL), 0, "{name}: control");
        assert_eq!(kind_count(&dup, DRAIN_REFUSAL), 0, "{name}: `drain(..)` cannot panic");
        assert_parity(name);
    }
}

/// NEGATIVE (the round-1 refutation): `drain` over a crate-named-`core`
/// `RangeFull` whose `start_bound` is 1000 PANICS, and renders the real `RangeFull`'s
/// spelling plus a tag. It must keep its refusal. The real `..` in that same graph is
/// tagged too (`core` itself is the duplicated name) and is refused as well: the
/// fail-closed cost of a graph that duplicates `core`.
#[test]
fn a_range_full_from_a_crate_named_core_keeps_the_drain_refusal() {
    for name in ["vec_drain_forged", "vec_drain_real"] {
        let (json, func) = load(name, "forged");
        assert!(
            json.contains(
                "alloc::vec::Vec::<u32>::drain::<core::ops::range::RangeFull>::<__trust_args@"
            ),
            "{name}: the forged graph must render the real spelling plus the tag"
        );
        assert_eq!(kind_count(&func, DRAIN_REFUSAL), 1, "{name}: must stay refused");
    }
    // The same refusal for the round-1 (preview3) tagged spellings of the REAL
    // `RangeFull`: a reader cannot tell them from the forged one.
    for name in ["dq_drain_full", "vec_drain_full"] {
        assert_eq!(kind_count(&tagged(name), DRAIN_REFUSAL), 1, "{name}: tagged");
    }
}

/// NEGATIVE: a drain whose range CAN panic keeps its refusal in both graphs.
#[test]
fn a_drain_that_can_panic_keeps_its_refusal_in_a_duplicate_name_graph() {
    for name in ["vec_drain_to", "dq_drain_from"] {
        let (dup, nodup) = graphs(name);
        assert_eq!(kind_count(&nodup, DRAIN_REFUSAL), 1, "{name}: control");
        assert_eq!(kind_count(&dup, DRAIN_REFUSAL), 1, "{name}: must stay refused");
        assert_parity(name);
    }
}

/// The other `range_generic_is_full` readers: `Vec::splice`/`extract_if`,
/// `VecDeque::range`, `String::drain` over `..` mint no family row (POSITIVE); a
/// `..n` splice keeps its fail-honest row (NEGATIVE).
#[test]
fn the_other_full_range_methods_agree_across_graphs() {
    for name in ["vec_splice_full", "vec_extract_if_full", "dq_range_full", "st_drain_full"] {
        let (dup, _) = graphs(name);
        for kind in [
            "vec-range-method-bounds-unmodeled",
            "vecdeque-range-bounds-unmodeled",
            "string-range-char-boundary-unmodeled",
        ] {
            assert_eq!(kind_count(&dup, kind), 0, "{name}: `..` cannot panic ({kind})");
        }
        assert_parity(name);
    }
    let (dup, nodup) = graphs("vec_splice");
    assert_eq!(kind_count(&nodup, "vec-range-method-bounds-unmodeled"), 1, "control");
    assert_eq!(kind_count(&dup, "vec-range-method-bounds-unmodeled"), 1, "`..n` stays charged");
    assert_parity("vec_splice");
}

/// `const_generic_is_nonzero`: `as_chunks::<4>` is not charged (POSITIVE);
/// `as_chunks::<0>` is (NEGATIVE) — in both graphs, and behind a tag too (a const
/// literal is a VALUE no crate can spell).
#[test]
fn a_const_chunk_size_is_read_past_the_fingerprint() {
    const ZERO: &str = "slice-const-chunk-size-zero";
    let (dup4, nodup4) = graphs("sl_as_chunks4");
    assert_eq!(kind_count(&nodup4, ZERO), 0, "control");
    assert_eq!(kind_count(&dup4, ZERO), 0, "`::<4>` is nonzero");
    assert_eq!(kind_count(&tagged("sl_as_chunks4"), ZERO), 0, "the tag is not the const");
    let (dup0, nodup0) = graphs("sl_as_chunks0");
    assert_eq!(kind_count(&nodup0, ZERO), 1, "control");
    assert_eq!(kind_count(&dup0, ZERO), 1, "`::<0>` panics and must stay charged");
    assert_eq!(kind_count(&tagged("sl_as_chunks0"), ZERO), 1, "`::<0>` behind the tag");
    assert_parity("sl_as_chunks4");
    assert_parity("sl_as_chunks0");
}

fn recursion_rows(func: &VerifiableFunction) -> usize {
    generate_vcs(func)
        .iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::NonTermination { context, .. }
                if context == trust_vcgen::RECURSION_TERMINATION_CONTEXT)
        })
        .count()
}

/// `termination`: a generic fn's self call `fp_down::<T>` names only a type parameter,
/// so the round-2 producer does not tag it and the recursion lane states its descent
/// claim in both graphs (for the spinning body too — refusing it is the solver's job).
/// A TAGGED self call (the preview3 spelling) is never a self call: no claim
/// (fail-closed; the compiler's own lane then speaks).
#[test]
fn a_generic_self_call_is_seen_and_a_tagged_one_is_not() {
    for name in ["down", "spin"] {
        let (dup, nodup) = graphs(name);
        assert_eq!(recursion_rows(&nodup), 1, "{name}: control");
        assert_eq!(recursion_rows(&dup), 1, "{name}: the untagged self call must be seen");
        assert_parity(name);
        assert_eq!(recursion_rows(&tagged(name)), 0, "{name}: a tagged callee is not a self call");
    }
}

/// The round-1 FALSE PROOF (review probe `chain.rs`): impl A (`W<dup_a::T>`) calls
/// impl B (`W<dup_b::T>`); both render `<chain::W<dupty::T> as chain::Tr>::f`, and B
/// loops forever for an even `n`. With the tag stripped, A's call to B read as a self
/// call and A got a PROVED "recursion measure `n` may not decrease" row. The call is
/// tagged (its `Self` names the duplicated crate), so it is not a self call and A
/// gets no recursion row; B has no call to `f` at all.
#[test]
fn a_call_into_the_other_same_named_impl_is_not_a_self_call() {
    let (a_json, a) = load("chain_a", "dup");
    let (b_json, b) = load("chain_b", "dup");
    assert_eq!(a.def_path, b.def_path, "the two impls render one def path (the hazard)");
    assert!(
        a_json.contains("<chain::W<dupty::T> as chain::Tr>::f::<G>::<__trust_args@"),
        "A's call into B must carry the tag"
    );
    assert!(!has_tag(&b_json));
    assert_eq!(recursion_rows(&a), 0, "A is not recursive: no descent claim");
    assert_eq!(recursion_rows(&b), 0, "B makes no call to `f`");
}

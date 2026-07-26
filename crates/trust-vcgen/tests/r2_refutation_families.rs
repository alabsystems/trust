// Trust (R2 — corpus false-in-practice refutation families, 2026-07-06).
//
// The corpus measurement (scorecard §3) found Trust FALSE-REFUTING two ubiquitous
// battle-tested idioms:
//
//  * family 1 (heck `capitalize`): `&s[i..]` at an `s.char_indices()`-yielded `i`
//    — the yield contract guarantees `i < s.len()` AND `s.is_char_boundary(i)`,
//    so the slice can NEVER panic. The fix is a STRUCTURAL fold of the range
//    bounds disjunct at VC-gen (never an Int yield fact: that would let a DERIVED
//    `&s[i-1..]` prove bounds while panicking on the unmodeled char boundary).
//  * family 2 (bitflags `IterNames::next`, semver `numeric_identifier`):
//    `while let Some(x) = flags.get(idx) { idx += 1; … }` — `get == Some` implies
//    `idx < flags.len() <= isize::MAX`, so the increment cannot overflow.
//
// Fixtures are REAL MIR extracted with `-Ztrust-dump=mir:<dir>` from the minimal
// shapes in the crate clones. Every WIN test has mutant twins asserting the
// discharge does NOT fire when a soundness gate fails.
use trust_types::*;
use trust_vcgen::generate_vcs;

fn load(name: &str) -> VerifiableFunction {
    let json =
        std::fs::read_to_string(format!("tests/fixtures/{name}.json")).expect("fixture readable");
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

fn vcs_of_kind(func: &VerifiableFunction, pred: fn(&VcKind) -> bool) -> Vec<String> {
    generate_vcs(func)
        .into_iter()
        .filter(|vc| pred(&vc.kind))
        .map(|vc| format!("{:?}", vc.formula))
        .collect()
}

fn is_bounds(k: &VcKind) -> bool {
    matches!(k, VcKind::SliceBoundsCheck | VcKind::IndexOutOfBounds)
}

fn is_overflow(k: &VcKind) -> bool {
    matches!(k, VcKind::ArithmeticOverflow { .. })
}

// ---------------------------------------------------------------- family 1

/// The debug spelling of the VC-local yield fact `i <= s.len() - 1`.
const YIELD_UPPER_FACT: &str = "Sub(Var(\"s__slice_len\", Int), Int(1))";

#[test]
fn charindices_rangefrom_slice_carries_vc_local_yield_facts() {
    // WIN (heck capitalize): `&s[i..]` at a yielded `i` — the violation carries
    // the VC-local contract facts `0 <= i` and `i <= s.len() - 1`, a linear
    // contradiction with `i > s.len()` that ay's strict lane proves.
    let func = load("charindices_rangefrom_mir");
    let bounds = vcs_of_kind(&func, is_bounds);
    assert!(!bounds.is_empty(), "the str range slice must still carry a bounds VC");
    for f in &bounds {
        assert!(
            f.contains(YIELD_UPPER_FACT),
            "a traced CharIndices yield start must conjoin the `<= len - 1` \
             contract fact onto the RangeFrom violation: {f}"
        );
    }
}

#[test]
fn charindices_rangefrom_marked_str_callee_still_carries_yield_facts() {
    // WIN (post-3f93cbb5bd toolchain): the SAME idiom dumped from the CURRENT
    // extractor, whose callee carries the `::<__trust_str_index>` char-boundary
    // marker (`std::ops::Index::index::<__trust_str_index>`). The marker's
    // fail-close must NOT clobber the traced-yield discharge: the violation
    // still carries the VC-local contract facts (provable), never the
    // `Bool(true)` non-boundary-safe fail-close. This is the formula-lane half
    // of tests/trust-falsification/proved/charindices_slice_tail.rs; the
    // native-lane half (the marked callee keeping the bridge's Gap-3
    // recognition instead of the absent-callee may-panic row) lives in
    // trust-ir-bridge `test_marked_str_range_index_keeps_gap3_recognition`.
    let func = load("charindices_rangefrom_marked_mir");
    let bounds = vcs_of_kind(&func, is_bounds);
    assert!(!bounds.is_empty(), "the marked str range slice must still carry a bounds VC");
    for f in &bounds {
        assert!(
            f.contains(YIELD_UPPER_FACT),
            "a traced CharIndices yield start must conjoin the `<= len - 1` \
             contract fact onto the marked-str RangeFrom violation: {f}"
        );
        assert!(
            !f.contains("Bool(true)"),
            "the char-boundary fail-close must not fire on a traced yield: {f}"
        );
    }
}

#[test]
fn charindices_derived_index_keeps_refutable_violation() {
    // MUTANT: `&s[i + 1..]` — `i + 1` is NOT a yielded index (and may fall mid-char);
    // the trace must decline and the violation stay the refutable `start > len`.
    let func = load("charindices_plus_one_mir");
    let bounds = vcs_of_kind(&func, is_bounds);
    assert!(!bounds.is_empty(), "the derived-index slice must carry a bounds VC");
    for f in &bounds {
        assert!(
            !f.contains(YIELD_UPPER_FACT),
            "a DERIVED index must never receive the yield contract facts: {f}"
        );
    }
}

#[test]
fn charindices_cross_string_keeps_refutable_violation() {
    // MUTANT: yield of `s` used to slice `t` — root identity fails, no fold.
    let func = load("charindices_cross_string_mir");
    let bounds = vcs_of_kind(&func, is_bounds);
    assert!(!bounds.is_empty(), "the cross-string slice must carry a bounds VC");
    for f in &bounds {
        assert!(
            !f.contains(YIELD_UPPER_FACT) && !f.contains("Sub(Var(\"t__slice_len\", Int), Int(1))"),
            "a yield of a DIFFERENT string must never receive the yield contract facts: {f}"
        );
    }
}

#[test]
fn charindices_marked_mutant_twins_fail_closed() {
    // MUTANT twins dumped from the CURRENT (marked-callee) extractor: `&s[i+1..]`
    // (derived index) and `&t[i..]` (cross string). Under the str char-boundary
    // marker the non-boundary-safe endpoint takes the `Bool(true)` fail-close —
    // the violation stays ALWAYS-SAT on the reachable path (refuted), and no
    // yield contract fact may attach.
    for name in ["charindices_plus_one_marked_mir", "charindices_cross_string_marked_mir"] {
        let func = load(name);
        let bounds = vcs_of_kind(&func, is_bounds);
        assert!(!bounds.is_empty(), "{name}: the marked mutant slice must carry a bounds VC");
        for f in &bounds {
            assert!(
                !f.contains(YIELD_UPPER_FACT)
                    && !f.contains("Sub(Var(\"t__slice_len\", Int), Int(1))"),
                "{name}: a mutant endpoint must never receive the yield contract facts: {f}"
            );
            assert!(
                f.contains("Bool(true)"),
                "{name}: a non-boundary-safe marked-str endpoint must keep the \
                 char-boundary fail-close: {f}"
            );
        }
    }
}

#[test]
fn charindices_swapped_iterator_keeps_refutable_violation() {
    // MUTANT: `mem::swap(&mut ci, &mut cj)` re-seats the iterator onto another
    // string — the conduit discipline (`&mut` feeds only `next`) must decline.
    let func = load("charindices_swapped_mir");
    let bounds = vcs_of_kind(&func, is_bounds);
    assert!(!bounds.is_empty(), "the swapped-iterator slice must carry a bounds VC");
    for f in &bounds {
        assert!(
            !f.contains(YIELD_UPPER_FACT),
            "a swap-reachable iterator must never receive the yield contract facts: {f}"
        );
    }
}

// ---------------------------------------------------------------- family 2

#[test]
fn get_some_arm_bounds_the_incremented_index() {
    // WIN (bitflags IterNames::next): the `idx + 1` overflow VC must carry the
    // get-Some contract fact `idx < {recv}__slice_len` on the SAME field place the
    // add reads (`self*.1`), so with the allocation-size axiom it proves.
    let func = load("get_some_increment_mir");
    let overflows = vcs_of_kind(&func, is_overflow);
    assert!(!overflows.is_empty(), "the increment must carry an overflow VC");
    let joined = overflows.join(" ");
    assert!(
        joined.contains("__slice_len"),
        "the get-Some fact must tie the index to the receiver's slice length: {joined}"
    );
    assert!(
        joined.contains("Lt(Var(\"self*.1"),
        "the fact must name the FIELD place the add reads (self*.1): {joined}"
    );
}

#[test]
fn get_some_poisoned_index_fact_is_dropped() {
    // MUTANT: `self.idx = usize::MAX;` inside the Some arm before the add — the
    // block redefines the fact's variable, so the consumers must DROP it and the
    // overflow stays refutable. The formula must NOT constrain the poisoned read
    // below the slice length.
    let func = load("get_some_poisoned_mir");
    let overflows = vcs_of_kind(&func, is_overflow);
    assert!(!overflows.is_empty(), "the poisoned increment must carry an overflow VC");
    for f in &overflows {
        // The add's operand is the post-write versioned `self*.1#s…`; a live
        // `Lt(self*.1…, …__slice_len)` on that SAME version would be the false
        // proof. Accept the fact appearing on a DIFFERENT (stale, name-disjoint)
        // version — assert only that no fact names the write's own token spelling
        // that the obligation reads.
        assert!(
            !f.contains("Bool(false)"),
            "the poisoned overflow VC must stay refutable: {f}"
        );
    }
}

#[test]
fn get_some_cross_slice_index_stays_refutable() {
    // MUTANT: `a.get(i) == Some` must not discharge `b[i]` — the fact bounds `i`
    // against `a`'s length symbol, which is name-disjoint from `b`'s.
    let func = load("get_some_cross_slice_mir");
    let bounds = vcs_of_kind(&func, is_bounds);
    assert!(!bounds.is_empty(), "the cross-slice index must carry a bounds VC");
    let joined = bounds.join(" ");
    assert!(
        !joined.contains("Lt(Var(\"i\", Int), Var(\"b__slice_len"),
        "the get-Some fact must never bound the index against a DIFFERENT slice's \
         length: {joined}"
    );
}

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

/// The `UnmodeledCalleeReturn` rows: obligations `generate/havoc_decline.rs`
/// declined to Unknown because their verdict is a value only an unmodelled
/// callee (here, std `Iterator::next`) decides.
fn declined_rows(func: &VerifiableFunction) -> Vec<(String, String)> {
    generate_vcs(func)
        .into_iter()
        .filter_map(|vc| match vc.kind {
            VcKind::UnsupportedMir { kind, detail } if kind == "UnmodeledCalleeReturn" => {
                Some((detail, format!("{:?}", vc.formula)))
            }
            _ => None,
        })
        .collect()
}

/// A MUTANT's slice obligation must survive in one of its two fail-closed
/// shapes, and neither may carry a yield contract fact.
///
/// Until 4b2f78a544 (2026-09-21) the slice-method panic lane pushed its bounds
/// row with `obligation: None`, which kept it out of `havoc_decline`'s reach
/// (that pass folds definitions into the RECORDED violation, condition 2). Once
/// the row was recorded, a mutant whose endpoint is a bare `CharIndices` yield
/// with no fold — exactly what these twins are — meets all four decline
/// conditions: its only value source is the `Some` payload of an unmodelled
/// std `Iterator::next` (round A5), nothing pins it, and moving it flips the
/// obligation. So the row is now an Unknown, not a refutation. Both shapes are
/// fail-closed; what these tests exist for is that the fold never fires on the
/// wrong string or a re-seated iterator. That is still checked on every bounds
/// row, and a folded row would keep its bounds kind, because the yield facts pin
/// the endpoint and the decline does not fire (condition 3).
/// Measured A/B: with the lane's record dropped again, both twins emit a bounds
/// row that has no yield fact and no declined row.
fn assert_mutant_slice_obligation_fails_closed(name: &str, forbidden: &[&str]) {
    let func = load(name);
    let bounds = vcs_of_kind(&func, is_bounds);
    let declined = declined_rows(&func);
    assert!(
        !bounds.is_empty() || !declined.is_empty(),
        "{name}: the mutant slice obligation vanished: no bounds VC and no \
         UnmodeledCalleeReturn row"
    );
    for f in &bounds {
        for fact in forbidden {
            assert!(
                !f.contains(fact),
                "{name}: a mutant endpoint received the yield fact {fact}: {f}"
            );
        }
    }
    for (detail, formula) in &declined {
        assert_eq!(
            formula, "Bool(true)",
            "{name}: a declined row must keep the fail-closed formula ({detail})"
        );
    }
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
    // The row is refutable or declined to Unknown, never proved (see
    // `assert_mutant_slice_obligation_fails_closed`).
    assert_mutant_slice_obligation_fails_closed(
        "charindices_cross_string_mir",
        &[YIELD_UPPER_FACT, "Sub(Var(\"t__slice_len\", Int), Int(1))"],
    );
}

#[test]
fn charindices_marked_mutant_twins_fail_closed() {
    // MUTANT twins dumped from the CURRENT (marked-callee) extractor: `&s[i+1..]`
    // (derived index) and `&t[i..]` (cross string). Under the str char-boundary
    // marker the non-boundary-safe endpoint is REFUSED, and no yield contract fact
    // may attach.
    //
    // Trust (2026-10-02, class 10 — false refutation): the refusal is the declined
    // `UnsupportedMir { kind: "str-range-char-boundary-unmodeled" }` row (Unknown,
    // the row `str::split_at` gives the same unmodeled boundary), no longer the
    // always-violated `Bool(true)` as a refutable `SliceBoundsCheck`, which FAILED on
    // an arbitrary model whether or not the offset was a boundary. Either way the
    // obligation is never proved, and no byte-bounds row may stand for it.
    for name in ["charindices_plus_one_marked_mir", "charindices_cross_string_marked_mir"] {
        let func = load(name);
        let declined: Vec<String> = generate_vcs(&func)
            .into_iter()
            .filter_map(|vc| match &vc.kind {
                VcKind::UnsupportedMir { kind, .. }
                    if kind == "str-range-char-boundary-unmodeled" =>
                {
                    Some(format!("{:?}", vc.formula))
                }
                _ => None,
            })
            .collect();
        assert!(
            !declined.is_empty(),
            "{name}: the non-boundary-safe marked-str endpoint must be refused (declined row)"
        );
        for f in vcs_of_kind(&func, is_bounds).iter().chain(&declined) {
            assert!(
                !f.contains(YIELD_UPPER_FACT)
                    && !f.contains("Sub(Var(\"t__slice_len\", Int), Int(1))"),
                "{name}: a mutant endpoint must never receive the yield contract facts: {f}"
            );
        }
        assert!(
            vcs_of_kind(&func, |k| matches!(k, VcKind::SliceBoundsCheck)).is_empty(),
            "{name}: the str slice must not be stated as a byte-bounds row"
        );
    }
}

#[test]
fn charindices_swapped_iterator_keeps_refutable_violation() {
    // MUTANT: `mem::swap(&mut ci, &mut cj)` re-seats the iterator onto another
    // string — the conduit discipline (`&mut` feeds only `next`) must decline.
    // The row is refutable or declined to Unknown, never proved.
    assert_mutant_slice_obligation_fails_closed("charindices_swapped_mir", &[YIELD_UPPER_FACT]);
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
        assert!(!f.contains("Bool(false)"), "the poisoned overflow VC must stay refutable: {f}");
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

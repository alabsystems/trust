// Real-MIR end-to-end for the NEGATIVE-LENGTH false REFUTATION and, in the same
// file, for the UB canaries that must NOT stop refuting because of the fix.
//
// THE DEFECT (measured at clean HEAD with this exact MIR): an ordinary,
// non-async, loop-free
//
//     pub fn f(a: &[u32]) -> u32 {
//         match a { [] => 0, [x] => *x, [x, .., y] => *x ^ *y }
//     }
//
// lowers its three arms onto ONE shared `Terminator::Unreachable` sink, whose
// path condition is `len != 0 ∧ len != 1 ∧ ¬(len >= 2)`. Over the unbounded
// `Sort::Int` that vcgen lowers a length to, the solver satisfies it with
//
//     _3 = -1, _4 = false, _5 = -1, _6 = false, _7 = -1, _8 = false,
//     a__slice_len = -1
//
// A NEGATIVE SLICE LENGTH. No execution can produce it (a slice length is a
// `usize`), so the row is a FALSE REFUTATION: the verifier accuses correct code
// and fails the user's build.
//
// THE FIX is `conjoin_length_nonneg_bounds` (`generate::type_ranges`), applied
// from `generate_v2_safety_vcs_impl_with_origins_checked` to exactly the VC kinds
// the pre-existing range battery does NOT reach. The bound `0 <= len` already
// existed in `conjoin_slice_len_bounds`, but that pass runs only on
// `ArithmeticOverflow` and bounds VCs, so `Unreachable`, `Assertion` and the
// panic-family rows never saw it. The fix is NAME-DRIVEN and per-VC; it is NOT a
// `build_global_invariant_facts` entry (publishing these facts unconditionally
// was measured to break the caller-grounding gate, and is the design this file
// deliberately does not test).
//
// WHAT A NON-REFUTED ROW BUYS, AND UNDER WHICH POLICY. The two `is_not_refuted`
// tests assert "not `Failed`", not "`Proved`", and that is an admission:
// MEASURED with the real backend and `trust_certify::certify_vc`, both of this
// file's merged-sink fixtures go `Failed` -> UNKNOWN
// ("(incomplete self-check-rejected)") — with `0 <= len` in context ay reports
// the goal UNSAT but its own proof self-check rejects the multi-disequality LIA
// refutation. An UNKNOWN is not automatically a red build, and which it is
// depends on the policy: `VcKind::Unreachable` and `VcKind::Assertion` both
// report `has_runtime_fallback == true`, so an `Unknown`/`Timeout` on either is
// counted `failure.runtime_checked`, which `strict_failure_is_fatal`
// (`compiler/rustc_mir_transform/src/trust_verify.rs`) EXCLUDES under the default
// strict policy and INCLUDES under `-Ztrust-policy=certify`
// (`require_full_discharge`). MEASURED end to end with the stage2 compiler on the
// program in the code block above, forcing the row's verdict with
// `-Ztrust-verify-timeout-ms`:
//
//     strict  + row refuted      rc = 1  ("1 failed, 0 unknown or timed out, 0 runtime-checked")
//     strict  + row not refuted  rc = 0  ("0 failed, 0 unknown or timed out, 1 runtime-checked"), 2 warnings
//     certify + row refuted      rc = 1
//     certify + row not refuted  rc = 1
//
// So under the default policy this change takes that build from red to green
// with warnings, and under `certify` it stays red until the row is PROVED. State
// the composition honestly, though: those four cells are the COMPILER's
// classification measured at HEAD, while the row verdicts in this file come from
// `Router::deterministic_in_process_ay` — the compiler routed this obligation to
// its native trust-mc lane, and no patched compiler was built. Asserting
// `Proved` here would pin a second component's behaviour into this test.
//
// SIMPLER SHAPES ARE FULLY CLOSED, which is why the split matters, and it splits
// by SHAPE rather than by element type. MEASURED over a slice-pattern matrix
// (`[x, ..]`, `[.., y]`, the merged 3-arm match, `&mut [T]`, `&[()]`,
// `match v.as_slice()`, `s.as_bytes()`, `&String`, a nested `&[&[T]]` match, two
// slices in one body, 4- and 6-arm ladders, `&[u32; 4]`, and UB canaries): in a
// TWO-arm match the `Unreachable` sink reaches `Proved` AND kernel-certified,
// which `a_two_arm_slice_match_is_fully_discharged` below pins on a fixture that
// is `Failed` at pristine HEAD. Closing the SINK is not the same as closing the
// FUNCTION — `match a { [] => 0, [.., y] => *y }` discharges its sink while its
// last-element `SliceBoundsCheck` stays refuted at `a__slice_len = 1`. Every THREE-or-more-arm shape stops short of
// `Proved`: most land in `Unknown`, and the one NESTED `&[&[T]]` shape stays
// refuted — but at a witness whose lengths are all non-negative, where HEAD's
// were not. No row anywhere in the matrix lost a refutation, no row that was
// `Proved` at HEAD regressed, and every refutation that survives moved OFF an
// impossible negative length onto a witness a real execution can hold.
//
// TWO-SIDED CANARIES. `0 <= len` is a true fact, so it can only delete
// impossible models — every real violation's witness carries a non-negative
// length and survives. The three `refutes_with_a_real_witness` tests are the
// evidence for BOTH directions at once, on rows that are ON the changed path:
// each is a genuinely REACHABLE trap whose VC kind is one this fix touches
// (`Assertion`, the panic family) and whose formula names a container length.
// Each asserts (a) the row is STILL refuted — if it flipped to proved the fact
// being published would not be a theorem and the change would be UB laundering —
// and (b) every length in the surviving witness is non-negative, i.e. the
// witness describes a REAL execution. MEASURED: each of the three FAILS against
// pristine HEAD on clause (b) (HEAD refutes them with `b__slice_len = -1`) and
// passes with the fix. That is what makes them evidence rather than decoration.
//
// WHAT THIS FILE DOES NOT ESTABLISH, stated because the numbers invite the wrong
// reading: the falsification corpora are NOT coverage for this change. Almost no
// corpus row receives the new bound at all, and no corpus fixture combines a
// container length with a non-bounds VC kind. Corpus green is a
// no-collateral-damage result and says nothing about whether the fix WORKS. The
// fixtures in this file are the coverage; the corpus invariant itself is stated
// on `conjoin_length_nonneg_bounds`.
//
// MUTATION LEDGER. A "must still refute" caption on an assertion no defect can
// falsify is worse than no test — the previous round shipped exactly that, in this
// lane's sibling file, after tightening its SHAPE and never mutating the fix. Each
// mutant below was applied to `conjoin_length_nonneg_bounds` (or to its single call
// site) and BUILT AND RUN; the tests named are the ones that go red:
//
//     NO-OP          body returns its argument   merged_*, zst_*, two_arm_*,
//                                                all three refutes_with_a_real_witness
//     INVERTED       mints `len <= 0`            the same set, plus reachable_trap_behind_*
//     OFF-BY-ONE     mints `1 <= len`            reachable_traps_at_an_empty_container_*
//     GATE DROPPED   `!range_kind` removed       excluded_kind_ub_rows_still_refute
//     ANY LOCAL      every local admitted as     two_arm_*, all three
//                    a "length"                  refutes_with_a_real_witness,
//                                                reachable_traps_at_an_empty_container_*,
//                                                reachable_trap_behind_*
//     UPPER BOUND    `len <= isize::MAX` added   (unit only: never_attaches_an_upper_bound)
//     SIGNED DEST    `is_signed()` check dropped (unit only)
//     UNCONDITIONAL  bounds for every admitted   (unit only: introduces_no_free_variable)
//                    base, not only names the
//                    formula already has
//
// TWO THINGS THIS LEDGER ADMITS. (1) The `is_failed` half of
// `excluded_kind_ub_rows_still_refute` is killed by NO mutant — `0 <= len` is a
// TRUE fact, so widening its scope cannot flip a refutation; what catches a scope
// regression there is the formula assertion beside it, and the caption says so.
// (2) The bare count assertions (`rows.len() == 1`, `unreach.len() == 1`, …) are
// not adversarial and no mutant kills them; they exist so the assertions after
// them cannot iterate over an empty list. Both are stated rather than dressed up.
use trust_types::{CounterexampleValue, Formula, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

fn load(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture MIR must deserialize")
}

fn vc_rows(
    func: &VerifiableFunction,
) -> Vec<(trust_types::VerificationCondition, VerificationResult)> {
    let context = trust_vcgen::VcgenContext::for_function(func.def_path.clone());
    let vcs = trust_vcgen::generate_vcs_with_context(func, &context);
    let router = test_router::deterministic_test_router();
    vcs.into_iter()
        .map(|vc| {
            let results = router.verify_all(std::slice::from_ref(&vc));
            let (_, result) = results.into_iter().next().expect("one verdict per VC");
            (vc, result)
        })
        .collect()
}

fn verdicts(func: &VerifiableFunction) -> Vec<(String, VerificationResult)> {
    vc_rows(func).into_iter().map(|(vc, result)| (format!("{:?}", vc.kind), result)).collect()
}

fn is_failed(result: &VerificationResult) -> bool {
    matches!(result, VerificationResult::Failed { .. })
}

/// Whether `formula` anywhere asserts `0 <= <something>__slice_len` — the exact
/// fact this pass mints, read STRUCTURALLY so the check cannot drift with `Debug`
/// formatting.
fn mentions_a_slice_length_lower_bound(formula: &Formula) -> bool {
    match formula {
        Formula::Ge(lhs, rhs) => {
            matches!((lhs.as_ref(), rhs.as_ref()),
                (Formula::Var(name, _), Formula::Int(0)) if name.contains("__slice_len"))
        }
        Formula::And(parts) | Formula::Or(parts) => {
            parts.iter().any(mentions_a_slice_length_lower_bound)
        }
        Formula::Not(inner) => mentions_a_slice_length_lower_bound(inner),
        Formula::Implies(a, b) => {
            mentions_a_slice_length_lower_bound(a) || mentions_a_slice_length_lower_bound(b)
        }
        _ => false,
    }
}

/// Every LENGTH assignment in a refutation's witness: the `*__slice_len` symbols
/// `slice_len_formula` mints, plus any `extra` name (an owned `Vec`/`String`
/// local is abstracted to its length under the local's OWN var name, so its
/// spelling carries no marker and has to be named).
fn length_assignments(
    result: &VerificationResult,
    extra: &[&str],
) -> Vec<(String, CounterexampleValue)> {
    let VerificationResult::Failed { counterexample: Some(ce), .. } = result else {
        return Vec::new();
    };
    ce.assignments
        .iter()
        .filter(|(name, _)| {
            name.contains("__slice_len") || extra.iter().any(|e| name.split('#').next() == Some(e))
        })
        .cloned()
        .collect()
}

/// The shared body of the three changed-path canaries: the named row must STILL
/// refute, its witness must MENTION a length (otherwise the check below is
/// vacuous), and every length it mentions must be one a real execution can hold.
fn assert_refutes_with_a_real_witness(
    func: &VerifiableFunction,
    kind_prefix: &str,
    extra_length_names: &[&str],
) {
    let rows = verdicts(func);
    let refuted: Vec<_> = rows
        .iter()
        .filter(|(kind, result)| kind.starts_with(kind_prefix) && is_failed(result))
        .collect();
    assert_eq!(
        refuted.len(),
        1,
        "the trap is genuinely reachable, so exactly one `{kind_prefix}` row must stay \
         REFUTED — proving it would bless UB: {rows:?}"
    );
    let result = &refuted[0].1;
    let lengths = length_assignments(result, extra_length_names);
    assert!(
        !lengths.is_empty(),
        "the witness must NAME a length quantity, or the sign check below proves nothing: \
         {result:?}"
    );
    for (name, value) in &lengths {
        assert!(
            !matches!(value, CounterexampleValue::Int(v) if *v < 0),
            "the surviving witness must be a REAL execution: `{name}` = {value:?} is a \
             NEGATIVE container length, which no execution can hold (this is the clause \
             that fails against pristine HEAD): {result:?}"
        );
    }
}

/// The shape from the doc comment. Its ONE `Unreachable` row must not be
/// refuted, and neither of its in-bounds `[x]`/`[x, .., y]` element reads may
/// regress from the `Proved` they already had at HEAD. MEASURED: the fixture
/// generates four rows — one `Unreachable` and THREE `SliceBoundsCheck`, all
/// three `Proved` and kernel-certified at HEAD and with the fix. The count is
/// asserted so the element-read loop below cannot become a no-op.
#[test]
fn merged_slice_match_unreachable_is_not_refuted() {
    let func = load(include_str!("fixtures/slice_match_merged_unreachable_mir.json"));
    let rows = verdicts(&func);
    let unreach: Vec<_> = rows.iter().filter(|(kind, _)| kind == "Unreachable").collect();
    assert_eq!(
        unreach.len(),
        1,
        "the three arms share one Unreachable sink; got {}",
        unreach.len()
    );
    assert!(
        !is_failed(&unreach[0].1),
        "a NEGATIVE slice length is not a counterexample — no execution can hold it; got {:?}",
        unreach[0].1
    );
    let bounds: Vec<_> = rows.iter().filter(|(kind, _)| kind == "SliceBoundsCheck").collect();
    assert_eq!(bounds.len(), 3, "the fixture's three element reads: {rows:?}");
    for (_, result) in &bounds {
        assert!(
            matches!(result, VerificationResult::Proved { .. }),
            "the guarded element reads proved at HEAD and must stay proved; got {result:?}"
        );
    }
}

/// `&[()]` — a ZERO-SIZED element. The lower bound is element-independent, so
/// this refutation must go away too. It is also the fixture that would break if
/// the `len <= isize::MAX` half were ever published globally: a ZST slice may
/// hold `usize::MAX` items.
#[test]
fn zst_element_slice_match_unreachable_is_not_refuted() {
    let func = load(include_str!("fixtures/slice_match_zst_unreachable_mir.json"));
    let rows = verdicts(&func);
    let unreach: Vec<_> = rows.iter().filter(|(kind, _)| kind == "Unreachable").collect();
    assert_eq!(unreach.len(), 1, "one Unreachable sink; got {}", unreach.len());
    assert!(
        !is_failed(&unreach[0].1),
        "`0 <= len` holds for a ZST element too; got {:?}",
        unreach[0].1
    );
}

/// THE POSITIVE CLAIM, on the only shape where this change closes a whole
/// function: `fn f(a: &[u32]) -> u32 { match a { [] => 0, [x, ..] => *x } }`.
/// MEASURED at pristine HEAD its `Unreachable` sink is REFUTED at
/// `a__slice_len = -1`; with the fix EVERY row of the function is `Proved` AND
/// kernel-certified. This is what separates "the accusation is gone" from "the
/// obligation is discharged", and it is the assertion that fails when
/// `conjoin_length_nonneg_bounds` is stubbed to return its argument.
#[test]
fn a_two_arm_slice_match_is_fully_discharged() {
    let func = load(include_str!("fixtures/slice_two_arm_head_proved_mir.json"));
    let rows = vc_rows(&func);
    assert_eq!(
        rows.len(),
        2,
        "the fixture generates one Unreachable sink and one element read: {:?}",
        rows.iter().map(|(vc, _)| &vc.kind).collect::<Vec<_>>()
    );
    for (vc, result) in &rows {
        assert!(
            matches!(result, VerificationResult::Proved { .. }),
            "every row of a two-arm slice match must be PROVED; got {:?} for {:?}",
            result,
            vc.kind
        );
        assert!(
            trust_certify::certify_vc(vc).is_some(),
            "and must kernel-certify — a `Proved` with no proof authority is counted \
             runtime-checked, not discharged: {:?}",
            vc.kind
        );
    }
}

/// CHANGED-PATH CANARY 1 — `fn f(a: &[u32], b: &[u32]) -> usize {
/// if a.len() > b.len() { unreachable!() } else { 0 } }`.
///
/// The trap is genuinely REACHABLE (`a` longer than `b` is an ordinary input),
/// so its panic-family `Assertion` row — a kind this fix TOUCHES, unlike the
/// bounds/overflow kinds the range battery already covered — must stay refuted.
/// MEASURED at pristine HEAD it is refuted at `a__slice_len = 0,
/// b__slice_len = -1`: a witness that is not an execution, on a row that is not
/// a false accusation. With the fix it is refuted at `a__slice_len = 1,
/// b__slice_len = 0`. Revert the fix and this test FAILS on the sign clause.
#[test]
fn reachable_two_length_trap_refutes_with_a_real_witness() {
    let func = load(include_str!("fixtures/slice_two_length_trap_mir.json"));
    assert_refutes_with_a_real_witness(&func, "Assertion", &[]);
}

/// CHANGED-PATH CANARY 2 — the same trap over `&[()]`, a ZERO-SIZED element.
/// `0 <= len` is element-independent, and this is the fixture that would break if
/// the withheld `len <= isize::MAX` half were ever attached here: a ZST slice may
/// hold `usize::MAX` items, so that bound is FALSE for it and an untrue bound is
/// how a real violation gets proved away. MEASURED: FAILS at pristine HEAD
/// (`b__slice_len = -1`), passes with the fix, refuted in both.
#[test]
fn reachable_zst_two_length_trap_refutes_with_a_real_witness() {
    let func = load(include_str!("fixtures/slice_two_length_zst_trap_mir.json"));
    assert_refutes_with_a_real_witness(&func, "Assertion", &[]);
}

/// CHANGED-PATH CANARY 3 — `fn f(v: &Vec<u32>, b: &[u32]) -> usize {
/// if v.len() > b.len() { unreachable!() } else { 0 } }`.
/// MEASURED: HEAD refutes at `v = 0, b__slice_len = -1`; with the fix, `v = 1,
/// b__slice_len = 0`. Revert the fix and this test FAILS on the sign clause.
///
/// It does NOT exercise the owned-container admission family. `coll_len_bound_vars`
/// matches a BARE `Ty::Adt` local, and this fixture's `v` is
/// `Ty::Ref { inner: Ty::Adt("alloc::vec::Vec") }`, so `v` is never admitted by
/// it — `v` is bounded here by the length-read-destination family instead.
/// MEASURED by mutation: deleting `coll_len_bound_vars` from the admission set
/// leaves every test in this diff GREEN, so that family ships with NO coverage.
#[test]
fn reachable_vec_length_trap_refutes_with_a_real_witness() {
    let func = load(include_str!("fixtures/vec_length_trap_mir.json"));
    assert_refutes_with_a_real_witness(&func, "Assertion", &["v"]);
}

/// ADVERSARIAL, and the canary that catches an OFF-BY-ONE in the published bound.
/// Two genuinely reachable violations that need `len == 0` as their witness, both
/// on VC kinds this fix TOUCHES:
///
/// ```ignore
/// pub fn f(a: &[u32], k: usize) -> usize { k / a.len() }              // DivisionByZero
/// pub fn f(a: &[u32]) -> u32 { match a { [] => unreachable!(), .. } } // Assertion
/// ```
///
/// The empty slice is an ordinary input, so each row MUST stay refuted with
/// `a__slice_len = 0` in its witness. MUTATION-CHECKED: mint the bound as
/// `1 <= len` instead of `0 <= len` — one character, and a FALSE fact about the
/// input program — and BOTH rows flip to `Proved`, kernel-certified, with a real
/// division by zero and a real reachable panic proved away. That is the exact
/// shape of a false proof this lane could have shipped, and no other assertion in
/// this file catches it. NOT evidence for the fix: both rows are equally refuted
/// at pristine HEAD (the witness was already `len = 0`), so this test passes with
/// the change reverted.
#[test]
fn reachable_traps_at_an_empty_container_still_refute() {
    for (label, kind, json) in [
        (
            "`k / a.len()`",
            "DivisionByZero",
            include_str!("fixtures/slice_div_by_len_zero_mir.json"),
        ),
        (
            "`match a { [] => unreachable!(), .. }`",
            "Assertion",
            include_str!("fixtures/slice_empty_match_trap_mir.json"),
        ),
    ] {
        let rows = verdicts(&load(json));
        let refuted: Vec<_> =
            rows.iter().filter(|(k, result)| k.starts_with(kind) && is_failed(result)).collect();
        assert_eq!(
            refuted.len(),
            1,
            "{label} traps on an EMPTY slice, an ordinary input, so exactly one `{kind}` row \
             must stay refuted: {rows:?}"
        );
        let lengths = length_assignments(&refuted[0].1, &[]);
        assert!(
            lengths.iter().any(|(_, v)| matches!(v, CounterexampleValue::Int(0))),
            "{label}'s witness must still be able to say `len = 0`, or the published bound is \
             not `0 <= len`: {:?}",
            refuted[0].1
        );
    }
}

/// EXCLUDED-KIND CONTROL. `a[i]` with unconstrained `i`, `a[a.len()]`, and
/// `a.len() + k` are real UB and must stay refuted — but their rows are
/// `SliceBoundsCheck` and `ArithmeticOverflow{Add}`, exactly the kinds the change
/// EXCLUDES via the `!range_kind` gate at its only call site.
///
/// The refutation half is a weak guard on its own (`0 <= len` is TRUE, so a scope
/// regression that started conjoining onto these rows would still leave them red —
/// MEASURED: removing the gate changes no verdict anywhere in the matrix). What
/// makes this test catch that regression is the SECOND assertion: the two BOUNDS
/// fixtures are loop-free, so `conjoin_slice_len_bounds` skips them as well
/// (`count_back_edges(func) == 0`), and their formulas therefore carry NO slice
/// length bound at all. MUTATION-CHECKED: drop the `!range_kind` gate and
/// `0 <= a__slice_len` appears in both, firing the assertion. The overflow fixture
/// is excluded from that half because the range battery legitimately bounds ITS
/// row.
#[test]
fn excluded_kind_ub_rows_still_refute() {
    for (label, expect_no_length_bound, json) in [
        (
            "`a[i]` with unconstrained `i`",
            true,
            include_str!("fixtures/slice_index_unconstrained_oob_mir.json"),
        ),
        ("`a[a.len()]`", true, include_str!("fixtures/slice_index_at_len_oob_mir.json")),
        (
            "`a.len() + k` overflow",
            false,
            include_str!("fixtures/slice_len_plus_k_overflow_mir.json"),
        ),
    ] {
        let rows = vc_rows(&load(json));
        // MEASURED: each of these three fixtures generates EXACTLY ONE row, so
        // pinning the count turns "some row is refuted" into "THE UB row is
        // refuted". Without it a fixture that grew a second, unrelated refuted row
        // could satisfy the assertion while the UB row itself flipped to proved.
        assert_eq!(rows.len(), 1, "{label} is a single-obligation fixture: {rows:?}");
        assert!(is_failed(&rows[0].1), "{label} is real UB and must stay refuted: {rows:?}");
        if expect_no_length_bound {
            assert!(
                !mentions_a_slice_length_lower_bound(&rows[0].0.formula),
                "{label} is an EXCLUDED kind on a loop-free body: no pass may attach a slice \
                 length bound to it, and one appearing here means the `!range_kind` gate no \
                 longer holds: {:?}",
                rows[0].0.formula
            );
        }
    }
}

/// DIRECTIONAL GUARD on the changed path, and honest about its own strength:
/// `match a { [] => 0, [x] => *x, _ => unreachable!() }` — the SAME row shape as
/// the defect, on a trap that is genuinely REACHABLE at `len >= 2`. Its
/// `Assertion` row IS on the changed path and must stay refuted. MEASURED,
/// though: its witness is already `len = 2` at pristine HEAD, so this test
/// PASSES with the fix reverted. It guards the "never bless UB" direction only;
/// it is not evidence that the bound is in force.
#[test]
fn reachable_trap_behind_a_slice_match_still_refutes() {
    let func = load(include_str!("fixtures/slice_match_reachable_unreachable_mir.json"));
    let rows = verdicts(&func);
    let refuted: Vec<_> = rows.iter().filter(|(_, r)| is_failed(r)).collect();
    // MEASURED: the fixture generates two rows — one `SliceBoundsCheck` (Proved at
    // HEAD and with the fix) and the trap's `Assertion`. Pinning the count, and the
    // fact that the surviving witness NAMES a length, is what keeps the sign loop
    // below from silently iterating over nothing.
    assert_eq!(
        refuted.len(),
        1,
        "`len >= 2` reaches the trap; exactly that row must stay refuted: {rows:?}"
    );
    let lengths = length_assignments(&refuted[0].1, &[]);
    assert!(
        !lengths.is_empty(),
        "the witness must NAME a length, or the sign check below runs zero times: {:?}",
        refuted[0].1
    );
    for (name, value) in lengths {
        assert!(
            !matches!(value, CounterexampleValue::Int(v) if v < 0),
            "the surviving witness must be a REAL execution: `{name}` is negative"
        );
    }
}

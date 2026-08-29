// Regression: an array→slice UNSIZE coercion must keep the array's STATIC length.
//
// `a.len()` on a `&[T; N]` does not read the array. rustc coerces first:
//
//     _3 = copy _1 as &[u8] (PointerCoercion(Unsize, Implicit));
//     _2 = PtrMetadata(move _3);
//
// `slice_len_formula` maps `_1`'s type to `Formula::Int(N)` but maps `_3`'s
// slice-reference type to the FREE var `_3__slice_len`, so without a tie at the
// coercion the `N` is discarded exactly where the length is read. A free length
// then refutes every obligation that consumes it — `a.len() - 1` (Sub underflow),
// a guarded `a[i]` (bounds), `100 / a.len()` (div-by-zero), `x % a.len()`
// (rem-by-zero) — on code that cannot fault.
//
// The two `still_refute` tests below are the soundness direction, and they are not
// symmetric decoration: the first tests that a tie exists, the second that it is
// the RIGHT one. A tie that resolved a destination to some other array's `N` would
// pass every "proves" test here and prove a real out-of-bounds read.
//
// The fixtures are the REAL extracted MIR (`-Ztrust-dump=mir-only:<dir>`) of the
// four functions quoted beside each loader.
use trust_types::*;
use trust_vcgen::generate_vcs;

fn fixture(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture MIR must deserialize")
}

fn safe_len_minus_one() -> VerifiableFunction {
    // pub fn f(a: &[u8; 8]) -> usize { a.len() - 1 }
    fixture(include_str!("fixtures/unsize_s_len_minus1.json"))
}

fn safe_guarded_index() -> VerifiableFunction {
    // pub fn f(a: &[u8; 8], i: usize) -> u8 { if i < a.len() { a[i] } else { 0 } }
    fixture(include_str!("fixtures/unsize_s_guarded_idx.json"))
}

fn unsafe_unguarded_index() -> VerifiableFunction {
    // pub fn f(a: &[u8; 8], i: usize) -> u8 { let s: &[u8] = a; s[i] }
    fixture(include_str!("fixtures/unsize_r_oob_slice_of_array.json"))
}

fn unsafe_crossed_lengths() -> VerifiableFunction {
    // pub fn f(i: usize) -> u8 {
    //     let a: [u8; 8] = [1; 8];
    //     let b: [u8; 2] = [2; 2];
    //     let s: &[u8] = &a;
    //     let t: &[u8] = &b;
    //     if i < s.len() { t[i] } else { 0 }   // guards on 8, indexes a len-2 slice
    // }
    fixture(include_str!("fixtures/unsize_r_two_slices.json"))
}

fn router() -> trust_router::Router {
    trust_router::Router::deterministic_in_process_ay(30_000)
}

fn verdict(router: &trust_router::Router, vc: &VerificationCondition) -> VerificationResult {
    let results = router.verify_all(std::slice::from_ref(vc));
    results.into_iter().next().expect("one verdict per VC").1
}

fn arithmetic_and_bounds(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    generate_vcs(func)
        .into_iter()
        .filter(|vc| {
            matches!(
                vc.kind,
                VcKind::ArithmeticOverflow { .. }
                    | VcKind::IndexOutOfBounds
                    | VcKind::SliceBoundsCheck
            )
        })
        .collect()
}

/// Every free `__slice_len` variable reachable from `formula`.
fn slice_len_vars(formula: &Formula) -> std::collections::BTreeSet<String> {
    formula
        .free_variables()
        .into_iter()
        .filter(|v| v.split('#').next().unwrap_or(v).ends_with("__slice_len"))
        .collect()
}

/// The array→slice coercion's length must reach the obligation as the CONSTANT 8,
/// not as a free variable, and the subtraction must then discharge.
///
/// Two independent assertions, because either alone is weak. Presence of the
/// literal `Int(8)` alone would survive a tie that names the WRONG destination
/// (the fact would be inert); an ay `Proved` alone would survive a tie that
/// over-constrains the model into vacuity. Together they pin that the fact is
/// both present and load-bearing.
#[test]
fn unsize_keeps_the_array_length_and_len_minus_one_proves() {
    let func = safe_len_minus_one();
    let vcs = arithmetic_and_bounds(&func);
    assert_eq!(vcs.len(), 1, "one Sub obligation; got {:?}", kinds(&vcs));
    let vc = &vcs[0];

    // The length term the obligation reads must be pinned to the array's `8`.
    let dbg = format!("{:?}", vc.formula);
    let lens = slice_len_vars(&vc.formula);
    for name in &lens {
        assert!(
            dbg.contains(&format!("Eq(Var(\"{name}\", Int), Int(8))"))
                || dbg.contains(&format!("Eq(Int(8), Var(\"{name}\", Int))")),
            "the coerced slice's length `{name}` is not tied to the source array's 8 — \
             it is a free variable and the obligation is refutable at length 0: {dbg}"
        );
    }

    let result = verdict(&router(), vc);
    assert!(
        matches!(result, VerificationResult::Proved { .. }),
        "`a.len() - 1` on a `&[u8; 8]` cannot underflow; got {result:?}\nformula: {dbg}"
    );
    assert!(
        trust_certify::certify_vc(vc).is_some(),
        "the proved subtraction must kernel-certify — an ay `Proved` with no kernel \
         token is reported `Unknown` under `-Ztrust-policy=certify`: {dbg}"
    );
}

/// The idiomatic guarded index `if i < a.len() { a[i] }` on a `&[T; N]`: the
/// guard's length read and the bounds obligation's length read must resolve to the
/// SAME constant, so the conjunction is UNSAT.
#[test]
fn guarded_index_on_array_reference_proves() {
    let func = safe_guarded_index();
    let vcs = arithmetic_and_bounds(&func);
    assert_eq!(vcs.len(), 1, "one bounds obligation; got {:?}", kinds(&vcs));
    let result = verdict(&router(), &vcs[0]);
    assert!(
        matches!(result, VerificationResult::Proved { .. }),
        "a guarded index on a `&[u8; 8]` is in bounds; got {result:?}\nformula: {:?}",
        vcs[0].formula
    );
    assert!(
        trust_certify::certify_vc(&vcs[0]).is_some(),
        "the proved bounds obligation must kernel-certify: {:?}",
        vcs[0].formula
    );
}

/// SOUNDNESS DIRECTION. Tying the length must not bless a real out-of-bounds read.
/// `let s: &[u8] = a; s[i]` with an unconstrained `i` is genuinely OOB (it panics
/// at runtime for `i >= 8`), so it must STILL be refuted — and, because the length
/// is now the true `8`, the counterexample must be a REACHABLE one.
#[test]
fn unguarded_index_through_the_coercion_still_refutes() {
    let func = unsafe_unguarded_index();
    let vcs = arithmetic_and_bounds(&func);
    let router = router();
    let refutations: Vec<_> = vcs
        .iter()
        .map(|vc| verdict(&router, vc))
        .filter(|r| matches!(r, VerificationResult::Failed { .. }))
        .collect();
    assert_eq!(
        refutations.len(),
        1,
        "the unguarded `s[i]` must be refuted; verdicts: {:?}",
        vcs.iter().map(|vc| verdict(&router, vc)).collect::<Vec<_>>()
    );
    // The witness must satisfy the tied length, not contradict it: an index of 8
    // into a length-8 slice. A counterexample that only exists because the length
    // was free (`s__slice_len = 0`) would mean the tie never reached this VC.
    let VerificationResult::Failed { counterexample: Some(ce), .. } = &refutations[0] else {
        panic!("a refutation of a bounds obligation must carry a counterexample");
    };
    for (name, value) in &ce.assignments {
        if name.split('#').next().unwrap_or(name).ends_with("__slice_len") {
            assert_eq!(
                format!("{value}"),
                "8",
                "the witness assigns `{name}` a length other than the source array's 8, \
                 so the coercion's length tie did not reach this obligation: {ce:?}"
            );
        }
    }
}

/// SOUNDNESS DIRECTION, aliasing case. Two coercions in one body must not share a
/// length. Guarding on the length-8 slice and indexing the length-2 one is a real
/// bug (it panics for `i` in `2..8`); a tie that resolved either destination to the
/// wrong array's `N` would prove it.
#[test]
fn crossed_lengths_from_two_coercions_still_refute() {
    let func = unsafe_crossed_lengths();
    let vcs = arithmetic_and_bounds(&func);
    let router = router();
    let mut refuted = 0;
    let mut witnesses = Vec::new();
    for vc in &vcs {
        if let VerificationResult::Failed { counterexample, .. } = verdict(&router, vc) {
            refuted += 1;
            witnesses.push(counterexample);
        }
    }
    assert_eq!(
        refuted,
        1,
        "guarding on an 8-element array and indexing a 2-element one must be refuted; \
         obligations: {:?}",
        vcs.iter().map(|vc| verdict(&router, vc)).collect::<Vec<_>>()
    );
    // Both lengths must appear, and they must be DIFFERENT: 8 for the guarded slice,
    // 2 for the indexed one. A single shared length is the exact over-eager tie this
    // test exists to kill.
    let ce = witnesses.remove(0).expect("a bounds refutation carries a counterexample");
    let lengths: std::collections::BTreeSet<String> = ce
        .assignments
        .iter()
        .filter(|(n, _)| n.split('#').next().unwrap_or(n).ends_with("__slice_len"))
        .map(|(_, v)| format!("{v}"))
        .collect();
    assert!(
        lengths.contains("8") && lengths.contains("2"),
        "the two coerced slices must keep their OWN lengths (8 and 2); witness lengths \
         were {lengths:?} in {ce:?}"
    );
}

// =========================================================================
// STALE LENGTH TIE — the tie must not survive a REASSIGNMENT of its subject.
//
// The tie above is minted at the array->slice CAST, keyed on the destination's
// derived metadata name `{dest}__slice_len`. A CAST also DEFINES that name, so a
// reassignment spelled as a cast re-versions it and the join sees two tokens; a
// reassignment spelled as an `Rvalue::Use` (`s = <call dest>`, `s = t`) defines
// only the bare name `s`, and every gen-set built from `formula_def_name` over
// `extract_block_definitions` therefore left `s__slice_len` unversioned. The cast
// block's token stayed the only one reaching the join and `s__slice_len == 8` was
// conjoined onto a path where `s` had been reseated to a length-2 or length-0
// slice — certified-PROVED bodies that panic at runtime.
//
// Every fixture below is the REAL extracted MIR of the quoted body, and every
// `reassign_*` body was RUN under stock rustc (`-O -C debug-assertions=on`) and
// observed to PANIC on the input range named beside it. `PROVED` on any of them is
// a false proof, which is why each asserts a refutation rather than "not proved".
//
// The guard in each is a CONSTANT comparison on purpose: it is then the tie ALONE
// that can discharge the post-reassignment bound, so the assertion cannot pass for
// an unrelated reason. `reassign_by_cast` is the control for the shape that always
// behaved correctly, and `const_guard_no_reassign` is the SAFE body with the same
// guard and no reassignment — the win this fix must not destroy.

/// Assert `func` is REJECTED: at least one of its safety obligations is refuted.
///
/// This is the whole-function property the compiler reports — a body is accepted
/// only when EVERY obligation proves — so it is the exact statement of "this
/// runtime-panicking body is not falsely proved". It is deliberately not
/// positional: which per-path obligation carries the refutation is an artifact of
/// the path split, and pinning that would fail on a re-split that changed nothing
/// about soundness.
///
/// The single failure path is this panic, so the diagnostic is always the one
/// printed (an `assert!` guarding a later `remove(0)` would be dead: the indexing
/// panic fires first and reports nothing).
fn assert_body_is_rejected(func: &VerifiableFunction, what: &str) {
    let vcs = arithmetic_and_bounds(func);
    let router = router();
    let verdicts: Vec<VerificationResult> = vcs.iter().map(|vc| verdict(&router, vc)).collect();
    if !verdicts.iter().any(|r| matches!(r, VerificationResult::Failed { .. })) {
        panic!(
            "FALSE PROOF: {what} panics at runtime, yet every one of its {} safety \
             obligations was proved. Verdicts: {verdicts:?}",
            verdicts.len()
        );
    }
}

/// `s = <call dest>` — the reassignment spelled as an `Rvalue::Use` of a call's
/// destination. Panics for `2 <= i < 8`.
///
///     let a: [u8; 8] = [..]; let mut s: &[u8] = &a;
///     if i < 8 { s = short_slice(); s[i] } else { 0 }
#[test]
fn reassignment_from_a_call_dest_still_refutes() {
    assert_body_is_rejected(
        &fixture(include_str!("fixtures/unsize_r_reassign_call_dest.json")),
        "`s = short_slice(); s[i]` under a constant guard on the OLD length",
    );
}

/// `s = t` between two slice locals — no call, no cast, still an `Rvalue::Use`.
/// Panics for `2 <= i < 8`.
#[test]
fn reassignment_from_another_slice_local_still_refutes() {
    assert_body_is_rejected(
        &fixture(include_str!("fixtures/unsize_r_reassign_slice_local.json")),
        "`s = t; s[i]` under a constant guard on `s`'s OLD length",
    );
}

/// Reassignment inside a LOOP: the stale tie reaches the loop header through the
/// back edge. Panics for `2 <= i < 8` and `n >= 2`.
#[test]
fn reassignment_in_a_loop_still_refutes() {
    assert_body_is_rejected(
        &fixture(include_str!("fixtures/unsize_r_reassign_in_loop.json")),
        "`while k < n { acc += s[i]; s = short_slice(); }`",
    );
}

/// Reassignment on ONE arm, obligation at the MERGE — the join where the cast
/// block's token was the only one reaching. Panics for `c` and `2 <= i < 8`.
#[test]
fn reassignment_on_one_branch_still_refutes() {
    assert_body_is_rejected(
        &fixture(include_str!("fixtures/unsize_r_reassign_branch_merge.json")),
        "`if c { s = short_slice(); } s[i]`",
    );
}

/// A callee handed `&mut s` RESEATS it. The caller sees only a `Call` terminator,
/// so this is the alias-havoc channel rather than a statement destination.
/// Panics for `2 <= i < 16`.
#[test]
fn callee_reseat_through_mut_ref_still_refutes() {
    assert_body_is_rejected(
        &fixture(include_str!("fixtures/unsize_r_reassign_mut_reseat.json")),
        "`reseat(&mut s); s[i]` where `reseat` does `*r = short_slice()`",
    );
}

/// The length was READ into a temp before the reassignment, so a live and a stale
/// length coexist in the same body. Panics for `2 <= i < 8`.
#[test]
fn reassignment_after_a_length_read_still_refutes() {
    assert_body_is_rejected(
        &fixture(include_str!("fixtures/unsize_r_reassign_after_len_read.json")),
        "`let n = s.len(); sink(n); s = short_slice(); if i < 8 { s[i] }`",
    );
}

/// A STORE through the reassigned slice, not a read — the obligation kind is
/// `IndexOutOfBounds` on the store's place. Panics for `2 <= i < 8`.
#[test]
fn store_through_a_reassigned_slice_still_refutes() {
    assert_body_is_rejected(
        &fixture(include_str!("fixtures/unsize_r_reassign_then_store.json")),
        "`s = &mut b[..]; s[i] = v`",
    );
}

/// CONTROL — the reassignment IS a cast, which mints its own `__slice_len` def.
/// This shape refuted before the version fix and must keep refuting: if it ever
/// stops, the reassignment channel has been closed by something that also removed
/// the cast's own definition. Panics for `2 <= i < 8`.
#[test]
fn cast_reassignment_control_still_refutes() {
    assert_body_is_rejected(
        &fixture(include_str!("fixtures/unsize_r_reassign_by_cast.json")),
        "`s = &b; s[i]` where `b: [u8; 2]`",
    );
}

/// COMPLETENESS DIRECTION — the same constant-guarded index with NO reassignment.
/// This is the win the re-versioning must not destroy: it is refuted without the
/// tie, and every obligation must be PROVED and kernel-CERTIFIED with it.
///
///     let a: [u8; 8] = [..]; let s: &[u8] = &a;
///     if i < 8 { s[i] } else { 0 }
#[test]
fn const_guarded_index_without_reassignment_still_proves() {
    let func = fixture(include_str!("fixtures/unsize_s_const_guard_no_reassign.json"));
    let vcs = arithmetic_and_bounds(&func);
    assert!(!vcs.is_empty(), "the indexed body must mint a bounds obligation");
    let router = router();
    for vc in &vcs {
        let result = verdict(&router, vc);
        assert!(
            matches!(result, VerificationResult::Proved { .. }),
            "`if i < 8 {{ s[i] }}` on a coerced `[u8; 8]` is in bounds; got {result:?}\n\
             formula: {:?}",
            vc.formula
        );
        assert!(
            trust_certify::certify_vc(vc).is_some(),
            "the proved bounds obligation must kernel-certify: {:?}",
            vc.formula
        );
    }
}

fn kinds(vcs: &[VerificationCondition]) -> Vec<String> {
    vcs.iter().map(|vc| format!("{:?}", vc.kind)).collect()
}

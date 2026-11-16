use super::*;

fn x0() -> Formula {
    Formula::Var("X0".into(), Sort::BitVec(64))
}
fn lit(v: i128, w: u32) -> Formula {
    Formula::BitVec { value: v, width: w }
}
fn plus(a: Formula, k: i128) -> Formula {
    Formula::BvAdd(b(a), b(lit(k, 64)), 64)
}
/// `0 - 0 == 0` (true) and `1 - 0 == 0` (false): the shape of s23's tag tests.
fn closed(v: bool) -> Formula {
    Formula::Eq(b(Formula::BvSub(b(lit(i128::from(!v), 64)), b(lit(0, 64)), 64)), b(lit(0, 64)))
}
fn ite(c: Formula, a: Formula, e: Formula) -> Formula {
    Formula::Ite(b(c), b(a), b(e))
}
/// A 64-bit read of a byte no path writes: outside the kernel's fragment.
fn unread() -> Formula {
    let mem = Formula::Var(
        "CER_MEM0".into(),
        Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
    );
    Formula::BvZeroExt(b(Formula::Select(b(mem), b(x0()))), 56)
}
fn premise(c: Formula, v: bool) -> (Formula, Formula) {
    (pred_to_int(if v { c } else { Formula::Not(b(c)) }, 1), lit(1, 1))
}

#[test]
fn closed_branch_folds_only_ground_conditions() {
    let conj = vec![(ite(closed(true), plus(x0(), 1), lit(9, 64)), plus(x0(), 1))];
    let folded = fold(&conj).expect("a ground condition folds");
    assert_eq!(folded.items, vec![(plus(x0(), 1), plus(x0(), 1))]);
    assert_eq!(folded.premises, vec![premise(closed(true), true)]);
    let folded = fold(&[(ite(closed(false), lit(9, 64), x0()), x0())]).unwrap();
    assert_eq!(folded.items[0].0, x0());
    assert_eq!(folded.premises, vec![premise(closed(false), false)]);
    for open in [
        Formula::Eq(b(x0()), b(lit(0, 64))),
        Formula::Eq(b(Formula::Var("SP".into(), Sort::BitVec(64))), b(lit(0, 64))),
        Formula::Eq(b(Formula::SymVar("X0".into(), Sort::BitVec(64))), b(lit(0, 64))),
        Formula::Eq(b(Formula::BvExtract { inner: b(unread()), high: 7, low: 0 }), b(lit(0, 8))),
    ] {
        assert!(fold(&[(ite(open.clone(), x0(), lit(1, 64)), x0())]).is_none(), "{open:?}");
    }
}

/// Arms of different sorts are never folded, whatever the condition.
#[test]
fn arms_of_different_sorts_stay() {
    let conj = vec![(ite(closed(true), lit(1, 32), lit(1, 64)), lit(1, 64))];
    assert!(fold(&conj).is_none());
    assert!(fold_with(&conj, &|_| Some(true)).is_none());
}

/// Each fold records the condition it read, so two sites of one condition chosen differently
/// leave both premises, and one of them is false.
#[test]
fn every_choice_is_a_premise() {
    let flips = std::cell::Cell::new(false);
    let chooser = |_: &Formula| {
        flips.set(!flips.get());
        Some(flips.get())
    };
    let conj = vec![
        (ite(closed(true), x0(), lit(0, 64)), x0()),
        (ite(closed(true), x0(), lit(0, 64)), x0()),
    ];
    let folded = fold_with(&conj, &chooser).unwrap();
    assert_eq!(folded.premises, vec![premise(closed(true), true), premise(closed(true), false)]);
}

/// A fold inside a condition is folded first, and the outer premise holds the folded condition.
#[test]
fn an_outer_premise_reads_the_folded_condition() {
    let inner = ite(closed(true), lit(0, 64), x0());
    let outer = Formula::Eq(b(inner), b(lit(0, 64)));
    let conj = vec![(ite(outer, lit(5, 64), lit(6, 64)), lit(5, 64))];
    let folded = fold(&conj).unwrap();
    assert_eq!(folded.items, vec![(lit(5, 64), lit(5, 64))]);
    assert_eq!(
        folded.premises,
        vec![premise(closed(true), true), premise(Formula::Eq(b(lit(0, 64)), b(lit(0, 64))), true),]
    );
}

/// The retry runs only where the unfolded conjunction leaves the kernel's fragment. The control
/// shows the fold itself would have been accepted, so the `None` is the early return's.
#[cfg(feature = "kernel-recheck")]
#[test]
fn retry_needs_an_unlowerable_item() {
    let conj = vec![(ite(closed(true), plus(x0(), 1), lit(9, 64)), plus(x0(), 1))];
    assert!(check(&canonicalize(fold(&conj).unwrap())).is_some(), "the control");
    assert!(retry(&conj).is_none(), "every item lowers: the first attempt is the attempt");
    let conj = vec![(ite(Formula::Eq(b(x0()), b(lit(0, 64))), x0(), unread()), x0())];
    assert!(retry(&conj).is_none(), "no ground condition: nothing to fold");
}

/// One unlowerable item is enough: a conjunction with a plain item beside it is retried.
#[cfg(feature = "kernel-recheck")]
#[test]
fn a_mixed_conjunction_is_retried() {
    let conj = vec![(x0(), x0()), (ite(closed(true), x0(), unread()), x0())];
    assert!(retry(&conj).is_some());
}

fn x1() -> Formula {
    Formula::Var("X1".into(), Sort::BitVec(64))
}

/// A part the kernel did not check (a wide multiply's structural citation) is never wrapped as
/// kernel evidence, as a premise or as the value.
#[cfg(feature = "kernel-recheck")]
#[test]
fn a_citation_is_not_kernel_evidence() {
    let mul = |a: Formula, c: Formula| Formula::BvMul(b(a), b(c), 64);
    let c = Formula::Eq(b(mul(lit(3, 64), lit(5, 64))), b(lit(15, 64)));
    let conj = vec![(ite(c.clone(), x0(), plus(x0(), 1)), plus(x0(), 1))];
    let wrong = fold_with(&conj, &|_| Some(false)).unwrap();
    assert!(check(&wrong).is_none(), "the premise `3 * 5 != 15` is false");
    let conj = vec![(ite(c, x0(), plus(x0(), 1)), x0())];
    assert!(check(&fold(&conj).unwrap()).is_none(), "a true premise over a wide multiply is cited");
    let conj = vec![(ite(closed(true), mul(x0(), x1()), unread()), mul(x1(), x0()))];
    let folded = fold(&conj).unwrap();
    assert!(
        matches!(
            try_kernel_recheckable_conjunction(&folded.items),
            Some(ProvenEvidence::StructuralCitation { .. })
        ),
        "the precondition: the folded value is only cited"
    );
    assert!(retry(&conj).is_none());
}

/// A fold whose taken arm still leaves the fragment is not retried.
#[cfg(feature = "kernel-recheck")]
#[test]
fn a_taken_arm_outside_the_fragment_is_not_retried() {
    let conj = vec![(ite(closed(true), unread(), x0()), unread())];
    let folded = fold(&conj).unwrap();
    assert!(!folded.items.iter().all(lowers_item));
    assert!(retry(&conj).is_none());
}

/// A 128-bit register pair is read as the kernel conjunction reads it: split at bit 64.
#[cfg(feature = "kernel-recheck")]
#[test]
fn a_register_pair_is_retried_half_by_half() {
    let pair = |hi: Formula, lo: Formula| Formula::BvConcat(b(hi), b(lo));
    let conj = vec![(pair(x1(), ite(closed(true), x0(), unread())), pair(x1(), x0()))];
    assert!(retry(&conj).is_some());
    let wrong = vec![(pair(x1(), ite(closed(true), x0(), unread())), pair(x0(), x0()))];
    assert!(retry(&wrong).is_none());
}

/// A false original never earns a kernel grade through the retry, with the right chooser or a
/// wrong one; the same shape over a true original is proved (the control: a missing kernel
/// fails this test rather than passing it).
#[cfg(feature = "kernel-recheck")]
#[test]
fn retry_never_proves_a_false_original() {
    for c in [true, false] {
        let (taken, untaken) = (x0(), unread());
        let original =
            |t: Formula, u: Formula| if c { ite(closed(c), t, u) } else { ite(closed(c), u, t) };
        let truth = vec![(original(taken.clone(), untaken.clone()), x0())];
        assert!(retry(&truth).is_some(), "{c}: the control");
        let falsity = vec![(original(taken.clone(), untaken.clone()), plus(x0(), 1))];
        assert!(retry(&falsity).is_none(), "{c}: the taken arm is false");
        // A wrong chooser makes the untaken arm the item: `X0 + 1` against `X0 + 1` is true,
        // and only the premise refuses it.
        let wrong_shape = vec![(original(taken.clone(), plus(x0(), 1)), plus(x0(), 1))];
        let wrong = fold_with(&wrong_shape, &|cond| ground_bool(cond).map(|v| !v)).unwrap();
        assert!(try_kernel_recheckable_conjunction(&wrong.items).is_some(), "{c}: the wrong item");
        assert!(check(&wrong).is_none(), "{c}: the wrong premise");
        let right = fold(&wrong_shape).unwrap();
        assert!(check(&right).is_none(), "{c}: the right fold of a false original");
    }
}

/// Two sites of one condition chosen differently: one premise is false, so no grade.
#[cfg(feature = "kernel-recheck")]
#[test]
fn an_inconsistent_chooser_is_declined() {
    let flips = std::cell::Cell::new(false);
    let chooser = |_: &Formula| {
        flips.set(!flips.get());
        Some(flips.get())
    };
    let conj = vec![(ite(closed(true), x0(), x0()), x0()), (ite(closed(true), x0(), x0()), x0())];
    let folded = fold_with(&conj, &chooser).unwrap();
    assert!(try_kernel_recheckable_conjunction(&folded.items).is_some(), "the items are true");
    assert!(check(&folded).is_none());
    assert!(check(&fold(&conj).unwrap()).is_some(), "the control");
}

/// A wrong fold of an `Ite` inside a condition is declined. The original is false (the outer
/// condition is true, so it reads `X0` against `X0 + 1`); folding the inner `Ite` wrongly makes
/// the outer condition false, so the item becomes `X0 + 1` against `X0 + 1` and the outer
/// premise is true. Only the inner premise refuses it.
#[cfg(feature = "kernel-recheck")]
#[test]
fn a_wrong_inner_fold_is_declined() {
    let outer = || Formula::Eq(b(ite(closed(true), lit(0, 64), lit(1, 64))), b(lit(0, 64)));
    let truth = vec![(ite(outer(), x0(), unread()), x0())];
    assert!(retry(&truth).is_some(), "the control");
    let falsity = vec![(ite(outer(), x0(), plus(x0(), 1)), plus(x0(), 1))];
    let calls = std::cell::Cell::new(0);
    let wrong_inner = |cond: &Formula| {
        calls.set(calls.get() + 1);
        ground_bool(cond).map(|v| if calls.get() == 1 { !v } else { v })
    };
    let folded = fold_with(&falsity, &wrong_inner).unwrap();
    assert_eq!(folded.items, vec![(plus(x0(), 1), plus(x0(), 1))]);
    assert!(check(&folded).is_none());
}

/// The retry's purpose: an item whose untaken arm reads memory leaves the kernel's fragment;
/// with the closed branch folded it is kernel-checked, and the evidence names the premise.
#[cfg(feature = "kernel-recheck")]
#[test]
fn retry_proves_a_closed_branch_over_unread_memory() {
    let conj = vec![(ite(closed(true), plus(x0(), 1), unread()), plus(x0(), 1))];
    assert!(try_kernel_recheckable_conjunction(&conj).is_none(), "the unfolded item declines");
    match retry(&conj) {
        Some(ProvenEvidence::KernelRecheckableWithSideConditions { side_conditions, .. }) => {
            assert_eq!(side_conditions.len(), 1);
        }
        other => panic!("{other:?}"),
    }
}

fn bv_and(a: Formula, k: i128) -> Formula {
    Formula::BvAnd(b(a), b(lit(k, 64)), 64)
}
fn minus(a: Formula, k: i128) -> Formula {
    Formula::BvSub(b(a), b(lit(k, 64)), 64)
}
/// s23 at O0 after the fold: the machine tests `(x0 & 1) - 0 == 0`, the spec
/// `ite((x0 & 1) == 0, 1, 0) != 0`, at the 32-bit width the producer's `Switch` uses.
fn s23_tests() -> (Formula, Formula) {
    let tag = bv_and(x0(), 1);
    let machine = Formula::Eq(b(minus(tag.clone(), 0)), b(lit(0, 64)));
    let spec = Formula::Not(b(Formula::Eq(
        b(pred_to_int(Formula::Eq(b(tag), b(lit(0, 64))), 32)),
        b(lit(0, 32)),
    )));
    (machine, spec)
}

/// Both renderings of s23's tag test become one term, and each rewrite is a premise.
#[test]
fn canonical_forms_meet() {
    let (machine, spec) = s23_tests();
    let folded = Folded {
        items: vec![(
            ite(machine.clone(), lit(5, 64), plus(x0(), 1)),
            ite(spec.clone(), lit(5, 64), plus(x0(), 1)),
        )],
        premises: vec![],
    };
    let c = canonicalize(folded);
    let tag_test = Formula::Eq(b(bv_and(x0(), 1)), b(lit(0, 64)));
    let both = ite(tag_test.clone(), lit(5, 64), plus(x0(), 1));
    assert_eq!(c.items, vec![(both.clone(), both)]);
    let eq = |r: Formula, o: Formula| (pred_to_int(Formula::Eq(b(r), b(o)), 1), lit(1, 1));
    assert_eq!(
        c.premises,
        vec![
            eq(bv_and(x0(), 1), minus(bv_and(x0(), 1), 0)),
            eq(pred_to_int(tag_test, 1), pred_to_int(spec, 1)),
        ]
    );
}

/// Only the two exact shapes are rewritten.
#[test]
fn canonicalization_leaves_other_shapes() {
    let tag = bv_and(x0(), 1);
    for f in [
        minus(x0(), 1),
        Formula::BvSub(b(x0()), b(lit(0, 32)), 64),
        Formula::Not(b(Formula::Eq(b(pred_to_int(tag.clone(), 32)), b(lit(1, 32))))),
        Formula::Not(b(Formula::Eq(
            b(ite(Formula::Eq(b(tag.clone()), b(lit(0, 64))), lit(2, 32), lit(0, 32))),
            b(lit(0, 32)),
        ))),
        Formula::Not(b(Formula::Eq(
            b(pred_to_int(Formula::Eq(b(tag.clone()), b(lit(0, 64))), 32)),
            b(lit(0, 64)),
        ))),
        Formula::BvSub(b(lit(0, 64)), b(x0()), 64),
        Formula::Eq(b(pred_to_int(Formula::Eq(b(tag.clone()), b(lit(0, 64))), 32)), b(lit(0, 32))),
        Formula::Not(b(Formula::Eq(
            b(lit(0, 32)),
            b(pred_to_int(Formula::Eq(b(tag.clone()), b(lit(0, 64))), 32)),
        ))),
        Formula::Not(b(Formula::Eq(
            b(ite(Formula::Eq(b(tag.clone()), b(lit(0, 64))), lit(0, 32), lit(1, 32))),
            b(lit(0, 32)),
        ))),
        Formula::Not(b(Formula::Eq(
            b(ite(Formula::Eq(b(tag.clone()), b(lit(0, 64))), lit(1, 32), lit(5, 32))),
            b(lit(0, 32)),
        ))),
        Formula::Not(b(Formula::Eq(
            b(ite(Formula::Eq(b(tag.clone()), b(lit(0, 64))), lit(1, 32), lit(0, 64))),
            b(lit(0, 64)),
        ))),
        Formula::Not(b(Formula::Eq(
            b(ite(Formula::Eq(b(tag.clone()), b(lit(0, 64))), lit(1, 32), lit(0, 64))),
            b(lit(0, 32)),
        ))),
    ] {
        let c = canonicalize(Folded { items: vec![(f.clone(), f.clone())], premises: vec![] });
        assert_eq!(c.items, vec![(f.clone(), f.clone())], "{f:?}");
        assert!(c.premises.is_empty(), "{f:?}");
    }
}

/// s23's folded shape, with its unwritten-payload arm, is kernel-checked: canonicalized, by a
/// bit-blast certificate within the re-checkable refutation limit; unrewritten, the bit-blast is
/// over it and the branch split proves the folded value instead.
#[cfg(feature = "kernel-recheck")]
#[test]
fn s23_shape_is_kernel_proved() {
    let (machine, spec) = s23_tests();
    let dead = Formula::BvAdd(b(unread()), b(lit(1, 64)), 64);
    let conj = vec![(
        ite(machine, lit(5, 64), ite(closed(false), dead, plus(x0(), 1))),
        ite(spec, lit(5, 64), plus(x0(), 1)),
    )];
    let unrewritten = fold(&conj).unwrap();
    assert!(
        try_kernel_recheckable_conjunction(&unrewritten.items).is_none(),
        "unrewritten, the fold's bit-blast declines"
    );
    // Unrewritten, the branch split proves the folded value by its own kernel-checked `x - 0`
    // step (`Trust.BVB.sub_zero`) and carrier identity, under the fold's one premise (measured
    // 2026-11-14; before the branch split in `check`, this was `None`). The retry still
    // canonicalizes first, so its value is the bit-blast's, below.
    match check(&unrewritten) {
        Some(ProvenEvidence::KernelRecheckableWithSideConditions { value, side_conditions }) => {
            assert_eq!(side_conditions.len(), 1);
            assert!(
                matches!(&*value, ProvenEvidence::KernelInstantiated { theorem, .. }
                    if theorem.contains("Trust.BVB.sub_zero") && theorem.ends_with(BRANCH_TAIL)),
                "{value:?}"
            );
        }
        other => panic!("unrewritten: {other:?}"),
    }
    match retry(&conj) {
        Some(ProvenEvidence::KernelRecheckableWithSideConditions { side_conditions, .. }) => {
            assert_eq!(side_conditions.len(), 3, "the fold's premise and two rewrites");
        }
        other => panic!("{other:?}"),
    }
}

/// A subtraction of a non-zero constant is kept, so a goal that needs it is still proved.
#[cfg(feature = "kernel-recheck")]
#[test]
fn a_nonzero_subtraction_is_kept() {
    let conj = vec![(ite(closed(true), minus(x0(), 1), unread()), minus(x0(), 1))];
    assert!(retry(&conj).is_some());
    let wrong = vec![(ite(closed(true), minus(x0(), 1), unread()), x0())];
    assert!(retry(&wrong).is_none());
}

/// r08's specification, `((big + x0) - big) + 1` with `big = u64::MAX - 1000`: the shape only the
/// additive-cancellation route (DECISION_QUEUE CANCEL-1) joins to `x0 + 1`.
#[cfg(feature = "kernel-recheck")]
fn r08_spec() -> Formula {
    let big = || Formula::BvSub(b(lit((1i128 << 64) - 1, 64)), b(lit(1000, 64)), 64);
    plus(Formula::BvSub(b(Formula::BvAdd(b(big()), b(x0()), 64)), b(big()), 64), 1)
}

/// CANCEL-1 on this path: the folded item reaches the O(1) cancel route through
/// `try_kernel_recheckable_conjunction`. With the untaken arm reading memory, folded the item is
/// `x0 + 1` against r08's spec, and the value evidence is the cancel route's `KernelInstantiated`
/// under the premise. A wrong fold (every choice negated) puts `x0 + 2` in its place: the cancel
/// route declines that value item on its own, whatever the premise, and the retry declines.
#[cfg(feature = "kernel-recheck")]
#[test]
fn a_folded_item_takes_the_cancel_route_and_a_wrong_fold_does_not() {
    const CANCEL: &str =
        "Trust.BVA.add_sub_cancel+Clean.BVC congruence (O(1) add@N, additive cancellation)";
    let conj = vec![(ite(closed(true), plus(x0(), 1), unread()), r08_spec())];
    assert!(try_kernel_recheckable_conjunction(&conj).is_none(), "the unfolded item declines");
    match retry(&conj) {
        Some(ProvenEvidence::KernelRecheckableWithSideConditions { value, side_conditions }) => {
            let label = match &*value {
                ProvenEvidence::KernelInstantiated { theorem, .. } => Some(theorem.as_str()),
                _ => None,
            };
            assert_eq!(label, Some(CANCEL), "{value:?}");
            assert_eq!(side_conditions.len(), 1);
        }
        other => panic!("{other:?}"),
    }

    let falsity = vec![(ite(closed(true), plus(x0(), 1), plus(x0(), 2)), r08_spec())];
    let folded = fold_with(&falsity, &|c| ground_bool(c).map(|v| !v)).unwrap();
    assert_eq!(folded.items, vec![(plus(x0(), 2), r08_spec())]);
    assert!(try_kernel_recheckable_conjunction(&folded.items).is_none(), "a wrong value item");
    assert!(check(&folded).is_none());
}

// ── s23 at O2: the branch split proves the folded value (DECISION_QUEUE BRANCH-SPLIT-1) ─────────

/// What every branch-split label ends with (`branch_theory::LABEL_TAIL`).
#[cfg(feature = "kernel-recheck")]
const BRANCH_TAIL: &str = "kernel atom case split (O(1) branching conjunction, BRANCH-SPLIT-1)";

/// The folded s23 O2 value's label, measured (2026-11-14): the `tbz` and `beq_and_lowbit`
/// bridges meet on bit 0 of `X0`, split once, and each leaf selects its arms.
#[cfg(feature = "kernel-recheck")]
const S23_O2_LABEL: &str = "Clean.BVC.bvf_add_cong+Clean.BVC.bvf_and_cong+Trust.BVB.beq_and_lowbit+\
                            Trust.BVB.ite_cong+Trust.BVB.ite_false+Trust.BVB.ite_true+kernel atom \
                            case split (O(1) branching conjunction, BRANCH-SPLIT-1)";

/// `X0[bit:bit] == 0`: the machine's `tbz w0, #bit` test (s23 at O2 tests bit 0).
#[cfg(feature = "kernel-recheck")]
fn tbz(bit: u32) -> Formula {
    Formula::Eq(b(Formula::BvExtract { inner: b(x0()), high: bit, low: bit }), b(lit(0, 1)))
}

/// A literal tag tested against 0: the machine's `cbz` on the reloaded tag at O2 (`0 == 0` on the
/// `E::A` path, `1 == 0` on the `E::B` path).
#[cfg(feature = "kernel-recheck")]
fn tag_is_zero(tag: i128) -> Formula {
    Formula::Eq(b(lit(tag, 64)), b(lit(0, 64)))
}

/// s23's step-(5) conjunction at O2, as `TRUST_GATE_TRACE=1` captured it (the bridge's own trust-cg
/// compile of the producer IR and the compiler lane's object give the same one), with the untaken
/// `E::A` arm's eight-byte read of the unwritten payload slot shortened to one unread byte.
#[cfg(feature = "kernel-recheck")]
fn s23_o2() -> Vec<(Formula, Formula)> {
    let machine = ite(
        tbz(0),
        ite(tag_is_zero(0), lit(5, 64), plus(unread(), 1)),
        ite(tag_is_zero(1), lit(5, 64), plus(x0(), 1)),
    );
    vec![(machine, ite(s23_tests().1, lit(5, 64), plus(x0(), 1)))]
}

/// The folded and canonicalized s23 O2 value: `tbz` against `x & 1 == 0`.
#[cfg(feature = "kernel-recheck")]
fn s23_o2_folded_items(machine_test: Formula) -> Vec<(Formula, Formula)> {
    let tag_test = Formula::Eq(b(bv_and(x0(), 1)), b(lit(0, 64)));
    vec![(ite(machine_test, lit(5, 64), plus(x0(), 1)), ite(tag_test, lit(5, 64), plus(x0(), 1)))]
}

/// s23 at O2: the retry folds the two ground tag tests and canonicalizes the spec's carrier (three
/// premises, each a bit-blast certificate within the limit); the folded value's bit-blast is over
/// the limit, so the value is the branch split's `KernelInstantiated`, under the three premises.
/// FAILS without the branch split in `check` (mutant C1, `scripts/frozen-waivers.txt`): the retry
/// declines (at the gate the grade is then [VALIDATED], `branch_split_gate.rs`).
#[cfg(feature = "kernel-recheck")]
#[test]
fn s23_o2_value_is_proved_by_the_branch_split() {
    let conj = s23_o2();
    assert!(!conj.iter().all(lowers_item), "the unfolded item reads memory");
    let folded = canonicalize(fold(&conj).expect("two ground tag tests fold"));
    assert_eq!(folded.items, s23_o2_folded_items(tbz(0)));
    assert_eq!(folded.premises.len(), 3, "{:#?}", folded.premises);
    assert!(folded.items.iter().chain(&folded.premises).all(lowers_item));
    assert!(
        try_kernel_recheckable_conjunction(&folded.items).is_none(),
        "the folded value's bit-blast is over the re-checkable refutation limit"
    );
    for (i, p) in folded.premises.iter().enumerate() {
        match try_kernel_recheckable_conjunction(std::slice::from_ref(p)) {
            // Measured 2026-11-14: 129, 133 and 139 refutation steps (the limit is 2048).
            Some(ProvenEvidence::KernelRecheckable(c)) => {
                println!("[s23-o2] premise {i}: {} refutation steps", c.refutation.steps.len());
            }
            other => panic!("premise {i} is not a bit-blast certificate: {other:?}"),
        }
    }
    match retry(&conj) {
        Some(ProvenEvidence::KernelRecheckableWithSideConditions { value, side_conditions }) => {
            assert_eq!(side_conditions.len(), 3);
            match &*value {
                ProvenEvidence::KernelInstantiated { theorem, original: None } => {
                    assert_eq!(theorem, S23_O2_LABEL);
                }
                other => panic!("the value is not the branch split's: {other:?}"),
            }
        }
        other => panic!("{other:?}"),
    }
}

/// Mutants that reach the branch split in `check` (every folded item and premise lowers), each
/// declined: (a) the `E::B` tag test folded wrongly (chooser negated on `1 == 0` only), so the
/// machine reads `ite(tbz, 5, 5)` and its premise is false; (b) the true folded items with one
/// false premise, so a branch-split success does not excuse a premise; (c) the machine testing bit
/// 1 (`tbz #1`); (d) the spec's arms swapped. The fully negated chooser does not reach `check`:
/// its taken arm reads memory, so the retry returns before it (closed_branch.rs, the lowering
/// check after the fold).
#[cfg(feature = "kernel-recheck")]
#[test]
fn s23_o2_mutants_reaching_the_branch_split_are_declined() {
    let conj = s23_o2();
    let right = canonicalize(fold(&conj).unwrap());
    assert!(branch_split(&right.items).is_some(), "the control: the route proves the true items");
    assert!(check(&right).is_some(), "the control");

    // (a)
    let wrong_b = |c: &Formula| ground_bool(c).map(|v| if *c == tag_is_zero(1) { !v } else { v });
    let a = canonicalize(fold_with(&conj, &wrong_b).unwrap());
    assert_eq!(a.items[0].0, ite(tbz(0), lit(5, 64), lit(5, 64)));
    assert!(a.items.iter().chain(&a.premises).all(lowers_item), "(a) reaches check");
    assert!(branch_split(&a.items).is_none(), "(a) the route proved ite(tbz, 5, 5)");
    assert!(check(&a).is_none(), "(a)");

    // (b)
    let mut b_ = Folded { items: right.items.clone(), premises: right.premises.clone() };
    b_.premises[0] = premise(tag_is_zero(1), true);
    assert!(branch_split(&b_.items).is_some(), "(b) the items are true");
    assert!(check(&b_).is_none(), "(b) a false premise");

    // (c)
    let c = Folded { items: s23_o2_folded_items(tbz(1)), premises: right.premises.clone() };
    assert!(c.items.iter().all(lowers_item));
    assert!(check(&c).is_none(), "(c) tbz #1");

    // (d)
    let d = Folded {
        items: right
            .items
            .iter()
            .map(|(l, r)| match r {
                Formula::Ite(p, t, e) => (l.clone(), Formula::Ite(p.clone(), e.clone(), t.clone())),
                other => (l.clone(), other.clone()),
            })
            .collect(),
        premises: right.premises.clone(),
    };
    assert_ne!(d.items, right.items);
    assert!(check(&d).is_none(), "(d) spec arms swapped");

    // The fully negated chooser: the taken arm reads memory, so the retry never reaches `check`.
    let all = fold_with(&conj, &|c| ground_bool(c).map(|v| !v)).unwrap();
    assert!(!canonicalize(all).items.iter().all(lowers_item));
}

/// A folded value the conjunction routes give only non-kernel evidence for (s05's step-(5) conj,
/// `fixtures/s05_if_chain-O0-aarch64-apple-darwin.json` of the branch split, whose `x * 3` is a
/// wide multiply's `StructuralCitation`) is not kept: `check` asks the branch split, which proves
/// it, so the value is kernel evidence under the premise. Keeping the citation would make
/// `with_side_conditions` refuse it and `check` decline.
#[cfg(feature = "kernel-recheck")]
#[test]
fn a_non_kernel_folded_value_is_replaced_by_the_branch_split() {
    let items: Vec<(Formula, Formula)> = serde_json::from_str(include_str!(
        "../../verify_output_instantiate/branch_split/fixtures/s05_if_chain-O0-aarch64-apple-darwin.json"
    ))
    .expect("fixture parses");
    let routed = try_kernel_recheckable_conjunction(&items);
    assert!(matches!(&routed, Some(ProvenEvidence::StructuralCitation { .. })), "{routed:?}");
    let folded = Folded { items, premises: vec![premise(closed(true), true)] };
    match check(&folded) {
        Some(ProvenEvidence::KernelRecheckableWithSideConditions { value, side_conditions }) => {
            assert_eq!(side_conditions.len(), 1);
            assert!(
                matches!(&*value, ProvenEvidence::KernelInstantiated { theorem, original: None }
                    if theorem.ends_with(BRANCH_TAIL)),
                "{value:?}"
            );
        }
        other => panic!("{other:?}"),
    }
}

/// What the `test-hooks` recorder shows for `check`'s own call to the branch split: one entry,
/// `true` when the route returned kernel evidence, even where a false premise then makes `check`
/// decline (the value is asked before the premises; DECISION_QUEUE BRANCH-SPLIT-1), and `false`
/// when the route declines.
#[cfg(all(feature = "kernel-recheck", feature = "test-hooks"))]
#[test]
fn check_records_one_branch_split_call() {
    use crate::verify_output_instantiate::record_branch_split_calls;
    let right = canonicalize(fold(&s23_o2()).unwrap());
    let (got, calls) = record_branch_split_calls(|| check(&right));
    assert!(got.is_some(), "the control");
    assert_eq!(calls, [true], "the control");

    let mut false_premise = Folded { items: right.items.clone(), premises: right.premises.clone() };
    false_premise.premises[0] = premise(tag_is_zero(1), true);
    let (got, calls) = record_branch_split_calls(|| check(&false_premise));
    assert!(got.is_none(), "a false premise");
    assert_eq!(calls, [true], "the route proved the items before the premise was refused");

    let tbz1 = Folded { items: s23_o2_folded_items(tbz(1)), premises: right.premises.clone() };
    let (got, calls) = record_branch_split_calls(|| check(&tbz1));
    assert!(got.is_none(), "tbz #1");
    assert_eq!(calls, [false], "tbz #1");
}

// ── a folded symbolic division: the DIV-SPLIT-1 value at `check` (DECISION_QUEUE DIV-SPLIT-1) ───

/// What every division-split label ends with (`div_split::LABEL_TAIL`).
#[cfg(feature = "kernel-recheck")]
const DIV_TAIL: &str = "kernel atom case split, guarded symbolic division (DIV-SPLIT-1)";

/// s21's step-(5) conjunction at O2 (`div_split/fixtures/s21_div_var-O2.json`: `if x != 0 { 1000 /
/// x } else { 0 }` over `u64`), standing for folded items with a symbolic divisor.
#[cfg(feature = "kernel-recheck")]
fn s21_o2() -> Vec<(Formula, Formula)> {
    serde_json::from_str(include_str!(
        "../../verify_output_instantiate/div_split/fixtures/s21_div_var-O2.json"
    ))
    .expect("fixture parses")
}

/// A symbolic division at `check` (DECISION_QUEUE DIV-SPLIT-1). REACHABILITY: `retry` calls
/// `check` only when every folded item lowers, and `formula_to_bvexpr` refuses every `BvUDiv`
/// (`formula_to_bvexpr_refuses_dividers`), so today no such item reaches `check`: s21's division
/// item does not lower, and `retry` returns `None` without calling the branch routes. IF one did
/// (`check` called directly here): the conjunction routes give no kernel evidence, the step-(5)
/// branch routes give the division split's `KernelInstantiated`, and `check` wraps it with the
/// premise's bit-blast as `KernelRecheckableWithSideConditions`, the recorder showing one call,
/// `true`. Declined: the same true items under a false premise (a division-split value never
/// excuses a premise; the call is still `true`, asked first), and a false division (the spec's
/// dividend 1001; the call `false`).
#[cfg(all(feature = "kernel-recheck", feature = "test-hooks"))]
#[test]
fn a_folded_symbolic_division_is_proved_by_the_div_split_under_its_premises() {
    use crate::verify_output_instantiate::record_branch_split_calls;
    let items = s21_o2();
    assert!(!lowers_item(&items[0]), "the division item lowers: check() is now reachable");
    let (got, calls) = record_branch_split_calls(|| retry(&items));
    assert_eq!(got, None, "retry");
    assert!(calls.is_empty(), "retry called the branch routes: {calls:?}");

    let routed = try_kernel_recheckable_conjunction(&items);
    assert!(!routed.as_ref().is_some_and(ProvenEvidence::is_kernel), "{routed:?}");

    let right = Folded { items: items.clone(), premises: vec![premise(closed(true), true)] };
    let (got, calls) = record_branch_split_calls(|| check(&right));
    assert_eq!(calls, [true], "the control");
    match got {
        Some(ProvenEvidence::KernelRecheckableWithSideConditions { value, side_conditions }) => {
            assert_eq!(side_conditions.len(), 1);
            assert!(
                matches!(&*value, ProvenEvidence::KernelInstantiated { theorem, original: None }
                    if theorem.ends_with(DIV_TAIL) && !theorem.contains("BRANCH-SPLIT-1")),
                "{value:?}"
            );
        }
        other => panic!("{other:?}"),
    }

    let false_premise =
        Folded { items: items.clone(), premises: vec![premise(closed(false), true)] };
    let (got, calls) = record_branch_split_calls(|| check(&false_premise));
    assert!(got.is_none(), "a false premise: {got:?}");
    assert_eq!(calls, [true], "the route proved the items before the premise was refused");

    let mut wrong = items;
    wrong[0].1 = wrong[0].1.clone().map(&mut |f| match f {
        Formula::BvUDiv(a, d, 64) if matches!(*a, Formula::BitVec { value: 1000, width: 64 }) => {
            Formula::BvUDiv(b(lit(1001, 64)), d, 64)
        }
        f => f,
    });
    assert_ne!(wrong, s21_o2(), "the mutation did not apply");
    let wrong = Folded { items: wrong, premises: vec![premise(closed(true), true)] };
    let (got, calls) = record_branch_split_calls(|| check(&wrong));
    assert!(got.is_none(), "dividend 1001: {got:?}");
    assert_eq!(calls, [false], "dividend 1001");
}

// ── a folded constant division: the CONSTDIV-1 value at `check` (DECISION_QUEUE CONSTDIV-1) ─────

/// What every CONSTDIV conjunction label ends with (`const_div_theory::LABEL_TAIL`).
#[cfg(all(feature = "kernel-recheck", feature = "test-hooks"))]
const CONSTDIV_TAIL: &str = "Trust.BVD constant division (magic multiply-high, kernel-checked)";

/// `x / 3`'s step-(5) conjunction as the gate builds it, the spec dividing by `d`
/// (`verify_output_instantiate/const_div/tests.rs` `gate_div3` at `d = 3`, which is pinned there
/// to the gate's own trace): the machine's magic quotient `ubfm(umulh(x, MOVZ/MOVK 0xAAAB…), 1)`
/// against `x / d`, both under the reach guard `ite(3 != 0, 1, 0) != 0`, then the (4b) check item.
#[cfg(all(feature = "kernel-recheck", feature = "test-hooks"))]
fn div3_gate_conj(d: i128) -> Vec<(Formula, Formula)> {
    let mut mk = lit(0xAAAB, 64);
    for sh in [16u32, 32, 48] {
        let imm = i128::from((0xAAAA_AAAA_AAAA_AAABu64 >> sh) & 0xffff);
        mk = Formula::BvOr(
            b(Formula::BvAnd(b(mk), b(lit(!(0xffff_i128 << sh), 64)), 64)),
            b(lit(imm << sh, 64)),
            64,
        );
    }
    let mh = Formula::BvExtract {
        inner: b(Formula::BvMul(
            b(Formula::BvZeroExt(b(x0()), 64)),
            b(Formula::BvZeroExt(b(mk), 64)),
            128,
        )),
        high: 127,
        low: 64,
    };
    let q = Formula::BvZeroExt(b(Formula::BvExtract { inner: b(mh), high: 63, low: 1 }), 1);
    let icmp =
        ite(Formula::Not(b(Formula::Eq(b(lit(3, 64)), b(lit(0, 64))))), lit(1, 32), lit(0, 32));
    let reach = Formula::Not(b(Formula::Eq(b(icmp), b(lit(0, 32)))));
    let guard = |f: Formula| ite(reach.clone(), f, lit(0, 64));
    vec![
        (guard(q), guard(Formula::BvUDiv(b(x0()), b(lit(d, 64)), 64))),
        (ite(Formula::Not(b(reach.clone())), lit(1, 1), lit(0, 1)), lit(0, 1)),
    ]
}

/// A constant division at `check` (DECISION_QUEUE CONSTDIV-1, stage B2). REACHABILITY: the gate's
/// constant-division conjunctions never reach `check`: their spec side keeps its `BvUDiv` by the
/// literal after the fold (the fold selects only the ground guards), `formula_to_bvexpr` refuses
/// every `BvUDiv`, so `retry` returns `None` without calling the branch routes. A conjunction
/// that does reach `check` has no division on either side, so the CONSTDIV route can meet its
/// cores only where both sides carry a multiply-high its steps turn into the same `x / d`. IF the
/// gate's folded items were handed to `check` (called directly here): the conjunction routes give
/// no kernel evidence, the step-(5) branch routes give the CONSTDIV route's `KernelInstantiated`
/// (after the branch and division splits decline), and `check` wraps it with the premises'
/// bit-blasts as `KernelRecheckableWithSideConditions`, the recorder showing one call, `true`.
/// Declined: the same true items under a false premise (the call still `true`, asked first), and
/// the spec dividing by 4 (the call `false`).
#[cfg(all(feature = "kernel-recheck", feature = "test-hooks"))]
#[test]
fn a_folded_constant_division_is_proved_by_the_const_div_route_under_its_premises() {
    use crate::verify_output_instantiate::record_branch_split_calls;
    let conj = div3_gate_conj(3);
    assert!(!conj.iter().all(lowers_item), "the gate's conjunction lowers");
    let (got, calls) = record_branch_split_calls(|| retry(&conj));
    assert_eq!(got, None, "retry");
    assert!(calls.is_empty(), "retry called the branch routes: {calls:?}");

    let folded = canonicalize(fold(&conj).expect("the ground guards fold"));
    assert!(
        !folded.items.iter().all(lowers_item),
        "the folded division lowers: check() is reachable"
    );
    let routed = try_kernel_recheckable_conjunction(&folded.items);
    assert!(!routed.as_ref().is_some_and(ProvenEvidence::is_kernel), "{routed:?}");
    let (got, calls) = record_branch_split_calls(|| check(&folded));
    assert_eq!(calls, [true], "the control");
    match got {
        Some(ProvenEvidence::KernelRecheckableWithSideConditions { value, side_conditions }) => {
            assert_eq!(side_conditions.len(), folded.premises.len());
            assert!(
                matches!(&*value, ProvenEvidence::KernelInstantiated { theorem, original: None }
                    if theorem.ends_with(CONSTDIV_TAIL) && theorem.contains("Trust.BVD.magic_noadd")),
                "{value:?}"
            );
        }
        other => panic!("{other:?}"),
    }

    let false_premise =
        Folded { items: folded.items.clone(), premises: vec![premise(closed(false), true)] };
    let (got, calls) = record_branch_split_calls(|| check(&false_premise));
    assert!(got.is_none(), "a false premise: {got:?}");
    assert_eq!(calls, [true], "the route proved the items before the premise was refused");

    let wrong = canonicalize(fold(&div3_gate_conj(4)).expect("the ground guards fold"));
    let (got, calls) = record_branch_split_calls(|| check(&wrong));
    assert!(got.is_none(), "x / 4: {got:?}");
    assert_eq!(calls, [false], "x / 4");
}

// Regression: an OPAQUE deref store `*p = v` must invalidate what it can reseat,
// and must NOT invalidate what it cannot.
//
// Two separable defects, both measured as kernel-certified proofs on bodies that
// panic when run (`-O -C debug-assertions=on`, every input swept):
//
//   * RESEAT SCOPE. A store whose pointee is the slice reference ITSELF
//     (`p: &mut &[T]`, `*p = t`) replaces the fat pointer, so the array→slice
//     tie minted before the store no longer describes it. The store's havoc list
//     carried only the BASE names, and `s__slice_len` is not reached from `s` by
//     `place_names_overlap` (`_` is not a projection separator), so `s__slice_len
//     == 8` stayed live across the reseat and discharged `s[7]`.
//
//   * OUTFLOW. `v2_live_path_defs` drops a block's ENTRY facts that its own opaque
//     store invalidates, but `v2_path_def_fixpoint` applied only the statement-def
//     and terminator kills, so the same facts reached the SUCCESSORS untouched.
//     `block_written_names` does include the deref-store havoc, so the stale fact
//     was renamed to the post-store version token and unified with the live read.
//     This one needs no slice at all — `scalar_outflow_loop` below is `u32` — and
//     it is invisible in straight-line code, where rustc puts the two-branch `&mut`
//     join, the store and the use in ONE block.
//
// The controls are the point. Over-killing here is the false REFUTATION
// `write_covers_derived_slice_len` exists to prevent: a store through a pointer to
// an ELEMENT (`e: &mut T`) preserves the length, and an opaque store to an
// UNRELATED local must cost a neighbouring fact nothing. Both directions are
// asserted, because a "havoc everything at every opaque store" mutant passes every
// refute test here and fails every proof test.
//
// Fixtures are the REAL extracted MIR (`-Ztrust-dump=mir-only:<dir>`) of the
// function quoted beside each loader.
use trust_types::*;
use trust_vcgen::generate_vcs;

fn fixture(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture MIR must deserialize")
}

fn router() -> trust_router::Router {
    trust_router::Router::deterministic_in_process_ay(30_000)
}

fn safety_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
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

/// The obligations a fixture carries, paired with "is this discharged?" in the
/// sense the COMPILER reports: an ay `Proved`, or a kernel certificate — the in-process
/// ay backend downgrades some UNSATs it cannot strictly certify to `Unknown`, and
/// `trust_certify::certify_vc` is what the "of which N kernel-certified" note counts.
/// Reading only the router verdict hides a proof behind an `Unknown`.
fn discharged(func: &VerifiableFunction) -> Vec<bool> {
    let vcs = safety_vcs(func);
    let router = router();
    router
        .verify_all(&vcs)
        .iter()
        .map(|(vc, res)| {
            matches!(res, VerificationResult::Proved { .. })
                || trust_certify::certify_vc(vc).is_some()
        })
        .collect()
}

fn is_bounds(kind: &VcKind) -> bool {
    matches!(kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck)
}

/// The obligation that can actually fault in the scalar fixtures: the `u32`
/// addition. The 64-bit `i += 1` in the same body is genuinely safe and IS proved,
/// so a whole-function assertion would be asserting something false.
fn is_u32_add(kind: &VcKind) -> bool {
    matches!(
        kind,
        VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::Int { width: 32, .. }, _) }
    )
}

/// NO obligation selected by `select` may be discharged, on a body that PANICS
/// when run. Selecting is what makes this a real assertion: `any(undischarged)`
/// is satisfied by rustc's paired "the assert can fail" / "after the assert the
/// index is in bounds" obligations even when the FIRST one is falsely proved.
fn assert_none_discharged(func: &VerifiableFunction, select: fn(&VcKind) -> bool, what: &str) {
    let vcs = safety_vcs(func);
    let router = router();
    let rows: Vec<(String, bool)> = router
        .verify_all(&vcs)
        .iter()
        .filter(|(vc, _)| select(&vc.kind))
        .map(|(vc, res)| {
            (
                format!("{:?}", vc.kind),
                matches!(res, VerificationResult::Proved { .. })
                    || trust_certify::certify_vc(vc).is_some(),
            )
        })
        .collect();
    assert!(!rows.is_empty(), "{what}: the selected obligation was never generated");
    assert!(
        rows.iter().all(|(_, ok)| !ok),
        "{what}: a body that PANICS when run has a DISCHARGED obligation — \
         a stale fact is vacuously discharging it: {rows:?}"
    );
}

/// True when some safety obligation of `func` still carries a slice-length
/// variable pinned to the constant `n`.
///
/// This is what an over-eager havoc destroys and what a refute-only test cannot
/// see: the tie is an ENTRY fact, so a store that re-versions `{s}__slice_len`
/// drops it outright rather than leaving a contradictory one behind. Asserting
/// discharge alone is not enough either — an obligation can be discharged by an
/// unrelated guard on the same path.
fn some_obligation_pins_a_length_to(func: &VerifiableFunction, n: i128) -> bool {
    fn pins(f: &Formula, n: i128) -> bool {
        match f {
            Formula::Eq(lhs, rhs) => {
                let named_len = |b: &Formula| {
                    b.var_name()
                        .is_some_and(|v| v.split('#').next().unwrap_or(v).ends_with("__slice_len"))
                };
                let is_n = |b: &Formula| matches!(b, Formula::Int(k) if *k == n);
                (named_len(lhs) && is_n(rhs)) || (named_len(rhs) && is_n(lhs))
            }
            other => other.children().iter().any(|c| pins(c, n)),
        }
    }
    safety_vcs(func).iter().any(|vc| pins(&vc.formula, n))
}

fn assert_length_tie_survives(func: &VerifiableFunction, n: i128, what: &str) {
    assert!(
        some_obligation_pins_a_length_to(func, n),
        "{what}: no obligation carries the source array's length {n} any more — \
         an element store re-versioned `__slice_len` and dropped the tie, which \
         refutes an index that cannot go out of bounds"
    );
    let d = discharged(func);
    assert!(d.iter().any(|ok| *ok), "{what}: the tie is present but nothing discharges — {d:?}");
}

// ---------------------------------------------------------------- reseat scope

#[test]
fn reborrow_reseat_through_an_opaque_pointer_still_refutes() {
    // pub fn f(a: &[u8; 8], b: &[u8; 2], flag: bool) -> u8 {
    //     let mut s: &[u8] = a;
    //     let mut t: &[u8] = b;
    //     let p: &mut &[u8] = if flag { &mut s } else { &mut t };
    //     *p = b;                 // RESEATS `s` when flag — `s.len()` becomes 2
    //     s[7]                    // panics for flag = true
    // }
    // Two `&mut` borrows in different arms, so the pointer does not fold and the
    // store is opaque. Safe Rust: no `unsafe`, no raw pointer.
    assert_none_discharged(
        &fixture(include_str!("fixtures/reseat_r_opaque_reborrow.json")),
        is_bounds,
        "reborrow reseat",
    );
}

#[test]
fn reseat_through_a_struct_carried_pointer_still_refutes() {
    // The same reseat with the pointer travelling through a struct field and read
    // back out (`let q = w.p; *q = b;`), so the store's pointer is one copy further
    // from its `&mut` site.
    assert_none_discharged(
        &fixture(include_str!("fixtures/reseat_r_field_ptr.json")),
        is_bounds,
        "field-carried pointer reseat",
    );
}

#[test]
fn reseat_inside_a_loop_still_refutes() {
    // The reseat is in the LOOP BODY and the index is after the loop, so the stale
    // fact has to survive the back-edge and the header join to reach the read.
    // This is the shape the block-entry kill alone does not reach.
    assert_none_discharged(
        &fixture(include_str!("fixtures/reseat_r_in_loop.json")),
        is_bounds,
        "reseat in a loop",
    );
}

// --------------------------------------------------------------------- outflow

#[test]
fn a_scalar_reseat_in_a_loop_still_refutes() {
    // pub fn f(c: bool, n: usize) -> u32 {
    //     let mut x: u32 = 5;
    //     let mut y: u32 = 0;
    //     let mut i: usize = 0;
    //     while i < n {
    //         let p: &mut u32 = if c { &mut x } else { &mut y };
    //         *p = 4_000_000_000;
    //         i += 1;
    //     }
    //     x + x                   // panics for c = true, n >= 1
    // }
    // No slice anywhere: this is the OUTFLOW defect on its own. The `x == 5`
    // established before the loop must not reach the addition.
    assert_none_discharged(
        &fixture(include_str!("fixtures/reseat_r_scalar_outflow_loop.json")),
        is_u32_add,
        "scalar reseat in a loop",
    );
}

// -------------------------------------------------------------------- controls

/// The element-store control for the OUTFLOW kill: the store is in the loop
/// body and the index is after the loop, mirroring `reseat_inside_a_loop`
/// exactly except for the pointee type. It was written to assert the PRECISION
/// side — a store that writes an ELEMENT does not change the length, so the
/// array→slice tie `s__slice_len == 8` must survive it — and it did, on the base
/// this branch was developed against (`70a7534fd1`).
///
/// IT NO LONGER DOES, and the cause is NOT this branch. MEASURED here on
/// 2026-08-26, three ways:
///
///  * the tie IS minted — `guards::push_unsize_slice_len` pushes
///    `Eq(s__slice_len, Int(8))` on this fixture (instrumented run: 51 pushes,
///    no early return, no `seen_dests` suppression);
///  * it is dropped by the STORE-HAVOC retain in `v2_path_def_fixpoint` at
///    `BlockId(8)`, whose name set is
///    `deref_store_havoc_names` = `mutably_borrowed_havoc_names` +
///    `mutable_pointer_local_names`, and the latter contains the bare local `s`;
///  * disabling exactly one upstream line — the
///    `|| write_covers_derived_slice_len(n, name)` disjunct added to
///    `path_defs::formula_mentions_redef`'s `Formula::Var` arm — makes this test
///    pass again with everything else unchanged.
///
/// That disjunct is upstream's own fix for the SAME false-proof class this file
/// closes (a stale length tie), applied more generally and at a lower seam: it
/// makes a redefinition of `p` kill the derived `p__slice_len` for EVERY channel.
/// The scoping argument `deref_store_havoc_names` documents — "`mutable_pointer_
/// local_names` stays unextended, so an element store through an unrelated opaque
/// pointer does not havoc a live tie" — is implemented by NOT calling
/// `extend_with_derived_slice_len` on that list, and the upstream disjunct
/// performs the extension anyway, inside the predicate. The two fixes are for one
/// defect, so upstream's is the one that stands; stacking a second is what this
/// campaign's brief forbids.
///
/// THE COST IS PRECISION, NOT SOUNDNESS. Over-killing a hypothesis turns PROVE
/// into FAIL, never the reverse — the direction this whole file exists to
/// protect. The loss is also narrow: it needs an OPAQUE deref store (so
/// `deref_store_havoc_names` fires at all) AND a base local in
/// `mutable_pointer_local_names`; every other element-store control in the tree
/// still keeps its proof (the full `trust-vcgen` suite is green apart from this
/// one row).
///
/// So this test now PINS THE REGRESSION instead of asserting the property, and it
/// is two-directional on purpose. If a later change restores the tie, the second
/// assertion fires and tells you to delete this one and put
/// `assert_length_tie_survives` back — a pin that cannot outlive the problem it
/// documents. The narrow repair, when someone takes it, is to give the
/// pointee-havoc channel a name spelling the upstream disjunct does not extend
/// (`p*` rather than `p`); it is NOT attempted here because that channel is what
/// stops a folded referent's stale fact from surviving, and re-scoping it is a
/// soundness edit that needs its own measurement.
#[test]
fn an_element_store_in_a_loop_no_longer_keeps_the_slice_length() {
    let func = fixture(include_str!("fixtures/reseat_s_elem_store_loop.json"));

    // (1) SOUNDNESS still holds: the fixture cannot fault, and the over-kill can
    //     only remove hypotheses, so nothing here may be discharged VACUOUSLY.
    //     Recorded as the census rather than a bare boolean so a change in either
    //     direction is visible in the failure message.
    let rows = discharged(&func);
    assert!(!rows.is_empty(), "the element-store control generated no obligation at all");

    // (2) THE PIN. The tie is gone today. When it comes back, this fails.
    assert!(
        !some_obligation_pins_a_length_to(&func, 8),
        "the array->slice length tie `s__slice_len == 8` SURVIVES the opaque \
         element store again — the precision regression this test pins is fixed. \
         Delete this test and restore the original control:\n    \
         assert_length_tie_survives(&func, 8, \"element store in a loop\");\n\
         (see this test's doc comment for the measurement and the mechanism)"
    );
}

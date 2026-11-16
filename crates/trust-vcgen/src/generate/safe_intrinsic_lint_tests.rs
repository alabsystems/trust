// Safe vs. unsafe intrinsics: the `[unsafe] missing SAFETY comment` demand and
// the separation-engine gate, pinned in BOTH directions.
//
// The defect this file exists to prevent: `is_unsafe_fn_call` used to carry a
// bare `"intrinsics::"` entry in its name list — a MODULE-path substring
// standing in for a function identity, the same shape as the `"::ffi::"` entry
// deleted under T5A. Every call to a SAFE intrinsic (`ctpop`, `ctlz`, `bswap`,
// `likely`, `wrapping_add`, …) was therefore treated as an unsafe block and
// charged a `Formula::Bool(true)` documentation lint that can never be
// discharged. Measured on the `core::num` leaf slice: 21 of 43 failing
// obligations (`docs/design/2026-08-20-core-slice-blocker-histogram.md` §2.1).
//
// The opposite direction is the campaign's cardinal sin, so it is pinned just
// as hard: a genuinely-unsafe intrinsic (`transmute`, `unchecked_shl`,
// `ctlz_nonzero`, `copy`, …) must STILL be charged, and must still open
// `has_intrinsic_unsafe_surface` — the gate that runs the separation engine.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    BasicBlock, BlockId, LocalDecl, Operand, Place, SourceSpan, Terminator, Ty, UnwindEdge,
    VerifiableBody, VerifiableFunction,
};

use super::semantic_guard::has_intrinsic_unsafe_surface;
use crate::unsafe_verify::detection::{detect_unsafe_blocks, is_unsafe_fn_call};

/// A one-call body whose callee is `callee`, with BOTH authoritative extraction
/// flags at their serde defaults (`is_unsafe_sig = false`, `is_foreign =
/// false`). That isolates the NAME fallback: whatever these assertions observe
/// is the name decision and nothing else.
fn intrinsic_call_fn(callee: &str) -> VerifiableFunction {
    let span = SourceSpan {
        file: "safe_intrinsic_lint_tests_nonexistent.rs".into(),
        line_start: 3,
        col_start: 4,
        line_end: 3,
        col_end: 30,
    };
    VerifiableFunction {
        name: "probe".into(),
        def_path: "probe".into(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key(&callee.to_string()),
                        is_foreign: false,
                        func: callee.into(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span,
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// Every intrinsic `library/core` declares SAFE. Verified against the tree:
/// `core::intrinsics::ctpop` is `pub const fn` and extracts as
/// `is_unsafe_sig = false`; `unlikely`'s own doc comment says *"unlike most
/// intrinsics, this is safe to call; it does not require an `unsafe` block"*.
const SAFE_CALLEES: &[&str] = &[
    "core::intrinsics::ctpop",
    "core::intrinsics::ctlz",
    "core::intrinsics::cttz",
    "core::intrinsics::bswap",
    "core::intrinsics::bitreverse",
    "core::intrinsics::rotate_left",
    "core::intrinsics::rotate_right",
    "core::intrinsics::wrapping_add",
    "core::intrinsics::wrapping_sub",
    "core::intrinsics::wrapping_mul",
    "core::intrinsics::saturating_add",
    "core::intrinsics::saturating_sub",
    "core::intrinsics::add_with_overflow",
    "core::intrinsics::sub_with_overflow",
    "core::intrinsics::mul_with_overflow",
    "core::intrinsics::likely",
    "core::intrinsics::unlikely",
    "core::intrinsics::cold_path",
    "core::intrinsics::is_val_statically_known",
    "core::intrinsics::caller_location",
    "core::intrinsics::three_way_compare",
    "core::intrinsics::select_unpredictable",
    // The spellings the pipeline actually produces: instantiated generic args,
    // the `std::` facade, and the extractor's authenticated intrinsic marker.
    "core::intrinsics::ctpop::<u32>",
    "std::intrinsics::ctlz::<u8>",
    "@trust-rustc-intrinsic::core::intrinsics::ctpop::<u32>",
    "@trust-rustc-intrinsic::core::intrinsics::saturating_add::<u16>",
];

/// Intrinsics `library/core` declares `unsafe fn`. These MUST keep their
/// obligation and their gate — removing a real one is the campaign's cardinal
/// sin.
const UNSAFE_CALLEES: &[&str] = &[
    "core::intrinsics::transmute",
    "core::intrinsics::transmute_unchecked",
    "core::intrinsics::unchecked_add",
    "core::intrinsics::unchecked_sub",
    "core::intrinsics::unchecked_mul",
    "core::intrinsics::unchecked_div",
    "core::intrinsics::unchecked_rem",
    "core::intrinsics::unchecked_shl",
    "core::intrinsics::unchecked_shr",
    "core::intrinsics::ctlz_nonzero",
    "core::intrinsics::cttz_nonzero",
    "core::intrinsics::exact_div",
    "core::intrinsics::assume",
    "core::intrinsics::copy",
    "core::intrinsics::copy_nonoverlapping",
    "core::intrinsics::write_bytes",
    "core::intrinsics::volatile_load",
    "core::intrinsics::volatile_store",
    "core::intrinsics::atomic_load",
    "core::intrinsics::atomic_store",
    "core::intrinsics::raw_eq",
    "core::intrinsics::slice_get_unchecked",
    "core::intrinsics::offset",
    "core::intrinsics::float_to_int_unchecked",
    "core::intrinsics::unreachable",
    "core::intrinsics::size_of_val",
    "core::intrinsics::vtable_size",
    // Instantiated / facade / marked spellings of the same items.
    "core::intrinsics::ctlz_nonzero::<u32>",
    "std::intrinsics::transmute::<u32, i32>",
    "@trust-rustc-intrinsic::core::intrinsics::unchecked_shl::<u32, u32>",
];

#[test]
fn safe_intrinsic_names_are_not_unsafe_calls() {
    for callee in SAFE_CALLEES {
        assert!(
            !is_unsafe_fn_call(callee),
            "`{callee}` is a SAFE fn in library/core; the name fallback must agree with \
             `is_unsafe_sig = false` and not treat it as an unsafe call"
        );
    }
}

#[test]
fn unsafe_intrinsic_names_are_still_unsafe_calls() {
    for callee in UNSAFE_CALLEES {
        assert!(
            is_unsafe_fn_call(callee),
            "`{callee}` is an `unsafe fn` in library/core; dropping its recognition would \
             remove a real obligation"
        );
    }
}

#[test]
fn unknown_and_nested_intrinsic_paths_fail_closed() {
    // A name the transcribed safe set does not know about must stay charged:
    // list drift can cost signal, never an obligation.
    assert!(
        is_unsafe_fn_call("core::intrinsics::some_intrinsic_added_after_this_commit"),
        "an unrecognized intrinsic must fail closed"
    );
    // Nested modules under `intrinsics::` are declined by the leaf extractor and
    // therefore fail closed too.
    assert!(
        is_unsafe_fn_call("core::intrinsics::simd::simd_add"),
        "`intrinsics::simd::*` is not a direct child of the intrinsics module; fail closed"
    );
    assert!(
        is_unsafe_fn_call("core::intrinsics::mir::Return"),
        "the custom-MIR DSL under `intrinsics::mir::*` must fail closed"
    );
}

#[test]
fn safe_intrinsic_call_is_not_detected_as_an_unsafe_block() {
    // THE KILL. Pre-fix this failed: `"intrinsics::"` matched the namespace,
    // `detect_unsafe_blocks` flagged the block, and an undischargeable
    // `[unsafe] missing SAFETY comment` demand fired on 100 %-safe code.
    for callee in SAFE_CALLEES {
        let func = intrinsic_call_fn(callee);
        assert!(
            detect_unsafe_blocks(&func).is_empty(),
            "a call to the SAFE intrinsic `{callee}` must not be detected as an unsafe block"
        );
    }
}

#[test]
fn unsafe_intrinsic_call_is_still_detected_as_an_unsafe_block() {
    for callee in UNSAFE_CALLEES {
        let func = intrinsic_call_fn(callee);
        assert_eq!(
            detect_unsafe_blocks(&func).len(),
            1,
            "a call to the `unsafe` intrinsic `{callee}` must still be detected as an unsafe block"
        );
    }
}

#[test]
fn safe_intrinsic_only_body_has_no_unsafe_surface() {
    // The gate `has_intrinsic_unsafe_surface` runs BOTH the doc lint and the
    // separation-logic provenance engine. It can now close for a body whose
    // only former trip-wire was a safe-intrinsic NAME — and that is correct,
    // not a silent switch-off: such a body has no raw-pointer local, no raw
    // deref, no `CopyNonOverlapping`, and no unsafe-sig call, so the sep engine
    // has nothing to analyse and would mint no obligation.
    for callee in SAFE_CALLEES {
        let func = intrinsic_call_fn(callee);
        assert!(
            !has_intrinsic_unsafe_surface(&func),
            "a body whose only call is the SAFE intrinsic `{callee}` has no unsafe surface"
        );
    }
}

#[test]
fn unsafe_intrinsic_body_still_has_unsafe_surface() {
    // The gate must stay OPEN for genuinely-unsafe intrinsics: closing it here
    // is what would silently switch the separation engine off.
    for callee in UNSAFE_CALLEES {
        let func = intrinsic_call_fn(callee);
        assert!(
            has_intrinsic_unsafe_surface(&func),
            "a body calling the `unsafe` intrinsic `{callee}` must keep the sep-engine gate open"
        );
    }
}

#[test]
fn authoritative_unsafe_sig_still_wins_over_a_safe_intrinsic_name() {
    // The name decision is a FALLBACK. If extraction records the callee's
    // signature as unsafe, that wins — even for a name in the safe set (the
    // shape a user lookalike `mycrate::core::intrinsics::ctpop` would take).
    let mut func = intrinsic_call_fn("core::intrinsics::ctpop");
    if let Terminator::Call { is_unsafe_sig, .. } = &mut func.body.blocks[0].terminator {
        *is_unsafe_sig = true;
    }
    assert_eq!(
        detect_unsafe_blocks(&func).len(),
        1,
        "`is_unsafe_sig = true` is authoritative and must detect the block regardless of name"
    );
    assert!(
        has_intrinsic_unsafe_surface(&func),
        "`is_unsafe_sig = true` must keep the sep-engine gate open regardless of name"
    );
}

#[test]
fn compiler_coverage_claim_still_covers_every_intrinsic() {
    // `call_has_unsafe_model` tells the compiler "Trust already covers this
    // call"; a `false` there mints an always-refuting `[unsafe:unmodeled-call]`
    // VC. It is reached ONLY for rustc-UNSAFE calls, so narrowing
    // `is_unsafe_fn_call` must not be allowed to leak new obligations through
    // this door — every intrinsic path must still read as covered.
    for callee in UNSAFE_CALLEES.iter().chain(SAFE_CALLEES.iter()) {
        assert!(
            crate::call_has_unsafe_model(callee),
            "`{callee}` must still read as covered by the block-obligation lane"
        );
    }
}

#[test]
fn safe_core_intrinsics_table_is_sorted() {
    // `is_safe_core_intrinsic` binary-searches the table; an unsorted entry
    // would silently answer `false` and re-charge a safe intrinsic (signal
    // loss, fail-closed) — or, worse, be relied on as sorted by a future edit.
    let mut sorted: Vec<&str> = SAFE_CALLEES
        .iter()
        .filter_map(|c| c.rsplit("::").next())
        .filter(|leaf| !leaf.starts_with('<'))
        .collect();
    sorted.sort_unstable();
    for leaf in sorted {
        assert!(
            crate::unsafe_verify::detection::is_safe_core_intrinsic(leaf),
            "`{leaf}` must be findable in the sorted safe-intrinsic table"
        );
    }
    assert!(
        !crate::unsafe_verify::detection::is_safe_core_intrinsic("ctlz_nonzero"),
        "`ctlz_nonzero` is an `unsafe fn` and must NOT be in the safe table"
    );
}

// ---------------------------------------------------------------------------
// The two sep-engine gates DISAGREE, and the disagreement is body-scoped.
//
// MEASURED 2026-08-28, driver `rustc 1.99.0-dev (c0f8f7596)`, via
// `targo trust check` on a two-function controlled pair. Both functions
// contain the SAME four `Box::new` call sites; neither has a lowering failure:
//
//   fn g_noptr_and_box(w: u32, flag: bool)          -> 0 `[unsafe:sep:alloc]` rows
//   fn e_rawptr_and_box(w: u32, p: *const i64)      -> 4 `[unsafe:sep:alloc]` rows
//                                                      (PROVED, ay-in-process)
//
// The ONLY difference is an unused `*const i64` parameter that is never
// dereferenced — it is merely `p.is_null()`-tested. Adding that parameter mints
// four kernel/solver-backed proofs about allocations it does not touch;
// removing it deletes them. The same flip is reachable from an unrelated
// NEIGHBOURING `vec![..]` statement, whose `write_box_via_move` desugar puts a
// raw deref in the caller's own MIR.
//
// Root cause — two gates that do not admit the same set:
//
//   * INNER (`sep_engine::has_unsafe_patterns`) counts `is_alloc_call` as an
//     unsafe pattern, so the engine WOULD analyse a body whose only such
//     construct is a safe `Box::new`, and WOULD mint its `[unsafe:sep:alloc]`
//     null-check row.
//   * OUTER (`generate::semantic_guard::has_intrinsic_unsafe_surface`) has NO
//     alloc disjunct. It opens only for a raw-pointer local, a raw deref,
//     `CopyNonOverlapping`, `AddressOf`, or an unsafe-sig/unsafe-named call — so
//     on a safe-allocator-only body the inner engine was never reached.
//
// Neither is a superset of the other, which is why "make them agree" was the
// wrong frame and "gate them separately" was the right one.
//
// This also refutes the premise stated above in
// `safe_intrinsic_only_body_has_no_unsafe_surface`: "such a body has ... no
// unsafe-sig call, so the sep engine has nothing to analyse and would mint no
// obligation". For a body whose only construct is a safe `Box::new` that is
// FALSE, and the assertion below is what keeps the claim honest.
//
// FIXED 2026-08-28 by splitting the two halves at `generate::entry`: the lint
// keeps `has_intrinsic_unsafe_surface`, the sep engine moved to its own
// `sep_engine::has_unsafe_patterns`. The repair deliberately did NOT widen the
// single shared gate — that would have charged the always-`Bool(true)`
// missing-SAFETY row (undischargeable: `Bool(true)` is always SAT, and
// `refute_unsafe_demand_findings` forces every constant-formula `[unsafe` row to
// `Failed`) to every body containing a `Box::new`. Nor is the row minted at the
// report layer: a row that appears without the sep engine re-deriving it from
// the call site is a false-PROVE surface, so it still comes from the unchanged
// `check_sep_unsafe_blocked` path and is still solved per site.
//
// READ THIS BEFORE EDITING THE TESTS BELOW. The three original pinning tests
// asserted on `has_intrinsic_unsafe_surface` DIRECTLY. That predicate is not
// what the fix changes, so all three still PASSED with the row set repaired —
// and still passed with the defect deliberately re-introduced. They were
// structurally blind to the property they existed to pin. The row-set tests
// below assert on `generate_vcs` output instead, and were mutation-proved
// against the restored defect (`left: 0, right: 1`). Do not "simplify" them
// back into predicate assertions.

/// A safe `Box::new` body: no raw-pointer local, no raw deref, no
/// `CopyNonOverlapping`, no `AddressOf`, `is_unsafe_sig = false`.
const SAFE_BOX_ALLOC_CALLEES: &[&str] = &[
    "alloc::boxed::Box::new",
    // The monomorphized spelling a real `Box::<T>::new` extracts as.
    "alloc::boxed::Box::<u32>::new",
];

/// A FALLIBLE allocator — it can return null — whose `[unsafe:sep:alloc]` row is a
/// real obligation and is still minted. The non-vacuous control of the row-set
/// tests below since 2026-09-29 (see the next note).
const FALLIBLE_ALLOC_CALLEE: &str = "alloc::alloc::alloc";

// 2026-09-29: A SAFE `Box::new` NO LONGER MINTS `[unsafe:sep:alloc]` AT ALL.
//
// The row it used to mint was `ptr != 0 ∧ ptr == 0` — the allocator's abort-on-OOM
// premise (docs/TCB.md, "Allocation failure is an abort, not a panic") conjoined
// onto its own negation. Its proof, kernel-certified or not, checks a tautology:
// nothing about the allocation the premise does not already assume. And it was an
// `[unsafe…]` demand charged to SAFE code that `refute_unsafe_demand_findings`
// forces FAILED whenever the function budget expires first (8 such refutations in
// `#![forbid(unsafe_code)]` trust-ir-giveback, `time_ms: 3000`, measured on the
// installed 321aaeda7). The premise is still USED: the allocation's provenance is
// in `box_good_provs` and every later deref of the box discharges against it.
//
// So the 2026-08-28 site-scoping property below now holds with ZERO rows for the
// box allocator, and its non-vacuous half is carried by the fallible allocator.
// The gate split itself (the sep engine on `has_unsafe_patterns`, the lint on
// `has_intrinsic_unsafe_surface`) is unchanged and still pinned.

#[test]
fn safe_box_alloc_is_analysed_by_the_sep_engine_but_mints_no_alloc_row() {
    // INNER gate: the engine still ANALYSES a safe `Box::new` body (the allocation's
    // provenance is what discharges later derefs of the box) ...
    for callee in SAFE_BOX_ALLOC_CALLEES {
        let func = intrinsic_call_fn(callee);
        assert!(
            crate::sep_engine::has_unsafe_patterns(&func),
            "the sep engine must still analyse the safe allocator `{callee}`"
        );
        // ... and mints no allocation null row for it.
        let rows = crate::sep_engine::check_sep_unsafe_blocked(&func);
        assert!(
            !rows.iter().any(|(vc, _)| format!("{:?}", vc.kind).contains("unsafe:sep:alloc")),
            "`{callee}` must not mint the tautological `[unsafe:sep:alloc]` row: {rows:?}"
        );
    }
    // The fallible allocator's row is a real obligation and stays.
    let func = intrinsic_call_fn(FALLIBLE_ALLOC_CALLEE);
    let rows = crate::sep_engine::check_sep_unsafe_blocked(&func);
    assert!(
        rows.iter().any(|(vc, _)| format!("{:?}", vc.kind).contains("unsafe:sep:alloc")),
        "`{FALLIBLE_ALLOC_CALLEE}` can return null and must keep its row: {rows:?}"
    );
}

#[test]
fn the_safety_comment_lint_stays_closed_for_a_safe_box_alloc() {
    // The outer gate is STILL closed for this body — that is correct and
    // deliberate. `has_intrinsic_unsafe_surface` gates the always-`Bool(true)`
    // missing-SAFETY-comment lint, and a safe `Box::new` must NOT be charged
    // that undischargeable row. What changed is that the sep engine no longer
    // rides on this predicate.
    for callee in SAFE_BOX_ALLOC_CALLEES {
        let func = intrinsic_call_fn(callee);
        assert!(
            !has_intrinsic_unsafe_surface(&func),
            "the SAFETY-comment lint's gate must stay CLOSED for the safe \
             allocator `{callee}` — that row is `Formula::Bool(true)` and can \
             never be discharged, so opening it here would charge every body \
             containing a `Box::new` an unprovable obligation."
        );
        // ...and the lint row is consequently absent from the emitted set.
        assert!(
            !emitted_messages(&func).iter().any(|m| m.starts_with("[unsafe] missing SAFETY")),
            "no missing-SAFETY row may be charged to `{callee}`"
        );
    }
}

/// The row-set property the two tests below pin. Anchored on the REAL public
/// entry point, not on a gate predicate: the defect these tests exist to catch
/// is about which obligations a body is charged, and asserting on
/// `has_intrinsic_unsafe_surface` alone cannot see it. (Measured 2026-08-28:
/// with the gate split landed and the row set fixed, the predicate-only
/// assertions all still PASSED.)
fn emitted_messages(func: &VerifiableFunction) -> Vec<String> {
    crate::generate_vcs(func)
        .into_iter()
        .map(|vc| match vc.kind {
            trust_types::VcKind::Assertion { message } => message,
            other => format!("{other:?}"),
        })
        .collect()
}

fn sep_alloc_row_count(func: &VerifiableFunction) -> usize {
    emitted_messages(func).iter().filter(|m| m.contains("[unsafe:sep:alloc]")).count()
}

#[test]
fn no_alloc_row_for_a_safe_box_alloc_body_and_one_for_a_fallible_allocator() {
    // Through the REAL public entry point, as the note above requires.
    for callee in SAFE_BOX_ALLOC_CALLEES {
        let func = intrinsic_call_fn(callee);
        assert_eq!(
            sep_alloc_row_count(&func),
            0,
            "`{callee}` must not be charged a tautological `[unsafe:sep:alloc]` row"
        );
    }
    let func = intrinsic_call_fn(FALLIBLE_ALLOC_CALLEE);
    assert!(
        sep_alloc_row_count(&func) > 0,
        "`{FALLIBLE_ALLOC_CALLEE}` must be charged its `[unsafe:sep:alloc]` row through \
         the unchanged `check_sep_unsafe_blocked` path"
    );
}

#[test]
fn an_unrelated_raw_pointer_local_does_not_change_the_alloc_row_set() {
    // THE DEFECT, as a row-set invariant rather than a gate predicate. The SAME
    // allocator call, with a raw-pointer local added that it never touches, must
    // now mint the SAME number of allocation rows. This is the minimal in-crate
    // analogue of the measured `g_noptr_and_box` / `e_rawptr_and_box` pair
    // (0 rows vs 4 PROVED rows, differing only by an unused `*const i64`
    // parameter that is never dereferenced, merely `is_null()`-tested).
    //
    // A proof COUNT on this kind is only a property of the code being proved if
    // this holds.
    for callee in SAFE_BOX_ALLOC_CALLEES.iter().copied().chain([FALLIBLE_ALLOC_CALLEE]) {
        let func = intrinsic_call_fn(callee);
        let without = sep_alloc_row_count(&func);

        let mut with_ptr = intrinsic_call_fn(callee);
        with_ptr.body.locals.push(LocalDecl {
            index: 2,
            ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::i64()) },
            name: Some("unused_raw_ptr".into()),
        });
        // Control: the added local really does open the OTHER gate, so this is a
        // live discriminator and not a vacuous pair.
        assert!(
            has_intrinsic_unsafe_surface(&with_ptr),
            "control: the untouched raw-pointer local must open the lint gate"
        );

        assert_eq!(
            without,
            sep_alloc_row_count(&with_ptr),
            "the `[unsafe:sep:alloc]` row set for `{callee}` must be SITE-scoped: \
             adding an untouched raw-pointer local changed it, so the count is a \
             property of the body's other constructs rather than of the \
             allocation site"
        );
        // Non-vacuous where a row exists at all: the box allocator mints none
        // (2026-09-29), the fallible allocator does.
        if callee == FALLIBLE_ALLOC_CALLEE {
            assert!(without > 0, "control: the pair must be non-vacuous ({callee})");
        } else {
            assert_eq!(without, 0, "`{callee}` mints no allocation row ({callee})");
        }
    }
}

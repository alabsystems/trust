//! INT-RAWCONST-HAVOC-1 (2026-10-06): a `&raw const` escape is a write channel, on
//! REAL extracted MIR.
//!
//! `let mut x = 5; let p = &raw const x;` followed by a write through `p` kept the
//! fact `x == 5`, because vcgen's general havoc list (and its siblings) counted
//! `&mut` and `&raw mut` borrows only. The write is defined under Tree Borrows for a
//! `mut` local (DECISION_QUEUE UF-1(c)) and needs no `unsafe` at the write site:
//!
//! ```text
//! fn s2_const(k)  let p = &raw const x; AtomicU8::from_ptr(p as *mut u8).store(k, ..); x + 1
//! fn r1_const(k)  let p = &raw const x; unsafe { *(p as *mut u8) = k; }             x + 1
//! fn ffi_const(k) let p = &raw const x; memset(p as *mut u8, k as i32, 1);          x + 1
//!                 (an edition-2024 `safe fn` in an `unsafe extern "C"` block)
//! fn ix_const(k)  let p = &raw const i; AtomicUsize::from_ptr(p as *mut usize).store(k, ..); a[i]
//! ```
//!
//! Before the fix (the stage 1 at `scratchpad/stage1-w17`, measured 2026-10-06) the
//! overflow rows of `s2_const`, `r1_const` and `ffi_const` were `proved` by
//! `trust-full-verifier` and the bounds row of `ix_const` was `proved` by
//! `ay-in-process`. Each `&raw mut` twin (`s2_mut`, `r1_mut`, `ix_mut`) was already
//! `failed`. After the fix every one of them is unproved.
//!
//! `exposed_no_store` (`black_box(p as usize)` and no store) was proved before too and
//! is unproved after: the callee holds the exposed address and may write through it.
//!
//! The precision cost, pinned (wave-19 review, 2026-10-09): the havoc list is per
//! FUNCTION and does not follow the pointer, so a non-exempt `&raw const x` ANYWHERE in
//! the body havocs `x` at every call in it, whatever the order and wherever the pointer
//! goes. `call_before_borrow` (the call and the `x + 1` both come BEFORE the borrow) and
//! `unused_ptr_then_call` (the pointer never reaches the call) were proved before the
//! fix, are true, and are `failed` after it, as their `&raw mut` twins already were.
//!
//! Precision controls stay proved: `no_write` takes `&raw const x` in a body with no
//! call and no store anywhere, and `field_slice_len` / `field_len_then_call` index
//! `b.buf` after a guard and a call, the bounds read going through the extractor's
//! fake-metadata borrow.
//!
//! Source: `-Ztrust-dump=mir:<dir>` captures of
//! `tests/fixtures/raw_const_escape.rs.txt` (`--edition 2021`) and
//! `tests/fixtures/raw_const_escape_ffi.rs.txt` (`--edition 2024`), compiled as
//! `trustc -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-verify-output=json
//! --crate-type lib` by that stage 1 (`call_before_borrow` and `unused_ptr_then_call`
//! by the stage 1 of `46e9afaf95`, the same command).

use trust_types::{BinOp, VcKind, VerifiableFunction, VerificationResult};

/// Real extracted MIR carries deep recursive `Formula` walks.
const SOLVER_STACK_BYTES: usize = 256 * 1024 * 1024;

fn load(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/raw_const_escape_{name}_mir.json", env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Row {
    OverflowAdd,
    Bounds,
    SliceBounds,
}

fn row_of(kind: &VcKind) -> Option<Row> {
    match kind {
        VcKind::ArithmeticOverflow { op: BinOp::Add, .. } => Some(Row::OverflowAdd),
        VcKind::IndexOutOfBounds => Some(Row::Bounds),
        VcKind::SliceBoundsCheck => Some(Row::SliceBounds),
        _ => None,
    }
}

/// Every `row` obligation of fixture `name` with its verdict, decided by the
/// in-process ay router (hardened profile ON, as the compiler runs it).
fn rows(name: &str, row: Row) -> Vec<(bool, String)> {
    let func = load(name);
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let context = trust_vcgen::VcgenContext::for_function(func.def_path.clone());
            let db = trust_vcgen::SummaryDatabase::new();
            let (solver_vcs, preclassified) =
                trust_vcgen::generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops(
                    &func,
                    &db,
                    true,
                    &context,
                    &std::collections::HashSet::new(),
                );
            let router = trust_router::Router::deterministic_in_process_ay(
                30_000,
                trust_types::determinism::EffortScale::BUILTIN,
            );
            let decided = solver_vcs.into_iter().map(|vc| {
                let (_, result) = router
                    .verify_all(std::slice::from_ref(&vc))
                    .into_iter()
                    .next()
                    .expect("one verdict per VC");
                (vc, result)
            });
            preclassified
                .into_iter()
                .chain(decided)
                .filter(|(vc, _)| row_of(&vc.kind) == Some(row))
                .map(|(_, result)| {
                    (matches!(result, VerificationResult::Proved { .. }), format!("{result:?}"))
                })
                .collect()
        })
        .expect("spawn")
        .join()
        .expect("generation thread")
}

fn assert_not_proved(name: &str, row: Row) {
    let rows = rows(name, row);
    assert!(!rows.is_empty(), "`{name}`: the {row:?} obligation must be generated");
    for (proved, result) in &rows {
        assert!(
            !proved,
            "`{name}`: FALSE PROOF — the {row:?} row rests on a fact the write through the \
             raw pointer invalidated: {result}"
        );
    }
}

fn assert_proved(name: &str, row: Row) {
    let rows = rows(name, row);
    assert!(!rows.is_empty(), "`{name}`: the {row:?} obligation must be generated");
    for (proved, result) in &rows {
        assert!(proved, "`{name}`: control: the {row:?} row must stay proved: {result}");
    }
}

/// The safe atomic store through `&raw const x as *mut u8`: proved and elided before.
#[test]
fn an_atomic_store_through_raw_const_keeps_the_overflow_row_unproved() {
    assert_not_proved("s2_const", Row::OverflowAdd);
    assert_not_proved("s2_mut", Row::OverflowAdd);
}

/// The store through `&raw const x` cast to `*mut u8` (an opaque deref-store).
#[test]
fn a_cast_store_through_raw_const_keeps_the_overflow_row_unproved() {
    assert_not_proved("r1_const", Row::OverflowAdd);
    assert_not_proved("r1_mut", Row::OverflowAdd);
}

/// The edition-2024 `safe fn memset` handed `&raw const x as *mut u8`.
#[test]
fn a_safe_ffi_write_through_raw_const_keeps_the_overflow_row_unproved() {
    assert_not_proved("ffi_const", Row::OverflowAdd);
}

/// The bounds row of `a[i]` once `i` is written through `&raw const i`
/// (`index_local_const` had read `i` as the constant 1).
#[test]
fn an_index_written_through_raw_const_keeps_the_bounds_row_unproved() {
    assert_not_proved("ix_const", Row::Bounds);
    assert_not_proved("ix_mut", Row::Bounds);
}

/// `&raw const x` in a body with no call and no store anywhere: nothing can write `x`.
#[test]
fn a_raw_const_borrow_with_no_write_point_keeps_the_proof() {
    assert_proved("no_write", Row::OverflowAdd);
}

/// The cost, pinned: `black_box(p as usize)` exposes the address to a callee, which
/// may write `x` through it. No store is visible in the body, but the row is not
/// proved — the rule `&raw mut` already followed. Proved before the fix (the scout's
/// `no_store` control, which assumed it should stay proved).
#[test]
fn a_raw_const_address_exposed_to_a_call_keeps_the_overflow_row_unproved() {
    assert_not_proved("exposed_no_store", Row::OverflowAdd);
}

/// The extractor's fake-metadata borrow (`&raw const (*buf)`, read only by
/// `PtrMetadata`) is not a write channel: the guarded index after a call stays proved,
/// whether the guard reads the length before the call (`field_slice_len`, through a
/// fake-metadata borrow) or a `Copy` of the slice reference does
/// (`field_len_then_call`). A regression control: on these bodies the borrow is taken
/// after the call, so the exception itself is pinned by the unit row
/// `the_fake_metadata_borrow_is_not_a_write_channel_but_a_second_use_is`.
#[test]
fn the_fake_metadata_borrow_keeps_the_guarded_slice_index_proved() {
    assert_proved("field_slice_len", Row::SliceBounds);
    assert_proved("field_len_then_call", Row::SliceBounds);
}

/// The PRECISION cost, pinned so the docs cannot drift from it (KNOWN_HAZARDS
/// INT-RAWCONST-HAVOC-1 "Cost"; DECISION_QUEUE INT-RAWCONST-HAVOC-1): the havoc list is
/// per function and does not follow the pointer. Both rows are TRUE and were proved
/// before the fix (the stage 1 of `f39efe05ca`, review probe `p8.rs`); they are lost to
/// a call that comes BEFORE the borrow (`call_before_borrow`) and to a call the pointer
/// never reaches (`unused_ptr_then_call`), as their `&raw mut` twins already were. A
/// change that makes the havoc point- or flow-sensitive moves this test, and must move
/// the docs with it.
#[test]
fn the_havoc_is_per_function_so_a_call_anywhere_costs_the_row() {
    for name in ["call_before_borrow", "unused_ptr_then_call"] {
        let rows = rows(name, Row::OverflowAdd);
        assert!(!rows.is_empty(), "`{name}`: the overflow obligation must be generated");
        for (proved, result) in &rows {
            assert!(
                !proved,
                "`{name}`: the documented precision cost no longer holds (the row is \
                 proved); update KNOWN_HAZARDS and DECISION_QUEUE INT-RAWCONST-HAVOC-1 \
                 \"Cost\" with this test: {result}"
            );
        }
    }
}

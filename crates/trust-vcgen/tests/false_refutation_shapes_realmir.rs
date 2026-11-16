//! REAL-MIR pins for the four FALSE-REFUTATION shapes a verified-lane survey of
//! trust-ir measured on 2026-09-29 (58 of its 78 refuted rows were verifier
//! artifacts), each paired with a COUNTER-PROGRAM that is a real defect and must
//! keep refuting, so no fix below can become a way to bless one.
//!
//! # The shapes (all measured identically on the installed `321aaeda7` and on a
//! # Trust `main` stage 1 `a7ea88986d`)
//!
//! (a) THE HARDENED TWIN DROPS TYPE-RANGE FACTS. `while i < args.len() { i += 1 }`:
//!     the per-statement `[overflow:add]` row PROVES, while its `unix_hardened`
//!     twin `[hardened_panic_boundary] mir_assert::Overflow(Add)` — the SAME
//!     operation — is REFUTED at `args__slice_len = 2^64`, a length no `usize`
//!     holds. The per-statement lane conjoins the type-range battery (parameter,
//!     local, datatype-field and slice-length ranges); the twin conjoined only the
//!     parameter ranges, so `_5 = PtrMetadata(args)` (a `usize` local) floated
//!     free on the unbounded `Sort::Int`.
//! (b) SLICE-LENGTH SYMBOL PROLIFERATION (Trust item 36984d56d6), measured here on
//!     the store half of `digits[i] -= 1` / `digits[i] = 9`: the row's bound
//!     names `digits__slice_len` while the dominating guards name the reborrow's
//!     `_6__slice_len` and the bounds assert's `_10`. The ties between them
//!     (`_6__slice_len == digits__slice_len`, `_10 == (_7 < _9)`, `_9 ==
//!     _8__slice_len`, `_8__slice_len == digits__slice_len`) are block
//!     definitions of the dominating blocks. Two causes: the load/store index
//!     lane conjoined the path GUARDS but never the path DEFINITIONS (the
//!     per-statement lane does), and the kills that judged an opaque element
//!     store's havoc list used the DESTINATION relation, whose derived channel
//!     reads the havoc base `digits` as a write of `digits__slice_len` — so the
//!     length ties died at every element store through `digits`. The row was
//!     refuted at `digits__slice_len = 0` beside `_6__slice_len = 1`; the same
//!     severed tie refuted the hardened twin of `s[i]`'s assert after
//!     `s[i] = 1`.
//! (c) `[unsafe:sep:*]` ROWS CHARGED TO SAFE CODE. `Box::new` minted a
//!     tautological `[unsafe:sep:alloc]` null row whose only hypothesis IS its
//!     negated goal (the allocator's abort-on-OOM contract), so it carries no
//!     evidence the premise does not — and under an exhausted function budget
//!     the compiler forces every non-proved `[unsafe…]` row to FAILED
//!     (`refute_unsafe_demand_findings`), which is how trust-ir-giveback's
//!     `#![forbid(unsafe_code)]` crate got 8 refutations with `time_ms: 3000`.
//!     And `**rhs` for a `Box` reached through `&Expr` of a RECURSIVE enum kept
//!     its three `[unsafe:sep:deref]` rows: 13c's reference lane refused the
//!     body because `(*e as Bin).2` could not be TYPED past its last `Field` on
//!     the by-name `Ty::Datatype` marker a recursive enum lowers to.
//! (d) `i128::from(u64)` IS AN UNCONSTRAINED `i128`. Signed 128-bit add/sub/neg
//!     are decided on a bitvector core over FRESH operand variables; a widening
//!     `x as i128` is encoded structurally (zero-extension), the SAME widening
//!     spelled as the std call `<i128 as From<u64>>::from(x)` was not, so
//!     `i128::from(x) + 1` was refuted at `i128::MAX`.
//!
//! # Fixtures
//!
//! `tests/fixtures/false_refutation_*_mir.json` are the compiler's own
//! extraction of [`tests/data/false_refutation_shapes.rs`], captured with
//!
//! ```text
//! trustc --edition 2024 --crate-type lib -Ztrust-verify-profile=unix_hardened \
//!        -Ztrust-policy=advisory -Ztrust-dump=mir:<dir> false_refutation_shapes.rs
//! ```
//!
//! on Trust `main` stage 1 `a7ea88986d` (2026-09-28); only the `span.file`
//! fields were rewritten to the repo-relative source path.
//!
//! Every row is produced through the entry the compiler calls
//! (`generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops`,
//! hardened profile ON) and decided by the deterministic in-process `ay` router.
//!
//! # Mutation ledger (built and run 2026-09-29; each mutant reverts ONE fix)
//!
//! ```text
//! mutant                                              tests that go red
//! twin keeps only parameter ranges (a)                a_slice_bounded_increment…, a_real_overflow_after_the_loop…,
//!                                                     b_guarded_decrement_store_and_loop_increment…, b_the_store_of…
//! index lane without path definitions (b)             b_the_store_of…, b_guarded_decrement_store…
//! prefix kill's whole-block havoc back to Dest (b)    b_the_store_of…, b_guarded_decrement_store…
//! hardened entry kill's havoc back to Dest (b)        b_a_bounds_assert_after_an_element_store…
//! fixpoint outflow havoc back to Dest (b)             opaque_deref_store_reseat::an_element_store_in_a_loop_keeps…
//! Box::new mints its alloc row again (c)              c_box_new_mints_no_allocation_null_row
//! touch_place types the final variant Field (c)       c_a_box_behind_a_reference_to_a_recursive_enum…
//! Datatype Downcast refused again (c)                 c_a_box_behind_a_reference_to_a_recursive_enum…
//! FENCE mutants, added 2026-09-30 (each must keep rows; src/sep_engine_box_deref_tests.rs;
//! these real-MIR tests stay green under every one of them):
//! compaction marker admitted as a recursive enum (c)  the_compaction_marker_is_not_a_recursive_enum,
//!                                                       the_recursive_enum_admission_refuses_the_…
//! touch_place early return without its `Downcast`     a_bare_field_read_of_a_datatype_anywhere_keeps_the_
//!   guard (c)                                           reference_lane_rows, the_recursive_enum_admission_…
//! bare `Field` on a Datatype admitted on the box      a_bare_field_of_a_datatype_on_the_box_path_keeps_its_rows,
//!   path (c)                                            the_recursive_enum_admission_refuses_the_…
//! From/Into is not a widening source (d)              d_a_widened_u64_cannot_overflow_i128_add_or_neg
//! const fold does not see the From call (d)           d_a_widened_u64_constant_folds_exactly
//! block-def pin not skipped on a widening source (d)  d_a_widened_u64_constant_folds_exactly
//! SOUNDNESS: borrowed locals lose their explicit      opaque_deref_store_reseat::{reborrow_reseat…,
//!   `__slice_len` twin (what the plain relation         reseat_through_a_struct_carried_pointer…,
//!   relies on)                                           reseat_inside_a_loop…}
//! index lane renamed at the block terminal            (none — no fixture distinguishes it; kept because
//!                                                      `v2_live_path_defs_at_point` requires the rename at
//!                                                      the SAME point as the facts it keeps)
//! ```
//!
//! Every counter-program stays refuted under the fixed code.
//!
//! # The premise of (b)'s plain-relation kill was incomplete (2026-09-30)
//!
//! The SOUNDNESS row above names what the plain relation relies on: the explicit
//! `__slice_len` twin of every place on the slot-aliasing list. As landed with
//! this file, that list admitted `&mut` and `&raw mut` only, and a `&mut [u8]`
//! local reseated through `&raw const s as *mut _` in a LOOP went from refuted to
//! kernel-certified PROVED; the same omission already proved straight-line, call
//! and shared-slice reseats (and a scalar's stale value) before this file. None of
//! the three `&mut` canaries uses that channel, so the ledger's S1 mutant could
//! not see it. Closed by the own-storage write-channel rule (`&raw const` of an
//! OWNED place joins the list, and the stability scans of a local's own storage ask
//! the same rule), written as `slot_write_channel` on the r8c union lane and on main
//! as `path_defs::own_storage_write_borrow` (H2, 96db9eb9f0), the one kept when the
//! two were merged on 2026-10-08; its own ledger, measured 2026-09-30, is in
//! `opaque_deref_store_reseat.rs` (its `&raw const` section) and
//! `src/generate/slot_write_channel_tests.rs`. All sixteen tests here stay green
//! under that rule, and under each of its mutants.
#[path = "support/realmir_rows.rs"]
mod realmir_rows;

use realmir_rows::{
    NEGATION, PRIMARY_ADD, PRIMARY_SUB, Row, TWIN_ADD, TWIN_NEG, TWIN_SUB, Verdict, at, expect,
};
use trust_types::BlockId;

/// The fixtures' file-name prefix (`tests/fixtures/false_refutation_{name}_mir.json`).
const FIXTURE_PREFIX: &str = "false_refutation_";

/// Fixture `name`'s function ([`realmir_rows::load`]).
fn load(name: &str) -> trust_types::VerifiableFunction {
    realmir_rows::load(FIXTURE_PREFIX, name)
}

/// Every row of fixture `name`, hardened profile ON ([`realmir_rows::rows`]).
fn rows(name: &str, box_deref_ops: &[(usize, usize)]) -> Vec<Row> {
    realmir_rows::rows(FIXTURE_PREFIX, name, box_deref_ops)
}

/// [`rows`] with the REFERENCE_ARG_BOX_VALID premise installed for the argument
/// locals `reference_box_params`, as the compiler installs it (`with_reference_box_root_params`).
fn rows_with_reference_box_premise(
    name: &str,
    box_deref_ops: &[(usize, usize)],
    reference_box_params: &[usize],
) -> Vec<Row> {
    realmir_rows::rows_of_with_reference_box_premise(
        load(name),
        box_deref_ops,
        reference_box_params,
    )
}

// ─── (a) the hardened twin carries the per-statement lane's type ranges ─────────

/// `count_args` (source line 8, `i += 1` under `while i < args.len()`).
/// Before the fix: primary PROVED, twin FAILED at `args__slice_len = 2^64`.
#[test]
fn a_slice_bounded_increment_proves_on_both_twins() {
    let rows = rows("count_args", &[]);
    expect(&rows, 8, PRIMARY_ADD, 1, Verdict::Proved, "the primary already proved");
    expect(
        &rows,
        8,
        TWIN_ADD,
        1,
        Verdict::Proved,
        "the hardened twin states the same operation and must carry the same \
         `usize` range facts (`_5 = PtrMetadata(args)` <= usize::MAX)",
    );
}

/// COUNTER (a): `args.len() + 1` over `&[()]`. A zero-sized element admits
/// `len == usize::MAX`, so this is a REAL overflow — both twins must refute.
/// This is the row that would go green if the slice-length UPPER bound were
/// ever attached without its non-ZST gate.
#[test]
fn a_zst_slice_length_plus_one_still_refutes_on_both_twins() {
    let rows = rows("zst_len_plus_one", &[]);
    expect(&rows, 15, PRIMARY_ADD, 1, Verdict::Failed, "real overflow at len == usize::MAX");
    expect(&rows, 15, TWIN_ADD, 1, Verdict::Failed, "real overflow at len == usize::MAX");
}

/// COUNTER (a'): after the loop `i == args.len()`, and `i + k` overflows for a
/// large `k` — the range facts bound each operand, never the sum.
#[test]
fn a_real_overflow_after_the_loop_still_refutes_on_both_twins() {
    let rows = rows("after_loop_plus", &[]);
    expect(&rows, 22, TWIN_ADD, 1, Verdict::Proved, "`i += 1` under `i < len` is safe");
    expect(&rows, 24, PRIMARY_ADD, 1, Verdict::Failed, "`i + k` overflows for k = usize::MAX");
    expect(&rows, 24, TWIN_ADD, 1, Verdict::Failed, "`i + k` overflows for k = usize::MAX");
}

// ─── (b) one slice length: the index lane carries the dominating ties ──────────

/// `dec_every` (line 44, `digits[i] -= 1` under `while i < digits.len()`): the
/// STORE-side `[slice]` row of the compound assignment is dominated by the
/// bounds assert on the same index; it was refuted at `digits__slice_len = 0`
/// beside `_6__slice_len = 1`. The decrement itself is a REAL underflow (a zero
/// digit) and must stay refuted on both twins — the counter in the same body.
#[test]
fn b_the_store_of_a_compound_index_assignment_carries_its_bounds_ties() {
    let rows = rows("dec_every", &[]);
    expect(
        &rows,
        44,
        "SliceBoundsCheck",
        1,
        Verdict::Proved,
        "the index is bounded by the dominating assert `_10 == (_7 < _9)` whose \
         length `_9` is tied to `digits__slice_len`",
    );
    expect(&rows, 44, PRIMARY_SUB, 1, Verdict::Failed, "a zero digit really underflows");
    expect(&rows, 44, TWIN_SUB, 1, Verdict::Failed, "a zero digit really underflows");
    expect(&rows, 45, TWIN_ADD, 1, Verdict::Proved, "(a) again: `i += 1` under `i < len`");
}

/// `dec_first_nonzero` (line 32 `digits[i] -= 1`, line 36 `i += 1`): the store
/// row, the decrement and its twin, and the loop increment's twin. The decrement reads
/// `digits[i]` through a fresh index temp after the guard's read through another, so it
/// proves only through the element-read congruence (VGAPS-G1; FAILED before it, the
/// trust-ir survey's rows 110 and 114).
#[test]
fn b_guarded_decrement_store_and_loop_increment_are_not_refuted() {
    let rows = rows("dec_first_nonzero", &[]);
    expect(&rows, 32, "SliceBoundsCheck", 1, Verdict::Proved, "store dominated by its assert");
    expect(&rows, 32, PRIMARY_SUB, 1, Verdict::Proved, "`digits[i] -= 1` under `digits[i] > 0`");
    expect(&rows, 32, TWIN_SUB, 1, Verdict::Proved, "the decrement's hardened twin likewise");
    expect(&rows, 36, TWIN_ADD, 1, Verdict::Proved, "(a): `i += 1` under `i < len`");
}

/// COUNTER (b): the guard reads `digits[0]`, the decrement writes `digits[1]`
/// — a REAL underflow no length tie may discharge.
#[test]
fn b_a_guard_on_one_element_does_not_discharge_another() {
    let rows = rows("dec_neighbour", &[]);
    expect(&rows, 52, PRIMARY_SUB, 1, Verdict::Failed, "`digits[1]` may be 0");
    expect(&rows, 52, TWIN_SUB, 1, Verdict::Failed, "`digits[1]` may be 0");
}

/// `store_then_read` (lines 124-125: `if i < s.len() { s[i] = 1; s[i] }`): the
/// second read's bounds assert sits in the SAME block as the element store
/// `s[i] = 1`, so every kill of that block applies to it. The store's opaque-store
/// havoc used to be judged with the DESTINATION relation, whose derived channel read
/// the havoc base `s` as a write of `s__slice_len`; the hardened twin of that assert
/// lost the guard's length tie and was refuted at `s__slice_len = 0` beside a guard
/// length of 1. (The per-statement row of the same read already proved.)
#[test]
fn b_a_bounds_assert_after_an_element_store_keeps_its_length_tie() {
    let rows = rows("store_then_read", &[]);
    expect(&rows, 125, "mir_assert::BoundsCheck", 1, Verdict::Proved, "`i < s.len()` guards it");
    expect(&rows, 125, "SliceBoundsCheck", 1, Verdict::Proved, "`i < s.len()` guards it");
}

/// COUNTER (b''): the same shape reading `s[j]` with `j` unguarded — a REAL
/// out-of-bounds read the kept length tie must not discharge.
#[test]
fn b_an_unguarded_second_index_after_an_element_store_still_refutes() {
    let rows = rows("store_then_read_other", &[]);
    expect(&rows, 135, "mir_assert::BoundsCheck", 1, Verdict::Failed, "`j` is unguarded");
    expect(&rows, 135, "SliceBoundsCheck", 1, Verdict::Failed, "`j` is unguarded");
}

// ─── (c) no `[unsafe:sep:*]` demand for safe Box code ──────────────────────────

/// `Box::new` in safe code: no `[unsafe:sep:alloc]` row at all. Its non-null
/// result is the allocator's abort-on-OOM contract (docs/TCB.md), a premise the
/// row could only restate.
#[test]
fn c_box_new_mints_no_allocation_null_row() {
    for name in ["bin", "boxed"] {
        let rows = rows(name, &[]);
        let alloc: Vec<_> = rows.iter().filter(|r| r.kind.contains("[unsafe:sep:alloc]")).collect();
        assert!(
            alloc.is_empty(),
            "`{name}`: a safe `Box::new` is not an unsafe demand: {alloc:#?}"
        );
    }
}

/// `rhs_const` (line 74, `**rhs` for `rhs: &Box<Expr>` bound out of `e: &Expr`,
/// `Expr` RECURSIVE). The compiler nominates the synthesized `*box` reads at
/// `bb1[3]` (`discriminant(*_8)`) and `bb6[0]` (`((*_9) as Const).0`).
///
/// No `[unsafe…]` row of ANY family, not only `[unsafe:sep:deref]` (strengthened
/// 2026-09-30): the body is safe code, so a row that merely changed its label
/// (`[unsafe:sep:alloc]`, `[unsafe:sep:heap]`, …) would be the same false demand —
/// and the installed lane's trust-ir-giveback log carried a fourth
/// `[unsafe:sep:heap] out-of-bounds` row at the `**rhs` site (line 74) that a
/// deref-only filter would not see. The refusals the admission must keep (the
/// compaction marker, a bare `Field` on a `Ty::Datatype`, an untypeable bare read)
/// are pinned in `src/sep_engine_box_deref_tests.rs`.
///
/// Trust (2026-10-14, DECISION_QUEUE D100): the root is THROUGH the reference
/// argument `e`, so it rests on REFERENCE_ARG_BOX_VALID (R1: one
/// premise, one grade) and roots only where the compiler installed that premise for
/// `e`. This test used to generate with no premise and expect no `[unsafe…]` row,
/// which pinned the undemoted, undisclosed root D100 rules out. It now runs the
/// compiler's sequence on the real MIR: the install gate
/// (`reference_box_root_would_fire` over the `Ty::Ref` arguments) must name `e`,
/// generation under exactly that install must mint no `[unsafe…]` row, and
/// generation with no premise must keep the deref rows.
#[test]
fn c_a_box_behind_a_reference_to_a_recursive_enum_mints_no_unsafe_rows() {
    const NOMINATED: [(usize, usize); 2] = [(1, 3), (6, 0)];
    let func = load("rhs_const");
    let candidates: Vec<usize> = (1..=func.body.arg_count)
        .filter(|&arg| {
            func.body
                .locals
                .iter()
                .any(|decl| decl.index == arg && matches!(decl.ty, trust_types::Ty::Ref { .. }))
        })
        .collect();
    let set: trust_types::fx::FxHashSet<(BlockId, usize)> =
        NOMINATED.iter().map(|&(b, s)| (BlockId(b), s)).collect();
    let installed = trust_vcgen::reference_box_root_would_fire(&func, &set, &candidates);
    assert_eq!(installed, vec![1], "the gate installs the premise for `e` (`_1`)");

    let premised = rows_with_reference_box_premise("rhs_const", &NOMINATED, &installed);
    let unsafe_rows: Vec<_> = premised.iter().filter(|r| r.kind.contains("[unsafe")).collect();
    assert!(
        unsafe_rows.is_empty(),
        "the box is validity-rooted at the `&Expr` parameter through \
         `(*e as Bin).2`; nothing in the body is unsafe: {unsafe_rows:#?}"
    );

    let bare = rows("rhs_const", &NOMINATED);
    assert!(
        bare.iter().any(|r| r.kind.contains("[unsafe:sep:deref] null check")),
        "no premise, no root through `e`: {bare:#?}"
    );
}

/// COUNTER (c): a raw-pointer parameter may be null. Its three deref rows must
/// stay, and none may be proved (the null row stays REFUTED).
#[test]
fn c_a_raw_pointer_deref_keeps_its_rows() {
    let rows = rows("deref_raw", &[]);
    for label in ["null check", "allocation validity", "alignment check"] {
        let hits: Vec<_> = rows
            .iter()
            .filter(|r| r.kind.contains("[unsafe:sep:deref]") && r.kind.contains(label))
            .collect();
        assert_eq!(hits.len(), 1, "`*p` keeps its `{label}` row: {rows:#?}");
        assert_ne!(hits[0].verdict, Verdict::Proved, "`*p` may be null: {:#?}", hits[0]);
    }
    let null =
        rows.iter().find(|r| r.kind.contains("[unsafe:sep:deref] null check")).expect("null row");
    assert_eq!(null.verdict, Verdict::Failed, "a null `p` is a real witness: {null:#?}");
}

/// COUNTER (c'): `Box::from_raw(p)` of an arbitrary pointer is not a `Box::new`
/// root: the deref of the resulting box keeps its null row.
#[test]
fn c_a_box_from_raw_deref_keeps_its_rows() {
    let rows = rows("from_raw_read", &[]);
    let null: Vec<_> =
        rows.iter().filter(|r| r.kind.contains("[unsafe:sep:deref] null check")).collect();
    assert_eq!(null.len(), 1, "`*Box::from_raw(p)` keeps its null row: {rows:#?}");
    assert_ne!(null[0].verdict, Verdict::Proved, "`p` may be null: {:#?}", null[0]);
}

// ─── (d) a lossless std integer conversion is the widening it is ───────────────

/// `i128::from(x) + 1` for `x: u64` (line 104) and `-i128::from(x)` (line 108):
/// the operand lies in `[0, 2^64)`.
///
/// The hardened twins — a pure bitvector core — PROVE. The per-statement rows are
/// asserted NOT REFUTED rather than proved, and that is an admission: they carry
/// the parameter's `Int`-sorted range (`0 <= x <= u64::MAX`) beside the bitvector
/// core, sharing no variable with it, and ay computes UNSAT but its strict proof
/// validation rejects the mixed-theory refutation ("step t0 uses unverified trust
/// rule" -> "(incomplete self-check-rejected)"), so the row lands UNKNOWN. Before
/// the fix both rows were REFUTED at `i128::MAX` / `i128::MIN`.
#[test]
fn d_a_widened_u64_cannot_overflow_i128_add_or_neg() {
    let inc = rows("widen_inc", &[]);
    expect(&inc, 104, TWIN_ADD, 1, Verdict::Proved, "`[0, 2^64) + 1` fits i128");
    let primary = at(&inc, 104, PRIMARY_ADD);
    assert_eq!(primary.len(), 1, "one primary add row: {inc:#?}");
    assert_ne!(
        primary[0].verdict,
        Verdict::Failed,
        "no x: u64 widens to i128::MAX: {:#?}",
        primary[0]
    );

    let neg = rows("widen_neg", &[]);
    expect(&neg, 108, TWIN_NEG, 1, Verdict::Proved, "no x: u64 widens to i128::MIN");
    let primary = at(&neg, 108, NEGATION);
    assert!(!primary.is_empty(), "the primary negation rows must exist: {neg:#?}");
    for row in primary {
        assert_ne!(row.verdict, Verdict::Failed, "no x: u64 widens to i128::MIN: {row:#?}");
    }
}

/// `let wide = i128::from(u64::MAX) + 1; -wide` (lines 99-100) — the trust-ir
/// conformance shape (`generate.rs:468/477`).
#[test]
fn d_a_widened_u64_constant_folds_exactly() {
    let rows = rows("wide_const", &[]);
    expect(&rows, 99, PRIMARY_ADD, 1, Verdict::Proved, "`2^64 - 1 + 1` fits i128");
    expect(&rows, 99, TWIN_ADD, 1, Verdict::Proved, "`2^64 - 1 + 1` fits i128");
    let neg: Vec<_> = rows
        .iter()
        .filter(|r| r.line == 100 && (r.kind.contains(NEGATION) || r.kind.contains(TWIN_NEG)))
        .collect();
    assert!(!neg.is_empty(), "the negation rows must exist: {rows:#?}");
    for row in neg {
        assert_eq!(row.verdict, Verdict::Proved, "`-(2^64)` is not i128::MIN: {row:#?}");
    }
}

/// COUNTER (d): the conversion bounds `x`, never `n`: `i128::from(x) + n`
/// overflows for `n = i128::MAX`.
#[test]
fn d_the_conversion_does_not_bound_the_other_operand() {
    let rows = rows("widen_plus", &[]);
    expect(&rows, 113, PRIMARY_ADD, 1, Verdict::Failed, "n = i128::MAX overflows");
    expect(&rows, 113, TWIN_ADD, 1, Verdict::Failed, "n = i128::MAX overflows");
}

/// COUNTER (d'): an i128 parameter carries no widening at all.
#[test]
fn d_an_unwidened_i128_increment_still_refutes() {
    let rows = rows("i128_inc", &[]);
    expect(&rows, 118, PRIMARY_ADD, 1, Verdict::Failed, "x = i128::MAX overflows");
    expect(&rows, 118, TWIN_ADD, 1, Verdict::Failed, "x = i128::MAX overflows");
}

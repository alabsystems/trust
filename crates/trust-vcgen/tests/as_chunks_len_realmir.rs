//! TRUST-KI-1015-1, the `as_chunks` remainder shape: a correct program's
//! `buf[..rest.len()]` after `let (blocks, rest) = data.as_chunks::<64>()` was FAILED
//! (refuted with a counterexample no execution reaches).
//!
//! # The defect (measured 2026-10-15)
//!
//! aterm-digest `Sha256::update` (sha256.rs:121-127 at aterm `848d791bd`) splits its
//! input with `data.as_chunks::<BLOCK_LEN>()`, compresses the whole blocks and copies
//! the tail into its `[u8; 64]` buffer: `self.buf[..rest.len()].copy_from_slice(rest)`.
//! The `[slice]` row of that index (127:16, `rest.len() <= 64`) was FAILED by the
//! in-process `ay` lane on the channel seal `b58a105dde` (raw `trustc`) and on main
//! (the stage 1 of `edbb3f3009`; the crate-level rows of `9fa33ffd06` below, and again
//! of `5138cede2c`, which carries TRUST-KI-1015-1's loop-index and sub-slice fixes), with the
//! model `rest__slice_len = 65` beside `data` of length 0. The call `_5 =
//! core::slice::<impl [u8]>::as_chunks::<64>(copy data)` is havocked by the VC lane and
//! nothing related the two halves' length names to the receiver's length or to `N`.
//! Every correct function of `tests/data/as_chunks_len.rs` was FAILED the same way on
//! the channel and on main (`as_rchunks`, `as_chunks_mut`, `as_rchunks_mut`, a `[u32]`
//! receiver, `63 - rest.len()`, `data.len() - rest.len()`, `6 - rest.len()` under
//! `len == 70`, `blocks.len() - 2` under `len == 130`, and `blocks[1]` under
//! `data.len() >= 8`), twins included.
//!
//! # The fix
//!
//! `generate/as_chunks_len.rs`: on the normal return of core's `as_chunks::<N>` family
//! the remainder's length `R` and the chunk slice's length `C` satisfy `R == len - N*C`,
//! `0 <= R < N` (Euclidean division, stated linearly) — post-return definitions of the
//! call in the path-definition fixpoint. See that module for the gates.
//!
//! # What these tests pin
//!
//! * the digest's own row (its real MIR, `aterm_digest_sha256_update`) is PROVED (and
//!   Clean-kernel certified, measured; the `Sub` and chunk-index rows prove without a
//!   certificate);
//! * every correct function's rows at its index or subtraction are PROVED, twins
//!   included;
//! * every wrong twin keeps its panicking row FAILED (each panics natively on the input
//!   its comment names: `records/digest-update-aschunks/repro/run_native.rs`);
//! * the gates, each by an edit of `s2_no_loop`'s real MIR that mints nothing: a user
//!   trait method named `as_chunks`, a user type's inherent `as_chunks`, a callee key
//!   not from the real sysroot, an `N` in the callee that disagrees with the
//!   destination's array type, an `as_rchunks` spelling over an `as_chunks`
//!   destination, a receiver the call itself writes, a receiver or halves of the other
//!   mutability, a chunk or remainder element unlike the receiver's, `N == 0`, and a
//!   destination that is one field of a local;
//! * `a_symbolic_n_mints_no_length` pins `collection_range::const_generic_literal`'s
//!   refusal of a non-literal `N`. That is shared code, not a gate of
//!   `generate/as_chunks_len.rs`: no edit of that module turns it red.
//!
//! # Falsification (2026-10-15; one edit of `generate/as_chunks_len.rs` each, restored
//! byte-for-byte; `records/digest-update-aschunks/logs/mutants/` on the measuring host,
//! re-run on main `5138cede2c` + this change: `records/digest-update-aschunks-finish2/`;
//! the sub-gate mutants are the adversarial review's, `records/digest-update-aschunks-review2/`,
//! and the whole set was re-run with the sub-gate rails: `records/digest-update-aschunks-revise2/`)
//!
//! ```text
//! mutant                                   tests that go red
//! the facts off (main's behaviour)         the 5 correct-shape tests, the digest's included
//! `R < N` weakened to `R <= N`             the slice, arithmetic and chunk-index tests
//! `R == len + 1 - N * C` (unsound)         arithmetic, every_wrong_twin (w5 reads PROVED)
//! the destination-type gate off            an_n_that_disagrees_with_the_destination_type,
//!                                          halves_of_the_other_mutability, both
//!                                          element-unlike-the-receiver's tests
//! the array length == N check alone off    an_n_that_disagrees_with_the_destination_type
//! the halves' order swapped                the correct-shape tests (the type gate refuses)
//!                                          + an_rchunks_spelling_over_an_as_chunks_destination
//! order swapped AND type gate off          the above + every_wrong_twin (w8 reads PROVED)
//! the real-sysroot key check off           an_as_chunks_callee_not_from_the_real_sysroot
//! the receiver-kill check off              a_receiver_the_call_itself_writes
//! the core-inherent root AND ` as ` off    a_user_trait_method_named_as_chunks,
//!                                          a_user_type_method_named_as_chunks
//! the core-inherent root alone off         a_user_type_method_named_as_chunks
//! the receiver's mutability check off      a_receiver_of_the_other_mutability
//! the halves' mutability check off         halves_of_the_other_mutability
//! the chunk element == receiver's off      a_chunk_element_unlike_the_receivers
//! the remainder element == receiver's off  a_remainder_element_unlike_the_receivers
//! the `N != 0` filter off                  a_zero_n_mints_no_contradiction (PROVED by
//!                                          `R < 0` beside `0 <= R`)
//! whole-local destination AND halves-kill  a_projected_destination
//! ```
//!
//! Six edits turn nothing red. Each was measured and is recorded here, not hidden:
//!
//! * the ` as ` check alone and the unauthenticated-stamp check alone. Both are subsumed
//!   by `is_core_slice_inherent`'s anchored `core::slice::<impl [` root on an
//!   authenticated sysroot crate, so they are defence in depth;
//! * dropping `0 <= R`. A slice length's type range already bounds it;
//! * the whole-local destination check alone and the halves-kill check alone. Each one
//!   refuses `a_projected_destination` without the other: a write of one field leaves the
//!   other half's length alive, and a whole local is killed whole. They are pinned only
//!   together, and no shape found refuses under one of them alone;
//! * the distinct-names check. Fields `.0` and `.1` of one local always name two
//!   lengths, so the check has nothing to refuse. It is defence in depth.
//!
//! # Not covered (still FAILED on a correct program)
//!
//! `data.chunks_exact(64).remainder()` (`s12_chunks_exact_rem`): the remainder is a
//! field of the `ChunksExact` the first call builds and the second reads; not this
//! route (docs/KNOWN_HAZARDS.md, TRUST-KI-1015-1). Its wrong twin stays FAILED.
//!
//! Also still FAILED is a row that relates a half to a SECOND read of the receiver
//! behind a `&mut`, for example `d.len() - rest.len()` with `d: &mut &[u8]` or
//! `d: &mut &str` (through `as_bytes`), or with a slice field of a `&mut S` parameter.
//! The fact names the length of the receiver temp the call read, and the later `.len()`
//! reads the place again through a fresh deref temp whose length is tied to nothing.
//! With `s: &mut String`, `s.len() - s.as_bytes().as_chunks::<4>().1.len()` is FAILED
//! for a neighbouring reason: the length of that `as_bytes` result is tied to nothing,
//! so the receiver of the call has no length related to `s.len()`. These rows are
//! FAILED with and without this change. They were found by the adversarial review,
//! `records/digest-update-aschunks-review2/` (cb05 cb07 cb14 cy10 cy14).
//!
//! # Fixtures
//!
//! `tests/fixtures/as_chunks_len/<fn>.json` are the compiler's own extraction of
//! `tests/data/as_chunks_len.rs`, captured with the channel seal's raw `trustc`
//! (`b58a105dde`, no trustd):
//!
//! ```text
//! trustc --crate-type lib --edition 2024 --crate-name repro --emit=metadata -C debuginfo=2 \
//!        -Ztrust-verify-level=2 -Ztrust-policy=advisory -Ztrust-verify-profile=unix_hardened \
//!        -Ztrust-dump=mir:<dir> as_chunks_len.rs
//! ```
//!
//! with only the `span.file` fields rewritten to the repo-relative source path.
//! `aterm_digest_sha256_update.json` is the same capture of aterm-digest at aterm
//! `848d791bd` (`Sha256::update`; `span.file` rewritten to
//! `aterm-digest-848d791bd/src/sha256.rs`, a source this repo does not carry). Every
//! row goes through the entry the compiler calls (hardened profile ON) and is decided
//! by the deterministic in-process `ay` router, the `ay-in-process` lane that refuted
//! them.
#[path = "support/realmir_rows.rs"]
mod realmir_rows;

use realmir_rows::{Row, Verdict, rows_of};
use trust_types::{Operand, Place, Projection, Terminator, Ty, VerifiableFunction};

const SLICE: &str = "SliceBoundsCheck";
const BOUNDS: &str = "IndexOutOfBounds";
const TWIN_BOUNDS: &str = "mir_assert::BoundsCheck";
const SUB: &str = "ArithmeticOverflow { op: Sub";
const TWIN_SUB: &str = "mir_assert::Overflow(Sub)";

fn load(name: &str) -> VerifiableFunction {
    realmir_rows::load_path(&format!(
        "{}/tests/fixtures/as_chunks_len/{name}.json",
        env!("CARGO_MANIFEST_DIR")
    ))
}

fn rows(name: &str) -> Vec<Row> {
    rows_of(load(name), &[])
}

/// The rows at `line` whose kind contains one of `needles`.
fn at<'a>(rows: &'a [Row], line: u32, needles: &[&str]) -> Vec<&'a Row> {
    rows.iter().filter(|r| r.line == line && needles.iter().any(|n| r.kind.contains(n))).collect()
}

fn dump(rows: &[Row]) -> Vec<(u32, &str, Verdict)> {
    rows.iter().map(|r| (r.line, r.kind.as_str(), r.verdict)).collect()
}

/// At least one row at `line` matches `needles`, and EVERY such row is PROVED.
fn all_proved(name: &str, rows: &[Row], line: u32, needles: &[&str]) {
    let hits = at(rows, line, needles);
    assert!(!hits.is_empty(), "{name}:{line}: no {needles:?} row; rows: {:#?}", dump(rows));
    for row in hits {
        assert_eq!(
            row.verdict,
            Verdict::Proved,
            "{name}:{line} `{}` must be PROVED (a correct program)\nresult: {}\nformula: {:?}",
            row.kind,
            row.result,
            row.vc.formula
        );
    }
}

/// Some row at `line` matching `needles` is FAILED: the real panic stays refuted.
fn some_failed(name: &str, rows: &[Row], line: u32, needles: &[&str]) {
    let hits = at(rows, line, needles);
    assert!(
        hits.iter().any(|r| r.verdict == Verdict::Failed),
        "{name}:{line}: the real panic must stay FAILED; rows there: {:#?}",
        hits.iter().map(|r| (&r.kind, r.verdict, &r.result)).collect::<Vec<_>>()
    );
}

/// No row at `line` matching `needles` is PROVED (a gate test: the fact is absent).
fn none_proved(name: &str, rows: &[Row], line: u32, needles: &[&str]) {
    let hits = at(rows, line, needles);
    assert!(!hits.is_empty(), "{name}:{line}: no {needles:?} row; rows: {:#?}", dump(rows));
    for row in hits {
        assert_ne!(
            row.verdict,
            Verdict::Proved,
            "{name}:{line} `{}` must NOT be proved without the fact\nformula: {:?}",
            row.kind,
            row.vc.formula
        );
    }
}

/// The correct functions and the line of the row their index or subtraction mints.
const SAFE_SLICE: &[(&str, u32)] = &[
    ("s1_digest_tail", 11),
    ("s2_no_loop", 18),
    ("s3_rchunks", 23),
    ("s4_chunks_mut", 28),
    ("s5_rchunks_mut", 33),
    ("s11_words", 66),
];
const SAFE_SUB: &[(&str, u32)] = &[
    ("s6_room_left", 38),
    ("s7_whole_part", 43),
    ("s10_exact_rest", 61),
    ("s13_exact_count", 151),
];
const SAFE_INDEX: &[(&str, u32)] = &[("s8_block_count", 48), ("s9_rblock_count", 53)];

/// The wrong twins, the line of their panicking row, and its kinds.
const WRONG: &[(&str, u32, &[&str])] = &[
    ("w1_buf_too_small", 77, &[SLICE]),
    ("w2_room_off_by_one", 83, &[SUB, TWIN_SUB]),
    ("w3_rest_nonempty", 89, &[SUB, TWIN_SUB]),
    ("w4_rchunks_buf_too_small", 95, &[SLICE]),
    ("w5_block_count_off_by_one", 101, &[BOUNDS, TWIN_BOUNDS]),
    ("w6_chunks_mut_buf_too_small", 107, &[SLICE]),
    ("w7_rblock_count_off_by_one", 113, &[BOUNDS, TWIN_BOUNDS]),
    ("w8_exact_rest_off_by_one", 122, &[SUB, TWIN_SUB]),
    ("w9_rest_is_not_the_head", 128, &[SUB, TWIN_SUB]),
    ("w10_words_buf_too_small", 134, &[SLICE]),
    ("w11_rchunks_mut_buf_too_small", 140, &[SLICE]),
    ("w12_chunks_exact_rem_buf_too_small", 146, &[SLICE]),
    ("w13_rest_of_a_whole_block", 158, &[SUB, TWIN_SUB]),
    ("w14_count_off_by_one", 164, &[SUB, TWIN_SUB]),
];

#[test]
fn the_digest_tail_copy_after_as_chunks_is_proved() {
    let rows = rows("aterm_digest_sha256_update");
    all_proved("aterm_digest_sha256_update", &rows, 127, &[SLICE]);
}

#[test]
fn a_remainder_of_the_as_chunks_family_fits_a_buffer_of_n() {
    for &(name, line) in SAFE_SLICE {
        all_proved(name, &rows(name), line, &[SLICE]);
    }
}

#[test]
fn arithmetic_on_an_as_chunks_remainder_is_proved_on_both_rows() {
    for &(name, line) in SAFE_SUB {
        let rows = rows(name);
        all_proved(name, &rows, line, &[SUB]);
        all_proved(name, &rows, line, &[TWIN_SUB]);
    }
}

#[test]
fn a_chunk_index_under_a_guard_on_the_receiver_is_proved() {
    for &(name, line) in SAFE_INDEX {
        let rows = rows(name);
        all_proved(name, &rows, line, &[BOUNDS]);
        all_proved(name, &rows, line, &[TWIN_BOUNDS]);
    }
}

#[test]
fn every_wrong_twin_stays_refuted() {
    for &(name, line, kinds) in WRONG {
        let rows = rows(name);
        for kind in kinds {
            some_failed(name, &rows, line, &[kind]);
        }
    }
}

/// `s2_no_loop` with its `as_chunks::<64>` call terminator edited by `edit`. The gate
/// tests below expect its slice row NOT proved (the gate refused the fact).
fn s2_with(edit: impl Fn(&mut Terminator)) -> Vec<Row> {
    let mut func = load("s2_no_loop");
    let mut edited = 0;
    for block in &mut func.body.blocks {
        if matches!(&block.terminator, Terminator::Call { func: callee, .. } if callee.contains("as_chunks"))
        {
            edit(&mut block.terminator);
            edited += 1;
        }
    }
    assert_eq!(edited, 1, "s2_no_loop has one as_chunks call");
    rows_of(func, &[])
}

/// [`s2_with`], editing the callee string.
fn s2_with_callee(edit: impl Fn(&str) -> String) -> Vec<Row> {
    s2_with(|t| {
        if let Terminator::Call { func: callee, .. } = t {
            *callee = edit(callee);
        }
    })
}

#[test]
fn the_unedited_gate_fixture_proves() {
    // The control for the gate tests below: the same fixture, unedited, proves.
    all_proved("s2_no_loop", &s2_with(|_| {}), 18, &[SLICE]);
}

#[test]
fn a_user_trait_method_named_as_chunks_mints_no_length() {
    let rows = s2_with_callee(|_| "<[u8] as repro::Ext>::as_chunks::<64>".to_string());
    none_proved("s2_no_loop (user trait)", &rows, 18, &[SLICE]);
}

#[test]
fn a_user_type_method_named_as_chunks_mints_no_length() {
    // A user type's inherent `as_chunks`, spelled as the channel's `trustc` spells one
    // (records/digest-update-aschunks-review2, `re02`). Only `[T]`'s own crate can write
    // an inherent `[T]::as_chunks`, so without the `core::slice::<impl [` root this callee
    // has no ` as ` to refuse it. The key is left real-sysroot here, so this rail pins
    // the root check alone; in real MIR the key check refuses it as well.
    let rows = s2_with_callee(|_| "repro::Sl::<'_>::as_chunks::<64>".to_string());
    none_proved("s2_no_loop (user type method)", &rows, 18, &[SLICE]);
}

#[test]
fn an_as_chunks_callee_not_from_the_real_sysroot_mints_no_length() {
    let rows = s2_with(|t| {
        if let Terminator::Call { callee_key: Some(key), .. } = t {
            key.krate_is_real_sysroot = false;
        }
    });
    none_proved("s2_no_loop (non-sysroot key)", &rows, 18, &[SLICE]);
}

#[test]
fn an_n_that_disagrees_with_the_destination_type_mints_no_length() {
    // `as_chunks::<32>` would bound the remainder below 32 and prove the row (measured:
    // red with the type gate removed); the destination's MIR type says `[[u8; 64]]`, so
    // the instantiation is not believed.
    let rows = s2_with_callee(|callee| callee.replace("::<64>", "::<32>"));
    none_proved("s2_no_loop (N mismatch)", &rows, 18, &[SLICE]);
}

#[test]
fn an_rchunks_spelling_over_an_as_chunks_destination_mints_no_length() {
    let rows = s2_with_callee(|callee| callee.replace("as_chunks", "as_rchunks"));
    none_proved("s2_no_loop (order mismatch)", &rows, 18, &[SLICE]);
}

#[test]
fn a_symbolic_n_mints_no_length() {
    let rows = s2_with_callee(|callee| callee.replace("::<64>", "::<N>"));
    none_proved("s2_no_loop (symbolic N)", &rows, 18, &[SLICE]);
}

#[test]
fn a_receiver_the_call_itself_writes_mints_no_length() {
    // `_5 = as_chunks::<64>(copy _5.1)`: the receiver's length name is one the call
    // writes, so on the return edge it no longer holds the length the call read, and the
    // bare fact would read `R == R - 64 * C` (measured: PROVED without the gate).
    let rows = s2_with(|t| {
        if let Terminator::Call { args, dest, .. } = t {
            args[0] =
                Operand::Copy(Place { local: dest.local, projections: vec![Projection::Field(1)] });
        }
    });
    none_proved("s2_no_loop (receiver written by the call)", &rows, 18, &[SLICE]);
}

// The sub-gate tests below edit `s2_no_loop`'s local declarations or its call, the way
// the gate tests above edit its call. Except for `N == 0`, real MIR of a call to core's
// method cannot carry these shapes, because the destination's and the receiver's types
// are the method's signature at its instantiation. Each test is red under the mutant of
// `generate/as_chunks_len.rs` that drops its sub-gate. Without these tests the review
// measured those mutants green (records/digest-update-aschunks-review2, X2 X3 X6 X8,
// and X1 with X4). The re-run is in records/digest-update-aschunks-revise2.

fn u8_ty() -> Ty {
    Ty::Int { width: 8, signed: false }
}

fn u32_ty() -> Ty {
    Ty::Int { width: 32, signed: false }
}

fn slice_ref(mutable: bool, elem: Ty) -> Ty {
    Ty::Ref { mutable, inner: Box::new(Ty::Slice { elem: Box::new(elem) }) }
}

fn array(elem: Ty, len: u64) -> Ty {
    Ty::Array { elem: Box::new(elem), len }
}

/// The destination type of `as_chunks{,_mut}::<len>` over `elem`s of the given
/// element types: `(&[[chunk; len]], &[rem])`.
fn chunks_pair(mutable: bool, chunk: Ty, len: u64, rem: Ty) -> Ty {
    Ty::Tuple(vec![slice_ref(mutable, array(chunk, len)), slice_ref(mutable, rem)])
}

/// `s2_no_loop` edited by `edit`, after checking the locals these tests edit: `_2` is
/// the receiver `data: &[u8]` and `_5` the call's destination `(&[[u8; 64]], &[u8])`.
/// The edited fixture's slice row (`buf[..rest.len()]`, line 18) is expected NOT proved.
fn s2_edited(edit: impl FnOnce(&mut VerifiableFunction)) -> Vec<Row> {
    let mut func = load("s2_no_loop");
    assert_eq!(func.body.locals[2].ty, slice_ref(false, u8_ty()), "_2 is `data: &[u8]`");
    assert_eq!(
        func.body.locals[5].ty,
        chunks_pair(false, u8_ty(), 64, u8_ty()),
        "_5 is the destination of `as_chunks::<64>`"
    );
    edit(&mut func);
    rows_of(func, &[])
}

#[test]
fn a_receiver_of_the_other_mutability_mints_no_length() {
    // `as_chunks` takes `&self`: a `&mut [u8]` receiver is not its signature.
    let rows = s2_edited(|f| f.body.locals[2].ty = slice_ref(true, u8_ty()));
    none_proved("s2_no_loop (&mut receiver)", &rows, 18, &[SLICE]);
}

#[test]
fn halves_of_the_other_mutability_mint_no_length() {
    // `as_chunks` returns shared halves: `(&mut [[u8; 64]], &mut [u8])` is `as_chunks_mut`'s.
    let rows = s2_edited(|f| f.body.locals[5].ty = chunks_pair(true, u8_ty(), 64, u8_ty()));
    none_proved("s2_no_loop (&mut halves)", &rows, 18, &[SLICE]);
}

#[test]
fn a_chunk_element_unlike_the_receivers_mints_no_length() {
    // `[[u32; 64]]` chunks of a `[u8]` receiver: not core's `as_chunks` at this type.
    let rows = s2_edited(|f| f.body.locals[5].ty = chunks_pair(false, u32_ty(), 64, u8_ty()));
    none_proved("s2_no_loop (chunk element u32)", &rows, 18, &[SLICE]);
}

#[test]
fn a_remainder_element_unlike_the_receivers_mints_no_length() {
    // A `[u32]` remainder of a `[u8]` receiver: not core's `as_chunks` at this type.
    let rows = s2_edited(|f| f.body.locals[5].ty = chunks_pair(false, u8_ty(), 64, u32_ty()));
    none_proved("s2_no_loop (remainder element u32)", &rows, 18, &[SLICE]);
}

#[test]
fn a_zero_n_mints_no_contradiction() {
    // `as_chunks::<0>` compiles, and core's `assert!(N != 0)` panics at run time
    // (measured natively). The `ConstChunkSize` row refuses the call as
    // `slice-const-chunk-size-zero`, UNKNOWN. The channel's `trustc` emits exactly this
    // edit for `data.as_chunks::<0>()`: the callee `as_chunks::<0>` and the destination
    // `(&[[u8; 0]], &[u8])` (records/digest-update-aschunks-revise2/direct/zero-n). The
    // normal return is dead, so `R < 0` beside `0 <= R` would hold vacuously there. It
    // would also prove every row after the call by contradiction alone, so the module
    // mints nothing for `N == 0`. This rail is conservative, not a soundness rail.
    let rows = s2_edited(|f| {
        f.body.locals[5].ty = chunks_pair(false, u8_ty(), 0, u8_ty());
        let mut edited = 0;
        for block in &mut f.body.blocks {
            if let Terminator::Call { func: callee, .. } = &mut block.terminator
                && callee.contains("as_chunks::<64>")
            {
                *callee = callee.replace("::<64>", "::<0>");
                edited += 1;
            }
        }
        assert_eq!(edited, 1, "s2_no_loop has one as_chunks::<64> call");
    });
    none_proved("s2_no_loop (N == 0)", &rows, 18, &[SLICE]);
}

#[test]
fn a_projected_destination_mints_no_length() {
    // `_5.1 = as_chunks::<64>(copy _2)`: the call writes one field, so the halves'
    // length names the module would read (`_5.0`, `_5.1`) are not the call's result.
    // Two gates refuse it, each alone: the destination must be a whole local, and the
    // terminator kill must kill both halves' names (`_5.0__slice_len` survives a write
    // of `_5.1`). Measured: red only with both off.
    let rows = s2_with(|t| {
        if let Terminator::Call { dest, .. } = t {
            dest.projections.push(Projection::Field(1));
        }
    });
    none_proved("s2_no_loop (projected destination)", &rows, 18, &[SLICE]);
}

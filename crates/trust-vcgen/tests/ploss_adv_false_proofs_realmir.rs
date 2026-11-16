// Reproducers (H1 stale range bound, H2 raw-const store, H3 asm output) from
// the 2026-10-08 adversarial pass over the integrated tree
// `land/proof-loss-fixes` (bbaf3bdaeb; product code = e618d75ec5). Every `_bug` below
// PANICS natively at -O0 and at -O1 on the input in its source comment, and its panic row
// is PROVED and/or `certify_vc`-certified by `generate_vcs` + the deterministic in-process
// ay router -- on the integrated tree AND on bare origin/main c132f5a193 (pre-existing;
// none is introduced by the four proof-loss merges). These tests assert the SOUND outcome
// (not proved, not certified); every one of them FAILED when they were written.
//
// STATUS. H1 is closed at its root (2026-10-08): the global resolver licenses the
// POINTEE a projected bound names (`iterator_yield::projected_bound_names_one_value`), and
// the slice range lane names a projected bound by its version at the read into the range
// when that is its value at the call (`range_bound_use::projected_read_name`); the
// controls in `h1_projected_bound_controls_still_prove` keep their proofs. H2 is closed
// at its root (2026-10-08): every write-channel scan asks ONE predicate,
// `path_defs::borrow_write_target` (own storage: `own_storage_write_borrow`), and a
// `&raw const` of the body's own storage is a write channel there; the controls in
// `h2_raw_const_controls_keep_their_proofs` keep theirs. H3 is closed at its root
// (2026-10-08): a terminator `trust_types::Terminator::place_writes` calls `Unlocatable`
// (an `Opaque`) writes EVERY local in the version oracle
// (`path_defs::terminator_def_names_structured`), and the interval lane forgets them on
// its out-edge (`abstract_interp::transfer_terminator`); the controls in
// `h3_inline_asm_controls_still_prove` keep their proofs, and the three in the ignored
// `h3_asm_that_cannot_write_k_keeps_its_proof` are the precision that costs until the
// extraction carries the asm's operands. LAUNDERED-ALIAS-STORE (with its overflow form
// LAUNDERED-ALIAS-ELIDE-1) is closed at its root (2026-10-11, prepared, not built into a
// compiler): a write into escaped storage in a body holding an unresolved raw copy of a
// pointer havocs the whole-function list (`path_defs::write_havocs_function_list`), and a
// same-pointee raw-pointer cast folds like a copy (`resolve_referent_guarded`); the controls
// in `laundered_alias_controls_still_prove` keep their proofs.
//
// H1 -- STALE-BOUND-CALL-RENAME. A range bound (slice range index, `..=`, a `Bound` pair)
// or a range-ITERATOR end that is read through a REFERENCE or a raw pointer (`r = ..*z`,
// `for i in 0..*z`, `..(*p).len`) is resolved GLOBALLY by
// `iterator_yield::resolve_range_bound_formula`'s projected arm, licensed only by the
// pointer ROOT being single-valued and never projection-written. The bare formula it
// returns is then (a) respelled by the referent fold to the POINTEE's own name (`*z` ->
// `len`, `s*.len`) and (b) version-renamed at the INDEX CALL (or, for a yield fact, at
// the row) -- not where the range was built. A direct write to the pointee after the
// range is built (legal once `z`'s borrow ended: SAFE CODE), or a write through another
// raw pointer, plus a guard on the NEW value then discharges a violation about a value
// the range does not hold. Class 10 (`range_bound_use`) closed exactly this for a
// multiply-written LOCAL bound; the projected / folded arm still takes the global path
// first, so its banner's "never the bare name renamed at the call" does not hold here.
//   pb04/pb05  `z = &mut len` / `&len`; `r = ..*z; len = n; if len > 8 {return} buf[r]`
//              (formula: violation `len#<post-write> > 8`, guard `len#<post-write> <= 8`)
//   pb10       `z = &s.len` of a `&mut St` PARAMETER, `s.len = n` after
//   pb11       `z = &st.len` of a LOCAL struct
//   pb12/pb14  exclusive pair `*a..*b`, `RangeFrom` `*z..`
//   pb16/pb17  `..=*z`, `(Bound::Included(*z), Bound::Unbounded)` (`collection_range`)
//   pb06/pb13  the YIELD lane: `for i in 0..*z { len = n; if len > 8 {return} buf[i] }`
//              -- the fact `i < len#<row version>` binds to the post-write value
//   pb02       raw pointers `p == q`: `r = ..(*p).len; (*q).len = n; if (*p).len > 8
//              {return} buf[r]` -- the oracle DOES bump `p*.0` at the store through `q`;
//              the call-point rename picks the bumped version
// The mirror is a false REFUTATION of a correct program: `pb15_folded_guard_first_ctl`
// (guard, then `r = ..*z`, then `len = n`, then `buf[r]`) FAILS on all levels.
//
// H2 -- RAW-CONST-STORE. A store through a pointer made by `&raw const k` and cast to
// `*mut` is not attributed to `k` (the formula carries no definition for the store; the
// later read is `k`'s pre-store version), so `t[k]` is certified at -O0 and PROVED and
// certified at -O1 while the program indexes with the stored value. `fd05` is the same
// through the referent fold's guard (`if k == k0 {return}` becomes infeasible). Whether
// writing through a `&raw const`-derived pointer of a `mut` local is UB is
// aliasing-model dependent (Stacked Borrows: UB; Tree Borrows: allowed). The crate's own
// `guards::value_local_is_unstable` already counts `AddressOf` of EITHER mutability as an
// escape; the version oracle does not. The same store through `&raw mut k` typed
// `*const` (`fd07`, `fd09` in adv_fold.rs) is NOT proved -- the gap is the const borrow.
// ROOT: the write-channel scans -- above all `path_defs::mutably_borrowed_local_names`,
// the havoc list of an opaque deref store and of every call -- matched `&mut` / `&raw
// mut` only, so the opaque store through `p as *mut` havocked every pointer local but
// never `k`. They now all ask `path_defs::borrow_write_target`, which counts `&raw const
// P` unless `addr_of_is_read_only` (through a shared reference to `Freeze` data); the
// own-storage form (`own_storage_write_borrow`) leaves a `&raw const` BEHIND a pointer to
// that pointer's own channel. `ploss_adv/h2_raw_const.rs` adds the field / element /
// whole-struct / `cast_mut()` / byte-store / callee / tuple-carried / loop forms.
//
// H3 -- OPAQUE-ASM-OUTPUT. The extractor lowers `asm!` to `Terminator::Opaque { kind:
// "InlineAsm", targets }` and DROPS its output operands, so an `inout(reg) k` write is
// invisible to the version oracle: `let mut k = n & 3; asm!("add {0}, {0}, #4", inout(reg)
// k); t[k]` (aarch64) PROVES and certifies `t[k]` at -O0 and -O1 while every input panics.
// The function also carries the `UnsupportedMir { kind: "InlineAsm" }` Unknown row, so it
// is never fully verified; the per-obligation proof is still false (and counted by a
// per-obligation proof ledger). (The class-10 range lane declines the same write:
// `as01`/`as03` in adv_asm.rs stay Unknown.)
// ROOT: the extractor's `Opaque` keeps the successors and drops the destination, and
// trust-types says so -- `Terminator::place_writes` answers `PlaceWrites::Unlocatable`
// and `local_write` `LocalWrite::Unlocatable` for every local -- but the version oracle
// read the `Opaque` as a call WITHOUT a destination: `TermHavoc::Function` (the locals a
// pointer can reach), never a local that is only ever an asm OUTPUT. It now mints every
// local's write name there, as it already does for the other write with no place
// (`CopyNonOverlapping`), and the interval lane follows. `ploss_adv/h3_asm.rs` adds every
// place-writing operand kind (`out`, `lateout`, `inlateout`, a split `inout(reg) x =>
// k`, an explicit register), `options(nomem, nostack, pure)`, a field output, two
// outputs, a loop-carried output, and arithmetic / divisor / constant-index uses.
//
// Fixtures: `tests/fixtures/ploss_adv/{name}_o{0,1}.json`, extracted by the d36c551fa
// stage2 compiler (`rereview-tc`)
//
//   rustc -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-dump=mir-only:<dir> \
//         --edition 2024 --crate-type lib -Copt-level={0,1} --emit metadata <src>
//
// from `adv_ptrbound.rs`, `adv_ptrbound2.rs`, `adv_fold.rs`, `adv_cell.rs`, `adv_asm.rs`,
// `h1_alias.rs`, `h1_ctl.rs`, `h2_raw_const.rs`, `h3_asm.rs` beside them
// (span paths rewritten to `ploss_adv/<file>.rs`). Native runs, MIR dumps, verdicts on
// main and merged: ~/agent-evidence/2026-10-trust-soundness/ploss/adv/.
//
// `h1_alias_cast.rs` (`al07`-`al18`, 2026-10-11, LAUNDERED-ALIAS-STORE /
// LAUNDERED-ALIAS-ELIDE-1) was dumped the same way (`--crate-name adv`) by the stage 1
// of 1213387e6d (`scratchpad/stage1-w24probe`, main after wave 23).
use trust_types::{VcKind, VerifiableFunction, VerificationCondition, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

const LEVELS: [&str; 2] = ["o0", "o1"];

fn load(name: &str, level: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/ploss_adv/{name}_{level}.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json)
        .unwrap_or_else(|e| panic!("{path}: fixture MIR must deserialize: {e}"))
}

fn slice_row(kind: &VcKind) -> bool {
    matches!(kind, VcKind::SliceBoundsCheck)
}

fn index_row(kind: &VcKind) -> bool {
    matches!(kind, VcKind::IndexOutOfBounds)
}

fn overflow_row(kind: &VcKind) -> bool {
    matches!(kind, VcKind::ArithmeticOverflow { .. })
}

fn div_row(kind: &VcKind) -> bool {
    matches!(kind, VcKind::DivisionByZero)
}

struct Row {
    name: &'static str,
    line: u32,
    col: u32,
    kind: fn(&VcKind) -> bool,
}

const fn row(name: &'static str, line: u32, col: u32, kind: fn(&VcKind) -> bool) -> Row {
    Row { name, line, col, kind }
}

/// H1: PROVED and certified at -O0 and -O1 on origin/main c132f5a193 and on
/// land/proof-loss-fixes; every program panics.
const STALE_BOUND: &[Row] = &[
    row("pb04_folded_ref_bound_bug", 76, 7, slice_row),
    row("pb05_shared_ref_bound_bug", 88, 7, slice_row),
    row("pb10_mut_param_field_bug", 19, 7, slice_row),
    row("pb11_local_struct_field_bug", 31, 7, slice_row),
    row("pb12_pair_folded_end_bug", 45, 7, slice_row),
    row("pb14_range_from_folded_bug", 72, 7, slice_row),
    row("pb16_inclusive_folded_bug", 96, 7, slice_row),
    row("pb17_bound_pair_folded_bug", 109, 7, slice_row),
    row("pb06_yield_end_folded_ref_bug", 102, 15, index_row),
    row("pb13_yield_end_mut_param_field_bug", 58, 15, index_row),
    row("pb02_alias_param_write_range_bug", 43, 11, slice_row),
    // Found while fixing H1 (`ploss_adv/h1_alias.rs`): a CALLEE writes the field
    // between the range and the index (`r = ..s.len; set(s, n); if s.len > 8 {return}
    // buf[r]`, and the range-loop twin). PROVED and certified at -O0 and -O1 on
    // land/proof-loss-fixes; both panic at `s.len = 100, n = 3`.
    row("al04_callee_write_range_bug", 79, 7, slice_row),
    row("al05_callee_write_yield_bug", 90, 15, index_row),
];

/// H2: certified at -O0, PROVED and certified at -O1, on both trees; every program panics.
const RAW_CONST_STORE: &[Row] = &[
    row("fd08_raw_const_store_no_fold_bug", 148, 4, index_row),
    row("ce06_raw_const_store_index_bug", 70, 4, index_row),
    row("fd05_raw_const_cast_store_bug", 100, 4, index_row),
    // `ploss_adv/h2_raw_const.rs`, written while fixing H2: the same store through a
    // `&raw const` of an array ELEMENT, of a WHOLE struct (a field written through the
    // cast), after a guard, through `addr_of!(k).cast_mut()`, as a partial (`*mut u8`)
    // write, by a CALLEE handed the `*const`, carried in a tuple, and in a loop.
    row("h2b_elem_raw_const_store_bug", 25, 4, index_row),
    row("h2c_guarded_raw_const_store_bug", 37, 4, index_row),
    row("h2d_addr_of_cast_mut_bug", 47, 4, index_row),
    row("h2e_byte_store_bug", 56, 4, index_row),
    row("h2f_callee_store_bug", 67, 4, index_row),
    row("h2g_whole_struct_field_store_bug", 76, 4, index_row),
    row("h2h_tuple_carried_raw_const_bug", 84, 4, index_row),
    row("h2i_loop_store_bug", 97, 4, index_row),
];

/// H3: PROVED and certified at -O0 and -O1 on both trees; panics for every input.
const OPAQUE_ASM_OUTPUT: &[Row] = &[
    row("as02_asm_inout_index_bug", 21, 4, index_row),
    // `ploss_adv/h3_asm.rs`, written while fixing H3: every operand kind that writes a
    // place (`out`, `lateout`, `inlateout`, a split `inout(reg) x => k`, an explicit
    // register), `options(nomem, nostack, pure)`, a FIELD output, two outputs, and a
    // loop-carried output. Each PROVED and certified at -O0 and -O1 on 96db9eb9f0; each
    // panics on every input (h3k: on every input with two or more loop turns).
    row("h3a_out_bug", 19, 4, index_row),
    row("h3b_lateout_bug", 26, 4, index_row),
    row("h3c_inlateout_bug", 33, 4, index_row),
    row("h3d_split_inout_bug", 41, 4, index_row),
    row("h3e_nomem_pure_inout_bug", 48, 4, index_row),
    row("h3f_field_inout_bug", 55, 4, index_row),
    row("h3h_explicit_reg_out_bug", 69, 4, index_row),
    row("h3k_loop_inout_bug", 95, 15, index_row),
    row("h3l_second_output_bug", 106, 4, index_row),
    // The asm output feeds an ARITHMETIC row (`k + 1` on a `u8` the asm set to 255:
    // panics at -O0 and with debug assertions; plain -O1 wraps to 0, so the row's
    // no-overflow claim is false there too), a DIVISOR (`n / k`, `k == 1` before the asm,
    // 0 after), and a CONSTANT index (`k == 1` before the asm, 4 after).
    row("h3m_overflow_after_asm_bug", 163, 4, overflow_row),
    row("h3n_divisor_after_asm_bug", 171, 4, div_row),
    row("h3o_const_then_asm_index_bug", 178, 4, index_row),
    // Already refuted on 96db9eb9f0 (pinned so the fix cannot reopen them): the output
    // place `*k` of a `&mut` parameter, and the MEMORY clobber -- the asm stores through
    // a pointer it receives as an input (`&raw mut k`; a `&mut St` parameter's field).
    row("h3g_deref_inout_bug", 62, 4, index_row),
    row("h3i_store_through_ptr_bug", 78, 4, index_row),
    row("h3j_store_through_param_bug", 86, 4, index_row),
];

fn router() -> trust_router::Router {
    test_router::deterministic_test_router()
}

/// The panic rows of `r` at `level`: the rows at `r`'s span whose kind is `r.kind`, or
/// the declined `UnsupportedMir` row a lane emits in its place (`slice-range-*` when the
/// slice range-index bound is not licensed, `UnmodeledCalleeReturn` when the yield fact
/// is withheld and the index is an unmodelled `next` payload). Each with its verdict and
/// whether `certify_vc` certifies it.
fn verdicts(r: &Row, level: &str) -> Vec<(VerificationCondition, VerificationResult, bool)> {
    let func = load(r.name, level);
    let (line, col, kind) = (r.line, r.col, r.kind);
    let (name, level) = (r.name, level.to_string());
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let vcs: Vec<VerificationCondition> = trust_vcgen::generate_vcs(&func)
                .into_iter()
                .filter(|vc| {
                    vc.location.line_start == line
                        && vc.location.col_start == col
                        && (kind(&vc.kind) || matches!(vc.kind, VcKind::UnsupportedMir { .. }))
                })
                .collect();
            assert!(!vcs.is_empty(), "{name} {level}: no panic row at {line}:{col}");
            let results = router().verify_all(&vcs);
            results
                .into_iter()
                .map(|(vc, result)| {
                    let certified = trust_certify::certify_vc(&vc).is_some();
                    (vc, result, certified)
                })
                .collect()
        })
        .expect("spawn")
        .join()
        .expect("generation and verification must not panic")
}

/// [`verdicts`] through the entry the compiler drives -- generation paired with the
/// in-pass interval discharge (`generate_vcs_with_discharge`): a row the abstract-
/// interpretation pre-pass discharges is answered there and never reaches the solver,
/// and every row that does reach it carries that pre-pass's interval assumptions. A
/// stale interval across an `asm!` is a false proof on THIS path even when the
/// formula path (`generate_vcs`) re-versions the written local.
fn verdicts_with_discharge(
    r: &Row,
    level: &str,
) -> Vec<(VerificationCondition, VerificationResult, bool)> {
    let func = load(r.name, level);
    let (line, col, kind) = (r.line, r.col, r.kind);
    let (name, level) = (r.name, level.to_string());
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let at_row = |vc: &VerificationCondition| {
                vc.location.line_start == line
                    && vc.location.col_start == col
                    && (kind(&vc.kind) || matches!(vc.kind, VcKind::UnsupportedMir { .. }))
            };
            let (solver_vcs, discharged) = trust_vcgen::generate_vcs_with_discharge(&func);
            let mut out: Vec<(VerificationCondition, VerificationResult)> =
                discharged.into_iter().filter(|(vc, _)| at_row(vc)).collect();
            let to_solve: Vec<VerificationCondition> =
                solver_vcs.into_iter().filter(|vc| at_row(vc)).collect();
            out.extend(router().verify_all(&to_solve));
            assert!(!out.is_empty(), "{name} {level}: no panic row at {line}:{col} (discharge)");
            out.into_iter()
                .map(|(vc, result)| {
                    let certified = trust_certify::certify_vc(&vc).is_some();
                    (vc, result, certified)
                })
                .collect()
        })
        .expect("spawn")
        .join()
        .expect("generation and verification must not panic")
}

fn unsound(rows: &[Row]) -> Vec<String> {
    let mut bad = Vec::new();
    for r in rows {
        for level in LEVELS {
            for (vc, result, certified) in verdicts(r, level) {
                let proved = matches!(result, VerificationResult::Proved { .. });
                if proved || certified {
                    bad.push(format!(
                        "{} {level} {}:{} {:?}: proved={proved} certified={certified}",
                        r.name, r.line, r.col, vc.kind
                    ));
                }
            }
        }
    }
    bad
}

/// The rows of `rows` that are not PROVED (or that a lane declined to `UnsupportedMir`).
fn not_proved(rows: &[Row]) -> Vec<String> {
    let mut lost = Vec::new();
    for r in rows {
        for level in LEVELS {
            for (vc, result, _) in verdicts(r, level) {
                if !matches!(result, VerificationResult::Proved { .. }) || !(r.kind)(&vc.kind) {
                    lost.push(format!(
                        "{} {level} {}:{} {:?}: {result:?}",
                        r.name, r.line, r.col, vc.kind
                    ));
                }
            }
        }
    }
    lost
}

#[test]
fn h1_stale_bound_renamed_at_the_call_is_never_proved() {
    let bad = unsound(STALE_BOUND);
    assert!(bad.is_empty(), "panicking programs' rows proved or certified:\n{}", bad.join("\n"));
}

#[test]
fn h2_store_through_raw_const_pointer_is_never_proved() {
    let bad = unsound(RAW_CONST_STORE);
    assert!(bad.is_empty(), "panicking programs' rows proved or certified:\n{}", bad.join("\n"));
}

/// H2's CONTROLS (`ploss_adv/h2_raw_const.rs`): correct programs that take a `&raw const`
/// of a local and only READ through it, store through a `&raw const` of ANOTHER local
/// (`k` itself is never borrowed), guard the value AFTER the store, and the slice index
/// whose bounds prelude takes `&raw const (*s)` (a borrow BEHIND a reference, which the
/// own-storage rule leaves to the reference's own channel). On land/proof-loss-fixes + H1
/// (252f3a9fbf) every row is PROVED at -O1, and at -O0 `certify_vc` certifies it (the
/// router answers Unknown there for all but `h2c8`, which it PROVES); the H2 fix must
/// keep each row proved or certified, at both levels.
#[test]
fn h2_raw_const_controls_keep_their_proofs() {
    const CONTROLS: &[Row] = &[
        row("h2c1_raw_const_read_ctl", 106, 4, index_row),
        row("h2c2_raw_const_other_store_ctl", 115, 4, index_row),
        row("h2c3_raw_const_read_both_ctl", 123, 4, index_row),
        row("h2c3_raw_const_read_both_ctl", 123, 11, index_row),
        row("h2c4_guard_after_store_ctl", 134, 4, index_row),
        row("h2c8_slice_param_ctl", 166, 4, slice_row),
    ];
    let mut lost = Vec::new();
    for r in CONTROLS {
        for level in LEVELS {
            for (vc, result, certified) in verdicts(r, level) {
                let proved = matches!(result, VerificationResult::Proved { .. });
                if !(r.kind)(&vc.kind) || !(proved || certified) {
                    lost.push(format!(
                        "{} {level} {}:{} {:?}: {result:?} certified={certified}",
                        r.name, r.line, r.col, vc.kind
                    ));
                }
            }
        }
    }
    assert!(lost.is_empty(), "correct programs' rows lost their proofs:\n{}", lost.join("\n"));
}

/// THE PRECISION THE H2 FIX COSTS, pinned as a consistency property: a `&raw const k`
/// is now the write channel a `&raw mut k` always was, so a correct program that takes
/// one, reads through it, and makes an unrelated call (`h2c6`) gets the verdict its
/// `&raw mut` twin (`h2c7`) already got on land/proof-loss-fixes: the call havocs every
/// write-borrowed local (`path_defs::escape_havoc`, the coarse TINV-18 rule), so `k` is
/// free after `black_box` and the index is refuted at both levels. (`h2c6` was PROVED at
/// -O1 and certified at -O0 before the fix -- the one correct-program row the fix loses
/// over the parity corpora.) A precision fix for the pair -- a write-borrow whose pointer
/// is only ever read through cannot write -- must move both rows together.
#[test]
fn h2_raw_const_answers_like_raw_mut() {
    let shape = |name: &'static str, line: u32, level: &str| -> Vec<(String, &'static str, bool)> {
        verdicts(&row(name, line, 4, index_row), level)
            .into_iter()
            .map(|(vc, result, certified)| {
                let verdict = match result {
                    VerificationResult::Proved { .. } => "proved",
                    VerificationResult::Failed { .. } => "failed",
                    VerificationResult::Unknown { .. } => "unknown",
                    _ => "other",
                };
                (format!("{:?}", vc.kind), verdict, certified)
            })
            .collect()
    };
    for level in LEVELS {
        let raw_const = shape("h2c6_raw_const_then_call_ctl", 150, level);
        let raw_mut = shape("h2c7_raw_mut_then_call_ctl", 158, level);
        assert_eq!(raw_const, raw_mut, "{level}: `&raw const` and `&raw mut` twins disagree");
    }
}

#[test]
fn h3_inline_asm_output_is_never_ignored() {
    let bad = unsound(OPAQUE_ASM_OUTPUT);
    assert!(bad.is_empty(), "panicking programs' rows proved or certified:\n{}", bad.join("\n"));
}

/// H3 through the compiler's entry (`generate_vcs_with_discharge`): the interval
/// pre-pass must forget what an `Opaque` terminator may write, exactly as the formula
/// path re-versions it, or its merged environment discharges the row (or hands the
/// solver the stale interval as an assumption).
#[test]
fn h3_inline_asm_output_is_never_discharged() {
    let mut bad = Vec::new();
    for r in OPAQUE_ASM_OUTPUT {
        for level in LEVELS {
            for (vc, result, certified) in verdicts_with_discharge(r, level) {
                let proved = matches!(result, VerificationResult::Proved { .. });
                if proved || certified {
                    bad.push(format!(
                        "{} {level} {}:{} {:?}: {result:?} certified={certified}",
                        r.name, r.line, r.col, vc.kind
                    ));
                }
            }
        }
    }
    assert!(bad.is_empty(), "panicking programs' rows discharged:\n{}", bad.join("\n"));
}

/// H3, the interval lane itself: the abstract state on an `asm!`'s out-edge must contain
/// the value the asm WROTE into its output `k` (4 for the index rows, 255 for `h3m`, 0 for
/// `h3n`). On 96db9eb9f0 the edge kept `k`'s pre-asm interval (`[0, 3]`, `[1, 1]`):
/// `transfer_terminator` forgot what a `Call` may write but not what an `Opaque`
/// terminator may, while the formula path versions every local there. No row above is
/// discharged by that stale state today (the evaluator gives up on these formulas), but
/// the discharge's whole-function join, which a versioned name falls back to, rests on
/// the state holding at every program point.
#[test]
fn h3_interval_state_contains_the_asm_written_value() {
    const WRITTEN: &[(&str, i128)] = &[
        ("as02_asm_inout_index_bug", 4),
        ("h3a_out_bug", 4),
        ("h3b_lateout_bug", 4),
        ("h3c_inlateout_bug", 4),
        ("h3d_split_inout_bug", 4),
        ("h3e_nomem_pure_inout_bug", 4),
        ("h3h_explicit_reg_out_bug", 4),
        ("h3k_loop_inout_bug", 4),
        ("h3l_second_output_bug", 4),
        ("h3m_overflow_after_asm_bug", 255),
        ("h3n_divisor_after_asm_bug", 0),
        ("h3o_const_then_asm_index_bug", 4),
    ];
    let mut bad = Vec::new();
    for &(name, written) in WRITTEN {
        for level in LEVELS {
            let func = load(name, level);
            let fp = trust_vcgen::fixpoint(&func, trust_vcgen::type_aware_initial_state(&func));
            let mut edges = 0;
            for block in &func.body.blocks {
                let trust_types::Terminator::Opaque { kind, targets, .. } = &block.terminator
                else {
                    continue;
                };
                if kind != "InlineAsm" {
                    continue;
                }
                for target in targets {
                    edges += 1;
                    let Some(state) = fp.block_states.get(target) else { continue };
                    let k = state.get("k");
                    if state.is_unreachable || k.lo > written || k.hi < written {
                        bad.push(format!(
                            "{name} {level} bb{} -> bb{}: k in [{}, {}] excludes {written}",
                            block.id.0, target.0, k.lo, k.hi
                        ));
                    }
                }
            }
            assert!(edges > 0, "{name} {level}: no InlineAsm out-edge");
        }
    }
    assert!(bad.is_empty(), "stale intervals across an asm:\n{}", bad.join("\n"));
}

/// H3's CONTROLS (`ploss_adv/h3_asm.rs`): correct programs with an `asm!` block whose
/// index fact does not cross the asm -- the guard tests the asm's OUTPUT after it
/// (`h3c1`), the fact is established after it (`h3c2`), the bound is the array TYPE's
/// (`h3c3`, a constant index). PROVED and certified at -O0 and -O1 on 96db9eb9f0; the H3
/// fix must keep each row PROVED.
#[test]
fn h3_inline_asm_controls_still_prove() {
    const CONTROLS: &[Row] = &[
        row("h3c1_guard_after_asm_ctl", 118, 4, index_row),
        row("h3c2_fact_after_asm_ctl", 126, 4, index_row),
        row("h3c3_const_index_ctl", 133, 4, index_row),
    ];
    let lost = not_proved(CONTROLS);
    assert!(lost.is_empty(), "correct programs' rows no longer proved:\n{}", lost.join("\n"));
}

/// OPEN, the precision the H3 fix costs -- ASM-OPERANDS-NOT-EXTRACTED. Correct programs
/// whose index fact crosses an `asm!` that cannot write the indexed local: `k` is only an
/// `in` operand (`h3c4`, `options(nomem)`), the asm's one output is ANOTHER local (`h3c5`,
/// `options(nomem, pure)`), the asm is a memory-clobbering `nop` and `k`'s address never
/// escapes (`h3c6`). PROVED and certified at -O0 and -O1 on 96db9eb9f0; the H3 fix
/// REFUTES all three, because `Terminator::Opaque { kind: "InlineAsm" }` carries no
/// operand, so every local is a possible output (`PlaceWrites::Unlocatable`) -- the
/// verdict a call that may write `k` gets (`h2c7`). Re-proving them needs the operands
/// where they exist, in rustc's MIR: the extractor must carry each `out` / `lateout` /
/// `inout` / `inlateout` place and the `nomem` / `readonly` options on the terminator,
/// and `Terminator::place_writes` must then answer those places instead of
/// `Unlocatable` (a memory-clobbering asm keeps the `Function` havoc).
#[test]
#[ignore = "ASM-OPERANDS-NOT-EXTRACTED: `Opaque{InlineAsm}` carries no operands, so every local is a possible asm output"]
fn h3_asm_that_cannot_write_k_keeps_its_proof() {
    const CONTROLS: &[Row] = &[
        row("h3c4_input_only_ctl", 140, 4, index_row),
        row("h3c5_nomem_other_output_ctl", 148, 4, index_row),
        row("h3c6_clobber_unescaped_ctl", 155, 4, index_row),
    ];
    let lost = not_proved(CONTROLS);
    assert!(lost.is_empty(), "correct programs' rows no longer proved:\n{}", lost.join("\n"));
}

/// The mirror of H1 (a false REFUTATION, not a false proof): the guard tests the value the
/// range was built from, the write comes after. Correct on every input (64-run sweep). The
/// licence that names the pointee by the storage it denotes declines it (Unknown) instead
/// of binding the bound to its post-write value: it must never be refuted.
#[test]
fn h1_mirror_control_is_not_refuted() {
    // `al06_callee_write_guard_first_ctl` is the callee-write mirror (guard, range,
    // `set(s, n)`, index), refuted on land/proof-loss-fixes the same way.
    let mirrors = [
        row("pb15_folded_guard_first_ctl", 84, 7, slice_row),
        row("al06_callee_write_guard_first_ctl", 102, 7, slice_row),
    ];
    for r in &mirrors {
        for level in LEVELS {
            for (vc, result, _) in verdicts(r, level) {
                assert!(
                    !matches!(result, VerificationResult::Failed { .. }),
                    "{} {level}: correct program refuted: {:?}",
                    r.name,
                    vc.formula
                );
            }
        }
    }
}

/// LAUNDERED-ALIAS-STORE, found while fixing H1 (not a range defect), and its overflow
/// form LAUNDERED-ALIAS-ELIDE-1 (2026-10-11): a store through `p = &raw mut len` did not
/// version a read through a copy of `p` that the referent fold cannot resolve, so `*q`
/// before and after the store shared one name. The ORDINARY read
/// `x = *q; *p = n; if *q > 7 {return} buf[x]` (`al02`) was PROVED and certified at -O0 and -O1 on
/// land/proof-loss-fixes and panics at `m = 100, n = 3`. Its range (`al01`) and
/// range-loop (`al03`) forms were PROVED there too; after the H1 fix both decline. The
/// laundering needs no call: `p as *const usize` (`al07`), the `&mut len` coercion plus
/// a cast (`al08`), `cast_const()` (`al09`), `wrapping_add(0)` (`al10`) and the opaque
/// `launder(p)` (`al11`) each left the `x + 1` row PROVED and kernel-certified on the
/// stage 1 of 1213387e6d, where the advisory lane then ELIDED the overflow check (the
/// binary returns 0 where rustc panics; `tests/ui/trust/laundered_alias_overflow_elide_run.rs`).
/// `al12` writes `len` DIRECTLY (`len = n`) instead of through `p`. `al13` (the store
/// through the cast copy, the reads through `p`) and `al14` (the store through a second
/// copy made by a call) were already kept: pinned so the fix cannot reopen them. All
/// panic at `m = usize::MAX, n = 3`; all are valid under Stacked and Tree Borrows
/// except `al12` under Stacked Borrows (the direct write pops `p`'s tag), which is still
/// a valid program under Tree Borrows.
///
/// THE FIX: the referent fold sees through a raw-pointer cast with an identical
/// pointee (`lib.rs` `resolve_referent_guarded`, the `Rvalue::Cast` arm: `al07`, `al08`
/// are then named by `len` itself), and a write to storage whose address was taken, in
/// a body that reads through a raw pointer the fold cannot resolve, havocs the
/// whole-function list exactly as an opaque store does
/// (`path_defs::write_havocs_function_list`: `al09`-`al12`).
///
/// LAUNDERED-ALIAS-CELL-1 (wave-24 review, 2026-10-12): the address may also escape by a
/// SHARED borrow of interior-mutable storage (`Cell::as_ptr(&c)`). `al19` (a direct
/// write `c = nc`) and `al20` (a store through a same-pointee cast of `&c`) left the
/// `x + 1` row PROVED and kernel-certified after the fix above; the root set now takes
/// every shared borrow of a place that may hold an `UnsafeCell` inline
/// (`path_defs::laundered_alias_roots`).
const LAUNDERED_ALIAS: &[Row] = &[
    row("al01_launder_store_range_bug", 33, 11, slice_row),
    row("al02_launder_store_read_bug", 49, 8, index_row),
    row("al03_launder_store_yield_bug", 65, 19, index_row),
    row("al07_cast_store_add_bug", 29, 8, overflow_row),
    row("al08_local_ref_cast_add_bug", 45, 8, overflow_row),
    row("al09_cast_const_add_bug", 60, 8, overflow_row),
    row("al10_wrapping_add_add_bug", 75, 8, overflow_row),
    row("al11_launder_call_add_bug", 90, 8, overflow_row),
    row("al12_direct_store_add_bug", 105, 8, overflow_row),
    row("al13_rev_cast_store_add_bug", 122, 8, overflow_row),
    row("al14_two_cast_add_bug", 139, 8, overflow_row),
    // LAUNDERED-ALIAS-CELL-1 (wave-24 review, 2026-10-12; dumped by the stage 1 of
    // 51eac007f3, `scratchpad/stage1-w24`): the address escapes by a SHARED borrow of a
    // `Cell` (`Cell::as_ptr(&c)`), which rooted nothing, so a direct write `c = nc`
    // (`al19`) and a store through `&c as *const Cell<usize> as *mut Cell<usize>`
    // (`al20`, which the wave-24 `Cast` arm folds to `c`) left the `x + 1` row PROVED.
    row("al19_cell_direct_add_bug", 215, 8, overflow_row),
    row("al20_cell_cast_store_add_bug", 235, 8, overflow_row),
];

#[test]
fn laundered_alias_store_is_never_proved() {
    let bad = unsound(LAUNDERED_ALIAS);
    assert!(bad.is_empty(), "panicking programs' rows proved or certified:\n{}", bad.join("\n"));
}

/// [`laundered_alias_store_is_never_proved`] through the entry the compiler drives
/// (`generate_vcs_with_discharge`): the interval pre-pass must not discharge a row the
/// formula path no longer proves. The compiler elides an overflow check on exactly
/// this path's `Proved` + certified answer.
#[test]
fn laundered_alias_store_is_never_discharged() {
    let mut bad = Vec::new();
    for r in LAUNDERED_ALIAS {
        for level in LEVELS {
            for (vc, result, certified) in verdicts_with_discharge(r, level) {
                let proved = matches!(result, VerificationResult::Proved { .. });
                if proved || certified {
                    bad.push(format!(
                        "{} {level} {}:{} {:?}: {result:?} certified={certified}",
                        r.name, r.line, r.col, vc.kind
                    ));
                }
            }
        }
    }
    assert!(bad.is_empty(), "panicking programs' rows discharged:\n{}", bad.join("\n"));
}

/// LAUNDERED-ALIAS-STORE's CONTROLS (`ploss_adv/h1_alias_cast.rs`): correct programs
/// beside the bugs -- the guard read BEFORE the store (`al15`), every access through `p`
/// itself (`al16`), a laundered copy that is only read (`al17`), and a store followed by
/// reads through the laundered copy that do not straddle it (`al18`). Each `x + 1` /
/// `*p + 1` / `*q + 1` overflow row was PROVED at -O0 and -O1 by the deterministic
/// in-process ay router before the fix (the crate's tree at 1213387e6d); the fix must
/// keep each one PROVED: no read that straddles no write loses a version.
///
/// Only the OVERFLOW row is asked, and it must be there: the `UnsupportedMir` rows at
/// the same span are the dereference's own `MisalignedPointerDereference` /
/// `NullPointerDereference` asserts (unmodelled by vcgen on every tree), not a lane
/// declining the overflow row, which is what [`not_proved`] counts them as.
#[test]
fn laundered_alias_controls_still_prove() {
    const CONTROLS: &[Row] = &[
        row("al15_cast_guard_first_ctl", 154, 8, overflow_row),
        row("al16_p_only_store_ctl", 168, 8, overflow_row),
        row("al17_cast_read_only_ctl", 181, 8, overflow_row),
        row("al18_store_then_read_ctl", 196, 8, overflow_row),
        // LAUNDERED-ALIAS-CELL-1's control: `al19` with the guard before the write.
        row("al21_cell_guard_first_ctl", 250, 8, overflow_row),
    ];
    let mut lost = Vec::new();
    for r in CONTROLS {
        for level in LEVELS {
            let rows: Vec<_> =
                verdicts(r, level).into_iter().filter(|(vc, _, _)| (r.kind)(&vc.kind)).collect();
            if rows.is_empty() {
                lost.push(format!("{} {level} {}:{}: no overflow row", r.name, r.line, r.col));
            }
            for (vc, result, _) in rows {
                if !matches!(result, VerificationResult::Proved { .. }) {
                    lost.push(format!(
                        "{} {level} {}:{} {:?}: {result:?}",
                        r.name, r.line, r.col, vc.kind
                    ));
                }
            }
        }
    }
    assert!(lost.is_empty(), "correct programs' rows no longer proved:\n{}", lost.join("\n"));
}

/// H1's CONTROLS: correct programs whose slice-range bound or range-loop end is read
/// through a reference or a pointer, and that PROVE on origin/main c132f5a193 and on
/// land/proof-loss-fixes (`ploss_adv/h1_ctl.rs`: a guarded `&St` field `..s.len`, a
/// single-assignment local through `z = &len` (`..*z`, `0..*z`), a guarded `&mut St`
/// field never written, and a field a callee writes BEFORE the guard and the range).
/// The H1 fix must keep every one of these rows PROVED: the global resolver keeps
/// answering a pointee that holds one value, and `range_bound_use` names one that a
/// callee wrote earlier by its version at the read into the range (`pc06`).
#[test]
fn h1_projected_bound_controls_still_prove() {
    const CONTROLS: &[Row] = &[
        row("pc01_param_field_guarded_ctl", 21, 7, slice_row),
        row("pc02_folded_ssa_local_ctl", 28, 7, slice_row),
        row("pc03_yield_param_field_ctl", 38, 15, index_row),
        row("pc04_yield_folded_ssa_ctl", 49, 15, index_row),
        row("pc05_mut_param_field_no_write_ctl", 61, 7, slice_row),
        row("pc06_call_before_range_ctl", 70, 7, slice_row),
    ];
    let lost = not_proved(CONTROLS);
    assert!(lost.is_empty(), "correct programs' rows no longer proved:\n{}", lost.join("\n"));
}

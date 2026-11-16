//! TRUST-KI-1015-1, the padding-tail shape of aterm-digest `Sha256::finalize`
//! (`sha256.rs:154:16` at aterm `848d791bd`): a correct `[slice]` row was FAILED.
//!
//! ```text
//! self.buf[self.buf_len] = 0x80;
//! self.buf_len += 1;
//! if self.buf_len > BLOCK_LEN - 8 { self.buf[self.buf_len..].fill(0); ..; self.buf_len = 0; }
//! self.buf[self.buf_len..BLOCK_LEN - 8].fill(0);    // in range on every path
//! ```
//!
//! # The defect (measured)
//!
//! On the channel seal `b58a105dde` the row was the declined `UnsupportedMir`
//! (`slice-range-bounds-unresolved`, Unknown). On main (`5138cede2c`, crate level) it is
//! `[slice]` FAILED by the in-process `ay` lane, with the model `_10 = 0`,
//! `_8.0 = 57`, `self.2#s10_0_s5_0 = 57` in `ok_finalize` (line 43). The MIR (`self` is
//! `_1`, `buf_len` its field `.2`):
//!
//! ```text
//! bb5:  _1.2 = move _8.0; _10 = copy _1.2; _12 = CheckedSub(const 64, const 8);
//!       assert(!move _12.1) -> bb6
//! bb6:  _11 = move _12.0; _9 = Gt(move _10, move _11); switchInt(move _9) -> [0: bb11, otherwise: bb7]
//! bb7..bb10 (the guard's arm; index_mut / fill / compress calls): ..; _1.2 = const 0; goto bb11
//! bb11 (the join, also the skip edge's target): _26 = copy _1.2; _28 = CheckedSub(64, 8); ..
//! bb12: .. index_mut(.., _26.._27)
//! ```
//!
//! The VC carried the branch merge (`!_9 => self.2#join == _8.0`, `_9 => self.2#join ==
//! 0`), the path guard `!(_10 > _11)` and `_26 == self.2#join`, but no fact on `_10`:
//! `_10 == self.buf_len`, made in `bb5` and so an ENTRY fact of the switch block `bb6`,
//! dies on the arm (which writes `buf_len`), the join's intersection dropped it, and the
//! guard constrained a free variable. Main made the row REFUTABLE without making it
//! decidable: `491bc3c273` (on main since `106337649b`) resolves the range bound `_26` at
//! the call, where the channel declined it, so the over-approximated VC reached `ay` and
//! its model was published as a counterexample.
//! The same holds through `&mut self` (`ok_finalize_ref`), over plain locals
//! (`ok_local`), and with the guard on a field's ENTRY value (`ok_entry_tail`), where
//! the skip edge has no definition of the length at all and the partial merge, which
//! wants two defining arms, says nothing about it.
//!
//! # The fix (`guards::skip_edge_join_definitions`)
//!
//! At a join the single-switch merge admits, with a skip edge `S -> J` (an `if` without
//! `else`): every bare `x == y` the path-definition fixpoint carries along the skip
//! edge that `J`'s intersection lost is restated as `g_skip => x == y`, and the other
//! arms' values of such a `y` as `g_i => y == v`, read from each arm's own outflow into
//! `J`. `g_i` are the exact route predicates the merges already use. Every conclusion is
//! a fact the fixpoint itself carries along that edge (`path_defs::path_def_base_outflow`
//! is the fixpoint's own step), so it adds no premise. Here the skip edge gives
//! `!_9 => _10 == self.2#join`, the false edge bounds `_10`, and the row is PROVED.
//! Because the copy is an entry fact of the switch block, the step's kills of entry facts
//! (the deref-store havoc, the kill of a declined definition's destination) are what keep
//! a restated copy true: `bad_byte_store_in_switch` and `bad_declined_rem_in_switch` are
//! the rows that show it.
//!
//! # What these tests pin
//!
//! * the tail row of every correct program, and of aterm-digest's own `finalize`, is
//!   PROVED (by `ay`; not kernel-certified, so targo's publication boundary withholds it
//!   as UNKNOWN: either way not FAILED);
//! * every wrong twin keeps its tail row exactly as on main: FAILED, or for the six
//!   whose row main does not decide (a raw-pointer store the bound resolution declines,
//!   a solver-incomplete alias, the `56 - n` of a raw-pointer store, the `static mut`
//!   read), never PROVED. Each panics natively at that row ("slice
//!   index starts at 57 but ends at 56", or for the `56 - n` twins "attempt to subtract
//!   with overflow"; the channel's `targo --unverified test` on a byte-for-byte copy of
//!   `tests/data/finalize_tail.rs`);
//! * a store the guard's copy does not see keeps a DECIDED row FAILED: the review's
//!   counterexamples to an outflow rebuilt without the fixpoint's entry-fact kills (a
//!   byte store through a `*mut u8` and a declined `%` in the switch block), and decided
//!   twins of the pointer-store rows above;
//! * the restated facts are the skip edge's and the arm's, each under its own route;
//! * a correct `+= 1` after the join (inside two wrong twins) is PROVED: the facts reach
//!   arithmetic rows too;
//! * aterm-digest's spill-branch slice (`sha256.rs:148:20`) stays the deliberate decline;
//! * the one correct row the fix was measured to move from Unknown to FAILED: the
//!   separation lane's null check of a `static mut` read (`bad_static_arm_call`), which
//!   that lane does not model (KNOWN_HAZARDS, TRUST-KI-1015-1).
//!
//! # Falsification (2026-10-15)
//!
//! Each mutant was built and run against these tests and the lib's `skip_edge_join` tests
//! (records: `~/salvage-2026-09-28/records/digest-finalize-tail-revise2/`, measurement 2):
//!
//! * `skip_edge_join_definitions` returning no fact (M-J): the PROVE tests, the
//!   restated-facts test, the after-the-join test and the static pin go red (every row as
//!   on main); the store, wrong-twin, undecided and decline tests stay green.
//! * the skip edge's and the arms' outflow rebuilt from their own definitions without the
//!   fixpoint's entry-fact kills (MK): the store test goes red (`bad_byte_store_in_switch`
//!   and `bad_declined_rem_in_switch` PROVED, and nothing else moves); dropping only the
//!   deref-store havoc reddens it through the byte store, dropping only the
//!   declined-destination kill through the `%`. Every other test stays green.
//! * the restated facts unguarded, or under the other edge's guard: the wrong-twin test
//!   goes red (`bad_entry_threshold` and `bad_entry_inverted` PROVED unguarded,
//!   `bad_entry_inverted` swapped), with the PROVE, restated-facts and static tests.
//! * the investigator's WIP (copies from the switch block's own definitions, kept when its
//!   write set rebinds neither side): all eight stay green.
//!
//! No mutant reddens the undecided test: it pins the decline, not the fix.
//!
//! # Fixtures
//!
//! `tests/fixtures/finalize_tail/<fn>_mir.json` are the compiler's own extraction of
//! `tests/data/finalize_tail.rs`, captured with the channel seal's raw `trustc`
//! (`b58a105dde`, `TRUSTD_DISABLE=1`, no jobserver) from the repository root:
//!
//! ```text
//! trustc --crate-type lib --edition 2024 --crate-name repro --emit=metadata \
//!        -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-dump=mir-only:<dir> \
//!        crates/trust-vcgen/tests/data/finalize_tail.rs
//! ```
//!
//! `aterm_digest_sha256_finalize_mir.json` is the same capture of aterm-digest's
//! `src/lib.rs` at aterm `848d791bd` (`Sha256::finalize`, the row at line 154). Rows are
//! produced through the entry the compiler calls (hardened profile ON) and decided by the
//! deterministic in-process `ay` router (`support/realmir_rows.rs`).
#[path = "support/realmir_rows.rs"]
mod realmir_rows;

use realmir_rows::{PRIMARY_ADD, PRIMARY_SUB, Row, TWIN_ADD, TWIN_SUB, Verdict, at, expect, rows};

const SLICE: &str = "SliceBoundsCheck";

fn fixture(name: &str) -> Vec<Row> {
    rows("finalize_tail/", name, &[])
}

/// The rendered formula of the one `kind` row at `line`.
fn formula_at(rows: &[Row], line: u32, kind: &str) -> String {
    let hits = at(rows, line, kind);
    assert_eq!(hits.len(), 1, "line {line}: one `{kind}` row");
    format!("{:?}", hits[0].vc.formula)
}

#[test]
fn the_padding_tail_of_a_correct_finalize_is_proved() {
    for (name, line) in [
        ("ok_finalize", 43),
        ("ok_finalize_ref", 59),
        ("ok_local", 192),
        ("ok_entry_tail", 176),
        ("aterm_digest_sha256_finalize", 154),
    ] {
        let rs = fixture(name);
        expect(
            &rs,
            line,
            SLICE,
            1,
            Verdict::Proved,
            &format!("{name}: the tail slice is in range on every path"),
        );
    }
}

#[test]
fn every_wrong_twin_keeps_its_tail_refuted() {
    for (name, line) in [
        ("bad_threshold", 74),
        ("bad_no_reset", 88),
        ("bad_stale_guard", 104),
        ("bad_increment_after_guard", 119),
        ("bad_write_after_guard", 135),
        ("bad_threshold_ref", 150),
        ("bad_guard_on_stale_copy", 166),
        ("bad_entry_threshold", 202),
        ("bad_entry_clamp_value", 212),
        ("bad_entry_inverted", 222),
        ("bad_entry_ref_store", 236),
        ("bad_raw_alias_store_straight", 311),
    ] {
        let rs = fixture(name);
        expect(
            &rs,
            line,
            SLICE,
            1,
            Verdict::Failed,
            &format!("{name}: panics natively at `buf[57..56]`"),
        );
    }
}

/// A store the guard's copy does not see, on a DECIDED row: each program panics at its
/// `56 - n` (the `_sub` twins of the pointer-store rows below, and the review's two
/// counterexamples). Every row stays FAILED, primary and hardened twin, exactly as on
/// main. `bad_byte_store_in_switch` and `bad_declined_rem_in_switch` copy `n` to `t` in
/// one block and write `n` in the switch block itself, where only the fixpoint's kills of
/// ENTRY facts (the deref-store havoc; the kill of a declined definition's destination)
/// drop `t == n`: an outflow rebuilt from the block's own definitions restates `t == n`
/// on the skip edge and proves `56 - n` (measured: both rows PROVED under that mutant).
/// `bad_param_arm_ref_store_sub` is the arm's half: `n` is a parameter no merge defines,
/// and the arm's `n = 0` is overwritten through a `&mut` before the join.
#[test]
fn a_store_the_guard_does_not_see_is_never_proved() {
    for (name, line) in [
        ("bad_declined_rem_in_switch", 335),
        ("bad_byte_store_in_switch", 351),
        ("bad_entry_ref_store_sub", 363),
        ("bad_local_arm_raw_store_sub", 388),
        ("bad_local_two_arm_raw_store_sub", 401),
        ("bad_param_arm_ref_store_sub", 412),
    ] {
        let rs = fixture(name);
        let why = format!("{name}: panics natively at `56 - 57`");
        expect(&rs, line, PRIMARY_SUB, 1, Verdict::Failed, &why);
        expect(&rs, line, TWIN_SUB, 1, Verdict::Failed, &why);
    }
}

/// The twins whose tail row main does not decide: a store through a raw pointer to the
/// length (the bound resolution declines the slice row, `slice-range-bounds-unresolved`,
/// before any restated fact could matter), two raw pointers that may alias (`ay` answers
/// Unknown), and the `56 - n` twin of the first (Unknown). These pin that the rows stay
/// undecided, NOT the restated facts: they stay green under every mutant of the fix
/// measured (see the header). The decided store rows are the test above.
#[test]
fn the_undecided_store_twins_are_never_proved() {
    let slice: &[&str] = &[SLICE, "slice-range-bounds-unresolved"];
    let sub: &[&str] = &[PRIMARY_SUB, TWIN_SUB];
    for (name, line, needles) in [
        ("bad_local_raw_store", 249, slice),
        ("bad_local_arm_raw_store", 262, slice),
        ("bad_local_two_arm_raw_store", 276, slice),
        ("bad_raw_alias_store", 294, slice),
        ("bad_local_raw_store_sub", 376, sub),
    ] {
        let rs = fixture(name);
        let tail: Vec<&Row> = rs
            .iter()
            .filter(|r| r.line == line && needles.iter().any(|n| r.kind.contains(n)))
            .collect();
        assert!(!tail.is_empty(), "{name}: the tail row at line {line} is generated");
        for row in tail {
            assert_ne!(
                row.verdict,
                Verdict::Proved,
                "{name} line {line} `{}` panics natively and must never be PROVED: {}",
                row.kind,
                row.result
            );
        }
    }
}

/// The restated facts: the guard's read is tied to the length on the skip edge only, and
/// the arm's value comes under the arm's own route.
#[test]
fn the_guard_read_is_tied_to_the_length_on_the_skip_edge_only() {
    let ok = formula_at(&fixture("ok_finalize"), 43, SLICE);
    let skip = r#"Implies(Not(Var("_9", Bool)), Eq(Var("_10", Int), Var("self.2#"#;
    assert!(ok.contains(skip), "ok_finalize: `!_9 => _10 == self.buf_len`: {ok}");
    assert!(
        !ok.contains(r#"Implies(Not(Not(Var("_9", Bool))), Eq(Var("_10", Int)"#),
        "ok_finalize: `_10` is never tied on the arm's route: {ok}"
    );
    let entry = formula_at(&fixture("ok_entry_tail"), 176, SLICE);
    for fact in [
        r#"Implies(Not(Var("_2", Bool)), Eq(Var("_3", Int), Var("pad.2#"#,
        r#"Implies(Not(Not(Var("_2", Bool))), Eq(Var("pad.2#e_s2_0", Int), Int(0)))"#,
    ] {
        assert!(entry.contains(fact), "ok_entry_tail: `{fact}` must reach the row: {entry}");
    }
}

/// aterm-digest's `self.buf[self.buf_len..].fill(0)` inside the spill branch
/// (`sha256.rs:148:20`) was a deliberate decline (`c888f21ea3`, `9cc4cdc14b`: the copy of
/// the bound is made in the indexing call's own block, whose definitions the row does not
/// conjoin). Trust (2026-10-17, gate RCA precision T5): the bound is now named by the
/// place it was read from (`self.buf_len`), which no statement of that block writes
/// (`panic_calls::projected_bound_read_in_call_block`), so the row is stated: no declined
/// row, one `[slice]` row, PROVED under the guard `buf_len > 56` and `buf_len <= 64`.
/// The seal (321aaeda75) published this row PROVED; the candidate gate of 2026-10-16
/// lost it as MISSING. Never refuted: the program is correct.
#[test]
fn the_spill_branch_slice_is_stated_and_proves() {
    let rs = fixture("aterm_digest_sha256_finalize");
    assert!(
        at(&rs, 148, "slice-range-bounds-unresolved").is_empty(),
        "no declined row at line 148"
    );
    expect(&rs, 148, SLICE, 1, Verdict::Proved, "the spill branch's tail slice");
}

/// A correct `self.buf_len += 1` after the join, where `buf_len` is 0 (the arm) or the
/// guarded `<= 56` (the skip edge): `bad_write_after_guard` line 134 (a second increment)
/// and `bad_increment_after_guard` line 118 (the guard on the entry length). No overflow;
/// both rows of each are PROVED (on main all four were FAILED). Each program's real panic
/// stays its tail row.
#[test]
fn an_increment_after_the_join_is_bounded_by_the_guard() {
    for (name, line) in [("bad_write_after_guard", 134), ("bad_increment_after_guard", 118)] {
        let rs = fixture(name);
        expect(&rs, line, PRIMARY_ADD, 1, Verdict::Proved, &format!("{name}: no overflow"));
        expect(&rs, line, TWIN_ADD, 1, Verdict::Proved, &format!("{name}: the hardened twin"));
    }
}

/// The one correct row SKIP-EDGE-JOIN-1 was measured to move from Unknown to FAILED
/// (KNOWN_HAZARDS, TRUST-KI-1015-1). `bad_static_arm_call` reads a `static mut` after an
/// `if` without `else`. Each read and write of the static is a deref of its address and
/// carries the separation lane's `[unsafe:sep:deref] null check for *_N.*` row, whose goal
/// is `__trust_sep__ptr__N.* == 0` over a pointer symbol no fact mentions: correct (a
/// static's address is never null), not modelled, and so decided by the path condition
/// alone. On main the guard's read (line 432) and the reset (line 433) are already FAILED;
/// the read after the join (line 437) was Unknown only because `ay` gave up on its path
/// condition (`incomplete`). The restated facts are true and let `ay` finish, so it is
/// FAILED here (M-J: Unknown again). A refutation of an unmodelled check, never a proof.
/// The panicking subtraction on line 437 is never PROVED. When the separation lane models a
/// static's address (the dump spells it `const OpaqueConst`), the three null checks
/// should stop failing: update this pin and the hazard entry together.
#[test]
fn the_static_read_null_check_is_the_disclosed_refutation() {
    let rs = fixture("bad_static_arm_call");
    for (line, ptr) in [(432, "_4"), (433, "_7"), (437, "_12")] {
        let label = format!("[unsafe:sep:deref] null check for *{ptr}.*");
        let hits = at(&rs, line, &label);
        assert_eq!(hits.len(), 1, "line {line}: one `{label}` row");
        assert_eq!(
            hits[0].verdict,
            Verdict::Failed,
            "line {line} `{label}`: the unmodelled null check is refuted: {}",
            hits[0].result
        );
    }
    // `_13 = CheckedSub(copy _9, copy _11)`, `_11` the read of `GLEN`: the rows whose goal is
    // `_9 - _11 < 0` (line 437 also checks the constant `BLOCK_LEN - 8` and the read's
    // alignment mask `8 - 1`, both correct, and their path facts mention `_9 - _11` too).
    let goal = r#"Lt(Sub(Var("_9", Int), Var("_11", Int)), Int(0))"#;
    let tail: Vec<&Row> = rs
        .iter()
        .filter(|r| {
            r.line == 437
                && (r.kind.contains(PRIMARY_SUB) || r.kind.contains(TWIN_SUB))
                && format!("{:?}", r.vc.formula).contains(goal)
        })
        .collect();
    assert_eq!(tail.len(), 2, "the row of `_9 - _11` and its hardened twin");
    for row in tail {
        assert_ne!(row.verdict, Verdict::Proved, "`56 - GLEN` panics natively: {}", row.result);
    }
}

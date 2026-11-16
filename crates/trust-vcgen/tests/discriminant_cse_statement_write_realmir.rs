//! REAL-MIR pin: two `discriminant(*L)` reads of one canonical referent are NOT tied
//! across a statement write of the referent or a reseat of `L`, even with no
//! `Call`/`Drop`/`Opaque` between them (DISC-CSE-PRE-BARRIER-WRITE-1, 2026-10-12).
//!
//! # What was wrong
//!
//! ```text
//! pub fn assign(v: u8) -> u8 {
//!     let mut cur = Some(v);
//!     if let None = &cur { return 0; }
//!     cur = None;
//!     if let Some(_) = &cur { 0 } else { v + 255 }
//! }
//! ```
//!
//! lowers to `_3 = &_2; _4 = discriminant(*_3)` … `_2 = move _5; _6 = &_2;
//! _7 = discriminant(*_6)`. `build_discriminant_cse_facts` groups the reads by their
//! canonical referent (`_2` for both) and tied `_4 == _7` because both precede every
//! barrier — on the claim that only a `Call`/`Drop`/`Opaque` can change the referent.
//! `cur = None` is a plain statement. With the false tie the `else` arm was
//! infeasible, its `v + 255` overflow row was PROVED and kernel-certified, and the
//! advisory, default and memory-safe lanes elided the check: `assign(1)` returned 0
//! where rustc panics "attempt to add with overflow". The same tie certified a false
//! `a[i]` bounds row (`idx`) under `-Ztrust-policy=certify`.
//!
//! # The matrix
//!
//! | fixture | channel | expectation |
//! |---|---|---|
//! | `assign` | `cur = None` | `[overflow:add]` not PROVED |
//! | `start` | `self.st = St::Busy` through `&mut self` | `[overflow:add]` not PROVED |
//! | `ref_mut` | `let m = &mut e; *m = None` | `[overflow:add]` not PROVED |
//! | `param_store` | `*e = None` through a `&mut` parameter | `[overflow:add]` not PROVED |
//! | `reseat` | `r = &b` | `[overflow:add]` not PROVED |
//! | `idx` | `s = S::Busy` | `[bounds]` not PROVED |
//! | `stable` | none: `cur` is never written | `[overflow:add]` PROVED (the arm is dead) |
//! | `stable_param` | none: `cur: &Option<u8>` is a frozen parameter | `[overflow:add]` PROVED |
//! | `unwritten` | none | no `[unreach]` row REFUTED |
//! | `derived_eq` | none: `#[derive(PartialEq)]` on a data-carrying enum | no `[unreach]` row REFUTED |
//!
//! The fact-level half (no `_4 == _7` equality for each liar, the tie kept for each
//! control, and the `SetDiscriminant`/`Deinit`/`&raw const` channels on hand-built
//! MIR) is in `src/tests.rs`
//! (`real_mir_statement_writes_and_reseats_are_not_tied_before_any_barrier`,
//! `real_mir_stable_referents_keep_their_pre_barrier_tie`,
//! `a_statement_write_or_a_reseat_refuses_the_pre_barrier_tie`).
//!
//! # Fixtures
//!
//! `tests/fixtures/discr_cse_stmt_write_*_mir.json` are the compiler's own extraction
//! of the source below, captured 2026-10-12 on the wave-25 probe stage 1
//! (`scratchpad/stage1-w25probe`, stamped "after wave 24, main ≈ `c15e0f2087`"; the
//! trust-vcgen, trust-mir-extract and `rustc_mir_transform` sources are unchanged
//! from `c15e0f2087` to this fix's base `de48052933`) with
//!
//! ```text
//! rustc --edition 2021 --crate-type lib -Ztrust-verify=on -Ztrust-policy=advisory \
//!       -Ztrust-dump=mir-only:<dir> discr_cse_stmt_write.rs
//! ```
//!
//! (`derived_eq` is `<Val as PartialEq>::eq`):
//!
//! ```text
//! #[derive(Clone, Copy, PartialEq)]
//! pub enum St { Idle, Busy }
//! pub struct Machine { pub st: St, pub hits: u8 }
//! impl Machine {
//!     pub fn start(&mut self) -> u8 {
//!         if let St::Busy = &self.st { return 0; }
//!         self.st = St::Busy;
//!         match &self.st { St::Idle => 0, St::Busy => self.hits + 1 }
//!     }
//! }
//! pub fn assign(v: u8) -> u8 {
//!     let mut cur = Some(v);
//!     if let None = &cur { return 0; }
//!     cur = None;
//!     if let Some(_) = &cur { 0 } else { v + 255 }
//! }
//! pub fn ref_mut(v: u8) -> u8 {
//!     let mut e: Option<u8> = Some(v);
//!     let r1 = &e;
//!     if let None = *r1 { return 0; }
//!     let m = &mut e; *m = None;
//!     let r2 = &e;
//!     match *r2 { Some(_) => 0, None => v + 255 }
//! }
//! pub fn param_store(e: &mut Option<u8>, v: u8) -> u8 {
//!     let r1 = &*e;
//!     if let None = *r1 { return 0; }
//!     *e = None;
//!     let r2 = &*e;
//!     match *r2 { Some(_) => 0, None => v + 255 }
//! }
//! pub fn reseat(v: u8) -> u8 {
//!     let a = Some(v);
//!     let b: Option<u8> = None;
//!     let mut r = &a;
//!     if let None = *r { return 0; }
//!     r = &b;
//!     if let Some(_) = *r { 0 } else { v + 255 }
//! }
//! pub fn stable(v: u8) -> u8 {
//!     let cur = Some(v);
//!     if let None = &cur { return 0; }
//!     if let Some(_) = &cur { 0 } else { v + 255 }
//! }
//! pub fn stable_param(cur: &Option<u8>, v: u8) -> u8 {
//!     if let None = cur { return 0; }
//!     if let Some(_) = cur { 0 } else { v + 255 }
//! }
//! pub fn unwritten(v: u8) -> u8 {
//!     let cur = Some(v);
//!     if let None = &cur { return 0; }
//!     match &cur { Some(_) => 1, None => unreachable!() }
//! }
//! #[derive(PartialEq)]
//! pub enum Val { A(u8), B(u16) }
//! #[derive(Clone, Copy)]
//! pub enum S { Idle, Busy }
//! pub fn idx(a: &[u8; 4], i: usize) -> u8 {
//!     let mut s = S::Idle;
//!     if let S::Busy = &s { return 0; }
//!     s = S::Busy;
//!     match &s { S::Idle => 0, S::Busy => a[i] }
//! }
//! ```
use trust_types::{VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

/// Stack for the generation/solver thread; real extracted MIR carries deep
/// recursive `Formula` walks (the same allowance the other realmir files make).
const SOLVER_STACK_BYTES: usize = 64 * 1024 * 1024;

fn load(name: &str) -> VerifiableFunction {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/discr_cse_stmt_write_");
    let text = std::fs::read_to_string(format!("{path}{name}_mir.json"))
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

/// Which rows of a fixture a test reads.
#[derive(Clone, Copy)]
enum Rows {
    Overflow,
    Bounds,
    Unreachable,
}

/// The verdict of every selected row of `name`, each dispatched to the
/// deterministic in-process ay the bridge uses.
fn verdicts(name: &str, rows: Rows) -> Vec<String> {
    let func = load(name);
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let vcs = trust_vcgen::generate_vcs(&func);
            let router = test_router::deterministic_test_router();
            let mut out = Vec::new();
            for vc in &vcs {
                let selected = match rows {
                    Rows::Overflow => matches!(vc.kind, VcKind::ArithmeticOverflow { .. }),
                    Rows::Bounds => matches!(vc.kind, VcKind::IndexOutOfBounds),
                    Rows::Unreachable => matches!(vc.kind, VcKind::Unreachable),
                };
                if !selected {
                    continue;
                }
                let verdict = match router
                    .verify_all(std::slice::from_ref(vc))
                    .into_iter()
                    .next()
                    .expect("one verdict per VC")
                    .1
                {
                    VerificationResult::Proved { .. } => "PROVED".to_string(),
                    VerificationResult::Failed { .. } => "REFUTED".to_string(),
                    other => format!("{other:?}").chars().take(24).collect(),
                };
                out.push(verdict);
            }
            out
        })
        .expect("spawn analysis thread")
        .join()
        .expect("analysis thread must not panic")
}

fn assert_none_proved(name: &str, rows: Rows, why: &str) {
    let verdicts = verdicts(name, rows);
    assert!(
        !verdicts.is_empty(),
        "{name}: the fixture must produce the row or this test proves nothing"
    );
    assert!(
        verdicts.iter().all(|v| v != "PROVED"),
        "{name}: {why}; the row panics on a real execution, so PROVED is a false proof \
         over a discriminant tie the statement broke: {verdicts:?}"
    );
}

/// `cur = None` between `&cur` and a fresh `&cur`.
#[test]
fn a_whole_reassignment_between_the_reads_is_not_a_false_proof() {
    assert_none_proved("assign", Rows::Overflow, "`assign(1)` reaches `1 + 255`");
}

/// `self.st = St::Busy` through `&mut self` between `&self.st` and a fresh `&self.st`.
#[test]
fn a_field_store_through_mut_self_is_not_a_false_proof() {
    assert_none_proved("start", Rows::Overflow, "`start` with `hits: 255` reaches `255 + 1`");
}

/// `let m = &mut e; *m = None` between `&e` and a fresh `&e`.
#[test]
fn a_store_through_a_mut_borrow_is_not_a_false_proof() {
    assert_none_proved("ref_mut", Rows::Overflow, "`ref_mut(1)` reaches `1 + 255`");
}

/// `*e = None` through a `&mut` parameter between `&*e` and a fresh `&*e`.
#[test]
fn a_store_through_a_mut_parameter_is_not_a_false_proof() {
    assert_none_proved(
        "param_store",
        Rows::Overflow,
        "`param_store(&mut Some(1), 1)` reaches `1 + 255`",
    );
}

/// `r = &b`: both reads are `*r`, of two different referents.
#[test]
fn a_reseat_of_the_shared_reference_is_not_a_false_proof() {
    assert_none_proved("reseat", Rows::Overflow, "`reseat(1)` reaches `1 + 255`");
}

/// `s = S::Busy`, then `a[i]` in the `Busy` arm: the bounds row the certify lane
/// accepted.
#[test]
fn the_bounds_row_behind_a_reassigned_enum_is_not_a_false_proof() {
    assert_none_proved("idx", Rows::Bounds, "`idx(&[1, 2, 3, 4], 9)` reaches `a[9]`");
}

/// Precision controls: an unwritten local and a frozen `&` parameter keep the tie, so
/// the dead arm's overflow row still proves.
#[test]
fn an_unwritten_referent_still_proves_its_dead_arm() {
    for name in ["stable", "stable_param"] {
        let verdicts = verdicts(name, Rows::Overflow);
        assert_eq!(
            verdicts,
            vec!["PROVED".to_string()],
            "{name}: nothing writes the referent, so the `else` arm is dead and its \
             `v + 255` row must keep its proof"
        );
    }
}

/// Precision controls: `unreachable!()` behind an unwritten referent and a derived
/// `PartialEq::eq` keep their `[unreach]` rows unrefuted.
#[test]
fn an_unwritten_referent_and_derived_eq_keep_their_unreachable_rows() {
    for name in ["unwritten", "derived_eq"] {
        let verdicts = verdicts(name, Rows::Unreachable);
        assert!(
            !verdicts.is_empty(),
            "{name}: the fixture must produce an `[unreach]` row or this test proves nothing"
        );
        assert!(
            verdicts.iter().all(|v| v != "REFUTED"),
            "{name}: the dead arm is unreachable on every execution; a refutation is a \
             counterexample over untied re-reads of an unwritten referent: {verdicts:?}"
        );
    }
}

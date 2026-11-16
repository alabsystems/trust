//! Trust (2026-10-15, STRING-AS-STR): `_s = <String as Deref>::deref(&s)` (and
//! `deref_mut`) is the `String`'s own bytes, so `slice_len(_s) == coll_len(s)` at the
//! call's return target, the `String` twin of VEC-AS-SLICE's view tie. Pinned on REAL
//! extracted MIR.
//!
//! The str-length rewrite (`rewrite_str_len_calls`) lowers `t.len()` on a `&str` to
//! `PtrMetadata(t)`, so the `s.len() == 0` guard said nothing about `t`'s length and
//! `std_string_view` below was refuted (`_4__slice_len#s2_t = 0, s = 1`) on the stage 1
//! of the 2026-10-14 merge (`tests/ui/trust/deref_len_tie_requires_std_self.rs`).
//!
//! The MIR under `tests/fixtures/string_view_len/` is `-Ztrust-dump=mir:<dir>` output
//! from that stage 1 (`-Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//! -Ztrust-policy=advisory`), re-serialized without whitespace, of `body.rs`:
//!
//! ```text
//! pub fn std_string_view(s: &String) -> usize {
//!     if s.len() == 0 { return 0; }
//!     let t: &str = s;
//!     t.len() - 1
//! }
//! pub fn string_view_after_clear(s: &mut String) -> usize {
//!     if s.len() == 0 { return 0; }
//!     s.clear();
//!     let t: &str = s;
//!     t.len() - 1
//! }
//! ```
//!
//! The first is correct and must prove. The second panics for any non-empty `s`
//! (`clear` empties it before the view is taken), so its `- 1` row must not. A view
//! taken through a `&mut String` parameter is out of scope: on the same stage 1 neither
//! its `s.len()` nor the view is tied to the `String`'s length (the row is refuted with
//! `s* = 0` beside `len = 1`), and the arm here does not change that; it stays unproved.

use trust_types::{VcKind, VerificationResult};

use super::*;

const MIR_VIEW: &str = include_str!("../tests/fixtures/string_view_len/std_string_view.json");
const MIR_AFTER_CLEAR: &str =
    include_str!("../tests/fixtures/string_view_len/string_view_after_clear.json");

/// A `Ty::Adt` name the producer gives an impersonating `alloc`'s `String`
/// (`sysroot_authenticated_def_path_str`).
const STAMPED_STRING: &str = "__trust_crate@1973d11b2baa21fa::alloc::string::String";

fn parse(mir: &str) -> VerifiableFunction {
    serde_json::from_str(mir).expect("the captured MIR fixture must deserialize")
}

/// The `- 1` overflow rows: the in-process ay's verdict on each routed row, and how many
/// the interval lane discharged without a solver.
fn sub_verdicts(func: VerifiableFunction) -> (Vec<VerificationResult>, usize) {
    std::thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(move || {
            let is_sub =
                |kind: &VcKind| matches!(kind, VcKind::ArithmeticOverflow { op: BinOp::Sub, .. });
            let (solver, discharged) = crate::generate_vcs_with_discharge(&func);
            let routed: Vec<_> = solver.iter().filter(|vc| is_sub(&vc.kind)).cloned().collect();
            let router = crate::test_router::deterministic_test_router();
            (
                router.verify_all(&routed).into_iter().map(|(_, r)| r).collect(),
                discharged.iter().filter(|(vc, _)| is_sub(&vc.kind)).count(),
            )
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

fn proved((routed, discharged): &(Vec<VerificationResult>, usize)) -> bool {
    discharged + routed.len() >= 1
        && routed.iter().all(|r| matches!(r, VerificationResult::Proved { .. }))
}

/// The local the `String` deref call writes, and its receiver.
fn deref_call(func: &VerifiableFunction) -> (usize, usize) {
    let calls: Vec<(usize, usize)> = func
        .body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::Call { func: f, args, dest, .. }
                if f.contains("alloc::string::String as") =>
            {
                match args.first() {
                    Some(Operand::Copy(p) | Operand::Move(p)) => Some((dest.local, p.local)),
                    _ => None,
                }
            }
            _ => None,
        })
        .collect();
    assert_eq!(calls.len(), 1, "one `String` deref call: {calls:?}");
    calls[0]
}

/// The fixtures carry std's own `String` view, as the extractor rendered it.
#[test]
fn the_fixtures_carry_std_string_deref() {
    for (mir, callee) in [
        (MIR_VIEW, "<alloc::string::String as core::ops::deref::Deref>::deref"),
        (MIR_AFTER_CLEAR, "<alloc::string::String as core::ops::deref::Deref>::deref"),
    ] {
        assert!(mir.contains(&format!("\"func\":\"{callee}\"")), "{callee}");
    }
}

/// The equation is minted at the deref call's return target, on the view's length.
#[test]
fn std_string_deref_ties_the_view_length_to_the_string_length() {
    {
        let func = parse(MIR_VIEW);
        let (view, _) = deref_call(&func);
        let view_len = crate::slice_len_formula(
            &func,
            &Operand::Copy(trust_types::Place { local: view, projections: vec![] }),
        )
        .expect("a `&str` view has a slice length");
        let facts = slice_last_some_nonempty_definitions(&func);
        assert!(
            facts.values().flatten().any(|fact| matches!(fact,
                Formula::Eq(lhs, _) if **lhs == view_len)),
            "{}: no `slice_len(view) == coll_len(s)` fact in {facts:?}",
            func.name
        );
    }
}

/// End to end through vcgen and the real in-process ay: the correct function now proves
/// its `- 1`, and the `clear` twin, whose length changes between the guard and the view,
/// does not (the base's length is not stable, so no equation is minted).
#[test]
fn std_string_view_rows_prove_and_a_cleared_string_does_not() {
    let rows = sub_verdicts(parse(MIR_VIEW));
    assert!(proved(&rows), "std_string_view: the view has the string's length: {rows:?}");
    let rows = sub_verdicts(parse(MIR_AFTER_CLEAR));
    assert!(!proved(&rows), "string_view_after_clear panics on a non-empty input: {rows:?}");
}

/// The RECEIVER conjunct is load-bearing on its own: with the receiver's pointee retyped
/// as an impersonating `alloc`'s stamped `String` (the callee text stays std's own
/// `Deref`, as a `#![no_std]` graph can spell it), no equation is minted and the row
/// stays unproved.
#[test]
fn a_std_string_view_spelling_on_a_forged_receiver_has_no_length_tie() {
    let mut func = parse(MIR_VIEW);
    let (_, receiver) = deref_call(&func);
    let Ty::Ref { inner, .. } = &mut func.body.locals[receiver].ty else {
        panic!("`_{receiver}` is a reference in the fixture")
    };
    assert!(
        matches!(inner.as_ref(), Ty::Adt { name, .. } if name == "alloc::string::String"),
        "`_{receiver}` points at std's `String`"
    );
    **inner = Ty::adt(STAMPED_STRING, vec![]);
    let rows = sub_verdicts(func);
    assert!(!proved(&rows), "a forged receiver's view has no std length: {rows:?}");
}

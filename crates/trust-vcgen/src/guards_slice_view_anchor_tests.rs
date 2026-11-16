//! Trust (2026-10-04, SLICE-VIEW-ANCHOR-1): std `Vec`'s slice view
//! (`callee_is_std_vec_slice_view`) is std's own `Deref`/`DerefMut` impl by the exact
//! top-level split, and the two call sites that hold the receiver also require it to
//! be a std `Vec` by MIR type. Pinned on REAL extracted MIR.
//!
//! The view recognizer feeds two length facts: a `&mut v` consumed by `Vec`'s own
//! `deref_mut`/`as_mut_slice` is length-benign (`local_mut_borrows_may_resize_one`),
//! and `_s = <Vec<T> as Deref>::deref(&v)` gets `slice_len(_s) == coll_len(v)`
//! (`slice_last_some_nonempty_definitions`; `vec_region` mints the same equation). Its
//! `deref` arm searched the whole callee with `contains(" as core::ops::deref::
//! DerefMut>::deref_mut")` and five sibling needles. A USER trait method named
//! `deref_mut` on std's `Vec<u32>`, whose trait takes a fn ITEM as its generic
//! argument, carries the needle inside that argument. Its body truncated `v`, the
//! `&mut v` still counted as benign, and `if v.len() == 0 { return 0; } <call>;
//! v.len() - 1` read `overflow:sub` Certified with the check elided (`usize::MAX`
//! returned). The `deref` twin (`View<F>::deref` returning `&[]`) got the view-length
//! equation and the same wrong value. Measured on the stage 1 of `fc62d8ba05`
//! (`integ/wave12`, whose compiler and trust-vcgen equal `ee3f51541d`'s) under the
//! advisory policy, and by the wave-12 review on the stage 1 of `ee3f51541d` under
//! default, strict, certify, memory-safe and advisory. It predates wave 12.
//!
//! The MIR under `tests/fixtures/slice_view_anchor/` is `-Ztrust-dump=mir:<dir>` output
//! from that stage 1 (`-Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//! -Ztrust-policy=advisory`), re-serialized without whitespace, of `body.rs`:
//!
//! ```text
//! pub struct X(Vec<u32>);
//! impl Deref for X { type Target = Vec<u32>; fn deref(&self) -> &Vec<u32> { &self.0 } }
//! impl DerefMut for X { fn deref_mut(&mut self) -> &mut Vec<u32> { &mut self.0 } }
//! pub trait Shrink<F> { fn deref_mut(&mut self, f: F); }
//! impl<F> Shrink<F> for Vec<u32> { fn deref_mut(&mut self, _f: F) { self.truncate(0); } }
//! pub fn user_len(mut v: Vec<u32>) -> usize {
//!     if v.len() == 0 { return 0; }
//!     Shrink::deref_mut(&mut v, <X as DerefMut>::deref_mut);
//!     v.len() - 1
//! }
//! pub trait View<F> { fn deref(&self, f: F) -> &[u32]; }
//! impl<F> View<F> for Vec<u32> { fn deref(&self, _f: F) -> &[u32] { &[] } }
//! pub fn view_len(v: Vec<u32>) -> usize {
//!     if v.len() == 0 { return 0; }
//!     let s = View::deref(&v, <X as DerefMut>::deref_mut);
//!     s.len() - 1
//! }
//! pub fn std_sort_len(mut v: Vec<u32>) -> usize {
//!     if v.len() == 0 { return 0; }
//!     v.sort();
//!     v.len() - 1
//! }
//! pub fn std_view_len(v: Vec<u32>) -> usize {
//!     if v.len() == 0 { return 0; }
//!     let s: &[u32] = &v;
//!     s.len() - 1
//! }
//! ```
//!
//! On that compiler all four functions printed `elided 1 kernel-certified overflow
//! checks`. The two std controls must keep their proof.

use trust_types::{VcKind, VerificationResult};

use super::*;

const MIR_USER_LEN: &str = include_str!("../tests/fixtures/slice_view_anchor/user_len.json");
const MIR_VIEW_LEN: &str = include_str!("../tests/fixtures/slice_view_anchor/view_len.json");
const MIR_STD_SORT_LEN: &str =
    include_str!("../tests/fixtures/slice_view_anchor/std_sort_len.json");
const MIR_STD_VIEW_LEN: &str =
    include_str!("../tests/fixtures/slice_view_anchor/std_view_len.json");

/// The two measured callees, exactly as the extractor rendered them.
const SHRINK_DEREF_MUT: &str = "<alloc::vec::Vec<u32> as body::Shrink<for<'_> fn(&'_ mut \
     body::X) -> &'_ mut <body::X as core::ops::deref::Deref>::Target {<body::X as \
     core::ops::deref::DerefMut>::deref_mut}>>::deref_mut";
const VIEW_DEREF: &str = "<alloc::vec::Vec<u32> as body::View<for<'_> fn(&'_ mut body::X) -> \
     &'_ mut <body::X as core::ops::deref::Deref>::Target {<body::X as \
     core::ops::deref::DerefMut>::deref_mut}>>::deref";
const STD_VEC_DEREF_MUT: &str = "<alloc::vec::Vec<u32> as core::ops::deref::DerefMut>::deref_mut";
const STD_VEC_DEREF: &str = "<alloc::vec::Vec<u32> as core::ops::deref::Deref>::deref";

/// A `Ty::Adt` name the producer gives an impersonating `alloc`'s `Vec`
/// (`sysroot_authenticated_def_path_str`).
const STAMPED_VEC: &str = "__trust_crate@1973d11b2baa21fa::alloc::vec::Vec<u32>";

fn parse(mir: &str) -> VerifiableFunction {
    serde_json::from_str(mir).expect("the captured MIR fixture must deserialize")
}

/// The callee of the one call whose receiver is `receiver`, checking the fixture.
fn callee_on(func: &VerifiableFunction, receiver: usize) -> String {
    let callees: Vec<&str> = func
        .body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::Call { func: f, args, .. }
                if matches!(args.first(), Some(Operand::Copy(p) | Operand::Move(p))
                    if p.local == receiver && p.projections.is_empty()) =>
            {
                Some(f.as_str())
            }
            _ => None,
        })
        .collect();
    assert_eq!(callees.len(), 1, "one call on `_{receiver}`: {callees:?}");
    callees[0].to_string()
}

/// Retype the pointee of the reference local `local` as the stamped impersonator ADT.
fn retype_pointee_as_stamped_vec(func: &mut VerifiableFunction, local: usize) {
    let Ty::Ref { inner, .. } = &mut func.body.locals[local].ty else {
        panic!("`_{local}` is a reference in the fixture")
    };
    assert!(matches!(inner.as_ref(), Ty::Seq { .. }), "`_{local}` points at std's `Vec`");
    **inner = Ty::adt(STAMPED_VEC, vec![]);
}

/// The `- 1` row of a fixture, as the production split leaves it.
struct SubRows {
    /// The in-process ay's verdict on each `Sub` overflow row handed to a solver.
    routed: Vec<VerificationResult>,
    /// `Sub` overflow rows the interval lane discharged without a solver.
    discharged: usize,
    /// Rows `havoc_decline` reclassified because their verdict rests on an
    /// unconstrained call result (`UnsupportedMir` `UnmodeledCalleeReturn`, Unknown).
    declined: usize,
}

impl SubRows {
    /// Not proved by any lane, and the row exists (as `Sub` or as the decline).
    fn not_proved(&self) -> bool {
        self.discharged == 0
            && self.routed.iter().all(|r| !matches!(r, VerificationResult::Proved { .. }))
            && self.routed.len() + self.declined >= 1
    }

    /// Proved, by the interval lane or by ay, and never declined.
    fn proved(&self) -> bool {
        self.declined == 0
            && self.discharged + self.routed.len() >= 1
            && self.routed.iter().all(|r| matches!(r, VerificationResult::Proved { .. }))
    }
}

/// The `- 1` row's verdicts from the real in-process ay, on a big stack (VC
/// generation and the solver search overflow libtest's default stack).
fn sub_rows(func: VerifiableFunction) -> SubRows {
    std::thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(move || {
            let is_sub =
                |kind: &VcKind| matches!(kind, VcKind::ArithmeticOverflow { op: BinOp::Sub, .. });
            let is_decline = |kind: &VcKind| {
                let VcKind::UnsupportedMir { kind, .. } = kind else { return false };
                kind == "UnmodeledCalleeReturn"
            };
            let (solver, discharged) = crate::generate_vcs_with_discharge(&func);
            let routed: Vec<_> = solver.iter().filter(|vc| is_sub(&vc.kind)).cloned().collect();
            let router = crate::test_router::deterministic_test_router();
            SubRows {
                routed: router.verify_all(&routed).into_iter().map(|(_, r)| r).collect(),
                discharged: discharged.iter().filter(|(vc, _)| is_sub(&vc.kind)).count(),
                declined: solver.iter().filter(|vc| is_decline(&vc.kind)).count()
                    + discharged.iter().filter(|(vc, _)| is_decline(&vc.kind)).count(),
            }
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

impl std::fmt::Debug for SubRows {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "routed {:?}, discharged {}, declined {}",
            self.routed, self.discharged, self.declined
        )
    }
}

/// The fixtures carry exactly the measured spellings.
#[test]
fn the_fixtures_carry_the_measured_callees() {
    assert_eq!(callee_on(&parse(MIR_USER_LEN), 6), SHRINK_DEREF_MUT);
    assert_eq!(callee_on(&parse(MIR_VIEW_LEN), 6), VIEW_DEREF);
    assert_eq!(callee_on(&parse(MIR_STD_SORT_LEN), 7), STD_VEC_DEREF_MUT);
    assert_eq!(callee_on(&parse(MIR_STD_VIEW_LEN), 6), STD_VEC_DEREF);
}

/// THE LIE, spelling half: both user trait methods carry std's `DerefMut` needle inside
/// a fn-item trait argument, and the old `contains` test admitted both.
#[test]
fn a_user_trait_method_carrying_the_deref_needle_is_not_a_std_vec_view() {
    for callee in [SHRINK_DEREF_MUT, VIEW_DEREF] {
        assert!(!callee_is_std_vec_slice_view(callee), "{callee}");
    }
    let refused = [
        // The other needles, each inside a user trait's argument.
        "<alloc::vec::Vec<u32> as m::Tr<fn() {<m::X as core::ops::Deref>::deref}>>::deref",
        "<alloc::vec::Vec<u32> as m::Tr<fn() {<m::X as \
         std::ops::DerefMut>::deref_mut}>>::deref_mut",
        "<std::vec::Vec<u32> as m::Tr<fn() {<m::X as \
         std::ops::Deref>::deref}>>::deref",
        // A user trait method on std's `Vec` that only shares the name.
        "<alloc::vec::Vec<u32> as m::Tr>::deref",
        // The wrong trait for the method, a suffix, a tagged call, another self type.
        "<alloc::vec::Vec<u32> as core::ops::deref::Deref>::deref_mut",
        "<alloc::vec::Vec<u32> as core::ops::deref::Deref>::deref::\
         <__trust_args@00000000000000010000000000000023>",
        "<alloc::string::String as core::ops::deref::Deref>::deref",
        "<m::Wrap as core::ops::deref::Deref>::deref",
        "<__trust_crate@1973d11b2baa21fa::alloc::vec::Vec<u32> as core::ops::deref::Deref>::deref",
        "core::ops::deref::Deref::deref",
        // An inherent-looking spelling that is a trait method.
        "<alloc::vec::Vec<u32> as m::Tr>::as_slice",
    ];
    for callee in refused {
        assert!(!callee_is_std_vec_slice_view(callee), "{callee}");
    }
}

/// CONTROL: std `Vec`'s own views in every spelling the old test accepted.
#[test]
fn std_vec_own_views_are_still_std_vec_views() {
    let accepted = [
        STD_VEC_DEREF,
        STD_VEC_DEREF_MUT,
        "<alloc::vec::Vec<u8> as core::ops::Deref>::deref",
        "<alloc::vec::Vec<u8> as core::ops::DerefMut>::deref_mut",
        "<std::vec::Vec<u8> as std::ops::Deref>::deref",
        "<std::vec::Vec<u8> as std::ops::DerefMut>::deref_mut",
        "<alloc::vec::Vec<u32, alloc::alloc::Global> as core::ops::deref::Deref>::deref",
        "<alloc::vec::Vec<for<'_> fn(&'_ u32) -> u32 {m::f}> as core::ops::deref::Deref>::deref",
        "alloc::vec::Vec::<u32>::as_slice",
        "alloc::vec::Vec::<u32>::as_mut_slice",
        "<alloc::vec::Vec<u32>>::as_slice",
    ];
    for callee in accepted {
        assert!(callee_is_std_vec_slice_view(callee), "{callee}");
    }
}

/// THE LIE, length-benign half: the `&mut v` handed to the user `Shrink::deref_mut`
/// may resize `v`; the one handed to std's own `DerefMut` (`v.sort()`) does not.
#[test]
fn a_mut_borrow_into_a_user_trait_deref_mut_may_resize_the_vec() {
    assert!(local_mut_borrows_may_resize(&parse(MIR_USER_LEN), 1));
    assert!(!local_mut_borrows_may_resize(&parse(MIR_STD_SORT_LEN), 1));
}

/// The RECEIVER conjunct is load-bearing on its own: `v.sort()`'s MIR with the
/// `&mut v` temp's pointee retyped as an impersonating `alloc`'s stamped `Vec` (the
/// callee text stays std's own `DerefMut`, as a `#![no_std]` graph can spell it).
#[test]
fn a_std_view_spelling_on_a_forged_receiver_is_not_length_benign() {
    let mut f = parse(MIR_STD_SORT_LEN);
    retype_pointee_as_stamped_vec(&mut f, 7);
    assert!(local_mut_borrows_may_resize(&f, 1));
}

/// End to end through vcgen and the real in-process ay: the two user rows are not
/// proved (each was Proved before: ay UNSAT through the false tie), and the two std
/// controls still are. Without the tie the user row is either a `Sub` row ay does not
/// prove or `havoc_decline`'s Unknown, since the second length is an unconstrained call
/// result.
#[test]
fn user_trait_view_rows_are_not_proved_and_std_view_rows_are() {
    for (name, mir) in [("user_len", MIR_USER_LEN), ("view_len", MIR_VIEW_LEN)] {
        let rows = sub_rows(parse(mir));
        assert!(rows.not_proved(), "{name}: the user method may change the length: {rows:?}");
    }
    for (name, mir) in [("std_sort_len", MIR_STD_SORT_LEN), ("std_view_len", MIR_STD_VIEW_LEN)] {
        let rows = sub_rows(parse(mir));
        assert!(rows.proved(), "{name}: std's own view keeps the length: {rows:?}");
    }
}

/// The view-length equation's receiver conjunct: `std_view_len` with the `&v` temp
/// retyped as the stamped impersonator. Its base `v` is still `Ty::Seq`, which is
/// what `place_is_std_vec` asked; the receiver itself now has to be std's `Vec` too.
#[test]
fn the_view_length_equation_needs_a_std_vec_receiver() {
    let mut f = parse(MIR_STD_VIEW_LEN);
    retype_pointee_as_stamped_vec(&mut f, 6);
    let rows = sub_rows(f);
    assert!(rows.not_proved(), "a forged receiver's view has no std length: {rows:?}");
}

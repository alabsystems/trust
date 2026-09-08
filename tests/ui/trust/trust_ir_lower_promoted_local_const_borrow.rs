//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// wave-PC (wave-full-0901 coverage tier): `&C` where `C` is a LOCAL scalar
// const, in an ESCAPING position — `const T1: &'static usize = &C` and
// `fn f() -> &'static i32 { &C }` alike (the largest single population
// inside the 43-sole `Return(borrow ptr escapes tail)` class). The
// wave-CB stack snapshot is faithful to pre-promotion MIR but its Alloca
// address can never be returned; rustc promotes the referent to a
// `'static` alloc after `mir_built`. The producer now mirrors that with a
// module GLOBAL whose `Constant::PhantomData` initializer the finalize
// seam patches through the SAME const-eval path as an ordinary deferred
// read (`PendingConst::promoted_global` — the wave-SD machinery, const
// flavor; ledger-tripwired so an unpatched placeholder can never splice
// silently). A pending-const body is NotRun and unflippable by the
// existing gates, so the stack-vs-global spelling is unobservable to the
// comparator; the delta is the `global_ptrs` return admission. The lane
// intercept sits OUTSIDE `is_const_borrow_arg` — that recognizer does not
// peel the `Deref{Borrow{..}}` reborrow adjustment rustc inserts at
// exactly the escaping positions (measured while landing this).
const C: usize = 1;
const NEG: i32 = -7;

// The const-init escaping shape (issue-17718's T1/T3): must LOWER.
pub const T1: &'static usize = &C;
pub static T3: &'static usize = &C;

// The fn-return escaping shape: must LOWER.
pub fn ref_const() -> &'static usize {
    &C
}

pub fn ref_neg() -> &'static i32 {
    &NEG
}

// wave-PC2: COMPOSITE consts join the lane — `&AA` where AA is an array
// const is the largest residual inside the same escape class. The seam's
// B7 composite leg decodes it against the GLOBAL's declared type + the
// body's registered tables. FOURTH trap, measured: that leg yields
// `Constant::Aggregate` for a tuple/struct target but `Constant::Array`
// for a first-class array — accepting only the former made every array
// const a `PendingPromoted(shape disagreement)` AND regressed bodies that
// used to lower by another route (this lane intercepts before them), with
// the seam's `bump_unsupported` showing up as an unsupported body carrying
// an EMPTY detail row.
const AA: [isize; 3] = [1, 2, 3];

pub const AB: &'static [isize; 3] = &AA;

pub fn ref_array() -> &'static [isize; 3] {
    &AA
}

// Negative control: an array of REFERENCE leaves has no constant image, so
// the lane screens it out AT MINT TIME (`seed_constant_ty` is the witness)
// and it falls through to its pre-existing route instead of minting a
// global the seam would then refuse. That screen is load-bearing in the
// other direction too: this lane intercepts BEFORE the older routes, so a
// shape it claims and cannot finish is a regression, not just a miss —
// measured on `const B: u8 = (&A)[0]`, which went unsupported with an
// EMPTY detail row (the coverage-side signature of a seam bump).
// `&[(&str, &str); 5]` is the measured field shape
// (consts/promoted_regression.rs BAR).
const REFS: [&'static str; 2] = ["a", "b"];

pub const REFS_BORROW: &'static [&'static str; 2] = &REFS;

fn main() {
    assert_eq!(*T1, 1);
    assert_eq!(*ref_const(), 1);
    assert_eq!(*ref_neg(), -7);
    assert_eq!(AB[0], 1);
    assert_eq!(ref_array()[2], 3);
    assert_eq!(REFS_BORROW[0], "a");
}

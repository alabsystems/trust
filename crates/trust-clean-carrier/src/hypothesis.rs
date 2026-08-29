// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **The narrow lift of the dependent-`Pi` refusal: a hypothesis argument.**
//!
//! # The refusal this lifts, and why it was there
//!
//! [`crate::carrier_signature_for`] refuses a genuinely dependent `Pi` with
//! [`CarrierRefused::DependentFunctionType`], and that refusal is right for the
//! case it was written for: `(a : UInt64) -> Vec a` flattened to `UInt64 ->
//! Vec` is a Rust signature that says something strictly weaker than the Clean
//! type. The dependency has nowhere to go, so the type does not carry.
//!
//! A **hypothesis** binder is the one dependent shape where the dependency
//! *does* have somewhere to go:
//!
//! ```text
//! def safe_rem (a b : UInt64) (h : b ≠ 0) : UInt64 := …
//! ```
//!
//! `h`'s domain mentions `b`, so the whole telescope is a dependent `Pi` and is
//! refused today — `fa788aab89` measured exactly that (*"a hypothesis-carrying
//! declaration cannot even be minted today"*). But `h` is a **proof**, and a
//! proof is erased on the Rust side. The Rust signature is `fn safe_rem(a: u64,
//! b: u64) -> u64`, arity 2, and the dependency becomes a **caller-side
//! precondition** `b != 0` — an ordinary Rust obligation, discharged at every
//! call site, never a `Faithful` token.
//!
//! # The five conditions, all required
//!
//! Erasing a binder is exactly the move the original refusal exists to
//! prevent, so the lift is conditioned rather than general:
//!
//! 1. **The domain is a RECOGNISED proposition.** Not "looks like a `Prop`" —
//!    it must be an atom this module can restate as a
//!    [`CleanOriginPrecondition`]. A hypothesis whose statement cannot be
//!    carried is refused ([`CarrierRefused::UnrecognisedHypothesis`]), because
//!    erasing it would drop a requirement the declaration makes and hand the
//!    caller a function with a weaker contract than the one the kernel checked.
//! 2. **Its operands are carried VALUE arguments or in-range numerals.** A
//!    hypothesis that mentions another hypothesis (a proof term) is refused:
//!    proofs are erased, so there would be nothing at the call site to
//!    substitute.
//! 3. **Nothing downstream depends on the proof.** The remainder of the type
//!    after a hypothesis binder must be closed with respect to it. If the
//!    result type mentions `h`, the value being produced depends on *which*
//!    proof was supplied and there is no Rust type for it — that is the
//!    original refusal, still in force.
//! 4. **Value positions stay non-dependent.** A value binder's domain, and the
//!    result, may not mention any earlier binder — precisely the check
//!    `carrier_signature_for` already makes. The lift widens *where a
//!    dependency may appear* (hypothesis domains only), never *whether values
//!    may be dependent*.
//! 5. **The value positions still carry totally.** Unchanged: every argument
//!    and the result go through [`crate::carrier_for`], one call per position.
//!
//! # Direction of failure
//!
//! Every path out of this module that is not a recognised hypothesis is a
//! refusal, and a refusal costs a mint, never a wrong binary. The lift can
//! therefore only ever make MORE declarations callable — each of them carrying
//! strictly MORE caller obligations than a non-hypothesis declaration does.

use clean_kernel::{Expr, ExprKind, Name};
use trust_types::clean_origin_precondition::{
    CleanOriginPrecondition, PreconditionOperand,
};

use crate::{CleanType, recognize, strip_mdata};

/// A recognised hypothesis binder: a proof argument that is **erased** in the
/// Rust signature and reappears as a caller-side precondition.
///
/// Constructible only by this module's recogniser (the field is private and
/// there is no public constructor), so a `Hypothesis` in hand is evidence that
/// the five conditions in the module docs were checked — the same sealing
/// discipline `Carrier` uses. The obligation it carries is public data
/// (`trust_types::clean_origin_precondition` explains why that is safe: a
/// precondition is a bill, not evidence).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Hypothesis {
    binder_index: usize,
    precondition: CleanOriginPrecondition,
}

impl Hypothesis {
    /// Which binder of the **full** telescope this was, 0-based — counting
    /// value binders and hypothesis binders together.
    ///
    /// Deliberately not the carried-argument index: a hypothesis has no
    /// carried-argument index, and inventing one would make an erased binder
    /// look like a parameter.
    #[must_use]
    pub fn binder_index(&self) -> usize {
        self.binder_index
    }

    /// The caller obligation this hypothesis becomes.
    #[must_use]
    pub fn precondition(&self) -> &CleanOriginPrecondition {
        &self.precondition
    }
}

/// Whether `domain` is *shaped like* a proposition.
///
/// Used ONLY to choose which refusal to report — never to admit anything. A
/// domain that answers `true` here and is not recognised by
/// [`recognise_hypothesis`] gets [`crate::CarrierRefused::UnrecognisedHypothesis`]
/// (v7/D3: name the supported forms and the options); one that answers `false`
/// keeps the ordinary positional carrier refusal it has always had.
///
/// The list is the set of heads Clean's `Prop`-formers use. It is deliberately
/// wider than what [`recognise_hypothesis`] accepts, because its job is to make
/// the DIAGNOSTIC right, and telling a user who wrote `(h : a < b)` that
/// `UInt64 -> …` "has no modeled Rust carrier for `LT.lt`" points at the wrong
/// problem.
pub(crate) fn is_proposition_shaped(domain: &Expr) -> bool {
    let (head, _) = uncurry(domain);
    let ExprKind::Const(name, _) = head.kind() else { return false };
    matches!(
        name.to_string().as_str(),
        "Ne" | "Eq"
            | "Not"
            | "Iff"
            | "And"
            | "Or"
            | "LT.lt"
            | "LE.le"
            | "GT.gt"
            | "GE.ge"
            | "Decidable"
            | "False"
            | "True"
    )
}

/// Read a hypothesis binder's domain as a caller-side precondition.
///
/// `binder_depth` is how many binders are open OUTSIDE `domain` (so a `BVar(i)`
/// inside it names telescope binder `binder_depth - 1 - i`).
/// `carried_index_of_binder[b]` is the carried-argument index of telescope
/// binder `b`, or `None` when that binder is itself an erased hypothesis.
///
/// `None` means "not an atom this module can restate", which the caller turns
/// into a refusal. It never means "vacuously fine".
pub(crate) fn recognise_hypothesis(
    domain: &Expr,
    binder_depth: usize,
    carried_index_of_binder: &[Option<usize>],
) -> Option<CleanOriginPrecondition> {
    let (head, args) = uncurry(domain);
    let ExprKind::Const(head_name, _) = head.kind() else { return None };

    // Two spellings of the same atom. `≠` is notation for `Ne`, and `Ne a b` is
    // *defined* as `¬ (a = b)`, so an elaborator may hand us either — reading
    // only one would make the lift depend on which the user's Clean happened to
    // produce, which is exactly the kind of spelling sensitivity `emit.rs`'s
    // `numeral_leaf` already had to grow a second arm for.
    let (ty, lhs, rhs) = match head_name.to_string().as_str() {
        // `@Ne α a b`
        "Ne" => match args[..] {
            [ty, lhs, rhs] => (ty, lhs, rhs),
            _ => return None,
        },
        // `Not (@Eq α a b)`
        "Not" => {
            let [inner] = args[..] else { return None };
            let (inner_head, inner_args) = uncurry(inner);
            let ExprKind::Const(inner_name, _) = inner_head.kind() else { return None };
            if inner_name.to_string() != "Eq" {
                return None;
            }
            match inner_args[..] {
                [ty, lhs, rhs] => (ty, lhs, rhs),
                _ => return None,
            }
        }
        _ => return None,
    };

    // The proposition must be stated at a FIXED-WIDTH unsigned Clean type. Two
    // reasons, both load-bearing: a numeral operand can only be range-checked
    // against a width, and the consuming renderer needs a width to state the
    // obligation at. `Nat`/`Int` (unbounded), `Bool`, `BitVec` and every
    // unmodeled type are refused here rather than guessed at.
    let width = match recognize(ty)? {
        CleanType::UInt(w) if matches!(w, 8 | 16 | 32 | 64) => w,
        _ => return None,
    };
    let carrier_name = format!("UInt{width}");

    let left = read_operand(lhs, &carrier_name, width, binder_depth, carried_index_of_binder)?;
    let right = read_operand(rhs, &carrier_name, width, binder_depth, carried_index_of_binder)?;

    let render = |o: PreconditionOperand| match o {
        PreconditionOperand::Argument(i) => format!("arg{i}"),
        PreconditionOperand::Literal(v) => v.to_string(),
    };
    Some(CleanOriginPrecondition::not_equal(
        left,
        right,
        width,
        format!("{} ≠ {} : {carrier_name}", render(left), render(right)),
    ))
}

/// Build a [`Hypothesis`] from a recognised atom. Private constructor, in this
/// module only.
pub(crate) fn seal(binder_index: usize, precondition: CleanOriginPrecondition) -> Hypothesis {
    Hypothesis { binder_index, precondition }
}

/// One side of a hypothesis atom: a carried value argument, or a numeral.
fn read_operand(
    operand: &Expr,
    carrier_name: &str,
    width: u32,
    binder_depth: usize,
    carried_index_of_binder: &[Option<usize>],
) -> Option<PreconditionOperand> {
    let operand = strip_mdata(operand);

    if let &ExprKind::BVar(index) = operand.kind() {
        let index = usize::try_from(index).ok()?;
        // Loose beyond the open telescope: the kernel would not have accepted
        // it, and we do not guess what it names.
        if index >= binder_depth {
            return None;
        }
        let binder = binder_depth - 1 - index;
        // `None` = the referenced binder is itself an erased hypothesis. A
        // proof term has no call-site value to substitute, so this is refused
        // rather than dropped.
        let carried = (*carried_index_of_binder.get(binder)?)?;
        return Some(PreconditionOperand::Argument(carried));
    }

    let value = numeral_leaf(operand, carrier_name)?;
    // Re-checked against the width HERE, not trusted from the spelling: an
    // out-of-range numeral in a hypothesis is a statement about a value the
    // carrier cannot hold, and admitting it would state the obligation at a
    // different number than the Clean text does.
    if width < 128 && value >= (1u128 << width) {
        return None;
    }
    Some(PreconditionOperand::Literal(value))
}

/// Read a numeral in either measured spelling — carrier `{C}.ofNat n`, or
/// surface `OfNat.ofNat {C} n (instOfNat{C} n)` with the two literals equal.
///
/// This mirrors `trust_clean_origin::emit`'s `numeral_leaf`, which measured
/// both spellings against the real island elaborator. It is re-stated rather
/// than shared because that function is on the other side of a crate boundary
/// this crate must not cross (`trust-clean-carrier` has exactly three
/// dependencies and `trust-clean-origin` depends on IT, not the reverse); the
/// unit tests below pin both spellings so the two cannot silently diverge on
/// the arm that matters.
fn numeral_leaf(operand: &Expr, carrier_name: &str) -> Option<u128> {
    let (head, args) = uncurry(operand);
    let ExprKind::Const(head_name, _) = head.kind() else { return None };

    if *head_name == Name::from_string(&format!("{carrier_name}.ofNat")) {
        let [literal] = args[..] else { return None };
        return nat_u128(literal);
    }

    if *head_name == Name::from_string("OfNat.ofNat") {
        let [ty, literal, instance] = args[..] else { return None };
        if !matches!(strip_mdata(ty).kind(),
            ExprKind::Const(n, _) if *n == Name::from_string(carrier_name))
        {
            return None;
        }
        let value = nat_u128(literal)?;
        let (instance_head, instance_args) = uncurry(instance);
        if !matches!(instance_head.kind(),
            ExprKind::Const(n, _) if *n == Name::from_string(&format!("instOfNat{carrier_name}")))
        {
            return None;
        }
        // The instance's own literal must AGREE with the value's. They are two
        // independent occurrences in the surface spelling, and a disagreement
        // means the term is not the numeral it looks like.
        let [instance_literal] = instance_args[..] else { return None };
        if nat_u128(instance_literal)? != value {
            return None;
        }
        return Some(value);
    }

    None
}

fn nat_u128(e: &Expr) -> Option<u128> {
    let n = crate::nat_literal(strip_mdata(e))?;
    // `BigNat` exposes `to_u64`; every width this module admits is <= 64, and a
    // numeral wider than that is refused rather than truncated.
    n.to_u64().map(u128::from)
}

/// Split `f a b c` into `(f, [a, b, c])`, stripping metadata as it goes.
fn uncurry(e: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args: Vec<&Expr> = Vec::new();
    let mut cursor = strip_mdata(e);
    while let ExprKind::App(func, arg) = cursor.kind() {
        args.push(strip_mdata(arg));
        cursor = strip_mdata(func);
    }
    args.reverse();
    (cursor, args)
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{BigNat, Level};

    fn c(n: &str) -> Expr {
        Expr::const_(Name::from_string(n), vec![])
    }

    fn ne(ty: Expr, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Ne"), vec![Level::succ(Level::zero())]), [
            ty, a, b,
        ])
    }

    fn not_eq(ty: Expr, a: Expr, b: Expr) -> Expr {
        Expr::app(
            c("Not"),
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [ty, a, b],
            ),
        )
    }

    /// `UInt64.ofNat n` — the carrier spelling.
    fn carrier_numeral(n: u64) -> Expr {
        Expr::app(c("UInt64.ofNat"), Expr::nat_lit(n))
    }

    /// `OfNat.ofNat UInt64 n (instOfNatUInt64 n)` — the surface spelling.
    fn surface_numeral(n: u64) -> Expr {
        Expr::apps(c("OfNat.ofNat"), [
            c("UInt64"),
            Expr::nat_lit(n),
            Expr::app(c("instOfNatUInt64"), Expr::nat_lit(n)),
        ])
    }

    /// Two value binders (`a`, `b`) are open; the hypothesis is binder 2.
    fn two_values() -> Vec<Option<usize>> {
        vec![Some(0), Some(1)]
    }

    #[test]
    fn both_spellings_of_b_ne_zero_read_identically() {
        for prop in [
            ne(c("UInt64"), Expr::bvar(0), carrier_numeral(0)),
            not_eq(c("UInt64"), Expr::bvar(0), carrier_numeral(0)),
            ne(c("UInt64"), Expr::bvar(0), surface_numeral(0)),
        ] {
            let atom = recognise_hypothesis(&prop, 2, &two_values())
                .unwrap_or_else(|| panic!("`b ≠ 0` must be recognised: {prop:?}"));
            assert_eq!(atom.left(), PreconditionOperand::Argument(1));
            assert_eq!(atom.right(), PreconditionOperand::Literal(0));
            assert_eq!(atom.width(), 64);
        }
    }

    #[test]
    fn the_de_bruijn_inversion_is_the_one_the_telescope_uses() {
        // `bvar(1)` under two open binders names binder 0, the FIRST argument.
        let prop = ne(c("UInt64"), Expr::bvar(1), carrier_numeral(0));
        let atom = recognise_hypothesis(&prop, 2, &two_values()).expect("recognised");
        assert_eq!(
            atom.left(),
            PreconditionOperand::Argument(0),
            "an off-by-one here states the obligation about the WRONG argument, which is \
             a silently wrong precondition rather than a refusal"
        );
    }

    #[test]
    fn a_hypothesis_over_another_proof_is_refused() {
        // Binder 2 IS a hypothesis (erased). A later hypothesis naming it has
        // nothing at the call site to substitute.
        let carried = vec![Some(0), Some(1), None];
        let prop = ne(c("UInt64"), Expr::bvar(0), carrier_numeral(0));
        assert!(
            recognise_hypothesis(&prop, 3, &carried).is_none(),
            "a proof term is erased; a precondition over one cannot be discharged"
        );
    }

    #[test]
    fn an_out_of_range_numeral_refuses_rather_than_wrapping() {
        // 256 does not fit `UInt8`. Reading it as 0 would state a DIFFERENT
        // obligation than the Clean text does.
        let prop = Expr::apps(
            Expr::const_(Name::from_string("Ne"), vec![Level::succ(Level::zero())]),
            [c("UInt8"), Expr::bvar(0), Expr::app(c("UInt8.ofNat"), Expr::nat_lit(256))],
        );
        assert!(recognise_hypothesis(&prop, 1, &[Some(0)]).is_none());

        // …and the in-range twin IS read, so the test above cannot pass because
        // of an unrelated typo.
        let ok = Expr::apps(
            Expr::const_(Name::from_string("Ne"), vec![Level::succ(Level::zero())]),
            [c("UInt8"), Expr::bvar(0), Expr::app(c("UInt8.ofNat"), Expr::nat_lit(255))],
        );
        let atom = recognise_hypothesis(&ok, 1, &[Some(0)]).expect("255 fits u8");
        assert_eq!(atom.right(), PreconditionOperand::Literal(255));
        assert_eq!(atom.width(), 8);
    }

    #[test]
    fn an_unbounded_or_unmodeled_statement_type_refuses() {
        for ty in [c("Nat"), c("Int"), c("Bool"), c("USize")] {
            let prop = ne(ty.clone(), Expr::bvar(0), Expr::bvar(0));
            assert!(
                recognise_hypothesis(&prop, 1, &[Some(0)]).is_none(),
                "a precondition needs a width to be stated at; {ty:?} has none this crate \
                 will guess"
            );
        }
    }

    #[test]
    fn a_disagreeing_surface_instance_literal_is_not_a_numeral() {
        // `OfNat.ofNat UInt64 0 (instOfNatUInt64 7)` is not the numeral it
        // looks like.
        let bogus = Expr::apps(c("OfNat.ofNat"), [
            c("UInt64"),
            Expr::nat_lit(0),
            Expr::app(c("instOfNatUInt64"), Expr::nat_lit(7)),
        ]);
        let prop = ne(c("UInt64"), Expr::bvar(0), bogus);
        assert!(recognise_hypothesis(&prop, 1, &[Some(0)]).is_none());
    }

    #[test]
    fn proposition_shaped_covers_more_than_the_recogniser_admits() {
        // That gap is the point: it decides which REFUSAL is reported.
        let lt = Expr::apps(Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]), [
            c("UInt64"),
            c("instLTUInt64"),
            Expr::bvar(1),
            Expr::bvar(0),
        ]);
        assert!(is_proposition_shaped(&lt));
        assert!(recognise_hypothesis(&lt, 2, &two_values()).is_none());
        // An ordinary value type is not proposition-shaped.
        assert!(!is_proposition_shaped(&c("UInt64")));
    }

    #[test]
    fn a_big_numeral_beyond_u64_refuses() {
        let big = Expr::app(c("UInt64.ofNat"), Expr::bignat_lit(BigNat::from_limbs(vec![0, 1])));
        let prop = ne(c("UInt64"), Expr::bvar(0), big);
        assert!(recognise_hypothesis(&prop, 1, &[Some(0)]).is_none());
    }
}

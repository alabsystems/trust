//! Fail-closed-by-construction discharge results.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0
//!
//! # Why this exists
//!
//! The 2026-06-19 soundness sweep found **eight** false-proofs — programs the
//! verifier reported PROVED/SAFE that can actually panic. Every one had the *same*
//! root cause: the result types let "could not model this" be **represented the
//! same way** as "proven safe". Concretely:
//!
//! ```text
//! let len = len?;                  // None  ⇒  whole fn returns None  ⇒  NO obligation = "safe"
//! match r { Sat => .., _ => None } // _ =>  ⇒  SMT Unknown folded into "no model" = prunable = "safe"
//! if is_total(callee_name) { Undef } // a NAME match ⇒ clean value, no obligation = "safe"
//! ```
//!
//! The `?` operator and catch-all matches are *idiomatic Rust* — so the unsound
//! default wasn't a typo a reviewer would catch; it was the language's default
//! behaviour applied to a type where **absence was overloaded to mean safety**.
//!
//! # What this fixes, mechanistically
//!
//! [`Discharge<T>`] makes the optimistic default **unrepresentable**:
//!
//! * "Unmodeled" is a *distinct* variant ([`Discharge::Unmodeled`]) — never equal to
//!   a modeled value.
//! * It implements [`Try`], and its [`branch`](Try::branch) **propagates**
//!   `Unmodeled` — so `let x = foo()?;` on a `Discharge` carries the *fail-closed*
//!   reason outward instead of silently dropping the obligation. The exact idiom
//!   that admitted HOLE-6A (`let len = len?;`) now *propagates may-panic* rather
//!   than vanishing the bounds check.
//! * The **only** way to assert a modeled/safe value is the explicit, greppable
//!   [`Discharge::modeled`]; there is no `Default`, no `From<Option>`, no way to
//!   reach a modeled value by dropping, `?`-ing, or `_ =>`-ing.
//! * Its combinators form a **monotone lattice toward may-panic**: `Unmodeled` joins
//!   to `Unmodeled` ([`Discharge::and`]), so "every unmodeled path contributes TOP"
//!   stops being a discipline you can forget and becomes an algebraic property the
//!   type enforces.
//!
//! This is the kernel of the "verify-the-verifier" effort: a class of soundness bug
//! that previously had to be *hunted* (adversarial agents + falsification mutants)
//! becomes one the compiler *rejects*.

#[cfg(feature = "try-sugar")]
use std::convert::Infallible;
#[cfg(feature = "try-sugar")]
use std::ops::{ControlFlow, FromResidual, Residual, Try};

/// Why a construct could not be soundly modeled. Carried outward by `?` so the
/// fail-closed verdict is *explained*, not anonymous.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FailReason(pub &'static str);

impl FailReason {
    #[must_use]
    pub fn what(&self) -> &'static str {
        self.0
    }
}

impl std::fmt::Display for FailReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "unmodeled (fail closed): {}", self.0)
    }
}

/// The result of trying to model a construct for discharge.
///
/// `Modeled(T)` is a fully-modeled artifact (a VC, a formula, a verdict).
/// `Unmodeled` is **fail-closed / may-panic (TOP)** — emphatically *not* "safe".
///
/// `?` propagates `Unmodeled`; the only constructor of `Modeled` is the explicit
/// [`Discharge::modeled`]. See the module docs for the soundness rationale.
#[must_use = "dropping a `Discharge` silently loses a soundness obligation; \
              consume it (e.g. `modeled_or` to supply the fail-closed default)"]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Discharge<T> {
    /// The construct was fully and soundly modeled.
    Modeled(T),
    /// The construct could not be soundly modeled — contributes may-panic (TOP).
    /// Propagated by `?`. NEVER silently coerces to a modeled/"safe" value.
    Unmodeled(FailReason),
}

impl<T> Discharge<T> {
    /// The single, explicit, greppable way to assert a fully-modeled value.
    /// (There is deliberately no `Default`/`From<Option>` that could reach here.)
    #[inline]
    pub fn modeled(value: T) -> Self {
        Discharge::Modeled(value)
    }

    /// Fail closed: the construct could not be soundly modeled → may-panic (TOP).
    #[inline]
    pub fn unmodeled(reason: &'static str) -> Self {
        Discharge::Unmodeled(FailReason(reason))
    }

    #[inline]
    #[must_use]
    pub fn is_modeled(&self) -> bool {
        matches!(self, Discharge::Modeled(_))
    }

    #[inline]
    #[must_use]
    pub fn is_unmodeled(&self) -> bool {
        matches!(self, Discharge::Unmodeled(_))
    }

    /// Collapse to a `T`, supplying the fail-closed (TOP) value **explicitly**.
    /// This is the audited boundary where an `Unmodeled` becomes a concrete
    /// may-panic obligation — the one place a reviewer must look.
    #[inline]
    pub fn modeled_or(self, fail_closed: impl FnOnce(FailReason) -> T) -> T {
        match self {
            Discharge::Modeled(t) => t,
            Discharge::Unmodeled(r) => fail_closed(r),
        }
    }

    /// Functor map over the modeled value; `Unmodeled` is carried through unchanged
    /// (monotone — mapping can never turn may-panic into safe).
    #[inline]
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Discharge<U> {
        match self {
            Discharge::Modeled(t) => Discharge::Modeled(f(t)),
            Discharge::Unmodeled(r) => Discharge::Unmodeled(r),
        }
    }

    /// Lattice join toward may-panic: `Modeled` only if BOTH are modeled; any
    /// `Unmodeled` dominates. Encodes "if any sub-part is unmodeled, the whole is
    /// may-panic" so a composite obligation can never be safer than its weakest part.
    #[inline]
    pub fn and<U>(self, other: Discharge<U>) -> Discharge<(T, U)> {
        match (self, other) {
            (Discharge::Modeled(t), Discharge::Modeled(u)) => Discharge::Modeled((t, u)),
            (Discharge::Unmodeled(r), _) | (_, Discharge::Unmodeled(r)) => Discharge::Unmodeled(r),
        }
    }
}

#[cfg(feature = "try-sugar")]
impl<T> Try for Discharge<T> {
    type Output = T;
    type Residual = Discharge<Infallible>;

    #[inline]
    fn from_output(output: T) -> Self {
        Discharge::Modeled(output)
    }

    #[inline]
    fn branch(self) -> ControlFlow<Self::Residual, T> {
        match self {
            Discharge::Modeled(t) => ControlFlow::Continue(t),
            // The load-bearing line: `?` carries the fail-closed reason OUT, instead
            // of dropping the obligation to "safe". This is what makes the
            // `let x = foo()?;` idiom sound by construction.
            Discharge::Unmodeled(r) => ControlFlow::Break(Discharge::Unmodeled(r)),
        }
    }
}

#[cfg(feature = "try-sugar")]
impl<T> FromResidual<Discharge<Infallible>> for Discharge<T> {
    #[inline]
    fn from_residual(residual: Discharge<Infallible>) -> Self {
        match residual {
            Discharge::Unmodeled(r) => Discharge::Unmodeled(r),
            // `Discharge<Infallible>::Modeled` holds an `Infallible`, which has no
            // values — this arm is unreachable.
            Discharge::Modeled(never) => match never {},
        }
    }
}

// Newer rustc's `Try` trait requires `type Residual: Residual<Self::Output>`
// (try_trait_v2_residual). `Discharge<Infallible>` is the residual carrier; its
// `TryType` for any output `T` is `Discharge<T>`.
#[cfg(feature = "try-sugar")]
impl<T> Residual<T> for Discharge<Infallible> {
    type TryType = Discharge<T>;
}

#[cfg(test)]
mod tests {
    use super::*;

    // The whole point, as an executable proof: `?` on a `Discharge` PROPAGATES the
    // fail-closed reason — it can NEVER silently produce a modeled/"safe" value.
    // This is the mechanistic death of HOLE-6A's `let len = len?;` bug.
    #[cfg(feature = "try-sugar")]
    #[test]
    fn question_mark_propagates_fail_closed_never_drops_to_safe() {
        fn unmodeled_len() -> Discharge<u32> {
            Discharge::unmodeled("Vec receiver len not modeled")
        }
        fn bounds_obligation() -> Discharge<u32> {
            let len = unmodeled_len()?; // MUST carry Unmodeled outward, not vanish.
            Discharge::modeled(len + 1)
        }
        match bounds_obligation() {
            Discharge::Unmodeled(r) => assert_eq!(r.what(), "Vec receiver len not modeled"),
            Discharge::Modeled(_) => panic!("`?` produced a modeled value from an unmodeled input \
                                             — the false-proof idiom is back"),
        }
    }

    #[cfg(feature = "try-sugar")]
    #[test]
    fn modeled_flows_through_question_mark() {
        fn modeled_len() -> Discharge<u32> {
            Discharge::modeled(41)
        }
        fn obligation() -> Discharge<u32> {
            let len = modeled_len()?;
            Discharge::modeled(len + 1)
        }
        assert_eq!(obligation(), Discharge::modeled(42));
    }

    #[test]
    fn join_is_monotone_toward_may_panic() {
        let a: Discharge<u32> = Discharge::modeled(1);
        let b: Discharge<u32> = Discharge::unmodeled("element type unknown");
        // ANY unmodeled part makes the composite unmodeled — never safer than its
        // weakest part. (This is the Attack-5 lesson as an algebraic law.)
        assert!(a.clone().and(b.clone()).is_unmodeled());
        assert!(b.and(a.clone()).is_unmodeled());
        assert!(a.clone().and(Discharge::modeled(2u8)).is_modeled());
    }

    #[test]
    fn fail_closed_default_is_explicit_and_audited() {
        // The only way an `Unmodeled` becomes a concrete value is the explicit
        // `modeled_or` boundary — there is no `Default`/`unwrap_or_default` path that
        // could quietly pick "safe".
        let d: Discharge<&str> = Discharge::unmodeled("dyn callee unresolved");
        let verdict = d.modeled_or(|_| "MAY_PANIC");
        assert_eq!(verdict, "MAY_PANIC");
    }
}

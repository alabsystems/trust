// trust-ny-bridge: route a ny-cert Farkas certificate through trust-certify.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! NS-Stage 0 of `docs/NEURO_SYMBOLIC.md`: bring a *neural-shaped* obligation
//! into the **same clean-kernel-checked path** as symbolic ones.
//!
//! A neural-network verifier (ny-cert / CROWN) emits a
//! [`FarkasCertificate`](ny_cert::FarkasCertificate): a linear constraint system
//! asserted infeasible, together with the non-negative Farkas multipliers that
//! collapse it to a contradiction. The *infeasible system itself* is exactly the
//! kind of object [`trust_certify::certify_violation`] refutes: a conjunction of
//! linear-integer order atoms over free `Int` variables. By translating the
//! certificate's constraint system into a [`trust_types::Formula`] violation and
//! handing it to `certify_violation`, the neural obligation lands in the clean
//! CIC kernel's re-check (`TypeChecker::check_type`, `infer_only = false`) — the
//! de Bruijn criterion — which puts the certificate **and** the solver that
//! produced it OUTSIDE the trusted base for that fragment.
//!
//! ## Cardinal rule: never a false `Certified`
//!
//! Everything is **fail-closed**. The supported fragment is the general
//! exact-rational (ℚ) form of ny-cert's Farkas certificates — which is what
//! ny-cert actually emits (f32 network weights are dyadic rationals). Each
//! constraint is **cleared to an equivalent integer constraint** before
//! translation: multiplying both sides of `Σ cᵢ·xᵢ ⋈ k` by the positive
//! integer LCM `L` of every denominator in the constraint preserves the
//! relation at every valuation (`a ⋈ b ⟺ L·a ⋈ L·b` for each of
//! `<, ≤, =, ≥, >` when `L > 0`), and `L` is by construction a common multiple
//! of all denominators, so every scaled value is an exact integer. All
//! clearing arithmetic is *checked* `u128`/`i128`: ANY denominator beyond
//! `u128`, ANY LCM overflow, ANY scaled value out of `i128` range, or ANY
//! downstream kernel rejection returns `None`. A conservative
//! `None`/`Unknown` is always acceptable; a false `Certified` is the worst
//! possible bug in this crate.
//!
//! ## No-feature build
//!
//! The heavy ny-cert dependency is pulled in only under the `ny` feature
//! (`trust-certify` already carries the clean kernel + ay). With the default
//! (no-feature) build this crate is an **empty lib** that compiles instantly;
//! there is no public surface and nothing to test.

#![forbid(unsafe_code)]

#[cfg(feature = "ny")]
mod bridge {
    use ny_cert::{ConstraintKind, FarkasCertificate, LinearConstraint, Rat};
    use trust_types::{Formula, Sort};

    /// Exact-integer projection of a ny-cert [`Rat`].
    ///
    /// Returns `Some(n)` **only** when the rational is an exact integer
    /// (reduced denominator `1`) whose numerator fits `i128`. A denominator
    /// `> 1`, or a numerator out of `i128` range, returns `None` (fail-closed):
    /// the QF_LIA-integer fragment trust-certify reconstructs has no place for a
    /// genuine fraction, so we refuse rather than approximate. This is the
    /// unscaled (`scale = 1`) special case of [`scale_rat_to_i128`]; the
    /// translation path clears denominators first, so it never needs to reject
    /// a fraction whose constraint-wide LCM fits the checked arithmetic.
    #[must_use]
    pub fn rat_to_i128(r: &Rat) -> Option<i128> {
        // `Rat` is stored reduced with a positive denominator (the BigRational
        // invariant), so `den == 1` is exactly the integrality test.
        let den: i128 = r.den().try_into().ok()?;
        if den != 1 {
            return None;
        }
        r.num().try_into().ok()
    }

    /// Greatest common divisor over `u128` (Euclid). `gcd(a, 0) = a`.
    fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
        while b != 0 {
            let t = a % b;
            a = b;
            b = t;
        }
        a
    }

    /// Checked least common multiple over `u128`.
    ///
    /// Returns `None` (fail-closed) when either input is `0` (a denominator can
    /// never be `0` under the `BigRational` positive-denominator invariant, but
    /// we refuse rather than divide by zero) or when the LCM overflows `u128`.
    fn checked_lcm_u128(a: u128, b: u128) -> Option<u128> {
        if a == 0 || b == 0 {
            return None;
        }
        // a / gcd(a, b) is exact, so the only overflow site is the final mul.
        (a / gcd_u128(a, b)).checked_mul(b)
    }

    /// LCM of every denominator in a constraint — all coefficients *and* the
    /// right-hand-side constant — computed with checked `u128` arithmetic.
    ///
    /// This is the positive integer that clears the constraint: scaling both
    /// sides by it yields an equivalent all-integer constraint. Returns `None`
    /// (fail-closed) the instant ANY denominator exceeds `u128` or the running
    /// LCM overflows; we refuse rather than approximate.
    #[must_use]
    pub fn constraint_denominator_lcm(c: &LinearConstraint) -> Option<u128> {
        let mut lcm: u128 = 1;
        // Denominators are positive by the BigRational invariant; a value out
        // of u128 range fails the conversion (and hence the constraint).
        for coeff in c.coefficients.values() {
            let den: u128 = coeff.den().try_into().ok()?;
            lcm = checked_lcm_u128(lcm, den)?;
        }
        let den: u128 = c.constant.den().try_into().ok()?;
        checked_lcm_u128(lcm, den)
    }

    /// Exact scaling of a ny-cert [`Rat`] by a positive integer `scale` that is
    /// a common multiple of its denominator: returns `num · (scale / den)` as
    /// `i128`.
    ///
    /// Every step is checked (fail-closed `None`): the denominator must fit
    /// `u128`, it must divide `scale` exactly (so no division ever rounds — the
    /// caller passes the constraint-wide denominator LCM, which divides by
    /// construction; anything else is refused), the quotient must fit `i128`,
    /// and the final multiplication must not overflow `i128`.
    #[must_use]
    pub fn scale_rat_to_i128(r: &Rat, scale: u128) -> Option<i128> {
        let den: u128 = r.den().try_into().ok()?;
        if den == 0 || !scale.is_multiple_of(den) {
            // Fail-closed: `scale` must be an exact common multiple; a rounded
            // division here would silently change the constraint.
            return None;
        }
        let factor: i128 = i128::try_from(scale / den).ok()?;
        let num: i128 = r.num().try_into().ok()?;
        num.checked_mul(factor)
    }

    /// Map a ny-cert relation onto the matching [`Formula`] comparison
    /// constructor over `lhs ⋈ rhs`.
    fn relate(kind: ConstraintKind, lhs: Formula, rhs: Formula) -> Formula {
        let (l, r) = (Box::new(lhs), Box::new(rhs));
        match kind {
            ConstraintKind::Lt => Formula::Lt(l, r),
            ConstraintKind::Le => Formula::Le(l, r),
            ConstraintKind::Gt => Formula::Gt(l, r),
            ConstraintKind::Ge => Formula::Ge(l, r),
            ConstraintKind::Eq => Formula::Eq(l, r),
        }
    }

    /// Translate one [`LinearConstraint`] `Σ cᵢ·xᵢ ⋈ constant` into a
    /// [`Formula`] over [`Sort::Int`], **clearing rational denominators**.
    ///
    /// Rational clearing: the constraint is first scaled by the positive
    /// integer LCM `L` of every denominator in it ([`constraint_denominator_lcm`]),
    /// which is an equivalence at every valuation (`a ⋈ b ⟺ L·a ⋈ L·b` for
    /// `L > 0` and each of `<, ≤, =, ≥, >`) and makes every scaled coefficient
    /// and the scaled constant an exact integer ([`scale_rat_to_i128`], checked
    /// arithmetic throughout). An all-integer constraint has `L = 1` and passes
    /// through byte-identically to the pre-clearing translation.
    ///
    /// The left-hand side is the sum of the scaled `cᵢ·xᵢ` terms, folded with
    /// `Add` in the certificate's deterministic (sorted-name) coefficient
    /// order; the right-hand side is the scaled `Int(constant)`. A constraint
    /// with no variables has an empty sum, which we render as the integer `0`
    /// (a constant-vs-constant relation — still inside the fragment).
    ///
    /// A scaled coefficient of exactly `1` is emitted as a **bare `Var`**, not
    /// `Mul(Int(1), Var)`: ay normalizes `(* 1 x)` to `x`, so the redundant
    /// `Mul` would make the reconstructed Farkas literal fail to match the
    /// asserted hypothesis and fall back to `trustedAy` (which the zero-trust
    /// budget rejects). Other scaled coefficients (including `-1`) become
    /// `Mul(Int(c), Var)`, the linear-by-constant form trust-certify supports
    /// via a weighted Farkas lemma.
    ///
    /// Returns `None` (fail-closed) the instant clearing leaves the checked
    /// arithmetic: a denominator beyond `u128`, an LCM overflow, or a scaled
    /// value out of `i128` range.
    #[must_use]
    pub fn linear_constraint_to_formula(c: &LinearConstraint) -> Option<Formula> {
        let scale = constraint_denominator_lcm(c)?;
        let mut lhs: Option<Formula> = None;
        // BTreeMap iteration is sorted by name → deterministic fold order.
        for (name, coeff) in &c.coefficients {
            let coeff = scale_rat_to_i128(coeff, scale)?;
            // ny-cert's `with_kind` already drops zero coefficients; skip any
            // that slip through so we never emit a `0*x` term.
            if coeff == 0 {
                continue;
            }
            let var = Formula::Var(name.clone(), Sort::Int);
            let term = if coeff == 1 {
                var
            } else {
                Formula::Mul(Box::new(Formula::Int(coeff)), Box::new(var))
            };
            lhs = Some(match lhs {
                None => term,
                Some(acc) => Formula::Add(Box::new(acc), Box::new(term)),
            });
        }
        let lhs = lhs.unwrap_or(Formula::Int(0));
        let constant = scale_rat_to_i128(&c.constant, scale)?;
        Some(relate(c.kind, lhs, Formula::Int(constant)))
    }

    /// Translate a [`FarkasCertificate`] into the violation [`Formula`] that
    /// [`trust_certify::certify_violation`] refutes.
    ///
    /// The certificate asserts its constraint system is **infeasible**; that
    /// system — the conjunction of all its constraints, each cleared to integer
    /// form — *is* the violation the clean kernel must refute as `False`. (The
    /// multipliers are the solver's own witness; they are deliberately ignored
    /// here, since the kernel re-derives the refutation from the asserted
    /// system itself, keeping the ny-cert solver outside the trusted base.
    /// Rational multipliers therefore need no clearing of their own: a
    /// nonnegative ℚ-combination refuting the original system, rescaled
    /// per-constraint and cleared by the positive LCM of its denominators, is a
    /// nonnegative ℤ-combination refuting the cleared system — so an integer
    /// Farkas witness always exists for ay to re-derive.)
    ///
    /// Returns `None` if the system is empty or ANY constraint fails rational
    /// clearing into the checked-`i128` integer fragment (fail-closed).
    #[must_use]
    pub fn farkas_to_violation(cert: &FarkasCertificate) -> Option<Formula> {
        if cert.constraints.is_empty() {
            return None;
        }
        let mut conjuncts = Vec::with_capacity(cert.constraints.len());
        for c in &cert.constraints {
            conjuncts.push(linear_constraint_to_formula(c)?);
        }
        Some(Formula::And(conjuncts))
    }

    /// Route a ny-cert [`FarkasCertificate`] through the clean-kernel-checked
    /// Certified path.
    ///
    /// Translates the certificate's infeasible system to a violation
    /// [`Formula`], then hands it to [`trust_certify::certify_violation`], which
    /// drives the in-process ay solver, reconstructs a kernel proof term under a
    /// ZERO-TRUST budget, and re-checks it with the clean CIC kernel. Returns
    /// `Some(ProofEvidence::CleanCic { .. })` only when that whole pipeline
    /// succeeds; `None` on ANY failure — a cert whose rational clearing leaves
    /// the checked arithmetic, a non-`UNSAT` system, residual trust, or kernel
    /// rejection. Never a false `Certified`.
    #[must_use]
    pub fn certify_farkas(cert: &FarkasCertificate) -> Option<trust_ir::ProofEvidence> {
        let violation = farkas_to_violation(cert)?;
        trust_certify::certify_violation(&violation)
    }
}

#[cfg(feature = "ny")]
pub use bridge::{
    certify_farkas, constraint_denominator_lcm, farkas_to_violation,
    linear_constraint_to_formula, rat_to_i128, scale_rat_to_i128,
};

#[cfg(all(test, feature = "ny"))]
mod tests {
    use super::*;
    use ny_cert::{ConstraintKind, FarkasCertificate, LinearConstraint, Rat};
    use trust_types::Formula;

    fn int(n: i128) -> Rat {
        Rat::from_int(n)
    }

    /// (a) An integer-coefficient INFEASIBLE system `x ≤ 1 ∧ x ≥ 2` routes all
    /// the way through to a kernel-CHECKED `CleanCic` certificate — the de
    /// Bruijn criterion applied to a neural-shaped input. The clean kernel
    /// (not the ny-cert solver) re-derives and re-checks the refutation.
    #[test]
    fn certifies_integer_infeasible_system_as_cleancic() {
        // x ≤ 1  and  x ≥ 2  →  infeasible over the integers (and the reals).
        let cert = FarkasCertificate {
            constraints: vec![
                LinearConstraint::with_kind(ConstraintKind::Le, &[("x", int(1))], int(1)),
                LinearConstraint::with_kind(ConstraintKind::Ge, &[("x", int(1))], int(2)),
            ],
            // Multipliers are ignored by the bridge; the kernel re-derives the
            // refutation. Provide the genuine Farkas witness (1·c0 + 1·c1) for
            // realism.
            multipliers: vec![Rat::ONE, Rat::ONE],
        };

        let evidence =
            certify_farkas(&cert).expect("integer-coefficient infeasible system must certify");

        match evidence {
            trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } => {
                assert!(!term.is_empty(), "CleanCic term bytes must be non-empty");
                assert!(!context.is_empty(), "CleanCic context bytes must be non-empty");
                assert_ne!(
                    lineage,
                    trust_ir::ProofDigest::zero(),
                    "lineage digest must bind the payload"
                );
            }
            other => panic!("expected ProofEvidence::CleanCic, got {other:?}"),
        }
    }

    /// (a) A genuinely RATIONAL infeasible system — denominators {2, 3, 6},
    /// exactly what ny-cert emits — now routes all the way through to a
    /// kernel-CHECKED `CleanCic` certificate via rational clearing. Before the
    /// clearing extension this certificate returned `None` at translation.
    ///
    ///   (1/2)·x ≤ 1    —·2→   x ≤ 2
    ///   (1/3)·x ≥ 7/6  —·6→   2·x ≥ 7      (so x ≥ 3.5 — infeasible with x ≤ 2)
    ///
    /// The downstream path is IDENTICAL to the integer test above: ay refutes
    /// the cleared system and the clean kernel re-checks the proof term. The
    /// rational multipliers (1, 3/2) are the solver's witness for the original
    /// units; the bridge ignores them and the kernel re-derives.
    #[test]
    fn certifies_rational_infeasible_system_as_cleancic() {
        let half = Rat::new(1, 2).expect("1/2 is a valid rational");
        let third = Rat::new(1, 3).expect("1/3 is a valid rational");
        let seven_sixths = Rat::new(7, 6).expect("7/6 is a valid rational");
        let cert = FarkasCertificate {
            constraints: vec![
                LinearConstraint::with_kind(ConstraintKind::Le, &[("x", half)], int(1)),
                LinearConstraint::with_kind(ConstraintKind::Ge, &[("x", third)], seven_sixths),
            ],
            multipliers: vec![Rat::ONE, Rat::new(3, 2).expect("3/2 is a valid rational")],
        };

        // Clearing is exact: the translated violation is the integer system.
        let violation =
            farkas_to_violation(&cert).expect("rational system must clear to integer form");
        let x = || Box::new(Formula::Var("x".into(), trust_types::Sort::Int));
        assert_eq!(
            violation,
            Formula::And(vec![
                Formula::Le(x(), Box::new(Formula::Int(2))),
                Formula::Ge(
                    Box::new(Formula::Mul(Box::new(Formula::Int(2)), x())),
                    Box::new(Formula::Int(7)),
                ),
            ]),
            "clearing must scale each constraint by its own denominator LCM"
        );

        let evidence =
            certify_farkas(&cert).expect("rational infeasible system must certify after clearing");
        match evidence {
            trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } => {
                assert!(!term.is_empty(), "CleanCic term bytes must be non-empty");
                assert!(!context.is_empty(), "CleanCic context bytes must be non-empty");
                assert_ne!(
                    lineage,
                    trust_ir::ProofDigest::zero(),
                    "lineage digest must bind the payload"
                );
            }
            other => panic!("expected ProofEvidence::CleanCic, got {other:?}"),
        }
    }

    /// (a) The REAL corpus infeasibility certificates — the four all-integer
    /// ReLU-encoding Farkas witnesses ay-milp extracts from ny's captured
    /// `mip-46963-*` VNN-COMP window MILPs — each route all the way through to a
    /// kernel-CHECKED `CleanCic` certificate. These are GENUINE multi-variable
    /// linear-integer Farkas combinations (e.g. `2·x0 − x1 ≥ −3`,
    /// `x3 + x5 − x8 ≥ 0`), NOT single-variable intervals or unit-coefficient
    /// chains: the contradiction needs a weighted ℚ-combination, cleared to a
    /// nonnegative ℤ-combination, which ay re-derives and the clean kernel
    /// re-checks under a ZERO-TRUST budget. The constraint systems are the exact
    /// facts ay-milp's `FarkasCertificate` references, transcribed from the
    /// `handoff_mip-46963-*.cert` extractions.
    #[test]
    fn certifies_real_corpus_relu_farkas_certs_as_cleancic() {
        // (kind, constant, [(var, coeff)…]) — one entry per referenced fact.
        type C<'a> = (ConstraintKind, i128, &'a [(&'a str, i128)]);
        let ge = ConstraintKind::Ge;
        let le = ConstraintKind::Le;

        // mip-46963-000012: x0 ≤ 1 ; 2·x0 − x1 ≥ −3 ; x1 ≥ 10.
        let c000012: Vec<C> = vec![
            (le, 1, &[("x0", 1)]),
            (ge, -3, &[("x0", 2), ("x1", -1)]),
            (ge, 10, &[("x1", 1)]),
        ];
        // mip-46963-000021: x1 ≤ 1 ; x5 ≤ 1 ; x1 − x3 ≥ 0 ; x3 + x5 − x8 ≥ 0 ; x8 ≥ 10.
        let c000021: Vec<C> = vec![
            (le, 1, &[("x1", 1)]),
            (le, 1, &[("x5", 1)]),
            (ge, 0, &[("x1", 1), ("x3", -1)]),
            (ge, 0, &[("x3", 1), ("x5", 1), ("x8", -1)]),
            (ge, 10, &[("x8", 1)]),
        ];
        // mip-46963-000022: identical shape to 000021.
        let c000022 = c000021.clone();
        // mip-46963-000023 (8 facts): the deepest chain.
        let c000023: Vec<C> = vec![
            (le, 1, &[("x0", 1)]),
            (le, 1, &[("x1", 1)]),
            (ge, 1, &[("x6", 1)]),
            (ge, 0, &[("x1", 1), ("x3", -1)]),
            (ge, 1, &[("x0", 1), ("x1", 1), ("x4", -1)]),
            (le, 1, &[("x4", -1), ("x5", 1), ("x6", 1)]),
            (ge, 0, &[("x3", 1), ("x5", 1), ("x8", -1)]),
            (ge, 10, &[("x8", 1)]),
        ];

        for (name, system) in [
            ("mip-46963-000012", &c000012),
            ("mip-46963-000021", &c000021),
            ("mip-46963-000022", &c000022),
            ("mip-46963-000023", &c000023),
        ] {
            let constraints: Vec<LinearConstraint> = system
                .iter()
                .map(|(kind, k, terms)| {
                    let ts: Vec<(&str, Rat)> =
                        terms.iter().map(|(v, a)| (*v, int(*a))).collect();
                    LinearConstraint::with_kind(*kind, &ts, int(*k))
                })
                .collect();
            // Multipliers are ignored by the bridge (the kernel re-derives); a
            // 1-per-constraint placeholder keeps the cert well-formed.
            let multipliers = vec![Rat::ONE; constraints.len()];
            let cert = FarkasCertificate { constraints, multipliers };

            let evidence = certify_farkas(&cert)
                .unwrap_or_else(|| panic!("{name}: real corpus Farkas cert must certify as CleanCic"));
            match evidence {
                trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } => {
                    assert!(!term.is_empty(), "{name}: CleanCic term bytes must be non-empty");
                    assert!(!context.is_empty(), "{name}: CleanCic context bytes must be non-empty");
                    assert_ne!(
                        lineage,
                        trust_ir::ProofDigest::zero(),
                        "{name}: lineage digest must bind the payload"
                    );
                }
                other => panic!("{name}: expected ProofEvidence::CleanCic, got {other:?}"),
            }
        }
    }

    /// (SOUNDNESS) The multi-variable Farkas path must NOT certify a SATISFIABLE
    /// system. This is corpus cert `mip-46963-000012` with its one binding bound
    /// relaxed (`x1 ≥ 10` → `x1 ≥ 0`): now `x0 = x1 = 0` satisfies all three
    /// constraints (`2·0 − 0 = 0 ≥ −3` ✓), so no nonnegative Farkas combination
    /// yields a contradiction. `certify_farkas` must return `None` — a false
    /// `Certified` here would be exactly the unsoundness the whole path exists to
    /// make unrepresentable. (Same negative-coefficient shape that DOES certify
    /// when `x1 ≥ 10`, so this isolates the feasibility check, not the shape.)
    #[test]
    fn satisfiable_negative_coefficient_system_must_not_certify() {
        let ge = ConstraintKind::Ge;
        let le = ConstraintKind::Le;
        let cert = FarkasCertificate {
            constraints: vec![
                LinearConstraint::with_kind(le, &[("x0", int(1))], int(1)),
                LinearConstraint::with_kind(ge, &[("x0", int(2)), ("x1", int(-1))], int(-3)),
                LinearConstraint::with_kind(ge, &[("x1", int(1))], int(0)), // relaxed: was ≥ 10
            ],
            multipliers: vec![Rat::ONE, Rat::ONE, Rat::ONE],
        };
        assert!(
            certify_farkas(&cert).is_none(),
            "a SATISFIABLE negative-coefficient system must fail closed, never certify"
        );
    }

    /// Rational clearing scales a MIXED-denominator constraint by the LCM of
    /// all its denominators — {2, 3, 6} → 6 — and every scaled value is an
    /// exact integer: (1/2)·x + (1/3)·y ≤ 5/6  —·6→  3·x + 2·y ≤ 5.
    #[test]
    fn clears_mixed_denominators_within_one_constraint() {
        let c = LinearConstraint::with_kind(
            ConstraintKind::Le,
            &[("x", Rat::new(1, 2).unwrap()), ("y", Rat::new(1, 3).unwrap())],
            Rat::new(5, 6).unwrap(),
        );
        assert_eq!(constraint_denominator_lcm(&c), Some(6));
        let f = linear_constraint_to_formula(&c).expect("mixed denominators must clear");
        let var = |n: &str| Box::new(Formula::Var(n.into(), trust_types::Sort::Int));
        assert_eq!(
            f,
            Formula::Le(
                Box::new(Formula::Add(
                    Box::new(Formula::Mul(Box::new(Formula::Int(3)), var("x"))),
                    Box::new(Formula::Mul(Box::new(Formula::Int(2)), var("y"))),
                )),
                Box::new(Formula::Int(5)),
            ),
            "clearing by LCM 6 must yield 3x + 2y ≤ 5 exactly"
        );
    }

    /// A coefficient that clears to exactly `1` is emitted as a bare `Var`
    /// (the ay-normal form), same as an unscaled unit coefficient:
    /// (1/6)·x + (1/2)·y ≤ 4/3  —·6→  x + 3·y ≤ 8.
    #[test]
    fn cleared_unit_coefficient_is_bare_var() {
        let c = LinearConstraint::with_kind(
            ConstraintKind::Le,
            &[("x", Rat::new(1, 6).unwrap()), ("y", Rat::new(1, 2).unwrap())],
            Rat::new(4, 3).unwrap(),
        );
        let f = linear_constraint_to_formula(&c).expect("must clear");
        let var = |n: &str| Box::new(Formula::Var(n.into(), trust_types::Sort::Int));
        assert_eq!(
            f,
            Formula::Le(
                Box::new(Formula::Add(
                    var("x"),
                    Box::new(Formula::Mul(Box::new(Formula::Int(3)), var("y"))),
                )),
                Box::new(Formula::Int(8)),
            ),
            "a coefficient clearing to 1 must be a bare Var, not Mul(Int(1), _)"
        );
    }

    /// (b) Overflow anywhere in clearing fails CLOSED. A denominator beyond
    /// `u128` range can never participate in checked clearing.
    #[test]
    fn fails_closed_on_denominator_beyond_u128() {
        use num_bigint::BigInt;
        // 1 / 2^200 — the denominator does not fit u128.
        let tiny = Rat::from_bigints(BigInt::from(1), BigInt::from(1) << 200).unwrap();
        let c = LinearConstraint::with_kind(ConstraintKind::Le, &[("x", tiny)], int(1));
        assert_eq!(constraint_denominator_lcm(&c), None, "den > u128 must fail closed");
        assert!(linear_constraint_to_formula(&c).is_none(), "translation must fail closed");
        let cert = FarkasCertificate {
            constraints: vec![c, LinearConstraint::with_kind(ConstraintKind::Ge, &[("x", int(1))], int(2))],
            multipliers: vec![Rat::ONE, Rat::ONE],
        };
        assert!(certify_farkas(&cert).is_none(), "certify_farkas must fail closed");
    }

    /// (b) The LCM itself overflowing `u128` fails CLOSED: 2^127 and 2^127 − 1
    /// are coprime, so their LCM is their product ≈ 2^254 ≫ u128::MAX.
    #[test]
    fn fails_closed_on_lcm_overflow() {
        use num_bigint::BigInt;
        let d1 = Rat::from_bigints(BigInt::from(1), BigInt::from(1) << 127).unwrap();
        let d2 =
            Rat::from_bigints(BigInt::from(1), (BigInt::from(1) << 127) - BigInt::from(1)).unwrap();
        let c = LinearConstraint::with_kind(ConstraintKind::Le, &[("x", d1), ("y", d2)], int(1));
        assert_eq!(
            constraint_denominator_lcm(&c),
            None,
            "coprime 2^127 and 2^127−1 must overflow the checked LCM"
        );
        assert!(linear_constraint_to_formula(&c).is_none(), "translation must fail closed");
    }

    /// (b) Scaling overflow fails CLOSED: numerator 2^126 with denominator 3,
    /// sharing a constraint with denominator 2, clears by LCM 6 with factor 2 —
    /// and 2^126 · 2 = 2^127 > i128::MAX.
    #[test]
    fn fails_closed_on_scaling_overflow() {
        use num_bigint::BigInt;
        let big = Rat::from_bigints(BigInt::from(1) << 126, BigInt::from(3)).unwrap();
        assert_eq!(
            scale_rat_to_i128(&big, 6),
            None,
            "checked mul must refuse a scaled numerator beyond i128"
        );
        let c = LinearConstraint::with_kind(
            ConstraintKind::Le,
            &[("x", big), ("y", Rat::new(1, 2).unwrap())],
            int(1),
        );
        assert_eq!(constraint_denominator_lcm(&c), Some(6), "the LCM itself is fine");
        assert!(linear_constraint_to_formula(&c).is_none(), "translation must fail closed");
        // A numerator already beyond i128 fails closed even unscaled.
        let huge = Rat::from_bigints(BigInt::from(1) << 200, BigInt::from(1)).unwrap();
        assert_eq!(scale_rat_to_i128(&huge, 1), None, "num > i128 must fail closed");
    }

    /// `scale_rat_to_i128` refuses a `scale` that is NOT a common multiple of
    /// the denominator (a rounded division would silently change the
    /// constraint) — fail-closed even against caller misuse.
    #[test]
    fn scale_rat_to_i128_requires_exact_multiple() {
        let third = Rat::new(1, 3).unwrap();
        assert_eq!(scale_rat_to_i128(&third, 4), None, "3 ∤ 4 must fail closed");
        assert_eq!(scale_rat_to_i128(&third, 6), Some(2), "6/3 · 1 = 2 exactly");
        assert_eq!(scale_rat_to_i128(&Rat::new(-5, 2).unwrap(), 6), Some(-15));
        assert_eq!(scale_rat_to_i128(&Rat::from_int(7), 1), Some(7));
    }

    /// A system that becomes FEASIBLE after clearing must not certify: the
    /// cleared form of (1/2)·x ≤ 1 ∧ x ≥ 2 is x ≤ 2 ∧ x ≥ 2, satisfied by
    /// x = 2 — ay finds it SAT and the pipeline returns `None` (fail-closed;
    /// never a fabricated `Certified` for a satisfiable system).
    #[test]
    fn feasible_after_clearing_does_not_certify() {
        let half = Rat::new(1, 2).expect("1/2 is a valid rational");
        // Fractions still never project through the UNSCALED integer path…
        assert_eq!(rat_to_i128(&half), None, "fractional Rat must not project to i128");
        let cert = FarkasCertificate {
            constraints: vec![
                LinearConstraint::with_kind(ConstraintKind::Le, &[("x", half)], int(1)),
                LinearConstraint::with_kind(ConstraintKind::Ge, &[("x", int(1))], int(2)),
            ],
            multipliers: vec![Rat::ONE, Rat::ONE],
        };
        // …but the constraint now TRANSLATES (clearing: x ≤ 2)…
        let f = linear_constraint_to_formula(&cert.constraints[0])
            .expect("fractional coefficient must clear");
        assert_eq!(
            f,
            Formula::Le(
                Box::new(Formula::Var("x".into(), trust_types::Sort::Int)),
                Box::new(Formula::Int(2)),
            ),
        );
        // …and the certificate is rejected on its (lack of) merits: SAT.
        assert!(
            certify_farkas(&cert).is_none(),
            "a satisfiable cleared system must never certify"
        );
    }

    /// `rat_to_i128` accepts exact integers (including negatives and reduced
    /// fractions that collapse to integers) and rejects genuine fractions.
    #[test]
    fn rat_to_i128_exact_integer_only() {
        assert_eq!(rat_to_i128(&Rat::from_int(0)), Some(0));
        assert_eq!(rat_to_i128(&Rat::from_int(7)), Some(7));
        assert_eq!(rat_to_i128(&Rat::from_int(-9)), Some(-9));
        // 4/2 reduces to 2 → an exact integer.
        assert_eq!(rat_to_i128(&Rat::new(4, 2).unwrap()), Some(2));
        // 1/3 is a genuine fraction.
        assert_eq!(rat_to_i128(&Rat::new(1, 3).unwrap()), None);
    }

    /// The translated violation is the conjunction of all constraints, in
    /// certificate order, over `Sort::Int`.
    #[test]
    fn farkas_to_violation_is_conjunction_of_constraints() {
        let cert = FarkasCertificate {
            constraints: vec![
                LinearConstraint::with_kind(ConstraintKind::Le, &[("x", int(1))], int(1)),
                LinearConstraint::with_kind(ConstraintKind::Ge, &[("x", int(1))], int(2)),
            ],
            multipliers: vec![Rat::ONE, Rat::ONE],
        };
        let violation = farkas_to_violation(&cert).expect("integer system must translate");
        match violation {
            Formula::And(conjuncts) => {
                assert_eq!(conjuncts.len(), 2, "one conjunct per constraint");
            }
            other => panic!("expected And of constraints, got {other:?}"),
        }
    }

    /// An empty constraint system is not a violation (fail-closed).
    #[test]
    fn fails_closed_on_empty_system() {
        let cert = FarkasCertificate { constraints: vec![], multipliers: vec![] };
        assert!(farkas_to_violation(&cert).is_none(), "empty system must fail closed");
        assert!(certify_farkas(&cert).is_none(), "empty system must not certify");
    }
}

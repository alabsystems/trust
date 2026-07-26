// trust-router/ay_certify.rs: NATIVE kernel certification of an ay UNSAT proof.
//
// Experimental native reconstruction of selected ay UNSAT proofs in Clean.
//
// IMPORTANT: this module does NOT own router certification authority.  It can
// produce locally kernel-checked candidate payloads, but the live
// `VerificationResult` carrier cannot yet bind those bytes to the exact VC
// digest or replay them at every `Certified` consumer.  The public in-process
// backend therefore remains `SmtBacked`; see its `promote_to_certified` hard
// block.  Do not use `CertifyOutcome::Certified` as a router assurance label.
//
// ## The trust root is the Clean kernel — NOT ay, NOT Carcara
//
// The certification pipeline is:
//
//   ay UNSAT (structured `ay_core::Proof`)
//      │  [clean-auto `attempt_reconstruction` — reads ay's OWN proof data
//      │   structures; no Alethe string round-trip, no Carcara]
//      ▼
//   `clean_kernel::Expr` refutation term
//      │  [clean-auto `certify_reconstruction` — 5 FAIL-CLOSED gates incl. the
//      │   real kernel `check_type(proof_term, False)` and an INDEPENDENT
//      │   `trustedAy`/`trustedArith` re-scan]
//      ▼
//   `CertifiedPayload { trust_count: 0 }`   ⇒   local reconstruction candidate
//                                               (NOT a router promotion)
//
// `clean-auto` is pulled in with its DEFAULT (`ay-smt`) features ONLY — NOT
// `carcara-verify`. So the `carcara::check` path is not even linked into this
// decision: a false Carcara verdict cannot affect the trust seal. The
// `carcara-crosscheck` lane (a separate feature) remains an OPTIONAL
// defense-in-depth pre-check on the SmtBacked lane, never the trust root here.
//
// ## Scope (honest)
//
// Milestone 1 is the 2-bound QF_LIA fragment named by the roadmap: a violation
// formula equivalent to `lo < x ∧ x < hi` with `hi <= lo` (UNSAT). This is the
// smallest real obligation that goes ay-Alethe → kernel-`Certified` end-to-end.
// The same pipe generalizes theory-by-theory (BV mul/div/shift, arrays,
// nonlinear, quantifiers) — that is future work; see
// reports/proof-carrying-ay-roadmap.md §(a.3)/§(b.2).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use ay_core::{FarkasAnnotation, Proof, TermStore, TheoryLemmaKind};
use clean_auto::bridge::ay_contract::{
    CertifiedPayload, NotCertified, VariableMapping, reconstruct_and_certify_ay_proof,
};
use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, ConstantKind, Environment, Expr, ExprVisitor, FVarId, Level, LevelVec,
    LocalContext, TypeChecker, is_foundational_axiom, is_trust_marker,
};

/// Why a native kernel certification attempt did not yield a `Certified` seal.
///
/// Every variant is FAIL-CLOSED: the caller keeps the honest pre-certification
/// verdict (`SmtBacked` from ay's strict checker) rather than upgrading. A
/// `Certified` seal is emitted ONLY on [`CertifyOutcome::Certified`].
#[derive(Debug)]
pub enum CertifyOutcome {
    /// The Clean kernel re-checked the reconstructed refutation to `False`
    /// modulo the 3 Lean-core axioms, with ZERO trust in ay. Carries the
    /// serialized kernel proof term (the auditable evidence).
    Certified(CertifiedPayload),
    /// Reconstruction/certification did not fully close in the kernel (a
    /// residual `trustedAy`, an open term, or a kernel rejection). The honest
    /// `SmtBacked` verdict survives.
    NotCertified(NotCertified),
    /// A non-foundational domain axiom (or a trust marker) survived in the
    /// certified term's transitive constant closure — the modulo-3 residue
    /// check failed, so we refuse to call it `Certified`.
    AxiomResidueImpure(Vec<String>),
}

impl CertifyOutcome {
    /// True iff the Clean kernel certified the refutation with a clean modulo-3
    /// axiom residue and zero trust in ay.
    #[must_use]
    pub fn is_certified(&self) -> bool {
        matches!(self, CertifyOutcome::Certified(_))
    }
}

/// `Int.ofNat n` — the kernel encoding of a non-negative integer literal, the
/// exact form clean-auto's concrete-Int chain closer recognizes.
fn int_ofnat(n: u64) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), Expr::nat_lit(n))
}

/// `@LT.lt.{0} Int instLTInt a b` — the kernel proposition `a < b` over `Int`.
fn lt_int(a: &Expr, b: &Expr) -> Expr {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]), int_ty),
                Expr::const_(Name::from_string("instLTInt"), vec![]),
            ),
            a.clone(),
        ),
        b.clone(),
    )
}

/// `Not False` — the negated goal for a proof-by-contradiction whose conclusion
/// is `False` (the reconstructor closes the empty clause into a proof of the
/// negated goal; here the goal is literally `False`).
fn negated_false_goal() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        Expr::const_(Name::from_string("False"), vec![]),
    )
}

/// Classify an axiom `name` (already known to be a `ConstantKind::Axiom`) as
/// SOUNDNESS RESIDUE or a benign parameter.
///
/// An axiom is soundness residue — a genuine gap in a `Certified` claim — iff:
///   * it is a TRUST MARKER (`sorryAx` / `sorry` / `trustedAy` / `trustedArith`;
///     `is_trust_marker`), OR
///   * its type is a PROPOSITION (`infer_sort(type) == 0`, i.e. `Sort 0` / `Prop`),
///     meaning the axiom ASSERTS an unproved fact (a domain lemma).
///
/// It is NOT residue when its type lives in `Type`/`Sort u≥1` — those are pure
/// DATA/PARAMETER declarations. The VC's own free variable (`x : Int`, modeled
/// as the opaque axiom `testX`) is exactly such a parameter: it is the `∀x` the
/// obligation quantifies over, not an unproved lemma, so it must not count as
/// residue. (Foundational axioms — propext/Quot.sound/Classical.choice — are
/// filtered by `is_foundational_axiom` before we reach here.)
fn axiom_is_soundness_residue(name: &Name, ty: &Expr, env: &Environment) -> bool {
    if is_trust_marker(name) {
        return true;
    }
    // Propositional axiom ⇒ asserts a fact ⇒ residue. A sort-inference failure
    // is treated conservatively AS residue (fail-closed: an axiom we cannot
    // classify must not silently pass the purity gate).
    let tc = TypeChecker::new(env);
    match tc.infer_sort(ty) {
        Ok(level) => level.is_zero(),
        Err(_) => true,
    }
}

/// Walk a certified term's transitive constant closure and return every
/// SOUNDNESS-RESIDUE axiom it reaches (trust markers + propositional/domain
/// axioms), classified against `env` via [`axiom_is_soundness_residue`].
///
/// Empty ⇒ the term's axiom residue is `⊆` the 3 Lean-core axioms (modulo 3),
/// with no ay/arith trust and no unproved lemma — the strongest honesty check
/// on a `Certified` claim. Benign data parameters (the VC's free variables) are
/// intentionally excluded.
fn scan_axiom_residue(term: &Expr, env: &Environment) -> Vec<String> {
    let mut residue = std::collections::BTreeSet::new();
    let mut seen = std::collections::BTreeSet::new();
    let mut worklist: Vec<Name> = collect_const_names(term);

    while let Some(name) = worklist.pop() {
        if !seen.insert(name.to_string()) {
            continue;
        }
        let Some(info) = env.get_const(&name) else {
            continue;
        };
        if info.kind == ConstantKind::Axiom
            && !is_foundational_axiom(&name)
            && axiom_is_soundness_residue(&name, &info.type_, env)
        {
            residue.insert(name.to_string());
        }
        // Follow transitive references through the constant's type and value.
        worklist.extend(collect_const_names(&info.type_));
        if let Some(value) = info.value.as_ref() {
            worklist.extend(collect_const_names(value));
        }
    }

    residue.into_iter().collect()
}

/// Collect every `Const` name referenced anywhere in `expr`.
fn collect_const_names(expr: &Expr) -> Vec<Name> {
    struct Collector;
    impl ExprVisitor for Collector {
        type Result = Vec<Name>;
        fn combine(&self, mut a: Self::Result, mut b: Self::Result) -> Self::Result {
            a.append(&mut b);
            a
        }
        fn visit_const(&mut self, name: &Name, _levels: &LevelVec) -> Self::Result {
            vec![name.clone()]
        }
    }
    Collector.visit_expr(expr)
}

/// Environment with the Int arithmetic + ordering lemmas the concrete-Int chain
/// closer needs (`init_int_ord_lemmas`), plus the `testX` symbol the fixture
/// binds. Mirrors clean-auto's own `mk_env_for_int_arith` e2e setup.
fn int_arith_env() -> Result<Environment, String> {
    let mut env = Environment::new();
    env.init_int_ord_lemmas().map_err(|e| format!("init_int_ord_lemmas: {e:?}"))?;
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    env.add_decl(clean_kernel::Declaration::Axiom {
        name: Name::from_string("testX"),
        level_params: vec![],
        type_: int_ty,
    })
    .map_err(|e| format!("add testX: {e:?}"))?;
    Ok(env)
}

/// Build ay's structured UNSAT proof for `lo < x ∧ x < hi` (UNSAT when
/// `hi <= lo`), plus the `VariableMapping` and hypothesis `LocalContext` the
/// reconstruction consumes. `complete` controls whether the propositional
/// skeleton actually derives the empty clause: when `false`, the second
/// resolution is dropped so the root still carries `¬(x < hi)` — a deliberately
/// INCOMPLETE proof for the fail-closed negative control.
///
/// Constants are genuine ay integers (`mk_int`), matching a real ay QF_LIA
/// refutation, so clean-auto's concrete-Int closer discharges `lo < hi` via
/// `NonNeg.casesOn` with NO `trustedAy`.
fn build_lia_two_bound_proof(
    lo: u64,
    hi: u64,
    complete: bool,
) -> (TermStore, VariableMapping, Proof, LocalContext) {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let lo_e = int_ofnat(lo);
    let hi_e = int_ofnat(hi);
    let test_x = Expr::const_(Name::from_string("testX"), vec![]);

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let ay_lo = terms.mk_int(num_bigint::BigInt::from(lo));
    let ay_hi = terms.mk_int(num_bigint::BigInt::from(hi));
    let ay_x = terms.mk_var("testX", ay::Sort::Int);

    map.register_var("testX", test_x.clone(), int_ty);

    let lt_lo_x = terms.mk_lt(ay_lo, ay_x);
    let lt_x_hi = terms.mk_lt(ay_x, ay_hi);
    let not_lt_lo_x = terms.mk_not(lt_lo_x);
    let not_lt_x_hi = terms.mk_not(lt_x_hi);

    let lt_lo_x_prop = lt_int(&lo_e, &test_x);
    let lt_x_hi_prop = lt_int(&test_x, &hi_e);

    let h1 = FVarId::new(10);
    let h2 = FVarId::new(11);
    map.register_hypothesis("h_lo_lt_x", h1, Expr::fvar(h1), lt_lo_x_prop.clone());
    map.register_hypothesis("h_x_lt_hi", h2, Expr::fvar(h2), lt_x_hi_prop.clone());

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    let s0 = proof.add_theory_lemma_with_farkas_and_kind(
        "LIA",
        vec![not_lt_lo_x, not_lt_x_hi],
        farkas,
        TheoryLemmaKind::LiaGeneric,
    );
    let s1 = proof.add_assume(lt_lo_x, None);
    let s2 = proof.add_resolution(vec![not_lt_x_hi], not_lt_lo_x, s0, s1);
    if complete {
        let s3 = proof.add_assume(lt_x_hi, None);
        proof.add_resolution(vec![], not_lt_x_hi, s2, s3);
    }

    let mut ctx = LocalContext::new();
    ctx.push_with_id(h1, Name::from_string("h_lo_lt_x"), lt_lo_x_prop, BinderInfo::Default);
    ctx.push_with_id(h2, Name::from_string("h_x_lt_hi"), lt_x_hi_prop, BinderInfo::Default);

    (terms, map, proof, ctx)
}

/// Natively certify the milestone-1 QF_LIA obligation `lo < x ∧ x < hi`
/// (UNSAT iff `hi <= lo`) against the Clean kernel.
///
/// Returns [`CertifyOutcome::Certified`] IFF the native reconstruction closed
/// in the kernel (`check_type(_, False)` passed), the payload carries
/// `trust_count == 0`, AND the term's transitive axiom residue is `⊆` the 3
/// Lean-core axioms. Any other outcome is FAIL-CLOSED (the caller keeps
/// `SmtBacked`). This never consults Carcara.
///
/// # Errors
///
/// Returns `Err(String)` only for an environment-construction failure (a
/// programmer/kernel-setup error), never for a certification failure — those
/// are represented as [`CertifyOutcome`] variants so the caller can act on them.
pub fn certify_lia_two_bound_unsat(lo: u64, hi: u64) -> Result<CertifyOutcome, String> {
    let env = int_arith_env()?;
    let (terms, map, proof, ctx) = build_lia_two_bound_proof(lo, hi, /* complete */ true);
    let negated_goal = negated_false_goal();

    match reconstruct_and_certify_ay_proof(&proof, &terms, &map, &negated_goal, &env, &ctx) {
        Ok(payload) => {
            // The kernel already re-checked the term to `False` (gate e) and
            // re-scanned for `trustedAy`/`trustedArith` (gate d ⇒ trust_count 0).
            // Independently confirm the FULL modulo-3 axiom residue is clean:
            // deserialize the certified term and walk its transitive closure.
            let term = clean_auto::bridge::ay_contract::deserialize_term(&payload.term_bytes)
                .map_err(|e| format!("deserialize certified term: {e:?}"))?;
            let residue = scan_axiom_residue(&term, &env);
            if residue.is_empty() {
                Ok(CertifyOutcome::Certified(payload))
            } else {
                Ok(CertifyOutcome::AxiomResidueImpure(residue))
            }
        }
        Err(not_certified) => Ok(CertifyOutcome::NotCertified(not_certified)),
    }
}

/// A two-bound LIA violation fragment `lo < x ∧ x < hi` recognized from a
/// Trust [`Formula`], normalized so `lo`/`hi` are the numeric bounds and `x` is
/// the shared free variable. UNSAT iff `hi <= lo`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LiaTwoBoundFragment {
    /// The shared free-variable name (the `∀x` the obligation quantifies over).
    pub var: String,
    /// Lower open bound: `lo < x`.
    pub lo: i128,
    /// Upper open bound: `x < hi`.
    pub hi: i128,
}

/// A single strict bound over one variable, oriented as `lo < var` or
/// `var < hi`, extracted from a comparison literal (normalizing `>`).
enum StrictBound {
    /// `c < x`  (a lower bound `x > c`).
    Lower { var: String, c: i128 },
    /// `x < c`  (an upper bound).
    Upper { var: String, c: i128 },
}

/// Match a single strict-inequality literal into a [`StrictBound`]. Handles
/// `Lt`/`Gt` in both `(var, const)` and `(const, var)` orientations.
fn match_strict_bound(f: &trust_types::Formula) -> Option<StrictBound> {
    use trust_types::Formula as F;
    let as_var = |g: &F| match g {
        F::Var(name, _) => Some(name.clone()),
        _ => None,
    };
    let as_int = |g: &F| match g {
        F::Int(v) => Some(*v),
        F::UInt(v) => i128::try_from(*v).ok(),
        _ => None,
    };
    match f {
        // x < c  ⇒ Upper;  c < x ⇒ Lower
        F::Lt(a, b) => match (as_var(a), as_int(b), as_int(a), as_var(b)) {
            (Some(var), Some(c), _, _) => Some(StrictBound::Upper { var, c }),
            (_, _, Some(c), Some(var)) => Some(StrictBound::Lower { var, c }),
            _ => None,
        },
        // x > c  ⇒ Lower;  c > x ⇒ Upper
        F::Gt(a, b) => match (as_var(a), as_int(b), as_int(a), as_var(b)) {
            (Some(var), Some(c), _, _) => Some(StrictBound::Lower { var, c }),
            (_, _, Some(c), Some(var)) => Some(StrictBound::Upper { var, c }),
            _ => None,
        },
        _ => None,
    }
}

/// Recognize the milestone-1 two-bound LIA fragment `lo < x ∧ x < hi` in a
/// Trust violation [`Formula`], in any conjunct order / operator orientation.
///
/// Returns `Some` only when the formula is EXACTLY two strict bounds over the
/// SAME variable that pin it from both sides (one lower, one upper). This is a
/// deliberately NARROW recognizer — the milestone-1 fragment, not general LIA.
pub fn recognize_lia_two_bound(formula: &trust_types::Formula) -> Option<LiaTwoBoundFragment> {
    use trust_types::Formula as F;
    let conjuncts: Vec<&F> = match formula {
        F::And(terms) if terms.len() == 2 => terms.iter().collect(),
        _ => return None,
    };
    let b0 = match_strict_bound(conjuncts[0])?;
    let b1 = match_strict_bound(conjuncts[1])?;
    match (b0, b1) {
        (StrictBound::Lower { var: v0, c: lo }, StrictBound::Upper { var: v1, c: hi })
        | (StrictBound::Upper { var: v1, c: hi }, StrictBound::Lower { var: v0, c: lo })
            if v0 == v1 =>
        {
            Some(LiaTwoBoundFragment { var: v0, lo, hi })
        }
        _ => None,
    }
}

/// Certify a Trust violation [`Formula`] IFF it is the milestone-1 two-bound
/// LIA fragment `lo < x ∧ x < hi` AND that fragment is UNSAT (`hi <= lo`).
///
/// This is the router-facing entry: given the SAME violation formula the
/// in-process ay backend asserted, decide whether the Clean kernel can natively
/// re-prove its unsatisfiability. Returns `None` when the formula is outside the
/// recognized fragment (so the caller keeps the honest `SmtBacked` verdict);
/// otherwise the [`CertifyOutcome`] (which is itself fail-closed).
///
/// Non-negative bounds only (the concrete-Int closer's `Int.ofNat` domain);
/// negative or `> i64`-magnitude bounds fall outside milestone 1 and return
/// `None` (fail-closed).
///
/// # Errors
///
/// Propagates an environment-construction failure from
/// [`certify_lia_two_bound_unsat`].
pub fn certify_lia_violation_formula(
    formula: &trust_types::Formula,
) -> Result<Option<CertifyOutcome>, String> {
    let Some(frag) = recognize_lia_two_bound(formula) else {
        return Ok(None);
    };
    // Only the UNSAT, non-negative-bound fragment is a milestone-1 candidate.
    // A satisfiable fragment (lo < hi) or negative/oversized bounds ⇒ decline
    // (fail-closed: the caller keeps SmtBacked).
    if frag.hi > frag.lo {
        return Ok(None);
    }
    let (Ok(lo), Ok(hi)) = (u64::try_from(frag.lo), u64::try_from(frag.hi)) else {
        return Ok(None);
    };
    Ok(Some(certify_lia_two_bound_unsat(lo, hi)?))
}

/// FAIL-CLOSED negative control: attempt to certify an INCOMPLETE proof of the
/// same obligation (the propositional skeleton does not derive the empty
/// clause). This MUST NOT certify — it is the wrong-proof control that proves
/// the honest pre-certification verdict survives a malformed refutation.
///
/// # Errors
///
/// Same as [`certify_lia_two_bound_unsat`].
pub fn certify_lia_two_bound_incomplete_control(
    lo: u64,
    hi: u64,
) -> Result<CertifyOutcome, String> {
    let env = int_arith_env()?;
    let (terms, map, proof, ctx) = build_lia_two_bound_proof(lo, hi, /* complete */ false);
    let negated_goal = negated_false_goal();

    match reconstruct_and_certify_ay_proof(&proof, &terms, &map, &negated_goal, &env, &ctx) {
        Ok(payload) => {
            let term = clean_auto::bridge::ay_contract::deserialize_term(&payload.term_bytes)
                .map_err(|e| format!("deserialize certified term: {e:?}"))?;
            let residue = scan_axiom_residue(&term, &env);
            if residue.is_empty() {
                Ok(CertifyOutcome::Certified(payload))
            } else {
                Ok(CertifyOutcome::AxiomResidueImpure(residue))
            }
        }
        Err(not_certified) => Ok(CertifyOutcome::NotCertified(not_certified)),
    }
}

// ─────────────────────────── MILESTONE 2 — BV multiplication ───────────────────
//
// Build a local Clean candidate for a `bvmul`-involving VC by re-checking the
// array-multiplier bit-blast refutation. This does not promote a live router
// verdict; transport and replay remain intentionally unwired.

/// A `bvmul`-involving equality VC recognized from a Trust [`Formula`],
/// normalized to the two [`clean_auto::bridge::ay_contract::BvExpr`] sides of the
/// equality whose disequality ay refutes. UNSAT iff the equality is a valid
/// bitvector identity.
pub struct BvMulEqFragment {
    /// The bit-blastable lhs of the equality.
    pub lhs: clean_auto::bridge::ay_contract::BvExpr,
    /// The bit-blastable rhs of the equality.
    pub rhs: clean_auto::bridge::ay_contract::BvExpr,
    /// True iff a `BvMul` node appears anywhere in either side (the milestone-2
    /// scope gate — a pure add/xor VC is out of scope here, handled elsewhere).
    pub involves_mul: bool,
}

/// Translate a Trust bitvector [`Formula`] into an ay
/// [`clean_auto::bridge::ay_contract::BvExpr`], tracking whether a `BvMul`
/// appears. Returns `None` for any node outside the bit-blastable fragment the
/// milestone-2 array-multiplier reconstruction covers (so the caller declines,
/// fail-closed).
fn formula_to_bvexpr(
    f: &trust_types::Formula,
) -> Option<(clean_auto::bridge::ay_contract::BvExpr, bool)> {
    formula_to_bvexpr_ops(f).map(|(e, ops)| (e, ops.mul))
}

/// Which bit-blastable ops a translated [`clean_auto::bridge::ay_contract::BvExpr`]
/// subtree contains. Used to scope the recognizers: milestone 2 gates on `mul`,
/// milestone 3 gates on `shift`. Both flags OR up through the recursion.
#[derive(Debug, Clone, Copy, Default)]
struct BvOpsSeen {
    /// A `BvMul` node appears somewhere in the subtree.
    mul: bool,
    /// A `BvShl` / `BvLShr` / `BvAShr` node appears somewhere in the subtree.
    shift: bool,
}

impl BvOpsSeen {
    fn or(self, other: Self) -> Self {
        Self { mul: self.mul || other.mul, shift: self.shift || other.shift }
    }
}

/// Translate a Trust bitvector [`Formula`] into an ay
/// [`clean_auto::bridge::ay_contract::BvExpr`], tracking which bit-blastable ops
/// (mul / shift) the subtree contains. Returns `None` for any node outside the
/// bit-blastable fragment the reflection covers (so the caller declines,
/// fail-closed).
///
/// The `BvExpr::{Shl, Lshr, Ashr}` arms are the milestone-3 addition; every other
/// arm is unchanged from milestone 2. NOTE: bitvector DIVISION (`BvUDiv`/`BvSDiv`)
/// is DELIBERATELY absent — ay's `BvExpr` fragment has no divider blaster, so a
/// div VC has no bit-blast refutation to reflect and stays out-of-fragment
/// (fail-closed → `None`); see [`recognize_bvdiv_out_of_fragment`].
fn formula_to_bvexpr_ops(
    f: &trust_types::Formula,
) -> Option<(clean_auto::bridge::ay_contract::BvExpr, BvOpsSeen)> {
    use clean_auto::bridge::ay_contract::BvExpr;
    use trust_types::{Formula as F, Sort};
    let none = BvOpsSeen::default();
    match f {
        F::Var(name, Sort::BitVec(w)) => Some((BvExpr::leaf(name, *w), none)),
        F::SymVar(sym, Sort::BitVec(w)) => Some((BvExpr::leaf(sym.as_str(), *w), none)),
        F::BitVec { value, width } => {
            // Two's-complement literal; BvExpr::const_val takes a u128 pattern.
            let bits = if *width >= 128 { u128::MAX } else { (1u128 << width) - 1 };
            let v = (*value as u128) & bits;
            Some((BvExpr::const_val(v, *width), none))
        }
        F::BvMul(a, b, _w) => {
            let (ea, oa) = formula_to_bvexpr_ops(a)?;
            let (eb, ob) = formula_to_bvexpr_ops(b)?;
            Some((
                BvExpr::Mul(Box::new(ea), Box::new(eb)),
                oa.or(ob).or(BvOpsSeen { mul: true, shift: false }),
            ))
        }
        F::BvAdd(a, b, _w) => {
            let (ea, oa) = formula_to_bvexpr_ops(a)?;
            let (eb, ob) = formula_to_bvexpr_ops(b)?;
            Some((BvExpr::Add(Box::new(ea), Box::new(eb)), oa.or(ob)))
        }
        // Milestone 3 — variable shifts (barrel shifter). `bvshl` / `bvlshr`
        // (zero-fill) / `bvashr` (sign-fill). Both operands share one width.
        F::BvShl(a, b, _w) => {
            let (ea, oa) = formula_to_bvexpr_ops(a)?;
            let (eb, ob) = formula_to_bvexpr_ops(b)?;
            Some((
                BvExpr::Shl(Box::new(ea), Box::new(eb)),
                oa.or(ob).or(BvOpsSeen { mul: false, shift: true }),
            ))
        }
        F::BvLShr(a, b, _w) => {
            let (ea, oa) = formula_to_bvexpr_ops(a)?;
            let (eb, ob) = formula_to_bvexpr_ops(b)?;
            Some((BvExpr::lshr(ea, eb), oa.or(ob).or(BvOpsSeen { mul: false, shift: true })))
        }
        F::BvAShr(a, b, _w) => {
            let (ea, oa) = formula_to_bvexpr_ops(a)?;
            let (eb, ob) = formula_to_bvexpr_ops(b)?;
            Some((BvExpr::ashr(ea, eb), oa.or(ob).or(BvOpsSeen { mul: false, shift: true })))
        }
        F::BvSub(a, b, _w) => {
            let (ea, oa) = formula_to_bvexpr_ops(a)?;
            let (eb, ob) = formula_to_bvexpr_ops(b)?;
            Some((BvExpr::Sub(Box::new(ea), Box::new(eb)), oa.or(ob)))
        }
        // Bitwise ops (per-bit gates, no carry). `BvOr` in particular is the RAW
        // identity wrapper the live M-POS gate emits around a shift/mul result
        // (`bvor(0, x)`), so translating it is what lets the router recognize the
        // real machine-output shape. All bit-blast to existing gate kinds the
        // op-agnostic reflection re-checks.
        F::BvOr(a, b, _w) => {
            let (ea, oa) = formula_to_bvexpr_ops(a)?;
            let (eb, ob) = formula_to_bvexpr_ops(b)?;
            Some((BvExpr::or(ea, eb), oa.or(ob)))
        }
        F::BvAnd(a, b, _w) => {
            let (ea, oa) = formula_to_bvexpr_ops(a)?;
            let (eb, ob) = formula_to_bvexpr_ops(b)?;
            Some((BvExpr::and(ea, eb), oa.or(ob)))
        }
        F::BvXor(a, b, _w) => {
            let (ea, oa) = formula_to_bvexpr_ops(a)?;
            let (eb, ob) = formula_to_bvexpr_ops(b)?;
            Some((BvExpr::xor(ea, eb), oa.or(ob)))
        }
        F::BvNot(a, _w) => {
            let (ea, oa) = formula_to_bvexpr_ops(a)?;
            Some((BvExpr::Not(Box::new(ea)), oa))
        }
        F::BvZeroExt(a, bits) => {
            let (ea, oa) = formula_to_bvexpr_ops(a)?;
            Some((BvExpr::zero_ext(ea, *bits), oa))
        }
        F::BvSignExt(a, bits) => {
            let (ea, oa) = formula_to_bvexpr_ops(a)?;
            Some((BvExpr::sign_ext(ea, *bits), oa))
        }
        F::BvExtract { inner, high, low } => {
            let (ei, oi) = formula_to_bvexpr_ops(inner)?;
            Some((BvExpr::extract(ei, *high, *low), oi))
        }
        // Any other node (DIVISION / concat / int-bv conversions / comparisons /
        // etc.) is outside the bit-blastable scope: decline (fail-closed).
        _ => None,
    }
}

/// The widest `BvMul` the local reconstruction lane will attempt. The
/// array-multiplier bit-blast is O(w²) gates and its kernel reflection re-check is
/// linear in the blast, so a WIDE recognized mul (e.g. 32/64-bit) would hang/OOM
/// the now-shipped verifier — the same hazard trust-cg-bridge's
/// M-POS gate caps with `MAX_RECHECKABLE_MUL_WIDTH = 8` (verify_output.rs). A wider
/// mul stays honestly `SmtBacked` (decline, never a wrong verdict). Availability
/// cap only — soundness is unaffected either way.
const MAX_CERTIFY_MUL_WIDTH: usize = 8;

/// The maximum width of any `BvMul` node in `f` (0 if none). Walks exactly the
/// bit-blastable fragment `formula_to_bvexpr_ops` translates (plus the `Eq` root);
/// a node outside it contributes no width — the translation declines it anyway.
fn max_bvmul_width(f: &trust_types::Formula) -> usize {
    use trust_types::Formula as F;
    let mut max = 0usize;
    let mut stack = vec![f];
    while let Some(node) = stack.pop() {
        match node {
            F::BvMul(a, b, w) => {
                max = max.max(*w as usize);
                stack.push(a);
                stack.push(b);
            }
            F::Eq(a, b)
            | F::BvAdd(a, b, _)
            | F::BvSub(a, b, _)
            | F::BvShl(a, b, _)
            | F::BvLShr(a, b, _)
            | F::BvAShr(a, b, _)
            | F::BvOr(a, b, _)
            | F::BvAnd(a, b, _)
            | F::BvXor(a, b, _) => {
                stack.push(a);
                stack.push(b);
            }
            F::Not(a) | F::BvNot(a, _) | F::BvZeroExt(a, _) | F::BvSignExt(a, _) => {
                stack.push(a);
            }
            F::BvExtract { inner, .. } => stack.push(inner),
            _ => {}
        }
    }
    max
}

/// Recognize a `bvmul`-involving equality VC in a Trust violation [`Formula`].
///
/// The violation formula that ay refutes is the DISEQUALITY `not(lhs == rhs)`
/// (unsatisfiable iff `lhs == rhs` is a valid bitvector identity). This accepts
/// exactly `Not(Eq(lhs, rhs))` where both sides translate into the bit-blastable
/// `BvExpr` fragment AND at least one side contains a `BvMul` (the milestone-2
/// scope) AND every `BvMul` is within [`MAX_CERTIFY_MUL_WIDTH`] (the tractability
/// cap for the shipped lane). Returns `None` otherwise (so the caller keeps
/// `SmtBacked`).
pub fn recognize_bvmul_eq(formula: &trust_types::Formula) -> Option<BvMulEqFragment> {
    use trust_types::Formula as F;
    let F::Not(inner) = formula else {
        return None;
    };
    let F::Eq(a, b) = inner.as_ref() else {
        return None;
    };
    // Tractability cap BEFORE translation: a wide mul's O(w²) blast would hang the
    // shipped verifier's reconstruction attempt — decline before doing the work.
    if max_bvmul_width(inner) > MAX_CERTIFY_MUL_WIDTH {
        return None;
    }
    let (lhs, ma) = formula_to_bvexpr(a)?;
    let (rhs, mb) = formula_to_bvexpr(b)?;
    let involves_mul = ma || mb;
    if !involves_mul {
        return None; // out of milestone-2 scope (no multiply).
    }
    Some(BvMulEqFragment { lhs, rhs, involves_mul })
}

/// Natively certify a Trust `bvmul` violation [`Formula`] IFF it is a recognized
/// `bvmul`-involving equality disequality `not(lhs == rhs)` that ay refutes.
///
/// This is the router-facing milestone-2 entry: given the SAME violation formula
/// the in-process ay backend asserted, decide whether the Clean kernel can
/// natively re-check ay's array-multiplier bit-blast refutation. Returns:
///   * `Ok(None)` — the formula is outside the recognized bvmul fragment (caller
///     keeps `SmtBacked`);
///   * `Ok(Some(true))` — kernel-CERTIFIED modulo 3 (`Unsat` re-checked,
///     `trust_count == 0`, axiom residue `⊆` the 3 Lean-core axioms);
///   * `Ok(Some(false))` — recognized but declined fail-closed (satisfiable /
///     kernel-reject / residual trust / impure residue).
///
/// # Errors
/// Propagates an environment-construction failure as `String`.
pub fn certify_bvmul_violation_formula(
    formula: &trust_types::Formula,
) -> Result<Option<bool>, String> {
    let Some(frag) = recognize_bvmul_eq(formula) else {
        return Ok(None);
    };
    // The native kernel reflection re-check reduces `checkRefutes <clauses>
    // <refutation>` by a DEEP recursion (linear in the ~hundreds of bit-blast
    // clauses / resolution steps of the array multiplier). That reduction
    // overflows a default (2 MB) thread stack (observed as SIGBUS), so run the
    // whole certification on a dedicated large-stack thread — the same convention
    // clean's own kernel-heavy tests use (`run_with_stack`). This is a robustness
    // wrapper, NOT a soundness relaxation: the kernel gates are unchanged.
    run_on_large_stack(move || {
        let env = clean_auto::bridge::ay_contract::bvmul_certify_env()?;
        match clean_auto::bridge::ay_contract::certify_bvmul_unsat(&env, &frag.lhs, &frag.rhs) {
            // A genuine, kernel-re-checked, foundational-residue Unsat term: the
            // clean-side composer already enforced trust_count == 0 and the
            // modulo-3 residue gate, so reaching Ok here IS the Certified seal.
            // RELEASE-MODE fail-closed re-check of that cross-submodule invariant
            // (do NOT rely on the clean pin alone — a `trust_count != 0` payload
            // declines to SmtBacked instead of promoting).
            Ok(certified) => Ok(Some(certified.payload.trust_count == 0)),
            // SAT / undecided / kernel-reject / impure residue ⇒ fail-closed decline.
            Err(_) => Ok(Some(false)),
        }
    })
}

// ─────────────────────────── MILESTONE 3 — BV shift ────────────────────────────
//
// Build a local Clean candidate for a `bvshl`/`bvlshr`/`bvashr`-involving VC by
// re-checking ay's barrel-shifter bit-blast refutation. This REUSES the
// milestone-2 OP-AGNOSTIC
// reflection (`certify_unsat_by_reflection` reflects the CNF resolution refutation,
// not the op), so the new work here is only the recognizer + wiring. Same
// fail-closed discipline as milestones 1/2. It does not promote a live router
// verdict; div (`bvudiv`/`bvsdiv`) stays
// out-of-fragment (ay has no divider blaster) — see `recognize_bvdiv_out_of_fragment`.

/// A `bvshift`-involving equality VC recognized from a Trust [`Formula`],
/// normalized to the two [`clean_auto::bridge::ay_contract::BvExpr`] sides of the
/// equality whose disequality ay refutes. UNSAT iff the equality is a valid
/// bitvector identity.
pub struct BvShiftEqFragment {
    /// The bit-blastable lhs of the equality.
    pub lhs: clean_auto::bridge::ay_contract::BvExpr,
    /// The bit-blastable rhs of the equality.
    pub rhs: clean_auto::bridge::ay_contract::BvExpr,
    /// True iff a `BvShl`/`BvLShr`/`BvAShr` node appears anywhere in either side
    /// (the milestone-3 scope gate).
    pub involves_shift: bool,
}

/// Recognize a `bvshift`-involving equality VC in a Trust violation [`Formula`].
///
/// The violation formula that ay refutes is the DISEQUALITY `not(lhs == rhs)`
/// (unsatisfiable iff `lhs == rhs` is a valid bitvector identity). This accepts
/// exactly `Not(Eq(lhs, rhs))` where both sides translate into the bit-blastable
/// `BvExpr` fragment AND at least one side contains a `BvShl`/`BvLShr`/`BvAShr`
/// (the milestone-3 scope). Returns `None` otherwise (so the caller keeps
/// `SmtBacked`).
pub fn recognize_bvshift_eq(formula: &trust_types::Formula) -> Option<BvShiftEqFragment> {
    use trust_types::Formula as F;
    let F::Not(inner) = formula else {
        return None;
    };
    let F::Eq(a, b) = inner.as_ref() else {
        return None;
    };
    let (lhs, oa) = formula_to_bvexpr_ops(a)?;
    let (rhs, ob) = formula_to_bvexpr_ops(b)?;
    let involves_shift = oa.shift || ob.shift;
    if !involves_shift {
        return None; // out of milestone-3 scope (no shift).
    }
    Some(BvShiftEqFragment { lhs, rhs, involves_shift })
}

/// Recognize a bitvector DIVISION VC (`bvudiv`/`bvsdiv`) so the router can report
/// it as an HONEST out-of-fragment decline rather than silently mis-classifying.
///
/// Returns `true` iff `formula` is a `Not(Eq(..))` whose sides mention a `BvUDiv`
/// or `BvSDiv` node. ay's `BvExpr` fragment has NO divider blaster (restoring /
/// non-restoring), so there is no bit-blast refutation to reflect: a div VC is
/// GENUINELY out-of-fragment and is DECLINED fail-closed (kept `SmtBacked`). This
/// recognizer NEVER certifies — it only surfaces the honest reason. Certifying
/// div is future work (needs a divider blaster in ay first).
#[must_use]
pub fn recognize_bvdiv_out_of_fragment(formula: &trust_types::Formula) -> bool {
    use trust_types::Formula as F;
    let F::Not(inner) = formula else {
        return false;
    };
    let F::Eq(a, b) = inner.as_ref() else {
        return false;
    };
    formula_mentions_div(a) || formula_mentions_div(b)
}

/// True iff `f` contains a `BvUDiv`/`BvSDiv` node anywhere in its subtree.
fn formula_mentions_div(f: &trust_types::Formula) -> bool {
    use trust_types::Formula as F;
    match f {
        F::BvUDiv(..) | F::BvSDiv(..) => true,
        F::BvMul(a, b, _)
        | F::BvAdd(a, b, _)
        | F::BvSub(a, b, _)
        | F::BvShl(a, b, _)
        | F::BvLShr(a, b, _)
        | F::BvAShr(a, b, _) => formula_mentions_div(a) || formula_mentions_div(b),
        F::BvZeroExt(a, _) | F::BvSignExt(a, _) => formula_mentions_div(a),
        F::BvExtract { inner, .. } => formula_mentions_div(inner),
        _ => false,
    }
}

/// Natively certify a Trust `bvshift` violation [`Formula`] IFF it is a recognized
/// `bvshift`-involving equality disequality `not(lhs == rhs)` that ay refutes.
///
/// This is the router-facing milestone-3 entry: given the SAME violation formula
/// the in-process ay backend asserted, decide whether the Clean kernel can natively
/// re-check ay's barrel-shifter bit-blast refutation, REUSING the op-agnostic
/// milestone-2 reflection. Returns:
///   * `Ok(None)` — the formula is outside the recognized bvshift fragment (caller
///     keeps `SmtBacked`);
///   * `Ok(Some(true))` — kernel-CERTIFIED modulo 3 (`Unsat` re-checked,
///     `trust_count == 0`, axiom residue `⊆` the 3 Lean-core axioms);
///   * `Ok(Some(false))` — recognized but declined fail-closed (satisfiable /
///     kernel-reject / residual trust / impure residue / oversized refutation
///     capped-decline).
///
/// # Errors
/// Propagates an environment-construction failure as `String`.
pub fn certify_bvshift_violation_formula(
    formula: &trust_types::Formula,
) -> Result<Option<bool>, String> {
    let Some(frag) = recognize_bvshift_eq(formula) else {
        return Ok(None);
    };
    // Same large-stack robustness wrapper as milestone 2: the deep native kernel
    // reflection reduction (linear in the barrel-shifter's clauses / resolution
    // steps) would overflow a default thread stack. This is a robustness wrapper,
    // NOT a soundness relaxation: the kernel gates are unchanged.
    run_on_large_stack(move || {
        let env = clean_auto::bridge::ay_contract::bvmul_certify_env()?;
        match clean_auto::bridge::ay_contract::certify_bvshift_unsat(&env, &frag.lhs, &frag.rhs) {
            // A genuine, kernel-re-checked, foundational-residue Unsat term: the
            // clean-side composer already enforced trust_count == 0 and the
            // modulo-3 residue gate, so reaching Ok here IS the Certified seal.
            // RELEASE-MODE fail-closed re-check of that cross-submodule invariant
            // (do NOT rely on the clean pin alone — a `trust_count != 0` payload
            // declines to SmtBacked instead of promoting).
            Ok(certified) => Ok(Some(certified.payload.trust_count == 0)),
            // SAT / undecided / kernel-reject / impure residue / oversized
            // refutation ⇒ fail-closed decline (keep SmtBacked).
            Err(_) => Ok(Some(false)),
        }
    })
}

/// Stack size for the kernel-reflection certification thread (256 MiB) — ample
/// for the array-multiplier bit-blast reduction, well above the default 2 MiB.
const BVMUL_CERTIFY_STACK_BYTES: usize = 256 * 1024 * 1024;

/// Run `f` on a dedicated thread with a large stack, returning its result. Used
/// so the deep native kernel reduction cannot overflow the caller's (default)
/// thread stack. A panic in `f` (e.g. a kernel invariant violation) is caught as
/// a fail-closed `Err` rather than aborting the router.
fn run_on_large_stack<F>(f: F) -> Result<Option<bool>, String>
where
    F: FnOnce() -> Result<Option<bool>, String> + Send + 'static,
{
    let handle = std::thread::Builder::new()
        .name("pcay-bvmul-certify".to_string())
        .stack_size(BVMUL_CERTIFY_STACK_BYTES)
        .spawn(f)
        .map_err(|e| format!("spawn certify thread: {e}"))?;
    match handle.join() {
        Ok(result) => result,
        // A panic inside the kernel re-check is FAIL-CLOSED: decline (keep
        // SmtBacked) rather than propagate the panic and never a false Certified.
        Err(_) => Ok(Some(false)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// MILESTONE 1 (positive): the roadmap's `x > 10 ∧ x < 5` QF_LIA UNSAT VC is
    /// kernel-CERTIFIED modulo 3, natively, with `trust_count == 0`. Its
    /// violation formula is `10 < x ∧ x < 5` (hi=5 <= lo=10 ⇒ UNSAT).
    #[test]
    fn x_gt10_lt5_is_kernel_certified_zero_trust() {
        let outcome = certify_lia_two_bound_unsat(10, 5).expect("env setup");
        match outcome {
            CertifyOutcome::Certified(payload) => {
                assert_eq!(
                    payload.trust_count, 0,
                    "milestone-1 LIA UNSAT must certify with ZERO trust in ay"
                );
                assert!(
                    !payload.term_bytes.is_empty(),
                    "Certified payload must carry the serialized kernel proof term"
                );
            }
            other => panic!(
                "x>10 && x<5 must be kernel-Certified via the native reconstruction, got {other:?}"
            ),
        }
    }

    /// The `Certified` seal's axiom residue is `⊆` the 3 Lean-core axioms: no
    /// `trustedAy`, no `trustedArith`, no domain axiom. (If the residue were
    /// impure, `certify_lia_two_bound_unsat` returns `AxiomResidueImpure`, not
    /// `Certified` — so reaching `Certified` already proves this, but assert the
    /// residue directly on the deserialized term for an explicit witness.)
    #[test]
    fn certified_term_axiom_residue_is_modulo_three() {
        let env = int_arith_env().expect("env");
        let (terms, map, proof, ctx) = build_lia_two_bound_proof(10, 5, true);
        let negated_goal = negated_false_goal();
        let payload =
            reconstruct_and_certify_ay_proof(&proof, &terms, &map, &negated_goal, &env, &ctx)
                .expect("must certify");
        let term = clean_auto::bridge::ay_contract::deserialize_term(&payload.term_bytes)
            .expect("deserialize");
        let residue = scan_axiom_residue(&term, &env);
        assert!(
            residue.is_empty(),
            "certified term must depend only on the 3 Lean-core axioms (modulo 3); \
             found non-foundational residue: {residue:?}"
        );
    }

    /// FAIL-CLOSED negative control: an INCOMPLETE proof (root not the empty
    /// clause) must NOT certify — the honest SmtBacked verdict survives.
    #[test]
    fn incomplete_proof_is_not_certified_fail_closed() {
        let outcome = certify_lia_two_bound_incomplete_control(10, 5).expect("env setup");
        assert!(
            !outcome.is_certified(),
            "a wrong/incomplete proof must FAIL-CLOSED (never Certified), got {outcome:?}"
        );
        // Specifically it is a reconstruction/certification failure, not an
        // axiom-residue impurity (there is no valid term to scan).
        assert!(
            matches!(outcome, CertifyOutcome::NotCertified(_)),
            "incomplete proof must surface as NotCertified, got {outcome:?}"
        );
    }

    /// A genuinely SATISFIABLE bound pair (`lo < x ∧ x < hi` with `lo < hi`,
    /// e.g. `2 < x ∧ x < 9` — satisfiable at x=5) is NOT UNSAT, so the
    /// two-bound chain cannot close to `False`: certification must fail-closed.
    /// This guards against a false-PROVE of a satisfiable obligation.
    #[test]
    fn satisfiable_bounds_do_not_certify() {
        let outcome = certify_lia_two_bound_unsat(2, 9).expect("env setup");
        assert!(
            !outcome.is_certified(),
            "a SATISFIABLE bound pair (2 < x < 9) must NOT be certified as UNSAT, got {outcome:?}"
        );
    }

    use trust_types::{Formula, Sort};

    /// The EXACT roadmap VC as a Trust `Formula`: `x > 10 ∧ x < 5`. The router
    /// recognizer + certifier lifts it to `Certified` via the Clean kernel.
    #[test]
    fn router_formula_x_gt10_lt5_is_certified() {
        let formula = Formula::And(vec![
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10))),
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(5))),
        ]);
        let frag = recognize_lia_two_bound(&formula).expect("must recognize the 2-bound fragment");
        assert_eq!(frag, LiaTwoBoundFragment { var: "x".into(), lo: 10, hi: 5 });

        let outcome = certify_lia_violation_formula(&formula)
            .expect("env setup")
            .expect("recognized UNSAT fragment must produce a CertifyOutcome");
        assert!(
            outcome.is_certified(),
            "x>10 && x<5 (as a Trust Formula) must be kernel-Certified, got {outcome:?}"
        );
    }

    /// A SATISFIABLE Trust formula (`x > 2 ∧ x < 9`) is declined by the router
    /// certifier (returns `None`) — the caller keeps SmtBacked. Never a
    /// false-PROVE.
    #[test]
    fn router_formula_satisfiable_is_declined() {
        let formula = Formula::And(vec![
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(2))),
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(9))),
        ]);
        // Recognized as a 2-bound fragment, but SAT (lo=2 < hi=9) ⇒ declined.
        assert!(recognize_lia_two_bound(&formula).is_some());
        let outcome = certify_lia_violation_formula(&formula).expect("env setup");
        assert!(
            outcome.is_none(),
            "a satisfiable fragment must be DECLINED (None), got {outcome:?}"
        );
    }

    /// A formula OUTSIDE the milestone-1 fragment (a single bound, or bounds
    /// over different variables) is not recognized ⇒ the certifier declines,
    /// keeping SmtBacked.
    #[test]
    fn router_formula_out_of_fragment_is_declined() {
        // Single bound.
        let one_bound =
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10)));
        assert!(recognize_lia_two_bound(&one_bound).is_none());
        assert!(certify_lia_violation_formula(&one_bound).expect("env").is_none());

        // Two bounds over DIFFERENT variables (x, y) — not the pin-from-both-
        // sides fragment.
        let two_vars = Formula::And(vec![
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10))),
            Formula::Lt(Box::new(Formula::Var("y".into(), Sort::Int)), Box::new(Formula::Int(5))),
        ]);
        assert!(recognize_lia_two_bound(&two_vars).is_none());
        assert!(certify_lia_violation_formula(&two_vars).expect("env").is_none());
    }

    // ─────────────────────── MILESTONE 2 — BV multiplication ────────────────────

    /// A bvmul leaf (`Var(BitVec)`).
    fn bv_var(name: &str, w: u32) -> Formula {
        Formula::Var(name.into(), Sort::BitVec(w))
    }

    /// The milestone-2 bvmul widening no-overflow VC as a Trust violation
    /// `Formula`: `not( extract(zero_ext(A*B, 8), 7, 0) == A*B )` at width 8. This
    /// is UNSAT (the widened readout fuses to the truncated product), so the
    /// router recognizer + certifier lifts it to Certified via the Clean kernel.
    fn bvmul_widening_violation(w: u32) -> Formula {
        let a = bv_var("A0", w);
        let b = bv_var("B0", w);
        let machine = Formula::BvExtract {
            inner: Box::new(Formula::BvZeroExt(
                Box::new(Formula::BvMul(Box::new(a.clone()), Box::new(b.clone()), w)),
                w,
            )),
            high: w - 1,
            low: 0,
        };
        let spec = Formula::BvMul(Box::new(a), Box::new(b), w);
        Formula::Not(Box::new(Formula::Eq(Box::new(machine), Box::new(spec))))
    }

    /// MILESTONE 2 (positive): the bvmul widening no-overflow VC (as a Trust
    /// `Formula`) is recognized AND kernel-CERTIFIED modulo 3 via the native
    /// array-multiplier bit-blast reflection. (Runs the ~20s width-8 kernel
    /// re-check.)
    #[test]
    fn router_bvmul_widening_is_certified() {
        let formula = bvmul_widening_violation(8);
        let frag = recognize_bvmul_eq(&formula).expect("must recognize the bvmul eq fragment");
        assert!(frag.involves_mul, "fragment must carry a BvMul");

        let outcome = certify_bvmul_violation_formula(&formula)
            .expect("env setup")
            .expect("recognized bvmul VC must produce a decision");
        assert!(
            outcome,
            "the bvmul widening no-overflow VC must be kernel-Certified (modulo 3), got {outcome}"
        );
    }

    /// TRACTABILITY CAP: a WIDE bvmul (width 32 > `MAX_CERTIFY_MUL_WIDTH`) is NOT
    /// recognized — the O(w²) array-multiplier blast would hang/OOM the shipped
    /// verifier's reconstruction attempt, so the lane declines up front
    /// (availability cap; soundness unaffected). The width-8 shape stays in.
    #[test]
    fn router_wide_bvmul_is_capped_out_of_fragment() {
        let wide = bvmul_widening_violation(32);
        assert!(
            recognize_bvmul_eq(&wide).is_none(),
            "a 32-bit bvmul must be capped out of the shipped reconstruction lane",
        );
        assert_eq!(
            certify_bvmul_violation_formula(&wide).expect("env setup"),
            None,
            "the capped-out wide mul must keep SmtBacked (Ok(None))",
        );
        assert!(
            recognize_bvmul_eq(&bvmul_widening_violation(8)).is_some(),
            "the width-8 shape must remain recognized",
        );
    }

    /// FAIL-CLOSED (never false-PROVE): a SATISFIABLE bvmul VC — `not(A*B == A+B)`
    /// is SAT (multiply != add) — is recognized but DECLINED (`Some(false)`), so
    /// the caller keeps SmtBacked. ay finds a model and never fabricates a proof.
    #[test]
    fn router_satisfiable_bvmul_is_declined() {
        let a = bv_var("A0", 8);
        let b = bv_var("B0", 8);
        let lhs = Formula::BvMul(Box::new(a.clone()), Box::new(b.clone()), 8);
        let rhs = Formula::BvAdd(Box::new(a), Box::new(b), 8);
        let formula = Formula::Not(Box::new(Formula::Eq(Box::new(lhs), Box::new(rhs))));
        // Recognized (involves mul), but SAT ⇒ declined.
        assert!(recognize_bvmul_eq(&formula).is_some());
        let outcome = certify_bvmul_violation_formula(&formula).expect("env setup");
        assert_eq!(
            outcome,
            Some(false),
            "a satisfiable bvmul VC must be DECLINED (Some(false)), never Certified"
        );
    }

    /// A bvmul-FREE VC (`not(A + B == B + A)`, a pure bvadd identity) is NOT
    /// recognized by the milestone-2 recognizer (no multiply) ⇒ the certifier
    /// declines (`None`), keeping SmtBacked. Guards the milestone-2 scope.
    #[test]
    fn router_non_mul_bv_is_out_of_fragment() {
        let a = bv_var("A0", 8);
        let b = bv_var("B0", 8);
        let lhs = Formula::BvAdd(Box::new(a.clone()), Box::new(b.clone()), 8);
        let rhs = Formula::BvAdd(Box::new(b), Box::new(a), 8);
        let formula = Formula::Not(Box::new(Formula::Eq(Box::new(lhs), Box::new(rhs))));
        assert!(
            recognize_bvmul_eq(&formula).is_none(),
            "a bvmul-free BV VC is out of the milestone-2 fragment"
        );
        assert!(
            certify_bvmul_violation_formula(&formula).expect("env").is_none(),
            "a bvmul-free BV VC must be declined (None)"
        );
    }

    /// A non-BV VC (the milestone-1 LIA shape) is not recognized by the bvmul
    /// recognizer ⇒ `None` (the two recognizers are disjoint).
    #[test]
    fn router_lia_formula_not_recognized_as_bvmul() {
        let formula = Formula::And(vec![
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10))),
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(5))),
        ]);
        assert!(recognize_bvmul_eq(&formula).is_none());
    }

    // ─────────────────────── MILESTONE 3 — BV shift ─────────────────────────────

    /// A `bvshl(V, S)` identity readout violation as a Trust `Formula`:
    /// `not( bvor(0, bvshl(V,S)) == bvshl(V,S) )` at width `w`. UNSAT (the wrapped
    /// readout fuses to the bare shift), so the router recognizer + certifier lifts
    /// it to Certified via the Clean kernel.
    fn bvshl_identity_violation(w: u32) -> Formula {
        let v = bv_var("V0", w);
        let s = bv_var("S0", w);
        let shift = Formula::BvShl(Box::new(v), Box::new(s), w);
        let machine = Formula::BvOr(
            Box::new(Formula::BitVec { value: 0, width: w }),
            Box::new(shift.clone()),
            w,
        );
        Formula::Not(Box::new(Formula::Eq(Box::new(machine), Box::new(shift))))
    }

    /// MILESTONE 3 (positive): the `bvshl` identity readout VC (as a Trust
    /// `Formula`, width 2 for a fast kernel re-check) is recognized AND
    /// kernel-CERTIFIED modulo 3 via the native barrel-shifter bit-blast reflection
    /// (the SAME op-agnostic reflection milestone 2 uses).
    #[test]
    fn router_bvshl_identity_is_certified() {
        let formula = bvshl_identity_violation(2);
        let frag = recognize_bvshift_eq(&formula).expect("must recognize the bvshift eq fragment");
        assert!(frag.involves_shift, "fragment must carry a BvShl/BvLShr/BvAShr");

        let outcome = certify_bvshift_violation_formula(&formula)
            .expect("env setup")
            .expect("recognized bvshift VC must produce a decision");
        assert!(
            outcome,
            "the bvshl identity VC must be kernel-Certified (modulo 3), got {outcome}"
        );
    }

    /// FAIL-CLOSED (never false-PROVE): a SATISFIABLE shift VC — the
    /// signed-vs-unsigned bug class `not( ashr(V,S) == lshr(V,S) )` is SAT — is
    /// recognized but DECLINED (`Some(false)`), so the caller keeps SmtBacked. ay
    /// finds a model and never fabricates a proof.
    #[test]
    fn router_satisfiable_ashr_vs_lshr_is_declined() {
        let v = bv_var("V0", 4);
        let s = bv_var("S0", 4);
        let lhs = Formula::BvAShr(Box::new(v.clone()), Box::new(s.clone()), 4);
        let rhs = Formula::BvLShr(Box::new(v), Box::new(s), 4);
        let formula = Formula::Not(Box::new(Formula::Eq(Box::new(lhs), Box::new(rhs))));
        // Recognized (involves shift), but SAT ⇒ declined.
        assert!(recognize_bvshift_eq(&formula).is_some());
        let outcome = certify_bvshift_violation_formula(&formula).expect("env setup");
        assert_eq!(
            outcome,
            Some(false),
            "a satisfiable ashr-vs-lshr shift VC must be DECLINED (Some(false)), never Certified"
        );
    }

    /// A shift-FREE VC (`not(A + B == B + A)`, a pure bvadd identity) is NOT
    /// recognized by the milestone-3 recognizer (no shift) ⇒ the certifier declines
    /// (`None`), keeping SmtBacked. Guards the milestone-3 scope.
    #[test]
    fn router_non_shift_bv_is_out_of_fragment() {
        let a = bv_var("A0", 8);
        let b = bv_var("B0", 8);
        let lhs = Formula::BvAdd(Box::new(a.clone()), Box::new(b.clone()), 8);
        let rhs = Formula::BvAdd(Box::new(b), Box::new(a), 8);
        let formula = Formula::Not(Box::new(Formula::Eq(Box::new(lhs), Box::new(rhs))));
        assert!(
            recognize_bvshift_eq(&formula).is_none(),
            "a shift-free BV VC is out of the milestone-3 fragment"
        );
        assert!(
            certify_bvshift_violation_formula(&formula).expect("env").is_none(),
            "a shift-free BV VC must be declined (None)"
        );
    }

    /// HONEST OUT-OF-FRAGMENT: a bitvector DIVISION VC (`bvudiv`/`bvsdiv`) is NOT
    /// recognized by the shift recognizer (returns `None`), because ay's `BvExpr`
    /// fragment has no divider blaster — there is no bit-blast refutation to
    /// reflect. `recognize_bvdiv_out_of_fragment` surfaces the honest reason. The
    /// caller keeps SmtBacked; div is never (falsely) certified. This is the
    /// documented fail-closed decline for div (certifying div is future work).
    #[test]
    fn router_bvdiv_is_out_of_fragment_declined() {
        let a = bv_var("A0", 8);
        let b = bv_var("B0", 8);
        // not( udiv(A,B) == udiv(A,B) ) — a would-be trivial identity, but div is
        // out-of-fragment regardless of (un)satisfiability.
        let lhs = Formula::BvUDiv(Box::new(a.clone()), Box::new(b.clone()), 8);
        let rhs = Formula::BvUDiv(Box::new(a), Box::new(b), 8);
        let formula = Formula::Not(Box::new(Formula::Eq(Box::new(lhs), Box::new(rhs))));

        assert!(
            recognize_bvdiv_out_of_fragment(&formula),
            "a bvudiv VC must be recognized AS a division (honest out-of-fragment reason)"
        );
        assert!(
            recognize_bvshift_eq(&formula).is_none(),
            "division is out of the shift fragment (no divider blaster in ay)"
        );
        assert!(recognize_bvmul_eq(&formula).is_none(), "division is out of the mul fragment too");
        assert!(
            certify_bvshift_violation_formula(&formula).expect("env").is_none(),
            "a bvudiv VC must be declined (None) — fail-closed, keep SmtBacked"
        );
    }

    /// A signed `bvsdiv` VC is likewise out-of-fragment (declined), NEVER certified.
    #[test]
    fn router_bvsdiv_is_out_of_fragment_declined() {
        let a = bv_var("A0", 8);
        let b = bv_var("B0", 8);
        let lhs = Formula::BvSDiv(Box::new(a.clone()), Box::new(b.clone()), 8);
        let rhs = Formula::BvSDiv(Box::new(a), Box::new(b), 8);
        let formula = Formula::Not(Box::new(Formula::Eq(Box::new(lhs), Box::new(rhs))));
        assert!(recognize_bvdiv_out_of_fragment(&formula));
        assert!(recognize_bvshift_eq(&formula).is_none());
        assert!(certify_bvshift_violation_formula(&formula).expect("env").is_none());
    }

    /// The three recognizers are disjoint: a bvshift VC is not recognized by the
    /// mul recognizer, and a non-shift VC is not recognized as div.
    #[test]
    fn router_shift_and_mul_and_div_recognizers_are_disjoint() {
        let shift = bvshl_identity_violation(4);
        assert!(recognize_bvshift_eq(&shift).is_some());
        assert!(recognize_bvmul_eq(&shift).is_none());
        assert!(!recognize_bvdiv_out_of_fragment(&shift));
    }
}

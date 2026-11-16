// ignore-tidy-file-filelength -- pre-existing size, recorded 2026-10-17; do not grow casually
//! The REAL-valued (QF_LRA) linear refutation lane.
//!
//! An infeasible conjunction of linear order atoms over [`Sort::Real`]
//! variables with exact-rational [`Formula::Rat`] literals is refuted NATIVELY —
//! an exact-rational Farkas search (closed rows, proportional pairs, interval
//! bound propagation, then a Phase-1 simplex under Bland's rule on the Motzkin
//! dual LP whose witness is re-verified before use, then greedy
//! Fourier–Motzkin as the last fallback) finds multipliers, and the
//! kernel term replays the weighted combination over the clean kernel's
//! quotient `Rat` (`Rat.mul_le_mul_of_nonneg_left` scaling, `Rat.sub_nonneg_of_le`
//! per row, `Rat.add_le_add` summation, a ring normalizer that reduces each
//! row's `Bᵢ − Aᵢ` and then the running sum to canonical linear form, and the
//! definitional `Int.NonNeg` closer on the false residual `0 ≤ K` / `0 < K`).
//! ay cross-checks the SAME hypotheses in `QF_LRA` (verdict only), and the
//! clean kernel re-checks the term — the de Bruijn criterion, unchanged.
//!
//! ORDER OF WORK. The deterministic, budgeted search runs FIRST, and alone:
//! the cheap witnesses, then the exact-rational simplex — complete for every
//! system inside its caps, so a Phase-1 that COMPLETES with a positive optimum
//! is an exact [`SimplexSearch::NoWitness`] verdict that ENDS the search;
//! greedy Fourier–Motzkin runs only after a cap/meter decline. A satisfiable
//! pool therefore declines in the simplex's own milliseconds with no solver
//! consulted. A witness is then replayed, the term passes the codec gate, and
//! the finish tail asks ay ONCE, under [`AyCrossCheck::Required`], over the
//! identical hypotheses (defense in depth — the same tail every lane runs).
//! ay is consulted only for a pool that already carries a verified witness,
//! and it never holds `ay_exec_lock` for a SAT pool. Neither answer is ever
//! proof: only the kernel's `False` is.
//!
//! RETIRED: an ay PRE-SOLVE before the search. It was measured before the
//! simplex existed, when a dense 12-variable SAT pool ran Fourier–Motzkin to
//! its row cap (~0.2–1 s in debug) and ay's `Sat` saved that. With the
//! simplex, the whole search on the widest admitted pools (dense 32 variables
//! × 64 rows) costs ≤ 5.7 s in debug, while the pre-solve on those pools cost
//! 32–111 s (`Unsat` or `Abstained`) under the 90 s wall-clock
//! `AY_DIRECT_SOLVE_TIMEOUT_MS` deadline — so a dense UNSAT pool's outcome
//! depended on machine speed (a lapsed deadline → `Abstained` → decline),
//! although `recheck_cleancic` regenerates the certificate and byte-compares.
//! Its removal moves no certificate byte: the pre-solve produced no artifact.
//!
//! WHY A SEPARATE LANE. The theorem the Int lane's kernel term proves is
//! INTEGER infeasibility (`tighten_strict_int_bounds`, `x<c ⟹ x≤c−1`, the
//! `Int.*` lemma vocabulary). `2x ≥ 1 ∧ 2x ≤ 1` and `0 < x ∧ x < 1` are
//! integer-infeasible but real-FEASIBLE, so an Int-encoded certificate of a
//! real-valued system (a ny-cert Farkas witness over network activations) is a
//! FALSE certificate. Here every variable is a kernel `Rat` skolem, every
//! literal a `Rat.mk` term, strict rows stay strict (one strict row is kept
//! strict so the residual is `0 < K` with `K ≤ 0`, never weakened away), and
//! the kernel-checked theorem is genuinely "the rational system is infeasible"
//! — exact for linear systems with rational data, since such a system is
//! ℝ-feasible iff ℚ-feasible.
//!
//! WHY NOT ay → CIC RECONSTRUCTION. clean-auto's Real reconstruction lane is
//! built on `Real.*` `Declaration::Axiom`s, which [`proof_axiom_closure_is_clean`]
//! rightly rejects. Every lemma this lane names is a kernel-checked
//! `Declaration::Theorem` whose axiom closure is a subset of the foundational
//! `Quot*`/`propext` residue.
//!
//! INERTNESS. The lane returns `None` before any work unless some order atom
//! carries a `Real` variable or a `Rat` literal, and it refuses a pool whose
//! order atoms mix `Int`-sorted leaves with `Real` ones. Int obligations are
//! untouched: every existing Int certificate keeps its exact bytes.
//!
//! SOUNDNESS. Same ∧-elimination argument as [`collect_supported_atoms`]:
//! conjuncts outside the fragment are DROPPED (weakening), so a satisfiable
//! violation stays satisfiable, no Farkas witness exists, ay answers `Sat`, and
//! nothing is minted. A minted term is fully kernel-checked (twice — once
//! directly, once after the payload round-trip) under the closure audit.
//!
//! CERTIFICATE SIZE. Every `Eq.subst` rewrite step copies its motive, so the
//! term grows with (rewrite steps) × (motive size). The normalizer therefore
//! keeps motives SMALL: each row's difference `Bᵢ − Aᵢ` is normalized IN PLACE
//! on its own fact `0 ≤ Bᵢ − Aᵢ` (motive over that row's term only), rows are
//! then combined one at a time with `Rat.add_le_add` and the running canonical
//! sum is merged in place (motive over the running sum only). The node count is
//! O(rows × (row size + variables)²) with a small constant instead of the
//! previous O(rows² × ...): measured on the box system `0 ≤ vᵢ ≤ 1 ∧ Σvᵢ ≥
//! n+1` (see `box_systems_certify_within_the_codec_limit`), n=10 went from
//! 1.38 MB to 0.22 MB, n=15 from 3.31 MB to 0.39 MB, and n=20/25 from
//! "exceeds the proof codec's 2,000,000-node limit" to 0.61 MB / 0.88 MB
//! (364K codec nodes at n=25).
//!
//! RESOURCE DISCIPLINE. The replay and the kernel check recurse to the depth
//! of the proof term, so the lane's heavy work (Farkas search, replay, codec
//! gate, ay cross-check, kernel re-check) runs on a dedicated
//! [`REAL_LANE_STACK_BYTES`] thread (the 256 MiB precedent of the router's
//! `bvmul` lane); a panic there is a clean `None`. Independently, explicit caps
//! ([`MAX_REAL_ATOMS`], [`MAX_TERM_DEPTH`], [`MAX_ROW_VARS`],
//! [`MAX_CHAIN_STEPS`], [`NODE_BUDGET`]) decline before any construction could
//! grow past the codec's node/depth limits, and the codec itself is run on the
//! term BEFORE the kernel check so nothing the consumer would refuse is ever
//! kernel-checked.

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::expr::{BigNat, ExprKind};
use clean_kernel::name::{Name, NameInner};
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, FVarId, Level};
use num_bigint::{BigInt, BigUint, Sign};
use num_rational::BigRational;
use trust_types::{Formula, Sort};

use super::{
    Atom, AyCrossCheck, Carrier, HYP_FVAR_BASE, Hyp, ObligationIdentity, atom_identity_key,
    base_env, const_app, encoded_var_name, eq_refl_int, finish_certificate_carrier, normalize_atom,
    serialize_term,
};

type Q = BigRational;

/// Structural budget: more kept atoms than this and the lane declines before
/// any solver or kernel work.
const MAX_REAL_ATOMS: usize = 64;

/// Maximum nesting depth of one side of a kept atom (`Add`/`Sub`/`Neg`/`Mul`
/// levels). Deeper terms decline before the parser recurses into them.
const MAX_TERM_DEPTH: usize = 64;

/// Maximum number of DISTINCT variables one kept atom may mention. Wider rows
/// decline. Sized from the worst shape at the cap — two fully dense rows over
/// exactly this many variables (`Σ ≥ n+1 ∧ Σ ≤ n`), whose two normalizations
/// plus one full merge are each O(n²) nodes: measured ≈ 2.2M codec nodes at
/// 48 (over the codec's limit), so 32 keeps that shape near 1M with the
/// 64-atom box systems (`n = 31`) well inside the budget too.
const MAX_ROW_VARS: usize = 32;

/// Maximum number of term nodes (`Var`/`Lit`/`Add`/`Sub`/`Neg`/`Mul`) on one
/// side of a kept atom. Bounds the normalizer's recursion (a left-nested sum
/// is rotated right one node at a time) independently of the depth cap.
const MAX_ROW_NODES: usize = 512;

/// Maximum number of `Eq.subst` steps nested in ONE proof spine. Each step
/// nests the previous proof one level deeper, and the proof codec refuses a
/// term deeper than 4,096; this keeps every spine — the accumulated sum's
/// included — comfortably below it.
const MAX_CHAIN_STEPS: usize = 3000;

/// Node budget for the replay term, counted the way the proof codec counts
/// (expression nodes plus name/level/literal nodes). The codec's own limit is
/// 2,000,000; this declines the construction early instead of building a term
/// the consumer would refuse.
const NODE_BUDGET: usize = 1_500_000;

/// Stack for the lane's heavy work (see the module banner).
const REAL_LANE_STACK_BYTES: usize = 256 * 1024 * 1024;

// ---------------------------------------------------------------------------
// Exact rationals.
// ---------------------------------------------------------------------------

fn q_from_int(n: i64) -> Q {
    Q::from_integer(BigInt::from(n))
}

fn q_is_zero(q: &Q) -> bool {
    q.numer().sign() == Sign::NoSign
}

fn q_is_neg(q: &Q) -> bool {
    q.numer().sign() == Sign::Minus
}

fn q_is_pos(q: &Q) -> bool {
    q.numer().sign() == Sign::Plus
}

/// Parse a [`Formula::Rat`] literal into a REDUCED rational (`Ratio::new`
/// divides out the gcd and puts the sign on the numerator), so two spellings of
/// one value never yield two distinct kernel literals. The contract's `RatLit`
/// already enforces canonical decimal syntax; the sign/zero checks here are
/// belt and braces.
fn parse_rat_lit(f: &Formula) -> Option<Q> {
    let (num, den) = f.rat_parts()?;
    let num: BigInt = num.parse().ok()?;
    let den: BigInt = den.parse().ok()?;
    if den.sign() != Sign::Plus {
        return None;
    }
    Some(Q::new(num, den))
}

// ---------------------------------------------------------------------------
// Kernel term builders over `Rat`.
// ---------------------------------------------------------------------------

fn k(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn lvl1() -> Level {
    Level::succ(Level::zero())
}

pub(crate) fn rat_ty() -> Expr {
    k("Rat")
}

/// Arbitrary-precision `Nat` literal (little-endian limbs, the convention
/// `BigNat::from_limbs` and `BigUint::to_u64_digits` share).
fn nat_big(u: &BigUint) -> Expr {
    Expr::bignat_lit(BigNat::from_limbs(u.to_u64_digits()))
}

/// `Int.ofNat n` / `Int.negSucc (|n|-1)` for an arbitrary-precision integer.
fn int_big(n: &BigInt) -> Expr {
    if n.sign() == Sign::Minus {
        Expr::app(k("Int.negSucc"), nat_big(&(n.magnitude() - BigUint::from(1u32))))
    } else {
        Expr::app(k("Int.ofNat"), nat_big(n.magnitude()))
    }
}

/// The rational literal `Rat.mk n d` (`d ≥ 1`, reduced). `0` is `Rat.mk 0 1`
/// and `1` is `Rat.mk 1 1`, definitionally equal to `Rat.zero` / `Rat.one`.
fn rat_lit(q: &Q) -> Expr {
    const_app("Rat.mk", [int_big(q.numer()), nat_big(q.denom().magnitude())])
}

fn rat_add(a: Expr, b: Expr) -> Expr {
    const_app("Rat.add", [a, b])
}

fn rat_mul(a: Expr, b: Expr) -> Expr {
    const_app("Rat.mul", [a, b])
}

fn rat_neg(a: Expr) -> Expr {
    const_app("Rat.neg", [a])
}

fn rat_sub(a: Expr, b: Expr) -> Expr {
    const_app("Rat.sub", [a, b])
}

fn rat_le(a: Expr, b: Expr) -> Expr {
    const_app("Rat.le", [a, b])
}

fn rat_lt(a: Expr, b: Expr) -> Expr {
    const_app("Rat.lt", [a, b])
}

fn var_expr(name: &str) -> Expr {
    k(&encoded_var_name(name))
}

/// `@Eq.{1} Rat a b`
fn eq_rat(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq"), vec![lvl1()]), [rat_ty(), a, b])
}

/// `@Eq.refl.{1} Rat a`
fn eq_refl_rat(a: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq.refl"), vec![lvl1()]), [rat_ty(), a])
}

/// `@Eq.symm.{1} Rat a b h`
fn eq_symm_rat(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq.symm"), vec![lvl1()]), [rat_ty(), a, b, h])
}

/// `@Eq.subst.{1} Rat motive a b (h : Eq a b) (m : motive a) : motive b`
fn eq_subst_rat(motive: Expr, a: Expr, b: Expr, h: Expr, m: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.subst"), vec![lvl1()]),
        [rat_ty(), motive, a, b, h, m],
    )
}

/// `@Int.NonNeg.mk n : Int.NonNeg (Int.ofNat n)` — the definitional witness of
/// a true closed `Rat.le`/`Rat.lt` (its type reduces, through `Quot.lift` and
/// the native `Int` literal reducers, to the cross-product `Int.NonNeg`).
fn nonneg_mk_big(n: &BigUint) -> Expr {
    Expr::app(k("Int.NonNeg.mk"), nat_big(n))
}

/// Node count of a kernel expression the way the proof codec counts it: one
/// per expression node, one per name component (plus the anonymous root), one
/// per universe-level node, one per literal (plus its limbs when big).
/// Iterative, so a deep term costs no stack.
fn expr_nodes(root: &Expr) -> usize {
    fn name_nodes(name: &Name) -> usize {
        let mut n = 1;
        let mut cur = name;
        while let NameInner::Str(parent, _) | NameInner::Num(parent, _) = cur.inner() {
            n += 1;
            cur = parent;
        }
        n
    }
    fn level_nodes(level: &Level) -> usize {
        let mut n = 0;
        let mut pending = vec![level];
        while let Some(l) = pending.pop() {
            n += 1;
            match l {
                Level::Zero => {}
                Level::Succ(inner) => pending.push(inner),
                Level::Max(a, b) | Level::IMax(a, b) => {
                    pending.push(a);
                    pending.push(b);
                }
                Level::Param(name) => n += name_nodes(name),
            }
        }
        n
    }
    let mut n = 0;
    let mut pending = vec![root];
    while let Some(e) = pending.pop() {
        n += 1;
        match e.kind() {
            ExprKind::Const(name, levels) => {
                n += name_nodes(name) + levels.iter().map(level_nodes).sum::<usize>();
            }
            ExprKind::App(f, a) => {
                pending.push(f);
                pending.push(a);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                pending.push(ty);
                pending.push(body);
            }
            ExprKind::Sort(level) => n += level_nodes(level),
            ExprKind::Lit(_) => n += 2,
            _ => {}
        }
    }
    n
}

// ---------------------------------------------------------------------------
// The linear term fragment (mirrors the kernel encoding one-to-one).
// ---------------------------------------------------------------------------

/// A supported real-valued linear term. Built from a [`Formula`] by
/// [`RTerm::from_formula`]; rendered to the kernel by [`RTerm::to_kernel`] and
/// to SMT-LIB by [`RTerm::to_smt`]. The normalizer works on this tree so the
/// kernel expression it rewrites is EXACTLY the one the hypotheses state.
#[derive(Clone, Debug, PartialEq, Eq)]
enum RTerm {
    Var(String),
    Lit(Q),
    Add(Box<RTerm>, Box<RTerm>),
    Sub(Box<RTerm>, Box<RTerm>),
    Neg(Box<RTerm>),
    /// Linear product: at least one operand is a literal.
    Mul(Box<RTerm>, Box<RTerm>),
}

impl RTerm {
    /// `None` outside the fragment: an `Int`-sorted leaf, a non-`Real` variable,
    /// a product of two non-literals, any other operator, a term nested deeper
    /// than [`MAX_TERM_DEPTH`], or one with more than [`MAX_ROW_NODES`] nodes.
    fn from_formula(f: &Formula) -> Option<RTerm> {
        let mut nodes = 0usize;
        Self::parse(f, 0, &mut nodes)
    }

    fn parse(f: &Formula, depth: usize, nodes: &mut usize) -> Option<RTerm> {
        if depth > MAX_TERM_DEPTH {
            return None;
        }
        *nodes += 1;
        if *nodes > MAX_ROW_NODES {
            return None;
        }
        let next = depth + 1;
        Some(match f {
            Formula::Var(name, Sort::Real) => RTerm::Var(name.clone()),
            Formula::SymVar(sym, Sort::Real) => RTerm::Var(sym.as_str().to_string()),
            Formula::Rat(_) => RTerm::Lit(parse_rat_lit(f)?),
            Formula::Add(a, b) => RTerm::Add(
                Box::new(Self::parse(a, next, nodes)?),
                Box::new(Self::parse(b, next, nodes)?),
            ),
            Formula::Sub(a, b) => RTerm::Sub(
                Box::new(Self::parse(a, next, nodes)?),
                Box::new(Self::parse(b, next, nodes)?),
            ),
            Formula::Neg(a) => RTerm::Neg(Box::new(Self::parse(a, next, nodes)?)),
            Formula::Mul(a, b) => {
                let (ta, tb) = (Self::parse(a, next, nodes)?, Self::parse(b, next, nodes)?);
                if !matches!(ta, RTerm::Lit(_)) && !matches!(tb, RTerm::Lit(_)) {
                    return None;
                }
                RTerm::Mul(Box::new(ta), Box::new(tb))
            }
            _ => return None,
        })
    }

    /// Every variable LEAF of the term — including one whose net coefficient
    /// cancels (`x − x`, `0·x`): the SMT and kernel hypotheses spell it, so it
    /// must be declared. Iterative.
    fn collect_vars(&self, out: &mut BTreeSet<String>) {
        let mut pending = vec![self];
        while let Some(t) = pending.pop() {
            match t {
                RTerm::Var(x) => {
                    out.insert(x.clone());
                }
                RTerm::Lit(_) => {}
                RTerm::Add(a, b) | RTerm::Sub(a, b) | RTerm::Mul(a, b) => {
                    pending.push(a);
                    pending.push(b);
                }
                RTerm::Neg(a) => pending.push(a),
            }
        }
    }

    fn to_kernel(&self) -> Expr {
        match self {
            RTerm::Var(x) => var_expr(x),
            RTerm::Lit(q) => rat_lit(q),
            RTerm::Add(a, b) => rat_add(a.to_kernel(), b.to_kernel()),
            RTerm::Sub(a, b) => rat_sub(a.to_kernel(), b.to_kernel()),
            RTerm::Neg(a) => rat_neg(a.to_kernel()),
            RTerm::Mul(a, b) => rat_mul(a.to_kernel(), b.to_kernel()),
        }
    }

    /// SMT-LIB2 over `Real`. Literals use the spelling ay's text backend was
    /// measured to accept in `QF_LRA`: `n`, `(- n)`, `(/ n d)`, `(/ (- n) d)`.
    fn to_smt(&self) -> String {
        match self {
            RTerm::Var(x) => encoded_var_name(x),
            RTerm::Lit(q) => rat_smt(q),
            RTerm::Add(a, b) => format!("(+ {} {})", a.to_smt(), b.to_smt()),
            RTerm::Sub(a, b) => format!("(- {} {})", a.to_smt(), b.to_smt()),
            RTerm::Neg(a) => format!("(- {})", a.to_smt()),
            RTerm::Mul(a, b) => format!("(* {} {})", a.to_smt(), b.to_smt()),
        }
    }

    /// The exact linear form `Σ cᵢ·xᵢ + c`.
    fn linform(&self) -> RLin {
        match self {
            RTerm::Var(x) => {
                RLin { terms: BTreeMap::from([(x.clone(), q_from_int(1))]), c: q_from_int(0) }
            }
            RTerm::Lit(q) => RLin { terms: BTreeMap::new(), c: q.clone() },
            RTerm::Add(a, b) => a.linform().add(&b.linform()),
            RTerm::Sub(a, b) => a.linform().add(&b.linform().scale(&q_from_int(-1))),
            RTerm::Neg(a) => a.linform().scale(&q_from_int(-1)),
            RTerm::Mul(a, b) => match (a.as_ref(), b.as_ref()) {
                (RTerm::Lit(c), t) | (t, RTerm::Lit(c)) => t.linform().scale(c),
                _ => unreachable!("RTerm::Mul always carries a literal operand"),
            },
        }
    }
}

fn int_smt(n: &BigInt) -> String {
    if n.sign() == Sign::Minus { format!("(- {})", n.magnitude()) } else { n.to_string() }
}

fn rat_smt(q: &Q) -> String {
    if q.denom() == &BigInt::from(1) {
        int_smt(q.numer())
    } else {
        format!("(/ {} {})", int_smt(q.numer()), q.denom())
    }
}

/// A linear form with exact-rational coefficients (zero coefficients dropped).
#[derive(Clone, Debug)]
struct RLin {
    terms: BTreeMap<String, Q>,
    c: Q,
}

impl RLin {
    fn add(&self, other: &RLin) -> RLin {
        let mut terms = self.terms.clone();
        for (x, c) in &other.terms {
            let v = terms.get(x).cloned().unwrap_or_else(|| q_from_int(0)) + c;
            if q_is_zero(&v) {
                terms.remove(x);
            } else {
                terms.insert(x.clone(), v);
            }
        }
        RLin { terms, c: &self.c + &other.c }
    }

    fn scale(&self, s: &Q) -> RLin {
        if q_is_zero(s) {
            return RLin { terms: BTreeMap::new(), c: q_from_int(0) };
        }
        RLin { terms: self.terms.iter().map(|(x, c)| (x.clone(), c * s)).collect(), c: &self.c * s }
    }
}

// ---------------------------------------------------------------------------
// Fragment collection (the Real twin of `collect_supported_atoms`).
// ---------------------------------------------------------------------------

/// One kept order atom with both sides already parsed into the fragment.
struct RealAtom<'a> {
    atom: Atom<'a>,
    lhs: RTerm,
    rhs: RTerm,
    /// `a < b` (true) vs `a ≤ b` (false).
    strict: bool,
}

/// Iterative leaf search (a hostile formula can nest arbitrarily deep).
fn has_leaf(f: &Formula, pred: &impl Fn(&Formula) -> bool) -> bool {
    let mut pending = vec![f];
    while let Some(cur) = pending.pop() {
        if pred(cur) {
            return true;
        }
        trust_types::for_each_formula_child(cur, |c| pending.push(c));
    }
    false
}

fn is_int_leaf(f: &Formula) -> bool {
    matches!(
        f,
        Formula::Var(_, Sort::Int)
            | Formula::SymVar(_, Sort::Int)
            | Formula::Int(_)
            | Formula::UInt(_)
    )
}

fn is_real_leaf(f: &Formula) -> bool {
    matches!(f, Formula::Var(_, Sort::Real) | Formula::SymVar(_, Sort::Real) | Formula::Rat(_))
}

/// Keep the conjuncts inside the supported linear-REAL atom fragment. Returns
/// `None` — the lane is inert — unless at least one order atom carries a `Real`
/// leaf, and refuses (`None`) a pool whose order atoms also carry an `Int` leaf
/// anywhere (an Int obligation, or a mixed one, is never this lane's). Atoms are
/// deduplicated by structural identity exactly as the Int lane does. The
/// variable set is collected from the TERM STRUCTURE of every kept atom, so a
/// variable whose net coefficient cancels is still declared. An atom deeper
/// than [`MAX_TERM_DEPTH`] is outside the fragment (dropped, like any other
/// unsupported conjunct); an atom wider than [`MAX_ROW_VARS`] makes the whole
/// lane decline.
fn collect_real_atoms<'a>(
    conjuncts: &[&'a Formula],
) -> Option<(Vec<RealAtom<'a>>, BTreeSet<String>)> {
    let mut saw_real = false;
    let mut saw_int = false;
    let mut kept: Vec<RealAtom<'a>> = Vec::new();
    let mut kept_keys: Vec<(bool, &'a Formula, &'a Formula)> = Vec::new();
    let mut var_names: BTreeSet<String> = BTreeSet::new();
    for &c in conjuncts {
        let Some(normalized) = normalize_atom(c) else {
            continue;
        };
        let real = has_leaf(c, &is_real_leaf);
        let int = has_leaf(c, &is_int_leaf);
        saw_real |= real;
        saw_int |= int;
        if !real || int {
            continue;
        }
        // Every side of every resulting atom must parse; a conjunct outside the
        // linear fragment is dropped (weakening — sound for a refutation).
        let mut parsed: Vec<RealAtom<'a>> = Vec::new();
        let mut in_fragment = true;
        for atom in normalized {
            let (a, b, strict) = match atom {
                Atom::Lt(a, b) => (a, b, true),
                Atom::Le(a, b) => (a, b, false),
            };
            let (Some(lhs), Some(rhs)) = (RTerm::from_formula(a), RTerm::from_formula(b)) else {
                in_fragment = false;
                break;
            };
            parsed.push(RealAtom { atom, lhs, rhs, strict });
        }
        if !in_fragment {
            continue;
        }
        for ra in parsed {
            let key = atom_identity_key(&ra.atom);
            if kept_keys.iter().any(|kk| kk.0 == key.0 && kk.1 == key.1 && kk.2 == key.2) {
                continue;
            }
            let mut row_vars = BTreeSet::new();
            ra.lhs.collect_vars(&mut row_vars);
            ra.rhs.collect_vars(&mut row_vars);
            if row_vars.len() > MAX_ROW_VARS {
                return None;
            }
            var_names.extend(row_vars);
            kept_keys.push(key);
            kept.push(ra);
        }
    }
    if !saw_real || saw_int || kept.is_empty() {
        return None;
    }
    Some((kept, var_names))
}

/// The canonical hypothesis list: one [`Hyp`] per kept atom, fvars from
/// [`HYP_FVAR_BASE`], names `h_{i}`, SMT over `Real`, kernel props over `Rat`
/// (bare `Rat.lt` / `Rat.le`, definitionally the `instLTRat`/`instLERat` forms
/// the lemmas are stated in). Producer and consumer build the IDENTICAL list.
fn real_hyps_from_atoms(atoms: &[RealAtom<'_>]) -> Vec<Hyp> {
    atoms
        .iter()
        .enumerate()
        .map(|(i, ra)| {
            let (op, rel): (&str, fn(Expr, Expr) -> Expr) =
                if ra.strict { ("<", rat_lt) } else { ("<=", rat_le) };
            Hyp {
                smt: format!("({op} {} {})", ra.lhs.to_smt(), ra.rhs.to_smt()),
                prop: rel(ra.lhs.to_kernel(), ra.rhs.to_kernel()),
                fvar: FVarId::new(HYP_FVAR_BASE + i as u64),
                name: format!("h_{i}"),
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// The Farkas witness: exact-rational search.
// ---------------------------------------------------------------------------

/// A constant residual `cst` (weak: `0 ≤ cst`; strict: `0 < cst`) is false.
fn residual_is_false(cst: &Q, strict: bool) -> bool {
    if strict { !q_is_pos(cst) } else { q_is_neg(cst) }
}

/// Non-negative rational Farkas witness over rows `0 ≤ rowᵢ` (weak) / `0 <
/// rowᵢ` (strict): multipliers `λ ≥ 0` whose combination is a constant `c`
/// with `c < 0`, or `c ≤ 0` when a strict row carries positive weight (Motzkin).
/// Returns `(λ, residual_is_strict)`, or `None` for a satisfiable system or a
/// search beyond the row cap (fail closed). Multipliers are realized by SCALING
/// in the kernel term, so no multiplier-sum cap applies.
///
/// Search order (deterministic, so the certificate is a function of the
/// obligation): the cheap witnesses of [`cheap_farkas_witness`] first, then
/// the exact-rational simplex of [`simplex_farkas_search`] (complete for every
/// system inside its caps, its witness re-verified in exact arithmetic before
/// it is returned). Its three-valued answer steers the rest: a
/// [`SimplexSearch::NoWitness`] verdict is exact and ENDS the search (no
/// witness exists, so Fourier–Motzkin would only spend time to say `None`);
/// only a [`SimplexSearch::Declined`] — a cap or meter decline, nothing known
/// — falls through to greedy Fourier–Motzkin as the last fallback.
fn find_farkas_multipliers_real(rows: &[(RLin, bool)]) -> Option<(Vec<Q>, bool)> {
    cheap_farkas_witness(rows).or_else(|| match simplex_farkas_search(rows) {
        SimplexSearch::Witness(mult, strict) => Some((mult, strict)),
        SimplexSearch::NoWitness => None,
        SimplexSearch::Declined => fourier_motzkin(rows),
    })
}

/// The witnesses a dense system hides from Fourier–Motzkin but that cost
/// O(rows² × vars) to find directly:
///
/// 1. a single CLOSED row that is false (`0 ≤ −1`, `0 < 0`);
/// 2. a PROPORTIONAL pair `rowⱼ = −t·rowᵢ` on every coefficient (`t > 0`) —
///    the interval `x ≤ 1 ∧ x ≥ 2`, `x < y ∧ y < x`, and every two-row Farkas
///    combination;
/// 3. INTERVAL BOUND PROPAGATION: single-variable rows give each variable its
///    tightest lower/upper bound; a multi-variable row `0 ≤ Σ aⱼxⱼ + c` is
///    refuted when its maximum over the box (`aⱼ > 0` takes the upper bound,
///    `aⱼ < 0` the lower) is negative — with multiplier `|aⱼ|/|bⱼ|` on the
///    bound row whose coefficient on `xⱼ` is `bⱼ`. This is the shape of the
///    ny-cert box systems and of "dense noise rows over a bounded box", where
///    Fourier–Motzkin's intermediate row count explodes before the (few) rows
///    that matter are ever combined.
fn cheap_farkas_witness(rows: &[(RLin, bool)]) -> Option<(Vec<Q>, bool)> {
    let n = rows.len();
    let zero = q_from_int(0);
    let one = q_from_int(1);

    // 1. closed rows.
    for (i, (r, strict)) in rows.iter().enumerate() {
        if r.terms.is_empty() && residual_is_false(&r.c, *strict) {
            let mut mult = vec![zero.clone(); n];
            mult[i] = one.clone();
            return Some((mult, *strict));
        }
    }

    // 2. proportional pairs.
    for i in 0..n {
        let (ri, si) = &rows[i];
        let Some((x0, ci0)) = ri.terms.iter().next() else {
            continue;
        };
        for j in (i + 1)..n {
            let (rj, sj) = &rows[j];
            if rj.terms.len() != ri.terms.len() {
                continue;
            }
            let Some(cj0) = rj.terms.get(x0) else {
                continue;
            };
            let t = -(cj0 / ci0);
            if !q_is_pos(&t) {
                continue;
            }
            let proportional =
                ri.terms.iter().all(|(x, ci)| rj.terms.get(x).is_some_and(|cj| *cj == -(&t * ci)));
            if !proportional {
                continue;
            }
            let cst = &t * &ri.c + &rj.c;
            let strict = *si || *sj;
            if residual_is_false(&cst, strict) {
                let mut mult = vec![zero.clone(); n];
                mult[i] = t;
                mult[j] = one.clone();
                return Some((mult, strict));
            }
        }
    }

    // 3. interval bound propagation.
    struct Bound {
        value: Q,
        row: usize,
        strict: bool,
    }
    let mut lower: BTreeMap<&str, Bound> = BTreeMap::new();
    let mut upper: BTreeMap<&str, Bound> = BTreeMap::new();
    for (i, (r, strict)) in rows.iter().enumerate() {
        if r.terms.len() != 1 {
            continue;
        }
        let (x, a) = r.terms.iter().next()?;
        // `0 ≤ a·x + c`: `a > 0` gives `x ≥ −c/a`, `a < 0` gives `x ≤ −c/a`.
        let value = -(&r.c / a);
        let is_lower = q_is_pos(a);
        let table = if is_lower { &mut lower } else { &mut upper };
        let better = match table.get(x.as_str()) {
            None => true,
            Some(b) => {
                let tighter = if is_lower { value > b.value } else { value < b.value };
                tighter || (value == b.value && *strict && !b.strict)
            }
        };
        if better {
            table.insert(x.as_str(), Bound { value, row: i, strict: *strict });
        }
    }
    'rows: for (i, (r, strict)) in rows.iter().enumerate() {
        if r.terms.len() < 2 {
            continue;
        }
        let mut mult = vec![zero.clone(); n];
        let mut cst = r.c.clone();
        let mut residual_strict = *strict;
        for (x, a) in &r.terms {
            let table = if q_is_pos(a) { &upper } else { &lower };
            let Some(bound) = table.get(x.as_str()) else {
                continue 'rows;
            };
            let bound_row = &rows[bound.row].0;
            let b = bound_row.terms.get(x)?;
            let lam = -(a / b); // > 0: the signs of `a` and `b` differ.
            cst += &lam * &bound_row.c;
            mult[bound.row] = &mult[bound.row] + &lam;
            residual_strict |= bound.strict;
        }
        if residual_is_false(&cst, residual_strict) {
            mult[i] = one.clone();
            return Some((mult, residual_strict));
        }
    }
    None
}

/// Exact-rational Fourier–Motzkin with a GREEDY elimination order: at every
/// step the variable with the fewest `#positive × #negative` row pairs is
/// eliminated (ties by name), which keeps the intermediate row count far below
/// name order on sparse systems. A search past `ROW_CAP` rows declines.
///
/// KNOWN LIMIT: FM is exponential in the worst case — a dense contradiction
/// over a dozen variables that needs more than two rows and is not a
/// bound-propagation shape pushes it past `ROW_CAP` within two eliminations
/// (`simplex_farkas_tests::fm_declines_but_simplex_certifies_a_dense_four_row_contradiction`
/// measures one). It is therefore the LAST fallback, behind
/// [`simplex_farkas_search`], and reached only after a cap/meter decline
/// ([`SimplexSearch::Declined`]) — never after a [`SimplexSearch::NoWitness`]
/// verdict, which already proves this search would return `None`.
fn fourier_motzkin(rows: &[(RLin, bool)]) -> Option<(Vec<Q>, bool)> {
    const ROW_CAP: usize = 4000;
    let n = rows.len();

    #[derive(Clone)]
    struct FmRow {
        coeffs: BTreeMap<String, Q>,
        cst: Q,
        mult: Vec<Q>,
        strict: bool,
    }

    fn contradiction(r: &FmRow) -> bool {
        r.coeffs.is_empty() && residual_is_false(&r.cst, r.strict)
    }

    /// Scale a derived row so its multipliers sum to one: the combination is
    /// invariant under a positive scale, and this keeps the rationals small.
    fn normalize(r: &mut FmRow) {
        let s = r.mult.iter().fold(q_from_int(0), |acc, m| acc + m);
        if q_is_pos(&s) && s != q_from_int(1) {
            for v in r.coeffs.values_mut() {
                *v = &*v / &s;
            }
            r.cst = &r.cst / &s;
            for m in &mut r.mult {
                *m = &*m / &s;
            }
        }
    }

    let mut remaining: BTreeSet<String> =
        rows.iter().flat_map(|(r, _)| r.terms.keys().cloned()).collect();

    let mut current: Vec<FmRow> = Vec::with_capacity(n);
    for (i, (r, strict)) in rows.iter().enumerate() {
        let mut mult = vec![q_from_int(0); n];
        mult[i] = q_from_int(1);
        let row = FmRow { coeffs: r.terms.clone(), cst: r.c.clone(), mult, strict: *strict };
        if contradiction(&row) {
            return Some((row.mult, row.strict));
        }
        current.push(row);
    }

    while !remaining.is_empty() {
        // Greedy choice: minimum pos × neg, ties by name.
        let mut best: Option<(usize, &str)> = None;
        for v in &remaining {
            let (mut pos, mut neg) = (0usize, 0usize);
            for r in &current {
                match r.coeffs.get(v) {
                    Some(c) if q_is_pos(c) => pos += 1,
                    Some(c) if q_is_neg(c) => neg += 1,
                    _ => {}
                }
            }
            let score = pos * neg;
            if best.is_none_or(|(s, _)| score < s) {
                best = Some((score, v.as_str()));
            }
        }
        let v = best?.1.to_string();
        remaining.remove(&v);

        let mut pos: Vec<&FmRow> = Vec::new();
        let mut neg: Vec<&FmRow> = Vec::new();
        let mut next: Vec<FmRow> = Vec::new();
        for r in &current {
            match r.coeffs.get(&v) {
                Some(c) if q_is_pos(c) => pos.push(r),
                Some(c) if q_is_neg(c) => neg.push(r),
                _ => next.push(r.clone()),
            }
        }
        for p in &pos {
            for nn in &neg {
                let ap = p.coeffs.get(&v).cloned().unwrap_or_else(|| q_from_int(0)); // > 0
                let an = -nn.coeffs.get(&v).cloned().unwrap_or_else(|| q_from_int(0)); // > 0
                // combined = an·p + ap·n  (the coefficient on `v` cancels).
                let mut coeffs: BTreeMap<String, Q> = BTreeMap::new();
                for key in p.coeffs.keys().chain(nn.coeffs.keys()) {
                    if *key == v || coeffs.contains_key(key) {
                        continue;
                    }
                    let cp = p.coeffs.get(key).cloned().unwrap_or_else(|| q_from_int(0));
                    let cn = nn.coeffs.get(key).cloned().unwrap_or_else(|| q_from_int(0));
                    let val = &an * &cp + &ap * &cn;
                    if !q_is_zero(&val) {
                        coeffs.insert(key.clone(), val);
                    }
                }
                let cst = &an * &p.cst + &ap * &nn.cst;
                let mult: Vec<Q> = (0..n).map(|i| &an * &p.mult[i] + &ap * &nn.mult[i]).collect();
                let mut row = FmRow { coeffs, cst, mult, strict: p.strict || nn.strict };
                normalize(&mut row);
                if row.coeffs.is_empty() {
                    if contradiction(&row) {
                        return Some((row.mult, row.strict));
                    }
                    // A satisfied constant row is redundant.
                    continue;
                }
                next.push(row);
                if next.len() > ROW_CAP {
                    return None;
                }
            }
        }
        current = next;
    }
    current.iter().find(|r| contradiction(r)).map(|r| (r.mult.clone(), r.strict))
}

// ---------------------------------------------------------------------------
// The exact-rational simplex Farkas search.
// ---------------------------------------------------------------------------

/// Maximum number of tableau cells (constraints × columns, artificial columns
/// and the right-hand side included) the simplex builds. The dual LP has one
/// constraint per variable that survives presolve plus two, and one column per
/// surviving row plus the slack plus one artificial per constraint: at the
/// atom cap over 64 variables that is 66 × 132 ≈ 8.7K cells. A pool that
/// mentions many hundreds of DISTINCT variables (64 atoms × 32 variables each
/// is admitted by the caps) would build a tableau of a million exact
/// rationals, so past this budget the simplex declines (`None`;
/// Fourier–Motzkin is still tried) instead of allocating it.
const SIMPLEX_CELL_BUDGET: usize = 65_536;

/// Pivot cap for one Phase-1 run, as a multiple of (constraints + columns).
/// Bland's rule never revisits a basis and so terminates without any cap, but
/// its bound on the number of bases visited is combinatorial, so the cap keeps
/// the worst case a clean decline (`None`, then Fourier–Motzkin) instead of a
/// stall. Measured pivot counts (debug build; "size" is constraints +
/// columns): the `mip-46963` shapes take 5–10 pivots (size 17–32), the crown
/// 4 (size 13), the box systems n = 10..30 take 22–62 (size 45–125), the
/// 12-variable noise case 16, the 12-variable / 40-row dense contradiction 72
/// (size 69), the seeded dense 8–20-variable systems 10–30 (size 25–45) — all
/// at or under 1 × size. The cap is 8 × size. HONESTLY: that is NO margin at
/// the admitted extreme. An adversarial round on dense 32-variable × 64-row
/// pools (exactly `MAX_ROW_VARS` × `MAX_REAL_ATOMS`, every row dense) measured
/// 552–993 pivots at size 133 — a worst ratio of 7.47, 93% of this cap — and
/// 1302 pivots (ratio 6.6) on 64 distinct variables × 64 rows; and under an
/// unbounded meter (`simplex_farkas_tests::simplex_work_measurements`) an
/// eight-row-core 32 × 64 pool and a 64-variable pool of 32-wide rows RUN
/// INTO the cap (1064 and 1576 pivots) and decline on it. In the lane those
/// shapes never get that far: [`SIMPLEX_WORK_BUDGET`] stops them after about
/// a second, and they are shapes the lane cannot certify anyway (their
/// supports decline at the replay's [`NODE_BUDGET`]). This cap is the
/// backstop for a run whose per-pivot work stays small, not a bound the
/// admitted shapes respect.
const SIMPLEX_PIVOT_FACTOR: usize = 8;

/// The DETERMINISTIC arithmetic work budget of one [`simplex_farkas`] call —
/// the Phase-1 solve and every support-reduction sub-solve draw on the same
/// meter. The unit is machine-independent: for every tableau cell written by
/// a pivot (the structural and artificial columns, the right-hand side and the
/// reduced-cost row) the meter is charged `1 + bits` of the integer written,
/// and the initial tableau is charged the same way. It is a function of the
/// obligation alone — no clock, no allocator, no thread — so the certificate
/// (produced or declined) stays a function of the obligation, which
/// `recheck_cleancic` relies on when it regenerates and byte-compares.
///
/// SIZED (debug build, num-bigint unoptimized, ≈ 45M work units per second;
/// `simplex_farkas_tests::simplex_work_measurements` prints the current
/// figures and `simplex_work_budget_declines_the_widest_admitted_pools` pins
/// the declines). The widest ADMITTED shapes — dense 32-variable × 64-row
/// pools, `MAX_ROW_VARS` × `MAX_REAL_ATOMS`, from the adversarial round's
/// generator and the in-tree one — need 78M–231M for Phase-1 alone (472–852
/// pivots; one seed runs into the pivot cap), and 64- and 200-variable pools
/// of 32-wide rows 0.8G–1.1G; all of them exhaust this budget at 50.0M–50.3M
/// (the overshoot is one pivot's charge) in 0.7–1.1 s and decline. Under the
/// rational tableau without a meter the same 32 × 64 solves took 137–220 s,
/// the 64-variable one 671 s, and the support reduction after them more than
/// ten minutes. Declining them costs nothing the lane could have had: every
/// 32-variable support, even a five-row core, declines at the replay's
/// [`NODE_BUDGET`] (measured 36–79 s of replay per pool). Every shape the lane
/// certifies today stays far under: the `mip-46963` systems, the crown, the
/// box systems n = 10..30 and the noise cases spend 0.3K–50K (≤ 0.1%), the
/// seeded dense 8–20-variable suite 8K–101K (≤ 0.2%), the dense four-row
/// contradiction 1.94M (3.9%, support reduction included), and dense pools
/// up to 25 variables × 60 rows 0.4M–30M (≤ 61%) — the 28 × 64 pool (64M) is
/// the first dense shape the meter stops.
const SIMPLEX_WORK_BUDGET: u64 = 50_000_000;

/// The work meter of one [`simplex_farkas`] call (see
/// [`SIMPLEX_WORK_BUDGET`]). `spent` only grows; once it passes `budget`
/// every solve on the meter declines at its next check.
struct SimplexWork {
    spent: u64,
    budget: u64,
}

impl SimplexWork {
    fn with_budget(budget: u64) -> SimplexWork {
        SimplexWork { spent: 0, budget }
    }

    fn fresh() -> SimplexWork {
        SimplexWork::with_budget(SIMPLEX_WORK_BUDGET)
    }

    fn exhausted(&self) -> bool {
        self.spent > self.budget
    }

    /// Charge `cost`; `false` once the budget is exceeded.
    fn charge(&mut self, cost: u64) -> bool {
        self.spent = self.spent.saturating_add(cost);
        !self.exhausted()
    }
}

/// The meter's price of one written integer: `1 + bits`.
fn int_cost(n: &BigInt) -> u64 {
    1 + n.bits()
}

fn big_gcd(a: &BigInt, b: &BigInt) -> BigInt {
    let mut a = BigInt::from_biguint(Sign::Plus, a.magnitude().clone());
    let mut b = BigInt::from_biguint(Sign::Plus, b.magnitude().clone());
    while b.sign() != Sign::NoSign {
        let r = &a % &b;
        a = b;
        b = r;
    }
    a
}

fn big_lcm(a: &BigInt, b: &BigInt) -> BigInt {
    let g = big_gcd(a, b);
    if g.sign() == Sign::NoSign { BigInt::from(0) } else { (a * b) / g }
}

/// Phase-1 simplex for `E·v = b`, `v ≥ 0` over exact rationals: one artificial
/// variable per constraint, minimize their sum. The pivot rule is BLAND'S: the
/// entering column is the LOWEST-indexed one with a negative reduced cost and
/// the leaving row is the minimum-ratio row, ties to the lowest-indexed basic
/// variable. Bland's rule never revisits a basis, so the iteration terminates
/// without a cycling guard, and the whole run is a deterministic function of
/// `(E, b)` (dense `Vec`s, index order — no hashing, no randomness). Returns
/// the final basic solution `v`, the pivot count, and whether the artificial
/// sum reached zero (`true`: the system is feasible and `v` solves it;
/// `false`: the optimum stayed positive, the system is infeasible and `v` is
/// merely the last basic point — handed back so the caller's verifier is
/// exercised on it too); `None` when `max_pivots` or the shared `work` budget
/// is exceeded, or — impossible for a Phase-1 objective bounded below by
/// zero, kept as a defensive decline — when a column is unbounded.
///
/// ARITHMETIC: INTEGER-PRESERVING (fraction-free, Edmonds/Bareiss) pivoting.
/// The tableau holds `D · B⁻¹[E | I]`, `D · B⁻¹b` and `D · (c − c_B B⁻¹[E |
/// I])` as INTEGERS with the single common denominator `D = det B > 0`; a
/// pivot on `(r, j)` with pivot entry `p` leaves the pivot row alone, maps
/// every other cell to `(p·x − x_j·p_row) / D` (an exact division — the
/// results are minors of the integer input, and a non-zero remainder, which
/// no correct run produces, is a `None`), and sets `D := p`. Entries are
/// bounded by minors of the input (Hadamard), and no gcd is ever taken, which
/// is what makes a pivot cheap. To make the input integer the STRUCTURAL
/// COLUMNS of `E` are scaled by the lcm of their denominators and `b` by the
/// lcm of its own — never a constraint row, which would reweight the Phase-1
/// objective. Positive column scaling leaves Bland's choices unchanged (a
/// reduced cost keeps its sign; the ratios of one column all scale alike, so
/// the minimum and its ties are the same rows), so the basis sequence, and
/// therefore `v` once unscaled, is exactly that of the rational tableau.
fn phase1_simplex(
    e: &[Vec<Q>],
    b: &[Q],
    max_pivots: usize,
    work: &mut SimplexWork,
) -> Option<(Vec<Q>, usize, bool)> {
    let k_rows = e.len();
    let n_cols = e.first().map_or(0, Vec::len);
    let width = n_cols + k_rows;
    let zero = BigInt::from(0);
    let one = BigInt::from(1);
    if b.len() != k_rows || e.iter().any(|r| r.len() != n_cols) || work.exhausted() {
        return None;
    }
    let is_zero = |x: &BigInt| x.sign() == Sign::NoSign;
    let is_pos = |x: &BigInt| x.sign() == Sign::Plus;
    let is_neg = |x: &BigInt| x.sign() == Sign::Minus;
    // Column scales: the lcm of the denominators down each structural column,
    // and of `b`. A scaled entry is `numer · (scale / denom)`, an integer.
    let col_scale: Vec<BigInt> = (0..n_cols)
        .map(|j| e.iter().fold(one.clone(), |acc, r| big_lcm(&acc, r[j].denom())))
        .collect();
    let b_scale: BigInt = b.iter().fold(one.clone(), |acc, v| big_lcm(&acc, v.denom()));
    let scaled = |v: &Q, scale: &BigInt| -> BigInt { v.numer() * (scale / v.denom()) };
    // Tableau rows with a non-negative right-hand side (flip the sign of a
    // constraint whose `bₖ < 0`), the artificial identity block appended.
    let mut t: Vec<Vec<BigInt>> = Vec::with_capacity(k_rows);
    let mut rhs: Vec<BigInt> = Vec::with_capacity(k_rows);
    let mut cost = 0u64;
    for (k, row) in e.iter().enumerate() {
        let flip = q_is_neg(&b[k]);
        let mut tr: Vec<BigInt> = Vec::with_capacity(width);
        tr.extend(row.iter().enumerate().map(|(j, v)| {
            let s = scaled(v, &col_scale[j]);
            if flip { -s } else { s }
        }));
        tr.extend((0..k_rows).map(|a| if a == k { one.clone() } else { zero.clone() }));
        cost += tr.iter().map(int_cost).sum::<u64>();
        t.push(tr);
        let s = scaled(&b[k], &b_scale);
        rhs.push(if flip { -s } else { s });
    }
    let mut basis: Vec<usize> = (n_cols..width).collect();
    // Reduced costs of the Phase-1 objective Σ artificial: `0 − Σₖ Tₖⱼ` on a
    // structural column, `1 − 1 = 0` on an artificial one.
    let mut d: Vec<BigInt> = (0..width)
        .map(|j| {
            if j < n_cols {
                -t.iter().fold(zero.clone(), |acc, r| acc + &r[j])
            } else {
                zero.clone()
            }
        })
        .collect();
    cost += d.iter().map(int_cost).sum::<u64>() + rhs.iter().map(int_cost).sum::<u64>();
    if !work.charge(cost) {
        return None;
    }
    let mut den = one.clone();
    let mut pivots = 0usize;
    loop {
        let Some(j) = (0..width).find(|&j| is_neg(&d[j])) else {
            break;
        };
        // Minimum ratio `rhs[r] / t[r][j]` over `t[r][j] > 0`, compared
        // cross-multiplied (both denominators positive).
        let mut leave: Option<usize> = None;
        for r in 0..k_rows {
            if !is_pos(&t[r][j]) {
                continue;
            }
            let better = match leave {
                None => true,
                Some(lr) => {
                    let lhs = &rhs[r] * &t[lr][j];
                    let rhs_ = &rhs[lr] * &t[r][j];
                    lhs < rhs_ || (lhs == rhs_ && basis[r] < basis[lr])
                }
            };
            if better {
                leave = Some(r);
            }
        }
        let r = leave?;
        pivots += 1;
        if pivots > max_pivots {
            return None;
        }
        // Pivot on (r, j): the pivot row stays; every other row, the
        // right-hand side and the reduced costs become `(p·x − f·p_row) / D`.
        let p = t[r][j].clone();
        let prow = t[r].clone();
        let prhs = rhs[r].clone();
        let mut cost = 0u64;
        let mut exact = true;
        let mut update = |x: &mut BigInt, f: &BigInt, pc: &BigInt| {
            if is_zero(x) && is_zero(pc) {
                return;
            }
            let num = &p * &*x - f * pc;
            if !is_zero(&(&num % &den)) {
                exact = false;
            }
            *x = num / &den;
            cost += int_cost(x);
        };
        for k in 0..k_rows {
            if k == r {
                continue;
            }
            let f = t[k][j].clone();
            for c in 0..width {
                update(&mut t[k][c], &f, &prow[c]);
            }
            update(&mut rhs[k], &f, &prhs);
        }
        let f = d[j].clone();
        for c in 0..width {
            update(&mut d[c], &f, &prow[c]);
        }
        if !exact {
            return None;
        }
        den = p;
        basis[r] = j;
        if !work.charge(cost) {
            return None;
        }
    }
    // Feasible iff every artificial variable still in the basis sits at zero.
    let feasible = (0..k_rows).all(|r| basis[r] < n_cols || is_zero(&rhs[r]));
    let mut v = vec![q_from_int(0); n_cols];
    for r in 0..k_rows {
        if basis[r] < n_cols {
            // `vⱼ = (rhs[r] / D) · scaleⱼ / b_scale`.
            v[basis[r]] = Q::new(&rhs[r] * &col_scale[basis[r]], &den * &b_scale);
        }
    }
    Some((v, pivots, feasible))
}

/// Verify a candidate Farkas witness in exact arithmetic — the soundness guard
/// between the simplex and the replay: every multiplier is non-negative, the
/// weighted combination of the rows cancels on EVERY variable, and the
/// residual constant is negative, or non-positive with a strict row carrying
/// positive weight (Motzkin). Returns the strictness of the residual, or
/// `None` for anything else (the all-zero vector included).
fn verify_farkas_witness(rows: &[(RLin, bool)], mult: &[Q]) -> Option<bool> {
    if mult.len() != rows.len() || mult.iter().any(q_is_neg) {
        return None;
    }
    let mut acc = RLin { terms: BTreeMap::new(), c: q_from_int(0) };
    let mut strict = false;
    for (i, (r, s)) in rows.iter().enumerate() {
        if q_is_pos(&mult[i]) {
            acc = acc.add(&r.scale(&mult[i]));
            strict |= *s;
        }
    }
    if !acc.terms.is_empty() || !residual_is_false(&acc.c, strict) {
        return None;
    }
    Some(strict)
}

/// The UNVERIFIED simplex candidate: the multipliers `y` the Phase-1 run of
/// the dual LP ends on, with the pivot count (for the measurements) and the
/// Phase-1 verdict (`true`: the LP is feasible and `y` solves it; `false`: the
/// LP is infeasible, so the row system is satisfiable, and `y` is only the
/// last basic point). `None` when a cap declined. Never handed to the replay
/// directly — [`simplex_farkas`] requires the verdict AND
/// [`verify_farkas_witness`] on the multipliers.
///
/// THE LP (Motzkin transposition). Over rows `0 ≤ rowᵢ` (`i ∉ S`) and
/// `0 < rowᵢ` (`i ∈ S`) with `rowᵢ = Σⱼ aᵢⱼ xⱼ + cᵢ`, find
///
/// ```text
///   y ≥ 0, t ≥ 0,   Σᵢ aᵢⱼ yᵢ = 0 for every j,   Σᵢ cᵢ yᵢ + t = 0,   t + Σᵢ∈S yᵢ = 1.
/// ```
///
/// (⇐) A solution combines the rows into `0 ⋈ Σᵢ cᵢ yᵢ = −t`. If `t > 0` the
/// residual is negative — a Farkas refutation. If `t = 0` then `Σ_S yᵢ = 1`,
/// some strict row carries positive weight, and the combination is `0 < 0`.
/// Either way the system is infeasible; this is exactly what
/// [`verify_farkas_witness`] re-checks. (⇒) Motzkin's transposition theorem:
/// an infeasible system has `y ≥ 0` with `yᵀA = 0` and either `yᵀc < 0`, or
/// `yᵀc ≤ 0` with `Σ_S y > 0`. In the first case set `t = −yᵀc > 0`, in the
/// second `t = 0`; in both `t + Σ_S y > 0`, so scaling `(y, t)` by its
/// reciprocal satisfies the last constraint. The LP is therefore feasible iff
/// the row system is infeasible, and the exact Phase-1 simplex decides it —
/// no ε-lifting is needed because the strict rows enter only through the
/// normalization `t + Σ_S y = 1`, which is linear. With no strict row the
/// last constraint reads `t = 1`, i.e. plain Farkas with `yᵀc = −1`.
///
/// PRESOLVE (sound and complete): a variable that appears in exactly one row
/// forces that row's multiplier to zero (nothing can cancel its coefficient),
/// so the row is dropped, to a fixpoint; the LP is built over the survivors.
///
/// DETERMINISM: rows in obligation order, variables in `BTreeSet` order,
/// Bland's rule inside; the candidate is a function of the row list. The
/// solve draws on `work` (see [`SIMPLEX_WORK_BUDGET`]) and declines once it
/// is spent.
fn simplex_farkas_candidate(
    rows: &[(RLin, bool)],
    work: &mut SimplexWork,
) -> Option<(Vec<Q>, usize, bool)> {
    let m = rows.len();
    let zero = q_from_int(0);
    let one = q_from_int(1);

    let mut alive = vec![true; m];
    loop {
        let mut occurrences: BTreeMap<&str, (usize, usize)> = BTreeMap::new();
        for (i, (r, _)) in rows.iter().enumerate() {
            if !alive[i] {
                continue;
            }
            for x in r.terms.keys() {
                let e = occurrences.entry(x.as_str()).or_insert((0, i));
                e.0 += 1;
                e.1 = i;
            }
        }
        let mut changed = false;
        for (count, i) in occurrences.into_values() {
            if count == 1 && alive[i] {
                alive[i] = false;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let live: Vec<usize> = (0..m).filter(|&i| alive[i]).collect();
    if live.is_empty() {
        return None;
    }
    let vars: BTreeSet<&str> =
        live.iter().flat_map(|&i| rows[i].0.terms.keys().map(String::as_str)).collect();
    let n_cols = live.len() + 1; // yᵢ per live row, then t
    let k_rows = vars.len() + 2;
    let cells = k_rows * (n_cols + k_rows + 1);
    if cells > SIMPLEX_CELL_BUDGET {
        return None;
    }
    let mut e: Vec<Vec<Q>> = Vec::with_capacity(k_rows);
    let mut b: Vec<Q> = Vec::with_capacity(k_rows);
    for x in &vars {
        let mut row = vec![zero.clone(); n_cols];
        for (col, &i) in live.iter().enumerate() {
            if let Some(a) = rows[i].0.terms.get(*x) {
                row[col] = a.clone();
            }
        }
        e.push(row);
        b.push(zero.clone());
    }
    let mut row = vec![zero.clone(); n_cols];
    for (col, &i) in live.iter().enumerate() {
        row[col] = rows[i].0.c.clone();
    }
    row[live.len()] = one.clone();
    e.push(row);
    b.push(zero.clone());
    let mut row = vec![zero.clone(); n_cols];
    for (col, &i) in live.iter().enumerate() {
        if rows[i].1 {
            row[col] = one.clone();
        }
    }
    row[live.len()] = one.clone();
    e.push(row);
    b.push(one);

    let max_pivots = SIMPLEX_PIVOT_FACTOR * (k_rows + n_cols + k_rows);
    let (v, pivots, feasible) = phase1_simplex(&e, &b, max_pivots, work)?;
    let mut mult = vec![zero; m];
    for (col, &i) in live.iter().enumerate() {
        mult[i] = v[col].clone();
    }
    Some((mult, pivots, feasible))
}

/// The three-valued outcome of one simplex search over a row list. The lane
/// search reads all three ([`find_farkas_multipliers_real`]); the two-valued
/// view [`SimplexSearch::witness`] is what the older entry points return.
///
/// `NoWitness` is an EXACT verdict: Phase-1 COMPLETED with a positive
/// optimum, so NO Farkas witness exists over the ORIGINAL rows and any later
/// search would return `None`. Two facts carry it.
///
/// 1. The presolve of [`simplex_farkas_candidate`] preserves witness
///    existence in BOTH directions. A variable `x` occurring in exactly one
///    live row `i` (coefficient `aᵢₓ ≠ 0`) forces `λᵢ · aᵢₓ = 0`, i.e.
///    `λᵢ = 0`, in every witness `λ ≥ 0` with `Σᵢ λᵢ aᵢⱼ = 0` for all `j`:
///    so every witness over the rows WITH `i` is one over the rows without
///    it (⇒), and every witness over the survivors extends by zeros to one
///    over all rows (⇐). By induction to the fixpoint, the original rows and
///    the survivors have the SAME set of witnesses.
/// 2. The Motzkin LP over the survivors is feasible iff a witness over the
///    survivors exists (the (⇐)/(⇒) argument on [`simplex_farkas_candidate`]),
///    and a completed Phase-1 decides that LP exactly: under the
///    fraction-free tableau `den = det B > 0`, so every sign is the rational
///    tableau's, and `feasible` (every basic artificial at right-hand side
///    `0`) is exactly "Phase-1 optimum `== 0`".
///
/// Fourier–Motzkin only ever returns a member of that same witness set (a
/// non-negative combination that cancels every variable with a false
/// residual), so after `NoWitness` it would return `None` too: ending the
/// search here changes no outcome, it only removes FM's time. (A presolve
/// that drops EVERY row is such a proof as well, but it is reported as
/// `Declined` — conservative, and FM is instantaneous on it.)
///
/// `Declined` is a cap/meter/inexact decline — [`SIMPLEX_CELL_BUDGET`], the
/// pivot cap, the [`SIMPLEX_WORK_BUDGET`] meter, an inexact pivot, an empty
/// presolve — or a failed [`verify_farkas_witness`] (which no correct run
/// produces). Nothing is known about the rows, so the caller falls through
/// to Fourier–Motzkin.
#[derive(Clone, Debug, PartialEq, Eq)]
enum SimplexSearch {
    /// A witness that passed [`verify_farkas_witness`], with the strictness
    /// of its residual.
    Witness(Vec<Q>, bool),
    NoWitness,
    Declined,
}

impl SimplexSearch {
    /// The two-valued view: the witness, or `None` for BOTH `NoWitness` and
    /// `Declined`.
    fn witness(self) -> Option<(Vec<Q>, bool)> {
        match self {
            SimplexSearch::Witness(mult, strict) => Some((mult, strict)),
            SimplexSearch::NoWitness | SimplexSearch::Declined => None,
        }
    }
}

/// The primary multiplier finder: the Phase-1 simplex of
/// [`simplex_farkas_candidate`] on the Motzkin dual LP, its answer accepted
/// ONLY after [`verify_farkas_witness`] recombines it in exact arithmetic (a
/// failed verification — which no correct run produces — is a
/// [`SimplexSearch::Declined`], so the caller still falls through to
/// Fourier–Motzkin). The residual is reported strict when any strict row
/// carries positive weight, exactly as the cheap and FM witnesses do, so the
/// replay keeps one such row strict. [`simplex_farkas_search`] is the
/// three-valued entry point on a fresh meter; [`simplex_farkas`] and
/// [`simplex_farkas_metered`] are its two-valued views.
///
/// SUPPORT REDUCTION. The vertex Phase-1 lands on can carry up to
/// (variables + 2) positive multipliers, and on a dense contradiction buried
/// under dense satisfiable noise it drags noise rows into the witness
/// (measured: 13 rows where 4 suffice, a 3.6 MB certificate at 1.42M codec
/// nodes — the replay's cost is per dense row). So the witness is then
/// REDUCED greedily and deterministically: for each supported row in index
/// order, the sub-LP over the other supported rows is re-solved, and the row
/// is dropped for good when a verified witness survives without it. The result
/// is an irreducible support; every intermediate witness is verified, and a
/// sub-solve that declines on a cap just keeps the row. At most
/// (variables + 2) extra solves, each over a smaller LP — and all of them on
/// the ONE work meter of the call ([`SIMPLEX_WORK_BUDGET`]): once it is
/// spent the reduction stops and the best verified witness so far is
/// returned, so the reduction can never add unbounded work.
fn simplex_farkas_search(rows: &[(RLin, bool)]) -> SimplexSearch {
    simplex_farkas_on(rows, &mut SimplexWork::fresh())
}

/// [`simplex_farkas_search`] collapsed to its witness (`None` for both
/// `NoWitness` and `Declined`).
fn simplex_farkas(rows: &[(RLin, bool)]) -> Option<(Vec<Q>, bool)> {
    simplex_farkas_search(rows).witness()
}

/// [`simplex_farkas`] with its work meter handed back (for the measurements
/// and the budget tests): `spent` is the deterministic cost of the whole
/// call, whether it produced a witness or declined.
fn simplex_farkas_metered(rows: &[(RLin, bool)]) -> (Option<(Vec<Q>, bool)>, SimplexWork) {
    let mut work = SimplexWork::fresh();
    let witness = simplex_farkas_on(rows, &mut work).witness();
    (witness, work)
}

fn simplex_farkas_on(rows: &[(RLin, bool)], work: &mut SimplexWork) -> SimplexSearch {
    let Some((mult, _, feasible)) = simplex_farkas_candidate(rows, work) else {
        return SimplexSearch::Declined;
    };
    if !feasible {
        // Phase-1 completed with a positive optimum: an exact verdict.
        return SimplexSearch::NoWitness;
    }
    let Some(mut strict) = verify_farkas_witness(rows, &mult) else {
        return SimplexSearch::Declined; // fail-safe: FM still gets its turn
    };
    let mut best = mult;
    let support: Vec<usize> = (0..rows.len()).filter(|&i| q_is_pos(&best[i])).collect();
    for &drop in &support {
        if work.exhausted() {
            break; // the meter is spent: keep the best verified witness so far
        }
        if !q_is_pos(&best[drop]) {
            continue; // already left the support through an earlier reduction
        }
        let trial: Vec<usize> =
            (0..rows.len()).filter(|&i| i != drop && q_is_pos(&best[i])).collect();
        if trial.is_empty() {
            break;
        }
        let sub: Vec<(RLin, bool)> = trial.iter().map(|&i| rows[i].clone()).collect();
        let Some((sub_mult, _, true)) = simplex_farkas_candidate(&sub, work) else {
            continue;
        };
        let mut candidate = vec![q_from_int(0); rows.len()];
        for (k, &i) in trial.iter().enumerate() {
            candidate[i] = sub_mult[k].clone();
        }
        if let Some(s) = verify_farkas_witness(rows, &candidate) {
            best = candidate;
            strict = s;
        }
    }
    // Fail closed: the returned witness is the one verified last.
    match verify_farkas_witness(rows, &best).filter(|&s| s == strict) {
        Some(strict) => SimplexSearch::Witness(best, strict),
        None => SimplexSearch::Declined,
    }
}

// ---------------------------------------------------------------------------
// The ring normalizer: in-place `Eq.subst` rewriting under a context.
// ---------------------------------------------------------------------------

/// One frame of the context a rewrite happens under (outermost first in a
/// context vector): the hole is the LEFT / RIGHT operand of `Rat.add` /
/// `Rat.mul` with the other operand fixed.
#[derive(Clone)]
enum Frame {
    AddL(Expr),
    AddR(Expr),
    MulL(Expr),
    MulR(Expr),
}

fn plug(ctx: &[Frame], hole: Expr) -> Expr {
    ctx.iter().rev().fold(hole, |acc, frame| match frame {
        Frame::AddL(r) => rat_add(acc, r.clone()),
        Frame::AddR(l) => rat_add(l.clone(), acc),
        Frame::MulL(r) => rat_mul(acc, r.clone()),
        Frame::MulR(l) => rat_mul(l.clone(), acc),
    })
}

fn with_frame(ctx: &[Frame], frame: Frame) -> Vec<Frame> {
    let mut v = ctx.to_vec();
    v.push(frame);
    v
}

/// What a rewriter's proof establishes about its current term `cur`.
enum Shape {
    /// `proof : Eq Rat lhs cur` — a standalone equality chain.
    Eq { lhs: Expr },
    /// `proof : Rat.le Rat.zero cur` (weak) / `Rat.lt Rat.zero cur` (strict) —
    /// a Farkas fact rewritten IN PLACE, so the motive carries only `cur`.
    Fact { strict: bool },
}

/// A proof about a current term, extended one rewrite at a time: given `h : Eq
/// a b` and a context with `cur = ctx[a]`, the new proof is `Eq.subst (λ t.
/// P ctx[t]) a b h proof : P ctx[b]`. The kernel checks `h` against `Eq a b`
/// DEFINITIONALLY, which is what lets a lemma stated with `Rat.zero`/`Rat.one`
/// rewrite a term spelled with `Rat.mk 0 1` / `Rat.mk 1 1`; `a`/`b` are always
/// spelled in this lane's own canonical literal form, so the proof's TYPE stays
/// syntactically canonical. Every step is charged against [`NODE_BUDGET`] and
/// [`MAX_CHAIN_STEPS`]; exceeding either fails closed.
struct Rewriter {
    shape: Shape,
    cur: Expr,
    proof: Expr,
    /// `Eq.subst` steps nested in `proof` (its spine depth).
    steps: usize,
    /// Codec-style node count of `proof`.
    nodes: usize,
}

impl Rewriter {
    fn chain(e: Expr) -> Rewriter {
        let proof = eq_refl_rat(e.clone());
        let nodes = expr_nodes(&proof);
        Rewriter { shape: Shape::Eq { lhs: e.clone() }, cur: e, proof, steps: 0, nodes }
    }

    fn fact(strict: bool, cur: Expr, proof: Expr) -> Rewriter {
        let nodes = expr_nodes(&proof);
        Rewriter { shape: Shape::Fact { strict }, cur, proof, steps: 0, nodes }
    }

    fn strict(&self) -> bool {
        matches!(self.shape, Shape::Fact { strict: true })
    }

    /// The motive body with the hole at `bvar 0`. Everything else in it sits
    /// under the motive's binder, so a loose bound variable it carries (only
    /// the shuffle lemma's own proof has any — see [`shuffle_lemma_proof`]) is
    /// lifted by one; closed terms lift for free.
    fn body(&self, ctx: &[Frame]) -> Expr {
        fn lift1(e: &Expr) -> Expr {
            if e.has_loose_bvars() { e.lift(1) } else { e.clone() }
        }
        let lifted: Vec<Frame> = ctx
            .iter()
            .map(|f| match f {
                Frame::AddL(e) => Frame::AddL(lift1(e)),
                Frame::AddR(e) => Frame::AddR(lift1(e)),
                Frame::MulL(e) => Frame::MulL(lift1(e)),
                Frame::MulR(e) => Frame::MulR(lift1(e)),
            })
            .collect();
        let hole = plug(&lifted, Expr::bvar(0));
        match &self.shape {
            Shape::Eq { lhs } => eq_rat(lift1(lhs), hole),
            Shape::Fact { strict: false } => rat_le(k("Rat.zero"), hole),
            Shape::Fact { strict: true } => rat_lt(k("Rat.zero"), hole),
        }
    }

    fn charge(&mut self, motive: &Expr, a: &Expr, b: &Expr, h: &Expr) -> Option<()> {
        self.steps += 1;
        if self.steps > MAX_CHAIN_STEPS {
            return None;
        }
        self.nodes += expr_nodes(motive) + expr_nodes(a) + expr_nodes(b) + expr_nodes(h) + 12;
        if self.nodes > NODE_BUDGET {
            return None;
        }
        Some(())
    }

    /// Fails (closed) if the builder's bookkeeping and the actual current term
    /// disagree — a bug can only FAIL to certify, never mint a wrong proof (the
    /// kernel would reject it anyway; this just keeps the error local).
    fn rw(&mut self, ctx: &[Frame], a: Expr, b: Expr, h: Expr) -> Option<()> {
        if plug(ctx, a.clone()) != self.cur {
            return None;
        }
        let motive = Expr::lam(BinderInfo::Default, rat_ty(), self.body(ctx));
        self.charge(&motive, &a, &b, &h)?;
        let prev = std::mem::replace(&mut self.proof, Expr::bvar(0));
        self.proof = eq_subst_rat(motive, a, b.clone(), h, prev);
        self.cur = plug(ctx, b);
        Some(())
    }

    /// For a fact whose LEFT side is `a` instead of `Rat.zero` (the `0 + 0` a
    /// `Rat.add_le_add` of two `0 ≤ _` facts leaves): rewrite it to `b`.
    fn rw_left(&mut self, a: Expr, b: Expr, h: Expr) -> Option<()> {
        let Shape::Fact { strict } = self.shape else {
            return None;
        };
        let rel: fn(Expr, Expr) -> Expr = if strict { rat_lt } else { rat_le };
        let motive = Expr::lam(BinderInfo::Default, rat_ty(), rel(Expr::bvar(0), self.cur.clone()));
        self.charge(&motive, &a, &b, &h)?;
        let prev = std::mem::replace(&mut self.proof, Expr::bvar(0));
        self.proof = eq_subst_rat(motive, a, b, h, prev);
        Some(())
    }
}

/// The canonical form of a linear term: a constant `k` in front of the
/// monomials `cᵢ·xᵢ` (`cᵢ ≠ 0`) in variable-name order, spelled in the kernel
/// as `k + (c₁*x₁ + (c₂*x₂ + (… + (cₙ*xₙ + 0))))`. The constant in FRONT and
/// the `+ 0` terminator are what make merging cheap: two constants combine at
/// the root in one shuffle, and an exhausted list folds away with a single
/// `Rat.add_zero` / `Rat.zero_add` instead of a walk to the end.
struct Canon {
    parts: Vec<(String, Q)>,
    k: Q,
}

impl Canon {
    fn expr(&self) -> Expr {
        nested(&self.parts, &self.k)
    }
}

fn mono(x: &str, c: &Q) -> Expr {
    rat_mul(rat_lit(c), var_expr(x))
}

/// `c₁*x₁ + (… + (cₙ*xₙ + 0))`.
fn monomial_list(parts: &[(String, Q)]) -> Expr {
    parts.iter().rev().fold(rat_lit(&q_from_int(0)), |acc, (x, c)| rat_add(mono(x, c), acc))
}

/// `k + monomial_list(parts)`.
fn nested(parts: &[(String, Q)], kk: &Q) -> Expr {
    rat_add(rat_lit(kk), monomial_list(parts))
}

/// Two rearrangement lemmas the normalizer rests on, neither registered in the
/// kernel environment under that shape:
///
/// * SHUFFLE `(a + b) + (c + d) = (a + c) + (b + d)` — how two canonical forms
///   meet (constants with constants, a shared variable's two monomials);
/// * LEFT-COMM `a + (b + c) = b + (a + c)` — how a monomial is inserted into a
///   canonical list one position at a time.
///
/// The replay term PROVES each once, over abstract operands, and binds both at
/// its root with beta-redexes: `(λ shuffle. (λ leftcomm. <proof of False>)
/// <leftcomm proof>) <shuffle proof>`. Every use on the proof spine is then a
/// four- or three-argument application instead of a rewrite chain copying the
/// whole running sum several times. The uses are `bvar 1` / `bvar 0` because
/// the spine sits DIRECTLY under those two binders: every `Eq.subst` step
/// nests as an APPLICATION argument (never under a lambda — motives are
/// sibling arguments, and a row's proof is an argument of the summation
/// lemma), so no other binder intervenes.
fn shuffle_lemma_app(a: Expr, b: Expr, c: Expr, d: Expr) -> Expr {
    Expr::apps(Expr::bvar(1), [a, b, c, d])
}

fn left_comm_lemma_app(a: Expr, b: Expr, c: Expr) -> Expr {
    Expr::apps(Expr::bvar(0), [a, b, c])
}

/// `∀ (a b c d : Rat), Eq ((a + b) + (c + d)) ((a + c) + (b + d))`.
fn shuffle_lemma_type() -> Expr {
    let (a, b, c, d) = (Expr::bvar(3), Expr::bvar(2), Expr::bvar(1), Expr::bvar(0));
    let body = eq_rat(
        rat_add(rat_add(a.clone(), b.clone()), rat_add(c.clone(), d.clone())),
        rat_add(rat_add(a, c), rat_add(b, d)),
    );
    (0..4).fold(body, |acc, _| Expr::pi(BinderInfo::Default, rat_ty(), acc))
}

/// `λ (a b c d : Rat). <Eq.subst chain>` proving [`shuffle_lemma_type`] from
/// `Rat.add_assoc` and `Rat.add_comm`: `(a+b)+(c+d) = a+(b+(c+d)) =
/// a+((b+c)+d) = a+((c+b)+d) = a+(c+(b+d)) = (a+c)+(b+d)`. The operands are
/// loose bound variables while the chain is built; [`Rewriter::body`] lifts
/// them under each motive's binder.
fn shuffle_lemma_proof() -> Option<Expr> {
    let (a, b, c, d) = (Expr::bvar(3), Expr::bvar(2), Expr::bvar(1), Expr::bvar(0));
    let cd = rat_add(c.clone(), d.clone());
    let bd = rat_add(b.clone(), d.clone());
    let mut ch = Rewriter::chain(rat_add(rat_add(a.clone(), b.clone()), cd.clone()));
    // 1. (a+b)+(c+d) = a+(b+(c+d))
    ch.rw(
        &[],
        rat_add(rat_add(a.clone(), b.clone()), cd.clone()),
        rat_add(a.clone(), rat_add(b.clone(), cd.clone())),
        const_app("Rat.add_assoc", [a.clone(), b.clone(), cd.clone()]),
    )?;
    // 2. b+(c+d) = (b+c)+d
    ch.rw(
        &[Frame::AddR(a.clone())],
        rat_add(b.clone(), cd.clone()),
        rat_add(rat_add(b.clone(), c.clone()), d.clone()),
        eq_symm_rat(
            rat_add(rat_add(b.clone(), c.clone()), d.clone()),
            rat_add(b.clone(), cd),
            const_app("Rat.add_assoc", [b.clone(), c.clone(), d.clone()]),
        ),
    )?;
    // 3. b+c = c+b
    ch.rw(
        &[Frame::AddR(a.clone()), Frame::AddL(d.clone())],
        rat_add(b.clone(), c.clone()),
        rat_add(c.clone(), b.clone()),
        const_app("Rat.add_comm", [b.clone(), c.clone()]),
    )?;
    // 4. (c+b)+d = c+(b+d)
    ch.rw(
        &[Frame::AddR(a.clone())],
        rat_add(rat_add(c.clone(), b.clone()), d.clone()),
        rat_add(c.clone(), bd.clone()),
        const_app("Rat.add_assoc", [c.clone(), b.clone(), d.clone()]),
    )?;
    // 5. a+(c+(b+d)) = (a+c)+(b+d)
    ch.rw(
        &[],
        rat_add(a.clone(), rat_add(c.clone(), bd.clone())),
        rat_add(rat_add(a.clone(), c.clone()), bd.clone()),
        eq_symm_rat(
            rat_add(rat_add(a.clone(), c.clone()), bd.clone()),
            rat_add(a.clone(), rat_add(c.clone(), bd.clone())),
            const_app("Rat.add_assoc", [a.clone(), c.clone(), bd.clone()]),
        ),
    )?;
    if ch.cur != rat_add(rat_add(a, c), bd) {
        return None;
    }
    Some((0..4).fold(ch.proof, |acc, _| Expr::lam(BinderInfo::Default, rat_ty(), acc)))
}

/// `∀ (a b c : Rat), Eq (a + (b + c)) (b + (a + c))`.
fn left_comm_lemma_type() -> Expr {
    let (a, b, c) = (Expr::bvar(2), Expr::bvar(1), Expr::bvar(0));
    let body = eq_rat(rat_add(a.clone(), rat_add(b.clone(), c.clone())), rat_add(b, rat_add(a, c)));
    (0..3).fold(body, |acc, _| Expr::pi(BinderInfo::Default, rat_ty(), acc))
}

/// `λ (a b c : Rat). <Eq.subst chain>` proving [`left_comm_lemma_type`]:
/// `a+(b+c) = (a+b)+c = (b+a)+c = b+(a+c)`.
fn left_comm_lemma_proof() -> Option<Expr> {
    let (a, b, c) = (Expr::bvar(2), Expr::bvar(1), Expr::bvar(0));
    let mut ch = Rewriter::chain(rat_add(a.clone(), rat_add(b.clone(), c.clone())));
    // 1. a+(b+c) = (a+b)+c
    ch.rw(
        &[],
        rat_add(a.clone(), rat_add(b.clone(), c.clone())),
        rat_add(rat_add(a.clone(), b.clone()), c.clone()),
        eq_symm_rat(
            rat_add(rat_add(a.clone(), b.clone()), c.clone()),
            rat_add(a.clone(), rat_add(b.clone(), c.clone())),
            const_app("Rat.add_assoc", [a.clone(), b.clone(), c.clone()]),
        ),
    )?;
    // 2. a+b = b+a
    ch.rw(
        &[Frame::AddL(c.clone())],
        rat_add(a.clone(), b.clone()),
        rat_add(b.clone(), a.clone()),
        const_app("Rat.add_comm", [a.clone(), b.clone()]),
    )?;
    // 3. (b+a)+c = b+(a+c)
    ch.rw(
        &[],
        rat_add(rat_add(b.clone(), a.clone()), c.clone()),
        rat_add(b.clone(), rat_add(a.clone(), c.clone())),
        const_app("Rat.add_assoc", [b.clone(), a.clone(), c.clone()]),
    )?;
    if ch.cur != rat_add(b, rat_add(a, c)) {
        return None;
    }
    Some((0..3).fold(ch.proof, |acc, _| Expr::lam(BinderInfo::Default, rat_ty(), acc)))
}

/// Closed-literal equality closer: `Eq Rat (op lit lit) (lit tgt)` for a
/// closed `Rat.add`/`Rat.mul` whose UNREDUCED raw representative is
/// `(raw_n, raw_d)` and whose value is `tgt`. `Rat` is `Quot Rat.Raw
/// Rat.Raw.Equiv`, so `@Quot.sound Rat.Raw Rat.Raw.Equiv (Raw.mk raw) (Raw.mk
/// tgt) (Eq.refl Int (raw_n·tgt_d))` proves it — the `Equiv` obligation
/// `raw_n·tgt_d = tgt_n·raw_d` closes by the kernel's native `Int.mul` reducer
/// and the left-hand `op` reduces to the raw representative by `Quot.lift` iota.
fn closed_eq_via_sound(raw_n: &BigInt, raw_d: &BigUint, tgt: &Q) -> Expr {
    let witness = raw_n * BigInt::from(tgt.denom().magnitude().clone());
    let raw = const_app("Rat.Raw.mk", [int_big(raw_n), nat_big(raw_d)]);
    let target = const_app("Rat.Raw.mk", [int_big(tgt.numer()), nat_big(tgt.denom().magnitude())]);
    Expr::apps(
        Expr::const_(Name::from_string("Quot.sound"), vec![lvl1()]),
        [k("Rat.Raw"), k("Rat.Raw.Equiv"), raw, target, eq_refl_int(int_big(&witness))],
    )
}

/// `(h : Eq (Rat.add a b) (lit (a+b)), a+b)` — raw `Rat.add` on literals is
/// `(n₁·d₂ + n₂·d₁, d₁·d₂)`.
fn fold_add(a: &Q, b: &Q) -> (Expr, Q) {
    let (da, db) = (a.denom().magnitude(), b.denom().magnitude());
    let raw_n = a.numer() * BigInt::from(db.clone()) + b.numer() * BigInt::from(da.clone());
    let raw_d = da * db;
    let sum = a + b;
    (closed_eq_via_sound(&raw_n, &raw_d, &sum), sum)
}

/// `(h : Eq (Rat.mul a b) (lit (a·b)), a·b)` — raw `Rat.mul` is `(n₁·n₂, d₁·d₂)`.
fn fold_mul(a: &Q, b: &Q) -> (Expr, Q) {
    let raw_n = a.numer() * b.numer();
    let raw_d = a.denom().magnitude() * b.denom().magnitude();
    let prod = a * b;
    (closed_eq_via_sound(&raw_n, &raw_d, &prod), prod)
}

/// `Eq (Rat.neg T) (Rat.mul (-1) T)`, derived from `Rat.neg_neg`,
/// `Rat.neg_mul_neg` and `Rat.one_mul` (there is no registered `neg_eq_neg_one_mul`):
/// `(-1)·T = (-1)·(-(-T)) = 1·(-T) = -T`, then symmetry.
fn neg_eq_neg_one_mul(t: &Expr) -> Option<Expr> {
    let m1 = rat_lit(&q_from_int(-1));
    let one = rat_lit(&q_from_int(1));
    let nt = rat_neg(t.clone());
    let nnt = rat_neg(nt.clone());
    let mut c = Rewriter::chain(rat_mul(m1.clone(), t.clone()));
    c.rw(
        &[Frame::MulR(m1.clone())],
        t.clone(),
        nnt.clone(),
        eq_symm_rat(nnt.clone(), t.clone(), const_app("Rat.neg_neg", [t.clone()])),
    )?;
    c.rw(
        &[],
        rat_mul(m1.clone(), nnt),
        rat_mul(one.clone(), nt.clone()),
        const_app("Rat.neg_mul_neg", [one.clone(), nt.clone()]),
    )?;
    c.rw(&[], rat_mul(one, nt.clone()), nt.clone(), const_app("Rat.one_mul", [nt.clone()]))?;
    Some(eq_symm_rat(rat_mul(m1, t.clone()), nt, c.proof))
}

/// A monomial-shaped term: `x`, `-x`, `c·x`, `x·c`. Rewrites it under `ctx`
/// to the spelling `mono(x, c)` (at most one step) and returns `(x, c)`; a
/// zero coefficient is NOT a monomial (the caller folds it to a literal).
fn as_monomial(r: &mut Rewriter, ctx: &[Frame], t: &RTerm) -> Option<Option<(String, Q)>> {
    let one = q_from_int(1);
    Some(match t {
        RTerm::Var(x) => {
            let xe = var_expr(x);
            // x = 1*x           (Eq.symm (Rat.one_mul x))
            r.rw(
                ctx,
                xe.clone(),
                mono(x, &one),
                eq_symm_rat(
                    rat_mul(k("Rat.one"), xe.clone()),
                    xe.clone(),
                    const_app("Rat.one_mul", [xe]),
                ),
            )?;
            Some((x.clone(), one))
        }
        RTerm::Neg(inner) => match inner.as_ref() {
            RTerm::Var(x) => {
                let xe = var_expr(x);
                let m1 = q_from_int(-1);
                // -x = (-1)*x
                r.rw(ctx, rat_neg(xe.clone()), mono(x, &m1), neg_eq_neg_one_mul(&xe)?)?;
                Some((x.clone(), m1))
            }
            _ => None,
        },
        RTerm::Mul(a, b) => match (a.as_ref(), b.as_ref()) {
            (RTerm::Lit(c), RTerm::Var(x)) if !q_is_zero(c) => Some((x.clone(), c.clone())),
            (RTerm::Var(x), RTerm::Lit(c)) if !q_is_zero(c) => {
                // x*c = c*x   (Rat.mul_comm x c)
                let (xe, lit) = (var_expr(x), rat_lit(c));
                r.rw(
                    ctx,
                    rat_mul(xe.clone(), lit.clone()),
                    rat_mul(lit.clone(), xe.clone()),
                    const_app("Rat.mul_comm", [xe, lit]),
                )?;
                Some((x.clone(), c.clone()))
            }
            _ => None,
        },
        _ => None,
    })
}

/// Under `ctx` the current term is `m + L` with `m = mono(x, c)` and `L` a
/// canonical monomial list; insert `m` at its sorted position (LEFT-COMM to
/// pass a smaller monomial, the shuffle-free `Rat.add_assoc` + `Eq.symm
/// Rat.right_distrib` + fold to combine an equal variable, `Rat.zero_mul` +
/// `Rat.zero_add` if it cancels). Returns the merged list.
fn insert_monomial(
    r: &mut Rewriter,
    ctx: &[Frame],
    x: &str,
    c: &Q,
    list: &[(String, Q)],
) -> Option<Vec<(String, Q)>> {
    let mut ctx = ctx.to_vec();
    let mut out: Vec<(String, Q)> = Vec::with_capacity(list.len() + 1);
    let m = mono(x, c);
    let mut rest: &[(String, Q)] = list;
    loop {
        let Some(((y, d), tail)) = rest.split_first() else {
            // m + 0 is already canonical.
            out.push((x.to_string(), c.clone()));
            return Some(out);
        };
        if x < y.as_str() {
            out.push((x.to_string(), c.clone()));
            out.extend(rest.iter().cloned());
            return Some(out);
        }
        let my = mono(y, d);
        let tail_e = monomial_list(tail);
        if x > y.as_str() {
            // m + (my + R) = my + (m + R)                (left-comm)
            r.rw(
                &ctx,
                rat_add(m.clone(), rat_add(my.clone(), tail_e.clone())),
                rat_add(my.clone(), rat_add(m.clone(), tail_e.clone())),
                left_comm_lemma_app(m.clone(), my.clone(), tail_e),
            )?;
            out.push((y.clone(), d.clone()));
            ctx.push(Frame::AddR(my));
            rest = tail;
            continue;
        }
        // Same variable: c*x + (d*x + R) = (c*x + d*x) + R = (c + d)*x + R.
        let xe = var_expr(x);
        r.rw(
            &ctx,
            rat_add(m.clone(), rat_add(my.clone(), tail_e.clone())),
            rat_add(rat_add(m.clone(), my.clone()), tail_e.clone()),
            eq_symm_rat(
                rat_add(rat_add(m.clone(), my.clone()), tail_e.clone()),
                rat_add(m.clone(), rat_add(my.clone(), tail_e.clone())),
                const_app("Rat.add_assoc", [m.clone(), my.clone(), tail_e.clone()]),
            ),
        )?;
        let ctx_head = with_frame(&ctx, Frame::AddL(tail_e.clone()));
        let (cl, dl) = (rat_lit(c), rat_lit(d));
        let coef_sum = rat_add(cl.clone(), dl.clone());
        r.rw(
            &ctx_head,
            rat_add(m.clone(), my.clone()),
            rat_mul(coef_sum.clone(), xe.clone()),
            eq_symm_rat(
                rat_mul(coef_sum.clone(), xe.clone()),
                rat_add(m, my),
                const_app("Rat.right_distrib", [cl, dl, xe.clone()]),
            ),
        )?;
        let (h, l) = fold_add(c, d);
        r.rw(&with_frame(&ctx_head, Frame::MulL(xe.clone())), coef_sum, rat_lit(&l), h)?;
        if q_is_zero(&l) {
            r.rw(&ctx_head, mono(x, &l), rat_lit(&l), const_app("Rat.zero_mul", [xe]))?;
            r.rw(
                &ctx,
                rat_add(rat_lit(&l), tail_e.clone()),
                tail_e.clone(),
                const_app("Rat.zero_add", [tail_e]),
            )?;
        } else {
            out.push((x.to_string(), l));
        }
        out.extend(tail.iter().cloned());
        return Some(out);
    }
}

/// Normalize the fragment term `t`, which currently sits at `plug(ctx,
/// t.to_kernel())` inside `r.cur`, to its [`Canon`] at the same position.
///
/// A left-nested sum `(a₁ + a₂) + b` is first rotated to `a₁ + (a₂ + b)`
/// (`Rat.add_assoc` on the small original spelling); the right operand of a
/// sum is normalized FIRST and a literal or monomial left operand is then
/// folded / inserted directly into it, so a chain of `n` summands costs O(n)
/// small steps instead of O(n) full merges. Recursion depth is bounded by
/// [`MAX_ROW_NODES`].
fn normalize(r: &mut Rewriter, ctx: &[Frame], t: &RTerm) -> Option<Canon> {
    let zero = q_from_int(0);
    let zero_lit = rat_lit(&zero);
    match t {
        RTerm::Lit(q) => {
            // q = q + 0        (Eq.symm (Rat.add_zero q))
            let qe = rat_lit(q);
            r.rw(
                ctx,
                qe.clone(),
                rat_add(qe.clone(), zero_lit),
                eq_symm_rat(
                    rat_add(qe.clone(), k("Rat.zero")),
                    qe.clone(),
                    const_app("Rat.add_zero", [qe]),
                ),
            )?;
            Some(Canon { parts: Vec::new(), k: q.clone() })
        }
        RTerm::Add(a, b) => {
            if let RTerm::Add(a1, a2) = a.as_ref() {
                // (a1 + a2) + b = a1 + (a2 + b)      (Rat.add_assoc a1 a2 b)
                let (e1, e2, eb) = (a1.to_kernel(), a2.to_kernel(), b.to_kernel());
                r.rw(
                    ctx,
                    rat_add(rat_add(e1.clone(), e2.clone()), eb.clone()),
                    rat_add(e1.clone(), rat_add(e2.clone(), eb.clone())),
                    const_app("Rat.add_assoc", [e1, e2, eb]),
                )?;
                let rotated = RTerm::Add(a1.clone(), Box::new(RTerm::Add(a2.clone(), b.clone())));
                return normalize(r, ctx, &rotated);
            }
            let cb = normalize(r, &with_frame(ctx, Frame::AddR(a.to_kernel())), b)?;
            let (kb, lb) = (rat_lit(&cb.k), monomial_list(&cb.parts));
            if let RTerm::Lit(q) = a.as_ref() {
                // q + (kb + L) = (q + kb) + L, then fold.
                let qe = rat_lit(q);
                r.rw(
                    ctx,
                    rat_add(qe.clone(), rat_add(kb.clone(), lb.clone())),
                    rat_add(rat_add(qe.clone(), kb.clone()), lb.clone()),
                    eq_symm_rat(
                        rat_add(rat_add(qe.clone(), kb.clone()), lb.clone()),
                        rat_add(qe.clone(), rat_add(kb.clone(), lb.clone())),
                        const_app("Rat.add_assoc", [qe.clone(), kb.clone(), lb.clone()]),
                    ),
                )?;
                let (h, sum) = fold_add(q, &cb.k);
                r.rw(&with_frame(ctx, Frame::AddL(lb)), rat_add(qe, kb), rat_lit(&sum), h)?;
                return Some(Canon { parts: cb.parts, k: sum });
            }
            if let Some((x, c)) = as_monomial(r, &with_frame(ctx, Frame::AddL(cb.expr())), a)? {
                // m + (kb + L) = kb + (m + L), then insert m into L.
                let m = mono(&x, &c);
                r.rw(
                    ctx,
                    rat_add(m.clone(), rat_add(kb.clone(), lb.clone())),
                    rat_add(kb.clone(), rat_add(m.clone(), lb.clone())),
                    left_comm_lemma_app(m, kb.clone(), lb),
                )?;
                let parts =
                    insert_monomial(r, &with_frame(ctx, Frame::AddR(kb)), &x, &c, &cb.parts)?;
                return Some(Canon { parts, k: cb.k });
            }
            let ca = normalize(r, &with_frame(ctx, Frame::AddL(cb.expr())), a)?;
            merge(r, ctx, &ca, &cb)
        }
        RTerm::Sub(a, b) => {
            // Rat.sub A B  ≡  Rat.add A (Rat.neg B)  definitionally (Eq.refl).
            let (ae, be) = (a.to_kernel(), b.to_kernel());
            let orig = rat_sub(ae.clone(), be.clone());
            r.rw(ctx, orig.clone(), rat_add(ae, rat_neg(be)), eq_refl_rat(orig))?;
            let rewritten = RTerm::Add(a.clone(), Box::new(RTerm::Neg(b.clone())));
            normalize(r, ctx, &rewritten)
        }
        RTerm::Var(_) | RTerm::Neg(_) | RTerm::Mul(_, _) => {
            if let Some((x, c)) = as_monomial(r, ctx, t)? {
                // m = m + 0 = 0 + (m + 0)
                let m = mono(&x, &c);
                let list = rat_add(m.clone(), zero_lit.clone());
                r.rw(
                    ctx,
                    m.clone(),
                    list.clone(),
                    eq_symm_rat(
                        rat_add(m.clone(), k("Rat.zero")),
                        m.clone(),
                        const_app("Rat.add_zero", [m]),
                    ),
                )?;
                r.rw(
                    ctx,
                    list.clone(),
                    rat_add(zero_lit, list.clone()),
                    eq_symm_rat(
                        rat_add(k("Rat.zero"), list.clone()),
                        list.clone(),
                        const_app("Rat.zero_add", [list]),
                    ),
                )?;
                return Some(Canon { parts: vec![(x, c)], k: zero });
            }
            match t {
                RTerm::Neg(a) => {
                    let ae = a.to_kernel();
                    let m1 = q_from_int(-1);
                    r.rw(
                        ctx,
                        rat_neg(ae.clone()),
                        rat_mul(rat_lit(&m1), ae.clone()),
                        neg_eq_neg_one_mul(&ae)?,
                    )?;
                    let ca = normalize(r, &with_frame(ctx, Frame::MulR(rat_lit(&m1))), a)?;
                    distribute(r, ctx, &m1, &ca)
                }
                RTerm::Mul(a, b) => {
                    let (coef, other) = match (a.as_ref(), b.as_ref()) {
                        (RTerm::Lit(c), o) => (c, o),
                        (o, RTerm::Lit(c)) => {
                            // T*c = c*T   (Rat.mul_comm T c)
                            let (oe, lit) = (o.to_kernel(), rat_lit(c));
                            r.rw(
                                ctx,
                                rat_mul(oe.clone(), lit.clone()),
                                rat_mul(lit.clone(), oe.clone()),
                                const_app("Rat.mul_comm", [oe, lit]),
                            )?;
                            (c, o)
                        }
                        _ => return None,
                    };
                    let lit = rat_lit(coef);
                    if q_is_zero(coef) {
                        // 0*T = 0   (Rat.zero_mul T) — on the ORIGINAL T, no normalization needed.
                        let oe = other.to_kernel();
                        r.rw(
                            ctx,
                            rat_mul(lit.clone(), oe.clone()),
                            lit,
                            const_app("Rat.zero_mul", [oe]),
                        )?;
                        return normalize(r, ctx, &RTerm::Lit(zero));
                    }
                    let co = normalize(r, &with_frame(ctx, Frame::MulR(lit)), other)?;
                    distribute(r, ctx, coef, &co)
                }
                _ => None,
            }
        }
    }
}

/// Under `ctx` the current term is `Rat.mul (lit coef) (nested(parts, k))` with
/// `coef ≠ 0`; push the scalar through (`Rat.left_distrib`, `Eq.symm
/// Rat.mul_assoc`, closed folds — the trailing `c * 0` folds to `0` like any
/// closed product) and collect the scaled monomials. Iterative.
fn distribute(r: &mut Rewriter, ctx: &[Frame], coef: &Q, c: &Canon) -> Option<Canon> {
    let lit = rat_lit(coef);
    let zero = q_from_int(0);
    // c*(k + L) = c*k + c*L                        (Rat.left_distrib c k L)
    let (ke, list) = (rat_lit(&c.k), monomial_list(&c.parts));
    r.rw(
        ctx,
        rat_mul(lit.clone(), rat_add(ke.clone(), list.clone())),
        rat_add(rat_mul(lit.clone(), ke.clone()), rat_mul(lit.clone(), list.clone())),
        const_app("Rat.left_distrib", [lit.clone(), ke.clone(), list.clone()]),
    )?;
    // c*k = (c·k)                                  (closed fold)
    let (h, prod) = fold_mul(coef, &c.k);
    r.rw(
        &with_frame(ctx, Frame::AddL(rat_mul(lit.clone(), list))),
        rat_mul(lit.clone(), ke),
        rat_lit(&prod),
        h,
    )?;
    let mut ctx = with_frame(ctx, Frame::AddR(rat_lit(&prod)));
    let mut out: Vec<(String, Q)> = Vec::with_capacity(c.parts.len());
    let mut rest: &[(String, Q)] = &c.parts;
    loop {
        let Some(((x, cx), tail_parts)) = rest.split_first() else {
            // c*0 = 0                                  (closed fold)
            let (h, z) = fold_mul(coef, &zero);
            r.rw(&ctx, rat_mul(lit, rat_lit(&zero)), rat_lit(&z), h)?;
            return Some(Canon { parts: out, k: prod });
        };
        let m = mono(x, cx);
        let tail = monomial_list(tail_parts);
        // c*(m + R) = c*m + c*R                      (Rat.left_distrib c m R)
        r.rw(
            &ctx,
            rat_mul(lit.clone(), rat_add(m.clone(), tail.clone())),
            rat_add(rat_mul(lit.clone(), m.clone()), rat_mul(lit.clone(), tail.clone())),
            const_app("Rat.left_distrib", [lit.clone(), m.clone(), tail.clone()]),
        )?;
        // c*(cx*x) = (c*cx)*x                        (Eq.symm (Rat.mul_assoc c cx x))
        let ctx_head = with_frame(&ctx, Frame::AddL(rat_mul(lit.clone(), tail)));
        let xe = var_expr(x);
        let cxl = rat_lit(cx);
        r.rw(
            &ctx_head,
            rat_mul(lit.clone(), m),
            rat_mul(rat_mul(lit.clone(), cxl.clone()), xe.clone()),
            eq_symm_rat(
                rat_mul(rat_mul(lit.clone(), cxl.clone()), xe.clone()),
                rat_mul(lit.clone(), rat_mul(cxl.clone(), xe.clone())),
                const_app("Rat.mul_assoc", [lit.clone(), cxl.clone(), xe.clone()]),
            ),
        )?;
        // (c*cx) = L                                 (closed fold)
        let (h, l) = fold_mul(coef, cx);
        r.rw(&with_frame(&ctx_head, Frame::MulL(xe)), rat_mul(lit.clone(), cxl), rat_lit(&l), h)?;
        ctx.push(Frame::AddR(mono(x, &l)));
        out.push((x.clone(), l));
        rest = tail_parts;
    }
}

/// Under `ctx` the current term is `Rat.add (nested(pa, ka)) (nested(pb, kb))`;
/// merge into one canonical form: the constants meet at the root by one
/// shuffle and fold, then the two sorted monomial lists merge (`Rat.add_assoc`
/// to pass a monomial, `Rat.add_comm` to swap sides, the shuffle plus `Eq.symm
/// Rat.right_distrib` and a closed fold to combine a shared variable — with
/// `Rat.zero_mul` + `Rat.zero_add` when it cancels — and one `Rat.add_zero` /
/// `Rat.zero_add` when a list is exhausted). Iterative.
fn merge(r: &mut Rewriter, ctx: &[Frame], a: &Canon, b: &Canon) -> Option<Canon> {
    enum Step {
        BothDone,
        ADone,
        BDone,
        TakeA,
        Swap,
        Same,
    }
    let zero = rat_lit(&q_from_int(0));
    // (ka + LA) + (kb + LB) = (ka + kb) + (LA + LB)      (shuffle)
    let (kae, kbe) = (rat_lit(&a.k), rat_lit(&b.k));
    let (la, lb) = (monomial_list(&a.parts), monomial_list(&b.parts));
    let lists = rat_add(la.clone(), lb.clone());
    r.rw(
        ctx,
        rat_add(rat_add(kae.clone(), la.clone()), rat_add(kbe.clone(), lb.clone())),
        rat_add(rat_add(kae.clone(), kbe.clone()), lists.clone()),
        shuffle_lemma_app(kae.clone(), la, kbe.clone(), lb),
    )?;
    // ka + kb = K                                         (closed fold)
    let (h, kk) = fold_add(&a.k, &b.k);
    r.rw(&with_frame(ctx, Frame::AddL(lists)), rat_add(kae, kbe), rat_lit(&kk), h)?;

    let mut ctx = with_frame(ctx, Frame::AddR(rat_lit(&kk)));
    let mut out: Vec<(String, Q)> = Vec::with_capacity(a.parts.len() + b.parts.len());
    let (mut pa, mut pb): (&[(String, Q)], &[(String, Q)]) = (&a.parts, &b.parts);
    loop {
        let a_all = monomial_list(pa);
        let b_all = monomial_list(pb);
        let step = match (pa.first(), pb.first()) {
            (None, None) => Step::BothDone,
            (Some(_), None) => Step::BDone,
            (None, Some(_)) => Step::ADone,
            (Some((xa, _)), Some((xb, _))) => {
                if xa < xb {
                    Step::TakeA
                } else if xa > xb {
                    Step::Swap
                } else {
                    Step::Same
                }
            }
        };
        match step {
            Step::BothDone => {
                // 0 + 0 = 0                                  (Rat.zero_add 0)
                r.rw(
                    &ctx,
                    rat_add(zero.clone(), zero.clone()),
                    zero,
                    const_app("Rat.zero_add", [a_all]),
                )?;
                return Some(Canon { parts: out, k: kk });
            }
            Step::BDone => {
                // LA + 0 = LA                                (Rat.add_zero LA)
                r.rw(
                    &ctx,
                    rat_add(a_all.clone(), zero),
                    a_all.clone(),
                    const_app("Rat.add_zero", [a_all]),
                )?;
                out.extend(pa.iter().cloned());
                return Some(Canon { parts: out, k: kk });
            }
            Step::ADone => {
                // 0 + LB = LB                                (Rat.zero_add LB)
                r.rw(
                    &ctx,
                    rat_add(zero, b_all.clone()),
                    b_all.clone(),
                    const_app("Rat.zero_add", [b_all]),
                )?;
                out.extend(pb.iter().cloned());
                return Some(Canon { parts: out, k: kk });
            }
            Step::TakeA => {
                // (ma + RA) + LB = ma + (RA + LB)            (Rat.add_assoc)
                let ((xa, ca), ra) = pa.split_first()?;
                let ma = mono(xa, ca);
                let rest_a = monomial_list(ra);
                r.rw(
                    &ctx,
                    rat_add(a_all, b_all.clone()),
                    rat_add(ma.clone(), rat_add(rest_a.clone(), b_all.clone())),
                    const_app("Rat.add_assoc", [ma.clone(), rest_a, b_all]),
                )?;
                out.push((xa.clone(), ca.clone()));
                ctx.push(Frame::AddR(ma));
                pa = ra;
            }
            Step::Swap => {
                // LA + LB = LB + LA, then continue with the roles swapped.
                r.rw(
                    &ctx,
                    rat_add(a_all.clone(), b_all.clone()),
                    rat_add(b_all.clone(), a_all.clone()),
                    const_app("Rat.add_comm", [a_all, b_all]),
                )?;
                std::mem::swap(&mut pa, &mut pb);
            }
            Step::Same => {
                // (ma + RA) + (mb + RB) = (ma + mb) + (RA + RB)   (shuffle)
                let ((x, ca), ra) = pa.split_first()?;
                let ((_, cb), rb) = pb.split_first()?;
                let xe = var_expr(x);
                let (ma, mb) = (mono(x, ca), mono(x, cb));
                let (rest_a, rest_b) = (monomial_list(ra), monomial_list(rb));
                let rests = rat_add(rest_a.clone(), rest_b.clone());
                r.rw(
                    &ctx,
                    rat_add(a_all, b_all),
                    rat_add(rat_add(ma.clone(), mb.clone()), rests.clone()),
                    shuffle_lemma_app(ma.clone(), rest_a, mb.clone(), rest_b),
                )?;
                // ca*x + cb*x = (ca + cb)*x              (Eq.symm (Rat.right_distrib))
                let ctx_head = with_frame(&ctx, Frame::AddL(rests.clone()));
                let (cal, cbl) = (rat_lit(ca), rat_lit(cb));
                let coef_sum = rat_add(cal.clone(), cbl.clone());
                r.rw(
                    &ctx_head,
                    rat_add(ma.clone(), mb.clone()),
                    rat_mul(coef_sum.clone(), xe.clone()),
                    eq_symm_rat(
                        rat_mul(coef_sum.clone(), xe.clone()),
                        rat_add(ma, mb),
                        const_app("Rat.right_distrib", [cal, cbl, xe.clone()]),
                    ),
                )?;
                // (ca + cb) = L                          (closed fold)
                let (h, l) = fold_add(ca, cb);
                r.rw(&with_frame(&ctx_head, Frame::MulL(xe.clone())), coef_sum, rat_lit(&l), h)?;
                if q_is_zero(&l) {
                    // 0*x = 0       (Rat.zero_mul x)
                    r.rw(&ctx_head, mono(x, &l), rat_lit(&l), const_app("Rat.zero_mul", [xe]))?;
                    // 0 + R = R     (Rat.zero_add R)
                    r.rw(
                        &ctx,
                        rat_add(rat_lit(&l), rests.clone()),
                        rests.clone(),
                        const_app("Rat.zero_add", [rests]),
                    )?;
                } else {
                    out.push((x.clone(), l.clone()));
                    ctx.push(Frame::AddR(mono(x, &l)));
                }
                pa = ra;
                pb = rb;
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The Farkas replay term.
// ---------------------------------------------------------------------------

/// Build a kernel term of type `False` in the hypothesis context, or `None`
/// (fail closed) when no rational Farkas witness exists, any construction step
/// disagrees with its own bookkeeping, or a resource cap is hit.
///
/// Shape: for every row with a positive multiplier, `0 ≤ λᵢ·Bᵢ − λᵢ·Aᵢ` (or
/// `0 <`, for the ONE strict row kept strict) is normalized in place to `0 ≤
/// Dᵢ` with `Dᵢ` canonical; the facts are then folded left to right with
/// `Rat.add_le_add` / `Rat.add_lt_add_of_lt_of_le` (`0 + 0 ≤ Acc + Dᵢ`, the left
/// side rewritten to `0` by `Rat.add_zero`) and the running sum merged in place
/// to canonical form, ending at `0 ≤ K` / `0 < K` with `K` a false literal,
/// closed by the `Int` order lemmas on the cross product.
fn farkas_refutation_real(atoms: &[RealAtom<'_>], hyps: &[Hyp]) -> Option<Expr> {
    if atoms.len() != hyps.len() || atoms.is_empty() {
        return None;
    }
    // Row per atom: `0 ≤ B − A` (weak) / `0 < B − A` (strict).
    let rows: Vec<(RLin, bool)> = atoms
        .iter()
        .map(|ra| (ra.rhs.linform().add(&ra.lhs.linform().scale(&q_from_int(-1))), ra.strict))
        .collect();
    let (mult, mut strict_residual) = find_farkas_multipliers_real(&rows)?;
    if mult.len() != atoms.len() || mult.iter().any(q_is_neg) {
        return None;
    }

    // Row order: the ONE strict row kept strict goes first (Motzkin), then the
    // rest ascending; every other strict row is weakened by `Rat.le_of_lt`.
    let positive: Vec<usize> = (0..atoms.len()).filter(|&i| q_is_pos(&mult[i])).collect();
    let designated = positive.iter().copied().find(|&i| atoms[i].strict);
    if designated.is_none() {
        strict_residual = false;
    }
    // Row order: the kept-strict row first (it seeds the strict fact), then the
    // rest by DECREASING width (ties by index) — the running sum then starts at
    // its widest and every later row cancels into it, instead of growing it.
    let mut order: Vec<usize> = Vec::with_capacity(positive.len());
    if strict_residual {
        order.push(designated?);
    }
    let mut rest: Vec<usize> =
        positive.iter().copied().filter(|&i| !(strict_residual && Some(i) == designated)).collect();
    rest.sort_by(|&i, &j| rows[j].0.terms.len().cmp(&rows[i].0.terms.len()).then(i.cmp(&j)));
    order.extend(rest);
    if order.is_empty() {
        return None;
    }

    let one = q_from_int(1);
    let zero = k("Rat.zero");
    let mut acc: Option<(Rewriter, Canon)> = None;
    // Every row's proof is nested under all the steps the running sum takes
    // AFTER it was merged, so the deepest point of the final term is the
    // longest row spine plus the whole accumulated spine.
    let mut deepest_row = 0usize;
    for &i in &order {
        let ra = &atoms[i];
        let (a, b) = (ra.lhs.to_kernel(), ra.rhs.to_kernel());
        let h = Expr::fvar(hyps[i].fvar);
        let keep_strict = strict_residual && Some(i) == designated;
        if keep_strict && acc.is_some() {
            return None;
        }
        let base = if ra.strict && !keep_strict {
            const_app("Rat.le_of_lt", [a.clone(), b.clone(), h])
        } else {
            h
        };
        let lam = &mult[i];
        let (l, r, lt, rt, proof) = if *lam == one {
            (a, b, ra.lhs.clone(), ra.rhs.clone(), base)
        } else {
            let lam_e = rat_lit(lam);
            let (la, lb) = (rat_mul(lam_e.clone(), a.clone()), rat_mul(lam_e.clone(), b.clone()));
            // λ = n/d with n ≥ 1: `0 ≤ λ` is `Int.NonNeg n`, `0 < λ` is `Int.NonNeg (n-1)`.
            let n = lam.numer().magnitude();
            let scaled = if keep_strict {
                let pos = nonneg_mk_big(&(n - BigUint::from(1u32)));
                const_app("Rat.mul_lt_mul_of_pos_left", [lam_e, a, b, base, pos])
            } else {
                const_app("Rat.mul_le_mul_of_nonneg_left", [lam_e, a, b, base, nonneg_mk_big(n)])
            };
            let lt = RTerm::Mul(Box::new(RTerm::Lit(lam.clone())), Box::new(ra.lhs.clone()));
            let rt = RTerm::Mul(Box::new(RTerm::Lit(lam.clone())), Box::new(ra.rhs.clone()));
            (la, lb, lt, rt, scaled)
        };
        // 0 ≤ R − L  (or 0 < R − L), normalized in place on this row's own fact.
        let diff_lemma = if keep_strict { "Rat.sub_pos_of_lt" } else { "Rat.sub_nonneg_of_le" };
        let hdiff = const_app(diff_lemma, [l.clone(), r.clone(), proof]);
        let mut row = Rewriter::fact(keep_strict, rat_sub(r, l), hdiff);
        let canon = normalize(&mut row, &[], &RTerm::Sub(Box::new(rt), Box::new(lt)))?;
        if canon.expr() != row.cur {
            return None;
        }
        deepest_row = deepest_row.max(row.steps);
        acc = Some(match acc {
            None => (row, canon),
            Some((prev, prev_canon)) => {
                if prev.steps + row.steps + 4 > MAX_CHAIN_STEPS
                    || prev.nodes + row.nodes > NODE_BUDGET
                {
                    return None;
                }
                let strict = prev.strict();
                let lemma = if strict { "Rat.add_lt_add_of_lt_of_le" } else { "Rat.add_le_add" };
                let sum = rat_add(prev.cur.clone(), row.cur.clone());
                let (steps, nodes) =
                    (prev.steps + 2, prev.nodes + row.nodes + 2 * expr_nodes(&sum));
                let proof = const_app(
                    lemma,
                    [zero.clone(), prev.cur, zero.clone(), row.cur, prev.proof, row.proof],
                );
                let mut f = Rewriter::fact(strict, sum, proof);
                f.steps = steps;
                f.nodes = nodes;
                // 0 + 0 = 0   (Rat.add_zero 0) on the left.
                f.rw_left(
                    rat_add(zero.clone(), zero.clone()),
                    zero.clone(),
                    const_app("Rat.add_zero", [zero.clone()]),
                )?;
                let merged = merge(&mut f, &[], &prev_canon, &canon)?;
                if merged.expr() != f.cur {
                    return None;
                }
                (f, merged)
            }
        });
    }
    let (mut acc, canon) = acc?;
    if !canon.parts.is_empty() || acc.cur != canon.expr() {
        return None;
    }
    if acc.steps + deepest_row + 8 > MAX_CHAIN_STEPS {
        return None;
    }
    let kq = canon.k;
    if !residual_is_false(&kq, strict_residual) {
        return None;
    }
    // K + 0 = K   (Rat.add_zero K): the fact is now `rel 0 K` on a bare literal.
    let ke = rat_lit(&kq);
    acc.rw(
        &[],
        rat_add(ke.clone(), rat_lit(&q_from_int(0))),
        ke.clone(),
        const_app("Rat.add_zero", [ke]),
    )?;
    let refuted = acc.proof;

    // `Rat.le 0 (n/d)` reduces to `Int.le 0 n` and `Rat.lt 0 (n/d)` to
    // `Int.lt 0 n`; close with the Int order lemmas on the literal cross-products.
    let n = kq.numer();
    let (zero, ne) = (int_big(&BigInt::from(0)), int_big(n));
    let body = if strict_residual {
        // h : 0 < n with n ≤ 0:  Int.lt_irrefl 0 (Int.lt_of_lt_of_le 0 n 0 h (NonNeg.mk (0-n)))
        let pos = nonneg_mk_big(n.magnitude());
        let lt00 = const_app("Int.lt_of_lt_of_le", [zero.clone(), ne, zero.clone(), refuted, pos]);
        Expr::app(const_app("Int.lt_irrefl", [zero]), lt00)
    } else {
        // h : 0 ≤ n with n < 0:  Int.lt_irrefl n (Int.lt_of_lt_of_le n 0 n (NonNeg.mk (-n-1)) h)
        let pos = nonneg_mk_big(&(n.magnitude() - BigUint::from(1u32)));
        let ltnn = const_app("Int.lt_of_lt_of_le", [ne.clone(), zero, ne.clone(), pos, refuted]);
        Expr::app(const_app("Int.lt_irrefl", [ne]), ltnn)
    };
    // Bind the two rearrangement lemmas the spine uses (`bvar 1` = shuffle,
    // `bvar 0` = left-comm) at the root.
    let inner = Expr::app(
        Expr::lam(BinderInfo::Default, left_comm_lemma_type(), body),
        left_comm_lemma_proof()?,
    );
    let outer = Expr::lam(BinderInfo::Default, shuffle_lemma_type(), inner);
    Some(Expr::app(outer, shuffle_lemma_proof()?))
}

// ---------------------------------------------------------------------------
// Environment.
// ---------------------------------------------------------------------------

/// The Real lane's shared lemma environment: the Int lane's [`base_env`] plus
/// the registrars that carry every `Rat` order/monotonicity theorem the replay
/// names (`init_nn_verify_rat_ordering` for `Rat.sub_nonneg_of_le`;
/// `init_algebra_rat_add_lt_add_mixed` for `Rat.add_lt_add_of_lt_of_le` and,
/// transitively, `Rat.le_of_lt`, `Rat.add_le_add`,
/// `Rat.mul_le_mul_of_nonneg_left`, `Rat.mul_lt_mul_of_pos_left`,
/// `Rat.sub_pos_of_lt`, `Rat.neg_neg`, `Rat.neg_mul_neg`). A SEPARATE
/// process-global so the Int lane's environment — and the lemma-vocabulary pin
/// on it — is untouched. Every added declaration is a kernel-checked theorem.
pub(super) fn real_base_env() -> Option<&'static Environment> {
    static REAL_BASE_ENV: std::sync::OnceLock<Option<Environment>> = std::sync::OnceLock::new();
    REAL_BASE_ENV
        .get_or_init(|| {
            let mut env = base_env()?.clone();
            env.init_nn_verify_rat_ordering().ok()?;
            env.init_algebra_rat_add_lt_add_mixed().ok()?;
            Some(env)
        })
        .as_ref()
}

/// KR0 switch: the Clean reference entry over the Real lane's base
/// environment (no skolems; their type is `Rat`), built once per process.
pub(crate) fn real_reference() -> Option<&'static crate::reference_mint::CarrierReference> {
    static REAL_REFERENCE: std::sync::OnceLock<Option<crate::reference_mint::CarrierReference>> =
        std::sync::OnceLock::new();
    REAL_REFERENCE
        .get_or_init(|| crate::reference_mint::carrier_reference("real", real_base_env(), rat_ty()))
        .as_ref()
}

/// The Real lane's kernel environment: the shared lemma env plus a `Rat`-typed
/// axiom per free variable. Producer and consumer share this. A variable whose
/// encoded name collides with a kernel constant (or with another variable's
/// encoding) fails `add_decl` and the lane declines.
pub(crate) fn build_env_real(var_names: &BTreeSet<String>) -> Option<Environment> {
    let mut env = real_base_env()?.clone();
    for name in var_names {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(&encoded_var_name(name)),
            level_params: vec![],
            type_: rat_ty(),
        })
        .ok()?;
    }
    Some(env)
}

// ---------------------------------------------------------------------------
// The lane.
// ---------------------------------------------------------------------------

/// The heavy half of the lane: hypotheses, the Farkas search (deterministic
/// and budgeted — no solver is consulted before it, see the module banner,
/// ORDER OF WORK), replay, the proof codec gate, and (inside
/// [`finish_certificate_carrier`]) the single ay cross-check, the kernel
/// re-check and the payload round-trip. Runs on the large-stack thread
/// [`run_on_real_lane_stack`] spawns.
fn certify_real_atoms(
    atoms: &[RealAtom<'_>],
    var_names: &BTreeSet<String>,
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    let hyps = real_hyps_from_atoms(atoms);
    let term = farkas_refutation_real(atoms, &hyps)?;
    // Exact codec gate BEFORE the kernel check: a term the consumer's codec
    // would refuse (node or depth limit) is never kernel-checked.
    serialize_term(&term).ok()?;
    finish_certificate_carrier(
        &hyps,
        &term,
        var_names,
        identity,
        AyCrossCheck::Required,
        Carrier::Real,
    )
}

/// The generic linear-REAL fragment certificate path. Inert (`None`, no work,
/// no thread) on Int obligations — see the module banner. Everything after
/// atom collection runs on a dedicated [`REAL_LANE_STACK_BYTES`] thread; a
/// thread that cannot be spawned or that panics is a clean `None`.
pub(crate) fn certify_linear_real_fragment(
    conjuncts: &[&Formula],
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    let (atoms, var_names) = collect_real_atoms(conjuncts)?;
    if atoms.len() > MAX_REAL_ATOMS {
        return None;
    }
    run_on_real_lane_stack(|| certify_real_atoms(&atoms, &var_names, identity))
}

/// The lane's [`REAL_LANE_STACK_BYTES`] thread, through
/// [`crate::on_stack_carrying_stop`]: the stop its ay cross-check records on
/// that thread reaches the run that consumed the lane, so a decline an
/// abstaining ay caused is never memoized (plan P4, T4.2).
pub(crate) fn run_on_real_lane_stack<T: Send>(
    work: impl FnOnce() -> Option<T> + Send,
) -> Option<T> {
    crate::on_stack_carrying_stop("trust-certify-real-lane", REAL_LANE_STACK_BYTES, work)
}

/// The dense SATISFIABLE 12-variable pool of
/// `resource_and_scale_regressions::dense_satisfiable_pool_declines_quickly`
/// — `xᵢ ≥ 0`, `Σxᵢ ≤ 1`, and 15 dense mixed-sign noise rows `Σ cᵢxᵢ ≤ 50 + j`
/// with coefficients cycling through `−1, 2, 1` (no contradiction: all
/// `xᵢ = 0` is a model), 28 rows. Shared with `simplex_farkas_tests`, which
/// checks the search's verdict on exactly this pool.
#[cfg(test)]
fn dense_satisfiable_pool_12() -> Formula {
    fn b(f: Formula) -> Box<Formula> {
        Box::new(f)
    }
    fn rv(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Real)
    }
    let names: Vec<String> = (0..12).map(|i| format!("d{i:02}")).collect();
    let mut rows: Vec<Formula> =
        names.iter().map(|nm| Formula::Ge(b(rv(nm)), b(Formula::rat_from_int(0)))).collect();
    let sum = names[1..].iter().fold(rv(&names[0]), |acc, nm| Formula::Add(b(acc), b(rv(nm))));
    rows.push(Formula::Le(b(sum), b(Formula::rat_from_int(1))));
    for j in 0..15usize {
        let coeffs = [-1i128, 2, 1];
        let lhs = names
            .iter()
            .enumerate()
            .map(|(i, nm)| Formula::Mul(b(Formula::rat_from_int(coeffs[(i + j) % 3])), b(rv(nm))))
            .reduce(|acc, t| Formula::Add(b(acc), b(t)))
            .expect("12 terms");
        rows.push(Formula::Le(b(lhs), b(Formula::rat_from_int(50 + j as i128))));
    }
    assert_eq!(rows.len(), 28);
    Formula::And(rows)
}

#[cfg(test)]
mod real_fragment_tests {
    use clean_kernel::env::ConstantKind;
    use trust_ir::ProofEvidence;

    use super::super::{
        certify_lanes, certify_violation, collect_const_names, deserialize_term,
        normalize_violation, proof_axiom_closure_is_clean, proof_axiom_closure_is_clean_for,
        recheck_cleancic,
    };
    use super::*;

    fn rv(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Real)
    }
    fn iv(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }
    fn q(num: &str, den: &str) -> Formula {
        Formula::rat(num, den).expect("canonical literal")
    }
    fn qi(n: i128) -> Formula {
        Formula::rat_from_int(n)
    }
    fn b(f: Formula) -> Box<Formula> {
        Box::new(f)
    }
    fn mul(a: Formula, x: Formula) -> Formula {
        Formula::Mul(b(a), b(x))
    }
    fn add(a: Formula, c: Formula) -> Formula {
        Formula::Add(b(a), b(c))
    }
    fn le(a: Formula, c: Formula) -> Formula {
        Formula::Le(b(a), b(c))
    }
    fn lt(a: Formula, c: Formula) -> Formula {
        Formula::Lt(b(a), b(c))
    }
    fn ge(a: Formula, c: Formula) -> Formula {
        Formula::Ge(b(a), b(c))
    }
    fn gt(a: Formula, c: Formula) -> Formula {
        Formula::Gt(b(a), b(c))
    }
    fn and(v: Vec<Formula>) -> Formula {
        Formula::And(v)
    }

    /// `Σ aᵢ·xᵢ ⋈ k` over `Real` with integer data spelled as `Rat` literals.
    fn row(kind: &str, terms: &[(&str, i128)], k: i128) -> Formula {
        let mut lhs: Option<Formula> = None;
        for (x, a) in terms {
            let t = if *a == 1 { rv(x) } else { mul(qi(*a), rv(x)) };
            lhs = Some(match lhs {
                None => t,
                Some(acc) => add(acc, t),
            });
        }
        let lhs = lhs.unwrap_or_else(|| qi(0));
        match kind {
            "le" => le(lhs, qi(k)),
            "lt" => lt(lhs, qi(k)),
            "ge" => ge(lhs, qi(k)),
            "gt" => gt(lhs, qi(k)),
            "eq" => Formula::Eq(b(lhs), b(qi(k))),
            _ => unreachable!(),
        }
    }

    fn certified(violation: &Formula, what: &str) -> (Vec<u8>, Vec<u8>, trust_ir::ProofDigest) {
        match certify_violation(violation) {
            Some(ProofEvidence::CleanCic { term, context, lineage, .. }) => {
                assert!(
                    recheck_cleancic(&term, &context, &lineage, violation),
                    "{what}: the consumer-side recheck must accept the producer's bytes"
                );
                (term, context, lineage)
            }
            other => panic!("{what}: expected Some(CleanCic), got {other:?}"),
        }
    }

    /// Run the lane DIRECTLY (bypassing every other rung) on a violation.
    fn lane(violation: &Formula) -> Option<ProofEvidence> {
        let normalized = normalize_violation(violation).expect("normalizes");
        let conjuncts = normalized.view();
        let identity = ObligationIdentity::from_violation(violation).expect("identity");
        certify_linear_real_fragment(&conjuncts, &identity)
    }

    /// (SOUNDNESS, RED FIRST) `2x ≥ 1 ∧ 2x ≤ 1` and `0 < x ∧ x < 1` are
    /// integer-infeasible but real-FEASIBLE (`x = 1/2`): over `Sort::Real` with
    /// `Rat` literals they must NOT certify — while the SAME `0 < x ∧ x < 1`
    /// over `Sort::Int` with `Int` literals keeps certifying, because for
    /// integer variables integer infeasibility IS the theorem (the Int lane's
    /// `tighten_strict_int_bounds` is correct there). The Int spelling of
    /// `2x ≥ 1 ∧ 2x ≤ 1` is pinned only as OUTSIDE this lane: the Int lane
    /// declines it today (its refutation needs an integrality cut no Int rung
    /// supplies — a pre-existing limit, measured, not a change), and this lane
    /// must neither certify nor touch it.
    #[test]
    fn real_feasible_integer_infeasible_systems_are_not_certified() {
        let half_open = and(vec![ge(mul(qi(2), rv("x")), qi(1)), le(mul(qi(2), rv("x")), qi(1))]);
        assert!(
            certify_violation(&half_open).is_none(),
            "2x ≥ 1 ∧ 2x ≤ 1 has the real solution 1/2"
        );
        let unit = and(vec![lt(qi(0), rv("x")), lt(rv("x"), qi(1))]);
        assert!(certify_violation(&unit).is_none(), "0 < x < 1 has real solutions");
        let unit_neg = and(vec![gt(rv("x"), qi(0)), Formula::Not(b(ge(rv("x"), qi(1))))]);
        assert!(certify_violation(&unit_neg).is_none(), "negated-atom spelling of 0 < x < 1");

        let int_unit = and(vec![lt(Formula::Int(0), iv("x")), lt(iv("x"), Formula::Int(1))]);
        assert!(lane(&int_unit).is_none(), "the Real lane is inert on the Int spelling");
        assert!(certify_violation(&int_unit).is_some(), "over Int, 0 < x < 1 is infeasible");
        let two = || Formula::Int(2);
        let int_half_open = and(vec![
            ge(Formula::Mul(b(two()), b(iv("x"))), Formula::Int(1)),
            le(Formula::Mul(b(two()), b(iv("x"))), Formula::Int(1)),
        ]);
        assert!(lane(&int_half_open).is_none(), "the Real lane is inert on the Int spelling");
    }

    /// A satisfiable multi-variable system (corpus `mip-46963-000012` with its
    /// binding bound relaxed) must fail closed.
    #[test]
    fn satisfiable_real_systems_are_not_certified() {
        let relaxed = and(vec![
            row("le", &[("x0", 1)], 1),
            row("ge", &[("x0", 2), ("x1", -1)], -3),
            row("ge", &[("x1", 1)], 0),
        ]);
        assert!(certify_violation(&relaxed).is_none());
        let feasible_rational = and(vec![le(mul(q("1", "2"), rv("x")), qi(1)), ge(rv("x"), qi(2))]);
        assert!(certify_violation(&feasible_rational).is_none(), "(1/2)x ≤ 1 ∧ x ≥ 2 has x = 2");
        let two_strict_ok = and(vec![lt(rv("x"), rv("y")), lt(rv("y"), add(rv("x"), qi(1)))]);
        assert!(certify_violation(&two_strict_ok).is_none(), "x < y < x + 1 is satisfiable");
    }

    /// `x ≤ 1 ∧ x ≥ 2` — the interval shape — certifies as a kernel-checked
    /// `CleanCic` and the public rechecker accepts it.
    #[test]
    fn certifies_interval_contradiction() {
        certified(&and(vec![le(rv("x"), qi(1)), ge(rv("x"), qi(2))]), "x ≤ 1 ∧ x ≥ 2");
    }

    /// Genuinely rational data (`(1/2)x ≤ 1 ∧ (1/3)x ≥ 7/6`, i.e. `x ≤ 2 ∧ x ≥
    /// 7/2`) certifies with the rationals carried EXACTLY into the kernel term —
    /// the multipliers are realized by scaling, not repetition.
    #[test]
    fn certifies_rational_coefficient_system() {
        certified(
            &and(vec![
                le(mul(q("1", "2"), rv("x")), qi(1)),
                ge(mul(q("1", "3"), rv("x")), q("7", "6")),
            ]),
            "(1/2)x ≤ 1 ∧ (1/3)x ≥ 7/6",
        );
        // Literal on the right of the product, and a `Sub`/`Neg` spelling.
        certified(
            &and(vec![
                le(mul(rv("x"), q("1", "2")), qi(1)),
                ge(mul(rv("x"), q("1", "3")), q("7", "6")),
            ]),
            "x·(1/2) ≤ 1 ∧ x·(1/3) ≥ 7/6",
        );
        certified(
            &and(vec![
                le(Formula::Sub(b(rv("x")), b(rv("y"))), qi(-1)),
                le(Formula::Neg(b(Formula::Sub(b(rv("x")), b(rv("y"))))), qi(0)),
            ]),
            "x − y ≤ −1 ∧ −(x − y) ≤ 0",
        );
    }

    /// STRICT rows stay strict: `x ≥ 1 ∧ x < 1` and `x > 0 ∧ x ≤ 0` are
    /// infeasible ONLY because `<` is strict (weakening gives the satisfiable
    /// `x = 1` / `x = 0`), so a certificate proves the Motzkin residual `0 < 0`
    /// is what the lane closes.
    #[test]
    fn certifies_strict_row_infeasibility() {
        certified(&and(vec![ge(rv("x"), qi(1)), lt(rv("x"), qi(1))]), "x ≥ 1 ∧ x < 1");
        certified(&and(vec![gt(rv("x"), qi(0)), le(rv("x"), qi(0))]), "x > 0 ∧ x ≤ 0");
        // Two strict rows: x < y ∧ y < x. One is kept strict, the other weakened.
        certified(&and(vec![lt(rv("x"), rv("y")), lt(rv("y"), rv("x"))]), "x < y ∧ y < x");
        // A strict row with a NON-unit multiplier (scaled by `Rat.mul_lt_mul_of_pos_left`).
        certified(
            &and(vec![lt(mul(qi(2), rv("x")), qi(2)), ge(mul(qi(3), rv("x")), qi(3))]),
            "2x < 2 ∧ 3x ≥ 3",
        );
    }

    /// The four `mip-46963-*` corpus systems (all-integer ReLU-encoding Farkas
    /// witnesses, negative coefficients, multi-variable combinations)
    /// transcribed over `Real`/`Rat` — each certifies.
    #[test]
    fn certifies_mip_46963_corpus_systems() {
        type C<'a> = (&'a str, i128, &'a [(&'a str, i128)]);
        let c000012: Vec<C> = vec![
            ("le", 1, &[("x0", 1)]),
            ("ge", -3, &[("x0", 2), ("x1", -1)]),
            ("ge", 10, &[("x1", 1)]),
        ];
        let c000021: Vec<C> = vec![
            ("le", 1, &[("x1", 1)]),
            ("le", 1, &[("x5", 1)]),
            ("ge", 0, &[("x1", 1), ("x3", -1)]),
            ("ge", 0, &[("x3", 1), ("x5", 1), ("x8", -1)]),
            ("ge", 10, &[("x8", 1)]),
        ];
        let c000022 = c000021.clone();
        let c000023: Vec<C> = vec![
            ("le", 1, &[("x0", 1)]),
            ("le", 1, &[("x1", 1)]),
            ("ge", 1, &[("x6", 1)]),
            ("ge", 0, &[("x1", 1), ("x3", -1)]),
            ("ge", 1, &[("x0", 1), ("x1", 1), ("x4", -1)]),
            ("le", 1, &[("x4", -1), ("x5", 1), ("x6", 1)]),
            ("ge", 0, &[("x3", 1), ("x5", 1), ("x8", -1)]),
            ("ge", 10, &[("x8", 1)]),
        ];
        for (name, system) in [
            ("mip-46963-000012", &c000012),
            ("mip-46963-000021", &c000021),
            ("mip-46963-000022", &c000022),
            ("mip-46963-000023", &c000023),
        ] {
            let violation =
                and(system.iter().map(|(kind, k, terms)| row(kind, terms, *k)).collect());
            certified(&violation, name);
        }
    }

    /// Arbitrary-precision literals: `((2^200+1)/3)·x ≤ 1 ∧ x ≥ 3` is infeasible
    /// (`2^200+1 > 1`) and the 200-bit numerator rides into the kernel term as a
    /// `BigNat` literal.
    #[test]
    fn certifies_big_literal_system() {
        let big = (BigInt::from(1) << 200u32) + BigInt::from(1);
        let violation =
            and(vec![le(mul(q(&big.to_string(), "3"), rv("x")), qi(1)), ge(rv("x"), qi(3))]);
        certified(&violation, "big literal");
    }

    /// An `Eq` row is two `≤` rows: `x = 1 ∧ x ≥ 2` certifies.
    #[test]
    fn certifies_equality_row() {
        certified(
            &and(vec![Formula::Eq(b(rv("x")), b(qi(1))), ge(rv("x"), qi(2))]),
            "x = 1 ∧ x ≥ 2",
        );
    }

    /// The CROWN shape: a strict negated-property row against a bound,
    /// `y ≤ 2x ∧ x ≤ 1/2 ∧ y > 1` (needs multipliers 1, 2, 1 and the strict row).
    #[test]
    fn certifies_crown_shape() {
        let crown = and(vec![
            le(rv("y"), mul(qi(2), rv("x"))),
            le(rv("x"), q("1", "2")),
            gt(rv("y"), qi(1)),
        ]);
        certified(&crown, "crown");
    }

    /// The certificate is a function of the obligation alone: two UNCACHED runs
    /// (the memo is bypassed, so this really exercises the producer twice)
    /// yield identical bytes, the rechecker accepts them, and a tampered term
    /// is refused.
    #[test]
    fn certificates_are_deterministic_and_tamper_evident() {
        let violation = and(vec![
            le(mul(q("1", "2"), rv("x")), qi(1)),
            ge(mul(q("1", "3"), rv("x")), q("7", "6")),
        ]);
        let identity = ObligationIdentity::from_violation(&violation).expect("identity");
        let a = certify_lanes(&violation, &identity).expect("certifies");
        let b2 = certify_lanes(&violation, &identity).expect("certifies");
        assert_eq!(a, b2, "certificate bytes must be deterministic across uncached runs");
        let (term, context, lineage) = certified(&violation, "determinism");
        assert!(
            matches!(&a, ProofEvidence::CleanCic { term: t, .. } if *t == term),
            "the memoized payload is the uncached payload"
        );
        let mut tampered = term.clone();
        tampered.push(0);
        assert!(
            !recheck_cleancic(&tampered, &context, &lineage, &violation),
            "tampered term refused"
        );
        let other = and(vec![le(rv("x"), qi(1)), ge(rv("x"), qi(2))]);
        assert!(
            !recheck_cleancic(&term, &context, &lineage, &other),
            "a certificate is bound to its own obligation"
        );
    }

    /// CLOSURE AUDIT: the regenerated term's transitive constant closure holds
    /// only the foundational axioms (now including `Quot.ind`) and the
    /// obligation's own `Rat` skolems — under the REAL carrier. Under the INT
    /// carrier the very same `Rat` skolems are oracles and the audit rejects
    /// them (and symmetrically an Int skolem is rejected under the Real
    /// carrier); a term naming `Real.le_trans` — a clean `Declaration::Axiom` —
    /// is rejected even in an environment that declares it.
    #[test]
    fn closure_audit_admits_rat_skolems_and_rejects_real_axioms() {
        let violation = and(vec![lt(rv("x"), rv("y")), lt(rv("y"), rv("x"))]);
        let (term, _, _) = certified(&violation, "audit");
        let term = deserialize_term(&term).expect("producer's own serialization");
        let vars = BTreeSet::from(["x".to_string(), "y".to_string()]);
        let env = build_env_real(&vars).expect("real env");
        assert!(
            proof_axiom_closure_is_clean_for(&env, &term, &vars, Carrier::Real),
            "the Real certificate must audit clean under its own carrier"
        );
        assert!(
            !proof_axiom_closure_is_clean_for(
                &env,
                &term,
                &BTreeSet::from(["x".to_string()]),
                Carrier::Real
            ),
            "a Rat skolem outside the exact obligation variable set is rejected"
        );
        assert!(
            !proof_axiom_closure_is_clean_for(&env, &term, &vars, Carrier::Int),
            "a Rat-typed skolem is an oracle to the INT-carrier audit"
        );
        assert!(
            !proof_axiom_closure_is_clean(&env, &term, &vars),
            "the Int-only entry point is exactly the Int-carrier audit"
        );
        // The mirror image: an Int-typed constant named like a variable is an
        // oracle to the Real-carrier audit.
        let mut int_env = env.clone();
        int_env
            .add_decl(Declaration::Axiom {
                name: Name::from_string(&encoded_var_name("z")),
                level_params: vec![],
                type_: super::super::int_ty(),
            })
            .expect("declare an Int-typed z");
        let z = Expr::const_(Name::from_string(&encoded_var_name("z")), vec![]);
        let zvars = BTreeSet::from(["z".to_string()]);
        assert!(proof_axiom_closure_is_clean_for(&int_env, &z, &zvars, Carrier::Int));
        assert!(!proof_axiom_closure_is_clean_for(&int_env, &z, &zvars, Carrier::Real));

        let mut hostile = env.clone();
        hostile.init_real_linear_order().expect("clean's Real order axioms register");
        let real_le_trans = Name::from_string("Real.le_trans");
        let info = hostile.get_const(&real_le_trans).expect("Real.le_trans is declared");
        assert_eq!(info.kind, ConstantKind::Axiom, "Real.le_trans is an axiom in clean");
        assert!(
            !proof_axiom_closure_is_clean_for(
                &hostile,
                &Expr::const_(real_le_trans, vec![]),
                &vars,
                Carrier::Real
            ),
            "a term resting on a Real.* axiom must be rejected"
        );
    }

    /// INERTNESS: a pool mixing `Int` and `Real` order atoms is not this lane's
    /// (`None`), and an Int-only obligation gets `None` from the lane while the
    /// Int pipeline still certifies it — so no Int certificate changes bytes.
    #[test]
    fn lane_is_inert_on_mixed_and_int_only_pools() {
        let mixed = and(vec![le(rv("x"), qi(1)), ge(rv("x"), qi(2)), le(iv("i"), Formula::Int(0))]);
        assert!(lane(&mixed).is_none(), "mixed Int/Real pool must be refused by the Real lane");
        let mixed_atom = and(vec![le(rv("x"), qi(1)), ge(rv("x"), qi(2)), le(iv("i"), qi(0))]);
        assert!(lane(&mixed_atom).is_none(), "an atom mixing Int and Real leaves refuses the lane");

        let int_only = and(vec![le(iv("x"), Formula::Int(1)), ge(iv("x"), Formula::Int(2))]);
        assert!(lane(&int_only).is_none(), "the Real lane must not touch an Int obligation");
        assert!(certify_violation(&int_only).is_some(), "the Int lane still certifies it");
    }

    /// Every constant the Real certificate names is a pre-existing kernel
    /// declaration from the lane's fixed vocabulary — a future edit that
    /// reaches for a new lemma has to say so here. The kernel term must
    /// actually contain the scaling, the Motzkin sum, the ring normalizer's
    /// closed folds and the closing Int lemmas.
    #[test]
    fn real_certificate_names_only_preexisting_kernel_lemmas() {
        let crown = and(vec![
            le(rv("y"), mul(qi(2), rv("x"))),
            le(rv("x"), q("1", "2")),
            gt(rv("y"), qi(1)),
        ]);
        let (term, _, _) = certified(&crown, "vocabulary");
        let term = deserialize_term(&term).expect("producer's own serialization");
        let mut names = Vec::new();
        assert!(collect_const_names(&term, &mut names), "every node must be auditable");
        let used: BTreeSet<String> = names.iter().map(|n| n.to_string()).collect();
        let expected: BTreeSet<String> = [
            // Carrier and literals.
            "Rat",
            "Rat.mk",
            "Rat.zero",
            "Rat.one",
            "Rat.add",
            "Rat.mul",
            "Rat.neg",
            "Rat.sub",
            "Rat.le",
            "Rat.lt",
            "Rat.Raw",
            "Rat.Raw.mk",
            "Rat.Raw.Equiv",
            "Int",
            "Int.ofNat",
            "Int.negSucc",
            "Int.NonNeg.mk",
            // Weighted Farkas rows and the Motzkin sum.
            "Rat.le_of_lt",
            "Rat.mul_le_mul_of_nonneg_left",
            "Rat.mul_lt_mul_of_pos_left",
            "Rat.add_le_add",
            "Rat.add_lt_add_of_lt_of_le",
            "Rat.sub_nonneg_of_le",
            "Rat.sub_pos_of_lt",
            // Ring normalizer.
            "Rat.left_distrib",
            "Rat.right_distrib",
            "Rat.mul_assoc",
            "Rat.mul_comm",
            "Rat.add_assoc",
            "Rat.add_comm",
            "Rat.one_mul",
            "Rat.add_zero",
            "Rat.zero_mul",
            "Rat.zero_add",
            "Rat.neg_neg",
            "Rat.neg_mul_neg",
            "Eq",
            "Eq.refl",
            "Eq.subst",
            "Eq.symm",
            "Quot.sound",
            // Closing the false residual.
            "Int.lt_of_lt_of_le",
            "Int.lt_irrefl",
            // The obligation's own free real variables.
            "x",
            "y",
        ]
        .into_iter()
        .map(str::to_string)
        .collect();
        assert!(
            used.is_subset(&expected),
            "certificate names constants outside the pre-existing inventory: {:?}",
            used.difference(&expected).collect::<Vec<_>>()
        );
        for required in [
            "Rat.mul_le_mul_of_nonneg_left",
            "Rat.add_lt_add_of_lt_of_le",
            "Rat.sub_pos_of_lt",
            "Rat.right_distrib",
            "Quot.sound",
            "Int.lt_irrefl",
        ] {
            assert!(used.contains(required), "certificate does not use {required}");
        }
    }
}

/// REFUTER 1 (soundness) — adopted as permanent regression tests. Every
/// system that is satisfiable BY CONSTRUCTION must fail closed, in every
/// spelling the fragment admits; the controls beside them keep the suite
/// non-vacuous.
#[cfg(test)]
mod refuter1_soundness {
    use trust_ir::ProofEvidence;
    use trust_types::{SourceSpan, VcKind, VerificationCondition};

    use super::super::{
        FOUNDATIONAL_AXIOMS, certify_vc, certify_violation, lineage_digest,
        proof_axiom_closure_is_clean_for, recheck_cleancic, recheck_vc_cleancic,
    };
    use super::*;

    fn qi(n: i64) -> Q {
        Q::from_integer(BigInt::from(n))
    }
    fn qr(n: i64, d: i64) -> Q {
        Q::new(BigInt::from(n), BigInt::from(d))
    }
    fn lit(q: &Q) -> Formula {
        Formula::rat(&q.numer().to_string(), &q.denom().to_string()).expect("canonical literal")
    }
    fn rv(n: &str) -> Formula {
        Formula::Var(n.to_string(), Sort::Real)
    }
    fn iv(n: &str) -> Formula {
        Formula::Var(n.to_string(), Sort::Int)
    }
    fn bx(f: Formula) -> Box<Formula> {
        Box::new(f)
    }
    fn le(a: Formula, b: Formula) -> Formula {
        Formula::Le(bx(a), bx(b))
    }
    fn lt(a: Formula, b: Formula) -> Formula {
        Formula::Lt(bx(a), bx(b))
    }
    fn ge(a: Formula, b: Formula) -> Formula {
        Formula::Ge(bx(a), bx(b))
    }
    fn gt(a: Formula, b: Formula) -> Formula {
        Formula::Gt(bx(a), bx(b))
    }
    fn eq(a: Formula, b: Formula) -> Formula {
        Formula::Eq(bx(a), bx(b))
    }
    fn add(a: Formula, b: Formula) -> Formula {
        Formula::Add(bx(a), bx(b))
    }
    fn sub(a: Formula, b: Formula) -> Formula {
        Formula::Sub(bx(a), bx(b))
    }
    fn mul(a: Formula, b: Formula) -> Formula {
        Formula::Mul(bx(a), bx(b))
    }
    fn neg(a: Formula) -> Formula {
        Formula::Neg(bx(a))
    }
    fn not(a: Formula) -> Formula {
        Formula::Not(bx(a))
    }
    fn and(v: Vec<Formula>) -> Formula {
        Formula::And(v)
    }

    fn cert(v: &Formula) -> Option<(Vec<u8>, Vec<u8>, trust_ir::ProofDigest)> {
        match certify_violation(v) {
            Some(ProofEvidence::CleanCic { term, context, lineage, .. }) => {
                assert!(recheck_cleancic(&term, &context, &lineage, v), "recheck pairs");
                Some((term, context, lineage))
            }
            Some(other) => panic!("non-CleanCic evidence: {other:?}"),
            None => None,
        }
    }
    fn certifies(v: &Formula) -> bool {
        cert(v).is_some()
    }

    // ── deterministic PRNG ────────────────────────────────────────────────
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
        fn range(&mut self, lo: i64, hi: i64) -> i64 {
            lo + (self.next() % ((hi - lo + 1) as u64)) as i64
        }
        fn coin(&mut self) -> bool {
            self.next() & 1 == 1
        }
    }

    /// Spell `c·x` in one of the fragment's shapes.
    fn spell_mono(rng: &mut Rng, x: &str, c: &Q) -> Formula {
        if *c == qi(1) && rng.coin() {
            return rv(x);
        }
        if *c == qi(-1) && rng.coin() {
            return neg(rv(x));
        }
        if rng.coin() { mul(lit(c), rv(x)) } else { mul(rv(x), lit(c)) }
    }

    /// Spell `Σ cᵢ·xᵢ + k` (k optional) with random Add/Sub/Neg nesting; returns
    /// the formula and its exact value at the point `p`.
    fn spell_side(
        rng: &mut Rng,
        vars: &[&str],
        p: &[Q],
        nterms: usize,
        with_k: bool,
    ) -> (Formula, Q) {
        let mut acc: Option<Formula> = None;
        let mut val = qi(0);
        for _ in 0..nterms {
            let vi = rng.range(0, vars.len() as i64 - 1) as usize;
            let c = qr(rng.range(-3, 3), rng.range(1, 3));
            if c == qi(0) && rng.coin() {
                continue;
            }
            val += &c * &p[vi];
            let (f, subtract) = if q_is_neg(&c) && rng.coin() {
                (spell_mono(rng, vars[vi], &(-c.clone())), true)
            } else {
                (spell_mono(rng, vars[vi], &c), false)
            };
            acc = Some(match acc {
                None => {
                    if subtract {
                        neg(f)
                    } else {
                        f
                    }
                }
                Some(a) => {
                    if subtract {
                        sub(a, f)
                    } else if rng.coin() {
                        add(a, f)
                    } else {
                        add(f, a)
                    }
                }
            });
        }
        if with_k || acc.is_none() {
            let k = qr(rng.range(-5, 5), rng.range(1, 4));
            val += &k;
            acc = Some(match acc {
                None => lit(&k),
                Some(a) => {
                    if rng.coin() {
                        add(a, lit(&k))
                    } else {
                        sub(a, lit(&(-k)))
                    }
                }
            });
        }
        (acc.unwrap(), val)
    }

    /// One atom TRUE at `p`, in a random relation/spelling.
    fn true_atom(rng: &mut Rng, vars: &[&str], p: &[Q]) -> Formula {
        let (nl, kl) = (rng.range(1, 3) as usize, rng.coin());
        let (l, vl) = spell_side(rng, vars, p, nl, kl);
        let nr = rng.range(0, 2) as usize;
        let (r, vr) = spell_side(rng, vars, p, nr, true);
        use std::cmp::Ordering::*;
        let choices: Vec<fn(Formula, Formula) -> Formula> = match vl.cmp(&vr) {
            Less => {
                vec![le, lt, |a, b| not(ge(a, b)), |a, b| not(le(b, a)), |a, b| gt(b, a), |a, b| {
                    ge(b, a)
                }]
            }
            Equal => vec![le, ge, eq, |a, b| eq(b, a), |a, b| not(lt(a, b)), |a, b| not(gt(a, b))],
            Greater => {
                vec![ge, gt, |a, b| not(le(a, b)), |a, b| not(ge(b, a)), |a, b| lt(b, a), |a, b| {
                    le(b, a)
                }]
            }
        };
        let pick = rng.range(0, choices.len() as i64 - 1) as usize;
        choices[pick](l, r)
    }

    /// (SOUNDNESS, RANDOMIZED) Every system here is SATISFIABLE BY
    /// CONSTRUCTION (each atom is generated true at a fixed rational point), in
    /// every spelling the fragment admits (Mul on either side, Sub/Neg, Eq rows,
    /// literal on either side, negated atoms, duplicate atoms, dropped junk
    /// conjuncts, zero coefficients). Not one may certify.
    #[test]
    fn r1_random_satisfiable_real_systems_never_certify() {
        let vars = ["x", "y", "z", "w"];
        let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
        let mut minted = Vec::new();
        for case in 0..400 {
            let nv = rng.range(1, 4) as usize;
            let p: Vec<Q> = (0..nv).map(|_| qr(rng.range(-6, 6), rng.range(1, 4))).collect();
            let vs = &vars[..nv];
            let natoms = rng.range(1, 6) as usize;
            let mut conj: Vec<Formula> = (0..natoms).map(|_| true_atom(&mut rng, vs, &p)).collect();
            if rng.coin() {
                let d = conj[rng.range(0, natoms as i64 - 1) as usize].clone();
                conj.push(d);
            }
            match rng.range(0, 3) {
                0 => conj.push(not(eq(rv("x"), rv("y")))),
                1 => {
                    conj.push(Formula::Or(vec![lt(rv("x"), lit(&qi(0))), ge(rv("x"), lit(&qi(0)))]))
                }
                2 => conj.push(Formula::Bool(true)),
                _ => {}
            }
            let violation = and(conj);
            if certifies(&violation) {
                minted.push((case, violation));
            }
        }
        assert!(minted.is_empty(), "FALSE CERTIFICATES on satisfiable systems: {minted:#?}");
    }

    /// Controls: the SAME spelling machinery does produce live certificates on
    /// genuinely infeasible systems (so the randomized test is not vacuous).
    #[test]
    fn r1_spelling_controls_certify() {
        let h = qr(1, 2);
        assert!(certifies(&and(vec![
            le(mul(rv("x"), lit(&h)), lit(&qi(1))),
            ge(rv("x"), lit(&qi(3)))
        ])));
        assert!(certifies(&and(vec![
            not(ge(rv("x"), lit(&qi(1)))),
            not(lt(rv("x"), lit(&qi(1))))
        ])));
        assert!(certifies(&and(vec![
            eq(sub(rv("x"), rv("y")), lit(&qi(1))),
            eq(rv("y"), rv("x"))
        ])));
        assert!(certifies(&and(vec![lt(neg(rv("x")), lit(&qi(0))), le(rv("x"), lit(&qi(0)))])));
        assert!(certifies(&and(vec![
            lt(add(lit(&qr(1, 3)), rv("x")), add(rv("y"), lit(&qr(1, 3)))),
            lt(rv("y"), rv("x")),
        ])));
    }

    /// Systems whose ONLY contradiction is integrality — real-feasible.
    #[test]
    fn r1_integrality_only_contradictions_never_certify() {
        let big = (BigInt::from(1) << 200u32) + BigInt::from(1);
        let bigq = Q::new(big, BigInt::from(1));
        let cases = vec![
            ("3x = 1", and(vec![eq(mul(lit(&qi(3)), rv("x")), lit(&qi(1)))])),
            (
                "3x ≥ 1 ∧ 3x ≤ 1",
                and(vec![
                    ge(mul(lit(&qi(3)), rv("x")), lit(&qi(1))),
                    le(mul(lit(&qi(3)), rv("x")), lit(&qi(1))),
                ]),
            ),
            (
                "x + y = 1 ∧ x = y",
                and(vec![eq(add(rv("x"), rv("y")), lit(&qi(1))), eq(rv("x"), rv("y"))]),
            ),
            (
                "0 < x ∧ x < 1/1000000",
                and(vec![lt(lit(&qi(0)), rv("x")), lt(rv("x"), lit(&qr(1, 1_000_000)))]),
            ),
            (
                "x < y ∧ y < x + 1/(2^200+1)",
                and(vec![lt(rv("x"), rv("y")), lt(rv("y"), add(rv("x"), lit(&(qi(1) / &bigq))))]),
            ),
            (
                "2x - 2y = 1",
                and(vec![eq(
                    sub(mul(lit(&qi(2)), rv("x")), mul(lit(&qi(2)), rv("y"))),
                    lit(&qi(1)),
                )]),
            ),
            (
                "x ≥ 1/2 ∧ x ≤ 1/2 ∧ 2x ≥ 1 ∧ 2x ≤ 1",
                and(vec![
                    ge(rv("x"), lit(&qr(1, 2))),
                    le(rv("x"), lit(&qr(1, 2))),
                    ge(mul(lit(&qi(2)), rv("x")), lit(&qi(1))),
                    le(mul(lit(&qi(2)), rv("x")), lit(&qi(1))),
                ]),
            ),
            (
                "x > 0 ∧ x < 1 ∧ y > 0 ∧ y < 1 ∧ x + y = 1",
                and(vec![
                    gt(rv("x"), lit(&qi(0))),
                    lt(rv("x"), lit(&qi(1))),
                    gt(rv("y"), lit(&qi(0))),
                    lt(rv("y"), lit(&qi(1))),
                    eq(add(rv("x"), rv("y")), lit(&qi(1))),
                ]),
            ),
        ];
        for (name, v) in cases {
            assert!(!certifies(&v), "FALSE CERTIFICATE: {name}");
        }
    }

    /// Farkas combinations that sum to `0 ≤ 0` / a satisfied strict residual,
    /// with mixed strict/non-strict rows: none may certify. Controls: the
    /// genuinely infeasible neighbours do — including the cancelled-variable
    /// rows that used to decline (`x − x < 0` alone: the variable is declared
    /// from the term structure now).
    #[test]
    fn r1_zero_sum_and_strictness_bookkeeping() {
        let z = lit(&qi(0));
        let sat = vec![
            ("x ≤ y ∧ y ≤ x", and(vec![le(rv("x"), rv("y")), le(rv("y"), rv("x"))])),
            (
                "x ≤ y ∧ y ≤ z ∧ z ≤ x",
                and(vec![le(rv("x"), rv("y")), le(rv("y"), rv("z")), le(rv("z"), rv("x"))]),
            ),
            (
                "x ≤ y ∧ y ≤ x ∧ x - y < 1",
                and(vec![
                    le(rv("x"), rv("y")),
                    le(rv("y"), rv("x")),
                    lt(sub(rv("x"), rv("y")), lit(&qi(1))),
                ]),
            ),
            (
                "x ≤ y ∧ y ≤ x ∧ x < y + 1/2",
                and(vec![
                    le(rv("x"), rv("y")),
                    le(rv("y"), rv("x")),
                    lt(rv("x"), add(rv("y"), lit(&qr(1, 2)))),
                ]),
            ),
            ("x - x ≤ 0", and(vec![le(sub(rv("x"), rv("x")), z.clone())])),
            ("x - x < 1", and(vec![lt(sub(rv("x"), rv("x")), lit(&qi(1)))])),
            (
                "(1/3)x + (2/3)x - x < 1",
                and(vec![lt(
                    sub(add(mul(lit(&qr(1, 3)), rv("x")), mul(lit(&qr(2, 3)), rv("x"))), rv("x")),
                    lit(&qi(1)),
                )]),
            ),
            (
                "(1/2)x + (1/2)x ≤ 1 ∧ x ≥ 1",
                and(vec![
                    le(
                        add(mul(lit(&qr(1, 2)), rv("x")), mul(lit(&qr(1, 2)), rv("x"))),
                        lit(&qi(1)),
                    ),
                    ge(rv("x"), lit(&qi(1))),
                ]),
            ),
            (
                "x ≤ 1 ∧ x ≤ 1 ∧ x ≥ 1 (duplicate)",
                and(vec![
                    le(rv("x"), lit(&qi(1))),
                    le(rv("x"), lit(&qi(1))),
                    ge(rv("x"), lit(&qi(1))),
                ]),
            ),
            (
                "x < 1 ∧ x ≤ 1 ∧ x ≥ 1/2",
                and(vec![
                    lt(rv("x"), lit(&qi(1))),
                    le(rv("x"), lit(&qi(1))),
                    ge(rv("x"), lit(&qr(1, 2))),
                ]),
            ),
            (
                "0·x ≤ -0 ∧ 0·y ≥ 0",
                and(vec![
                    le(mul(z.clone(), rv("x")), z.clone()),
                    ge(mul(z.clone(), rv("y")), z.clone()),
                ]),
            ),
            (
                "0·x < 1 ∧ x ≥ 5",
                and(vec![lt(mul(z.clone(), rv("x")), lit(&qi(1))), ge(rv("x"), lit(&qi(5)))]),
            ),
            (
                "2x - 2y ≤ 0 ∧ y - x ≤ 0 ∧ x < y + 1",
                and(vec![
                    le(sub(mul(lit(&qi(2)), rv("x")), mul(lit(&qi(2)), rv("y"))), z.clone()),
                    le(sub(rv("y"), rv("x")), z.clone()),
                    lt(rv("x"), add(rv("y"), lit(&qi(1)))),
                ]),
            ),
            (
                "-x ≤ 0 ∧ x ≤ 0 ∧ -x < 1",
                and(vec![
                    le(neg(rv("x")), z.clone()),
                    le(rv("x"), z.clone()),
                    lt(neg(rv("x")), lit(&qi(1))),
                ]),
            ),
            (
                "2x < 1 ∧ x ≥ 1/4",
                and(vec![lt(mul(lit(&qi(2)), rv("x")), lit(&qi(1))), ge(rv("x"), lit(&qr(1, 4)))]),
            ),
            (
                "x < y ∧ y < z ∧ z < x + 1",
                and(vec![
                    lt(rv("x"), rv("y")),
                    lt(rv("y"), rv("z")),
                    lt(rv("z"), add(rv("x"), lit(&qi(1)))),
                ]),
            ),
            (
                "SymVar x ≤ 2 ∧ Var x ≥ 1",
                and(vec![
                    le(Formula::var_sym(trust_types::Symbol::intern("x"), Sort::Real), lit(&qi(2))),
                    ge(rv("x"), lit(&qi(1))),
                ]),
            ),
        ];
        for (name, v) in sat {
            assert!(!certifies(&v), "FALSE CERTIFICATE: {name}");
        }
        let unsat = vec![
            ("x < y ∧ y ≤ x", and(vec![lt(rv("x"), rv("y")), le(rv("y"), rv("x"))])),
            (
                "x ≤ y ∧ y < z ∧ z ≤ x",
                and(vec![le(rv("x"), rv("y")), lt(rv("y"), rv("z")), le(rv("z"), rv("x"))]),
            ),
            ("x - x < 0 (alone)", and(vec![lt(sub(rv("x"), rv("x")), z.clone())])),
            (
                "x - x < 0 ∧ x ≤ 5",
                and(vec![lt(sub(rv("x"), rv("x")), z.clone()), le(rv("x"), lit(&qi(5)))]),
            ),
            (
                "(1/3)x + (2/3)x - x < 0 ∧ x ≤ 5",
                and(vec![
                    lt(
                        sub(
                            add(mul(lit(&qr(1, 3)), rv("x")), mul(lit(&qr(2, 3)), rv("x"))),
                            rv("x"),
                        ),
                        z.clone(),
                    ),
                    le(rv("x"), lit(&qi(5))),
                ]),
            ),
            (
                "(1/2)x + (1/2)x ≤ 0 ∧ x ≥ 1",
                and(vec![
                    le(add(mul(lit(&qr(1, 2)), rv("x")), mul(lit(&qr(1, 2)), rv("x"))), z.clone()),
                    ge(rv("x"), lit(&qi(1))),
                ]),
            ),
            (
                "x < 1 ∧ x < 1 ∧ x ≥ 1 (duplicate strict)",
                and(vec![
                    lt(rv("x"), lit(&qi(1))),
                    lt(rv("x"), lit(&qi(1))),
                    ge(rv("x"), lit(&qi(1))),
                ]),
            ),
            ("0·x < 0 (alone)", and(vec![lt(mul(z.clone(), rv("x")), z.clone())])),
            (
                "0·x < 0 ∧ x ≤ 5",
                and(vec![lt(mul(z.clone(), rv("x")), z.clone()), le(rv("x"), lit(&qi(5)))]),
            ),
            (
                "-x ≤ 0 ∧ x ≤ 0 ∧ -x < 0",
                and(vec![
                    le(neg(rv("x")), z.clone()),
                    le(rv("x"), z.clone()),
                    lt(neg(rv("x")), z.clone()),
                ]),
            ),
            (
                "2x < 1 ∧ x ≥ 1/2 (strict row, λ = 1/2)",
                and(vec![lt(mul(lit(&qi(2)), rv("x")), lit(&qi(1))), ge(rv("x"), lit(&qr(1, 2)))]),
            ),
            (
                "x < y ∧ y < z ∧ z < x",
                and(vec![lt(rv("x"), rv("y")), lt(rv("y"), rv("z")), lt(rv("z"), rv("x"))]),
            ),
            (
                "SymVar x ≤ 1 ∧ Var x ≥ 2 (one variable)",
                and(vec![
                    le(Formula::var_sym(trust_types::Symbol::intern("x"), Sort::Real), lit(&qi(1))),
                    ge(rv("x"), lit(&qi(2))),
                ]),
            ),
        ];
        for (name, v) in unsat {
            assert!(certifies(&v), "control should certify: {name}");
        }
        // A variable whose encoded name collides with a kernel constant fails
        // closed (the skolem cannot be declared), never mints a wrong term.
        let shadow = and(vec![le(rv("Rat.zero"), lit(&qi(1))), ge(rv("Rat.zero"), lit(&qi(2)))]);
        assert!(!certifies(&shadow), "a variable named after a kernel constant declines");
    }

    /// Huge and tiny literals, including one above the kernel's ~16384-bit
    /// BigNat multiplication ceiling: never a false certificate.
    #[test]
    fn r1_extreme_literals() {
        let two = BigInt::from(2);
        let p300 = Q::new(two.pow(300), BigInt::from(1));
        let p20000 = Q::new(two.pow(20000), BigInt::from(1));
        let tiny = qi(1) / &p300;
        let sat = vec![
            (
                "x ≥ 2^-300 ∧ x ≤ 2·2^-300",
                and(vec![ge(rv("x"), lit(&tiny)), le(rv("x"), lit(&(&tiny * qi(2))))]),
            ),
            ("x ≤ 2^300 ∧ x ≥ 2", and(vec![le(rv("x"), lit(&p300)), ge(rv("x"), lit(&qi(2)))])),
            ("x ≤ 2^20000 ∧ x ≥ 2", and(vec![le(rv("x"), lit(&p20000)), ge(rv("x"), lit(&qi(2)))])),
            (
                "2^20000·x ≤ 2^20000 ∧ x ≥ 1",
                and(vec![le(mul(lit(&p20000), rv("x")), lit(&p20000)), ge(rv("x"), lit(&qi(1)))]),
            ),
            (
                "x ≥ 2^300 ∧ x ≤ 2^300 + 2^-300",
                and(vec![ge(rv("x"), lit(&p300)), le(rv("x"), lit(&(&p300 + &tiny)))]),
            ),
        ];
        for (name, v) in sat {
            assert!(!certifies(&v), "FALSE CERTIFICATE: {name}");
        }
        assert!(
            certifies(&and(vec![ge(rv("x"), lit(&p300)), le(rv("x"), lit(&(&p300 - &tiny)))])),
            "2^300 gap control"
        );
        // Above the kernel's BigNat multiplication ceiling the lane may decline;
        // it must never crash and never mint a wrong term.
        let over_cap = and(vec![ge(rv("x"), lit(&p20000)), le(rv("x"), lit(&qi(1)))]);
        let _ = certifies(&over_cap);
    }

    /// Non-canonical / hostile `Rat` spellings: the contract's `RatLit` refuses
    /// every one at construction (and at deserialization), so the lane can
    /// never see `+1`, `1/-2`, `1/0`, whitespace, hex, exponents or `-0`. An
    /// UNREDUCED but canonical-syntax literal (`2/4`) is a distinct literal
    /// denoting `1/2`, which the lane reduces on parse.
    #[test]
    fn r1_hostile_rat_literals() {
        for (n, d) in [
            ("1", "-2"),
            ("-1", "-2"),
            ("1", "0"),
            ("+1", "2"),
            (" 1", "2"),
            ("0x10", "1"),
            ("1e3", "1"),
            ("1_000", "1"),
            ("１", "1"),
            ("--1", "2"),
            ("-0", "1"),
            ("01", "1"),
            ("1", "01"),
            ("", "1"),
            ("1", ""),
        ] {
            assert!(Formula::rat(n, d).is_none(), "{n:?}/{d:?} must be refused by the contract");
        }
        let two_fourths = Formula::rat("2", "4").expect("canonical syntax, unreduced");
        assert!(
            !certifies(&and(vec![le(rv("x"), two_fourths.clone()), ge(rv("x"), lit(&qr(1, 2)))])),
            "x ≤ 2/4 ∧ x ≥ 1/2 is SAT"
        );
        assert!(
            certifies(&and(vec![lt(rv("x"), two_fourths), ge(rv("x"), lit(&qr(1, 2)))])),
            "x < 2/4 ∧ x ≥ 1/2 control"
        );
    }

    /// Variable-name encoding: two DISTINCT names that encode to the same kernel
    /// / SMT symbol would let a satisfiable two-variable system be certified as
    /// a one-variable contradiction. `encoded_var_name` returns a "simple" name
    /// verbatim and hex-encodes any other name under the prefix `trust_var_`,
    /// so the simple name `trust_var_3178` and the non-simple name `1x`
    /// (hex 31 78) collide — and the lane must fail closed on the collision.
    #[test]
    fn r1_var_name_encoding_collision_real_lane() {
        assert_eq!(
            encoded_var_name("1x"),
            encoded_var_name("trust_var_3178"),
            "the encoding is not injective"
        );
        let v = and(vec![le(rv("1x"), lit(&qi(1))), ge(rv("trust_var_3178"), lit(&qi(2)))]);
        assert!(
            !certifies(&v),
            "FALSE CERTIFICATE: distinct Real variables aliased by encoded_var_name"
        );
    }

    #[test]
    fn r1_var_name_encoding_collision_int_lane() {
        let v = and(vec![le(iv("1x"), Formula::Int(1)), ge(iv("trust_var_3178"), Formula::Int(2))]);
        assert!(
            !certifies(&v),
            "FALSE CERTIFICATE: distinct Int variables aliased by encoded_var_name"
        );
    }

    /// The rechecker cannot be fooled: tampered context/lineage/term, and a
    /// certificate presented against any other obligation (another Real one,
    /// the Int spelling, a superset formula, a different VC identity).
    #[test]
    fn r1_recheck_cannot_be_fooled() {
        let a = and(vec![
            le(mul(lit(&qr(1, 2)), rv("x")), lit(&qi(1))),
            ge(mul(lit(&qr(1, 3)), rv("x")), lit(&qr(7, 6))),
        ]);
        let (term, context, lineage) = cert(&a).expect("A certifies");
        // Tampered context (flip a byte in the middle), tampered lineage.
        let mut ctx2 = context.clone();
        let mid = ctx2.len() / 2;
        ctx2[mid] ^= 0x5a;
        assert!(!recheck_cleancic(&term, &ctx2, &lineage, &a), "tampered context accepted");
        let mut ctx3 = context.clone();
        ctx3.push(0);
        assert!(!recheck_cleancic(&term, &ctx3, &lineage, &a), "extended context accepted");
        let mut term2 = term.clone();
        let m = term2.len() / 3;
        term2[m] ^= 0x01;
        assert!(!recheck_cleancic(&term2, &context, &lineage, &a), "tampered term accepted");
        let other = and(vec![le(rv("x"), lit(&qi(1))), ge(rv("x"), lit(&qi(2)))]);
        let forged_lineage =
            lineage_digest(&term, &context, &ObligationIdentity::from_violation(&other).unwrap());
        assert!(!recheck_cleancic(&term, &context, &forged_lineage, &a), "forged lineage accepted");
        assert!(
            !recheck_cleancic(&term, &context, &lineage, &other),
            "certificate re-used for another Real obligation"
        );
        assert!(
            !recheck_cleancic(&term, &context, &forged_lineage, &other),
            "certificate re-used with re-stamped lineage"
        );
        // Superset formula (still UNSAT, same kept atoms): the lineage must differ.
        let superset = and(vec![a.clone(), le(rv("y"), lit(&qi(0)))]);
        assert!(
            !recheck_cleancic(&term, &context, &lineage, &superset),
            "certificate re-used for a superset obligation"
        );
        // Int spelling of the interval with the Real certificate bytes.
        let int_spelling = and(vec![le(iv("x"), Formula::Int(2)), ge(iv("x"), Formula::Int(4))]);
        assert!(!recheck_cleancic(&term, &context, &lineage, &int_spelling));
        // The SAT relaxation must not accept anyone's bytes.
        let sat =
            and(vec![le(mul(lit(&qr(1, 2)), rv("x")), lit(&qi(1))), ge(rv("x"), lit(&qi(2)))]);
        assert!(!recheck_cleancic(&term, &context, &lineage, &sat));

        // VC identity: same formula, different function → refused.
        let vc = |f: &str| VerificationCondition {
            kind: VcKind::Assertion { message: "r1".to_string() },
            function: f.into(),
            location: SourceSpan::default(),
            formula: a.clone(),
            contract_metadata: None,
            obligation: None,
        };
        let v1 = vc("f1");
        let Some(ProofEvidence::CleanCic { term: t, context: c, lineage: l, .. }) = certify_vc(&v1)
        else {
            panic!("certify_vc on the Real system");
        };
        assert!(recheck_vc_cleancic(&t, &c, &l, &v1), "control");
        assert!(
            !recheck_vc_cleancic(&t, &c, &l, &vc("f2")),
            "certificate re-used across VC identities"
        );
        assert!(
            !recheck_cleancic(&t, &c, &l, &a),
            "VC-minted lineage accepted on the formula-only path"
        );
        assert_eq!(t, term, "the payload is identity-independent");
    }

    /// Every lemma the lane may name has a clean transitive closure in the Real
    /// environment, and none of them is an axiom.
    #[test]
    fn r1_real_env_vocabulary_closure_is_clean() {
        use clean_kernel::env::ConstantKind;
        let vars: BTreeSet<String> = ["x", "y"].into_iter().map(str::to_string).collect();
        let env = build_env_real(&vars).expect("real env");
        let vocab = [
            "Rat",
            "Rat.mk",
            "Rat.zero",
            "Rat.one",
            "Rat.add",
            "Rat.mul",
            "Rat.neg",
            "Rat.sub",
            "Rat.le",
            "Rat.lt",
            "Rat.Raw",
            "Rat.Raw.mk",
            "Rat.Raw.Equiv",
            "Int",
            "Int.ofNat",
            "Int.negSucc",
            "Int.NonNeg.mk",
            "Rat.le_of_lt",
            "Rat.mul_le_mul_of_nonneg_left",
            "Rat.mul_lt_mul_of_pos_left",
            "Rat.add_le_add",
            "Rat.add_lt_add_of_lt_of_le",
            "Rat.sub_nonneg_of_le",
            "Rat.sub_pos_of_lt",
            "Rat.left_distrib",
            "Rat.right_distrib",
            "Rat.mul_assoc",
            "Rat.mul_comm",
            "Rat.add_assoc",
            "Rat.add_comm",
            "Rat.one_mul",
            "Rat.add_zero",
            "Rat.zero_mul",
            "Rat.zero_add",
            "Rat.neg_neg",
            "Rat.neg_mul_neg",
            "Eq",
            "Eq.refl",
            "Eq.subst",
            "Eq.symm",
            "Quot.sound",
            "Int.lt_of_lt_of_le",
            "Int.lt_irrefl",
        ];
        let mut bad = Vec::new();
        for name in vocab {
            let n = Name::from_string(name);
            let Some(info) = env.get_const(&n) else {
                bad.push(format!("{name}: NOT DECLARED"));
                continue;
            };
            if info.kind == ConstantKind::Axiom && !FOUNDATIONAL_AXIOMS.contains(&name) {
                bad.push(format!("{name}: is an AXIOM"));
            }
            if !proof_axiom_closure_is_clean_for(
                &env,
                &Expr::const_(n, vec![]),
                &vars,
                Carrier::Real,
            ) {
                bad.push(format!("{name}: closure not clean"));
            }
        }
        assert!(bad.is_empty(), "{bad:#?}");
    }

    /// Real-sorted systems must not leak into the Int lanes that run BEFORE the
    /// Real lane (closed-constant, disjunctive, split-disequality, ...).
    #[test]
    fn r1_int_lanes_are_inert_on_real_inputs() {
        let sat = vec![
            (
                "x ≤ 1 ∧ Or([x ≥ 1/2, x ≥ 3])",
                and(vec![
                    le(rv("x"), lit(&qi(1))),
                    Formula::Or(vec![ge(rv("x"), lit(&qr(1, 2))), ge(rv("x"), lit(&qi(3)))]),
                ]),
            ),
            (
                "x > 0 ∧ Or([x - 1/2 < 0, x > 5])",
                and(vec![
                    gt(rv("x"), lit(&qi(0))),
                    Formula::Or(vec![
                        lt(sub(rv("x"), lit(&qr(1, 2))), lit(&qi(0))),
                        gt(rv("x"), lit(&qi(5))),
                    ]),
                ]),
            ),
            (
                "closed Or over Rat literals (true)",
                and(vec![Formula::Or(vec![
                    lt(lit(&qr(1, 2)), lit(&qi(1))),
                    gt(lit(&qr(1, 2)), lit(&qi(1))),
                ])]),
            ),
            (
                "x ≤ y ∧ y ≤ x ∧ x ≠ y over Real",
                and(vec![le(rv("x"), rv("y")), le(rv("y"), rv("x")), not(eq(rv("x"), rv("y")))]),
            ),
            (
                "x = 1/2 ∧ x ≠ 0",
                and(vec![eq(rv("x"), lit(&qr(1, 2))), not(eq(rv("x"), lit(&qi(0))))]),
            ),
            (
                "Not(Not(0 < x)) ∧ x < 1",
                and(vec![not(not(lt(lit(&qi(0)), rv("x")))), lt(rv("x"), lit(&qi(1)))]),
            ),
            (
                "b ⟺ (0 < x) ∧ b ∧ x < 1",
                and(vec![
                    eq(Formula::Var("b".into(), Sort::Bool), lt(lit(&qi(0)), rv("x"))),
                    Formula::Var("b".into(), Sort::Bool),
                    lt(rv("x"), lit(&qi(1))),
                ]),
            ),
            (
                "Implies(x ≥ 0, x ≥ 1) ∧ x ≥ 1/2 ∧ x < 1",
                and(vec![
                    Formula::Implies(bx(ge(rv("x"), lit(&qi(0)))), bx(ge(rv("x"), lit(&qi(1))))),
                    ge(rv("x"), lit(&qr(1, 2))),
                    lt(rv("x"), lit(&qi(1))),
                ]),
            ),
        ];
        for (name, v) in sat {
            assert!(!certifies(&v), "FALSE CERTIFICATE: {name}");
        }
        // Mixed atom through the public entry (gate) — must be None.
        assert!(
            !certifies(&and(vec![le(iv("i"), lit(&qi(0))), ge(iv("i"), lit(&qi(1)))])),
            "ill-sorted mixed atoms"
        );
        assert!(
            !certifies(&and(vec![le(rv("x"), Formula::Int(0)), ge(rv("x"), Formula::Int(1))])),
            "Real var vs Int literal"
        );
        // Same name, two sorts: the Real half alone is SAT, the Int half alone is SAT.
        assert!(
            !certifies(&and(vec![le(rv("x"), lit(&qi(1))), ge(iv("x"), Formula::Int(2))])),
            "x:Real ≤ 1 ∧ x:Int ≥ 2"
        );
    }
}

/// REFUTER 2 (completeness) — the two gaps it measured, now pinned as the
/// behaviour the lane's contract promises.
#[cfg(test)]
mod refuter2_real_lane_gaps {
    use super::super::certify_violation;
    use super::*;

    fn rv(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Real)
    }
    fn qi(n: i128) -> Formula {
        Formula::rat_from_int(n)
    }
    fn b(f: Formula) -> Box<Formula> {
        Box::new(f)
    }

    /// GAP 1 (fixed): a kept atom whose linear form has a ZERO coefficient on
    /// some variable (`x − x`, `0·x`, `(x + y) − x`) still spells that variable
    /// in its SMT and kernel hypotheses; the variable set is collected from the
    /// TERM STRUCTURE, so it is declared and the system certifies.
    #[test]
    fn cancelled_variable_rows_certify() {
        let alone =
            Formula::And(vec![Formula::Le(b(Formula::Sub(b(rv("x")), b(rv("x")))), b(qi(-1)))]);
        assert!(certify_violation(&alone).is_some(), "x − x ≤ −1 is infeasible over the reals");
        let zero_coeff =
            Formula::And(vec![Formula::Ge(b(Formula::Mul(b(qi(0)), b(rv("x")))), b(qi(1)))]);
        assert!(certify_violation(&zero_coeff).is_some(), "0·x ≥ 1 is infeasible");
        let in_sum = Formula::And(vec![
            Formula::Le(
                b(Formula::Sub(b(Formula::Add(b(rv("x")), b(rv("y")))), b(rv("x")))),
                b(qi(0)),
            ),
            Formula::Ge(b(rv("y")), b(qi(1))),
        ]);
        assert!(certify_violation(&in_sum).is_some(), "(x + y) − x ≤ 0 ∧ y ≥ 1 is infeasible");
    }

    /// GAP 2 (fixed): a 51-row, 25-variable system (`0 ≤ vᵢ ≤ 1` for 25
    /// variables plus `Σ vᵢ ≥ 26`) is under the 64-atom cap and has a one-step
    /// Farkas witness. It used to overflow a default thread stack (process
    /// ABORT) and then exceed the proof codec's 2,000,000-node limit; it now
    /// certifies from a DEFAULT 2 MiB test thread (the lane owns its own
    /// stack) with a certificate inside the codec limit.
    #[test]
    fn fifty_one_row_box_system_certifies_under_the_atom_cap() {
        let n = 25usize;
        let names: Vec<String> = (0..n).map(|i| format!("v{i:03}")).collect();
        let mut rows = Vec::new();
        for nm in &names {
            rows.push(Formula::Ge(b(rv(nm)), b(qi(0))));
            rows.push(Formula::Le(b(rv(nm)), b(qi(1))));
        }
        let sum = names[1..].iter().fold(rv(&names[0]), |acc, nm| Formula::Add(b(acc), b(rv(nm))));
        rows.push(Formula::Ge(b(sum), b(qi(n as i128 + 1))));
        let violation = Formula::And(rows);
        assert!(
            certify_violation(&violation).is_some(),
            "51 rows / 25 variables is inside the documented fragment"
        );
    }
}

/// Resource discipline and certificate scale: the lane declines CLEANLY on
/// inputs past its caps (from a default-stack thread — no abort, no panic),
/// certifies the box systems inside the proof codec's limits, and finds the
/// witnesses dense noise rows used to hide from Fourier–Motzkin.
#[cfg(test)]
mod resource_and_scale_regressions {
    use trust_ir::ProofEvidence;

    use super::super::{certify_violation, deserialize_term, recheck_cleancic};
    use super::*;

    fn rv(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Real)
    }
    fn qi(n: i128) -> Formula {
        Formula::rat_from_int(n)
    }
    fn b(f: Formula) -> Box<Formula> {
        Box::new(f)
    }
    fn add(a: Formula, c: Formula) -> Formula {
        Formula::Add(b(a), b(c))
    }
    fn mul(a: Formula, c: Formula) -> Formula {
        Formula::Mul(b(a), b(c))
    }
    fn le(a: Formula, c: Formula) -> Formula {
        Formula::Le(b(a), b(c))
    }
    fn lt(a: Formula, c: Formula) -> Formula {
        Formula::Lt(b(a), b(c))
    }
    fn ge(a: Formula, c: Formula) -> Formula {
        Formula::Ge(b(a), b(c))
    }
    fn gt(a: Formula, c: Formula) -> Formula {
        Formula::Gt(b(a), b(c))
    }
    fn and(v: Vec<Formula>) -> Formula {
        Formula::And(v)
    }
    fn sum_of(names: &[String]) -> Formula {
        names[1..].iter().fold(rv(&names[0]), |acc, nm| add(acc, rv(nm)))
    }

    /// `0 ≤ vᵢ ≤ 1` for `n` variables plus `Σ vᵢ ≥ n + 1`: 2n+1 rows.
    fn box_system(n: usize) -> Formula {
        let names: Vec<String> = (0..n).map(|i| format!("v{i:03}")).collect();
        let mut rows = Vec::new();
        for nm in &names {
            rows.push(ge(rv(nm), qi(0)));
            rows.push(le(rv(nm), qi(1)));
        }
        rows.push(ge(sum_of(&names), qi(n as i128 + 1)));
        and(rows)
    }

    fn cleancic(violation: &Formula, what: &str) -> (Vec<u8>, Expr) {
        match certify_violation(violation) {
            Some(ProofEvidence::CleanCic { term, context, lineage, .. }) => {
                assert!(recheck_cleancic(&term, &context, &lineage, violation), "{what}: recheck");
                let expr = deserialize_term(&term).expect("producer's own serialization");
                (term, expr)
            }
            other => panic!("{what}: expected Some(CleanCic), got {other:?}"),
        }
    }

    /// SCALE: the box systems with n = 10, 15, 20, 25 variables all certify
    /// (from a default test thread) with certificates inside the proof codec's
    /// 2,000,000-node limit, and their size is reported so a regression in the
    /// normalizer's motive discipline is visible. Before the restructure: n=10
    /// was 1,375,783 bytes, n=15 3,314,249 bytes, and n=20 / n=25 declined
    /// (codec limit); after: 215,039 / 389,804 / 611,719 / 880,784 bytes —
    /// measured on this machine.
    #[test]
    fn box_systems_certify_within_the_codec_limit() {
        for n in [10usize, 15, 20, 25] {
            let violation = box_system(n);
            let t0 = std::time::Instant::now();
            let (bytes, expr) = cleancic(&violation, &format!("box system n={n}"));
            let elapsed = t0.elapsed();
            let nodes = expr_nodes(&expr);
            eprintln!(
                "[real-lane scale] box n={n} rows={} bytes={} codec_nodes={} certify+recheck={elapsed:?}",
                2 * n + 1,
                bytes.len(),
                nodes
            );
            assert!(nodes <= 2_000_000, "n={n}: {nodes} nodes exceeds the codec limit");
            // Measured: 89K / 161K / 253K / 364K codec nodes. A regression in the
            // motive discipline is a multiple of that, not a rounding error.
            assert!(nodes <= 600_000, "n={n}: {nodes} nodes — the motive discipline regressed");
        }
    }

    /// CRASH (fixed): a 75-deep `Add` chain is past [`MAX_TERM_DEPTH`]; the atom
    /// is outside the fragment, the lane declines from a DEFAULT 2 MiB test
    /// thread, and the process neither aborts nor panics. The same shape at
    /// depth 40 (inside the cap) certifies.
    #[test]
    fn seventy_five_deep_add_chain_declines_cleanly_on_the_default_stack() {
        let chain = |depth: usize| (0..depth).fold(rv("x"), |acc, _| add(acc, rv("x")));
        let deep = and(vec![le(chain(75), qi(-1)), ge(rv("x"), qi(0))]);
        assert!(certify_violation(&deep).is_none(), "past MAX_TERM_DEPTH the lane declines");
        let inside = and(vec![le(chain(40), qi(-1)), ge(rv("x"), qi(0))]);
        let _ = cleancic(&inside, "41 x's ≤ −1 ∧ x ≥ 0");
    }

    /// CRASH (fixed): a single row over 63 variables is past [`MAX_ROW_VARS`];
    /// the lane declines from a default test thread without touching the
    /// kernel. The same two-row shape at [`MAX_ROW_VARS`] variables certifies.
    #[test]
    fn sixty_three_variable_row_declines_cleanly_on_the_default_stack() {
        let two_rows = |n: usize| {
            let names: Vec<String> = (0..n).map(|i| format!("w{i:02}")).collect();
            and(vec![ge(sum_of(&names), qi(n as i128 + 1)), le(sum_of(&names), qi(n as i128))])
        };
        assert!(certify_violation(&two_rows(63)).is_none(), "past MAX_ROW_VARS the lane declines");
        let t0 = std::time::Instant::now();
        let (bytes, expr) = cleancic(&two_rows(MAX_ROW_VARS), "Σ ≥ n+1 ∧ Σ ≤ n at MAX_ROW_VARS");
        eprintln!(
            "[real-lane scale] two dense rows over {MAX_ROW_VARS} vars: bytes={} codec_nodes={} certify+recheck={:?}",
            bytes.len(),
            expr_nodes(&expr),
            t0.elapsed()
        );
    }

    /// FM (fixed): dense satisfiable noise rows over 12 variables used to push
    /// Fourier–Motzkin past its row cap so the 13-row bound contradiction
    /// (`Σxᵢ ≤ 1 ∧ xᵢ ≥ 1`) was lost. Interval bound propagation finds it
    /// before FM runs. The noise rows alone (no lower bounds) are SAT and must
    /// not certify.
    #[test]
    fn dense_noise_rows_do_not_hide_a_bound_contradiction() {
        let names: Vec<String> = (0..12).map(|i| format!("x{i}")).collect();
        let noise = |j: usize| {
            let coeffs = [-1i128, 2, 1];
            let lhs = names.iter().enumerate().fold(None, |acc: Option<Formula>, (i, nm)| {
                let t = mul(qi(coeffs[(i + j) % 3]), rv(nm));
                Some(match acc {
                    None => t,
                    Some(a) => add(a, t),
                })
            });
            le(lhs.expect("12 terms"), qi(50 + j as i128))
        };
        let mut rows: Vec<Formula> = names.iter().map(|nm| ge(rv(nm), qi(0))).collect();
        rows.push(le(sum_of(&names), qi(1)));
        let sat_rows = {
            let mut r = rows.clone();
            r.extend((0..9).map(noise));
            r
        };
        assert!(
            certify_violation(&and(sat_rows)).is_none(),
            "the noise system without lower bounds is SAT"
        );
        rows.extend(names[..6].iter().map(|nm| ge(rv(nm), qi(1))));
        rows.extend(names[6..].iter().map(|nm| ge(rv(nm), qi(1))));
        rows.extend((0..9).map(noise));
        assert_eq!(rows.len(), 34);
        let t0 = std::time::Instant::now();
        let (bytes, expr) = cleancic(&and(rows), "noise (12 vars, 9 noise rows)");
        eprintln!(
            "[real-lane scale] noise(12,9): bytes={} codec_nodes={} certify+recheck={:?}",
            bytes.len(),
            expr_nodes(&expr),
            t0.elapsed()
        );
    }

    /// LATENCY: the dense SATISFIABLE 12-variable pool
    /// [`dense_satisfiable_pool_12`] (`xᵢ ≥ 0`, `Σxᵢ ≤ 1`, 15 dense mixed-sign
    /// noise rows — no contradiction) declines on the simplex's exact
    /// `NoWitness` verdict, BEFORE Fourier–Motzkin runs and with no solver
    /// consulted. Measured with FM as the only search: ~1.0 s in debug
    /// (exact-rational FM to `ROW_CAP`); with the simplex ending the search:
    /// tens of ms. The bound is deliberately generous (a debug build on a
    /// loaded machine), but a return to the FM-to-the-cap path on a slower
    /// shape is a multiple of it.
    #[test]
    fn dense_satisfiable_pool_declines_quickly() {
        let pool = dense_satisfiable_pool_12();
        let t0 = std::time::Instant::now();
        let outcome = certify_violation(&pool);
        let elapsed = t0.elapsed();
        eprintln!(
            "[real-lane latency] dense SAT pool (12 vars, 15 noise rows): declined in {elapsed:?}"
        );
        assert!(outcome.is_none(), "the pool is satisfiable (all xᵢ = 0) and must not certify");
        assert!(
            elapsed < std::time::Duration::from_secs(5),
            "a dense SAT pool took {elapsed:?} to decline — the simplex's `NoWitness` verdict \
             must end the search before Fourier–Motzkin runs"
        );
    }

    /// The cheap witnesses respect strictness exactly: a residual of `0` is a
    /// contradiction only when a strict row carries positive weight.
    #[test]
    fn cheap_witnesses_respect_strictness() {
        // Bound propagation: x > 1 ∧ y ≥ 1 ∧ x + y ≤ 2 (strict → infeasible).
        let strict_box =
            and(vec![gt(rv("x"), qi(1)), ge(rv("y"), qi(1)), le(add(rv("x"), rv("y")), qi(2))]);
        let _ = cleancic(&strict_box, "x > 1 ∧ y ≥ 1 ∧ x + y ≤ 2");
        let weak_box =
            and(vec![ge(rv("x"), qi(1)), ge(rv("y"), qi(1)), le(add(rv("x"), rv("y")), qi(2))]);
        assert!(certify_violation(&weak_box).is_none(), "x = y = 1 satisfies the weak twin");
        // A looser strict bound must not outrank a tighter weak one: x > 0 ∧ x ≥ 1 ∧ y ≥ 1 ∧ x + y ≤ 2 is SAT.
        let looser_strict = and(vec![
            gt(rv("x"), qi(0)),
            ge(rv("x"), qi(1)),
            ge(rv("y"), qi(1)),
            le(add(rv("x"), rv("y")), qi(2)),
        ]);
        assert!(certify_violation(&looser_strict).is_none(), "x = y = 1 satisfies it");
        // Proportional pairs: 2x < 2 ∧ x ≥ 1 (strict → infeasible); 2x ≤ 2 ∧ x ≥ 1 is SAT.
        let _ = cleancic(
            &and(vec![lt(mul(qi(2), rv("x")), qi(2)), ge(rv("x"), qi(1))]),
            "2x < 2 ∧ x ≥ 1",
        );
        assert!(
            certify_violation(&and(vec![le(mul(qi(2), rv("x")), qi(2)), ge(rv("x"), qi(1))]))
                .is_none()
        );
        // Bound rows with non-unit coefficients: 3x ≥ 3 ∧ 2y ≤ 2 ∧ y − x ≥ 1/2 is SAT... and y − x > 0 is
        // (x = y = 1 → y − x = 0): the strict target is refuted, the weak one is not.
        let _ = cleancic(
            &and(vec![
                ge(mul(qi(3), rv("x")), qi(3)),
                le(mul(qi(2), rv("y")), qi(2)),
                gt(Formula::Sub(b(rv("y")), b(rv("x"))), qi(0)),
            ]),
            "3x ≥ 3 ∧ 2y ≤ 2 ∧ y − x > 0",
        );
        assert!(
            certify_violation(&and(vec![
                ge(mul(qi(3), rv("x")), qi(3)),
                le(mul(qi(2), rv("y")), qi(2)),
                ge(Formula::Sub(b(rv("y")), b(rv("x"))), qi(0))
            ]))
            .is_none(),
            "x = y = 1 satisfies the weak twin"
        );
    }
}

/// RE-REFUTER 2 (round 2) — PERMANENT pin of a measured process ABORT (FIXED:
/// every public entry point now runs its iterative depth gate on the caller's
/// thread and builds the identity INSIDE `on_certify_stack`; this pin is the
/// regression guard).
///
/// `certify_violation` / `certify_vc` USED TO build the [`ObligationIdentity`]
/// (`bincode::serialize` of the violation — a serde-derived RECURSION) on the
/// CALLER's thread, BEFORE `certify_with_identity`'s depth gate and 256 MiB
/// scoped thread. Measured (debug build, this machine): an `Add` chain deeper
/// than ~180 overflows a default 2 MiB thread there (≈ 11 KB of stack per
/// nesting level), and one deeper than ~750 overflows an 8 MiB main thread —
/// well inside `MAX_VIOLATION_DEPTH = 2048`, so the gate never runs and the
/// process aborts (`SIGABRT`) instead of declining. The wrapper itself is
/// sound: with the identity built elsewhere, `certify_with_identity` declines
/// 2047-, 2049- and 4000-deep chains from a 2 MiB thread. Production
/// (`trust-router` `router.rs` `std::thread::spawn`) calls these entry points
/// from default-stack threads.
///
/// The pin runs the child in a SUBPROCESS so a red pin is a failed assertion,
/// not a dead test binary. It was RED until identity construction moved inside
/// the large-stack thread, behind the depth gate.
#[cfg(test)]
mod refuter2_round2_identity_stack_pin {
    use super::super::certify_violation;
    use super::*;

    fn rv(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Real)
    }
    fn qi(n: i128) -> Formula {
        Formula::rat_from_int(n)
    }
    fn b(f: Formula) -> Box<Formula> {
        Box::new(f)
    }
    /// `x + x + … + x ≤ −1 ∧ x ≥ 0` with `depth` nested `Add`s.
    fn chain(depth: usize) -> Formula {
        let c = (0..depth).fold(rv("x"), |acc, _| Formula::Add(b(acc), b(rv("x"))));
        Formula::And(vec![Formula::Le(b(c), b(qi(-1))), Formula::Ge(b(rv("x")), b(qi(0)))])
    }

    /// Child: one public-API call on the default harness thread, then one via
    /// `std::thread::spawn` (default stack). A no-op without the env var, and
    /// `#[ignore]`d so a plain run does not count that no-op as a pass; the
    /// parent re-executes it with `--ignored --exact`.
    #[test]
    #[ignore = "subprocess child: re-executed by \
                deep_violation_declines_instead_of_aborting_on_a_default_stack"]
    fn deep_chain_child() {
        let Ok(depth) = std::env::var("TRUST_CERTIFY_PIN_CHAIN_DEPTH") else {
            return;
        };
        let depth: usize = depth.parse().expect("depth");
        let v = chain(depth);
        eprintln!("PIN harness depth={depth} some={}", certify_violation(&v).is_some());
        let v2 = chain(depth);
        let some =
            std::thread::spawn(move || certify_violation(&v2).is_some()).join().expect("join");
        eprintln!("PIN spawn depth={depth} some={some}");
        // Deep formulas' own drop glue recurses; not the subject here.
        std::mem::forget(v);
    }

    /// Child for the VC-shaped entry points (`certify_vc`, `recheck_cleancic`,
    /// `recheck_vc_cleancic`, `replay_vc_evidence`): every one of them
    /// serializes the obligation for its identity, and `from_vc` also recurses
    /// into the authenticated-obligation record, so the chain is placed BOTH
    /// as the violation and as the record's body. All on the default harness
    /// thread. A no-op without the env var, and `#[ignore]`d so a plain run does
    /// not count that no-op as a pass; the parent re-executes it with
    /// `--ignored --exact`.
    #[test]
    #[ignore = "subprocess child: re-executed by \
                deep_vc_entry_points_decline_instead_of_aborting_on_a_default_stack"]
    fn deep_chain_vc_child() {
        use trust_types::{ObligationRecord, SourceSpan, VcKind, VerificationCondition};

        use super::super::{certify_vc, recheck_cleancic, recheck_vc_cleancic, replay_vc_evidence};
        let Ok(depth) = std::env::var("TRUST_CERTIFY_PIN_VC_CHAIN_DEPTH") else {
            return;
        };
        let depth: usize = depth.parse().expect("depth");
        let vc = VerificationCondition {
            kind: VcKind::Assertion { message: "deep".to_string() },
            function: "pin".into(),
            location: SourceSpan::default(),
            formula: chain(depth),
            contract_metadata: None,
            obligation: Some(ObligationRecord {
                body: chain(depth),
                wrappers: vec![],
                subject: None,
                width: None,
            }),
        };
        let digest = trust_ir::ProofDigest::zero();
        let evidence = trust_ir::ProofEvidence::CleanCic {
            term: vec![],
            context: vec![],
            lineage: digest.clone(),
            kernel_recheck: None,
        };
        eprintln!(
            "PIN vc depth={depth} certify_vc={} recheck_cleancic={} recheck_vc_cleancic={} \
             replay_vc_evidence={}",
            certify_vc(&vc).is_some(),
            recheck_cleancic(&[], &[], &digest, &vc.formula),
            recheck_vc_cleancic(&[], &[], &digest, &vc),
            replay_vc_evidence(&vc, &evidence)
        );
        // Deep formulas' own drop glue recurses; not the subject here.
        std::mem::forget(vc);
    }

    fn child_status_of(test: &str, var: &str, depth: usize) -> (Option<i32>, Option<i32>, String) {
        use std::os::unix::process::ExitStatusExt;
        let exe = std::env::current_exe().expect("test binary");
        // The child is `#[ignore]`d: `--ignored` selects it, `--exact` only it.
        let out = std::process::Command::new(exe)
            .args(["--ignored", "--exact", test, "--nocapture"])
            .env(var, depth.to_string())
            .env_remove("RUST_MIN_STACK")
            .output()
            .expect("run child");
        let stderr = String::from_utf8_lossy(&out.stderr).to_string();
        (out.status.signal(), out.status.code(), stderr)
    }

    fn child_status(depth: usize) -> (Option<i32>, Option<i32>, String) {
        child_status_of(
            "real_fragment::refuter2_round2_identity_stack_pin::deep_chain_child",
            "TRUST_CERTIFY_PIN_CHAIN_DEPTH",
            depth,
        )
    }

    /// The VC-shaped entry points must likewise DECLINE (`None` / `false`) a
    /// deep obligation from a default-stack thread, never abort — including
    /// past `MAX_VIOLATION_DEPTH` (2047 + the `And`/`Le` levels), where the
    /// iterative gate answers before anything recursive runs.
    #[test]
    fn deep_vc_entry_points_decline_instead_of_aborting_on_a_default_stack() {
        for depth in [150usize, 300, 1000, 2047, 4000] {
            let (sig, code, stderr) = child_status_of(
                "real_fragment::refuter2_round2_identity_stack_pin::deep_chain_vc_child",
                "TRUST_CERTIFY_PIN_VC_CHAIN_DEPTH",
                depth,
            );
            assert_eq!(
                sig, None,
                "{depth}-deep VC: a VC-shaped entry point ABORTED the process (signal {sig:?}):\n\
                 {stderr}"
            );
            assert_eq!(code, Some(0), "{depth}-deep VC: {stderr}");
            assert!(
                stderr.contains(&format!(
                    "PIN vc depth={depth} certify_vc=false recheck_cleancic=false \
                     recheck_vc_cleancic=false replay_vc_evidence=false"
                )),
                "{stderr}"
            );
        }
    }

    /// A 300-deep `Add` chain must DECLINE from a default-stack thread, never
    /// abort the process. (150-deep is the passing control: past
    /// `MAX_TERM_DEPTH`, it declines cleanly today.)
    #[test]
    fn deep_violation_declines_instead_of_aborting_on_a_default_stack() {
        let (sig, code, stderr) = child_status(150);
        assert_eq!(sig, None, "150-deep control must not die by signal:\n{stderr}");
        assert_eq!(code, Some(0), "150-deep control: {stderr}");
        assert!(stderr.contains("PIN harness depth=150 some=false"), "{stderr}");
        assert!(stderr.contains("PIN spawn depth=150 some=false"), "{stderr}");
        for depth in [300usize, 1000, 2047] {
            let (sig, code, stderr) = child_status(depth);
            assert_eq!(
                sig, None,
                "{depth}-deep chain: certify_violation ABORTED the process (signal {sig:?}) — \
                 ObligationIdentity::from_violation's bincode recursion runs on the caller's \
                 stack before the depth gate / 256 MiB thread:\n{stderr}"
            );
            assert_eq!(code, Some(0), "{depth}-deep chain: {stderr}");
            assert!(stderr.contains(&format!("PIN harness depth={depth} some=false")), "{stderr}");
            assert!(stderr.contains(&format!("PIN spawn depth={depth} some=false")), "{stderr}");
        }
    }
}

// ===========================================================================
// FINAL REFUTER — a red pin when written (2026-09-16), green as MEASURED
// 2026-10-09 below; it stays as the regression test. The native-planning entry
// points (`certify_vc_for_native_planning`,
// `vc_fits_native_planning_certification_budget`) serialized the WHOLE VC on the
// caller's thread before anything bounded the authenticated-obligation record.
// ===========================================================================
#[cfg(test)]
mod refuter_final_native_planning_identity_pin {
    use trust_types::{ObligationRecord, SourceSpan, VcKind, VerificationCondition};

    use super::super::{
        certify_vc_for_native_planning, vc_fits_native_planning_certification_budget,
    };
    use super::*;

    fn iv(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }
    fn b(f: Formula) -> Box<Formula> {
        Box::new(f)
    }
    /// `x + x + … + x ≤ −1 ∧ x ≥ 0` over `Sort::Int` with `depth` nested `Add`s.
    fn chain_int(depth: usize) -> Formula {
        let c = (0..depth).fold(iv("x"), |acc, _| Formula::Add(b(acc), b(iv("x"))));
        Formula::And(vec![
            Formula::Le(b(c), b(Formula::Int(-1))),
            Formula::Ge(b(iv("x")), b(Formula::Int(0))),
        ])
    }

    /// Child: `vc.formula` is `true` — shallow, inside the planning grammar —
    /// but the authenticated-obligation record's `body` is a deep chain.
    /// `preflight_unsigned_bv_order_vc_for_native_planning` walks `vc.formula`
    /// iteratively (depth ≤ 16, ≤ 96 nodes) and then calls
    /// `bincode::serialized_size(vc)`, which recurses into `vc.obligation`
    /// (body, subject, wrapper facts/guards) on the CALLER's stack with no
    /// bound at all; `ObligationIdentity::from_vc` would do the same next.
    /// Runs on the default harness thread. A no-op without the env var, and
    /// `#[ignore]`d so a plain run does not count that no-op as a pass; the
    /// parent re-executes it with `--ignored --exact`.
    #[test]
    #[ignore = "subprocess child: re-executed by \
                native_planning_entry_points_decline_instead_of_aborting_on_a_deep_obligation_record"]
    fn native_planning_child() {
        let Ok(depth) = std::env::var("TRUST_CERTIFY_PIN_NP_OBLIGATION_DEPTH") else {
            return;
        };
        let depth: usize = depth.parse().expect("depth");
        let vc = VerificationCondition {
            kind: VcKind::IndexOutOfBounds,
            function: "np".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: Some(ObligationRecord {
                body: chain_int(depth),
                wrappers: vec![],
                subject: None,
                width: None,
            }),
        };
        eprintln!("NP depth={depth} fits={}", vc_fits_native_planning_certification_budget(&vc));
        eprintln!("NP depth={depth} certify={}", certify_vc_for_native_planning(&vc).is_some());
        // Deep formulas' own drop glue recurses; not the subject here.
        std::mem::forget(vc);
    }

    /// MEASURED 2026-09-16 (debug build, 2 MiB harness thread): depth 16
    /// `fits=true certify=false`; depth 150 `fits=false` (declined on the
    /// 2 KiB identity cap — but only AFTER recursing); depth 300 / 1000 / 4000
    /// SIGABRT (signal 6). The general entry points (`certify_vc`,
    /// `certify_violation`, `recheck_cleancic`, `recheck_vc_cleancic`,
    /// `replay_vc_evidence`) gate every obligation-record formula through the
    /// iterative `vc_within_depth_gate` first; this path does not. RED until
    /// the preflight bounds the record (or refuses `obligation: Some(_)`,
    /// which the compiler's guarded-index lane never populates) BEFORE
    /// `serialized_size` / `from_vc`.
    ///
    /// MEASURED 2026-10-09 (debug build, default harness thread): every depth
    /// exits 0; depth 16 `fits=true certify=false`, depths 150 / 300 / 1000 /
    /// 4000 `fits=false certify=false`.
    ///
    /// A clean exit alone proves nothing: a child filter that selects no test
    /// (a renamed child, a moved module) also exits 0. So every depth must
    /// print BOTH `NP` lines, and the record must DECLINE (`certify=false`) at
    /// every depth; `fits=` is required to be present, not pinned.
    #[test]
    fn native_planning_entry_points_decline_instead_of_aborting_on_a_deep_obligation_record() {
        use std::os::unix::process::ExitStatusExt;
        let mut failures: Vec<String> = Vec::new();
        for depth in [16usize, 150, 300, 1000, 4000] {
            let exe = std::env::current_exe().expect("test binary");
            // The child is `#[ignore]`d: `--ignored` selects it, `--exact` only it.
            let out = std::process::Command::new(exe)
                .args([
                    "--ignored",
                    "--exact",
                    "real_fragment::refuter_final_native_planning_identity_pin::native_planning_child",
                    "--nocapture",
                ])
                .env("TRUST_CERTIFY_PIN_NP_OBLIGATION_DEPTH", depth.to_string())
                .env_remove("RUST_MIN_STACK")
                .output()
                .expect("run child");
            let stderr = String::from_utf8_lossy(&out.stderr).to_string();
            let np: Vec<&str> = stderr.lines().filter(|l| l.starts_with("NP ")).collect();
            let line = format!(
                "depth={depth}: signal={:?} code={:?} {}",
                out.status.signal(),
                out.status.code(),
                np.join(" | ")
            );
            eprintln!("PIN native-planning {line}");
            if out.status.signal().is_some() || out.status.code() != Some(0) {
                failures.push(line);
                continue;
            }
            let fits = format!("NP depth={depth} fits=");
            if !np.iter().any(|l| l.starts_with(&fits)) {
                failures.push(format!(
                    "{line}: no `{fits}` line: the child did not run (stdout:\n{})",
                    String::from_utf8_lossy(&out.stdout)
                ));
                continue;
            }
            let declined = format!("NP depth={depth} certify=false");
            if !np.iter().any(|l| l.trim_end() == declined) {
                failures.push(format!("{line}: expected `{declined}`"));
            }
        }
        assert!(
            failures.is_empty(),
            "certify_vc_for_native_planning / vc_fits_native_planning_certification_budget \
             on a deep authenticated-obligation record: the child ABORTED (the planning \
             preflight bounds `vc.formula` but serializes the whole VC, obligation record \
             included, on the caller's stack), did not run, or did not decline:\n{}",
            failures.join("\n")
        );
    }
}

/// The exact-rational simplex Farkas search ([`simplex_farkas`]): the shapes
/// Fourier–Motzkin declined now certify, seeded dense infeasible systems
/// certify end to end, seeded satisfiable systems never produce a witness (the
/// verifier rejects every candidate), the strict-row (Motzkin) shapes are
/// found by the simplex alone, the caps decline cleanly, certificates are
/// byte-deterministic across uncached runs, and the timings are measured.
#[cfg(test)]
mod simplex_farkas_tests {
    use trust_ir::ProofEvidence;

    use super::super::{
        certify_lanes, certify_violation, deserialize_term, normalize_violation, recheck_cleancic,
    };
    use super::*;

    /// One row `0 ≤ Σ aⱼ·xⱼ + c` (`strict`: `0 <`) with integer data.
    #[derive(Clone, Debug)]
    struct Row {
        terms: Vec<(String, i64)>,
        c: i64,
        strict: bool,
    }

    fn rv(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Real)
    }
    fn qi(n: i64) -> Formula {
        Formula::rat_from_int(n as i128)
    }
    fn b(f: Formula) -> Box<Formula> {
        Box::new(f)
    }

    /// The row list the lane builds: zero coefficients dropped, duplicates
    /// summed, exactly [`RTerm::linform`]'s shape.
    fn rlin_rows(rows: &[Row]) -> Vec<(RLin, bool)> {
        rows.iter()
            .map(|r| {
                let mut terms: BTreeMap<String, Q> = BTreeMap::new();
                for (x, a) in &r.terms {
                    let v = terms.get(x).cloned().unwrap_or_else(|| q_from_int(0)) + q_from_int(*a);
                    if q_is_zero(&v) {
                        terms.remove(x);
                    } else {
                        terms.insert(x.clone(), v);
                    }
                }
                (RLin { terms, c: q_from_int(r.c) }, r.strict)
            })
            .collect()
    }

    /// The violation spelling `Σ aⱼ·xⱼ ≥ −c` (`>` when strict), which
    /// normalizes to the row `0 ≤ Σ aⱼ·xⱼ + c`.
    fn formula(rows: &[Row]) -> Formula {
        Formula::And(
            rows.iter()
                .map(|r| {
                    let mut lhs: Option<Formula> = None;
                    for (x, a) in &r.terms {
                        let t = if *a == 1 { rv(x) } else { Formula::Mul(b(qi(*a)), b(rv(x))) };
                        lhs = Some(match lhs {
                            None => t,
                            Some(acc) => Formula::Add(b(acc), b(t)),
                        });
                    }
                    let lhs = lhs.unwrap_or_else(|| qi(0));
                    if r.strict {
                        Formula::Gt(b(lhs), b(qi(-r.c)))
                    } else {
                        Formula::Ge(b(lhs), b(qi(-r.c)))
                    }
                })
                .collect(),
        )
    }

    /// The rows the LANE derives from a violation (through the real atom
    /// collector), so a measurement runs the search on exactly the lane's input.
    fn lane_rows(violation: &Formula) -> Vec<(RLin, bool)> {
        let normalized = normalize_violation(violation).expect("normalizes");
        let conjuncts = normalized.view();
        let (atoms, _) = collect_real_atoms(&conjuncts).expect("real atoms");
        atoms
            .iter()
            .map(|ra| (ra.rhs.linform().add(&ra.lhs.linform().scale(&q_from_int(-1))), ra.strict))
            .collect()
    }

    fn certified(violation: &Formula, what: &str) -> (Vec<u8>, Expr) {
        match certify_violation(violation) {
            Some(ProofEvidence::CleanCic { term, context, lineage, .. }) => {
                assert!(recheck_cleancic(&term, &context, &lineage, violation), "{what}: recheck");
                let expr = deserialize_term(&term).expect("producer's own serialization");
                (term, expr)
            }
            other => panic!("{what}: expected Some(CleanCic), got {other:?}"),
        }
    }

    // ── deterministic PRNG (xorshift64) ───────────────────────────────────
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
        fn range(&mut self, lo: i64, hi: i64) -> i64 {
            lo + (self.next() % ((hi - lo + 1) as u64)) as i64
        }
        fn coin(&mut self) -> bool {
            self.next() & 1 == 1
        }
        fn shuffle<T>(&mut self, v: &mut [T]) {
            for i in (1..v.len()).rev() {
                let j = self.range(0, i as i64) as usize;
                v.swap(i, j);
            }
        }
    }

    fn names(n: usize) -> Vec<String> {
        (0..n).map(|i| format!("x{i:02}")).collect()
    }

    /// A dense row over ALL of `vars` with coefficients in `[-3, 3] \ {0}`
    /// (never a single-variable row, so bound propagation cannot fire).
    fn dense_terms(rng: &mut Rng, vars: &[String]) -> Vec<(String, i64)> {
        vars.iter()
            .map(|x| {
                let mut a = rng.range(-3, 3);
                if a == 0 {
                    a = if rng.coin() { 1 } else { -1 };
                }
                (x.clone(), a)
            })
            .collect()
    }

    /// A row TRUE at the integer point `p` with slack `≥ 1` (so a strict
    /// spelling stays true): `c = −Σ aⱼ pⱼ + slack`.
    fn true_row(rng: &mut Rng, vars: &[String], p: &[i64], strict: bool) -> Row {
        let terms = dense_terms(rng, vars);
        let val: i64 = terms.iter().enumerate().map(|(j, (_, a))| a * p[j]).sum();
        Row { terms, c: -val + rng.range(1, 6), strict }
    }

    /// An INFEASIBLE core by construction: `k − 1` random dense rows with
    /// positive integer multipliers `λᵢ`, and a last row equal to `−Σ λᵢ rowᵢ`
    /// on every coefficient with its constant chosen so that `Σ λᵢ cᵢ + c_k`
    /// is `−1` (Farkas) or, when `motzkin`, `0` with one core row strict.
    fn infeasible_core(rng: &mut Rng, vars: &[String], k: usize, motzkin: bool) -> Vec<Row> {
        let mut rows: Vec<Row> = Vec::with_capacity(k);
        let mut lambdas: Vec<i64> = Vec::with_capacity(k - 1);
        for _ in 0..k - 1 {
            rows.push(Row { terms: dense_terms(rng, vars), c: rng.range(-5, 5), strict: false });
            lambdas.push(rng.range(1, 3));
        }
        if motzkin {
            let s = rng.range(0, k as i64 - 2) as usize;
            rows[s].strict = true;
        }
        let mut last: Vec<(String, i64)> = Vec::with_capacity(vars.len());
        for (j, x) in vars.iter().enumerate() {
            let sum: i64 = rows.iter().zip(&lambdas).map(|(r, l)| l * r.terms[j].1).sum();
            last.push((x.clone(), -sum));
        }
        let csum: i64 = rows.iter().zip(&lambdas).map(|(r, l)| l * r.c).sum();
        rows.push(Row { terms: last, c: if motzkin { -csum } else { -1 - csum }, strict: false });
        rows
    }

    /// The 12-variable / 40-row dense contradiction: a 4-row infeasible core
    /// (multipliers 1, 2, 1, 1 — needs all four rows) under 36 dense
    /// mixed-sign noise rows that are jointly satisfiable (true at the origin
    /// shifted by a random point).
    fn dense_four_row_system() -> Vec<Row> {
        let vars = names(12);
        let mut rng = Rng(0x2545_F491_4F6C_DD1D);
        let mut rows = infeasible_core(&mut rng, &vars, 4, false);
        let p: Vec<i64> = (0..12).map(|_| rng.range(-2, 2)).collect();
        for _ in 0..36 {
            rows.push(true_row(&mut rng, &vars, &p, false));
        }
        rng.shuffle(&mut rows);
        rows
    }

    /// A dense INFEASIBLE pool: a `k`-row core under `nrows − k` dense
    /// satisfiable noise rows, shuffled — the shape the budget tests and the
    /// pinned-bytes test are built on (`seed` fixes the whole construction).
    fn seeded_dense_pool(seed: u64, nv: usize, nrows: usize, k: usize) -> Vec<Row> {
        let vars = names(nv);
        let mut rng = Rng(seed);
        let mut rows = infeasible_core(&mut rng, &vars, k, false);
        let p: Vec<i64> = (0..nv).map(|_| rng.range(-2, 2)).collect();
        while rows.len() < nrows {
            rows.push(true_row(&mut rng, &vars, &p, false));
        }
        rng.shuffle(&mut rows);
        rows
    }

    /// SHA-256 of a byte string, hex — the pinned-bytes tests compare these.
    fn sha256_hex(bytes: &[u8]) -> String {
        use sha2::{Digest, Sha256};
        let mut h = Sha256::new();
        h.update(bytes);
        h.finalize().iter().map(|b| format!("{b:02x}")).collect()
    }

    /// The certificate bytes of a violation, UNCACHED (the producer run, not a
    /// memoized payload).
    fn uncached_bytes(violation: &Formula) -> Option<Vec<u8>> {
        let identity = ObligationIdentity::from_violation(violation)?;
        match certify_lanes(violation, &identity)? {
            ProofEvidence::CleanCic { term, .. } => Some(term),
            _ => None,
        }
    }

    /// A `mip-46963` system: `(kind, k, terms)` rows, `kind` `"le"` for `Σ ≤
    /// k` and anything else for `Σ ≥ k`.
    fn mip_system(system: &[(&str, i64, &[(&str, i64)])]) -> Formula {
        Formula::And(
            system
                .iter()
                .map(|(kind, k, terms)| {
                    let mut lhs: Option<Formula> = None;
                    for (x, a) in terms.iter() {
                        let t = if *a == 1 { rv(x) } else { Formula::Mul(b(qi(*a)), b(rv(x))) };
                        lhs = Some(match lhs {
                            None => t,
                            Some(acc) => Formula::Add(b(acc), b(t)),
                        });
                    }
                    let lhs = lhs.expect("terms");
                    match *kind {
                        "le" => Formula::Le(b(lhs), b(qi(*k))),
                        _ => Formula::Ge(b(lhs), b(qi(*k))),
                    }
                })
                .collect(),
        )
    }

    const MIP_000012: &[(&str, i64, &[(&str, i64)])] =
        &[("le", 1, &[("x0", 1)]), ("ge", -3, &[("x0", 2), ("x1", -1)]), ("ge", 10, &[("x1", 1)])];
    const MIP_000021: &[(&str, i64, &[(&str, i64)])] = &[
        ("le", 1, &[("x1", 1)]),
        ("le", 1, &[("x5", 1)]),
        ("ge", 0, &[("x1", 1), ("x3", -1)]),
        ("ge", 0, &[("x3", 1), ("x5", 1), ("x8", -1)]),
        ("ge", 10, &[("x8", 1)]),
    ];
    const MIP_000023: &[(&str, i64, &[(&str, i64)])] = &[
        ("le", 1, &[("x0", 1)]),
        ("le", 1, &[("x1", 1)]),
        ("ge", 1, &[("x6", 1)]),
        ("ge", 0, &[("x1", 1), ("x3", -1)]),
        ("ge", 1, &[("x0", 1), ("x1", 1), ("x4", -1)]),
        ("le", 1, &[("x4", -1), ("x5", 1), ("x6", 1)]),
        ("ge", 0, &[("x3", 1), ("x5", 1), ("x8", -1)]),
        ("ge", 10, &[("x8", 1)]),
    ];

    /// The crown `y ≤ 2x ∧ x ≤ 1/2 ∧ y > 1`.
    fn crown_system() -> Formula {
        Formula::And(vec![
            Formula::Le(b(rv("y")), b(Formula::Mul(b(qi(2)), b(rv("x"))))),
            Formula::Le(b(rv("x")), b(Formula::rat("1", "2").expect("literal"))),
            Formula::Gt(b(rv("y")), b(qi(1))),
        ])
    }

    /// The ny-cert box system: `0 ≤ vᵢ ≤ 1` for `n` variables and `Σ vᵢ ≥ n + 1`.
    fn box_system(n: usize) -> Formula {
        let nm: Vec<String> = (0..n).map(|i| format!("v{i:03}")).collect();
        let mut rows = Vec::new();
        for x in &nm {
            rows.push(Formula::Ge(b(rv(x)), b(qi(0))));
            rows.push(Formula::Le(b(rv(x)), b(qi(1))));
        }
        let sum = nm[1..].iter().fold(rv(&nm[0]), |acc, x| Formula::Add(b(acc), b(rv(x))));
        rows.push(Formula::Ge(b(sum), b(qi(n as i64 + 1))));
        Formula::And(rows)
    }

    /// The 12-variable noise case: a box contradiction (`xᵢ ≥ 0`, `Σ ≤ 1`, `xᵢ
    /// ≥ 1`) under `noise` dense satisfiable rows.
    fn noise_system(noise: usize) -> Formula {
        let nm: Vec<String> = (0..12).map(|i| format!("x{i}")).collect();
        let mut rows: Vec<Formula> = nm.iter().map(|x| Formula::Ge(b(rv(x)), b(qi(0)))).collect();
        let sum = nm[1..].iter().fold(rv(&nm[0]), |acc, x| Formula::Add(b(acc), b(rv(x))));
        rows.push(Formula::Le(b(sum), b(qi(1))));
        rows.extend(nm.iter().map(|x| Formula::Ge(b(rv(x)), b(qi(1)))));
        for j in 0..noise {
            let coeffs = [-1i64, 2, 1];
            let lhs = nm.iter().enumerate().fold(None, |acc: Option<Formula>, (i, x)| {
                let t = Formula::Mul(b(qi(coeffs[(i + j) % 3])), b(rv(x)));
                Some(match acc {
                    None => t,
                    Some(a) => Formula::Add(b(a), b(t)),
                })
            });
            rows.push(Formula::Le(b(lhs.expect("terms")), b(qi(50 + j as i64))));
        }
        Formula::And(rows)
    }

    /// The lane's reference shapes, named.
    fn reference_shapes() -> Vec<(String, Formula)> {
        let mut shapes: Vec<(String, Formula)> = vec![
            ("mip-46963-000012".into(), mip_system(MIP_000012)),
            ("mip-46963-000021".into(), mip_system(MIP_000021)),
            ("mip-46963-000022".into(), mip_system(MIP_000021)),
            ("mip-46963-000023".into(), mip_system(MIP_000023)),
            ("crown".into(), crown_system()),
        ];
        for n in [10usize, 15, 20, 25, 30] {
            shapes.push((format!("box n={n}"), box_system(n)));
        }
        shapes.push(("noise(12,9)".into(), noise_system(9)));
        shapes.push(("noise(12,15)".into(), noise_system(15)));
        shapes.push(("dense 4-row/12-var/40 rows".into(), formula(&dense_four_row_system())));
        shapes
    }

    /// (DETERMINISM ACROSS THE BUDGET CHANGE, PINNED) The simplex witness and
    /// the certificate bytes of every reference shape and of two mid-size
    /// dense infeasible pools that go through the simplex, pinned as SHA-256
    /// digests RECORDED FROM THE TREE BEFORE the work budget and the
    /// integer-preserving pivoting landed (the rational tableau, no meter).
    /// The budget leaves these shapes untouched (each spends under a tenth of
    /// it), and fraction-free pivoting under positive column scaling visits
    /// exactly the bases the rational tableau visited, so the multipliers —
    /// and with them the certificate — must be byte-identical. A digest that
    /// moves here is a change in what the lane PRODUCES, which
    /// `recheck_cleancic` (regenerate and byte-compare) would refuse.
    #[test]
    fn simplex_certificates_are_pinned_across_the_budget_change() {
        let mut shapes = reference_shapes();
        shapes.push((
            "pool 16x30".into(),
            formula(&seeded_dense_pool(0x1234_5678_9ABC_DEF1, 16, 30, 4)),
        ));
        shapes.push((
            "pool 14x24".into(),
            formula(&seeded_dense_pool(0x0F0F_1E1E_2D2D_3C3C, 14, 24, 5)),
        ));
        for (what, witness_digest, len, digest) in SIMPLEX_CERTIFICATE_PINS {
            let violation = &shapes.iter().find(|(w, _)| w == what).expect("a reference shape").1;
            let rows = lane_rows(violation);
            let (w, work) = simplex_farkas_metered(&rows);
            let w = w.expect("the simplex finds the witness");
            assert_eq!(
                sha256_hex(format!("{w:?}").as_bytes()),
                *witness_digest,
                "{what}: the simplex multipliers moved"
            );
            assert!(
                work.spent * 10 <= SIMPLEX_WORK_BUDGET,
                "{what}: spends {} — not well under the budget",
                work.spent
            );
            let bytes = uncached_bytes(violation).expect("certifies");
            assert_eq!(bytes.len(), *len, "{what}: certificate length moved");
            assert_eq!(sha256_hex(&bytes), *digest, "{what}: certificate bytes moved");
        }
    }

    /// The pins of [`simplex_certificates_are_pinned_across_the_budget_change`]:
    /// (shape, witness digest, certificate length, certificate digest), each
    /// recorded from the tree BEFORE the work budget landed and unmoved since
    /// — the retired ay pre-solve produced no artifact, so its removal could
    /// not move them either ([`real_lane_certifies_without_an_ay_pre_solve`]).
    const SIMPLEX_CERTIFICATE_PINS: &[(&str, &str, usize, &str)] = &[
        (
            "mip-46963-000012",
            "af61ebe01d3728d74e914450cf8dbc6fa00f031af4d829502e7e0fa4c7680f73",
            43448,
            "b4396d08606fd3c0c841375c1e9e9e70d5f5eab9780d462259e562748eed3559",
        ),
        (
            "mip-46963-000021",
            "39549d62aff8c327168538b04bde60ef53955a59001fbfb2e52427cccf60241e",
            127358,
            "bbda6c9fecddfd47eeae20089a46d26dba2a7b376a898b00073bb7d0a82013e7",
        ),
        (
            "mip-46963-000023",
            "9d470c49183c0d61e2a7d489bb792d57f8122900ad7b07607f1bb49eca6f73bd",
            257543,
            "a7b2d9f06480539f255c76b251373042b72fb9fcb998c5c94938ec5bfacd122f",
        ),
        (
            "crown",
            "10830658a133f017f970c03f7988343c9ea1737c3319339e37e2533a911eb93f",
            41347,
            "50bdb4f83547c96536c79c0e06d0119d2112ae7a1e9a32a6f047c05bcea5cffc",
        ),
        (
            "box n=10",
            "1075bbf4015ce784b0ff6887aeec6f027b485ac9548e66d902b8415dce67085a",
            215039,
            "a5a167919ebbc47a480698912a5098d8188c4192f6a654f0f3c60650ecbfd9aa",
        ),
        (
            "box n=20",
            "37c08763d258f276d23f670466842f5d76295f63e72cda0da3ffa25eaec5b5e1",
            611719,
            "8e9903b6851d954369138ea0cfe3f89a23fd979354a3cf0ffc53f8926b3ba60b",
        ),
        (
            "box n=30",
            "727fdfeac23cd774b52b3d281f868d5d316b8e1a880e1397cb9f2b0fb9c913f2",
            1196999,
            "e4082da5f637207594f2a7b3233ec469f0ded90c4a2ea6701024e028c7bdaac5",
        ),
        (
            "noise(12,9)",
            "3716aa8fb192dec6fcf50fc7685cf408f116c72b80dce4c1310b7c4079a08f28",
            418018,
            "37594b619c9702bfbbf2f42bcd2737fd439389c83609622bf74aac540ea3c0a9",
        ),
        (
            "noise(12,15)",
            "cae65fa27434ad5d810b164ff46922fcff84f5c05d1479b02f6c80c5d6b31518",
            418018,
            "37594b619c9702bfbbf2f42bcd2737fd439389c83609622bf74aac540ea3c0a9",
        ),
        (
            "dense 4-row/12-var/40 rows",
            "931b1767df13e2fdf8ea11ff5011657e1757790c6d8ea490bf3ff787f6d1eb89",
            3606632,
            "2507071812c49681f1164bf53ec8d8bad51e4b27ec591fdf6c365d20f73c9cbc",
        ),
        (
            "pool 16x30",
            "ac896df0ff5a26fef1f21f71bd2a62aac4e33955733230edf8dd0a237cc39605",
            1164365,
            "9837882a9f69228bb90ff13aa8d1df028be0cc90cdce3a19c6b84f70509f2ed0",
        ),
        (
            "pool 14x24",
            "1a6a481291681d64be75139223bc6a422bbec130817d07c3ef43cf3c88f22da5",
            1268937,
            "05a453d23c9e1fd252db3f0e47dd9fd93cc5f16c0f42435db761d51870e2b408",
        ),
    ];

    /// (`NoWitness` ENDS THE SEARCH) On satisfiable pools the simplex
    /// completes Phase-1 with a positive optimum and reports the exact
    /// [`SimplexSearch::NoWitness`]; the lane search then returns `None`
    /// WITHOUT running Fourier–Motzkin — and FM, asked directly, returns
    /// `None` on every one of them, the equivalence [`SimplexSearch`]'s doc
    /// argues, checked here on the 12-variable dense SAT pool of
    /// `dense_satisfiable_pool_declines_quickly` and on 50 seeded
    /// satisfiable-by-construction systems over 8–20 variables.
    #[test]
    fn simplex_search_reports_no_witness_on_satisfiable_pools() {
        let mut pools: Vec<(String, Vec<(RLin, bool)>)> = vec![(
            "dense SAT pool (12 vars, 15 noise rows)".into(),
            lane_rows(&dense_satisfiable_pool_12()),
        )];
        let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
        for case in 0..50 {
            let nv = rng.range(8, 20) as usize;
            let vars = names(nv);
            let p: Vec<i64> = (0..nv).map(|_| rng.range(-3, 3)).collect();
            let nrows = rng.range(6, 14) as usize;
            let rows: Vec<Row> = (0..nrows)
                .map(|_| {
                    let strict = rng.coin();
                    true_row(&mut rng, &vars, &p, strict)
                })
                .collect();
            pools.push((format!("seeded satisfiable case {case}"), rlin_rows(&rows)));
        }
        for (what, lin) in &pools {
            assert!(cheap_farkas_witness(lin).is_none(), "{what}: no cheap witness");
            assert_eq!(
                simplex_farkas_search(lin),
                SimplexSearch::NoWitness,
                "{what}: Phase-1 must complete with a positive optimum"
            );
            assert!(find_farkas_multipliers_real(lin).is_none(), "{what}: the lane search is None");
            assert!(fourier_motzkin(lin).is_none(), "{what}: FM would have said None as well");
        }
    }

    /// (A CAP DECLINE STILL REACHES FM) The 200-variable pool of
    /// [`widest_admitted_pools`] — sparse, 32 of 200 variables per row —
    /// exhausts the work meter, so the simplex reports
    /// [`SimplexSearch::Declined`] (nothing known, NOT `NoWitness`), and the
    /// SEARCH (`find_farkas_multipliers_real`, on the raw row list) falls
    /// through to greedy Fourier–Motzkin, which finds the witness the simplex
    /// was not allowed to. This is a statement about the search alone: the
    /// LANE never sees this pool's core, whose 96-wide row exceeds
    /// `MAX_TERM_DEPTH` and is dropped at atom collection, so end to end the
    /// pool declines on the fragment caps before any search runs.
    #[test]
    fn simplex_search_declines_to_fm_on_the_sparse_wide_pool() {
        let pools = widest_admitted_pools();
        let (what, lin, _) =
            pools.iter().find(|(w, _, _)| w.contains("200 vars")).expect("the 200-variable pool");
        let t0 = std::time::Instant::now();
        assert_eq!(
            simplex_farkas_search(lin),
            SimplexSearch::Declined,
            "{what}: expected a meter decline"
        );
        let st = t0.elapsed();
        let t0 = std::time::Instant::now();
        let (mult, strict) =
            find_farkas_multipliers_real(lin).expect("the lane search reaches FM and certifies");
        let lt = t0.elapsed();
        assert_eq!(verify_farkas_witness(lin, &mult), Some(strict), "{what}: the witness verifies");
        assert_eq!(
            fourier_motzkin(lin),
            Some((mult, strict)),
            "{what}: the lane's witness is FM's witness"
        );
        eprintln!("[simplex-search] {what}: simplex declined in {st:?}, FM certified in {lt:?}");
    }

    /// (NO ay PRE-SOLVE, BYTES UNMOVED) Two certifying shapes go end to end
    /// through the producer — search, replay, codec gate, the finish tail's
    /// single ay cross-check, kernel re-check, round-trip — and the bytes
    /// equal the pins in [`SIMPLEX_CERTIFICATE_PINS`], recorded before the
    /// budget change and before the ay pre-solve was retired: the search
    /// change only altered `None` paths, and the pre-solve produced no
    /// artifact, so neither could move a byte.
    #[test]
    fn real_lane_certifies_without_an_ay_pre_solve() {
        let shapes = reference_shapes();
        for what in ["mip-46963-000012", "crown"] {
            let (_, _, len, digest) =
                SIMPLEX_CERTIFICATE_PINS.iter().find(|(w, ..)| *w == what).expect("pinned");
            let violation = &shapes.iter().find(|(w, _)| w == what).expect("a reference shape").1;
            let identity = ObligationIdentity::from_violation(violation).expect("identity");
            let t0 = std::time::Instant::now();
            let Some(ProofEvidence::CleanCic { term, context, lineage, .. }) =
                certify_lanes(violation, &identity)
            else {
                panic!("{what}: expected Some(CleanCic)");
            };
            let elapsed = t0.elapsed();
            assert!(recheck_cleancic(&term, &context, &lineage, violation), "{what}: recheck");
            assert_eq!(term.len(), *len, "{what}: certificate length moved");
            assert_eq!(sha256_hex(&term), *digest, "{what}: certificate bytes moved");
            eprintln!("[real-lane] {what}: certified end to end in {elapsed:?}");
        }
    }

    // ── the adversarial round's generator: exact-rational rows ────────────

    /// One row with exact-rational data (`0 ≤ Σ aⱼ·xⱼ + c`, `strict`: `0 <`).
    #[derive(Clone, Debug)]
    struct RRow {
        terms: Vec<(String, Q)>,
        c: Q,
        strict: bool,
    }

    fn q(n: i64, d: i64) -> Q {
        Q::new(BigInt::from(n), BigInt::from(d))
    }

    fn lit(v: &Q) -> Formula {
        Formula::rat(&v.numer().to_string(), &v.denom().to_string()).expect("canonical literal")
    }

    impl Rng {
        /// A non-zero coefficient in `[-mag, mag]`, rational with probability ~1/4.
        fn coeff(&mut self, mag: i64, rational: bool) -> Q {
            let mut n = self.range(-mag, mag);
            if n == 0 {
                n = if self.coin() { 1 } else { -1 };
            }
            let d = if rational && self.range(0, 3) == 0 { self.range(2, 5) } else { 1 };
            q(n, d)
        }
    }

    fn rlin_rrows(rows: &[RRow]) -> Vec<(RLin, bool)> {
        rows.iter()
            .map(|r| {
                let mut terms: BTreeMap<String, Q> = BTreeMap::new();
                for (x, a) in &r.terms {
                    let v = terms.get(x).cloned().unwrap_or_else(|| q_from_int(0)) + a;
                    if q_is_zero(&v) {
                        terms.remove(x);
                    } else {
                        terms.insert(x.clone(), v);
                    }
                }
                (RLin { terms, c: r.c.clone() }, r.strict)
            })
            .collect()
    }

    /// `Σ aⱼ·xⱼ ≥ −c` (`>` when strict), which normalizes to `0 ≤ Σ aⱼ·xⱼ + c`.
    fn rformula(rows: &[RRow]) -> Formula {
        Formula::And(
            rows.iter()
                .map(|r| {
                    let mut lhs: Option<Formula> = None;
                    for (x, a) in &r.terms {
                        let t = if *a == q_from_int(1) {
                            rv(x)
                        } else {
                            Formula::Mul(b(lit(a)), b(rv(x)))
                        };
                        lhs = Some(match lhs {
                            None => t,
                            Some(acc) => Formula::Add(b(acc), b(t)),
                        });
                    }
                    let lhs = lhs.unwrap_or_else(|| Formula::rat_from_int(0));
                    let rhs = lit(&(-&r.c));
                    if r.strict { Formula::Gt(b(lhs), b(rhs)) } else { Formula::Ge(b(lhs), b(rhs)) }
                })
                .collect(),
        )
    }

    /// A row true at point `p` with slack `≥ min_slack` over a random
    /// `width`-subset of `vars`, coefficients up to 9 in magnitude.
    fn rsat_row(
        rng: &mut Rng,
        vars: &[String],
        p: &[Q],
        width: usize,
        strict: bool,
        rational: bool,
        min_slack: i64,
    ) -> RRow {
        let mut idx: Vec<usize> = (0..vars.len()).collect();
        rng.shuffle(&mut idx);
        idx.truncate(width);
        idx.sort_unstable();
        let terms: Vec<(String, Q)> =
            idx.iter().map(|&j| (vars[j].clone(), rng.coeff(9, rational))).collect();
        let val = idx.iter().zip(&terms).fold(q_from_int(0), |acc, (&j, (_, a))| acc + a * &p[j]);
        let slack = q(rng.range(min_slack, 6), if rational && rng.coin() { 3 } else { 1 });
        RRow { terms, c: -val + slack, strict }
    }

    /// An infeasible core with RATIONAL positive multipliers `λᵢ ∈ {1/3, 1/2,
    /// 1, 3/2, 2, 5/2}` over `width`-subsets of `vars`, and a last row equal
    /// to `−Σ λᵢ rowᵢ` with residual `−δ` (`δ ∈ {1, 1/2, 1/7}`), or `0` with a
    /// strict core row (Motzkin).
    fn rinfeasible_core(
        rng: &mut Rng,
        vars: &[String],
        k: usize,
        width: usize,
        motzkin: bool,
        rational: bool,
    ) -> Vec<RRow> {
        let lams = [q(1, 3), q(1, 2), q(1, 1), q(3, 2), q(2, 1), q(5, 2)];
        let mut rows: Vec<RRow> = Vec::new();
        let mut lambdas: Vec<Q> = Vec::new();
        for _ in 0..k - 1 {
            let mut idx: Vec<usize> = (0..vars.len()).collect();
            rng.shuffle(&mut idx);
            idx.truncate(width);
            idx.sort_unstable();
            let terms = idx.iter().map(|&j| (vars[j].clone(), rng.coeff(5, rational))).collect();
            rows.push(RRow { terms, c: q(rng.range(-5, 5), 1), strict: false });
            lambdas.push(lams[rng.range(0, 5) as usize].clone());
        }
        if motzkin {
            let s = rng.range(0, k as i64 - 2) as usize;
            rows[s].strict = true;
        }
        let mut sums: BTreeMap<String, Q> = BTreeMap::new();
        let mut csum = q_from_int(0);
        for (r, l) in rows.iter().zip(&lambdas) {
            csum += l * &r.c;
            for (x, a) in &r.terms {
                *sums.entry(x.clone()).or_insert_with(|| q_from_int(0)) += l * a;
            }
        }
        let last: Vec<(String, Q)> =
            sums.into_iter().filter(|(_, v)| !q_is_zero(v)).map(|(x, v)| (x, -v)).collect();
        let delta = match rng.range(0, 2) {
            0 => q(1, 1),
            1 => q(1, 2),
            _ => q(1, 7),
        };
        rows.push(RRow {
            terms: last,
            c: if motzkin { -csum } else { -delta - csum },
            strict: false,
        });
        rows
    }

    /// The adversarial round's pool: `nrows` rows over `nvars` variables,
    /// `width` per row, a `k`-row core (the refuter's `rf_pivot_cap_at_lane_caps`
    /// / `rf_wide_pool_cost` construction).
    fn refuter_pool(seed: u64, nvars: usize, width: usize, nrows: usize, k: usize) -> Vec<RRow> {
        let vars = names(nvars);
        let mut rng = Rng(seed);
        let mut rows = rinfeasible_core(&mut rng, &vars, k, width, false, false);
        let p: Vec<Q> = (0..nvars).map(|_| q(rng.range(-2, 2), 1)).collect();
        while rows.len() < nrows {
            rows.push(rsat_row(&mut rng, &vars, &p, width, false, false, 0));
        }
        rng.shuffle(&mut rows);
        rows
    }

    /// The widest ADMITTED pools — the shapes the work budget exists for:
    /// dense 32-variable × 64-row pools from the adversarial round's generator
    /// (`MAX_ROW_VARS` × `MAX_REAL_ATOMS`, rational core multipliers,
    /// coefficients up to 9), the in-tree dense 32×64 pool, and 64- and
    /// 200-variable pools of 32-wide rows (inside `SIMPLEX_CELL_BUDGET`).
    fn widest_admitted_pools() -> Vec<(String, Vec<(RLin, bool)>, Formula)> {
        let mut shapes: Vec<(String, Vec<(RLin, bool)>, Formula)> = Vec::new();
        for (seed, width, k) in [
            (0x5EED_0000_0000_0010u64, 32usize, 5usize),
            (0x5EED_0000_0000_0011, 16, 6),
            (0x5EED_0000_0000_0012, 32, 3),
            (0x5EED_0000_0000_0013, 32, 8),
        ] {
            let rows = refuter_pool(seed, 32, width, 64, k);
            let what = format!("refuter 32 vars/{width} per row x64 core={k}");
            shapes.push((what, rlin_rrows(&rows), rformula(&rows)));
        }
        let rows = seeded_dense_pool(0x5EED_0000_0000_0001 ^ 32 << 8, 32, 64, 5);
        shapes.push(("dense 32x64 core=5".into(), rlin_rows(&rows), formula(&rows)));
        for nvars in [64usize, 200] {
            let rows = refuter_pool(0x5EED_0000_0000_0020 ^ nvars as u64, nvars, 32, 64, 5);
            let what = format!("refuter wide {nvars} vars/32 per row x64");
            shapes.push((what, rlin_rrows(&rows), rformula(&rows)));
        }
        shapes
    }

    /// (WORK BUDGET, PINNED) Every widest admitted pool DECLINES on the work
    /// meter: the metered call returns `None` with the meter exhausted, having
    /// overshot [`SIMPLEX_WORK_BUDGET`] by less than one budget (the overshoot
    /// is one pivot's charge), Fourier–Motzkin declines behind it, and the
    /// lane search has no witness — except on the 200-variable pool, which is
    /// sparse (32 of 200 variables per row) and which greedy FM then
    /// certifies. The bound is the deterministic counter, never a clock; the
    /// timings are printed. For the first pool
    /// `certify_violation` runs end to end and returns `None` without an
    /// abort — the decline that used to cost 137–671 s of simplex plus 36–79
    /// s of replay (every 32-variable support declines at the replay's
    /// `NODE_BUDGET` anyway) now costs the simplex about a second, and no ay
    /// solve precedes the search (the retired pre-solve cost ~42 s here).
    #[test]
    fn simplex_work_budget_declines_the_widest_admitted_pools() {
        for (i, (what, lin, violation)) in widest_admitted_pools().iter().enumerate() {
            let t0 = std::time::Instant::now();
            let (witness, work) = simplex_farkas_metered(lin);
            let st = t0.elapsed();
            assert!(witness.is_none(), "{what}: expected a budget decline");
            assert!(work.exhausted(), "{what}: declined but the meter is not exhausted");
            assert!(
                work.spent < 2 * SIMPLEX_WORK_BUDGET,
                "{what}: overshoot past one budget: {}",
                work.spent
            );
            let t0 = std::time::Instant::now();
            let fallback = find_farkas_multipliers_real(lin);
            let lt = t0.elapsed();
            let live: BTreeSet<&str> =
                lin.iter().flat_map(|(r, _)| r.terms.keys().map(String::as_str)).collect();
            if live.len() <= 64 {
                // Dense pools: Fourier–Motzkin declines behind the simplex too.
                assert!(fallback.is_none(), "{what}: FM must decline on a dense pool");
            } else {
                // The 200-variable pool is SPARSE (32 of 200 per row): greedy
                // FM finds the witness the simplex was not allowed to.
                assert!(fallback.is_some(), "{what}: greedy FM finds the sparse witness");
            }
            eprintln!(
                "[simplex-budget] {what}: rows={} declined at work={} (budget {SIMPLEX_WORK_BUDGET}) \
                 simplex={st:?} lane-search={} ({lt:?})",
                lin.len(),
                work.spent,
                fallback.is_some()
            );
            if i == 0 {
                let t0 = std::time::Instant::now();
                assert!(certify_violation(violation).is_none(), "{what}: must decline end to end");
                eprintln!("[simplex-budget] {what}: end-to-end decline in {:?}", t0.elapsed());
            }
        }
    }

    /// (MEASUREMENT) The work meter on the reference shapes, on dense pools
    /// between them and the admitted extreme, and on the widest admitted pools
    /// under an UNBOUNDED meter (what they would cost without the budget).
    /// Numbers are printed; the budget-relative claims of
    /// [`SIMPLEX_WORK_BUDGET`]'s doc are read off this output.
    #[test]
    #[ignore = "measurement instrument: prints the simplex work meter, including UNBOUNDED-budget \
                solves over dense pools, and asserts nothing; run with --ignored --nocapture"]
    fn simplex_work_measurements() {
        for (what, violation) in &reference_shapes() {
            let rows = lane_rows(violation);
            let t0 = std::time::Instant::now();
            let (w, work) = simplex_farkas_metered(&rows);
            let support = w.as_ref().map(|(m, _)| m.iter().filter(|x| q_is_pos(x)).count());
            eprintln!(
                "[simplex-work] {what}: rows={} support={support:?} work={} ({:.1}% of budget) in {:?}",
                rows.len(),
                work.spent,
                100.0 * work.spent as f64 / SIMPLEX_WORK_BUDGET as f64,
                t0.elapsed()
            );
        }
        let mut pools: Vec<(String, Vec<(RLin, bool)>)> = Vec::new();
        for (nv, nrows, k) in
            [(14usize, 24usize, 5usize), (16, 30, 4), (20, 40, 4), (25, 60, 4), (28, 64, 5)]
        {
            let rows = seeded_dense_pool(0x5EED_0000_0000_0001 ^ (nv as u64) << 8, nv, nrows, k);
            pools.push((format!("dense {nv}x{nrows} core={k}"), rlin_rows(&rows)));
        }
        // The 200-variable pool is left out here: its unbounded solve alone is
        // 25 s (1.1G work, measured once) — the decline test covers it.
        pools.extend(
            widest_admitted_pools()
                .into_iter()
                .map(|(w, lin, _)| (w, lin))
                .filter(|(w, _)| !w.contains("200")),
        );
        for (what, lin) in &pools {
            let mut work = SimplexWork::with_budget(u64::MAX);
            let t0 = std::time::Instant::now();
            let cand = simplex_farkas_candidate(lin, &mut work);
            let ct = t0.elapsed();
            let cand_work = work.spent;
            let Some((mult, pivots, feasible)) = cand else {
                eprintln!(
                    "[simplex-work] {what} (unbounded meter): rows={} phase-1 hit the PIVOT CAP \
                     after work={cand_work} ({ct:?})",
                    lin.len()
                );
                continue;
            };
            let mut reduced = String::new();
            if lin.len() < 64 {
                let mut work = SimplexWork::with_budget(u64::MAX);
                let t0 = std::time::Instant::now();
                let full = simplex_farkas_on(lin, &mut work).witness();
                let support = full.as_ref().map(|(m, _)| m.iter().filter(|x| q_is_pos(x)).count());
                reduced = format!(
                    "; with reduction: support={support:?} work={} ({:?})",
                    work.spent,
                    t0.elapsed()
                );
            }
            let support = mult.iter().filter(|x| q_is_pos(x)).count();
            eprintln!(
                "[simplex-work] {what} (unbounded meter): rows={} phase-1 feasible={feasible} \
                 pivots={pivots} support={support} work={cand_work} ({ct:?}){reduced}; budget \
                 {SIMPLEX_WORK_BUDGET}",
                lin.len()
            );
        }
    }

    /// (PREVIOUSLY DECLINING) The dense 12-variable contradiction whose witness
    /// needs four rows: the cheap witnesses have nothing (no closed row, no
    /// proportional pair, no single-variable row), Fourier–Motzkin alone
    /// blows past `ROW_CAP` on the second elimination and returns `None`
    /// (measured here), and the simplex finds a verified witness — the lane
    /// certifies it end to end.
    #[test]
    fn fm_declines_but_simplex_certifies_a_dense_four_row_contradiction() {
        let rows = dense_four_row_system();
        assert_eq!(rows.len(), 40);
        let lin = rlin_rows(&rows);
        assert!(cheap_farkas_witness(&lin).is_none(), "no cheap witness by construction");
        let t0 = std::time::Instant::now();
        assert!(fourier_motzkin(&lin).is_none(), "FM alone must exceed ROW_CAP on this shape");
        let fm = t0.elapsed();
        let t0 = std::time::Instant::now();
        let (mult, strict) = simplex_farkas(&lin).expect("the simplex finds the witness");
        let simplex = t0.elapsed();
        assert!(!strict);
        assert_eq!(verify_farkas_witness(&lin, &mult), Some(false));
        let positive = mult.iter().filter(|m| q_is_pos(m)).count();
        assert!(positive >= 4, "the contradiction needs at least the four core rows: {positive}");
        eprintln!(
            "[simplex] dense 4-row/12-var/40 rows: FM declined in {fm:?}, simplex witness in \
             {simplex:?} ({positive} positive multipliers)"
        );
        let violation = formula(&rows);
        let t0 = std::time::Instant::now();
        let (bytes, expr) = certified(&violation, "dense four-row contradiction");
        eprintln!(
            "[simplex] dense 4-row end to end: bytes={} codec_nodes={} certify+recheck={:?}",
            bytes.len(),
            expr_nodes(&expr),
            t0.elapsed()
        );
    }

    /// (PREVIOUSLY DECLINING, RANDOMIZED) Seeded dense INFEASIBLE-by-construction
    /// systems over 8–20 variables: a 3–5-row core whose positive combination is
    /// `0·x − 1` (or `0·x + 0` with a strict core row — the Motzkin case),
    /// shuffled among 4–8 dense satisfiable noise rows. Every one certifies end
    /// to end (kernel-checked, codec round-tripped, ay cross-checked, rechecked).
    #[test]
    fn seeded_dense_infeasible_systems_certify() {
        let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
        let mut through_simplex = 0usize;
        let mut total = 0usize;
        for nv in [8usize, 10, 12, 14, 16, 18, 20] {
            for rep in 0..2 {
                let vars = names(nv);
                let k = rng.range(3, 5) as usize;
                let motzkin = rng.coin();
                let mut rows = infeasible_core(&mut rng, &vars, k, motzkin);
                let p: Vec<i64> = (0..nv).map(|_| rng.range(-2, 2)).collect();
                for _ in 0..rng.range(4, 8) {
                    let strict = rng.coin();
                    rows.push(true_row(&mut rng, &vars, &p, strict));
                }
                rng.shuffle(&mut rows);
                let lin = rlin_rows(&rows);
                let cheap = cheap_farkas_witness(&lin).is_some();
                let (mult, pivots, feasible) =
                    simplex_farkas_candidate(&lin, &mut SimplexWork::fresh())
                        .expect("inside the caps");
                assert!(feasible, "nv={nv} rep={rep}: the dual LP is feasible by construction");
                let (_, work) = simplex_farkas_metered(&lin);
                assert!(
                    work.spent * 10 <= SIMPLEX_WORK_BUDGET,
                    "nv={nv} rep={rep}: spends {} — not well under the budget",
                    work.spent
                );
                let strict = verify_farkas_witness(&lin, &mult)
                    .unwrap_or_else(|| panic!("nv={nv} rep={rep}: witness must verify"));
                // The residual is strict exactly when a strict row is weighted
                // (a Motzkin core may still be refuted through a negative
                // residual that avoids its strict row — also a valid witness).
                assert_eq!(
                    strict,
                    rows.iter().enumerate().any(|(i, r)| r.strict && q_is_pos(&mult[i]))
                );
                let t0 = std::time::Instant::now();
                let (bytes, _) = certified(&formula(&rows), &format!("nv={nv} rep={rep}"));
                eprintln!(
                    "[simplex] seeded infeasible nv={nv} rows={} core={k} motzkin={motzkin} \
                     cheap={cheap} pivots={pivots} work={} bytes={} certify+recheck={:?}",
                    rows.len(),
                    work.spent,
                    bytes.len(),
                    t0.elapsed()
                );
                total += 1;
                through_simplex += usize::from(!cheap);
            }
        }
        assert!(through_simplex * 2 >= total, "most seeded systems must exercise the simplex");
    }

    /// (SOUNDNESS, RANDOMIZED) 500 seeded SATISFIABLE-by-construction systems
    /// over 8–20 variables (every row true at a random integer point, strict
    /// rows with slack): the Phase-1 optimum stays positive on every one, the
    /// verifier REJECTS the last basic point the simplex ends on, the simplex
    /// returns no witness, and the lane certifies nothing.
    #[test]
    fn seeded_satisfiable_systems_never_certify() {
        let mut rng = Rng(0xD1B5_4A32_D192_ED03);
        let mut minted = Vec::new();
        for case in 0..500 {
            let nv = rng.range(8, 20) as usize;
            let vars = names(nv);
            let p: Vec<i64> = (0..nv).map(|_| rng.range(-3, 3)).collect();
            let nrows = rng.range(6, 14) as usize;
            let rows: Vec<Row> = (0..nrows)
                .map(|_| {
                    let strict = rng.coin();
                    true_row(&mut rng, &vars, &p, strict)
                })
                .collect();
            let lin = rlin_rows(&rows);
            let (mult, _, feasible) =
                simplex_farkas_candidate(&lin, &mut SimplexWork::fresh()).expect("inside the caps");
            assert!(!feasible, "case {case}: the dual LP of a satisfiable system is infeasible");
            assert_eq!(
                verify_farkas_witness(&lin, &mult),
                None,
                "case {case}: the verifier must reject the final basic point"
            );
            assert!(simplex_farkas(&lin).is_none(), "case {case}: no witness");
            let violation = formula(&rows);
            if certify_violation(&violation).is_some() {
                minted.push((case, violation));
            }
        }
        assert!(minted.is_empty(), "FALSE CERTIFICATES on satisfiable systems: {minted:#?}");
    }

    /// (DETERMINISM) The dense four-row system goes through the simplex (no
    /// cheap witness): two UNCACHED producer runs yield identical bytes, and
    /// the search itself returns identical multipliers on repeated calls.
    #[test]
    fn simplex_certificates_are_byte_deterministic() {
        let rows = dense_four_row_system();
        let lin = rlin_rows(&rows);
        assert!(cheap_farkas_witness(&lin).is_none());
        let w1 = simplex_farkas(&lin).expect("witness");
        let w2 = simplex_farkas(&lin).expect("witness");
        assert_eq!(w1, w2, "the multipliers are a function of the row list");
        let violation = formula(&rows);
        let identity = ObligationIdentity::from_violation(&violation).expect("identity");
        let a = certify_lanes(&violation, &identity).expect("certifies");
        let b2 = certify_lanes(&violation, &identity).expect("certifies");
        assert_eq!(a, b2, "certificate bytes must be deterministic across uncached runs");
        let (term, _) = certified(&violation, "memoized");
        assert!(
            matches!(&a, ProofEvidence::CleanCic { term: t, .. } if *t == term),
            "the memoized payload is the uncached payload"
        );
    }

    /// (STRICT ROWS, MOTZKIN) Called DIRECTLY — bypassing the cheap witnesses —
    /// the simplex finds the strict-row shapes: `x ≥ 1 ∧ x < 1`, `x < y ∧ y <
    /// x`, the crown `y ≤ 2x ∧ x ≤ 1/2 ∧ y > 1`, and `2x < 2 ∧ 3x ≥ 3` (a strict
    /// row with a non-unit multiplier); each witness verifies with a STRICT
    /// residual, and each weak twin (`<` relaxed to `≤`) is refused.
    #[test]
    fn simplex_finds_strict_row_witnesses_by_motzkin() {
        let r = |terms: &[(&str, i64)], c: i64, strict: bool| Row {
            terms: terms.iter().map(|(x, a)| (x.to_string(), *a)).collect(),
            c,
            strict,
        };
        // Rows are `0 ⋈ Σ a x + c`: x ≥ 1 is `0 ≤ x − 1`, x < 1 is `0 < 1 − x`.
        let shapes: Vec<(&str, Vec<Row>)> = vec![
            ("x ≥ 1 ∧ x < 1", vec![r(&[("x", 1)], -1, false), r(&[("x", -1)], 1, true)]),
            (
                "x < y ∧ y < x",
                vec![r(&[("x", -1), ("y", 1)], 0, true), r(&[("x", 1), ("y", -1)], 0, true)],
            ),
            (
                "crown",
                vec![
                    r(&[("x", 2), ("y", -1)], 0, false),
                    r(&[("x", -2)], 1, false), // 2x ≤ 1, the integer spelling of x ≤ 1/2
                    r(&[("y", 1)], -1, true),
                ],
            ),
            ("2x < 2 ∧ 3x ≥ 3", vec![r(&[("x", -2)], 2, true), r(&[("x", 3)], -3, false)]),
        ];
        for (what, rows) in shapes {
            let lin = rlin_rows(&rows);
            let (mult, strict) = simplex_farkas(&lin).unwrap_or_else(|| panic!("{what}: witness"));
            assert!(strict, "{what}: the residual is strict");
            assert_eq!(verify_farkas_witness(&lin, &mult), Some(true), "{what}");
            let weak: Vec<Row> = rows.iter().map(|r| Row { strict: false, ..r.clone() }).collect();
            assert!(simplex_farkas(&rlin_rows(&weak)).is_none(), "{what}: the weak twin is SAT");
        }
        // Mixed: a negative residual with a strict row weighted is still reported strict.
        let both = vec![r(&[("x", 1)], -2, true), r(&[("x", -1)], 1, false)];
        let lin = rlin_rows(&both);
        let (_, strict) = simplex_farkas(&lin).expect("x > 2 ∧ x ≤ 1");
        assert!(strict);
    }

    /// (CAPS) A pivot cap of zero declines a system that needs a pivot (`None`,
    /// not a wrong answer), and a pool whose surviving variables would need a
    /// tableau past [`SIMPLEX_CELL_BUDGET`] (40 rows × 32 variables, every
    /// variable in exactly two rows so presolve keeps all of it) declines
    /// before allocating. Presolve drops a row whose variable appears nowhere
    /// else, so a system that is all such rows never reaches the tableau.
    #[test]
    fn simplex_declines_cleanly_past_its_caps() {
        let rows = dense_four_row_system();
        let lin = rlin_rows(&rows);
        let (_, pivots, feasible) =
            simplex_farkas_candidate(&lin, &mut SimplexWork::fresh()).expect("in budget");
        assert!(feasible && pivots > 0);
        // Rebuild the same LP by hand with the cap at zero.
        let e = vec![vec![q_from_int(1), q_from_int(1)]];
        let bb = vec![q_from_int(1)];
        assert!(
            phase1_simplex(&e, &bb, 0, &mut SimplexWork::fresh()).is_none(),
            "one pivot is needed; the cap is zero"
        );
        assert!(matches!(
            phase1_simplex(&e, &bb, 1, &mut SimplexWork::fresh()),
            Some((_, 1, true))
        ));

        let wide: Vec<Row> = (0..40)
            .map(|i| Row {
                terms: (0..32).map(|j| (format!("w{:03}", (16 * i + j) % 640), 1)).collect(),
                c: -1,
                strict: false,
            })
            .collect();
        let lin = rlin_rows(&wide);
        assert!(
            simplex_farkas_candidate(&lin, &mut SimplexWork::fresh()).is_none(),
            "640 surviving variables: over budget"
        );

        let lonely: Vec<Row> = (0..5)
            .map(|i| Row {
                terms: vec![(format!("l{i}"), 1), ("shared".to_string(), 1)],
                c: -1,
                strict: false,
            })
            .collect();
        assert!(
            simplex_farkas_candidate(&rlin_rows(&lonely), &mut SimplexWork::fresh()).is_none(),
            "presolve empties it"
        );
    }

    /// (MEASUREMENT) Timings and pivot counts on the lane's reference shapes:
    /// the four `mip-46963` systems, the crown, the box systems n = 10..30,
    /// the 12-variable noise case, and the dense four-row contradiction. The
    /// search is timed on the lane's own rows; the end-to-end figure is
    /// `certify_violation` plus the recheck. Numbers are printed, not asserted.
    #[test]
    fn simplex_measurements() {
        for (what, violation) in &reference_shapes() {
            let rows = lane_rows(violation);
            let t0 = std::time::Instant::now();
            let cheap = cheap_farkas_witness(&rows).is_some();
            let cheap_t = t0.elapsed();
            let t0 = std::time::Instant::now();
            let simplex = simplex_farkas_candidate(&rows, &mut SimplexWork::fresh());
            let simplex_t = t0.elapsed();
            let pivots = simplex.as_ref().map(|(_, p, _)| *p);
            let found = simplex
                .as_ref()
                .is_some_and(|(m, _, f)| *f && verify_farkas_witness(&rows, m).is_some());
            let work = simplex_farkas_metered(&rows).1.spent;
            assert!(
                work * 10 <= SIMPLEX_WORK_BUDGET,
                "{what}: spends {work} — not well under the budget"
            );
            let t0 = std::time::Instant::now();
            let search = find_farkas_multipliers_real(&rows).is_some();
            let search_t = t0.elapsed();
            let t0 = std::time::Instant::now();
            let (bytes, _) = certified(violation, what);
            let end_to_end = t0.elapsed();
            eprintln!(
                "[simplex-measure] {what}: rows={} cheap={cheap} ({cheap_t:?}) simplex={found} \
                 pivots={pivots:?} work={work} ({simplex_t:?}) lane-search={search} ({search_t:?}) \
                 bytes={} certify+recheck={end_to_end:?}",
                rows.len(),
                bytes.len()
            );
            assert!(search && found);
        }
    }
}

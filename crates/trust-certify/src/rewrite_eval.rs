// Trust (D5-B follow-up, 2026-09-25): the KERNEL-CHECKED REWRITING lane.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Refute a violation by EQUALITY REWRITING and PROPOSITIONAL EVALUATION, with
//! every rewrite justified inside the CIC term the kernel re-checks.
//!
//! # Why this lane exists (measured 2026-09-25)
//!
//! The compiler mints D5-B's body-inferred return equalities from the crate-wide
//! extraction, which reads PRE-optimization MIR. There `fn guard(bit: u32) ->
//! bool { bit < 64 }` is `_2 = copy _1; _0 = Lt(move _2, const 64)`, so the
//! check VC's violation is
//!
//! ```text
//! _2 = bit  ∧  (_0 ⟺ _2 < 64)  ∧  ¬(_0 ⟺ bit < 64)
//! ```
//!
//! and no earlier lane refutes it: the propositional closure lane needs the
//! negated leaf `_0 ⟺ bit < 64` present VERBATIM, and the linear-Int lanes drop
//! every `Bool`-sorted conjunct. The optimized twin (copy propagated) is
//! certified, which is why the D5-B realmir tests — built from optimized dumps —
//! never saw it. The same temporaries, plus Boolean definitions (`_3 ⟺ a`,
//! `_2 ⟺ b < 64`) and the implication pair a diamond's `Ite` elimination emits,
//! are what kept every branchy helper uncertified.
//!
//! # What the lane does
//!
//! 1. **Hypotheses** are the violation's OWN top-level conjuncts — flattened
//!    through `And` only, `Bool(true)` dropped — each translated by [`enc_prop`].
//!    No [`super::NORMALIZATION_STEPS`] derivation is read: nothing in the
//!    context is a trusted consequence of another conjunct. A conjunct outside
//!    the encodable fragment is DROPPED (a weakening: a satisfiable violation
//!    stays satisfiable).
//! 2. **Int rewriting.** Every conjunct `a = b` between two `Int` variables or a
//!    variable and a literal joins an equivalence class. Each class gets a
//!    representative (its literal if it has one, else its least variable name),
//!    and every other conjunct is rewritten to representatives by
//!    `Eq.subst (motive := λz. P[x := z]) (h : x = rep) (p : P[x])`, where `h`
//!    is an `Eq.trans`/`Eq.symm` chain of the class's own conjunct hypotheses. A
//!    class holding two distinct literals is itself the refutation.
//! 3. **Bool definitions.** A conjunct `v ⟺ φ` (a `Bool` variable against a
//!    formula not mentioning it, acyclic over the chosen set) defines `v`; every
//!    other conjunct is rewritten by `Eq.subst (motive := λP. Q[v := P])
//!    (propext h) (q : Q[v])`.
//! 4. **Evaluation.** Over the rewritten facts (split through `And`, extended by
//!    bounded forward chaining through `→` and `⟺`), a three-valued evaluator
//!    decides subformulas from the facts, from syntactic reflexivity
//!    (`Eq.refl`, `Iff.intro id id`) and from closed integer arithmetic
//!    (`Int.NonNeg.mk` witnesses, [`super::refute_false_eq`],
//!    [`super::refute_false_atom`]), building an intuitionistic proof term for
//!    every verdict. A fact that evaluates to FALSE closes the refutation.
//! 5. **Restart and split.** A fact chaining derives that the rewriting would
//!    have used (an `Int` alias such as `_3 = d`, a Bool definition) restarts the
//!    pass with it as one more fact; a pass that stalls on an implication with an
//!    undecided antecedent case-splits on that atom (`Or.rec` over
//!    `Classical.em A`, each branch refuted with `A` / `¬A` as a lambda-bound
//!    fact), bounded in depth and pool size. This is the caller side of a
//!    diamond helper's lemma (`x / nz(d)`).
//! 6. [`super::finish_certificate`] as for every Int lane: ay's independent
//!    UNSAT (required), the full kernel `check_type(term, False)` with the
//!    axiom-closure audit, and the serialized round-trip re-check.
//!
//! # Soundness — what is trusted, and what the kernel checks
//!
//! The KERNEL checks every rewrite (each `Eq.subst` must type against the exact
//! motive, the equality chain must type, `propext` must receive a real `Iff`
//! proof), every propositional step and every closed arithmetic fact. A bug in
//! the class computation, the definition selection or the evaluator produces a
//! term that does not type-check, and the lane returns `None`.
//!
//! TRUSTED is exactly the TRANSLATION of each kept conjunct, [`enc_prop`] /
//! [`smt_prop`] (the ay rendering is defence in depth only). It is compositional
//! and faithful on its fragment: `Int` terms as the other Int lanes encode them
//! (variables are `Int`-typed skolems, literals `Int.ofNat`/`Int.negSucc`, `+`
//! and literal `*` as `HAdd`/`HMul`); `=`/`<`/`≤`/`>`/`≥` over `Int` as `Eq`/
//! `LT.lt`/`LE.le` (flipped for `>`/`≥`); `¬ ∧ ∨ →` as `Not And Or` and the
//! arrow; `=` between two `Bool` formulas as `Iff`. The ONE abstraction is a
//! `Bool` variable `v`, encoded as the proposition `v = 1` over a fresh
//! `Int`-typed skolem `v`: for any model `M` of the violation, sending each
//! `Int` variable to `M(x)` and each `Bool` variable to `1` if `M(v)` else `0`
//! satisfies every encoded conjunct (induction on the conjunct), so a kernel
//! proof of `False` from them proves the violation unsatisfiable. That model
//! transfer needs the variable → skolem map to be INJECTIVE, which the lane
//! enforces: a name used at two sorts, or two names with one encoded spelling,
//! declines the whole lane. The axiom closure is the audited one — the `Int`
//! skolems plus the foundational residue, of which this lane uses `propext` (Bool
//! definitions) and, through `Classical.em`, `Classical.choice` (case splits).
//!
//! # Position
//!
//! Called LAST by the producer, after every other lane declined, so no
//! certificate the producer already minted changes shape or bytes; the consumer
//! re-check regenerates through the same producer, so producer and re-checker
//! stay single-sourced. Everything here is deterministic (ordered maps, no hash
//! iteration).

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, FVarId, Level};
use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{Formula, Sort};

use super::{
    ClosedOrderAtom, Hyp, ObligationIdentity, const_app, encoded_var_name, eq_int, eq_refl_int,
    eq_subst_int, eq_symm_int, eq_trans_int, false_expr, finish_certificate, hadd_int, hmul_int,
    int_literal_to_kernel, int_literal_to_smt, int_literal_value, int_ty, le_int,
    linear_mul_operands, lt_int, nonneg_gap_u128, nonneg_mk_u128, not_prop, push_hyp,
    refute_false_atom, refute_false_eq,
};

// COST. The lane runs on every violation every other lane declined, so its
// work is bounded up front and a pool past any cap is declined before any
// rewriting: total nodes of the violation, top-level conjuncts, nodes of one
// fact while Bool definitions expand it, substitution steps per fact, and the
// total nodes of all rewritten facts (which bounds the evaluator: every
// evaluation is linear in its formula times the recursion depth, and each round
// evaluates each fact a bounded number of times).

/// A violation with more top-level conjuncts than this is declined.
const MAX_POOL: usize = 256;
/// A violation with more formula nodes than this is declined.
const MAX_VIOLATION_NODES: usize = 8_192;
/// A Bool-definition rewrite stops expanding a fact past this many nodes, and a
/// rewritten fact still past it is dropped from the evaluation.
const MAX_FACT_NODES: usize = 1_024;
/// Cap on Bool-definition substitutions applied to one fact.
const MAX_BOOL_STEPS: usize = 32;
/// The rewritten facts together may not exceed this many nodes.
const MAX_TOTAL_FACT_NODES: usize = 16_384;
/// Forward-chaining rounds.
const MAX_ROUNDS: usize = 4;
/// Re-runs of the rewriting after chaining derived a new equality.
const MAX_RESTARTS: usize = 4;
/// Case-split depth (`Classical.em`), so at most `2^MAX_SPLITS` branches.
const MAX_SPLITS: usize = 2;
/// Case splits are tried only when the saturated facts are this small.
const MAX_SPLIT_NODES: usize = 2_048;
/// Cap on facts (after splitting and chaining).
const MAX_FACTS: usize = 2_048;
/// Evaluator recursion bound.
const MAX_EVAL_DEPTH: usize = 64;
/// Local fvars (lambda binders, motive holes) are numbered from here, far above
/// the context hypotheses (`HYP_FVAR_BASE + i`). Every one is abstracted away
/// before the term is returned, so none reaches the certificate.
const LOCAL_FVAR_BASE: u64 = 1 << 40;

mod paths;

pub(super) fn certify_rewrite_path_disjunction(
    violation: &Formula,
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    paths::certify(violation, identity)
}

// ---------------------------------------------------------------------------
// The translation (TRUSTED).
// ---------------------------------------------------------------------------

/// A substitution hole: at the named leaf of the given sort, emit `expr`
/// instead of the leaf's own encoding. Used only to build rewrite MOTIVES.
#[derive(Clone, Copy)]
enum Hole<'a> {
    None,
    /// `Int` variable leaf `name` ↦ `expr : Int`.
    Int(&'a str, &'a Expr),
    /// `Bool` variable leaf `name` ↦ `expr : Prop` (replacing `name = 1`).
    Bool(&'a str, &'a Expr),
}

/// A variable leaf (`Var` or its interned twin `SymVar`, semantically identical).
fn leaf(f: &Formula) -> Option<(&str, &Sort)> {
    match f {
        Formula::Var(name, sort) => Some((name.as_str(), sort)),
        Formula::SymVar(sym, sort) => Some((sym.as_str(), sort)),
        _ => None,
    }
}

/// Syntactically `Bool`-valued (a connective, a comparison, a `Bool` literal or
/// a `Bool` variable). Decides whether an `Eq` is `Iff` or an `Int` equality.
fn is_bool_valued(f: &Formula) -> bool {
    matches!(
        f,
        Formula::Bool(_)
            | Formula::Not(_)
            | Formula::And(_)
            | Formula::Or(_)
            | Formula::Implies(..)
            | Formula::Eq(..)
            | Formula::Lt(..)
            | Formula::Le(..)
            | Formula::Gt(..)
            | Formula::Ge(..)
    ) || matches!(leaf(f), Some((_, Sort::Bool)))
}

fn skolem(name: &str) -> Expr {
    Expr::const_(Name::from_string(&encoded_var_name(name)), vec![])
}

fn true_expr() -> Expr {
    static TRUE: std::sync::OnceLock<Expr> = std::sync::OnceLock::new();
    TRUE.get_or_init(|| Expr::const_(Name::from_string("True"), vec![])).clone()
}

/// The proposition a `Bool` variable `v` stands for: `v = 1` over its `Int`
/// skolem (see the module doc for the model transfer).
fn bool_var_prop(name: &str) -> Option<Expr> {
    Some(eq_int(skolem(name), int_literal_to_kernel(1)?))
}

/// `Int` term encoding (the Int lanes' own spelling).
fn enc_term(f: &Formula, hole: Hole<'_>) -> Option<Expr> {
    if let Some((name, sort)) = leaf(f) {
        if *sort != Sort::Int {
            return None;
        }
        if let Hole::Int(h, e) = hole
            && h == name
        {
            return Some(e.clone());
        }
        return Some(skolem(name));
    }
    if let Some(n) = int_literal_value(f) {
        return int_literal_to_kernel(n);
    }
    match f {
        Formula::Add(a, b) => Some(hadd_int(enc_term(a, hole)?, enc_term(b, hole)?)),
        Formula::Mul(a, b) => {
            let (k, t) = linear_mul_operands(a, b)?;
            Some(hmul_int(enc_term(t, hole)?, int_literal_to_kernel(k)?))
        }
        _ => None,
    }
}

fn smt_term(f: &Formula) -> Option<String> {
    if let Some((name, sort)) = leaf(f) {
        return (*sort == Sort::Int).then(|| encoded_var_name(name));
    }
    if let Some(n) = int_literal_value(f) {
        return int_literal_to_smt(n);
    }
    match f {
        Formula::Add(a, b) => Some(format!("(+ {} {})", smt_term(a)?, smt_term(b)?)),
        Formula::Mul(a, b) => {
            let (k, t) = linear_mul_operands(a, b)?;
            Some(format!("(* {} {})", smt_term(t)?, int_literal_to_smt(k)?))
        }
        _ => None,
    }
}

/// Right-nested `And`/`Or` of `props` (`unit` for none, the prop itself for one).
fn nest(connective: &'static str, unit: Expr, props: &[Expr]) -> Expr {
    match props {
        [] => unit,
        [only] => only.clone(),
        [head, rest @ ..] => {
            const_app(connective, [head.clone(), nest(connective, unit.clone(), rest)])
        }
    }
}

/// The CIC proposition for a `Bool`-sorted formula (see the module doc).
fn enc_prop(f: &Formula, hole: Hole<'_>) -> Option<Expr> {
    if let Some((name, sort)) = leaf(f) {
        if *sort != Sort::Bool {
            return None;
        }
        if let Hole::Bool(h, e) = hole
            && h == name
        {
            return Some(e.clone());
        }
        return bool_var_prop(name);
    }
    let both = |a: &Formula, b: &Formula| Some((enc_term(a, hole)?, enc_term(b, hole)?));
    match f {
        Formula::Bool(true) => Some(true_expr()),
        Formula::Bool(false) => Some(false_expr()),
        Formula::Not(a) => Some(not_prop(enc_prop(a, hole)?)),
        Formula::And(gs) => {
            let props = gs.iter().map(|g| enc_prop(g, hole)).collect::<Option<Vec<_>>>()?;
            Some(nest("And", true_expr(), &props))
        }
        Formula::Or(gs) => {
            let props = gs.iter().map(|g| enc_prop(g, hole)).collect::<Option<Vec<_>>>()?;
            Some(nest("Or", false_expr(), &props))
        }
        Formula::Implies(a, b) => Some(Expr::arrow(enc_prop(a, hole)?, enc_prop(b, hole)?)),
        Formula::Eq(a, b) if is_bool_valued(a) && is_bool_valued(b) => {
            Some(const_app("Iff", [enc_prop(a, hole)?, enc_prop(b, hole)?]))
        }
        Formula::Eq(a, b) => both(a, b).map(|(x, y)| eq_int(x, y)),
        Formula::Lt(a, b) => both(a, b).map(|(x, y)| lt_int(x, y)),
        Formula::Le(a, b) => both(a, b).map(|(x, y)| le_int(x, y)),
        Formula::Gt(a, b) => both(a, b).map(|(x, y)| lt_int(y, x)),
        Formula::Ge(a, b) => both(a, b).map(|(x, y)| le_int(y, x)),
        _ => None,
    }
}

/// SMT-LIB rendering, mirroring [`enc_prop`] (for the ay cross-check only).
fn smt_prop(f: &Formula) -> Option<String> {
    if let Some((name, sort)) = leaf(f) {
        return (*sort == Sort::Bool).then(|| format!("(= {} 1)", encoded_var_name(name)));
    }
    let nary = |op: &str, unit: &str, gs: &[Formula]| -> Option<String> {
        let parts = gs.iter().map(smt_prop).collect::<Option<Vec<_>>>()?;
        Some(match parts.len() {
            0 => unit.to_string(),
            1 => parts.into_iter().next()?,
            _ => format!("({op} {})", parts.join(" ")),
        })
    };
    let bin = |op: &str, a: &Formula, b: &Formula| {
        Some(format!("({op} {} {})", smt_term(a)?, smt_term(b)?))
    };
    match f {
        Formula::Bool(true) => Some("true".into()),
        Formula::Bool(false) => Some("false".into()),
        Formula::Not(a) => Some(format!("(not {})", smt_prop(a)?)),
        Formula::And(gs) => nary("and", "true", gs),
        Formula::Or(gs) => nary("or", "false", gs),
        Formula::Implies(a, b) => Some(format!("(=> {} {})", smt_prop(a)?, smt_prop(b)?)),
        Formula::Eq(a, b) if is_bool_valued(a) && is_bool_valued(b) => {
            Some(format!("(= {} {})", smt_prop(a)?, smt_prop(b)?))
        }
        Formula::Eq(a, b) => bin("=", a, b),
        Formula::Lt(a, b) => bin("<", a, b),
        Formula::Le(a, b) => bin("<=", a, b),
        Formula::Gt(a, b) => bin("<", b, a),
        Formula::Ge(a, b) => bin("<=", b, a),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Fragment-preserving formula maps (only ever applied to encodable formulas).
// ---------------------------------------------------------------------------

fn map_leaves_opt(f: &Formula, sub: &dyn Fn(&Formula) -> Option<Formula>) -> Option<Formula> {
    if let Some(replacement) = sub(f) {
        return Some(replacement);
    }
    let fold_children = |gs: &[Formula], wrap: fn(Vec<Formula>) -> Formula| -> Option<Formula> {
        let mut out: Option<Vec<Formula>> = None;
        for (i, g) in gs.iter().enumerate() {
            if let Some(mapped) = map_leaves_opt(g, sub) {
                let vec = out.get_or_insert_with(|| {
                    let mut v = Vec::with_capacity(gs.len());
                    v.extend_from_slice(&gs[..i]);
                    v
                });
                vec.push(mapped);
            } else if let Some(vec) = &mut out {
                vec.push(g.clone());
            }
        }
        out.map(wrap)
    };
    let fold_bin = |a: &Formula, b: &Formula, wrap: fn(Box<Formula>, Box<Formula>) -> Formula| {
        match (map_leaves_opt(a, sub), map_leaves_opt(b, sub)) {
            (None, None) => None,
            (ma, mb) => Some(wrap(
                Box::new(ma.unwrap_or_else(|| a.clone())),
                Box::new(mb.unwrap_or_else(|| b.clone())),
            )),
        }
    };
    match f {
        Formula::Not(a) => map_leaves_opt(a, sub).map(|ma| Formula::Not(Box::new(ma))),
        Formula::And(gs) => fold_children(gs, Formula::And),
        Formula::Or(gs) => fold_children(gs, Formula::Or),
        Formula::Implies(a, b) => fold_bin(a, b, Formula::Implies),
        Formula::Eq(a, b) => fold_bin(a, b, Formula::Eq),
        Formula::Lt(a, b) => fold_bin(a, b, Formula::Lt),
        Formula::Le(a, b) => fold_bin(a, b, Formula::Le),
        Formula::Gt(a, b) => fold_bin(a, b, Formula::Gt),
        Formula::Ge(a, b) => fold_bin(a, b, Formula::Ge),
        Formula::Add(a, b) => fold_bin(a, b, Formula::Add),
        Formula::Mul(a, b) => fold_bin(a, b, Formula::Mul),
        _ => None,
    }
}

fn subst_leaf(f: &Formula, name: &str, sort: &Sort, by: &Formula) -> Formula {
    map_leaves_opt(f, &|g| match leaf(g) {
        Some((n, s)) if n == name && s == sort => Some(by.clone()),
        _ => None,
    })
    .unwrap_or_else(|| f.clone())
}

fn leaves_of(f: &Formula, sort: &Sort, out: &mut BTreeSet<String>) {
    trust_types::visit_formula_nodes(f, &mut |g| {
        if let Some((name, s)) = leaf(g)
            && s == sort
            && !out.contains(name)
        {
            out.insert(name.to_string());
        }
    });
}

fn mentions(f: &Formula, name: &str, sort: &Sort) -> bool {
    trust_types::any_formula_node(f, &mut |g| {
        matches!(leaf(g), Some((n, s)) if n == name && s == sort)
    })
}

fn node_count(f: &Formula) -> usize {
    let mut nodes = 0usize;
    trust_types::visit_formula_nodes(f, &mut |_| nodes += 1);
    nodes
}

// ---------------------------------------------------------------------------
// Proof-term combinators (UNTRUSTED: the kernel re-checks everything built here).
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
enum IntEvaluation {
    Literals,
    ClosedAdditions,
}

impl IntEvaluation {
    fn value(self, formula: &Formula) -> Option<i128> {
        fn closed_addition(formula: &Formula, depth: usize) -> Option<i128> {
            if depth > MAX_EVAL_DEPTH {
                return None;
            }
            match formula {
                Formula::Add(a, b) => {
                    closed_addition(a, depth + 1)?.checked_add(closed_addition(b, depth + 1)?)
                }
                _ => int_literal_value(formula),
            }
        }
        match self {
            Self::Literals => int_literal_value(formula),
            Self::ClosedAdditions => closed_addition(formula, 0),
        }
    }
}

struct Fresh {
    next_id: u64,
    int_evaluation: IntEvaluation,
    // Disabled for every pre-existing flat lane, preserving its exact terms.
    proof_sharing: bool,
    proof_bindings: Vec<(FVarId, Expr, Expr)>,
}

impl Fresh {
    fn next(&mut self) -> FVarId {
        self.next_id += 1;
        FVarId::new(LOCAL_FVAR_BASE + self.next_id)
    }

    // Bind a complex derived proof once. Its original proposition and actual
    // proof value remain in the term and must be checked by the same kernel.
    // FVar leaves already name checked hypotheses or scoped definitions.
    fn share_proof(&mut self, formula: &Formula, proof: Expr) -> Option<Expr> {
        if !self.proof_sharing || matches!(proof.kind(), clean_kernel::expr::ExprKind::FVar(_)) {
            return Some(proof);
        }
        let proposition = enc_prop(formula, Hole::None)?;
        let id = self.next();
        self.proof_bindings.push((id, proposition, proof));
        Some(Expr::fvar(id))
    }

    /// `λ (h : ty). body(h)`, with `h` abstracted to the bound variable.
    fn lam(&mut self, ty: Expr, body: impl FnOnce(Expr) -> Option<Expr>) -> Option<Expr> {
        let h = self.next();
        let inner = body(Expr::fvar(h))?;
        Some(Expr::lam(BinderInfo::Default, ty, inner.abstract_fvar(h)))
    }
}

fn false_elim(target: Expr, h: Expr) -> Expr {
    static HEAD: std::sync::OnceLock<Expr> = std::sync::OnceLock::new();
    let head = HEAD.get_or_init(|| Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]));
    Expr::apps(head.clone(), [target, h])
}

/// `@Eq.subst.{1} Prop motive a b h m : motive b` (propositional rewrite).
fn eq_subst_prop(motive: Expr, a: Expr, b: Expr, h: Expr, m: Expr) -> Expr {
    static HEAD: std::sync::OnceLock<Expr> = std::sync::OnceLock::new();
    let head = HEAD.get_or_init(|| {
        Expr::app(
            Expr::const_(Name::from_string("Eq.subst"), vec![Level::succ(Level::zero())]),
            Expr::prop(),
        )
    });
    Expr::apps(head.clone(), [motive, a, b, h, m])
}

/// Proofs of each component of a right-nested `And` from `h : And …`.
fn and_components(props: &[Expr], h: Expr) -> Vec<Expr> {
    match props {
        [] => Vec::new(),
        [_] => vec![h],
        [head, rest @ ..] => {
            let rest_prop = nest("And", true_expr(), rest);
            let mut out = vec![const_app("And.left", [head.clone(), rest_prop.clone(), h.clone()])];
            out.extend(and_components(rest, const_app("And.right", [head.clone(), rest_prop, h])));
            out
        }
    }
}

fn and_intro(props: &[Expr], proofs: &[Expr]) -> Option<Expr> {
    match (props, proofs) {
        ([], []) => Some(Expr::const_(Name::from_string("True.intro"), vec![])),
        ([_], [p]) => Some(p.clone()),
        ([head, rest @ ..], [p, ps @ ..]) => Some(const_app(
            "And.intro",
            [head.clone(), nest("And", true_expr(), rest), p.clone(), and_intro(rest, ps)?],
        )),
        _ => None,
    }
}

fn or_inject(props: &[Expr], index: usize, proof: Expr) -> Option<Expr> {
    match props {
        [] => None,
        [_] => (index == 0).then_some(proof),
        [head, rest @ ..] => {
            let rest_prop = nest("Or", false_expr(), rest);
            if index == 0 {
                Some(const_app("Or.inl", [head.clone(), rest_prop, proof]))
            } else {
                Some(const_app(
                    "Or.inr",
                    [head.clone(), rest_prop, or_inject(rest, index - 1, proof)?],
                ))
            }
        }
    }
}

/// `(Or …) → False` from one refutation per disjunct (`Or.rec` into `False`).
fn or_refute(props: &[Expr], refs: &[Expr], fresh: &mut Fresh) -> Option<Expr> {
    match (props, refs) {
        ([], []) => fresh.lam(false_expr(), Some),
        ([_], [r]) => Some(r.clone()),
        ([head, rest @ ..], [r, rs @ ..]) => {
            let rest_prop = nest("Or", false_expr(), rest);
            let or_prop = const_app("Or", [head.clone(), rest_prop.clone()]);
            let motive = Expr::lam(BinderInfo::Default, or_prop.clone(), false_expr());
            let rest_ref = or_refute(rest, rs, fresh)?;
            fresh.lam(or_prop, |h| {
                Some(const_app("Or.rec", [head.clone(), rest_prop, motive, r.clone(), rest_ref, h]))
            })
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Int equivalence classes (rewriting step 2).
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Node {
    /// Ordered FIRST so a class's representative is its literal when it has one.
    Lit(i128),
    Var(String),
}

fn int_node(f: &Formula, evaluation: IntEvaluation) -> Option<Node> {
    match leaf(f) {
        Some((name, Sort::Int)) => Some(Node::Var(name.to_string())),
        Some(_) => None,
        None => evaluation.value(f).map(Node::Lit),
    }
}

/// Two `Int` terms with the same encoding: one variable (either spelling) or
/// one literal value, or structurally identical.
fn same_int_term(a: &Formula, b: &Formula, evaluation: IntEvaluation) -> bool {
    match (int_node(a, evaluation), int_node(b, evaluation)) {
        (Some(x), Some(y)) => x == y,
        _ => a == b,
    }
}

fn node_expr(n: &Node) -> Option<Expr> {
    match n {
        Node::Lit(k) => int_literal_to_kernel(*k),
        Node::Var(name) => Some(skolem(name)),
    }
}

fn node_formula(n: &Node) -> Formula {
    match n {
        Node::Lit(k) => Formula::Int(*k),
        Node::Var(name) => Formula::Var(name.clone(), Sort::Int),
    }
}

/// `x = y` edges from the facts: `adj[x]` holds `(y, proof of x = y)`.
type Adjacency = BTreeMap<Node, Vec<(Node, Expr)>>;

/// A proof of `from = to` along a shortest path of `adj` (BFS, deterministic).
fn path_proof(adj: &Adjacency, from: &Node, to: &Node) -> Option<Expr> {
    if from == to {
        return Some(eq_refl_int(node_expr(from)?));
    }
    let mut parent: BTreeMap<Node, (Node, Expr)> = BTreeMap::new();
    let mut queue = VecDeque::from([from.clone()]);
    let mut seen = BTreeSet::from([from.clone()]);
    while let Some(node) = queue.pop_front() {
        if &node == to {
            break;
        }
        for (next, proof) in adj.get(&node).into_iter().flatten() {
            if seen.insert(next.clone()) {
                parent.insert(next.clone(), (node.clone(), proof.clone()));
                queue.push_back(next.clone());
            }
        }
    }
    // Walk back to `from`, collecting the edges in forward order.
    let mut edges: Vec<(Node, Node, Expr)> = Vec::new();
    let mut cursor = to.clone();
    while &cursor != from {
        let (prev, proof) = parent.get(&cursor)?.clone();
        edges.push((prev.clone(), cursor, proof));
        cursor = prev;
    }
    edges.reverse();
    let mut iter = edges.into_iter();
    let (start, mut end, mut acc) = iter.next()?;
    let start_e = node_expr(&start)?;
    for (_, next, proof) in iter {
        acc = eq_trans_int(start_e.clone(), node_expr(&end)?, node_expr(&next)?, acc, proof);
        end = next;
    }
    Some(acc)
}

// ---------------------------------------------------------------------------
// Facts and the evaluator.
// ---------------------------------------------------------------------------

/// A formula together with a proof term of its [`enc_prop`] encoding.
#[derive(Clone)]
struct Fact {
    formula: Formula,
    proof: Expr,
}

/// A three-valued verdict with its evidence: `True(p)` carries `p : ⌜f⌝`,
/// `False(r)` carries `r : ⌜f⌝ → False`.
enum Val {
    True(Expr),
    False(Expr),
    Unknown,
}

#[derive(Default)]
struct Kb {
    facts: Vec<Fact>,
    index: FxHashMap<Formula, usize>,
    neg_index: FxHashMap<Formula, usize>,
    has_int_eq: bool,
    has_neg_int_eq: bool,
    fired: Vec<bool>,
}

impl Kb {
    /// Add a fact, splitting a conjunction into its components.
    fn add(&mut self, formula: Formula, proof: Expr, fresh: &mut Fresh) -> Option<()> {
        if self.facts.len() >= MAX_FACTS {
            return None;
        }
        if self.index.contains_key(&formula) {
            return Some(());
        }
        // Hoist before projecting And: each child's proof then refers to this
        // checked parent definition instead of copying the whole derivation.
        let proof = fresh.share_proof(&formula, proof)?;
        if let Formula::And(gs) = &formula {
            let props = gs.iter().map(|g| enc_prop(g, Hole::None)).collect::<Option<Vec<_>>>()?;
            for (g, p) in gs.iter().zip(and_components(&props, proof.clone())) {
                self.add(g.clone(), p, fresh)?;
            }
        }
        let idx = self.facts.len();
        match &formula {
            Formula::Not(inner) => {
                if matches!(inner.as_ref(), Formula::Eq(a, _) if !is_bool_valued(a)) {
                    self.has_neg_int_eq = true;
                }
                self.neg_index.entry((**inner).clone()).or_insert(idx);
            }
            Formula::Eq(a, _) if !is_bool_valued(a) => {
                self.has_int_eq = true;
            }
            _ => {}
        }
        self.index.insert(formula.clone(), idx);
        self.facts.push(Fact { formula, proof });
        self.fired.push(false);
        Some(())
    }

    fn get(&self, f: &Formula) -> Option<&Expr> {
        self.index.get(f).map(|&i| &self.facts[i].proof)
    }

    /// A verdict read straight from the facts (and `Int` `=` symmetry).
    fn lookup(&self, f: &Formula, fresh: &mut Fresh) -> Option<Val> {
        if let Some(p) = self.get(f) {
            return Some(Val::True(p.clone()));
        }
        if let Some(&idx) = self.neg_index.get(f) {
            return Some(Val::False(self.facts[idx].proof.clone()));
        }
        if (self.has_int_eq || self.has_neg_int_eq)
            && let Formula::Eq(a, b) = f
            && !is_bool_valued(a)
        {
            let flipped = Formula::Eq(b.clone(), a.clone());
            if self.has_int_eq
                && let Some(p) = self.get(&flipped)
            {
                let (ka, kb) = (enc_term(a, Hole::None)?, enc_term(b, Hole::None)?);
                return Some(Val::True(eq_symm_int(kb, ka, p.clone())));
            }
            if self.has_neg_int_eq
                && let Some(&idx) = self.neg_index.get(&flipped)
            {
                let (ka, kb) = (enc_term(a, Hole::None)?, enc_term(b, Hole::None)?);
                // ¬(b = a) and h : a = b ⊢ False.
                let r = self.facts[idx].proof.clone();
                let lam = fresh.lam(eq_int(ka.clone(), kb.clone()), |h| {
                    Some(Expr::app(r, eq_symm_int(ka, kb, h)))
                })?;
                return Some(Val::False(lam));
            }
        }
        None
    }

    fn eval(&self, f: &Formula, fresh: &mut Fresh, depth: usize) -> Val {
        if depth > MAX_EVAL_DEPTH {
            return Val::Unknown;
        }
        let structural = self.eval_structural(f, fresh, depth).unwrap_or(Val::Unknown);
        match structural {
            Val::Unknown => self.lookup(f, fresh).unwrap_or(Val::Unknown),
            decided => decided,
        }
    }

    fn eval_structural(&self, f: &Formula, fresh: &mut Fresh, depth: usize) -> Option<Val> {
        let d = depth + 1;
        Some(match f {
            Formula::Bool(true) => Val::True(Expr::const_(Name::from_string("True.intro"), vec![])),
            Formula::Bool(false) => Val::False(fresh.lam(false_expr(), Some)?),
            Formula::Not(a) => match self.eval(a, fresh, d) {
                Val::True(p) => Val::False(
                    fresh.lam(not_prop(enc_prop(a, Hole::None)?), |h| Some(Expr::app(h, p)))?,
                ),
                Val::False(r) => Val::True(r),
                Val::Unknown => Val::Unknown,
            },
            Formula::And(gs) => {
                let props =
                    gs.iter().map(|g| enc_prop(g, Hole::None)).collect::<Option<Vec<_>>>()?;
                let mut proofs = Vec::with_capacity(gs.len());
                let mut all_true = true;
                for (i, g) in gs.iter().enumerate() {
                    match self.eval(g, fresh, d) {
                        Val::True(p) => proofs.push(p),
                        Val::False(r) => {
                            let whole = nest("And", true_expr(), &props);
                            return Some(Val::False(fresh.lam(whole, |h| {
                                let component = and_components(&props, h).into_iter().nth(i)?;
                                Some(Expr::app(r, component))
                            })?));
                        }
                        Val::Unknown => all_true = false,
                    }
                }
                if !all_true {
                    return Some(Val::Unknown);
                }
                Val::True(and_intro(&props, &proofs)?)
            }
            Formula::Or(gs) => {
                let props =
                    gs.iter().map(|g| enc_prop(g, Hole::None)).collect::<Option<Vec<_>>>()?;
                let mut refs = Vec::with_capacity(gs.len());
                let mut all_false = true;
                for (i, g) in gs.iter().enumerate() {
                    match self.eval(g, fresh, d) {
                        Val::True(p) => return Some(Val::True(or_inject(&props, i, p)?)),
                        Val::False(r) => refs.push(r),
                        Val::Unknown => all_false = false,
                    }
                }
                if !all_false {
                    return Some(Val::Unknown);
                }
                Val::False(or_refute(&props, &refs, fresh)?)
            }
            Formula::Implies(a, b) => {
                let (pa_ty, pb_ty) = (enc_prop(a, Hole::None)?, enc_prop(b, Hole::None)?);
                let va = self.eval(a, fresh, d);
                if let Val::False(ra) = &va {
                    let ra = ra.clone();
                    return Some(Val::True(
                        fresh.lam(pa_ty, |h| Some(false_elim(pb_ty, Expr::app(ra, h))))?,
                    ));
                }
                match (va, self.eval(b, fresh, d)) {
                    (_, Val::True(pb)) => Val::True(fresh.lam(pa_ty, |_| Some(pb))?),
                    (Val::True(pa), Val::False(rb)) => {
                        Val::False(fresh.lam(Expr::arrow(pa_ty, pb_ty), |h| {
                            Some(Expr::app(rb, Expr::app(h, pa)))
                        })?)
                    }
                    _ => Val::Unknown,
                }
            }
            Formula::Eq(a, b) if is_bool_valued(a) && is_bool_valued(b) => {
                let (pa_ty, pb_ty) = (enc_prop(a, Hole::None)?, enc_prop(b, Hole::None)?);
                if a == b {
                    let id_a = fresh.lam(pa_ty.clone(), Some)?;
                    return Some(Val::True(const_app(
                        "Iff.intro",
                        [pa_ty, pb_ty, id_a.clone(), id_a],
                    )));
                }
                let iff = const_app("Iff", [pa_ty.clone(), pb_ty.clone()]);
                match (self.eval(a, fresh, d), self.eval(b, fresh, d)) {
                    (Val::True(pa), Val::True(pb)) => {
                        let fwd = fresh.lam(pa_ty.clone(), |_| Some(pb))?;
                        let bwd = fresh.lam(pb_ty.clone(), |_| Some(pa))?;
                        Val::True(const_app("Iff.intro", [pa_ty, pb_ty, fwd, bwd]))
                    }
                    (Val::False(ra), Val::False(rb)) => {
                        let fwd = fresh.lam(pa_ty.clone(), |h| {
                            Some(false_elim(pb_ty.clone(), Expr::app(ra, h)))
                        })?;
                        let bwd = fresh.lam(pb_ty.clone(), |h| {
                            Some(false_elim(pa_ty.clone(), Expr::app(rb, h)))
                        })?;
                        Val::True(const_app("Iff.intro", [pa_ty, pb_ty, fwd, bwd]))
                    }
                    (Val::True(pa), Val::False(rb)) => Val::False(fresh.lam(iff, |h| {
                        Some(Expr::app(rb, const_app("Iff.mp", [pa_ty, pb_ty, h, pa])))
                    })?),
                    (Val::False(ra), Val::True(pb)) => Val::False(fresh.lam(iff, |h| {
                        Some(Expr::app(ra, const_app("Iff.mpr", [pa_ty, pb_ty, h, pb])))
                    })?),
                    _ => Val::Unknown,
                }
            }
            Formula::Eq(a, b) => {
                let (ka, kb) = (enc_term(a, Hole::None)?, enc_term(b, Hole::None)?);
                if same_int_term(a, b, fresh.int_evaluation) {
                    return Some(Val::True(eq_refl_int(ka)));
                }
                match (fresh.int_evaluation.value(a), fresh.int_evaluation.value(b)) {
                    (Some(x), Some(y)) if x != y => {
                        Val::False(fresh.lam(eq_int(ka, kb), |h| refute_false_eq(x, y, h))?)
                    }
                    _ => Val::Unknown,
                }
            }
            Formula::Lt(a, b) => self.eval_order(a, b, true, fresh)?,
            Formula::Le(a, b) => self.eval_order(a, b, false, fresh)?,
            Formula::Gt(a, b) => self.eval_order(b, a, true, fresh)?,
            Formula::Ge(a, b) => self.eval_order(b, a, false, fresh)?,
            _ => Val::Unknown,
        })
    }

    /// `a < b` (`strict`) or `a ≤ b` over two closed literals, or with both
    /// sides the same term.
    fn eval_order(&self, a: &Formula, b: &Formula, strict: bool, fresh: &mut Fresh) -> Option<Val> {
        let (ka, kb) = (enc_term(a, Hole::None)?, enc_term(b, Hole::None)?);
        let prop =
            if strict { lt_int(ka.clone(), kb.clone()) } else { le_int(ka.clone(), kb.clone()) };
        if same_int_term(a, b, fresh.int_evaluation) {
            return Some(if strict {
                Val::False(
                    fresh.lam(prop, |h| Some(Expr::app(const_app("Int.lt_irrefl", [ka]), h)))?,
                )
            } else {
                Val::True(const_app("Int.le_refl", [ka]))
            });
        }
        let (Some(x), Some(y)) = (fresh.int_evaluation.value(a), fresh.int_evaluation.value(b))
        else {
            return Some(Val::Unknown);
        };
        let atom = ClosedOrderAtom { a: x, b: y, is_lt: strict };
        // Preserve the original lane's reducer range. The final fallback may
        // refute wider false orders with `refute_false_atom`'s u128 witness;
        // it still asks the kernel to check the original, unfolded Add terms.
        let wide = i64::try_from(x).is_err() || i64::try_from(y).is_err();
        if wide && (matches!(fresh.int_evaluation, IntEvaluation::Literals) || !atom.is_false()) {
            return Some(Val::Unknown);
        }
        if atom.is_false() {
            return Some(Val::False(fresh.lam(prop, |h| refute_false_atom(&atom, h))?));
        }
        // True: `a < b` is `NonNeg (b - a - 1)`, `a ≤ b` is `NonNeg (b - a)`.
        let gap = nonneg_gap_u128(y, x)?;
        let witness = if strict { gap.checked_sub(1)? } else { gap };
        Some(Val::True(nonneg_mk_u128(witness)))
    }

    /// The atom to case-split on: the first undecided antecedent of an
    /// implication fact (under any number of `¬`), or the first undecided side
    /// of a `⟺` fact. `None` when there is nothing to split.
    fn split_candidate(&self, fresh: &mut Fresh) -> Option<Formula> {
        fn strip(mut f: &Formula) -> &Formula {
            while let Formula::Not(inner) = f {
                f = inner;
            }
            f
        }
        let atomic = |f: &Formula| {
            matches!(
                f,
                Formula::Eq(..)
                    | Formula::Lt(..)
                    | Formula::Le(..)
                    | Formula::Gt(..)
                    | Formula::Ge(..)
            ) || matches!(leaf(f), Some((_, Sort::Bool)))
        };
        for fact in &self.facts {
            let sides: [Option<&Formula>; 2] = match &fact.formula {
                Formula::Implies(a, _) => [Some(a), None],
                Formula::Eq(a, b) if is_bool_valued(a) && is_bool_valued(b) => [Some(a), Some(b)],
                _ => continue,
            };
            for side in sides.into_iter().flatten() {
                let atom = strip(side);
                if atomic(atom) && matches!(self.eval(atom, fresh, 0), Val::Unknown) {
                    return Some(atom.clone());
                }
            }
        }
        None
    }

    /// Search the facts for one that evaluates FALSE: its refutation applied to
    /// its own proof is the certificate term.
    fn refutation(&self, fresh: &mut Fresh) -> Option<Expr> {
        self.facts.iter().find_map(|fact| match self.eval(&fact.formula, fresh, 0) {
            Val::False(r) => Some(Expr::app(r, fact.proof.clone())),
            _ => None,
        })
    }

    /// One round of forward chaining: modus ponens through `→` facts and both
    /// directions of `⟺` facts. Returns whether anything was added.
    fn chain(&mut self, fresh: &mut Fresh) -> Option<bool> {
        let mut added = false;
        let mut i = 0;
        while i < self.facts.len() {
            if self.fired[i] {
                i += 1;
                continue;
            }
            let Fact { formula, proof } = self.facts[i].clone();
            let mut derived: Vec<(Formula, Expr)> = Vec::new();
            match &formula {
                Formula::Implies(a, b) => {
                    if let Val::True(pa) = self.eval(a, fresh, 0) {
                        derived.push(((**b).clone(), Expr::app(proof, pa)));
                    }
                }
                Formula::Eq(a, b) if is_bool_valued(a) && is_bool_valued(b) => {
                    let (pa_ty, pb_ty) = (enc_prop(a, Hole::None)?, enc_prop(b, Hole::None)?);
                    match self.eval(a, fresh, 0) {
                        Val::True(pa) => derived.push((
                            (**b).clone(),
                            const_app("Iff.mp", [pa_ty.clone(), pb_ty.clone(), proof.clone(), pa]),
                        )),
                        Val::False(ra) => {
                            let r = fresh.lam(pb_ty.clone(), |h| {
                                Some(Expr::app(
                                    ra,
                                    const_app(
                                        "Iff.mpr",
                                        [pa_ty.clone(), pb_ty.clone(), proof.clone(), h],
                                    ),
                                ))
                            })?;
                            derived.push((Formula::Not(b.clone()), r));
                        }
                        Val::Unknown => {}
                    }
                    match self.eval(b, fresh, 0) {
                        Val::True(pb) => derived.push((
                            (**a).clone(),
                            const_app("Iff.mpr", [pa_ty.clone(), pb_ty.clone(), proof.clone(), pb]),
                        )),
                        Val::False(rb) => {
                            let r = fresh.lam(pa_ty.clone(), |h| {
                                Some(Expr::app(
                                    rb,
                                    const_app(
                                        "Iff.mp",
                                        [pa_ty.clone(), pb_ty.clone(), proof.clone(), h],
                                    ),
                                ))
                            })?;
                            derived.push((Formula::Not(a.clone()), r));
                        }
                        Val::Unknown => {}
                    }
                }
                _ => {}
            }
            if !derived.is_empty() {
                self.fired[i] = true;
                for (f, p) in derived {
                    if !self.index.contains_key(&f) {
                        self.add(f, p, fresh)?;
                        added = true;
                    }
                }
            }
            i += 1;
        }
        Some(added)
    }
}

// ---------------------------------------------------------------------------
// The lane.
// ---------------------------------------------------------------------------

fn flatten_and<'a>(f: &'a Formula, out: &mut Vec<&'a Formula>) {
    match f {
        Formula::And(children) => children.iter().for_each(|c| flatten_and(c, out)),
        Formula::Bool(true) => {}
        other => out.push(other),
    }
}

/// The variable → skolem map must be injective (module doc): every variable
/// name at ONE sort, and no two names sharing an encoded spelling.
fn injective_skolems(conjuncts: &[&Formula]) -> Option<BTreeSet<String>> {
    let mut by_encoded: BTreeMap<String, (&str, bool)> = BTreeMap::new();
    for &c in conjuncts {
        if !trust_types::all_formula_nodes(c, &mut |g| {
            let Some((name, sort)) = leaf(g) else { return true };
            let is_bool = match sort {
                Sort::Bool => true,
                Sort::Int => false,
                _ => return false,
            };
            let entry = by_encoded.entry(encoded_var_name(name)).or_insert((name, is_bool));
            entry.0 == name && entry.1 == is_bool
        }) {
            return None;
        }
    }
    Some(by_encoded.into_values().map(|(name, _)| name.to_string()).collect())
}

/// The lane entry point (see the module doc). Returns `None` whenever any step
/// declines; never a certificate the kernel did not re-check.
pub(super) fn certify_rewrite_evaluation(
    violation: &Formula,
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    certify_rewrite_evaluation_with(violation, identity, IntEvaluation::Literals)
}

/// Final fallback for successive checked additions whose SSA aliases only
/// become literal equalities after rewriting. Closed addition is proof search:
/// hypotheses and their kernel encodings remain the original formulas.
pub(super) fn certify_rewrite_evaluation_with_closed_additions(
    violation: &Formula,
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    certify_rewrite_evaluation_with(violation, identity, IntEvaluation::ClosedAdditions)
}

fn certify_rewrite_evaluation_with(
    violation: &Formula,
    identity: &ObligationIdentity,
    evaluation: IntEvaluation,
) -> Option<trust_ir::ProofEvidence> {
    let (hyps, facts, var_names) = prepare_rewrite_hypotheses(violation)?;

    let mut fresh = Fresh {
        next_id: 0,
        int_evaluation: evaluation,
        proof_sharing: false,
        proof_bindings: Vec::new(),
    };
    let term = refute(facts, &mut fresh, MAX_SPLITS)?;
    finish_certificate(&hyps, &term, &var_names, identity)
}

/// Reconstruct only the original hypothesis context; never run rewrite search.
/// Shared with the producer so replay does not trust serialized assumptions.
pub(super) fn presented_context_variables(
    violation: &Formula,
    context: &[u8],
) -> Option<BTreeSet<String>> {
    prepare_rewrite_hypotheses(violation)
        .and_then(|(hyps, _, vars)| {
            let expected =
                super::serialize_context(&super::reduced_context(&super::build_ctx(&hyps))).ok()?;
            (expected == context).then_some(vars)
        })
        .or_else(|| paths::presented_context_variables(violation, context))
}

fn prepare_rewrite_hypotheses(
    violation: &Formula,
) -> Option<(Vec<Hyp>, Vec<Fact>, BTreeSet<String>)> {
    if node_count(violation) > MAX_VIOLATION_NODES {
        return None;
    }
    let mut flat = Vec::new();
    flatten_and(violation, &mut flat);
    if flat.is_empty() || flat.len() > MAX_POOL {
        return None;
    }
    // A literal `false` conjunct is a PRODUCER PLACEHOLDER or an already
    // discharged row, never a refutation this lane should mint authority for.
    // Measured 2026-09-25: an unlowered contract predicate
    // (`#[trust::invariant(x > 0)]`, `Custom trust.contract unsupported`) carries
    // `Bool(false)` as its violation, no earlier lane certified it, and this lane
    // did — the compiler's authority validator then refused the label ("Proved
    // label lacked exact kernel/native proof authority"), but a consumer of
    // `certify_vc` must not depend on that backstop. A genuine closed
    // contradiction is the closed-constant lane's, not this one's.
    if flat.iter().any(|c| matches!(c, Formula::Bool(false))) {
        return None;
    }
    // 1. Hypotheses: the encodable conjuncts, verbatim.
    let mut kept: Vec<(&Formula, Expr, String)> = Vec::new();
    for c in flat {
        if let (Some(prop), Some(smt)) = (enc_prop(c, Hole::None), smt_prop(c)) {
            kept.push((c, prop, smt));
        }
    }
    let kept_formulas: Vec<&Formula> = kept.iter().map(|(c, ..)| *c).collect();
    let var_names = injective_skolems(&kept_formulas)?;
    // A pool with no variable at all is closed arithmetic — not this lane's.
    if var_names.is_empty() {
        return None;
    }
    let mut hyps: Vec<Hyp> = Vec::new();
    let mut facts: Vec<Fact> = Vec::new();
    for (c, prop, smt) in kept {
        let fvar = push_hyp(&mut hyps, smt, prop);
        facts.push(Fact { formula: c.clone(), proof: Expr::fvar(fvar) });
    }

    Some((hyps, facts, var_names))
}

/// The outcome of one rewrite-evaluate-chain pass.
enum Saturation {
    /// A term of type `False` over the facts' proofs.
    Refuted(Expr),
    /// No refutation; the saturated knowledge base (rewritten and chained).
    Open(Kb),
}

fn proof_free_variables(proof: &Expr, out: &mut FxHashSet<FVarId>) -> Option<()> {
    use clean_kernel::expr::ExprKind;
    let mut pending = vec![proof];
    let mut visited = FxHashSet::default();
    while let Some(proof) = pending.pop() {
        // Expr children form a shared immutable DAG. Walk each borrowed node
        // once; expanding every incoming edge can take exponential work even
        // when the proof itself has only a few dozen distinct nodes. All nodes
        // stay alive under the input borrow, so their addresses remain stable.
        if !proof.has_fvar_quick() || !visited.insert(std::ptr::from_ref(proof)) {
            continue;
        }
        match proof.kind() {
            ExprKind::FVar(id) => {
                out.insert(*id);
            }
            ExprKind::App(function, argument) => {
                pending.extend([function.as_ref(), argument.as_ref()])
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                pending.extend([ty.as_ref(), body.as_ref()]);
            }
            ExprKind::Let(_, ty, value, body, _) => {
                pending.extend([ty.as_ref(), value.as_ref(), body.as_ref()]);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => pending.push(inner),
            // This producer constructs ordinary CIC terms only. If its grammar
            // grows, decline rather than overlook a dependency in a new node.
            _ => return None,
        }
    }
    Some(())
}

fn close_proof_bindings(mut proof: Expr, bindings: Vec<(FVarId, Expr, Expr)>) -> Option<Expr> {
    let mut needed = FxHashSet::default();
    proof_free_variables(&proof, &mut needed)?;
    for (id, proposition, value) in bindings.into_iter().rev() {
        if !needed.remove(&id) {
            continue;
        }
        // Retain the transitive dependency closure of the proof actually
        // returned. Unused search derivations are not part of its theorem.
        proof_free_variables(&proposition, &mut needed)?;
        proof_free_variables(&value, &mut needed)?;
        proof = Expr::let_named(Name::anon(), proposition, value, proof.abstract_fvar(id), false);
    }
    Some(proof)
}

/// Refute `facts`: saturate, restart on newly derived equalities, then split.
///
/// * RESTART: chaining can derive a fact the rewriting would have used had it
///   been present from the start — an `Int` alias (`_3 = d` out of `¬(d = 0) →
///   _3 = d`) or a rewritten unit (`_3 = 0` out of the asserted `_4` with
///   `_4 ⟺ _3 = 0`). Each is added, with the proof it was derived by, to the
///   input facts and the pass is run again (at most [`MAX_RESTARTS`] times).
/// * SPLIT: when saturation stalls on an implication whose antecedent is
///   undecided, case-split on its atom `A` with `Classical.em A` and refute both
///   branches (`Or.rec`), each with `A` (or `¬A`) as one more fact bound by the
///   branch's lambda — at most [`MAX_SPLITS`] deep and only for small pools.
///
/// The injected lemma of a DIAMOND helper reaches its caller as exactly such an
/// implication pair (`¬(d = 0) → _3 = d`, `¬¬(d = 0) → _3 = 1`), so this is what
/// lets `x / nz(d)` certify, not only prove.
fn refute(facts: Vec<Fact>, fresh: &mut Fresh, splits_left: usize) -> Option<Expr> {
    if !fresh.proof_sharing {
        return refute_inner(facts, fresh, splits_left);
    }
    // A recursive branch owns only definitions created after this marker.
    // Close them BEFORE its caller abstracts the branch assumption, and remove
    // them even when search declines so no sibling can inherit those proofs.
    let marker = fresh.proof_bindings.len();
    let result = refute_inner(facts, fresh, splits_left);
    let bindings = fresh.proof_bindings.split_off(marker);
    close_proof_bindings(result?, bindings)
}

fn refute_inner(facts: Vec<Fact>, fresh: &mut Fresh, splits_left: usize) -> Option<Expr> {
    let mut facts = facts;
    let mut open = None;
    for _ in 0..MAX_RESTARTS {
        match saturate(&facts, fresh)? {
            Saturation::Refuted(term) => return Some(term),
            Saturation::Open(kb) => {
                let known: FxHashSet<&Formula> = facts.iter().map(|f| &f.formula).collect();
                let derived: Vec<Fact> = kb
                    .facts
                    .iter()
                    .filter(|f| {
                        restart_worthy(&f.formula, fresh.int_evaluation)
                            && !known.contains(&f.formula)
                    })
                    .cloned()
                    .collect();
                if derived.is_empty() {
                    open = Some(kb);
                    break;
                }
                facts.extend(derived);
            }
        }
    }
    let kb = open?;
    if splits_left == 0
        || kb.facts.iter().map(|f| node_count(&f.formula)).sum::<usize>() > MAX_SPLIT_NODES
    {
        return None;
    }
    let atom = kb.split_candidate(fresh)?;
    let prop = enc_prop(&atom, Hole::None)?;
    let not_atom = Formula::Not(Box::new(atom.clone()));
    let branch = |assumed: Formula, ty: Expr, fresh: &mut Fresh| -> Option<Expr> {
        let h = fresh.next();
        let mut with = facts.clone();
        with.push(Fact { formula: assumed, proof: Expr::fvar(h) });
        let body = refute(with, fresh, splits_left - 1)?;
        Some(Expr::lam(BinderInfo::Default, ty, body.abstract_fvar(h)))
    };
    let pos = branch(atom, prop.clone(), fresh)?;
    let neg = branch(not_atom, not_prop(prop.clone()), fresh)?;
    let or_prop = const_app("Or", [prop.clone(), not_prop(prop.clone())]);
    let motive = Expr::lam(BinderInfo::Default, or_prop, false_expr());
    let em = const_app("Classical.em", [prop.clone()]);
    Some(const_app("Or.rec", [prop.clone(), not_prop(prop), motive, pos, neg, em]))
}

/// A derived fact worth restarting the rewriting for: an `Int` alias or
/// var-to-literal equality, or a `Bool` variable definition.
fn restart_worthy(f: &Formula, evaluation: IntEvaluation) -> bool {
    let Formula::Eq(a, b) = f else { return false };
    if let (Some(x), Some(y)) = (int_node(a, evaluation), int_node(b, evaluation)) {
        return x != y;
    }
    is_bool_valued(a)
        && is_bool_valued(b)
        && (matches!(leaf(a), Some((_, Sort::Bool))) || matches!(leaf(b), Some((_, Sort::Bool))))
}

/// One pass: Int classes, Bool definitions, evaluation and chaining.
fn saturate(facts: &[Fact], fresh: &mut Fresh) -> Option<Saturation> {
    let facts: Vec<Fact> = facts.to_vec();
    // 2. Int classes from `x = y` / `x = k` facts.
    let mut adj: Adjacency = BTreeMap::new();
    let mut alias_fact = vec![false; facts.len()];
    for (i, fact) in facts.iter().enumerate() {
        let Formula::Eq(a, b) = &fact.formula else { continue };
        let (Some(na), Some(nb)) =
            (int_node(a, fresh.int_evaluation), int_node(b, fresh.int_evaluation))
        else {
            continue;
        };
        if na == nb {
            continue;
        }
        let (ea, eb) = (node_expr(&na)?, node_expr(&nb)?);
        adj.entry(na.clone()).or_default().push((nb.clone(), fact.proof.clone()));
        adj.entry(nb).or_default().push((na, eq_symm_int(ea, eb, fact.proof.clone())));
        alias_fact[i] = true;
    }
    let mut rep: BTreeMap<String, Node> = BTreeMap::new();
    let mut rep_proof: BTreeMap<String, Expr> = BTreeMap::new();
    let mut seen: BTreeSet<Node> = BTreeSet::new();
    for start in adj.keys() {
        if !seen.insert(start.clone()) {
            continue;
        }
        // The component, in BFS order.
        let mut component = vec![start.clone()];
        let mut queue = VecDeque::from([start.clone()]);
        while let Some(node) = queue.pop_front() {
            for (next, _) in adj.get(&node).into_iter().flatten() {
                if seen.insert(next.clone()) {
                    component.push(next.clone());
                    queue.push_back(next.clone());
                }
            }
        }
        component.sort();
        let representative = component[0].clone();
        // Two distinct literals in one class ARE the refutation.
        if let (Node::Lit(x), Some(Node::Lit(y))) = (&representative, component.get(1)) {
            let proof = path_proof(&adj, &representative, &Node::Lit(*y))?;
            return refute_false_eq(*x, *y, proof).map(Saturation::Refuted);
        }
        for member in &component {
            if let Node::Var(name) = member
                && member != &representative
            {
                rep_proof.insert(name.clone(), path_proof(&adj, member, &representative)?);
                rep.insert(name.clone(), representative.clone());
            }
        }
    }

    // Rewrite every non-alias fact to representatives.
    let mut rewritten: Vec<Fact> = Vec::new();
    for (fact, is_alias) in facts.into_iter().zip(alias_fact) {
        if is_alias {
            continue; // Absorbed by the classes.
        }
        let Fact { mut formula, mut proof } = fact;
        let mut vars = BTreeSet::new();
        leaves_of(&formula, &Sort::Int, &mut vars);
        for x in vars {
            let (Some(target), Some(eq)) = (rep.get(&x), rep_proof.get(&x)) else { continue };
            let z = fresh.next();
            let z_expr = Expr::fvar(z);
            let body = enc_prop(&formula, Hole::Int(&x, &z_expr))?;
            let motive = Expr::lam(BinderInfo::Default, int_ty(), body.abstract_fvar(z));
            proof = eq_subst_int(motive, skolem(&x), node_expr(target)?, eq.clone(), proof);
            formula = subst_leaf(&formula, &x, &Sort::Int, &node_formula(target));
        }
        rewritten.push(Fact { formula, proof });
    }

    // 3. Bool definitions `v ⟺ φ`, acyclic over the chosen set.
    let mut defs: Vec<(String, Formula, Expr)> = Vec::new(); // (v, φ, (v = 1) = ⌜φ⌝)
    let mut defined: BTreeMap<String, Formula> = BTreeMap::new();
    let mut def_fact = vec![false; rewritten.len()];
    for (i, fact) in rewritten.iter().enumerate() {
        let Formula::Eq(a, b) = &fact.formula else { continue };
        if !(is_bool_valued(a) && is_bool_valued(b)) {
            continue;
        }
        let (pa, pb) = (enc_prop(a, Hole::None)?, enc_prop(b, Hole::None)?);
        let candidate = match (leaf(a), leaf(b)) {
            (Some((v, Sort::Bool)), _) if !mentions(b, v, &Sort::Bool) => {
                Some((v.to_string(), (**b).clone(), fact.proof.clone(), pa.clone(), pb.clone()))
            }
            (_, Some((v, Sort::Bool))) if !mentions(a, v, &Sort::Bool) => {
                // Flip `Iff ⌜φ⌝ (v = 1)` to `Iff (v = 1) ⌜φ⌝`.
                let flipped = const_app(
                    "Iff.intro",
                    [
                        pb.clone(),
                        pa.clone(),
                        const_app("Iff.mpr", [pa.clone(), pb.clone(), fact.proof.clone()]),
                        const_app("Iff.mp", [pa.clone(), pb.clone(), fact.proof.clone()]),
                    ],
                );
                Some((v.to_string(), (**a).clone(), flipped, pb, pa))
            }
            _ => None,
        };
        let Some((v, phi, iff_proof, v_prop, phi_prop)) = candidate else { continue };
        if defined.contains_key(&v) || reaches(&phi, &v, &defined) {
            continue;
        }
        let eq = const_app("propext", [v_prop, phi_prop, iff_proof]);
        defined.insert(v.clone(), phi.clone());
        defs.push((v, phi, eq));
        def_fact[i] = true;
    }

    // Rewrite every non-definition fact through the definitions.
    let mut kb = Kb::default();
    let mut total_nodes = 0usize;
    for (fact, is_def) in rewritten.into_iter().zip(def_fact) {
        if is_def {
            continue; // Absorbed by the definitions.
        }
        let Fact { mut formula, mut proof } = fact;
        for _ in 0..MAX_BOOL_STEPS {
            if node_count(&formula) > MAX_FACT_NODES {
                break;
            }
            let Some((v, phi, eq)) = defs.iter().find(|(v, ..)| mentions(&formula, v, &Sort::Bool))
            else {
                break;
            };
            let z = fresh.next();
            let z_expr = Expr::fvar(z);
            let body = enc_prop(&formula, Hole::Bool(v, &z_expr))?;
            let motive = Expr::lam(BinderInfo::Default, Expr::prop(), body.abstract_fvar(z));
            proof = eq_subst_prop(
                motive,
                bool_var_prop(v)?,
                enc_prop(phi, Hole::None)?,
                eq.clone(),
                proof,
            );
            formula = subst_leaf(&formula, v, &Sort::Bool, phi);
        }
        // An oversized fact is DROPPED (a weakening), keeping every evaluation
        // bounded by `MAX_FACT_NODES` squared.
        let nodes = node_count(&formula);
        if nodes > MAX_FACT_NODES {
            continue;
        }
        total_nodes += nodes;
        if total_nodes > MAX_TOTAL_FACT_NODES {
            return None;
        }
        kb.add(formula, proof, fresh)?;
    }

    // 4. Evaluate; chain; evaluate again.
    for _ in 0..=MAX_ROUNDS {
        if let Some(term) = kb.refutation(fresh) {
            return Some(Saturation::Refuted(term));
        }
        if !kb.chain(fresh)? {
            break;
        }
    }
    Some(Saturation::Open(kb))
}

/// Does `phi` reach the Bool variable `v` through the chosen definitions?
fn reaches<'a>(phi: &'a Formula, v: &str, defined: &'a BTreeMap<String, Formula>) -> bool {
    let mut stack = vec![phi];
    let mut visited: FxHashSet<String> = FxHashSet::default();
    while let Some(f) = stack.pop() {
        let mut vars = BTreeSet::new();
        leaves_of(f, &Sort::Bool, &mut vars);
        for w in vars {
            if w == v {
                return true;
            }
            if visited.insert(w.clone())
                && let Some(next) = defined.get(&w)
            {
                stack.push(next);
            }
        }
    }
    false
}

#[cfg(test)]
#[path = "rewrite_eval_tests.rs"]
mod tests;

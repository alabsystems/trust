// trust-clean/clean_bridge.rs: Bridge between Trust verification IR and clean kernel
//
// Translates Trust's Formula/VcKind types into clean kernel expressions (Expr)
// and provides certificate verification using clean's CertVerifier.
//
// The translation encodes our first-order verification conditions as clean
// theorem statements (Prop-valued expressions). A ProofCert witnessing such
// a statement can then be verified by the clean kernel's type checker.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// ---------------------------------------------------------------------------
// Name helpers
// ---------------------------------------------------------------------------

// Trust: memoize the clean prelude Environment so it is not rebuilt per-VC.
// `Environment::with_prelude()` re-typechecks ~50 prelude constants on every
// call (a profiled compile-time hot path). We build it once and hand out clones.
use std::sync::OnceLock;

use clean_kernel::cert::{CertVerifier, ProofCert};
use clean_kernel::env::{ConstantKind, Declaration, EnvError, Environment};
use clean_kernel::expr::ExprKind;
use clean_kernel::level::Level as LeanLevel;
use clean_kernel::name::Name as LeanName;
use clean_kernel::{BinderInfo, Expr as LeanExpr, TypeChecker};
use trust_types::{Formula, Sort, VcKind};

use crate::error::CertificateError;

// ---------------------------------------------------------------------------
// Certification environment — prelude + the Trust.* canonical-VC signature
// ---------------------------------------------------------------------------

static CERT_ENV: OnceLock<Option<Environment>> = OnceLock::new();

/// Memoized environment in which canonical VC theorems
/// (`Trust.VC.holds <kind> <formula>`, see [`translate_vc_to_clean_theorem`])
/// are STATED, PROVED, and REPLAYED. It is `with_prelude()` extended with the
/// `Trust.*` signature registered by [`register_trust_vc_signature`] (every
/// declaration kernel-type-checked by `add_decl`; none is an axiom).
///
/// `None` (fail-closed: nothing certifies) if registration ever fails.
fn certification_env() -> Option<Environment> {
    CERT_ENV
        .get_or_init(|| {
            let mut env = Environment::try_with_prelude().ok()?;
            register_trust_vc_signature(&mut env).ok()?;
            Some(env)
        })
        .clone()
}

/// Register the `Trust.*` signature that makes canonical VC theorems
/// well-typed and (for genuinely-refutable violations) provable.
///
/// Semantics of the canonical statement: `Trust.VC.holds k p` is DEFINED as
/// `¬p` — "the translated violation formula is refutable". The formula
/// translation ([`translate_formula`]) maps SMT terms and atoms into `Prop`
/// via the constants declared here.
///
/// SOUNDNESS DESIGN (what keeps a provable `Trust.VC.holds k ⟦f⟧` meaning
/// "f is unsatisfiable"):
///
/// - Every term/atom former (`Trust.Formula.var/int/add/lt/…`) is a
///   `Declaration::Opaque`: its inhabitation witness is kernel-type-checked at
///   registration, but the constant NEVER unfolds afterwards (`Reducibility::
///   Opaque` is excluded from delta in the clean kernel). Distinct opaque
///   applications therefore never collapse definitionally, and no proof can
///   inhabit or refute an atom except from the formula's own hypotheses —
///   i.e. exactly the empty-theory (propositional + EUF) fragment.
/// - `Trust.Formula.eq` is the ONLY equality with structure: a REDUCIBLE
///   definition `fun a b => @Eq Prop a b`, giving refutations access to
///   `Eq.trans/symm/congrArg/congr` over the opaque term encodings.
/// - `Trust.Formula.implies := fun a b => a → b` (reducible), so implication
///   keeps its logical meaning.
/// - The LOSSY translation arms are deliberately NOT declared:
///   `Trust.Formula.unknown` and `Trust.Sort.Unknown` collapse distinct Trust
///   terms to one constant, so any formula whose translation contains them
///   must stay UNCERTIFIABLE — the kernel rejects the undeclared constant and
///   every path fails closed to its prior assurance.
/// - Axiom-backed shortcuts (`sorry`, `trustedAy`, `propext`, …) are rejected
///   by the strict closure gate in [`verify_proof_cert`] /
///   [`kernel_gate_and_serialize`], NOT by this signature. In particular
///   `@Eq Prop` is classically degenerate (with propext + choice, any three
///   Props have two equal), so the closure gate requiring a ZERO-axiom
///   transitive closure is load-bearing for EUF soundness, not cosmetic.
fn register_trust_vc_signature(env: &mut Environment) -> Result<(), EnvError> {
    let prop = LeanExpr::prop();
    let type0 = LeanExpr::sort(LeanLevel::succ(LeanLevel::zero()));
    let nat = const_expr("Nat");
    let string = const_expr("String");
    let bool_ty = const_expr("Bool");
    let true_c = const_expr("True");
    let nat_zero = const_expr("Nat.zero");
    let tsort = const_expr("Trust.Sort");
    let vckind = const_expr("Trust.VcKind");

    // `args → ret` and the matching constant witness `fun (_ : args)… => body`.
    let arrows = |args: &[LeanExpr], ret: &LeanExpr| -> LeanExpr {
        args.iter().rev().fold(ret.clone(), |acc, a| LeanExpr::arrow(a.clone(), acc))
    };
    let const_fun = |args: &[LeanExpr], body: &LeanExpr| -> LeanExpr {
        args.iter()
            .rev()
            .fold(body.clone(), |acc, a| LeanExpr::lam(BinderInfo::Default, a.clone(), acc))
    };
    let opaque = |nm: &str, args: &[LeanExpr], ret: &LeanExpr, wit: &LeanExpr| -> Declaration {
        Declaration::Opaque {
            name: name(nm),
            level_params: vec![],
            type_: arrows(args, ret),
            value: const_fun(args, wit),
        }
    };

    // Nominal carrier types for sorts and VC kinds. Their (unfoldable) Nat
    // realization is harmless: every element below is an Opaque constant, so
    // no two of them are ever definitionally equal.
    for carrier in ["Trust.Sort", "Trust.VcKind"] {
        env.add_decl(Declaration::Definition {
            name: name(carrier),
            level_params: vec![],
            type_: type0.clone(),
            value: nat.clone(),
            is_reducible: false,
        })?;
    }

    // Sorts (translate_sort). `Trust.Sort.Unknown` deliberately absent.
    env.add_decl(opaque("Trust.Sort.Bool", &[], &tsort, &nat_zero))?;
    env.add_decl(opaque("Trust.Sort.Int", &[], &tsort, &nat_zero))?;
    env.add_decl(opaque("Trust.Sort.BitVec", &[nat.clone()], &tsort, &nat_zero))?;
    env.add_decl(opaque("Trust.Sort.Array", &[tsort.clone(), tsort.clone()], &tsort, &nat_zero))?;

    // VC kinds (translate_vc_kind). `unknown` IS declared: kind identity is
    // bound by the certificate fingerprint + canonical bytes, and
    // `Trust.VC.holds` discards the kind, so kind-collapse carries no logical
    // content — unlike formula-collapse, which is why the formula-side
    // `unknown` stays undeclared.
    for k in [
        "arithmeticOverflow",
        "shiftOverflow",
        "divisionByZero",
        "remainderByZero",
        "indexOutOfBounds",
        "sliceBoundsCheck",
        "assertion",
        "precondition",
        "postcondition",
        "castOverflow",
        "negationOverflow",
        "unreachable",
        "deadState",
        "deadlock",
        "temporal",
        "liveness",
        "fairness",
        "protocolViolation",
        "taintViolation",
        "refinementViolation",
        "resilienceViolation",
        "nonTermination",
        "neuralRobustness",
        "neuralOutputRange",
        "neuralLipschitz",
        "neuralMonotonicity",
        "dataRace",
        "insufficientOrdering",
        "translationValidation",
        "floatDivByZero",
        "floatOverflowInf",
        "invalidDiscriminant",
        "aggregateArrayLengthMismatch",
        "unsafeOperation",
        "unknown",
    ] {
        env.add_decl(opaque(&format!("Trust.VcKind.{k}"), &[], &vckind, &nat_zero))?;
    }

    // Opaque formula/term formers (translate_formula). One carrier: Prop.
    // Bool-sorted variables sit directly under And/Or/Not in the canonical
    // translation, so the term carrier MUST be (definitionally) Prop; the
    // opacity of every former is what keeps that carrier non-degenerate.
    let p2 = [prop.clone(), prop.clone()];
    let p3 = [prop.clone(), prop.clone(), prop.clone()];
    let p2n = [prop.clone(), prop.clone(), nat.clone()];
    let p1n = [prop.clone(), nat.clone()];
    for (nm, args) in [
        ("var", &[string.clone(), tsort.clone()] as &[LeanExpr]),
        ("int", &[nat.clone()]),
        ("bitvec", &[nat.clone(), nat.clone()]),
        ("add", &p2),
        ("sub", &p2),
        ("mul", &p2),
        ("div", &p2),
        ("rem", &p2),
        ("neg", &[prop.clone()]),
        ("lt", &p2),
        ("le", &p2),
        ("gt", &p2),
        ("ge", &p2),
        ("bvAdd", &p2n),
        ("bvSub", &p2n),
        ("bvMul", &p2n),
        ("bvUDiv", &p2n),
        ("bvSDiv", &p2n),
        ("bvURem", &p2n),
        ("bvSRem", &p2n),
        ("bvAnd", &p2n),
        ("bvOr", &p2n),
        ("bvXor", &p2n),
        ("bvShl", &p2n),
        ("bvLShr", &p2n),
        ("bvAShr", &p2n),
        ("bvULt", &p2n),
        ("bvULe", &p2n),
        ("bvSLt", &p2n),
        ("bvSLe", &p2n),
        ("bvNot", &p1n),
        ("bvToInt", &[prop.clone(), nat.clone(), bool_ty.clone()]),
        ("intToBv", &p1n),
        ("bvExtract", &[prop.clone(), nat.clone(), nat.clone()]),
        ("bvConcat", &p2),
        ("bvZeroExt", &p1n),
        ("bvSignExt", &p1n),
        ("ite", &p3),
        ("forall", &[string.clone(), tsort.clone(), prop.clone()]),
        ("exists", &[string.clone(), tsort.clone(), prop.clone()]),
        ("select", &p2),
        ("store", &p3),
    ] {
        env.add_decl(opaque(&format!("Trust.Formula.{nm}"), args, &prop, &true_c))?;
    }

    // Trust.Formula.eq : Prop → Prop → Prop := fun a b => @Eq Prop a b
    // (REDUCIBLE — the EUF refutations rewrite through it).
    let eq1 = LeanExpr::const_(name("Eq"), vec![LeanLevel::succ(LeanLevel::zero())]);
    env.add_decl(Declaration::Definition {
        name: name("Trust.Formula.eq"),
        level_params: vec![],
        type_: arrows(&p2, &prop),
        value: LeanExpr::lam(
            BinderInfo::Default,
            prop.clone(),
            LeanExpr::lam(
                BinderInfo::Default,
                prop.clone(),
                LeanExpr::apps(eq1, [prop.clone(), LeanExpr::bvar(1), LeanExpr::bvar(0)]),
            ),
        ),
        is_reducible: true,
    })?;

    // Trust.Formula.implies : Prop → Prop → Prop := fun a b => a → b
    env.add_decl(Declaration::Definition {
        name: name("Trust.Formula.implies"),
        level_params: vec![],
        type_: arrows(&p2, &prop),
        value: LeanExpr::lam(
            BinderInfo::Default,
            prop.clone(),
            LeanExpr::lam(
                BinderInfo::Default,
                prop.clone(),
                LeanExpr::pi(BinderInfo::Default, LeanExpr::bvar(1), LeanExpr::bvar(1)),
            ),
        ),
        is_reducible: true,
    })?;

    // Trust.VC.holds : Trust.VcKind → Prop → Prop := fun _ p => ¬p
    // THE canonical replay identity: the VC holds iff its violation formula
    // is refutable.
    env.add_decl(Declaration::Definition {
        name: name("Trust.VC.holds"),
        level_params: vec![],
        type_: arrows(&[vckind.clone(), prop.clone()], &prop),
        value: LeanExpr::lam(
            BinderInfo::Default,
            vckind,
            LeanExpr::lam(
                BinderInfo::Default,
                prop.clone(),
                LeanExpr::app(const_expr("Not"), LeanExpr::bvar(0)),
            ),
        ),
        is_reducible: true,
    })?;

    Ok(())
}

// ---------------------------------------------------------------------------
// Strict axiom-closure gate
// ---------------------------------------------------------------------------

/// Collect every `Const` name in `e`. Returns `false` (caller must FAIL
/// CLOSED) on any expression node outside the core fragment (free variables,
/// SProp/Squash/Cubical/ZFC mode extensions) — a closed core proof never
/// contains them, and auditing what they can smuggle is not this gate's job.
fn collect_core_consts(e: &LeanExpr, out: &mut Vec<LeanName>) -> bool {
    match e.kind() {
        ExprKind::BVar(_) | ExprKind::Sort(_) | ExprKind::Lit(_) => true,
        ExprKind::Const(n, _) => {
            out.push(n.clone());
            true
        }
        ExprKind::App(f, a) => collect_core_consts(f, out) && collect_core_consts(a, out),
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
            collect_core_consts(t, out) && collect_core_consts(b, out)
        }
        ExprKind::Let(_, t, v, b, _) => {
            collect_core_consts(t, out)
                && collect_core_consts(v, out)
                && collect_core_consts(b, out)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => collect_core_consts(inner, out),
        _ => false,
    }
}

/// STRICT transitive axiom-closure check: `true` iff every constant reachable
/// from `root` (through declaration types AND values) exists in `env` and none
/// is `ConstantKind::Axiom`.
///
/// This is deliberately STRICTER than the kernel's `axiom_deps` residue (which
/// whitelists the foundational axioms): the prelude ships `sorry.{u} : {α :
/// Sort u} → α` (and `trustedAy`/`trustedArith`) as axiom-kind constants, so
/// without this gate `sorry (Trust.VC.holds k f)` would be a one-node forged
/// certificate for ANY VC; and `propext` (+ choice) makes `@Eq Prop`
/// classically degenerate, which would let a foreign proof falsely certify
/// satisfiable disequality patterns. A `Certified` verdict must carry a
/// ZERO-axiom kernel proof — no exceptions, no whitelist.
fn proof_is_axiom_free(env: &Environment, root: &LeanExpr) -> bool {
    let mut work: Vec<LeanName> = Vec::new();
    if !collect_core_consts(root, &mut work) {
        return false;
    }
    let mut seen: std::collections::HashSet<LeanName> = std::collections::HashSet::new();
    while let Some(n) = work.pop() {
        if !seen.insert(n.clone()) {
            continue;
        }
        let Some(info) = env.get_const(&n) else {
            return false;
        };
        if info.kind == ConstantKind::Axiom {
            return false;
        }
        if !collect_core_consts(&info.type_, &mut work) {
            return false;
        }
        if let Some(value) = &info.value {
            if !collect_core_consts(value, &mut work) {
                return false;
            }
        }
    }
    true
}

/// The shared 4-step + closure kernel gate every fast-path constructor runs
/// before emitting certificate bytes: direct check, certified inference +
/// def-eq against the CANONICAL theorem, full replay re-verification, and the
/// strict axiom-closure check. Any failure returns `None` (fail-closed).
fn kernel_gate_and_serialize(
    env: &Environment,
    proof: &LeanExpr,
    theorem: &LeanExpr,
) -> Option<Vec<u8>> {
    let tc = TypeChecker::new(env);
    tc.check_type(proof, theorem).ok()?;

    let (inferred_type, proof_cert) = tc.infer_type_with_cert(proof).ok()?;
    if !tc.is_def_eq(&inferred_type, theorem) {
        return None;
    }

    let mut verifier = CertVerifier::new(env);
    let (replayed_expr, replayed_type) = verifier.replay_and_verify(&proof_cert).ok()?;
    if !tc.is_def_eq(&replayed_type, theorem) {
        return None;
    }
    tc.check_type(&replayed_expr, theorem).ok()?;
    if !proof_is_axiom_free(env, &replayed_expr) {
        return None;
    }

    serialize_proof_cert(&proof_cert).ok()
}

/// Construct a clean Name from a dotted string.
fn name(s: &str) -> LeanName {
    LeanName::from_string(s)
}

/// Construct a clean constant expression (zero universe levels).
fn const_expr(s: &str) -> LeanExpr {
    LeanExpr::const_(name(s), Vec::<LeanLevel>::new())
}

// ---------------------------------------------------------------------------
// Genuine kernel certification (direct-contradiction fragment)
// ---------------------------------------------------------------------------

/// True iff `formula` is structurally a DIRECT CONTRADICTION: `And [X, Not X]`
/// (in either order). Such a violation is unsatisfiable by the universal
/// tautology `∀ P, (And P (Not P)) → False`.
fn is_direct_contradiction(formula: &Formula) -> bool {
    let Formula::And(children) = formula else { return false };
    if children.len() != 2 {
        return false;
    }
    let neg_of = |notx: &Formula, x: &Formula| matches!(notx, Formula::Not(inner) if **inner == *x);
    neg_of(&children[0], &children[1]) || neg_of(&children[1], &children[0])
}

/// Build the genuine, closed, axiom-free clean CIC proof term and theorem for
/// `∀ (P : Prop), (And P (Not P)) → False`, over ONLY prelude constants. This is
/// the universal refutation that subsumes any direct-contradiction violation.
/// (Mirrors the kernel test `trust_kernel_certified.rs`.) Retained as the
/// memo-env regression fixture; the production constructor now proves the
/// CANONICAL instance directly (see `kernel_certify_direct_contradiction`).
#[cfg(test)]
fn direct_contradiction_proof_and_theorem() -> (LeanExpr, LeanExpr) {
    let and_c = const_expr("And");
    let not_c = const_expr("Not");
    let false_c = || const_expr("False");
    let and_left = const_expr("And.left");
    let and_right = const_expr("And.right");
    let prop = LeanExpr::prop();

    // `And P (Not P)` with the Prop var P at de Bruijn index `depth`.
    let and_p_not_p = |depth: u32| {
        let p = LeanExpr::bvar(depth);
        let not_p = LeanExpr::app(not_c.clone(), p.clone());
        LeanExpr::app(LeanExpr::app(and_c.clone(), p), not_p)
    };

    // ∀ (P : Prop), (And P (Not P)) → False
    let theorem =
        LeanExpr::pi(BinderInfo::Default, prop.clone(), LeanExpr::arrow(and_p_not_p(0), false_c()));

    // fun (P : Prop) (h : And P (Not P)) =>
    //   absurd P False (And.left P (Not P) h) (And.right P (Not P) h)
    // `absurd : {a:Prop} {b:Sort u} → a → ¬a → b` takes ¬a as an ARGUMENT rather
    // than applying it, so the cert replayer never has to unfold `Not P` into a Pi
    // in an application head (the pattern its earlier `(¬P) P` form tripped on).
    // P=bvar1, h=bvar0 in the body; `b := False : Prop` ⇒ `absurd.{0}`.
    let p1 = || LeanExpr::bvar(1);
    let not_p1 = || LeanExpr::app(not_c.clone(), p1());
    let h0 = || LeanExpr::bvar(0);
    let left = LeanExpr::app(LeanExpr::app(LeanExpr::app(and_left, p1()), not_p1()), h0()); // : P
    let right = LeanExpr::app(LeanExpr::app(LeanExpr::app(and_right, p1()), not_p1()), h0()); // : ¬P
    let absurd_c = LeanExpr::const_(name("absurd"), vec![LeanLevel::zero()]);
    let body = LeanExpr::apps(absurd_c, [p1(), false_c(), left, right]);
    let proof = LeanExpr::lam(
        BinderInfo::Default,
        prop.clone(),
        LeanExpr::lam(BinderInfo::Default, and_p_not_p(0), body),
    );

    (proof, theorem)
}

/// If `formula` is a direct contradiction `X ∧ ¬X`, have the clean CIC kernel
/// verify a proof of the CANONICAL VC theorem `Trust.VC.holds <kind>
/// <formula>` — which unfolds to `¬⟦formula⟧` — and return a serialized,
/// replay-verified [`ProofCert`]. `None` otherwise.
///
/// The proof is the direct-contradiction instance
/// `fun (h : And ⟦X⟧ (Not ⟦X⟧)) => absurd ⟦X⟧ False (And.left … h)
/// (And.right … h)` at the formula's OWN translated atom, so the statement the
/// kernel re-typechecks is exactly what `generate_certificate` replays against
/// — the fast path and the canonical verifier share one identity.
///
/// SOUND: the clean kernel is the sole authority. A non-contradiction formula,
/// a lossy translation (undeclared `Trust.Formula.unknown`), or any kernel
/// rejection returns `None` → the caller stays at its prior (SmtBacked/
/// Trusted) assurance. It is impossible to mint `Certified` here without a
/// genuine kernel acceptance of the canonical statement.
pub(crate) fn kernel_certify_direct_contradiction(
    kind: &VcKind,
    formula: &Formula,
) -> Option<Vec<u8>> {
    if !is_direct_contradiction(formula) {
        return None;
    }
    let Formula::And(children) = formula else { return None };
    // Which side is X and which is ¬X?
    let x_first = matches!(&children[1], Formula::Not(inner) if **inner == children[0]);
    let x = if x_first { &children[0] } else { &children[1] };
    let tx = translate_formula(x);
    let not_tx = LeanExpr::app(const_expr("Not"), tx.clone());
    let (first, second) =
        if x_first { (tx.clone(), not_tx.clone()) } else { (not_tx.clone(), tx.clone()) };
    // ⟦formula⟧ — identical to translate_formula(formula) by construction.
    let tf = LeanExpr::apps(const_expr("And"), [first.clone(), second.clone()]);

    let h = LeanExpr::bvar(0);
    let left = LeanExpr::apps(const_expr("And.left"), [first.clone(), second.clone(), h.clone()]);
    let right = LeanExpr::apps(const_expr("And.right"), [first, second, h]);
    let (hx, hnx) = if x_first { (left, right) } else { (right, left) };
    let absurd0 = LeanExpr::const_(name("absurd"), vec![LeanLevel::zero()]);
    let body = LeanExpr::apps(absurd0, [tx, const_expr("False"), hx, hnx]);
    let proof = LeanExpr::lam(BinderInfo::Default, tf, body);

    let theorem = translate_vc_to_clean_theorem(kind, formula);
    let env = certification_env()?;
    kernel_gate_and_serialize(&env, &proof, &theorem)
}

// ---------------------------------------------------------------------------
// Genuine kernel certification (general propositional fragment)
// ---------------------------------------------------------------------------

/// Max number of distinct propositional atoms we certify by exhaustive case
/// split. The proof term has `2^n` leaves, so this bounds both build time and
/// the kernel's checking work. Refutations needing more atoms fall through to
/// reconstruction (Trusted) rather than being certified here.
const MAX_PROP_VARS: usize = 16;

/// The propositional skeleton of a [`Formula`] OVER ITS CANONICAL TRANSLATION:
/// Boolean connectives kept (`Implies` structurally too, since
/// `Trust.Formula.implies` reduces to `→`), maximal non-connective subterms
/// abstracted to independent atoms. Each node caches `prop` — the clean
/// translation of the corresponding sub-formula, node-for-node identical to
/// [`translate_formula`] output — so proofs built from the skeleton inhabit
/// exactly the canonical statement.
///
/// A refutation of this skeleton (false under ALL assignments to the atoms) is
/// a SOUND refutation of the concrete formula, because the concrete formula is
/// one instance of the abstraction. It is intentionally INCOMPLETE: theory-
/// dependent refutations (e.g. `x>0 ∧ x<0`, whose atoms are independent here)
/// are NOT certified — they correctly fall through, never falsely Certified.
struct PropSkel {
    kind: PropSkelKind,
    /// Canonical clean translation of this sub-skeleton.
    prop: LeanExpr,
}

enum PropSkelKind {
    Const(bool),
    Atom(usize),
    Not(Box<PropSkel>),
    And(Box<PropSkel>, Box<PropSkel>),
    Or(Box<PropSkel>, Box<PropSkel>),
    Implies(Box<PropSkel>, Box<PropSkel>),
}

/// Extract the canonical propositional skeleton, interning distinct atoms (by
/// structural `Formula` equality) into `atoms` / their translations into
/// `atom_props`. The `prop` fields mirror `translate_formula` EXACTLY
/// (including `And([]) ≡ True`, `Or([]) ≡ False`, left-fold nesting).
fn canon_skeleton(
    formula: &Formula,
    atoms: &mut Vec<Formula>,
    atom_props: &mut Vec<LeanExpr>,
) -> PropSkel {
    let mk = |kind: PropSkelKind, prop: LeanExpr| PropSkel { kind, prop };
    match formula {
        Formula::Bool(b) => {
            mk(PropSkelKind::Const(*b), const_expr(if *b { "True" } else { "False" }))
        }
        Formula::Not(inner) => {
            let s = canon_skeleton(inner, atoms, atom_props);
            let prop = LeanExpr::app(const_expr("Not"), s.prop.clone());
            mk(PropSkelKind::Not(Box::new(s)), prop)
        }
        Formula::And(children) | Formula::Or(children) => {
            let is_and = matches!(formula, Formula::And(_));
            if children.is_empty() {
                return mk(
                    PropSkelKind::Const(is_and),
                    const_expr(if is_and { "True" } else { "False" }),
                );
            }
            let mut acc = canon_skeleton(&children[0], atoms, atom_props);
            for child in &children[1..] {
                let s = canon_skeleton(child, atoms, atom_props);
                let conn = if is_and { "And" } else { "Or" };
                let prop = LeanExpr::apps(const_expr(conn), [acc.prop.clone(), s.prop.clone()]);
                let kind = if is_and {
                    PropSkelKind::And(Box::new(acc), Box::new(s))
                } else {
                    PropSkelKind::Or(Box::new(acc), Box::new(s))
                };
                acc = mk(kind, prop);
            }
            acc
        }
        Formula::Implies(a, b) => {
            let sa = canon_skeleton(a, atoms, atom_props);
            let sb = canon_skeleton(b, atoms, atom_props);
            let prop = LeanExpr::apps(
                const_expr("Trust.Formula.implies"),
                [sa.prop.clone(), sb.prop.clone()],
            );
            mk(PropSkelKind::Implies(Box::new(sa), Box::new(sb)), prop)
        }
        // Maximal non-connective subterm → independent atom.
        atom => {
            let idx = atoms.iter().position(|a| a == atom).unwrap_or_else(|| {
                atoms.push(atom.clone());
                atom_props.push(translate_formula(atom));
                atoms.len() - 1
            });
            mk(PropSkelKind::Atom(idx), atom_props[idx].clone())
        }
    }
}

/// Truth value of the skeleton under the atom assignment `mask` (bit `i` =
/// atom `i` true).
fn eval_skel(s: &PropSkel, mask: u32) -> bool {
    match &s.kind {
        PropSkelKind::Const(b) => *b,
        PropSkelKind::Atom(i) => mask & (1u32 << i) != 0,
        PropSkelKind::Not(a) => !eval_skel(a, mask),
        PropSkelKind::And(a, b) => eval_skel(a, mask) && eval_skel(b, mask),
        PropSkelKind::Or(a, b) => eval_skel(a, mask) || eval_skel(b, mask),
        PropSkelKind::Implies(a, b) => !eval_skel(a, mask) || eval_skel(b, mask),
    }
}

/// Builds the constructive refutation `⟦formula⟧ → False` for an UNSAT
/// skeleton, entirely over the CONCRETE translated atoms (Props, not Bools) —
/// so its inferred type IS the canonical statement, up to unfolding
/// `Trust.VC.holds`/`Not`.
///
/// The construction is the Glivenko-style double-negation split: for each atom
/// `A_i`, the axiom-free tautology `¬¬(A_i ∨ ¬A_i)` is applied to a
/// continuation that `Or.rec`-splits on the disjunct; at each of the `2^n`
/// leaves every atom carries a literal hypothesis, and the structurally-false
/// skeleton is refuted by mutual recursion (`refute`/`prove`) over its shape.
/// Binder bookkeeping uses the same named-placeholder + `mk_lam` abstraction
/// technique as the EUF reconstruction below.
struct PropRefuter<'a> {
    atom_props: &'a [LeanExpr],
    /// Per-atom literal hypothesis in the current branch:
    /// `(true, h : A_i)` or `(false, h : ¬A_i)`.
    lits: Vec<Option<(bool, LeanExpr)>>,
    mask: u32,
    next_ph: usize,
}

impl PropRefuter<'_> {
    fn fresh(&mut self) -> (LeanName, LeanExpr) {
        let n = LeanName::from_string(&format!("__trust_vc_prop_{}", self.next_ph));
        self.next_ph += 1;
        let t = LeanExpr::const_(n.clone(), Vec::<LeanLevel>::new());
        (n, t)
    }

    /// `absurd.{0} a target ha hna` — refutation-by-contradiction with the
    /// negation passed as an ARGUMENT (never applied), the replayer-safe form.
    fn absurd(&self, target: LeanExpr, a: LeanExpr, ha: LeanExpr, hna: LeanExpr) -> LeanExpr {
        let absurd0 = LeanExpr::const_(name("absurd"), vec![LeanLevel::zero()]);
        LeanExpr::apps(absurd0, [a, target, ha, hna])
    }

    /// Proof of `False` from `h : ⟦s⟧`, defined when `eval(s) = false` under
    /// the current assignment. `None` on any inconsistency (fail-closed).
    fn refute(&mut self, s: &PropSkel, h: LeanExpr) -> Option<LeanExpr> {
        match &s.kind {
            PropSkelKind::Const(false) => Some(h),
            PropSkelKind::Const(true) => None,
            PropSkelKind::Atom(i) => {
                let (positive, term) = self.lits[*i].clone()?;
                if positive {
                    return None;
                }
                Some(self.absurd(const_expr("False"), s.prop.clone(), h, term))
            }
            PropSkelKind::Not(a) => {
                let pa = self.prove(a)?;
                Some(self.absurd(const_expr("False"), a.prop.clone(), pa, h))
            }
            PropSkelKind::And(a, b) => {
                if !eval_skel(a, self.mask) {
                    let ha =
                        LeanExpr::apps(const_expr("And.left"), [a.prop.clone(), b.prop.clone(), h]);
                    self.refute(a, ha)
                } else if !eval_skel(b, self.mask) {
                    let hb = LeanExpr::apps(
                        const_expr("And.right"),
                        [a.prop.clone(), b.prop.clone(), h],
                    );
                    self.refute(b, hb)
                } else {
                    None
                }
            }
            PropSkelKind::Or(a, b) => {
                let (na, ta) = self.fresh();
                let body_a = self.refute(a, ta)?;
                let minor_a = mk_lam(&na, a.prop.clone(), body_a);
                let (nb, tb) = self.fresh();
                let body_b = self.refute(b, tb)?;
                let minor_b = mk_lam(&nb, b.prop.clone(), body_b);
                let or_ty = LeanExpr::apps(const_expr("Or"), [a.prop.clone(), b.prop.clone()]);
                let motive = LeanExpr::lam(BinderInfo::Default, or_ty, const_expr("False"));
                Some(LeanExpr::apps(
                    const_expr("Or.rec"),
                    [a.prop.clone(), b.prop.clone(), motive, minor_a, minor_b, h],
                ))
            }
            PropSkelKind::Implies(a, b) => {
                // eval(a) = true, eval(b) = false: modus ponens, then refute b.
                let pa = self.prove(a)?;
                self.refute(b, LeanExpr::app(h, pa))
            }
        }
    }

    /// Proof of `⟦s⟧`, defined when `eval(s) = true` under the current
    /// assignment.
    fn prove(&mut self, s: &PropSkel) -> Option<LeanExpr> {
        match &s.kind {
            PropSkelKind::Const(true) => Some(const_expr("True.intro")),
            PropSkelKind::Const(false) => None,
            PropSkelKind::Atom(i) => {
                let (positive, term) = self.lits[*i].clone()?;
                if positive { Some(term) } else { None }
            }
            PropSkelKind::Not(a) => {
                let (n, t) = self.fresh();
                let body = self.refute(a, t)?;
                Some(mk_lam(&n, a.prop.clone(), body))
            }
            PropSkelKind::And(a, b) => {
                let pa = self.prove(a)?;
                let pb = self.prove(b)?;
                Some(LeanExpr::apps(
                    const_expr("And.intro"),
                    [a.prop.clone(), b.prop.clone(), pa, pb],
                ))
            }
            PropSkelKind::Or(a, b) => {
                if eval_skel(a, self.mask) {
                    let pa = self.prove(a)?;
                    Some(LeanExpr::apps(const_expr("Or.inl"), [a.prop.clone(), b.prop.clone(), pa]))
                } else {
                    let pb = self.prove(b)?;
                    Some(LeanExpr::apps(const_expr("Or.inr"), [a.prop.clone(), b.prop.clone(), pb]))
                }
            }
            PropSkelKind::Implies(a, b) => {
                let (n, t) = self.fresh();
                if eval_skel(b, self.mask) {
                    let pb = self.prove(b)?;
                    Some(mk_lam(&n, a.prop.clone(), pb))
                } else {
                    // eval(a) = false: from h : ⟦a⟧, absurd into ⟦b⟧.
                    let (n2, t2) = self.fresh();
                    let refuted = self.refute(a, t2)?;
                    let neg = mk_lam(&n2, a.prop.clone(), refuted);
                    let body = self.absurd(b.prop.clone(), a.prop.clone(), t, neg);
                    Some(mk_lam(&n, a.prop.clone(), body))
                }
            }
        }
    }

    /// The double-negation case split over atoms `i..n`; every leaf refutes
    /// `root` from `h_root : ⟦root⟧` under a total literal assignment.
    fn split(&mut self, i: usize, root: &PropSkel, h_root: &LeanExpr) -> Option<LeanExpr> {
        if i == self.atom_props.len() {
            return self.refute(root, h_root.clone());
        }
        let ai = self.atom_props[i].clone();
        let not_ai = LeanExpr::app(const_expr("Not"), ai.clone());
        let or_ty = LeanExpr::apps(const_expr("Or"), [ai.clone(), not_ai.clone()]);

        // Minors of the case split.
        let (pn, pt) = self.fresh();
        self.lits[i] = Some((true, pt));
        self.mask |= 1u32 << i;
        let pos_body = self.split(i + 1, root, h_root)?;
        let minor_pos = mk_lam(&pn, ai.clone(), pos_body);

        let (nn, nt) = self.fresh();
        self.lits[i] = Some((false, nt));
        self.mask &= !(1u32 << i);
        let neg_body = self.split(i + 1, root, h_root)?;
        let minor_neg = mk_lam(&nn, not_ai.clone(), neg_body);
        self.lits[i] = None;

        // Continuation: fun (c : A_i ∨ ¬A_i) => Or.rec … c
        let (cn, ct) = self.fresh();
        let motive = LeanExpr::lam(BinderInfo::Default, or_ty.clone(), const_expr("False"));
        let case_split = LeanExpr::apps(
            const_expr("Or.rec"),
            [ai.clone(), not_ai.clone(), motive, minor_pos, minor_neg, ct],
        );
        let cont = mk_lam(&cn, or_ty.clone(), case_split);

        // The axiom-free tautology ¬¬(A_i ∨ ¬A_i), applied to the continuation:
        // fun (k : ¬(A_i ∨ ¬A_i)) =>
        //   absurd (Or.inr (fun (a : A_i) => absurd (Or.inl a) k)) k
        let (kn, kt) = self.fresh();
        let (an, at) = self.fresh();
        let inl = LeanExpr::apps(const_expr("Or.inl"), [ai.clone(), not_ai.clone(), at]);
        let inner = self.absurd(const_expr("False"), or_ty.clone(), inl, kt.clone());
        let inr_arg = mk_lam(&an, ai.clone(), inner);
        let inr = LeanExpr::apps(const_expr("Or.inr"), [ai, not_ai, inr_arg]);
        let outer = self.absurd(const_expr("False"), or_ty.clone(), inr, kt);
        let nnem = mk_lam(&kn, LeanExpr::app(const_expr("Not"), or_ty), outer);
        Some(LeanExpr::app(nnem, cont))
    }
}

/// If `formula`'s propositional skeleton is UNSAT (false under every
/// assignment to its atoms), have the clean CIC kernel verify a constructive
/// proof of the CANONICAL VC theorem `Trust.VC.holds <kind> <formula>`
/// (≡ `¬⟦formula⟧`) and return a serialized, replay-verified [`ProofCert`].
/// `None` otherwise.
///
/// This GENERALISES [`kernel_certify_direct_contradiction`] to ANY
/// propositional refutation (multi-clause resolution, arbitrary And/Or/Not/
/// Implies): the skeleton being classically UNSAT makes `¬⟦formula⟧`
/// intuitionistically provable (Glivenko), and the proof is built explicitly
/// via the `¬¬(A ∨ ¬A)` double-negation split — no classical axiom, no
/// `Decidable` instance, no Bool reflection.
///
/// SOUND + fail-closed: a SAT skeleton returns `None` before any kernel work;
/// theory-dependent refutations (atoms that are really dependent predicates)
/// are propositionally SAT here and correctly decline; lossy translations
/// (`Trust.Formula.unknown`) are rejected by the kernel because the constant
/// is deliberately undeclared. Bounded by [`MAX_PROP_VARS`] atoms.
pub(crate) fn kernel_certify_propositional(kind: &VcKind, formula: &Formula) -> Option<Vec<u8>> {
    let mut atoms = Vec::new();
    let mut atom_props = Vec::new();
    let root = canon_skeleton(formula, &mut atoms, &mut atom_props);
    let n = atoms.len();
    if n > MAX_PROP_VARS {
        return None;
    }
    // Sound abstraction gate: certify ONLY if the skeleton is false under
    // EVERY assignment. (The kernel would reject a bad proof anyway; this
    // keeps the decline path cheap and explicit.)
    if (0..(1u32 << n)).any(|mask| eval_skel(&root, mask)) {
        return None;
    }

    let mut builder =
        PropRefuter { atom_props: &atom_props, lits: vec![None; n], mask: 0, next_ph: 0 };
    let (hn, ht) = builder.fresh();
    let body = builder.split(0, &root, &ht)?;
    let proof = mk_lam(&hn, root.prop.clone(), body);

    let theorem = translate_vc_to_clean_theorem(kind, formula);
    let env = certification_env()?;
    kernel_gate_and_serialize(&env, &proof, &theorem)
}

// ---------------------------------------------------------------------------
// Genuine kernel certification (EUF — equality fragment)
// ---------------------------------------------------------------------------
//
// Certifies refutations that close by EQUALITY reasoning (transitivity +
// symmetry over an equality graph), e.g. `a=b ∧ b=c ∧ ¬(a=c)`. The
// propositional path cannot see this (it treats `a=b`, `b=c`, `a=c` as
// independent Bool atoms, propositionally SAT). We treat each maximal term as
// an opaque element of a universally-quantified carrier `T : Type`, take the
// formula's equality literals as hypotheses, and — when a disequality's two
// sides are connected in the equality graph — emit a closed CIC term
// `fun T (terms…) (eq-hyps…) (diseq-hyp) => diseq-hyp (Eq.trans/Eq.symm chain)`
// of type `… → False`. The clean kernel checks it; soundness reduces to the
// kernel. This is congruence-FREE (no `f(a)=f(b)` from `a=b`) — sound but
// incomplete; theory-dependent and congruence-only refutations decline.

/// Locally-nameless binder construction over sentinel-`Const` placeholders.
/// `mk_pi`/`mk_lam` abstract a named placeholder out of `inner` (→ `bvar(0)`,
/// shifting under nested binders) so multi-binder telescopes can be built
/// inside-out without hand-computing de Bruijn indices. Only the variants we
/// actually construct are traversed; anything else is returned unchanged (it
/// never carries a placeholder).
fn euf_ph_name(id: usize) -> LeanName {
    LeanName::from_string(&format!("__euf_fv_{id}"))
}

fn euf_ph(id: usize) -> LeanExpr {
    LeanExpr::const_(euf_ph_name(id), Vec::<LeanLevel>::new())
}

fn abstract_ph(e: &LeanExpr, ph: &LeanName, depth: u32) -> LeanExpr {
    match e.kind() {
        ExprKind::Const(n, _) if n == ph => LeanExpr::bvar(depth),
        ExprKind::App(f, a) => LeanExpr::app(abstract_ph(f, ph, depth), abstract_ph(a, ph, depth)),
        ExprKind::Lam(_, ty, body) => LeanExpr::lam(
            BinderInfo::Default,
            abstract_ph(ty, ph, depth),
            abstract_ph(body, ph, depth + 1),
        ),
        ExprKind::Pi(_, ty, body) => LeanExpr::pi(
            BinderInfo::Default,
            abstract_ph(ty, ph, depth),
            abstract_ph(body, ph, depth + 1),
        ),
        _ => e.clone(),
    }
}

fn mk_pi(ph: &LeanName, dom: LeanExpr, inner: LeanExpr) -> LeanExpr {
    LeanExpr::pi(BinderInfo::Default, dom, abstract_ph(&inner, ph, 0))
}

fn mk_lam(ph: &LeanName, dom: LeanExpr, inner: LeanExpr) -> LeanExpr {
    LeanExpr::lam(BinderInfo::Default, dom, abstract_ph(&inner, ph, 0))
}

/// `@Eq.{1} carrier lhs rhs`.
fn euf_eq(carrier: &LeanExpr, lhs: &LeanExpr, rhs: &LeanExpr) -> LeanExpr {
    let eq1 = LeanExpr::const_(name("Eq"), vec![LeanLevel::succ(LeanLevel::zero())]);
    LeanExpr::apps(eq1, vec![carrier.clone(), lhs.clone(), rhs.clone()])
}

/// Max distinct DAG nodes / reconstruction depth — bounds build + kernel work.
/// Exceeding either declines (fail-closed), like `MAX_PROP_VARS`.
const MAX_EUF_NODES: usize = 256;
const MAX_EUF_DEPTH: u32 = 64;

/// A node in the EUF term DAG. Interning is by FULL structural `Formula`
/// equality (injective by construction — distinct Trust terms get distinct
/// NodeIds), which is the load-bearing defense against false-Certify by
/// encoding-collapse: the clean kernel cannot see the original Formula, so the
/// ONLY guarantee that a hypothesis binder faithfully equals its claimed literal
/// is that `enc` is injective on distinct terms.
#[derive(Clone)]
enum EufNode {
    /// Opaque element of the carrier T.
    Leaf,
    /// `f_op` applied to child nodes; `f_op` is an uninterpreted function symbol.
    App(usize, Vec<usize>),
}

/// Best-effort result sort of a Formula. Folded into the function-symbol key so
/// sort-POLYMORPHIC operators (Select/Store/Ite/BvConcat) over different sorts
/// never share a symbol — defense in depth against conflating two genuinely
/// different functions (the multi-sort hole). `None` only loses completeness.
fn euf_infer_sort(t: &Formula) -> Option<Sort> {
    match t {
        Formula::Bool(_) => Some(Sort::Bool),
        Formula::Int(_) | Formula::UInt(_) => Some(Sort::Int),
        Formula::BitVec { width, .. } => Some(Sort::BitVec(*width)),
        Formula::Var(_, s) | Formula::SymVar(_, s) => Some(s.clone()),
        Formula::Add(..)
        | Formula::Sub(..)
        | Formula::Mul(..)
        | Formula::Div(..)
        | Formula::Rem(..)
        | Formula::Neg(_)
        | Formula::BvToInt(..) => Some(Sort::Int),
        Formula::BvAdd(_, _, w)
        | Formula::BvSub(_, _, w)
        | Formula::BvMul(_, _, w)
        | Formula::BvUDiv(_, _, w)
        | Formula::BvSDiv(_, _, w)
        | Formula::BvURem(_, _, w)
        | Formula::BvSRem(_, _, w)
        | Formula::BvAnd(_, _, w)
        | Formula::BvOr(_, _, w)
        | Formula::BvXor(_, _, w)
        | Formula::BvShl(_, _, w)
        | Formula::BvLShr(_, _, w)
        | Formula::BvAShr(_, _, w)
        | Formula::BvNot(_, w) => Some(Sort::BitVec(*w)),
        Formula::IntToBv(_, w) | Formula::BvZeroExt(_, w) | Formula::BvSignExt(_, w) => {
            Some(Sort::BitVec(*w))
        }
        Formula::BvExtract { high, low, .. } => Some(Sort::BitVec(high - low + 1)),
        Formula::BvConcat(a, b) => match (euf_infer_sort(a), euf_infer_sort(b)) {
            (Some(Sort::BitVec(wa)), Some(Sort::BitVec(wb))) => Some(Sort::BitVec(wa + wb)),
            _ => None,
        },
        Formula::Select(arr, _) => match euf_infer_sort(arr) {
            Some(Sort::Array(_, e)) => Some(*e),
            _ => None,
        },
        Formula::Store(arr, _, _) => euf_infer_sort(arr),
        Formula::Ite(_, then_, _) => euf_infer_sort(then_),
        _ => None,
    }
}

/// If `t` is a congruence-modeled APPLICATION, return its function-symbol key
/// (operator + ALL semantics-bearing payload + arity + result sort); `None` ⇒
/// treat `t` as an opaque Leaf. CONSERVATIVE keying: two app nodes share a
/// function symbol IFF this key matches — under-keying (conflating two real
/// functions) is the only unsound move, so every distinguishing attribute is
/// folded in; over-keying merely loses completeness.
fn euf_fsym_key(t: &Formula) -> Option<String> {
    let arity = t.children().len();
    if arity == 0 {
        return None;
    }
    let op = match t {
        Formula::Neg(_) => "neg".to_string(),
        Formula::Add(..) => "add".to_string(),
        Formula::Sub(..) => "sub".to_string(),
        Formula::Mul(..) => "mul".to_string(),
        Formula::Div(..) => "div".to_string(),
        Formula::Rem(..) => "rem".to_string(),
        Formula::Select(..) => "select".to_string(),
        Formula::Store(..) => "store".to_string(),
        Formula::Ite(..) => "ite".to_string(),
        Formula::BvConcat(..) => "bvconcat".to_string(),
        Formula::BvAdd(_, _, w) => format!("bvadd:{w}"),
        Formula::BvSub(_, _, w) => format!("bvsub:{w}"),
        Formula::BvMul(_, _, w) => format!("bvmul:{w}"),
        Formula::BvUDiv(_, _, w) => format!("bvudiv:{w}"),
        Formula::BvSDiv(_, _, w) => format!("bvsdiv:{w}"),
        Formula::BvURem(_, _, w) => format!("bvurem:{w}"),
        Formula::BvSRem(_, _, w) => format!("bvsrem:{w}"),
        Formula::BvAnd(_, _, w) => format!("bvand:{w}"),
        Formula::BvOr(_, _, w) => format!("bvor:{w}"),
        Formula::BvXor(_, _, w) => format!("bvxor:{w}"),
        Formula::BvShl(_, _, w) => format!("bvshl:{w}"),
        Formula::BvLShr(_, _, w) => format!("bvlshr:{w}"),
        Formula::BvAShr(_, _, w) => format!("bvashr:{w}"),
        Formula::BvNot(_, w) => format!("bvnot:{w}"),
        Formula::BvZeroExt(_, w) => format!("bvzext:{w}"),
        Formula::BvSignExt(_, w) => format!("bvsext:{w}"),
        Formula::BvExtract { high, low, .. } => format!("bvextract:{high}:{low}"),
        Formula::BvToInt(_, w, signed) => format!("bvtoint:{w}:{signed}"),
        Formula::IntToBv(_, w) => format!("inttobv:{w}"),
        Formula::Pred(sym, args) => format!("pred:{sym:?}:{}", args.len()),
        // Bool-/Prop-valued or unmodeled operators → opaque leaf.
        _ => return None,
    };
    Some(format!("{op}|a{arity}|{:?}", euf_infer_sort(t)))
}

/// A justified edge of the proof forest (the actual merges, undirected).
struct EufEdge {
    u: usize,
    v: usize,
    justif: EufJustif,
}

enum EufJustif {
    /// Input equality literal `pos[idx]` (oriented `(pos[idx].0, pos[idx].1)`).
    Lit(usize),
    /// Congruence: `u`, `v` are app nodes with the same fsym whose argument
    /// classes all coincided at merge time.
    Cong,
}

/// EUF engine: term DAG + proof-producing congruence closure + CIC reconstruction.
struct Euf {
    formulas: Vec<Formula>,
    nodes: Vec<EufNode>,
    fsym_keys: Vec<String>,
    fsym_arity: Vec<usize>,
    /// Representative formula per function symbol — the first App node interned
    /// with that key. Used to build the CONCRETE instantiation lambda for the
    /// symbol's binder in the abstract refutation (all same-key nodes share the
    /// operator + literal payload by construction of `euf_fsym_key`).
    fsym_rep: Vec<Formula>,
    pos: Vec<(usize, usize)>,
    // union-find
    parent: Vec<usize>,
    rank: Vec<usize>,
    // proof forest
    edges: Vec<EufEdge>,
    adj: Vec<Vec<usize>>,
    // reconstruction state
    enc_memo: Vec<Option<LeanExpr>>,
    pe_memo: std::collections::HashMap<(usize, usize), LeanExpr>,
    // cached kernel constants
    carrier: LeanExpr,
    type0: LeanExpr,
    eq_trans: LeanExpr,
    eq_symm: LeanExpr,
    congr_arg: LeanExpr,
    congr: LeanExpr,
    rfl: LeanExpr,
    not_c: LeanExpr,
}

impl Euf {
    fn new() -> Self {
        let lvl1 = LeanLevel::succ(LeanLevel::zero());
        Euf {
            formulas: Vec::new(),
            nodes: Vec::new(),
            fsym_keys: Vec::new(),
            fsym_arity: Vec::new(),
            fsym_rep: Vec::new(),
            pos: Vec::new(),
            parent: Vec::new(),
            rank: Vec::new(),
            edges: Vec::new(),
            adj: Vec::new(),
            enc_memo: Vec::new(),
            pe_memo: std::collections::HashMap::new(),
            carrier: euf_ph(0),
            type0: LeanExpr::sort(LeanLevel::succ(LeanLevel::zero())),
            eq_trans: LeanExpr::const_(name("Eq.trans"), vec![lvl1.clone()]),
            eq_symm: LeanExpr::const_(name("Eq.symm"), vec![lvl1.clone()]),
            congr_arg: LeanExpr::const_(name("congrArg"), vec![lvl1.clone(), lvl1.clone()]),
            congr: LeanExpr::const_(name("congr"), vec![lvl1.clone(), lvl1.clone()]),
            rfl: LeanExpr::const_(name("rfl"), vec![lvl1.clone()]),
            not_c: const_expr("Not"),
        }
    }

    /// Intern a Formula into the DAG (recursing children first). Injective on
    /// distinct Formulas. `None` if the node budget is exceeded.
    fn intern(&mut self, t: &Formula) -> Option<usize> {
        if let Some(i) = self.formulas.iter().position(|f| f == t) {
            return Some(i);
        }
        let node = match euf_fsym_key(t) {
            Some(key) => {
                let children: Vec<usize> =
                    t.children().iter().map(|c| self.intern(c)).collect::<Option<Vec<_>>>()?;
                let fsym = self.fsym_id(&key, children.len(), t);
                EufNode::App(fsym, children)
            }
            None => EufNode::Leaf,
        };
        if self.formulas.len() >= MAX_EUF_NODES {
            return None;
        }
        let id = self.formulas.len();
        self.formulas.push(t.clone());
        self.nodes.push(node);
        self.parent.push(id);
        self.rank.push(0);
        self.adj.push(Vec::new());
        self.enc_memo.push(None);
        Some(id)
    }

    fn fsym_id(&mut self, key: &str, arity: usize, rep: &Formula) -> usize {
        if let Some(i) = self.fsym_keys.iter().position(|k| k == key) {
            i
        } else {
            self.fsym_keys.push(key.to_string());
            self.fsym_arity.push(arity);
            self.fsym_rep.push(rep.clone());
            self.fsym_keys.len() - 1
        }
    }

    fn find(&mut self, x: usize) -> usize {
        let mut r = x;
        while self.parent[r] != r {
            r = self.parent[r];
        }
        // path compression
        let mut c = x;
        while self.parent[c] != r {
            let nxt = self.parent[c];
            self.parent[c] = r;
            c = nxt;
        }
        r
    }

    /// Union `x`,`y` AND record an undirected proof-forest edge (no-op if equal).
    fn merge(&mut self, x: usize, y: usize, justif: EufJustif) {
        let rx = self.find(x);
        let ry = self.find(y);
        if rx == ry {
            return;
        }
        let eidx = self.edges.len();
        self.edges.push(EufEdge { u: x, v: y, justif });
        self.adj[x].push(eidx);
        self.adj[y].push(eidx);
        if self.rank[rx] < self.rank[ry] {
            self.parent[rx] = ry;
        } else if self.rank[rx] > self.rank[ry] {
            self.parent[ry] = rx;
        } else {
            self.parent[ry] = rx;
            self.rank[rx] += 1;
        }
    }

    /// Proof-producing congruence closure to fixpoint.
    fn close(&mut self) {
        // seed with input equalities
        let seed: Vec<(usize, usize, usize)> =
            self.pos.iter().enumerate().map(|(ei, &(u, v))| (u, v, ei)).collect();
        for (u, v, ei) in seed {
            self.merge(u, v, EufJustif::Lit(ei));
        }
        // congruence fixpoint (naive; bounded by MAX_EUF_NODES)
        loop {
            let mut changed = false;
            let n = self.nodes.len();
            for a in 0..n {
                let EufNode::App(fa, args_a) = self.nodes[a].clone() else { continue };
                for b in (a + 1)..n {
                    let EufNode::App(fb, args_b) = self.nodes[b].clone() else { continue };
                    if fa != fb || args_a.len() != args_b.len() {
                        continue;
                    }
                    if self.find(a) == self.find(b) {
                        continue;
                    }
                    let all_eq =
                        args_a.iter().zip(&args_b).all(|(&x, &y)| self.find(x) == self.find(y));
                    if all_eq {
                        self.merge(a, b, EufJustif::Cong);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
    }

    // ---- id scheme (disjoint placeholder ranges) ----
    fn leaf_ph_id(&self, node: usize) -> usize {
        1 + node
    }
    fn fsym_ph_id(&self, f: usize) -> usize {
        1 + self.nodes.len() + f
    }
    fn hyp_ph_id(&self, i: usize) -> usize {
        1 + self.nodes.len() + self.fsym_keys.len() + i
    }
    fn diseq_ph_id(&self) -> usize {
        1 + self.nodes.len() + self.fsym_keys.len() + self.pos.len()
    }

    /// Encode a node as a carrier-typed CIC term (memoized): Leaf → element
    /// placeholder; App → curried application of the function-symbol placeholder.
    fn enc(&mut self, node: usize) -> LeanExpr {
        if let Some(e) = &self.enc_memo[node] {
            return e.clone();
        }
        let e = match self.nodes[node].clone() {
            EufNode::Leaf => euf_ph(self.leaf_ph_id(node)),
            EufNode::App(f, children) => {
                let mut acc = euf_ph(self.fsym_ph_id(f));
                for c in children {
                    let ce = self.enc(c);
                    acc = LeanExpr::app(acc, ce);
                }
                acc
            }
        };
        self.enc_memo[node] = Some(e.clone());
        e
    }

    /// Build T→…→T with `k` arrows (over the carrier placeholder).
    fn fn_ty(&self, k: usize) -> LeanExpr {
        let mut t = self.carrier.clone();
        for _ in 0..k {
            t = LeanExpr::pi(BinderInfo::Default, self.carrier.clone(), t);
        }
        t
    }

    /// BFS the proof forest from `x` to `y`; return ordered `(from, to, edge)` steps.
    fn forest_path(&self, x: usize, y: usize) -> Option<Vec<(usize, usize, usize)>> {
        use std::collections::VecDeque;
        let mut prev: Vec<Option<(usize, usize)>> = vec![None; self.nodes.len()];
        let mut visited = vec![false; self.nodes.len()];
        let mut queue = VecDeque::new();
        visited[x] = true;
        queue.push_back(x);
        while let Some(u) = queue.pop_front() {
            if u == y {
                break;
            }
            for &eidx in &self.adj[u] {
                let e = &self.edges[eidx];
                let other = if e.u == u { e.v } else { e.u };
                if !visited[other] {
                    visited[other] = true;
                    prev[other] = Some((u, eidx));
                    queue.push_back(other);
                }
            }
        }
        if !visited[y] {
            return None;
        }
        let mut steps = Vec::new();
        let mut cur = y;
        while cur != x {
            let (p, eidx) = prev[cur]?;
            steps.push((p, cur, eidx));
            cur = p;
        }
        steps.reverse();
        Some(steps)
    }

    /// Proof term of `@Eq T enc(x) enc(y)` (memoized). `None` on depth/closure gaps.
    fn prove_eq(&mut self, x: usize, y: usize, depth: u32) -> Option<LeanExpr> {
        if depth > MAX_EUF_DEPTH {
            return None;
        }
        if x == y {
            let ex = self.enc(x);
            return Some(LeanExpr::apps(self.rfl.clone(), vec![self.carrier.clone(), ex]));
        }
        if let Some(e) = self.pe_memo.get(&(x, y)) {
            return Some(e.clone());
        }
        let path = self.forest_path(x, y)?;
        // build step proofs : @Eq T enc(z_i) enc(z_{i+1})
        let mut steps: Vec<LeanExpr> = Vec::with_capacity(path.len());
        for &(from, to, eidx) in &path {
            steps.push(self.build_step(from, to, eidx, depth)?);
        }
        // chain with Eq.trans (left fold)
        let mut acc = steps[0].clone();
        for i in 1..path.len() {
            let z0 = self.enc(x);
            let zi = self.enc(path[i].0);
            let zi1 = self.enc(path[i].1);
            acc = LeanExpr::apps(
                self.eq_trans.clone(),
                vec![self.carrier.clone(), z0, zi, zi1, acc, steps[i].clone()],
            );
        }
        self.pe_memo.insert((x, y), acc.clone());
        Some(acc)
    }

    /// Proof of `@Eq T enc(from) enc(to)` for one proof-forest edge.
    fn build_step(&mut self, from: usize, _to: usize, eidx: usize, depth: u32) -> Option<LeanExpr> {
        let (eu, ev) = (self.edges[eidx].u, self.edges[eidx].v);
        // base : @Eq T enc(eu) enc(ev)
        let base = match &self.edges[eidx].justif {
            EufJustif::Lit(pos_idx) => euf_ph(self.hyp_ph_id(*pos_idx)),
            EufJustif::Cong => self.cong_proof(eu, ev, depth + 1)?,
        };
        if eu == from {
            Some(base)
        } else {
            // edge is (to, from): reorient with Eq.symm.
            let e_eu = self.enc(eu);
            let e_ev = self.enc(ev);
            Some(LeanExpr::apps(self.eq_symm.clone(), vec![self.carrier.clone(), e_eu, e_ev, base]))
        }
    }

    /// Congruence proof of `@Eq T enc(a) enc(b)` for same-fsym app nodes via the
    /// curried congrArg+congr spine, arg subproofs from `prove_eq` (recursion).
    fn cong_proof(&mut self, a: usize, b: usize, depth: u32) -> Option<LeanExpr> {
        let EufNode::App(fa, args_a) = self.nodes[a].clone() else { return None };
        let EufNode::App(fb, args_b) = self.nodes[b].clone() else { return None };
        if fa != fb || args_a.len() != args_b.len() || args_a.is_empty() {
            return None;
        }
        let f = euf_ph(self.fsym_ph_id(fa));
        let n = args_a.len();
        let ea0 = self.enc(args_a[0]);
        let eb0 = self.enc(args_b[0]);
        let p0 = self.prove_eq(args_a[0], args_b[0], depth)?;
        if n == 1 {
            return Some(LeanExpr::apps(
                self.congr_arg.clone(),
                vec![self.carrier.clone(), self.carrier.clone(), ea0, eb0, f, p0],
            ));
        }
        // n >= 2: lift arg0 via congrArg (β = the partial-application arrow type),
        // then peel each remaining arg via congr.
        let mut head1 = LeanExpr::app(f.clone(), ea0.clone());
        let mut head2 = LeanExpr::app(f.clone(), eb0.clone());
        let mut acc = LeanExpr::apps(
            self.congr_arg.clone(),
            vec![self.carrier.clone(), self.fn_ty(n - 1), ea0, eb0, f, p0],
        );
        for t in 1..n {
            let eat = self.enc(args_a[t]);
            let ebt = self.enc(args_b[t]);
            let pt = self.prove_eq(args_a[t], args_b[t], depth)?;
            acc = LeanExpr::apps(
                self.congr.clone(),
                vec![
                    self.carrier.clone(),
                    self.fn_ty(n - t - 1),
                    head1.clone(),
                    head2.clone(),
                    eat.clone(),
                    ebt.clone(),
                    acc,
                    pt,
                ],
            );
            head1 = LeanExpr::app(head1, eat);
            head2 = LeanExpr::app(head2, ebt);
        }
        Some(acc)
    }

    /// Build the closed proof term + theorem refuting disequality `(p, q)`.
    /// Binds the carrier, EVERY function symbol, EVERY leaf node, EVERY positive
    /// literal as a hypothesis, and the disequality — closed BY CONSTRUCTION (no
    /// "used-set" minimization, so no binder can be dropped). The body uses only
    /// a subset; unused ∀-binders are harmless. Returns `None` if `(p, q)` is not
    /// entailed or reconstruction hits the depth cap.
    fn build_refutation(&mut self, p: usize, q: usize) -> Option<(LeanExpr, LeanExpr)> {
        if self.find(p) != self.find(q) {
            return None;
        }
        let chain = self.prove_eq(p, q, 0)?; // @Eq T enc(p) enc(q)
        let body = LeanExpr::app(euf_ph(self.diseq_ph_id()), chain);

        // Precompute the encodings needed for binder TYPES.
        let n_nodes = self.nodes.len();
        let n_fsyms = self.fsym_keys.len();
        let n_pos = self.pos.len();
        let leaves: Vec<usize> =
            (0..n_nodes).filter(|&n| matches!(self.nodes[n], EufNode::Leaf)).collect();
        let hyp_types: Vec<LeanExpr> = (0..n_pos)
            .map(|i| {
                let (l, r) = self.pos[i];
                let el = self.enc(l);
                let er = self.enc(r);
                euf_eq(&self.carrier, &el, &er)
            })
            .collect();
        let ep = self.enc(p);
        let eq = self.enc(q);
        let diseq_type = LeanExpr::app(self.not_c.clone(), euf_eq(&self.carrier, &ep, &eq));
        let fn_tys: Vec<LeanExpr> = (0..n_fsyms).map(|f| self.fn_ty(self.fsym_arity[f])).collect();

        // Wrap inside-out: diseq, hyps(rev), leaves(rev), fsyms(rev), carrier.
        let mut proof = mk_lam(&euf_ph_name(self.diseq_ph_id()), diseq_type.clone(), body);
        let mut theorem = mk_pi(&euf_ph_name(self.diseq_ph_id()), diseq_type, const_expr("False"));
        for i in (0..n_pos).rev() {
            let id = self.hyp_ph_id(i);
            proof = mk_lam(&euf_ph_name(id), hyp_types[i].clone(), proof);
            theorem = mk_pi(&euf_ph_name(id), hyp_types[i].clone(), theorem);
        }
        for &leaf in leaves.iter().rev() {
            let id = self.leaf_ph_id(leaf);
            proof = mk_lam(&euf_ph_name(id), self.carrier.clone(), proof);
            theorem = mk_pi(&euf_ph_name(id), self.carrier.clone(), theorem);
        }
        for f in (0..n_fsyms).rev() {
            let id = self.fsym_ph_id(f);
            proof = mk_lam(&euf_ph_name(id), fn_tys[f].clone(), proof);
            theorem = mk_pi(&euf_ph_name(id), fn_tys[f].clone(), theorem);
        }
        proof = mk_lam(&euf_ph_name(0), self.type0.clone(), proof);
        theorem = mk_pi(&euf_ph_name(0), self.type0.clone(), theorem);

        Some((proof, theorem))
    }
}

/// Concrete instantiation lambda for a function symbol, from its
/// representative formula: `fun (x_1 … x_a : Prop) => <head> x… <literals>`,
/// where the DAG-children positions become binders (in `children()` order —
/// the order `enc` applies them) and every non-term payload (widths, extract
/// bounds, signedness) is baked in from the representative. Same-key nodes
/// share that payload by construction of [`euf_fsym_key`].
///
/// `None` for operators without a faithful canonical translation (`Pred` and
/// anything hitting the `Trust.Formula.unknown` arm) — the EUF path then
/// declines entirely (fail-closed).
fn euf_fsym_lambda(rep: &Formula) -> Option<LeanExpr> {
    let prop = LeanExpr::prop();
    let natl = |w: u32| LeanExpr::nat_lit(u64::from(w));
    let lam1 = |body: LeanExpr| LeanExpr::lam(BinderInfo::Default, prop.clone(), body);
    let lam2 = |body: LeanExpr| lam1(LeanExpr::lam(BinderInfo::Default, prop.clone(), body));
    let lam3 = |body: LeanExpr| lam2(LeanExpr::lam(BinderInfo::Default, prop.clone(), body));
    let b0 = LeanExpr::bvar(0);
    let b1 = LeanExpr::bvar(1);
    let b2 = LeanExpr::bvar(2);
    let un = |nm: &str| Some(lam1(LeanExpr::app(const_expr(nm), LeanExpr::bvar(0))));
    let bin = |nm: &str| Some(lam2(LeanExpr::apps(const_expr(nm), [b1.clone(), b0.clone()])));
    let tri =
        |nm: &str| Some(lam3(LeanExpr::apps(const_expr(nm), [b2.clone(), b1.clone(), b0.clone()])));
    let binw = |nm: &str, w: u32| {
        Some(lam2(LeanExpr::apps(const_expr(nm), [b1.clone(), b0.clone(), natl(w)])))
    };
    let unw = |nm: &str, w: u32| Some(lam1(LeanExpr::apps(const_expr(nm), [b0.clone(), natl(w)])));
    match rep {
        Formula::Neg(_) => un("Trust.Formula.neg"),
        Formula::Add(..) => bin("Trust.Formula.add"),
        Formula::Sub(..) => bin("Trust.Formula.sub"),
        Formula::Mul(..) => bin("Trust.Formula.mul"),
        Formula::Div(..) => bin("Trust.Formula.div"),
        Formula::Rem(..) => bin("Trust.Formula.rem"),
        Formula::Select(..) => bin("Trust.Formula.select"),
        Formula::Store(..) => tri("Trust.Formula.store"),
        Formula::Ite(..) => tri("Trust.Formula.ite"),
        Formula::BvConcat(..) => bin("Trust.Formula.bvConcat"),
        Formula::BvAdd(_, _, w) => binw("Trust.Formula.bvAdd", *w),
        Formula::BvSub(_, _, w) => binw("Trust.Formula.bvSub", *w),
        Formula::BvMul(_, _, w) => binw("Trust.Formula.bvMul", *w),
        Formula::BvUDiv(_, _, w) => binw("Trust.Formula.bvUDiv", *w),
        Formula::BvSDiv(_, _, w) => binw("Trust.Formula.bvSDiv", *w),
        Formula::BvURem(_, _, w) => binw("Trust.Formula.bvURem", *w),
        Formula::BvSRem(_, _, w) => binw("Trust.Formula.bvSRem", *w),
        Formula::BvAnd(_, _, w) => binw("Trust.Formula.bvAnd", *w),
        Formula::BvOr(_, _, w) => binw("Trust.Formula.bvOr", *w),
        Formula::BvXor(_, _, w) => binw("Trust.Formula.bvXor", *w),
        Formula::BvShl(_, _, w) => binw("Trust.Formula.bvShl", *w),
        Formula::BvLShr(_, _, w) => binw("Trust.Formula.bvLShr", *w),
        Formula::BvAShr(_, _, w) => binw("Trust.Formula.bvAShr", *w),
        Formula::BvNot(_, w) => unw("Trust.Formula.bvNot", *w),
        Formula::BvZeroExt(_, w) => unw("Trust.Formula.bvZeroExt", *w),
        Formula::BvSignExt(_, w) => unw("Trust.Formula.bvSignExt", *w),
        Formula::IntToBv(_, w) => unw("Trust.Formula.intToBv", *w),
        Formula::BvExtract { high, low, .. } => Some(lam1(LeanExpr::apps(
            const_expr("Trust.Formula.bvExtract"),
            [b0.clone(), natl(*high), natl(*low)],
        ))),
        Formula::BvToInt(_, w, signed) => Some(lam1(LeanExpr::apps(
            const_expr("Trust.Formula.bvToInt"),
            [b0, natl(*w), const_expr(if *signed { "Bool.true" } else { "Bool.false" })],
        ))),
        // Pred / unmodeled operators: no faithful spine — decline.
        _ => None,
    }
}

/// Left-fold conjunction translation of `cs` (non-empty) — the exact shape
/// `translate_formula` gives `Formula::And(cs)`.
fn euf_fold_translation(cs: &[Formula]) -> LeanExpr {
    let mut r = translate_formula(&cs[0]);
    for c in &cs[1..] {
        r = LeanExpr::apps(const_expr("And"), [r, translate_formula(c)]);
    }
    r
}

/// Collect the conjunct literals of `g` in `flatten` order, TOGETHER with a
/// kernel proof term for each, extracted from `h : ⟦g⟧` by `And.left`/
/// `And.right` chains that mirror the left-fold translation exactly.
fn euf_collect_conjuncts<'f>(g: &'f Formula, h: LeanExpr, out: &mut Vec<(&'f Formula, LeanExpr)>) {
    fn peel<'f>(cs: &'f [Formula], h: LeanExpr, out: &mut Vec<(&'f Formula, LeanExpr)>) {
        let m = cs.len();
        if m == 1 {
            euf_collect_conjuncts(&cs[0], h, out);
            return;
        }
        // ⟦cs⟧ = And ⟦cs[..m-1]⟧ ⟦cs[m-1]⟧
        let left_t = euf_fold_translation(&cs[..m - 1]);
        let right_t = translate_formula(&cs[m - 1]);
        let hl =
            LeanExpr::apps(const_expr("And.left"), [left_t.clone(), right_t.clone(), h.clone()]);
        let hr = LeanExpr::apps(const_expr("And.right"), [left_t, right_t, h]);
        peel(&cs[..m - 1], hl, out);
        euf_collect_conjuncts(&cs[m - 1], hr, out);
    }
    if let Formula::And(cs) = g {
        if cs.is_empty() {
            return;
        }
        peel(cs, h, out);
    } else {
        out.push((g, h));
    }
}

/// If `formula`'s equality literals refute one of its disequality literals —
/// by transitivity, symmetry, AND CONGRUENCE (`f(a)=f(b)` from `a=b`) — have the
/// clean CIC kernel verify a proof of the CANONICAL VC theorem
/// `Trust.VC.holds <kind> <formula>` (≡ `¬⟦formula⟧`) and return a serialized,
/// replay-verified [`ProofCert`]. `None` otherwise.
///
/// Construction: the closed abstract refutation from [`Euf::build_refutation`]
/// (`∀ T fsyms leaves eq-hyps diseq, False`) is APPLIED at the canonical
/// encoding — carrier `T := Prop`, each function symbol at its concrete
/// `Trust.Formula.*` spine (via [`euf_fsym_lambda`]), each leaf at its
/// `translate_formula` image, each equality hypothesis at the `And.left/right`
/// projection of `h : ⟦formula⟧` (whose type `Trust.Formula.eq ⟦l⟧ ⟦r⟧`
/// REDUCES to `@Eq Prop ⟦l⟧ ⟦r⟧`), and the disequality at its projection.
/// Under beta, the abstract encoding reduces to exactly the canonical
/// translation, so `fun (h : ⟦formula⟧) => refutation … : ¬⟦formula⟧`.
///
/// SOUND + incomplete + fail-closed: emits ONLY when a real congruence-closure
/// refutation exists AND the kernel ACCEPTS the canonical term. Interning is by
/// full structural `Formula` equality (injective — distinct terms never
/// collapse; the opaque `Trust.Formula.*` signature keeps the kernel-side
/// encoding equally collapse-free); hypothesis proofs are ONLY verbatim `Eq`
/// conjunct projections; derived equalities are proved (congrArg/congr/
/// Eq.trans/Eq.symm), never assumed. Theory-dependent refutations, lossy
/// translations, and anything the kernel rejects decline — never falsely
/// Certified.
pub(crate) fn kernel_certify_euf(kind: &VcKind, formula: &Formula) -> Option<Vec<u8>> {
    // Conjuncts + their extraction proofs from the single hypothesis
    // `h : ⟦formula⟧` (as a named placeholder, abstracted at the end).
    let h_name = LeanName::from_string("__trust_vc_hyp");
    let h_ph = LeanExpr::const_(h_name.clone(), Vec::<LeanLevel>::new());
    let mut conjuncts: Vec<(&Formula, LeanExpr)> = Vec::new();
    euf_collect_conjuncts(formula, h_ph, &mut conjuncts);

    let mut euf = Euf::new();
    let mut pos_proofs: Vec<LeanExpr> = Vec::new();
    let mut negs: Vec<(usize, usize, LeanExpr)> = Vec::new();
    for (c, h) in &conjuncts {
        match c {
            Formula::Eq(l, r) => {
                let li = euf.intern(l)?;
                let ri = euf.intern(r)?;
                if li != ri {
                    euf.pos.push((li, ri));
                    pos_proofs.push(h.clone());
                }
            }
            Formula::Not(inner) => {
                if let Formula::Eq(l, r) = &**inner {
                    let li = euf.intern(l)?;
                    let ri = euf.intern(r)?;
                    negs.push((li, ri, h.clone()));
                }
            }
            _ => {}
        }
    }
    if negs.is_empty() {
        return None;
    }

    euf.close();

    // Every fsym must have a faithful concrete spine (fail-closed otherwise —
    // the abstract refutation binds ALL of them).
    let fsym_lams: Vec<LeanExpr> =
        euf.fsym_rep.iter().map(euf_fsym_lambda).collect::<Option<Vec<_>>>()?;
    let tf = translate_formula(formula);
    let theorem = translate_vc_to_clean_theorem(kind, formula);
    let env = certification_env()?;

    for (p, q, hneg) in &negs {
        let Some((abstract_proof, _abstract_theorem)) = euf.build_refutation(*p, *q) else {
            continue;
        };
        let leaf_terms: Vec<LeanExpr> = (0..euf.nodes.len())
            .filter(|&i| matches!(euf.nodes[i], EufNode::Leaf))
            .map(|i| translate_formula(&euf.formulas[i]))
            .collect();
        // Application order mirrors build_refutation's binder order:
        // carrier, fsyms, leaves, eq-hyps, diseq.
        let mut args: Vec<LeanExpr> =
            Vec::with_capacity(1 + fsym_lams.len() + leaf_terms.len() + pos_proofs.len() + 1);
        args.push(LeanExpr::prop());
        args.extend(fsym_lams.iter().cloned());
        args.extend(leaf_terms);
        args.extend(pos_proofs.iter().cloned());
        args.push(hneg.clone());
        let body = LeanExpr::apps(abstract_proof, args);
        let proof = mk_lam(&h_name, tf.clone(), body);

        // THE kernel gate — the sole authority — against the CANONICAL theorem.
        if let Some(bytes) = kernel_gate_and_serialize(&env, &proof, &theorem) {
            return Some(bytes);
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Sort → clean Expr translation
// ---------------------------------------------------------------------------

/// Translate a Trust Sort into a clean type expression.
///
/// - `Sort::Bool`    → `Trust.Sort.Bool`
/// - `Sort::Int`     → `Trust.Sort.Int`
/// - `Sort::BitVec(w)` → `Trust.Sort.BitVec w`
/// - `Sort::Array(i,e)` → `Trust.Sort.Array <idx> <elem>`
pub(crate) fn translate_sort(sort: &Sort) -> LeanExpr {
    match sort {
        Sort::Bool => const_expr("Trust.Sort.Bool"),
        Sort::Int => const_expr("Trust.Sort.Int"),
        Sort::BitVec(w) => {
            LeanExpr::app(const_expr("Trust.Sort.BitVec"), LeanExpr::nat_lit(u64::from(*w)))
        }
        Sort::Array(idx, elem) => LeanExpr::apps(
            const_expr("Trust.Sort.Array"),
            vec![translate_sort(idx), translate_sort(elem)],
        ),
        _ => const_expr("Trust.Sort.Unknown"),
    }
}

// ---------------------------------------------------------------------------
// Formula → clean Expr translation
// ---------------------------------------------------------------------------

/// Translate a Trust Formula into a clean Prop expression.
///
/// The translation maps our first-order SMT-like formulas into clean
/// kernel terms that live in Prop. Each Formula variant maps to a
/// corresponding `Trust.Formula.*` constant applied to its operands.
///
/// This is the key bridge: the resulting Expr is the theorem statement
/// that a ProofCert must witness.
pub fn translate_formula(formula: &Formula) -> LeanExpr {
    match formula {
        // Literals
        Formula::Bool(true) => const_expr("True"),
        Formula::Bool(false) => const_expr("False"),
        // Trust: EXACT ENCODING (2026-07-24) — these were `nat_lit(n as u64)`, i.e.
        // `n mod 2^64`, a SILENT TRUNCATION that makes the map NON-INJECTIVE: two
        // formulas differing by a multiple of 2^64 translated to the SAME theorem.
        // That matters HERE because this is the theorem a `ProofCert` must witness
        // (`certificate.rs` → `translate_vc_to_clean_theorem` → `verify_proof_cert`),
        // so a cert for one VC could verify against a numerically different one. It is
        // the same defect class as the demonstrated `clean_ground::int_lit_to_expr`
        // false accept. `nat_lit_u128` is a drop-in — `BigNat::from_limbs` normalizes a
        // trailing zero limb back to `Small`, so every value that already worked
        // encodes byte-identically (pinned by `translate_formula_encodes_wide_literals_
        // distinctly`).
        Formula::Int(n) => {
            // Encode as Trust.Formula.int <nat>
            // For negative values, wrap in Trust.Formula.neg
            if *n >= 0 {
                LeanExpr::app(const_expr("Trust.Formula.int"), LeanExpr::nat_lit_u128(n.unsigned_abs()))
            } else {
                LeanExpr::app(
                    const_expr("Trust.Formula.neg"),
                    LeanExpr::app(
                        const_expr("Trust.Formula.int"),
                        LeanExpr::nat_lit_u128(n.unsigned_abs()),
                    ),
                )
            }
        }
        Formula::UInt(n) => {
            LeanExpr::app(const_expr("Trust.Formula.int"), LeanExpr::nat_lit_u128(*n))
        }
        // Trust: NOT CHANGED, and deliberately so — FLAGGED FOR A SEPARATE DECISION.
        // `value` is an `i128` carrying a BIT PATTERN, not a mathematical integer, so
        // the right exact encoding depends on bitvector semantics this change has not
        // established: `*value as u64` takes the low 64 bits, whereas `*value as u128`
        // would take the low 128, and the two DIFFER for a negative `value` (two's
        // complement at a different width). Making it "exact" without settling which
        // width the carrier denotes could change the meaning of every negative bitvec
        // literal. The truncation is therefore left in place, visible and recorded,
        // rather than replaced by a guess. Determine the carrier's width semantics
        // first, then encode exactly.
        Formula::BitVec { value, width } => LeanExpr::apps(
            const_expr("Trust.Formula.bitvec"),
            vec![LeanExpr::nat_lit(*value as u64), LeanExpr::nat_lit(u64::from(*width))],
        ),

        // Variables
        Formula::Var(name_str, sort) => LeanExpr::apps(
            const_expr("Trust.Formula.var"),
            vec![LeanExpr::str_lit(name_str.as_str()), translate_sort(sort)],
        ),

        // Boolean connectives
        Formula::Not(inner) => LeanExpr::app(const_expr("Not"), translate_formula(inner)),
        Formula::And(children) => {
            if children.is_empty() {
                return const_expr("True");
            }
            let mut result = translate_formula(&children[0]);
            for child in &children[1..] {
                result = LeanExpr::apps(const_expr("And"), vec![result, translate_formula(child)]);
            }
            result
        }
        Formula::Or(children) => {
            if children.is_empty() {
                return const_expr("False");
            }
            let mut result = translate_formula(&children[0]);
            for child in &children[1..] {
                result = LeanExpr::apps(const_expr("Or"), vec![result, translate_formula(child)]);
            }
            result
        }
        Formula::Implies(lhs, rhs) => LeanExpr::apps(
            const_expr("Trust.Formula.implies"),
            vec![translate_formula(lhs), translate_formula(rhs)],
        ),

        // Comparisons
        Formula::Eq(lhs, rhs) => LeanExpr::apps(
            const_expr("Trust.Formula.eq"),
            vec![translate_formula(lhs), translate_formula(rhs)],
        ),
        Formula::Lt(lhs, rhs) => LeanExpr::apps(
            const_expr("Trust.Formula.lt"),
            vec![translate_formula(lhs), translate_formula(rhs)],
        ),
        Formula::Le(lhs, rhs) => LeanExpr::apps(
            const_expr("Trust.Formula.le"),
            vec![translate_formula(lhs), translate_formula(rhs)],
        ),
        Formula::Gt(lhs, rhs) => LeanExpr::apps(
            const_expr("Trust.Formula.gt"),
            vec![translate_formula(lhs), translate_formula(rhs)],
        ),
        Formula::Ge(lhs, rhs) => LeanExpr::apps(
            const_expr("Trust.Formula.ge"),
            vec![translate_formula(lhs), translate_formula(rhs)],
        ),

        // Integer arithmetic
        Formula::Add(lhs, rhs) => translate_binop("Trust.Formula.add", lhs, rhs),
        Formula::Sub(lhs, rhs) => translate_binop("Trust.Formula.sub", lhs, rhs),
        Formula::Mul(lhs, rhs) => translate_binop("Trust.Formula.mul", lhs, rhs),
        Formula::Div(lhs, rhs) => translate_binop("Trust.Formula.div", lhs, rhs),
        Formula::Rem(lhs, rhs) => translate_binop("Trust.Formula.rem", lhs, rhs),
        Formula::Neg(inner) => {
            LeanExpr::app(const_expr("Trust.Formula.neg"), translate_formula(inner))
        }

        // Bitvector arithmetic
        Formula::BvAdd(lhs, rhs, w) => translate_bv_binop("Trust.Formula.bvAdd", lhs, rhs, *w),
        Formula::BvSub(lhs, rhs, w) => translate_bv_binop("Trust.Formula.bvSub", lhs, rhs, *w),
        Formula::BvMul(lhs, rhs, w) => translate_bv_binop("Trust.Formula.bvMul", lhs, rhs, *w),
        Formula::BvUDiv(lhs, rhs, w) => translate_bv_binop("Trust.Formula.bvUDiv", lhs, rhs, *w),
        Formula::BvSDiv(lhs, rhs, w) => translate_bv_binop("Trust.Formula.bvSDiv", lhs, rhs, *w),
        Formula::BvURem(lhs, rhs, w) => translate_bv_binop("Trust.Formula.bvURem", lhs, rhs, *w),
        Formula::BvSRem(lhs, rhs, w) => translate_bv_binop("Trust.Formula.bvSRem", lhs, rhs, *w),
        Formula::BvAnd(lhs, rhs, w) => translate_bv_binop("Trust.Formula.bvAnd", lhs, rhs, *w),
        Formula::BvOr(lhs, rhs, w) => translate_bv_binop("Trust.Formula.bvOr", lhs, rhs, *w),
        Formula::BvXor(lhs, rhs, w) => translate_bv_binop("Trust.Formula.bvXor", lhs, rhs, *w),
        Formula::BvNot(inner, w) => LeanExpr::apps(
            const_expr("Trust.Formula.bvNot"),
            vec![translate_formula(inner), LeanExpr::nat_lit(u64::from(*w))],
        ),
        Formula::BvShl(lhs, rhs, w) => translate_bv_binop("Trust.Formula.bvShl", lhs, rhs, *w),
        Formula::BvLShr(lhs, rhs, w) => translate_bv_binop("Trust.Formula.bvLShr", lhs, rhs, *w),
        Formula::BvAShr(lhs, rhs, w) => translate_bv_binop("Trust.Formula.bvAShr", lhs, rhs, *w),

        // Bitvector comparisons
        Formula::BvULt(lhs, rhs, w) => translate_bv_binop("Trust.Formula.bvULt", lhs, rhs, *w),
        Formula::BvULe(lhs, rhs, w) => translate_bv_binop("Trust.Formula.bvULe", lhs, rhs, *w),
        Formula::BvSLt(lhs, rhs, w) => translate_bv_binop("Trust.Formula.bvSLt", lhs, rhs, *w),
        Formula::BvSLe(lhs, rhs, w) => translate_bv_binop("Trust.Formula.bvSLe", lhs, rhs, *w),

        // Bitvector conversions
        Formula::BvToInt(inner, w, signed) => LeanExpr::apps(
            const_expr("Trust.Formula.bvToInt"),
            vec![
                translate_formula(inner),
                LeanExpr::nat_lit(u64::from(*w)),
                if *signed { const_expr("Bool.true") } else { const_expr("Bool.false") },
            ],
        ),
        Formula::IntToBv(inner, w) => LeanExpr::apps(
            const_expr("Trust.Formula.intToBv"),
            vec![translate_formula(inner), LeanExpr::nat_lit(u64::from(*w))],
        ),
        Formula::BvExtract { inner, high, low } => LeanExpr::apps(
            const_expr("Trust.Formula.bvExtract"),
            vec![
                translate_formula(inner),
                LeanExpr::nat_lit(u64::from(*high)),
                LeanExpr::nat_lit(u64::from(*low)),
            ],
        ),
        Formula::BvConcat(lhs, rhs) => translate_binop("Trust.Formula.bvConcat", lhs, rhs),
        Formula::BvZeroExt(inner, w) => LeanExpr::apps(
            const_expr("Trust.Formula.bvZeroExt"),
            vec![translate_formula(inner), LeanExpr::nat_lit(u64::from(*w))],
        ),
        Formula::BvSignExt(inner, w) => LeanExpr::apps(
            const_expr("Trust.Formula.bvSignExt"),
            vec![translate_formula(inner), LeanExpr::nat_lit(u64::from(*w))],
        ),

        // Conditional
        Formula::Ite(cond, then_, else_) => LeanExpr::apps(
            const_expr("Trust.Formula.ite"),
            vec![translate_formula(cond), translate_formula(then_), translate_formula(else_)],
        ),

        // Quantifiers
        Formula::Forall(bindings, body) => {
            let mut result = translate_formula(body);
            // Encode innermost binding first (reverse order for de Bruijn)
            for (var_name, sort) in bindings.iter().rev() {
                result = LeanExpr::apps(
                    const_expr("Trust.Formula.forall"),
                    vec![LeanExpr::str_lit(var_name.as_str()), translate_sort(sort), result],
                );
            }
            result
        }
        Formula::Exists(bindings, body) => {
            let mut result = translate_formula(body);
            for (var_name, sort) in bindings.iter().rev() {
                result = LeanExpr::apps(
                    const_expr("Trust.Formula.exists"),
                    vec![LeanExpr::str_lit(var_name.as_str()), translate_sort(sort), result],
                );
            }
            result
        }

        // Arrays
        Formula::Select(array, index) => translate_binop("Trust.Formula.select", array, index),
        Formula::Store(array, index, value) => LeanExpr::apps(
            const_expr("Trust.Formula.store"),
            vec![translate_formula(array), translate_formula(index), translate_formula(value)],
        ),
        _ => const_expr("Trust.Formula.unknown"),
    }
}

/// Translate a binary operation (integer domain).
fn translate_binop(op_name: &str, lhs: &Formula, rhs: &Formula) -> LeanExpr {
    LeanExpr::apps(const_expr(op_name), vec![translate_formula(lhs), translate_formula(rhs)])
}

/// Translate a bitvector binary operation (with width parameter).
fn translate_bv_binop(op_name: &str, lhs: &Formula, rhs: &Formula, width: u32) -> LeanExpr {
    LeanExpr::apps(
        const_expr(op_name),
        vec![translate_formula(lhs), translate_formula(rhs), LeanExpr::nat_lit(u64::from(width))],
    )
}

// ---------------------------------------------------------------------------
// VcKind → clean Expr translation
// ---------------------------------------------------------------------------

/// Translate a VcKind into a clean expression representing the VC category.
///
/// This is used as metadata in the theorem statement so the clean proof
/// can reference which kind of obligation is being discharged.
pub(crate) fn translate_vc_kind(kind: &VcKind) -> LeanExpr {
    match kind {
        VcKind::ArithmeticOverflow { .. } => const_expr("Trust.VcKind.arithmeticOverflow"),
        VcKind::ShiftOverflow { .. } => const_expr("Trust.VcKind.shiftOverflow"),
        VcKind::DivisionByZero => const_expr("Trust.VcKind.divisionByZero"),
        VcKind::RemainderByZero => const_expr("Trust.VcKind.remainderByZero"),
        VcKind::IndexOutOfBounds => const_expr("Trust.VcKind.indexOutOfBounds"),
        VcKind::SliceBoundsCheck => const_expr("Trust.VcKind.sliceBoundsCheck"),
        VcKind::Assertion { .. } => const_expr("Trust.VcKind.assertion"),
        VcKind::Precondition { .. } => const_expr("Trust.VcKind.precondition"),
        VcKind::Postcondition => const_expr("Trust.VcKind.postcondition"),
        VcKind::CastOverflow { .. } => const_expr("Trust.VcKind.castOverflow"),
        VcKind::NegationOverflow { .. } => const_expr("Trust.VcKind.negationOverflow"),
        VcKind::Unreachable => const_expr("Trust.VcKind.unreachable"),
        VcKind::DeadState { .. } => const_expr("Trust.VcKind.deadState"),
        VcKind::Deadlock => const_expr("Trust.VcKind.deadlock"),
        VcKind::Temporal { .. } => const_expr("Trust.VcKind.temporal"),
        // Trust: Liveness and fairness clean translations.
        VcKind::Liveness { .. } => const_expr("Trust.VcKind.liveness"),
        VcKind::Fairness { .. } => const_expr("Trust.VcKind.fairness"),
        // Trust: Protocol composition verification
        VcKind::ProtocolViolation { .. } => const_expr("Trust.VcKind.protocolViolation"),
        VcKind::TaintViolation { .. } => const_expr("Trust.VcKind.taintViolation"),
        VcKind::RefinementViolation { .. } => const_expr("Trust.VcKind.refinementViolation"),
        VcKind::ResilienceViolation { .. } => const_expr("Trust.VcKind.resilienceViolation"),
        VcKind::NonTermination { .. } => const_expr("Trust.VcKind.nonTermination"),
        // Data race and memory ordering clean translations.
        VcKind::DataRace { .. } => const_expr("Trust.VcKind.dataRace"),
        VcKind::InsufficientOrdering { .. } => const_expr("Trust.VcKind.insufficientOrdering"),
        // Translation validation.
        VcKind::TranslationValidation { .. } => const_expr("Trust.VcKind.translationValidation"),
        // Floating-point operation VCs.
        VcKind::FloatDivisionByZero => const_expr("Trust.VcKind.floatDivByZero"),
        VcKind::FloatOverflowToInfinity { .. } => const_expr("Trust.VcKind.floatOverflowInf"),
        // Rvalue safety VCs.
        VcKind::InvalidDiscriminant { .. } => const_expr("Trust.VcKind.invalidDiscriminant"),
        VcKind::AggregateArrayLengthMismatch { .. } => {
            const_expr("Trust.VcKind.aggregateArrayLengthMismatch")
        }
        // Unsafe operation.
        VcKind::UnsafeOperation { .. } => const_expr("Trust.VcKind.unsafeOperation"),
        _ => const_expr("Trust.VcKind.unknown"),
    }
}

// ---------------------------------------------------------------------------
// Full canonical VC → clean theorem statement
// ---------------------------------------------------------------------------

/// Translate canonical VC bytes into a clean theorem-statement expression.
///
/// The canonical bytes encode a VcKind + Formula pair (see canonical.rs).
/// This function decodes the canonical form and produces a clean Prop
/// expression that a ProofCert must witness.
///
/// For now, this takes a VC directly rather than decoding from bytes,
/// since we always have the VC available at the call site.
pub fn translate_vc_to_clean_theorem(kind: &VcKind, formula: &Formula) -> LeanExpr {
    // The theorem is: Trust.VC.holds <kind> <formula>
    // This wraps the formula in a VC-kind-annotated Prop.
    LeanExpr::apps(
        const_expr("Trust.VC.holds"),
        vec![translate_vc_kind(kind), translate_formula(formula)],
    )
}

// ---------------------------------------------------------------------------
// Certificate verification via clean kernel
// ---------------------------------------------------------------------------

/// Verify a clean ProofCert against a theorem expression using the kernel.
///
/// This is the trust boundary: if this function returns `Ok(())`, the
/// proof term has been type-checked by the clean kernel and the result
/// can be upgraded from Trusted to Certified.
///
/// Replay runs in the CERTIFICATION environment (prelude + the `Trust.*`
/// canonical-VC signature), so proofs of `Trust.VC.holds <kind> <formula>`
/// statements are checkable, and it enforces a STRICT zero-axiom transitive
/// closure on the replayed proof — the prelude ships `sorry`/`trustedAy`/
/// `trustedArith`/`propext` as axiom-kind constants, and every one of them
/// would otherwise be a certificate-forgery primitive (see
/// [`proof_is_axiom_free`]).
///
/// # Arguments
///
/// * `proof_cert` - The clean proof certificate to verify
/// * `theorem_expr` - The clean expression representing the theorem statement
///
/// # Errors
///
/// - `KernelRejected` if clean's certificate replay rejects the proof term
/// - `KernelRejected` if the proof's transitive closure reaches an axiom-kind
///   constant
/// - `KernelRejected` if the replayed proof does not inhabit the theorem statement
pub fn verify_proof_cert(
    proof_cert: &ProofCert,
    theorem_expr: &LeanExpr,
) -> Result<(), CertificateError> {
    let Some(env) = certification_env() else {
        return Err(CertificateError::KernelRejected {
            reason: "clean certification environment failed to initialize".to_string(),
        });
    };
    let mut verifier = CertVerifier::new(&env);

    let (proof_expr, proven_type) =
        verifier.replay_and_verify(proof_cert).map_err(|e| CertificateError::KernelRejected {
            reason: format!("clean CertVerifier rejected proof replay: {e}"),
        })?;

    // Trust: STRICT axiom-closure gate — a Certified verdict must carry a
    // zero-axiom kernel proof. No whitelist: `sorry (Trust.VC.holds k f)`
    // type-checks, and propext(+choice) degenerates `@Eq Prop`; both must be
    // rejected HERE, before the def-eq identity can be claimed.
    if !proof_is_axiom_free(&env, &proof_expr) {
        return Err(CertificateError::KernelRejected {
            reason: "clean certificate depends on axiom-kind constants (e.g. sorry/trustedAy/\
                     propext) — refusing to certify"
                .to_string(),
        });
    }

    let tc = TypeChecker::new(&env);
    if !tc.is_def_eq(&proven_type, theorem_expr) {
        return Err(CertificateError::KernelRejected {
            reason: "clean certificate proves a different theorem than requested".to_string(),
        });
    }

    tc.check_type(&proof_expr, theorem_expr).map_err(|e| CertificateError::KernelRejected {
        reason: format!("clean TypeChecker rejected replayed proof: {e}"),
    })?;

    Ok(())
}

/// Deserialize a proof certificate from bytes (bincode format).
///
/// This is the inverse of the serialization that solvers produce.
/// The bytes are opaque to Trust — only clean can interpret them.
pub fn deserialize_proof_cert(bytes: &[u8]) -> Result<ProofCert, CertificateError> {
    bincode::deserialize(bytes).map_err(|e| CertificateError::InvalidProofTerm {
        reason: format!("failed to deserialize clean ProofCert: {e}"),
    })
}

/// Serialize a proof certificate to bytes (bincode format).
///
/// Used when storing certificates alongside compiled artifacts.
pub fn serialize_proof_cert(cert: &ProofCert) -> Result<Vec<u8>, CertificateError> {
    bincode::serialize(cert).map_err(|e| CertificateError::SerializationFailed {
        reason: format!("failed to serialize clean ProofCert: {e}"),
    })
}

/// Convert a `LeanProofTerm` (our intermediate representation)
/// to serialized `ProofCert` bytes for the clean kernel.
///
/// This bridges the reconstruction pipeline output to the kernel-checked
/// certification path. The translation maps our term constructors to
/// clean-kernel's ProofCert variants:
///
/// - `LeanProofTerm::Const(name)` -> `ProofCert::Const { name, levels: [] }`
/// - `LeanProofTerm::App(f, a)` -> `ProofCert::App { func, arg }`
/// - `LeanProofTerm::Lambda{..}` -> `ProofCert::Lam { .. }`
/// - `LeanProofTerm::Sort(u)` -> `ProofCert::Sort { level }`
/// - `LeanProofTerm::Var(idx)` -> `ProofCert::BVar { idx, .. }`
/// - `LeanProofTerm::ByDecidability{..}` -> `ProofCert::Const("decide")`
/// - `LeanProofTerm::ByAssumption{..}` -> `ProofCert::BVar { idx, .. }`
///
/// Returns the serialized bytes. Conversion or serialization failures are
/// returned as errors so callers cannot accidentally wrap debug text in a
/// trusted certificate payload.
pub fn serialize_proof_cert_from_lean_term(
    term: &crate::reconstruction::LeanProofTerm,
) -> Result<Vec<u8>, CertificateError> {
    let cert = lean_term_to_proof_cert(term)?;
    serialize_proof_cert(&cert)
}

/// Convert a `LeanProofTerm` to a clean-kernel `ProofCert`.
fn lean_term_to_proof_cert(
    term: &crate::reconstruction::LeanProofTerm,
) -> Result<ProofCert, CertificateError> {
    use clean_kernel::BinderInfo;

    use crate::reconstruction::LeanProofTerm;

    match term {
        LeanProofTerm::Var(idx) => Ok(ProofCert::BVar {
            idx: checked_bvar_index(*idx)?,
            expected_type: Box::new(LeanExpr::prop()),
        }),
        LeanProofTerm::App(f, a) => {
            let fn_cert = lean_term_to_proof_cert(f)?;
            let arg_cert = lean_term_to_proof_cert(a)?;
            Ok(ProofCert::App {
                fn_cert: Box::new(fn_cert),
                fn_type: Box::new(LeanExpr::prop()),
                arg_cert: Box::new(arg_cert),
                result_type: Box::new(LeanExpr::prop()),
            })
        }
        LeanProofTerm::Lambda { binder_type, body, .. } => {
            let arg_cert = lean_term_to_proof_cert(binder_type)?;
            let body_cert = lean_term_to_proof_cert(body)?;
            Ok(ProofCert::Lam {
                binder_info: BinderInfo::Default,
                arg_type_cert: Box::new(arg_cert),
                body_cert: Box::new(body_cert),
                result_type: Box::new(LeanExpr::prop()),
            })
        }
        LeanProofTerm::Sort(level) => {
            Ok(ProofCert::Sort { level: LeanLevel::zero().add_offset(*level) })
        }
        LeanProofTerm::Const(name_str) => Ok(ProofCert::Const {
            name: LeanName::from_string(name_str),
            levels: vec![],
            type_: Box::new(LeanExpr::prop()),
        }),
        LeanProofTerm::ByDecidability { .. } => Ok(ProofCert::Const {
            name: LeanName::from_string("decide"),
            levels: vec![],
            type_: Box::new(LeanExpr::prop()),
        }),
        LeanProofTerm::ByAssumption { hypothesis_index } => Ok(ProofCert::BVar {
            idx: checked_bvar_index(*hypothesis_index)?,
            expected_type: Box::new(LeanExpr::prop()),
        }),
        LeanProofTerm::Let { ty, value, body, .. } => {
            let ty_cert = lean_term_to_proof_cert(ty)?;
            let val_cert = lean_term_to_proof_cert(value)?;
            let body_cert = lean_term_to_proof_cert(body)?;
            Ok(ProofCert::Let {
                type_cert: Box::new(ty_cert),
                value_cert: Box::new(val_cert),
                body_cert: Box::new(body_cert),
                result_type: Box::new(LeanExpr::prop()),
            })
        }
    }
}

fn checked_bvar_index(idx: usize) -> Result<u32, CertificateError> {
    u32::try_from(idx).map_err(|_| CertificateError::InvalidProofTerm {
        reason: format!("de Bruijn index {idx} exceeds clean ProofCert u32 range"),
    })
}

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;

    /// Helper: check that a clean Expr's debug output contains a Name component.
    ///
    /// clean Name debug format shows `Str(Name { ... }, "component")`, so
    /// we search for the quoted string component in the debug output.
    fn debug_contains_name(expr: &LeanExpr, name_component: &str) -> bool {
        let debug = format!("{expr:?}");
        // Name components appear as quoted strings in the Str variant
        debug.contains(&format!("\"{name_component}\""))
    }

    // -----------------------------------------------------------------------
    // Sort translation tests
    // -----------------------------------------------------------------------

    #[test]
    fn translate_sort_bool() {
        let expr = translate_sort(&Sort::Bool);
        assert!(
            debug_contains_name(&expr, "Bool") && debug_contains_name(&expr, "Sort"),
            "Bool sort should produce Const with Sort.Bool name"
        );
    }

    #[test]
    fn translate_sort_int() {
        let expr = translate_sort(&Sort::Int);
        assert!(
            debug_contains_name(&expr, "Int") && debug_contains_name(&expr, "Sort"),
            "Int sort should produce Const with Sort.Int name"
        );
    }

    #[test]
    fn translate_sort_bitvec() {
        let expr = translate_sort(&Sort::BitVec(32));
        assert!(
            debug_contains_name(&expr, "BitVec"),
            "BitVec sort should contain BitVec name component"
        );
    }

    #[test]
    fn translate_sort_array() {
        let expr = translate_sort(&Sort::Array(Box::new(Sort::Int), Box::new(Sort::Bool)));
        assert!(
            debug_contains_name(&expr, "Array"),
            "Array sort should contain Array name component"
        );
    }

    // -----------------------------------------------------------------------
    // Formula translation tests
    // -----------------------------------------------------------------------

    #[test]
    fn translate_formula_bool_true() {
        let expr = translate_formula(&Formula::Bool(true));
        assert!(debug_contains_name(&expr, "True"), "Bool(true) should translate to True");
    }

    #[test]
    fn translate_formula_bool_false() {
        let expr = translate_formula(&Formula::Bool(false));
        assert!(debug_contains_name(&expr, "False"), "Bool(false) should translate to False");
    }

    #[test]
    fn translate_formula_int_positive() {
        let expr = translate_formula(&Formula::Int(42));
        assert!(
            debug_contains_name(&expr, "int") && debug_contains_name(&expr, "Formula"),
            "Int(42) should contain Formula.int name"
        );
    }

    #[test]
    fn translate_formula_int_negative() {
        let expr = translate_formula(&Formula::Int(-7));
        assert!(debug_contains_name(&expr, "neg"), "Int(-7) should contain neg name");
    }

    #[test]
    fn translate_formula_var() {
        let expr = translate_formula(&Formula::Var("x".into(), Sort::Int));
        assert!(
            debug_contains_name(&expr, "var") && debug_contains_name(&expr, "Formula"),
            "Var should translate to Formula.var"
        );
    }

    #[test]
    fn translate_formula_not() {
        let expr = translate_formula(&Formula::Not(Box::new(Formula::Bool(true))));
        assert!(debug_contains_name(&expr, "Not"), "Not should translate to Not");
    }

    #[test]
    fn translate_formula_and() {
        let expr =
            translate_formula(&Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]));
        assert!(debug_contains_name(&expr, "And"), "And should translate to And");
    }

    #[test]
    fn translate_formula_and_empty() {
        let expr = translate_formula(&Formula::And(vec![]));
        assert!(debug_contains_name(&expr, "True"), "And([]) should translate to True");
    }

    #[test]
    fn translate_formula_or_empty() {
        let expr = translate_formula(&Formula::Or(vec![]));
        assert!(debug_contains_name(&expr, "False"), "Or([]) should translate to False");
    }

    #[test]
    fn translate_formula_comparison_le() {
        let expr = translate_formula(&Formula::Le(
            Box::new(Formula::Int(0)),
            Box::new(Formula::Var("x".into(), Sort::Int)),
        ));
        assert!(
            debug_contains_name(&expr, "le") && debug_contains_name(&expr, "Formula"),
            "Le should translate to Formula.le"
        );
    }

    #[test]
    fn translate_formula_arithmetic_add() {
        let expr = translate_formula(&Formula::Add(
            Box::new(Formula::Var("a".into(), Sort::Int)),
            Box::new(Formula::Var("b".into(), Sort::Int)),
        ));
        assert!(
            debug_contains_name(&expr, "add") && debug_contains_name(&expr, "Formula"),
            "Add should translate to Formula.add"
        );
    }

    #[test]
    fn translate_formula_bv_add() {
        let expr = translate_formula(&Formula::BvAdd(
            Box::new(Formula::BitVec { value: 1, width: 32 }),
            Box::new(Formula::BitVec { value: 2, width: 32 }),
            32,
        ));
        assert!(debug_contains_name(&expr, "bvAdd"), "BvAdd should translate to Formula.bvAdd");
    }

    #[test]
    fn translate_formula_ite() {
        let expr = translate_formula(&Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Int(1)),
            Box::new(Formula::Int(0)),
        ));
        assert!(
            debug_contains_name(&expr, "ite") && debug_contains_name(&expr, "Formula"),
            "Ite should translate to Formula.ite"
        );
    }

    #[test]
    fn translate_formula_forall() {
        let expr = translate_formula(&Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Le(
                Box::new(Formula::Int(0)),
                Box::new(Formula::Var("x".into(), Sort::Int)),
            )),
        ));
        assert!(
            debug_contains_name(&expr, "forall") && debug_contains_name(&expr, "Formula"),
            "Forall should translate to Formula.forall"
        );
    }

    // -----------------------------------------------------------------------
    // VcKind translation tests
    // -----------------------------------------------------------------------

    #[test]
    fn translate_vc_kind_variants() {
        let cases: Vec<(VcKind, &str)> = vec![
            (VcKind::DivisionByZero, "divisionByZero"),
            (VcKind::RemainderByZero, "remainderByZero"),
            (VcKind::IndexOutOfBounds, "indexOutOfBounds"),
            (VcKind::Postcondition, "postcondition"),
            (VcKind::Unreachable, "unreachable"),
            (VcKind::Deadlock, "deadlock"),
            (VcKind::CastOverflow { from_ty: Ty::usize(), to_ty: Ty::Bool }, "castOverflow"),
            (VcKind::NegationOverflow { ty: Ty::usize() }, "negationOverflow"),
        ];
        for (kind, expected_suffix) in cases {
            let expr = translate_vc_kind(&kind);
            assert!(
                debug_contains_name(&expr, expected_suffix),
                "VcKind::{kind:?} should contain '{expected_suffix}'"
            );
        }
    }

    // -----------------------------------------------------------------------
    // Full VC → theorem translation tests
    // -----------------------------------------------------------------------

    #[test]
    fn translate_vc_to_theorem() {
        let theorem = translate_vc_to_clean_theorem(
            &VcKind::DivisionByZero,
            &Formula::Not(Box::new(Formula::Eq(
                Box::new(Formula::Var("divisor".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))),
        );
        assert!(
            debug_contains_name(&theorem, "holds") && debug_contains_name(&theorem, "VC"),
            "theorem should be wrapped in Trust.VC.holds"
        );
        assert!(
            debug_contains_name(&theorem, "divisionByZero"),
            "theorem should contain divisionByZero kind"
        );
    }

    // -----------------------------------------------------------------------
    // Midpoint overflow VC translation (real-world test)
    // -----------------------------------------------------------------------

    #[test]
    fn translate_midpoint_overflow_vc() {
        let formula = Formula::Not(Box::new(Formula::And(vec![
            Formula::Le(
                Box::new(Formula::Int(0)),
                Box::new(Formula::Add(
                    Box::new(Formula::Var("a".into(), Sort::Int)),
                    Box::new(Formula::Var("b".into(), Sort::Int)),
                )),
            ),
            Formula::Le(
                Box::new(Formula::Add(
                    Box::new(Formula::Var("a".into(), Sort::Int)),
                    Box::new(Formula::Var("b".into(), Sort::Int)),
                )),
                Box::new(Formula::Int((1i128 << 64) - 1)),
            ),
        ])));

        let theorem = translate_vc_to_clean_theorem(
            &VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::usize(), Ty::usize()) },
            &formula,
        );

        assert!(debug_contains_name(&theorem, "holds"), "midpoint VC theorem should contain holds");
        assert!(
            debug_contains_name(&theorem, "arithmeticOverflow"),
            "midpoint VC should reference arithmeticOverflow"
        );
        assert!(debug_contains_name(&theorem, "Not"), "midpoint VC should contain negation");
    }

    // -----------------------------------------------------------------------
    // Serialization roundtrip test
    // -----------------------------------------------------------------------

    #[test]
    fn proof_cert_serialization_roundtrip() {
        let cert = ProofCert::Sort { level: LeanLevel::zero() };
        let bytes = serialize_proof_cert(&cert).expect("should serialize");
        assert!(!bytes.is_empty(), "serialized bytes should be non-empty");
        let recovered = deserialize_proof_cert(&bytes).expect("should deserialize");
        assert_eq!(cert, recovered, "ProofCert should survive serialization roundtrip");
    }

    #[test]
    fn verify_proof_cert_rejects_theorem_type_certificate_as_proof() {
        let theorem = LeanExpr::prop();
        let cert_for_theorem_expr = ProofCert::Sort { level: LeanLevel::zero() };

        let err = verify_proof_cert(&cert_for_theorem_expr, &theorem)
            .expect_err("a type certificate for Prop is not a proof of Prop");
        assert!(
            matches!(err, CertificateError::KernelRejected { .. }),
            "should be KernelRejected, got: {err:?}"
        );
        assert!(
            err.to_string().contains("different theorem"),
            "reason should identify theorem mismatch, got: {err}"
        );
    }

    fn test_kind() -> VcKind {
        VcKind::Assertion { message: "kernel fast-path test".to_string() }
    }

    #[test]
    fn direct_contradiction_helper_emits_replayable_proof_cert() {
        let p = Formula::Var("p".into(), Sort::Bool);
        let formula = Formula::And(vec![p.clone(), Formula::Not(Box::new(p))]);
        let kind = test_kind();

        let bytes = kernel_certify_direct_contradiction(&kind, &formula)
            .expect("direct contradiction should kernel-certify");
        let cert = deserialize_proof_cert(&bytes).expect("helper should emit ProofCert bytes");

        // The emitted cert proves THE CANONICAL statement — the exact theorem
        // `generate_certificate` replays against. This identity is what makes
        // the pipeline's kernel-Certified fast path live end-to-end.
        let theorem = translate_vc_to_clean_theorem(&kind, &formula);
        verify_proof_cert(&cert, &theorem)
            .expect("emitted ProofCert should replay against the canonical Trust.VC.holds theorem");
    }

    #[test]
    fn direct_contradiction_reversed_order_also_certifies() {
        // ¬X ∧ X (Not-side first) must certify against ITS canonical theorem.
        let p = Formula::Var("p".into(), Sort::Bool);
        let formula = Formula::And(vec![Formula::Not(Box::new(p.clone())), p]);
        let kind = test_kind();
        let bytes = kernel_certify_direct_contradiction(&kind, &formula)
            .expect("reversed direct contradiction should kernel-certify");
        let cert = deserialize_proof_cert(&bytes).expect("ProofCert bytes");
        let theorem = translate_vc_to_clean_theorem(&kind, &formula);
        verify_proof_cert(&cert, &theorem).expect("replays against the canonical theorem");
    }

    #[test]
    fn memoized_certification_env_kernel_verdict_matches_fresh() {
        // The memo (`certification_env()`) hands out a CLONE of a once-built
        // prelude + Trust.* signature env. A clone must be kernel-verdict-
        // identical to a freshly built one: it must accept exactly the proofs a
        // fresh env accepts. We assert this on the universal direct-
        // contradiction proof that exercises the full check /
        // infer_type_with_cert path (and previously regressed on an older pin).
        let (proof, theorem) = direct_contradiction_proof_and_theorem();

        let fresh = {
            let mut env = Environment::try_with_prelude().expect("prelude builds");
            register_trust_vc_signature(&mut env).expect("Trust.* signature registers");
            env
        };
        let memo = certification_env().expect("memoized env builds"); // memoized clone

        let tc_fresh = TypeChecker::new(&fresh);
        let tc_memo = TypeChecker::new(&memo);

        assert!(
            tc_fresh.check_type(&proof, &theorem).is_ok(),
            "fresh env must accept the direct-contradiction proof"
        );
        assert!(
            tc_memo.check_type(&proof, &theorem).is_ok(),
            "memoized (cloned) env must accept the same proof as a fresh env"
        );

        let (ty_fresh, _) =
            tc_fresh.infer_type_with_cert(&proof).expect("fresh infer_type_with_cert");
        let (ty_memo, _) = tc_memo.infer_type_with_cert(&proof).expect("memo infer_type_with_cert");
        assert!(tc_fresh.is_def_eq(&ty_fresh, &theorem));
        assert!(tc_memo.is_def_eq(&ty_memo, &theorem));
    }

    #[test]
    fn direct_contradiction_helper_fails_closed_for_non_matching_formula() {
        let p = Formula::Var("p".into(), Sort::Bool);
        let formula =
            Formula::And(vec![p, Formula::Not(Box::new(Formula::Var("q".into(), Sort::Bool)))]);

        assert!(
            kernel_certify_direct_contradiction(&test_kind(), &formula).is_none(),
            "non-direct contradiction must not emit a certificate"
        );
    }

    #[test]
    fn lossy_translation_fails_closed_on_every_fast_path() {
        // SymVar has NO faithful translation arm — it hits the
        // `Trust.Formula.unknown` constant, which is DELIBERATELY undeclared in
        // the certification environment (two distinct lossy terms would
        // otherwise collapse to one kernel constant — a false-Certify vector).
        // Even a structurally perfect contradiction over it must decline.
        let s = Formula::SymVar("s0".into(), Sort::Int);
        let formula = Formula::And(vec![s.clone(), Formula::Not(Box::new(s))]);
        let kind = test_kind();
        assert!(
            kernel_certify_direct_contradiction(&kind, &formula).is_none(),
            "lossy translation must fail closed on the direct-contradiction path",
        );
        assert!(
            kernel_certify_propositional(&kind, &formula).is_none(),
            "lossy translation must fail closed on the propositional path",
        );
    }

    #[test]
    fn verify_rejects_axiom_backed_proof_of_canonical_theorem() {
        // THE FORGERY CONTROL for the strict closure gate: the prelude ships
        // `sorry.{u} : {α : Sort u} → α` as an axiom-kind constant, so
        // `sorry (Trust.VC.holds k f)` KERNEL-TYPECHECKS at the canonical
        // theorem for ANY VC — including satisfiable violations. Both halves
        // are asserted: the kernel alone accepts it; verify_proof_cert rejects.
        let kind = test_kind();
        // A SATISFIABLE violation — certifying it would be a false-Certify.
        let formula = Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Var("y".into(), Sort::Int)),
        )));
        let theorem = translate_vc_to_clean_theorem(&kind, &formula);
        let env = certification_env().expect("certification env builds");
        let tc = TypeChecker::new(&env);

        let sorry0 = LeanExpr::const_(name("sorry"), vec![LeanLevel::zero()]);
        let forged = LeanExpr::app(sorry0, theorem.clone());
        let (ty, cert) = tc
            .infer_type_with_cert(&forged)
            .expect("control: the kernel alone accepts the sorry-backed term");
        assert!(
            tc.is_def_eq(&ty, &theorem),
            "control: without the closure gate the forgery def-eqs the canonical theorem"
        );

        let err = verify_proof_cert(&cert, &theorem)
            .expect_err("axiom-backed proof must be rejected by the closure gate");
        assert!(
            matches!(err, CertificateError::KernelRejected { .. })
                && err.to_string().contains("axiom"),
            "rejection must name the axiom-closure gate, got: {err}"
        );
    }

    // -----------------------------------------------------------------------
    // General propositional certification (canonical double-negation split)
    // -----------------------------------------------------------------------

    fn pvar(n: &str) -> Formula {
        Formula::Var(n.into(), Sort::Bool)
    }
    fn pnot(f: Formula) -> Formula {
        Formula::Not(Box::new(f))
    }

    #[test]
    fn propositional_certifies_two_clause_resolution() {
        // (p ∨ q) ∧ ¬p ∧ ¬q  is UNSAT — multi-clause resolution the
        // direct-contradiction path cannot handle.
        let formula = Formula::And(vec![
            Formula::Or(vec![pvar("p"), pvar("q")]),
            pnot(pvar("p")),
            pnot(pvar("q")),
        ]);
        let kind = test_kind();
        assert!(
            kernel_certify_direct_contradiction(&kind, &formula).is_none(),
            "this is NOT a direct contradiction"
        );
        let bytes = kernel_certify_propositional(&kind, &formula)
            .expect("2-clause resolution must kernel-certify");
        // The emitted ProofCert must replay against the CANONICAL VC theorem.
        let cert = deserialize_proof_cert(&bytes).expect("emits ProofCert bytes");
        let theorem = translate_vc_to_clean_theorem(&kind, &formula);
        verify_proof_cert(&cert, &theorem)
            .expect("emitted cert replays against the canonical Trust.VC.holds theorem");
    }

    #[test]
    fn propositional_certifies_three_variable_refutation() {
        // (p ∨ q) ∧ (¬p ∨ r) ∧ ¬q ∧ ¬r  is UNSAT.
        let formula = Formula::And(vec![
            Formula::Or(vec![pvar("p"), pvar("q")]),
            Formula::Or(vec![pnot(pvar("p")), pvar("r")]),
            pnot(pvar("q")),
            pnot(pvar("r")),
        ]);
        assert!(
            kernel_certify_propositional(&test_kind(), &formula).is_some(),
            "3-variable propositional refutation must kernel-certify"
        );
    }

    #[test]
    fn propositional_subsumes_direct_contradiction() {
        // p ∧ ¬p — the direct-contradiction shape — is also certified by the
        // general propositional path.
        let formula = Formula::And(vec![pvar("p"), pnot(pvar("p"))]);
        assert!(
            kernel_certify_propositional(&test_kind(), &formula).is_some(),
            "direct contradiction must also certify via the general path"
        );
    }

    #[test]
    fn propositional_certifies_implies_refutation() {
        // (p → q) ∧ p ∧ ¬q is UNSAT through the IMPLICATION structure —
        // certifiable because Trust.Formula.implies reduces to `→`.
        let formula = Formula::And(vec![
            Formula::Implies(Box::new(pvar("p")), Box::new(pvar("q"))),
            pvar("p"),
            pnot(pvar("q")),
        ]);
        let kind = test_kind();
        let bytes = kernel_certify_propositional(&kind, &formula)
            .expect("modus-ponens refutation must kernel-certify");
        let cert = deserialize_proof_cert(&bytes).expect("emits ProofCert bytes");
        let theorem = translate_vc_to_clean_theorem(&kind, &formula);
        verify_proof_cert(&cert, &theorem).expect("replays against the canonical theorem");
    }

    #[test]
    fn propositional_declines_satisfiable_formula() {
        // p ∨ q is SATISFIABLE — its skeleton is true at p:=true.
        // Fail-closed: no certificate.
        let formula = Formula::Or(vec![pvar("p"), pvar("q")]);
        assert!(
            kernel_certify_propositional(&test_kind(), &formula).is_none(),
            "a satisfiable formula must NOT be certified",
        );
    }

    #[test]
    fn propositional_declines_theory_dependent_refutation() {
        // x < 0 ∧ x > 0 is UNSAT, but ONLY by arithmetic theory reasoning. Its
        // propositional skeleton treats `x<0` and `x>0` as INDEPENDENT atoms A,B,
        // and `A ∧ B` is SAT. The certifier MUST decline — certifying it would be
        // a false-Certified (theory soundness is not the kernel's to assume).
        let x = Formula::Var("x".into(), Sort::Int);
        let zero = Formula::Int(0);
        let formula = Formula::And(vec![
            Formula::Lt(Box::new(x.clone()), Box::new(zero.clone())),
            Formula::Gt(Box::new(x), Box::new(zero)),
        ]);
        assert!(
            kernel_certify_propositional(&test_kind(), &formula).is_none(),
            "theory-dependent refutation must NOT be propositionally certified — honest invariant",
        );
    }

    #[test]
    fn propositional_declines_when_atom_count_exceeds_bound() {
        // A wide conjunction of distinct atoms is SAT (no contradiction) AND
        // exceeds MAX_PROP_VARS — must decline cleanly, not panic or hang.
        let children: Vec<Formula> =
            (0..(MAX_PROP_VARS + 4)).map(|i| pvar(&format!("p{i}"))).collect();
        let formula = Formula::And(children);
        assert!(
            kernel_certify_propositional(&test_kind(), &formula).is_none(),
            "more than MAX_PROP_VARS atoms must decline",
        );
    }

    // -----------------------------------------------------------------------
    // EUF certification (equality-graph transitivity / symmetry)
    // -----------------------------------------------------------------------

    fn ivar(n: &str) -> Formula {
        Formula::Var(n.into(), Sort::Int)
    }
    fn eq(l: Formula, r: Formula) -> Formula {
        Formula::Eq(Box::new(l), Box::new(r))
    }
    fn neq(l: Formula, r: Formula) -> Formula {
        Formula::Not(Box::new(eq(l, r)))
    }

    #[test]
    fn euf_certifies_transitivity_chain() {
        // a=b ∧ b=c ∧ ¬(a=c) is EUF-UNSAT; propositional CANNOT see it.
        let formula = Formula::And(vec![
            eq(ivar("a"), ivar("b")),
            eq(ivar("b"), ivar("c")),
            neq(ivar("a"), ivar("c")),
        ]);
        assert!(
            kernel_certify_propositional(&test_kind(), &formula).is_none(),
            "propositional path must NOT certify a transitivity-only refutation"
        );
        let kind = test_kind();
        let bytes = kernel_certify_euf(&kind, &formula)
            .expect("EUF path must certify the transitivity-chain refutation");
        // The emitted ProofCert must replay against the CANONICAL VC theorem.
        let cert = deserialize_proof_cert(&bytes).expect("emits ProofCert bytes");
        let theorem = translate_vc_to_clean_theorem(&kind, &formula);
        verify_proof_cert(&cert, &theorem)
            .expect("EUF cert replays against the canonical Trust.VC.holds theorem");
    }

    #[test]
    fn euf_certifies_chain_with_reversed_literals() {
        // Orientation stress: edges given as b=a and c=b; diseq as ¬(c=a).
        // Path c → b → a uses Eq.symm on both edges.
        let formula = Formula::And(vec![
            eq(ivar("b"), ivar("a")),
            eq(ivar("c"), ivar("b")),
            neq(ivar("c"), ivar("a")),
        ]);
        assert!(
            kernel_certify_euf(&test_kind(), &formula).is_some(),
            "EUF must certify a chain regardless of literal orientation (symm)"
        );
    }

    #[test]
    fn euf_certifies_longer_chain() {
        // a=b ∧ b=c ∧ c=d ∧ d=e ∧ ¬(a=e): 4-step chain.
        let formula = Formula::And(vec![
            eq(ivar("a"), ivar("b")),
            eq(ivar("b"), ivar("c")),
            eq(ivar("c"), ivar("d")),
            eq(ivar("d"), ivar("e")),
            neq(ivar("a"), ivar("e")),
        ]);
        let bytes = kernel_certify_euf(&test_kind(), &formula)
            .expect("EUF must certify a 4-step transitivity chain");
        // The emitted ProofCert must be a well-formed serialized cert.
        let _cert = deserialize_proof_cert(&bytes).expect("EUF emits a ProofCert");
    }

    #[test]
    fn euf_declines_when_disequality_not_entailed() {
        // a=b ∧ ¬(a=c): c is NOT connected to a — the disequality is consistent.
        // EUF must decline (no false-Certified).
        let formula = Formula::And(vec![eq(ivar("a"), ivar("b")), neq(ivar("a"), ivar("c"))]);
        assert!(
            kernel_certify_euf(&test_kind(), &formula).is_none(),
            "EUF must decline when the disequality is not entailed by the equalities",
        );
    }

    #[test]
    fn euf_declines_pure_equalities_no_disequality() {
        // a=b ∧ b=c with no disequality: satisfiable, nothing to refute.
        let formula = Formula::And(vec![eq(ivar("a"), ivar("b")), eq(ivar("b"), ivar("c"))]);
        assert!(
            kernel_certify_euf(&test_kind(), &formula).is_none(),
            "EUF must decline a formula with no disequality literal",
        );
    }

    fn neg(f: Formula) -> Formula {
        Formula::Neg(Box::new(f))
    }
    fn add(a: Formula, b: Formula) -> Formula {
        Formula::Add(Box::new(a), Box::new(b))
    }

    #[test]
    fn euf_declines_opaque_pseudo_congruence() {
        // fa=p ∧ fb=q ∧ a=b ∧ ¬(p=q) with fa,fb OPAQUE leaves (NOT real
        // applications of a function to a,b). Congruence closure has nothing to
        // fire on — fa,fb are unrelated to a,b — so p,q stay unconnected →
        // DECLINE. (Congruence only applies to genuine f(·) application terms.)
        let fa = Formula::Var("fa".into(), Sort::Int);
        let fb = Formula::Var("fb".into(), Sort::Int);
        let formula = Formula::And(vec![
            eq(fa, ivar("p")),
            eq(fb, ivar("q")),
            eq(ivar("a"), ivar("b")),
            neq(ivar("p"), ivar("q")),
        ]);
        assert!(
            kernel_certify_euf(&test_kind(), &formula).is_none(),
            "opaque pseudo-congruence (no real applications) must decline",
        );
    }

    #[test]
    fn euf_certifies_unary_congruence() {
        // Neg(a)=p ∧ Neg(b)=q ∧ a=b ∧ ¬(p=q): a~b ⇒ Neg(a)~Neg(b) (congrArg),
        // so p~Neg(a)~Neg(b)~q contradicts ¬(p=q). REAL congruence.
        let formula = Formula::And(vec![
            eq(neg(ivar("a")), ivar("p")),
            eq(neg(ivar("b")), ivar("q")),
            eq(ivar("a"), ivar("b")),
            neq(ivar("p"), ivar("q")),
        ]);
        assert!(
            kernel_certify_euf(&test_kind(), &formula).is_some(),
            "unary congruence (Neg) refutation must kernel-certify",
        );
    }

    #[test]
    fn euf_certifies_binary_congruence() {
        // Add(a,c)=p ∧ Add(b,c)=q ∧ a=b ∧ ¬(p=q): a~b (and c~c) ⇒
        // Add(a,c)~Add(b,c) via the congrArg+congr spine.
        let formula = Formula::And(vec![
            eq(add(ivar("a"), ivar("c")), ivar("p")),
            eq(add(ivar("b"), ivar("c")), ivar("q")),
            eq(ivar("a"), ivar("b")),
            neq(ivar("p"), ivar("q")),
        ]);
        assert!(
            kernel_certify_euf(&test_kind(), &formula).is_some(),
            "binary congruence (Add) refutation must kernel-certify",
        );
    }

    #[test]
    fn euf_certifies_nested_congruence() {
        // Neg(Neg(a))=p ∧ Neg(Neg(b))=q ∧ a=b ∧ ¬(p=q): exercises RECURSIVE
        // congruence (Neg(a)~Neg(b) then Neg(Neg(a))~Neg(Neg(b))).
        let formula = Formula::And(vec![
            eq(neg(neg(ivar("a"))), ivar("p")),
            eq(neg(neg(ivar("b"))), ivar("q")),
            eq(ivar("a"), ivar("b")),
            neq(ivar("p"), ivar("q")),
        ]);
        assert!(
            kernel_certify_euf(&test_kind(), &formula).is_some(),
            "nested congruence refutation must kernel-certify",
        );
    }

    #[test]
    fn euf_declines_int_uint_collapse() {
        // ¬(Int(5) = UInt(5)): genuinely DISTINCT Trust terms of distinct sorts.
        // Injective full-Formula interning keeps them separate, so p≠q and there
        // is no reflexivity route → DECLINE. Certifying this would be a critical
        // false-Certify (claiming a satisfiable disequality is unsat).
        let formula =
            Formula::And(vec![Formula::Not(Box::new(eq(Formula::Int(5), Formula::UInt(5))))]);
        assert!(
            kernel_certify_euf(&test_kind(), &formula).is_none(),
            "distinct literals Int(5)/UInt(5) must NOT collapse — honest invariant",
        );
    }

    #[test]
    fn euf_declines_cross_sort_pseudo_chain() {
        // UInt(5)=x ∧ ¬(Int(5)=x): as DISTINCT terms, Int(5) is unconnected to x
        // (only UInt(5) is) → DECLINE. Guards against the encoding-collapse hole.
        let formula =
            Formula::And(vec![eq(Formula::UInt(5), ivar("x")), neq(Formula::Int(5), ivar("x"))]);
        assert!(
            kernel_certify_euf(&test_kind(), &formula).is_none(),
            "Int(5) and UInt(5) must not be conflated across an equality — honest invariant",
        );
    }

    #[test]
    fn deserialize_invalid_bytes_fails() {
        let bad_bytes = vec![0xFF, 0x00, 0xDE, 0xAD];
        let err = deserialize_proof_cert(&bad_bytes)
            .expect_err("invalid bytes should fail deserialization");
        assert!(
            matches!(err, CertificateError::InvalidProofTerm { .. }),
            "should be InvalidProofTerm, got: {err:?}"
        );
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn lean_term_rejects_bvar_index_overflow() {
        let term = crate::reconstruction::LeanProofTerm::Var(u32::MAX as usize + 1);
        let err = lean_term_to_proof_cert(&term).expect_err("overflowing index should fail");
        assert!(
            matches!(err, CertificateError::InvalidProofTerm { .. }),
            "should be InvalidProofTerm, got: {err:?}"
        );
    }

    #[test]
    fn lean_term_preserves_sort_level_above_two() {
        let term = crate::reconstruction::LeanProofTerm::Sort(3);
        let cert = lean_term_to_proof_cert(&term).expect("sort should convert");
        assert_eq!(cert, ProofCert::Sort { level: LeanLevel::zero().add_offset(3) });
    }

    #[test]
    fn serialize_complex_proof_cert() {
        use clean_kernel::BinderInfo;

        let cert = ProofCert::Lam {
            binder_info: BinderInfo::Default,
            arg_type_cert: Box::new(ProofCert::Sort { level: LeanLevel::succ(LeanLevel::zero()) }),
            body_cert: Box::new(ProofCert::BVar {
                idx: 0,
                expected_type: Box::new(LeanExpr::sort(LeanLevel::zero())),
            }),
            result_type: Box::new(LeanExpr::prop()),
        };

        let bytes = serialize_proof_cert(&cert).expect("should serialize complex cert");
        let recovered = deserialize_proof_cert(&bytes).expect("should deserialize complex cert");
        assert_eq!(cert, recovered);
    }

    // -----------------------------------------------------------------------
    // Complex formula translation tests
    // -----------------------------------------------------------------------

    #[test]
    fn translate_implies() {
        let expr = translate_formula(&Formula::Implies(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Bool(false)),
        ));
        assert!(
            debug_contains_name(&expr, "implies") && debug_contains_name(&expr, "Formula"),
            "Implies should translate to Formula.implies"
        );
    }

    #[test]
    fn translate_select_store() {
        let arr = Formula::Var("arr".into(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)));
        let select =
            translate_formula(&Formula::Select(Box::new(arr.clone()), Box::new(Formula::Int(0))));
        assert!(debug_contains_name(&select, "select"), "Select should contain select name");

        let store = translate_formula(&Formula::Store(
            Box::new(arr),
            Box::new(Formula::Int(0)),
            Box::new(Formula::Int(42)),
        ));
        assert!(debug_contains_name(&store, "store"), "Store should contain store name");
    }

    #[test]
    fn translate_exists() {
        let expr = translate_formula(&Formula::Exists(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Eq(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(42)),
            )),
        ));
        assert!(
            debug_contains_name(&expr, "exists") && debug_contains_name(&expr, "Formula"),
            "Exists should translate to Formula.exists"
        );
    }

    #[test]
    fn translate_bitvec_conversions() {
        let bv_to_int = translate_formula(&Formula::BvToInt(
            Box::new(Formula::BitVec { value: 255, width: 8 }),
            8,
            false,
        ));
        assert!(debug_contains_name(&bv_to_int, "bvToInt"), "BvToInt should contain bvToInt name");

        let int_to_bv = translate_formula(&Formula::IntToBv(Box::new(Formula::Int(42)), 32));
        assert!(debug_contains_name(&int_to_bv, "intToBv"), "IntToBv should contain intToBv name");
    }

    /// Trust: SOUNDNESS PIN (2026-07-24) — `translate_formula` must be INJECTIVE on
    /// integer literals. This is the theorem a `ProofCert` must witness
    /// (`certificate.rs` → `translate_vc_to_clean_theorem` → `verify_proof_cert`), so a
    /// collision would let a cert for one VC verify against a numerically DIFFERENT
    /// one — the same defect class as the demonstrated `clean_ground::int_lit_to_expr`
    /// false accept, which is how this site was found.
    #[test]
    fn translate_formula_encodes_wide_literals_distinctly() {
        // The collisions the old `n as u64` produced.
        assert_ne!(translate_formula(&Formula::Int(1i128 << 64)), translate_formula(&Formula::Int(0)));
        assert_ne!(
            translate_formula(&Formula::Int((1i128 << 64) + 1)),
            translate_formula(&Formula::Int(1))
        );
        assert_ne!(translate_formula(&Formula::Int(1i128 << 70)), translate_formula(&Formula::Int(0)));
        assert_ne!(
            translate_formula(&Formula::Int(i128::MAX)),
            translate_formula(&Formula::Int(i128::from(u64::MAX)))
        );
        // Negative literals go through `Trust.Formula.neg` and must be injective too.
        assert_ne!(
            translate_formula(&Formula::Int(-(1i128 << 70))),
            translate_formula(&Formula::Int(0))
        );
        assert_ne!(
            translate_formula(&Formula::Int(i128::MIN)),
            translate_formula(&Formula::Int(-(1i128 << 64)))
        );
        // `UInt` truncated a full u128 through `as u64` — the widest exposure here.
        assert_ne!(
            translate_formula(&Formula::UInt(1u128 << 64)),
            translate_formula(&Formula::UInt(0))
        );
        assert_ne!(
            translate_formula(&Formula::UInt(u128::MAX)),
            translate_formula(&Formula::UInt(u128::from(u64::MAX)))
        );
        // NO CHURN: the previously-working range is untouched, so every existing
        // certificate still witnesses the same theorem.
        for n in [0i128, 1, -1, 42, i128::from(i64::MAX), i128::from(u64::MAX)] {
            assert_eq!(translate_formula(&Formula::Int(n)), translate_formula(&Formula::Int(n)));
        }
        assert_eq!(
            translate_formula(&Formula::Int(i128::from(u64::MAX))),
            translate_formula(&Formula::Int(i128::from(u64::MAX)))
        );
    }
}

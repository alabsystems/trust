// trust-certify: kernel re-check of a compiler-finalized body-bound `ensures`
// claim (TCB closure plan step 1 — the `BodyBoundNativeReplay` row).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Re-derive a body-bound postcondition in the Clean kernel instead of
//! believing trust-wp's answer.
//!
//! # What this lane is for
//!
//! `ResultProofAuthority::BodyBoundNativeReplay` passes a row because a private
//! receipt proves trust-wp's in-process adapter really ran on it. Nothing
//! re-derives the answer, so the adapter is trusted code. This module removes
//! the adapter from that row's trusted base the same way
//! [`crate::certify_vc`] removes `ay` from a QF_LIA row's: it never reads the
//! verdict, it reconstructs the obligation as a CIC term and lets the kernel
//! judge.
//!
//! # The input is a proposition, not a proof
//!
//! trust-wp emits a verdict plus evidence artifacts (bundle/request/proof
//! digests). There is no proof object and no derivation trace to translate.
//! What *is* available is the compiler's own `trust_wp.trust-formula.v1` claim
//! envelope, pinned byte-for-byte into the native proof obligation before
//! dispatch, and rebuilt-and-compared at the sealing seam. That envelope is the
//! proposition trust-wp was asked to prove, so it is what the kernel is asked to
//! prove here. Reconstruction is possible because the envelope is a closed
//! statement, not because trust-wp said anything about it.
//!
//! # The claim shape, and why an unbounded-`Int` reading is the right one
//!
//! The body-bound envelope (built by `trust_ir_bridge::trust_wp_claim`) is
//!
//! ```text
//! { "schema": "trust_wp.trust-formula.v1",
//!   "variables": [ { "name": _, "sort": "int" | "bool" }, ... ],
//!   "body": { "op": "let", "name": "result", "sort": _,
//!             "value": <parameter | int/bool literal>,
//!             "body": <comparison / boolean-connective tree> } }
//! ```
//!
//! and its fragment forbids arithmetic everywhere (blueprint amendment 1:
//! machine arithmetic modeled over unbounded `Int` is a confirmed false-proof
//! vector — `result + 1 > result` is `Int`-valid and false at `u64::MAX`). With
//! no arithmetic and an exact defining equation, every machine-integer state
//! embeds into an `Int` valuation, so a statement proved for all of `Int` holds
//! for the machine states. Proving over `Int` is therefore the *stronger*
//! claim, which is the only direction that is safe to take.
//!
//! # The four steps, mirroring the `KernelCertified` lane
//!
//! 1. **Decode** the pinned envelope into a typed claim, fail-closed. Every
//!    node outside the accepted fragment declines; nothing is guessed.
//! 2. **Build the goal** as a `Prop`: universals are skolemized as opaque
//!    environment constants (an arbitrary constant is exactly a universally
//!    quantified variable), `result` is substituted by its defining expression,
//!    and the boolean connectives become the corresponding `Prop` connectives.
//!    The intuitionistic reading of `Not`/`implies` is *stronger* than the
//!    classical one the claim intends, so it too errs safe.
//! 3. **Build a proof term** for that goal here, from the goal alone. The
//!    prover is deliberately small (reflexivity of `Eq` and of `Int.le`, plus
//!    the introduction rules of the connectives); anything it cannot close
//!    fails closed and the row keeps its existing `Trusted` authority.
//! 4. **Re-check** with `TypeChecker::check_type` under a zero-trust budget: an
//!    axiom-closure audit restricts the term's transitive constant closure to
//!    this claim's own skolems and Clean's foundational axioms, then the
//!    serialized payload is deserialized and re-checked against an
//!    independently rebuilt environment and goal.
//!
//! # What stays trusted
//!
//! The kernel implementation, and the *construction of the goal* — that the
//! envelope really renders the authored `ensures` of this body. Contract
//! lowering and the trust-ir body walker that produced the envelope are
//! upstream of every engine and are not checked by anything here. What leaves
//! the base is trust-wp: its adapter, its replay, and its verdict are never
//! consulted on this path.

use std::collections::{BTreeMap, BTreeSet};

use clean_auto::bridge::ay_contract::{deserialize_term, serialize_term};
use clean_kernel::name::Name;
use clean_kernel::{Declaration, Environment, Expr, Level, LocalContext, TypeChecker};
use serde_json::Value;
use sha2::{Digest, Sha256};

/// Lineage domain tag. Distinct from every other `CleanCic` lane so a
/// certificate can never alias across lanes.
const LINEAGE_DOMAIN: &str = "trust-certify.cleancic.body-bound-ensures.v1";

/// Skolem-name prefix. Claim names admit `.`, `#`, `[`, `]`, `@` and friends,
/// and `Name::from_string` reads `.` as hierarchy separators — so a raw name
/// could otherwise land on a library constant such as `Int.le`. Hex-encoding
/// every byte keeps the map injective and confines it to one flat namespace no
/// Clean declaration occupies.
const SKOLEM_PREFIX: &str = "trust_bb_";

/// Node budget for the decoded claim. The envelope reaching here is already
/// compiler-built and small; the cap exists so a future producer bug cannot
/// turn goal construction into unbounded work inside the verification pass.
const MAX_CLAIM_NODES: usize = 512;

/// Foundational Clean axioms a proof may depend on. Same list as the QF_LIA
/// lane's — these are the kernel's own base, not domain knowledge about the
/// program.
const FOUNDATIONAL_AXIOMS: [&str; 6] =
    ["Classical.choice", "propext", "Quot", "Quot.mk", "Quot.lift", "Quot.sound"];

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ClaimSort {
    Int,
    Bool,
}

/// An atomic operand. The fragment admits only these in comparison position:
/// a declared variable or a literal. A compound (boolean-valued) operand would
/// need a `Bool`-level reflection of a `Prop`, so it declines instead.
#[derive(Clone, PartialEq, Eq, Debug)]
enum ClaimTerm {
    /// Declared variable, held by its raw claim name.
    Var(String),
    Int(i64),
    Bool(bool),
}

/// The decoded claim body, already normalized: `gt`/`ge` are rewritten to
/// `Lt`/`Le` with the operands swapped (`a > b` is `b < a`), and `result` is
/// substituted by its defining term at decode time.
#[derive(Clone, PartialEq, Eq, Debug)]
enum ClaimProp {
    True,
    False,
    /// A `bool`-sorted operand standing in formula position: it holds iff the
    /// operand is `Bool.true`.
    IsTrue(ClaimTerm),
    Eq(ClaimSort, ClaimTerm, ClaimTerm),
    Ne(ClaimSort, ClaimTerm, ClaimTerm),
    /// `lhs <= rhs` over `Int`.
    Le(ClaimTerm, ClaimTerm),
    /// `lhs < rhs` over `Int`.
    Lt(ClaimTerm, ClaimTerm),
    Not(Box<ClaimProp>),
    And(Box<ClaimProp>, Box<ClaimProp>),
    Or(Box<ClaimProp>, Box<ClaimProp>),
    Implies(Box<ClaimProp>, Box<ClaimProp>),
}

/// A decoded body-bound claim: the skolem signature plus the substituted body.
#[derive(Clone, PartialEq, Eq, Debug)]
struct BodyBoundClaim {
    /// Declared variables in claim order, with their sorts. Every one becomes
    /// an opaque environment constant.
    variables: Vec<(String, ClaimSort)>,
    body: ClaimProp,
}

/// Why a claim could not be kernel-certified. Returned so callers and the RED
/// fixtures can assert on the *reason*, not merely on `None`: a fail-closed
/// control that declines for an unrelated parse quirk discriminates nothing.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum BodyBoundCertifyError {
    /// The pinned formula is not the body-bound trust-formula schema.
    UnexpectedSchema(String),
    /// The envelope is not well-formed, or is outside the accepted fragment.
    ClaimOutsideFragment(String),
    /// The kernel environment for this claim's signature could not be built.
    EnvironmentRejected,
    /// No proof term could be built for the goal from the accepted rule set.
    /// A FALSE claim lands here — there is no honest proof to build.
    NoProofTerm,
    /// The kernel refused the constructed proof against the constructed goal.
    KernelRejectedProof,
    /// The proof's transitive constant closure reaches an axiom that is neither
    /// one of this claim's skolems nor a foundational Clean axiom.
    ProofClosureNotClean,
    /// Serialization or the deserialized re-check failed.
    PayloadRoundTripRejected,
}

impl std::fmt::Display for BodyBoundCertifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnexpectedSchema(schema) => {
                write!(f, "body-bound claim has schema `{schema}`, not the trust-formula envelope")
            }
            Self::ClaimOutsideFragment(reason) => {
                write!(f, "body-bound claim is outside the kernel-certifiable fragment: {reason}")
            }
            Self::EnvironmentRejected => {
                write!(f, "kernel environment rejected the claim signature")
            }
            Self::NoProofTerm => write!(f, "no kernel proof term exists for this claim's goal"),
            Self::KernelRejectedProof => {
                write!(f, "the clean kernel rejected the constructed proof against the goal")
            }
            Self::ProofClosureNotClean => {
                write!(f, "the proof's axiom closure is not restricted to skolems and foundations")
            }
            Self::PayloadRoundTripRejected => {
                write!(f, "the serialized certificate failed its independent re-check")
            }
        }
    }
}

/// Kernel-certify one compiler-finalized body-bound `ensures` claim.
///
/// `schema`/`payload` are the pinned `trust_ir::ProofFormula` fields of the
/// native proof obligation; `obligation_identity` is the caller's canonical,
/// injective identity for the row the certificate will authorize. Both the
/// canonical claim text and that identity are bound into the lineage digest, so
/// a certificate minted for one row cannot be replayed against another.
///
/// Returns `Ok` only when the Clean kernel accepted a proof of the reconstructed
/// goal with a clean axiom closure and the serialized payload re-checked after a
/// round trip. Every other outcome is an `Err` naming the exact gate that
/// refused; callers keep their existing, weaker authority.
pub fn certify_body_bound_ensures_claim(
    schema: &str,
    payload: &str,
    obligation_identity: &[u8],
) -> Result<trust_ir::ProofEvidence, BodyBoundCertifyError> {
    if schema != trust_types::trust_formula_v1::TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION {
        return Err(BodyBoundCertifyError::UnexpectedSchema(schema.to_string()));
    }
    // Duplicate-key rejection first: two readers must not be able to disagree
    // about which body was committed. The shared validator then enforces the
    // arithmetic-free fragment below both this lane and the trust-wp adapter,
    // and yields the canonical text bound into the lineage.
    let value = trust_types::trust_formula_v1::parse_unique_proof_json_payload(payload)
        .map_err(BodyBoundCertifyError::ClaimOutsideFragment)?;
    let canonical =
        trust_types::trust_formula_v1::canonical_arithmetic_free_trust_formula_v1_payload(&value)
            .map_err(BodyBoundCertifyError::ClaimOutsideFragment)?;

    let claim =
        decode_body_bound_claim(&value).map_err(BodyBoundCertifyError::ClaimOutsideFragment)?;

    let env = build_claim_env(&claim.variables).ok_or(BodyBoundCertifyError::EnvironmentRejected)?;
    let goal = prop_to_expr(&claim.body).ok_or(BodyBoundCertifyError::NoProofTerm)?;
    let proof = prove(&claim.body).ok_or(BodyBoundCertifyError::NoProofTerm)?;

    if TypeChecker::with_context(&env, LocalContext::new()).check_type(&proof, &goal).is_err() {
        return Err(BodyBoundCertifyError::KernelRejectedProof);
    }
    if !proof_axiom_closure_is_clean(&env, &proof, &claim.variables) {
        return Err(BodyBoundCertifyError::ProofClosureNotClean);
    }

    let term_bytes =
        serialize_term(&proof).map_err(|_| BodyBoundCertifyError::PayloadRoundTripRejected)?;
    let context_bytes = crate::canonical_empty_context_bytes()
        .ok_or(BodyBoundCertifyError::PayloadRoundTripRejected)?;
    if !payload_roundtrip_rechecks(&canonical, &claim, &term_bytes) {
        return Err(BodyBoundCertifyError::PayloadRoundTripRejected);
    }

    let lineage = lineage_digest(&term_bytes, &context_bytes, &canonical, obligation_identity);
    Ok(trust_ir::ProofEvidence::CleanCic {
        term: term_bytes,
        context: context_bytes,
        lineage,
        // Same reason as the QF_LIA lane: the pinned TrustIR dispatcher has no
        // obligation-bound external recheck route for this term, so advertising
        // one would be false. The certificate is locally kernel-rechecked.
        kernel_recheck: None,
    })
}

// ---------------------------------------------------------------------------
// Decode
// ---------------------------------------------------------------------------

fn decode_body_bound_claim(value: &Value) -> Result<BodyBoundClaim, String> {
    let object = value.as_object().ok_or("claim is not a JSON object")?;
    // A top-level `result` binding is the FREE-VARIABLE abstraction of the
    // postcondition — the thing the body-bound lane exists to avoid. Only a
    // `let`-bound `result` ties the claim to this body, so refuse the other.
    if object.contains_key("result") {
        return Err("claim carries a top-level `result` binding, so it is not body-bound".into());
    }

    let mut variables = Vec::new();
    let mut sorts: BTreeMap<String, ClaimSort> = BTreeMap::new();
    if let Some(declared) = object.get("variables") {
        for binding in declared.as_array().ok_or("`variables` is not an array")? {
            let binding = binding.as_object().ok_or("a variable binding is not an object")?;
            let name = binding
                .get("name")
                .and_then(Value::as_str)
                .ok_or("a variable binding has no string `name`")?;
            let sort = decode_sort(binding.get("sort").and_then(Value::as_str))?;
            if name == "result" {
                return Err("a declared variable is named `result`".into());
            }
            if sorts.insert(name.to_string(), sort).is_some() {
                return Err(format!("duplicate variable binding `{name}`"));
            }
            variables.push((name.to_string(), sort));
        }
    }

    let body = object.get("body").ok_or("claim has no `body`")?;
    let let_node = body.as_object().ok_or("claim `body` is not an object")?;
    if let_node.get("op").and_then(Value::as_str) != Some("let") {
        return Err("claim body is not the body-bound `let result = ...` form".into());
    }
    if let_node.get("name").and_then(Value::as_str) != Some("result") {
        return Err("claim body binds a name other than `result`".into());
    }
    let result_sort = decode_sort(let_node.get("sort").and_then(Value::as_str))?;
    let defining = let_node.get("value").ok_or("`let` has no `value`")?;
    let (defining_term, defining_sort) =
        decode_term(defining, &sorts, None).map_err(|e| format!("defining expression: {e}"))?;
    if defining_sort != result_sort {
        return Err("the defining expression's sort differs from the declared result sort".into());
    }

    let mut budget = MAX_CLAIM_NODES;
    let inner = let_node.get("body").ok_or("`let` has no `body`")?;
    let body = decode_prop(inner, &sorts, Some(&(defining_term, result_sort)), &mut budget)?;
    Ok(BodyBoundClaim { variables, body })
}

fn decode_sort(sort: Option<&str>) -> Result<ClaimSort, String> {
    match sort {
        Some("int") => Ok(ClaimSort::Int),
        Some("bool") => Ok(ClaimSort::Bool),
        Some(other) => Err(format!("sort `{other}` is outside the int/bool fragment")),
        None => Err("a binding has no string `sort`".into()),
    }
}

/// Decode an atomic operand. `result` resolves to the `let`-bound defining term
/// when one is in scope; that substitution is what makes the goal a statement
/// about THIS body.
fn decode_term(
    value: &Value,
    sorts: &BTreeMap<String, ClaimSort>,
    result: Option<&(ClaimTerm, ClaimSort)>,
) -> Result<(ClaimTerm, ClaimSort), String> {
    let object = value.as_object().ok_or("operand is not an object")?;
    if let Some(literal) = object.get("int") {
        let literal = literal.as_i64().ok_or("`int` literal is not an i64")?;
        return Ok((ClaimTerm::Int(literal), ClaimSort::Int));
    }
    if let Some(literal) = object.get("bool") {
        let literal = literal.as_bool().ok_or("`bool` literal is not a boolean")?;
        return Ok((ClaimTerm::Bool(literal), ClaimSort::Bool));
    }
    if let Some(name) = object.get("var") {
        let name = name.as_str().ok_or("`var` is not a string")?;
        if name == "result" {
            let (term, sort) = result.ok_or("`result` is referenced outside its `let`")?;
            return Ok((term.clone(), *sort));
        }
        let sort = sorts.get(name).ok_or_else(|| format!("undeclared variable `{name}`"))?;
        return Ok((ClaimTerm::Var(name.to_string()), *sort));
    }
    Err("operand is not a variable or a literal".into())
}

fn decode_prop(
    value: &Value,
    sorts: &BTreeMap<String, ClaimSort>,
    result: Option<&(ClaimTerm, ClaimSort)>,
    budget: &mut usize,
) -> Result<ClaimProp, String> {
    *budget = budget.checked_sub(1).ok_or("claim exceeds the node budget")?;
    let object = value.as_object().ok_or("formula node is not an object")?;

    // A leaf in formula position must be bool-sorted; it holds iff it is true.
    if object.contains_key("int") {
        return Err("an integer leaf appears in formula position".into());
    }
    if object.contains_key("bool") || object.contains_key("var") {
        let (term, sort) = decode_term(value, sorts, result)?;
        if sort != ClaimSort::Bool {
            return Err("a non-boolean leaf appears in formula position".into());
        }
        return Ok(match term {
            ClaimTerm::Bool(true) => ClaimProp::True,
            ClaimTerm::Bool(false) => ClaimProp::False,
            other => ClaimProp::IsTrue(other),
        });
    }

    let op = object.get("op").and_then(Value::as_str).ok_or("formula node has no `op`")?;
    match op {
        "not" => {
            let inner = object.get("expr").ok_or("`not` has no `expr`")?;
            Ok(ClaimProp::Not(Box::new(decode_prop(inner, sorts, result, budget)?)))
        }
        "and" | "or" | "implies" => {
            let lhs = object.get("lhs").ok_or("connective has no `lhs`")?;
            let rhs = object.get("rhs").ok_or("connective has no `rhs`")?;
            let lhs = Box::new(decode_prop(lhs, sorts, result, budget)?);
            let rhs = Box::new(decode_prop(rhs, sorts, result, budget)?);
            Ok(match op {
                "and" => ClaimProp::And(lhs, rhs),
                "or" => ClaimProp::Or(lhs, rhs),
                _ => ClaimProp::Implies(lhs, rhs),
            })
        }
        "eq" | "ne" | "lt" | "le" | "gt" | "ge" => {
            let lhs = object.get("lhs").ok_or("comparison has no `lhs`")?;
            let rhs = object.get("rhs").ok_or("comparison has no `rhs`")?;
            let (lhs, lhs_sort) = decode_term(lhs, sorts, result)?;
            let (rhs, rhs_sort) = decode_term(rhs, sorts, result)?;
            if lhs_sort != rhs_sort {
                return Err("a comparison relates operands of different sorts".into());
            }
            match op {
                "eq" => Ok(ClaimProp::Eq(lhs_sort, lhs, rhs)),
                "ne" => Ok(ClaimProp::Ne(lhs_sort, lhs, rhs)),
                _ if lhs_sort != ClaimSort::Int => {
                    Err("an order comparison relates non-integer operands".into())
                }
                // `a > b` IS `b < a` and `a >= b` IS `b <= a`; normalizing here
                // keeps one relation per direction in the goal builder.
                "lt" => Ok(ClaimProp::Lt(lhs, rhs)),
                "le" => Ok(ClaimProp::Le(lhs, rhs)),
                "gt" => Ok(ClaimProp::Lt(rhs, lhs)),
                _ => Ok(ClaimProp::Le(rhs, lhs)),
            }
        }
        other => Err(format!("operator `{other}` is outside the accepted fragment")),
    }
}

// ---------------------------------------------------------------------------
// Goal construction
// ---------------------------------------------------------------------------

/// Injective, collision-free kernel name for a claim variable.
fn skolem_name(raw: &str) -> String {
    let mut encoded = String::from(SKOLEM_PREFIX);
    for byte in raw.as_bytes() {
        encoded.push_str(&format!("{byte:02x}"));
    }
    encoded
}

fn sort_ty(sort: ClaimSort) -> Expr {
    match sort {
        ClaimSort::Int => Expr::const_(Name::from_string("Int"), Vec::new()),
        ClaimSort::Bool => Expr::const_(Name::from_string("Bool"), Vec::new()),
    }
}

/// Kernel term for an operand. `None` only for an integer literal the kernel
/// encoding cannot represent — impossible for the i64 the decoder admits, but
/// threaded rather than asserted so a widened fragment declines instead of
/// panicking inside the compiler's verification pass.
fn term_to_expr(term: &ClaimTerm) -> Option<Expr> {
    match term {
        ClaimTerm::Var(name) => {
            Some(Expr::const_(Name::from_string(&skolem_name(name)), Vec::new()))
        }
        ClaimTerm::Int(value) => super::int_literal_to_kernel(i128::from(*value)),
        ClaimTerm::Bool(true) => Some(Expr::const_(Name::from_string("Bool.true"), Vec::new())),
        ClaimTerm::Bool(false) => Some(Expr::const_(Name::from_string("Bool.false"), Vec::new())),
    }
}

/// `@Eq.{1} ty lhs rhs`. Both `Int` and `Bool` live in `Type 0`, so the level is
/// the same for either sort.
fn eq_prop(sort: ClaimSort, lhs: &ClaimTerm, rhs: &ClaimTerm) -> Option<Expr> {
    Some(Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [sort_ty(sort), term_to_expr(lhs)?, term_to_expr(rhs)?],
    ))
}

fn order_prop(relation: &str, lhs: &ClaimTerm, rhs: &ClaimTerm) -> Option<Expr> {
    Some(Expr::apps(
        Expr::const_(Name::from_string(relation), Vec::new()),
        [term_to_expr(lhs)?, term_to_expr(rhs)?],
    ))
}

fn connective_prop(name: &str, lhs: &ClaimProp, rhs: &ClaimProp) -> Option<Expr> {
    Some(Expr::apps(
        Expr::const_(Name::from_string(name), Vec::new()),
        [prop_to_expr(lhs)?, prop_to_expr(rhs)?],
    ))
}

fn prop_to_expr(prop: &ClaimProp) -> Option<Expr> {
    match prop {
        ClaimProp::True => Some(Expr::const_(Name::from_string("True"), Vec::new())),
        ClaimProp::False => Some(Expr::const_(Name::from_string("False"), Vec::new())),
        ClaimProp::IsTrue(term) => eq_prop(ClaimSort::Bool, term, &ClaimTerm::Bool(true)),
        ClaimProp::Eq(sort, lhs, rhs) => eq_prop(*sort, lhs, rhs),
        ClaimProp::Ne(sort, lhs, rhs) => Some(Expr::app(
            Expr::const_(Name::from_string("Not"), Vec::new()),
            eq_prop(*sort, lhs, rhs)?,
        )),
        ClaimProp::Le(lhs, rhs) => order_prop("Int.le", lhs, rhs),
        ClaimProp::Lt(lhs, rhs) => order_prop("Int.lt", lhs, rhs),
        ClaimProp::Not(inner) => Some(Expr::app(
            Expr::const_(Name::from_string("Not"), Vec::new()),
            prop_to_expr(inner)?,
        )),
        ClaimProp::And(lhs, rhs) => connective_prop("And", lhs, rhs),
        ClaimProp::Or(lhs, rhs) => connective_prop("Or", lhs, rhs),
        // `A → B` as a non-dependent `Pi`. The intuitionistic implication is
        // stronger than the claim's classical one, so proving it is safe.
        ClaimProp::Implies(lhs, rhs) => Some(Expr::pi(
            clean_kernel::BinderInfo::Default,
            prop_to_expr(lhs)?,
            prop_to_expr(rhs)?,
        )),
    }
}

// ---------------------------------------------------------------------------
// Proof construction
// ---------------------------------------------------------------------------

/// Build a proof term for `prop`, or `None` when the accepted rule set cannot
/// close it. This is a *proposer*: the kernel below is what decides whether the
/// result is a proof, so an incomplete prover costs coverage, never soundness.
///
/// The rules are the introduction forms of the connectives plus two
/// reflexivities. Deliberately no case split, no decision procedure, no
/// arithmetic: the body-bound fragment's provable claims are the ones that hold
/// for *every* valuation with no hypotheses in scope, which is exactly the
/// reflexive and structurally-true family.
fn prove(prop: &ClaimProp) -> Option<Expr> {
    match prop {
        ClaimProp::True => Some(Expr::const_(Name::from_string("True.intro"), Vec::new())),
        // `Eq ty t t` — the identity postcondition of a body that returns its
        // own parameter, and of `result == <literal>` against that literal.
        ClaimProp::Eq(sort, lhs, rhs) if lhs == rhs => Some(Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
            [sort_ty(*sort), term_to_expr(lhs)?],
        )),
        ClaimProp::IsTrue(ClaimTerm::Bool(true)) => Some(Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
            [sort_ty(ClaimSort::Bool), term_to_expr(&ClaimTerm::Bool(true))?],
        )),
        // `t <= t` — `ensures result >= x { x }` after substitution.
        ClaimProp::Le(lhs, rhs) if lhs == rhs => Some(Expr::app(
            Expr::const_(Name::from_string("Int.le_refl"), Vec::new()),
            term_to_expr(lhs)?,
        )),
        ClaimProp::And(lhs, rhs) => Some(Expr::apps(
            Expr::const_(Name::from_string("And.intro"), Vec::new()),
            [prop_to_expr(lhs)?, prop_to_expr(rhs)?, prove(lhs)?, prove(rhs)?],
        )),
        ClaimProp::Or(lhs, rhs) => {
            let (left, right) = (prop_to_expr(lhs)?, prop_to_expr(rhs)?);
            if let Some(proof) = prove(lhs) {
                return Some(Expr::apps(
                    Expr::const_(Name::from_string("Or.inl"), Vec::new()),
                    [left, right, proof],
                ));
            }
            Some(Expr::apps(
                Expr::const_(Name::from_string("Or.inr"), Vec::new()),
                [left, right, prove(rhs)?],
            ))
        }
        // The hypothesis is discarded: only an unconditionally true consequent
        // is closed here. A conditional postcondition therefore fails closed
        // rather than being weakened into something that happens to check.
        ClaimProp::Implies(lhs, rhs) => Some(Expr::lam(
            clean_kernel::BinderInfo::Default,
            prop_to_expr(lhs)?,
            prove(rhs)?,
        )),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Zero-trust re-check
// ---------------------------------------------------------------------------

/// The environment the goal and proof are checked in: Clean's Int order theory
/// and its lemmas, `Bool`, the propositional connectives, and one opaque
/// constant per claim variable.
///
/// `init_bool` also installs Clean's ambient `sorryAx` oracle. That is exactly why
/// [`proof_axiom_closure_is_clean`] below is not optional: typing alone would
/// accept a one-node inhabitant of any goal, so admissibility is decided by the
/// term's transitive constant closure, not by the environment's contents.
fn build_claim_env(variables: &[(String, ClaimSort)]) -> Option<Environment> {
    // Memoized: the lemma environment is identical for every claim, and this
    // runs inside the compiler's verification pass on each body-bound row.
    static BASE: std::sync::OnceLock<Option<Environment>> = std::sync::OnceLock::new();
    let mut env = BASE
        .get_or_init(|| {
            let mut env = Environment::default();
            env.init_int_ord_lemmas().ok()?;
            env.init_and().ok()?;
            env.init_bool().ok()?;
            Some(env)
        })
        .clone()?;
    for (name, sort) in variables {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(&skolem_name(name)),
            level_params: Vec::new(),
            type_: sort_ty(*sort),
        })
        .ok()?;
    }
    Some(env)
}

/// Restrict the proof's transitive constant closure to this claim's own
/// skolems and the foundational Clean axioms. A skolem is admissible because it
/// is an opaque constant of the claim's own sort — proving the goal for an
/// arbitrary constant is what makes the statement universal. Any other axiom
/// (`sorryAx`, `trustedAy`, a domain assumption) means the term did not earn its
/// goal, so it is refused.
fn proof_axiom_closure_is_clean(
    env: &Environment,
    term: &Expr,
    variables: &[(String, ClaimSort)],
) -> bool {
    use clean_kernel::env::ConstantKind;

    let permitted: BTreeMap<Name, Expr> = variables
        .iter()
        .map(|(name, sort)| (Name::from_string(&skolem_name(name)), sort_ty(*sort)))
        .collect();

    let mut work = Vec::new();
    if !super::collect_const_names(term, &mut work) {
        return false;
    }
    let mut seen: BTreeSet<Name> = BTreeSet::new();
    while let Some(name) = work.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        let Some(info) = env.get_const(&name) else {
            return false;
        };
        if info.kind == ConstantKind::Axiom {
            let is_claim_skolem = permitted.get(&name) == Some(&info.type_);
            let is_foundational =
                FOUNDATIONAL_AXIOMS.iter().any(|allowed| name == Name::from_string(allowed));
            if !is_claim_skolem && !is_foundational {
                return false;
            }
        }
        if !super::collect_const_names(&info.type_, &mut work) {
            return false;
        }
        if let Some(value) = &info.value
            && !super::collect_const_names(value, &mut work)
        {
            return false;
        }
    }
    true
}

/// The check an independent consumer runs, from the two artifacts the
/// certificate is bound to and nothing else: re-decode the claim from the
/// canonical payload text, rebuild the environment and goal from that decode,
/// deserialize the term, and re-check it.
///
/// Re-decoding rather than reusing the in-memory claim is the point — it is what
/// makes the lineage's claim text, not this process's parse of it, the thing the
/// certificate answers to.
fn payload_roundtrip_rechecks(
    canonical_claim: &str,
    claim: &BodyBoundClaim,
    term_bytes: &[u8],
) -> bool {
    let Ok(value) = serde_json::from_str::<Value>(canonical_claim) else {
        return false;
    };
    let Ok(replayed) = decode_body_bound_claim(&value) else {
        return false;
    };
    if &replayed != claim {
        return false;
    }
    let Ok(term) = deserialize_term(term_bytes) else {
        return false;
    };
    let Some(env) = build_claim_env(&replayed.variables) else {
        return false;
    };
    let Some(goal) = prop_to_expr(&replayed.body) else {
        return false;
    };
    TypeChecker::with_context(&env, LocalContext::new()).check_type(&term, &goal).is_ok()
        && proof_axiom_closure_is_clean(&env, &term, &replayed.variables)
}

/// SHA-256 lineage over the term, the empty closed context, the canonical claim
/// text, and the caller's row identity. Each field is tagged and
/// length-prefixed, so the encoding is injective and a certificate cannot be
/// transplanted onto another claim or another row.
fn lineage_digest(
    term_bytes: &[u8],
    context_bytes: &[u8],
    canonical_claim: &str,
    obligation_identity: &[u8],
) -> trust_ir::ProofDigest {
    let mut hasher = Sha256::new();
    hasher.update(LINEAGE_DOMAIN.as_bytes());
    for (tag, field) in [
        (b"term:".as_slice(), term_bytes),
        (b"ctx:".as_slice(), context_bytes),
        (b"claim:".as_slice(), canonical_claim.as_bytes()),
        (b"row:".as_slice(), obligation_identity),
    ] {
        hasher.update(tag);
        hasher.update((field.len() as u64).to_le_bytes());
        hasher.update(field);
    }
    let digest = hasher.finalize();
    let mut bytes = [0u8; 32];
    bytes.copy_from_slice(&digest);
    trust_ir::ProofDigest::sha256(bytes)
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    const SCHEMA: &str = trust_types::trust_formula_v1::TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION;

    fn envelope(variables: Value, result_sort: &str, defining: Value, body: Value) -> String {
        json!({
            "schema": SCHEMA,
            "variables": variables,
            "body": {
                "op": "let",
                "name": "result",
                "sort": result_sort,
                "value": defining,
                "body": body,
            },
        })
        .to_string()
    }

    /// `fn bool_identity(flag: bool) -> bool ensures result == flag { flag }` —
    /// the shipped `s1c_body_bound_bool_identity_receipt` fixture's claim.
    fn bool_identity_payload() -> String {
        envelope(
            json!([{ "name": "flag", "sort": "bool" }]),
            "bool",
            json!({ "var": "flag" }),
            json!({ "op": "eq", "lhs": { "var": "result" }, "rhs": { "var": "flag" } }),
        )
    }

    /// `fn ge_refl(x: u64) -> u64 ensures result >= x { x }` — the blueprint's
    /// worked example.
    fn ge_refl_payload() -> String {
        envelope(
            json!([{ "name": "x", "sort": "int" }]),
            "int",
            json!({ "var": "x" }),
            json!({ "op": "ge", "lhs": { "var": "result" }, "rhs": { "var": "x" } }),
        )
    }

    #[test]
    fn bool_identity_claim_is_kernel_certified() {
        let evidence = certify_body_bound_ensures_claim(SCHEMA, &bool_identity_payload(), b"row-1")
            .expect("the bool identity postcondition is kernel-provable");
        assert!(matches!(evidence, trust_ir::ProofEvidence::CleanCic { .. }));
    }

    #[test]
    fn ge_refl_claim_is_kernel_certified() {
        certify_body_bound_ensures_claim(SCHEMA, &ge_refl_payload(), b"row-1")
            .expect("`result >= x` for a body returning `x` is kernel-provable");
    }

    #[test]
    fn conjunction_of_reflexive_atoms_is_kernel_certified() {
        let payload = envelope(
            json!([{ "name": "x", "sort": "int" }]),
            "int",
            json!({ "var": "x" }),
            json!({
                "op": "and",
                "lhs": { "op": "ge", "lhs": { "var": "result" }, "rhs": { "var": "x" } },
                "rhs": { "op": "eq", "lhs": { "var": "result" }, "rhs": { "var": "x" } },
            }),
        );
        certify_body_bound_ensures_claim(SCHEMA, &payload, b"row-1")
            .expect("a conjunction of reflexive atoms is kernel-provable");
    }

    /// The implication shape exercises the one proof rule that builds a binder
    /// (`fun _ : P => q`), so it also covers the term's serialization.
    #[test]
    fn implication_with_a_provable_consequent_is_kernel_certified() {
        let atom = json!({ "op": "eq", "lhs": { "var": "result" }, "rhs": { "var": "x" } });
        let payload = envelope(
            json!([{ "name": "x", "sort": "int" }]),
            "int",
            json!({ "var": "x" }),
            json!({ "op": "implies", "lhs": atom, "rhs": atom }),
        );
        certify_body_bound_ensures_claim(SCHEMA, &payload, b"row-1")
            .expect("an implication whose consequent is reflexive is kernel-provable");
    }

    /// RED. A FALSE postcondition for the same body: `result > x` cannot hold
    /// when the body returns `x`. The lane must refuse, and must refuse because
    /// there is no proof of THIS goal — not because the envelope failed to
    /// parse.
    #[test]
    fn strictly_greater_than_own_argument_is_refused_for_the_right_reason() {
        let payload = envelope(
            json!([{ "name": "x", "sort": "int" }]),
            "int",
            json!({ "var": "x" }),
            json!({ "op": "gt", "lhs": { "var": "result" }, "rhs": { "var": "x" } }),
        );
        let error = certify_body_bound_ensures_claim(SCHEMA, &payload, b"row-1")
            .expect_err("`result > x` is false for a body returning `x`");
        assert_eq!(
            error,
            BodyBoundCertifyError::NoProofTerm,
            "the refusal must be the absence of a proof of `x < x`, not a decode failure"
        );
        // Non-vacuity: the SAME envelope with the true `>=` DOES certify, so the
        // refusal above discriminates the false claim from the true one rather
        // than rejecting the whole shape.
        certify_body_bound_ensures_claim(SCHEMA, &ge_refl_payload(), b"row-1")
            .expect("the true sibling of the refused claim still certifies");
    }

    /// RED. A forged claim: the postcondition names a DIFFERENT variable than
    /// the one the body returns. `result == y` for `{ x }` is not valid, and no
    /// reflexivity closes it.
    #[test]
    fn postcondition_about_another_parameter_is_refused() {
        let payload = envelope(
            json!([{ "name": "x", "sort": "int" }, { "name": "y", "sort": "int" }]),
            "int",
            json!({ "var": "x" }),
            json!({ "op": "eq", "lhs": { "var": "result" }, "rhs": { "var": "y" } }),
        );
        assert_eq!(
            certify_body_bound_ensures_claim(SCHEMA, &payload, b"row-1"),
            Err(BodyBoundCertifyError::NoProofTerm)
        );
    }

    /// RED. The free-variable abstraction (`result` as a top-level binding
    /// rather than `let`-bound to the body) proves a postcondition about an
    /// arbitrary return value. It must never reach the kernel on this lane.
    #[test]
    fn free_variable_result_binding_is_refused() {
        let payload = json!({
            "schema": SCHEMA,
            "variables": [{ "name": "x", "sort": "int" }],
            "result": { "name": "result", "sort": "int" },
            "body": { "op": "ge", "lhs": { "result": true }, "rhs": { "var": "x" } },
        })
        .to_string();
        let error = certify_body_bound_ensures_claim(SCHEMA, &payload, b"row-1").unwrap_err();
        assert!(
            matches!(error, BodyBoundCertifyError::ClaimOutsideFragment(ref reason)
                if reason.contains("body-bound")),
            "expected the not-body-bound refusal, got {error:?}"
        );
    }

    /// RED. Arithmetic is the confirmed false-proof vector (`result + 1 > result`
    /// is Int-valid and false at `u64::MAX`). The shared ingress validator must
    /// refuse it before any goal is built.
    #[test]
    fn arithmetic_in_the_claim_is_refused_at_ingress() {
        let payload = envelope(
            json!([{ "name": "x", "sort": "int" }]),
            "int",
            json!({ "var": "x" }),
            json!({
                "op": "gt",
                "lhs": { "op": "add", "lhs": { "var": "result" }, "rhs": { "int": 1 } },
                "rhs": { "var": "result" },
            }),
        );
        assert!(matches!(
            certify_body_bound_ensures_claim(SCHEMA, &payload, b"row-1"),
            Err(BodyBoundCertifyError::ClaimOutsideFragment(_))
        ));
    }

    /// The honest residue, pinned. `3 <= 7` is TRUE but the prover has no rule
    /// for a literal order comparison, so the whole claim declines and the row
    /// keeps its `Trusted` authority. This is the family `BodyBoundNativeReplay`
    /// still carries, and it must decline rather than be closed by guesswork.
    #[test]
    fn a_true_claim_outside_the_rule_set_declines_instead_of_guessing() {
        let payload = envelope(
            json!([{ "name": "x", "sort": "int" }]),
            "int",
            json!({ "var": "x" }),
            json!({
                "op": "and",
                "lhs": { "op": "ge", "lhs": { "var": "result" }, "rhs": { "var": "x" } },
                "rhs": { "op": "le", "lhs": { "int": 3 }, "rhs": { "int": 7 } },
            }),
        );
        assert_eq!(
            certify_body_bound_ensures_claim(SCHEMA, &payload, b"row-1"),
            Err(BodyBoundCertifyError::NoProofTerm)
        );
    }

    #[test]
    fn a_foreign_schema_is_refused() {
        assert_eq!(
            certify_body_bound_ensures_claim("TrustWpPureExprV1", &ge_refl_payload(), b"row-1"),
            Err(BodyBoundCertifyError::UnexpectedSchema("TrustWpPureExprV1".to_string()))
        );
    }

    /// RED. `init_bool` puts Clean's ambient `sorryAx` in the environment, so
    /// the kernel WILL type an oracle-rooted inhabitant of the goal. The closure
    /// audit is the gate that refuses it; this pins that the gate, not the type
    /// checker, is what stops an oracle proof.
    #[test]
    fn a_sorry_rooted_proof_is_refused_by_the_closure_audit() {
        let claim = decode_body_bound_claim(
            &serde_json::from_str(&ge_refl_payload()).expect("valid claim JSON"),
        )
        .expect("the ge_refl claim decodes");
        let env = build_claim_env(&claim.variables).expect("environment builds");
        let goal = prop_to_expr(&claim.body).expect("the goal is constructible");

        // `sorryAx : {α : Sort u} → Bool → α` — the ambient oracle `init_bool`
        // pulls in. Instantiated at the goal it inhabits anything.
        let forged = Expr::apps(
            Expr::const_(Name::from_string("sorryAx"), vec![Level::zero()]),
            [goal.clone(), Expr::const_(Name::from_string("Bool.true"), Vec::new())],
        );
        assert!(
            TypeChecker::with_context(&env, LocalContext::new())
                .check_type(&forged, &goal)
                .is_ok(),
            "the ambient oracle really does type-check, which is why the audit exists"
        );
        assert!(
            !proof_axiom_closure_is_clean(&env, &forged, &claim.variables),
            "a sorry-rooted term must fail the axiom-closure audit"
        );
    }

    /// Decode a payload and return `(env, goal)` for the kernel-level controls.
    fn env_and_goal(payload: &str) -> (Environment, Expr, BodyBoundClaim) {
        let claim =
            decode_body_bound_claim(&serde_json::from_str(payload).expect("valid claim JSON"))
                .expect("claim decodes");
        let env = build_claim_env(&claim.variables).expect("environment builds");
        let goal = prop_to_expr(&claim.body).expect("the goal is constructible");
        (env, goal, claim)
    }

    /// RED, at the KERNEL rather than at the prover. The lane's own refusal of
    /// `result > x` is the prover having no rule, which on its own would not
    /// show the kernel discriminates anything. Hand the kernel the reflexivity
    /// term anyway and watch it reject — while the SAME term against the true
    /// `<=` goal in the SAME environment is accepted.
    #[test]
    fn the_kernel_rejects_a_reflexivity_proof_of_a_false_order_goal() {
        let false_payload = envelope(
            json!([{ "name": "x", "sort": "int" }]),
            "int",
            json!({ "var": "x" }),
            json!({ "op": "gt", "lhs": { "var": "result" }, "rhs": { "var": "x" } }),
        );
        let (env, false_goal, claim) = env_and_goal(&false_payload);
        let refl = Expr::app(
            Expr::const_(Name::from_string("Int.le_refl"), Vec::new()),
            term_to_expr(&ClaimTerm::Var("x".to_string())).expect("skolem term"),
        );

        let rejection = TypeChecker::with_context(&env, LocalContext::new())
            .check_type(&refl, &false_goal)
            .expect_err("`x <= x` is not a proof of `x < x`");
        // Pin the SHAPE of the rejection: a type mismatch between the term's
        // own type and the goal, not a missing declaration or a malformed term.
        // Observed shape: `TypeMismatch { expected: Int.lt x x, inferred:
        // Int.le x x }` — the goal and the term's own type, not a lookup or
        // elaboration failure.
        let rendered = format!("{rejection:?}");
        assert!(
            rendered.contains("Mismatch") || rendered.contains("mismatch"),
            "expected a type mismatch, got {rendered}"
        );

        let (_, true_goal, _) = env_and_goal(&ge_refl_payload());
        assert!(
            TypeChecker::with_context(&env, LocalContext::new())
                .check_type(&refl, &true_goal)
                .is_ok(),
            "the same term against the true goal must check — otherwise the rejection above \
             discriminates nothing"
        );
        assert!(proof_axiom_closure_is_clean(&env, &refl, &claim.variables));
    }

    /// RED. A proof built for one claim's skolem must not authorize another
    /// claim's goal, even though both are reflexivity of `<=`.
    #[test]
    fn the_kernel_rejects_a_proof_transplanted_from_another_claim() {
        let other = envelope(
            json!([{ "name": "y", "sort": "int" }]),
            "int",
            json!({ "var": "y" }),
            json!({ "op": "ge", "lhs": { "var": "result" }, "rhs": { "var": "y" } }),
        );
        let (env, goal, _) = env_and_goal(&other);
        let foreign = Expr::app(
            Expr::const_(Name::from_string("Int.le_refl"), Vec::new()),
            term_to_expr(&ClaimTerm::Var("x".to_string())).expect("skolem term"),
        );
        assert!(
            TypeChecker::with_context(&env, LocalContext::new())
                .check_type(&foreign, &goal)
                .is_err(),
            "`x <= x` must not prove `y <= y`"
        );
    }

    /// The lineage binds the row identity, so a certificate minted for one row
    /// is a different artifact from the same claim's certificate on another.
    #[test]
    fn lineage_binds_the_row_identity() {
        let one = certify_body_bound_ensures_claim(SCHEMA, &ge_refl_payload(), b"row-1").unwrap();
        let two = certify_body_bound_ensures_claim(SCHEMA, &ge_refl_payload(), b"row-2").unwrap();
        let (
            trust_ir::ProofEvidence::CleanCic { lineage: one, .. },
            trust_ir::ProofEvidence::CleanCic { lineage: two, .. },
        ) = (&one, &two)
        else {
            panic!("both mints are CleanCic evidence");
        };
        assert_ne!(one, two);
    }
}

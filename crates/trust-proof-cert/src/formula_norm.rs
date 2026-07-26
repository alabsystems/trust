// trust-proof-cert formula normalization
//
// Canonical normalization for Formula comparison. Supports AC flattening,
// commutativity normalization, double negation elimination, constant folding,
// basic arithmetic identities, and alpha-normalization for quantifiers.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::{cmp::Ordering, collections::BTreeSet};

use trust_types::{Formula, Sort};

// ---------------------------------------------------------------------------
// Sort key (NOT a public Ord impl on Formula)
// ---------------------------------------------------------------------------

/// Discriminant tag for formula sort key ordering.
/// Lower values sort first.
fn variant_tag(f: &Formula) -> u16 {
    match f {
        Formula::Bool(false) => 0,
        Formula::Bool(true) => 1,
        Formula::Int(_) => 2,
        Formula::UInt(_) => 3,
        Formula::BitVec { .. } => 4,
        Formula::Var(..) => 5,
        Formula::Not(_) => 10,
        Formula::And(_) => 11,
        Formula::Or(_) => 12,
        Formula::Implies(..) => 13,
        Formula::Eq(..) => 20,
        Formula::Lt(..) => 21,
        Formula::Le(..) => 22,
        Formula::Gt(..) => 23,
        Formula::Ge(..) => 24,
        Formula::Add(..) => 30,
        Formula::Sub(..) => 31,
        Formula::Mul(..) => 32,
        Formula::Div(..) => 33,
        Formula::Rem(..) => 34,
        Formula::Neg(_) => 35,
        // Per-operation BV variants
        Formula::BvAdd(..) => 40,
        Formula::BvSub(..) => 41,
        Formula::BvMul(..) => 42,
        Formula::BvUDiv(..) => 43,
        Formula::BvSDiv(..) => 44,
        Formula::BvURem(..) => 45,
        Formula::BvSRem(..) => 46,
        Formula::BvAnd(..) => 47,
        Formula::BvOr(..) => 48,
        Formula::BvXor(..) => 49,
        Formula::BvNot(..) => 50,
        Formula::BvShl(..) => 51,
        Formula::BvLShr(..) => 52,
        Formula::BvAShr(..) => 53,
        Formula::BvULt(..) => 60,
        Formula::BvULe(..) => 61,
        Formula::BvSLt(..) => 62,
        Formula::BvSLe(..) => 63,
        Formula::BvToInt(..) => 70,
        Formula::IntToBv(..) => 71,
        Formula::BvExtract { .. } => 72,
        Formula::BvConcat(..) => 73,
        Formula::BvZeroExt(..) => 74,
        Formula::BvSignExt(..) => 75,
        Formula::Ite(..) => 80,
        Formula::Forall(..) => 90,
        Formula::Exists(..) => 91,
        Formula::Select(..) => 100,
        Formula::Store(..) => 101,
        // Catch-all for #[non_exhaustive] future variants
        _ => 999,
    }
}

/// Custom sort key for normalization ordering.
///
/// This is intentionally NOT a public `Ord` impl on `Formula` to avoid
/// implying semantic meaning. Used only within normalization.
pub(crate) fn formula_sort_key(a: &Formula, b: &Formula) -> Ordering {
    let tag_a = variant_tag(a);
    let tag_b = variant_tag(b);
    let tag_cmp = tag_a.cmp(&tag_b);
    if tag_cmp != Ordering::Equal {
        return tag_cmp;
    }

    // Same variant — compare contents
    match (a, b) {
        (Formula::Bool(x), Formula::Bool(y)) => x.cmp(y),
        (Formula::Int(x), Formula::Int(y)) => x.cmp(y),
        (Formula::UInt(x), Formula::UInt(y)) => x.cmp(y),
        (Formula::BitVec { value: v1, width: w1 }, Formula::BitVec { value: v2, width: w2 }) => {
            w1.cmp(w2).then_with(|| v1.cmp(v2))
        }
        (Formula::Var(n1, s1), Formula::Var(n2, s2)) => n1.cmp(n2).then_with(|| sort_cmp(s1, s2)),
        // For compound formulas, compare children recursively
        _ => {
            let ca = a.children();
            let cb = b.children();
            let len_cmp = ca.len().cmp(&cb.len());
            if len_cmp != Ordering::Equal {
                return len_cmp;
            }
            for (x, y) in ca.iter().zip(cb.iter()) {
                let child_cmp = formula_sort_key(x, y);
                if child_cmp != Ordering::Equal {
                    return child_cmp;
                }
            }
            Ordering::Equal
        }
    }
}

/// Compare sorts for ordering (used in sort key).
fn sort_cmp(a: &Sort, b: &Sort) -> Ordering {
    // Leverage the existing Ord impl on Sort
    a.cmp(b)
}

// ---------------------------------------------------------------------------
// Normalization
// ---------------------------------------------------------------------------

/// Normalize a formula to canonical form.
///
/// Normalization rules applied (bottom-up):
/// - Flatten nested `And`/`Or`
/// - AC flattening for `Add`, `Mul`, `BvAdd`, `BvMul`, `BvAnd`, `BvOr`, `BvXor`
/// - Sort commutative operands using `formula_sort_key`
/// - Double negation elimination: `Not(Not(x))` -> `x`
/// - Constant folding: `And([true, x])` -> `x`, `Or([false, x])` -> `x`
/// - Basic arithmetic identities: `x + 0` -> `x`, `x * 1` -> `x`, `x * 0` -> `0`
/// - Commutativity normalization for `Eq`: order operands by sort key
/// - Alpha-normalization for quantifiers: rename bound vars to `_q0`, `_q1`, ...
#[must_use]
pub fn normalize(formula: &Formula) -> Formula {
    let mut counter = 0;
    normalize_inner(formula, &mut counter)
}

fn normalize_inner(formula: &Formula, counter: &mut usize) -> Formula {
    // Bottom-up: normalize children first, then apply rules at this node
    let normalized_children = match formula {
        // Leaves
        Formula::Bool(_)
        | Formula::Int(_)
        | Formula::UInt(_)
        | Formula::BitVec { .. }
        | Formula::Var(..) => {
            return formula.clone();
        }

        // Quantifiers get special alpha-normalization
        Formula::Forall(bindings, body) => {
            return normalize_quantifier(true, bindings, body, counter);
        }
        Formula::Exists(bindings, body) => {
            return normalize_quantifier(false, bindings, body, counter);
        }

        // Everything else: normalize children via map_children
        _ => formula.clone().map_children(&mut |child| normalize_inner(&child, counter)),
    };

    // Apply simplification rules at this node
    simplify(normalized_children)
}

/// Alpha-normalize quantifiers by renaming bound variables to `_q0`, `_q1`, ...
fn normalize_quantifier(
    is_forall: bool,
    bindings: &[(trust_types::Symbol, Sort)],
    body: &Formula,
    counter: &mut usize,
) -> Formula {
    // Build renamed bindings and substitution map
    let mut renamed_body = body.clone();
    let mut new_bindings: Vec<(trust_types::Symbol, Sort)> = Vec::with_capacity(bindings.len());

    for (name, sort) in bindings {
        let new_name = format!("_q{counter}");
        *counter += 1;
        renamed_body = renamed_body.rename_var(name.as_str(), &new_name);
        new_bindings.push((trust_types::Symbol::intern(&new_name), sort.clone()));
    }

    // Normalize the renamed body
    let normalized_body = normalize_inner(&renamed_body, counter);

    if is_forall {
        Formula::Forall(new_bindings, Box::new(normalized_body))
    } else {
        Formula::Exists(new_bindings, Box::new(normalized_body))
    }
}

/// Apply simplification rules to a single node (children already normalized).
fn simplify(f: Formula) -> Formula {
    match f {
        // Double negation elimination
        Formula::Not(inner) => {
            if let Formula::Not(inner2) = *inner {
                return *inner2;
            }
            Formula::Not(inner)
        }

        // And: flatten, constant fold, sort
        Formula::And(terms) => simplify_and(terms),

        // Or: flatten, constant fold, sort
        Formula::Or(terms) => simplify_or(terms),

        // Eq: normalize operand order
        Formula::Eq(a, b) => {
            if formula_sort_key(&a, &b) == Ordering::Greater {
                Formula::Eq(b, a)
            } else {
                Formula::Eq(a, b)
            }
        }

        // Add: commutative normalization + identity
        Formula::Add(a, b) => {
            // x + 0 -> x
            if is_zero(&b) {
                return *a;
            }
            if is_zero(&a) {
                return *b;
            }
            // Sort operands
            if formula_sort_key(&a, &b) == Ordering::Greater {
                Formula::Add(b, a)
            } else {
                Formula::Add(a, b)
            }
        }

        // Mul: commutative normalization + identity
        Formula::Mul(a, b) => {
            // x * 0 -> 0
            if is_zero(&a) {
                return *a;
            }
            if is_zero(&b) {
                return *b;
            }
            // x * 1 -> x
            if is_one(&b) {
                return *a;
            }
            if is_one(&a) {
                return *b;
            }
            // Sort operands
            if formula_sort_key(&a, &b) == Ordering::Greater {
                Formula::Mul(b, a)
            } else {
                Formula::Mul(a, b)
            }
        }

        // BvAdd: commutative normalization
        Formula::BvAdd(a, b, w) => {
            if formula_sort_key(&a, &b) == Ordering::Greater {
                Formula::BvAdd(b, a, w)
            } else {
                Formula::BvAdd(a, b, w)
            }
        }

        // Legacy BvMul: commutative normalization
        Formula::BvMul(a, b, w) => {
            if formula_sort_key(&a, &b) == Ordering::Greater {
                Formula::BvMul(b, a, w)
            } else {
                Formula::BvMul(a, b, w)
            }
        }

        // Legacy BvAnd: commutative normalization
        Formula::BvAnd(a, b, w) => {
            if formula_sort_key(&a, &b) == Ordering::Greater {
                Formula::BvAnd(b, a, w)
            } else {
                Formula::BvAnd(a, b, w)
            }
        }

        // Legacy BvOr: commutative normalization
        Formula::BvOr(a, b, w) => {
            if formula_sort_key(&a, &b) == Ordering::Greater {
                Formula::BvOr(b, a, w)
            } else {
                Formula::BvOr(a, b, w)
            }
        }

        // Legacy BvXor: commutative normalization
        Formula::BvXor(a, b, w) => {
            if formula_sort_key(&a, &b) == Ordering::Greater {
                Formula::BvXor(b, a, w)
            } else {
                Formula::BvXor(a, b, w)
            }
        }

        // Everything else passes through
        other => other,
    }
}

/// Flatten and simplify And.
fn simplify_and(terms: Vec<Formula>) -> Formula {
    let mut flat = Vec::new();
    for t in terms {
        match t {
            Formula::And(inner) => flat.extend(inner),
            Formula::Bool(true) => {} // identity: skip
            f => flat.push(f),
        }
    }

    // Short-circuit: if any is false, result is false
    if flat.iter().any(|t| matches!(t, Formula::Bool(false))) {
        return Formula::Bool(false);
    }

    match flat.len() {
        0 => Formula::Bool(true),
        1 => flat.into_iter().next().expect("len is 1"),
        _ => {
            flat.sort_by(formula_sort_key);
            Formula::And(flat)
        }
    }
}

/// Flatten and simplify Or.
fn simplify_or(terms: Vec<Formula>) -> Formula {
    let mut flat = Vec::new();
    for t in terms {
        match t {
            Formula::Or(inner) => flat.extend(inner),
            Formula::Bool(false) => {} // identity: skip
            f => flat.push(f),
        }
    }

    // Short-circuit: if any is true, result is true
    if flat.iter().any(|t| matches!(t, Formula::Bool(true))) {
        return Formula::Bool(true);
    }

    match flat.len() {
        0 => Formula::Bool(false),
        1 => flat.into_iter().next().expect("len is 1"),
        _ => {
            flat.sort_by(formula_sort_key);
            Formula::Or(flat)
        }
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn is_zero(f: &Formula) -> bool {
    matches!(f, Formula::Int(0) | Formula::UInt(0))
}

fn is_one(f: &Formula) -> bool {
    matches!(f, Formula::Int(1) | Formula::UInt(1))
}

// ---------------------------------------------------------------------------
// Normalized equality
// ---------------------------------------------------------------------------

/// Structural equality after normalization.
///
/// Named `normalized_equal` (not `semantically_equal`) since normalization
/// is incomplete — ay remains the source of truth for full semantic equivalence.
#[must_use]
pub fn normalized_equal(a: &Formula, b: &Formula) -> bool {
    normalize(a) == normalize(b)
}

/// Syntactic formula implication check (sound, incomplete).
#[must_use]
pub fn formula_subsumes(stronger: &Formula, weaker: &Formula) -> bool {
    let stronger = normalize(stronger);
    let weaker = normalize(weaker);
    formula_subsumes_normalized(&stronger, &weaker)
}

fn formula_subsumes_normalized(stronger: &Formula, weaker: &Formula) -> bool {
    if stronger == weaker
        || matches!(stronger, Formula::Bool(true) | Formula::Bool(false))
        || matches!(weaker, Formula::Bool(true))
    {
        return true;
    }

    if let Formula::And(terms) = stronger
        && terms.iter().any(|term| formula_subsumes_normalized(term, weaker))
    {
        return true;
    }

    if let Formula::Or(terms) = weaker
        && terms.iter().any(|term| formula_subsumes_normalized(stronger, term))
    {
        return true;
    }

    false
}

// ---------------------------------------------------------------------------
// SemanticProperty
// ---------------------------------------------------------------------------

use serde::{Deserialize, Serialize};

/// A property with semantic meaning, wrapping a formula.
///
/// Combines a human-readable label with the actual formula it represents.
/// Does NOT derive `Hash` since `Formula` lacks `Hash`. Use `label` for
/// hashing in collections.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticProperty {
    /// Human-readable label (e.g., "precondition", "postcondition", "invariant").
    pub label: String,
    /// The formula expressing this property.
    pub formula: Formula,
    /// The semantic category of this property.
    pub kind: PropertyKind,
}

/// Categorization of semantic properties for proof composition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum PropertyKind {
    Precondition,
    Postcondition,
    Invariant,
    LoopInvariant,
    Assertion,
    TypeRefinement,
    FrameCondition,
}

impl SemanticProperty {
    /// Create a new semantic property.
    #[must_use]
    pub fn new(label: impl Into<String>, formula: Formula, kind: PropertyKind) -> Self {
        Self { label: label.into(), formula, kind }
    }

    /// Create a semantic property from a label with a trivially true formula.
    /// Useful for backward compatibility with `Property(String)`.
    #[must_use]
    pub fn from_label(label: impl Into<String>) -> Self {
        Self { label: label.into(), formula: Formula::Bool(true), kind: PropertyKind::Assertion }
    }

    /// Check if two semantic properties are equivalent after normalization.
    #[must_use]
    pub fn normalized_eq(&self, other: &Self) -> bool {
        self.label == other.label
            && self.kind == other.kind
            && normalized_equal(&self.formula, &other.formula)
    }

    /// Syntactic subsumption check: does self logically imply other?
    ///
    /// This is a conservative check based on normalized formula structure.
    /// Returns true only when we can syntactically determine implication.
    /// Returns false when unsure (the caller can fall back to SMT).
    ///
    /// Subsumption rules:
    /// - true subsumes everything
    /// - P subsumes P (reflexive)
    /// - P subsumes true
    /// - And([..., P, ...]) subsumes P (conjunction implies conjunct)
    /// - false subsumes everything (ex falso quodlibet)
    /// - P subsumes Or([..., P, ...]) (disjunct implies disjunction)
    #[must_use]
    pub fn subsumes(&self, other: &Self) -> bool {
        self.label == other.label
            && self.kind == other.kind
            && formula_subsumes(&self.formula, &other.formula)
    }

    // Trust: BTreeMap for deterministic certificate output
    /// Collect the free variables in this property's formula.
    #[must_use]
    pub fn free_variables(&self) -> BTreeSet<String> {
        self.formula.free_variables().into_iter().collect()
    }
}

impl From<super::composition::Property> for SemanticProperty {
    fn from(p: super::composition::Property) -> Self {
        Self::from_label(p.0)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{Formula, Sort};

    fn var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    fn bv_var(name: &str, w: u32) -> Formula {
        Formula::Var(name.into(), Sort::BitVec(w))
    }

    // -- Idempotency --

    #[test]
    fn test_normalize_idempotent_simple() {
        let f = Formula::And(vec![
            Formula::Not(Box::new(var("x"))),
            Formula::Or(vec![var("y"), Formula::Bool(false)]),
        ]);
        let n1 = normalize(&f);
        let n2 = normalize(&n1);
        assert_eq!(n1, n2, "normalize must be idempotent");
    }

    #[test]
    fn test_normalize_idempotent_quantifier() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)))),
        );
        let n1 = normalize(&f);
        let n2 = normalize(&n1);
        assert_eq!(n1, n2, "normalize must be idempotent for quantifiers");
    }

    // -- Commutativity --

    #[test]
    fn test_commutative_add() {
        let a = Formula::Add(Box::new(var("x")), Box::new(Formula::Int(1)));
        let b = Formula::Add(Box::new(Formula::Int(1)), Box::new(var("x")));
        assert!(normalized_equal(&a, &b));
    }

    #[test]
    fn test_commutative_mul() {
        let a = Formula::Mul(Box::new(var("a")), Box::new(var("b")));
        let b = Formula::Mul(Box::new(var("b")), Box::new(var("a")));
        assert!(normalized_equal(&a, &b));
    }

    #[test]
    fn test_commutative_eq() {
        let a = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let b = Formula::Eq(Box::new(Formula::Int(0)), Box::new(var("x")));
        assert!(normalized_equal(&a, &b));
    }

    // -- AC flattening --

    #[test]
    fn test_ac_flatten_and() {
        let nested = Formula::And(vec![Formula::And(vec![var("a"), var("b")]), var("c")]);
        let flat = Formula::And(vec![var("a"), var("b"), var("c")]);
        assert!(normalized_equal(&nested, &flat));
    }

    #[test]
    fn test_ac_flatten_or() {
        let nested = Formula::Or(vec![Formula::Or(vec![var("a"), var("b")]), var("c")]);
        let flat = Formula::Or(vec![var("a"), var("b"), var("c")]);
        assert!(normalized_equal(&nested, &flat));
    }

    // -- Alpha normalization --

    #[test]
    fn test_alpha_normalize_forall() {
        let f1 = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)))),
        );
        let f2 = Formula::Forall(
            vec![("y".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(0)))),
        );
        assert!(normalized_equal(&f1, &f2));
    }

    #[test]
    fn test_alpha_normalize_exists() {
        let f1 = Formula::Exists(
            vec![("a".into(), Sort::Int)],
            Box::new(Formula::Lt(Box::new(var("a")), Box::new(Formula::Int(10)))),
        );
        let f2 = Formula::Exists(
            vec![("z".into(), Sort::Int)],
            Box::new(Formula::Lt(Box::new(var("z")), Box::new(Formula::Int(10)))),
        );
        assert!(normalized_equal(&f1, &f2));
    }

    // -- BV commutativity --

    #[test]
    fn test_bv_add_commutative() {
        let a = Formula::BvAdd(Box::new(bv_var("a", 32)), Box::new(bv_var("b", 32)), 32);
        let b = Formula::BvAdd(Box::new(bv_var("b", 32)), Box::new(bv_var("a", 32)), 32);
        assert!(normalized_equal(&a, &b));
    }

    #[test]
    fn test_bv_and_commutative() {
        let a = Formula::BvAnd(Box::new(bv_var("x", 64)), Box::new(bv_var("y", 64)), 64);
        let b = Formula::BvAnd(Box::new(bv_var("y", 64)), Box::new(bv_var("x", 64)), 64);
        assert!(normalized_equal(&a, &b));
    }

    #[test]
    fn test_bv_or_commutative() {
        let a = Formula::BvOr(Box::new(bv_var("x", 32)), Box::new(bv_var("y", 32)), 32);
        let b = Formula::BvOr(Box::new(bv_var("y", 32)), Box::new(bv_var("x", 32)), 32);
        assert!(normalized_equal(&a, &b));
    }

    #[test]
    fn test_bv_xor_commutative() {
        let a = Formula::BvXor(Box::new(bv_var("a", 8)), Box::new(bv_var("b", 8)), 8);
        let b = Formula::BvXor(Box::new(bv_var("b", 8)), Box::new(bv_var("a", 8)), 8);
        assert!(normalized_equal(&a, &b));
    }

    #[test]
    fn test_bv_mul_commutative() {
        let a = Formula::BvMul(Box::new(bv_var("p", 16)), Box::new(bv_var("q", 16)), 16);
        let b = Formula::BvMul(Box::new(bv_var("q", 16)), Box::new(bv_var("p", 16)), 16);
        assert!(normalized_equal(&a, &b));
    }

    // -- Double negation elimination --

    #[test]
    fn test_double_negation() {
        let f = Formula::Not(Box::new(Formula::Not(Box::new(var("x")))));
        assert_eq!(normalize(&f), var("x"));
    }

    // -- Constant folding --

    #[test]
    fn test_and_true_identity() {
        let f = Formula::And(vec![Formula::Bool(true), var("x")]);
        assert_eq!(normalize(&f), var("x"));
    }

    #[test]
    fn test_and_false_absorbing() {
        let f = Formula::And(vec![var("x"), Formula::Bool(false), var("y")]);
        assert_eq!(normalize(&f), Formula::Bool(false));
    }

    #[test]
    fn test_or_false_identity() {
        let f = Formula::Or(vec![Formula::Bool(false), var("x")]);
        assert_eq!(normalize(&f), var("x"));
    }

    #[test]
    fn test_or_true_absorbing() {
        let f = Formula::Or(vec![var("x"), Formula::Bool(true), var("y")]);
        assert_eq!(normalize(&f), Formula::Bool(true));
    }

    // -- Arithmetic identities --

    #[test]
    fn test_add_zero_identity() {
        let f = Formula::Add(Box::new(var("x")), Box::new(Formula::Int(0)));
        assert_eq!(normalize(&f), var("x"));
    }

    #[test]
    fn test_mul_one_identity() {
        let f = Formula::Mul(Box::new(var("x")), Box::new(Formula::Int(1)));
        assert_eq!(normalize(&f), var("x"));
    }

    #[test]
    fn test_mul_zero_absorbing() {
        let f = Formula::Mul(Box::new(var("x")), Box::new(Formula::Int(0)));
        assert_eq!(normalize(&f), Formula::Int(0));
    }

    // -- And/Or sorting --

    #[test]
    fn test_and_sorts_commutative() {
        let a = Formula::And(vec![var("z"), var("a"), var("m")]);
        let b = Formula::And(vec![var("m"), var("z"), var("a")]);
        assert!(normalized_equal(&a, &b));
    }

    // -- SemanticProperty --

    #[test]
    fn test_semantic_property_new() {
        let sp = SemanticProperty::new(
            "precondition",
            Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))),
            PropertyKind::Precondition,
        );
        assert_eq!(sp.label, "precondition");
        assert_eq!(sp.kind, PropertyKind::Precondition);
    }

    #[test]
    fn test_semantic_property_from_label() {
        let sp = SemanticProperty::from_label("invariant");
        assert_eq!(sp.label, "invariant");
        assert_eq!(sp.formula, Formula::Bool(true));
        assert_eq!(sp.kind, PropertyKind::Assertion);
    }

    #[test]
    fn test_semantic_property_normalized_eq() {
        let sp1 = SemanticProperty::new(
            "postcondition",
            Formula::Add(Box::new(var("x")), Box::new(Formula::Int(1))),
            PropertyKind::Postcondition,
        );
        let sp2 = SemanticProperty::new(
            "postcondition",
            Formula::Add(Box::new(Formula::Int(1)), Box::new(var("x"))),
            PropertyKind::Postcondition,
        );
        assert!(sp1.normalized_eq(&sp2));
    }

    #[test]
    fn test_semantic_property_different_labels() {
        let sp1 = SemanticProperty::new("pre", Formula::Bool(true), PropertyKind::Precondition);
        let sp2 = SemanticProperty::new("post", Formula::Bool(true), PropertyKind::Postcondition);
        assert!(!sp1.normalized_eq(&sp2));
    }

    #[test]
    fn test_semantic_property_from_property() {
        use crate::composition::Property;
        let p = Property::new("Assertion");
        let sp: SemanticProperty = p.into();
        assert_eq!(sp.label, "Assertion");
        assert_eq!(sp.formula, Formula::Bool(true));
        assert_eq!(sp.kind, PropertyKind::Assertion);
    }

    #[test]
    fn test_subsumes_reflexive() {
        let sp = SemanticProperty::new(
            "assert",
            Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))),
            PropertyKind::Assertion,
        );
        assert!(sp.subsumes(&sp));
    }

    #[test]
    fn test_subsumes_true_is_universal() {
        let universal =
            SemanticProperty::new("assert", Formula::Bool(true), PropertyKind::Assertion);
        let target = SemanticProperty::new(
            "assert",
            Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))),
            PropertyKind::Assertion,
        );
        assert!(universal.subsumes(&target));
    }

    #[test]
    fn test_subsumes_false_is_universal() {
        let impossible =
            SemanticProperty::new("assert", Formula::Bool(false), PropertyKind::Assertion);
        let target = SemanticProperty::new(
            "assert",
            Formula::Lt(Box::new(var("x")), Box::new(Formula::Int(10))),
            PropertyKind::Assertion,
        );
        assert!(impossible.subsumes(&target));
    }

    #[test]
    fn test_subsumes_conjunction_implies_conjunct() {
        let conjunction = SemanticProperty::new(
            "assert",
            Formula::And(vec![var("a"), var("b"), var("c")]),
            PropertyKind::Assertion,
        );
        let conjunct = SemanticProperty::new("assert", var("a"), PropertyKind::Assertion);
        assert!(conjunction.subsumes(&conjunct));
    }

    #[test]
    fn test_subsumes_disjunct_implies_disjunction() {
        let disjunct = SemanticProperty::new("assert", var("a"), PropertyKind::Assertion);
        let disjunction = SemanticProperty::new(
            "assert",
            Formula::Or(vec![var("a"), var("b"), var("c")]),
            PropertyKind::Assertion,
        );
        assert!(disjunct.subsumes(&disjunction));
    }

    #[test]
    fn test_subsumes_different_labels() {
        let lhs = SemanticProperty::new("pre", var("a"), PropertyKind::Assertion);
        let rhs = SemanticProperty::new("post", var("a"), PropertyKind::Assertion);
        assert!(!lhs.subsumes(&rhs));
    }

    #[test]
    fn test_subsumes_normalized_commutativity() {
        let lhs = SemanticProperty::new(
            "assert",
            Formula::Add(Box::new(var("x")), Box::new(Formula::Int(1))),
            PropertyKind::Assertion,
        );
        let rhs = SemanticProperty::new(
            "assert",
            Formula::Add(Box::new(Formula::Int(1)), Box::new(var("x"))),
            PropertyKind::Assertion,
        );
        assert!(lhs.subsumes(&rhs));
    }

    #[test]
    fn test_formula_subsumes_standalone() {
        let stronger = Formula::And(vec![var("a"), var("b")]);
        let weaker = Formula::Or(vec![var("a"), var("c")]);
        assert!(formula_subsumes(&stronger, &weaker));
        assert!(!formula_subsumes(&var("a"), &Formula::And(vec![var("a"), var("b")])));
    }

    #[test]
    fn test_semantic_property_free_variables() {
        let sp = SemanticProperty::new(
            "assert",
            Formula::Forall(
                vec![("y".into(), Sort::Int)],
                Box::new(Formula::And(vec![
                    Formula::Var("x".into(), Sort::Int),
                    Formula::Var("y".into(), Sort::Int),
                    Formula::Var("z".into(), Sort::Int),
                ])),
            ),
            PropertyKind::Assertion,
        );

        let free = sp.free_variables();
        assert_eq!(free.len(), 2);
        assert!(free.contains("x"));
        assert!(free.contains("z"));
        assert!(!free.contains("y"));
    }

    #[test]
    fn test_property_kind_serialization() {
        let json = serde_json::to_string(&PropertyKind::LoopInvariant)
            .expect("PropertyKind should serialize");
        let roundtrip: PropertyKind =
            serde_json::from_str(&json).expect("PropertyKind should deserialize");
        assert_eq!(roundtrip, PropertyKind::LoopInvariant);
    }

    // -- Edge cases --

    #[test]
    fn test_empty_and() {
        assert_eq!(normalize(&Formula::And(vec![])), Formula::Bool(true));
    }

    #[test]
    fn test_empty_or() {
        assert_eq!(normalize(&Formula::Or(vec![])), Formula::Bool(false));
    }

    #[test]
    fn test_singleton_and() {
        let f = Formula::And(vec![var("x")]);
        assert_eq!(normalize(&f), var("x"));
    }

    #[test]
    fn test_singleton_or() {
        let f = Formula::Or(vec![var("x")]);
        assert_eq!(normalize(&f), var("x"));
    }

    #[test]
    fn test_normalize_preserves_non_commutative() {
        // Sub, Div, Rem are NOT commutative — order must be preserved
        let f = Formula::Sub(Box::new(var("x")), Box::new(var("y")));
        let n = normalize(&f);
        assert_eq!(n, Formula::Sub(Box::new(var("x")), Box::new(var("y"))));
    }

    #[test]
    fn test_normalize_leaf_unchanged() {
        assert_eq!(normalize(&Formula::Bool(true)), Formula::Bool(true));
        assert_eq!(normalize(&Formula::Int(42)), Formula::Int(42));
        assert_eq!(normalize(&var("x")), var("x"));
    }

    #[test]
    fn test_deeply_nested_normalization() {
        // And(And(And(a, b), c), d) should flatten to And(a, b, c, d)
        let inner = Formula::And(vec![var("a"), var("b")]);
        let mid = Formula::And(vec![inner, var("c")]);
        let outer = Formula::And(vec![mid, var("d")]);

        let flat = Formula::And(vec![var("a"), var("b"), var("c"), var("d")]);
        assert!(normalized_equal(&outer, &flat));
    }
}

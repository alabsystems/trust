// trust_vcgen/separation_logic/encoding.rs: FOL translation and heap encoding
//
// Translates separation logic formulas to first-order logic with explicit
// heap arrays for SMT solving. Includes disjointness encoding for the
// separating conjunction and unsafe block pre/post condition encoding.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationCondition};

use super::formula::SepFormula;

// ────────────────────────────────────────────────────────────────────────────
// Translation: separation logic -> FOL with explicit heap encoding
// ────────────────────────────────────────────────────────────────────────────

/// Translate a separation logic formula to FOL with explicit heap encoding.
///
/// The heap is modeled as an SMT array `heap: (Array Int Int)`.
/// - `PointsTo { addr, value }` becomes `Select(heap, addr) == value`
/// - `SepStar(P, Q)` becomes `P_fol AND Q_fol AND disjointness(P_addrs, Q_addrs)`
/// - `SepWand(P, Q)` becomes `Implies(P_fol, Q_fol)` (conservative approx)
/// - `Emp` becomes `true`
/// - `Pure(phi)` becomes `phi`
///
/// The `heap_var` parameter is the name of the heap array variable.
#[must_use]
pub fn sep_to_formula(sep: &SepFormula, heap_var: &str) -> Formula {
    let heap =
        Formula::Var(heap_var.to_string(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)));
    sep_to_formula_inner(sep, &heap)
}

/// Internal recursive translation.
fn sep_to_formula_inner(sep: &SepFormula, heap: &Formula) -> Formula {
    match sep {
        SepFormula::PointsTo { addr, value } => {
            // Select(heap, addr) == value
            Formula::Eq(
                Box::new(Formula::Select(Box::new(heap.clone()), Box::new(addr.clone()))),
                Box::new(value.clone()),
            )
        }
        SepFormula::SepStar(lhs, rhs) => {
            // P * Q: both hold AND addresses are disjoint
            let lhs_fol = sep_to_formula_inner(lhs, heap);
            let rhs_fol = sep_to_formula_inner(rhs, heap);
            let disjoint = encode_heap_disjointness(lhs, rhs);
            Formula::And(vec![lhs_fol, rhs_fol, disjoint])
        }
        SepFormula::SepWand(lhs, rhs) => {
            // P -* Q: conservative approximation as implication.
            // Full magic wand semantics requires second-order quantification
            // over heaps, which is undecidable in general. We approximate:
            // "if P holds on the current heap, then Q holds."
            let lhs_fol = sep_to_formula_inner(lhs, heap);
            let rhs_fol = sep_to_formula_inner(rhs, heap);
            Formula::Implies(Box::new(lhs_fol), Box::new(rhs_fol))
        }
        SepFormula::Emp => Formula::Bool(true),
        SepFormula::Pure(f) => f.clone(),
    }
}

/// Encode heap disjointness for a separating conjunction `P * Q`.
///
/// Collects all addresses referenced in P and Q and asserts they are pairwise
/// distinct. This is the key semantic content of `*` beyond conjunction.
#[must_use]
pub fn encode_heap_disjointness(lhs: &SepFormula, rhs: &SepFormula) -> Formula {
    let lhs_addrs = collect_addresses(lhs);
    let rhs_addrs = collect_addresses(rhs);

    if lhs_addrs.is_empty() || rhs_addrs.is_empty() {
        return Formula::Bool(true);
    }

    let mut constraints = Vec::with_capacity(lhs_addrs.len() * rhs_addrs.len());
    for l_addr in &lhs_addrs {
        for r_addr in &rhs_addrs {
            // l_addr != r_addr
            constraints.push(Formula::Not(Box::new(Formula::Eq(
                Box::new((*l_addr).clone()),
                Box::new((*r_addr).clone()),
            ))));
        }
    }

    if constraints.len() == 1 {
        constraints.pop().unwrap_or(Formula::Bool(true))
    } else {
        Formula::And(constraints)
    }
}

/// Collect all concrete address formulas from a separation logic formula.
pub(super) fn collect_addresses(sep: &SepFormula) -> Vec<&Formula> {
    let mut addrs = Vec::with_capacity(sep.cell_count());
    collect_addresses_inner(sep, &mut addrs);
    addrs
}

fn collect_addresses_inner<'a>(sep: &'a SepFormula, addrs: &mut Vec<&'a Formula>) {
    match sep {
        SepFormula::PointsTo { addr, .. } => {
            addrs.push(addr);
        }
        SepFormula::SepStar(lhs, rhs) | SepFormula::SepWand(lhs, rhs) => {
            collect_addresses_inner(lhs, addrs);
            collect_addresses_inner(rhs, addrs);
        }
        SepFormula::Emp | SepFormula::Pure(_) => {}
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Unsafe block encoding
// ────────────────────────────────────────────────────────────────────────────

/// Encode an unsafe block pattern as separation logic verification conditions.
///
/// Given the separation logic precondition (what must hold before the unsafe
/// block) and postcondition (what must hold after), produces a VC asserting
/// the precondition is satisfiable and the postcondition follows.
#[must_use]
pub fn encode_unsafe_block(
    func_name: &str,
    pre: &SepFormula,
    post: &SepFormula,
    span: &SourceSpan,
    heap_var: &str,
) -> Vec<VerificationCondition> {
    let pre_fol = sep_to_formula(pre, heap_var);
    let post_fol = sep_to_formula(post, heap_var);
    let fn_sym: trust_types::Symbol = func_name.into();

    vec![
        // VC 1: Precondition must be satisfiable (not trivially false)
        VerificationCondition {
            kind: VcKind::Assertion {
                message: format!("[unsafe:sep] heap precondition for unsafe block in {func_name}"),
            },
            function: fn_sym,
            location: span.clone(),
            formula: Formula::Not(Box::new(pre_fol.clone())),
            contract_metadata: None,
            obligation: None,
        },
        // VC 2: Postcondition must follow from precondition
        // Violation: precondition holds but postcondition doesn't
        VerificationCondition {
            kind: VcKind::Assertion {
                message: format!("[unsafe:sep] heap postcondition for unsafe block in {func_name}"),
            },
            function: fn_sym,
            location: span.clone(),
            formula: Formula::And(vec![pre_fol, Formula::Not(Box::new(post_fol))]),
            contract_metadata: None,
            obligation: None,
        },
    ]
}

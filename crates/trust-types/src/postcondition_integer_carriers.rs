//! Shared selection of declared integer carriers for completed postcondition rows.
//! Naming and range mathematics stay with each producer's existing constructors;
//! the selection, SSA ambiguity/sort guards and checked-result refusal are common.

use crate::fx::{FxHashMap, FxHashSet};
use crate::{Formula, LocalDecl, Sort, Ty, VerifiableFunction};

/// Conjoin the declared integer carriers of actual local/return symbols.
///
/// `local_name` must use the producer's collision-safe whole-local vocabulary;
/// `carrier` must describe the complete declared type (no inferred interval).
/// The caller applies this only to completed arithmetic postcondition rows,
/// AFTER every unmodeled-value/refutation tripwire, with the return named `_0`.
/// Parameters, projections, noninteger sorts and ambiguous SSA names are left
/// alone. The function adds no identities between different SSA versions.
///
/// A `(integer, bool)` checked-result carrier can denote an UNWRAPPED arithmetic
/// intermediate. Refuse this entire augmentation whenever one exists, covering
/// aliases through copies, aggregates and multiple definitions without a new
/// provenance analysis. Existing assert-passed semantics remain authoritative.
#[must_use]
pub fn conjoin_postcondition_integer_carriers(
    func: &VerifiableFunction,
    formula: Formula,
    local_name: impl FnMut(&LocalDecl) -> String,
    carrier: impl FnMut(&Formula, &Ty) -> Option<Formula>,
) -> Formula {
    let mut bounds = postcondition_integer_carrier_facts(func, &formula, local_name, carrier);
    if bounds.is_empty() {
        formula
    } else {
        bounds.push(formula);
        Formula::And(bounds)
    }
}

/// Select the SAME declared carrier facts as
/// [`conjoin_postcondition_integer_carriers`], without choosing their conjunction
/// layout. Producers still apply these only after their refusal tripwires; this
/// function grants no pinning or proof authority. Order and occurrence
/// multiplicity are preserved, including across SSA spellings.
#[must_use]
pub fn postcondition_integer_carrier_facts(
    func: &VerifiableFunction,
    formula: &Formula,
    mut local_name: impl FnMut(&LocalDecl) -> String,
    mut carrier: impl FnMut(&Formula, &Ty) -> Option<Formula>,
) -> Vec<Formula> {
    let mut has_candidate_int_local = false;
    for decl in &func.body.locals {
        if matches!(
            &decl.ty,
            Ty::Tuple(fields)
                if fields.len() == 2
                    && fields[0].int_width().is_some()
                    && matches!(fields[1], Ty::Bool)
        ) {
            return Vec::new();
        }
        if (decl.index == 0 || decl.index > func.body.arg_count) && decl.ty.int_width().is_some() {
            has_candidate_int_local = true;
        }
    }
    if !has_candidate_int_local {
        return Vec::new();
    }

    // If a naming callback maps distinct declarations to one vocabulary, never
    // overwrite a carrier or introduce a local fact under a parameter's name.
    // Count every declaration, including nonscalar locals.
    let locals_len = func.body.locals.len();
    let mut named: Vec<(&LocalDecl, std::borrow::Cow<'static, str>)> =
        Vec::with_capacity(locals_len);
    for decl in &func.body.locals {
        let name = if decl.index == 0 {
            std::borrow::Cow::Borrowed("_0")
        } else {
            std::borrow::Cow::Owned(local_name(decl))
        };
        named.push((decl, name));
    }
    let mut name_counts =
        FxHashMap::<&str, usize>::with_capacity_and_hasher(locals_len, Default::default());
    let mut index_counts =
        FxHashMap::<usize, usize>::with_capacity_and_hasher(locals_len, Default::default());
    for (decl, name) in &named {
        *name_counts.entry(name.as_ref()).or_default() += 1;
        *index_counts.entry(decl.index).or_default() += 1;
    }
    let mut types = FxHashMap::<&str, &Ty>::default();
    for (decl, base) in &named {
        if (decl.index >= 1 && decl.index <= func.body.arg_count) || decl.ty.int_width().is_none() {
            continue;
        }
        if name_counts.get(base.as_ref()) != Some(&1) || index_counts.get(&decl.index) != Some(&1) {
            continue;
        }
        types.insert(base.as_ref(), &decl.ty);
    }
    if types.is_empty() {
        return Vec::new();
    }

    let mut occurrences: Vec<(&Formula, &str, &Ty)> = Vec::new();
    let mut non_int_names = FxHashSet::<&str>::default();
    let source_names: FxHashSet<&str> = func
        .body
        .locals
        .iter()
        .filter_map(|decl| decl.name.as_deref().filter(|n| n.contains('#')))
        .collect();
    crate::visit_formula_nodes(formula, &mut |f| {
        if let Formula::Var(name, sort) = f {
            let (base, has_hash) = match name.split_once('#') {
                Some((base, _)) => (base, true),
                None => (name.as_str(), false),
            };
            let Some(&ty) = types.get(base) else {
                return;
            };
            if *sort == Sort::Int {
                if !(has_hash && !source_names.is_empty() && source_names.contains(name.as_str())) {
                    occurrences.push((f, name.as_str(), ty));
                }
            } else {
                non_int_names.insert(name.as_str());
            }
        }
    });
    let mut bounds = Vec::new();
    for (var_formula, name, ty) in occurrences {
        if non_int_names.contains(name) {
            continue;
        }
        // Keep occurrence multiplicity: the spine compares modulo SSA suffixes
        // and cannot distinguish two versions from repeated uses of one name.
        // Emitting once per occurrence makes this augmentation commute with
        // that existing comparison, without changing it or dropping live facts.
        // As in versioned_param_type_ranges, a real source local named `x#e`
        // must not acquire a differently-typed local `x`'s carrier.
        if let Some(bound) = carrier(var_formula, ty) {
            bounds.push(bound);
        }
    }
    bounds
}

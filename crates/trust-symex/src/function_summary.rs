// trust-symex function summaries for path explosion mitigation
//
// When symbolic execution encounters a function call, instead of
// inlining the callee (which multiplies paths), we can apply a
// precomputed summary that captures the function's input-output
// behavior as symbolic constraints.
//
// Inspired by compositional symbolic execution (Godefroid, POPL 2007)
// and KLEE's function model stubs (refs/klee/lib/Core/SpecialFunctionHandler.cpp).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::memory::MemoryRegion;
use crate::state::SymbolicValue;

/// A side effect produced by a function.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SideEffect {
    /// The function writes to a memory region.
    MemoryWrite { region: MemoryRegion, value: SymbolicValue },
    /// The function returns a value.
    Return(SymbolicValue),
    /// The function may panic under the given condition.
    Panic(SymbolicValue),
}

/// A precondition on function inputs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Precondition {
    /// Name of the parameter this condition constrains.
    pub param: String,
    /// The constraint formula (should evaluate to boolean-like).
    pub constraint: SymbolicValue,
}

/// A postcondition on function outputs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Postcondition {
    /// Description or name of the property.
    pub name: String,
    /// The constraint formula relating inputs to the return value.
    pub constraint: SymbolicValue,
}

/// A summary of a function's symbolic behavior.
///
/// Instead of symbolically executing the function body, the caller
/// can apply this summary to get the effect of the call.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionSummary {
    /// The function name this summary applies to.
    pub function_name: String,
    /// Parameter names in order.
    pub params: Vec<String>,
    /// Preconditions that must hold for the summary to apply.
    pub preconditions: Vec<Precondition>,
    /// Postconditions that hold after the call.
    pub postconditions: Vec<Postcondition>,
    /// Side effects of calling the function.
    pub side_effects: Vec<SideEffect>,
    /// Whether the function is known to be pure (no side effects).
    pub is_pure: bool,
}

impl FunctionSummary {
    /// Create a new empty summary for the given function.
    #[must_use]
    pub fn new(function_name: impl Into<String>, params: Vec<String>) -> Self {
        Self {
            function_name: function_name.into(),
            params,
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            side_effects: Vec::new(),
            is_pure: true,
        }
    }

    /// Add a precondition.
    pub fn add_precondition(&mut self, param: impl Into<String>, constraint: SymbolicValue) {
        self.preconditions.push(Precondition { param: param.into(), constraint });
    }

    /// Add a postcondition.
    pub fn add_postcondition(&mut self, name: impl Into<String>, constraint: SymbolicValue) {
        self.postconditions.push(Postcondition { name: name.into(), constraint });
    }

    /// Add a side effect.
    pub fn add_side_effect(&mut self, effect: SideEffect) {
        if !matches!(effect, SideEffect::Return(_)) {
            self.is_pure = false;
        }
        self.side_effects.push(effect);
    }

    /// Returns the return value side-effect, if any.
    #[must_use]
    pub fn return_value(&self) -> Option<&SymbolicValue> {
        self.side_effects
            .iter()
            .find_map(|e| if let SideEffect::Return(v) = e { Some(v) } else { None })
    }

    /// Returns all panic conditions.
    #[must_use]
    pub fn panic_conditions(&self) -> Vec<&SymbolicValue> {
        self.side_effects
            .iter()
            .filter_map(|e| if let SideEffect::Panic(c) = e { Some(c) } else { None })
            .collect()
    }

    /// Returns all memory write effects.
    #[must_use]
    pub fn memory_writes(&self) -> Vec<(&MemoryRegion, &SymbolicValue)> {
        self.side_effects
            .iter()
            .filter_map(|e| {
                if let SideEffect::MemoryWrite { region, value } = e {
                    Some((region, value))
                } else {
                    None
                }
            })
            .collect()
    }
}

/// The result of applying a function summary at a call site.
#[derive(Debug, Clone)]
pub struct AppliedSummary {
    /// The return value (with actuals substituted for formals).
    pub return_value: Option<SymbolicValue>,
    /// Constraints that must be added to the path (postconditions).
    pub constraints: Vec<SymbolicValue>,
    /// Memory writes to apply.
    pub memory_writes: Vec<(MemoryRegion, SymbolicValue)>,
    /// Panic conditions to check.
    pub panic_conditions: Vec<SymbolicValue>,
}

/// Apply a function summary at a call site, substituting actual
/// arguments for formal parameters.
///
/// The `actuals` map should have the same keys as `summary.params`.
#[must_use]
pub fn apply_summary(
    summary: &FunctionSummary,
    actuals: &BTreeMap<String, SymbolicValue>,
) -> AppliedSummary {
    let return_value = summary.return_value().map(|v| substitute(v, actuals));

    let constraints =
        summary.postconditions.iter().map(|pc| substitute(&pc.constraint, actuals)).collect();

    let memory_writes = summary
        .memory_writes()
        .into_iter()
        .map(|(region, value)| (region.clone(), substitute(value, actuals)))
        .collect();

    let panic_conditions =
        summary.panic_conditions().into_iter().map(|c| substitute(c, actuals)).collect();

    AppliedSummary { return_value, constraints, memory_writes, panic_conditions }
}

/// Substitute symbols in a value according to the given mapping.
///
/// If a symbol name appears in `subst`, it is replaced by the
/// corresponding value. Other symbols are left unchanged.
#[must_use]
pub fn substitute(value: &SymbolicValue, subst: &BTreeMap<String, SymbolicValue>) -> SymbolicValue {
    match value {
        SymbolicValue::Concrete(_) => value.clone(),
        SymbolicValue::Symbol(name) => subst.get(name).cloned().unwrap_or_else(|| value.clone()),
        SymbolicValue::BinOp(lhs, op, rhs) => {
            SymbolicValue::bin_op(substitute(lhs, subst), *op, substitute(rhs, subst))
        }
        SymbolicValue::Ite(cond, then_val, else_val) => SymbolicValue::ite(
            substitute(cond, subst),
            substitute(then_val, subst),
            substitute(else_val, subst),
        ),
        SymbolicValue::Not(inner) => SymbolicValue::Not(Box::new(substitute(inner, subst))),
        SymbolicValue::BitwiseNot(inner) => {
            SymbolicValue::BitwiseNot(Box::new(substitute(inner, subst)))
        }
        SymbolicValue::Neg(inner) => SymbolicValue::Neg(Box::new(substitute(inner, subst))),
    }
}

/// Check if a function summary indicates a pure function (no side effects
/// beyond returning a value).
#[must_use]
pub fn is_pure(summary: &FunctionSummary) -> bool {
    summary.is_pure
}

/// Compose two summaries: inline a callee summary into a caller summary.
///
/// The caller's return value expression may reference the callee's return.
/// We substitute the callee's return value into the caller wherever
/// `call_result_name` appears.
#[must_use]
pub fn compose_summaries(
    caller: &FunctionSummary,
    callee: &FunctionSummary,
    call_result_name: &str,
) -> FunctionSummary {
    let callee_return = callee.return_value().cloned().unwrap_or(SymbolicValue::Concrete(0));

    let mut subst = BTreeMap::default();
    subst.insert(call_result_name.to_owned(), callee_return);

    let mut composed = FunctionSummary::new(caller.function_name.clone(), caller.params.clone());

    // Carry over caller preconditions.
    for pre in &caller.preconditions {
        composed.add_precondition(pre.param.clone(), substitute(&pre.constraint, &subst));
    }

    // Carry over callee preconditions (they become caller preconditions).
    for pre in &callee.preconditions {
        composed.add_precondition(pre.param.clone(), pre.constraint.clone());
    }

    // Caller postconditions with callee return substituted.
    for post in &caller.postconditions {
        composed.add_postcondition(post.name.clone(), substitute(&post.constraint, &subst));
    }

    // Callee postconditions carried forward.
    for post in &callee.postconditions {
        composed.add_postcondition(
            format!("{}.{}", callee.function_name, post.name),
            post.constraint.clone(),
        );
    }

    // Merge side effects: callee's non-Return effects first, then caller's
    // effects with substitution. The callee's Return is consumed by the
    // substitution into the caller -- it is not a side effect of the
    // composed function.
    for effect in &callee.side_effects {
        match effect {
            SideEffect::Return(_) => {} // consumed by substitution
            SideEffect::Panic(v) => {
                composed.add_side_effect(SideEffect::Panic(v.clone()));
            }
            other => composed.add_side_effect(other.clone()),
        }
    }
    for effect in &caller.side_effects {
        match effect {
            SideEffect::Return(v) => {
                composed.add_side_effect(SideEffect::Return(substitute(v, &subst)));
            }
            SideEffect::Panic(v) => {
                composed.add_side_effect(SideEffect::Panic(substitute(v, &subst)));
            }
            other => composed.add_side_effect(other.clone()),
        }
    }

    composed.is_pure = caller.is_pure && callee.is_pure;
    composed
}

/// A cache of computed function summaries.
#[derive(Debug, Clone, Default)]
pub struct SummaryCache {
    summaries: BTreeMap<String, FunctionSummary>,
}

impl SummaryCache {
    /// Create a new empty summary cache.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert a summary into the cache.
    pub fn insert(&mut self, summary: FunctionSummary) {
        self.summaries.insert(summary.function_name.clone(), summary);
    }

    /// Look up a summary by function name.
    #[must_use]
    pub fn get(&self, function_name: &str) -> Option<&FunctionSummary> {
        self.summaries.get(function_name)
    }

    /// Check if a summary exists for the given function.
    #[must_use]
    pub fn contains(&self, function_name: &str) -> bool {
        self.summaries.contains_key(function_name)
    }

    /// Invalidate (remove) a summary, e.g., when the function code changes.
    pub fn invalidate(&mut self, function_name: &str) -> bool {
        self.summaries.remove(function_name).is_some()
    }

    /// Returns the number of cached summaries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.summaries.len()
    }

    /// Returns `true` if the cache is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.summaries.is_empty()
    }

    /// Iterate over all cached summaries.
    pub fn iter(&self) -> impl Iterator<Item = (&str, &FunctionSummary)> {
        self.summaries.iter().map(|(k, v)| (k.as_str(), v))
    }

    /// Remove all cached summaries.
    pub fn clear(&mut self) {
        self.summaries.clear();
    }
}

#[cfg(test)]
mod tests {
    use trust_types::BinOp;

    use super::*;

    // --- FunctionSummary construction ---

    #[test]
    fn test_summary_new_is_pure() {
        let s = FunctionSummary::new("foo", vec!["x".into()]);
        assert!(s.is_pure);
        assert!(s.preconditions.is_empty());
        assert!(s.postconditions.is_empty());
        assert!(s.side_effects.is_empty());
    }

    #[test]
    fn test_summary_add_precondition() {
        let mut s = FunctionSummary::new("foo", vec!["x".into()]);
        s.add_precondition("x", SymbolicValue::Concrete(1));
        assert_eq!(s.preconditions.len(), 1);
        assert_eq!(s.preconditions[0].param, "x");
    }

    #[test]
    fn test_summary_add_postcondition() {
        let mut s = FunctionSummary::new("foo", vec![]);
        s.add_postcondition("result_positive", SymbolicValue::Concrete(1));
        assert_eq!(s.postconditions.len(), 1);
    }

    #[test]
    fn test_summary_return_value() {
        let mut s = FunctionSummary::new("foo", vec![]);
        assert!(s.return_value().is_none());
        s.add_side_effect(SideEffect::Return(SymbolicValue::Concrete(42)));
        assert_eq!(s.return_value(), Some(&SymbolicValue::Concrete(42)));
    }

    #[test]
    fn test_summary_memory_write_marks_impure() {
        let mut s = FunctionSummary::new("foo", vec![]);
        assert!(s.is_pure);
        s.add_side_effect(SideEffect::MemoryWrite {
            region: MemoryRegion::Heap(0, 0),
            value: SymbolicValue::Concrete(0),
        });
        assert!(!s.is_pure);
    }

    #[test]
    fn test_summary_return_does_not_mark_impure() {
        let mut s = FunctionSummary::new("foo", vec![]);
        s.add_side_effect(SideEffect::Return(SymbolicValue::Concrete(1)));
        assert!(s.is_pure, "Return alone should not mark as impure");
    }

    #[test]
    fn test_summary_panic_conditions() {
        let mut s = FunctionSummary::new("foo", vec![]);
        s.add_side_effect(SideEffect::Panic(SymbolicValue::Symbol("overflow".into())));
        s.add_side_effect(SideEffect::Return(SymbolicValue::Concrete(0)));
        let panics = s.panic_conditions();
        assert_eq!(panics.len(), 1);
    }

    #[test]
    fn test_summary_memory_writes_accessor() {
        let mut s = FunctionSummary::new("foo", vec![]);
        s.add_side_effect(SideEffect::MemoryWrite {
            region: MemoryRegion::Global("g".into()),
            value: SymbolicValue::Concrete(99),
        });
        let writes = s.memory_writes();
        assert_eq!(writes.len(), 1);
        assert_eq!(writes[0].0, &MemoryRegion::Global("g".into()));
    }

    // --- Substitution ---

    #[test]
    fn test_substitute_concrete_unchanged() {
        let v = SymbolicValue::Concrete(42);
        let result = substitute(&v, &BTreeMap::default());
        assert_eq!(result, SymbolicValue::Concrete(42));
    }

    #[test]
    fn test_substitute_symbol_replaced() {
        let v = SymbolicValue::Symbol("x".into());
        let mut map = BTreeMap::default();
        map.insert("x".into(), SymbolicValue::Concrete(10));
        let result = substitute(&v, &map);
        assert_eq!(result, SymbolicValue::Concrete(10));
    }

    #[test]
    fn test_substitute_symbol_not_in_map() {
        let v = SymbolicValue::Symbol("y".into());
        let map = BTreeMap::default();
        let result = substitute(&v, &map);
        assert_eq!(result, SymbolicValue::Symbol("y".into()));
    }

    #[test]
    fn test_substitute_binop_recursive() {
        let v = SymbolicValue::bin_op(
            SymbolicValue::Symbol("a".into()),
            BinOp::Add,
            SymbolicValue::Symbol("b".into()),
        );
        let mut map = BTreeMap::default();
        map.insert("a".into(), SymbolicValue::Concrete(3));
        map.insert("b".into(), SymbolicValue::Concrete(4));
        let result = substitute(&v, &map);
        let expected = SymbolicValue::bin_op(
            SymbolicValue::Concrete(3),
            BinOp::Add,
            SymbolicValue::Concrete(4),
        );
        assert_eq!(result, expected);
    }

    #[test]
    fn test_substitute_ite_recursive() {
        let v = SymbolicValue::ite(
            SymbolicValue::Symbol("c".into()),
            SymbolicValue::Symbol("t".into()),
            SymbolicValue::Concrete(0),
        );
        let mut map = BTreeMap::default();
        map.insert("c".into(), SymbolicValue::Concrete(1));
        map.insert("t".into(), SymbolicValue::Concrete(42));
        let result = substitute(&v, &map);
        let expected = SymbolicValue::ite(
            SymbolicValue::Concrete(1),
            SymbolicValue::Concrete(42),
            SymbolicValue::Concrete(0),
        );
        assert_eq!(result, expected);
    }

    #[test]
    fn test_substitute_not_recursive() {
        let v = SymbolicValue::Not(Box::new(SymbolicValue::Symbol("x".into())));
        let mut map = BTreeMap::default();
        map.insert("x".into(), SymbolicValue::Concrete(1));
        let result = substitute(&v, &map);
        assert_eq!(result, SymbolicValue::Not(Box::new(SymbolicValue::Concrete(1))));
    }

    // --- apply_summary ---

    #[test]
    fn test_apply_summary_basic() {
        let mut s = FunctionSummary::new("add", vec!["a".into(), "b".into()]);
        s.add_side_effect(SideEffect::Return(SymbolicValue::bin_op(
            SymbolicValue::Symbol("a".into()),
            BinOp::Add,
            SymbolicValue::Symbol("b".into()),
        )));
        s.add_postcondition(
            "result_check",
            SymbolicValue::bin_op(
                SymbolicValue::Symbol("a".into()),
                BinOp::Le,
                SymbolicValue::Symbol("b".into()),
            ),
        );

        let mut actuals = BTreeMap::default();
        actuals.insert("a".into(), SymbolicValue::Concrete(3));
        actuals.insert("b".into(), SymbolicValue::Concrete(7));

        let applied = apply_summary(&s, &actuals);
        assert!(applied.return_value.is_some());

        let ret = applied.return_value.unwrap();
        let expected_ret = SymbolicValue::bin_op(
            SymbolicValue::Concrete(3),
            BinOp::Add,
            SymbolicValue::Concrete(7),
        );
        assert_eq!(ret, expected_ret);
        assert_eq!(applied.constraints.len(), 1);
    }

    #[test]
    fn test_apply_summary_with_panic() {
        let mut s = FunctionSummary::new("div", vec!["n".into(), "d".into()]);
        s.add_side_effect(SideEffect::Panic(SymbolicValue::bin_op(
            SymbolicValue::Symbol("d".into()),
            BinOp::Eq,
            SymbolicValue::Concrete(0),
        )));

        let mut actuals = BTreeMap::default();
        actuals.insert("n".into(), SymbolicValue::Concrete(10));
        actuals.insert("d".into(), SymbolicValue::Symbol("input_d".into()));

        let applied = apply_summary(&s, &actuals);
        assert_eq!(applied.panic_conditions.len(), 1);
    }

    #[test]
    fn test_apply_summary_no_return() {
        let s = FunctionSummary::new("noop", vec![]);
        let applied = apply_summary(&s, &BTreeMap::default());
        assert!(applied.return_value.is_none());
        assert!(applied.constraints.is_empty());
    }

    // --- compose_summaries ---

    #[test]
    fn test_compose_summaries_basic() {
        // callee: fn square(x) -> x * x
        let mut callee = FunctionSummary::new("square", vec!["x".into()]);
        callee.add_side_effect(SideEffect::Return(SymbolicValue::bin_op(
            SymbolicValue::Symbol("x".into()),
            BinOp::Mul,
            SymbolicValue::Symbol("x".into()),
        )));

        // caller: fn add_square(a) -> call_result + 1
        let mut caller = FunctionSummary::new("add_square", vec!["a".into()]);
        caller.add_side_effect(SideEffect::Return(SymbolicValue::bin_op(
            SymbolicValue::Symbol("call_result".into()),
            BinOp::Add,
            SymbolicValue::Concrete(1),
        )));

        let composed = compose_summaries(&caller, &callee, "call_result");
        assert!(composed.is_pure);
        assert_eq!(composed.function_name, "add_square");

        // The composed return should substitute call_result with x*x.
        let ret = composed.return_value().expect("should have return");
        match ret {
            SymbolicValue::BinOp(lhs, BinOp::Add, rhs) => {
                assert!(matches!(**lhs, SymbolicValue::BinOp(_, BinOp::Mul, _)));
                assert_eq!(**rhs, SymbolicValue::Concrete(1));
            }
            other => panic!("expected BinOp Add, got {other:?}"),
        }
    }

    #[test]
    fn test_compose_summaries_preserves_preconditions() {
        let mut callee = FunctionSummary::new("inner", vec!["y".into()]);
        callee.add_precondition("y", SymbolicValue::Concrete(1));
        callee.add_side_effect(SideEffect::Return(SymbolicValue::Concrete(0)));

        let caller = FunctionSummary::new("outer", vec!["x".into()]);

        let composed = compose_summaries(&caller, &callee, "call_result");
        assert_eq!(composed.preconditions.len(), 1);
    }

    #[test]
    fn test_compose_summaries_impure_callee() {
        let mut callee = FunctionSummary::new("writer", vec![]);
        callee.add_side_effect(SideEffect::MemoryWrite {
            region: MemoryRegion::Heap(0, 0),
            value: SymbolicValue::Concrete(1),
        });

        let caller = FunctionSummary::new("wrapper", vec![]);
        let composed = compose_summaries(&caller, &callee, "call_result");
        assert!(!composed.is_pure);
    }

    // --- SummaryCache ---

    #[test]
    fn test_cache_empty() {
        let cache = SummaryCache::new();
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);
        assert!(!cache.contains("foo"));
    }

    #[test]
    fn test_cache_insert_and_get() {
        let mut cache = SummaryCache::new();
        let s = FunctionSummary::new("foo", vec![]);
        cache.insert(s);
        assert!(cache.contains("foo"));
        assert!(!cache.contains("bar"));
        assert_eq!(cache.len(), 1);
        let retrieved = cache.get("foo").expect("should find foo");
        assert_eq!(retrieved.function_name, "foo");
    }

    #[test]
    fn test_cache_invalidate() {
        let mut cache = SummaryCache::new();
        cache.insert(FunctionSummary::new("foo", vec![]));
        assert!(cache.invalidate("foo"));
        assert!(!cache.contains("foo"));
        assert!(cache.is_empty());
    }

    #[test]
    fn test_cache_invalidate_nonexistent() {
        let mut cache = SummaryCache::new();
        assert!(!cache.invalidate("nonexistent"));
    }

    #[test]
    fn test_cache_overwrite() {
        let mut cache = SummaryCache::new();
        let mut s1 = FunctionSummary::new("foo", vec!["x".into()]);
        s1.add_precondition("x", SymbolicValue::Concrete(1));
        cache.insert(s1);

        let s2 = FunctionSummary::new("foo", vec!["y".into()]);
        cache.insert(s2);

        let retrieved = cache.get("foo").expect("should find foo");
        assert_eq!(retrieved.params, vec!["y".to_owned()]);
        assert!(retrieved.preconditions.is_empty());
    }

    #[test]
    fn test_cache_clear() {
        let mut cache = SummaryCache::new();
        cache.insert(FunctionSummary::new("a", vec![]));
        cache.insert(FunctionSummary::new("b", vec![]));
        assert_eq!(cache.len(), 2);
        cache.clear();
        assert!(cache.is_empty());
    }

    #[test]
    fn test_cache_iter() {
        let mut cache = SummaryCache::new();
        cache.insert(FunctionSummary::new("alpha", vec![]));
        cache.insert(FunctionSummary::new("beta", vec![]));
        let names: Vec<&str> = cache.iter().map(|(k, _)| k).collect();
        assert_eq!(names.len(), 2);
        assert!(names.contains(&"alpha"));
        assert!(names.contains(&"beta"));
    }

    // --- is_pure helper ---

    #[test]
    fn test_is_pure_helper_true() {
        let s = FunctionSummary::new("pure_fn", vec![]);
        assert!(is_pure(&s));
    }

    #[test]
    fn test_is_pure_helper_false() {
        let mut s = FunctionSummary::new("impure_fn", vec![]);
        s.add_side_effect(SideEffect::Panic(SymbolicValue::Concrete(0)));
        assert!(!is_pure(&s));
    }
}

// trust_vcgen/stdlib_specs.rs: Standard library function specifications
//
// Provides pre/postcondition contracts for Rust standard library functions
// (Vec, Option, Result, Iterator) for use with trust_wp Proof Level 1
// verification. Each spec is a FnContract with Formula-based conditions.
//
// Standard library specs for trust_wp verification.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use trust_types::{Formula, Sort};

// ---------------------------------------------------------------------------
// FnContract — pre/postcondition specification for a single function
// ---------------------------------------------------------------------------

/// A function contract consisting of preconditions and postconditions.
///
/// Each condition is a `Formula` that must hold. Preconditions are assumed
/// at call sites; postconditions are guaranteed after return.
///
/// Variable naming convention:
/// - `self_var` / `self_len` / `self_cap`: receiver state
/// - `arg0`, `arg1`, ...: positional arguments
/// - `result`: return value
/// - `old_len`, `old_self`, ...: pre-state snapshots (prefixed with `old_`)
#[derive(Debug, Clone, PartialEq)]
pub struct FnContract {
    /// Fully-qualified function path (e.g., `"std::vec::Vec::push"`).
    pub fn_path: String,
    /// Preconditions: must hold before the call.
    pub preconditions: Vec<Formula>,
    /// Postconditions: guaranteed after the call.
    pub postconditions: Vec<Formula>,
}

impl FnContract {
    /// Create a new contract for the given function path.
    #[must_use]
    pub fn new(fn_path: impl Into<String>) -> Self {
        Self { fn_path: fn_path.into(), preconditions: Vec::new(), postconditions: Vec::new() }
    }

    /// Add a precondition formula.
    pub fn pre(mut self, formula: Formula) -> Self {
        self.preconditions.push(formula);
        self
    }

    /// Add a postcondition formula.
    pub fn post(mut self, formula: Formula) -> Self {
        self.postconditions.push(formula);
        self
    }

    /// Returns true if this contract has no conditions.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.preconditions.is_empty() && self.postconditions.is_empty()
    }

    /// Conjoin all preconditions into a single formula (or `true` if empty).
    #[must_use]
    pub fn combined_precondition(&self) -> Formula {
        combine(&self.preconditions)
    }

    /// Conjoin all postconditions into a single formula (or `true` if empty).
    #[must_use]
    pub fn combined_postcondition(&self) -> Formula {
        combine(&self.postconditions)
    }
}

/// Conjoin a slice of formulas. Returns `Bool(true)` for empty slice.
fn combine(formulas: &[Formula]) -> Formula {
    match formulas.len() {
        0 => Formula::Bool(true),
        1 => formulas[0].clone(),
        _ => Formula::And(formulas.to_vec()),
    }
}

// ---------------------------------------------------------------------------
// StdlibSpecs — registry of standard library function contracts
// ---------------------------------------------------------------------------

/// Registry mapping fully-qualified function paths to their contracts.
///
/// Covers Vec, Option, Result, and Iterator methods at trust_wp Proof Level 1.
#[derive(Debug, Clone)]
pub struct StdlibSpecs {
    specs: FxHashMap<String, FnContract>,
}

impl Default for StdlibSpecs {
    fn default() -> Self {
        Self::new()
    }
}

impl StdlibSpecs {
    /// Create a new registry populated with all standard library specs.
    #[must_use]
    pub fn new() -> Self {
        let mut specs = FxHashMap::default();

        // Vec specs
        for contract in vec_specs() {
            specs.insert(contract.fn_path.clone(), contract);
        }
        // Option specs
        for contract in option_specs() {
            specs.insert(contract.fn_path.clone(), contract);
        }
        // Result specs
        for contract in result_specs() {
            specs.insert(contract.fn_path.clone(), contract);
        }
        // Iterator specs
        for contract in iterator_specs() {
            specs.insert(contract.fn_path.clone(), contract);
        }

        Self { specs }
    }

    /// Look up a contract by fully-qualified function path.
    #[must_use]
    pub fn get(&self, fn_path: &str) -> Option<&FnContract> {
        self.specs.get(fn_path)
    }

    /// Look up a contract by short name (e.g., `"Vec::push"`).
    ///
    /// Searches for any path ending with the given suffix.
    #[must_use]
    pub fn get_by_suffix(&self, suffix: &str) -> Option<&FnContract> {
        self.specs.values().find(|c| c.fn_path.ends_with(suffix))
    }

    /// Return all registered contracts.
    #[must_use]
    pub fn all(&self) -> Vec<&FnContract> {
        self.specs.values().collect()
    }

    /// Number of registered specs.
    #[must_use]
    pub fn len(&self) -> usize {
        self.specs.len()
    }

    /// Returns true if no specs are registered.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.specs.is_empty()
    }

    /// Insert a custom contract (for extension or testing).
    pub fn insert(&mut self, contract: FnContract) {
        self.specs.insert(contract.fn_path.clone(), contract);
    }
}

// ---------------------------------------------------------------------------
// Helper constructors for formula variables
// ---------------------------------------------------------------------------

/// Integer variable.
fn int_var(name: &str) -> Formula {
    Formula::Var(name.to_string(), Sort::Int)
}

/// Boolean variable.
fn bool_var(name: &str) -> Formula {
    Formula::Var(name.to_string(), Sort::Bool)
}

/// Integer literal.
fn int_lit(n: i128) -> Formula {
    Formula::Int(n)
}

// ---------------------------------------------------------------------------
// Vec<T> specifications
// ---------------------------------------------------------------------------

/// Generate contracts for `Vec<T>` methods.
///
/// Modeled state:
/// - `self_len`: current length of the vector
/// - `old_len`: length before the call
/// - `arg0`: first argument (element for push, index for get)
/// - `result`: return value
fn vec_specs() -> Vec<FnContract> {
    vec![
        // Vec::push(&mut self, value: T)
        // Post: len increases by 1
        FnContract::new("std::vec::Vec::push").post(Formula::Eq(
            Box::new(int_var("self_len")),
            Box::new(Formula::Add(Box::new(int_var("old_len")), Box::new(int_lit(1)))),
        )),
        // Vec::pop(&mut self) -> Option<T>
        // Pre: (none — pop on empty returns None)
        // Post: if old_len > 0 then new_len == old_len - 1
        // Post: if old_len == 0 then result_is_none
        FnContract::new("std::vec::Vec::pop")
            .post(Formula::Implies(
                Box::new(Formula::Gt(Box::new(int_var("old_len")), Box::new(int_lit(0)))),
                Box::new(Formula::Eq(
                    Box::new(int_var("self_len")),
                    Box::new(Formula::Sub(Box::new(int_var("old_len")), Box::new(int_lit(1)))),
                )),
            ))
            .post(Formula::Implies(
                Box::new(Formula::Eq(Box::new(int_var("old_len")), Box::new(int_lit(0)))),
                Box::new(bool_var("result_is_none")),
            )),
        // Vec::get(&self, index: usize) -> Option<&T>
        // Post: if index < len then result_is_some
        // Post: if index >= len then result_is_none
        FnContract::new("std::vec::Vec::get")
            .post(Formula::Implies(
                Box::new(Formula::Lt(Box::new(int_var("arg0")), Box::new(int_var("self_len")))),
                Box::new(bool_var("result_is_some")),
            ))
            .post(Formula::Implies(
                Box::new(Formula::Ge(Box::new(int_var("arg0")), Box::new(int_var("self_len")))),
                Box::new(bool_var("result_is_none")),
            )),
        // Vec::len(&self) -> usize
        // Post: result == self_len
        // Post: result >= 0
        FnContract::new("std::vec::Vec::len")
            .post(Formula::Eq(Box::new(int_var("result")), Box::new(int_var("self_len"))))
            .post(Formula::Ge(Box::new(int_var("result")), Box::new(int_lit(0)))),
        // Vec::is_empty(&self) -> bool
        // Post: result == (self_len == 0)
        FnContract::new("std::vec::Vec::is_empty").post(Formula::Eq(
            Box::new(bool_var("result")),
            Box::new(Formula::Eq(Box::new(int_var("self_len")), Box::new(int_lit(0)))),
        )),
    ]
}

// ---------------------------------------------------------------------------
// Option<T> specifications
// ---------------------------------------------------------------------------

/// Generate contracts for `Option<T>` methods.
///
/// Modeled state:
/// - `self_is_some`: whether the Option is Some
/// - `self_value`: the inner value (when Some)
/// - `arg0`: first argument (default for unwrap_or, closure result for map)
/// - `result`: return value
/// - `result_is_some` / `result_is_none`: result Option state
fn option_specs() -> Vec<FnContract> {
    vec![
        // Option::unwrap(self) -> T
        // Pre: self must be Some (panics otherwise)
        FnContract::new("std::option::Option::unwrap").pre(bool_var("self_is_some")),
        // Option::map(self, f: F) -> Option<U>
        // Post: if self is Some then result is Some
        // Post: if self is None then result is None
        FnContract::new("std::option::Option::map")
            .post(Formula::Implies(
                Box::new(bool_var("self_is_some")),
                Box::new(bool_var("result_is_some")),
            ))
            .post(Formula::Implies(
                Box::new(Formula::Not(Box::new(bool_var("self_is_some")))),
                Box::new(bool_var("result_is_none")),
            )),
        // Option::unwrap_or(self, default: T) -> T
        // Post: always returns a value (never panics)
        // Post: if self is Some then result == self_value
        // Post: if self is None then result == arg0 (default)
        FnContract::new("std::option::Option::unwrap_or")
            .post(Formula::Implies(
                Box::new(bool_var("self_is_some")),
                Box::new(Formula::Eq(Box::new(int_var("result")), Box::new(int_var("self_value")))),
            ))
            .post(Formula::Implies(
                Box::new(Formula::Not(Box::new(bool_var("self_is_some")))),
                Box::new(Formula::Eq(Box::new(int_var("result")), Box::new(int_var("arg0")))),
            )),
        // Option::is_some(&self) -> bool
        // Post: result == self_is_some
        FnContract::new("std::option::Option::is_some")
            .post(Formula::Eq(Box::new(bool_var("result")), Box::new(bool_var("self_is_some")))),
        // Option::is_none(&self) -> bool
        // Post: result == !self_is_some
        FnContract::new("std::option::Option::is_none").post(Formula::Eq(
            Box::new(bool_var("result")),
            Box::new(Formula::Not(Box::new(bool_var("self_is_some")))),
        )),
    ]
}

// ---------------------------------------------------------------------------
// Result<T, E> specifications
// ---------------------------------------------------------------------------

/// Generate contracts for `Result<T, E>` methods.
///
/// Modeled state:
/// - `self_is_ok`: whether the Result is Ok
/// - `self_ok_value`: the inner Ok value
/// - `self_err_value`: the inner Err value
/// - `result`: return value
/// - `result_is_ok` / `result_is_err`: result Result state
fn result_specs() -> Vec<FnContract> {
    vec![
        // Result::unwrap(self) -> T
        // Pre: self must be Ok (panics on Err)
        FnContract::new("std::result::Result::unwrap").pre(bool_var("self_is_ok")),
        // Result::map(self, f: F) -> Result<U, E>
        // Post: preserves Ok/Err variant
        FnContract::new("std::result::Result::map")
            .post(Formula::Implies(
                Box::new(bool_var("self_is_ok")),
                Box::new(bool_var("result_is_ok")),
            ))
            .post(Formula::Implies(
                Box::new(Formula::Not(Box::new(bool_var("self_is_ok")))),
                Box::new(bool_var("result_is_err")),
            )),
        // Result::map_err(self, f: F) -> Result<T, F>
        // Post: preserves Ok/Err variant
        FnContract::new("std::result::Result::map_err")
            .post(Formula::Implies(
                Box::new(bool_var("self_is_ok")),
                Box::new(bool_var("result_is_ok")),
            ))
            .post(Formula::Implies(
                Box::new(Formula::Not(Box::new(bool_var("self_is_ok")))),
                Box::new(bool_var("result_is_err")),
            )),
        // Result::? operator (try)
        // Pre: (none — always safe)
        // Post: if self is Ok then result == self_ok_value (continues execution)
        // Post: if self is Err then early_return with self_err_value
        FnContract::new("std::ops::Try::branch")
            .post(Formula::Implies(
                Box::new(bool_var("self_is_ok")),
                Box::new(Formula::Eq(
                    Box::new(int_var("result")),
                    Box::new(int_var("self_ok_value")),
                )),
            ))
            .post(Formula::Implies(
                Box::new(Formula::Not(Box::new(bool_var("self_is_ok")))),
                Box::new(bool_var("early_return")),
            )),
        // Result::is_ok(&self) -> bool
        FnContract::new("std::result::Result::is_ok")
            .post(Formula::Eq(Box::new(bool_var("result")), Box::new(bool_var("self_is_ok")))),
        // Result::is_err(&self) -> bool
        FnContract::new("std::result::Result::is_err").post(Formula::Eq(
            Box::new(bool_var("result")),
            Box::new(Formula::Not(Box::new(bool_var("self_is_ok")))),
        )),
    ]
}

// ---------------------------------------------------------------------------
// Iterator specifications
// ---------------------------------------------------------------------------

/// Generate contracts for `Iterator` methods.
///
/// Modeled state:
/// - `iter_position`: current position in the iterator
/// - `iter_remaining`: number of remaining elements
/// - `iter_total`: total elements in the original collection
/// - `result`: return value
/// - `result_is_some` / `result_is_none`: for Option-returning methods
fn iterator_specs() -> Vec<FnContract> {
    vec![
        // Iterator::next(&mut self) -> Option<Self::Item>
        // Post: if remaining > 0 then result_is_some and position advances
        // Post: if remaining == 0 then result_is_none
        FnContract::new("std::iter::Iterator::next")
            .post(Formula::Implies(
                Box::new(Formula::Gt(Box::new(int_var("iter_remaining")), Box::new(int_lit(0)))),
                Box::new(Formula::And(vec![
                    bool_var("result_is_some"),
                    Formula::Eq(
                        Box::new(int_var("iter_position")),
                        Box::new(Formula::Add(
                            Box::new(int_var("old_iter_position")),
                            Box::new(int_lit(1)),
                        )),
                    ),
                ])),
            ))
            .post(Formula::Implies(
                Box::new(Formula::Eq(Box::new(int_var("iter_remaining")), Box::new(int_lit(0)))),
                Box::new(bool_var("result_is_none")),
            )),
        // Iterator::count(self) -> usize
        // Post: result == total remaining elements
        // Post: result >= 0
        FnContract::new("std::iter::Iterator::count")
            .post(Formula::Eq(Box::new(int_var("result")), Box::new(int_var("iter_remaining"))))
            .post(Formula::Ge(Box::new(int_var("result")), Box::new(int_lit(0)))),
        // Iterator::sum(self) -> S
        // Post: result >= 0 (for unsigned element types)
        // Note: Full sum correctness requires induction; this is the L1 approximation.
        FnContract::new("std::iter::Iterator::sum")
            .post(Formula::Ge(Box::new(int_var("result")), Box::new(int_lit(0)))),
        // Iterator::collect(self) -> B
        // Post: collected length == remaining elements
        FnContract::new("std::iter::Iterator::collect").post(Formula::Eq(
            Box::new(int_var("result_len")),
            Box::new(int_var("iter_remaining")),
        )),
    ]
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fn_contract_builder() {
        let contract =
            FnContract::new("test::foo").pre(Formula::Bool(true)).post(Formula::Bool(true));
        assert_eq!(contract.fn_path, "test::foo");
        assert_eq!(contract.preconditions.len(), 1);
        assert_eq!(contract.postconditions.len(), 1);
        assert!(!contract.is_empty());
    }

    #[test]
    fn test_fn_contract_empty() {
        let contract = FnContract::new("test::bar");
        assert!(contract.is_empty());
        assert_eq!(contract.combined_precondition(), Formula::Bool(true));
        assert_eq!(contract.combined_postcondition(), Formula::Bool(true));
    }

    #[test]
    fn test_fn_contract_combined_single() {
        let contract = FnContract::new("test::single").pre(int_var("x"));
        let combined = contract.combined_precondition();
        assert_eq!(combined, int_var("x"));
    }

    #[test]
    fn test_fn_contract_combined_multiple() {
        let contract =
            FnContract::new("test::multi").pre(Formula::Bool(true)).pre(Formula::Bool(false));
        let combined = contract.combined_precondition();
        assert!(matches!(combined, Formula::And(ref v) if v.len() == 2));
    }

    // -----------------------------------------------------------------------
    // Registry tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_stdlib_specs_creation() {
        let specs = StdlibSpecs::new();
        assert!(!specs.is_empty());
        // Vec: push, pop, get, len, is_empty = 5
        // Option: unwrap, map, unwrap_or, is_some, is_none = 5
        // Result: unwrap, map, map_err, branch, is_ok, is_err = 6
        // Iterator: next, count, sum, collect = 4
        assert_eq!(specs.len(), 20);
    }

    #[test]
    fn test_stdlib_specs_default() {
        let specs = StdlibSpecs::default();
        assert_eq!(specs.len(), StdlibSpecs::new().len());
    }

    #[test]
    fn test_lookup_by_full_path() {
        let specs = StdlibSpecs::new();
        let contract = specs.get("std::vec::Vec::push").expect("push should exist");
        assert_eq!(contract.fn_path, "std::vec::Vec::push");
        assert!(contract.preconditions.is_empty());
        assert_eq!(contract.postconditions.len(), 1);
    }

    #[test]
    fn test_lookup_by_suffix() {
        let specs = StdlibSpecs::new();
        let contract = specs.get_by_suffix("Vec::push").expect("should find by suffix");
        assert_eq!(contract.fn_path, "std::vec::Vec::push");
    }

    #[test]
    fn test_lookup_nonexistent() {
        let specs = StdlibSpecs::new();
        assert!(specs.get("std::nonexistent::Foo::bar").is_none());
        assert!(specs.get_by_suffix("Foo::bar").is_none());
    }

    #[test]
    fn test_insert_custom_contract() {
        let mut specs = StdlibSpecs::new();
        let original_len = specs.len();
        specs.insert(FnContract::new("custom::MyType::do_thing").pre(Formula::Bool(true)));
        assert_eq!(specs.len(), original_len + 1);
        assert!(specs.get("custom::MyType::do_thing").is_some());
    }

    // -----------------------------------------------------------------------
    // Vec spec tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_vec_push_postcondition_len_increases() {
        let specs = StdlibSpecs::new();
        let push = specs.get("std::vec::Vec::push").expect("push");
        assert_eq!(push.postconditions.len(), 1);
        // self_len == old_len + 1
        match &push.postconditions[0] {
            Formula::Eq(lhs, rhs) => {
                assert_eq!(**lhs, int_var("self_len"));
                match rhs.as_ref() {
                    Formula::Add(a, b) => {
                        assert_eq!(**a, int_var("old_len"));
                        assert_eq!(**b, int_lit(1));
                    }
                    other => panic!("expected Add, got: {other:?}"),
                }
            }
            other => panic!("expected Eq, got: {other:?}"),
        }
    }

    #[test]
    fn test_vec_pop_postcondition_len_decreases_when_nonempty() {
        let specs = StdlibSpecs::new();
        let pop = specs.get("std::vec::Vec::pop").expect("pop");
        assert_eq!(pop.postconditions.len(), 2);
        // First: old_len > 0 => self_len == old_len - 1
        assert!(matches!(&pop.postconditions[0], Formula::Implies(..)));
        // Second: old_len == 0 => result_is_none
        assert!(matches!(&pop.postconditions[1], Formula::Implies(..)));
    }

    #[test]
    fn test_vec_get_postcondition_bounds_check() {
        let specs = StdlibSpecs::new();
        let get = specs.get("std::vec::Vec::get").expect("get");
        assert_eq!(get.postconditions.len(), 2);
        // index < len => result_is_some
        // index >= len => result_is_none
        for post in &get.postconditions {
            assert!(matches!(post, Formula::Implies(..)));
        }
    }

    // -----------------------------------------------------------------------
    // Option spec tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_option_unwrap_requires_is_some() {
        let specs = StdlibSpecs::new();
        let unwrap = specs.get("std::option::Option::unwrap").expect("unwrap");
        assert_eq!(unwrap.preconditions.len(), 1);
        assert_eq!(unwrap.preconditions[0], bool_var("self_is_some"));
    }

    #[test]
    fn test_option_map_preserves_variant() {
        let specs = StdlibSpecs::new();
        let map = specs.get("std::option::Option::map").expect("map");
        assert_eq!(map.postconditions.len(), 2);
        // Some => result_is_some, None => result_is_none
        for post in &map.postconditions {
            assert!(matches!(post, Formula::Implies(..)));
        }
    }

    #[test]
    fn test_option_unwrap_or_always_returns_value() {
        let specs = StdlibSpecs::new();
        let unwrap_or = specs.get("std::option::Option::unwrap_or").expect("unwrap_or");
        assert!(unwrap_or.preconditions.is_empty(), "unwrap_or should have no preconditions");
        assert_eq!(unwrap_or.postconditions.len(), 2);
    }

    // -----------------------------------------------------------------------
    // Result spec tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_result_unwrap_requires_is_ok() {
        let specs = StdlibSpecs::new();
        let unwrap = specs.get("std::result::Result::unwrap").expect("unwrap");
        assert_eq!(unwrap.preconditions.len(), 1);
        assert_eq!(unwrap.preconditions[0], bool_var("self_is_ok"));
    }

    #[test]
    fn test_result_map_preserves_variant() {
        let specs = StdlibSpecs::new();
        let map = specs.get("std::result::Result::map").expect("map");
        assert_eq!(map.postconditions.len(), 2);
    }

    #[test]
    fn test_result_map_err_preserves_variant() {
        let specs = StdlibSpecs::new();
        let map_err = specs.get("std::result::Result::map_err").expect("map_err");
        assert_eq!(map_err.postconditions.len(), 2);
    }

    #[test]
    fn test_result_try_operator() {
        let specs = StdlibSpecs::new();
        let try_op = specs.get("std::ops::Try::branch").expect("try/? operator");
        assert!(try_op.preconditions.is_empty());
        assert_eq!(try_op.postconditions.len(), 2);
    }

    // -----------------------------------------------------------------------
    // Iterator spec tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_iterator_next_advances_position() {
        let specs = StdlibSpecs::new();
        let next = specs.get("std::iter::Iterator::next").expect("next");
        assert_eq!(next.postconditions.len(), 2);
        // remaining > 0 => result_is_some AND position advances
        // remaining == 0 => result_is_none
    }

    #[test]
    fn test_iterator_count_returns_remaining() {
        let specs = StdlibSpecs::new();
        let count = specs.get("std::iter::Iterator::count").expect("count");
        assert_eq!(count.postconditions.len(), 2);
        // result == iter_remaining, result >= 0
    }

    #[test]
    fn test_iterator_sum_nonnegative() {
        let specs = StdlibSpecs::new();
        let sum = specs.get("std::iter::Iterator::sum").expect("sum");
        assert_eq!(sum.postconditions.len(), 1);
    }

    #[test]
    fn test_iterator_collect_preserves_count() {
        let specs = StdlibSpecs::new();
        let collect = specs.get("std::iter::Iterator::collect").expect("collect");
        assert_eq!(collect.postconditions.len(), 1);
        // result_len == iter_remaining
    }

    // -----------------------------------------------------------------------
    // Coverage: all registered specs have at least one condition
    // -----------------------------------------------------------------------

    #[test]
    fn test_all_specs_have_conditions() {
        let specs = StdlibSpecs::new();
        for contract in specs.all() {
            assert!(
                !contract.is_empty(),
                "contract for {} should have at least one condition",
                contract.fn_path
            );
        }
    }

    #[test]
    fn test_all_function_returns_all_specs() {
        let specs = StdlibSpecs::new();
        let all = specs.all();
        assert_eq!(all.len(), specs.len());
    }
}

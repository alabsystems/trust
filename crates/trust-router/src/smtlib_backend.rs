// trust-router/smtlib_backend.rs: SMT-LIB2 serialization + shared utility functions
//
// Serializes Formula to SMT-LIB2 text and parses solver output. The legacy
// SmtLibBackend subprocess struct has been removed in favor of direct library
// calls. The serialization and result-parsing utilities remain in production;
// the stderr classifier remains as regression-tested historical policy only.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;
use std::fmt::Write;

use trust_types::*;

use crate::smt2_export;

// SmtLibBackend struct, its subprocess-based impls, and kill_process_by_pid
// removed — superseded by direct library calls via
// trust-bmc / trust_wp). The utility functions below (generate_smtlib_script,
// parse_solver_output, stderr_indicates_unreliable) remain in use.

/// Check if solver stderr contains patterns indicating the result
/// may be unreliable. These patterns suggest the solver hit resource limits,
/// used incomplete quantifier instantiation, or otherwise produced a result
/// that should not be trusted as a definitive proof.
///
/// Returns `true` if any unreliability indicator is found in stderr.
#[cfg(test)]
pub(crate) fn stderr_indicates_unreliable(stderr: &str) -> bool {
    if stderr.is_empty() {
        return false;
    }
    let lower = stderr.to_lowercase();
    // Patterns that indicate the solver result may be unreliable:
    // - rlimit / resource limit exhaustion
    // - incomplete quantifier instantiation
    // - timeout within the solver (internal timeout, not our process timeout)
    // - memory limit
    // - "gave up" / "approximat" heuristic fallback
    const UNRELIABLE_PATTERNS: &[&str] = &[
        "rlimit",
        "resource limit",
        "incomplete",
        "quantifier instantiation",
        "timeout",
        "memout",
        "memory limit",
        "gave up",
        "approximat",
    ];
    UNRELIABLE_PATTERNS.iter().any(|pat| lower.contains(pat))
}

/// Generate a complete SMT-LIB2 script for a verification condition.
///
/// The script installs the query's EFFORT count (`effort`, the one
/// size-scaled count `min(C, max(1, k · size))` over this script's one
/// assertion, sent as ay `(set-option :rlimit N)` before its check-sat: the
/// deterministic bound that ends an undecided search; the caller's wall clock
/// is only a backstop), declares variables, asserts the formula, calls
/// check-sat, and if sat, calls get-model to extract counterexample values. It
/// ends by asking for ay's statistics block, whose `:unknown.reason` says WHY
/// an `unknown` stopped (see [`crate::ay_stop`]).
pub(crate) fn generate_smtlib_script(
    formula: &Formula,
    effort: trust_types::determinism::QueryEffort,
) -> String {
    let mut script = String::new();

    // THE SAME SELECTOR as the in-process lane and the canonical transcript:
    // `smt2_export::detect_logic`, i.e. the shared feature-set -> logic-name
    // lattice in `trust_types::logic_lattice`. Not a private rule of this
    // emitter's own — the previous `has_bitvectors() ? QF_BV : QF_LIA` missed
    // quantified formulas (a `QF_` prefix means quantifier-free) and the array
    // theory, and any second rule here would be free to disagree with the
    // program ay actually executes. Because it IS the same function, the M1
    // defect (a floating-point formula mixed with `Int`/`Real` arithmetic
    // headed `QF_FP`) reached this script emitter too and is fixed here by the
    // same change.
    let logic = smt2_export::detect_logic(formula);
    let _ = writeln!(script, "(set-logic {logic})");

    // Add:produce-models so (get-model) works correctly.
    script.push_str("(set-option :produce-models true)\n");

    // The query's deterministic effort count (plan §3.2a).
    let _ = writeln!(script, "{}", effort.smt2_command());

    // DECLARATIONS, from the same three sources the canonical transcript
    // (`problem_smt2`) composes, so the external-solver script and the
    // in-process program declare the same sorts and symbols under the same
    // logic line. The datatype sort preamble comes FIRST (a `declare-const` at
    // a datatype sort is malformed until its sort identifier is in scope), then
    // the free variables, then the uninterpreted `Pred`/`FnApp` symbols — which
    // this emitter used to omit entirely, so a script could apply `(dir_open d)`
    // or a bare `FnApp` symbol that nothing declared, under a `QF_UF*` logic
    // line that correctly said UF was needed.
    for decl in smt2_export::emit_sort_preamble(formula) {
        let _ = writeln!(script, "{decl}");
    }
    let mut vars = BTreeSet::new();
    collect_vars(formula, &mut vars);
    for (name, sort) in &vars {
        let _ = writeln!(
            script,
            "(declare-const {} {})",
            escape_smtlib_symbol(name),
            sort_to_smtlib(sort)
        );
    }
    for decl in smt2_export::uninterpreted_symbol_declarations(formula) {
        let _ = writeln!(script, "{decl}");
    }

    // Assert the formula
    let _ = writeln!(script, "(assert {})", formula_to_smtlib(formula));

    // Check satisfiability
    script.push_str("(check-sat)\n");

    // Request model on sat for counterexample extraction
    script.push_str("(get-model)\n");

    // ay's own account of the solve: on `unknown`, `:unknown.reason` names the
    // bound that ended it. Nothing reads it on a decided solve.
    script.push_str("(get-info :all-statistics)\n");

    script.push_str("(exit)\n");
    script
}

/// Delegate to the canonical `Formula::to_smtlib()` method in trust-types.
pub(crate) fn formula_to_smtlib(formula: &Formula) -> String {
    formula.to_smtlib()
}

/// Delegate to the canonical `Sort::to_smtlib()` method in trust-types.
fn sort_to_smtlib(sort: &Sort) -> String {
    sort.to_smtlib()
}

/// All free variables (with sorts) in a formula, quantifier-bound names
/// excluded.
///
/// Delegates to [`smt2_export::collect_free_vars`], the ONE free-variable
/// collector: this module carried a byte-for-byte duplicate of that walk, which
/// is the shape every divergence in this class has taken. `SymVar` resolves to
/// its string spelling so it gets a `declare-const` like a `Var`.
fn collect_vars(formula: &Formula, vars: &mut BTreeSet<(String, Sort)>) {
    vars.extend(smt2_export::collect_free_vars(formula));
}

// has_bitvectors: removed -- use Formula::has_bitvectors() directly.

/// Parse solver stdout into a VerificationResult.
///
/// Expected output format:
/// - First line: "sat", "unsat", or "unknown"
/// - If sat, subsequent lines contain the model in s-expression format
///
/// Accepts `solver_warnings` captured from stderr. These are
/// attached to `Proved` results so callers can inspect solver diagnostics.
pub(crate) fn parse_solver_output(
    output: &str,
    elapsed_ms: u64,
    solver_warnings: Vec<String>,
) -> VerificationResult {
    // Strip solver banner / comment lines before locating the verdict. ay
    // frames every session with DIMACS-style `c ` lines (`c ay.session.start …`
    // first, `c ay.session.end …` last), and SMT-LIB permits `;` comments;
    // none is part of the `(check-sat)` response. Without this the leading
    // `c ay.session.start` banner makes `starts_with("unsat")` fail and every
    // solve degrades to Unknown.
    let cleaned = output
        .lines()
        .filter(|line| {
            let t = line.trim_start();
            !(t == "c" || t.starts_with("c ") || t.starts_with(';'))
        })
        .collect::<Vec<_>>()
        .join("\n");
    let trimmed = cleaned.trim();

    if trimmed.starts_with("unsat") {
        return VerificationResult::Proved {
            solver: "ay-smtlib".into(),
            time_ms: elapsed_ms,
            // Parsed bare "unsat" with no validated proof => Unchecked assurance,
            // not Sound. A require_assurance boundary downgrades it.
            strength: ProofStrength::smt_unsat_unvalidated(),
            proof_certificate: None,
            solver_warnings: if solver_warnings.is_empty() { None } else { Some(solver_warnings) },
            native_proof_envelope: None,
        };
    }

    if trimmed.starts_with("sat") {
        let counterexample = parse_model(trimmed);
        return VerificationResult::Failed {
            solver: "ay-smtlib".into(),
            time_ms: elapsed_ms,
            counterexample,
        };
    }

    if trimmed.starts_with("unknown") {
        // ay's statistics block (requested by `generate_smtlib_script`) names
        // the bound that ended the search. Without it the stop is unexplained,
        // and an unexplained stop is never counted as reproducible.
        return match crate::ay_stop::AyUnknownAccount::parse(trimmed) {
            Some(account) => {
                account.stop().unknown_result("ay-smtlib", elapsed_ms, &account.describe())
            }
            None => trust_types::determinism::StopCause::Unclassified.unknown_result(
                "ay-smtlib",
                elapsed_ms,
                "solver returned unknown",
            ),
        };
    }

    // Parse errors or unexpected output: the solver broke protocol.
    trust_types::determinism::StopCause::SolverFault.unknown_result(
        "ay-smtlib",
        elapsed_ms,
        &format!("unexpected solver output: {}", &trimmed[..trimmed.len().min(200)]),
    )
}

/// Parse a model from solver output following the "sat" line.
///
/// Expected format (SMT-LIB2 ay-style):
/// ```text
/// sat
/// (model
///   (define-fun a () Int 42)
///   (define-fun b () Int 7)
/// )
/// ```
///
/// Or the parenthesized variant:
/// ```text
/// sat
/// (
///   (define-fun a () Int 42)
///   (define-fun b () Int 7)
/// )
/// ```
fn parse_model(output: &str) -> Option<Counterexample> {
    let mut assignments = Vec::new();

    // Find all define-fun entries
    for line in output.lines() {
        let trimmed = line.trim();
        if !trimmed.contains("define-fun") {
            continue;
        }

        // Parse: (define-fun <name> () <sort> <value>)
        if let Some(assignment) = parse_define_fun(trimmed) {
            assignments.push(assignment);
        }
    }

    if assignments.is_empty() {
        return None;
    }

    // Sort by name for deterministic output
    assignments.sort_by(|a, b| a.0.cmp(&b.0));
    Some(Counterexample::new(assignments))
}

/// Parse a single `(define-fun name () Sort value)` line.
fn parse_define_fun(line: &str) -> Option<(String, CounterexampleValue)> {
    // Strip outer parens and leading whitespace
    let content = line.trim().trim_start_matches('(');

    // Skip past "define-fun "
    let rest = content.strip_prefix("define-fun ")?;

    // Extract name (first token)
    let name_end = rest.find(|c: char| c.is_whitespace())?;
    let name = rest[..name_end].to_string();
    let rest = rest[name_end..].trim();

    // Skip past "()" (empty parameter list)
    let rest = rest.strip_prefix("()")?.trim();

    // Extract sort name (next token or parenthesized expression)
    let (sort_str, rest) = if rest.starts_with('(') {
        // Parenthesized sort like (_ BitVec 32)
        let depth = find_matching_paren(rest)?;
        (&rest[..=depth], rest[depth + 1..].trim())
    } else {
        let end = rest.find(|c: char| c.is_whitespace())?;
        (&rest[..end], rest[end..].trim())
    };

    // The rest is the value (possibly with trailing parens)
    let value_str = rest.trim_end_matches(')').trim();

    // Parse the value based on sort
    let value = parse_model_value(sort_str, value_str)?;

    Some((name, value))
}

/// Find the index of the matching closing paren for an opening paren at position 0.
fn find_matching_paren(s: &str) -> Option<usize> {
    let mut depth = 0;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Parse a model value given its SMT-LIB2 sort and value string.
fn parse_model_value(sort_str: &str, value_str: &str) -> Option<CounterexampleValue> {
    if sort_str == "Bool" {
        return match value_str {
            "true" => Some(CounterexampleValue::Bool(true)),
            "false" => Some(CounterexampleValue::Bool(false)),
            _ => None,
        };
    }

    if sort_str == "Int" {
        return parse_int_value(value_str);
    }

    // BitVec sort: (_ BitVec N)
    if sort_str.contains("BitVec") {
        return parse_bv_value(value_str);
    }

    None
}

/// Parse an integer value, handling SMT-LIB2 negation syntax `(- N)`.
fn parse_int_value(s: &str) -> Option<CounterexampleValue> {
    let s = s.trim();
    if s.starts_with("(-") || s.starts_with("(- ") {
        // Negative: (- 42) or (-42)
        let inner = s.trim_start_matches('(').trim_start_matches('-').trim().trim_end_matches(')');
        let n: i128 = inner.parse().ok()?;
        Some(CounterexampleValue::Int(-n))
    } else if let Ok(n) = s.parse::<i128>() {
        if n >= 0 {
            Some(CounterexampleValue::Uint(n as u128))
        } else {
            Some(CounterexampleValue::Int(n))
        }
    } else {
        None
    }
}

/// Parse a bitvector value like `#x0000000a` or `#b1010` or `(_ bv10 32)`.
fn parse_bv_value(s: &str) -> Option<CounterexampleValue> {
    let s = s.trim();
    if let Some(hex) = s.strip_prefix("#x") {
        let n = u128::from_str_radix(hex, 16).ok()?;
        Some(CounterexampleValue::Uint(n))
    } else if let Some(bin) = s.strip_prefix("#b") {
        let n = u128::from_str_radix(bin, 2).ok()?;
        Some(CounterexampleValue::Uint(n))
    } else if s.starts_with("(_ bv") {
        // (_ bv<value> <width>)
        let inner = s.trim_start_matches("(_ bv").trim_end_matches(')');
        let parts: Vec<&str> = inner.split_whitespace().collect();
        if let Some(val_str) = parts.first() {
            let n: u128 = val_str.parse().ok()?;
            Some(CounterexampleValue::Uint(n))
        } else {
            None
        }
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ---- Formula translation tests ----

    #[test]
    fn test_formula_to_smtlib_literals() {
        assert_eq!(formula_to_smtlib(&Formula::Bool(true)), "true");
        assert_eq!(formula_to_smtlib(&Formula::Bool(false)), "false");
        assert_eq!(formula_to_smtlib(&Formula::Int(42)), "42");
        assert_eq!(formula_to_smtlib(&Formula::Int(0)), "0");
        assert_eq!(formula_to_smtlib(&Formula::Int(-7)), "(- 7)");
    }

    #[test]
    fn test_formula_to_smtlib_variables() {
        let f = Formula::Var("x".to_string(), Sort::Int);
        assert_eq!(formula_to_smtlib(&f), "x");

        let f = Formula::Var("flag".to_string(), Sort::Bool);
        assert_eq!(formula_to_smtlib(&f), "flag");
    }

    #[test]
    fn test_formula_to_smtlib_arithmetic() {
        let a = Formula::Var("a".to_string(), Sort::Int);
        let b = Formula::Var("b".to_string(), Sort::Int);

        let add = Formula::Add(Box::new(a.clone()), Box::new(b.clone()));
        assert_eq!(formula_to_smtlib(&add), "(+ a b)");

        let sub = Formula::Sub(Box::new(a.clone()), Box::new(b.clone()));
        assert_eq!(formula_to_smtlib(&sub), "(- a b)");

        let mul = Formula::Mul(Box::new(a.clone()), Box::new(b.clone()));
        assert_eq!(formula_to_smtlib(&mul), "(* a b)");

        // soundness (round-7): Rust `/` and `%` are TRUNCATED, so they lower
        // to the sign-corrected encoding (not bare Euclidean div/mod).
        let div = Formula::Div(Box::new(a.clone()), Box::new(b.clone()));
        assert_eq!(
            formula_to_smtlib(&div),
            "(div (- a (ite (>= a 0) (mod a b) (- (mod (- a) b)))) b)"
        );

        let rem = Formula::Rem(Box::new(a), Box::new(b));
        assert_eq!(formula_to_smtlib(&rem), "(ite (>= a 0) (mod a b) (- (mod (- a) b)))");
    }

    #[test]
    fn test_formula_to_smtlib_comparisons() {
        let a = Formula::Var("a".to_string(), Sort::Int);
        let b = Formula::Var("b".to_string(), Sort::Int);

        assert_eq!(
            formula_to_smtlib(&Formula::Lt(Box::new(a.clone()), Box::new(b.clone()))),
            "(< a b)"
        );
        assert_eq!(
            formula_to_smtlib(&Formula::Le(Box::new(a.clone()), Box::new(b.clone()))),
            "(<= a b)"
        );
        assert_eq!(
            formula_to_smtlib(&Formula::Gt(Box::new(a.clone()), Box::new(b.clone()))),
            "(> a b)"
        );
        assert_eq!(
            formula_to_smtlib(&Formula::Ge(Box::new(a.clone()), Box::new(b.clone()))),
            "(>= a b)"
        );
        assert_eq!(formula_to_smtlib(&Formula::Eq(Box::new(a), Box::new(b))), "(= a b)");
    }

    #[test]
    fn test_formula_to_smtlib_boolean_connectives() {
        let a = Formula::Var("p".to_string(), Sort::Bool);
        let b = Formula::Var("q".to_string(), Sort::Bool);

        assert_eq!(formula_to_smtlib(&Formula::Not(Box::new(a.clone()))), "(not p)");
        assert_eq!(formula_to_smtlib(&Formula::And(vec![a.clone(), b.clone()])), "(and p q)");
        assert_eq!(formula_to_smtlib(&Formula::Or(vec![a.clone(), b.clone()])), "(or p q)");
        assert_eq!(formula_to_smtlib(&Formula::Implies(Box::new(a), Box::new(b))), "(=> p q)");

        // Empty and/or
        assert_eq!(formula_to_smtlib(&Formula::And(vec![])), "true");
        assert_eq!(formula_to_smtlib(&Formula::Or(vec![])), "false");
    }

    #[test]
    fn test_formula_to_smtlib_nested() {
        // (a + b) > MAX -- the midpoint overflow formula shape
        let a = Formula::Var("a".to_string(), Sort::Int);
        let b = Formula::Var("b".to_string(), Sort::Int);
        let sum = Formula::Add(Box::new(a), Box::new(b));
        let max_val = Formula::Int(18446744073709551615);
        let overflow = Formula::Gt(Box::new(sum), Box::new(max_val));

        assert_eq!(formula_to_smtlib(&overflow), "(> (+ a b) 18446744073709551615)");
    }

    #[test]
    fn test_formula_to_smtlib_bitvectors() {
        let bv = Formula::BitVec { value: 10, width: 32 };
        assert_eq!(formula_to_smtlib(&bv), "(_ bv10 32)");

        let a = Formula::Var("x".to_string(), Sort::BitVec(32));
        let b = Formula::Var("y".to_string(), Sort::BitVec(32));
        let bvadd = Formula::BvAdd(Box::new(a), Box::new(b), 32);
        assert_eq!(formula_to_smtlib(&bvadd), "(bvadd x y)");
    }

    #[test]
    fn test_formula_to_smtlib_ite() {
        let cond = Formula::Var("c".to_string(), Sort::Bool);
        let then = Formula::Int(1);
        let els = Formula::Int(0);
        let ite = Formula::Ite(Box::new(cond), Box::new(then), Box::new(els));
        assert_eq!(formula_to_smtlib(&ite), "(ite c 1 0)");
    }

    // ---- Output parsing tests ----

    #[test]
    fn test_parse_solver_output_unsat() {
        let result = parse_solver_output("unsat\n", 5, vec![]);
        assert!(result.is_proved());
        assert_eq!(result.solver_name(), "ay-smtlib");
        assert_eq!(result.time_ms(), 5);
        // No warnings when stderr is empty
        if let VerificationResult::Proved { solver_warnings, .. } = &result {
            assert!(solver_warnings.is_none());
        }
    }

    // Verify that stderr warnings are captured in Proved results
    #[test]
    fn test_parse_solver_output_unsat_with_warnings() {
        let warnings = vec![
            "WARNING: unknown option :produce-proofs".to_string(),
            "WARNING: deprecated feature used".to_string(),
        ];
        let result = parse_solver_output("unsat\n", 5, warnings.clone());
        assert!(result.is_proved());
        if let VerificationResult::Proved { solver_warnings, .. } = &result {
            let warnings = solver_warnings.as_ref().expect("should have warnings");
            assert_eq!(warnings.len(), 2);
            assert_eq!(warnings[0], "WARNING: unknown option :produce-proofs");
            assert_eq!(warnings[1], "WARNING: deprecated feature used");
        } else {
            panic!("expected Proved");
        }
    }

    #[test]
    fn test_parse_solver_output_sat_with_model() {
        let output = r#"sat
(model
  (define-fun a () Int 18446744073709551615)
  (define-fun b () Int 1)
)"#;
        let result = parse_solver_output(output, 10, vec![]);
        assert!(result.is_failed());
        if let VerificationResult::Failed { counterexample: Some(cex), .. } = &result {
            assert_eq!(cex.assignments.len(), 2);
            assert_eq!(cex.assignments[0].0, "a");
            assert_eq!(cex.assignments[1].0, "b");
        } else {
            panic!("expected Failed with counterexample");
        }
    }

    #[test]
    fn test_parse_solver_output_sat_no_model() {
        let result = parse_solver_output("sat\n", 3, vec![]);
        assert!(result.is_failed());
        if let VerificationResult::Failed { counterexample, .. } = &result {
            assert!(counterexample.is_none());
        } else {
            panic!("expected Failed");
        }
    }

    #[test]
    fn test_parse_solver_output_unknown() {
        let result = parse_solver_output("unknown\n", 1000, vec![]);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
        // No statistics block: the stop is unexplained, never deterministic.
        assert_eq!(
            trust_types::determinism::StopCause::of_result(&result),
            trust_types::determinism::StopCause::Unclassified
        );
    }

    #[test]
    fn an_unknown_names_the_bound_ay_says_ended_it() {
        use trust_types::determinism::StopCause;
        // What the one-shot script's trailing `(get-info :all-statistics)`
        // prints after `(get-model)` fails on an unknown.
        let output = "unknown\n(error \"line 9 column 10: model is not available\")\n\
                      (:conflicts 100000\n :unknown.reason \"resourceout\")\n";
        let result = parse_solver_output(output, 1700, vec![]);
        assert_eq!(StopCause::of_result(&result), StopCause::Effort);
        let clock = parse_solver_output("unknown\n(:unknown.reason \"timeout\")\n", 9, vec![]);
        assert_eq!(StopCause::of_result(&clock), StopCause::WallBackstop);
        let folded = parse_solver_output("unknown\n(:unknown.reason \"canceled\")\n", 9, vec![]);
        assert_eq!(StopCause::of_result(&folded), StopCause::Unclassified);
    }

    #[test]
    fn a_decided_solve_ignores_the_statistics_block() {
        let output = "sat\n(model\n  (define-fun a () Int 1)\n)\n(:conflicts 4\n :decisions 9)\n";
        let result = parse_solver_output(output, 3, vec![]);
        let VerificationResult::Failed { counterexample: Some(cex), .. } = &result else {
            panic!("expected Failed with counterexample, got {result:?}");
        };
        assert_eq!(cex.assignments.len(), 1, "statistics lines are not model entries");
        let proved = parse_solver_output("unsat\n(:conflicts 4)\n", 3, vec![]);
        assert!(proved.is_proved());
    }

    #[test]
    fn test_parse_solver_output_unexpected() {
        let result = parse_solver_output("(error \"some problem\")\n", 1, vec![]);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
        if let VerificationResult::Unknown { reason, .. } = &result {
            assert!(reason.contains("unexpected solver output"));
        }
        assert_eq!(
            trust_types::determinism::StopCause::of_result(&result),
            trust_types::determinism::StopCause::SolverFault
        );
    }

    #[test]
    fn the_script_carries_the_effort_budget_and_asks_why() {
        let formula = Formula::Bool(true);
        let script = generate_smtlib_script(
            &formula,
            trust_types::determinism::QueryEffort { size: 1, conflicts: 12_345 },
        );
        let rlimit = script.find("(set-option :rlimit 12345)").expect("effort budget sent");
        let check = script.find("(check-sat)").expect("check-sat sent");
        let stats = script.find("(get-info :all-statistics)").expect("statistics requested");
        assert!(
            rlimit < check && check < stats,
            "budget before the solve, account after:\n{script}"
        );
        assert!(!script.contains(":timeout"), "the wall clock is the caller's backstop, not ay's");
    }

    /// Plan §3.2a: the one-shot script's `:rlimit` is its own query's count,
    /// `k · size`, so two queries of different sizes carry different values.
    #[test]
    fn the_one_shot_script_carries_the_per_query_count() {
        use trust_types::determinism::EffortScale;
        let scale = EffortScale { conflicts_per_node: 10 };
        let x = || Formula::Var("x".into(), Sort::Int);
        let small = Formula::Lt(Box::new(x()), Box::new(Formula::Int(1)));
        let large = Formula::And(vec![
            Formula::Lt(Box::new(x()), Box::new(Formula::Int(1))),
            Formula::Gt(Box::new(x()), Box::new(Formula::Int(5))),
        ]);
        for formula in [small, large] {
            let effort = scale.for_query(&[&formula]);
            assert_eq!(effort.conflicts, 10 * trust_types::determinism::query_size(&[&formula]));
            let script = generate_smtlib_script(&formula, effort);
            assert!(
                script.contains(&format!("(set-option :rlimit {})\n", effort.conflicts)),
                "{script}"
            );
            assert_eq!(script.matches(":rlimit").count(), 1, "{script}");
        }
    }

    // ---- Model parsing tests ----

    #[test]
    fn test_parse_define_fun_int() {
        let line = "  (define-fun x () Int 42)";
        let (name, val) = parse_define_fun(line).expect("should parse");
        assert_eq!(name, "x");
        assert!(matches!(val, CounterexampleValue::Uint(42)));
    }

    #[test]
    fn test_parse_define_fun_negative_int() {
        let line = "  (define-fun y () Int (- 7))";
        let (name, val) = parse_define_fun(line).expect("should parse");
        assert_eq!(name, "y");
        assert!(matches!(val, CounterexampleValue::Int(-7)));
    }

    #[test]
    fn test_parse_define_fun_bool() {
        let line = "  (define-fun flag () Bool true)";
        let (name, val) = parse_define_fun(line).expect("should parse");
        assert_eq!(name, "flag");
        assert!(matches!(val, CounterexampleValue::Bool(true)));
    }

    #[test]
    fn test_parse_define_fun_bitvec_hex() {
        let line = "  (define-fun x () (_ BitVec 32) #x0000000a)";
        let (name, val) = parse_define_fun(line).expect("should parse");
        assert_eq!(name, "x");
        assert!(matches!(val, CounterexampleValue::Uint(10)));
    }

    #[test]
    fn test_parse_define_fun_bitvec_binary() {
        let line = "  (define-fun bits () (_ BitVec 4) #b1010)";
        let (name, val) = parse_define_fun(line).expect("should parse");
        assert_eq!(name, "bits");
        assert!(matches!(val, CounterexampleValue::Uint(10)));
    }

    // ---- Script generation tests ----

    #[test]
    fn test_generate_smtlib_script_simple() {
        // 2 == 0 (trivially unsat for division-by-zero check)
        let formula = Formula::Eq(Box::new(Formula::Int(2)), Box::new(Formula::Int(0)));
        let script = generate_smtlib_script(
            &formula,
            trust_types::determinism::EffortScale::BUILTIN.for_query(&[&formula]),
        );
        assert!(script.contains("(set-logic QF_LIA)"));
        assert!(script.contains("(assert (= 2 0))"));
        assert!(script.contains("(check-sat)"));
        assert!(script.contains("(exit)"));
        // No variable declarations for constant formula
        assert!(!script.contains("declare-const"));
    }

    #[test]
    fn test_generate_smtlib_script_with_vars() {
        let formula = Formula::Lt(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Int(10)),
        );
        let script = generate_smtlib_script(
            &formula,
            trust_types::determinism::EffortScale::BUILTIN.for_query(&[&formula]),
        );
        assert!(script.contains("(declare-const x Int)"));
        assert!(script.contains("(assert (< x 10))"));
    }

    #[test]
    fn test_generate_smtlib_script_bitvector_logic() {
        let formula = Formula::BvAdd(
            Box::new(Formula::Var("x".to_string(), Sort::BitVec(32))),
            Box::new(Formula::Var("y".to_string(), Sort::BitVec(32))),
            32,
        );
        let script = generate_smtlib_script(
            &formula,
            trust_types::determinism::EffortScale::BUILTIN.for_query(&[&formula]),
        );
        assert!(script.contains("(set-logic QF_BV)"));
        assert!(script.contains("(declare-const x (_ BitVec 32))"));
        assert!(script.contains("(declare-const y (_ BitVec 32))"));
    }

    // ---- Variable collection tests ----

    #[test]
    fn test_collect_vars_simple() {
        let formula = Formula::And(vec![
            Formula::Var("a".to_string(), Sort::Int),
            Formula::Var("b".to_string(), Sort::Int),
            Formula::Int(42),
        ]);
        let mut vars = BTreeSet::new();
        collect_vars(&formula, &mut vars);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&("a".to_string(), Sort::Int)));
        assert!(vars.contains(&("b".to_string(), Sort::Int)));
    }

    #[test]
    fn test_collect_vars_deduplicates() {
        let a = Formula::Var("x".to_string(), Sort::Int);
        let formula = Formula::Add(Box::new(a.clone()), Box::new(a));
        let mut vars = BTreeSet::new();
        collect_vars(&formula, &mut vars);
        assert_eq!(vars.len(), 1);
    }

    #[test]
    fn test_collect_vars_keeps_free_var_shadowed_by_nested_quantifier() {
        let free_x = Formula::Var("x".to_string(), Sort::Int);
        let bound_x = Formula::Var("x".to_string(), Sort::Int);
        let formula = Formula::And(vec![
            Formula::Gt(Box::new(free_x), Box::new(Formula::Int(0))),
            Formula::Exists(
                vec![(Symbol::intern("x"), Sort::Int)],
                Box::new(Formula::Gt(Box::new(bound_x), Box::new(Formula::Int(1)))),
            ),
        ]);

        let mut vars = BTreeSet::new();
        collect_vars(&formula, &mut vars);
        assert_eq!(vars.len(), 1);
        assert!(vars.contains(&("x".to_string(), Sort::Int)));

        let script = generate_smtlib_script(
            &formula,
            trust_types::determinism::EffortScale::BUILTIN.for_query(&[&formula]),
        );
        assert_eq!(script.matches("(declare-const x Int)").count(), 1);
    }

    #[test]
    fn test_collect_vars_excludes_only_active_quantifier_bindings() {
        let formula = Formula::Forall(
            vec![(Symbol::intern("x"), Sort::Int)],
            Box::new(Formula::Gt(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Var("y".to_string(), Sort::Int)),
            )),
        );

        let mut vars = BTreeSet::new();
        collect_vars(&formula, &mut vars);
        assert_eq!(vars.len(), 1);
        assert!(!vars.contains(&("x".to_string(), Sort::Int)));
        assert!(vars.contains(&("y".to_string(), Sort::Int)));

        let script = generate_smtlib_script(
            &formula,
            trust_types::determinism::EffortScale::BUILTIN.for_query(&[&formula]),
        );
        assert!(!script.contains("(declare-const x Int)"));
        assert!(script.contains("(declare-const y Int)"));
    }

    // SymVar must be collected just like Var.
    #[test]
    fn test_collect_vars_includes_symvar() {
        let sym = Symbol::intern("s");
        let formula = Formula::And(vec![
            Formula::Var("x".to_string(), Sort::Int),
            Formula::SymVar(sym, Sort::Bool),
        ]);
        let mut vars = BTreeSet::new();
        collect_vars(&formula, &mut vars);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&("x".to_string(), Sort::Int)));
        assert!(vars.contains(&("s".to_string(), Sort::Bool)));

        // Also verify the generated script includes declare-const for the SymVar
        let script = generate_smtlib_script(
            &formula,
            trust_types::determinism::EffortScale::BUILTIN.for_query(&[&formula]),
        );
        assert!(script.contains("(declare-const s Bool)"));
        assert!(script.contains("(declare-const x Int)"));
    }

    // ---- Sort translation tests ----

    #[test]
    fn test_sort_to_smtlib() {
        assert_eq!(sort_to_smtlib(&Sort::Bool), "Bool");
        assert_eq!(sort_to_smtlib(&Sort::Int), "Int");
        assert_eq!(sort_to_smtlib(&Sort::BitVec(64)), "(_ BitVec 64)");
        assert_eq!(
            sort_to_smtlib(&Sort::Array(Box::new(Sort::Int), Box::new(Sort::Bool))),
            "(Array Int Bool)"
        );
    }

    // ---- Integration-style test: midpoint overflow formula ----

    #[test]
    fn test_midpoint_overflow_script() {
        // The midpoint overflow VC: exists a, b in [0, MAX] such that a + b > MAX
        let max_val = (1i128 << 64) - 1;
        let a = Formula::Var("a".to_string(), Sort::Int);
        let b = Formula::Var("b".to_string(), Sort::Int);
        let sum = Formula::Add(Box::new(a.clone()), Box::new(b.clone()));

        let formula = Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(a.clone())),
            Formula::Le(Box::new(a), Box::new(Formula::Int(max_val))),
            Formula::Le(Box::new(Formula::Int(0)), Box::new(b.clone())),
            Formula::Le(Box::new(b), Box::new(Formula::Int(max_val))),
            Formula::Not(Box::new(Formula::And(vec![
                Formula::Le(Box::new(Formula::Int(0)), Box::new(sum.clone())),
                Formula::Le(Box::new(sum), Box::new(Formula::Int(max_val))),
            ]))),
        ]);

        let script = generate_smtlib_script(
            &formula,
            trust_types::determinism::EffortScale::BUILTIN.for_query(&[&formula]),
        );

        // Verify script structure
        assert!(script.contains("(set-logic QF_LIA)"));
        assert!(script.contains("(declare-const a Int)"));
        assert!(script.contains("(declare-const b Int)"));
        assert!(script.contains("(assert"));
        assert!(script.contains("(check-sat)"));
        assert!(script.contains("(get-model)"));

        // The overflow formula should contain the AND with bounds and NOT
        assert!(script.contains("(<= 0 a)"));
        assert!(script.contains(&format!("(<= a {max_val})")));
        assert!(script.contains("(not"));
    }

    // SmtLibBackend VerificationBackend trait tests removed — the struct is
    // dead code under pipeline-v2.

    // ---- stderr handling tests ----

    #[test]
    fn test_stderr_indicates_unreliable_empty() {
        assert!(!stderr_indicates_unreliable(""));
    }

    #[test]
    fn test_stderr_indicates_unreliable_benign_warning() {
        // A benign warning that is not an unreliability indicator
        assert!(!stderr_indicates_unreliable("WARNING: unknown logic QF_LIA\n"));
    }

    #[test]
    fn test_stderr_indicates_unreliable_rlimit() {
        assert!(stderr_indicates_unreliable("WARNING: rlimit reached\n"));
    }

    #[test]
    fn test_stderr_indicates_unreliable_resource_limit() {
        assert!(stderr_indicates_unreliable("(error \"resource limit exceeded\")\n"));
    }

    #[test]
    fn test_stderr_indicates_unreliable_incomplete() {
        assert!(stderr_indicates_unreliable("WARNING: incomplete quantifier instantiation\n"));
    }

    #[test]
    fn test_stderr_indicates_unreliable_timeout() {
        assert!(stderr_indicates_unreliable("WARNING: solver timeout in theory combination\n"));
    }

    #[test]
    fn test_stderr_indicates_unreliable_memout() {
        assert!(stderr_indicates_unreliable("memout\n"));
    }

    #[test]
    fn test_stderr_indicates_unreliable_case_insensitive() {
        assert!(stderr_indicates_unreliable("RLIMIT REACHED\n"));
        assert!(stderr_indicates_unreliable("Incomplete reasoning\n"));
    }

    #[test]
    fn test_stderr_indicates_unreliable_gave_up() {
        assert!(stderr_indicates_unreliable("WARNING: solver gave up on subproblem\n"));
    }

    #[test]
    fn test_stderr_indicates_unreliable_approximation() {
        assert!(stderr_indicates_unreliable("using approximation for nonlinear arithmetic\n"));
    }

    #[test]
    fn test_get_model_after_unsat_stderr_is_preserved_as_warning() {
        let stderr = "(error \"model is not available\")\n";
        assert!(!stderr_indicates_unreliable(stderr));

        let result =
            parse_solver_output("unsat\n", 5, vec!["(error \"model is not available\")".into()]);
        assert!(result.is_proved());
        if let VerificationResult::Proved { solver_warnings, .. } = &result {
            assert_eq!(
                solver_warnings.as_ref(),
                Some(&vec!["(error \"model is not available\")".to_string()])
            );
        } else {
            panic!("expected Proved");
        }
    }
}

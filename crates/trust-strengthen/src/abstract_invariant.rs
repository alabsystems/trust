// trust-strengthen/abstract_invariant.rs: Loop invariant inference from abstract domains
//
// Implements abstract interpretation over interval, octagon, sign, and
// congruence domains with widening/narrowing to compute loop invariant
// candidates. The inferred invariants are formatted as Trust spec annotations.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt;

// ---------------------------------------------------------------------------
// Abstract domains
// ---------------------------------------------------------------------------

/// An abstract domain element used for invariant inference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AbstractDomain {
    /// Interval domain: variable in [lo, hi].
    Interval { lo: i64, hi: i64 },
    /// Octagonal constraints: each (var1, var2, bound) means var1 - var2 <= bound.
    Octagon(Vec<(String, String, i64)>),
    /// Sign domain: positive, negative, zero, or unknown.
    Sign(String),
    /// Congruence domain: value === remainder (mod modulus).
    Congruence { modulus: u64, remainder: u64 },
    /// Top: no information (any value).
    Top,
    /// Bottom: unreachable / empty set.
    Bottom,
}

impl fmt::Display for AbstractDomain {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Interval { lo, hi } => write!(f, "[{lo}, {hi}]"),
            Self::Octagon(constraints) => {
                let parts: Vec<String> =
                    constraints.iter().map(|(a, b, c)| format!("{a} - {b} <= {c}")).collect();
                write!(f, "octagon({})", parts.join(", "))
            }
            Self::Sign(s) => write!(f, "sign({s})"),
            Self::Congruence { modulus, remainder } => {
                write!(f, "x === {remainder} (mod {modulus})")
            }
            Self::Top => write!(f, "top"),
            Self::Bottom => write!(f, "bottom"),
        }
    }
}

impl AbstractDomain {
    /// Join (least upper bound) of two abstract domain elements.
    /// Retained: core abstract domain operation, used by InvariantInferrer and tests.
    pub(crate) fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Bottom, x) | (x, Self::Bottom) => x.clone(),
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Interval { lo: l1, hi: h1 }, Self::Interval { lo: l2, hi: h2 }) => {
                Self::Interval { lo: (*l1).min(*l2), hi: (*h1).max(*h2) }
            }
            (Self::Sign(a), Self::Sign(b)) => {
                if a == b {
                    Self::Sign(a.clone())
                } else {
                    Self::Top
                }
            }
            (
                Self::Congruence { modulus: m1, remainder: r1 },
                Self::Congruence { modulus: m2, remainder: r2 },
            ) => {
                if m1 == m2 && r1 == r2 {
                    Self::Congruence { modulus: *m1, remainder: *r1 }
                } else {
                    Self::Top
                }
            }
            _ => Self::Top,
        }
    }

    /// Meet (greatest lower bound) of two abstract domain elements.
    /// Retained: core abstract domain operation, dual of join.
    #[cfg(test)]
    pub(crate) fn meet(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Top, x) | (x, Self::Top) => x.clone(),
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (Self::Interval { lo: l1, hi: h1 }, Self::Interval { lo: l2, hi: h2 }) => {
                let lo = (*l1).max(*l2);
                let hi = (*h1).min(*h2);
                if lo > hi { Self::Bottom } else { Self::Interval { lo, hi } }
            }
            (Self::Sign(a), Self::Sign(b)) => {
                if a == b {
                    Self::Sign(a.clone())
                } else {
                    Self::Bottom
                }
            }
            _ => Self::Bottom,
        }
    }

    /// Check whether this domain element is bottom (unreachable).
    /// Retained: core abstract domain predicate.
    #[cfg(test)]
    pub(crate) fn is_bottom(&self) -> bool {
        matches!(self, Self::Bottom)
    }

    /// Check whether this domain element is top (no information).
    /// Retained: core abstract domain predicate.
    #[cfg(test)]
    pub(crate) fn is_top(&self) -> bool {
        matches!(self, Self::Top)
    }
}

// ---------------------------------------------------------------------------
// Invariant candidate
// ---------------------------------------------------------------------------

/// A candidate loop invariant inferred from abstract interpretation.
#[derive(Debug, Clone, PartialEq)]
pub struct InvariantCandidate {
    /// Human-readable expression for the invariant (e.g. "0 <= x && x <= 100").
    pub expression: String,
    /// The abstract domain element that produced this candidate.
    pub domain: AbstractDomain,
    /// Confidence in [0.0, 1.0] that this invariant is correct.
    pub confidence: f64,
    /// Variables involved in the invariant.
    pub variables: Vec<String>,
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Precision level for abstract interpretation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DomainPrecision {
    /// Fast but imprecise: only interval domain.
    Low,
    /// Balanced: intervals + sign.
    Medium,
    /// Slow but precise: intervals + octagons + congruence.
    High,
}

/// Configuration for the invariant inference engine.
#[derive(Debug, Clone)]
pub struct AbstractInferenceConfig {
    /// Maximum number of widening steps before giving up.
    pub max_widening_steps: usize,
    /// Which abstract domains to use.
    pub precision: DomainPrecision,
    /// Whether to apply narrowing after widening to recover precision.
    pub use_narrowing: bool,
}

impl Default for AbstractInferenceConfig {
    fn default() -> Self {
        Self { max_widening_steps: 100, precision: DomainPrecision::Medium, use_narrowing: true }
    }
}

// ---------------------------------------------------------------------------
// Inference result
// ---------------------------------------------------------------------------

/// Result of invariant inference over a loop.
#[derive(Debug, Clone)]
pub struct AbstractInferenceResult {
    /// Candidate invariants produced.
    pub candidates: Vec<InvariantCandidate>,
    /// Number of abstract interpretation iterations performed.
    pub iterations: usize,
    /// Whether the analysis reached a fixed point.
    pub converged: bool,
}

// ---------------------------------------------------------------------------
// Invariant inferrer
// ---------------------------------------------------------------------------

/// Infers loop invariants using abstract interpretation with widening.
#[derive(Debug, Clone)]
pub struct InvariantInferrer {
    config: AbstractInferenceConfig,
}

impl InvariantInferrer {
    /// Create a new invariant inferrer with the given configuration.
    pub fn new(config: AbstractInferenceConfig) -> Self {
        Self { config }
    }

    /// Infer loop invariants from a textual representation of a loop.
    ///
    /// `loop_body` is a simplified representation of the loop body statements
    /// (one per line, e.g. "x = x + 1"). `init_state` describes the initial
    /// state before the loop (e.g. "x = 0").
    pub fn infer_loop_invariant(
        &self,
        loop_body: &str,
        init_state: &str,
    ) -> AbstractInferenceResult {
        // Parse initial state into an abstract domain
        let mut state = self.parse_init_state(init_state);
        let statements: Vec<&str> = loop_body.lines().filter(|l| !l.trim().is_empty()).collect();

        let mut iterations = 0;
        let mut converged = false;

        for _ in 0..self.config.max_widening_steps {
            // Trust: fail closed on per-function verify-budget exhaustion. A widened
            // state that has not yet reached a fixpoint is not a sound loop invariant,
            // so drop the strengthening entirely (no candidates, not converged) rather
            // than emit a non-inductive one. Completeness loss only, never a proof.
            if trust_types::verify_budget::budget_exhausted() {
                return AbstractInferenceResult { candidates: Vec::new(), iterations, converged: false };
            }
            iterations += 1;

            // Apply transfer functions for each statement
            let mut new_state = state.clone();
            for stmt in &statements {
                new_state = self.abstract_transfer(&new_state, stmt);
            }

            // Widen to force convergence
            let widened = self.widen_invariant(&state, &new_state);

            if widened == state {
                converged = true;
                break;
            }

            state = widened;
        }

        // Optionally narrow to recover precision (only tighten infinite bounds)
        if converged && self.config.use_narrowing {
            for stmt in &statements {
                let transferred = self.abstract_transfer(&state, stmt);
                state = self.narrow(&state, &transferred);
            }
        }

        // Build candidates from the final abstract state
        let candidates = self.build_candidates(&state, loop_body, init_state);

        AbstractInferenceResult { candidates, iterations, converged }
    }

    /// Apply the abstract transfer function for a single statement.
    ///
    /// Supports simple patterns:
    /// - `x = x + N` / `x = x - N` (increment/decrement)
    /// - `x = N` (assignment to constant)
    /// - `x = y` (copy)
    pub fn abstract_transfer(&self, state: &AbstractDomain, statement: &str) -> AbstractDomain {
        let stmt = statement.trim();
        if stmt.is_empty() {
            return state.clone();
        }

        // Pattern: "x = x + N"
        if let Some(delta) = parse_increment(stmt) {
            return match state {
                AbstractDomain::Interval { lo, hi } => AbstractDomain::Interval {
                    lo: lo.saturating_add(delta),
                    hi: hi.saturating_add(delta),
                },
                AbstractDomain::Sign(s) if s == "positive" && delta > 0 => {
                    AbstractDomain::Sign("positive".into())
                }
                AbstractDomain::Sign(s) if s == "negative" && delta < 0 => {
                    AbstractDomain::Sign("negative".into())
                }
                AbstractDomain::Sign(_) if delta > 0 => AbstractDomain::Top,
                AbstractDomain::Sign(_) if delta < 0 => AbstractDomain::Top,
                AbstractDomain::Bottom => AbstractDomain::Bottom,
                _ => state.clone(),
            };
        }

        // Pattern: "x = N" (constant assignment)
        if let Some(val) = parse_const_assign(stmt) {
            return AbstractDomain::Interval { lo: val, hi: val };
        }

        // Unknown statement: return state unchanged (conservative)
        state.clone()
    }

    /// Widen: accelerate convergence by extrapolating the interval.
    ///
    /// Standard interval widening: if a bound grew, push it to +/- infinity
    /// (represented as i64::MIN / i64::MAX).
    pub fn widen_invariant(
        &self,
        old_inv: &AbstractDomain,
        new_inv: &AbstractDomain,
    ) -> AbstractDomain {
        match (old_inv, new_inv) {
            (AbstractDomain::Bottom, x) => x.clone(),
            (x, AbstractDomain::Bottom) => x.clone(),
            (
                AbstractDomain::Interval { lo: l1, hi: h1 },
                AbstractDomain::Interval { lo: l2, hi: h2 },
            ) => {
                let lo = if *l2 < *l1 { i64::MIN } else { *l1 };
                let hi = if *h2 > *h1 { i64::MAX } else { *h1 };
                AbstractDomain::Interval { lo, hi }
            }
            (AbstractDomain::Sign(a), AbstractDomain::Sign(b)) => {
                if a == b {
                    AbstractDomain::Sign(a.clone())
                } else {
                    AbstractDomain::Top
                }
            }
            (AbstractDomain::Top, _) | (_, AbstractDomain::Top) => AbstractDomain::Top,
            _ => new_inv.join(old_inv),
        }
    }

    /// Strengthen a candidate by tightening its domain or raising confidence.
    pub fn strengthen_candidate(&self, candidate: &InvariantCandidate) -> InvariantCandidate {
        match &candidate.domain {
            AbstractDomain::Interval { lo, hi } => {
                // If we have a finite interval, confidence is high
                let tighter_confidence = if *lo != i64::MIN && *hi != i64::MAX {
                    (candidate.confidence + 0.1).min(1.0)
                } else {
                    candidate.confidence
                };
                InvariantCandidate {
                    expression: candidate.expression.clone(),
                    domain: candidate.domain.clone(),
                    confidence: tighter_confidence,
                    variables: candidate.variables.clone(),
                }
            }
            AbstractDomain::Bottom => InvariantCandidate {
                expression: "false".into(),
                domain: AbstractDomain::Bottom,
                confidence: 1.0,
                variables: vec![],
            },
            _ => candidate.clone(),
        }
    }

    /// Validate that a candidate invariant is inductive over the loop body.
    ///
    /// Checks: applying the loop body to the invariant domain yields a state
    /// contained in (or equal to) the invariant domain.
    pub fn validate_invariant(&self, candidate: &InvariantCandidate, loop_body: &str) -> bool {
        let statements: Vec<&str> = loop_body.lines().filter(|l| !l.trim().is_empty()).collect();
        let mut state = candidate.domain.clone();

        for stmt in &statements {
            state = self.abstract_transfer(&state, stmt);
        }

        // Check inclusion: post-state should be subsumed by the candidate domain
        self.is_subsumed(&state, &candidate.domain)
    }

    /// Format a candidate invariant as a first-class Trust loop clause.
    pub fn format_as_spec(&self, candidate: &InvariantCandidate) -> String {
        match &candidate.domain {
            AbstractDomain::Interval { lo, hi } => {
                let var = candidate.variables.first().map(|s| s.as_str()).unwrap_or("x");
                if *lo == i64::MIN {
                    format!("invariant {var} <= {hi}")
                } else if *hi == i64::MAX {
                    format!("invariant {lo} <= {var}")
                } else {
                    format!("invariant {lo} <= {var} && {var} <= {hi}")
                }
            }
            AbstractDomain::Sign(s) => {
                let var = candidate.variables.first().map(|v| v.as_str()).unwrap_or("x");
                match s.as_str() {
                    "positive" => format!("invariant {var} > 0"),
                    "negative" => format!("invariant {var} < 0"),
                    "zero" => format!("invariant {var} == 0"),
                    "non_negative" => format!("invariant {var} >= 0"),
                    _ => format!("// unsupported invariant sign domain: {s}"),
                }
            }
            AbstractDomain::Congruence { modulus, remainder } => {
                let var = candidate.variables.first().map(|v| v.as_str()).unwrap_or("x");
                format!("invariant {var} % {modulus} == {remainder}")
            }
            AbstractDomain::Bottom => "invariant false".into(),
            AbstractDomain::Top => "invariant true".into(),
            AbstractDomain::Octagon(constraints) => {
                let parts: Vec<String> =
                    constraints.iter().map(|(a, b, c)| format!("{a} - {b} <= {c}")).collect();
                format!("invariant {}", parts.join(" && "))
            }
        }
    }

    // -----------------------------------------------------------------------
    // Internal helpers
    // -----------------------------------------------------------------------

    /// Narrowing operator: tighten only infinite bounds using the new information.
    ///
    /// Unlike meet, this only replaces bounds that are at +/- infinity with
    /// finite values from `new`, preserving finite bounds from `old`.
    fn narrow(&self, old: &AbstractDomain, new: &AbstractDomain) -> AbstractDomain {
        match (old, new) {
            (
                AbstractDomain::Interval { lo: l1, hi: h1 },
                AbstractDomain::Interval { lo: l2, hi: h2 },
            ) => {
                let lo = if *l1 == i64::MIN { *l2 } else { *l1 };
                let hi = if *h1 == i64::MAX { *h2 } else { *h1 };
                if lo > hi { AbstractDomain::Bottom } else { AbstractDomain::Interval { lo, hi } }
            }
            _ => old.clone(),
        }
    }

    /// Parse the initial state string into an abstract domain.
    ///
    /// Supports patterns like "x = 0", "x = 5", etc.
    fn parse_init_state(&self, init_state: &str) -> AbstractDomain {
        if let Some(val) = parse_const_assign(init_state) {
            return AbstractDomain::Interval { lo: val, hi: val };
        }

        // Try to detect sign from the initial state
        let trimmed = init_state.trim();
        if trimmed.contains("= 0") {
            return AbstractDomain::Interval { lo: 0, hi: 0 };
        }

        AbstractDomain::Top
    }

    /// Build invariant candidates from the final abstract state.
    fn build_candidates(
        &self,
        state: &AbstractDomain,
        loop_body: &str,
        init_state: &str,
    ) -> Vec<InvariantCandidate> {
        let vars = extract_variables(loop_body, init_state);
        let mut candidates = Vec::new();

        match state {
            AbstractDomain::Interval { lo, hi } => {
                let confidence = if *lo != i64::MIN && *hi != i64::MAX {
                    0.9
                } else if *lo != i64::MIN || *hi != i64::MAX {
                    0.7
                } else {
                    0.3
                };
                let expression = match (*lo, *hi) {
                    (l, h) if l != i64::MIN && h != i64::MAX => {
                        let var = vars.first().map(|s| s.as_str()).unwrap_or("x");
                        format!("{l} <= {var} && {var} <= {h}")
                    }
                    (l, _) if l != i64::MIN => {
                        let var = vars.first().map(|s| s.as_str()).unwrap_or("x");
                        format!("{l} <= {var}")
                    }
                    (_, h) if h != i64::MAX => {
                        let var = vars.first().map(|s| s.as_str()).unwrap_or("x");
                        format!("{var} <= {h}")
                    }
                    _ => "true".into(),
                };
                candidates.push(InvariantCandidate {
                    expression,
                    domain: state.clone(),
                    confidence,
                    variables: vars.clone(),
                });
            }
            AbstractDomain::Sign(s) => {
                candidates.push(InvariantCandidate {
                    expression: format!(
                        "sign({})",
                        vars.first().map(|v| v.as_str()).unwrap_or("x")
                    ),
                    domain: state.clone(),
                    confidence: 0.6,
                    variables: vars.clone(),
                });
                // Also emit the sign constraint textually
                let var = vars.first().map(|v| v.as_str()).unwrap_or("x");
                let expr = match s.as_str() {
                    "positive" => format!("{var} > 0"),
                    "negative" => format!("{var} < 0"),
                    "zero" => format!("{var} == 0"),
                    "non_negative" => format!("{var} >= 0"),
                    _ => return candidates,
                };
                candidates.push(InvariantCandidate {
                    expression: expr,
                    domain: state.clone(),
                    confidence: 0.65,
                    variables: vars,
                });
            }
            AbstractDomain::Bottom => {
                candidates.push(InvariantCandidate {
                    expression: "false".into(),
                    domain: AbstractDomain::Bottom,
                    confidence: 1.0,
                    variables: vec![],
                });
            }
            AbstractDomain::Top => {
                candidates.push(InvariantCandidate {
                    expression: "true".into(),
                    domain: AbstractDomain::Top,
                    confidence: 0.1,
                    variables: vars,
                });
            }
            AbstractDomain::Congruence { modulus, remainder } => {
                let var = vars.first().map(|v| v.as_str()).unwrap_or("x");
                candidates.push(InvariantCandidate {
                    expression: format!("{var} % {modulus} == {remainder}"),
                    domain: state.clone(),
                    confidence: 0.75,
                    variables: vars,
                });
            }
            AbstractDomain::Octagon(constraints) => {
                for (a, b, c) in constraints {
                    candidates.push(InvariantCandidate {
                        expression: format!("{a} - {b} <= {c}"),
                        domain: AbstractDomain::Octagon(vec![(a.clone(), b.clone(), *c)]),
                        confidence: 0.8,
                        variables: vec![a.clone(), b.clone()],
                    });
                }
            }
        }

        candidates
    }

    /// Check whether `inner` is subsumed by `outer` (inner subset of outer).
    fn is_subsumed(&self, inner: &AbstractDomain, outer: &AbstractDomain) -> bool {
        match (inner, outer) {
            (AbstractDomain::Bottom, _) => true,
            (_, AbstractDomain::Top) => true,
            (
                AbstractDomain::Interval { lo: l1, hi: h1 },
                AbstractDomain::Interval { lo: l2, hi: h2 },
            ) => l1 >= l2 && h1 <= h2,
            (AbstractDomain::Sign(a), AbstractDomain::Sign(b)) => a == b,
            (
                AbstractDomain::Congruence { modulus: m1, remainder: r1 },
                AbstractDomain::Congruence { modulus: m2, remainder: r2 },
            ) => m1 == m2 && r1 == r2,
            _ => false,
        }
    }
}

// ---------------------------------------------------------------------------
// Parsing helpers
// ---------------------------------------------------------------------------

/// Parse "x = x + N" or "x = x - N", returning Some(delta).
fn parse_increment(stmt: &str) -> Option<i64> {
    let stmt = stmt.trim();
    // Match "VAR = VAR + N" or "VAR = VAR - N"
    let parts: Vec<&str> = stmt.splitn(2, '=').collect();
    if parts.len() != 2 {
        return None;
    }
    let lhs = parts[0].trim();
    let rhs = parts[1].trim();

    // Try "VAR + N"
    if let Some(rest) = rhs.strip_prefix(lhs) {
        let rest = rest.trim();
        if let Some(num_str) = rest.strip_prefix('+') {
            return num_str.trim().parse::<i64>().ok();
        }
        if let Some(num_str) = rest.strip_prefix('-') {
            return num_str.trim().parse::<i64>().ok().map(|n| -n);
        }
    }

    None
}

/// Parse "x = N" where N is a constant integer.
fn parse_const_assign(stmt: &str) -> Option<i64> {
    let stmt = stmt.trim();
    let parts: Vec<&str> = stmt.splitn(2, '=').collect();
    if parts.len() != 2 {
        return None;
    }
    let rhs = parts[1].trim();
    // Only match if RHS is a plain integer (not an expression)
    if rhs.contains('+') || rhs.contains('-') && !rhs.starts_with('-') {
        return None;
    }
    rhs.parse::<i64>().ok()
}

/// Extract variable names from the loop body and init state.
fn extract_variables(loop_body: &str, init_state: &str) -> Vec<String> {
    let mut vars = Vec::new();
    for line in init_state.lines().chain(loop_body.lines()) {
        let line = line.trim();
        if let Some(eq_pos) = line.find('=') {
            let lhs = line[..eq_pos].trim();
            if !lhs.is_empty()
                && lhs.chars().all(|c| c.is_alphanumeric() || c == '_')
                && !vars.contains(&lhs.to_string())
            {
                vars.push(lhs.to_string());
            }
        }
    }
    if vars.is_empty() {
        vars.push("x".into());
    }
    vars
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn default_config() -> AbstractInferenceConfig {
        AbstractInferenceConfig::default()
    }

    fn simple_inferrer() -> InvariantInferrer {
        InvariantInferrer::new(default_config())
    }

    // -- AbstractDomain tests --

    #[test]
    fn test_interval_join() {
        let a = AbstractDomain::Interval { lo: 0, hi: 5 };
        let b = AbstractDomain::Interval { lo: 3, hi: 10 };
        assert_eq!(a.join(&b), AbstractDomain::Interval { lo: 0, hi: 10 });
    }

    #[test]
    fn test_interval_meet() {
        let a = AbstractDomain::Interval { lo: 0, hi: 5 };
        let b = AbstractDomain::Interval { lo: 3, hi: 10 };
        assert_eq!(a.meet(&b), AbstractDomain::Interval { lo: 3, hi: 5 });
    }

    #[test]
    fn test_interval_meet_empty() {
        let a = AbstractDomain::Interval { lo: 0, hi: 2 };
        let b = AbstractDomain::Interval { lo: 5, hi: 10 };
        assert_eq!(a.meet(&b), AbstractDomain::Bottom);
    }

    #[test]
    fn test_bottom_join() {
        let a = AbstractDomain::Bottom;
        let b = AbstractDomain::Interval { lo: 1, hi: 5 };
        assert_eq!(a.join(&b), b);
    }

    #[test]
    fn test_top_meet() {
        let a = AbstractDomain::Top;
        let b = AbstractDomain::Interval { lo: 1, hi: 5 };
        assert_eq!(a.meet(&b), b);
    }

    #[test]
    fn test_sign_join_same() {
        let a = AbstractDomain::Sign("positive".into());
        let b = AbstractDomain::Sign("positive".into());
        assert_eq!(a.join(&b), AbstractDomain::Sign("positive".into()));
    }

    #[test]
    fn test_sign_join_different() {
        let a = AbstractDomain::Sign("positive".into());
        let b = AbstractDomain::Sign("negative".into());
        assert_eq!(a.join(&b), AbstractDomain::Top);
    }

    // -- Transfer function tests --

    #[test]
    fn test_transfer_increment() {
        let inf = simple_inferrer();
        let state = AbstractDomain::Interval { lo: 0, hi: 5 };
        let result = inf.abstract_transfer(&state, "x = x + 1");
        assert_eq!(result, AbstractDomain::Interval { lo: 1, hi: 6 });
    }

    #[test]
    fn test_transfer_decrement() {
        let inf = simple_inferrer();
        let state = AbstractDomain::Interval { lo: 3, hi: 10 };
        let result = inf.abstract_transfer(&state, "x = x - 2");
        assert_eq!(result, AbstractDomain::Interval { lo: 1, hi: 8 });
    }

    #[test]
    fn test_transfer_const_assign() {
        let inf = simple_inferrer();
        let state = AbstractDomain::Top;
        let result = inf.abstract_transfer(&state, "y = 42");
        assert_eq!(result, AbstractDomain::Interval { lo: 42, hi: 42 });
    }

    #[test]
    fn test_transfer_unknown_statement() {
        let inf = simple_inferrer();
        let state = AbstractDomain::Interval { lo: 0, hi: 5 };
        let result = inf.abstract_transfer(&state, "call foo()");
        assert_eq!(result, state);
    }

    #[test]
    fn test_transfer_bottom_propagates() {
        let inf = simple_inferrer();
        let state = AbstractDomain::Bottom;
        let result = inf.abstract_transfer(&state, "x = x + 1");
        assert_eq!(result, AbstractDomain::Bottom);
    }

    // -- Widening tests --

    #[test]
    fn test_widen_grows_upper() {
        let inf = simple_inferrer();
        let old = AbstractDomain::Interval { lo: 0, hi: 5 };
        let new = AbstractDomain::Interval { lo: 0, hi: 6 };
        let widened = inf.widen_invariant(&old, &new);
        assert_eq!(widened, AbstractDomain::Interval { lo: 0, hi: i64::MAX });
    }

    #[test]
    fn test_widen_grows_lower() {
        let inf = simple_inferrer();
        let old = AbstractDomain::Interval { lo: 3, hi: 10 };
        let new = AbstractDomain::Interval { lo: 2, hi: 10 };
        let widened = inf.widen_invariant(&old, &new);
        assert_eq!(widened, AbstractDomain::Interval { lo: i64::MIN, hi: 10 });
    }

    #[test]
    fn test_widen_stable() {
        let inf = simple_inferrer();
        let old = AbstractDomain::Interval { lo: 0, hi: 10 };
        let new = AbstractDomain::Interval { lo: 0, hi: 10 };
        let widened = inf.widen_invariant(&old, &new);
        assert_eq!(widened, old);
    }

    // -- Full inference tests --

    #[test]
    fn test_infer_simple_increment_loop() {
        let inf = simple_inferrer();
        let result = inf.infer_loop_invariant("x = x + 1", "x = 0");
        assert!(result.converged);
        assert!(!result.candidates.is_empty());

        // Should find that x >= 0
        let has_lower_bound = result
            .candidates
            .iter()
            .any(|c| matches!(&c.domain, AbstractDomain::Interval { lo, .. } if *lo == 0));
        assert!(has_lower_bound, "Expected lower bound of 0, candidates: {:?}", result.candidates);
    }

    #[test]
    fn test_infer_empty_body_converges() {
        let inf = simple_inferrer();
        let result = inf.infer_loop_invariant("", "x = 5");
        assert!(result.converged);
        assert!(!result.candidates.is_empty());
        assert_eq!(result.iterations, 1);
    }

    // -- Strengthen candidate tests --

    #[test]
    fn test_strengthen_finite_interval() {
        let inf = simple_inferrer();
        let candidate = InvariantCandidate {
            expression: "0 <= x && x <= 10".into(),
            domain: AbstractDomain::Interval { lo: 0, hi: 10 },
            confidence: 0.8,
            variables: vec!["x".into()],
        };
        let strengthened = inf.strengthen_candidate(&candidate);
        assert!(strengthened.confidence > candidate.confidence);
    }

    #[test]
    fn test_strengthen_bottom() {
        let inf = simple_inferrer();
        let candidate = InvariantCandidate {
            expression: "unreachable".into(),
            domain: AbstractDomain::Bottom,
            confidence: 0.5,
            variables: vec![],
        };
        let strengthened = inf.strengthen_candidate(&candidate);
        assert_eq!(strengthened.confidence, 1.0);
        assert_eq!(strengthened.expression, "false");
    }

    // -- Validate invariant tests --

    #[test]
    fn test_validate_inductive_invariant() {
        let inf = simple_inferrer();
        let candidate = InvariantCandidate {
            expression: "0 <= x".into(),
            domain: AbstractDomain::Interval { lo: 0, hi: i64::MAX },
            confidence: 0.9,
            variables: vec!["x".into()],
        };
        assert!(inf.validate_invariant(&candidate, "x = x + 1"));
    }

    #[test]
    fn test_validate_non_inductive() {
        let inf = simple_inferrer();
        let candidate = InvariantCandidate {
            expression: "0 <= x && x <= 5".into(),
            domain: AbstractDomain::Interval { lo: 0, hi: 5 },
            confidence: 0.9,
            variables: vec!["x".into()],
        };
        // x = x + 1 on [0,5] gives [1,6], not contained in [0,5]
        assert!(!inf.validate_invariant(&candidate, "x = x + 1"));
    }

    // -- Format as spec tests --

    #[test]
    fn test_format_interval_spec() {
        let inf = simple_inferrer();
        let candidate = InvariantCandidate {
            expression: "0 <= x && x <= 100".into(),
            domain: AbstractDomain::Interval { lo: 0, hi: 100 },
            confidence: 0.9,
            variables: vec!["x".into()],
        };
        let spec = inf.format_as_spec(&candidate);
        assert_eq!(spec, "invariant 0 <= x && x <= 100");
    }

    #[test]
    fn test_format_sign_spec() {
        let inf = simple_inferrer();
        let candidate = InvariantCandidate {
            expression: "x > 0".into(),
            domain: AbstractDomain::Sign("positive".into()),
            confidence: 0.7,
            variables: vec!["x".into()],
        };
        let spec = inf.format_as_spec(&candidate);
        assert_eq!(spec, "invariant x > 0");
    }

    #[test]
    fn test_format_congruence_spec() {
        let inf = simple_inferrer();
        let candidate = InvariantCandidate {
            expression: "x % 2 == 0".into(),
            domain: AbstractDomain::Congruence { modulus: 2, remainder: 0 },
            confidence: 0.75,
            variables: vec!["x".into()],
        };
        let spec = inf.format_as_spec(&candidate);
        assert_eq!(spec, "invariant x % 2 == 0");
    }

    // -- Domain property tests --

    #[test]
    fn test_domain_is_bottom() {
        assert!(AbstractDomain::Bottom.is_bottom());
        assert!(!AbstractDomain::Top.is_bottom());
        assert!(!AbstractDomain::Interval { lo: 0, hi: 1 }.is_bottom());
    }

    #[test]
    fn test_domain_is_top() {
        assert!(AbstractDomain::Top.is_top());
        assert!(!AbstractDomain::Bottom.is_top());
    }

    #[test]
    fn test_domain_display() {
        assert_eq!(format!("{}", AbstractDomain::Interval { lo: 0, hi: 10 }), "[0, 10]");
        assert_eq!(format!("{}", AbstractDomain::Top), "top");
        assert_eq!(format!("{}", AbstractDomain::Bottom), "bottom");
        assert_eq!(format!("{}", AbstractDomain::Sign("positive".into())), "sign(positive)");
    }

    // -- Congruence join tests --

    #[test]
    fn test_congruence_join_same() {
        let a = AbstractDomain::Congruence { modulus: 4, remainder: 1 };
        let b = AbstractDomain::Congruence { modulus: 4, remainder: 1 };
        assert_eq!(a.join(&b), AbstractDomain::Congruence { modulus: 4, remainder: 1 });
    }

    #[test]
    fn test_congruence_join_different() {
        let a = AbstractDomain::Congruence { modulus: 4, remainder: 1 };
        let b = AbstractDomain::Congruence { modulus: 4, remainder: 3 };
        assert_eq!(a.join(&b), AbstractDomain::Top);
    }

    // -- Parsing helper tests --

    #[test]
    fn test_parse_increment_add() {
        assert_eq!(parse_increment("x = x + 3"), Some(3));
    }

    #[test]
    fn test_parse_increment_sub() {
        assert_eq!(parse_increment("x = x - 2"), Some(-2));
    }

    #[test]
    fn test_parse_increment_not_matching() {
        assert_eq!(parse_increment("y = 42"), None);
    }

    #[test]
    fn test_parse_const_assign_positive() {
        assert_eq!(parse_const_assign("x = 0"), Some(0));
        assert_eq!(parse_const_assign("y = 42"), Some(42));
    }

    #[test]
    fn test_extract_variables_single() {
        let vars = extract_variables("x = x + 1", "x = 0");
        assert_eq!(vars, vec!["x".to_string()]);
    }

    #[test]
    fn test_extract_variables_multiple() {
        let vars = extract_variables("x = x + 1\ny = y - 1", "x = 0");
        assert!(vars.contains(&"x".to_string()));
        assert!(vars.contains(&"y".to_string()));
    }
}

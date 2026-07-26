// trust-temporal/ctl.rs: Computation Tree Logic model checking
//
// Implements the CTL labeling algorithm for finite state machines.
// For each CTL operator, computes the set of states satisfying the formula
// using fixpoint iteration over the state space.
//
// References:
//   Clarke, Grumberg, Peled. "Model Checking" (MIT Press, 2000). Ch. 4.
//   Baier, Katoen. "Principles of Model Checking" (MIT Press, 2008). Ch. 6.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;
use std::fmt;
use trust_types::fx::{FxHashMap, FxHashSet};

use crate::{StateId, StateMachine, Trace};

// ---------------------------------------------------------------------------
// CTL Formula AST
// ---------------------------------------------------------------------------

/// A Computation Tree Logic formula.
///
/// CTL formulas combine propositional logic with path quantifiers (E/A) and
/// temporal operators (X/F/G/U). Every temporal operator must be immediately
/// preceded by a path quantifier.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum CtlFormula {
    /// Constant true.
    True,
    /// Constant false.
    False,
    /// Atomic proposition: a named boolean predicate evaluated per state.
    Atom(String),
    /// Negation.
    Not(Box<CtlFormula>),
    /// Conjunction.
    And(Box<CtlFormula>, Box<CtlFormula>),
    /// Disjunction.
    Or(Box<CtlFormula>, Box<CtlFormula>),
    /// EX phi: there Exists a path where phi holds in the neXt state.
    EX(Box<CtlFormula>),
    /// EF phi: there Exists a path where phi holds at some Future state.
    EF(Box<CtlFormula>),
    /// EG phi: there Exists a path where phi holds Globally.
    EG(Box<CtlFormula>),
    /// E[phi U psi]: there Exists a path where phi holds Until psi.
    EU(Box<CtlFormula>, Box<CtlFormula>),
    /// AX phi: on All paths, phi holds in the neXt state.
    AX(Box<CtlFormula>),
    /// AF phi: on All paths, phi holds at some Future state.
    AF(Box<CtlFormula>),
    /// AG phi: on All paths, phi holds Globally.
    AG(Box<CtlFormula>),
    /// A[phi U psi]: on All paths, phi holds Until psi.
    AU(Box<CtlFormula>, Box<CtlFormula>),
}

impl fmt::Display for CtlFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CtlFormula::True => write!(f, "true"),
            CtlFormula::False => write!(f, "false"),
            CtlFormula::Atom(name) => write!(f, "{name}"),
            CtlFormula::Not(inner) => write!(f, "!({inner})"),
            CtlFormula::And(l, r) => write!(f, "({l} && {r})"),
            CtlFormula::Or(l, r) => write!(f, "({l} || {r})"),
            CtlFormula::EX(inner) => write!(f, "EX({inner})"),
            CtlFormula::EF(inner) => write!(f, "EF({inner})"),
            CtlFormula::EG(inner) => write!(f, "EG({inner})"),
            CtlFormula::EU(l, r) => write!(f, "E[{l} U {r}]"),
            CtlFormula::AX(inner) => write!(f, "AX({inner})"),
            CtlFormula::AF(inner) => write!(f, "AF({inner})"),
            CtlFormula::AG(inner) => write!(f, "AG({inner})"),
            CtlFormula::AU(l, r) => write!(f, "A[{l} U {r}]"),
        }
    }
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors from CTL formula parsing.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CtlParseError {
    /// Unexpected end of input.
    UnexpectedEof,
    /// Unexpected token at the given position.
    UnexpectedToken { pos: usize, found: String },
    /// Unmatched parenthesis.
    UnmatchedParen { pos: usize },
    /// Empty formula.
    EmptyFormula,
    /// Missing temporal operator after path quantifier.
    MissingTemporalOp { pos: usize, quantifier: String },
}

impl fmt::Display for CtlParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CtlParseError::UnexpectedEof => write!(f, "unexpected end of input"),
            CtlParseError::UnexpectedToken { pos, found } => {
                write!(f, "unexpected token '{found}' at position {pos}")
            }
            CtlParseError::UnmatchedParen { pos } => {
                write!(f, "unmatched parenthesis at position {pos}")
            }
            CtlParseError::EmptyFormula => write!(f, "empty formula"),
            CtlParseError::MissingTemporalOp { pos, quantifier } => {
                write!(
                    f,
                    "path quantifier '{quantifier}' at position {pos} must be followed by X, F, G, or U-bracket"
                )
            }
        }
    }
}

impl std::error::Error for CtlParseError {}

// ---------------------------------------------------------------------------
// Model checker result
// ---------------------------------------------------------------------------

/// Result of CTL model checking.
#[derive(Debug, Clone)]
pub struct CtlResult {
    /// States satisfying the formula.
    pub satisfying_states: FxHashSet<StateId>,
    /// Optional witness or counterexample path.
    pub witness: Option<Trace>,
}

impl CtlResult {
    /// Whether the initial state satisfies the formula.
    #[must_use]
    pub fn holds_at_initial(&self, initial: StateId) -> bool {
        self.satisfying_states.contains(&initial)
    }
}

// ---------------------------------------------------------------------------
// CTL Model Checker (labeling algorithm)
// ---------------------------------------------------------------------------

/// CTL model checker using the labeling (fixpoint) algorithm.
///
/// Given a `StateMachine` and a `CtlFormula`, computes the exact set of states
/// satisfying the formula. Atomic propositions are matched against state labels.
pub struct CtlModelChecker<'a> {
    machine: &'a StateMachine,
    /// All state IDs for iteration.
    all_states: Vec<StateId>,
    /// Predecessor map: state -> set of states that can reach it in one step.
    predecessors: FxHashMap<StateId, Vec<StateId>>,
}

impl<'a> CtlModelChecker<'a> {
    /// Create a model checker for the given state machine.
    #[must_use]
    pub fn new(machine: &'a StateMachine) -> Self {
        let all_states: Vec<StateId> = machine.states.iter().map(|s| s.id).collect();

        // Build predecessor map
        let mut predecessors: FxHashMap<StateId, Vec<StateId>> = FxHashMap::default();
        for state in &all_states {
            predecessors.entry(*state).or_default();
        }
        for transition in &machine.transitions {
            predecessors.entry(transition.to).or_default().push(transition.from);
        }

        Self { machine, all_states, predecessors }
    }

    /// Check which states satisfy the given CTL formula.
    #[must_use]
    pub fn check(&self, formula: &CtlFormula) -> CtlResult {
        let satisfying_states = self.eval(formula);
        let witness = self.extract_witness(formula, &satisfying_states);
        CtlResult { satisfying_states, witness }
    }

    /// Core recursive evaluation: returns the set of states satisfying `formula`.
    fn eval(&self, formula: &CtlFormula) -> FxHashSet<StateId> {
        match formula {
            CtlFormula::True => self.all_states.iter().copied().collect(),
            CtlFormula::False => FxHashSet::default(),
            CtlFormula::Atom(name) => self.eval_atom(name),
            CtlFormula::Not(inner) => {
                let inner_set = self.eval(inner);
                self.all_states.iter().copied().filter(|s| !inner_set.contains(s)).collect()
            }
            CtlFormula::And(l, r) => {
                let left = self.eval(l);
                let right = self.eval(r);
                left.intersection(&right).copied().collect()
            }
            CtlFormula::Or(l, r) => {
                let left = self.eval(l);
                let right = self.eval(r);
                left.union(&right).copied().collect()
            }
            CtlFormula::EX(inner) => self.check_ex(inner),
            CtlFormula::EF(inner) => self.check_ef(inner),
            CtlFormula::EG(inner) => self.check_eg(inner),
            CtlFormula::EU(phi, psi) => self.check_eu(phi, psi),
            // A-quantified operators via duality with E-quantified:
            //   AX phi = !EX(!phi)
            //   AF phi = !EG(!phi)
            //   AG phi = !EF(!phi)
            //   A[phi U psi] = !E[!psi U (!phi && !psi)] && !EG(!psi)
            CtlFormula::AX(inner) => self.check_ax(inner),
            CtlFormula::AF(inner) => self.check_af(inner),
            CtlFormula::AG(inner) => self.check_ag(inner),
            CtlFormula::AU(phi, psi) => self.check_au(phi, psi),
        }
    }

    /// Evaluate an atomic proposition: returns states whose labels contain `name`.
    fn eval_atom(&self, name: &str) -> FxHashSet<StateId> {
        self.machine
            .states
            .iter()
            .filter(|s| s.labels.iter().any(|l| l == name))
            .map(|s| s.id)
            .collect()
    }

    /// EX(phi): states that have at least one successor satisfying phi.
    fn check_ex(&self, inner: &CtlFormula) -> FxHashSet<StateId> {
        let phi_states = self.eval(inner);
        let mut result = FxHashSet::default();

        for &state in &self.all_states {
            let has_phi_successor =
                self.machine.successors(state).iter().any(|s| phi_states.contains(s));
            if has_phi_successor {
                result.insert(state);
            }
        }

        result
    }

    /// EF(phi): states from which there exists a path reaching a phi-state.
    ///
    /// Computed as least fixpoint: EF(phi) = phi OR EX(EF(phi)).
    /// Implementation: backward BFS from phi-states.
    fn check_ef(&self, inner: &CtlFormula) -> FxHashSet<StateId> {
        let phi_states = self.eval(inner);
        let mut result = phi_states.clone();
        let mut queue: VecDeque<StateId> = phi_states.into_iter().collect();

        while let Some(state) = queue.pop_front() {
            if let Some(preds) = self.predecessors.get(&state) {
                for &pred in preds {
                    if result.insert(pred) {
                        queue.push_back(pred);
                    }
                }
            }
        }

        result
    }

    /// EG(phi): states from which there exists an infinite path along which phi
    /// always holds.
    ///
    /// Computed as greatest fixpoint: EG(phi) = phi AND EX(EG(phi)).
    /// Implementation: start with phi-states, iteratively remove states that
    /// have no successor within the current set.
    fn check_eg(&self, inner: &CtlFormula) -> FxHashSet<StateId> {
        let phi_states = self.eval(inner);
        let mut current = phi_states;

        loop {
            let next: FxHashSet<StateId> = current
                .iter()
                .copied()
                .filter(|&state| self.machine.successors(state).iter().any(|s| current.contains(s)))
                .collect();

            if next == current {
                break;
            }
            current = next;
        }

        current
    }

    /// E[phi U psi]: states from which there exists a path where phi holds
    /// until psi becomes true.
    ///
    /// Computed as least fixpoint: E[phi U psi] = psi OR (phi AND EX(E[phi U psi])).
    /// Implementation: backward BFS from psi-states through phi-states.
    fn check_eu(&self, phi: &CtlFormula, psi: &CtlFormula) -> FxHashSet<StateId> {
        let phi_states = self.eval(phi);
        let psi_states = self.eval(psi);

        let mut result = psi_states.clone();
        let mut queue: VecDeque<StateId> = psi_states.into_iter().collect();

        while let Some(state) = queue.pop_front() {
            if let Some(preds) = self.predecessors.get(&state) {
                for &pred in preds {
                    if phi_states.contains(&pred) && result.insert(pred) {
                        queue.push_back(pred);
                    }
                }
            }
        }

        result
    }

    /// AX(phi): states where ALL successors satisfy phi.
    /// AX(phi) = !EX(!phi). Also: states with no successors vacuously satisfy AX.
    fn check_ax(&self, inner: &CtlFormula) -> FxHashSet<StateId> {
        let phi_states = self.eval(inner);
        let mut result = FxHashSet::default();

        for &state in &self.all_states {
            let successors = self.machine.successors(state);
            if successors.iter().all(|s| phi_states.contains(s)) {
                result.insert(state);
            }
        }

        result
    }

    /// AF(phi): on all paths, phi eventually holds.
    /// AF(phi) = !EG(!phi).
    /// Computed as least fixpoint: AF(phi) = phi OR AX(AF(phi)).
    /// Implementation: backward from phi-states, adding a predecessor only when
    /// ALL of its successors are already in the result set.
    fn check_af(&self, inner: &CtlFormula) -> FxHashSet<StateId> {
        let phi_states = self.eval(inner);
        let mut result = phi_states.clone();
        let mut queue: VecDeque<StateId> = phi_states.into_iter().collect();

        // Count how many successors of each state are NOT yet in result
        let mut remaining: FxHashMap<StateId, usize> = FxHashMap::default();
        for &state in &self.all_states {
            remaining.insert(state, self.machine.successors(state).len());
        }

        while let Some(state) = queue.pop_front() {
            if let Some(preds) = self.predecessors.get(&state) {
                for &pred in preds {
                    if result.contains(&pred) {
                        continue;
                    }
                    if let Some(count) = remaining.get_mut(&pred) {
                        *count = count.saturating_sub(1);
                        if *count == 0 {
                            result.insert(pred);
                            queue.push_back(pred);
                        }
                    }
                }
            }
        }

        result
    }

    /// AG(phi): on all paths, phi holds globally.
    /// AG(phi) = !EF(!phi).
    fn check_ag(&self, inner: &CtlFormula) -> FxHashSet<StateId> {
        let not_inner = CtlFormula::Not(Box::new(inner.clone()));
        let ef_not = self.check_ef(&not_inner);
        self.all_states.iter().copied().filter(|s| !ef_not.contains(s)).collect()
    }

    /// A[phi U psi]: on all paths, phi holds until psi.
    /// Computed directly as least fixpoint:
    /// A[phi U psi] = psi OR (phi AND AX(A[phi U psi]))
    ///
    /// Implementation: backward from psi-states, adding a predecessor only when
    /// it satisfies phi AND all its successors are already in the result set.
    fn check_au(&self, phi: &CtlFormula, psi: &CtlFormula) -> FxHashSet<StateId> {
        let phi_states = self.eval(phi);
        let psi_states = self.eval(psi);

        let mut result = psi_states.clone();
        let mut queue: VecDeque<StateId> = psi_states.into_iter().collect();

        let mut remaining: FxHashMap<StateId, usize> = FxHashMap::default();
        for &state in &self.all_states {
            remaining.insert(state, self.machine.successors(state).len());
        }

        while let Some(state) = queue.pop_front() {
            if let Some(preds) = self.predecessors.get(&state) {
                for &pred in preds {
                    if result.contains(&pred) {
                        continue;
                    }
                    if let Some(count) = remaining.get_mut(&pred) {
                        *count = count.saturating_sub(1);
                        if *count == 0 && phi_states.contains(&pred) {
                            result.insert(pred);
                            queue.push_back(pred);
                        }
                    }
                }
            }
        }

        result
    }

    /// Extract a witness or counterexample path from the initial state.
    ///
    /// For existential formulas (EF, EG, EU): a witness path demonstrating
    /// the property. For universal formulas (AG, AF): a counterexample if the
    /// initial state does NOT satisfy the formula.
    fn extract_witness(
        &self,
        formula: &CtlFormula,
        satisfying: &FxHashSet<StateId>,
    ) -> Option<Trace> {
        let initial = self.machine.initial;
        match formula {
            // For EF: find a path from initial to a satisfying state
            CtlFormula::EF(inner) => {
                if satisfying.contains(&initial) {
                    let target_states = self.eval(inner);
                    self.find_path_to_set(initial, &target_states)
                } else {
                    None
                }
            }
            // For AG: if initial doesn't satisfy, find counterexample
            CtlFormula::AG(inner) => {
                if !satisfying.contains(&initial) {
                    let not_inner_states = {
                        let inner_states = self.eval(inner);
                        self.all_states
                            .iter()
                            .copied()
                            .filter(|s| !inner_states.contains(s))
                            .collect::<FxHashSet<_>>()
                    };
                    self.find_path_to_set(initial, &not_inner_states)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// BFS to find a path from `start` to any state in `targets`.
    fn find_path_to_set(&self, start: StateId, targets: &FxHashSet<StateId>) -> Option<Trace> {
        if targets.contains(&start) {
            return Some(Trace::new(vec![start]));
        }

        let mut visited = FxHashSet::default();
        let mut parent: FxHashMap<StateId, StateId> = FxHashMap::default();
        let mut queue = VecDeque::new();

        visited.insert(start);
        queue.push_back(start);

        while let Some(current) = queue.pop_front() {
            for succ in self.machine.successors(current) {
                if visited.insert(succ) {
                    parent.insert(succ, current);
                    if targets.contains(&succ) {
                        // Reconstruct path
                        let mut path = vec![succ];
                        let mut node = succ;
                        while let Some(&prev) = parent.get(&node) {
                            path.push(prev);
                            node = prev;
                        }
                        path.reverse();
                        return Some(Trace::new(path));
                    }
                    queue.push_back(succ);
                }
            }
        }

        None
    }
}

// ---------------------------------------------------------------------------
// CTL Parser
// ---------------------------------------------------------------------------

/// Token types for the CTL lexer.
#[derive(Debug, Clone, PartialEq, Eq)]
enum CtlToken {
    Ident(String),
    True,
    False,
    Not,
    And,
    Or,
    LParen,
    RParen,
    LBracket,
    RBracket,
    /// Path quantifier E (existential).
    Exists,
    /// Path quantifier A (universal).
    ForAll,
    /// Temporal operator X (next).
    Next,
    /// Temporal operator F (future/eventually).
    Future,
    /// Temporal operator G (globally/always).
    Globally,
    /// Temporal operator U (until) -- used inside E[..U..] and A[..U..]
    Until,
}

/// Tokenize a CTL formula string.
fn ctl_tokenize(input: &str) -> Result<Vec<(CtlToken, usize)>, CtlParseError> {
    let mut tokens = Vec::new();
    let chars: Vec<char> = input.chars().collect();
    let mut i = 0;

    while i < chars.len() {
        match chars[i] {
            ' ' | '\t' | '\n' | '\r' => i += 1,
            '(' => {
                tokens.push((CtlToken::LParen, i));
                i += 1;
            }
            ')' => {
                tokens.push((CtlToken::RParen, i));
                i += 1;
            }
            '[' => {
                tokens.push((CtlToken::LBracket, i));
                i += 1;
            }
            ']' => {
                tokens.push((CtlToken::RBracket, i));
                i += 1;
            }
            '!' => {
                tokens.push((CtlToken::Not, i));
                i += 1;
            }
            '&' if i + 1 < chars.len() && chars[i + 1] == '&' => {
                tokens.push((CtlToken::And, i));
                i += 2;
            }
            '|' if i + 1 < chars.len() && chars[i + 1] == '|' => {
                tokens.push((CtlToken::Or, i));
                i += 2;
            }
            c if c.is_ascii_alphabetic() || c == '_' => {
                let start = i;
                while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                    i += 1;
                }
                let word: String = chars[start..i].iter().collect();
                let tok = match word.as_str() {
                    "true" => CtlToken::True,
                    "false" => CtlToken::False,
                    "EX" => {
                        tokens.push((CtlToken::Exists, start));
                        CtlToken::Next
                    }
                    "EF" => {
                        tokens.push((CtlToken::Exists, start));
                        CtlToken::Future
                    }
                    "EG" => {
                        tokens.push((CtlToken::Exists, start));
                        CtlToken::Globally
                    }
                    "AX" => {
                        tokens.push((CtlToken::ForAll, start));
                        CtlToken::Next
                    }
                    "AF" => {
                        tokens.push((CtlToken::ForAll, start));
                        CtlToken::Future
                    }
                    "AG" => {
                        tokens.push((CtlToken::ForAll, start));
                        CtlToken::Globally
                    }
                    "E" => CtlToken::Exists,
                    "A" => CtlToken::ForAll,
                    "X" => CtlToken::Next,
                    "F" => CtlToken::Future,
                    "G" => CtlToken::Globally,
                    "U" => CtlToken::Until,
                    _ => CtlToken::Ident(word),
                };
                tokens.push((tok, start));
            }
            _ => {
                return Err(CtlParseError::UnexpectedToken { pos: i, found: chars[i].to_string() });
            }
        }
    }

    Ok(tokens)
}

/// Recursive descent parser for CTL formulas.
///
/// Grammar (informal):
/// ```text
/// formula     = disjunction
/// disjunction = conjunction ("||" conjunction)*
/// conjunction = unary ("&&" unary)*
/// unary       = "!" unary
///             | "EX" unary | "EF" unary | "EG" unary
///             | "AX" unary | "AF" unary | "AG" unary
///             | "E" "[" formula "U" formula "]"
///             | "A" "[" formula "U" formula "]"
///             | primary
/// primary     = "true" | "false" | IDENT | "(" formula ")"
/// ```
struct CtlParser {
    tokens: Vec<(CtlToken, usize)>,
    pos: usize,
}

impl CtlParser {
    fn new(tokens: Vec<(CtlToken, usize)>) -> Self {
        Self { tokens, pos: 0 }
    }

    fn peek(&self) -> Option<&CtlToken> {
        self.tokens.get(self.pos).map(|(t, _)| t)
    }

    fn peek_pos(&self) -> usize {
        self.tokens.get(self.pos).map_or(0, |(_, p)| *p)
    }

    fn advance(&mut self) -> Option<(CtlToken, usize)> {
        if self.pos < self.tokens.len() {
            let tok = self.tokens[self.pos].clone();
            self.pos += 1;
            Some(tok)
        } else {
            None
        }
    }

    fn parse_formula(&mut self) -> Result<CtlFormula, CtlParseError> {
        self.parse_disjunction()
    }

    fn parse_disjunction(&mut self) -> Result<CtlFormula, CtlParseError> {
        let mut left = self.parse_conjunction()?;
        while self.peek() == Some(&CtlToken::Or) {
            self.advance();
            let right = self.parse_conjunction()?;
            left = CtlFormula::Or(Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_conjunction(&mut self) -> Result<CtlFormula, CtlParseError> {
        let mut left = self.parse_unary()?;
        while self.peek() == Some(&CtlToken::And) {
            self.advance();
            let right = self.parse_unary()?;
            left = CtlFormula::And(Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_unary(&mut self) -> Result<CtlFormula, CtlParseError> {
        match self.peek().cloned() {
            Some(CtlToken::Not) => {
                self.advance();
                let inner = self.parse_unary()?;
                Ok(CtlFormula::Not(Box::new(inner)))
            }
            Some(CtlToken::Exists) => {
                let pos = self.peek_pos();
                self.advance();
                self.parse_existential(pos)
            }
            Some(CtlToken::ForAll) => {
                let pos = self.peek_pos();
                self.advance();
                self.parse_universal(pos)
            }
            _ => self.parse_primary(),
        }
    }

    /// Parse after seeing 'E': expect X, F, G, or '[' for until.
    fn parse_existential(&mut self, quantifier_pos: usize) -> Result<CtlFormula, CtlParseError> {
        match self.peek().cloned() {
            Some(CtlToken::Next) => {
                self.advance();
                let inner = self.parse_unary()?;
                Ok(CtlFormula::EX(Box::new(inner)))
            }
            Some(CtlToken::Future) => {
                self.advance();
                let inner = self.parse_unary()?;
                Ok(CtlFormula::EF(Box::new(inner)))
            }
            Some(CtlToken::Globally) => {
                self.advance();
                let inner = self.parse_unary()?;
                Ok(CtlFormula::EG(Box::new(inner)))
            }
            Some(CtlToken::LBracket) => {
                self.advance();
                let phi = self.parse_formula()?;
                if self.peek() != Some(&CtlToken::Until) {
                    return Err(CtlParseError::UnexpectedToken {
                        pos: self.peek_pos(),
                        found: format!("{:?}", self.peek()),
                    });
                }
                self.advance();
                let psi = self.parse_formula()?;
                if self.peek() != Some(&CtlToken::RBracket) {
                    return Err(CtlParseError::UnmatchedParen { pos: self.peek_pos() });
                }
                self.advance();
                Ok(CtlFormula::EU(Box::new(phi), Box::new(psi)))
            }
            _ => Err(CtlParseError::MissingTemporalOp {
                pos: quantifier_pos,
                quantifier: "E".to_string(),
            }),
        }
    }

    /// Parse after seeing 'A': expect X, F, G, or '[' for until.
    fn parse_universal(&mut self, quantifier_pos: usize) -> Result<CtlFormula, CtlParseError> {
        match self.peek().cloned() {
            Some(CtlToken::Next) => {
                self.advance();
                let inner = self.parse_unary()?;
                Ok(CtlFormula::AX(Box::new(inner)))
            }
            Some(CtlToken::Future) => {
                self.advance();
                let inner = self.parse_unary()?;
                Ok(CtlFormula::AF(Box::new(inner)))
            }
            Some(CtlToken::Globally) => {
                self.advance();
                let inner = self.parse_unary()?;
                Ok(CtlFormula::AG(Box::new(inner)))
            }
            Some(CtlToken::LBracket) => {
                self.advance();
                let phi = self.parse_formula()?;
                if self.peek() != Some(&CtlToken::Until) {
                    return Err(CtlParseError::UnexpectedToken {
                        pos: self.peek_pos(),
                        found: format!("{:?}", self.peek()),
                    });
                }
                self.advance();
                let psi = self.parse_formula()?;
                if self.peek() != Some(&CtlToken::RBracket) {
                    return Err(CtlParseError::UnmatchedParen { pos: self.peek_pos() });
                }
                self.advance();
                Ok(CtlFormula::AU(Box::new(phi), Box::new(psi)))
            }
            _ => Err(CtlParseError::MissingTemporalOp {
                pos: quantifier_pos,
                quantifier: "A".to_string(),
            }),
        }
    }

    fn parse_primary(&mut self) -> Result<CtlFormula, CtlParseError> {
        match self.peek().cloned() {
            Some(CtlToken::True) => {
                self.advance();
                Ok(CtlFormula::True)
            }
            Some(CtlToken::False) => {
                self.advance();
                Ok(CtlFormula::False)
            }
            Some(CtlToken::Ident(name)) => {
                self.advance();
                Ok(CtlFormula::Atom(name))
            }
            Some(CtlToken::LParen) => {
                let paren_pos = self.peek_pos();
                self.advance();
                let inner = self.parse_formula()?;
                if self.peek() != Some(&CtlToken::RParen) {
                    return Err(CtlParseError::UnmatchedParen { pos: paren_pos });
                }
                self.advance();
                Ok(inner)
            }
            Some(_) => {
                let pos = self.peek_pos();
                let (tok, _) = self.advance().expect("invariant: peeked Some");
                Err(CtlParseError::UnexpectedToken { pos, found: format!("{tok:?}") })
            }
            None => Err(CtlParseError::UnexpectedEof),
        }
    }
}

/// Parse a CTL formula string into a `CtlFormula` AST.
///
/// Supported syntax:
/// - Constants: `true`, `false`
/// - Atoms: identifiers like `p`, `ready`, `safe`
/// - Boolean: `!` (not), `&&` (and), `||` (or)
/// - Existential temporal: `EX`, `EF`, `EG`, `E[phi U psi]`
/// - Universal temporal: `AX`, `AF`, `AG`, `A[phi U psi]`
/// - Parentheses for grouping
///
/// # Errors
///
/// Returns `CtlParseError` on malformed input.
pub fn parse_ctl(input: &str) -> Result<CtlFormula, CtlParseError> {
    let input = input.trim();
    if input.is_empty() {
        return Err(CtlParseError::EmptyFormula);
    }
    let tokens = ctl_tokenize(input)?;
    if tokens.is_empty() {
        return Err(CtlParseError::EmptyFormula);
    }
    let mut parser = CtlParser::new(tokens);
    let formula = parser.parse_formula()?;
    if parser.pos < parser.tokens.len() {
        let pos = parser.peek_pos();
        return Err(CtlParseError::UnexpectedToken {
            pos,
            found: format!("{:?}", parser.tokens[parser.pos].0),
        });
    }
    Ok(formula)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{State, StateMachineBuilder, Transition};

    // ---- Helper: microwave oven model ----
    // States: Idle(start), Heating(active), Done(terminal,done)
    // Transitions: Idle->Heating, Heating->Heating, Heating->Done
    fn microwave_model() -> StateMachine {
        StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Idle").with_label("start"))
            .add_state(State::new(StateId(1), "Heating").with_label("active"))
            .add_state(State::new(StateId(2), "Done").with_label("terminal").with_label("done"))
            .add_transition(Transition::new(StateId(0), StateId(1), "start"))
            .add_transition(Transition::new(StateId(1), StateId(1), "heat"))
            .add_transition(Transition::new(StateId(1), StateId(2), "finish"))
            .build()
    }

    // ---- Helper: branching model ----
    // States: S0(init), S1(a), S2(b), S3(a,b)
    // S0->S1, S0->S2, S1->S3, S2->S3, S3->S3
    fn branching_model() -> StateMachine {
        StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "S0").with_label("init"))
            .add_state(State::new(StateId(1), "S1").with_label("a"))
            .add_state(State::new(StateId(2), "S2").with_label("b"))
            .add_state(State::new(StateId(3), "S3").with_label("a").with_label("b"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go_a"))
            .add_transition(Transition::new(StateId(0), StateId(2), "go_b"))
            .add_transition(Transition::new(StateId(1), StateId(3), "merge"))
            .add_transition(Transition::new(StateId(2), StateId(3), "merge"))
            .add_transition(Transition::new(StateId(3), StateId(3), "loop"))
            .build()
    }

    // ---- Parser tests ----

    #[test]
    fn test_parse_ctl_atom() {
        let f = parse_ctl("ready").expect("should parse atom");
        assert_eq!(f, CtlFormula::Atom("ready".into()));
    }

    #[test]
    fn test_parse_ctl_true_false() {
        assert_eq!(parse_ctl("true").unwrap(), CtlFormula::True);
        assert_eq!(parse_ctl("false").unwrap(), CtlFormula::False);
    }

    #[test]
    fn test_parse_ctl_ex() {
        let f = parse_ctl("EX active").unwrap();
        assert_eq!(f, CtlFormula::EX(Box::new(CtlFormula::Atom("active".into()))));
    }

    #[test]
    fn test_parse_ctl_ef() {
        let f = parse_ctl("EF done").unwrap();
        assert_eq!(f, CtlFormula::EF(Box::new(CtlFormula::Atom("done".into()))));
    }

    #[test]
    fn test_parse_ctl_eg() {
        let f = parse_ctl("EG safe").unwrap();
        assert_eq!(f, CtlFormula::EG(Box::new(CtlFormula::Atom("safe".into()))));
    }

    #[test]
    fn test_parse_ctl_eu() {
        let f = parse_ctl("E[active U done]").unwrap();
        assert_eq!(
            f,
            CtlFormula::EU(
                Box::new(CtlFormula::Atom("active".into())),
                Box::new(CtlFormula::Atom("done".into())),
            )
        );
    }

    #[test]
    fn test_parse_ctl_ax() {
        let f = parse_ctl("AX safe").unwrap();
        assert_eq!(f, CtlFormula::AX(Box::new(CtlFormula::Atom("safe".into()))));
    }

    #[test]
    fn test_parse_ctl_af() {
        let f = parse_ctl("AF done").unwrap();
        assert_eq!(f, CtlFormula::AF(Box::new(CtlFormula::Atom("done".into()))));
    }

    #[test]
    fn test_parse_ctl_ag() {
        let f = parse_ctl("AG safe").unwrap();
        assert_eq!(f, CtlFormula::AG(Box::new(CtlFormula::Atom("safe".into()))));
    }

    #[test]
    fn test_parse_ctl_au() {
        let f = parse_ctl("A[active U done]").unwrap();
        assert_eq!(
            f,
            CtlFormula::AU(
                Box::new(CtlFormula::Atom("active".into())),
                Box::new(CtlFormula::Atom("done".into())),
            )
        );
    }

    #[test]
    fn test_parse_ctl_not() {
        let f = parse_ctl("!error").unwrap();
        assert_eq!(f, CtlFormula::Not(Box::new(CtlFormula::Atom("error".into()))));
    }

    #[test]
    fn test_parse_ctl_and_or() {
        let f = parse_ctl("p && q || r").unwrap();
        // && binds tighter than ||
        assert_eq!(
            f,
            CtlFormula::Or(
                Box::new(CtlFormula::And(
                    Box::new(CtlFormula::Atom("p".into())),
                    Box::new(CtlFormula::Atom("q".into())),
                )),
                Box::new(CtlFormula::Atom("r".into())),
            )
        );
    }

    #[test]
    fn test_parse_ctl_nested() {
        let f = parse_ctl("AG (EF done)").unwrap();
        assert_eq!(
            f,
            CtlFormula::AG(Box::new(CtlFormula::EF(Box::new(CtlFormula::Atom("done".into())))))
        );
    }

    #[test]
    fn test_parse_ctl_empty_error() {
        assert_eq!(parse_ctl("").unwrap_err(), CtlParseError::EmptyFormula);
    }

    #[test]
    fn test_parse_ctl_unmatched_paren() {
        let err = parse_ctl("(p && q").unwrap_err();
        assert!(matches!(err, CtlParseError::UnmatchedParen { .. }));
    }

    #[test]
    fn test_parse_ctl_display() {
        let f = CtlFormula::AG(Box::new(CtlFormula::EF(Box::new(CtlFormula::Atom("done".into())))));
        let s = f.to_string();
        assert!(s.contains("AG"));
        assert!(s.contains("EF"));
        assert!(s.contains("done"));
    }

    // ---- Model checker tests ----

    #[test]
    fn test_check_atom_matches_labels() {
        let model = microwave_model();
        let checker = CtlModelChecker::new(&model);
        let result = checker.check(&CtlFormula::Atom("active".into()));
        assert!(result.satisfying_states.contains(&StateId(1)));
        assert!(!result.satisfying_states.contains(&StateId(0)));
    }

    #[test]
    fn test_check_true_all_states() {
        let model = microwave_model();
        let checker = CtlModelChecker::new(&model);
        let result = checker.check(&CtlFormula::True);
        assert_eq!(result.satisfying_states.len(), 3);
    }

    #[test]
    fn test_check_false_no_states() {
        let model = microwave_model();
        let checker = CtlModelChecker::new(&model);
        let result = checker.check(&CtlFormula::False);
        assert!(result.satisfying_states.is_empty());
    }

    #[test]
    fn test_check_not() {
        let model = microwave_model();
        let checker = CtlModelChecker::new(&model);
        let result = checker.check(&CtlFormula::Not(Box::new(CtlFormula::Atom("active".into()))));
        assert!(result.satisfying_states.contains(&StateId(0)));
        assert!(result.satisfying_states.contains(&StateId(2)));
        assert!(!result.satisfying_states.contains(&StateId(1)));
    }

    #[test]
    fn test_check_ex_microwave() {
        let model = microwave_model();
        let checker = CtlModelChecker::new(&model);
        // EX(active): states with a successor labeled "active"
        let result = checker.check(&CtlFormula::EX(Box::new(CtlFormula::Atom("active".into()))));
        // Idle->Heating(active), Heating->Heating(active)
        assert!(result.satisfying_states.contains(&StateId(0)));
        assert!(result.satisfying_states.contains(&StateId(1)));
        // Done has no successors
        assert!(!result.satisfying_states.contains(&StateId(2)));
    }

    #[test]
    fn test_check_ef_reachability() {
        let model = microwave_model();
        let checker = CtlModelChecker::new(&model);
        // EF(done): can we reach a "done" state?
        let result = checker.check(&CtlFormula::EF(Box::new(CtlFormula::Atom("done".into()))));
        // All states can reach Done
        assert!(result.satisfying_states.contains(&StateId(0)));
        assert!(result.satisfying_states.contains(&StateId(1)));
        assert!(result.satisfying_states.contains(&StateId(2)));
    }

    #[test]
    fn test_check_eg_always_on_some_path() {
        let model = microwave_model();
        let checker = CtlModelChecker::new(&model);
        // EG(active): is there a path where "active" holds forever?
        // Heating has a self-loop, so yes from Heating.
        let result = checker.check(&CtlFormula::EG(Box::new(CtlFormula::Atom("active".into()))));
        assert!(result.satisfying_states.contains(&StateId(1)));
        // Idle is NOT active, so EG(active) is false from Idle
        assert!(!result.satisfying_states.contains(&StateId(0)));
    }

    #[test]
    fn test_check_eu_until() {
        let model = microwave_model();
        let checker = CtlModelChecker::new(&model);
        // E[active U done]: active holds until done on some path
        let result = checker.check(&CtlFormula::EU(
            Box::new(CtlFormula::Atom("active".into())),
            Box::new(CtlFormula::Atom("done".into())),
        ));
        // Heating satisfies: active now, and can reach Done
        assert!(result.satisfying_states.contains(&StateId(1)));
        // Done satisfies vacuously (psi holds immediately)
        assert!(result.satisfying_states.contains(&StateId(2)));
        // Idle: not active, so EU doesn't hold from Idle
        assert!(!result.satisfying_states.contains(&StateId(0)));
    }

    #[test]
    fn test_check_ax_all_successors() {
        let model = branching_model();
        let checker = CtlModelChecker::new(&model);
        // AX(a || b): all successors have label 'a' or 'b'
        let formula = CtlFormula::AX(Box::new(CtlFormula::Or(
            Box::new(CtlFormula::Atom("a".into())),
            Box::new(CtlFormula::Atom("b".into())),
        )));
        let result = checker.check(&formula);
        // S0's successors are S1(a) and S2(b) -- both have a or b
        assert!(result.satisfying_states.contains(&StateId(0)));
        // S3's successor is S3(a,b)
        assert!(result.satisfying_states.contains(&StateId(3)));
    }

    #[test]
    fn test_check_af_inevitable() {
        let model = microwave_model();
        let checker = CtlModelChecker::new(&model);
        // AF(done): on all paths, "done" is eventually reached
        let result = checker.check(&CtlFormula::AF(Box::new(CtlFormula::Atom("done".into()))));
        // Done: trivially yes
        assert!(result.satisfying_states.contains(&StateId(2)));
        // Heating: has a self-loop path that never reaches Done, so AF(done) is false
        assert!(!result.satisfying_states.contains(&StateId(1)));
        // Idle: path goes through Heating which can loop forever, so AF(done) is false
        assert!(!result.satisfying_states.contains(&StateId(0)));
    }

    #[test]
    fn test_check_ag_globally() {
        let model = branching_model();
        let checker = CtlModelChecker::new(&model);
        // AG(a || b || init): all reachable states have a, b, or init
        let formula = CtlFormula::AG(Box::new(CtlFormula::Or(
            Box::new(CtlFormula::Or(
                Box::new(CtlFormula::Atom("a".into())),
                Box::new(CtlFormula::Atom("b".into())),
            )),
            Box::new(CtlFormula::Atom("init".into())),
        )));
        let result = checker.check(&formula);
        // All states have at least one of these labels
        assert!(result.holds_at_initial(StateId(0)));
    }

    #[test]
    fn test_check_au_all_paths_until() {
        let model = branching_model();
        let checker = CtlModelChecker::new(&model);
        // A[init || a || b  U  a && b]: on all paths, (init|a|b) holds until (a&b)
        let phi = CtlFormula::Or(
            Box::new(CtlFormula::Or(
                Box::new(CtlFormula::Atom("init".into())),
                Box::new(CtlFormula::Atom("a".into())),
            )),
            Box::new(CtlFormula::Atom("b".into())),
        );
        let psi = CtlFormula::And(
            Box::new(CtlFormula::Atom("a".into())),
            Box::new(CtlFormula::Atom("b".into())),
        );
        let result = checker.check(&CtlFormula::AU(Box::new(phi), Box::new(psi)));
        // S3 satisfies psi directly
        assert!(result.satisfying_states.contains(&StateId(3)));
        // S1(a) and S2(b) satisfy phi and all paths lead to S3
        assert!(result.satisfying_states.contains(&StateId(1)));
        assert!(result.satisfying_states.contains(&StateId(2)));
        // S0(init) satisfies phi and all paths go through S1/S2 to S3
        assert!(result.satisfying_states.contains(&StateId(0)));
    }

    #[test]
    fn test_check_nested_formula() {
        let model = microwave_model();
        let checker = CtlModelChecker::new(&model);
        // AG(active -> EF(done)): globally, if active then done is reachable
        let inner = CtlFormula::Or(
            Box::new(CtlFormula::Not(Box::new(CtlFormula::Atom("active".into())))),
            Box::new(CtlFormula::EF(Box::new(CtlFormula::Atom("done".into())))),
        );
        let formula = CtlFormula::AG(Box::new(inner));
        let result = checker.check(&formula);
        // This should hold everywhere since Heating can always reach Done
        assert!(result.holds_at_initial(StateId(0)));
    }

    #[test]
    fn test_check_ef_witness_extraction() {
        let model = microwave_model();
        let checker = CtlModelChecker::new(&model);
        let result = checker.check(&CtlFormula::EF(Box::new(CtlFormula::Atom("done".into()))));
        // Should have a witness path from initial to a "done" state
        let witness = result.witness.expect("should have witness for EF");
        assert!(witness.starts_at(StateId(0)));
        assert!(witness.visits(StateId(2))); // Done state
    }

    #[test]
    fn test_check_ag_counterexample() {
        let model = microwave_model();
        let checker = CtlModelChecker::new(&model);
        // AG(start): should fail since Heating is not "start"
        let result = checker.check(&CtlFormula::AG(Box::new(CtlFormula::Atom("start".into()))));
        assert!(!result.holds_at_initial(StateId(0)));
        let cex = result.witness.expect("should have counterexample for failed AG");
        assert!(cex.starts_at(StateId(0)));
    }

    #[test]
    fn test_fixpoint_convergence_eg() {
        // Ensure EG converges on a model with multiple cycles
        let model = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "S0").with_label("p"))
            .add_state(State::new(StateId(1), "S1").with_label("p"))
            .add_state(State::new(StateId(2), "S2").with_label("p"))
            .add_state(State::new(StateId(3), "S3"))
            .add_transition(Transition::new(StateId(0), StateId(1), "a"))
            .add_transition(Transition::new(StateId(1), StateId(2), "b"))
            .add_transition(Transition::new(StateId(2), StateId(0), "c"))
            .add_transition(Transition::new(StateId(1), StateId(3), "escape"))
            .build();

        let checker = CtlModelChecker::new(&model);
        let result = checker.check(&CtlFormula::EG(Box::new(CtlFormula::Atom("p".into()))));
        // S0->S1->S2->S0 is a cycle where all have "p"
        assert!(result.satisfying_states.contains(&StateId(0)));
        assert!(result.satisfying_states.contains(&StateId(1)));
        assert!(result.satisfying_states.contains(&StateId(2)));
        // S3 doesn't have "p"
        assert!(!result.satisfying_states.contains(&StateId(3)));
    }

    #[test]
    fn test_fixpoint_convergence_ef() {
        // Chain: S0->S1->S2->S3(target). All should satisfy EF(target).
        let model = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "S0"))
            .add_state(State::new(StateId(1), "S1"))
            .add_state(State::new(StateId(2), "S2"))
            .add_state(State::new(StateId(3), "S3").with_label("target"))
            .add_transition(Transition::new(StateId(0), StateId(1), "a"))
            .add_transition(Transition::new(StateId(1), StateId(2), "b"))
            .add_transition(Transition::new(StateId(2), StateId(3), "c"))
            .build();

        let checker = CtlModelChecker::new(&model);
        let result = checker.check(&CtlFormula::EF(Box::new(CtlFormula::Atom("target".into()))));
        for i in 0..4 {
            assert!(result.satisfying_states.contains(&StateId(i)));
        }
    }

    #[test]
    fn test_empty_model() {
        let model =
            StateMachineBuilder::new(StateId(0)).add_state(State::new(StateId(0), "lone")).build();
        let checker = CtlModelChecker::new(&model);

        // AX(false) should hold vacuously (no successors)
        let result = checker.check(&CtlFormula::AX(Box::new(CtlFormula::False)));
        assert!(result.satisfying_states.contains(&StateId(0)));
    }
}

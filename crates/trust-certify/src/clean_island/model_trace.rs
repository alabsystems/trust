// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The fast, UNTRUSTED reading of a finite model beside [`super::model_check`]:
//! it searches, and the kernel confirms.
//!
//! - [`presearch`] explores the model before the kernel is asked anything. A
//!   reachable state that breaks an invariant is reported only after the
//!   KERNEL replays the run to it and evaluates the invariant false there
//!   (`replayRun`, `rowVerdict` in the served checker), so an unsafe model is
//!   caught at any size the search covers, not only within the kernel's
//!   budget; a model with more states than the budget is not handed to the
//!   kernel's search at all.
//! - [`shortest_run`] answers "how does it get there" for a state the kernel's
//!   own search named.
//! - [`first_truncation`] finds a subtraction that stops at zero.
//!
//! It reads the model's data off the
//! kernel environment (weak-head normal forms of the `ScalarModel` value, so
//! helper definitions an author wrote are seen through), interprets the
//! checker's grammar over it, and breadth-first searches from the initial
//! state for the kernel's state. UNTRUSTED, and held to the kernel twice: a run
//! is reported only when it ends at exactly the state the kernel named, and
//! only after the KERNEL REPLAYS it — `replayRun M <action positions>` in the
//! served checker module takes each step with the checker's own guard and
//! successor, and every row must equal this module's. So each printed step is
//! one the checker takes; that the run is a shortest one rests on the search
//! here. Anything the interpreter cannot read (a construct outside the
//! grammar, an overflow, two updates of one variable) yields no run rather
//! than a guess.
//!
//! Semantics mirror `Trust/FiniteModel.lean`: `Nat` state, truncated `sub`,
//! comparisons over `Nat`, connectives over `Bool`, `ite` at either sort, an
//! action enabled when its guard is true, updates simultaneous over the
//! pre-state, an update of an undeclared name ignored.

use std::collections::{HashMap, VecDeque};

use clean_kernel::tc::TypeChecker;
use clean_kernel::{Expr, Level, Name};

use super::model_check::{NAMESPACE, head_and_args, list, nat, string};

/// One step of a run: the action taken (`(initial)` for the first) and the
/// state after it, `(variable, value)` in the model's declaration order.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CleanIslandModelStep {
    pub action: String,
    pub state: Vec<(String, u64)>,
}

/// A subtraction that stops at zero on a reachable state: `left - right` with
/// `left < right`, evaluated in `place` at `state`. The model language is over
/// the naturals, so this is 0 where an integer reading gives a negative
/// number — and a guard `a <= b - 1` is then TRUE at `a = b = 0`, where the
/// `a < b` it was written for is false.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CleanIslandModelTruncation {
    pub place: String,
    pub left: u64,
    pub right: u64,
    pub state: Vec<(String, u64)>,
}

/// More states than this and a search gives up.
pub(super) const MAX_STATES: usize = 1 << 18;

/// What a kernel check of a model's whole state space costs: the expression
/// nodes it evaluates (`work`, the measure the kernel's limits are set in) and
/// the successor rows it builds, hashes and looks up (`steps`), each
/// `variables` long, among `states` rows.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(super) struct Effort {
    pub(super) work: u64,
    pub(super) steps: u64,
    pub(super) variables: u64,
    pub(super) states: u64,
}

impl Effort {
    /// Estimated kernel seconds for a safety proof (release, one machine): a
    /// least-squares fit over the 32 proofs of a real program's models that
    /// took 3.5 s to 175 s, the kernel checking the search's rows; the median
    /// estimate is 1.02 times the time, and 80% fall within 0.71 to 1.34. Work
    /// alone missed by up to 15x on a model whose every action is always
    /// enabled (8,194 states, 229,432 successors).
    pub(super) fn seconds(&self) -> f64 {
        let (work, steps, variables, states) =
            (self.work as f64, self.steps as f64, self.variables as f64, self.states.max(2) as f64);
        1.23e-5 * work + 3.94e-6 * steps * variables * states.log2()
    }
}

/// What [`presearch`] found.
pub(super) enum Presearch {
    /// A reachable state breaks invariant `invariant`; the kernel replayed
    /// `run` to it and evaluates that invariant false in its last state.
    Violation { invariant: String, run: Vec<CleanIslandModelStep> },
    /// Every reachable state was visited and none breaks an invariant. `work`
    /// is the size of that search in expression nodes evaluated — what the
    /// kernel repeats to prove the model, so its cost estimate.
    /// `rows`: every reachable row, in the order the checker lays its index
    /// out in one pass (ascending `rowHash`, then the row).
    Exhausted { states: usize, effort: Effort, rows: Vec<Vec<u64>> },
    /// The model could not be read, has more than [`MAX_STATES`] states, or
    /// the kernel did not confirm what the search found.
    Unread,
}

/// Explore `model` breadth first for a state that breaks an invariant.
#[allow(dead_code)]
pub(super) fn presearch(tc: &TypeChecker<'_>, model: &Expr) -> Presearch {
    let Some(machine) = Machine::decode(tc, model) else { return Presearch::Unread };
    presearch_machine(tc, model, &machine)
}

/// Explore `model` breadth first for an invariant violation and for its first
/// saturating subtraction within `limit` states, decoding `model` once.
pub(super) fn presearch_and_first_truncation(
    tc: &TypeChecker<'_>,
    model: &Expr,
    limit: usize,
) -> (Presearch, Option<CleanIslandModelTruncation>) {
    let Some(machine) = Machine::decode(tc, model) else {
        return (Presearch::Unread, None);
    };
    (presearch_machine(tc, model, &machine), first_truncation_machine(&machine, limit))
}

fn presearch_machine(tc: &TypeChecker<'_>, model: &Expr, machine: &Machine) -> Presearch {
    let broken = |state: &[u64]| -> Option<Option<usize>> {
        for (index, (_, invariant)) in machine.invariants.iter().enumerate() {
            if !invariant.truth(state)? {
                return Some(Some(index));
            }
        }
        Some(None)
    };
    let Some((reached, stopped)) = machine.search(|state| Some(broken(state)?.is_some())) else {
        return Presearch::Unread;
    };
    let Some(target) = stopped else {
        let states = reached.len();
        let effort = machine.effort(reached.keys().map(Vec::as_slice));
        let mut keyed: Vec<(u64, Vec<u64>)> =
            reached.into_keys().map(|row| (row_hash(&row), row)).collect();
        keyed.sort_unstable();
        let rows = keyed.into_iter().map(|(_, row)| row).collect();
        return Presearch::Exhausted { states, effort, rows };
    };
    let confirmed = || {
        let index = broken(&target)??;
        let (run, positions) = machine.run_to(&reached, &target)?;
        (kernel_replays(tc, model, &positions, &run)
            && kernel_row_breaks(tc, model, &target, index))
        .then(|| Presearch::Violation { invariant: machine.invariants[index].0.clone(), run })
    };
    confirmed().unwrap_or(Presearch::Unread)
}

/// An expression nested deeper than this is not read (decoding, evaluation and
/// drop all recurse on it).
const MAX_DEPTH: usize = 256;

pub(super) enum Term {
    Int(u64),
    Var(usize),
    Add(Box<Term>, Box<Term>),
    Sub(Box<Term>, Box<Term>),
    Gt(Box<Term>, Box<Term>),
    Le(Box<Term>, Box<Term>),
    Eq(Box<Term>, Box<Term>),
    Neq(Box<Term>, Box<Term>),
    Or(Box<Term>, Box<Term>),
    And(Box<Term>, Box<Term>),
    Iff(Box<Term>, Box<Term>),
    Ite(Box<Term>, Box<Term>, Box<Term>),
    Bool(bool),
}

pub(super) struct Action {
    pub(super) name: String,
    /// `None`: `Guard.always`.
    guard: Option<Term>,
    /// One slot per declared variable; `None` leaves it unchanged.
    updates: Vec<Option<Term>>,
}

pub(super) struct Machine {
    /// The name the model gives itself (`ScalarModel.mk "Name" ...`).
    pub(super) name: String,
    constants: Vec<(String, u64)>,
    pub(super) variables: Vec<String>,
    pub(super) initial: Vec<u64>,
    pub(super) actions: Vec<Action>,
    invariants: Vec<(String, Term)>,
}

/// A shortest run of `model` from its initial state to `target`, which must
/// break invariant number `invariant` — or `None` when this module cannot
/// read the model or does not reproduce the kernel's answer.
pub(super) fn shortest_run(
    tc: &TypeChecker<'_>,
    model: &Expr,
    target: &[u64],
    invariant: usize,
) -> Option<Vec<CleanIslandModelStep>> {
    let machine = Machine::decode(tc, model)?;
    if target.len() != machine.variables.len()
        || machine.invariants.get(invariant)?.1.truth(target) != Some(false)
    {
        return None;
    }
    let (reached, stopped) = machine.search(|state| Some(state == target))?;
    stopped?;
    let (run, positions) = machine.run_to(&reached, target)?;
    kernel_replays(tc, model, &positions, &run).then_some(run)
}

/// The kernel term of the list `items` of type `List element` (level 0).
pub(super) fn list_of(element: Expr, items: Vec<Expr>) -> Expr {
    let constant = |name: &str| Expr::const_(Name::from_string(name), vec![Level::zero()]);
    let nil = Expr::app(constant("List.nil"), element.clone());
    let cons_element = Expr::app(constant("List.cons"), element);
    items
        .into_iter()
        .rev()
        .fold(nil, |rest, item| Expr::app(Expr::app(cons_element.clone(), item), rest))
}

/// The checker's `rowHash`, exactly: a polynomial over the row from its last
/// entry, then a cube, both modulo the prime 4294967291.
pub(super) fn row_hash(row: &[u64]) -> u64 {
    const P: u128 = 4_294_967_291;
    let h = row
        .iter()
        .rev()
        .fold(7u128, |acc, &v| (acc * 1_000_003 + u128::from(v) * 2_654_435_761 + 1) % P);
    let cube = (h * ((h * h) % P)) % P;
    u64::try_from(cube).expect("below the modulus")
}

pub(super) fn nat_list(values: impl DoubleEndedIterator<Item = u64>) -> Expr {
    let list_constant = |name: &str| Expr::const_(Name::from_string(name), vec![Level::zero()]);
    let nat_ty = Expr::const_str("Nat");
    let nil = Expr::app(list_constant("List.nil"), nat_ty.clone());
    let cons_nat = Expr::app(list_constant("List.cons"), nat_ty);
    values.rev().fold(nil, |rest, value| {
        Expr::app(Expr::app(cons_nat.clone(), Expr::nat_lit(value)), rest)
    })
}

/// Whether the kernel's `rowVerdict model row` is `invariantFails _ invariant`.
fn kernel_row_breaks(tc: &TypeChecker<'_>, model: &Expr, row: &[u64], invariant: usize) -> bool {
    let verdict = tc.whnf(&Expr::app(
        Expr::app(Expr::const_str(&format!("{NAMESPACE}.rowVerdict")), model.clone()),
        nat_list(row.iter().copied()),
    ));
    let (head, args) = head_and_args(&verdict);
    let ("Option.some", [_, verdict]) = (head.as_str(), &args[..]) else { return false };
    let (head, args) = head_and_args(&tc.whnf(verdict));
    let [_, index] = &args[..] else { return false };
    head == format!("{NAMESPACE}.CheckVerdict.invariantFails")
        && nat(tc, index) == u64::try_from(invariant).ok()
}

/// Whether the kernel's `replayRun model positions` is exactly `run`'s rows.
pub(super) fn kernel_replays(
    tc: &TypeChecker<'_>,
    model: &Expr,
    positions: &[usize],
    run: &[CleanIslandModelStep],
) -> bool {
    let steps = nat_list(positions.iter().map(|position| *position as u64));
    let replay = tc.whnf(&Expr::app(
        Expr::app(Expr::const_str(&format!("{NAMESPACE}.replayRun")), model.clone()),
        steps,
    ));
    let (head, args) = head_and_args(&replay);
    let ("Option.some", [_, rows]) = (head.as_str(), &args[..]) else { return false };
    let Some(rows) = list(tc, rows) else { return false };
    rows.len() == run.len()
        && rows.iter().zip(run).all(|(row, step)| {
            list(tc, row).is_some_and(|cells| {
                cells.len() == step.state.len()
                    && cells
                        .iter()
                        .zip(&step.state)
                        .all(|(cell, (_, value))| nat(tc, cell) == Some(*value))
            })
        })
}

/// Every reached state with the state and action it was first reached from
/// (`None` for the initial state).
type Reached = HashMap<Vec<u64>, Option<(Vec<u64>, usize)>>;

/// A [`Machine`] as ty's transition system: a state is a row, an action its
/// position, and a fingerprint 128 bits of hash of the row (a collision could
/// only drop a state from this untrusted search, whose rows the kernel checks).
pub(super) struct MachineSystem<'m>(pub(super) &'m Machine);

/// The action (by position) whose guard or update cannot be evaluated on a
/// reachable state.
#[derive(Debug)]
pub(super) struct Unevaluable(pub(super) usize);

impl std::fmt::Display for Unevaluable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "the step of action {} cannot be evaluated on a reachable state", self.0)
    }
}

impl std::error::Error for Unevaluable {}

impl tla_mc_core::TransitionSystem for MachineSystem<'_> {
    type State = Vec<u64>;
    type Action = usize;
    type Fingerprint = u128;
    type Error = Unevaluable;

    fn initial_states(&self) -> Result<Vec<Vec<u64>>, Unevaluable> {
        Ok(vec![self.0.initial.clone()])
    }

    fn successors(&self, state: &Vec<u64>) -> Result<Vec<(usize, Vec<u64>)>, Unevaluable> {
        let mut out = Vec::with_capacity(self.0.actions.len());
        for (index, action) in self.0.actions.iter().enumerate() {
            let enabled = match &action.guard {
                None => true,
                Some(guard) => guard.truth(state).ok_or(Unevaluable(index))?,
            };
            if !enabled {
                continue;
            }
            let mut next = state.clone();
            for (slot, update) in action.updates.iter().enumerate() {
                if let Some(value) = update {
                    next[slot] = value.number(state).ok_or(Unevaluable(index))?;
                }
            }
            out.push((index, next));
        }
        Ok(out)
    }

    fn fingerprint(&self, state: &Vec<u64>) -> u128 {
        use std::hash::{Hash, Hasher};
        let half = |seed: u8| {
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            seed.hash(&mut hasher);
            state.hash(&mut hasher);
            hasher.finish()
        };
        (u128::from(half(0)) << 64) | u128::from(half(1))
    }
}

/// What the search keeps: every state with the state and action it was
/// first reached by (ty reports a transition before it admits the target),
/// and where `stop` stopped it.
struct Recorder<F> {
    reached: Reached,
    pending: Option<(Vec<u64>, usize)>,
    stop: F,
    stopped: Option<Vec<u64>>,
    failed: bool,
}

impl<F: FnMut(&[u64]) -> Option<bool> + Send> tla_mc_core::ExplorationObserver<MachineSystem<'_>>
    for Recorder<F>
{
    fn on_new_state(&mut self, state: &Vec<u64>) -> bool {
        self.reached.insert(state.clone(), self.pending.take());
        match (self.stop)(state) {
            Some(false) => true,
            Some(true) => {
                self.stopped = Some(state.clone());
                false
            }
            None => {
                self.failed = true;
                false
            }
        }
    }

    fn on_transition(&mut self, action: &usize, from: &Vec<u64>, to: &Vec<u64>) -> bool {
        if to != from && !self.reached.contains_key(to) {
            self.pending = Some((from.clone(), *action));
        }
        true
    }

    fn on_deadlock(&mut self, _state: &Vec<u64>) {}

    fn is_done(&self) -> bool {
        self.stopped.is_some() || self.failed
    }
}

impl Machine {
    /// Breadth first from the initial state, asking `stop` about each state as
    /// it is first reached (the initial one included) and stopping at the
    /// first it accepts. Returns every state reached, each with the state and
    /// action it was first reached by, and the one stopped at (`None`: the
    /// reachable states were exhausted). The search is ty's
    /// (`tla_mc_core::explore_bfs`) over [`MachineSystem`]: the queue and the
    /// actions' declaration order, so the result is a function of the model
    /// alone, and first discovery is at minimal depth. `None` when a guard, an
    /// update or `stop` cannot be evaluated, or past [`MAX_STATES`].
    fn search(
        &self,
        stop: impl FnMut(&[u64]) -> Option<bool> + Send,
    ) -> Option<(Reached, Option<Vec<u64>>)> {
        let system = MachineSystem(self);
        let mut recorder =
            Recorder { reached: HashMap::new(), pending: None, stop, stopped: None, failed: false };
        let options =
            tla_mc_core::BfsOptions { max_states: Some(MAX_STATES), ..Default::default() };
        let outcome =
            tla_mc_core::explore_bfs_with_options(&system, &mut recorder, &options).ok()?;
        if recorder.failed || outcome.state_limit_reached {
            return None;
        }
        Some((recorder.reached, recorder.stopped))
    }

    /// The run from the initial state to `target` through `reached`, and the
    /// positions of the actions it takes.
    fn run_to(
        &self,
        reached: &Reached,
        target: &[u64],
    ) -> Option<(Vec<CleanIslandModelStep>, Vec<usize>)> {
        let mut run = Vec::new();
        let mut positions = Vec::new();
        let mut at = target.to_vec();
        loop {
            let from = reached.get(&at)?.clone();
            let action = from.as_ref().map_or_else(
                || "(initial)".to_owned(),
                |(_, index)| self.actions[*index].name.clone(),
            );
            run.push(CleanIslandModelStep {
                action,
                state: self.variables.iter().cloned().zip(at.iter().copied()).collect(),
            });
            match from {
                Some((previous, index)) => {
                    positions.push(index);
                    at = previous;
                }
                None => break,
            }
        }
        run.reverse();
        positions.reverse();
        Some((run, positions))
    }
}

/// The first truncating subtraction among the first `limit` reachable states
/// of `model`, breadth first: in an invariant, in any action's guard, or in an
/// update of an enabled action (only the taken branch of an `ite` counts).
/// `None` when there is none there, or the model cannot be read.
#[allow(dead_code)]
pub(super) fn first_truncation(
    tc: &TypeChecker<'_>,
    model: &Expr,
    limit: usize,
) -> Option<CleanIslandModelTruncation> {
    let machine = Machine::decode(tc, model)?;
    first_truncation_machine(&machine, limit)
}

fn first_truncation_machine(
    machine: &Machine,
    limit: usize,
) -> Option<CleanIslandModelTruncation> {
    if !machine.has_sub() {
        return None;
    }
    let found =
        |place: String, (left, right): (u64, u64), state: &[u64]| CleanIslandModelTruncation {
            place,
            left,
            right,
            state: machine.variables.iter().cloned().zip(state.iter().copied()).collect(),
        };
    let mut reached: std::collections::HashSet<Vec<u64>> = std::collections::HashSet::new();
    let mut frontier = VecDeque::new();
    reached.insert(machine.initial.clone());
    frontier.push_back(machine.initial.clone());
    while let Some(state) = frontier.pop_front() {
        for (name, invariant) in &machine.invariants {
            if let Some(operands) = invariant.truncates(&state) {
                return Some(found(format!("invariant `{name}`"), operands, &state));
            }
        }
        for action in &machine.actions {
            if let Some(operands) = action.guard.as_ref().and_then(|guard| guard.truncates(&state))
            {
                return Some(found(format!("the guard of `{}`", action.name), operands, &state));
            }
            let enabled = match &action.guard {
                None => true,
                Some(guard) => guard.truth(&state)?,
            };
            if !enabled {
                continue;
            }
            let mut next = state.clone();
            for (slot, update) in action.updates.iter().enumerate() {
                let Some(value) = update else { continue };
                if let Some(operands) = value.truncates(&state) {
                    let place =
                        format!("the update of `{}` in `{}`", machine.variables[slot], action.name);
                    return Some(found(place, operands, &state));
                }
                next[slot] = value.number(&state)?;
            }
            if reached.len() < limit && !reached.contains(&next) {
                reached.insert(next.clone());
                frontier.push_back(next);
            }
        }
    }
    None
}

/// How many states this module's reading of `model` reaches — for the tests
/// that hold it to the kernel checker's own count.
#[cfg(test)]
pub(super) fn reachable_states(tc: &TypeChecker<'_>, model: &Expr) -> Option<usize> {
    Some(Machine::decode(tc, model)?.search(|_| Some(false))?.0.len())
}

impl Machine {
    /// The expression nodes the check evaluates at `state`: every invariant,
    /// every guard, and the updates of each enabled action.
    #[cfg(test)]
    pub(super) fn work_at(&self, state: &[u64]) -> u64 {
        let invariants: u64 = self.invariants.iter().map(|(_, term)| term.size()).sum();
        let actions: u64 = self
            .actions
            .iter()
            .map(|action| {
                let guard = action.guard.as_ref().map_or(0, Term::size);
                let enabled = action.guard.as_ref().is_none_or(|g| g.truth(state) == Some(true));
                let updates: u64 =
                    if enabled { action.updates.iter().flatten().map(Term::size).sum() } else { 0 };
                guard + updates
            })
            .sum();
        invariants + actions
    }

    /// What a kernel check over `states` (every reachable state) costs.
    pub(super) fn effort<'s>(&self, states: impl Iterator<Item = &'s [u64]>) -> Effort {
        let to = |n: usize| u64::try_from(n).unwrap_or(u64::MAX);
        let invariant_work: u64 = self.invariants.iter().map(|(_, term)| term.size()).sum();
        let guard_work: u64 =
            self.actions.iter().map(|action| action.guard.as_ref().map_or(0, Term::size)).sum();
        let base_state_work = invariant_work + guard_work;
        let action_update_sizes: Vec<u64> = self
            .actions
            .iter()
            .map(|action| action.updates.iter().flatten().map(Term::size).sum())
            .collect();
        let mut work = 0u64;
        let mut steps = 0u64;
        let mut state_count = 0usize;
        for state in states {
            state_count += 1;
            work += base_state_work;
            for (action, &update_work) in self.actions.iter().zip(&action_update_sizes) {
                if action.guard.as_ref().is_none_or(|g| g.truth(state) == Some(true)) {
                    work += update_work;
                    steps += 1;
                }
            }
        }
        Effort { work, steps, variables: to(self.variables.len()), states: to(state_count) }
    }

    /// An expression of this model (a claim's goal), read in its scope.
    pub(super) fn term(&self, tc: &TypeChecker<'_>, expression: &Expr) -> Option<Term> {
        Scope { tc, constants: &self.constants, variables: &self.variables }.term(expression)
    }

    /// `state` with its variables' names.
    pub(super) fn named(&self, state: &[u64]) -> Vec<(String, u64)> {
        self.variables.iter().cloned().zip(state.iter().copied()).collect()
    }

    /// Whether any invariant, action guard, or action update contains a subtraction (`Term::Sub`).
    pub(super) fn has_sub(&self) -> bool {
        self.invariants.iter().any(|(_, term)| term.has_sub())
            || self.actions.iter().any(|action| {
                action.guard.as_ref().is_some_and(Term::has_sub)
                    || action.updates.iter().flatten().any(Term::has_sub)
            })
    }

    pub(super) fn decode(tc: &TypeChecker<'_>, model: &Expr) -> Option<Self> {
        let fields = constructor(tc, model, "ScalarModel.mk", 5)?;
        let mut constants: Vec<(String, u64)> = Vec::new();
        for entry in list(tc, &fields[1])? {
            let entry = constructor(tc, &entry, "Constant.mk", 2)?;
            constants.push((string(tc, &entry[0])?, nat(tc, &entry[1])?));
        }
        let mut variables = Vec::new();
        let mut initial = Vec::new();
        for entry in list(tc, &fields[2])? {
            let entry = constructor(tc, &entry, "StateVar.mk", 2)?;
            let name = string(tc, &entry[0])?;
            if variables.contains(&name) {
                return None;
            }
            variables.push(name);
            initial.push(nat(tc, &entry[1])?);
        }
        let scope = Scope { tc, constants: &constants, variables: &variables };
        let mut actions = Vec::new();
        for entry in list(tc, &fields[3])? {
            let entry = constructor(tc, &entry, "Action.mk", 3)?;
            let (guard_head, guard_args) = head_and_args(&tc.whnf(&entry[1]));
            let guard =
                match (guard_head.strip_prefix(&format!("{NAMESPACE}.Guard."))?, &guard_args[..]) {
                    ("always", []) => None,
                    ("when", [condition]) => Some(scope.term(condition)?),
                    _ => return None,
                };
            let mut updates: Vec<Option<Term>> = variables.iter().map(|_| None).collect();
            for update in list(tc, &entry[2])? {
                let update = constructor(tc, &update, "Update.mk", 2)?;
                let name = string(tc, &update[0])?;
                // An update of an undeclared name is ignored, as `ActionHolds` does.
                let Some(slot) = variables.iter().position(|variable| *variable == name) else {
                    continue;
                };
                if updates[slot].is_some() {
                    return None;
                }
                updates[slot] = Some(scope.term(&update[1])?);
            }
            actions.push(Action { name: string(tc, &entry[0])?, guard, updates });
        }
        let mut invariants = Vec::new();
        for entry in list(tc, &fields[4])? {
            let entry = constructor(tc, &entry, "Invariant.mk", 2)?;
            invariants.push((string(tc, &entry[0])?, scope.term(&entry[1])?));
        }
        Some(Self {
            name: string(tc, &fields[0])?,
            constants,
            variables,
            initial,
            actions,
            invariants,
        })
    }
}

/// The arguments of `expression` when it reduces to an application of the
/// constructor `name` (in the model namespace) with `arity` arguments.
pub(super) fn constructor(
    tc: &TypeChecker<'_>,
    expression: &Expr,
    name: &str,
    arity: usize,
) -> Option<Vec<Expr>> {
    let (head, args) = head_and_args(&tc.whnf(expression));
    (head == format!("{NAMESPACE}.{name}") && args.len() == arity).then_some(args)
}

struct Scope<'a, 'env> {
    tc: &'a TypeChecker<'env>,
    constants: &'a [(String, u64)],
    variables: &'a [String],
}

impl Scope<'_, '_> {
    fn term(&self, expression: &Expr) -> Option<Term> {
        self.term_within(expression, MAX_DEPTH)
    }

    fn term_within(&self, expression: &Expr, depth: usize) -> Option<Term> {
        let depth = depth.checked_sub(1)?;
        let reduced = self.tc.whnf(expression);
        let (head, args) = head_and_args(&reduced);
        let two = |build: fn(Box<Term>, Box<Term>) -> Term| -> Option<Term> {
            let [left, right] = &args[..] else { return None };
            Some(build(
                Box::new(self.term_within(left, depth)?),
                Box::new(self.term_within(right, depth)?),
            ))
        };
        match head.strip_prefix(&format!("{NAMESPACE}.ScalarExpr."))? {
            "int" => Some(Term::Int(nat(self.tc, args.first()?)?)),
            "var" => {
                let name = string(self.tc, args.first()?)?;
                Some(Term::Var(self.variables.iter().position(|variable| *variable == name)?))
            }
            "constRef" => {
                // The first constant of that name, as the checker reads it;
                // same-named constants that disagree are outside the grammar
                // only when one is referenced.
                let name = string(self.tc, args.first()?)?;
                let mut named = self.constants.iter().filter(|(known, _)| *known == name);
                let value = named.next()?.1;
                named.all(|(_, other)| *other == value).then_some(Term::Int(value))
            }
            "add" => two(Term::Add),
            "sub" => two(Term::Sub),
            "gt" => two(Term::Gt),
            "le" => two(Term::Le),
            "eq" => two(Term::Eq),
            "neq" => two(Term::Neq),
            "or" => two(Term::Or),
            "and" => two(Term::And),
            "iff" => two(Term::Iff),
            "ite" => {
                let [condition, then, otherwise] = &args[..] else { return None };
                Some(Term::Ite(
                    Box::new(self.term_within(condition, depth)?),
                    Box::new(self.term_within(then, depth)?),
                    Box::new(self.term_within(otherwise, depth)?),
                ))
            }
            "bool" => {
                let (literal, _) = head_and_args(&self.tc.whnf(args.first()?));
                match literal.as_str() {
                    "Bool.true" => Some(Term::Bool(true)),
                    "Bool.false" => Some(Term::Bool(false)),
                    _ => None,
                }
            }
            // forallIn, fnAccess, except, comprehension: function-valued state.
            _ => None,
        }
    }
}

impl Term {
    /// Whether any node in the term is a subtraction (`Term::Sub`).
    fn has_sub(&self) -> bool {
        match self {
            Self::Int(_) | Self::Var(_) | Self::Bool(_) => false,
            Self::Sub(_, _) => true,
            Self::Add(a, b)
            | Self::Gt(a, b)
            | Self::Le(a, b)
            | Self::Eq(a, b)
            | Self::Neq(a, b)
            | Self::Or(a, b)
            | Self::And(a, b)
            | Self::Iff(a, b) => a.has_sub() || b.has_sub(),
            Self::Ite(c, a, b) => c.has_sub() || a.has_sub() || b.has_sub(),
        }
    }

    /// How many nodes the term has.
    fn size(&self) -> u64 {
        match self {
            Self::Int(_) | Self::Var(_) | Self::Bool(_) => 1,
            Self::Add(a, b)
            | Self::Sub(a, b)
            | Self::Gt(a, b)
            | Self::Le(a, b)
            | Self::Eq(a, b)
            | Self::Neq(a, b)
            | Self::Or(a, b)
            | Self::And(a, b)
            | Self::Iff(a, b) => 1 + a.size() + b.size(),
            Self::Ite(c, a, b) => 1 + c.size() + a.size() + b.size(),
        }
    }

    /// The term as a `Nat`, or `None` when it is not one (or overflows).
    fn number(&self, state: &[u64]) -> Option<u64> {
        match self {
            Self::Int(value) => Some(*value),
            Self::Var(slot) => state.get(*slot).copied(),
            Self::Add(left, right) => left.number(state)?.checked_add(right.number(state)?),
            Self::Sub(left, right) => {
                Some(left.number(state)?.saturating_sub(right.number(state)?))
            }
            Self::Ite(condition, then, otherwise) => {
                if condition.truth(state)? {
                    then.number(state)
                } else {
                    otherwise.number(state)
                }
            }
            _ => None,
        }
    }

    /// The operands of the first subtraction that stops at zero when the term
    /// is evaluated in `state`: `left - right` with `left < right`.
    fn truncates(&self, state: &[u64]) -> Option<(u64, u64)> {
        match self {
            Self::Int(_) | Self::Var(_) | Self::Bool(_) => None,
            Self::Sub(left, right) => {
                left.truncates(state).or_else(|| right.truncates(state)).or_else(|| {
                    let (left, right) = (left.number(state)?, right.number(state)?);
                    (left < right).then_some((left, right))
                })
            }
            Self::Add(left, right)
            | Self::Gt(left, right)
            | Self::Le(left, right)
            | Self::Eq(left, right)
            | Self::Neq(left, right)
            | Self::Or(left, right)
            | Self::And(left, right)
            | Self::Iff(left, right) => left.truncates(state).or_else(|| right.truncates(state)),
            Self::Ite(condition, then, otherwise) => condition.truncates(state).or_else(|| {
                if condition.truth(state)? {
                    then.truncates(state)
                } else {
                    otherwise.truncates(state)
                }
            }),
        }
    }

    /// The term as a `Bool`, or `None` when it is not one.
    pub(super) fn truth(&self, state: &[u64]) -> Option<bool> {
        match self {
            Self::Gt(left, right) => Some(left.number(state)? > right.number(state)?),
            Self::Le(left, right) => Some(left.number(state)? <= right.number(state)?),
            Self::Eq(left, right) => Some(left.number(state)? == right.number(state)?),
            Self::Neq(left, right) => Some(left.number(state)? != right.number(state)?),
            // Both operands are evaluated: a connective over an ill-sorted
            // operand has no value, whatever the other operand is.
            Self::Or(left, right) => {
                let (left, right) = (left.truth(state)?, right.truth(state)?);
                Some(left || right)
            }
            Self::And(left, right) => {
                let (left, right) = (left.truth(state)?, right.truth(state)?);
                Some(left && right)
            }
            Self::Iff(left, right) => Some(left.truth(state)? == right.truth(state)?),
            Self::Ite(condition, then, otherwise) => {
                if condition.truth(state)? {
                    then.truth(state)
                } else {
                    otherwise.truth(state)
                }
            }
            Self::Bool(value) => Some(*value),
            _ => None,
        }
    }
}

/// The run as the lines of a diagnostic note: the initial state in full, then
/// per step the action and the variables it changed. A long run keeps its
/// first [`SHOWN_HEAD`] and last [`SHOWN_TAIL`] steps.
#[must_use]
pub fn render_run(model: &str, invariant: &str, run: &[CleanIslandModelStep]) -> String {
    const SHOWN_HEAD: usize = 4;
    const SHOWN_TAIL: usize = 16;
    let assignments = |pairs: &mut dyn Iterator<Item = &(String, u64)>| {
        pairs.map(|(name, value)| format!("{name} = {value}")).collect::<Vec<_>>().join(", ")
    };
    let steps = run.len().saturating_sub(1);
    let action_width = run.iter().map(|step| step.action.len()).max().unwrap_or(0);
    let number_width = steps.to_string().len();
    let mut lines = vec![format!(
        "a shortest run of `{model}` to the state that breaks `{invariant}` ({steps} step{}); \
         the kernel replayed each step:",
        if steps == 1 { "" } else { "s" }
    )];
    for (number, step) in run.iter().enumerate() {
        if run.len() > SHOWN_HEAD + SHOWN_TAIL + 1 {
            if number == SHOWN_HEAD {
                lines.push(format!(
                    "  {:>number_width$}  ({} steps not shown)",
                    "...",
                    run.len() - SHOWN_HEAD - SHOWN_TAIL
                ));
            }
            if (SHOWN_HEAD..run.len() - SHOWN_TAIL).contains(&number) {
                continue;
            }
        }
        let shown = match number.checked_sub(1).and_then(|previous| run.get(previous)) {
            None => assignments(&mut step.state.iter()),
            Some(previous) => {
                let changed = assignments(
                    &mut step
                        .state
                        .iter()
                        .zip(&previous.state)
                        .filter(|(now, was)| now != was)
                        .map(|(now, _)| now),
                );
                if changed.is_empty() { "(no change)".to_owned() } else { changed }
            }
        };
        lines.push(format!("  {number:>number_width$}: {:<action_width$}  {shown}", step.action));
    }
    lines.join("\n")
}

/// A progress counterexample as the lines of a diagnostic note: the stem like
/// a run, then the loop the run repeats forever (or that it stutters).
#[must_use]
pub fn render_lasso(
    claim: &str,
    model: &str,
    stem: &[CleanIslandModelStep],
    cycle: &[CleanIslandModelStep],
) -> String {
    let assignments = |pairs: &mut dyn Iterator<Item = &(String, u64)>| {
        pairs.map(|(name, value)| format!("{name} = {value}")).collect::<Vec<_>>().join(", ")
    };
    let total = stem.len() + cycle.len();
    let action_width = stem.iter().chain(cycle).map(|step| step.action.len()).max().unwrap_or(0);
    let number_width = total.saturating_sub(1).to_string().len();
    let mut lines = vec![format!(
        "a fair run of `{model}` that leaves the goal of `{claim}` for good; the kernel replayed \
         each step and evaluated the goal and the fairness conditions on the loop:"
    )];
    // Every step's line, then the middle of a long stem or loop left out.
    const SHOWN_HEAD: usize = 4;
    const SHOWN_TAIL: usize = 16;
    let mut previous: Option<&CleanIslandModelStep> = None;
    let mut step_lines = Vec::with_capacity(total);
    for (number, step) in stem.iter().chain(cycle).enumerate() {
        let shown = match previous {
            None => assignments(&mut step.state.iter()),
            Some(previous) => assignments(
                &mut step
                    .state
                    .iter()
                    .zip(&previous.state)
                    .filter(|(now, was)| now != was)
                    .map(|(now, _)| now),
            ),
        };
        step_lines
            .push(format!("  {number:>number_width$}: {:<action_width$}  {shown}", step.action));
        previous = Some(step);
    }
    let mut part = |lines: &mut Vec<String>, from: usize, len: usize| {
        for offset in 0..len {
            if len > SHOWN_HEAD + SHOWN_TAIL + 1 {
                if offset == SHOWN_HEAD {
                    lines.push(format!(
                        "  {:>number_width$}  ({} steps not shown)",
                        "...",
                        len - SHOWN_HEAD - SHOWN_TAIL
                    ));
                }
                if (SHOWN_HEAD..len - SHOWN_TAIL).contains(&offset) {
                    continue;
                }
            }
            lines.push(std::mem::take(&mut step_lines[from + offset]));
        }
    };
    part(&mut lines, 0, stem.len());
    if !cycle.is_empty() {
        lines.push(format!("  then it repeats these {} step(s) forever:", cycle.len()));
        part(&mut lines, stem.len(), cycle.len());
    }
    if cycle.is_empty() {
        lines.push(
            "  then it stutters there forever: no fair action can change that state".to_owned(),
        );
    }
    lines.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn counter_run(steps: u64) -> Vec<CleanIslandModelStep> {
        (0..=steps)
            .map(|x| CleanIslandModelStep {
                action: if x == 0 { "(initial)".to_owned() } else { "Step".to_owned() },
                state: vec![("x".to_owned(), x)],
            })
            .collect()
    }

    /// A short run prints every step; a long one keeps its head and tail, says
    /// how many it left out, and keeps its columns aligned past step 9.
    #[test]
    fn a_long_run_is_elided_and_stays_aligned() {
        let short = render_run("M", "Bound", &counter_run(3));
        assert_eq!(short.lines().count(), 5, "{short}");
        assert!(
            short.starts_with("a shortest run of `M` to the state that breaks `Bound` (3 steps)")
        );

        let long = render_run("M", "Bound", &counter_run(57));
        let lines: Vec<&str> = long.lines().collect();
        assert_eq!(lines.len(), 1 + 4 + 1 + 16, "{long}");
        assert_eq!(lines[1], "   0: (initial)  x = 0");
        assert_eq!(lines[4], "   3: Step       x = 3");
        assert_eq!(lines[5], "  ...  (38 steps not shown)");
        assert_eq!(lines[6], "  42: Step       x = 42");
        assert_eq!(lines[21], "  57: Step       x = 57");
    }
}

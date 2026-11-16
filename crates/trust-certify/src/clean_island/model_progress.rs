// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Progress claims: the untrusted search for a fair run that leaves the goal
//! for good, which the kernel then confirms.
//!
//! A `Trust.Temporal.FiniteModel.ScalarProgress` says its goal holds again and
//! again on every fair run of its model (`[]<> goal`). The counterexample is a
//! LASSO: a stem from the initial state, then a loop the run repeats forever
//! without the goal holding anywhere on it, such that fairness does not forbid
//! it. Fairness is about steps that CHANGE the state, and a run may stutter
//! forever, exactly as in `Trust.Temporal` (`NonStuttering`, `Enabled`).
//!
//! The search (Emerson–Lei over the strongly connected components of the
//! non-goal states) is this module's, on [`super::model_trace`]'s reading of
//! the model. What it finds is reported only after the KERNEL confirms it:
//! `lassoVerdict claim stem loop` in the served checker replays the stem and
//! the loop with the checker's own guards and successors and evaluates the
//! goal and every fairness condition on the loop's rows.
//!
//! Finding no counterexample PROVES NOTHING: it is this untrusted search's
//! answer over the states it reached, and is reported as exactly that.

use std::collections::{HashMap, VecDeque};

use clean_kernel::tc::TypeChecker;
use clean_kernel::{Environment, Expr};

use super::model_check::{NAMESPACE, head_and_args, list, string};
use super::model_trace::{
    CleanIslandModelStep, Effort, MAX_STATES, Machine, MachineSystem, Unevaluable, constructor,
    kernel_replays, nat_list,
};

/// A row's levels, outermost first, each `(rank, helper)`.
pub(super) type Levels = Vec<(u64, u64)>;

/// A certificate row: a reachable row and its levels.
pub(super) type CertificateRow = (Vec<u64>, Levels);

/// What [`search`] found for one claim.
pub(super) enum ProgressSearch {
    /// A fair run leaves the goal for good, and the kernel confirmed it.
    /// `stem` starts with `(initial)`; `cycle` is the loop from the stem's
    /// last state back to it, EMPTY when the run stutters there forever.
    Livelock { model: String, stem: Vec<CleanIslandModelStep>, cycle: Vec<CleanIslandModelStep> },
    /// Every reachable state was explored and no fair run leaves the goal for
    /// good — this module's answer, not a proof. `certificate` is the
    /// certificate the kernel's `progressCheck` reads (every reachable row
    /// with its levels), or why none was found; `effort` is what the kernel's
    /// check costs.
    NoCounterexample {
        model: String,
        states: usize,
        certificate: Result<Vec<CertificateRow>, String>,
        effort: Effort,
    },
    /// The claim could not be read or searched; why.
    Unread(String),
}

/// The reachable graph, states in breadth-first order (index 0 is initial).
struct Graph {
    states: Vec<Vec<u64>>,
    /// Per state, every step that CHANGES it: `(action, target)`.
    moves: Vec<Vec<(usize, usize)>>,
    /// Per state, the state and action it was first reached by.
    parent: Vec<Option<(usize, usize)>>,
}

/// Builds the [`Graph`] while ty's search (`tla_mc_core::explore_bfs`) runs:
/// ty reports each transition before it admits the target, so a new state's
/// parent and the move that found it are known when it is admitted.
struct GraphBuilder {
    graph: Graph,
    index: HashMap<Vec<u64>, usize>,
    pending: Option<(usize, usize)>,
    pending_move: Option<(usize, usize)>,
}

impl tla_mc_core::ExplorationObserver<MachineSystem<'_>> for GraphBuilder {
    fn on_new_state(&mut self, state: &Vec<u64>) -> bool {
        let fresh = self.graph.states.len();
        self.index.insert(state.clone(), fresh);
        self.graph.states.push(state.clone());
        self.graph.moves.push(Vec::new());
        self.graph.parent.push(self.pending.take());
        if let Some((from, action)) = self.pending_move.take() {
            self.graph.moves[from].push((action, fresh));
        }
        true
    }

    fn on_transition(&mut self, action: &usize, from: &Vec<u64>, to: &Vec<u64>) -> bool {
        let from_index = self.index[from];
        self.pending = Some((from_index, *action));
        self.pending_move = None;
        // A step that leaves the state as it is, is no move.
        if to != from {
            match self.index.get(to) {
                Some(&target) => self.graph.moves[from_index].push((*action, target)),
                None => self.pending_move = Some((from_index, *action)),
            }
        }
        true
    }

    fn on_deadlock(&mut self, _state: &Vec<u64>) {}

    fn is_done(&self) -> bool {
        false
    }
}

impl Graph {
    /// `Err` says why the reachable graph could not be built.
    fn explore(machine: &Machine) -> Result<Self, String> {
        let system = MachineSystem(machine);
        let mut builder = GraphBuilder {
            graph: Self { states: Vec::new(), moves: Vec::new(), parent: Vec::new() },
            index: HashMap::new(),
            pending: None,
            pending_move: None,
        };
        let options =
            tla_mc_core::BfsOptions { max_states: Some(MAX_STATES), ..Default::default() };
        let outcome = tla_mc_core::explore_bfs_with_options(&system, &mut builder, &options)
            .map_err(|error| match error {
                tla_mc_core::BfsError::Successors(source) => {
                    match source.downcast_ref::<Unevaluable>() {
                        Some(Unevaluable(action)) => format!(
                            "a step of `{}` cannot be evaluated on a reachable state",
                            machine.actions[*action].name
                        ),
                        None => source.to_string(),
                    }
                }
                other => other.to_string(),
            })?;
        if outcome.state_limit_reached {
            return Err(format!(
                "its model has more than {MAX_STATES} reachable states, the most the search explores"
            ));
        }
        Ok(builder.graph)
    }

    fn can_move(&self, state: usize, action: usize) -> bool {
        self.moves[state].iter().any(|(taken, _)| *taken == action)
    }

    /// The strongly connected components of the subgraph on `alive` (ty's
    /// `tla_mc_core::tarjan_scc`), each sorted, in order of their nearest state
    /// to the initial one. A single state is a component (a run may stutter
    /// there forever).
    fn components(&self, alive: &[bool]) -> Vec<Vec<usize>> {
        let nodes = (0..self.states.len()).filter(|&state| alive[state]);
        let found = tla_mc_core::tarjan_scc(nodes, |&state: &usize| {
            self.moves[state]
                .iter()
                .map(|&(_, target)| target)
                .filter(|&target| alive[target])
                .collect::<Vec<_>>()
        });
        let mut components: Vec<Vec<usize>> = found
            .sccs
            .iter()
            .map(|scc| {
                let mut component = scc.nodes().to_vec();
                component.sort_unstable();
                component
            })
            .collect();
        components.sort_by_key(|component| component[0]);
        components
    }

    /// A component a fair run can stay in forever, nearest the initial state
    /// first (Emerson–Lei).
    fn fair_component(
        &self,
        alive: &[bool],
        weak: &[usize],
        strong: &[usize],
    ) -> Option<Vec<usize>> {
        let mut inside = vec![false; self.states.len()];
        for component in self.components(alive) {
            for &state in &component {
                inside[state] = true;
            }
            let found = self.fair_within(&component, &inside, weak, strong);
            for &state in &component {
                inside[state] = false;
            }
            if found.is_some() {
                return found;
            }
        }
        None
    }

    /// [`Self::fair_component`] for one component, `inside` marking its states.
    fn fair_within(
        &self,
        component: &[usize],
        inside: &[bool],
        weak: &[usize],
        strong: &[usize],
    ) -> Option<Vec<usize>> {
        {
            let taken = |action: usize| {
                component.iter().any(|&state| {
                    self.moves[state].iter().any(|&(a, target)| a == action && inside[target])
                })
            };
            // Weakly fair, never taken here, and enabled at every state: it
            // stays enabled on any run confined here. No fair run stays.
            if weak.iter().any(|&action| {
                !taken(action) && component.iter().all(|&state| self.can_move(state, action))
            }) {
                return None;
            }
            // Strongly fair and never taken here: a fair run may stay only by
            // avoiding the states where it is enabled.
            let avoid: Vec<usize> =
                strong.iter().copied().filter(|&action| !taken(action)).collect();
            let dropped: Vec<usize> = component
                .iter()
                .copied()
                .filter(|&state| avoid.iter().any(|&action| self.can_move(state, action)))
                .collect();
            if dropped.is_empty() {
                return Some(component.to_vec());
            }
            let mut remaining = inside.to_vec();
            for state in dropped {
                remaining[state] = false;
            }
            self.fair_component(&remaining, weak, strong)
        }
    }

    /// The certificate the kernel's `progressCheck` reads: every reachable
    /// state as its row and its LEVELS, outermost first, each `(rank,
    /// helper)` (a goal state has none). `Err` names a region no fair action
    /// leaves, which the search should have reported as a livelock.
    fn certificate(
        &self,
        alive: &[bool],
        weak: &[usize],
        strong: &[usize],
        machine: &Machine,
    ) -> Result<Vec<CertificateRow>, String> {
        let mut levels = vec![Vec::new(); self.states.len()];
        for (state, below) in self.rank_region(alive, weak, strong, machine)? {
            levels[state] = below;
        }
        Ok(self.states.iter().cloned().zip(levels).collect())
    }

    /// The levels of the states of `region`, from this level down. A
    /// component of the graph `region` spans has as its rank its height above
    /// the components below it, so every step out of it goes down. Its helper
    /// is a weakly fair action that moves every state of it and has no step
    /// inside it. Failing that, a strongly fair action with no step inside it
    /// that moves some of its states: a run that stays in the component must,
    /// once fairness has it, keep to the states that action cannot move, and
    /// those are ranked one level deeper without it.
    fn rank_region(
        &self,
        region: &[bool],
        weak: &[usize],
        strong: &[usize],
        machine: &Machine,
    ) -> Result<Vec<(usize, Levels)>, String> {
        let components = self.components(region);
        let mut owner = vec![usize::MAX; self.states.len()];
        for (index, component) in components.iter().enumerate() {
            for &state in component {
                owner[state] = index;
            }
        }
        let height = self.heights(&components, &owner);
        let mut ranked = Vec::new();
        for (index, component) in components.iter().enumerate() {
            let rank = height[index];
            let inside = |action: usize| {
                component.iter().any(|&state| {
                    self.moves[state]
                        .iter()
                        .any(|&(a, target)| a == action && owner[target] == index)
                })
            };
            if let Some(helper) = weak.iter().copied().find(|&action| {
                component.iter().all(|&state| self.can_move(state, action)) && !inside(action)
            }) {
                ranked.extend(component.iter().map(|&state| (state, vec![(rank, helper as u64)])));
                continue;
            }
            let mut found = None;
            for (position, &action) in strong.iter().enumerate() {
                if inside(action) {
                    continue;
                }
                let mut asleep = vec![false; self.states.len()];
                let mut awake = false;
                for &state in component {
                    if self.can_move(state, action) {
                        awake = true;
                    } else {
                        asleep[state] = true;
                    }
                }
                if !awake {
                    continue;
                }
                let rest: Vec<usize> = strong
                    .iter()
                    .enumerate()
                    .filter(|&(other, _)| other != position)
                    .map(|(_, &other)| other)
                    .collect();
                if let Ok(deeper) = self.rank_region(&asleep, weak, &rest, machine) {
                    found = Some((action, deeper));
                    break;
                }
            }
            let Some((helper, deeper)) = found else {
                return Err(format!(
                    "no fair action leaves the {}-state region around {{ {} }}, though the search \
                     found no fair run that stays in it: a defect in Trust to report",
                    component.len(),
                    machine
                        .named(&self.states[component[0]])
                        .iter()
                        .map(|(name, value)| format!("{name} = {value}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                ));
            };
            let mut below: HashMap<usize, Levels> = deeper.into_iter().collect();
            for &state in component {
                let mut levels = vec![(rank, helper as u64)];
                levels.extend(below.remove(&state).unwrap_or_default());
                ranked.push((state, levels));
            }
        }
        Ok(ranked)
    }

    /// Each component's height in the graph of the components: one more than
    /// the highest component a step out of it reaches (iterative DFS).
    fn heights(&self, components: &[Vec<usize>], owner: &[usize]) -> Vec<u64> {
        let mut height: Vec<Option<u64>> = vec![None; components.len()];
        let mut stack = Vec::new();
        for root in 0..components.len() {
            if height[root].is_some() {
                continue;
            }
            stack.push((root, false));
            while let Some((component, expanded)) = stack.pop() {
                if height[component].is_some() {
                    continue;
                }
                let below = components[component]
                    .iter()
                    .flat_map(|&state| self.moves[state].iter().map(|&(_, target)| owner[target]))
                    .filter(|&other| other != usize::MAX && other != component);
                if expanded {
                    let top = below.filter_map(|other| height[other]).max().unwrap_or(0);
                    height[component] = Some(top + 1);
                } else {
                    stack.push((component, true));
                    stack.extend(
                        below
                            .filter(|&other| height[other].is_none())
                            .map(|other| (other, false)),
                    );
                }
            }
        }
        height.into_iter().map(|h| h.unwrap_or(1)).collect()
    }

    /// A shortest walk of moving steps from `from` to a state accepted by
    /// `goal`, staying inside `inside`: `(action, target)` per step.
    fn walk(
        &self,
        inside: &[bool],
        from: usize,
        goal: impl Fn(usize) -> bool,
    ) -> Option<Vec<(usize, usize)>> {
        let mut came: HashMap<usize, (usize, usize)> = HashMap::new();
        let mut queue = VecDeque::from([from]);
        let mut end = goal(from).then_some(from);
        while end.is_none() {
            let state = queue.pop_front()?;
            for &(action, target) in &self.moves[state] {
                if inside[target] && target != from && !came.contains_key(&target) {
                    came.insert(target, (state, action));
                    if goal(target) {
                        end = Some(target);
                        break;
                    }
                    queue.push_back(target);
                }
            }
        }
        let mut steps = Vec::new();
        let mut at = end?;
        while at != from {
            let (previous, action) = came[&at];
            steps.push((action, at));
            at = previous;
        }
        steps.reverse();
        Some(steps)
    }
}

/// Search `claim` (a constant of type `ScalarProgress`) for a fair run that
/// leaves its goal for good.
pub(super) fn search(env: &Environment, claim: &Expr) -> ProgressSearch {
    let unread = |why: &str| ProgressSearch::Unread(why.to_owned());
    let tc = &TypeChecker::with_mode(env, env.mode());
    // What the kernel says of a lasso, by its own checker each time (a long
    // replay must not inherit a spent evaluation limit): `Some(true)` it
    // confirms, `Some(false)` it evaluates a condition false, `None` it
    // cannot read the claim or a step; `Err` it ran out of evaluation.
    let kernel = |stem: Expr, cycle: Expr| -> Result<Option<bool>, ()> {
        let fresh = TypeChecker::with_mode(env, env.mode());
        let verdict = fresh.whnf(&Expr::app(
            Expr::app(
                Expr::app(Expr::const_str(&format!("{NAMESPACE}.lassoVerdict")), claim.clone()),
                stem,
            ),
            cycle,
        ));
        let (head, args) = head_and_args(&verdict);
        match (head.as_str(), &args[..]) {
            ("Option.none", [_]) => Ok(None),
            ("Option.some", [_, answer]) => match head_and_args(&fresh.whnf(answer)).0.as_str() {
                "Bool.true" => Ok(Some(true)),
                "Bool.false" => Ok(Some(false)),
                _ => Err(()),
            },
            _ => Err(()),
        }
    };
    let Some(fields) = constructor(tc, claim, "ScalarProgress.mk", 4) else {
        return unread("it does not reduce to a `ScalarProgress.mk`");
    };
    let Some(machine) = Machine::decode(tc, &fields[0]) else {
        return unread("its model uses a construct outside the checker's grammar");
    };
    // The model constant's name, or the name an unnamed model gives itself.
    let model = match head_and_args(&fields[0]) {
        (name, args) if args.is_empty() && !name.is_empty() => name,
        _ => machine.name.clone(),
    };
    let Some(goal) = machine.term(tc, &fields[1]) else {
        return unread("its goal uses a construct outside the checker's grammar");
    };
    // THE action of that name: fairness of a name two actions share is
    // ambiguous, and the kernel's `actionSlot` declines it too.
    let fair = |names: &Expr| -> Result<Vec<usize>, String> {
        let names = list(tc, names).ok_or("its fair actions are not a list of names")?;
        names
            .iter()
            .map(|name| {
                let name = string(tc, name).ok_or("a fair action's name is not a string")?;
                let mut named = machine
                    .actions
                    .iter()
                    .enumerate()
                    .filter(|(_, action)| action.name == name)
                    .map(|(position, _)| position);
                match (named.next(), named.next()) {
                    (Some(position), None) => Ok(position),
                    (None, _) => Err(format!(
                        "it names the fair action `{name}`, which its model does not declare"
                    )),
                    (Some(_), Some(_)) => Err(format!(
                        "it names the fair action `{name}`, which its model declares more than once"
                    )),
                }
            })
            .collect()
    };
    let (weak, strong) = match (fair(&fields[2]), fair(&fields[3])) {
        (Ok(weak), Ok(strong)) => (weak, strong),
        (Err(why), _) | (_, Err(why)) => return ProgressSearch::Unread(why),
    };
    if let Some(&both) = weak.iter().find(|action| strong.contains(action)) {
        return ProgressSearch::Unread(format!(
            "it names `{}` both weakly and strongly fair",
            machine.actions[both].name
        ));
    }
    let graph = match Graph::explore(&machine) {
        Ok(graph) => graph,
        Err(why) => return ProgressSearch::Unread(why),
    };
    let mut alive = Vec::with_capacity(graph.states.len());
    for state in &graph.states {
        match goal.truth(state) {
            Some(holds) => alive.push(!holds),
            None => return unread("its goal is not a Boolean on a reachable state"),
        }
    }
    let Some(component) = graph.fair_component(&alive, &weak, &strong) else {
        // "No counterexample" is only worth saying of a claim the kernel can
        // read: otherwise no lasso could ever have been confirmed.
        return match kernel(nat_list(std::iter::empty()), nat_list(std::iter::empty())) {
            Ok(Some(_)) => ProgressSearch::NoCounterexample {
                model,
                states: graph.states.len(),
                certificate: graph.certificate(&alive, &weak, &strong, &machine),
                effort: machine.effort(graph.states.iter().map(Vec::as_slice)),
            },
            Ok(None) => unread(
                "the kernel's checker cannot read it (its model or goal is outside the grammar)",
            ),
            Err(()) => unread("the kernel did not finish reading it within its evaluation limit"),
        };
    };

    // The lasso: a shortest stem to the component's nearest state, then a loop
    // through what fairness asks of it — a step of every fair action that has
    // one inside, and a state where every other weakly fair action is off.
    let entry = component[0];
    let mut inside = vec![false; graph.states.len()];
    for &state in &component {
        inside[state] = true;
    }
    let mut stem = Vec::new();
    let mut at = entry;
    while let Some((previous, action)) = graph.parent[at] {
        stem.push((action, at));
        at = previous;
    }
    stem.reverse();
    let mut cycle: Vec<(usize, usize)> = Vec::new();
    let mut here = entry;
    for &action in weak.iter().chain(&strong) {
        if cycle.iter().any(|(taken, _)| *taken == action) {
            continue;
        }
        let edge = component.iter().find_map(|&state| {
            graph.moves[state]
                .iter()
                .find(|&&(a, target)| a == action && inside[target])
                .map(|&(_, target)| (state, target))
        });
        let leg = match edge {
            Some((source, target)) => {
                graph.walk(&inside, here, |state| state == source).map(|mut steps| {
                    steps.push((action, target));
                    steps
                })
            }
            // No step inside: a weakly fair action must be off somewhere on
            // the loop (a strongly fair one is off everywhere in here).
            None if weak.contains(&action) => {
                graph.walk(&inside, here, |state| !graph.can_move(state, action))
            }
            None => Some(Vec::new()),
        };
        let Some(leg) = leg else { return unread("no loop through its fair component was found") };
        here = leg.last().map_or(here, |&(_, target)| target);
        cycle.extend(leg);
    }
    if here != entry {
        let Some(back) = graph.walk(&inside, here, |state| state == entry) else {
            return unread("no loop through its fair component was found");
        };
        cycle.extend(back);
    }

    // The kernel's word on it.
    let positions =
        |steps: &[(usize, usize)]| nat_list(steps.iter().map(|&(action, _)| action as u64));
    let found = format!(
        "the search found a fair run that leaves the goal for good ({} steps, then a loop of {})",
        stem.len(),
        cycle.len()
    );
    match kernel(positions(&stem), positions(&cycle)) {
        Ok(Some(true)) => {}
        Ok(Some(false)) => {
            return ProgressSearch::Unread(format!(
                "{found}, but the kernel evaluates one of its conditions false: the search and \
                 the checker disagree, which is a defect in Trust to report"
            ));
        }
        Ok(None) => {
            return ProgressSearch::Unread(format!(
                "{found}, but the kernel's checker cannot read the claim or one of the steps"
            ));
        }
        Err(()) => {
            return ProgressSearch::Unread(format!(
                "{found}, but the kernel reached its evaluation limit before it finished \
                 replaying it"
            ));
        }
    }
    let step = |&(action, target): &(usize, usize)| CleanIslandModelStep {
        action: machine.actions[action].name.clone(),
        state: machine.named(&graph.states[target]),
    };
    let stem_len = 1 + stem.len();
    let mut run = Vec::with_capacity(stem_len + cycle.len());
    run.push(CleanIslandModelStep {
        action: "(initial)".to_owned(),
        state: machine.named(&graph.states[0]),
    });
    run.extend(stem.iter().map(step));
    run.extend(cycle.iter().map(step));
    // The states printed are this module's; hold them to the kernel's rows.
    let taken: Vec<usize> = stem.iter().chain(&cycle).map(|&(action, _)| action).collect();
    if !kernel_replays(tc, &fields[0], &taken, &run) {
        return unread("the kernel's replay of the run does not match the states found");
    }
    let named_cycle = run.split_off(stem_len);
    ProgressSearch::Livelock { model, stem: run, cycle: named_cycle }
}

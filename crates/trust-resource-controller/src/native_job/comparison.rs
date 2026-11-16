// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Preselected comparison population. These are graph/configuration DATA,
//! never native executions, proof outcomes or permission to publish a ref.
use std::collections::BTreeMap;

use super::*;

mod land;
pub use land::{LandSelection, SourcePair};

const MAX_PAIRS: usize = MAX_NODES / 2;
const MAX_REPETITIONS: u32 = 31;
const MAX_ACTIONS: usize = 64;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Metric {
    /// Actual parent entry-to-return interval, including transport/capture.
    /// This is not CPU attribution, quietness or statistical significance.
    ParentActionIntervalV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActionPair {
    pub action: String,
    pub repetition: u32,
    pub baseline: NodeId,
    pub candidate: NodeId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Selection {
    /// Same original workload source indices for both produced programs.
    /// Program build sources are independently retained and may differ.
    pub workload_sources: Vec<u32>,
    pub pairs: Vec<ActionPair>,
    pub repetitions: u32,
    pub focus: String,
    pub metric: Metric,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Side {
    Baseline,
    Candidate,
}

fn selected_program(
    artifact: &Artifact,
    baseline: &Artifact,
    candidate: &Artifact,
) -> Option<Side> {
    if artifact == baseline {
        Some(Side::Baseline)
    } else if artifact == candidate {
        Some(Side::Candidate)
    } else {
        None
    }
}

/// Follow actual declared artifact edges, bounded independently of Plan's DAG
/// checks. Nested produced tools remain visible in the requested population;
/// paired_shape subsequently refuses that unsupported comparison profile.
fn origin(
    plan: &Plan,
    mut id: NodeId,
    baseline: &Artifact,
    candidate: &Artifact,
) -> io::Result<Option<Side>> {
    for _ in 0..MAX_NODES {
        let node = plan.nodes.get(id.0 as usize).ok_or_else(invalid)?;
        let artifact = match &node.kind {
            Kind::Compile { frontend: Frontend::Produced(artifact), .. } => artifact,
            Kind::Verify { artifact, .. }
            | Kind::Tests { artifact, .. }
            | Kind::Run { artifact, .. } => artifact,
            _ => return Ok(None),
        };
        if let Some(side) = selected_program(artifact, baseline, candidate) {
            return Ok(Some(side));
        }
        if artifact.producer.0 >= id.0 {
            return Err(invalid());
        }
        id = artifact.producer;
    }
    Err(invalid())
}

impl Selection {
    fn syntax(&self) -> io::Result<()> {
        if self.workload_sources.is_empty()
            || self.workload_sources.len() > MAX_SOURCES
            || self.workload_sources.windows(2).any(|pair| pair[0] >= pair[1])
            || self.pairs.is_empty()
            || self.pairs.len() > MAX_PAIRS
            || !(1..=MAX_REPETITIONS).contains(&self.repetitions)
            || !name(&self.focus)
        {
            return Err(invalid());
        }
        let mut nodes = BTreeSet::new();
        let mut population = BTreeMap::<&str, BTreeSet<u32>>::new();
        for pair in &self.pairs {
            if !name(&pair.action)
                || pair.repetition >= self.repetitions
                || !nodes.insert(pair.baseline)
                || !nodes.insert(pair.candidate)
                || !population.entry(&pair.action).or_default().insert(pair.repetition)
            {
                return Err(invalid());
            }
        }
        if population.len() > MAX_ACTIONS
            || !population.contains_key(self.focus.as_str())
            || population.values().any(|repetitions| repetitions.len() != self.repetitions as usize)
        {
            return Err(invalid());
        }
        Ok(())
    }

    /// Require the complete requested descendant population, including failed
    /// or unsupported nodes. A parser cannot discard one to make comparison
    /// complete. Native outcome/configuration checks remain the caller's duty.
    pub fn validate(
        &self,
        plan: &Plan,
        baseline: &Artifact,
        candidate: &Artifact,
        comparison: NodeId,
    ) -> io::Result<()> {
        self.syntax()?;
        if baseline == candidate
            || comparison.0 as usize >= plan.nodes.len()
            || self.workload_sources.iter().any(|index| *index as usize >= plan.sources.len())
        {
            return Err(invalid());
        }
        let selected = plan.nodes.get(comparison.0 as usize).ok_or_else(invalid)?;
        let mut ancestors = BTreeSet::new();
        let mut pending =
            selected.dependencies.iter().map(|dependency| dependency.node).collect::<Vec<_>>();
        while let Some(id) = pending.pop() {
            if id.0 >= comparison.0 {
                return Err(invalid());
            }
            if ancestors.insert(id) {
                let node = plan.nodes.get(id.0 as usize).ok_or_else(invalid)?;
                for dependency in &node.dependencies {
                    if dependency.node.0 >= id.0 {
                        return Err(invalid());
                    }
                    pending.push(dependency.node);
                }
            }
        }
        let mut expected = BTreeSet::new();
        for index in 0..plan.nodes.len() {
            let id = NodeId(index as u32);
            if origin(plan, id, baseline, candidate)?.is_some() {
                if id.0 >= comparison.0 || !ancestors.contains(&id) {
                    return Err(invalid());
                }
                expected.insert(id);
            }
        }
        let paired = self
            .pairs
            .iter()
            .flat_map(|pair| [pair.baseline, pair.candidate])
            .collect::<BTreeSet<_>>();
        if paired != expected {
            return Err(invalid());
        }
        let by_baseline = self
            .pairs
            .iter()
            .map(|pair| (pair.baseline, pair.candidate))
            .collect::<BTreeMap<_, _>>();
        // Preserve action order/cache history instead of relabeling a warm
        // candidate as its cold baseline. This finite profile requires the
        // same topological action order on both sides.
        let ordered = by_baseline.values().copied().collect::<Vec<_>>();
        if ordered.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(invalid());
        }
        let mut outputs = BTreeMap::new();
        let mut reverse_outputs = BTreeMap::new();
        let mut before_outputs = BTreeSet::new();
        let mut after_outputs = BTreeSet::new();
        let mut action_cases = BTreeMap::<&str, NodeId>::new();
        for pair in &self.pairs {
            if origin(plan, pair.baseline, baseline, candidate)? != Some(Side::Baseline)
                || origin(plan, pair.candidate, baseline, candidate)? != Some(Side::Candidate)
            {
                return Err(invalid());
            }
            if let Some(previous) = action_cases.insert(&pair.action, pair.baseline)
                && !same_case(plan, previous, pair.baseline)?
            {
                return Err(invalid());
            }
            let before_node = &plan.nodes[pair.baseline.0 as usize];
            let after_node = &plan.nodes[pair.candidate.0 as usize];
            if before_node.timeout_ns != after_node.timeout_ns {
                return Err(invalid());
            }
            let dependency_map = |node: &Node, translate: bool| {
                node.dependencies
                    .iter()
                    .map(|dependency| {
                        let id = if translate && dependency.node == baseline.producer {
                            candidate.producer
                        } else if translate {
                            *by_baseline.get(&dependency.node).unwrap_or(&dependency.node)
                        } else {
                            dependency.node
                        };
                        (id, dependency.condition)
                    })
                    .collect::<BTreeMap<_, _>>()
            };
            if dependency_map(before_node, true) != dependency_map(after_node, false) {
                return Err(invalid());
            }
            let before = &plan.nodes[pair.baseline.0 as usize].kind;
            let after = &plan.nodes[pair.candidate.0 as usize].kind;
            match (before, after) {
                (
                    Kind::Compile {
                        source: a,
                        output: x,
                        unit: u,
                        mode: m,
                        features: f,
                        frontend: Frontend::Produced(p),
                    },
                    Kind::Compile {
                        source: b,
                        output: y,
                        unit: v,
                        mode: n,
                        features: g,
                        frontend: Frontend::Produced(q),
                    },
                ) => {
                    if a != b
                        || !self.workload_sources.contains(a)
                        || u != v
                        || m != n
                        || f != g
                        || p != baseline
                        || q != candidate
                        || outputs.get(x).is_some_and(|old| old != y)
                        || reverse_outputs.get(y).is_some_and(|old| old != x)
                    {
                        return Err(invalid());
                    }
                    outputs.insert(*x, *y);
                    reverse_outputs.insert(*y, *x);
                    before_outputs.insert(*x);
                    after_outputs.insert(*y);
                }
                (
                    Kind::Verify { artifact: a, policy: p },
                    Kind::Verify { artifact: b, policy: q },
                ) => {
                    if p != q || !paired_artifacts(a, b, baseline, candidate, &by_baseline) {
                        return Err(invalid());
                    }
                }
                (
                    Kind::Tests { artifact: a, arguments: p },
                    Kind::Tests { artifact: b, arguments: q },
                )
                | (
                    Kind::Run { artifact: a, arguments: p },
                    Kind::Run { artifact: b, arguments: q },
                ) => {
                    if p != q || !paired_artifacts(a, b, baseline, candidate, &by_baseline) {
                        return Err(invalid());
                    }
                }
                _ => return Err(invalid()),
            }
        }
        // Distinct original output domains are required on both sides; a
        // candidate may not reuse baseline artifacts or populate its cache.
        if !before_outputs.is_disjoint(&after_outputs) {
            return Err(invalid());
        }
        Ok(())
    }

    pub(super) fn write(&self, e: &mut Encoder) -> io::Result<()> {
        self.syntax()?;
        e.number(1);
        e.number(self.workload_sources.len() as u64);
        for source in &self.workload_sources {
            e.number(u64::from(*source));
        }
        e.number(u64::from(self.repetitions));
        e.bytes(self.focus.as_bytes())?;
        e.number(match self.metric {
            Metric::ParentActionIntervalV1 => 1,
        });
        e.number(self.pairs.len() as u64);
        for pair in &self.pairs {
            e.bytes(pair.action.as_bytes())?;
            e.number(u64::from(pair.repetition));
            e.number(u64::from(pair.baseline.0));
            e.number(u64::from(pair.candidate.0));
        }
        Ok(())
    }
    pub(super) fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        if d.number()? != 1 {
            return Err(invalid());
        }
        let count = d.count(MAX_SOURCES)?;
        let mut workload_sources = Vec::with_capacity(count);
        for _ in 0..count {
            workload_sources.push(d.narrow()?);
        }
        let repetitions = d.narrow()?;
        let focus = read_name(d)?;
        let metric = match d.number()? {
            1 => Metric::ParentActionIntervalV1,
            _ => return Err(invalid()),
        };
        let count = d.count(MAX_PAIRS)?;
        let mut pairs = Vec::with_capacity(count);
        for _ in 0..count {
            pairs.push(ActionPair {
                action: read_name(d)?,
                repetition: d.narrow()?,
                baseline: NodeId(d.narrow()?),
                candidate: NodeId(d.narrow()?),
            });
        }
        let selection = Self { workload_sources, pairs, repetitions, focus, metric };
        selection.syntax()?;
        Ok(selection)
    }
}

/// Repetitions cannot be relabeled mixtures of sources, flags, action kinds or
/// cache history. Actual effective compiler configuration is checked again by
/// the retained native caller; this is conservative declared-input equality.
fn same_case(plan: &Plan, a: NodeId, b: NodeId) -> io::Result<bool> {
    let get = |id: NodeId| plan.nodes.get(id.0 as usize).ok_or_else(invalid);
    let before = get(a)?;
    let after = get(b)?;
    if before.timeout_ns != after.timeout_ns {
        return Ok(false);
    }
    Ok(match (&before.kind, &after.kind) {
        (
            Kind::Compile { source: x, output: u, unit: p, mode: m, features: f, .. },
            Kind::Compile { source: y, output: v, unit: q, mode: n, features: g, .. },
        ) => {
            let history =
                |id: NodeId, output: u32| {
                    plan.nodes[..id.0 as usize]
                        .iter()
                        .filter_map(move |node| match &node.kind {
                            Kind::Compile {
                                source, output: actual, unit, mode, features, ..
                            } if *actual == output => Some((source, unit, mode, features)),
                            _ => None,
                        })
                        .collect::<Vec<_>>()
                };
            x == y && p == q && m == n && f == g && history(a, *u) == history(b, *v)
        }
        (Kind::Verify { artifact: x, policy: p }, Kind::Verify { artifact: y, policy: q }) => {
            p == q && x.unit == y.unit && same_case(plan, x.producer, y.producer)?
        }
        (Kind::Tests { artifact: x, arguments: p }, Kind::Tests { artifact: y, arguments: q })
        | (Kind::Run { artifact: x, arguments: p }, Kind::Run { artifact: y, arguments: q }) => {
            p == q && x.unit == y.unit && same_case(plan, x.producer, y.producer)?
        }
        _ => false,
    })
}

fn read_name(d: &mut Decoder<'_>) -> io::Result<String> {
    let length = d.count(256)?;
    let text = std::str::from_utf8(d.take(length)?).map_err(|_| invalid())?;
    if !name(text) {
        return Err(invalid());
    }
    Ok(text.to_owned())
}

fn paired_artifacts(
    before: &Artifact,
    after: &Artifact,
    baseline: &Artifact,
    candidate: &Artifact,
    mapping: &BTreeMap<NodeId, NodeId>,
) -> bool {
    (before == baseline && after == candidate)
        || (before.unit == after.unit && mapping.get(&before.producer) == Some(&after.producer))
}

#[cfg(test)]
mod tests;

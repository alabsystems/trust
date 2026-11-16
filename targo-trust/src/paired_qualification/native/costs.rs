//! Consumed diagnostic comparison of checked observations. This module cannot
//! create an execution owner, identify a cache hit, grant proof credit or land
//! a proposed change. Overlapping CPU scopes are deliberately never summed.
use std::collections::BTreeMap;

use serde_json::{Value, json};
use trust_resource_controller::accounting::Observation;
use trust_resource_controller::paired_qualification::service;

use crate::paired_qualification::protocol::Protocol;

pub(super) struct RootObservation {
    pub invocation_elapsed_ns: Option<u64>,
    pub leader_runtime_ns: u64,
    pub accounting: Option<Observation>,
}
pub(super) struct Side<'a> {
    pub protocol: &'a Protocol,
    pub intervals: &'a BTreeMap<service::Node, Option<u64>>,
    pub root: Option<&'a RootObservation>,
}
fn label(node: service::Node) -> String {
    match node {
        service::Node::AyCompile => "AY compilation".into(),
        service::Node::ConsumerCompile => "consumer compilation".into(),
        service::Node::Advisory => "advisory verification".into(),
        service::Node::Strict => "strict verification".into(),
        service::Node::Inventory { target } => {
            format!("{} inventory", trust_test_execution::workload::TARGETS[target as usize])
        }
        service::Node::Sample { target, repetition } => format!(
            "{} sample {}",
            trust_test_execution::workload::TARGETS[target as usize],
            repetition + 1
        ),
    }
}
fn difference(before: u64, after: u64) -> Value {
    json!({"direction":if after<before{"lower"}else if after>before{"higher"}else{"equal"},
        "magnitude":before.abs_diff(after)})
}
fn measured(observation: Option<Observation>) -> bool {
    observation.is_some_and(|o| o.cpu_times.is_some() && o.peak_rss_bytes.is_some())
}
fn root_json(root: Option<&RootObservation>) -> Value {
    root.map_or(Value::Null,|r|json!({"invocation_elapsed_ns":r.invocation_elapsed_ns,
        "leader_go_to_exit_ns":r.leader_runtime_ns,"accounting":r.accounting.map(super::accounting_json),
        "scope":"original Root child and waited descendants, including local helpers; separately hosted targets are excluded; no sum with member counters"}))
}
struct Collected {
    complete: bool,
    rows: Vec<Value>,
    longest: Option<(service::Node, u64)>,
    samples: [Vec<Option<u64>>; 2],
}
fn collect(repetitions: u32, side: &Side<'_>) -> Collected {
    let expected = service::Node::population(repetitions).unwrap_or_default();
    let outcomes = side.protocol.outcomes().map(|row| (row.node, row)).collect::<BTreeMap<_, _>>();
    let expected_keys = expected.iter().copied().collect::<Vec<_>>();
    let observed_keys = outcomes.keys().copied().collect::<Vec<_>>();
    let mut complete = !expected.is_empty()
        && expected_keys == observed_keys
        && side.protocol.measured()
        && side.protocol.ready.as_ref().is_some_and(|r| r.repetitions == repetitions)
        && side.root.is_some_and(|root| {
            root.invocation_elapsed_ns.is_some_and(|ns| ns >= root.leader_runtime_ns)
                && measured(root.accounting)
        });
    let compilers = side
        .protocol
        .compiler_observations()
        .map(|row| (row.node, row))
        .collect::<BTreeMap<_, _>>();
    let mut rows = Vec::new();
    let mut longest: Option<(service::Node, u64)> = None;
    let mut samples: [Vec<Option<u64>>; 2] = [Vec::new(), Vec::new()];
    for node in expected {
        let interval = side.intervals.get(&node).copied().flatten();
        let interval_valid = interval.is_some_and(|ns| {
            side.root.and_then(|root| root.invocation_elapsed_ns).is_some_and(|root| ns <= root)
        });
        complete &= interval_valid;
        if let Some(ns) = interval.filter(|_| interval_valid) {
            if longest.is_none_or(|(_, old)| ns > old) {
                longest = Some((node, ns));
            }
        }
        let mut row = json!({"node":format!("{node:?}"),"label":label(node),"frontend_observed_registration_to_terminal_ns":interval});
        match outcomes.get(&node).map(|row| &row.result) {
            Some(service::Result::Compiled { succeeded, local_workers_joined, .. }) => {
                let observation = compilers.get(&node).copied();
                complete &= *succeeded
                    && *local_workers_joined
                    && observation
                        .and_then(|o| o.counts.as_ref())
                        .is_some_and(|c| c.successful_primary_processes.is_some());
                row["compiler_report"] =
                    observation.map_or(Value::Null, super::compiler_observation_json);
            }
            Some(service::Result::Captured { capture, elapsed_ns, .. }) => {
                let native = outcomes[&node];
                complete &= Protocol::native_complete(native)
                    && measured(capture.accounting)
                    && capture.runtime_ns.is_some_and(|runtime| runtime <= *elapsed_ns);
                row["native_action"] = json!({"action_elapsed_ns":elapsed_ns,"leader_go_to_exit_ns":capture.runtime_ns,
                    "accounting":capture.accounting.map(super::accounting_json),
                    "scope":"same original admitted action and its waited descendants; separate from Root/helpers and other hosted members"});
                if let service::Node::Sample { target, .. } = node {
                    samples[target as usize].push(
                        (Protocol::native_complete(native)
                            && capture.outcome
                                == Some(trust_resource_controller::Outcome::Exit(0)))
                        .then_some(*elapsed_ns),
                    );
                }
            }
            _ => {
                complete = false;
                if let service::Node::Sample { target, .. } = node {
                    samples[target as usize].push(None);
                }
            }
        }
        rows.push(row);
    }
    Collected { complete, rows, longest, samples }
}
/// All repetitions remain in the denominator. A missing observation never
/// disappears through filtering and is never substituted with a zero.
fn samples(values: &[Option<u64>], expected: usize) -> Value {
    if values.len() != expected || expected == 0 || values.iter().any(Option::is_none) {
        return json!({"complete":false,"expected":expected,"observations":values});
    }
    let mut sorted = values.iter().map(|n| n.unwrap()).collect::<Vec<_>>();
    sorted.sort_unstable();
    json!({"complete":true,"expected":expected,"observations":values,
        "scope":"successful complete sample action wall intervals only; CPU/RSS completeness stays independently required",
        "minimum_ns":sorted[0],"median_upper_ns":sorted[sorted.len()/2],"maximum_ns":sorted[sorted.len()-1]})
}
pub(super) fn compare(
    repetitions: u32,
    before: Side<'_>,
    after: Side<'_>,
    eligible: bool,
) -> Value {
    let control = collect(repetitions, &before);
    let candidate = collect(repetitions, &after);
    let complete = eligible && control.complete && candidate.complete;
    let launches=[service::Node::AyCompile,service::Node::ConsumerCompile].map(|node| {
        let a=compiler_counts(before.protocol,node);let b=compiler_counts(after.protocol,node);
        json!({"node":format!("{node:?}"),"registered_units":[a.map(|c|c.registered),b.map(|c|c.registered)],
            "successful_primary_processes":[a.and_then(|c|c.successful_primary_processes),b.and_then(|c|c.successful_primary_processes)],
            "change":if complete {a.and_then(|c|c.successful_primary_processes).zip(b.and_then(|c|c.successful_primary_processes)).map(|(a,b)|difference(a,b))}else{None},
            "scope":"physical compiler launch counts from checked original reports; a decrease is not itself a cache-hit or proof-reuse claim"})
    });
    let root_change = if complete {
        before
            .root
            .and_then(|r| r.invocation_elapsed_ns)
            .zip(after.root.and_then(|r| r.invocation_elapsed_ns))
            .map(|(a, b)| difference(a, b))
    } else {
        None
    };
    let bottleneck = |side: &Collected| {
        if complete {
            side.longest.map(|(node,ns)|json!({"node":format!("{node:?}"),
        "label":label(node),"observed_interval_ns":ns,"basis":"longest frontend-observed registration-to-terminal interval; includes delivery/backpressure; not an inferred CPU cause or summed critical path"}))
        } else {
            None
        }
    };
    json!({"schema":"trust.paired-native-cost-comparison.v1","complete":complete,
        "input_and_semantic_comparison_eligible":eligible,
        "control":{"complete_measurements":control.complete,"root":root_json(before.root),"nodes":control.rows,
            "sample_elapsed":control.samples.iter().map(|v|samples(v,repetitions as usize)).collect::<Vec<_>>(),"measured_bottleneck_candidate":bottleneck(&control)},
        "candidate":{"complete_measurements":candidate.complete,"root":root_json(after.root),"nodes":candidate.rows,
            "sample_elapsed":candidate.samples.iter().map(|v|samples(v,repetitions as usize)).collect::<Vec<_>>(),"measured_bottleneck_candidate":bottleneck(&candidate)},
        "invocation_elapsed_change":root_change,"compiler_launch_changes":launches,
        "scope":"diagnostic original observations only; overlapping Root/helper/member CPU is never summed; no cache/proof/source, admission or landing grant"})
}

fn compiler_counts(
    protocol: &Protocol,
    node: service::Node,
) -> Option<&service::compiler_observation::Counts> {
    protocol.compiler_observations().find(|o| o.node == node).and_then(|o| o.counts.as_ref())
}

#[cfg(test)]
mod tests;

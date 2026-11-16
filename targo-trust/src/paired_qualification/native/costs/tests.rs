use trust_resource_controller::accounting::{CpuTimes, Scope};

use super::*;

fn protocol(metrics: bool) -> Protocol {
    // Serialized observation fixtures only; never live candidates or grants.
    let mut protocol = crate::paired_qualification::protocol::tests::complete_graph(metrics);
    let final_observation = service::Final {
        binding: protocol.binding().unwrap().clone(),
        repetitions: 1,
        finished: 8,
        blocked: 0,
        inputs_unchanged: true,
        snapshot: [5; 16],
        members: 6,
    };
    protocol.frame(&final_observation.encode().unwrap()).unwrap();
    protocol
}
fn root(metrics: bool) -> RootObservation {
    RootObservation {
        invocation_elapsed_ns: Some(1000),
        leader_runtime_ns: 900,
        accounting: Some(Observation {
            scope: Scope::ChildAndWaitedDescendantsV1,
            cpu_times: metrics.then_some(CpuTimes { user_ns: 0, system_ns: 0 }),
            peak_rss_bytes: Some(0),
        }),
    }
}
fn intervals() -> BTreeMap<service::Node, Option<u64>> {
    service::Node::population(1)
        .unwrap()
        .into_iter()
        .map(|node| {
            (
                node,
                Some(if node == service::Node::AyCompile {
                    100
                } else if node == service::Node::ConsumerCompile {
                    80
                } else {
                    10
                }),
            )
        })
        .collect()
}
#[test]
fn measured_candidate_identifies_an_observed_node_without_summing_cpu_or_claiming_reuse() {
    let before = protocol(true);
    let after = protocol(true);
    let root = root(true);
    let before_intervals = intervals();
    let mut after_intervals = intervals();
    after_intervals.insert(service::Node::AyCompile, Some(50));
    let result = compare(
        1,
        Side { protocol: &before, intervals: &before_intervals, root: Some(&root) },
        Side { protocol: &after, intervals: &after_intervals, root: Some(&root) },
        true,
    );
    assert_eq!(result["complete"], true);
    assert_eq!(result["control"]["measured_bottleneck_candidate"]["node"], "AyCompile");
    assert_eq!(result["candidate"]["measured_bottleneck_candidate"]["node"], "ConsumerCompile");
    assert_eq!(result["compiler_launch_changes"][0]["successful_primary_processes"], json!([0, 0]));
    assert_eq!(result["compiler_launch_changes"][0]["change"]["direction"], "equal");
    assert_eq!(result["control"]["root"]["accounting"]["cpu_times"]["user_ns"], 0);
    assert!(result.get("total_cpu_ns").is_none());
    assert!(result.get("cache_hits").is_none());
}
#[test]
fn missing_metrics_or_one_original_node_never_becomes_zero_or_a_partial_bottleneck() {
    let before = protocol(true);
    let after = protocol(true);
    let complete = root(true);
    let unknown = root(false);
    let original = intervals();
    let mut partial = intervals();
    partial.remove(&service::Node::Sample { target: 1, repetition: 0 });
    for (observed, root) in [(&partial, &complete), (&original, &unknown)] {
        let result = compare(
            1,
            Side { protocol: &before, intervals: &original, root: Some(&complete) },
            Side { protocol: &after, intervals: observed, root: Some(root) },
            true,
        );
        assert_eq!(result["complete"], false);
        assert_eq!(result["candidate"]["measured_bottleneck_candidate"], Value::Null);
        assert_eq!(result["candidate"]["nodes"].as_array().unwrap().len(), 8);
        assert_eq!(result["invocation_elapsed_change"], Value::Null);
    }
}
#[test]
fn final_input_or_semantic_failure_withholds_comparisons_even_with_complete_measurements() {
    let p = protocol(true);
    let r = root(true);
    let intervals = intervals();
    let result = compare(
        1,
        Side { protocol: &p, intervals: &intervals, root: Some(&r) },
        Side { protocol: &p, intervals: &intervals, root: Some(&r) },
        false,
    );
    assert_eq!(result["control"]["complete_measurements"], true);
    assert_eq!(result["complete"], false);
    assert_eq!(result["control"]["measured_bottleneck_candidate"], Value::Null);
    assert_eq!(result["compiler_launch_changes"][0]["change"], Value::Null);
}
#[test]
fn repeated_sample_statistics_require_the_entire_requested_population_and_preserve_zero() {
    for count in [1, 3, 32] {
        let values = (0..count).map(|n| Some(n as u64)).collect::<Vec<_>>();
        assert_eq!(samples(&values, count)["complete"], true);
        assert_eq!(samples(&values, count)["minimum_ns"], 0);
        assert_eq!(samples(&values[..count - 1], count)["complete"], false);
        let mut missing = values;
        missing[count / 2] = None;
        let result = samples(&missing, count);
        assert_eq!(result["complete"], false);
        assert_eq!(result["observations"].as_array().unwrap().len(), count);
        assert!(result.get("median_upper_ns").is_none());
    }
    let changed = difference(0, u64::MAX);
    assert_eq!(changed["magnitude"].as_u64(), Some(u64::MAX));
    assert_eq!(difference(u64::MAX, 0)["direction"], "lower");
}

//! The real original Site::admits body captured from the unchanged self-use source.
use std::sync::OnceLock;

use trust_certify::inferred_return_proof::{
    InferredReturnProofGraph, replay_inferred_return_graph,
};

fn fixture() -> &'static InferredReturnProofGraph {
    static GRAPH: OnceLock<InferredReturnProofGraph> = OnceLock::new();
    GRAPH.get_or_init(|| {
        // Retained once from the real extractor/certifier run. Tests replay
        // these immutable proof facts; they never invoke a solver.
        let graph: InferredReturnProofGraph = serde_json::from_slice(include_bytes!(
            "fixtures/inferred-return-actual-proof-graph.json"
        ))
        .unwrap();
        let input: serde_json::Value =
            serde_json::from_str(include_str!("fixtures/inferred-return-actual-callee.json"))
                .unwrap();
        assert_eq!(serde_json::to_value(&graph.nodes[0].function).unwrap(), input["function"]);
        assert_eq!(
            serde_json::to_value(graph.nodes[0].identity).unwrap(),
            input["callee_identity"]
        );
        graph
    })
}

#[test]
fn actual_callee_graph_replays_every_original_check_and_reuses_fact() {
    let first = replay_inferred_return_graph(fixture()).unwrap();
    let second = replay_inferred_return_graph(fixture()).unwrap();
    assert_eq!(first.digest(), second.digest());
}

#[test]
fn inferred_graph_refuses_missing_duplicate_tampered_and_assumption_inputs() {
    let mut cases = Vec::new();
    cases.push(InferredReturnProofGraph::default());
    let mut graph = fixture().clone();
    graph.nodes.push(graph.nodes[0].clone());
    cases.push(graph);
    let mut graph = fixture().clone();
    graph.nodes[0].evidence.pop();
    cases.push(graph);
    let mut graph = fixture().clone();
    let own_identity = graph.nodes[0].identity;
    graph.nodes[0].children.push(own_identity);
    cases.push(graph);
    let mut graph = fixture().clone();
    graph.nodes[0].function.body.blocks.clear();
    cases.push(graph);
    let mut graph = fixture().clone();
    graph.nodes[0].function.preconditions.push(trust_types::Formula::Bool(false));
    graph.nodes[0].function.body.blocks = vec![trust_types::BasicBlock {
        id: trust_types::BlockId(0),
        stmts: vec![trust_types::Statement::Assign {
            place: trust_types::Place::local(0),
            rvalue: trust_types::Rvalue::Use(trust_types::Operand::Constant(
                trust_types::ConstValue::Bool(false),
            )),
            span: graph.nodes[0].function.span.clone(),
        }],
        terminator: trust_types::Terminator::Return,
    }];
    cases.push(graph);
    let mut graph = fixture().clone();
    if let trust_ir::ProofEvidence::CleanCic { lineage, .. } = &mut graph.nodes[0].evidence[0] {
        lineage.bytes[0] ^= 1;
    } else {
        panic!("not CleanCic")
    };
    cases.push(graph);
    for (index, case) in cases.iter().enumerate() {
        assert!(replay_inferred_return_graph(case).is_err(), "mutant {index}");
    }
}

#[test]
fn entry_hypotheses_cannot_supply_the_unconditional_return_proof() {
    let mut graph = fixture().clone();
    graph.nodes[0].function.preconditions.push(trust_types::Formula::Bool(false));
    // The exact original check generator clears entry hypotheses; a stronger
    // unconditional fact remains valid, rather than being proved vacuously.
    assert!(replay_inferred_return_graph(&graph).is_ok());
}

#[test]
fn actual_dependency_edges_reject_cycles_missing_nodes_and_unbound_calls() {
    fn with_call(identity: Option<trust_types::CalleeIdentity>) -> InferredReturnProofGraph {
        let mut graph = fixture().clone();
        let node = &mut graph.nodes[0];
        node.children = identity.into_iter().collect();
        node.function.body.blocks[0].terminator = trust_types::Terminator::Call {
            func: node.function.def_path.clone(),
            args: vec![],
            dest: trust_types::Place::local(0),
            target: Some(trust_types::BlockId(0)),
            span: node.function.span.clone(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            unwind: trust_types::UnwindEdge::Unreachable,
            callee_identity: identity,
            callee_key: None,
        };
        graph
    }
    let own = fixture().nodes[0].identity;
    assert_eq!(
        replay_inferred_return_graph(&with_call(Some(own))).unwrap_err(),
        "cyclic or over-depth inferred return graph"
    );
    let missing = trust_types::CalleeIdentity { def_index: own.def_index + 1, ..own };
    assert_eq!(
        replay_inferred_return_graph(&with_call(Some(missing))).unwrap_err(),
        "missing inferred return dependency"
    );
    assert_eq!(
        replay_inferred_return_graph(&with_call(None)).unwrap_err(),
        "unbound original callee identity"
    );
}

#[test]
fn actual_callee_replay_keeps_original_function_budget() {
    use std::time::{Duration, Instant};

    use trust_types::determinism::StopCause;
    use trust_types::verify_budget::{VerifyBudgetGuard, WALL_POLL_INTERVAL, exhaustion_cause};
    let graph = fixture();
    replay_inferred_return_graph(graph)
        .expect("retained body proofs replay with the current kernel");
    for (deadline, steps, cause) in [
        (None, 0, StopCause::Steps),
        (
            Some(Instant::now() - Duration::from_millis(1)),
            WALL_POLL_INTERVAL,
            StopCause::WallBackstop,
        ),
    ] {
        let _budget = VerifyBudgetGuard::install(deadline, steps);
        assert!(replay_inferred_return_graph(graph).is_err());
        assert_eq!(exhaustion_cause(), Some(cause));
    }
}

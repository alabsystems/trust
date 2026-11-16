//! Pure custody/graph/renderer controls. Real compiler storage capture is
//! exercised independently by run-make/trust-source-static-readback; these
//! tests do not claim that synthetic bytes are a Rust execution or proof.

use std::num::NonZeroU64;

use rustc_span::DUMMY_SP;
use rustc_span::def_id::DefIndex;

use super::*;

fn allocation(value: u64) -> AllocId {
    AllocId(NonZeroU64::new(value).unwrap())
}

fn owner(index: u32) -> LocalDefId {
    LocalDefId { local_def_index: DefIndex::from_u32(index) }
}

fn body(index: u32, static_index: u32, alloc: u64) -> CapturedBody {
    CapturedBody {
        owner: owner(index),
        uses: vec![StaticUse {
            expr_index: 7,
            definition: owner(static_index).to_def_id(),
            allocation: allocation(alloc),
            span: DUMMY_SP,
        }],
        scan_error: None,
    }
}

fn memory() -> ConstantImageMemory {
    ConstantImageMemory {
        layout: ConstantImageLayout { size_bytes: 4, align_bytes: 2 },
        mutable: true,
        bytes: vec![Some(0), None, Some(255), None],
        relocations: Vec::new(),
    }
}

fn graph() -> Graph {
    let mut graph = Graph::default();
    let id = graph.reserve(allocation(1)).unwrap();
    graph.nodes.insert(id, ConstantImageNode::Memory(memory()));
    graph
}

fn definition_named(name: &str, hash: u64) -> ConstantImageDefinition {
    ConstantImageDefinition {
        def_path: name.into(),
        def_path_hash: CallableDefPathHash::new(11, hash),
    }
}

#[test]
fn allocation_identity_not_contents_controls_reservation() {
    let mut graph = graph();
    assert_eq!(graph.reserve(allocation(1)).unwrap(), 0);
    assert_eq!(graph.reserve(allocation(2)).unwrap(), 1);
    graph.nodes.insert(1, ConstantImageNode::Memory(memory()));
    assert_eq!(graph.nodes[&0], graph.nodes[&1]);
    assert_ne!(graph.allocations[0], graph.allocations[1]);
    assert!(graph.validate().is_ok());
    assert_eq!(graph.reserve(allocation(1)).unwrap(), 0);
}

#[test]
fn self_cycle_uses_reserved_identity_without_recursive_expansion() {
    let mut graph = graph();
    let mut memory = memory();
    memory.relocations.push(ConstantImageRelocation {
        offset_bytes: 0,
        pointer: ConstantImagePointer {
            allocation_id: graph.reserve(allocation(1)).unwrap(),
            offset_bytes: 0,
            immutable: true,
            shared_ref: true,
        },
    });
    graph.nodes.insert(0, ConstantImageNode::Memory(memory));
    assert!(graph.validate().is_ok());
    assert_eq!(graph.allocations.len(), 1);
    assert!(graph_json(&[], &graph, &BTreeSet::new()).contains("\"allocation_id\":0"));
}

#[test]
fn exact_caps_refuse_before_mutating_budgets_or_assigning_an_extra_id() {
    let mut graph = Graph::default();
    for index in 1..=MAX_NODES {
        assert_eq!(graph.reserve(allocation(index as u64)).unwrap(), (index - 1) as u32);
    }
    assert_eq!(
        graph.reserve(allocation(1000)).unwrap_err(),
        "source static readback exceeds budget of 64 nodes"
    );
    assert_eq!(graph.allocations.len(), MAX_NODES);
    assert_eq!(graph.reserve(allocation(1)).unwrap(), 0);
    assert!(graph.charge(MAX_BYTES, MAX_RELOCATIONS).is_ok());
    assert_eq!(
        graph.charge(1, 0).unwrap_err(),
        "source static readback exceeds budget of 65536 bytes"
    );
    assert_eq!(
        graph.charge(0, 1).unwrap_err(),
        "source static readback exceeds budget of 1024 relocations"
    );
    assert_eq!((graph.bytes, graph.relocations), (MAX_BYTES, MAX_RELOCATIONS));
    graph.bytes = usize::MAX;
    assert!(graph.charge(1, 0).unwrap_err().contains("overflow"));
}

#[test]
fn failed_owner_cannot_publish_partial_graph_or_exhaust_another_owner() {
    let mut refused = graph();
    let error = refused.charge(MAX_BYTES + 1, 0).unwrap_err();
    let report = graph_json(&["{\"allocation_id\":0}".into()], &refused, &BTreeSet::from([error]));
    assert!(report.contains("\"capture_status\":\"refused\""));
    assert!(report.contains("\"statics\":[],\"nodes\":[]"));
    let mut independent = graph();
    independent.charge(4, 0).unwrap();
    let report = graph_json(&["{\"allocation_id\":0}".into()], &independent, &BTreeSet::new());
    assert!(report.contains("\"capture_status\":\"complete\""));
    assert!(report.contains("\"statics\":[{\"allocation_id\":0}]"));
}

#[test]
fn unfinished_and_orphan_graphs_are_not_rendered_as_complete() {
    let mut graph = graph();
    graph.reserve(allocation(2)).unwrap();
    assert!(graph.validate().unwrap_err().contains("incomplete"));
    assert!(graph_json(&[], &graph, &BTreeSet::new()).contains("\"nodes\":[]"));
    graph.nodes.insert(1, ConstantImageNode::Memory(memory()));
    let mut memory = memory();
    memory.relocations.push(ConstantImageRelocation {
        offset_bytes: 0,
        pointer: ConstantImagePointer {
            allocation_id: 77,
            offset_bytes: 0,
            immutable: false,
            shared_ref: false,
        },
    });
    graph.nodes.insert(0, ConstantImageNode::Memory(memory));
    assert!(graph.validate().unwrap_err().contains("orphan relocation"));
    let report = graph_json(&[], &graph, &BTreeSet::new());
    assert!(report.contains("\"capture_status\":\"refused\""));
    assert!(report.contains("\"statics\":[],\"nodes\":[]"));
}

#[test]
fn initialization_layout_relocation_and_both_provenance_flags_survive_rendering() {
    let mut memory = memory();
    memory.relocations.push(ConstantImageRelocation {
        offset_bytes: 2,
        pointer: ConstantImagePointer {
            allocation_id: 7,
            offset_bytes: 13,
            immutable: false,
            shared_ref: true,
        },
    });
    let json = memory_json(&memory);
    assert!(json.contains("\"layout\":{\"size_bytes\":4,\"align_bytes\":2}"));
    assert!(json.contains("\"mutable\":true,\"bytes\":[0,null,255,null]"));
    assert!(json.contains("\"offset_bytes\":2,\"pointer\":{\"allocation_id\":7,\"offset_bytes\":13,\"immutable\":false,\"shared_ref\":true}"));
}

#[test]
fn static_and_full_function_instance_identities_are_not_display_labels() {
    let first = ConstantImageNode::Static {
        definition: definition_named("same_label", 12),
        declared_mutable: false,
        freeze: false,
        thread_local: false,
        foreign: false,
        initializer: memory(),
    };
    let second = ConstantImageNode::Static {
        definition: definition_named("same_label", 13),
        declared_mutable: false,
        freeze: false,
        thread_local: false,
        foreign: false,
        initializer: memory(),
    };
    assert_ne!(node_json(0, &first), node_json(0, &second));
    let function = |fingerprint| ConstantImageNode::Function {
        definition: definition_named("init", 14),
        instance_fingerprint: fingerprint,
        instance_debug: "init::<u8>".into(),
        callee_identity: trust_types::CalleeIdentity {
            stable_crate_id: 11,
            def_index: 21,
            substs_digest: [22, 23],
        },
    };
    assert_ne!(node_json(0, &function([1, 2])), node_json(0, &function([1, 3])));
    let json = node_json(0, &function([1, 2]));
    assert!(json.contains("\"instance_fingerprint\":[\"0000000000000001\",\"0000000000000002\"]"));
    assert!(json.contains("\"callee_identity\":{\"stable_crate_id\":\"000000000000000b\",\"def_index\":21,\"substs_digest\":[\"0000000000000016\",\"0000000000000017\"]}"));
}

#[test]
fn repeated_static_identity_across_owners_is_valid_but_conflicting_allocation_poison_is_sticky() {
    let mut registry = CaptureRegistry::default();
    registry.insert(body(1, 90, 100));
    registry.insert(body(2, 90, 100));
    registry.check_inventory(&BTreeSet::from([1, 2]));
    assert!(registry.errors.is_empty());
    assert_eq!(registry.statics.len(), 1);
    registry.insert(body(3, 90, 101));
    assert!(registry.errors.iter().any(|error| error.contains("identity conflict")));
    registry.insert(body(4, 90, 100));
    registry.check_inventory(&BTreeSet::from([1, 2, 3, 4]));
    assert!(!registry.errors.is_empty());
    assert_eq!(registry.statics[&owner(90).to_def_id()], allocation(100));
}

#[test]
fn duplicate_missing_and_orphan_owners_refuse_and_take_resets_the_attempt() {
    let mut registry = CaptureRegistry::default();
    registry.insert(body(1, 90, 100));
    registry.insert(body(1, 91, 101));
    assert_eq!(registry.bodies.len(), 1);
    assert!(registry.errors.iter().any(|error| error.contains("duplicate")));
    registry.check_inventory(&BTreeSet::from([2]));
    assert!(registry.errors.iter().any(|error| error.contains("1 missing, 1 orphan")));
    registry.insert(body(2, 91, 101));
    registry.check_inventory(&BTreeSet::from([1, 2]));
    assert!(!registry.errors.is_empty(), "late callbacks cannot repair failed inventory");
    let refused = std::mem::take(&mut registry);
    assert!(!refused.errors.is_empty());
    assert!(registry.errors.is_empty());
    assert!(registry.bodies.is_empty());
    assert!(registry.statics.is_empty());
}

#[test]
fn source_scan_refusal_is_per_owner_and_does_not_change_registration_inventory() {
    let mut registry = CaptureRegistry::default();
    let mut refused = body(1, 90, 100);
    refused.scan_error = Some("source static readback exceeds scan budget".into());
    registry.insert(refused);
    registry.insert(body(2, 91, 101));
    registry.check_inventory(&BTreeSet::from([1, 2]));
    assert!(registry.errors.is_empty());
    assert!(registry.bodies[&1].scan_error.is_some());
    assert!(registry.bodies[&2].scan_error.is_none());
    assert_eq!(registry.bodies[&1].uses.len(), 1, "refusal cannot erase retained source uses");
}

#[test]
fn coverage_append_is_opt_in_canonical_and_inside_the_existing_commit_marker() {
    let coverage = "{\n  \"crate\": \"subject\"\n}\n".to_string();
    assert_eq!(append_to_coverage(coverage.clone(), None).unwrap(), coverage);
    let appended = append_to_coverage(coverage, Some("{\"proof_authority\":false}")).unwrap();
    assert_eq!(
        appended,
        "{\n  \"crate\": \"subject\",\n  \"source_static_readback\": {\"proof_authority\":false}\n}\n"
    );
    assert!(append_to_coverage("{}".into(), Some("{}")).is_err());
    assert!(append_to_coverage("{}\r\n".into(), Some("{}")).is_err());
    assert_eq!(quoted("\"\\\n\r\t\u{1f}é"), "\"\\\"\\\\\\n\\r\\t\\u001fé\"");
}

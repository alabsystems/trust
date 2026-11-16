//! Bounded compiler-owned callee-body inventory, never proof admission.
//!
//! Every direct call is resolved with the caller's compiler environment. Full
//! compiler Instances, not printed names or DefIds alone, key captured bodies.
//! Indirect calls, missing bodies, and budget frontiers remain explicit. Drop
//! glue and implicit runtime calls are not claimed covered by this inventory.

use std::collections::{HashMap, VecDeque};

use rustc_middle::mir;
use rustc_middle::ty::{self, TyCtxt};
use serde_json::{Value, json};
use trust_mir_extract::instance_body::{
    FaithfulInstanceError, extract_instance_faithful, faithful_instance_descriptor,
    resolve_faithful_call,
};
use trust_types::{ConstantImageNode, VerifiableFunction};

const MAX_INSTANCES: usize = 64;
const MAX_BODY_NODES: usize = 4096;
const MAX_BODY_JSON_BYTES: usize = 16 * 1024 * 1024;

struct Inventory<'tcx> {
    tcx: TyCtxt<'tcx>,
    ids: HashMap<ty::Instance<'tcx>, usize>,
    pending: VecDeque<(usize, ty::Instance<'tcx>)>,
    records: Vec<Value>,
    refused_edges: usize,
    refused_bodies: usize,
}

impl<'tcx> Inventory<'tcx> {
    fn target(&mut self, instance: ty::Instance<'tcx>) -> Result<Value, String> {
        let descriptor = faithful_instance_descriptor(self.tcx, instance)
            .map_err(|error| format!("resolved instance descriptor refused: {error}"))?;
        if let Some(id) = self.ids.get(&instance) {
            return Ok(json!({"instance": descriptor, "body_id": id}));
        }
        if self.ids.len() >= MAX_INSTANCES {
            self.refused_edges += 1;
            return Ok(json!({
                "instance": descriptor,
                "body_id": null,
                "refusal": "instance inventory budget exhausted",
            }));
        }
        let id = self.ids.len();
        self.ids.insert(instance, id);
        self.pending.push_back((id, instance));
        Ok(json!({"instance": descriptor, "body_id": id}))
    }

    fn edges(
        &mut self,
        body: &mir::Body<'tcx>,
        function: &VerifiableFunction,
        allocation_functions: Vec<(u32, Result<ty::Instance<'tcx>, FaithfulInstanceError>)>,
    ) -> Result<Value, String> {
        let mut calls = Vec::new();
        let mut other_execution_edges = Vec::new();
        for (block, data) in body.basic_blocks.iter_enumerated() {
            let (operand, kind) = match &data.terminator().kind {
                mir::TerminatorKind::Call { func, .. } => (func, "call"),
                mir::TerminatorKind::TailCall { func, .. } => (func, "tail_call"),
                mir::TerminatorKind::Drop { .. }
                | mir::TerminatorKind::InlineAsm { .. }
                | mir::TerminatorKind::Yield { .. } => {
                    other_execution_edges.push(json!({
                        "block": block.as_usize(),
                        "terminator": format!("{:?}", data.terminator().kind),
                        "status": "not-inventoried-runtime-edge",
                    }));
                    continue;
                }
                _ => continue,
            };
            let model_identity = function
                .body
                .blocks
                .iter()
                .find(|model| model.id.0 == block.as_usize())
                .and_then(|model| match &model.terminator {
                    trust_types::Terminator::Call { callee_identity, .. }
                    | trust_types::Terminator::TailCall { callee_identity, .. } => *callee_identity,
                    _ => None,
                });
            match resolve_faithful_call(self.tcx, body, operand) {
                Ok(resolved) => {
                    // This association concerns the written call. The resolved
                    // impl/shim's own identity is deliberately a separate field.
                    let identity_matches = model_identity == Some(resolved.syntactic_identity);
                    if !identity_matches {
                        self.refused_edges += 1;
                    }
                    calls.push(json!({
                        "block": block.as_usize(),
                        "kind": kind,
                        "syntactic_definition": resolved.syntactic_definition,
                        "syntactic_identity": resolved.syntactic_identity,
                        "extracted_call_identity": model_identity,
                        "extracted_call_identity_matches": identity_matches,
                        "resolved": self.target(resolved.instance)?,
                    }));
                }
                Err(error) => {
                    self.refused_edges += 1;
                    calls.push(json!({
                        "block": block.as_usize(),
                        "kind": kind,
                        "extracted_call_identity": model_identity,
                        "refusal": error.to_string(),
                        "operand_debug": format!("{operand:?}"),
                    }));
                }
            }
        }
        let mut relocations = Vec::new();
        for (allocation_id, instance) in allocation_functions {
            match instance {
                Ok(instance) => relocations.push(json!({
                    "body_local_allocation_id": allocation_id,
                    "resolved": self.target(instance)?,
                })),
                Err(error) => {
                    self.refused_edges += 1;
                    relocations.push(json!({
                        "body_local_allocation_id": allocation_id,
                        "refusal": error.to_string(),
                    }));
                }
            }
        }
        Ok(json!({
            "calls": calls,
            "constant_function_allocations": relocations,
            "other_execution_edges": other_execution_edges,
        }))
    }
}

fn render_mir<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> Result<String, String> {
    let mut bytes = Vec::new();
    mir::pretty::MirWriter::new(tcx)
        .write_mir_fn(body, &mut bytes)
        .map_err(|error| format!("cannot render instance MIR: {error}"))?;
    String::from_utf8(bytes).map_err(|error| error.to_string())
}

fn refused_edge_count(records: &[Value]) -> usize {
    records
        .iter()
        .filter_map(|record| record.get("edges"))
        .flat_map(|edges| {
            ["calls", "constant_function_allocations"]
                .into_iter()
                .filter_map(|kind| edges.get(kind).and_then(Value::as_array))
                .flatten()
        })
        .filter(|edge| {
            edge.get("refusal").is_some()
                || edge.get("extracted_call_identity_matches") == Some(&Value::Bool(false))
                || edge.get("resolved").is_some_and(|target| target.get("refusal").is_some())
        })
        .count()
}

pub fn capture<'tcx>(
    tcx: TyCtxt<'tcx>,
    root_body: &mir::Body<'tcx>,
    root_function: &VerifiableFunction,
    root_allocations: Vec<(u32, Result<ty::Instance<'tcx>, FaithfulInstanceError>)>,
) -> Result<Value, String> {
    // The selected production helper has no type/const parameters. Do not use
    // this root constructor for an arbitrary generic definition.
    let root_instance = ty::Instance::mono(tcx, root_body.source.def_id());
    let root_descriptor =
        faithful_instance_descriptor(tcx, root_instance).map_err(|error| error.to_string())?;
    let mut inventory = Inventory {
        tcx,
        ids: HashMap::from([(root_instance, 0)]),
        pending: VecDeque::new(),
        records: Vec::new(),
        refused_edges: 0,
        refused_bodies: 0,
    };
    let root_edges = inventory.edges(root_body, root_function, root_allocations)?;
    inventory.records.push(json!({
        "body_id": 0,
        "instance": root_descriptor,
        "status": "captured-root-in-parent-report",
        "edges": root_edges,
    }));
    while let Some((id, instance)) = inventory.pending.pop_front() {
        let descriptor =
            faithful_instance_descriptor(tcx, instance).map_err(|error| error.to_string())?;
        match extract_instance_faithful(tcx, instance) {
            Err(error) => {
                inventory.refused_bodies += 1;
                inventory.records.push(json!({
                    "body_id": id,
                    "instance": descriptor,
                    "status": "body-refused",
                    "refusal": error.to_string(),
                }));
            }
            Ok(captured) => {
                let body_nodes = captured
                    .mir
                    .basic_blocks
                    .iter()
                    .map(|block| block.statements.len() + 1)
                    .sum::<usize>();
                let function_json =
                    serde_json::to_value(&captured.function).map_err(|error| error.to_string())?;
                let body_json_bytes =
                    serde_json::to_vec(&function_json).map_err(|error| error.to_string())?.len();
                if body_nodes > MAX_BODY_NODES || body_json_bytes > MAX_BODY_JSON_BYTES {
                    inventory.refused_bodies += 1;
                    inventory.records.push(json!({
                        "body_id": id,
                        "instance": descriptor,
                        "status": "body-refused",
                        "refusal": "instance body exceeds diagnostic output budget",
                        "body_nodes": body_nodes,
                        "body_json_bytes": body_json_bytes,
                    }));
                    continue;
                }
                let edges = inventory.edges(
                    &captured.mir,
                    &captured.function,
                    captured.allocation_functions,
                )?;
                inventory.records.push(json!({
                    "body_id": id,
                    "instance": descriptor,
                    "status": "captured-not-verified",
                    "function_json_sha256": super::support::json_digest(&function_json)?,
                    "function": function_json,
                    "instantiated_mir_text": render_mir(tcx, &captured.mir)?,
                    "instantiated_mir_debug": format!("{:#?}", captured.mir),
                    "edges": edges,
                }));
            }
        }
    }
    // Fingerprints are portable diagnostics, not the in-process de-dup key.
    // Never silently serialize two distinct Instances as the same identity.
    let mut fingerprints = HashMap::new();
    for instance in inventory.ids.keys() {
        let ConstantImageNode::Function { instance_fingerprint, .. } =
            faithful_instance_descriptor(tcx, *instance).map_err(|error| error.to_string())?
        else {
            return Err("instance descriptor is not a function".into());
        };
        if fingerprints.insert(instance_fingerprint, instance).is_some() {
            return Err("distinct compiler instances share one diagnostic fingerprint".into());
        }
    }
    Ok(json!({
        "schema_version": "trust.faithful-callee-inventory.diagnostic/v1",
        "evidence_grade": "diagnostic-no-official-evidence",
        "max_instances": MAX_INSTANCES,
        "max_body_nodes": MAX_BODY_NODES,
        "max_body_json_bytes": MAX_BODY_JSON_BYTES,
        // A call may have both an identity mismatch and a budget refusal.
        // Preserve the event census, but count each refused edge only once.
        "refusal_events": inventory.refused_edges,
        "refused_call_or_relocation_edges": refused_edge_count(&inventory.records),
        "refused_bodies": inventory.refused_bodies,
        "whole_execution_closure_established": false,
        "limits": [
            "Only explicit call/tail-call and successfully captured constant-function targets are inventoried.",
            "Drop glue, implicit runtime calls, indirect-call target sets and unwind semantics remain separate obligations.",
            "An exact instantiated MIR body is not an executable-lowering or source-refinement certificate.",
            "Captured functions may still contain unsupported operations or memory images with no execution semantics."
        ],
        "bodies": inventory.records,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refusal_census_counts_overlapping_reasons_once_per_edge() {
        let records = vec![
            json!({"edges": {
                "calls": [
                    {"extracted_call_identity_matches": true, "resolved": {"body_id": 1}},
                    {"extracted_call_identity_matches": false,
                     "resolved": {"body_id": null, "refusal": "budget"}},
                    {"refusal": "indirect"},
                    {"extracted_call_identity_matches": false, "resolved": {"body_id": 2}},
                    {"extracted_call_identity_matches": true,
                     "resolved": {"body_id": null, "refusal": "budget"}}
                ],
                "constant_function_allocations": [
                    {"body_local_allocation_id": 1, "resolved": {"body_id": 3}},
                    {"body_local_allocation_id": 2, "refusal": "allocation mismatch"}
                ],
                "other_execution_edges": [{"status": "not-inventoried-runtime-edge"}]
            }}),
            json!({"status": "body-refused", "refusal": "Intrinsic"}),
        ];
        assert_eq!(refused_edge_count(&records), 5);
        assert_eq!(refused_edge_count(&[]), 0);
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Direct THIR static-use custody and bounded **cold initializer** readback.
//!
//! This is diagnostic source/storage evidence, not a lowering, evaluator, or
//! proof capability. A cold `LazyLock<T>` contains its initializer function,
//! not an initialized `T`; no union arm or current runtime value is inferred.
//! The temporary evaluator dependency is rustc CTFE (today implemented using
//! MIR), not MIR operand/body extraction. Collection inside `mir_built` never
//! evaluates a static. Readback runs only at the post-analysis finalizer seam.
//! Publication is opt-in through the existing direct dump / emit request and
//! rides the module's existing generation-bound coverage commit marker.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use rustc_abi::{Endian, Size};
use rustc_data_structures::fingerprint::Fingerprint;
use rustc_data_structures::stable_hash::{StableHash, StableHasher};
use rustc_middle::mir::interpret::{AllocId, Allocation, CtfeProvenance, GlobalAlloc, alloc_range};
use rustc_middle::thir::{ExprKind, Thir};
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use rustc_session::Session;
use rustc_span::Span;
use rustc_span::def_id::{DefId, LocalDefId};
use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{
    CallableDefPathHash, ConstantImageDefinition, ConstantImageLayout, ConstantImageMemory,
    ConstantImageNode, ConstantImagePointer, ConstantImageRelocation, ConstantImageTarget,
};

const MAX_NODES: usize = 64;
const MAX_BYTES: usize = 64 * 1024;
const MAX_RELOCATIONS: usize = 1024;
const MAX_BODY_EXPRS: usize = 65_536;
const MAX_BODIES: usize = 65_536;
const MAX_USES: usize = 4096;
const MAX_SOURCE_SNIPPET: usize = 64 * 1024;
const SOURCE_DIGEST_DOMAIN: &str = "trust.thir.source-static-readback.source.v1";

#[derive(Clone)]
struct StaticUse {
    expr_index: usize,
    definition: DefId,
    allocation: AllocId,
    span: Span,
}

struct CapturedBody {
    owner: LocalDefId,
    uses: Vec<StaticUse>,
    scan_error: Option<String>,
}

/// Session-owned, main-hook-only facts. Duplicate/conflicting callbacks poison
/// the attempt; replacement, late callbacks, and equal bytes cannot repair it.
#[derive(Default)]
pub(crate) struct CaptureRegistry {
    bodies: BTreeMap<u32, CapturedBody>,
    statics: FxHashMap<DefId, AllocId>,
    errors: BTreeSet<String>,
}

impl CaptureRegistry {
    fn error(&mut self, error: String) {
        // Bounded error retention; any retained error refuses the whole graph.
        if self.errors.len() < 32 {
            self.errors.insert(error);
        }
    }

    fn insert(&mut self, body: CapturedBody) {
        let index = body.owner.local_def_index.as_u32();
        if self.bodies.contains_key(&index) {
            self.error(format!("duplicate source static readback body registration: {index}"));
            return;
        }
        if self.bodies.len() >= MAX_BODIES {
            self.error(format!("source static readback exceeds budget of {MAX_BODIES} bodies"));
            return;
        }
        for usage in &body.uses {
            match self.statics.get(&usage.definition) {
                Some(allocation) if *allocation != usage.allocation => {
                    self.error("source static readback static allocation identity conflict".into());
                }
                Some(_) => {}
                None => {
                    self.statics.insert(usage.definition, usage.allocation);
                }
            }
        }
        self.bodies.insert(index, body);
    }

    fn check_inventory(&mut self, expected: &BTreeSet<u32>) {
        let actual: BTreeSet<_> = self.bodies.keys().copied().collect();
        let missing = expected.difference(&actual).count();
        let orphan = actual.difference(expected).count();
        if missing != 0 || orphan != 0 {
            self.error(format!(
                "source static readback body inventory mismatch: {missing} missing, {orphan} orphan"
            ));
        }
    }
}

fn requested(sess: &Session) -> bool {
    sess.opts.unstable_opts.trust_dump.ir.is_some()
        || sess.opts.output_types.contains_key(&rustc_session::config::OutputType::TrustIr)
}

/// Scan the exact borrowed hook-time arena BEFORE ordinary lowering refusals.
/// An arena occurrence is a source fact, not a claim that the expression runs.
pub(crate) fn record(tcx: TyCtxt<'_>, owner: LocalDefId, thir: &Thir<'_>) {
    if !requested(tcx.sess) {
        return;
    }
    let mut body = CapturedBody { owner, uses: Vec::new(), scan_error: None };
    if thir.exprs.len() > MAX_BODY_EXPRS {
        body.scan_error = Some(format!(
            "source static readback exceeds scan budget of {MAX_BODY_EXPRS} expressions"
        ));
    } else {
        for (index, expression) in thir.exprs.iter_enumerated() {
            if let ExprKind::StaticRef { alloc_id, def_id, .. } = &expression.kind {
                if body.uses.len() == MAX_USES {
                    body.scan_error = Some(format!(
                        "source static readback exceeds budget of {MAX_USES} occurrences"
                    ));
                    break;
                }
                body.uses.push(StaticUse {
                    expr_index: index.index(),
                    definition: *def_id,
                    allocation: *alloc_id,
                    span: expression.span,
                });
            }
        }
    }
    tcx.sess.with_trust_compiler_state::<CaptureRegistry, _>(|state| state.insert(body));
}

/// Reserve actual allocation identities before reading children. This is also
/// the cycle/equal-bytes control surface used by rustc-free graph unit tests.
#[derive(Default)]
struct Graph {
    ids: FxHashMap<AllocId, u32>,
    allocations: Vec<AllocId>,
    nodes: BTreeMap<u32, ConstantImageNode>,
    bytes: usize,
    relocations: usize,
}

impl Graph {
    fn reserve(&mut self, allocation: AllocId) -> Result<u32, String> {
        if let Some(id) = self.ids.get(&allocation) {
            return Ok(*id);
        }
        if self.allocations.len() >= MAX_NODES {
            return Err(format!("source static readback exceeds budget of {MAX_NODES} nodes"));
        }
        let id = u32::try_from(self.allocations.len())
            .map_err(|_| "source static readback allocation ID overflow".to_string())?;
        self.allocations.push(allocation);
        self.ids.insert(allocation, id);
        Ok(id)
    }

    fn charge(&mut self, bytes: usize, relocations: usize) -> Result<(), String> {
        let bytes =
            self.bytes.checked_add(bytes).ok_or("source static readback byte budget overflow")?;
        let relocations = self
            .relocations
            .checked_add(relocations)
            .ok_or("source static readback relocation budget overflow")?;
        if bytes > MAX_BYTES {
            return Err(format!("source static readback exceeds budget of {MAX_BYTES} bytes"));
        }
        if relocations > MAX_RELOCATIONS {
            return Err(format!(
                "source static readback exceeds budget of {MAX_RELOCATIONS} relocations"
            ));
        }
        self.bytes = bytes;
        self.relocations = relocations;
        Ok(())
    }

    fn pointer(
        &mut self,
        provenance: CtfeProvenance,
        offset: Size,
    ) -> Result<ConstantImagePointer, String> {
        let (allocation, immutable, shared_ref) = provenance.into_parts();
        Ok(ConstantImagePointer {
            allocation_id: self.reserve(allocation)?,
            offset_bytes: offset.bytes(),
            immutable,
            shared_ref,
        })
    }

    fn memory(
        &mut self,
        tcx: TyCtxt<'_>,
        allocation: &Allocation,
    ) -> Result<ConstantImageMemory, String> {
        let pointers = allocation.provenance().ptrs();
        self.charge(allocation.len(), pointers.len())?;
        // Only INTERNED allocations reach this API: GlobalAlloc::Memory or an
        // eval_static_initializer result. None is never normalized to zero.
        let raw = allocation.inspect_with_uninit_and_ptr_outside_interpreter(0..allocation.len());
        let bytes = raw
            .iter()
            .enumerate()
            .map(|(index, byte)| {
                allocation.init_mask().get(Size::from_bytes(index)).then_some(*byte)
            })
            .collect();
        let pointer_size = tcx.data_layout.pointer_size();
        let mut previous_end = 0;
        let mut relocations = Vec::with_capacity(pointers.len());
        for &(offset, provenance) in pointers.iter() {
            let end = offset
                .bytes()
                .checked_add(pointer_size.bytes())
                .ok_or("source static readback relocation range overflow")?;
            if offset.bytes() < previous_end || end > allocation.size().bytes() {
                return Err("source static readback overlapping or out-of-bounds relocation".into());
            }
            previous_end = end;
            let scalar =
                allocation.read_scalar(&tcx, alloc_range(offset, pointer_size), true).map_err(
                    |error| format!("source static readback relocation read failed: {error:?}"),
                )?;
            let pointer = scalar.to_pointer(&tcx);
            let (read_provenance, target_offset) = pointer.into_raw_parts();
            if read_provenance != Some(provenance) {
                return Err("source static readback lost compiler pointer provenance".into());
            }
            relocations.push(ConstantImageRelocation {
                offset_bytes: offset.bytes(),
                pointer: self.pointer(provenance, target_offset)?,
            });
        }
        Ok(ConstantImageMemory {
            layout: ConstantImageLayout {
                size_bytes: allocation.size().bytes(),
                align_bytes: allocation.align.bytes(),
            },
            mutable: allocation.mutability.is_mut(),
            bytes,
            relocations,
        })
    }

    fn node(&mut self, tcx: TyCtxt<'_>, allocation: AllocId) -> Result<ConstantImageNode, String> {
        match tcx.try_get_global_alloc(allocation) {
            Some(GlobalAlloc::Memory(value)) => {
                self.memory(tcx, value.inner()).map(ConstantImageNode::Memory)
            }
            Some(GlobalAlloc::Static(did)) => {
                if tcx.is_foreign_item(did) || tcx.is_thread_local_static(did) {
                    return Err(
                        "source static readback foreign or thread-local static unsupported".into(),
                    );
                }
                let static_ty = static_type(tcx, did)?;
                let declared_mutable = tcx
                    .static_mutability(did)
                    .ok_or("source static readback static has no declared mutability")?
                    .is_mut();
                let freeze = crate::is_freeze_without_reveal(
                    tcx,
                    static_ty,
                    ty::TypingEnv::fully_monomorphized(),
                );
                let initializer = tcx.eval_static_initializer(did).map_err(|error| {
                    format!("source static readback initializer evaluation failed: {error:?}")
                })?;
                Ok(ConstantImageNode::Static {
                    definition: definition(tcx, did),
                    declared_mutable,
                    freeze,
                    thread_local: false,
                    foreign: false,
                    initializer: self.memory(tcx, initializer.inner())?,
                })
            }
            Some(GlobalAlloc::Function { instance }) => {
                // Generic identity helper only: no MIR body/operand producer.
                let callee_identity =
                    trust_mir_extract::instance_identity(tcx, instance.def_id(), instance.args)
                        .ok_or("source static readback function instance is not concrete")?;
                Ok(ConstantImageNode::Function {
                    definition: definition(tcx, instance.def_id()),
                    instance_fingerprint: instance_fingerprint(tcx, instance),
                    instance_debug: format!("{instance:?}"),
                    callee_identity,
                })
            }
            Some(GlobalAlloc::VTable(..)) => {
                Err("source static readback vtable unsupported".into())
            }
            Some(GlobalAlloc::TypeId { .. }) => {
                Err("source static readback type-ID unsupported".into())
            }
            None => Err("source static readback missing compiler allocation".into()),
        }
    }

    fn complete(&mut self, tcx: TyCtxt<'_>) -> Result<(), String> {
        let mut index = 0;
        // Reading a node reserves children but does not recursively evaluate
        // them. Self references and cycles keep the pre-reserved identity.
        while index < self.allocations.len() {
            let allocation = self.allocations[index];
            let node = self.node(tcx, allocation)?;
            self.nodes.insert(index as u32, node);
            index += 1;
        }
        self.validate()
    }

    fn validate(&self) -> Result<(), String> {
        if self.allocations.len() != self.nodes.len() || self.ids.len() != self.nodes.len() {
            return Err("source static readback incomplete allocation closure".into());
        }
        for (index, allocation) in self.allocations.iter().enumerate() {
            let id = index as u32;
            if self.ids.get(allocation) != Some(&id) {
                return Err("source static readback allocation identity ledger mismatch".into());
            }
            let node = self.nodes.get(&id).ok_or("source static readback orphan allocation ID")?;
            if let ConstantImageNode::Memory(memory)
            | ConstantImageNode::Static { initializer: memory, .. } = node
            {
                if memory.layout.size_bytes != memory.bytes.len() as u64
                    || !memory.layout.align_bytes.is_power_of_two()
                {
                    return Err("source static readback memory layout mismatch".into());
                }
                if memory
                    .relocations
                    .iter()
                    .any(|relocation| !self.nodes.contains_key(&relocation.pointer.allocation_id))
                {
                    return Err("source static readback orphan relocation target".into());
                }
            }
        }
        Ok(())
    }
}

fn definition(tcx: TyCtxt<'_>, did: DefId) -> ConstantImageDefinition {
    let hash = tcx.def_path_hash(did);
    ConstantImageDefinition {
        def_path: rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(did)),
        def_path_hash: CallableDefPathHash::new(
            hash.stable_crate_id().as_u64(),
            hash.local_hash().as_u64(),
        ),
    }
}

fn static_type<'tcx>(tcx: TyCtxt<'tcx>, did: DefId) -> Result<ty::Ty<'tcx>, String> {
    let ty = tcx
        .try_normalize_erasing_regions(
            ty::TypingEnv::fully_monomorphized(),
            tcx.type_of(did).instantiate_identity(),
        )
        .map_err(|error| format!("source static readback type normalization failed: {error:?}"))?;
    if ty.has_non_region_param()
        || ty.has_non_region_infer()
        || ty.has_non_region_placeholders()
        || ty.has_escaping_bound_vars()
    {
        return Err("source static readback static type is not concrete".into());
    }
    Ok(tcx.erase_and_anonymize_regions(ty))
}

fn type_fingerprint<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> [u64; 2] {
    let fingerprint: Fingerprint = tcx.with_stable_hashing_context(|mut hcx| {
        let mut hasher = StableHasher::new();
        hcx.while_hashing_spans(false, |hcx| ty.stable_hash(hcx, &mut hasher));
        hasher.finish()
    });
    let (lo, hi) = fingerprint.split();
    [lo.as_u64(), hi.as_u64()]
}

fn instance_fingerprint<'tcx>(tcx: TyCtxt<'tcx>, instance: ty::Instance<'tcx>) -> [u64; 2] {
    let erased = tcx.erase_and_anonymize_regions(instance);
    let fingerprint: Fingerprint = tcx.with_stable_hashing_context(|mut hcx| {
        let mut hasher = StableHasher::new();
        hcx.while_hashing_spans(false, |hcx| erased.stable_hash(hcx, &mut hasher));
        hasher.finish()
    });
    let (lo, hi) = fingerprint.split();
    [lo.as_u64(), hi.as_u64()]
}

fn quoted(text: &str) -> String {
    let mut out = String::from("\"");
    for ch in text.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            ch if ch < '\u{20}' => {
                let _ = write!(out, "\\u{:04x}", ch as u32);
            }
            ch => out.push(ch),
        }
    }
    out.push('"');
    out
}

fn definition_json(definition: &ConstantImageDefinition) -> String {
    format!(
        "{{\"def_path\":{},\"def_path_hash\":{{\"stable_crate_id\":\"{:016x}\",\"local_hash\":\"{:016x}\"}}}}",
        quoted(&definition.def_path),
        definition.def_path_hash.stable_crate_id(),
        definition.def_path_hash.local_hash()
    )
}

fn fingerprint_json(fingerprint: [u64; 2]) -> String {
    format!("[\"{:016x}\",\"{:016x}\"]", fingerprint[0], fingerprint[1])
}

fn source_json(tcx: TyCtxt<'_>, span: Span) -> Result<String, String> {
    if span.is_dummy() {
        return Err("source static readback source span is dummy".into());
    }
    let source_map = tcx.sess.source_map();
    let location = source_map.lookup_char_pos(span.lo());
    // Refuse absent compiler snapshots; never reopen a source file on disk.
    if location.file.src.is_none()
        || span.hi() > location.file.end_position()
        || span.hi().0.saturating_sub(span.lo().0) as usize > MAX_SOURCE_SNIPPET
    {
        return Err(
            "source static readback source snapshot unavailable or exceeds snippet budget".into()
        );
    }
    let snippet = source_map
        .span_to_snippet(span)
        .map_err(|error| format!("source static readback source snippet unavailable: {error:?}"))?;
    let digest = trust_ir::ProofDigest::sha256_domain(SOURCE_DIGEST_DOMAIN, snippet.as_bytes());
    let mut hex = String::with_capacity(64);
    for byte in digest.bytes {
        let _ = write!(hex, "{byte:02x}");
    }
    Ok(format!(
        "{{\"diagnostic\":{},\"file_hash\":{},\"snippet_digest\":\"sha256:{}\",\"snippet_digest_domain\":{}}}",
        quoted(&source_map.span_to_diagnostic_string(span)),
        quoted(&location.file.src_hash.to_string()),
        hex,
        quoted(SOURCE_DIGEST_DOMAIN)
    ))
}

fn memory_json(memory: &ConstantImageMemory) -> String {
    let bytes = memory
        .bytes
        .iter()
        .map(|byte| match byte {
            Some(byte) => byte.to_string(),
            None => "null".into(),
        })
        .collect::<Vec<_>>()
        .join(",");
    let relocations = memory.relocations.iter().map(|relocation| {
        let pointer = &relocation.pointer;
        format!("{{\"offset_bytes\":{},\"pointer\":{{\"allocation_id\":{},\"offset_bytes\":{},\"immutable\":{},\"shared_ref\":{}}}}}",
            relocation.offset_bytes, pointer.allocation_id, pointer.offset_bytes, pointer.immutable, pointer.shared_ref)
    }).collect::<Vec<_>>().join(",");
    format!(
        "{{\"layout\":{{\"size_bytes\":{},\"align_bytes\":{}}},\"mutable\":{},\"bytes\":[{}],\"relocations\":[{}]}}",
        memory.layout.size_bytes, memory.layout.align_bytes, memory.mutable, bytes, relocations
    )
}

fn node_json(id: u32, node: &ConstantImageNode) -> String {
    match node {
        ConstantImageNode::Memory(memory) => format!(
            "{{\"allocation_id\":{id},\"kind\":\"memory\",\"memory\":{}}}",
            memory_json(memory)
        ),
        ConstantImageNode::Static {
            definition,
            declared_mutable,
            freeze,
            thread_local,
            foreign,
            initializer,
        } => {
            format!(
                "{{\"allocation_id\":{id},\"kind\":\"static\",\"definition\":{},\"declared_mutable\":{declared_mutable},\"freeze\":{freeze},\"thread_local\":{thread_local},\"foreign\":{foreign},\"initializer\":{}}}",
                definition_json(definition),
                memory_json(initializer)
            )
        }
        ConstantImageNode::Function {
            definition,
            instance_fingerprint,
            instance_debug,
            callee_identity,
        } => {
            format!(
                "{{\"allocation_id\":{id},\"kind\":\"function\",\"definition\":{},\"instance_fingerprint\":{},\"instance_debug\":{},\"callee_identity\":{{\"stable_crate_id\":\"{:016x}\",\"def_index\":{},\"substs_digest\":{}}}}}",
                definition_json(definition),
                fingerprint_json(*instance_fingerprint),
                quoted(instance_debug),
                callee_identity.stable_crate_id,
                callee_identity.def_index,
                fingerprint_json(callee_identity.substs_digest)
            )
        }
    }
}

fn graph_json(roots: &[String], graph: &Graph, errors: &BTreeSet<String>) -> String {
    let mut errors = errors.clone();
    if errors.is_empty() {
        if let Err(error) = graph.validate() {
            errors.insert(error);
        }
    }
    let complete = errors.is_empty();
    let nodes = if complete {
        graph.nodes.iter().map(|(id, node)| node_json(*id, node)).collect::<Vec<_>>().join(",")
    } else {
        String::new()
    };
    let roots = if complete { roots.join(",") } else { String::new() };
    let errors = errors.iter().map(|error| quoted(error)).collect::<Vec<_>>().join(",");
    let status = if complete { "complete" } else { "refused" };
    // Never publish orphan IDs or partially captured storage after a failure.
    format!(
        "{{\"capture_status\":\"{status}\",\"errors\":[{errors}],\"statics\":[{roots}],\"nodes\":[{nodes}]}}"
    )
}

fn body_json(
    tcx: TyCtxt<'_>,
    index: u32,
    body: &CapturedBody,
    attempt_errors: &BTreeSet<String>,
) -> (String, bool) {
    let mut errors = attempt_errors.clone();
    if let Some(error) = &body.scan_error {
        errors.insert(error.clone());
    }
    let mut observe_source = |span| match source_json(tcx, span) {
        Ok(source) => source,
        Err(error) => {
            errors.insert(error);
            "null".into()
        }
    };
    let source =
        if body.uses.is_empty() { "null".into() } else { observe_source(tcx.def_span(body.owner)) };
    // Render the full observed source roster FIRST. Graph budget/evaluation
    // failures cannot hide a later use or erase the owner from the denominator.
    let uses = body
        .uses
        .iter()
        .map(|usage| {
            format!(
                "{{\"expr_index\":{},\"static_definition\":{},\"source\":{}}}",
                usage.expr_index,
                definition_json(&definition(tcx, usage.definition)),
                observe_source(usage.span)
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let mut roots = Vec::new();
    let mut graph = Graph::default();
    let mut seen = FxHashSet::default();
    // Arena expression order then relocation offset order determine this ONE
    // body's namespace. Other bodies/large statics cannot exhaust its budget.
    let result = (|| -> Result<(), String> {
        if !errors.is_empty() || body.uses.is_empty() {
            return Ok(());
        }
        if trust_mir_extract::ctfe_reentrancy::frozen() {
            return Err("source static readback requires post-analysis CTFE seam".into());
        }
        for usage in &body.uses {
            if !matches!(tcx.try_get_global_alloc(usage.allocation), Some(GlobalAlloc::Static(did)) if did == usage.definition)
            {
                return Err(
                    "source static readback THIR allocation/static definition mismatch".into()
                );
            }
            if seen.insert(usage.definition) {
                let ty = static_type(tcx, usage.definition)?;
                roots.push(format!("{{\"definition\":{},\"allocation_id\":{},\"type_fingerprint\":{},\"type_debug\":{}}}",
                    definition_json(&definition(tcx, usage.definition)), graph.reserve(usage.allocation)?,
                    fingerprint_json(type_fingerprint(tcx, ty)), quoted(&format!("{ty:?}"))));
            }
        }
        graph.complete(tcx)
    })();
    if let Err(error) = result {
        errors.insert(error);
    }
    let complete = errors.is_empty();
    (
        format!(
            "{{\"owner\":{},\"def_index\":{index},\"source\":{source},\"uses\":[{uses}],\"graph\":{}}}",
            definition_json(&definition(tcx, body.owner.to_def_id())),
            graph_json(&roots, &graph, &errors)
        ),
        complete,
    )
}

/// Take Session storage before any query. Required body analyses must already
/// be complete. Each owner's bounded closure is independent; one refused large
/// initializer cannot hide the actual literal helper's successful cold graph.
/// Neither successful nor refused diagnostics alter admissions/proof grades.
pub(crate) fn finalize(tcx: TyCtxt<'_>) -> Option<String> {
    let mut registry = tcx.sess.with_trust_compiler_state::<CaptureRegistry, _>(std::mem::take);
    if !requested(tcx.sess) {
        return None;
    }
    registry
        .check_inventory(&tcx.hir_body_owners().map(|def| def.local_def_index.as_u32()).collect());
    let target = ConstantImageTarget {
        triple: tcx.sess.opts.target_triple.to_string(),
        data_layout: tcx.sess.target.data_layout.to_string(),
        pointer_size_bytes: tcx.data_layout.pointer_size().bytes(),
        little_endian: tcx.data_layout.endian == Endian::Little,
    };
    let mut complete_bodies = 0;
    let bodies = registry
        .bodies
        .iter()
        .map(|(index, body)| {
            let (body, complete) = body_json(tcx, *index, body, &registry.errors);
            complete_bodies += usize::from(complete);
            body
        })
        .collect::<Vec<_>>()
        .join(",");
    let body_count = registry.bodies.len();
    let refused_bodies = body_count - complete_bodies;
    let inventory_complete = registry.errors.is_empty();
    let status = if !inventory_complete || (refused_bodies != 0 && complete_bodies == 0) {
        "refused"
    } else if refused_bodies != 0 {
        "partial"
    } else {
        "complete"
    };
    let errors = registry.errors.iter().map(|error| quoted(error)).collect::<Vec<_>>().join(",");
    Some(format!(
        "{{\"schema\":\"trust.thir.source-static-readback.v1\",\"producer\":\"thir_static_ref\",\"storage_phase\":\"cold_initializer_only\",\"evaluator_dependency\":\"rustc_ctfe\",\"proof_authority\":false,\"native_verification_requests\":false,\"allocation_namespace\":\"per_body\",\"capture_status\":\"{status}\",\"inventory_complete\":{inventory_complete},\"body_count\":{body_count},\"complete_bodies\":{complete_bodies},\"refused_bodies\":{refused_bodies},\"errors\":[{errors}],\"limits\":{{\"nodes\":{MAX_NODES},\"bytes\":{MAX_BYTES},\"relocations\":{MAX_RELOCATIONS},\"body_expressions\":{MAX_BODY_EXPRS},\"body_occurrences\":{MAX_USES},\"bodies\":{MAX_BODIES},\"source_snippet_bytes\":{MAX_SOURCE_SNIPPET}}},\"target\":{{\"triple\":{},\"data_layout\":{},\"pointer_size_bytes\":{},\"little_endian\":{}}},\"bodies\":[{bodies}]}}",
        quoted(&target.triple),
        quoted(&target.data_layout),
        target.pointer_size_bytes,
        target.little_endian,
    ))
}

pub(crate) fn append_to_coverage(
    coverage: String,
    readback: Option<&str>,
) -> Result<String, String> {
    let Some(readback) = readback else {
        return Ok(coverage);
    };
    let prefix = coverage
        .strip_suffix("}\n")
        .ok_or("source static readback coverage lacks canonical closing delimiter")?;
    Ok(format!(
        "{},\n  \"source_static_readback\": {readback}\n}}\n",
        prefix.trim_end_matches('\n')
    ))
}

#[cfg(test)]
mod tests;

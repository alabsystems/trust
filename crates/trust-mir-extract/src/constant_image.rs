// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Bounded diagnostic capture of already evaluated MIR constant storage.
//!
//! This is not a constant evaluator or a value/provenance proof. In particular,
//! a static's initializer is recorded separately from its identity and is never
//! asserted to describe its current runtime contents.

use std::cell::RefCell;
use std::collections::{BTreeMap, VecDeque};
use std::marker::PhantomData;
use std::rc::Rc;

use rustc_abi::{Endian, Size};
use rustc_data_structures::fingerprint::Fingerprint;
use rustc_data_structures::stable_hash::{StableHash, StableHasher};
use rustc_middle::mir;
use rustc_middle::mir::interpret::{AllocId, Allocation, CtfeProvenance, GlobalAlloc, alloc_range};
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use rustc_span::def_id::DefId;
use trust_types::fx::FxHashMap;
use trust_types::{
    CallableDefPathHash, ConstantImageDefinition, ConstantImageLayout, ConstantImageMemory,
    ConstantImageNode, ConstantImageOwner, ConstantImagePointer, ConstantImageRelocation,
    ConstantImageRoot, ConstantImageTarget, ConstantMemoryImage,
};

const MAX_NODES: usize = 64;
const MAX_BYTES: usize = 64 * 1024;
const MAX_RELOCATIONS: usize = 1024;

struct ImageState {
    owner_did: DefId,
    owner_phase: mir::MirPhase,
    owner: Option<ConstantImageOwner>,
    target: Option<ConstantImageTarget>,
    ids: FxHashMap<AllocId, u32>,
    allocations: Vec<AllocId>,
    nodes: BTreeMap<u32, ConstantImageNode>,
    bytes: usize,
    relocations: usize,
    failure: Option<String>,
}

thread_local! {
    static IMAGE_STATE: RefCell<Option<ImageState>> = const { RefCell::new(None) };
}

/// One body's allocation identity namespace. Nested extraction restores the
/// outer namespace rather than clearing or renumbering its allocations.
pub(crate) struct MemoryImageScope {
    previous: Option<ImageState>,
    // A TLS guard must be dropped on the thread that opened it.
    _thread: PhantomData<Rc<()>>,
}

impl MemoryImageScope {
    pub(crate) fn begin(_tcx: TyCtxt<'_>, body: &mir::Body<'_>) -> Self {
        let state = ImageState {
            owner_did: body.source.def_id(),
            owner_phase: body.phase,
            owner: None,
            target: None,
            ids: FxHashMap::default(),
            allocations: Vec::new(),
            nodes: BTreeMap::new(),
            bytes: 0,
            relocations: 0,
            failure: None,
        };
        let previous = IMAGE_STATE.with(|slot| slot.replace(Some(state)));
        Self { previous, _thread: PhantomData }
    }
}

impl Drop for MemoryImageScope {
    fn drop(&mut self) {
        IMAGE_STATE.with(|slot| {
            slot.replace(self.previous.take());
        });
    }
}

/// Do not hold a RefCell borrow across rustc queries: a query may itself enter a
/// nested body extraction. The state is returned even when unwinding. A direct
/// reentrant image extraction without its own body scope refuses instead.
struct StateLease {
    state: Option<ImageState>,
}

impl Drop for StateLease {
    fn drop(&mut self) {
        IMAGE_STATE.with(|slot| {
            slot.replace(self.state.take());
        });
    }
}

fn definition_hash(tcx: TyCtxt<'_>, did: DefId) -> CallableDefPathHash {
    let hash = tcx.def_path_hash(did);
    CallableDefPathHash::new(hash.stable_crate_id().as_u64(), hash.local_hash().as_u64())
}

pub(crate) fn definition(tcx: TyCtxt<'_>, did: DefId) -> ConstantImageDefinition {
    ConstantImageDefinition {
        def_path: crate::safe_def_path_str(tcx, did),
        def_path_hash: definition_hash(tcx, did),
    }
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

pub(crate) fn instance_fingerprint<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
) -> [u64; 2] {
    let erased = tcx.erase_and_anonymize_regions(instance);
    let fingerprint: Fingerprint = tcx.with_stable_hashing_context(|mut hcx| {
        let mut hasher = StableHasher::new();
        hcx.while_hashing_spans(false, |hcx| erased.stable_hash(hcx, &mut hasher));
        hasher.finish()
    });
    let (lo, hi) = fingerprint.split();
    [lo.as_u64(), hi.as_u64()]
}

/// Snapshot only while the owning body's scope is still open. Allocation
/// positions are exactly the IDs used by that extraction's image records.
/// Discovery must still intersect this list with successfully emitted images:
/// a failed image may have reserved allocations before its refusal latched.
pub(crate) fn captured_allocations() -> Vec<AllocId> {
    IMAGE_STATE.with(|slot| {
        slot.borrow().as_ref().map(|state| state.allocations.clone()).unwrap_or_default()
    })
}

impl ImageState {
    fn reserve(&mut self, allocation: AllocId) -> Result<u32, String> {
        if let Some(id) = self.ids.get(&allocation) {
            return Ok(*id);
        }
        if self.allocations.len() >= MAX_NODES {
            return Err(format!("constant memory image exceeds body budget of {MAX_NODES} nodes"));
        }
        let id = u32::try_from(self.allocations.len())
            .map_err(|_| "constant memory image allocation ID overflow".to_string())?;
        // Reserve BEFORE traversing children, including self-referential statics.
        // Equal byte contents never merge two compiler allocation identities.
        self.allocations.push(allocation);
        self.ids.insert(allocation, id);
        Ok(id)
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
        let new_bytes = self
            .bytes
            .checked_add(allocation.len())
            .ok_or_else(|| "constant memory image byte budget overflow".to_string())?;
        if new_bytes > MAX_BYTES {
            return Err(format!("constant memory image exceeds body budget of {MAX_BYTES} bytes"));
        }
        // This API is valid for INTERNED allocations only. Callers supply either
        // GlobalAlloc::Memory or eval_static_initializer's ConstAllocation.
        let pointers = allocation.provenance().ptrs();
        let new_relocations = self
            .relocations
            .checked_add(pointers.len())
            .ok_or_else(|| "constant memory image relocation budget overflow".to_string())?;
        if new_relocations > MAX_RELOCATIONS {
            return Err(format!(
                "constant memory image exceeds body budget of {MAX_RELOCATIONS} relocations"
            ));
        }
        self.bytes = new_bytes;
        self.relocations = new_relocations;

        let raw = allocation.inspect_with_uninit_and_ptr_outside_interpreter(0..allocation.len());
        let bytes = raw
            .iter()
            .enumerate()
            .map(|(index, byte)| {
                allocation.init_mask().get(Size::from_bytes(index)).then_some(*byte)
            })
            .collect();
        let pointer_size = tcx.data_layout.pointer_size();
        let mut relocations = Vec::with_capacity(pointers.len());
        let mut previous_end = 0_u64;
        // rustc's SortedMap iterates in offset order, making traversal and ID
        // assignment deterministic without sorting unstable compiler AllocIds.
        for &(offset, provenance) in pointers.iter() {
            let end = offset
                .bytes()
                .checked_add(pointer_size.bytes())
                .ok_or_else(|| "constant memory image relocation range overflow".to_string())?;
            if offset.bytes() < previous_end || end > allocation.size().bytes() {
                return Err(
                    "constant memory image has overlapping or out-of-bounds relocation".into()
                );
            }
            previous_end = end;
            let scalar =
                allocation.read_scalar(&tcx, alloc_range(offset, pointer_size), true).map_err(
                    |error| format!("constant memory image relocation read failed: {error:?}"),
                )?;
            let pointer = scalar.to_pointer(&tcx);
            let (read_provenance, target_offset) = pointer.into_raw_parts();
            if read_provenance != Some(provenance) {
                return Err("constant memory image relocation lost compiler provenance".into());
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

    fn node<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        allocation: AllocId,
    ) -> Result<ConstantImageNode, String> {
        match tcx.try_get_global_alloc(allocation) {
            Some(GlobalAlloc::Memory(value)) => {
                self.memory(tcx, value.inner()).map(ConstantImageNode::Memory)
            }
            Some(GlobalAlloc::Static(did)) => {
                if crate::ctfe_reentrancy::frozen() {
                    return Err(
                        "constant memory image static initializer requires CTFE while frozen"
                            .into(),
                    );
                }
                if tcx.is_foreign_item(did) || tcx.is_thread_local_static(did) {
                    return Err(
                        "constant memory image does not support foreign or thread-local statics"
                            .into(),
                    );
                }
                let static_ty = tcx
                    .try_normalize_erasing_regions(
                        ty::TypingEnv::fully_monomorphized(),
                        tcx.type_of(did).instantiate_identity(),
                    )
                    .map_err(|error| {
                        format!("constant memory image static type normalization failed: {error:?}")
                    })?;
                if static_ty.has_non_region_param()
                    || static_ty.has_non_region_infer()
                    || static_ty.has_non_region_placeholders()
                {
                    return Err("constant memory image static type is not concrete".into());
                }
                let declared_mutable = tcx
                    .static_mutability(did)
                    .ok_or_else(|| {
                        "constant memory image static has no declared mutability".to_string()
                    })?
                    .is_mut();
                let freeze = static_ty.is_freeze(tcx, ty::TypingEnv::fully_monomorphized());
                let initializer = tcx.eval_static_initializer(did).map_err(|error| {
                    format!("constant memory image static initializer evaluation failed: {error:?}")
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
                let callee_identity =
                    crate::convert::callee_identity_for(tcx, instance.def_id(), instance.args)
                        .ok_or_else(|| {
                            "constant memory image function instance is not concrete".to_string()
                        })?;
                Ok(ConstantImageNode::Function {
                    definition: definition(tcx, instance.def_id()),
                    instance_fingerprint: instance_fingerprint(tcx, instance),
                    instance_debug: format!("{instance:?}"),
                    callee_identity,
                })
            }
            Some(GlobalAlloc::VTable(..)) => {
                Err("constant memory image vtable allocation is unsupported".into())
            }
            Some(GlobalAlloc::TypeId { .. }) => {
                Err("constant memory image type-ID allocation is unsupported".into())
            }
            None => Err("constant memory image refers to a missing compiler allocation".into()),
        }
    }

    fn reachable_nodes(
        &mut self,
        tcx: TyCtxt<'_>,
        root: &ConstantImageRoot,
    ) -> Result<BTreeMap<u32, ConstantImageNode>, String> {
        let mut pending = VecDeque::new();
        match root {
            ConstantImageRoot::Pointer(pointer) => pending.push_back(pointer.allocation_id),
            ConstantImageRoot::Indirect { allocation_id, .. }
            | ConstantImageRoot::Slice { allocation_id, .. } => pending.push_back(*allocation_id),
            ConstantImageRoot::ScalarBits { .. } | ConstantImageRoot::ZeroSized => {}
        }
        let mut nodes = BTreeMap::new();
        while let Some(id) = pending.pop_front() {
            if nodes.contains_key(&id) {
                continue;
            }
            let allocation = *self.allocations.get(id as usize).ok_or_else(|| {
                "constant memory image has an unreserved allocation ID".to_string()
            })?;
            let node = if let Some(cached) = self.nodes.get(&id) {
                if crate::ctfe_reentrancy::frozen()
                    && matches!(cached, ConstantImageNode::Static { .. })
                {
                    return Err(
                        "constant memory image static initializer requires CTFE while frozen"
                            .into(),
                    );
                }
                cached.clone()
            } else {
                let node = self.node(tcx, allocation)?;
                self.nodes.insert(id, node.clone());
                node
            };
            let memory = match &node {
                ConstantImageNode::Memory(memory)
                | ConstantImageNode::Static { initializer: memory, .. } => Some(memory),
                ConstantImageNode::Function { .. } => None,
            };
            if let Some(memory) = memory {
                pending.extend(memory.relocations.iter().map(|r| r.pointer.allocation_id));
            }
            nodes.insert(id, node);
        }
        Ok(nodes)
    }
}

pub(crate) fn extract_memory_image<'tcx>(
    tcx: TyCtxt<'tcx>,
    constant: &mir::ConstOperand<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
) -> Result<ConstantMemoryImage, String> {
    if !crate::ty_convert::faithful_scalars() {
        return Err("constant memory images require faithful extraction mode".into());
    }
    let mir::Const::Val(value, original_ty) = constant.const_ else {
        return Err("constant memory image requires an already evaluated Const::Val".into());
    };
    let original_ty = tcx.erase_and_anonymize_regions(original_ty);
    if original_ty.has_non_region_param()
        || original_ty.has_non_region_infer()
        || original_ty.has_non_region_placeholders()
        || original_ty.has_escaping_bound_vars()
    {
        return Err("constant memory image requires a fully concrete Rust type".into());
    }
    let state = IMAGE_STATE.with(|slot| slot.borrow_mut().take());
    let mut lease = StateLease { state };
    let state = lease
        .state
        .as_mut()
        .ok_or_else(|| "constant memory image has no active body allocation scope".to_string())?;
    if let Some(failure) = &state.failure {
        return Err(format!("constant memory image body scope previously refused: {failure}"));
    }
    let result: Result<ConstantMemoryImage, String> = (|| {
        let compiler_layout =
            crate::tuple_layouts::extractor_layout_of(tcx, typing_env, original_ty).ok_or_else(
                || format!("constant memory image type layout unavailable for `{original_ty}`"),
            )?;
        if !compiler_layout.is_sized() {
            return Err("constant memory image root has unsized layout".into());
        }
        let layout = ConstantImageLayout {
            size_bytes: compiler_layout.size.bytes(),
            align_bytes: compiler_layout.align.bytes(),
        };
        let root = match value {
            mir::ConstValue::Scalar(scalar) => {
                if scalar.size().bytes() != layout.size_bytes {
                    return Err("constant memory image scalar size differs from Rust layout".into());
                }
                match scalar.try_to_scalar_int() {
                    Ok(integer) => ConstantImageRoot::ScalarBits {
                        bits: integer.to_bits(integer.size()),
                        size_bytes: integer.size().bytes(),
                    },
                    Err(_) => {
                        let pointer = scalar.to_pointer(&tcx);
                        let (provenance, offset) = pointer.into_raw_parts();
                        let provenance = provenance.ok_or_else(|| {
                            "constant memory image pointer unexpectedly lost provenance".to_string()
                        })?;
                        ConstantImageRoot::Pointer(state.pointer(provenance, offset)?)
                    }
                }
            }
            mir::ConstValue::Indirect { alloc_id, offset } => ConstantImageRoot::Indirect {
                allocation_id: state.reserve(alloc_id)?,
                offset_bytes: offset.bytes(),
            },
            mir::ConstValue::Slice { alloc_id, meta } => {
                ConstantImageRoot::Slice { allocation_id: state.reserve(alloc_id)?, metadata: meta }
            }
            mir::ConstValue::ZeroSized => {
                if layout.size_bytes != 0 {
                    return Err("constant memory image zero-sized root has nonzero layout".into());
                }
                ConstantImageRoot::ZeroSized
            }
        };
        let nodes = state.reachable_nodes(tcx, &root)?;
        if let ConstantImageRoot::Indirect { allocation_id, offset_bytes } = &root {
            let Some(ConstantImageNode::Memory(memory)) = nodes.get(allocation_id) else {
                return Err(
                    "constant memory image indirect root is not an ordinary memory allocation"
                        .into(),
                );
            };
            let end = offset_bytes
                .checked_add(layout.size_bytes)
                .ok_or_else(|| "constant memory image indirect root range overflow".to_string())?;
            if end > memory.layout.size_bytes
                || memory.layout.align_bytes < layout.align_bytes
                || offset_bytes % layout.align_bytes != 0
            {
                return Err(
                    "constant memory image indirect root exceeds allocation bounds or alignment"
                        .into(),
                );
            }
        }
        let owner_did = state.owner_did;
        let owner_phase = state.owner_phase;
        let owner = state
            .owner
            .get_or_insert_with(|| ConstantImageOwner {
                def_path: crate::safe_def_path_str(tcx, owner_did),
                def_path_hash: definition_hash(tcx, owner_did),
                mir_phase: format!("{owner_phase:?}"),
            })
            .clone();
        let target = state
            .target
            .get_or_insert_with(|| ConstantImageTarget {
                triple: tcx.sess.opts.target_triple.to_string(),
                data_layout: tcx.sess.target.data_layout.to_string(),
                pointer_size_bytes: tcx.data_layout.pointer_size().bytes(),
                little_endian: tcx.data_layout.endian == Endian::Little,
            })
            .clone();
        Ok(ConstantMemoryImage {
            schema_version: 1,
            owner,
            target,
            ty: crate::ty_convert::convert_ty_in_env(tcx, typing_env, original_ty),
            ty_fingerprint: type_fingerprint(tcx, original_ty),
            layout,
            root,
            nodes,
        })
    })();
    if let Err(error) = &result {
        // A partial traversal may have reserved IDs or consumed a budget. Keep
        // the whole scope refused instead of retrying against partial evidence.
        state.failure = Some(error.clone());
    }
    result
}

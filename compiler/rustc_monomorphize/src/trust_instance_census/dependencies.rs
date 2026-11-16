//! Trust: render only the typed observations retained by existing collector
//! visits. This module never evaluates constants or asks for vtable allocations.

use std::collections::{BTreeMap, BTreeSet};

use rustc_data_structures::fingerprint::Fingerprint;
use rustc_data_structures::stable_hash::{StableHash, StableHasher};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::interpret::{AllocId, ConstAllocation};
use rustc_middle::mono::{
    CollectionMode, MonoItem, TrustAllocation, TrustAllocationForm, TrustAllocationSource,
    TrustDependencyKind, TrustDependencyOrigin, TrustDependencySite, TrustVtableEntry,
};
use rustc_middle::ty::{Ty, TyCtxt};
use serde_json::{Value, json};

use super::{identity, instance_kind};
use crate::collector::UsageMap;

pub(super) struct Snapshot {
    pub nodes: Vec<Value>,
    pub owners: Vec<Value>,
    pub occurrences: Vec<Value>,
    pub eager_const_owners: Vec<Value>,
    pub eager_const_occurrences: Vec<Value>,
}

// Compare full typed identities as well as their diagnostic hash spelling.
// In particular, equal allocation contents must not merge distinct AllocIds.
#[derive(Clone, Copy, PartialEq, Eq)]
enum NodeIdentity<'tcx> {
    Item(MonoItem<'tcx>),
    Allocation(AllocId),
    Initializer(DefId),
    Vtable(Ty<'tcx>, Ty<'tcx>),
}

struct Nodes<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    collected: &'a BTreeSet<String>,
    rows: BTreeMap<String, (NodeIdentity<'tcx>, Value)>,
}

fn allocation_id(id: AllocId) -> String {
    format!("alloc:{}", id.0.get())
}

fn initializer_id(tcx: TyCtxt<'_>, def: DefId) -> String {
    format!("initializer:{}", identity(tcx, MonoItem::Static(def)))
}

fn vtable_id(tcx: TyCtxt<'_>, impl_ty: Ty<'_>, trait_ty: Ty<'_>) -> String {
    tcx.with_stable_hashing_context(|mut hcx| {
        let mut hasher = StableHasher::new();
        (impl_ty, trait_ty).stable_hash(&mut hcx, &mut hasher);
        let fingerprint: Fingerprint = hasher.finish();
        let hex: String =
            fingerprint.to_le_bytes().iter().map(|byte| format!("{byte:02x}")).collect();
        format!("vtable:{hex}")
    })
}

fn mode(mode: CollectionMode) -> &'static str {
    match mode {
        CollectionMode::UsedItems => "used",
        CollectionMode::MentionedItems => "mentioned",
    }
}

fn origin(origin: TrustDependencyOrigin) -> &'static str {
    match origin {
        TrustDependencyOrigin::Mir => "mir",
        TrustDependencyOrigin::DebugInfo => "debug-info",
        TrustDependencyOrigin::RequiredConst => "required-const",
        TrustDependencyOrigin::MentionedItem => "mentioned-item",
        TrustDependencyOrigin::Static => "static",
        TrustDependencyOrigin::GlobalAsm => "global-asm",
        TrustDependencyOrigin::EagerConstRoot => "eager-const-root",
    }
}

fn site(site: TrustDependencySite) -> &'static str {
    match site {
        TrustDependencySite::InstanceUse => "instance-use",
        TrustDependencySite::Closure => "closure",
        TrustDependencySite::ThreadLocalStatic => "thread-local-static",
        TrustDependencySite::LanguageItem => "language-item",
        TrustDependencySite::AsmStatic => "asm-static",
        TrustDependencySite::IntrinsicPanic => "intrinsic-panic",
        TrustDependencySite::IntrinsicFallback => "intrinsic-fallback",
        TrustDependencySite::VtableMethod => "vtable-method",
        TrustDependencySite::AllocationStatic => "allocation-static",
        TrustDependencySite::AllocationFunction => "allocation-function",
        TrustDependencySite::ThreadLocalShim => "thread-local-shim",
    }
}

fn memory_fields(row: &mut Value, allocation: ConstAllocation<'_>) {
    let allocation = allocation.inner();
    row["size_bytes"] = json!(allocation.size().bytes());
    row["align_bytes"] = json!(allocation.align.bytes());
    row["mutable"] = json!(allocation.mutability.is_mut());
}

impl<'a, 'tcx> Nodes<'a, 'tcx> {
    fn insert(&mut self, id: String, key: NodeIdentity<'tcx>, mut row: Value) -> String {
        row["id"] = json!(id);
        if let Some((previous_key, previous_row)) = self.rows.get(&id) {
            if *previous_key != key || *previous_row != row {
                self.tcx.dcx().fatal("Rust instance census: conflicting dependency node identity");
            }
        } else {
            self.rows.insert(id.clone(), (key, row));
        }
        id
    }

    fn item(&mut self, item: MonoItem<'tcx>) -> String {
        let raw_id = identity(self.tcx, item);
        let def = item.def_id();
        let (kind, detail, args) = match item {
            MonoItem::Fn(instance) => (
                instance_kind(instance.def),
                format!("{:?}", instance.def),
                format!("{:?}", instance.args),
            ),
            MonoItem::Static(_) => ("static", String::new(), String::new()),
            MonoItem::GlobalAsm(_) => ("global-asm", String::new(), String::new()),
        };
        self.insert(
            format!("item:{raw_id}"),
            NodeIdentity::Item(item),
            json!({
                "kind": "item", "mono_item_kind": kind,
                "instance_detail": detail, "generic_args": args,
                "def": self.tcx.def_path_debug_str(def),
                "def_path_hash": format!("{:?}", self.tcx.def_path_hash(def)),
                "def_kind": format!("{:?}", self.tcx.def_kind(def)),
                "definition_is_local": def.is_local(),
                "collected": self.collected.contains(&raw_id),
            }),
        )
    }

    fn allocation(&mut self, id: AllocId, allocation: TrustAllocation<'tcx>) -> String {
        let row = match allocation {
            TrustAllocation::Memory(allocation) => {
                let mut row = json!({"kind": "memory-allocation"});
                memory_fields(&mut row, allocation);
                row
            }
            TrustAllocation::Function(instance) => {
                let target = self.item(MonoItem::Fn(instance));
                json!({"kind": "function-allocation", "target": target})
            }
            TrustAllocation::Static(def) => {
                let target = self.item(MonoItem::Static(def));
                json!({"kind": "static-allocation", "target": target})
            }
            TrustAllocation::Vtable(ty, dyn_ty) => json!({
                "kind": "vtable-allocation", "impl_ty": format!("{ty:?}"),
                "trait_type": format!("{dyn_ty:?}"),
            }),
            TrustAllocation::TypeId(ty) => {
                json!({"kind": "type-id-allocation", "ty": format!("{ty:?}")})
            }
        };
        self.insert(allocation_id(id), NodeIdentity::Allocation(id), row)
    }

    fn initializer(&mut self, def: DefId, allocation: ConstAllocation<'tcx>) -> String {
        let target = self.item(MonoItem::Static(def));
        let mut row = json!({"kind": "static-initializer", "static": target});
        memory_fields(&mut row, allocation);
        self.insert(initializer_id(self.tcx, def), NodeIdentity::Initializer(def), row)
    }

    fn vtable(&mut self, impl_ty: Ty<'tcx>, trait_ty: Ty<'tcx>) -> String {
        self.insert(
            vtable_id(self.tcx, impl_ty, trait_ty),
            NodeIdentity::Vtable(impl_ty, trait_ty),
            json!({"kind": "vtable", "impl_ty": format!("{impl_ty:?}"), "trait_type": format!("{trait_ty:?}")}),
        )
    }

    fn occurrence(&mut self, kind: TrustDependencyKind<'tcx>) -> Value {
        match kind {
            TrustDependencyKind::InstanceUse {
                target,
                site: at,
                collector_direct_call,
                local_codegen,
            } => {
                let target = self.item(target);
                json!({"kind": "instance-use", "target": target, "site": site(at),
                    "collector_direct_call": collector_direct_call, "local_codegen": local_codegen})
            }
            TrustDependencyKind::Allocation { id, allocation } => {
                let target = self.allocation(id, allocation);
                json!({"kind": "allocation", "target": target})
            }
            TrustDependencyKind::AllocationRoot {
                id,
                offset_bytes,
                form,
                metadata,
                immutable,
                shared_ref,
            } => {
                let form = match form {
                    TrustAllocationForm::Pointer => "pointer",
                    TrustAllocationForm::Indirect => "indirect",
                    TrustAllocationForm::Slice => "slice",
                };
                json!({"kind": "allocation-root", "target": allocation_id(id), "form": form,
                    "offset_bytes": offset_bytes, "metadata": metadata,
                    "immutable": immutable, "shared_ref": shared_ref})
            }
            TrustDependencyKind::StaticInitializer { def_id, allocation } => {
                let target = self.initializer(def_id, allocation);
                json!({"kind": "static-initializer", "target": target})
            }
            TrustDependencyKind::Relocation {
                source,
                target,
                offset_bytes,
                immutable,
                shared_ref,
            } => {
                let source = match source {
                    TrustAllocationSource::Allocation(id) => allocation_id(id),
                    TrustAllocationSource::StaticInitializer(def) => initializer_id(self.tcx, def),
                };
                json!({"kind": "relocation", "source": source, "target": allocation_id(target),
                    "offset_bytes": offset_bytes, "immutable": immutable, "shared_ref": shared_ref})
            }
            TrustDependencyKind::Vtable { impl_ty, trait_ty, entry_count } => {
                let target = self.vtable(impl_ty, trait_ty);
                json!({"kind": "vtable", "target": target, "entry_count": entry_count})
            }
            TrustDependencyKind::VtableEntry { impl_ty, trait_ty, slot, entry, local_codegen } => {
                let source = vtable_id(self.tcx, impl_ty, trait_ty);
                let (kind, target, trait_ref) = match entry {
                    TrustVtableEntry::DropInPlace => ("drop-in-place", None, None),
                    TrustVtableEntry::Size => ("size", None, None),
                    TrustVtableEntry::Align => ("align", None, None),
                    TrustVtableEntry::Vacant => ("vacant", None, None),
                    TrustVtableEntry::Method(instance) => {
                        ("method", Some(self.item(MonoItem::Fn(instance))), None)
                    }
                    TrustVtableEntry::TraitVPtr(trait_ref) => {
                        ("trait-vptr", None, Some(format!("{trait_ref:?}")))
                    }
                };
                json!({"kind": "vtable-entry", "source": source, "slot": slot,
                    "entry_kind": kind, "target": target, "trait_ref": trait_ref,
                    "local_codegen": local_codegen})
            }
            TrustDependencyKind::VtableMaterialization { source, target } => {
                json!({"kind": "vtable-materialization", "source": allocation_id(source), "target": allocation_id(target)})
            }
        }
    }
}

pub(super) fn snapshot<'tcx>(
    tcx: TyCtxt<'tcx>,
    items: &[MonoItem<'tcx>],
    usage: &UsageMap<'tcx>,
) -> Snapshot {
    let collected = items.iter().map(|item| identity(tcx, *item)).collect::<BTreeSet<_>>();
    let mut nodes = Nodes { tcx, collected: &collected, rows: BTreeMap::new() };
    let mut owners = BTreeMap::new();
    let mut occurrences = Vec::new();
    let mut used_owners = BTreeSet::new();
    // Owner sorting makes parallel collector scheduling irrelevant. Ordinals
    // preserve per-owner observer order, not execution order or call counts.
    let visits = usage
        .dependencies
        .items()
        .map(|(&(item, pass), records)| {
            (format!("item:{}:{}", identity(tcx, item), mode(pass)), item, pass, records)
        })
        .into_sorted_stable_ord_by_key(|row| &row.0);
    for (owner, item, pass, records) in visits {
        let item_id = nodes.item(item);
        let is_collected = collected.contains(&identity(tcx, item));
        if pass == CollectionMode::UsedItems {
            if !is_collected || !used_owners.insert(identity(tcx, item)) {
                tcx.dcx().fatal("Rust instance census: invalid used dependency owner");
            }
        }
        let row = json!({"id": owner, "item": item_id, "collection_mode": mode(pass), "collected": is_collected});
        if owners.insert(owner.clone(), row).is_some() {
            tcx.dcx().fatal("Rust instance census: duplicate dependency owner");
        }
        for (ordinal, observation) in records.iter().enumerate() {
            if matches!(observation.origin, TrustDependencyOrigin::EagerConstRoot) {
                tcx.dcx().fatal("Rust instance census: root observation on mono-body owner");
            }
            if pass == CollectionMode::MentionedItems
                && observation.mode != CollectionMode::MentionedItems
            {
                tcx.dcx().fatal("Rust instance census: used dependency in mentioned-only visit");
            }
            let mut row = nodes.occurrence(observation.kind);
            row["owner"] = json!(owner);
            row["ordinal"] = json!(ordinal);
            row["mode"] = json!(mode(observation.mode));
            row["origin"] = json!(origin(observation.origin));
            occurrences.push(row);
        }
    }
    if used_owners != collected {
        tcx.dcx().fatal("Rust instance census: incomplete dependency owner population");
    }
    // Trust: root scans are a separate typed owner population. They neither
    // replace the recursive owner census above nor become collected mono items.
    let Some(visits) = &usage.eager_const_visits else {
        tcx.dcx().fatal("Rust instance census: missing eager free-const scan observation");
    };
    if !tcx.sess.link_dead_code() && !visits.is_empty() {
        tcx.dcx().fatal("Rust instance census: eager free-const scans on lazy strategy");
    }
    let mut eager_const_owners = BTreeMap::new();
    let mut eager_const_occurrences = BTreeMap::new();
    for visit in visits {
        if !matches!(tcx.def_kind(visit.def_id), rustc_hir::def::DefKind::Const { .. }) {
            tcx.dcx().fatal("Rust instance census: eager root owner is not a local free const");
        }
        let hash: String = tcx
            .def_path_hash(visit.def_id.to_def_id())
            .0
            .to_le_bytes()
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect();
        let owner = format!("eager-const:{hash}");
        let row = json!({
            "id": owner, "kind": "free-const", "phase": "root-discovery",
            "def": tcx.def_path_debug_str(visit.def_id.to_def_id()),
            "def_path_hash": hash, "definition_is_local": true,
            "collection_mode": "used", "collected": false,
            "dependency_count": visit.dependencies.len(),
        });
        // Keep the typed identity beside its spelling; duplicates/collisions
        // refuse instead of merging distinct successful constant scans.
        if eager_const_owners.insert(owner.clone(), (visit.def_id, row)).is_some() {
            tcx.dcx().fatal("Rust instance census: duplicate eager free-const owner identity");
        }
        let mut records = Vec::new();
        for (ordinal, observation) in visit.dependencies.iter().enumerate() {
            if observation.mode != CollectionMode::UsedItems
                || !matches!(observation.origin, TrustDependencyOrigin::EagerConstRoot)
            {
                tcx.dcx().fatal("Rust instance census: wrong eager free-const observation context");
            }
            if !matches!(
                observation.kind,
                TrustDependencyKind::Allocation { .. }
                    | TrustDependencyKind::AllocationRoot { .. }
                    | TrustDependencyKind::Relocation { .. }
                    | TrustDependencyKind::VtableMaterialization { .. }
                    | TrustDependencyKind::InstanceUse {
                        site: TrustDependencySite::AllocationFunction
                            | TrustDependencySite::AllocationStatic,
                        ..
                    }
            ) {
                tcx.dcx()
                    .fatal("Rust instance census: unexpected eager free-const dependency kind");
            }
            let mut row = nodes.occurrence(observation.kind);
            row["owner"] = json!(owner);
            row["ordinal"] = json!(ordinal);
            row["mode"] = json!("used");
            row["origin"] = json!("eager-const-root");
            records.push(row);
        }
        eager_const_occurrences.insert(owner, records);
    }
    let eager_const_occurrences: Vec<_> = eager_const_occurrences.into_values().flatten().collect();
    // References can precede their node's observation (a relocation is recorded
    // before recursion). Validate after the full population has been rendered.
    for row in occurrences.iter().chain(&eager_const_occurrences) {
        for field in ["source", "target"] {
            if let Some(target) = row.get(field).and_then(Value::as_str) {
                if !nodes.rows.contains_key(target) {
                    tcx.dcx().fatal("Rust instance census: unknown dependency endpoint");
                }
            }
        }
    }
    Snapshot {
        nodes: nodes.rows.into_values().map(|(_, row)| row).collect(),
        owners: owners.into_values().collect(),
        occurrences,
        eager_const_owners: eager_const_owners.into_values().map(|(_, row)| row).collect(),
        eager_const_occurrences,
    }
}

//! Trust (plan step 3.3, docs/design/2026-10-02-step3-lean-through-trust-ir.md §5.4): the F1
//! inventory from published Clean rows and a bounded exact Rust IR fragment.
//!
//! Trust (step 2 increment 7): plain local nongeneric Rust functions can also
//! answer from their exact D28-conserved handoff. `rust_inventory` checks both
//! retained THIR and canonical IR: primitive expressions, scalar local cells
//! and the existing exact-source thin-pointer comparison model qualify only
//! without implicit runtime services, required constants or function addresses.
//! Existing MIR-based monomorphization checks remain; this increment retires
//! the inventory walk for that fragment, not all MIR queries for the function.
//!
//! Until increment 7 derives F1's work list from trust-ir, the work list is rustc's mono-item
//! collector, and the collector walked a Clean-origin def's `clean_origin_mir` MIR. That MIR is
//! the MIR lane's spelling, not the trust-ir row F1 lowers: a wrapping-binop def's MIR calls the
//! marker-authenticated `u64::wrapping_add`, where its trust-ir row is one `BinOp::Add`. So F1's
//! census carried an `[upstream-body]` row for `core::num::<impl u64>::wrapping_add` that no Rust
//! body and no trust-ir row calls (measured on `tests/run-make/trust-cg-clean-origin-below-gate`).
//!
//! On F1 the collector now asks [`neighbours`] (the `trust_f1_clean_origin_neighbours` hook) for a
//! Clean-origin item, and gets its PUBLISHED row's call edges: the Rust callees the row's `Call`s
//! name, mapped back to their definitions through the F1 handoff's exact identity index. No MIR
//! is read for an item answered that way; an item with no complete row to read is walked as
//! before (below).
//!
//! # Why this cannot over-license
//!
//! The answer only chooses which items the collector VISITS. Every visited item is still lowered
//! from trust-ir and refused or gated exactly as before; a Clean-origin item is still refused
//! (`[clean-below-gate]`). An under-collected neighbour can only make a later lowering fail (a
//! missing body), never admit one.
//!
//! # When the answer is "walk the MIR as ever" (`None`)
//!
//! Off F1, for a Rust item outside that fragment, and when no F1 handoff is installed yet (a collection that runs
//! before crate finalization, e.g. a `-Ztrust-dump` probe): the pre-3.3 behaviour, so a cached
//! inventory is never computed from a handoff that did not exist.
//!
//! Also whenever this lane has no complete row to read in its place (plan R-8: MIR leaves a path
//! only where trust-ir measures at least as good there):
//! * no row is recorded for the def (the recorder runs only with verification on until plan step
//!   3.5, and a planner-skipped def has no row on any lane);
//! * the row references a function the handoff does not index (a Clean-origin row that is not an
//!   entry of the Session's carrier ledger, or a Rust body the handoff did not assemble) or a
//!   generic definition, or references something trust-ir's dependency census cannot follow (an
//!   indirect call, an unresolved destructor).
//!
//! Since plan step 3.4 the handoff also indexes the carrier ledger's rows (authenticated tier-`gate`
//! Clean rows, `AssembledCrateModuleForCodegen::checked_with_ledger`), so a row whose callee is
//! such a row is answered from trust-ir like a row calling an assembled Rust body; the rule above
//! is unchanged (an unindexed callee still walks the MIR). That callee is visited as its own item
//! and asked of this hook in turn; nothing it answers admits a body.
//!
//! Reading such a row would drop a real callee: before the step-3 review it answered `Some(&[])`
//! for an unrecorded def, and a Rust callee reached only through it fell out of every F1
//! inventory and the census (`tests/run-make/trust-cg-f1-mixed-crate`'s t4p, a private `inc`
//! called only from a Lean def: 0/2 with verification off where verification on read 0/4). The
//! MIR walk keeps the MIR lane's neighbours, MIR-only primitive callees included (t1's
//! `u64::wrapping_add` is an `[upstream-body]` row again with verification off), which is what
//! the base compiler did. Step 3.5 records on every F1 compile and removes the unrecorded case
//! for every shape the recorder publishes.
//!
//! # When the answer is the row's callees (`Some`)
//!
//! A recorded row whose every function reference maps to a non-generic local definition:
//! exactly those definitions, each once; `Some(&[])` for a call-free row (t1's `cleanWsum`,
//! whose MIR calls `u64::wrapping_add` where its row is one `add`).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use rustc_middle::ty::{self, TyCtxt};
use rustc_span::def_id::{DefId, DefIndex, LOCAL_CRATE};

use super::clean_below_gate::disclosed_rows;

// Trust (step 2 increment 7): source-checked Rust rows share this existing
// inventory hook. The module name is historical; Clean admission is unchanged.
mod rust_inventory;

/// The `trust_f1_clean_origin_neighbours` hook provider. See the module docs.
pub(crate) fn neighbours<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Option<&'tcx [DefId]> {
    if !tcx.sess.trust_cg_frontend_is_trust_ir() {
        return None;
    }
    let ty::InstanceKind::Item(def_id) = instance.def else { return None };
    let local = def_id.as_local()?;
    if !tcx.resolutions(()).clean_origin_defs.iter().any(|&(def, _, _)| def == local) {
        return rust_inventory::neighbours(tcx, instance, local);
    }
    let def_path =
        rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(local.to_def_id()));
    // `None` from the closure: no handoff installed; `Some(None)`: no complete row to read.
    // Either way, walk the MIR as ever.
    let indices = tcx
        .sess
        .with_trust_compiler_state::<trust_thir_lower::AssembledCrateModuleForCodegen, _>(
            |handoff| {
                let module = handoff.assembled_module().ok()?;
                Some(row_neighbours(&module, &def_path, |func_id| {
                    handoff.indexed_def_index(func_id)
                }))
            },
        )
        .flatten();
    let callees: Option<Vec<DefId>> = indices.map(|indices| {
        indices
            .into_iter()
            .map(|index| DefId { krate: LOCAL_CRATE, index: DefIndex::from_u32(index) })
            .collect()
    });
    // A Rust callee of a Clean island is a carrier-typed free `fn`. A generic definition has no
    // single instance to name here, so a row that calls one is not read.
    match callees {
        Some(callees) if callees.iter().all(|def| tcx.generics_of(*def).count() == 0) => {
            Some(tcx.arena.alloc_from_iter(callees))
        }
        _ => {
            // Plan step 3.5 (design §5.7): the collector now walks this Clean-origin item's
            // `clean_origin_mir` MIR. That is the inventory's read, charged to the reach
            // counter's `inventory` lane once per walk: the body is demanded here, inside the ask,
            // so the collector's own demand right after is answered from the cache and nothing
            // is charged twice. The step-3 exit requires this lane to be zero.
            let _ask = trust_thir_lower::clean_origin_reach::ask(
                tcx.sess,
                trust_thir_lower::clean_origin_reach::ReachLane::Inventory,
            );
            let _ = tcx.instance_mir(instance.def);
            None
        }
    }
}

/// The local `DefIndex` of every callee of the published Clean-origin row for `def_path`, in
/// call order, each once, mapped through `index` (the F1 handoff's identity index). `None` when
/// the row cannot stand in for the MIR walk: no emitted row is recorded for the def (nothing
/// recorded on this lane, or a planner-skipped def), the row's function is not a
/// `Producer::Clean` body, or a callee is not indexed. PURE.
pub(crate) fn row_neighbours(
    module: &trust_ir::Module,
    def_path: &str,
    index: impl Fn(trust_ir::value::FuncId) -> Option<u32>,
) -> Option<Vec<u32>> {
    published_row_callees(module, def_path)?.into_iter().map(index).collect()
}

/// The callee `FuncId`s of the published Clean-origin row for `def_path`, in discovery order,
/// each once; `None` when the module carries no emitted row for it (nothing recorded on this
/// lane, or a planner-skipped def), the row's function is not a `Producer::Clean` body, or the
/// row is not a complete list of what it references. The row is located through the
/// clean-origin disclosure (`fn:<id>` names the published `FuncId`). PURE.
///
/// The references are read by trust-ir's own dependency census, not by matching `Inst::Call`:
/// the census follows every function a row's instructions name (a `Call`, a
/// `CallCannotUnwind`, an `Invoke`, a function-address constant, a resolved drop's glue), and
/// REFUSES what it cannot follow (an indirect call, an unresolved destructor or symbol, a
/// malformed body). A refusal at the row itself makes the row incomplete. A self-reference is
/// not a neighbour (the collector is visiting the def already).
pub(crate) fn published_row_callees(
    module: &trust_ir::Module,
    def_path: &str,
) -> Option<Vec<trust_ir::value::FuncId>> {
    use trust_ir::function_dependencies::{
        DependencyNode, DependencySite, inspect_function_dependencies,
    };
    let row = disclosed_rows(module)
        .into_iter()
        .find(|row| row.def_path == def_path && row.func_id.is_some())?;
    let root = module
        .functions
        .iter()
        .find(|f| {
            Some(f.id.index()) == row.func_id && f.producer == Some(trust_ir::Producer::Clean)
        })?
        .id;
    let census = inspect_function_dependencies(module, root);
    let at_root = |site: &DependencySite| match site {
        DependencySite::Root => true,
        DependencySite::Definition(DependencyNode::Function(id)) => *id == root,
        DependencySite::Instruction { function, .. } => *function == root,
        _ => false,
    };
    if census.refusals().iter().any(|refusal| at_root(&refusal.site)) {
        return None;
    }
    let mut callees = Vec::new();
    for edge in census.edges() {
        if let (DependencySite::Instruction { function, .. }, DependencyNode::Function(callee)) =
            (&edge.site, &edge.target)
            && *function == root
            && *callee != root
            && !callees.contains(callee)
        {
            callees.push(*callee);
        }
    }
    Some(callees)
}

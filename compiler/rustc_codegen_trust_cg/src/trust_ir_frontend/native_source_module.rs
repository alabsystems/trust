//! An ABI-checked source module for the full native Trust-IR consumer.
//!
//! Unlike the scalar legalizer, this transport keeps logical closure parameters
//! and every function/table identity. Its caller checks each source instance's
//! actual rustc ABI and supplies the session's conserved IDs. A non-source ID
//! acquires no licence here: only the conservation query may derive an adapter
//! ID, and its exact module must still be the checked handoff below.

use std::collections::{BTreeMap, BTreeSet};

use trust_cg_bridge::call_event::{FnPlacement, ProducerBody};
use trust_cg_bridge::codegen_backend::FunctionLinkage;
use trust_ir::function_dependencies::inspect_function_dependencies;
use trust_ir::{Endianness, FuncId, Inst, Linkage, Module, Producer, StructPassingPolicy};

use super::FrontendRefusal;
use super::codegen_module::{CodegenModuleOutput, ExpectedTarget, linkage_of};

#[path = "native_source_module/adapter_placement.rs"]
mod adapter_placement;
pub(crate) mod foreign_declarations;

/// A selected source instance whose unchanged signature has passed the native
/// source ABI agreement check. A placement is diagnostic input to the existing
/// independent object gate; its presence asserts no proof grade.
pub(crate) struct NativeWorkItem {
    pub(crate) func: FuncId,
    pub(crate) symbol: String,
    pub(crate) linkage: FunctionLinkage,
    pub(crate) never_inline: bool,
    pub(crate) placement: Option<FnPlacement>,
    /// A real source dependency omitted from rustc's optimized mono inventory.
    pub(crate) inventory_residue: bool,
}

pub(crate) struct NativeModuleInput<'a> {
    pub(crate) producer: &'a Module,
    /// The exact checked and conservation-filtered session handoff. A missing
    /// handoff refuses: an instance assembler's edited module cannot inherit
    /// its adapter licence and the comparison must never be skipped.
    pub(crate) base: Option<&'a Module>,
    pub(crate) items: &'a [NativeWorkItem],
    /// From effect_conservation::conserved_function_ids in this session.
    pub(crate) conserved: &'a BTreeSet<FuncId>,
    /// The complete handoff.codegen_body_ids() projection, not a name heuristic.
    pub(crate) source_ids: &'a BTreeSet<FuncId>,
    /// Exact original source Items rechecked through the immutable declaration
    /// ledger. This is ABI/identity input only, never an external-body proof.
    pub(crate) foreign_declarations: &'a BTreeSet<FuncId>,
    pub(crate) has_statics: bool,
    pub(crate) target: &'a ExpectedTarget,
}

#[path = "native_source_module/routing.rs"]
mod routing;
#[cfg(test)]
use routing::has_reachable_closure;
pub(crate) use routing::{NativeRouteInput, uses_native_source};

fn refusal(symbol: &str, detail: impl Into<String>) -> FrontendRefusal {
    FrontendRefusal::CodegenModule { symbol: symbol.into(), detail: detail.into() }
}

/// Preserve the whole module. Every defined function must have either a real
/// selected source instance or an independently derived adapter licence. This
/// first source-native transport refuses unexplained inventory residue and
/// statics; it never substitutes extern declarations or drops evidence tables.
pub(crate) fn build(input: &NativeModuleInput<'_>) -> CodegenModuleOutput {
    let producer = input.producer;
    let mut out = CodegenModuleOutput {
        m_cg: producer.clone(),
        symbols: BTreeMap::new(),
        bodies: BTreeMap::new(),
        placements: BTreeMap::new(),
        never_inline: BTreeSet::new(),
        residue: Vec::new(),
        refusals: Vec::new(),
    };
    if !matches!(input.base, Some(base) if producer == base) {
        out.refusals.push(refusal(
            &producer.name,
            "source-native transport requires the exact conservation-filtered handoff module; \
             edited instance modules do not inherit its source-derived adapter licences",
        ));
    }
    match &producer.target_info {
        Some(info)
            if info.triple == input.target.triple
                && info.pointer_size == input.target.pointer_size
                && info.pointer_size == 8
                && info.endianness == Endianness::Little
                && info.struct_passing == StructPassingPolicy::Unclassified => {}
        _ => out.refusals.push(refusal(
            &producer.name,
            "source-native transport requires this exact 64-bit little-endian target with \
             unclassified producer aggregate passing; each source ABI is checked separately",
        )),
    }
    if !producer.globals.is_empty() || input.has_statics {
        out.refusals.push(refusal(
            &producer.name,
            "source-native transport has no qualified collector-static/global identity binding",
        ));
    }
    if !producer.global_asm.is_empty() || !producer.drop_glue.is_empty() {
        out.refusals.push(refusal(
            &producer.name,
            "source-native transport does not yet qualify global assembly or drop-glue tables",
        ));
    }

    let mut items = BTreeMap::new();
    let mut symbol_owners = BTreeMap::new();
    for item in input.items {
        if items.insert(item.func, item).is_some() {
            out.refusals
                .push(refusal(&item.symbol, "two source work items claim one producer FuncId"));
        }
        if symbol_owners.insert(&item.symbol, item.func).is_some() {
            out.refusals.push(refusal(&item.symbol, "two source work items claim one link symbol"));
        }
        if !input.source_ids.contains(&item.func) {
            out.refusals.push(refusal(
                &item.symbol,
                "selected source instance has no exact handoff source identity",
            ));
        }
        if producer.function_by_id(item.func).is_none_or(|f| f.is_declaration()) {
            out.refusals.push(refusal(&item.symbol, "selected source body is missing"));
        }
    }

    let mut names = BTreeSet::new();
    for function in &producer.functions {
        if !names.insert(&function.name) {
            out.refusals.push(refusal(&function.name, "producer link symbol is ambiguous"));
        }
        if function.is_declaration() {
            if input.foreign_declarations.contains(&function.id)
                && foreign_declarations::recorded(producer, function.id)
            {
                out.symbols.insert(function.id, function.name.clone());
            } else {
                out.refusals.push(refusal(&function.name,
                    "source-native transport has no exact source ABI for this declaration"));
            }
            continue;
        }
        if function.producer != Some(Producer::TRust) || !input.conserved.contains(&function.id) {
            out.refusals.push(refusal(
                &function.name,
                "defined body is not a conserved Rust source or source-derived adapter",
            ));
        }
        match items.get(&function.id) {
            Some(item) => {
                if function.name != item.symbol {
                    out.refusals.push(refusal(
                        &item.symbol,
                        "source instance symbol differs from its exact producer body",
                    ));
                }
                if item.inventory_residue {
                    out.residue.push(super::codegen_module::ResidueRow {
                        symbol: item.symbol.clone(),
                        producer_func: item.func,
                        m_cg_func: item.func,
                    });
                }
                if let Some(placement) = &item.placement {
                    out.placements.insert(item.symbol.clone(), placement.clone());
                }
                if item.never_inline {
                    out.never_inline.insert(item.symbol.clone());
                }
                let (linkage, visibility) = linkage_of(item.linkage);
                if let Some(body) = out.m_cg.functions.iter_mut().find(|f| f.id == function.id) {
                    body.name = item.symbol.clone();
                    body.linkage = linkage;
                    body.visibility = visibility;
                }
            }
            None if input.source_ids.contains(&function.id) => {
                out.refusals.push(refusal(
                    &function.name,
                    "source inventory residue lacks an exact selected native ABI",
                ));
            }
            None => {
                // Under exact-base binding and the complete source-ID map,
                // conservation's remaining IDs are its derived adapters. They
                // keep their original symbol and never gain a Rust DefIndex.
                if function.linkage != Linkage::Internal {
                    out.refusals.push(refusal(
                        &function.name,
                        "source-derived adapter must retain internal linkage",
                    ));
                }
                match adapter_placement::derive(input, function.id) {
                    Ok(Some(placement)) => {
                        out.placements.insert(function.name.clone(), placement);
                    }
                    Ok(None) => {} // The independent gate reports missing P as Unknown.
                    Err(detail) => out.refusals.push(refusal(&function.name, detail)),
                }
            }
        }
        out.symbols.insert(function.id, function.name.clone());
        out.bodies.insert(function.name.clone(), ProducerBody { producer: 0, func: function.id });
    }

    // Both images must have the same complete dependency identities. In
    // particular, a symbol-address constant cannot silently retain an old name
    // if future symbol transport is added above. No reference is renumbered.
    for function in producer.functions.iter().filter(|f| !f.is_declaration()) {
        let before = inspect_function_dependencies(producer, function.id);
        let after = inspect_function_dependencies(&out.m_cg, function.id);
        for (label, census) in [("producer", &before), ("native module", &after)] {
            for problem in census.refusals() {
                if matches!(problem.kind,
                    trust_ir::function_dependencies::DependencyRefusalKind::BodylessFunction(id)
                        if input.foreign_declarations.contains(&id)
                            && foreign_declarations::recorded(producer, id))
                { continue; }
                out.refusals.push(refusal(
                    &function.name,
                    format!("{label} dependency refusal at {:?}: {:?}", problem.site, problem.kind),
                ));
            }
        }
        if before.nodes() != after.nodes() || before.edges() != after.edges() {
            out.refusals.push(refusal(
                &function.name,
                "native symbol transport changed the producer dependency identities",
            ));
        }
    }
    out
}

// Trust: out-of-line unit tests, as tidy's `unit_tests` check requires.
#[cfg(test)]
mod tests;

// Trust: out-of-line unit tests, as tidy's `unit_tests` check requires.
#[cfg(test)]
#[path = "native_source_module/tests/adapter_tests.rs"]
mod adapter_tests;
#[cfg(test)]
#[path = "native_source_module/tests/foreign_declarations.rs"]
pub(crate) mod foreign_declarations_tests;

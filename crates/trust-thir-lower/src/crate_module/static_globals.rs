//! One allocation per compiler static identity, never per body or display name.

use std::collections::{HashMap, HashSet};

use rustc_span::def_id::DefId;
use trust_ir::value::GlobalId;
use trust_ir::{Global, Module};

use super::BodyRecord;
use crate::GlobalOrigin;

/// Every minted global has an origin; absence cannot silently mean promotion.
pub(super) fn validate_origins(record: &BodyRecord) -> Result<(), &'static str> {
    if record.global_origins.len() != record.globals.len() {
        return Err("GlobalOrigin(incomplete ledger)");
    }
    let mut statics = HashSet::new();
    for (global, origin) in record.globals.iter().zip(&record.global_origins) {
        match origin {
            GlobalOrigin::Static(def) if !statics.insert(*def) => {
                return Err("GlobalOrigin(duplicate static identity)");
            }
            GlobalOrigin::BodyLocal if global.mutable => {
                return Err("GlobalOrigin(mutable global without static identity)");
            }
            _ => {}
        }
    }
    for pending in &record.pending_consts {
        if let Some(global) = pending.static_global {
            if record.global_origins.get(global.as_usize())
                != Some(&GlobalOrigin::Static(pending.def_id))
            {
                return Err("GlobalOrigin(deferred static identity disagreement)");
            }
        }
    }
    Ok(())
}

/// Assembly-attempt-local state. Tables are append-only: even if a later body
/// remap fails, an interned global remains valid and its index cannot dangle.
/// Conflicting observations are sticky and withhold *all* claimant bodies.
#[derive(Default)]
pub(super) struct StaticGlobals {
    interned: HashMap<DefId, GlobalId>,
    poisoned: HashSet<DefId>,
}

impl StaticGlobals {
    pub(super) fn poison_record(&mut self, record: &BodyRecord) {
        for origin in &record.global_origins {
            if let GlobalOrigin::Static(def) = origin {
                self.poisoned.insert(*def);
            }
        }
        // A damaged origin ledger cannot hide the independent deferred claim.
        for pending in &record.pending_consts {
            if pending.static_global.is_some() {
                self.poisoned.insert(pending.def_id);
            }
        }
    }

    pub(super) fn conflicts(&self, record: &BodyRecord) -> bool {
        record.global_origins.iter().any(
            |origin| matches!(origin, GlobalOrigin::Static(def) if self.poisoned.contains(def)),
        )
    }

    /// Called only after the existing initializer gate and complete type remap.
    /// SymbolAddr/FnDef initializers remain outside that gate; no relocation is
    /// silently carried across the assembly rename. Constants use TrustIR's
    /// recursive bit-exact equality (including NaNs and signed floating zero).
    pub(super) fn intern(
        &mut self,
        module: &mut Module,
        origin: GlobalOrigin,
        mut global: Global,
    ) -> Option<GlobalId> {
        if let GlobalOrigin::Static(def) = origin {
            if self.poisoned.contains(&def) {
                return None;
            }
            if let Some(id) = self.interned.get(&def).copied() {
                let Some(existing) = module.globals.get(id.as_usize()) else {
                    self.poisoned.insert(def);
                    return None;
                };
                // Ignore only the body-local display label. Comparing the
                // whole Global retains every present and future attribute.
                global.name = existing.name.clone();
                if global != *existing {
                    self.poisoned.insert(def);
                    return None;
                }
                return Some(id);
            }
        }
        let index = u32::try_from(module.globals.len()).ok()?;
        let id = GlobalId::new(index);
        global.name = format!("__trust_promoted_{index}");
        module.globals.push(global);
        if let GlobalOrigin::Static(def) = origin {
            self.interned.insert(def, id);
        }
        Some(id)
    }
}

#[cfg(test)]
#[path = "static_globals/tests.rs"]
mod tests;

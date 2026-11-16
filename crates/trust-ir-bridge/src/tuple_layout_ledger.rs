//! Rustc's tuple layouts, admitted into the bridge's module (2026-09-29).
//!
//! `trust_types::Ty::Tuple` carries no layout, so until this file a non-empty tuple
//! reached the bridge with no byte offsets on any lane. The bridge guessed
//! `index * size_of(field)` until 2026-09-28 and has emitted an unknown offset since
//! (`address_from_pointer`, "CASE 3 NAMES NO OFFSET"). The faithful extraction lane
//! now records rustc's own `layout_of` answer per tuple
//! (`VerifiableFunction::tuple_layouts`, written only by `trust_mir_extract::tuple_layouts`),
//! and this file is where the bridge turns such a row into a module
//! `TupleLayoutDescriptor`. The unknown-offset spelling stays as the fail-closed
//! fallback for every tuple that is not admitted here.
//!
//! ADMISSION is the THIR producer's `register_tuple_layout` discipline, restated over
//! this bridge's module:
//!
//! * the row must be this BODY's own (`TupleLayouts::layout_of` on the body's own
//!   spelling of the tuple, which also refuses an incoherent row);
//! * the module's target must be the row's target, or unset (it is then set to the
//!   row's, `abi: None` and `StructPassingPolicy::Unclassified`, as
//!   `crate_module::source_target_info` does);
//! * every element's size and ABI alignment IN THIS MODULE must equal the ones rustc
//!   laid the tuple out over, so the offsets are rustc's and so are the extents;
//! * `Module::validate_tuple_layouts` must accept the module with the row added.
//!
//! Offsets come only from the row. Nothing here computes one.
//!
//! ONE ROW PER TRUST-IR TUPLE, FOR THE WHOLE MODULE. A descriptor is keyed by the
//! MAPPED type, and a module can hold one layout per key. Two source spellings can map
//! to one trust-ir tuple while rustc lays them out differently (field order follows
//! niches, which trust-ir does not spell), and two bodies can record different rows for
//! one key. Either way the key is POISONED for the rest of the module: its descriptor
//! is withdrawn, so is every descriptor whose layout depended on it, and no later body
//! can re-admit it. Addresses an earlier body already emitted from the withdrawn row
//! stay correct for that body — they are that body's own rustc offsets.
//!
//! A FIELD ADDRESS NEEDS THIS BODY'S OWN ROW. `admit_tuple_layout` answers whether
//! THIS body may read a declared offset; a descriptor another body admitted is not
//! evidence about this one, so `address_from_pointer` asks before every tuple field
//! address and names no offset when the answer is no.
//!
//! CLOSURE ENVIRONMENTS are not covered: trust-ir has no layout shape for
//! `Ty::Closure`, so a capture address keeps the unknown-offset spelling until the
//! format can carry one.

use trust_ir::ty::Ty as TrustIrTy;
use trust_ir::value::TyId;
use trust_ir::{Module, TupleLayoutDescriptor};
use trust_types::{TupleLayouts, Ty};

use super::LoweringCtx;

/// The empty table every `LoweringCtx` starts from (no body, no row).
pub(super) static EMPTY_TUPLE_LAYOUTS: TupleLayouts =
    TupleLayouts { target: None, entries: Vec::new() };

/// Module-scoped tuple-layout state, threaded through every `lower_function_into`
/// call that builds one module. A `LoweringCtx` without one admits no tuple layout.
#[derive(Debug, Default)]
pub(super) struct TupleLayoutLedger {
    /// The one source spelling each trust-ir tuple was mapped from in this module.
    spellings: Vec<(TrustIrTy, Ty)>,
    /// Trust-ir tuples this module declares no layout for, for good.
    poisoned: Vec<TrustIrTy>,
}

impl TupleLayoutLedger {
    fn is_poisoned(&self, mapped: &TrustIrTy) -> bool {
        self.poisoned.contains(mapped)
    }

    fn mark_poisoned(&mut self, mapped: &TrustIrTy) {
        if !self.poisoned.contains(mapped) {
            self.poisoned.push(mapped.clone());
        }
    }

    /// Poison `mapped` and withdraw its descriptor, then every descriptor whose layout
    /// no longer resolves because it was laid out over a withdrawn one.
    fn poison(&mut self, mapped: &TrustIrTy, module: &mut Module) {
        self.mark_poisoned(mapped);
        loop {
            let withdraw = module.tuple_layouts.iter().position(|desc| {
                module.types.get(desc.tuple_type.as_usize()).is_none_or(|ty| {
                    self.poisoned.contains(ty) || module.ty_layout_shape(ty).is_err()
                })
            });
            let Some(index) = withdraw else { break };
            let desc = module.tuple_layouts.remove(index);
            if let Some(ty) = module.types.get(desc.tuple_type.as_usize()).cloned() {
                self.mark_poisoned(&ty);
            }
        }
    }
}

impl LoweringCtx<'_> {
    /// Record that this module maps the source tuple `source` to `mapped`. A second,
    /// DIFFERENT source spelling of the same trust-ir tuple poisons it: rustc may lay
    /// the two out differently, and the module could hold only one of them.
    pub(super) fn note_tuple_spelling(&mut self, source: &Ty, mapped: &TrustIrTy) {
        if !matches!(mapped, TrustIrTy::Tuple(elems) if !elems.is_empty()) {
            return;
        }
        let Some(ledger) = self.tuple_ledger.as_deref_mut() else { return };
        let first_is_same = ledger
            .spellings
            .iter()
            .find(|(seen, _)| seen == mapped)
            .map(|(_, first)| first == source);
        match first_is_same {
            Some(true) => {}
            Some(false) => ledger.poison(mapped, self.module),
            None => ledger.spellings.push((mapped.clone(), source.clone())),
        }
    }

    /// Admit THIS body's rustc layout of the tuple `source` (mapped to `mapped`) into
    /// the module, and answer whether this body may compute a field address from the
    /// module's declared layout of `mapped`. See the module doc for the four
    /// admission conditions and the poisoning rule. `false` never changes an emitted
    /// address into a guess: the caller then names no offset.
    pub(super) fn admit_tuple_layout(&mut self, source: &Ty, mapped: &TrustIrTy) -> bool {
        let TrustIrTy::Tuple(elems) = mapped else { return false };
        if elems.is_empty() {
            return false;
        }
        let layouts: &TupleLayouts = self.tuple_layouts;
        let Some(ledger) = self.tuple_ledger.as_deref_mut() else { return false };
        if ledger.is_poisoned(mapped) {
            return false;
        }
        let (Some(row), Some(target)) = (layouts.layout_of(source), layouts.target.as_ref()) else {
            return false;
        };
        if row.field_offsets.len() != elems.len() {
            return false;
        }
        let endianness = if target.little_endian {
            trust_ir::Endianness::Little
        } else {
            trust_ir::Endianness::Big
        };
        let previous_target = self.module.target_info.clone();
        match &previous_target {
            Some(declared)
                if declared.triple == target.triple
                    && declared.pointer_size == target.pointer_size
                    && declared.endianness == endianness => {}
            Some(_) => return false,
            None => {
                self.module.target_info = Some(trust_ir::TargetInfo {
                    triple: target.triple.clone(),
                    pointer_size: target.pointer_size,
                    endianness,
                    abi: None,
                    struct_passing: trust_ir::StructPassingPolicy::Unclassified,
                });
            }
        }
        let extents_agree = elems.iter().enumerate().all(|(index, elem)| {
            self.module.ty_layout_shape(elem).is_ok_and(|shape| {
                shape.size_bytes() == Some(row.field_sizes[index])
                    && shape.align_bits == row.field_aligns[index].checked_mul(8)
            })
        });
        if !extents_agree {
            self.module.target_info = previous_target;
            return false;
        }
        let declared = self
            .module
            .tuple_layouts
            .iter()
            .position(|desc| self.module.types.get(desc.tuple_type.as_usize()) == Some(mapped));
        if let Some(index) = declared {
            let desc = &self.module.tuple_layouts[index];
            if desc.size == row.size
                && desc.align == row.align
                && desc.field_offsets == row.field_offsets
            {
                return true;
            }
            ledger.poison(mapped, self.module);
            return false;
        }
        let (tuple_type, added) = match self.module.types.iter().position(|ty| ty == mapped) {
            Some(index) => (TyId::new(index as u32), false),
            // A full type table is a refusal (trust-ir D1b): name no offset.
            None => match self.module.add_type(mapped.clone()) {
                Ok(id) => (id, true),
                Err(_) => {
                    self.module.target_info = previous_target;
                    return false;
                }
            },
        };
        self.module.tuple_layouts.push(TupleLayoutDescriptor {
            tuple_type,
            size: row.size,
            align: row.align,
            field_offsets: row.field_offsets.clone(),
        });
        if self.module.validate_tuple_layouts().is_ok() {
            return true;
        }
        self.module.tuple_layouts.pop();
        if added {
            self.module.types.pop();
        }
        self.module.target_info = previous_target;
        false
    }
}

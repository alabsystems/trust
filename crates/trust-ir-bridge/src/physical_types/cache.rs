//! Cache complete root requests against one immutable definition table.
//!
//! Recursive expansion is deliberately not cached: its active names, depth and
//! remaining node budget are inputs. Every miss still starts the original root
//! algorithm, including whole-root rollback on exhaustion.

use std::mem::size_of;

use trust_types::{AdtLayoutInfo, DatatypeDefs, Ty};

const MAX_KEY_BYTES: usize = 256;
const MAX_ENTRIES: usize = 64;
const MAX_RETAINED_BYTES: usize = 1_048_576;
const MAX_RETAINED_NODES: usize = 2048;

struct Entry {
    name: Box<str>,
    result: Ty,
}

pub(super) struct Normalizer<'a> {
    defs: &'a DatatypeDefs,
    physical: bool,
    entries: Vec<Entry>,
    retained_bytes: usize,
    retained_nodes: usize,
    #[cfg(test)]
    misses: usize,
}

impl<'a> Normalizer<'a> {
    pub(super) fn new(defs: &'a DatatypeDefs) -> Self {
        Self {
            defs,
            physical: super::has_physical_definitions(defs),
            entries: Vec::new(),
            retained_bytes: 0,
            retained_nodes: 0,
            #[cfg(test)]
            misses: 0,
        }
    }

    pub(super) fn has_physical_definitions(&self) -> bool {
        self.physical
    }

    pub(super) fn normalize(&mut self, ty: &Ty) -> Ty {
        if !self.physical {
            return ty.clone();
        }
        // This variant has exactly one variable component, its name. With a
        // fixed immutable defs table the bounded name is the COMPLETE input,
        // not a lossy key for an inline or logical datatype. No deep Ty hashing.
        let key = match ty {
            Ty::Datatype { name, variants }
                if variants.is_empty() && name.len() <= MAX_KEY_BYTES =>
            {
                Some(name.as_str())
            }
            _ => None,
        };
        if let Some(name) = key {
            if let Some(entry) = self.entries.iter().find(|entry| entry.name.as_ref() == name) {
                return entry.result.clone();
            }
        }
        #[cfg(test)]
        {
            self.misses += 1;
        }
        let result = super::normalize_physical(ty, self.defs);
        if let Some(name) = key {
            self.retain(name, &result);
        }
        result
    }

    fn retain(&mut self, name: &str, result: &Ty) {
        if self.entries.len() == MAX_ENTRIES {
            return;
        }
        let mut room = Room {
            bytes: MAX_RETAINED_BYTES - self.retained_bytes,
            nodes: MAX_RETAINED_NODES - self.retained_nodes,
        };
        let before = room;
        // Charge the complete fixed entry allocation on the first insertion,
        // including unused slots. Root Ty storage is counted again below;
        // double charging is conservative, sharing never reduces the charge.
        let entry_storage =
            if self.entries.is_empty() { MAX_ENTRIES * size_of::<Entry>() } else { 0 };
        if room.bytes(entry_storage).is_none()
            || room.bytes(name.len()).is_none()
            || room.ty(result, 0).is_none()
        {
            return;
        }
        if self.entries.is_empty() {
            self.entries = Vec::with_capacity(MAX_ENTRIES);
        }
        self.entries.push(Entry { name: name.into(), result: result.clone() });
        self.retained_bytes += before.bytes - room.bytes;
        self.retained_nodes += before.nodes - room.nodes;
    }
}

#[derive(Clone, Copy)]
struct Room {
    bytes: usize,
    nodes: usize,
}

impl Room {
    fn bytes(&mut self, bytes: usize) -> Option<()> {
        self.bytes = self.bytes.checked_sub(bytes)?;
        Some(())
    }

    fn ty(&mut self, ty: &Ty, depth: usize) -> Option<()> {
        if depth >= super::MAX_DEPTH {
            return None;
        }
        self.nodes = self.nodes.checked_sub(1)?;
        self.bytes(size_of::<Ty>())?;
        match ty {
            Ty::Bool
            | Ty::Char
            | Ty::Int { width: _, signed: _ }
            | Ty::Float { width: _ }
            | Ty::PtrSizedInt { signed: _ }
            | Ty::Unit
            | Ty::Never => Some(()),
            Ty::Ref { inner, mutable: _ }
            | Ty::RawPtr { pointee: inner, mutable: _ }
            | Ty::Array { elem: inner, len: _ }
            | Ty::Slice { elem: inner } => self.ty(inner, depth + 1),
            Ty::Seq { elem, drop_auth } => {
                // This transient authority is Copy, not serialized/hash material.
                // The cache retains the actual Ty and never reconstructs its stamp.
                let _stamp = *drop_auth;
                self.ty(elem, depth + 1)
            }
            Ty::Datatype { name, variants } if variants.is_empty() => self.bytes(name.capacity()),
            Ty::Adt {
                name,
                fields,
                variants,
                disc_index_safe: _,
                faithful_enum_repr: _,
                arbitrary_precision,
                validity_wrapper: _,
                layout,
                enum_layout,
                adt_kind: _,
            } if variants.is_empty() && enum_layout.is_none() => {
                // Conservatively charge shared bodies as if this cache retained
                // their entire allocation, including every Ty inline and again
                // recursively. Pointer sharing cannot evade the aggregate cap.
                let _stamp = *arbitrary_precision;
                self.bytes(name.capacity())?;
                self.bytes(5 * size_of::<usize>())?;
                self.bytes(fields.capacity().checked_mul(size_of::<(String, Ty)>())?)?;
                for (name, field) in fields.iter() {
                    self.bytes(name.capacity())?;
                    self.ty(field, depth + 1)?;
                }
                // Empty SharedVec bodies still own an Arc/Vec allocation.
                self.bytes(5 * size_of::<usize>())?;
                self.bytes(variants.capacity().checked_mul(size_of::<trust_types::VariantDef>())?)?;
                if let Some(layout) = layout {
                    let AdtLayoutInfo { size: _, align: _, field_offsets, repr } = layout.as_ref();
                    self.bytes(size_of::<AdtLayoutInfo>())?;
                    self.bytes(field_offsets.capacity().checked_mul(size_of::<u64>())?)?;
                    self.bytes(repr.capacity())?;
                }
                Some(())
            }
            // This is storage accounting, never type admission. Enums, callables,
            // logical bodies and future shapes bypass the cache until their
            // retained allocations are accounted for. Normalization is unchanged.
            _ => None,
        }
    }
}

#[cfg(test)]
#[path = "cache_tests.rs"]
mod tests;

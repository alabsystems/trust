// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! Rustc's own layout of the tuple types a body names, carried out of band.
//!
//! WHY THIS EXISTS. `Ty::Tuple` carries no layout, so a non-empty tuple used to
//! reach the trust-ir bridge with no byte offsets on ANY lane. The bridge then
//! spelled a tuple field's address as `field index * size_of(field)` — a guess
//! that names byte 1 for `(u32, u8).1`, where the field lives at byte 4 — and
//! the MIR-side oracle of the interpretation differential EXECUTED it
//! (reports/2026-09-28-freeze-ratification-review.md, "Not closed here"). Since
//! 2026-09-28 the bridge emits an unknown offset instead of the guess; this table
//! is what lets it emit rustc's EXACT offset where rustc computed one.
//!
//! WHO WRITES IT. `trust_mir_extract::ty_convert` is the only writer, and only on
//! the FAITHFUL extraction lane (the differential's oracle, the crate-seam bundle,
//! the F1 upstream-instance MIR lane), exactly where `Ty::Adt::layout` is filled:
//! a non-empty table is hash-visible, so filling it on a verifier lane would move
//! shipped proof-cert and content pins. Every value is a `layout_of` answer for a
//! fully concrete tuple type; nothing here is derived from sizes and indices.
//!
//! WHAT A CONSUMER MUST STILL CHECK. A row states what rustc computed for the
//! RUSTC tuple the body's `Ty::Tuple` was lowered from, including each field's
//! own rustc size and ABI alignment. A consumer that lays the tuple out in its own
//! representation (the bridge's trust-ir module) must admit a row only where its
//! own element layouts agree with those recorded field sizes and alignments, as
//! the THIR producer's `register_tuple_layout` does — otherwise the offsets would
//! be rustc's while the field extents were someone else's.

use serde::{Deserialize, Serialize};

use crate::Ty;

/// The target a body's tuple layouts were computed for.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LayoutTarget {
    /// rustc's `llvm_target` triple.
    pub triple: String,
    /// Pointer width in BYTES.
    pub pointer_size: u32,
    /// `true` for a little-endian target.
    pub little_endian: bool,
}

/// Rustc's `layout_of` answer for one tuple type, indexed by tuple position.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TupleLayoutInfo {
    /// The tuple exactly as this body spells it (`Ty::Tuple`, non-empty).
    pub tuple: Ty,
    /// Size in bytes.
    pub size: u64,
    /// ABI alignment in bytes.
    pub align: u64,
    /// Byte offset of each field, by tuple position (rustc may reorder fields in
    /// memory; position `i` is still the source's `.i`).
    pub field_offsets: Vec<u64>,
    /// Each field's own rustc size in bytes, by tuple position.
    pub field_sizes: Vec<u64>,
    /// Each field's own rustc ABI alignment in bytes, by tuple position.
    pub field_aligns: Vec<u64>,
}

impl TupleLayoutInfo {
    /// The row is internally coherent: one entry per field everywhere, a
    /// power-of-two alignment that divides the size, and every field inside the
    /// tuple at an offset its own alignment divides. A consumer still checks the
    /// row against its own representation; this only refuses a row that cannot
    /// describe any layout.
    #[must_use]
    pub fn is_coherent(&self) -> bool {
        let Ty::Tuple(fields) = &self.tuple else { return false };
        let n = fields.len();
        n > 0
            && self.field_offsets.len() == n
            && self.field_sizes.len() == n
            && self.field_aligns.len() == n
            && self.align.is_power_of_two()
            && self.size % self.align == 0
            && (0..n).all(|i| {
                let (offset, size, align) =
                    (self.field_offsets[i], self.field_sizes[i], self.field_aligns[i]);
                align.is_power_of_two()
                    && offset % align == 0
                    && offset.checked_add(size).is_some_and(|end| end <= self.size)
            })
            && (0..n).all(|i| {
                (i + 1..n).all(|j| {
                    let (a, b) = (self.field_offsets[i], self.field_offsets[j]);
                    let (a_end, b_end) = (a + self.field_sizes[i], b + self.field_sizes[j]);
                    // Two sized fields may not share a byte.
                    self.field_sizes[i] == 0 || self.field_sizes[j] == 0 || a_end <= b || b_end <= a
                })
            })
    }
}

/// A body's tuple layouts: at most one row per distinct `Ty::Tuple`, all computed
/// for `target`.
///
/// SERDE DISCIPLINE, the `VerifiableBody::datatype_defs` rule: an EMPTY table is
/// exactly the pre-carrier meaning ("this body carries no tuple layout") and must
/// never reach the wire or stable hash material; a NON-empty table is
/// hash-visible, because two bodies that disagree on where a tuple's fields live
/// are different objects.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TupleLayouts {
    /// The target every row was computed for; `None` iff `entries` is empty.
    pub target: Option<LayoutTarget>,
    /// Rows in a canonical order (by the serialized tuple type), so the table's
    /// serialization is a function of its contents.
    pub entries: Vec<TupleLayoutInfo>,
}

impl TupleLayouts {
    /// No row: the pre-carrier meaning.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// The row for `tuple`, if the table has one and it is coherent.
    #[must_use]
    pub fn layout_of(&self, tuple: &Ty) -> Option<&TupleLayoutInfo> {
        self.entries.iter().find(|row| row.tuple == *tuple).filter(|row| row.is_coherent())
    }

    /// Build a table from rows recorded for one target. Rows are put in canonical
    /// order; a tuple recorded twice with DIFFERENT rows is dropped altogether
    /// (fail-closed: its field addresses then name no offset), and an incoherent
    /// row is dropped. A `None` target keeps the table empty.
    #[must_use]
    pub fn from_rows(target: Option<LayoutTarget>, rows: Vec<TupleLayoutInfo>) -> Self {
        let Some(target) = target else { return Self::default() };
        let mut keyed: Vec<(String, TupleLayoutInfo)> = Vec::with_capacity(rows.len());
        let mut conflicted: Vec<String> = Vec::new();
        for row in rows.into_iter().filter(TupleLayoutInfo::is_coherent) {
            let Ok(key) = serde_json::to_string(&row.tuple) else { continue };
            match keyed.iter().find(|(existing, _)| *existing == key) {
                Some((_, existing)) if *existing == row => {}
                Some(_) => conflicted.push(key),
                None => keyed.push((key, row)),
            }
        }
        keyed.retain(|(key, _)| !conflicted.contains(key));
        keyed.sort_by(|(left, _), (right, _)| left.cmp(right));
        if keyed.is_empty() {
            return Self::default();
        }
        Self { target: Some(target), entries: keyed.into_iter().map(|(_, row)| row).collect() }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn target() -> LayoutTarget {
        LayoutTarget { triple: "aarch64-apple-darwin".into(), pointer_size: 8, little_endian: true }
    }

    fn u32_u8(offsets: [u64; 2]) -> TupleLayoutInfo {
        TupleLayoutInfo {
            tuple: Ty::Tuple(vec![Ty::u32(), Ty::u8()]),
            size: 8,
            align: 4,
            field_offsets: offsets.to_vec(),
            field_sizes: vec![4, 1],
            field_aligns: vec![4, 1],
        }
    }

    #[test]
    fn a_coherent_row_is_served_and_an_incoherent_one_is_not() {
        let table = TupleLayouts::from_rows(Some(target()), vec![u32_u8([0, 4])]);
        assert_eq!(table.layout_of(&Ty::Tuple(vec![Ty::u32(), Ty::u8()])), Some(&u32_u8([0, 4])));
        // `u32` at byte 2 is misaligned: no layout, not a guess.
        let table = TupleLayouts::from_rows(Some(target()), vec![u32_u8([2, 0])]);
        assert!(table.is_empty(), "an incoherent row must not survive: {table:?}");
        // Two fields sharing byte 0 describe no layout either.
        let table = TupleLayouts::from_rows(Some(target()), vec![u32_u8([0, 0])]);
        assert!(table.is_empty(), "overlapping fields must not survive: {table:?}");
    }

    #[test]
    fn a_tuple_recorded_twice_with_different_layouts_has_no_layout() {
        let table = TupleLayouts::from_rows(Some(target()), vec![u32_u8([0, 4]), u32_u8([4, 0])]);
        assert!(table.is_empty(), "conflicting observations must drop the tuple: {table:?}");
        let table = TupleLayouts::from_rows(Some(target()), vec![u32_u8([0, 4]), u32_u8([0, 4])]);
        assert_eq!(table.entries.len(), 1, "an identical re-observation is one row");
    }

    #[test]
    fn no_target_means_no_table() {
        assert!(TupleLayouts::from_rows(None, vec![u32_u8([0, 4])]).is_empty());
    }
}

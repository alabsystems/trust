//! ALLOC-STRIDE-ADT-2 (2026-10-07): the COMPILER's element-size table for one
//! function — a LOWER bound of rustc's `size_of` for each lowered type key the
//! extractor produced, carried beside the function on [`crate::VcgenContext`]
//! and never inside it.
//!
//! WHY A SIDE TABLE. `trust_types::Ty` carries no layout on the verifier lane:
//! `Ty::Adt::layout` and `VerifiableFunction::tuple_layouts` are filled on the
//! faithful lane only, because a filled value is part of the content hash every
//! proof-certificate and census pin reads (the B3-4 T3 shield). The live-length
//! capacity lane (`generate::alloc_len`) still needs the size of a slice/`Vec`
//! SOURCE element to discharge `Vec::with_capacity(src.len())` over a
//! pointer-heavy element (clean-ck0's six rows), where the structural field-sum
//! bound of ALLOC-STRIDE-ADT-1 is near 0. This table is that size, from the same
//! compiler authority (`tcx.layout_of`) that already writes the target stride
//! `__trust_elem_bytes@N`.
//!
//! WHY IT CANNOT MOVE A HASH, STRUCTURALLY. [`ElemSizeTable`] has NO serde
//! derive, and neither does `VcgenContext`. Putting it inside any hashed or
//! serialized struct would fail to compile; it can never reach `stable_model_json`,
//! a fixture, a proof bundle or a certificate.
//!
//! WHY A DECODED FUNCTION NEVER HAS ONE. Only `rustc_mir_transform::trust_verify`
//! builds a table (through `trust_mir_extract::
//! extract_function_with_contract_bundle_and_elem_sizes`); a function decoded from
//! JSON, a fixture, a replayed bundle and every other caller of vcgen get none,
//! which answers `None` — the ADT-1 structural bound alone — exactly as before.
//!
//! THE BOUND. Every rustc preimage the extractor lowered to a key is recorded:
//! sized (`layout_of` under the #48 re-entrancy funnel, monomorphic, sized,
//! inhabited) as `Bytes(n)`, merged by MINIMUM, and anything else — generic,
//! unsized, alias, coroutine, layout error, uninhabited — as `Unknown`, which is
//! STICKY. So `lower_bound(K)` is either `None` or `min over every preimage R of K
//! of size_of(R)`, a lower bound of the size of whichever preimage the actual
//! element is. A zero-sized lower bound is `None`, as `alloc_len` treats a ZST.
//! The maximum observation is retained too: an exact physical stride is available
//! only when every recorded preimage has the same known size. A minimum alone
//! must never scale a memory access or pointer offset.

use trust_types::Ty;
use trust_types::fx::FxHashMap;

/// One key's recorded answer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Entry {
    /// Extrema of `size_of` over every preimage recorded so far.
    Bytes { min: u64, max: u64 },
    /// Some preimage could not be sized. Never leaves this state.
    Unknown,
}

impl Entry {
    fn from_size(size: Option<u64>) -> Self {
        size.map_or(Self::Unknown, |size| Self::Bytes { min: size, max: size })
    }

    fn merge(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bytes { min: a, max: b }, Self::Bytes { min: c, max: d }) => {
                Self::Bytes { min: a.min(c), max: b.max(d) }
            }
            _ => Self::Unknown,
        }
    }
}

/// The compiler's per-function element-size table. Deliberately NOT
/// `Serialize`/`Deserialize` (module docs).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ElemSizeTable {
    rows: FxHashMap<Ty, Entry>,
}

impl ElemSizeTable {
    /// An empty table: every lookup answers `None`.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Record that a preimage of `key` has `size` (`None`: could not be sized).
    /// Retains both extrema; a `None` poisons `key` for good.
    pub fn record(&mut self, key: Ty, size: Option<u64>) {
        let incoming = Entry::from_size(size);
        self.rows
            .entry(key)
            .and_modify(|entry| *entry = entry.merge(incoming))
            .or_insert(incoming);
    }

    /// [`Self::record`] without taking ownership: clones `key` only when it is
    /// new (the extractor calls this at every type-lowering exit).
    pub fn record_ref(&mut self, key: &Ty, size: Option<u64>) {
        let incoming = Entry::from_size(size);
        if let Some(entry) = self.rows.get_mut(key) {
            *entry = entry.merge(incoming);
        } else {
            self.rows.insert(key.clone(), incoming);
        }
    }

    /// A lower bound of `size_of` for every preimage of `key`: `Some(n)` with
    /// `n >= 1`, or `None` (no row, a poisoned row, or a zero-sized one).
    #[must_use]
    pub fn lower_bound(&self, key: &Ty) -> Option<u64> {
        match self.rows.get(key)? {
            Entry::Bytes { min, .. } if *min >= 1 => Some(*min),
            _ => None,
        }
    }

    /// Exact `size_of` only when every recorded preimage agrees. A zero-sized
    /// observation is exact too; an absent, poisoned or conflicting key is not.
    #[must_use]
    pub fn exact_size(&self, key: &Ty) -> Option<u64> {
        match self.rows.get(key)? {
            Entry::Bytes { min, max } if min == max => Some(*min),
            _ => None,
        }
    }

    /// An observed unknown/conflict must not fall back to a structural guess.
    pub(crate) fn has_record(&self, key: &Ty) -> bool {
        self.rows.contains_key(key)
    }

    /// No row at all.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    /// Number of keys recorded (sized or poisoned).
    #[must_use]
    pub fn len(&self) -> usize {
        self.rows.len()
    }

    /// A deterministic digest of the whole table, for the (observation-only) VC
    /// artifact cache key: rows sorted by their canonical model JSON. Never an
    /// identity of the function and never authority.
    #[must_use]
    pub fn stable_digest(&self) -> String {
        let mut rows: Vec<(Vec<u8>, Option<(u64, u64)>)> = self
            .rows
            .iter()
            .map(|(key, entry)| {
                let bytes = trust_types::stable_model_json_bytes(key)
                    .unwrap_or_else(|_| format!("{key:?}").into_bytes());
                let size = match entry {
                    Entry::Bytes { min, max } => Some((*min, *max)),
                    Entry::Unknown => None,
                };
                (bytes, size)
            })
            .collect();
        rows.sort_unstable();
        let cap = 31
            + rows
                .iter()
                .map(|(k, s)| 8 + k.len() + if s.is_some() { 17 } else { 1 })
                .sum::<usize>();
        let mut material = Vec::with_capacity(cap);
        material.extend_from_slice(b"trust.vcgen.elem-size-table.v2\0");
        for (key, size) in rows {
            material.extend_from_slice(&(key.len() as u64).to_le_bytes());
            material.extend_from_slice(&key);
            match size {
                Some((min, max)) => {
                    material.push(1);
                    material.extend_from_slice(&min.to_le_bytes());
                    material.extend_from_slice(&max.to_le_bytes());
                }
                None => material.push(0),
            }
        }
        trust_types::stable_sha256_hex(&material)
    }
}

/// The digest an [`ElemSizeTable`] is bound to: the parts of the function its
/// keys are read from — the local declarations, the return type and the
/// datatype-definition table — after the extractor's final stamp. A function
/// whose types were changed after the table was built (or another instance that
/// shares the def path) hashes differently, and the table is then ignored.
#[must_use]
pub fn elem_size_binding_digest(func: &trust_types::VerifiableFunction) -> Option<String> {
    let locals = trust_types::stable_model_json_bytes(&func.body.locals).ok()?;
    let ret = trust_types::stable_model_json_bytes(&func.body.return_ty).ok()?;
    let defs = trust_types::stable_model_json_bytes(&func.body.datatype_defs).ok()?;
    Some(trust_types::stable_sha256_hex_parts(&[
        b"trust.vcgen.elem-size-binding.v1\0",
        &(locals.len() as u64).to_le_bytes(),
        &locals,
        &(ret.len() as u64).to_le_bytes(),
        &ret,
        &defs,
    ]))
}

/// A table bound to the function it was built for.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ElemSizeBinding {
    pub(crate) table: ElemSizeTable,
    pub(crate) bound_digest: String,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tuple(n: u32) -> Ty {
        Ty::Tuple(vec![Ty::Int { width: n, signed: false }])
    }

    #[test]
    fn rows_merge_by_minimum() {
        let mut t = ElemSizeTable::new();
        t.record(tuple(8), Some(88));
        t.record(tuple(8), Some(64));
        t.record(tuple(8), Some(72));
        assert_eq!(t.lower_bound(&tuple(8)), Some(64));
        assert_eq!(t.lower_bound(&tuple(16)), None);
        let mut r = ElemSizeTable::new();
        r.record_ref(&tuple(8), Some(88));
        r.record_ref(&tuple(8), Some(64));
        r.record_ref(&tuple(8), Some(72));
        assert_eq!(r, t);
        r.record_ref(&tuple(8), None);
        assert_eq!(r.lower_bound(&tuple(8)), None);
    }

    #[test]
    fn an_unknown_preimage_poisons_its_key_for_good() {
        let mut t = ElemSizeTable::new();
        t.record(tuple(8), Some(88));
        t.record(tuple(8), None);
        t.record(tuple(8), Some(88));
        assert_eq!(t.lower_bound(&tuple(8)), None);
        let mut u = ElemSizeTable::new();
        u.record(tuple(8), None);
        u.record(tuple(8), Some(88));
        assert_eq!(u.lower_bound(&tuple(8)), None);
    }

    #[test]
    fn a_zero_sized_row_answers_none() {
        let mut t = ElemSizeTable::new();
        t.record(Ty::Tuple(vec![]), Some(0));
        assert_eq!(t.lower_bound(&Ty::Tuple(vec![])), None);
        // and a ZST preimage drags a shared key to 0 as well
        t.record(tuple(8), Some(8));
        t.record(tuple(8), Some(0));
        assert_eq!(t.lower_bound(&tuple(8)), None);
    }

    #[test]
    fn the_digest_is_order_independent_and_sees_every_row() {
        let mut a = ElemSizeTable::new();
        a.record(tuple(8), Some(1));
        a.record(tuple(16), Some(2));
        let mut b = ElemSizeTable::new();
        b.record(tuple(16), Some(2));
        b.record(tuple(8), Some(1));
        assert_eq!(a.stable_digest(), b.stable_digest());
        b.record(tuple(32), None);
        assert_ne!(a.stable_digest(), b.stable_digest());
        assert_ne!(ElemSizeTable::new().stable_digest(), a.stable_digest());
    }

    #[test]
    fn exact_sizes_require_every_preimage_to_agree() {
        let key = tuple(32);
        let mut table = ElemSizeTable::new();
        assert_eq!(table.exact_size(&key), None);
        table.record_ref(&key, Some(8));
        table.record(key.clone(), Some(8));
        assert_eq!(table.exact_size(&key), Some(8));
        table.record_ref(&key, Some(12));
        table.record(key.clone(), Some(8));
        assert_eq!(table.lower_bound(&key), Some(8));
        assert_eq!(table.exact_size(&key), None, "a minimum is not an exact stride");
    }

    #[test]
    fn unknown_preimages_never_recover_exact_sizes() {
        for observations in [[Some(8), None, Some(8)], [None, Some(8), Some(8)]] {
            let mut table = ElemSizeTable::new();
            for size in observations { table.record(tuple(32), size); }
            assert_eq!(table.exact_size(&tuple(32)), None);
            assert!(table.has_record(&tuple(32)), "unknown is distinct from absent");
        }
    }

    #[test]
    fn exact_zero_is_distinct_from_a_nonzero_allocation_lower_bound() {
        let key = Ty::Tuple(vec![]);
        let mut table = ElemSizeTable::new();
        table.record(key.clone(), Some(0));
        assert_eq!(table.exact_size(&key), Some(0));
        assert_eq!(table.lower_bound(&key), None);
        table.record(key.clone(), Some(8));
        assert_eq!(table.exact_size(&key), None);
        assert_eq!(table.lower_bound(&key), None);
    }

    #[test]
    fn the_digest_distinguishes_exact_and_conflicting_equal_minima() {
        let mut exact = ElemSizeTable::new();
        exact.record(tuple(32), Some(8));
        let mut conflicting = exact.clone();
        conflicting.record(tuple(32), Some(12));
        assert_eq!(exact.lower_bound(&tuple(32)), conflicting.lower_bound(&tuple(32)));
        assert_ne!(exact.stable_digest(), conflicting.stable_digest());
        let mut reverse = ElemSizeTable::new();
        reverse.record(tuple(32), Some(12));
        reverse.record(tuple(32), Some(8));
        assert_eq!(conflicting.stable_digest(), reverse.stable_digest());
    }
}

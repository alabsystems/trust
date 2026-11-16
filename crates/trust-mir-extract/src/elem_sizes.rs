//! ALLOC-STRIDE-ADT-2 (2026-10-07): rustc's element sizes for the VERIFIER lane, as a
//! side table that never enters the extracted function.
//!
//! `trust_vcgen::ElemSizeTable` maps a LOWERED type key to a lower bound of
//! `size_of` over every rustc type this extraction lowered to that key. It is filled
//! here, by a recorder that wraps EVERY exit of `ty_convert::convert_ty_inner`
//! (memo hits, cut markers and budget bails included), PLUS the one post-lowering
//! rewrite that mints a consulted key at a sized position — Lever A's field
//! compaction (`compact_oversized_field`, whose call sites call
//! [`record_compacted`]) — so every rustc preimage of a key at a position the
//! consumer sizes is seen. (The 2026-10-07 review found the compaction gap: a
//! compacted field's erased-name marker is shared with cut points of a same-named
//! ADT of another crate and with back-edges of another generic instantiation, and
//! was read with THEIR row. Lever-A child refs inside `Datatype.variants`
//! (`datatype_child_field_ty`) stay unrecorded: the consumer never sizes a
//! position inside a `Datatype`'s variants.) It is handed to vcgen on `VcgenContext` by the compiler's TrustVerify
//! site only (`extract_function_with_contract_bundle_and_elem_sizes`).
//!
//! HASH-INVISIBLE BY CONSTRUCTION: the recorder only READS `(rustc type, lowered
//! type)` pairs after the lowering returned and never changes the lowered type, and
//! the table lives outside `VerifiableFunction` (it has no serde impl at all). The
//! lowering — and so every content hash, census key and proof-certificate pin — is
//! byte-identical with the scope open or closed (`elem_sizes_tests` in this crate's
//! test suite measures it).
//!
//! THE SIZE: `Some(layout.size)` only for a type the #48 re-entrancy funnel's check
//! admits (`ctfe_reentrancy::layout_query_is_reentrant_safe`: no parameter, inference
//! variable, placeholder, alias, coroutine or coroutine witness anywhere) through the
//! fields of every local ADT it names, TRANSITIVELY (`reentrant_safe_unbounded`: the
//! deep funnel without its six-level cap), laid out under the fully-monomorphized
//! environment (exact for such a type, as `tuple_layouts::cycle_safe_layout_of`), sized,
//! inhabited and not zero-sized. Every other preimage records `None`, which POISONS its
//! key for good. Generic means absent; absent means the stride stays the structural
//! bound, which keeps the row.

use std::cell::{Cell, RefCell};

use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use trust_types::Ty as TrustTy;
use trust_types::fx::{FxHashMap, FxHashSet};
use trust_vcgen::ElemSizeTable;

#[derive(Default)]
struct Collector {
    /// A table is being collected for the extraction that opened the scope.
    active: bool,
    table: ElemSizeTable,
    /// Scope-wide memo of `sound_size_of` keyed by `crate::interned_ty_identity(ty)`.
    /// Cleared with the scope on entry and drop so one extraction's `Ty<'tcx>`
    /// pointer addresses never outlive its `TyCtxt<'tcx>`.
    size_by_ty_id: FxHashMap<usize, Option<u64>>,
}

thread_local! {
    static ACTIVE: Cell<bool> = const { Cell::new(false) };
    static COLLECTOR: RefCell<Collector> = RefCell::new(Collector::default());
}

/// RAII scope for ONE extraction's element-size table. It SAVES the enclosing
/// collector and RESTORES it on drop, so a nested extraction neither inherits the
/// outer table nor writes into it; an INACTIVE scope (every extraction that did not
/// ask for a table) suspends recording for its own duration.
pub(crate) struct ElemSizeScope {
    prev: Option<Collector>,
}

impl ElemSizeScope {
    pub(crate) fn begin(active: bool) -> Self {
        crate::ty_convert::bump_extraction_scope_epoch();
        ACTIVE.set(active);
        let prev = COLLECTOR.with(|c| {
            c.replace(Collector {
                active,
                table: ElemSizeTable::default(),
                size_by_ty_id: FxHashMap::default(),
            })
        });
        ElemSizeScope { prev: Some(prev) }
    }

    /// The table recorded so far in THIS scope.
    pub(crate) fn take_table(&self) -> ElemSizeTable {
        COLLECTOR.with(|c| std::mem::take(&mut c.borrow_mut().table))
    }
}

impl Drop for ElemSizeScope {
    fn drop(&mut self) {
        if let Some(prev) = self.prev.take() {
            crate::ty_convert::bump_extraction_scope_epoch();
            ACTIVE.set(prev.active);
            COLLECTOR.with(|c| *c.borrow_mut() = prev);
        }
    }
}

/// The key shapes the consumer (`trust_vcgen::generate::alloc_len`) consults: an
/// extractor-minted ADT, a tuple, an array, a datatype. Nothing else is recorded.
fn consulted_shape(lowered: &TrustTy) -> bool {
    match lowered {
        TrustTy::Adt { adt_kind, .. } => adt_kind.is_some(),
        TrustTy::Tuple(_) | TrustTy::Array { .. } | TrustTy::Datatype { .. } => true,
        _ => false,
    }
}

/// The #48 re-entrancy funnel's question
/// (`ctfe_reentrancy::layout_query_is_reentrant_safe_deep`) WITHOUT its six-level
/// cap: does every type reachable from `ty` — `ty` itself and, transitively, the
/// fields of every LOCAL ADT any of them names — pass the funnel's own-flags check
/// (`layout_query_is_reentrant_safe`: nothing generic, inferred, placeholder,
/// aliased, coroutine or coroutine witness, no escaping bound vars)?
///
/// MEASURED 2026-10-07: the capped walk answered `false` for clean-ck0's `Term`
/// (`Term -> TermKind -> Level -> LevelKind -> Name -> NameRepr -> NameNode`, seven
/// local ADTs deep through `Arc`), so every source element that names a `Term`
/// was poisoned and none of the six rows moved. The cap is a cost bound, not part
/// of the funnel's argument: a deeper walk checks strictly MORE types with the same
/// predicate. Termination here comes from a visited set over the instantiated ADT
/// types (a recursive type is expanded once) and a budget of expanded ADTs that
/// fails closed (polymorphic recursion can name unboundedly many instantiations).
/// Field types are read unnormalized, exactly as the funnel reads them.
fn reentrant_safe_unbounded<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    const MAX_EXPANDED_ADTS: usize = 4096;
    let mut expanded: FxHashSet<ty::Ty<'tcx>> = FxHashSet::default();
    let mut current = Some(ty);
    let mut work: Vec<ty::Ty<'tcx>> = Vec::new();
    while let Some(t) = current.take().or_else(|| work.pop()) {
        if !crate::ctfe_reentrancy::layout_query_is_reentrant_safe(t) {
            return false;
        }
        if !crate::ctfe_reentrancy::walk_types_until(t, |inner| {
            let ty::Adt(def, args) = inner.kind() else { return true };
            if !def.did().is_local() || !expanded.insert(inner) {
                return true;
            }
            if expanded.len() > MAX_EXPANDED_ADTS {
                return false;
            }
            for field in def.all_fields() {
                work.push(tcx.type_of(field.did).instantiate(tcx, args).skip_normalization());
            }
            true
        }) {
            return false;
        }
    }
    true
}

/// rustc's size of `ty`, or `None` when it is not a sound, nonzero answer (module docs).
/// The question is asked under the fully-monomorphized environment, exactly as
/// `tuple_layouts::cycle_safe_layout_of` asks it, behind the uncapped funnel above.
fn sound_size_of<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> Option<u64> {
    let ty = tcx.erase_and_anonymize_regions(ty);
    if ty.has_escaping_bound_vars() || !reentrant_safe_unbounded(tcx, ty) {
        return None;
    }
    let layout = tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty)).ok()?;
    if !layout.is_sized() || layout.is_uninhabited() {
        return None;
    }
    Some(layout.size.bytes()).filter(|&n| n >= 1)
}

/// Record that `ty` lowered to `lowered`. A no-op unless an ACTIVE scope is open and
/// `lowered` has a consulted shape. The size answer is memoized per interned rustc type
/// across the entire active [`ElemSizeScope`].
pub(crate) fn record<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>, lowered: &TrustTy) {
    if !ACTIVE.get() || !consulted_shape(lowered) {
        return;
    }
    let ty_id = crate::interned_ty_identity(ty);
    let hit = COLLECTOR.with(|c| {
        let mut c = c.borrow_mut();
        if let Some(&size) = c.size_by_ty_id.get(&ty_id) {
            c.table.record_ref(lowered, size);
            true
        } else {
            false
        }
    });
    if hit {
        return;
    }
    let computed = sound_size_of(tcx, ty);
    COLLECTOR.with(|c| {
        let mut c = c.borrow_mut();
        c.size_by_ty_id.insert(ty_id, computed);
        c.table.record_ref(lowered, computed);
    });
}

/// Record the preimage of a COMPACTED field (`ty_convert::compact_oversized_field`,
/// Lever A). Compaction rewrites a field AFTER `convert_ty_inner` returned, into a
/// by-name marker key (`Datatype { name: <erased path>, variants: [] }` or
/// `__trust_compacted_aggregate`) that the wrapper never saw paired with this field's
/// rustc type — and that key is shared with every cut point, back-edge guard and
/// other compaction of the same erased name, INCLUDING a same-named ADT of another
/// crate (bin `foo` / lib `foo`) or another instantiation of a generic. Unrecorded,
/// the marker read another preimage's row: a false lower bound (review 2026-10-07).
///
/// * A TOP-LEVEL marker (the field was an `Adt`, a `Datatype` or anything else): its
///   one preimage here is `field_ty` itself, recorded like any lowering exit — so
///   it MIN-merges into, or poisons, the shared key.
/// * A marker under a `Ref`/`RawPtr` (compaction keeps the pointer and compacts the
///   pointee): its preimage is a pointee this function does not re-derive, so every
///   consulted key in the compacted subtree is POISONED (fail closed). The consumer
///   never sizes a pointee, so this loses no row it could discharge.
pub(crate) fn record_compacted<'tcx>(
    tcx: TyCtxt<'tcx>,
    field_ty: ty::Ty<'tcx>,
    compacted: &TrustTy,
) {
    if !ACTIVE.get() {
        return;
    }
    match compacted {
        TrustTy::Ref { inner: pointee, .. } | TrustTy::RawPtr { pointee, .. } => {
            poison_consulted_keys(pointee);
        }
        top => record(tcx, field_ty, top),
    }
}

/// Poison every consulted key in `ty` (a compacted pointee: only `Ref`/`RawPtr`
/// wrappers around one marker, but walked generally so a future compaction shape
/// cannot slip a key past).
fn poison_consulted_keys(ty: &TrustTy) {
    COLLECTOR.with(|c| {
        let mut c = c.borrow_mut();
        let mut current = Some(ty);
        let mut work: Vec<&TrustTy> = Vec::new();
        while let Some(t) = current.take().or_else(|| work.pop()) {
            if consulted_shape(t) {
                c.table.record_ref(t, None);
            }
            match t {
                TrustTy::Ref { inner, .. } => current = Some(inner),
                TrustTy::RawPtr { pointee, .. } => current = Some(pointee),
                TrustTy::Tuple(fields) => work.extend(fields.iter()),
                TrustTy::Array { elem, .. } => current = Some(elem),
                _ => {}
            }
        }
    });
}

/// Is a table being collected on this thread now (tests).
#[cfg(test)]
pub(crate) fn active() -> bool {
    ACTIVE.get()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key() -> TrustTy {
        TrustTy::Tuple(vec![TrustTy::Int { width: 64, signed: false }])
    }

    #[test]
    fn a_nested_scope_saves_and_restores_the_outer_table() {
        let outer = ElemSizeScope::begin(true);
        COLLECTOR.with(|c| c.borrow_mut().table.record_ref(&key(), Some(8)));
        {
            // A nested extraction that did not ask for a table: recording is
            // suspended and the outer rows are invisible to it.
            let inner = ElemSizeScope::begin(false);
            assert!(!active());
            assert!(inner.take_table().is_empty());
        }
        {
            // A nested extraction that DID ask: it starts empty and its rows do
            // not leak into the outer table.
            let inner = ElemSizeScope::begin(true);
            COLLECTOR.with(|c| c.borrow_mut().table.record_ref(&key(), None));
            assert_eq!(inner.take_table().lower_bound(&key()), None);
        }
        assert!(active());
        let table = outer.take_table();
        assert_eq!(table.lower_bound(&key()), Some(8));
        drop(outer);
        assert!(!active());
    }

    #[test]
    fn only_consulted_shapes_are_keys() {
        assert!(consulted_shape(&key()));
        assert!(consulted_shape(&TrustTy::Array { elem: Box::new(key()), len: 2 }));
        assert!(consulted_shape(&TrustTy::Datatype { name: "d".into(), variants: vec![] }));
        assert!(!consulted_shape(&TrustTy::Int { width: 8, signed: false }));
        assert!(!consulted_shape(&TrustTy::Ref { mutable: false, inner: Box::new(key()) }));
        assert!(!consulted_shape(&TrustTy::Unsupported { kind: "k".into(), detail: "d".into() }));
        assert!(!consulted_shape(&TrustTy::adt("hand::Built", vec![])));
    }
}

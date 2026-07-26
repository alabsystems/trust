//! Witness decode + re-intern.
//!
//! Inverts `encode::encode_root`: parses a per-root witness (magic + type table
//! + body) and reconstructs an owned `ty::TypeckResults<'tcx>`, re-interned in
//! the *given* `tcx`. Every `Ty` is rebuilt via `Ty::new_*` / `tcx.mk_args` and
//! every embedded `DefId` is resolved via `tcx.def_path_hash_to_def_id` — where
//! `None` (a def that no longer exists / shifted crate) is a clean cache miss,
//! never a panic (`context.rs:1457`). Regions come back as `tcx.lifetimes.re_erased`
//! (`context.rs:401`), matching the post-writeback cold form.
//!
//! FAIL-SAFE: any structural error — a short buffer, an out-of-range type index,
//! an unknown tag, a `DefPathHash` that no longer resolves — returns `None`, and
//! the compiler falls through to real typeck. The reconstructed result is a
//! *candidate* only; the mandatory linear checker (PLAN.md §6) is the authority
//! that decides whether it may be used.
//!
//! The type table is built in index order into a `Vec<Ty>`. The encoder emits
//! each distinct region-erased type once with its children BEFORE its parents
//! (child index < parent index), so every by-index child reference resolves
//! against an already-built prefix of the vec.
//!
//! ## v1 reconstruction fidelity (honest gaps)
//!
//! `adjustments` is rebuilt exactly (enriched record). The remaining lossy
//! fields — inherited from the Phase-0 byte format, unchanged here — are:
//! `pat_binding_modes` (mode byte is a placeholder → rebuilt as
//! `BindingMode::NONE`), `pat_adjustments` (kind byte is a placeholder →
//! rebuilt as `PatAdjust::BuiltinDeref`), and `liberated_fn_sigs` (no
//! safety/abi/variadic → rebuilt as safe / `extern "Rust"` / non-variadic).
//! These are faithful for the straight-line, match-ergonomics-free, safe-Rust
//! v1 enabled set; widening beyond it requires enriching those records (or
//! excluding non-default cases at mint time). See the crate integration notes.

use rustc_abi::{ExternAbi, FieldIdx};
use rustc_data_structures::fingerprint::Fingerprint;
use rustc_hir::def::{CtorKind, DefKind};
use rustc_hir::def_id::{DefPathHash, LocalDefId};
use rustc_hir::{BindingMode, HirId, ItemLocalId, Mutability, OwnerId, Safety};
use rustc_middle::ty::adjustment::{
    Adjust, Adjustment, AllowTwoPhase, AutoBorrow, AutoBorrowMutability, DerefAdjustKind,
    PatAdjust, PatAdjustment, PointerCoercion,
};
use rustc_middle::ty::{self, GenericArg, GenericArgsRef, Ty, TyCtxt};
use rustc_span::Symbol;

/// `ty::IntTy as u8` inverse (rustc_ast_ir declaration order).
const INT_TYS: [ty::IntTy; 6] = [
    ty::IntTy::Isize,
    ty::IntTy::I8,
    ty::IntTy::I16,
    ty::IntTy::I32,
    ty::IntTy::I64,
    ty::IntTy::I128,
];
const UINT_TYS: [ty::UintTy; 6] = [
    ty::UintTy::Usize,
    ty::UintTy::U8,
    ty::UintTy::U16,
    ty::UintTy::U32,
    ty::UintTy::U64,
    ty::UintTy::U128,
];
const FLOAT_TYS: [ty::FloatTy; 4] =
    [ty::FloatTy::F16, ty::FloatTy::F32, ty::FloatTy::F64, ty::FloatTy::F128];

/// A bounds-checked little-endian byte cursor. Every read returns `Option`; a
/// short buffer yields `None`, which propagates to a fail-safe decode miss.
struct Cursor<'a> {
    b: &'a [u8],
    o: usize,
}

impl<'a> Cursor<'a> {
    fn new(b: &'a [u8]) -> Self {
        Cursor { b, o: 0 }
    }

    fn u8(&mut self) -> Option<u8> {
        let v = *self.b.get(self.o)?;
        self.o += 1;
        Some(v)
    }

    fn u16(&mut self) -> Option<u16> {
        let v = u16::from_le_bytes(self.b.get(self.o..self.o + 2)?.try_into().ok()?);
        self.o += 2;
        Some(v)
    }

    fn u32(&mut self) -> Option<u32> {
        let v = u32::from_le_bytes(self.b.get(self.o..self.o + 4)?.try_into().ok()?);
        self.o += 4;
        Some(v)
    }

    fn u64(&mut self) -> Option<u64> {
        let v = u64::from_le_bytes(self.b.get(self.o..self.o + 8)?.try_into().ok()?);
        self.o += 8;
        Some(v)
    }

    fn bytes(&mut self, n: usize) -> Option<&'a [u8]> {
        let s = self.b.get(self.o..self.o + n)?;
        self.o += n;
        Some(s)
    }

    fn is_eof(&self) -> bool {
        self.o == self.b.len()
    }

    /// Read a full 128-bit `DefPathHash` (`Fingerprint::from_le_bytes`).
    fn dph(&mut self) -> Option<DefPathHash> {
        let arr: [u8; 16] = self.bytes(16)?.try_into().ok()?;
        Some(DefPathHash(Fingerprint::from_le_bytes(arr)))
    }
}

fn mut_of(x: u8) -> Option<Mutability> {
    match x {
        0 => Some(Mutability::Not),
        1 => Some(Mutability::Mut),
        _ => None,
    }
}

/// Look up an already-built type by table index.
fn ty_at<'tcx>(tys: &[Ty<'tcx>], idx: u32) -> Option<Ty<'tcx>> {
    tys.get(idx as usize).copied()
}

/// Rebuild a generic-args list (`encode_args` inverse). Only `Type` and
/// `Lifetime` args exist in the grammar; const args escape at encode time.
fn build_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    c: &mut Cursor<'_>,
    tys: &[Ty<'tcx>],
) -> Option<GenericArgsRef<'tcx>> {
    let n = c.u8()? as usize;
    let mut v: Vec<GenericArg<'tcx>> = Vec::with_capacity(n);
    for _ in 0..n {
        let k = c.u8()?;
        match k {
            0 => v.push(ty_at(tys, c.u32()?)?.into()),
            1 => v.push(tcx.lifetimes.re_erased.into()),
            _ => return None,
        }
    }
    Some(tcx.mk_args(&v))
}

/// Rebuild one type-table entry, resolving by-index child references against
/// the already-built prefix `tys`. Re-interns via `Ty::new_*` / `mk_args`.
fn build_ty<'tcx>(tcx: TyCtxt<'tcx>, entry: &[u8], tys: &[Ty<'tcx>]) -> Option<Ty<'tcx>> {
    let mut c = Cursor::new(entry);
    let re = tcx.lifetimes.re_erased;
    let tag = c.u8()?;
    let ty = match tag {
        0 => tcx.types.bool,
        1 => tcx.types.char,
        2 => Ty::new_int(tcx, *INT_TYS.get(c.u8()? as usize)?),
        3 => Ty::new_uint(tcx, *UINT_TYS.get(c.u8()? as usize)?),
        4 => Ty::new_float(tcx, *FLOAT_TYS.get(c.u8()? as usize)?),
        5 => tcx.types.str_,
        6 => tcx.types.never,
        7 => {
            let n = c.u16()? as usize;
            let mut elems: Vec<Ty<'tcx>> = Vec::with_capacity(n);
            for _ in 0..n {
                elems.push(ty_at(tys, c.u32()?)?);
            }
            Ty::new_tup(tcx, &elems)
        }
        8 => {
            let m = mut_of(c.u8()?)?;
            let p = ty_at(tys, c.u32()?)?;
            Ty::new_ref(tcx, re, p, m)
        }
        9 => {
            let m = mut_of(c.u8()?)?;
            let p = ty_at(tys, c.u32()?)?;
            Ty::new_ptr(tcx, p, m)
        }
        10 => {
            let e = ty_at(tys, c.u32()?)?;
            Ty::new_slice(tcx, e)
        }
        11 => {
            let e = ty_at(tys, c.u32()?)?;
            let len = c.u64()?;
            Ty::new_array(tcx, e, len)
        }
        12 => {
            let dph = c.dph()?;
            let did = tcx.def_path_hash_to_def_id(dph)?;
            if !matches!(tcx.def_kind(did), DefKind::Struct | DefKind::Union | DefKind::Enum) {
                return None;
            }
            let args = build_args(tcx, &mut c, tys)?;
            if !tcx.check_args_compatible(did, args) {
                return None;
            }
            Ty::new_adt(tcx, tcx.adt_def(did), args)
        }
        13 => {
            let dph = c.dph()?;
            let did = tcx.def_path_hash_to_def_id(dph)?;
            if !matches!(
                tcx.def_kind(did),
                DefKind::Fn | DefKind::AssocFn | DefKind::Ctor(_, CtorKind::Fn)
            ) {
                return None;
            }
            let args = build_args(tcx, &mut c, tys)?;
            if !tcx.check_args_compatible(did, args) {
                return None;
            }
            Ty::new_fn_def(tcx, did, args)
        }
        14 => {
            let unsafe_ = c.u8()?;
            // Scope-widening (schema v4): the fn-pointer ABI is round-tripped.
            let abi_packed = c.u8()?;
            let ninputs = c.u8()? as usize;
            let mut ins: Vec<Ty<'tcx>> = Vec::with_capacity(ninputs);
            for _ in 0..ninputs {
                ins.push(ty_at(tys, c.u32()?)?);
            }
            let out = ty_at(tys, c.u32()?)?;
            let safety = match unsafe_ {
                0 => Safety::Safe,
                1 => Safety::Unsafe,
                _ => return None,
            };
            let n_ins = ins.len();
            let sig = ty::FnSig {
                inputs_and_output: tcx.mk_type_list_from_iter(ins.into_iter().chain([out])),
                fn_sig_kind: ty::FnSigKind::new(
                    ExternAbi::from_packed(abi_packed),
                    safety,
                    false,
                    None,
                    n_ins,
                )
                .ok()?,
            };
            Ty::new_fn_ptr(tcx, ty::Binder::dummy(sig))
        }
        15 => {
            let idx = c.u32()?;
            let nl = c.u8()? as usize;
            let nm = std::str::from_utf8(c.bytes(nl)?).ok()?;
            Ty::new_param(tcx, idx, Symbol::intern(nm))
        }
        // 255 is the encoder's escape placeholder (never present in a committed
        // witness); any unknown tag is a fail-safe miss.
        _ => return None,
    };
    // Type-table entries are length-delimited. Reject ignored suffix bytes so
    // corrupt lengths and truncated compact fields cannot become alternate,
    // non-canonical encodings of a different type.
    if !c.is_eof() {
        return None;
    }
    Some(ty)
}

/// Invert `encode_adjustment`: `(kind_byte, payload_byte?, target)` → `Adjustment`.
fn rebuild_adjust<'tcx>(
    kind_byte: u8,
    payload: Option<u8>,
    target: Ty<'tcx>,
) -> Option<Adjustment<'tcx>> {
    let kind = match kind_byte {
        0 => Adjust::NeverToAny,
        1 => match payload? {
            0 => Adjust::Deref(DerefAdjustKind::Builtin),
            _ => return None,
        },
        2 => Adjust::Borrow(match payload? {
            0 => AutoBorrow::Ref(AutoBorrowMutability::Not),
            1 => AutoBorrow::Ref(AutoBorrowMutability::Mut {
                allow_two_phase_borrow: AllowTwoPhase::No,
            }),
            2 => AutoBorrow::Ref(AutoBorrowMutability::Mut {
                allow_two_phase_borrow: AllowTwoPhase::Yes,
            }),
            3 => AutoBorrow::RawPtr(Mutability::Not),
            4 => AutoBorrow::RawPtr(Mutability::Mut),
            5 => AutoBorrow::Pin(Mutability::Not),
            6 => AutoBorrow::Pin(Mutability::Mut),
            _ => return None,
        }),
        3 => Adjust::Pointer(match payload? {
            0 => PointerCoercion::ReifyFnPointer(Safety::Safe),
            1 => PointerCoercion::ReifyFnPointer(Safety::Unsafe),
            2 => PointerCoercion::UnsafeFnPointer,
            3 => PointerCoercion::ClosureFnPointer(Safety::Safe),
            4 => PointerCoercion::ClosureFnPointer(Safety::Unsafe),
            5 => PointerCoercion::MutToConstPointer,
            6 => PointerCoercion::ArrayToPointer,
            7 => PointerCoercion::Unsize,
            _ => return None,
        }),
        4 => Adjust::GenericReborrow(match payload? {
            0 => Mutability::Not,
            1 => Mutability::Mut,
            _ => return None,
        }),
        _ => return None,
    };
    Some(Adjustment { kind, target })
}

/// Parse a witness and reconstruct an owned `TypeckResults`, re-interned in
/// `tcx`. Returns `None` on any structural error (fail-safe).
pub fn decode_and_reintern<'tcx>(
    tcx: TyCtxt<'tcx>,
    root: LocalDefId,
    bytes: &[u8],
) -> Option<ty::TypeckResults<'tcx>> {
    let mut c = Cursor::new(bytes);

    // magic
    if c.bytes(4)? != crate::schema::WITNESS_MAGIC {
        return None;
    }

    // type table — build in index order (children precede parents).
    let n_types = c.u32()? as usize;
    // Every entry consumes at least its u16 length plus one tag byte. Bound
    // allocation by the actual payload so a four-byte corrupt count cannot
    // request an attacker-sized Vec before the cursor detects EOF.
    if n_types > bytes.len() / 3 {
        return None;
    }
    let mut tys: Vec<Ty<'tcx>> = Vec::with_capacity(n_types);
    for _ in 0..n_types {
        let len = c.u16()? as usize;
        let entry = c.bytes(len)?;
        let t = build_ty(tcx, entry, &tys)?;
        tys.push(t);
    }

    // body — build the candidate result. `hir_owner` re-derived from the root
    // so every inserted HirId's owner matches (validate_hir_id_for_typeck_results).
    let hir_owner = OwnerId { def_id: root };
    let owner_nodes = tcx.hir_owner_nodes(hir_owner);
    let mut tr = ty::TypeckResults::new(hir_owner);
    let hid = |local: u32| {
        let local_id = ItemLocalId::from_u32(local);
        owner_nodes.nodes.get(local_id)?;
        Some(HirId { owner: hir_owner, local_id })
    };

    // node_types
    let n = c.u32()?;
    for _ in 0..n {
        let id = c.u32()?;
        let t = ty_at(&tys, c.u32()?)?;
        if tr.node_types_mut().insert(hid(id)?, t).is_some() {
            return None;
        }
    }

    // node_args
    let n = c.u32()?;
    for _ in 0..n {
        let id = c.u32()?;
        let args = build_args(tcx, &mut c, &tys)?;
        if tr.node_args_mut().insert(hid(id)?, args).is_some() {
            return None;
        }
    }

    // field_indices
    let n = c.u32()?;
    for _ in 0..n {
        let id = c.u32()?;
        let fi = c.u32()?;
        if tr.field_indices_mut().insert(hid(id)?, FieldIdx::from_u32(fi)).is_some() {
            return None;
        }
    }

    // adjustments (enriched record → faithful Adjustment)
    let n = c.u32()?;
    for _ in 0..n {
        let id = c.u32()?;
        let nsteps = c.u8()? as usize;
        let mut steps: Vec<Adjustment<'tcx>> = Vec::with_capacity(nsteps);
        for _ in 0..nsteps {
            let kind_byte = c.u8()?;
            let payload = if (1..=4).contains(&kind_byte) { Some(c.u8()?) } else { None };
            let target = ty_at(&tys, c.u32()?)?;
            steps.push(rebuild_adjust(kind_byte, payload, target)?);
        }
        if tr.adjustments_mut().insert(hid(id)?, steps).is_some() {
            return None;
        }
    }

    // pat_binding_modes (placeholder byte in v1 → default binding mode)
    let n = c.u32()?;
    for _ in 0..n {
        let id = c.u32()?;
        let _mode = c.u8()?;
        if tr.pat_binding_modes_mut().insert(hid(id)?, BindingMode::NONE).is_some() {
            return None;
        }
    }

    // pat_adjustments (placeholder kind byte in v1 → BuiltinDeref + source)
    let n = c.u32()?;
    for _ in 0..n {
        let id = c.u32()?;
        let nsteps = c.u8()? as usize;
        let mut steps: Vec<PatAdjustment<'tcx>> = Vec::with_capacity(nsteps);
        for _ in 0..nsteps {
            let _kind = c.u8()?;
            let source = ty_at(&tys, c.u32()?)?;
            steps.push(PatAdjustment { kind: PatAdjust::BuiltinDeref, source });
        }
        if tr.pat_adjustments_mut().insert(hid(id)?, steps).is_some() {
            return None;
        }
    }

    // liberated_fn_sigs (no safety/abi/variadic in the format → safe/Rust/non-variadic)
    let n = c.u32()?;
    for _ in 0..n {
        let id = c.u32()?;
        let ninputs = c.u8()? as usize;
        let mut ins: Vec<Ty<'tcx>> = Vec::with_capacity(ninputs);
        for _ in 0..ninputs {
            ins.push(ty_at(&tys, c.u32()?)?);
        }
        let out = ty_at(&tys, c.u32()?)?;
        let n_ins = ins.len();
        let sig = ty::FnSig {
            inputs_and_output: tcx.mk_type_list_from_iter(ins.into_iter().chain([out])),
            fn_sig_kind: ty::FnSigKind::new(ExternAbi::Rust, Safety::Safe, false, None, n_ins)
                .ok()?,
        };
        if tr.liberated_fn_sigs_mut().insert(hid(id)?, sig).is_some() {
            return None;
        }
    }

    // fru_field_types
    let n = c.u32()?;
    for _ in 0..n {
        let id = c.u32()?;
        let ntys = c.u8()? as usize;
        let mut v: Vec<Ty<'tcx>> = Vec::with_capacity(ntys);
        for _ in 0..ntys {
            v.push(ty_at(&tys, c.u32()?)?);
        }
        if tr.fru_field_types_mut().insert(hid(id)?, v).is_some() {
            return None;
        }
    }

    // coercion_casts (id set)
    let n = c.u32()?;
    for _ in 0..n {
        let id = c.u32()?;
        let local_id = ItemLocalId::from_u32(id);
        owner_nodes.nodes.get(local_id)?;
        if tr.coercion_casts().contains(&local_id) {
            return None;
        }
        tr.set_coercion_cast(local_id);
    }

    // type_dependent_defs (Follow-on 2): the method/operator picks. Gated on the
    // fail-closed interlock — if method-pick admission is not sound under the
    // current key, a store carrying picks forces a decode MISS (-> real typeck).
    let n = c.u32()?;
    if n > 0 && !crate::key::METHOD_PICKS_SOUND_UNDER_CURRENT_KEY {
        return None;
    }
    for _ in 0..n {
        let id = c.u32()?;
        let dph = c.dph()?;
        // `None` (def gone / shifted) => fail-safe miss, same discipline as ADT.
        let did = tcx.def_path_hash_to_def_id(dph)?;
        if !matches!(tcx.def_kind(did), DefKind::AssocFn) {
            return None;
        }
        if tr.type_dependent_defs_mut().insert(hid(id)?, Ok((DefKind::AssocFn, did))).is_some() {
            return None;
        }
    }

    // used_trait_imports (Follow-on 2): local trait-import DefIds, for lint parity.
    let n = c.u32()?;
    for _ in 0..n {
        let dph = c.dph()?;
        let local = tcx.def_path_hash_to_def_id(dph)?.as_local()?;
        if tr.used_trait_imports.contains(&local) {
            return None;
        }
        tr.used_trait_imports.insert(local);
    }

    // The body has no extension area in this schema. Silent suffix acceptance
    // would hide a corrupt count/length and make multiple byte strings decode
    // to the same candidate, weakening the structural fail-closed boundary.
    c.is_eof().then_some(tr)
}

//! Replay-capable witness encoder.
//!
//! Ported from the P0 prototype (`reports/typeck-moonshot/p0/replay_checker.rs`,
//! `WitnessEncoder` + `encode_full_typeck_results`), with one load-bearing
//! change per PLAN.md §3: every `DefId` is stored as its FULL 128-bit
//! `DefPathHash` (`Fingerprint::to_le_bytes`), not the size-only 64-bit
//! `to_smaller_hash`, so the decoder can look the def back up with
//! `def_path_hash_to_def_id`.
//!
//! The encoder is TOTAL but PARTIAL: any type outside the re-internable
//! grammar makes `encode_root` return `None`, and that root is simply not
//! minted (the per-field fallback of PLAN.md §5 / constraint 1).
//!
//! Phase 1 enrichment (reconstruction-notes.md): the adjustment record now
//! carries a `kind_byte` (+ a `payload_byte` for kinds 1..=4) before the target
//! type index, so `decode` can rebuild the exact `ty::adjustment::Adjust`
//! (Borrow's Ref/RawPtr/Pin + mutability + two-phase, Pointer's coercion variant
//! + fn-pointer safety, ReborrowPin's mutability, builtin Deref). Overloaded /
//! Pin deref is not reconstructible in v1 and marks the root non-mintable. Every
//! other field's byte format is unchanged from Phase 0.

use rustc_data_structures::fx::FxHashMap;
use rustc_hir::HirId;
use rustc_middle::ty::{self, Ty, TyCtxt, TypeckResults};

/// Deduplicating structural type-table encoder. Each distinct (region-erased)
/// `Ty` is encoded once; nodes reference it by index.
pub(crate) struct WitnessEncoder<'tcx> {
    tcx: TyCtxt<'tcx>,
    entries: Vec<Vec<u8>>,
    index: FxHashMap<Ty<'tcx>, u32>,
    /// True if any type/adjustment fell outside the re-internable grammar. When
    /// set, the root is not mintable (encode_root returns None).
    escaped: bool,
}

impl<'tcx> WitnessEncoder<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        WitnessEncoder { tcx, entries: Vec::new(), index: FxHashMap::default(), escaped: false }
    }

    fn dph(&self, did: rustc_hir::def_id::DefId, b: &mut Vec<u8>) {
        b.extend(self.tcx.def_path_hash(did).0.to_le_bytes());
    }

    /// Encode a type, returning its table index. Sets `escaped` and returns a
    /// sentinel index on any type outside the grammar.
    fn encode_ty(&mut self, t: Ty<'tcx>) -> u32 {
        let t = self.tcx.erase_and_anonymize_regions(t);
        if let Some(&i) = self.index.get(&t) {
            return i;
        }
        let mut b: Vec<u8> = Vec::with_capacity(8);
        match t.kind() {
            ty::Bool => b.push(0),
            ty::Char => b.push(1),
            ty::Int(i) => {
                b.push(2);
                b.push(*i as u8)
            }
            ty::Uint(u) => {
                b.push(3);
                b.push(*u as u8)
            }
            ty::Float(f) => {
                b.push(4);
                b.push(*f as u8)
            }
            ty::Str => b.push(5),
            ty::Never => b.push(6),
            ty::Tuple(elts) => {
                if elts.len() > u16::MAX as usize {
                    return self.escape(t);
                }
                let idxs: Vec<u32> = elts.iter().map(|e| self.encode_ty(e)).collect();
                b.push(7);
                b.extend((idxs.len() as u16).to_le_bytes());
                for i in idxs {
                    b.extend(i.to_le_bytes())
                }
            }
            ty::Ref(_, p, m) => {
                let pi = self.encode_ty(*p);
                b.push(8);
                b.push(matches!(m, rustc_hir::Mutability::Mut) as u8);
                b.extend(pi.to_le_bytes())
            }
            ty::RawPtr(p, m) => {
                let pi = self.encode_ty(*p);
                b.push(9);
                b.push(matches!(m, rustc_hir::Mutability::Mut) as u8);
                b.extend(pi.to_le_bytes())
            }
            ty::Slice(e) => {
                let ei = self.encode_ty(*e);
                b.push(10);
                b.extend(ei.to_le_bytes())
            }
            ty::Array(e, n) => {
                let ei = self.encode_ty(*e);
                match n.try_to_target_usize(self.tcx) {
                    Some(len) => {
                        b.push(11);
                        b.extend(ei.to_le_bytes());
                        b.extend(len.to_le_bytes())
                    }
                    None => return self.escape(t),
                }
            }
            ty::Adt(def, args) => {
                b.push(12);
                self.dph(def.did(), &mut b);
                if !self.encode_args(*args, &mut b) {
                    return self.escape(t);
                }
            }
            ty::FnDef(did, args) => {
                b.push(13);
                self.dph(*did, &mut b);
                if !self.encode_args(*args, &mut b) {
                    return self.escape(t);
                }
            }
            // Closures (scope widening, precise/parity lane): a closure TYPE is
            // `Closure(def_id, args)` where `args` = parent (generic) substs +
            // closure-kind + `sig_as_fn_ptr` + tupled-upvars. The `sig_as_fn_ptr`
            // uses the `extern "rust-call"` (splatted) ABI, which the FnPtr arm
            // escapes — encoding the FULL args would sink every closure root. But
            // kind_ty and the sig are a deterministic function of
            // (def_id, parent_args, upvars), so encode only the identity-bearing
            // parts: the parent generic args + the captured-upvar tuple (`()` for a
            // capture-less closure). Deterministic + escape-free, and a complete
            // closure identity for the parity byte-comparison. (Capture-bearing
            // closures are still excluded at mint by the non-empty
            // `closure_min_captures` gate; this lane is never trusted.)
            ty::Closure(did, args) => {
                b.push(16);
                self.dph(*did, &mut b);
                let closure = args.as_closure();
                let parent = self.tcx.mk_args(closure.parent_args());
                if !self.encode_args(parent, &mut b) {
                    return self.escape(t);
                }
                b.extend(self.encode_ty(closure.tupled_upvars_ty()).to_le_bytes());
            }
            ty::FnPtr(sig_tys, hdr) => {
                // Only binder-trivial fn pointers round-trip (HRTB bound_vars
                // are part of type identity and survive region erasure — the
                // P0 reintern round-trip caught this; see RESULTS.md §2c).
                if !sig_tys.bound_vars().is_empty() {
                    return self.escape(t);
                }
                let sig = self.tcx.instantiate_bound_regions_with_erased(sig_tys.with(*hdr));
                if sig.c_variadic() {
                    return self.escape(t);
                }
                // Soundness (audit 2026-07-22, ranks 1 & 4): the tag-14 encoding
                // records only safety + input/output types — NOT the fn-pointer
                // ABI or the splatted-arg index — and `decode` rebuilds both as
                // their Rust/None defaults. The linear checker's reify/call-fnptr
                // arms compare arity+types only, so a non-Rust-ABI or splatted
                // fn-ptr TYPE would reconstruct wrong yet ACCEPT (a checked-not-
                // trusted breach: confirmed extern-"C" fn-ptr -> borrowck equate
                // ICE). Until the ABI is round-tripped faithfully (the widening
                // work-stream), escape such fn-ptr types so the root is not
                // mintable (fail-safe MISS -> real typeck), mirroring c_variadic.
                // splatted is still not round-tripped -> escape it. The ABI IS now
                // round-tripped faithfully (the `as_packed` byte below, schema v4),
                // so non-Rust-ABI fn-ptr TYPES are minted again (the scope-widening
                // re-admission of the audit rank-1 escape). Sound: the whole-SVH key
                // attests the environment, decode restores the exact ABI via
                // `from_packed`, and the checker's reify-fn-ptr arm independently
                // re-checks `abi()`/`safety()`.
                if sig.splatted().is_some() {
                    return self.escape(t);
                }
                if sig.inputs().len() > u8::MAX as usize {
                    return self.escape(t);
                }
                let ins: Vec<u32> = sig.inputs().iter().map(|i| self.encode_ty(*i)).collect();
                let out = self.encode_ty(sig.output());
                b.push(14);
                b.push(sig.safety().is_unsafe() as u8);
                // Round-trip the fn-pointer ABI (folds the unwind flag).
                b.push(sig.abi().as_packed());
                b.push(ins.len() as u8);
                for i in ins {
                    b.extend(i.to_le_bytes())
                }
                b.extend(out.to_le_bytes())
            }
            ty::Param(pt) => {
                b.push(15);
                b.extend(pt.index.to_le_bytes());
                let nm = pt.name.as_str();
                if nm.len() > u8::MAX as usize {
                    return self.escape(t);
                }
                b.push(nm.len() as u8);
                b.extend(nm.as_bytes())
            }
            _ => return self.escape(t),
        }
        self.push_entry(t, b)
    }

    fn encode_args(&mut self, args: ty::GenericArgsRef<'tcx>, b: &mut Vec<u8>) -> bool {
        if args.len() > u8::MAX as usize {
            return false;
        }
        b.push(args.len() as u8);
        for a in args.iter() {
            match a.kind() {
                ty::GenericArgKind::Type(at) => {
                    b.push(0);
                    b.extend(self.encode_ty(at).to_le_bytes());
                }
                ty::GenericArgKind::Lifetime(_) => b.push(1),
                // Const generic args are v1-exotic (Display-form is unstable
                // for reconstruction); escape.
                ty::GenericArgKind::Const(_) => return false,
            }
        }
        true
    }

    /// Encode one value-expression adjustment step in the enriched,
    /// reconstruction-faithful form:
    ///
    /// ```text
    /// kind_byte  [payload_byte for kinds 1..=4]  u32 target_type_index
    /// ```
    ///
    /// `decode::rebuild_adjust` inverts this exactly. Any step v1 cannot
    /// faithfully reconstruct — an overloaded deref (which also registers a
    /// `type_dependent_defs` pick, so it is mint-excluded anyway) or a pin
    /// deref (`pin_ergonomics`) — sets `escaped`, so `encode_root` discards the
    /// whole root. `Unsize`-to-`dyn` needs no special case: its target type is
    /// `ty::Dynamic`, which is outside the grammar, so `encode_ty` escapes it.
    fn encode_adjustment(&mut self, a: &ty::adjustment::Adjustment<'tcx>, b: &mut Vec<u8>) {
        use rustc_hir::Mutability;
        use ty::adjustment::{
            Adjust, AllowTwoPhase, AutoBorrow, AutoBorrowMutability, DerefAdjustKind,
            PointerCoercion as PC,
        };
        match &a.kind {
            Adjust::NeverToAny => {
                b.push(0);
            }
            Adjust::Deref(DerefAdjustKind::Builtin) => {
                b.push(1);
                b.push(0);
            }
            Adjust::Deref(_) => {
                // Overloaded / pin deref: not faithfully reconstructible in v1.
                self.escaped = true;
                b.push(1);
                b.push(255);
            }
            Adjust::Borrow(ab) => {
                b.push(2);
                let payload: u8 = match ab {
                    AutoBorrow::Ref(AutoBorrowMutability::Not) => 0,
                    AutoBorrow::Ref(AutoBorrowMutability::Mut {
                        allow_two_phase_borrow: AllowTwoPhase::No,
                    }) => 1,
                    AutoBorrow::Ref(AutoBorrowMutability::Mut {
                        allow_two_phase_borrow: AllowTwoPhase::Yes,
                    }) => 2,
                    AutoBorrow::RawPtr(Mutability::Not) => 3,
                    AutoBorrow::RawPtr(Mutability::Mut) => 4,
                    AutoBorrow::Pin(Mutability::Not) => 5,
                    AutoBorrow::Pin(Mutability::Mut) => 6,
                };
                b.push(payload);
            }
            Adjust::Pointer(pc) => {
                b.push(3);
                let payload: u8 = match pc {
                    PC::ReifyFnPointer(s) => {
                        if s.is_unsafe() {
                            1
                        } else {
                            0
                        }
                    }
                    PC::UnsafeFnPointer => 2,
                    PC::ClosureFnPointer(s) => {
                        if s.is_unsafe() {
                            4
                        } else {
                            3
                        }
                    }
                    PC::MutToConstPointer => 5,
                    PC::ArrayToPointer => 6,
                    PC::Unsize => 7,
                };
                b.push(payload);
            }
            Adjust::GenericReborrow(m) => {
                b.push(4);
                b.push(matches!(m, Mutability::Mut) as u8);
            }
        }
        b.extend(self.encode_ty(a.target).to_le_bytes());
    }

    fn escape(&mut self, t: Ty<'tcx>) -> u32 {
        self.escaped = true;
        // Still push a placeholder so indices stay consistent; the whole root
        // is discarded by encode_root when `escaped` is set.
        self.push_entry(t, vec![255])
    }

    fn push_entry(&mut self, t: Ty<'tcx>, b: Vec<u8>) -> u32 {
        let i = self.entries.len() as u32;
        self.entries.push(b);
        self.index.insert(t, i);
        i
    }
}

/// Encode one root's full witness payload, or `None` if any type/field falls
/// outside the re-internable grammar (that root is not mintable).
pub fn encode_root<'tcx>(tcx: TyCtxt<'tcx>, tr: &TypeckResults<'tcx>) -> Option<Vec<u8>> {
    let mut enc = WitnessEncoder::new(tcx);
    let mut body: Vec<u8> = Vec::new();
    let put_u32 = |b: &mut Vec<u8>, v: u32| b.extend(v.to_le_bytes());

    // node_types
    let nt = tr.node_types();
    let items = nt.items_in_stable_order();
    let node_ids: Vec<_> = items.iter().map(|(id, _)| *id).collect();
    put_u32(&mut body, items.len() as u32);
    for (id, t) in &items {
        put_u32(&mut body, id.as_u32());
        let ti = enc.encode_ty(**t);
        put_u32(&mut body, ti);
    }

    // node_args (probe every node id; no read-side table accessor)
    let mut na: Vec<(rustc_hir::ItemLocalId, ty::GenericArgsRef<'tcx>)> = Vec::new();
    for id in &node_ids {
        let hid = HirId { owner: tr.hir_owner, local_id: *id };
        if let Some(args) = tr.node_args_opt(hid) {
            if !args.is_empty() {
                na.push((*id, args));
            }
        }
    }
    put_u32(&mut body, na.len() as u32);
    for (id, args) in na {
        put_u32(&mut body, id.as_u32());
        if !enc.encode_args(args, &mut body) {
            return None;
        }
    }

    // field_indices
    let fi = tr.field_indices().items_in_stable_order();
    put_u32(&mut body, fi.len() as u32);
    for (id, idx) in fi {
        put_u32(&mut body, id.as_u32());
        put_u32(&mut body, idx.as_u32());
    }

    // adjustments (enriched: kind byte + optional payload byte + target type).
    // `decode::rebuild_adjust` reads this format back into a faithful
    // `ty::adjustment::Adjustment`. A step v1 cannot reconstruct sets `escaped`.
    let adj = tr.adjustments().items_in_stable_order();
    put_u32(&mut body, adj.len() as u32);
    for (id, steps) in adj {
        if steps.len() > u8::MAX as usize {
            return None;
        }
        put_u32(&mut body, id.as_u32());
        body.push(steps.len() as u8);
        for a in steps {
            enc.encode_adjustment(a, &mut body);
        }
    }

    // pat_binding_modes (byte)
    let pbm = tr.pat_binding_modes().items_in_stable_order();
    put_u32(&mut body, pbm.len() as u32);
    for (id, _m) in &pbm {
        put_u32(&mut body, id.as_u32());
        body.push(0);
    }

    // pat_adjustments (tag + source type)
    let pa = tr.pat_adjustments().items_in_stable_order();
    put_u32(&mut body, pa.len() as u32);
    for (id, steps) in pa {
        if steps.len() > u8::MAX as usize {
            return None;
        }
        put_u32(&mut body, id.as_u32());
        body.push(steps.len() as u8);
        for st in steps {
            body.push(0);
            body.extend(enc.encode_ty(st.source).to_le_bytes());
        }
    }

    // liberated_fn_sigs
    let lf = tr.liberated_fn_sigs().items_in_stable_order();
    put_u32(&mut body, lf.len() as u32);
    for (id, sig) in lf {
        if sig.inputs().len() > u8::MAX as usize {
            return None;
        }
        put_u32(&mut body, id.as_u32());
        body.push(sig.inputs().len() as u8);
        for i in sig.inputs() {
            body.extend(enc.encode_ty(*i).to_le_bytes());
        }
        body.extend(enc.encode_ty(sig.output()).to_le_bytes());
    }

    // fru_field_types
    let fr = tr.fru_field_types().items_in_stable_order();
    put_u32(&mut body, fr.len() as u32);
    for (id, tys) in fr {
        if tys.len() > u8::MAX as usize {
            return None;
        }
        put_u32(&mut body, id.as_u32());
        body.push(tys.len() as u8);
        for t in tys {
            body.extend(enc.encode_ty(*t).to_le_bytes());
        }
    }

    // coercion_casts (sorted id set)
    let cc = tr.coercion_casts();
    put_u32(&mut body, cc.len() as u32);
    let mut cast_ids: Vec<u32> =
        cc.items().into_sorted_stable_ord().iter().map(|i| i.as_u32()).collect();
    cast_ids.sort();
    for id in cast_ids {
        put_u32(&mut body, id);
    }

    // type_dependent_defs (Follow-on 2): the method/operator picks. mintable()
    // has already restricted these to monomorphic AssocFn, so each is
    // (localid, DefPathHash of the picked AssocFn). Belt-and-braces: escape on
    // any non-AssocFn / error pick that slipped the gate.
    let td = tr.type_dependent_defs().items_in_stable_order();
    put_u32(&mut body, td.len() as u32);
    for (id, r) in td {
        put_u32(&mut body, id.as_u32());
        match r {
            Ok((rustc_hir::def::DefKind::AssocFn, did)) => enc.dph(*did, &mut body),
            _ => {
                enc.escaped = true;
                // still emit a fixed-width placeholder so the stream stays parseable
                body.extend([0u8; 16]);
            }
        }
    }

    // used_trait_imports (Follow-on 2): recorded so the unused-import lint is
    // byte-identical on replay. Map each local trait import to its DefPathHash
    // and emit in stable-sorted order (DefPathHash is StableCompare; LocalDefId
    // is not).
    let tcx = enc.tcx;
    let uti = tr
        .used_trait_imports
        .items()
        .map(|d| tcx.def_path_hash(d.to_def_id()))
        .into_sorted_stable_ord();
    put_u32(&mut body, uti.len() as u32);
    for h in uti {
        body.extend(h.0.to_le_bytes());
    }

    if enc.escaped {
        return None;
    }

    // assemble: magic + type table + body
    let mut out: Vec<u8> = Vec::with_capacity(body.len() + 8 * enc.entries.len() + 16);
    out.extend(crate::schema::WITNESS_MAGIC);
    put_u32(&mut out, enc.entries.len() as u32);
    for e in &enc.entries {
        if e.len() > u16::MAX as usize {
            return None;
        }
        out.extend((e.len() as u16).to_le_bytes());
        out.extend(e);
    }
    out.extend(body);
    Some(out)
}

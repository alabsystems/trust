//! trust-ir -> rustc MIR: the compat shim ("LLVM2", P1.2 slices 1+2+3).
//!
//! Reconstructs a `rustc_middle::mir::Body` from the producer's `trust_ir::Module` for the
//! SCALAR fragment (straight-line, if/join, and single-loop CFGs): int/bool params,
//! `Inst::Const`, `Inst::BinOp`, the checked `Inst::Overflow` + `Assert` idiom the producer
//! emits under overflow checks, `Inst::ICmp`, `Inst::UnOp`, `Inst::Br`/`Inst::CondBr` (block
//! params -> one MIR local per param, assigned by each predecessor before its goto edge —
//! loop back-edges included, so cyclic producer CFGs lower without special casing),
//! `Inst::Return` (value-carrying AND unit), and memory-promoted locals
//! (`Inst::Alloca`/`Store`/`Load` on proven-private slots).
//!
//! OPAQUE NON-SCALAR PARAMS (slice 3): a param whose trust-ir type is `Ty::Ptr` (closure
//! environments `&{closure}` / `&mut {closure}`, plain `&T`/`&mut T`), `Ty::Unit` (real `()`
//! params and by-value NON-capturing `FnOnce` closure envs), or `Ty::Tuple` of scalars is
//! admitted as a DECLARATION ONLY. The derived body needs the param local's TYPE to be
//! faithful, but trust-ir's `Ty::Ptr` erases the pointee — so the shim resolves the
//! ABI-boundary types from a [`SigSource`] (the differential provides them; the flip lane
//! re-derives them from `tcx` — see `rederive_abi_sig`) and
//! THREADS the built rustc type through after proving the trust-ir type is
//! faithfully-widenable to it (`Ptr` ↔ any ref/raw-ptr; `Unit` ↔ `()`/zero-upvar closure;
//! `Tuple` ↔ same-arity scalar tuple; count and per-position shape checked, fail-closed).
//! WHY THREADING CANNOT HIDE A SEMANTIC DIFFERENCE: (a) the comparator renders arg types
//! from the BUILT side exactly, and the derived decl IS the built type, so the type channel
//! is compared, not assumed; (b) every USE of an opaque param value fails closed —
//! `operand()` refuses opaque `ValueId`s with a precise reason — so the threaded type can
//! never flow into an op/terminator whose semantics the shim would have to model. Scalar
//! params keep the shim's own denotation (see `scalar_rustc_ty`).
//!
//! POINTER-WIDTH RESPELL — RETIRED (v25 B1, RFC TRUST_IR_V2). The subsystem existed because
//! the producer's `map_ty` collapsed `isize`/`usize` to the target's fixed-width int, so the
//! shim had to VOTE over the built ABI anchors to recover the source spelling (`PtrSpell`).
//! B1 gives the producer first-class `Ty::Isize`/`Ty::Usize`/`Ty::Char` spellings, so
//! `scalar_rustc_ty` denotes them directly (one trust-ir type -> exactly one rustc type) and
//! the vote could never match again (no collapsed anchor exists). Deleted, not disabled.
//!
//! STORAGE MARKERS: the shim emits NO `StorageLive`/`StorageDead`. Reconstruction from the
//! Module alone is IMPOSSIBLE: `fn tail(a,b) {a+b}` and `fn letted(a,b) {let s=a+b; s}`
//! lower to byte-identical trust-ir functions but different built marker sequences
//! (probes/w2_marker_infeasibility.rs), so any `f(Module) -> markers` is wrong on one of
//! them. Marker fidelity is instead PROVEN OR REFUSED per body by the comparator's exact
//! marker channel (`mir_differential::canon_markers`), and the flip only consumes a derived
//! body at `-O` (`sess.emit_lifetime_markers()`) when that channel proved exact equality —
//! which today means "the built body's reachable subgraph is marker-free" (unit fns,
//! const-returning closures, param-identity bodies).
//!
//! Everything else is FAIL-CLOSED: `lower_ir_to_mir` returns `Err(Unsupported)` with a reason,
//! never a mis-lowered body. The derived `Body` is used ONLY by the derived-vs-built MIR
//! differential (`crate::mir_differential`) — it is never fed to borrowck / codegen / queries —
//! but it is constructed honestly (the same invariants `construct_fn`'s `Body::new` establishes:
//! `_0` return place, then args, then temps; one outermost `SourceScope`; `MirPhase::Built`).
//!
//! Shape fidelity notes (what makes derived ≡ built achievable):
//!   * `Inst::Const` is FOLDED into operands (no statement), matching how the MIR builder puts
//!     literals directly into `Operand::Constant`.
//!   * The producer's checked-arithmetic idiom `Overflow + Const(false) + Const(true) +
//!     Select(!overflowed) + Assert` is recognized as ONE unit and emitted as rustc's canonical
//!     `_t = <op>WithOverflow(a, b); assert(!move (_t.1), Overflow(op, a, b))` pair
//!     (`builder/expr/as_rvalue.rs::build_binary_op`), with `UnwindAction::Continue` exactly as
//!     `Builder::assert` uses (`builder/scope.rs:1754`).
//!   * The producer's bool-not idiom `Const(false) + Const(true) + Select(b ? false : true)` is
//!     recognized and emitted as MIR `UnaryOp(Not, b)`.
//!   * The producer's CHECKED-SHIFT idiom `[Cast{Trunc → unsigned twin}] + Const(LHS_BITS) +
//!     ICmp(Ult) + Assert + [Cast{amount → shifted ty}] + BinOp(Shl|LShr|AShr)` is recognized as
//!     ONE unit (`shift_idiom`) and emitted as rustc's canonical shift-overflow check
//!     (`as_rvalue.rs:473-521`): `[_t = amt as u_ty (IntToInt);] _b = Lt(_t|amt, BITS);
//!     assert(move _b, expected=true, Overflow(op, l, amt)); _r = Shl|Shr(l, amt)` — with the
//!     ORIGINAL amount operand in the shift (MIR permits a differently-typed amount; the
//!     module-side value cast exists only for trust-ir's same-type `eval_binop` contract and is
//!     value-preserving under the just-asserted range, so it has no MIR counterpart). With
//!     overflow checks OFF the pair `Cast + BinOp(shift)` maps to the bare `Shl|Shr(l, amt)`
//!     (`shift_value_cast_pair`; out-of-range is UB on both sides, so discarding the
//!     value-preserving cast cannot change a defined execution).
//!   * `Inst::CondBr` (edge args always empty in the producer's `lower_if`/`lower_logical_op`)
//!     becomes `TerminatorKind::if_(cond, then, else)` — the identical
//!     `SwitchTargets::static_if(0, else, then)` encoding the MIR builder produces.
//!   * A value-less `Inst::Return` on a `returns: []` signature (the producer's unit-return
//!     convention) lowers to `_0 = const (); return` with `_0: ()` — exactly the shape
//!     `Builder::push_assign_unit` + `construct_fn` give the built body of a unit fn.
//!   * MEMORY-PROMOTED SLOTS (slice 2): each `Inst::Alloca` (count-less, align-less, scalar
//!     pointee) becomes ONE fresh MIR local of the pointee type; `Store` -> a plain assign to
//!     that local; `Load` -> a FRESH temp copied from it (an SSA load value is the slot's
//!     value AT LOAD TIME — aliasing the slot local directly would wrongly see later stores).
//!     Erasing the pointer indirection is CORRECT only while the slot stays private, so a
//!     pre-pass PROVES the Alloca's pointer never escapes: its `ValueId` may appear ONLY as
//!     the `ptr` of a non-volatile `Load`/`Store`. The escape probe reuses
//!     `trust_ir::mem2reg::rewrite_inst` — the authoritative match-on-every-variant operand
//!     walker — so a use through ANY operand position (call/aggregate/binop/branch-arg/
//!     return/GEP/store-as-value/...) fails closed, and a future `Inst` variant is covered
//!     automatically. The built-MIR counterpart (`_r = &mut _x`, deref reads/writes) is
//!     absorbed by the comparator's alias tracking (`mir_differential` module docs).
//!   * DIRECT CALLS (wave 6): `Inst::Call { callee, args }` declares exactly one SSA result for a
//!     non-unit callee and zero SSA results for a unit callee, matching function signatures and
//!     `Inst::Return`. Both shapes become `TerminatorKind::Call { func:
//!     Operand::Constant(zero-sized FnDef), args, destination: fresh temp (or the tail return place)
//!     of the callee's declared return type, target: Some(succ), unwind: Continue, call_source:
//!     Normal, fn_span }` — MIR requires a destination even for `()`, while TrustIR does not invent
//!     a unit SSA value. The call splits the MIR chain exactly like an assert.
//!     CALLEE IDENTITY is resolved through the producer's `Lowered::callees` ledger (threaded
//!     in by both callers): the per-body `FuncId` is DefIndex-derived, so the ledger entry —
//!     unique, tripwire-checked (`def_id.index == func_id`) — is the ONLY honest way back to a
//!     `DefId`; zero or multiple entries for one `FuncId` fail closed (the crate assembler's
//!     ambiguity rule, `crate_module::resolve_callee`). The func operand is spelled EXACTLY as
//!     built MIR spells it (`Ty::FnDef(def_id, [])` via `Operand::function_handle`) — which is
//!     only PROVABLY the built spelling when the site's THIR callee type was that same
//!     `FnDef`: a free `DefKind::Fn`, or an INHERENT-impl `DefKind::AssocFn`, with
//!     `generics_of(def_id).count() == 0` (no params at all ⇒ the site's `GenericArgs` is
//!     `[]`). A TRAIT-impl method fails closed — the built site spells the TRAIT fn's DefId
//!     (resolution to the impl happens at mono, not in MIR) — as do generic callees,
//!     intrinsics (`tcx.intrinsic`; a direct HIR call to one is producer-admissible),
//!     `#[track_caller]` callees (codegen materializes the caller `Location` from the call
//!     span, which the shim carries only fn-level — panic-Location fidelity), non-Rust-ABI /
//!     variadic callees (unwind ABI differs), and closure-body callees (the producer's
//!     `ClosureCall` untupling — its env `Alloca` escapes into the call args, so the slice-2
//!     escape probe already rejects those bodies wholesale). Extern (cross-crate) callees
//!     resolve identically — `CalleeRef::def_id` is the full lifetime-free `DefId`.
//!     ARG/RET FIDELITY: arity must equal the callee's `fn_sig` inputs; each lowered arg
//!     operand's rustc type must EXACTLY equal the declared input type; the return type must
//!     be a scalar whose trust-ir spelling round-trips through the global `scalar_rustc_ty`
//!     denotation (one spelling per type since v25 B1), or unit. UNWIND: built MIR at `Built` phase gives
//!     every call (and, in any diverge-carrying body, every assert) `UnwindAction::
//!     Cleanup(bbN)` where `bbN` is the drop tree's lone-`resume` cleanup block (verified on
//!     real `-Zdump-mir=built`, probes/w6_shim_calls.rs); the shim instead emits the
//!     POST-`RemoveNoopLandingPads` normal form `UnwindAction::Continue` + NO cleanup block —
//!     the SAME convention the assert arm has always used, proven byte-parity-safe by the
//!     w2–w5 flip byte-compare probes (that pass runs in `run_analysis_cleanup_passes`, which
//!     the flip replays 1:1, normalizing the built sibling to the identical shape). The
//!     differential's raw call channel (`mir_differential::raw_call_channel`) separately
//!     verifies the BUILT side's unwind is exactly that benign shape and fails closed on real
//!     cleanup work (drops), `Terminate`, or `Unreachable` unwinds.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com> | Copyright 2026 | License: Apache-2.0

use std::collections::HashMap;

use rustc_abi::{FIRST_VARIANT, FieldIdx};
use rustc_hir::def::DefKind;
use rustc_index::IndexVec;
use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
// Trust (wave-str): `CTFE_ALLOC_SALT` (= 0) is the dedup salt `tcx.allocate_bytes_dedup` uses for a
// `&str` literal's byte allocation; using it means the shim's re-emitted `&str` const dedups to the
// SAME `AllocId` as the built literal → byte-identical codegen.
use rustc_middle::mir::interpret::CTFE_ALLOC_SALT;
use rustc_middle::mir::{
    AggregateKind, AssertKind, BasicBlock, BasicBlockData, BinOp as MirBinOp, Body, BorrowKind,
    CallSource, CastKind, ClearCrossCrate, Const as MirConst, ConstOperand, ConstValue, Local,
    LocalDecl, MirSource, Operand, Place, Rvalue, SourceInfo, SourceScope, SourceScopeData,
    SourceScopeLocalData, Statement, StatementKind, Terminator, TerminatorKind, UnOp as MirUnOp,
    UnwindAction, VarDebugInfo, VarDebugInfoContents, WithRetag,
};
use rustc_middle::ty::{self, Ty as RustcTy, TyCtxt, TypeVisitableExt};
use rustc_span::def_id::LocalDefId;
use rustc_span::{Span, Spanned, sym};
// Trust (wave-str): `GlobalId` is not re-exported at the `trust_ir` crate root (unlike `ValueId`),
// so import it from its defining module.
use trust_ir::value::GlobalId;
use trust_ir::{
    BinOp, BlockId, CastOp, Constant, FuncId, ICmpOp, Inst, InstrNode, Module, OverflowOp, Ty,
    UnOp, ValueId,
};

use crate::{CalleeRef, SiteArg, SiteTy};

/// Fail-closed rejection: a trust-ir construct (or producer/built-MIR shape divergence) this
/// slice does not model. Carrying a reason string keeps the differential's `DerivedUnsupported`
/// verdict diagnosable per body.
#[derive(Debug)]
pub struct Unsupported {
    pub reason: String,
}

fn unsup<T>(reason: impl Into<String>) -> Result<T, Unsupported> {
    Err(Unsupported { reason: reason.into() })
}

/// Trust (wave-D, Drop-free aggregate constructor-return FLIP): recognize the InsertField chain that
/// builds a returned struct value. The producer lowers `Struct { f0, f1, .. }` as a typed
/// `Const{Ty::Struct, Constant::Aggregate(seeds)}` seed followed by an `InsertField{field: k}` per
/// field (see `lib.rs` `ExprKind::Adt`). Traces `ret_val` backward through the `InsertField` links to
/// the seed, validating the chain writes EVERY field index `0..seeds.len()` exactly once. Returns
/// `(field_vals in index order, skip_ids)` — `skip_ids` are the seed + InsertField result ids the
/// main loop must NOT translate (the Return arm rebuilds one `Rvalue::Aggregate` from them). Returns
/// `None` (fail closed) if the tail is not a full, well-formed constructor chain: a block param
/// (control flow / phi), a partial chain, a duplicate / out-of-bounds field index, or a chain link
/// that is not `InsertField`/seed-`Const`. A NESTED aggregate field is left for the main loop (its
/// value id is a chain VALUE, not walked here), where the un-skipped nested `InsertField`/`Const`
/// fails closed — so slice-1 admits only flat, scalar-field constructor returns.
fn recognize_agg_return_chain(
    value_def: &HashMap<ValueId, &InstrNode>,
    ret_val: ValueId,
) -> Option<(Vec<ValueId>, Vec<ValueId>)> {
    let mut skip: Vec<ValueId> = Vec::new();
    let mut fields: Vec<(u32, ValueId)> = Vec::new();
    let mut cur = ret_val;
    // Acyclic producer SSA bounds the walk; a visited-count cap fails closed on a malformed
    // (cyclic) chain rather than hanging — defense-in-depth (unreachable for valid producer output).
    let max_steps = value_def.len() + 1;
    let mut steps = 0usize;
    loop {
        steps += 1;
        if steps > max_steps {
            return None;
        }
        let node = value_def.get(&cur)?;
        match &node.inst {
            Inst::InsertField { aggregate, field, value, .. } => {
                skip.push(cur);
                fields.push((*field, *value));
                cur = *aggregate;
            }
            Inst::Const { value: Constant::Aggregate(seeds), .. } => {
                skip.push(cur);
                let n = seeds.len();
                if fields.len() != n {
                    return None;
                }
                let mut slots: Vec<Option<ValueId>> = vec![None; n];
                for (idx, val) in &fields {
                    let i = *idx as usize;
                    if i >= n || slots[i].is_some() {
                        return None;
                    }
                    slots[i] = Some(*val);
                }
                let field_vals: Vec<ValueId> = slots.into_iter().collect::<Option<Vec<_>>>()?;
                return Some((field_vals, skip));
            }
            _ => return None,
        }
    }
}

/// Trust (B3-2a/B3-2c): recognize the producer's sole first-class `Ty::Enum`
/// construction convention. A niladic variant is a bare enum-typed aggregate
/// constant containing its discriminant. A one-field variant inserts the payload
/// at field 1 of an enum-typed aggregate seed containing the discriminant at field
/// 0. Returns `(discriminant, payload, skip)`; the payload value is deliberately
/// not skipped so the reconstruction path must bind and type-check it. Computed
/// discriminants, non-enum seeds, malformed aggregate arities, and deeper insert
/// chains return `None` and therefore fail closed.
fn recognize_enum_construction(
    value_def: &HashMap<ValueId, &InstrNode>,
    ret_val: ValueId,
) -> Option<(i128, Option<ValueId>, Vec<ValueId>)> {
    // Trust (B3-2a E1): the producer's first-class Ty::Enum
    // construction convention. (i) NILADIC: the returned value IS a bare
    // `Const{ty: Ty::Enum, value: Aggregate([Int(disc)])}` — no InsertField at
    // all. (ii) 1-PAYLOAD
    // (dead in B3-2a, live in 2b): `InsertField{field: 1, value: %pv}` over a
    // `Const{Ty::Enum, Aggregate([Int(disc), seed])}`. (iii) any deeper chain
    // fails closed (mirrors the flip fragment's ≤1-field rule). The general
    // model emits SIGN-EXTENDED effective discriminants — emit_enum_variant's
    // width-masked compare (E2) is what makes negative discs match.
    if let Some(node) = value_def.get(&ret_val) {
        if let Inst::Const { ty: Ty::Enum(_), value: Constant::Aggregate(seeds) } = &node.inst {
            if seeds.len() == 1 {
                if let Constant::Int(disc) = &seeds[0] {
                    return Some((*disc, None, vec![ret_val]));
                }
            }
            return None;
        }
    }
    let Inst::InsertField { aggregate, field, value, .. } = &value_def.get(&ret_val)?.inst else {
        return None;
    };
    // Trust (B3-2a E1 ii): the one-payload shape — field 1 over an enum-typed
    // constant seed.
    if *field == 1 {
        if let Inst::Const { ty: Ty::Enum(_), value: Constant::Aggregate(seeds) } =
            &value_def.get(aggregate)?.inst
        {
            if seeds.len() == 2 {
                if let Constant::Int(disc) = &seeds[0] {
                    return Some((*disc, Some(*value), vec![ret_val, *aggregate]));
                }
            }
            return None;
        }
    }
    // Trust (B3-2c T2 slice 2): the legacy wave-Y/YP tag-insert tail is DELETED —
    // the producer emits only the general Ty::Enum convention above; a tuple-model
    // chain can no longer occur.
    let _ = value;
    None
}

/// Trust (wave-Y/wave-Z/wave-YP shared): emit `place = Rvalue::Aggregate(Adt(did, variant_k, args),
/// [payload?])` for an enum variant whose rustc discriminant VALUE is `disc`. Recovers the variant
/// index `k` by matching `disc` against the AUTHORITATIVE `adt.discriminants(tcx)` set — the same
/// source wave-V's Switch reshape trusts (repr/explicit-disc FAITHFUL, NOT a raw variant index); a
/// tag matching no variant (exotic/negative repr) fails closed. Identity (DefId + GenericArgs) comes
/// from `ret_rty` (= `built_ret_ty`), the ONLY sound source (attack A1). The comparator renders both
/// built (`_0 = E::A(v)`) and this reconstruction as `agg(adt:E:k,[op])`, so a wrong `k`/payload →
/// mismatch → no flip.
///
/// `payload` is `Some(op)` for a 1-field variant (`Some(x)` / `Ok(v)`), `None` for a niladic variant
/// (`None` / a fieldless `E::A`). WELL-TYPEDNESS GATE (wave-P): a payload operand's type MUST equal
/// the recovered variant's single field type (region-erased both sides), else the aggregate is
/// ill-typed → a CTFE `mir_assign_valid_types` span_bug on the const seam — fail closed. Shared by
/// the wave-Y/YP DIRECT-return arm and the wave-Z BRANCH-edge arm.
fn emit_enum_variant<'tcx>(
    tcx: TyCtxt<'tcx>,
    cx: &mut ShimCx<'tcx>,
    cur: BasicBlock,
    place: Place<'tcx>,
    ret_rty: RustcTy<'tcx>,
    disc: i128,
    payload: Option<Operand<'tcx>>,
) -> Result<(), Unsupported> {
    let ty::Adt(adt_def, args) = ret_rty.kind() else {
        return unsup("enum construction: return type is not an Adt (unreachable)");
    };
    let variants: Vec<_> = adt_def.discriminants(tcx).collect();
    let mut vidx = None;
    for (vi, d) in &variants {
        // Trust (B3-2a E2): WIDTH-MASKED compare — the general model emits
        // SIGN-EXTENDED effective discriminants (a negative `#[repr(i16)]` disc
        // arrives as an all-ones-extended i128) while rustc's `Discr.val` is the
        // raw pattern truncated to the discr type's width. Mask BOTH to that
        // width (the Switch reshape's `lit & mask` convergence); a raw compare
        // silently misses every negative-disc general ctor — comparator-BLIND.
        let (size, _signed) = d.ty.int_size_and_signed(tcx);
        let mask = size.unsigned_int_max();
        if d.val & mask == (disc as u128) & mask {
            vidx = Some(*vi);
            break;
        }
    }
    let Some(mut vidx) = vidx else {
        return unsup("enum construction: no variant matches the produced discriminant");
    };
    if cx.sat_perturb == Some(SatPerturb::EnumCtor) && variants.len() >= 2 {
        // SAT control: construct the WRONG VARIANT (the next one, cyclically).
        // Same-arity rotations reach the comparator as a value mismatch; a
        // different-arity rotation fails the arity gate below (flips vanish) —
        // both are the perturbation being CAUGHT.
        cx.sat_perturb_count += 1;
        let pos = variants.iter().position(|(vi, _)| *vi == vidx).unwrap_or(0);
        vidx = variants[(pos + 1) % variants.len()].0;
    }

    // Well-typedness gate: a payload operand must match the recovered variant's field arity + type.
    let want_arity = payload.is_some() as usize;
    if adt_def.variant(vidx).fields.len() != want_arity {
        return unsup("enum construction: variant arity != produced payload arity");
    }
    if let Some(op) = &payload {
        let fty = adt_def.variant(vidx).fields[FieldIdx::ZERO].ty(tcx, args).skip_normalization();
        // Region-erase + normalize both sides (wave-P idiom, to_mir.rs:2554): a semantically-equal
        // but lifetime-differing field type must not FALSE-reject, while isize/usize vs i64/u64 stay
        // DISTINCT so the real ill-typed-aggregate ICE hazard is still caught. `unwrap_or(t)` never
        // panics on a stuck projection (runs outside the flip's catch_unwind).
        let te = ty::TypingEnv::fully_monomorphized();
        // Trust (P1 stdlib-harvest unblock): `fully_monomorphized` normalize REQUIRES param-free
        // input; a param-bearing type reaches `type_of_const_param` → hard `bug!` ICE (not `Err`,
        // so `unwrap_or` can't catch it). Guard the input like every other such site in this crate.
        let norm = |t: RustcTy<'tcx>| {
            if t.has_non_region_param() || t.has_non_region_infer() {
                return t;
            }
            crate::cycle_safe_normalize(tcx, te, t)
        };
        if norm(op.ty(&cx.local_decls, tcx)) != norm(fty) {
            return unsup("enum construction: payload operand type != variant field type");
        }
    }
    // SAT control (B3-2b EnumPayload): AFTER the type gate, BEFORE assembly.
    let mut payload = payload;
    if cx.sat_perturb == Some(SatPerturb::EnumPayload) {
        if let Some(orig) = payload.as_ref() {
            let fty =
                adt_def.variant(vidx).fields[FieldIdx::ZERO].ty(tcx, args).skip_normalization();
            let width: Option<u64> = match fty.kind() {
                ty::Bool => Some(1),
                ty::Int(i) => i.bit_width(),
                ty::Uint(u) => u.bit_width(),
                ty::Float(f) => Some(f.bit_width() as u64),
                _ => None,
            };
            if let Some(w) = width {
                // A distinctive nonzero pattern; if the original IS that exact
                // constant, use its complement so the substitution is never a
                // no-op (the inert-control trap).
                let mask = if w >= 128 { u128::MAX } else { (1u128 << w) - 1 };
                let mut bits = 0x5A5A_5A5A_5A5A_5A5A_5A5A_5A5A_5A5A_5A5Au128 & mask;
                if let Operand::Constant(c) = orig {
                    if c.const_.try_to_bits(rustc_abi::Size::from_bits(w)) == Some(bits) {
                        bits = (!bits) & mask;
                    }
                }
                let const_ =
                    MirConst::from_bits(tcx, bits, ty::TypingEnv::fully_monomorphized(), fty);
                payload = Some(Operand::Constant(Box::new(ConstOperand {
                    span: cx.span,
                    user_ty: None,
                    const_,
                })));
                cx.sat_perturb_count += 1;
            }
        }
    }

    let fields: IndexVec<FieldIdx, Operand<'tcx>> = payload.into_iter().collect();
    cx.assign(
        cur,
        place,
        Rvalue::Aggregate(
            Box::new(AggregateKind::Adt(adt_def.did(), vidx, args, None, None)),
            fields,
        ),
    );
    Ok(())
}

/// Trust (wave-str): the raw UTF-8 bytes a `&str`-literal's `global_addr @global.N` points to. The
/// producer promotes a string literal to a module `Global` whose `initializer` is a homogeneous
/// byte array (`Constant::Array`/`Aggregate` of `Int(0..=255)`). Returns `None` (→ fail closed →
/// no flip) if the global is missing, has no initializer, or holds a non-byte-array constant — the
/// shim never guesses the string contents.
fn global_str_bytes(module: &Module, global: GlobalId) -> Option<Vec<u8>> {
    let g = module.globals.get(global.as_usize())?;
    let elems = match g.initializer.as_ref()? {
        Constant::Array(e) | Constant::Aggregate(e) => e,
        _ => return None,
    };
    elems
        .iter()
        .map(|c| match c {
            Constant::Int(v) if (0..=255).contains(v) => Some(*v as u8),
            _ => None,
        })
        .collect()
}

/// Trust (wave-str, `&str`-LITERAL-RETURN FLIP): recognize a returned `&str` literal. The producer
/// models `&str` as a fat pointer `Ty::Tuple([Ptr, I64])` and builds `"lit"` as a two-field
/// InsertField chain over a 2-elem `(ptr, i64)` const seed — field 0 = `global_addr @global.N` (the
/// data pointer into the promoted string-bytes global), field 1 = `const i64 <len>`. Built MIR
/// instead folds the whole thing into a single `_0 = const "lit"`. Reuses `recognize_agg_return_chain`
/// for the chain walk (a 2-field aggregate over a 2-elem seed), then verifies the two field VALUES.
/// Returns `(global, claimed_len, skip)`; `skip` extends the chain skip set with the `GlobalAddr` and
/// `const i64 len` nodes so the main loop drops them (the shim has no `GlobalAddr` arm → a
/// non-skipped one fails closed). Any deviation from the exact shape → `None` (clean-only, never a
/// miscompile — the byte-faithful `_0 = const "lit"` is re-emitted only on an exact match).
fn recognize_str_return(
    value_def: &HashMap<ValueId, &InstrNode>,
    ret_val: ValueId,
) -> Option<(GlobalId, u64, Vec<ValueId>)> {
    // Trust (B2-2): the producer now spells the `&str` literal as ONE first-class
    // fat-pointer construction — `PtrFromParts { ptr_ty: FatPtr(Str), metadata_ty:
    // U64, data: <GlobalAddr>, metadata: <Const U64 len> }` — so the recognizer is a
    // direct 3-node match (the former 5-node tuple seed + InsertField chain walk
    // retired with the anonymous spelling). Skip set = the three matched nodes; the
    // shim has NO arm for GlobalAddr or PtrFromParts, so a non-skipped use of any of
    // them still fails closed in `cx.operand` — the soundness discipline unchanged.
    let (data, metadata) = match &value_def.get(&ret_val)?.inst {
        Inst::PtrFromParts {
            ptr_ty: Ty::FatPtr(trust_ir::FatPtrKind::Str),
            metadata_ty: Ty::U64,
            data,
            metadata,
        } => (*data, *metadata),
        _ => return None,
    };
    let global = match &value_def.get(&data)?.inst {
        Inst::GlobalAddr { global } => *global,
        _ => return None,
    };
    let len = match &value_def.get(&metadata)?.inst {
        Inst::Const { ty: Ty::U64, value: Constant::Int(v) } if *v >= 0 => *v as u64,
        _ => return None,
    };
    Some((global, len, vec![ret_val, data, metadata]))
}

/// Trust (wave-24, ref-escape FLIP-COHERENCE): recognize the WRITE triple at `nodes[i..=i+2]` —
/// `agg = Load(*P):Struct` / `new = InsertField(agg, k, v)` / `Store(*P, new)` — where `P` is a
/// `&mut`-param pointer (registered in `fwd_ptr_params`). Returns `(arg place of P, field index k,
/// stored value id v)` so the caller can emit the byte-faithful MIR field assign `(*P).k = v` (the
/// exact `[Deref, Field(k)]` place shape rustc's builder produces for `s.k = v`). Returns `None`
/// (the caller falls through to the fail-closed `Load` handler) unless EVERY structural condition
/// holds: adjacency, a registered `Ty::Struct` pointee, matching `agg`/`new`/`P`, non-volatile,
/// unaligned. Single-use of `agg`/`new` is enforced downstream by construction — skipping their
/// defining nodes leaves any OTHER use referencing an undefined value, which fails closed.
fn recognize_field_write<'tcx>(
    fwd_ptr_params: &HashMap<ValueId, Place<'tcx>>,
    nodes: &[InstrNode],
    i: usize,
) -> Option<(Place<'tcx>, u32, ValueId)> {
    if i + 2 >= nodes.len() {
        return None;
    }
    let Inst::Load { ty, ptr, volatile: false, align: None } = &nodes[i].inst else {
        return None;
    };
    // Trust (wave-IL R1): THIS GATE IS LOAD-BEARING FOR ANOTHER WAVE. `aggregate_load_refusal`
    // deliberately omits `Ty::Struct` so this idiom stays alive, which makes `Ty::Struct(_)` here
    // the ONLY thing keeping a non-struct whole-aggregate `Load` out of the triple recognizer.
    // Widening it (an enum field-write idiom, say) is a decision about wave-IL's flip exclusion
    // too, not just about this recognizer — `test_field_write_recognizer_is_struct_only` pins it
    // so that decision has to be taken explicitly.
    if !matches!(ty, Ty::Struct(_)) {
        return None;
    }
    let argplace = *fwd_ptr_params.get(ptr)?;
    let agg = *nodes[i].results.first()?;
    let Inst::InsertField { aggregate, field, value, .. } = &nodes[i + 1].inst else {
        return None;
    };
    if *aggregate != agg {
        return None;
    }
    let new = *nodes[i + 1].results.first()?;
    let (field, value) = (*field, *value);
    let Inst::Store { ptr: sptr, value: sval, volatile: false, align: None, .. } =
        &nodes[i + 2].inst
    else {
        return None;
    };
    if *sptr != *ptr || *sval != new {
        return None;
    }
    Some((argplace, field, value))
}

/// Trust (wave-29, interior-borrow-return FLIP): given a ref-param pointee struct `s_ty` and the
/// returned reference's pointee `t_ty`, find the UNIQUE field of `s_ty` whose declared type is
/// `t_ty` AND whose byte offset is 0. This inverts the producer's wave-25 `field_byte_offset` gate
/// (which only emitted the flippable bare-ptr `return pv` shape for an offset-0 field) to recover
/// the field index the shim must borrow. Mirrors `lib.rs::field_byte_offset` exactly: a single-field
/// struct's sole field sits at offset 0 by construction (no layout query); a multi-field struct's
/// offsets come ONLY from rustc's authoritative `layout.fields.offset`; unresolved input is
/// rejected before the query because this shim is called from the `mir_built` differential path,
/// where opaque/generic normalization can query-cycle. The caller
/// enforces `t_ty` scalar (`flip::scalar_ok`), so two matching fields can never share offset 0
/// (scalars are non-ZST) → the offset-0 match is unique. Returns `None` on non-struct `s_ty`,
/// no matching field, or an ambiguous (ZST-tie) match.
fn interior_field_at_offset_zero<'tcx>(
    tcx: TyCtxt<'tcx>,
    s_ty: RustcTy<'tcx>,
    t_ty: RustcTy<'tcx>,
) -> Option<(u32, RustcTy<'tcx>)> {
    let ty::Adt(adt, args) = s_ty.kind() else {
        return None;
    };
    if !adt.is_struct() {
        return None;
    }
    let variant = adt.non_enum_variant();
    let nfields = variant.fields.len();
    if nfields == 0 {
        return None;
    }
    // Single-field struct: the sole field is at offset 0 by construction — no layout query (and so
    // this path stays alive for a generic single-field newtype whose layout query is unavailable).
    let layout = if nfields == 1 {
        None
    } else {
        if !crate::layout_query_is_reentrant_safe(s_ty) {
            return None;
        }
        let te = ty::TypingEnv::fully_monomorphized();
        Some(crate::cycle_safe_layout_of(tcx, te, s_ty)?)
    };
    let mut found: Option<(u32, RustcTy<'tcx>)> = None;
    for (idx, fdef) in variant.fields.iter().enumerate() {
        // Trust: rust 1.99 — `FieldDef::ty` returns `Unnormalized<Ty>`; unwrap with
        // `.skip_normalization()` (the offset-0 scalar-field match below is structural).
        let fty = fdef.ty(tcx, args).skip_normalization();
        if fty != t_ty {
            continue;
        }
        let at_zero = match &layout {
            // Bounds-check: `offset` panics out of range, and a layout may
            // carry fewer field entries than the ADT declares.
            Some(l) if idx < l.fields.count() => l.fields.offset(idx).bytes() == 0,
            Some(_) => false,
            None => true,
        };
        if at_zero {
            if found.is_some() {
                // Two same-type fields at offset 0 (only possible via ZSTs, which `t_ty` scalar
                // excludes) — refuse rather than guess.
                return None;
            }
            found = Some((idx as u32, fty));
        }
    }
    found
}

/// Coarse variant name for an unhandled instruction (kept `&'static` so reasons stay stable
/// for tallying; the full node is deliberately not dumped into the reason).
fn inst_name(inst: &Inst) -> &'static str {
    match inst {
        Inst::BinOp { .. } => "BinOp",
        Inst::UnOp { .. } => "UnOp",
        Inst::Overflow { .. } => "Overflow",
        Inst::ICmp { .. } => "ICmp",
        Inst::FCmp { .. } => "FCmp",
        Inst::Cast { .. } => "Cast",
        Inst::Load { .. } => "Load",
        Inst::Store { .. } => "Store",
        Inst::Alloca { .. } => "Alloca",
        Inst::HeapAlloc { .. } => "HeapAlloc",
        Inst::GEP { .. } => "GEP",
        Inst::Br { .. } => "Br",
        Inst::CondBr { .. } => "CondBr",
        Inst::Switch { .. } => "Switch",
        Inst::Call { .. } => "Call",
        Inst::CallIndirect { .. } => "CallIndirect",
        Inst::Return { .. } => "Return",
        Inst::ExtractField { .. } => "ExtractField",
        Inst::InsertField { .. } => "InsertField",
        Inst::ExtractElement { .. } => "ExtractElement",
        Inst::InsertElement { .. } => "InsertElement",
        Inst::Const { .. } => "Const",
        Inst::Undef { .. } => "Undef",
        Inst::Assume { .. } => "Assume",
        Inst::Assert { .. } => "Assert",
        Inst::Unreachable => "Unreachable",
        Inst::Copy { .. } => "Copy",
        Inst::Select { .. } => "Select",
        _ => "Other",
    }
}

/// trust-ir scalar -> the rustc type it denotes. `None` for every non-scalar (fail-closed at the
/// caller). Since v25 B1 every scalar (including `Isize`/`Usize`/`Char`) has exactly ONE rustc
/// denotation, so this is the single source of truth — the former per-body `PtrSpell` respell
/// is retired (module docs, POINTER-WIDTH RESPELL — RETIRED).
fn scalar_rustc_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: &Ty) -> Option<RustcTy<'tcx>> {
    Some(match ty {
        Ty::Bool => tcx.types.bool,
        Ty::I8 => tcx.types.i8,
        Ty::I16 => tcx.types.i16,
        Ty::I32 => tcx.types.i32,
        Ty::I64 => tcx.types.i64,
        Ty::I128 => tcx.types.i128,
        Ty::U8 => tcx.types.u8,
        Ty::U16 => tcx.types.u16,
        Ty::U32 => tcx.types.u32,
        Ty::U64 => tcx.types.u64,
        Ty::U128 => tcx.types.u128,
        // Trust (wave-FL): the two IEEE float widths join the scalar fragment. F16/F128 stay
        // OUT (no proven scalar-fragment codegen path) — they return None here → fail closed.
        Ty::F32 => tcx.types.f32,
        Ty::F64 => tcx.types.f64,
        // Trust (v25 B1): the faithful scalars denote DIRECTLY — one trust-ir
        // type -> exactly one rustc type again (this is what retires the
        // PtrSpell inversion and the char/u32 flip carve-out).
        Ty::Isize => tcx.types.isize,
        Ty::Usize => tcx.types.usize,
        Ty::Char => tcx.types.char,
        _ => return None,
    })
}

/// The trust-ir scalar spellings the shim can denote — bool + the fixed-width ints + the two IEEE
/// floats (Trust wave-FL) + the v25 B1 faithful scalars (isize/usize/char, each with its own
/// unambiguous global spelling). Backs the reverse lookup (`scalar_rustc_ty(c) == Some(rustc)`).
/// F16/F128 stay OUT (fail closed).
const SCALAR_CANDS: [Ty; 16] = [
    Ty::Bool,
    Ty::I8,
    Ty::I16,
    Ty::I32,
    Ty::I64,
    Ty::I128,
    Ty::U8,
    Ty::U16,
    Ty::U32,
    Ty::U64,
    Ty::U128,
    Ty::F32,
    Ty::F64,
    Ty::Isize,
    Ty::Usize,
    Ty::Char,
];

/// Trust (wave-C): re-materialize the lifetime-free `SiteArg` encoding into an intern-equal
/// `GenericArgsRef` — the SITE args built MIR spells in the `FnDef(site_def_id, _)` func operand.
/// The encoder (`crate::encode_site_args`) preserved every arg 1:1 (type args only; a region/const
/// arg made the whole callee un-encodable), so this rebuild yields the exact interned args, which
/// the comparator's `raw_call_channel` re-verifies pairwise. A lossy rebuild would produce a
/// non-matching `FnDef` → no `DerivedAgreed` → clean-only (miss a flip, never a wrong one).
fn rebuild_site_args<'tcx>(tcx: TyCtxt<'tcx>, enc: &[SiteArg]) -> ty::GenericArgsRef<'tcx> {
    tcx.mk_args_from_iter(enc.iter().map(|a| match a {
        SiteArg::Ty(t) => ty::GenericArg::from(rebuild_site_ty(tcx, t)),
        // Trust (wave-CR): a lifetime arg → `ReErased`. Built's real region differs, but the
        // comparator's raw-call channel erases regions on both sides before pinning callee identity,
        // so this rebuilt `FnDef` compares equal on did+type/const args (SOUND — region-only-different
        // FnDefs codegen identically). The rebuilt `GenericArgs` is a valid interned args list (a
        // region param position takes `ReErased`); the value-arg ABI/DST gates are unaffected (regions
        // carry no ABI).
        SiteArg::ErasedRegion => ty::GenericArg::from(tcx.lifetimes.re_erased),
    }))
}

fn rebuild_site_ty<'tcx>(tcx: TyCtxt<'tcx>, t: &SiteTy) -> RustcTy<'tcx> {
    match t {
        SiteTy::Bool => tcx.types.bool,
        SiteTy::Char => tcx.types.char,
        SiteTy::Str => tcx.types.str_,
        SiteTy::Int(i) => RustcTy::new_int(tcx, *i),
        SiteTy::Uint(u) => RustcTy::new_uint(tcx, *u),
        SiteTy::Float(f) => RustcTy::new_float(tcx, *f),
        SiteTy::Tuple(ts) => {
            RustcTy::new_tup_from_iter(tcx, ts.iter().map(|e| rebuild_site_ty(tcx, e)))
        }
        SiteTy::Slice(el) => RustcTy::new_slice(tcx, rebuild_site_ty(tcx, el)),
        SiteTy::Array(el, n) => RustcTy::new_array(tcx, rebuild_site_ty(tcx, el), *n),
        SiteTy::Adt(did, args) => {
            let adt = tcx.adt_def(*did);
            let ga = tcx.mk_args_from_iter(
                args.iter().map(|e| ty::GenericArg::from(rebuild_site_ty(tcx, e))),
            );
            RustcTy::new_adt(tcx, adt, ga)
        }
    }
}

fn int_width(ty: &Ty) -> Option<u32> {
    Some(match ty {
        Ty::I8 | Ty::U8 => 8,
        Ty::I16 | Ty::U16 => 16,
        // Trust (v25 B1): char's 32-bit carrier joins the width table (its
        // Unicode range is a value property, not a width one).
        Ty::I32 | Ty::U32 | Ty::Char => 32,
        // Trust (v25 B1): pointer-width ints at the pinned 64-bit target.
        Ty::I64 | Ty::U64 | Ty::Isize | Ty::Usize => 64,
        Ty::I128 | Ty::U128 => 128,
        _ => return None,
    })
}

fn is_signed_int(ty: &Ty) -> bool {
    matches!(ty, Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::I128 | Ty::Isize)
}

fn is_unsigned_int(ty: &Ty) -> bool {
    // Trust (v25 B1): char joins the UNSIGNED side for switch/compare
    // re-derivation (its operations are unsigned over the code point).
    matches!(ty, Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128 | Ty::Usize | Ty::Char)
}

fn is_int(ty: &Ty) -> bool {
    is_signed_int(ty) || is_unsigned_int(ty)
}

/// Trust (wave-FL): the two IEEE float widths the shim admits into its scalar fragment.
/// Deliberately NARROWER than `trust_ir::Ty::is_float()` (which also admits `F16`) — F16/F128 stay
/// fail-closed (no proven scalar-fragment codegen path). Gate every float arm on THIS, not `is_float`.
fn is_f32_or_f64(ty: &Ty) -> bool {
    matches!(ty, Ty::F32 | Ty::F64)
}

/// A trust-ir SSA value's MIR denotation: a constant (folded, statement-free — matching the MIR
/// builder's literal folding) or a place (an arg local, a temp, or a projected field of a checked
/// tuple temp). Both payloads are `Copy`.
#[derive(Clone, Copy)]
enum VOp<'tcx> {
    Konst(MirConst<'tcx>),
    Plc(Place<'tcx>),
}

/// Trust (B3-2a): the SAT-perturbation class selected by `-Ztrust-sat-perturb` —
/// the re-landed negative control (the retired TRUST_*_PERTURB env hooks, now a
/// TRACKED flag accepted only with `-Ztrust-verify=off -Ztrust-ir-lower`). Each
/// class deliberately corrupts ONE shim lowering so the flip comparator MUST
/// reject the derived body; a perturbed compile that still flips is a comparator
/// hole. Classes are applied at the exact sites the legacy hooks covered plus
/// the B3-2 seams:
/// `EnumReshape` swaps the folded-variant/otherwise routing; `EnumCaseValue`
/// re-values a folded case PAST the sorted domain (task #107's strengthening —
/// the folded-arm-is-Unreachable blind spot); `EnumCtor` corrupts the emitted
/// discriminant of a recognized construction; `EnumDiscIndex` substitutes the
/// VARIANT INDEX for the effective discriminant (the index-vs-disc seam — inert
/// on default-repr enums, so the smoke must carry explicit discriminants);
/// `SwitchMap` corrupts the case->target MAPPING after the wave-YM sort (a
/// pre-sort reorder would be undone by the sort — the manufactured-green trap).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum SatPerturb {
    EnumReshape,
    EnumCaseValue,
    EnumCtor,
    EnumDiscIndex,
    SwitchMap,
    /// Trust (B3-2b): corrupt the CONSTRUCTED payload — substitute the payload
    /// operand with a same-typed, structurally-distinct constant AFTER the
    /// well-typedness gate (a wrong-typed operand would be a CTFE span_bug
    /// compiler CRASH, not a caught flip — the wave-P hazard; a zeroed payload
    /// is inert under const-fold — the manufactured-green trap).
    EnumPayload,
}

impl SatPerturb {
    fn from_flag(v: &str) -> Option<Self> {
        Some(match v {
            "enum-reshape" => Self::EnumReshape,
            "enum-case-value" => Self::EnumCaseValue,
            "enum-ctor" => Self::EnumCtor,
            "enum-disc-index" => Self::EnumDiscIndex,
            "switch-map" => Self::SwitchMap,
            "enum-payload" => Self::EnumPayload,
            _ => return None,
        })
    }
}

struct ShimCx<'tcx> {
    tcx: TyCtxt<'tcx>,
    span: Span,
    source_info: SourceInfo,
    /// Trust (C2-spans, consumption): the Module's file table, for resolving each
    /// `InstrNode.span` back to a rustc `Span`. See `set_span_from_node`.
    files: Vec<String>,
    /// Trust (C2-scopes): how many entries the rebuilt `source_scopes` table has, so a node's
    /// stamped index can be range-checked before it becomes a `SourceScope`. Always >= 1 (the
    /// outermost scope always exists), which is why a producer that stamps nothing still
    /// yields a valid body.
    scope_count: u32,
    local_decls: IndexVec<Local, LocalDecl<'tcx>>,
    blocks: IndexVec<BasicBlock, BasicBlockData<'tcx>>,
    /// trust-ir SSA value -> its MIR denotation. SSA ids are function-unique, so one flat map.
    env: HashMap<ValueId, VOp<'tcx>>,
    /// OPAQUE param values (slice 3): admitted as arg-local DECLARATIONS only. Deliberately
    /// NOT bound in `env`, so `operand()` fails closed — with the class name — on any use.
    opaque_params: HashMap<ValueId, &'static str>,
    /// Trust (wave-8a): the MIR arg place of each opaque `"Ptr"`-class param (`&T`/`&mut T`/raw
    /// ptr). NOT in `env` (so arithmetic/read uses of it still fail closed via `operand()`), but
    /// consulted by the `Inst::Call` arg lowering to FORWARD the pointer into a call argument —
    /// the one use the fragment proves faithful (built spells `_a = &(*_p); call(move _a)`; the
    /// differential's `ref-alias` L7 binds `_a ↦ _p`, so passing `_p` directly is congruent).
    fwd_ptr_params: HashMap<ValueId, Place<'tcx>>,
    /// Trust (B3-2a): the active SAT-perturbation class (None in every real
    /// compile; Some only under `-Ztrust-sat-perturb` in the burn-in lane) +
    /// the count of applications — a class that never fires is an INERT
    /// control, and the validator must fail on count==0 (the silent-inert
    /// precedent). Logged at body end via the trust_ir_flip info family.
    sat_perturb: Option<SatPerturb>,
    sat_perturb_count: u32,
    /// Trust (enum discriminant-read FLIP): the MIR arg place of each
    /// `"EnumDisc"`-class by-value enum param (`param_rty`). Like `fwd_ptr_params`
    /// it is NOT in `env` (so a bare use of the enum value fails closed in `operand()`), but is
    /// consulted by the `Inst::ExtractField` lowering to re-emit `_d = Discriminant(place)` for
    /// the producer's `extractfield 0` tag read.
    enum_disc_params: HashMap<ValueId, Place<'tcx>>,
    /// Trust (wave-V): each discriminant TEMP the `ExtractField 0` lowering minted, mapped to its
    /// `(source enum place, AdtDef)`. The `Inst::Switch` lowering consults this to recognize a
    /// switch driven by an enum discriminant and reshape it into built's EXHAUSTIVE form (all tag
    /// values explicit + an `Unreachable` otherwise) — the one structural rewrite the enum arc
    /// needs so the comparator reaches DerivedAgreed.
    enum_disc_temps: HashMap<Place<'tcx>, (Place<'tcx>, ty::AdtDef<'tcx>)>,
    /// Trust (enum arc slice 2): the VARIANT a case/default MIR block is reached under — populated
    /// by the `Inst::Switch` enum reshape (each case's discriminant -> its `VariantIdx`, plus the one
    /// folded/default variant). A payload read `extractfield %e, 1+k` inside such a block lowers to a
    /// `Downcast(variant)+Field(k)` place using this map; a block with no known variant fails closed.
    block_variant: HashMap<BasicBlock, rustc_abi::VariantIdx>,
    /// trust-ir block -> its (entry) MIR block. Asserts split trust-ir blocks into MIR chains,
    /// so a trust-ir block's INSTRUCTIONS may span several MIR blocks; this maps to the first.
    block_map: HashMap<BlockId, BasicBlock>,
    /// trust-ir block -> the MIR locals allocated for its block params (one per param, in param
    /// order). Predecessor edges assign these before their goto.
    param_locals: HashMap<BlockId, Vec<Place<'tcx>>>,
    /// Overflow checks on for this crate? Gates shapes whose BUILT counterpart carries asserts
    /// the producer does not model (shifts, `Neg`) — those must fail closed, not falsely agree.
    overflow_checks: bool,
}

/// Trust (C2-scopes, consumption): rebuild MIR's `source_scopes` from the Module's tree.
///
/// Entry 0 is always minted HERE, from the body span `tcx` already gave us, rather than from
/// the producer — one location, one owner, nothing to disagree about. Producer entry 0 is the
/// same root and contributes only its (absent) span.
///
/// FAILS CLOSED on any topology violation. A malformed tree is a producer bug, and the
/// alternative — flattening to a single scope and carrying on — would hand a debugger a body
/// claiming every binding is visible everywhere. Refusing the flip for that body costs an
/// optimization opportunity; the flattening costs correctness of the thing being built.
///
/// `lint_root` is the fn's own `HirId` for every entry: the producer only ever opens
/// `let`-visibility scopes, which built creates with `LintLevel::Inherited`, and inheriting
/// through a chain rooted at the fn yields exactly the fn's lint root at every depth.
/// The scope table's structural invariant, as a pure check so it can be TESTED — the rest of
/// `build_source_scopes` needs a `TyCtxt` and cannot be. Returns the failing rule's name, or
/// `None` when the table is well-formed.
///
/// `parent < index` is doing double duty: it forbids cycles (a cycle needs some edge pointing
/// forward or to itself) AND it guarantees a single forward pass suffices, because a scope's
/// parent is always already built when the scope is reached.
fn scope_topology_error(scopes: &[trust_ir::ScopeData]) -> Option<&'static str> {
    match scopes.first() {
        None => return Some("scope table present but empty"),
        Some(root) if root.parent.is_some() => return Some("scope 0 is not the root"),
        Some(_) => {}
    }
    for (i, sc) in scopes.iter().enumerate().skip(1) {
        match sc.parent {
            None => return Some("non-root scope without a parent"),
            Some(p) if p as usize >= i => {
                return Some("scope parent is not earlier than the scope");
            }
            Some(_) => {}
        }
    }
    None
}

fn build_source_scopes<'tcx>(
    tcx: TyCtxt<'tcx>,
    hir_id: rustc_hir::HirId,
    body_span: Span,
    files: &[String],
    scopes: Option<&[trust_ir::ScopeData]>,
) -> Result<IndexVec<SourceScope, SourceScopeData<'tcx>>, Unsupported> {
    let mk = |span: Span, parent: Option<SourceScope>| SourceScopeData {
        span,
        parent_scope: parent,
        inlined: None,
        inlined_parent_scope: None,
        // These scopes are reconstructed from TrustIR lexical metadata, not
        // minted from an authored Rust loop query. They must never supply E4/E5
        // source-loop identity authority.
        local_data: ClearCrossCrate::Set(SourceScopeLocalData {
            lint_root: hir_id,
            trust_loop_hir_local_id: None,
        }),
    };
    let mut out: IndexVec<SourceScope, SourceScopeData<'tcx>> = IndexVec::new();
    out.push(mk(body_span, None));
    let Some(scopes) = scopes else { return Ok(out) };
    if let Some(err) = scope_topology_error(scopes) {
        return unsup(err);
    }
    for (i, sc) in scopes.iter().enumerate().skip(1) {
        // Sound by `scope_topology_error` above: entry `i > 0` has a parent, and it is `< i`,
        // so the parent's `SourceScopeData` is already pushed and readable.
        let parent = SourceScope::from_u32(sc.parent.unwrap_or(0));
        let _ = i;
        // A scope whose location did not survive inherits its parent's. Unlike an instruction
        // span there is no "current location" to keep, and a `DUMMY_SP` scope would make
        // codegen mint a lexical block at line 0.
        let span = sc
            .span
            .and_then(|s| span_from_source_span(tcx, files, s))
            .unwrap_or(out[parent].span);
        out.push(mk(span, Some(parent)));
    }
    Ok(out)
}

/// Trust (C2-spans): a trust-ir `SourceSpan` -> a zero-length rustc `Span` at that point.
/// Shared by instruction spans and scope spans so the two can never drift apart.
///
/// `SourceSpan.col` counts CHARS (`lookup_char_pos` returns `CharPos`); a rustc `BytePos`
/// needs the byte offset of that char within the line — approximating chars as bytes lies on
/// any non-ASCII line, so the line text is walked.
///
/// `col == <chars in line>` is a REAL position — one past the last character, before the
/// newline — and it is the one built MIR uses most: `shrink_to_hi()` on a body span lands
/// exactly there for the fn-end return terminator. It is resolved exactly, to the line's byte
/// length. Only `col >` that is out of range, and that fails closed (returns `None`, caller
/// keeps whatever location it had) rather than approximating: a span pointing at a
/// plausible-but-wrong column is worse than no span, because the debugger reports it with
/// confidence and the reader cannot tell it is fiction.
///
/// This distinction is recorded because getting it wrong is measurable in both directions,
/// and both mistakes were made here in turn. The original code ended with
/// `unwrap_or(line_text.len())`, which is correct for `col == len` and fiction beyond it.
/// Reading built's epilogue rows (legitimately at `len + 1` in 1-based DWARF columns) as
/// evidence of that fallback firing, I removed the whole branch — which turned the single
/// most common end-of-line span into "no span", and `llvm-dwarfdump` immediately showed
/// derived epilogue rows collapsing onto the previous statement's line. Reject what is out
/// of range; resolve what is merely at the edge.
fn span_from_source_span(
    tcx: TyCtxt<'_>,
    files: &[String],
    sp: trust_ir::SourceSpan,
) -> Option<Span> {
    let path = files.get(sp.file as usize)?;
    let sm = tcx.sess.source_map();
    let file = sm
        .files()
        .iter()
        .find(|f| f.name.prefer_local_unconditionally().to_string() == *path)
        .cloned()?;
    if sp.line == 0 {
        return None;
    }
    let line_idx = (sp.line - 1) as usize;
    if line_idx >= file.count_lines() {
        return None;
    }
    let bounds = file.line_bounds(line_idx);
    let line_text = file.get_line(line_idx)?;
    let col = sp.col as usize;
    let byte_in_line = match line_text.char_indices().nth(col) {
        Some((byte, _)) => byte,
        // Exactly one past the last char: the end-of-line position, not an overrun.
        None if col == line_text.chars().count() => line_text.len(),
        None => return None,
    };
    let lo = bounds.start + rustc_span::BytePos(u32::try_from(byte_in_line).ok()?);
    if lo >= bounds.end {
        return None;
    }
    Some(Span::with_root_ctxt(lo, lo))
}

impl<'tcx> ShimCx<'tcx> {
    /// Trust (C2-spans, consumption): re-point `source_info` at an instruction's stamped
    /// location. Unstamped nodes (terminators; pre-span producers) keep the CURRENT span —
    /// sticky attribution, so an assert split mid-chain inherits the arithmetic node's span.
    ///
    /// `SourceSpan.col` counts CHARS (`lookup_char_pos` returns `CharPos`); a rustc `BytePos`
    /// needs the byte offset of that char within the line — approximating chars as bytes lies
    /// on any non-ASCII line, so the line text is walked. Every failure keeps the current
    /// `source_info` (metadata must never fail a body).
    fn set_span_from_node(&mut self, node: &InstrNode) {
        // Trust (C2-scopes): scope FIRST and independently of the span. The two halves fail
        // separately — an unlocatable instruction may still have a known scope, and vice
        // versa — so an early return on one must not silently skip the other. An index past
        // the table is dropped, not clamped: the producer and consumer disagreeing about the
        // tree is exactly when guessing does damage.
        if let Some(scope) = node.scope {
            if scope < self.scope_count {
                self.source_info.scope = SourceScope::from_u32(scope);
            }
        }
        let Some(sp) = node.span else { return };
        let Some(span) = span_from_source_span(self.tcx, &self.files, sp) else { return };
        self.source_info.span = span;
    }

    fn temp(&mut self, ty: RustcTy<'tcx>) -> Place<'tcx> {
        Place::from(self.local_decls.push(LocalDecl::with_source_info(ty, self.source_info)))
    }

    /// [`scalar_rustc_ty`], the single type-denotation entry point for body
    /// construction. Since v25 B1 the denotation is global and unambiguous
    /// (the former per-body `PtrSpell` respell is retired).
    fn scalar_ty(&self, ty: &Ty) -> Option<RustcTy<'tcx>> {
        scalar_rustc_ty(self.tcx, ty)
    }

    /// Trust (wave-E): the inverse of [`scalar_ty`] — find the trust-ir scalar whose denotation
    /// equals `ty`. Since v25 B1 the denotation is global and injective over `SCALAR_CANDS`
    /// (isize/usize/char have their own first-class spellings — the former per-body respell
    /// recovery is retired), so the `find` is unambiguous; a non-scalar `ty` yields `None`
    /// → fail closed.
    fn ir_scalar_of_body(&self, ty: RustcTy<'tcx>) -> Option<Ty> {
        SCALAR_CANDS.into_iter().find(|c| self.scalar_ty(c) == Some(ty))
    }

    fn new_block(&mut self) -> BasicBlock {
        self.blocks.push(BasicBlockData::new(None, false))
    }

    fn push_stmt(&mut self, bb: BasicBlock, kind: StatementKind<'tcx>) {
        self.blocks[bb].statements.push(Statement::new(self.source_info, kind));
    }

    fn assign(&mut self, bb: BasicBlock, place: Place<'tcx>, rvalue: Rvalue<'tcx>) {
        self.push_stmt(bb, StatementKind::Assign(Box::new((place, rvalue))));
    }

    fn terminate(&mut self, bb: BasicBlock, kind: TerminatorKind<'tcx>) -> Result<(), Unsupported> {
        if self.blocks[bb].terminator.is_some() {
            // Defensive: a trust-ir block with two terminators is malformed input.
            return unsup("double terminator in one block");
        }
        // Trust: rust 1.99 — `Terminator` grew an `attributes: ThinVec<AttributeKind>` field.
        // Plain lowering carries none (rustc_mir_build's `CFG::terminate` passes
        // `ThinVec::new()`); `Default::default()` is the same empty value, byte-identical
        // to what built MIR carries.
        self.blocks[bb].terminator = Some(Terminator {
            source_info: self.source_info,
            kind,
            attributes: Default::default(),
        });
        Ok(())
    }

    /// The MIR operand denoting trust-ir value `v`: `Operand::Copy` for a `Copy` type,
    /// `Operand::Move` for a non-`Copy` (Drop-free) place. Trust (wave-GH2) NOTE: this does NOT
    /// always match built's operand KIND — built spells the LAST use of a `Copy`-typed rvalue temp
    /// as `Move` (as_operand temp discipline) where this returns `Copy`. That skew is congruent
    /// under LEDGER L8 and codegen-invisible for Immediate/Pair operands, but ABI-VISIBLE for a
    /// memory-ABI struct call arg — the Call arm re-spells that exact case to `Move` (parity), and
    /// the flip gate fail-closes any residual memory-ABI whole-struct `Copy` arg.
    /// Trust (wave-X): pre-wave-X every fragment place was a scalar/`Copy` type, so this was
    /// unconditionally `Copy`; the relaxed aggregate-return gate now admits a NON-`Copy` Drop-free
    /// struct return/field, and a bare whole-struct `Copy` of a non-`Copy` type is ILL-TYPED →
    /// MIR-validation ICE at flip time. `Move` is always well-typed, is exactly what built emits
    /// for a non-`Copy` place (built can never emit `Copy` of one), and the comparator folds
    /// `Move`≡`Copy` (`operand_expr` LEDGER L8) → `DerivedAgreed` is unaffected. The shim is
    /// concrete-only (param_rty rejects generic params), so `fully_monomorphized` copy-check is safe.
    fn operand(&self, v: ValueId) -> Result<Operand<'tcx>, Unsupported> {
        match self.env.get(&v) {
            Some(VOp::Konst(c)) => Ok(Operand::Constant(Box::new(ConstOperand {
                span: self.span,
                user_ty: None,
                const_: *c,
            }))),
            Some(VOp::Plc(p)) => {
                let pty = p.ty(&self.local_decls, self.tcx).ty;
                let te = ty::TypingEnv::fully_monomorphized();
                if crate::cycle_safe_is_copy(self.tcx, te, pty) {
                    Ok(Operand::Copy(*p))
                } else {
                    Ok(Operand::Move(*p))
                }
            }
            None => match self.opaque_params.get(&v) {
                // Slice 3: opaque non-scalar params are declaration-only; ANY value use of
                // one is outside the fragment (the shim does not model ops over them).
                Some(class) => unsup(format!("use of opaque {class} param value v{}", v.index())),
                None => unsup(format!("use of undefined value v{}", v.index())),
            },
        }
    }

    /// Trust (wave-29, interior-borrow-return FLIP): reconstruct the real interior shared borrow
    /// `&((*arg_place).K)` that the producer erased to a bare-ptr `return pv` (wave-25, offset-0
    /// field). `s_ty` is the ref-param pointee struct, `t_ty` the returned reference's (scalar)
    /// pointee. `K` is the UNIQUE offset-0 field of type `t_ty` — since the producer only emitted
    /// `return pv` for an offset-0 field, that field IS the one built borrowed, so the reconstructed
    /// `[Deref, Field(K)]` borrow is byte-identical to built (the differential's `iref(a{p},K)`
    /// observable independently re-pins K on both sides — a wrong K → mismatch → no flip). Fails
    /// closed (→ `DerivedUnsupported` → clean-only, exactly wave-25) when `s_ty` is not a concrete
    /// struct with such a unique field.
    fn reconstruct_interior_borrow(
        &self,
        arg_place: Place<'tcx>,
        s_ty: RustcTy<'tcx>,
        t_ty: RustcTy<'tcx>,
    ) -> Result<Rvalue<'tcx>, Unsupported> {
        let (k, field_ty) = match interior_field_at_offset_zero(self.tcx, s_ty, t_ty) {
            Some(kf) => kf,
            None => {
                return unsup(
                    "interior-borrow return: no unique scalar offset-0 field of the return type",
                );
            }
        };
        // Exactly the `[Deref, Field(K)]` place shape rustc's builder emits for `&self.field`
        // (mirrors the wave-24 field-store construction), borrowed SHARED with an erased region
        // (post-analysis `Runtime(Optimized)` MIR erases all regions, matching the built `_0` type).
        let deref = self.tcx.mk_place_deref(arg_place);
        let fplace = self.tcx.mk_place_field(deref, FieldIdx::from_u32(k), field_ty);
        Ok(Rvalue::Ref(self.tcx.lifetimes.re_erased, BorrowKind::Shared, fplace))
    }

    /// Trust (wave-30, interior-borrow-as-ARG FLIP): the CALL-ARG twin of `reconstruct_interior_borrow`.
    /// When a forwarded ptr param (`got` = `&S`) is passed where the callee wants `want` = `&T` (T a
    /// scalar) — the `g(&self.field)` case the producer erased to the base ptr — reconstruct the real
    /// `&((*place).K)` interior borrow, typed `want`. `Some(rvalue)` iff both `got` and `want` are
    /// SHARED refs and `T ∈ {bool,int,uint}` (= flip::scalar_ok / wave-29 gate) and `S` has a unique
    /// offset-0 field of type `T`; `None` otherwise → the caller forwards the raw ptr, which fails the
    /// exact arg-type check (clean-only preserved, exactly as before wave-30).
    fn try_reconstruct_interior_arg(
        &self,
        place: Place<'tcx>,
        got: RustcTy<'tcx>,
        want: RustcTy<'tcx>,
    ) -> Option<Rvalue<'tcx>> {
        let (s_ty, t_ty) = match (got.kind(), want.kind()) {
            (ty::Ref(_, s, gm), ty::Ref(_, t, wm)) if gm.is_not() && wm.is_not() => (*s, *t),
            _ => return None,
        };
        if !matches!(t_ty.kind(), ty::Bool | ty::Int(_) | ty::Uint(_)) {
            return None;
        }
        self.reconstruct_interior_borrow(place, s_ty, t_ty).ok()
    }

    /// trust-ir constant -> `mir::Const`. Ints are masked to the type width before
    /// `Const::from_bits` (which expects in-range bits).
    fn const_of(&self, ty: &Ty, c: &Constant) -> Result<MirConst<'tcx>, Unsupported> {
        // Trust (wave-UA): the value-less refusal runs FIRST, as this shim's own predicate.
        // See `unit_const_refusal` for why it is a predicate and not a `_ =>` fall-through.
        if let Some(reason) = unit_const_refusal(ty, c) {
            return unsup(reason);
        }
        match (ty, c) {
            (Ty::Bool, Constant::Bool(b)) => Ok(MirConst::from_bool(self.tcx, *b)),
            (t, Constant::Int(v)) if is_int(t) => {
                let w = int_width(t).expect("is_int implies width");
                let bits: u128 =
                    if w == 128 { *v as u128 } else { (*v as u128) & (u128::MAX >> (128 - w)) };
                // The const carries the type's one global denotation (v25 B1:
                // an isize/usize/char const is isize/usize/char-typed, exactly
                // like the built body's const).
                let rty = match self.scalar_ty(t) {
                    Some(rt) => rt,
                    None => return unsup("non-scalar const type"),
                };
                Ok(MirConst::from_bits(self.tcx, bits, ty::TypingEnv::fully_monomorphized(), rty))
            }
            // Trust-IR v24's canonical spelling for the upper half of u128.
            // It is legal only against `Ty::U128`; every smaller/other type
            // fails closed instead of truncating a 128-bit value.
            (Ty::U128, Constant::U128(v)) => {
                let rty = self.tcx.types.u128;
                Ok(MirConst::from_bits(self.tcx, *v, ty::TypingEnv::fully_monomorphized(), rty))
            }
            // Trust: first-class struct values (`Ty::Struct` seeds) are OUTSIDE the shim
            // fragment — a struct body must never reach the flip. An OWN stable reason class
            // (not the generic one below) keeps the derived-verdict histogram diagnosable.
            (Ty::Struct(_), _) => unsup("Const(struct value)"),
            // Trust (B3-2a E4): the C-LIKE single-head seed — `Aggregate([Int(disc)])`
            // at `Ty::Enum` — is exactly the general niladic construction constant the
            // E1 recognizer skips at RETURN position; at non-return positions (a
            // `let e = E::A;` local) it must materialize. It cannot be spelled as a
            // MIR scalar here without the Adt identity, so this wall arm stays for it
            // TOO — but with its OWN reason so the histogram separates "C-like local
            // materialization" (a 2b lever) from genuinely-unsupported payload seeds.
            (Ty::Enum(_), Constant::Aggregate(seeds))
                if seeds.len() == 1 && matches!(seeds[0], Constant::Int(_)) =>
            {
                unsup("Const(enum value: C-like local)")
            }
            // Trust (wave-5): first-class GENERAL-enum values (`Ty::Enum` seeds) — same
            // fail-closed wall, own reason class for the histogram.
            (Ty::Enum(_), _) => unsup("Const(enum value)"),
            // Trust (wave-FL): float constants. The producer carries every float as an f64
            // (`Constant::Float(f64)`, bit-exact). Bits are the IEEE pattern typed by the float
            // rustc ty — EXACTLY built's shape (`MirConst::from_bits`, same as the int arm). For F32
            // the f64 carrier must round-trip losslessly through f32 or the emitted const could
            // byte-differ from built — fail closed otherwise (defense-in-depth per the f32-nan
            // carrier lesson; also fails an f32 NaN closed, which is fine/fail-safe). The comparator
            // renders both sides' `ConstValue::FloatBits` as an injective `c:fbits:` token, so a
            // wrong reconstructed value can only miss a flip, never ship a wrong one (AXIS-B).
            (t, Constant::Float(v)) if is_f32_or_f64(t) => {
                let rty = match self.scalar_ty(t) {
                    Some(rt) => rt,
                    None => return unsup("non-scalar float const type"),
                };
                let bits: u128 = match t {
                    Ty::F64 => (*v).to_bits() as u128,
                    Ty::F32 => {
                        if (*v as f32) as f64 != *v {
                            return unsup("lossy f64->f32 float const carrier");
                        }
                        (*v as f32).to_bits() as u128
                    }
                    _ => return unsup("float const on non-f32/f64 type"),
                };
                Ok(MirConst::from_bits(self.tcx, bits, ty::TypingEnv::fully_monomorphized(), rty))
            }
            _ => unsup("Const(non int/bool)"),
        }
    }
}

/// The rustc type an arg local declares for trust-ir param `p`, given the BUILT body's decl
/// type `built` for the same position (slice 3 threading; see module docs). Returns
/// `(rustc_ty, Some(class))` for the opaque classes, `(rustc_ty, None)` for scalars.
/// Fail-closed on any shape the widening cannot PROVE faithful.
fn param_rty<'tcx>(
    tcx: TyCtxt<'tcx>,
    p: &Ty,
    built: RustcTy<'tcx>,
) -> Result<(RustcTy<'tcx>, Option<&'static str>), Unsupported> {
    // Scalars: the shim's own denotation (v25 B1: one trust-ir scalar -> exactly one rustc
    // type, isize/usize/char included — no per-body respell).
    if let Some(srt) = scalar_rustc_ty(tcx, p) {
        return Ok((srt, None));
    }
    match p {
        // Closure envs (`&{closure}` / `&mut {closure}`) and plain refs; the producer maps
        // every thin ref to `Ty::Ptr` (lib.rs map_ty), raw pointers are fail-closed there
        // but admitted here defensively should the producer ever widen.
        Ty::Ptr => match built.kind() {
            ty::Ref(..) | ty::RawPtr(..) => Ok((built, Some("Ptr"))),
            _ => unsup(format!("param widening: trust-ir Ptr vs built non-ref/ptr {built:?}")),
        },
        // Trust (B2-3): a trait-object fat param — thread the BUILT `&dyn Trait` through
        // as the decl type (byte-identical on both sides; the B2-2 `FatPtr(Str)` return-
        // arm precedent) iff built is the matching SHARED dyn ref. Declared opaque like
        // `Ptr`: the flip gates key on the built rustc type (`opaque_arg_ty_ok` admits
        // any `ty::Ref`), so the pre-existing &dyn flip lanes survive the producer's fat
        // respell with zero flip.rs changes — the class marker below keeps the one
        // to_mir-side consumer (forwarding into a call arg) enabled.
        Ty::FatPtr(trust_ir::FatPtrKind::TraitObject { .. }) => match built.kind() {
            ty::Ref(_, pointee, m) if matches!(pointee.kind(), ty::Dynamic(..)) && m.is_not() => {
                Ok((built, Some("FatPtr(dyn)")))
            }
            _ => unsup(format!(
                "param widening: trust-ir FatPtr(TraitObject) vs built non-&dyn {built:?}"
            )),
        },
        // Real `()` params, and the by-value NON-capturing FnOnce closure env (a ZST the
        // producer signs `Ty::Unit`, matching the MIR-side oracle's convention).
        Ty::Unit => {
            if built.is_unit() {
                return Ok((built, Some("Unit")));
            }
            match built.kind() {
                ty::Closure(_, args) if args.as_closure().upvar_tys().is_empty() => {
                    Ok((built, Some("Unit(zst-closure-env)")))
                }
                _ => unsup(format!("param widening: trust-ir Unit vs built {built:?}")),
            }
        }
        // Scalar tuples (incl. the checked-pair shape). Arity + per-position scalar
        // equality proven against the built tuple; reads still fail closed (opaque).
        // Raw `scalar_rustc_ty` here is deliberate: this is a faithfulness PREDICATE on a
        // declaration-only param (the built type is threaded wholesale), not a type
        // materialization — a pointer-width tuple elem vs a built isize/usize field stays
        // fail-closed, byte-for-byte the pre-respell behavior.
        Ty::Tuple(elems) => match built.kind() {
            ty::Tuple(fields) if fields.len() == elems.len() => {
                for (e, f) in elems.iter().zip(fields.iter()) {
                    match scalar_rustc_ty(tcx, e) {
                        Some(srt) if srt == f => {}
                        _ => {
                            return unsup(format!(
                                "param widening: tuple elem {e:?} vs built {f:?}"
                            ));
                        }
                    }
                }
                Ok((built, Some("Tuple")))
            }
            // Trust (B3-2c T2 slice 2): the wave-V/YM legacy-model EnumDisc Tuple
            // param arm is DELETED — the producer no longer spells any enum as
            // Ty::Tuple([I64, payload]); every enum param is Ty::Enum (general
            // lane) or opaque.
            _ => unsup(format!("param widening: trust-ir Tuple vs built {built:?}")),
        },
        // Trust (wave-F): a by-value Drop-free (concrete, `!needs_drop`) STRUCT param. Bound in `env`
        // as a READABLE whole-struct place (opacity `None`); scalar FIELD reads (`Inst::ExtractField`)
        // fold into a field-projected place. Its IDENTITY (DefId + args) is ABI-gate-pinned (flip.rs
        // re-checks the arg-local rustc type against built), the SAME anchor wave-D used for
        // `built_ret_ty` on the return — so the args-free extraction name cannot hide a
        // cross-instantiation. `!needs_drop` (looser than Copy — admits e.g. `struct A{a:isize}`)
        // keeps `ElaborateDrops` a no-op → pass-totality. Concrete-only (a generic `S<T>` param fails
        // the param guard → clean-only). The flip gate's `struct_args_read_only` confines every use to
        // a scalar field read, so the shim never emits a bare whole-struct `Copy(_1)` (which would be
        // ill-typed for a non-Copy struct → MIR-validation ICE). Drop-bearing / non-struct → catch-all.
        Ty::Struct(_) => {
            if built.has_non_region_param() || built.has_non_region_infer() {
                return unsup("struct param has generic params (concrete-only slice)");
            }
            let te = ty::TypingEnv::fully_monomorphized();
            match built.kind() {
                ty::Adt(adt, _)
                    if adt.is_struct() && !crate::cycle_safe_needs_drop(tcx, te, built) =>
                {
                    Ok((built, None))
                }
                _ => unsup(format!("non-scalar param type {p:?} (Drop-bearing / non-struct)")),
            }
        }
        // Trust (enum arc, slice 1 — niladic PAYLOAD-enum discriminant FLIP): a by-value PAYLOAD
        // enum param (`enum E { A(i32), B(bool) }`) whose match reads ONLY the discriminant tag (arms
        // bind no payload — `A(_) | B(_)`). The producer takes the general path and spells it
        // `Ty::Enum(eid)`, the sole enum model post-B3-2c. Declare the
        // derived arg with the BUILT enum type (ABI byte-identical — no ABI-gate change) and classify
        // it `"EnumDisc"`: declaration ONLY, never in `env`, so the `ExtractField 0` lowering re-emits
        // built's `_d = Discriminant(_1)` (type-agnostic — `discriminant_ty` handles a niche layout)
        // and the `Inst::Switch` reshape rebuilds built's exhaustive `SwitchInt` (variant-agnostic,
        // `adt.discriminants`). The flip gate's `enum_args_disc_read_only` independently confines EVERY
        // mention of the arg to that bare discriminant read, so a body that reads the PAYLOAD (a
        // `Downcast` — slice 2) fails closed there → no flip. CONCRETE + Drop-free ONLY (a generic /
        // Drop-bearing enum fails the guards below → catch-all, clean-only). Payload reads and enum
        // CONSTRUCTION stay `DerivedUnsupported` (the shim leaves a field>=1 read unbound; `const_of`
        // Ty::Enum is walled) — the intended slice-1 boundary.
        Ty::Enum(_) => match built.kind() {
            ty::Adt(adt, _)
                if adt.is_enum()
                    && !adt.variants().is_empty()
                    && !built.has_non_region_param()
                    && !built.has_non_region_infer()
                    && !crate::cycle_safe_needs_drop(
                        tcx,
                        ty::TypingEnv::fully_monomorphized(),
                        built,
                    ) =>
            {
                Ok((built, Some("EnumDisc")))
            }
            _ => unsup(format!("enum param widening: trust-ir Enum vs built {built:?}")),
        },
        // Trust (wave-UV): the by-VALUE (`FnOnce`) CAPTURING closure env, which the producer signs
        // `Ty::Closure(ClosureTyId)` (`lib.rs closure_env_param_ty`). REFUSED BY NAME. It already
        // fell into the catch-all below, so this arm is a zero-behaviour-change hardening — and
        // that is the point: the wave-UV `UpvarRef` fork's CLEAN-ONLY claim rests on this refusal,
        // and a claim resting on a catch-all is resting on somebody else's absence (the failure
        // mode `aggregate_load_refusal` was written to eliminate). There is no congruent MIR decl
        // type: the built rustc type is `ty::Closure`, whose fields are `repr(Rust)` upvars, while
        // `Ty::Closure`'s captures are a positional register-level list with NO LAYOUT
        // (`trust-ir/src/shape.rs`) — nothing to thread through as a declaration.
        Ty::Closure(_) => unsup("closure-env param: no congruent MIR decl type (by-value env)"),
        _ => unsup(format!("non-scalar param type {p:?}")),
    }
}

/// Reconstruct a `mir::Body` from `module`'s single function (`FuncId(0)`), or fail closed.
///
/// The ABI-boundary types (`_0` + arg locals) come from `sig` — a [`SigSource`]. The
/// differential PROVIDES them (it compares against built by definition, so threading the
/// hook's values is not a compile-path dependence); the flip lane says [`SigSource::Rederive`]
/// and the shim computes them from `tcx` (`fn_sig`/`type_of`/closure sig — the same recipe
/// `build_mir` consumed via THIR), so the compile path is a function of
/// `(tcx, def, Module, callees)` alone and never reads the built body's decls (C1/M1,
/// docs/DESIGN-P1-ir-inversion.md §3). They are threaded into the derived body's opaque
/// non-scalar param decls (slice 3, args only).
///
/// `callees` is the producer's identity ledger (`Lowered::callees`) for THIS body — the only
/// honest `FuncId -> DefId` resolution for `Inst::Call` (module docs, DIRECT CALLS). The
/// differential passes `lowered.callees`; the flip passes the ledger snapshot the registry
/// recorded alongside the green Module.
///
/// The derived body is well-formed for extraction/comparison purposes only (see module docs).
/// Trust (B3-3): flip lanes are DIRECT-only. The shim's enum recognizers
/// (construction reshape, EnumDisc lane, Switch re-emit, emit_enum_variant)
/// all reason about the LOGICAL discriminant; a `Niche` layout descriptor
/// changes what the enum's bytes MEAN (the descriptor is normative), so a
/// niche-described enum must never enter a flip lane — its width-masked
/// compares could manufacture agreement evidence from a descriptor-blind
/// misread. `None` (no descriptor) and `Direct` (a plain tag word carrying
/// the discriminant — the semantics every recognizer already assumes) stay
/// admitted; an unresolvable def fails CLOSED.
fn enum_flip_direct_only(module: &trust_ir::Module, eid: trust_ir::EnumId) -> bool {
    match module.enum_def(eid) {
        None => false,
        Some(def) => match &def.layout {
            // RECORDED FAIL-OPEN, deliberately NOT changed on this branch (it predates it).
            // `layout: None` means NO descriptor was attached, not "the descriptor says Direct" —
            // so a niche-encoded enum whose descriptor merely failed to be recorded is ADMITTED
            // into the flip lane by this arm, which is exactly the read the `Some(desc)` arm below
            // exists to refuse. The absence of a descriptor is being treated as evidence about the
            // encoding, and it is not. Three independent implementers reviewing this branch each
            // named this arm; none touched it, because flipping it to `false` changes flip
            // admission for every descriptor-less enum in the corpus and that delta has not been
            // measured. Fix it as its own change, with its own census.
            None => true,
            Some(desc) => {
                matches!(desc.encoding, trust_ir::ty::EnumTagEncoding::Direct { .. })
            }
        },
    }
}

/// Trust (C1/M1): where the shim's ABI-boundary types come from.
pub enum SigSource<'tcx> {
    /// Caller-supplied `(arg_tys, _0 ty)`. Used by the DIFFERENTIAL, which compares derived
    /// against built by definition — at the `mir_built` hook these values are byte-identical
    /// to the THIR/typeck types the builder itself consumed, so this is provenance-honest.
    Provided(Vec<RustcTy<'tcx>>, RustcTy<'tcx>),
    /// Re-derive from `tcx` (`rederive_abi_sig`). Used by the FLIP, so the compile path never
    /// reads built MIR. The flip's ABI gate then compares the re-derivation against built —
    /// two independent derivations, which is what makes that gate evidence instead of the
    /// tautology it was when `d` was constructed from `n`.
    Rederive,
}

/// Trust (C1/M1): compute the ABI-boundary rustc types from `tcx` alone — the same recipe
/// `build_mir` consumed via THIR (typeck's liberated signature), re-derived at consume time.
/// Regions are ERASED (the flip's product exists only at runtime phases, where the validator
/// already requires no free regions) and associated types normalized under the body's
/// post-analysis typing env. Fail-closed outside the fragment: a body this cannot type simply
/// does not flip — the ABI gate downstream re-checks every answer against built, so a wrong
/// derivation can never produce a wrong body, only a rejected flip.
fn rederive_abi_sig<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
) -> Result<(Vec<RustcTy<'tcx>>, RustcTy<'tcx>), Unsupported> {
    use rustc_hir::def::DefKind;
    let typing_env = ty::TypingEnv::post_analysis(tcx, def);
    match tcx.def_kind(def) {
        DefKind::Fn { .. } | DefKind::AssocFn { .. } => {
            // Trust: 1.99 — `instantiate_identity` returns `Unnormalized<T>`; unwrap, then let
            // `normalize_erasing_late_bound_regions` (plain-`Binder` contract in this tree)
            // do the normalization + erasure.
            let sig = tcx.fn_sig(def).instantiate_identity().skip_normalization();
            if sig.skip_binder().has_non_region_param() {
                return Err(Unsupported { reason: "abi rederive: generic fn signature".into() });
            }
            let sig = tcx.normalize_erasing_late_bound_regions(typing_env, sig);
            Ok((sig.inputs().to_vec(), sig.output()))
        }
        DefKind::Const { .. }
        | DefKind::AssocConst { .. }
        | DefKind::Static { .. }
        | DefKind::AnonConst { .. }
        | DefKind::InlineConst { .. } => {
            let ty = tcx.type_of(def).instantiate_identity().skip_normalization();
            if ty.has_non_region_param() {
                return Err(Unsupported { reason: "abi rederive: generic const type".into() });
            }
            // `try_` + `unwrap_or`: a normalization that cannot make progress leaves the raw
            // type, and the flip's ABI gate downstream rejects the mismatch — fail closed,
            // never a panic on this lane.
            let ty = tcx
                .try_normalize_erasing_regions(typing_env, ty::Unnormalized::new_wip(ty))
                .unwrap_or(ty);
            Ok((Vec::new(), ty))
        }
        DefKind::Closure { .. } => {
            let closure_ty = tcx.type_of(def).instantiate_identity().skip_normalization();
            if closure_ty.has_non_region_param() {
                return Err(Unsupported { reason: "abi rederive: generic closure".into() });
            }
            let ty::Closure(_, args) = closure_ty.kind() else {
                // Coroutine-closures also carry DefKind::Closure; their env/arg convention is
                // out of this fragment.
                return Err(Unsupported {
                    reason: "abi rederive: non-plain-closure body (coroutine-closure)".into(),
                });
            };
            let closure_args = args.as_closure();
            let env_ty =
                tcx.closure_env_ty(closure_ty, closure_args.kind(), tcx.lifetimes.re_erased);
            let sig = tcx.normalize_erasing_late_bound_regions(typing_env, closure_args.sig());
            let ty::Tuple(arg_tys) = sig.inputs()[0].kind() else {
                return Err(Unsupported { reason: "abi rederive: untupled closure sig".into() });
            };
            // `env_ty` is constructed here with `re_erased` and no projections — nothing to
            // normalize.
            let mut inputs = vec![env_ty];
            inputs.extend(arg_tys.iter());
            Ok((inputs, sig.output()))
        }
        other => Err(Unsupported {
            reason: format!("abi rederive: {other:?} body outside fragment"),
        }),
    }
}

pub fn lower_ir_to_mir<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    module: &Module,
    callees: &[CalleeRef],
    sig_source: SigSource<'tcx>,
) -> Result<Body<'tcx>, Unsupported> {
    // The historical parameter names survive as bindings: every downstream comment about
    // "the built type" (attack A1, ABI anchors) still holds in the Provided lane, and in the
    // Rederive lane the value is the tcx-derived signature type — equally rustc-authoritative,
    // never producer-minted, so the A1 argument (identity must not come from the Module)
    // is preserved by construction.
    let (built_arg_tys, built_ret_ty) = match sig_source {
        SigSource::Provided(arg_tys, ret_ty) => (arg_tys, ret_ty),
        SigSource::Rederive => rederive_abi_sig(tcx, def)?,
    };
    let built_arg_tys = &built_arg_tys[..];
    let func = match module.function_by_id(FuncId::new(0)) {
        Some(f) => f,
        None => return unsup("module has no FuncId(0) function"),
    };
    let sig = match module.func_type(func.ty) {
        Some(s) => s,
        None => return unsup("missing func type"),
    };
    if sig.is_vararg {
        return unsup("vararg signature");
    }
    let span = tcx.def_span(def);
    let source_info = SourceInfo::outermost(span);

    // Count/shape gate for the threading (slice 3): one built decl type per trust-ir param.
    if built_arg_tys.len() != sig.params.len() {
        return unsup(format!(
            "param count mismatch: trust-ir {} vs built {}",
            sig.params.len(),
            built_arg_tys.len()
        ));
    }
    let ret_rty = match sig.returns.as_slice() {
        // The producer's unit-return convention is `returns: []` (matching the MIR-side
        // bridge); the built body declares RETURN_PLACE `()` — mirror it (slice 2 item 1).
        [] => tcx.types.unit,
        [t] => match scalar_rustc_ty(tcx, t) {
            Some(t) => t,
            // Trust (wave-15): a THIN-reference return (`-> &T`/`-> &mut T`/`-> *T`). The producer
            // maps every thin ref to `Ty::Ptr`; thread the BUILT return type exactly as `param_rty`
            // does for a Ptr ARG (`built_ret_ty` IS the faithful spelling). A fat-DST ref never reaches here — the producer fails
            // closed on it (`&str` -> "Return(borrow ptr escapes tail)", `&dyn` -> "Unsize(...)").
            // Floats and any non-ref-ptr `Ty::Ptr` still fail closed. Admitting the return here
            // keeps `&T`/`&mut T`/raw-ptr returns clean (DerivedAgreed); the FLIP gate (flip.rs)
            // then restricts the actual flip to SHARED-ref `_0` only — `&mut`/raw-ptr stay
            // clean-only. Carries the trust-ir type in the fail message so the scorecard's
            // derived_detail discriminates the gap class (e.g. an F32/F64 return).
            None => match t {
                Ty::Ptr => match built_ret_ty.kind() {
                    ty::Ref(..) | ty::RawPtr(..) => built_ret_ty,
                    _ => {
                        return unsup(format!(
                            "return widening: trust-ir Ptr vs built non-ref/ptr {built_ret_ty:?}"
                        ));
                    }
                },
                // Trust (wave-D, Drop-free aggregate constructor-return FLIP): a struct RETURN.
                // Declare `_0` with the BUILT struct type — the ABI anchor and the ONLY sound source
                // of the Adt's DefId + GenericArgs. The trust-ir `Ty::Struct` carries neither, and
                // the differential's `safe_def_path_str` erases args, so the comparator cannot see a
                // wrong-args reconstruction; sourcing identity from `built_ret_ty` forecloses it (the
                // aggregate is built from `ret_rty.kind()` in the Return arm). Concrete-only (a generic
                // `-> Wrapper<T>` fails the param-free guard → clean-only) so `fully_monomorphized()`
                // is param-free-safe, matching the rest of the shim. Trust (wave-X): the gate is
                // `!needs_drop` — NOT `Copy`. `Copy` was over-strict: the load-bearing invariant is
                // "no drop glue" (a Drop-bearing return makes `ElaborateDrops`/`AbortUnwindingCalls` do
                // real work → breaks the Continue-everywhere pass-totality the flip relies on). A NON-
                // `Copy` yet Drop-free struct (e.g. `struct A { x: i32 }` without `#[derive(Copy)]`, or
                // one with a non-`Copy` Drop-free field) has NO drop glue, so returning/moving it keeps
                // every pass total — exactly the wave-F relaxation the PARAM gate already made
                // (`arg_struct_ty_ok`). The one non-`Copy` hazard — a bare whole-struct `Copy` operand
                // is ill-typed → MIR-validation ICE — is closed at the SOURCE: `cx.operand` emits
                // `Move` for a non-`Copy` place (matches built exactly). Drop-bearing / non-struct still
                // fail closed (mirrored by `flip::agg_return_ty_ok`).
                Ty::Struct(_) => {
                    if built_ret_ty.has_non_region_param() || built_ret_ty.has_non_region_infer() {
                        return unsup(
                            "aggregate return type has generic params (concrete-only slice)",
                        );
                    }
                    let te = ty::TypingEnv::fully_monomorphized();
                    match built_ret_ty.kind() {
                        ty::Adt(adt_def, _)
                            if adt_def.is_struct()
                                && !crate::cycle_safe_needs_drop(tcx, te, built_ret_ty) =>
                        {
                            built_ret_ty
                        }
                        _ => {
                            return unsup(
                                "aggregate return type is Drop-bearing / non-Copy / non-struct",
                            );
                        }
                    }
                }
                // Trust (wave-L, scalar-tuple constructor-return FLIP): a TUPLE return
                // `-> (A, B, ...)`. Built emits `_0 = (move _i, move _j, ...)` =
                // `Rvalue::Aggregate(AggregateKind::Tuple, [..])` — structurally identical to the
                // `Ty::Struct` case above except the aggregate kind (no Adt DefId/GenericArgs to
                // pin: `AggregateKind::Tuple` is nullary, so there is no attack-A1 identity surface).
                // Declare `_0` with the BUILT tuple type (the ABI anchor). First slice: every element
                // a fragment scalar (`Bool | Int | Uint`, matching `flip::scalar_ok`) — a scalar tuple
                // is unconditionally `Copy && !needs_drop`, but the checks ride along as
                // defense-in-depth. A tuple with a NON-scalar element (nested aggregate / ptr / float)
                // fails closed here (and independently: its nested `Const{Aggregate}` seed is not
                // skipped by `recognize_agg_return_chain` → fails closed in the main loop). Concrete-
                // only (a generic elem fails the param-free guard → clean-only), mirrored by
                // `flip::agg_return_ty_ok`.
                Ty::Tuple(_) => {
                    if built_ret_ty.has_non_region_param() || built_ret_ty.has_non_region_infer() {
                        return unsup("tuple return type has generic params (concrete-only slice)");
                    }
                    let te = ty::TypingEnv::fully_monomorphized();
                    match built_ret_ty.kind() {
                        ty::Tuple(elems)
                            if !elems.is_empty()
                                && elems.iter().all(|e| {
                                    matches!(e.kind(), ty::Bool | ty::Int(_) | ty::Uint(_))
                                })
                                && crate::cycle_safe_is_copy(tcx, te, built_ret_ty)
                                && !crate::cycle_safe_needs_drop(tcx, te, built_ret_ty) =>
                        {
                            built_ret_ty
                        }
                        // Trust (B3-2c T2 slice 2): the wave-Y/YP tuple-branch enum
                        // return arm is DELETED — no enum is tuple-spelled anymore;
                        // ctor returns ride the Ty::Enum sibling (E3) below.
                        // Trust (wave-str, `&str`-LITERAL-RETURN FLIP): the `-> &str` literal
                        // return declares `_0` with the BUILT `&str` (the ABI anchor + the sound
                        // return type — the Return arm rebuilds `_0 = const "lit"` from the
                        // recognized string global). SHARED `&str` ONLY. Region comes from
                        // `built_ret_ty` (erased), never a manufactured `'static`. (Pre-B2-2 the
                        // producer spelling was `Ty::Tuple([Ptr, I64])` and this arm lived in the
                        // tuple branch; the FatPtr(Str) sibling below is the post-flip home —
                        // this arm remains for any residual tuple-spelled return.)
                        ty::Ref(_, inner, m) if inner.is_str() && m.is_not() => built_ret_ty,
                        _ => {
                            return unsup(
                                "tuple return type is empty / non-scalar element / non-tuple",
                            );
                        }
                    }
                }
                // Trust (B3-2a E3): the producer's fieldless/C-like `-> E` spelling is
                // now first-class `Ty::Enum` — the tuple-branch enum arm above stops
                // firing for the migrated class the moment the producer respells, and
                // without this sibling every ctor-return flip would fall to the
                // non-scalar reject. Same gates as the tuple-branch arm (built enum,
                // non-empty, ≤1 field per variant, concrete, Drop-free); the general
                // construction recognizer (E1) + width-masked emit_enum_variant (E2)
                // rebuild `_0` from the BUILT type exactly as before.
                Ty::Enum(eid)
                    if matches!(built_ret_ty.kind(),
                        ty::Adt(adt, _) if adt.is_enum()
                            && !adt.variants().is_empty()
                            && adt.variants().iter().all(|v| v.fields.len() <= 1))
                        && !built_ret_ty.has_non_region_param()
                        && !built_ret_ty.has_non_region_infer()
                        && !built_ret_ty.needs_drop(tcx, ty::TypingEnv::fully_monomorphized())
                        // Trust (B3-3): DIRECT-only — see enum_flip_direct_only.
                        && enum_flip_direct_only(module, *eid) =>
                {
                    built_ret_ty
                }
                // Trust (B2-2): the producer's `-> &str` spelling is now first-class
                // `Ty::FatPtr(Str)`. Same rule as the former tuple-branch arm: declare
                // `_0` with the BUILT `&str` (ABI anchor; the Return arm rebuilds
                // `_0 = const "lit"` from the recognized string global — anything that
                // fails the construction recognizer stays clean-only).
                Ty::FatPtr(trust_ir::FatPtrKind::Str)
                    if matches!(built_ret_ty.kind(),
                        ty::Ref(_, inner, m) if inner.is_str() && m.is_not()) =>
                {
                    built_ret_ty
                }
                _ => return unsup(format!("non-scalar return type {t:?}")),
            },
        },
        _ => return unsup("multi-value return signature"),
    };
    let mut param_rtys: Vec<RustcTy<'tcx>> = Vec::with_capacity(sig.params.len());
    let mut param_opacity: Vec<Option<&'static str>> = Vec::with_capacity(sig.params.len());
    for (p, &bty) in sig.params.iter().zip(built_arg_tys.iter()) {
        // Trust (B3-3): DIRECT-only for the whole EnumDisc lane — see
        // enum_flip_direct_only (fail-closed on an unresolvable def).
        if let Ty::Enum(eid) = p {
            if !enum_flip_direct_only(module, *eid) {
                return unsup(
                    "enum param with a non-Direct layout descriptor (flip lanes are DIRECT-only)",
                );
            }
        }
        let (rty, opaque) = param_rty(tcx, p, bty)?;
        param_rtys.push(rty);
        param_opacity.push(opaque);
    }

    // Trust (C2-scopes): built BEFORE the walk, because `set_span_from_node` range-checks
    // every stamped index against it — a scope table assembled afterwards could only be
    // checked afterwards, i.e. never on the path that uses it.
    let source_scopes = build_source_scopes(
        tcx,
        tcx.local_def_id_to_hir_id(def),
        span,
        &module.files,
        func.scopes.as_deref(),
    )?;
    let mut cx = ShimCx {
        tcx,
        span,
        source_info,
        files: module.files.clone(),
        scope_count: u32::try_from(source_scopes.len()).unwrap_or(u32::MAX),
        local_decls: IndexVec::new(),
        blocks: IndexVec::new(),
        env: HashMap::new(),
        opaque_params: HashMap::new(),
        fwd_ptr_params: HashMap::new(),
        enum_disc_params: HashMap::new(),
        enum_disc_temps: HashMap::new(),
        block_variant: HashMap::new(),
        block_map: HashMap::new(),
        param_locals: HashMap::new(),
        overflow_checks: tcx.sess.overflow_checks(),
        // Trust (B3-2a): resolve the SAT-perturbation class once per body. An
        // unknown class name fails CLOSED (no perturbation, count stays 0 —
        // the validator's count>0 gate then fails the run loudly rather than
        // letting a typo'd class read as a passing control).
        sat_perturb: tcx
            .sess
            .opts
            .unstable_opts
            .trust_sat_perturb
            .as_deref()
            .and_then(SatPerturb::from_flag),
        sat_perturb_count: 0,
    };

    // Locals: _0 = return place, then one per argument (the `Body::new` ordering invariant).
    cx.local_decls.push(LocalDecl::with_source_info(ret_rty, source_info));
    let mut arg_places: Vec<Place<'tcx>> = Vec::with_capacity(param_rtys.len());
    for rty in &param_rtys {
        let l = cx.local_decls.push(LocalDecl::with_source_info(*rty, source_info));
        arg_places.push(Place::from(l));
    }

    // Blocks: the producer guarantees `blocks[0]` is the entry (lower_fn reorders it first); the
    // shim relies on that so START_BLOCK == the entry. Verify rather than assume.
    if func.blocks.is_empty() {
        return unsup("function has no blocks");
    }
    if func.blocks[0].id != func.entry {
        return unsup("blocks[0] is not the entry block");
    }
    for blk in &func.blocks {
        if cx.block_map.contains_key(&blk.id) {
            return unsup("duplicate block id");
        }
        let mir_bb = cx.new_block();
        cx.block_map.insert(blk.id, mir_bb);
    }

    // Entry params ARE the function arguments: bind them to the arg locals. Non-entry block
    // params get one fresh MIR temp each; predecessors assign it on their edge.
    let entry = &func.blocks[0];
    if entry.params.len() != sig.params.len() {
        return unsup("entry param count != signature param count");
    }
    for (i, (v, pty)) in entry.params.iter().enumerate() {
        if *pty != sig.params[i] {
            return unsup("entry param type != signature param type");
        }
        match param_opacity[i] {
            // Opaque param (slice 3): declaration only — never bound in `env`, so any use
            // fails closed in `operand()` with the class name.
            Some(class) => {
                cx.opaque_params.insert(*v, class);
                // Trust (wave-8a): a `"Ptr"`-class param (a `&T`/`&mut T`/raw-ptr arg) may still
                // be FORWARDED into a call argument — record its arg place for that one path.
                if class == "Ptr" || class == "FatPtr(dyn)" {
                    // Trust (B2-3): a `"FatPtr(dyn)"`-class param forwards exactly like
                    // a thin `"Ptr"` — the derived MIR passes the caller's `&dyn` place
                    // through unchanged (16-byte fat copy, same both sides).
                    cx.fwd_ptr_params.insert(*v, arg_places[i]);
                }
                // Trust (wave-V): an `"EnumDisc"`-class param (a by-value fieldless enum) may be
                // read for its discriminant tag — record its arg place for the `ExtractField 0`
                // lowering. Still OUT of `env`, so a bare (non-discriminant) use fails closed.
                if class == "EnumDisc" {
                    cx.enum_disc_params.insert(*v, arg_places[i]);
                }
            }
            None => {
                cx.env.insert(*v, VOp::Plc(arg_places[i]));
            }
        }
    }
    // Trust (wave-Z, BRANCH-SELECTED fieldless-enum return FLIP): the mk_sel case —
    // `fn f(c) -> E { if c { E::A } else { E::B } }`. Unlike wave-Y's DIRECT `ret <ctor>`, the
    // producer constructs each variant in a BRANCH block and joins them through a block PARAM the
    // return reads (`ret %p`, %p the SOLE param of the return block J), because the enum value is
    // control-flow selected. Built MIR instead assigns `_0 = E::A` / `_0 = E::B` DIRECTLY in each
    // branch and `return`s at the join. So the reshape binds J's param to RETURN_PLACE `_0` (see the
    // block-param loop just below — no scalar temp, which the non-scalar `(i64,i64)` enum-model param
    // would fail closed on) and rewrites each `br J(%feed)` edge into
    // `_0 = Aggregate(Adt{did, variant_k}, [])` (the wave-Y reconstruction, moved onto the edge, in
    // the `Inst::Br` arm). The join's `ret %p` then rides the wave-J self-assign-skip arm (%p → `_0`
    // → a bare `return`). This DETECTION must run BEFORE the block-param loop (which is where the
    // non-scalar param would otherwise fail closed); the chain-node skip set is threaded into
    // `agg_skip` further down. FIRST SLICE: EVERY incoming edge to J must be a `br` carrying a DIRECT
    // enum construction (mk_sel / match-on-bool); a feed through a NESTED join param (mk_sel3's
    // phi-of-phi) is NOT resolved → `enum_join_block` stays unset → the inner join's non-scalar param
    // fails closed (no flip; correct, just not YET flipped). Fail-safe: the comparator re-verifies
    // against `mir_built`; a wrong variant/shape → NO flip, never a miscompile (wave-V/wave-Y
    // backstop).
    let mut enum_join_block: Option<BlockId> = None;
    let mut enum_join_feeds: HashMap<ValueId, i128> = HashMap::new();
    let mut enum_join_skip: Vec<ValueId> = Vec::new();
    if matches!(ret_rty.kind(), ty::Adt(adt, _) if adt.is_enum()) {
        let mut value_def: HashMap<ValueId, &InstrNode> = HashMap::new();
        for blk in &func.blocks {
            for node in &blk.body {
                for r in &node.results {
                    value_def.insert(*r, node);
                }
            }
        }
        // Locate the join J: the SOLE `Return`, returning the SOLE param of a non-entry block.
        let mut ret_count = 0usize;
        let mut join: Option<BlockId> = None;
        for blk in &func.blocks {
            for node in &blk.body {
                if let Inst::Return { values } = &node.inst {
                    ret_count += 1;
                    if let [v] = values.as_slice() {
                        if blk.id != func.entry && blk.params.len() == 1 && blk.params[0].0 == *v {
                            join = Some(blk.id);
                        }
                    }
                }
            }
        }
        if ret_count == 1 {
            if let Some(jid) = join {
                // Every incoming edge to J must be a `br` whose single arg is a direct enum
                // construction. Collect the (feed → disc) map + chain-node skip set; require at least
                // one such edge and REFUSE (fail closed) if ANY `br J(..)` deviates. A condbr/switch
                // edge to J cannot carry the param value; the CondBr/Switch arms already reject a
                // param-bearing target (`param_locals[J]` non-empty once we bind it), so J's param is
                // fed only by these `br` edges.
                let mut feeds: HashMap<ValueId, i128> = HashMap::new();
                let mut chain_skip: Vec<ValueId> = Vec::new();
                let mut edge_ok = true;
                let mut any_edge = false;
                for blk in &func.blocks {
                    for node in &blk.body {
                        if let Inst::Br { target, args } = &node.inst {
                            if *target == jid {
                                any_edge = true;
                                match args.as_slice() {
                                    [feed] => {
                                        // Trust (wave-YP): wave-Z branch-selected returns stay
                                        // FIELDLESS-only — a payload branch feed (`br J(Some(x))`,
                                        // payload `Some(_)`) would need the operand routed onto the
                                        // edge (out of this slice), so match `None` payload and fail
                                        // closed on a payload construction.
                                        if let Some((disc, None, skip)) =
                                            recognize_enum_construction(&value_def, *feed)
                                        {
                                            feeds.insert(*feed, disc);
                                            chain_skip.extend(skip);
                                        } else {
                                            edge_ok = false;
                                        }
                                    }
                                    _ => edge_ok = false,
                                }
                            }
                        }
                    }
                }
                if edge_ok && any_edge {
                    enum_join_block = Some(jid);
                    enum_join_feeds = feeds;
                    enum_join_skip = chain_skip;
                }
            }
        }
    }

    for blk in func.blocks.iter().skip(1) {
        // Trust (wave-Z): the branch-selected enum-return JOIN block. Bind its SOLE param to
        // RETURN_PLACE `_0` (not a fresh scalar temp — the `(i64,i64)` enum-model param is
        // non-scalar). Each predecessor `br J(<ctor>)` edge assigns `_0 = Aggregate(...)` directly
        // (the `Inst::Br` arm), and the join's `ret %p` reads `_0` → the wave-J self-assign-skip arm
        // emits a bare `return`. `param_locals[J] = [_0]` (non-empty) also makes any stray
        // condbr/switch edge to J fail closed in those arms.
        if Some(blk.id) == enum_join_block {
            let rp = Place::from(rustc_middle::mir::RETURN_PLACE);
            cx.env.insert(blk.params[0].0, VOp::Plc(rp));
            cx.param_locals.insert(blk.id, vec![rp]);
            continue;
        }
        let mut places: Vec<Place<'tcx>> = Vec::with_capacity(blk.params.len());
        for (v, pty) in &blk.params {
            let rty = match cx.scalar_ty(pty) {
                Some(t) => t,
                // Type-carrying reason (an F32/F64 merge param is the float-body shape here;
                // floats stay outside the shim's scalar fragment — see the return-type gate).
                None => return unsup(format!("non-scalar block param {pty:?}")),
            };
            let place = cx.temp(rty);
            cx.env.insert(*v, VOp::Plc(place));
            places.push(place);
        }
        cx.param_locals.insert(blk.id, places);
    }

    // ---- P1.2 slice 2: memory-promoted slots (Alloca/Store/Load) pre-pass ----
    // Map each count-less scalar `Alloca` to ONE fresh MIR local of the pointee type, then
    // PROVE the slot pointer never escapes: its `ValueId` may appear only as the `ptr` of a
    // `Load`/`Store`. Note the slot's ValueId is deliberately NOT bound in `cx.env`, so even
    // if a use slipped past the probe, `operand()` would fail closed ("undefined value").
    let mut slot_map: HashMap<ValueId, (Place<'tcx>, Ty)> = HashMap::new();
    {
        for blk in &func.blocks {
            for node in &blk.body {
                if let Inst::Alloca { ty, count, align } = &node.inst {
                    if count.is_some() {
                        return unsup("Alloca with a count (array slot)");
                    }
                    if align.is_some() {
                        return unsup("Alloca with explicit align");
                    }
                    let r = match node.results.as_slice() {
                        &[r] => r,
                        _ => return unsup("Alloca without a single result"),
                    };
                    let rty = match cx.scalar_ty(ty) {
                        Some(t) => t,
                        None => return unsup("Alloca of non-scalar pointee"),
                    };
                    if slot_map.insert(r, (cx.temp(rty), ty.clone())).is_some() {
                        return unsup("duplicate Alloca result id");
                    }
                }
            }
        }
        if !slot_map.is_empty() {
            // Sentinel strictly above every id in use (mirrors mem2reg's probe setup).
            let max_id = func.max_value_id();
            if max_id == u32::MAX {
                return unsup("value id space exhausted (no escape-probe sentinel)");
            }
            let sentinel = ValueId::new(max_id + 1);
            for blk in &func.blocks {
                for node in &blk.body {
                    for (&slot, _) in slot_map.iter() {
                        if alloca_escapes(&node.inst, slot, sentinel) {
                            return unsup("Alloca pointer escapes (non-Load/Store-ptr use)");
                        }
                    }
                }
            }
        }
    }

    // Trust (wave-D, Drop-free aggregate constructor-return FLIP): recognize each struct-returning
    // body's InsertField chain and (in the Return arm) collapse it to a single `Rvalue::Aggregate`.
    // The seed `Const` + `InsertField` result ids are SKIPPED in the main loop (exactly like Alloca):
    // they are never bound in `cx.env`, so any OTHER use of one fails closed in `cx.operand`. Only
    // engaged when the return is a struct (`ret_rty` an Adt struct, gated Drop-free above); every
    // other body leaves both maps empty (zero overhead, byte-identical to the pre-wave-D path).
    let mut agg_skip: std::collections::HashSet<ValueId> = std::collections::HashSet::new();
    let mut agg_chains: HashMap<ValueId, Vec<ValueId>> = HashMap::new();
    // Trust (wave-L): the SAME InsertField-chain recognizer serves tuple returns — the producer
    // emits `const (A,B){0,0}` seed + `insertfield`s + `ret` for a tuple exactly as for a struct
    // (`recognize_agg_return_chain` matches `Constant::Aggregate` type-agnostically). Engage it when
    // the return is a struct OR a NON-empty tuple (the return-type gate above already restricted the
    // tuple to concrete all-scalar; unit `()` is `returns: []` → this arm is not reached).
    if matches!(ret_rty.kind(), ty::Adt(adt, _) if adt.is_struct())
        || matches!(ret_rty.kind(), ty::Tuple(elems) if !elems.is_empty())
    {
        let mut value_def: HashMap<ValueId, &InstrNode> = HashMap::new();
        for blk in &func.blocks {
            for node in &blk.body {
                for r in &node.results {
                    value_def.insert(*r, node);
                }
            }
        }
        for blk in &func.blocks {
            for node in &blk.body {
                if let Inst::Return { values } = &node.inst {
                    if let [v] = values.as_slice() {
                        if let Some((field_vals, skip)) = recognize_agg_return_chain(&value_def, *v)
                        {
                            for s in skip {
                                agg_skip.insert(s);
                            }
                            agg_chains.insert(*v, field_vals);
                        }
                    }
                }
            }
        }
    }

    // Trust (B3-2a/B3-2c enum construction FLIP): recognize each `ret %r` whose
    // value uses the producer's first-class `Ty::Enum` convention. The Return arm
    // rebuilds `_0 = Aggregate(Adt{did, variant_k}, [payload?])` from the recorded
    // discriminant and optional payload. Reuse `agg_skip` for the construction
    // nodes: a skipped id is never bound in `env`, so any other use fails closed.
    // Every non-enum body leaves `enum_ctor` empty.
    let mut enum_ctor: HashMap<ValueId, (i128, Option<ValueId>)> = HashMap::new();
    if matches!(ret_rty.kind(), ty::Adt(adt, _) if adt.is_enum()) {
        let mut value_def: HashMap<ValueId, &InstrNode> = HashMap::new();
        for blk in &func.blocks {
            for node in &blk.body {
                for r in &node.results {
                    value_def.insert(*r, node);
                }
            }
        }
        for blk in &func.blocks {
            for node in &blk.body {
                if let Inst::Return { values } = &node.inst {
                    if let [v] = values.as_slice() {
                        if let Some((disc, payload, skip)) =
                            recognize_enum_construction(&value_def, *v)
                        {
                            for s in skip {
                                agg_skip.insert(s);
                            }
                            enum_ctor.insert(*v, (disc, payload));
                        }
                    }
                }
            }
        }
    }

    // Trust (wave-Z): merge the branch-selected enum-return chain nodes (detected BEFORE the
    // block-param allocation, see `enum_join_skip`) into `agg_skip` — the seed/disc/insertfield
    // nodes of every `br JOIN(<ctor>)` feed are dropped from the main loop exactly like wave-Y's.
    for s in &enum_join_skip {
        agg_skip.insert(*s);
    }

    // Trust (wave-str, `&str`-LITERAL-RETURN FLIP): recognize each `ret %r` whose `%r` builds a
    // `&str` literal via the producer's fat-ptr insertfield chain (`global_addr` + `const i64 len`
    // over a `(ptr,i64)` seed — see `recognize_str_return`). Engage ONLY when `_0` is a shared
    // `&str` (the return-type gate admitted the producer's `Ty::Tuple([Ptr,I64])` model against a
    // BUILT `&str`); the Return arm rebuilds `_0 = const "lit"` from the recorded string global.
    // Reuse `agg_skip` for the chain nodes (a skipped id, never bound in `env`, fails any other use
    // closed in `cx.operand` — in particular the otherwise-unhandled `GlobalAddr`). Every non-`&str`
    // body leaves `str_ret` empty (zero overhead).
    let mut str_ret: HashMap<ValueId, (GlobalId, u64)> = HashMap::new();
    // Trust (wave-GH): `value_def` is now built UNCONDITIONALLY (was inside the `ret_rty is &str`
    // block) so the wave-GH call-arg pass below can walk fat-`&str` chains too. Cheap; empty for a
    // fat-ptr-free body.
    let mut value_def: HashMap<ValueId, &InstrNode> = HashMap::new();
    for blk in &func.blocks {
        for node in &blk.body {
            for r in &node.results {
                value_def.insert(*r, node);
            }
        }
    }
    if matches!(ret_rty.kind(), ty::Ref(_, inner, _) if inner.is_str()) {
        for blk in &func.blocks {
            for node in &blk.body {
                if let Inst::Return { values } = &node.inst {
                    if let [v] = values.as_slice() {
                        if let Some((global, len, skip)) = recognize_str_return(&value_def, *v) {
                            for s in skip {
                                agg_skip.insert(s);
                            }
                            str_ret.insert(*v, (global, len));
                        }
                    }
                }
            }
        }
    }

    // Trust (wave-GH, global_addr hoist — `&str`-literal as a CALL ARG): the arg-position twin of
    // wave-str. The producer models a `&str`-literal call argument (`println!("hi")` →
    // `Arguments::from_str("hi\n")`) as the SAME fat-ptr insertfield chain it uses for a `&str`
    // return (`global_addr` + `const i64 len` over a `(ptr,i64)` seed). Built MIR instead passes a
    // single `const "lit"`. Recognize every fat-`&str` chain whose head feeds a `Call` ARG, record
    // it in `str_operand`, and DROP its chain nodes via `agg_skip` (so the otherwise-unhandled
    // `GlobalAddr`/`InsertField` nodes don't hit the `Inst::Other` fail-closed). The arg-lowering
    // loop then emits `const "lit"` (typed with the callee's DECLARED param type, gated `&str`
    // there) in place of the chain — byte-identical to built. A recognized head used anywhere OTHER
    // than a `&str` call arg still fails closed (its chain is skipped → `cx.operand` sees an
    // undefined value) → clean-only, never a wrong flip. Empty for a fat-ptr-free body (zero overhead).
    let mut str_operand: HashMap<ValueId, (GlobalId, u64)> = HashMap::new();
    for blk in &func.blocks {
        for node in &blk.body {
            if let Inst::Call { args, .. } = &node.inst {
                for a in args {
                    if str_operand.contains_key(a) {
                        continue;
                    }
                    if let Some((global, len, skip)) = recognize_str_return(&value_def, *a) {
                        for s in skip {
                            agg_skip.insert(s);
                        }
                        str_operand.insert(*a, (global, len));
                    }
                }
            }
        }
    }

    // Translate each trust-ir block's instruction list into a chain of MIR blocks (asserts split
    // the chain). The producer guarantees exactly one terminator, last.
    for blk in &func.blocks {
        let mut cur = cx.block_map[&blk.id];
        let nodes: &[InstrNode] = &blk.body;
        // Trust (B3-2c T2 slice 2): the wave-YD deferred-payload arm
        // materialization is DELETED (the defer site is gone).
        let mut i = 0usize;
        while i < nodes.len() {
            let node = &nodes[i];
            // Trust (C2-spans, consumption): every statement/terminator minted while lowering
            // THIS node carries its stamped source location.
            cx.set_span_from_node(node);
            // Trust (wave-D): skip the seed `Const` / `InsertField` nodes of a recognized aggregate
            // constructor-return chain — the Return arm rebuilds them as one `Rvalue::Aggregate`.
            // (Same discipline as Alloca: a skipped id is never bound in `cx.env`, so any OTHER use
            // fails closed in `cx.operand` → the whole body → DerivedUnsupported → no flip.)
            if node.results.iter().any(|r| agg_skip.contains(r)) {
                i += 1;
                continue;
            }
            // Trust (wave-IL R1): the AGGREGATE-load refusal runs HERE — at the top of the node
            // loop, ABOVE `recognize_field_write` and above the `match &node.inst` arms — because
            // "first" is the whole point of the predicate. `recognize_field_write` below consumes
            // an `Inst::Load` triple WITHOUT ever reaching the `Inst::Load` arm, so a refusal
            // sited in that arm is not first: it would sit behind whatever type set that
            // recognizer happens to gate on today. See `aggregate_load_refusal`.
            if let Inst::Load { ty, .. } = &node.inst {
                if let Some(reason) = aggregate_load_refusal(ty) {
                    return unsup(reason);
                }
            }
            // Trust (wave-24, ref-escape FLIP-COHERENCE): collapse the WRITE triple
            // `agg = Load(*P):Struct` → `new = InsertField(agg, k, v)` → `Store(*P, new)` through a
            // `&mut`-param ptr `P` into a single MIR field-projected assign `(*P).k = v` — the exact
            // shape rustc's builder emits for `s.k = v` (place projections `[Deref, Field(k)]`), so
            // the derived body canonicalizes byte-identically to built. SOUND single-use: if `agg`
            // or `new` is used anywhere else, skipping its defining node leaves that use referencing
            // an undefined value → `cx.operand` fails closed → DerivedUnsupported → no flip (rustc's
            // correct built MIR ships). The comparator makes the store's caller-memory effect an
            // explicit DISCRIMINATING observable (see mir_differential `Env::refstore`).
            if let Some((argplace, field, vval)) =
                recognize_field_write(&cx.fwd_ptr_params, nodes, i)
            {
                let v_op = cx.operand(vval)?;
                let field_rty = v_op.ty(&cx.local_decls, tcx);
                let deref = tcx.mk_place_deref(argplace);
                let fplace = tcx.mk_place_field(deref, FieldIdx::from_u32(field), field_rty);
                // Trust (wave-24b): reproduce built's operand-temp + storage markers so the marker
                // channel (`mir_differential::canon_markers`) matches → `markers_exact=true` → the
                // flip fires at `-O` too (not just `-O0`). rustc lowers `s.k = v` by evaluating the
                // RHS into a temp FIRST: `StorageLive(_3); _3 = copy _2; (*_1).k = move _3;
                // StorageDead(_3)` (produces canon markers `mk b0.0:live s0:i32` / `mk b0.2:dead
                // s0:i32`). ONE derived temp with a fully self-contained lifetime — the shim knows
                // exactly when it lives (unlike general marker retirement, to_mir docs / ledger L2).
                // The semantic channel still collapses `_t = copy v; (*P).k = move _t` (L5
                // local-elim) to the same `mem[...]` observable, so `DerivedAgreed` is preserved.
                let tmp = cx.temp(field_rty);
                cx.push_stmt(cur, StatementKind::StorageLive(tmp.local));
                // Trust: rust 1.99 — `Rvalue::Use` carries a `WithRetag` payload (the retag
                // became an operand-level annotation). rustc_mir_build emits `WithRetag::Yes`
                // at every builder assign site (no `::No` anywhere in that crate), so the
                // byte-faithful mirror here is `Yes` — at all `Rvalue::Use` sites in this shim.
                cx.assign(cur, tmp, Rvalue::Use(v_op, WithRetag::Yes));
                cx.assign(cur, fplace, Rvalue::Use(Operand::Move(tmp), WithRetag::Yes));
                cx.push_stmt(cur, StatementKind::StorageDead(tmp.local));
                i += 3;
                continue;
            }
            match &node.inst {
                // ---- checked arithmetic: the Overflow + Assert idiom (one unit) ----
                Inst::Overflow { op, ty, lhs, rhs } => {
                    let (res, of) = match node.results.as_slice() {
                        &[r, o] => (r, o),
                        _ => return unsup("Overflow without (result, overflowed) results"),
                    };
                    // The producer's canonical suffix: Const(false), Const(true),
                    // Select(overflowed ? false : true), Assert(ok). Anything else fails closed.
                    let idiom = (|| -> Option<ValueId> {
                        let n1 = nodes.get(i + 1)?;
                        let n2 = nodes.get(i + 2)?;
                        let n3 = nodes.get(i + 3)?;
                        let n4 = nodes.get(i + 4)?;
                        let fc = match &n1.inst {
                            Inst::Const { ty: Ty::Bool, value: Constant::Bool(false) } => {
                                *n1.results.first()?
                            }
                            _ => return None,
                        };
                        let tc = match &n2.inst {
                            Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) } => {
                                *n2.results.first()?
                            }
                            _ => return None,
                        };
                        let ok = match &n3.inst {
                            Inst::Select { ty: Ty::Bool, cond, then_val, else_val }
                                if *cond == of && *then_val == fc && *else_val == tc =>
                            {
                                *n3.results.first()?
                            }
                            _ => return None,
                        };
                        match &n4.inst {
                            Inst::Assert { cond } if *cond == ok => Some(ok),
                            _ => None,
                        }
                    })();
                    if idiom.is_none() {
                        return unsup("Overflow outside the canonical assert idiom");
                    }
                    if !is_int(ty) {
                        return unsup("Overflow on non-int type");
                    }
                    let rty = cx.scalar_ty(ty).expect("is_int implies scalar");
                    let (checked_op, plain_op) = match op {
                        OverflowOp::AddOverflow => (MirBinOp::AddWithOverflow, MirBinOp::Add),
                        OverflowOp::SubOverflow => (MirBinOp::SubWithOverflow, MirBinOp::Sub),
                        OverflowOp::MulOverflow => (MirBinOp::MulWithOverflow, MirBinOp::Mul),
                    };
                    let l = cx.operand(*lhs)?;
                    let r = cx.operand(*rhs)?;
                    let tup_ty = RustcTy::new_tup(tcx, &[rty, tcx.types.bool]);
                    let tmp = cx.temp(tup_ty);
                    cx.assign(
                        cur,
                        tmp,
                        Rvalue::BinaryOp(checked_op, Box::new((l.to_copy(), r.to_copy()))),
                    );
                    let val_place = tcx.mk_place_field(tmp, FieldIdx::ZERO, rty);
                    let of_place = tcx.mk_place_field(tmp, FieldIdx::from_u32(1), tcx.types.bool);
                    cx.env.insert(res, VOp::Plc(val_place));
                    cx.env.insert(of, VOp::Plc(of_place));
                    // The assert splits the MIR chain, mirroring `Builder::assert`.
                    let succ = cx.new_block();
                    cx.terminate(
                        cur,
                        TerminatorKind::Assert {
                            cond: Operand::Move(of_place),
                            expected: false,
                            msg: Box::new(AssertKind::Overflow(plain_op, l, r)),
                            target: succ,
                            unwind: UnwindAction::Continue,
                        },
                    )?;
                    cur = succ;
                    i += 5;
                }
                // ---- checked shifts: [Cast?]+Const+ICmp+Assert+[Cast?]+BinOp as ONE unit ----
                // (mirrors builder/expr/as_rvalue.rs:473-521; see `shift_idiom` for the wiring
                // equations — any deviation falls through to the fail-closed arms below.)
                Inst::Cast { .. } | Inst::Const { .. }
                    if cx.overflow_checks && shift_idiom(nodes, i).is_some() =>
                {
                    let idm = shift_idiom(nodes, i).expect("guard checked");
                    let l = cx.operand(idm.lhs)?;
                    let r = cx.operand(idm.amt)?;
                    let u_rty = match cx.scalar_ty(&idm.u_ty) {
                        Some(t) => t,
                        None => return unsup("shift range-check type is non-scalar"),
                    };
                    // Built MIR casts the amount to its unsigned twin iff the amount type is
                    // SIGNED (an equal-width IntToInt), else compares the amount directly.
                    let amt_u = if idm.range_cast {
                        let t = cx.temp(u_rty);
                        cx.assign(cur, t, Rvalue::Cast(CastKind::IntToInt, r.to_copy(), u_rty));
                        Operand::Move(t)
                    } else {
                        r.to_copy()
                    };
                    let bits = cx.const_of(&idm.u_ty, &Constant::Int(idm.bits))?;
                    let inbounds = cx.temp(tcx.types.bool);
                    cx.assign(
                        cur,
                        inbounds,
                        Rvalue::BinaryOp(
                            MirBinOp::Lt,
                            Box::new((
                                amt_u,
                                Operand::Constant(Box::new(ConstOperand {
                                    span: cx.span,
                                    user_ty: None,
                                    const_: bits,
                                })),
                            )),
                        ),
                    );
                    // The assert splits the MIR chain, mirroring `Builder::assert`.
                    let succ = cx.new_block();
                    cx.terminate(
                        cur,
                        TerminatorKind::Assert {
                            cond: Operand::Move(inbounds),
                            expected: true,
                            msg: Box::new(AssertKind::Overflow(
                                idm.mir_op,
                                l.to_copy(),
                                r.to_copy(),
                            )),
                            target: succ,
                            unwind: UnwindAction::Continue,
                        },
                    )?;
                    cur = succ;
                    let rty = match cx.scalar_ty(&idm.ty) {
                        Some(t) => t,
                        None => return unsup("shift on non-scalar type"),
                    };
                    let tmp = cx.temp(rty);
                    // The ORIGINAL amount operand, exactly like built MIR (MIR's Shl/Shr accept
                    // a differently-typed amount; the module-side value cast serves trust-ir's
                    // same-type `eval_binop` contract and — value-preserving under the range
                    // assert that just ran — has no MIR counterpart).
                    cx.assign(cur, tmp, Rvalue::BinaryOp(idm.mir_op, Box::new((l, r))));
                    cx.env.insert(idm.result, VOp::Plc(tmp));
                    i += idm.len;
                }
                // ---- checks-OFF shifts: the value-retype Cast + BinOp pair, bare Shl/Shr ----
                Inst::Cast { .. }
                    if !cx.overflow_checks && shift_value_cast_pair(nodes, i).is_some() =>
                {
                    let (lhs, amt, sty, mir_op, result) =
                        shift_value_cast_pair(nodes, i).expect("guard checked");
                    let l = cx.operand(lhs)?;
                    let r = cx.operand(amt)?;
                    let rty = match cx.scalar_ty(&sty) {
                        Some(t) => t,
                        None => return unsup("shift on non-scalar type"),
                    };
                    let tmp = cx.temp(rty);
                    cx.assign(cur, tmp, Rvalue::BinaryOp(mir_op, Box::new((l, r))));
                    cx.env.insert(result, VOp::Plc(tmp));
                    i += 2;
                }
                // ---- general integer / bool → integer cast (MIR `IntToInt`) ----
                // A STANDALONE `x as T` (or `bool as T`) the producer lowered to a single
                // `Inst::Cast{Trunc|ZExt|SExt, <int|bool>, <int>}`. Built MIR lowers every such
                // cast to ONE `Rvalue::Cast(CastKind::IntToInt)` statement — verified via
                // `-Zdump-mir=all` (`_x = move _y as i32 (IntToInt)` for i64→i32, `as u8 (IntToInt)`
                // for bool→u8, equal-width reinterprets alike). The shift idioms above already
                // consumed any cast that is part of a checked/unchecked shift, so only genuine
                // value casts reach here. FAIL-CLOSED on any non-integer cast op: float→float /
                // int→float (`FP*`, `*ToFP`) casts DO now reach here (Trust wave-FL admitted float
                // locals into `scalar_ok`, so a float-bearing body is no longer rejected wholesale
                // before the shim) — they hit the `_ => unsup("Cast op ... outside integer
                // fragment")` arm and fail closed cleanly (NO ICE). Float casts are out of scope for
                // wave-FL (which admits float params/returns/arithmetic/consts only); this defensive
                // arm is now load-bearing, not hypothetical.
                Inst::Cast { op, src_ty, dst_ty, operand } => {
                    let r = match node.results.first() {
                        Some(r) => *r,
                        None => return unsup("Cast without result"),
                    };
                    match op {
                        CastOp::Trunc | CastOp::ZExt | CastOp::SExt => {}
                        // Trust (#164 follow-through): an EQUAL-WIDTH integer reinterpret.
                        //
                        // `1861805e6b` fixed the producer to emit `Bitcast` rather than `Trunc`
                        // at equal width — the trust-ir validator rejects `trunc i32 -> u32`
                        // outright, so those modules were ill-formed. But the shim's admission
                        // list was not widened with it, so from that commit every body carrying a
                        // same-width int cast began failing closed HERE, and the flip it used to
                        // earn silently disappeared. Measured: `pub fn d(x: u64) -> u64 { x >> 1 }`
                        // went from flipping to `DerivedUnsupported "shim: Cast op Bitcast outside
                        // integer fragment"`, taking the flip5 baseline from 4 to 3. A producer
                        // correctness fix outran its consumer; this is the consumer catching up.
                        //
                        // Lowering is IDENTICAL to the other three ops — built MIR spells an
                        // equal-width reinterpret as the same `Rvalue::Cast(CastKind::IntToInt)`
                        // ("equal-width reinterprets alike", per the `-Zdump-mir` note above), so
                        // no new shape reaches the comparator.
                        //
                        // GATED, deliberately, rather than admitting `Bitcast` wholesale: the op
                        // also spells pointer and float bit-reinterprets, which are NOT `IntToInt`
                        // and must keep failing closed. Both sides must be integer-like AND the
                        // same width — exactly the condition under which the producer chooses it
                        // (`int_to_int_cast_op`, lib.rs).
                        CastOp::Bitcast
                            if int_width(src_ty).is_some()
                                && int_width(src_ty) == int_width(dst_ty) => {}
                        _ => return unsup(format!("Cast op {op:?} outside integer fragment")),
                    }
                    let rty = match cx.scalar_ty(dst_ty) {
                        Some(t) => t,
                        None => return unsup("Cast to non-scalar type"),
                    };
                    let o = cx.operand(*operand)?;
                    let tmp = cx.temp(rty);
                    cx.assign(cur, tmp, Rvalue::Cast(CastKind::IntToInt, o, rty));
                    cx.env.insert(r, VOp::Plc(tmp));
                    i += 1;
                }
                // ---- the bool-not idiom: Const(false), Const(true), Select(b ? f : t) ----
                Inst::Const { ty: Ty::Bool, value: Constant::Bool(false) }
                    if bool_not_idiom(nodes, i).is_some() =>
                {
                    let (cond, result) = bool_not_idiom(nodes, i).expect("guard checked");
                    let c = cx.operand(cond)?;
                    let tmp = cx.temp(tcx.types.bool);
                    cx.assign(cur, tmp, Rvalue::UnaryOp(MirUnOp::Not, c));
                    cx.env.insert(result, VOp::Plc(tmp));
                    i += 3;
                }
                // ---- div/rem: the producer's bare-`Assert` div-guard idiom, re-emitted as built
                // MIR's `Eq`-based canonical form (the ONE structural rewrite in the shim; the
                // De Morgan dual is value-preserving — both encode the identical trap conditions,
                // and DerivedAgreed ships THIS faithful body). See `div_idiom`.
                Inst::Const { value: Constant::Int(0), .. } if div_idiom(nodes, i).is_some() => {
                    let idm = div_idiom(nodes, i).expect("guard checked");
                    // Fail-close a div/rem whose RESULT is DEAD (adversarial-review #3): only a
                    // live-result div keeps its value in the comparator's canonical form, pinning
                    // both operands (the divisor is separately pinned by the div-by-zero assert
                    // cond). See `value_used_in`.
                    if !value_used_in(&nodes[i + idm.len..], idm.result) {
                        return unsup("div/rem with a dead (unused) result");
                    }
                    let rty = match cx.scalar_ty(&idm.ty) {
                        Some(t) => t,
                        None => return unsup("div/rem on non-scalar type"),
                    };
                    let dividend = cx.operand(idm.dividend)?;
                    let divisor = cx.operand(idm.divisor)?;
                    // ICE-guard ([[trust-ir-respell-lossy-for-isize-usize]]): the reconstructed
                    // const comparands below are built at `rty`; if a real operand's MIR type
                    // differs (an isize/usize respell this body did not vote), `Eq(op, const)`
                    // would be ill-typed — fail closed rather than emit an invalid derived body.
                    if dividend.ty(&cx.local_decls, tcx) != rty
                        || divisor.ty(&cx.local_decls, tcx) != rty
                    {
                        return unsup("div/rem operand type != reconstructed const type");
                    }
                    let span = cx.span;
                    let c_zero = cx.const_of(&idm.ty, &Constant::Int(0))?;
                    let signed_consts = if idm.signed {
                        let minv =
                            signed_int_min(&idm.ty).expect("signed idiom implies signed int type");
                        Some((
                            cx.const_of(&idm.ty, &Constant::Int(-1))?,
                            cx.const_of(&idm.ty, &Constant::Int(minv))?,
                        ))
                    } else {
                        None
                    };
                    let konst = |c: MirConst<'tcx>| {
                        Operand::Constant(Box::new(ConstOperand { span, user_ty: None, const_: c }))
                    };
                    // div-by-zero guard: `assert(!Eq(divisor, 0), Division/RemainderByZero(dividend))`.
                    let z = cx.temp(tcx.types.bool);
                    cx.assign(
                        cur,
                        z,
                        Rvalue::BinaryOp(
                            MirBinOp::Eq,
                            Box::new((divisor.to_copy(), konst(c_zero))),
                        ),
                    );
                    let succ1 = cx.new_block();
                    let zero_msg = if idm.op == MirBinOp::Div {
                        AssertKind::DivisionByZero(dividend.to_copy())
                    } else {
                        AssertKind::RemainderByZero(dividend.to_copy())
                    };
                    cx.terminate(
                        cur,
                        TerminatorKind::Assert {
                            cond: Operand::Move(z),
                            expected: false,
                            msg: Box::new(zero_msg),
                            target: succ1,
                            unwind: UnwindAction::Continue,
                        },
                    )?;
                    cur = succ1;
                    if let Some((c_neg1, c_min)) = signed_consts {
                        // overflow guard: `assert(!BitAnd(Eq(divisor, -1), Eq(dividend, MIN)),
                        // Overflow(op, dividend, divisor))` — built's EXACT operand order
                        // (`Eq(divisor, -1)` first, then `Eq(dividend, MIN)`).
                        let e1 = cx.temp(tcx.types.bool);
                        cx.assign(
                            cur,
                            e1,
                            Rvalue::BinaryOp(
                                MirBinOp::Eq,
                                Box::new((divisor.to_copy(), konst(c_neg1))),
                            ),
                        );
                        let e2 = cx.temp(tcx.types.bool);
                        cx.assign(
                            cur,
                            e2,
                            Rvalue::BinaryOp(
                                MirBinOp::Eq,
                                Box::new((dividend.to_copy(), konst(c_min))),
                            ),
                        );
                        let ov = cx.temp(tcx.types.bool);
                        cx.assign(
                            cur,
                            ov,
                            Rvalue::BinaryOp(
                                MirBinOp::BitAnd,
                                Box::new((Operand::Move(e1), Operand::Move(e2))),
                            ),
                        );
                        let succ2 = cx.new_block();
                        cx.terminate(
                            cur,
                            TerminatorKind::Assert {
                                cond: Operand::Move(ov),
                                expected: false,
                                msg: Box::new(AssertKind::Overflow(
                                    idm.op,
                                    dividend.to_copy(),
                                    divisor.to_copy(),
                                )),
                                target: succ2,
                                unwind: UnwindAction::Continue,
                            },
                        )?;
                        cur = succ2;
                    }
                    // The div/rem itself (MIR `Div`/`Rem`; signedness is carried by the operand type).
                    let tmp = cx.temp(rty);
                    cx.assign(cur, tmp, Rvalue::BinaryOp(idm.op, Box::new((dividend, divisor))));
                    cx.env.insert(idm.result, VOp::Plc(tmp));
                    i += idm.len;
                }
                // ---- plain constants: folded into operands, no statement ----
                Inst::Const { ty, value } => {
                    let r = match node.results.first() {
                        Some(r) => *r,
                        None => return unsup("Const without result"),
                    };
                    let c = cx.const_of(ty, value)?;
                    cx.env.insert(r, VOp::Konst(c));
                    i += 1;
                }
                // ---- plain (wrapping / bitwise) binary ops ----
                Inst::BinOp { op, ty, lhs, rhs } => {
                    let r = match node.results.first() {
                        Some(r) => *r,
                        None => return unsup("BinOp without result"),
                    };
                    let mir_op = match op {
                        // A plain wrapping +/-/* on ints under overflow checks means the
                        // producer and the built MIR disagree on checkedness — never translate
                        // that silently (the built side carries an assert we would not).
                        BinOp::Add | BinOp::Sub | BinOp::Mul if is_int(ty) => {
                            if cx.overflow_checks {
                                return unsup("wrapping BinOp under overflow checks");
                            }
                            match op {
                                BinOp::Add => MirBinOp::Add,
                                BinOp::Sub => MirBinOp::Sub,
                                _ => MirBinOp::Mul,
                            }
                        }
                        BinOp::And if is_int(ty) || *ty == Ty::Bool => MirBinOp::BitAnd,
                        BinOp::Or if is_int(ty) || *ty == Ty::Bool => MirBinOp::BitOr,
                        BinOp::Xor if is_int(ty) || *ty == Ty::Bool => MirBinOp::BitXor,
                        // Shifts: the built MIR carries an in-bounds assert under overflow
                        // checks that the producer does not model — fail closed there. The
                        // logical/arithmetic flavor must match the type's signedness (the
                        // producer's map_binop is coarser; reject the mismatch).
                        BinOp::Shl if is_int(ty) && !cx.overflow_checks => MirBinOp::Shl,
                        BinOp::LShr if is_unsigned_int(ty) && !cx.overflow_checks => MirBinOp::Shr,
                        BinOp::AShr if is_signed_int(ty) && !cx.overflow_checks => MirBinOp::Shr,
                        // Trust (wave-FL): float arithmetic is TRAP-FREE — NO overflow/div-zero
                        // assert on either side (unlike int Add/Sub/Mul under overflow checks or
                        // int Div/Rem's guard idiom), so emit the BARE op with NO `overflow_checks`
                        // gate and BARE Div/Rem. The producer emits the `F*` family (lib.rs
                        // `emit_arith_binop` maps built Add->FAdd, Div->FDiv, ...); FMin/FMax are
                        // excluded (built lowers them to intrinsic CALLS, not a MIR BinOp) → they
                        // fall through to the catch-all fail-closed.
                        BinOp::FAdd | BinOp::FSub | BinOp::FMul | BinOp::FDiv | BinOp::FRem
                            if is_f32_or_f64(ty) =>
                        {
                            match op {
                                BinOp::FAdd => MirBinOp::Add,
                                BinOp::FSub => MirBinOp::Sub,
                                BinOp::FMul => MirBinOp::Mul,
                                BinOp::FDiv => MirBinOp::Div,
                                _ => MirBinOp::Rem,
                            }
                        }
                        // Div/Rem: built MIR guards these with div-by-zero (+ MIN/-1) assert
                        // chains. The producer emits its own guard sequence (bare `Inst::Assert`s
                        // over `Ne`-comparisons + a `Select` disjunction) whose polarity/shape
                        // does not map 1:1 onto MIR's `Eq`-based asserts — the bare `Assert`
                        // rejects first, and the trailing div `BinOp` fails closed here too.
                        _ => return unsup(format!("BinOp({op:?}) on {ty:?}")),
                    };
                    let rty = match cx.scalar_ty(ty) {
                        Some(t) => t,
                        None => return unsup("BinOp on non-scalar type"),
                    };
                    let l = cx.operand(*lhs)?;
                    let rr = cx.operand(*rhs)?;
                    let tmp = cx.temp(rty);
                    cx.assign(cur, tmp, Rvalue::BinaryOp(mir_op, Box::new((l, rr))));
                    cx.env.insert(r, VOp::Plc(tmp));
                    i += 1;
                }
                // ---- comparisons ----
                Inst::ICmp { op, ty, lhs, rhs } => {
                    let r = match node.results.first() {
                        Some(r) => *r,
                        None => return unsup("ICmp without result"),
                    };
                    // Signedness flavor must agree with the operand type (Eq/Ne are neutral;
                    // U* also covers bool, which the producer compares as unsigned).
                    let mir_op = match op {
                        ICmpOp::Eq => MirBinOp::Eq,
                        ICmpOp::Ne => MirBinOp::Ne,
                        ICmpOp::Slt if is_signed_int(ty) => MirBinOp::Lt,
                        ICmpOp::Sle if is_signed_int(ty) => MirBinOp::Le,
                        ICmpOp::Sgt if is_signed_int(ty) => MirBinOp::Gt,
                        ICmpOp::Sge if is_signed_int(ty) => MirBinOp::Ge,
                        ICmpOp::Ult if is_unsigned_int(ty) || *ty == Ty::Bool => MirBinOp::Lt,
                        ICmpOp::Ule if is_unsigned_int(ty) || *ty == Ty::Bool => MirBinOp::Le,
                        ICmpOp::Ugt if is_unsigned_int(ty) || *ty == Ty::Bool => MirBinOp::Gt,
                        ICmpOp::Uge if is_unsigned_int(ty) || *ty == Ty::Bool => MirBinOp::Ge,
                        _ => return unsup(format!("ICmp({op:?}) flavor/type mismatch on {ty:?}")),
                    };
                    if cx.scalar_ty(ty).is_none() {
                        return unsup("ICmp on non-scalar type");
                    }
                    let l = cx.operand(*lhs)?;
                    let rr = cx.operand(*rhs)?;
                    let tmp = cx.temp(tcx.types.bool);
                    cx.assign(cur, tmp, Rvalue::BinaryOp(mir_op, Box::new((l, rr))));
                    cx.env.insert(r, VOp::Plc(tmp));
                    i += 1;
                }
                // ---- unary ops ----
                Inst::UnOp { op, ty, operand } => {
                    let r = match node.results.first() {
                        Some(r) => *r,
                        None => return unsup("UnOp without result"),
                    };
                    let mir_op = match op {
                        // Integer bitwise not. (The producer lowers BOOL not via the Select
                        // idiom handled above, never via UnOp::Not on Ty::Bool.)
                        UnOp::Not if is_int(ty) => MirUnOp::Not,
                        // Signed negation: under overflow checks the BUILT body precedes this
                        // with an `OverflowNeg` assert the producer deliberately omits
                        // (lib.rs `ExprKind::Unary` docs) — fail closed rather than falsely
                        // agree on a body whose built form traps on MIN.
                        UnOp::Neg if is_signed_int(ty) => {
                            if cx.overflow_checks {
                                return unsup(
                                    "Neg under overflow checks (built emits OverflowNeg assert)",
                                );
                            }
                            MirUnOp::Neg
                        }
                        _ => return unsup(format!("UnOp({op:?}) on {ty:?}")),
                    };
                    let rty = match cx.scalar_ty(ty) {
                        Some(t) => t,
                        None => return unsup("UnOp on non-scalar type"),
                    };
                    let o = cx.operand(*operand)?;
                    let tmp = cx.temp(rty);
                    cx.assign(cur, tmp, Rvalue::UnaryOp(mir_op, o));
                    cx.env.insert(r, VOp::Plc(tmp));
                    i += 1;
                }
                // ---- terminators ----
                Inst::Return { values } => {
                    if i + 1 != nodes.len() {
                        return unsup("Return not last in block");
                    }
                    match (values.as_slice(), sig.returns.len()) {
                        // Trust (wave-J): the returned value was written DIRECTLY into `_0` by a
                        // preceding call whose result flowed straight here (the shim routed that
                        // call's destination to RETURN_PLACE — the struct-call-result-return case,
                        // byte-identical to built's `_0 = f(..) -> bb; bb: return`). `_0` already holds
                        // the value; emit ONLY the terminator below — a `_0 = move _0` self-assign is
                        // redundant, absent from built, and would perturb the comparison. Nothing else
                        // ever binds a value to bare `_0`, so this guard is exact.
                        (&[v], 1)
                            if matches!(
                                cx.env.get(&v),
                                Some(VOp::Plc(p))
                                    if p.local == rustc_middle::mir::RETURN_PLACE
                                        && p.projection.is_empty()
                            ) => {}
                        // Trust (wave-Y/wave-YP, enum CONSTRUCTION FLIP): a recognized enum constructor
                        // — rebuild `_0 = Rvalue::Aggregate(Adt(did, variant_k, args), [payload?])`.
                        // Wave-Y: a fieldless/niladic variant → EMPTY operand list. Wave-YP: a 1-field
                        // variant (`Some(x)`/`Ok(v)`) → the payload operand, resolved from the recorded
                        // payload value id via `cx.operand` (the SAME machinery built uses; the value
                        // node was deliberately left unskipped so the main loop bound it). Recover the
                        // variant index k by matching the produced tag literal against the AUTHORITATIVE
                        // discriminant set (`adt.discriminants`); identity from `ret_rty` (attack A1).
                        // The comparator renders both built (`_0=E::A(v)`) and derived as
                        // `agg(adt:E:k,[op])`, so a wrong k/payload → mismatch → no flip.
                        // `emit_enum_variant` gates the payload operand's type against the variant
                        // field type (wave-P ICE guard) and fails closed on an arity/tag mismatch.
                        (&[v], 1) if enum_ctor.contains_key(&v) => {
                            let (disc, payload_val) = enum_ctor[&v];
                            let payload = match payload_val {
                                Some(pv) => Some(cx.operand(pv)?),
                                None => None,
                            };
                            emit_enum_variant(
                                tcx,
                                &mut cx,
                                cur,
                                Place::from(rustc_middle::mir::RETURN_PLACE),
                                ret_rty,
                                disc,
                                payload,
                            )?;
                        }
                        // Trust (wave-str, `&str`-LITERAL-RETURN FLIP): a recognized `&str` literal
                        // return — rebuild built's single `_0 = const "lit"`. The bytes come from the
                        // recognized string global (`global_str_bytes`), cross-checked against the
                        // producer-claimed length (a mismatch fails closed — AXIS B).
                        // `tcx.allocate_bytes_dedup(bytes, CTFE_ALLOC_SALT)` DEDUPS to the SAME
                        // `AllocId` as the built literal → byte-identical codegen. The const is typed
                        // with `ret_rty` (= `built_ret_ty`, the erased-region `&str`), never a
                        // manufactured `'static`, so it is well-typed by construction (AXIS A).
                        (&[v], 1) if str_ret.contains_key(&v) => {
                            let (global, claimed_len) = str_ret[&v];
                            let bytes = match global_str_bytes(module, global) {
                                Some(b) => b,
                                None => {
                                    return unsup(
                                        "str return: global has no readable byte-array initializer",
                                    );
                                }
                            };
                            if bytes.len() as u64 != claimed_len {
                                return unsup(
                                    "str return: global byte length != producer-claimed length",
                                );
                            }
                            let alloc_id =
                                tcx.allocate_bytes_dedup(bytes.as_slice(), CTFE_ALLOC_SALT);
                            let const_ = MirConst::Val(
                                ConstValue::Slice { alloc_id, meta: bytes.len() as u64 },
                                ret_rty,
                            );
                            cx.assign(
                                cur,
                                Place::from(rustc_middle::mir::RETURN_PLACE),
                                Rvalue::Use(
                                    Operand::Constant(Box::new(ConstOperand {
                                        span: cx.span,
                                        user_ty: None,
                                        const_,
                                    })),
                                    WithRetag::Yes,
                                ),
                            );
                        }
                        // Trust (wave-D, Drop-free aggregate constructor-return FLIP): a recognized
                        // constructor chain — rebuild the single
                        // `_0 = Rvalue::Aggregate(Adt(did, 0, args), [fields])` from the collapsed
                        // InsertField chain. The Adt DefId + GenericArgs come from `ret_rty`
                        // (= `built_ret_ty`), the ONLY sound source (attack A1: `safe_def_path_str`
                        // erases args, so the comparator cannot catch a wrong-args reconstruction —
                        // there must be no alternative source). Each field operand is the chain's
                        // per-index value via `cx.operand`; a non-scalar / undefined field (e.g. a
                        // nested aggregate whose tail was NOT skipped) fails closed there. A guard arm
                        // (not a wrapping `if`) keeps the scalar/ref return arm below byte-identical.
                        (&[v], 1) if agg_chains.contains_key(&v) => {
                            let field_vals = &agg_chains[&v];
                            // Trust (wave-L): the aggregate kind + declared arity for the collapsed
                            // constructor chain. A STRUCT sources DefId + GenericArgs from `ret_rty`
                            // (= `built_ret_ty`, the ONLY sound identity source — attack A1); a TUPLE
                            // carries no identity (`AggregateKind::Tuple` is nullary) so nothing can be
                            // mis-sourced. Arity is the struct variant's field count / the tuple length.
                            let (kind, arity, tuple_elems) = match ret_rty.kind() {
                                ty::Adt(adt_def, args) if adt_def.is_struct() => (
                                    AggregateKind::Adt(
                                        adt_def.did(),
                                        FIRST_VARIANT,
                                        args,
                                        None,
                                        None,
                                    ),
                                    adt_def.non_enum_variant().fields.len(),
                                    None,
                                ),
                                ty::Tuple(elems) => {
                                    (AggregateKind::Tuple, elems.len(), Some(elems))
                                }
                                _ => {
                                    return unsup("aggregate return: _0 is not a struct or tuple");
                                }
                            };
                            // Defense-in-depth: the reconstructed field count must equal the aggregate's
                            // declared arity (a malformed chain → wrong-arity aggregate → validation ICE).
                            if field_vals.len() != arity {
                                return unsup("aggregate return: field count != aggregate arity");
                            }
                            let mut field_ops: Vec<Operand<'tcx>> =
                                Vec::with_capacity(field_vals.len());
                            for fv in field_vals {
                                field_ops.push(cx.operand(*fv)?);
                            }
                            // Trust (wave-L): well-typedness gate for a TUPLE return — every
                            // reconstructed operand's type MUST equal the built tuple element type.
                            // (Historically this guarded the pre-B1 isize/usize width-collapse, where
                            // a cast-sourced element respelled i64/u64 could diverge from the built
                            // element type; v25 B1's first-class spellings make that mix impossible,
                            // but the check stays as the general type-coherence wall.)
                            // `_0` is declared from `built_ret_ty` (ABI-exact), so a divergent operand
                            // yields an ill-typed `Aggregate` → MIR-validation ICE. Fail closed on any
                            // mismatch (per-element-anchored PARAMS always match; casts do not). NB the
                            // wave-D STRUCT path carries the identical latent risk (a cast-sourced
                            // isize field), but it is unreached by the clean wave-D corpus and a
                            // too-strict `f.ty(tcx,args)`-vs-operand check could regress its flips via
                            // normalization; hardening it is a separate follow-up, so this gate is
                            // deliberately tuple-scoped (the only shape wave-L newly admits).
                            if let Some(elems) = tuple_elems {
                                for (op, ety) in field_ops.iter().zip(elems.iter()) {
                                    if op.ty(&cx.local_decls, tcx) != ety {
                                        return unsup(
                                            "tuple return: field operand type != element type (isize/usize respell divergence)",
                                        );
                                    }
                                }
                            } else if let ty::Adt(adt_def, args) = ret_rty.kind() {
                                // Trust (wave-P): the wave-D STRUCT constructor-return path carries
                                // the IDENTICAL isize/usize respell risk the tuple gate guards (the
                                // follow-up the wave-L comment above deferred). A field seed sourced
                                // as fixed-width I64/U64 — e.g. an all-const `usize` field lowered
                                // `const u64 0` — yields an operand typed `u64` for a `usize` field,
                                // an ILL-TYPED `Rvalue::Aggregate`. On the assoc-const / const-fn CTFE
                                // seam `KnownPanicsLint`'s const interpreter rejects it with a
                                // `mir_assign_valid_types` span_bug — a HARD compile abort the flip's
                                // fail-open cannot undo (the Bug diagnostic fires BEFORE catch_unwind).
                                // Gate each field operand's type against the built field type (from
                                // `built_ret_ty`'s Adt `args`, the ABI-exact source); fail closed on
                                // any divergence. Region-erase BOTH sides so a semantically-equal but
                                // lifetime-differing concrete field type is not a FALSE rejection (the
                                // wave-L comment's "regress its flips via normalization" concern);
                                // isize/usize vs i64/u64 stay DISTINCT under normalization, so the real
                                // hazard is still caught. Rejecting here loses only flips that were
                                // producing an ICE-inducing ill-typed body — never a sound flip.
                                // Fallible normalize (this runs OUTSIDE the flip's catch_unwind, in
                                // `lower_ir_to_mir`); `unwrap_or(t)` mirrors the in-tree idiom
                                // (`lib.rs` norm helper) and never panics on a stuck projection.
                                let te = ty::TypingEnv::fully_monomorphized();
                                // Trust (P1 stdlib-harvest unblock): guard param-bearing input —
                                // `fully_monomorphized` normalize of a const-param projection is a
                                // hard `bug!` ICE that `unwrap_or` cannot catch. Fail-closed to the
                                // un-normalized type (a field-type mismatch → no flip), matching the
                                // param-free guard used at every other such site in this crate.
                                let norm = |t: ty::Ty<'tcx>| {
                                    if t.has_non_region_param() || t.has_non_region_infer() {
                                        return t;
                                    }
                                    crate::cycle_safe_normalize(tcx, te, t)
                                };
                                for (op, fdef) in
                                    field_ops.iter().zip(adt_def.non_enum_variant().fields.iter())
                                {
                                    if norm(op.ty(&cx.local_decls, tcx))
                                        != norm(fdef.ty(tcx, args).skip_normalization())
                                    {
                                        return unsup(
                                            "struct return: field operand type != field type (isize/usize respell divergence)",
                                        );
                                    }
                                }
                            }
                            let fields: IndexVec<FieldIdx, Operand<'tcx>> =
                                field_ops.into_iter().collect();
                            cx.assign(
                                cur,
                                Place::from(rustc_middle::mir::RETURN_PLACE),
                                Rvalue::Aggregate(Box::new(kind), fields),
                            );
                        }
                        (&[v], 1) => {
                            // Trust (wave-15): a RETURNED ref param lives in `fwd_ptr_params`, not
                            // `env` — resolve it there (mirror the call-arg forward at the Call arm),
                            // using `Copy` (NOT `Move`): built spells a thin-ref identity return
                            // `_0 = copy _1`, so `Copy` matches built's operand kind and makes a
                            // STRAIGHT-LINE identity forward byte-identical to built. The flip's
                            // actual safety invariant is NOT byte-identity, though — it is the
                            // `DerivedAgreed` canonical/semantic equivalence proved by
                            // `mir_differential` (a `mut`-param-reassignment or multi-arm ref return
                            // can emit semantically-equal but byte-DIFFERENT code, exactly as a
                            // pure-scalar `mut`-arg body already does under the pre-existing flip —
                            // the burn-in's `flip_removed_dead_stores` class covers that benign
                            // divergence). A non-forwardable value still routes through `operand()`,
                            // which fails closed on any out-of-fragment use.
                            match cx.fwd_ptr_params.get(&v).copied() {
                                Some(place) => {
                                    // Trust (wave-29, interior-borrow-return FLIP): the returned
                                    // value is a ref PARAM. Two shapes the producer erases to the
                                    // same bare-ptr `return pv`, distinguished by the BUILT types:
                                    //  * `_1: &S`, `_0: &S` (S==T): a thin-ref IDENTITY return
                                    //    (`fn id(&self)->&S{self}`, wave-15) — forward `_0 = copy _1`.
                                    //  * `_1: &S`, `_0: &T`, S≠T: an interior shared borrow of an
                                    //    offset-0 field (`fn get(&self)->&T{&self.f}`, wave-25) —
                                    //    reconstruct the real `_0 = &((*_1).K)` (the producer erased
                                    //    the field to a bare ptr because addr==base at offset 0).
                                    let ret_pointee = ret_rty.builtin_deref(true);
                                    let arg_pointee =
                                        cx.local_decls[place.local].ty.builtin_deref(true);
                                    match (ret_pointee, arg_pointee) {
                                        (Some(t_ty), Some(s_ty)) if t_ty != s_ty => {
                                            // SHARED-ref base only (matches the comparator's
                                            // `is_shared_ref_param` gate and the flip gate); a
                                            // `&mut self`/raw-ptr getter stays clean-only (NotRun).
                                            if !matches!(
                                                cx.local_decls[place.local].ty.kind(),
                                                ty::Ref(_, _, m) if m.is_not()
                                            ) {
                                                return unsup(
                                                    "interior-borrow return: base is not a shared \
                                                     ref param",
                                                );
                                            }
                                            // Only the flip gate's scalar field types (`flip::scalar_ok`
                                            // = bool/int/uint) are reconstructed; a char/float/
                                            // non-scalar offset-0 field return stays clean-only (fails
                                            // closed here → `NotRun`, exactly wave-25).
                                            if !matches!(
                                                t_ty.kind(),
                                                ty::Bool | ty::Int(_) | ty::Uint(_)
                                            ) {
                                                return unsup(
                                                    "interior-borrow return: non-scalar field type \
                                                     outside flip fragment",
                                                );
                                            }
                                            let rv =
                                                cx.reconstruct_interior_borrow(place, s_ty, t_ty)?;
                                            // Trust (wave-29b): reproduce built's reborrow-temp form
                                            // EXACTLY — built spells the offset-0 field return as
                                            //   StorageLive(_2); _2 = &((*_1).K); _0 = &(*_2); StorageDead(_2)
                                            // (markers on the reborrow temp `_2`). Emitting the SAME
                                            // shape (a temp `t` typed `&FieldTy`, then `_0 = &(*t)`)
                                            // makes the derived body byte-identical to built up to
                                            // local numbering, so (a) the marker channel agrees
                                            // (`markers_exact=true`) → the flip fires at `-O`, not just
                                            // `-O0`, and (b) codegen is byte-identical at EVERY opt
                                            // level, preserving the shipped wave-29 `-O0` object (which
                                            // was already byte-identical to built via the direct form).
                                            // The comparator folds both `t = &((*_1).K)` (NORM) and the
                                            // `_0 = &(*t)` reborrow to the same `iref(a{p},K)` observable
                                            // (unchanged — built rode exactly this reborrow arm since
                                            // wave-29), so `DerivedAgreed` holds.
                                            let tmp = cx.temp(ret_rty);
                                            cx.push_stmt(
                                                cur,
                                                StatementKind::StorageLive(tmp.local),
                                            );
                                            cx.assign(cur, tmp, rv);
                                            let reborrow = Rvalue::Ref(
                                                cx.tcx.lifetimes.re_erased,
                                                BorrowKind::Shared,
                                                cx.tcx.mk_place_deref(tmp),
                                            );
                                            cx.assign(
                                                cur,
                                                Place::from(rustc_middle::mir::RETURN_PLACE),
                                                reborrow,
                                            );
                                            cx.push_stmt(
                                                cur,
                                                StatementKind::StorageDead(tmp.local),
                                            );
                                        }
                                        // S==T identity forward (wave-15) — direct, no temp (built
                                        // spells `_0 = copy _1` with no marker, markers_exact already).
                                        (Some(t_ty), Some(s_ty)) if t_ty == s_ty => {
                                            cx.assign(
                                                cur,
                                                Place::from(rustc_middle::mir::RETURN_PLACE),
                                                Rvalue::Use(Operand::Copy(place), WithRetag::Yes),
                                            );
                                        }
                                        // A ptr param returned from a non-ref return type is an
                                        // unexpected producer shape — fail closed rather than emit a
                                        // possibly ill-typed copy.
                                        _ => {
                                            return unsup(
                                                "returned ptr param with non-ref return type",
                                            );
                                        }
                                    }
                                }
                                None => {
                                    cx.assign(
                                        cur,
                                        Place::from(rustc_middle::mir::RETURN_PLACE),
                                        Rvalue::Use(cx.operand(v)?, WithRetag::Yes),
                                    );
                                }
                            }
                        }
                        // The producer's unit convention: `returns: []` + value-less Return.
                        // Mirror `Builder::push_assign_unit`: `_0 = const ()` then `return`.
                        (&[], 0) => {
                            cx.assign(
                                cur,
                                Place::from(rustc_middle::mir::RETURN_PLACE),
                                Rvalue::Use(
                                    Operand::Constant(Box::new(ConstOperand {
                                        span: cx.span,
                                        user_ty: None,
                                        const_: MirConst::zero_sized(tcx.types.unit),
                                    })),
                                    WithRetag::Yes,
                                ),
                            );
                        }
                        _ => return unsup("Return arity != signature returns"),
                    }
                    cx.terminate(cur, TerminatorKind::Return)?;
                    i += 1;
                }
                Inst::Br { target, args } => {
                    if i + 1 != nodes.len() {
                        return unsup("Br not last in block");
                    }
                    // The entry block's params are the fn ARGUMENTS (no param locals were
                    // allocated for it), so a branch back to entry cannot bind them here.
                    if *target == func.entry {
                        return unsup("Br to entry block");
                    }
                    let target_bb = match cx.block_map.get(target) {
                        Some(bb) => *bb,
                        None => return unsup("Br to unknown block"),
                    };
                    let params = cx.param_locals.get(target).cloned().unwrap_or_default();
                    if params.len() != args.len() {
                        return unsup("Br arg count != target param count");
                    }
                    // Trust (wave-Z): this edge feeds the branch-selected enum-return JOIN. `place`
                    // is RETURN_PLACE `_0` (bound in the block-param loop); rebuild the variant
                    // DIRECTLY into `_0` (the wave-Y reconstruction on the edge) instead of the
                    // generic `Use` — the feed's `(i64,i64)` InsertField chain is skipped (`agg_skip`)
                    // and never bound in `env`, so a generic `cx.operand(arg)` would fail closed. The
                    // pre-pass guarantees every arg into this JOIN is a recognized enum construction.
                    if Some(*target) == enum_join_block {
                        for (place, arg) in params.iter().zip(args.iter()) {
                            let disc = match enum_join_feeds.get(arg) {
                                Some(d) => *d,
                                None => {
                                    return unsup(
                                        "wave-Z: enum-join edge arg not a recognized construction",
                                    );
                                }
                            };
                            // wave-Z is FIELDLESS-only (the branch-feed recognizer required a `None`
                            // payload), so pass no payload operand.
                            emit_enum_variant(tcx, &mut cx, cur, *place, ret_rty, disc, None)?;
                        }
                    } else {
                        for (place, arg) in params.iter().zip(args.iter()) {
                            // Trust (wave-YM): a deferred LEGACY shared-slot payload arg — re-materialize
                            // as the arm-specific `((_e as V).k)` = `Downcast(block_variant[cur])+Field(k)`
                            // (the payload read moved from the entry block into THIS variant arm, exactly
                            // as built reads it). `block_variant[cur]` MUST be present — this `br` leaves
                            // a variant arm; absent → fail closed. Scalar field only; a wrong variant/
                            // field can only MISS the flip (comparator backstop).
                            // Trust (B3-2c T2 slice 2): the wave-YM deferred-payload
                            // re-materialization is DELETED (the defer site is gone;
                            // the map is empty by construction).
                            let o = cx.operand(*arg)?;
                            cx.assign(cur, *place, Rvalue::Use(o, WithRetag::Yes));
                        }
                    }
                    cx.terminate(cur, TerminatorKind::Goto { target: target_bb })?;
                    i += 1;
                }
                Inst::CondBr { cond, then_target, then_args, else_target, else_args } => {
                    if i + 1 != nodes.len() {
                        return unsup("CondBr not last in block");
                    }
                    // The producer's lower_if / lower_logical_op never pass edge args on a
                    // CondBr (join args ride the arm Brs). Edge args would need trampoline
                    // blocks — out of this slice.
                    if !then_args.is_empty() || !else_args.is_empty() {
                        return unsup("CondBr with edge args");
                    }
                    if *then_target == func.entry || *else_target == func.entry {
                        return unsup("CondBr to entry block");
                    }
                    let then_bb = match cx.block_map.get(then_target) {
                        Some(bb) => *bb,
                        None => return unsup("CondBr to unknown then block"),
                    };
                    let else_bb = match cx.block_map.get(else_target) {
                        Some(bb) => *bb,
                        None => return unsup("CondBr to unknown else block"),
                    };
                    // Targets with params but no edge args would be malformed; verify.
                    if !cx.param_locals.get(then_target).map_or(true, |p| p.is_empty())
                        || !cx.param_locals.get(else_target).map_or(true, |p| p.is_empty())
                    {
                        return unsup("CondBr target has block params");
                    }
                    let c = cx.operand(*cond)?;
                    // Same encoding as the MIR builder: SwitchTargets::static_if(0, else, then).
                    cx.terminate(cur, TerminatorKind::if_(c, then_bb, else_bb))?;
                    i += 1;
                }
                // Trust (wave-R): the N-way generalization of `CondBr` — an integer-match
                // `Inst::Switch` becomes `TerminatorKind::SwitchInt { discr, targets }`, the same
                // terminator rustc's match lowering emits. Edge args are refused exactly like CondBr
                // (the producer's integer-match Switch never passes them — join args ride the arm
                // `Br`s). Each case value is encoded as the discriminant type's RAW bits (two's-
                // complement, truncated to the type width) — the identical `u128` encoding rustc's
                // SwitchInt uses — so the derived terminator matches built. Integer discriminants,
                // incl. isize/usize at pointer width (wave-S — the ABI gate re-checks a param discr's
                // exact usize/isize type; a respelled internal-temp discr is codegen-inert since
                // usize/u64 are layout-identical); non-integer → fail closed. An EMPTY case set (the
                // pat_binding degenerate `match k {
                // n => .. }`) lowers to a plain `Goto` (built emits no switch for an irrefutable-only
                // match). Fail-safe: any mismatch → the comparator rejects (no flip) or the burn-in's
                // CRITICAL detector catches it; a wrong routing can never silently ship.
                Inst::Switch { value, default, default_args, cases, .. } => {
                    if i + 1 != nodes.len() {
                        return unsup("Switch not last in block");
                    }
                    if !default_args.is_empty() || cases.iter().any(|c| !c.args.is_empty()) {
                        return unsup("Switch with edge args");
                    }
                    if *default == func.entry || cases.iter().any(|c| c.target == func.entry) {
                        return unsup("Switch to entry block");
                    }
                    let mut default_bb = match cx.block_map.get(default) {
                        Some(bb) => *bb,
                        None => return unsup("Switch to unknown default block"),
                    };
                    if !cx.param_locals.get(default).map_or(true, |p| p.is_empty()) {
                        return unsup("Switch default target has block params");
                    }
                    let discr = cx.operand(*value)?;
                    // Trust (wave-V): is this switch driven by a fieldless-enum discriminant temp
                    // (`_d = Discriminant(_e)`, minted by the `ExtractField 0` lowering)? If so,
                    // remember the enum's `AdtDef` so we can reshape the producer's `N-1 cases +
                    // default` form into built's EXHAUSTIVE `all tags explicit + Unreachable
                    // otherwise` form below. Non-enum switches carry `None` and are untouched.
                    let enum_reshape: Option<ty::AdtDef<'tcx>> = match &discr {
                        Operand::Copy(p) | Operand::Move(p) => {
                            cx.enum_disc_temps.get(p).map(|(_, adt)| *adt)
                        }
                        _ => None,
                    };
                    // The discriminant's integer width, to encode each case value as the type's raw
                    // bits — matching built's SwitchInt. Explicit per-variant match: robust, no width-
                    // helper API dependency. isize/usize resolve to the target pointer width (wave-S);
                    // non-integer fails closed.
                    let width: u64 = match discr.ty(&cx.local_decls, tcx).kind() {
                        ty::Int(ity) => match ity {
                            ty::IntTy::I8 => 8,
                            ty::IntTy::I16 => 16,
                            ty::IntTy::I32 => 32,
                            ty::IntTy::I64 => 64,
                            ty::IntTy::I128 => 128,
                            // Trust (wave-S): admit isize at pointer width. On every supported
                            // target isize IS the fixed-width int of `pointer_size()` (I16/I32/I64),
                            // which the arms above already flip byte-identically; use the real
                            // pointer width (NOT a literal) so the case-value mask below truncates
                            // correctly on 16/32-bit. `map_ty` already fails the producer closed on
                            // exotic widths, so those are unreachable here.
                            ty::IntTy::Isize => tcx.data_layout.pointer_size().bits(),
                        },
                        ty::Uint(uty) => match uty {
                            ty::UintTy::U8 => 8,
                            ty::UintTy::U16 => 16,
                            ty::UintTy::U32 => 32,
                            ty::UintTy::U64 => 64,
                            ty::UintTy::U128 => 128,
                            // Trust (wave-S): admit usize at pointer width (usize IS the fixed-width
                            // uint of `pointer_size()`); see the isize note above.
                            ty::UintTy::Usize => tcx.data_layout.pointer_size().bits(),
                        },
                        _ => return unsup("Switch on non-fixed-width-integer discriminant"),
                    };
                    let mask: u128 = if width >= 128 { u128::MAX } else { (1u128 << width) - 1 };
                    let mut targets: Vec<(u128, BasicBlock)> = Vec::with_capacity(cases.len());
                    for c in cases {
                        let Some(lit) = integer_switch_case_bits(&c.value, width) else {
                            return unsup("Switch case value not an integer constant");
                        };
                        let tbb = match cx.block_map.get(&c.target) {
                            Some(bb) => *bb,
                            None => return unsup("Switch case to unknown block"),
                        };
                        if !cx.param_locals.get(&c.target).map_or(true, |p| p.is_empty()) {
                            return unsup("Switch case target has block params");
                        }
                        targets.push((lit & mask, tbb));
                    }
                    // Trust (wave-V, fieldless-enum discriminant-switch RESHAPE): the producer lowers
                    // an EXHAUSTIVE enum match by popping the LAST variant into the `default` edge
                    // (`lower_enum_match` step 4) — `switch %d [0:.. 1:.. default:..]`. Built MIR
                    // instead lists EVERY tag explicitly and routes the (impossible) `otherwise` to
                    // an `Unreachable` block — `switchInt(_d) -> [0:.. 1:.. 2:.. otherwise:unreach]`.
                    // Reconstruct built's exact form: source the AUTHORITATIVE tag set from
                    // `adt.discriminants(tcx)` (faithful for `#[repr(uN)]`/explicit discriminants —
                    // NOT variant indices), and reshape ONLY when EXACTLY ONE tag is missing (i.e.
                    // the producer folded exactly the last variant into `default`). Any other case
                    // (wildcard `_` arm the type is not exhaustive over → built keeps `otherwise ->
                    // arm`, no unreachable; or >1 missing tag) is left VERBATIM → it will not match
                    // built → no flip (fail-safe: the comparator re-verifies derived ≡ built, so a
                    // wrong reshape can only MISS a flip, never miscompile).
                    if let Some(adt) = enum_reshape {
                        // Trust (enum arc slice 2): record the VARIANT each case/default block is
                        // entered under (disc -> VariantIdx), so a payload read inside the block can
                        // Downcast to the right variant. Case blocks are recorded here (before the
                        // SAT switch-perturb swap below, so the map reflects the TRUE routing); the
                        // single folded variant is recorded against the producer's `default` arm
                        // (default_bb) inside `missing.len() == 1`, BEFORE the reshape reassigns it.
                        let disc_to_vidx: std::collections::HashMap<u128, rustc_abi::VariantIdx> =
                            adt.discriminants(tcx)
                                .map(|(vidx, disc)| (disc.val & mask, vidx))
                                .collect();
                        for (dv, tbb) in &targets {
                            if let Some(&vidx) = disc_to_vidx.get(dv) {
                                cx.block_variant.insert(*tbb, vidx);
                            }
                        }
                        let present: std::collections::HashSet<u128> =
                            targets.iter().map(|(v, _)| *v).collect();
                        let mut missing: Vec<u128> = Vec::new();
                        for (_vidx, disc) in adt.discriminants(tcx) {
                            let dv = disc.val & mask;
                            if !present.contains(&dv) {
                                missing.push(dv);
                            }
                        }
                        if missing.len() == 1 {
                            let m = missing[0];
                            if let Some(&vidx) = disc_to_vidx.get(&m) {
                                cx.block_variant.insert(default_bb, vidx);
                            }
                            let unreach = cx.new_block();
                            cx.terminate(unreach, TerminatorKind::Unreachable)?;
                            if cx.sat_perturb == Some(SatPerturb::EnumReshape) {
                                // SAT control: route the folded (genuinely-reachable)
                                // variant to UNREACHABLE and keep `otherwise` live —
                                // the wave-V semantics inverted. The comparator MUST
                                // reject the derived body.
                                cx.sat_perturb_count += 1;
                                targets.push((m, unreach));
                            } else {
                                // Correct: the one folded (genuinely-reachable) variant routes to the
                                // producer's `default` arm; the impossible `otherwise` is unreachable.
                                targets.push((m, default_bb));
                                default_bb = unreach;
                            }
                            if cx.sat_perturb == Some(SatPerturb::EnumCaseValue) {
                                // SAT control (task #107 H2): re-value the folded case PAST
                                // the discriminant domain (max+1) — the folded-arm-is-
                                // Unreachable blind spot. Applied before the sort; the value
                                // survives it (it is strictly larger than every real case).
                                cx.sat_perturb_count += 1;
                                let max = targets.iter().map(|(v, _)| *v).max().unwrap_or(0);
                                if let Some(last) = targets.last_mut() {
                                    last.0 = max.wrapping_add(1) & mask;
                                }
                            }
                        }
                        if cx.sat_perturb == Some(SatPerturb::EnumDiscIndex) {
                            // SAT control: substitute VARIANT INDEXES for effective
                            // discriminants in the case values — the index-vs-disc
                            // seam (the oracle's live model-bug class). Inert on
                            // default-repr enums (index == disc), so the smoke must
                            // carry explicit discriminants to make this non-vacuous.
                            let mut applied = false;
                            for (dv, _) in targets.iter_mut() {
                                if let Some(&vidx) = disc_to_vidx.get(dv) {
                                    let idx = vidx.as_u32() as u128;
                                    if idx != *dv {
                                        *dv = idx & mask;
                                        applied = true;
                                    }
                                }
                            }
                            if applied {
                                cx.sat_perturb_count += 1;
                            }
                        }
                        // Trust (wave-YM): emit the SwitchInt cases in ASCENDING discriminant order.
                        // rustc (built) canonicalizes enum-match cases by value, but the producer emits
                        // them in ARM order. When arm order != value order (e.g. `match o { Some(x) =>
                        // .., None => .. }` — Some=disc 1 BEFORE None=disc 0), the canonical block layout
                        // diverges and the flip is missed; sorting aligns them. A no-op when the arms are
                        // already value-ordered (fieldless/general enums whose arms follow variant order,
                        // e.g. wave-V `dir_match`, slices-1-2 `e_read`). Enum-reshape ONLY — an integer
                        // `Inst::Switch` (wave-R) is untouched (this is inside the `enum_reshape` block).
                        targets.sort_by(|a, b| a.0.cmp(&b.0));
                        if cx.sat_perturb == Some(SatPerturb::SwitchMap) && targets.len() >= 2 {
                            // SAT control: corrupt the value->target MAPPING **after**
                            // the wave-YM sort (a pre-sort reorder would be undone by
                            // the sort — the manufactured-green trap): rotate the
                            // target blocks one position while keeping the sorted
                            // case values in place.
                            cx.sat_perturb_count += 1;
                            let first_bb = targets[0].1;
                            for i in 0..targets.len() - 1 {
                                targets[i].1 = targets[i + 1].1;
                            }
                            let last = targets.len() - 1;
                            targets[last].1 = first_bb;
                        }
                    }
                    if targets.is_empty() {
                        // An irrefutable-only match (`match k { n => .. }`) — built emits no switch.
                        cx.terminate(cur, TerminatorKind::Goto { target: default_bb })?;
                    } else {
                        let switch_targets =
                            rustc_middle::mir::SwitchTargets::new(targets.into_iter(), default_bb);
                        cx.terminate(
                            cur,
                            TerminatorKind::SwitchInt { discr, targets: switch_targets },
                        )?;
                    }
                    i += 1;
                }
                Inst::Unreachable => {
                    if i + 1 != nodes.len() {
                        return unsup("Unreachable not last in block");
                    }
                    cx.terminate(cur, TerminatorKind::Unreachable)?;
                    i += 1;
                }
                // ---- memory-promoted slots (validated by the pre-pass) ----
                Inst::Alloca { .. } => {
                    // Already mapped to a MIR local; the Alloca itself emits no statement
                    // (the local IS the storage — built MIR has no counterpart either).
                    if node.results.first().map_or(true, |r| !slot_map.contains_key(r)) {
                        return unsup("Alloca not registered by the pre-pass");
                    }
                    i += 1;
                }
                Inst::Store { ty, ptr, value, volatile, align } => {
                    if *volatile {
                        return unsup("volatile Store");
                    }
                    if align.is_some() {
                        return unsup("Store with explicit align");
                    }
                    let (place, sty) = match slot_map.get(ptr) {
                        Some((p, t)) => (*p, t.clone()),
                        // Trust: wave-5 — a REF-TYPED PARAM's pointer (`fn f(r: &mut i32) {
                        // *r = v }`) is a Store through an opaque `Ty::Ptr` param: the pointee
                        // slot is the CALLER's, so there is no Alloca→local mapping to erase it
                        // into. Ref-param bodies are NOT flip candidates yet — precise reason,
                        // distinct from a genuinely unknown pointer.
                        None if cx.opaque_params.contains_key(ptr) => {
                            return unsup(
                                "Store through a ref-typed param pointer (caller-owned slot; \
                                 ref-param bodies are not flip candidates)",
                            );
                        }
                        None => return unsup("Store to a non-Alloca pointer"),
                    };
                    if *ty != sty {
                        return unsup("Store type != slot pointee type");
                    }
                    let o = cx.operand(*value)?;
                    cx.assign(cur, place, Rvalue::Use(o, WithRetag::Yes));
                    i += 1;
                }
                Inst::Load { ty, ptr, volatile, align } => {
                    // Trust (wave-IL R1): the AGGREGATE refusal already ran, at the TOP of this
                    // node loop — above `recognize_field_write`, which consumes `Inst::Load`
                    // triples without ever reaching this arm. Re-stating it here would be dead.
                    if *volatile {
                        return unsup("volatile Load");
                    }
                    if align.is_some() {
                        return unsup("Load with explicit align");
                    }
                    let r = match node.results.first() {
                        Some(r) => *r,
                        None => return unsup("Load without result"),
                    };
                    let (place, sty) = match slot_map.get(ptr) {
                        Some((p, t)) => (*p, t.clone()),
                        // Trust (wave-S): `*r` reading a SHARED-ref scalar param — load through
                        // `(*_p)` of the real MIR arg. `fwd_ptr_params ⊆ opaque_params` (a "Ptr"-class
                        // param is registered in both), so this MUST precede the opaque reject. Gate to
                        // a SHARED ref (`m.is_not()` — the `&mut`/raw/WRITE side stays closed at the
                        // Store arm) whose pointee is a SCALAR equal to the loaded type (a fat
                        // `&str`/`&[T]`/`&dyn` pointee fails `scalar_ty` → unsup). The load VALUE is
                        // return-observable only; a shared referent can't be mutated through `_p` and
                        // every write path fails closed, so this is a pure value fold — no caller-memory
                        // observable is needed (unlike the wave-24 WRITE side).
                        None if cx.fwd_ptr_params.contains_key(ptr) => {
                            let argp = cx.fwd_ptr_params.get(ptr).copied().unwrap();
                            let pointee = match cx.local_decls[argp.local].ty.kind() {
                                ty::Ref(_, pointee, m) if m.is_not() => *pointee,
                                _ => {
                                    return unsup(
                                        "Load through a non-shared-ref param (write side / &mut / \
                                         raw ptr)",
                                    );
                                }
                            };
                            match cx.scalar_ty(ty) {
                                Some(srt) if srt == pointee => {}
                                _ => {
                                    return unsup(
                                        "Load through ref param: non-scalar or mismatched pointee",
                                    );
                                }
                            }
                            (cx.tcx.mk_place_deref(argp), ty.clone())
                        }
                        // Trust: wave-5 — a NON-forwardable opaque `Ty::Ptr` param load (caller-owned
                        // slot; no local to map). See the Store arm; those bodies are not flip
                        // candidates.
                        None if cx.opaque_params.contains_key(ptr) => {
                            return unsup(
                                "Load through a ref-typed param pointer (caller-owned slot; \
                                 ref-param bodies are not flip candidates)",
                            );
                        }
                        None => return unsup("Load from a non-Alloca pointer"),
                    };
                    if *ty != sty {
                        return unsup("Load type != slot pointee type");
                    }
                    // A fresh temp per load: an SSA load VALUE is the slot's value AT LOAD
                    // TIME; binding the slot local directly would wrongly observe later
                    // stores through earlier load results.
                    let rty = cx.scalar_ty(ty).expect("slot pointee proven scalar");
                    let tmp = cx.temp(rty);
                    cx.assign(cur, tmp, Rvalue::Use(Operand::Copy(place), WithRetag::Yes));
                    cx.env.insert(r, VOp::Plc(tmp));
                    i += 1;
                }
                // ---- direct calls (wave 6; module docs, DIRECT CALLS) ----
                Inst::Call { callee, args } => {
                    let res = match node.results.as_slice() {
                        [] => None,
                        &[r] => Some(r),
                        _ => return unsup("Call with more than one result"),
                    };
                    // CALLEE IDENTITY: the ledger is the ONLY honest FuncId -> DefId map (the
                    // per-body FuncId is DefIndex-derived). Zero or multiple entries for one
                    // FuncId fail closed — the crate assembler's exact ambiguity rule
                    // (`crate_module::resolve_callee`).
                    let idents: Vec<&CalleeRef> =
                        callees.iter().filter(|c| c.func_id == *callee).collect();
                    let cref = match idents.as_slice() {
                        [c] => *c,
                        [] => return unsup("Call(unledgered callee FuncId)"),
                        _ => return unsup("Call(ambiguous callee FuncId: index collision)"),
                    };
                    let def_id = cref.def_id;
                    // Ledger-invariant tripwires (admit_callee's construction), never assumed.
                    if def_id.index.as_u32() != cref.def_index
                        || def_id.index.as_u32() != callee.index()
                        || def_id.is_local() != cref.is_local
                    {
                        return unsup("Call(ledger identity tripwire)");
                    }
                    // Trust (wave-C): the SITE identity built MIR spells (`FnDef(site_def_id,
                    // site_args)`). For a free fn / inherent method `site_def_id == def_id` (resolved);
                    // for a TRAIT method / overloaded-operator desugar it is the TRAIT method (the site
                    // spelling — resolution to the impl happens at mono, not in MIR). Rebuild the
                    // concrete site args; a callee whose args were not in the encodable concrete
                    // fragment (`None`) fails closed here — clean-only, exactly the pre-wave-C
                    // generic-callee reject.
                    // Trust (B2-3 slice 2): a FORCED-HAVOC callee (generic wave-20 or dyn
                    // dispatch) must NEVER derive a direct call — for a Virtual callee the
                    // built MIR does vtable dispatch, and a derived `FnDef(site_def_id, …)`
                    // direct call would devirtualize to a body runtime dispatch may not
                    // select (a miscompile). Today `force_havoc ⇒ site_args == None`, so the
                    // match below already rejects; this explicit gate makes the invariant
                    // structural rather than a coupling (same reason string — the
                    // flip-frontier classifier buckets stay byte-stable).
                    if cref.force_havoc {
                        return unsup("Call(callee site args not encodable / not concrete-mono)");
                    }
                    let site_def_id = cref.site_def_id;
                    let enc = match &cref.site_args {
                        Some(e) => e,
                        None => {
                            return unsup(
                                "Call(callee site args not encodable / not concrete-mono)",
                            );
                        }
                    };
                    let site_args = rebuild_site_args(tcx, enc);
                    // Arity tripwire (defends `fn_sig(...).instantiate` against an ICE): the encoder
                    // preserved every arg 1:1, so a `Some` encoding always matches the callee's generic
                    // count — a mismatch is a ledger bug, fail closed.
                    if site_args.len() != tcx.generics_of(site_def_id).count() {
                        return unsup("Call(site args arity tripwire)");
                    }
                    // SITE def-kind gate (wave-C): a free fn, an inherent-impl method, OR a TRAIT
                    // method / operator desugar (the site spells the trait fn; codegen resolves to the
                    // impl at mono). The `DefKind::Trait` parent arm is the wave-C widening.
                    match tcx.def_kind(site_def_id) {
                        DefKind::Fn => {}
                        DefKind::AssocFn => match tcx.def_kind(tcx.parent(site_def_id)) {
                            DefKind::Impl { of_trait: false } => {}
                            DefKind::Trait => {}
                            _ => {
                                return unsup("Call(assoc-fn parent outside inherent-impl/trait)");
                            }
                        },
                        _ => return unsup("Call(callee def-kind outside Fn/AssocFn)"),
                    }
                    // Trust (wave-intr): an intrinsic callee is admitted IFF it is on the
                    // span-INSENSITIVE, value-only allowlist below. At `Built` phase rustc spells an
                    // intrinsic call as a plain `Call` to `FnDef(intrinsic, args)` (verified
                    // `-Zdump-mir=built`; only `write_via_move`/`write_box_via_move` are lowered
                    // earlier, into assignments — neither is on this list). The shim's reconstructed
                    // byte-congruent `Call` (`Operand::function_handle`, below) is then lowered by
                    // `LowerIntrinsics` + codegen IDENTICALLY to built — those passes read only
                    // `func`/`args`/`destination`/`sym::name`, never the (fn-level) span. The
                    // comparator pins the interned `FnDef` (DefId + generic args) via
                    // `raw_call_channel` and the operand types via arg-fidelity, and return-fidelity
                    // keeps the result scalar — so an admitted intrinsic can only flip at
                    // `DerivedAgreed`. EXCLUDED (fail closed): `caller_location` (codegen reads the
                    // CALL span → wrong `Location`, a real miscompile), CTFE-alloc
                    // (`const_allocate`/…), `is_val_statically_known`, `transmute` (layout-sensitive,
                    // deferred to a later slice), and `assume` (no type argument, deferred until it
                    // has a dedicated differential fixture). Every admitted name carries a type arg
                    // pinned by the call channel. `#[track_caller]` FNs are covered below.
                    let intrinsic_flip_ok = |d: Option<ty::IntrinsicDef>| -> bool {
                        match d {
                            None => true,
                            Some(i) => matches!(
                                i.name,
                                sym::size_of
                                    | sym::align_of
                                    | sym::ctpop
                                    | sym::ctlz
                                    | sym::cttz
                                    | sym::ctlz_nonzero
                                    | sym::cttz_nonzero
                                    | sym::bswap
                                    | sym::bitreverse
                                    | sym::rotate_left
                                    | sym::rotate_right
                                    | sym::wrapping_add
                                    | sym::wrapping_sub
                                    | sym::wrapping_mul
                                    | sym::saturating_add
                                    | sym::saturating_sub
                                    | sym::unchecked_add
                                    | sym::unchecked_sub
                                    | sym::unchecked_mul
                                    | sym::unchecked_div
                                    | sym::unchecked_rem
                                    | sym::unchecked_shl
                                    | sym::unchecked_shr
                            ),
                        }
                    };
                    if !(intrinsic_flip_ok(tcx.intrinsic(site_def_id))
                        && intrinsic_flip_ok(tcx.intrinsic(def_id)))
                    {
                        return unsup("Call(intrinsic callee outside flip allowlist)");
                    }
                    if tcx
                        .codegen_fn_attrs(site_def_id)
                        .flags
                        .contains(CodegenFnAttrFlags::TRACK_CALLER)
                        || tcx
                            .codegen_fn_attrs(def_id)
                            .flags
                            .contains(CodegenFnAttrFlags::TRACK_CALLER)
                    {
                        return unsup("Call(track_caller callee: caller-Location fidelity)");
                    }
                    // `instantiate_bound_regions_with_erased`, not `skip_binder`: a callee param
                    // like `&i32` carries a LATE-bound lifetime, which `skip_binder` leaves as an
                    // escaping `ReBound` that region erasure can't touch — so an arg-type check
                    // against a forwarded (already-erased) ref would spuriously diverge on the
                    // region. Erasing the binder's regions up front yields `&'{erased} i32`, the
                    // exact codegen-visible shape. (Arity/ABI/variadic/return checks below are
                    // region-insensitive, so this is strictly a fidelity improvement for them too.)
                    // Trust (wave-C): instantiate at the SITE args (the concrete sig for a generic
                    // callee — `fn(&i32)->i32` for `Tr::tm` at Self=i32); for a zero-generic callee
                    // `site_args == []` so this equals `instantiate_identity()` (wave-6 byte-identical).
                    let sig = tcx.instantiate_bound_regions_with_erased(
                        // Trust: 1.99 — instantiate returns Unnormalized<T>; unwrap.
                        tcx.fn_sig(site_def_id).instantiate(tcx, site_args).skip_normalization(),
                    );
                    // Trust (wave-J): NORMALIZE the instantiated callee sig. A trait-method callee —
                    // most commonly an overloaded operator (`a + b` desugars to `<V2 as Add>::add`) —
                    // declares its return (and sometimes an input) as an ASSOCIATED-TYPE PROJECTION
                    // (`<Self as Add>::Output` = `Alias(Projection, ..)`). The fragment checks below
                    // (`ir_scalar_of_body`, the struct arm, the arg exact-type match) cannot classify a
                    // projection, so they spuriously reported "outside the fragment" on a return that
                    // concretely resolves to `V2`. At a CONCRETE call site (`site_args` param-free) the
                    // projection normalizes to its concrete definition — the SAME type built MIR carries
                    // (rustc normalizes in MIR) — so the reconstructed call becomes MORE byte-identical,
                    // never less: normalization is a semantics-preserving equivalence, so it can only
                    // turn a spurious mismatch into a true match, never a wrong type into a false one.
                    // Guarded param-free (matches wave-D/F): a still-generic sig (a generic-caller
                    // forward) is left untouched — `fully_monomorphized()` is param-free-only — so it
                    // fails closed downstream exactly as before; `.unwrap_or(sig)` also tolerates a
                    // normalization that cannot make progress.
                    let sig = if sig.has_non_region_param()
                        || sig.has_non_region_infer()
                        || sig.has_non_region_placeholders()
                        || sig.has_opaque_types()
                        || sig.has_escaping_bound_vars()
                    {
                        sig
                    } else {
                        tcx.try_normalize_erasing_regions(
                            ty::TypingEnv::fully_monomorphized(),
                            ty::Unnormalized::new_wip(sig),
                        )
                        .unwrap_or(sig)
                    };
                    if sig.c_variadic() {
                        return unsup("Call(variadic callee)");
                    }
                    if sig.abi() != rustc_abi::ExternAbi::Rust {
                        // Foreign-ABI call edges carry their own unwind/abort semantics
                        // (`AbortUnwindingCalls`) — outside this slice's proof.
                        return unsup("Call(non-Rust-ABI callee)");
                    }
                    if sig.inputs().len() != args.len() {
                        return unsup("Call(arity != callee signature)");
                    }
                    // RETURN fidelity: unit, or a fixed-width scalar whose trust-ir spelling
                    // round-trips through THIS function's denotation — so an active
                    // pointer-width respell can never leave the call result ill-typed
                    // against the ops that consume it (module docs, DIRECT CALLS).
                    let ret_rty_callee = sig.output();
                    // Trust: result arity follows the same canonical unit convention as function
                    // signatures and `Inst::Return`: `()` has zero IR results, every admitted
                    // non-unit return has exactly one. Reject either crossed shape before building
                    // MIR; it is malformed producer IR, never a representational exception.
                    match (ret_rty_callee.is_unit(), res) {
                        (true, None) | (false, Some(_)) => {}
                        (true, Some(_)) => {
                            return unsup("unit Call unexpectedly declares a result");
                        }
                        (false, None) => return unsup("non-unit Call has no result"),
                    }
                    if !ret_rty_callee.is_unit() {
                        // Trust (wave-E): probe through the BODY'S respell (`ir_scalar_of_body`), not
                        // the global `ir_scalar_of` — so a callee returning `isize`/`usize` is admitted
                        // in a pointer-width-anchored body (denoted `I64`/`U64`, the same spelling the
                        // dest temp's later consumers use). The round-trip guard below is then
                        // guaranteed by construction, but kept as defense-in-depth.
                        match cx.ir_scalar_of_body(ret_rty_callee) {
                            Some(ir_ret) => {
                                if cx.scalar_ty(&ir_ret) != Some(ret_rty_callee) {
                                    return unsup(
                                        "Call(callee return conflicts with the pointer-width respell)",
                                    );
                                }
                            }
                            // Trust (wave-J): a by-value Copy + Drop-free STRUCT callee return (the
                            // common overloaded-operator shape `a + b` -> `<V2 as Add>::add` -> `V2`,
                            // and any trait-method call whose `Output` NORMALIZES (above) to a concrete
                            // Copy struct). The dest temp below is typed with the REAL rustc struct type,
                            // sourced from the ABI-pinned, normalized callee sig — so the reconstructed
                            // `dest: V2 = add(a, b)` is byte-identical to what built MIR emits for the
                            // desugared operator call (identity re-verified by `raw_call_channel`).
                            // Copy + `!needs_drop` keeps `ElaborateDrops` a no-op (the Continue-everywhere
                            // pass-totality the flip relies on), mirroring wave-D's body-`_0` return gate
                            // EXACTLY. The returned struct value is fully observable in the canonical form
                            // (`dest = call(..); <use of dest>`) — no hidden caller-memory effect (unlike
                            // a `&mut` field write), so no new comparator observable is needed; downstream
                            // uses of the result are each independently gated (a whole-struct arg by the
                            // exact-type match, a scalar field read by the wave-F `ExtractField` arm, a
                            // struct body-return by wave-D's `_0`). A still-unresolved projection (generic
                            // caller), a non-struct, a Drop-bearing or non-Copy struct all fail closed.
                            None => {
                                let te = ty::TypingEnv::fully_monomorphized();
                                let admit = !ret_rty_callee.has_non_region_param()
                                    && !ret_rty_callee.has_non_region_infer()
                                    && matches!(
                                        ret_rty_callee.kind(),
                                        ty::Adt(adt, _) if adt.is_struct()
                                    )
                                    && crate::cycle_safe_is_copy(tcx, te, ret_rty_callee)
                                    && !crate::cycle_safe_needs_drop(tcx, te, ret_rty_callee);
                                if !admit {
                                    return unsup(format!(
                                        "Call(callee return outside the fragment: \
                                         {ret_rty_callee:?})"
                                    ));
                                }
                            }
                        }
                    }
                    // ARG fidelity: each lowered operand's rustc type must EXACTLY equal the
                    // callee's declared input type (covers respell drift and the producer's
                    // isize/usize collapse alike — fail closed, never a layout argument).
                    let mut mir_args: Vec<Spanned<Operand<'tcx>>> = Vec::with_capacity(args.len());
                    for (a, &want) in args.iter().zip(sig.inputs().iter()) {
                        // Trust (wave-8a): a forwarded opaque `"Ptr"` param (`g(r)`, `s.method()`
                        // receiver) — pass its arg place directly. Built spells this
                        // `_x = &(*_p); call(move _x)`; forwarding `_p` with `move` is congruent
                        // under the differential's `ref-alias`/`move-as-copy` normalizations, and
                        // `move` is valid for both `&T` (Copy — reads it) and `&mut T`. Its
                        // declared type IS the built ref type (`param_rty` threaded it), so the
                        // exact type check below still proves fidelity; a respell can't touch a
                        // ref. Any NON-forward use of a `Ptr` param already failed in `operand()`.
                        let op = match cx.fwd_ptr_params.get(a).copied() {
                            Some(place) => {
                                // Trust (wave-30, interior-borrow-as-ARG FLIP): a forwarded ptr param
                                // whose type != the callee's declared param type is the interior-borrow
                                // arg case `g(&self.field)` — got=`&S`, want=`&FieldTy` (the producer
                                // erased the offset-0 interior borrow to the base ptr). Reconstruct the
                                // real `_tmp = &((*place).K)` (REUSE wave-29, `want`'s pointee as T),
                                // typed `want`, and move it in. A non-reconstructable mismatch falls
                                // through with the raw forward → the exact type check below fails closed
                                // (clean-only preserved). A matching type (`g(self)`/`g(r)`) forwards
                                // unchanged (wave-8a).
                                let got = cx.local_decls[place.local].ty;
                                if tcx.erase_and_anonymize_regions(got)
                                    != tcx.erase_and_anonymize_regions(want)
                                {
                                    match cx.try_reconstruct_interior_arg(place, got, want) {
                                        Some(rv) => {
                                            let tmp = cx.temp(want);
                                            cx.assign(cur, tmp, rv);
                                            Operand::Move(tmp)
                                        }
                                        None => Operand::Move(place),
                                    }
                                } else {
                                    Operand::Move(place)
                                }
                            }
                            None => match str_operand.get(a) {
                                // Trust (wave-GH): a recognized fat-`&str` chain head as a call arg.
                                // Emit `const "lit"` typed with the callee's DECLARED param type
                                // `want` (gated `&str`) — byte-identical to built's `const "lit"`
                                // argument. Reuses wave-str's `global_str_bytes` +
                                // `allocate_bytes_dedup(_, CTFE_ALLOC_SALT)` (DEDUPS to the SAME
                                // AllocId as the built literal → byte-identical codegen). The
                                // length is cross-checked against the producer-claimed length.
                                Some(&(global, claimed_len)) if matches!(want.kind(), ty::Ref(_, inner, _) if inner.is_str()) =>
                                {
                                    let bytes = match global_str_bytes(module, global) {
                                        Some(b) => b,
                                        None => {
                                            return unsup(
                                                "str arg: global has no readable byte-array initializer",
                                            );
                                        }
                                    };
                                    if bytes.len() as u64 != claimed_len {
                                        return unsup(
                                            "str arg: global byte length != producer-claimed length",
                                        );
                                    }
                                    let alloc_id =
                                        tcx.allocate_bytes_dedup(bytes.as_slice(), CTFE_ALLOC_SALT);
                                    let const_ = MirConst::Val(
                                        ConstValue::Slice { alloc_id, meta: bytes.len() as u64 },
                                        want,
                                    );
                                    Operand::Constant(Box::new(ConstOperand {
                                        span: cx.span,
                                        user_ty: None,
                                        const_,
                                    }))
                                }
                                // A recognized head whose chain was skipped but which the callee
                                // does NOT want as `&str` → fail closed (the head is unbound in
                                // `env`, so `cx.operand` would fail regardless; be explicit).
                                Some(_) => {
                                    return unsup(
                                        "str arg: recognized &str chain but callee param is not &str",
                                    );
                                }
                                None => cx.operand(*a)?,
                            },
                        };
                        // Trust (wave-GH2, operand-spelling PARITY): built spells a ONE-SHOT
                        // rvalue call-result temp handed to the next call as a MOVE
                        // (`_1 = _print(move _2)` — rustc_mir_build as_operand mints the temp and
                        // moves it), while `cx.operand` spells every Copy-typed place `Copy`. The
                        // comparator folds Move≡Copy (LEDGER L8), which is codegen-invisible for
                        // Immediate/Pair operands — but a MEMORY-ABI struct arg (`Arguments`, 48B)
                        // is passed INDIRECTLY, and codegen_ssa gives a `Copy` arg a defensive
                        // fresh-alloca+memcpy while `Move` passes the temp's own address
                        // (rustc_codegen_ssa/src/mir/block.rs, adversarial finding wave-GH2). So
                        // re-spell as `Move` exactly where built does: a STRUCT-typed bare temp
                        // that (a) is a shim-minted PRIOR-call result, (b) is used NOWHERE else
                        // in the function (this arg is its single consuming node, appearing once
                        // in this call's args), AND (c) whose defining call sits EARLIER IN THIS
                        // SAME BLOCK. (c) is the builder's rvalue-temp discipline and is the
                        // DYNAMIC-single-use guarantee: each execution of the block re-defines the
                        // value before this single use consumes it. A CROSS-BLOCK def (a value
                        // created before a loop, consumed inside it — tests/ui/mir/
                        // issue-76740-copy-propagation.rs) has ONE lexical use but MANY dynamic
                        // uses; `move` there hands the callee ownership of the caller's slot,
                        // which a by-value `mut self` callee mutates IN PLACE → the next iteration
                        // reads the mutated value (use-after-move miscompile; source legality does
                        // NOT shield Copy types the way borrowck shields non-Copy moves). Such an
                        // operand stays `Copy`, and the flip gate's memory-ABI parity check then
                        // fail-closes the body (clean-only). Multi-use values keep `Copy` (built
                        // reads a user variable → copy). Scalars keep the shipped `Copy` spelling
                        // (congruent AND codegen-identical).
                        let op = match &op {
                            Operand::Copy(p)
                                if p.projection.is_empty()
                                    && matches!(
                                        p.ty(&cx.local_decls, tcx).ty.kind(),
                                        ty::Adt(adt, _) if adt.is_struct()
                                    )
                                    && matches!(
                                        value_def.get(a).map(|n| &n.inst),
                                        Some(Inst::Call { .. })
                                    )
                                    && blk.body[..i].iter().any(|n| n.results.contains(a))
                                    && args.iter().filter(|&&x| x == *a).count() == 1
                                    && func
                                        .blocks
                                        .iter()
                                        .flat_map(|b| b.body.iter())
                                        .filter(|n| value_used_in(std::slice::from_ref(*n), *a))
                                        .count()
                                        == 1 =>
                            {
                                Operand::Move(*p)
                            }
                            _ => op,
                        };
                        let got = match &op {
                            Operand::Copy(p) | Operand::Move(p) => p.ty(&cx.local_decls, tcx).ty,
                            Operand::Constant(c) => c.const_.ty(),
                            _ => return unsup("Call(arg operand outside fragment)"),
                        };
                        // Both sides are region-ERASED here (MIR is post-borrowck; `sig` had its
                        // late-bound regions erased above, the place type is MIR-erased) — the
                        // extra erase is defensive/idempotent. Referent types and the isize/usize
                        // respell fidelity this check guards are untouched by region erasure.
                        if tcx.erase_and_anonymize_regions(got)
                            != tcx.erase_and_anonymize_regions(want)
                        {
                            return unsup(format!(
                                "Call(arg type {got:?} != callee input {want:?})"
                            ));
                        }
                        mir_args.push(Spanned { node: op, span: cx.span });
                    }
                    // Trust (wave-J): route a DIRECTLY-RETURNED call result STRAIGHT into `_0`
                    // rather than a fresh temp. Built MIR writes a tail-expression call — the common
                    // overloaded-operator body `fn add(a,b) -> V2 { a + b }` — directly into the return
                    // place (`_0 = <V2 as Add>::add(move _1, move _2) -> bb1; bb1: return;`), because
                    // the operator call IS the returned tail expr (no intermediate temp). Mirroring that
                    // makes the derived body BYTE-IDENTICAL — no intermediate struct temp, and no
                    // whole-struct `_0 = move _tmp` (which the flip fragment forbids for a struct). `_0`'s
                    // struct type is then separately gated Copy + `!needs_drop` by BOTH the return-type
                    // check above AND wave-D's `agg_return_ty_ok` in flip's `gate_derived_body`; the bare
                    // `_0` call destination passes `place_ok`.
                    //
                    // GATE (all checked): for a non-unit call, the NEXT TrustIR node is exactly
                    // `Return([res])` (`res` this call's sole result); for a canonical unit call, it is
                    // exactly `Return([])` and the call declares no SSA result. The body return and the
                    // callee's NORMALIZED return must equal `_0`'s built type `ret_rty`, so the direct
                    // write is type-exact. MIR still requires a destination for `()`, hence the unit
                    // case writes the unit-typed `_0` without inventing an IR value. Any non-adjacent,
                    // multi-value, or mismatched shape uses a fresh temp, which remains fail-closed.
                    // The Return arm below emits ONLY the terminator when a non-unit `res` is bound to
                    // bare `_0` (no redundant `_0 = move _0` self-assignment).
                    let route_to_ret = ret_rty_callee == ret_rty
                        && match res {
                            Some(res) => matches!(
                                nodes.get(i + 1).map(|n| &n.inst),
                                Some(Inst::Return { values })
                                    if matches!(values.as_slice(), &[v] if v == res)
                            ),
                            None => matches!(
                                nodes.get(i + 1).map(|n| &n.inst),
                                Some(Inst::Return { values }) if values.is_empty()
                            ),
                        };
                    let dest = if route_to_ret {
                        Place::from(rustc_middle::mir::RETURN_PLACE)
                    } else {
                        cx.temp(ret_rty_callee)
                    };
                    // Trust (wave-C): spell the SITE identity `FnDef(site_def_id, site_args)` — exactly
                    // what built MIR writes. For a zero-generic callee this is `FnDef(def_id, [])` (the
                    // wave-6 spelling, byte-identical). The comparator's `raw_call_channel` re-verifies
                    // this interned `FnDef` against built's pairwise (the soundness anchor).
                    let func = Operand::function_handle(tcx, site_def_id, site_args, cx.span);
                    // The call splits the MIR chain exactly like an assert.
                    let succ = cx.new_block();
                    cx.terminate(
                        cur,
                        TerminatorKind::Call {
                            func,
                            args: mir_args.into_boxed_slice(),
                            destination: dest,
                            target: Some(succ),
                            // The post-`RemoveNoopLandingPads` normal form — the assert arm's
                            // proven convention (module docs, DIRECT CALLS: built spells
                            // `Cleanup(lone-resume)` at `Built`, and the replayed cleanup
                            // pass normalizes it to exactly this).
                            unwind: UnwindAction::Continue,
                            call_source: CallSource::Normal,
                            fn_span: cx.span,
                        },
                    )?;
                    if let Some(res) = res {
                        cx.env.insert(res, VOp::Plc(dest));
                    }
                    cur = succ;
                    i += 1;
                }
                // Trust (wave-F): a scalar FIELD READ of a by-value struct (`s.k`). The producer
                // emits `ExtractField{aggregate, field}` for the read of field `field` of `aggregate`.
                // Admit it ONLY when the aggregate denotes a PLACE (a struct param bound in `env` as
                // `VOp::Plc` — wave-F's `param_rty` arm is the sole producer of such bindings) whose
                // base rustc type is a struct `Adt`, `field` is in bounds, and the field type is a
                // SCALAR (denotable through this body's respell). We fold to a MIR field-projected
                // place `(base.k)` — the exact place rustc's builder emits for `s.k` — sourcing the
                // field TYPE + IDENTITY from the base place's ABI-PINNED Adt type
                // (`variant.fields[k].ty(tcx, args)`), NOT the args-free `ExtractField.ty`, so no
                // cross-instantiation can hide behind the erased trust-ir name. Reading only a scalar
                // field keeps the emitted operand a scalar `Copy((base.k))` (always well-typed), never
                // a bare whole-struct `Copy(base)` (ill-typed for a non-Copy struct → MIR-validation
                // ICE) — the `flip.rs` `struct_args_read_only` guard independently confines every
                // struct-arg mention to exactly this shape. Non-place aggregate / non-Adt base /
                // non-struct / OOB / non-scalar field all fail closed (rustc's built MIR ships).
                Inst::ExtractField { aggregate, field, .. } => {
                    let r = match node.results.as_slice() {
                        &[r] => r,
                        _ => return unsup("ExtractField without a single result"),
                    };
                    // Trust (wave-V, fieldless-enum discriminant-read FLIP): the producer models a
                    // fieldless enum as `(i64, i64)` and reads its TAG via `extractfield 0` on the
                    // enum PARAM (which is `"EnumDisc"`-opaque, so NOT in `env`). Re-emit built's
                    // `_d = Discriminant(place)` for field 0 (`disc_ty = discriminant_ty` — isize
                    // for a repr-less enum, the exact type built uses); field >= 1 is the unused
                    // payload placeholder slot — a fieldless enum NEVER binds it, so leave `r`
                    // UNBOUND (any downstream read fails closed in `operand()`). Register the minted
                    // temp so the `Inst::Switch` lowering can reshape the discriminant switch.
                    if let Some(&place) = cx.enum_disc_params.get(aggregate) {
                        let base_rty = place.ty(&cx.local_decls, tcx).ty;
                        let ty::Adt(adt, args) = base_rty.kind() else {
                            return unsup("EnumDisc param is not an Adt (unreachable)");
                        };
                        if *field == 0 {
                            let disc_ty = base_rty.discriminant_ty(tcx);
                            let tmp = cx.temp(disc_ty);
                            cx.assign(cur, tmp, Rvalue::Discriminant(place));
                            cx.env.insert(r, VOp::Plc(tmp));
                            cx.enum_disc_temps.insert(tmp, (place, *adt));
                        } else {
                            // field >= 1. TWO shapes reach here, distinguished by whether THIS MIR block
                            // (`cur`) is a variant arm whose variant actually has a field at index k:
                            //  (A) a PAYLOAD read `extractfield %e, 1+k` inside a variant's arm block ->
                            //      `((_e as V).k)` = a `Downcast(V)+Field(k)` place. V is the variant the
                            //      block is entered under, recorded by the `Inst::Switch` reshape in
                            //      `block_variant` (disc->VariantIdx). A wrong variant/field can only MISS
                            //      the flip (derived `Downcast` differs from built's -> no `DerivedAgreed`),
                            //      never miscompile.
                            //  (B) the LEGACY fieldless model (`Ty::Tuple([I64,I64])`, ALSO in
                            //      enum_disc_params) reads field 1 as an UNUSED placeholder in the ENTRY
                            //      block (before the switch), where `block_variant` is absent — and any
                            //      genuinely fieldless variant has no field at k. Leave `r` UNBOUND (the
                            //      wave-V no-op; a real downstream use fails closed in `operand()`). This
                            //      preserves EVERY fieldless-enum flip (wave-V/Y/Z/OR).
                            let k = (*field as usize) - 1;
                            let payload = cx
                                .block_variant
                                .get(&cur)
                                .copied()
                                .filter(|v0| k < adt.variant(*v0).fields.len());
                            if let Some(vidx0) = payload {
                                let vidx = vidx0;
                                let variant = adt.variant(vidx);
                                if k >= variant.fields.len() {
                                    return unsup("enum payload field index out of bounds");
                                }
                                let fidx = FieldIdx::from_usize(k);
                                let field_ty =
                                    variant.fields[fidx].ty(tcx, args).skip_normalization();
                                if cx.ir_scalar_of_body(field_ty).is_none() {
                                    return unsup(
                                        "enum payload field non-scalar (outside fragment)",
                                    );
                                }
                                let dc = tcx.mk_place_downcast(place, *adt, vidx);
                                let fplace = tcx.mk_place_field(dc, fidx, field_ty);
                                cx.env.insert(r, VOp::Plc(fplace));
                            }
                            // Trust (B3-2c T2 slice 2): the wave-YM shared-slot DEFER branch is
                            // DELETED (no enum is tuple-spelled; the general model reads payloads
                            // per-arm). An unattributed read leaves `r` UNBOUND (wave-V no-op).
                        }
                        i += 1;
                    } else {
                        let base = match cx.env.get(aggregate) {
                            Some(VOp::Plc(p)) => *p,
                            _ => {
                                return unsup(
                                    "ExtractField aggregate is not a place (outside fragment)",
                                );
                            }
                        };
                        let base_rty = base.ty(&cx.local_decls, tcx).ty;
                        let ty::Adt(adt, args) = base_rty.kind() else {
                            return unsup("ExtractField base is not an Adt (outside fragment)");
                        };
                        if !adt.is_struct() {
                            return unsup("ExtractField base is not a struct (outside fragment)");
                        }
                        let variant = adt.non_enum_variant();
                        let arity = variant.fields.len();
                        let k = *field as usize;
                        if k >= arity {
                            return unsup("ExtractField index out of bounds");
                        }
                        let fidx = FieldIdx::from_usize(k);
                        let field_ty = variant.fields[fidx].ty(tcx, *args).skip_normalization();
                        if cx.ir_scalar_of_body(field_ty).is_none() {
                            return unsup("ExtractField(non-scalar field outside fragment)");
                        }
                        let fplace = tcx.mk_place_field(base, fidx, field_ty);
                        cx.env.insert(r, VOp::Plc(fplace));
                        i += 1;
                    }
                }
                other => return unsup(format!("Inst::{}", inst_name(other))),
            }
        }
        if cx.blocks[cur].terminator.is_none() {
            return unsup("block chain left unterminated");
        }
    }

    // Defensive: every MIR block we allocated must have been terminated (assert-split
    // successors are terminated by the continuation of the same trust-ir block).
    if cx.blocks.iter().any(|b| b.terminator.is_none()) {
        return unsup("derived body has an unterminated block");
    }

    // Trust (B3-2a): the SAT-perturbation application count, on stderr so the
    // burn-in validator can enforce count > 0 per class (a control that never
    // fires is INERT — the silent-inert precedent). Burn-in lanes only (the
    // driver requires `-Ztrust-verify=off -Ztrust-ir-lower`), so a plain eprintln
    // is the honest, grep-stable channel.
    if let Some(class) = cx.sat_perturb {
        eprintln!(
            "trust-sat-perturb: def={def:?} class={class:?} applications={}",
            cx.sat_perturb_count
        );
    }

    // `source_scopes` was built up front (see `build_source_scopes`); a body whose Module
    // carries no tree gets exactly the one outermost scope this used to hard-code.

    // Trust (C2-names, consumption): mint `var_debug_info` from the Module's `value_names`.
    //
    // Scope is deliberately PARAMS ONLY, and that is a soundness choice, not laziness: entry
    // param i is `ValueId(i)` at the producer and `Local(i + 1)` here (the `Body::new` ordering
    // invariant asserted just below — `_0` return place, then one local per arg), so the mapping
    // is exact by construction with nothing to desync. A non-param `ValueId` has no such
    // identity: `cx.env` maps it to a `VOp` that may be a temp, a constant, or a projection, and
    // guessing a local for it would attach a user-visible NAME to the wrong storage — a debugger
    // lying is worse than a debugger silent. Locals land when the ledger carries the binding's
    // own denotation, not before.
    //
    // `argument_index` is 1-based per the field's contract. Names beyond `arg_count` (a producer
    // that starts stamping locals before this consumer learns to place them) are SKIPPED, not
    // approximated.
    let mut var_debug_info: Vec<VarDebugInfo<'tcx>> = Vec::new();
    for (v, name) in func.value_names.iter().flatten() {
        let idx = v.index() as usize;
        if idx >= param_rtys.len() {
            continue;
        }
        let local = Local::from_usize(idx + 1);
        var_debug_info.push(VarDebugInfo {
            name: rustc_span::Symbol::intern(name),
            source_info: cx.local_decls[local].source_info,
            composite: None,
            value: VarDebugInfoContents::Place(Place::from(local)),
            argument_index: u16::try_from(idx + 1).ok(),
        });
    }

    Ok(Body::new(
        MirSource::item(def.to_def_id()),
        cx.blocks,
        source_scopes,
        cx.local_decls,
        IndexVec::new(),
        param_rtys.len(),
        var_debug_info,
        span,
        None,
        None,
    ))
}

/// Recover a Trust-IR integer Switch case as raw fixed-width bits. V24's
/// `U128` spelling is accepted only for the 128-bit discriminator it can
/// faithfully inhabit; every narrower use fails closed before masking.
fn integer_switch_case_bits(value: &Constant, width: u64) -> Option<u128> {
    match value {
        Constant::Int(v) => Some(*v as u128),
        Constant::U128(v) if width == 128 => Some(*v),
        _ => None,
    }
}

/// True iff `cand` (an `Alloca` result) is used inside `inst` as anything OTHER than the
/// `ptr` of a `Load`/`Store` — i.e. the slot pointer escapes through this instruction.
///
/// Non-destructive probe over `trust_ir::mem2reg::rewrite_inst` (the authoritative
/// match-on-every-variant operand walker, the same technique mem2reg's own escape analysis
/// uses): clone the instruction, remap `cand -> sentinel`, then for `Load`/`Store` restore
/// the (legitimately remapped) `ptr` back to `cand`. Any surviving difference means `cand`
/// appeared in a non-`ptr` operand position. A `Store` whose VALUE is the slot pointer
/// stays different (only `ptr` is restored), so store-the-address escapes are caught.
fn alloca_escapes(inst: &Inst, cand: ValueId, sentinel: ValueId) -> bool {
    let mut probe = inst.clone();
    let map: HashMap<ValueId, ValueId> = std::iter::once((cand, sentinel)).collect();
    trust_ir::mem2reg::rewrite_inst(&mut probe, &map);
    match &mut probe {
        Inst::Load { ptr, .. } | Inst::Store { ptr, .. } if *ptr == sentinel => {
            *ptr = cand;
        }
        _ => {}
    }
    &probe != inst
}

/// Match the producer's bool-not idiom at `nodes[i..]`: `Const(false)`, `Const(true)`,
/// `Select { Bool, cond, then_val: false, else_val: true }`. Returns `(cond, select_result)`.
/// NOT matched when the `Select` is the tail of an Overflow assert (that idiom is consumed
/// whole from the `Inst::Overflow` index, so its consts are never re-visited).
fn bool_not_idiom(nodes: &[InstrNode], i: usize) -> Option<(ValueId, ValueId)> {
    let n0 = nodes.get(i)?;
    let n1 = nodes.get(i + 1)?;
    let n2 = nodes.get(i + 2)?;
    let fc = match &n0.inst {
        Inst::Const { ty: Ty::Bool, value: Constant::Bool(false) } => *n0.results.first()?,
        _ => return None,
    };
    let tc = match &n1.inst {
        Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) } => *n1.results.first()?,
        _ => return None,
    };
    match &n2.inst {
        Inst::Select { ty: Ty::Bool, cond, then_val, else_val }
            if *then_val == fc && *else_val == tc =>
        {
            Some((*cond, *n2.results.first()?))
        }
        _ => None,
    }
}

/// Trust (wave-U, div/rem FLIP): the producer's div/rem guard idiom, anchored on the leading
/// `Const 0` of the div-by-zero check and fully wiring-checked to the terminating `Div`/`Rem`.
///
/// The producer emits (UNSIGNED): `Const 0`, `ICmp Ne(divisor, 0)`, `Assert`, `[U]Div/Rem(dividend,
/// divisor)`. SIGNED adds a MIN/-1 overflow guard between the div-by-zero `Assert` and the div:
/// `Const -1`, `Const MIN`, `ICmp Ne(divisor, -1)`, `ICmp Ne(dividend, MIN)`, `Const true`,
/// `Select(divisor != -1 ? true : dividend != MIN)`, `Assert`, `[S]Div/Rem`. That guard is the
/// De Morgan DUAL of built MIR's `Eq`-based asserts — div-by-zero `Eq(divisor, 0)`; overflow
/// `BitAnd(Eq(divisor, -1), Eq(dividend, MIN))` — so the emission arm RE-EMITS built's exact form
/// rather than the producer's (the ONE structural rewrite in the shim, value-preserving: both
/// encode the identical trap conditions, and DerivedAgreed ships the shim's faithful body). Every
/// field is pinned by OPERAND IDENTITY to the terminating `Div`/`Rem` (the divisor checked `!= 0`
/// is the div's divisor; for signed, the MIN/-1 comparands are the div's dividend/divisor); any
/// deviation returns `None` → the bare `Assert` fails closed exactly as before wave-U → no flip.
struct DivIdiom {
    /// MIR `Div` or `Rem` (MIR has no signed/unsigned variant — signedness is the operand type's).
    op: MirBinOp,
    /// Carries the MIN/-1 overflow guard (a signed `SDiv`/`SRem`).
    signed: bool,
    /// The trust-ir operand type (all three of the div-by-zero comparand, the ICmp, and the div
    /// agree on it).
    ty: Ty,
    dividend: ValueId,
    divisor: ValueId,
    /// The `Div`/`Rem` result value.
    result: ValueId,
    /// trust-ir nodes consumed (4 unsigned, 11 signed).
    len: usize,
}

/// Signed MIN of a fixed-width int type as `i128` (128 handled specially — negating `1i128 << 127`
/// overflows `i128`, so the general `-(1 << (w-1))` formula must not reach the 128-bit case).
fn signed_int_min(ty: &Ty) -> Option<i128> {
    let w = int_width(ty)?;
    Some(if w == 128 { i128::MIN } else { -(1i128 << (w - 1)) })
}

/// Trust (wave-U, adversarial-review #3): does any node in `rest` consume value `v` as an operand?
/// Used to fail-close a div/rem whose RESULT is DEAD. A dead div's value expression can be dropped
/// by the comparator's pure-assign elimination (whose soundness assumes a dropped assign is
/// trap-free — the module docs' L5 precondition, historically justified by "Div/Rem excluded"),
/// which would leave an UNSIGNED div's DIVIDEND un-pinned in the canonical form (the divisor stays
/// pinned by the live div-by-zero assert cond, the signed dividend by the overflow assert cond).
/// Flipping only a LIVE-result div keeps the div value in the canonical form, pinning BOTH operands,
/// so the trap-free precondition is never leaned on for a trapping op. `_ => false` is the
/// conservative default: an un-enumerated use reads as DEAD → the div fails closed (over-rejection,
/// never a wrong flip). SSA + block params make a within-block forward scan complete — a use in a
/// later block arrives via THIS block's terminator args, which are nodes in `rest`.
fn value_used_in(rest: &[InstrNode], v: ValueId) -> bool {
    let has = |xs: &[ValueId]| xs.contains(&v);
    rest.iter().any(|n| match &n.inst {
        Inst::BinOp { lhs, rhs, .. }
        | Inst::Overflow { lhs, rhs, .. }
        | Inst::ICmp { lhs, rhs, .. }
        | Inst::FCmp { lhs, rhs, .. } => *lhs == v || *rhs == v,
        Inst::UnOp { operand, .. } | Inst::Cast { operand, .. } | Inst::Copy { operand, .. } => {
            *operand == v
        }
        Inst::Select { cond, then_val, else_val, .. } => {
            *cond == v || *then_val == v || *else_val == v
        }
        Inst::Assert { cond } | Inst::Assume { cond } => *cond == v,
        Inst::Store { ptr, value, .. } => *ptr == v || *value == v,
        Inst::Load { ptr, .. } => *ptr == v,
        Inst::Return { values } => has(values),
        Inst::Br { args, .. } => has(args),
        Inst::CondBr { cond, then_args, else_args, .. } => {
            *cond == v || has(then_args) || has(else_args)
        }
        Inst::Switch { value, default_args, cases, .. } => {
            *value == v || has(default_args) || cases.iter().any(|c| has(&c.args))
        }
        Inst::Call { args, .. } => has(args),
        Inst::CallIndirect { callee, args, .. } => *callee == v || has(args),
        Inst::InsertField { aggregate, value, .. } => *aggregate == v || *value == v,
        Inst::ExtractField { aggregate, .. } => *aggregate == v,
        Inst::InsertElement { array, index, value, .. } => {
            *array == v || *index == v || *value == v
        }
        Inst::ExtractElement { array, index, .. } => *array == v || *index == v,
        _ => false,
    })
}

fn div_idiom(nodes: &[InstrNode], i: usize) -> Option<DivIdiom> {
    // n0: `Const{int, 0}` — the div-by-zero comparand.
    let n0 = nodes.get(i)?;
    let (zty, zero) = match &n0.inst {
        Inst::Const { ty, value: Constant::Int(0) } if is_int(ty) => {
            (ty.clone(), *n0.results.first()?)
        }
        _ => return None,
    };
    // n1: `ICmp Ne(divisor, 0)`.
    let n1 = nodes.get(i + 1)?;
    let divisor = match &n1.inst {
        Inst::ICmp { op: ICmpOp::Ne, ty, lhs, rhs } if *ty == zty && *rhs == zero => *lhs,
        _ => return None,
    };
    let nz = *n1.results.first()?;
    // n2: `Assert(divisor != 0)`.
    match &nodes.get(i + 2)?.inst {
        Inst::Assert { cond } if *cond == nz => {}
        _ => return None,
    }
    // UNSIGNED: n3 = `[U]Div/Rem(dividend, divisor)`. (Signed div/rem ALWAYS carries the overflow
    // guard, so a `UDiv`/`URem` here means the whole idiom is unsigned.)
    let n3 = nodes.get(i + 3)?;
    if let Inst::BinOp { op, ty, lhs, rhs } = &n3.inst {
        let mop = match op {
            BinOp::UDiv => Some(MirBinOp::Div),
            BinOp::URem => Some(MirBinOp::Rem),
            _ => None,
        };
        if let Some(mir_op) = mop {
            // Signedness COHERENCE (adversarial-review hardening): a `UDiv`/`URem` must be on an
            // UNSIGNED type. Detection infers signedness from the opcode, so cross-check it against
            // the type — a `UDiv{ty:i32}` (which built would guard with a MIN/-1 overflow assert we
            // would omit) fails closed here, independent of the producer's op/type coherence.
            if *ty == zty && *rhs == divisor && is_unsigned_int(&zty) {
                return Some(DivIdiom {
                    op: mir_op,
                    signed: false,
                    ty: zty,
                    dividend: *lhs,
                    divisor,
                    result: *n3.results.first()?,
                    len: 4,
                });
            }
            // A `UDiv`/`URem` whose divisor is not the value just checked `!= 0`, or on a
            // non-unsigned type: not our idiom.
            return None;
        }
    }
    // SIGNED overflow guard — the operand type MUST be signed (coherence with the SDiv/SRem opcode;
    // a signed guard chain on an unsigned type is rejected, so the guard SET always matches built).
    if !is_signed_int(&zty) {
        return None;
    }
    // n3 `Const -1`, n4 `Const MIN`, n5 `ICmp Ne(divisor, -1)`,
    // n6 `ICmp Ne(dividend, MIN)`, n7 `Const true`, n8 `Select`, n9 `Assert`, n10 `[S]Div/Rem`.
    let neg1 = match &n3.inst {
        Inst::Const { ty, value: Constant::Int(-1) } if *ty == zty => *n3.results.first()?,
        _ => return None,
    };
    let minv = signed_int_min(&zty)?;
    let n4 = nodes.get(i + 4)?;
    let minc = match &n4.inst {
        Inst::Const { ty, value: Constant::Int(v) } if *ty == zty && *v == minv => {
            *n4.results.first()?
        }
        _ => return None,
    };
    let n5 = nodes.get(i + 5)?;
    let ne_div_neg1 = match &n5.inst {
        Inst::ICmp { op: ICmpOp::Ne, ty, lhs, rhs }
            if *ty == zty && *lhs == divisor && *rhs == neg1 =>
        {
            *n5.results.first()?
        }
        _ => return None,
    };
    let n6 = nodes.get(i + 6)?;
    let (dividend, ne_dvd_min) = match &n6.inst {
        Inst::ICmp { op: ICmpOp::Ne, ty, lhs, rhs } if *ty == zty && *rhs == minc => {
            (*lhs, *n6.results.first()?)
        }
        _ => return None,
    };
    let n7 = nodes.get(i + 7)?;
    let truev = match &n7.inst {
        Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) } => *n7.results.first()?,
        _ => return None,
    };
    // `Select(divisor != -1 ? true : dividend != MIN)` == `(divisor != -1) || (dividend != MIN)`.
    let n8 = nodes.get(i + 8)?;
    let sel = match &n8.inst {
        Inst::Select { ty: Ty::Bool, cond, then_val, else_val }
            if *cond == ne_div_neg1 && *then_val == truev && *else_val == ne_dvd_min =>
        {
            *n8.results.first()?
        }
        _ => return None,
    };
    match &nodes.get(i + 9)?.inst {
        Inst::Assert { cond } if *cond == sel => {}
        _ => return None,
    }
    let n10 = nodes.get(i + 10)?;
    let (mir_op, result) = match &n10.inst {
        Inst::BinOp { op: BinOp::SDiv, ty, lhs, rhs }
            if *ty == zty && *lhs == dividend && *rhs == divisor =>
        {
            (MirBinOp::Div, *n10.results.first()?)
        }
        Inst::BinOp { op: BinOp::SRem, ty, lhs, rhs }
            if *ty == zty && *lhs == dividend && *rhs == divisor =>
        {
            (MirBinOp::Rem, *n10.results.first()?)
        }
        _ => return None,
    };
    Some(DivIdiom { op: mir_op, signed: true, ty: zty, dividend, divisor, result, len: 11 })
}

/// The producer's CHECKED-SHIFT idiom, parsed and fully wiring-checked (see `shift_idiom`).
struct ShiftIdiom {
    /// Nodes consumed (4-6: optional range cast + Const + ICmp + Assert + optional value cast
    /// + BinOp).
    len: usize,
    /// The shifted value.
    lhs: ValueId,
    /// The ORIGINAL amount value (its own integer type — what built MIR's cast/assert/shift use).
    amt: ValueId,
    /// The shifted/result type.
    ty: Ty,
    /// The range-comparison type (the amount's unsigned same-width twin).
    u_ty: Ty,
    /// The asserted bound — validated `== int_width(ty)`.
    bits: i128,
    /// Whether the module carries the leading signed-amount `Trunc` (built MIR then carries the
    /// matching `IntToInt` cast statement).
    range_cast: bool,
    /// `Shl` or `Shr` (flavor validated against `ty`'s signedness).
    mir_op: MirBinOp,
    /// The shift's result `ValueId`.
    result: ValueId,
}

/// Match the producer's CHECKED-SHIFT idiom at `nodes[i..]` (`emit_arith_binop`'s `<<`/`>>`
/// arm under overflow checks):
///
/// ```text
/// [Cast{Trunc, amt_ty(signed), u_ty(unsigned twin), amt}]   (iff the amount type is signed)
/// Const{u_ty, Int(LHS_BITS)}
/// ICmp{Ult, u_ty, amount_u, bits}
/// Assert{inbounds}
/// [Cast{Trunc|SExt|ZExt, amt_ty, ty, amt}]                  (iff the amount needs the retype)
/// BinOp{Shl|LShr|AShr, ty, lhs, amount_v}
/// ```
///
/// Every wiring equation is CHECKED, not assumed: the compared value must be the lead cast's
/// result (signed) or the raw amount (unsigned), the asserted bound must equal the shifted
/// type's width, the shift's amount operand must be the correctly-`ty`-typed amount form, and
/// the `LShr`/`AShr` flavor must match `ty`'s signedness. Any deviation → `None` (the caller
/// falls through to the fail-closed arms).
fn shift_idiom(nodes: &[InstrNode], i: usize) -> Option<ShiftIdiom> {
    let mut k = i;
    // Optional leading range cast: the signed amount reinterpreted as its unsigned twin.
    let lead: Option<(ValueId, Ty, ValueId, Ty)> = match &nodes.get(k)?.inst {
        // Trust (#164 follow-through): `Bitcast`, NOT `Trunc`. This arm is guarded on
        // `int_width(src) == int_width(dst)`, and since 1861805e6b the producer spells an
        // equal-width reinterpret `Bitcast` — `trunc i32 -> u32` is REJECTED by the trust-ir
        // validator. So the old `Trunc` spelling here could only ever match a module that is
        // ill-formed by the format's own rules: a dead arm, and its deadness is what silently
        // withdrew the flip for every guarded shift (measured on
        // `pub fn d(x: u64) -> u64 { x >> 1 }`). Matching only the well-formed spelling keeps
        // the arm honest rather than accepting both and pretending the invalid one is legal.
        Inst::Cast { op: CastOp::Bitcast, src_ty, dst_ty, operand }
            if is_signed_int(src_ty)
                && is_unsigned_int(dst_ty)
                && int_width(src_ty) == int_width(dst_ty) =>
        {
            let res = *nodes[k].results.first()?;
            k += 1;
            Some((*operand, src_ty.clone(), res, dst_ty.clone()))
        }
        _ => None,
    };
    // The LHS_BITS constant, typed at the comparison (unsigned twin) type.
    let (u_ty, bits, bits_res) = match &nodes.get(k)?.inst {
        Inst::Const { ty, value: Constant::Int(v) } if is_unsigned_int(ty) => {
            (ty.clone(), *v, *nodes[k].results.first()?)
        }
        _ => return None,
    };
    k += 1;
    // The range comparison.
    let (cmp_lhs, inbounds) = match &nodes.get(k)?.inst {
        Inst::ICmp { op: ICmpOp::Ult, ty, lhs, rhs } if *ty == u_ty && *rhs == bits_res => {
            (*lhs, *nodes[k].results.first()?)
        }
        _ => return None,
    };
    k += 1;
    // The range assert.
    match &nodes.get(k)?.inst {
        Inst::Assert { cond } if *cond == inbounds => {}
        _ => return None,
    }
    k += 1;
    // Wiring: the compared value is the lead cast's result (signed amount, cast to `u_ty`) or
    // the raw amount itself (already-unsigned amount, compared at its own type).
    let (amt, amt_ty) = match &lead {
        Some((operand, src_ty, res, dst_ty)) => {
            if cmp_lhs != *res || *dst_ty != u_ty {
                return None;
            }
            (*operand, src_ty.clone())
        }
        None => (cmp_lhs, u_ty.clone()),
    };
    // Optional value retype cast (amount → the shifted type; trust-ir's same-type contract).
    let val_cast: Option<(ValueId, Ty)> = match nodes.get(k).map(|n| &n.inst) {
        // Trust (#164 follow-through): `Bitcast` joins the three width-changing spellings.
        // This cast's width is NOT constrained by the pattern, so all four are reachable —
        // an amount already at the shifted type's width retypes with `Bitcast`.
        Some(Inst::Cast {
            op: CastOp::Trunc | CastOp::SExt | CastOp::ZExt | CastOp::Bitcast,
            src_ty,
            dst_ty,
            operand,
        }) if *operand == amt && *src_ty == amt_ty && is_int(dst_ty) => {
            let res = *nodes[k].results.first()?;
            k += 1;
            Some((res, dst_ty.clone()))
        }
        _ => None,
    };
    // The shift itself.
    let (mir_op, ty, lhs, rhs, result) = match &nodes.get(k)?.inst {
        Inst::BinOp { op, ty, lhs, rhs } if is_int(ty) => {
            let mir_op = match op {
                BinOp::Shl => MirBinOp::Shl,
                BinOp::LShr if is_unsigned_int(ty) => MirBinOp::Shr,
                BinOp::AShr if is_signed_int(ty) => MirBinOp::Shr,
                _ => return None,
            };
            (mir_op, ty.clone(), *lhs, *rhs, *nodes[k].results.first()?)
        }
        _ => return None,
    };
    k += 1;
    // The shift's amount operand must be the amount value CORRECTLY TYPED at `ty`: the raw
    // amount (its own type already is `ty`), the lead trunc's result (the unsigned twin IS
    // `ty`), or the value cast's result (cast to `ty`).
    let rhs_ok = match &val_cast {
        Some((res, dst_ty)) => rhs == *res && *dst_ty == ty,
        None => {
            (rhs == amt && amt_ty == ty)
                || lead.as_ref().is_some_and(|(_, _, res, dst_ty)| rhs == *res && *dst_ty == ty)
        }
    };
    if !rhs_ok {
        return None;
    }
    // The asserted bound must be the shifted type's exact bit width.
    if int_width(&ty).map(i128::from) != Some(bits) {
        return None;
    }
    Some(ShiftIdiom {
        len: k - i,
        lhs,
        amt,
        ty,
        u_ty,
        bits,
        range_cast: lead.is_some(),
        mir_op,
        result,
    })
}

/// Match the producer's checks-OFF shift pair at `nodes[i..]`: the value-retype
/// `Cast{Trunc|SExt|ZExt, amt_ty, ty, amt}` immediately feeding
/// `BinOp{Shl|LShr|AShr, ty, lhs, cast}`. Returns `(lhs, original_amount, ty, mir_op, result)`
/// — the emitted MIR uses the ORIGINAL amount (built MIR has no cast here; out-of-range is UB
/// on both sides, so discarding the value-preserving retype cannot change a defined execution).
fn shift_value_cast_pair(
    nodes: &[InstrNode],
    i: usize,
) -> Option<(ValueId, ValueId, Ty, MirBinOp, ValueId)> {
    let (amt, cast_res, dst_ty) = match &nodes.get(i)?.inst {
        // Trust (#164 follow-through): `Bitcast` is the equal-width spelling (see `shift_idiom`).
        Inst::Cast {
            op: CastOp::Trunc | CastOp::SExt | CastOp::ZExt | CastOp::Bitcast,
            src_ty,
            dst_ty,
            operand,
        } if is_int(src_ty) && is_int(dst_ty) =>
        {
            (*operand, *nodes[i].results.first()?, dst_ty.clone())
        }
        _ => return None,
    };
    match &nodes.get(i + 1)?.inst {
        Inst::BinOp { op, ty, lhs, rhs } if *ty == dst_ty && *rhs == cast_res => {
            let mir_op = match op {
                BinOp::Shl => MirBinOp::Shl,
                BinOp::LShr if is_unsigned_int(ty) => MirBinOp::Shr,
                BinOp::AShr if is_signed_int(ty) => MirBinOp::Shr,
                _ => return None,
            };
            Some((*lhs, amt, ty.clone(), mir_op, *nodes[i + 1].results.first()?))
        }
        _ => None,
    }
}

/// Trust (wave-IL): the shim's OWN refusal of a WHOLE-AGGREGATE `Inst::Load`, returning the
/// fail-closed reason class, or `None` for a load `to_mir` may go on to consider.
///
/// WHY A PREDICATE AND NOT AN INHERITANCE. Before this wave a `Load { ty: Ty::Enum(_) }` — the
/// instruction wave-IL's `if let PAT = <&E>` lowering emits — died in three different places, and
/// all three were the SAME classifier wearing three hats: the `Alloca` pre-pass
/// (`cx.scalar_ty(ty)` -> `None` -> "Alloca of non-scalar pointee", so an enum slot never enters
/// `slot_map`), the forwarded-ref-param arm ("Load through ref param: non-scalar or mismatched
/// pointee", again `scalar_ty`), and the "Load from a non-Alloca pointer" fall-through that only
/// catches what the first two already excluded. One predicate behind three doors is not three
/// walls; a future wave that teaches `scalar_ty` a niche-optimized enum spelling would open all
/// three at once, silently, with no diff in this file. Stated here, the construct's flip
/// exclusion survives that widening: `to_mir` consults this first and returns.
///
/// WHAT IS REFUSED: the COMPOSITE spellings for which this shim has NO congruent MIR lowering at
/// all — `Enum`/`Array`/`Tuple`/`Record`/`Set`/`Sequence`/`Closure` — plus `Ty::Unit`, which
/// denotes no value at all (the wave-UA lesson: the producer overloads `Ty::Unit` as a
/// fail-closed placeholder AND as the wave-EL opaque-lane spelling, so a unit load is never a
/// value read). `Ty::Struct` is deliberately EXCLUDED — see the next paragraph.
/// `Ty::Ptr`/`FatPtr`/`Never`/`Error`/`Func`/`Ref`-family spellings are left to the pre-existing
/// arms: they are not aggregates, and moving their rejection would relocate a reject this wave
/// has no business touching.
///
/// WHY `Ty::Struct` IS NOT IN THE REFUSED SET, AND WHY THAT IS THE LOAD-BEARING PART. A
/// whole-struct `Load` is a LIVE, SUPPORTED, FLIP-ELIGIBLE lane: `recognize_field_write` (wave-24)
/// matches the triple `agg = Load(*P):Struct` / `new = InsertField(agg, k, v)` / `Store(*P, new)`
/// through a `&mut`-param pointer and re-emits it as the byte-faithful `(*P).k = v`. That
/// recognizer runs at the TOP of the node loop and consumes three nodes with `i += 3; continue` —
/// it never reaches the `Inst::Load` match arm at all. Two consequences, both deliberate:
///   * this predicate is CALLED from the top of that loop, ABOVE `recognize_field_write`, so
///     "`to_mir` consults this first and returns" is a fact about the call site and not a hope;
///   * `Ty::Struct` must therefore be ABSENT here, or the hoist would silently delete the wave-24
///     field-write lane. Its exclusion is delegated, knowingly, to `recognize_field_write`'s own
///     `matches!(ty, Ty::Struct(_))` gate — and `test_field_write_recognizer_is_struct_only` pins
///     that gate, so extending the idiom to enums (which would otherwise reinstate exactly the
///     wall-of-absence this predicate exists to remove) fails a test instead of passing silently.
/// A struct whole-load that is NOT part of that triple still fails closed downstream on
/// `scalar_ty`, unchanged by this wave.
///
/// A strict no-op at HEAD, but not because "everything listed already failed closed" — that claim
/// was false for `Ty::Struct` and is why it is gone from the set. For the spellings that REMAIN,
/// each returns `None` from `scalar_rustc_ty` and so already died on one of the three routes
/// above; this changes only the reason CLASS the derived-verdict histogram records, the same
/// separate-the-histogram discipline `unit_const_refusal` follows.
fn aggregate_load_refusal(ty: &Ty) -> Option<&'static str> {
    match ty {
        Ty::Enum(_)
        | Ty::Array(..)
        | Ty::Tuple(_)
        | Ty::Record(_)
        | Ty::Set(..)
        | Ty::Sequence(_)
        | Ty::Closure(_) => Some("Load of a whole aggregate (no congruent MIR operand)"),
        Ty::Unit => Some("Load of a unit value (no MIR operand)"),
        _ => None,
    }
}

/// Trust (wave-UA): the shim's OWN refusal of a VALUE-LESS constant, returning the fail-closed
/// reason class, or `None` for a constant `const_of` may go on to consider.
///
/// WHY A PREDICATE AND NOT A FALL-THROUGH. Before this wave a `Ty::Unit` constant reached
/// `const_of`'s `_ => unsup("Const(non int/bool)")` catch-all only because no arm above HAPPENED
/// to match it: `Ty::Bool` no, `is_int(Ty::Unit)` false, `Ty::U128`/`Struct`/`Enum` no,
/// `is_f32_or_f64` false. That is a wall made of somebody else's absence — the fb85a73d4a failure
/// mode — and it is exactly the wall a future widening of `const_of` (a `Ty::Unit` arm added for
/// some unrelated lane, or a broadened `is_int`) would silently delete, letting a unit-arg call
/// reach the codegen flip on a const the comparator never proved congruent. Stated here, the
/// refusal survives any such widening: `const_of` consults this first and returns.
///
/// WHAT IS REFUSED, AND WHY EACH:
///   * `Ty::Unit` at any constant — built MIR carries no operand this shim can compare a
///     zero-sized unit against; fabricating one is a claim the differential never checked. This
///     is the type the wave-UA argument lane emits (`try_lower_unit_arg`).
///   * `Constant::PhantomData` at any type — the producer's zero-size marker. It is legal ONLY
///     against `Ty::Unit` per the IR validator (`shape_matches_ty`), so any OTHER pairing
///     reaching here is already ill-typed; and the producer also uses it as a deferral SENTINEL
///     under a mapped type (`PendingConst`) and as the `Ty::Ptr` lane filler inside aggregate
///     seeds, neither of which denotes a value. None may be minted into MIR.
///
/// Both refusals are strict no-ops at HEAD — every pair they claim was ALREADY refused — but not
/// all of them by the catch-all, and the difference is worth stating precisely. `(Ty::Unit, _)`
/// and `PhantomData` at the scalar/pointer types did fall to `_ => unsup("Const(non int/bool)")`.
/// `(Ty::Struct(_), PhantomData)` instead fell to the wall arm `unsup("Const(struct value)")`,
/// and `(Ty::Enum(_), PhantomData)` to `unsup("Const(enum value)")`. Both of those still refuse;
/// only the reason CLASS moves — to a hoisted, phantom-specific one — which is the same
/// separate-the-histogram discipline those two wall arms were themselves written to serve.
fn unit_const_refusal(ty: &Ty, c: &Constant) -> Option<&'static str> {
    match (ty, c) {
        (Ty::Unit, _) => Some("Const(unit value: no MIR operand)"),
        (_, Constant::PhantomData) => Some("Const(phantom value: no MIR operand)"),
        _ => None,
    }
}

#[cfg(test)]
mod unit_const_wall_tests {
    use std::collections::HashMap;

    use rustc_middle::mir::{Local, Place};
    use trust_ir::{Constant, Inst, InstrNode, Ty, ValueId};

    use super::{SCALAR_CANDS, aggregate_load_refusal, recognize_field_write, unit_const_refusal};

    /// THE wave-IL FLIP EXCLUSION. `Inst::Load { ty: Ty::Enum(_) }` is what
    /// `try_lower_if_let_ref_enum` emits, and it is refused HERE, by this predicate, on the type
    /// alone. The assertion is deliberately NOT routed through `scalar_ty`: the point of the
    /// predicate is that it keeps refusing even if some future wave teaches the scalar
    /// classifier a niche-optimized enum spelling — the widening that would otherwise open the
    /// `Alloca` pre-pass, the ref-param arm and the non-Alloca fall-through simultaneously.
    #[test]
    fn test_aggregate_load_refusal_enum_load_refused() {
        assert_eq!(
            aggregate_load_refusal(&Ty::Enum(trust_ir::EnumId(0))),
            Some("Load of a whole aggregate (no congruent MIR operand)"),
        );
    }

    /// The rest of the composite family, plus the value-less `Ty::Unit` lane under its own
    /// reason class. Stated over the whole set so the wall is not one hand-picked member.
    /// `Ty::Struct` is NOT in this list — see `test_field_write_recognizer_is_struct_only`.
    #[test]
    fn test_aggregate_load_refusal_covers_the_composite_family() {
        for ty in [
            Ty::Enum(trust_ir::EnumId(2)),
            Ty::Array(trust_ir::TyId(3), 4),
            Ty::Tuple(vec![Ty::I64, Ty::Bool]),
        ] {
            assert_eq!(
                aggregate_load_refusal(&ty),
                Some("Load of a whole aggregate (no congruent MIR operand)"),
                "a whole-aggregate load must not be mintable at {ty}",
            );
        }
        assert_eq!(
            aggregate_load_refusal(&Ty::Unit),
            Some("Load of a unit value (no MIR operand)")
        );
    }

    /// The predicate must not shadow any lane `to_mir` genuinely supports, or it would drop
    /// coverage rather than add safety: every scalar the shim can denote passes through.
    #[test]
    fn test_aggregate_load_refusal_scalar_loads_pass_through() {
        for ty in SCALAR_CANDS {
            assert_eq!(aggregate_load_refusal(&ty), None, "{ty} is a supported load lane");
        }
        // The pointer/never spellings keep their PRE-EXISTING rejects; this wave does not
        // relocate them.
        assert_eq!(aggregate_load_refusal(&Ty::Ptr), None);
        assert_eq!(aggregate_load_refusal(&Ty::FatPtr(trust_ir::FatPtrKind::Str)), None);
        // And `Ty::Struct` passes through too — it is a LIVE lane (`recognize_field_write`), not
        // an oversight. Refusing it here would silently delete the wave-24 field-write idiom,
        // because this predicate is consulted ABOVE that recognizer in the node loop.
        assert_eq!(
            aggregate_load_refusal(&Ty::Struct(trust_ir::StructId(1))),
            None,
            "a struct whole-load is the wave-24 field-write lane, not a refusal",
        );
    }

    /// Build the wave-24 WRITE triple `agg = Load(*P):<ty>` / `new = InsertField(agg, k, v)` /
    /// `Store(*P, new)` over a carrier of type `load_ty`, with `P = %0` registered as a
    /// `&mut`-param pointer. Everything except `load_ty` is held fixed, so the recognizer's
    /// verdict isolates the type gate.
    fn write_triple(load_ty: Ty) -> (HashMap<ValueId, Place<'static>>, Vec<InstrNode>) {
        let (p, agg, new, v) =
            (ValueId::new(0), ValueId::new(1), ValueId::new(2), ValueId::new(3));
        let fwd: HashMap<ValueId, Place<'static>> =
            HashMap::from([(p, Place::from(Local::from_u32(1)))]);
        let nodes = vec![
            InstrNode::new(Inst::Load { ty: load_ty.clone(), ptr: p, volatile: false, align: None })
                .with_result(agg),
            InstrNode::new(Inst::InsertField {
                ty: load_ty.clone(),
                aggregate: agg,
                field: 0,
                value: v,
            })
            .with_result(new),
            InstrNode::new(Inst::Store {
                ty: load_ty,
                ptr: p,
                value: new,
                volatile: false,
                align: None,
            }),
        ];
        (fwd, nodes)
    }

    /// THE CORRECTION THAT MADE `aggregate_load_refusal` TRUE. `recognize_field_write` consumes an
    /// `Inst::Load` triple at the TOP of the node loop with `i += 3; continue` — it never reaches
    /// the `Inst::Load` match arm. So wave-IL's whole-enum-load flip exclusion held, before this
    /// fix, only because that recognizer HAPPENS to gate on `Ty::Struct(_)`: somebody else's
    /// current contents, i.e. the wall-of-absence the wave claimed to have removed.
    ///
    /// Two halves, and both are needed. The POSITIVE half proves the fixture really is the shape
    /// the recognizer accepts (otherwise the negative half would be vacuous — every `None` could
    /// be an unrelated structural miss). The NEGATIVE half is the pin: swap ONLY the load type to
    /// an enum, and the recognizer must still decline. Fill that absence in — teach the idiom
    /// enum field-writes — and this test fails, forcing the author to confront that the same edit
    /// would route a `Load { ty: Ty::Enum(_) }` past `aggregate_load_refusal` were the predicate
    /// not hoisted above it.
    #[test]
    fn test_field_write_recognizer_is_struct_only() {
        let (fwd, nodes) = write_triple(Ty::Struct(trust_ir::StructId(7)));
        assert_eq!(
            recognize_field_write(&fwd, &nodes, 0),
            Some((Place::from(Local::from_u32(1)), 0, ValueId::new(3))),
            "the struct write triple IS the wave-24 lane — if this stops matching, the negative \
             assertions below stop meaning anything",
        );
        for load_ty in [
            Ty::Enum(trust_ir::EnumId(7)),
            Ty::Tuple(vec![Ty::I64, Ty::Bool]),
            Ty::Array(trust_ir::TyId(0), 2),
            Ty::Unit,
            Ty::U64,
        ] {
            let (fwd, nodes) = write_triple(load_ty.clone());
            assert_eq!(
                recognize_field_write(&fwd, &nodes, 0),
                None,
                "the field-write idiom must stay struct-only: a {load_ty} whole-load reaching it \
                 would bypass `aggregate_load_refusal`",
            );
        }
    }

    /// The wave-UA argument lane's exact emission — `Inst::Const { ty: Ty::Unit, value:
    /// PhantomData }` — is refused, by this predicate, under its own reason class. `Ty::Unit`
    /// wins over the PhantomData arm so a unit const reads as a unit refusal, not a phantom one.
    #[test]
    fn test_unit_const_refusal_unit_typed_const_refused() {
        assert_eq!(
            unit_const_refusal(&Ty::Unit, &Constant::PhantomData),
            Some("Const(unit value: no MIR operand)"),
        );
        // Refused for its TYPE, whatever constant is paired with it.
        assert_eq!(
            unit_const_refusal(&Ty::Unit, &Constant::Int(0)),
            Some("Const(unit value: no MIR operand)"),
        );
        assert_eq!(
            unit_const_refusal(&Ty::Unit, &Constant::Aggregate(Vec::new())),
            Some("Const(unit value: no MIR operand)"),
        );
    }

    /// The producer's zero-size marker never becomes a MIR const, including at the scalar and
    /// pointer types where it appears as a deferral sentinel / aggregate-seed lane filler.
    #[test]
    fn test_unit_const_refusal_phantom_data_refused_at_every_type() {
        for ty in [Ty::Ptr, Ty::I64, Ty::Bool, Ty::F64, Ty::U128] {
            assert_eq!(
                unit_const_refusal(&ty, &Constant::PhantomData),
                Some("Const(phantom value: no MIR operand)"),
                "PhantomData must not be mintable at {ty}",
            );
        }
    }

    /// The flippable scalar constants are untouched — this predicate must not shadow any lane
    /// `const_of` genuinely supports, or it would silently drop coverage rather than add safety.
    #[test]
    fn test_unit_const_refusal_scalar_constants_pass_through() {
        assert_eq!(unit_const_refusal(&Ty::Bool, &Constant::Bool(true)), None);
        assert_eq!(unit_const_refusal(&Ty::I64, &Constant::Int(-7)), None);
        assert_eq!(unit_const_refusal(&Ty::U128, &Constant::U128(u128::MAX)), None);
        assert_eq!(unit_const_refusal(&Ty::F32, &Constant::Float(1.0)), None);
        // The wall arms below it keep their own, more specific reason classes.
        assert_eq!(unit_const_refusal(&Ty::Ptr, &Constant::Int(0)), None);
    }
}

#[cfg(test)]
mod u128_v24_reconstruction_tests {
    use super::*;

    #[test]
    fn upper_half_u128_switch_case_keeps_all_bits() {
        assert_eq!(integer_switch_case_bits(&Constant::U128(u128::MAX), 128), Some(u128::MAX),);
        assert_eq!(
            integer_switch_case_bits(&Constant::U128(i128::MAX as u128 + 1), 128),
            Some(i128::MAX as u128 + 1),
        );
    }

    #[test]
    fn u128_switch_case_cannot_narrow() {
        assert_eq!(integer_switch_case_bits(&Constant::U128(u128::MAX), 64), None);
        assert_eq!(integer_switch_case_bits(&Constant::Int(-1), 64), Some(u128::MAX));
    }
}


#[cfg(test)]
mod scope_topology_tests {
    use super::scope_topology_error;
    use trust_ir::ScopeData;

    fn sc(parent: Option<u32>) -> ScopeData {
        ScopeData { parent, span: None }
    }

    #[test]
    fn well_formed_chain_and_fan_out_are_accepted() {
        assert_eq!(scope_topology_error(&[sc(None)]), None, "lone root");
        // The `let`-chain shape the producer actually emits.
        assert_eq!(
            scope_topology_error(&[sc(None), sc(Some(0)), sc(Some(1))]),
            None,
            "nested chain"
        );
        // Sibling scopes under one parent — two blocks at the same depth.
        assert_eq!(
            scope_topology_error(&[sc(None), sc(Some(0)), sc(Some(0)), sc(Some(2))]),
            None,
            "fan-out"
        );
    }

    #[test]
    fn every_malformed_shape_is_rejected() {
        // Each case is a way a buggy producer could hand us a tree that a naive
        // consumer would either hang on or silently flatten.
        assert!(scope_topology_error(&[]).is_some(), "empty table");
        assert!(scope_topology_error(&[sc(Some(0))]).is_some(), "root claims a parent");
        assert!(
            scope_topology_error(&[sc(None), sc(None)]).is_some(),
            "second root"
        );
        assert!(
            scope_topology_error(&[sc(None), sc(Some(1))]).is_some(),
            "self-parent: the one-node cycle"
        );
        assert!(
            scope_topology_error(&[sc(None), sc(Some(2)), sc(Some(1))]).is_some(),
            "forward reference: the two-node cycle"
        );
        assert!(
            scope_topology_error(&[sc(None), sc(Some(9))]).is_some(),
            "parent past the end of the table"
        );
    }
}


#[cfg(test)]
mod emission_chokepoint_tests {
    /// Trust (C2 repair): `LowerCx::push_node` is documented as "the ONLY instruction-emission
    /// chokepoint" — it is where `cur_span` and `cur_scope` are stamped. That claim was FALSE
    /// for most of C2's life: `emit_call` and four static/global sites pushed to `self.cur`
    /// directly, so every `Inst::Call` shipped with no span and no scope, and the consumer
    /// silently inherited the previous node's location.
    ///
    /// Nothing in the type system prevents the next author from writing `self.cur.push(..)`
    /// again, and the failure is invisible — no error, no ICE, just debug info that quietly
    /// points at the wrong line. So the invariant is pinned at the SOURCE: exactly one
    /// `self.cur.push(` may exist in the producer, the one inside `push_node` itself.
    ///
    /// A source-text guard is crude, and it is the honest tool here: the alternative is an
    /// invariant stated only in a doc comment, which is precisely what failed.
    #[test]
    fn push_node_is_the_only_emission_site() {
        let src = include_str!("lib.rs");
        let sites = src.matches("self.cur.push(").count();
        assert_eq!(
            sites, 1,
            "found {sites} `self.cur.push(` sites in trust-thir-lower/src/lib.rs; exactly one \
             is allowed (the body of `push_node`). A new direct push bypasses span/scope \
             stamping — route it through `self.push_node(..)` instead."
        );
    }

    /// Trust (wave-UV): the by-VALUE closure-env param must be refused BY NAME, not by falling
    /// off the end of `param_rty` into the catch-all.
    ///
    /// The `UpvarRef` by-value fork's CLEAN-ONLY claim is "no body of this shape can reach the
    /// codegen flip", and the derived-MIR half of that claim is this refusal. A claim that rests
    /// on a catch-all rests on somebody else's absence: widen the catch-all — or add a `Ty` arm
    /// above it that happens to swallow closures — and the flip exclusion evaporates silently,
    /// with no test going red. So the arm's EXISTENCE and its POSITION (before the catch-all,
    /// which is what makes it the one that fires) are pinned at the source.
    ///
    /// Needles are assembled at run time: this test's own source is inside
    /// `include_str!("to_mir.rs")`, so a literal needle would match itself and the guard would
    /// pass with the production arm deleted.
    #[test]
    fn test_closure_env_param_is_refused_by_name() {
        let producer = include_str!("to_mir.rs");
        let lane = producer
            .find(&format!("fn {}<'tcx>(", "param_rty"))
            .expect("`param_rty` must exist");
        let arm = format!("Ty::{}(_) => unsup(\"closure-env param", "Closure");
        assert_eq!(
            producer.matches(arm.as_str()).count(),
            1,
            "the by-value closure env must be refused by its OWN named arm, exactly once",
        );
        let arm_at = producer[lane..].find(arm.as_str()).expect("the arm is inside `param_rty`");
        // The TOP-LEVEL catch-all, anchored by its 8-space match-arm indentation: the `Ty::Struct`
        // arm nests a same-worded refusal one level deeper, and matching that one instead would
        // make this ordering assertion pass for the wrong reason.
        let catch_all = format!("\n        {} => unsup(format!(\"non-scalar param {}", "_", "type");
        let catch_at =
            producer[lane..].find(catch_all.as_str()).expect("the catch-all is inside `param_rty`");
        assert!(
            arm_at < catch_at,
            "the named closure arm must precede the catch-all, or the catch-all is still what \
             fires and the refusal is not by name",
        );
    }
}

#[cfg(test)]
mod str_const_flip_firewall_tests {
    use std::collections::HashMap;

    use trust_ir::{Constant, FatPtrKind, Inst, InstrNode, Ty, ValueId};
    use trust_ir::value::GlobalId;

    use super::recognize_str_return;

    fn node(inst: Inst, result: ValueId) -> InstrNode {
        InstrNode::new(inst).with_result(result)
    }

    /// Build the three-node `&str` fat-pointer chain the producer emits, with `metadata` supplied
    /// by the caller so the LITERAL lane (a real `Constant::Int` length) and the CONST lane (the
    /// `Constant::PhantomData` sentinel) differ in exactly one node.
    fn chain(metadata_value: Constant) -> (Vec<InstrNode>, ValueId) {
        let data = ValueId::new(0);
        let len = ValueId::new(1);
        let fat = ValueId::new(2);
        (
            vec![
                node(Inst::GlobalAddr { global: GlobalId::new(0) }, data),
                node(Inst::Const { ty: Ty::U64, value: metadata_value }, len),
                node(
                    Inst::PtrFromParts {
                        ptr_ty: Ty::FatPtr(FatPtrKind::Str),
                        metadata_ty: Ty::U64,
                        data,
                        metadata: len,
                    },
                    fat,
                ),
            ],
            fat,
        )
    }

    fn defs(nodes: &[InstrNode]) -> HashMap<ValueId, &InstrNode> {
        nodes.iter().filter_map(|n| n.results.first().map(|v| (*v, n))).collect()
    }

    /// THE MISCOMPILE FIREWALL, pinned at the node type.
    ///
    /// Built MIR keeps a `&str` CONST unevaluated (`_0 = const names::NAME`); it folds only a
    /// LITERAL to `_0 = const "…"`. The shim's return-type gate ADMITS `Ty::FatPtr(Str)` against a
    /// built `&str`, so if the const lane emitted a real `Constant::Int` length its chain would be
    /// byte-indistinguishable from a literal's, `recognize_str_return` would match, and the shim
    /// would rewrite the return into `_0 = const "Clean.BVC.bvAppend"` — a MANUFACTURED comparator
    /// divergence against built MIR's unevaluated const.
    ///
    /// The `Constant::PhantomData` metadata sentinel makes this recognizer refuse BY ITS OWN
    /// PREDICATE (the `Constant::Int(v)` arm), independently of the three `pending_consts`
    /// emptiness gates upstream. Refusing means the chain is NOT added to the skip set, so the
    /// unhandled `Inst::GlobalAddr` then fails the whole shim closed.
    #[test]
    fn test_recognize_str_return_refuses_a_phantomdata_metadata_node() {
        let (nodes, fat) = chain(Constant::PhantomData);
        assert!(
            recognize_str_return(&defs(&nodes), fat).is_none(),
            "a const-sourced fat pointer must NOT be recognized as a foldable &str literal"
        );
    }

    /// The POSITIVE CONTROL that makes the refusal above non-vacuous: the same chain with a real
    /// length IS recognized, so the test is discriminating the metadata node and nothing else.
    #[test]
    fn test_recognize_str_return_still_accepts_the_literal_chain() {
        let (nodes, fat) = chain(Constant::Int(7));
        let (global, len, skip) = recognize_str_return(&defs(&nodes), fat)
            .expect("the str LITERAL lane must keep flipping");
        assert_eq!(global, GlobalId::new(0));
        assert_eq!(len, 7);
        assert_eq!(skip.len(), 3, "all three chain nodes must be skipped");
    }

    /// A negative length is not a byte count. Pinned alongside the sentinel refusal so the
    /// `v >= 0` clause is not silently dropped while widening the arm.
    #[test]
    fn test_recognize_str_return_refuses_a_negative_length() {
        let (nodes, fat) = chain(Constant::Int(-1));
        assert!(recognize_str_return(&defs(&nodes), fat).is_none());
    }
}

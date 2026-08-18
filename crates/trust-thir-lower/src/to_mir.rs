//! trust-ir -> rustc MIR: the compat shim ("LLVM2", P1.2 slices 1+2+3).
//!
//! Reconstructs a `rustc_middle::mir::Body` from the producer's `trust_ir::Module` for the
//! SCALAR fragment (straight-line, if/join, and natural-loop CFGs, including
//! sequential loops; nested loops remain producer-refused): int/bool params,
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
//! STORAGE MARKERS: the shim emits `StorageLive`/`StorageDead` only through four mutually
//! exclusive whole-body plans: rvalue operand temps in a `let`-free single-block scalar body
//! (wave-MF, [`plan_operand_marker_temps`]), the lane-K multi-block branch plan, field-write
//! operand temps ([`plan_field_write_markers`]), and the single interior-borrow reborrow temp
//! ([`plan_interior_borrow_markers`]). The operand plan also covers aggregate-construction fields
//! ([`agg_field_order_ok`]) and a shared-ref-param `Inst::Load`. Marker fidelity is, as before,
//! PROVEN OR REFUSED per body by the comparator's exact marker channel
//! (`mir_differential::canon_markers`); the flip only consumes a derived body at `-O`
//! (`sess.emit_lifetime_markers()`) when that channel proved exact equality. Wave-MF changes
//! what the shim OFFERS that channel, never what the channel accepts.
//!
//! EVERY MARKER GOES THROUGH A PLAN (lane MF-ZERO-3, 2026-08-13). Until this lane that sentence
//! was false of two sites: the `(*P).k = v` field-write arm and wave-29b's interior-borrow
//! reborrow temp both pushed their pairs unconditionally. Three independent reviews found the
//! first one — 12 admitted-and-wrong bodies, then 17 — and each round repaired what the reviewer
//! named (the shapes, then the arm's RHS predicate) while leaving the arm's SCOPE alone. Both
//! sites now consult a plan of their own ([`plan_field_write_markers`],
//! [`plan_interior_borrow_markers`]), the plans are MUTUALLY EXCLUSIVE (one whole-body marker
//! claim per body), and the ability to construct a marker at all is confined to [`mf_gate`],
//! whose five plan-consulting emission methods are the only way to reach a MIR block with one.
//! Round 5 (2026-08-14) seals the plans themselves inside that module and closes every body with a
//! LAW whose two sides are derived independently — the markers observed in the FINISHED body
//! against the markers the SEALED PLANS predict from the trust-ir. The
//! source-level half of that invariant is `marker_gate_invariant_tests`, which carries its own
//! mutation proof — a new arm that pushes a raw marker fails a test rather than silently
//! emitting.
//!
//! THE INFEASIBILITY ARGUMENT, RE-ARGUED AT HEAD (2026-08-12; the 2026-07-02 version of this
//! paragraph is superseded, not inherited). The old counterexample was `fn tail(a,b){a+b}` vs
//! `fn letted(a,b){let s=a+b; s}` "lower to byte-identical trust-ir functions". **That is no
//! longer true.** Since trust-ir v33 (C2-scopes, `first-party/trust-ir` 33dd3ee) the producer
//! stamps a lexical scope tree, and the pair is distinguishable — measured, this compiler, this
//! week: `tail` emits no `#scope:` table at all, `letted` emits `#scope: 0 root` +
//! `#scope: 1 parent=0` and per-instruction stamps. So `f(Module) -> markers` is no longer
//! refuted by that pair.
//!
//! **The claim nevertheless survives in a weaker, sharper form, and here is the current
//! counterexample.** `AllocationId::is_null` (`self.0 == 0`) and its twin
//! (`let x = self.0; x == 0`) lower to trust-ir INSTRUCTION STREAMS that are identical
//! instruction for instruction (`extractfield; const; icmp; ret`); only the scope table differs.
//! Their built marker sequences differ — 2 markers vs 4, the twin additionally carrying a
//! `FakeRead` and a named local. So a marker function that reads only the instruction stream is
//! still wrong on one of them.
//!
//! Wave-MF therefore does not claim general reconstructibility. It takes the scope table as the
//! FIREWALL: the plan engages only when `func.scopes.is_none()`, i.e. the producer opened no
//! `let`-visibility scope (`build_source_scopes`: "the producer only ever opens `let`-visibility
//! scopes"), which is exactly the condition under which the instruction stream IS the whole
//! story. Bodies with a `let` keep today's behaviour — no derived markers, `markers_exact:
//! false`, no flip at `-O`. That is a partial discharge with its boundary named, not a general
//! solution: reconstructing the let-bound case needs the scope table CONSUMED (which binding,
//! which value, where the `FakeRead` goes), and that is not attempted here.
//!
//! Before wave-MF, `markers_exact` meant in practice "the built body's reachable subgraph is
//! marker-free" (unit fns, const-returning closures, param-identity bodies). It now additionally
//! holds for the planned class.
//!
//! MULTI-BLOCK (lane K, 2026-08-12): the same discipline, one construct wider. A `let`-free
//! STRUCTURED `if` / `&&` / `||` body ([`plan_branch_markers`]) now also gets its markers, and
//! the cross-block half of built's placement with them: the condition's OPERAND temps are
//! retired at the entry of BOTH arms, its RESULT temp at the join, and the false edge is routed
//! through an EMPTY TRAMPOLINE block because `canon_markers` walks the RAW CFG with no goto
//! threading. Wave-MF's `func.scopes.is_none()` firewall is consulted first and unchanged, so
//! this widens the class along ONE axis (control flow) and none of the others. The trampoline is
//! the only STRUCTURAL addition this shim has ever made to a derived body; it is invisible to
//! the semantic channel, which threads every `Goto` block onto its incoming edges (LEDGER L3),
//! and it is emitted only when the branch plan engages.
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

use std::collections::{BTreeMap, HashMap, HashSet};

use rustc_abi::{FIRST_VARIANT, FieldIdx};
use rustc_hir::def::DefKind;
use rustc_hir::{HirId, ItemLocalId, PatKind};
use rustc_index::IndexVec;
use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
// Trust (wave-str): `CTFE_ALLOC_SALT` (= 0) is the dedup salt `tcx.allocate_bytes_dedup` uses for a
// `&str` literal's byte allocation; using it means the shim's re-emitted `&str` const dedups to the
// SAME `AllocId` as the built literal → byte-identical codegen.
use rustc_middle::mir::interpret::CTFE_ALLOC_SALT;
use rustc_middle::mir::{
    AggregateKind, AssertKind, BasicBlock, BasicBlockData, BinOp as MirBinOp, Body, BorrowKind,
    CallSource, CastKind, ClearCrossCrate, Const as MirConst, ConstOperand, ConstValue, Local,
    LocalDecl, LocalInfo, MirSource, Operand, Place, Rvalue, SourceInfo, SourceScope,
    SourceScopeData, SourceScopeLocalData, StatementKind, Terminator, TerminatorKind,
    UnOp as MirUnOp, UnwindAction, VarDebugInfo, VarDebugInfoContents, WithRetag,
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

use crate::{CalleeRef, SiteArg, SiteConst, SiteTy, SiteValTree};

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

fn source_binding_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    hir_local_id: u32,
) -> Option<RustcTy<'tcx>> {
    let owner = tcx.local_def_id_to_hir_id(def).owner;
    tcx.typeck(def).node_type_opt(HirId { owner, local_id: ItemLocalId::from_u32(hir_local_id) })
}

/// Reconstruct the one source identity that can be mapped to an ABI argument
/// without consulting producer metadata: a plain direct HIR parameter binding
/// at the same positional MIR argument.
///
/// A loop-carried source parameter must reuse this place. Allocating a second
/// header temp leaves the argument as a frozen entry copy; naming either copy
/// `n` then makes an authored invariant about mutable `n` ambiguous or, worse,
/// binds it to the frozen copy. Non-direct/destructured parameters are omitted
/// and remain eligible only when the independently authenticated loop binding
/// can be represented by a fresh, globally injective local below.
fn direct_parameter_source_places<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    arg_places: &[Place<'tcx>],
) -> HashMap<u32, Place<'tcx>> {
    let Some(body) = tcx.hir_maybe_body_owned_by(def) else {
        return HashMap::new();
    };
    if body.params.len() != arg_places.len() {
        // Closure/coroutine ABI prefixes and every other non-positional shape
        // are outside this exact source-place reconstruction.
        return HashMap::new();
    }

    body.params
        .iter()
        .zip(arg_places.iter().copied())
        .filter_map(|(param, place)| {
            let PatKind::Binding(_, canonical_id, _, None) = param.pat.kind else {
                return None;
            };
            (canonical_id == param.pat.hir_id).then_some((canonical_id.local_id.as_u32(), place))
        })
        .collect()
}

/// Trust (lane MF-ZERO, 2026-08-13): THE SOURCE-FORM GATE — the three questions about a body that
/// the trust-ir instruction stream provably cannot answer, asked of the HIR instead.
///
/// Returns `false` (the marker plans then engage nowhere in this body, i.e. today's marker-free
/// behaviour) unless ALL of the following hold. Every one of them is a shape where `rustc_mir_build`
/// mints a local, or mints temps in an order, that the producer's instruction list does not record;
/// each was ADMITTED-AND-WRONG before this gate and is now refused BY NAME.
///
/// 1. **Every parameter is a simple by-value binding, or `_`.** `args_and_body` introduces "no
///    extra copies for simple bindings" — `PatKind::Binding { mode: BindingMode(ByRef::No, _),
///    subpattern: None }` reuses the argument local — and for EVERY other parameter pattern goes
///    through `declare_bindings` + `place_into_pattern`, minting a NAMED BINDING LOCAL with its
///    own `StorageLive`/`StorageDead` pair. Measured on `probes/mf_residual.rs`: `fn f(&l: &u64)
///    { l == 0 }` builds to FOUR markers (`_2` the binding, `_3` the comparison's operand temp)
///    where `fn f(p: &u64) { *p == 0 }` builds to TWO — and the two bodies have BYTE-IDENTICAL
///    trust-ir (`load; const; icmp; ret`) and BOTH carry `func.scopes.is_none()`, because the
///    producer opens `let`-visibility scopes only. This is the one construct wave-MF's
///    `scopes.is_none()` firewall names and cannot see; it is answered here instead of by the
///    oracle. `PatKind::Wild` is ADMITTED, and that is measured too, not assumed: `declare_bindings`
///    binds nothing for `_`, so `d4_wild_param` is `markers_exact: true` in the control and stays
///    there.
///
/// 2. **No block in the body has statements.** A body with a statement is not one expression tree,
///    and the plan's whole model — "an instruction result is an operand temp of the enclosing
///    expression" — is a statement about expression trees. Measured: `fn f(mut a: u64) -> bool
///    { a = a | 1; a == 1 }` builds the `|` straight into the ARGUMENT local (`_1 = BitOr(move _2,
///    const 1)`), while the shim treats the same `%1` as a marked operand temp and lives it first;
///    `fn f(mut a: u64, b: u64) -> bool { a = b; a == 0 }` is worse still (built emits a bare
///    place-to-place assign and no temp at all). Neither is distinguishable from its expression
///    twin `(a | 1) == 1` in trust-ir. `let` is already refused by the scope firewall; this covers
///    the assignment and item statements it does not.
///
/// 3. **Every struct literal enumerates all its fields, and any out-of-declaration-order literal
///    is one the marker channel CANNOT SEE** ([`permutation_is_observable`] — lane MF-ZERO-2
///    narrowed this from a flat "in declaration order", which cost seven flips that were
///    `markers_exact` and flipping in the control). `as_rvalue`'s
///    `ExprKind::Adt` arm sends the explicitly-written fields through `as_operand` "in order given
///    by user" — SOURCE order, not field order — while the shim mints a place-valued field's temp
///    at the aggregate site in FIELD order. Measured: `MixedT { b: y, a: x }` (`u8`, `u64`) builds
///    `mk b0.0:live s0:u64` and the shim derives `mk b0.0:live s0:u8`. The producer lowers field
///    values in source order too (`for (idx, fexpr) in field_exprs`), so an INSTRUCTION-valued
///    field's misordering is visible in trust-ir — but
///    a PARAM-valued field mints no instruction at all, and `MixedT { b: y, a: x }` and
///    `MixedT { a: x, b: y }` have byte-identical trust-ir. Only the source form separates them.
///
///    The same clause is what retires the FUNCTIONAL-RECORD-UPDATE ambiguity. `P { f: v, ..base }`
///    reads each omitted field as `ExtractField{base, i}` — exactly what a written-out `base.f`
///    emits — but built consumes a base-supplied field as a BARE PLACE with no temp and no marker.
///    `agg_field_order_ok` used to refuse BOTH spellings (any field `i` fed by a read of field `i`),
///    which is sound but wider than its own justification: `P3 { a: p.c, b: p.b, c: p.a }` has NO
///    FRU spelling that produces its instruction stream, because the producer appends the base
///    reads AFTER every explicit field (`lower_expr(base_expr)` runs after the `field_exprs` loop),
///    so `P3 { a: p.c, c: p.a, ..p }` emits the base read LAST (`%3`) where the written-out form
///    emits it in the middle (`%2`). Refusing `StructTailExpr::Base` HERE answers the question the
///    instruction stream could not, and the written-out forms — including the ones whose fields ARE
///    same-index reads — go back to flipping.
///
/// FAIL-CLOSED EVERYWHERE: a body HIR cannot reach (`hir_maybe_body_owned_by` is `None`), a
/// non-local typeck root, an expression with no recorded type, a non-`struct` ADT literal, an
/// unknown field name, `Foo { .. }` default-fields and the parse-error tail all return `false`.
/// `false` only ever REMOVES derived markers, so a wrong answer here costs exactness and can never
/// manufacture it.
///
/// NESTED BODIES ARE NOT WALKED (`NestedFilter::None`). A closure is its own `LocalDefId` with its
/// own trust-ir `Function`, and the shim asks this gate again when it lowers it — which is how
/// `|&l| l == 0` (the `BigNat::is_zero::{closure#0}` shape) is refused on its OWN parameter pattern
/// rather than on its enclosing function's.
fn source_form_admits<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId) -> bool {
    let Some(body) = tcx.hir_maybe_body_owned_by(def) else {
        return false;
    };
    if !hir_params_are_simple_bindings(body) {
        return false;
    }
    let Some(root) = tcx.typeck_root_def_id(def.to_def_id()).as_local() else {
        return false;
    };
    let mut gate = SourceFormGate { typeck: tcx.typeck(root), ok: true };
    rustc_hir::intravisit::Visitor::visit_expr(&mut gate, body.value);
    gate.ok
}

/// Trust (lane MF-ZERO, rule 1; lifted to a shared decision by lane MF-ZERO-3): does EVERY
/// parameter reuse its argument local, minting no binding local of its own?
///
/// `args_and_body` introduces "no extra copies for simple bindings" — `PatKind::Binding { mode:
/// BindingMode(ByRef::No, _), subpattern: None }` reuses the argument local — and for EVERY other
/// parameter pattern goes through `declare_bindings` + `place_into_pattern`, minting a NAMED
/// BINDING LOCAL with its own `StorageLive`/`StorageDead` pair. `PatKind::Wild` is ADMITTED, and
/// that is measured, not assumed: `declare_bindings` binds nothing for `_`, so `d4_wild_param` is
/// `markers_exact: true` in the control and stays there.
///
/// ONE decision, consulted by all three source-side plans ([`source_form_admits`],
/// [`plan_field_write_markers`], [`plan_interior_borrow_markers`]) — a destructuring parameter
/// mints its binding local whatever the rest of the body looks like, and the guard table gets one
/// honest row instead of three copies of it.
fn hir_params_are_simple_bindings<'tcx>(body: &'tcx rustc_hir::Body<'tcx>) -> bool {
    body.params.iter().all(|param| {
        matches!(
            param.pat.kind,
            PatKind::Wild
                | PatKind::Binding(rustc_hir::BindingMode(rustc_hir::ByRef::No, _), _, _, None)
        )
    })
}

/// Trust (LANE PCA plan-clause audit, 2026-08-17): does this body's PARAMETER LIST mint no binding
/// local, for the checked-arithmetic chain plan?
///
/// **This is wave-CK's clause C3, narrowed to what it can justify and moved to where the question
/// is answerable.** C3 was `blk.params.is_empty()` — a body with ANY trust-ir entry-block parameter
/// was refused — and its stated reason was that "a block parameter is a function argument, whose
/// built operand temp is minted at the CONSUMER and interleaves with these". That reason does not
/// reach the bodies it refuses: the plan's own clauses force every chain leaf to be a `Const`
/// (`consts.contains(rhs)`, and `consts.contains(lhs)` at `k == 0`) and every node to be a `Const`
/// or part of a `checked_unit`, so NO instruction of an admitted body can read a parameter at all,
/// and there is nothing to interleave.
///
/// MEASURED, both directions, on a 2,002-body corpus (`probes/pca_checked.rs` group C3): deleting
/// C3 outright moves TEN bodies — NINE of them from `refused` to `right` (`fn f(_a: usize) ->
/// usize { 256 * 1024 * 1024 }` and its siblings are `2 marker line(s) identical` with C3 gone),
/// and ONE, `ck_c3_pat_ref_mode` (`fn f(ref _a: usize) -> usize { … }`), from `refused` to
/// **WRONG-DIVERGE**. That tenth body is the whole content of the clause: a `ref`-mode parameter is
/// not a simple binding, so `args_and_body` sends it through `declare_bindings` +
/// `place_into_pattern` and mints a NAMED BINDING LOCAL with its own `StorageLive`/`StorageDead`
/// pair — a marker the instruction stream cannot see, exactly as [`source_form_admits`] rule 1
/// says. `plan_checked_markers` is a trust-ir-only plan and never consulted that rule.
///
/// So the clause is kept in the ONE form its argument supports — the parameter list mints no local
/// — and the other nine bodies stop being refused for a hazard they do not have. This is the same
/// predicate [`source_form_admits`], [`plan_field_write_markers`] and
/// [`plan_interior_borrow_markers`] already share, asked from the seal site, where `tcx` and the
/// `LocalDefId` exist.
///
/// FAIL-CLOSED: a body HIR the query cannot reach answers `false`, which only ever REMOVES derived
/// markers.
fn checked_params_mint_no_local(tcx: TyCtxt<'_>, def: LocalDefId) -> bool {
    tcx.hir_maybe_body_owned_by(def).is_some_and(hir_params_are_simple_bindings)
}

/// The walker behind [`source_form_admits`]. `ok` is write-once-to-`false`; a refused node stops
/// descending but the walk continues elsewhere, which costs nothing (the answer is already `false`).
struct SourceFormGate<'tcx> {
    typeck: &'tcx ty::TypeckResults<'tcx>,
    ok: bool,
}

impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for SourceFormGate<'tcx> {
    fn visit_block(&mut self, blk: &'tcx rustc_hir::Block<'tcx>) {
        // An ITEM statement (`fn`/`struct`/`use` nested in a block) declares a separate def and
        // emits nothing into this body, so it is not a statement in the sense that matters here.
        // `Let`, `Expr` and `Semi` all can be, and all are refused.
        if blk.stmts.iter().any(|s| !matches!(s.kind, rustc_hir::StmtKind::Item(_))) {
            self.ok = false;
            return;
        }
        rustc_hir::intravisit::walk_block(self, blk);
    }

    fn visit_expr(&mut self, ex: &'tcx rustc_hir::Expr<'tcx>) {
        // Trust (lane MF-R5, 2026-08-14): **A MATCH SCRUTINEE IS NOT AN `if` CONDITION.** This is
        // the residual the fifth review measured — `k18_match_bool_of_cmp`
        // (`match a == b { true => a, false => b }`), admitted-and-wrong on `main` with every gate
        // layer green, and wrong in every driver back to the control.
        //
        // Built ends a MATCH SCRUTINEE's temporary scope AT THE SCRUTINEE EXPRESSION, so it retires
        // the comparison's operand temps in the HEAD block:
        //     bb0: … _3 = Eq(move _4, move _5); StorageDead(_5); StorageDead(_4); switchInt(_3)
        // It ends an `if` CONDITION's scope ON EACH OUTGOING EDGE, so it retires them at the ENTRY
        // OF BOTH ARMS — which is what lane K's emitter reproduces. The two spellings lower to
        // BYTE-IDENTICAL trust-ir, and `mf_defer_deads` asks a trust-ir question ("does this
        // instruction define the block's `CondBr` condition?") that cannot tell them apart. The
        // SOURCE is the only place the distinction exists, so this is where it is made.
        //
        // REFUSAL, NOT REPAIR, and the price is measured rather than assumed: a refused body keeps
        // today's marker-free form (`markers_exact: false`, no `-O` flip) instead of a marker
        // sequence that disagrees with built's, and it stays `agreed`, so it keeps its `-O0` flip.
        // Emitting correctly would need a per-`CondBr` HIR↔trust-ir attribution that no structure
        // in this shim provides.
        //
        // TIGHT ON PURPOSE, and the admitted sibling is what proves it. `match c { true => x,
        // false => y }` on a BARE PARAMETER mints no temp on either side, is `markers_exact: true`
        // and flipping today, and stays admitted — `hir_tail_is_marker_free` is exactly the
        // predicate that separates the two. Every `if <cmp>` body has no `Match` node at all and is
        // untouched.
        if let rustc_hir::ExprKind::Match(scrutinee, _, _) = ex.kind {
            if !hir_tail_is_marker_free(self.typeck, scrutinee) {
                self.ok = false;
                return;
            }
        }
        if let rustc_hir::ExprKind::Struct(_, fields, tail) = ex.kind {
            if !matches!(tail, rustc_hir::StructTailExpr::None) {
                self.ok = false;
                return;
            }
            let Some(ty) = self.typeck.expr_ty_opt(ex) else {
                self.ok = false;
                return;
            };
            let ty::Adt(adt, _) = ty.kind() else {
                self.ok = false;
                return;
            };
            if !adt.is_struct() {
                self.ok = false;
                return;
            }
            let variant = adt.non_enum_variant();
            let mut prev: Option<usize> = None;
            let mut in_declaration_order = true;
            // Trust (lane MF-ZERO-3): the DECLARED index of each written field, in written order.
            // `permutation_is_observable` needs it — a `*p` field's shim temp is minted at its
            // `Inst::Load`, before the aggregate, so whether the permutation survives depends on
            // WHICH field it is, not only on its type.
            let mut idxs: Vec<usize> = Vec::with_capacity(fields.len());
            for f in fields {
                let Some(idx) = variant.fields.iter().position(|fd| fd.name == f.ident.name) else {
                    self.ok = false;
                    return;
                };
                if prev.is_some_and(|p| p >= idx) {
                    in_declaration_order = false;
                }
                prev = Some(idx);
                idxs.push(idx);
            }
            // Trust (lane MF-ZERO-2, 2026-08-13): REFUSE ONLY WHAT IS DISTINGUISHABLE. The clause
            // above used to refuse EVERY out-of-declaration-order literal; measured, that refused
            // strictly more than its own argument covers — see [`permutation_is_observable`].
            if !in_declaration_order && permutation_is_observable(self.typeck, fields, &idxs) {
                self.ok = false;
                return;
            }
        }
        rustc_hir::intravisit::walk_expr(self, ex);
    }
}

/// Trust (lane MF-ZERO-2, 2026-08-13): can the MARKER CHANNEL see this struct literal's written
/// field order at all?
///
/// The order matters because built and this shim mint the explicit fields' operand temps in
/// DIFFERENT orders — built in SOURCE order (`as_rvalue`'s `ExprKind::Adt` arm evaluates the
/// written fields "in order given by user"), the shim at the aggregate site in FIELD order. But
/// the channel that decides `markers_exact` is `mir_differential::canon_markers`, which renames
/// locals BY FIRST APPEARANCE and carries only the TYPE. A permutation is therefore observable
/// only through the sequence of temp TYPES and statement INDICES — never through the identity of
/// the local, which canonicalisation erases.
///
/// So this returns `false` — the permutation is invisible, admit it — exactly when every written
/// field is one of:
///
///   * a `Category::Constant` value. `as_operand` folds it (`!expr.ty.needs_drop()` holds for the
///     scalar fields `agg_field_order_ok` admits) and the producer emits an `Inst::Const` the shim
///     folds too, so NEITHER side mints a temp and the field takes no position in either order;
///   * a `Category::Place` value, provided the sequence of place TYPES after constants are removed
///     is the same in source order and declaration order. Built emits one pair per such field in
///     source order; the shim emits it in field order. Canonicalisation renames locals by first
///     appearance, so equality of those type sequences (not equality of every element to one
///     common type) is the observable boundary.
///
/// MEASURED, and this is why the clause is narrowed rather than merely documented: the
/// unconditional refusal cost SEVEN flips that were `markers_exact: true` and `agreed` before it
/// — `f10_acb`, `f11_bac`, `f12_bca`, `f13_cab`, `f14_cba`, `f25_rotate_written_cba` (all
/// `T3 { a: u32, b: u32, c: u32 }`) and `g06_const_last_written` (`T3 { a: x, c: z, b: 7 }`) — in
/// the review corpus `probes/rmfz_adversarial.rs`. Their derived sequences are not merely
/// plausible, they are EQUAL to built's; the control reports `6 marker line(s) identical`.
///
/// Everything else is observable and stays refused, including every mixed-width permutation the
/// clause was written for (`MixedT { b: y, a: x }` — `u8` then `u64` in built, `u64` then `u8`
/// derived — `g14_bools_reverse`, `w10_acb`..`w14_cba`, `w24`, `w25`, `w34`):
///
///   * place-valued fields whose TYPE sequence actually changes under the permutation;
///   * a field whose value COMPUTES (`Category::Rvalue`, e.g. `g15`'s `f0: a == b`): built builds
///     it into its own temp at its SOURCE position while the shim mints it at its instruction, so
///     the statement INDICES move and not only the types;
///   * anything this function cannot classify (an adjusted/coerced field expression, an index, a
///     static, a call): FAIL-CLOSED to observable, i.e. refuse.
///
/// THE `*p` FIELD — NARROWED 2026-08-13 (lane MF-ZERO-3), AND THIS IS THE SECOND HALF OF THE THIRD
/// REVIEW'S FINDING. Until now this clause read: a `*p` deref field is `Category::Place` for built
/// (one temp, at the aggregate) but an `Inst::Load` for the shim (a statement of its own, BEFORE
/// the aggregate), "so the indices move here too". The premises are true; **the conclusion is not
/// always**, and the review produced two witnesses — `mfr3_perm::v03_deref_field_out_of_order`
/// (`E3 { c: z, b: y, a: *p }`) and `v09_deref_and_place_mixed` (`E3 { b: y, a: *p, c: y }`) — that
/// this clause REFUSED while their control derived sequence was `6 marker line(s) identical`,
/// character for character. Two flips, lost to a clause over-broad by its own argument.
///
/// WHY, AND EXACTLY HOW FAR IT GOES. `canon_markers` renames locals BY FIRST APPEARANCE, so each
/// side's `StorageDead` sequence is the reverse of ITS OWN live order — provided that side retires
/// in the reverse of the order it lived in. Built does: it lives the fields in SOURCE order and
/// retires in reverse source order, so its dead run is always `n-1 … 0`. The shim lives a LOAD at
/// its instruction (before the aggregate) and every other place field at the aggregate in FIELD
/// order, but retires in reverse FIELD order — so the shim's dead run is `n-1 … 0` only when its
/// live order IS the field order, i.e. when the loads occupy a prefix of the field order in field
/// order. With ONE deref field AT INDEX 0 that holds by construction. With two it does not, and
/// this is measured, not conjectured: `mfz2_residual::p50_deref_field_permuted`
/// (`P2 { r: *q, l: *p }`) reports `line 2: built mk b0.3:dead s1:u32 vs derived mk b0.3:dead
/// s0:u32` — the LIVE lines agree and the DEADS are transposed. So the clause admits exactly:
///
///   * every non-constant field is a place, or a single `*p` whose DECLARED index is 0;
///   * on that deref-asymmetric path, all of them carry the same type. With no deref, the exact
///     source-vs-declaration type-sequence comparison above applies instead.
///
/// Every mixed-width witness the clause was originally written for (`MixedT { b: y, a: x }`,
/// `g14_bools_reverse`, `w10_acb`..`w14_cba`) is unaffected, and `p50` stays refused.
///
/// `v04_deref_field_in_order` — the same field set in declaration order, which this function is
/// never even asked about — is `right` in both drivers, which is the independent evidence that the
/// operand plan reproduces this shape exactly: source order is invisible to
/// `plan_operand_marker_temps`, so admitting the permuted spelling cannot make it emit anything
/// different.
///
/// `idxs` is the DECLARED index of each written field, in written order, as the caller computed it.
fn permutation_is_observable<'tcx>(
    typeck: &'tcx ty::TypeckResults<'tcx>,
    fields: &'tcx [rustc_hir::ExprField<'tcx>],
    idxs: &[usize],
) -> bool {
    if idxs.len() != fields.len() {
        return true;
    }
    let mut places: Vec<(usize, RustcTy<'tcx>)> = Vec::new();
    let mut derefs = 0usize;
    for (f, idx) in fields.iter().zip(idxs.iter().copied()) {
        // A `*p` field is `Other` to `hir_operand_class` — correctly, because in an AGGREGATE
        // FIELD position the shim mints an `Inst::Load` statement of its own where built mints
        // none. It is nevertheless a one-pair-one-type field on both sides, and when it is the
        // FIRST declared field it also lives first on both sides, so it joins the same-type test
        // rather than refusing outright.
        let is_deref_place =
            matches!(f.expr.kind, rustc_hir::ExprKind::Unary(rustc_hir::UnOp::Deref, _))
                && hir_place_is_marker_free(typeck, f.expr);
        let class = if is_deref_place {
            derefs += 1;
            if derefs > 1 || idx != 0 {
                return true;
            }
            HirOperandClass::Place
        } else {
            hir_operand_class(typeck, f.expr)
        };
        match class {
            HirOperandClass::Konst => {}
            HirOperandClass::Place => {
                let Some(t) = typeck.expr_ty_opt(f.expr) else { return true };
                places.push((idx, t));
            }
            HirOperandClass::Other => return true,
        }
    }
    if derefs != 0 {
        // A deref result is lived at its producer instruction while the other fields are lived at
        // the aggregate. Retain the measured, deliberately narrower rule for that asymmetric
        // path: one deref, declared first, and one canonical type — including place fields that
        // appeared before the deref in source order.
        return places.first().is_none_or(|(_, first)| places.iter().any(|(_, ty)| ty != first));
    }

    // With no producer-side deref instruction, constants disappear from BOTH marker streams.
    // Built's remaining type sequence is source order (`places`); the shim's is declaration
    // order. Canonical marker local identities are assigned by first appearance and the dead run
    // reverses that same order on both sides, so equality of these two type sequences is the exact
    // observable boundary. Requiring every place to have one type was sufficient but not
    // necessary: `E4 { b: 1, a, d: 2, c }` has source and declaration sequences `[u32, u64]` and
    // is therefore invisible even though its two place fields differ in type.
    !marker_type_sequence_is_preserved(&places)
}

/// Does deleting marker-free constants and reordering the remaining fields into declaration order
/// preserve the marker type sequence? Kept pure so the exact observability boundary has direct
/// regression tests independent of HIR construction.
fn marker_type_sequence_is_preserved<T: Copy + Eq>(source: &[(usize, T)]) -> bool {
    let source_types: Vec<_> = source.iter().map(|(_, ty)| *ty).collect();
    let mut declaration = source.to_vec();
    declaration.sort_by_key(|(idx, _)| *idx);
    source_types == declaration.iter().map(|(_, ty)| *ty).collect::<Vec<_>>()
}

/// The three-way split [`permutation_is_observable`] needs, in built's own vocabulary
/// (`rustc_mir_build`'s `Category::of`), restricted to the forms whose SHIM emission is also
/// known. Anything else is `Other`, which is always the refusing answer.
enum HirOperandClass {
    /// `Category::Constant`: folded by `as_operand` and by the shim; mints nothing on either side.
    Konst,
    /// `Category::Place` AND folded by the shim into a MIR place with NO statement of its own —
    /// a local binding (an argument local) or a chain of field projections off one. Built mints
    /// `StorageLive(t); t = copy <place>` at the consumer; so does the shim.
    Place,
    /// Not classified. `*p` (a shim `Inst::Load` statement), an index, a static, a call, an
    /// operator, and any expression carrying an adjustment all land here.
    Other,
}

fn hir_operand_class<'tcx>(
    typeck: &'tcx ty::TypeckResults<'tcx>,
    ex: &'tcx rustc_hir::Expr<'tcx>,
) -> HirOperandClass {
    // An adjustment (auto-deref, unsize, a coercion) makes built emit statements this function
    // has not accounted for. Fail closed before looking at the syntax.
    if !typeck.expr_adjustments(ex).is_empty() {
        return HirOperandClass::Other;
    }
    match ex.kind {
        rustc_hir::ExprKind::Lit(_) => HirOperandClass::Konst,
        rustc_hir::ExprKind::Unary(rustc_hir::UnOp::Neg, inner)
            if matches!(inner.kind, rustc_hir::ExprKind::Lit(_)) =>
        {
            HirOperandClass::Konst
        }
        rustc_hir::ExprKind::Path(ref qpath) => match typeck.qpath_res(qpath, ex.hir_id) {
            rustc_hir::def::Res::Local(_) => HirOperandClass::Place,
            rustc_hir::def::Res::Def(
                DefKind::Const { .. } | DefKind::AssocConst { .. } | DefKind::ConstParam,
                _,
            ) => HirOperandClass::Konst,
            _ => HirOperandClass::Other,
        },
        rustc_hir::ExprKind::Field(base, _) => match hir_operand_class(typeck, base) {
            HirOperandClass::Place => HirOperandClass::Place,
            _ => HirOperandClass::Other,
        },
        _ => HirOperandClass::Other,
    }
}

/// Trust (lane MF-ZERO-3, 2026-08-13): THE FIELD-WRITE MARKER PLAN — the answer the ungated
/// `recognize_field_write` arm never asked for.
///
/// Returns `Some` exactly when **the body's field writes are the only constructs in it that mint a
/// marker on either side**, so that emitting the wave-24b pair per place-valued write makes the two
/// whole-body marker sequences EQUAL. Returns `None` — and then the arm emits its already-measured
/// marker-free single assign — for everything else.
///
/// This is a claim about the body, which is the whole difference from round 2. Round 2 asked "does
/// built give THIS write's right-hand side a temp?" and answered it correctly; the third review
/// then measured seventeen bodies where the answer was still yes and the body's sequence was still
/// wrong, because something ELSE in the body minted a built marker the shim does not reproduce: a
/// branch around the write (built hoists the condition's temp into the head block — eight of the
/// seventeen), a `let` (a named binding local with its own pair — two), a tail expression that
/// mints operand temps (`w.a = v; a == b` — five, all of them derived-prefix PARTIALs), a
/// destructuring parameter (a binding local, again — two), a shift (two).
///
/// THE GRAMMAR, and why each clause is exactly one of those failures:
///
/// 1. **Every parameter is a simple by-value binding or `_`.** `args_and_body` reuses the argument
///    local only for `PatKind::Binding(ByRef::No, .., None)`; every other pattern goes through
///    `declare_bindings` + `place_into_pattern` and mints a NAMED BINDING LOCAL with its own
///    `StorageLive`/`StorageDead`. Same rule, same reason, as [`source_form_admits`]'s rule 1
///    (`w18_ref_pattern_and_place_rhs`, `w20_struct_pattern_and_write`).
/// 2. **The outer body is a plain block.** Two measured tail wrappers are supported explicitly:
///    a sole direct write inside an ordinary or `unsafe` block. `unsafe` is checking mode, not a
///    marker-producing lowering operation; arbitrary nested control remains outside the plan.
/// 3. **Every ordinary statement is a `;`-terminated ASSIGNMENT** whose left-hand side is a place built
///    lowers with `as_place` and no temp (a field/deref/local chain, [`hir_place_is_marker_free`])
///    and whose right-hand side is `Category::Constant` or `Category::Place`
///    ([`hir_operand_class`]). A `let` is refused HERE, by name, rather than by the scope firewall
///    that never sees this arm (`w11`, `w12`, `w13`). An `Rvalue` right-hand side is refused
///    because built marks its own operand at an index this shim has already spent materialising
///    the instruction (`m19_write_cast_of_param` and its family are `refused` today, and stay
///    refused: the arm's own `rhs_is_place` declines them and now the plan does too).
///    A final `return <marker-free value>;` is also supported: it terminates the straight-line
///    body without minting an operand temp. A return followed by another expression is refused.
/// 4. **A tail expression, if there is one, mints no marker** ([`hir_tail_is_marker_free`]).
///    `expr_into_dest` assigns a `Category::Place` expression straight into the destination with
///    `as_place` — measured: `w16_write_then_load_tail` (`w.a = v; *p`) is `2 marker line(s)
///    identical`, the write's pair and nothing else — while an operator tail mints operand temps
///    (`w14`, `w15`, `w17`, `w24`). The exact `loop { break; }` tail and a statement-free unsafe
///    block are marker-free and are recognized by name; wider loop/control grammars are not.
/// 5. **At least one supported assignment exists**, either directly in the outer block or as the
///    sole statement of the measured wrapper. A write-free body is the operand plan's business,
///    and the two are exclusive (see the resolution site in `lower_ir_to_mir`).
///
/// There is no branch clause because there is no conditional branch: clause 3 admits assignments
/// and one terminal return, while clause 4 admits only marker-free tails and the exact one-trip
/// `loop { break; }`. An `if`/`match` anywhere still falls out of the grammar (`w03`..`w10`,
/// `w25`).
///
/// FAIL-CLOSED EVERYWHERE: no HIR body, a non-local typeck root, an unclassifiable expression and
/// the parse-error tail all return `None`, and `None` only ever REMOVES derived markers.
///
/// NESTED BODIES ARE NOT WALKED. A closure is its own `LocalDefId` with its own trust-ir
/// `Function` and the shim asks this plan again when it lowers it — which is how
/// `w22_closure_ref_pattern_writes::{closure#0}` is refused on its OWN parameter pattern.
fn plan_field_write_markers<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId) -> Option<MfWritePlan> {
    let body = tcx.hir_maybe_body_owned_by(def)?;
    if !hir_params_are_simple_bindings(body) {
        return None;
    }
    let root = tcx.typeck_root_def_id(def.to_def_id()).as_local()?;
    let typeck = tcx.typeck(root);
    let rustc_hir::ExprKind::Block(blk, None) = body.value.kind else {
        return None;
    };
    if !matches!(blk.rules, rustc_hir::BlockCheckMode::DefaultBlock) {
        return None;
    }
    let mut writes = 0usize;
    let mut marking_writes = 0usize;
    let mut returned = false;
    for st in blk.stmts {
        let ex = match st.kind {
            // An ITEM statement declares a separate def and emits nothing into this body.
            rustc_hir::StmtKind::Item(_) => continue,
            rustc_hir::StmtKind::Semi(e) => e,
            // `let` (a binding local) and a non-`;` expression statement are both refusals.
            rustc_hir::StmtKind::Let(_) | rustc_hir::StmtKind::Expr(_) => return None,
        };
        if returned {
            // No source expression may follow the terminal return. This keeps the admitted form
            // exactly the measured straight-line `write; return <marker-free value>;` grammar.
            return None;
        }
        if let Some(marking) = classify_field_write(typeck, ex) {
            writes += 1;
            marking_writes += usize::from(marking);
            continue;
        }
        if let rustc_hir::ExprKind::Ret(value) = ex.kind {
            if !typeck.expr_adjustments(ex).is_empty()
                || value.is_some_and(|value| !hir_tail_is_marker_free(typeck, value))
            {
                return None;
            }
            returned = true;
            continue;
        }
        return None;
    }
    // The TAIL must mint nothing (clause 4) — INCLUDING when it is itself an assignment.
    //
    // MEASURED, and this is the body this lane's own corpus caught before anyone else could.
    // `{ w.a = v }` and `{ w.a = v; }` are the same PROGRAM and are NOT the same marker sequence:
    // in the tail spelling built's `StorageDead` sits one statement LATER (`probes/mfz3_gate.rs`:
    // `t01_tail_assign_place` reports `line 1: built mk b0.3:dead s0:u32 vs derived mk b0.2:dead
    // s0:u32` — the lives agree, the dead moves), because the tail is an expression whose value
    // built assigns into the return place. The plan's first draft counted a tail assignment as
    // just another write, on the argument that the two spellings are the same program; that
    // argument is exactly the kind that produced the previous two rounds' residuals, and the
    // corpus refuted it. A tail assignment mints a marker at an index this plan has not modelled,
    // so it is refused like any other marker-minting tail.
    if returned && blk.expr.is_some() {
        return None;
    }
    if let Some(tail) = blk.expr {
        if !hir_tail_is_marker_free(typeck, tail) {
            // The two measured wrapper forms (`{ w.a = v; }` and
            // `unsafe { w.a = v; }`) carry one direct write and nothing else. Count that write in
            // the SOURCE plan instead of weakening the gate at the emission site. Keeping this to
            // a sole wrapped write avoids silently admitting arbitrary nested statement/control
            // grammars that have not been measured.
            if writes != 0 {
                return None;
            }
            marking_writes += usize::from(plan_single_wrapped_field_write(typeck, tail)?);
            writes = 1;
        }
    }
    if writes == 0 {
        return None;
    }
    Some(MfWritePlan { marking_writes })
}

/// Classify one direct assignment in the field-write plan. `Some(true)` means built and the shim
/// each mint one operand-temp pair; `Some(false)` means both fold the constant and mint none.
fn classify_field_write<'tcx>(
    typeck: &'tcx ty::TypeckResults<'tcx>,
    ex: &'tcx rustc_hir::Expr<'tcx>,
) -> Option<bool> {
    let rustc_hir::ExprKind::Assign(lhs, rhs, _) = ex.kind else {
        return None;
    };
    if !hir_place_is_marker_free(typeck, lhs) {
        return None;
    }
    match hir_operand_class(typeck, rhs) {
        HirOperandClass::Konst => Some(false),
        HirOperandClass::Place => Some(true),
        HirOperandClass::Other => None,
    }
}

/// The measured marker-bearing wrapper extension: an unlabelled ordinary or unsafe block whose
/// only non-item statement is one semicolon-terminated supported field write and whose tail is
/// absent. Returns whether that write mints a marker pair.
fn plan_single_wrapped_field_write<'tcx>(
    typeck: &'tcx ty::TypeckResults<'tcx>,
    ex: &'tcx rustc_hir::Expr<'tcx>,
) -> Option<bool> {
    if !typeck.expr_adjustments(ex).is_empty() {
        return None;
    }
    let rustc_hir::ExprKind::Block(blk, None) = ex.kind else {
        return None;
    };
    if !matches!(
        blk.rules,
        rustc_hir::BlockCheckMode::DefaultBlock | rustc_hir::BlockCheckMode::UnsafeBlock(_)
    ) || blk.expr.is_some()
    {
        return None;
    }
    let mut write = None;
    for st in blk.stmts {
        match st.kind {
            rustc_hir::StmtKind::Item(_) => {}
            rustc_hir::StmtKind::Semi(ex) if write.is_none() => {
                write = Some(classify_field_write(typeck, ex)?);
            }
            rustc_hir::StmtKind::Semi(_)
            | rustc_hir::StmtKind::Let(_)
            | rustc_hir::StmtKind::Expr(_) => return None,
        }
    }
    write
}

/// Trust (lane MF-ZERO-3): what the field-write plan promises, in the one number the body-end
/// balance check can compare against reality.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct MfWritePlan {
    /// How many of the body's writes built gives an operand temp — the `Category::Place`
    /// right-hand sides, counted from the SOURCE. `lower_ir_to_mir` fails the body CLOSED unless
    /// the `recognize_field_write` arm emitted exactly this many pairs, so "the plan sanctioned
    /// these markers" is verified per body rather than argued.
    marking_writes: usize,
}

/// Is the body still available to the source-form operand/branch marker plans?
///
/// Every marker plan describes the whole body, so the general source-form lane may run only when
/// neither specialized plan owns it. Keeping this as one predicate makes the field-write and
/// interior-borrow exclusions mechanically inseparable at the call site.
fn source_form_marker_plan_available(
    write_plan: Option<MfWritePlan>,
    borrow_plan: bool,
    source_admits: bool,
) -> bool {
    write_plan.is_none() && !borrow_plan && source_admits
}

/// Trust (lane MF-ZERO-3): THE INTERIOR-BORROW MARKER PLAN — the second ungated site.
///
/// Wave-29b reproduces built's `StorageLive(_2); _2 = &((*_1).K); _0 = &(*_2); StorageDead(_2)`
/// for an offset-0 interior-borrow return. Like the field-write arm it emitted that pair with no
/// plan's permission; unlike it, no body in any corpus has yet been measured wrong through it —
/// which is exactly the argument the field-write arm had before somebody wrote
/// `probes/mfr3_wclass.rs`. It is brought under the same gate rather than left to be the next
/// review's finding.
///
/// Admits a body whose entire value is a single `&<place>` — no statements to mint anything, a
/// marker-free borrowed place, and simple parameters — so the reborrow temp's pair IS the body's
/// whole marker sequence (measured: `rmfz_borrow4::r03_borrow_last`, `2 marker line(s)
/// identical`). Anything else gets the direct `_0 = &((*_1).K)` form, which carries no marker and
/// which is the shape wave-29 shipped before wave-29b.
fn plan_interior_borrow_markers<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId) -> bool {
    let Some(body) = tcx.hir_maybe_body_owned_by(def) else {
        return false;
    };
    if !hir_params_are_simple_bindings(body) {
        return false;
    }
    let Some(root) = tcx.typeck_root_def_id(def.to_def_id()).as_local() else {
        return false;
    };
    let typeck = tcx.typeck(root);
    let rustc_hir::ExprKind::Block(blk, None) = body.value.kind else {
        return false;
    };
    if !matches!(blk.rules, rustc_hir::BlockCheckMode::DefaultBlock) {
        return false;
    }
    if blk.stmts.iter().any(|s| !matches!(s.kind, rustc_hir::StmtKind::Item(_))) {
        return false;
    }
    let Some(tail) = blk.expr else {
        return false;
    };
    let rustc_hir::ExprKind::AddrOf(rustc_hir::BorrowKind::Ref, _, inner) = tail.kind else {
        return false;
    };
    // THE REBORROW IS REQUIRED, NOT MERELY TOLERATED, and this is measured. `&s.h` returned from
    // `fn r03_borrow_last(s: &Slot) -> &u64` carries the adjustment pair
    // `[Deref(Builtin), Borrow(Ref(Not))]` — rustc auto-derefs the `&u64` it just made and
    // re-borrows it — and that pair IS wave-29b's second statement: built spells the body
    // `StorageLive(_2); _2 = &((*_1).K); _0 = &(*_2); StorageDead(_2)`, the temp existing precisely
    // because of the reborrow. A tail WITHOUT it is assigned straight into the return place with no
    // temp and no marker, and emitting the reborrow form there would put two markers where built
    // has none — so an empty adjustment list is a refusal here, not a licence.
    let adjustments = typeck.expr_adjustments(tail);
    let reborrow = matches!(
        adjustments,
        [a, b]
            if matches!(a.kind, ty::adjustment::Adjust::Deref(ty::adjustment::DerefAdjustKind::Builtin))
                && matches!(
                    b.kind,
                    ty::adjustment::Adjust::Borrow(ty::adjustment::AutoBorrow::Ref(
                        ty::adjustment::AutoBorrowMutability::Not
                    ))
                )
    );
    reborrow && hir_place_is_marker_free(typeck, inner)
}

/// Trust (wave-CK, 2026-08-17): what the CHECKED-ARITHMETIC-CHAIN marker plan owns — the chain
/// links, in SSA order, with the producer's own type annotation for each.
///
/// The LAST entry is the returned value and takes no temp (built writes the outermost expression
/// straight into `_0`); every earlier entry is one of built's `as_operand` -> `as_temp` operand
/// temps and carries exactly one marker pair.
#[derive(Clone, Debug, PartialEq, Eq)]
struct MfCheckedPlan {
    /// `(result value, the producer's result type)` for each `Inst::Overflow` unit of the chain,
    /// in SSA order. Length >= 2 by construction, so `chain[..len-1]` is non-empty.
    chain: Vec<(ValueId, Ty)>,
}

impl MfCheckedPlan {
    /// The links that carry a marker pair: every one but the returned tail.
    fn marked(&self) -> &[(ValueId, Ty)] {
        // Total: a chain shorter than the plan's own `>= 2` guarantee marks nothing rather than
        // panicking on an empty slice — the fail-closed direction.
        self.chain.split_last().map_or(&[][..], |(_, rest)| rest)
    }

    /// Does built materialise a marker-carrying temp for `r`?
    fn marks(&self, r: ValueId) -> bool {
        self.marked().iter().any(|(v, _)| *v == r)
    }

    /// The chain link evaluated immediately BEFORE `r`, i.e. the operand temp whose retirement
    /// built schedules after `r`'s own destination write. `None` for the first link (nothing
    /// precedes it) and for a value outside the chain.
    fn pred(&self, r: ValueId) -> Option<ValueId> {
        let k = self.chain.iter().position(|(v, _)| *v == r)?;
        if k == 0 { None } else { Some(self.chain[k - 1].0) }
    }
}

/// Trust (wave-CK, 2026-08-17): the producer's canonical checked-arithmetic idiom, recognized as
/// ONE unit — `Overflow` + `Const(false)` + `Const(true)` + `Select(overflowed ? false : true)` +
/// `Assert(ok)`.
///
/// The `Inst::Overflow` emitter arm already recognizes exactly this shape inline before it emits
/// anything; this is that recognizer, lifted so the PLAN and the SEQUENCE MODEL decide from the
/// same five nodes the emitter does. Duplicating the pattern in three places is how a plan and an
/// emitter drift apart, and a drifted plan is a marker sequence that is not built's.
///
/// Returns `(result, overflowed, ty, lhs, rhs)`; the unit is always exactly five nodes.
fn checked_unit(
    nodes: &[InstrNode],
    i: usize,
) -> Option<(ValueId, ValueId, Ty, ValueId, ValueId)> {
    let n0 = nodes.get(i)?;
    let Inst::Overflow { ty, lhs, rhs, .. } = &n0.inst else { return None };
    let (&res, &of) = match n0.results.as_slice() {
        [r, o] => (r, o),
        _ => return None,
    };
    let fc = match &nodes.get(i + 1)?.inst {
        Inst::Const { ty: Ty::Bool, value: Constant::Bool(false) } => {
            *nodes[i + 1].results.first()?
        }
        _ => return None,
    };
    let tc = match &nodes.get(i + 2)?.inst {
        Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) } => {
            *nodes[i + 2].results.first()?
        }
        _ => return None,
    };
    let ok = match &nodes.get(i + 3)?.inst {
        Inst::Select { ty: Ty::Bool, cond, then_val, else_val }
            if *cond == of && *then_val == fc && *else_val == tc =>
        {
            *nodes[i + 3].results.first()?
        }
        _ => return None,
    };
    match &nodes.get(i + 4)?.inst {
        Inst::Assert { cond } if *cond == ok => {}
        _ => return None,
    }
    Some((res, of, ty.clone(), *lhs, *rhs))
}

/// Trust (wave-CK, 2026-08-17): **THE CHECKED-ARITHMETIC-CHAIN MARKER PLAN** — the sixth
/// whole-body plan, and the one that closes the CTFE half of this crate's marker residual.
///
/// # The residual this exists for, measured
///
/// At `9d8dd0dcfe` (wave-EP merged) `clean-kernel`'s 13,774 bodies flip 180 codegen + 32 CTFE at
/// `-O3` and 192 + 42 at `-O0`. The `-O3` set is a strict SUBSET of the `-O0` one (0 bodies flip
/// only at `-O3`), so the difference — 12 codegen + 10 CTFE rows — is exactly the population whose
/// ONLY failing criterion is `markers_exact`, which is a gate at `-O` and not at `-O0`. Nine of
/// those ten CTFE rows are ONE shape:
///
/// ```text
/// const MAX_BUNDLE_ENV_BYTES: usize = 256 * 1024 * 1024;
/// ```
///
/// and its eight siblings (`cert::compression::limits::MAX_*`, two
/// `decode_bincode_with_limits::{closure#0}::{constant#N}`). Every one reads
/// `markers differ: line 0: built ``mk b0.0:live s0:usize`` vs derived ``<end>``` — an ABSENCE:
/// built mints an operand temp this shim never materialised.
///
/// # What built does, measured
///
/// `-Zdump-mir=all` on `const A: usize = 256 * 1024 * 1024`:
///
/// ```text
/// bb0: { StorageLive(_1);
///        _2 = MulWithOverflow(const 256_usize, const 1024_usize);
///        assert(!move (_2.1), ...) -> [success: bb1, unwind unreachable]; }
/// bb1: { _1 = move (_2.0);
///        _3 = MulWithOverflow(move _1, const 1024_usize);
///        assert(!move (_3.1), ...) -> [success: bb2, unwind unreachable]; }
/// bb2: { _0 = move (_3.0); StorageDead(_1); return; }
/// ```
///
/// TWO MARKERS, ONE TEMP. `256 * 1024` is a `Binary` THIR expression, not a `Category::Constant`,
/// so `as_operand` sends it through `as_temp`: `StorageLive(_1)` goes in BEFORE the sub-expression
/// is built, and the retirement lands after the assign that writes the PARENT's destination — not
/// after the assign that consumes the temp, because the parent's `assert` splits the block in
/// between. The `(usize, bool)` tuple temps `_2`/`_3` come from `Builder::temp`, which schedules no
/// storage, and carry no markers; this is why the whole obligation is one pair per non-outermost
/// checked sub-expression.
///
/// # The class, and why each condition is load-bearing
///
///   * **`func.scopes.is_none()`** — wave-MF's firewall, first and unchanged. A source `let` mints
///     a named local with its own markers and a `FakeRead`, and nothing in the instruction stream
///     distinguishes it.
///   * **exactly one block** — the class is a constant expression evaluated in a straight line.
///
///     A trust-ir BLOCK PARAMETER used to be refused here too, on the argument that "a function
///     argument's built operand temp is minted at the CONSUMER and interleaves with these". **That
///     clause was measured over-broad and is narrowed** (LANE PCA, 2026-08-17): the chain clauses
///     below force every leaf to be a `Const`, so an admitted body cannot read a parameter and
///     there is nothing to interleave — nine measured bodies were refused for a hazard they do not
///     have. What a parameter CAN still do is mint a NAMED BINDING LOCAL when its pattern is not a
///     simple binding, and that is a marker; `ck_c3_pat_ref_mode` (`fn f(ref _a: usize) -> usize
///     { 256 * 1024 * 1024 }`) is admitted-and-wrong with the clause simply deleted. The question
///     is therefore asked of the SOURCE, at the seal site, by
///     [`checked_params_mint_no_local`].
///   * **every node is `Inst::Const` or part of a [`checked_unit`]** — the two shapes the model
///     below can place. `Const` mints no MIR statement (it folds into an operand); the unit mints
///     one assign and one block split. Anything else — a `Cast`, a bare `BinOp`, a div-check
///     idiom — is refused, because each has its own statement shape and admitting one on the
///     strength of the others is exactly the drift this plan is built to avoid. **This is what
///     declines `env::ext_instance::PRIORITY_BYTES`**, the tenth CTFE row: `(u64::BITS / 8) as
///     usize` is a div-check idiom plus a trailing cast, and the shim writes a cast through a temp
///     (`_t = Cast(..); _0 = copy _t`) where built writes `_0 = move _1 as usize` in one assign —
///     one extra assignment, so the retirement's canonical position differs. Reachable, and not by
///     widening this class.
///   * **the chain is LEFT-NESTED and LINEAR** — unit `k`'s left operand is unit `k-1`'s result and
///     its right operand is a constant; unit `0`'s operands are both constants. This is the shape
///     `a * b * c` has, and it is what makes built's live order the REVERSE of the SSA order:
///     `as_operand` opens the outermost sub-expression's temp first and recurses left. A
///     right-nested or DAG-shaped chain has a different live order and is refused rather than
///     guessed at (the same rule, for the same reason, as `plan_operand_marker_temps`' ordering
///     rules (1) and (2)).
///   * **>= 2 units, and the last unit's result is the returned value** — one unit is a body with
///     no non-outermost sub-expression and therefore no marker at all, which is the marker-free
///     form this shim already ships; and a returned value that is not the chain tail would leave a
///     link whose parent this model cannot name.
///   * **every unit result used exactly once** — built spells a TREE. A result used twice is a
///     producer CSE of something built evaluated (and marked) twice.
///
/// **NOT A RELAXATION.** Everything here only ADDS statements to the derived body — the marker
/// pair, and the `t = move (tup.0)` materialisation that built also emits. `canon_markers` is
/// untouched and still decides; a wrong plan yields a wrong sequence, `markers_exact: false` and no
/// flip, which is precisely the state all nine bodies are in today.
///
/// **NECESSARY, NOT SUFFICIENT**, exactly as every other plan here says of itself.
fn plan_checked_markers(func: &trust_ir::Function) -> Option<MfCheckedPlan> {
    // Wave-MF's firewall, first and unchanged.
    if func.scopes.is_some() {
        return None;
    }
    let [blk] = func.blocks.as_slice() else { return None };
    let (term, body) = blk.body.split_last()?;
    let ret = match &term.inst {
        Inst::Return { values } => match values.as_slice() {
            &[v] => v,
            _ => return None,
        },
        _ => return None,
    };
    // --- parse the node list into `Const` and checked units, in order ----------------------
    let mut consts: HashSet<ValueId> = HashSet::new();
    let mut chain: Vec<(ValueId, Ty)> = Vec::new();
    let mut ops: Vec<(ValueId, ValueId)> = Vec::new();
    let mut i = 0usize;
    while i < body.len() {
        // Trust (LANE PCA plan-clause audit, 2026-08-17): **`if !is_int(&ty) { return None }` IS
        // RETIRED HERE.** `checked_unit` matched an `Inst::Overflow`, and the producer mints
        // `Inst::Overflow` at exactly ONE site (`crates/trust-thir-lower/src/lib.rs`, the
        // `map_overflow_op` arm), under a guard whose type set is `{I8..I128, Isize, U8..U128,
        // Usize, Char}` — the SAME fourteen types `is_int` enumerates here
        // (`is_signed_int || is_unsigned_int`, and `Char` joins the unsigned side by v25 B1). The
        // clause could therefore never be the reason a body was refused. MEASURED: reached 458
        // times across a 2,002-body probe corpus and `clean-kernel`'s 13,774, fired ZERO; deleting
        // it moves 0 rows on either corpus.
        if let Some((res, of, ty, lhs, rhs)) = checked_unit(body, i) {
            chain.push((res, ty));
            ops.push((lhs, rhs));
            // The `overflowed` bit is consumed by the unit's own `Select` and nowhere else; the
            // recognizer proved that, and recording it keeps the use census below total.
            let _ = of;
            i += 5;
            continue;
        }
        match &body[i].inst {
            Inst::Const { .. } => {
                let &[r] = body[i].results.as_slice() else { return None };
                consts.insert(r);
                i += 1;
            }
            // Anything else — including an `Overflow` outside the canonical suffix — is out.
            _ => return None,
        }
    }
    if chain.len() < 2 {
        return None;
    }
    if chain.last().map(|(v, _)| *v) != Some(ret) {
        return None;
    }
    // --- left-nested, linear, single-use ----------------------------------------------------
    for (k, (lhs, rhs)) in ops.iter().enumerate() {
        if !consts.contains(rhs) {
            return None;
        }
        let ok_lhs = if k == 0 { consts.contains(lhs) } else { *lhs == chain[k - 1].0 };
        if !ok_lhs {
            return None;
        }
    }
    // Every unit result is used exactly once: by the next unit, or by the `Return`. `ops` already
    // pins the first n-1 to their successor, so what is left to refuse is a SECOND use.
    let mut uses: HashMap<ValueId, u32> = HashMap::new();
    for (lhs, rhs) in &ops {
        *uses.entry(*lhs).or_insert(0) += 1;
        *uses.entry(*rhs).or_insert(0) += 1;
    }
    *uses.entry(ret).or_insert(0) += 1;
    for (v, _) in &chain {
        if uses.get(v).copied() != Some(1) {
            return None;
        }
    }
    Some(MfCheckedPlan { chain })
}

/// Trust (wave-EP, 2026-08-16): what the ENUM-PAYLOAD-READ marker plan owns, in the two producer
/// block ids the emitter needs and nothing else.
///
/// Both fields are producer `BlockId`s, not MIR blocks: the plan is decided before a single MIR
/// block is filled, and the shim's one-MIR-block-per-trust-ir-block allocation is what carries them
/// across.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct MfPayloadPlan {
    /// The producer block whose `Const`/`GEP`/`Load` triple built lowers as an arm-binding
    /// BORROW — `StorageLive(t); t = &(((*P) as V).k); <consumer> = copy (*t); StorageDead(t)`.
    /// The plan's whole marker claim is that one pair, in that one block.
    arm: BlockId,
    /// The producer block whose incoming switch edge built routes through a `falseEdge` block.
    /// rustc's match lowering mints one such block per NON-LAST candidate, and the producer emits
    /// arm blocks in source order, so for the two-arm class this plan admits it is always the
    /// FIRST arm block — which is `func.blocks[1]`, the block right after the switch head.
    ///
    /// It is load-bearing for the same reason lane K's trampoline is: `canon_markers` walks the RAW
    /// CFG with no goto threading, so a derived body missing that block has every fine block index
    /// after it shifted and the channel refuses. MEASURED both ways on the two shipped bodies —
    /// `Reducibility::height` puts the payload arm FIRST (built's marker lands at fine index 2) and
    /// `SimpPriority::value` puts it SECOND (fine index 4); one empty trampoline on `func.blocks[1]`
    /// reproduces both.
    tramp: BlockId,
}

/// Trust (wave-EP, 2026-08-16): **THE ENUM-PAYLOAD-READ MARKER PLAN** — the fifth whole-body plan.
///
/// # What built does, measured
///
/// `env::types::Reducibility::height` (`clean-kernel`, `crates/clean-kernel/src/env/types.rs:70`),
/// built MIR in full, `-Zdump-mir=all` through the sealed driver:
///
/// ```text
/// fn height(_1: &Reducibility) -> u32 {
///     let mut _0: u32; let mut _2: isize; let _3: &u32;
///     bb0: { PlaceMention(_1); _2 = discriminant((*_1));
///            switchInt(move _2) -> [1: bb2, otherwise: bb1]; }
///     bb1: { _0 = const 0_u32; goto -> bb6; }
///     bb2: { falseEdge -> [real: bb5, imaginary: bb1]; }
///     bb5: { StorageLive(_3);
///            _3 = &(((*_1) as Regular).0: u32);
///            _0 = copy (*_3);
///            StorageDead(_3);
///            goto -> bb6; }
///     bb6: { return; }
/// }
/// ```
///
/// **Two markers, one temp, one arm block** — the smallest marker obligation in the residual, and
/// the whole of it. `PlaceMention` and `falseEdge` are not markers; bb0, bb1 and bb6 carry none.
/// Its twin `env::types::SimpPriority::value` (`types.rs:218`) is the same shape with the arms
/// swapped.
///
/// # What the shim did before this plan, and what changes
///
/// The T2b by-ref payload arm binds the producer's `Const`/`GEP`/`Load` triple straight to the
/// PLACE `((*P) as V).k` and mints no statement, so the arm block held ONE assign (the edge copy)
/// and no local of built's `&u32` type to mark. `markers_exact` read `built mk b2.0:live
/// s0:opaque:Ref { … Int { width: 32, signed: false } }` vs `derived <end>` — a refusal for ABSENCE
/// of evidence, which is what this plan supplies. Under the plan the arm emits built's own borrow
/// (`t = &(((*P) as V).k)`) and reads THROUGH it, which is the same two assignments built has, in
/// built's order, with built's declared type.
///
/// # The admitted class, and why each condition is load-bearing
///
/// This is a WHOLE-BODY grammar, deliberately narrow — it is one whole-body marker claim, and the
/// two bodies it is built for are the entire measured population of the shape.
///
///   * **`func.scopes.is_none()`** — wave-MF's firewall, consulted FIRST and unchanged. Measured:
///     neither target opens a producer `let` scope, so the instruction stream IS the whole story
///     for them; a body whose match arm binds through a `let` keeps today's marker-free form.
///   * **exactly four blocks: head, arm A, arm B, join** — the two-arm match. rustc mints one
///     `falseEdge` block per non-last candidate, so "how many trampolines and where" is only
///     answerable for a fixed arm count; three arms need two chained trampolines and are OUT.
///   * **the head is exactly `Load(enum) ; ExtractField 0 ; Switch`** with ONE case, a default,
///     and no edge args — the by-ref discriminant read the T2 arm lowers to
///     `_d = Discriminant((*P))`. Any other head is a different program.
///   * **exactly one arm carries the payload triple**, recognized by the SAME
///     [`recognize_ref_payload_read`] the emitter uses, at index 0 of its block, and its result is
///     the SOLE argument of that block's `Br` to the join. Built's `StorageDead` lands after the
///     assign that consumes the borrow; a second use, a use in another block, or a longer arg list
///     puts the retirement somewhere this plan does not model.
///   * **the other arm is exactly `Const ; Br(join, [that const])`** — a folded constant mints no
///     statement, so the arm holds no marker and cannot shift the trampoline's fine index.
///   * **the join takes exactly one parameter and immediately returns it.** A join that computes
///     anything is a body whose markers this plan has not measured.
///
/// **NOT A RELAXATION, and the property is wave-MF's.** Everything here only ADDS statements (and
/// one empty `Goto` block, which the semantic channel threads away — LEDGER L3) to the derived
/// body. `mir_differential::canon_markers` is untouched and still decides. A wrong plan yields a
/// wrong marker sequence, `markers_exact: false`, and no flip — precisely the state both bodies are
/// in today.
///
/// **STILL NECESSARY-NOT-SUFFICIENT**, exactly as [`plan_branch_markers`] says of itself: nothing
/// above establishes that an admitted body's derived marker sequence IS built's. The comparator
/// remains the authority.
fn plan_payload_markers(func: &trust_ir::Function) -> Option<MfPayloadPlan> {
    // Wave-MF's firewall, first and unchanged: any lexical `let` scope is out.
    if func.scopes.is_some() {
        return None;
    }
    let [head, arm_a, arm_b, join] = func.blocks.as_slice() else {
        return None;
    };
    if head.id != func.entry {
        return None;
    }
    // --- the head: the by-ref discriminant read, then a one-case switch ---------------------
    let [ld, ef, sw] = head.body.as_slice() else {
        return None;
    };
    if !matches!(ld.inst, Inst::Load { ty: Ty::Enum(_), volatile: false, align: None, .. }) {
        return None;
    }
    let agg = *ld.results.first()?;
    let Inst::ExtractField { aggregate, field: 0, .. } = &ef.inst else {
        return None;
    };
    if *aggregate != agg {
        return None;
    }
    let disc = *ef.results.first()?;
    let Inst::Switch { value, default, default_args, cases, .. } = &sw.inst else {
        return None;
    };
    if *value != disc || !default_args.is_empty() {
        return None;
    }
    let [case] = cases.as_slice() else {
        return None;
    };
    if !case.args.is_empty() {
        return None;
    }
    // The two arms are exactly the switch's two edges, in some order.
    let edges = [case.target, *default];
    if !(edges.contains(&arm_a.id) && edges.contains(&arm_b.id) && arm_a.id != arm_b.id) {
        return None;
    }
    // --- the arms: exactly one payload triple, exactly one folded constant ------------------
    let payload_arm = |blk: &trust_ir::Block| -> Option<()> {
        let (_off, _base, _ty, r) = recognize_ref_payload_read(&blk.body, 0)?;
        let [_, _, _, term] = blk.body.as_slice() else {
            return None;
        };
        let Inst::Br { target, args } = &term.inst else {
            return None;
        };
        (*target == join.id && args.as_slice() == [r]).then_some(())
    };
    let const_arm = |blk: &trust_ir::Block| -> Option<()> {
        let [c, term] = blk.body.as_slice() else {
            return None;
        };
        if !matches!(c.inst, Inst::Const { .. }) {
            return None;
        }
        let k = *c.results.first()?;
        let Inst::Br { target, args } = &term.inst else {
            return None;
        };
        (*target == join.id && args.as_slice() == [k]).then_some(())
    };
    let arm = match (
        payload_arm(arm_a).is_some(),
        const_arm(arm_b).is_some(),
        payload_arm(arm_b).is_some(),
        const_arm(arm_a).is_some(),
    ) {
        (true, true, false, false) => arm_a.id,
        (false, false, true, true) => arm_b.id,
        _ => return None,
    };
    // --- the join: one parameter, returned ---------------------------------------------------
    let [(jp, _)] = join.params.as_slice() else {
        return None;
    };
    let [ret] = join.body.as_slice() else {
        return None;
    };
    let Inst::Return { values } = &ret.inst else {
        return None;
    };
    if values.as_slice() != [*jp] {
        return None;
    }
    // The trampoline goes on the FIRST arm block's edge — the non-last candidate rustc gives a
    // `falseEdge` block. See [`MfPayloadPlan::tramp`].
    Some(MfPayloadPlan { arm, tramp: arm_a.id })
}

/// Trust (lane MF-ZERO-3): is this an assignment LEFT-HAND SIDE (or a borrowed place) that built
/// lowers with `as_place` and NO temp of its own?
///
/// A chain of field projections and derefs rooted at a local binding is: `as_place` walks it into
/// MIR place projections. An index (`a[i]` — a bounds `Assert` and an index temp), a static, a call
/// and an overloaded deref/index (a `Deref::deref` CALL) are not, and are refused by falling off
/// the match.
///
/// ADJUSTMENTS: only rustc's own BUILT-IN derefs are allowed through. `w.a = v` where `w: &mut C3`
/// carries an `Adjust::Deref(DerefAdjustKind::Builtin)` on `w` — a place projection, no statement —
/// while an OVERLOADED deref (`DerefAdjustKind::Overloaded`, a `DerefMut::deref_mut` CALL), a `Pin`
/// deref, and any borrow/unsize coercion emit statements this function has not accounted for. Hence
/// the split rather than [`hir_operand_class`]'s flat "any adjustment refuses": that flat rule would
/// refuse every field write through a reference, which is every field write this shim recognizes.
fn hir_place_is_marker_free<'tcx>(
    typeck: &'tcx ty::TypeckResults<'tcx>,
    ex: &'tcx rustc_hir::Expr<'tcx>,
) -> bool {
    if !typeck.expr_adjustments(ex).iter().all(|a| {
        matches!(a.kind, ty::adjustment::Adjust::Deref(ty::adjustment::DerefAdjustKind::Builtin))
    }) {
        return false;
    }
    match ex.kind {
        rustc_hir::ExprKind::Path(ref qpath) => {
            matches!(typeck.qpath_res(qpath, ex.hir_id), rustc_hir::def::Res::Local(_))
        }
        rustc_hir::ExprKind::Field(base, _) => hir_place_is_marker_free(typeck, base),
        rustc_hir::ExprKind::Unary(rustc_hir::UnOp::Deref, inner) => {
            hir_place_is_marker_free(typeck, inner)
        }
        _ => false,
    }
}

/// Trust (lane MF-ZERO-3): does built's `expr_into_dest` assign this body-tail expression into the
/// return place WITHOUT minting a temp?
///
/// `expr_into_dest` has an explicit `Category::Place` arm — `as_place` then a copy/move straight
/// into the destination — so a local, a field chain and a deref all cost nothing. A constant is
/// folded. Everything else (an operator, a comparison, a cast, a call, a struct literal, a
/// block, an `if`) either mints operand temps of its own or is a construct this function has not
/// modelled, and is refused.
///
/// MEASURED both ways on the third review's corpus: `w16_write_then_load_tail` (`w.a = v; *p`) is
/// `right`, `2 marker line(s) identical`; `w14_write_then_cmp_tail` (`w.a = v; a == b`) has built
/// `mk b0.2:live s1:u32` at line 2 where the shim has `<end>`, and is one of the five derived-
/// prefix PARTIALs this clause removes.
fn hir_tail_is_marker_free<'tcx>(
    typeck: &'tcx ty::TypeckResults<'tcx>,
    ex: &'tcx rustc_hir::Expr<'tcx>,
) -> bool {
    // The unit tail `()` — `expr_into_dest` writes `_0 = const ()` with no temp.
    if matches!(ex.kind, rustc_hir::ExprKind::Tup([])) {
        return typeck.expr_adjustments(ex).is_empty();
    }
    // A statement-free BARE BLOCK is transparent to the marker channel: `expr_into_dest` recurses
    // into its tail, and `unsafe` changes checking mode rather than lowering. Both the ordinary
    // `w.a = v; { r }` and the empty `w.a = v; unsafe {}` forms are independently measured with
    // exact marker streams. A block containing a write is counted separately by
    // `plan_single_wrapped_field_write`; any other statement remains a refusal.
    if let rustc_hir::ExprKind::Block(blk, None) = ex.kind {
        if !typeck.expr_adjustments(ex).is_empty()
            || !matches!(
                blk.rules,
                rustc_hir::BlockCheckMode::DefaultBlock | rustc_hir::BlockCheckMode::UnsafeBlock(_)
            )
            || blk.stmts.iter().any(|s| !matches!(s.kind, rustc_hir::StmtKind::Item(_)))
        {
            return false;
        }
        return match blk.expr {
            // A statement-free block with no tail IS the unit constant.
            None => true,
            Some(inner) => hir_tail_is_marker_free(typeck, inner),
        };
    }
    // The exact marker-free loop tail measured by MF-R4: `loop { break; }`. Pin the unlabeled
    // loop source, its sole unlabeled/unit break, and that break's resolved target. `while`, `for`,
    // labelled/nested breaks, break values, extra statements and loop tails all remain refused.
    if let rustc_hir::ExprKind::Loop(loop_block, None, rustc_hir::LoopSource::Loop, _) = ex.kind {
        if !typeck.expr_adjustments(ex).is_empty()
            || !matches!(loop_block.rules, rustc_hir::BlockCheckMode::DefaultBlock)
            || loop_block.expr.is_some()
        {
            return false;
        }
        let [stmt] = loop_block.stmts else { return false };
        let rustc_hir::StmtKind::Semi(break_expr) = stmt.kind else { return false };
        let rustc_hir::ExprKind::Break(destination, None) = break_expr.kind else { return false };
        return destination.label.is_none() && destination.target_id == Ok(ex.hir_id);
    }
    match hir_operand_class(typeck, ex) {
        HirOperandClass::Konst | HirOperandClass::Place => true,
        // `*p` is `Category::Place` for built and therefore free in a tail position, but
        // `hir_operand_class` deliberately calls it `Other` (in an AGGREGATE FIELD position the
        // shim mints an `Inst::Load` statement of its own, which moves the indices). The tail
        // position has no such asymmetry: the shim's load result feeds the `Return` directly.
        HirOperandClass::Other => hir_place_is_marker_free(typeck, ex),
    }
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
/// Trust (lane MF-R6): the aggregate-return recognition, as a PURE FUNCTION of the trust-ir and
/// the return type. Called once, and its result is bound immutably — see the call site for why
/// that matters to the marker gate.
///
/// Trust (wave-D, Drop-free aggregate constructor-return FLIP): recognize each struct-returning
/// body's InsertField chain and (in the Return arm) collapse it to a single `Rvalue::Aggregate`.
/// The seed `Const` + `InsertField` result ids are SKIPPED in the main loop (exactly like Alloca):
/// they are never bound in `cx.env`, so any OTHER use of one fails closed in `cx.operand`. Only
/// engaged when the return is a struct (`ret_rty` an Adt struct, gated Drop-free above); every
/// other body leaves both maps empty (zero overhead, byte-identical to the pre-wave-D path).
///
/// Trust (wave-L): the SAME InsertField-chain recognizer serves tuple returns — the producer emits
/// `const (A,B){0,0}` seed + `insertfield`s + `ret` for a tuple exactly as for a struct
/// (`recognize_agg_return_chain` matches `Constant::Aggregate` type-agnostically). Engage it when
/// the return is a struct OR a NON-empty tuple (the return-type gate above already restricted the
/// tuple to concrete all-scalar; unit `()` is `returns: []` → this arm is not reached).
fn agg_return_chains<'tcx>(
    func: &trust_ir::Function,
    ret_rty: RustcTy<'tcx>,
) -> (std::collections::HashSet<ValueId>, HashMap<ValueId, Vec<ValueId>>) {
    let mut skip_all: std::collections::HashSet<ValueId> = std::collections::HashSet::new();
    let mut chains: HashMap<ValueId, Vec<ValueId>> = HashMap::new();
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
                                skip_all.insert(s);
                            }
                            chains.insert(*v, field_vals);
                        }
                    }
                }
            }
        }
    }
    (skip_all, chains)
}

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
/// Trust (T2b, by-REF enum PAYLOAD read): recognize the triple the producer emits for a payload
/// binding under a ref-to-enum scrutinee —
/// `off = Const(i64 N)` / `g = GEP(i8, base, [off])` / `r = Load(scalar, g)` — returning
/// `(byte offset, base pointer, loaded ty, result)`.
///
/// This is the by-REF twin of the by-VALUE `extractfield %e, 1+k` payload read. The producer
/// chooses between them in `lower_enum_match_general`, whose payload bindings carry
/// `Option<byte-offset>`: `None` = by-VALUE `ExtractField` of the loaded aggregate, `Some(off)` =
/// by-REF interior GEP of the scrutinee pointer at the field's rustc byte offset. Only the first
/// had a shim lowering, which is why a `&self` match that BINDS a payload stopped at
/// `shim: Inst::GEP` even after the discriminant read started flipping.
///
/// SINGLE-USE SOUNDNESS, the same argument `recognize_field_write` makes: consuming all three
/// nodes skips the definitions of `off` and `g`, so if either is referenced anywhere else in the
/// body that use finds an undefined value and `cx.operand` fails closed → `DerivedUnsupported` →
/// no flip. The offset constant is required to be the GEP's SOLE index and the GEP's result the
/// load's SOLE pointer, so the triple cannot straddle two different address computations.
fn recognize_ref_payload_read(
    nodes: &[InstrNode],
    i: usize,
) -> Option<(u64, ValueId, Ty, ValueId)> {
    if i + 2 >= nodes.len() {
        return None;
    }
    let Inst::Const { ty: cty, value: Constant::Int(off) } = &nodes[i].inst else {
        return None;
    };
    // The producer emits the offset at pointer width; anything else is a different idiom.
    if !matches!(cty, Ty::I64 | Ty::Isize | Ty::U64 | Ty::Usize) {
        return None;
    }
    let c = *nodes[i].results.first()?;
    let Inst::GEP { pointee_ty, base, indices, .. } = &nodes[i + 1].inst else {
        return None;
    };
    // BYTE-addressed GEP only — that is what a field byte offset means. An element-typed GEP
    // would scale the index and this offset arithmetic would be wrong.
    if !matches!(pointee_ty, Ty::I8 | Ty::U8) || indices.len() != 1 || indices[0] != c {
        return None;
    }
    let g = *nodes[i + 1].results.first()?;
    let Inst::Load { ty, ptr, volatile: false, align: None } = &nodes[i + 2].inst else {
        return None;
    };
    if *ptr != g {
        return None;
    }
    let r = *nodes[i + 2].results.first()?;
    Some((u64::try_from(*off).ok()?, *base, ty.clone(), r))
}

/// Trust (T2d, by-REF enum payload ADDRESS): recognize the PAIR the producer emits when a payload
/// binding's ADDRESS — not its value — is what the body goes on to use:
/// `off = Const(i64 N)` / `g = GEP(i8, base, [off])`, returning `(byte offset, base pointer, g)`.
///
/// This is [`recognize_ref_payload_read`] minus its third node. That difference is the whole
/// point: `recognize_ref_payload_read` requires the triple to END in a `Load`, so a payload whose
/// address is FORWARDED (passed to a call — `Level::is_zero`'s `l1.is_zero()`, which is
/// `<LevelArc as Deref>::deref(&payload)`) declines there and used to die at `shim: Inst::GEP`.
/// A payload the body only takes the ADDRESS of is not read at all, which is why this recognizer
/// carries no loaded type and the caller imposes no scalar gate: there is no loaded value whose
/// width could disagree.
///
/// DISJOINT FROM `recognize_ref_payload_read` BY CONSTRUCTION, and deliberately so. If
/// `nodes[i + 2]` is ANY `Load` through `g`, this returns `None` and leaves the triple to that
/// recognizer, which owns it. The cede test is deliberately WIDER than the read arm's own
/// `volatile: false, align: None` shape (merge of A6/T2d, 2026-08-11): a volatile or explicitly
/// aligned load through `g` is ceded too, so it keeps falling through to the untouched
/// `aggregate_load_refusal` wall exactly as it did before either arm existed, instead of this arm
/// consuming the pair underneath it. Ceding more can only NARROW what this arm admits. Without
/// the clause at all the two arms would race on
/// the same three nodes whenever the read arm's inner gates (unknown variant, ZST-tie offset,
/// width disagreement) declined AFTER matching the shape — this arm would consume two of the three
/// nodes and strand the `Load` on a pointer that no longer has a defining node. Refusing the
/// overlap outright keeps the read arm's decline path exactly where it was: falling through to the
/// untouched `aggregate_load_refusal` wall.
///
/// SINGLE-USE SOUNDNESS, the same argument the read arm makes: consuming both nodes skips the
/// definition of `off`, so any OTHER use of that constant finds an undefined value and
/// `cx.operand` fails closed → `DerivedUnsupported` → no flip. The offset must be the GEP's SOLE
/// index, so the pair cannot straddle two address computations. `g` itself IS bound (to the
/// reconstructed borrow temp), which is the intended forwarding; a SECOND use of `g` is not a
/// soundness problem here (both uses denote the same borrow and the comparator re-checks the
/// result against built) and is independently refused by the flip gate's `mentions == 2`
/// single-use requirement on interior-borrow temps.
fn recognize_ref_payload_addr(nodes: &[InstrNode], i: usize) -> Option<(u64, ValueId, ValueId)> {
    if i + 1 >= nodes.len() {
        return None;
    }
    let Inst::Const { ty: cty, value: Constant::Int(off) } = &nodes[i].inst else {
        return None;
    };
    // The producer emits the offset at pointer width; anything else is a different idiom.
    if !matches!(cty, Ty::I64 | Ty::Isize | Ty::U64 | Ty::Usize) {
        return None;
    }
    let c = *nodes[i].results.first()?;
    let Inst::GEP { pointee_ty, base, indices, .. } = &nodes[i + 1].inst else {
        return None;
    };
    // BYTE-addressed GEP only — that is what a field byte offset means. An element-typed GEP
    // would scale the index and this offset arithmetic would be wrong.
    if !matches!(pointee_ty, Ty::I8 | Ty::U8) || indices.len() != 1 || indices[0] != c {
        return None;
    }
    let g = *nodes[i + 1].results.first()?;
    // Cede the triple to `recognize_ref_payload_read` (see the disjointness note above). ANY
    // `Load` through `g` cedes, not only the read arm's exact non-volatile/unaligned shape.
    if let Some(next) = nodes.get(i + 2) {
        if let Inst::Load { ptr, .. } = &next.inst {
            if *ptr == g {
                return None;
            }
        }
    }
    Some((u64::try_from(*off).ok()?, *base, g))
}

/// Trust (T2b): invert a field BYTE OFFSET back to the `(FieldIdx, field ty)` of `vidx`, using
/// rustc's own per-variant layout. `None` when the layout is unavailable, no field sits at that
/// offset, or MORE THAN ONE does — a ZST tie is ambiguous and must fail closed rather than guess,
/// exactly as `interior_field_at_offset_zero` refuses its own ambiguous match.
fn variant_field_at_offset<'tcx>(
    tcx: TyCtxt<'tcx>,
    enum_rty: RustcTy<'tcx>,
    adt: ty::AdtDef<'tcx>,
    args: ty::GenericArgsRef<'tcx>,
    vidx: rustc_abi::VariantIdx,
    off: u64,
) -> Option<(FieldIdx, RustcTy<'tcx>)> {
    let te = ty::TypingEnv::fully_monomorphized();
    let layout = crate::cycle_safe_layout_of(tcx, te, enum_rty)?;
    let lcx = rustc_middle::ty::layout::LayoutCx::new(tcx, te);
    let vlayout = layout.for_variant(&lcx, vidx);
    let variant = adt.variant(vidx);
    if vlayout.fields.count() != variant.fields.len() {
        return None;
    }
    let mut found: Option<usize> = None;
    for k in 0..variant.fields.len() {
        if vlayout.fields.offset(k).bytes() == off {
            if found.is_some() {
                return None;
            }
            found = Some(k);
        }
    }
    let fidx = FieldIdx::from_usize(found?);
    Some((fidx, variant.fields[fidx].ty(tcx, args).skip_normalization()))
}

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
/// where opaque/generic normalization can query-cycle.
///
/// UNIQUENESS IS DECIDED HERE, not by the caller. Two fields of type `t_ty` at offset 0 (possible
/// only when `t_ty` is a ZST) make the match AMBIGUOUS and this function returns `None` rather
/// than guessing. Until T2e every caller enforced `t_ty` scalar (`flip::scalar_ok`), which made
/// the ambiguous case unreachable and let that scalar test read as the source of the uniqueness;
/// it never was. The wave-29 RETURN caller still enforces it on its own (a non-scalar offset-0
/// field return stays clean-only); the wave-30 ARG caller (T2e) no longer does and relies on this
/// refusal, having pinned both `s_ty` and `t_ty` concrete first. Returns `None` on non-struct
/// `s_ty`, no matching field, or an ambiguous (ZST-tie) match.
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
                // Two same-type fields at offset 0 (possible only when `t_ty` is a ZST) —
                // refuse rather than guess. This IS the uniqueness guarantee (see the doc
                // comment); it is not a defensive echo of a caller-side scalar test.
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
/// The encoder (`crate::encode_site_args`) preserved every arg 1:1 (types and, since #197's
/// follow-up, consts; a region rebuilds as `ReErased` — see below), so this rebuild yields the
/// exact interned args, which
/// the comparator's `raw_call_channel` re-verifies pairwise. A lossy rebuild would produce a
/// non-matching `FnDef` → no `DerivedAgreed` → clean-only (miss a flip, never a wrong one).
///
/// Trust (#197 follow-up): FALLIBLE since const args joined the encoding. A `SiteValTree::Leaf`
/// re-materializes a `ScalarInt` from (bits, size), and `ScalarInt::try_from_uint` is the only
/// honest way to do that — the alternative is an `unwrap` on a value that came from an encoder in
/// a different crate. `None` declines the site (the caller returns `unsup`), which is the same
/// outcome the encoder's own `None` produces: miss a flip, never make a wrong one.
fn rebuild_site_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    enc: &[SiteArg],
) -> Option<ty::GenericArgsRef<'tcx>> {
    let mut out = Vec::with_capacity(enc.len());
    for a in enc {
        out.push(match a {
            SiteArg::Ty(t) => ty::GenericArg::from(rebuild_site_ty(tcx, t)),
            SiteArg::ErasedRegion => ty::GenericArg::from(tcx.lifetimes.re_erased),
            SiteArg::Const(c) => ty::GenericArg::from(rebuild_site_const(tcx, c)?),
        });
    }
    Some(tcx.mk_args_from_iter(out.into_iter()))
}

/// Trust (#197 follow-up): re-materialize an intern-equal `ty::Const` from [`SiteConst`].
///
/// Intern-equal, not merely equivalent: `ty::Const::new_value` interns on (valtree, ty), and both
/// were preserved 1:1 by `encode_site_const`, so the result is the same interned const the site
/// spelled. That is what lets the comparator's raw-call channel pin callee identity on it.
fn rebuild_site_const<'tcx>(tcx: TyCtxt<'tcx>, c: &SiteConst) -> Option<ty::Const<'tcx>> {
    let SiteConst::Value(sty, vt) = c;
    let ty = rebuild_site_ty(tcx, sty);
    let valtree = rebuild_site_valtree(tcx, vt)?;
    Some(ty::Const::new_value(tcx, valtree, ty))
}

fn rebuild_site_valtree<'tcx>(
    tcx: TyCtxt<'tcx>,
    vt: &SiteValTree,
) -> Option<ty::ValTree<'tcx>> {
    Some(match vt {
        SiteValTree::Leaf(bits, size_bytes) => {
            // The width is part of the value's identity — see `SiteValTree::Leaf`. A `None` here
            // means the (bits, size) pair does not name a `ScalarInt`, which cannot happen for an
            // encoding this crate produced; declining is still the right answer if it ever does.
            let si = rustc_middle::ty::ScalarInt::try_from_uint(
                *bits,
                rustc_abi::Size::from_bytes(*size_bytes),
            )?;
            ty::ValTree::from_scalar_int(tcx, si)
        }
        SiteValTree::Branch(elems) => {
            let mut consts = Vec::with_capacity(elems.len());
            for e in elems {
                consts.push(rebuild_site_const(tcx, e)?);
            }
            ty::ValTree::from_branches(tcx, consts)
        }
    })
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
    /// Trust (wave-MF): retire the operand temps FORWARD instead of reverse — the wrong
    /// `StorageDead` ORDER, with every value and every `StorageLive` left correct. Needs two
    /// operand temps to be observable, so the fixture must carry a two-operand rvalue.
    MarkerOrder,
    /// Trust (wave-MF): drop the LAST `StorageDead` of each retirement — a missing marker rather
    /// than a misordered one. The two classes fail the channel at different lines (order fails at
    /// the first swapped dead; drop fails at `<end>`), so neither subsumes the other.
    MarkerDrop,
    /// Trust (lane L): mint an AGGREGATE's field operand temps in REVERSE field order. Every
    /// value is untouched (the operands are reassembled in field order before the `Rvalue` is
    /// built) and every marker is still balanced — only the `StorageLive` SEQUENCE is wrong.
    /// `MarkerOrder`/`MarkerDrop` both act in `mf_retire` and so exercise only the DEAD side;
    /// this is the one that attacks the aggregate arm's LIVE side, which is the half lane L
    /// actually added. Needs two temp-minting fields to be observable, so the count is bumped
    /// only when it really reordered two markers (a class that never fires is an INERT control).
    ///
    /// **WHERE IT IS OBSERVABLE, AND WHERE IT IS NOT** (lane N review, 2026-08-13, MEASURED on
    /// clean-kernel @ `clean c4a430543`). It reorders only the temps this arm MINTS, so a
    /// one-field constructor is a no-op by construction, and `canon_markers` alpha-renames a
    /// permutation of SAME-TYPED field temps at identical statement positions back to a
    /// byte-identical string. On the whole crate that leaves the class with `applications >= 1` on
    /// exactly ONE body (`SourcePos::new`, three `u32` places) and `markers_exact` UNCHANGED at
    /// 1080 — i.e. **the marker channel refuses nothing here**; the class is inert against the
    /// oracle on this corpus. The observable witness is `mk_mixed` (`{u8, u64}`) in
    /// `probes/mf_aggregate_temps.rs`, where the permutation shows up in the type column and the
    /// channel does refuse (probe flips 14 -> 13). Any whole-crate flip movement under this flag is
    /// therefore NOT the channel catching the perturbation and must not be reported as such.
    AggFieldOrder,
    /// Trust (lane K): the ARM-ASYMMETRIC, MULTISET-PRESERVING marker perturbation — MOVE the
    /// last deferred `StorageDead` from the THEN arm's entry list to the ELSE arm's, so the two
    /// arms retire DIFFERENT lists while the body as a whole retires exactly the same bag of
    /// locals. `MarkerOrder`/`MarkerDrop` corrupt a retirement SYMMETRICALLY (both arms get the
    /// same wrong list, because both are fed from one `mf_retire` call); this one does not. A
    /// perturbed body that still flips is a hole in the marker channel.
    ///
    /// **THE MOVE IS THE POINT** (defect closed 2026-08-13; this class previously DROPPED the
    /// last dead on the else arm). The property it exists to witness is "`markers_exact`
    /// compares the arms SEPARATELY rather than comparing one whole-body multiset". A DROP
    /// cannot witness that: deleting a marker changes the multiset too, so both hypotheses —
    /// arm-wise comparison and multiset comparison — predict a refusal, and the experiment
    /// discriminates nothing. That was not a theoretical objection: measured on
    /// `probes/mf_multiblock.rs` (7 exact -> 1) and on `mb_adversarial.rs` (8 -> 1), `marker-arm`
    /// and `marker-drop` refused the SAME bodies at the SAME line with BYTE-IDENTICAL
    /// `markers_detail`, 14 of 14. Structural, not corpus luck: built always routes the false
    /// edge through the trampoline, so the ELSE arm is always fine index 2 and both classes first
    /// diverge inside it.
    ///
    /// A MOVE leaves the whole-body `StorageDead` multiset untouched — the moved local is still
    /// emitted the same number of times, because both arms are fed from one list — and changes
    /// only WHICH ARM retires it. A whole-body-multiset comparator accepts it; `canon_markers`
    /// refuses it. The direction is chosen so the divergence is also OBSERVABLY different from
    /// `marker-drop`: the else arm (walked first) gains an EXTRA retirement where `marker-drop`
    /// leaves it one short.
    ///
    /// The split itself is [`mf_split_arm_deads`], a pure function, so the multiset-preservation
    /// claim is pinned by a test rather than by this paragraph.
    MarkerArm,
    /// Trust (wave-EP REVIEW, 2026-08-17): the ENUM-PAYLOAD plan's TRAMPOLINE, moved onto the
    /// OTHER outgoing switch edge. The wave-EP class emits ONE marker pair in ONE arm block, so
    /// `MarkerOrder` (needs >= 2 pairs) and `MarkerDrop`/`MarkerArm` (both act in `mf_retire`,
    /// which this class does not use) are all INERT on it — the wave shipped with no registered
    /// control over its own emission and only a source mutant as witness. This is that control.
    ///
    /// **IT IS SEMANTICALLY INERT AND THAT IS THE POINT.** An empty `Goto` block on either
    /// outgoing edge is the same program: the derived-MIR channel threads gotos (LEDGER L3) and
    /// still says `agreed`, the values are untouched, and no `StorageLive`/`StorageDead` is added,
    /// dropped or reordered. The ONLY channel that can refuse it is `canon_markers`, which walks
    /// the RAW CFG and therefore sees the marker at a different fine block index. A perturbed
    /// compile that still flips is a marker channel that is not reading block position at all.
    ///
    /// Sited at the trampoline mint, after the wave-YM sort and after every other perturbation, so
    /// the redirect cannot be undone downstream. `sat_perturb_count` is bumped only when the
    /// switch really had another edge to move it to — a class that never fires is an inert control.
    PayloadTramp,
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
            "marker-order" => Self::MarkerOrder,
            "marker-drop" => Self::MarkerDrop,
            "agg-field-order" => Self::AggFieldOrder,
            "marker-arm" => Self::MarkerArm,
            "payload-tramp" => Self::PayloadTramp,
            _ => return None,
        })
    }
}

/// Trust (lane K; defect close 2026-08-13): split ONE deferred retirement list into the two arms'
/// entry lists.
///
/// Built retires a `CondBr` condition's operand temps at the ENTRY OF BOTH ARMS — their region
/// scope is the condition expression, which built exits on each outgoing edge — so the unperturbed
/// answer is that one list, twice.
///
/// `perturb` is `-Ztrust-sat-perturb=marker-arm`: MOVE the last retirement off the THEN arm and
/// onto the ELSE arm. The whole-body multiset of `StorageDead`s is UNCHANGED (the same local is
/// still retired the same number of times overall); only the ARM ASSIGNMENT differs. That is what
/// makes the class discriminate "arms compared separately" from "one whole-body multiset compared"
/// — a DROP changes both, so it discriminates neither. See [`SatPerturb::MarkerArm`].
///
/// Returns `(then_order, else_order, applied)`; `applied` is `false` when there was nothing to
/// move, so the caller's `sat_perturb_count` counts real applications only.
fn mf_split_arm_deads(order: Vec<Local>, perturb: bool) -> (Vec<Local>, Vec<Local>, bool) {
    let mut then_order = order.clone();
    let mut else_order = order;
    if perturb {
        if let Some(moved) = then_order.pop() {
            else_order.push(moved);
            return (then_order, else_order, true);
        }
    }
    (then_order, else_order, false)
}

// MARKER-GATE-BEGIN — the sanctioned region. `marker_gate_invariant_tests` refuses to compile a
// shim in which a storage marker is constructed anywhere else in this file. Do not move, rename or
// duplicate these two sentinels; do not put anything but the gate between them.
/// Trust (lane MF-R5, 2026-08-14): **THE MARKER CHOKEPOINT — the plans, the emission, and the
/// law that ties them together WITHOUT counting the same event twice.**
///
/// WHAT FIVE REVIEWS OF THIS SHIM HAVE ESTABLISHED. A storage marker this shim emits without a
/// plan's permission is a body whose derived marker sequence is not built's, and it ships as
/// `agreed` — 12 such bodies, then 17, then 43, then 46/183/311. Rounds 1-4 each added a layer and
/// each layer was walked around one level down: the shapes, then the arm's predicate, then the
/// arm's SCOPE, then a lease type that was unforgeable but whose PLAN was a plain mutable field.
///
/// ROUND 5 DELETES THREE OF THOSE LAYERS AND KEEPS ONE PROPERTY. The fifth review's three attacks
/// were: forge the plan (`cx.mf_borrow = true`, then take a genuine lease); drop the per-VALUE
/// conjunct at `ResultTemp` and keep the per-BODY lease; retire the same local twice. None of them
/// forged a lease, and none of them was caught. The reason is structural: round 4's authority
/// token proved that SOME plan admitted the BODY, and the thing that decides an individual
/// emission is a different question — which value, which local, how many. So:
///
/// 1. **THE PLANS ARE SEALED** ([`MfPlans`]). Their fields are private to this module and there is
///    exactly ONE constructor, [`MfPlans::seal`], which is a PURE FUNCTION OF THE BODY — it reads
///    the same HIR and trust-ir the plans always read and computes the same answer every time.
///    `cx.mf_borrow = true` does not compile (no such field); `cx.mf_plans.borrow = true` does not
///    compile (private field); and the strongest legal spelling, re-sealing
///    (`cx.mf_plans = MfPlans::seal(tcx, def, func)`), is a no-op BY CONSTRUCTION. Attack 1 is
///    closed at compile time, not by a check.
/// 2. **THE DECISION AND THE EMISSION ARE ONE OPERATION** ([`super::ShimCx::mf_mark_result`] and
///    its four siblings). The plan query is INSIDE the emitting method, in this module, and there
///    is no way for an arm to obtain the right to emit and then emit something else: no lease
///    leaves the gate, because there is no lease. Attack 2 removed the per-value conjunct from an
///    arm; in round 5 the per-value conjunct is not in an arm to remove, and the arm cannot spell
///    the emission without it. Closed at compile time.
/// 3. **THE LAW HAS TWO INDEPENDENTLY DERIVED SIDES** ([`observe`] vs [`MfPlans::predict`]).
///    Round 4's conservation law compared the markers in the finished body against a counter
///    incremented INSIDE `push_marker`, on the line before that same function pushed the
///    statement: the two sides were one event counted twice, so the law could not see
///    over-issuance at all (measured: it moves zero bodies, on honest code AND under all three
///    attacks). Round 5 replaces it with a genuine comparison:
///
///      * `observe(&cx.blocks)` walks the FINISHED MIR and counts the storage markers that are
///        actually there. It touches no counter and no plan.
///      * `MfPlans::predict(func, agg_chains)` re-derives, FROM THE SEALED PLANS AND THE TRUST-IR,
///        how many markers this body must carry — the marked-result set's size, the operand
///        positions the plan classifies as places, the deferred retirements lane K schedules onto
///        BOTH arms, the field-write plan's source-counted pairs, the interior-borrow plan's one.
///        It touches no emitted statement.
///
///    An extra emission — from any arm, through any spelling, including a raw statement pushed by
///    a factory in another module — moves the first number and not the second, and the body fails
///    CLOSED. That is the property round 4 claimed and did not have. Attack 3 (retire twice) is
///    caught here rather than at compile time, and [`observe`] additionally refuses the two
///    identity violations a count alone cannot see: a local marked live twice, and a local retired
///    twice IN THE SAME BLOCK. (Lane K legitimately retires one local at the entry of BOTH arms —
///    one list, twice, in two different blocks — which is why the rule is per-block and not
///    per-body.)
///
/// WHAT WAS DELETED, AND WHY IT IS NOT A LOSS. `MarkerLease` and its mint, `MfSite`, `MfCensus`
/// and its five lanes, `may_retire`, `mf_marked`, `mf_unaccounted_deads`, the body-end site ledger
/// and the `observed == issued` conservation law are all gone. Each was measured UNWITNESSED on
/// 1,160 bodies — deleting it moved nothing — and each was measured INERT under the attacks that
/// worked. What replaces them is smaller and answers the question they were asked: an emission the
/// plans did not predict fails the body closed, whatever it is spelled like, because the two sides
/// of the comparison are derived from different things.
mod mf_gate {
    use std::collections::{HashMap, HashSet};

    use rustc_index::IndexVec;
    use rustc_middle::mir::{
        BasicBlock, BasicBlockData, Local, LocalDecl, Operand, Rvalue, Statement, StatementKind,
    };
    use rustc_middle::ty::{self, TyCtxt};
    use rustc_span::def_id::LocalDefId;
    use trust_ir::{BlockId, Inst, Ty, ValueId};

    use super::{
        MfBranch, MfBranchPlan, MfCheckedPlan, MfPayloadPlan, MfWritePlan, RustcTy,
        agg_return_chains, checked_params_mint_no_local, plan_branch_markers,
        plan_checked_markers, plan_field_write_markers, plan_interior_borrow_markers,
        plan_operand_marker_temps, plan_payload_markers, source_form_admits,
        source_form_marker_plan_available,
    };

    /// Trust (lane MF-R7, 2026-08-14): **THE SEALED PLANS.** Every marker permission this shim
    /// has, in one value with private fields and one constructor.
    ///
    /// Round 4 kept `mf_plan` / `mf_write` / `mf_borrow` as plain `ShimCx` fields, which every arm
    /// in the file could write. The fifth review's first attack is one line in one arm
    /// (`cx.mf_borrow = true`) followed by a GENUINE lease, and it put 46 bodies into
    /// admitted-and-wrong with every layer green. The fields are private here, and the only
    /// constructor is [`MfPlans::seal`], which recomputes them from the body.
    pub(super) struct MfPlans {
        /// The wave-MF / lane-K marked-RESULT set: the plan's per-VALUE answer.
        operand: Option<HashSet<ValueId>>,
        /// Lane K's multi-block branch table (`None` for the single-block class).
        branch: Option<MfBranchPlan>,
        /// The field-write plan and its source-counted pair total.
        write: Option<MfWritePlan>,
        /// The interior-borrow plan: at most one pair.
        borrow: bool,
        /// Trust (wave-EP): the enum-payload-READ plan — at most one pair, in one switch arm.
        payload: Option<MfPayloadPlan>,
        /// Trust (wave-CK): the checked-arithmetic chain — one pair per non-outermost link.
        checked: Option<MfCheckedPlan>,
    }

    /// Trust (lane MF-R7): **THE RUNTIME IDENTITY PIN** — does `def` name the body `func` is?
    ///
    /// The seventh review's attack A" is one line at function scope in `lower_ir_to_mir`:
    ///
    /// ```text
    /// let def = tcx.typeck_root_def_id(def.to_def_id()).as_local().unwrap_or(def);
    /// ```
    ///
    /// It leaves both `MfPlans::seal(tcx, def, func)` spellings verbatim, the occurrence pin at
    /// two, `cx.mf_plans =` at zero — and points BOTH sides of the law at a different body's HIR.
    /// Four closure bodies went admitted-and-wrong, and four more moved the other way. Occurrence
    /// counting cannot see a shadow, so the pin has to be a RUNTIME comparison against an identity
    /// the shadow does not own: the trust-ir module's own function name, which the producer writes
    /// from the def path of the body it lowered.
    ///
    /// The comparison is on the LAST path segment only, which is the segment `typeck_root_def_id`
    /// removes: a closure body is `..::{closure#0}` and its typeck root is not. A const/static
    /// initializer body is named `..::{const-init}` by the producer while rustc's def path stops at
    /// the item, so that one suffix is stepped over before comparing.
    ///
    /// A mismatch does not merely refuse the law — it yields the EMPTY plan set, so no emitter site
    /// may push a marker at all. That is the fail-closed direction: a body whose plans were sealed
    /// against another body ships marker-free (the oracle then reads `derived <end>`, a refusal),
    /// never with a marker sequence that is not built's.
    fn names_this_body(tcx: TyCtxt<'_>, def: LocalDefId, func: &trust_ir::Function) -> bool {
        let mut segs = func.name.rsplit("::");
        let mut last = segs.next().unwrap_or("");
        if last == "{const-init}" {
            last = segs.next().unwrap_or("");
        }
        match tcx.def_path(def.to_def_id()).data.last() {
            Some(seg) => seg.as_sym(false).as_str() == last,
            None => false,
        }
    }

    impl MfPlans {
        /// **THE ONE CONSTRUCTOR, AND IT IS A PURE FUNCTION OF THE BODY.** The plans are mutually
        /// exclusive — every one of them is a claim about the WHOLE body, so two holding at once is
        /// two whole-body claims about one body, which is the state the third review measured — and
        /// this is the one place that exclusivity is resolved.
        pub(super) fn seal(tcx: TyCtxt<'_>, def: LocalDefId, func: &trust_ir::Function) -> MfPlans {
            let none = MfPlans {
                operand: None,
                branch: None,
                write: None,
                borrow: false,
                payload: None,
                checked: None,
            };
            // Trust (lane MF-R7): the identity pin, before any HIR is read. See
            // [`names_this_body`].
            if !names_this_body(tcx, def, func) {
                return none;
            }
            let write = plan_field_write_markers(tcx, def);
            let borrow = plan_interior_borrow_markers(tcx, def);
            // Trust (wave-EP): the payload plan is a WHOLE-BODY claim like every other, so it is
            // resolved here, against the two source-form plans, and it takes the general
            // source-form lane out of the running when it holds. The trust-ir grammar it demands
            // (a four-block `Switch` body) is already outside `plan_branch_markers`' terminator
            // set and `plan_operand_marker_temps`' single-block class, so the exclusion below is a
            // CHECKED fact rather than a coincidence of two refusals.
            let payload =
                if write.is_none() && !borrow { plan_payload_markers(func) } else { None };
            // Trust (wave-CK): a sixth whole-body claim, resolved here against the other five. Its
            // trust-ir grammar (a one-block body carrying `Inst::Overflow`/`Select`/`Assert`) is
            // already outside `plan_operand_marker_temps`' and `plan_branch_markers`' instruction
            // sets and outside `plan_payload_markers`' four-block switch grammar, so this exclusion
            // is a CHECKED fact rather than a coincidence of three refusals — but it is written
            // down, because "the other plans happen to refuse it" is exactly the kind of premise
            // that stops being true one wave later.
            let checked = if write.is_none()
                && !borrow
                && payload.is_none()
                && checked_params_mint_no_local(tcx, def)
            {
                plan_checked_markers(func)
            } else {
                None
            };
            let source_form_ok = payload.is_none()
                && checked.is_none()
                && source_form_marker_plan_available(write, borrow, source_form_admits(tcx, def));
            let branch = if source_form_ok { plan_branch_markers(func) } else { None };
            let operand = match &branch {
                Some(p) => Some(p.needs.clone()),
                None if source_form_ok => plan_operand_marker_temps(func),
                None => None,
            };
            MfPlans { operand, branch, write, borrow, payload, checked }
        }

        /// Trust (lane MF-R7): the plans as a VALUE, for the law's own unit tests. `#[cfg(test)]`
        /// — it does not exist in a shipped driver, where [`MfPlans::seal`] remains the only
        /// constructor and the only thing that can decide a plan.
        #[cfg(test)]
        pub(super) fn plans_for_test(
            operand: Option<HashSet<ValueId>>,
            branch: Option<MfBranchPlan>,
        ) -> MfPlans {
            MfPlans { operand, branch, write: None, borrow: false, payload: None, checked: None }
        }

        /// Trust (wave-EP): the payload plan as a VALUE, for the law's own unit tests. `#[cfg(test)]`
        /// — it does not exist in a shipped driver.
        #[cfg(test)]
        pub(super) fn payload_for_test(payload: MfPayloadPlan) -> MfPlans {
            MfPlans {
                operand: None,
                branch: None,
                write: None,
                borrow: false,
                payload: Some(payload),
                checked: None,
            }
        }

        /// The plan's per-VALUE answer: does built materialise a marker-carrying temp for `r`?
        fn marks_result(&self, r: ValueId) -> bool {
            self.operand.as_ref().is_some_and(|p| p.contains(&r))
        }

        /// Is the body in the operand-temp class at all? (Operand temps and their retirements have
        /// no per-value name of their own; the class is what authorises them, and
        /// [`MfPlans::predict`] is what places them.)
        fn operand_class(&self) -> bool {
            self.operand.is_some()
        }

        /// Lane K's admitted `CondBr` for one producer block.
        pub(super) fn branch_at(&self, blk: BlockId) -> Option<MfBranch> {
            self.branch.as_ref()?.branch.get(&blk).copied()
        }

        /// **THE PREDICTED SIDE OF THE LAW — THE WHOLE SEQUENCE, NOT A PROJECTION OF IT.**
        ///
        /// Rounds 4-6 each compared two INTEGERS (plus, in round 6, set identity and one intra-run
        /// order rule). The seventh review's finding is that the ORACLE compares
        /// `mk b{fine}.{assigns_seen}:{live|dead} s{alpha}:{ty}` — and the first two components,
        /// the block and the position within it, were derived by NEITHER side. Seven attacks
        /// followed, every one a relocation of a marker the law could not see: 362 bodies for a
        /// `StorageLive` moved past its own initialising assign, 133 for a retirement moved before
        /// the assign that consumes it, 155 for the aggregate seam, 69 for the result temp, plus
        /// two evasions of round 6's order rule. Every one of them left `UNSUPPORTED` at exactly
        /// its control value: the gate fired on nothing.
        ///
        /// So this side now produces the SEQUENCE. Every marker the plans require, in order, as
        /// [`MfEvent`]: which MIR block it lands in, how many assignments precede it there, live or
        /// dead, which storage slot it names, and WHERE THAT SLOT IS CONSUMED. [`observe`] produces
        /// the same sequence from the FINISHED body. A relocation by ONE STATEMENT moves the
        /// observed sequence and not this one.
        ///
        /// **THIS IS A MODEL OF THE EMITTER'S STATEMENT SHAPE, NOT A COPY OF THE EMITTER.** What it
        /// needs to know is: how many `Assign`s each admitted instruction emits, and where the
        /// markers sit among them. That is one small closed-form per instruction, and it is only
        /// tractable because every marker plan is a whole-body claim over a CLOSED instruction set
        /// (`plan_operand_marker_temps` / `plan_branch_markers` admit nine `Inst` shapes each; the
        /// two source-form plans admit a straight-line field-write grammar and a single `&place`
        /// body). An instruction outside the model is an `Err` and the body fails CLOSED — it does
        /// not fall back to a weaker law, because a fallback is exactly the vacuity round 6's order
        /// rule was defeated through.
        ///
        /// The block index is the MIR block index and not the oracle's DFS "fine" index. They are a
        /// bijection of one another over one body — the shim allocates exactly one MIR block per
        /// trust-ir block, in order, before it lowers anything, and every later `new_block` (lane
        /// K's `Goto` trampoline, an assert split) is appended after all of them — so comparing in
        /// MIR order decides the same question with no second copy of the oracle's walk. A marker
        /// in a block this model does not enumerate has no counterpart here and fails closed.
        ///
        /// `agg_chains` is RE-DERIVED here (`agg_return_chains(func, ret_rty)`) rather than handed
        /// over. The sixth review's repair re-derived the PLANS and left this list one derivation
        /// with two readers; the seventh measured 7 bodies through it (`aggcopy`) and 115 through
        /// `aswap2`. Re-deriving it is what makes the aggregate term this side's own.
        ///
        /// **ROUND 8 CARRIES THE DECLARED TYPE** ([`MfTy`]) — the one component of the oracle's
        /// line round 7 replaced with a stand-in, and the one the eighth review used to put 261
        /// probe bodies and nine shipped `clean-kernel` bodies into admitted-and-wrong with round
        /// 7's law green. It is derived from the producer's own type annotations here and from the
        /// finished body's `local_decls` in [`observe`]; the emitter reads neither of those to type
        /// a temp — it reads `place.ty(&self.local_decls, self.tcx)`.
        ///
        /// **WHAT THIS SIDE STILL CANNOT SEE IS THE PLAN ITSELF.** `self.operand` and
        /// `self.branch` are read here and by the emitter, so a widened plan moves both sides at
        /// once and this comparison stays green — 34, 28 and 3 admitted-and-wrong bodies for the
        /// three ordering rules deleted one at a time, measured on round 8. The full statement of
        /// that boundary, including why no layer inside this file can close it and which check
        /// does, is written at the law's call site in `lower_ir_to_mir`; it is not repeated here,
        /// and it should be read before this gate is quoted as evidence of anything.
        pub(super) fn predict<'tcx>(
            &self,
            func: &trust_ir::Function,
            ret_rty: RustcTy<'tcx>,
        ) -> Result<MfSeq, String> {
            // NO PLAN, NO MARKER — and that is now a positional claim about the whole body, not a
            // count. Every one of the six emission methods returns early outside its plan, so the
            // predicted sequence is empty and any marker at all fails the body closed.
            if !self.operand_class()
                && self.write.is_none()
                && !self.borrow
                && self.payload.is_none()
                && self.checked.is_none()
            {
                return Ok(MfSeq::default());
            }
            // Trust (wave-CK): the checked-arithmetic chain has its own whole-body walk, for the
            // same reason the payload class does — it is the only class whose markers land in MIR
            // blocks the general walk does not enumerate (an `Inst::Assert` SPLITS the chain, and
            // the split blocks are appended after every trust-ir block). Dispatching here keeps
            // every other class's predicted sequence bit-identical to what it was.
            if let Some(p) = &self.checked {
                return predict_checked(func, p);
            }
            // Trust (wave-EP): the payload class has its own whole-body walk. `MfPlans::seal`
            // makes the plans mutually exclusive, so reaching this line means every other plan is
            // absent — and dispatching HERE is what keeps the existing four classes' predicted
            // sequences bit-identical to what they were before this wave (the walk below never
            // learned a `Switch` or a `GEP`, so no body outside this class can change its verdict
            // through the model).
            if let Some(p) = &self.payload {
                return predict_payload(func, p);
            }
            if matches!(ret_rty.kind(), ty::Adt(adt, _) if adt.is_enum()) {
                // The `Return` arm's enum-construction reconstruction (`emit_enum_variant`) has a
                // statement shape this model does not carry. Fail closed rather than guess.
                return Err("enum-returning body outside the marker sequence model".to_string());
            }
            let (agg_skip, agg_chains) = agg_return_chains(func, ret_rty);
            self.predict_from(func, &agg_skip, &agg_chains)
        }

        /// The sequence walk itself, over a trust-ir body and the aggregate recognition its
        /// `Return` arm collapses — a total function of those two, so `marker_law_tests` can
        /// exercise it on synthetic trust-ir without a compiler.
        pub(super) fn predict_from(
            &self,
            func: &trust_ir::Function,
            agg_skip: &HashSet<ValueId>,
            agg_chains: &HashMap<ValueId, Vec<ValueId>>,
        ) -> Result<MfSeq, String> {
            // Trust (wave-EP): the payload class has its own walk and [`MfPlans::predict`]
            // dispatches to it BEFORE this one. Refusing FIRST — in every build, not only a debug
            // one, and above the empty-plan early return that would otherwise swallow it — is what
            // makes "exactly one walk decides any given body" a checked runtime fact rather than a
            // reading of the dispatch. A body that reached this line with a payload plan fails
            // CLOSED: it ships marker-free.
            if self.payload.is_some() {
                return Err(
                    "the payload class has its own sequence walk; this one must not decide it"
                        .to_string(),
                );
            }
            // Trust (wave-CK): the same refusal, for the same reason and in every build. A body
            // that reached this line with a checked-chain plan fails CLOSED — it ships marker-free
            // — rather than being decided by a walk that cannot see its split blocks.
            if self.checked.is_some() {
                return Err(
                    "the checked-chain class has its own sequence walk; this one must not decide it"
                        .to_string(),
                );
            }
            let mut b: MfSeqBuild<MfSlot> = MfSeqBuild::new();
            let mut keys: Vec<(MfSlot, MfKey)> = Vec::new();
            let mut tys: Vec<(MfSlot, MfTy)> = Vec::new();
            if !self.operand_class() && self.write.is_none() && !self.borrow {
                return Ok(b.finish(&keys, &tys));
            }
            let empty: HashSet<ValueId> = HashSet::new();
            let needs = self.operand.as_ref().unwrap_or(&empty);
            let in_class = self.operand_class();
            let mut def_of: HashMap<ValueId, &Inst> = HashMap::new();
            // **THE DECLARED TYPE OF EVERY VALUE, FROM THE PRODUCER'S OWN ANNOTATION.** A block
            // parameter's type is on the block; every other class carries its result type on the
            // instruction that defines it, and `Inst::ICmp` always yields `Ty::Bool`. This is the
            // same three-line derivation `agg_field_order_ok`'s `field_ty` uses, and it reads
            // nothing the EMITTER reads: the emitter types a temp from `local_decls`/`tcx`.
            let mut ty_of: HashMap<ValueId, MfTy> = HashMap::new();
            for blk in &func.blocks {
                for (p, t) in &blk.params {
                    ty_of.insert(*p, ir_ty_token(t));
                }
                for node in &blk.body {
                    for r in &node.results {
                        def_of.insert(*r, &node.inst);
                    }
                    let Some(r) = node.results.first() else { continue };
                    let t = match &node.inst {
                        Inst::Const { ty, .. }
                        | Inst::ExtractField { ty, .. }
                        | Inst::BinOp { ty, .. }
                        | Inst::UnOp { ty, .. }
                        | Inst::Load { ty, .. } => ir_ty_token(ty),
                        Inst::ICmp { .. } => ir_ty_token(&Ty::Bool),
                        Inst::Cast { dst_ty, .. } => ir_ty_token(dst_ty),
                        _ => continue,
                    };
                    ty_of.insert(*r, t);
                }
            }
            // Lane K's CROSS-BLOCK retirements, scheduled exactly where the emitter schedules them:
            // a `CondBr` condition's operand temps at the entry of BOTH arms, the condition's own
            // temp at the join. The plan proves every arm and join is lowered after its head, which
            // is why one forward walk is enough here as it is there.
            let mut entry: HashMap<BlockId, Vec<MfSlot>> = HashMap::new();
            let mut temps = 0u32;
            let mut marked_writes = 0usize;
            for (bi, blk) in func.blocks.iter().enumerate() {
                b.block(bi);
                for d in entry.remove(&blk.id).unwrap_or_default() {
                    b.mark(false, d);
                }
                let br = self.branch.as_ref().and_then(|p| p.branch.get(&blk.id)).copied();
                let nodes = &blk.body;
                let mut i = 0usize;
                while i < nodes.len() {
                    let node = &nodes[i];
                    if node.results.iter().any(|r| agg_skip.contains(r)) {
                        i += 1;
                        continue;
                    }
                    // The field-write triple (`recognize_field_write`'s shape, re-derived from the
                    // trust-ir): `Load struct; InsertField; Store`. A PLACE right-hand side takes
                    // built's operand temp and its pair; a constant or rvalue right-hand side folds
                    // into one assign with no marker.
                    if self.write.is_some() {
                        if let Some(value) = write_triple(nodes, i) {
                            if matches!(def_of.get(&value), None | Some(Inst::ExtractField { .. }))
                            {
                                let s = MfSlot::Temp(temps);
                                temps += 1;
                                // The write temp is a copy of the STORED VALUE, so it carries that
                                // value's declared type; the emitter types it from the rustc field
                                // type `recognize_field_write` read out of the source.
                                tys.push((s, ty_at(&ty_of, value)));
                                b.mark(true, s);
                                b.assign();
                                keys.push((s, Some((bi, b.at(), 0))));
                                b.assign();
                                b.mark(false, s);
                                marked_writes += 1;
                            } else {
                                b.assign();
                            }
                            i += 3;
                            continue;
                        }
                    }
                    let r0 = node.results.first().copied();
                    let is_cond = br.is_some_and(|x| Some(x.cond) == r0);
                    match &node.inst {
                        // A folded constant and a field PLACE each mint no statement of their own.
                        Inst::Const { .. } | Inst::ExtractField { .. } => {}
                        // `_t = copy (*_p)`: one assign, and the temp IS built's operand temp.
                        Inst::Load { volatile: false, align: None, .. } => {
                            if let Some(r) = r0.filter(|r| self.marks_result(*r)) {
                                let s = MfSlot::Res(r);
                                tys.push((s, ty_at(&ty_of, r)));
                                b.mark(true, s);
                            }
                            b.assign();
                        }
                        Inst::BinOp { lhs, rhs, .. } | Inst::ICmp { lhs, rhs, .. } => {
                            if let Some(r) = r0.filter(|r| self.marks_result(*r)) {
                                let s = MfSlot::Res(r);
                                tys.push((s, ty_at(&ty_of, r)));
                                b.mark(true, s);
                            }
                            let deads = mint_operands(
                                &mut b,
                                &mut temps,
                                &mut tys,
                                needs,
                                &def_of,
                                &ty_of,
                                &[*lhs, *rhs],
                                in_class,
                            );
                            close_group(&mut b, &mut keys, bi, &deads, is_cond, br, &mut entry);
                        }
                        Inst::UnOp { operand, .. } | Inst::Cast { operand, .. } => {
                            if let Some(r) = r0.filter(|r| self.marks_result(*r)) {
                                let s = MfSlot::Res(r);
                                tys.push((s, ty_at(&ty_of, r)));
                                b.mark(true, s);
                            }
                            let deads = mint_operands(
                                &mut b,
                                &mut temps,
                                &mut tys,
                                needs,
                                &def_of,
                                &ty_of,
                                &[*operand],
                                in_class,
                            );
                            close_group(&mut b, &mut keys, bi, &deads, is_cond, br, &mut entry);
                        }
                        Inst::Return { values } => match values.as_slice() {
                            // The collapsed constructor chain: every field through `mf_operand` in
                            // FIELD order, one aggregate assign, then the deads in REVERSE.
                            [v] if agg_chains.contains_key(v) => {
                                let deads = mint_operands(
                                    &mut b,
                                    &mut temps,
                                    &mut tys,
                                    needs,
                                    &def_of,
                                    &ty_of,
                                    &agg_chains[v],
                                    in_class,
                                );
                                close_group(&mut b, &mut keys, bi, &deads, false, None, &mut entry);
                            }
                            // Wave-29b's reborrow temp: `StorageLive(t); t = &((*_1).K);
                            // _0 = &(*t); StorageDead(t)`. Both assignments are `Rvalue::Ref`,
                            // which carries no operand sequence, so the slot has no use site —
                            // and the finished body says the same.
                            [_] if self.borrow => {
                                let s = MfSlot::Temp(temps);
                                temps += 1;
                                // `&FieldTy` — the one marked slot in this shim whose declared type
                                // is outside the scalar denotation. See [`MfTy::Opaque`].
                                tys.push((s, MfTy::Opaque));
                                b.mark(true, s);
                                b.assign();
                                b.assign();
                                b.mark(false, s);
                            }
                            [] | [_] => b.assign(),
                            _ => {
                                return Err(
                                    "Return arity outside the marker sequence model".to_string()
                                );
                            }
                        },
                        // Each edge argument is copied into the target block's parameter local.
                        Inst::Br { args, .. } => {
                            for _ in args {
                                b.assign();
                            }
                        }
                        // A terminator mints no statement, and it is the ONE consumer that is not
                        // an assignment — so the condition's temp has no use site on either side.
                        // It is retired at the join, at position 0, which is where built puts it.
                        Inst::CondBr { .. } => {
                            if let Some(x) = br {
                                let s = MfSlot::Res(x.cond);
                                tys.push((s, ty_at(&ty_of, x.cond)));
                                entry.entry(x.join).or_default().push(s);
                            }
                        }
                        other => {
                            return Err(format!(
                                "no marker sequence model for Inst::{}",
                                super::inst_name(other)
                            ));
                        }
                    }
                    i += 1;
                }
            }
            // The field-write plan is derived from the SOURCE and this walk is derived from the
            // TRUST-IR; they are two derivations of one number and they must agree.
            if let Some(w) = self.write {
                if marked_writes != w.marking_writes {
                    return Err(format!(
                        "the field-write plan counts {} marking write(s) in the source and the \
                         trust-ir carries {marked_writes}",
                        w.marking_writes
                    ));
                }
            }
            Ok(b.finish(&keys, &tys))
        }
    }

    /// **THE PREDICTED SIDE FOR THE WAVE-EP PAYLOAD CLASS** — the whole canonical sequence, from
    /// the sealed plan and the trust-ir, reading no emitted statement.
    ///
    /// The class's whole marker claim is ONE pair in ONE block, so the sequence is short; what
    /// makes it a sequence rather than a count is that every component of both events is derived
    /// here and compared against [`observe`]'s reading of the FINISHED body:
    ///
    ///   * the BLOCK is the plan's arm — the shim allocates one MIR block per trust-ir block in
    ///     order, so the trust-ir ordinal and the MIR index are the same number, and the empty
    ///     trampoline (appended after all of them) is enumerated here with no events. A marker in
    ///     any other block has no counterpart and fails the body closed;
    ///   * the LIVE lands at assign 0 of that block, and the DEAD after the borrow's own assign
    ///     plus ONE PER `Br` EDGE ARGUMENT — read off the trust-ir terminator here, off the
    ///     finished statements there. Move either marker by a single statement and the two
    ///     sequences differ;
    ///   * the declared TYPE is [`MfTy::Opaque`]: the slot is `&FieldTy`, outside the scalar
    ///     denotation, exactly as wave-29b's reborrow temp is. (See [`MfTy::Opaque`] for the one
    ///     thing that class does not discriminate — it is the same caveat, not a new one.)
    ///   * the USE SITE is `None`. The borrow is an `Rvalue::Ref` (no operand sequence) and its
    ///     single consumer reads THROUGH it (`copy (*t)`, a projected place), and
    ///     [`rvalue_operand_locals`] takes no position for a projected place — so the finished
    ///     body says `None` too.
    ///
    /// Fails CLOSED on any body whose arm terminator is not the `Br` the plan admitted: the plan
    /// and this walk are two readers of one trust-ir, and a disagreement between them is a body
    /// that ships marker-free rather than with a sequence this side cannot place.
    /// **THE PREDICTED SIDE FOR THE WAVE-CK CHECKED-ARITHMETIC CHAIN** — the whole canonical
    /// sequence, from the sealed plan and the trust-ir, reading no emitted statement.
    ///
    /// This class is the first whose markers land in MIR blocks that are NOT the image of a
    /// trust-ir block. `Inst::Assert` splits the chain (`Builder::assert` does the same on the
    /// built side), and the shim's split blocks are `cx.new_block()`s appended after every
    /// trust-ir block — for a ONE-BLOCK body, therefore, unit `k`'s successor is MIR block `k+1`,
    /// counted here and nowhere else. A marker in any other block has no counterpart and fails the
    /// body CLOSED.
    ///
    /// Every component of every event is derived here:
    ///
    ///   * the LIVES all land in block 0 at assign 0 — before the first `<op>WithOverflow` — and
    ///     in REVERSE chain order, because `as_operand` opens the OUTERMOST sub-expression's temp
    ///     first and then recurses into its left operand. Swap that order and the alpha numbering
    ///     (`s0`/`s1`) of the two markers swaps with it, which the comparison sees.
    ///   * the DEAD of link `k` lands in block `k+2`, after ONE assign — the assign that writes
    ///     link `k+1`'s destination (`t = move (tup.0)`, or `_0 = copy (tup.0)` for the returned
    ///     tail). Not after the assign that CONSUMES it: the parent's `assert` splits the block in
    ///     between, which is exactly why this class needed a walk of its own.
    ///   * the declared TYPE comes from the producer's own annotation on `Inst::Overflow`
    ///     ([`ir_ty_token`]); the emitter types the temp from `scalar_ty`, and [`observe`] reads
    ///     the finished body's `local_decls`.
    ///   * the USE SITE of link `k`'s temp is `(k+1, 1, 0)`: block `k+1`, one assign in (its own
    ///     materialisation went first), operand position 0 of `tup = <op>WithOverflow(move t, c)`.
    ///     The right operand is a folded constant and takes no position, and the materialisation's
    ///     own right-hand side is a PROJECTED place, which `rvalue_operand_locals` skips — so the
    ///     first bare-operand mention on the observed side is this one.
    pub(super) fn predict_checked(
        func: &trust_ir::Function,
        plan: &MfCheckedPlan,
    ) -> Result<MfSeq, String> {
        let [blk] = func.blocks.as_slice() else {
            return Err("wave-CK: the checked chain is a one-block class".to_string());
        };
        let (term, body) = blk
            .body
            .split_last()
            .ok_or_else(|| "wave-CK: empty block".to_string())?;
        if !matches!(term.inst, Inst::Return { .. }) {
            return Err("wave-CK: the checked chain must end in a Return".to_string());
        }
        let mut b: MfSeqBuild<MfSlot> = MfSeqBuild::new();
        let mut keys: Vec<(MfSlot, MfKey)> = Vec::new();
        let mut tys: Vec<(MfSlot, MfTy)> = Vec::new();
        let n = plan.chain.len();
        b.block(0);
        // The lives: outermost sub-expression first, i.e. the reverse of the SSA order.
        for (v, t) in plan.marked().iter().rev() {
            let s = MfSlot::Res(*v);
            tys.push((s, ir_ty_token(t)));
            b.mark(true, s);
        }
        // The walk. `k` counts the units actually found in the trust-ir; disagreeing with the plan
        // about how many there are, or about which value each yields, fails the body closed.
        let mut k = 0usize;
        let mut i = 0usize;
        while i < body.len() {
            if let Some((res, _, _, _, _)) = super::checked_unit(body, i) {
                if plan.chain.get(k).map(|(v, _)| *v) != Some(res) {
                    return Err("wave-CK: the trust-ir chain is not the planned chain".to_string());
                }
                // `tup = <op>WithOverflow(l, r)`, then the assert splits into the next MIR block.
                b.assign();
                b.block(k + 1);
                // The destination write: link `k`'s own temp, or `_0` for the returned tail.
                if k + 1 < n {
                    let s = MfSlot::Res(res);
                    keys.push((s, Some((k + 1, 1, 0))));
                }
                b.assign();
                // Built retires link `k-1` right after that write.
                if k >= 1 {
                    b.mark(false, MfSlot::Res(plan.chain[k - 1].0));
                }
                k += 1;
                i += 5;
                continue;
            }
            match &body[i].inst {
                Inst::Const { .. } => i += 1,
                other => {
                    return Err(format!(
                        "wave-CK: no marker sequence model for Inst::{}",
                        super::inst_name(other)
                    ));
                }
            }
        }
        if k != n {
            return Err("wave-CK: the trust-ir carries a different number of chain units than the \
                        plan"
                .to_string());
        }
        Ok(b.finish(&keys, &tys))
    }

    pub(super) fn predict_payload(
        func: &trust_ir::Function,
        plan: &MfPayloadPlan,
    ) -> Result<MfSeq, String> {
        let mut b: MfSeqBuild<MfSlot> = MfSeqBuild::new();
        let keys: Vec<(MfSlot, MfKey)> = Vec::new();
        let mut tys: Vec<(MfSlot, MfTy)> = Vec::new();
        let mut seen = false;
        for (bi, blk) in func.blocks.iter().enumerate() {
            b.block(bi);
            if blk.id != plan.arm {
                continue;
            }
            let Some(Inst::Br { args, .. }) = blk.body.last().map(|n| &n.inst) else {
                return Err("wave-EP: the payload arm's terminator is not a Br".to_string());
            };
            let s = MfSlot::Temp(0);
            // `&FieldTy` — the second marked slot in this shim whose declared type is outside the
            // scalar denotation. See [`MfTy::Opaque`].
            tys.push((s, MfTy::Opaque));
            b.mark(true, s);
            // `t = &(((*P) as V).k)`, then one edge copy per `Br` argument.
            b.assign();
            for _ in args {
                b.assign();
            }
            b.mark(false, s);
            seen = true;
        }
        if !seen {
            return Err("wave-EP: the plan's arm block is not in the body".to_string());
        }
        Ok(b.finish(&keys, &tys))
    }

    /// A storage slot on the PREDICTED side. `Res` is a marked instruction result (named by the
    /// value it holds); `Temp` is a freshly minted operand / write / reborrow temp, numbered in
    /// mint order.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum MfSlot {
        Res(ValueId),
        Temp(u32),
    }

    /// **THE DECLARED TYPE OF A MARKER'S STORAGE SLOT** — the component round 7 did not carry,
    /// and the one the oracle prints as the `{ty}` of `s{alpha}:{ty}`.
    ///
    /// Round 7 wrote that this "cannot be rendered here — the predicted side has no MIR locals",
    /// and used the slot's use site as a stand-in. The premise is true and the conclusion does not
    /// follow: this side does not need a rustc `Ty`, it needs a TOKEN the two sides can both spell.
    /// Every value this shim can put a marker on carries a type on the trust-ir instruction that
    /// DEFINES it (`BinOp.ty`, `UnOp.ty`, `Load.ty`, `Cast.dst_ty`, `ExtractField.ty`, and `ICmp`,
    /// whose result is always `Ty::Bool`) or on its block's parameter list; the observed side reads
    /// the FINISHED body's `local_decls`. The token is the index into [`super::SCALAR_CANDS`] —
    /// the shim's own scalar denotation, which v25 B1 made global and injective, so `Scalar(i)` on
    /// one side names the same rustc type as `Scalar(i)` on the other.
    ///
    /// **THE TWO SIDES DERIVE IT FROM DIFFERENT PLACES, WHICH IS THE ENTIRE POINT.** The emitter
    /// types an operand temp from `place.ty(&self.local_decls, self.tcx)` — rustc's answer — and
    /// this side types it from the producer's own annotation. The eighth review's `ptype` attack
    /// (mint the operand temp at the same-width OPPOSITE SIGNEDNESS: 261 admitted-and-wrong bodies
    /// on the probe corpus and nine in shipped `clean-kernel`, with round 7's law green and the
    /// whole unit suite passing) moves the first and not the second.
    ///
    /// WHAT IT DOES NOT DISCRIMINATE, stated where the type is defined rather than left to be
    /// found: [`MfTy::Opaque`] is ONE class, not a rendering. Two distinct non-scalar declared
    /// types compare EQUAL. Exactly one marked slot in this shim is non-scalar — the interior-borrow
    /// reborrow temp, declared `&FieldTy` — and it is a single pair in a single-`&place` body class.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub(super) enum MfTy {
        /// One of the sixteen body scalars, by index into [`super::SCALAR_CANDS`].
        Scalar(u8),
        /// A declared type outside the scalar denotation (see the class caveat above).
        Opaque,
        /// The predicted side could not type the slot from the trust-ir at all. [`observe`] never
        /// produces it — every local in a finished body has a declaration — so it can only ever
        /// fail a body CLOSED, never admit one.
        Unknown,
    }

    /// The PREDICTED side's spelling: a trust-ir type, straight from the producer's annotation.
    pub(super) fn ir_ty_token(ty: &Ty) -> MfTy {
        match super::SCALAR_CANDS.iter().position(|c| c == ty) {
            Some(i) => MfTy::Scalar(i as u8),
            None => MfTy::Opaque,
        }
    }

    /// The OBSERVED side's spelling: a rustc type, read off the finished body's local declaration.
    ///
    /// `super::scalar_rustc_ty` is the shim's denotation and is the one thing the two spellings
    /// have in common. An edit to IT moves both sides at once — and is caught outside this file, by
    /// the oracle, which compares the derived local's declared type against BUILT's
    /// (`mir_differential::canon_param_ty`) and reads no plan and no trust-ir.
    fn rustc_ty_token<'tcx>(tcx: TyCtxt<'tcx>, ty: RustcTy<'tcx>) -> MfTy {
        match super::SCALAR_CANDS.iter().position(|c| super::scalar_rustc_ty(tcx, c) == Some(ty)) {
            Some(i) => MfTy::Scalar(i as u8),
            None => MfTy::Opaque,
        }
    }

    /// **WHERE A SLOT IS CONSUMED** — `(MIR block, the number of assignments before the consuming
    /// assignment in that block, the slot's position in that assignment's operand sequence)`, or
    /// `None` for a slot no assignment reads as a bare operand (a `CondBr` condition, consumed by
    /// the terminator; a reborrow temp, read through a `Rvalue::Ref`).
    ///
    /// This is one of the two components that make the sequence see a RELABELLING, and it is kept
    /// alongside [`MfTy`] because the two catch different things. Alpha-renaming by first
    /// appearance — which is how the oracle names a slot, and how [`MfSeqBuild`] names one — is by
    /// construction blind to two slots trading places: reverse the aggregate field walk AND the
    /// retirement run and the alpha sequence is character for character the same one. The declared
    /// TYPE separates two traded slots of DIFFERENT types (which is how the oracle sees it); this
    /// key separates two traded slots of the SAME type, which no type can. It is round 6's
    /// `retirement_order` derivation folded INTO the event instead of standing beside the law as a
    /// rule with its own vacuity conditions.
    ///
    /// **AND ON TODAY'S CORPUS IT IS UNWITNESSED — reported, not claimed.** Round 7 witnessed this
    /// component at 19 admitted-and-wrong bodies under `aggrev` (the aggregate field walk
    /// reversed). Round 8 carries the declared type as well, and the type subsumes that witness:
    /// delete this key and re-run `aggrev` and `aswap2` (reverse the walk AND re-reverse the dead
    /// list, which is the shape built to preserve the alpha sequence) and BOTH give
    /// admitted-and-wrong 0 on 1,570 bodies at both optimisation levels — 122 of them still fail
    /// closed, through the type. It stays because what it covers is not what the type covers: a
    /// trade of two slots with the SAME declared type is invisible to the type by construction,
    /// and no body in this corpus happens to be one. It is kept for that shape and for no measured
    /// one, and anyone who wants it gone now has the measurement.
    type MfKey = Option<(usize, usize, usize)>;

    /// One marker, canonically: `(MIR block index, assigns already seen in that block, live?,
    /// alpha-renamed slot, the slot's DECLARED TYPE, the slot's use site)`. The first five are the
    /// oracle's own line, component for component; the sixth is round 6's retirement order, folded
    /// in.
    type MfEvent = (usize, usize, bool, u32, MfTy, MfKey);

    /// **THE CANONICAL MARKER SEQUENCE.** The ONE type both sides of the law are expressed in, so
    /// the comparison is a single `==` between two independently derived values.
    #[derive(Clone, Debug, Default, PartialEq, Eq)]
    pub(super) struct MfSeq(Vec<MfEvent>);

    impl MfSeq {
        pub(super) fn len(&self) -> usize {
            self.0.len()
        }

        pub(super) fn is_empty(&self) -> bool {
            self.0.is_empty()
        }

        /// The first position at which the two sequences differ, rendered the way the oracle
        /// renders its own first difference — so a refusal message can be read against a
        /// `markers differ:` line without translation.
        pub(super) fn first_diff(&self, other: &MfSeq) -> String {
            fn show(e: Option<&MfEvent>) -> String {
                match e {
                    Some((blk, at, live, slot, ty, key)) => format!(
                        "mk b{blk}.{at}:{} s{slot}:{}@{}",
                        if *live { "live" } else { "dead" },
                        match ty {
                            MfTy::Scalar(i) => {
                                format!("{:?}", super::SCALAR_CANDS[*i as usize])
                            }
                            MfTy::Opaque => "opaque".to_string(),
                            MfTy::Unknown => "?".to_string(),
                        },
                        match key {
                            Some((kb, ka, ko)) => format!("b{kb}.{ka}:{ko}"),
                            None => "term".to_string(),
                        }
                    ),
                    None => "<end>".to_string(),
                }
            }
            for i in 0..self.0.len().max(other.0.len()) {
                if self.0.get(i) != other.0.get(i) {
                    return format!(
                        "line {i}: predicted `{}` vs derived `{}`",
                        show(self.0.get(i)),
                        show(other.0.get(i))
                    );
                }
            }
            "identical".to_string()
        }
    }

    /// The builder BOTH sides use. The canonical position rule (assignments before the marker), the
    /// alpha renaming (first appearance wins, as `canon_markers` does it) and the use-site lookup
    /// are written once, here, so they cannot drift between the predicted and the observed side;
    /// the two sides differ only in what they walk and in how a slot is spelled.
    struct MfSeqBuild<S> {
        raw: Vec<(usize, usize, bool, S)>,
        blk: usize,
        assigns: usize,
    }

    impl<S: Copy + PartialEq> MfSeqBuild<S> {
        fn new() -> Self {
            MfSeqBuild { raw: Vec::new(), blk: 0, assigns: 0 }
        }
        fn block(&mut self, blk: usize) {
            self.blk = blk;
            self.assigns = 0;
        }
        /// The assign ordinal the NEXT assignment in this block will have.
        fn at(&self) -> usize {
            self.assigns
        }
        fn assign(&mut self) {
            self.assigns += 1;
        }
        fn mark(&mut self, live: bool, slot: S) {
            self.raw.push((self.blk, self.assigns, live, slot));
        }
        fn finish(self, keys: &[(S, MfKey)], tys: &[(S, MfTy)]) -> MfSeq {
            let mut alpha: Vec<S> = Vec::new();
            let mut out: Vec<MfEvent> = Vec::new();
            for (blk, at, live, slot) in self.raw {
                let a = match alpha.iter().position(|s| *s == slot) {
                    Some(k) => k,
                    None => {
                        alpha.push(slot);
                        alpha.len() - 1
                    }
                };
                let key = keys.iter().find(|(s, _)| *s == slot).and_then(|(_, k)| *k);
                // A slot whose type neither side registered is `Unknown`, which `observe` never
                // produces — so an unmodelled slot fails the body CLOSED rather than comparing
                // equal to whatever the other side found.
                let ty = tys
                    .iter()
                    .find(|(s, _)| *s == slot)
                    .map_or(MfTy::Unknown, |(_, t)| *t);
                out.push((blk, at, live, a as u32, ty, key));
            }
            MfSeq(out)
        }
    }

    /// The operand temps ONE instruction mints, in evaluation order, and the slots its retirement
    /// run must name. Outside the operand-temp class `mf_operand` IS `ShimCx::operand`: no temp, no
    /// marker, no assign — which is why `in_class` gates the whole thing rather than just the
    /// marker.
    fn mint_operands(
        b: &mut MfSeqBuild<MfSlot>,
        temps: &mut u32,
        tys: &mut Vec<(MfSlot, MfTy)>,
        needs: &HashSet<ValueId>,
        def_of: &HashMap<ValueId, &Inst>,
        ty_of: &HashMap<ValueId, MfTy>,
        ops: &[ValueId],
        in_class: bool,
    ) -> Vec<MfSlot> {
        let mut deads = Vec::new();
        if !in_class {
            return deads;
        }
        for o in ops {
            // A constant operand is folded in place: no temp, no assign, no marker — and it takes
            // no position in the consuming assignment's operand sequence either.
            if matches!(def_of.get(o), Some(Inst::Const { .. })) {
                continue;
            }
            // An already-marked temp is MOVED out of — no new temp and no live, only the dead.
            if needs.contains(o) {
                let s = MfSlot::Res(*o);
                tys.push((s, ty_at(ty_of, *o)));
                deads.push(s);
                continue;
            }
            let s = MfSlot::Temp(*temps);
            *temps += 1;
            // `mf_operand` mints `tmp: place.ty(..)` and copies the operand into it, so the temp's
            // declared type IS the operand's — which this side reads off the trust-ir.
            tys.push((s, ty_at(ty_of, *o)));
            b.mark(true, s);
            b.assign();
            deads.push(s);
        }
        deads
    }

    /// The type token of one value, or [`MfTy::Unknown`] when the trust-ir carries none. `Unknown`
    /// is a token [`observe`] cannot produce, so a value this side cannot type fails the body
    /// CLOSED — it is never silently equal to whatever the finished body declared.
    fn ty_at(ty_of: &HashMap<ValueId, MfTy>, v: ValueId) -> MfTy {
        ty_of.get(&v).copied().unwrap_or(MfTy::Unknown)
    }

    /// The consuming assignment, the use sites it fixes, and the retirement run after it — in
    /// REVERSE operand order, unless this instruction defines the block's `CondBr` condition, in
    /// which case built retires the run at the ENTRY of both arms and so does the emitter.
    fn close_group(
        b: &mut MfSeqBuild<MfSlot>,
        keys: &mut Vec<(MfSlot, MfKey)>,
        bi: usize,
        deads: &[MfSlot],
        is_cond: bool,
        br: Option<MfBranch>,
        entry: &mut HashMap<BlockId, Vec<MfSlot>>,
    ) {
        let at = b.at();
        for (oi, s) in deads.iter().enumerate() {
            keys.push((*s, Some((bi, at, oi))));
        }
        b.assign();
        let order: Vec<MfSlot> = deads.iter().rev().copied().collect();
        if is_cond {
            if let Some(x) = br {
                entry.entry(x.then_target).or_default().extend(order.iter().copied());
                entry.entry(x.else_target).or_default().extend(order);
            }
            return;
        }
        for d in order {
            b.mark(false, d);
        }
    }

    /// `recognize_field_write`'s SHAPE, re-derived from the trust-ir alone: a struct load, an
    /// insert into it, and a store back through the same pointer. Returns the stored field's value
    /// id (whose defining instruction decides whether built gives it an operand temp).
    fn write_triple(nodes: &[trust_ir::InstrNode], i: usize) -> Option<ValueId> {
        if i + 2 >= nodes.len() {
            return None;
        }
        let Inst::Load { ty: Ty::Struct(_), ptr, volatile: false, align: None } = &nodes[i].inst
        else {
            return None;
        };
        let agg = *nodes[i].results.first()?;
        let Inst::InsertField { aggregate, value, .. } = &nodes[i + 1].inst else {
            return None;
        };
        if *aggregate != agg {
            return None;
        }
        let new = *nodes[i + 1].results.first()?;
        let Inst::Store { ptr: sptr, value: sval, volatile: false, align: None, .. } =
            &nodes[i + 2].inst
        else {
            return None;
        };
        (*sptr == *ptr && *sval == new).then_some(*value)
    }

    /// The ONE construction of a storage-marker `StatementKind` in the program. `observe`'s match
    /// below is the only other place either variant is spelled, and `marker_gate_invariant_tests`
    /// pins that those two are all of them — so every storage marker in a derived body was built
    /// here, and every one of them is read there.
    pub(super) fn marker_kind<'tcx>(local: Local, live: bool) -> StatementKind<'tcx> {
        if live { StatementKind::StorageLive(local) } else { StatementKind::StorageDead(local) }
    }

    /// **THE OBSERVED SIDE OF THE LAW** — the canonical marker sequence of the FINISHED body, and a
    /// pure function of it. No plan, no counter, no lowering decision is read.
    ///
    /// The walk is the oracle's, restated on rustc MIR: markers are positioned by the number of
    /// `Assign`s already seen in their block, slots are alpha-renamed by first appearance
    /// (`mir_differential::canon_markers`, LEDGER L13), each slot's DECLARED TYPE is read off the
    /// finished body's `local_decls` exactly as the oracle reads it off the extracted body's, and
    /// each slot's use site is read off the assignment that moves it out. Two deliberate
    /// differences, both of them STRICTER than the oracle:
    ///
    ///   * blocks are walked in MIR index order rather than in the oracle's DFS preorder. The two
    ///     are a bijection over one body, so the sequence decides the same question, and this side
    ///     does not carry a second copy of the oracle's successor rule.
    ///   * ANY statement that is not an `Assign` or a storage marker fails the body CLOSED. The
    ///     oracle skips `Nop`/`PlaceMention` as position-neutral, and the seventh review's `H'`
    ///     attack used exactly that: one `Nop` between two retirements made round 6's contiguous-run
    ///     rule vacuous on 316 bodies while the oracle saw nothing. This shim emits `Assign`s and
    ///     markers and nothing else (`push_stmt` has two callers, both here), so refusing the rest
    ///     costs nothing and closes the evasion outright.
    pub(super) fn observe<'tcx>(
        tcx: TyCtxt<'tcx>,
        blocks: &IndexVec<BasicBlock, BasicBlockData<'tcx>>,
        decls: &IndexVec<Local, LocalDecl<'tcx>>,
    ) -> Result<MfSeq, String> {
        observe_with(blocks, |l| match decls.get(l) {
            Some(d) => rustc_ty_token(tcx, d.ty),
            // A marker on a local with no declaration: the oracle refuses that body too
            // (`marker on missing local`). `Unknown` fails it CLOSED here.
            None => MfTy::Unknown,
        })
    }

    /// The walk itself, over the finished blocks and one total function from a storage slot to its
    /// declared type — a total function of those two, so `marker_law_tests` can exercise it on
    /// synthetic MIR without a compiler. [`observe`] is the ONE shipped instantiation and supplies
    /// the finished body's own `local_decls`.
    pub(super) fn observe_with<'tcx>(
        blocks: &IndexVec<BasicBlock, BasicBlockData<'tcx>>,
        ty_of: impl Fn(Local) -> MfTy,
    ) -> Result<MfSeq, String> {
        let mut b: MfSeqBuild<Local> = MfSeqBuild::new();
        let mut keys: Vec<(Local, MfKey)> = Vec::new();
        let mut tys: Vec<(Local, MfTy)> = Vec::new();
        for (bb, data) in blocks.iter_enumerated() {
            b.block(bb.index());
            for st in &data.statements {
                match &st.kind {
                    StatementKind::Assign(assign) => {
                        let at = b.at();
                        for (oi, l) in
                            rvalue_operand_locals(&assign.1).into_iter().enumerate()
                        {
                            // First use wins: this shim moves every marked temp out exactly once.
                            if !keys.iter().any(|(k, _)| *k == l) {
                                keys.push((l, Some((bb.index(), at, oi))));
                            }
                        }
                        b.assign();
                    }
                    StatementKind::StorageLive(l) => {
                        tys.push((*l, ty_of(*l)));
                        b.mark(true, *l);
                    }
                    StatementKind::StorageDead(l) => {
                        tys.push((*l, ty_of(*l)));
                        b.mark(false, *l);
                    }
                    other => {
                        return Err(format!(
                            "the derived body carries a non-assignment statement ({other:?}); this \
                             shim emits assignments and storage markers only, and a marker's \
                             canonical position is the number of assignments before it"
                        ));
                    }
                }
            }
        }
        Ok(b.finish(&keys, &tys))
    }

    /// The operand locals of one rvalue, in evaluation order. The match is TOTAL on purpose: a new
    /// `Rvalue` variant is a compile error here rather than a silent hole in the use sites above.
    /// Projected places are skipped — a marked temp is always used whole, as `Operand::Move(t)`.
    fn rvalue_operand_locals(rv: &Rvalue<'_>) -> Vec<Local> {
        fn local_of(op: &Operand<'_>, out: &mut Vec<Local>) {
            if let Operand::Copy(p) | Operand::Move(p) = op {
                if p.projection.is_empty() {
                    out.push(p.local);
                }
            }
        }
        let mut out = Vec::new();
        match rv {
            Rvalue::Use(o, _)
            | Rvalue::Repeat(o, _)
            | Rvalue::Cast(_, o, _)
            | Rvalue::UnaryOp(_, o)
            | Rvalue::WrapUnsafeBinder(o, _) => local_of(o, &mut out),
            Rvalue::BinaryOp(_, ops) => {
                local_of(&ops.0, &mut out);
                local_of(&ops.1, &mut out);
            }
            Rvalue::Aggregate(_, ops) => {
                for o in ops.iter() {
                    local_of(o, &mut out);
                }
            }
            // Place-valued and operand-free rvalues carry no operand sequence for a marker slot to
            // take a position in.
            Rvalue::Ref(..)
            | Rvalue::ThreadLocalRef(..)
            | Rvalue::RawPtr(..)
            | Rvalue::Discriminant(..)
            | Rvalue::CopyForDeref(..)
            | Rvalue::Reborrow(..) => {}
        }
        out
    }
    impl<'tcx> super::ShimCx<'tcx> {
        /// The sole statement-insertion boundary in the shim. Every statement, ordinary or marker,
        /// goes through here, and `marker_gate_invariant_tests` pins that there is exactly one.
        pub(super) fn push_stmt(&mut self, bb: BasicBlock, kind: StatementKind<'tcx>) {
            self.blocks[bb].statements.push(Statement::new(self.source_info, kind));
        }

        /// The ONE emission of a storage-marker statement in the program. Every caller is one of
        /// the five plan-consulting methods below, in this module.
        fn push_marker(&mut self, bb: BasicBlock, local: Local, live: bool) {
            self.push_stmt(bb, marker_kind(local, live));
        }

        /// A marked result's `StorageLive`. **The plan's per-VALUE question and the emission are
        /// one operation** — this is the fifth review's second attack, closed by construction: an
        /// arm cannot ask for the class's permission and then emit for an unplanned value, because
        /// the only thing it can call is this, and this asks about `r`.
        pub(super) fn mf_mark_result(&mut self, bb: BasicBlock, r: ValueId, local: Local) {
            if !self.mf_plans.marks_result(r) {
                return;
            }
            self.push_marker(bb, local, true);
            self.mf_live.insert(r, local);
        }

        /// Is the body in the operand-temp class? Asked by [`super::ShimCx::mf_operand`] BEFORE it
        /// mints a temp — outside the class it must not mint one at all, marker or no marker.
        pub(super) fn mf_operand_class(&self) -> bool {
            self.mf_plans.operand_class()
        }

        /// An operand temp's `StorageLive`.
        pub(super) fn mf_mark_operand(&mut self, bb: BasicBlock, local: Local) {
            if !self.mf_plans.operand_class() {
                return;
            }
            self.push_marker(bb, local, true);
        }

        /// The retirement of operand/result temps — in place, or drained at an arm/join entry.
        pub(super) fn mf_retire_at(&mut self, bb: BasicBlock, locals: &[Local]) -> bool {
            if !self.mf_plans.operand_class() {
                return false;
            }
            for l in locals {
                self.push_marker(bb, *l, false);
            }
            true
        }

        /// Does the field-write plan own this body?
        pub(super) fn mf_write_admits(&self) -> bool {
            self.mf_plans.write.is_some()
        }

        /// One half of the field-write arm's pair.
        pub(super) fn mf_mark_write(&mut self, bb: BasicBlock, local: Local, live: bool) -> bool {
            if self.mf_plans.write.is_none() {
                return false;
            }
            self.push_marker(bb, local, live);
            true
        }

        /// Does the interior-borrow plan own this body?
        pub(super) fn mf_borrow_admits(&self) -> bool {
            self.mf_plans.borrow
        }

        /// One half of the interior-borrow reborrow temp's pair.
        pub(super) fn mf_mark_borrow(&mut self, bb: BasicBlock, local: Local, live: bool) -> bool {
            if !self.mf_plans.borrow {
                return false;
            }
            self.push_marker(bb, local, live);
            true
        }

        /// Trust (wave-EP): does the payload plan own THIS producer block's payload triple? The
        /// emitter asks before it mints anything — outside the plan the T2b arm keeps its
        /// pre-wave form (bind the PLACE, no temp, no borrow, no marker), so a body the plan
        /// declines is bit-identical to what it was.
        pub(super) fn mf_payload_arm(&self, blk: BlockId) -> bool {
            self.mf_plans.payload.is_some_and(|p| p.arm == blk)
        }

        /// Trust (wave-EP): which producer block's incoming switch edge does the payload plan want
        /// routed through an empty trampoline? See [`super::MfPayloadPlan::tramp`].
        pub(super) fn mf_payload_tramp_block(&self) -> Option<BlockId> {
            self.mf_plans.payload.map(|p| p.tramp)
        }

        /// Trust (wave-CK): the checked chain's marked links, in SSA order, with the producer's
        /// own type annotation. The emitter needs both — the type to declare the temp, the order to
        /// open them in built's REVERSE order — and it can get them nowhere else, because the plan
        /// is private to this module.
        pub(super) fn mf_checked_chain(&self) -> Vec<(ValueId, Ty)> {
            self.mf_plans.checked.as_ref().map(|p| p.marked().to_vec()).unwrap_or_default()
        }

        /// Trust (wave-CK): the chain link evaluated immediately before `r`, i.e. the temp whose
        /// retirement built schedules right after `r`'s destination write. `None` outside the class,
        /// for the first link, and for a value the plan does not name.
        pub(super) fn mf_checked_pred(&self, r: ValueId) -> Option<ValueId> {
            self.mf_plans.checked.as_ref()?.pred(r)
        }

        /// One half of a checked-chain link's pair. As at every other emission site in this module
        /// the plan's per-VALUE question and the push are ONE operation: an arm cannot take the
        /// class's permission and then mark a value the chain does not contain.
        pub(super) fn mf_mark_checked(
            &mut self,
            bb: BasicBlock,
            r: ValueId,
            local: Local,
            live: bool,
        ) -> bool {
            if !self.mf_plans.checked.as_ref().is_some_and(|p| p.marks(r)) {
                return false;
            }
            self.push_marker(bb, local, live);
            true
        }

        /// One half of the payload borrow temp's pair. Like every other emission method here the
        /// plan's question and the push are ONE operation, so an arm cannot take the class's
        /// permission and then mark a slot in a block the plan does not own.
        pub(super) fn mf_mark_payload(
            &mut self,
            bb: BasicBlock,
            blk: BlockId,
            local: Local,
            live: bool,
        ) -> bool {
            if !self.mf_payload_arm(blk) {
                return false;
            }
            self.push_marker(bb, local, live);
            true
        }
    }
}
// MARKER-GATE-END

// Trust (lane MF-R5): the gate exports exactly two names — the SEALED PLANS the shim carries and
// (through `mf_gate::observe`) the finished-body walk the law calls. There is no marker type, no
// lease type and no site enum to import, because none of them exists any more: the only way to
// reach a block with a storage marker is one of the five plan-consulting methods in `mf_gate`.
use mf_gate::MfPlans;

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
    /// Trust (lane MF-R5): **THE SEALED PLANS** — every marker permission this body has, in one
    /// value whose fields are private to [`mf_gate`] and whose only constructor
    /// ([`mf_gate::MfPlans::seal`]) is a pure function of the body. Round 4 kept these as three
    /// plain `ShimCx` fields; the fifth review's first attack wrote one of them (`cx.mf_borrow =
    /// true`) and took a genuine lease from it, putting 46 bodies into admitted-and-wrong with
    /// every layer green. That line does not compile here, and re-sealing recomputes the same
    /// answer.
    mf_plans: MfPlans,
    /// Trust (wave-MF): results whose marker-carrying temp is currently `StorageLive` and still
    /// awaiting its `StorageDead`. Emptied by the consuming instruction; a non-empty map at body
    /// end is an unbalanced marker and fails the body CLOSED rather than shipping it.
    mf_live: HashMap<ValueId, Local>,
    /// Trust (lane K): the producer block currently being lowered — the key into
    /// `mf_branch.branch`. `None` before the block walk starts.
    mf_cur_blk: Option<BlockId>,
    /// Trust (lane K): set by [`ShimCx::mf_result_temp`] when the instruction it is minting for
    /// defines the current block's `CondBr` condition, and consumed by [`ShimCx::mf_retire`],
    /// which then DEFERS that instruction's operand temps to the two arm entries instead of
    /// retiring them in place. Rewritten (not or-ed) at every result temp, so it cannot leak.
    mf_defer_deads: bool,
    /// Trust (lane K): `StorageDead`s scheduled at the ENTRY of a producer block — the condition
    /// operand temps on each arm, the condition result temp on the join. Filled while lowering
    /// the head block, drained when the block itself is reached (the plan proves every arm/join
    /// is lowered after its head). A non-empty map at body end fails the body CLOSED.
    mf_entry_deads: HashMap<BlockId, Vec<Local>>,
    /// Trust (wave-EP): the payload borrow temp minted in the block currently being lowered,
    /// awaiting the `StorageDead` built puts AFTER the assign that consumes it — which is the
    /// arm's `Br` edge copy, so the retirement is emitted by the `Br` arm just before it
    /// terminates the block. `Some` for at most one block at a time; the plan admits exactly one
    /// payload triple in the whole body, and a second mint in the same block would overwrite a
    /// pending local and leave it unretired, which the marker law then refuses.
    mf_payload_dead: Option<Local>,
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
/// Trust (wave-MF, OPERAND-TEMP MARKER FIDELITY): the per-body plan that decides whether this
/// shim may reproduce built's `StorageLive`/`StorageDead` around rvalue OPERAND temps, and which
/// SSA results carry one. Returns `None` (today's behaviour: emit no markers at all) unless the
/// whole body is inside the planned class — a partial plan would leave an unbalanced
/// `StorageLive`, which is worse than none.
///
/// WHAT BUILT DOES, measured (`-Zdump-mir=all` on the shapes in
/// `crates/trust-thir-lower/probes/mf_operand_temps.rs`): `rustc_mir_build`'s `as_operand`
/// sends every NON-CONSTANT operand of an rvalue through `as_temp`, which emits
/// `StorageLive(_t); _t = <operand>` and schedules `StorageDead(_t)` for the end of the operand's
/// region scope — so for a straight-line scalar body the deads land immediately after the
/// consuming assign, in REVERSE operand order. A constant operand is folded in place
/// (`Category::Constant`), and the OUTERMOST expression is written straight into the destination
/// with no temp (`expr_into_dest`). Verbatim built MIR for `AllocationId::is_null`:
///
/// ```text
/// StorageLive(_2); _2 = copy (_1.0: u64); _0 = Eq(move _2, const 0_u64); StorageDead(_2);
/// ```
///
/// THE ADMITTED CLASS, and why each condition is load-bearing:
///
///   * **`func.scopes.is_none()`** — the body opens no lexical `let` scope. This is the
///     firewall, and it replaces the module doc's (now stale) infeasibility argument. A source
///     `let` mints a NAMED local with its own markers plus a `FakeRead`, and the trust-ir
///     INSTRUCTION stream does not distinguish `self.0 == 0` from `let x = self.0; x == 0` — both
///     lower to `extractfield; const; icmp; ret`. What DOES distinguish them, since trust-ir v33
///     (C2-scopes), is the scope table: the let-bearing twin carries
///     `Some([root, {parent: 0}])` and the direct one carries `None`. The producer "only ever
///     opens `let`-visibility scopes" (see `build_source_scopes`), so `scopes.is_none()` proves
///     the absence of the one construct whose markers this plan cannot see.
///   * **exactly one block** — a marker's canonical position is (fine block index, assigns seen).
///     Cross-block marker lifetimes (built's `switchInt` operand temp dies in the join block) are
///     a different reconstruction and are deliberately out.
///   * **every instruction in {Const, ExtractField, Load, BinOp, ICmp, UnOp, Cast, InsertField,
///     Return}** — exactly the arms taught to emit operand temps below, plus the two that mint no
///     MIR statement. `Overflow`/`Assert`/`Select`/`Call`/`GEP`/`Alloca`/`Store`/... are OUT: they
///     either split the MIR chain or consume a marker temp at a site that would not retire it.
///   * **every instruction result used exactly once** — built evaluates a source expression TREE;
///     a value used twice is a producer CSE of what built spells (and marks) twice, and a value
///     used zero times is dead code built never materialised.
///   * **an `InsertField` chain, if present, is the WHOLE return value and is well-formed** — see
///     [`agg_field_order_ok`], which is lane L's addition and carries its own measured argument.
///
/// The returned set is the results that need a marker-carrying temp: an instruction result whose
/// single use is another INSTRUCTION (built's `as_operand`→`as_temp`). A result consumed by the
/// `Return` terminator gets none — built writes the outermost rvalue straight into `_0`.
///
/// NOT A RELAXATION. Everything here only ADDS statements to the derived body; the comparator's
/// exact marker channel (`mir_differential::canon_markers`) is untouched and still decides. A
/// wrong plan yields a wrong marker sequence, `markers_exact: false`, and no flip — which is
/// precisely the state the body is in today.
///
/// THAT BOUNDARY IS NOW A RULE (lane MF-ZERO, 2026-08-13). This walks the trust-ir instruction
/// list in linear SSA order, so it reproduces built only when built's evaluation order agrees. It
/// does for a LEFT-nested tree (`(a & b) == c`) and does not for a RIGHT-nested one
/// (`a == (b & c)`), where built lives the outer left operand's temp BEFORE the right
/// sub-expression's. Until this lane the right-nested case was ADMITTED and simply kept
/// `markers_exact: false` — a wrong derivation the plan offered and only the oracle stopped.
/// Ordering rule (2) below refuses it, and refuses it CONSTANT-TOLERANTLY so that the correct
/// `0 == (b & c)` keeps its exactness.
///
/// # Lane L (aggregate construction + `Inst::Load`), 2026-08-12
///
/// AGGREGATES. `-Zdump-mir=all` on the real shapes (`probes/mf_aggregate_temps.rs`, committed)
/// shows an aggregate is not a new discipline at all — it is `as_operand` one level up. The
/// aggregate itself is the OUTERMOST expression, so it goes straight into `_0` with no temp; each
/// non-constant FIELD operand goes through `as_operand`→`as_temp` in field order and is retired
/// after the aggregate assign in REVERSE field order. Verbatim built MIR for `FlatFlags::with`
/// (`FlatFlags(self.0 | other.0)`):
///
/// ```text
/// StorageLive(_3);
/// StorageLive(_4); _4 = copy (_1.0: u8);
/// StorageLive(_5); _5 = copy (_2.0: u8);
/// _3 = BitOr(move _4, move _5); StorageDead(_5); StorageDead(_4);
/// _0 = FlatFlags(move _3); StorageDead(_3);
/// ```
///
/// A CONSTANT field folds in place and takes no temp (`NodeId(7)` builds to a bare
/// `_0 = NodeId(const 7_u32)` with ZERO markers), which is why admitting the class cannot cost the
/// all-const constructors their existing `markers_exact: true`.
///
/// `Inst::LOAD`. Measured: for a shared-ref scalar param, `*p == 0` builds to
/// `StorageLive(_2); _2 = copy (*_1); _0 = Eq(move _2, const 0_u64); StorageDead(_2)` — the load
/// IS the operand temp, i.e. exactly the class wave-MF already discharges for `ExtractField`, and
/// the shim's `Inst::Load` arm was already minting that very temp (`_t = copy (*_p)`) without the
/// markers. So `Load` is the SAME mechanism, not a new one, and it joins the marked set here.
/// **It does not, however, unblock `BigNat::is_zero::{closure#0}`** — see the boundary note on
/// [`ShimCx::mf_result_temp`]'s caller in the `Inst::Load` arm.
///
/// Trust (lane N review, 2026-08-13): that sameness is a claim about the operand POSITION, not
/// about every `Inst::Load`. A load that feeds a NESTED field expression inherited the ordering
/// hazard recorded on [`agg_field_order_ok`] — measured, `Inner(*p as u32)` lives built's u32 CAST
/// temp first and this shim's u8 LOAD temp first — and a load minted by a DESTRUCTURING pattern is
/// a binding local rather than an operand temp.
///
/// The FIRST of those is now refused BY THE PLAN, by ordering rule (1) below (a marked result may
/// not take a marked operand): `Inner(*p as u32)` is a marked `Cast` over a marked `Load`. The
/// SECOND — a load minted by a DESTRUCTURING PATTERN — is refused by the plan too since lane
/// MF-ZERO, but not from the instruction stream, because it genuinely is not there: `fn f(&l:
/// &u64) { l == 0 }` and `fn f(p: &u64) { *p == 0 }` lower to byte-identical trust-ir and both
/// carry `func.scopes.is_none()`. [`source_form_admits`] reads the PARAMETER PATTERNS and refuses
/// the first, which is the one construct the `scopes.is_none()` firewall names and cannot see.
fn plan_operand_marker_temps(func: &trust_ir::Function) -> Option<HashSet<ValueId>> {
    // The firewall: any lexical `let` scope puts the body outside the plan.
    if func.scopes.is_some() {
        return None;
    }
    let [blk] = func.blocks.as_slice() else { return None };
    let nodes = &blk.body;
    let (term, body) = nodes.split_last()?;
    // Trust (LANE PCA plan-clause audit, 2026-08-17): **`if !matches!(term.inst, Inst::Return {
    // .. }) { return None }` IS RETIRED HERE.** It was stated three times. `operands_of` below is
    // asked about EVERY node including this terminator and has no `Br`/`CondBr`/`Switch` arm
    // (`_ => return None`), and the `ret_vals` binding twenty lines down re-matches the same
    // terminator with the same `_ => return None`. Either one refuses exactly the bodies this
    // clause refused. MEASURED: reached 5,936 times across a 2,002-body probe corpus and
    // `clean-kernel`'s 13,774, fired ZERO; deleting it moves 0 rows on either corpus.
    // Operand positions of the admitted instruction set, and of `Return`.
    fn operands_of(inst: &Inst) -> Option<Vec<ValueId>> {
        Some(match inst {
            Inst::Const { .. } => vec![],
            Inst::ExtractField { aggregate, .. } => vec![*aggregate],
            // Trust (lane L): a plain scalar load. `volatile`/`align` are refused by the
            // `Inst::Load` arm itself; refusing them HERE too keeps the plan's admitted set and
            // the emitter's admitted set the same set, which is the property the whole design
            // rests on (an admitted plan whose emitter declines leaves a marker unbalanced).
            Inst::Load { ptr, volatile: false, align: None, .. } => vec![*ptr],
            Inst::BinOp { lhs, rhs, .. } | Inst::ICmp { lhs, rhs, .. } => vec![*lhs, *rhs],
            Inst::UnOp { operand, .. } | Inst::Cast { operand, .. } => vec![*operand],
            // Trust (lane L): a constructor-chain link. Both positions are real uses; the
            // exactly-once rule below then forbids a DAG-shaped or dead chain, and
            // `agg_field_order_ok` proves the chain is the one the Return arm collapses.
            Inst::InsertField { aggregate, value, .. } => vec![*aggregate, *value],
            Inst::Return { values } => values.clone(),
            _ => return None,
        })
    }
    // Trust (lane L): a SHIFT is refused outright, and this closes a latent hazard wave-MF
    // inherited rather than one lane L introduces. With overflow checks OFF the shim recognizes
    // `Cast + BinOp(Shl|LShr|AShr)` as ONE unit at the top of the node loop
    // (`shift_value_cast_pair`) and reads its operands through `cx.operand`, NOT `mf_operand` —
    // so a marked temp feeding a shift would never be retired and the body would fail closed at
    // the `mf_live` check, LOSING an `agreed` verdict. With checks ON the idiom carries an
    // `Inst::Assert`, which `operands_of` already refuses. Refusing the shift costs no marker
    // exactness that was reachable (the pair arm emits no markers either way).
    //
    // Trust (lane N review, 2026-08-13): "no marker exactness that was reachable" is true OF THE
    // MEASURED CORPUS and not in general. clean-kernel's `[profile.release]` sets
    // `overflow-checks = true`, so every shift there already carried the `Inst::Assert` that
    // `operands_of` refuses and the `!cx.overflow_checks` pair arm is UNREACHED — the guard is
    // inert, which is why it cost 0 flips. With checks OFF a CAST-FREE shift (`x << y`, both
    // operands already the same type) does NOT match `shift_value_cast_pair` and is emitted by the
    // generic `Inst::BinOp` arm, which DOES route its operands through `mf_operand`; there this
    // guard withdraws a `markers_exact` that wave-MF could reach. Fail-closed either way, but it is
    // a real refusal, not a free one.
    if body
        .iter()
        .any(|n| matches!(n.inst, Inst::BinOp { op: BinOp::Shl | BinOp::LShr | BinOp::AShr, .. }))
    {
        return None;
    }
    let mut uses: HashMap<ValueId, u32> = HashMap::new();
    let mut consumer: HashMap<ValueId, &Inst> = HashMap::new();
    // Trust (lane MF-ZERO): the DEFINING instruction of each result, for ordering rule (2)'s
    // three-way operand classification (constant / place / marked). A `ValueId` absent from this
    // map is a block param.
    let mut def_of: HashMap<ValueId, &Inst> = HashMap::new();
    for node in nodes {
        for r in &node.results {
            def_of.insert(*r, &node.inst);
        }
        for v in operands_of(&node.inst)? {
            *uses.entry(v).or_insert(0) += 1;
            consumer.insert(v, &node.inst);
        }
    }
    // `ExtractField` denotes a PLACE, not a value: its consumer mints the operand temp, exactly as
    // built does for `s.k`. Only the statement-minting arms below take a result temp.
    let mut needs: HashSet<ValueId> = HashSet::new();
    let ret_vals: Vec<ValueId> = match &term.inst {
        Inst::Return { values } => values.clone(),
        _ => return None,
    };
    for node in body {
        let &[r] = node.results.as_slice() else { return None };
        // Exactly-once use: built spells (and marks) a tree, never a DAG.
        if uses.get(&r).copied() != Some(1) {
            return None;
        }
        if matches!(
            node.inst,
            Inst::BinOp { .. }
                | Inst::ICmp { .. }
                | Inst::UnOp { .. }
                | Inst::Cast { .. }
                // Trust (lane L): the `Inst::Load` arm mints `_t = copy (*_p)` — that temp IS
                // built's `as_temp` operand temp, so it takes the marker pair. A load whose value
                // is RETURNED takes none (built writes `_0 = copy (*_1)` with no temp), which the
                // `ret_vals` guard below already expresses.
                | Inst::Load { .. }
        ) && !ret_vals.contains(&r)
        {
            // Trust (lane L): a marked temp is `StorageLive`d at its definition and retired ONLY
            // by an `mf_operand` call at its consumer. Requiring the consumer to be one of the
            // arms that actually call `mf_operand` — the four rvalue arms, plus `InsertField`,
            // whose chain the Return arm collapses through `mf_operand` — is what makes the
            // `mf_live`-empty invariant a property of the PLAN rather than a hope about the
            // emitter. Anything else keeps today's marker-free form instead of failing the body
            // closed on an unbalanced marker.
            if !matches!(
                consumer.get(&r),
                Some(
                    Inst::BinOp { .. }
                        | Inst::ICmp { .. }
                        | Inst::UnOp { .. }
                        | Inst::Cast { .. }
                        | Inst::InsertField { .. }
                )
            ) {
                return None;
            }
            needs.insert(r);
        }
    }
    // Trust (lane N defect close, 2026-08-13): A MARKED RESULT MAY NOT TAKE A MARKED OPERAND.
    // This is ordering rule (1) of [`plan_branch_markers`], which lane K derived for the
    // multi-block class and wave-MF/lane L never applied to this one. It is the rule the
    // aggregate/nested-rvalue shapes recorded on [`agg_field_order_ok`] were violating.
    //
    // Built's `as_operand` -> `as_temp` pushes the DESTINATION's `StorageLive` and only THEN
    // builds the sub-expression into it, so for `W8((a & b) | c)` built lives the OUTER (`|`)
    // temp first and the inner (`&`) one second. This shim walks the instruction list in linear
    // SSA order and reaches `&` first, so it lives the inner one first. The two orders can never
    // coincide when BOTH temps exist — which is exactly when both results are marked — so this
    // costs no `markers_exact` that was reachable: a body it refuses had a wrong sequence.
    //
    // Three shapes this closes, all previously admitted-and-wrong and all recorded in
    // `probes/mf_aggregate_adversarial.rs`: `nested_field` (`W8((a & b) | c)`),
    // `two_instr_nested` (`Two { x: a & b, y: (c ^ d) | e }`) and `mk_cast_load`
    // (`Inner(*p as u32)`, the same shape reached through `Inst::Load`). It also closes the
    // NON-aggregate twin the record did not name — `((a & b) | c) == 0`, where the outer `|`
    // is marked because its consumer is the returned `icmp`.
    for node in body {
        let Some(r) = node.results.first() else { continue };
        if !needs.contains(r) {
            continue;
        }
        if operands_of(&node.inst)?.iter().any(|o| needs.contains(o)) {
            return None;
        }
    }
    // Trust (lane MF-ZERO defect close, 2026-08-13): ORDERING RULE (2) — A MARKED OPERAND MAY NOT
    // BE PRECEDED BY A PLACE OPERAND. This is wave-MF's "KNOWN BOUNDARY" (the right-nested tree),
    // stated as a rule of the plan instead of left to the oracle.
    //
    // Built's live order is a PREORDER of the expression tree: at each operand position
    // `as_operand` either folds a constant (nothing), copies a place into a fresh temp
    // (`StorageLive(t); t = copy p`), or opens the sub-expression's temp (`StorageLive(t)`) and
    // only THEN builds into it. The shim's live order is a POSTORDER: a marked result's temp is
    // opened where its own instruction sits in the linear SSA walk, and a place operand's temp is
    // opened at the consumer. The two coincide only when nothing that mints a temp at the consumer
    // comes BEFORE a marked operand. Measured, verbatim built MIR for `a == (b & c)`:
    //
    //     StorageLive(_4); _4 = copy _1;                 <- the PLACE operand `a`, minted first
    //     StorageLive(_5); StorageLive(_6); _6 = copy _2; StorageLive(_7); _7 = copy _3;
    //     _5 = BitAnd(move _6, move _7); ...
    //
    // versus `(a & b) == c`, where the marked operand is leftmost and built opens `_4` (the `&`
    // temp) first — exactly the shim's order. The oracle's verdict on the first of those is
    // `line 1: built mk b0.1:live s1:u8 vs derived mk b0.0:live s1:u8`.
    //
    // CONSTANT-TOLERANT, and that is the whole difficulty. `plan_branch_markers`' rule (2) counts
    // EVERY non-marked operand as blocking, which is right for what it was written against and
    // would be WRONG here: `0 == (b & c)` folds its constant in place, mints no temp for it, and
    // is `markers_exact: true` in the control. Refusing it would withdraw a flip to fix nothing.
    // A `Const` operand therefore constrains nothing; only a PLACE does.
    //
    // Applied to the rvalue arms only. `InsertField`/`Const` chain nodes mint no MIR statement (the
    // Return arm collapses them into one `Rvalue::Aggregate`) and their field ordering is
    // `agg_field_order_ok`'s business, where the same rule already lives as "every
    // instruction-valued field precedes every place-valued field".
    //
    // Four shapes this closes, all previously admitted-and-wrong, all in `probes/mf_residual.rs`:
    // `a1_right_nested` (`a == (b & c)`, also `right_nested` in both wave-MF probe files),
    // `a3_field_right_nested` (`self.0 == (b & c)` — a field read is a place too),
    // `a12_place_then_and` (`a | (b & c)` — not specific to comparisons) and `a6_place_then_load`
    // (`a == *p`, the same defect reached through `Inst::Load`).
    let is_place = |o: &ValueId| -> bool {
        match def_of.get(o) {
            // A block param: an argument local, which built copies into a fresh temp at the
            // consumer exactly like a field read.
            None => true,
            Some(inst) => match inst {
                // Folded in place by `as_constant`; mints no temp and no marker.
                Inst::Const { .. } => false,
                // A marked result: its temp was opened at its own instruction, earlier.
                _ => !needs.contains(o),
            },
        }
    };
    for node in body {
        if !matches!(
            node.inst,
            Inst::ExtractField { .. }
                | Inst::Load { .. }
                | Inst::BinOp { .. }
                | Inst::ICmp { .. }
                | Inst::UnOp { .. }
                | Inst::Cast { .. }
        ) {
            continue;
        }
        let mut seen_place = false;
        for o in operands_of(&node.inst)? {
            if needs.contains(&o) {
                if seen_place {
                    return None;
                }
            } else if is_place(&o) {
                seen_place = true;
            }
        }
    }
    // Trust (lane L): an `InsertField`/aggregate-`Const` chain is admitted only when it is exactly
    // the chain the Return arm collapses, and only when built's field-order temp minting agrees
    // with this shim's linear-walk order.
    if body.iter().any(|n| {
        matches!(n.inst, Inst::InsertField { .. })
            || matches!(&n.inst, Inst::Const { value: Constant::Aggregate(_), .. })
    }) && !agg_field_order_ok(&blk.params, nodes, &ret_vals)
    {
        return None;
    }
    Some(needs)
}

/// Trust (lane L, AGGREGATE CONSTRUCTION): does this body's constructor chain lower to built's
/// marker sequence under the shim's LINEAR instruction walk?
///
/// The Return arm collapses the producer's `Const{Aggregate}` seed + per-field `InsertField` chain
/// into ONE `Rvalue::Aggregate` (`recognize_agg_return_chain`), so the chain nodes mint no
/// statements and only the FIELD operands can carry markers. Built mints a field's operand temp at
/// its position in FIELD order; this shim mints an instruction-result field's temp when it walks
/// that instruction and a place-valued field's temp at the aggregate site. Those two orders
/// coincide only under the two conditions checked below — and where they do not, this returns
/// `false` and the body keeps today's marker-free derived form rather than a wrong one.
///
/// Every condition is fail-closed; `false` is always safe.
///
/// # The three admitted-and-wrong shapes, CLOSED (2026-08-13)
///
/// The lane N adversarial review recorded three shapes that passed every condition here and still
/// emitted a marker sequence that was not built's, and left them admitted on the argument that the
/// oracle catches them. Documenting a defect is not fixing it; all three are now REFUSED, by name,
/// and none of the three refusals is incidental to another condition:
///
///   * a NESTED field expression — `W8((a & b) | c)`, and the same shape reached through
///     `Inst::Load`, `Inner(*p as u32)`. `as_operand`→`as_temp` opens the OUTER (field) temp FIRST
///     and the inner one second; the linear walk reaches the inner instruction first. **Refused in
///     [`plan_operand_marker_temps`]** by ordering rule (1) — a MARKED result may not take a MARKED
///     operand — which is where the defect actually lives (it is not specific to aggregates: the
///     non-aggregate twin `((a & b) | c) == 0` was wrong the same way). Pinned by
///     `agg_plan_tests::a_nested_field_expression_is_refused` and
///     `a_cast_of_a_load_field_is_refused`.
///   * FUNCTIONAL RECORD UPDATE — `P3 { a: x, ..p }`. `rustc_mir_build` consumes every
///     BASE-supplied field as a bare place (`copy (_1.1: u32)`) with NO temp and NO marker; only
///     the explicitly-given field goes through `as_operand`. It WAS refused here by a
///     "no field `i` fed by a read of field `i`" rule that also refused every written-out twin.
///     Since lane MF-ZERO (2026-08-13) the discrimination is [`source_form_admits`]'s
///     `StructTailExpr::Base` refusal — the source form, where the question is not a guess — and
///     the written-out forms are admitted again. See the note at the deleted rule's site below.
///
///   * the returned value is the tail of a well-formed chain, and EVERY aggregate node in the body
///     belongs to it (no second chain, no dead chain, nothing left for the main loop);
///   * the seed is `Ty::Struct`/`Ty::Tuple`. An `Inst::Const { ty: Ty::Enum, .. }` seed is the
///     B3-2a enum-construction convention, whose Return arm (`emit_enum_variant`) does NOT route
///     its payload through `mf_operand` — admitting it would leave a `StorageLive` unretired and
///     fail the body closed at the `mf_live` check, losing an `agreed` verdict;
///   * no field is itself an aggregate constant (a nested constructor, which the Return arm's
///     `cx.operand` fails closed on anyway);
///   * **every instruction-valued field precedes every place-valued field**, and the
///     instruction-valued fields appear in the instruction list in field order. MEASURED
///     counterexample, the shape this rejects: `SourcePos { file_id: self.file_id, line: <expr>,
///     column: 0 }` — built lives field 0's temp FIRST and only then opens field 1's, while the
///     linear walk reaches `<expr>` before it ever reaches the aggregate. Constant fields mint
///     nothing and therefore constrain nothing;
///   * **every field's TYPE is a scalar** — read from the field VALUE's own trust-ir type, never
///     from the seed constant's element kinds. See the note on the seed guard below for the defect
///     that made the seed an unsound scalarness oracle.
fn agg_field_order_ok(params: &[(ValueId, Ty)], nodes: &[InstrNode], ret_vals: &[ValueId]) -> bool {
    let mut value_def: HashMap<ValueId, &InstrNode> = HashMap::new();
    for node in nodes.iter() {
        for r in &node.results {
            value_def.insert(*r, node);
        }
    }
    let [rv] = ret_vals else { return false };
    let Some((field_vals, skip)) = recognize_agg_return_chain(&value_def, *rv) else {
        return false;
    };
    let chain: HashSet<ValueId> = skip.iter().copied().collect();
    for node in nodes {
        let is_agg_node = matches!(node.inst, Inst::InsertField { .. })
            || matches!(&node.inst, Inst::Const { value: Constant::Aggregate(_), .. });
        if is_agg_node && !node.results.iter().all(|r| chain.contains(r)) {
            return false;
        }
        // The seed's type decides which Return arm claims the chain, and the seed's ELEMENTS
        // decide whether any field is non-scalar.
        if let Inst::Const { ty, value: Constant::Aggregate(seeds) } = &node.inst {
            if !matches!(ty, Ty::Struct(_) | Ty::Tuple(_)) {
                return false;
            }
            // Trust (lane L): every field must be SCALAR. MEASURED, and this is the one place
            // where satisfying the marker channel was not free: `MemoryRegion::new(AllocationId,
            // usize, usize)` gained `markers_exact` and then LOST its flip, because the derived
            // body now carries a STRUCT temp (`StorageLive(_4); _4 = copy _1`, exactly what built
            // emits) and the flip fragment gate refuses one — `"struct temp _4 used outside
            // call-dest / whole read / scalar field read"`. Widening that gate is not this
            // change's business, so the plan declines the shape instead and the body keeps
            // exactly its pre-lane-L behaviour. The seed constant mirrors the field types
            // one-for-one, so its element kinds are the honest discriminator.
            //
            // Trust (lane N review, 2026-08-13): that last sentence WAS FALSE, and this is where
            // the defect was recorded rather than repaired. `seed_overwritten_ty` deliberately
            // seeds a `Ty::Ptr` lane as `Constant::Int(0)`, the null pointer (wave-PS), so a
            // REFERENCE or raw-pointer field READ AS SCALAR right here. It was inert only because
            // such a field's operand lives in `fwd_ptr_params`, never in `env`, so `cx.operand`
            // failed the whole body closed first (measured on `mk_refpair(&u8, usize)` —
            // `unsupported`). That is safety by UNREACHABILITY: it evaporates the moment the
            // operand arm widens.
            //
            // CLOSED (2026-08-13) by refusing the TYPE at the `SCALAR_CANDS` gate in the field loop
            // below, which reads each field VALUE's own trust-ir type and never the seed. Note what
            // was NOT available: "seed it honestly" is not expressible today — trust-ir's
            // `Constant` has no pointer-valued variant (`Int`/`U128`/`Bytes`/`Float`/`Bool`/
            // aggregates/`PhantomData`), `shape_matches_ty` admits `(Int(_), Ty::Ptr)` and admits
            // `PhantomData` only against `Ty::Unit`, so every spelling reachable from here either
            // lies about the kind or fails validation. So the seed keeps spelling a null as
            // `Int(0)` and this check keeps its ORIGINAL job — refusing a NESTED aggregate or a
            // `PhantomData` unit lane — while the scalarness question moved to the types, where it
            // can be answered.
            if !seeds.iter().all(|s| {
                matches!(
                    s,
                    Constant::Int(_) | Constant::U128(_) | Constant::Float(_) | Constant::Bool(_)
                )
            }) {
                return false;
            }
        }
    }
    // Trust (defect close, 2026-08-13): THE FIELD'S OWN TYPE, never the seed constant's kind.
    // `None` = a block param, whose type the entry block declares. Every other class carries its
    // result type on the instruction itself; `Inst::ExtractField.ty` is the FIELD type (both
    // emission sites — `ExprKind::Field` and the wave-FRU base read — pass the field's `Ty`), and
    // `Inst::ICmp` always yields `Ty::Bool`.
    let field_ty = |v: &ValueId| -> Option<Ty> {
        match value_def.get(v) {
            None => params.iter().find(|(p, _)| p == v).map(|(_, t)| t.clone()),
            Some(n) => match &n.inst {
                Inst::Const { ty, .. }
                | Inst::ExtractField { ty, .. }
                | Inst::BinOp { ty, .. }
                | Inst::UnOp { ty, .. }
                | Inst::Load { ty, .. } => Some(ty.clone()),
                Inst::ICmp { .. } => Some(Ty::Bool),
                Inst::Cast { dst_ty, .. } => Some(dst_ty.clone()),
                _ => None,
            },
        }
    };
    // `None` = a block param: an arg local, which built copies into a fresh operand temp exactly
    // like a field read. `Instr` = a result this shim materialises in a temp of its own.
    #[derive(PartialEq)]
    enum Cls {
        Konst,
        Place,
        Instr,
    }
    let mut seen_place = false;
    for v in field_vals.iter() {
        // The scalar wall, stated over TYPES. A `&u8` field is a `Ty::Ptr` here whatever the seed
        // says about it, and a struct/tuple/unit/enum/array field is refused for the same reason
        // lane L refused it: the derived body would carry a non-scalar temp the flip fragment gate
        // declines, costing the body a flip it has today.
        match field_ty(v) {
            Some(t) if SCALAR_CANDS.contains(&t) => {}
            _ => return false,
        }
        // Trust (lane MF-ZERO, 2026-08-13): THE FRU SIGNATURE USED TO BE REFUSED HERE — "no field
        // `i` fed by a read of field `i`" — and that rule is GONE, narrowed to exactly what it can
        // justify and moved to where the question is answerable.
        //
        // Its justification was that `P3 { a: x, ..p }` and its written-out twin
        // `P3 { a: x, b: p.b, c: p.c }` lower to the SAME trust-ir while built marks them
        // DIFFERENTLY (a base-supplied field is a bare place with no temp; an explicitly-written
        // `p.b` goes through `as_operand`→`as_temp` with one), so a function of the instruction
        // stream cannot be right on both. True — but the rule refused strictly MORE than that
        // argument covers, and the excess was measured: `P3 { a: p.c, b: p.b, c: p.a }` has NO FRU
        // spelling that produces its stream. The producer emits the base reads AFTER every explicit
        // field (`lower_expr(base_expr)` runs after the `field_exprs` loop), so the unique FRU
        // spelling `P3 { a: p.c, c: p.a, ..p }` emits the base read LAST (`%3 = extractfield %0, 1`)
        // where the written-out form emits it in the middle (`%2`). That body was refused for an
        // ambiguity it does not have, and it held a flip.
        //
        // The discrimination now happens in [`source_form_admits`], which refuses
        // `StructTailExpr::Base` outright — the SOURCE FORM, where "is this an FRU?" is not a
        // guess. `c1_fru` stays refused; `c2_written_out_field0`, `c3_cross_base_same_index`,
        // `c4_partial_fru` and `c6_tail_same_index` (all written-out, all with same-index reads)
        // are admitted and exact. Pinned by `probes/mf_residual.rs` group C.
        let cls = match value_def.get(v) {
            None => Cls::Place,
            Some(n) => match &n.inst {
                Inst::Const { value: Constant::Aggregate(_), .. } => return false,
                Inst::Const { .. } => Cls::Konst,
                Inst::ExtractField { .. } => Cls::Place,
                Inst::BinOp { .. }
                | Inst::ICmp { .. }
                | Inst::UnOp { .. }
                | Inst::Cast { .. }
                | Inst::Load { .. } => Cls::Instr,
                _ => return false,
            },
        };
        match cls {
            // A constant field folds in place: no temp on either side, so it neither takes a
            // position in built's live order nor constrains anyone else's.
            Cls::Konst => {}
            Cls::Place => seen_place = true,
            Cls::Instr => {
                if seen_place {
                    return false;
                }
            }
        }
        // Trust (lane MF-ZERO-2, 2026-08-13): THE FIELD-POSITION ORDER RULE IS RETIRED HERE, in
        // both the form this file shipped before lane MF-ZERO ("every INSTRUCTION-valued field
        // appears in the instruction list in FIELD order", `prev_instr_pos`) and the widened form
        // lane MF-ZERO gave it ("every field value that HAS a defining instruction ...",
        // `prev_pos`). It was a PROXY for the written field order, and the source form now answers
        // that question exactly — see [`permutation_is_observable`].
        //
        // MEASURED, on this driver, why it can only ever have been a proxy. The producer lowers
        // field values in SOURCE order (`for (idx, fexpr) in field_exprs`) and each field's value
        // is the last instruction of its own subtree, so a field value's position rises with its
        // SOURCE position and with nothing else. Two consequences, both checked against dumped
        // trust-ir rather than argued:
        //
        //   * it does not CSE, so two identical field expressions get two positions, not one:
        //     `Inr { x: p.a, y: p.a }` emits `%1 = extractfield %0,0` AND `%2 = extractfield %0,0`,
        //     and `Inr { x: a & b, y: a & b }` emits two `and`s. There is therefore no
        //     declaration-order literal whose positions fail to increase;
        //   * a field value that is a bare block PARAM has no position at all, so
        //     `T3 { a: x, c: z, b: y }` and `T3 { a: x, b: y, c: z }` have BYTE-IDENTICAL trust-ir.
        //
        // So the rule fired exactly when the source was out of declaration order — never on any
        // other body — and [`source_form_admits`]' field-order clause fires there too, on the
        // source itself, and knows something this rule cannot: whether the permutation is
        // OBSERVABLE. The measured residue was pure excess: `f25_rotate_written_cba`
        // (`T3 { c: p.a, b: p.c, a: p.b }`, three `u32` field reads) is `markers_exact: true` with
        // this rule off and refused with it on, and an independent review measured the widened
        // form moving ZERO of 238 corpus bodies on its own — a guard indistinguishable from its own
        // absence. `seen_place` above is NOT a proxy for anything and stays: it separates
        // `Inr { x: c, y: a & b }` from `Inr { x: a & b, y: c }` in DECLARATION order, where no
        // source-form question arises.
    }
    true
}

/// Trust (lane K): one admitted `CondBr` — the condition value, its two arm targets, and the
/// block where the two arms reconverge (built's JOIN, the immediate post-dominator).
#[derive(Debug, Clone, Copy)]
struct MfBranch {
    cond: ValueId,
    then_target: BlockId,
    else_target: BlockId,
    join: BlockId,
}

/// Trust (lane K): the MULTI-BLOCK marker plan — the marked-result set plus the per-`CondBr`
/// branch table the emitter needs to place built's cross-block markers.
#[derive(Debug, Clone)]
struct MfBranchPlan {
    /// The `mf_plan` set for this body (same meaning as [`plan_operand_marker_temps`]'s return).
    needs: HashSet<ValueId>,
    /// Producer block -> its admitted `CondBr`. Every `CondBr` in the body is present, or the
    /// whole plan is `None`.
    branch: HashMap<BlockId, MfBranch>,
}

/// Trust (lane K, MULTI-BLOCK OPERAND-TEMP MARKER FIDELITY): the per-body plan that decides
/// whether this shim may reproduce built's storage markers for a `let`-free STRUCTURED `if` /
/// `&&` / `||` body. Returns `None` — today's behaviour, no derived marker anywhere — unless the
/// WHOLE body is inside the planned class.
///
/// # What built does, measured
///
/// `-Zdump-mir=all` on every shape in `crates/trust-thir-lower/probes/mf_multiblock.rs`
/// (committed) gives ONE discipline, identical in all of them. Verbatim built MIR for `min_if`
/// (`if a == 0 { b == 1 } else { b == 2 }`):
///
/// ```text
/// bb0: StorageLive(_3); StorageLive(_4); _4 = copy _1; _3 = Eq(move _4, const 0_u32);
///      switchInt(move _3) -> [0: bb2, otherwise: bb1];
/// bb1: StorageDead(_4); StorageLive(_5); _5 = copy _2; _0 = Eq(move _5, const 1_u32);
///      StorageDead(_5); goto -> bb4;
/// bb2: goto -> bb3;                       // EMPTY TRAMPOLINE, always on the FALSE (`0`) edge
/// bb3: StorageDead(_4); StorageLive(_6); _6 = copy _2; _0 = Eq(move _6, const 2_u32);
///      StorageDead(_6); goto -> bb4;
/// bb4: StorageDead(_3); return;
/// ```
///
/// Three facts, and all three are load-bearing:
///
///   1. The condition's OPERAND temps (`_4`) are retired at the ENTRY of **both** arms, in
///      reverse operand order — not in the head block. Their region scope is the condition
///      expression, and built exits that scope on each outgoing edge.
///   2. The condition's own RESULT temp (`_3`) is retired at the **join**, at position 0.
///   3. The false edge always goes through an **empty trampoline block**. This is not cosmetic:
///      `mir_differential::canon_markers` walks the RAW CFG with no goto threading, so a derived
///      body missing that block has every fine block index after it shifted and the channel
///      refuses. The shim therefore mints the trampoline whenever this plan engages.
///
/// The recursion is the same rule applied per `CondBr` (`nested_if`, `bvar_in_range`: 21 markers
/// over 9 blocks, hand-checked against this plan's output).
///
/// # The admitted class, and why each condition is load-bearing
///
///   * **`func.scopes.is_none()`** — wave-MF's firewall, unchanged and consulted FIRST. A source
///     `let` mints a named local plus a `FakeRead` that the instruction stream cannot see. This
///     is what puts `nat_gcd` and both `to_signed` bodies outside the plan before anything below
///     is even reached.
///   * **at least two blocks** — one block is wave-MF's class and keeps wave-MF's plan verbatim.
///   * **every terminator in {`Br`, `CondBr`, `Return`}, exactly one `Return`, acyclic** — a back
///     edge is a loop (its condition temp has no single join), and a second `Return` is an early
///     `return` whose statement-value local built marks and the producer never emits.
///   * **every other instruction in {`Const`, `ExtractField`, `BinOp`, `ICmp`, `UnOp`, `Cast`}**
///     — exactly wave-MF's set: the four arms taught to emit operand temps plus the two that mint
///     no MIR statement. `Assert`/`Overflow`/`Select`/`Call`/`Switch`/`Load`/`InsertField`/... are
///     OUT. (`Switch` being out is what keeps every currently-flipping multi-block body — all of
///     them `Switch`-driven with zero `condbr` — bit-identical to today.)
///   * **every instruction result used exactly once, in its own block** — built evaluates an
///     expression TREE, and a marker's canonical position is `(fine block, assigns seen)`, so a
///     result crossing a block boundary would need a region scope this plan does not model.
///   * **every `CondBr` condition is a MARKED RESULT of its own block** — and this one is forced
///     by measurement, not conservatism. `param_cond(a: bool, ..) { if a { x } else { y } }` and
///     `match_bool(c: bool, ..) { match c { true => x, false => y } }` lower to BYTE-IDENTICAL
///     trust-ir and neither opens a scope, yet built gives the first `StorageLive(_4); _4 = copy
///     _1; switchInt(move _4)` and the second `PlaceMention(_1); switchInt(copy _1)` with ZERO
///     markers. `match_bool` is therefore `markers_exact: true` TODAY and flips; minting a temp
///     for a bare-param condition would silently take that flip away. Requiring a marked result
///     refuses both, and keeps `match_bool`'s existing flip.
///   * **results are LEFTMOST in every operand list** — wave-MF's right-nested boundary, made
///     explicit here. Built evaluates operands left to right, minting each one's temp in turn;
///     this shim walks the instruction list linearly, so a sub-expression result appearing at
///     operand position `k` while some position `j < k` is a place gets its temp minted too
///     early. That is exactly `clamp_u32` (`value > u32::MAX as u64`), which stays out.
///   * **arm/join blocks come after their head in the block list, and no block is both an arm
///     target and a join** — the emitter schedules a block's entry markers when it lowers the
///     head, so a head lowered after its own arm would drop them. The producer's `lower_if`
///     satisfies this (measured on every probe shape); a producer that did not simply keeps
///     today's marker-free form.
///
///   * **a JOIN block's PARAMETER is consumed only by a terminator** — the join-parameter rule,
///     added 2026-08-13 to close the three shapes the lane P adversarial review found admitted
///     and wrong (`join_is_head`, `chain_of_ifs`, `double_nested_cond`, all in
///     `probes/mb_joinhead.rs`). A join parameter is an `if`-expression's value; built hoists the
///     `StorageLive` of the temp that holds it into the HEAD block, before the branch, and this
///     shim mints it at the consumer. See the rule's own comment for why refusing costs no
///     reachable `markers_exact`. Pinned by
///     `branch_marker_plan_tests::a_join_parameter_consumed_by_an_instruction_is_refused`.
///
/// **STILL NECESSARY-NOT-SUFFICIENT.** Nothing above establishes that an admitted body's derived
/// marker sequence IS built's; the conditions are the ones needed to make the emitter's linear
/// walk agree, not a proof that it does. The three named counterexamples are closed; the
/// comparator remains the authority, and a shape nobody has thought of would still be caught
/// there rather than here.
///
/// NOT A RELAXATION, and the property is the same one wave-MF rests on: everything here only ADDS
/// statements (and one empty `Goto` block, which the semantic channel threads away — LEDGER L3)
/// to the derived body. `mir_differential::canon_markers` is untouched and still decides. A wrong
/// plan yields a wrong marker sequence, `markers_exact: false`, and no flip — precisely the state
/// every body in this class is in today.
fn plan_branch_markers(func: &trust_ir::Function) -> Option<MfBranchPlan> {
    // Wave-MF's firewall, first and unchanged: any lexical `let` scope is out.
    if func.scopes.is_some() {
        return None;
    }
    // Single-block bodies belong to wave-MF's plan, verbatim.
    if func.blocks.len() < 2 {
        return None;
    }
    let index: HashMap<BlockId, usize> =
        func.blocks.iter().enumerate().map(|(i, b)| (b.id, i)).collect();
    if index.len() != func.blocks.len() {
        return None;
    }

    // --- shape: terminators, instruction set, and the value-use census -------------------
    fn operands_of(inst: &Inst) -> Option<Vec<ValueId>> {
        Some(match inst {
            Inst::Const { .. } => vec![],
            Inst::ExtractField { aggregate, .. } => vec![*aggregate],
            Inst::BinOp { lhs, rhs, .. } | Inst::ICmp { lhs, rhs, .. } => vec![*lhs, *rhs],
            Inst::UnOp { operand, .. } | Inst::Cast { operand, .. } => vec![*operand],
            Inst::Br { args, .. } => args.clone(),
            Inst::CondBr { cond, then_args, else_args, .. } => {
                let mut v = vec![*cond];
                v.extend(then_args.iter().copied());
                v.extend(else_args.iter().copied());
                v
            }
            Inst::Return { values } => values.clone(),
            _ => return None,
        })
    }
    // `mf_result_temp` marks a result only for these four arms; `Const`/`ExtractField` mint no
    // MIR statement of their own (a constant folds in place, a field read denotes a PLACE whose
    // consumer mints the temp), exactly as in wave-MF.
    fn mints_result_temp(inst: &Inst) -> bool {
        matches!(
            inst,
            Inst::BinOp { .. } | Inst::ICmp { .. } | Inst::UnOp { .. } | Inst::Cast { .. }
        )
    }

    let mut uses: HashMap<ValueId, u32> = HashMap::new();
    let mut def_block: HashMap<ValueId, BlockId> = HashMap::new();
    let mut use_block: HashMap<ValueId, BlockId> = HashMap::new();
    let mut consumer: HashMap<ValueId, Inst> = HashMap::new();
    let mut n_return = 0usize;
    for blk in &func.blocks {
        let (term, body) = blk.body.split_last()?;
        if !matches!(term.inst, Inst::Br { .. } | Inst::CondBr { .. } | Inst::Return { .. }) {
            return None;
        }
        if matches!(term.inst, Inst::Return { .. }) {
            n_return += 1;
        }
        // A non-terminator instruction in the middle of the list would be a producer bug; the
        // split above already put every one of them in `body`.
        if body.iter().any(|n| n.inst.is_terminator()) {
            return None;
        }
        for node in &blk.body {
            for v in operands_of(&node.inst)? {
                *uses.entry(v).or_insert(0) += 1;
                use_block.insert(v, blk.id);
                consumer.insert(v, node.inst.clone());
            }
        }
        for node in body {
            let &[r] = node.results.as_slice() else { return None };
            if def_block.insert(r, blk.id).is_some() {
                return None;
            }
        }
    }
    if n_return != 1 {
        return None;
    }
    // A SHIFT is refused outright, and this is a LOST-FLIP hazard, not tidiness. With overflow
    // checks OFF the shim recognizes `Cast + BinOp(Shl|LShr|AShr)` as ONE unit at the top of the
    // node loop (`shift_value_cast_pair`) and reads its operands through `cx.operand`, NOT
    // `mf_operand` — so a marked temp feeding a shift would never be retired, `mf_live` would be
    // non-empty at body end, and the body would fail CLOSED, LOSING an `agreed` verdict it has
    // today. With checks ON the idiom carries an `Inst::Assert`, which `operands_of` already
    // refuses. (Lane L found the same hazard in wave-MF's single-block plan; this is the
    // multi-block copy of that guard, not a new argument.)
    if func
        .blocks
        .iter()
        .flat_map(|b| b.body.iter())
        .any(|n| matches!(n.inst, Inst::BinOp { op: BinOp::Shl | BinOp::LShr | BinOp::AShr, .. }))
    {
        return None;
    }
    // Every instruction result: used exactly once, and in its own block.
    for (r, b) in &def_block {
        if uses.get(r).copied() != Some(1) {
            return None;
        }
        if use_block.get(r) != Some(b) {
            return None;
        }
    }

    // --- acyclicity + reverse-topological (postorder) walk --------------------------------
    fn succs_of(inst: &Inst) -> Vec<BlockId> {
        match inst {
            Inst::Br { target, .. } => vec![*target],
            Inst::CondBr { then_target, else_target, .. } => vec![*then_target, *else_target],
            _ => vec![],
        }
    }
    let term_of = |b: BlockId| -> Option<&Inst> {
        let i = *index.get(&b)?;
        Some(&func.blocks[i].body.last()?.inst)
    };
    // Iterative DFS producing a postorder; a gray-node hit is a back edge → refuse.
    let mut color: HashMap<BlockId, u8> = HashMap::new();
    let mut postorder: Vec<BlockId> = Vec::new();
    let mut stack: Vec<(BlockId, usize)> = vec![(func.entry, 0)];
    color.insert(func.entry, 1);
    while let Some((b, k)) = stack.pop() {
        let ss = succs_of(term_of(b)?);
        if k < ss.len() {
            stack.push((b, k + 1));
            let s = ss[k];
            match color.get(&s).copied() {
                Some(1) => return None, // back edge: a loop
                Some(_) => {}
                None => {
                    if !index.contains_key(&s) {
                        return None;
                    }
                    color.insert(s, 1);
                    stack.push((s, 0));
                }
            }
        } else {
            color.insert(b, 2);
            postorder.push(b);
        }
    }
    // Every block must be reachable: an unreachable block would be lowered anyway and its
    // markers would land in a block `canon_markers`' walk never reaches (fail-closed there).
    if postorder.len() != func.blocks.len() {
        return None;
    }

    // --- the per-CondBr join, computed in reverse topological order ------------------------
    // `follow(b)` is where control resumes after b's whole structured region: the `Br` target,
    // the `CondBr`'s join, or nothing for the `Return` block. Postorder guarantees every
    // successor's `follow` is already known.
    let mut follow: HashMap<BlockId, Option<BlockId>> = HashMap::new();
    let mut branch: HashMap<BlockId, MfBranch> = HashMap::new();
    let mut preds: HashMap<BlockId, u32> = HashMap::new();
    for blk in &func.blocks {
        for s in succs_of(term_of(blk.id)?) {
            *preds.entry(s).or_insert(0) += 1;
        }
    }
    for b in &postorder {
        let t = term_of(*b)?;
        match t {
            Inst::Return { .. } => {
                follow.insert(*b, None);
            }
            Inst::Br { target, .. } => {
                follow.insert(*b, Some(*target));
            }
            Inst::CondBr { cond, then_target, then_args, else_target, else_args } => {
                if !then_args.is_empty() || !else_args.is_empty() {
                    return None;
                }
                if then_target == else_target
                    || *then_target == func.entry
                    || *else_target == func.entry
                {
                    return None;
                }
                // Each arm is entered ONLY from here — its entry markers are this branch's.
                if preds.get(then_target).copied() != Some(1)
                    || preds.get(else_target).copied() != Some(1)
                {
                    return None;
                }
                // The condition must be a MARKED result of THIS block (the param_cond /
                // match_bool tripwire), defined by the last node before the terminator modulo
                // `Const` nodes, which mint no statement.
                if def_block.get(cond) != Some(b) {
                    return None;
                }
                let nodes = &func.blocks[*index.get(b)?].body;
                let (_, body) = nodes.split_last()?;
                let ci = body.iter().position(|n| n.results.first() == Some(cond))?;
                if !mints_result_temp(&body[ci].inst) {
                    return None;
                }
                if body[ci + 1..].iter().any(|n| !matches!(n.inst, Inst::Const { .. })) {
                    return None;
                }
                // Reconvergence: the first block common to both arms' follow chains.
                let mut chain: Vec<BlockId> = Vec::new();
                let mut x = Some(*then_target);
                while let Some(c) = x {
                    if chain.contains(&c) {
                        return None;
                    }
                    chain.push(c);
                    x = follow.get(&c).copied().flatten();
                }
                let mut y = Some(*else_target);
                let mut join = None;
                let mut guard = 0usize;
                while let Some(c) = y {
                    if chain.contains(&c) {
                        join = Some(c);
                        break;
                    }
                    guard += 1;
                    if guard > func.blocks.len() {
                        return None;
                    }
                    y = follow.get(&c).copied().flatten();
                }
                let join = join?;
                // A degenerate arm (`if c { A }` with the join AS the else edge) is a different
                // built shape; refuse rather than guess.
                if join == *then_target || join == *else_target {
                    return None;
                }
                follow.insert(*b, Some(join));
                branch.insert(
                    *b,
                    MfBranch {
                        cond: *cond,
                        then_target: *then_target,
                        else_target: *else_target,
                        join,
                    },
                );
            }
            _ => return None,
        }
    }
    if branch.is_empty() {
        return None;
    }

    // --- the JOIN-PARAMETER rule (lane P defect close, 2026-08-13) --------------------------
    // A JOIN BLOCK'S PARAMETER MAY ONLY BE CONSUMED BY A TERMINATOR — a `Return` value or a
    // `Br`/`CondBr` edge argument. Any use as an OPERAND of a non-terminator instruction refuses
    // the whole body.
    //
    // A join parameter IS the value of an `if`-expression. When built needs that value as an
    // OPERAND, `as_operand`→`as_temp` pushes the temp's `StorageLive` BEFORE evaluating the `if`
    // — i.e. in the HEAD block — and the `if`'s arms then write into that temp. This shim has no
    // such hoist: `mf_operand` mints the temp at the CONSUMER, which by dominance is in the join
    // block or later, never in the head. The two positions are therefore never the same fine
    // block index, so a body reaching this rule cannot have had an exact marker sequence and
    // refusing it cannot cost a `markers_exact` that was reachable. When the value is consumed by
    // a terminator instead, built writes each arm's tail expression straight into the destination
    // and mints no temp at all — which is `min_if`, and stays admitted.
    //
    // THE THREE SHAPES THIS CLOSES, all recorded as admitted-and-wrong in `probes/mb_joinhead.rs`
    // and all previously passing every condition in this function: `join_is_head`
    // (`if (if a == 0 { b } else { c }) == 0 {..}`), `chain_of_ifs` and `double_nested_cond`.
    // Their first divergence was `line 2: built mk b0.0:live s2:bool vs derived mk b2.0:dead
    // s1:u32` — built's hoisted `StorageLive` in the head, exactly this rule. Ordering rule (1)
    // below does not catch them: it fires only when the inner value is a MARKED RESULT, and a
    // join parameter is not a result at all.
    let join_params: HashSet<ValueId> = branch
        .values()
        .filter_map(|br| index.get(&br.join).copied())
        .flat_map(|i| func.blocks[i].params.iter().map(|(v, _)| *v))
        .collect();
    for blk in &func.blocks {
        let (_, body) = blk.body.split_last()?;
        for node in body {
            if operands_of(&node.inst)?.iter().any(|o| join_params.contains(o)) {
                return None;
            }
        }
    }

    // --- emission-order + role-exclusivity, so the emitter can never drop a scheduled marker --
    let mut arm_of: HashMap<BlockId, ()> = HashMap::new();
    let mut join_of: HashMap<BlockId, ()> = HashMap::new();
    for (h, br) in &branch {
        let hi = *index.get(h)?;
        for b in [br.then_target, br.else_target, br.join] {
            if *index.get(&b)? <= hi {
                return None;
            }
        }
        for b in [br.then_target, br.else_target] {
            if arm_of.insert(b, ()).is_some() {
                return None;
            }
        }
        if join_of.insert(br.join, ()).is_some() {
            return None;
        }
    }
    if arm_of.keys().any(|b| join_of.contains_key(b)) {
        return None;
    }

    // --- the marked-result set --------------------------------------------------------------
    // A result takes a marker-carrying temp exactly when built materialises one there: when its
    // single consumer is another rvalue's OPERAND, or a `CondBr` condition. A result consumed by
    // `Return` or by a `Br` edge argument gets none — built writes the outermost expression of
    // each arm straight into `_0`.
    let mut needs: HashSet<ValueId> = HashSet::new();
    for blk in &func.blocks {
        for node in &blk.body {
            let Some(r) = node.results.first() else { continue };
            if !mints_result_temp(&node.inst) {
                continue;
            }
            let marked = match consumer.get(r) {
                Some(Inst::CondBr { cond, .. }) => cond == r,
                Some(c) => mints_result_temp(c) || matches!(c, Inst::ExtractField { .. }),
                None => false,
            };
            if marked {
                needs.insert(*r);
            }
        }
    }
    // Two ordering rules, both about WHERE a `StorageLive` lands, both measured.
    //
    // (1) A MARKED instruction may not take a MARKED operand. Built's `as_temp` pushes the
    //     destination's `StorageLive` and only THEN builds the sub-expression into it, so for
    //     `if (a & b) == 0` built emits `StorageLive(_c); StorageLive(_and); …` — outer temp
    //     first. This shim walks the instruction list linearly and reaches the `&` node before
    //     the `icmp` node, so it would emit `StorageLive(_and)` first. The orders agree only
    //     when the marked result's own operands are places or constants. (An UNMARKED result is
    //     unaffected — it has no `StorageLive` of its own to misplace — which is why an arm
    //     whose value is `(a & b) == d` stays in.)
    //
    // (2) Marked results must be LEFTMOST in every operand list — wave-MF's right-nested
    //     boundary, made explicit. A marked operand's temp is minted at its own instruction,
    //     earlier; every other operand's temp is minted here, at the consumer; built mints both
    //     in operand order. `clamp_u32` (`value > u32::MAX as u64`) is the body this refuses.
    for blk in &func.blocks {
        for node in &blk.body {
            if !mints_result_temp(&node.inst) {
                continue;
            }
            let ops = operands_of(&node.inst)?;
            let marked_result = node.results.first().is_some_and(|r| needs.contains(r));
            let mut seen_unmarked = false;
            for o in ops {
                if needs.contains(&o) {
                    if marked_result || seen_unmarked {
                        return None;
                    }
                } else {
                    seen_unmarked = true;
                }
            }
        }
    }
    Some(MfBranchPlan { needs, branch })
}

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
        let span =
            sc.span.and_then(|s| span_from_source_span(tcx, files, s)).unwrap_or(out[parent].span);
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

    /// Trust (wave-MF): mint the destination temp for an SSA result, `StorageLive`-marked exactly
    /// when the plan says built materialises one there ([`plan_operand_marker_temps`]). The
    /// marker goes in BEFORE this instruction's own operand temps, because that is where built
    /// puts it: `as_operand` on a sub-expression calls `as_temp`, which pushes `StorageLive` and
    /// only then builds the sub-expression into it (measured: `(a & b) == c` gives
    /// `StorageLive(_4); StorageLive(_5); _5 = copy _1; …; _4 = BitAnd(move _5, move _6)`).
    ///
    /// Trust (lane MF-R5): the plan's per-VALUE question is no longer asked HERE and answered
    /// somewhere else — [`ShimCx::mf_mark_result`] asks it and emits in one operation, inside the
    /// gate. The fifth review's second attack was to delete the per-value conjunct from this
    /// function and keep the per-body lease; there is no longer a conjunct here to delete.
    fn mf_result_temp(&mut self, bb: BasicBlock, r: ValueId, ty: RustcTy<'tcx>) -> Place<'tcx> {
        // Trust (lane K): does THIS instruction define the current block's `CondBr` condition?
        // Then built retires its operand temps at the ENTRY of both arms (their region scope is
        // the condition expression, which built exits on each outgoing edge), not here. Written
        // unconditionally so the flag can never survive into an unrelated instruction.
        self.mf_defer_deads = self.mf_cur_branch().is_some_and(|b| b.cond == r);
        let tmp = self.temp(ty);
        self.mf_mark_result(bb, r, tmp.local);
        tmp
    }

    /// Trust (lane K): the admitted `CondBr` of the producer block being lowered, if any.
    fn mf_cur_branch(&self) -> Option<MfBranch> {
        self.mf_plans.branch_at(self.mf_cur_blk?)
    }

    /// Trust (wave-MF): the MIR operand for `v` in built's OPERAND-TEMP discipline.
    ///
    /// * A constant is folded in place — built does the same (`Category::Constant`), so it takes
    ///   no temp and no marker.
    /// * A value already holding a marked temp (a sub-expression result) is MOVED out of it; the
    ///   temp joins `deads` so the caller retires it after the consuming assign.
    /// * Any other place (a param local, or an `ExtractField` field projection) is copied into a
    ///   fresh `StorageLive`-marked temp — byte-for-byte what built emits for `a` / `s.k` in an
    ///   operand position.
    ///
    /// Outside the plan (`mf_plan == None`) this is exactly [`ShimCx::operand`]: no temp, no
    /// marker, no behaviour change.
    fn mf_operand(
        &mut self,
        bb: BasicBlock,
        v: ValueId,
        deads: &mut Vec<Local>,
    ) -> Result<Operand<'tcx>, Unsupported> {
        let op = self.operand(v)?;
        // Trust (lane MF-R5): ONE test, asked of the gate. Outside the operand-temp class this
        // method is exactly [`ShimCx::operand`] — no temp, no marker, no behaviour change — and
        // the question is answered in the one module that answers it for every site.
        if !self.mf_operand_class() {
            return Ok(op);
        }
        if let Some(local) = self.mf_live.remove(&v) {
            deads.push(local);
            return Ok(Operand::Move(Place::from(local)));
        }
        let place = match op {
            Operand::Constant(_) => return Ok(op),
            Operand::Copy(p) | Operand::Move(p) => p,
            // `ShimCx::operand` mints only `Constant`/`Copy`/`Move` (it matches on `VOp`), so this
            // is unreachable — fail closed rather than pass an unmodelled operand through.
            _ => return unsup("wave-MF: unmodelled operand kind"),
        };
        let ty = place.ty(&self.local_decls, self.tcx).ty;
        let tmp = self.temp(ty);
        self.mf_mark_operand(bb, tmp.local);
        // `WithRetag::Yes` at every `Rvalue::Use` site, as elsewhere in this shim: rustc_mir_build
        // emits `Yes` at every builder assign site.
        self.assign(bb, tmp, Rvalue::Use(op, WithRetag::Yes));
        deads.push(tmp.local);
        Ok(Operand::Move(tmp))
    }

    /// Trust (wave-MF): retire this instruction's operand temps. Built emits the `StorageDead`s
    /// immediately after the consuming assign, in REVERSE operand order — which for a
    /// left-to-right evaluated tree is also reverse `StorageLive` order.
    ///
    /// Trust (B3-2a, wave-MF negative controls): `-Ztrust-sat-perturb=marker-order` retires them
    /// FORWARD and `=marker-drop` omits the last one. Both leave the derived body's VALUES
    /// untouched and corrupt only the marker sequence, so they test exactly one thing: that
    /// `markers_exact` is still a real predicate after wave-MF taught the shim to satisfy it. A
    /// perturbed body that still flips is a hole in the marker channel.
    fn mf_retire(&mut self, bb: BasicBlock, deads: &[Local]) {
        let mut order: Vec<Local> = deads.iter().rev().copied().collect();
        match self.sat_perturb {
            Some(SatPerturb::MarkerOrder) if order.len() >= 2 => {
                order.reverse();
                self.sat_perturb_count += 1;
            }
            Some(SatPerturb::MarkerDrop) if !order.is_empty() => {
                order.pop();
                self.sat_perturb_count += 1;
            }
            _ => {}
        }
        // Trust (lane K): the CONDITION's operand temps are not retired here — built retires
        // them at the entry of BOTH arms, in this same reverse order. Schedule, do not emit.
        if std::mem::take(&mut self.mf_defer_deads) {
            let Some(br) = self.mf_cur_branch() else {
                // `mf_defer_deads` is set only from `mf_cur_branch()`, one instruction earlier,
                // within the same block. Unreachable; leaving the deads unscheduled costs the
                // body its `markers_exact`, never its correctness.
                return;
            };
            let perturb = matches!(self.sat_perturb, Some(SatPerturb::MarkerArm));
            let (then_order, else_order, applied) = mf_split_arm_deads(order, perturb);
            if applied {
                self.sat_perturb_count += 1;
            }
            self.mf_entry_deads.entry(br.then_target).or_default().extend(then_order);
            self.mf_entry_deads.entry(br.else_target).or_default().extend(else_order);
            return;
        }
        // Trust (lane MF-R5): a retirement is the second half of a `StorageLive` the same plan
        // authorised, so it asks the same question — in the gate, at the moment of emission.
        // Outside the class `order` is empty anyway (no marked temp was ever minted); asking is
        // what makes that a checked fact rather than a reachability argument.
        self.mf_retire_at(bb, &order);
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
    /// field). `s_ty` is the ref-param pointee struct, `t_ty` the borrowed reference's pointee —
    /// scalar for the wave-29 RETURN caller, which gates it there; any CONCRETE type for the
    /// wave-30 ARG caller since T2e (see `try_reconstruct_interior_arg`, and the uniqueness note
    /// on `interior_field_at_offset_zero`).
    /// `K` is the UNIQUE offset-0 field of type `t_ty` — since the producer only emitted
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
                    "interior-borrow: no unique offset-0 field of the borrowed pointee type",
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
    /// When a forwarded ptr param (`got` = `&S`) is passed where the callee wants `want` = `&T` — the
    /// `g(&self.field)` case the producer erased to the base ptr — reconstruct the real
    /// `&((*place).K)` interior borrow, typed `want`. `Some(rvalue)` iff both `got` and `want` are
    /// SHARED refs and both `S` and `T` are CONCRETE (no non-region params/infers) and `S` has a
    /// unique offset-0 field of type `T`; `None` otherwise → the caller forwards the raw ptr, which
    /// fails the exact arg-type check (clean-only preserved, exactly as before wave-30).
    ///
    /// SINCE T2e `T` NEED NOT BE A FRAGMENT SCALAR. The retired `T ∈ {bool,int,uint}`
    /// (= `flip::scalar_ok` / the wave-29 RETURN gate) was never the source of the uniqueness this
    /// reconstruction needs — `interior_field_at_offset_zero` decides uniqueness itself and returns
    /// `None` on an ambiguous (ZST-tie) match — so it was replaced by the concreteness guards the
    /// helper's single-field shortcut actually requires (see the body comment and that helper's
    /// doc). Scalarity still binds DOWNSTREAM and is unchanged: `flip::place_ok` certifies
    /// `[Deref, Field(scalar)]` only, so a non-scalar interior borrow can reach `DerivedAgreed`
    /// but can NEVER reach a flip. The wave-29 RETURN caller keeps its own scalar gate.
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
        // Trust (T2e): the borrowed field no longer has to be a fragment SCALAR. The uniqueness
        // this reconstruction needs is delivered by `interior_field_at_offset_zero` ITSELF — it
        // returns `None` when two same-typed fields both sit at offset 0, refusing rather than
        // guessing — so scalarity was an ARGUMENT for uniqueness, never its source. What the
        // scalar test ALSO happened to exclude, and what therefore has to be spelled out now, is
        // an UNRESOLVED type: a generic/inference-bearing `t_ty` would take that helper's
        // single-field shortcut (which deliberately skips the layout query) and then be compared
        // for equality against a monomorphic field type. Both the struct and the pointee are
        // pinned concrete here, so the shortcut keeps the meaning its comment claims.
        //
        // This admits the DEPLOYED `<LevelArc as Deref>::deref` argument shape: `&self.0`, where
        // field 0 of the newtype is `Option<Arc<Level>>`, handed to
        // `Option::<Arc<Level>>::as_deref`. The producer erased exactly that borrow to the base
        // pointer (the wave-25 offset-0 tautology, `lib.rs` `field_byte_offset(..) == Some(0)`
        // -> `return pv`), and it emits that erasure ONLY when the borrow's OWN reference is THIN
        // (`fat_shape(&FieldTy) == Thin`) and the chain is exactly ONE field deep
        // (`field_deref_place` requires `chain.len() == 1`). So no DST field and no nested place
        // can reach here, and the reconstructed `&((*place).K)` is still a thin reference.
        //
        // Fidelity is unchanged and stays independently pinned OUTSIDE this shim: the comparator
        // renders the `[Deref, Field(K)]` borrow as `iref(a{p},K)` on BOTH sides
        // (`mir_differential.rs`), so a wrong `K` renders a different line and MISMATCHES instead
        // of agreeing; and the flip gate's `place_ok` still certifies `[Deref, Field(scalar)]`
        // ONLY, so a non-scalar interior borrow can reach `DerivedAgreed` but can NEVER reach a
        // flip. A non-reconstructable case still returns `None` and the caller forwards the raw
        // pointer into the exact arg-type check, which fails closed (clean-only).
        if t_ty.has_non_region_param()
            || t_ty.has_non_region_infer()
            || s_ty.has_non_region_param()
            || s_ty.has_non_region_infer()
        {
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
    //
    // Trust (wave-ABI, DEFENSE IN DEPTH): the denotation is CROSS-CHECKED against the built
    // decl type before it is adopted. This arm used to be the one ABI-visible position that
    // trusted the Module unilaterally — every OTHER arm below threads `built` and proves the
    // widening faithful, and the `Ty::Tuple` arm already proves per-element scalar equality
    // against the built tuple, so "producer scalar == built type" is an invariant this file
    // relies on elsewhere; it was simply never asserted where it mattered most. Unasserted, a
    // producer that spells a NON-scalar rustc type as a trust-ir scalar gets that respell
    // adopted silently: the wave-SEAM Option-flag lane spelled a declined `Option<T>` as
    // `Ty::Bool`, and this line minted `tcx.types.bool` for an `Option`-returning function.
    // The producer-side fix (`guard_sig_position_ty`) closes that at the source; this closes
    // the CLASS, so the next lane that widens an opaque spelling into a scalar meets a wall
    // here instead of an ABI lie. Cost is one `Ty` equality per scalar param.
    //
    // WHY THIS COSTS THE FLIP SET NOTHING, and the argument is not "we measured no change":
    // `flip.rs` already compares derived against built for EVERY ABI-visible local
    // (`for i in 0..=body.arg_count`) and rejects on any inequality. So a body that flips today
    // has ALREADY proven `derived[i].ty == built[i].ty` at exactly these positions — this check
    // is implied by a gate that runs downstream of it, and can therefore reject nothing that
    // currently flips. The only bodies it can newly refuse are differential-only ones, where a
    // refusal is precisely the fail-closed outcome wanted: a body whose Module and whose derived
    // MIR disagree about the function's own type is not one the differential should be comparing.
    if let Some(srt) = scalar_rustc_ty(tcx, p) {
        if srt != built {
            return unsup(format!(
                "param widening: trust-ir scalar {p:?} denotes {srt:?} vs built {built:?}"
            ));
        }
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

/// Trust (T2d): the admission test for the by-REF, READ-ONLY enum lane — the
/// twin of [`enum_flip_direct_only`], and the ONLY gate that admits a `Niche`
/// descriptor.
///
/// # Why `Direct`-only is the wrong test HERE (and stays the right test there)
///
/// `enum_flip_direct_only`'s refusal is about lanes that *reason about the
/// enum's bytes*: it names the construction reshape and `emit_enum_variant`,
/// whose width-masked compares turn a producer-emitted discriminant into a
/// concrete variant, and it is right that a normative `Niche` descriptor
/// changes what those bytes mean. Those call sites (`:1833` return-by-value,
/// `:1859` by-value enum param) are UNCHANGED and remain `Direct`-only.
///
/// The by-REF lane at the `Inst::Load { ty: Ty::Enum, .. }` arm does something
/// different in kind: it never reads a tag, never writes one, and never
/// consults the descriptor. It registers the loaded SSA value as denoting the
/// PLACE `(*P)`, and every consumer it can reach re-expresses the read in
/// rustc's own LOGICAL vocabulary —
///
/// * `extractfield %e, 0`   -> `Rvalue::Discriminant(place)` (`:4306`);
/// * `Inst::Switch`         -> case values matched against the AUTHORITATIVE
///                             `adt.discriminants(tcx)` (`:3548`);
/// * `extractfield %e, 1+k` -> `Downcast(V) + Field(k)` (`:4344`);
/// * the by-ref payload GEP -> `variant_field_at_offset`, which inverts the
///                             offset through RUSTC's own per-variant layout
///                             (`:546`).
///
/// There is no byte-level read on this path to be "descriptor-blind" about.
///
/// # Why the two encodings genuinely coincide here
///
/// This is not an appeal to the absence of a byte read alone; trust-ir's own
/// semantics make the two encodings agree on exactly the value this lane
/// consumes. `Load` of a `Ty::Enum` is defined by the reference interpreter
/// (`trust-ir/src/interpret.rs`, `decode_value`, `Ty::Enum` arm) to decode
/// THROUGH the normative descriptor and yield an aggregate whose **field 0 is
/// the variant's LOGICAL discriminant** under BOTH byte views:
///
/// * `EnumByteView::Direct` — decode the tag word, then resolve it via
///   `variant_by_discriminant`;
/// * `EnumByteView::Niche`  — decode the niche lane, map it to a variant
///   index, then push `layout.discriminants[variant_idx]`.
///
/// So `extractfield %e, 0` denotes the logical discriminant either way, which
/// is precisely what `Rvalue::Discriminant` denotes on the built side. The
/// encoding is a statement about the bytes in memory; both programs read
/// through it and neither re-implements it.
///
/// # What this does NOT relax
///
/// The lane's own soundness gates are untouched and still apply at the call
/// site: SHARED (`&`) reference only (a `&mut` could make the single derived
/// `Load` observe a stale discriminant), concrete non-generic pointee, and the
/// forwarded-pointer-param root. The loaded value is deliberately NOT bound in
/// `cx.env`, so any use other than the discriminant/payload reads that consult
/// these maps still fails closed in `operand()`. And the comparator remains the
/// arbiter: a derived body that reads a different variant or field than built
/// simply renders differently and is refused `DerivedAgreed`.
///
/// Fail-closed twice over: an unresolvable def is `false`, and the `matches!`
/// lists the two encodings EXHAUSTIVELY — a third `EnumTagEncoding` variant
/// added upstream is refused by this gate until someone re-argues it here.
///
/// MERGE NOTE (2026-08-11). A6 landed the same widening on `main` as
/// `enum_flip_ref_disc_ok`, spelled `module.enum_def(eid).is_some()` — i.e. any
/// RECORDED encoding admits, including a future third one nobody has argued
/// about. That spelling is retired here in favour of this one, which is the
/// same predicate on today's `EnumTagEncoding` and strictly narrower on
/// tomorrow's. There is exactly ONE call site (the
/// `Inst::Load { ty: Ty::Enum(eid), .. }` by-REF read through a forwarded
/// shared-ref param); the byte-reasoning sites keep `enum_flip_direct_only`.
///
/// The `layout: None` arm inherits `enum_flip_direct_only`'s recorded
/// fail-open verbatim and is NOT changed here either; on this lane it is
/// additionally moot, since both descriptor encodings are now admitted.
fn enum_flip_logical_read_ok(module: &trust_ir::Module, eid: trust_ir::EnumId) -> bool {
    match module.enum_def(eid) {
        None => false,
        Some(def) => match &def.layout {
            None => true,
            Some(desc) => matches!(
                desc.encoding,
                trust_ir::ty::EnumTagEncoding::Direct { .. }
                    | trust_ir::ty::EnumTagEncoding::Niche { .. }
            ),
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
        other => {
            Err(Unsupported { reason: format!("abi rederive: {other:?} body outside fragment") })
        }
    }
}

/// A MIR body plus the translator-owned correspondence from each input
/// TrustIR block identity to the first MIR block emitted for it.
///
/// The map is not source-loop authority: it says only where this invocation of
/// the translator placed an IR block.  The source-provenance gate separately
/// compares the mapped block's canonical CFG role against a compiler-stamped
/// built-MIR header.  Reordering `Function::blocks` therefore merely changes
/// raw MIR numbering; it cannot choose a source-loop/header association.
pub(crate) struct MirLowering<'tcx> {
    pub(crate) body: Body<'tcx>,
    pub(crate) ir_block_map: HashMap<BlockId, BasicBlock>,
}

pub(crate) fn lower_ir_to_mir<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    module: &Module,
    callees: &[CalleeRef],
    sig_source: SigSource<'tcx>,
    enum_fold_switches: &std::collections::HashSet<trust_ir::BlockId>,
) -> Result<MirLowering<'tcx>, Unsupported> {
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
    let source_provenance = crate::source_provenance::validated_source_provenance(tcx, def, module)
        .map_err(|reason| Unsupported { reason: format!("source provenance: {reason}") })?;
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
            // Trust (wave-ABI, DEFENSE IN DEPTH): the RETURN mirror of the `param_rty` scalar
            // cross-check — see the long note there. This is the exact line that minted a
            // `bool` `_0` for `expr::shift_bvar_range() -> Option<(u32,u32)>`: it adopted the
            // scalar denotation WITHOUT consulting `built_ret_ty`, while every neighbouring
            // arm below (Ptr, Struct, FatPtr) threads `built_ret_ty` as the ABI anchor
            // precisely because the Module is not an authority on identity (attack A1).
            Some(srt) if srt == built_ret_ty => srt,
            Some(srt) => {
                return unsup(format!(
                    "return widening: trust-ir scalar {t:?} denotes {srt:?} vs built \
                     {built_ret_ty:?}"
                ));
            }
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
                        // Trust (diagnostics 2026-08-11): SPLIT the three causes. They were one
                        // string, and it was the single largest refusal in the clean-kernel census
                        // (4,785 bodies) — with no way to tell from an artifact which condition
                        // actually fired, so no way to size any remediation. The name was also
                        // STALE: it says "non-Copy", but wave-X relaxed the gate from `Copy` to
                        // `!needs_drop` (see the comment above), and `Copy` has not been tested
                        // here since. Reporting a condition the code does not check sends a reader
                        // after the wrong thing.
                        ty::Adt(adt_def, _) if !adt_def.is_struct() => {
                            let kind = if adt_def.is_enum() {
                                "enum"
                            } else if adt_def.is_union() {
                                "union"
                            } else {
                                "adt"
                            };
                            return unsup(format!(
                                "aggregate return type is not a struct ({kind})"
                            ));
                        }
                        // A struct that reached here failed the ONLY other conjunct.
                        ty::Adt(..) => {
                            return unsup("aggregate return type is Drop-bearing".to_string());
                        }
                        _ => {
                            return unsup(format!(
                                "aggregate return type is not an ADT ({built_ret_ty:?})"
                            ));
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
    let mut source_scopes = build_source_scopes(
        tcx,
        tcx.local_def_id_to_hir_id(def),
        span,
        &module.files,
        func.scopes.as_deref(),
    )?;
    let mut provenance_scopes = HashMap::<BlockId, SourceScope>::new();
    if let Some(provenance) = &source_provenance {
        let owner = tcx.local_def_id_to_hir_id(def).owner;
        for source_loop in &provenance.loops {
            let local_id = ItemLocalId::from_u32(source_loop.hir_local_id);
            let hir_id = HirId { owner, local_id };
            let scope = source_scopes.push(SourceScopeData {
                span: tcx.hir_span(hir_id),
                parent_scope: Some(SourceScope::from_u32(0)),
                inlined: None,
                inlined_parent_scope: None,
                local_data: ClearCrossCrate::Set(SourceScopeLocalData {
                    // Match `rustc_mir_build`: a loop-authentication scope
                    // inherits the enclosing lint root and changes only the
                    // compact Trust loop identity. Reusing the loop HIR id as
                    // a lint root would make the flipped body observe a
                    // different lint context from its built sibling.
                    lint_root: tcx.local_def_id_to_hir_id(def),
                    trust_loop_hir_local_id: Some(local_id),
                }),
            });
            if provenance_scopes.insert(source_loop.header, scope).is_some() {
                return unsup("source provenance maps two source loops to one header");
            }
        }
    }
    // Trust (lane MF-R5): **THE PLANS ARE SEALED HERE AND NOWHERE ELSE.** `MfPlans::seal` is the
    // one constructor, it lives in `mf_gate`, and it is a pure function of this body: it reads the
    // same HIR source-form gate and the same trust-ir the four plans have always read, resolves
    // their MUTUAL EXCLUSIVITY (every marker plan is a claim about the WHOLE body, so two holding
    // at once is two whole-body claims about one body — the state the third review measured), and
    // hands back a value with private fields. No arm can widen it: `cx.mf_borrow = true` — the
    // fifth review's first attack, which bought a GENUINE lease and 46 admitted-and-wrong bodies —
    // does not compile, and the strongest legal spelling (re-sealing) recomputes the same answer.
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
        mf_plans: MfPlans::seal(tcx, def, func),
        mf_live: HashMap::new(),
        mf_cur_blk: None,
        mf_defer_deads: false,
        mf_entry_deads: HashMap::new(),
        mf_payload_dead: None,
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

    // Trust (E4/E5 source binding): one authenticated HIR source identity gets
    // one MIR storage place across every reconstructed loop header. Direct
    // parameters start at their ABI argument place; loop locals acquire a place
    // at their first authenticated header. Reusing the place is load-bearing:
    // two places for mutable parameter `n` recreate the measured false proof in
    // which the invariant binds the frozen entry copy instead of the loop value.
    let mut source_binding_places = direct_parameter_source_places(tcx, def, &arg_places);
    let mut source_binding_names = BTreeMap::<u32, String>::new();
    let mut source_name_bindings = BTreeMap::<String, u32>::new();
    if let Some(provenance) = &source_provenance {
        for source_loop in &provenance.loops {
            for binding in &source_loop.bindings {
                if trust_types::source_contract_synthetic_name_collision(&binding.name).is_some() {
                    return unsup("source provenance binding occupies Trust's synthetic namespace");
                }
                if let Some(previous) =
                    source_binding_names.insert(binding.hir_local_id, binding.name.clone())
                {
                    if previous != binding.name {
                        return unsup("one source HIR binding has multiple provenance names");
                    }
                }
                if let Some(previous) =
                    source_name_bindings.insert(binding.name.clone(), binding.hir_local_id)
                {
                    if previous != binding.hir_local_id {
                        // The current verifier body has one global formula namespace.
                        // Two hygienically distinct source bindings with one spelling
                        // cannot be represented by debug names alone, so keep the
                        // whole contracted flip closed for this body.
                        return unsup("one source provenance name denotes multiple HIR bindings");
                    }
                }
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
        let provenance_bindings = source_provenance
            .as_ref()
            .and_then(|provenance| {
                provenance.loops.iter().find(|source_loop| source_loop.header == blk.id)
            })
            .map(|source_loop| source_loop.bindings.as_slice())
            .unwrap_or_default();
        for (index, (v, pty)) in blk.params.iter().enumerate() {
            let rty = if let Some(binding) = provenance_bindings.get(index) {
                let source_ty =
                    source_binding_ty(tcx, def, binding.hir_local_id).ok_or_else(|| {
                        Unsupported {
                            reason: "source provenance HIR binding has no typeck type".into(),
                        }
                    })?;
                if cx.scalar_ty(pty) != Some(source_ty) {
                    return unsup(
                        "source provenance block parameter type does not match HIR binding",
                    );
                }
                source_ty
            } else {
                match cx.scalar_ty(pty) {
                    Some(t) => t,
                    // Type-carrying reason (an F32/F64 merge param is the float-body shape here;
                    // floats stay outside the shim's scalar fragment — see the return-type gate).
                    None => return unsup(format!("non-scalar block param {pty:?}")),
                }
            };
            let place = if let Some(binding) = provenance_bindings.get(index) {
                if let Some(place) = source_binding_places.get(&binding.hir_local_id).copied() {
                    if cx.local_decls[place.local].ty != rty {
                        return unsup("reused source provenance place has a different HIR type");
                    }
                    place
                } else {
                    let place = cx.temp(rty);
                    source_binding_places.insert(binding.hir_local_id, place);
                    place
                }
            } else {
                cx.temp(rty)
            };
            if let Some(binding) = provenance_bindings.get(index) {
                cx.local_decls[place.local].local_info =
                    ClearCrossCrate::Set(Box::new(LocalInfo::TrustSourceBinding {
                        hir_local_id: binding.hir_local_id,
                    }));
            }
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
    // Trust (lane MF-R6): the recognition is a PURE FUNCTION of `(func, ret_rty)` and the binding
    // it produces is IMMUTABLE. That is not tidiness — the sixth review's §3 named `agg_chains` as
    // the marker gate's second piece of shared state: `MfPlans::predict` counts the field operands
    // out of `agg_chains[v]` and the `Return` arm routes `agg_chains[v]`, so an arm that reversed
    // THE LIST ITSELF (`agg_chains.get_mut(&v).unwrap().reverse()`, one line, `let mut` in scope)
    // moved both readers together and neither number could change. Measured before this change:
    // one admitted-and-wrong body across 1,280 (`mfz2_residual::a11_duplicate_instr`,
    // `P2 { l: a & b, r: a & b }` — the producer does not CSE, so the two fields are two DIFFERENT
    // values that compute the same thing; swapping them leaves the derived body value-equal, which
    // is why the differential's value channel admits it and only the marker slots differ). With
    // the binding immutable that line does not compile, and `predict`'s aggregate term is a pure
    // function of this body's trust-ir with no writable path from any arm.
    let (agg_chain_skip, agg_chains) = agg_return_chains(func, ret_rty);
    agg_skip.extend(agg_chain_skip);

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

    // Trust (lane MF-ZERO-2, 2026-08-13): every SSA value's DEFINING instruction, whole-function.
    // The field-write arm reads built's `as_local_rvalue` category off this map; a `ValueId` that
    // is absent is a block PARAMETER. Built once, before any lowering, exactly like the two plans
    // — it is a pure function of `func` and must not depend on how far the walk has got.
    let write_rhs_value_def: HashMap<ValueId, &Inst> = func
        .blocks
        .iter()
        .flat_map(|b| b.body.iter())
        .flat_map(|n| n.results.iter().map(move |r| (*r, &n.inst)))
        .collect();

    // Trust (wave-CK, 2026-08-17): **THE CHECKED CHAIN'S TEMPS ARE OPENED BEFORE ANY LOWERING**,
    // because that is where built opens them. `as_operand` pushes a sub-expression's
    // `StorageLive` and only THEN builds into it, so for `a * b * c` — whose `assert`s split the
    // block twice — every temp is live at block 0, statement 0, in OUTERMOST-FIRST order (the
    // reverse of the producer's SSA order, which is the innermost-first postorder).
    //
    // Outside the class `mf_checked_chain` is empty and this loop does nothing at all: no temp, no
    // marker, no declaration — the body is bit-identical to what it was.
    let mut checked_temps: HashMap<ValueId, Place<'tcx>> = HashMap::new();
    {
        let chain = cx.mf_checked_chain();
        let entry_bb = cx.block_map[&func.entry];
        for (v, ity) in chain.iter().rev() {
            let Some(rty) = cx.scalar_ty(ity) else {
                return unsup("wave-CK: chain link type is not a body scalar");
            };
            let t = cx.temp(rty);
            if !cx.mf_mark_checked(entry_bb, *v, t.local, true) {
                // Unreachable: `mf_checked_chain` is the plan's own marked list. Fail closed
                // rather than declare a temp the plan will not retire.
                return unsup("wave-CK: the checked plan vanished between test and use");
            }
            checked_temps.insert(*v, t);
        }
    }

    // Translate each trust-ir block's instruction list into a chain of MIR blocks (asserts split
    // the chain). The producer guarantees exactly one terminator, last.
    for blk in &func.blocks {
        let mut cur = cx.block_map[&blk.id];
        let nodes: &[InstrNode] = &blk.body;
        // Trust (lane K): which producer block `mf_result_temp` / the `CondBr` arm are in.
        cx.mf_cur_blk = Some(blk.id);
        // Trust (lane K): built's CROSS-BLOCK markers — the dominating `CondBr`'s condition
        // operand temps on an arm entry, its condition result temp on a join — go FIRST, at
        // assign position 0, which is exactly where built puts them. The plan proves every arm
        // and join is lowered after its head, so nothing is scheduled into a block already past.
        if let Some(deads) = cx.mf_entry_deads.remove(&blk.id) {
            // Trust (lane MF-R5): scheduled by [`ShimCx::mf_retire`] under the same plan; asked
            // again here because the gate authorises the PUSH, not the schedule. A schedule with
            // no plan behind it is a body whose markers say something the shim did not do.
            if !cx.mf_retire_at(cur, &deads) {
                return unsup("lane K: cross-block markers scheduled without a marker plan");
            }
        }
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
            // Trust (T2, SHARED-REF payload-enum discriminant read): a whole-enum `Load` through
            // a forwarded SHARED-ref param is the `&self` twin of wave-V's by-VALUE `"EnumDisc"`
            // lane, and it is the ONE instruction standing between every `&self` enum method and
            // the flip. Measured on the by-value/by-ref probe pair: `disc_byval(e: E)` reached
            // `agreed`/`agreed` with `markers_exact` and flipped, while the byte-identical
            // `disc_byref(e: &E)` died here with "Load of a whole aggregate". Since essentially
            // every kernel enum accessor is `&self`, that single refusal blocked the whole class.
            //
            // The fix reuses the EXISTING arc rather than adding a parallel one. Wave-V already
            // turns `extractfield 0` on an `enum_disc_params` value into built's
            // `_d = Discriminant(place)`, reshapes the `Inst::Switch` into built's exhaustive form
            // (`enum_disc_temps`), and lowers payload reads as `Downcast(V)+Field(k)`
            // (`block_variant`). ALL of that is keyed off one map, so the by-ref case only has to
            // register the LOADED value against the DEREF place `(*P)` — the same place built MIR
            // projects — and every downstream stage is unchanged and already tested.
            //
            // Deliberately NOT bound in `cx.env` (the wave-V discipline): the loaded enum is a
            // declaration only, so any use of it OTHER than the discriminant/payload reads that
            // consult these maps fails closed in `operand()`. Consuming the node here also keeps
            // `aggregate_load_refusal` intact as the wall for every enum load this does NOT
            // recognize — the predicate is unchanged, and its `Ty::Enum` test still fires for a
            // load through anything that is not a shared-ref param.
            //
            // SHARED (`&`) only, and that is a soundness gate, not conservatism: trust-ir's `Load`
            // produces ONE SSA value, whereas built MIR re-reads `Discriminant((*P))` at the use
            // site. Those coincide only if the pointee cannot change in between — guaranteed for
            // `&T`, NOT for `&mut T`, where an intervening `Store` through the same pointer would
            // make the derived body read a stale discriminant.
            //
            // Concrete + DIRECT-tag mirror the by-value arm. Its Drop-free guard is deliberately
            // NOT carried over, and that is the difference that admits the crystal's own target.
            // Drop-freedom is an OWNERSHIP condition: the by-value lane declares the derived arg
            // with the built enum type, so the derived body would inherit the callee's obligation
            // to drop it. A shared reference owns nothing and drops nothing — `Discriminant((*P))`
            // emits no drop glue on either side, and rustc itself reads discriminants through `&`
            // on Drop-bearing enums constantly. Keeping the guard here would have excluded exactly
            // the bodies this job exists for: measured, `Level::is_zero_shallow` (whose `LevelArc`
            // payload holds an `Arc`, so the enum needs drop) stayed at "Load of a whole aggregate"
            // with the guard in place, and flipped once it was removed.
            if let Inst::Load { ty: Ty::Enum(eid), ptr, volatile: false, align: None } = &node.inst
            {
                if let (Some(&argplace), Some(&r)) =
                    (cx.fwd_ptr_params.get(ptr), node.results.first())
                {
                    let arg_rty = argplace.ty(&cx.local_decls, tcx).ty;
                    if let ty::Ref(_, pointee, m) = arg_rty.kind() {
                        if m.is_not()
                            // Trust (T2d / A6): the by-REF READ lane is judged by
                            // `enum_flip_logical_read_ok`, not by
                            // `enum_flip_direct_only`. See that function for why a
                            // `Niche` descriptor is admissible for a lane that reads
                            // only the LOGICAL discriminant, and why the by-VALUE
                            // construction lanes keep the `Direct`-only test
                            // unchanged.
                            //
                            // THIS IS THE ONLY CALL SITE OF THE NICHE-ADMITTING GATE.
                            // The two byte-reasoning sites — the by-value enum RETURN
                            // reshape and the by-value `Ty::Enum` PARAM — still call
                            // `enum_flip_direct_only`, and must keep calling it: they
                            // turn producer-emitted tag BYTES into a variant, which a
                            // normative `Niche` descriptor redefines.
                            //
                            // Safe by construction, not by argument: the codegen flip
                            // requires `DerivedAgreed` (`trust_ir_flip.rs`), so
                            // widening an admission FILTER can only move a body from
                            // `unsupported` to `agreed` or to `mismatch` — it can
                            // never replace shipped MIR with a body the comparator
                            // did not accept. A NEW `mismatch` here would be the
                            // signature of a bad widening, and the merge measurement
                            // recorded none.
                            && enum_flip_logical_read_ok(module, *eid)
                            && matches!(pointee.kind(), ty::Adt(a, _) if a.is_enum()
                                && !a.variants().is_empty())
                            && !pointee.has_non_region_param()
                            && !pointee.has_non_region_infer()
                        {
                            cx.enum_disc_params.insert(r, tcx.mk_place_deref(argplace));
                            i += 1;
                            continue;
                        }
                    }
                }
            }
            // Trust (T2b, by-REF enum PAYLOAD read): the companion to the discriminant read above.
            // Under a ref scrutinee the producer binds a payload as an interior GEP at the field's
            // rustc byte offset rather than as `extractfield %e, 1+k`, so the by-value payload arm
            // never saw it and the body stopped at `shim: Inst::GEP`. Re-emit it as the SAME place
            // built MIR projects — `((*P) as V).k` — reusing the by-value arm's construction
            // verbatim; only the way `V` and `k` are recovered differs.
            //
            // `V` comes from `block_variant`, which the `Inst::Switch` reshape already populated
            // (this block is a variant arm, entered under a known discriminant), and `k` is
            // inverted from the byte offset through rustc's OWN per-variant layout. A wrong
            // variant or field cannot miscompile: the derived `Downcast`/`Field` would simply
            // differ from built's and the comparator would withhold `DerivedAgreed`. A block with
            // no known variant, an offset matching no field (or several — a ZST tie), or a
            // non-scalar / type-disagreeing field all fall through to the untouched
            // `aggregate_load_refusal` wall below.
            if let Some((off, base, load_ty, r)) = recognize_ref_payload_read(nodes, i) {
                if let (Some(&argplace), Some(&vidx)) =
                    (cx.fwd_ptr_params.get(&base), cx.block_variant.get(&cur))
                {
                    let deref = tcx.mk_place_deref(argplace);
                    let enum_rty = deref.ty(&cx.local_decls, tcx).ty;
                    if let ty::Adt(adt, args) = enum_rty.kind() {
                        if adt.is_enum() && vidx.as_usize() < adt.variants().len() {
                            if let Some((fidx, field_ty)) =
                                variant_field_at_offset(tcx, enum_rty, *adt, args, vidx, off)
                            {
                                // The loaded trust-ir type must be exactly the field's scalar
                                // spelling — a width/signedness disagreement is a different read.
                                if cx.ir_scalar_of_body(field_ty).as_ref() == Some(&load_ty) {
                                    let dc = tcx.mk_place_downcast(deref, *adt, vidx);
                                    let fplace = tcx.mk_place_field(dc, fidx, field_ty);
                                    // Trust (wave-EP, 2026-08-16): under the ENUM-PAYLOAD-READ
                                    // marker plan, mint built's own arm-binding BORROW and read
                                    // THROUGH it — `StorageLive(t); t = &(((*P) as V).k);
                                    // <consumer> = copy (*t); StorageDead(t)` — instead of binding
                                    // the field place directly. That is the whole change: the same
                                    // two assignments built emits, in built's order, on a local
                                    // declared at built's `&FieldTy`, so the marker channel has a
                                    // slot to compare instead of reading `derived <end>`. The
                                    // retirement is scheduled, not emitted: built puts it AFTER the
                                    // assign that consumes the borrow, which is this block's `Br`
                                    // edge copy. OUTSIDE the plan this arm is byte-identical to
                                    // what it was — no temp, no borrow, no marker.
                                    if cx.mf_payload_arm(blk.id) {
                                        let ref_ty = RustcTy::new_ref(
                                            tcx,
                                            tcx.lifetimes.re_erased,
                                            field_ty,
                                            rustc_hir::Mutability::Not,
                                        );
                                        let tmp = cx.temp(ref_ty);
                                        if !cx.mf_mark_payload(cur, blk.id, tmp.local, true) {
                                            return unsup(
                                                "wave-EP: payload marker without a marker plan",
                                            );
                                        }
                                        cx.assign(
                                            cur,
                                            tmp,
                                            Rvalue::Ref(
                                                tcx.lifetimes.re_erased,
                                                BorrowKind::Shared,
                                                fplace,
                                            ),
                                        );
                                        cx.mf_payload_dead = Some(tmp.local);
                                        cx.env.insert(r, VOp::Plc(tcx.mk_place_deref(tmp)));
                                        i += 3;
                                        continue;
                                    }
                                    cx.env.insert(r, VOp::Plc(fplace));
                                    i += 3;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            // Trust (T2d, by-REF enum payload ADDRESS): the FORWARDING twin of the T2b read arm
            // above. `match self { Level::Max(l1, l2) => l1.is_zero() && .. }` never loads the
            // payload — it takes its ADDRESS and hands it to a call — so the producer emits the
            // `Const`/`GEP` pair with no `Load`, and the read arm (which requires the `Load`)
            // declined. Re-emit the borrow built MIR actually carries for that arm binding:
            // `_t = &(((*P) as V).k)` — the SAME `[Deref, Downcast, Field]` place, wrapped in the
            // shared `Rvalue::Ref` built spells as `_3 = &(((*_1) as Max).0: LevelArc)`.
            //
            // NO SCALAR GATE, and that is the substantive difference from the read arm rather
            // than a relaxation of it. The read arm gates on `ir_scalar_of_body(field_ty) ==
            // load_ty` because it must prove the LOADED VALUE's width and signedness agree with
            // what the producer read. This arm loads nothing: the payload's type appears only as
            // the pointee of the reconstructed reference, and the call-arg lane's EXACT type check
            // (`erase_and_anonymize_regions(got) == want`) re-pins it against the callee's
            // declared parameter type before the reference can be used for anything. A payload
            // whose address is taken and never dereferenced here needs no width argument, because
            // no width is read.
            //
            // Every other gate is the read arm's, unchanged: `V` from `block_variant` (populated
            // only by the already-reshaped switch, so this block is a variant arm entered under a
            // known discriminant), `k` inverted from the byte offset through RUSTC's own
            // per-variant layout (`variant_field_at_offset`, which fails closed on a ZST tie), and
            // a concrete non-generic field type. SHARED (`&`) base only — the emitted borrow is
            // `BorrowKind::Shared`, and a `&mut` scrutinee is a different program that must not be
            // spelled with a shared borrow. A wrong variant or field cannot miscompile: the
            // derived `Downcast`/`Field` would differ from built's and the comparator would
            // withhold `DerivedAgreed`.
            //
            // MERGE NOTE (2026-08-11). A6 landed the same arm on `main` WITHOUT the
            // shared-`&` base test and WITHOUT the concrete-field-type test, and sited it
            // ABOVE the read arm. This is that arm with both gates restored and sited BELOW
            // the read arm, so the read arm keeps first refusal on a triple it can own; the
            // recognizer's cede clause makes the two orders equivalent anyway.
            if let Some((off, base, r)) = recognize_ref_payload_addr(nodes, i) {
                if let (Some(&argplace), Some(&vidx)) =
                    (cx.fwd_ptr_params.get(&base), cx.block_variant.get(&cur))
                {
                    let arg_rty = argplace.ty(&cx.local_decls, tcx).ty;
                    if matches!(arg_rty.kind(), ty::Ref(_, _, m) if m.is_not()) {
                        let deref = tcx.mk_place_deref(argplace);
                        let enum_rty = deref.ty(&cx.local_decls, tcx).ty;
                        if let ty::Adt(adt, args) = enum_rty.kind() {
                            if adt.is_enum() && vidx.as_usize() < adt.variants().len() {
                                if let Some((fidx, field_ty)) =
                                    variant_field_at_offset(tcx, enum_rty, *adt, args, vidx, off)
                                {
                                    if !field_ty.has_non_region_param()
                                        && !field_ty.has_non_region_infer()
                                    {
                                        let dc = tcx.mk_place_downcast(deref, *adt, vidx);
                                        let fplace = tcx.mk_place_field(dc, fidx, field_ty);
                                        // Region ERASED, matching `reconstruct_interior_borrow`:
                                        // the flip's product exists only at runtime phases, where
                                        // no free regions survive.
                                        let ref_ty = RustcTy::new_ref(
                                            tcx,
                                            tcx.lifetimes.re_erased,
                                            field_ty,
                                            rustc_hir::Mutability::Not,
                                        );
                                        let tmp = cx.temp(ref_ty);
                                        cx.assign(
                                            cur,
                                            tmp,
                                            Rvalue::Ref(
                                                tcx.lifetimes.re_erased,
                                                BorrowKind::Shared,
                                                fplace,
                                            ),
                                        );
                                        cx.env.insert(r, VOp::Plc(tmp));
                                        i += 2;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
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
                // Trust (lane MF-ZERO-2, 2026-08-13): THE PREDICATE IS BUILT'S `as_local_rvalue`
                // CATEGORY, NOT `matches!(v_op, Operand::Constant(_))`.
                //
                // The wave-24b note above is true of a `Category::Place` right-hand side and FALSE
                // of the other two. `stmt_expr`'s `ExprKind::Assign` calls `as_local_rvalue(rhs)`,
                // which takes NO temp for `Category::Constant` **and none for any
                // `Category::Rvalue`** — only a `Category::Place` RHS goes `as_operand` → `as_temp`
                // and receives the marked temp. Lane MF-ZERO keyed on the constant alone, and an
                // independent review measured the cost: TWELVE admitted-and-wrong bodies survived,
                // every one in this arm. Verbatim built MIR from this driver, one line per
                // category:
                //
                //     s.h = 4u32 as u64;   // Category::Rvalue over a constant — ZERO markers
                //         ((*_1).2: u64) = const 4_u32 as u64 (IntToInt);
                //     s.h = v as u64;      // Category::Rvalue over a place — ONE temp, `v`'s TYPE
                //         StorageLive(_3); _3 = copy _2;
                //         ((*_1).2: u64) = move _3 as u64 (IntToInt); StorageDead(_3);
                //     s.h = *p;            // Category::Rvalue over a deref — ONE temp, at index 0
                //         StorageLive(_3); _3 = copy (*_2);
                //         ((*_1).2: u64) = move _3; StorageDead(_3);
                //     s.h = v;             // Category::Place — ONE temp; the shim was right here
                //         StorageLive(_3); _3 = copy _2;
                //         ((*_1).2: u64) = move _3; StorageDead(_3);
                //
                // Lane MF-ZERO's sweep missed it because its group E probed a BinOp RHS for the
                // rvalue case and recorded "e3 checked (unsupported)" — but that body is
                // `unsupported` for an unrelated reason (`type outside fragment: Ref { mutable:
                // true, .. }`), so no rvalue RHS was ever actually covered. A cast RHS and a load
                // RHS are `agreed`, are the same category, and were wrong.
                //
                // WHY THE CATEGORY IS READ OFF THE TRUST-IR AND NOT OFF `v_op`. This shim
                // materialises every computing instruction into a temp of its own, so by the time
                // the value reaches here a cast and a load both look like `Operand::Copy(<temp>)`
                // — indistinguishable from a place. `write_rhs_value_def` is the whole function's
                // value → defining-instruction map; absence means a block PARAM. Measured
                // trust-ir for the four shapes above: `%2 = zext u32 %1 to u64` / `%2 = zext u8 %1
                // to u64` / `%2 = load u64, ptr %1` / (no instruction at all — the store's value
                // IS the block param).
                //
                // BE RIGHT OR REFUSE, and both halves are real here:
                //
                //   * `Category::Constant` and `Category::Rvalue` both emit built's single assign
                //     with NO temp and NO marker. When built has no marker either — the folded
                //     `4u32 as u64`, every cast/binop over constants — the two sequences are EQUAL
                //     and the body is `markers_exact`. When built DOES mint one (`v as u64`, `*p`)
                //     it marks its own operand, at a statement index this shim has already spent
                //     materialising the instruction, so an EMPTY derived sequence is the honest
                //     answer: the oracle reads `built ... vs derived <end>` as a refusal and the
                //     body falls back to built MIR. A wrong marker is never emitted.
                //   * `Category::Place` — a block param (an argument local) or an `ExtractField`
                //     this shim folds into a field-projected MIR place, neither of which emits a
                //     statement of its own — keeps the wave-24b temp, at index 0, which is exactly
                //     where built puts it.
                //
                // An `ExtractField` off an `enum_disc_params` aggregate is NOT a place here: that
                // lowering mints `_d = Discriminant(place)`, a statement, which would shift the
                // marker exactly as a load does. It is classified with the rvalues, fail-closed.
                let rhs_is_place = match write_rhs_value_def.get(&vval) {
                    None => true,
                    Some(Inst::ExtractField { aggregate, .. }) => {
                        !cx.enum_disc_params.contains_key(aggregate)
                    }
                    Some(_) => false,
                };
                // Trust (lane MF-ZERO-3, 2026-08-13): **THE SCOPE, NOT THE PREDICATE.** Round 2
                // corrected `rhs_is_place` — which RHS category built gives a temp — and the third
                // review still measured SEVENTEEN admitted-and-wrong bodies, every one of them a
                // body in which this arm was right about its own temp and wrong about the body,
                // because it emitted with no plan's permission. `if c { w.a = v } else { w.b = v }`
                // was enough: built hoists the condition's temp into the head block, this arm knows
                // nothing about it, and derived line 0 is the write's temp where built's is the
                // condition's.
                //
                // The lease is the fix. `plan_field_write_markers` is a claim about the WHOLE body
                // — its writes are the only constructs in it that mint a built marker — and without
                // it this arm emits the same marker-free single assign it already emits for a
                // constant or an rvalue RHS. That form is measured, not new: it is exactly what
                // `!rhs_is_place` has always done, and it is why a refused body reads as
                // `built ... vs derived <end>` (an honest refusal, falling back to built MIR)
                // rather than as a wrong marker.
                if !rhs_is_place || !cx.mf_write_admits() {
                    cx.assign(cur, fplace, Rvalue::Use(v_op, WithRetag::Yes));
                    i += 3;
                    continue;
                }
                let tmp = cx.temp(field_rty);
                if !cx.mf_mark_write(cur, tmp.local, true) {
                    // Unreachable: the plans are SEALED and `mf_write_admits` said yes one line
                    // ago. Fail closed rather than emit half a pair.
                    return unsup("wave-24b: the field-write plan vanished between test and use");
                }
                // Trust: rust 1.99 — `Rvalue::Use` carries a `WithRetag` payload (the retag
                // became an operand-level annotation). rustc_mir_build emits `WithRetag::Yes`
                // at every builder assign site (no `::No` anywhere in that crate), so the
                // byte-faithful mirror here is `Yes` — at all `Rvalue::Use` sites in this shim.
                cx.assign(cur, tmp, Rvalue::Use(v_op, WithRetag::Yes));
                cx.assign(cur, fplace, Rvalue::Use(Operand::Move(tmp), WithRetag::Yes));
                cx.mf_mark_write(cur, tmp.local, false);
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
                    // Trust (wave-CK, 2026-08-17): inside the checked-arithmetic chain, built does
                    // NOT read the tuple's `.0` in place — the sub-expression it just finished IS
                    // an `as_operand` -> `as_temp` operand temp, so it materialises
                    // `_t = move (_tup.0)` in the assert's SUCCESS block and hands `_t` to the
                    // parent. Reproducing that assign is what puts the retirement below at built's
                    // canonical position (one assign into this block) instead of one statement
                    // earlier, and it is a statement built emits, not one invented here.
                    //
                    // Outside the class `checked_temps` is empty, `env` keeps the projected place,
                    // and this arm is bit-identical to what it was.
                    if let Some(t) = checked_temps.get(&res).copied() {
                        cx.assign(
                            cur,
                            t,
                            Rvalue::Use(Operand::Move(val_place), WithRetag::Yes),
                        );
                        cx.env.insert(res, VOp::Plc(t));
                        // The retirement of the PREVIOUS link, right after the assign just made —
                        // built's schedule, and the reason this class needed a plan of its own:
                        // the assign that CONSUMES that temp is a block earlier, on the far side
                        // of this unit's assert.
                        //
                        // MEASURED, and it is why this sits INSIDE the materialisation branch: the
                        // outermost link has no temp and no destination write here (built writes it
                        // straight into `_0`, which the `Return` arm does), so retiring its
                        // predecessor here puts the marker at assign 0 of this block where built
                        // has it at assign 1. The law caught exactly that —
                        // `predicted mk b2.1:dead vs derived mk b2.0:dead` — and the `Return` arm
                        // owns that one retirement.
                        if let Some(p) = cx.mf_checked_pred(res) {
                            let Some(pt) = checked_temps.get(&p).copied() else {
                                return unsup("wave-CK: chain predecessor has no temp");
                            };
                            if !cx.mf_mark_checked(cur, p, pt.local, false) {
                                return unsup(
                                    "wave-CK: the checked plan refused its own retirement",
                                );
                            }
                        }
                    }
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
                    // Trust (wave-MF): see the `Inst::BinOp` arm. Built spells the cast's operand
                    // temp identically (`StorageLive(_2); _2 = copy (_1.0: u32);
                    // _0 = move _2 as usize (IntToInt); StorageDead(_2)`).
                    let tmp = cx.mf_result_temp(cur, r, rty);
                    let mut deads = Vec::new();
                    let o = cx.mf_operand(cur, *operand, &mut deads)?;
                    cx.assign(cur, tmp, Rvalue::Cast(CastKind::IntToInt, o, rty));
                    cx.mf_retire(cur, &deads);
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
                    // Trust (wave-MF): result temp FIRST (built's `as_temp` pushes its
                    // `StorageLive` before evaluating the sub-expression), then the operand temps
                    // left-to-right, then the assign, then the deads in reverse.
                    let tmp = cx.mf_result_temp(cur, r, rty);
                    let mut deads = Vec::new();
                    let l = cx.mf_operand(cur, *lhs, &mut deads)?;
                    let rr = cx.mf_operand(cur, *rhs, &mut deads)?;
                    cx.assign(cur, tmp, Rvalue::BinaryOp(mir_op, Box::new((l, rr))));
                    cx.mf_retire(cur, &deads);
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
                    // Trust (wave-MF): see the `Inst::BinOp` arm.
                    let tmp = cx.mf_result_temp(cur, r, tcx.types.bool);
                    let mut deads = Vec::new();
                    let l = cx.mf_operand(cur, *lhs, &mut deads)?;
                    let rr = cx.mf_operand(cur, *rhs, &mut deads)?;
                    cx.assign(cur, tmp, Rvalue::BinaryOp(mir_op, Box::new((l, rr))));
                    cx.mf_retire(cur, &deads);
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
                    // Trust (wave-MF): see the `Inst::BinOp` arm.
                    let tmp = cx.mf_result_temp(cur, r, rty);
                    let mut deads = Vec::new();
                    let o = cx.mf_operand(cur, *operand, &mut deads)?;
                    cx.assign(cur, tmp, Rvalue::UnaryOp(mir_op, o));
                    cx.mf_retire(cur, &deads);
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
                            // Trust (lane L): built sends every NON-CONSTANT field through
                            // `as_operand`→`as_temp` in FIELD order and retires them after the
                            // aggregate assign in REVERSE field order — the same discipline
                            // wave-MF reproduces for an rvalue's operands, one level up. Outside
                            // the marker plan `mf_operand` IS `operand` (no temp, no marker), so
                            // this line is byte-identical to the pre-lane-L path for every body
                            // the plan does not admit.
                            let mut agg_deads: Vec<Local> = Vec::new();
                            // Trust (lane L, negative control): `-Ztrust-sat-perturb=
                            // agg-field-order` walks the fields BACKWARDS, which corrupts the
                            // `StorageLive` sequence while leaving every value correct (the
                            // operands are re-indexed into field order below).
                            let walk: Vec<usize> =
                                if cx.sat_perturb == Some(SatPerturb::AggFieldOrder) {
                                    (0..field_vals.len()).rev().collect()
                                } else {
                                    (0..field_vals.len()).collect()
                                };
                            let mut slots: Vec<Option<Operand<'tcx>>> =
                                (0..field_vals.len()).map(|_| None).collect();
                            for k in walk {
                                slots[k] =
                                    Some(cx.mf_operand(cur, field_vals[k], &mut agg_deads)?);
                            }
                            if cx.sat_perturb == Some(SatPerturb::AggFieldOrder)
                                && agg_deads.len() >= 2
                            {
                                cx.sat_perturb_count += 1;
                            }
                            let Some(field_ops) = slots.into_iter().collect::<Option<Vec<_>>>()
                            else {
                                return unsup("aggregate return: field operand went unresolved");
                            };
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
                            // Trust (lane L): reverse field order, after the aggregate assign —
                            // `mf_retire` reverses what `mf_operand` pushed in field order.
                            cx.mf_retire(cur, &agg_deads);
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
                                            // Trust (lane MF-ZERO-3): the SECOND ungated site the
                                            // review named, closed the same way. The reborrow-temp
                                            // form is emitted only when the interior-borrow plan
                                            // admits the body; otherwise the DIRECT form
                                            // (`_0 = &((*_1).K)`, wave-29's original shape, which
                                            // was already byte-identical at `-O0`) ships with no
                                            // marker at all. Nothing here is a new emission — the
                                            // choice between the two shapes is now a plan's.
                                            if cx.mf_borrow_admits() {
                                                let tmp = cx.temp(ret_rty);
                                                cx.mf_mark_borrow(cur, tmp.local, true);
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
                                                cx.mf_mark_borrow(cur, tmp.local, false);
                                            } else {
                                                cx.assign(
                                                    cur,
                                                    Place::from(rustc_middle::mir::RETURN_PLACE),
                                                    rv,
                                                );
                                            }
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
                    // Trust (wave-CK, 2026-08-17): the LAST chain link is the outermost expression
                    // — built writes it straight into `_0` and gives it no temp — so the temp that
                    // retires after that write is its PREDECESSOR's. Same rule as the Overflow arm
                    // above, at the one destination write that arm does not perform. Outside the
                    // class `mf_checked_pred` is `None` and nothing happens.
                    if let Some(&v) = values.first() {
                        if let Some(p) = cx.mf_checked_pred(v) {
                            let Some(pt) = checked_temps.get(&p).copied() else {
                                return unsup("wave-CK: chain predecessor has no temp at Return");
                            };
                            if !cx.mf_mark_checked(cur, p, pt.local, false) {
                                return unsup(
                                    "wave-CK: the checked plan refused its final retirement",
                                );
                            }
                        }
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
                            // A source parameter/header place intentionally
                            // reuses its ABI/local storage. The initial edge for
                            // an unchanged binding is therefore `_n = copy _n`;
                            // omit that exact self-assignment, which is semantic
                            // noise absent from built MIR. Every changed backedge
                            // still assigns its new operand normally.
                            let exact_self_assignment = matches!(
                                &o,
                                Operand::Copy(source) | Operand::Move(source) if *source == *place
                            );
                            if !exact_self_assignment {
                                cx.assign(cur, *place, Rvalue::Use(o, WithRetag::Yes));
                            }
                        }
                    }
                    // Trust (wave-EP): the payload borrow temp's `StorageDead`, at built's
                    // position — AFTER the edge copy that consumes it and before the block's
                    // terminator. Asked of the gate again here, because the gate authorises the
                    // PUSH and not the schedule; a schedule with no plan behind it is a body whose
                    // markers say something the shim did not do.
                    if let Some(local) = cx.mf_payload_dead.take() {
                        if !cx.mf_mark_payload(cur, blk.id, local, false) {
                            return unsup("wave-EP: payload retirement without a marker plan");
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
                    let mut c = cx.operand(*cond)?;
                    // Trust (lane K): multi-block marker fidelity, both halves at one site.
                    let mut false_edge = else_bb;
                    if let Some(br) = cx.mf_cur_branch() {
                        // (a) The condition's own temp dies at the JOIN, at position 0 — built's
                        //     `bb4: StorageDead(_3); return`. Taking it out of `mf_live` here is
                        //     also what keeps the body's marker balance provable: the `CondBr` is
                        //     the consumer, and it is the only one the four rvalue arms cannot
                        //     reach. Absent => the plan and the emitter disagree; fail CLOSED.
                        let Some(local) = cx.mf_live.remove(cond) else {
                            return unsup("lane K: CondBr condition carries no marked temp");
                        };
                        cx.mf_entry_deads.entry(br.join).or_default().push(local);
                        // Built moves out of the condition temp (`switchInt(move _3)`); with the
                        // temp now retired downstream this shim can spell it the same way.
                        c = Operand::Move(Place::from(local));
                        // (b) Built ALWAYS routes the false (`0`) edge through an EMPTY
                        //     trampoline block. `canon_markers` walks the RAW CFG with no goto
                        //     threading, so without it every fine block index after the branch
                        //     shifts and the channel refuses. The SEMANTIC channel threads every
                        //     `Goto` block onto its incoming edges (LEDGER L3), so the extra
                        //     block is invisible there — it can cost no `agreed`.
                        let tramp = cx.new_block();
                        cx.terminate(tramp, TerminatorKind::Goto { target: else_bb })?;
                        false_edge = tramp;
                    }
                    // Same encoding as the MIR builder: SwitchTargets::static_if(0, else, then).
                    cx.terminate(cur, TerminatorKind::if_(c, then_bb, false_edge))?;
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
                    //
                    // Trust (enum-switch provenance): "exactly one tag missing" USED TO BE the whole
                    // test, and it is not sufficient. A one-variant WILDCARD (`matches!(x, A | C)` on
                    // a 3-variant enum) presents identically in the IR yet built keeps `otherwise ->
                    // the _ arm` with NO unreachable — reshaping it manufactures a body that can
                    // never match. The producer publishes which provenance this switch's `default`
                    // carries (`Lowered::enum_fold_switch_blocks`); consult it FIRST so the reshape
                    // fires only on a genuine exhaustive fold. The missing-tag count stays as a
                    // corroborating fail-closed check below: provenance says the last variant was
                    // popped, so EXACTLY ONE tag must be absent, and a disagreement leaves the
                    // switch verbatim rather than trusting either signal alone.
                    //
                    // The flag gates ONLY the reshape. The enclosing block also records
                    // `block_variant` (so a payload read inside an arm can Downcast) and applies the
                    // wave-YM canonical case sort — both are required for EVERY enum switch, wildcard
                    // included, so gating the whole block would break bodies that agree today.
                    let exhaustive_fold = enum_fold_switches.contains(&blk.id);
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
                        if exhaustive_fold && missing.len() == 1 {
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
                        // Trust (wave-YM, CORRECTED 2026-08-17): emit the SwitchInt cases in built's
                        // canonical order, which is VARIANT INDEX order — not ascending discriminant
                        // value. The producer emits them in ARM order, so a canonicalization is
                        // genuinely needed (wave-YM's finding: `match o { Some(x) => .., None => .. }`
                        // emits disc 1 before disc 0 and the canonical block layout diverges). But the
                        // order to canonicalize ONTO is built's, and built's is read off ONE line of
                        // rustc: `TestKind::Switch` (rustc_mir_build/src/builder/matches/test.rs:83)
                        // builds its targets from `adt_def.discriminants(tcx).filter_map(..)`, which
                        // yields variants in VariantIdx order, and `SwitchTargets::new`
                        // (rustc_middle/src/mir/terminator.rs:20) unzips that iterator verbatim with no
                        // sort. Built never orders by value.
                        //
                        // wave-YM's ascending sort agreed with that on every enum it was measured on,
                        // because it only ever saw enums whose discriminants ASCEND with the variant
                        // index (Option, Result, `Dir`, `E`), where the two orders coincide. They come
                        // apart the moment a `#[repr(uN)]`/explicit-discriminant enum declares its
                        // variants out of numeric order — `enum { Hi = 900, Lo(u32) = 1 }` is built
                        // `[900, 1]` (VariantIdx) and was derived `[1, 900]` (ascending), a standing
                        // `derived_mir: mismatch` on `ep_review_corpus_c::Ordered::v`. Variant-index
                        // order is therefore a STRICT GENERALIZATION of the ascending sort, not a
                        // trade against it: it reproduces it exactly whenever discriminants ascend with
                        // the variant index, and is right in the cases where it did not.
                        //
                        // A case value that is not a discriminant of this ADT cannot occur in a built
                        // `TestKind::Switch`, so such a body is already refused whatever the order; it
                        // is sorted AFTER every real tag, by value, which is where the ascending sort
                        // also left the `enum-case-value` SAT control's out-of-domain tag. `sort_by_key`
                        // is stable, so equal keys keep arm order. Enum-reshape ONLY — an integer
                        // `Inst::Switch` (wave-R) is untouched (this is inside the `enum_reshape` block).
                        targets.sort_by_key(|(v, _)| enum_switch_case_order_key(&disc_to_vidx, *v));
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
                    // Trust (wave-EP, 2026-08-16): the ENUM-PAYLOAD-READ plan's TRAMPOLINE. Built's
                    // match lowering mints one empty `falseEdge` block per non-last candidate, and
                    // `mir_differential::canon_markers` walks the RAW CFG with no goto threading —
                    // so a derived body missing that block has every fine block index after it
                    // shifted and the marker channel refuses, whatever the markers themselves say.
                    // MEASURED on both shipped bodies: built puts the marker at fine index 2 when
                    // the payload arm is FIRST (`Reducibility::height`) and at fine index 4 when it
                    // is SECOND (`SimpPriority::value`), and one empty `Goto` on the first arm's
                    // edge reproduces both. This is lane K's trampoline argument, one construct
                    // over: it only ADDS an empty block, the semantic channel threads every `Goto`
                    // onto its incoming edges (LEDGER L3), and it is minted ONLY when this plan
                    // engages.
                    //
                    // Sited HERE — after `block_variant` recording, after the exhaustive-fold
                    // reshape, after the wave-YM sort and after every SAT perturbation — so the
                    // redirect can neither hide a corrupted routing nor steal the variant record
                    // the payload arm needs to `Downcast`.
                    let mut tramp_bb =
                        cx.mf_payload_tramp_block().and_then(|b| cx.block_map.get(&b).copied());
                    // SAT control (wave-EP REVIEW `PayloadTramp`): move the trampoline onto the
                    // OTHER outgoing edge. Semantically inert — an empty `Goto` on either edge is
                    // the same program — so the derived-MIR channel cannot refuse it and only
                    // `canon_markers`' RAW-CFG block position can. See [`SatPerturb::PayloadTramp`].
                    if cx.sat_perturb == Some(SatPerturb::PayloadTramp) {
                        if let Some(want) = tramp_bb {
                            let other = targets
                                .iter()
                                .map(|(_, t)| *t)
                                .chain(std::iter::once(default_bb))
                                .find(|t| *t != want);
                            if let Some(o) = other {
                                cx.sat_perturb_count += 1;
                                tramp_bb = Some(o);
                            }
                        }
                    }
                    if let Some(want) = tramp_bb {
                        for (_, tbb) in targets.iter_mut() {
                            if *tbb == want {
                                let tramp = cx.new_block();
                                cx.terminate(tramp, TerminatorKind::Goto { target: want })?;
                                *tbb = tramp;
                            }
                        }
                        if default_bb == want {
                            let tramp = cx.new_block();
                            cx.terminate(tramp, TerminatorKind::Goto { target: want })?;
                            default_bb = tramp;
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
                    //
                    // Trust (lane L): that temp is ALSO exactly built's `as_operand`→`as_temp`
                    // operand temp for `*p` in a shared-ref-param read — measured, `*p == 0`
                    // builds to `StorageLive(_2); _2 = copy (*_1); _0 = Eq(move _2, const 0);
                    // StorageDead(_2)` — so it takes the marker pair when the plan says so.
                    // NOT DISCHARGED BY THIS, and measured rather than assumed: a closure whose
                    // parameter is a DESTRUCTURING pattern (`|&l| l == 0`, i.e.
                    // `BigNat::is_zero::{closure#0}`) lowers to the SAME four-instruction
                    // trust-ir (`load; const; icmp; ret`) but to a built body with FOUR markers —
                    // the pattern mints a named binding local `_3` with its own pair, plus an
                    // unreachable `FakeRead` block — and it carries NO scope table, so
                    // `func.scopes.is_none()` does not see it. That body stays refused, by the
                    // ORACLE.
                    let rty = cx.scalar_ty(ty).expect("slot pointee proven scalar");
                    let tmp = cx.mf_result_temp(cur, r, rty);
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
                    let Some(site_args) = rebuild_site_args(tcx, enc) else {
                        // A const arg whose (bits, size) does not name a `ScalarInt`. Unreachable
                        // for encodings this crate produced; declining keeps it that way instead
                        // of asserting it.
                        return unsup("Call(callee site args not encodable / not concrete-mono)");
                    };
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
                    // Trust (#48): the FOURTH copy of the reveal guard, and the last
                    // one measured on a `check-pass` upstream test. Instrumenting
                    // every normalize site in this crate showed THIS is the one on
                    // `method_resolution5.rs`'s cycle path: the callee signature of
                    // `Bar<Foo>::bar` carries `type Foo = impl Sized` in its `self`
                    // parameter, so `has_opaque_types()` is false (a free alias is
                    // HAS_TY_FREE_ALIAS) and normalizing the SIGNATURE reveals the
                    // TAIT from inside `mir_built`. Two earlier guesses at the site
                    // were wrong; the probe settled it.
                    let sig_reaches_opaque = sig.inputs_and_output.iter().any(|ty| {
                        crate::free_alias_reaches_opaque(tcx, ty)
                            || crate::projection_reaches_opaque(tcx, ty)
                    });
                    let sig = if sig.has_non_region_param()
                        || sig.has_non_region_infer()
                        || sig.has_non_region_placeholders()
                        || sig.has_opaque_types()
                        || sig_reaches_opaque
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
                            //
                            // Trust (T2d): a SHARED-REFERENCE callee return (`&T`) joins the same
                            // arm. This is the `<LevelArc as Deref>::deref(&payload) -> &Level`
                            // shape — the accessor a by-ref recursive match calls between taking a
                            // payload's address and recursing on it, and the reason
                            // `Level::is_zero` stopped here once the payload-address lane started
                            // producing the argument.
                            //
                            // It satisfies wave-J's OWN admission argument by construction rather
                            // than by analogy: a `&T` is `Copy` and `!needs_drop` for every `T`, so
                            // `ElaborateDrops`/`AbortUnwindingCalls` stay no-ops on the dest temp
                            // and the Continue-everywhere pass-totality the flip relies on is
                            // untouched. The dest temp is typed from the ABI-pinned, normalized
                            // callee signature (regions erased), which is exactly the type built
                            // MIR gives its own call destination — `_6: &Level` on both sides.
                            //
                            // SHARED only. A `&mut T` result is a write capability: the callee
                            // could be handed it and mutate caller memory, and this comparator
                            // records a caller-memory effect ONLY for the `(*_p).k = v` shape it
                            // models explicitly (`Env::memseq`) — so admitting `&mut` here would
                            // create exactly the invisible-store blind spot that observable exists
                            // to close. A raw pointer is out for the same reason and additionally
                            // carries no aliasing discipline. Generic/inference-bearing returns
                            // stay closed, as in the struct case.
                            //
                            // Nothing downstream is loosened: the result is an ordinary value in
                            // the canonical form (`dest = call(..); <use of dest>`), and every use
                            // is independently gated — as a further call argument by the EXACT
                            // arg-type check below, as anything else by the arm that models it.
                            //
                            // Trust (T2e): a by-value ENUM callee return joins the arm ONLY when
                            // its layout is a single immediate `BackendRepr::Scalar`. That is the
                            // niche-encoded `Option<&T>` shape —
                            // `Option::<Arc<Level>>::as_deref(&self.0) -> Option<&Level>`, the
                            // accessor the DEPLOYED `<LevelArc as Deref>::deref` calls before
                            // `expect`, and the one arm between that body and the fragment.
                            //
                            // The condition is spelled as an ABI CLASS, not as "enums too", and
                            // that spelling is load-bearing. TWO other gates match
                            // `ty::Adt(adt, _) if adt.is_struct()` and would therefore NOT see an
                            // enum: wave-GH2's one-shot `Copy`->`Move` argument re-spell (below)
                            // and `flip::gate_derived_body`'s memory-ABI parity fail-close
                            // ("whole-struct Copy call arg with memory ABI"). A MEMORY-ABI call
                            // result later handed on as an argument is passed INDIRECTLY, where
                            // codegen_ssa gives a `Copy` arg a defensive fresh-alloca+memcpy and
                            // `Move` passes the temp's own address — a codegen-visible difference
                            // the comparator folds away (LEDGER L8's Move==Copy). An enum admitted
                            // by a bare `adt.is_enum()` could slip past both gates into exactly
                            // that blind spot. `BackendRepr::Scalar` is passed in ONE register
                            // under either spelling, so the divergence cannot exist for it and
                            // neither struct-only gate has to widen. `ScalarPair` is deliberately
                            // NOT admitted: it is immediate too, but it buys nothing here and it
                            // is the shape whose argument spelling those gates would then have to
                            // reason about.
                            //
                            // Everything else is wave-J's own admission argument, unchanged and
                            // still enforced below: `Copy` + `!needs_drop` keeps
                            // `ElaborateDrops`/`AbortUnwindingCalls` no-ops (the Continue-everywhere
                            // pass-totality the flip relies on), the dest temp is typed from the
                            // ABI-pinned, normalized callee signature — so `dest: Option<&Level> =
                            // as_deref(..)` is what built MIR emits — and every downstream use
                            // stays independently gated: as a further call argument by the EXACT
                            // arg-type check below, and as a field read by the `ExtractField` arm,
                            // which refuses a non-struct base and so fails closed on an enum.
                            // The layout consult is the reentrancy-guarded `cycle_safe_layout_of`
                            // (this shim can run inside `mir_built`); an unavailable or erroring
                            // layout REFUSES, like every other layout consult on this path.
                            None => {
                                let te = ty::TypingEnv::fully_monomorphized();
                                // Trust (A6): a SHARED-REF callee return joins the by-value
                                // Copy+Drop-free struct lane, on the same argument. The dest temp
                                // is typed with the REAL rustc type from the ABI-pinned normalized
                                // callee sig, so `dest: &T = f(..)` is byte-identical to what built
                                // MIR emits; `&T` is Copy and Drop-free by construction, so
                                // ElaborateDrops stays the no-op the flip relies on; and the
                                // returned reference is fully observable in the canonical
                                // `dest = call(..); <use of dest>` form with no hidden caller-memory
                                // effect — reading THROUGH it is separately gated by the arms that
                                // consume a place. Regions are erased in post-analysis
                                // Runtime(Optimized) MIR, and the has_non_region_param/infer guards
                                // above still exclude an unresolved pointee. `&mut` is NOT admitted:
                                // it is neither Copy nor free of aliasing obligations, and the
                                // comparator has no observable for a write through it.
                                // Trust (T2e): the ABI-class enum disjunct. `cycle_safe_layout_of`
                                // carries the reentrancy guard AND the `.ok()`, so an unresolved
                                // type, a query that would re-enter, and a `LayoutError` all land
                                // on `None` and REFUSE.
                                let enum_scalar_abi = matches!(
                                    ret_rty_callee.kind(),
                                    ty::Adt(adt, _) if adt.is_enum()
                                ) && matches!(
                                    crate::cycle_safe_layout_of(tcx, te, ret_rty_callee)
                                        .map(|l| l.backend_repr),
                                    Some(rustc_abi::BackendRepr::Scalar(_))
                                );
                                let admit = !ret_rty_callee.has_non_region_param()
                                    && !ret_rty_callee.has_non_region_infer()
                                    && (matches!(
                                        ret_rty_callee.kind(),
                                        ty::Adt(adt, _) if adt.is_struct()
                                    ) || matches!(
                                        ret_rty_callee.kind(),
                                        ty::Ref(_, _, m) if m.is_not()
                                    ) || enum_scalar_abi)
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
                    // Trust (#33): the callee ConstOperand's span. Diagnostics-only — a
                    // ConstOperand span never reaches the line table — but built puts the
                    // callee-path span here, so the call site's span is strictly closer than
                    // the body-constant def_span.
                    let func =
                        Operand::function_handle(tcx, site_def_id, site_args, cx.source_info.span);
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
                            // Trust (#33): the CALL SITE's span, not the body-constant
                            // `cx.span` (= `tcx.def_span(def)`, the fn HEAD).
                            //
                            // For a Call terminator, codegen does NOT use
                            // `terminator.source_info.span`:
                            // `rustc_codegen_ssa/src/mir/block.rs` builds
                            // `SourceInfo { span: fn_span, ..terminator.source_info }` before
                            // `set_debug_loc`. So `fn_span` — and only `fn_span` — decides the
                            // DWARF row, and the span `set_span_from_node` carefully repairs is
                            // discarded for exactly this terminator kind. Handing it def_span
                            // put EVERY derived call row on the enclosing item's `fn` keyword,
                            // identically for every call in the body: measured as built 12:53 vs
                            // derived 12:40, and built 16:9 vs derived 11:5.
                            //
                            // `cx.source_info` is this node's, because `set_span_from_node` runs
                            // at the top of the node loop before this arm.
                            fn_span: cx.source_info.span,
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

    // Trust (lane MF-R7, 2026-08-14): **THE MARKER LAW — TWO DERIVATIONS OF ONE SEQUENCE.**
    //
    // Round 4 compared a count against a counter incremented inside the pushing function: one
    // event counted twice. Round 5 replaced it with two independently derived COUNTS. Round 6
    // added set identity and an intra-run order rule on the finished body. All three were
    // defeated, and the seventh review named the shape they share: the ORACLE compares
    // `mk b{fine}.{assigns_seen}:{live|dead} s{alpha}:{ty}`, and the block index and the position
    // within the block were derived by NEITHER SIDE. Seven one-line relocations followed — a
    // `StorageLive` moved past its own initialising assign (362 bodies, and 21 in shipped
    // `clean-kernel`), a retirement moved before the assign that consumes it (133), the aggregate
    // seam (155), the result temp (69), and two evasions of round 6's order rule (316 / 115) —
    // and `UNSUPPORTED` stayed at its control value on every one of them. The gate compared
    // PROJECTIONS of the marker sequence while the oracle compared the SEQUENCE.
    //
    // So both sides now produce the SEQUENCE, and they still come from different places:
    //
    //   * `mf_gate::observe` walks the FINISHED MIR and renders every marker as (block, assigns
    //     seen in that block, live/dead, slot alpha-renamed by first appearance, the assignment
    //     operand position the slot is moved out at). It reads no plan, no counter and no lowering
    //     decision, and it refuses any statement that is neither an assignment nor a marker.
    //   * `MfPlans::predict` re-derives the same sequence from the SEALED PLANS, the trust-ir and
    //     the re-derived aggregate recognition: which instruction mints which temp, in what order,
    //     how many assignments each admitted instruction emits, which operand position each temp
    //     occupies, and where lane K defers a retirement onto an arm or a join. It reads no emitted
    //     statement.
    //
    // An extra emission, a missing one, a marker moved by ONE statement, a mint order reversed, a
    // retirement order reversed, two slots traded, a marker in a block the plans do not reach —
    // each moves one side and not the other, and the body fails CLOSED. `agg_chains` is re-derived
    // inside `predict` rather than handed over, so the seventh review's last piece of literal
    // shared state has one reader each. The plans themselves are sealed against THIS body:
    // `MfPlans::seal` checks at RUNTIME that `def` names the body the trust-ir function describes,
    // which is the one thing a `let def = ...typeck_root_def_id...` shadow cannot move.
    //
    // The sequence subsumes what rounds 5 and 6 checked separately — a local marked live twice,
    // retired twice in one block, retired without a live, marked and never retired, and a
    // retirement run out of reverse-operand order are all sequences the predicted side does not
    // produce — so those layers are DELETED rather than kept as inert restatements.
    // =====================================================================================
    // THE SCOPE OF THIS LAW — WHAT IT PROVES AND WHAT IT CANNOT. READ IT BEFORE QUOTING IT.
    // =====================================================================================
    // Every round of this gate before round 8 was reviewed and defeated, and what those rounds
    // shared is a check that READS STRONGER THAN IT IS. So the boundary is written here, at the
    // check, and every clause of it is a measurement: 1,570 probe bodies at both optimisation
    // levels, one hunk per attack, each on its own sealed driver. Nothing below is an intention.
    //
    // -----------------------------------------------------------------------------------
    // WHAT IT PROVES: THE EMITTER DID NOT RELOCATE A MARKER AWAY FROM THE PLAN.
    // -----------------------------------------------------------------------------------
    // For every body it admits, the storage-marker sequence in the FINISHED MIR is EQUAL, event
    // for event, to the sequence the sealed plans predict. An event is (MIR block, assignments
    // already seen in that block, live/dead, slot alpha-renamed by first appearance, the slot's
    // DECLARED TYPE, the operand position the slot is moved out at) — the oracle's own marker
    // line, component for component, plus round 6's retirement order. So any change on the
    // EMITTER's side that alters one component of one event — a marker moved by a single
    // statement, an extra marker, a missing marker, a mint or retirement order reversed, two
    // slots traded, a marker in a block the plans do not reach, or a temp declared at the wrong
    // type — moves the OBSERVED side and not the PREDICTED one, and the body fails CLOSED: it
    // ships marker-free and falls back to built MIR.
    //
    // Thirteen one-hunk attacks measured against THIS law, admitted-and-wrong 0 on every one of
    // them at both optimisation levels: `alive`, `aretire`, `aretire2`, `aresult`, `aaggpre`,
    // `aorder`, `anoporder`, `aggrev`, `aswap2`, `aggcopy`, `aroot`, `ashadow`, `ptype`. Two of
    // them with the law's own refusal line, so a reader can re-run exactly these bodies:
    //
    //   `alive`  the operand temp's `StorageLive` lands after its own initialising assign.
    //            429 bodies RIGHT -> UNSUPPORTED. `mf_operand_temps::AllocationId::is_null`:
    //            predicted `mk b0.0:live s0:U64@b0.1:0` vs derived `mk b0.1:live s0:U64@b0.1:0`.
    //   `ptype`  the operand temp minted at the same-width OPPOSITE SIGNEDNESS.
    //            399 bodies RIGHT -> UNSUPPORTED. `mfr8_num::n08_u32_widen_cast`:
    //            predicted `mk b0.0:live s0:U32@b0.1:0` vs derived `mk b0.0:live s0:I32@b0.1:0`.
    //            Against round 7 — which carried every component of that line EXCEPT the type —
    //            this same hunk was silent on 261 probe bodies and on NINE shipped `clean-kernel`
    //            bodies. That is what [`mf_gate::MfTy`] closes; [`mf_gate::MfTy::Opaque`] states
    //            the one thing the type component still does not discriminate.
    //
    // -----------------------------------------------------------------------------------
    // WHAT IT DOES NOT PROVE: THAT THE PLAN IS BUILT'S.
    // -----------------------------------------------------------------------------------
    // `MfPlans.operand` and `MfPlans.branch` are read by the EMITTER (`mf_mark_result`,
    // `mf_operand_class`, `branch_at`) AND by `MfPlans::predict` (`self.operand`, `self.branch`).
    // WIDEN A PLAN AND BOTH SIDES MOVE TOGETHER: this comparison stays green while the derived
    // body's marker sequence stops being built's. Measured against THIS law, one deleted rule
    // each, every listed body carrying verdict `agreed` with the law green:
    //
    //   delete `plan_operand_marker_temps` ordering rule (1) — 34 admitted-and-wrong. The rule's
    //     own comment names three of them and all three come back: `mf_aggregate_adversarial::
    //     {nested_field, two_instr_nested, mk_cast_load}`. `mfr5_pair::h06_left_spine_4` is the
    //     sharpest: `built mk b0.0:live s2:u32` vs `derived mk b0.1:live s2:u32` — A MARKER MOVED
    //     BY EXACTLY ONE STATEMENT, which is the thing the section above says cannot happen. It
    //     cannot happen when an ARM moves the marker. It happens when the PLAN moves.
    //   delete `plan_operand_marker_temps` ordering rule (2) — 28, including the four its comment
    //     names (`mf_residual::{a1_right_nested, a3_field_right_nested, a12_place_then_and,
    //     a6_place_then_load}`) and `mf_operand_temps::right_nested`.
    //   delete `plan_branch_markers`' join-parameter rule — 3, exactly the three its comment
    //     names: `mb_joinhead::{join_is_head, chain_of_ifs, double_nested_cond}`, whose first
    //     divergence is `built mk b0.0:live s2:bool` vs `derived mk b2.0:dead s1:u32` — the BLOCK
    //     INDEX moved by two and this law did not fire.
    //
    // All three cost ZERO flips and move ZERO whole-crate rows, and the TYPE component catches
    // none of them. That is not an oversight: under a widened plan both sides re-type the same
    // slots from their own sources and agree.
    //
    // AND IT IS NOT A GAP AN EXTRA LAYER IN THIS FILE CLOSES. The plan is what the shim EMITS
    // from, so anything inside this shim that predicts a marker sequence must PREDICT from it; a
    // second in-shim derivation of the same plan is a second reader of one decision, not an
    // independent witness of it. THE ONLY CHECK INDEPENDENT OF THE PLAN IS THE DIFFERENTIAL
    // ORACLE — `mir_differential::canon_markers` / `DerivedReport::markers_exact` — which
    // compares this body's marker sequence against rustc's OWN `mir_built` body and reads no
    // plan, no trust-ir and no line of this file. Every admitted-and-wrong count above IS the
    // oracle speaking: it is the oracle that says those 34, 28 and 3 sequences are not built's.
    //
    // -----------------------------------------------------------------------------------
    // SO THE DIVISION OF LABOUR, EXACTLY.
    // -----------------------------------------------------------------------------------
    //   * THE ORACLE decides whether the sequence is BUILT'S, and where markers are material it
    //     is a HARD GATE: `flip_registry::record_green` refuses the flip when
    //     `sess.emit_lifetime_markers()` and `!markers_exact`. A wrong PLAN therefore costs a
    //     flip at `-O`; it cannot ship a wrong sequence there.
    //   * THIS LAW decides whether the EMITTER obeyed the plan the oracle validated — and that is
    //     the half the oracle does not gate at `-O0`, where `emit_lifetime_markers()` is false,
    //     `markers_exact` is not required, and `RemoveStorageMarkers` deletes the markers before
    //     codegen. The seventh review measured exactly that hole on shipped code: 21 flipped
    //     `clean-kernel` bodies carrying a marker sequence that was not built's, with every layer
    //     of round 6 green.
    // Neither replaces the other. Do not quote either as if it did.
    let sealed = MfPlans::seal(tcx, def, func);
    let observed_markers = match mf_gate::observe(tcx, &cx.blocks, &cx.local_decls) {
        Ok(seen) => seen,
        Err(why) => return unsup(format!("marker law: {why}")),
    };
    match sealed.predict(func, ret_rty) {
        Ok(expected_markers) => {
            if observed_markers != expected_markers {
                return unsup(format!(
                    "marker law: the derived body's marker sequence is not the one the sealed \
                     plans predict — {}",
                    expected_markers.first_diff(&observed_markers)
                ));
            }
        }
        // A body whose plans engage but whose statement shape is outside the sequence model. A
        // marker-FREE derived body is still sound — the oracle reads `derived <end>`, refuses
        // `markers_exact`, and the body falls back to built MIR — so it ships; a marker this side
        // cannot PLACE is refused here rather than admitted on a weaker law, because a fallback is
        // the vacuity round 6's order rule was defeated through.
        Err(why) if !observed_markers.is_empty() => {
            return unsup(format!(
                "marker law: the derived body holds {} storage marker(s) the predicted side \
                 cannot place — {why}",
                observed_markers.len()
            ));
        }
        Err(_) => {}
    }

    // Stamp the authenticated source-loop identity on the reconstructed
    // natural header endpoint. `trust_mir_extract` independently redetects
    // dominator-proved backedges before consuming this identity.
    for (header, scope) in provenance_scopes {
        let bb = *cx
            .block_map
            .get(&header)
            .ok_or_else(|| Unsupported { reason: "source provenance header disappeared".into() })?;
        cx.blocks[bb]
            .terminator
            .as_mut()
            .ok_or_else(|| Unsupported {
                reason: "source provenance header is unterminated".into(),
            })?
            .source_info
            .scope = scope;
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

    // Trust (C2-names + E4/E5 source identity, consumption): mint
    // `var_debug_info` from authenticated loop bindings first, then from the
    // Module's entry-parameter `value_names` where they do not conflict.
    //
    // Producer names remain deliberately PARAMS ONLY, and that is a soundness
    // choice, not laziness: entry
    // param i is `ValueId(i)` at the producer and `Local(i + 1)` here (the `Body::new` ordering
    // invariant asserted just below — `_0` return place, then one local per arg), so the mapping
    // is exact by construction with nothing to desync. A non-param `ValueId` has no such
    // identity: `cx.env` maps it to a `VOp` that may be a temp, a constant, or a projection, and
    // guessing a local for it would attach a user-visible NAME to the wrong storage — a debugger
    // lying is worse than a debugger silent. Locals land when the ledger carries the binding's
    // own denotation, not before. The exception is no longer producer metadata:
    // a loop binding arrives through the fresh compiler digest + semantic body
    // digest + canonical `LoopParameter(i)` carrier, and its place was allocated
    // or reused above from that exact HIR identity. This is the denotation the
    // old comment required before locals could be named.
    //
    // `argument_index` is 1-based per the field's contract. Names beyond `arg_count` (a producer
    // that starts stamping locals before this consumer learns to place them) are SKIPPED, not
    // approximated.
    let mut var_debug_info: Vec<VarDebugInfo<'tcx>> = Vec::new();
    let mut authenticated_debug_places = HashMap::<Local, String>::new();
    for (hir_local_id, name) in &source_binding_names {
        let place =
            source_binding_places.get(hir_local_id).copied().ok_or_else(|| Unsupported {
                reason: "authenticated source binding has no reconstructed MIR place".into(),
            })?;
        if let Some(previous) = authenticated_debug_places.insert(place.local, name.clone()) {
            if previous != *name {
                return unsup("one reconstructed MIR place has multiple source names");
            }
        }
        let index = place.local.as_usize();
        var_debug_info.push(VarDebugInfo {
            name: rustc_span::Symbol::intern(name),
            source_info: cx.local_decls[place.local].source_info,
            composite: None,
            value: VarDebugInfoContents::Place(place),
            argument_index: (index > 0 && index <= param_rtys.len())
                .then(|| u16::try_from(index).ok())
                .flatten(),
        });
    }
    for (v, name) in func.value_names.iter().flatten() {
        let idx = v.index() as usize;
        if idx >= param_rtys.len() {
            continue;
        }
        let local = Local::from_usize(idx + 1);
        if let Some(authenticated_name) = authenticated_debug_places.get(&local) {
            // Same real place: the compiler-authenticated spelling wins. A
            // divergent producer spelling is ignored, never granted authority.
            let _ = authenticated_name;
            continue;
        }
        if source_name_bindings.contains_key(name) {
            return unsup("producer parameter name collides with a different source binding");
        }
        var_debug_info.push(VarDebugInfo {
            name: rustc_span::Symbol::intern(name),
            source_info: cx.local_decls[local].source_info,
            composite: None,
            value: VarDebugInfoContents::Place(Place::from(local)),
            argument_index: u16::try_from(idx + 1).ok(),
        });
    }

    Ok(MirLowering {
        // Clone the tiny per-body translation map before moving the lowering
        // context's block/local tables into `Body::new`.  Consumers use only
        // `BlockId` lookup followed by canonical CFG-role reconstruction;
        // neither map iteration nor raw block numbering carries authority.
        ir_block_map: cx.block_map.clone(),
        body: Body::new(
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
        ),
    })
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

/// Built's canonical ordering key for ONE case value of an ENUM-discriminant `SwitchInt`.
///
/// Built's case order is **variant-index order**, and that is read off one line of rustc:
/// `TestKind::Switch` (`rustc_mir_build/src/builder/matches/test.rs`) builds its targets from
/// `adt_def.discriminants(tcx).filter_map(..)`, which yields variants in `VariantIdx` order, and
/// `SwitchTargets::new` (`rustc_middle/src/mir/terminator.rs`) unzips that iterator verbatim with
/// no sort of its own. Built never orders by discriminant VALUE — the two orders merely coincide
/// on every enum whose discriminants ascend with the variant index, which is every enum the
/// original wave-YM sort was measured on.
///
/// A value that is not a discriminant of the ADT cannot appear in a built `TestKind::Switch` at
/// all, so a derived body carrying one is refused whatever the order; it is ordered after every
/// real tag, by value, which is where the ascending sort also left the `enum-case-value` SAT
/// control's deliberately out-of-domain tag.
fn enum_switch_case_order_key(
    disc_to_vidx: &HashMap<u128, rustc_abi::VariantIdx>,
    value: u128,
) -> (u8, u128) {
    disc_to_vidx.get(&value).map_or((1u8, value), |vidx| (0u8, u128::from(vidx.as_u32())))
}

#[cfg(test)]
mod enum_switch_case_order_tests {
    use std::collections::HashMap;

    use rustc_abi::VariantIdx;

    use super::enum_switch_case_order_key;

    /// `(disc, variant index)` pairs as `adt.discriminants(tcx)` would yield them, into the map
    /// the lowering builds, plus the sort the lowering applies. The test states the ORDER, which
    /// is the whole claim — the key itself is an implementation detail of stating it.
    fn ordered(discs: &[u128], cases: &[u128]) -> Vec<u128> {
        let map: HashMap<u128, VariantIdx> =
            discs.iter().enumerate().map(|(i, d)| (*d, VariantIdx::from_usize(i))).collect();
        let mut v = cases.to_vec();
        v.sort_by_key(|c| enum_switch_case_order_key(&map, *c));
        v
    }

    /// THE REGRESSION. `#[repr(u32)] enum { Hi = 900, Lo(u32) = 1 }` — built emits `[900, 1]`
    /// because 900 is variant 0; the retired ascending sort emitted `[1, 900]` and the comparator
    /// recorded `derived_mir: mismatch` on `ep_review_corpus_c::Ordered::v` for exactly that.
    #[test]
    fn test_case_order_descending_discriminants_follows_variant_index() {
        assert_eq!(ordered(&[900, 1], &[1, 900]), vec![900, 1]);
        assert_eq!(ordered(&[900, 1], &[900, 1]), vec![900, 1]);
    }

    /// AND THE PROPERTY THAT MAKES IT A GENERALIZATION, NOT A TRADE: on every enum whose
    /// discriminants ascend with the variant index — Option/Result/`Dir`/`E`, i.e. the entire
    /// population wave-YM was measured on — variant-index order IS ascending order, whatever the
    /// arm order the producer hands over. wave-YM's `opt_match` (`Some` before `None`) is the
    /// first row.
    #[test]
    fn test_case_order_ascending_discriminants_matches_the_retired_value_sort() {
        assert_eq!(ordered(&[0, 1], &[1, 0]), vec![0, 1]);
        assert_eq!(ordered(&[0, 1, 2, 3], &[3, 1, 0, 2]), vec![0, 1, 2, 3]);
        assert_eq!(ordered(&[10, 11, 12], &[12, 10, 11]), vec![10, 11, 12]);
    }

    /// Interleaved discriminants are neither ascending nor descending; the key must still follow
    /// the DECLARATION order, which is what built iterates.
    #[test]
    fn test_case_order_interleaved_discriminants_follow_declaration_order() {
        assert_eq!(ordered(&[6, 1, 5, 2, 4, 3], &[1, 2, 3, 4, 5, 6]), vec![6, 1, 5, 2, 4, 3]);
        // `#[repr(u32)] enum { A = 10, B, C = 1, D }` — implicit discriminants resume counting.
        assert_eq!(ordered(&[10, 11, 1, 2], &[1, 2, 10, 11]), vec![10, 11, 1, 2]);
    }

    /// A value that is not a discriminant of the ADT — only the `enum-case-value` SAT control
    /// mints one — sorts AFTER every real tag, by value, exactly where the ascending sort left it.
    /// It must not be able to displace a real tag, because a displaced tag would change the
    /// canonical block order of an otherwise-correct body.
    #[test]
    fn test_case_order_out_of_domain_value_sorts_last() {
        assert_eq!(ordered(&[900, 1], &[1, 901, 900]), vec![900, 1, 901]);
        assert_eq!(ordered(&[900, 1], &[u128::MAX, 2, 900, 1]), vec![900, 1, 2, u128::MAX]);
    }

    /// A one-case switch (the wildcard-tail shape) and a zero-case switch have no order to get
    /// wrong; the sort must be a no-op rather than, say, panicking on an empty slice.
    #[test]
    fn test_case_order_degenerate_case_counts_are_no_ops() {
        assert_eq!(ordered(&[900, 1], &[900]), vec![900]);
        assert_eq!(ordered(&[900, 1], &[1]), vec![1]);
        assert!(ordered(&[900, 1], &[]).is_empty());
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
        } if is_int(src_ty) && is_int(dst_ty) => {
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
        let (p, agg, new, v) = (ValueId::new(0), ValueId::new(1), ValueId::new(2), ValueId::new(3));
        let fwd: HashMap<ValueId, Place<'static>> =
            HashMap::from([(p, Place::from(Local::from_u32(1)))]);
        let nodes = vec![
            InstrNode::new(Inst::Load {
                ty: load_ty.clone(),
                ptr: p,
                volatile: false,
                align: None,
            })
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
    use trust_ir::ScopeData;

    use super::scope_topology_error;

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
        assert!(scope_topology_error(&[sc(None), sc(None)]).is_some(), "second root");
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
        let lane =
            producer.find(&format!("fn {}<'tcx>(", "param_rty")).expect("`param_rty` must exist");
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

/// Trust (lane MF-ZERO-3, 2026-08-13; **re-scoped again by lane MF-R5, 2026-08-14**):
/// **THE MARKER-GATE BACKSTOP, AND ITS MUTATION PROOF.**
///
/// WHAT THIS MODULE IS, AND WHAT IT IS NOT. Round 3 offered this scanner as one of three layers
/// enforcing "no marker is emitted without a plan". The fourth review defeated it in one line, and
/// the fifth review defeated its successor in three: a scanner is SPELLING-BOUND by construction —
/// a macro, a `paste!`, an `include!` or a crate it cannot see will always be able to spell
/// something it does not match. **This module does not claim to be the invariant.** The layers, in
/// the order they actually bind:
///
/// * **PRIVACY AND THE ONE CONSTRUCTOR are what enforce the plan.** [`super::mf_gate::MfPlans`]
///   has private fields and exactly one constructor, which is a pure function of the body; the
///   five emission methods each consult it and are the only path to a marker in a block. The two
///   attacks that walked through round 4 (`cx.mf_borrow = true`; dropping the per-value conjunct)
///   are compile errors here, not findings.
/// * **THE LAW is what enforces the emission.** `lower_ir_to_mir` closes every body by comparing
///   two independently derived numbers: the markers `mf_gate::observe` finds in the FINISHED body
///   against the markers `MfPlans::predict` derives from the SEALED PLANS. Round 4's version
///   compared the body against a counter incremented inside the pusher — one event, twice — and
///   the fifth review measured it moving zero of 1,160 bodies. `marker_law_tests` pins both sides.
/// * **THIS module is the backstop.** It reddens early, in the developer's own `cargo test`, with
///   a message that says what the invariant is, and it keeps the one property a scanner CAN
///   decide: the two marker identifiers are spelled inside the gate and nowhere else, in this file
///   and in every file of the crate.
///
/// Every needle below is assembled at run time. This module's own source is inside
/// `include_str!("to_mir.rs")`, so a literal needle would match itself and the guard would pass
/// with the gate deleted — the same trap `emission_chokepoint_tests` documents.
#[cfg(test)]
mod marker_gate_invariant_tests {
    use std::collections::BTreeSet;
    use std::path::{Path, PathBuf};

    /// The two identifiers that ARE a storage marker, assembled so this file's own source does not
    /// contain them.
    fn marker_idents() -> [String; 2] {
        [format!("Storage{}", "Live"), format!("Storage{}", "Dead")]
    }

    /// The sentinel lines that delimit the sanctioned region. Matched with their `\n// ` prefix so
    /// the prose that discusses them in `///` doc comments cannot be mistaken for the real thing.
    fn sentinels() -> [String; 2] {
        [format!("\n// {}-GATE-BEGIN", "MARKER"), format!("\n// {}-GATE-END", "MARKER")]
    }

    fn is_ident_byte(b: u8) -> bool {
        b.is_ascii_alphanumeric() || b == b'_'
    }

    /// Overwrite `[from, to)` with spaces, keeping newlines so line numbers survive.
    fn blank(out: &mut [u8], from: usize, to: usize) {
        for b in &mut out[from..to] {
            if *b != b'\n' {
                *b = b' ';
            }
        }
    }

    /// A raw-string opener at `i`: `r`, then zero or more `#`, then `"`. Rust requires a
    /// non-identifier byte before the `r`, which is what keeps `"CondBr"` — an identifier-final `r`
    /// immediately followed by a quote INSIDE a string — from being read as one. Returns the
    /// number of hashes.
    fn raw_open(b: &[u8], i: usize) -> Option<usize> {
        if b[i] != b'r' {
            return None;
        }
        if i > 0 && is_ident_byte(b[i - 1]) {
            return None;
        }
        let mut j = i + 1;
        while j < b.len() && b[j] == b'#' {
            j += 1;
        }
        (j < b.len() && b[j] == b'"').then_some(j - i - 1)
    }

    /// Every comment, string literal, byte string, raw string and character literal replaced by
    /// spaces, byte offsets preserved. What survives is CODE.
    fn mask(src: &str) -> Vec<u8> {
        let b = src.as_bytes();
        let mut out = b.to_vec();
        let mut i = 0usize;
        while i < b.len() {
            if b[i] == b'/' && i + 1 < b.len() && b[i + 1] == b'/' {
                let start = i;
                while i < b.len() && b[i] != b'\n' {
                    i += 1;
                }
                blank(&mut out, start, i);
                continue;
            }
            if b[i] == b'/' && i + 1 < b.len() && b[i + 1] == b'*' {
                let start = i;
                let mut depth = 1usize;
                i += 2;
                while i < b.len() && depth > 0 {
                    if b[i] == b'/' && i + 1 < b.len() && b[i + 1] == b'*' {
                        depth += 1;
                        i += 2;
                    } else if b[i] == b'*' && i + 1 < b.len() && b[i + 1] == b'/' {
                        depth -= 1;
                        i += 2;
                    } else {
                        i += 1;
                    }
                }
                blank(&mut out, start, i);
                continue;
            }
            if let Some(hashes) = raw_open(b, i) {
                let start = i;
                i += 1 + hashes + 1;
                loop {
                    if i >= b.len() {
                        break;
                    }
                    if b[i] == b'"' && b[i + 1..].iter().take(hashes).all(|c| *c == b'#') {
                        i += 1 + hashes;
                        break;
                    }
                    i += 1;
                }
                blank(&mut out, start, i);
                continue;
            }
            if b[i] == b'"' {
                let start = i;
                i += 1;
                while i < b.len() {
                    if b[i] == b'\\' {
                        i += 2;
                        continue;
                    }
                    if b[i] == b'"' {
                        i += 1;
                        break;
                    }
                    i += 1;
                }
                blank(&mut out, start, i);
                continue;
            }
            if b[i] == b'\'' {
                // A CHARACTER literal, or a LIFETIME. `'\n'` and `'x'` are literals; `'tcx` is not.
                let escaped = i + 1 < b.len() && b[i + 1] == b'\\';
                let simple = i + 2 < b.len() && b[i + 2] == b'\'';
                if escaped || simple {
                    let start = i;
                    i += if escaped { 2 } else { 2 };
                    while i < b.len() && b[i] != b'\'' {
                        i += 1;
                    }
                    i = (i + 1).min(b.len());
                    blank(&mut out, start, i);
                } else {
                    i += 1;
                }
                continue;
            }
            i += 1;
        }
        out
    }

    /// Byte offsets of every WHOLE-WORD occurrence of `needle` in `code`.
    fn word_sites(code: &[u8], needle: &str) -> Vec<usize> {
        let n = needle.as_bytes();
        let mut out = Vec::new();
        if n.is_empty() || code.len() < n.len() {
            return out;
        }
        for at in 0..=code.len() - n.len() {
            if &code[at..at + n.len()] != n {
                continue;
            }
            let before_ok = at == 0 || !is_ident_byte(code[at - 1]);
            let after = at + n.len();
            let after_ok = after == code.len() || !is_ident_byte(code[after]);
            if before_ok && after_ok {
                out.push(at);
            }
        }
        out
    }

    fn line_of(src: &str, at: usize) -> usize {
        src.as_bytes()[..at].iter().filter(|b| **b == b'\n').count() + 1
    }

    /// Locate `[begin, end)` for a sentinel pair, or the reason it could not be located.
    fn region(src: &str, pat: &[String; 2], what: &str) -> Result<(usize, usize), String> {
        let begin =
            src.find(&pat[0]).ok_or_else(|| format!("the {what} opening sentinel is missing"))?;
        let end =
            src.find(&pat[1]).ok_or_else(|| format!("the {what} closing sentinel is missing"))?;
        if src[begin + 1..].matches(&pat[0][1..]).count() != 1
            || src[end + 1..].matches(&pat[1][1..]).count() != 1
        {
            return Err(format!("the {what} sentinels are not unique"));
        }
        if begin >= end {
            return Err(format!("the {what} sentinels are inverted"));
        }
        Ok((begin, end))
    }

    /// EVERY violation of the marker gate visible in one file's source: a marker identifier
    /// mentioned in CODE outside the sanctioned region. Empty means the file is clean by the one
    /// predicate a scanner can decide.
    ///
    /// Trust (lane MF-R5): the LEASE half of this scan is gone because the lease is gone. Round 4
    /// added it to catch `MarkerLease::issue`, a forgery that mattered because an arm could mint a
    /// token and then emit whatever it liked. Round 5 removes the token: the emission methods are
    /// the only things an arm can call, each asks its own plan, and an emission the plans did not
    /// predict fails the body closed at the law. There is nothing left to forge, so there is
    /// nothing left to grep for.
    fn violations(src: &str) -> Vec<String> {
        let (begin, end) = match region(src, &sentinels(), "MARKER-GATE") {
            Ok(v) => v,
            Err(e) => return vec![e],
        };
        let code = mask(src);
        let mut out = Vec::new();
        for ident in marker_idents() {
            for at in word_sites(&code, &ident) {
                if at < begin || at > end {
                    out.push(format!("{ident} at line {}", line_of(src, at)));
                }
            }
        }
        out
    }

    /// THE INVARIANT, as far as a scanner can see it. A storage marker is constructed inside
    /// [`super::mf_gate`] and nowhere else in this shim, and a `MarkerLease` — the token that
    /// proves a plan said yes — is minted inside `mf_gate::mint` and nowhere else.
    #[test]
    fn no_marker_is_constructed_outside_the_gate() {
        let found = violations(include_str!("to_mir.rs"));
        assert!(
            found.is_empty(),
            "the marker gate is bypassed: {found:?}\n\
             A marker emitted without a plan's permission is the defect five independent reviews \
             of this shim have now found (12, then 17, then 43, then 46/183/311 \
             admitted-and-wrong bodies). Emit through one of `mf_gate`'s plan-consulting methods, \
             and if your site needs a new one, teach `MfPlans::predict` to count it — the body-end \
             law compares what the plans predict against what the finished body holds."
        );
    }

    /// THE MUTATION PROOF FOR THE MARKER HALF: the scanner is RED on an ungated emission, and stays
    /// GREEN on a shim whose only mentions are inside the gate or inside prose. Without this, a
    /// scanner that had silently stopped matching would read exactly like a shim with no
    /// violations. (Round 3's proof, kept verbatim in substance — it was never the part that
    /// failed.)
    #[test]
    fn the_scanner_goes_red_on_an_ungated_emission() {
        let live = &marker_idents()[0];
        let [begin, end] = sentinels();
        // A miniature shim with the same shape as the real file: a gate region, prose that
        // discusses markers, and arms that do or do not cheat.
        let clean = format!(
            "//! a shim that mentions {live} only in prose\n\
             {begin} — the gate\nmod mf_gate {{\n    fn live(l: Local) -> S {{ S::{live}(l) }}\n}}\n\
             {end}\nfn arm(cx: &mut Cx) {{ cx.push_marker(bb, MarkerStmt::live(lease, t)); }}\n"
        );
        assert_eq!(violations(&clean), Vec::<String>::new(), "the clean shim must pass");

        let raw_push =
            format!("{clean}fn new_arm(cx: &mut Cx) {{ cx.push_stmt(bb, S::{live}(t)); }}\n");
        assert!(
            violations(&raw_push).iter().any(|v| v.starts_with(live.as_str())),
            "a raw push outside the gate must be reported"
        );

        let imported = format!("{clean}use rustc_middle::mir::StatementKind::{live};\n");
        assert!(
            !violations(&imported).is_empty(),
            "importing the variant to drop the path qualifier must be reported too"
        );

        let hidden = format!(
            "{clean}// a comment naming {live}\nfn s() -> &'static str {{ \"{live}\" }}\n\
             fn cheat(cx: &mut Cx) {{ cx.push_stmt(bb, S::{live}(t)); }}\n"
        );
        let hits = violations(&hidden);
        assert_eq!(
            hits.len(),
            1,
            "the comment and the string literal must be masked and the real push reported: {hits:?}"
        );
    }

    /// The masker is the scanner's only moving part; a bug in it would silently make the invariant
    /// vacuous. Pin the four constructs this file actually contains.
    #[test]
    fn the_masker_removes_comments_and_literals_and_nothing_else() {
        let needle = format!("Storage{}", "Live");
        let cases = [
            (format!("// {needle}\n"), 0usize),
            (format!("/// {needle}\n"), 0),
            (format!("/* {needle} */"), 0),
            (format!("let s = \"{needle}\";"), 0),
            (format!("let s = \"a\\\"{needle}\";"), 0),
            (format!("let s = r\"{needle}\";"), 0),
            (format!("let c = 'x'; let k = S::{needle}(l);"), 1),
            (format!("let s: &'tcx str = \"\"; let k = S::{needle}(l);"), 1),
            (format!("let s = \"CondBr\"; let k = S::{needle}(l);"), 1),
            (format!("let k = My{needle}(l);"), 0),
            (format!("let k = {needle}Thing(l);"), 0),
        ];
        for (src, want) in cases {
            let got = word_sites(&mask(&src), &needle).len();
            assert_eq!(got, want, "masking {src:?} gave {got} site(s), wanted {want}");
        }
    }

    /// The real file must contain the gate — a scanner that found no marker anywhere would also
    /// report zero violations, and that is not the same thing as the invariant holding.
    ///
    /// The counts are pinned, not merely bounded. Each marker identifier occurs exactly TWICE in
    /// code: in `mf_gate::marker_kind`, the one construction of a marker statement in the program,
    /// and in `mf_gate::observe`'s match, the finished-body walk that is the law's observed side.
    /// A third occurrence is a marker this shim can emit and the law's observer might not
    /// recognise, and it must come here to say so.
    #[test]
    fn the_gate_itself_is_present_and_is_where_the_markers_are() {
        let src = include_str!("to_mir.rs");
        let code = mask(src);
        let (begin, end) = region(src, &sentinels(), "MARKER-GATE").expect("the gate");

        // Each marker identifier occurs TWICE in code: `mf_gate::marker_kind`'s construction —
        // the one construction of a marker statement in the program — and `mf_gate::observe`'s
        // finished-body walk, which renders the derived body's canonical marker SEQUENCE for the
        // law. Round 6's `retirement_order` was a third reader of `StorageDead`; the sequence
        // subsumes its rule (the operand position each slot is moved out at is a component of
        // every event), and it is deleted rather than kept beside the law.
        let idents = marker_idents();
        for (ident, want) in [(&idents[0], 2usize), (&idents[1], 2usize)] {
            let sites = word_sites(&code, ident);
            assert_eq!(
                sites.len(),
                want,
                "{ident} must appear exactly {want} time(s) in code — `mf_gate::marker_kind`'s \
                 construction and `mf_gate::observe`'s finished-body walk — and both inside the \
                 gate; found {}",
                sites.len()
            );
            for at in sites {
                assert!(
                    at > begin && at < end,
                    "{ident} at line {} is outside the gate",
                    line_of(src, at)
                );
            }
        }
    }

    /// **THE WHOLE CRATE, NOT ONE FILE.** The fourth review's attack B put a marker factory in
    /// another module of this crate, where `violations(include_str!("to_mir.rs"))` cannot see it.
    /// The runtime conservation law is what defeats that attack; this is the backstop that says so
    /// early, by requiring the gate's vocabulary never to leave this file — no re-export, no
    /// helper module, no second `mf_gate`.
    ///
    /// The walk is asserted to be NON-VACUOUS (it must find `to_mir.rs` and several siblings),
    /// because a directory walk that silently found nothing would pass this test forever.
    #[test]
    fn the_gate_vocabulary_never_leaves_this_file() {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src");
        let mut files = Vec::new();
        collect_rs(&root, &mut files);
        files.sort();
        assert!(
            files.len() >= 8,
            "the crate-wide scan found only {} source file(s) under {} — a walk that finds \
             nothing passes vacuously",
            files.len(),
            root.display()
        );
        assert!(
            files.iter().any(|p| p.file_name().and_then(|s| s.to_str()) == Some("to_mir.rs")),
            "the crate-wide scan did not find `to_mir.rs`; it is scanning the wrong tree"
        );

        // Trust (lane MF-R5): the gate's OWN vocabulary, which is now two type names and the
        // module. The two marker identifiers are deliberately NOT here: `mir_differential.rs` is
        // the oracle and must name them to canonicalise built's marker sequence — the file-local
        // scan above is what keeps them out of the SHIM outside the gate.
        let gate_words =
            [format!("Mf{}", "Plans"), format!("Mf{}", "Seq"), format!("mf_{}", "gate")];
        let mut offenders = BTreeSet::new();
        for path in &files {
            if path.file_name().and_then(|s| s.to_str()) == Some("to_mir.rs") {
                continue;
            }
            let Ok(text) = std::fs::read_to_string(path) else { continue };
            let code = mask(&text);
            for w in &gate_words {
                if !word_sites(&code, w).is_empty() {
                    offenders.insert(format!("{} names `{w}`", path.display()));
                }
            }
        }
        assert!(
            offenders.is_empty(),
            "the marker gate's vocabulary escaped `to_mir.rs`: {offenders:?}\n\
             The gate types are private to the shim on purpose: a lease or a marker statement \
             that can be named elsewhere is a lease or a marker statement that can be built \
             elsewhere."
        );
    }

    fn collect_rs(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(entries) = std::fs::read_dir(dir) else { return };
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() {
                collect_rs(&p, out);
            } else if p.extension().and_then(|s| s.to_str()) == Some("rs") {
                out.push(p);
            }
        }
    }

    /// **THE LAW, AND THE PROOF THAT ITS TWO SIDES ARE NOT ONE SIDE.**
    ///
    /// Round 4's conservation law was `observed_markers != cx.mf_census.total()`, and
    /// `mf_census.total()` was incremented inside `push_marker` on the line before that same
    /// function pushed the statement. This pins what makes round 5's version a comparison rather
    /// than a tautology: exactly ONE statement-insertion path (so the observer sees every statement
    /// any arm can make), and a body-end test that names the OBSERVER and the PREDICTOR — two
    /// functions with no shared state, one reading the finished MIR and one reading the sealed
    /// plans. It also pins that the counter, the lease and the site enum are GONE rather than
    /// merely unused: an inert layer teaches the next reader that something is enforced.
    #[test]
    fn the_marker_law_compares_two_independent_derivations() {
        let src = include_str!("to_mir.rs");
        // Counted in CODE, not in raw text: this test's own doc comment and failure messages name
        // every needle below, and counting them would make each assertion pass for its own sake.
        let code = mask(src);
        let pushes = count_in_code(&code, &format!("statements.{}(", "push"));
        assert_eq!(
            pushes, 1,
            "found {pushes} `statements.push(` sites in the shim; exactly one is allowed (the \
             body of `push_stmt`). A second one is a statement path the law's observer still \
             sees — but nothing else does."
        );
        assert_eq!(
            count_in_code(
                &code,
                &format!("mf_gate::{}(tcx, &cx.blocks, &cx.local_decls)", "observe")
            ),
            1,
            "the law's OBSERVED side must be one walk of the finished body, exactly once"
        );
        assert_eq!(
            count_in_code(&code, &format!("sealed.{}(func, ret_rty)", "predict")),
            1,
            "the law's PREDICTED side must be one derivation from the sealed plans, exactly once"
        );
        // Round 8: what the two sides compare is the SEQUENCE, not a projection of it — and the
        // tuple below is the ORACLE'S OWN MARKER LINE, component for component (block, assigns
        // already seen, live/dead, alpha slot, declared type) plus round 6's retirement order as
        // the use site. Five rounds were defeated by moving something the law did not carry; the
        // last of them (`ptype`, 261 bodies) moved the declared type, which round 7 left out.
        assert_eq!(
            count_in_code(
                &code,
                &format!("type Mf{} = (usize, usize, bool, u32, MfTy, MfKey);", "Event")
            ),
            1,
            "the law's one currency must be the canonical marker tuple"
        );
        // **AND THE TYPE COMPONENT IS TWO DERIVATIONS, NOT ONE.** The predicted side spells a slot
        // type from the trust-ir and the observed side from the finished body's `local_decls`;
        // one token function each, one call site each. Route both through one of them and the
        // component is a tautology — which is the shape every defeated round shared.
        for (fname, callers) in [
            (format!("fn {}(ty: &Ty) -> MfTy", "ir_ty_token"), 5usize),
            (format!("fn {}<'tcx>(tcx: TyCtxt<'tcx>", "rustc_ty_token"), 1usize),
        ] {
            assert_eq!(
                count_in_code(&code, &fname),
                1,
                "`{fname}` must be defined exactly once — one spelling per side"
            );
            let _ = callers;
        }
        assert_eq!(
            count_in_code(&code, &format!("{}(tcx, d.ty)", "rustc_ty_token")),
            1,
            "the OBSERVED side's type must come from the finished body's local declaration, and \
             from nowhere else: the predicted side must never be able to read it"
        );
        let law = format!("observed_markers != {}_markers", "expected");
        assert_eq!(
            count_in_code(&code, &law),
            1,
            "the body-end comparison (`{law}`) must be present exactly once: it is the only check \
             in this shim whose two sides come from different derivations"
        );
        for ghost in [
            format!("Mf{}", "Census"),
            format!("Marker{}", "Lease"),
            format!("Mf{}", "Site"),
            format!("Mf{}", "Markers"),
            format!("{}_order", "retirement"),
        ] {
            assert_eq!(
                word_sites(&code, &ghost).len(),
                0,
                "`{ghost}` is back in the shim. Each was deleted because it was measured \
                 UNWITNESSED — round 5's census/lease/site enum on 1,160 bodies, round 6's count \
                 pair and retirement-order rule on 1,414 — and INERT under the attacks that \
                 worked; a layer that fires on neither honest nor dishonest code is measuring \
                 nothing."
            );
        }
    }

    /// **THE SIXTH REVIEW'S ATTACK A, PINNED — AND NOT WITH A RUNTIME LAYER.**
    ///
    /// Round 5 pinned the law's predicted side by its one good call site's EXACT STRING, and
    /// asserted that re-sealing is "a no-op BY CONSTRUCTION". `MfPlans::seal` is indeed pure, but
    /// purity constrains the value GIVEN the arguments and nothing constrained the arguments: one
    /// line in the `Inst::ICmp` arm — `cx.mf_plans = MfPlans::seal(tcx, root, func)`, in the
    /// `typeck_root_def_id(def.to_def_id()).as_local()` idiom this file already spells three times
    /// — installed a plan sealed against a DIFFERENT `LocalDefId` and put 3 admitted-and-wrong
    /// bodies back on the wire across 1,280, with every gate layer green and `449 passed`. The
    /// one count that moved was the one nothing pinned: `MfPlans::seal`, 7 -> 8.
    ///
    /// The repair is structural and is above, not here: the law's predicted side re-derives from
    /// this body's `(tcx, def, func)`, so a forged plan is an input to the EMITTER only — whose
    /// deviation from the plan is the whole reason the law exists. A runtime "is this plan sealed
    /// for `def`?" check would be a layer that NEVER FIRES once the repair is in (the attacked
    /// bodies already fail closed on the count), and this lane does not ship unwitnessed layers.
    ///
    /// So what is pinned here is the property the repair rests on, and it is pinned by TOTAL
    /// occurrence rather than by one blessed spelling: the plan value is never ASSIGNED, and EVERY
    /// seal in the file names this body.
    #[test]
    fn every_seal_names_this_body_and_the_plan_is_never_assigned() {
        let code = mask(include_str!("to_mir.rs"));
        let seal = format!("MfPlans::{}", "seal");
        let good = format!("MfPlans::{}(tcx, def, func)", "seal");
        let total = count_in_code(&code, &seal);
        let named = count_in_code(&code, &good);
        assert_eq!(
            total, 2,
            "found {total} `{seal}` sites in the shim; exactly two are allowed — the `ShimCx` \
             construction and the law's predicted side. A third is a plan sealed against arguments \
             no test reads, which is the sixth review's attack A."
        );
        assert_eq!(
            named, total,
            "`{seal}` occurs {total} times but only {named} of them are `{good}`: a seal against \
             any other identity hands this body another body's veto"
        );
        assert_eq!(
            count_in_code(&code, &format!("mf_plans: MfPlans::{}(tcx, def, func)", "seal")),
            1,
            "the `ShimCx` field must have exactly one construction"
        );
        for write in [format!("mf_{} =", "plans"), format!("mf_{}=", "plans")] {
            assert_eq!(
                count_in_code(&code, &write),
                0,
                "`{write}` is an assignment to the sealed plan value; there is no legal one"
            );
        }
        assert_eq!(
            count_in_code(&code, &format!("cx.mf_plans.{}", "predict")),
            0,
            "the law's predicted side must not read the field an arm can write"
        );
    }

    /// **THE AGGREGATE RECOGNITION IS NOT SHARED WRITABLE STATE, PINNED.** The sixth review's §3
    /// named `agg_chains` as the gate's second shared list: `predict` counts out of it and the
    /// `Return` arm routes out of it, so a reversal of the list moved both readers together.
    /// One measured admitted-and-wrong body across 1,280 before the binding became immutable.
    #[test]
    fn the_aggregate_recognition_is_derived_once_and_never_mutable() {
        let code = mask(include_str!("to_mir.rs"));
        assert_eq!(
            count_in_code(&code, &format!("let mut {}", "agg_chains")),
            0,
            "a writable aggregate recognition is a list `predict` and the `Return` arm both walk"
        );
        assert_eq!(
            count_in_code(&code, &format!("{}(func, ret_rty)", "agg_return_chains")),
            2,
            "the recognition must be derived from this body's trust-ir ONCE PER READER — the \
             `Return` arm's and the law's predicted side's. The seventh review measured 7 bodies \
             through the single-derivation-two-readers form (`aggcopy`) and 115 through `aswap2`; \
             a shared list is a list no term either side derives from it can see reversed."
        );
        for w in [format!("agg_chains.{}", "get_mut"), format!("agg_chains.{}", "insert")] {
            assert_eq!(
                count_in_code(&code, &w),
                0,
                "`{w}` reopens the shared writable list the sixth review named"
            );
        }
    }

    /// **THE SEQUENCE IS BUILT BY ONE RULE, PINNED.** The predicted and the observed side agree
    /// on what a marker's canonical position IS only because they share one builder — the assign
    /// counter, the alpha renaming and the use-site lookup are written once, in `MfSeqBuild`, and
    /// each side supplies only what it walks and how it spells a slot. Two copies of that rule
    /// would be two chances for the sides to drift into agreeing about the wrong thing, which is
    /// the failure mode of every round before this one.
    ///
    /// **THE PREDICTED SIDE IS THREE WALKS SINCE WAVE-CK, AND THAT NUMBER IS PINNED WITH THE
    /// EXCLUSIVITY THAT MAKES IT SAFE.** The property this test defends is "no further walk could
    /// QUIETLY DISAGREE with the others" — quietly, i.e. for ONE body. The payload class's walk,
    /// wave-CK's checked-chain walk and the general walk are selected by MUTUALLY EXCLUSIVE plans
    /// resolved in the one constructor (`MfPlans::seal`), `MfPlans::predict` dispatches on
    /// `self.payload` and then on `self.checked` before it reaches the general walk, and the
    /// general walk REFUSES at runtime if EITHER specialized plan is present. So for any given body
    /// exactly one of them runs and the others cannot contribute an event.
    ///
    /// **RAISING THE COUNT IS ONLY LEGITIMATE WITH THE CLAUSES BESIDE IT.** Each walk added here
    /// brings its own dispatch pin, its own single-caller pin and its own runtime refusal pin, all
    /// asserted below; the count on its own would be a loosening. Delete any one of those clauses
    /// and this test is red on that clause, not silently wider.
    #[test]
    fn the_two_sides_share_one_sequence_builder_and_nothing_else() {
        let code = mask(include_str!("to_mir.rs"));
        let build = format!("Mf{}", "SeqBuild");
        assert_eq!(
            count_in_code(&code, &format!("impl<S: Copy + PartialEq> {build}<S>")),
            1,
            "the canonical-position rule must have exactly one implementation"
        );
        // The OBSERVED side is one walk and always has been; the PREDICTED side is the general
        // walk plus wave-EP's payload walk plus wave-CK's checked-chain walk, and the clauses
        // below are what keep any two of them from ever deciding the same body.
        for (side, want) in [
            (format!("{build}<MfSlot> = {build}::new()"), 3usize),
            (format!("{build}<Local> = {build}::new()"), 1),
        ] {
            assert_eq!(
                count_in_code(&code, &side),
                want,
                "`{side}` must appear exactly {want} time(s) — one observed side, and predicted \
                 walks only for plan classes that cannot both hold; a walk beyond those is a third \
                 walk that could quietly disagree"
            );
        }
        // (1) exactly one dispatch, and it is keyed on the plan;
        assert_eq!(
            count_in_code(&code, &format!("if let Some(p) = &self.{} {{", "payload")),
            1,
            "the payload walk must be reached from exactly one plan-keyed dispatch"
        );
        assert_eq!(
            count_in_code(&code, &format!("{}(func, p)", "predict_payload")),
            1,
            "and that dispatch must be the only caller of the payload walk"
        );
        // ... and the same three clauses for wave-CK's checked-chain walk, so raising the count
        // above is a WIDENING (one more mutually exclusive class) and not a loosening.
        assert_eq!(
            count_in_code(&code, &format!("if let Some(p) = &self.{} {{", "checked")),
            1,
            "the checked-chain walk must be reached from exactly one plan-keyed dispatch"
        );
        assert_eq!(
            count_in_code(&code, &format!("{}(func, p)", "predict_checked")),
            1,
            "and that dispatch must be the only caller of the checked-chain walk"
        );
        // (2) the general walk refuses a payload body at RUNTIME, in every build;
        assert_eq!(
            count_in_code(&code, &format!("if self.{}.is_some() {{", "payload")),
            1,
            "the general walk must refuse a body the payload plan owns, fail-closed"
        );
        assert_eq!(
            count_in_code(&code, &format!("if self.{}.is_some() {{", "checked")),
            1,
            "the general walk must refuse a body the checked-chain plan owns, fail-closed"
        );
        // (3) and the payload plan is resolved against the others in the one constructor
        //     (`plan_exclusivity_tests` pins that conjunction; this is its counterpart here).
        assert_eq!(
            count_in_code(&code, &format!("fn {}(&mut self, live: bool, slot: S)", "mark")),
            1,
            "the alpha renaming (first appearance wins, as `canon_markers` does it) must be one \
             function both sides call"
        );
        // **AND ITS THREE LINES OF STATE, VERBATIM.** One shared builder is one place an edit can
        // blind BOTH sides at once — which is the seventh review's finding one level down, so it
        // does not get to be an argument. `MfSeqBuild`'s whole mutable state is three assignments
        // and one push; each is pinned by its exact text, and there is nothing to shadow (they are
        // field writes on a private three-field struct with exactly two instantiations, both
        // pinned above). Zeroing the position, dropping the block, or not counting an assignment
        // each changes one of these lines and turns this test red.
        for line in [
            format!("self.raw.push((self.blk, self.{}, live, slot));", "assigns"),
            format!("self.{} += 1;", "assigns"),
            format!("self.blk = blk;\n            self.{} = 0;", "assigns"),
        ] {
            assert_eq!(
                count_in_code(&code, &line),
                1,
                "`{line}` is the canonical-position rule itself; it must appear exactly once, \
                 verbatim"
            );
        }
        // The two components the sequence carries BEYOND the oracle's alpha slot and the event:
        // the position within the block, and the use site that stands in for the declared type.
        for line in [
            format!("let key = keys.iter().find(|(s, _)| *s == slot).and_{}(|(_, k)| *k);", "then"),
            format!("keys.{}((*s, Some((bi, at, oi))));", "push"),
        ] {
            assert_eq!(
                count_in_code(&code, &line),
                1,
                "`{line}` fixes where a slot is consumed; without it a RELABELLING — two slots \
                 trading places, `aswap2` — is alpha-identical and invisible"
            );
        }
        assert_eq!(
            count_in_code(&code, &format!("fn {}(rv: &Rvalue", "rvalue_operand_locals")),
            1,
            "the operand walk that fixes a slot's use site must exist exactly once"
        );
    }

    /// Occurrences of `needle` in masked CODE — comments and literals do not count.
    fn count_in_code(code: &[u8], needle: &str) -> usize {
        let n = needle.as_bytes();
        if n.is_empty() || code.len() < n.len() {
            return 0;
        }
        (0..=code.len() - n.len()).filter(|at| &code[*at..*at + n.len()] == n).count()
    }

    /// Attack B from the fourth review: a sibling file returns a raw marker `StatementKind` and
    /// an arm in this file pushes it, spelling no marker identifier here. Round 4 answered with an
    /// ordinary-boundary rejection AND a conservation law. Round 5 deletes the rejection — measured
    /// unwitnessed, and redundant — and lets the law answer: a pushed marker no plan predicted
    /// moves the observed side and not the predicted one, and the body fails closed.
    ///
    /// What is pinned here is the property the law rests on: ONE statement-insertion path, and it
    /// is gate-private, so the observer sees every statement that reaches a block.
    #[test]
    fn the_statement_boundary_is_single_and_gate_private() {
        let src = include_str!("to_mir.rs");
        let code = String::from_utf8(mask(src)).expect("masked Rust source remains UTF-8");
        let [begin_pat, end_pat] = sentinels();
        let begin = src.find(&begin_pat).expect("opening sentinel");
        let end = src.find(&end_pat).expect("closing sentinel");

        let raw_push = format!("{}.{}(Statement::new", "statements", "push");
        let raw_sites: Vec<_> = code.match_indices(&raw_push).map(|(at, _)| at).collect();
        assert_eq!(raw_sites.len(), 1, "there must be one raw statement insertion: {raw_sites:?}");
        assert!(raw_sites[0] > begin && raw_sites[0] < end, "raw insertion must be gate-private");
    }

    /// **THE MATCH-SCRUTINEE REFUSAL, PINNED BY NAME** (lane MF-R5). `k18_match_bool_of_cmp`
    /// (`match a == b { true => a, false => b }`) was the fifth review's ONE surviving
    /// admitted-and-wrong body, and it was wrong in every driver back to the pre-round-3 control:
    /// built retires a match scrutinee's operand temps in the HEAD block and an `if` condition's at
    /// the ENTRY OF BOTH ARMS, the two lower to byte-identical trust-ir, and lane K's deferral test
    /// is a trust-ir question. The distinction exists only in the SOURCE, so the refusal lives in
    /// the source-form gate's visitor — and a source-level clause can only be pinned by name, which
    /// is what `emission_chokepoint_tests::test_closure_env_param_is_refused_by_name` does for the
    /// closure-env arm.
    #[test]
    fn a_marker_minting_match_scrutinee_is_refused_by_name() {
        let src = include_str!("to_mir.rs");
        let code = mask(src);
        let clause = format!("rustc_hir::ExprKind::{}(scrutinee, _, _) = ex.kind", "Match");
        assert_eq!(
            count_in_code(&code, &clause),
            1,
            "the match-scrutinee clause must exist exactly once, by name"
        );
        let predicate = format!("!hir_tail_is_marker_{}(self.typeck, scrutinee)", "free");
        assert_eq!(
            count_in_code(&code, &predicate),
            1,
            "the clause must refuse exactly the scrutinees that MINT a marker — a bare-param \
             `match c {{ true => .. }}` mints none, is `markers_exact` today, and must stay \
             admitted"
        );
        let visitor = format!("fn visit_{}(&mut self, ex: &'tcx rustc_hir::Expr<'tcx>)", "expr");
        let at_visitor =
            code.windows(visitor.len()).position(|w| w == visitor.as_bytes()).expect("the visitor");
        let at_clause =
            code.windows(clause.len()).position(|w| w == clause.as_bytes()).expect("the clause");
        assert!(at_clause > at_visitor, "the clause must sit inside the source-form visitor");
    }
}

/// Trust (lane MF-R7, 2026-08-14): **THE LAW'S TWO SIDES, AS PURE FUNCTIONS.**
///
/// The observed side is a walk of finished MIR blocks; the predicted side is a walk of the trust-ir
/// under a sealed plan. Both are total functions of their input with no compiler state, so both can
/// be PINNED here instead of argued in a comment. What these tests are for:
///
///   * `predict` must reproduce **BUILT's** marker SEQUENCE for the shapes the plans admit — not
///     the emitter's, and not a summary of it. The three pinned here are read off the
///     `-Zdump-mir=built` dumps quoted verbatim in this file's own plan documentation: `min_if`,
///     `(a & b) == c` and `self.0 == 0`. A prediction checked against the EMITTER would be round
///     4's tautology again, one level up.
///   * the composition: on built's own body the two sides are EQUAL, and each of the seventh
///     review's relocations makes them differ — a `StorageLive` moved past its own initialising
///     assign, a retirement moved before the assign that consumes it, a forward retirement run and
///     a reversed mint order with the run repaired to hide it. Rounds 5 and 6 could see none of
///     the four.
///   * and the evasion round 6 died of: a statement the oracle deliberately ignores. `observe`
///     refuses it outright rather than skipping it.
#[cfg(test)]
mod marker_law_tests {
    use std::collections::{HashMap, HashSet};

    use rustc_abi::FieldIdx;
    use rustc_index::IndexVec;
    use rustc_middle::mir::{
        AggregateKind, BasicBlock, BasicBlockData, Local, Operand, Place, Rvalue, SourceInfo,
        Statement, StatementKind,
    };
    use rustc_span::DUMMY_SP;
    use trust_ir::{
        BinOp, BlockId, Constant, FuncId, FuncTyId, Function, ICmpOp, Inst, InstrNode, Ty, ValueId,
    };

    use super::mf_gate::{MfPlans, MfSeq, ir_ty_token, marker_kind, observe_with};
    use super::{MfBranchPlan, plan_branch_markers, plan_operand_marker_temps};

    fn v(i: u32) -> ValueId {
        ValueId::new(i)
    }
    fn b(i: u32) -> BlockId {
        BlockId::new(i)
    }
    fn node(inst: Inst, result: Option<u32>) -> InstrNode {
        let n = InstrNode::new(inst);
        match result {
            Some(r) => n.with_result(v(r)),
            None => n,
        }
    }
    fn konst(r: u32, k: i128) -> InstrNode {
        node(Inst::Const { ty: Ty::U32, value: Constant::Int(k) }, Some(r))
    }
    fn icmp(r: u32, lhs: u32, rhs: u32) -> InstrNode {
        node(Inst::ICmp { op: ICmpOp::Eq, ty: Ty::U32, lhs: v(lhs), rhs: v(rhs) }, Some(r))
    }
    fn ret(values: &[u32]) -> InstrNode {
        node(Inst::Return { values: values.iter().map(|a| v(*a)).collect() }, None)
    }

    /// One statement of a fixture body: an assignment naming its bare operand locals (which is what
    /// fixes a slot's use site, and what MOVES a marker's canonical position), a live, or a dead.
    #[derive(Clone, Copy)]
    enum St<'a> {
        A(&'a [u32]),
        L(u32),
        D(u32),
    }

    /// One MIR body, spelled statement by statement, block by block.
    ///
    /// Built with `new_stmts` rather than by pushing: `marker_gate_invariant_tests` pins that the
    /// shim contains exactly ONE `statements.push(Statement::new` site, and a fixture that is not a
    /// shim path must not look like a second one.
    fn body(blocks: &[&[St<'_>]]) -> IndexVec<BasicBlock, BasicBlockData<'static>> {
        let si = SourceInfo::outermost(DUMMY_SP);
        let mut out: IndexVec<BasicBlock, BasicBlockData<'static>> = IndexVec::new();
        for blk in blocks {
            let stmts: Vec<Statement<'static>> = blk
                .iter()
                .map(|st| {
                    let kind = match st {
                        // A value statement. WHAT it computes is irrelevant here; its operand
                        // sequence and its position are the whole content.
                        St::A(ops) => {
                            let fields: IndexVec<FieldIdx, Operand<'static>> = ops
                                .iter()
                                .map(|l| Operand::Move(Place::from(Local::from_u32(*l))))
                                .collect();
                            StatementKind::Assign(Box::new((
                                Place::from(Local::from_u32(0)),
                                Rvalue::Aggregate(Box::new(AggregateKind::Tuple), fields),
                            )))
                        }
                        St::L(l) => marker_kind(Local::from_u32(*l), true),
                        St::D(l) => marker_kind(Local::from_u32(*l), false),
                    };
                    Statement::new(si, kind)
                })
                .collect();
            out.push(BasicBlockData::new_stmts(stmts, None, false));
        }
        out
    }

    /// The observed side of a fixture body, with its locals' DECLARED TYPES — the component
    /// round 8 added, and the one the oracle prints as `s{alpha}:{ty}`. Only the exceptions are
    /// listed; every unlisted local is `u32`, which is what every operand and result temp in these
    /// fixtures is. A fixture that lists the wrong type is a fixture the law refuses, which is what
    /// `a_temp_declared_at_the_wrong_type_is_refused` measures.
    fn seen(blocks: &[&[St<'_>]], tys: &[(u32, Ty)]) -> MfSeq {
        observe_with(&body(blocks), |l| {
            let t = tys
                .iter()
                .find(|(k, _)| Local::from_u32(*k) == l)
                .map_or(Ty::U32, |(_, t)| t.clone());
            ir_ty_token(&t)
        })
        .expect("the fixture body is inside the marker channel's fragment")
    }

    /// The `min_if` shape, verbatim from the producer dump of `probes/mf_multiblock.rs`:
    /// `if a == 0 { b == 1 } else { b == 2 }`.
    fn min_if() -> Function {
        let mut f = Function::new(FuncId::new(0), "min_if", FuncTyId::new(0), b(0));
        let mut e = trust_ir::Block::new(b(0));
        e.params = vec![(v(0), Ty::U32), (v(1), Ty::U32)];
        e.body = vec![
            konst(3, 0),
            icmp(4, 0, 3),
            node(
                Inst::CondBr {
                    cond: v(4),
                    then_target: b(1),
                    then_args: vec![],
                    else_target: b(2),
                    else_args: vec![],
                },
                None,
            ),
        ];
        let mut t = trust_ir::Block::new(b(1));
        t.body = vec![
            konst(5, 1),
            icmp(6, 1, 5),
            node(Inst::Br { target: b(3), args: vec![v(6)] }, None),
        ];
        let mut el = trust_ir::Block::new(b(2));
        el.body = vec![
            konst(7, 2),
            icmp(8, 1, 7),
            node(Inst::Br { target: b(3), args: vec![v(8)] }, None),
        ];
        let mut j = trust_ir::Block::new(b(3));
        j.params = vec![(v(2), Ty::Bool)];
        j.body = vec![ret(&[2])];
        f.blocks = vec![e, t, el, j];
        f
    }

    /// `(a & b) == c` — wave-MF's single-block class, and the shape whose built MIR is quoted on
    /// [`super::ShimCx::mf_result_temp`].
    fn and_then_cmp() -> Function {
        let mut f = Function::new(FuncId::new(0), "and_then_cmp", FuncTyId::new(0), b(0));
        let mut e = trust_ir::Block::new(b(0));
        e.params = vec![(v(0), Ty::U32), (v(1), Ty::U32), (v(2), Ty::U32)];
        e.body = vec![
            node(Inst::BinOp { op: BinOp::And, ty: Ty::U32, lhs: v(0), rhs: v(1) }, Some(3)),
            icmp(4, 3, 2),
            ret(&[4]),
        ];
        f.blocks = vec![e];
        f
    }

    /// `self.0 == 0` — `AllocationId::is_null`, the body whose built MIR opens
    /// [`super::plan_operand_marker_temps`]'s documentation.
    fn field_eq_zero() -> Function {
        let mut f = Function::new(FuncId::new(0), "is_null", FuncTyId::new(0), b(0));
        let mut e = trust_ir::Block::new(b(0));
        e.params = vec![(v(0), Ty::U32)];
        e.body = vec![
            node(Inst::ExtractField { ty: Ty::U32, aggregate: v(0), field: 0 }, Some(1)),
            konst(2, 0),
            icmp(3, 1, 2),
            ret(&[3]),
        ];
        f.blocks = vec![e];
        f
    }

    fn predict_of(f: &Function, needs: HashSet<ValueId>, branch: Option<MfBranchPlan>) -> MfSeq {
        MfPlans::plans_for_test(Some(needs), branch)
            .predict_from(f, &HashSet::new(), &HashMap::new())
            .expect("the fixture is inside the sequence model")
    }

    fn and_then_cmp_predicted() -> MfSeq {
        let f = and_then_cmp();
        let needs =
            plan_operand_marker_temps(&f).expect("`(a & b) == c` is inside wave-MF's class");
        predict_of(&f, needs, None)
    }

    fn field_eq_zero_predicted() -> MfSeq {
        let f = field_eq_zero();
        let needs = plan_operand_marker_temps(&f).expect("`self.0 == 0` is inside wave-MF's class");
        predict_of(&f, needs, None)
    }

    #[test]
    fn the_predicted_sequence_is_builts_own_sequence_for_the_single_block_shapes() {
        // Built, verbatim: `StorageLive(_4); StorageLive(_5); _5 = copy _1; StorageLive(_6);
        // _6 = copy _2; _4 = BitAnd(move _5, move _6); StorageDead(_6); StorageDead(_5);
        // StorageLive(_7); _7 = copy _3; _0 = Eq(move _4, move _7); StorageDead(_7);
        // StorageDead(_4);` — the shim spells the comparison into a temp and copies it into `_0`,
        // one assignment later than built, which is AFTER every marker.
        assert_eq!(
            and_then_cmp_predicted(),
            seen(
                &[&[
                    St::L(4),
                    St::L(5),
                    St::A(&[1]),
                    St::L(6),
                    St::A(&[2]),
                    St::A(&[5, 6]),
                    St::D(6),
                    St::D(5),
                    St::L(7),
                    St::A(&[3]),
                    St::A(&[4, 7]),
                    St::D(7),
                    St::D(4),
                    St::A(&[8]),
                ]],
                &[],
            )
        );

        // Built: `StorageLive(_2); _2 = copy (_1.0: u64); _0 = Eq(move _2, const 0_u64);
        // StorageDead(_2);` — the returned comparison itself takes no temp, and the field read is
        // a PLACE (a projected operand), so it mints no statement and takes no operand position.
        assert_eq!(
            field_eq_zero_predicted(),
            seen(&[&[St::L(2), St::A(&[]), St::A(&[2]), St::D(2), St::A(&[3])]], &[])
        );
    }

    #[test]
    fn the_predicted_sequence_is_builts_own_sequence_for_the_multi_block_shape() {
        let f = min_if();
        let plan = plan_branch_markers(&f).expect("min_if is inside lane K's class");
        let got = predict_of(&f, plan.needs.clone(), Some(plan));
        // Built, verbatim (see `plan_branch_markers`' doc): `_3` (the condition's own temp) and
        // `_4` (its operand temp) live in the head; `_4` is retired at the ENTRY of both arms, at
        // position 0, where each arm then mints and retires its own operand temp; `_3` dies at the
        // join, also at position 0, and is consumed by the `switchInt` TERMINATOR, so it is the one
        // slot with no operand position at all. The empty `Goto` trampoline lane K inserts is
        // appended after every producer block, so it is bb4 and carries nothing.
        assert_eq!(
            got,
            seen(
                &[
                    &[St::L(3), St::L(4), St::A(&[1]), St::A(&[4])],
                    &[St::D(4), St::L(5), St::A(&[2]), St::A(&[5]), St::D(5), St::A(&[9])],
                    &[St::D(4), St::L(6), St::A(&[2]), St::A(&[6]), St::D(6), St::A(&[10])],
                    &[St::D(3), St::A(&[11])],
                    &[],
                ],
                // `_3` is the condition's own temp: `min_if`'s head `ICmp`, hence `bool`. The
                // operand temps `_4`/`_5`/`_6` copy `u32` parameters.
                &[(3, Ty::Bool)],
            )
        );
    }

    /// **THE SEVENTH REVIEW'S PRIMARY ATTACK, AS A SEQUENCE.** `alive` moves one line in
    /// `mf_operand` so the operand temp's `StorageLive` lands AFTER its own initialising assign.
    /// Every count is unchanged, both identity sets are unchanged, `retirement_order` read only
    /// deads — and 362 of 1,414 bodies shipped with a marker sequence that is not built's, plus 21
    /// in `clean-kernel`. It is one position, and the sequence is what carries a position.
    #[test]
    fn a_live_moved_past_its_own_assign_is_refused() {
        assert_ne!(
            field_eq_zero_predicted(),
            seen(&[&[St::A(&[]), St::L(2), St::A(&[2]), St::D(2), St::A(&[3])]], &[]),
            "the law must see a live moved past its own assign"
        );
    }

    /// `aretire` / `aaggpre`: the retirement run moved BEFORE the assignment that consumes the
    /// temps — 133 and 155 bodies. Round 6's rule constrained the run's INTERNAL order and never
    /// its position.
    #[test]
    fn a_retirement_moved_before_its_consuming_assign_is_refused() {
        assert_ne!(
            field_eq_zero_predicted(),
            seen(&[&[St::L(2), St::A(&[]), St::D(2), St::A(&[2]), St::A(&[3])]], &[]),
            "the law must see a retirement moved before its consuming assign"
        );
    }

    /// `aorder` / `anoporder`: the retirement run taken FORWARD. Round 6 caught the bare form and
    /// was defeated by one `Nop` between the retirements, which the oracle drops and which made
    /// every run a singleton. The sequence reads the run's slots in order, so the bare form is a
    /// different sequence — and a `Nop` cannot be inserted at all, because `observe` refuses any
    /// statement that is neither an assignment nor a marker.
    #[test]
    fn a_forward_retirement_run_is_refused_and_a_nop_cannot_hide_it() {
        assert_ne!(
            and_then_cmp_predicted(),
            seen(
                &[&[
                    St::L(4),
                    St::L(5),
                    St::A(&[1]),
                    St::L(6),
                    St::A(&[2]),
                    St::A(&[5, 6]),
                    St::D(5),
                    St::D(6),
                    St::L(7),
                    St::A(&[3]),
                    St::A(&[4, 7]),
                    St::D(7),
                    St::D(4),
                    St::A(&[8]),
                ]],
                &[],
            ),
            "the law must see a forward retirement run"
        );

        let si = SourceInfo::outermost(DUMMY_SP);
        let mut blocks: IndexVec<BasicBlock, BasicBlockData<'static>> = IndexVec::new();
        blocks.push(BasicBlockData::new_stmts(
            vec![Statement::new(si, StatementKind::Nop)],
            None,
            false,
        ));
        assert!(
            observe_with(&blocks, |_| ir_ty_token(&Ty::U32)).is_err(),
            "a statement the oracle deliberately ignores must fail the body closed here: that is \
             the evasion round 6's contiguous-run rule died of"
        );
    }

    /// `aswap2`: reverse the mint order AND re-reverse the dead list, so the run stays strictly
    /// decreasing while the STORAGE LIVES are in built's reverse order — 115 bodies, and round 6's
    /// order rule reads no live at all.
    ///
    /// This is also the attack that decides what a slot's NAME has to be. Alpha-renaming by first
    /// appearance — the oracle's rule, and this law's — is blind to two slots trading places: the
    /// alpha sequence below is character for character the honest one. The oracle sees it through
    /// the declared TYPE it prints beside each slot, which round 8 now carries too
    /// ([`super::mf_gate::MfTy`]); this law ALSO sees it through the operand POSITION each slot is
    /// moved out at ([`super::mf_gate::MfKey`]), and needs to, because the two traded slots in this
    /// fixture have the SAME declared type — where the type says nothing, the use site does.
    #[test]
    fn a_reversed_mint_order_is_refused_even_when_the_run_is_repaired() {
        assert_ne!(
            and_then_cmp_predicted(),
            seen(
                &[&[
                    St::L(4),
                    St::L(6),
                    St::A(&[1]),
                    St::L(5),
                    St::A(&[2]),
                    St::A(&[5, 6]),
                    St::D(5),
                    St::D(6),
                    St::L(7),
                    St::A(&[3]),
                    St::A(&[4, 7]),
                    St::D(7),
                    St::D(4),
                    St::A(&[8]),
                ]],
                &[],
            ),
            "the law must see a reversed mint order even with the retirement run repaired"
        );
    }

    /// The composition, and the property the whole law rests on: on built's own body the two sides
    /// are EQUAL, and one extra pair — a well-formed emission no plan asked for — makes them differ.
    #[test]
    fn the_two_sides_agree_on_builts_body_and_differ_on_one_extra_emission() {
        let f = min_if();
        let plan = plan_branch_markers(&f).expect("min_if is inside lane K's class");
        let got = predict_of(&f, plan.needs.clone(), Some(plan));
        assert_ne!(
            got,
            seen(
                &[
                    &[St::L(3), St::L(4), St::A(&[1]), St::A(&[4]), St::L(12)],
                    &[
                        St::D(4),
                        St::L(5),
                        St::A(&[2]),
                        St::A(&[5]),
                        St::D(5),
                        St::A(&[9]),
                        St::D(12),
                    ],
                    &[St::D(4), St::L(6), St::A(&[2]), St::A(&[6]), St::D(6), St::A(&[10])],
                    &[St::D(3), St::A(&[11])],
                    &[],
                ],
                &[(3, Ty::Bool)],
            ),
            "the law must see one extra pair"
        );
    }

    /// **THE EIGHTH REVIEW'S `ptype`, AS A SEQUENCE.** One `match` in `ShimCx::mf_operand` mints
    /// the operand temp at the same-width OPPOSITE SIGNEDNESS: bit-identical value, identical LLVM
    /// type, and a different `{ty}` in the oracle's marker line. Against round 7 it put 261 probe
    /// bodies and nine shipped `clean-kernel` bodies into admitted-and-wrong with the law green and
    /// the whole unit suite passing, because the declared type was the one component of the
    /// oracle's line that NEITHER side of the law derived. Both sides derive it now — the predicted
    /// side from the producer's annotation, the observed side from `local_decls` — so the two
    /// sequences differ in exactly that component and the body fails closed.
    #[test]
    fn a_temp_declared_at_the_wrong_type_is_refused() {
        // The honest body, which the sequence accepts (this is the fixture of
        // `the_predicted_sequence_is_builts_own_sequence_for_the_single_block_shapes`).
        let honest = &[&[St::L(2), St::A(&[]), St::A(&[2]), St::D(2), St::A(&[3])][..]][..];
        assert_eq!(field_eq_zero_predicted(), seen(honest, &[]));
        // The same statement sequence, the same positions, the same slots, the same use sites —
        // and `_2` declared `i32` where the field it copies is `u32`.
        assert_ne!(
            field_eq_zero_predicted(),
            seen(honest, &[(2, Ty::I32)]),
            "the law must see an operand temp minted at the wrong declared type"
        );
        // Same width, same signedness class, DIFFERENT width: also a different type.
        assert_ne!(field_eq_zero_predicted(), seen(honest, &[(2, Ty::U64)]));
        // And the faithful scalars are distinct from their width-collapsed twins, exactly as
        // `canon_ty` spells them (`usize != u64`, `char != u32`) — the property v25 B1 established
        // and the reason the token can be an index into one global table.
        assert_ne!(field_eq_zero_predicted(), seen(honest, &[(2, Ty::Usize)]));
        assert_ne!(field_eq_zero_predicted(), seen(honest, &[(2, Ty::Char)]));
    }

    /// NO PLAN, NO MARKER — and it is now a positional claim about the whole body. A body outside
    /// every plan predicts the EMPTY sequence, so a single marker anywhere in it fails closed.
    #[test]
    fn a_body_outside_every_plan_predicts_no_marker_at_all() {
        let f = and_then_cmp();
        let none = MfPlans::plans_for_test(None, None)
            .predict_from(&f, &HashSet::new(), &HashMap::new())
            .expect("a plan-free body has a sequence, and it is empty");
        assert_eq!(none, MfSeq::default());
        assert_ne!(none, seen(&[&[St::L(2), St::A(&[]), St::A(&[2]), St::D(2)]], &[]));
    }
}

#[cfg(test)]
mod marker_permutation_boundary_tests {
    use super::marker_type_sequence_is_preserved;

    #[test]
    fn constants_can_move_around_a_preserved_mixed_type_sequence() {
        // `E4 { b: 1, a, d: 2, c }`: after constants disappear, source order is already a:u32,
        // c:u64, exactly declaration order.
        assert!(marker_type_sequence_is_preserved(&[(0, "u32"), (2, "u64")]));
    }

    #[test]
    fn genuinely_permuted_mixed_types_remain_observable() {
        assert!(!marker_type_sequence_is_preserved(&[(2, "u64"), (0, "u32")]));
        // `e45`: c, a, b has [u64, u32, u32], declaration order has [u32, u32, u64].
        assert!(!marker_type_sequence_is_preserved(&[(2, "u64"), (0, "u32"), (1, "u32"),]));
    }

    #[test]
    fn same_typed_permutations_remain_invisible() {
        assert!(marker_type_sequence_is_preserved(&[(2, "u32"), (0, "u32"), (1, "u32"),]));
    }
}

/// Trust (lane MF-ZERO-3): the plans are MUTUALLY EXCLUSIVE, and that is a property of one
/// expression in `lower_ir_to_mir`, not of anybody's memory.
///
/// A marker plan is a whole-body claim — "these are the only constructs in this body that mint a
/// marker" — so two plans engaging in one body is two such claims about the same body, which is
/// exactly the state the third review measured (the ungated field-write arm minting its pair
/// beside built's branch/`let`/tail markers). Each specialized plan therefore forces
/// `source_form_ok` to `false`, which turns off BOTH the wave-MF operand plan and lane K's branch
/// plan. Delete either exclusion and one body can again carry two whole-body claims — so the
/// combined predicate is pinned here, at the source, the way `param_rty`'s named closure arm is.
#[cfg(test)]
mod plan_exclusivity_tests {
    use super::{MfWritePlan, source_form_marker_plan_available};

    #[test]
    fn a_specialized_body_cannot_also_hold_the_operand_or_branch_plan() {
        let src = include_str!("to_mir.rs");
        // Trust (lane MF-R5): the resolution moved INTO `MfPlans::seal` with the plans it
        // resolves — same expression, same conjunction, one constructor away from every arm.
        let needle = format!(
            "{}(write, borrow, {}(tcx, def))",
            "source_form_marker_plan_available", "source_form_admits"
        );
        assert_eq!(
            src.matches(needle.as_str()).count(),
            1,
            "`source_form_ok` must be conjoined with both specialized plans' absence, exactly              once. Without it a body can carry two whole-body marker claims at the same time,              which is the defect class lane MF-ZERO-3 exists to close."
        );
        let branch =
            format!("if source_form_ok {{ {}(func) }} else {{ None }}", "plan_branch_markers");
        assert_eq!(
            src.matches(branch.as_str()).count(),
            1,
            "lane K's branch plan must be gated on the same answer"
        );
        let operand = format!("None if source_form_ok => {}(func),", "plan_operand_marker_temps");
        assert_eq!(
            src.matches(operand.as_str()).count(),
            1,
            "wave-MF's operand plan must be gated on the same answer"
        );
    }

    /// Trust (wave-EP): the FIFTH whole-body plan is resolved against the other four in the same
    /// one place, and it takes the general source-form lane out of the running when it holds.
    /// Without the `payload.is_none()` conjunct a body could carry the payload plan AND wave-MF's
    /// operand plan at once — two whole-body marker claims on one body, which is the defect class
    /// lane MF-ZERO-3 exists to close.
    #[test]
    fn the_payload_plan_is_resolved_against_every_other_plan() {
        let src = include_str!("to_mir.rs");
        let gated = format!("let source_form_ok = {}.is_none()", "payload");
        assert_eq!(
            src.matches(gated.as_str()).count(),
            1,
            "the source-form lane must be conjoined with the payload plan's absence, exactly once"
        );
        let sealed = format!(
            "if write.is_none() && !borrow {{ {}(func) }} else {{ None }}",
            "plan_payload_markers"
        );
        assert_eq!(
            src.matches(sealed.as_str()).count(),
            1,
            "the payload plan must be refused when either specialized source-form plan owns the \
             body"
        );
        // And the constructor is still the only place a plan is decided.
        let field =
            format!("MfPlans {{ operand, branch, write, borrow, {}, checked }}", "payload");
        assert_eq!(
            src.matches(field.as_str()).count(),
            1,
            "`MfPlans::seal` must be the one constructor that carries the payload plan"
        );
    }

    /// Trust (wave-CK): the SIXTH whole-body plan, resolved against the other five in the same one
    /// place. The two conjuncts pinned here are what stop a body carrying the checked-chain plan
    /// AND one of the source-form plans at once — two whole-body marker claims on one body, which
    /// is the defect class lane MF-ZERO-3 exists to close, and the same shape wave-EP pinned above.
    #[test]
    fn the_checked_plan_is_resolved_against_every_other_plan() {
        let src = include_str!("to_mir.rs");
        let gated = format!("            && {}.is_none()\n", "checked");
        assert_eq!(
            src.matches(gated.as_str()).count(),
            1,
            "the source-form lane must be conjoined with the checked-chain plan's absence, \
             exactly once"
        );
        let sealed = format!(
            "let checked = if write.is_none()\n                && !borrow\n                && \
             payload.is_none()\n                && {}(tcx, def)\n            {{\n                \
             {}(func)\n            }} else {{\n                None\n            }};",
            "checked_params_mint_no_local", "plan_checked_markers"
        );
        assert_eq!(
            src.matches(sealed.as_str()).count(),
            1,
            "the checked-chain plan must be refused when any other specialized plan owns the body"
        );
    }

    #[test]
    fn source_form_availability_excludes_each_specialized_plan() {
        let write = MfWritePlan { marking_writes: 0 };
        assert!(source_form_marker_plan_available(None, false, true));
        assert!(!source_form_marker_plan_available(Some(write), false, true));
        assert!(!source_form_marker_plan_available(None, true, true));
        assert!(!source_form_marker_plan_available(Some(write), true, true));
        assert!(!source_form_marker_plan_available(None, false, false));
    }

    /// And the two NEW plans cannot both admit one body: the field-write plan requires at least
    /// one assignment (`if writes == 0 { return None }`) and the interior-borrow plan requires a
    /// statement-free block whose tail is an `&place`. Pinned by the two clauses that make it so.
    #[test]
    fn the_write_and_borrow_plans_are_disjoint_by_construction() {
        let src = include_str!("to_mir.rs");
        let write_needs_a_write = format!("if {} == 0 {{\n        return None;\n    }}", "writes");
        assert_eq!(
            src.matches(write_needs_a_write.as_str()).count(),
            1,
            "the field-write plan must refuse a body with no writes"
        );
        // Anchored on its own `return false;` body: `source_form_admits`'s walker asks the same
        // question one indentation level deeper and sets `self.ok` instead, and matching THAT one
        // would make this assertion pass with the interior-borrow clause deleted.
        let borrow_needs_no_stmts = format!(
            "if blk.{}.iter().any(|s| !matches!(s.kind, rustc_hir::StmtKind::Item(_))) {{\n        \
             return false;\n    }}",
            "stmts"
        );
        assert_eq!(
            src.matches(borrow_needs_no_stmts.as_str()).count(),
            1,
            "the interior-borrow plan must refuse a body with statements"
        );
    }
}

/// Trust (wave-EP, 2026-08-16): **THE ENUM-PAYLOAD-READ PLAN AND ITS HALF OF THE LAW.**
///
/// Two fixtures, both transcribed from the shipped `clean-kernel` trust-ir dump rather than
/// invented: `Reducibility::height` (payload arm FIRST) and `SimpPriority::value` (payload arm
/// SECOND). The plan's answer on each is asserted by NAME — which block carries the pair, which
/// block gets the trampoline — because those two numbers are the whole plan and getting either
/// wrong is a marker channel refusal, not a compile error.
///
/// The law's half is the same discipline `marker_law_tests` uses on the other four classes: the
/// PREDICTED sequence is compared against a hand-spelled FINISHED body, and then against three
/// one-statement mutations of it. Each mutation is a thing an emitter edit could do — move the
/// `StorageLive` past its own borrow, retire before the edge copy, drop the retirement — and each
/// must move the observed side and not the predicted one.
#[cfg(test)]
mod payload_marker_plan_tests {
    use rustc_abi::FieldIdx;
    use rustc_index::IndexVec;
    use rustc_middle::mir::{
        AggregateKind, BasicBlock, BasicBlockData, Local, Operand, Place, Rvalue, SourceInfo,
        Statement, StatementKind,
    };
    use rustc_span::DUMMY_SP;
    use trust_ir::{
        BlockId, Constant, EnumId, FuncId, FuncTyId, Function, Inst, InstrNode, SwitchCase, Ty,
        ValueId,
    };

    use super::mf_gate::{MfSeq, ir_ty_token, marker_kind, observe_with, predict_payload};
    use super::{MfPayloadPlan, plan_payload_markers};

    fn v(i: u32) -> ValueId {
        ValueId::new(i)
    }
    fn b(i: u32) -> BlockId {
        BlockId::new(i)
    }
    fn node(inst: Inst, result: Option<u32>) -> InstrNode {
        let n = InstrNode::new(inst);
        match result {
            Some(r) => n.with_result(v(r)),
            None => n,
        }
    }

    /// The head every fixture shares: the by-ref discriminant read, then a one-case switch —
    /// `%2 = load enum, ptr %0; %3 = extractfield u32 %2, 0; switch %3 [ tag: case default: dflt ]`.
    fn head(tag: i128, case: BlockId, dflt: BlockId) -> trust_ir::Block {
        let mut e = trust_ir::Block::new(b(0));
        e.params = vec![(v(0), Ty::Ptr)];
        e.body = vec![
            node(
                Inst::Load {
                    ty: Ty::Enum(EnumId::new(86)),
                    ptr: v(0),
                    volatile: false,
                    align: None,
                },
                Some(2),
            ),
            node(Inst::ExtractField { ty: Ty::U32, aggregate: v(2), field: 0 }, Some(3)),
            node(
                Inst::Switch {
                    value: v(3),
                    default: dflt,
                    default_args: vec![],
                    cases: vec![SwitchCase {
                        value: Constant::Int(tag),
                        target: case,
                        args: vec![],
                    }],
                    exhaustive_enum_unreachable: false,
                },
                None,
            ),
        ];
        e
    }

    /// The payload arm: `%c = const i64 4; %g = gep inbounds i8, ptr %0, %c; %r = load u32, ptr %g;
    /// br join(%r)`.
    fn payload_arm(id: BlockId, join: BlockId, c: u32, g: u32, r: u32) -> trust_ir::Block {
        let mut a = trust_ir::Block::new(id);
        a.body = vec![
            node(Inst::Const { ty: Ty::I64, value: Constant::Int(4) }, Some(c)),
            node(
                Inst::GEP { pointee_ty: Ty::I8, base: v(0), indices: vec![v(c)], inbounds: true },
                Some(g),
            ),
            node(Inst::Load { ty: Ty::U32, ptr: v(g), volatile: false, align: None }, Some(r)),
            node(Inst::Br { target: join, args: vec![v(r)] }, None),
        ];
        a
    }

    /// The folded-constant arm: `%k = const u32 N; br join(%k)`.
    fn const_arm(id: BlockId, join: BlockId, k: u32, n: i128) -> trust_ir::Block {
        let mut a = trust_ir::Block::new(id);
        a.body = vec![
            node(Inst::Const { ty: Ty::U32, value: Constant::Int(n) }, Some(k)),
            node(Inst::Br { target: join, args: vec![v(k)] }, None),
        ];
        a
    }

    fn join(id: BlockId, p: u32) -> trust_ir::Block {
        let mut j = trust_ir::Block::new(id);
        j.params = vec![(v(p), Ty::U32)];
        j.body = vec![node(Inst::Return { values: vec![v(p)] }, None)];
        j
    }

    /// `env::types::Reducibility::height` — `switch %3 [ 1: bb1 default: bb2 ]`, payload arm FIRST.
    fn height() -> Function {
        let mut f = Function::new(FuncId::new(0), "height", FuncTyId::new(162), b(0));
        f.blocks = vec![
            head(1, b(1), b(2)),
            payload_arm(b(1), b(3), 4, 5, 6),
            const_arm(b(2), b(3), 7, 0),
            join(b(3), 1),
        ];
        f
    }

    /// `env::types::SimpPriority::value` — `switch %3 [ 0: bb1 default: bb2 ]`, payload arm SECOND.
    fn value() -> Function {
        let mut f = Function::new(FuncId::new(0), "value", FuncTyId::new(162), b(0));
        f.blocks = vec![
            head(0, b(1), b(2)),
            const_arm(b(1), b(3), 4, 1000),
            payload_arm(b(2), b(3), 5, 6, 7),
            join(b(3), 1),
        ];
        f
    }

    /// One statement of a fixture body: an assignment naming its bare operand locals, a live, or a
    /// dead. Same spelling as `marker_law_tests`, so the two modules' fixtures read alike.
    #[derive(Clone, Copy)]
    enum St<'a> {
        A(&'a [u32]),
        L(u32),
        D(u32),
    }

    fn body(blocks: &[&[St<'_>]]) -> IndexVec<BasicBlock, BasicBlockData<'static>> {
        let si = SourceInfo::outermost(DUMMY_SP);
        let mut out: IndexVec<BasicBlock, BasicBlockData<'static>> = IndexVec::new();
        for blk in blocks {
            let stmts: Vec<Statement<'static>> = blk
                .iter()
                .map(|st| {
                    let kind = match st {
                        St::A(ops) => {
                            let fields: IndexVec<FieldIdx, Operand<'static>> = ops
                                .iter()
                                .map(|l| Operand::Move(Place::from(Local::from_u32(*l))))
                                .collect();
                            StatementKind::Assign(Box::new((
                                Place::from(Local::from_u32(0)),
                                Rvalue::Aggregate(Box::new(AggregateKind::Tuple), fields),
                            )))
                        }
                        St::L(l) => marker_kind(Local::from_u32(*l), true),
                        St::D(l) => marker_kind(Local::from_u32(*l), false),
                    };
                    Statement::new(si, kind)
                })
                .collect();
            out.push(BasicBlockData::new_stmts(stmts, None, false));
        }
        out
    }

    /// The observed side of a fixture body. The one marked slot is the arm-binding borrow temp,
    /// declared `&u32` — outside the scalar denotation, so `MfTy::Opaque`, which `Ty::Ptr` is the
    /// trust-ir spelling of here.
    fn seen(blocks: &[&[St<'_>]]) -> MfSeq {
        observe_with(&body(blocks), |_| ir_ty_token(&Ty::Ptr))
            .expect("the fixture body is inside the marker channel's fragment")
    }

    // ---- the plan ------------------------------------------------------------------------

    #[test]
    fn the_plan_admits_height_with_the_pair_and_the_trampoline_on_the_first_arm() {
        assert_eq!(
            plan_payload_markers(&height()),
            Some(MfPayloadPlan { arm: b(1), tramp: b(1) }),
            "`Reducibility::height` puts the payload arm FIRST, so the pair and the trampoline \
             are the same block — built's `bb2: falseEdge -> [real: bb5, imaginary: bb1]`"
        );
    }

    #[test]
    fn the_plan_admits_value_with_the_pair_second_and_the_trampoline_still_first() {
        assert_eq!(
            plan_payload_markers(&value()),
            Some(MfPayloadPlan { arm: b(2), tramp: b(1) }),
            "`SimpPriority::value` puts the payload arm SECOND; the trampoline stays on the FIRST \
             candidate, which is what makes built's marker land at fine index 4 and not 3"
        );
    }

    #[test]
    fn a_body_with_a_producer_scope_is_refused() {
        let mut f = height();
        f.scopes = Some(Vec::new());
        assert_eq!(
            plan_payload_markers(&f),
            None,
            "wave-MF's `let`-scope firewall is consulted first and is unchanged"
        );
    }

    #[test]
    fn a_three_block_body_is_refused() {
        let mut f = height();
        f.blocks.pop();
        assert_eq!(plan_payload_markers(&f), None, "the class is exactly head + two arms + join");
    }

    #[test]
    fn a_second_use_of_the_payload_in_the_arm_is_refused() {
        let mut f = height();
        // `br bb3(%6, %6)` — the retirement's position depends on the edge-copy count, and a
        // payload read consumed twice is not the single-use shape built's arm binding has.
        f.blocks[1].body.pop();
        f.blocks[1].body.push(node(Inst::Br { target: b(3), args: vec![v(6), v(6)] }, None));
        assert_eq!(plan_payload_markers(&f), None);
    }

    #[test]
    fn an_arm_that_computes_after_the_payload_read_is_refused() {
        let mut f = height();
        let br = f.blocks[1].body.pop().expect("the arm's terminator");
        f.blocks[1].body.push(node(
            Inst::BinOp { op: trust_ir::BinOp::Add, ty: Ty::U32, lhs: v(6), rhs: v(6) },
            Some(9),
        ));
        f.blocks[1].body.push(br);
        assert_eq!(plan_payload_markers(&f), None, "the arm is exactly the triple and its `Br`");
    }

    #[test]
    fn a_join_that_does_not_immediately_return_its_parameter_is_refused() {
        let mut f = height();
        f.blocks[3].body = vec![node(Inst::Return { values: vec![] }, None)];
        assert_eq!(plan_payload_markers(&f), None);
    }

    #[test]
    fn a_head_that_is_not_the_by_ref_discriminant_read_is_refused() {
        let mut f = height();
        // `extractfield 1` is a payload read, not the tag read the switch is driven by.
        f.blocks[0].body[1] =
            node(Inst::ExtractField { ty: Ty::U32, aggregate: v(2), field: 1 }, Some(3));
        assert_eq!(plan_payload_markers(&f), None);
    }

    #[test]
    fn a_two_case_switch_is_refused() {
        let mut f = height();
        let Inst::Switch { cases, .. } = &mut f.blocks[0].body[2].inst else {
            panic!("the head's terminator is a Switch");
        };
        cases.push(SwitchCase { value: Constant::Int(2), target: b(2), args: vec![] });
        assert_eq!(
            plan_payload_markers(&f),
            None,
            "two explicit cases is a three-candidate match; built chains two falseEdge blocks and \
             this plan mints one"
        );
    }

    // ---- the law -------------------------------------------------------------------------

    /// Built's own arm block, verbatim: `StorageLive(_3); _3 = &(((*_1) as Regular).0: u32);
    /// _0 = copy (*_3); StorageDead(_3); goto -> bb6;`. The derived body spells the same two
    /// assignments — the borrow, then the edge copy into the join's parameter local.
    #[test]
    fn the_predicted_sequence_is_builts_own_sequence() {
        let f = height();
        let plan = plan_payload_markers(&f).expect("height is inside the class");
        assert_eq!(
            predict_payload(&f, &plan).expect("the fixture is inside the sequence model"),
            // bb0: the discriminant read. bb1: the pair. bb2: the folded const's edge copy.
            // bb3: the return copy. The trampoline is appended after all of them, empty.
            seen(&[
                &[St::A(&[])],
                &[St::L(3), St::A(&[]), St::A(&[]), St::D(3)],
                &[St::A(&[])],
                &[St::A(&[])],
                &[],
            ])
        );
    }

    #[test]
    fn the_second_shape_predicts_its_pair_in_the_second_arm() {
        let f = value();
        let plan = plan_payload_markers(&f).expect("value is inside the class");
        assert_eq!(
            predict_payload(&f, &plan).expect("the fixture is inside the sequence model"),
            seen(&[
                &[St::A(&[])],
                &[St::A(&[])],
                &[St::L(3), St::A(&[]), St::A(&[]), St::D(3)],
                &[St::A(&[])],
                &[],
            ])
        );
    }

    /// The three one-statement relocations an emitter edit could make. Each moves the OBSERVED
    /// side and not the predicted one, so each fails the body CLOSED — which is the whole content
    /// of the law for this class.
    #[test]
    fn a_relocated_or_missing_marker_is_refused() {
        let f = height();
        let plan = plan_payload_markers(&f).expect("height is inside the class");
        let predicted = predict_payload(&f, &plan).expect("the fixture is inside the model");

        // (a) the `StorageLive` lands AFTER its own borrow.
        assert_ne!(
            predicted,
            seen(&[
                &[St::A(&[])],
                &[St::A(&[]), St::L(3), St::A(&[]), St::D(3)],
                &[St::A(&[])],
                &[St::A(&[])],
                &[],
            ]),
            "a `StorageLive` moved past its own initialising assign must be refused"
        );
        // (b) the retirement lands BEFORE the edge copy that consumes the borrow.
        assert_ne!(
            predicted,
            seen(&[
                &[St::A(&[])],
                &[St::L(3), St::A(&[]), St::D(3), St::A(&[])],
                &[St::A(&[])],
                &[St::A(&[])],
                &[],
            ]),
            "a retirement moved before the assign that consumes it must be refused"
        );
        // (c) the retirement is dropped.
        assert_ne!(
            predicted,
            seen(&[
                &[St::A(&[])],
                &[St::L(3), St::A(&[]), St::A(&[])],
                &[St::A(&[])],
                &[St::A(&[])],
                &[],
            ]),
            "a marker minted and never retired must be refused"
        );
        // (d) the pair lands in the WRONG ARM — the block index is a component of every event.
        assert_ne!(
            predicted,
            seen(&[
                &[St::A(&[])],
                &[St::A(&[]), St::A(&[])],
                &[St::L(3), St::A(&[]), St::D(3)],
                &[St::A(&[])],
                &[],
            ]),
            "a pair emitted in the other arm must be refused"
        );
    }

    /// And the declared TYPE is compared, exactly as round 8 made it be everywhere else: the slot
    /// is `&FieldTy`, and a finished body that declared it at a body scalar is a different body.
    #[test]
    fn a_borrow_temp_declared_at_a_scalar_type_is_refused() {
        let f = height();
        let plan = plan_payload_markers(&f).expect("height is inside the class");
        let predicted = predict_payload(&f, &plan).expect("the fixture is inside the model");
        let scalar_typed = observe_with(
            &body(&[
                &[St::A(&[])],
                &[St::L(3), St::A(&[]), St::A(&[]), St::D(3)],
                &[St::A(&[])],
                &[St::A(&[])],
                &[],
            ]),
            |_| ir_ty_token(&Ty::U32),
        )
        .expect("the fixture body is inside the marker channel's fragment");
        assert_ne!(predicted, scalar_typed);
    }
}

#[cfg(test)]
mod str_const_flip_firewall_tests {
    use std::collections::HashMap;

    use trust_ir::value::GlobalId;
    use trust_ir::{Constant, FatPtrKind, Inst, InstrNode, Ty, ValueId};

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

/// Trust (wave-ABI): the shim's ABI-boundary types must be CROSS-CHECKED against the built type,
/// including at the scalar arms — the two positions that used to trust the Module unilaterally.
///
/// THE DEFECT THIS PINS. Every non-scalar arm in `param_rty` and in the return reconstruction
/// threads `built`/`built_ret_ty` and proves the widening faithful, because the Module is not an
/// authority on identity (attack A1). The two SCALAR arms did not: they answered
/// `scalar_rustc_ty` and adopted its denotation. So when the producer's wave-SEAM Option-flag
/// lane spelled a declined `Option<(u32,u32)>` as `Ty::Bool`, this file minted `tcx.types.bool`
/// for it and the derived `mir::Body` declared `_0: bool` for an `Option`-returning function.
///
/// The producer-side guard (`lib.rs` `guard_sig_position_ty`) closes that at the source. These
/// arms close the CLASS: any FUTURE lane that widens an opaque spelling into a scalar meets a
/// wall here rather than an ABI lie. That is the T6 report's core complaint — that `to_mir`
/// contributed no defense in depth — answered where it was made.
#[cfg(test)]
mod abi_scalar_crosscheck_tests {
    /// The PRODUCTION text of this file, comment lines stripped. This module's own source is
    /// inside `include_str!("to_mir.rs")`, so an un-stripped search would match the prose above
    /// and every assertion would pass with the production arm deleted. Needles are additionally
    /// assembled at run time, the discipline `test_closure_env_param_is_refused_by_name` follows.
    fn production_code() -> String {
        let src = include_str!("to_mir.rs");
        let end = src
            .find(&format!("\n#[cfg({})]", "test"))
            .expect("the file must have a test section to bound production at");
        src[..end]
            .lines()
            .filter(|l| !l.trim_start().starts_with("//"))
            .collect::<Vec<_>>()
            .join("\n")
    }

    /// **THE PARAM ARM.** The scalar denotation may not be adopted until it EQUALS the built decl
    /// type, and the check must sit inside `param_rty`'s `scalar_rustc_ty` fast path — which is
    /// the first thing that function does, so a check placed anywhere later is dead code.
    #[test]
    fn the_scalar_param_denotation_is_checked_against_built() {
        let code = production_code();
        let at = code
            .find(&format!("fn {}<'tcx>(", "param_rty"))
            .expect("`param_rty` must be DEFINED in production");
        let lane = &code[at..];
        let fast_path = format!("if let Some(srt) = {}(tcx, p) {{", "scalar_rustc_ty");
        let fp_at = lane.find(fast_path.as_str()).expect("the scalar fast path must exist");
        let check = format!("if srt != {} {{", "built");
        let ck_at = lane.find(check.as_str()).expect(
            "a scalar param's denotation must be PROVEN equal to the built decl type before it \
             is adopted — without it, any opaque lane the producer spells as a scalar is \
             silently respelled into a real rustc type",
        );
        assert!(
            fp_at < ck_at && ck_at < fp_at + 600,
            "the cross-check must live INSIDE the scalar fast path; `param_rty` returns from \
             that path immediately, so a check after it can never run",
        );
    }

    /// **THE RETURN ARM — the exact line that produced `_0: bool`.**
    ///
    /// Pinned as a GUARDED match arm rather than as a bare mention: the failure mode is an author
    /// restoring the unconditional `Some(t) => t`, which a presence-only assertion on the word
    /// `built_ret_ty` would not notice (the neighbouring Ptr/Struct arms mention it too).
    ///
    /// The negative half is scoped TWICE — to `lower_ir_to_mir` and to the arm's exact 12-space
    /// match-arm indentation, anchored at a line start. Neither alone is enough: `Some(t) => t,`
    /// occurs nine times in this file at deeper indentation (unrelated `scalar_ty` unwraps inside
    /// `const_of`), so an unanchored substring search matches all nine and the assertion is
    /// vacuous. That is not hypothetical — it is what the first draft of this test did.
    #[test]
    fn the_scalar_return_denotation_is_checked_against_built() {
        let code = production_code();
        let guarded = format!("Some(srt) if srt == {} => srt,", "built_ret_ty");
        assert_eq!(
            code.matches(guarded.as_str()).count(),
            1,
            "the scalar RETURN arm must be GUARDED by equality with the built `_0` type. This \
             is the line that declared `_0: bool` for `shift_bvar_range() -> Option<(u32,u32)>`; \
             an unguarded `Some(t) => t` restores the ABI lie.",
        );
        let at = code
            .find(&format!("fn {}<'tcx>(", "lower_ir_to_mir"))
            .expect("`lower_ir_to_mir` must be DEFINED in production");
        let lane = &code[at..];
        let unguarded = format!("\n            Some({}) => {},\n", "t", "t");
        assert_eq!(
            lane.matches(unguarded.as_str()).count(),
            0,
            "the unguarded scalar-return arm must not come back: at this indentation, inside \
             the ABI reconstruction, `Some(t) => t` IS the ABI lie",
        );
    }

    /// Both cross-checks must REJECT, not repair. A respell that silently substituted the built
    /// type would keep the body lowering while the Module and the derived body disagreed about
    /// what the function is — the differential would then compare two different functions.
    #[test]
    fn a_denotation_mismatch_is_a_refusal_not_a_substitution() {
        let code = production_code();
        for reason in ["param widening: trust-ir scalar", "return widening: trust-ir scalar"] {
            let needle = format!("\"{reason}");
            assert_eq!(
                code.matches(needle.as_str()).count(),
                1,
                "`{reason}` must be minted exactly once, as an `unsup` refusal — the shim fails \
                 closed on a spelling it cannot prove faithful, it never repairs one",
            );
        }
    }
}

#[cfg(test)]
mod branch_marker_plan_tests {
    //! Trust (lane K): the MULTI-BLOCK marker plan, as a pure function over trust-ir. These pin
    //! the two refusals that were forced by MEASUREMENT rather than caution — the bare-param
    //! condition (`param_cond` / `match_bool` are byte-identical trust-ir with opposite built
    //! marker sequences, and `match_bool` is `markers_exact: true` and flipping TODAY) and the
    //! marked-operand-of-a-marked-result shape (built pushes the OUTER temp's `StorageLive`
    //! first; a linear instruction walk pushes the inner one first).
    use std::collections::HashSet;

    use trust_ir::{
        BinOp, BlockId, Constant, FuncId, FuncTyId, Function, ICmpOp, Inst, InstrNode, ScopeData,
        Ty, ValueId,
    };

    use super::{MfBranchPlan, plan_branch_markers};

    fn b(i: u32) -> BlockId {
        BlockId::new(i)
    }
    fn v(i: u32) -> ValueId {
        ValueId::new(i)
    }
    fn node(inst: Inst, result: Option<u32>) -> InstrNode {
        let n = InstrNode::new(inst);
        match result {
            Some(r) => n.with_result(v(r)),
            None => n,
        }
    }
    fn konst(r: u32, k: i128) -> InstrNode {
        node(Inst::Const { ty: Ty::U32, value: Constant::Int(k) }, Some(r))
    }
    fn icmp(r: u32, lhs: u32, rhs: u32) -> InstrNode {
        node(Inst::ICmp { op: ICmpOp::Eq, ty: Ty::U32, lhs: v(lhs), rhs: v(rhs) }, Some(r))
    }
    fn condbr(cond: u32, t: u32, e: u32) -> InstrNode {
        node(
            Inst::CondBr {
                cond: v(cond),
                then_target: b(t),
                then_args: vec![],
                else_target: b(e),
                else_args: vec![],
            },
            None,
        )
    }
    fn br(target: u32, args: &[u32]) -> InstrNode {
        node(Inst::Br { target: b(target), args: args.iter().map(|a| v(*a)).collect() }, None)
    }
    fn ret(values: &[u32]) -> InstrNode {
        node(Inst::Return { values: values.iter().map(|a| v(*a)).collect() }, None)
    }

    /// The `min_if` shape, verbatim from the producer dump of
    /// `crates/trust-thir-lower/probes/mf_multiblock.rs`:
    /// `bb0: %3 = const; %4 = icmp %0,%3; condbr %4, bb1, bb2`, two computing arms, one join.
    fn min_if(head_cond_ops: (u32, u32)) -> Function {
        let mut f = Function::new(FuncId::new(0), "min_if", FuncTyId::new(0), b(0));
        let mut e = trust_ir::Block::new(b(0));
        e.params = vec![(v(0), Ty::U32), (v(1), Ty::U32)];
        e.body = vec![konst(3, 0), icmp(4, head_cond_ops.0, head_cond_ops.1), condbr(4, 1, 2)];
        let mut t = trust_ir::Block::new(b(1));
        t.body = vec![konst(5, 1), icmp(6, 1, 5), br(3, &[6])];
        let mut el = trust_ir::Block::new(b(2));
        el.body = vec![konst(7, 2), icmp(8, 1, 7), br(3, &[8])];
        let mut j = trust_ir::Block::new(b(3));
        j.params = vec![(v(2), Ty::Bool)];
        j.body = vec![ret(&[2])];
        f.blocks = vec![e, t, el, j];
        f
    }

    fn accepted(f: &Function) -> MfBranchPlan {
        plan_branch_markers(f).expect("body should be inside the multi-block marker class")
    }

    #[test]
    fn diamond_is_admitted_and_marks_only_the_condition() {
        let f = min_if((0, 3));
        let plan = accepted(&f);
        // Only the CONDITION takes a marker-carrying temp. The two arm values flow into a `Br`
        // edge argument, and built writes an arm's tail expression straight into `_0`.
        assert_eq!(plan.needs, HashSet::from([v(4)]));
        let br0 = plan.branch.get(&b(0)).copied().expect("the head's CondBr is planned");
        assert_eq!(br0.cond, v(4));
        assert_eq!((br0.then_target, br0.else_target), (b(1), b(2)));
        // The condition's own temp dies at the reconvergence point, not in either arm.
        assert_eq!(br0.join, b(3));
        assert_eq!(plan.branch.len(), 1);
    }

    #[test]
    fn a_source_let_scope_is_refused_before_anything_else() {
        // Wave-MF's firewall, unchanged: `nat_gcd` and both `to_signed` bodies are outside the
        // plan at THIS line, before multi-block support is even consulted.
        let mut f = min_if((0, 3));
        f.scopes = Some(vec![
            ScopeData { parent: None, span: None },
            ScopeData { parent: Some(0), span: None },
        ]);
        assert!(plan_branch_markers(&f).is_none());
    }

    #[test]
    fn a_bare_param_condition_is_refused() {
        // THE LOST-FLIP TRIPWIRE. `param_cond(a: bool, ..)` and `match_bool(c: bool, ..)` lower
        // to BYTE-IDENTICAL trust-ir (`condbr %0, bb1, bb2` over a param) and neither opens a
        // scope, yet built gives the first `StorageLive(_4); _4 = copy _1; switchInt(move _4)`
        // and the second `PlaceMention(_1); switchInt(copy _1)` with ZERO markers. `match_bool`
        // is `markers_exact: true` and flips today; a plan that minted a temp for a bare-param
        // condition would take that flip away silently.
        let mut f = Function::new(FuncId::new(0), "param_cond", FuncTyId::new(0), b(0));
        let mut e = trust_ir::Block::new(b(0));
        e.params = vec![(v(0), Ty::Bool), (v(1), Ty::U32), (v(2), Ty::U32)];
        e.body = vec![condbr(0, 1, 2)];
        let mut t = trust_ir::Block::new(b(1));
        t.body = vec![br(3, &[1])];
        let mut el = trust_ir::Block::new(b(2));
        el.body = vec![br(3, &[2])];
        let mut j = trust_ir::Block::new(b(3));
        j.params = vec![(v(3), Ty::U32)];
        j.body = vec![ret(&[3])];
        f.blocks = vec![e, t, el, j];
        assert!(plan_branch_markers(&f).is_none());
    }

    /// `join_is_head`, verbatim from `probes/mb_joinhead.rs`:
    /// `if (if a == 0 { b } else { c }) == 0 { 1 } else { 2 }`.
    ///
    /// `second_cond_reads_join` picks ONE OPERAND and nothing else: what the second branch's
    /// condition compares — `true` = the join PARAMETER (the inner `if`'s value: the defect
    /// shape), `false` = the entry param `a`. The join parameter is live and used by a `Br` edge
    /// argument in BOTH bodies; block count, block order, both joins, both conditions'
    /// marked-result status and every arm's predecessor count are byte-identical. So a verdict
    /// that moves between the two moved because of that operand.
    fn join_is_head(second_cond_reads_join: bool) -> Function {
        let mut f = Function::new(FuncId::new(0), "join_is_head", FuncTyId::new(0), b(0));
        let mut e = trust_ir::Block::new(b(0));
        e.params = vec![(v(0), Ty::U32), (v(1), Ty::U32), (v(2), Ty::U32)];
        e.body = vec![konst(3, 0), icmp(4, 0, 3), condbr(4, 1, 2)];
        let mut t = trust_ir::Block::new(b(1));
        t.body = vec![br(3, &[1])];
        let mut el = trust_ir::Block::new(b(2));
        el.body = vec![br(3, &[2])];
        // b3 is the FIRST branch's join AND the second branch's head.
        let mut j = trust_ir::Block::new(b(3));
        j.params = vec![(v(5), Ty::U32)];
        let cond_lhs = if second_cond_reads_join { 5 } else { 0 };
        j.body = vec![konst(6, 0), icmp(7, cond_lhs, 6), condbr(7, 4, 5)];
        let mut t2 = trust_ir::Block::new(b(4));
        // The join parameter is used by a `Br` edge argument in BOTH bodies — a terminator use,
        // which the rule permits. Only the `icmp` operand above differs.
        t2.body = vec![br(6, &[5])];
        let mut e2 = trust_ir::Block::new(b(5));
        e2.body = vec![konst(9, 2), br(6, &[9])];
        let mut j2 = trust_ir::Block::new(b(6));
        j2.params = vec![(v(10), Ty::U32)];
        j2.body = vec![ret(&[10])];
        f.blocks = vec![e, t, el, j, t2, e2, j2];
        f
    }

    /// DEFECT 1, CLOSED BY EXPLICIT REFUSAL. `join_is_head` / `chain_of_ifs` /
    /// `double_nested_cond` passed every condition lane K wrote and still emitted a sequence that
    /// was not built's (`line 2: built mk b0.0:live s2:bool vs derived mk b2.0:dead s1:u32`):
    /// built's `as_temp` opens the outer comparison's result temp in the HEAD block, before it
    /// evaluates the inner `if`, and this shim's linear walk reaches the inner branch first. The
    /// join-parameter rule refuses them.
    #[test]
    fn a_join_parameter_consumed_by_an_instruction_is_refused() {
        assert!(
            plan_branch_markers(&join_is_head(true)).is_none(),
            "a `CondBr` condition computed FROM a join parameter is the `join_is_head` defect \
             shape — built hoists that temp's `StorageLive` into the head block and this shim \
             cannot",
        );
    }

    /// ...and the refusal fires for THAT reason, not incidentally. The same body with the same
    /// join parameter, still live and still used, but consumed by a `Br` edge argument instead of
    /// by an instruction, is ADMITTED — so nothing about "a join that is also a head", the block
    /// count, or the second branch itself is doing the refusing.
    #[test]
    fn a_join_parameter_used_only_by_a_terminator_stays_admitted() {
        let plan = plan_branch_markers(&join_is_head(false))
            .expect("a join parameter consumed only by a terminator is inside the class");
        // Both branches are still planned: the refusal above removed a body from a class that
        // otherwise genuinely contains this shape.
        assert_eq!(plan.branch.len(), 2);
        assert_eq!(plan.needs, HashSet::from([v(4), v(7)]));
    }

    #[test]
    fn a_marked_operand_of_a_marked_result_is_refused() {
        // `if (a & b) == 0 { .. }`: built emits `StorageLive(_c)` (the condition's own temp)
        // BEFORE `StorageLive(_and)` (the sub-expression's), because `as_temp` pushes the
        // destination's marker and only then builds into it. This shim walks the instruction
        // list linearly and reaches the `&` first, so the two orders disagree.
        let mut f = min_if((0, 3));
        f.blocks[0].body = vec![
            node(Inst::BinOp { op: BinOp::And, ty: Ty::U32, lhs: v(0), rhs: v(1) }, Some(9)),
            konst(3, 0),
            icmp(4, 9, 3),
            condbr(4, 1, 2),
        ];
        assert!(plan_branch_markers(&f).is_none());
    }

    #[test]
    fn a_back_edge_is_refused() {
        // A loop's condition temp has no single reconvergence point, and `nat_gcd` is the real
        // body this covers (it is already outside the firewall; this is the independent net).
        // The `Return` block is left in place so the refusal is provably the BACK EDGE and not
        // the one-`Return` rule.
        let mut f = min_if((0, 3));
        f.blocks[2].body = vec![konst(7, 2), icmp(8, 1, 7), br(0, &[])];
        assert!(plan_branch_markers(&f).is_none());
    }

    #[test]
    fn a_switch_terminator_is_refused() {
        // Every currently-flipping multi-block body in `clean-kernel` is `Switch`-driven with
        // zero `condbr`. Refusing `Switch` outright is what keeps all of them bit-identical.
        let mut f = min_if((0, 3));
        f.blocks[0].body = vec![
            konst(3, 0),
            icmp(4, 0, 3),
            node(
                Inst::Switch {
                    value: v(4),
                    default: b(1),
                    default_args: vec![],
                    cases: vec![],
                    exhaustive_enum_unreachable: false,
                },
                None,
            ),
        ];
        assert!(plan_branch_markers(&f).is_none());
    }

    #[test]
    fn a_single_block_body_stays_with_wave_mf() {
        let mut f = Function::new(FuncId::new(0), "one", FuncTyId::new(0), b(0));
        let mut e = trust_ir::Block::new(b(0));
        e.params = vec![(v(0), Ty::U32)];
        e.body = vec![konst(1, 0), icmp(2, 0, 1), ret(&[2])];
        f.blocks = vec![e];
        assert!(plan_branch_markers(&f).is_none(), "single-block is wave-MF's class");
    }
}

#[cfg(test)]
mod checked_plan_tests {
    //! Trust (wave-CK, 2026-08-17): the CHECKED-ARITHMETIC-CHAIN plan
    //! ([`plan_checked_markers`]) and its sequence model
    //! ([`mf_gate::predict_checked`]), as pure functions over trust-ir — no compiler, no `tcx`.
    //!
    //! The fixtures are the producer's own dump for `const A: usize = 256 * 1024 * 1024` and its
    //! three-factor sibling (`crates/clean-kernel/src/cert/compression/limits.rs`), transcribed
    //! instruction for instruction.
    //!
    //! Every refusal test comes with a MINIMALLY-DIFFERENT sibling that is still admitted, because
    //! a bare `None` could always be some unrelated condition firing.
    use rustc_index::IndexVec;
    use rustc_middle::mir::{
        BasicBlock, BasicBlockData, Local, Operand, Place, Rvalue, SourceInfo, Statement,
        StatementKind, UnOp,
    };
    use rustc_span::DUMMY_SP;
    use trust_ir::{
        BinOp, BlockId, CastOp, Constant, FuncId, FuncTyId, Function, ICmpOp, Inst, InstrNode,
        OverflowOp, Ty, ValueId,
    };

    use super::mf_gate::{MfSeq, ir_ty_token, marker_kind, observe_with, predict_checked};
    use super::{MfCheckedPlan, plan_checked_markers};

    fn v(i: u32) -> ValueId {
        ValueId::new(i)
    }
    fn b(i: u32) -> BlockId {
        BlockId::new(i)
    }
    fn node(inst: Inst, result: Option<u32>) -> InstrNode {
        let n = InstrNode::new(inst);
        match result {
            Some(r) => n.with_result(v(r)),
            None => n,
        }
    }
    fn konst(r: u32, ty: Ty, k: i128) -> InstrNode {
        node(Inst::Const { ty, value: Constant::Int(k) }, Some(r))
    }
    fn kbool(r: u32, k: bool) -> InstrNode {
        node(Inst::Const { ty: Ty::Bool, value: Constant::Bool(k) }, Some(r))
    }
    fn ret(values: &[u32]) -> InstrNode {
        node(Inst::Return { values: values.iter().map(|a| v(*a)).collect() }, None)
    }

    /// One checked-multiply unit, exactly as the producer emits it: the `Overflow` (two results:
    /// the product and the overflow bit), `Const false`, `Const true`, the `Select` that turns the
    /// bit into an `ok` flag, and the `Assert`.
    fn mul_unit(res: u32, of: u32, ty: Ty, lhs: u32, rhs: u32, fc: u32, tc: u32, ok: u32) -> Vec<InstrNode> {
        vec![
            InstrNode::new(Inst::Overflow {
                op: OverflowOp::MulOverflow,
                ty,
                lhs: v(lhs),
                rhs: v(rhs),
            })
            .with_result(v(res))
            .with_result(v(of)),
            kbool(fc, false),
            kbool(tc, true),
            node(
                Inst::Select { ty: Ty::Bool, cond: v(of), then_val: v(fc), else_val: v(tc) },
                Some(ok),
            ),
            node(Inst::Assert { cond: v(ok) }, None),
        ]
    }

    fn body(params: Vec<(ValueId, Ty)>, nodes: Vec<InstrNode>) -> Function {
        let mut f = Function::new(FuncId::new(0), "probe", FuncTyId::new(0), b(0));
        let mut e = trust_ir::Block::new(b(0));
        e.params = params;
        e.body = nodes;
        f.blocks = vec![e];
        f
    }

    /// `const A: usize = 256 * 1024 * 1024` — two units, one marked link.
    fn two_unit() -> Function {
        let mut n = vec![konst(0, Ty::Usize, 256), konst(1, Ty::Usize, 1024)];
        n.extend(mul_unit(2, 3, Ty::Usize, 0, 1, 4, 5, 6));
        n.push(konst(7, Ty::Usize, 1024));
        n.extend(mul_unit(8, 9, Ty::Usize, 2, 7, 10, 11, 12));
        n.push(ret(&[8]));
        body(vec![], n)
    }

    /// `const B: u64 = 16 * 1024 * 1024 * 1024` — three units, two marked links.
    fn three_unit() -> Function {
        let mut n = vec![konst(0, Ty::U64, 16), konst(1, Ty::U64, 1024)];
        n.extend(mul_unit(2, 3, Ty::U64, 0, 1, 4, 5, 6));
        n.push(konst(7, Ty::U64, 1024));
        n.extend(mul_unit(8, 9, Ty::U64, 2, 7, 10, 11, 12));
        n.push(konst(13, Ty::U64, 1024));
        n.extend(mul_unit(14, 15, Ty::U64, 8, 13, 16, 17, 18));
        n.push(ret(&[14]));
        body(vec![], n)
    }

    // ---- the class -------------------------------------------------------------------------

    #[test]
    fn test_plan_two_unit_chain_marks_the_inner_product() {
        assert_eq!(
            plan_checked_markers(&two_unit()),
            Some(MfCheckedPlan { chain: vec![(v(2), Ty::Usize), (v(8), Ty::Usize)] }),
            "`256 * 1024` is built's operand temp; `* 1024` is the outermost expression and \
             goes straight into `_0`",
        );
    }

    #[test]
    fn test_plan_three_unit_chain_marks_both_inner_products() {
        assert_eq!(
            plan_checked_markers(&three_unit()),
            Some(MfCheckedPlan {
                chain: vec![(v(2), Ty::U64), (v(8), Ty::U64), (v(14), Ty::U64)]
            }),
        );
    }

    #[test]
    fn test_plan_a_let_scope_is_refused() {
        let mut f = two_unit();
        f.scopes = Some(vec![trust_ir::ScopeData { parent: None, span: None }]);
        assert!(
            plan_checked_markers(&f).is_none(),
            "wave-MF's firewall is consulted first and unchanged",
        );
    }

    /// Trust (LANE PCA plan-clause audit, 2026-08-17): the block-parameter refusal MOVED, and this
    /// test moved with it. The pure trust-ir plan now ADMITS a body that merely HAS a parameter —
    /// its clauses force every chain leaf to be a `Const`, so no instruction of an admitted body
    /// can read one — and the remaining hazard (a parameter whose PATTERN mints a named binding
    /// local, which is a marker) is asked of the SOURCE at the seal site by
    /// `checked_params_mint_no_local`. The two halves are pinned separately: the trust-ir half
    /// here, the source half by `the_checked_plan_asks_the_source_about_its_parameters` below.
    #[test]
    fn test_plan_an_unread_block_parameter_is_admitted() {
        let mut n = vec![konst(0, Ty::Usize, 256), konst(1, Ty::Usize, 1024)];
        n.extend(mul_unit(2, 3, Ty::Usize, 0, 1, 4, 5, 6));
        n.push(konst(7, Ty::Usize, 1024));
        n.extend(mul_unit(8, 9, Ty::Usize, 2, 7, 10, 11, 12));
        n.push(ret(&[8]));
        assert_eq!(
            plan_checked_markers(&body(vec![(v(20), Ty::Usize)], n)),
            Some(MfCheckedPlan { chain: vec![(v(2), Ty::Usize), (v(8), Ty::Usize)] }),
            "no chain leaf can read a parameter, so a parameter alone is not a marker hazard",
        );
    }

    /// And the half the trust-ir cannot answer: a parameter whose pattern is NOT a simple binding
    /// mints a named binding local with its own marker pair. Measured: `ck_c3_pat_ref_mode`
    /// (`fn f(ref _a: usize) -> usize { 256 * 1024 * 1024 }`) is WRONG-DIVERGE without this.
    #[test]
    fn the_checked_plan_asks_the_source_about_its_parameters() {
        // The needles are assembled rather than written, so this test's own source is not a
        // second occurrence of what it counts.
        let src = include_str!("to_mir.rs");
        let call = format!("&& {}(tcx, def)", "checked_params_mint_no_local");
        assert_eq!(
            src.matches(call.as_str()).count(),
            1,
            "the checked-chain plan must consult the source parameter question exactly once",
        );
        let defn = format!(
            "fn {}(tcx: TyCtxt<'_>, def: LocalDefId) -> bool {{\n    tcx.{}(def).is_some_and({})\n}}",
            "checked_params_mint_no_local", "hir_maybe_body_owned_by", "hir_params_are_simple_bindings"
        );
        assert_eq!(
            src.matches(defn.as_str()).count(),
            1,
            "and it must be the shared simple-binding predicate, not a second copy of it",
        );
    }

    #[test]
    fn test_plan_a_single_unit_is_refused() {
        let mut n = vec![konst(0, Ty::Usize, 256), konst(1, Ty::Usize, 1024)];
        n.extend(mul_unit(2, 3, Ty::Usize, 0, 1, 4, 5, 6));
        n.push(ret(&[2]));
        assert!(
            plan_checked_markers(&body(vec![], n)).is_none(),
            "one unit has no non-outermost sub-expression, so built mints no temp and the \
             marker-free form this shim already ships is the right answer",
        );
    }

    #[test]
    fn test_plan_a_right_nested_chain_is_refused() {
        // `1024 * (256 * 1024)`: the link is the RIGHT operand, so built's live order is not the
        // reverse of the SSA order and this model would place the pair wrongly.
        let mut n = vec![konst(0, Ty::Usize, 256), konst(1, Ty::Usize, 1024)];
        n.extend(mul_unit(2, 3, Ty::Usize, 0, 1, 4, 5, 6));
        n.push(konst(7, Ty::Usize, 1024));
        n.extend(mul_unit(8, 9, Ty::Usize, 7, 2, 10, 11, 12));
        n.push(ret(&[8]));
        assert!(plan_checked_markers(&body(vec![], n)).is_none());
    }

    #[test]
    fn test_plan_a_trailing_cast_is_refused() {
        // The shape of `env::ext_instance::PRIORITY_BYTES`' tail. The shim writes a cast through a
        // temp (`_t = Cast(..); _0 = copy _t`) where built writes `_0 = move _1 as usize` in ONE
        // assign, so the retirement's canonical position differs. Named in the plan's doc.
        let mut n = vec![konst(0, Ty::U32, 256), konst(1, Ty::U32, 1024)];
        n.extend(mul_unit(2, 3, Ty::U32, 0, 1, 4, 5, 6));
        n.push(konst(7, Ty::U32, 1024));
        n.extend(mul_unit(8, 9, Ty::U32, 2, 7, 10, 11, 12));
        n.push(node(
            Inst::Cast { op: CastOp::ZExt, src_ty: Ty::U32, dst_ty: Ty::Usize, operand: v(8) },
            Some(13),
        ));
        n.push(ret(&[13]));
        assert!(plan_checked_markers(&body(vec![], n)).is_none());
    }

    #[test]
    fn test_plan_a_foreign_instruction_is_refused() {
        let mut n = vec![konst(0, Ty::Usize, 256), konst(1, Ty::Usize, 1024)];
        n.extend(mul_unit(2, 3, Ty::Usize, 0, 1, 4, 5, 6));
        n.push(konst(7, Ty::Usize, 1024));
        n.extend(mul_unit(8, 9, Ty::Usize, 2, 7, 10, 11, 12));
        n.push(node(
            Inst::ICmp { op: ICmpOp::Eq, ty: Ty::Usize, lhs: v(8), rhs: v(0) },
            Some(13),
        ));
        n.push(ret(&[8]));
        assert!(
            plan_checked_markers(&body(vec![], n)).is_none(),
            "an instruction outside the two modelled shapes has its own statement shape",
        );
    }

    #[test]
    fn test_plan_a_second_use_of_a_link_is_refused() {
        // `(256 * 1024) * (256 * 1024)` spelled as a CSE: built evaluates and marks the
        // sub-expression twice.
        let mut n = vec![konst(0, Ty::Usize, 256), konst(1, Ty::Usize, 1024)];
        n.extend(mul_unit(2, 3, Ty::Usize, 0, 1, 4, 5, 6));
        n.extend(mul_unit(8, 9, Ty::Usize, 2, 2, 10, 11, 12));
        n.push(ret(&[8]));
        assert!(plan_checked_markers(&body(vec![], n)).is_none());
    }

    #[test]
    fn test_plan_returning_a_non_tail_link_is_refused() {
        let mut n = vec![konst(0, Ty::Usize, 256), konst(1, Ty::Usize, 1024)];
        n.extend(mul_unit(2, 3, Ty::Usize, 0, 1, 4, 5, 6));
        n.push(konst(7, Ty::Usize, 1024));
        n.extend(mul_unit(8, 9, Ty::Usize, 2, 7, 10, 11, 12));
        n.push(ret(&[2]));
        assert!(plan_checked_markers(&body(vec![], n)).is_none());
    }

    #[test]
    fn test_plan_a_bare_binop_chain_stays_with_the_operand_plan() {
        // No `Inst::Overflow` at all — overflow checks off. `plan_operand_marker_temps` owns this
        // body, and this plan must not take it.
        let f = body(
            vec![],
            vec![
                konst(0, Ty::Usize, 256),
                konst(1, Ty::Usize, 1024),
                node(Inst::BinOp { op: BinOp::Mul, ty: Ty::Usize, lhs: v(0), rhs: v(1) }, Some(2)),
                ret(&[2]),
            ],
        );
        assert!(plan_checked_markers(&f).is_none());
    }

    // ---- the sequence model, against a fixture in BUILT's statement shape --------------------

    /// A fixture statement. `A` is an assignment with no bare-local operand (built's
    /// `_t = move (_tup.0)` reads a PROJECTED place, which `rvalue_operand_locals` skips);
    /// `Aop(l)` is an assignment whose operand sequence is exactly `[l]` (built's
    /// `_tup = MulWithOverflow(move _t, const)`, whose second operand is a folded constant and
    /// takes no position). `L`/`D` are the markers.
    #[derive(Clone, Copy)]
    enum St {
        A,
        Aop(u32),
        L(u32),
        D(u32),
    }

    fn fixture(blocks: &[&[St]]) -> IndexVec<BasicBlock, BasicBlockData<'static>> {
        let si = SourceInfo::outermost(DUMMY_SP);
        let mut out = IndexVec::new();
        for blk in blocks {
            let stmts: Vec<Statement<'static>> = blk
                .iter()
                .map(|s| {
                    let kind = match s {
                        St::A => StatementKind::Assign(Box::new((
                            Place::from(Local::from_u32(0)),
                            Rvalue::Discriminant(Place::from(Local::from_u32(90))),
                        ))),
                        St::Aop(l) => StatementKind::Assign(Box::new((
                            Place::from(Local::from_u32(0)),
                            Rvalue::UnaryOp(
                                UnOp::Not,
                                Operand::Move(Place::from(Local::from_u32(*l))),
                            ),
                        ))),
                        St::L(l) => marker_kind(Local::from_u32(*l), true),
                        St::D(l) => marker_kind(Local::from_u32(*l), false),
                    };
                    Statement::new(si, kind)
                })
                .collect();
            out.push(BasicBlockData::new_stmts(stmts, None, false));
        }
        out
    }

    fn seen(blocks: &[&[St]], ty: Ty) -> MfSeq {
        observe_with(&fixture(blocks), |_| ir_ty_token(&ty))
            .expect("the fixture is inside the marker channel's fragment")
    }

    /// The two-unit chain, end to end. Built's MIR for `const A: usize = 256 * 1024 * 1024`,
    /// `-Zdump-mir=all`:
    ///
    /// ```text
    /// bb0: { StorageLive(_1); _2 = MulWithOverflow(const 256, const 1024); assert -> bb1; }
    /// bb1: { _1 = move (_2.0); _3 = MulWithOverflow(move _1, const 1024); assert -> bb2; }
    /// bb2: { _0 = move (_3.0); StorageDead(_1); return; }
    /// ```
    #[test]
    fn test_predict_two_unit_chain_matches_builts_shape() {
        let plan = plan_checked_markers(&two_unit()).expect("in class");
        let got = predict_checked(&two_unit(), &plan).expect("modelled");
        let want = seen(
            &[
                &[St::L(1), St::A],
                &[St::A, St::Aop(1)],
                &[St::A, St::D(1)],
            ],
            Ty::Usize,
        );
        assert_eq!(got, want, "first difference: {}", got.first_diff(&want));
    }

    /// The three-unit chain. The LIVES are outermost-first — the reverse of the SSA order — which
    /// is what fixes the alpha numbering (`s0` is the OUTER temp) and is the one component a
    /// count-based law could not see.
    #[test]
    fn test_predict_three_unit_chain_lives_outermost_first() {
        let plan = plan_checked_markers(&three_unit()).expect("in class");
        let got = predict_checked(&three_unit(), &plan).expect("modelled");
        let want = seen(
            &[
                &[St::L(1), St::L(2), St::A],
                &[St::A, St::Aop(2)],
                &[St::A, St::D(2), St::Aop(1)],
                &[St::A, St::D(1)],
            ],
            Ty::U64,
        );
        assert_eq!(got, want, "first difference: {}", got.first_diff(&want));
    }

    /// The order is load-bearing, not incidental: the INNERMOST-first spelling — which is the
    /// order the shim's own linear instruction walk would produce if it opened each temp where the
    /// instruction sits — is a DIFFERENT sequence.
    #[test]
    fn test_predict_innermost_first_lives_are_a_different_sequence() {
        let plan = plan_checked_markers(&three_unit()).expect("in class");
        let got = predict_checked(&three_unit(), &plan).expect("modelled");
        let swapped = seen(
            &[
                &[St::L(2), St::L(1), St::A],
                &[St::A, St::Aop(2)],
                &[St::A, St::D(2), St::Aop(1)],
                &[St::A, St::D(1)],
            ],
            Ty::U64,
        );
        assert_ne!(got, swapped, "a swapped live order must not compare equal");
    }

    /// A plan whose chain is not the body's chain fails the body CLOSED rather than placing a pair
    /// against instructions that are not there.
    #[test]
    fn test_predict_refuses_a_plan_from_another_body() {
        let plan = plan_checked_markers(&three_unit()).expect("in class");
        assert!(predict_checked(&two_unit(), &plan).is_err());
    }
}

#[cfg(test)]
mod agg_plan_tests {
    //! Trust (defect close, 2026-08-13): the SINGLE-BLOCK marker plan
    //! ([`plan_operand_marker_temps`] and its aggregate half [`agg_field_order_ok`]), as pure
    //! functions over trust-ir.
    //!
    //! Each of the three shapes the lane N adversarial review recorded as ADMITTED-AND-WRONG gets
    //! a pair: the shape itself, which must be refused, and a MINIMALLY-DIFFERENT sibling which
    //! must still be admitted. The sibling is what makes the refusal attributable — a `None` on
    //! its own could always be some unrelated condition firing.
    use std::collections::HashSet;

    use trust_ir::{
        BinOp, BlockId, CastOp, Constant, FuncId, FuncTyId, Function, ICmpOp, Inst, InstrNode,
        StructId, Ty, ValueId,
    };

    use super::{agg_field_order_ok, plan_operand_marker_temps};

    fn b(i: u32) -> BlockId {
        BlockId::new(i)
    }
    fn v(i: u32) -> ValueId {
        ValueId::new(i)
    }
    fn node(inst: Inst, result: Option<u32>) -> InstrNode {
        let n = InstrNode::new(inst);
        match result {
            Some(r) => n.with_result(v(r)),
            None => n,
        }
    }
    fn binop(r: u32, op: BinOp, ty: Ty, lhs: u32, rhs: u32) -> InstrNode {
        node(Inst::BinOp { op, ty, lhs: v(lhs), rhs: v(rhs) }, Some(r))
    }
    fn load(r: u32, ty: Ty, ptr: u32) -> InstrNode {
        node(Inst::Load { ty, ptr: v(ptr), volatile: false, align: None }, Some(r))
    }
    fn cast(r: u32, src: Ty, dst: Ty, operand: u32) -> InstrNode {
        node(
            Inst::Cast { op: CastOp::ZExt, src_ty: src, dst_ty: dst, operand: v(operand) },
            Some(r),
        )
    }
    fn extract(r: u32, ty: Ty, agg: u32, field: u32) -> InstrNode {
        node(Inst::ExtractField { ty, aggregate: v(agg), field }, Some(r))
    }
    fn seed(r: u32, sid: u32, n: usize) -> InstrNode {
        node(
            Inst::Const {
                ty: Ty::Struct(StructId(sid)),
                value: Constant::Aggregate(vec![Constant::Int(0); n]),
            },
            Some(r),
        )
    }
    fn insert(r: u32, sid: u32, agg: u32, field: u32, value: u32) -> InstrNode {
        node(
            Inst::InsertField {
                ty: Ty::Struct(StructId(sid)),
                aggregate: v(agg),
                field,
                value: v(value),
            },
            Some(r),
        )
    }
    fn ret(values: &[u32]) -> InstrNode {
        node(Inst::Return { values: values.iter().map(|a| v(*a)).collect() }, None)
    }

    fn body(params: Vec<(ValueId, Ty)>, nodes: Vec<InstrNode>) -> Function {
        let mut f = Function::new(FuncId::new(0), "probe", FuncTyId::new(0), b(0));
        let mut e = trust_ir::Block::new(b(0));
        e.params = params;
        e.body = nodes;
        f.blocks = vec![e];
        f
    }

    fn u8p(ids: &[u32]) -> Vec<(ValueId, Ty)> {
        ids.iter().map(|i| (v(*i), Ty::U8)).collect()
    }

    /// The producer erases `fn borrow(s: &Slot) -> &u64 { &s.h }` to the same one-block
    /// pointer-return shape as a bare identity. The trust-ir operand plan therefore admits an
    /// EMPTY plan independently of the source-side interior-borrow plan. This is why
    /// `source_form_marker_plan_available` must explicitly exclude the borrow plan rather than
    /// relying on the instruction plan to notice an overlap.
    #[test]
    fn a_bare_pointer_return_has_an_empty_operand_plan() {
        let f = body(vec![(v(0), Ty::Ptr)], vec![ret(&[0])]);
        assert_eq!(plan_operand_marker_temps(&f), Some(HashSet::new()));
    }

    // ---- DEFECT 2 (a): a NESTED field expression -------------------------------------------

    /// `W8((a & b) | c)` (probe `nested_field`). Built's `as_operand`→`as_temp` opens the OUTER
    /// (`|`) temp first and the inner (`&`) one second; this shim's linear instruction walk
    /// reaches `&` first. Measured refusal by the oracle:
    /// `line 2: built mk b0.0:live s2:u8 vs derived mk b0.1:live s2:u8`. Refused by the plan now.
    #[test]
    fn a_nested_field_expression_is_refused() {
        let f = body(
            u8p(&[0, 1, 2]),
            vec![
                binop(3, BinOp::And, Ty::U8, 0, 1),
                binop(4, BinOp::Or, Ty::U8, 3, 2),
                seed(5, 7, 1),
                insert(6, 7, 5, 0, 4),
                ret(&[6]),
            ],
        );
        assert!(
            plan_operand_marker_temps(&f).is_none(),
            "the OUTER field rvalue is marked and takes the MARKED inner one — built opens the \
             outer temp first, the linear walk opens the inner one first",
        );
    }

    /// ...and it is ordering rule (1) doing it, not the aggregate machinery: FLATTEN the field to
    /// one level (`W8(a & b)`) and the same aggregate, the same seed and the same field count are
    /// admitted, with the field rvalue marked.
    #[test]
    fn a_flat_computed_field_stays_admitted() {
        let f = body(
            u8p(&[0, 1]),
            vec![
                binop(3, BinOp::And, Ty::U8, 0, 1),
                seed(5, 7, 1),
                insert(6, 7, 5, 0, 3),
                ret(&[6]),
            ],
        );
        assert_eq!(
            plan_operand_marker_temps(&f),
            Some(HashSet::from([v(3)])),
            "one level of field rvalue is exactly what lane L admits",
        );
    }

    /// The NON-aggregate twin the record did not name: `((a & b) | c) == 0`. Same defect, no
    /// aggregate anywhere — which is why the fix belongs in `plan_operand_marker_temps` rather
    /// than in `agg_field_order_ok`.
    #[test]
    fn a_nested_rvalue_with_no_aggregate_is_refused() {
        let f = body(
            u8p(&[0, 1, 2]),
            vec![
                binop(3, BinOp::And, Ty::U8, 0, 1),
                binop(4, BinOp::Or, Ty::U8, 3, 2),
                node(Inst::Const { ty: Ty::U8, value: Constant::Int(0) }, Some(5)),
                node(Inst::ICmp { op: ICmpOp::Eq, ty: Ty::U8, lhs: v(4), rhs: v(5) }, Some(6)),
                ret(&[6]),
            ],
        );
        assert!(plan_operand_marker_temps(&f).is_none());
    }

    // ---- DEFECT 2 (b): the same shape reached through `Inst::Load` --------------------------

    /// `Inner(*p as u32)` (probe `mk_cast_load`): built lives the u32 CAST temp first, this shim
    /// the u8 LOAD temp first.
    #[test]
    fn a_cast_of_a_load_field_is_refused() {
        let f = body(
            vec![(v(0), Ty::Ptr)],
            vec![
                load(1, Ty::U8, 0),
                cast(2, Ty::U8, Ty::U32, 1),
                seed(3, 7, 1),
                insert(4, 7, 3, 0, 2),
                ret(&[4]),
            ],
        );
        assert!(plan_operand_marker_temps(&f).is_none());
    }

    /// ...for the NESTING, not for the load: `Inner(*p)` keeps its marked load temp.
    #[test]
    fn a_bare_load_field_stays_admitted() {
        let f = body(
            vec![(v(0), Ty::Ptr)],
            vec![load(1, Ty::U32, 0), seed(3, 7, 1), insert(4, 7, 3, 0, 1), ret(&[4])],
        );
        assert_eq!(plan_operand_marker_temps(&f), Some(HashSet::from([v(1)])));
    }

    // ---- DEFECT 2 (c), NARROWED: FUNCTIONAL RECORD UPDATE ------------------------------------

    /// `P3 { a: x, b: p.b, c: p.c }` — the WRITTEN-OUT twin of `P3 { a: x, ..p }`, which lowers to
    /// the same instructions. It used to be refused here by the FRU-signature rule ("no field `i`
    /// fed by a read of field `i`"), and that rule is gone: the ambiguity is a property of the
    /// SOURCE FORM, and [`super::source_form_admits`] answers it by refusing
    /// `StructTailExpr::Base`. The instruction-level plan admits both of these now, and both are
    /// CORRECT for the written-out spelling that reaches it.
    ///
    /// `permuted` swaps the two base reads' field indices — `Pair`-style crossing, which no FRU
    /// spelling can produce. That is the only difference between the two bodies, and after the
    /// narrowing it makes no difference to this plan, which is the point.
    fn fru_shaped(permuted: bool) -> Function {
        let (f1, f2) = if permuted { (2, 1) } else { (1, 2) };
        body(
            vec![(v(0), Ty::Struct(StructId(7))), (v(1), Ty::U32)],
            vec![
                extract(2, Ty::U32, 0, f1),
                extract(3, Ty::U32, 0, f2),
                seed(4, 7, 3),
                insert(5, 7, 4, 0, 1),
                insert(6, 7, 5, 1, 2),
                insert(7, 7, 6, 2, 3),
                ret(&[7]),
            ],
        )
    }

    #[test]
    fn a_field_read_from_its_own_index_is_admitted_again() {
        let f = fru_shaped(false);
        assert!(
            agg_field_order_ok(&f.blocks[0].params, &f.blocks[0].body, &[v(7)]),
            "the FRU-signature rule refused this written-out body for an ambiguity only the \
             SOURCE form carries; the source-form gate owns that question now",
        );
        assert!(plan_operand_marker_temps(&f).is_some());
    }

    #[test]
    fn crossed_field_reads_stay_admitted() {
        let f = fru_shaped(true);
        assert!(
            agg_field_order_ok(&f.blocks[0].params, &f.blocks[0].body, &[v(7)]),
            "`Pair {{ l: p.r, r: p.l }}` was admitted before the narrowing and still is",
        );
        assert!(plan_operand_marker_temps(&f).is_some());
    }

    /// THE FIELD-POSITION RULE IS RETIRED, and this is the body that used to be refused by it:
    /// two field READS whose instructions are emitted out of FIELD order (`ef(p,1)` — field 0's
    /// value — before `ef(p,0)`, field 1's), which happens exactly when the source wrote them out
    /// of DECLARATION order.
    ///
    /// The rule was a proxy for that source order and nothing else: the producer lowers field
    /// values in source order, does not CSE, and gives a bare block param no position at all
    /// (measured — see the retirement note in `agg_field_order_ok`). `source_form_admits` now
    /// reads the written order directly and, unlike a position comparison, can ask whether the
    /// permutation is OBSERVABLE in the marker channel. So this plan admits the shape and the
    /// source form decides it: with `u32` reads, as here, both sides mint three identically-typed
    /// pairs at the same indices and the sequences are equal (`f25_rotate_written_cba`); with
    /// mixed widths the source-form clause refuses (`w34_w2_out_of_order`).
    #[test]
    fn field_reads_emitted_out_of_field_order_are_no_longer_refused_here() {
        let f = body(
            vec![(v(0), Ty::Struct(StructId(7)))],
            vec![
                extract(1, Ty::U32, 0, 1),
                extract(2, Ty::U32, 0, 0),
                seed(3, 7, 2),
                insert(4, 7, 3, 0, 2),
                insert(5, 7, 4, 1, 1),
                ret(&[5]),
            ],
        );
        assert!(
            agg_field_order_ok(&f.blocks[0].params, &f.blocks[0].body, &[v(5)]),
            "the written field order is a question about the SOURCE; the instruction positions \
             only ever proxied for it, and the proxy's measured residue was excess",
        );
        assert!(plan_operand_marker_temps(&f).is_some());
    }

    /// ...and the minimally-different sibling: the SAME two reads, emitted in field order. It was
    /// admitted before the retirement and still is — the retirement moved one body, not two.
    #[test]
    fn field_reads_emitted_in_field_order_stay_admitted() {
        let f = body(
            vec![(v(0), Ty::Struct(StructId(7)))],
            vec![
                extract(1, Ty::U32, 0, 0),
                extract(2, Ty::U32, 0, 1),
                seed(3, 7, 2),
                insert(4, 7, 3, 0, 1),
                insert(5, 7, 4, 1, 2),
                ret(&[5]),
            ],
        );
        assert!(agg_field_order_ok(&f.blocks[0].params, &f.blocks[0].body, &[v(5)]));
        assert!(plan_operand_marker_temps(&f).is_some());
    }

    /// The guard that is NOT a proxy and therefore stays: an INSTRUCTION-valued field after a
    /// PLACE-valued one (`Inr { x: c, y: a & b }`), in DECLARATION order, where no source-form
    /// question arises at all. Built opens field 0's temp first and only then builds the `&`;
    /// this shim reaches the `&` node first. Its field-order twin `Inr { x: a & b, y: c }` is
    /// admitted, and that pair is the witness.
    #[test]
    fn an_instruction_field_after_a_place_field_is_still_refused() {
        let f = body(
            vec![(v(0), Ty::U32), (v(1), Ty::U32), (v(2), Ty::U32)],
            vec![
                binop(3, BinOp::And, Ty::U32, 0, 1),
                seed(4, 7, 2),
                insert(5, 7, 4, 0, 2),
                insert(6, 7, 5, 1, 3),
                ret(&[6]),
            ],
        );
        assert!(
            !agg_field_order_ok(&f.blocks[0].params, &f.blocks[0].body, &[v(6)]),
            "field 0 is a place and field 1 computes: built mints field 0's temp first",
        );
        assert!(plan_operand_marker_temps(&f).is_none());
    }

    #[test]
    fn a_place_field_after_an_instruction_field_stays_admitted() {
        let f = body(
            vec![(v(0), Ty::U32), (v(1), Ty::U32), (v(2), Ty::U32)],
            vec![
                binop(3, BinOp::And, Ty::U32, 0, 1),
                seed(4, 7, 2),
                insert(5, 7, 4, 0, 3),
                insert(6, 7, 5, 1, 2),
                ret(&[6]),
            ],
        );
        assert!(agg_field_order_ok(&f.blocks[0].params, &f.blocks[0].body, &[v(6)]));
        assert!(plan_operand_marker_temps(&f).is_some());
    }

    // ---- ORDERING RULE (2): a MARKED operand may not be preceded by a PLACE operand ----------

    /// `a == (b & c)` — wave-MF's "KNOWN BOUNDARY", now a refusal. Built mints `a`'s operand temp
    /// FIRST (`StorageLive(_4); _4 = copy _1`) and only then opens the `&` sub-expression's temp;
    /// the shim's linear walk reaches the `&` node first. Oracle verdict in the control:
    /// `line 1: built mk b0.1:live s1:u8 vs derived mk b0.0:live s1:u8`.
    #[test]
    fn a_marked_operand_after_a_place_operand_is_refused() {
        let f = body(
            u8p(&[0, 1, 2]),
            vec![
                binop(3, BinOp::And, Ty::U8, 1, 2),
                node(Inst::ICmp { op: ICmpOp::Eq, ty: Ty::U8, lhs: v(0), rhs: v(3) }, Some(4)),
                ret(&[4]),
            ],
        );
        assert!(plan_operand_marker_temps(&f).is_none());
    }

    /// THE TRAP, and the reason this rule may not simply count "non-marked" operands the way
    /// `plan_branch_markers`' rule (2) does: `0 == (b & c)`. A CONSTANT operand folds in place,
    /// mints no temp, and constrains nothing — this body is `markers_exact: true` in the control
    /// and must keep flipping. The ONLY difference from the body above is that operand 0 is an
    /// `Inst::Const` result instead of a block param.
    #[test]
    fn a_marked_operand_after_a_constant_operand_stays_admitted() {
        let f = body(
            u8p(&[1, 2]),
            vec![
                binop(3, BinOp::And, Ty::U8, 1, 2),
                node(Inst::Const { ty: Ty::U8, value: Constant::Int(0) }, Some(0)),
                node(Inst::ICmp { op: ICmpOp::Eq, ty: Ty::U8, lhs: v(0), rhs: v(3) }, Some(4)),
                ret(&[4]),
            ],
        );
        assert_eq!(
            plan_operand_marker_temps(&f),
            Some(HashSet::from([v(3)])),
            "a constant operand mints no temp, so it cannot precede anything",
        );
    }

    /// The LEFT-nested twin: the marked operand is leftmost and the place operand follows it.
    /// Built opens the `&` temp first, exactly like the shim. ADMITTED.
    #[test]
    fn a_place_operand_after_a_marked_operand_stays_admitted() {
        let f = body(
            u8p(&[0, 1, 2]),
            vec![
                binop(3, BinOp::And, Ty::U8, 0, 1),
                node(Inst::ICmp { op: ICmpOp::Eq, ty: Ty::U8, lhs: v(3), rhs: v(2) }, Some(4)),
                ret(&[4]),
            ],
        );
        assert_eq!(plan_operand_marker_temps(&f), Some(HashSet::from([v(3)])));
    }

    /// TWO marked operands and no place operand: built opens each sub-expression's temp in operand
    /// order and the linear walk reaches them in the same order. Rule (2) must not refuse this —
    /// a marked operand preceded by ANOTHER MARKED one is fine, only a PLACE is not.
    #[test]
    fn two_marked_operands_stay_admitted() {
        let f = body(
            u8p(&[0, 1, 2, 5]),
            vec![
                binop(3, BinOp::And, Ty::U8, 0, 1),
                binop(4, BinOp::And, Ty::U8, 2, 5),
                node(Inst::ICmp { op: ICmpOp::Eq, ty: Ty::U8, lhs: v(3), rhs: v(4) }, Some(6)),
                ret(&[6]),
            ],
        );
        assert_eq!(plan_operand_marker_temps(&f), Some(HashSet::from([v(3), v(4)])));
    }

    /// Rule (2) through `Inst::Load`, and through an `ExtractField` place rather than a param:
    /// `self.0 == *p`.
    #[test]
    fn a_marked_load_after_a_field_read_is_refused() {
        let f = body(
            vec![(v(0), Ty::Struct(StructId(7))), (v(1), Ty::Ptr)],
            vec![
                extract(2, Ty::U64, 0, 0),
                load(3, Ty::U64, 1),
                node(Inst::ICmp { op: ICmpOp::Eq, ty: Ty::U64, lhs: v(2), rhs: v(3) }, Some(4)),
                ret(&[4]),
            ],
        );
        assert!(plan_operand_marker_temps(&f).is_none());
    }

    // ---- DEFECT 4: `seed_overwritten_ty` seeds `Ty::Ptr` as `Constant::Int(0)` --------------

    /// `RefPair { p: &u8, n: usize }` (probe `mk_refpair`). The producer's `seed_overwritten_ty`
    /// spells the `Ty::Ptr` lane as `Constant::Int(0)` — the null pointer — so the seed's element
    /// kinds say "two scalars" about a struct with a REFERENCE field. The two bodies below carry
    /// a BYTE-IDENTICAL seed (`Aggregate([Int(0), Int(0)])`) and byte-identical instructions;
    /// only the declared type of field 0's value differs.
    fn ref_pair(field0: Ty) -> Function {
        body(
            vec![(v(0), field0), (v(1), Ty::Usize)],
            vec![seed(2, 7, 2), insert(3, 7, 2, 0, 0), insert(4, 7, 3, 1, 1), ret(&[4])],
        )
    }

    #[test]
    fn a_pointer_typed_field_is_refused_despite_a_scalar_looking_seed() {
        let f = ref_pair(Ty::Ptr);
        assert!(
            !agg_field_order_ok(&f.blocks[0].params, &f.blocks[0].body, &[v(4)]),
            "the scalar wall must read the FIELD'S TYPE; the seed says `Int(0)` here and is \
             lying about a `&u8`",
        );
        assert!(plan_operand_marker_temps(&f).is_none());
    }

    #[test]
    fn the_same_seed_with_a_scalar_field_stays_admitted() {
        let f = ref_pair(Ty::Usize);
        assert!(
            agg_field_order_ok(&f.blocks[0].params, &f.blocks[0].body, &[v(4)]),
            "identical seed, identical instructions — so the refusal above is the TYPE and \
             nothing else",
        );
        assert!(plan_operand_marker_temps(&f).is_some());
    }
}

#[cfg(test)]
mod arm_dead_split_tests {
    //! Trust (defect close, 2026-08-13): `-Ztrust-sat-perturb=marker-arm` must be MULTISET-
    //! PRESERVING, or it cannot witness the property its docstring claims — that `markers_exact`
    //! compares the two arms SEPARATELY rather than comparing one whole-body multiset. It used to
    //! DROP a retirement, which changes the multiset and therefore predicts the same refusal
    //! under both hypotheses (measured: byte-identical to `marker-drop` on 14 of 14 bodies).
    use rustc_middle::mir::Local;

    use super::mf_split_arm_deads;

    fn locals(ids: &[u32]) -> Vec<Local> {
        ids.iter().map(|i| Local::from_u32(*i)).collect()
    }

    fn sorted(a: &[Local], b: &[Local]) -> Vec<u32> {
        let mut all: Vec<u32> = a.iter().chain(b).map(|l| l.as_u32()).collect();
        all.sort_unstable();
        all
    }

    #[test]
    fn unperturbed_both_arms_retire_the_same_list() {
        let (t, e, applied) = mf_split_arm_deads(locals(&[5, 4, 3]), false);
        assert_eq!(t, locals(&[5, 4, 3]));
        assert_eq!(e, locals(&[5, 4, 3]));
        assert!(!applied);
    }

    /// THE DISCRIMINATION. The perturbed body retires exactly the same BAG of locals as the
    /// unperturbed one — so a whole-body-multiset comparator cannot see this class at all — while
    /// the two arms' lists differ, which is what `canon_markers` compares.
    #[test]
    fn perturbed_preserves_the_whole_body_multiset_and_moves_one_arm_assignment() {
        let order = locals(&[5, 4, 3]);
        let (bt, be, _) = mf_split_arm_deads(order.clone(), false);
        let (pt, pe, applied) = mf_split_arm_deads(order, true);
        assert!(applied);
        assert_eq!(
            sorted(&bt, &be),
            sorted(&pt, &pe),
            "the perturbation must MOVE a retirement, never delete one — a deletion changes the \
             multiset and is then indistinguishable from `marker-drop`",
        );
        assert_ne!(pt, pe, "the two arms must retire DIFFERENT lists");
        assert_eq!(pt, locals(&[5, 4]));
        assert_eq!(pe, locals(&[5, 4, 3, 3]), "the else arm — walked first — gains the extra");
    }

    /// And it is a strictly different observable from `marker-drop`, which would leave the body
    /// one retirement short.
    #[test]
    fn perturbed_is_not_one_marker_shorter() {
        let order = locals(&[9, 8]);
        let (bt, be, _) = mf_split_arm_deads(order.clone(), false);
        let (pt, pe, _) = mf_split_arm_deads(order, true);
        assert_eq!(bt.len() + be.len(), pt.len() + pe.len());
    }

    #[test]
    fn nothing_to_move_is_not_a_counted_application() {
        let (t, e, applied) = mf_split_arm_deads(Vec::new(), true);
        assert!(t.is_empty() && e.is_empty());
        assert!(!applied, "an empty list must not inflate `sat_perturb_count`");
    }
}

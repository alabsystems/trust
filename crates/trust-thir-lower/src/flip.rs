//! Trust: the flip (P1 item 5) — derive the codegen-path `mir::Body` from trust-ir.
//!
//! [`derive_flip_body`] is called by `rustc_mir_transform::trust_ir_flip::try_flip` from inside
//! `inner_optimized_mir`, for every local body, right after the normal (built) body has been
//! stolen from `mir_drops_elaborated_and_const_checked`. It:
//!
//! 1. [`crate::flip_registry::take`]s the green `trust_ir::Module` recorded at the `mir_built`
//!    hook (recorded only when the derived-vs-built differential verdict was `DerivedAgreed`
//!    and every session gate held). No entry ⇒ [`FlipAttempt::NotCandidate`] — the silent,
//!    overwhelmingly common case.
//! 2. Runs fail-closed gates (each miss is a LOUD [`FlipAttempt::Rejected`], logged by the
//!    caller as a fallback):
//!    * **def-level** — not a const context (CTFE stays on built MIR wholesale in slice 1),
//!      not a coroutine, and no first-class loop clauses whose identifiers still
//!      require MIR source-place provenance absent from TrustIr.
//!    * **const-trap (lint-hazard)** — the flip pipeline re-runs `KnownPanicsLint` on the
//!      derived body (it is part of `run_analysis_to_runtime_passes`, which must be replayed
//!      1:1 for pass parity). On a body where a trap is statically decidable the lint would
//!      fire a SECOND time, at the shim's coarser span, and an `#[allow]` scoped to an inner
//!      statement would not cover it — a user-visible divergence. So any potentially trapping
//!      instruction (`Overflow`, shifts, `Neg`, plain `Add/Sub/Mul`) whose deciding operands
//!      are all `Inst::Const`-defined rejects the flip. (Constants that reach a trap only
//!      through a join ride block params, which lower to multi-assigned MIR locals that
//!      `KnownPanicsLint` refuses to propagate — on the built body identically — so the
//!      straight-line check is the complete hazard set.)
//!    * **structural** — the derived body is re-verified instruction by instruction against
//!      the slice-1 fragment: `Assign` of `Use`/`BinaryOp`/`UnaryOp` into scalar (or
//!      checked-pair tuple) locals, `Goto`/`SwitchInt`/`Assert(Overflow)`/`Return`/
//!      `Unreachable` terminators — plus (wave 6) DIRECT `Call`s in exactly the shim's
//!      emitted shape: zero-generic `FnDef` constant func, in-fragment args, bare-local
//!      destination, `Some` return target, `UnwindAction::Continue`, no cleanup blocks
//!      anywhere — in-range targets, drop-free / coroutine-free by allow-list. Borrow-free
//!      too, EXCEPT the one wave-29 interior-borrow-return shape `_0 = &((*_p).field)` (a
//!      SHARED borrow of an arg-ref struct field into RETURN_PLACE; `PromoteTemps` finds zero
//!      candidates since it borrows through a runtime param, not a const). This (not
//!      `catch_unwind`) is the real protection: the admitted
//!      fragment is total for every pass between `Built` and codegen, including the
//!      mandatory `Runtime(Optimized)` validation — direct-call bodies are what those
//!      passes chew through on every real compilation (totality citations at the gate's
//!      `Call` arm).
//!    * **ABI-visible types** — `_0..=arg_count` local types must be EXACTLY equal between
//!      derived and built. Since v25 B1 the producer carries `isize`/`usize`/`char`
//!      first-class and the shim denotes them directly (`to_mir::scalar_rustc_ty` — the
//!      former `PtrSpell` respell is retired), so honest signatures pass on their own
//!      spelling. The gate itself stays EXACT equality — never a
//!      layout argument — and still refuses mixed-anchor bodies (`fn(i64) -> isize`), where
//!      the respell fails closed to the collapse.
//! 3. **Stitches assert spans** from the built sibling: the derived body's `SourceInfo` is
//!    fn-level (trust-ir carries no spans yet), but an `Assert`'s span is user-visible — it
//!    becomes the panic `Location` in the emitted object. Both bodies' asserts are collected
//!    in the same canonical DFS preorder the differential used (switch targets in listed
//!    order then otherwise, assert success edge, goto target); `DerivedAgreed` proved the
//!    sequences correspond 1:1, and none of the passes between `Built` and
//!    `Runtime(PostCleanup)` reorder, add, or remove asserts. Kind + polarity are re-checked
//!    pairwise; any mismatch rejects the flip. Only the SPAN is copied — scopes index the
//!    derived body's own scope tree.
//!
//! The returned body is `MirPhase::Built`; the caller replays the normal pass pipeline over it
//! (see `rustc_mir_transform::trust_ir_flip`). Borrowck already ran — on the built sibling,
//! exactly as docs/DESIGN-P1-ir-inversion.md section 3 prescribes.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com> | Copyright 2026 | License: Apache-2.0

use std::collections::{HashMap, HashSet};

use rustc_middle::mir::visit::{MutatingUseContext, PlaceContext, Visitor};
use rustc_middle::mir::{
    AggregateKind, AssertKind, BasicBlock, Body, BorrowKind, CastKind, Local, Location, Operand,
    Place, ProjectionElem, RETURN_PLACE, Rvalue, START_BLOCK, Statement, StatementKind,
    TerminatorKind, UnwindAction,
};
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use rustc_span::Span;
use rustc_span::def_id::LocalDefId;
use trust_ir::{BinOp, Constant, FuncId, Inst, Module, UnOp, ValueId};

use crate::{flip_registry, to_mir};

/// Outcome of one flip attempt (see module docs).
pub enum FlipAttempt<'tcx> {
    /// No green Module recorded for this def — the normal path, silently.
    NotCandidate,
    /// A green Module existed but a fail-closed gate rejected it. The caller logs this loudly
    /// (it is a fallback event) and compiles the built body.
    Rejected { reason: String },
    /// The derived body, `MirPhase::Built`, gates passed, assert spans stitched.
    /// `asserts` is the number of (span-stitched) assert terminators, for observability.
    /// `lineage` is the record-time lineage digest of the (mini-module, callee ledger)
    /// this body was derived from ([`crate::lineage`]), RE-DERIVED and checked equal
    /// against the taken payload before this variant is constructed — the flip event logs
    /// it so the selected body can be matched, by digest equality, to the registry object
    /// and the published artifact row.
    Derived { body: Body<'tcx>, asserts: usize, lineage: trust_ir::ProofDigest },
}

fn rejected<'tcx>(reason: impl Into<String>) -> FlipAttempt<'tcx> {
    FlipAttempt::Rejected { reason: reason.into() }
}

/// Trust: attempt to derive the codegen-path body for `def` from its green trust-ir Module.
/// `normal` is the built body `inner_optimized_mir` just stole (post
/// `mir_drops_elaborated_and_const_checked`, post `remap_mir_for_const_eval_select`) — used
/// only as the metadata sibling (assert spans, ABI-visible type check), never for semantics.
pub fn derive_flip_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    normal: &Body<'tcx>,
) -> FlipAttempt<'tcx> {
    // Trust (B, final): take from the registry, or decline. An empty entry is the NORMAL state
    // for every body the hook did not green-record — it is not an incremental hole. The hole B
    // was written for was DISPROVED (`mir_built` carries no `cache_on_disk`, so it is never
    // replayed from disk — any process that demands it re-executes it, repopulating the
    // registry), and the "re-lower from THIR" recovery arm that briefly lived here was WORSE
    // than unnecessary: at this seam (`optimized_mir`) THIR has already been STOLEN by
    // unsafeck, so the arm ICE'd on `thir.borrow()` for every non-green body — 41 flag-induced
    // ICEs on a 600-file scorecard, zero on the five-body probe whose bodies were all
    // green-recorded. The probe could not see it; the scorecard could. Recorded here so the
    // arm does not come back: THIR IS NOT AVAILABLE AT FLIP TIME.
    let Some(flip_registry::GreenBody { module, callees, lineage }) = flip_registry::take(tcx, def)
    else {
        return FlipAttempt::NotCandidate;
    };

    // Trust (L1, artifact-lineage attestation): RE-DERIVE the lineage digest from the taken
    // (module, ledger) and require it to equal the value minted at `record_green`. The
    // registry is in-process Session state, so this is not a tamper check — it is the
    // standing obligation that the digest the flip event publishes actually describes the
    // bytes the flip is about to compile. A future producer that mutates a registry entry
    // between record and take, or a `GreenBody` minted by some other path with a digest that
    // does not match its own payload, fails CLOSED here (falls back to built MIR) instead of
    // emitting an attestation for an object that no longer exists. Cost is one module
    // serialization per FLIPPED body — the small set, not every lowered body.
    match crate::lineage::body_lineage_digest(&module, &callees) {
        Ok(rederived) if rederived == lineage => {}
        Ok(rederived) => {
            return rejected(format!(
                "lineage digest mismatch: registry entry carries {lineage}, its own \
                 (module, callee ledger) digests to {rederived}"
            ));
        }
        Err(error) => {
            return rejected(format!("lineage digest could not be re-derived at flip: {error}"));
        }
    }

    // ---- def-level gates ----
    // `record_green` applies this gate before inserting. Re-check after taking
    // as defense in depth so a future registry producer cannot bypass the
    // source-place boundary merely by reusing this derivation entry point.
    if !flip_registry::source_place_provenance_allows_flip(tcx, def) {
        return rejected(
            "first-class loop contract requires source-place provenance not carried by TrustIr",
        );
    }
    // Trust (CTFE flip lane): const/associated-const ITEMS reach this gate ONLY via the ctfe seam
    // (`trust_ir_flip::try_flip_ctfe`) and ARE admitted — their value is const-eval-interpreted from
    // MIR re-derived from the trust-ir Module. Const-qualification already ran on the BUILT sibling
    // (`mir_const_qualif` reads `mir_built`, never the derived body), so reconstruction cannot
    // produce a body that "fails const-checking"; and the drop-free scalar fragment keeps every
    // replayed const-context pass (`KnownPanicsLint`, `CheckLiveDrops`) inert.
    //
    // Trust (wave-I, const-fn codegen flip): a CONST FN (`Some(ConstFn)`) reaches this gate ONLY via
    // the CODEGEN seam (`try_flip`/`inner_optimized_mir`) — `try_flip_ctfe` pre-gates the ctfe seam
    // to `Const|Static` ITEMS and returns `None` for a const fn, so its `mir_for_ctfe` (const-eval)
    // body stays BUILT and its registry entry is never consumed there. On the codegen seam a const
    // fn is an ORDINARY runtime fn — it flips exactly like a non-const fn under the same fragment
    // gates below (incl. `const_trap_gate`, which still runs: a const fn is `is_fn_like`). The
    // resulting split — const-eval on BUILT, runtime on DERIVED — is BENIGN: `DerivedAgreed` proved
    // derived ≡ built, so a const fn called in both a const AND a runtime context agrees by
    // construction. (`optimized_mir` and `mir_for_ctfe` are ALREADY distinct phases/queries for a
    // const fn, so this adds no new representational invariant.) The registry `take` is one-shot but
    // race-free: `try_flip_ctfe` returns `None` for a const fn BEFORE the take, so only the codegen
    // seam ever consumes the entry, in any query order.
    //   * Static — linkage / `#[used]` / interior-mutability nuances, deferred to a later wave
    //     (also not recorded in the registry yet, so this is belt-and-suspenders).
    // A const ITEM (`Some(Const{..})`, ctfe seam), a const fn (`Some(ConstFn)`, codegen seam), or a
    // non-const fn (`None`, codegen seam) all fall through.
    match tcx.hir_body_const_context(def) {
        Some(rustc_hir::ConstContext::Static(_)) => {
            return rejected("static initializer (deferred to a later CTFE wave)");
        }
        _ => {}
    }
    if tcx.is_coroutine(def.to_def_id()) {
        return rejected("coroutine body");
    }
    // Unsatisfiable predicates shrink the built body to a lone `unreachable` — an intentional
    // upstream behavior the flip must not undo.
    if normal.basic_blocks[START_BLOCK].statements.is_empty()
        && matches!(normal.basic_blocks[START_BLOCK].terminator().kind, TerminatorKind::Unreachable)
    {
        return rejected("built body shrunk to `unreachable` (unsatisfiable predicates)");
    }

    // ---- const-trap (lint-hazard) gate, on the Module ----
    // Trust (CTFE arithmetic loosening): the gate exists ONLY to stop `KnownPanicsLint` — replayed
    // 1:1 in `run_analysis_to_runtime_passes` over the derived body — from re-emitting an
    // `arithmetic_overflow`/`unconditional_panic` diagnostic at the shim's coarse fn-level span.
    // But `KnownPanicsLint::run_lint` (rustc_mir_transform::known_panics_lint) is a TOTAL NO-OP on
    // any body that is neither fn-like nor an ASSOCIATED const — it returns before visiting
    // ("skip anon_const/statics/consts because they'll be evaluated by miri anyway"). For that class
    // — plain `const`, inline-const, and anon-const ITEMS, the CTFE seam's bulk — the lint emits
    // nothing on EITHER the built or the derived body, so there is no double-emit to defuse and the
    // gate is pure over-rejection: an overflowing such const surfaces ONLY at const-EVAL (E0080) via
    // the `Assert(Overflow)` terminator, whose span the flip already stitches from the built sibling,
    // so a flipped overflowing plain const errors at the SAME span, ONCE (a `1u32 << 40` trapping
    // plain const already flips + errors faithfully today). Fn bodies (the codegen seam is always
    // `is_fn_like`) and ASSOCIATED consts keep the gate: for them `KnownPanicsLint` DOES run and WOULD
    // double-emit — the overflow does NOT taint the body (it is a `MirLint`, so the ctfe-seam taint
    // guard cannot catch it). Predicate mirrors `KnownPanicsLint`'s own body gate, so they are aligned
    // by construction. Trust (wave-U): Div0/RemByZero are now ADMITTED by the assert-kind gate
    // below (the div/rem FLIP re-emits built's exact guards); OOB/neg-overflow stay excluded.
    let dk = tcx.def_kind(def);
    let known_panics_lint_runs =
        dk.is_fn_like() || matches!(dk, rustc_hir::def::DefKind::AssocConst { .. });
    if known_panics_lint_runs {
        if let Err(reason) = const_trap_gate(&module) {
            return rejected(reason);
        }
    }

    // ---- re-derive (deterministic: same tcx session, same Module as the hook compared).
    //      Trust (C1/M1): the ABI types are RE-DERIVED from tcx (`SigSource::Rederive`), not
    //      threaded from `normal` — the compile path is a function of (tcx, def, Module,
    //      callees) alone. The ABI gate below then compares that re-derivation against built:
    //      two independent derivations, so the gate can actually fail now. ----
    let mut body = match to_mir::lower_ir_to_mir(
        tcx,
        def,
        &module,
        &callees,
        to_mir::SigSource::Rederive,
    ) {
        Ok(b) => b,
        Err(e) => return rejected(format!("shim: {}", e.reason)),
    };

    // ---- structural gate on the derived body ----
    if let Err(reason) = gate_derived_body(tcx, &body) {
        return rejected(reason);
    }

    // ---- ABI-visible type equality (_0 ..= arg_count) ----
    if body.arg_count != normal.arg_count {
        return rejected(format!(
            "arg_count mismatch: derived {} vs built {}",
            body.arg_count, normal.arg_count
        ));
    }
    for i in 0..=body.arg_count {
        let l = Local::from_usize(i);
        let (d, n) = (body.local_decls[l].ty, normal.local_decls[l].ty);
        // Trust (v25 B1, sharpened by C1/M1): EXACT rustc-type equality, compared with
        // regions erased on both sides. `d` is now the tcx re-derivation
        // (`rederive_abi_sig`), NOT a copy of `n` — so this gate is two independent
        // derivations of the ABI and can genuinely fail, where before `d` was constructed
        // from `n` and the comparison was a tautology for every non-scalar param. Region
        // erasure is not a carve-out: the flip's product exists only at runtime phases,
        // where regions are already erased and semantically inert.
        if tcx.erase_and_anonymize_regions(d) != tcx.erase_and_anonymize_regions(n) {
            return rejected(format!(
                "ABI-visible type mismatch on _{i}: derived {d:?} vs built {n:?}"
            ));
        }
    }

    // ---- stitch assert spans from the built sibling ----
    let asserts = match verify_assert_parity(&body, normal) {
        Ok(n) => n,
        Err(reason) => return rejected(reason),
    };
    // Body-level span fidelity for dumps/diagnostics (semantics-free).
    body.span = normal.span;

    FlipAttempt::Derived { body, asserts, lineage }
}

// ---------------------------------------------------------------------------
// Gate 1: const-trap (lint-hazard) over the trust-ir Module
// ---------------------------------------------------------------------------

/// Reject the flip when any potentially trapping instruction has statically-constant deciding
/// operands (see module docs: `KnownPanicsLint` would fire twice, at a coarser span).
fn const_trap_gate(module: &Module) -> Result<(), String> {
    let Some(func) = module.function_by_id(FuncId::new(0)) else {
        return Err("module has no FuncId(0) function".to_string());
    };
    let mut const_vals: HashSet<ValueId> = HashSet::new();
    // Trust (wave-W, #105): also record each const's INTEGER VALUE, so the div arm can distinguish
    // the two KnownPanicsLint-hazard divisors (`0`, `-1`) from a lint-safe `x / CONST`.
    let mut const_int_vals: HashMap<ValueId, i128> = HashMap::new();
    // Trust-IR v24 spells the upper half of u128 separately. Every such value
    // is necessarily nonzero and not signed -1, so it is a lint-safe constant
    // divisor for this gate (the MIR reconstruction still preserves all bits).
    let mut const_upper_u128_vals: HashSet<ValueId> = HashSet::new();
    for blk in &func.blocks {
        for node in &blk.body {
            if let Inst::Const { value, .. } = &node.inst {
                const_vals.extend(node.results.iter().copied());
                if let Constant::Int(v) = value {
                    for r in &node.results {
                        const_int_vals.insert(*r, *v as i128);
                    }
                } else if matches!(value, Constant::U128(_)) {
                    const_upper_u128_vals.extend(node.results.iter().copied());
                }
            }
        }
    }
    let is_const = |v: &ValueId| const_vals.contains(v);
    for blk in &func.blocks {
        for node in &blk.body {
            match &node.inst {
                Inst::Overflow { lhs, rhs, .. } if is_const(lhs) && is_const(rhs) => {
                    return Err("const-const checked arithmetic (KnownPanicsLint would re-fire \
                                on the derived body)"
                        .to_string());
                }
                Inst::BinOp { op: BinOp::Shl | BinOp::LShr | BinOp::AShr, rhs, .. }
                    if is_const(rhs) =>
                {
                    return Err("const shift amount (KnownPanicsLint hazard)".to_string());
                }
                Inst::BinOp { op: BinOp::Add | BinOp::Sub | BinOp::Mul, lhs, rhs, .. }
                    if is_const(lhs) && is_const(rhs) =>
                {
                    return Err("const-const arithmetic (KnownPanicsLint hazard)".to_string());
                }
                Inst::UnOp { op: UnOp::Neg, operand, .. } if is_const(operand) => {
                    return Err("const negation (KnownPanicsLint hazard)".to_string());
                }
                // Trust (wave-U, div/rem FLIP; REFINED wave-W #105): a CONSTANT divisor is a
                // `KnownPanicsLint` hazard ONLY at the two trap-DECIDING values — const `0`
                // (div-by-zero, an `UnconditionalPanic` = hard compile error) and const `-1` (the
                // `MIN / -1` overflow-deciding operand). A NONZERO, non-`-1` const divisor
                // (`x / 7`, `x % 256`) is lint-SAFE and now ADMITTED: `mir_built` (which the
                // comparator diffs against, PRE-opt) carries the SAME `Eq(c, 0)` div-by-zero +
                // `BitAnd(Eq(c,-1), Eq(x,MIN))` overflow guards as `x / y` — const-prop has NOT run
                // yet, so `c` is a literal operand, not folded away — and the wave-U shim re-emits
                // them byte-identically (DerivedAgreed), so the corpus-common `x / CONST` idiom
                // flips. `KnownPanicsLint` on the flipped body evaluates `Eq(7, 0) = false` and
                // `Eq(7, -1) = false` → both asserts known-safe → NO fire, so no double-fire /
                // span-shift. Wave-U's earlier "assert-count mismatch → +0" reasoning was about the
                // OPTIMIZED body (where const-prop drops the dead guard), not `mir_built`. Keep the
                // two trap-deciding values (and any non-integer const divisor) fail-closed.
                Inst::BinOp {
                    op: BinOp::UDiv | BinOp::SDiv | BinOp::URem | BinOp::SRem,
                    rhs,
                    ..
                } if is_const(rhs) => match const_int_vals.get(rhs) {
                    Some(0) | Some(-1) => {
                        return Err("const trap-deciding divisor (0 / -1) KnownPanicsLint hazard"
                            .to_string());
                    }
                    Some(_) => {}
                    None if const_upper_u128_vals.contains(rhs) => {}
                    None => {
                        return Err("non-integer const divisor (conservative)".to_string());
                    }
                },
                _ => {}
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Gate 2: structural allow-list over the derived body
// ---------------------------------------------------------------------------

/// A scalar the slice-1 flip may declare: `bool` or a fixed-width int.
fn scalar_ok(ty: ty::Ty<'_>) -> bool {
    // Trust (wave-FL): `ty::Float(_)` (f32/f64) joins the scalar fragment so float-bearing bodies
    // (identity/const-return/arithmetic) enter the flip. Every float-flow the shim can't reconstruct
    // (float casts, FCmp, neg, tuples-of-float beyond wave-L) fails closed WITHOUT an ICE — verified
    // at the cast arm (`_ => unsup`) and the BinOp/const arms. f16/f128 are `ty::Float` too but the
    // shim's scalar_ty/const/BinOp arms gate on the trust-ir `is_f32_or_f64`, so an f16/f128 body
    // reaches the shim and then fails closed (no scalar_ty) — still fail-safe.
    // Trust (v25 B1): `ty::Char` joins the scalar fragment — the shim now
    // denotes real char locals (scalar_rustc_ty), so a char decl passes the
    // exact-equality ABI gate with no carve-out.
    matches!(ty.kind(), ty::Bool | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Char)
}

/// Trust (wave-D, Drop-free aggregate constructor-return FLIP): a RETURN local (`_0`) type the flip
/// may declare for a struct constructor return — a CONCRETE, Drop-free struct. The Drop-free
/// (`!needs_drop`) gate is load-bearing: an aggregate with drop glue would make
/// `ElaborateDrops`/`AbortUnwindingCalls` do real work, breaking the "every pass Built→
/// Runtime(Optimized) is total over the fragment" invariant the flip relies on. Concrete-only (a
/// generic `-> Wrapper<T>` fails the param-free guard → clean-only) so `fully_monomorphized()` is
/// param-free-safe, matching the shim's own denotation. Enums/unions (non-struct Adt) fail closed.
///
/// Trust (wave-X): the gate is `!needs_drop` — NOT `Copy` (dropped, mirroring the shim's relaxed
/// struct return-type gate). `Copy` was over-strict: a NON-`Copy` yet Drop-free struct has no drop
/// glue, so every pass stays total over it (the exact wave-F argument the PARAM gate already
/// applied in `arg_struct_ty_ok`). The whole-struct-`Copy`-of-a-non-`Copy` ICE hazard is closed at
/// the shim source (`cx.operand` emits `Move` for a non-`Copy` place), NOT here.
///
/// Trust (wave-L, scalar-tuple constructor-return FLIP): a TUPLE of fragment scalars (`scalar_ok`
/// per element) is admitted on the SAME footing — built constructs it via
/// `Rvalue::Aggregate(AggregateKind::Tuple, ..)`, byte-identical in shape to the struct case (no
/// Adt identity to pin). A scalar tuple is unconditionally `Copy && !needs_drop`; the `!needs_drop`
/// check below is trivially satisfied. A tuple with a non-scalar element fails the per-element
/// `scalar_ok` → clean-only (matched by the shim's own tuple return-type gate).
fn agg_return_ty_ok<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    if ty.has_non_region_param() || ty.has_non_region_infer() {
        return false;
    }
    let te = ty::TypingEnv::fully_monomorphized();
    // Trust (wave-Y): a FIELDLESS enum `_0` (every variant field-free) is admitted for construction
    // (`E::V`) on the same footing — Drop-free by construction, so pass-totality holds; the shim
    // rebuilds `_0 = Aggregate(Adt{variant_k}, [])` and the comparator's `agg(adt:E:k,[])` observable
    // pins the variant. Trust (wave-YP): extended to the LEGACY scalar-payload model — a variant with
    // AT MOST ONE field (`Option`, `Result`); the shim rebuilds `_0 = Aggregate(Adt{k}, [payload?])`
    // and the comparator's `agg(adt:E:k,[op])` pins variant + payload. `!needs_drop` (below) is the
    // real pass-totality gate (a drop-glue payload would make `ElaborateDrops` do work); a multi-field
    // enum (general model) is EXCLUDED here (`.len() <= 1`).
    let shape_ok = matches!(ty.kind(), ty::Adt(adt, _) if adt.is_struct())
        || matches!(ty.kind(), ty::Tuple(elems) if !elems.is_empty() && elems.iter().all(scalar_ok))
        || matches!(ty.kind(), ty::Adt(adt, _)
            if adt.is_enum() && !adt.variants().is_empty()
                && adt.variants().iter().all(|v| v.fields.len() <= 1));
    shape_ok && !ty.needs_drop(tcx, te)
}

/// Trust (wave-F, struct-param scalar-field-read FLIP): an ARG local (`_1..`) type the flip may
/// declare for a by-value struct param whose scalar fields are READ. Same concrete + Drop-free gate
/// as [`agg_return_ty_ok`] EXCEPT `Copy` is NOT required — a by-value `!needs_drop` struct (e.g.
/// `struct A { a: isize }`, which is non-`Copy` yet has no drop glue) is passed and its fields read
/// with no move/drop obligation, so every pass Built→Runtime(Optimized) stays total over it. The
/// `!needs_drop` gate is still load-bearing (drop glue would make `ElaborateDrops` do real work,
/// breaking pass-totality). The looser gate is SOUND only because the paired `struct_args_read_only`
/// guard confines every mention of such a local to a scalar FIELD read — so the shim never emits a
/// bare whole-struct `Copy`/`Move` of it (a non-`Copy` struct `Copy` would be ill-typed → ICE).
fn arg_struct_ty_ok<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    if ty.has_non_region_param() || ty.has_non_region_infer() {
        return false;
    }
    let te = ty::TypingEnv::fully_monomorphized();
    matches!(ty.kind(), ty::Adt(adt, _) if adt.is_struct()) && !ty.needs_drop(tcx, te)
}

/// Trust (wave-V, fieldless-enum discriminant-read FLIP): a by-value FIELDLESS enum ARG local
/// (`_1: E` where every variant of `E` is field-free — a C-like `enum E { A, B, C }`). The shim
/// declares the derived arg with this exact built type (ABI byte-identical), reads its tag via
/// `_d = Discriminant(_1)`, and the reshaped `SwitchInt` dispatches on it. `!needs_drop` is
/// belt-and-suspenders (a fieldless enum has no drop glue by construction) but keeps
/// `ElaborateDrops`/`AbortUnwindingCalls` no-ops → pass-totality. Concrete-only (a generic enum
/// fails the param guard). Payload/niche enums (any variant with fields) are EXCLUDED here — the
/// tag read alone does not reconstruct their layout — so they fall through to clean-only. The
/// paired `enum_args_disc_read_only` guard independently confines EVERY mention of such a local to
/// the bare discriminant read (no field/downcast/whole-value use), so the shim never emits an
/// ill-typed bare `Copy(_1)` of the enum.
fn arg_enum_ty_ok<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    if ty.has_non_region_param() || ty.has_non_region_infer() {
        return false;
    }
    let te = ty::TypingEnv::fully_monomorphized();
    // Trust (wave-V + enum arc slices 1–2): a by-value enum param read for its DISCRIMINANT and/or a
    // scalar PAYLOAD field. Wave-V restricted this to FIELDLESS enums; slice 1 admitted a PAYLOAD enum
    // (`enum E{A(i32),B(bool)}`) read for its tag only; slice 2 admits a payload read too. The paired
    // `enum_args_disc_read_only` guard (below) confines EVERY mention to a bare `Rvalue::Discriminant(_e)`
    // OR a `[Downcast(v), Field(k, scalar)]` payload read — a whole-value/other use fails there → no
    // flip. Concrete + Drop-free ONLY (mirrors `param_rty`'s Ty::Enum arm), so the shim declares the
    // derived arg with the byte-identical built type and never emits an ill-typed whole-enum Copy/Move.
    matches!(ty.kind(), ty::Adt(adt, _)
        if adt.is_enum()
            && !adt.variants().is_empty())
        && !ty.needs_drop(tcx, te)
}

/// A local type the slice-1 flip may declare: a scalar, a checked-arithmetic pair
/// `(int, bool)`, or unit. Unit locals (`_0` of every unit-returning fn, unit temps) are
/// ZSTs ordinary built MIR declares and assigns constantly — every pass between `Built`
/// and `Runtime(Optimized)` is total over them by construction. Admitting them closes the
/// burn-in's dominant fallback class (`local type outside fragment: ()`, 109/118 events,
/// i.e. nearly every `fn main`-shaped body).
fn local_ty_ok(ty: ty::Ty<'_>) -> bool {
    match ty.kind() {
        // NB: unit IS the 0-tuple, so it must be admitted HERE — a `_` arm below this one
        // never sees it (the wave-2 verification caught exactly that dead-code shadowing).
        ty::Tuple(elems) => {
            elems.is_empty()
                || (elems.len() == 2
                    && matches!(elems[0].kind(), ty::Int(_) | ty::Uint(_))
                    && elems[1].is_bool())
        }
        _ => scalar_ok(ty),
    }
}

/// An ARG-local type the slice-3 flip may additionally declare, but ONLY when the local is
/// proven never-mentioned in the body (the opaque param classes `to_mir::param_rty` threads
/// from the built sibling): refs / raw pointers (closure envs, plain refs), zero-upvar
/// by-value closure ZSTs, unit, and scalar tuples. Every pass between `Built` and
/// `Runtime(Optimized)` is total over an UNUSED arg local of these types — it is
/// declaration-only data the passes never inspect beyond its (sized, fully-monomorphic) type.
fn opaque_arg_ty_ok(ty: ty::Ty<'_>) -> bool {
    match ty.kind() {
        ty::Ref(..) | ty::RawPtr(..) => true,
        ty::Closure(_, args) => args.as_closure().upvar_tys().is_empty(),
        ty::Tuple(elems) => elems.iter().all(scalar_ok),
        _ => ty.is_unit(),
    }
}

/// Every `Local` mentioned by any statement or terminator (operands, places, assert
/// messages, switch discriminants — completeness by the MIR `Visitor`, which enumerates
/// every `Local` embedded anywhere in block data). Deliberately does NOT walk
/// `local_decls`/debug info: a declaration is not a mention.
fn mentioned_locals<'tcx>(body: &Body<'tcx>) -> HashSet<Local> {
    struct Mentions {
        used: HashSet<Local>,
    }
    impl<'tcx> Visitor<'tcx> for Mentions {
        fn visit_local(&mut self, local: Local, _ctx: PlaceContext, _loc: Location) {
            self.used.insert(local);
        }
    }
    let mut v = Mentions { used: HashSet::new() };
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        v.visit_basic_block_data(bb, data);
    }
    v.used
}

/// Trust (wave-8a): verify that every mention of a `ref_args` local is a BARE forwarding call
/// argument — `Operand::Move|Copy(Place{ local, projection: [] })` in a `TerminatorKind::Call`'s
/// `args`. Any other appearance (a statement, a projection like `(*_p)`, the call callee or
/// destination, a non-Call terminator) means the derived body OBSERVES the reference beyond
/// passing it through, which the slice-3 opaque-arg totality argument does not cover — fail
/// closed. Overriding `visit_terminator` to SKIP the bare call-arg operands, then relying on the
/// default walk for everything else, makes `visit_local` fire only on a non-forward use.
struct RefArgForwardGuard<'a> {
    ref_args: &'a HashSet<Local>,
    // Trust (wave-30): interior-arg temps `_tmp = &((*_arg).field); g(move _tmp)` — the borrow-into-
    // temp is admitted (the `_arg`-as-borrow-base does not flag), exactly as the wave-29 return borrow.
    interior_arg_temps: &'a HashSet<Local>,
    violation: Option<Local>,
}
impl<'tcx> Visitor<'tcx> for RefArgForwardGuard<'_> {
    fn visit_local(&mut self, local: Local, _ctx: PlaceContext, _loc: Location) {
        if self.ref_args.contains(&local) {
            self.violation.get_or_insert(local);
        }
    }
    fn visit_terminator(&mut self, term: &rustc_middle::mir::Terminator<'tcx>, loc: Location) {
        if let TerminatorKind::Call { func, args, destination, .. } = &term.kind {
            self.visit_operand(func, loc);
            // Writing INTO a ref arg (it as the call destination) is not forwarding.
            if self.ref_args.contains(&destination.local) {
                self.violation.get_or_insert(destination.local);
            }
            for arg in args.iter() {
                match &arg.node {
                    // A bare `_p` (no projection) forwarded as an argument: the admitted shape.
                    Operand::Move(p) | Operand::Copy(p) if p.projection.is_empty() => {}
                    // Anything else (a projected `(*_p).f`, a ref arg buried in an aggregate) is
                    // an observation — walk it so `visit_local` flags any ref-arg mention.
                    other => self.visit_operand(other, loc),
                }
            }
        } else {
            self.super_terminator(term, loc);
        }
    }
    // Trust (wave-15): the RETURN-forward `_0 = move|copy _p` (RETURN_PLACE <- a bare ref arg) is
    // the ONE statement-level use of a ref arg the fragment admits — the shim emits exactly this
    // for `fn(..) -> &T { param }`, mirroring built's `_0 = copy _1`. Skip it WITHOUT walking the
    // operand, so `visit_local` never fires on `_p`. Any OTHER statement use of a ref arg (a
    // non-return dest, a projected `(*_p)`, a ref arg inside an aggregate) still walks and flags —
    // the call-arg-forward-only property is preserved for every other body.
    fn visit_statement(&mut self, stmt: &Statement<'tcx>, loc: Location) {
        if let StatementKind::Assign(assign) = &stmt.kind {
            let (place, rvalue) = &**assign;
            if place.local == RETURN_PLACE && place.projection.is_empty() {
                // Trust: rust 1.99 — `Rvalue::Use` carries a `WithRetag` payload; either flag is
                // the same value-identity use, so the forward-recognizer ignores it.
                if let Rvalue::Use(Operand::Move(p) | Operand::Copy(p), _) = rvalue {
                    if p.projection.is_empty() && self.ref_args.contains(&p.local) {
                        return;
                    }
                }
            }
            // Trust (wave-24): the ref-escape WRITE `(*_p).k = <value>` — `_p` a ref arg,
            // projection EXACTLY `[Deref, Field]`. The store DEST use of `_p` is admitted (the
            // referent write is total, and the differential already proved the derived body ≡
            // built via the DISCRIMINATING `mem[...]` observable, so the field index is pinned).
            // Skip walking the DEST place so `_p`-as-store-target does not flag, but STILL walk the
            // RVALUE (`visit_rvalue`) so a ref arg observed in the stored VALUE (`(*_q)`, a
            // re-borrow) still flags. `place_ok` independently certifies the `[Deref, Field(scalar)]`
            // projection shape is total.
            if self.ref_args.contains(&place.local)
                && place.projection.len() == 2
                && matches!(place.projection[0], ProjectionElem::Deref)
                && matches!(place.projection[1], ProjectionElem::Field(..))
            {
                self.visit_rvalue(rvalue, loc);
                return;
            }
            // Trust (wave-29 + wave-30): the interior-borrow assignment `_dst = &((*_p).field)` —
            // `_dst` is RETURN_PLACE (wave-29, the returned getter) OR an interior-arg temp (wave-30,
            // `_tmp = &((*_p).f); g(move _tmp)`). The `_p`-as-borrow-base is the admitted use
            // (`place_ok` independently certifies the borrowed `[Deref, Field(scalar)]` / arg-ref
            // place, and the differential's `iref(a{p},k)` observable pins the field). Skip WITHOUT
            // walking so `_p` does not flag; there is no stored value to re-inspect (the rvalue IS
            // the admitted borrow — unlike wave-24's store, whose RVALUE could hide another ref arg).
            if place.projection.is_empty()
                && (place.local == RETURN_PLACE || self.interior_arg_temps.contains(&place.local))
            {
                if let Rvalue::Ref(_, BorrowKind::Shared, borrowed) = rvalue {
                    if self.ref_args.contains(&borrowed.local)
                        && borrowed.projection.len() == 2
                        && matches!(borrowed.projection[0], ProjectionElem::Deref)
                        && matches!(borrowed.projection[1], ProjectionElem::Field(..))
                    {
                        return;
                    }
                }
            }
            // Trust (wave-S): the shared-ref scalar READ `_t = copy|move (*_p)` — `_p` a ref arg,
            // rvalue a bare `[Deref]` read. Admit it WITHOUT walking the operand so `_p`-as-read does
            // not flag. The dest `_t` is a fragment scalar temp (`local_ty_ok`) and `place_ok`
            // independently certifies the `[Deref]` place is a shared-ref-to-scalar; a bare deref-read
            // hides no other ref-arg mention (unlike wave-24's store, whose stored VALUE could).
            if let Rvalue::Use(Operand::Copy(p) | Operand::Move(p), _) = rvalue {
                if self.ref_args.contains(&p.local)
                    && p.projection.len() == 1
                    && matches!(p.projection[0], ProjectionElem::Deref)
                {
                    return;
                }
            }
        }
        self.super_statement(stmt, loc);
    }
}

/// Trust (wave-30/29b, interior-borrow reborrow-temp FLIP): the set of shared-ref TEMP locals the shim
/// emits for `g(&self.field)` (wave-30) and `fn get(&self) -> &T { &self.field }` (wave-29b). Each is
/// assigned EXACTLY one interior borrow `_t = &((*_arg).Field(scalar))` (a `place_ok`-certified
/// [Deref, Field(scalar)]/arg-ref place) and used EXACTLY once as a bare `Operand::Move` — either a call
/// argument (`g(move _t)`, wave-30) OR a move into RETURN_PLACE (`_0 = move _t`, wave-29b's reborrow-temp
/// return getter, which reproduces built's `StorageLive(_2); _2 = &((*_1).K); _0 = &(*_2); StorageDead(_2)`
/// marker sequence so `markers_exact` holds at `-O`). NO other mention exists anywhere (total VALUE
/// mentions == 2: the def dest + the one use; storage markers are `NonUse` and uncounted). The
/// `mentions == 2` clause is the airtight single-use guarantee — a temp that is stored / returned twice /
/// re-borrowed / copied / used again appears a 3rd time and is rejected, so no interior pointer can escape
/// or alias beyond the one use. This is the flip gate's independent admission of the exact (and only)
/// shapes the shim's `try_reconstruct_interior_arg` + the return-getter reborrow-temp emission produce.
fn interior_arg_temps<'tcx>(body: &Body<'tcx>) -> HashSet<Local> {
    // Total place-local mentions per local (dest + every operand/projection occurrence).
    let mut mentions: HashMap<Local, u32> = HashMap::new();
    struct MentionCounter<'a> {
        m: &'a mut HashMap<Local, u32>,
    }
    impl<'tcx> Visitor<'tcx> for MentionCounter<'_> {
        fn visit_local(&mut self, l: Local, ctx: PlaceContext, _loc: Location) {
            // Trust (wave-29b): count VALUE mentions only. Storage markers / debuginfo
            // (`PlaceContext::NonUse`) do not observe the pointer value, so the built
            // reborrow-temp's `StorageLive(t)`/`StorageDead(t)` (which the return-getter shim now
            // reproduces to hold `markers_exact` at `-O`) must NOT inflate the count past the
            // airtight `def + single-use == 2` invariant. A real read/write is always a
            // Non/MutatingUse and is still counted, so no observation can hide.
            if matches!(ctx, PlaceContext::NonUse(_)) {
                return;
            }
            *self.m.entry(l).or_default() += 1;
        }
    }
    {
        let mut c = MentionCounter { m: &mut mentions };
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            c.visit_basic_block_data(bb, data);
        }
    }
    // The interior-borrow def (bare shared-ref dest); its single use — either a bare `Operand::Move`
    // call argument (`g(move _t)`, wave-30) or a shared reborrow into RETURN_PLACE (`_0 = &(*_t)`,
    // wave-29b's return getter).
    let mut borrow_def: HashMap<Local, u32> = HashMap::new();
    let mut callarg_move: HashMap<Local, u32> = HashMap::new();
    let mut ret_reborrow: HashMap<Local, u32> = HashMap::new();
    for (_bb, data) in body.basic_blocks.iter_enumerated() {
        for stmt in &data.statements {
            if let StatementKind::Assign(assign) = &stmt.kind {
                let (place, rvalue) = &**assign;
                // The interior-borrow definition `_t = &((*_arg).Field(scalar))`.
                if place.projection.is_empty()
                    && matches!(body.local_decls[place.local].ty.kind(), ty::Ref(_, _, m) if m.is_not())
                {
                    if let Rvalue::Ref(_, BorrowKind::Shared, borrowed) = rvalue {
                        if borrowed.projection.len() == 2
                            && matches!(borrowed.projection[0], ProjectionElem::Deref)
                            && matches!(borrowed.projection[1], ProjectionElem::Field(..))
                            && place_ok(body, borrowed).is_ok()
                        {
                            *borrow_def.entry(place.local).or_default() += 1;
                        }
                    }
                }
                // Trust (wave-29b): the return-getter use `_0 = &(*_t)` — a SHARED reborrow of a bare
                // interior temp into RETURN_PLACE (the reborrow-temp form the shim emits for
                // `fn get(&self) -> &T { &self.field }`, reproducing built's `_0 = &(*_2)` exactly).
                if place.local == RETURN_PLACE && place.projection.is_empty() {
                    if let Rvalue::Ref(_, BorrowKind::Shared, borrowed) = rvalue {
                        if borrowed.projection.len() == 1
                            && matches!(borrowed.projection[0], ProjectionElem::Deref)
                        {
                            *ret_reborrow.entry(borrowed.local).or_default() += 1;
                        }
                    }
                }
            }
        }
        if let Some(term) = &data.terminator {
            if let TerminatorKind::Call { args, .. } = &term.kind {
                for arg in args.iter() {
                    if let Operand::Move(p) = &arg.node {
                        if p.projection.is_empty() {
                            *callarg_move.entry(p.local).or_default() += 1;
                        }
                    }
                }
            }
        }
    }
    borrow_def
        .iter()
        .filter(|(l, &d)| {
            // EXACTLY one interior-borrow def, TOTAL value-mentions == 2 (def + the one use), and
            // that single use is EITHER a call-arg move (`g(move _t)`, wave-30) OR a shared reborrow
            // into `_0` (`_0 = &(*_t)`, wave-29b). `mentions == 2` guarantees the single use is the
            // recorded one — any store / second use / projected use adds a 3rd mention and rejects;
            // the two use-kinds are mutually exclusive under `mentions == 2` (a body with both would
            // count 3).
            d == 1
                && mentions.get(l) == Some(&2)
                && (callarg_move.get(l) == Some(&1) || ret_reborrow.get(l) == Some(&1))
        })
        .map(|(l, _)| *l)
        .collect()
}

fn ref_args_forward_only<'tcx>(
    body: &Body<'tcx>,
    ref_args: &HashSet<Local>,
    interior_arg_temps: &HashSet<Local>,
) -> Result<(), String> {
    let mut g = RefArgForwardGuard { ref_args, interior_arg_temps, violation: None };
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        g.visit_basic_block_data(bb, data);
    }
    match g.violation {
        Some(l) => Err(format!("ref arg {l:?} used outside a forwarding call argument")),
        None => Ok(()),
    }
}

/// Trust (wave-F): verify that every mention of a `struct_args` local (a by-value struct param
/// admitted by [`arg_struct_ty_ok`]) is either a scalar FIELD READ — a place whose FIRST projection
/// is `Field` in a NON-mutating context (`(_s.k)` read) — or (wave-K) a BARE whole-struct `_s` in a
/// NON-mutating use when the struct is `Copy` (the operator-arg `add(move _1, move _2)`). Otherwise:
///   * a BARE whole-struct use `_s` of a NON-`Copy` struct — the shim would render this `Copy(_s)`,
///     ill-typed for a non-`Copy` struct → MIR-validation ICE (wave-K admits it ONLY when `Copy`,
///     where `Copy(_s)`/`Move(_s)` is well-typed and the `move-as-copy` normalization congruences it);
///   * a WRITE `(_s.k) = v` / bare `_s = v` (mutating context) — the shim reconstructs only reads;
///   * a `Deref`/nested-first projection — outside the by-value field-read shape.
/// Modeled on [`RefArgForwardGuard`]: the admitted shape is recognized in `visit_place`, everything
/// else records a violation. This is the independent guarantee that makes the looser (Copy-free,
/// merely `!needs_drop`) [`arg_struct_ty_ok`] admission sound. The field's SCALAR-ness is separately
/// pinned by the shim (`ir_scalar_of_body`) and `place_ok`; here we only certify the ACCESS shape.
struct StructArgReadGuard<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    struct_args: &'a HashSet<Local>,
    violation: Option<Local>,
}
impl<'tcx> Visitor<'tcx> for StructArgReadGuard<'_, 'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, ctx: PlaceContext, loc: Location) {
        if self.struct_args.contains(&place.local) {
            let is_field_read = matches!(place.projection.first(), Some(ProjectionElem::Field(..)))
                && !ctx.is_mutating_use();
            // Trust (wave-K, operator idiom `a + b` → `<V2 as Add>::add(move _1, move _2)`): a BARE
            // whole-struct mention (`_s`, empty projection) in a NON-mutating use — the call-arg
            // move/copy `add(move _1, move _2)` — is admitted IFF the struct is `Copy`. A `Copy`
            // struct's `Copy(_s)`/`Move(_s)` is well-typed MIR (the shim emits exactly this; the
            // comparator's `move-as-copy` normalization congruences move-vs-copy), so it never hits
            // the ICE that `arg_struct_ty_ok`'s looser `!needs_drop` (Copy-free) admission risks — the
            // precise hazard this guard exists to prevent. Re-gate to `Copy` specifically (NOT merely
            // `!needs_drop`): a non-Copy by-value arg passed whole would be a `Move` that the shim's
            // `Copy(_s)` emission cannot honor. A mutating whole-struct use, or a Deref/nested-first
            // projection, still flags. Concrete-only (the derived body is monomorphized).
            let is_copy_whole_arg = place.projection.is_empty()
                && !ctx.is_mutating_use()
                && self.tcx.type_is_copy_modulo_regions(
                    ty::TypingEnv::fully_monomorphized(),
                    self.body.local_decls[place.local].ty,
                );
            if !is_field_read && !is_copy_whole_arg {
                self.violation.get_or_insert(place.local);
            }
        }
        self.super_place(place, ctx, loc);
    }
}

fn struct_args_read_only<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    struct_args: &HashSet<Local>,
) -> Result<(), String> {
    let mut g = StructArgReadGuard { tcx, body, struct_args, violation: None };
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        g.visit_basic_block_data(bb, data);
    }
    match g.violation {
        Some(l) => Err(format!(
            "struct-value arg {l:?} used outside a scalar field read / Copy whole-arg move"
        )),
        None => Ok(()),
    }
}

/// Trust (wave-GH2, struct call-result TEMP): a NON-arg local the flip may declare for a struct
/// value produced by one call and consumed whole by another — the `println!` desugar
/// (`_2 = Arguments::from_str(..); _1 = _print(move _2)`). Strictly TIGHTER than
/// [`arg_struct_ty_ok`]: `Copy` is REQUIRED (not merely `!needs_drop`), because a temp's raison
/// d'être is the whole-value hand-off, and the whole-use arm of [`StructTempGuard`] admits bare
/// mentions on the same `Copy` footing as wave-K (well-typed `Copy(_t)`/`Move(_t)`; `move-as-copy`
/// congruence). `!needs_drop` keeps `ElaborateDrops` a no-op (pass-totality); concrete-only
/// (param/infer-free) as everywhere in the fragment. The paired [`struct_temps_confined`] guard
/// restricts every mention to (a) the bare CALL-DESTINATION write, (b) a bare non-mutating
/// whole use (call-arg move), or (c) a non-mutating scalar field read — so no pass between
/// `Built` and `Runtime(Optimized)` can observe a shape outside what the shim faithfully emits.
fn temp_struct_ty_ok<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    if ty.has_non_region_param() || ty.has_non_region_infer() {
        return false;
    }
    let te = ty::TypingEnv::fully_monomorphized();
    matches!(ty.kind(), ty::Adt(adt, _) if adt.is_struct())
        && tcx.type_is_copy_modulo_regions(te, ty)
        && !ty.needs_drop(tcx, te)
}

/// Trust (wave-GH2): verify every mention of a `struct_temps` local (admitted by
/// [`temp_struct_ty_ok`]) is one of the three shapes the shim emits for a call-result struct
/// temp. Modeled on [`StructArgReadGuard`], with ONE additional admitted context: the bare
/// call-DESTINATION write (`_t = call(..)`, `PlaceContext::MutatingUse(Call)`) — an arg local
/// never has a def, a temp has exactly this one. Any OTHER mutating use (a plain `_t = rvalue`
/// assign, a field write, Drop, borrow-mut), a `Deref`/nested projection, or a projected
/// destination records a violation → no flip (clean-only preserved). The type-level `Copy`
/// admission makes the bare non-mutating whole use well-typed by construction.
struct StructTempGuard<'a> {
    struct_temps: &'a HashSet<Local>,
    violation: Option<Local>,
}
impl<'tcx> Visitor<'tcx> for StructTempGuard<'_> {
    fn visit_place(&mut self, place: &Place<'tcx>, ctx: PlaceContext, loc: Location) {
        if self.struct_temps.contains(&place.local) {
            let is_call_dest = place.projection.is_empty()
                && matches!(ctx, PlaceContext::MutatingUse(MutatingUseContext::Call));
            let is_whole_read = place.projection.is_empty() && !ctx.is_mutating_use();
            let is_field_read = matches!(place.projection.first(), Some(ProjectionElem::Field(..)))
                && !ctx.is_mutating_use();
            if !is_call_dest && !is_whole_read && !is_field_read {
                self.violation.get_or_insert(place.local);
            }
        }
        self.super_place(place, ctx, loc);
    }
}

fn struct_temps_confined<'tcx>(
    body: &Body<'tcx>,
    struct_temps: &HashSet<Local>,
) -> Result<(), String> {
    let mut g = StructTempGuard { struct_temps, violation: None };
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        g.visit_basic_block_data(bb, data);
    }
    match g.violation {
        Some(l) => Err(format!(
            "struct temp {l:?} used outside call-dest / whole read / scalar field read"
        )),
        None => Ok(()),
    }
}

/// Trust (wave-V, fieldless-enum discriminant-read FLIP): verify that every mention of an
/// `enum_args` local (a by-value fieldless enum admitted by [`arg_enum_ty_ok`]) is EXACTLY a bare
/// `Rvalue::Discriminant(_e)` read (empty projection). This is the independent guarantee that makes
/// the enum-arg admission sound: the shim reconstructs ONLY the discriminant read + the reshaped
/// switch, so a body that reads a field, downcasts, or takes the enum by value would exceed what
/// the shim can faithfully re-emit — and a bare `Copy(_e)`/`Move(_e)` of a (possibly non-`Copy` in
/// general, though fieldless enums are `Copy`) enum is out of the scalar fragment. Modeled on
/// [`StructArgReadGuard`], but the admitted shape is recognized in `visit_rvalue` (a `Discriminant`
/// rvalue is not distinguishable from a `Copy` by `PlaceContext` alone): we DO NOT descend into the
/// place of an admitted bare `Discriminant(_e)`, so `visit_place` only ever sees a NON-discriminant
/// mention of an enum arg — which it flags. A projected `Discriminant((*_e))` / `Discriminant(_e
/// downcast)` keeps its non-empty projection, is not admitted here, and is flagged when super-visited.
struct EnumArgDiscGuard<'a> {
    enum_args: &'a HashSet<Local>,
    violation: Option<Local>,
}
impl<'tcx> Visitor<'tcx> for EnumArgDiscGuard<'_> {
    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, loc: Location) {
        if let Rvalue::Discriminant(place) = rvalue {
            if self.enum_args.contains(&place.local) && place.projection.is_empty() {
                // Admitted bare discriminant read — do NOT descend into the place (so `visit_local`
                // never counts this as a mention). Every OTHER use of the enum arg is flagged.
                return;
            }
        }
        self.super_rvalue(rvalue, loc);
    }
    // Trust (enum arc slice 2): exempt a PAYLOAD read `((_e as V).k)` — projection EXACTLY
    // `[Downcast(_, v), Field(k, scalar)]` with base an enum arg. The shim re-emits exactly this place
    // (a `Downcast` to the block's variant + a scalar `Field`), so it is a faithful read; a WRONG
    // variant/field only MISSES the flip (the derived `Downcast` differs from built's → the canonical
    // compare rejects it), never miscompiles. Do NOT descend (so `visit_local` doesn't flag the base);
    // every OTHER mention of the enum arg still reaches `visit_local` via `super_place`.
    fn visit_place(&mut self, place: &Place<'tcx>, ctx: PlaceContext, loc: Location) {
        if self.enum_args.contains(&place.local)
            && place.projection.len() == 2
            && matches!(place.projection[0], ProjectionElem::Downcast(..))
            && matches!(place.projection[1], ProjectionElem::Field(_, fty) if scalar_ok(fty))
        {
            return;
        }
        self.super_place(place, ctx, loc);
    }
    // Trust (wave-V, adversarial-review H1): flag on `visit_local` (mirroring `RefArgForwardGuard`),
    // not `visit_place`, so an enum arg used as a projection-INDEX sub-local (`_arr[_e]`) is caught
    // too — `visit_place` only inspects the base local and would miss it. (That shape is dead today:
    // the shim never emits it and an enum-typed index is ill-typed; this is future-proof robustness.)
    // The admitted bare `Discriminant(_e)` (visit_rvalue) and payload read (visit_place) are exempted.
    fn visit_local(&mut self, local: Local, _ctx: PlaceContext, _loc: Location) {
        if self.enum_args.contains(&local) {
            self.violation.get_or_insert(local);
        }
    }
}

fn enum_args_disc_read_only<'tcx>(
    body: &Body<'tcx>,
    enum_args: &HashSet<Local>,
) -> Result<(), String> {
    let mut g = EnumArgDiscGuard { enum_args, violation: None };
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        g.visit_basic_block_data(bb, data);
    }
    match g.violation {
        Some(l) => Err(format!("enum arg {l:?} used outside a discriminant or payload-field read")),
        None => Ok(()),
    }
}

fn place_ok<'tcx>(body: &Body<'tcx>, place: &Place<'tcx>) -> Result<(), String> {
    if place.local.as_usize() >= body.local_decls.len() {
        return Err(format!("place local _{} out of range", place.local.as_usize()));
    }
    match place.projection.len() {
        0 => Ok(()),
        1 => match place.projection[0] {
            // The checked-pair tuple's value/overflow fields (`f <= 1` on any base), OR (wave-F) any
            // scalar field `(_s.k)` of a by-value STRUCT base — the struct-param field read. The
            // base's Adt type is ABI-gate-pinned, so field `k`'s identity/type is ground-truth, and
            // a `Field(k, scalar)` place on a sized struct is total under every replayed pass. The
            // `struct_args_read_only` guard separately certifies ONLY admitted struct args carry such
            // reads (so no non-struct base sneaks a `k > 1` field in through this widened arm).
            ProjectionElem::Field(f, fty)
                if scalar_ok(fty)
                    && (f.as_usize() <= 1
                        || matches!(
                            body.local_decls[place.local].ty.kind(),
                            ty::Adt(adt, _) if adt.is_struct()
                        )) =>
            {
                Ok(())
            }
            // Trust (wave-S): the shared-ref scalar READ place `(*_p)` — projection EXACTLY `[Deref]`
            // with the base an ARG (`1..=arg_count`) SHARED ref whose pointee is a fragment scalar. The
            // shim emits `_t = copy (*_p)` for `*r` (a `fwd_ptr_param` read); every pass replayed
            // between `Built` and `Runtime(Optimized)` is total over a deref of a shared-ref-to-scalar.
            // Mirrors the wave-24 `[Deref, Field]` write cert, minus the field. `m.is_not()` keeps
            // `&mut`/raw reads out (clean-only); `ref_args_forward_only` separately admits the
            // `_p`-as-read use.
            ProjectionElem::Deref
                if place.local.as_usize() >= 1
                    && place.local.as_usize() <= body.arg_count
                    && matches!(
                        body.local_decls[place.local].ty.kind(),
                        ty::Ref(_, pointee, m) if m.is_not() && scalar_ok(*pointee)
                    ) =>
            {
                Ok(())
            }
            _ => Err("non-Field projection outside fragment".to_string()),
        },
        // Trust (wave-24): the ref-escape WRITE dest `(*_p).k` — projection EXACTLY
        // `[Deref, Field(k, scalar)]` with the base local a reference / raw pointer. This is the
        // ONLY 2-level projection the shim emits (`to_mir::recognize_field_write` collapses the
        // `Load(*P):Struct → InsertField(k,v) → Store(*P)` triple to `(*P).k = v`). Every pass
        // replayed between `Built` and `Runtime(Optimized)` is total over a deref-then-scalar-field
        // place; the base must be a ref/ptr (a `Deref` of anything else is ill-typed MIR the shim
        // never builds) and the field scalar (the producer rejects non-scalar field referents,
        // wave-23). The ref-arg OBSERVATION gate (`ref_args_forward_only`) separately admits the
        // matching `_p`-as-store-target use; `place_ok` only certifies projection totality here.
        2 => match (place.projection[0], place.projection[1]) {
            (ProjectionElem::Deref, ProjectionElem::Field(_f, fty))
                if scalar_ok(fty)
                    // Base must be an ARG ref/ptr (`1..=arg_count`): the shim only builds a
                    // `[Deref, Field]` store through a `fwd_ptr_param` (an arg reference), so
                    // pinning to an arg matches the emitted shape exactly and keeps `_0`
                    // (the wave-15 shared-ref return local) out of this arm.
                    && place.local.as_usize() >= 1
                    && place.local.as_usize() <= body.arg_count
                    && matches!(
                        body.local_decls[place.local].ty.kind(),
                        ty::Ref(..) | ty::RawPtr(..)
                    ) =>
            {
                Ok(())
            }
            // Trust (enum arc slice 2): the payload READ `((_e as V).k)` — projection EXACTLY
            // `[Downcast(_, v), Field(k, scalar)]` with the base an enum ARG. The shim emits this for a
            // payload read of a by-value payload-enum param (a `Downcast` to the block's variant + a
            // scalar `Field`). A downcast-then-scalar-field place is total under every replayed pass —
            // it is the canonical shape rustc's own match lowering uses for arm payload access; the
            // base must be an enum arg and the field a fragment scalar. `enum_args_disc_read_only`
            // separately admits the matching `_e`-as-payload-read use; `place_ok` certifies totality.
            (ProjectionElem::Downcast(..), ProjectionElem::Field(_f, fty))
                if scalar_ok(fty)
                    && place.local.as_usize() >= 1
                    && place.local.as_usize() <= body.arg_count
                    && matches!(
                        body.local_decls[place.local].ty.kind(),
                        ty::Adt(adt, _) if adt.is_enum()
                    ) =>
            {
                Ok(())
            }
            _ => Err("multi-level projection outside fragment".to_string()),
        },
        _ => Err("multi-level projection outside fragment".to_string()),
    }
}

fn operand_ok<'tcx>(body: &Body<'tcx>, op: &Operand<'tcx>) -> Result<(), String> {
    match op {
        Operand::Copy(p) | Operand::Move(p) => place_ok(body, p),
        Operand::Constant(c) => {
            // Unit constants ride with unit locals (`_0 = const ()` in every unit-returning
            // body) — same totality argument as `local_ty_ok`.
            // Trust (wave-str, `&str`-LITERAL-RETURN FLIP): a shared `&str` literal const the shim
            // re-emits for `_0 = const "..."`. Read-only rodata, total for every replayed pass
            // (PromoteTemps-inert, no drop glue); the comparator's injective `c:str:<bytes>`
            // observable already discriminates the value. Shared `&str` only (a `&mut`/raw-ptr
            // const is never emitted here).
            let is_str_ref = matches!(
                c.const_.ty().kind(),
                ty::Ref(_, inner, m) if inner.is_str() && m.is_not()
            );
            if scalar_ok(c.const_.ty()) || c.const_.ty().is_unit() || is_str_ref {
                Ok(())
            } else {
                Err("non-scalar constant outside fragment".to_string())
            }
        }
        // Trust-fork operand variant (deferred runtime-check payload) — the shim never emits
        // it and its semantics are outside the flip fragment: fail closed.
        Operand::RuntimeChecks(_) => Err("RuntimeChecks operand outside fragment".to_string()),
    }
}

fn term_name(kind: &TerminatorKind<'_>) -> &'static str {
    match kind {
        TerminatorKind::Goto { .. } => "Goto",
        TerminatorKind::SwitchInt { .. } => "SwitchInt",
        TerminatorKind::Return => "Return",
        TerminatorKind::Unreachable => "Unreachable",
        TerminatorKind::Assert { .. } => "Assert",
        TerminatorKind::Call { .. } => "Call",
        TerminatorKind::Drop { .. } => "Drop",
        _ => "Other",
    }
}

/// Allow-list verification that the derived body is inside the slice-1 fragment — the property
/// that makes every pass from `Built` to `Runtime(Optimized)` (including the mandatory final
/// validation) total over it. Anything else fails closed.
fn gate_derived_body<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Result<(), String> {
    if body.coroutine.is_some() {
        return Err("derived body carries coroutine info".to_string());
    }
    // `_0` and every non-arg local must be in the scalar/checked-pair fragment. ARG locals
    // (1..=arg_count) may additionally carry an opaque non-scalar type (slice 3) — but then
    // the local must be proven NEVER MENTIONED below, so no pass can observe more than its
    // declaration.
    let mut opaque_args: Vec<Local> = Vec::new();
    // Trust (wave-8a): ref/raw-ptr arg locals that the derived body may FORWARD into a call
    // argument (`g(r)`, the `s.method()` receiver). Held separately from `opaque_args` because
    // they are allowed to be MENTIONED — but only as a bare call argument (`ref_args_forward_only`).
    let mut fwd_ref_args: HashSet<Local> = HashSet::new();
    // Trust (wave-F): by-value Drop-free STRUCT arg locals whose scalar fields are READ. Allowed to
    // be MENTIONED, but only as a scalar field read `(_s.k)` (`struct_args_read_only`), so the shim
    // never emits a bare whole-struct `Copy`/`Move` of a possibly-non-`Copy` struct (→ MIR ICE).
    let mut struct_val_args: HashSet<Local> = HashSet::new();
    // Trust (wave-V): by-value FIELDLESS enum arg locals whose discriminant tag is READ. Allowed to
    // be MENTIONED, but only as a bare `Rvalue::Discriminant(_e)` (`enum_args_disc_read_only`), so
    // the shim never emits a whole-enum `Copy`/`Move` (out of the scalar fragment) or a field read.
    let mut enum_val_args: HashSet<Local> = HashSet::new();
    // Trust (wave-30): shared-ref temps holding an interior borrow passed to a call
    // (`_tmp = &((*_arg).f); g(move _tmp)`) — admitted below by their single-def/single-call-arg-use
    // shape (`interior_arg_temps` proves total place-mentions == 2, so no other observation exists).
    let interior_arg_temps = interior_arg_temps(body);
    // Trust (wave-GH2): NON-arg struct temps holding a call result consumed whole by a later call
    // (`_2 = Arguments::from_str(..); _print(move _2)`). Copy + Drop-free + concrete only
    // (`temp_struct_ty_ok`); every mention confined by `struct_temps_confined` below.
    let mut struct_val_temps: HashSet<Local> = HashSet::new();
    for (l, decl) in body.local_decls.iter_enumerated() {
        if local_ty_ok(decl.ty) {
            continue;
        }
        // Trust (wave-30): an interior-arg temp `_tmp: &FieldTy`. Its borrow-into-temp + single
        // call-arg move are admitted by the `Rvalue::Ref` arm + `RefArgForwardGuard`; the
        // `interior_arg_temps` scan proved it is used ONLY there (mentions == 2), so every pass is
        // total over it exactly as over the wave-29 return-borrow local.
        if interior_arg_temps.contains(&l) {
            continue;
        }
        // Trust (wave-15): the RETURN local `_0` of a SHARED-ref identity return
        // (`fn(..) -> &T { param }`). The shim forwards a ref param straight into `_0`
        // (`_0 = copy _p; return`), reproducing built's `_0 = copy _1` byte-for-byte. ONLY `&T`
        // (shared): a `&mut T` / raw-ptr `_0` fails this `m.is_not()` guard and falls through to
        // the fail-closed arm (it is not an arg), so those returns stay clean-only (DerivedAgreed
        // but flip-rejected) pending a dedicated `&mut` burn-in. The ABI gate below independently
        // re-pins derived `_0` to the built `_0` type, so admitting it here loses no checking.
        if l.as_usize() == 0 && matches!(decl.ty.kind(), ty::Ref(_, _, m) if m.is_not()) {
            continue;
        }
        // Trust (wave-D): the RETURN local `_0` of a Drop-free aggregate constructor-return
        // (`fn new(..) -> Struct { Struct { .. } }`). The shim assigns `_0 = Rvalue::Aggregate(...)`
        // (from the collapsed InsertField chain); the ABI gate below re-pins `_0` to the built
        // struct type, and the `Rvalue::Aggregate` statement arm certifies the field operands are
        // fragment-scalar. Concrete Copy && !needs_drop struct only (`agg_return_ty_ok`) — a
        // Drop-bearing / non-Copy / generic struct falls through to the fail-closed arm (clean-only).
        if l.as_usize() == 0 && agg_return_ty_ok(tcx, decl.ty) {
            continue;
        }
        let is_arg = l.as_usize() >= 1 && l.as_usize() <= body.arg_count;
        if is_arg && matches!(decl.ty.kind(), ty::Ref(..) | ty::RawPtr(..)) {
            fwd_ref_args.insert(l);
        } else if is_arg && opaque_arg_ty_ok(decl.ty) {
            opaque_args.push(l);
        } else if is_arg && arg_struct_ty_ok(tcx, decl.ty) {
            // Trust (wave-F): a by-value Drop-free struct param whose scalar fields are READ. Its
            // scalar field reads are certified by `place_ok` (widened Field arm) + the shim's
            // `ir_scalar_of_body` gate; `struct_args_read_only` (below) proves EVERY mention is such
            // a read, so the shim never emits a bare whole-struct `Copy` (ill-typed for non-`Copy`).
            struct_val_args.insert(l);
        } else if is_arg && arg_enum_ty_ok(tcx, decl.ty) {
            // Trust (wave-V): a by-value fieldless enum param whose discriminant tag is READ. The
            // shim declares the derived arg with this exact built enum type (ABI byte-identical),
            // re-emits `_d = Discriminant(_e)` for the producer's `extractfield 0`, and reshapes the
            // discriminant switch to built's exhaustive form. `enum_args_disc_read_only` (below)
            // proves EVERY mention is such a bare discriminant read, so the shim never emits an
            // ill-typed whole-enum `Copy`/`Move` or a field/downcast read.
            enum_val_args.insert(l);
        } else if !is_arg && l.as_usize() != 0 && temp_struct_ty_ok(tcx, decl.ty) {
            // Trust (wave-GH2): a NON-arg struct TEMP holding a call result consumed whole by a
            // later call — the `println!` desugar's `_2: Arguments<'_>` (the wave-J callee-return
            // admission already types the call DEST with this struct; this arm lets the local DECL
            // through on the same Copy + Drop-free footing). `struct_temps_confined` (below)
            // proves every mention is the call-dest write, a whole non-mutating use, or a scalar
            // field read — nothing a replayed pass could act on beyond ordinary total MIR.
            struct_val_temps.insert(l);
        } else {
            return Err(format!("local type outside fragment: {:?}", decl.ty));
        }
    }
    if !opaque_args.is_empty() {
        let mentioned = mentioned_locals(body);
        for l in &opaque_args {
            if mentioned.contains(l) {
                return Err(format!("opaque non-scalar arg local {l:?} is mentioned in the body"));
            }
        }
    }
    // A never-mentioned ref arg trivially satisfies this; a forwarded one must appear ONLY as a
    // bare call argument (a projected/aggregate/other use is an observation → fail closed).
    if !fwd_ref_args.is_empty() {
        ref_args_forward_only(body, &fwd_ref_args, &interior_arg_temps)?;
    }
    // Trust (wave-S → B10 stage 2, RETIRED): the read+write order-mix fail-close that stood here
    // guarded the OLD order-blind canonical form (a shared-ref READ folded into the value channel
    // + a SORTED `mem[...]` suffix canonicalized reorder-blind). B10 made the memory channel
    // ORDERED — the comparator's memseq epoch stamps (`deref@m{n}`, `call@m{n}`) render any
    // read/write/call reorder as a DIFFERENT canonical string (the historical perturbation burn-in
    // flipped the mix smoke DerivedAgreed → DerivedMismatch), so a mix body's DerivedAgreed is now
    // ORDER-SENSITIVE and the containment gate is redundant. See
    // [[canonical-form-is-order-blind-across-observable-channels]] (retired for this mix).
    // Trust (wave-F): every by-value struct param admitted above must appear ONLY as a scalar field
    // read `(_s.k)` — never as a bare whole-struct operand (the shim would render it `Copy(_s)`,
    // ill-typed for a non-`Copy` struct → MIR-validation ICE) and never as a write target.
    if !struct_val_args.is_empty() {
        struct_args_read_only(tcx, body, &struct_val_args)?;
    }
    // Trust (wave-V): every by-value fieldless enum param admitted above must appear ONLY as a bare
    // `Rvalue::Discriminant(_e)` read — never taken by value / by field / by downcast (the shim
    // reconstructs only the discriminant read + the reshaped switch).
    if !enum_val_args.is_empty() {
        enum_args_disc_read_only(body, &enum_val_args)?;
    }
    // Trust (wave-GH2): every struct call-result temp admitted above must appear ONLY as the bare
    // call-destination write, a whole non-mutating use (call-arg move), or a scalar field read.
    if !struct_val_temps.is_empty() {
        struct_temps_confined(body, &struct_val_temps)?;
    }
    let n_blocks = body.basic_blocks.len();
    let target_ok = |bb: BasicBlock| -> Result<(), String> {
        if bb.as_usize() < n_blocks {
            Ok(())
        } else {
            Err(format!("branch target {bb:?} out of range"))
        }
    };
    for (_bb, data) in body.basic_blocks.iter_enumerated() {
        // The shim never creates cleanup blocks (its unwind convention is the
        // post-`RemoveNoopLandingPads` normal form, `Continue` everywhere) — a cleanup
        // block here would mean unwind structure the fragment argument does not cover.
        if data.is_cleanup {
            return Err("derived body carries a cleanup block".to_string());
        }
        for stmt in &data.statements {
            match &stmt.kind {
                StatementKind::Assign(assign) => {
                    let (place, rvalue) = &**assign;
                    place_ok(body, place)?;
                    match rvalue {
                        // Trust: rust 1.99 — `Rvalue::Use` carries a `WithRetag` payload; the
                        // flag does not change the value-use the fragment certifies.
                        Rvalue::Use(op, _) => operand_ok(body, op)?,
                        Rvalue::BinaryOp(_, ops) => {
                            operand_ok(body, &ops.0)?;
                            operand_ok(body, &ops.1)?;
                        }
                        Rvalue::UnaryOp(_, op) => operand_ok(body, op)?,
                        // Trust (wave-7): integer/bool → integer cast (`x as T`, `bool as T`).
                        // The shim emits EXACTLY `Rvalue::Cast(CastKind::IntToInt, op, dst)` for
                        // these (`to_mir`, general integer cast) and the dest is a scalar the
                        // fragment already admits. Every pass the flip replays is total over an
                        // `IntToInt` cast between scalars — it is the same statement built MIR
                        // carries for `as` (verified byte-for-byte via `-Zdump-mir`). Float / ptr
                        // cast kinds fall to the catch-all and fail closed (defence-in-depth: the
                        // shim never emits them and a float local is already rejected by
                        // `local_ty_ok`).
                        Rvalue::Cast(CastKind::IntToInt, op, ty) => {
                            operand_ok(body, op)?;
                            if !scalar_ok(*ty) {
                                return Err(format!("cast dest type outside fragment: {ty:?}"));
                            }
                        }
                        // Trust (wave-29/29b/30, interior-borrow FLIP): the SHARED borrows the shim
                        // emits. Two borrowed-place shapes are admitted:
                        //  * the interior borrow `_dst = &((*_p).field)` ([Deref, Field(scalar)], an
                        //    arg-ref base) — `_dst` is an interior-arg temp (wave-30
                        //    `_t = &((*_p).f); g(move _t)`) or the return temp (wave-29b
                        //    `_t = &((*_1).K)`), `place_ok` certifies the projection (reusing wave-24);
                        //  * the reborrow `_0 = &(*_t)` ([Deref] on `_t ∈ interior_arg_temps`) — the
                        //    wave-29b return getter's tail, reproducing built's `_0 = &(*_2)` exactly.
                        // The `_p`-as-borrow-base / `_t`-as-reborrow-base observations are admitted by
                        // the `RefArgForwardGuard`; the differential's `iref(a{p},K)` observable pins
                        // the field (a wrong K → mismatch → no flip). `PromoteTemps` finds ZERO
                        // candidates — the borrow is through a runtime PARAM, not a const/static — so
                        // the fragment's borrow-free invariant is relaxed to exactly these shapes.
                        Rvalue::Ref(_, BorrowKind::Shared, borrowed)
                            if place.projection.is_empty()
                                && (place.local == RETURN_PLACE
                                    || interior_arg_temps.contains(&place.local)) =>
                        {
                            // The `_0 = &(*_t)` reborrow of an interior temp (wave-29b): `[Deref]` on a
                            // certified interior temp is total (a plain deref of a `&FieldTy` temp the
                            // `interior_arg_temps` scan proved is single-use). Any other borrowed place
                            // must pass `place_ok` (the `[Deref, Field(scalar)]` interior shape).
                            let is_temp_reborrow = borrowed.projection.len() == 1
                                && matches!(borrowed.projection[0], ProjectionElem::Deref)
                                && interior_arg_temps.contains(&borrowed.local);
                            if !is_temp_reborrow {
                                place_ok(body, borrowed)?;
                            }
                        }
                        // Trust (wave-D, Drop-free aggregate constructor-return FLIP): the single
                        // `_0 = Rvalue::Aggregate(Adt(did, 0, args), [scalar fields])` the shim emits
                        // for a constructor return. Admitted ONLY into the bare RETURN_PLACE, variant
                        // 0, a single-variant STRUCT (not enum/union — `active_field` None,
                        // `is_struct()`), gated Drop-free (`agg_return_ty_ok` on `_0`); every field
                        // operand must be a fragment scalar/unit (`operand_ok`, which also rejects a
                        // projected/aggregate operand). The comparator's ORDERED `agg(...)` observable
                        // discriminates field order/values; `ElaborateDrops`/`AbortUnwindingCalls` are
                        // no-ops on a Drop-free aggregate, so every pass Built→Runtime(Optimized) is
                        // total over it. (`box_patterns` is not enabled → destructure via `matches!`.)
                        // Trust (wave-L): a TUPLE constructor return `_0 = (f0, f1, ...)` =
                        // `Rvalue::Aggregate(AggregateKind::Tuple, [scalar fields])` is admitted on the
                        // SAME footing as the struct case — `agg_return_ty_ok` gates `_0` to a
                        // non-empty all-scalar tuple (Drop-free by construction), the comparator's
                        // ORDERED `agg(tuple,[..])` observable discriminates field order/values, and a
                        // scalar tuple has no drop glue so pass-totality holds. No Adt identity to pin.
                        // Trust (wave-Y/wave-YP, enum CONSTRUCTION FLIP): `_0 = Aggregate(Adt(did,
                        // variant_k, args), [payload?])` — an enum variant construction. ANY variant
                        // index (unlike the struct case's forced 0). Wave-Y: EMPTY fields (`E::V`).
                        // Wave-YP: 0 OR 1 field (`Some(x)`/`Ok(v)`/`None`), over a concrete legacy
                        // scalar-payload enum (`agg_return_ty_ok` gates `_0` to `.len()<=1` + Drop-free).
                        // No drop glue (`!needs_drop`), so pass-totality holds; the comparator's
                        // `agg(adt:E:k,[op])` observable pins the variant + payload (a wrong k/payload →
                        // mismatch → no flip). The payload operand (if any) passes `operand_ok` below.
                        Rvalue::Aggregate(kind, fields)
                            if place.local == RETURN_PLACE
                                && place.projection.is_empty()
                                && (matches!(
                                    &**kind,
                                    AggregateKind::Adt(did, variant, _, user_ty, active_field)
                                        if variant.as_u32() == 0
                                            && user_ty.is_none()
                                            && active_field.is_none()
                                            && tcx.adt_def(*did).is_struct()
                                ) || matches!(&**kind, AggregateKind::Tuple)
                                    || matches!(
                                        &**kind,
                                        AggregateKind::Adt(did, variant, _, user_ty, active_field)
                                            if user_ty.is_none()
                                                && active_field.is_none()
                                                && fields.len() <= 1
                                                && tcx.adt_def(*did).is_enum()
                                                && tcx.adt_def(*did).variants().iter().all(|v| v.fields.len() <= 1)
                                                // Trust (wave-YP): the operand count MUST equal the
                                                // constructed variant's field arity (0 niladic / 1 payload).
                                                // Built MIR guarantees this, but assert it so a malformed
                                                // aggregate can never be admitted.
                                                && fields.len() == tcx.adt_def(*did).variant(*variant).fields.len()
                                                // Trust (#111 defense-in-depth): the aggregate's enum DefId
                                                // MUST be the RETURN_PLACE's own enum (unreachable divergence
                                                // — the shim always sources `did` from `ret_rty` — but assert
                                                // it so a future shim change can never flip a cross-enum
                                                // aggregate that `agg(adt:{name})` alone might not catch).
                                                && matches!(
                                                    body.local_decls[RETURN_PLACE].ty.kind(),
                                                    ty::Adt(ret_adt, _) if ret_adt.did() == *did
                                                )
                                    ))
                                && agg_return_ty_ok(tcx, body.local_decls[RETURN_PLACE].ty) =>
                        {
                            for op in fields {
                                operand_ok(body, op)?;
                            }
                        }
                        // Trust (wave-V, fieldless-enum discriminant-read FLIP): `_d =
                        // Discriminant(_e)` where `_e` is a by-value fieldless enum arg (admitted by
                        // `arg_enum_ty_ok`, and `enum_args_disc_read_only` certifies THIS is its only
                        // mention) read at the bare local (empty projection), and `_d` is a fragment
                        // scalar (the discriminant temp, `discriminant_ty` = a fixed-width int the
                        // `local_ty_ok` gate already classified). The comparator's `disc(ty, place)`
                        // observable pins the source; the reshaped SwitchInt (tag set + Unreachable
                        // otherwise, both already admitted terminators) reconstructs the dispatch.
                        Rvalue::Discriminant(d)
                            if d.projection.is_empty()
                                && enum_val_args.contains(&d.local)
                                && scalar_ok(body.local_decls[place.local].ty) => {}
                        other => {
                            return Err(format!("rvalue outside fragment: {other:?}"));
                        }
                    }
                }
                // Trust (wave-24b + wave-29b): a storage marker the shim reproduces to match built's
                // `StorageLive(_k); ...; StorageDead(_k)` so the marker channel (`canon_markers`)
                // agrees → `markers_exact=true` → the flip fires at `-O`. The local is EITHER a
                // SCALAR temp the fragment already admits (wave-24b field-store operand temp;
                // `local_ty_ok` classified every local above) OR an interior-borrow reborrow temp
                // `_t: &FieldTy` (wave-29b return getter, `StorageLive(t); t = &((*_1).K); _0 = &(*t);
                // StorageDead(t)`, reproducing built's reborrow-temp marker sequence). The
                // `interior_arg_temps` scan proved that ref temp is used ONLY as its single borrow-def
                // + reborrow (value-mentions == 2), so every pass is total over the marker exactly as over
                // a scalar one (`RemoveStorageMarkers` deletes them at `-O0`; codegen emits matching
                // `llvm.lifetime` intrinsics at `-O` since the marker sequences coincide).
                StatementKind::StorageLive(l) | StatementKind::StorageDead(l) => {
                    if !scalar_ok(body.local_decls[*l].ty) && !interior_arg_temps.contains(l) {
                        return Err(format!(
                            "storage marker on non-scalar local _{}",
                            l.as_usize()
                        ));
                    }
                }
                other => return Err(format!("statement outside fragment: {other:?}")),
            }
        }
        let Some(term) = &data.terminator else {
            return Err("derived block without terminator".to_string());
        };
        match &term.kind {
            TerminatorKind::Goto { target } => target_ok(*target)?,
            TerminatorKind::SwitchInt { discr, targets } => {
                operand_ok(body, discr)?;
                for t in targets.all_targets() {
                    target_ok(*t)?;
                }
            }
            TerminatorKind::Assert { cond, msg, target, unwind, .. } => {
                operand_ok(body, cond)?;
                if !matches!(unwind, UnwindAction::Continue) {
                    return Err("assert with non-Continue unwind".to_string());
                }
                // Trust (wave-U, div/rem FLIP): the div-guard asserts the shim now emits —
                // `DivisionByZero`/`RemainderByZero` (div-by-zero) and `Overflow(Div/Rem, ..)`
                // (signed MIN/-1). The div-by-zero kinds carry no `BinOp`; `assert_key` classes
                // them for the pairwise span-stitch. OOB (`BoundsCheck`) and `Neg`-overflow stay
                // excluded (the shim never emits them).
                if !matches!(
                    &**msg,
                    AssertKind::Overflow(..)
                        | AssertKind::DivisionByZero(..)
                        | AssertKind::RemainderByZero(..)
                ) {
                    return Err("assert message outside fragment".to_string());
                }
                target_ok(*target)?;
            }
            // Trust (wave-6): direct calls — admitted ONLY in the exact shape the shim
            // emits (`to_mir`, DIRECT CALLS). PASS-TOTALITY: every pass the flip replays
            // (`SimplifyCfg`, `PromoteTemps` [borrow-free ⇒ zero candidates],
            // `run_analysis_to_runtime_passes` — `CleanupPostBorrowck`,
            // `RemoveNoopLandingPads`, `CriticalCallEdges`, `ElaborateDrops`,
            // `AbortUnwindingCalls`, `Lint(KnownPanicsLint)`, …) and the unchanged
            // `optimized_mir` tail (incl. `MentionedItems`, which is what keeps the callee
            // collected for mono, and the mandatory `Runtime(Optimized)` validation)
            // processes built call bodies on essentially every real compilation — the
            // admitted shape is a strict SUBSET of what those passes consume daily.
            // `KnownPanicsLint` treats a call destination as unknown (never
            // const-propagates through it), so a call can never arm the double-lint hazard
            // the const-trap gate defuses — that gate is unaffected by calls (call results
            // are not `Inst::Const` values, so `is_const` never admits them).
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
                call_source: _,
                fn_span: _,
            } => {
                // The func operand: a constant of interned `FnDef` type. Trust (wave-C): its
                // GenericArgs may now be non-empty but must be CONCRETE (param/infer-free) — the
                // site spelling `Operand::function_handle(tcx, site_def_id, site_args)` for a
                // concrete-mono callee (`id::<i32>`, `Tr::tm` at Self=i32). A polymorphic FnDef
                // (unsubstituted `ty::Param`/infer) is rejected as defense-in-depth — the shim never
                // emits one, and the comparator's `raw_call_channel` already pinned this interned
                // `FnDef` to built's, so this gate is a redundant allow-list, not the discriminator.
                match func {
                    Operand::Constant(c) => match c.const_.ty().kind() {
                        ty::FnDef(_, fn_args) => {
                            if fn_args.has_non_region_param() || fn_args.has_non_region_infer() {
                                return Err(
                                    "call func FnDef with non-concrete GenericArgs".to_string()
                                );
                            }
                        }
                        other => {
                            return Err(format!("call func type outside fragment: {other:?}"));
                        }
                    },
                    _ => return Err("non-constant call func operand".to_string()),
                }
                for a in args.iter() {
                    operand_ok(body, &a.node)?;
                    // Trust (wave-GH2, operand-spelling PARITY fail-close): a whole-struct call
                    // arg spelled `Operand::Copy` whose layout is MEMORY-ABI (indirectly passed)
                    // is REJECTED. Built spells a one-shot rvalue temp `Move`; codegen_ssa gives a
                    // memory-backed `Copy` arg a defensive fresh-alloca+memcpy while `Move` passes
                    // the address — so a Copy-spelled memory-ABI arg is correct-but-byte-DIVERGENT
                    // vs built (adversarial finding, wave-GH2). LEDGER L8's Move≡Copy fold is
                    // therefore NOT codegen-blind for this one shape; this gate enforces the
                    // parity the comparator cannot see. Unresolved types are rejected before the
                    // layout query as well, since normalization may re-enter a query already on the
                    // compiler stack. The shim's Call arm re-spells the one-shot
                    // temp case to `Move` (parity fix); anything that still reaches here as a
                    // memory-ABI whole-struct `Copy` — a multi-use temp, a future admission —
                    // stays clean-only. Immediate/Pair (`ScalarPair`) struct `Copy` args (wave-K's
                    // V2) are codegen-identical under either spelling and stay admitted. A layout
                    // ERROR also rejects (fail-closed).
                    if let Operand::Copy(p) = &a.node {
                        if p.projection.is_empty() {
                            let aty = body.local_decls[p.local].ty;
                            if matches!(aty.kind(), ty::Adt(adt, _) if adt.is_struct()) {
                                if !crate::layout_query_is_reentrant_safe(aty) {
                                    return Err(format!(
                                        "whole-struct Copy call arg with memory ABI \
                                         (operand-kind parity): {aty:?}"
                                    ));
                                }
                                let te = ty::TypingEnv::fully_monomorphized();
                                match tcx.layout_of(te.as_query_input(aty)) {
                                    Ok(l)
                                        if !matches!(
                                            l.backend_repr,
                                            rustc_abi::BackendRepr::Memory { .. }
                                        ) => {}
                                    _ => {
                                        return Err(format!(
                                            "whole-struct Copy call arg with memory ABI \
                                             (operand-kind parity): {aty:?}"
                                        ));
                                    }
                                }
                            }
                        }
                    }
                }
                // Destination: a BARE local (the shim's fresh temp; its type already
                // passed the local-decl gate above — scalar/unit only).
                if !destination.projection.is_empty() {
                    return Err("projected call destination outside fragment".to_string());
                }
                place_ok(body, destination)?;
                let Some(target) = target else {
                    return Err("diverging call (no return target)".to_string());
                };
                target_ok(*target)?;
                if !matches!(unwind, UnwindAction::Continue) {
                    return Err("call with non-Continue unwind".to_string());
                }
            }
            TerminatorKind::Return | TerminatorKind::Unreachable => {}
            other => {
                return Err(format!("terminator outside fragment: {}", term_name(other)));
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Assert-span stitching from the built sibling
// ---------------------------------------------------------------------------

/// The blocks holding `Assert` terminators, in the canonical DFS preorder the differential's
/// comparator uses (successor order: switch targets in listed order then otherwise; assert
/// success edge; goto target). Fails closed on any terminator outside the fragment set.
fn asserts_in_dfs_order<'tcx>(body: &Body<'tcx>) -> Result<Vec<BasicBlock>, String> {
    let n_blocks = body.basic_blocks.len();
    let mut seen = vec![false; n_blocks];
    let mut asserts: Vec<BasicBlock> = Vec::new();
    let mut stack = vec![START_BLOCK];
    while let Some(bb) = stack.pop() {
        if bb.as_usize() >= n_blocks {
            return Err(format!("branch target {bb:?} out of range"));
        }
        if seen[bb.as_usize()] {
            continue;
        }
        seen[bb.as_usize()] = true;
        let Some(term) = &body.basic_blocks[bb].terminator else {
            return Err("block without terminator".to_string());
        };
        let succs: Vec<BasicBlock> = match &term.kind {
            TerminatorKind::Goto { target } => vec![*target],
            TerminatorKind::SwitchInt { targets, .. } => {
                let mut v: Vec<BasicBlock> = targets.iter().map(|(_, t)| t).collect();
                v.push(targets.otherwise());
                v
            }
            TerminatorKind::Assert { target, .. } => {
                asserts.push(bb);
                vec![*target]
            }
            // Trust (wave-6): calls interleave with asserts in call-carrying bodies; the
            // canonical preorder continues through the call's RETURN target — the same
            // successor rule the differential's walks use, so `DerivedAgreed`'s 1:1 assert
            // correspondence carries over verbatim. The normal sibling is post-
            // `run_analysis_to_runtime_passes` here (`RemoveNoopLandingPads` already
            // normalized the built `Cleanup(lone-resume)` to `Continue`), and the derived
            // body is `Continue` by construction — anything else is out of fragment.
            TerminatorKind::Call { target, unwind, .. } => {
                if !matches!(unwind, UnwindAction::Continue) {
                    return Err("call with non-Continue unwind in span stitching".to_string());
                }
                let Some(target) = target else {
                    return Err("diverging call in span stitching".to_string());
                };
                vec![*target]
            }
            TerminatorKind::Return | TerminatorKind::Unreachable => vec![],
            other => {
                return Err(format!(
                    "terminator outside fragment in span stitching: {}",
                    term_name(other)
                ));
            }
        };
        // Reverse so the FIRST successor is visited first (preorder).
        for s in succs.into_iter().rev() {
            if s.as_usize() < n_blocks && !seen[s.as_usize()] {
                stack.push(s);
            } else if s.as_usize() >= n_blocks {
                return Err(format!("branch target {s:?} out of range"));
            }
        }
    }
    Ok(asserts)
}

/// The KIND-identity of one fragment assert for pairwise matching. Trust (wave-U): the div-by-zero
/// kinds (`DivisionByZero`/`RemainderByZero`) carry no `BinOp`, so a bare `mir::BinOp` key can no
/// longer name every admitted assert — this enum distinguishes them. Op-carrying overflow keeps its
/// `BinOp` so an `Add`-overflow can never be span-stitched onto a `Div`-overflow.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
enum AssertClass {
    Overflow(rustc_middle::mir::BinOp),
    DivByZero,
    RemByZero,
}

/// The identity of one assert for pairwise matching: the kind class + expected polarity.
fn assert_key<'tcx>(kind: &TerminatorKind<'tcx>) -> Result<(AssertClass, bool), String> {
    let TerminatorKind::Assert { expected, msg, .. } = kind else {
        return Err("non-assert in assert list".to_string());
    };
    let class = match &**msg {
        AssertKind::Overflow(op, _, _) => AssertClass::Overflow(*op),
        AssertKind::DivisionByZero(_) => AssertClass::DivByZero,
        AssertKind::RemainderByZero(_) => AssertClass::RemByZero,
        other => return Err(format!("assert kind outside fragment: {other:?}")),
    };
    Ok((class, *expected))
}

/// Verify the derived body's assert sequence matches built (count + kind + polarity, DFS
/// order) — the fail-closed structural half of what was `stitch_assert_spans`. The SPAN
/// OVERWRITE it also performed is gone (C2-spans): the derived asserts now carry their own
/// locations from `InstrNode.span` consumption, and the panic-`Location` probe
/// (flip-on vs flip-off `file:line:col` equality on an overflow) is the gate that keeps them
/// honest. The parity checks stay because they are evidence, not metadata: `DerivedAgreed`
/// proved the sequences identical in canonical order, and this re-checks it at the seam
/// anyway — any mismatch rejects the flip. Returns the number of verified asserts.
fn verify_assert_parity<'tcx>(
    derived: &Body<'tcx>,
    normal: &Body<'tcx>,
) -> Result<usize, String> {
    let d_asserts = asserts_in_dfs_order(derived)?;
    let n_asserts = asserts_in_dfs_order(normal)?;
    if d_asserts.len() != n_asserts.len() {
        return Err(format!(
            "assert count mismatch: derived {} vs built {}",
            d_asserts.len(),
            n_asserts.len()
        ));
    }
    // Collect (key, span) from the built side first — no aliasing with the derived mutation.
    let mut stitched: Vec<(AssertClass, bool, Span)> = Vec::with_capacity(n_asserts.len());
    for bb in &n_asserts {
        let term = normal.basic_blocks[*bb].terminator();
        let (class, expected) = assert_key(&term.kind)?;
        stitched.push((class, expected, term.source_info.span));
    }
    for (i, bb) in d_asserts.iter().enumerate() {
        let (n_class, n_expected, _span) = stitched[i];
        let term = derived.basic_blocks[*bb].terminator();
        let (d_class, d_expected) = assert_key(&term.kind)?;
        if d_class != n_class || d_expected != n_expected {
            return Err(format!(
                "assert #{i} kind mismatch: derived ({d_class:?}, {d_expected}) vs \
                 built ({n_class:?}, {n_expected})"
            ));
        }
    }
    Ok(d_asserts.len())
}

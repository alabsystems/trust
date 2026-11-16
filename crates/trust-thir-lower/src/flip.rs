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
//!      require the source-loop-HIR/source-place proof binding absent from
//!      TrustIr's debug-oriented spans, scopes, and parameter names.
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
//! 3. **Stitches assert spans** from the built sibling: TrustIr carries instruction spans,
//!    but an `Assert`'s exact span is user-visible — it becomes the panic `Location` in the
//!    emitted object — and the differential already authenticated its built counterpart.
//!    Both bodies' asserts are collected
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

use rustc_middle::mir::visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor};
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
    let Some(flip_registry::GreenBody {
        module,
        callees,
        lineage,
        enum_fold_switch_blocks,
        source_header_correspondence,
    }) = flip_registry::take(tcx, def)
    else {
        return FlipAttempt::NotCandidate;
    };

    // This opaque witness is minted only after the mir_built hook compared the
    // carried source-loop association against compiler-stamped built headers
    // at equal, unique canonical CFG roles.  Recheck its private seal against
    // this entry's lineage at the consume seam: a future registry producer
    // that only validates the self-sealed module cannot forge the capability.
    if !source_header_correspondence.authenticates(lineage) {
        return rejected("source-loop header correspondence was not independently authenticated");
    }

    // Trust (L1, artifact-lineage attestation): RE-DERIVE the lineage digest from the taken
    // (module, ledger) and require it to equal the value minted at `record_green`. The
    // registry is in-process Session state, so this is not a tamper check — it is the
    // standing obligation that the digest the flip event publishes actually describes the
    // bytes the flip is about to compile. A future producer that mutates a registry entry
    // between record and take, or a `GreenBody` minted by some other path with a digest that
    // does not match its own payload, fails CLOSED here (falls back to built MIR) instead of
    // emitting an attestation for an object that no longer exists. Cost is one module
    // serialization per FLIPPED body — the small set, not every lowered body.
    match crate::lineage::body_lineage_digest(
        crate::lineage::DefinitionIdentity::from_def_id(tcx, def.to_def_id()),
        &module,
        &callees,
    ) {
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
    if !flip_registry::source_place_provenance_allows_flip(tcx, def, &module) {
        return rejected(
            "first-class loop contract source-loop/place provenance is missing, stale, or invalid",
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
        // Trust (enum-switch provenance): the hook-time set, taken from the SAME registry entry as
        // the module — not re-derived, because THIR is gone at this seam. Identical threading to
        // the differential's call site, so the flip consumes exactly the body the hook compared.
        &enum_fold_switch_blocks,
    ) {
        Ok(lowering) => lowering.body,
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
    // Trust (F2, 2026-09-29): the ABI also decides WHICH argument local is spread. Built MIR
    // sets `spread_arg = Some(_last)` for a non-closure `extern "rust-call"` body (a user `impl
    // Fn*`), the derived body is `Body::new` (`None`), and codegen maps arguments to the FnAbi
    // by it: the flip ICEd in `arg_local_refs` on a valid program. REFUSES MORE: a body whose
    // spread differs is simply not flipped.
    if let Some(reason) = spread_arg_refusal(body.spread_arg, normal.spread_arg) {
        return rejected(reason);
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

/// Trust (F2): the spread-argument half of the ABI gate, `TyCtxt`-free so it is tested whole.
/// `None` iff the derived body spreads exactly the argument built spreads (including neither).
pub(crate) fn spread_arg_refusal(derived: Option<Local>, built: Option<Local>) -> Option<String> {
    (derived != built)
        .then(|| format!("spread_arg mismatch: derived {derived:?} vs built {built:?}"))
}

// ---------------------------------------------------------------------------
// Gate 1: const-trap (lint-hazard) over the trust-ir Module
// ---------------------------------------------------------------------------

/// Reject the flip when any potentially trapping instruction has statically-constant deciding
/// operands (see module docs: `KnownPanicsLint` would fire twice, at a coarser span).
pub(crate) fn const_trap_gate(module: &Module) -> Result<(), String> {
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
    // Trust (2026-10-03, shift-count mask): the producer now masks a checks-OFF shift count
    // (`emit_masked_shift_count`: `amount & (BITS - 1)`), so a literal count reaches the shift
    // as the `And` of two constants rather than as a constant. The derived MIR is still the
    // bare `Shl(x, const k)` (`to_mir::shift_masked_unit`), so the `KnownPanicsLint` hazard is
    // unchanged: a shift by such an `And` stays a const-amount shift here, exactly as before
    // the mask existed.
    let mut masked_const_vals: HashSet<ValueId> = HashSet::new();
    for blk in &func.blocks {
        for node in &blk.body {
            if let Inst::BinOp { op: BinOp::And, lhs, rhs, .. } = &node.inst {
                if is_const(lhs) && is_const(rhs) {
                    masked_const_vals.extend(node.results.iter().copied());
                }
            }
        }
    }
    for blk in &func.blocks {
        for node in &blk.body {
            match &node.inst {
                Inst::Overflow { lhs, rhs, .. } if is_const(lhs) && is_const(rhs) => {
                    return Err("const-const checked arithmetic (KnownPanicsLint would re-fire \
                                on the derived body)"
                        .to_string());
                }
                Inst::BinOp { op: BinOp::Shl | BinOp::LShr | BinOp::AShr, rhs, .. }
                    if is_const(rhs) || masked_const_vals.contains(rhs) =>
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
    // Trust (wave-EP): arm-binding payload temps `_t = &(((*_arg) as V).k); _x = copy (*_t)` — the
    // `_arg`-as-borrow-base is admitted, on the same footing as the wave-30 interior borrow.
    payload_temps: &'a HashSet<Local>,
    // Trust (wave-AF): address-forward temps `_t = &((*_arg).k)` / `_t = &(((*_arg) as V).k);
    // g(copy _t)` over a NON-scalar field — the `_arg`-as-borrow-base is admitted on the same
    // footing as the wave-30 interior borrow and the wave-EP payload borrow. Scalarity of the
    // field never entered this guard's property: what it protects is that the reference VALUE
    // `_arg` does not escape, and what is stored in `_t` is a borrow of the REFERENT's field.
    addr_fwd_temps: &'a HashSet<Local>,
    // Trust (wave-W3): relay SOURCES — `_b = &(((*_arg) as V).k)` whose single use is the
    // reborrow `_g = &(*_b)` rather than a call argument. Same borrow places, same
    // forward-only property, and for the same reason: what is stored in `_b` is a borrow of the
    // REFERENT's field, not the reference value `_arg`.
    relay_srcs: &'a HashSet<Local>,
    // Trust (wave-FR): call-forward reborrow temps `_t = &[mut] (*_arg); f(move _t)` — the
    // `_arg`-as-borrow-base is admitted on the same footing as the wave-30 interior borrow:
    // what is stored in `_t` is built's own reborrow of the REFERENT, `call_fwd_reborrow_temps`
    // proved (mentions == 2) its only other appearance is one bare call-argument move, and the
    // callee receives exactly what forwarding `_arg` bare (the wave-8a form) already hands it.
    call_fwd_temps: &'a HashSet<Local>,
    // Trust (lane S1F): explicit-borrow pair INNER locals `_u = &((*_arg).0)` — the same
    // interior borrow place as wave-AF's, the same forward-only property for the same reason
    // (what is stored in `_u` is a borrow of the REFERENT's field), and `field_pair_temps`
    // proved (mentions == 2) its only other appearance is the pair's own `_t = &(*_u)`.
    field_pair_inners: &'a HashSet<Local>,
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
            // Trust (T2): the shared-ref DISCRIMINANT READ `_d = Discriminant((*_p))` — `_p` a ref
            // arg, source projection EXACTLY `[Deref]`. This is the by-ref twin of wave-V's
            // by-VALUE enum discriminant read, which never reaches this guard at all (a by-value
            // enum param is not a ref arg, so `ref_args` does not contain it). Without this arm
            // the by-ref lane passed the DIFFERENTIAL (`derived_mir: agreed`, `markers_exact`) and
            // then fell back here at `stage="gate"` with "ref arg _1 used outside a forwarding
            // call argument" — measured on `disc_byref` / `E::is_a` / `Level::is_zero_shallow`.
            //
            // Admitting it does not weaken the forward-only property. The read is a PURE
            // OBSERVATION of the referent: it writes a fresh discriminant temp, mutates nothing
            // through `_p`, and cannot alias-escape `_p` (no `Ref` rvalue, no aggregate). The
            // destination is required NOT to be a ref arg, so `_d` cannot be the arg itself, and
            // the SOURCE projection is pinned to exactly `[Deref]` — a projected
            // `Discriminant((*_p).f)` or a bare `Discriminant(_p)` still walks and flags. Every
            // other mention of `_p` in the body is unaffected and still has to be a forwarded call
            // argument.
            if let Rvalue::Discriminant(src) = rvalue {
                if !self.ref_args.contains(&place.local)
                    && self.ref_args.contains(&src.local)
                    && src.projection.len() == 1
                    && matches!(src.projection[0], ProjectionElem::Deref)
                {
                    return;
                }
            }
            // Trust (T2c): the shared-ref PAYLOAD READ `_x = copy (((*_p) as V).k)` — the
            // companion to the discriminant read above, and the shape the shim's by-ref payload
            // recognizer emits. Projection pinned to exactly `[Deref, Downcast, Field]`; anything
            // longer, shorter, or differently shaped still walks and flags.
            //
            // Like the discriminant read this is a PURE OBSERVATION of the referent: it copies a
            // scalar OUT of the enum payload into a fresh local. It cannot mutate through `_p`
            // (a copy, not a store) and cannot let the reference VALUE escape (the operand is the
            // payload scalar, not `_p`) — which is the property `ref_args_forward_only` exists to
            // protect. The destination must not itself be a ref arg.
            if let Rvalue::Use(Operand::Copy(src) | Operand::Move(src), _) = rvalue {
                if !self.ref_args.contains(&place.local)
                    && self.ref_args.contains(&src.local)
                    && src.projection.len() == 3
                    && matches!(src.projection[0], ProjectionElem::Deref)
                    && matches!(src.projection[1], ProjectionElem::Downcast(..))
                    && matches!(src.projection[2], ProjectionElem::Field(..))
                {
                    return;
                }
            }
            // Trust (wave-EP): the shared-ref ARM-BINDING BORROW `_t = &(((*_p) as V).k)` — the
            // same `[Deref, Downcast, Field]` place as the payload READ above, borrowed instead of
            // copied, which is what rustc's own match lowering emits for an arm binding. `_t` must
            // be a certified `payload_borrow_temps` local, i.e. one the mentions == 2 scan proved
            // is defined here and read exactly once through a bare `[Deref]`; the destination must
            // not itself be a ref arg.
            //
            // It does not weaken the forward-only property. The reference VALUE `_p` does not
            // escape: what is stored in `_t` is a borrow of the referent's PAYLOAD FIELD, not `_p`,
            // and `_t`'s only other mention is the scalar read `_x = copy (*_t)` — a pure
            // observation that mutates nothing through `_p` and hands nothing on. Anything longer,
            // shorter or differently shaped still walks and flags.
            if let Rvalue::Ref(_, BorrowKind::Shared, src) = rvalue {
                if !self.ref_args.contains(&place.local)
                    && place.projection.is_empty()
                    && self.payload_temps.contains(&place.local)
                    && self.ref_args.contains(&src.local)
                    && src.projection.len() == 3
                    && matches!(src.projection[0], ProjectionElem::Deref)
                    && matches!(src.projection[1], ProjectionElem::Downcast(..))
                    && matches!(src.projection[2], ProjectionElem::Field(..))
                {
                    return;
                }
            }
            // Trust (wave-AF): the ADDRESS-FORWARD borrow `_t = &((*_p).k)` /
            // `_t = &(((*_p) as V).k)` where the field is NOT a fragment scalar. Same two places
            // as the wave-29/30 interior borrow and the wave-EP payload borrow above, and the
            // forward-only property is untouched for the same reason both of those give: what is
            // stored in `_t` is a borrow of the REFERENT's field, not the reference value `_p`,
            // and `addr_forward_temps` proved (mentions == 2) that `_t`'s only other appearance is
            // a bare call argument — so `_p` is not observed beyond being the borrow base and
            // nothing derived from it is dereferenced here. `_t` must be a certified
            // `addr_forward_temps` local and the destination must not itself be a ref arg;
            // anything longer, shorter or differently shaped still walks and flags.
            if let Rvalue::Ref(_, BorrowKind::Shared, src) = rvalue {
                if !self.ref_args.contains(&place.local)
                    && place.projection.is_empty()
                    && (self.addr_fwd_temps.contains(&place.local)
                        || self.relay_srcs.contains(&place.local)
                        || self.field_pair_inners.contains(&place.local))
                    && self.ref_args.contains(&src.local)
                    && matches!(
                        src.projection.as_slice(),
                        [ProjectionElem::Deref, ProjectionElem::Field(..)]
                            | [
                                ProjectionElem::Deref,
                                ProjectionElem::Downcast(..),
                                ProjectionElem::Field(..)
                            ]
                    )
                {
                    return;
                }
            }
            // Trust (wave-FR): the CALL-FORWARD REBORROW `_t = &[mut] (*_p)` — `_t` a certified
            // `call_fwd_reborrow_temps` local (single def, single bare call-arg move, total
            // mentions == 2), source projection EXACTLY `[Deref]` on a ref arg, destination not
            // itself a ref arg. The reference VALUE `_p` does not escape: what is stored in `_t`
            // is built's own reborrow of the referent, and `_t`'s only other mention is the one
            // `Move` the call consumes — the same handing-through the wave-8a bare forward
            // already performs. Anything longer, shorter or differently shaped still walks and
            // flags.
            if let Rvalue::Ref(_, _, src) = rvalue {
                if !self.ref_args.contains(&place.local)
                    && place.projection.is_empty()
                    && self.call_fwd_temps.contains(&place.local)
                    && self.ref_args.contains(&src.local)
                    && src.projection.len() == 1
                    && matches!(src.projection[0], ProjectionElem::Deref)
                {
                    return;
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

/// Trust (wave-FR, 2026-08-21): the CALL-FORWARD REBORROW TEMPS — the `&T`/`&mut T` ARGUMENT
/// temps the shim's call-forward marker plan mints for a single-block tail call
/// (`to_mir::plan_call_fwd_markers`): `StorageLive(_t); _t = &(*_p); f(move _t); StorageDead(_t)`,
/// byte-for-byte built's own `as_operand` -> `as_temp` reborrow of a forwarded reference
/// parameter (measured verbatim with `-Zdump-mir=built` on
/// `fn a_def_eq(s: &C, a: &E, b: &E) -> bool { s.imp3(a, b) }`:
/// `_4 = &(*_1); _5 = &(*_2); _6 = &(*_3); _0 = C::imp3(move _4, move _5, move _6)`).
///
/// This is the flip gate's INDEPENDENT admission of that shape, on the standing pattern of
/// [`interior_arg_temps`]. "Plan-minted" is the EMITTER's side of the bargain (only
/// `to_mir`'s `mf_mark_call_fwd` can open the pair, and it refuses any value its plan does
/// not name); the two structural clauses are re-proven HERE, from the finished body alone:
///
///   * **the single def is `_t = &(*_p)` / `_t = &mut (*_p)`** — a `Rvalue::Ref` whose
///     borrowed place is projection EXACTLY `[Deref]` on an ARG local (`1..=arg_count`),
///     whose borrow kind MATCHES `_t`'s own declared mutability (`Shared` for `&T`,
///     `Mut { Default }` for `&mut T` — a one-sided mismatch is refused), and whose base
///     `_p` is declared at exactly `_t`'s own region-erased type (the emitter minted `_t`
///     at the callee's declared input type and separately proved the forwarded place
///     already had it; requiring it here makes the gate's proof independent of the
///     emitter's). The pointee must be CONCRETE and THIN ([`thin_shared_pointee_ok`]) —
///     the clause wave-AF owed and for the same reason: an unsized pointee makes `_t` a
///     WIDE `(data, metadata)` pair and the fragment models pointer metadata nowhere. A
///     fat `&str` reborrow stays refused (measured refusals: `mode::{impl#3,4}::fmt`).
///   * **the single use is ONE bare `Operand::Move(_t)` CALL argument, and TOTAL
///     value-mentions == 2** (the def dest + that one move; storage markers are `NonUse`
///     and uncounted, exactly as in [`interior_arg_temps`]). The mentions clause is the
///     airtight single-use guarantee: a temp that is read through, stored through,
///     re-borrowed, returned, or consumed twice appears a 3rd time and is REFUSED — the
///     same posture as [`is_ref_enum_payload_read`]: an address in transit, provably never
///     observed by this body beyond the one move, never reachable by a store.
///
/// PASS-TOTALITY is wave-30's argument unchanged: `&T`/`&mut T` is `!needs_drop` and a
/// borrow mints no move path (`ElaborateDrops` finds nothing to elaborate), `PromoteTemps`
/// finds ZERO candidates (the borrow is through a runtime param, not a const), and
/// mentions == 2 means no replayed pass can observe a shape the shim did not emit. The
/// `&mut` reborrow adds no new obligation HERE: this body neither reads nor writes through
/// `_t` (mentions == 2), and the referent mutation happens in the CALLEE — exactly as it
/// already does when the same body forwards `_p` bare, the wave-8a form this emission
/// replaces, whose `&mut` forward [`ref_args_forward_only`] already admits.
fn call_fwd_reborrow_temps<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> HashSet<Local> {
    // Total VALUE mentions per local (storage markers / debuginfo are NonUse and uncounted).
    let mut mentions: HashMap<Local, u32> = HashMap::new();
    struct MentionCounter<'a> {
        m: &'a mut HashMap<Local, u32>,
    }
    impl<'tcx> Visitor<'tcx> for MentionCounter<'_> {
        fn visit_local(&mut self, l: Local, ctx: PlaceContext, _loc: Location) {
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
    // The reborrow def `_t = &[mut] (*_p)`; the single use, a bare `Operand::Move` call argument.
    let mut borrow_def: HashMap<Local, u32> = HashMap::new();
    let mut callarg_move: HashMap<Local, u32> = HashMap::new();
    for (_bb, data) in body.basic_blocks.iter_enumerated() {
        for stmt in &data.statements {
            if let StatementKind::Assign(assign) = &stmt.kind {
                let (place, rvalue) = &**assign;
                if !place.projection.is_empty() {
                    continue;
                }
                let l = place.local;
                let is_arg = |x: Local| x.as_usize() >= 1 && x.as_usize() <= body.arg_count;
                if l == RETURN_PLACE || is_arg(l) {
                    continue;
                }
                let ty::Ref(_, pointee, m) = *body.local_decls[l].ty.kind() else {
                    continue;
                };
                let Rvalue::Ref(_, bk, borrowed) = rvalue else {
                    continue;
                };
                // Borrow kind must MATCH the temp's own declared mutability — one-sided
                // mismatches (a `Mut` borrow into a `&T` temp, or vice versa) are refused.
                let kind_matches = match bk {
                    BorrowKind::Shared => m.is_not(),
                    BorrowKind::Mut { kind: rustc_middle::mir::MutBorrowKind::Default } => {
                        m.is_mut()
                    }
                    _ => false,
                };
                if !kind_matches {
                    continue;
                }
                if borrowed.projection.len() == 1
                    && matches!(borrowed.projection[0], ProjectionElem::Deref)
                    && is_arg(borrowed.local)
                    // `_p`'s declared type must BE `_t`'s (region-erased): the reborrow
                    // reproduces the parameter's own reference, nothing narrower or wider.
                    && tcx.erase_and_anonymize_regions(body.local_decls[borrowed.local].ty)
                        == tcx.erase_and_anonymize_regions(body.local_decls[l].ty)
                    // Concrete + THIN pointee — the wave-AF clause, owed identically here.
                    && thin_shared_pointee_ok(tcx, pointee)
                {
                    *borrow_def.entry(l).or_default() += 1;
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
            // EXACTLY one reborrow def, TOTAL value-mentions == 2, and the one use is a bare
            // call-argument move. Any store / second use / projected use / re-borrow adds a
            // 3rd mention and REFUSES the local — fail closed.
            d == 1 && mentions.get(l) == Some(&2) && callarg_move.get(l) == Some(&1)
        })
        .map(|(l, _)| *l)
        .collect()
}

/// Trust (lane EM, 2026-08-21): facts certifying one `&str`-LITERAL ARGUMENT PAIR — the two
/// locals built mints for a `&str` literal call argument, and the shim's CF_STR emission
/// (`to_mir`'s `mf_mark_call_fwd_lit` leg) now reproduces:
///
/// ```text
/// _u = const "lit";    // the literal's own local            (&str, shared)
/// _t = &(*_u);         // the argument temp: a FAT reborrow  (&str, shared)
/// f(.., move _t, ..);  // the one use: a bare call-argument move
/// ```
///
/// Keeping the facts as one value makes the production predicate directly executable in unit
/// tests, exactly as `CallDestFwdFacts` and `RelayPairFacts` do — the `mentions == 2` walls
/// are not left as uncommitted producer observations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct StrLitPairFacts {
    /// `_t = &(*_u)` SHARED borrow defs of the arg temp (its ONLY admitted def kind).
    borrow_defs: u32,
    /// `_u = const "..."` (`&str`-typed constant) defs of the literal local (its ONLY admitted
    /// def kind).
    const_defs: u32,
    /// TOTAL value-mentions of `_t` (storage markers are `NonUse` and uncounted).
    t_mentions: u32,
    /// TOTAL value-mentions of `_u`.
    u_mentions: u32,
    /// Bare `Operand::Move` call-argument uses of `_t`.
    t_callarg_moves: u32,
    /// `_t` and `_u` are the SAME local (`_t = &(*_t)`) — refused explicitly rather than
    /// assumed absent, on the pattern of wave-FR's self-referential clause.
    self_pair: bool,
}

fn str_lit_pair_admits(f: StrLitPairFacts) -> bool {
    f.borrow_defs == 1
        && f.const_defs == 1
        && f.t_mentions == 2
        && f.u_mentions == 2
        && f.t_callarg_moves == 1
        && !f.self_pair
}

/// Trust (lane EM, 2026-08-21): the `&str`-LITERAL ARGUMENT PAIRS — the wave-WB deferred
/// admission, taken now that the CF_STR emission fires (the `call_fwd_arg_admits` literal
/// clause demanded an adjustment-free `&str` literal, a shape built never mints temps for; see
/// the corrected clause in `to_mir.rs`). Byte-for-byte built's own two-local spelling, measured
/// verbatim with `-Zdump-mir=built` on `fn e3(f: &mut Formatter<'_>) -> fmt::Result
/// { f.write_str("hello") }`:
///
/// ```text
/// StorageLive(_3); StorageLive(_4); _4 = const "hello"; _3 = &(*_4);
/// _0 = Formatter::<'_>::write_str(move _2, move _3) -> bb1;
/// bb1: StorageDead(_3); StorageDead(_2); StorageDead(_4);
/// ```
///
/// This is the ONE place the fragment admits a fat `&str` BORROW DEF, and the walls are the
/// same two the wave-WB `str_fat` call-dest class already carries, plus the pair link:
///
///   * **the arg temp's single def is `_t = &(*_u)`** — a SHARED `Rvalue::Ref`, projection
///     EXACTLY `[Deref]`, whose base `_u` is a NON-arg local declared at exactly `_t`'s own
///     region-erased `&str` type;
///   * **the literal local's single def is `_u = const "..."`** — a `&str`-typed
///     `Operand::Constant`, the exact constant `operand_ok`'s wave-str arm already admits
///     (read-only rodata, `PromoteTemps`-inert, no drop glue);
///   * **TOTAL value-mentions == 2 on BOTH locals**: `_u` is the const def + the one borrow
///     base; `_t` is the borrow def + ONE bare `Operand::Move` call argument. A deref-read, a
///     store, a re-borrow, a second forward, a projected use — each is a THIRD mention on its
///     local and REFUSES the pair, fail closed. So the fat `(ptr, len)` pair rides only in
///     transit: it is never split, inspected or stored, and the pointee `str` produces no
///     value in this body (wave-AF's argument, verbatim; `&str` is `Copy` + `!needs_drop`, so
///     `ElaborateDrops` finds nothing). `PromoteTemps` is the one pass with an opinion on a
///     borrow-of-const shape, and it requires the borrow base to be a promotable CONST PLACE —
///     `_u` is a runtime local with a non-promotable sibling use (the call move via `_t`), and
///     the differential separately re-checks the finished body against built, so a promotion
///     divergence can only cost the flip, never ship.
///
/// `&[T]`, `&dyn Trait`, `&mut str` and every other wide pointee stay refused: this set admits
/// `str` SHARED, both locals, pair-linked, and nothing else.
#[derive(Default)]
struct StrLitPairs {
    /// The argument temps `_t = &(*_u); f(move _t)`.
    args: HashSet<Local>,
    /// The literal locals `_u = const "..."`.
    lits: HashSet<Local>,
}

impl StrLitPairs {
    fn contains(&self, l: &Local) -> bool {
        self.args.contains(l) || self.lits.contains(l)
    }
}

fn str_lit_pair_temps<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> StrLitPairs {
    // Total VALUE mentions per local (storage markers / debuginfo are NonUse and uncounted).
    let mut mentions: HashMap<Local, u32> = HashMap::new();
    struct MentionCounter<'a> {
        m: &'a mut HashMap<Local, u32>,
    }
    impl<'tcx> Visitor<'tcx> for MentionCounter<'_> {
        fn visit_local(&mut self, l: Local, ctx: PlaceContext, _loc: Location) {
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
    let is_arg = |x: Local| x.as_usize() >= 1 && x.as_usize() <= body.arg_count;
    let is_shared_str = |l: Local| {
        matches!(*body.local_decls[l].ty.kind(), ty::Ref(_, pointee, m)
            if m.is_not() && pointee.is_str())
    };
    // The candidate defs: `_t = &(*_u)` pair links, `_u = const "..."` literal defs, and the
    // bare call-argument moves.
    let mut borrow_def: HashMap<Local, (u32, Local)> = HashMap::new();
    let mut const_def: HashMap<Local, u32> = HashMap::new();
    let mut callarg_move: HashMap<Local, u32> = HashMap::new();
    for (_bb, data) in body.basic_blocks.iter_enumerated() {
        for stmt in &data.statements {
            if let StatementKind::Assign(assign) = &stmt.kind {
                let (place, rvalue) = &**assign;
                if !place.projection.is_empty() {
                    continue;
                }
                let l = place.local;
                if l == RETURN_PLACE || is_arg(l) || !is_shared_str(l) {
                    continue;
                }
                match rvalue {
                    Rvalue::Ref(_, BorrowKind::Shared, borrowed)
                        if borrowed.projection.len() == 1
                            && matches!(borrowed.projection[0], ProjectionElem::Deref)
                            && !is_arg(borrowed.local)
                            && borrowed.local != RETURN_PLACE
                            // `_u`'s declared type must BE `_t`'s (region-erased): the
                            // reborrow reproduces the literal's own `&str`, nothing else.
                            && tcx.erase_and_anonymize_regions(
                                body.local_decls[borrowed.local].ty,
                            ) == tcx.erase_and_anonymize_regions(body.local_decls[l].ty) =>
                    {
                        let e = borrow_def.entry(l).or_insert((0, borrowed.local));
                        e.0 += 1;
                        e.1 = borrowed.local;
                    }
                    Rvalue::Use(Operand::Constant(c), _)
                        if matches!(c.const_.ty().kind(), ty::Ref(_, inner, m)
                            if m.is_not() && inner.is_str()) =>
                    {
                        *const_def.entry(l).or_default() += 1;
                    }
                    _ => {}
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
    let mut out = StrLitPairs::default();
    for (t, &(defs, u)) in borrow_def.iter() {
        let facts = StrLitPairFacts {
            borrow_defs: defs,
            const_defs: const_def.get(&u).copied().unwrap_or(0),
            t_mentions: mentions.get(t).copied().unwrap_or(0),
            u_mentions: mentions.get(&u).copied().unwrap_or(0),
            t_callarg_moves: callarg_move.get(t).copied().unwrap_or(0),
            self_pair: *t == u,
        };
        if str_lit_pair_admits(facts) {
            out.args.insert(*t);
            out.lits.insert(u);
        }
    }
    out
}

/// Trust (lane S1F, 2026-08-22): facts certifying one EXPLICIT-BORROW FIELD PAIR — the two
/// locals built mints for `&p.0` passed under the reborrow coercion (the derived `Ord::cmp`'s
/// `::core::cmp::Ord::cmp(&self.0, &other.0)`), which the call-forward plan's pair form now
/// reproduces with built's own storage spans:
///
/// ```text
/// _u = &((*_p).0: F);   // the field borrow's own local: an interior borrow of a ref ARG
/// _t = &(*_u);          // the argument temp: a bare reborrow of `_u`
/// f(.., move _t, ..);   // the one use: a bare call-argument move
/// ```
///
/// Kept as one value so the production predicate is directly executable in unit tests, exactly
/// as `StrLitPairFacts` and `RelayPairFacts` are.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FieldPairFacts {
    /// `_u = &((*_p).k)` interior-borrow defs of the inner local (its ONLY admitted def kind).
    u_borrow_defs: u32,
    /// TOTAL value-mentions of `_u` (storage markers are `NonUse` and uncounted).
    u_mentions: u32,
    /// `_t = &(*_u)` SHARED reborrow defs of the arg temp (its ONLY admitted def kind).
    t_reborrow_defs: u32,
    /// TOTAL value-mentions of `_t`.
    t_mentions: u32,
    /// Bare `Operand::Move` call-argument uses of `_t`.
    t_callarg_moves: u32,
    /// `_t` and `_u` are the SAME local — refused explicitly rather than assumed absent.
    self_pair: bool,
}

fn field_pair_admits(f: FieldPairFacts) -> bool {
    f.u_borrow_defs == 1
        && f.u_mentions == 2
        && f.t_reborrow_defs == 1
        && f.t_mentions == 2
        && f.t_callarg_moves == 1
        && !f.self_pair
}

/// Trust (lane S1F): the admitted explicit-borrow field pairs, as two linked sets.
#[derive(Default)]
struct FieldPairs {
    /// The argument temps `_t = &(*_u); f(move _t)`.
    args: HashSet<Local>,
    /// The inner locals `_u = &((*_p).k)`.
    inners: HashSet<Local>,
}

impl FieldPairs {
    fn contains(&self, l: &Local) -> bool {
        self.args.contains(l) || self.inners.contains(l)
    }
}

/// Trust (lane S1F, 2026-08-22): the EXPLICIT-BORROW FIELD PAIRS — `_u = &((*_p).k: F)` (the
/// wave-AF address-forward def, verbatim: a NON-arg, non-`_0` local declared `&F` SHARED with
/// [`thin_shared_pointee_ok`], borrowing an [`interior_field_ty`] place of a ref ARG whose field
/// type equals `F`) whose SINGLE use is the bare reborrow `_t = &(*_u)` into a NON-arg, non-`_0`
/// local declared at `_u`'s exact region-erased type, whose SINGLE use is ONE bare
/// `Operand::Move` call argument — TOTAL value-mentions == 2 on BOTH locals. This is
/// [`str_lit_pair_temps`]' pair-linked discipline with [`addr_forward_temps`]' def in the inner
/// slot: the address rides `_u` -> `_t` -> the callee and is never dereferenced, stored or split
/// in this body; `&F` is `Copy` and `!needs_drop`; `PromoteTemps` finds no candidate (the borrow
/// is through a runtime param). FAIL-CLOSED: any third mention on either local refuses both.
fn field_pair_temps<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> FieldPairs {
    let mut mentions: HashMap<Local, u32> = HashMap::new();
    struct MentionCounter<'a> {
        m: &'a mut HashMap<Local, u32>,
    }
    impl<'tcx> Visitor<'tcx> for MentionCounter<'_> {
        fn visit_local(&mut self, l: Local, ctx: PlaceContext, _loc: Location) {
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
    let is_arg = |x: Local| x.as_usize() >= 1 && x.as_usize() <= body.arg_count;
    let mut inner_def: HashMap<Local, u32> = HashMap::new();
    let mut reborrow_def: HashMap<Local, (u32, Local)> = HashMap::new();
    let mut callarg_move: HashMap<Local, u32> = HashMap::new();
    for (_bb, data) in body.basic_blocks.iter_enumerated() {
        for stmt in &data.statements {
            let StatementKind::Assign(assign) = &stmt.kind else { continue };
            let (place, rvalue) = &**assign;
            if !place.projection.is_empty() {
                continue;
            }
            let l = place.local;
            if l == RETURN_PLACE || is_arg(l) {
                continue;
            }
            let ty::Ref(_, pointee, m) = *body.local_decls[l].ty.kind() else { continue };
            if !m.is_not() || !thin_shared_pointee_ok(tcx, pointee) {
                continue;
            }
            let Rvalue::Ref(_, BorrowKind::Shared, borrowed) = rvalue else { continue };
            if borrowed.projection.len() == 1
                && matches!(borrowed.projection[0], ProjectionElem::Deref)
                && !is_arg(borrowed.local)
                && borrowed.local != RETURN_PLACE
                && tcx.erase_and_anonymize_regions(body.local_decls[borrowed.local].ty)
                    == tcx.erase_and_anonymize_regions(body.local_decls[l].ty)
            {
                let e = reborrow_def.entry(l).or_insert((0, borrowed.local));
                e.0 += 1;
                e.1 = borrowed.local;
            } else if is_arg(borrowed.local) && interior_field_ty(body, borrowed) == Some(pointee) {
                *inner_def.entry(l).or_default() += 1;
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
    let mut out = FieldPairs::default();
    for (t, &(defs, u)) in reborrow_def.iter() {
        let facts = FieldPairFacts {
            u_borrow_defs: inner_def.get(&u).copied().unwrap_or(0),
            u_mentions: mentions.get(&u).copied().unwrap_or(0),
            t_reborrow_defs: defs,
            t_mentions: mentions.get(t).copied().unwrap_or(0),
            t_callarg_moves: callarg_move.get(t).copied().unwrap_or(0),
            self_pair: *t == u,
        };
        if field_pair_admits(facts) {
            out.args.insert(*t);
            out.inners.insert(u);
        }
    }
    out
}

/// Trust (wave-WB8, 2026-08-21): facts certifying one CHAIN IN-TRANSIT REBORROW PAIR — the
/// two locals the chain-forward emission (`to_mir::plan_chain_fwd_markers`) mints for a
/// REFERENCE-returning inner call whose result feeds the final call:
///
/// ```text
/// _u = name(move _w);  // the inner call's destination      (&str / &Level, shared)
/// _t = &(*_u);         // the outer argument temp: a reborrow, at the successor's entry
/// f(.., move _t, ..);  // the one use: a bare call-argument move
/// ```
///
/// Keeping the facts as one value makes the production predicate directly executable in unit
/// tests, exactly as `StrLitPairFacts` and `CallDestFwdFacts` do — the `mentions == 2` walls
/// are not left as uncommitted producer observations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct TransitPairFacts {
    /// `_t = &(*_u)` SHARED borrow defs of the arg temp (its ONLY admitted def kind).
    borrow_defs: u32,
    /// Bare call-DESTINATION defs of the transit local (its ONLY admitted def kind).
    u_calldest_defs: u32,
    /// TOTAL value-mentions of `_t` (storage markers are `NonUse` and uncounted).
    t_mentions: u32,
    /// TOTAL value-mentions of `_u`.
    u_mentions: u32,
    /// Bare `Operand::Move` call-argument uses of `_t`.
    t_callarg_moves: u32,
    /// `_t` and `_u` are the SAME local (`_t = &(*_t)`) — refused explicitly rather than
    /// assumed absent, on the pattern of wave-FR's self-referential clause.
    self_pair: bool,
}

fn transit_pair_admits(f: TransitPairFacts) -> bool {
    f.borrow_defs == 1
        && f.u_calldest_defs == 1
        && f.t_mentions == 2
        && f.u_mentions == 2
        && f.t_callarg_moves == 1
        && !f.self_pair
}

/// Trust (wave-WB8, 2026-08-21): the CHAIN IN-TRANSIT REBORROW PAIRS — wave-WB's lone
/// call-dest forward temp with the forward link REPLACED by built's own reborrow, which is
/// what the chain-forward marker emission now reproduces (measured verbatim,
/// `-Zdump-mir=built`, probes/em3.rs `Ax::fmt`:
/// `_5 = Ax::name(move _6) -> bb1; bb1: _4 = &(*_5); …; _0 = write_str(move _3, move _4)`).
///
/// The soundness argument is the two parents' arguments, composed, with the pair link making
/// each half's base the other half:
///
///   * **`_u`'s single def is a bare CALL DESTINATION and its single use is the reborrow
///     base** — wave-WB's `calldest_forward_temps` admits the same def kind with a
///     call-argument use; here the use is the borrow base of `_t`'s def, and the
///     `mentions == 2` wall proves there is no other observation of `_u` in the body.
///   * **`_t`'s single def is `_t = &(*_u)` SHARED and its single use is ONE bare
///     `Operand::Move` call argument** — wave-FR's `call_fwd_reborrow_temps` admits the same
///     shape with an ARG base; the base here is the pair's own certified `_u`, declared at
///     exactly `_t`'s region-erased type.
///
/// So both locals are an address in transit: no value of the pointee is ever materialised in
/// this body, its drop glue and width are not this fragment's business (`&T` is `Copy` +
/// `!needs_drop`, `ElaborateDrops` finds nothing), and `PromoteTemps` finds no candidate (the
/// borrow base is a runtime call result, never a const place). TWO POINTEE CLASSES, exactly
/// wave-WB's: THIN concrete (`&Level`), and EXACTLY `str` (`<AxiomId as Display>::fmt`'s
/// `&str` in transit) — the fat `(ptr, len)` pair rides as an opaque immediate the
/// `mentions == 2` walls prove is never split, inspected or stored. `&[T]`, `&dyn Trait`,
/// `&mut` anything and every other pointee stay refused.
#[derive(Default)]
struct TransitPairs {
    /// The outer argument temps `_t = &(*_u); f(move _t)`.
    args: HashSet<Local>,
    /// The in-transit call destinations `_u = g(..)`.
    dests: HashSet<Local>,
}

impl TransitPairs {
    fn contains(&self, l: &Local) -> bool {
        self.args.contains(l) || self.dests.contains(l)
    }
}

fn transit_pair_temps<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> TransitPairs {
    // Total VALUE mentions per local (storage markers / debuginfo are NonUse and uncounted).
    let mut mentions: HashMap<Local, u32> = HashMap::new();
    struct MentionCounter<'a> {
        m: &'a mut HashMap<Local, u32>,
    }
    impl<'tcx> Visitor<'tcx> for MentionCounter<'_> {
        fn visit_local(&mut self, l: Local, ctx: PlaceContext, _loc: Location) {
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
    let is_arg = |x: Local| x.as_usize() >= 1 && x.as_usize() <= body.arg_count;
    // A shared reference whose pointee is concrete THIN, or exactly `str` — the two measured
    // classes, the same split wave-WB's call-dest set carries.
    let pointee_ok = |l: Local| match *body.local_decls[l].ty.kind() {
        ty::Ref(_, pointee, m) if m.is_not() => {
            thin_shared_pointee_ok(tcx, pointee) || matches!(pointee.kind(), ty::Str)
        }
        _ => false,
    };
    let mut borrow_def: HashMap<Local, (u32, Local)> = HashMap::new();
    let mut calldest_def: HashMap<Local, u32> = HashMap::new();
    let mut callarg_move: HashMap<Local, u32> = HashMap::new();
    for (_bb, data) in body.basic_blocks.iter_enumerated() {
        for stmt in &data.statements {
            if let StatementKind::Assign(assign) = &stmt.kind {
                let (place, rvalue) = &**assign;
                if !place.projection.is_empty() {
                    continue;
                }
                let l = place.local;
                if l == RETURN_PLACE || is_arg(l) || !pointee_ok(l) {
                    continue;
                }
                if let Rvalue::Ref(_, BorrowKind::Shared, borrowed) = rvalue {
                    if borrowed.projection.len() == 1
                        && matches!(borrowed.projection[0], ProjectionElem::Deref)
                        && !is_arg(borrowed.local)
                        && borrowed.local != RETURN_PLACE
                        // `_u`'s declared type must BE `_t`'s (region-erased): the reborrow
                        // reproduces the inner call's own reference, nothing else.
                        && tcx.erase_and_anonymize_regions(body.local_decls[borrowed.local].ty)
                            == tcx.erase_and_anonymize_regions(body.local_decls[l].ty)
                    {
                        let e = borrow_def.entry(l).or_insert((0, borrowed.local));
                        e.0 += 1;
                        e.1 = borrowed.local;
                    }
                }
            }
        }
        if let Some(term) = &data.terminator {
            if let TerminatorKind::Call { args, destination, .. } = &term.kind {
                if destination.projection.is_empty()
                    && destination.local != RETURN_PLACE
                    && !is_arg(destination.local)
                {
                    *calldest_def.entry(destination.local).or_default() += 1;
                }
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
    let mut out = TransitPairs::default();
    for (t, &(defs, u)) in borrow_def.iter() {
        let facts = TransitPairFacts {
            borrow_defs: defs,
            u_calldest_defs: calldest_def.get(&u).copied().unwrap_or(0),
            t_mentions: mentions.get(t).copied().unwrap_or(0),
            u_mentions: mentions.get(&u).copied().unwrap_or(0),
            t_callarg_moves: callarg_move.get(t).copied().unwrap_or(0),
            self_pair: *t == u,
        };
        if transit_pair_admits(facts) {
            out.args.insert(*t);
            out.dests.insert(u);
        }
    }
    out
}

/// Trust (wave-WB, 2026-08-21): facts certifying one LONE CALL-DESTINATION FORWARD temp — the
/// call-dest sibling of the wave-FR reborrow admission, and the "lone source" the W3 relay
/// refuses BY DESIGN (`relay_pair_admits` requires a forward reborrow PAIR with
/// `source_callarg_uses == 0`; this class has NO forward and EXACTLY ONE call-arg use, so the
/// two sets are disjoint by construction). Keeping the facts as one value makes the production
/// predicate directly executable in unit tests, exactly as `RelayPairFacts` does — the
/// `mentions == 2` wall is not left as an uncommitted producer observation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CallDestFwdFacts {
    /// Bare call-DESTINATION defs of the local (its ONLY admitted def kind — a borrow def or a
    /// plain-assign def lands the local in a different set or in the fail-closed arm).
    calldest_defs: u32,
    /// TOTAL value-mentions (storage markers are `NonUse` and uncounted, exactly as in
    /// [`interior_arg_temps`]).
    mentions: u32,
    /// Bare `Operand::Copy|Move` call-argument uses.
    callarg_uses: u32,
    /// The local appears as an ARGUMENT of the very call that defines it (`_t = f(move _t)`) —
    /// a shape real MIR cannot produce initialized (the argument is read before the destination
    /// is written), REFUSED explicitly rather than assumed absent, on the pattern of wave-FR's
    /// self-referential `_f = &(*_f)` clause.
    self_feed: bool,
}

fn calldest_fwd_admits(f: CallDestFwdFacts) -> bool {
    f.calldest_defs == 1 && f.mentions == 2 && f.callarg_uses == 1 && !f.self_feed
}

/// Trust (wave-WB, 2026-08-21): the LONE CALL-DEST FORWARD temps — NON-arg, non-`_0` locals
/// declared `&P` SHARED whose SINGLE def is a bare CALL DESTINATION and whose SINGLE use is ONE
/// bare `Copy|Move` CALL ARGUMENT, with TOTAL value-mentions == 2:
///
/// ```text
/// _t = f(..);          // the only def: a bare call destination
/// g(move _t);          // the only use: a bare call argument
/// ```
///
/// This is `<LevelArc as PartialEq>::eq` (`%2 = deref(self); %3 = deref(other);
/// Level::eq(%2, %3)`), `<LevelArc as Debug>::fmt`, and `expr::kind::arc_eq` — the wall-B
/// "lone-source relay" class of the never-flip partition
/// (`data/crystal_never_flip_partition_2026-08-20.json`, clean 5bdb4ee6a).
///
/// The soundness argument is wave-W3's accessor-destination argument with the forward link
/// REPLACED by a use kind two older waves already admit:
///   * the DEF is the `Call` arm's bare-local destination — the exact def kind the W3 relay
///     already admits for its source (`root_def`, call-destination arm), certified by
///     `place_ok`'s empty-projection arm on the destination;
///   * the USE is a bare call argument — the exact use kind wave-30/wave-AF/wave-FR already
///     admit for their ref temps (`operand_ok` on a bare local place);
///   * **TOTAL value-mentions == 2 is the load-bearing wall**: a deref-read, a store through,
///     a re-borrow, a second forward, a projected use — each is a THIRD mention and REFUSES,
///     fail closed. So `_t` is an address in transit: no value of `P` is ever materialised in
///     this body, which is why `P`'s drop glue and width are not this fragment's business
///     (wave-AF's argument, verbatim). `&P` is `Copy` + `!needs_drop`, so
///     `ElaborateDrops`/`AbortUnwindingCalls` are no-ops over it, and `PromoteTemps` finds no
///     candidate (the def is a call, not a borrow — there is NO `Rvalue::Ref` to promote).
///
/// TWO POINTEE CLASSES, held as separate sets so each carries its own measured census:
///   * `thin` — pointee CONCRETE and THIN ([`thin_shared_pointee_ok`]), the wave-AF clause;
///   * `str_fat` — pointee EXACTLY `str` (`ty::Str`), the ONE wide pointee this fragment
///     admits, and ONLY in this in-transit shape (`<AxiomId as Display>::fmt`'s
///     `_t = name(_1); Formatter::write_str(_f, move _t)`). The fat `(ptr, len)` pair rides as
///     an opaque immediate the body provably never inspects: the mentions == 2 wall proves no
///     deref, no projection, no store, no re-borrow — so the metadata is never split,
///     reconstructed or minted here (both producer and consumer are CALLEES, pinned by the
///     comparator's raw-call channel before this gate runs). Every borrow-MINTING path
///     (wave-29b/30/AF/W3/FR `Rvalue::Ref` arms) keeps its THIN clause untouched: nothing in
///     this set admits a borrow def, so no fat borrow can be minted through it. `&[T]`,
///     `&dyn Trait`, `&mut str` and every other wide pointee stay refused.
///
/// FAIL-CLOSED and NARROWING-ONLY: a local not in this set keeps every refusal it had. The
/// differential independently re-checked the derived body against built (`DerivedAgreed` is
/// required before any flip attempt), so a wrong callee or wrong value can only cost the flip,
/// never ship.
#[derive(Default)]
struct CallDestFwd {
    /// Concrete + THIN pointee (`&Level`, `&Expr`).
    thin: HashSet<Local>,
    /// Pointee EXACTLY `str` — the in-transit fat-pointer class (`&str`).
    str_fat: HashSet<Local>,
}

impl CallDestFwd {
    fn contains(&self, l: &Local) -> bool {
        self.thin.contains(l) || self.str_fat.contains(l)
    }
}

fn calldest_forward_temps<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> CallDestFwd {
    // Total VALUE mentions per local (storage markers / debuginfo are NonUse and uncounted).
    let mut mentions: HashMap<Local, u32> = HashMap::new();
    struct MentionCounter<'a> {
        m: &'a mut HashMap<Local, u32>,
    }
    impl<'tcx> Visitor<'tcx> for MentionCounter<'_> {
        fn visit_local(&mut self, l: Local, ctx: PlaceContext, _loc: Location) {
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
    let mut calldest_def: HashMap<Local, u32> = HashMap::new();
    let mut callarg_use: HashMap<Local, u32> = HashMap::new();
    let mut self_feed: HashSet<Local> = HashSet::new();
    for (_bb, data) in body.basic_blocks.iter_enumerated() {
        let Some(term) = &data.terminator else { continue };
        let TerminatorKind::Call { args, destination, .. } = &term.kind else { continue };
        let dest_admissible = destination.projection.is_empty()
            && destination.local != RETURN_PLACE
            && destination.local.as_usize() > body.arg_count
            && matches!(body.local_decls[destination.local].ty.kind(), ty::Ref(_, _, m) if m.is_not());
        if dest_admissible {
            *calldest_def.entry(destination.local).or_default() += 1;
        }
        for arg in args.iter() {
            if let Operand::Copy(p) | Operand::Move(p) = &arg.node {
                if p.projection.is_empty() {
                    *callarg_use.entry(p.local).or_default() += 1;
                    if dest_admissible && p.local == destination.local {
                        self_feed.insert(p.local);
                    }
                }
            }
        }
    }
    let mut out = CallDestFwd::default();
    for (&l, &d) in calldest_def.iter() {
        let facts = CallDestFwdFacts {
            calldest_defs: d,
            mentions: mentions.get(&l).copied().unwrap_or_default(),
            callarg_uses: callarg_use.get(&l).copied().unwrap_or_default(),
            self_feed: self_feed.contains(&l),
        };
        if !calldest_fwd_admits(facts) {
            continue;
        }
        let ty::Ref(_, pointee, _) = *body.local_decls[l].ty.kind() else { continue };
        if thin_shared_pointee_ok(tcx, pointee) {
            out.thin.insert(l);
        } else if matches!(pointee.kind(), ty::Str) {
            out.str_fat.insert(l);
        }
        // Any other pointee (slice, dyn, non-str unsized, non-concrete): NOT admitted —
        // the local keeps its fail-closed refusal.
    }
    out
}

fn ref_args_forward_only<'tcx>(
    body: &Body<'tcx>,
    ref_args: &HashSet<Local>,
    interior_arg_temps: &HashSet<Local>,
    payload_temps: &HashSet<Local>,
    addr_fwd_temps: &HashSet<Local>,
    relay_srcs: &HashSet<Local>,
    call_fwd_temps: &HashSet<Local>,
    field_pair_inners: &HashSet<Local>,
) -> Result<(), String> {
    let mut g = RefArgForwardGuard {
        ref_args,
        interior_arg_temps,
        payload_temps,
        addr_fwd_temps,
        relay_srcs,
        call_fwd_temps,
        field_pair_inners,
        violation: None,
    };
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
            // Trust (wave-MC, 2026-08-20): a BARE WHOLE-VALUE STORE `_t = <rvalue>` at empty
            // projection, which is the by-value call-chain class's ARGUMENT temp
            // (`_t = copy _param; f(move _t)` — built's own `as_operand` -> `as_temp`, measured
            // verbatim in `crates/trust-thir-lower/probes/mc_call.rs`).
            //
            // This is the SAME footing as `is_call_dest`, not a new one: both are the local's
            // single definition writing a WHOLE value of the local's own declared type, and
            // `temp_struct_ty_ok` has already required that type to be a concrete, `Copy`,
            // Drop-free struct. What makes a mention dangerous here is a PROJECTED write
            // (`(_t.k) = v`), a `Drop`, or a mutable borrow — each of which reads or invalidates
            // part of a value the shim did not write — and every one of those still records a
            // violation, because each is either non-empty-projection or a different
            // `MutatingUseContext`. `ElaborateDrops`/`AbortUnwindingCalls` stay no-ops over a
            // `!needs_drop` local however it was written, so pass-totality is untouched.
            let is_bare_store = place.projection.is_empty()
                && matches!(ctx, PlaceContext::MutatingUse(MutatingUseContext::Store));
            let is_whole_read = place.projection.is_empty() && !ctx.is_mutating_use();
            let is_field_read = matches!(place.projection.first(), Some(ProjectionElem::Field(..)))
                && !ctx.is_mutating_use();
            if !is_call_dest && !is_bare_store && !is_whole_read && !is_field_read {
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
            "struct temp {l:?} used outside call-dest / bare store / whole read / scalar field read"
        )),
        None => Ok(()),
    }
}

/// Trust (wave-WB, 2026-08-21, enum call-result TEMP): a NON-arg local the flip may declare for
/// a FIELDLESS enum value produced by one call and consumed whole — wave-GH2's call-result-temp
/// discipline extended from `Copy` Drop-free STRUCTS to `Copy` Drop-free FIELDLESS enums
/// (`ConstantOrigin::needs_recheck`'s `_t: OriginTrust = trust(_1); needs_recheck(move _t)`,
/// `<BinderData as Default>::default`'s `_t: BinderInfo = default()` consumed by the aggregate
/// return — the wall-B "enum temps" class of the never-flip partition).
///
/// STRICTLY TIGHTER than [`temp_struct_ty_ok`] in shape: FIELDLESS only (every variant
/// field-free — the wave-V ARG restriction, kept verbatim), so the enum's layout is its bare
/// discriminant scalar and no payload/niche layout is ever reconstructed here. `Copy` +
/// `!needs_drop` keep `ElaborateDrops`/`AbortUnwindingCalls` no-ops (pass-totality — the
/// wave-GH2 argument, verbatim); concrete-only as everywhere in the fragment. The paired
/// [`enum_temps_confined`] guard is TIGHTER than [`StructTempGuard`] too: a mention is admitted
/// ONLY as (a) the bare CALL-DESTINATION write or (b) a bare whole `Copy`/`Move` OPERAND read —
/// no bare store, no field read (ill-typed on an enum without a downcast), no discriminant read
/// (that stays wave-V's ARG-only shape; a `Discriminant(_t)` rvalue on a temp additionally
/// fails the gate's rvalue arm, which pins its source to an `enum_val_args` member).
fn temp_enum_ty_ok<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    if ty.has_non_region_param() || ty.has_non_region_infer() {
        return false;
    }
    let te = ty::TypingEnv::fully_monomorphized();
    matches!(ty.kind(), ty::Adt(adt, _)
        if adt.is_enum()
            && !adt.variants().is_empty()
            && adt.variants().iter().all(|v| v.fields.is_empty()))
        && tcx.type_is_copy_modulo_regions(te, ty)
        && !ty.needs_drop(tcx, te)
}

/// Trust (wave-WB): verify every mention of an `enum_temps` local (admitted by
/// [`temp_enum_ty_ok`]) is one of the TWO shapes the derived body carries for a call-result
/// fieldless-enum temp: the bare call-destination write, or a bare whole `Copy`/`Move` operand
/// read (a call argument or an aggregate field operand). Any OTHER context — a bare `Store`
/// def, a projected use, a `Discriminant` inspect, a borrow, a Drop — records a violation → no
/// flip (clean-only preserved). Deliberately NARROWER than [`StructTempGuard`]: no bare-store
/// arm (no admitted body defines an enum temp by plain assign) and no field-read arm (ill-typed
/// on an enum base without a downcast).
struct EnumTempGuard<'a> {
    enum_temps: &'a HashSet<Local>,
    violation: Option<Local>,
}
impl<'tcx> Visitor<'tcx> for EnumTempGuard<'_> {
    fn visit_place(&mut self, place: &Place<'tcx>, ctx: PlaceContext, loc: Location) {
        if self.enum_temps.contains(&place.local) {
            let is_call_dest = place.projection.is_empty()
                && matches!(ctx, PlaceContext::MutatingUse(MutatingUseContext::Call));
            let is_whole_operand = place.projection.is_empty()
                && matches!(
                    ctx,
                    PlaceContext::NonMutatingUse(
                        NonMutatingUseContext::Copy | NonMutatingUseContext::Move
                    )
                );
            if !is_call_dest && !is_whole_operand {
                self.violation.get_or_insert(place.local);
            }
        }
        self.super_place(place, ctx, loc);
    }
}

fn enum_temps_confined<'tcx>(body: &Body<'tcx>, enum_temps: &HashSet<Local>) -> Result<(), String> {
    let mut g = EnumTempGuard { enum_temps, violation: None };
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        g.visit_basic_block_data(bb, data);
    }
    match g.violation {
        Some(l) => Err(format!("enum temp {l:?} used outside call-dest / bare whole operand read")),
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

/// Trust (wave-AF, 2026-08-19): the FIELD TYPE of an INTERIOR place read through a SHARED-ref ARG
/// — either `((*_p).k)` (projection `[Deref, Field(k, fty)]`) or the by-REF enum payload
/// `(((*_p) as V).k)` (projection `[Deref, Downcast(v), Field(k, fty)]`, and then `_p`'s pointee
/// must be an enum) — or `None` when `place` is neither.
///
/// Extracted so the READ path and the ADDRESS path differ in EXACTLY ONE clause and in nothing
/// else. The READ path ([`is_ref_enum_payload_read`], `place_ok`) requires `scalar_ok(fty)`
/// because it produces a VALUE of that type; the ADDRESS path ([`addr_forward_temps`]) does not,
/// because it produces only a thin shared reference and the paired confinement proves nothing is
/// ever loaded through it.
///
/// NOT AN ARM OF `place_ok`, for `place_ok`'s own stated reason: it is direction-blind and is
/// called on assign DESTINATIONS, so admitting a non-scalar field there would also admit a STORE
/// through a shared reference. This helper is only ever consulted from the BORROW path.
fn interior_field_ty<'tcx>(body: &Body<'tcx>, place: &Place<'tcx>) -> Option<ty::Ty<'tcx>> {
    // Base must be a SHARED-ref ARG, exactly as `place_ok`'s `[Deref, …]` arms require.
    if place.local.as_usize() < 1 || place.local.as_usize() > body.arg_count {
        return None;
    }
    let ty::Ref(_, pointee, m) = *body.local_decls[place.local].ty.kind() else {
        return None;
    };
    if !m.is_not() {
        return None;
    }
    match place.projection.as_slice() {
        [ProjectionElem::Deref, ProjectionElem::Field(_, fty)] => Some(*fty),
        [ProjectionElem::Deref, ProjectionElem::Downcast(..), ProjectionElem::Field(_, fty)]
            if matches!(pointee.kind(), ty::Adt(adt, _) if adt.is_enum()) =>
        {
            Some(*fty)
        }
        _ => None,
    }
}

/// Trust (T2c): is `place` the by-REF enum payload READ `(((*_p) as V).k)` — projection EXACTLY
/// `[Deref, Downcast(v), Field(k, scalar)]` with the base a SHARED-ref ARG whose pointee is an
/// enum? This is the COMPOSITION of two shapes `place_ok` already admits at two levels — wave-24's
/// `Deref` through a ref arg and the enum arc's `Downcast+Field` payload read — and it inherits
/// totality from both: a deref of a shared-ref arg is total, and downcast-then-scalar-field is the
/// canonical shape rustc's own match lowering emits for arm payload access.
///
/// DELIBERATELY NOT AN ARM OF `place_ok`. `place_ok` is direction-blind and `gate_derived_body`
/// calls it on every assign DESTINATION as well as on operands, so a 3-level arm there would also
/// admit `(((*_p) as V).k) = <value>` — a STORE through a SHARED reference, which is not a shape
/// this lane emits and must not be admitted on the strength of the shim merely never emitting it
/// (a wall made of somebody else's absence). Sited on the READ path only, the admission cannot be
/// reached by a destination.
fn is_ref_enum_payload_read<'tcx>(body: &Body<'tcx>, place: &Place<'tcx>) -> bool {
    place.projection.len() == 3
        && matches!(place.projection[0], ProjectionElem::Deref)
        && matches!(place.projection[1], ProjectionElem::Downcast(..))
        && matches!(place.projection[2], ProjectionElem::Field(_, fty) if scalar_ok(fty))
        && place.local.as_usize() >= 1
        && place.local.as_usize() <= body.arg_count
        && matches!(
            body.local_decls[place.local].ty.kind(),
            ty::Ref(_, pointee, m) if m.is_not()
                && matches!(pointee.kind(), ty::Adt(adt, _) if adt.is_enum())
        )
}

/// Trust (wave-AF, 2026-08-19): may the flip DECLARE a shared-reference local `&P` for a
/// NON-scalar `P` whose ADDRESS this body only ever forwards?
///
/// `scalar_ok(fty)` on the borrowed field was carrying THREE properties at once. Two of them are
/// not owed on the address path, and the third is — so it is spelled here instead of inherited.
///
/// * **`P` has no drop glue** — NOT owed. `_t` is a BORROW: `&P` is `Copy` and `!needs_drop` for
///   every `P`, and a shared borrow mints no move path at all —
///   `rustc_mir_dataflow/src/move_paths/builder.rs:441`, `gather_rvalue`'s
///   `Rvalue::Ref(..) => {}` — so `ElaborateDrops` finds nothing to elaborate and NO DROP
///   OBLIGATION IS TRANSFERRED. The obligation stays with whoever OWNS the aggregate, and that is
///   the CALLER: the borrow base is a shared-ref PARAM this body cannot even write through.
/// * **a value of `P` has a known width** — NOT owed, and this is the SHIM's own recorded reason
///   for the same relaxation on its side of the seam (`to_mir.rs:6956-6963`, the T2d arm: *"This
///   arm loads nothing … A payload whose address is taken and never dereferenced here needs no
///   width argument, because no width is read"*; and `to_mir.rs:5425-5429`, wave-T2e: *"the
///   borrowed field no longer has to be a fragment SCALAR … scalarity was an ARGUMENT for
///   uniqueness, never its source"*). [`addr_forward_temps`]'s mentions == 2 clause is what makes
///   "never dereferenced" a proof rather than a hope.
/// * **`&P` is a THIN pointer** — OWED, and it is the one property `scalar_ok` was supplying
///   silently. An unsized `P` makes `&P` a WIDE `(data, metadata)` pair and the fragment models
///   pointer metadata nowhere. **This clause is not hypothetical: 2 of the 29 `-O0` fragment
///   local-type refusals in `clean-kernel` are `&'{erased} str`** (`<mode::AxiomId as
///   Display>::fmt`, `<mode::CleanMode as Display>::fmt`), which this predicate REFUSES.
///
///   Both PEERS already apply exactly this gate to exactly these lanes, so the three sides now
///   agree by construction rather than by coincidence: the producer's by-ref payload binding
///   (`lib.rs:22908-22915`, `ptr_thin = pointee.is_sized(tcx, te)`, tag `"EnumMatch(ref payload
///   non-thin binding)"`) and the shim's interior-borrow erasure (`to_mir.rs:5439-5442`, which
///   emits only when `fat_shape(&FieldTy) == Thin`).
///
///   Conservative in the safe direction: an `extern type` tail is `!Sized` yet ITS pointers are
///   THIN (the `PointeeMeta` note, `lib.rs:2869-2871`), so `is_sized` REFUSES a shape that would
///   in fact have been fine. Refusing more is fail-closed.
///
/// Concrete-only (param/infer-free) as everywhere else in the fragment, and as both peers require
/// of the same field type (`to_mir.rs:5451-5457`).
fn concrete_thin_pointee_admits(has_param: bool, has_infer: bool, is_sized: bool) -> bool {
    !has_param && !has_infer && is_sized
}

fn thin_shared_pointee_ok<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    let has_param = ty.has_non_region_param();
    let has_infer = ty.has_non_region_infer();
    // Preserve the old fail-fast query boundary: there is no reason to ask
    // rustc for a concrete layout property when the type is not concrete.
    let is_sized =
        !has_param && !has_infer && ty.is_sized(tcx, ty::TypingEnv::fully_monomorphized());
    concrete_thin_pointee_admits(has_param, has_infer, is_sized)
}

/// Trust (wave-AF, 2026-08-19): the set of shared-ref TEMP locals holding the ADDRESS of an
/// interior place that is FORWARDED WHOLE into a call and never dereferenced —
/// `_t = &((*_p).k); g(copy _t)` (the shim's T2e interior-borrow reconstruction,
/// `to_mir.rs:5415-5459`) and `_t = &(((*_p) as V).k); g(copy _t)` (the T2d by-REF enum payload
/// ADDRESS arm, `to_mir.rs:6947-7024`, which is what
/// `match self { Level::Max(l1, l2) => l1.is_zero() && .. }` lowers to: the payload is never
/// loaded, its address is taken and handed to a call).
///
/// This is [`interior_arg_temps`]'s discipline over [`interior_field_ty`]'s two borrowed-place
/// shapes, and it is a THIRD separate set rather than a widening of [`interior_arg_temps`] or
/// [`payload_borrow_temps`], for the reason wave-EP already gave: folding them together would let
/// one set's temp inherit another's USE KIND on the strength of neither having been measured.
///
/// **The ONE clause that is new, and the whole of what this lane changes:** the borrowed field
/// type is NOT required to be `scalar_ok`. Everything else is the existing discipline verbatim.
/// See [`thin_shared_pointee_ok`] for what that clause was carrying and which part of it survives.
///
/// Admitted iff ALL of:
///   * `_t` is a NON-arg, non-`_0` local declared `&P` SHARED (`m.is_not()`) with
///     [`thin_shared_pointee_ok`] — so the local is a thin pointer and `P` is concrete;
///   * EXACTLY ONE def, `_t = Rvalue::Ref(_, Shared, borrowed)`, with `borrowed` a place
///     [`interior_field_ty`] recognizes AND its field type EQUAL to `_t`'s declared pointee — so
///     `Subtyper` inserts nothing (`add_subtyping_projections.rs:39-47` acts only where the
///     region-erased place and rvalue types DIFFER);
///   * EXACTLY ONE use, a BARE `Operand::Copy|Move(_t)` (empty projection) in a `Call`'s `args`.
///     `Copy` is admitted because `&P` IS `Copy` and the shim spells every Copy-typed place
///     `Copy` (`to_mir.rs:5347-5353`); the wave-GH2 memory-ABI `Copy`-vs-`Move` divergence is
///     specific to indirectly-passed STRUCT args and is fail-closed separately at the `Call` arm,
///     which does not fire for a reference (an Immediate scalar under every ABI);
///   * TOTAL value-mentions == 2 (the def dest + the one use). Storage markers are `NonUse` and
///     uncounted, exactly as in [`interior_arg_temps`] and [`payload_borrow_temps`].
///
/// **That last clause is the load-bearing one.** It is what proves `_t` is NEVER DEREFERENCED:
/// a deref-read, a reborrow, a second forward, a store — each is a third mention and rejects. So
/// no value of type `P` is ever produced in this body, which is precisely why `P`'s drop glue and
/// `P`'s width are not this fragment's business. `P` is `LevelArc`, `HashMap<..>`, `Vec<..>` —
/// `Drop`-bearing, `Arc`-backed, niched, all of it — and none of that is ever materialised here.
///
/// FAIL-CLOSED and NARROWING-ONLY: a local not in this set keeps every refusal it had. The
/// differential independently re-checks the derived body against built, and the comparator renders
/// the borrow as `iref(a{p},K)` on both sides, so a wrong field or variant can only cost the flip,
/// never ship.
fn addr_forward_temps<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> HashSet<Local> {
    // Total place-local mentions per local (dest + every operand/projection occurrence), by the
    // same VALUE-mention rule `interior_arg_temps` uses.
    let mut mentions: HashMap<Local, u32> = HashMap::new();
    struct MentionCounter<'a> {
        m: &'a mut HashMap<Local, u32>,
    }
    impl<'tcx> Visitor<'tcx> for MentionCounter<'_> {
        fn visit_local(&mut self, l: Local, ctx: PlaceContext, _loc: Location) {
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
    let mut borrow_def: HashMap<Local, u32> = HashMap::new();
    let mut callarg_use: HashMap<Local, u32> = HashMap::new();
    for (_bb, data) in body.basic_blocks.iter_enumerated() {
        for stmt in &data.statements {
            let StatementKind::Assign(assign) = &stmt.kind else { continue };
            let (place, rvalue) = &**assign;
            // The address definition, into a bare NON-arg, non-`_0` local declared
            // shared-ref-to-a-thin-concrete-pointee.
            if !place.projection.is_empty()
                || place.local == RETURN_PLACE
                || place.local.as_usize() <= body.arg_count
            {
                continue;
            }
            let ty::Ref(_, pointee, m) = *body.local_decls[place.local].ty.kind() else { continue };
            if !m.is_not() || !thin_shared_pointee_ok(tcx, pointee) {
                continue;
            }
            if let Rvalue::Ref(_, BorrowKind::Shared, borrowed) = rvalue {
                if interior_field_ty(body, borrowed) == Some(pointee) {
                    *borrow_def.entry(place.local).or_default() += 1;
                }
            }
        }
        if let Some(term) = &data.terminator {
            if let TerminatorKind::Call { args, .. } = &term.kind {
                for arg in args.iter() {
                    if let Operand::Copy(p) | Operand::Move(p) = &arg.node {
                        if p.projection.is_empty() {
                            *callarg_use.entry(p.local).or_default() += 1;
                        }
                    }
                }
            }
        }
    }
    borrow_def
        .iter()
        .filter(|(l, &d)| d == 1 && mentions.get(l) == Some(&2) && callarg_use.get(l) == Some(&1))
        .map(|(l, _)| *l)
        .collect()
}

/// Trust (wave-W3, 2026-08-20): the DEREF-RECURSION REFERENCE RELAY — the four shared-ref temps
/// the shim mints per `x.p()` where `x: &Wrapper`, `Wrapper: Deref<Target = T>` is a USER impl,
/// and `p` is a method on `T`. This is `clean_kernel::level::Level::is_zero` / `::is_nonzero`, the
/// designated crystal target, and every body in its class.
///
/// # The shape, and why it is FOUR locals and not one
///
/// `l1.p()` is `T::p(&*<Wrapper as Deref>::deref(&*l1))` — TWO calls, and built MIR spells the
/// address that travels between them with a chain of four temps (measured off this driver's own
/// built MIR for `Level::is_zero`; wave-DR reproduces the same chain and its 28 storage markers,
/// which is what made `markers_exact` hold and turned this body's SILENT decline into a LOUD one):
///
/// ```text
///   StorageLive(_b); _b = &(((*_1) as Max).0: LevelArc);   // the arm BINDING      &Wrapper
///   StorageLive(_g); _g = &(*_b);                          // the argument REBORROW &Wrapper
///   StorageLive(_d); _d = <LevelArc as Deref>::deref(move _g) -> ..;  // the accessor DEST &T
///   _a = &(*_d);                                           // the AUTOREF           &T
///   StorageDead(_g);
///   _r = Level::is_zero(move _a) -> ..;
/// ```
///
/// Each link is a shared reference to a NON-scalar pointee, so `local_ty_ok` refuses the first one
/// it reaches and the whole body falls back. The four decompose into exactly TWO roles:
///
/// * a **SOURCE** (`_b`, `_d`) — an address PRODUCED here, either as the interior/enum-payload
///   borrow of a shared-ref ARG ([`interior_field_ty`]'s two places, the wave-AF shapes) or as a
///   bare `Call` DESTINATION; reborrowed exactly once into a forwarder;
/// * a **FORWARD** (`_g`, `_a`) — `_f = &(*_s)` off a source, handed to exactly one call.
///
/// The chain length is pinned at exactly two links. A source is never itself a forward and a
/// forward is never a source, so nothing longer, and nothing cyclic, can enter: `_f = &(*_f)` is
/// excluded explicitly, and a would-be third link has neither a root def nor a source's use.
///
/// # THE READ-ONLY OBLIGATION, AND WHY IT IS A PROOF
///
/// Every member carries TOTAL value-mentions == 2 — the def, and one use. Storage markers and
/// debuginfo are `PlaceContext::NonUse` and are not counted, exactly as in [`interior_arg_temps`],
/// [`payload_borrow_temps`] and [`addr_forward_temps`]; a real read or write is always a
/// Non/MutatingUse and IS counted, so no observation can hide behind the exemption.
///
/// The def writes `_t` ITSELF (a `Rvalue::Ref` into the bare local, or a call destination), never
/// through it. The use is drawn from exactly two syntactic forms, and each is enumerated here
/// rather than assumed:
///
/// * a bare `Operand::Copy|Move(_t)` (EMPTY projection) in a `Call`'s `args` — a non-mutating use
///   of the pointer VALUE;
/// * the base of `_f = Rvalue::Ref(_, BorrowKind::Shared, (*_t))` — a shared borrow, which takes
///   an ADDRESS: it loads no value out of `*_t` and stores none into it.
///
/// **Therefore no store through any member exists in this body, and that is counted, not
/// asserted.** A store `(*_t)…= v` is a MutatingUse mention of `_t` — a THIRD mention — and is
/// rejected. So is a load `copy (*_t)`, a `&mut (*_t)` reborrow (which also fails the
/// `BorrowKind::Shared` requirement), a second forward, and any projected use. No value of the
/// pointee is ever materialised in this body, which is why the pointee's drop glue and width are
/// not this fragment's business — wave-AF's argument, and it holds link for link.
///
/// **And the admission is spelled where a destination cannot reach it.** Like [`interior_field_ty`]
/// and [`is_ref_enum_payload_read`], this is NOT an arm of `place_ok`. `place_ok` is
/// direction-blind and `gate_derived_body` calls it on every assign DESTINATION; its only
/// `[Deref]` arm requires the base to be an **ARG** local with a **scalar** pointee, and every
/// member of this set is NON-arg by its first clause. So a destination `(*_t)` / `(*_t).k` is
/// refused by `place_ok` even with the mention count removed. The two refusals are INDEPENDENT,
/// and the mutation probes measure each.
///
/// # The remaining clauses
///
/// * `_t` is a NON-arg, non-`_0` local declared `&P` SHARED (`m.is_not()`) with
///   [`thin_shared_pointee_ok`] — concrete, and a THIN pointer, since the fragment models pointer
///   metadata nowhere. This is the clause that refuses a `Deref<Target = str>` relay.
/// * a FORWARD's declared pointee EQUALS its source's, so `Subtyper` inserts nothing
///   (`add_subtyping_projections.rs:39-47` acts only where the region-erased place and rvalue
///   types differ); a SOURCE's borrowed field type likewise equals its own declared pointee.
/// * EXACTLY ONE def and EXACTLY ONE use per member, and a source's single reborrow use must be
///   the very forward that names it.
///
/// FAIL-CLOSED and NARROWING-ONLY: a local not in this set keeps every refusal it had. The
/// differential independently re-checks the derived body against built (`DerivedAgreed` +
/// `markers_exact` are both already required before this gate runs), so a wrong field, variant or
/// callee can only cost the flip, never ship.
#[derive(Default)]
struct DerefRelay {
    /// The address PRODUCERS — the arm binding `_b` and the accessor destination `_d`.
    srcs: HashSet<Local>,
    /// The address FORWARDS — the argument reborrow `_g` and the autoref `_a`.
    fwds: HashSet<Local>,
}

/// The facts which certify one W3 source/forward pair. Keeping this as one
/// value makes the production predicate directly executable in unit tests;
/// in particular, the `mentions == 2` wall is not left as an uncommitted
/// producer observation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct RelayPairFacts {
    forward_reborrow_defs: u32,
    forward_root_defs: u32,
    forward_mentions: u32,
    forward_callarg_uses: u32,
    source_root_defs: u32,
    source_is_forward: bool,
    source_mentions: u32,
    source_reborrow_use_is_exact: bool,
    source_callarg_uses: u32,
}

fn relay_pair_admits(facts: RelayPairFacts) -> bool {
    facts.forward_reborrow_defs == 1
        && facts.forward_root_defs == 0
        && facts.forward_mentions == 2
        && facts.forward_callarg_uses == 1
        && facts.source_root_defs == 1
        && !facts.source_is_forward
        && facts.source_mentions == 2
        && facts.source_reborrow_use_is_exact
        && facts.source_callarg_uses == 0
}

impl DerefRelay {
    fn contains(&self, l: &Local) -> bool {
        self.srcs.contains(l) || self.fwds.contains(l)
    }
}

/// Is `borrowed` the borrow `place` is admitted to hold, given `place` is a relay member? A SOURCE
/// holds one of [`interior_field_ty`]'s two interior places (field type == its declared pointee);
/// a FORWARD holds the bare reborrow `(*_s)` of a SOURCE. Anything else falls through to
/// `place_ok` and fails closed there.
fn is_relay_borrow<'tcx>(
    body: &Body<'tcx>,
    relay: &DerefRelay,
    place: &Place<'tcx>,
    borrowed: &Place<'tcx>,
) -> bool {
    if place.local == RETURN_PLACE || !place.projection.is_empty() {
        return false;
    }
    let ty::Ref(_, pointee, _) = *body.local_decls[place.local].ty.kind() else {
        return false;
    };
    if relay.srcs.contains(&place.local) {
        return interior_field_ty(body, borrowed) == Some(pointee);
    }
    relay.fwds.contains(&place.local)
        && borrowed.projection.len() == 1
        && matches!(borrowed.projection[0], ProjectionElem::Deref)
        && relay.srcs.contains(&borrowed.local)
        // Defence in depth: `deref_relay_temps` admitted the pair only with equal pointees, so
        // `Subtyper` inserts nothing. Re-derive it here rather than inherit it, so a future
        // producer that puts two relay pairs in one body cannot cross-wire them past this arm.
        && matches!(
            body.local_decls[borrowed.local].ty.kind(),
            ty::Ref(_, p2, m2) if m2.is_not() && *p2 == pointee
        )
}

fn deref_relay_temps<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> DerefRelay {
    // Total VALUE-mention count per local — the same rule `interior_arg_temps` uses.
    let mut mentions: HashMap<Local, u32> = HashMap::new();
    struct MentionCounter<'a> {
        m: &'a mut HashMap<Local, u32>,
    }
    impl<'tcx> Visitor<'tcx> for MentionCounter<'_> {
        fn visit_local(&mut self, l: Local, ctx: PlaceContext, _loc: Location) {
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
    let thin = |ty: ty::Ty<'tcx>| thin_shared_pointee_ok(tcx, ty);
    // The declaration every member must carry: a NON-arg, non-`_0` local declared `&P` SHARED with
    // `P` concrete and thin. Returns `P`.
    let decl_ok = |l: Local| -> Option<ty::Ty<'tcx>> {
        if l == RETURN_PLACE
            || l.as_usize() <= body.arg_count
            || l.as_usize() >= body.local_decls.len()
        {
            return None;
        }
        let ty::Ref(_, pointee, m) = *body.local_decls[l].ty.kind() else {
            return None;
        };
        (m.is_not() && thin(pointee)).then_some(pointee)
    };

    // One pass: every def and every use shape this set can name.
    // A SOURCE's def — the interior/payload borrow, or a bare call destination.
    let mut root_def: HashMap<Local, u32> = HashMap::new();
    // A FORWARD's def `_f = &(*_s)`: forward -> (source, count).
    let mut reborrow_def: HashMap<Local, (Local, u32)> = HashMap::new();
    // The matching SOURCE use: source -> (forward, count).
    let mut reborrow_use: HashMap<Local, (Local, u32)> = HashMap::new();
    // A bare `Copy|Move` call argument.
    let mut callarg_use: HashMap<Local, u32> = HashMap::new();
    for (_bb, data) in body.basic_blocks.iter_enumerated() {
        for stmt in &data.statements {
            let StatementKind::Assign(assign) = &stmt.kind else { continue };
            let (place, rvalue) = &**assign;
            let Rvalue::Ref(_, BorrowKind::Shared, borrowed) = rvalue else { continue };
            if !place.projection.is_empty() {
                continue;
            }
            let Some(pointee) = decl_ok(place.local) else { continue };
            if interior_field_ty(body, borrowed) == Some(pointee) {
                *root_def.entry(place.local).or_default() += 1;
                continue;
            }
            // `_f = &(*_s)`. `borrowed.local != place.local` excludes the self-referential
            // `_f = &(*_f)`, whose two mentions would otherwise satisfy the count while reading
            // an uninitialised local.
            if borrowed.projection.len() == 1
                && matches!(borrowed.projection[0], ProjectionElem::Deref)
                && borrowed.local != place.local
                && decl_ok(borrowed.local) == Some(pointee)
            {
                let d = reborrow_def.entry(place.local).or_insert((borrowed.local, 0));
                d.0 = borrowed.local;
                d.1 += 1;
                let u = reborrow_use.entry(borrowed.local).or_insert((place.local, 0));
                u.0 = place.local;
                u.1 += 1;
            }
        }
        if let Some(term) = &data.terminator {
            if let TerminatorKind::Call { args, destination, .. } = &term.kind {
                if destination.projection.is_empty() && decl_ok(destination.local).is_some() {
                    *root_def.entry(destination.local).or_default() += 1;
                }
                for arg in args.iter() {
                    if let Operand::Copy(p) | Operand::Move(p) = &arg.node {
                        if p.projection.is_empty() {
                            *callarg_use.entry(p.local).or_default() += 1;
                        }
                    }
                }
            }
        }
    }

    // Admit a FORWARD only together with the SOURCE it names, both fully certified here. The
    // source's own conditions are checked inline rather than by a second fixpoint, which is what
    // keeps the relation acyclic and the chain exactly two links long.
    let mut fwds: HashSet<Local> = HashSet::new();
    let mut srcs: HashSet<Local> = HashSet::new();
    for (&f, &(s, n)) in reborrow_def.iter() {
        let facts = RelayPairFacts {
            forward_reborrow_defs: n,
            forward_root_defs: root_def.get(&f).copied().unwrap_or_default(),
            forward_mentions: mentions.get(&f).copied().unwrap_or_default(),
            forward_callarg_uses: callarg_use.get(&f).copied().unwrap_or_default(),
            source_root_defs: root_def.get(&s).copied().unwrap_or_default(),
            source_is_forward: reborrow_def.contains_key(&s),
            source_mentions: mentions.get(&s).copied().unwrap_or_default(),
            source_reborrow_use_is_exact: reborrow_use.get(&s) == Some(&(f, 1)),
            source_callarg_uses: callarg_use.get(&s).copied().unwrap_or_default(),
        };
        if !relay_pair_admits(facts) {
            continue;
        }
        fwds.insert(f);
        srcs.insert(s);
    }
    DerefRelay { srcs, fwds }
}

/// Trust (wave-EP, 2026-08-16): the set of shared-ref TEMP locals the shim emits for an ARM-BINDING
/// payload borrow — `StorageLive(t); t = &(((*_p) as V).k); _x = copy (*t); StorageDead(t)`, which
/// is byte-for-byte the sequence rustc's own match lowering emits for
/// `match self { E::V(h) => *h, .. }` (measured in full on `env::types::Reducibility::height`).
///
/// This is [`interior_arg_temps`]'s discipline over a THIRD borrowed-place shape and a SECOND use
/// shape, and it is deliberately a separate set rather than a widening of that one: the two differ
/// in what they prove, and folding them together would let a wave-30 call-arg temp inherit this
/// use kind (and vice versa) on the strength of neither having been measured.
///
/// Admitted iff ALL of:
///   * `_t` is declared `&S` with `S` a fragment scalar — the same declaration wave-29b/wave-30
///     already admit;
///   * EXACTLY ONE def, `_t = &(borrowed)`, with `borrowed` the by-ref payload read
///     [`is_ref_enum_payload_read`] ALREADY certifies on the operand path. Borrowing a place is
///     total wherever reading it is: the base is a runtime shared-ref PARAM (so `PromoteTemps`
///     finds no candidate — no const/static operand), the field is a scalar (no drop glue), the
///     borrow is `Shared` with an erased region, and the projection is exactly the one rustc's
///     match lowering itself builds for arm payload access;
///   * EXACTLY ONE use, `_x = copy (*_t)` with `_x` NOT an argument — a deref-read of a
///     shared-ref-to-scalar, which is precisely the totality `place_ok`'s wave-S `[Deref]` arm
///     certifies, differing only in that the base is this proven single-def temp rather than an
///     arg local;
///   * TOTAL value-mentions == 2 (the def dest + the one use). Storage markers are `NonUse` and
///     uncounted, exactly as in [`interior_arg_temps`]. That clause is the airtight single-use
///     guarantee: a temp stored, re-borrowed, copied or used again appears a third time and is
///     rejected, so no interior pointer can escape or alias beyond the one read.
///
/// FAIL-CLOSED and NARROWING-ONLY: a local not in this set keeps every refusal it had. The
/// differential independently re-checks the derived body against built, so a wrong variant or
/// field can only cost the flip, never ship.
fn payload_borrow_temps<'tcx>(body: &Body<'tcx>) -> HashSet<Local> {
    // Total place-local mentions per local (dest + every operand/projection occurrence), by the
    // same VALUE-mention rule `interior_arg_temps` uses.
    let mut mentions: HashMap<Local, u32> = HashMap::new();
    struct MentionCounter<'a> {
        m: &'a mut HashMap<Local, u32>,
    }
    impl<'tcx> Visitor<'tcx> for MentionCounter<'_> {
        fn visit_local(&mut self, l: Local, ctx: PlaceContext, _loc: Location) {
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
    let mut borrow_def: HashMap<Local, u32> = HashMap::new();
    let mut deref_read: HashMap<Local, u32> = HashMap::new();
    for (_bb, data) in body.basic_blocks.iter_enumerated() {
        for stmt in &data.statements {
            let StatementKind::Assign(assign) = &stmt.kind else { continue };
            let (place, rvalue) = &**assign;
            // The arm-binding borrow definition `_t = &(((*_p) as V).k)`.
            if place.projection.is_empty()
                && matches!(
                    body.local_decls[place.local].ty.kind(),
                    ty::Ref(_, pointee, m) if m.is_not() && scalar_ok(*pointee)
                )
            {
                if let Rvalue::Ref(_, BorrowKind::Shared, borrowed) = rvalue {
                    if is_ref_enum_payload_read(body, borrowed) {
                        *borrow_def.entry(place.local).or_default() += 1;
                    }
                }
            }
            // The single use `_x = copy (*_t)`, into a non-argument local.
            let is_arg_dest =
                place.local.as_usize() >= 1 && place.local.as_usize() <= body.arg_count;
            if place.projection.is_empty() && !is_arg_dest {
                if let Rvalue::Use(Operand::Copy(src) | Operand::Move(src), _) = rvalue {
                    if src.projection.len() == 1
                        && matches!(src.projection[0], ProjectionElem::Deref)
                    {
                        *deref_read.entry(src.local).or_default() += 1;
                    }
                }
            }
        }
    }
    borrow_def
        .iter()
        .filter(|(l, &d)| d == 1 && mentions.get(l) == Some(&2) && deref_read.get(l) == Some(&1))
        .map(|(l, _)| *l)
        .collect()
}

fn operand_ok<'tcx>(
    body: &Body<'tcx>,
    payload_temps: &HashSet<Local>,
    op: &Operand<'tcx>,
) -> Result<(), String> {
    match op {
        Operand::Copy(p) | Operand::Move(p) => {
            if is_ref_enum_payload_read(body, p) {
                return Ok(());
            }
            // Trust (wave-EP): the arm-binding borrow's single READ `copy (*_t)` — `[Deref]` on a
            // temp `payload_borrow_temps` proved is single-def/single-use and declared
            // shared-ref-to-scalar. Same totality as `place_ok`'s wave-S `[Deref]` arm; that arm
            // pins its base to an ARG local, which is why this one is here and not there.
            if p.projection.len() == 1
                && matches!(p.projection[0], ProjectionElem::Deref)
                && payload_temps.contains(&p.local)
            {
                return Ok(());
            }
            place_ok(body, p)
        }
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
/// Trust (lane L9, 2026-08-19): **THE LOOP PLAN'S `()` REGION LOCALS** — the FOURTH non-scalar
/// marked local this fragment admits, and the one whose proof is the strongest of the four.
///
/// `plan_loop_markers` reproduces built's storage spans for a `loop { if c { break; } BODY }` by
/// minting two locals that hold NO VALUE AT ALL: the loop's own `()` value (built's `_2`, opened
/// in the pre-header and retired at the loop exit) and the `if`-statement's `()` value (built's
/// `_4`, opened in the header every iteration and retired on both edges out of its region). They
/// exist so the derived body's marker SEQUENCE is built's — which `markers_exact` then verifies
/// against built independently — and for nothing else.
///
/// Admitted iff ALL of:
///   * the local is NON-arg and not `_0`;
///   * it is declared `()`;
///   * it carries at least one storage marker (otherwise there is nothing to admit);
///   * **TOTAL value-mentions == 0.** Storage markers are `NonUse` and uncounted, exactly as in
///     [`interior_arg_temps`], [`payload_borrow_temps`] and [`addr_forward_temps`].
///
/// **THAT LAST CLAUSE IS STRICTLY STRONGER THAN THE THREE SETS ABOVE, which rest on
/// value-mentions == 2 (one def, one use).** Zero mentions means the local is never defined, never
/// read, never moved, never borrowed and never stored to: no value of its type is produced in this
/// body at all, so every pass is total over the marker exactly as over a scalar one. `()` is
/// additionally a ZST, so the `llvm.lifetime` intrinsics codegen emits for it at `-O` describe an
/// empty range; `RemoveStorageMarkers` deletes them outright at `-O0`.
///
/// FAIL-CLOSED and NARROWING-ONLY: a local not in this set keeps every refusal it had, and a
/// body outside the loop plan has no such local, so no body admitted today changes. The oracle
/// re-checks the marker sequence against built regardless, so a wrong span can only cost the
/// flip, never ship.
/// Trust (lane S1F, 2026-08-22): facts certifying one UNIT CALL-DESTINATION temp — the `()`
/// local `rustc_mir_build::stmt_expr` mints for a unit call in STATEMENT position
/// (`{ f(self); }`), which the call-forward plan's unit-statement form now reproduces with
/// built's own storage span around it:
///
/// ```text
/// StorageLive(_2);            // opened before every argument temp
/// _2 = f(move _3) -> bb1;     // the ONLY mention: a bare call destination
/// bb1: StorageDead(_3); StorageDead(_2); _0 = const (); return;
/// ```
///
/// Kept as one value so the production predicate is directly executable in unit tests, exactly
/// as `CallDestFwdFacts` and `StrLitPairFacts` are.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct UnitCallDestFacts {
    /// Bare call-DESTINATION defs of the local (its ONLY admitted def kind).
    calldest_defs: u32,
    /// TOTAL value-mentions (storage markers are `NonUse` and uncounted).
    mentions: u32,
}

fn unit_calldest_admits(f: UnitCallDestFacts) -> bool {
    f.calldest_defs == 1 && f.mentions == 1
}

/// Trust (lane S1F, 2026-08-22): the UNIT CALL-DESTINATION temps — NON-arg, non-`_0` locals
/// declared `()` whose SINGLE value mention is ONE bare `Call` destination. The argument is
/// [`unit_region_temps`]' made one notch weaker and then recovered by the type: the one mention
/// is a WRITE of a `()` — a ZST, `Copy`, `!needs_drop` — so no value is ever read out of the
/// local, `ElaborateDrops` finds nothing to elaborate, `RemoveStorageMarkers` deletes the pair
/// at `-O0`, and the `llvm.lifetime` intrinsics codegen emits at `-O` describe an empty range.
/// Every pass between `Built` and `Runtime(Optimized)` is total over it exactly as over a
/// scalar temp. FAIL-CLOSED and NARROWING-ONLY: a `()` local with any second mention (a read,
/// a second write, a projection) is not in the set and keeps every refusal it had.
fn unit_calldest_temps<'tcx>(body: &Body<'tcx>) -> HashSet<Local> {
    let mut mentions: HashMap<Local, u32> = HashMap::new();
    struct MentionCounter<'a> {
        m: &'a mut HashMap<Local, u32>,
    }
    impl<'tcx> Visitor<'tcx> for MentionCounter<'_> {
        fn visit_local(&mut self, l: Local, ctx: PlaceContext, _loc: Location) {
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
    let mut calldest_defs: HashMap<Local, u32> = HashMap::new();
    for (_bb, data) in body.basic_blocks.iter_enumerated() {
        let Some(term) = &data.terminator else { continue };
        let TerminatorKind::Call { destination, .. } = &term.kind else { continue };
        if destination.projection.is_empty() {
            *calldest_defs.entry(destination.local).or_default() += 1;
        }
    }
    calldest_defs
        .iter()
        .filter(|(l, &d)| {
            **l != RETURN_PLACE
                && l.as_usize() > body.arg_count
                && body.local_decls[**l].ty.is_unit()
                && unit_calldest_admits(UnitCallDestFacts {
                    calldest_defs: d,
                    mentions: mentions.get(l).copied().unwrap_or(0),
                })
        })
        .map(|(l, _)| *l)
        .collect()
}

/// Trust (lane S1F, 2026-08-22): facts certifying one REBORROWED-RETURN CALL-DESTINATION temp —
/// the `&P` local built routes a tail call into when its reference result is reborrowed into
/// `_0` (`fn deref(&self) -> &R { self.resources() }`, and the overloaded-`Deref` coercion of a
/// bare `self`), which the call-forward plan's reborrowed-return form reproduces with built's
/// own storage span:
///
/// ```text
/// StorageLive(_2);                 // opened before every argument temp
/// _2 = f(move _3) -> bb1;          // the ONLY def: a bare call destination
/// bb1: _0 = &(*_2); StorageDead(_3); StorageDead(_2); return;   // the ONLY use
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CallDestRetFacts {
    /// Bare call-DESTINATION defs of the local (its ONLY admitted def kind).
    calldest_defs: u32,
    /// TOTAL value-mentions (storage markers are `NonUse` and uncounted).
    mentions: u32,
    /// `_0 = &(*_d)` SHARED reborrows of the local into bare `_0` (its ONLY admitted use).
    ret_reborrows: u32,
}

fn calldest_ret_admits(f: CallDestRetFacts) -> bool {
    f.calldest_defs == 1 && f.mentions == 2 && f.ret_reborrows == 1
}

/// Trust (lane S1F, 2026-08-22): the REBORROWED-RETURN CALL-DESTINATION temps — NON-arg,
/// non-`_0` locals declared `&P` SHARED with [`thin_shared_pointee_ok`], whose SINGLE def is a
/// bare `Call` destination and whose SINGLE use is the shared reborrow `_0 = &(*_d)` into bare
/// `_0`, TOTAL value-mentions == 2. This is [`calldest_forward_temps`]' discipline with
/// wave-29b's return-getter USE (`_0 = &(*_t)`) in place of the call-argument one: the address
/// rides the call's return slot into `_0` and is never dereferenced, stored or split in this
/// body; `&P` is `Copy` and `!needs_drop`; `PromoteTemps` finds no candidate. FAIL-CLOSED: any
/// third mention refuses the local.
fn calldest_ret_reborrow_temps<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> HashSet<Local> {
    let mut mentions: HashMap<Local, u32> = HashMap::new();
    struct MentionCounter<'a> {
        m: &'a mut HashMap<Local, u32>,
    }
    impl<'tcx> Visitor<'tcx> for MentionCounter<'_> {
        fn visit_local(&mut self, l: Local, ctx: PlaceContext, _loc: Location) {
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
    let mut calldest_defs: HashMap<Local, u32> = HashMap::new();
    let mut ret_reborrows: HashMap<Local, u32> = HashMap::new();
    for (_bb, data) in body.basic_blocks.iter_enumerated() {
        for stmt in &data.statements {
            let StatementKind::Assign(assign) = &stmt.kind else { continue };
            let (place, rvalue) = &**assign;
            if place.local != RETURN_PLACE || !place.projection.is_empty() {
                continue;
            }
            if let Rvalue::Ref(_, BorrowKind::Shared, borrowed) = rvalue {
                if borrowed.projection.len() == 1
                    && matches!(borrowed.projection[0], ProjectionElem::Deref)
                {
                    *ret_reborrows.entry(borrowed.local).or_default() += 1;
                }
            }
        }
        let Some(term) = &data.terminator else { continue };
        let TerminatorKind::Call { destination, .. } = &term.kind else { continue };
        if destination.projection.is_empty() {
            *calldest_defs.entry(destination.local).or_default() += 1;
        }
    }
    calldest_defs
        .iter()
        .filter(|(l, &d)| {
            **l != RETURN_PLACE
                && l.as_usize() > body.arg_count
                && matches!(*body.local_decls[**l].ty.kind(), ty::Ref(_, pointee, m)
                    if m.is_not() && thin_shared_pointee_ok(tcx, pointee))
                && calldest_ret_admits(CallDestRetFacts {
                    calldest_defs: d,
                    mentions: mentions.get(l).copied().unwrap_or(0),
                    ret_reborrows: ret_reborrows.get(l).copied().unwrap_or(0),
                })
        })
        .map(|(l, _)| *l)
        .collect()
}

fn unit_region_temps<'tcx>(body: &Body<'tcx>) -> HashSet<Local> {
    let mut mentions: HashMap<Local, u32> = HashMap::new();
    struct MentionCounter<'a> {
        m: &'a mut HashMap<Local, u32>,
    }
    impl<'tcx> Visitor<'tcx> for MentionCounter<'_> {
        fn visit_local(&mut self, l: Local, ctx: PlaceContext, _loc: Location) {
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
    let mut marked: HashSet<Local> = HashSet::new();
    for (_bb, data) in body.basic_blocks.iter_enumerated() {
        for stmt in &data.statements {
            if let StatementKind::StorageLive(l) | StatementKind::StorageDead(l) = &stmt.kind {
                marked.insert(*l);
            }
        }
    }
    marked
        .into_iter()
        .filter(|l| {
            *l != RETURN_PLACE
                && l.as_usize() > body.arg_count
                && body.local_decls[*l].ty.is_unit()
                && !mentions.contains_key(l)
        })
        .collect()
}

pub(crate) fn gate_derived_body<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Result<(), String> {
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
    // Trust (wave-EP): shared-ref temps holding an ARM-BINDING payload borrow read through exactly
    // once (`_t = &(((*_p) as V).k); _x = copy (*_t)`) — admitted below by their single-def /
    // single-deref-read shape (`payload_borrow_temps` proves total place-mentions == 2, so no other
    // observation exists).
    let payload_temps = payload_borrow_temps(body);
    // Trust (lane L9): the loop plan's two `()` REGION locals — value-mentions == 0, so the local
    // is a storage span and nothing else. See [`unit_region_temps`].
    let unit_regions = unit_region_temps(body);
    // Trust (lane S1F): the call-forward unit-statement form's `()` call-destination temp —
    // one bare `Call` destination write, no other value mention. See [`unit_calldest_temps`].
    let unit_calldest = unit_calldest_temps(body);
    // Trust (lane S1F): the reborrowed-return call-destination temps `_d = f(..); _0 = &(*_d)`
    // — one bare call-destination write, one shared reborrow into `_0`. See
    // [`calldest_ret_reborrow_temps`].
    let calldest_ret = calldest_ret_reborrow_temps(tcx, body);
    // Trust (wave-AF): shared-ref temps holding the ADDRESS of a NON-scalar interior place,
    // forwarded whole into one call and NEVER dereferenced (`_t = &((*_p).k); g(copy _t)` and its
    // enum-payload twin) — admitted below by their single-def / single-call-arg-use shape
    // (`addr_forward_temps` proves total place-mentions == 2, so no other observation exists).
    let addr_fwd_temps = addr_forward_temps(tcx, body);
    // Trust (wave-FR): the call-forward reborrow temps `_t = &[mut] (*_p); f(move _t)` — the
    // argument temps `to_mir`'s call-forward marker plan mints for a single-block tail call,
    // admitted by their single-def / single-call-arg-move shape (`call_fwd_reborrow_temps`
    // proves total value-mentions == 2, so no other observation exists).
    let call_fwd_temps = call_fwd_reborrow_temps(tcx, body);
    // Trust (lane EM): the `&str`-LITERAL argument pairs `_u = const "lit"; _t = &(*_u);
    // f(move _t)` — the two locals the CF_STR emission mints for a `&str` literal call
    // argument, admitted by their pair-linked single-def / mentions == 2 shape
    // (`str_lit_pair_temps` proves the fat pointer rides only in transit).
    let str_lit_pairs = str_lit_pair_temps(tcx, body);
    // Trust (lane S1F): the explicit-borrow field pairs `_u = &((*_p).0); _t = &(*_u);
    // f(move _t)` — the derived `Ord::cmp`'s two locals per argument, admitted by their
    // pair-linked single-def / mentions == 2 shape (`field_pair_temps`).
    let field_pairs = field_pair_temps(tcx, body);
    // Trust (wave-WB8): the chain in-transit reborrow pairs `_u = g(..); _t = &(*_u);
    // f(move _t)` — the two locals the chain-forward marker emission mints for a
    // reference-returning inner call, admitted by their pair-linked single-def /
    // mentions == 2 shape (`transit_pair_temps` proves the address rides only in transit).
    let transit_pairs = transit_pair_temps(tcx, body);
    // Trust (wave-WB): the lone call-dest forward temps `_t = f(..); g(move _t)` — the wall-B
    // "lone-source relay" class (thin pointee) and its in-transit `&str` sibling, admitted below
    // by their single-calldest-def / single-call-arg-use shape (`calldest_forward_temps` proves
    // total value-mentions == 2, so no other observation exists).
    let calldest_fwd = calldest_forward_temps(tcx, body);
    // Trust (wave-W3): the deref-recursion reference relay — the arm binding, its argument
    // reborrow, the accessor's destination and its autoref, each proven (mentions == 2) to be an
    // address in transit that this body never dereferences. See [`deref_relay_temps`].
    let relay = deref_relay_temps(tcx, body);
    // Trust (wave-GH2): NON-arg struct temps holding a call result consumed whole by a later call
    // (`_2 = Arguments::from_str(..); _print(move _2)`). Copy + Drop-free + concrete only
    // (`temp_struct_ty_ok`); every mention confined by `struct_temps_confined` below.
    let mut struct_val_temps: HashSet<Local> = HashSet::new();
    // Trust (wave-WB): NON-arg FIELDLESS-enum temps holding a call result consumed whole
    // (`_t = trust(_1); needs_recheck(move _t)`). Copy + Drop-free + concrete + fieldless only
    // (`temp_enum_ty_ok`); every mention confined by `enum_temps_confined` below.
    let mut enum_val_temps: HashSet<Local> = HashSet::new();
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
        // Trust (wave-EP): the arm-binding payload temp `_t: &S`. Its borrow-into-temp and its one
        // deref-read are admitted by the `Rvalue::Ref` arm + `operand_ok`; the `payload_borrow_temps`
        // scan proved it is used ONLY there (mentions == 2), so every replayed pass is total over it
        // exactly as over the wave-29b/wave-30 interior temps.
        if payload_temps.contains(&l) {
            continue;
        }
        // Trust (wave-AF): the address-forward temp `_t: &FieldTy` with `FieldTy` NOT a fragment
        // scalar — `_t = &((*_p).k); g(copy _t)` and its `[Deref, Downcast, Field]` twin. Its
        // borrow-into-temp is admitted by the `Rvalue::Ref` arm + `RefArgForwardGuard`, and its
        // one call-argument use by `operand_ok` (a bare local place). `addr_forward_temps` proved
        // it is used ONLY there (mentions == 2), so `_t` is NEVER DEREFERENCED and no value of
        // `FieldTy` is ever produced in this body — which is why `FieldTy`'s drop glue and width
        // are not this fragment's business. `thin_shared_pointee_ok` separately keeps `_t` a THIN
        // pointer, the one thing the retired `scalar_ok(fty)` was silently supplying.
        if addr_fwd_temps.contains(&l) {
            continue;
        }
        // Trust (wave-W3): a relay member `_t: &P` with `P` NOT a fragment scalar — the four
        // links of `x.p()` through an overloaded `Deref`. Its def is admitted by the `Rvalue::Ref`
        // arm (`is_relay_borrow`) or, for the accessor destination, by the `Call` arm's bare-local
        // destination; its one use by `operand_ok` (a bare local place) or by the reborrow that
        // names it. `deref_relay_temps` proved it is used ONLY there (mentions == 2), so `_t` is
        // never dereferenced and no value of `P` is ever produced in this body.
        if relay.contains(&l) {
            continue;
        }
        // Trust (wave-FR): a call-forward reborrow temp `_t: &T` / `&mut T` — the tail call's
        // argument temp. Its def is admitted by the `Rvalue::Ref` arms (shared and mut), its
        // one use by `operand_ok` (a bare local place moved as a call argument);
        // `call_fwd_reborrow_temps` proved it is used ONLY there (mentions == 2), so `_t` is
        // NEVER DEREFERENCED, never stored through and never re-borrowed in this body — an
        // address in transit, on wave-30's exact footing, with the pointee separately pinned
        // concrete + THIN.
        if call_fwd_temps.contains(&l) {
            continue;
        }
        // Trust (lane EM): a `&str`-literal argument pair member — the literal's own local
        // `_u = const "..."` or the argument temp `_t = &(*_u)`. `str_lit_pair_temps` proved
        // the pair-linked single-def / mentions == 2 shape: `_u` is the const def + the one
        // borrow base, `_t` is the borrow def + one bare call-argument move — so the fat
        // `(ptr, len)` pair is never split, stored, re-borrowed or dereferenced here, and no
        // value of `str` is ever produced in this body.
        if str_lit_pairs.contains(&l) {
            continue;
        }
        // Trust (wave-WB8): a chain in-transit pair member — the inner call's destination
        // `_u` or the outer argument temp `_t = &(*_u)`. `transit_pair_temps` proved the
        // pair-linked single-def / mentions == 2 shape: `_u` is the call-dest write + the one
        // borrow base, `_t` is the borrow def + one bare call-argument move — so the address
        // (thin, or the one admitted `str` fat pair) is never split, stored, re-borrowed or
        // dereferenced here, and no value of the pointee is ever produced in this body.
        if transit_pairs.contains(&l) {
            continue;
        }
        // Trust (lane S1F): an explicit-borrow field pair member — the inner local
        // `_u = &((*_p).0)` or the argument temp `_t = &(*_u)`. `field_pair_temps` proved the
        // pair-linked single-def / mentions == 2 shape on both, so the address is never
        // dereferenced, stored, re-borrowed or split here, and no value of the pointee is ever
        // produced in this body — wave-AF's footing, pair-linked as lane EM's.
        if field_pairs.contains(&l) {
            continue;
        }
        // Trust (lane S1F): a reborrowed-return call-destination temp `_d: &P`. Its def is
        // admitted by the `Call` arm's bare-local destination, its one use by the `Rvalue::Ref`
        // arm's `_0 = &(*_d)` clause; `calldest_ret_reborrow_temps` proved it is used ONLY
        // there (mentions == 2), so `_d` is never dereferenced, stored through or re-borrowed
        // elsewhere — an address in transit on wave-WB's exact footing.
        if calldest_ret.contains(&l) {
            continue;
        }
        // Trust (wave-WB): a lone call-dest forward temp `_t: &P` (thin class) or `_t: &str`
        // (in-transit fat class). Its def is admitted by the `Call` arm's bare-local
        // destination (`place_ok` empty-projection), its one use by `operand_ok` (a bare local
        // place as a call argument); `calldest_forward_temps` proved it is used ONLY there
        // (mentions == 2), so `_t` is NEVER DEREFERENCED, never stored through and never
        // re-borrowed in this body — an address in transit on wave-AF's exact footing. The
        // `str` class additionally rides its `(ptr, len)` metadata as an opaque immediate this
        // body provably never splits (see `calldest_forward_temps`).
        if calldest_fwd.contains(&l) {
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
        } else if !is_arg && l.as_usize() != 0 && temp_enum_ty_ok(tcx, decl.ty) {
            // Trust (wave-WB): a NON-arg FIELDLESS-enum TEMP holding a call result consumed
            // whole — `ConstantOrigin::needs_recheck`'s `_t: OriginTrust`, `BinderData::
            // default`'s `_t: BinderInfo`. `enum_temps_confined` (below) proves every mention
            // is the bare call-dest write or a bare whole Copy/Move operand read — nothing a
            // replayed pass could act on beyond ordinary total MIR (the wave-GH2 argument over
            // a strictly simpler layout: a bare discriminant scalar).
            enum_val_temps.insert(l);
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
        ref_args_forward_only(
            body,
            &fwd_ref_args,
            &interior_arg_temps,
            &payload_temps,
            &addr_fwd_temps,
            &relay.srcs,
            &call_fwd_temps,
            &field_pairs.inners,
        )?;
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
    // Trust (wave-WB): every fieldless-enum call-result temp admitted above must appear ONLY as
    // the bare call-destination write or a bare whole Copy/Move operand read.
    if !enum_val_temps.is_empty() {
        enum_temps_confined(body, &enum_val_temps)?;
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
                        Rvalue::Use(op, _) => operand_ok(body, &payload_temps, op)?,
                        Rvalue::BinaryOp(_, ops) => {
                            operand_ok(body, &payload_temps, &ops.0)?;
                            operand_ok(body, &payload_temps, &ops.1)?;
                        }
                        Rvalue::UnaryOp(_, op) => operand_ok(body, &payload_temps, op)?,
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
                            operand_ok(body, &payload_temps, op)?;
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
                                    || interior_arg_temps.contains(&place.local)
                                    || payload_temps.contains(&place.local)
                                    || addr_fwd_temps.contains(&place.local)
                                    || relay.contains(&place.local)
                                    || call_fwd_temps.contains(&place.local)
                                    || str_lit_pairs.args.contains(&place.local)
                                    || transit_pairs.args.contains(&place.local)
                                    || field_pairs.contains(&place.local)) =>
                        {
                            // The `_0 = &(*_t)` reborrow of an interior temp (wave-29b): `[Deref]` on a
                            // certified interior temp is total (a plain deref of a `&FieldTy` temp the
                            // `interior_arg_temps` scan proved is single-use). Any other borrowed place
                            // must pass `place_ok` (the `[Deref, Field(scalar)]` interior shape).
                            let is_temp_reborrow = borrowed.projection.len() == 1
                                && matches!(borrowed.projection[0], ProjectionElem::Deref)
                                && interior_arg_temps.contains(&borrowed.local);
                            // Trust (wave-EP): the arm-binding borrow `_t = &(((*_p) as V).k)` —
                            // the SAME `[Deref, Downcast, Field(scalar)]` place `operand_ok`
                            // already certifies on the read path, on the same shared-ref enum arg
                            // base. Borrowing it is total wherever reading it is; `place_ok` is
                            // direction-blind and deliberately carries no 3-level arm, so the
                            // admission is spelled here, on the borrow path only.
                            let is_payload_borrow = payload_temps.contains(&place.local)
                                && is_ref_enum_payload_read(body, borrowed);
                            // Trust (wave-AF): the address-forward borrow — the SAME two interior
                            // places, with the field type NOT required to be a fragment scalar.
                            // `place_ok` is direction-blind and is called on assign DESTINATIONS,
                            // so the non-scalar admission is spelled HERE, on the borrow path
                            // only, and can never be reached by a store. `addr_forward_temps`
                            // certified the base (a SHARED-ref ARG), the field type (concrete,
                            // thin, equal to `_t`'s pointee), and — decisively — that `_t` is
                            // never dereferenced.
                            let is_addr_fwd_borrow = addr_fwd_temps.contains(&place.local)
                                && interior_field_ty(body, borrowed).is_some();
                            // Trust (wave-W3): the relay's two borrow defs — a SOURCE's interior
                            // place, and a FORWARD's bare `(*_s)` reborrow of a SOURCE. Spelled
                            // here, on the borrow path, for `place_ok`'s own stated reason: it is
                            // direction-blind, so neither shape may become an arm of it.
                            let is_relay = is_relay_borrow(body, &relay, place, borrowed);
                            // Trust (wave-FR): the call-forward reborrow def `_t = &(*_p)` — a
                            // bare `[Deref]` of a SHARED ref ARG into a certified
                            // `call_fwd_reborrow_temps` local. `place_ok`'s `[Deref]` arm pins
                            // its pointee to a fragment SCALAR (it certifies a READ, which
                            // produces a value); this borrow produces only the ADDRESS, the
                            // scan proved `_t` is never dereferenced here, and the pointee is
                            // separately pinned concrete + THIN — so the admission is spelled
                            // HERE, on the borrow path only, where a store can never reach it
                            // (wave-AF's own siting argument, verbatim).
                            let is_call_fwd_borrow = call_fwd_temps.contains(&place.local)
                                && borrowed.projection.len() == 1
                                && matches!(borrowed.projection[0], ProjectionElem::Deref)
                                && borrowed.local.as_usize() >= 1
                                && borrowed.local.as_usize() <= body.arg_count;
                            // Trust (lane EM): the `&str`-literal pair's borrow def
                            // `_t = &(*_u)` — a bare `[Deref]` of the pair's own LITERAL
                            // local into its certified arg temp. This is the fragment's ONE
                            // fat borrow def, and it is pair-pinned on BOTH sides:
                            // `str_lit_pair_temps` certified `_t`'s set membership AND that
                            // `_u` is `_t`'s one linked base (const-defed, mentions == 2), so
                            // a borrow of any OTHER local into `_t` — or of `_u` into any
                            // other destination — still lands in `place_ok` and is refused.
                            // Spelled here, on the borrow path only, where a store can never
                            // reach it (wave-AF's siting argument, verbatim).
                            let is_str_lit_pair_borrow = str_lit_pairs.args.contains(&place.local)
                                && borrowed.projection.len() == 1
                                && matches!(borrowed.projection[0], ProjectionElem::Deref)
                                && str_lit_pairs.lits.contains(&borrowed.local);
                            // Trust (wave-WB8): the chain pair's borrow def `_t = &(*_u)` —
                            // a bare `[Deref]` of the pair's own certified in-transit call
                            // destination into its certified arg temp, pair-pinned on BOTH
                            // sides exactly as the `&str`-literal pair is: a borrow of any
                            // OTHER local into `_t`, or of `_u` into any other destination,
                            // still lands in `place_ok` and is refused. Spelled here, on the
                            // borrow path only, where a store can never reach it (wave-AF's
                            // siting argument, verbatim).
                            let is_transit_pair_borrow = transit_pairs.args.contains(&place.local)
                                && borrowed.projection.len() == 1
                                && matches!(borrowed.projection[0], ProjectionElem::Deref)
                                && transit_pairs.dests.contains(&borrowed.local);
                            // Trust (lane S1F): the explicit-borrow field pair's two defs —
                            // the INNER `_u = &((*_p).0: F)` (wave-AF's interior place, field
                            // type not required to be a fragment scalar, into a certified
                            // inner local) and the OUTER `_t = &(*_u)` (a bare `[Deref]` of
                            // the pair's own certified inner into its certified arg temp,
                            // pair-pinned on BOTH sides exactly as the `&str`-literal pair
                            // is). Spelled here, on the borrow path only (wave-AF's siting
                            // argument, verbatim).
                            let is_field_pair_inner_borrow =
                                field_pairs.inners.contains(&place.local)
                                    && interior_field_ty(body, borrowed).is_some();
                            let is_field_pair_reborrow = field_pairs.args.contains(&place.local)
                                && borrowed.projection.len() == 1
                                && matches!(borrowed.projection[0], ProjectionElem::Deref)
                                && field_pairs.inners.contains(&borrowed.local);
                            // Trust (lane S1F): the reborrowed return `_0 = &(*_d)` — a bare
                            // `[Deref]` of a certified call-destination temp into bare `_0`,
                            // wave-29b's return-getter use with the call-destination def.
                            let is_calldest_ret_reborrow = place.local == RETURN_PLACE
                                && borrowed.projection.len() == 1
                                && matches!(borrowed.projection[0], ProjectionElem::Deref)
                                && calldest_ret.contains(&borrowed.local);
                            if !is_temp_reborrow
                                && !is_payload_borrow
                                && !is_addr_fwd_borrow
                                && !is_relay
                                && !is_call_fwd_borrow
                                && !is_str_lit_pair_borrow
                                && !is_transit_pair_borrow
                                && !is_field_pair_inner_borrow
                                && !is_field_pair_reborrow
                                && !is_calldest_ret_reborrow
                            {
                                place_ok(body, borrowed)?;
                            }
                        }
                        // Trust (wave-FR): the MUT call-forward reborrow def `_t = &mut (*_p)`
                        // — the `&mut T` argument temp of the same tail-call class, admitted
                        // ONLY into a certified `call_fwd_reborrow_temps` local (whose scan
                        // already pinned the borrow kind to `Mut { Default }` MATCHING the
                        // temp's own declared mutability, the base to an ARG declared at `_t`'s
                        // exact region-erased type, and the pointee concrete + THIN). No other
                        // destination may take a `&mut` borrow: anything outside the set still
                        // lands in the fail-closed `other =>` arm below. The referent mutation
                        // happens in the CALLEE, exactly as it already does when this body
                        // forwards `_p` bare — the wave-8a form this emission replaces.
                        Rvalue::Ref(
                            _,
                            BorrowKind::Mut { kind: rustc_middle::mir::MutBorrowKind::Default },
                            borrowed,
                        ) if place.projection.is_empty()
                            && call_fwd_temps.contains(&place.local)
                            && borrowed.projection.len() == 1
                            && matches!(borrowed.projection[0], ProjectionElem::Deref)
                            && borrowed.local.as_usize() >= 1
                            && borrowed.local.as_usize() <= body.arg_count => {}
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
                                operand_ok(body, &payload_temps, op)?;
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
                        // Trust (T2, SHARED-REF discriminant-read FLIP): the by-REF twin of the
                        // arm above — `_d = Discriminant((*_p))` where `_p` is a forwarded SHARED
                        // ref arg, read at projection EXACTLY `[Deref]`, into a fragment scalar.
                        // This is the shape every `&self` enum accessor takes, and it is what
                        // `to_mir`'s shared-ref enum `Load` recognizer emits.
                        //
                        // Same three certificates as the by-value arm, one of them stronger: the
                        // comparator's `disc(ty, place)` observable pins the source place (now
                        // including its `Deref`), the reshaped `SwitchInt` reconstructs the
                        // dispatch from already-admitted terminators, and `ref_args_forward_only`
                        // confines every OTHER mention of `_p` to a forwarded call argument — the
                        // by-ref analogue of `enum_args_disc_read_only`. Stronger, because a
                        // shared reference cannot be written through at all, so unlike a by-value
                        // enum arg there is no store that could make the single derived SSA `Load`
                        // disagree with built's re-read at the use site.
                        Rvalue::Discriminant(d)
                            if d.projection.len() == 1
                                && matches!(d.projection[0], ProjectionElem::Deref)
                                && fwd_ref_args.contains(&d.local)
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
                //
                // Trust (wave-EP, 2026-08-16): a THIRD admitted non-scalar marked local — the
                // arm-binding payload temp `_t: &FieldTy` of `StorageLive(t);
                // t = &(((*_p) as V).k); _x = copy (*t); StorageDead(t)`, which is byte-for-byte
                // built's own arm binding. The argument is wave-29b's, unchanged: the
                // `payload_borrow_temps` scan proved this ref temp is used ONLY as its single
                // borrow-def + single deref-read (value-mentions == 2), so every pass is total over
                // the marker exactly as over a scalar one, and the two marker sequences coincide
                // by construction — that is what `markers_exact` then verifies against built.
                StatementKind::StorageLive(l) | StatementKind::StorageDead(l) => {
                    // Trust (wave-W3): a FOURTH admitted non-scalar marked local — a relay
                    // member. Built's own match lowering brackets all four links with
                    // `StorageLive`/`StorageDead` (28 marker lines on `Level::is_zero`), which is
                    // exactly what wave-DR reproduces, so `markers_exact` holds only if these
                    // markers are here. The argument is wave-29b's, unchanged: the mentions == 2
                    // scan proved the local is used ONLY as its def + one use, so every pass is
                    // total over the marker exactly as over a scalar one.
                    // Trust (wave-MC, 2026-08-20): a FIFTH admitted non-scalar marked local —
                    // the by-value CALL-ARGUMENT temp `_t: S` of `StorageLive(_t);
                    // _t = copy _param; f(move _t); StorageDead(_t)`, which is byte-for-byte
                    // built's own `as_operand` -> `as_temp` (measured verbatim in
                    // `crates/trust-thir-lower/probes/mc_call.rs`, and quoted on
                    // `to_mir::plan_call_markers`).
                    //
                    // The argument is wave-29b's, and it is STRONGER here rather than weaker:
                    //   * `temp_struct_ty_ok` already required `S` to be a CONCRETE struct that is
                    //     `Copy` AND `!needs_drop`, so `ElaborateDrops`/`AbortUnwindingCalls` find
                    //     nothing to elaborate on it — the property wave-29b had to argue from the
                    //     mention count, this one has from the TYPE;
                    //   * `struct_temps_confined` has ALREADY RUN (above, before this loop) and
                    //     proved every mention of `_t` is the bare whole-value store that defines
                    //     it, a whole non-mutating read, a scalar field read, or a call-destination
                    //     write — so no pass can observe a shape the shim did not emit;
                    //   * and the two marker SEQUENCES coincide by construction, which
                    //     `markers_exact` then verifies against built. At `-O0`
                    //     `RemoveStorageMarkers` deletes them; at `-O` codegen emits matching
                    //     `llvm.lifetime` intrinsics precisely because the sequences agree.
                    //
                    // WITHOUT THIS the class is unreachable and the refusal is loud rather than
                    // silent: `reason="storage marker on non-scalar local _3"`, measured on
                    // `clean_kernel::expr::meta::ExprMeta::has_loose_bvars` with
                    // `markers_exact: true` and `4 marker line(s) identical` already in hand.
                    if !scalar_ok(body.local_decls[*l].ty)
                        && !interior_arg_temps.contains(l)
                        && !payload_temps.contains(l)
                        && !unit_regions.contains(l)
                        && !relay.contains(l)
                        && !struct_val_temps.contains(l)
                        && !call_fwd_temps.contains(l)
                        // Trust (wave-WB): the lone call-dest forward temps and the fieldless-
                        // enum call-result temps carry built's own storage spans; the mentions
                        // == 2 scan (calldest) / the confinement guard (enum, Copy + Drop-free
                        // by type) prove every pass is total over the marker exactly as over a
                        // scalar one — wave-29b's argument, unchanged.
                        && !calldest_fwd.contains(l)
                        && !enum_val_temps.contains(l)
                        // Trust (lane EM): the `&str`-literal pair's two locals carry built's
                        // own storage spans (`StorageLive(_3); StorageLive(_4); ...;
                        // StorageDead(_3); ...; StorageDead(_4)`, measured verbatim on
                        // `f.write_str("hello")`); the pair-linked mentions == 2 scan proved
                        // every pass is total over the markers exactly as over a scalar one —
                        // wave-29b's argument, unchanged.
                        && !str_lit_pairs.contains(l)
                        // Trust (wave-WB8): the chain pair's two locals carry built's own
                        // storage spans (`StorageLive(_4); StorageLive(_5); …;
                        // StorageDead(_4); …; StorageDead(_5)`, measured verbatim on
                        // `f.write_str(self.name())`); the pair-linked mentions == 2 scan
                        // proved every pass is total over the markers exactly as over a
                        // scalar one — wave-29b's argument, unchanged.
                        && !transit_pairs.contains(l)
                        // Trust (lane S1F, 2026-08-22): the ADDRESS-FORWARD temp `_t: &F` with
                        // `F` NOT a fragment scalar — `StorageLive(_t); _t = &((*_p).0: F);
                        // g(move _t); StorageDead(_t)`, the call-forward plan's FIELD-projection
                        // class, byte-for-byte built's own `as_operand` -> `as_temp` interior
                        // borrow of a `self.map.len()` receiver (measured verbatim,
                        // `probes/s1f.rs` a1: `_2 = &((*_1).0: HashMap<u64, u64>)`). The set
                        // itself is wave-AF's, unchanged; what is new is ONLY that its members
                        // may carry the pair. The argument is wave-FR's for the bare reborrow,
                        // and it is the same argument because it rests on the same facts:
                        // `addr_forward_temps` proved (value-mentions == 2) that `_t` is its one
                        // borrow def and its one call-argument use and NOTHING else — never
                        // dereferenced, never stored, never reborrowed — so no value of `F` is
                        // produced in this body and `F`'s width and drop glue are not its
                        // business; `&F` is `Copy` and `!needs_drop` by construction, so
                        // `ElaborateDrops` finds nothing to elaborate; and the pointee is
                        // separately pinned concrete + THIN (`thin_shared_pointee_ok`). Storage
                        // markers are `NonUse` and do not enter the mention count, so the set
                        // admits the marked and the unmarked temp alike; `RemoveStorageMarkers`
                        // deletes the pair at `-O0` and codegen emits matching `llvm.lifetime`
                        // intrinsics at `-O` precisely because the sequences agree — which
                        // `markers_exact` verifies against built regardless.
                        //
                        // WITHOUT THIS the class is unreachable and the refusal is loud rather
                        // than silent: `reason="storage marker on non-scalar local _2"` on
                        // every `&HashMap`/`&Vec` forwarder the plan admits.
                        && !addr_fwd_temps.contains(l)
                        // Trust (lane S1F): the unit-statement form's `()` call-destination
                        // temp carries built's own storage span (`StorageLive(_2); …;
                        // StorageDead(_2); _0 = const ()`, measured verbatim on `{ f(self); }`);
                        // `unit_calldest_temps` proved its one mention is the call's write of
                        // a ZST, so every pass is total over the marker exactly as over a
                        // scalar one — wave-29b's argument, with the type doing the work.
                        && !unit_calldest.contains(l)
                        // Trust (lane S1F): the explicit-borrow field pair's two locals carry
                        // built's own storage spans (`live _3; live _4; …; dead _4; dead _3`,
                        // measured verbatim on the derived `Ord::cmp`); the pair-linked
                        // mentions == 2 scan proved every pass is total over the markers
                        // exactly as over a scalar one — wave-29b's argument, unchanged.
                        && !field_pairs.contains(l)
                        // Trust (lane S1F): the reborrowed-return destination temp carries
                        // built's own storage span (`live _2; …; _0 = &(*_2); dead _3;
                        // dead _2`, measured verbatim on `{ self.resources() }`); the mentions
                        // == 2 scan proved every pass is total over the marker exactly as over
                        // a scalar one — wave-29b's argument, unchanged.
                        && !calldest_ret.contains(l)
                    {
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
            TerminatorKind::Goto { target, .. } => target_ok(*target)?,
            TerminatorKind::SwitchInt { discr, targets } => {
                operand_ok(body, &payload_temps, discr)?;
                for t in targets.all_targets() {
                    target_ok(*t)?;
                }
            }
            TerminatorKind::Assert { cond, msg, target, unwind, .. } => {
                operand_ok(body, &payload_temps, cond)?;
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
                    operand_ok(body, &payload_temps, &a.node)?;
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
                            // Trust (wave-WB): the same parity hazard applies to a whole-
                            // ENUM `Copy` arg (wave-WB admits enum call-result temps as whole
                            // call args). A fieldless enum is an Immediate scalar and never
                            // trips this, but the gate checks the layout rather than assume
                            // the set stayed fieldless — fail closed on any memory-ABI Adt.
                            if matches!(aty.kind(), ty::Adt(adt, _) if adt.is_struct() || adt.is_enum())
                            {
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
                // passed the local-decl gate above — a fragment scalar/unit, a wave-J callee-return
                // struct/enum, or (wave-W3) a relay SOURCE `&P`, which that gate admitted only
                // after proving the local is an address this body never dereferences).
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
            TerminatorKind::Goto { target, .. } => vec![*target],
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
            // correspondence carries over verbatim.
            //
            // Trust (wave-W3b, 2026-08-20): `Unreachable` joins `Continue`, and the reason is
            // that this walk runs over BOTH bodies AT DIFFERENT PHASES. The clause was written
            // for a `panic=unwind` world — "the normal sibling is post-
            // `run_analysis_to_runtime_passes`, where `RemoveNoopLandingPads` already normalized
            // the built `Cleanup(lone-resume)` to `Continue`". Under `panic=abort` that premise
            // is FALSE and unsatisfiable: `AbortUnwindingCalls`
            // (`rustc_mir_transform::abort_unwinding_calls`, inside
            // `run_runtime_lowering_passes`) sees `layout::fn_can_unwind == false` for every
            // Rust-ABI callee and rewrites EVERY call's unwind to `UnwindAction::Unreachable`.
            // So on a `panic=abort` crate NO call-carrying body can present a `Continue` built
            // call, and this walk refused every one of them — measured on `clean-kernel`
            // (`profile.release` sets `panic = "abort"`): **403 bodies at `-O0`**, and at `-O3`
            // it is what stood between `level::Level::is_zero` / `::is_nonzero` and the flip
            // once wave-W3 cleared their locals.
            //
            // Admitting it does NOT weaken the derived fragment, and that is checked, not
            // argued: `gate_derived_body`'s own `Call` arm still requires
            // `UnwindAction::Continue` on the DERIVED body and runs BEFORE this walk
            // (`derive_flip_body` calls the gate, then `verify_assert_parity`). What changes is
            // only what this walk tolerates on the BUILT sibling — a body the flip does not
            // produce and does not control.
            //
            // The two bodies still agree by CONSTRUCTION at codegen: `advance_built_to_runtime`
            // replays `run_analysis_to_runtime_passes` — the same public entry, the same
            // `AbortUnwindingCalls`, the same session panic strategy and the same callee ABIs
            // (the call `func` operands are pinned to built's by `raw_call_channel` and the ABI
            // gate) — so the derived body receives the identical `Continue -> Unreachable`
            // rewrite before it ever reaches codegen.
            //
            // `Cleanup(bb)` stays REFUSED and that clause is the load-bearing one: a cleanup
            // successor is a block this DFS does not walk, so an `Assert` inside it would be
            // missing from the enumeration. `Terminate(_)` stays refused too (fail-closed; it is
            // the `!body_can_unwind` arm, a shape this fragment has never measured).
            // `Unreachable` carries NO successor block at all, so the enumeration stays complete.
            TerminatorKind::Call { target, unwind, .. } => {
                if !span_stitch_call_unwind_admits(unwind) {
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

/// Unlike the derived-body structural gate, span stitching walks the
/// post-runtime-pass built sibling as well. `panic=abort` rewrites its Rust
/// calls to `Unreachable`; cleanup-bearing and terminating shapes remain out
/// of fragment.
fn span_stitch_call_unwind_admits(unwind: &UnwindAction) -> bool {
    matches!(unwind, UnwindAction::Continue | UnwindAction::Unreachable)
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
pub(crate) fn verify_assert_parity<'tcx>(
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

#[cfg(test)]
mod w3_regression_tests {
    use rustc_middle::mir::UnwindTerminateReason;

    use super::*;

    const ACCEPT_PAIR: RelayPairFacts = RelayPairFacts {
        forward_reborrow_defs: 1,
        forward_root_defs: 0,
        forward_mentions: 2,
        forward_callarg_uses: 1,
        source_root_defs: 1,
        source_is_forward: false,
        source_mentions: 2,
        source_reborrow_use_is_exact: true,
        source_callarg_uses: 0,
    };

    #[test]
    fn w3_exact_source_forward_pair_admits() {
        assert!(
            relay_pair_admits(ACCEPT_PAIR),
            "a gate which refuses the exact four-temp W3 relay would make the lane vacuous",
        );
    }

    #[test]
    fn w3_wide_or_non_concrete_pointee_is_refused() {
        assert!(concrete_thin_pointee_admits(false, false, true));
        assert!(
            !concrete_thin_pointee_admits(false, false, false),
            "a wide Deref::Target such as str carries metadata this fragment does not model",
        );
        assert!(!concrete_thin_pointee_admits(true, false, true));
        assert!(!concrete_thin_pointee_admits(false, true, true));
    }

    #[test]
    fn w3_any_forbidden_extra_use_is_refused() {
        let mut extra_source_observation = ACCEPT_PAIR;
        extra_source_observation.source_mentions = 3;
        assert!(
            !relay_pair_admits(extra_source_observation),
            "a load, store, second reborrow, or other third source mention must close the lane",
        );

        let mut extra_forward_observation = ACCEPT_PAIR;
        extra_forward_observation.forward_mentions = 3;
        assert!(
            !relay_pair_admits(extra_forward_observation),
            "a load, store, or other third forward mention must close the lane",
        );

        let mut second_forward = ACCEPT_PAIR;
        second_forward.source_reborrow_use_is_exact = false;
        assert!(!relay_pair_admits(second_forward));

        let mut second_callarg = ACCEPT_PAIR;
        second_callarg.forward_callarg_uses = 2;
        assert!(!relay_pair_admits(second_callarg));
    }

    #[test]
    fn w3b_accepts_abort_unreachable_but_not_unwalked_unwind_shapes() {
        assert!(span_stitch_call_unwind_admits(&UnwindAction::Continue));
        assert!(
            span_stitch_call_unwind_admits(&UnwindAction::Unreachable),
            "panic=abort rewrites the built sibling to Unreachable before span stitching",
        );
        assert!(!span_stitch_call_unwind_admits(&UnwindAction::Cleanup(BasicBlock::from_u32(1),)));
        assert!(!span_stitch_call_unwind_admits(&UnwindAction::Terminate(
            UnwindTerminateReason::Abi,
        )));
    }

    const ACCEPT_CALLDEST: CallDestFwdFacts =
        CallDestFwdFacts { calldest_defs: 1, mentions: 2, callarg_uses: 1, self_feed: false };

    /// Trust (lane S1F): the storage-marker arm admits the address-forward set — and ONLY by
    /// membership in that set, whose mentions == 2 clause is the proof. The needle is BUILT
    /// FROM PARTS so this test's own source never contains it.
    #[test]
    fn s1f_storage_markers_are_admitted_on_address_forward_temps() {
        let src = include_str!("flip.rs");
        let needle = format!("&& !{}.contains(l)", "addr_fwd_temps");
        assert_eq!(
            src.matches(needle.as_str()).count(),
            1,
            "the field-projection class rides the wave-AF set's proof, in the marker arm, once"
        );
        let set = format!("let {} = {}(tcx, body);", "addr_fwd_temps", "addr_forward_temps");
        assert_eq!(src.matches(set.as_str()).count(), 1, "one set, one constructor");
    }

    const ACCEPT_FIELD_PAIR: FieldPairFacts = FieldPairFacts {
        u_borrow_defs: 1,
        u_mentions: 2,
        t_reborrow_defs: 1,
        t_mentions: 2,
        t_callarg_moves: 1,
        self_pair: false,
    };

    #[test]
    fn s1f_exact_field_pair_admits() {
        assert!(
            field_pair_admits(ACCEPT_FIELD_PAIR),
            "a gate which refuses the exact two-local explicit-borrow pair would make the \
             pair class vacuous",
        );
    }

    #[test]
    fn s1f_any_forbidden_field_pair_shape_is_refused() {
        for (i, mutate) in [
            (&|f: &mut FieldPairFacts| f.u_mentions = 3) as &dyn Fn(&mut FieldPairFacts),
            &|f| f.t_mentions = 3,
            &|f| f.u_borrow_defs = 0,
            &|f| f.u_borrow_defs = 2,
            &|f| f.t_reborrow_defs = 2,
            &|f| f.t_callarg_moves = 0,
            &|f| f.t_callarg_moves = 2,
            &|f| f.self_pair = true,
        ]
        .iter()
        .enumerate()
        {
            let mut f = ACCEPT_FIELD_PAIR;
            mutate(&mut f);
            assert!(!field_pair_admits(f), "mutant {i} must be refused: {f:?}");
        }
        let src = include_str!("flip.rs");
        let needle = format!("&& !{}.contains(l)", "field_pairs");
        assert_eq!(src.matches(needle.as_str()).count(), 1, "admitted in the marker arm, once");
    }

    const ACCEPT_CALLDEST_RET: CallDestRetFacts =
        CallDestRetFacts { calldest_defs: 1, mentions: 2, ret_reborrows: 1 };

    #[test]
    fn s1f_exact_calldest_ret_reborrow_admits() {
        assert!(
            calldest_ret_admits(ACCEPT_CALLDEST_RET),
            "a gate which refuses the exact reborrowed-return destination shape would make the \
             class vacuous",
        );
    }

    #[test]
    fn s1f_any_forbidden_calldest_ret_shape_is_refused() {
        for (i, mutate) in [
            (&|f: &mut CallDestRetFacts| f.mentions = 3) as &dyn Fn(&mut CallDestRetFacts),
            &|f| f.calldest_defs = 2,
            &|f| f.ret_reborrows = 0,
            &|f| f.ret_reborrows = 2,
            &|f| {
                f.calldest_defs = 0;
                f.mentions = 1;
            },
        ]
        .iter()
        .enumerate()
        {
            let mut f = ACCEPT_CALLDEST_RET;
            mutate(&mut f);
            assert!(!calldest_ret_admits(f), "mutant {i} must be refused: {f:?}");
        }
        let src = include_str!("flip.rs");
        let needle = format!("&& !{}.contains(l)", "calldest_ret");
        assert_eq!(src.matches(needle.as_str()).count(), 1, "admitted in the marker arm, once");
    }

    const ACCEPT_UNIT_CALLDEST: UnitCallDestFacts =
        UnitCallDestFacts { calldest_defs: 1, mentions: 1 };

    #[test]
    fn s1f_exact_unit_calldest_admits() {
        assert!(
            unit_calldest_admits(ACCEPT_UNIT_CALLDEST),
            "a gate which refuses the exact unit call-destination shape would make the \
             unit-statement class vacuous",
        );
    }

    #[test]
    fn s1f_any_forbidden_unit_calldest_shape_is_refused() {
        let mut read_back = ACCEPT_UNIT_CALLDEST;
        read_back.mentions = 2;
        assert!(!unit_calldest_admits(read_back), "a second mention is a read or a second write");
        let mut double_def = ACCEPT_UNIT_CALLDEST;
        double_def.calldest_defs = 2;
        double_def.mentions = 2;
        assert!(!unit_calldest_admits(double_def));
        let mut never_written = ACCEPT_UNIT_CALLDEST;
        never_written.calldest_defs = 0;
        never_written.mentions = 0;
        assert!(
            !unit_calldest_admits(never_written),
            "a never-written `()` local is `unit_region_temps`' business, not this set's"
        );
        let src = include_str!("flip.rs");
        let needle = format!("&& !{}.contains(l)", "unit_calldest");
        assert_eq!(src.matches(needle.as_str()).count(), 1, "admitted in the marker arm, once");
    }

    #[test]
    fn wb_exact_lone_calldest_forward_admits() {
        assert!(
            calldest_fwd_admits(ACCEPT_CALLDEST),
            "a gate which refuses the exact lone call-dest forward shape would make wave-WB vacuous",
        );
    }

    #[test]
    fn wb_any_forbidden_calldest_shape_is_refused() {
        let mut third_mention = ACCEPT_CALLDEST;
        third_mention.mentions = 3;
        assert!(
            !calldest_fwd_admits(third_mention),
            "a deref-read, store, re-borrow, second forward or projected use is a third mention \
             and must close the lane",
        );

        let mut no_use = ACCEPT_CALLDEST;
        no_use.callarg_uses = 0;
        no_use.mentions = 2;
        assert!(
            !calldest_fwd_admits(no_use),
            "two defs / a non-call-arg second mention must not ride the mentions count alone",
        );

        let mut double_def = ACCEPT_CALLDEST;
        double_def.calldest_defs = 2;
        assert!(!calldest_fwd_admits(double_def));

        let mut double_use = ACCEPT_CALLDEST;
        double_use.callarg_uses = 2;
        assert!(!calldest_fwd_admits(double_use));

        let mut self_feed = ACCEPT_CALLDEST;
        self_feed.self_feed = true;
        assert!(
            !calldest_fwd_admits(self_feed),
            "`_t = f(move _t)` reads an uninitialized local and must be refused explicitly",
        );
    }

    #[test]
    fn w3b_legacy_continue_only_mutant_is_killed() {
        let continue_only = |unwind: &UnwindAction| matches!(unwind, UnwindAction::Continue);
        assert!(!continue_only(&UnwindAction::Unreachable));
        assert!(span_stitch_call_unwind_admits(&UnwindAction::Unreachable));
    }

    const ACCEPT_STR_LIT_PAIR: StrLitPairFacts = StrLitPairFacts {
        borrow_defs: 1,
        const_defs: 1,
        t_mentions: 2,
        u_mentions: 2,
        t_callarg_moves: 1,
        self_pair: false,
    };

    #[test]
    fn em_exact_str_lit_pair_admits() {
        assert!(
            str_lit_pair_admits(ACCEPT_STR_LIT_PAIR),
            "a gate which refuses the exact two-local `&str`-literal pair would make the lane-EM \
             admission vacuous",
        );
    }

    #[test]
    fn em_any_forbidden_str_lit_pair_shape_is_refused() {
        let mut t_third_mention = ACCEPT_STR_LIT_PAIR;
        t_third_mention.t_mentions = 3;
        assert!(
            !str_lit_pair_admits(t_third_mention),
            "a deref-read, store, re-borrow, second forward or projected use of the arg temp is \
             a third mention and must close the lane",
        );

        let mut u_third_mention = ACCEPT_STR_LIT_PAIR;
        u_third_mention.u_mentions = 3;
        assert!(
            !str_lit_pair_admits(u_third_mention),
            "a second use of the literal local (a second reborrow, a call arg, a store) is a \
             third mention and must close the lane",
        );

        let mut no_const_def = ACCEPT_STR_LIT_PAIR;
        no_const_def.const_defs = 0;
        no_const_def.u_mentions = 2;
        assert!(
            !str_lit_pair_admits(no_const_def),
            "a base whose def is NOT the `&str` constant (a call dest, a borrow, an arg copy) \
             must not ride the mentions count alone",
        );

        let mut double_borrow_def = ACCEPT_STR_LIT_PAIR;
        double_borrow_def.borrow_defs = 2;
        assert!(!str_lit_pair_admits(double_borrow_def));

        let mut double_const_def = ACCEPT_STR_LIT_PAIR;
        double_const_def.const_defs = 2;
        assert!(!str_lit_pair_admits(double_const_def));

        let mut no_callarg = ACCEPT_STR_LIT_PAIR;
        no_callarg.t_callarg_moves = 0;
        assert!(
            !str_lit_pair_admits(no_callarg),
            "an arg temp whose one use is not a bare call-argument move (a return, a store \
             source) must be refused",
        );

        let mut double_callarg = ACCEPT_STR_LIT_PAIR;
        double_callarg.t_callarg_moves = 2;
        assert!(!str_lit_pair_admits(double_callarg));

        let mut self_pair = ACCEPT_STR_LIT_PAIR;
        self_pair.self_pair = true;
        assert!(
            !str_lit_pair_admits(self_pair),
            "`_t = &(*_t)` reads an uninitialized local and must be refused explicitly",
        );
    }

    const ACCEPT_TRANSIT_PAIR: TransitPairFacts = TransitPairFacts {
        borrow_defs: 1,
        u_calldest_defs: 1,
        t_mentions: 2,
        u_mentions: 2,
        t_callarg_moves: 1,
        self_pair: false,
    };

    #[test]
    fn wb8_exact_transit_pair_admits() {
        assert!(
            transit_pair_admits(ACCEPT_TRANSIT_PAIR),
            "a gate which refuses the exact two-local chain in-transit pair would make the \
             wave-WB8 admission vacuous",
        );
    }

    #[test]
    fn wb8_any_forbidden_transit_pair_shape_is_refused() {
        let mut t_third_mention = ACCEPT_TRANSIT_PAIR;
        t_third_mention.t_mentions = 3;
        assert!(
            !transit_pair_admits(t_third_mention),
            "a deref-read, store, re-borrow, second forward or projected use of the arg temp is \
             a third mention and must close the lane",
        );

        let mut u_third_mention = ACCEPT_TRANSIT_PAIR;
        u_third_mention.u_mentions = 3;
        assert!(
            !transit_pair_admits(u_third_mention),
            "a second use of the in-transit local (a second reborrow, a call arg, a store) is a \
             third mention and must close the lane",
        );

        let mut no_calldest_def = ACCEPT_TRANSIT_PAIR;
        no_calldest_def.u_calldest_defs = 0;
        assert!(
            !transit_pair_admits(no_calldest_def),
            "a base whose def is NOT a bare call destination (a const, a borrow, an arg copy) \
             must not ride the mentions count alone",
        );

        let mut double_borrow_def = ACCEPT_TRANSIT_PAIR;
        double_borrow_def.borrow_defs = 2;
        assert!(!transit_pair_admits(double_borrow_def));

        let mut double_calldest_def = ACCEPT_TRANSIT_PAIR;
        double_calldest_def.u_calldest_defs = 2;
        assert!(!transit_pair_admits(double_calldest_def));

        let mut no_callarg = ACCEPT_TRANSIT_PAIR;
        no_callarg.t_callarg_moves = 0;
        assert!(
            !transit_pair_admits(no_callarg),
            "an arg temp whose one use is not a bare call-argument move (a return, a store \
             source) must be refused",
        );

        let mut double_callarg = ACCEPT_TRANSIT_PAIR;
        double_callarg.t_callarg_moves = 2;
        assert!(!transit_pair_admits(double_callarg));

        let mut self_pair = ACCEPT_TRANSIT_PAIR;
        self_pair.self_pair = true;
        assert!(
            !transit_pair_admits(self_pair),
            "`_t = &(*_t)` reads an uninitialized local and must be refused explicitly",
        );
    }
}

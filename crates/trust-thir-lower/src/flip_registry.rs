//! Trust: the flip registry (P1 item 5) — plumbing the green verdict + `trust_ir::Module`
//! from the `mir_built` hook to the `optimized_mir` provider.
//!
//! The `build_mir_inner_impl` hook (rustc_mir_build) is the only seam where the THIR-side
//! lowering AND the derived-vs-built MIR differential verdict both exist. When the verdict is
//! `DerivedAgreed` — the shim-derived MIR was proven canonically identical to the freshly built
//! MIR — the hook calls [`record_green`], which snapshots the per-body `trust_ir::Module` here.
//! Later, `rustc_mir_transform::trust_ir_flip::try_flip` (called from `inner_optimized_mir`)
//! [`take`]s the Module, re-derives a `mir::Body` from it, and — after fail-closed gates — the
//! compiler consumes that derived MIR on the codegen path: the first real
//! "compiled from trust-ir" lane.
//!
//! Ordering is guaranteed by the query graph: `optimized_mir` → `mir_drops_elaborated…` →
//! `mir_promoted` → `mir_built` (the hook). If `mir_built` was loaded from an incremental cache
//! the hook never ran, the registry is empty, and every body takes the normal path — fail-closed.
//!
//! Thread-safe (`mir_built` runs in parallel) through Session-owned compiler state, like
//! [`crate::crate_module`]. Memory-bounded: only GREEN bodies are recorded (green ⇒ the
//! slice-1 scalar fragment ⇒ small Modules), and [`take`] removes the entry — `optimized_mir`
//! runs at most once per def per session.
//!
//! # Session gates ([`flip_session_enabled`], checked at RECORD time so the registry never
//! # accumulates when the flip cannot fire)
//!
//! * `-Z trust-ir-lower` — the flip is part of the trust-ir lane; the flag is the opt-in.
//! * `-Z trust-ir-flip=no` disables the lane entirely (byte-compare baseline
//!   for the equivalence probes). This is a tracked option because the lane
//!   directly selects codegen/CTFE MIR.
//! * no first-class `invariant`/`decreases` loop clauses. Their source names
//!   currently bind through MIR debug-place provenance, while the direct
//!   TrustIr module carries neither source-place identity nor `var_debug_info`.
//!   Flipping such a body would preserve execution but erase the verifier's
//!   only exact binder. The body stays on built MIR until that provenance rides
//!   TrustIr; ordinary contract-free bodies remain eligible.
//! * `-C debuginfo=0` only: the shim does not yet thread per-statement spans or
//!   `var_debug_info`, so flipping under debuginfo would silently degrade debug info.
//!   Fail-closed until spans ride trust-ir (P1.5). (Assert PANIC-LOCATION spans are already
//!   exact — [`crate::flip`] stitches them from the borrow-checked sibling.)
//! * no `-C instrument-coverage`: coverage mappings are span-derived; dummy spans would
//!   corrupt them.
//!
//! # Per-BODY marker gate (slice 3 — replaces the old `-O0`-only session gate)
//!
//! The shim emits no `StorageLive`/`StorageDead` (reconstruction from the Module alone is
//! provably impossible — `to_mir` module docs), so under `-O` a flipped body could lack the
//! LLVM lifetime hints the built body carries. Instead of gating the whole session to `-O0`,
//! [`record_green`] takes the derived-MIR differential's EXACT marker-channel verdict
//! (`DerivedReport::markers_exact`) and records a body at `-O` only when the marker
//! sequences were proven line-identical (today: the built body's reachable subgraph is
//! marker-free — unit fns, const-returning closures, param-identity bodies). When
//! `!sess.emit_lifetime_markers()` (`-O0`, no sanitizers) marker divergence is
//! codegen-immaterial — `RemoveStorageMarkers` (enabled exactly then, `mir_opt_level > 0`)
//! deletes markers+Nops from every body before codegen and codegen only emits
//! `llvm.lifetime` intrinsics under `emit_lifetime_markers()` — so `markers_exact` is not
//! required. The flip therefore flips what it can PROVE at each opt level, per body.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com> | Copyright 2026 | License: Apache-2.0

use std::collections::HashMap;

use rustc_middle::ty::TyCtxt;
use rustc_session::config::DebugInfo;
use rustc_span::def_id::LocalDefId;
use trust_ir::Module;

use crate::{CalleeRef, Lowered};

/// Green bodies for one compiler Session. The crate-local `DefIndex` is safe as
/// the key only inside that Session; a process-global registry let a later
/// rustc_driver Session consume stale MIR from an earlier crate at the same
/// index. Session storage is also the synchronization boundary for parallel
/// `mir_built` queries.
#[derive(Default)]
struct SessionFlipRegistry {
    entries: HashMap<u32, (Module, Vec<CalleeRef>)>,
    /// def_indexes that saw a SECOND `record_green` — the once-per-def
    /// invariant broke, so no lowering for that def may be trusted for the
    /// rest of the session (see `record_green`). `take` refuses them.
    poisoned: std::collections::HashSet<u32>,
}

/// Trust: all session-level flip gates (see module docs). Cheap; called per green body.
/// NOTE: lifetime markers are deliberately NOT a session gate anymore — they are a per-BODY
/// gate in [`record_green`] (`markers_exact`), so `-O` sessions flip what they can prove.
///
/// # What `debuginfo == None` costs, measured
///
/// The shim reconstructs MIR from the Module alone and the Module carries no
/// spans or `var_debug_info`, so a flipped body would silently lose the
/// line tables and local names the built body carries. That is not a
/// correctness question — it is a debugger-visible regression the flip has no
/// way to repair, so the session declines rather than emit a body it cannot
/// describe.
///
/// The scope of that decision deserves to be stated where the condition is,
/// because it is larger than it reads. targo's `dev` profile resolves to
/// `TomlDebugInfo::Full` and it emits `-C debuginfo` only when the level is not
/// `None`, so `dev` compiles carry `-C debuginfo=2` and `release` compiles carry
/// no debuginfo flag at all. Re-measured 2026-07-25 on a five-body scalar probe:
/// **5 flips with no `-C debuginfo` flag and at `=0`, 0 at `=1` and `=2`**, and
/// 3 at `-C opt-level=3` where the per-body marker gate takes the rest.
/// "Compiled from trust-ir" therefore describes debuginfo-free builds — a
/// `--release`-shaped profile — and never the default verified `targo trust
/// build`. (Earlier probe, kept because it shows the producer moving and the
/// cliff not: 4 at `-C debuginfo=0`, 1 at `-O`.)
///
/// The gate is not a coverage lever. Relaxing it to raise the flip rate would
/// trade real evidence for a bigger number; the way to widen this is to thread
/// spans and `var_debug_info` through the Module so a flipped body can carry
/// what it replaced.
pub fn flip_session_enabled(tcx: TyCtxt<'_>) -> bool {
    session_gates_allow_flip(
        tcx.sess.trust_ir_lower_enabled(),
        tcx.sess.opts.unstable_opts.trust_ir_flip,
        tcx.sess.opts.debuginfo,
        tcx.sess.instrument_coverage(),
    )
}

/// The gate above with the `TyCtxt` lifted out, so the scope it claims is a
/// test obligation and not just a comment. Splitting it is the only way the
/// measured numbers can be defended against a one-character edit.
pub const fn session_gates_allow_flip(
    trust_ir_lower_enabled: bool,
    trust_ir_flip_flag: bool,
    debuginfo: DebugInfo,
    instrument_coverage: bool,
) -> bool {
    trust_ir_lower_enabled
        && trust_ir_flip_flag
        && debuginfo_level_allows_flip(debuginfo)
        && !instrument_coverage
}

/// Exactly one debuginfo level is reproducible by the shim: the one that asks
/// for nothing. Every other level names line tables or locals the derived body
/// has no way to carry, so admitting it would emit a body that silently
/// describes itself wrongly to a debugger.
const fn debuginfo_level_allows_flip(debuginfo: DebugInfo) -> bool {
    match debuginfo {
        DebugInfo::None => true,
        // Trust (C2): line tables are NOT yet earned, and this arm records the measurement
        // rather than the intention. Widening it to `LineTablesOnly` was tried and REVERTED:
        // with the flip admitted at that level, `llvm-dwarfdump --debug-line` on a three-fn
        // probe disagreed with built on every row (built rows at cols 25/25/27/27/29,
        // derived at 30/27/34/29/33).
        //
        // The Module is NOT the problem — its spans are right. The artifact for the same
        // probe records `ret ; #loc: 0 2 24` (0-based col 24 = the `{`, i.e. built's 1-based
        // 25) and `and ; #loc: 0 3 26` (= built's 27). The defect is in CONSUMPTION:
        // `to_mir::set_span_from_node`'s CharPos -> BytePos reconstruction lands the wrong
        // byte for some nodes. Fix that, re-run the dwarfdump comparison, and this arm can
        // open honestly.
        //
        // `Limited`/`Full` additionally want the LEXICAL SCOPE TREE (`SourceScopeData`
        // nesting) and the derived body has exactly one fn-level scope, so they stay shut
        // beyond the line question.
        DebugInfo::LineDirectivesOnly
        | DebugInfo::LineTablesOnly
        | DebugInfo::Limited
        | DebugInfo::Full => false,
    }
}

fn loop_contract_count_allows_flip(first_class_loop_contracts: usize) -> bool {
    first_class_loop_contracts == 0
}

/// Whether this definition has enough source-place provenance for the current
/// TrustIr -> MIR flip. Native loop clauses are parser-island expressions whose
/// identifiers are rebound to MIR places during E4/E5 reconstruction. The
/// direct module does not carry that binding yet, so only a definition with no
/// first-class loop clauses may enter the flip registry.
pub fn source_place_provenance_allows_flip(tcx: TyCtxt<'_>, def: LocalDefId) -> bool {
    let first_class_loop_contracts = tcx
        .hir_maybe_body_owned_by(def)
        .and_then(|body| body.contract)
        .map_or(0, |contract| contract.loop_clauses.len());
    loop_contract_count_allows_flip(first_class_loop_contracts)
}

/// Trust: called from the `mir_built` hook for bodies whose derived-MIR differential verdict is
/// `DerivedAgreed` (the caller checks the verdict; `unsupported` is re-checked here defensively).
/// `markers_exact` is the differential's EXACT marker-channel verdict for THIS body; when the
/// session emits lifetime markers (`-O` / sanitizers) it is required (see module docs).
/// No-op unless every gate holds — the registry stays empty when the flip cannot fire.
pub fn record_green(tcx: TyCtxt<'_>, def: LocalDefId, lowered: &Lowered, markers_exact: bool) {
    if !flip_session_enabled(tcx) {
        return;
    }
    if !source_place_provenance_allows_flip(tcx, def) {
        return;
    }
    // Trust: per-body marker gate (module docs). Fail-closed: an unproven marker sequence
    // must never reach codegen where markers are material.
    if tcx.sess.emit_lifetime_markers() && !markers_exact {
        return;
    }
    // Defensive: a green verdict implies a clean lowering, but never trust the caller.
    if !lowered.unsupported.is_empty() {
        return;
    }
    // Trust (CTFE flip lane): FN bodies flip on the CODEGEN seam (`optimized_mir` → `try_flip`);
    // const/associated-const INITIALIZER bodies (`BodyKind::ConstInit`) flip on the CTFE seam
    // (`inner_mir_for_ctfe` → `try_flip_ctfe`), where the const-eval interpreter consumes MIR
    // re-derived from the trust-ir Module. `BodyKind::Fn` covers const FNs too — they are gated OUT
    // on BOTH seams (`flip::derive_flip_body`'s ConstFn arm rejects on the codegen seam;
    // `try_flip_ctfe`'s `Const|Static` pre-gate returns before `take` on the ctfe seam) so a const
    // fn can never get a split ctfe-vs-runtime body. STATIC initializers (`BodyKind::StaticInit`,
    // linkage / interior-mutability nuances) stay on built MIR pending a later wave. Any other body
    // kind is refused outright. The `pending_consts` gate below is a further defense: a const
    // initializer carrying un-evaluated placeholder sentinels is still refused.
    if !matches!(lowered.body_kind, crate::BodyKind::Fn | crate::BodyKind::ConstInit) {
        return;
    }
    // Trust: a pending-const body carries un-evaluated placeholder sentinels (patched only by
    // the crate finalizer, and only in the DUMP copy) — its Module must never reach codegen.
    // The derived-MIR differential already returns `DerivedUnsupported` for such bodies (so
    // the caller never sees a green verdict), but never trust the caller.
    if !lowered.pending_consts.is_empty() {
        return;
    }
    let def_index = def.to_def_id().index.as_u32();
    tcx.sess.with_trust_compiler_state::<SessionFlipRegistry, _>(|reg| {
        // `mir_built` runs once per def, so a SECOND registration for the same
        // def_index is an invariant violation — and a dangerous one. The
        // registry key is the bare DefIndex (no GenericArgs), while `take` is
        // consumed by `optimized_mir`/`mir_for_ctfe`, which are keyed on
        // LocalDefId. A first-write-wins `or_insert_with` would therefore let
        // ONE body's Module be codegen'd for the definition even if a later
        // registration carried a DIFFERENT lowering (e.g. a per-instance lane
        // specialized to one instantiation) — a silent MISCOMPILE with no
        // diagnostic. POISON instead: drop the entry and mark the def_index
        // permanently ineligible so `take` returns None and the body falls
        // back to built MIR (fail-closed, never a wrong body).
        match reg.entries.entry(def_index) {
            std::collections::hash_map::Entry::Vacant(v) => {
                v.insert((lowered.module.clone(), lowered.callees.clone()));
            }
            std::collections::hash_map::Entry::Occupied(o) => {
                o.remove();
                reg.poisoned.insert(def_index);
            }
        }
    });
}

/// Trust: consume the green `(Module, callee ledger)` for `def`, if any. Removing the entry
/// bounds memory and makes a second `take` (which cannot happen: `optimized_mir` runs once per
/// def per session) inert. A poisoned registry (panic while locked) yields `None` —
/// fail-closed to the normal path.
pub fn take(tcx: TyCtxt<'_>, def: LocalDefId) -> Option<(Module, Vec<CalleeRef>)> {
    let def_index = def.to_def_id().index.as_u32();
    tcx.sess.with_trust_compiler_state::<SessionFlipRegistry, _>(|reg| {
        // A poisoned def NEVER yields a module: the flip falls back to built
        // MIR rather than risk codegen'ing a body registered for different
        // args (see `record_green`).
        if reg.poisoned.contains(&def_index) {
            return None;
        }
        reg.entries.remove(&def_index)
    })
}

#[cfg(test)]
mod tests {
    use rustc_session::config::DebugInfo;

    use super::{loop_contract_count_allows_flip, session_gates_allow_flip};

    /// The measured scope of "compiled from trust-ir", pinned so it cannot be
    /// widened by editing one comparison. Measured 2026-07-25 on a five-body
    /// scalar probe against stage2 `d8a9eb292`: 5 flips at `-C debuginfo=0` and
    /// with no `-C debuginfo` flag at all, 0 at `-C debuginfo=1` and `=2`. targo
    /// emits `-C debuginfo=2` for the `dev` profile and no flag at all for
    /// `release`, so this predicate is the whole reason the default verified
    /// build flips nothing.
    #[test]
    fn only_debuginfo_free_sessions_flip() {
        assert!(
            session_gates_allow_flip(true, true, DebugInfo::None, false),
            "a debuginfo-free, coverage-free session with both flags on must flip"
        );
        for level in [
            DebugInfo::LineDirectivesOnly,
            DebugInfo::LineTablesOnly,
            DebugInfo::Limited,
            DebugInfo::Full,
        ] {
            assert!(
                !session_gates_allow_flip(true, true, level, false),
                "{level:?} asks for line tables or locals the shim cannot reconstruct; \
                 admitting it would emit a body that describes itself wrongly"
            );
        }
    }

    #[test]
    fn every_other_session_gate_is_independently_sufficient_to_decline() {
        assert!(
            !session_gates_allow_flip(false, true, DebugInfo::None, false),
            "the flip is part of the trust-ir lane; without the lowering there is no Module"
        );
        assert!(
            !session_gates_allow_flip(true, false, DebugInfo::None, false),
            "-Ztrust-ir-flip=no is the byte-compare negative control and must disable the lane"
        );
        assert!(
            !session_gates_allow_flip(true, true, DebugInfo::None, true),
            "coverage mappings are span-derived; the shim's dummy spans would corrupt them"
        );
    }

    #[test]
    fn first_class_loop_clauses_are_the_only_source_provenance_gate() {
        assert!(
            loop_contract_count_allows_flip(0),
            "an ordinary function must remain eligible at the source-provenance gate"
        );
        assert!(!loop_contract_count_allows_flip(1), "one native loop clause must block the flip");
        assert!(
            !loop_contract_count_allows_flip(2),
            "an invariant/decreases pair must block the flip as one provenance-sensitive lane"
        );
    }
}

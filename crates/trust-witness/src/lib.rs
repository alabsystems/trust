//! trust-witness — the typeck-moonshot warm-replay witness.
//!
//! "Elaborate once, check thereafter" (docs/TYPECK_MOONSHOT.md). rustc typeck
//! stays the expensive elaborator; on a cold compile we MINT a per-root
//! witness of the full downstream-consumed `TypeckResults` surface; on a warm
//! compile we DECODE + RE-INTERN + CHECK it and replay instead of re-inferring.
//! Every step is fail-safe: a miss / decode failure / check failure falls
//! through to real typeck (replay is an optimization, never an authority).
//!
//! This crate is the OUT-OF-TREE-validated core (P0: checker r=0.086, reintern
//! 0 mismatches, size 0.11-0.32x of rustc's incremental cache). The compiler
//! wiring (PLAN.md §2) consumes `encode_root`, `mintable`, `witness_key`,
//! `commit`, and — in later phases — the decode/reintern/checker path.
//!
//! Requires `rustc_private`; built only via `x.py build --stage 2`.
#![feature(rustc_private)]
// Mirror trust-thir-lower: rustc_private crates need `extern crate` for linkage
// even where edition-2021 path resolution makes the declaration path-unused.
#![allow(unused_extern_crates)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_ast_ir;
extern crate rustc_data_structures;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;
extern crate rustc_span;

pub mod checker;
pub mod decode;
pub mod encode;
pub mod key;
pub mod schema;
pub mod store;

use std::collections::BTreeMap;
use std::path::Path;

pub use checker::{CheckOutcome, accepts, check};
pub use decode::decode_and_reintern;
pub use encode::encode_root;
pub use key::{precise_witness_key, store_stem, witness_key};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::{TyCtxt, TypeckResults};

/// The v1 enabled-set predicate (PLAN.md §6): mint a root only when every
/// surviving `TypeckResults` field is checker-re-derivable or empty — i.e. the
/// "zero-trusted-residue" set. This is the SOUND-but-narrow v1 restriction; it
/// excludes the pick surface (method/operator resolutions), closures,
/// coroutines, and error-tainted results. Widening it is the A1-A3
/// forest-replay work, which stays future/experimental.
///
/// v1 checks the accessible exclusion fields; the in-tree Phase-0 wiring adds a
/// `rustc_middle` helper for the few private fields and the mint-time
/// checker self-run. Being conservative here is safe: Phase 0 does not consume
/// witnesses, so an over-mint is inert until the replay path (which re-checks).
pub fn mintable<'tcx>(tr: &TypeckResults<'tcx>, precise: bool) -> bool {
    use rustc_abi::ExternAbi;
    use rustc_hir::def::DefKind;
    use rustc_hir::{BindingMode, HirId, Safety};
    use rustc_middle::ty::TypeVisitableExt;
    tr.tainted_by_errors.is_none()
        // Mandatory cold-side completeness gate (TRUST lane). These fields are not
        // in the witness grammar and the decoder initializes them empty; accepting
        // a nonempty cold value would install results that differ from typeck. The
        // precise/parity lane never installs a decoded result — it returns real
        // typeck and only byte-compares — so an unencoded field is omitted
        // identically on both the mint and replay sides (same code) and parity
        // still holds. Relaxing this here is what admits closures (they populate
        // `closure_kind_origins` / `closure_size_eval`) into the shadow measurement.
        && (precise || tr.trust_witness_unencoded_fields_are_empty())
        // Method/operator picks (type_dependent_defs): admit only fully-
        // MONOMORPHIC, direct AssocFn picks (Follow-on 2). Their impl-selection
        // half is re-derived by the checker (Instance::try_resolve); their
        // name/probe-uniqueness half is key-attested under the whole-SVH key
        // (key::METHOD_PICKS_SOUND_UNDER_CURRENT_KEY). Off that key, or for any
        // non-AssocFn / generic pick, fall back to the method-free requirement.
        && (if key::METHOD_PICKS_SOUND_UNDER_CURRENT_KEY {
            tr.type_dependent_defs().items_in_stable_order().into_iter().all(|(id, r)| {
                matches!(r, Ok((DefKind::AssocFn, _)))
                    && tr
                        .node_args_opt(HirId { owner: tr.hir_owner, local_id: id })
                        .is_none_or(|a| !a.has_param())
            })
        } else {
            tr.type_dependent_defs().items_in_stable_order().is_empty()
        })
        // Splatted defs / method turbofish (user_provided_types) are not
        // reconstructed and would span_bug in the check-THIR build; exclude.
        && tr.splatted_defs().items_in_stable_order().is_empty()
        && tr.user_provided_types().items_in_stable_order().is_empty()
        // offset_of! (audit 2026-07-22, rank 3): offset_of_data is NOT encoded,
        // and the OffsetOf node lives in a nested anon-const child body the
        // root-body checker never walks — so an offset_of! root ACCEPTs, then a
        // later thir_body of the child const unwraps the empty offset_of_data map
        // -> ICE (a fail-safe breach). Exclude until child bodies are covered.
        && tr.offset_of_data().items_in_stable_order().is_empty()
        // No closures/coroutines (removes span-bearing fields and the
        // closure_captures -> typeck(root) cycle) — in the TRUST lane. The
        // precise/parity lane ADMITS them (scope widening): the reduced
        // `ty::Closure` encoding captures parent-args + the upvar tuple, the walk
        // set admits Closure children, and nothing is trusted — so these gates,
        // which exist only to protect trusted reconstruction, are lifted.
        && (precise || tr.closure_min_captures.is_empty())
        && (precise || tr.coroutine_stalled_predicates.is_empty())
        // v1 lossy-field SOUNDNESS gate (reconstruction-notes.md, decode.rs): the
        // decoder rebuilds pat_binding_modes as NONE, pat_adjustments as
        // BuiltinDeref, and liberated_fn_sigs as safe/Rust/non-variadic. The
        // linear checker validates node TYPES, not these, so a root whose real
        // values differ from those defaults could reconstruct wrong and slip the
        // checker. Mint only roots already at the defaults — excluding `let mut` /
        // `ref` bindings, match-ergonomics patterns, and unsafe/extern/variadic
        // fns. (Enriching these records to widen the set is future work.)
        && tr
            .pat_binding_modes()
            .items_in_stable_order()
            .into_iter()
            .all(|(_, m)| *m == BindingMode::NONE)
        && tr.pat_adjustments().items_in_stable_order().is_empty()
        && tr.liberated_fn_sigs().items_in_stable_order().into_iter().all(|(_, s)| {
            // splatted (audit 2026-07-22, rank 4): the splatted-arg index is not
            // round-tripped (decode rebuilds None), so a splatted root sig would
            // reconstruct wrong yet slip the checker — exclude it (trust lane).
            // A CLOSURE's liberated sig is `extern "rust-call"` (splatted, non-Rust
            // ABI), so this gate would sink every closure root. The precise/parity
            // lane never trusts the reconstruction — its sig input/output TYPES
            // still round-trip through encode_root — so admit non-Rust/splatted
            // sigs there (scope widening).
            precise
                || (s.safety() == Safety::Safe
                    && s.abi() == ExternAbi::Rust
                    && !s.c_variadic()
                    && s.splatted().is_none())
        })
}

/// Return `true` only when `root` owns exactly its primary body. The linear
/// checker validates one check-THIR body; every map in `TypeckResults` is
/// shared with inline/anonymous const and other typeck-child bodies. Checking
/// only child method picks is insufficient: a child-owned node type,
/// adjustment, field index, signature, or cast flag would still be installed
/// without being re-derived. Until replay checks the complete body forest,
/// exclude the whole root whenever its HIR owner contains another body.
pub fn root_body_is_sole_body(tcx: TyCtxt<'_>, root: LocalDefId) -> bool {
    let Some(body) = tcx.hir_maybe_body_owned_by(root) else {
        return false;
    };
    let body_id = body.id().hir_id;
    if body_id.owner.def_id != root {
        return false;
    }
    let bodies = &tcx.hir_owner_nodes(body_id.owner).bodies;
    bodies.len() == 1 && bodies.contains_key(&body_id.local_id)
}

/// Non-panicking equivalent of the root-body part of
/// `TyCtxt::hir_enclosing_body_owner`. Witness bytes carry `ItemLocalId`s, so
/// the replay authority must reject an out-of-range ID (or a valid ID outside
/// any body) instead of indexing the HIR table or reaching rustc's `bug!`.
fn local_id_is_in_root_body(
    tcx: TyCtxt<'_>,
    root: LocalDefId,
    owner: rustc_hir::OwnerId,
    mut local_id: rustc_hir::ItemLocalId,
) -> bool {
    let nodes = &tcx.hir_owner_nodes(owner).nodes;
    loop {
        let Some(node) = nodes.get(local_id) else {
            return false;
        };
        if local_id == rustc_hir::ItemLocalId::ZERO {
            return false;
        }
        let parent_id = node.parent;
        let Some(parent) = nodes.get(parent_id) else {
            return false;
        };
        if let Some((body_owner, _)) = parent.node.associated_body() {
            return body_owner == root;
        }
        local_id = parent_id;
    }
}

/// Coverage guard (audit 2026-07-22, rank 2): the linear checker walks ONLY the
/// root fn body's check-THIR, re-deriving each method/operator pick there
/// (Follow-on 2's `Instance::try_resolve` half). A pick keyed to a typeck-CHILD
/// body — an inline const `const { .. }` or an anon const, which share the
/// root's `TypeckResults` but are separate THIR bodies — is installed but NEVER
/// re-derived, so `trusted_weak` stays 0 and the root wrongly ACCEPTs. Require
/// every pick to be keyed inside the root body; a child-body pick makes the root
/// non-mintable / non-replayable (fail-safe MISS -> real typeck). Enforced at
/// BOTH mint (don't produce) and replay (the mandatory authority, sound against
/// any stored witness).
pub fn picks_all_in_root_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    root: LocalDefId,
    tr: &TypeckResults<'tcx>,
) -> bool {
    tr.type_dependent_defs()
        .items_in_stable_order()
        .into_iter()
        .all(|(local_id, _)| local_id_is_in_root_body(tcx, root, tr.hir_owner, local_id))
}

/// Forest-checking increment 1 (2026-07-23): the set of typeck bodies the replay
/// checker must WALK to soundly admit a root — the root plus every typeck-CHILD
/// body that shares its `TypeckResults`. `nested_bodies_within` returns exactly
/// those shared-TR children (value inline consts, closures, coroutines — NOT anon
/// consts, which are their own typeck roots). Increment 1 admits ONLY roots whose
/// every such child is a value inline const (`DefKind::InlineConst`); any closure
/// or coroutine child ⇒ `None` (fail-safe MISS — those need capture/upvar
/// round-tripping, a later increment). A root with no shared-TR children (or only
/// anon-const children) returns `Some([root])` and is the original sole-body lane.
pub fn forest_const_walk_set(
    tcx: TyCtxt<'_>,
    root: LocalDefId,
    precise: bool,
) -> Option<Vec<LocalDefId>> {
    use rustc_hir::def::DefKind;
    let body = tcx.hir_maybe_body_owned_by(root)?;
    if body.id().hir_id.owner.def_id != root {
        return None;
    }
    let mut set = vec![root];
    for child in tcx.nested_bodies_within(root).iter() {
        let admissible = tcx.def_kind(child) == DefKind::InlineConst
            // Scope widening (precise/parity lane ONLY): also admit CLOSURE
            // children. Capture-less closures pass mintable (empty
            // closure_min_captures); the parity gate never trusts the result, so
            // this only widens what the shadow-mint measures, never the trust lane.
            || (precise && tcx.def_kind(child) == DefKind::Closure);
        if !admissible {
            return None;
        }
        set.push(child);
    }
    Some(set)
}

/// As `local_id_is_in_root_body`, but accepts membership in ANY walked forest body
/// (they all share one HIR owner). A pick's `ItemLocalId` whose innermost
/// `associated_body` owner is one of `walked` is covered; otherwise (out of range,
/// no enclosing body, or a body NOT walked) it is not.
fn local_id_is_in_walked_bodies(
    tcx: TyCtxt<'_>,
    owner: rustc_hir::OwnerId,
    mut local_id: rustc_hir::ItemLocalId,
    walked: &[LocalDefId],
) -> bool {
    let nodes = &tcx.hir_owner_nodes(owner).nodes;
    loop {
        let Some(node) = nodes.get(local_id) else {
            return false;
        };
        if local_id == rustc_hir::ItemLocalId::ZERO {
            return false;
        }
        let parent_id = node.parent;
        let Some(parent) = nodes.get(parent_id) else {
            return false;
        };
        if let Some((body_owner, _)) = parent.node.associated_body() {
            return walked.contains(&body_owner);
        }
        local_id = parent_id;
    }
}

/// Coverage guard generalized to the walked forest: every method/operator pick
/// must be keyed inside a body the checker walks, else the root is rejected
/// (fail-safe MISS). Pairs with the checker's `rederived` covered-set gate.
pub fn picks_all_in_walked_bodies<'tcx>(
    tcx: TyCtxt<'tcx>,
    tr: &TypeckResults<'tcx>,
    walked: &[LocalDefId],
) -> bool {
    tr.type_dependent_defs()
        .items_in_stable_order()
        .into_iter()
        .all(|(local_id, _)| local_id_is_in_walked_bodies(tcx, tr.hir_owner, local_id, walked))
}

/// Encode + write the packed store for every minted root of an error-free
/// crate. Roots whose types fall outside the re-internable grammar are silently
/// skipped (they are simply not minted). Returns the number of witnesses
/// written, or `None` if the store could not be written.
pub fn commit<'tcx>(
    tcx: TyCtxt<'tcx>,
    dir: &Path,
    roots: &[LocalDefId],
    precise: bool,
) -> Option<usize> {
    let mut entries: BTreeMap<String, Vec<u8>> = BTreeMap::new();
    for &root in roots {
        // Forest-checking (increment 1): mint only roots whose whole typeck forest
        // is the root + value-inline-const children the replay checker will walk.
        // A coroutine child ⇒ skip (fail-safe; replay would reject anyway). Under
        // the precise/parity flag we ALSO admit closure children — capture-less
        // closures pass mintable, and the parity gate never trusts the result, so
        // this only widens what the shadow-mint measures (scope widening).
        let Some(walk) = forest_const_walk_set(tcx, root, precise) else {
            continue;
        };
        let tr = tcx.typeck(root);
        if !mintable(tr, precise) {
            continue;
        }
        // Coverage: don't mint a witness with a pick keyed outside the walked forest.
        if !picks_all_in_walked_bodies(tcx, tr, &walk) {
            continue;
        }
        // Mint under the effective key: the whole-SVH `witness_key` by default, or
        // the edit-loop `precise_witness_key` under the shadow-mint measurement flag.
        let Some(key) = (if precise {
            precise_witness_key(tcx, root, tr)
        } else {
            witness_key(tcx, root)
        }) else {
            continue;
        };
        let Some(bytes) = encode_root(tcx, tr) else { continue };
        entries.insert(key, bytes);
    }
    let n = entries.len();
    match store::write(dir, &store_stem(tcx), &entries) {
        Ok(()) => {
            tracing::debug!(dir = %dir.display(), witnesses = n, "trust-witness: crate store committed");
            Some(n)
        }
        Err(e) => {
            tracing::warn!(error = %e, "trust-witness: store write failed");
            None
        }
    }
}

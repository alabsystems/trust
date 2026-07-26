//! trust-mir-extract: Bridge from tRustc MIR to trust-types verification model
//!
//! Walks tRustc's Body<'tcx> and produces VerifiableFunction instances that
//! the downstream pipeline (trust_vcgen, trust-router) can operate on without
//! any rustc dependencies.
//!
//! Requires: #![feature(rustc_private)]
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// Trust: rustc_private + box_patterns needed when built standalone (cargo +nightly).
// When built as part of the compiler workspace (via x.py), the extern crates
// are resolved through Cargo.toml path dependencies.
#![feature(rustc_private)]
#![feature(register_tool)]
#![register_tool(trust)]
#![feature(box_patterns)]
// This rustc-private bridge intentionally uses compiler-internal features.
#![allow(internal_features)]
#![allow(unused_extern_crates)]
#![allow(unknown_lints)]
// Trust: 1.99 added the `rustc::symbol_intern_string_literal` internal lint
// (prefer pre-interned `sym::` over `Symbol::intern("...")`). Trust's #[cfg(test)]
// fixtures intern short ad-hoc predicate strings ("x > 0", ...) that have no
// pre-interned symbol; allow it crate-wide (only test code interns literals).
#![allow(rustc::symbol_intern_string_literal)]
#![allow(rustc::usage_of_ty_tykind)]
#![allow(rustc::usage_of_qualified_ty)]
#![allow(rustc::default_hash_types)]
// dead_code audit: crate-level suppression removed

extern crate rustc_abi;
extern crate rustc_ast_ir;
extern crate rustc_data_structures;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;

// Research-only MIR call-graph implementation. The production interprocedural
// pipeline uses the shared `trust-types`/`trust-vcgen` graph; this second graph
// has no non-test caller. Compile its tests without carrying a redundant graph
// implementation in every trustc build.
#[cfg(test)]
mod call_graph;
// Research-only feasibility transform for a synthetic, fuel-shaped Cell
// counter. It is deliberately excluded from production builds: the real
// compiler has neither a sound automatic cluster/reference discovery contract
// nor a u32-to-inductive-fuel refinement witness. Keeping this test-only makes
// the remaining production extraction gap explicit instead of advertising an
// unwired public API.
#[cfg(test)]
mod cell_threading;
pub mod contract_assumption_gate;
mod convert;
pub use convert::{
    collect_certified_paired_condvar_wait_calls, CertifiedPairedCondvarWaitCallSite,
};
pub use convert::func_operand_name;
pub use convert::is_derived_total_method;
pub use convert::is_total_derived_trait_call;
pub use convert::trust_try_total_marker;
// Research-only backward slicing for VC minimization. No production caller
// consumes the sliced body yet, so compiling this sizeable analysis into
// trustc only adds build time and an accidentally-advertised integration
// surface. Keep its adversarial unit tests without shipping unwired code.
#[cfg(test)]
mod slicing;
// verifier-perf: cheap fast-reject classifier so the verifier
// pass can skip lowering on functions it provably can't handle.
pub mod supportability;
// per-crate policy bucketing — decides whether the verifier
// should generate proof obligations on a function or boundary-extract
// only. Pairs with supportability::classify for the two-axis decision.
pub mod policy;
mod ty_convert;
mod verifier_api;

use rustc_hir::attrs::AttributeKind;
use rustc_hir::def::DefKind;
use rustc_middle::mir;
use rustc_middle::mir::trust_contract as rustc_trust_contract;
use rustc_middle::ty::print::{
    with_no_trimmed_paths, with_no_visible_paths, with_resolve_crate_name,
};
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use rustc_span::Symbol;
use rustc_span::def_id::{DefId, LOCAL_CRATE};
use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::*;
use std::sync::Arc;
#[allow(deprecated)]
pub use verifier_api::{
    TRUST_COMPILER_STABLE_CRATE_ID_METADATA_KEY, VerifierVcContentIdentity,
    contract_bundle_to_verifier_api, contract_bundle_to_verifier_api_with_compiler_identity,
    contract_bundle_to_verifier_api_with_crate_name, function_to_verifier_api_bundle,
    function_to_verifier_api_bundle_with_compiler_identity,
    function_to_verifier_api_bundle_with_crate_name,
    function_to_verifier_api_bundle_with_loop_feedback_candidates,
    function_to_verifier_api_bundle_with_loop_feedback_candidates_and_compiler_identity,
    function_to_verifier_api_bundle_with_loop_feedback_candidates_and_crate_name,
    verifier_api_emitted_vc_indices, verifier_source_digest, verifier_vc_content_identity,
    verifier_vc_content_identity_with_crate_name, verifier_vc_content_identity_with_source_digest,
    verifier_vc_content_identity_with_source_digest_and_crate_name,
};

/// Return a crate-qualified, definition-site path without triggering the
/// `trimmed_def_paths` query.
///
/// Trust uses this string as a semantic routing identity, so it must neither
/// omit the local crate nor select a context-dependent visible re-export.
pub fn safe_def_path_str(tcx: TyCtxt<'_>, def_id: DefId) -> String {
    with_resolve_crate_name!(with_no_visible_paths!(with_no_trimmed_paths!(
        tcx.def_path_str(def_id)
    )))
}

/// Like [`safe_def_path_str`] but renders the path with its CONCRETE
/// monomorphized generic arguments (`std::vec::Vec::<[u8; 1099511627776]>::with_capacity`
/// rather than the generic `Vec::<T>::with_capacity`). Used for bulk-allocation
/// sink callees so the element type — and hence `size_of::<T>()` — is recoverable
/// downstream for the capacity-overflow (`count * size_of::<T>() < isize::MAX`)
/// obligation, which the count-only path cannot establish for a multi-byte element
/// (SOUNDNESS, hunt-11: a `Vec::<[u8; 1<<40]>::with_capacity(n)` capacity overflow
/// was reported proved — and kernel-certified — because `T` was erased to the
/// generic param here).
pub fn safe_def_path_str_with_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: rustc_middle::ty::GenericArgsRef<'tcx>,
) -> String {
    with_resolve_crate_name!(with_no_visible_paths!(with_no_trimmed_paths!(
        tcx.def_path_str_with_args(def_id, args)
    )))
}

/// Return an identity-bearing concrete def-path for a monomorphized instance.
///
/// The ordinary rendered path is retained for the common unambiguous crate
/// graph. If two crate instances share a name, the path incorporates rustc's
/// stable crate and full generic-argument identities so display-text
/// collisions cannot merge distinct codegen instances.
pub fn exact_def_path_str_with_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: rustc_middle::ty::GenericArgsRef<'tcx>,
) -> String {
    let path = safe_def_path_str_with_args(tcx, def_id, args);
    convert::direct_call_def_path(tcx, def_id, args, path)
}

/// Opaque whole-crate authority for paired-condvar wait-site collection.
///
/// This value is constructor-free, non-serializable, and bound to one rustc
/// crate revision. The only minting API below owns the candidate discovery and
/// exhaustive MIR inventory; callers cannot supply functions, candidates, or a
/// raw struct/field map. Bridge consumers receive only opaque exact-site
/// capabilities derived from this token and the current post-transform body.
#[derive(Debug)]
pub struct PairedCondvarCrateCertificate {
    session_seal: Arc<()>,
    certificate_seal: Arc<()>,
    stable_crate_id: u64,
    pairs: FxHashMap<(u64, u64), Vec<(usize, usize)>>,
    // Audit evidence retained in the opaque token. These fields deliberately
    // have no getters: they bind the authority to the exact definitions and
    // extracted bodies inspected by the minting sweep, but are not a second
    // caller-populatable authority surface.
    _condvar_type_defs: FxHashSet<(u64, u64)>,
    _mutex_type_defs: FxHashSet<(u64, u64)>,
    _wait_callee_defs: FxHashSet<(u64, u64)>,
    _inspected_bodies: Vec<PairedCondvarInspectedBody>,
    _licensed_wait_sites: FxHashSet<PairedCondvarLicensedWaitSite>,
}

/// Production authority switch for the paired-condvar semantic lane.
///
/// Keep this false until a real compiler/TyCtxt fixture demonstrates a
/// non-empty certificate and exact-site bridge discharge, and the collector
/// authenticates `Condvar`, `Mutex`, and `Condvar::wait` as definitions from
/// the compiler's genuine sysroot `std` crate (crate identity, not merely a
/// non-local DefId plus rendered path). The synthetic recognizer and sealed-
/// capability tests remain useful while production minting stays dark.
pub const PAIRED_CONDVAR_AUTHORITY_AVAILABLE: bool = false;

/// Canonical digest used to bind an extractor-minted call-site capability to
/// the exact [`VerifiableBody`] later consumed by the bridge.
#[doc(hidden)]
pub fn paired_condvar_body_digest(body: &VerifiableBody) -> Option<String> {
    serde_json::to_vec(body).ok().map(|bytes| stable_sha256_hex(&bytes))
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct PairedCondvarInspectedBody {
    _owner: (u64, u64),
    _promoted: Option<usize>,
    _mir_digest: String,
}

/// One genuine std wait call observed by the no-caller-input pre-transform
/// crate inventory. Post-transform collection must match this complete record
/// in addition to revalidating the current MIR receiver shape. Keeping the
/// original body digest in the record makes its provenance back to the exact
/// inspected body explicit without pretending pre- and post-transform MIR are
/// byte-identical.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct PairedCondvarLicensedWaitSite {
    _owner: (u64, u64),
    _promoted: Option<usize>,
    _block: usize,
    _callee_def: (u64, u64),
    _callee: String,
    _source_span: SourceSpan,
    _receiver_place: String,
    _guard_place: String,
    _inspected_mir_digest: String,
}

impl PairedCondvarLicensedWaitSite {
    fn matches_current_identity(
        &self,
        owner: (u64, u64),
        promoted: Option<usize>,
        block: usize,
        callee_def: (u64, u64),
        callee: &str,
        source_span: &SourceSpan,
        receiver_place: &str,
        guard_place: &str,
    ) -> bool {
        self._owner == owner
            && self._promoted == promoted
            && self._block == block
            && self._callee_def == callee_def
            && self._callee == callee
            && self._source_span == *source_span
            && self._receiver_place == receiver_place
            && self._guard_place == guard_place
    }
}

/// Generic MIR definitions are not an exhaustive inventory of the concrete
/// instances that codegen may create. Until this lane owns that instance set,
/// one generic local body darkens the whole optional certificate.
fn paired_condvar_generic_body_keeps_lane_dark(generic_parameter_count: usize) -> bool {
    generic_parameter_count != 0
}

#[derive(Default)]
struct PairedCondvarSessionSeal(Option<Arc<()>>);

fn paired_condvar_session_seal(tcx: TyCtxt<'_>) -> Arc<()> {
    tcx.sess.with_trust_compiler_state::<PairedCondvarSessionSeal, _>(|state| {
        Arc::clone(state.0.get_or_insert_with(|| Arc::new(())))
    })
}

fn paired_def_key(tcx: TyCtxt<'_>, def_id: DefId) -> (u64, u64) {
    let hash = tcx.def_path_hash(def_id);
    (hash.stable_crate_id().as_u64(), hash.local_hash().as_u64())
}

fn local_item_has_direct_trust_attr(tcx: TyCtxt<'_>, def_id: DefId, name: &str) -> bool {
    #[allow(deprecated)]
    tcx.get_all_attrs(def_id).iter().any(|attr| {
        matches!(
            attr.path().as_slice(),
            [tool, attr_name] if tool.as_str() == "trust" && attr_name.as_str() == name
        )
    })
}

fn empty_paired_condvar_crate_certificate(tcx: TyCtxt<'_>) -> PairedCondvarCrateCertificate {
    PairedCondvarCrateCertificate {
        session_seal: paired_condvar_session_seal(tcx),
        certificate_seal: Arc::new(()),
        stable_crate_id: tcx.stable_crate_id(LOCAL_CRATE).as_u64(),
        pairs: FxHashMap::default(),
        _condvar_type_defs: FxHashSet::default(),
        _mutex_type_defs: FxHashSet::default(),
        _wait_callee_defs: FxHashSet::default(),
        _inspected_bodies: Vec::new(),
        _licensed_wait_sites: FxHashSet::default(),
    }
}

/// Record one exact body and every genuine `std::sync::Condvar::wait` site it
/// contains. Any genuine wait that cannot be mapped one-to-one into the freshly
/// extracted body invalidates the entire crate certificate. Local lookalikes
/// are intentionally ignored: DefId identity, not rendered source text, decides
/// whether a call is licensable.
fn record_paired_body_inventory<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    function: &VerifiableFunction,
    promoted: Option<usize>,
    certificate: &mut PairedCondvarCrateCertificate,
) -> bool {
    let Some(mir_digest) = paired_condvar_body_digest(&function.body) else {
        return false;
    };
    let owner = body.source.def_id();
    let owner_key = paired_def_key(tcx, owner);
    if function.def_path != safe_def_path_str(tcx, owner) {
        return false;
    }

    let mut wait_defs = FxHashSet::default();
    let mut licensed_sites = Vec::new();
    for (bb, block) in body.basic_blocks.iter_enumerated() {
        let mir::TerminatorKind::Call { func, .. } = &block.terminator().kind else {
            continue;
        };
        let mir::Operand::Constant(box constant) = func else { continue };
        let rustc_middle::ty::TyKind::FnDef(def_id, _) = constant.const_.ty().kind() else {
            continue;
        };
        if !def_id.is_local() && safe_def_path_str(tcx, *def_id) == "std::sync::Condvar::wait" {
            let mir::TerminatorKind::Call { args, .. } = &block.terminator().kind else {
                return false;
            };
            if args.len() != 2 {
                return false;
            }
            let callee = func_operand_name(tcx, func);
            let mut lowered_blocks =
                function.body.blocks.iter().filter(|b| b.id.0 == bb.as_usize());
            let Some(lowered_block) = lowered_blocks.next() else {
                return false;
            };
            if lowered_blocks.next().is_some() {
                return false;
            }
            let Terminator::Call { func: lowered, span, .. } = &lowered_block.terminator else {
                return false;
            };
            if *lowered != callee {
                return false;
            }
            let callee_def = paired_def_key(tcx, *def_id);
            wait_defs.insert(callee_def);
            licensed_sites.push(PairedCondvarLicensedWaitSite {
                _owner: owner_key,
                _promoted: promoted,
                _block: bb.as_usize(),
                _callee_def: callee_def,
                _callee: callee,
                _source_span: span.clone(),
                _receiver_place: format!("{:?}", args[0].node),
                _guard_place: format!("{:?}", args[1].node),
                _inspected_mir_digest: mir_digest.clone(),
            });
        }
    }

    let inspected = PairedCondvarInspectedBody {
        _owner: owner_key,
        _promoted: promoted,
        _mir_digest: mir_digest,
    };
    if certificate
        ._inspected_bodies
        .iter()
        .any(|existing| existing._owner == owner_key && existing._promoted == promoted)
    {
        return false;
    }
    if licensed_sites.iter().any(|site| certificate._licensed_wait_sites.contains(site)) {
        return false;
    }
    certificate._wait_callee_defs.extend(wait_defs);
    certificate._licensed_wait_sites.extend(licensed_sites);
    certificate._inspected_bodies.push(inspected);
    true
}

/// Mint the paired-condvar authority for exactly this rustc crate revision.
///
/// The function accepts no caller-provided bodies, candidates, or certificate
/// map. It inventories every local MIR key and promoted body itself and returns
/// an empty (non-authorizing) token on every stolen body, unclassified def kind,
/// const-context gap, std/core/alloc impersonation, unsupported extracted MIR,
/// or semantic certification failure.
#[must_use]
#[allow(rustc::untracked_query_information, rustc::potential_query_instability)]
pub fn certify_paired_condvars_for_crate(tcx: TyCtxt<'_>) -> PairedCondvarCrateCertificate {
    let mut certificate = empty_paired_condvar_crate_certificate(tcx);
    if !PAIRED_CONDVAR_AUTHORITY_AVAILABLE {
        return certificate;
    }
    let mut candidates = Vec::new();
    let mut candidate_keys = FxHashMap::default();
    for item in tcx.hir_crate_items(()).free_items() {
        let did = item.owner_id.to_def_id();
        if !matches!(tcx.def_kind(did), DefKind::Struct)
            || !local_item_has_direct_trust_attr(tcx, did, "paired")
        {
            continue;
        }
        let adt = tcx.adt_def(did);
        if !adt.is_struct() {
            continue;
        }
        let variant = adt.non_enum_variant();
        if variant.ctor.is_some() {
            continue;
        }
        let args = ty::GenericArgs::identity_for_item(tcx, did);
        let mut condvar_fields = Vec::new();
        let mut mutex_fields = Vec::new();
        let mut public_condvar = false;
        for (idx, field) in variant.fields.iter_enumerated() {
            let field_ty = field.ty(tcx, args).skip_normalization();
            let ty::Adt(field_adt, _) = field_ty.kind() else { continue };
            if field_adt.did().is_local() {
                continue;
            }
            match safe_def_path_str(tcx, field_adt.did()).as_str() {
                "std::sync::Condvar" => {
                    certificate._condvar_type_defs.insert(paired_def_key(tcx, field_adt.did()));
                    if field.vis.is_public() {
                        public_condvar = true;
                    } else {
                        condvar_fields.push(idx.as_usize());
                    }
                }
                "std::sync::Mutex" if !field.vis.is_public() => {
                    certificate._mutex_type_defs.insert(paired_def_key(tcx, field_adt.did()));
                    mutex_fields.push(idx.as_usize());
                }
                _ => {}
            }
        }
        if !public_condvar && !condvar_fields.is_empty() && !mutex_fields.is_empty() {
            let struct_name = safe_def_path_str(tcx, did);
            candidate_keys.insert(struct_name.clone(), paired_def_key(tcx, did));
            candidates.push(trust_vcgen::PairedCondvarCandidate {
                struct_name,
                condvar_fields,
                mutex_fields,
                field_count: variant.fields.len(),
            });
        }
    }
    if candidates.is_empty() {
        return certificate;
    }

    for def_id in tcx.hir_crate_items(()).definitions() {
        let path = safe_def_path_str(tcx, def_id.to_def_id());
        if path.starts_with("std::") || path.starts_with("core::") || path.starts_with("alloc::") {
            certificate.pairs.clear();
            return certificate;
        }
    }

    let mut functions = Vec::new();
    for &local_def_id in tcx.mir_keys(()) {
        let def_id = local_def_id.to_def_id();
        // Generic MIR definitions are not a monomorphized-instance inventory.
        // Check every MIR key before any def-kind/trivial-const fast path so a
        // generic closure, constructor, or otherwise-skipped const cannot evade
        // the whole-lane-dark rule.
        if paired_condvar_generic_body_keeps_lane_dark(tcx.generics_of(def_id).count()) {
            certificate.pairs.clear();
            return certificate;
        }
        let body = match tcx.def_kind(def_id) {
            DefKind::Ctor(..) => continue,
            DefKind::Fn | DefKind::AssocFn | DefKind::Closure => {
                match tcx.hir_body_const_context(local_def_id) {
                    None | Some(rustc_hir::ConstContext::ConstFn) => {
                        let steal = tcx.mir_drops_elaborated_and_const_checked(local_def_id);
                        if steal.is_stolen() {
                            certificate.pairs.clear();
                            return certificate;
                        }
                        let borrowed = steal.borrow();
                        let function = extract_function_with_contract_bundle(tcx, &borrowed, None);
                        if !record_paired_body_inventory(
                            tcx,
                            &borrowed,
                            &function,
                            None,
                            &mut certificate,
                        ) {
                            certificate.pairs.clear();
                            return certificate;
                        }
                        functions.push(function);
                        None
                    }
                    Some(_) => {
                        certificate.pairs.clear();
                        return certificate;
                    }
                }
            }
            DefKind::Const { .. }
            | DefKind::AssocConst { .. }
            | DefKind::AnonConst
            | DefKind::InlineConst
            | DefKind::Static { .. } => {
                if tcx.is_trivial_const(local_def_id) {
                    continue;
                }
                Some(tcx.mir_for_ctfe(local_def_id))
            }
            _ => {
                certificate.pairs.clear();
                return certificate;
            }
        };
        if let Some(body) = body {
            let function = extract_function_with_contract_bundle(tcx, body, None);
            if !record_paired_body_inventory(tcx, body, &function, None, &mut certificate) {
                certificate.pairs.clear();
                return certificate;
            }
            functions.push(function);
        }
        for (promoted_index, promoted) in tcx.promoted_mir(def_id).iter().enumerate() {
            let function = extract_function_with_contract_bundle(tcx, promoted, None);
            if !record_paired_body_inventory(
                tcx,
                promoted,
                &function,
                Some(promoted_index),
                &mut certificate,
            ) {
                certificate.pairs.clear();
                return certificate;
            }
            functions.push(function);
        }
    }

    for pair in trust_vcgen::certify_paired_condvars(&functions, &candidates) {
        let Some(&struct_key) = candidate_keys.get(&pair.struct_name) else {
            certificate.pairs.clear();
            return certificate;
        };
        certificate
            .pairs
            .entry(struct_key)
            .or_default()
            .push((pair.condvar_field, pair.mutex_field));
    }
    certificate
}

#[cfg(test)]
mod paired_condvar_authority_tests {
    use super::*;

    fn licensed_site() -> PairedCondvarLicensedWaitSite {
        PairedCondvarLicensedWaitSite {
            _owner: (1, 2),
            _promoted: None,
            _block: 3,
            _callee_def: (4, 5),
            _callee: "std::sync::Condvar::wait::<u64>".into(),
            _source_span: SourceSpan {
                file: "paired.rs".into(),
                line_start: 10,
                col_start: 2,
                line_end: 10,
                col_end: 24,
            },
            _receiver_place: "move _7".into(),
            _guard_place: "move _8".into(),
            _inspected_mir_digest: "pre-transform-body-digest".into(),
        }
    }

    #[test]
    fn generic_body_keeps_whole_paired_condvar_lane_dark() {
        assert!(!paired_condvar_generic_body_keeps_lane_dark(0));
        assert!(paired_condvar_generic_body_keeps_lane_dark(1));
        assert!(paired_condvar_generic_body_keeps_lane_dark(usize::MAX));
    }

    #[test]
    fn paired_condvar_production_authority_stays_dark_pending_real_tycx_positive() {
        assert!(!PAIRED_CONDVAR_AUTHORITY_AVAILABLE);
    }

    #[test]
    fn stale_or_mutated_wait_site_never_matches_the_license() {
        let site = licensed_site();
        let exact = |block, callee: &str, span: &SourceSpan, receiver: &str, guard: &str| {
            site.matches_current_identity(
                (1, 2),
                None,
                block,
                (4, 5),
                callee,
                span,
                receiver,
                guard,
            )
        };
        assert!(exact(
            3,
            "std::sync::Condvar::wait::<u64>",
            &site._source_span,
            "move _7",
            "move _8",
        ));
        assert!(!exact(
            4,
            "std::sync::Condvar::wait::<u64>",
            &site._source_span,
            "move _7",
            "move _8",
        ));
        assert!(!exact(
            3,
            "std::sync::Condvar::wait::<u32>",
            &site._source_span,
            "move _7",
            "move _8",
        ));
        let mut moved_span = site._source_span.clone();
        moved_span.line_start += 1;
        assert!(!exact(3, "std::sync::Condvar::wait::<u64>", &moved_span, "move _7", "move _8",));
        assert!(!exact(
            3,
            "std::sync::Condvar::wait::<u64>",
            &site._source_span,
            "move _70",
            "move _8",
        ));
        assert!(!exact(
            3,
            "std::sync::Condvar::wait::<u64>",
            &site._source_span,
            "move _7",
            "move _80",
        ));
        assert!(!site.matches_current_identity(
            (9, 9),
            None,
            3,
            (4, 5),
            "std::sync::Condvar::wait::<u64>",
            &site._source_span,
            "move _7",
            "move _8",
        ));
        assert!(!site.matches_current_identity(
            (1, 2),
            Some(0),
            3,
            (4, 5),
            "std::sync::Condvar::wait::<u64>",
            &site._source_span,
            "move _7",
            "move _8",
        ));
        assert!(!site.matches_current_identity(
            (1, 2),
            None,
            3,
            (9, 9),
            "std::sync::Condvar::wait::<u64>",
            &site._source_span,
            "move _7",
            "move _8",
        ));
    }
}

/// Error returned when a compiler-native Trust contract bundle cannot be
/// converted into the rustc-independent `trust-types` model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TrustContractBundleConversionError {
    /// The bundle summary claims contracts exist, but the dense contract list
    /// is empty. Treat this as unavailable data rather than a successful empty
    /// extraction.
    NonConvertibleNonEmptyBundle { summary_total: u32 },
    /// The query summary and the actual function-plus-loop storage disagree.
    /// Treat the bundle as corrupt rather than trusting either partial view.
    SummaryCardinalityMismatch { summary_total: u32, actual_total: usize },
    /// The compiler contract kind has no equivalent in `trust-types::Contract`.
    UnsupportedContractKind { index: usize, kind: String },
    /// The compiler contract is anchored somewhere the current target model
    /// cannot represent without losing information.
    UnsupportedSubject { index: usize, subject: String },
    /// The compiler predicate is explicitly marked unsupported.
    UnsupportedPredicate { index: usize, reason: String },
    /// The predicate points at a MIR local value that has not been lowered to a
    /// stable textual or structured contract expression yet.
    MirLocalPredicate { index: usize, local: usize },
}

pub(crate) const UNSUPPORTED_COMPILER_CONTRACT_PREFIX: &str =
    "__trust_unsupported_compiler_contract__:";
pub(crate) const LOWERED_COMPILER_CONTRACT_PREFIX: &str = "__trust_lowered_compiler_contract__:";

impl std::fmt::Display for TrustContractBundleConversionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NonConvertibleNonEmptyBundle { summary_total } => write!(
                f,
                "Trust contract bundle summary reports {summary_total} contracts but no convertible contract entries are present"
            ),
            Self::SummaryCardinalityMismatch { summary_total, actual_total } => write!(
                f,
                "Trust contract bundle summary reports {summary_total} contracts but contains {actual_total} function and loop contract entries"
            ),
            Self::UnsupportedContractKind { index, kind } => {
                write!(f, "Trust contract #{index} has unsupported kind {kind}")
            }
            Self::UnsupportedSubject { index, subject } => {
                write!(f, "Trust contract #{index} has unsupported subject {subject}")
            }
            Self::UnsupportedPredicate { index, reason } => {
                write!(f, "Trust contract #{index} has unsupported predicate: {reason}")
            }
            Self::MirLocalPredicate { index, local } => {
                write!(f, "Trust contract #{index} uses non-convertible MIR local _{local}")
            }
        }
    }
}

impl std::error::Error for TrustContractBundleConversionError {}

/// A MIR construct that the verification-oriented TrustIr can abstract, but
/// the executable trust-cg path cannot reproduce byte-for-byte.
///
/// Codegen must never continue past this error: doing so would verify one
/// abstract program and emit another executable program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CodegenExtractionError {
    /// Extraction changed executable control flow (for example, rewriting
    /// `std::process::exit` into an ordinary Rust return).
    SemanticAbstraction { def_path: String, block: usize, detail: String },
    /// TrustIr contains a sentinel, placeholder, or layout-erased construct
    /// whose runtime meaning is not fully represented.
    UnsupportedMir { def_path: String, location: String, detail: String },
    /// Extraction changed the body topology, so MIR and TrustIr can no longer
    /// be related block-for-block.
    StructuralMismatch { def_path: String, detail: String },
}

impl std::fmt::Display for CodegenExtractionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SemanticAbstraction { def_path, block, detail } => {
                write!(
                    f,
                    "codegen-faithful extraction of `{def_path}` failed at bb{block}: {detail}"
                )
            }
            Self::UnsupportedMir { def_path, location, detail } => {
                write!(
                    f,
                    "codegen-faithful extraction of `{def_path}` failed at {location}: {detail}"
                )
            }
            Self::StructuralMismatch { def_path, detail } => {
                write!(
                    f,
                    "codegen-faithful extraction of `{def_path}` changed MIR structure: {detail}"
                )
            }
        }
    }
}

impl std::error::Error for CodegenExtractionError {}

/// Convert a compiler-native Trust contract bundle into the rustc-independent
/// `trust-types` bundle consumed by MIR extraction.
///
/// This conversion is intentionally fail-closed. Whole-function
/// `Requires`/`Ensures`/`Decreases` clauses retain their dense compiler index,
/// while E4/E5 loop clauses are carried in the parallel `loop_contracts` lane
/// with their loop-head spans. Predicates may be opaque text, boolean literals,
/// or explicit unsupported payloads; unsupported predicates are preserved so
/// VC generation creates a visible per-clause Unknown instead of dropping
/// authored semantics.
pub fn convert_trust_contract_bundle<'tcx>(
    tcx: TyCtxt<'tcx>,
    bundle: &rustc_trust_contract::TrustContractBundle<'tcx>,
) -> Result<CompilerContractBundle, TrustContractBundleConversionError> {
    if bundle.is_empty() {
        return if bundle.summary.total == 0 {
            Ok(CompilerContractBundle::default())
        } else {
            Err(TrustContractBundleConversionError::NonConvertibleNonEmptyBundle {
                summary_total: bundle.summary.total,
            })
        };
    }

    let actual_total = bundle.len();
    if bundle.summary.total as usize != actual_total {
        return Err(TrustContractBundleConversionError::SummaryCardinalityMismatch {
            summary_total: bundle.summary.total,
            actual_total,
        });
    }

    let mut contracts = Vec::with_capacity(bundle.contracts.len());
    let mut typed_propositions = Vec::new();
    // Preserve `TrustContractId` order exactly. Downstream native TrustIr lowering
    // reconstructs stable source/assertion ids from this dense contract index.
    for (id, contract) in bundle.contracts.iter_enumerated() {
        let index = id.as_usize();
        let kind = convert_trust_contract_kind(index, contract.kind)?;
        convert_trust_contract_subject(index, contract.subject)?;
        let (body, proposition) =
            convert_trust_contract_predicate(index, &contract.predicate.kind)?;
        if let Some((formula, variable_domains)) = proposition {
            typed_propositions.push(trust_types::CompilerContractProposition {
                source_contract_index: index,
                kind,
                body: body.clone(),
                formula,
                variable_domains,
            });
        }
        contracts.push(Contract { kind, span: convert::convert_span(tcx, contract.span), body });
    }

    let mut loop_contracts = Vec::with_capacity(bundle.loop_contracts.len());
    for (index, contract) in bundle.loop_contracts.iter().enumerate() {
        let kind = match contract.kind {
            rustc_trust_contract::TrustContractKind::LoopInvariant => {
                trust_types::LoopContractKind::Invariant
            }
            rustc_trust_contract::TrustContractKind::Decreases => {
                trust_types::LoopContractKind::Decreases
            }
            kind => {
                return Err(TrustContractBundleConversionError::UnsupportedContractKind {
                    index,
                    kind: format!("{kind:?}"),
                });
            }
        };
        let rustc_trust_contract::TrustContractSubject::HirLoop { id, loop_span, header_span } =
            contract.subject
        else {
            return Err(TrustContractBundleConversionError::UnsupportedSubject {
                index,
                subject: format!("{:?}", contract.subject),
            });
        };
        let (body, _) = convert_trust_contract_predicate(index, &contract.predicate.kind)?;
        loop_contracts.push(trust_types::LoopContractSpec {
            kind,
            source_loop_id: id.index,
            loop_head: convert::convert_span(tcx, loop_span),
            header_span: convert::convert_span(tcx, header_span),
            span: convert::convert_span(tcx, contract.span),
            body,
        });
    }

    Ok(CompilerContractBundle::new(contracts)
        .with_typed_propositions(typed_propositions)
        .with_loop_contracts(loop_contracts))
}

fn convert_trust_contract_kind(
    index: usize,
    kind: rustc_trust_contract::TrustContractKind,
) -> Result<ContractKind, TrustContractBundleConversionError> {
    match kind {
        rustc_trust_contract::TrustContractKind::Requires => Ok(ContractKind::Requires),
        rustc_trust_contract::TrustContractKind::Ensures => Ok(ContractKind::Ensures),
        rustc_trust_contract::TrustContractKind::Decreases => Ok(ContractKind::Decreases),
        _ => Err(TrustContractBundleConversionError::UnsupportedContractKind {
            index,
            kind: format!("{kind:?}"),
        }),
    }
}

fn convert_trust_contract_subject(
    index: usize,
    subject: rustc_trust_contract::TrustContractSubject,
) -> Result<(), TrustContractBundleConversionError> {
    match subject {
        rustc_trust_contract::TrustContractSubject::Function => Ok(()),
        _ => Err(TrustContractBundleConversionError::UnsupportedSubject {
            index,
            subject: format!("{subject:?}"),
        }),
    }
}

fn convert_trust_contract_predicate(
    index: usize,
    predicate: &rustc_trust_contract::TrustContractPredicateKind,
) -> Result<
    (String, Option<(Formula, Vec<trust_types::CompilerContractVariableDomain>)>),
    TrustContractBundleConversionError,
> {
    match predicate {
        rustc_trust_contract::TrustContractPredicateKind::Typed { text, proposition } => {
            let body = text.to_string();
            let (formula, variable_domains) = trust_contract_proposition_to_formula_and_domains(
                proposition,
            )
            .map_err(|reason| {
                TrustContractBundleConversionError::UnsupportedPredicate { index, reason }
            })?;
            let Some(source) = body.strip_prefix(LOWERED_COMPILER_CONTRACT_PREFIX) else {
                return Err(TrustContractBundleConversionError::UnsupportedPredicate {
                    index,
                    reason: "typed compiler proposition is missing its canonical lowering prefix"
                        .to_string(),
                });
            };
            let round_trip = trust_types::parse_spec_expr(source).and_then(|parsed| {
                trust_types::compiler_contract_formula_with_domains(&parsed, &variable_domains)
            });
            if round_trip.as_ref() != Some(&formula) {
                return Err(TrustContractBundleConversionError::UnsupportedPredicate {
                    index,
                    reason: "typed compiler proposition does not structurally match its canonical source spelling"
                        .to_string(),
                });
            }
            Ok((body, Some((formula, variable_domains))))
        }
        rustc_trust_contract::TrustContractPredicateKind::Opaque { text } => {
            Ok((text.to_string(), None))
        }
        rustc_trust_contract::TrustContractPredicateKind::BoolLiteral { value } => Ok((
            format!("{LOWERED_COMPILER_CONTRACT_PREFIX}{value}"),
            Some((Formula::Bool(*value), Vec::new())),
        )),
        rustc_trust_contract::TrustContractPredicateKind::MirLocal { local } => {
            Err(TrustContractBundleConversionError::MirLocalPredicate {
                index,
                local: local.as_usize(),
            })
        }
        rustc_trust_contract::TrustContractPredicateKind::Unsupported { reason } => {
            Ok((format!("{UNSUPPORTED_COMPILER_CONTRACT_PREFIX}{}", reason), None))
        }
    }
}

/// Lossless conversion from the compiler-query proposition into the static
/// verifier formula. No source text is parsed here.
pub fn trust_contract_proposition_to_formula(
    proposition: &rustc_trust_contract::TrustContractProposition,
) -> Formula {
    use rustc_trust_contract::TrustContractProposition as Proposition;
    use rustc_trust_contract::TrustContractPropositionDomain as Domain;

    let boxed =
        |proposition: &Proposition| Box::new(trust_contract_proposition_to_formula(proposition));
    match proposition {
        Proposition::Bool(value) => Formula::Bool(*value),
        Proposition::Int(value) => Formula::Int(*value),
        Proposition::UInt(value) => Formula::UInt(*value),
        Proposition::Var { name, domain } => Formula::Var(
            name.to_string(),
            if *domain == Domain::Bool { Sort::Bool } else { Sort::Int },
        ),
        Proposition::Not(inner) => Formula::Not(boxed(inner)),
        Proposition::And(terms) => {
            Formula::And(terms.iter().map(trust_contract_proposition_to_formula).collect())
        }
        Proposition::Or(terms) => {
            Formula::Or(terms.iter().map(trust_contract_proposition_to_formula).collect())
        }
        Proposition::Implies(lhs, rhs) => Formula::Implies(boxed(lhs), boxed(rhs)),
        Proposition::Eq(lhs, rhs) => Formula::Eq(boxed(lhs), boxed(rhs)),
        Proposition::Lt(lhs, rhs) => Formula::Lt(boxed(lhs), boxed(rhs)),
        Proposition::Le(lhs, rhs) => Formula::Le(boxed(lhs), boxed(rhs)),
        Proposition::Gt(lhs, rhs) => Formula::Gt(boxed(lhs), boxed(rhs)),
        Proposition::Ge(lhs, rhs) => Formula::Ge(boxed(lhs), boxed(rhs)),
        Proposition::Add(lhs, rhs) => Formula::Add(boxed(lhs), boxed(rhs)),
        Proposition::Sub(lhs, rhs) => Formula::Sub(boxed(lhs), boxed(rhs)),
        Proposition::Mul(lhs, rhs) => Formula::Mul(boxed(lhs), boxed(rhs)),
        Proposition::Div(lhs, rhs) => Formula::Div(boxed(lhs), boxed(rhs)),
        Proposition::Rem(lhs, rhs) => Formula::Rem(boxed(lhs), boxed(rhs)),
        Proposition::Neg(inner) => Formula::Neg(boxed(inner)),
    }
}

/// Convert the query tree while retaining its exact source-domain identity.
/// Conflicting domains for the same canonical variable are rejected instead
/// of choosing an arbitrary occurrence.
pub fn trust_contract_proposition_to_formula_and_domains(
    proposition: &rustc_trust_contract::TrustContractProposition,
) -> Result<(Formula, Vec<trust_types::CompilerContractVariableDomain>), String> {
    use rustc_trust_contract::TrustContractProposition as Proposition;
    use rustc_trust_contract::TrustContractPropositionDomain as Domain;
    use trust_types::{CompilerContractValueDomain as ValueDomain, CompilerContractVariableDomain};

    fn collect(
        proposition: &Proposition,
        domains: &mut std::collections::BTreeMap<String, ValueDomain>,
    ) -> Result<(), String> {
        match proposition {
            Proposition::Var { name, domain } => {
                let domain = match domain {
                    Domain::Bool => ValueDomain::Bool,
                    Domain::MathematicalInt => ValueDomain::MathematicalInt,
                    Domain::PointerSizedInt { width, signed } => {
                        ValueDomain::PointerSizedInt { width: *width, signed: *signed }
                    }
                    Domain::MachineInt { width, signed } => {
                        ValueDomain::MachineInt { width: *width, signed: *signed }
                    }
                };
                let name = name.to_string();
                if let Some(previous) = domains.insert(name.clone(), domain) {
                    if previous != domain {
                        return Err(format!(
                            "typed compiler proposition gives `{name}` conflicting domains {previous:?} and {domain:?}"
                        ));
                    }
                }
            }
            Proposition::Not(inner) | Proposition::Neg(inner) => collect(inner, domains)?,
            Proposition::And(terms) | Proposition::Or(terms) => {
                for term in terms {
                    collect(term, domains)?;
                }
            }
            Proposition::Implies(lhs, rhs)
            | Proposition::Eq(lhs, rhs)
            | Proposition::Lt(lhs, rhs)
            | Proposition::Le(lhs, rhs)
            | Proposition::Gt(lhs, rhs)
            | Proposition::Ge(lhs, rhs)
            | Proposition::Add(lhs, rhs)
            | Proposition::Sub(lhs, rhs)
            | Proposition::Mul(lhs, rhs)
            | Proposition::Div(lhs, rhs)
            | Proposition::Rem(lhs, rhs) => {
                collect(lhs, domains)?;
                collect(rhs, domains)?;
            }
            Proposition::Bool(_) | Proposition::Int(_) | Proposition::UInt(_) => {}
        }
        Ok(())
    }

    let formula = trust_contract_proposition_to_formula(proposition);
    let mut domains = std::collections::BTreeMap::new();
    collect(proposition, &mut domains)?;
    let variable_domains = domains
        .into_iter()
        .map(|(name, domain)| CompilerContractVariableDomain { name, domain })
        .collect::<Vec<_>>();
    if trust_types::compiler_contract_formula_with_domains(&formula, &variable_domains).as_ref()
        != Some(&formula)
    {
        return Err(
            "typed compiler proposition has an incomplete or non-canonical domain map".to_string()
        );
    }
    Ok((formula, variable_domains))
}

/// Extract a VerifiableFunction from a rustc MIR Body.
///
/// This is the main entry point. Called once per function in the crate.
/// The default native path fails closed when compiler-owned contract facts are
/// unavailable: it will not scrape Rust source files to reconstruct contracts.
/// Trust (v25 B1): FAITHFUL-SCALAR extraction — identical to
/// [`extract_function`] except isize/usize/char keep their identity
/// (`TrustTy::PtrSizedInt`/`TrustTy::Char`) instead of the legacy width
/// collapse. This is the trust-ir DIFFERENTIAL's lane (the bridge maps the
/// faithful spellings onto `trust_ir::Ty::Isize/Usize/Char` so producer and
/// oracle signatures agree by leaf equality). The verifier pipeline stays on
/// the legacy entry until its own migration wave.
pub fn extract_function_faithful<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
) -> VerifiableFunction {
    let _guard = crate::ty_convert::FaithfulScalarsGuard::enable();
    extract_function(tcx, body)
}

pub fn extract_function<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> VerifiableFunction {
    extract_function_with_contract_bundle(tcx, body, None)
}

/// Extract executable MIR for the trust-cg backend without verifier-only
/// abstractions.
///
/// Unlike [`extract_function`], this API is a checked, fallible seam. It keeps
/// real derived bodies, requires one-to-one executable control flow, and
/// recursively rejects every TrustIr placeholder before any object emission.
pub fn extract_function_for_codegen<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
) -> Result<VerifiableFunction, CodegenExtractionError> {
    let mut function = extract_function_with_purpose(tcx, body, None, ExtractionPurpose::Codegen);
    validate_codegen_fidelity(tcx, body, &mut function)?;
    Ok(function)
}

/// Extract a VerifiableFunction using an optional typed compiler contract bundle.
///
/// Passing `None` preserves the native fail-closed behavior: only compiler/HIR
/// facts are considered; the legacy source scraper is deleted, so there is no
/// text-recovery fallback of any kind.
pub fn extract_function_with_contract_bundle<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    compiler_contracts: Option<&CompilerContractBundle>,
) -> VerifiableFunction {
    extract_function_with_purpose(tcx, body, compiler_contracts, ExtractionPurpose::Verification)
}

fn extract_function_with_purpose<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    compiler_contracts: Option<&CompilerContractBundle>,
    purpose: ExtractionPurpose,
) -> VerifiableFunction {
    let def_id = body.source.def_id();
    let def_path = safe_def_path_str(tcx, def_id);
    let metadata = extract_metadata_with_contract_bundle(tcx, body, compiler_contracts);
    // Trust: Use opt_item_name to avoid panic on closures/synthetic items
    // (e.g. `fmt::builders::{closure#0}`). Fall back to last segment of def_path.
    let name = tcx
        .opt_item_name(def_id)
        .map(|s| s.to_string())
        .unwrap_or_else(|| def_path.rsplit("::").next().unwrap_or(&def_path).to_string());

    // Parse contract bodies into formulas for direct consumption.
    let (mut preconditions, mut postconditions) =
        parse_contract_specs_with_typed(&metadata.contracts, compiler_contracts);

    // Build structured FunctionSpec from contracts.
    let spec = metadata.spec.clone();

    // Build both views of MIR debug names before extraction, then extend them
    // from one shared, HIR-owned parameter recovery.  The extracted local names
    // and the raw assumption-gate multimap must never disagree about a recovered
    // parameter: doing the two recoveries independently lets one side accept a
    // spelling that the other side rejected as ambiguous.
    let mut debug_local_names = build_debug_name_map(body);
    let mut debug_name_locals = build_debug_name_multimap(body);
    recover_direct_parameter_names(tcx, body, &mut debug_local_names, &mut debug_name_locals);

    let verifiable_body = extract_body(tcx, body, purpose, &debug_local_names);

    // Derived bodies stay intact. An attribute/trait name cannot authorize a
    // synthetic zero-obligation replacement: Hash and Debug execute caller-
    // supplied hasher/writer behavior, and `automatically_derived` is itself
    // source-spellable.

    // The text parser gives ordinary identifiers `Sort::Int`. Restore the
    // source signature's Boolean parameter/return sorts before either body
    // assumptions or modular summaries consume the formulas. This makes
    // `requires(flag)` / `requires(flag == true)` bind the actual Bool local
    // instead of becoming an ungroundable integer atom.
    retype_contract_formulas_for_body(&mut preconditions, &mut postconditions, &verifiable_body);

    // Soundness gate: contract preconditions become BODY hypotheses
    // (`conjoin_live_preconditions`), which is only sound if they bind genuine
    // entry parameters. Shadowed debug names provably transferred a param bound
    // to an unconstrained body local (false PROVE); unsatisfiable predicates
    // would verify vacuously. Gate failure drops the assumption — never the
    // function. Call-site Precondition VCs are generated elsewhere and stay
    // ungated (callers must prove the full predicate).
    // Trust (#14): at low `-Cdebuginfo` the verification body's `var_debug_info`
    // is EMPTY (probe-confirmed: `param_locals=[(1, None)]`,
    // `debug_name_locals={}`), so the NATIVE (span-only, verifier-language)
    // first-class clause lane — `fn f(..) requires x < 10` — cannot bind its
    // parameter through debug names and `gate_contract_preconditions` drops the
    // assumption. Recover the parameter names from the HIR body's exact vector
    // of plain direct bindings, which is debuginfo-independent. This is SOUND:
    // MIR guarantees locals `1..=arg_count` ARE the parameters in declaration
    // order, so naming local `i` by the `i`-th HIR binding names the real entry
    // parameter. Recovery happens ONLY when HIR and MIR parameter counts match
    // and every HIR parameter is a plain binding; each name is then rejected if
    // either debug map already occupies its local or spelling. With empty
    // `var_debug_info` no body local carries a name, so no shadow can exist in
    // the formula namespace (the copy-propagated-shadow false-PROVE hazard
    // requires a *misleading debug entry*, which absent debug info cannot
    // produce). Every present-but-conflicting debug-name case keeps its existing
    // fail-closed shadow gate untouched. The shared recovery above injects every
    // accepted HIR binding into both maps before body extraction.
    let skipped = contract_assumption_gate::gate_contract_preconditions(
        &mut preconditions,
        &verifiable_body,
        &debug_name_locals,
    );
    for reason in &skipped {
        tcx.sess.dcx().span_warn(
            body.span,
            format!(
                "`#[trust::requires]` on `{name}` is not assumed for body verification: {}",
                reason.describe()
            ),
        );
    }

    // Trust: attach always-true enum-discriminant range invariants so exhaustive
    // `match` arms prove their otherwise-`Unreachable` obligation instead of
    // degrading to runtime-checked. See `enum_discriminant_range_preconditions`.
    preconditions.extend(enum_discriminant_range_preconditions(tcx, body, &verifiable_body));

    // Trust: attach the always-true Unicode-scalar-value range invariant for
    // char-typed locals (the char type invariant; see
    // `char_range_preconditions`) — without it the u32 lowering lets the
    // solver pick values above char::MAX (e.g. 268435456) and false-refute
    // arithmetic/allocation guards downstream of `.chars()` loops.
    preconditions.extend(char_range_preconditions(body, &verifiable_body));

    // Trust: attach the always-true integer type-range invariant
    // `MIN_T <= p <= MAX_T` for each integer PARAMETER — without it the param's
    // `Sort::Int` var is unconstrained and the solver false-refutes facts that
    // hold for every in-type value (e.g. `x.saturating_add(y) >= x` needs
    // `y >= 0`). A type tautology, so sound to add unconditionally after the
    // assumption gate (see `integer_param_range_preconditions`). Audit #6.
    preconditions.extend(integer_param_range_preconditions(&verifiable_body));

    VerifiableFunction {
        name,
        def_path,
        span: convert::convert_span(tcx, body.span),
        body: verifiable_body,
        contracts: metadata.contracts,
        preconditions,
        postconditions,
        spec,
    }
}

/// Trust: emit always-true enum-discriminant range invariants as function
/// preconditions. Two consumers benefit: an exhaustive `match` discharges its
/// `otherwise -> Unreachable` obligation statically (the original #24 use), and
/// — #28 — an `e as int` cast and any arithmetic on the result are bounded, so
/// `let d = e as u32; if d >= 1 { d - 1 }` proves instead of false-FAILing.
///
/// For a discriminant temp `_d` assigned exactly once — by
/// `Rvalue::Discriminant(_p)` where `_p` is an enum with valid discriminant tags
/// `{t0, t1, …}` — the fact `_d ∈ {t0, t1, …}` holds wherever `_d` is read (the
/// discriminant of any validly-constructed enum is one of its tags; reading the
/// discriminant of an invalidly-constructed one is already UB upstream). We emit
/// it for *every* such temp, independent of how `_d` is consumed. For an
/// exhaustive switch `check_unreachable` conjoins it into the unreachable block's
/// path condition `_d ∉ targets`, giving `(_d ∈ tags) ∧ (_d ∉ tags)` = UNSAT →
/// proved; a partial match closed with `unreachable_unchecked()` (`targets ⊊
/// tags`) stays SAT → not proved, preserving its genuine UB obligation. For the
/// `e as int` path the same `_d ∈ {tags}` kills the free-i64 cast-overflow model
/// (`_d = -1`) that otherwise false-FAILs the cast and any downstream arithmetic.
///
/// Soundness rests on single-assignment: a global precondition about `_d` is only
/// sound if `_d` never legitimately holds a non-discriminant value, so we require
/// exactly one write to `_d` across the body. Emitting it unconditionally (not
/// only when `_d` drives an `Unreachable`-otherwise switch) is monotone-safe: the
/// fact is always true, so it can only turn a false-FAIL into a PROVE, never an
/// overflow into a false-PROVE. The tag values are discriminant *values*
/// (`discr.val`), matching both the `e as int` cast result and a `match` guard,
/// so this introduces no value-vs-index skew on the read side.
fn enum_discriminant_range_preconditions<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    vbody: &VerifiableBody,
) -> Vec<Formula> {
    // Single pass over the lowered body: count writes per local so the
    // single-assignment soundness gate below can require exactly one definition
    // of each discriminant temp.
    let mut write_counts: FxHashMap<usize, u32> = FxHashMap::default();
    for block in &vbody.blocks {
        for stmt in &block.stmts {
            let written = match stmt {
                Statement::Assign { place, .. } => Some(place.local),
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                    Some(place.local)
                }
                _ => None,
            };
            if let Some(local) = written {
                *write_counts.entry(local).or_default() += 1;
            }
        }
        if let Terminator::Call { dest, .. } = &block.terminator {
            *write_counts.entry(dest.local).or_default() += 1;
        }
    }

    // Resolve each whole-local discriminant temp `_d = Discriminant(src)` to the
    // tag set of `src`'s enum type. Scanning the rustc body (not the lowered
    // `vbody`) lets `Place::ty` resolve `src` through an arbitrary projection
    // chain — `Downcast` / `Field` / `Deref` — so a discriminant read on a
    // *nested* enum payload (e.g. the inner `Result` of `Option<Result<_, _>>`,
    // read as `Discriminant(o.downcast(1).field(0))`) recovers the INNER enum's
    // tags. Using the inner tag set is soundness-critical: emitting the outer
    // enum's (possibly smaller) tag set could exclude a valid inner discriminant
    // and turn a genuinely-reachable block UNSAT — a false-PROVE. rustc local
    // indices coincide with `vbody` local indices, so this map keys join with the
    // `vbody`-derived `d` in the switch loop below.
    let mut discr_tags: FxHashMap<usize, Vec<u128>> = FxHashMap::default();
    for bb in body.basic_blocks.iter() {
        for stmt in &bb.statements {
            let mir::StatementKind::Assign(box (place, mir::Rvalue::Discriminant(src))) =
                &stmt.kind
            else {
                continue;
            };
            if !place.projection.is_empty() {
                continue;
            }
            if let Some(tags) = place_enum_tags(tcx, body, src) {
                discr_tags.insert(place.local.as_usize(), tags);
            }
        }
    }

    // Emit `_d ∈ {tags}` for every single-assignment discriminant temp, in a
    // deterministic (ascending-local) order. Iterating the temps directly rather
    // than only those feeding an `Unreachable`-otherwise switch extends the
    // invariant to the `e as int` cast / arithmetic path; the exhaustive-
    // match discharge is the subset whose temp also drives such a switch.
    let mut out = Vec::new();
    let mut ds: Vec<usize> = discr_tags.keys().copied().collect();
    ds.sort_unstable();
    for d in ds {
        let tags = &discr_tags[&d];
        if tags.is_empty() {
            continue;
        }
        // Discriminant temps are non-return (0), non-argument (1..=arg_count) locals.
        if d <= vbody.arg_count {
            continue;
        }
        // Sound only if `_d` is never overwritten with a non-discriminant value.
        if write_counts.get(&d).copied() != Some(1) {
            continue;
        }
        // Must be integer-sorted to share its SMT var with the cast / switch guard.
        if !matches!(vbody.locals.get(d).map(|l| &l.ty), Some(Ty::Int { .. })) {
            continue;
        }
        let name =
            vbody.locals.get(d).and_then(|l| l.name.clone()).unwrap_or_else(|| format!("_{d}"));
        let eqs: Vec<Formula> = tags
            .iter()
            .map(|&t| {
                Formula::Eq(
                    Box::new(Formula::var(&name, Sort::Int)),
                    Box::new(discriminant_tag_to_formula(t)),
                )
            })
            .collect();
        out.push(match eqs.len() {
            1 => eqs.into_iter().next().unwrap_or(Formula::Bool(true)),
            _ => Formula::Or(eqs),
        });
    }
    out
}

/// Trust: emit the always-true Unicode-scalar-value range invariant for
/// char-typed locals as function preconditions — the exact sibling of
/// [`enum_discriminant_range_preconditions`] for the `char` type invariant.
///
/// Rust guarantees every `char` value is a Unicode scalar value: in
/// `[0, 0x10FFFF]` and outside the surrogate gap `[0xD800, 0xDFFF]`
/// (constructing any other value — e.g. via `char::from_u32_unchecked` — is
/// declared UB, so no defined execution violates it). The lowering models
/// `char` as `u32` (ty_convert: "Char: map to u32"), erasing that invariant;
/// the solver then picks values above `char::MAX` (observed: 268435456) and
/// FALSE-REFUTES arithmetic and allocation guards downstream of `.chars()`
/// loops. Char-ness is recovered from the RUSTC body's local types (the
/// lowered body only shows the u32).
///
/// SOUNDNESS mirrors the discriminant pass: the fact is a universal type
/// invariant (monotone — it deletes only infeasible models; any real
/// violation's witness also satisfies it, so no false-PROVE), and it is
/// emitted only for non-argument locals with EXACTLY ONE textual definition
/// (every value the local ever holds comes from that one char-producing
/// statement), binding the bare entry name exactly as the discriminant facts
/// do. Arguments are skipped like the discriminant pass skips them (a
/// parameter-named precondition would become a call-site PROVE obligation —
/// a separate mechanism).
fn char_range_preconditions<'tcx>(body: &mir::Body<'tcx>, vbody: &VerifiableBody) -> Vec<Formula> {
    // Textual write counts (same single-assignment gate as the discriminant
    // pass — one MIR assignment statement, even inside a loop, means every
    // value the local holds is produced by that char-typed definition).
    let mut write_counts: FxHashMap<usize, u32> = FxHashMap::default();
    for block in &vbody.blocks {
        for stmt in &block.stmts {
            let written = match stmt {
                Statement::Assign { place, .. } => Some(place.local),
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                    Some(place.local)
                }
                _ => None,
            };
            if let Some(local) = written {
                *write_counts.entry(local).or_default() += 1;
            }
        }
        if let Terminator::Call { dest, .. } = &block.terminator {
            *write_counts.entry(dest.local).or_default() += 1;
        }
    }

    let mut out = Vec::new();
    for (idx, decl) in body.local_decls.iter_enumerated() {
        if !matches!(decl.ty.kind(), rustc_middle::ty::TyKind::Char) {
            continue;
        }
        let l = idx.as_usize();
        // Non-return, non-argument locals only (see the doc comment).
        if l == 0 || l <= vbody.arg_count {
            continue;
        }
        if write_counts.get(&l).copied() != Some(1) {
            continue;
        }
        // Defensive: the lowered local must be the u32 char lowers to, so the
        // fact shares its SMT var with the arithmetic/comparison reads.
        if !matches!(vbody.locals.get(l).map(|d| &d.ty), Some(Ty::Int { width: 32, signed: false }))
        {
            continue;
        }
        let name =
            vbody.locals.get(l).and_then(|d| d.name.clone()).unwrap_or_else(|| format!("_{l}"));
        let var = || Formula::var(&name, Sort::Int);
        out.push(Formula::And(vec![
            Formula::Ge(Box::new(var()), Box::new(Formula::Int(0))),
            Formula::Le(Box::new(var()), Box::new(Formula::Int(0x10FFFF))),
            Formula::Not(Box::new(Formula::And(vec![
                Formula::Ge(Box::new(var()), Box::new(Formula::Int(0xD800))),
                Formula::Le(Box::new(var()), Box::new(Formula::Int(0xDFFF))),
            ]))),
        ]));
    }
    out
}

/// Attach the always-true type-range invariant `MIN_T <= p <= MAX_T` for each
/// integer PARAMETER `p` (locals `1..=arg_count`). A parameter has no in-body
/// definition to bound it, so its lowered `Sort::Int` SMT var is otherwise
/// unconstrained and the solver may pick an OUT-OF-TYPE value (e.g. a "negative"
/// `u32`), FALSELY REFUTING an arithmetic/postcondition fact that holds for every
/// real value of the type (e.g. `x.saturating_add(y) >= x` needs `y >= 0`; a
/// guarded `arr[i]` with `i: usize` needs `i >= 0`). Over-refutation audit #6.
///
/// SOUND unconditionally: the bound is a TAUTOLOGY of the parameter's type — it
/// holds for EVERY value the parameter can take, entry or (for a `mut` param)
/// after any in-body reassignment, since a reassignment preserves the type. So,
/// unlike a value-specific `#[requires]`, it is immune to the shadow/mutation
/// hazards the contract-assumption gate guards against, and is added AFTER that
/// gate (like the char/discriminant range facts). It can only CLOSE a false
/// refutation, never admit a false proof. Capped at width <= 64 (the literal
/// bounds must be i128-representable; wider params get no fact — fail-open to the
/// prior behavior, never mis-bounded).
fn integer_param_range_preconditions(vbody: &VerifiableBody) -> Vec<Formula> {
    let mut out = Vec::new();
    for decl in &vbody.locals {
        if decl.index < 1 || decl.index > vbody.arg_count {
            continue;
        }
        let Ty::Int { width, signed } = &decl.ty else {
            continue;
        };
        let (width, signed) = (*width, *signed);
        if width == 0 || width > 64 {
            continue;
        }
        let Some(name) = decl.name.as_deref() else {
            continue;
        };
        // Name the fact EXACTLY as `place_to_var_name` names this local in the
        // body VCs: the source name only when it is UNIQUE across all locals,
        // else the collision-safe `_<index>`. A shadowed param name (shared with
        // a body local) otherwise renders as `_<index>` in the body while this
        // fact would say the bare name — disconnected (harmless) at best, or, if
        // it collided onto a differently-typed shadow, an unsound bound. This
        // keeps the fact bound to THIS parameter local and no other.
        let name_unique =
            vbody.locals.iter().filter(|d| d.name.as_deref() == Some(name)).count() == 1;
        let var_name = if name_unique { name.to_string() } else { format!("_{}", decl.index) };
        let (min, max): (i128, i128) = if signed {
            (-(1i128 << (width - 1)), (1i128 << (width - 1)) - 1)
        } else {
            (0, (1i128 << width) - 1)
        };
        let var = || Formula::var(&var_name, Sort::Int);
        out.push(Formula::And(vec![
            Formula::Ge(Box::new(var()), Box::new(Formula::Int(min))),
            Formula::Le(Box::new(var()), Box::new(Formula::Int(max))),
        ]));
    }
    out
}

/// Tag set of the enum a `Discriminant(place)` rvalue reads, or `None` if `place`
/// is not enum-typed. `Place::ty` walks the projection elems (`Downcast` /
/// `Field` / `Deref`), so for a nested-enum payload read this returns the INNER
/// enum's type — exactly the type whose tag the `Discriminant` rvalue observes.
fn place_enum_tags<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    place: &mir::Place<'tcx>,
) -> Option<Vec<u128>> {
    // Peel a single reference defensively: a by-`&Enum` match lowers to
    // `Discriminant((*r))`, which `Place::ty` already resolves to the enum, but a
    // bare reference source would otherwise be misread.
    let mut ty = place.ty(&body.local_decls, tcx).ty;
    if let rustc_middle::ty::TyKind::Ref(_, inner, _) = ty.kind() {
        ty = *inner;
    }
    if let rustc_middle::ty::TyKind::Adt(adt_def, _) = ty.kind() {
        if adt_def.is_enum() {
            return Some(adt_def.discriminants(tcx).map(|(_, discr)| discr.val).collect());
        }
    }
    None
}

/// Trust: piece #13 step-2 (safe-async data-safety) — whether `place`'s type is
/// (or peels a single reference to) a COROUTINE frame. A `Discriminant` read on a
/// coroutine selects the resume STATE; its `SwitchInt` covers the valid states
/// with an `otherwise -> Unreachable` arm that is genuinely infeasible (the
/// discriminant is always one of the declared states). We recognize this
/// STRUCTURALLY (the source is a coroutine + the switch cases + an unreachable
/// otherwise) rather than via the coroutine LAYOUT query: `coroutine_layout`
/// requires the OPTIMIZED MIR of this very body, so calling it from inside the
/// MIR-optimization pass (`trust_verify`) triggers a query CYCLE (E0391). The
/// state discriminant type is `u32` and the `otherwise -> unreachable` is rustc's
/// own certification that the switch cases are exhaustive over the states, so no
/// tag-set computation is needed — the case set trivially equals the full state
/// set. SOUNDNESS: identical "selector ∈ cases ⇒ otherwise infeasible" reasoning
/// as an enum match; only a coroutine-discriminant switch with an unreachable
/// otherwise is marked, so a genuine `unreachable_unchecked` elsewhere is
/// untouched.
fn place_ty_is_coroutine<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    place: &mir::Place<'tcx>,
) -> bool {
    let mut ty = place.ty(&body.local_decls, tcx).ty;
    if let rustc_middle::ty::TyKind::Ref(_, inner, _) = ty.kind() {
        ty = *inner;
    }
    matches!(ty.kind(), rustc_middle::ty::TyKind::Coroutine(..))
}

/// Mirror `trust_vcgen::u128_to_formula` so the invariant's constant terms are
/// byte-identical to the switch guard's, guaranteeing they cancel for exhaustive
/// matches regardless of the discriminant's absolute (possibly signed) value.
fn discriminant_tag_to_formula(value: u128) -> Formula {
    match i128::try_from(value) {
        Ok(n) => Formula::Int(n),
        Err(_) => Formula::UInt(value),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExtractionPurpose {
    Verification,
    Codegen,
}

/// Extract trust-related metadata for a local MIR body.
///
/// This is a sidecar API for issue #10: it keeps the existing `VerifiableFunction`
/// shape intact while making trust annotations explicit and independently testable.
/// Like `extract_function`, this native path does not use compatibility source
/// scraping when compiler contract facts are unavailable.
#[cfg(test)]
pub(crate) fn extract_metadata<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> TrustMetadata {
    extract_metadata_with_contract_bundle(tcx, body, None)
}

fn extract_metadata_with_contract_bundle<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    compiler_contracts: Option<&CompilerContractBundle>,
) -> TrustMetadata {
    let def_id = body.source.def_id();
    let (contracts, contract_extraction) = extract_contracts(tcx, def_id, compiler_contracts);
    // Proof items come exclusively from the compiler-owned contract bundle
    // (native syntax, e.g. `TrustProofItemSource::NativeHarness`). The legacy
    // `#[kani::proof]` / `#[kani::proof_for_contract]` HIR-attribute import was
    // deleted in the R2 deletion wave (D-B).
    let proof_items =
        compiler_contracts.map(|bundle| bundle.proof_items.clone()).unwrap_or_default();
    // Build structured FunctionSpec from contracts.
    let spec = build_function_spec(&contracts);
    TrustMetadata {
        contracts,
        proof_items,
        trust_annotations: extract_trust_annotations(tcx, def_id),
        spec,
        contract_extraction,
    }
}

/// Trust: Safely get the span of an attribute. Returns None for parsed
/// built-in attributes that have no meaningful span (e.g., #[inline]).
/// Only `Unparsed` (custom/tool) attributes and a few known `Parsed` variants
/// carry a usable span; all others return None instead of panicking.
fn safe_attr_span(attr: &rustc_hir::Attribute) -> Option<rustc_span::Span> {
    match attr {
        // Custom / tool attributes always have a span.
        rustc_hir::Attribute::Unparsed(item) => Some(item.span),
        // Known Parsed variants with spans (mirrors AttributeExt::span).
        rustc_hir::Attribute::Parsed(AttributeKind::DocComment { span, .. }) => Some(*span),
        rustc_hir::Attribute::Parsed(AttributeKind::Deprecated { span, .. }) => Some(*span),
        // All other Parsed attributes don't have a reliably accessible span.
        rustc_hir::Attribute::Parsed(_) => None,
    }
}

fn extract_contracts(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    compiler_contracts: Option<&CompilerContractBundle>,
) -> (Vec<Contract>, ContractExtractionReport) {
    let synthetic_parameter = def_id
        .as_local()
        .and_then(|local_def_id| first_synthetic_contract_parameter(tcx, local_def_id));
    if let Some(bundle) = compiler_contracts {
        if !bundle.contracts.is_empty() {
            if let Some((span, name, collision)) = synthetic_parameter.as_ref() {
                return reject_contracts_for_synthetic_parameter(tcx, *span, name, *collision);
            }
            return (
                bundle.contracts.clone(),
                ContractExtractionReport {
                    source: ContractExtractionSource::CompilerContractBundle,
                    source_scraping_used: false,
                    diagnostics: vec![],
                },
            );
        }
    }

    let Some(local_def_id) = def_id.as_local() else {
        return (
            vec![],
            ContractExtractionReport {
                source: ContractExtractionSource::Unavailable,
                source_scraping_used: false,
                diagnostics: vec![
                    "contract extraction unavailable for non-local DefId; source scraping disabled"
                        .to_string(),
                ],
            },
        );
    };

    let hir_id = tcx.local_def_id_to_hir_id(local_def_id);
    let source_map = tcx.sess.source_map();
    let contracts: Vec<_> = tcx
        .hir_attrs(hir_id)
        .iter()
        .filter_map(|attr| {
            let kind = attr.path().last().copied().and_then(contract_kind_from_symbol)?;
            let span = attr.value_span().or_else(|| safe_attr_span(attr))?;
            let body = attr
                .value_str()
                .map(|value| value.to_string())
                .or_else(|| {
                    safe_attr_span(attr).and_then(|s| {
                        source_map
                            .span_to_snippet(s)
                            .ok()
                            .map(|snippet| contract_body_from_attr_snippet(&snippet))
                    })
                })
                .unwrap_or_default();

            Some(Contract { kind, span: convert::convert_span(tcx, span), body })
        })
        .collect();

    if !contracts.is_empty() {
        if let Some((span, name, collision)) = synthetic_parameter.as_ref() {
            return reject_contracts_for_synthetic_parameter(tcx, *span, name, *collision);
        }
        return (
            contracts,
            ContractExtractionReport {
                source: ContractExtractionSource::RustcHirAttributes,
                source_scraping_used: false,
                diagnostics: vec![],
            },
        );
    }

    // R-U §1.2-5: the legacy compat/debug source-scraping fallback is deleted.
    // When neither a compiler bundle nor HIR attributes provide contract facts,
    // extraction fails closed: no contracts, an explicit diagnostic, never a
    // silently recovered spec.
    (
        vec![],
        ContractExtractionReport {
            source: ContractExtractionSource::Unavailable,
            source_scraping_used: false,
            diagnostics: vec![
                "native contract facts unavailable; compatibility source scraping disabled"
                    .to_string(),
            ],
        },
    )
}

/// Find a source parameter whose name aliases a Formula leaf minted by Trust.
///
/// This mirrors the compiler query's recursive parameter-pattern gate.  The
/// extractor must repeat the check because `extract_function(tcx, body)` and
/// the HIR-attribute compatibility seam can run with `compiler_contracts ==
/// None`; trusting those attributes without this guard would bypass the query
/// entirely.  Return only the first collision: one hard error is enough to
/// make the definition unavailable, and no partial contract bundle survives.
fn first_synthetic_contract_parameter(
    tcx: TyCtxt<'_>,
    local_def_id: rustc_span::def_id::LocalDefId,
) -> Option<(rustc_span::Span, String, trust_types::SourceContractSyntheticNameCollision)> {
    struct Collector {
        found:
            Option<(rustc_span::Span, String, trust_types::SourceContractSyntheticNameCollision)>,
    }

    impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for Collector {
        fn visit_pat(&mut self, pat: &'tcx rustc_hir::Pat<'tcx>) {
            if self.found.is_none() {
                if let rustc_hir::PatKind::Binding(_, canonical_id, ident, _) = pat.kind {
                    if canonical_id == pat.hir_id {
                        if let Some(collision) =
                            trust_types::source_contract_synthetic_name_collision(
                                ident.name.as_str(),
                            )
                        {
                            self.found = Some((pat.span, ident.name.to_string(), collision));
                        }
                    }
                }
            }
            rustc_hir::intravisit::walk_pat(self, pat);
        }
    }

    let body = tcx.hir_maybe_body_owned_by(local_def_id)?;
    let mut collector = Collector { found: None };
    use rustc_hir::intravisit::Visitor as _;
    for param in body.params {
        collector.visit_pat(param.pat);
    }
    collector.found
}

fn reject_contracts_for_synthetic_parameter(
    tcx: TyCtxt<'_>,
    span: rustc_span::Span,
    name: &str,
    collision: trust_types::SourceContractSyntheticNameCollision,
) -> (Vec<Contract>, ContractExtractionReport) {
    let namespace = match collision {
        trust_types::SourceContractSyntheticNameCollision::ReturnPlace => "return-place",
        trust_types::SourceContractSyntheticNameCollision::OldValue => "pre-state",
        trust_types::SourceContractSyntheticNameCollision::Projection => "projection",
        trust_types::SourceContractSyntheticNameCollision::PositionalPlace => {
            "positional MIR-place"
        }
        trust_types::SourceContractSyntheticNameCollision::PredicateSymbol => "predicate-symbol",
        trust_types::SourceContractSyntheticNameCollision::GeneratedMetadata => {
            "generated Formula metadata"
        }
    };
    let diagnostic = format!(
        "parameter `{name}` collides with the source-contract synthetic {namespace} namespace"
    );
    // The canonical `trust_contracts` query normally emitted the same class of
    // hard error first.  Avoid duplicate noise when it did; when extraction is
    // entered directly with no bundle, this is the load-bearing fail-closed
    // diagnostic that prevents a dropped caller requirement from compiling.
    if tcx.dcx().has_errors().is_none() {
        tcx.dcx().span_err(span, diagnostic.clone());
    }
    (
        Vec::new(),
        ContractExtractionReport {
            source: ContractExtractionSource::Unavailable,
            source_scraping_used: false,
            diagnostics: vec![diagnostic],
        },
    )
}

fn extract_trust_annotations(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<TrustAnnotation> {
    let Some(local_def_id) = def_id.as_local() else {
        return vec![];
    };

    let hir_id = tcx.local_def_id_to_hir_id(local_def_id);
    let source_map = tcx.sess.source_map();

    tcx.hir_attrs(hir_id)
        .iter()
        .flat_map(|attr| {
            let span = match safe_attr_span(attr) {
                Some(s) => s,
                None => return vec![],
            };
            source_map
                .span_to_snippet(span)
                .ok()
                .map(|snippet| {
                    // Trust (T9 contract-panic): a malformed/empty
                    // `contract_panic` payload is a HARD extraction error, not a
                    // silent drop — an annotation that can never match a panic
                    // message must not vanish while the user believes their
                    // intentional-panic contract is recorded. (rustc dedups the
                    // byte-identical diagnostic if this extraction runs twice
                    // for the same def.)
                    for reason in contract_panic_extraction_errors(&snippet) {
                        tcx.sess.dcx().span_err(span, reason);
                    }
                    trust_annotations_from_attr_snippet(&snippet)
                        .into_iter()
                        .map(|(kind, body)| TrustAnnotation {
                            kind,
                            span: convert::convert_span(tcx, span),
                            body,
                        })
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default()
        })
        .collect()
}

/// Trust (T9 contract-panic): the `contract_panic(message_contains = "...")`
/// payloads declared on `def_id`, for the compiler's verify pass to thread to
/// the trust-vcgen panic-call mint sites through its owner-bound `VcgenContext`.
/// Reuses [`extract_trust_annotations`] — the SAME parser the metadata path
/// uses — so a payload can never differ between the recorded annotation and
/// the one the vcgen matcher sees. Malformed payloads have already been
/// reported as hard errors inside `extract_trust_annotations`; they extract to
/// nothing here (fail-closed: no marker is ever stamped from a broken payload).
#[must_use]
pub fn extract_contract_panic_annotations(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<String> {
    use rustc_hir::def::DefKind;
    let contract_bodies = |did: DefId| -> Vec<String> {
        extract_trust_annotations(tcx, did)
            .into_iter()
            .filter(|a| a.kind == TrustAnnotationKind::ContractPanic)
            .map(|a| a.body)
            .collect::<Vec<_>>()
    };
    let mut out = contract_bodies(def_id);
    // A `#[trust::contract_panic(message_contains = "...")]` on a fn documents an intentional
    // panic for the WHOLE fn body — including panics raised inside its nested closures /
    // coroutines / const-blocks, each of which is a DISTINCT child `def_id`. But
    // `extract_trust_annotations` reads attributes on `def_id` alone, so a nested body would
    // MISS its enclosing fn's contract and the author's declared panic would re-refute — an
    // asymmetry vs `item_has_trust_skip_attr`, which walks to the crate root. Walk ancestors
    // while the current def is a nested body, folding in each enclosing scope's contract_panic
    // bodies up to and including the enclosing fn.
    //
    // SOUNDNESS: `contract_panic` is MESSAGE-MATCHED (`message_contains`). Inheriting it excuses
    // ONLY a nested-body panic whose message matches the declared string — exactly the author's
    // stated intent for that fn's implementation; a differently-messaged panic in the closure
    // still refutes. So this adds no power beyond the message match the mechanism already trusts.
    let mut cur = def_id;
    while matches!(
        tcx.def_kind(cur),
        DefKind::Closure | DefKind::InlineConst | DefKind::AnonConst | DefKind::SyntheticCoroutineBody
    ) {
        let Some(parent) = tcx.opt_parent(cur) else { break };
        out.extend(contract_bodies(parent));
        cur = parent;
    }
    out
}

fn contract_kind_from_symbol(name: Symbol) -> Option<ContractKind> {
    contract_kind_from_name(name.as_str().as_ref())
}

fn contract_kind_from_name(name: &str) -> Option<ContractKind> {
    let name = name.trim();
    let name = name.rsplit("::").next().unwrap_or(name);

    match name {
        "requires" | "contracts_requires" | "trust_requires" => Some(ContractKind::Requires),
        "ensures" | "contracts_ensures" | "trust_ensures" => Some(ContractKind::Ensures),
        "invariant" | "trust_invariant" => Some(ContractKind::Invariant),
        "decreases" | "trust_decreases" => Some(ContractKind::Decreases),
        _ => None,
    }
}

fn contract_body_from_attr_snippet(snippet: &str) -> String {
    let mut body = snippet.trim();

    if let Some(stripped) = body.strip_prefix("#[").and_then(|s| s.strip_suffix(']')) {
        body = stripped.trim();
    }

    if let Some(open_idx) = body.find('(') {
        if let Some(close_idx) = body.rfind(')') {
            if close_idx > open_idx {
                return body[open_idx + 1..close_idx].trim().to_string();
            }
        }
    }

    if let Some(eq_idx) = body.find('=') {
        return body[eq_idx + 1..].trim().trim_matches('"').to_string();
    }

    String::new()
}

fn normalized_contract_spec_body(kind: ContractKind, body: &str) -> Option<String> {
    let body = strip_string_literal(body);
    let body = body.trim();
    let body = body.strip_prefix(LOWERED_COMPILER_CONTRACT_PREFIX).unwrap_or(body);
    if body.is_empty() {
        return None;
    }

    match kind {
        ContractKind::Ensures => {
            Some(normalize_ensures_closure_body(body).unwrap_or_else(|| body.to_string()))
        }
        _ => Some(body.to_string()),
    }
}

fn build_function_spec(contracts: &[Contract]) -> trust_types::FunctionSpec {
    let mut spec = trust_types::FunctionSpec::default();
    for contract in contracts {
        let Some(body) = normalized_contract_spec_body(contract.kind, &contract.body) else {
            continue;
        };
        match contract.kind {
            ContractKind::Requires => spec.requires.push(body),
            ContractKind::Ensures => spec.ensures.push(body),
            ContractKind::Invariant | ContractKind::LoopInvariant => spec.invariants.push(body),
            ContractKind::Decreases | ContractKind::TypeRefinement | ContractKind::Modifies => {}
            _ => {}
        }
    }
    spec
}

fn normalize_ensures_closure_body(body: &str) -> Option<String> {
    let mut rest = body.trim();
    if let Some(stripped) = rest.strip_prefix("move") {
        rest = stripped.trim_start();
    }
    if !rest.starts_with('|') {
        return None;
    }

    let after_open = &rest[1..];
    let close_idx = after_open.find('|')?;
    let arg_spec = after_open[..close_idx].trim();
    if arg_spec.is_empty() || arg_spec.contains(',') {
        return None;
    }

    let arg_name = arg_spec.split(':').next()?.trim();
    if arg_name.is_empty() || !arg_name.chars().all(|ch| ch == '_' || ch.is_ascii_alphanumeric()) {
        return None;
    }

    let mut expr = after_open[close_idx + 1..].trim();
    if let Some(block_expr) = strip_single_expr_block(expr) {
        expr = block_expr;
    }
    if expr.is_empty() {
        return None;
    }

    let expr = replace_deref_ident(expr, arg_name, "result");
    Some(replace_ident(expr.as_str(), arg_name, "result"))
}

fn strip_single_expr_block(expr: &str) -> Option<&str> {
    let expr = expr.trim();
    let inner = expr.strip_prefix('{')?.strip_suffix('}')?.trim();
    if inner.is_empty() || inner.contains(';') {
        return None;
    }
    Some(inner)
}

fn replace_deref_ident(expr: &str, ident: &str, replacement: &str) -> String {
    let mut out = String::with_capacity(expr.len());
    let bytes = expr.as_bytes();
    let ident_bytes = ident.as_bytes();
    let mut i = 0usize;

    while i < bytes.len() {
        if bytes[i] == b'*' {
            let mut j = i + 1;
            while j < bytes.len() && bytes[j].is_ascii_whitespace() {
                j += 1;
            }
            if bytes.get(j..j + ident_bytes.len()) == Some(ident_bytes)
                && is_ident_start_boundary(expr, j)
                && is_ident_end_boundary(expr, j + ident_bytes.len())
            {
                out.push_str(replacement);
                i = j + ident_bytes.len();
                continue;
            }
        }
        out.push(bytes[i] as char);
        i += 1;
    }

    out
}

fn replace_ident(expr: &str, ident: &str, replacement: &str) -> String {
    let mut out = String::with_capacity(expr.len());
    let bytes = expr.as_bytes();
    let ident_bytes = ident.as_bytes();
    let mut i = 0usize;

    while i < bytes.len() {
        if bytes.get(i..i + ident_bytes.len()) == Some(ident_bytes)
            && is_ident_start_boundary(expr, i)
            && is_ident_end_boundary(expr, i + ident_bytes.len())
        {
            out.push_str(replacement);
            i += ident_bytes.len();
            continue;
        }
        out.push(bytes[i] as char);
        i += 1;
    }

    out
}

fn is_ident_start_boundary(text: &str, start: usize) -> bool {
    start == 0 || !is_ident_char(text.as_bytes()[start - 1])
}

fn is_ident_end_boundary(text: &str, end: usize) -> bool {
    end == text.len() || !is_ident_char(text.as_bytes()[end])
}

fn is_ident_char(b: u8) -> bool {
    (b as char).is_ascii_alphanumeric() || b == b'_'
}

fn trust_annotations_from_attr_snippet(snippet: &str) -> Vec<(TrustAnnotationKind, String)> {
    let mut body = snippet.trim();

    if let Some(stripped) = body.strip_prefix("#[").and_then(|s| s.strip_suffix(']')) {
        body = stripped.trim();
    }

    trust_annotations_from_attr_body(body)
}

fn trust_annotations_from_attr_body(body: &str) -> Vec<(TrustAnnotationKind, String)> {
    let body = body.trim();

    if let Some(rest) = body.strip_prefix("trust(").and_then(|s| s.strip_suffix(')')) {
        return split_trust_annotation_items(rest)
            .into_iter()
            .flat_map(trust_annotation_from_item)
            .collect();
    }

    trust_annotation_from_item(body)
}

fn split_trust_annotation_items(body: &str) -> Vec<&str> {
    let mut items = Vec::new();
    let mut start = 0usize;
    let mut depth = 0usize;
    let mut in_string = false;
    let mut escape = false;

    for (idx, ch) in body.char_indices() {
        if in_string {
            if escape {
                escape = false;
            } else if ch == '\\' {
                escape = true;
            } else if ch == '"' {
                in_string = false;
            }
            continue;
        }

        match ch {
            '"' => in_string = true,
            '(' => depth += 1,
            ')' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => {
                items.push(body[start..idx].trim());
                start = idx + ch.len_utf8();
            }
            _ => {}
        }
    }

    let tail = body[start..].trim();
    if !tail.is_empty() {
        items.push(tail);
    }

    items
}

fn trust_annotation_from_item(item: &str) -> Vec<(TrustAnnotationKind, String)> {
    let item = item.trim();
    if item.is_empty() {
        return vec![];
    }

    match item {
        "boundary" | "trust_boundary" => {
            vec![(TrustAnnotationKind::Boundary, String::new())]
        }
        "model" | "trust_model" => vec![(TrustAnnotationKind::Model, String::new())],
        _ => {
            if let Some(body) = trust_assumption_body(item) {
                vec![(TrustAnnotationKind::Assumption, body)]
            } else if let Some(Ok(payload)) = trust_contract_panic_body(item) {
                // Trust (T9 contract-panic): only the WELL-FORMED payload
                // extracts here. The malformed case (`Some(Err(..))`) is NOT a
                // silent drop — `contract_panic_extraction_errors` re-walks the
                // same items at the tcx-bearing extraction site and emits a hard
                // compile error (the unknown-item drop below is the anti-pattern
                // for a recognized-but-broken contract annotation).
                vec![(TrustAnnotationKind::ContractPanic, payload)]
            } else {
                vec![]
            }
        }
    }
}

/// Trust (T9 contract-panic): parse one `contract_panic` annotation item.
///
/// Returns:
///   * `None` — the item is not a `contract_panic` item at all (callers fall
///     through to the unknown-item handling);
///   * `Some(Ok(payload))` — well-formed
///     `contract_panic(message_contains = "<non-empty>")`, payload extracted;
///   * `Some(Err(reason))` — the item IS a `contract_panic` annotation but its
///     payload is malformed or empty. This MUST surface as an extraction ERROR
///     (never a silent drop): a contract-panic annotation that parses to
///     nothing could never match a panic message, and silently dropping it
///     would leave the user believing their intentional-panic contract is
///     recorded when it is not.
///
/// Accepted spellings mirror the sibling arms (`assume`/`trust_assume`) plus
/// the `#[trust::contract_panic(...)]` tool-attribute path form, whose snippet
/// reaches this parser as a single `trust::contract_panic(...)` item.
fn trust_contract_panic_body(item: &str) -> Option<Result<String, String>> {
    let item = item.trim();
    let rest = item
        .strip_prefix("trust::contract_panic")
        .or_else(|| item.strip_prefix("trust_contract_panic"))
        .or_else(|| item.strip_prefix("contract_panic"))?;
    // Reject a mere identifier-prefix collision (e.g. `contract_panicky`).
    if rest.starts_with(|c: char| c.is_ascii_alphanumeric() || c == '_') {
        return None;
    }

    let malformed = |detail: &str| {
        Some(Err(format!(
            "malformed contract_panic annotation `{item}`: {detail}; expected \
             contract_panic(message_contains = \"<non-empty substring of the panic message>\")"
        )))
    };

    let rest = rest.trim();
    let Some(inner) = rest.strip_prefix('(').and_then(|s| s.strip_suffix(')')) else {
        return malformed("missing `(message_contains = \"...\")` payload");
    };
    let inner = inner.trim();
    let Some(value) = inner.strip_prefix("message_contains") else {
        return malformed("payload must be `message_contains = \"...\"`");
    };
    let value = value.trim_start();
    let Some(value) = value.strip_prefix('=') else {
        return malformed("expected `=` after `message_contains`");
    };
    let value = value.trim();
    // The payload must be an explicit non-empty string literal: an unquoted or
    // empty payload matches nothing (or, worse, everything a future laxer
    // matcher might accept) and is rejected fail-closed.
    let Some(payload) = value.strip_prefix('"').and_then(|s| s.strip_suffix('"')) else {
        return malformed("`message_contains` value must be a double-quoted string literal");
    };
    if payload.trim().is_empty() {
        return malformed("`message_contains` payload must be a non-empty substring");
    }
    Some(Ok(payload.to_string()))
}

/// Trust (T9 contract-panic): the malformed-`contract_panic` diagnostics for one
/// attribute snippet. Mirrors the `trust_annotations_from_attr_snippet` →
/// `trust_annotations_from_attr_body` → item traversal exactly (same `#[..]`
/// strip, same `trust(...)` unwrap, same depth/string-aware item split), and
/// shares the single item recognizer `trust_contract_panic_body`, so the "is
/// this a contract_panic item?" judgment can never drift between the extractor
/// and this error walk. Returns one human-readable reason per malformed item.
fn contract_panic_extraction_errors(snippet: &str) -> Vec<String> {
    let mut body = snippet.trim();
    if let Some(stripped) = body.strip_prefix("#[").and_then(|s| s.strip_suffix(']')) {
        body = stripped.trim();
    }
    let items: Vec<&str> =
        if let Some(rest) = body.strip_prefix("trust(").and_then(|s| s.strip_suffix(')')) {
            split_trust_annotation_items(rest)
        } else {
            vec![body]
        };
    items
        .into_iter()
        .filter_map(|item| match trust_contract_panic_body(item) {
            Some(Err(reason)) => Some(reason),
            _ => None,
        })
        .collect()
}

fn trust_assumption_body(item: &str) -> Option<String> {
    let item = item.trim();

    if let Some(rest) = item.strip_prefix("assume").or_else(|| item.strip_prefix("trust_assume")) {
        let rest = rest.trim();
        if rest.is_empty() {
            return Some(String::new());
        }

        if let Some(rest) = rest.strip_prefix('(').and_then(|s| s.strip_suffix(')')) {
            return Some(strip_string_literal(rest.trim()));
        }

        if let Some(rest) = rest.strip_prefix('=') {
            return Some(strip_string_literal(rest.trim()));
        }
    }

    None
}

fn strip_string_literal(text: &str) -> String {
    let trimmed = text.trim();
    trimmed.strip_prefix('"').and_then(|s| s.strip_suffix('"')).unwrap_or(trimmed).to_string()
}

/// Parse contract bodies into precondition and postcondition formulas.
///
/// Uses `trust_types::parse_spec_expr` to convert textual contract bodies from
/// `#[requires("expr")]` and `#[ensures("expr")]` attributes into `Formula` values.
/// An unparseable `requires` is represented by `false`: dropping a declared
/// caller obligation would be fail-open.  Unparseable `ensures` remains
/// withheld because assuming a malformed guarantee would also be unsound.
#[cfg(test)]
fn parse_contract_specs(contracts: &[Contract]) -> (Vec<Formula>, Vec<Formula>) {
    parse_contract_specs_with_typed(contracts, None)
}

fn parse_contract_specs_with_typed(
    contracts: &[Contract],
    compiler_contracts: Option<&CompilerContractBundle>,
) -> (Vec<Formula>, Vec<Formula>) {
    let mut preconditions = Vec::new();
    let mut postconditions = Vec::new();

    for (index, contract) in contracts.iter().enumerate() {
        let typed = compiler_contracts.and_then(|bundle| {
            let has_typed_row = bundle
                .typed_propositions
                .iter()
                .any(|proposition| proposition.source_contract_index == index);
            match bundle.typed_proposition(index, contract) {
                Some(proposition) => Some(Ok(proposition.formula.clone())),
                None if has_typed_row => Some(Err(())),
                None => None,
            }
        });
        if let Some(typed) = typed {
            match (contract.kind, typed) {
                (ContractKind::Requires, Ok(formula)) => preconditions.push(formula),
                (ContractKind::Ensures, Ok(formula)) => postconditions.push(formula),
                (ContractKind::Requires, Err(())) => preconditions.push(Formula::Bool(false)),
                (ContractKind::Ensures, Err(())) => {}
                _ => {}
            }
            continue;
        }
        let Some(body) = normalized_contract_spec_body(contract.kind, &contract.body) else {
            if contract.kind == ContractKind::Requires {
                preconditions.push(Formula::Bool(false));
            }
            continue;
        };
        let Some(formula) = trust_types::parse_spec_expr(&body) else {
            if contract.kind == ContractKind::Requires {
                preconditions.push(Formula::Bool(false));
            }
            continue;
        };
        match contract.kind {
            ContractKind::Requires => preconditions.push(formula),
            ContractKind::Ensures => postconditions.push(formula),
            ContractKind::Invariant | ContractKind::Decreases => {}
            _ => {}
        }
    }

    (preconditions, postconditions)
}

fn source_contract_sort_for_ty(ty: &Ty) -> Sort {
    // A float PARAMETER must restore to its IEEE sort, not the `Int` default: the
    // text parser's `coerce_float_comparison_operands` sorts `s <= 1.0e30` at f64,
    // but `retype_contract_formulas_for_body` then re-sorts every var whose name is
    // a parameter — so a BARE f64 param `s` (a3d-geom's `scale(self, s)`, the
    // `fov_y`/`near`/`far` of the projection builders) would be clobbered back to
    // `Int`, breaking the assumption-gate witness (`eval_float` no longer fires, so
    // the all-zeros model is not found and the whole magnitude precondition is
    // dropped). A FIELD var (`self.0`) is unaffected either way — its name is not a
    // parameter name, so it is never in this environment and keeps its parsed sort.
    match ty {
        Ty::Bool => Sort::Bool,
        Ty::Float { width: 64 } => Sort::Float { eb: 11, sb: 53 },
        Ty::Float { width: 32 } => Sort::Float { eb: 8, sb: 24 },
        _ => Sort::Int,
    }
}

fn contract_sort_environment_for_body(
    body: &VerifiableBody,
) -> std::collections::BTreeMap<String, Sort> {
    let mut sorts = std::collections::BTreeMap::new();
    for local in &body.locals {
        if local.index < 1 || local.index > body.arg_count {
            continue;
        }
        let Some(name) = local.name.as_ref() else { continue };
        sorts.insert(name.clone(), source_contract_sort_for_ty(&local.ty));
        if let Ty::Ref { inner, .. } = &local.ty {
            sorts.insert(format!("{name}*"), source_contract_sort_for_ty(inner));
        }
    }
    sorts.insert("_0".to_string(), source_contract_sort_for_ty(&body.return_ty));
    sorts
}

fn retype_contract_formulas_for_body(
    preconditions: &mut Vec<Formula>,
    postconditions: &mut Vec<Formula>,
    body: &VerifiableBody,
) {
    let sorts = contract_sort_environment_for_body(body);
    for formula in preconditions.iter_mut().chain(postconditions.iter_mut()) {
        *formula = trust_types::retype_formula_variables(formula.clone(), &sorts);
    }
    // A contract clause is a predicate. Keep malformed non-Boolean postconditions
    // out of the reusable fact set; malformed requires are rejected by the body
    // witness gate and remain represented by their raw Contract row for tooling.
    postconditions.retain(|formula| trust_types::infer_sort(formula) == Sort::Bool);
}

/// Extract parsed contract formulas `(preconditions, postconditions)` for an
/// arbitrary `DefId`, including a **bodyless trait-method declaration**.
///
/// The native `trust_contracts` query yields nothing for a trait-method decl
/// (there is no body to attach proof facts to), but its `#[requires]` /
/// `#[ensures]` attributes are still present on the HIR node. This reads them
/// directly (via the same `hir_attrs` path as [`extract_function`]) and parses
/// them with [`trust_types::parse_spec_expr`], so a `dyn Trait` method's
/// contract can be modeled for closed-world dispatch reasoning.
///
/// Native facts only — compiler bundle / HIR attributes, no source scraping
/// (the compat lane is deleted). Returns empty vecs when the def has no recognizable
/// contract attributes. CROSS-CRATE: the native `trust_contracts` query is
/// `separate_provide_extern`, so a NON-LOCAL def's `#[requires]`/`#[ensures]`
/// are read from crate metadata too — this is required for caller-side
/// cross-crate precondition discharge to be fail-closed.
#[must_use]
pub fn extract_contract_formulas_for_def(
    tcx: TyCtxt<'_>,
    def_id: DefId,
) -> (Vec<Formula>, Vec<Formula>) {
    let args = rustc_middle::ty::GenericArgs::identity_for_item(tcx, def_id);
    extract_contract_formulas_for_instance(tcx, def_id, args)
}

/// Extract contract formulas using the exact generic arguments at a call site.
///
/// A generic definition is not a typed contract identity: `f::<bool>` and
/// `f::<i32>` can give the same parameter name different solver sorts.  Callers
/// must use this entry point and key their memo/summary by `(DefId, args)`.
#[must_use]
pub fn extract_contract_formulas_for_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: rustc_middle::ty::GenericArgsRef<'tcx>,
) -> (Vec<Formula>, Vec<Formula>) {
    // The authoritative source is the native typed `trust_contracts` query,
    // which yields structurally typed ensures/requires predicates for the
    // supported query vocabulary (and explicit opaque rows outside it) for any
    // def that has a body. A trait method can only carry a contract via a
    // *default body* (the contract macro rejects bodyless fns), so this covers
    // exactly the trait methods that are eligible for closed-world dispatch
    // reasoning. The `hir_attrs` fallback inside `extract_contracts` handles
    // the attribute surface when no native bundle is present.
    // Trust (cross-crate precondition discharge): read `trust_contracts` on BOTH
    // the local and non-local branch. The query is `separate_provide_extern`
    // (queries.rs:769), so it decodes from crate metadata for a NON-LOCAL def
    // exactly as it does locally. `extract_contracts` short-circuits on a
    // non-empty `compiler_contracts` bundle (lib.rs:623) before reaching its own
    // `as_local()` gate, so a populated cross-crate bundle is honored without
    // touching local-only HIR.
    let rustc_bundle = tcx.trust_contracts(def_id);
    let bundle = match convert_trust_contract_bundle(tcx, rustc_bundle) {
        Ok(bundle) => bundle,
        Err(reason) => {
            let fallback = fail_closed_caller_formulas_for_conversion_error(rustc_bundle);
            let declared_requires = rustc_bundle
                .contracts
                .iter()
                .filter(|contract| {
                    contract.kind == rustc_trust_contract::TrustContractKind::Requires
                })
                .count();
            tcx.dcx().warn(format!(
                "Trust contracts on `{}` are unsupported: {reason}; all guarantees are withheld and {declared_requires} declared caller requirement(s) fail closed",
                safe_def_path_str_with_args(tcx, def_id, args),
            ));
            return fallback;
        }
    };
    let (contracts, _report) = extract_contracts(tcx, def_id, Some(&bundle));
    let has_requires = contracts.iter().any(|contract| contract.kind == ContractKind::Requires);
    let has_ensures = contracts.iter().any(|contract| contract.kind == ContractKind::Ensures);
    if !has_requires && !has_ensures {
        return (Vec::new(), Vec::new());
    }

    let signature = match contract_signature_environment_for_def(tcx, def_id, args) {
        Ok(signature) => signature,
        Err(reason) => {
            tcx.dcx().warn(format!(
                "Trust contracts on `{}` cannot be bound to the typed function signature: {reason}; caller-side requires fail closed",
                safe_def_path_str_with_args(tcx, def_id, args),
            ));
            // Withholding a postcondition is safe. A declared requires whose
            // identity cannot be rebound must remain an impossible caller
            // obligation rather than silently disappear.
            return (
                if has_requires { vec![Formula::Bool(false)] } else { Vec::new() },
                Vec::new(),
            );
        }
    };

    let mut preconditions = Vec::new();
    let mut postconditions = Vec::new();
    for (index, contract) in contracts.iter().enumerate() {
        let (target, clause) = match contract.kind {
            ContractKind::Requires => {
                (&mut preconditions, trust_types::SourceContractClause::Requires)
            }
            ContractKind::Ensures => {
                (&mut postconditions, trust_types::SourceContractClause::Ensures)
            }
            _ => continue,
        };
        let invalid = || {
            if contract.kind == ContractKind::Requires { Some(Formula::Bool(false)) } else { None }
        };
        // `Unsupported` is an explicit compiler-owned semantic state, not a
        // source predicate spelling.  Its payload is diagnostic prose (and may
        // contain quotes/backticks from the original expression), so feeding it
        // through the source parser produces a misleading parse warning at
        // every call site.  Preserve the fail-closed contract boundary
        // directly: an unsupported `requires` remains the impossible caller
        // obligation, while an unsupported `ensures` contributes no guarantee.
        if contract.body.starts_with(UNSUPPORTED_COMPILER_CONTRACT_PREFIX) {
            if let Some(formula) = invalid() {
                target.push(formula);
            }
            continue;
        }
        let Some(body) = normalized_contract_spec_body(contract.kind, &contract.body) else {
            if let Some(formula) = invalid() {
                target.push(formula);
            }
            continue;
        };
        if let Err(error) = trust_types::validate_source_spec_expr(&body, clause, &signature.sorts)
        {
            tcx.dcx().warn(format!(
                "Trust {:?} on `{}` is not a well-typed source predicate: {error}; {}",
                contract.kind,
                safe_def_path_str_with_args(tcx, def_id, args),
                if contract.kind == ContractKind::Requires {
                    "caller-side requires fail closed"
                } else {
                    "postcondition is withheld"
                },
            ));
            if let Some(formula) = invalid() {
                target.push(formula);
            }
            continue;
        }
        let has_typed_row = bundle
            .typed_propositions
            .iter()
            .any(|proposition| proposition.source_contract_index == index);
        let formula = if let Some(proposition) = bundle.typed_proposition(index, contract) {
            proposition.formula.clone()
        } else if has_typed_row {
            tcx.dcx().warn(format!(
                "Trust {:?} on `{}` has duplicate or stale compiler-owned typed proposition provenance; {}",
                contract.kind,
                safe_def_path_str_with_args(tcx, def_id, args),
                if contract.kind == ContractKind::Requires {
                    "caller-side requires fail closed"
                } else {
                    "postcondition is withheld"
                },
            ));
            if let Some(formula) = invalid() {
                target.push(formula);
            }
            continue;
        } else {
            let Ok(formula) = trust_types::parse_spec_expr_result(&body) else {
                if let Some(formula) = invalid() {
                    target.push(formula);
                }
                continue;
            };
            formula
        };
        let typed = retype_source_contract_formula(formula, &signature.sorts);
        let typed = match canonicalize_entry_collection_lengths(typed, &signature.parameters) {
            Ok(typed) => typed,
            Err(reason) => {
                tcx.dcx().warn(format!(
                    "Trust {:?} on `{}` cannot bind a collection-length accessor: {reason}; {}",
                    contract.kind,
                    safe_def_path_str_with_args(tcx, def_id, args),
                    if contract.kind == ContractKind::Requires {
                        "caller-side requires fail closed"
                    } else {
                        "postcondition is withheld"
                    },
                ));
                if let Some(formula) = invalid() {
                    target.push(formula);
                }
                continue;
            }
        };
        match trust_types::check_formula_sort(&typed) {
            Ok(Sort::Bool) => target.push(typed),
            outcome => {
                // NEVER silent: this fallback makes every call site of the
                // function carry an unprovable `Bool(false)` obligation — the
                // exact "constant-true violation with an empty counterexample"
                // shape that cost a debugging session when the sort checker
                // rejected float orderings without a trace. Same warning
                // discipline as the validate-lane failure above.
                tcx.dcx().warn(format!(
                    "Trust {:?} on `{}` is not Bool-sorted after signature retyping ({outcome:?}); {}",
                    contract.kind,
                    safe_def_path_str_with_args(tcx, def_id, args),
                    if contract.kind == ContractKind::Requires {
                        "caller-side requires fail closed"
                    } else {
                        "postcondition is withheld"
                    },
                ));
                if let Some(formula) = invalid() {
                    target.push(formula);
                }
                continue;
            }
        }
    }
    (preconditions, postconditions)
}

/// A failed compiler-bundle conversion must not become an empty successful
/// contract set. Every declared `requires` remains an impossible caller
/// obligation and every `ensures` is withheld. Loop clauses are reported by
/// the conversion error and make whole-function verification unsupported.
fn fail_closed_caller_formulas_for_conversion_error(
    bundle: &rustc_trust_contract::TrustContractBundle<'_>,
) -> (Vec<Formula>, Vec<Formula>) {
    let has_requires = bundle
        .contracts
        .iter()
        .any(|contract| contract.kind == rustc_trust_contract::TrustContractKind::Requires);
    (if has_requires { vec![Formula::Bool(false)] } else { Vec::new() }, Vec::new())
}

fn retype_source_contract_formula(
    formula: Formula,
    signature_sorts: &std::collections::BTreeMap<String, Sort>,
) -> Formula {
    let mut sorts = signature_sorts.clone();
    for name in formula.free_variables() {
        if sorts.contains_key(&name) {
            continue;
        }
        if let Some(base) = name.strip_prefix("old_") {
            if let Some(sort) = signature_sorts.get(base) {
                sorts.insert(name, sort.clone());
                continue;
            }
        }
        let synthetic_base = name
            .strip_suffix("_len")
            .or_else(|| name.strip_suffix("_discr"))
            .or_else(|| name.strip_suffix("_value"))
            .or_else(|| name.strip_suffix("_sign"));
        if synthetic_base.is_some_and(|base| signature_sorts.contains_key(base)) {
            sorts.insert(name, Sort::Int);
        }
        // A FIELD-CHAIN var (`self.0`, `self*.0.0`, `self.0[3].1`) deliberately gets
        // NO entry: the signature environment carries only bare parameter names
        // (plus `<p>*` pointees and `_0`), and a field's type is not recoverable
        // from the name alone here. Forcing `Int` (the old behavior) clobbered the
        // parser's float coercion on f64 field bounds — `self.0 <= 1.0e30` parses
        // Float-sorted, and an Int-clobbered operand either fails the Bool sort
        // check (requires fails closed) or mis-sorts the caller-side Precondition
        // VC. Missing the map keeps the PARSED sort, mirroring the body lane
        // (`contract_sort_environment_for_body`), where field-chain names likewise
        // miss the exact-name retype map. A wrongly-parsed sort can only fail to
        // match downstream — the caller obligation stays (fail-closed).
    }
    trust_types::retype_formula_variables(formula, &sorts)
}

struct ContractSignatureEnvironment {
    sorts: std::collections::BTreeMap<String, Sort>,
    parameters: Vec<(String, Ty)>,
}

fn contract_signature_environment_for_def<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: rustc_middle::ty::GenericArgsRef<'tcx>,
) -> Result<ContractSignatureEnvironment, String> {
    let signature = tcx.fn_sig(def_id).instantiate(tcx, args).skip_binder();
    let inputs = signature.inputs();
    let identities = tcx.fn_arg_idents(def_id);
    if identities.len() != inputs.len() {
        return Err(format!(
            "parameter identity count {} does not match signature input count {}",
            identities.len(),
            inputs.len(),
        ));
    }

    let mut sorts = std::collections::BTreeMap::new();
    let mut parameters = Vec::with_capacity(inputs.len());
    for (index, (identity, input)) in identities.iter().zip(inputs.iter()).enumerate() {
        // Positional `_N` is the same deterministic fallback used by the
        // compiler's callee_param_names and MIR local naming (local 0 is return).
        let name =
            identity.map(|ident| ident.to_string()).unwrap_or_else(|| format!("_{}", index + 1));
        if let Some(collision) = trust_types::source_contract_synthetic_name_collision(&name) {
            let namespace = match collision {
                trust_types::SourceContractSyntheticNameCollision::ReturnPlace => "return-place",
                trust_types::SourceContractSyntheticNameCollision::OldValue => "pre-state",
                trust_types::SourceContractSyntheticNameCollision::Projection => "projection",
                trust_types::SourceContractSyntheticNameCollision::PositionalPlace => {
                    "positional MIR-place"
                }
                trust_types::SourceContractSyntheticNameCollision::PredicateSymbol => {
                    "predicate-symbol"
                }
                trust_types::SourceContractSyntheticNameCollision::GeneratedMetadata => {
                    "generated Formula metadata"
                }
            };
            return Err(format!(
                "parameter `{name}` collides with the source-contract synthetic {namespace} namespace"
            ));
        }
        if input.has_non_region_param() {
            return Err(format!(
                "parameter `{name}` remains generic after call-site instantiation"
            ));
        }
        let lowered = ty_convert::convert_ty(tcx, *input);
        sorts.insert(name.clone(), source_contract_sort_for_ty(&lowered));
        if let Ty::Ref { inner, .. } = &lowered {
            sorts.insert(format!("{name}*"), source_contract_sort_for_ty(inner));
            // A SHARED-ref struct receiver's field bounds spell the pointee
            // chain (`(*self).2` -> `self*.2`); enumerate its scalar leaves
            // under the starred head. A `&mut` pointee is enumerated too — the
            // env only assigns SORTS (never truth), and the entry-stability /
            // assumption gates own the mutability soundness question.
            insert_projected_scalar_leaf_sorts(
                &mut sorts,
                &format!("{name}*"),
                inner,
                PROJECTED_LEAF_DEPTH_LIMIT,
                &mut { PROJECTED_LEAF_ENTRY_BUDGET },
            );
        }
        // Field-chain entries for a BY-VALUE aggregate param (`self: Vec3` ->
        // "self.0"; `m: Mat4` -> "m.0[0].0"). Without them the source-contract
        // validator's chain lookup misses, its Field fallback types the leaf
        // Int, and every float field bound is IllTyped -> the whole requires
        // falls to Bool(false) (an unprovable caller obligation at every call
        // site). The entries carry the same positional index-and-bracket
        // spelling BOTH parsers produce for the canonicalized contract text.
        insert_projected_scalar_leaf_sorts(
            &mut sorts,
            &name,
            &lowered,
            PROJECTED_LEAF_DEPTH_LIMIT,
            &mut { PROJECTED_LEAF_ENTRY_BUDGET },
        );
        parameters.push((name, lowered));
    }
    if signature.output().has_non_region_param() {
        return Err("return type remains generic after call-site instantiation".to_string());
    }
    let output = ty_convert::convert_ty(tcx, signature.output());
    if !matches!(output, Ty::Unit) {
        sorts.insert("_0".to_string(), source_contract_sort_for_ty(&output));
    }
    Ok(ContractSignatureEnvironment { sorts, parameters })
}

/// Return the exact instantiated parameter types used to bind a direct
/// callee's source contracts, in declaration order.
///
/// `None` is deliberately fail-closed: a direct summary without a type vector
/// cannot render generated collection-length symbols, so its length-bearing
/// preconditions remain free and non-dischargeable at the call site.
#[must_use]
pub fn extract_contract_param_types_for_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: rustc_middle::ty::GenericArgsRef<'tcx>,
) -> Option<Vec<Ty>> {
    contract_signature_environment_for_def(tcx, def_id, args)
        .ok()
        .map(|signature| signature.parameters.into_iter().map(|(_, ty)| ty).collect())
}

/// Rebind the source parser's exact collection accessor leaf (`p_len`) to the
/// one length spelling consumed by MIR bounds and modular call substitution
/// (`p__slice_len`). The rebinding is authorized only by the instantiated
/// signature type. If a real parameter already owns `p_len`, the source leaf is
/// ambiguous after parser lowering and the clause is rejected rather than
/// allowing the two values to alias.
fn canonicalize_entry_collection_lengths(
    mut formula: Formula,
    parameters: &[(String, Ty)],
) -> Result<Formula, String> {
    for (name, ty) in parameters {
        if !contract_ty_has_collection_length(ty) {
            continue;
        }
        let source = format!("{name}_len");
        if !formula.free_variables().contains(&source) {
            continue;
        }
        if parameters.iter().any(|(other, _)| other == &source) {
            return Err(format!(
                "generated accessor leaf `{source}` collides with a parameter of the same name"
            ));
        }
        formula = formula.rename_var(&source, &format!("{name}__slice_len"));
    }
    Ok(formula)
}

fn contract_ty_has_collection_length(ty: &Ty) -> bool {
    match ty {
        Ty::Slice { .. } | Ty::Array { .. } | Ty::SymArray { .. } => true,
        Ty::Ref { inner, .. } => contract_ty_has_collection_length(inner),
        Ty::RawPtr { pointee, .. } => contract_ty_has_collection_length(pointee),
        _ => false,
    }
}

/// Bounded depth for [`insert_projected_scalar_leaf_sorts`] — deep enough for
/// any real geometry/config aggregate (`Mat4 -> cols -> [Vec4; 4] -> field` is
/// depth 3), shallow enough that a pathological nest terminates immediately.
const PROJECTED_LEAF_DEPTH_LIMIT: u32 = 8;
/// Entry budget per PARAMETER for the projected-leaf enumeration. On
/// exhaustion the walk simply stops inserting: a missing entry sends the
/// validator to its integer fallback, which fails a float bound closed
/// (`Bool(false)`) — never a wrong sort.
const PROJECTED_LEAF_ENTRY_BUDGET: u32 = 512;
/// Longest array whose elements are enumerated element-by-element; matches the
/// float lane's uniform-index cap in trust-vcgen.
const PROJECTED_LEAF_ARRAY_LIMIT: u64 = 64;

/// Insert `"{prefix}<projection-chain>" -> scalar sort` entries for every
/// Bool/float/integer LEAF reachable from `ty` through STRUCT fields (`.i`,
/// positional index — the canonicalized-contract spelling), tuple fields
/// (`.i`), and fixed-length array elements (`[k]`). The spellings are
/// byte-identical to (a) the var names `spec_parse` lowers the canonicalized
/// contract text to and (b) `projected_chain_name` in the source-contract
/// validator, so ONE map keys both validation and retyping.
///
/// ENUMS are not walked (their field view is variant-dependent — a chain name
/// would be ambiguous); symbolic-length arrays, references, pointers, and every
/// other shape stop the walk at that node (fail-closed: the leaf simply gets no
/// entry). Assigning a WRONG sort is the only hazard, and every inserted sort
/// is the leaf's own `source_contract_sort_for_ty`.
fn insert_projected_scalar_leaf_sorts(
    sorts: &mut std::collections::BTreeMap<String, Sort>,
    prefix: &str,
    ty: &Ty,
    depth: u32,
    budget: &mut u32,
) {
    if depth == 0 || *budget == 0 {
        return;
    }
    match ty {
        Ty::Adt { fields, variants, .. } if variants.is_empty() => {
            for (index, (_, field_ty)) in fields.iter().enumerate() {
                insert_projected_scalar_leaf_entry(
                    sorts,
                    &format!("{prefix}.{index}"),
                    field_ty,
                    depth - 1,
                    budget,
                );
            }
        }
        Ty::Tuple(items) => {
            for (index, item_ty) in items.iter().enumerate() {
                insert_projected_scalar_leaf_entry(
                    sorts,
                    &format!("{prefix}.{index}"),
                    item_ty,
                    depth - 1,
                    budget,
                );
            }
        }
        Ty::Array { elem, len } if *len <= PROJECTED_LEAF_ARRAY_LIMIT => {
            for k in 0..*len {
                insert_projected_scalar_leaf_entry(
                    sorts,
                    &format!("{prefix}[{k}]"),
                    elem,
                    depth - 1,
                    budget,
                );
            }
        }
        _ => {}
    }
}

/// One node of the projected-leaf walk: a scalar gets its entry; an aggregate
/// recurses. (Split from the walker so the scalar/aggregate decision reads at
/// the insertion site.)
fn insert_projected_scalar_leaf_entry(
    sorts: &mut std::collections::BTreeMap<String, Sort>,
    name: &str,
    ty: &Ty,
    depth: u32,
    budget: &mut u32,
) {
    if *budget == 0 {
        return;
    }
    match ty {
        Ty::Bool | Ty::Float { .. } | Ty::Int { .. } => {
            sorts.insert(name.to_string(), source_contract_sort_for_ty(ty));
            *budget -= 1;
        }
        _ => insert_projected_scalar_leaf_sorts(sorts, name, ty, depth, budget),
    }
}

fn extract_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    purpose: ExtractionPurpose,
    debug_names: &FxHashMap<usize, String>,
) -> VerifiableBody {
    // verifier-coverage: the body's own typing env is the sound
    // context for revealing `impl Trait` (opaque) alias types in local /
    // return positions. On the optimized (Runtime-phase) MIR the verifier
    // runs on, this is `TypingEnv::post_analysis(..)`, the mode in which
    // rustc resolves an alias's concrete underlying type within its defining
    // scope. `convert_ty_in_env` resolves monomorphic opaque/projection/inherent
    // aliases and fails safe to `Unsupported` otherwise — see
    // `ty_convert::normalize_alias`.
    let typing_env = body.typing_env(tcx);

    let locals = body
        .local_decls
        .iter_enumerated()
        .map(|(local, decl)| {
            let index = local.as_usize();
            LocalDecl {
                index,
                ty: ty_convert::convert_ty_in_env(tcx, typing_env, decl.ty),
                name: debug_names.get(&index).cloned(),
            }
        })
        .collect();

    let blocks = body
        .basic_blocks
        .iter_enumerated()
        .map(|(bb, bb_data)| {
            convert::convert_basic_block(
                tcx,
                bb,
                bb_data,
                Some(&body.local_decls),
                Some(typing_env),
            )
        })
        .collect();

    let return_ty =
        ty_convert::convert_ty_in_env(tcx, typing_env, body.local_decls[mir::RETURN_PLACE].ty);

    let mut vbody = VerifiableBody { locals, blocks, arg_count: body.arg_count, return_ty };
    if purpose == ExtractionPurpose::Verification {
        // These rewrites are proof-oriented normalizations. Even where they are
        // logically equivalent, they are not a one-to-one executable lowering,
        // so the codegen-purpose path must retain the original MIR shape.
        convert::rewrite_range_contains_calls(tcx, body, &mut vbody);
        convert::discharge_provably_safe_pointer_asserts(tcx, body, &mut vbody);
        // Spawn calls deliberately retain their authenticated def-path unchanged.
        // A callee-name suffix is not proof authority, so extraction never stamps one.
    }
    // Trust: stamp the TyCtxt-vetted exhaustiveness flag onto SwitchInt
    // terminators so the native CHC translator can refute the otherwise-
    // `Unreachable` arm of a full enum match. Runs after lowering because it
    // needs the lowered locals/blocks AND the rustc `mir::Body`.
    mark_exhaustive_enum_unreachable_switches(tcx, body, &mut vbody);
    // Preserve every Drop terminator. In particular, value provenance alone never
    // rewrites a `std::io::Error` Drop into a branch; downstream classification must
    // use authenticated type evidence and otherwise fail closed.
    vbody
}

/// Recover direct parameter bindings from HIR when optimized MIR no longer
/// retains a `VarDebugInfo` row for them.
///
/// The recovery is deliberately narrow: only plain by-value bindings from a
/// body whose parameter count exactly matches MIR are eligible. Existing MIR
/// debug names remain authoritative, and any source-name collision fails
/// closed for that binding instead of guessing which local it denotes.
fn recover_direct_parameter_names(
    tcx: TyCtxt<'_>,
    body: &mir::Body<'_>,
    local_names: &mut FxHashMap<usize, String>,
    name_locals: &mut FxHashMap<String, Vec<usize>>,
) {
    let Some(local_def_id) = body.source.def_id().as_local() else {
        return;
    };
    let Some(hir_body) = tcx.hir_maybe_body_owned_by(local_def_id) else {
        return;
    };
    let source_names = hir_body
        .params
        .iter()
        .map(|param| match param.pat.kind {
            rustc_hir::PatKind::Binding(
                rustc_hir::BindingMode(rustc_hir::ByRef::No, _),
                _,
                ident,
                None,
            ) => Some(ident.name.to_string()),
            _ => None,
        })
        .collect::<Vec<_>>();
    merge_recovered_parameter_names(local_names, name_locals, body.arg_count, &source_names);
}

/// Merge one exact HIR parameter vector into both verifier name maps.
///
/// Recovery is all-or-nothing with respect to HIR shape: the HIR body must have
/// exactly one plain, direct binding for every MIR argument. Individual names
/// then remain fail-closed when they occupy Trust's generated namespace, repeat
/// in the HIR vector, or collide with any debug-owned local or spelling. The
/// occupancy snapshot is taken before insertion so acceptance cannot depend on
/// hash-map or parameter traversal order.
#[allow(rustc::potential_query_instability)]
fn merge_recovered_parameter_names(
    local_names: &mut FxHashMap<usize, String>,
    name_locals: &mut FxHashMap<String, Vec<usize>>,
    arg_count: usize,
    source_names: &[Option<String>],
) {
    if source_names.len() != arg_count || source_names.iter().any(Option::is_none) {
        return;
    }

    let mut source_name_counts = std::collections::BTreeMap::new();
    for name in source_names.iter().flatten() {
        *source_name_counts.entry(name.as_str()).or_insert(0usize) += 1;
    }
    let occupied_locals: FxHashSet<usize> =
        local_names.keys().copied().chain(name_locals.values().flatten().copied()).collect();
    let occupied_names: FxHashSet<&str> = local_names
        .values()
        .map(String::as_str)
        .chain(name_locals.keys().map(String::as_str))
        .collect();

    let mut accepted = Vec::new();
    for (position, name) in source_names.iter().flatten().enumerate() {
        // A legal Rust parameter may occupy a name Trust later mints for a
        // Formula leaf (`s__slice_len`, `__trust_constparam_*`, `_0_value`,
        // etc.).  Never recover that spelling into the verifier model: the
        // per-local `_<index>` fallback is injective, while retaining the
        // source spelling could alias generated metadata even on a function
        // with no contract bundle.
        if trust_types::source_contract_synthetic_name_collision(name).is_some() {
            continue;
        }
        let local = position + 1;
        if source_name_counts.get(name.as_str()) != Some(&1)
            || occupied_locals.contains(&local)
            || occupied_names.contains(name.as_str())
        {
            continue;
        }
        accepted.push((local, name.clone()));
    }

    for (local, name) in accepted {
        local_names.insert(local, name.clone());
        name_locals.insert(name, vec![local]);
    }
}

fn validate_codegen_fidelity<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &mir::Body<'tcx>,
    function: &mut VerifiableFunction,
) -> Result<(), CodegenExtractionError> {
    let def_path = function.def_path.clone();
    let fail = |location: String, detail: String| CodegenExtractionError::UnsupportedMir {
        def_path: def_path.clone(),
        location,
        detail,
    };

    if function.body.locals.len() != mir_body.local_decls.len() {
        return Err(CodegenExtractionError::StructuralMismatch {
            def_path,
            detail: format!(
                "local count changed from {} to {}",
                mir_body.local_decls.len(),
                function.body.locals.len()
            ),
        });
    }
    if function.body.blocks.len() != mir_body.basic_blocks.len() {
        return Err(CodegenExtractionError::StructuralMismatch {
            def_path,
            detail: format!(
                "block count changed from {} to {}",
                mir_body.basic_blocks.len(),
                function.body.blocks.len()
            ),
        });
    }

    if let Some(detail) = codegen_ty_issue(&function.body.return_ty, "return type") {
        return Err(fail("return type".to_string(), detail));
    }
    for (expected, local) in function.body.locals.iter().enumerate() {
        if local.index != expected {
            return Err(CodegenExtractionError::StructuralMismatch {
                def_path,
                detail: format!(
                    "local declaration order changed at slot {expected}: extracted _{}",
                    local.index
                ),
            });
        }
        if let Some(detail) = codegen_ty_issue(&local.ty, &format!("local _{}", local.index)) {
            return Err(fail(format!("local _{}", local.index), detail));
        }
    }

    for (bb, mir_block) in mir_body.basic_blocks.iter_enumerated() {
        let block_index = bb.as_usize();
        let ir_block = &function.body.blocks[block_index];
        if ir_block.id != BlockId(block_index) {
            return Err(CodegenExtractionError::StructuralMismatch {
                def_path,
                detail: format!(
                    "bb{block_index} became bb{} in extracted block order",
                    ir_block.id.0
                ),
            });
        }
        if ir_block.stmts.len() != mir_block.statements.len() {
            return Err(CodegenExtractionError::StructuralMismatch {
                def_path,
                detail: format!(
                    "bb{block_index} statement count changed from {} to {}",
                    mir_block.statements.len(),
                    ir_block.stmts.len()
                ),
            });
        }
        for (statement_index, (mir_statement, statement)) in
            mir_block.statements.iter().zip(&ir_block.stmts).enumerate()
        {
            let location = format!("bb{block_index}[{statement_index}]");
            if !codegen_statement_shape_matches(&mir_statement.kind, statement) {
                return Err(CodegenExtractionError::StructuralMismatch {
                    def_path,
                    detail: format!(
                        "{location} changed statement kind `{}` into `{}`",
                        mir_statement.kind.name(),
                        codegen_statement_name(statement)
                    ),
                });
            }
            if let Some(detail) = codegen_statement_issue(statement) {
                return Err(fail(location, detail));
            }
        }

        validate_codegen_terminator(
            tcx,
            &def_path,
            block_index,
            mir_block.terminator(),
            &ir_block.terminator,
            function.body.blocks.len(),
        )?;
    }

    Ok(())
}

fn codegen_ty_issue(ty: &Ty, context: &str) -> Option<String> {
    let nested = |child: &Ty, suffix: &str| codegen_ty_issue(child, &format!("{context}{suffix}"));
    match ty {
        Ty::Ref { inner, .. } => nested(inner, " pointee"),
        Ty::RawPtr { pointee, .. } => nested(pointee, " pointee"),
        Ty::Slice { elem } | Ty::Array { elem, .. } => nested(elem, " element"),
        Ty::SymArray { .. } => {
            Some(format!("{context} has a symbolic array length after monomorphization"))
        }
        Ty::Tuple(fields) => {
            fields.iter().enumerate().find_map(|(index, field)| nested(field, &format!(".{index}")))
        }
        // These verification models omit rustc's concrete field offsets,
        // discriminant encoding, vtable, or state-machine layout.
        Ty::Adt { name, .. } => Some(format!("{context} uses layout-erased ADT `{name}`")),
        Ty::Datatype { name, .. } => Some(format!("{context} uses proof-only datatype `{name}`")),
        Ty::Closure { name, .. } => Some(format!("{context} uses layout-erased closure `{name}`")),
        Ty::Dynamic { trait_name } => Some(format!(
            "{context} uses trait object `{trait_name}` without exact vtable metadata"
        )),
        Ty::Coroutine { name, .. } => {
            Some(format!("{context} uses layout-erased coroutine `{name}`"))
        }
        Ty::FnDef { sig, .. } | Ty::FnPtr { sig } => {
            for (index, param) in sig.params.iter().enumerate() {
                if let Some(detail) = nested(param, &format!(" parameter {index}")) {
                    return Some(detail);
                }
            }
            nested(&sig.ret, " return")
        }
        Ty::Unsupported { kind, detail } => {
            Some(format!("{context} contains unsupported type `{kind}`: {detail}"))
        }
        Ty::Int { width, .. } if *width > 64 => Some(format!(
            "{context} uses a {width}-bit integer, but executable TrustIr currently preserves at most 64 bits"
        )),
        Ty::Bv(width) if *width > 64 => Some(format!(
            "{context} uses a {width}-bit bitvector, but executable TrustIr currently preserves at most 64 bits"
        )),
        Ty::Bool | Ty::Int { .. } | Ty::Float { .. } | Ty::Bv(_) | Ty::Unit | Ty::Never => None,
        other => Some(format!(
            "{context} uses a type without codegen-fidelity classification: {other:?}"
        )),
    }
}

fn codegen_projection_issue(projection: &Projection) -> Option<String> {
    match projection {
        Projection::Field(_) | Projection::Index(_) | Projection::Deref => None,
        Projection::ConstantIndex { .. } | Projection::Subslice { .. } => None,
        Projection::Downcast(variant) => {
            Some(format!("downcast to variant {variant} lacks concrete rustc layout metadata"))
        }
        Projection::OpaqueCast(_) => {
            Some("opaque-cast projection is a verifier-only type placeholder".to_string())
        }
        Projection::UnwrapUnsafeBinder(_) => {
            Some("unsafe-binder projection is not executable TrustIr".to_string())
        }
        other => Some(format!("unclassified projection {other:?}")),
    }
}

fn codegen_place_issue(place: &Place) -> Option<String> {
    place.projections.iter().enumerate().find_map(|(index, projection)| {
        codegen_projection_issue(projection).map(|detail| format!("projection {index}: {detail}"))
    })
}

fn codegen_const_issue(value: &ConstValue) -> Option<String> {
    match value {
        ConstValue::Bool(_) | ConstValue::Unit => None,
        ConstValue::Int(_) => Some(
            "signed integer constant erases its source bit width; executable codegen cannot infer it faithfully"
                .to_string(),
        ),
        ConstValue::Uint(_, width) if *width > 64 => Some(format!(
            "{width}-bit unsigned constant exceeds executable TrustIr's 64-bit immediate width"
        )),
        ConstValue::Uint(value, width)
            if *width == 0 || *value >= (1_u128 << *width) =>
        {
            Some(format!(
                "unsigned constant {value} does not fit its declared {width}-bit width"
            ))
        }
        ConstValue::Uint(_, _) => None,
        ConstValue::FloatBits { width, .. } => Some(format!(
            "exact {width}-bit float constant has no executable TrustIr bridge lowering"
        )),
        ConstValue::Float(_) => {
            Some("legacy float constant loses its source bit width".to_string())
        }
        ConstValue::Str { .. } => Some(
            "string/byte constant is represented as a symbolic value without allocation provenance"
                .to_string(),
        ),
        ConstValue::OpaqueConst => Some("opaque constant placeholder".to_string()),
        ConstValue::OpaqueScalar { .. } => Some("opaque scalar placeholder".to_string()),
        ConstValue::ConstParam { .. } => {
            Some("uninstantiated const parameter after monomorphization".to_string())
        }
        ConstValue::UnitVariantRef { .. } => Some(
            "unit-variant reference omits the referenced allocation and layout".to_string(),
        ),
        ConstValue::CallableItem { .. } => {
            Some("callable-item constant is an identity-only placeholder".to_string())
        }
        other => Some(format!("unclassified constant {other:?}")),
    }
}

fn codegen_operand_issue(operand: &Operand) -> Option<String> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => codegen_place_issue(place),
        Operand::Constant(value) => codegen_const_issue(value),
        Operand::Symbolic(_) => Some("symbolic verifier operand".to_string()),
        Operand::Unsupported { kind, detail } => {
            Some(format!("unsupported operand `{kind}`: {detail}"))
        }
        other => Some(format!("unclassified operand {other:?}")),
    }
}

fn codegen_rvalue_issue(rvalue: &Rvalue) -> Option<String> {
    let operands = |values: &[&Operand]| values.iter().find_map(|op| codegen_operand_issue(op));
    match rvalue {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) => operands(&[op]),
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            operands(&[lhs, rhs])
        }
        Rvalue::Ref { place, .. }
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::AddressOf(_, place)
        | Rvalue::CopyForDeref(place) => codegen_place_issue(place),
        Rvalue::Repeat(op, _) => codegen_operand_issue(op),
        Rvalue::Aggregate(kind, values) => {
            let kind_issue = match kind {
                AggregateKind::Tuple | AggregateKind::Array | AggregateKind::RawPtr { .. } => None,
                AggregateKind::Adt { name, .. } => {
                    Some(format!("ADT aggregate `{name}` omits concrete rustc layout"))
                }
                AggregateKind::Closure { name, .. } => {
                    Some(format!("closure aggregate `{name}` omits concrete environment layout"))
                }
                AggregateKind::Coroutine { name } | AggregateKind::CoroutineClosure { name } => {
                    Some(format!("coroutine aggregate `{name}` omits concrete state layout"))
                }
                other => Some(format!("unclassified aggregate {other:?}")),
            };
            kind_issue.or_else(|| values.iter().find_map(codegen_operand_issue))
        }
        Rvalue::Unsupported { kind, detail, .. } => {
            Some(format!("unsupported rvalue `{kind}`: {detail}"))
        }
        other => Some(format!("unclassified rvalue {other:?}")),
    }
}

fn codegen_statement_shape_matches(
    mir_kind: &mir::StatementKind<'_>,
    statement: &Statement,
) -> bool {
    match (mir_kind, statement) {
        (mir::StatementKind::Assign(_), Statement::Assign { .. })
        | (mir::StatementKind::SetDiscriminant { .. }, Statement::SetDiscriminant { .. })
        | (mir::StatementKind::StorageLive(_), Statement::StorageLive(_))
        | (mir::StatementKind::StorageDead(_), Statement::StorageDead(_))
        | (mir::StatementKind::PlaceMention(_), Statement::PlaceMention(_))
        | (mir::StatementKind::Coverage(_), Statement::Coverage)
        | (mir::StatementKind::ConstEvalCounter, Statement::ConstEvalCounter)
        | (mir::StatementKind::Nop, Statement::Nop)
        | (mir::StatementKind::FakeRead(_), Statement::Nop)
        | (mir::StatementKind::AscribeUserType(_, _), Statement::Nop)
        | (mir::StatementKind::BackwardIncompatibleDropHint { .. }, Statement::Nop) => true,
        (mir::StatementKind::Intrinsic(_), Statement::Intrinsic { .. })
        | (mir::StatementKind::Intrinsic(_), Statement::Unsupported { .. }) => true,
        _ => false,
    }
}

fn codegen_statement_name(statement: &Statement) -> &'static str {
    match statement {
        Statement::Assign { .. } => "Assign",
        Statement::StorageLive(_) => "StorageLive",
        Statement::StorageDead(_) => "StorageDead",
        Statement::SetDiscriminant { .. } => "SetDiscriminant",
        Statement::Deinit { .. } => "Deinit",
        Statement::Retag { .. } => "Retag",
        Statement::PlaceMention(_) => "PlaceMention",
        Statement::Intrinsic { .. } => "Intrinsic",
        Statement::Unsupported { .. } => "Unsupported",
        Statement::Coverage => "Coverage",
        Statement::ConstEvalCounter => "ConstEvalCounter",
        Statement::Nop => "Nop",
        _ => "<unclassified>",
    }
}

fn codegen_statement_issue(statement: &Statement) -> Option<String> {
    match statement {
        Statement::Assign { place, rvalue, .. } => {
            codegen_place_issue(place).or_else(|| codegen_rvalue_issue(rvalue))
        }
        Statement::SetDiscriminant { place, .. }
        | Statement::Deinit { place }
        | Statement::Retag { place } => codegen_place_issue(place),
        Statement::PlaceMention(place) => codegen_place_issue(place),
        Statement::Intrinsic { name, .. } => {
            Some(format!("intrinsic `{name}` has no codegen-faithful memory/effect lowering"))
        }
        Statement::Unsupported { kind, detail, .. } => {
            Some(format!("unsupported statement `{kind}`: {detail}"))
        }
        Statement::StorageLive(_)
        | Statement::StorageDead(_)
        | Statement::Coverage
        | Statement::ConstEvalCounter
        | Statement::Nop => None,
        other => Some(format!("unclassified statement {other:?}")),
    }
}

fn validate_codegen_terminator<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_path: &str,
    block: usize,
    mir_terminator: &mir::Terminator<'tcx>,
    terminator: &Terminator,
    block_count: usize,
) -> Result<(), CodegenExtractionError> {
    let unsupported = |detail: String| CodegenExtractionError::UnsupportedMir {
        def_path: def_path.to_string(),
        location: format!("bb{block} terminator"),
        detail,
    };
    let abstraction = |detail: String| CodegenExtractionError::SemanticAbstraction {
        def_path: def_path.to_string(),
        block,
        detail,
    };

    if let mir::TerminatorKind::Call { func, target: None, .. } = &mir_terminator.kind {
        let callee = convert::func_operand_name(tcx, func);
        if convert::is_total_noreturn_call(&callee) {
            return Err(abstraction(format!(
                "MIR Call `{callee}` has process-termination semantics, but executable TrustIr has no process-exit terminator (the verifier model uses Return)"
            )));
        }
    }

    if let Terminator::Opaque { kind, targets, .. } = terminator {
        return Err(unsupported(format!("opaque terminator `{kind}` with targets {targets:?}")));
    }

    match (&mir_terminator.kind, terminator) {
        (mir::TerminatorKind::Goto { target }, Terminator::Goto(ir_target))
            if ir_target.0 == target.as_usize() => {}
        (
            mir::TerminatorKind::SwitchInt { discr, targets },
            Terminator::SwitchInt { discr: ir_discr, targets: ir_targets, otherwise, .. },
        ) => {
            let exact_targets = targets
                .iter()
                .map(|(value, target)| (value, BlockId(target.as_usize())))
                .eq(ir_targets.iter().copied());
            if !exact_targets || otherwise.0 != targets.otherwise().as_usize() {
                return Err(abstraction("SwitchInt targets changed during extraction".to_string()));
            }
            if let Some(detail) = codegen_operand_issue(ir_discr) {
                return Err(unsupported(format!("SwitchInt discriminant: {detail}")));
            }
            let _ = discr;
        }
        (mir::TerminatorKind::Return, Terminator::Return)
        | (mir::TerminatorKind::Unreachable, Terminator::Unreachable) => {}
        (
            mir::TerminatorKind::Call { func, args, destination: _, target, unwind, .. },
            Terminator::Call {
                func: callee,
                args: ir_args,
                dest,
                target: ir_target,
                is_foreign,
                ..
            },
        ) => {
            if !matches!(unwind, mir::UnwindAction::Unreachable) {
                return Err(unsupported(format!(
                    "call unwind action `{unwind:?}` is not represented by TrustIr"
                )));
            }
            if !matches!(func, mir::Operand::Constant(box constant)
                if matches!(constant.const_.ty().kind(), rustc_middle::ty::TyKind::FnDef(..)))
            {
                return Err(unsupported(
                    "indirect call target has no executable callable representation".to_string(),
                ));
            }
            if callee == convert::TRUST_TOTAL_CLONE_SENTINEL
                || callee.contains("::<__trust_try_total>")
                || callee.contains("::<__trust_elem_bytes_")
                || callee.contains("::<__trust_str_index>")
            {
                return Err(unsupported(format!("verifier-only callable placeholder `{callee}`")));
            }
            if *is_foreign {
                return Err(unsupported(format!(
                    "foreign call `{callee}` lacks exact ABI metadata"
                )));
            }
            if args.len() != ir_args.len()
                || target.map(|target| BlockId(target.as_usize())) != *ir_target
            {
                return Err(abstraction(format!(
                    "call `{callee}` arguments or normal target changed"
                )));
            }
            if let Some(detail) = codegen_place_issue(dest) {
                return Err(unsupported(format!("call destination: {detail}")));
            }
            if let Some(detail) = ir_args.iter().find_map(codegen_operand_issue) {
                return Err(unsupported(format!("call argument: {detail}")));
            }
        }
        (mir::TerminatorKind::Call { func, .. }, Terminator::Return) => {
            return Err(abstraction(format!(
                "MIR Call `{func:?}` was rewritten into an ordinary Return (noreturn/exit semantics lost)"
            )));
        }
        (mir::TerminatorKind::Call { .. }, other) => {
            return Err(abstraction(format!(
                "MIR Call was rewritten into {}",
                codegen_terminator_name(other)
            )));
        }
        (mir::TerminatorKind::Assert { .. }, _) => {
            return Err(unsupported(
                "Assert omits the exact panic payload and executable unwind edge".to_string(),
            ));
        }
        (mir::TerminatorKind::Drop { .. }, _) => {
            return Err(unsupported(
                "Drop omits the concrete drop-glue instance and executable unwind edge".to_string(),
            ));
        }
        (mir::TerminatorKind::FalseEdge { real_target, .. }, Terminator::Goto(target))
        | (mir::TerminatorKind::FalseUnwind { real_target, .. }, Terminator::Goto(target))
            if target.0 == real_target.as_usize() => {}
        (mir::TerminatorKind::CoroutineDrop, Terminator::Return) => {}
        (mir::TerminatorKind::UnwindResume, _) => {
            return Err(unsupported(
                "UnwindResume has no executable exception-handling lowering".to_string(),
            ));
        }
        (mir::TerminatorKind::UnwindTerminate(reason), _) => {
            return Err(unsupported(format!(
                "UnwindTerminate::{reason:?} has no distinct executable sink"
            )));
        }
        (original, extracted) => {
            return Err(CodegenExtractionError::StructuralMismatch {
                def_path: def_path.to_string(),
                detail: format!(
                    "bb{block} terminator `{}` became `{}`",
                    original.name(),
                    codegen_terminator_name(extracted)
                ),
            });
        }
    }

    for successor in terminator.unguarded_successors() {
        if successor.0 >= block_count {
            return Err(CodegenExtractionError::StructuralMismatch {
                def_path: def_path.to_string(),
                detail: format!(
                    "bb{block} has out-of-range successor bb{} for {block_count} blocks",
                    successor.0
                ),
            });
        }
    }
    Ok(())
}

fn codegen_terminator_name(terminator: &Terminator) -> &'static str {
    match terminator {
        Terminator::Goto(_) => "Goto",
        Terminator::SwitchInt { .. } => "SwitchInt",
        Terminator::Return => "Return",
        Terminator::Call { .. } => "Call",
        Terminator::Assert { .. } => "Assert",
        Terminator::Drop { .. } => "Drop",
        Terminator::Opaque { .. } => "Opaque",
        Terminator::Unreachable => "Unreachable",
        Terminator::Resume => "Resume",
        _ => "<unclassified>",
    }
}

/// Set `exhaustive_enum_unreachable` on every lowered `SwitchInt` whose selector
/// is a genuine single-assignment enum-discriminant temp, whose explicit case
/// values are EXACTLY the enum's full valid discriminant tag set, and whose
/// `otherwise` arm is `Unreachable`. Only such switches may have
/// `selector ∈ {case values}` conjoined into the default arm downstream, so
/// plain-integer switches and partial matches keep their genuine
/// `unreachable_unchecked` UB (Unknown/Fail). Reuses the exact tag-set / gating
/// machinery of `enum_discriminant_range_preconditions`.
fn mark_exhaustive_enum_unreachable_switches<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    vbody: &mut VerifiableBody,
) {
    use std::collections::BTreeSet;

    // (1) single-assignment write counts — identical to the gate in
    // `enum_discriminant_range_preconditions` (built from immutable views first
    // so they don't alias the `&mut vbody.blocks` borrow below).
    let mut write_counts: FxHashMap<usize, u32> = FxHashMap::default();
    for block in &vbody.blocks {
        for stmt in &block.stmts {
            let written = match stmt {
                Statement::Assign { place, .. } => Some(place.local),
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                    Some(place.local)
                }
                _ => None,
            };
            if let Some(local) = written {
                *write_counts.entry(local).or_default() += 1;
            }
        }
        if let Terminator::Call { dest, .. } = &block.terminator {
            *write_counts.entry(dest.local).or_default() += 1;
        }
    }

    // (2) discriminant-temp tag sets — identical to
    // `enum_discriminant_range_preconditions`: `_d = Discriminant(src)` with a
    // whole-local dest maps `d` to the enum's full tag set.
    let mut discr_tags: FxHashMap<usize, Vec<u128>> = FxHashMap::default();
    // Trust: piece #13 step-2 — locals `_d = Discriminant(coroutine_src)`. A
    // coroutine's resume-STATE discriminant switch has an `otherwise ->
    // Unreachable` arm that is genuinely infeasible; recognized STRUCTURALLY (no
    // layout query — that would cycle, E0391) below.
    let mut coroutine_discr_temps: BTreeSet<usize> = BTreeSet::new();
    for bb in body.basic_blocks.iter() {
        for stmt in &bb.statements {
            let mir::StatementKind::Assign(box (place, mir::Rvalue::Discriminant(src))) =
                &stmt.kind
            else {
                continue;
            };
            if !place.projection.is_empty() {
                continue;
            }
            if let Some(tags) = place_enum_tags(tcx, body, src) {
                discr_tags.insert(place.local.as_usize(), tags);
            } else if place_ty_is_coroutine(tcx, body, src) {
                coroutine_discr_temps.insert(place.local.as_usize());
            }
        }
    }

    let arg_count = vbody.arg_count;
    // Snapshot locals' integer-sortedness keyed by index (avoids borrowing
    // `vbody.locals` while `vbody.blocks` is mutably borrowed below).
    let int_locals: BTreeSet<usize> =
        vbody.locals.iter().filter(|l| matches!(&l.ty, Ty::Int { .. })).map(|l| l.index).collect();
    // Otherwise-target reachability snapshot: which lowered blocks end in
    // `Unreachable`, keyed by the block's own `BlockId` (not its vec position,
    // so the `otherwise` BlockId lookup is correct even if blocks are reordered).
    let unreachable_blocks: BTreeSet<usize> = vbody
        .blocks
        .iter()
        .filter(|b| matches!(b.terminator, Terminator::Unreachable))
        .map(|b| b.id.0)
        .collect();

    for block in &mut vbody.blocks {
        let Terminator::SwitchInt {
            discr, targets, otherwise, exhaustive_enum_unreachable, ..
        } = &mut block.terminator
        else {
            continue;
        };
        // (a) selector is a whole-local enum-discriminant temp, single-assigned,
        // non-argument, integer-sorted.
        let Some(d) = whole_local_operand(discr) else { continue };
        // Trust: piece #13 step-2 — a COROUTINE resume-STATE discriminant switch.
        // Its `otherwise -> Unreachable` arm is genuinely infeasible (the state is
        // always one of the declared coroutine states), so mark it exhaustive.
        // Recognized structurally (source is a coroutine + single-assigned u32 temp
        // + unreachable otherwise); NO tag-set equality check — computing the tag
        // set needs the coroutine LAYOUT query, which cycles inside this MIR pass
        // (E0391). rustc emits the `otherwise -> unreachable` ONLY when the switch
        // cases cover all valid states, so it is itself the exhaustiveness
        // certification. The same single-assignment / non-arg / integer-sort gates
        // apply so a mutated or non-state selector is excluded.
        if coroutine_discr_temps.contains(&d) {
            if d <= arg_count
                || write_counts.get(&d).copied() != Some(1)
                || !int_locals.contains(&d)
            {
                continue;
            }
            if unreachable_blocks.contains(&otherwise.0) {
                *exhaustive_enum_unreachable = true;
            }
            continue;
        }
        let Some(tags) = discr_tags.get(&d) else { continue };
        if tags.is_empty()
            || d <= arg_count
            || write_counts.get(&d).copied() != Some(1)
            || !int_locals.contains(&d)
        {
            continue;
        }
        // (b) explicit case values == FULL valid tag set (equality, not subset).
        let cases: BTreeSet<u128> = targets.iter().map(|(v, _)| *v).collect();
        let full: BTreeSet<u128> = tags.iter().copied().collect();
        if cases != full {
            continue;
        }
        // (c) otherwise target's terminator is `Unreachable`.
        if !unreachable_blocks.contains(&otherwise.0) {
            continue;
        }
        *exhaustive_enum_unreachable = true;
    }
}

/// A switch discriminant operand resolved to a whole-local index, or `None` for
/// projected / constant / symbolic operands (which can never be a plain
/// single-assignment discriminant temp).
fn whole_local_operand(op: &Operand) -> Option<usize> {
    match op {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => Some(p.local),
        _ => None,
    }
}

/// Build the RAW debug-info name → locals multimap (no last-write-wins
/// collapse). The assumption gate needs multiplicity: optimized MIR copy-prop
/// can attach a shadowed binding's debug entry to another local — including a
/// different parameter's — which the collapsed map hides.
pub fn build_debug_name_multimap(body: &mir::Body<'_>) -> FxHashMap<String, Vec<usize>> {
    use rustc_middle::mir::VarDebugInfoContents;
    let mut names: FxHashMap<String, Vec<usize>> = FxHashMap::default();

    for debug_info in &body.var_debug_info {
        if let VarDebugInfoContents::Place(place) = &debug_info.value {
            if place.projection.is_empty() {
                names.entry(debug_info.name.to_string()).or_default().push(place.local.as_usize());
            }
        }
    }

    names
}

/// Build a map from Local index to user-visible variable name using debug info.
fn build_debug_name_map(body: &mir::Body<'_>) -> FxHashMap<usize, String> {
    use rustc_middle::mir::VarDebugInfoContents;
    let mut names: FxHashMap<usize, String> = FxHashMap::default();

    for debug_info in &body.var_debug_info {
        if let VarDebugInfoContents::Place(place) = &debug_info.value {
            if place.projection.is_empty() {
                let local = place.local.as_usize();
                let new_name = debug_info.name.to_string();
                // Trust #soundness (global generated-name collision): Rust
                // permits identifiers that occupy Trust's generated Formula
                // namespace.  Demote every such debug name to the unique
                // per-local fallback by omitting it from the extracted model.
                // This closes both `s__slice_len` vs the length of slice `s`
                // and `__trust_constparam_0_N` vs const generic `N`, including
                // contract-less bodies whose query is never evaluated.  It
                // also keeps every downstream fact producer on one spelling,
                // rather than relying on each producer to duplicate a denylist.
                if trust_types::source_contract_synthetic_name_collision(&new_name).is_some() {
                    continue;
                }
                names.insert(local, new_name);
            }
        }
    }

    names
}

#[cfg(test)]
mod tests {
    use super::*;
    extern crate rustc_driver;
    extern crate rustc_hir;
    extern crate rustc_interface;

    use std::collections::BTreeMap;
    use std::io;
    use std::path::{Path, PathBuf};
    use std::sync::Arc;

    use rustc_driver::Compilation;
    use rustc_interface::interface::{Compiler, Config};
    use rustc_middle::mir::trust_contract::{
        TrustContract, TrustContractBundle, TrustContractKind, TrustContractPayloadType,
        TrustContractPredicate, TrustContractPredicateKind, TrustContractSource,
        TrustContractSubject, TrustContractSummary, TrustContractVerifierSort, TrustLoopId,
    };
    use rustc_span::{DUMMY_SP, sym};

    const CONTRACT_FIXTURE_SOURCE: &str = r#"
#![feature(contracts)]

use core::contracts::{ensures, requires};

#[requires(n > 0)]
fn reciprocal(n: u32) -> f64 {
    1.0 / (n as f64)
}

#[ensures(|ret: &i32| *ret >= 0)]
fn abs_broken(x: i32) -> i32 {
    x
}

fn no_contracts(x: i32) -> i32 {
    x + 1
}

// Legal Rust names in Trust's generated Formula namespace must be demoted even
// when there is no contract (and therefore no trust_contracts query gate).
#[allow(non_snake_case)]
fn generated_formula_name_params(
    s: &[u8],
    s__slice_len: usize,
    __trust_constparam_0_N: usize,
) -> usize {
    s.len() + s__slice_len + __trust_constparam_0_N
}

fn slice_last(s: &[u8]) -> u8 {
    s[s.len() - 1]
}

fn option_value(x: i32) -> Option<i32> {
    Some(x)
}

enum TrustRefDir {
    North,
    South,
}

fn trust_dir_by_value(d: TrustRefDir) -> u32 {
    match d {
        TrustRefDir::North => 1,
        TrustRefDir::South => 2,
    }
}

fn trust_dir_by_ref(d: &TrustRefDir) -> u32 {
    match d {
        TrustRefDir::North => 1,
        TrustRefDir::South => 2,
    }
}

// an `enum as int` cast reads the discriminant into a temp that does
// NOT drive an exhaustive-match `otherwise -> Unreachable` switch. The
// generalized discriminant-range precondition must still bound it.
fn trust_discr_as_int(d: TrustRefDir) -> u32 {
    let n = d as u32;
    n + 1
}
"#;
    const CONTRACT_FIXTURE_PATH: &str = "contracts_fixture.rs";
    const CALL_TARGET_FIXTURE_SOURCE: &str = r#"
#![feature(lang_items, no_core)]
#![no_core]

#[lang = "sized"]
pub trait Sized: MetaSized {}

#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}

#[lang = "pointee_sized"]
pub trait PointeeSized {}

#[lang = "copy"]
pub trait Copy: Clone {}

#[lang = "clone"]
pub trait Clone {}

pub trait LocalDebug {}

#[inline(never)]
pub fn helper() -> i32 {
    7
}

pub fn caller() -> i32 {
    helper()
}

pub fn helper_fn_ptr() -> fn() -> i32 {
    helper
}

pub fn dyn_debug_ref(x: &dyn LocalDebug) -> &dyn LocalDebug {
    x
}

pub fn exit_wrapper() -> i32 {
    helper()
}

#[inline(never)]
pub fn identity<T>(value: T) -> T {
    value
}

pub fn mixed_generic_calls(flag: bool, number: i32) -> i32 {
    let _ = identity::<bool>(flag);
    identity::<i32>(number)
}

pub fn collision() -> i32 {
    1
}

pub mod trust_mir_extract_call_target_fixture {
    pub fn collision() -> i32 {
        2
    }
}
"#;
    const CALL_TARGET_FIXTURE_PATH: &str = "call_target_fixture.rs";
    const CODEGEN_FIDELITY_FIXTURE_SOURCE: &str = r#"
#[derive(Clone)]
pub struct Derived(pub u32);

#[inline(never)]
pub fn identity(x: u32) -> u32 {
    x
}

#[inline(never)]
pub fn clone_derived(value: &Derived) -> Derived {
    value.clone()
}

#[inline(never)]
pub fn exit_now() -> ! {
    std::process::exit(7)
}

#[inline(never)]
pub fn may_panic(x: u32) -> u32 {
    if x == 0 { panic!("zero") }
    x
}

#[inline(never)]
pub fn calls_may_panic(x: u32) -> u32 {
    may_panic(x)
}

#[inline(never)]
pub fn checked_add(x: u32) -> u32 {
    x + 1
}

#[inline(never)]
pub fn opaque_bytes() -> &'static [u8] {
    b"abc"
}

#[inline(never)]
pub fn spawn_with_literal_name() -> std::io::Result<std::thread::JoinHandle<()>> {
    std::thread::Builder::new()
        .name("trust-worker".to_string())
        .spawn(|| {})
}

#[inline(never)]
pub fn drop_os_error() {
    let error = std::io::Error::from_raw_os_error(5);
    drop(error);
}
"#;
    const CODEGEN_FIDELITY_FIXTURE_PATH: &str = "codegen_fidelity_fixture.rs";
    const OPTION_RETURN_FIXTURE_SOURCE: &str = r#"
#![feature(auto_traits, const_trait_impl, lang_items, no_core)]
#![no_core]

#[lang = "sized"]
pub trait Sized: MetaSized {}

#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}

#[lang = "pointee_sized"]
pub trait PointeeSized {}

#[lang = "copy"]
pub trait Copy: Clone {}

#[lang = "clone"]
pub trait Clone {}

#[lang = "freeze"]
pub unsafe auto trait Freeze {}

#[lang = "destruct"]
pub const trait Destruct: PointeeSized {}

pub mod std {
    pub mod option {
        pub enum Option<T> {
            None,
            Some(T),
        }
    }
}

pub fn option_value(x: i32) -> crate::std::option::Option<i32> {
    crate::std::option::Option::Some(x)
}
"#;
    const OPTION_RETURN_FIXTURE_PATH: &str = "option_return_fixture.rs";

    // Lever A step 2: a faithful miniature of the kernel's universe-`Level`
    // enum, compiled under `--crate-name clean_kernel` so its def path is
    // EXACTLY `clean_kernel::level::Level` — the def-path the datatype gate
    // (`is_level_datatype_target`) matches. `Param` carries the opaque `Name`,
    // mirroring `clean-kernel/src/level/mod.rs`.
    //
    // `#![no_core]` (like the `option_return`/`call_target` fixtures): the
    // in-process stage2 rustc ICEs (`bug!("expected associated item for operator
    // trait")` in `rustc_hir_typeck::method`) when compiling any std-USING
    // fixture, which is why the full-std fixture tests (contract, const-aggregate)
    // fail environmentally here. The real kernel stores the recursive children
    // behind `Arc<Level>` (= `LevelArc`); this fixture uses raw pointers, which
    // `peel_transparent_pointers` peels to `Level` EXACTLY as it peels
    // `Arc<Level>`, so the extracted datatype shape is identical. (The `Arc`/`Box`/
    // `Rc` wrapper-name recognition is covered by a pure unit test in
    // `ty_convert`.)
    const LEVEL_FIXTURE_SOURCE: &str = r#"
#![feature(lang_items, no_core)]
#![no_core]
#![allow(dead_code)]

#[lang = "sized"]
pub trait Sized: MetaSized {}

#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}

#[lang = "pointee_sized"]
pub trait PointeeSized {}

#[lang = "copy"]
pub trait Copy: Clone {}

#[lang = "clone"]
pub trait Clone {}

pub mod name {
    pub struct Name(pub u64);
}

pub mod level {
    use crate::name::Name;

    pub enum Level {
        Zero,
        Succ(*const Level),
        Max(*const Level, *const Level),
        IMax(*const Level, *const Level),
        Param(Name),
    }
}

pub fn make_level() -> level::Level {
    level::Level::Zero
}
"#;
    const LEVEL_FIXTURE_PATH: &str = "level_fixture.rs";

    // Lever A step 5: a faithful miniature of the kernel's `Expr` STRUCT and the
    // `ExprKind` ENUM (the type the real `infer_type` matches on), compiled under
    // `--crate-name clean_kernel` with the SAME module nesting as the real kernel
    // (`expr/mod.rs` → `expr::Expr`, `expr/kind.rs` → `expr::kind::ExprKind`), so
    // the def paths are EXACTLY what the step-5 datatype gates match. The recursive
    // children use raw pointers (`*const Expr`), which `peel_transparent_pointers`
    // peels IDENTICALLY to the real kernel's `Arc<Expr>` children — so the extracted
    // datatype shape matches. `#![no_core]` for the same reason as the Level fixture
    // (the in-process stage2 rustc ICEs on any std-using fixture). `ExprKind` here
    // carries a REPRESENTATIVE subset of the real 25 variants — one of every
    // FIELD SHAPE the generic lowering must handle: a scalar (`BVar` u32), a `Level`
    // payload (`Sort`), `Name` payloads (`Const`/`Proj`), recursive `Expr` children
    // (`App`/`Lam`/`Let`/`Proj`), a `bool` (`Let`), an opaque `Literal`/`BinderData`
    // payload, a nullary variant (`SProp`), and a struct-style named-field variant
    // (`CubicalPath`). The lowering is generic over `adt_def.variants()`, so it
    // faithfully lowers whatever variant set the REAL `ExprKind` has.
    const EXPR_FIXTURE_SOURCE: &str = r#"
#![feature(lang_items, no_core)]
#![no_core]
#![allow(dead_code)]

#[lang = "sized"]
pub trait Sized: MetaSized {}

#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}

#[lang = "pointee_sized"]
pub trait PointeeSized {}

#[lang = "copy"]
pub trait Copy: Clone {}

#[lang = "clone"]
pub trait Clone {}

pub mod name {
    pub struct Name(pub u64);
}

pub mod level {
    use crate::name::Name;

    pub enum Level {
        Zero,
        Succ(*const Level),
        Max(*const Level, *const Level),
        IMax(*const Level, *const Level),
        Param(Name),
    }
}

pub mod expr {
    pub mod meta {
        pub struct ExprMeta(pub u64);
    }

    pub mod binder {
        pub struct BinderData(pub u64);
    }

    pub mod lit {
        pub enum Literal {
            Nat(u64),
            Str(u64),
        }
    }

    pub mod kind {
        use crate::level::Level;
        use crate::name::Name;
        use super::Expr;
        use super::binder::BinderData;
        use super::lit::Literal;

        pub enum ExprKind {
            BVar(u32),
            Sort(Level),
            Const(Name),
            App(*const Expr, *const Expr),
            Lam(BinderData, *const Expr, *const Expr),
            Let(*const Expr, *const Expr, *const Expr, bool),
            Lit(Literal),
            Proj(Name, u32, *const Expr),
            SProp,
            CubicalPath {
                ty: *const Expr,
                left: *const Expr,
                right: *const Expr,
            },
        }
    }

    pub struct Expr {
        pub kind: kind::ExprKind,
        pub meta: meta::ExprMeta,
    }
}

pub fn make_exprkind() -> expr::kind::ExprKind {
    expr::kind::ExprKind::SProp
}

pub fn wrap_expr(k: expr::kind::ExprKind, m: expr::meta::ExprMeta) -> expr::Expr {
    expr::Expr { kind: k, meta: m }
}

pub fn build_sort(l: level::Level) -> expr::kind::ExprKind {
    expr::kind::ExprKind::Sort(l)
}

pub fn build_sort_expr(l: level::Level, m: expr::meta::ExprMeta) -> expr::Expr {
    expr::Expr { kind: expr::kind::ExprKind::Sort(l), meta: m }
}
"#;
    const EXPR_FIXTURE_PATH: &str = "expr_fixture.rs";

    // WALL C (recursive-datatype-function induction lane) — the SMALLEST REAL
    // self-recursive datatype function: `mirror : &Level -> Level` over the
    // 2-constructor `Level` slice (`Zero | Succ`), the exact shape
    // trust-certify's `level_recursive_functional` discharges by `Level.rec`
    // induction. Compiled under `--crate-name clean_kernel` with the SAME
    // `level::Level` module path as the step-2 fixture, so the step-2 datatype
    // gate (`is_level_datatype_target`) fires and the enum lowers to
    // `Ty::Datatype` — this miniature deliberately carries ONLY the zero/succ
    // constructors (the recursion PRIMITIVE); the full 5-variant `Level`
    // (multi-IH `Max`/`IMax` arms) is the named follow-up.
    //
    // `#![no_core]` + raw-pointer recursive child, for the same environmental
    // reason as the Level/Expr fixtures (the in-process stage2 rustc ICEs on
    // std-using fixtures; `peel_transparent_pointers` peels `*const Level`
    // exactly as it peels the real kernel's `Arc<Level>`). The `Succ` result
    // payload reuses the local's address (`&m`) — semantically dangling at
    // runtime, but this fixture is only ever MIR-extracted, never executed,
    // and the datatype model erases the pointer indirection.
    const MIRROR_FIXTURE_SOURCE: &str = r#"
#![feature(auto_traits, lang_items, no_core)]
#![no_core]
#![allow(dead_code)]

#[lang = "sized"]
pub trait Sized: MetaSized {}

#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}

#[lang = "pointee_sized"]
pub trait PointeeSized {}

#[lang = "copy"]
pub trait Copy: Clone {}

#[lang = "clone"]
pub trait Clone {}

#[lang = "freeze"]
pub unsafe auto trait Freeze {}

pub mod level {
    pub enum Level {
        Zero,
        Succ(*const Level),
    }
}

use level::Level;

pub fn mirror(l: &Level) -> Level {
    match l {
        Level::Zero => Level::Zero,
        Level::Succ(p) => {
            let m = mirror(unsafe { &**p });
            Level::Succ(&m)
        }
    }
}
"#;
    const MIRROR_FIXTURE_PATH: &str = "mirror_fixture.rs";

    // WALL C SCALED TO MUTUAL SCCs — the smallest REAL fuel-indexed mutual
    // cluster: a 3-function ring `fm -> gm -> hm -> fm` (one genuine call-graph
    // SCC of size 3, the size and shape of the kernel's
    // `infer_type <-> whnf <-> is_def_eq` cluster). The FUEL index reuses the
    // gated `level::Level` slice (`Zero | Succ` IS nat-shaped) and the payload
    // reuses the gated `expr::kind::ExprKind` path (2-ctor `A | B` slice), so
    // BOTH enums lower to `Ty::Datatype` through the existing step-2/step-5
    // def-path gates — no extractor changes needed for the mutual fixture.
    // Each member matches fuel first (Zero => per-constructor identity rebuild,
    // NO calls), then the payload; the `Succ` arm's `B` case calls the NEXT
    // ring member at the one-step-smaller fuel — exactly the shape
    // trust-vcgen's `mutual_recursive_datatype_functional` lane walks.
    //
    // `#![no_core]` + raw-pointer recursive children + address-of-local result
    // payloads, for the same environmental reasons as the mirror fixture (the
    // fixture is only ever MIR-extracted, never executed).
    const MUTUAL_FIXTURE_SOURCE: &str = r#"
#![feature(auto_traits, lang_items, no_core)]
#![no_core]
#![allow(dead_code)]

#[lang = "sized"]
pub trait Sized: MetaSized {}

#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}

#[lang = "pointee_sized"]
pub trait PointeeSized {}

#[lang = "copy"]
pub trait Copy: Clone {}

#[lang = "clone"]
pub trait Clone {}

#[lang = "freeze"]
pub unsafe auto trait Freeze {}

pub mod level {
    pub enum Level {
        Zero,
        Succ(*const Level),
    }
}

pub mod expr {
    pub mod kind {
        pub enum ExprKind {
            A,
            B(*const ExprKind),
        }
    }
}

use expr::kind::ExprKind;
use level::Level;

pub fn fm(fuel: &Level, e: &ExprKind) -> ExprKind {
    match fuel {
        Level::Zero => match e {
            ExprKind::A => ExprKind::A,
            ExprKind::B(x) => ExprKind::B(unsafe { &**x }),
        },
        Level::Succ(k) => match e {
            ExprKind::A => ExprKind::A,
            ExprKind::B(x) => {
                let m = gm(unsafe { &**k }, unsafe { &**x });
                ExprKind::B(&m)
            }
        },
    }
}

pub fn gm(fuel: &Level, e: &ExprKind) -> ExprKind {
    match fuel {
        Level::Zero => match e {
            ExprKind::A => ExprKind::A,
            ExprKind::B(x) => ExprKind::B(unsafe { &**x }),
        },
        Level::Succ(k) => match e {
            ExprKind::A => ExprKind::A,
            ExprKind::B(x) => {
                let m = hm(unsafe { &**k }, unsafe { &**x });
                ExprKind::B(&m)
            }
        },
    }
}

pub fn hm(fuel: &Level, e: &ExprKind) -> ExprKind {
    match fuel {
        Level::Zero => match e {
            ExprKind::A => ExprKind::A,
            ExprKind::B(x) => ExprKind::B(unsafe { &**x }),
        },
        Level::Succ(k) => match e {
            ExprKind::A => ExprKind::A,
            ExprKind::B(x) => {
                let m = fm(unsafe { &**k }, unsafe { &**x });
                ExprKind::B(&m)
            }
        },
    }
}
"#;
    const MUTUAL_FIXTURE_PATH: &str = "mutual_fixture.rs";

    // THE LITERAL-CLUSTER fixture — the extraction twin of the combined
    // literal-cluster lane (multi-IH constructors, opaque payload fields,
    // model=reference postconditions; see trust-integration-tests'
    // `mutual_literal_cluster_e2e`). A genuine 2-SCC model cluster {fm, gm}
    // and a 2-SCC reference cluster {fr, gr} over the FULL 5-constructor
    // `level::Level` payload (`Zero | Succ | Max | IMax | Param(Name)` — the
    // def-path-gated full Level slice: Max/IMax carry TWO recursive fields,
    // Param an opaque `name::Name`), fuel-indexed by the def-path-gated
    // `expr::kind::ExprKind` path carrying a nat-shaped `Z | S` slice (the
    // mutual lane's fuel gate is STRUCTURAL, not name-bound, so any gated
    // 2-ctor nat shape indexes it). Model members rebuild per-constructor at
    // fuel Z; reference members return the payload DIRECTLY at fuel Z (which
    // needs `Level: Copy` — methodless lang-item impls below) — two pointwise
    // equal but STRUCTURALLY different folds. `gm_wrong` is the extracted
    // NEGATIVE-control body: identical to `gm` except its IMax step arm
    // rebuilds `Max` — wrong in ONE branch of a two-IH arm.
    //
    // `#[inline(never)]`: fm/gm and fr/gr protect themselves (rustc's MIR
    // inliner refuses SCC-internal inlining) but `gm_wrong -> fm` is NOT in
    // any cycle with `fm`, so without the attribute the inliner may flatten
    // fm's body into gm_wrong and destroy the cluster-call shape.
    //
    // `#![no_core]` + raw-pointer recursive children + address-of-local result
    // payloads, for the same environmental reasons as the mirror/mutual
    // fixtures (the fixture is only ever MIR-extracted, never executed).
    const LITERAL_CLUSTER_FIXTURE_SOURCE: &str = r#"
#![feature(auto_traits, lang_items, no_core)]
#![no_core]
#![allow(dead_code)]

#[lang = "sized"]
pub trait Sized: MetaSized {}

#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}

#[lang = "pointee_sized"]
pub trait PointeeSized {}

#[lang = "copy"]
pub trait Copy: Clone {}

#[lang = "clone"]
pub trait Clone {}

#[lang = "freeze"]
pub unsafe auto trait Freeze {}

// no_core carries NO builtin Copy impls for primitives; the lang-item traits
// here are methodless, so these empty impls are the whole story. They are
// needed so `Name` and `Level` (u64 / raw-pointer fields) can be `Copy` —
// which the REFERENCE members' direct fuel-Z return (`*e`) and the `Param`
// arms' opaque-field copy (`*n`) require.
impl Clone for u64 {}
impl Copy for u64 {}
impl<T> Clone for *const T {}
impl<T> Copy for *const T {}

pub mod name {
    pub struct Name(pub u64);

    impl crate::Clone for Name {}
    impl crate::Copy for Name {}
}

pub mod level {
    use crate::name::Name;

    pub enum Level {
        Zero,
        Succ(*const Level),
        Max(*const Level, *const Level),
        IMax(*const Level, *const Level),
        Param(Name),
    }

    impl crate::Clone for Level {}
    impl crate::Copy for Level {}
}

pub mod expr {
    pub mod kind {
        pub enum ExprKind {
            Z,
            S(*const ExprKind),
        }
    }
}

use expr::kind::ExprKind;
use level::Level;

#[inline(never)]
pub fn fm(fuel: &ExprKind, e: &Level) -> Level {
    match fuel {
        ExprKind::Z => match e {
            Level::Zero => Level::Zero,
            Level::Succ(x) => Level::Succ(unsafe { &**x }),
            Level::Max(a, b) => Level::Max(unsafe { &**a }, unsafe { &**b }),
            Level::IMax(a, b) => Level::IMax(unsafe { &**a }, unsafe { &**b }),
            Level::Param(n) => Level::Param(*n),
        },
        ExprKind::S(k) => match e {
            Level::Zero => Level::Zero,
            Level::Succ(x) => {
                let m = gm(unsafe { &**k }, unsafe { &**x });
                Level::Succ(&m)
            }
            Level::Max(a, b) => {
                let ma = gm(unsafe { &**k }, unsafe { &**a });
                let mb = gm(unsafe { &**k }, unsafe { &**b });
                Level::Max(&ma, &mb)
            }
            Level::IMax(a, b) => {
                let ia = gm(unsafe { &**k }, unsafe { &**a });
                let ib = gm(unsafe { &**k }, unsafe { &**b });
                Level::IMax(&ia, &ib)
            }
            Level::Param(n) => Level::Param(*n),
        },
    }
}

#[inline(never)]
pub fn gm(fuel: &ExprKind, e: &Level) -> Level {
    match fuel {
        ExprKind::Z => match e {
            Level::Zero => Level::Zero,
            Level::Succ(x) => Level::Succ(unsafe { &**x }),
            Level::Max(a, b) => Level::Max(unsafe { &**a }, unsafe { &**b }),
            Level::IMax(a, b) => Level::IMax(unsafe { &**a }, unsafe { &**b }),
            Level::Param(n) => Level::Param(*n),
        },
        ExprKind::S(k) => match e {
            Level::Zero => Level::Zero,
            Level::Succ(x) => {
                let m = fm(unsafe { &**k }, unsafe { &**x });
                Level::Succ(&m)
            }
            Level::Max(a, b) => {
                let ma = fm(unsafe { &**k }, unsafe { &**a });
                let mb = fm(unsafe { &**k }, unsafe { &**b });
                Level::Max(&ma, &mb)
            }
            Level::IMax(a, b) => {
                let ia = fm(unsafe { &**k }, unsafe { &**a });
                let ib = fm(unsafe { &**k }, unsafe { &**b });
                Level::IMax(&ia, &ib)
            }
            Level::Param(n) => Level::Param(*n),
        },
    }
}

#[inline(never)]
pub fn gm_wrong(fuel: &ExprKind, e: &Level) -> Level {
    match fuel {
        ExprKind::Z => match e {
            Level::Zero => Level::Zero,
            Level::Succ(x) => Level::Succ(unsafe { &**x }),
            Level::Max(a, b) => Level::Max(unsafe { &**a }, unsafe { &**b }),
            Level::IMax(a, b) => Level::IMax(unsafe { &**a }, unsafe { &**b }),
            Level::Param(n) => Level::Param(*n),
        },
        ExprKind::S(k) => match e {
            Level::Zero => Level::Zero,
            Level::Succ(x) => {
                let m = fm(unsafe { &**k }, unsafe { &**x });
                Level::Succ(&m)
            }
            Level::Max(a, b) => {
                let ma = fm(unsafe { &**k }, unsafe { &**a });
                let mb = fm(unsafe { &**k }, unsafe { &**b });
                Level::Max(&ma, &mb)
            }
            Level::IMax(a, b) => {
                let ia = fm(unsafe { &**k }, unsafe { &**a });
                let ib = fm(unsafe { &**k }, unsafe { &**b });
                Level::Max(&ia, &ib)
            }
            Level::Param(n) => Level::Param(*n),
        },
    }
}

#[inline(never)]
pub fn fr(fuel: &ExprKind, e: &Level) -> Level {
    match fuel {
        ExprKind::Z => *e,
        ExprKind::S(k) => match e {
            Level::Zero => Level::Zero,
            Level::Succ(x) => {
                let m = gr(unsafe { &**k }, unsafe { &**x });
                Level::Succ(&m)
            }
            Level::Max(a, b) => {
                let ma = gr(unsafe { &**k }, unsafe { &**a });
                let mb = gr(unsafe { &**k }, unsafe { &**b });
                Level::Max(&ma, &mb)
            }
            Level::IMax(a, b) => {
                let ia = gr(unsafe { &**k }, unsafe { &**a });
                let ib = gr(unsafe { &**k }, unsafe { &**b });
                Level::IMax(&ia, &ib)
            }
            Level::Param(n) => Level::Param(*n),
        },
    }
}

#[inline(never)]
pub fn gr(fuel: &ExprKind, e: &Level) -> Level {
    match fuel {
        ExprKind::Z => *e,
        ExprKind::S(k) => match e {
            Level::Zero => Level::Zero,
            Level::Succ(x) => {
                let m = fr(unsafe { &**k }, unsafe { &**x });
                Level::Succ(&m)
            }
            Level::Max(a, b) => {
                let ma = fr(unsafe { &**k }, unsafe { &**a });
                let mb = fr(unsafe { &**k }, unsafe { &**b });
                Level::Max(&ma, &mb)
            }
            Level::IMax(a, b) => {
                let ia = fr(unsafe { &**k }, unsafe { &**a });
                let ib = fr(unsafe { &**k }, unsafe { &**b });
                Level::IMax(&ia, &ib)
            }
            Level::Param(n) => Level::Param(*n),
        },
    }
}
"#;
    const LITERAL_CLUSTER_FIXTURE_PATH: &str = "literal_cluster_fixture.rs";

    // THE CELL-COUNTER fixture — the INTERIOR-MUTABILITY extraction-gap
    // prototype (the heartbeat `Cell<u32>` residual). A genuine 2-SCC model
    // cluster {fm, gm} whose budget lives in an interior-mutable cell on a
    // `&Tc` parameter (the literal `TypeChecker` discipline: read the counter
    // at entry, fail-closed exhaustion on `Z`, write the decremented counter
    // back, call the sibling THROUGH the same `&Tc` — the remainder is never
    // passed or returned, it lives in the cell), plus the hand-THREADED
    // reference 2-SCC {fr, gr} in exactly the `threaded_budget_functional`
    // lane shape (`(&Fuel, &E) -> Res` with `Res = Mk(Fuel, E)`).
    //
    // The interior mutability is the REAL mechanism: a `#[lang = "unsafe_cell"]`
    // struct (the same lang item `core::cell::Cell` is built on) wrapped by
    // `FuelCell` with `#[inline(never)]` accessor fns `cell_get`/`cell_set` —
    // the accessor-CALL recognition mirrors how the real `Cell::<u32>::get/set`
    // std fns would be recognized by def-path. `&self` is modeled as the
    // explicit `tc: &Tc` first parameter (identical MIR: `self` IS `_1`).
    //
    // `fm_leak` is the fail-closed NEGATIVE control: it passes `tc` to a
    // function outside the recognized accessor/cluster-call grammar (an escape
    // through which the cell could be mutated), so `thread_cell_state` must
    // refuse it.
    //
    // `#![no_core]` + raw-pointer recursive children + address-of-local result
    // payloads, for the same environmental reasons as the mirror/mutual/
    // literal-cluster fixtures (the fixture is only ever MIR-extracted, never
    // executed).
    const CELL_COUNTER_FIXTURE_SOURCE: &str = r#"
#![feature(auto_traits, lang_items, no_core)]
#![no_core]
#![allow(dead_code)]

#[lang = "sized"]
pub trait Sized: MetaSized {}

#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}

#[lang = "pointee_sized"]
pub trait PointeeSized {}

#[lang = "copy"]
pub trait Copy: Clone {}

#[lang = "clone"]
pub trait Clone {}

#[lang = "freeze"]
pub unsafe auto trait Freeze {}

// The REAL interior-mutability mechanism: the same lang item `core::cell`
// is built on. `FuelCell` plays `Cell<u32>` (the heartbeat counter), with the
// nat-shaped `Fuel` standing in for the numeric budget (the fuel lanes'
// standing u32-as-nat modeling step).
#[lang = "unsafe_cell"]
#[repr(transparent)]
pub struct UnsafeCell<T> {
    value: T,
}

impl<T> Clone for *const T {}
impl<T> Copy for *const T {}

pub mod fuel {
    pub enum Fuel {
        Z,
        S(*const Fuel),
    }

    impl crate::Clone for Fuel {}
    impl crate::Copy for Fuel {}
}

pub mod expr {
    pub enum E {
        A,
        B(*const E),
        M(*const E, *const E),
    }

    impl crate::Clone for E {}
    impl crate::Copy for E {}
}

pub mod res {
    use crate::expr::E;
    use crate::fuel::Fuel;

    pub enum Res {
        Mk(Fuel, E),
    }
}

use expr::E;
use fuel::Fuel;
use res::Res;

pub struct FuelCell {
    value: UnsafeCell<*const Fuel>,
}

pub struct Tc {
    pub heartbeat: FuelCell,
}

#[inline(never)]
pub fn cell_get(c: &FuelCell) -> *const Fuel {
    unsafe { *(&c.value as *const UnsafeCell<*const Fuel> as *const *const Fuel) }
}

// `allow(invalid_reference_casting)`: the write really is through the
// `#[lang = "unsafe_cell"]` wrapper (defined behavior — the same cast
// `core::cell::UnsafeCell::get` performs); the lint's heuristic just does not
// recognize the hand-rolled no_core spelling.
#[allow(invalid_reference_casting)]
#[inline(never)]
pub fn cell_set(c: &FuelCell, v: *const Fuel) {
    unsafe {
        *(&c.value as *const UnsafeCell<*const Fuel> as *mut *const Fuel) = v;
    }
}

// ── The MODEL cluster: budget in the cell, never in the signature ────────────

#[inline(never)]
pub fn fm(tc: &Tc, e: &E) -> E {
    match unsafe { &*cell_get(&tc.heartbeat) } {
        Fuel::Z => *e,
        Fuel::S(k) => {
            cell_set(&tc.heartbeat, *k);
            match e {
                E::A => E::A,
                E::B(x) => {
                    let r = gm(tc, unsafe { &**x });
                    E::B(&r)
                }
                E::M(x, y) => {
                    let r1 = gm(tc, unsafe { &**x });
                    let r2 = gm(tc, unsafe { &**y });
                    E::M(&r1, &r2)
                }
            }
        }
    }
}

#[inline(never)]
pub fn gm(tc: &Tc, e: &E) -> E {
    match unsafe { &*cell_get(&tc.heartbeat) } {
        Fuel::Z => *e,
        Fuel::S(k) => {
            cell_set(&tc.heartbeat, *k);
            match e {
                E::A => E::A,
                E::B(x) => {
                    let r = fm(tc, unsafe { &**x });
                    E::B(&r)
                }
                E::M(x, y) => {
                    let r1 = fm(tc, unsafe { &**x });
                    let r2 = fm(tc, unsafe { &**y });
                    E::M(&r1, &r2)
                }
            }
        }
    }
}

// ── The NEGATIVE control: `tc` ESCAPES the accessor/cluster-call grammar ─────

#[inline(never)]
pub fn leak(_tc: &Tc) {}

#[inline(never)]
pub fn fm_leak(tc: &Tc, e: &E) -> E {
    let _p = cell_get(&tc.heartbeat);
    leak(tc);
    *e
}

// ── The hand-THREADED reference cluster (already in the lane shape) ──────────

#[inline(never)]
pub fn fr(fuel: &Fuel, e: &E) -> Res {
    match fuel {
        // `*fuel` (the exhausted input, which IS `Z` in this arm) rather than a
        // fresh `Fuel::Z`: a constructed fieldless variant inside an aggregate
        // argument gets const-promoted to an opaque constant at
        // -Zmir-opt-level=3, which the threaded lane's symbolic walk cannot
        // resolve; the runtime copy of the matched-on param resolves under the
        // Z branch.
        Fuel::Z => Res::Mk(*fuel, *e),
        Fuel::S(k) => match e {
            E::A => Res::Mk(unsafe { **k }, E::A),
            E::B(x) => {
                let r = gr(unsafe { &**k }, unsafe { &**x });
                let Res::Mk(rf, rv) = r;
                Res::Mk(rf, E::B(&rv))
            }
            E::M(x, y) => {
                let r1 = gr(unsafe { &**k }, unsafe { &**x });
                let Res::Mk(r1f, r1v) = r1;
                let r2 = gr(&r1f, unsafe { &**y });
                let Res::Mk(r2f, r2v) = r2;
                Res::Mk(r2f, E::M(&r1v, &r2v))
            }
        },
    }
}

#[inline(never)]
pub fn gr(fuel: &Fuel, e: &E) -> Res {
    match fuel {
        Fuel::Z => Res::Mk(*fuel, *e),
        Fuel::S(k) => match e {
            E::A => Res::Mk(unsafe { **k }, E::A),
            E::B(x) => {
                let r = fr(unsafe { &**k }, unsafe { &**x });
                let Res::Mk(rf, rv) = r;
                Res::Mk(rf, E::B(&rv))
            }
            E::M(x, y) => {
                let r1 = fr(unsafe { &**k }, unsafe { &**x });
                let Res::Mk(r1f, r1v) = r1;
                let r2 = fr(&r1f, unsafe { &**y });
                let Res::Mk(r2f, r2v) = r2;
                Res::Mk(r2f, E::M(&r1v, &r2v))
            }
        },
    }
}
"#;
    const CELL_COUNTER_FIXTURE_PATH: &str = "cell_counter_fixture.rs";

    struct InMemoryContractFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryContractFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(CONTRACT_FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(CONTRACT_FIXTURE_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected contract fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in contract tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    struct InMemoryCallTargetFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryCallTargetFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(CALL_TARGET_FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(CALL_TARGET_FIXTURE_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected call target fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in call-target tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    struct InMemoryCodegenFidelityFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryCodegenFidelityFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(CODEGEN_FIDELITY_FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(CODEGEN_FIDELITY_FIXTURE_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected codegen-fidelity fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in codegen-fidelity tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    struct InMemoryOptionReturnFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryOptionReturnFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(OPTION_RETURN_FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(OPTION_RETURN_FIXTURE_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected option return fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in option return tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    struct InMemoryLevelFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryLevelFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(LEVEL_FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(LEVEL_FIXTURE_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected level fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in level tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    struct InMemoryExprFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryExprFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(EXPR_FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(EXPR_FIXTURE_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected expr fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in expr tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    struct InMemoryMirrorFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryMirrorFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(MIRROR_FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(MIRROR_FIXTURE_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected mirror fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in mirror tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    struct InMemoryMutualFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryMutualFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(MUTUAL_FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(MUTUAL_FIXTURE_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected mutual fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in mutual tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    struct InMemoryLiteralClusterFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryLiteralClusterFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(LITERAL_CLUSTER_FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(LITERAL_CLUSTER_FIXTURE_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected literal-cluster fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in literal-cluster tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    struct InMemoryCellCounterFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryCellCounterFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(CELL_COUNTER_FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(CELL_COUNTER_FIXTURE_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected cell-counter fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in cell-counter tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    struct LevelExtractionCallbacks {
        level_ty: Option<Ty>,
        /// Diagnostic: every nominal-ADT type seen while scanning, so a miss
        /// surfaces the actual def paths instead of an opaque `None`.
        probe: Vec<String>,
    }

    /// Lever A step 5 — extracts BOTH the `Expr` struct and the `ExprKind` enum
    /// datatype from one compile of the expr fixture (mirrors `LevelExtractionCallbacks`).
    struct ExprExtractionCallbacks {
        exprkind_ty: Option<Ty>,
        expr_ty: Option<Ty>,
        /// Diagnostic: every nominal-ADT type seen while scanning.
        probe: Vec<String>,
    }

    impl rustc_driver::Callbacks for ExprExtractionCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryExprFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();
            for def_id in tcx.hir_body_owners() {
                let did = def_id.to_def_id();
                if !matches!(tcx.def_kind(did), rustc_hir::def::DefKind::Fn) {
                    continue;
                }
                let body = tcx.optimized_mir(did);
                for local in &body.local_decls {
                    if let rustc_middle::ty::TyKind::Adt(adt_def, _) = local.ty.kind() {
                        let path = safe_def_path_str(tcx, adt_def.did());
                        self.probe.push(path.clone());
                        // Local-crate defs render WITHOUT the crate-name prefix; an
                        // upstream dependency would render with it. Accept either,
                        // and match EXACTLY (no suffix) so `expr::Expr` and
                        // `expr::kind::ExprKind` never cross-classify.
                        // Trust: M6 rung-7 sweep — `body` is a real compiled MIR body, so
                        // use its own `typing_env` (matching `extract_body`'s locals)
                        // instead of the plain env-less `convert_ty`. These extraction
                        // helpers scan the SAME `Expr`/`ExprKind` recursive-ADT family
                        // rung-7 diagnosed the closure-capture divergence on; the current
                        // `#![no_core]` fixture (no aliases) never exercises the gap, but
                        // this closes it by construction for any future fixture that does.
                        if matches!(
                            path.as_str(),
                            "expr::kind::ExprKind" | "clean_kernel::expr::kind::ExprKind"
                        ) && self.exprkind_ty.is_none()
                        {
                            self.exprkind_ty = Some(ty_convert::convert_ty_in_env(
                                tcx,
                                body.typing_env(tcx),
                                local.ty,
                            ));
                        }
                        if matches!(path.as_str(), "expr::Expr" | "clean_kernel::expr::Expr")
                            && self.expr_ty.is_none()
                        {
                            self.expr_ty = Some(ty_convert::convert_ty_in_env(
                                tcx,
                                body.typing_env(tcx),
                                local.ty,
                            ));
                        }
                    }
                }
            }
            Compilation::Stop
        }
    }

    impl rustc_driver::Callbacks for LevelExtractionCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryLevelFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();
            // Look at EVERY nominal-ADT definition in the crate directly (an enum
            // inside `mod level` is not a crate-root free item, so a MIR-local scan
            // can miss it). `hir_body_owners` + `optimized_mir` locals are scanned
            // too as a fallback / to mirror the real extraction path.
            for def_id in tcx.hir_body_owners() {
                let did = def_id.to_def_id();
                if !matches!(tcx.def_kind(did), rustc_hir::def::DefKind::Fn) {
                    continue;
                }
                let body = tcx.optimized_mir(did);
                for local in &body.local_decls {
                    if let rustc_middle::ty::TyKind::Adt(adt_def, _) = local.ty.kind() {
                        let path = safe_def_path_str(tcx, adt_def.did());
                        self.probe.push(path.clone());
                        // Local-crate defs render WITHOUT the crate-name prefix
                        // (`level::Level`); an upstream dependency would render
                        // `clean_kernel::level::Level`. Accept either.
                        let is_level =
                            matches!(path.as_str(), "level::Level" | "clean_kernel::level::Level");
                        // Trust: M6 rung-7 sweep — use `body`'s own `typing_env`, same as
                        // the `ExprExtractionCallbacks` fix above.
                        if is_level && self.level_ty.is_none() {
                            self.level_ty = Some(ty_convert::convert_ty_in_env(
                                tcx,
                                body.typing_env(tcx),
                                local.ty,
                            ));
                        }
                    }
                }
            }
            Compilation::Stop
        }
    }

    struct ContractExtractionCallbacks {
        functions: BTreeMap<String, VerifiableFunction>,
        metadata: BTreeMap<String, TrustMetadata>,
        empty_bundle_metadata: BTreeMap<String, TrustMetadata>,
        conversion_fixture: Option<ContractConversionFixture>,
        query_contracts: Option<CompilerContractBundle>,
    }

    impl rustc_driver::Callbacks for ContractExtractionCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryContractFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();

            for item_id in tcx.hir_free_items() {
                let item = tcx.hir_item(item_id);
                if let rustc_hir::ItemKind::Fn { ident, .. } = item.kind {
                    let def_id = item.owner_id.def_id.to_def_id();
                    let body = tcx.optimized_mir(def_id);
                    let name = ident.name.to_string();
                    // Mirror the production verifier path: built-in contract
                    // attributes are consumed by rustc and arrive at extraction
                    // through the typed `trust_contracts` query bundle. A bare
                    // `extract_function(..., None)` cannot and must not recover
                    // them from source text.
                    let compiler_contracts =
                        convert_trust_contract_bundle(tcx, tcx.trust_contracts(def_id))
                            .expect("rustc query payload should convert for fixture functions");
                    self.metadata.insert(
                        name.clone(),
                        extract_metadata_with_contract_bundle(tcx, body, Some(&compiler_contracts)),
                    );
                    self.empty_bundle_metadata.insert(
                        name.clone(),
                        extract_metadata_with_contract_bundle(
                            tcx,
                            body,
                            Some(&CompilerContractBundle::default()),
                        ),
                    );
                    self.functions.insert(
                        name.clone(),
                        extract_function_with_contract_bundle(tcx, body, Some(&compiler_contracts)),
                    );
                    if name == "no_contracts" && self.conversion_fixture.is_none() {
                        self.conversion_fixture =
                            Some(build_contract_conversion_fixture(tcx, def_id));
                    }
                    if name == "reciprocal" && self.query_contracts.is_none() {
                        self.query_contracts = Some(compiler_contracts);
                    }
                }
            }

            Compilation::Stop
        }
    }

    #[derive(Debug, Default)]
    struct CallTargetFixture {
        functions: BTreeMap<String, VerifiableFunction>,
        direct_call_symbols: BTreeMap<String, Vec<String>>,
        direct_call_func_types: BTreeMap<String, Vec<Ty>>,
        canonical_def_paths: Vec<String>,
        crate_def_path: String,
    }

    struct CallTargetCallbacks {
        fixture: CallTargetFixture,
    }

    #[derive(Debug, Default)]
    struct CodegenFidelityFixture {
        verifier: BTreeMap<String, VerifiableFunction>,
        raw_codegen: BTreeMap<String, VerifiableFunction>,
        codegen: BTreeMap<String, Result<VerifiableFunction, CodegenExtractionError>>,
    }

    struct CodegenFidelityCallbacks {
        fixture: CodegenFidelityFixture,
    }

    struct OptionReturnCallbacks {
        function: Option<VerifiableFunction>,
    }

    impl rustc_driver::Callbacks for CallTargetCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryCallTargetFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();

            for item_id in tcx.hir_free_items() {
                let item = tcx.hir_item(item_id);
                if let rustc_hir::ItemKind::Fn { ident, .. } = item.kind {
                    let fn_name = ident.name.to_string();
                    let def_id = item.owner_id.def_id.to_def_id();
                    let body = tcx.optimized_mir(def_id);
                    self.fixture.canonical_def_paths.push(safe_def_path_str(tcx, def_id));
                    self.fixture.functions.insert(fn_name.clone(), extract_function(tcx, body));
                    self.fixture
                        .direct_call_symbols
                        .insert(fn_name.clone(), direct_call_symbol_names(tcx, body));
                    self.fixture
                        .direct_call_func_types
                        .insert(fn_name, direct_call_func_types(tcx, body));
                }
            }
            self.fixture.crate_def_path =
                safe_def_path_str(tcx, rustc_span::def_id::CRATE_DEF_ID.to_def_id());

            Compilation::Stop
        }
    }

    impl rustc_driver::Callbacks for CodegenFidelityCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryCodegenFidelityFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();

            for def_id in tcx.hir_body_owners() {
                let did = def_id.to_def_id();
                let path = safe_def_path_str(tcx, did);
                // Local def paths may omit the crate-name prefix (for example,
                // `identity` rather than `fixture::identity`). Classify by the
                // exact final segment while retaining the enclosing-path check
                // for the generated Clone implementation.
                let leaf = path.rsplit("::").next().unwrap_or(path.as_str());
                let key = if leaf == "identity" {
                    Some("identity")
                } else if leaf == "clone_derived" {
                    Some("clone_derived")
                } else if leaf == "exit_now" {
                    Some("exit_now")
                } else if leaf == "calls_may_panic" {
                    Some("calls_may_panic")
                } else if leaf == "checked_add" {
                    Some("checked_add")
                } else if leaf == "opaque_bytes" {
                    Some("opaque_bytes")
                } else if leaf == "spawn_with_literal_name" {
                    Some("spawn_with_literal_name")
                } else if leaf == "drop_os_error" {
                    Some("drop_os_error")
                } else if leaf == "clone" && path.contains("Derived") {
                    Some("derived_clone_impl")
                } else {
                    None
                };
                let Some(key) = key else { continue };
                let body = tcx.optimized_mir(did);
                self.fixture.verifier.insert(key.to_string(), extract_function(tcx, body));
                self.fixture.raw_codegen.insert(
                    key.to_string(),
                    extract_function_with_purpose(tcx, body, None, ExtractionPurpose::Codegen),
                );
                self.fixture
                    .codegen
                    .insert(key.to_string(), extract_function_for_codegen(tcx, body));
            }

            Compilation::Stop
        }
    }

    impl rustc_driver::Callbacks for OptionReturnCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryOptionReturnFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();

            for item_id in tcx.hir_free_items() {
                let item = tcx.hir_item(item_id);
                if let rustc_hir::ItemKind::Fn { ident, .. } = item.kind {
                    if ident.name.as_str() == "option_value" {
                        let body = tcx.optimized_mir(item.owner_id.def_id.to_def_id());
                        self.function = Some(extract_function(tcx, body));
                        break;
                    }
                }
            }

            Compilation::Stop
        }
    }

    /// Lever A step 3 (real MIR body): extract EVERY free function of the Expr
    /// fixture into a `VerifiableFunction`, so a test can inspect the actual MIR
    /// body a datatype-construction function lowers to (the input that
    /// `trust-vcgen`'s datatype-functional VC-gen consumes).
    struct ExprBodyCallbacks {
        functions: BTreeMap<String, VerifiableFunction>,
    }

    impl rustc_driver::Callbacks for ExprBodyCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryExprFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();
            for item_id in tcx.hir_free_items() {
                let item = tcx.hir_item(item_id);
                if let rustc_hir::ItemKind::Fn { ident, .. } = item.kind {
                    let body = tcx.optimized_mir(item.owner_id.def_id.to_def_id());
                    self.functions.insert(ident.name.to_string(), extract_function(tcx, body));
                }
            }
            Compilation::Stop
        }
    }

    /// WALL C — extracts every free function of the mirror fixture (the
    /// self-recursive `mirror : &Level -> Level`) into a `VerifiableFunction`
    /// (mirrors `ExprBodyCallbacks`).
    struct MirrorBodyCallbacks {
        functions: BTreeMap<String, VerifiableFunction>,
    }

    impl rustc_driver::Callbacks for MirrorBodyCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryMirrorFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();
            for item_id in tcx.hir_free_items() {
                let item = tcx.hir_item(item_id);
                if let rustc_hir::ItemKind::Fn { ident, .. } = item.kind {
                    let body = tcx.optimized_mir(item.owner_id.def_id.to_def_id());
                    self.functions.insert(ident.name.to_string(), extract_function(tcx, body));
                }
            }
            Compilation::Stop
        }
    }

    /// WALL C scaled to MUTUAL SCCs — extracts every free function of the
    /// mutual ring fixture (`fm -> gm -> hm -> fm`) into `VerifiableFunction`s
    /// (mirrors `MirrorBodyCallbacks`).
    struct MutualBodyCallbacks {
        functions: BTreeMap<String, VerifiableFunction>,
    }

    impl rustc_driver::Callbacks for MutualBodyCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryMutualFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();
            for item_id in tcx.hir_free_items() {
                let item = tcx.hir_item(item_id);
                if let rustc_hir::ItemKind::Fn { ident, .. } = item.kind {
                    let body = tcx.optimized_mir(item.owner_id.def_id.to_def_id());
                    self.functions.insert(ident.name.to_string(), extract_function(tcx, body));
                }
            }
            Compilation::Stop
        }
    }

    /// EXTRACTION SERIALIZATION — extracts every free function of the
    /// literal-cluster fixture (model {fm, gm} + negative `gm_wrong` +
    /// reference {fr, gr} over the FULL 5-ctor Level) into
    /// `VerifiableFunction`s (mirrors `MutualBodyCallbacks`).
    struct LiteralClusterBodyCallbacks {
        functions: BTreeMap<String, VerifiableFunction>,
    }

    impl rustc_driver::Callbacks for LiteralClusterBodyCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryLiteralClusterFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();
            for item_id in tcx.hir_free_items() {
                let item = tcx.hir_item(item_id);
                if let rustc_hir::ItemKind::Fn { ident, .. } = item.kind {
                    let body = tcx.optimized_mir(item.owner_id.def_id.to_def_id());
                    self.functions.insert(ident.name.to_string(), extract_function(tcx, body));
                }
            }
            Compilation::Stop
        }
    }

    /// INTERIOR-MUTABILITY GAP — extracts every free function of the
    /// cell-counter fixture (cell accessors + cell-mediated model {fm, gm} +
    /// negative `fm_leak` + hand-threaded reference {fr, gr}) into
    /// `VerifiableFunction`s (mirrors `LiteralClusterBodyCallbacks`).
    struct CellCounterBodyCallbacks {
        functions: BTreeMap<String, VerifiableFunction>,
    }

    impl rustc_driver::Callbacks for CellCounterBodyCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryCellCounterFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();
            for item_id in tcx.hir_free_items() {
                let item = tcx.hir_item(item_id);
                if let rustc_hir::ItemKind::Fn { ident, .. } = item.kind {
                    let body = tcx.optimized_mir(item.owner_id.def_id.to_def_id());
                    self.functions.insert(ident.name.to_string(), extract_function(tcx, body));
                }
            }
            Compilation::Stop
        }
    }

    fn compiler_sysroot() -> String {
        // Bootstrap exports RUSTC_SYSROOT for the compiler BUILD, which can be
        // stage0-sysroot even while this stage1 test binary embeds a newer
        // rustc_driver.  Treat that ambient value as a last-resort candidate,
        // and validate every override before handing it to an in-process
        // compiler.  TRUST_TEST_SYSROOT is the unambiguous fixture-only escape
        // hatch; TEST_SYSROOT retains bootstrap/Cargo compatibility.
        std::env::var("TRUST_TEST_SYSROOT")
            .ok()
            .and_then(validated_trust_sysroot)
            .or_else(|| std::env::var("TEST_SYSROOT").ok().and_then(validated_trust_sysroot))
            .or_else(|| {
                option_env!("TEST_SYSROOT").map(str::to_owned).and_then(validated_trust_sysroot)
            })
            .or_else(local_trust_sysroot)
            .or_else(|| std::env::var("RUSTC_SYSROOT").ok().and_then(validated_trust_sysroot))
            .or_else(|| std::env::var("SYSROOT").ok().and_then(validated_trust_sysroot))
            .unwrap_or_else(|| {
                panic!(
                    "trust-mir-extract direct fixtures require a local Trust sysroot; \
                     set TRUST_TEST_SYSROOT/TEST_SYSROOT to a sysroot containing \
                     bin/trustc plus host core/std, or build stage1/stage2 at \
                     build/<host>. Invalid ambient RUSTC_SYSROOT/SYSROOT values \
                     are rejected rather than mixing compiler versions."
                )
            })
    }

    fn validated_trust_sysroot(candidate: String) -> Option<String> {
        let candidate = PathBuf::from(candidate);
        is_local_trust_sysroot(&candidate)
            .then(|| candidate.canonicalize().unwrap_or(candidate).to_string_lossy().into_owned())
    }

    fn local_trust_sysroot() -> Option<String> {
        let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
        let repo_root = manifest_dir.parent()?.parent()?;
        let mut build_roots = vec![repo_root.join("build/host")];

        if let Ok(host) = std::env::var("CFG_COMPILER_HOST_TRIPLE") {
            build_roots.push(repo_root.join("build").join(host));
        }
        for host in [
            "aarch64-unknown-linux-gnu",
            "aarch64-apple-darwin",
            "x86_64-apple-darwin",
            "x86_64-unknown-linux-gnu",
        ] {
            build_roots.push(repo_root.join("build").join(host));
        }

        let candidates = build_roots
            .into_iter()
            .flat_map(|root| ["stage2", "stage1"].map(move |stage| root.join(stage)));

        candidates
            .into_iter()
            .find_map(|candidate| validated_trust_sysroot(candidate.to_string_lossy().into_owned()))
    }

    fn is_local_trust_sysroot(candidate: &Path) -> bool {
        candidate.join("bin/trustc").is_file()
            && sysroot_has_host_std(candidate)
            && sysroot_compiler_matches_driver(candidate)
    }

    /// The in-process `rustc_driver` linked into this test binary must match the
    /// compiler that built the candidate sysroot's `std`/`core`, or metadata
    /// load fails with E0514 ("found crate `std` compiled by an incompatible
    /// version of rustc"), cascading into a broken prelude and surfacing as the
    /// generic, misleading `failed to compile contract fixture` panic. When a
    /// version-skewed sysroot survives the structural check (e.g. `stage2` is a
    /// build behind `stage1` after an interrupted rebuild), skip it so
    /// resolution falls through to a matching candidate — or to the explicit
    /// no-sysroot diagnostic — instead of handing the driver a mismatched std.
    ///
    /// LENIENT by construction: it only ever REJECTS on a proven version
    /// mismatch. If the driver's own version is unknown, or the candidate's
    /// `trustc --version` cannot be queried or does not parse, the prior
    /// structural acceptance stands — a robustness gate must never turn a valid
    /// sysroot away.
    fn sysroot_compiler_matches_driver(candidate: &Path) -> bool {
        let Some(driver_version) = rustc_interface::util::rustc_version_str() else {
            return true;
        };
        let driver_version = driver_version.trim();
        if driver_version.is_empty() {
            return true;
        }
        let Ok(output) =
            std::process::Command::new(candidate.join("bin/trustc")).arg("--version").output()
        else {
            return true;
        };
        if !output.status.success() {
            return true;
        }
        // The candidate compiler built this sysroot's std, so its `--version`
        // line embeds the exact identity `rustc_version_str()` reports (e.g.
        // `1.99.0-dev (2513b19da 2026-07-21)`). A substring match tolerates the
        // surrounding `rustc … (trustc)` framing without depending on its shape.
        String::from_utf8_lossy(&output.stdout).contains(driver_version)
    }

    fn sysroot_has_host_std(candidate: &Path) -> bool {
        let Ok(entries) = candidate.join("lib/rustlib").read_dir() else {
            return false;
        };

        entries.flatten().any(|entry| {
            let lib_dir = entry.path().join("lib");
            has_rmeta(&lib_dir, "libcore-") && has_rmeta(&lib_dir, "libstd-")
        })
    }

    fn has_rmeta(lib_dir: &Path, prefix: &str) -> bool {
        let Ok(entries) = lib_dir.read_dir() else {
            return false;
        };

        entries.flatten().any(|entry| {
            let file_name = entry.file_name();
            let file_name = file_name.to_string_lossy();
            file_name.starts_with(prefix) && file_name.ends_with(".rmeta")
        })
    }

    #[derive(Debug, Default)]
    struct ContractFixture {
        functions: BTreeMap<String, VerifiableFunction>,
        metadata: BTreeMap<String, TrustMetadata>,
        empty_bundle_metadata: BTreeMap<String, TrustMetadata>,
        conversion: ContractConversionFixture,
        query_contracts: Option<CompilerContractBundle>,
    }

    #[derive(Debug, Default)]
    struct ContractConversionFixture {
        supported: CompilerContractBundle,
        unsupported: CompilerContractBundle,
        empty: CompilerContractBundle,
        mir_local_error: Option<TrustContractBundleConversionError>,
        unsupported_kind_error: Option<TrustContractBundleConversionError>,
        nonconvertible_error: Option<TrustContractBundleConversionError>,
        loop_only: CompilerContractBundle,
        mixed_loop: CompilerContractBundle,
        mixed_loop_caller_fallback: (Vec<Formula>, Vec<Formula>),
        loop_only_len: usize,
        loop_only_iter_count: usize,
        loop_only_is_empty: bool,
    }

    fn build_contract_conversion_fixture<'tcx>(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
    ) -> ContractConversionFixture {
        let mut supported = TrustContractBundle::empty(def_id);
        push_synthetic_contract(
            tcx,
            &mut supported,
            TrustContractKind::Requires,
            TrustContractSubject::Function,
            TrustContractPredicateKind::Opaque { text: sym::trust_test_contract_x_gt_zero },
        );
        push_synthetic_contract(
            tcx,
            &mut supported,
            TrustContractKind::Ensures,
            TrustContractSubject::Function,
            TrustContractPredicateKind::BoolLiteral { value: true },
        );
        refresh_synthetic_summary(&mut supported);

        let empty = TrustContractBundle::empty(def_id);

        let mut unsupported = TrustContractBundle::empty(def_id);
        push_synthetic_contract(
            tcx,
            &mut unsupported,
            TrustContractKind::Requires,
            TrustContractSubject::Function,
            TrustContractPredicateKind::Unsupported {
                reason: sym::trust_test_contract_not_lowered,
            },
        );
        refresh_synthetic_summary(&mut unsupported);

        let mut mir_local = TrustContractBundle::empty(def_id);
        push_synthetic_contract(
            tcx,
            &mut mir_local,
            TrustContractKind::Requires,
            TrustContractSubject::Function,
            TrustContractPredicateKind::MirLocal { local: mir::Local::from_usize(1) },
        );
        refresh_synthetic_summary(&mut mir_local);

        let mut unsupported_kind = TrustContractBundle::empty(def_id);
        push_synthetic_contract(
            tcx,
            &mut unsupported_kind,
            TrustContractKind::Invariant,
            TrustContractSubject::Function,
            TrustContractPredicateKind::Opaque { text: sym::trust_test_contract_x_gt_zero },
        );
        refresh_synthetic_summary(&mut unsupported_kind);

        let mut nonconvertible = TrustContractBundle::empty(def_id);
        nonconvertible.summary.total = 1;

        let mut loop_only = TrustContractBundle::empty(def_id);
        push_synthetic_loop_contract(
            tcx,
            &mut loop_only,
            TrustContractKind::LoopInvariant,
            TrustLoopId { index: 0 },
        );
        push_synthetic_loop_contract(
            tcx,
            &mut loop_only,
            TrustContractKind::Decreases,
            TrustLoopId { index: 0 },
        );
        refresh_synthetic_summary(&mut loop_only);
        let loop_only_len = loop_only.len();
        let loop_only_iter_count = loop_only.iter_all().count();
        let loop_only_is_empty = loop_only.is_empty();

        let mut mixed_loop = supported.clone();
        push_synthetic_loop_contract(
            tcx,
            &mut mixed_loop,
            TrustContractKind::LoopInvariant,
            TrustLoopId { index: 0 },
        );
        refresh_synthetic_summary(&mut mixed_loop);
        let mixed_loop_caller_fallback =
            fail_closed_caller_formulas_for_conversion_error(&mixed_loop);
        ContractConversionFixture {
            supported: convert_trust_contract_bundle(tcx, &supported)
                .expect("supported synthetic bundle should convert"),
            unsupported: convert_trust_contract_bundle(tcx, &unsupported)
                .expect("unsupported predicate should be preserved for verifier API lowering"),
            empty: convert_trust_contract_bundle(tcx, &empty)
                .expect("empty synthetic bundle should convert"),
            mir_local_error: Some(
                convert_trust_contract_bundle(tcx, &mir_local)
                    .expect_err("MIR local predicate should fail closed"),
            ),
            unsupported_kind_error: Some(
                convert_trust_contract_bundle(tcx, &unsupported_kind)
                    .expect_err("unsupported kind should fail closed"),
            ),
            nonconvertible_error: Some(
                convert_trust_contract_bundle(tcx, &nonconvertible)
                    .expect_err("non-empty summary without entries should fail closed"),
            ),
            loop_only: convert_trust_contract_bundle(tcx, &loop_only)
                .expect("loop-only bundle should retain every authored loop clause"),
            mixed_loop: convert_trust_contract_bundle(tcx, &mixed_loop)
                .expect("mixed bundle should retain function and loop lanes"),
            mixed_loop_caller_fallback,
            loop_only_len,
            loop_only_iter_count,
            loop_only_is_empty,
        }
    }

    fn push_synthetic_contract<'tcx>(
        tcx: TyCtxt<'tcx>,
        bundle: &mut TrustContractBundle<'tcx>,
        kind: TrustContractKind,
        subject: TrustContractSubject,
        predicate_kind: TrustContractPredicateKind,
    ) {
        bundle.contracts.push(TrustContract {
            kind,
            source: TrustContractSource::Attribute,
            subject,
            citation: None,
            predicate: TrustContractPredicate {
                ty: TrustContractPayloadType::Rust(tcx.types.bool),
                kind: predicate_kind,
            },
            span: DUMMY_SP,
            keyword_span: None,
        });
    }

    fn push_synthetic_loop_contract<'tcx>(
        _tcx: TyCtxt<'tcx>,
        bundle: &mut TrustContractBundle<'tcx>,
        kind: TrustContractKind,
        id: TrustLoopId,
    ) {
        bundle.loop_contracts.push(TrustContract {
            kind,
            source: TrustContractSource::Native,
            subject: TrustContractSubject::HirLoop {
                id,
                loop_span: DUMMY_SP,
                header_span: DUMMY_SP,
            },
            citation: None,
            predicate: TrustContractPredicate {
                ty: TrustContractPayloadType::Verifier(if kind == TrustContractKind::Decreases {
                    TrustContractVerifierSort::Int
                } else {
                    TrustContractVerifierSort::Bool
                }),
                kind: TrustContractPredicateKind::Unsupported {
                    reason: sym::trust_test_contract_not_lowered,
                },
            },
            span: DUMMY_SP,
            keyword_span: Some(DUMMY_SP),
        });
    }

    fn refresh_synthetic_summary(bundle: &mut TrustContractBundle<'_>) {
        let mut summary = TrustContractSummary::default();
        summary.total = bundle.len() as u32;
        for contract in bundle.iter_all() {
            match contract.kind {
                TrustContractKind::Requires => summary.requires += 1,
                TrustContractKind::Ensures => summary.ensures += 1,
                TrustContractKind::Invariant | TrustContractKind::LoopInvariant => {
                    summary.invariants += 1;
                }
                TrustContractKind::Decreases => summary.decreases += 1,
                TrustContractKind::Asserts => summary.assertions += 1,
                TrustContractKind::Assumes
                | TrustContractKind::Refinement
                | TrustContractKind::Temporal => {}
            }
            if matches!(
                &contract.predicate.kind,
                TrustContractPredicateKind::Opaque { .. }
                    | TrustContractPredicateKind::Unsupported { .. }
            ) {
                summary.opaque += 1;
            }
        }
        bundle.summary = summary;
    }

    fn extract_contract_fixture() -> ContractFixture {
        let mut callbacks = ContractExtractionCallbacks {
            functions: BTreeMap::new(),
            metadata: BTreeMap::new(),
            empty_bundle_metadata: BTreeMap::new(),
            conversion_fixture: None,
            query_contracts: None,
        };
        let mut args = vec![
            "rustc".to_string(),
            CONTRACT_FIXTURE_PATH.to_string(),
            "--crate-name".to_string(),
            "trust_mir_extract_contracts_fixture".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
            "-Zno-codegen".to_string(),
            // All embedded compiler fixtures stop during analysis.  Select
            // rustc's built-in dummy backend explicitly so unit tests neither
            // dlopen the staged default nor poison the process-global backend
            // loader when a test sysroot is incomplete.
            "-Zcodegen-backend=dummy".to_string(),
            "-Ztrust-verify=off".to_string(),
        ];
        args.push("--sysroot".to_string());
        args.push(compiler_sysroot());

        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile contract fixture");

        ContractFixture {
            functions: callbacks.functions,
            metadata: callbacks.metadata,
            empty_bundle_metadata: callbacks.empty_bundle_metadata,
            conversion: callbacks
                .conversion_fixture
                .expect("synthetic contract conversion fixture should be built"),
            query_contracts: callbacks.query_contracts,
        }
    }

    fn extract_call_target_fixture() -> CallTargetFixture {
        let mut callbacks = CallTargetCallbacks { fixture: CallTargetFixture::default() };
        // This is a self-contained no_core fixture; requiring a staged sysroot
        // would make it depend on unrelated std assembly.
        let args = vec![
            "rustc".to_string(),
            CALL_TARGET_FIXTURE_PATH.to_string(),
            "--crate-name".to_string(),
            "trust_mir_extract_call_target_fixture".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
            "-Zno-codegen".to_string(),
            "-Zcodegen-backend=dummy".to_string(),
            "-Ztrust-verify=off".to_string(),
            "-Ainternal_features".to_string(),
        ];

        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile call-target fixture");

        callbacks.fixture
    }

    fn extract_codegen_fidelity_fixture() -> CodegenFidelityFixture {
        let mut callbacks = CodegenFidelityCallbacks { fixture: CodegenFidelityFixture::default() };
        let mut args = vec![
            "rustc".to_string(),
            CODEGEN_FIDELITY_FIXTURE_PATH.to_string(),
            "--crate-name".to_string(),
            "trust_mir_extract_codegen_fidelity_fixture".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=0".to_string(),
            "-Cdebug-assertions=yes".to_string(),
            "-Zno-codegen".to_string(),
            "-Zcodegen-backend=dummy".to_string(),
            "-Ztrust-verify=off".to_string(),
        ];
        args.push("--sysroot".to_string());
        args.push(compiler_sysroot());

        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile codegen-fidelity fixture");

        callbacks.fixture
    }

    fn extract_option_return_fixture() -> VerifiableFunction {
        let mut callbacks = OptionReturnCallbacks { function: None };
        let args = vec![
            "rustc".to_string(),
            OPTION_RETURN_FIXTURE_PATH.to_string(),
            "--crate-name".to_string(),
            "trust_mir_extract_option_return_fixture".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
            "-Zno-codegen".to_string(),
            "-Zcodegen-backend=dummy".to_string(),
            "-Ztrust-verify=off".to_string(),
            "-Ainternal_features".to_string(),
        ];

        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile no_core option return fixture");

        callbacks.function.expect("option_value should be extracted")
    }

    fn extract_level_datatype_fixture() -> Ty {
        let mut callbacks = LevelExtractionCallbacks { level_ty: None, probe: Vec::new() };
        // no_core fixture: no `--sysroot` (no extern crates), `-Ainternal_features`
        // to allow `#![feature(lang_items, no_core)]` — mirrors the option-return
        // fixture's invocation, which compiles in-process where std fixtures ICE.
        // `-Ztrust-verify=off`: this stage2 rustc runs the native Trust verification
        // pass ON EVERY COMPILE (batteries-on default); it hard-errors on
        // `make_level` (a raw-pointer-bearing datatype it treats as an unmodeled
        // construct), which flakily aborts the fixture compile. We only need the
        // extracted `Level` type here, not to verify the fixture, so opt out (the
        // `TRUST_VANILLA_RUSTC_FLAG` compiletest uses for the same reason).
        let args = vec![
            "rustc".to_string(),
            LEVEL_FIXTURE_PATH.to_string(),
            "--crate-name".to_string(),
            "clean_kernel".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
            "-Zno-codegen".to_string(),
            "-Zcodegen-backend=dummy".to_string(),
            "-Ztrust-verify=off".to_string(),
            "-Ainternal_features".to_string(),
        ];

        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile clean_kernel Level fixture");

        callbacks.level_ty.unwrap_or_else(|| {
            panic!(
                "clean_kernel::level::Level should be extracted; ADT locals seen: {:?}",
                callbacks.probe
            )
        })
    }

    /// Lever A step 5 — compile the expr fixture in-process and return the
    /// extracted `(ExprKind, Expr)` types. Same invocation as the Level fixture
    /// (`--crate-name clean_kernel`, `no_core`, `-Ztrust-verify=off` to opt out of
    /// the batteries-on native trust-verify pass that ICEs on raw-pointer datatypes).
    fn extract_expr_datatypes_fixture() -> (Ty, Ty) {
        let mut callbacks =
            ExprExtractionCallbacks { exprkind_ty: None, expr_ty: None, probe: Vec::new() };
        let args = vec![
            "rustc".to_string(),
            EXPR_FIXTURE_PATH.to_string(),
            "--crate-name".to_string(),
            "clean_kernel".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
            "-Zno-codegen".to_string(),
            "-Zcodegen-backend=dummy".to_string(),
            "-Ztrust-verify=off".to_string(),
            "-Ainternal_features".to_string(),
        ];

        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile clean_kernel Expr fixture");

        let probe = callbacks.probe.clone();
        let exprkind_ty = callbacks.exprkind_ty.unwrap_or_else(|| {
            panic!(
                "clean_kernel::expr::kind::ExprKind should be extracted; ADT locals seen: {probe:?}"
            )
        });
        let expr_ty = callbacks.expr_ty.unwrap_or_else(|| {
            panic!("clean_kernel::expr::Expr should be extracted; ADT locals seen: {probe:?}")
        });
        (exprkind_ty, expr_ty)
    }

    /// Lever A step 3 — compile the Expr fixture and extract every free
    /// function's real MIR body as a `VerifiableFunction`.
    fn extract_expr_fixture_bodies() -> BTreeMap<String, VerifiableFunction> {
        let mut callbacks = ExprBodyCallbacks { functions: BTreeMap::new() };
        let args = vec![
            "rustc".to_string(),
            EXPR_FIXTURE_PATH.to_string(),
            "--crate-name".to_string(),
            "clean_kernel".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
            "-Zno-codegen".to_string(),
            "-Zcodegen-backend=dummy".to_string(),
            "-Ztrust-verify=off".to_string(),
            "-Ainternal_features".to_string(),
        ];
        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile clean_kernel Expr fixture");
        callbacks.functions
    }

    #[test]
    fn recovered_parameter_names_populate_both_low_debuginfo_maps() {
        let mut local_names = FxHashMap::default();
        let mut name_locals = FxHashMap::default();
        merge_recovered_parameter_names(
            &mut local_names,
            &mut name_locals,
            2,
            &[Some("x".to_string()), Some("xs".to_string())],
        );

        assert_eq!(local_names.get(&1).map(String::as_str), Some("x"));
        assert_eq!(local_names.get(&2).map(String::as_str), Some("xs"));
        assert_eq!(name_locals.get("x").map(Vec::as_slice), Some(&[1][..]));
        assert_eq!(name_locals.get("xs").map(Vec::as_slice), Some(&[2][..]));
    }

    #[test]
    fn recovered_parameter_names_require_an_exact_plain_hir_vector() {
        let mut local_names = FxHashMap::default();
        let mut name_locals = FxHashMap::default();
        merge_recovered_parameter_names(
            &mut local_names,
            &mut name_locals,
            2,
            &[Some("n".to_string())],
        );
        assert!(local_names.is_empty());
        assert!(name_locals.is_empty());

        merge_recovered_parameter_names(
            &mut local_names,
            &mut name_locals,
            2,
            &[None, Some("plain".to_string())],
        );
        assert!(local_names.is_empty());
        assert!(name_locals.is_empty());
    }

    #[test]
    fn recovered_parameter_names_reject_occupied_duplicate_and_synthetic_names() {
        let mut local_names = FxHashMap::default();
        local_names.insert(4, "debug_name".to_string());
        let mut name_locals = FxHashMap::default();
        name_locals.insert("raw_name".to_string(), vec![5, 6]);
        name_locals.insert("local_one_is_occupied".to_string(), vec![1]);

        merge_recovered_parameter_names(
            &mut local_names,
            &mut name_locals,
            8,
            &[
                Some("candidate_for_occupied_local".to_string()),
                Some("debug_name".to_string()),
                Some("raw_name".to_string()),
                Some("candidate_for_occupied_local_four".to_string()),
                Some("duplicate".to_string()),
                Some("duplicate".to_string()),
                Some("s__slice_len".to_string()),
                Some("xs".to_string()),
            ],
        );

        // Locals occupied through either map, names occupied through either map,
        // duplicate HIR names, and Trust's generated namespace all fail closed.
        for local in [1, 2, 3, 5, 6, 7] {
            assert_eq!(local_names.get(&local), None, "local {local} was recovered");
        }
        assert_eq!(local_names.get(&4).map(String::as_str), Some("debug_name"));
        assert_eq!(local_names.get(&8).map(String::as_str), Some("xs"));
        assert_eq!(name_locals.get("xs").map(Vec::as_slice), Some(&[8][..]));
        assert!(!name_locals.contains_key("candidate_for_occupied_local"));
        assert!(!name_locals.contains_key("candidate_for_occupied_local_four"));
        assert!(!name_locals.contains_key("duplicate"));
        assert!(!name_locals.contains_key("s__slice_len"));
    }

    /// WALL C — compile the mirror fixture and extract every free function's
    /// real MIR body as a `VerifiableFunction`. Same invocation as the Expr
    /// fixture (`--crate-name clean_kernel`, `no_core`, `-Ztrust-verify=off`).
    fn extract_mirror_fixture_bodies() -> BTreeMap<String, VerifiableFunction> {
        let mut callbacks = MirrorBodyCallbacks { functions: BTreeMap::new() };
        let args = vec![
            "rustc".to_string(),
            MIRROR_FIXTURE_PATH.to_string(),
            "--crate-name".to_string(),
            "clean_kernel".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
            "-Zno-codegen".to_string(),
            "-Zcodegen-backend=dummy".to_string(),
            "-Ztrust-verify=off".to_string(),
            "-Ainternal_features".to_string(),
        ];
        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile clean_kernel mirror fixture");
        callbacks.functions
    }

    /// EXTRACTION SERIALIZATION — compile the literal-cluster fixture and
    /// extract every free function's real MIR body as a `VerifiableFunction`.
    /// Same invocation as the mirror/mutual fixtures.
    fn extract_literal_cluster_fixture_bodies() -> BTreeMap<String, VerifiableFunction> {
        let mut callbacks = LiteralClusterBodyCallbacks { functions: BTreeMap::new() };
        let args = vec![
            "rustc".to_string(),
            LITERAL_CLUSTER_FIXTURE_PATH.to_string(),
            "--crate-name".to_string(),
            "clean_kernel".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
            "-Zno-codegen".to_string(),
            "-Zcodegen-backend=dummy".to_string(),
            "-Ztrust-verify=off".to_string(),
            "-Ainternal_features".to_string(),
        ];
        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile clean_kernel literal-cluster fixture");
        callbacks.functions
    }

    /// INTERIOR-MUTABILITY GAP — compile the cell-counter fixture and
    /// extract every free function's real MIR body as a `VerifiableFunction`.
    /// Same invocation as the mirror/mutual/literal-cluster fixtures.
    fn extract_cell_counter_fixture_bodies() -> BTreeMap<String, VerifiableFunction> {
        let mut callbacks = CellCounterBodyCallbacks { functions: BTreeMap::new() };
        let args = vec![
            "rustc".to_string(),
            CELL_COUNTER_FIXTURE_PATH.to_string(),
            "--crate-name".to_string(),
            "clean_kernel".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
            "-Zno-codegen".to_string(),
            "-Zcodegen-backend=dummy".to_string(),
            "-Ztrust-verify=off".to_string(),
            "-Ainternal_features".to_string(),
        ];
        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile clean_kernel cell-counter fixture");
        callbacks.functions
    }

    // ── EXTRACTED-ARTIFACT SERIALIZATION (the extraction -> integration
    //    hand-off) ─────────────────────────────────────────────────────────────
    //
    // trust-integration-tests cannot run the in-process rustc, so its lane
    // e2e tests consume the extractor's output through COMMITTED serialized
    // artifacts under `crates/trust-integration-tests/fixtures/extracted/`.
    // The artifacts are REGENERATED, never hand-edited: the gate tests below
    // re-extract the fixture in-process, serialize it, and compare
    // byte-for-byte against the committed file — any drift between the live
    // extractor and the committed artifact fails the suite. Regenerate with
    //
    //   TRUST_UPDATE_EXTRACTED_FIXTURES=1 <the usual trust-mir-extract --lib
    //   incantation> extracted_
    //
    // and commit the JSON together with the extractor change. The
    // serialization is pipeline plumbing, NOT TCB: the artifacts are the
    // post-conversion `VerifiableFunction` form (everything rustc-internal is
    // already gone by then), and the kernel check downstream remains the
    // authority on every proof obligation.

    /// The committed artifacts directory (inside trust-integration-tests).
    fn extracted_artifacts_dir() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../trust-integration-tests/fixtures/extracted")
    }

    /// Canonical serialization of an extraction run: pretty JSON of the
    /// name -> `VerifiableFunction` map (BTreeMap: key order is stable;
    /// struct fields serialize in declaration order), trailing newline.
    fn serialize_extracted_functions(functions: &BTreeMap<String, VerifiableFunction>) -> String {
        let mut json = serde_json::to_string_pretty(functions)
            .expect("VerifiableFunction serialization is infallible");
        json.push('\n');
        json
    }

    /// The drift gate: the fresh in-process extraction must match the
    /// committed artifact byte-for-byte. With `TRUST_UPDATE_EXTRACTED_FIXTURES=1`
    /// the committed artifact is (re)written instead.
    fn assert_matches_committed_artifact(
        artifact: &str,
        functions: &BTreeMap<String, VerifiableFunction>,
    ) {
        let json = serialize_extracted_functions(functions);
        let path = extracted_artifacts_dir().join(artifact);
        if std::env::var_os("TRUST_UPDATE_EXTRACTED_FIXTURES").is_some() {
            std::fs::create_dir_all(extracted_artifacts_dir()).expect("create fixtures/extracted");
            std::fs::write(&path, &json)
                .unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
            eprintln!("regenerated extracted artifact {}", path.display());
            return;
        }
        let committed = std::fs::read_to_string(&path).unwrap_or_else(|e| {
            panic!(
                "missing committed extracted artifact {} ({e}). The artifact is \
                 REGENERATED, never hand-edited: rerun this test with \
                 TRUST_UPDATE_EXTRACTED_FIXTURES=1 and commit the JSON.",
                path.display()
            )
        });
        assert!(
            committed == json,
            "extracted artifact DRIFT: {} no longer matches the live extractor's \
             output. If the extractor change is intentional, regenerate with \
             TRUST_UPDATE_EXTRACTED_FIXTURES=1 and commit the JSON together with \
             the change (the integration e2e tests consume this artifact).",
            path.display()
        );
    }

    /// WALL C scaled to MUTUAL SCCs — compile the mutual ring fixture and
    /// extract every free function's real MIR body as a `VerifiableFunction`.
    /// Same invocation as the mirror fixture.
    fn extract_mutual_fixture_bodies() -> BTreeMap<String, VerifiableFunction> {
        let mut callbacks = MutualBodyCallbacks { functions: BTreeMap::new() };
        let args = vec![
            "rustc".to_string(),
            MUTUAL_FIXTURE_PATH.to_string(),
            "--crate-name".to_string(),
            "clean_kernel".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
            "-Zno-codegen".to_string(),
            "-Zcodegen-backend=dummy".to_string(),
            "-Ztrust-verify=off".to_string(),
            "-Ainternal_features".to_string(),
        ];
        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile clean_kernel mutual fixture");
        callbacks.functions
    }

    /// Lever A step 3 (FAITHFULNESS of the VC-gen INPUT): the real extracted MIR
    /// body of `build_sort(l) = ExprKind::Sort(l)` is exactly the
    /// `Rvalue::Aggregate(Adt { variant = Sort, .. }, [l])` over a `Ty::Datatype`
    /// dest that `trust-vcgen::datatype_functional` models as `Ctor("Sort",[l])`.
    /// This closes the gap between the hand-built representatives in the
    /// trust-vcgen unit tests and what the extractor actually produces.
    #[test]
    fn real_mir_sort_arm_body_is_datatype_aggregate() {
        let bodies = extract_expr_fixture_bodies();
        let f = bodies
            .get("build_sort")
            .unwrap_or_else(|| panic!("build_sort not extracted; saw {:?}", bodies.keys()));

        // The return type is the modeled ExprKind datatype (step 5), not Unsupported.
        assert!(
            f.body.return_ty.is_datatype(),
            "build_sort return type must be a modeled datatype, got {:?}",
            f.body.return_ty
        );

        // Find the enum-variant construction: `_x = ExprKind::Sort(l)`.
        let mut matched = None;
        for block in &f.body.blocks {
            for stmt in &block.stmts {
                let Statement::Assign {
                    place,
                    rvalue: Rvalue::Aggregate(AggregateKind::Adt { variant, .. }, ops),
                    ..
                } = stmt
                else {
                    continue;
                };
                let dest_ty = f.body.locals.iter().find(|d| d.index == place.local).map(|d| &d.ty);
                if let Some(Ty::Datatype { name, variants }) = dest_ty {
                    if name.ends_with("ExprKind") {
                        matched = Some((*variant, variants.clone(), ops.len()));
                    }
                }
            }
        }

        let (variant, variants, n_ops) = matched
            .expect("build_sort must lower to an Aggregate(Adt) constructing an ExprKind variant");
        let (ctor, fields) = &variants[variant];
        assert_eq!(ctor, "Sort", "the constructed variant is Sort");
        assert_eq!(fields.len(), 1, "Sort has one (Level) field");
        assert_eq!(n_ops, 1, "the Aggregate carries exactly the single level operand");
    }

    /// WALL C (FAITHFULNESS of the recursive VC-gen INPUT): the real extracted
    /// MIR of the SELF-recursive `mirror : &Level -> Level` has exactly the
    /// shape `trust-vcgen::recursive_datatype_functional` walks (the
    /// `extracted_mirror_func` transcriptions in trust-vcgen's unit tests
    /// mirror it; trust-integration-tests' `recursive_datatype_functional_e2e`
    /// consumes the LITERAL extraction via the drift-gated committed artifact,
    /// see `extracted_mirror_artifact_matches_committed`):
    ///   * the 2-variant `level::Level` lowers to `Ty::Datatype` (return slot),
    ///     the parameter to `Ref { Datatype }`;
    ///   * a `Discriminant((*_1))` + `SwitchInt` covering BOTH variant tags,
    ///     `otherwise -> Unreachable` (exhaustive match);
    ///   * the Zero arm builds `Aggregate(Adt { variant: 0 }, [])` into `_0`;
    ///   * the Succ arm reads the payload `((*_1 as Succ).0)`, SELF-CALLS
    ///     `mirror` on it (the recursive occurrence the VC lane replaces with
    ///     the IH variable), and builds `Aggregate(Adt { variant: 1 }, [ptr])`
    ///     from the call result (through the `&m as *const _` AddressOf).
    #[test]
    fn real_mir_recursive_mirror_body_shape() {
        let bodies = extract_mirror_fixture_bodies();
        let f = bodies
            .get("mirror")
            .unwrap_or_else(|| panic!("mirror not extracted; saw {:?}", bodies.keys()));

        // Return slot: the modeled 2-variant Level datatype.
        let Ty::Datatype { name, variants } = &f.body.return_ty else {
            panic!("mirror return type must be a modeled datatype, got {:?}", f.body.return_ty);
        };
        assert_eq!(name, "clean_kernel::level::Level");
        assert_eq!(
            variants.iter().map(|(c, fs)| (c.as_str(), fs.len())).collect::<Vec<_>>(),
            vec![("Zero", 0), ("Succ", 1)],
            "the fixture Level slice is Zero | Succ(Level)"
        );
        // Parameter: a reference to the same datatype (the model peels it).
        assert_eq!(f.body.arg_count, 1);
        let param_ty = &f.body.locals.iter().find(|d| d.index == 1).expect("param _1").ty;
        assert!(
            matches!(param_ty, Ty::Ref { inner, .. } if inner.is_datatype()),
            "param must be &Level, got {param_ty:?}"
        );

        // The match: Discriminant((*_1)) driving a SwitchInt over BOTH tags,
        // with the exhaustive-match otherwise -> Unreachable.
        let mut saw_discr_on_param = false;
        let mut switch = None;
        for block in &f.body.blocks {
            for stmt in &block.stmts {
                if let Statement::Assign { rvalue: Rvalue::Discriminant(p), .. } = stmt {
                    assert_eq!(p.local, 1, "the discriminant is read off the parameter");
                    assert_eq!(p.projections, vec![Projection::Deref]);
                    saw_discr_on_param = true;
                }
            }
            if let Terminator::SwitchInt { targets, otherwise, .. } = &block.terminator {
                switch = Some((targets.clone(), *otherwise));
            }
        }
        assert!(saw_discr_on_param, "must read discriminant((*_1))");
        let (targets, otherwise) = switch.expect("mirror must lower to a SwitchInt match");
        let mut tags: Vec<u128> = targets.iter().map(|(t, _)| *t).collect();
        tags.sort_unstable();
        assert_eq!(tags, vec![0, 1], "the switch must cover both constructor tags");
        let otherwise_block =
            f.body.blocks.iter().find(|b| b.id == otherwise).expect("otherwise block");
        assert!(
            matches!(otherwise_block.terminator, Terminator::Unreachable),
            "exhaustive match: otherwise must be Unreachable, got {:?}",
            otherwise_block.terminator
        );

        // The SELF-recursive call, fed by the Succ payload read.
        let mut saw_payload_read = false;
        let mut self_call = None;
        for block in &f.body.blocks {
            for stmt in &block.stmts {
                if let Statement::Assign { rvalue: Rvalue::Use(Operand::Copy(p)), .. } = stmt {
                    if p.local == 1
                        && p.projections
                            == vec![
                                Projection::Deref,
                                Projection::Downcast(1),
                                Projection::Field(0),
                            ]
                    {
                        saw_payload_read = true;
                    }
                }
            }
            if let Terminator::Call { func: callee, args, target, .. } = &block.terminator {
                if callee == "clean_kernel::mirror" {
                    assert_eq!(args.len(), 1, "mirror takes one argument");
                    assert!(target.is_some(), "the recursive call returns normally");
                    self_call = Some(());
                }
            }
        }
        assert!(saw_payload_read, "the Succ arm must read the payload ((*_1 as Succ).0)");
        assert!(self_call.is_some(), "mirror must contain the SELF-recursive call");

        // Both constructor arms build `_0` as datatype aggregates: the Zero arm
        // a nullary variant-0, the Succ arm a unary variant-1 from the call
        // result (via AddressOf).
        let mut zero_arm = false;
        let mut succ_arm = false;
        let mut saw_addressof = false;
        for block in &f.body.blocks {
            for stmt in &block.stmts {
                match stmt {
                    Statement::Assign {
                        place,
                        rvalue: Rvalue::Aggregate(AggregateKind::Adt { variant, .. }, ops),
                        ..
                    } if place.local == 0 && place.projections.is_empty() => match variant {
                        0 => {
                            assert!(ops.is_empty(), "Zero is nullary");
                            zero_arm = true;
                        }
                        1 => {
                            assert_eq!(ops.len(), 1, "Succ carries one payload");
                            succ_arm = true;
                        }
                        v => panic!("unexpected variant {v} constructed into _0"),
                    },
                    Statement::Assign { rvalue: Rvalue::AddressOf(_, p), .. } => {
                        // `&m as *const Level` — the address of the recursive
                        // call's result local.
                        assert!(p.projections.is_empty());
                        saw_addressof = true;
                    }
                    _ => {}
                }
            }
        }
        assert!(zero_arm, "the Zero arm must build Aggregate(variant 0, [])");
        assert!(succ_arm, "the Succ arm must build Aggregate(variant 1, [result ptr])");
        assert!(saw_addressof, "the Succ arm coerces the call result via AddressOf");
    }

    /// WALL C SCALED TO MUTUAL SCCs (FAITHFULNESS of the mutual VC-gen INPUT):
    /// the real extracted MIR of the 3-function ring `fm -> gm -> hm -> fm`
    /// has exactly the fuel-indexed cluster shape
    /// `trust-vcgen::mutual_recursive_datatype_functional` walks (the
    /// `ring_member` transcriptions in trust-vcgen's unit tests mirror it;
    /// trust-integration-tests' `mutual_recursive_datatype_functional_e2e`
    /// consumes the LITERAL extraction via the drift-gated committed artifact,
    /// see `extracted_mutual_artifact_matches_committed`):
    ///   * the fuel parameter is `&level::Level` with the nat-shaped 2-variant
    ///     slice (`Zero` nullary, `Succ` unary-recursive) and the payload
    ///     parameter/return is the 2-variant `expr::kind::ExprKind` datatype;
    ///   * the FIRST match is on the FUEL discriminant (`(*_1)`), the payload
    ///     match on `(*_2)` under BOTH fuel arms, exhaustive-otherwise
    ///     `Unreachable`;
    ///   * the Zero (base) subtree contains NO call — the identity rebuild
    ///     reads the `B` payload and rebuilds `Aggregate(variant 1, ..)`;
    ///   * the Succ (step) subtree reads the smaller fuel `((*_1 as Succ).0)`,
    ///     reads the `B` payload, and calls the NEXT ring member with TWO
    ///     arguments (fuel first) — the cross-member cluster edge the mutual
    ///     lane turns into the `[calls=..]`-tagged IH atom;
    ///   * the call-graph over the trio is one genuine SCC of size 3.
    #[test]
    fn real_mir_mutual_cluster_body_shape() {
        let bodies = extract_mutual_fixture_bodies();
        let ring = [("fm", "gm"), ("gm", "hm"), ("hm", "fm")];
        for (name, next) in ring {
            let f = bodies
                .get(name)
                .unwrap_or_else(|| panic!("{name} not extracted; saw {:?}", bodies.keys()));

            // Return slot + payload parameter: the modeled 2-variant ExprKind.
            let Ty::Datatype { name: ret_name, variants } = &f.body.return_ty else {
                panic!("{name} return type must be a modeled datatype, got {:?}", f.body.return_ty);
            };
            assert_eq!(ret_name, "clean_kernel::expr::kind::ExprKind");
            assert_eq!(
                variants.iter().map(|(c, fs)| (c.as_str(), fs.len())).collect::<Vec<_>>(),
                vec![("A", 0), ("B", 1)],
                "the payload slice is A | B(ExprKind)"
            );
            assert_eq!(f.body.arg_count, 2, "{name} takes (fuel, payload)");
            let fuel_ty = &f.body.locals.iter().find(|d| d.index == 1).expect("param _1").ty;
            let Ty::Ref { inner, .. } = fuel_ty else {
                panic!("{name} fuel param must be &Level, got {fuel_ty:?}");
            };
            let Ty::Datatype { name: fuel_name, variants: fuel_variants } = inner.as_ref() else {
                panic!("{name} fuel param must peel to a datatype, got {inner:?}");
            };
            assert_eq!(fuel_name, "clean_kernel::level::Level");
            assert_eq!(
                fuel_variants.iter().map(|(c, fs)| (c.as_str(), fs.len())).collect::<Vec<_>>(),
                vec![("Zero", 0), ("Succ", 1)],
                "the fuel index is nat-shaped"
            );
            let payload_ty = &f.body.locals.iter().find(|d| d.index == 2).expect("param _2").ty;
            assert!(
                matches!(payload_ty, Ty::Ref { inner, .. } if inner.is_datatype()),
                "{name} payload param must be &ExprKind, got {payload_ty:?}"
            );

            // Discriminant reads: the fuel match off `(*_1)` and the payload
            // match(es) off `(*_2)`; every switch's otherwise is Unreachable.
            let mut disc_locals: std::collections::HashMap<usize, usize> =
                std::collections::HashMap::new();
            for block in &f.body.blocks {
                for stmt in &block.stmts {
                    if let Statement::Assign { place, rvalue: Rvalue::Discriminant(p), .. } = stmt {
                        assert_eq!(p.projections, vec![Projection::Deref]);
                        disc_locals.insert(place.local, p.local);
                    }
                }
            }
            assert!(
                disc_locals.values().any(|&param| param == 1),
                "{name} must read discriminant((*_1)) — the fuel match"
            );
            assert!(
                disc_locals.values().any(|&param| param == 2),
                "{name} must read discriminant((*_2)) — the payload match"
            );
            let mut first_switch_param = None;
            for block in &f.body.blocks {
                if let Terminator::SwitchInt { discr, targets, otherwise, .. } = &block.terminator {
                    let local = match discr {
                        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => p.local,
                        other => panic!("{name} switch discr must be a plain local, got {other:?}"),
                    };
                    let param = disc_locals
                        .get(&local)
                        .unwrap_or_else(|| panic!("{name} switch on unread discriminant"));
                    if first_switch_param.is_none() {
                        first_switch_param = Some(*param);
                    }
                    let mut tags: Vec<u128> = targets.iter().map(|(t, _)| *t).collect();
                    tags.sort_unstable();
                    assert_eq!(tags, vec![0, 1], "{name} switches cover both constructor tags");
                    let ob = f.body.blocks.iter().find(|b| b.id == *otherwise).expect("otherwise");
                    assert!(
                        matches!(ob.terminator, Terminator::Unreachable),
                        "{name}: exhaustive match otherwise must be Unreachable"
                    );
                }
            }
            assert_eq!(
                first_switch_param,
                Some(1),
                "{name}: the FIRST switch (entry block) must match the FUEL parameter"
            );

            // The smaller-fuel read and the cross-member call (fuel first).
            let mut saw_fuel_payload_read = false;
            let mut cluster_call = None;
            for block in &f.body.blocks {
                for stmt in &block.stmts {
                    if let Statement::Assign { rvalue: Rvalue::Use(Operand::Copy(p)), .. } = stmt {
                        if p.local == 1
                            && p.projections
                                == vec![
                                    Projection::Deref,
                                    Projection::Downcast(1),
                                    Projection::Field(0),
                                ]
                        {
                            saw_fuel_payload_read = true;
                        }
                    }
                }
                if let Terminator::Call { func: callee, args, target, .. } = &block.terminator {
                    assert_eq!(
                        callee,
                        &format!("clean_kernel::{next}"),
                        "{name}'s only call is its ring successor"
                    );
                    assert_eq!(args.len(), 2, "cluster calls pass (fuel, payload)");
                    assert!(target.is_some(), "the cluster call returns normally");
                    cluster_call = Some(());
                }
            }
            assert!(
                saw_fuel_payload_read,
                "{name}: the Succ arm must read the smaller fuel ((*_1 as Succ).0)"
            );
            assert!(cluster_call.is_some(), "{name} must contain the cross-member call");
        }

        // The trio really is ONE strongly connected component of size 3: the
        // extracted call edges form exactly the ring fm -> gm -> hm -> fm.
        let mut edges: Vec<(String, String)> = Vec::new();
        for (name, _) in ring {
            for block in &bodies[name].body.blocks {
                if let Terminator::Call { func: callee, .. } = &block.terminator {
                    edges.push((name.to_string(), callee.clone()));
                }
            }
        }
        edges.sort();
        edges.dedup();
        assert_eq!(
            edges,
            vec![
                ("fm".to_string(), "clean_kernel::gm".to_string()),
                ("gm".to_string(), "clean_kernel::hm".to_string()),
                ("hm".to_string(), "clean_kernel::fm".to_string()),
            ],
            "the extracted cluster is the single 3-cycle SCC"
        );
    }

    /// EXTRACTION SERIALIZATION (shape sanity): the literal-cluster fixture
    /// extracts with the shapes its consumers rely on — the payload is the
    /// FULL 5-constructor `level::Level` (multi-IH `Max`/`IMax`, opaque
    /// `Param(Name)`), the fuel is the nat-shaped 2-constructor
    /// `expr::kind::ExprKind` slice, the model cluster {fm, gm} and the
    /// reference cluster {fr, gr} are genuine 2-SCCs, the reference members'
    /// fuel-Z arm is a DIRECT payload return (no per-ctor rebuild), and
    /// `gm_wrong` differs from the true bodies exactly by rebuilding Max in
    /// an IMax step arm. The full byte-level pin is the committed artifact
    /// (see `extracted_literal_cluster_artifact_matches_committed`).
    #[test]
    fn real_mir_literal_cluster_body_shape() {
        let bodies = extract_literal_cluster_fixture_bodies();
        assert_eq!(
            bodies.keys().cloned().collect::<Vec<_>>(),
            vec!["fm", "fr", "gm", "gm_wrong", "gr"],
            "the five cluster functions extract"
        );

        for (name, f) in &bodies {
            // Return slot + payload parameter: the FULL modeled Level.
            let Ty::Datatype { name: ret_name, variants } = &f.body.return_ty else {
                panic!("{name} return type must be a modeled datatype, got {:?}", f.body.return_ty);
            };
            assert_eq!(ret_name, "clean_kernel::level::Level");
            assert_eq!(
                variants.iter().map(|(c, fs)| (c.as_str(), fs.len())).collect::<Vec<_>>(),
                vec![("Zero", 0), ("Succ", 1), ("Max", 2), ("IMax", 2), ("Param", 1)],
                "{name}: the payload is the full Level slice"
            );
            // The Param field is the opaque Name (a by-name datatype ref).
            let param_field = &variants[4].1[0].1;
            assert!(
                matches!(
                    param_field,
                    Ty::Datatype { name, variants }
                        if name == "clean_kernel::name::Name" && variants.is_empty()
                ),
                "{name}: Param carries the opaque Name ref, got {param_field:?}"
            );
            // Fuel parameter: the nat-shaped gated ExprKind slice.
            assert_eq!(f.body.arg_count, 2, "{name} takes (fuel, payload)");
            let fuel_ty = &f.body.locals.iter().find(|d| d.index == 1).expect("param _1").ty;
            let Ty::Ref { inner, .. } = fuel_ty else {
                panic!("{name} fuel param must be &ExprKind, got {fuel_ty:?}");
            };
            let Ty::Datatype { name: fuel_name, variants: fuel_variants } = inner.as_ref() else {
                panic!("{name} fuel param must peel to a datatype, got {inner:?}");
            };
            assert_eq!(fuel_name, "clean_kernel::expr::kind::ExprKind");
            assert_eq!(
                fuel_variants.iter().map(|(c, fs)| (c.as_str(), fs.len())).collect::<Vec<_>>(),
                vec![("Z", 0), ("S", 1)],
                "{name}: the fuel index is nat-shaped"
            );
        }

        // Call edges: the model 2-SCC, the wrong twin's edge into it, and the
        // reference 2-SCC.
        let mut edges: Vec<(String, String)> = Vec::new();
        for (name, f) in &bodies {
            for block in &f.body.blocks {
                if let Terminator::Call { func: callee, args, .. } = &block.terminator {
                    assert_eq!(args.len(), 2, "{name}: cluster calls pass (fuel, payload)");
                    edges.push((name.clone(), callee.clone()));
                }
            }
        }
        edges.sort();
        edges.dedup();
        assert_eq!(
            edges,
            vec![
                ("fm".to_string(), "clean_kernel::gm".to_string()),
                ("fr".to_string(), "clean_kernel::gr".to_string()),
                ("gm".to_string(), "clean_kernel::fm".to_string()),
                ("gm_wrong".to_string(), "clean_kernel::fm".to_string()),
                ("gr".to_string(), "clean_kernel::fr".to_string()),
            ],
            "model SCC {{fm,gm}}, reference SCC {{fr,gr}}, gm_wrong -> fm"
        );

        // Reference members: the fuel-Z arm is a DIRECT `copy (*_2)` return
        // into _0 — no per-constructor rebuild (the model/reference folds are
        // genuinely different).
        for name in ["fr", "gr"] {
            let f = &bodies[name];
            let direct_base = f.body.blocks.iter().any(|b| {
                b.stmts.iter().any(|s| {
                    matches!(
                        s,
                        Statement::Assign { place, rvalue: Rvalue::Use(Operand::Copy(p)), .. }
                            if place.local == 0
                                && place.projections.is_empty()
                                && p.local == 2
                                && p.projections == vec![Projection::Deref]
                    )
                })
            });
            assert!(direct_base, "{name}: the fuel-Z arm returns the payload directly");
        }

        // gm vs gm_wrong: same everything except ONE aggregate variant — the
        // IMax step arm's rebuild (IMax=3 in gm, Max=2 in gm_wrong).
        let rebuild_variants = |f: &VerifiableFunction| -> Vec<usize> {
            f.body
                .blocks
                .iter()
                .flat_map(|b| &b.stmts)
                .filter_map(|s| match s {
                    Statement::Assign {
                        place,
                        rvalue: Rvalue::Aggregate(AggregateKind::Adt { variant, .. }, _),
                        ..
                    } if place.local == 0 && place.projections.is_empty() => Some(*variant),
                    _ => None,
                })
                .collect()
        };
        let gm_variants = rebuild_variants(&bodies["gm"]);
        let wrong_variants = rebuild_variants(&bodies["gm_wrong"]);
        assert_eq!(gm_variants.len(), wrong_variants.len());
        let diffs: Vec<(usize, usize)> = gm_variants
            .iter()
            .zip(&wrong_variants)
            .filter(|(a, b)| a != b)
            .map(|(a, b)| (*a, *b))
            .collect();
        assert_eq!(
            diffs,
            vec![(3, 2)],
            "gm_wrong differs from gm exactly by rebuilding Max (2) where gm rebuilds IMax (3)"
        );
    }

    /// Drift gate: the committed expr-fixture artifact (`build_sort`,
    /// `build_sort_expr`) is byte-identical to the live extraction.
    #[test]
    fn extracted_expr_artifact_matches_committed() {
        let bodies = extract_expr_fixture_bodies();
        assert!(bodies.contains_key("build_sort"), "saw {:?}", bodies.keys());
        assert_matches_committed_artifact("expr_fixture_functions.json", &bodies);
    }

    /// Drift gate: the committed mirror artifact (the WALL C self-recursive
    /// `mirror`, consumed by `recursive_datatype_functional_e2e`) is
    /// byte-identical to the live extraction.
    #[test]
    fn extracted_mirror_artifact_matches_committed() {
        let bodies = extract_mirror_fixture_bodies();
        assert!(bodies.contains_key("mirror"), "saw {:?}", bodies.keys());
        assert_matches_committed_artifact("mirror_fixture_functions.json", &bodies);
    }

    /// Drift gate: the committed mutual-ring artifact (fm/gm/hm, consumed by
    /// `mutual_recursive_datatype_functional_e2e`) is byte-identical to the
    /// live extraction.
    #[test]
    fn extracted_mutual_artifact_matches_committed() {
        let bodies = extract_mutual_fixture_bodies();
        assert_eq!(bodies.keys().cloned().collect::<Vec<_>>(), vec!["fm", "gm", "hm"]);
        assert_matches_committed_artifact("mutual_fixture_functions.json", &bodies);
    }

    /// Drift gate: the committed literal-cluster artifact (fm/gm/gm_wrong/
    /// fr/gr, consumed by `mutual_literal_cluster_e2e`) is byte-identical to
    /// the live extraction.
    #[test]
    fn extracted_literal_cluster_artifact_matches_committed() {
        let bodies = extract_literal_cluster_fixture_bodies();
        assert_eq!(
            bodies.keys().cloned().collect::<Vec<_>>(),
            vec!["fm", "fr", "gm", "gm_wrong", "gr"]
        );
        assert_matches_committed_artifact("literal_cluster_fixture_functions.json", &bodies);
    }

    /// The canonical cluster spec for the cell-counter fixture: the
    /// cell-mediated model {fm, gm}, the hand-threaded reference {fr, gr}, and
    /// the accessor callee names.
    fn cell_counter_spec() -> crate::cell_threading::CellThreadingSpec {
        crate::cell_threading::CellThreadingSpec {
            members: vec!["fm".to_string(), "gm".to_string()],
            references: vec!["fr".to_string(), "gr".to_string()],
            get_fn: "cell_get".to_string(),
            set_fn: "cell_set".to_string(),
        }
    }

    /// INTERIOR-MUTABILITY GAP — the Cell→threading transform on the LITERAL
    /// extracted MIR. Extract the cell-mediated cluster and lower it with
    /// `thread_cell_state`, then assert the output is in the
    /// `threaded_budget_functional` lane grammar: `(&Fuel, E) -> Res`, a fuel
    /// switch whose Z arm is the pinned exhaustion `Mk(*fuel, *e)`, and cluster
    /// calls whose fuel argument is the current cell state (`&(*_9)` for the
    /// first call, a reborrow of the previous call's remainder `_.0` for the
    /// threaded second call). The negative control (`fm_leak`, which passes the
    /// holder to an out-of-grammar callee) must fail closed.
    #[test]
    fn real_mir_cell_counter_threads_to_lane_shape() {
        use crate::cell_threading::thread_cell_state;
        let bodies = extract_cell_counter_fixture_bodies();
        assert_eq!(
            bodies.keys().cloned().collect::<Vec<_>>(),
            vec!["cell_get", "cell_set", "fm", "fm_leak", "fr", "gm", "gr", "leak"],
            "the cell fixture extracts the accessors, model, negative, and reference"
        );

        let threaded = thread_cell_state(&bodies, &cell_counter_spec())
            .expect("the cell-mediated cluster lowers to the threaded shape");
        assert_eq!(threaded.keys().cloned().collect::<Vec<_>>(), vec!["fm", "fr", "gm", "gr"]);

        // The result-pair datatype `Res = Mk(Fuel, E)`, derived from the
        // reference return type by normalization.
        let res_dt = &threaded["fr"].body.return_ty;
        let Ty::Datatype { name: res_name, variants: res_variants } = res_dt else {
            panic!("Res must normalize to a datatype, got {res_dt:?}");
        };
        assert_eq!(res_name, "clean_kernel::res::Res");
        assert_eq!(res_variants.len(), 1, "the pair has one constructor");
        assert_eq!(res_variants[0].0, "Mk");

        for name in ["fm", "gm"] {
            let f = &threaded[name];
            // Threaded signature: `_1: &Fuel`, `_0: Res`.
            assert_eq!(f.body.arg_count, 2);
            assert_eq!(f.body.return_ty, *res_dt, "{name} now returns the result pair");
            let fuel_param = &f.body.locals.iter().find(|l| l.index == 1).unwrap().ty;
            let Ty::Ref { inner, .. } = fuel_param else {
                panic!("{name} param _1 must be &Fuel, got {fuel_param:?}");
            };
            let Ty::Datatype { name: fuel_name, variants: fuel_variants } = inner.as_ref() else {
                panic!("{name} fuel param must peel to a datatype");
            };
            assert_eq!(fuel_name, "clean_kernel::fuel::Fuel");
            assert_eq!(
                fuel_variants.iter().map(|(c, fs)| (c.as_str(), fs.len())).collect::<Vec<_>>(),
                vec![("Z", 0), ("S", 1)],
                "{name}: the fuel index is nat-shaped"
            );

            // NO surviving cell mechanism: no call to a cell accessor, and `_1`
            // is never an assignment destination (it is the read-only fuel).
            for b in &f.body.blocks {
                if let Terminator::Call { func: callee, .. } = &b.terminator {
                    assert!(
                        callee != "cell_get" && callee != "cell_set",
                        "{name}: accessor calls are lowered away, saw {callee}"
                    );
                }
                for s in &b.stmts {
                    if let Statement::Assign { place, .. } = s {
                        assert_ne!(place.local, 1, "{name}: the fuel param is never written");
                    }
                }
            }

            // Every return site produces the result pair `_0 = Mk(_, _)`.
            let returns_pair = f.body.blocks.iter().any(|b| {
                b.stmts.iter().any(|s| {
                    matches!(s, Statement::Assign {
                        place,
                        rvalue: Rvalue::Aggregate(AggregateKind::Adt { name, variant: 0, .. }, ops),
                        ..
                    } if place.local == 0
                        && name == "clean_kernel::res::Res"
                        && ops.len() == 2)
                })
            });
            assert!(returns_pair, "{name}: return sites are wrapped into Mk(rem, payload)");

            // The cluster calls are threaded: every remaining Call targets the
            // sibling member and passes a fuel-typed first argument.
            let cluster_calls = f
                .body
                .blocks
                .iter()
                .filter_map(|b| match &b.terminator {
                    Terminator::Call { func: callee, args, .. } => {
                        Some((callee.clone(), args.len()))
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert!(
                !cluster_calls.is_empty()
                    && cluster_calls
                        .iter()
                        .all(|(c, argc)| { (c == "fm" || c == "gm") && *argc == 2 }),
                "{name}: all surviving calls are 2-arg cluster calls, saw {cluster_calls:?}"
            );
        }
    }

    /// INTERIOR-MUTABILITY GAP negative — the transform FAILS CLOSED when the
    /// holder escapes the accessor/cluster-call grammar. Threading a spec that
    /// includes `fm_leak` (which passes `tc` to the out-of-grammar `leak`)
    /// yields `None`.
    #[test]
    fn cell_threading_rejects_holder_escape() {
        use crate::cell_threading::{CellThreadingSpec, thread_cell_state};
        let bodies = extract_cell_counter_fixture_bodies();
        let escaping = CellThreadingSpec {
            members: vec!["fm".to_string(), "gm".to_string(), "fm_leak".to_string()],
            references: vec!["fr".to_string(), "gr".to_string()],
            get_fn: "cell_get".to_string(),
            set_fn: "cell_set".to_string(),
        };
        assert!(
            thread_cell_state(&bodies, &escaping).is_none(),
            "a holder that escapes to an out-of-grammar callee must fail closed"
        );
    }

    /// Drift gate: the committed THREADED artifact (`fm/fr/gm/gr` in the
    /// threaded-budget lane shape, consumed by `cell_threading_e2e`) is
    /// byte-identical to `thread_cell_state` applied to the live extraction.
    #[test]
    fn extracted_cell_threaded_artifact_matches_committed() {
        use crate::cell_threading::thread_cell_state;
        let bodies = extract_cell_counter_fixture_bodies();
        let threaded = thread_cell_state(&bodies, &cell_counter_spec())
            .expect("the cell-mediated cluster lowers to the threaded shape");
        assert_eq!(threaded.keys().cloned().collect::<Vec<_>>(), vec!["fm", "fr", "gm", "gr"]);
        assert_matches_committed_artifact("cell_threaded_functions.json", &threaded);
    }

    /// Structural node count of a lowered `Ty`, short-circuited at `cap` so a
    /// pathological (blown-up) tree costs O(cap) to measure rather than hanging.
    /// Used by the step-5 tests to prove the by-name refs keep extraction BOUNDED.
    fn ty_total_node_count(ty: &Ty, cap: usize) -> usize {
        fn go(ty: &Ty, cap: usize, acc: &mut usize) {
            if *acc >= cap {
                return;
            }
            *acc += 1;
            match ty {
                Ty::Datatype { variants, .. } => {
                    for (_, fs) in variants {
                        for (_, t) in fs {
                            go(t, cap, acc);
                        }
                    }
                }
                Ty::Adt { fields, variants, .. } => {
                    for (_, t) in fields {
                        go(t, cap, acc);
                    }
                    for v in variants {
                        for (_, t) in &v.fields {
                            go(t, cap, acc);
                        }
                    }
                }
                Ty::Ref { inner, .. } => go(inner, cap, acc),
                Ty::RawPtr { pointee, .. } => go(pointee, cap, acc),
                Ty::Tuple(ts) => ts.iter().for_each(|t| go(t, cap, acc)),
                _ => {}
            }
        }
        let mut acc = 0;
        go(ty, cap, &mut acc);
        acc
    }

    fn direct_call_symbol_names<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> Vec<String> {
        let typing_env = body.typing_env(tcx);

        body.basic_blocks
            .iter()
            .filter_map(|bb| match &bb.terminator().kind {
                mir::TerminatorKind::Call { func, .. } => match func {
                    mir::Operand::Constant(box const_op) => match const_op.const_.ty().kind() {
                        rustc_middle::ty::TyKind::FnDef(def_id, generic_args) => {
                            rustc_middle::ty::Instance::try_resolve(
                                tcx,
                                typing_env,
                                *def_id,
                                *generic_args,
                            )
                            .ok()
                            .flatten()
                            .map(|instance| tcx.symbol_name(instance).name.to_string())
                        }
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            })
            .collect()
    }

    fn direct_call_func_types<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> Vec<Ty> {
        // Trust: M6 rung-7 sweep — use `body`'s own `typing_env` instead of the
        // plain env-less `convert_ty` (mirrors `direct_call_symbol_names` above,
        // which already computes the same `body.typing_env(tcx)`).
        let typing_env = body.typing_env(tcx);
        body.basic_blocks
            .iter()
            .filter_map(|bb| match &bb.terminator().kind {
                mir::TerminatorKind::Call { func, .. } => match func {
                    mir::Operand::Constant(box const_op)
                        if matches!(
                            const_op.const_.ty().kind(),
                            rustc_middle::ty::TyKind::FnDef(..)
                        ) =>
                    {
                        Some(ty_convert::convert_ty_in_env(tcx, typing_env, const_op.const_.ty()))
                    }
                    _ => None,
                },
                _ => None,
            })
            .collect()
    }

    fn extracted_call_targets(func: &VerifiableFunction) -> Vec<String> {
        func.body
            .blocks
            .iter()
            .filter_map(|bb| match &bb.terminator {
                Terminator::Call { func, .. } => Some(func.clone()),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn codegen_fidelity_validator_recursively_rejects_placeholders() {
        let nested = Ty::Ref {
            mutable: false,
            inner: Box::new(Ty::Tuple(vec![
                Ty::u32(),
                Ty::Unsupported { kind: "test".to_string(), detail: "nested".to_string() },
            ])),
        };
        assert!(
            codegen_ty_issue(&nested, "test type").is_some_and(|detail| detail.contains("nested")),
            "nested unsupported types must not escape the codegen gate"
        );
        assert!(codegen_projection_issue(&Projection::OpaqueCast(Ty::u32())).is_some());
        assert!(codegen_const_issue(&ConstValue::OpaqueConst).is_some());
        assert!(
            codegen_ty_issue(&Ty::Int { width: 128, signed: true }, "signed adversary")
                .is_some_and(|detail| detail.contains("128-bit integer"))
        );
        assert!(
            codegen_ty_issue(&Ty::Bv(128), "bitvector adversary")
                .is_some_and(|detail| detail.contains("128-bit bitvector"))
        );
        assert!(
            codegen_const_issue(&ConstValue::Int(1))
                .is_some_and(|detail| detail.contains("source bit width"))
        );
        assert!(
            codegen_const_issue(&ConstValue::Uint(1, 128))
                .is_some_and(|detail| detail.contains("128-bit unsigned"))
        );
        assert!(
            codegen_const_issue(&ConstValue::Uint(256, 8))
                .is_some_and(|detail| detail.contains("does not fit"))
        );
        assert!(
            codegen_const_issue(&ConstValue::FloatBits { bits: 0, width: 32 })
                .is_some_and(|detail| detail.contains("no executable TrustIr bridge lowering"))
        );
        assert!(codegen_const_issue(&ConstValue::Uint(255, 8)).is_none());
        assert!(
            codegen_const_issue(&ConstValue::CallableItem {
                def_path: "fixture::callback".to_string(),
                kind: CallableKind::FnDef,
                def_path_hash: CallableDefPathHash::new(1, 2),
            })
            .is_some()
        );
    }

    #[test]
    fn codegen_extraction_separates_verifier_abstractions_and_fails_closed() {
        let fixture = extract_codegen_fidelity_fixture();

        // Proof-authority quarantine: production verification extraction must leave
        // Builder::spawn's authenticated callee identity untouched. A forgeable
        // `::<__trust_spawn_namesafe>` suffix must never be emitted, even for the
        // literal, nul-free name shape the retired experimental analysis recognized.
        let spawn = fixture
            .verifier
            .get("spawn_with_literal_name")
            .expect("spawn_with_literal_name should be collected");
        let spawn_targets = extracted_call_targets(spawn);
        assert!(
            spawn_targets.iter().any(|callee| callee.contains("Builder::spawn")),
            "fixture must retain a Builder::spawn call, got {spawn_targets:?}"
        );
        assert!(
            spawn_targets.iter().all(|callee| !callee.contains("__trust_spawn_namesafe")),
            "production extraction must never stamp spawn proof authority: {spawn_targets:?}"
        );

        // The companion value-provenance experiment is retired too: even an Error
        // produced directly by from_raw_os_error keeps its real destruction operation.
        // Depending on the exact std/compiler revision, optimized MIR represents this
        // as either a Drop terminator or the still-authenticated core::mem::drop call.
        // The downstream bridge may fail closed on either shape, but extraction must
        // not turn it into an unauthenticated Goto discharge.
        let drop_os_error =
            fixture.verifier.get("drop_os_error").expect("drop_os_error should be collected");
        let is_io_error_place = |place: &Place| {
            matches!(
                drop_os_error.body.locals.get(place.local).map(|local| &local.ty),
                Some(Ty::Adt { name, .. }) if name.contains("::io::") && name.ends_with("::Error")
            )
        };
        assert!(
            drop_os_error.body.blocks.iter().any(|block| {
                match &block.terminator {
                    Terminator::Drop { place, .. } => is_io_error_place(place),
                    Terminator::Call { func, args, .. }
                        if func.starts_with("core::mem::drop::<")
                            && func.contains("::io::error::Error") =>
                    {
                        matches!(
                            args.as_slice(),
                            [Operand::Move(place) | Operand::Copy(place)] if is_io_error_place(place)
                        )
                    }
                    _ => false,
                }
            }),
            "production extraction must preserve the std::io::Error destruction operation: {drop_os_error:?}"
        );

        fixture
            .codegen
            .get("identity")
            .expect("identity should be collected")
            .as_ref()
            .expect("scalar identity should have a codegen-faithful extraction");

        let verifier_exit = fixture
            .verifier
            .get("exit_now")
            .expect("exit_now should be collected for verification");
        assert!(
            verifier_exit.body.blocks.iter().any(|block| {
                matches!(
                    &block.terminator,
                    Terminator::Opaque { kind, .. }
                        if kind.contains("Call::") && kind.contains("process::exit")
                )
            }),
            "process::exit must retain its real opaque call instead of becoming Return: {verifier_exit:?}"
        );

        let exit = fixture.codegen.get("exit_now").expect("exit_now should be collected");
        assert!(
            matches!(exit, Err(CodegenExtractionError::UnsupportedMir { detail, .. })
                if detail.contains("opaque terminator")
                    && detail.contains("Call::")
                    && detail.contains("process::exit")),
            "process::exit must fail codegen closed as an opaque call, never become a normal return: {exit:?}"
        );

        let unwind =
            fixture.codegen.get("calls_may_panic").expect("calls_may_panic should be collected");
        assert!(
            matches!(unwind, Err(CodegenExtractionError::UnsupportedMir { detail, .. })
                if detail.contains("unwind") || detail.contains("Unwind")),
            "call cleanup/continue semantics must fail closed: {unwind:?}"
        );

        let checked = fixture.codegen.get("checked_add").expect("checked_add should be collected");
        assert!(
            matches!(checked, Err(CodegenExtractionError::UnsupportedMir { detail, .. })
                if detail.contains("Assert") || detail.contains("assert")),
            "assert panic payload/unwind semantics must fail closed: {checked:?}"
        );

        let opaque = fixture.codegen.get("opaque_bytes").expect("opaque_bytes should be collected");
        assert!(
            matches!(opaque, Err(CodegenExtractionError::UnsupportedMir { detail, .. })
                if detail.contains("constant") || detail.contains("symbolic")),
            "opaque constants must fail closed before codegen: {opaque:?}"
        );

        let verifier_derived = fixture
            .verifier
            .get("derived_clone_impl")
            .expect("derived Clone impl should be collected");
        assert!(
            verifier_derived.body.blocks.len() != 1
                || !verifier_derived.body.blocks[0].stmts.is_empty()
                || !matches!(verifier_derived.body.blocks[0].terminator, Terminator::Return),
            "verification mode must preserve the real derived body, never synthetic empty proof input"
        );
        let clone_caller = fixture
            .verifier
            .get("clone_derived")
            .expect("derived Clone caller should be collected");
        let clone_targets = extracted_call_targets(clone_caller);
        assert!(
            clone_targets.iter().any(|callee| {
                callee.ends_with("::clone")
                    && callee.contains("Clone")
                    && callee.contains("Derived")
            }),
            "the derived Clone call must retain its real callee identity: {clone_targets:?}",
        );
        assert!(
            clone_targets.iter().all(|callee| {
                callee != trust_types::total_call_summaries::TRUST_TOTAL_CLONE_SENTINEL
            }),
            "the retired total-Clone sentinel must never appear at a live call site: {clone_targets:?}",
        );
        let raw_codegen_derived = fixture
            .raw_codegen
            .get("derived_clone_impl")
            .expect("raw codegen-purpose derived body should be collected");
        assert!(
            raw_codegen_derived.body.blocks.len() != 1
                || !raw_codegen_derived.body.blocks[0].stmts.is_empty()
                || !matches!(raw_codegen_derived.body.blocks[0].terminator, Terminator::Return),
            "codegen purpose must retain the real derived method body"
        );
        assert!(
            fixture
                .codegen
                .get("derived_clone_impl")
                .expect("derived Clone codegen result should be collected")
                .is_err(),
            "layout-erased derived code must fail closed, never emit havoc/trivial return"
        );
    }

    #[test]
    fn trust_annotation_snippets_parse_conservatively() {
        let boundary = trust_annotations_from_attr_snippet("#[trust(boundary)]");
        assert_eq!(boundary.len(), 1);
        assert_eq!(boundary[0].0, TrustAnnotationKind::Boundary);
        assert!(boundary[0].1.is_empty());

        let model = trust_annotations_from_attr_snippet("#[trust(model)]");
        assert_eq!(model.len(), 1);
        assert_eq!(model[0].0, TrustAnnotationKind::Model);
        assert!(model[0].1.is_empty());

        let assume = trust_annotations_from_attr_snippet(
            "#[trust(assume = \"calls an authenticated gateway\")]",
        );
        assert_eq!(assume.len(), 1);
        assert_eq!(assume[0].0, TrustAnnotationKind::Assumption);
        assert_eq!(assume[0].1, "calls an authenticated gateway");

        let nested = trust_annotations_from_attr_snippet(
            "#[trust(boundary, assume(\"exactly once\"), model)]",
        );
        assert_eq!(nested.len(), 3);
        assert_eq!(nested[0].0, TrustAnnotationKind::Boundary);
        assert_eq!(nested[1].0, TrustAnnotationKind::Assumption);
        assert_eq!(nested[1].1, "exactly once");
        assert_eq!(nested[2].0, TrustAnnotationKind::Model);

        let direct = trust_annotations_from_attr_snippet(
            "#[trust_assume = \"state transitions are explicit\"]",
        );
        assert_eq!(direct.len(), 1);
        assert_eq!(direct[0].0, TrustAnnotationKind::Assumption);
        assert_eq!(direct[0].1, "state transitions are explicit");
    }

    #[test]
    fn trust_annotation_snippets_ignore_unrelated_attrs() {
        assert!(trust_annotations_from_attr_snippet("#[doc = \"hello\"]").is_empty());
        assert!(trust_annotations_from_attr_snippet("#[trust(other)]").is_empty());
    }

    #[test]
    fn extracted_call_targets_use_semantic_paths_not_codegen_symbols() {
        let fixture = extract_call_target_fixture();

        let helper = fixture.functions.get("helper").expect("helper should be extracted");
        let caller = fixture.functions.get("caller").expect("caller should be extracted");
        let exit_wrapper =
            fixture.functions.get("exit_wrapper").expect("exit_wrapper should be extracted");

        assert_eq!(helper.name, "helper");
        assert!(
            helper.def_path.ends_with("::helper"),
            "expected semantic def_path for helper, got `{}`",
            helper.def_path
        );

        let caller_targets = extracted_call_targets(caller);
        assert_eq!(caller_targets, vec![helper.def_path.clone()]);
        assert_ne!(caller_targets[0], helper.name);

        let caller_symbols = fixture
            .direct_call_symbols
            .get("caller")
            .expect("caller direct-call symbols should be captured");
        assert_eq!(caller_symbols.len(), 1);
        assert_ne!(caller_targets[0], caller_symbols[0]);

        let exit_targets = extracted_call_targets(exit_wrapper);
        assert_eq!(exit_targets, vec![helper.def_path.clone()]);

        let exit_symbols = fixture
            .direct_call_symbols
            .get("exit_wrapper")
            .expect("exit_wrapper direct-call symbols should be captured");
        assert_eq!(exit_symbols.len(), 1);
        assert_ne!(exit_targets[0], exit_symbols[0]);
    }

    #[test]
    fn semantic_def_paths_are_crate_qualified_and_injective() {
        let fixture = extract_call_target_fixture();
        let crate_name = "trust_mir_extract_call_target_fixture";
        let root_item = format!("{crate_name}::collision");
        let same_named_module_item = format!("{crate_name}::{crate_name}::collision");

        assert_eq!(fixture.crate_def_path, crate_name);
        assert!(
            fixture.canonical_def_paths.contains(&root_item),
            "{:?}",
            fixture.canonical_def_paths
        );
        assert!(
            fixture.canonical_def_paths.contains(&same_named_module_item),
            "{:?}",
            fixture.canonical_def_paths
        );
        assert_ne!(root_item, same_named_module_item);
    }

    #[test]
    fn generic_call_targets_carry_exact_monomorphization_identity() {
        let fixture = extract_call_target_fixture();
        let caller = fixture
            .functions
            .get("mixed_generic_calls")
            .expect("mixed generic caller should be extracted");
        let targets = extracted_call_targets(caller);
        assert_eq!(targets.len(), 2, "{targets:?}");
        assert_ne!(targets[0], targets[1]);
        assert!(targets.iter().any(|target| target.contains("identity::<bool>")), "{targets:?}");
        assert!(targets.iter().any(|target| target.contains("identity::<i32>")), "{targets:?}");
    }

    #[test]
    fn function_item_call_operands_lower_to_fndef_types() {
        let fixture = extract_call_target_fixture();
        let caller = fixture.functions.get("caller").expect("caller should be extracted");
        let helper = fixture.functions.get("helper").expect("helper should be extracted");
        let call_types = fixture
            .direct_call_func_types
            .get("caller")
            .expect("caller direct-call function types should be captured");

        assert_eq!(call_types.len(), 1);
        let Ty::FnDef { name, sig } = &call_types[0] else {
            panic!("expected direct-call operand to lower as FnDef, got {:?}", call_types[0]);
        };
        assert_eq!(name, &helper.def_path);
        assert!(sig.params.is_empty(), "helper takes no arguments: {sig:?}");
        assert_eq!(*sig.ret, Ty::i32());
        assert!(
            caller.body.locals.iter().all(|local| !matches!(local.ty, Ty::Unsupported { .. })),
            "callable type lowering should not inject Unsupported locals in caller: {:?}",
            caller.body.locals
        );
    }

    #[test]
    fn function_pointer_return_type_lowers_to_fnptr_signature() {
        let fixture = extract_call_target_fixture();
        let function =
            fixture.functions.get("helper_fn_ptr").expect("helper_fn_ptr should be extracted");

        let Ty::FnPtr { sig } = &function.body.return_ty else {
            panic!(
                "expected helper_fn_ptr return type to lower as FnPtr, got {:?}",
                function.body.return_ty
            );
        };
        assert!(sig.params.is_empty(), "helper function pointer takes no arguments: {sig:?}");
        assert_eq!(*sig.ret, Ty::i32());
    }

    #[test]
    fn dyn_trait_references_lower_to_dynamic_pointees() {
        let fixture = extract_call_target_fixture();
        let function =
            fixture.functions.get("dyn_debug_ref").expect("dyn_debug_ref should be extracted");

        let Ty::Ref { inner: ret_inner, .. } = &function.body.return_ty else {
            panic!(
                "expected dyn_debug_ref return type to be a reference, got {:?}",
                function.body.return_ty
            );
        };
        let Ty::Dynamic { trait_name } = ret_inner.as_ref() else {
            panic!("expected dyn_debug_ref return pointee to be Dynamic, got {ret_inner:?}");
        };
        assert_eq!(trait_name, "trust_mir_extract_call_target_fixture::LocalDebug");

        let arg = function
            .body
            .locals
            .iter()
            .find(|local| local.index == 1)
            .expect("dyn_debug_ref argument local should be present");
        let Ty::Ref { inner: arg_inner, .. } = &arg.ty else {
            panic!("expected dyn_debug_ref argument to be a reference, got {:?}", arg.ty);
        };
        assert!(matches!(arg_inner.as_ref(), Ty::Dynamic { .. }));
    }

    // Tests for parse_contract_specs

    #[test]
    fn parse_contract_specs_extracts_requires_as_preconditions() {
        let contracts = vec![Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "x > 0".to_string(),
        }];
        let (pre, post) = parse_contract_specs(&contracts);
        assert_eq!(pre.len(), 1);
        assert!(post.is_empty());
        assert_eq!(
            pre[0],
            Formula::Gt(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )
        );
    }

    #[test]
    fn parse_contract_specs_extracts_ensures_as_postconditions() {
        let contracts = vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: "result >= 0".to_string(),
        }];
        let (pre, post) = parse_contract_specs(&contracts);
        assert!(pre.is_empty());
        assert_eq!(post.len(), 1);
        // "result" maps to "_0" in the spec parser
        assert_eq!(
            post[0],
            Formula::Ge(
                Box::new(Formula::Var("_0".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )
        );
    }

    #[test]
    fn parse_contract_specs_extracts_closure_ensures_as_postconditions() {
        let contracts = vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: "|ret: &i32| *ret >= 0".to_string(),
        }];
        let (pre, post) = parse_contract_specs(&contracts);
        assert!(pre.is_empty());
        assert_eq!(post.len(), 1);
        assert_eq!(
            post[0],
            Formula::Ge(
                Box::new(Formula::Var("_0".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )
        );
    }

    /// Closure-contract decompilation for a STRUCT-FIELD-referencing ensures:
    /// `|ret: &i32| *ret == p.value` normalizes to `result == p.value` and parses
    /// (general field projection) to `Eq(_0, Var("p.value"))`. Combined with the
    /// reflection/inhabitation field-projection grounding, this lets a real
    /// struct-accessor closure contract become a kernel-proven dependent type.
    #[test]
    fn parse_contract_specs_extracts_field_referencing_closure_ensures() {
        let contracts = vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: "|ret: &i32| *ret == p.value".to_string(),
        }];
        let (pre, post) = parse_contract_specs(&contracts);
        assert!(pre.is_empty());
        assert_eq!(post.len(), 1, "field-referencing closure ensures must no longer be dropped");
        assert_eq!(
            post[0],
            Formula::Eq(
                Box::new(Formula::Var("_0".to_string(), Sort::Int)),
                Box::new(Formula::Var("p.value".to_string(), Sort::Int)),
            )
        );
    }

    #[test]
    fn parse_contract_specs_handles_multiple_contracts() {
        let contracts = vec![
            Contract {
                kind: ContractKind::Requires,
                span: SourceSpan::default(),
                body: "n > 0".to_string(),
            },
            Contract {
                kind: ContractKind::Requires,
                span: SourceSpan::default(),
                body: "n < 100".to_string(),
            },
            Contract {
                kind: ContractKind::Ensures,
                span: SourceSpan::default(),
                body: "result >= n".to_string(),
            },
        ];
        let (pre, post) = parse_contract_specs(&contracts);
        assert_eq!(pre.len(), 2);
        assert_eq!(post.len(), 1);
    }

    #[test]
    fn parse_contract_specs_consumes_unique_exact_typed_proposition() {
        let contract = Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}result == x"),
        };
        let typed = Formula::Eq(
            Box::new(Formula::Var("_0".to_string(), Sort::Int)),
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
        );
        let compiler_contracts = CompilerContractBundle::new(vec![contract.clone()])
            .with_typed_propositions(vec![CompilerContractProposition {
                source_contract_index: 0,
                kind: contract.kind,
                body: contract.body.clone(),
                formula: typed.clone(),
                variable_domains: vec![
                    trust_types::CompilerContractVariableDomain {
                        name: "_0".to_string(),
                        domain: trust_types::CompilerContractValueDomain::MathematicalInt,
                    },
                    trust_types::CompilerContractVariableDomain {
                        name: "x".to_string(),
                        domain: trust_types::CompilerContractValueDomain::MathematicalInt,
                    },
                ],
            }]);

        let (pre, post) = parse_contract_specs_with_typed(&[contract], Some(&compiler_contracts));
        assert!(pre.is_empty());
        assert_eq!(post, vec![typed]);
    }

    #[test]
    fn typed_compiler_predicate_conversion_rejects_prefix_or_structure_drift() {
        use rustc_middle::mir::trust_contract::{
            TrustContractPredicateKind, TrustContractProposition as Proposition,
            TrustContractPropositionDomain as Domain,
        };

        rustc_span::create_default_session_globals_then(|| {
            let exact = TrustContractPredicateKind::Typed {
                text: Symbol::intern("__trust_lowered_compiler_contract__:x == 0"),
                proposition: Proposition::Eq(
                    Box::new(Proposition::Var {
                        name: Symbol::intern("x"),
                        domain: Domain::MachineInt { width: 8, signed: false },
                    }),
                    Box::new(Proposition::Int(0)),
                ),
            };
            assert_eq!(
                convert_trust_contract_predicate(0, &exact),
                Ok((
                    "__trust_lowered_compiler_contract__:x == 0".to_string(),
                    Some((
                        Formula::Eq(
                            Box::new(Formula::Var("x".to_string(), Sort::Int)),
                            Box::new(Formula::Int(0)),
                        ),
                        vec![trust_types::CompilerContractVariableDomain {
                            name: "x".to_string(),
                            domain: trust_types::CompilerContractValueDomain::MachineInt {
                                width: 8,
                                signed: false,
                            },
                        }],
                    )),
                ))
            );

            let missing_prefix = TrustContractPredicateKind::Typed {
                text: Symbol::intern("x == 0"),
                proposition: Proposition::Eq(
                    Box::new(Proposition::Var {
                        name: Symbol::intern("x"),
                        domain: Domain::MachineInt { width: 8, signed: false },
                    }),
                    Box::new(Proposition::Int(0)),
                ),
            };
            assert!(convert_trust_contract_predicate(0, &missing_prefix).is_err());

            let structural_drift = TrustContractPredicateKind::Typed {
                text: Symbol::intern("__trust_lowered_compiler_contract__:x == 0"),
                proposition: Proposition::Le(
                    Box::new(Proposition::Var {
                        name: Symbol::intern("x"),
                        domain: Domain::MachineInt { width: 8, signed: false },
                    }),
                    Box::new(Proposition::Int(0)),
                ),
            };
            assert!(convert_trust_contract_predicate(0, &structural_drift).is_err());
        });
    }

    #[test]
    fn bool_literal_typed_row_uses_canonical_compiler_prefix() {
        use rustc_middle::mir::trust_contract::TrustContractPredicateKind;

        assert_eq!(
            convert_trust_contract_predicate(
                0,
                &TrustContractPredicateKind::BoolLiteral { value: true },
            ),
            Ok((
                format!("{LOWERED_COMPILER_CONTRACT_PREFIX}true"),
                Some((Formula::Bool(true), Vec::new())),
            ))
        );
    }

    #[test]
    fn direct_call_collection_length_uses_canonical_summary_symbol() {
        let slice =
            Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) };
        let source = Formula::Gt(
            Box::new(Formula::Var("xs_len".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let canonical =
            canonicalize_entry_collection_lengths(source, &[("xs".to_string(), slice.clone())])
                .expect("an unambiguous slice accessor must canonicalize");
        assert_eq!(
            canonical,
            Formula::Gt(
                Box::new(Formula::Var("xs__slice_len".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )
        );

        let collision = canonicalize_entry_collection_lengths(
            Formula::Var("xs_len".to_string(), Sort::Int),
            &[("xs".to_string(), slice), ("xs_len".to_string(), Ty::usize())],
        )
        .expect_err("a real parameter must never alias the generated accessor leaf");
        assert!(collision.contains("collides"), "unexpected rejection: {collision}");
    }

    #[test]
    fn parse_contract_specs_rejects_duplicate_or_stale_typed_provenance() {
        let requires = Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}x > 0"),
        };
        let exact = CompilerContractProposition {
            source_contract_index: 0,
            kind: requires.kind,
            body: requires.body.clone(),
            formula: Formula::Gt(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            variable_domains: vec![trust_types::CompilerContractVariableDomain {
                name: "x".to_string(),
                domain: trust_types::CompilerContractValueDomain::MathematicalInt,
            }],
        };
        let mut stale = exact.clone();
        stale.body.push_str(" && true");
        let compiler_contracts = CompilerContractBundle::new(vec![requires.clone()])
            .with_typed_propositions(vec![exact, stale]);

        let (pre, post) = parse_contract_specs_with_typed(&[requires], Some(&compiler_contracts));
        assert_eq!(pre, vec![Formula::Bool(false)]);
        assert!(post.is_empty());
    }

    #[test]
    fn parse_contract_specs_rejects_formula_drift_with_exact_provenance_fields() {
        let requires = Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}x > 0"),
        };
        let compiler_contracts = CompilerContractBundle::new(vec![requires.clone()])
            .with_typed_propositions(vec![CompilerContractProposition {
                source_contract_index: 0,
                kind: requires.kind,
                body: requires.body.clone(),
                formula: Formula::Le(
                    Box::new(Formula::Var("x".to_string(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                variable_domains: vec![trust_types::CompilerContractVariableDomain {
                    name: "x".to_string(),
                    domain: trust_types::CompilerContractValueDomain::MathematicalInt,
                }],
            }]);

        let (pre, post) = parse_contract_specs_with_typed(&[requires], Some(&compiler_contracts));
        assert_eq!(pre, vec![Formula::Bool(false)]);
        assert!(post.is_empty());
    }

    #[test]
    fn parse_contract_specs_fails_closed_on_unparseable_requires() {
        let contracts = vec![Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "???invalid".to_string(),
        }];
        let (pre, post) = parse_contract_specs(&contracts);
        assert_eq!(pre, vec![Formula::Bool(false)]);
        assert!(post.is_empty());
    }

    #[test]
    fn parse_contract_specs_fails_closed_on_empty_requires() {
        let contracts = vec![Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "  ".to_string(),
        }];
        let (pre, post) = parse_contract_specs(&contracts);
        assert_eq!(pre, vec![Formula::Bool(false)]);
        assert!(post.is_empty());
    }

    #[test]
    fn parse_contract_specs_ignores_invariant_and_decreases() {
        let contracts = vec![
            Contract {
                kind: ContractKind::Invariant,
                span: SourceSpan::default(),
                body: "x > 0".to_string(),
            },
            Contract {
                kind: ContractKind::Decreases,
                span: SourceSpan::default(),
                body: "n".to_string(),
            },
        ];
        let (pre, post) = parse_contract_specs(&contracts);
        assert!(pre.is_empty());
        assert!(post.is_empty());
    }

    // Trust: #472 — Additional tests to increase test density

    // --- contract_body_from_attr_snippet tests ---

    #[test]
    fn test_contract_body_from_attr_snippet_parenthesized() {
        assert_eq!(contract_body_from_attr_snippet("#[requires(x > 0)]"), "x > 0");
    }

    #[test]
    fn test_contract_body_from_attr_snippet_with_quotes() {
        assert_eq!(
            contract_body_from_attr_snippet("#[ensures(\"result >= 0\")]"),
            "\"result >= 0\""
        );
    }

    #[test]
    fn test_contract_body_from_attr_snippet_eq_form() {
        assert_eq!(contract_body_from_attr_snippet("#[requires = \"x > 0\"]"), "x > 0");
    }

    #[test]
    fn test_contract_body_from_attr_snippet_no_body_returns_empty() {
        assert_eq!(contract_body_from_attr_snippet("#[requires]"), "");
    }

    #[test]
    fn test_contract_body_from_attr_snippet_raw_text() {
        // No #[...] wrapper
        assert_eq!(contract_body_from_attr_snippet("requires(a + b < c)"), "a + b < c");
    }

    #[test]
    fn test_contract_body_from_attr_snippet_nested_parens() {
        assert_eq!(contract_body_from_attr_snippet("#[requires(f(x) > g(y))]"), "f(x) > g(y)");
    }

    #[test]
    fn test_contract_body_from_attr_snippet_whitespace_trimmed() {
        assert_eq!(contract_body_from_attr_snippet("  #[requires(  a > b  )]  "), "a > b");
    }

    #[test]
    fn test_contract_kind_from_name_supports_namespaced_requires() {
        assert_eq!(contract_kind_from_name("trust::requires"), Some(ContractKind::Requires));
    }

    #[test]
    fn test_contract_kind_from_name_supports_namespaced_ensures() {
        assert_eq!(contract_kind_from_name("trust::ensures"), Some(ContractKind::Ensures));
    }

    #[test]
    fn test_normalized_contract_spec_body_unquotes_string_literal() {
        assert_eq!(
            normalized_contract_spec_body(ContractKind::Requires, "\"x > 0\""),
            Some("x > 0".to_string())
        );
    }

    #[test]
    fn test_normalized_contract_spec_body_maps_ensures_closure_to_result() {
        assert_eq!(
            normalized_contract_spec_body(ContractKind::Ensures, "move |ret: &i32| { *ret >= 0 }"),
            Some("result >= 0".to_string())
        );
    }

    // --- strip_string_literal tests ---

    #[test]
    fn test_strip_string_literal_removes_quotes() {
        assert_eq!(strip_string_literal("\"hello world\""), "hello world");
    }

    #[test]
    fn test_strip_string_literal_no_quotes_passthrough() {
        assert_eq!(strip_string_literal("no_quotes"), "no_quotes");
    }

    #[test]
    fn test_strip_string_literal_empty_quoted() {
        assert_eq!(strip_string_literal("\"\""), "");
    }

    #[test]
    fn test_strip_string_literal_trims_whitespace() {
        assert_eq!(strip_string_literal("  \"trimmed\"  "), "trimmed");
    }

    #[test]
    fn test_strip_string_literal_single_quote_no_strip() {
        // Only matching double quotes are stripped
        assert_eq!(strip_string_literal("\"unmatched"), "\"unmatched");
    }

    // --- trust_annotation_from_item tests ---

    #[test]
    fn test_trust_annotation_from_item_boundary() {
        let result = trust_annotation_from_item("boundary");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Boundary);
        assert!(result[0].1.is_empty());
    }

    #[test]
    fn test_trust_annotation_from_item_trust_boundary() {
        let result = trust_annotation_from_item("trust_boundary");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Boundary);
    }

    #[test]
    fn test_trust_annotation_from_item_model() {
        let result = trust_annotation_from_item("model");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Model);
        assert!(result[0].1.is_empty());
    }

    #[test]
    fn test_trust_annotation_from_item_trust_model() {
        let result = trust_annotation_from_item("trust_model");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Model);
    }

    #[test]
    fn test_trust_annotation_from_item_assume_empty() {
        let result = trust_annotation_from_item("assume");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Assumption);
        assert!(result[0].1.is_empty());
    }

    #[test]
    fn test_trust_annotation_from_item_assume_with_parens() {
        let result = trust_annotation_from_item("assume(\"safe by design\")");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Assumption);
        assert_eq!(result[0].1, "safe by design");
    }

    #[test]
    fn test_trust_annotation_from_item_assume_with_eq() {
        let result = trust_annotation_from_item("assume = \"always valid\"");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Assumption);
        assert_eq!(result[0].1, "always valid");
    }

    #[test]
    fn test_trust_annotation_from_item_empty_returns_empty() {
        assert!(trust_annotation_from_item("").is_empty());
    }

    #[test]
    fn test_trust_annotation_from_item_unknown_returns_empty() {
        assert!(trust_annotation_from_item("whatever").is_empty());
        assert!(trust_annotation_from_item("debug").is_empty());
        assert!(trust_annotation_from_item("inline").is_empty());
    }

    // --- contract_panic (T9) tests ---

    #[test]
    fn test_contract_panic_item_well_formed_extracts_payload() {
        for item in [
            "contract_panic(message_contains = \"capacity is\")",
            "trust_contract_panic(message_contains = \"capacity is\")",
            "trust::contract_panic(message_contains = \"capacity is\")",
            "contract_panic( message_contains=\"capacity is\" )",
        ] {
            let result = trust_annotation_from_item(item);
            assert_eq!(result.len(), 1, "item `{item}` should extract");
            assert_eq!(result[0].0, TrustAnnotationKind::ContractPanic);
            assert_eq!(result[0].1, "capacity is");
        }
    }

    #[test]
    fn test_contract_panic_nested_in_trust_list() {
        let anns = trust_annotations_from_attr_snippet(
            "#[trust(boundary, contract_panic(message_contains = \"lock poisoned, or\"))]",
        );
        assert_eq!(anns.len(), 2);
        assert_eq!(anns[0].0, TrustAnnotationKind::Boundary);
        assert_eq!(anns[1].0, TrustAnnotationKind::ContractPanic);
        // The depth/string-aware splitter must keep a comma INSIDE the payload.
        assert_eq!(anns[1].1, "lock poisoned, or");
    }

    #[test]
    fn test_contract_panic_tool_attr_snippet_form() {
        let anns = trust_annotations_from_attr_snippet(
            "#[trust::contract_panic(message_contains = \"ArrayVec overflow\")]",
        );
        assert_eq!(anns.len(), 1);
        assert_eq!(anns[0].0, TrustAnnotationKind::ContractPanic);
        assert_eq!(anns[0].1, "ArrayVec overflow");
    }

    #[test]
    fn test_contract_panic_malformed_payload_is_error_not_silent_drop() {
        // Every malformed spelling must (a) extract NOTHING and (b) produce an
        // extraction error via `contract_panic_extraction_errors` — the silent
        // unknown-item drop is the anti-pattern for a recognized-but-broken
        // contract annotation.
        for snippet in [
            "#[trust(contract_panic)]",                            // no payload
            "#[trust(contract_panic())]",                          // empty parens
            "#[trust(contract_panic(message_contains))]",          // no value
            "#[trust(contract_panic(message_contains = ))]",       // no literal
            "#[trust(contract_panic(message_contains = \"\"))]",   // empty payload
            "#[trust(contract_panic(message_contains = \"  \"))]", // blank payload
            "#[trust(contract_panic(message_contains = bare))]",   // unquoted
            "#[trust(contract_panic(substring = \"x\"))]",         // wrong key
            "#[trust::contract_panic]",                            // tool form, no payload
        ] {
            assert!(
                trust_annotations_from_attr_snippet(snippet).is_empty(),
                "malformed `{snippet}` must not extract an annotation"
            );
            assert_eq!(
                contract_panic_extraction_errors(snippet).len(),
                1,
                "malformed `{snippet}` must produce exactly one extraction error"
            );
        }
    }

    #[test]
    fn test_contract_panic_well_formed_produces_no_errors() {
        for snippet in [
            "#[trust(contract_panic(message_contains = \"capacity is\"))]",
            "#[trust::contract_panic(message_contains = \"capacity is\")]",
            "#[trust(boundary)]",
            "#[doc = \"hello\"]",
            "#[trust(other)]", // unknown items stay silently dropped, not errors
        ] {
            assert!(
                contract_panic_extraction_errors(snippet).is_empty(),
                "`{snippet}` must not produce contract_panic errors"
            );
        }
    }

    #[test]
    fn test_contract_panic_prefix_collision_is_not_recognized() {
        // An identifier that merely SHARES the prefix is not a contract_panic
        // item: it must neither extract nor error (ordinary unknown-item drop).
        assert!(trust_annotation_from_item("contract_panicky").is_empty());
        assert!(contract_panic_extraction_errors("#[trust(contract_panicky)]").is_empty());
    }

    // --- trust_assumption_body tests ---

    #[test]
    fn test_trust_assumption_body_bare_assume() {
        assert_eq!(trust_assumption_body("assume"), Some(String::new()));
    }

    #[test]
    fn test_trust_assumption_body_trust_assume() {
        assert_eq!(trust_assumption_body("trust_assume"), Some(String::new()));
    }

    #[test]
    fn test_trust_assumption_body_paren_form() {
        assert_eq!(trust_assumption_body("assume(\"reason\")"), Some("reason".to_string()));
    }

    #[test]
    fn test_trust_assumption_body_eq_form() {
        assert_eq!(trust_assumption_body("assume = \"reason\""), Some("reason".to_string()));
    }

    #[test]
    fn test_trust_assumption_body_trust_assume_paren() {
        assert_eq!(trust_assumption_body("trust_assume(\"safe\")"), Some("safe".to_string()));
    }

    #[test]
    fn test_trust_assumption_body_not_assume_returns_none() {
        assert_eq!(trust_assumption_body("boundary"), None);
        assert_eq!(trust_assumption_body("model"), None);
        assert_eq!(trust_assumption_body("other"), None);
    }

    // --- split_trust_annotation_items tests ---

    #[test]
    fn test_split_trust_annotation_items_single() {
        let items = split_trust_annotation_items("boundary");
        assert_eq!(items, vec!["boundary"]);
    }

    #[test]
    fn test_split_trust_annotation_items_multiple() {
        let items = split_trust_annotation_items("boundary, model, assume");
        assert_eq!(items, vec!["boundary", "model", "assume"]);
    }

    #[test]
    fn test_split_trust_annotation_items_nested_parens() {
        let items = split_trust_annotation_items("assume(\"a, b\"), model");
        assert_eq!(items, vec!["assume(\"a, b\")", "model"]);
    }

    #[test]
    fn test_split_trust_annotation_items_empty() {
        let items = split_trust_annotation_items("");
        assert!(items.is_empty());
    }

    #[test]
    fn test_split_trust_annotation_items_escaped_strings() {
        let items = split_trust_annotation_items("assume(\"contains \\\"escaped\\\"\"), boundary");
        assert_eq!(items.len(), 2);
        assert_eq!(items[1], "boundary");
    }

    // --- trust_annotations_from_attr_body tests ---

    #[test]
    fn test_trust_annotations_from_attr_body_trust_wrapper() {
        let anns = trust_annotations_from_attr_body("trust(boundary)");
        assert_eq!(anns.len(), 1);
        assert_eq!(anns[0].0, TrustAnnotationKind::Boundary);
    }

    #[test]
    fn test_trust_annotations_from_attr_body_direct_item() {
        let anns = trust_annotations_from_attr_body("boundary");
        assert_eq!(anns.len(), 1);
        assert_eq!(anns[0].0, TrustAnnotationKind::Boundary);
    }

    #[test]
    fn test_trust_annotations_from_attr_body_trust_multi() {
        let anns = trust_annotations_from_attr_body("trust(boundary, model)");
        assert_eq!(anns.len(), 2);
        assert_eq!(anns[0].0, TrustAnnotationKind::Boundary);
        assert_eq!(anns[1].0, TrustAnnotationKind::Model);
    }

    // --- parse_contract_specs edge cases ---

    #[test]
    fn test_parse_contract_specs_empty_contracts() {
        let (pre, post) = parse_contract_specs(&[]);
        assert!(pre.is_empty());
        assert!(post.is_empty());
    }

    #[test]
    fn test_parse_contract_specs_mixed_valid_invalid() {
        let contracts = vec![
            Contract {
                kind: ContractKind::Requires,
                span: SourceSpan::default(),
                body: "x > 0".to_string(),
            },
            Contract {
                kind: ContractKind::Requires,
                span: SourceSpan::default(),
                body: "???invalid".to_string(),
            },
            Contract {
                kind: ContractKind::Ensures,
                span: SourceSpan::default(),
                body: "result == 1".to_string(),
            },
        ];
        let (pre, post) = parse_contract_specs(&contracts);
        assert_eq!(pre.len(), 2, "invalid requires must remain an explicit caller obligation");
        assert!(pre.iter().any(|formula| formula == &Formula::Bool(false)));
        assert_eq!(post.len(), 1, "valid ensures should be parsed");
    }

    #[test]
    fn test_parse_contract_specs_only_whitespace_body() {
        let contracts = vec![Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "\t\n  ".to_string(),
        }];
        let (pre, post) = parse_contract_specs(&contracts);
        assert_eq!(pre, vec![Formula::Bool(false)]);
        assert!(post.is_empty());
    }

    // --- trust_annotations_from_attr_snippet edge cases ---

    #[test]
    fn test_trust_annotations_from_attr_snippet_empty() {
        assert!(trust_annotations_from_attr_snippet("").is_empty());
    }

    #[test]
    fn test_trust_annotations_from_attr_snippet_whitespace_only() {
        assert!(trust_annotations_from_attr_snippet("   ").is_empty());
    }

    #[test]
    fn test_trust_annotations_from_attr_snippet_trust_assume_eq_form() {
        let result =
            trust_annotations_from_attr_snippet("#[trust_assume = \"sound by construction\"]");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Assumption);
        assert_eq!(result[0].1, "sound by construction");
    }

    #[test]
    fn test_trust_annotations_from_attr_snippet_bare_boundary() {
        let result = trust_annotations_from_attr_snippet("boundary");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Boundary);
    }

    #[test]
    fn convert_trust_contract_bundle_maps_supported_requires_ensures_payloads() {
        let fixture = extract_contract_fixture();
        let converted = &fixture.conversion.supported.contracts;

        assert_eq!(converted.len(), 2);
        assert_eq!(converted[0].kind, ContractKind::Requires);
        assert_eq!(converted[0].body, "x > 0");
        assert_eq!(converted[0].span, SourceSpan::default());
        assert_eq!(converted[1].kind, ContractKind::Ensures);
        assert_eq!(converted[1].body, format!("{LOWERED_COMPILER_CONTRACT_PREFIX}true"));
    }

    #[test]
    fn convert_trust_contract_bundle_accepts_empty_bundle() {
        let fixture = extract_contract_fixture();
        assert!(fixture.conversion.empty.contracts.is_empty());
    }

    #[test]
    fn convert_trust_contract_bundle_maps_function_decreases() {
        rustc_span::create_default_session_globals_then(|| {
            let index = 7;
            assert_eq!(
                convert_trust_contract_kind(index, TrustContractKind::Decreases),
                Ok(ContractKind::Decreases)
            );
            assert_eq!(
                convert_trust_contract_subject(index, TrustContractSubject::Function),
                Ok(())
            );
            let (body, proposition) = convert_trust_contract_predicate(
                index,
                &TrustContractPredicateKind::Opaque { text: sym::trust_test_contract_x_gt_zero },
            )
            .expect("function decreases payload should remain visible");
            assert_eq!(body, "x > 0");
            assert_eq!(proposition, None);
            assert_eq!(
                convert_trust_contract_kind(index, TrustContractKind::Invariant),
                Err(TrustContractBundleConversionError::UnsupportedContractKind {
                    index,
                    kind: "Invariant".to_string(),
                })
            );
        });
    }

    #[test]
    fn convert_trust_contract_bundle_preserves_unsupported_predicates_fail_closed() {
        let fixture = extract_contract_fixture();

        assert_eq!(fixture.conversion.unsupported.contracts.len(), 1);
        assert_eq!(fixture.conversion.unsupported.contracts[0].kind, ContractKind::Requires);
        assert_eq!(
            fixture.conversion.unsupported.contracts[0].body,
            format!("{UNSUPPORTED_COMPILER_CONTRACT_PREFIX}not_lowered")
        );
        assert_eq!(
            fixture.conversion.mir_local_error,
            Some(TrustContractBundleConversionError::MirLocalPredicate { index: 0, local: 1 })
        );
        assert_eq!(
            fixture.conversion.unsupported_kind_error,
            Some(TrustContractBundleConversionError::UnsupportedContractKind {
                index: 0,
                kind: "Invariant".to_string(),
            })
        );
        assert_eq!(
            fixture.conversion.nonconvertible_error,
            Some(TrustContractBundleConversionError::NonConvertibleNonEmptyBundle {
                summary_total: 1,
            })
        );
    }

    #[test]
    fn loop_contract_bundles_count_metadata_and_convert_into_parallel_lane() {
        let fixture = extract_contract_fixture();

        assert!(!fixture.conversion.loop_only_is_empty);
        assert_eq!(fixture.conversion.loop_only_len, 2);
        assert_eq!(fixture.conversion.loop_only_iter_count, 2);

        // E4/E5: authored loop clauses convert into the parallel
        // `loop_contracts` lane — never dropped, never silently merged into
        // the dense function-contract index. Unsupported predicate payloads
        // keep their explicit fail-closed marker so the vcgen pairing lane
        // (`bind_compiler_loop_contracts`) rejects them loudly.
        assert!(fixture.conversion.loop_only.contracts.is_empty());
        assert_eq!(fixture.conversion.loop_only.loop_contracts.len(), 2);
        assert_eq!(
            fixture.conversion.loop_only.loop_contracts[0].kind,
            trust_types::LoopContractKind::Invariant
        );
        assert_eq!(
            fixture.conversion.loop_only.loop_contracts[1].kind,
            trust_types::LoopContractKind::Decreases
        );
        assert!(
            fixture.conversion.loop_only.loop_contracts[0]
                .body
                .starts_with(UNSUPPORTED_COMPILER_CONTRACT_PREFIX)
        );

        assert_eq!(fixture.conversion.mixed_loop.contracts.len(), 2);
        assert_eq!(fixture.conversion.mixed_loop.loop_contracts.len(), 1);
        assert_eq!(
            fixture.conversion.mixed_loop.loop_contracts[0].kind,
            trust_types::LoopContractKind::Invariant
        );

        assert_eq!(
            fixture.conversion.mixed_loop_caller_fallback,
            (vec![Formula::Bool(false)], Vec::new()),
            "a conversion failure must still preserve a declared requires as an impossible caller obligation and withhold ensures",
        );
        assert_eq!(fixture.conversion.mixed_loop.contracts.len(), 2);
        assert_eq!(fixture.conversion.mixed_loop.loop_contracts.len(), 1);
    }

    #[test]
    fn current_rustc_contract_query_lowers_simple_comparison_predicate() {
        let fixture = extract_contract_fixture();
        let query_contracts =
            fixture.query_contracts.expect("reciprocal query contracts should convert");

        assert_eq!(query_contracts.contracts.len(), 1);
        assert_eq!(query_contracts.contracts[0].kind, ContractKind::Requires);
        assert_eq!(
            query_contracts.contracts[0].body,
            format!("{LOWERED_COMPILER_CONTRACT_PREFIX}(n) > (0)")
        );
        assert_eq!(
            normalized_contract_spec_body(
                query_contracts.contracts[0].kind,
                &query_contracts.contracts[0].body
            ),
            Some("(n) > (0)".to_string())
        );
    }

    #[test]
    fn compiler_contract_attrs_extract_into_pre_and_postconditions() {
        let fixture = extract_contract_fixture();
        let functions = &fixture.functions;

        let reciprocal = functions.get("reciprocal").expect("reciprocal should be extracted");
        assert_eq!(reciprocal.contracts.len(), 1);
        assert_eq!(
            reciprocal.contracts[0].body,
            format!("{LOWERED_COMPILER_CONTRACT_PREFIX}(n) > (0)")
        );
        assert_eq!(reciprocal.spec.requires, vec!["(n) > (0)".to_string()]);
        assert_eq!(
            reciprocal.preconditions,
            vec![
                Formula::Gt(
                    Box::new(Formula::Var("n".to_string(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                Formula::And(vec![
                    Formula::Ge(
                        Box::new(Formula::Var("n".to_string(), Sort::Int)),
                        Box::new(Formula::Int(0)),
                    ),
                    Formula::Le(
                        Box::new(Formula::Var("n".to_string(), Sort::Int)),
                        Box::new(Formula::Int(u32::MAX.into())),
                    ),
                ]),
            ]
        );

        let abs_broken = functions.get("abs_broken").expect("abs_broken should be extracted");
        assert_eq!(abs_broken.contracts.len(), 1);
        assert_eq!(
            abs_broken.contracts[0].body,
            format!("{LOWERED_COMPILER_CONTRACT_PREFIX}(result) >= (0)")
        );
        assert_eq!(abs_broken.spec.ensures, vec!["(result) >= (0)".to_string()]);
        assert_eq!(
            abs_broken.postconditions,
            vec![Formula::Ge(
                Box::new(Formula::Var("_0".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )]
        );

        let reciprocal_metadata =
            fixture.metadata.get("reciprocal").expect("reciprocal metadata should be extracted");
        assert!(!reciprocal_metadata.contract_extraction.source_scraping_used);
        // This fixture mirrors the production verifier path by converting and
        // passing rustc's typed `trust_contracts` query bundle. Deleting the
        // compat/debug scraper must preserve that stronger provenance label.
        assert_eq!(
            reciprocal_metadata.contract_extraction.source,
            ContractExtractionSource::CompilerContractBundle
        );
        // R2 deletion D-B: proof items come exclusively from the compiler-owned
        // bundle; no HIR-attribute proof import runs, so plain contract-bearing
        // functions carry no imported proof items.
        assert!(reciprocal_metadata.proof_items.is_empty());
    }

    #[test]
    fn empty_compiler_contract_bundle_does_not_invent_consumed_hir_contract_attrs() {
        let fixture = extract_contract_fixture();
        let reciprocal = fixture
            .empty_bundle_metadata
            .get("reciprocal")
            .expect("reciprocal metadata should be extracted with empty bundle");

        assert!(reciprocal.contracts.is_empty());
        assert!(reciprocal.spec.requires.is_empty());
        assert_eq!(reciprocal.contract_extraction.source, ContractExtractionSource::Unavailable);
        assert!(!reciprocal.contract_extraction.source_scraping_used);
        assert!(
            reciprocal
                .contract_extraction
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains(
                    "native contract facts unavailable; compatibility source scraping disabled"
                )),
            "expected fail-closed diagnostic, got {:?}",
            reciprocal.contract_extraction.diagnostics
        );
    }

    #[test]
    fn native_no_contract_bundle_fails_closed_without_source_scraping() {
        let fixture = extract_contract_fixture();
        let no_contracts = fixture
            .metadata
            .get("no_contracts")
            .expect("no_contracts metadata should be extracted");

        assert!(no_contracts.contracts.is_empty());
        assert_eq!(no_contracts.contract_extraction.source, ContractExtractionSource::Unavailable);
        assert!(!no_contracts.contract_extraction.source_scraping_used);
        assert!(
            no_contracts
                .contract_extraction
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains(
                    "native contract facts unavailable; compatibility source scraping disabled"
                )),
            "expected fail-closed diagnostic, got {:?}",
            no_contracts.contract_extraction.diagnostics
        );

        let function = fixture.functions.get("no_contracts").expect("function should be extracted");
        assert!(function.contracts.is_empty());
        assert_eq!(
            function.preconditions,
            vec![Formula::And(vec![
                Formula::Ge(
                    Box::new(Formula::Var("x".to_string(), Sort::Int)),
                    Box::new(Formula::Int(i32::MIN.into())),
                ),
                Formula::Le(
                    Box::new(Formula::Var("x".to_string(), Sort::Int)),
                    Box::new(Formula::Int(i32::MAX.into())),
                ),
            ])],
            "only the tautological i32 parameter range should be present"
        );
        assert!(function.postconditions.is_empty());
    }

    #[test]
    fn extraction_demotes_generated_formula_parameter_names_without_contracts() {
        let fixture = extract_contract_fixture();
        let function = fixture
            .functions
            .get("generated_formula_name_params")
            .expect("generated-name fixture should be extracted");

        assert_eq!(function.body.locals[1].name.as_deref(), Some("s"));
        assert_eq!(function.body.locals[2].name, None);
        assert_eq!(function.body.locals[3].name, None);
        assert_eq!(trust_vcgen::place_to_var_name(function, &Place::local(1)), "s");
        assert_eq!(trust_vcgen::place_to_var_name(function, &Place::local(2)), "_2");
        assert_eq!(trust_vcgen::place_to_var_name(function, &Place::local(3)), "_3");
        assert_ne!(trust_vcgen::place_to_var_name(function, &Place::local(2)), "s__slice_len");
        assert_ne!(
            trust_vcgen::place_to_var_name(function, &Place::local(3)),
            trust_types::const_param_symbol(0, "N")
        );
    }

    #[test]
    fn real_mir_slice_last_preserves_slice_fat_pointer_shape() {
        let fixture = extract_contract_fixture();
        let function = fixture.functions.get("slice_last").expect("slice_last should be extracted");

        let arg = function
            .body
            .locals
            .iter()
            .find(|local| local.index == 1)
            .expect("slice_last slice argument local should be present");
        assert_eq!(
            arg.ty,
            Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) },
            "real rustc MIR slice argument must retain fat-pointer pointee shape"
        );
        assert_eq!(function.body.return_ty, Ty::u8());
        assert!(
            function.body.locals.iter().all(|local| !local.ty.is_unsupported()),
            "slice_last type extraction should not fail closed for ordinary slice shape: {:?}",
            function.body.locals
        );
        assert!(
            function.body.blocks.iter().flat_map(|block| &block.stmts).any(|stmt| {
                let Statement::Assign { rvalue: Rvalue::Use(Operand::Copy(place)), .. } = stmt
                else {
                    return false;
                };
                place.local == 1
                    && place.projections.contains(&Projection::Deref)
                    && place
                        .projections
                        .iter()
                        .any(|projection| matches!(projection, Projection::Index(_)))
            }),
            "slice_last should lower the real MIR indexed slice read without losing the slice local"
        );
    }

    #[test]
    fn option_return_type_lowers_to_explicit_tagged_adt() {
        let function = extract_option_return_fixture();

        let Ty::Adt { name, fields, .. } = &function.body.return_ty else {
            panic!(
                "expected Option return to lower as tagged ADT, got {:?}",
                function.body.return_ty
            );
        };
        assert!(
            name.ends_with("::option::Option") || name.ends_with("::Option"),
            "unexpected Option ADT path `{name}`"
        );
        assert_eq!(fields.len(), 2);
        assert_eq!(fields[0], ("__tag".to_string(), Ty::isize()));
        assert_eq!(fields[1], ("__v1_0".to_string(), Ty::i32()));
        assert!(
            function.body.locals.iter().all(|local| !local.ty.is_unsupported()),
            "Option lowering should not leave unsupported local types: {:?}",
            function.body.locals
        );
    }

    /// Lever A step 2 (real MIR): the kernel universe-`Level` enum extracts as a
    /// native recursive `Ty::Datatype` with its five real constructors and by-name
    /// `Level` self-references, NOT the recursive-ADT `Ty::Unsupported` degrade
    /// (the `Ty::Unsupported { kind: "TyKind::Adt", detail: "recursive …" }` shape
    /// this crate emits for un-modeled recursive ADTs). Def-path gated to `Level`.
    #[test]
    fn real_mir_clean_kernel_level_lowers_to_datatype() {
        let level_ty = extract_level_datatype_fixture();

        assert!(
            !level_ty.is_unsupported(),
            "Level must not degrade to Unsupported, got {level_ty:?}"
        );
        let Ty::Datatype { name, variants } = &level_ty else {
            panic!("Level must lower to Ty::Datatype, got {level_ty:?}");
        };
        // Def paths render without the crate-name prefix for the crate under
        // compilation (`level::Level`) and with it for an upstream dependency
        // (`clean_kernel::level::Level`); accept either via suffix match.
        assert!(name.ends_with("level::Level"), "unexpected Level datatype name `{name}`");
        assert_eq!(variants.len(), 5, "Level has five constructors: {variants:?}");

        let field_list = |ctor: &str| -> &Vec<(String, Ty)> {
            variants
                .iter()
                .find(|(n, _)| n == ctor)
                .map(|(_, fs)| fs)
                .unwrap_or_else(|| panic!("missing constructor {ctor} in {variants:?}"))
        };
        // A by-name recursive `Level` self-reference: `Ty::Datatype` named `Level`
        // with an EMPTY variant list (the definitional occurrence is the outer type).
        let is_level_ref = |t: &Ty| {
            matches!(
                t,
                Ty::Datatype { name, variants }
                    if name.ends_with("level::Level") && variants.is_empty()
            )
        };

        assert!(field_list("Zero").is_empty(), "Zero has no fields");

        let succ = field_list("Succ");
        assert_eq!(succ.len(), 1, "Succ has one Level field: {succ:?}");
        assert!(is_level_ref(&succ[0].1), "Succ field is a Level self-ref: {:?}", succ[0].1);

        for ctor in ["Max", "IMax"] {
            let fs = field_list(ctor);
            assert_eq!(fs.len(), 2, "{ctor} has two Level fields: {fs:?}");
            assert!(
                fs.iter().all(|(_, t)| is_level_ref(t)),
                "{ctor} fields are Level self-refs: {fs:?}"
            );
        }

        let param = field_list("Param");
        assert_eq!(param.len(), 1, "Param has one Name field: {param:?}");
        assert!(
            matches!(
                &param[0].1,
                Ty::Datatype { name, variants }
                    if name.ends_with("name::Name") && variants.is_empty()
            ),
            "Param field is an opaque Name datatype ref: {:?}",
            param[0].1
        );
    }

    /// Lever A step 5 (real MIR): the kernel `ExprKind` enum — the type the real
    /// `infer_type` matches on — extracts as a native recursive `Ty::Datatype` with
    /// one constructor per variant, its recursive `Arc<Expr>` children as BY-NAME
    /// `Expr` refs, its `Sort` payload as a `Level` ref, and its `Name`/`Literal`/
    /// `BinderData` payloads as opaque datatype refs — NOT the recursive-ADT
    /// `Ty::Unsupported` / produced-node-budget degrade. Extraction is BOUNDED (the
    /// by-name refs keep the produced tree O(variants), dodging the 464 MB blow-up).
    #[test]
    fn real_mir_clean_kernel_exprkind_lowers_to_datatype() {
        let (exprkind_ty, _expr_ty) = extract_expr_datatypes_fixture();

        assert!(
            !exprkind_ty.is_unsupported(),
            "ExprKind must not degrade to Unsupported, got {exprkind_ty:?}"
        );
        let Ty::Datatype { name, variants } = &exprkind_ty else {
            panic!("ExprKind must lower to Ty::Datatype, got {exprkind_ty:?}");
        };
        assert!(
            name.ends_with("expr::kind::ExprKind"),
            "unexpected ExprKind datatype name `{name}`"
        );

        // BOUNDED-EXTRACTION EVIDENCE: with by-name refs the whole tree is a
        // handful of nodes. A full expansion (refs NOT used) would be thousands /
        // OOM, and a degrade would be `Unsupported` (asserted against above). A
        // small, exact node count proves the blow-up is dodged.
        let nodes = ty_total_node_count(&exprkind_ty, 100_000);
        assert!(
            nodes < 100,
            "ExprKind datatype must be BOUNDED (by-name refs, no expansion); got {nodes} nodes"
        );

        let field_list = |ctor: &str| -> &Vec<(String, Ty)> {
            variants
                .iter()
                .find(|(n, _)| n == ctor)
                .map(|(_, fs)| fs)
                .unwrap_or_else(|| panic!("missing constructor {ctor} in {variants:?}"))
        };
        // A by-name `Expr` self-reference: `Ty::Datatype` named `expr::Expr` with an
        // EMPTY variant list (its definition is the `Expr` datatype occurrence).
        let is_expr_ref = |t: &Ty| {
            matches!(
                t,
                Ty::Datatype { name, variants }
                    if name.ends_with("expr::Expr") && variants.is_empty()
            )
        };
        let is_ref_ending = |t: &Ty, suffix: &str| {
            matches!(
                t,
                Ty::Datatype { name, variants }
                    if name.ends_with(suffix) && variants.is_empty()
            )
        };

        // Scalar payload: BVar(u32) → a real Int sort, not a datatype ref.
        let bvar = field_list("BVar");
        assert_eq!(bvar.len(), 1, "BVar has one u32 field: {bvar:?}");
        assert_eq!(bvar[0].1, Ty::Int { width: 32, signed: false }, "BVar payload is u32");

        // Sort(Level) → a by-name Level datatype ref (step-2 cross-reference).
        let sort = field_list("Sort");
        assert_eq!(sort.len(), 1, "Sort has one Level field: {sort:?}");
        assert!(
            is_ref_ending(&sort[0].1, "level::Level"),
            "Sort payload is a Level datatype ref: {:?}",
            sort[0].1
        );

        // Const(Name) → an opaque Name datatype ref.
        let konst = field_list("Const");
        assert!(
            is_ref_ending(&konst[0].1, "name::Name"),
            "Const payload is a Name datatype ref: {:?}",
            konst[0].1
        );

        // App(Expr, Expr) → two by-name Expr self-refs (the recursion, unexpanded).
        let app = field_list("App");
        assert_eq!(app.len(), 2, "App has two Expr fields: {app:?}");
        assert!(app.iter().all(|(_, t)| is_expr_ref(t)), "App fields are Expr refs: {app:?}");

        // Lam(BinderData, Expr, Expr) → opaque BinderData ref + two Expr refs.
        let lam = field_list("Lam");
        assert_eq!(lam.len(), 3, "Lam has three fields: {lam:?}");
        assert!(
            is_ref_ending(&lam[0].1, "binder::BinderData"),
            "Lam[0] is a BinderData ref: {:?}",
            lam[0].1
        );
        assert!(
            is_expr_ref(&lam[1].1) && is_expr_ref(&lam[2].1),
            "Lam[1..] are Expr refs: {lam:?}"
        );

        // Let(Expr, Expr, Expr, bool) → three Expr refs + a real Bool.
        let let_ = field_list("Let");
        assert_eq!(let_.len(), 4, "Let has four fields: {let_:?}");
        assert!(
            is_expr_ref(&let_[0].1) && is_expr_ref(&let_[1].1) && is_expr_ref(&let_[2].1),
            "Let[0..3] are Expr refs: {let_:?}"
        );
        assert_eq!(let_[3].1, Ty::Bool, "Let's nonDep flag is a real Bool sort");

        // SProp → a nullary constructor (no fields).
        assert!(field_list("SProp").is_empty(), "SProp has no fields");

        // CubicalPath { ty, left, right } → a struct-style variant, three Expr refs
        // keyed by their SOURCE field names (not positional indices).
        let cpath = field_list("CubicalPath");
        assert_eq!(cpath.len(), 3, "CubicalPath has three fields: {cpath:?}");
        assert_eq!(
            cpath.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>(),
            vec!["ty", "left", "right"],
            "CubicalPath fields keep their source names"
        );
        assert!(cpath.iter().all(|(_, t)| is_expr_ref(t)), "CubicalPath fields are Expr refs");
    }

    /// Lever A step 5 (real MIR): the kernel `Expr` struct extracts as a
    /// single-constructor `Ty::Datatype` whose `kind` field is a by-name `ExprKind`
    /// ref and whose `meta` field is an opaque `ExprMeta` ref — the OTHER half of
    /// the Expr↔ExprKind mutual recursion, both by-name so neither expands the other.
    #[test]
    fn real_mir_clean_kernel_expr_lowers_to_datatype() {
        let (_exprkind_ty, expr_ty) = extract_expr_datatypes_fixture();

        assert!(!expr_ty.is_unsupported(), "Expr must not degrade to Unsupported, got {expr_ty:?}");
        let Ty::Datatype { name, variants } = &expr_ty else {
            panic!("Expr must lower to Ty::Datatype, got {expr_ty:?}");
        };
        assert!(name.ends_with("expr::Expr"), "unexpected Expr datatype name `{name}`");

        // A struct is a ONE-constructor ADT (named after the struct itself).
        assert_eq!(variants.len(), 1, "Expr struct is a single-constructor datatype: {variants:?}");
        let (ctor_name, fields) = &variants[0];
        assert!(
            ctor_name.ends_with("Expr"),
            "sole constructor is named after the struct: {ctor_name}"
        );
        assert_eq!(fields.len(), 2, "Expr has kind + meta fields: {fields:?}");

        assert_eq!(fields[0].0, "kind", "first field is `kind`");
        assert!(
            matches!(
                &fields[0].1,
                Ty::Datatype { name, variants }
                    if name.ends_with("expr::kind::ExprKind") && variants.is_empty()
            ),
            "Expr.kind is a by-name ExprKind ref (recursion NOT expanded): {:?}",
            fields[0].1
        );

        assert_eq!(fields[1].0, "meta", "second field is `meta`");
        assert!(
            matches!(
                &fields[1].1,
                Ty::Datatype { name, variants }
                    if name.ends_with("meta::ExprMeta") && variants.is_empty()
            ),
            "Expr.meta is an opaque ExprMeta datatype ref: {:?}",
            fields[1].1
        );

        // BOUNDED: root + kind ref + meta ref = a tiny tree.
        let nodes = ty_total_node_count(&expr_ty, 100_000);
        assert!(nodes < 20, "Expr datatype must be BOUNDED; got {nodes} nodes");
    }

    /// A discriminant-range precondition is `discr == t0 OR discr == t1 OR ...`
    /// (or a lone `discr == t0`): each disjunct equates a variable to an integer
    /// tag constant. This is the always-true enum-tag invariant that
    /// `enum_discriminant_range_preconditions` attaches so an exhaustive `match`
    /// discharges its `otherwise -> Unreachable` obligation.
    fn is_tag_equality(formula: &Formula) -> bool {
        matches!(
            formula,
            Formula::Eq(lhs, rhs)
                if matches!(lhs.as_ref(), Formula::Var(_, _) | Formula::SymVar(_, _))
                    && matches!(rhs.as_ref(), Formula::Int(_) | Formula::UInt(_))
        )
    }

    fn has_discriminant_range_precondition(preconditions: &[Formula]) -> bool {
        preconditions.iter().any(|formula| match formula {
            Formula::Or(disjuncts) => {
                !disjuncts.is_empty() && disjuncts.iter().all(is_tag_equality)
            }
            single => is_tag_equality(single),
        })
    }

    /// Regression: matching on a `&Enum` must attach the same discriminant-range
    /// precondition as matching the enum by value. A `match` on a reference lowers
    /// the switch's discriminant read as `discriminant((*r))` — a `Deref` projection
    /// on the source place. Before the by-ref fix, `enum_discriminant_range_preconditions`
    /// rejected that deref source and dropped the precondition, so the exhaustive-match
    /// `otherwise -> Unreachable` obligation false-failed for code like `area_ish(&Shape)`
    /// that is no worse than its by-value form.
    #[test]
    fn real_mir_enum_match_by_ref_matches_by_value_discriminant_precondition() {
        let fixture = extract_contract_fixture();
        let by_value = fixture
            .functions
            .get("trust_dir_by_value")
            .expect("trust_dir_by_value should be extracted");
        let by_ref = fixture
            .functions
            .get("trust_dir_by_ref")
            .expect("trust_dir_by_ref should be extracted");

        assert!(
            has_discriminant_range_precondition(&by_value.preconditions),
            "by-value enum match should carry a discriminant-range precondition, got {:?}",
            by_value.preconditions
        );
        assert!(
            has_discriminant_range_precondition(&by_ref.preconditions),
            "matching on &Enum must emit a discriminant-range precondition exactly as the \
             by-value form does, otherwise the exhaustive-match Unreachable obligation \
             false-fails; got {:?}",
            by_ref.preconditions
        );
        assert_eq!(
            by_value.preconditions, by_ref.preconditions,
            "the by-ref discriminant-range precondition must be identical to the by-value one \
             (same tag set, same single-assignment discriminant temp)"
        );
    }

    /// regression: an `enum as int` cast (here `d as u32`) reads the
    /// discriminant into a temp that does *not* drive an exhaustive-match
    /// `otherwise -> Unreachable` switch. The original
    /// `enum_discriminant_range_preconditions` only emitted the tag-range fact for
    /// switch-driving temps, so the cast result read as a free i64 and the
    /// cast-overflow VC (and any arithmetic on it) false-FAILed. After the
    /// generalization to *every* single-assignment discriminant temp, this function
    /// must carry the discriminant-range precondition exactly as a `match` does.
    #[test]
    fn real_mir_enum_as_int_cast_carries_discriminant_precondition() {
        let fixture = extract_contract_fixture();
        let cast = fixture
            .functions
            .get("trust_discr_as_int")
            .expect("trust_discr_as_int should be extracted");
        assert!(
            has_discriminant_range_precondition(&cast.preconditions),
            "an `enum as int` cast must carry a discriminant-range precondition even \
             without an exhaustive match, got {:?}",
            cast.preconditions
        );
    }
    // ---- Trust: def-contracts lane sort environment (caller-side Precondition VCs) ----

    #[test]
    fn def_lane_retype_keeps_float_sort_on_field_chain_vars() {
        // The def-contracts lane must NOT clobber a Float-sorted field-chain var
        // to Int: `self.0 <= 1.0e30` parses with `self.0` at Float{11,53} (the
        // parser's float coercion), and the signature environment carries only
        // the BARE param name `self`. The old `split_once('.')` arm forced
        // `self.0` to Int, mis-sorting the caller-side Precondition VC operand
        // (or failing the Bool sort check → requires fails closed). Field-chain
        // vars — dotted, deref-dotted, and bracketed — must keep parsed sorts,
        // mirroring the body lane.
        let f64_sort = Sort::Float { eb: 11, sb: 53 };
        let mut signature_sorts = BTreeMap::new();
        signature_sorts.insert("self".to_string(), Sort::Int);
        signature_sorts.insert("self*".to_string(), Sort::Int);
        for chain in ["self.0", "self*.0.0", "self.0[3].1"] {
            let formula = Formula::Le(
                Box::new(Formula::Var(chain.to_string(), f64_sort.clone())),
                Box::new(Formula::FpConst {
                    bits: u128::from(1.0e30f64.to_bits()),
                    eb: 11,
                    sb: 53,
                }),
            );
            let typed = retype_source_contract_formula(formula, &signature_sorts);
            let Formula::Le(lhs, _) = typed else { panic!("retype must preserve shape") };
            assert_eq!(
                *lhs,
                Formula::Var(chain.to_string(), f64_sort.clone()),
                "field-chain var `{chain}` must keep its parsed Float sort"
            );
        }
    }

    #[test]
    fn def_lane_retype_still_resorts_bare_params_and_synthetics() {
        // Regression guards for what the fix must NOT change: a bare f64 param
        // name takes its signature sort at any depth (difference bounds), and a
        // synthetic `<param>_len` var still lands at Int.
        let f64_sort = Sort::Float { eb: 11, sb: 53 };
        let mut signature_sorts = BTreeMap::new();
        signature_sorts.insert("near".to_string(), f64_sort.clone());
        signature_sorts.insert("far".to_string(), f64_sort.clone());
        signature_sorts.insert("arr".to_string(), Sort::Int);
        let formula = Formula::And(vec![
            Formula::Le(
                Box::new(Formula::Sub(
                    Box::new(Formula::Var("near".to_string(), Sort::Int)),
                    Box::new(Formula::Var("far".to_string(), Sort::Int)),
                )),
                Box::new(Formula::FpConst {
                    bits: u128::from((-1.0e-6f64).to_bits()),
                    eb: 11,
                    sb: 53,
                }),
            ),
            Formula::Ge(
                Box::new(Formula::Var("arr_len".to_string(), Sort::Bool)),
                Box::new(Formula::Int(1)),
            ),
        ]);
        let typed = retype_source_contract_formula(formula, &signature_sorts);
        let Formula::And(items) = typed else { panic!("retype must preserve shape") };
        let Formula::Le(sub, _) = &items[0] else { panic!("Le expected") };
        let Formula::Sub(near, far) = sub.as_ref() else { panic!("Sub expected") };
        assert_eq!(**near, Formula::Var("near".to_string(), f64_sort.clone()));
        assert_eq!(**far, Formula::Var("far".to_string(), f64_sort));
        let Formula::Ge(len, _) = &items[1] else { panic!("Ge expected") };
        assert_eq!(**len, Formula::Var("arr_len".to_string(), Sort::Int));
    }
}

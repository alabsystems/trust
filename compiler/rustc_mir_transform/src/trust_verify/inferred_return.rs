//! Trust (D5-B, 2026-09-24): kernel-checked BODY-INFERRED return summaries —
//! the compiler side (identity, admission and the call-site summary).
//!
//! ## What this closes
//!
//! ```text
//! pub fn guard(bit: u32) -> bool { bit < 64 }
//! pub fn shift_via_guard(x: u64, bit: u32) -> Option<u64> {
//!     if !guard(bit) { return None; }
//!     Some(x >> bit)
//! }
//! ```
//!
//! After D5-A the caller's shift row is a HELD `UNKNOWN` (the refutation over
//! `guard`'s unmodeled result is not an execution). The inline twin proves, and
//! so does the same helper with `ensures result == (bit < 64)` written by hand.
//! This module writes that clause FOR the author — but never trusts the
//! writer: `trust_vcgen::infer_return_candidate` (an untrusted synthesizer)
//! proposes `_0 == E(params)` together with the ordinary body-aware postcondition
//! VCs over a contract-free clone of the callee, and the candidate is minted
//! only if the Clean CIC kernel certifies EVERY one of them
//! (`trust_certify::certify_vc`). A wrong `E` is refused by the kernel and
//! nothing is minted.
//!
//! ## Identity (decided from `TyCtxt`, never from a rendered string)
//!
//! The callee must be a local or freshly re-derivable declared dependency's
//! free function or inherent method; no trait dispatch, closure, constructor
//! or foreign item is admitted. It must have no generic
//! parameters at all (so the identity instantiation is the only one and the
//! body that was checked is the body every call runs); not a Clean-origin def
//! (those have their own definitional lane); without `#[no_mangle]`,
//! `#[export_name]`, `#[linkage]` or any other extern indicator (its symbol can
//! be interposed at link time, so the checked body need not be the one that
//! runs); without any `trust::` attribute of its own and without an inherited
//! `#[trust::skip]` / `#[trust::assume_total]`; and with no authored contract of
//! any kind (an inferred clause never shares a summary with an authored one —
//! the `contract_skip_ensures_launder` shape).
//!
//! A bounded acyclic call chain may compose only exact typed scalar/enum return
//! equations whose original-body rows were already kernel-checked here.
//! Dependency permission, static linkage, source-unsafe metadata and the
//! existing re-derivation budget are checked before reading a foreign body.
//!
//! Its extracted `def_path` must be UNIQUE among the crate's extracted bodies
//! and among every local body owner (`body_summary_key_collisions`, Trust
//! SUMMARY-NAME-COLLIDE-1), and at each call site the summary is keyed by that
//! exact string, only when
//! the call's `func_operand_name` is byte-identical to it and the caller-body
//! pre-scan names this `DefId` as the sole owner of that name.
//!
//! ## What a minted summary means
//!
//! A lemma the compiler proved about the callee's own extracted body in THIS
//! compilation. It rides the existing, audited postcondition-composition lane
//! (`FunctionSummary::with_body_inferred_return` sets the same reuse bit as a
//! verified `ensures`), so the call-site rebinding and SSA versioning are the
//! ones every composed `ensures` already uses, and the D5-A screen sees the
//! callee as pinned (`SummaryDatabase::postcondition_pinning_callees`: an
//! inferred `_0 == E(params)` with no `requires` determines the result).

use rustc_ast::attr::AttributeExt;
use rustc_data_structures::fx::{FxHashMap, FxHashSet, FxIndexMap};
use rustc_hir::def::DefKind;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::def_id::DefId;

/// Whether `def_id` may carry a body-inferred return summary at all — the
/// call-site-independent identity gate (see the module doc).
fn identity_admissible(tcx: TyCtxt<'_>, def_id: DefId) -> Result<(), &'static str> {
    // Trust: an inherent method has an exact item identity too. Trait dispatch
    // and generic instantiations remain outside this return-summary channel.
    if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn)
        || tcx.trait_of_assoc(def_id).is_some()
        || tcx.trait_impl_of_assoc(def_id).is_some()
    {
        return Err("not a free function or inherent method");
    }
    if !def_id.is_local()
        && !super::foreign_rederivation::foreign_body_rederivable_here(tcx, def_id)
    {
        return Err("foreign body is not re-derivable here");
    }
    if tcx.is_foreign_item(def_id) {
        return Err("foreign item");
    }
    if tcx.generics_of(def_id).count() != 0 {
        return Err("generic");
    }
    if def_id.as_local().is_some_and(|local| crate::clean_origin_mir::is_clean_origin(tcx, local)) {
        return Err("clean-origin");
    }
    if tcx.intrinsic(def_id).is_some() || !super::attrs_queryable(tcx, def_id) {
        return Err("intrinsic or unavailable attributes");
    }
    let attrs = tcx.codegen_fn_attrs(def_id);
    if attrs.contains_extern_indicator() || attrs.symbol_name.is_some() || attrs.linkage.is_some() {
        return Err("exported symbol (interposable)");
    }
    #[allow(deprecated)]
    let own_trust_attr = tcx
        .get_all_attrs(def_id)
        .iter()
        .any(|attr| matches!(attr.path().as_slice(), [tool, _] if tool.as_str() == "trust"));
    if own_trust_attr
        || super::item_has_trust_skip_attr(tcx, def_id)
        || super::item_has_trust_attr(tcx, def_id, "assume_total")
    {
        return Err("trust attribute");
    }
    let contracts = super::trust_contracts_if_any(tcx, def_id);
    if contracts.is_some_and(|bundle| !bundle.is_empty())
        || (!def_id.is_local() && contracts.is_none())
    {
        return Err("authored contract");
    }
    Ok(())
}

fn trace_enabled() -> bool {
    super::env_flag_enabled("TRUST_INFERRED_RETURN_DEBUG")
}

/// Mint the crate's body-inferred return summaries: synthesize a candidate for
/// every admissible body in `funcs` and keep exactly the ones whose check VCs
/// the Clean kernel certifies. `def_ids[i]` is the `DefId` `funcs[i]` was
/// extracted from.
///
/// `funcs` is the crate-wide inventory, extracted from
/// `mir_drops_elaborated_and_const_checked` — PRE-optimization MIR, so every
/// helper keeps its temporaries (`guard`: `_2 = copy _1; _0 = Lt(move _2, 64)`)
/// and its check VCs carry the aliases. Measured 2026-09-25: until trust-certify's
/// kernel-checked rewriting lane (`rewrite_eval`) no certifier lane saw through
/// them and this mint produced NOTHING. A realmir fixture built from an
/// optimized (per-function) dump does not test this path; the pre-optimization
/// rebuilds in `crates/trust-vcgen/tests/inferred_return_realmir.rs` §5 do.
///
/// Trust (2026-10-05, SUMMARY-NAME-COLLIDE-1): `key_collisions` is the
/// compiler's set of `def_path` keys two local body owners share
/// (`super::body_summary_key_collisions`). The count below sees only the
/// extracted bodies; a key in that set is refused as a duplicate too, so D5-B
/// and the other body-derived lanes refuse the same keys.
pub(super) fn mint_inferred_returns(
    tcx: TyCtxt<'_>,
    funcs: &[trust_types::VerifiableFunction],
    def_ids: &[DefId],
    key_collisions: &FxHashSet<String>,
) -> (
    FxHashMap<DefId, trust_vcgen::InferredReturn>,
    FxHashMap<DefId, trust_certify::inferred_return_proof::InferredReturnProofNode>,
) {
    let mut minted = FxHashMap::default();
    let mut proofs = FxHashMap::default();
    // A parallel-vector mismatch means the inventory is not the one this
    // function was written against: mint nothing (fail closed).
    if funcs.len() != def_ids.len() {
        return (minted, proofs);
    }
    let mut def_path_count: FxHashMap<&str, usize> = FxHashMap::default();
    for func in funcs {
        *def_path_count.entry(func.def_path.as_str()).or_default() += 1;
    }
    let trace = trace_enabled();
    // Preserve the extracted inventory's order when checking summary-name
    // collisions; hash-table order must not enter the compiler query.
    let functions: FxIndexMap<_, _> = def_ids.iter().copied().zip(funcs).collect();
    // Trust (T3 L4, C07p; design D-VC-6): each admission writes its check rows into a VC
    // context of its own, dropped when the admission ends; the row oracle's count over
    // them is one crate-level PARITY row (`crate:inferred-return`).
    let mut parity = trust_types::vc_context::ParityTally::default();
    for (func, &def_id) in funcs.iter().zip(def_ids) {
        let unique = def_path_count.get(func.def_path.as_str()).copied() == Some(1)
            && !key_collisions.contains(func.def_path.as_str());
        // Trust: each root has a bounded acyclic dependency walk. Every child
        // enters `minted` only after its own original-body kernel checks.
        let mut visiting = FxHashSet::default();
        let mut remaining = 32;
        let admitted = super::with_scoped_rows(&mut parity, |rows| {
            admit_tree(
                tcx,
                &functions,
                key_collisions,
                &mut minted,
                &mut proofs,
                &mut visiting,
                &mut remaining,
                0,
                def_id,
                unique,
                rows,
            )
        });
        match admitted {
            Ok(candidate) => {
                if trace {
                    eprintln!(
                        "TRUST_INFERRED_RETURN: {} MINTED {:?} ({} check row(s) kernel-certified)",
                        func.def_path,
                        candidate.postcondition(),
                        candidate.check_vcs().len(),
                    );
                }
                minted.insert(def_id, candidate);
            }
            Err(reason) => {
                if trace {
                    eprintln!("TRUST_INFERRED_RETURN: {} declined: {reason}", func.def_path);
                }
            }
        }
    }
    // Trust (T3 L4, C07p): the admissions' row-oracle count, once per mint that ran.
    super::elide_audit::record_crate_parity(
        tcx,
        "crate:inferred-return",
        &parity,
        &[trust_types::vc_context::Oracle::Row],
    );
    (minted, proofs)
}

/// Trust: a return fact may cross a call only after the exact callee body has
/// cleared the existing identity and kernel bars in this compilation. Unknown
/// calls, recursion and exhausted walks leave the original call opaque.
#[allow(clippy::too_many_arguments)]
fn admit_tree<'tcx>(
    tcx: TyCtxt<'tcx>,
    functions: &FxIndexMap<DefId, &trust_types::VerifiableFunction>,
    key_collisions: &FxHashSet<String>,
    minted: &mut FxHashMap<DefId, trust_vcgen::InferredReturn>,
    proofs: &mut FxHashMap<DefId, trust_certify::inferred_return_proof::InferredReturnProofNode>,
    visiting: &mut FxHashSet<DefId>,
    remaining: &mut usize,
    depth: usize,
    def_id: DefId,
    unique: bool,
    rows: &mut trust_types::vc_context::VcContext,
) -> Result<trust_vcgen::InferredReturn, &'static str> {
    if let Some(candidate) = minted.get(&def_id) {
        return Ok(candidate.clone());
    }
    if depth > 8 || *remaining == 0 || !visiting.insert(def_id) {
        return Err("recursive or over-budget return dependency");
    }
    *remaining -= 1;
    let result = (|| {
        let owned;
        let func = if let Some(func) = functions.get(&def_id) {
            *func
        } else {
            if def_id.is_local() {
                return Err("local body absent from exact inventory");
            }
            identity_admissible(tcx, def_id)?;
            if super::foreign_rederivation::admit_foreign_rederivation(tcx, def_id).is_some() {
                return Err("foreign return dependency admission refused");
            }
            owned = trust_mir_extract::extract_function_with_contract_bundle(
                tcx,
                tcx.optimized_mir(def_id),
                None,
            );
            &owned
        };
        let unique = unique
            && !key_collisions.contains(&func.def_path)
            && !functions
                .iter()
                .any(|(other_id, other)| *other_id != def_id && other.def_path == func.def_path);
        let initial_refusal = match admit(tcx, func, def_id, unique, rows, &[], proofs) {
            Ok(candidate) => return Ok(candidate),
            Err(reason) => {
                if trace_enabled() {
                    eprintln!(
                        "TRUST_INFERRED_RETURN: {} initial admission declined: {reason}",
                        func.def_path,
                    );
                }
                reason
            }
        };
        // Trust: contracted callers may need a child's return fact without lending a
        // fact themselves. The shared cost preflight bounds this walk; return
        // semantics belong to the shared synthesizer, not a second type filter
        // here. Every child and final candidate still passes `admit` below.
        if !trust_vcgen::return_dependency_body_within_budget(func) {
            return Err(initial_refusal);
        }
        let targets = direct_item_callees(tcx, def_id)?;
        let mut inputs = Vec::new();
        let mut seen = FxHashSet::default();
        for block in &func.body.blocks {
            let trust_types::Terminator::Call { callee_identity: Some(identity), .. } =
                &block.terminator
            else {
                continue;
            };
            if !seen.insert(*identity) {
                continue;
            }
            let child = *targets.get(identity).ok_or("unresolved return dependency")?;
            if trace_enabled() {
                eprintln!(
                    "TRUST_INFERRED_RETURN: {} depends on {}",
                    func.def_path,
                    super::probe_label(tcx, child),
                );
            }
            let inferred = admit_tree(
                tcx,
                functions,
                key_collisions,
                minted,
                proofs,
                visiting,
                remaining,
                depth + 1,
                child,
                true,
                rows,
            )?;
            inputs.push(
                trust_vcgen::InferredReturnCall::new(*identity, &inferred)
                    .ok_or("callee is outside the typed return fragment")?,
            );
        }
        if inputs.is_empty() {
            // Trust: a leaf cannot compose a child to repair its first refusal.
            // Keep that actual synthesis/identity/kernel failure for its caller.
            return Err(initial_refusal);
        }
        admit(tcx, func, def_id, unique, rows, &inputs, proofs)
    })();
    visiting.remove(&def_id);
    if let Ok(candidate) = &result {
        minted.insert(def_id, candidate.clone());
    }
    result
}

/// Read call identities from the same real MIR inventory, rather than
/// reconstructing DefIds from names or trusting a serialized ordinal.
fn direct_item_callees<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> Result<FxHashMap<trust_types::CalleeIdentity, DefId>, &'static str> {
    let scan = |body: &rustc_middle::mir::Body<'tcx>| {
        let mut targets = FxHashMap::default();
        for block in body.basic_blocks.iter() {
            let rustc_middle::mir::TerminatorKind::Call { func, .. } = &block.terminator().kind
            else {
                continue;
            };
            let ty::FnDef(callee, args) = *func.ty(&body.local_decls, tcx).kind() else {
                return Err("indirect return dependency");
            };
            // Trust: both bound variables and supplied arguments make this
            // dependency generic; neither may enter the monomorphic summary.
            if !args.bound_vars().is_empty()
                || !args.skip_binder().is_empty()
                || tcx.trait_of_assoc(callee).is_some()
                || tcx.trait_impl_of_assoc(callee).is_some()
            {
                return Err("generic or dispatched return dependency");
            }
            let identity = trust_mir_extract::item_identity(tcx, callee)
                .ok_or("return dependency identity unavailable")?;
            targets.insert(identity, callee);
        }
        Ok(targets)
    };
    if let Some(local) = def_id.as_local() {
        let body = tcx.mir_drops_elaborated_and_const_checked(local);
        if body.is_stolen() {
            return Err("return dependency body already consumed");
        }
        scan(&body.borrow())
    } else {
        scan(tcx.optimized_mir(def_id))
    }
}

/// One body's admission: synthesis, identity, then THE KERNEL CHECK.
fn admit(
    tcx: TyCtxt<'_>,
    func: &trust_types::VerifiableFunction,
    def_id: DefId,
    def_path_unique: bool,
    // Trust (T3 L4, C07p): this admission's own VC context.
    rows: &mut trust_types::vc_context::VcContext,
    callees: &[trust_vcgen::InferredReturnCall],
    proofs: &mut FxHashMap<DefId, trust_certify::inferred_return_proof::InferredReturnProofNode>,
) -> Result<trust_vcgen::InferredReturn, &'static str> {
    // The summary is keyed by this string at call sites: a def path two
    // extracted bodies share cannot name one of them.
    if !def_path_unique {
        return Err("duplicate def_path");
    }
    // The pure structural synthesizer first: it declines almost every body in
    // O(body) without a query, so the identity queries below run only for the
    // handful of fragment-shaped helpers.
    let candidate = if callees.is_empty() {
        trust_vcgen::infer_return_candidate_rows(func, rows)?
    } else {
        trust_vcgen::infer_return_candidate_with_calls_rows(func, callees, rows)?
    };
    identity_admissible(tcx, def_id)?;
    // THE ADMISSION: every check row kernel-certified (a zero-trust UNSAT of
    // `defs ∧ ¬(_0 == E)` over the callee's own body with every entry hypothesis
    // cleared). Any `None` — an unsupported shape, an ay miss, a kernel
    // rejection — mints nothing.
    let mut evidence = Vec::new();
    for (index, vc) in candidate.check_vcs().iter().enumerate() {
        let certificate = trust_certify::certify_vc(vc);
        if certificate.is_none() {
            if trace_enabled() {
                eprintln!(
                    "TRUST_INFERRED_RETURN: {} kernel declined check row {} of {}",
                    func.def_path,
                    index,
                    candidate.check_vcs().len(),
                );
                // Trust: preserve the actual declined input for an independent
                // reproducer. This diagnostic never retries or admits a row.
                // The certifier may have refused a too-deep input before any
                // recursive serialization. Reuse the bounded snapshot writer,
                // then wrap its exact JSON as a string (including i128 values).
                if let Some(vc_json) =
                    trust_types::original_vc_snapshot::bounded_original_vc_json(vc)
                {
                    match serde_json::to_string(&(
                        func.def_path.as_str(),
                        index,
                        candidate.check_vcs().len(),
                        vc_json,
                    )) {
                        Ok(snapshot) => {
                            eprintln!("TRUST_INFERRED_RETURN:VC_DECLINED {snapshot}");
                        }
                        Err(error) => eprintln!(
                            "TRUST_INFERRED_RETURN: failed to serialize declined row: {error}"
                        ),
                    }
                } else {
                    eprintln!(
                        "TRUST_INFERRED_RETURN: declined row exceeds diagnostic snapshot bounds"
                    );
                }
            }
            return Err("kernel did not certify every check row");
        }
        evidence.push(certificate.expect("certificate was checked above"));
    }
    // Trust: retain the exact inputs and proofs already checked above. A
    // serialized record is not authority; its consumer must replay it.
    let identity = trust_mir_extract::item_identity(tcx, def_id)
        .ok_or("inferred return item identity unavailable")?;
    proofs.insert(
        def_id,
        trust_certify::inferred_return_proof::InferredReturnProofNode {
            identity,
            function: func.clone(),
            children: callees.iter().map(trust_vcgen::InferredReturnCall::identity).collect(),
            evidence,
        },
    );
    Ok(candidate)
}

/// The body-inferred summary for one direct call site, or `None` (the call
/// keeps its pre-D5-B treatment exactly). `callee_name` is the call's
/// `func_operand_name` — the key the summary DB is consulted with — and
/// `name_owner` the caller-body pre-scan's sole owner of that name.
pub(super) fn callee_summary<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller_def_id: DefId,
    callee_def_id: DefId,
    args: ty::GenericArgs<'tcx>,
    callee_name: &str,
    name_owner: Option<DefId>,
) -> Option<trust_vcgen::FunctionSummary> {
    let refuse = |reason: &str| {
        if trace_enabled() {
            eprintln!(
                "TRUST_INFERRED_RETURN: call {callee_name} from {} not summarized: {reason}",
                super::probe_label(tcx, caller_def_id)
            );
        }
        None
    };
    if callee_def_id == caller_def_id {
        return refuse("self call");
    }
    if !args.is_empty() {
        return refuse("non-identity instantiation");
    }
    if name_owner != Some(callee_def_id) {
        return refuse("summary key not uniquely owned in the caller body");
    }
    // Cheap map probe first: almost every callee (std, generic, contracted, or
    // simply outside the fragment) has no minted entry.
    let inferred = super::with_crate_verification_state(tcx.sess, |state| {
        state.inferred_returns.get(&callee_def_id).cloned()
    });
    let Some(inferred) = inferred else {
        return refuse("no kernel-certified inferred return");
    };
    // Re-assert the mint's identity gate at the use site (defence in depth: the
    // map is keyed by `DefId`, and this is the same predicate).
    if let Err(reason) = identity_admissible(tcx, callee_def_id) {
        return refuse(reason);
    }
    // The DB is string-keyed: the call's key must BE the checked body's name.
    if inferred.def_path() != callee_name {
        return refuse("call key differs from the checked body's def_path");
    }
    let summary = trust_vcgen::FunctionSummary::new(callee_name.to_string())
        .with_body_inferred_return(&inferred);
    // `with_body_inferred_return` refuses to mix; a fresh summary must carry it.
    if summary.postconditions.is_empty() {
        return refuse("builder refused");
    }
    Some(summary)
}

/// Trust: retain only the shared DAG reachable through the caller's exact
/// typed call identities. No def-path search or omitted child can supply a fact.
pub(super) fn proof_graph_for(
    tcx: TyCtxt<'_>,
    function: &trust_types::VerifiableFunction,
) -> Option<trust_certify::inferred_return_proof::InferredReturnProofGraph> {
    super::with_crate_verification_state(tcx.sess, |state| {
        let mut by_identity = std::collections::BTreeMap::new();
        #[allow(rustc::potential_query_instability)]
        for proof in state.inferred_return_derivations.values() {
            if by_identity.insert(proof.identity, proof).is_some() {
                return None;
            }
        }
        let mut pending = Vec::new();
        for block in &function.body.blocks {
            if let trust_types::Terminator::Call { callee_identity, .. } = &block.terminator {
                pending.push((*callee_identity)?);
            }
        }
        let mut selected = std::collections::BTreeMap::new();
        while let Some(identity) = pending.pop() {
            if selected.contains_key(&identity) {
                continue;
            }
            if selected.len() >= 32 {
                return None;
            }
            let proof = *by_identity.get(&identity)?;
            pending.extend(proof.children.iter().copied());
            selected.insert(identity, proof.clone());
        }
        Some(trust_certify::inferred_return_proof::InferredReturnProofGraph {
            nodes: selected.into_values().collect(),
        })
    })
}

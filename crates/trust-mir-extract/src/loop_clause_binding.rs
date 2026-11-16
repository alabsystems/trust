//! A loop clause binds the source binding IN SCOPE AT ITS LOOP, or nothing.
//!
//! Trust #soundness (VS-1 follow-up, 2026-10-04). VC generation binds every
//! identifier of a loop clause (`invariant`, loop `decreases`) by SPELLING: the
//! clause's `x` is the one extracted local whose name is `x`, and the extracted
//! names come from `build_debug_name_map`, one per local, over the whole body.
//! That map is the right namespace for a SIGNATURE clause, whose identifiers
//! denote parameters. A loop clause is written inside the body, where `x` means
//! the binding that is lexically in scope at the loop, and MIR can leave that
//! binding with no local at all: a binding MIR folded to a constant gets a
//! constant `var_debug_info` row (`x => const 50_u32`), and a constant or a
//! projection row names no local. The spelling then falls back to an OUTER
//! binding of the same name. Measured on a stage 1 carrying VS-1's extractor
//! (`a4f092223`, VS-1 before its final rebase) for
//!
//! ```text
//! pub fn lp5(x: u32, k: u32) -> u32 {
//!     let z = x; { let z = k; }
//!     let mut i = x;
//!     let x = 50u32;
//!     while i < 5 invariant i >= x { i += 1; }
//!     i
//! }
//! ```
//!
//! the rows were `x => _1, k => _2, z => _1, z => _2, i => _3, x => const 50`,
//! the clause bound `_3 >= _1`, and the FALSE invariant (at `lp5(0, 0)` the loop
//! head has `i = 0`, `x = 50`) reported `3 proved` at `-Cdebuginfo=2` and `0`
//! and at `-Copt-level=3`, and `of which 1 kernel-certified` under
//! `-Ztrust-policy=certify`. VS-1 widened this. Under the old last-write
//! collapse the alias `z`, whose rows are on two locals, still named `_1`, so
//! `x` named nothing and the clause failed closed (read from the two collapse
//! rules, not re-measured on a pre-VS-1 build); VS-1 drops `z`, and `_1` falls
//! back to `x`. Without the alias the same false clause was proved before and
//! after VS-1 (KNOWN_HAZARDS "CLOSED 2026-10-04 (VS-1)", residual 1).
//!
//! The query already knows which binding a loop clause means: for each spelling
//! it reads, `TrustContractPredicate::source_place_bindings` carries the HIR
//! local id of the binding visible at the loop, resolved through the region
//! scope tree. [`refuse_loop_clauses_bound_outside_their_scope`] checks every
//! such spelling against the local the formula namespace binds it to, and
//! accepts the binding on one of two pieces of evidence:
//!
//! 1. STORAGE: the local carries the same compiler-owned HIR identity
//!    (`LocalInfo::TrustSourceBinding`, or `BindingForm::Var` before cleanup) and
//!    its declaration is not from an inlined callee. The local IS the binding's
//!    storage. This covers parameters and every binding MIR kept in its own
//!    local.
//! 2. OWN ROW: every `var_debug_info` row of the binding itself (its spelling,
//!    the span of its HIR binding pattern, and a scope that is not inlined) is a
//!    whole-local row on that local. A copy propagated onto another local
//!    (`let alias = xs;` puts `alias => _1` on the argument) keeps its own row,
//!    and the row's place is where debuginfo reads the binding in its scope.
//!
//! Anything else fails closed: the clause's bound contract is replaced by its
//! unpaired form, which VC generation reports as one non-refutable
//! `UnsupportedMir` row per clause (never proved), and the compiler names the
//! reason. A constant or projection row is never evidence, and neither is a
//! row of an OUTER binding with the same spelling, which is what closes `lp5`.
//! A clause whose map is incomplete (`None` for a structural proposition) is
//! refused too: some spelling in it then has no compiler-owned identity to
//! check.
//!
//! What this does not cover: debuginfo that MIR optimizations leave wrong. The
//! OWN ROW evidence trusts a binding's own row exactly as far as the formula
//! namespace already trusts every row.

use rustc_middle::mir;
use rustc_middle::mir::trust_contract as rustc_trust_contract;
use rustc_middle::ty::TyCtxt;
use trust_types::{
    CompilerContractBundle, ContractKind, LoopContractKind, UNPAIRED_LOOP_CONTRACT_PREFIX,
    VerifiableFunction,
};

/// Where one `var_debug_info` row of the in-scope binding puts its value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OwnRow {
    /// `name => _k`: a whole-local place with no projection and no fragment.
    WholeLocal(usize),
    /// A constant, a projection, or a composite fragment: it names no local.
    NotALocal,
}

/// The evidence that a spelling's local denotes the in-scope binding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BindingEvidence {
    /// The local carries the binding's own HIR identity.
    Storage,
    /// Every row of the binding itself is a whole-local row on the local.
    OwnRow,
}

/// Decide one spelling. `bound_local` is the local the formula namespace binds
/// the spelling to; `storage_identity` is the HIR identity that local carries
/// (`None` for an inlined, temporary or cleared declaration); `in_scope` is the
/// HIR identity of the binding the query resolved at the loop; `own_rows` are
/// that binding's own debug rows.
pub(crate) fn decide_loop_clause_binding(
    bound_local: usize,
    storage_identity: Option<u32>,
    in_scope: u32,
    own_rows: &[OwnRow],
) -> Result<BindingEvidence, String> {
    if storage_identity == Some(in_scope) {
        return Ok(BindingEvidence::Storage);
    }
    if !own_rows.is_empty() && own_rows.iter().all(|row| *row == OwnRow::WholeLocal(bound_local)) {
        return Ok(BindingEvidence::OwnRow);
    }
    let why = if own_rows.is_empty() {
        "that binding is not stored there and has no debug row of its own".to_string()
    } else if own_rows.contains(&OwnRow::NotALocal) {
        "that binding is not stored there, and its own debug row is a constant or a projection, \
         which names no local"
            .to_string()
    } else {
        "that binding is not stored there, and its own debug row puts it on another local"
            .to_string()
    };
    Err(format!(
        "its spelling names MIR local _{bound_local}, but the binding in scope at the loop is \
         HIR local {in_scope}, and {why}"
    ))
}

/// The HIR identity a MIR local declaration carries, if it is a crate-local,
/// non-inlined user binding. Mirrors `trust_loop_monitor_places` in
/// `trust_verify.rs`, which rebinds certified loop monitors by the same identity.
fn storage_identity(body: &mir::Body<'_>, local: usize) -> Option<u32> {
    if local >= body.local_decls.len() {
        return None;
    }
    let decl = &body.local_decls[mir::Local::from_usize(local)];
    // An inlined callee's declaration carries an id from ANOTHER owner's HIR, so
    // the same number would mean a different binding.
    if decl.source_info.scope.inlined_instance(&body.source_scopes).is_some() {
        return None;
    }
    match &decl.local_info {
        mir::ClearCrossCrate::Set(info) => match &**info {
            mir::LocalInfo::TrustSourceBinding { hir_local_id } => Some(*hir_local_id),
            mir::LocalInfo::User(mir::BindingForm::Var(binding)) => {
                Some(binding.binding_hir_local_id.as_u32())
            }
            _ => None,
        },
        mir::ClearCrossCrate::Clear => None,
    }
}

/// The debug rows MIR building emitted for the HIR binding `hir_local_id` of
/// `owner`: its spelling, its binding pattern's span, and a scope that is not an
/// inlined callee's. `Err` when the id does not name a binding pattern.
fn own_debug_rows(
    tcx: TyCtxt<'_>,
    body: &mir::Body<'_>,
    owner: rustc_hir::OwnerId,
    spelling: &str,
    hir_local_id: u32,
) -> Result<Vec<OwnRow>, String> {
    let nodes = tcx.hir_owner_nodes(owner);
    let index = usize::try_from(hir_local_id).unwrap_or(usize::MAX);
    let Some(parented) = (index < nodes.nodes.len())
        .then(|| &nodes.nodes[rustc_hir::ItemLocalId::from_usize(index)])
    else {
        return Err(format!("HIR local {hir_local_id} does not exist in the clause's owner"));
    };
    let rustc_hir::Node::Pat(pat) = parented.node else {
        return Err(format!("HIR local {hir_local_id} is not a binding pattern"));
    };
    let rustc_hir::PatKind::Binding(_, _, ident, _) = pat.kind else {
        return Err(format!("HIR local {hir_local_id} is not a binding pattern"));
    };
    if ident.name.as_str() != spelling {
        return Err(format!(
            "HIR local {hir_local_id} binds `{}`, not `{spelling}`",
            ident.name.as_str()
        ));
    }
    Ok(body
        .var_debug_info
        .iter()
        .filter(|row| {
            row.name.as_str() == spelling
                && row.source_info.span == pat.span
                && row.source_info.scope.inlined_instance(&body.source_scopes).is_none()
        })
        .map(|row| match &row.value {
            mir::VarDebugInfoContents::Place(place)
                if place.projection.is_empty() && row.composite.is_none() =>
            {
                OwnRow::WholeLocal(place.local.as_usize())
            }
            _ => OwnRow::NotALocal,
        })
        .collect())
}

/// Check one loop clause's spellings. `Ok` also when the clause binds nothing
/// this gate can judge (a spelling no local carries, or two locals carry, is
/// refused by VC generation itself).
fn check_loop_clause<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    owner: Option<rustc_hir::OwnerId>,
    query: Option<&rustc_trust_contract::TrustContract<'tcx>>,
    func: &VerifiableFunction,
) -> Result<(), String> {
    let Some(query) = query else {
        return Err(
            "e45.loop-binding.missing-query-clause: the compiler query has no record of this clause"
                .to_string(),
        );
    };
    let bindings = match (&query.predicate.kind, &query.predicate.source_place_bindings) {
        (_, Some(bindings)) => bindings,
        (rustc_trust_contract::TrustContractPredicateKind::Typed { .. }, None) => {
            return Err("e45.loop-binding.incomplete-map: the compiler query has no complete \
                 source-binding map for this clause, so its spellings cannot be checked against \
                 the bindings in scope at the loop"
                .to_string());
        }
        // Not a structural proposition: it has no typed row to prove, and the
        // loop binder already refused it.
        (_, None) => return Ok(()),
    };
    if bindings.is_empty() {
        return Ok(());
    }
    let Some(owner) = owner else {
        return Err("e45.loop-binding.foreign-body: the clause's body is not crate-local, so the \
             HIR bindings in scope at its loop cannot be read"
            .to_string());
    };
    let mut place = trust_types::Place { local: 0, projections: Vec::new() };
    for binding in bindings {
        // A reference-typed scalar is spelled `r*`; its root local is `r`.
        let spelled = binding.name.as_str();
        let root = spelled.strip_suffix('*').unwrap_or(spelled);
        // Exactly the lookup VC generation uses to bind a loop-formula leaf
        // (`type_loop_formula`, `read_only_collection_model_for_name`).
        let mut matched_local: Option<usize> = None;
        let mut ambiguous = false;
        for decl in &func.body.locals {
            let could_match = decl.name.as_deref() == Some(root)
                || root.strip_prefix('_').and_then(|s| s.parse::<usize>().ok())
                    == Some(decl.index);
            if !could_match {
                continue;
            }
            place.local = decl.index;
            if trust_vcgen::place_to_var_name(func, &place) == root {
                if matched_local.replace(decl.index).is_some() {
                    ambiguous = true;
                    break;
                }
            }
        }
        let Some(bound_local) = matched_local.filter(|_| !ambiguous) else { continue };
        let identity = storage_identity(body, bound_local);
        let own_rows = if identity == Some(binding.hir_local_id) {
            Vec::new()
        } else {
            own_debug_rows(tcx, body, owner, root, binding.hir_local_id).map_err(|reason| {
                format!("e45.loop-binding.unreadable-binding: `{root}`: {reason}")
            })?
        };
        decide_loop_clause_binding(bound_local, identity, binding.hir_local_id, &own_rows)
            .map_err(|reason| format!("e45.loop-binding.not-in-scope: `{root}`: {reason}"))?;
    }
    Ok(())
}

/// Refuse every loop clause in `func` whose spellings the formula namespace
/// binds to a local other than the binding in scope at the loop (see the module
/// header). A refused clause's contract becomes its unpaired form, so VC
/// generation emits one fail-closed `UnsupportedMir` row for it. Must run right
/// after `trust_vcgen::bind_compiler_loop_contract_bundle`, on the same `func`,
/// `body` and bundles. Returns `(loop clause index, reason)` per refusal.
pub fn refuse_loop_clauses_bound_outside_their_scope<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    rustc_bundle: &rustc_trust_contract::TrustContractBundle<'tcx>,
    compiler_contracts: &CompilerContractBundle,
    func: &mut VerifiableFunction,
) -> Vec<(usize, String)> {
    let mut refusals = Vec::new();
    if compiler_contracts.loop_contracts.is_empty() {
        return refusals;
    }
    let owner = body.source.def_id().as_local().map(|def| tcx.local_def_id_to_hir_id(def).owner);
    // The loop binder appends one contract per loop clause right after the dense
    // function contracts (`verifier_api_source_contracts` reads them there too).
    let base = compiler_contracts.contracts.len();
    for (index, spec) in compiler_contracts.loop_contracts.iter().enumerate() {
        let Some(contract) = func.contracts.get(base + index) else { continue };
        let kind_matches = matches!(
            (contract.kind, spec.kind),
            (ContractKind::LoopInvariant, LoopContractKind::Invariant)
                | (ContractKind::Decreases, LoopContractKind::Decreases)
        );
        // Only a clause bound to its MIR header can yield a proof; an unpaired
        // one is already fail-closed.
        let bound = kind_matches
            && contract.span == spec.span
            && contract.body.strip_prefix("bb").and_then(|rest| rest.split_once(": ")).is_some_and(
                |(header, rest)| {
                    header.parse::<usize>().ok() == spec.mir_header && rest == spec.body
                },
            );
        if !bound {
            continue;
        }
        if let Err(reason) =
            check_loop_clause(tcx, body, owner, rustc_bundle.loop_contracts.get(index), func)
        {
            func.contracts[base + index].body =
                format!("{UNPAIRED_LOOP_CONTRACT_PREFIX}{}", spec.body);
            refusals.push((index, reason));
        }
    }
    refusals
}

#[cfg(test)]
mod tests {
    use super::{BindingEvidence, OwnRow, decide_loop_clause_binding};

    /// `lp5` (module header): `x` binds `_1`, the parameter, whose identity is
    /// the parameter's (HIR 3), while the binding in scope is `let x = 50u32`
    /// (HIR 20), whose only row is a constant.
    #[test]
    fn loop_binding_refuses_an_outer_binding_behind_a_constant_shadow() {
        let refusal = decide_loop_clause_binding(1, Some(3), 20, &[OwnRow::NotALocal]).unwrap_err();
        assert!(refusal.contains("_1") && refusal.contains("constant"), "{refusal}");
    }

    /// `let x = p.0;` gives the shadow a projection row: the same refusal.
    #[test]
    fn loop_binding_refuses_an_outer_binding_behind_a_projection_shadow() {
        assert!(decide_loop_clause_binding(1, Some(3), 21, &[OwnRow::NotALocal]).is_err());
    }

    /// The shadow has no row at all (a flipped body, or stripped debuginfo): the
    /// parameter's own identity is not the in-scope binding's, so it is refused.
    #[test]
    fn loop_binding_refuses_when_the_in_scope_binding_has_no_row() {
        let refusal = decide_loop_clause_binding(1, Some(3), 20, &[]).unwrap_err();
        assert!(refusal.contains("no debug row"), "{refusal}");
    }

    /// The in-scope binding's row is on another local than the one the spelling
    /// names, or on two locals.
    #[test]
    fn loop_binding_refuses_a_row_on_another_local() {
        assert!(decide_loop_clause_binding(1, Some(3), 20, &[OwnRow::WholeLocal(4)]).is_err());
        assert!(
            decide_loop_clause_binding(
                1,
                None,
                20,
                &[OwnRow::WholeLocal(1), OwnRow::WholeLocal(4)]
            )
            .is_err()
        );
        assert!(
            decide_loop_clause_binding(1, None, 20, &[OwnRow::WholeLocal(1), OwnRow::NotALocal])
                .is_err()
        );
    }

    /// A parameter, or a binding MIR kept in its own local: storage identity.
    #[test]
    fn loop_binding_accepts_the_bindings_own_storage() {
        assert_eq!(decide_loop_clause_binding(3, Some(12), 12, &[]), Ok(BindingEvidence::Storage));
        // Identity wins even when the binding's row was folded to a constant:
        // the local is the binding's storage, whatever it holds.
        assert_eq!(
            decide_loop_clause_binding(3, Some(12), 12, &[OwnRow::NotALocal]),
            Ok(BindingEvidence::Storage)
        );
    }

    /// `let alias = xs;` (native_loop_collection_semantics.rs#alias): CopyProp
    /// removes `alias`'s local and moves its row onto `_1`, the argument.
    #[test]
    fn loop_binding_accepts_a_copy_whose_own_row_is_on_the_local() {
        assert_eq!(
            decide_loop_clause_binding(1, Some(2), 9, &[OwnRow::WholeLocal(1)]),
            Ok(BindingEvidence::OwnRow)
        );
        assert_eq!(
            decide_loop_clause_binding(1, None, 9, &[OwnRow::WholeLocal(1), OwnRow::WholeLocal(1)]),
            Ok(BindingEvidence::OwnRow)
        );
    }
}

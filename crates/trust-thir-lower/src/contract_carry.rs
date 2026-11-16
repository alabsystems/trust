// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! WS5.5, STAGED — the contract-bound carry, built, tested and measured, with
//! ZERO rows born live.
//!
//! Roadmap row WS5.5 (`two-language-completion-roadmap.md`, trust-ir) and the
//! 08-27 design §5 (`docs/design/2026-08-27-two-language-direct-to-trust-ir.md`):
//! carry each authored contract clause of `tcx.trust_contracts` into the direct
//! module as a TYPED `ProofFormula` — a `Function.summary` (requires / ensures /
//! decreases, `params`, `proved: false`, `backed_by: None`) plus one `Pending`
//! contract-kind obligation row per clause — instead of the string-typed
//! `DesignOnly` disclosure (`crate::contract_disclosure`).
//!
//! # Staged, exactly like Step 2 of DIRECT-LANE-PROOF-AUTHORITY.md
//!
//! The tier that ADMITS these rows (`contract-bound-v3`, design name
//! `contract-bound-v2`; see "Naming" below) is an owner-signed capability-tier
//! change (DG-60) in two BYTE-IDENTICAL frozen files (`direct_obligations.rs`,
//! `crate_module.rs`). This module therefore lands everything that does NOT
//! move a frozen byte:
//!
//! * the session-state carry ([`ContractCarryRegistry`]), filled at emission by
//!   the mainline lowering in `lib.rs` — the loop-lowering arm records each
//!   contract loop's header the way `DirectObligationRecord` records an assert;
//! * the pure clause carrier ([`carry_clause`]) and the fail-closed installer
//!   ([`install_contract_obligations`]);
//! * the staged rung ([`contract_bound_inventory_errors`]): exactly what the
//!   owner-signed `DirectObligationTier::ContractBoundPending` arm will admit,
//!   as a pure function over a module.
//!
//! NOTHING in production calls the installer on the published module, and
//! `DIRECT_OBLIGATION_CAPABILITY` stays `ObligationBearingPending`: the live
//! finalizer still births zero contract rows, the registry populates and is
//! dropped with the session, and every artifact is byte-identical. The only
//! registry reader is the zero-authority shadow behind
//! [`TRUST_CONTRACT_CARRY_SHADOW_ENV`] (`crate::contract_carry_shadow`), which
//! installs on a CLONE and writes a JSON sidecar. The exact owner-signed flip
//! hunks are spelled in `docs/design/DIRECT-LANE-PROOF-AUTHORITY.md`
//! ("WS5.5 — the contract-bound tier, staged").
//! The compatibility compiler's native WP path also reuses the query capture
//! and pure clause binder below. It does not call the direct-module installer
//! or change that staged capability tier.
//!
//! # What a carried clause is
//!
//! * Every leaf binds → schema [`CONTRACT_CLAUSE_SCHEMA`]: `payload` is the
//!   canonical proposition JSON of `crate::contract_render` (byte-identical to
//!   the disclosure's `proposition` field), `bindings` maps every free name to
//!   a typed IR place, and `smtlib` is present only when the WHOLE clause has
//!   an exact SMT-LIB rendering (signedness rides the operator, `bvslt` /
//!   `bvult`, because `ClauseSort` has none — F-026). An opaque schema's
//!   rendering is never read by trust-ir (`ProofFormula::smtlib_text`,
//!   `formula_schema.rs`), so `smtlib` here is a router index, not a second
//!   formula.
//! * Anything else → schema [`CONTRACT_OPAQUE_SCHEMA`], `payload` = the
//!   canonical predicate JSON (the AUTHORED text for a `Typed`/`Opaque`
//!   predicate; the reason / MIR local for the text-less `Unsupported` /
//!   `MirLocal` kinds, which carry no authored text), and EMPTY `bindings`,
//!   which spells UNBINDABLE under the v41 rule. Nothing is dropped, nothing
//!   is invented.
//!
//! # Bindings (never by debug name)
//!
//! * Function clauses: a free name binds to `Param { index }` only when it is
//!   the ident of a SIMPLE by-value binding pattern of a formal parameter,
//!   read from the HIR param pattern at emission. The query's own admission
//!   gate (`reject_unrepresentable_contract_parameter_names`) refuses every
//!   contract-bearing function in which two parameter bindings share a
//!   displayed name, so the name -> HIR binding map is injective here. `result`
//!   (spelled `_0` by the query) binds to `ResultSlot { 0 }`. The exit value of
//!   a `&mut` parameter (`x*` in an `ensures`) binds to `MutParamExit`, and
//!   only when the IR types that parameter `&mut T` / `*mut T`.
//! * Loop clauses: a free name binds to `Value(v)` where `v` is the loop
//!   header's block parameter carrying that source binding — matched by the
//!   compiler-owned `hir_local_id` of `source_place_bindings` against the
//!   loop's canonical binding catalog, whose `i`-th entry IS header parameter
//!   `i` (the E4/E5 carried-prefix rule of `lower_loop`).
//! * UNBINDABLE, so the clause goes opaque: a name from a destructuring
//!   parameter pattern (no `Param` of its own); an entry-state pointee read
//!   (`*x` in a `requires`/`decreases`, `old(*x)`), which waits for a
//!   `ParamPointeeEntry` place (DG-63, the blocked rows); a `mut` parameter in
//!   an `ensures` (its exit value is not its entry value); a projection, an
//!   `old(..)` or a synthetic (`__`) leaf; and a place whose IR type does not
//!   admit the clause sort.
//!
//! Sorts: `MachineInt{w}` / `PointerSizedInt{w}` -> `BitVec(w)`,
//! `MathematicalInt` -> `Int`, `Bool` -> `Bool`, `Float{32}` -> `Float{8,24}`,
//! `Float{64}` -> `Float{11,53}`. trust-ir's `clause_sort_admits` also admits
//! `Int` over a fixed-width place (the width-strip hazard its own
//! `ClauseBinding` doc names); the staged rung refuses that strip itself.
//!
//! # Naming
//!
//! The 08-27 design §5 and `contract_disclosure.rs` called this rung
//! `contract-bound-v2`; the owner amendment of 2026-08-30 gave ordinal 2 to
//! `obligation-bearing-pending-v2` and reserved the contract-bound name for
//! THIS rung. Shipped markers carry the rung ORDINAL, and under
//! D36/D37 (2026-10-02) the Clean carrier is a codegen-license
//! authority (`clean-carrier-gate`), not a ladder rung, so no rung sits between
//! the two: design name `contract-bound-v2` = marker [`CONTRACT_BOUND_MARKER`].

use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet};

use rustc_middle::mir::trust_contract::{
    TrustContractBundle, TrustContractKind, TrustContractPredicateKind, TrustContractProposition,
    TrustContractPropositionDomain, TrustContractSubject,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;
use trust_ir::proof::clause_typing::clause_sort_admits;
use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort};
use trust_ir::{
    BlockId, FuncId, FunctionSummary, Inst, Module, ObligationKind, ObligationSite,
    PROOF_OBLIGATION_SOURCE_TEXT_ID_MAX_BYTES, ProofFormula, ProofId, ProofObligation,
    ProofObligationSourceIdentity, ProofStatus, Ty, ValueId,
};

/// The stable, versioned `source_id` every contract row carries.
pub const CONTRACT_SOURCE_ID: &str = "trust-thir-lower/contract@1";
/// Schema of a clause whose every free name is bound to a typed IR place.
pub const CONTRACT_CLAUSE_SCHEMA: &str = "trust.contract-clause@1";
/// Schema of a clause carried as authored, with EMPTY (= unbindable) bindings.
pub const CONTRACT_OPAQUE_SCHEMA: &str = "trust.contract-opaque@1";
/// The coverage marker the owner-signed flip will give the contract-bound
/// rung (design name `contract-bound-v2`; see the module doc's "Naming").
pub const CONTRACT_BOUND_MARKER: &str = "contract-bound-v3";
/// The env var that turns on the zero-authority shadow
/// (`crate::contract_carry_shadow`): a directory the shadow writes
/// `<crate>.contract-carry.shadow.json` into. Unset = no work at all.
pub const TRUST_CONTRACT_CARRY_SHADOW_ENV: &str = "TRUST_CONTRACT_CARRY_SHADOW";
/// The exact refusal the staged rung gives a summary that claims `proved`.
pub const PROVED_FALSE_ONLY: &str = "contract-bound tier admits proved:false only";

// ============================== the carry (session state) ===================

/// Which role a clause plays, and so which row kind it mints.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ClauseRole {
    /// Function `requires` -> `summary.requires` + a `Precondition` row.
    Requires,
    /// Function `ensures` -> `summary.ensures` + a `Postcondition` row.
    Ensures,
    /// Function `decreases` -> `summary.decreases` + a `Termination` row.
    Decreases,
    /// Loop `invariant` -> a `LoopInvariant` row sited at the loop header.
    LoopInvariant,
    /// Loop `decreases` -> a `Termination` row sited at the loop header.
    LoopDecreases,
}

impl ClauseRole {
    /// The row kind this role mints.
    pub fn obligation_kind(self) -> ObligationKind {
        match self {
            Self::Requires => ObligationKind::Precondition,
            Self::Ensures => ObligationKind::Postcondition,
            Self::Decreases | Self::LoopDecreases => ObligationKind::Termination,
            Self::LoopInvariant => ObligationKind::LoopInvariant,
        }
    }

    /// Stable identity / disclosure tag.
    pub fn tag(self) -> &'static str {
        match self {
            Self::Requires => "requires",
            Self::Ensures => "ensures",
            Self::Decreases => "decreases",
            Self::LoopInvariant => "loop-invariant",
            Self::LoopDecreases => "loop-decreases",
        }
    }

    /// Function-level roles feed the summary; loop roles are sited rows only.
    pub fn is_loop(self) -> bool {
        matches!(self, Self::LoopInvariant | Self::LoopDecreases)
    }

    /// A predicate is Bool-sorted; a measure is numeric.
    fn is_measure(self) -> bool {
        matches!(self, Self::Decreases | Self::LoopDecreases)
    }
}

/// How a formal parameter is passed, from its rustc type at emission.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParamReference {
    /// `x: T` by value.
    ByValue,
    /// `x: &T`.
    Shared,
    /// `x: &mut T`.
    Mut,
    /// Anything else a pointee could hide behind (a raw pointer, a box, …).
    Other,
}

/// A formal parameter whose HIR pattern is a SIMPLE by-value binding (`x` or
/// `mut x`). A destructuring or wildcard pattern has no entry here: its names
/// have no `Param { index }` of their own.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CarryParam {
    /// Index into the IR signature's `FuncTy::params`.
    pub ir_index: u32,
    /// The binding's ident — the spelling the query's free names use.
    pub name: String,
    /// The compiler-owned HIR identity of the binding (owner-relative).
    pub hir_local_id: u32,
    /// `mut x`: the local may be reassigned, so its exit value is not its
    /// entry value.
    pub mutable: bool,
    pub reference: ParamReference,
}

/// Identity of a source loop within its owning body (the query's `TrustLoopId`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct LoopKey {
    pub index: u32,
    pub hir_local_id: u32,
}

/// One authored clause, copied out of the query at emission. Every field is
/// lifetime-free, so the record can ride session state to the finalizer.
#[derive(Debug, Clone, PartialEq)]
pub struct CarryClause {
    pub role: ClauseRole,
    /// Position in the query's storage: the dense `TrustContractId` for a
    /// function clause, the `loop_contracts` index for a loop clause. Stable,
    /// and part of the row identity.
    pub ordinal: u32,
    /// The loop a loop clause is authored on.
    pub loop_key: Option<LoopKey>,
    pub predicate: TrustContractPredicateKind,
    /// Loop clauses: the query's complete exact source-place map (name,
    /// `hir_local_id`), or `None` (fail-closed: every leaf unbindable).
    pub place_bindings: Option<Vec<(String, u32)>>,
}

/// A contract loop's header, recorded AT EMISSION by the loop-lowering arm of
/// `lib.rs` (`lower_loop`), exactly as `DirectObligationRecord` records an
/// assert position, and re-resolved at install.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContractLoopHeader {
    /// `TrustLoopId.hir_local_id` of the source loop.
    pub hir_local_id: u32,
    /// The header block the loop's clauses are sited at (`(header, 0)`).
    pub header: BlockId,
    /// The block whose `Br` enters the header (the pre-loop block).
    pub pre_header: BlockId,
    /// Every header block parameter, in order. The first
    /// `plan_bindings.len()` are the canonical source-binding prefix.
    pub header_params: Vec<ValueId>,
    /// The loop's canonical source-binding catalog (name-sorted, as
    /// `source_provenance::source_loop_plans` builds it): entry `i` is carried
    /// by header parameter `i`.
    pub plan_bindings: Vec<(String, u32)>,
}

/// Everything one contract-bearing body contributes to the carry, keyed by
/// `def_index` — the key `BodyRecord` and `DirectBodyObligations` ride under.
#[derive(Debug, Clone, PartialEq)]
pub struct ContractBodyRecord {
    pub def_index: u32,
    /// `with_no_trimmed_paths!(def_path_str)` (crate name NOT included) — the
    /// spelling `crate_module::record` and the direct rows use.
    pub def_path: String,
    /// `FuncTy::params.len()` of the per-body function at emission.
    pub ir_param_count: Option<u32>,
    pub params: Vec<CarryParam>,
    /// `Some(reason)`: no leaf of this body binds to a function place (e.g. a
    /// closure body, whose IR param 0 is the environment).
    pub binding_refusal: Option<&'static str>,
    pub clauses: Vec<CarryClause>,
    pub loop_headers: Vec<ContractLoopHeader>,
    /// A clause this carry cannot place at all (a kind or subject outside the
    /// carried set). The installer withholds the whole body with an error: a
    /// new kind is a forced decision, never a silent drop.
    pub refusal: Option<String>,
}

/// Session-scoped carry from the lowering to the finalizer (or the shadow).
/// Duplicate registrations are RETAINED as a defect ledger; the installer
/// fails closed on them.
#[derive(Debug, Default)]
pub struct ContractCarryRegistry {
    pub bodies: BTreeMap<u32, ContractBodyRecord>,
    pub duplicate_def_indices: Vec<u32>,
}

impl ContractCarryRegistry {
    pub fn insert(&mut self, body: ContractBodyRecord) {
        match self.bodies.entry(body.def_index) {
            Entry::Occupied(_) => self.duplicate_def_indices.push(body.def_index),
            Entry::Vacant(slot) => {
                slot.insert(body);
            }
        }
    }

    pub fn is_empty(&self) -> bool {
        self.bodies.is_empty() && self.duplicate_def_indices.is_empty()
    }
}

/// The emission-time header record `lower_loop` (`lib.rs`) takes for a
/// contract loop, right after it opens the header block. The lowering keeps
/// one per `hir_local_id` and moves them into the body's
/// [`ContractBodyRecord`] at registration, so the registry is keyed by
/// `(def_index, hir_local_id)`.
pub(crate) fn header_for_loop(
    hir_local_id: u32,
    header: BlockId,
    pre_header: BlockId,
    header_params: &[(ValueId, Ty)],
    plan_bindings: &[crate::source_provenance::SourceBindingPlan],
) -> ContractLoopHeader {
    ContractLoopHeader {
        hir_local_id,
        header,
        pre_header,
        header_params: header_params.iter().map(|(value, _)| *value).collect(),
        plan_bindings: plan_bindings
            .iter()
            .map(|binding| (binding.name.clone(), binding.hir_local_id))
            .collect(),
    }
}

/// Register one lowered body's contract carry. Called by the mainline
/// `mir_built`-hook lowering only (the same two gates as the direct-obligation
/// registration: never the `trust_ir_of` query lowering, never the discarded
/// collect-all census). Inert for a contract-free body.
pub(crate) fn register_contract_body(
    tcx: TyCtxt<'_>,
    def: LocalDefId,
    module: &Module,
    loop_headers: Vec<ContractLoopHeader>,
) {
    let ir_param_count = module
        .functions
        .first()
        .and_then(|function| module.func_type(function.ty))
        .and_then(|ft| u32::try_from(ft.params.len()).ok());
    let Some(mut record) = capture_contract_body(tcx, def, ir_param_count) else {
        return;
    };
    record.loop_headers = loop_headers;
    tcx.sess
        .with_trust_compiler_state::<ContractCarryRegistry, _>(|registry| registry.insert(record));
}

/// Read the existing compiler contract query and HIR formal-parameter map.
///
/// This is source data only. It neither installs contract obligations nor
/// changes direct-lane authority. Consumers must still resolve its types
/// against their actual emitted function before using [`carry_clause`].
pub fn capture_contract_body(
    tcx: TyCtxt<'_>,
    def: LocalDefId,
    ir_param_count: Option<u32>,
) -> Option<ContractBodyRecord> {
    // The query's own disk-cache contract: invoked only for items that can
    // carry contracts.
    if !TrustContractBundle::def_may_have_contracts(tcx, def) {
        return None;
    }
    let bundle = tcx.trust_contracts(def.to_def_id());
    if bundle.is_empty() {
        return None;
    }
    let def_path =
        rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def.to_def_id()));
    let (params, binding_refusal) = carry_params(tcx, def, ir_param_count);
    let (clauses, refusal) = carry_clauses(&bundle);
    let record = ContractBodyRecord {
        def_index: def.to_def_id().index.as_u32(),
        def_path,
        ir_param_count,
        params,
        binding_refusal,
        clauses,
        loop_headers: Vec::new(),
        refusal,
    };
    Some(record)
}

/// The bindable formal parameters of `def`, from its HIR param patterns and
/// their rustc types — never from a debug name.
fn carry_params(
    tcx: TyCtxt<'_>,
    def: LocalDefId,
    ir_param_count: Option<u32>,
) -> (Vec<CarryParam>, Option<&'static str>) {
    use rustc_hir::def::DefKind;
    use rustc_hir::{BindingMode, ByRef, Mutability, PatKind};
    use rustc_middle::ty;

    let Some(body) = tcx.hir_maybe_body_owned_by(def) else {
        return (Vec::new(), Some("the body owner has no HIR body"));
    };
    let typeck = tcx.typeck(def);
    let mut params = Vec::new();
    for (index, param) in body.params.iter().enumerate() {
        let PatKind::Binding(BindingMode(ByRef::No, mutability), hir_id, ident, None) =
            param.pat.kind
        else {
            continue;
        };
        let param_ty = typeck.pat_ty(param.pat);
        let reference = match param_ty.kind() {
            ty::Ref(_, _, Mutability::Mut) => ParamReference::Mut,
            ty::Ref(_, _, Mutability::Not) => ParamReference::Shared,
            ty::RawPtr(..) => ParamReference::Other,
            _ if param_ty.is_box() => ParamReference::Other,
            _ => ParamReference::ByValue,
        };
        let Ok(ir_index) = u32::try_from(index) else { continue };
        params.push(CarryParam {
            ir_index,
            name: ident.name.to_string(),
            hir_local_id: hir_id.local_id.as_u32(),
            mutable: mutability == Mutability::Mut,
            reference,
        });
    }
    // Only a fn / assoc fn body signs its declared params at `FuncTy::params`
    // index == HIR param index. A closure body's IR param 0 is its
    // environment (`lib.rs`, the closure-env signature convention), so no
    // closure leaf binds; its clauses are carried opaque.
    let refusal = if !matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn) {
        Some("a non-fn body (closure): its IR signature is not the HIR param list")
    } else if ir_param_count != u32::try_from(body.params.len()).ok() {
        Some("the IR signature's arity differs from the HIR param list")
    } else {
        None
    };
    (params, refusal)
}

/// Copy every authored clause out of the bundle. A kind or subject outside
/// the carried set is a body-level refusal (an install error), never a drop.
fn carry_clauses(bundle: &TrustContractBundle<'_>) -> (Vec<CarryClause>, Option<String>) {
    let mut clauses = Vec::new();
    let mut refusal = None;
    for (ordinal, contract) in bundle.contracts.iter().enumerate() {
        let role = match (contract.kind, contract.subject) {
            (TrustContractKind::Requires, TrustContractSubject::Function) => ClauseRole::Requires,
            (TrustContractKind::Ensures, TrustContractSubject::Function) => ClauseRole::Ensures,
            (TrustContractKind::Decreases, TrustContractSubject::Function) => ClauseRole::Decreases,
            (kind, subject) => {
                refusal.get_or_insert_with(|| {
                    format!(
                        "function contract {ordinal} has kind {kind:?} / subject {subject:?}, \
                         which the contract carry does not place"
                    )
                });
                continue;
            }
        };
        let Ok(ordinal) = u32::try_from(ordinal) else { continue };
        clauses.push(CarryClause {
            role,
            ordinal,
            loop_key: None,
            predicate: contract.predicate.kind.clone(),
            place_bindings: None,
        });
    }
    for (ordinal, contract) in bundle.loop_contracts.iter().enumerate() {
        let (role, id) = match (contract.kind, contract.subject) {
            (TrustContractKind::LoopInvariant, TrustContractSubject::HirLoop { id, .. }) => {
                (ClauseRole::LoopInvariant, id)
            }
            (TrustContractKind::Decreases, TrustContractSubject::HirLoop { id, .. }) => {
                (ClauseRole::LoopDecreases, id)
            }
            (kind, subject) => {
                refusal.get_or_insert_with(|| {
                    format!(
                        "loop contract {ordinal} has kind {kind:?} / subject {subject:?}, which \
                         the contract carry does not place"
                    )
                });
                continue;
            }
        };
        let Ok(ordinal) = u32::try_from(ordinal) else { continue };
        clauses.push(CarryClause {
            role,
            ordinal,
            loop_key: Some(LoopKey { index: id.index, hir_local_id: id.hir_local_id }),
            predicate: contract.predicate.kind.clone(),
            place_bindings: contract.predicate.source_place_bindings.as_ref().map(|bindings| {
                bindings
                    .iter()
                    .map(|binding| (binding.name.to_string(), binding.hir_local_id))
                    .collect()
            }),
        });
    }
    (clauses, refusal)
}

// ============================== the clause carrier (pure) ===================

/// A loop header, re-resolved against the module the rows go into.
#[derive(Debug, Clone)]
pub struct ResolvedHeader<'a> {
    pub record: &'a ContractLoopHeader,
    /// The ASSEMBLED type of each header parameter (the splice may remap
    /// table ids, so the recorded emission-time type is never trusted).
    pub param_tys: Vec<Ty>,
}

/// What the clause carrier may bind against.
#[derive(Debug, Clone)]
pub struct ClauseContext<'a> {
    pub params: &'a [CarryParam],
    pub binding_refusal: Option<&'static str>,
    pub param_tys: &'a [Ty],
    pub return_tys: &'a [Ty],
    pub pointer_bits: Option<u32>,
    /// The re-resolved header of the clause's loop (loop clauses only).
    pub header: Option<ResolvedHeader<'a>>,
}

/// One carried clause: the formula, and why it went opaque if it did.
#[derive(Debug, Clone, PartialEq)]
pub struct CarriedClause {
    pub formula: ProofFormula,
    pub opaque_reason: Option<String>,
}

/// The ClauseSort a proposition domain is read at, or `None` (unbindable).
pub fn clause_sort_for_domain(domain: TrustContractPropositionDomain) -> Option<ClauseSort> {
    match domain {
        TrustContractPropositionDomain::Bool => Some(ClauseSort::Bool),
        TrustContractPropositionDomain::MathematicalInt => Some(ClauseSort::Int),
        TrustContractPropositionDomain::MachineInt { width, .. }
        | TrustContractPropositionDomain::PointerSizedInt { width, .. } => {
            Some(ClauseSort::BitVec(width))
        }
        TrustContractPropositionDomain::Float { width: 32 } => {
            Some(ClauseSort::Float { eb: 8, sb: 24 })
        }
        TrustContractPropositionDomain::Float { width: 64 } => {
            Some(ClauseSort::Float { eb: 11, sb: 53 })
        }
        TrustContractPropositionDomain::Float { .. } => None,
    }
}

/// Carry one clause. Pure: every input is in `clause` and `cx`.
pub fn carry_clause(clause: &CarryClause, cx: &ClauseContext<'_>) -> CarriedClause {
    let typed = match &clause.predicate {
        TrustContractPredicateKind::Typed { proposition, .. } => Some(proposition.clone()),
        TrustContractPredicateKind::BoolLiteral { value } if !clause.role.is_measure() => {
            Some(TrustContractProposition::Bool(*value))
        }
        TrustContractPredicateKind::BoolLiteral { .. }
        | TrustContractPredicateKind::Opaque { .. }
        | TrustContractPredicateKind::MirLocal { .. }
        | TrustContractPredicateKind::Unsupported { .. } => None,
    };
    let Some(proposition) = typed else {
        return opaque(clause, "the query carries no typed proposition for this clause".into());
    };
    let mut leaves: BTreeMap<String, TrustContractPropositionDomain> = BTreeMap::new();
    if let Err(name) = collect_leaves(&proposition, &mut leaves) {
        return opaque(clause, format!("free name `{name}` carries two domains"));
    }
    let mut bindings: Vec<(String, ClauseBinding)> = Vec::with_capacity(leaves.len());
    for (name, domain) in &leaves {
        match bind_leaf(name, *domain, clause, cx) {
            Ok(binding) => bindings.push((name.clone(), binding)),
            Err(reason) => return opaque(clause, format!("free name `{name}`: {reason}")),
        }
    }
    let payload = crate::contract_render::render_proposition(&proposition);
    let mut formula = ProofFormula::new(CONTRACT_CLAUSE_SCHEMA, payload);
    if let Some((text, sort)) = smt::render_clause(&proposition, clause.role.is_measure()) {
        formula.smtlib = Some(text);
        formula.sort = Some(sort);
    }
    formula.bindings = bindings;
    CarriedClause { formula, opaque_reason: None }
}

fn opaque(clause: &CarryClause, reason: String) -> CarriedClause {
    CarriedClause {
        formula: ProofFormula::new(
            CONTRACT_OPAQUE_SCHEMA,
            crate::contract_render::render_predicate(&clause.predicate),
        ),
        opaque_reason: Some(reason),
    }
}

/// Every `Var` leaf, name -> domain. `Err(name)` when one name carries two
/// domains (the query never builds that; refused rather than guessed).
fn collect_leaves(
    p: &TrustContractProposition,
    out: &mut BTreeMap<String, TrustContractPropositionDomain>,
) -> Result<(), String> {
    use TrustContractProposition as P;
    match p {
        P::Var { name, domain } => match out.entry(name.to_string()) {
            Entry::Vacant(slot) => {
                slot.insert(*domain);
                Ok(())
            }
            Entry::Occupied(slot) if slot.get() == domain => Ok(()),
            Entry::Occupied(slot) => Err(slot.key().clone()),
        },
        P::Bool(_) | P::Int(_) | P::UInt(_) | P::Float { .. } => Ok(()),
        P::Not(a) | P::Neg(a) => collect_leaves(a, out),
        P::And(xs) | P::Or(xs) => xs.iter().try_for_each(|x| collect_leaves(x, out)),
        P::Implies(a, b)
        | P::Eq(a, b)
        | P::Lt(a, b)
        | P::Le(a, b)
        | P::Gt(a, b)
        | P::Ge(a, b)
        | P::Add(a, b)
        | P::Sub(a, b)
        | P::Mul(a, b)
        | P::Div(a, b)
        | P::Rem(a, b) => {
            collect_leaves(a, out)?;
            collect_leaves(b, out)
        }
    }
}

/// A plain source identifier: no projection, deref, index or synthetic
/// (`__`, `old_`) spelling.
fn is_plain_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else { return false };
    (first.is_ascii_alphabetic() || first == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
        && !name.contains("__")
        && !name.starts_with("old_")
}

fn bind_leaf(
    name: &str,
    domain: TrustContractPropositionDomain,
    clause: &CarryClause,
    cx: &ClauseContext<'_>,
) -> Result<ClauseBinding, String> {
    let sort = clause_sort_for_domain(domain)
        .ok_or_else(|| format!("its domain {domain:?} has no clause sort"))?;
    let (place, ir_ty) = if clause.role.is_loop() {
        bind_loop_leaf(name, clause, cx)?
    } else {
        bind_function_leaf(name, clause.role, cx)?
    };
    if !clause_sort_admits(&sort, &ir_ty, cx.pointer_bits) {
        return Err(format!(
            "its place {place:?} has IR type {ir_ty}, which does not admit sort {sort:?}"
        ));
    }
    Ok(ClauseBinding { sort, place })
}

fn bind_function_leaf(
    name: &str,
    role: ClauseRole,
    cx: &ClauseContext<'_>,
) -> Result<(ClausePlace, Ty), String> {
    if let Some(reason) = cx.binding_refusal {
        return Err(reason.to_string());
    }
    if name == "_0" || name == "result" {
        if role != ClauseRole::Ensures {
            return Err("`result` outside an ensures clause".into());
        }
        let ty = cx.return_tys.first().ok_or("the IR signature has no return slot")?;
        return Ok((ClausePlace::ResultSlot { index: 0 }, ty.clone()));
    }
    let find = |base: &str| cx.params.iter().find(|param| param.name == base);
    if let Some(base) = name.strip_suffix('*') {
        if !is_plain_identifier(base) {
            return Err("a projected or nested pointee read has no ClausePlace".into());
        }
        let param = find(base).ok_or("names no simple parameter binding")?;
        return match (role, param.reference) {
            (ClauseRole::Ensures, ParamReference::Mut) if param.mutable => Err(format!(
                "`mut` reference parameter `{base}` may be reassigned, so `{base}*` at exit \
                 need not be the exit value behind the original borrow that MutParamExit names"
            )),
            (ClauseRole::Ensures, ParamReference::Mut) => {
                let ty = cx
                    .param_tys
                    .get(param.ir_index as usize)
                    .ok_or("the parameter is past the IR signature")?;
                match ty {
                    Ty::RefMut(pointee) | Ty::PtrMut(pointee) => Ok((
                        ClausePlace::MutParamExit { index: param.ir_index },
                        (**pointee).clone(),
                    )),
                    other => Err(format!(
                        "the exit value of `&mut` parameter `{base}` needs a typed `&mut T` / \
                         `*mut T` IR parameter for MutParamExit, and the IR spells it {other}"
                    )),
                }
            }
            (ClauseRole::Ensures, _) => Err(format!(
                "the pointee of non-`&mut` parameter `{base}` has no ClausePlace (waits for \
                 ParamPointeeEntry, DG-63)"
            )),
            _ => Err(format!(
                "an entry-state pointee read of reference parameter `{base}` has no ClausePlace \
                 (waits for ParamPointeeEntry, DG-63)"
            )),
        };
    }
    if !is_plain_identifier(name) {
        return Err("a projection, `old(..)` or synthetic leaf has no ClausePlace".into());
    }
    let param = find(name).ok_or(
        "names no simple by-value parameter binding (a destructured or unknown name has no \
         Param of its own)",
    )?;
    if param.reference != ParamReference::ByValue {
        return Err("a reference parameter itself is not a scalar place".into());
    }
    if role == ClauseRole::Ensures && param.mutable {
        return Err(format!(
            "`mut` parameter `{name}` may be reassigned, so its value at exit is not its entry \
             value and no ClausePlace says which an ensures clause reads"
        ));
    }
    let ty = cx
        .param_tys
        .get(param.ir_index as usize)
        .ok_or("the parameter is past the IR signature")?;
    Ok((ClausePlace::Param { index: param.ir_index }, ty.clone()))
}

fn bind_loop_leaf(
    name: &str,
    clause: &CarryClause,
    cx: &ClauseContext<'_>,
) -> Result<(ClausePlace, Ty), String> {
    let header = cx.header.as_ref().ok_or("the loop header did not re-resolve")?;
    if !is_plain_identifier(name) {
        return Err("a projection, deref or synthetic leaf is not a carried source binding".into());
    }
    let bindings = clause
        .place_bindings
        .as_ref()
        .ok_or("the query recorded no complete source-place map for this clause")?;
    let (_, hir_local_id) = bindings
        .iter()
        .find(|(binding, _)| binding == name)
        .ok_or("not an exact source binding of this clause")?;
    let position = header
        .record
        .plan_bindings
        .iter()
        .position(|(binding, hir)| binding == name && hir == hir_local_id)
        .ok_or("not in the loop's carried source-binding catalog")?;
    let value = header
        .record
        .header_params
        .get(position)
        .ok_or("the header carries fewer parameters than its binding catalog")?;
    let ty = header.param_tys.get(position).ok_or("the assembled header lost a parameter")?;
    Ok((ClausePlace::Value(*value), ty.clone()))
}

// ============================== SMT-LIB rendering (exact or none) ===========

mod smt {
    use rustc_middle::mir::trust_contract::{
        TrustContractProposition as P, TrustContractPropositionDomain as D,
    };

    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Sort {
        Bool,
        Int,
        Bv { width: u32, signed: bool },
    }

    /// The exact SMT-LIB2 rendering of a whole clause and its sort, or `None`
    /// when any part has no exact rendering. Spec arithmetic is MATHEMATICAL
    /// (`proposition_domain_sort` reads every machine integer as `Int`), so a
    /// bit-vector `+`/`-`/`*` (which wraps) is never emitted for it; `/` and
    /// `%` have no exact SMT-LIB reading here (truncating vs. Euclidean), and
    /// floats are not rendered. A bit-vector measure has no exact rendering
    /// either: a `decreases` order needs the signedness its sort cannot carry.
    pub(super) fn render_clause(p: &P, measure: bool) -> Option<(String, String)> {
        let sort = sort_of(p)?;
        match (measure, sort) {
            (false, Some(Sort::Bool)) => Some((render(p, Sort::Bool)?, "Bool".to_string())),
            (true, Some(Sort::Int) | None) => Some((render(p, Sort::Int)?, "Int".to_string())),
            _ => None,
        }
    }

    fn domain_sort(domain: D) -> Option<Sort> {
        match domain {
            D::Bool => Some(Sort::Bool),
            D::MathematicalInt => Some(Sort::Int),
            D::MachineInt { width, signed } | D::PointerSizedInt { width, signed } => {
                Some(Sort::Bv { width, signed })
            }
            D::Float { .. } => None,
        }
    }

    /// `Some(None)` is a literal whose sort its context decides.
    fn sort_of(p: &P) -> Option<Option<Sort>> {
        match p {
            P::Bool(_)
            | P::Not(_)
            | P::And(_)
            | P::Or(_)
            | P::Implies(..)
            | P::Eq(..)
            | P::Lt(..)
            | P::Le(..)
            | P::Gt(..)
            | P::Ge(..) => Some(Some(Sort::Bool)),
            P::Int(_) | P::UInt(_) => Some(None),
            P::Float { .. } => None,
            P::Var { domain, .. } => Some(Some(domain_sort(*domain)?)),
            P::Add(a, b) | P::Sub(a, b) | P::Mul(a, b) | P::Div(a, b) | P::Rem(a, b) => {
                merge(sort_of(a)?, sort_of(b)?)
            }
            P::Neg(a) => sort_of(a),
        }
    }

    fn merge(a: Option<Sort>, b: Option<Sort>) -> Option<Option<Sort>> {
        match (a, b) {
            (Some(x), Some(y)) if x != y => None,
            (Some(x), _) | (_, Some(x)) => Some(Some(x)),
            (None, None) => Some(None),
        }
    }

    fn symbol(name: &str) -> Option<String> {
        if trust_ir::proof::clause_typing::is_smt_simple_symbol(name) {
            Some(name.to_string())
        } else if !name.is_empty() && !name.contains(['|', '\\']) {
            Some(format!("|{name}|"))
        } else {
            None
        }
    }

    fn literal(value: i128, sort: Sort) -> Option<String> {
        match sort {
            Sort::Bool => None,
            Sort::Int if value < 0 => Some(format!("(- {})", value.unsigned_abs())),
            Sort::Int => Some(value.to_string()),
            Sort::Bv { width, signed } => {
                if width == 0 || width > 128 {
                    return None;
                }
                let fits = if signed {
                    width == 128 || {
                        let bound = 1i128 << (width - 1);
                        (-bound..bound).contains(&value)
                    }
                } else {
                    // Every non-negative i128 is below 2^127.
                    value >= 0 && (width >= 127 || value < 1i128 << width)
                };
                if !fits {
                    return None;
                }
                let mask = if width == 128 { u128::MAX } else { (1u128 << width) - 1 };
                Some(format!("(_ bv{} {width})", (value as u128) & mask))
            }
        }
    }

    fn unsigned_literal(value: u128, sort: Sort) -> Option<String> {
        match sort {
            Sort::Bool => None,
            Sort::Int => Some(value.to_string()),
            Sort::Bv { width, signed } => {
                let max = if signed {
                    (1u128.checked_shl(width.checked_sub(1)?)?).checked_sub(1)?
                } else if width >= 128 {
                    u128::MAX
                } else {
                    (1u128 << width) - 1
                };
                (width > 0 && width <= 128 && value <= max)
                    .then(|| format!("(_ bv{value} {width})"))
            }
        }
    }

    fn render(p: &P, expect: Sort) -> Option<String> {
        let is_bool = expect == Sort::Bool;
        match p {
            P::Bool(b) => is_bool.then(|| b.to_string()),
            P::Int(value) => literal(*value, expect),
            P::UInt(value) => unsigned_literal(*value, expect),
            P::Float { .. } => None,
            P::Var { name, domain } => {
                if domain_sort(*domain)? != expect {
                    return None;
                }
                symbol(name.as_str())
            }
            P::Not(a) => {
                if !is_bool {
                    return None;
                }
                Some(format!("(not {})", render(a, Sort::Bool)?))
            }
            P::And(xs) | P::Or(xs) => {
                if !is_bool {
                    return None;
                }
                let parts = xs.iter().map(|x| render(x, Sort::Bool)).collect::<Option<Vec<_>>>()?;
                let (op, unit) =
                    if matches!(p, P::And(_)) { ("and", "true") } else { ("or", "false") };
                Some(match parts.len() {
                    0 => unit.to_string(),
                    1 => parts.into_iter().next()?,
                    _ => format!("({op} {})", parts.join(" ")),
                })
            }
            P::Implies(a, b) => {
                if !is_bool {
                    return None;
                }
                Some(format!("(=> {} {})", render(a, Sort::Bool)?, render(b, Sort::Bool)?))
            }
            P::Eq(a, b) => {
                if !is_bool {
                    return None;
                }
                if sort_of(a)? == Some(Sort::Bool) || sort_of(b)? == Some(Sort::Bool) {
                    return Some(format!(
                        "(= {} {})",
                        render(a, Sort::Bool)?,
                        render(b, Sort::Bool)?
                    ));
                }
                let (_, a, b) = numeric_pair(a, b)?;
                Some(format!("(= {a} {b})"))
            }
            P::Lt(a, b) if is_bool => compare(a, b, ["<", "bvslt", "bvult"]),
            P::Le(a, b) if is_bool => compare(a, b, ["<=", "bvsle", "bvule"]),
            P::Gt(a, b) if is_bool => compare(a, b, [">", "bvsgt", "bvugt"]),
            P::Ge(a, b) if is_bool => compare(a, b, [">=", "bvsge", "bvuge"]),
            P::Lt(..) | P::Le(..) | P::Gt(..) | P::Ge(..) => None,
            P::Add(a, b) => int_arith(a, b, "+", expect),
            P::Sub(a, b) => int_arith(a, b, "-", expect),
            P::Mul(a, b) => int_arith(a, b, "*", expect),
            P::Div(..) | P::Rem(..) => None,
            P::Neg(a) => {
                if expect != Sort::Int {
                    return None;
                }
                Some(format!("(- {})", render(a, Sort::Int)?))
            }
        }
    }

    /// Both operands at their merged numeric sort (a literal pair is `Int`).
    fn numeric_pair(a: &P, b: &P) -> Option<(Sort, String, String)> {
        let sort = merge(sort_of(a)?, sort_of(b)?)?.unwrap_or(Sort::Int);
        if sort == Sort::Bool {
            return None;
        }
        Some((sort, render(a, sort)?, render(b, sort)?))
    }

    /// `[int, signed bit-vector, unsigned bit-vector]` operator spellings.
    fn compare(a: &P, b: &P, ops: [&str; 3]) -> Option<String> {
        let (sort, a, b) = numeric_pair(a, b)?;
        let op = match sort {
            Sort::Int => ops[0],
            Sort::Bv { signed: true, .. } => ops[1],
            Sort::Bv { signed: false, .. } => ops[2],
            Sort::Bool => return None,
        };
        Some(format!("({op} {a} {b})"))
    }

    /// Arithmetic is rendered only over `Int`: a bit-vector `bvadd` WRAPS and
    /// would state a different formula than the mathematical spec `+`.
    fn int_arith(a: &P, b: &P, op: &str, expect: Sort) -> Option<String> {
        let (sort, a, b) = numeric_pair(a, b)?;
        (sort == Sort::Int && expect == Sort::Int).then(|| format!("({op} {a} {b})"))
    }
}

// ============================== install (staged; never on the published module)

/// What [`install_contract_obligations`] did. Counts are DISCLOSURES; the
/// `errors` the caller collected are the gate.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ContractInstallOutcome {
    /// Bodies whose carry installed (summary and/or rows).
    pub bodies_installed: usize,
    /// Registered bodies with no spliced `FuncId` (their rows would dangle).
    pub bodies_skipped_unspliced: usize,
    /// Bodies withheld whole by a carry defect (an error was pushed).
    pub bodies_withheld: usize,
    pub summaries_installed: usize,
    pub rows_installed: usize,
    /// Loop-clause rows withheld because their header did not re-resolve.
    pub loop_rows_withheld: usize,
    pub clauses_typed: usize,
    pub clauses_opaque: usize,
    /// One entry per opaque clause: `(def_path, role tag, ordinal, reason)`.
    pub opaque: Vec<(String, &'static str, u32, String)>,
}

/// Re-resolve a recorded loop header against the module the rows go into.
/// `Err` is a carry defect: the rows are withheld, never sited by guess.
pub fn reresolve_header<'a>(
    function: &trust_ir::Function,
    record: &'a ContractLoopHeader,
) -> Result<ResolvedHeader<'a>, String> {
    let header =
        function.blocks.iter().find(|block| block.id == record.header).ok_or_else(|| {
            format!("header block {} is not in the function", record.header.index())
        })?;
    let params: Vec<ValueId> = header.params.iter().map(|(value, _)| *value).collect();
    if params != record.header_params {
        return Err(format!(
            "header block {} carries parameters {params:?}, not the recorded {:?}",
            record.header.index(),
            record.header_params
        ));
    }
    if record.plan_bindings.len() > params.len() {
        return Err("the header carries fewer parameters than its binding catalog".to_string());
    }
    if header.body.is_empty() {
        return Err(format!("header block {} has no instruction 0", record.header.index()));
    }
    let entry =
        function.blocks.iter().find(|block| block.id == record.pre_header).ok_or_else(|| {
            format!("pre-header block {} is not in the function", record.pre_header.index())
        })?;
    match entry.body.last().map(|node| &node.inst) {
        Some(Inst::Br { target, .. }) if *target == record.header => {}
        other => {
            return Err(format!(
                "pre-header block {} does not end in `br` to the header {} (ends in {other:?})",
                record.pre_header.index(),
                record.header.index()
            ));
        }
    }
    Ok(ResolvedHeader {
        record,
        param_tys: header.params.iter().map(|(_, ty)| ty.clone()).collect(),
    })
}

/// Install the recorded contract carry into an ASSEMBLED crate module:
/// summaries plus Pending contract-kind rows.
///
/// STAGED: no production path calls this on the published module (the
/// owner-signed flip, DG-60, adds that call at the finalizer, after the
/// direct-obligation install and before run 4). The zero-authority shadow
/// calls it on a clone.
///
/// * `assigned` — assemble pass 1's dense `def_index -> FuncId` map, sorted.
/// * Every carry DEFECT pushes into `errors` and withholds — the whole body,
///   or (a header that does not re-resolve) that loop's rows. An unbindable
///   leaf is not a defect: the clause is carried opaque and disclosed.
pub fn install_contract_obligations(
    module: &mut Module,
    crate_name: &str,
    assigned: &[(u32, FuncId)],
    registry: ContractCarryRegistry,
    errors: &mut Vec<String>,
) -> ContractInstallOutcome {
    let mut outcome = ContractInstallOutcome::default();
    if !registry.duplicate_def_indices.is_empty() {
        errors.push(format!(
            "contract-carry install: duplicate per-body registrations for def indices {:?}; a \
             body lowered twice cannot contribute contract rows (fix the registration wiring, \
             not this gate)",
            registry.duplicate_def_indices
        ));
        return outcome;
    }
    let pointer_bits = module.target_info.as_ref().map(|t| t.pointer_size.saturating_mul(8));
    let mut seen: BTreeSet<(String, String)> = module
        .proof_obligations
        .iter()
        .filter_map(|o| o.source.as_ref())
        .map(|s| (s.source_id.clone(), s.assertion_id.clone()))
        .collect();

    for (def_index, body) in &registry.bodies {
        let Some(fid) =
            assigned.binary_search_by_key(def_index, |(d, _)| *d).ok().map(|i| assigned[i].1)
        else {
            outcome.bodies_skipped_unspliced += 1;
            continue;
        };
        let at = format!("`{crate_name}::{}`", body.def_path);
        let withhold = |errors: &mut Vec<String>, detail: String| {
            errors.push(format!(
                "contract-carry install: {at}: {detail}; body withheld (fail closed)"
            ));
        };
        let candidates: Vec<usize> = module
            .functions
            .iter()
            .enumerate()
            .filter(|(_, f)| f.id == fid)
            .map(|(i, _)| i)
            .collect();
        let [position] = candidates[..] else {
            withhold(
                errors,
                format!("FuncId {} names {} functions", fid.index(), candidates.len()),
            );
            outcome.bodies_withheld += 1;
            continue;
        };
        let function = &module.functions[position];
        let defect = if function.is_declaration() {
            Some("its FuncId is a body-less declaration, and a contract summary is never minted on one".to_string())
        } else if function.producer != Some(trust_ir::Producer::TRust) {
            Some(format!("its function carries producer {:?}, not Some(TRust)", function.producer))
        } else if function.summary.is_some() {
            Some(
                "its function already carries a summary, which this install never overwrites"
                    .to_string(),
            )
        } else if let Some(refusal) = &body.refusal {
            Some(refusal.clone())
        } else {
            None
        };
        if let Some(detail) = defect {
            withhold(errors, detail);
            outcome.bodies_withheld += 1;
            continue;
        }
        let Some(signature) = module.func_type(function.ty).cloned() else {
            withhold(errors, format!("functy.{} does not resolve", function.ty.index()));
            outcome.bodies_withheld += 1;
            continue;
        };
        if body.ir_param_count != u32::try_from(signature.params.len()).ok() {
            withhold(
                errors,
                format!(
                    "the recorded IR arity {:?} is not the assembled signature's {}",
                    body.ir_param_count,
                    signature.params.len()
                ),
            );
            outcome.bodies_withheld += 1;
            continue;
        }

        // Re-resolve every loop header a clause is sited at.
        let mut headers: BTreeMap<u32, Result<ResolvedHeader<'_>, String>> = BTreeMap::new();
        for clause in &body.clauses {
            let Some(key) = clause.loop_key else { continue };
            headers.entry(key.hir_local_id).or_insert_with(|| {
                let mut matching =
                    body.loop_headers.iter().filter(|h| h.hir_local_id == key.hir_local_id);
                match (matching.next(), matching.next()) {
                    (None, _) => Err(format!(
                        "loop (hir local {}) has no recorded header; the emission-time binding \
                         is missing",
                        key.hir_local_id
                    )),
                    (Some(_), Some(_)) => Err(format!(
                        "loop (hir local {}) has more than one recorded header",
                        key.hir_local_id
                    )),
                    (Some(record), None) => reresolve_header(function, record),
                }
            });
        }
        for (hir, resolved) in &headers {
            if let Err(detail) = resolved {
                errors.push(format!(
                    "contract-carry install: {at}: loop (hir local {hir}) header self-check \
                     failed: {detail}; its rows are withheld, never sited by guess (fail closed)"
                ));
            }
        }

        let mut summary = FunctionSummary::new();
        summary.params = (0..signature.params.len())
            .map(|index| {
                body.params
                    .iter()
                    .find(|param| param.ir_index as usize == index)
                    .map_or_else(|| format!("__param{index}"), |param| param.name.clone())
            })
            .collect();
        let mut rows: Vec<(ClauseRole, u32, Option<LoopKey>, ProofFormula, Option<BlockId>)> =
            Vec::new();
        for clause in &body.clauses {
            let header = match clause.loop_key {
                None => None,
                Some(key) => match headers.get(&key.hir_local_id) {
                    Some(Ok(resolved)) => Some(resolved.clone()),
                    _ => {
                        outcome.loop_rows_withheld += 1;
                        continue;
                    }
                },
            };
            let header_block = header.as_ref().map(|h| h.record.header);
            let cx = ClauseContext {
                params: &body.params,
                binding_refusal: body.binding_refusal,
                param_tys: &signature.params,
                return_tys: &signature.returns,
                pointer_bits,
                header,
            };
            let carried = carry_clause(clause, &cx);
            match &carried.opaque_reason {
                None => outcome.clauses_typed += 1,
                Some(reason) => {
                    outcome.clauses_opaque += 1;
                    outcome.opaque.push((
                        body.def_path.clone(),
                        clause.role.tag(),
                        clause.ordinal,
                        reason.clone(),
                    ));
                }
            }
            match clause.role {
                ClauseRole::Requires => summary.requires.push(carried.formula.clone()),
                ClauseRole::Ensures => summary.ensures.push(carried.formula.clone()),
                ClauseRole::Decreases => summary.decreases.push(carried.formula.clone()),
                ClauseRole::LoopInvariant | ClauseRole::LoopDecreases => {}
            }
            rows.push((
                clause.role,
                clause.ordinal,
                clause.loop_key,
                carried.formula,
                header_block,
            ));
        }

        let has_fn_clause = body.clauses.iter().any(|c| !c.role.is_loop());
        let mut minted: Vec<ProofObligation> = Vec::with_capacity(rows.len());
        let mut identity_defect = None;
        for (role, ordinal, loop_key, formula, header_block) in rows {
            let assertion_id =
                clause_assertion_id(crate_name, &body.def_path, role, ordinal, loop_key);
            if !seen.insert((CONTRACT_SOURCE_ID.to_string(), assertion_id.clone())) {
                identity_defect = Some(assertion_id);
                break;
            }
            let Ok(next) = u32::try_from(module.proof_obligations.len() + minted.len()) else {
                identity_defect = Some("the obligation table exceeds u32".to_string());
                break;
            };
            let mut row = ProofObligation::new(
                ProofId::new(next),
                role.obligation_kind(),
                ProofStatus::Pending,
                clamp_description(&format!(
                    "authored `{}` clause {ordinal} of `{crate_name}::{}`: carried at the \
                     staged contract-bound tier. RECORDED BY THE LOWERING, NOT PROVED.",
                    role.tag(),
                    body.def_path
                )),
            )
            .with_function(fid)
            .with_source(ProofObligationSourceIdentity::new(CONTRACT_SOURCE_ID, assertion_id))
            .with_formula(formula);
            if let Some(header) = header_block {
                row = row.with_site(ObligationSite::new(fid, header, 0));
            }
            minted.push(row);
        }
        if let Some(identity) = identity_defect {
            withhold(
                errors,
                format!(
                    "duplicate or unmintable contract-row identity ({CONTRACT_SOURCE_ID}, {identity})"
                ),
            );
            outcome.bodies_withheld += 1;
            continue;
        }
        if has_fn_clause {
            module.functions[position].summary = Some(summary);
            outcome.summaries_installed += 1;
        }
        outcome.rows_installed += minted.len();
        module.proof_obligations.extend(minted);
        outcome.bodies_installed += 1;
    }
    outcome
}

/// One emission identity recipe for the installer and its diagnostic consumer.
pub(crate) fn clause_assertion_id(
    crate_name: &str,
    def_path: &str,
    role: ClauseRole,
    ordinal: u32,
    loop_key: Option<LoopKey>,
) -> String {
    let suffix = match loop_key {
        None => format!("#{}#c{ordinal}", role.tag()),
        Some(key) => format!("#loop{}#{}#c{ordinal}", key.index, role.tag()),
    };
    clamp_identity(crate_name, def_path, &suffix)
}

/// Suffix-preserving identity clamp (the direct lane's `direct_assertion_id`
/// rule): the `{crate}::{def_path}` head is cut to the byte cap, the
/// `#role#c{ordinal}` tail that makes it unique is always kept.
fn clamp_identity(crate_name: &str, def_path: &str, suffix: &str) -> String {
    let max = PROOF_OBLIGATION_SOURCE_TEXT_ID_MAX_BYTES;
    let clean =
        |s: &str| -> String { s.chars().map(|c| if c.is_control() { '_' } else { c }).collect() };
    let suffix = clean(suffix);
    let budget = max.saturating_sub(suffix.len());
    let head_raw = clean(&format!("{crate_name}::{def_path}"));
    let mut head = String::new();
    for (offset, ch) in head_raw.trim().char_indices() {
        if offset + ch.len_utf8() > budget {
            break;
        }
        head.push(ch);
    }
    let id = format!("{}{suffix}", head.trim_end());
    if id.trim().is_empty() { "contract".to_string() } else { id }
}

/// One-line description free of the text format's string delimiters.
fn clamp_description(value: &str) -> String {
    value
        .chars()
        .map(|c| match c {
            '"' | '\\' => '\'',
            c if c.is_control() => ' ',
            c => c,
        })
        .collect()
}

// ============================== the staged rung ==============================

/// The canonical clause sort of an IR place type — what the carry binds a
/// place at. `Int` over a fixed-width integer is NOT canonical (the
/// width-strip hazard), although trust-ir's `clause_sort_admits` admits it.
fn canonical_sort(ty: &Ty, pointer_bits: Option<u32>) -> Option<ClauseSort> {
    match ty {
        Ty::Bool => Some(ClauseSort::Bool),
        Ty::F32 => Some(ClauseSort::Float { eb: 8, sb: 24 }),
        Ty::F64 => Some(ClauseSort::Float { eb: 11, sb: 53 }),
        Ty::Isize | Ty::Usize => pointer_bits.map(ClauseSort::BitVec),
        _ if ty.is_integer() => ty.bit_width().map(ClauseSort::BitVec),
        _ => None,
    }
}

/// The STAGED contract-bound rung: exactly what the owner-signed
/// `DirectObligationTier::ContractBoundPending` arm admits (DG-60), as a pure
/// function. NOT the live tier — `DIRECT_OBLIGATION_CAPABILITY` stays
/// `ObligationBearingPending`, whose arm refuses every row this admits.
///
/// Admits exactly:
/// * on a BODIED function, a `summary` with `proved == false`,
///   `backed_by == None`, every clause of schema [`CONTRACT_CLAUSE_SCHEMA`]
///   (every binding at its place's canonical sort) or
///   [`CONTRACT_OPAQUE_SCHEMA`] (empty bindings, no rendering);
/// * `Pending` rows of kind `Precondition` / `Postcondition` / `Termination` /
///   `LoopInvariant` with `source_id` [`CONTRACT_SOURCE_ID`], a function
///   scope, a formula and no public identity; a function-level row's formula
///   is a clause of its function's summary in the role its kind backs, and a
///   loop row (`LoopInvariant`, or a sited `Termination`) is sited in its own
///   function;
/// * everything `obligation-bearing-pending-v2` admits — the remainder is
///   DELEGATED to `inventory_errors_at_tier(.., ObligationBearingPending)`, so
///   certificates, diagnostics, function claims, spec proof bindings, Linked
///   spec modules and every foreign row stay refused exactly as there.
pub fn contract_bound_inventory_errors(module: &Module) -> Vec<String> {
    let mut errors = Vec::new();
    let pointer_bits = module.target_info.as_ref().map(|t| t.pointer_size.saturating_mul(8));
    let tripwire = "direct-THIR contract-bound authority tripwire";

    for function in &module.functions {
        let Some(summary) = &function.summary else { continue };
        let at = format!("function #{} (`{}`)", function.id.index(), function.name);
        if function.is_declaration() {
            errors.push(format!(
                "{tripwire}: {at} is a body-less declaration carrying a summary; the \
                 contract-bound tier admits a summary only on a bodied function"
            ));
        }
        if summary.proved {
            errors.push(format!("{tripwire}: {at}: {PROVED_FALSE_ONLY}"));
        }
        if summary.backed_by.is_some() {
            errors.push(format!(
                "{tripwire}: {at}: the contract-bound tier admits backed_by: None only"
            ));
        }
        let signature = module.func_type(function.ty);
        for (role, clauses) in [
            ("requires", &summary.requires),
            ("ensures", &summary.ensures),
            ("decreases", &summary.decreases),
        ] {
            for (index, clause) in clauses.iter().enumerate() {
                for detail in clause_shape_errors(function, signature, clause, pointer_bits) {
                    errors.push(format!("{tripwire}: {at} {role} clause {index}: {detail}"));
                }
            }
        }
    }

    let mut remainder_rows = Vec::with_capacity(module.proof_obligations.len());
    for (index, row) in module.proof_obligations.iter().enumerate() {
        let is_contract_row =
            row.source.as_ref().is_some_and(|source| source.source_id == CONTRACT_SOURCE_ID);
        if !is_contract_row {
            remainder_rows.push(row.clone());
            continue;
        }
        let mut violations: Vec<String> = Vec::new();
        if row.status != ProofStatus::Pending {
            violations.push(format!("status {} (must be pending)", row.status));
        }
        if row.source.as_ref().is_some_and(|source| source.public.is_some()) {
            violations.push("carries a public obligation identity".to_string());
        }
        let owner = row.function.and_then(|fid| {
            let mut matching = module.functions.iter().filter(|f| f.id == fid);
            match (matching.next(), matching.next()) {
                (Some(f), None) => Some(f),
                _ => None,
            }
        });
        if row.function.is_none() {
            violations.push("has no owning-function scope".to_string());
        } else if owner.is_none() {
            violations.push("its function scope does not resolve to exactly one function".into());
        }
        match &row.formula {
            None => violations.push("carries no formula".to_string()),
            Some(formula) => {
                if let Some(function) = owner {
                    let signature = module.func_type(function.ty);
                    violations.extend(clause_shape_errors(
                        function,
                        signature,
                        formula,
                        pointer_bits,
                    ));
                }
            }
        }
        let sited = row.site.is_some();
        if let (Some(site), Some(fid)) = (row.site, row.function) {
            if site.function != fid {
                violations.push("is sited in another function".to_string());
            }
        }
        let role = match (&row.kind, sited) {
            (ObligationKind::Precondition, false) => Some("requires"),
            (ObligationKind::Postcondition, false) => Some("ensures"),
            (ObligationKind::Termination, false) => Some("decreases"),
            (ObligationKind::Termination, true) | (ObligationKind::LoopInvariant, true) => None,
            (kind, sited) => {
                violations.push(format!(
                    "kind {kind:?} {} (the contract carry mints Precondition / Postcondition / \
                     function Termination unsited, LoopInvariant / loop Termination sited)",
                    if sited { "sited" } else { "unsited" }
                ));
                None
            }
        };
        if let (Some(role), Some(function), Some(formula)) = (role, owner, &row.formula) {
            let clauses = function.summary.as_ref().map(|summary| match role {
                "requires" => &summary.requires,
                "ensures" => &summary.ensures,
                _ => &summary.decreases,
            });
            if !clauses.is_some_and(|clauses| clauses.contains(formula)) {
                violations
                    .push(format!("its formula is no {role} clause of its function's summary"));
            }
        }
        if !violations.is_empty() {
            errors.push(format!(
                "{tripwire}: obligation {index} {}; every contract row must be a claim-free \
                 Pending contract-kind record (source_id {CONTRACT_SOURCE_ID:?}, function bound, \
                 formula carried)",
                violations.join(", ")
            ));
        }
    }

    // Everything else is judged by the rung below, unchanged.
    let mut remainder = module.clone();
    for function in &mut remainder.functions {
        function.summary = None;
    }
    remainder.proof_obligations = remainder_rows;
    errors.extend(crate::direct_obligations::inventory_errors_at_tier(
        &remainder,
        crate::direct_obligations::DirectObligationTier::ObligationBearingPending,
    ));
    errors
}

/// Shape rules for one carried clause formula (a summary clause or a row's).
fn clause_shape_errors(
    function: &trust_ir::Function,
    signature: Option<&trust_ir::FuncTy>,
    formula: &ProofFormula,
    pointer_bits: Option<u32>,
) -> Vec<String> {
    let mut errors = Vec::new();
    match formula.schema.as_str() {
        CONTRACT_OPAQUE_SCHEMA => {
            if !formula.bindings.is_empty() {
                errors.push("an opaque clause binds names (it must spell UNBINDABLE)".to_string());
            }
            if formula.smtlib.is_some() {
                errors.push("an opaque clause carries an SMT-LIB rendering".to_string());
            }
        }
        CONTRACT_CLAUSE_SCHEMA => {
            for (name, binding) in &formula.bindings {
                let ty = match binding.place {
                    ClausePlace::Param { index } => {
                        signature.and_then(|ft| ft.params.get(index as usize)).cloned()
                    }
                    ClausePlace::ResultSlot { index } => {
                        signature.and_then(|ft| ft.returns.get(index as usize)).cloned()
                    }
                    ClausePlace::MutParamExit { index } => {
                        match signature.and_then(|ft| ft.params.get(index as usize)) {
                            Some(Ty::RefMut(pointee) | Ty::PtrMut(pointee)) => {
                                Some((**pointee).clone())
                            }
                            _ => None,
                        }
                    }
                    ClausePlace::Value(value) => function
                        .blocks
                        .iter()
                        .flat_map(|block| block.params.iter())
                        .find(|(param, _)| *param == value)
                        .map(|(_, ty)| ty.clone()),
                    _ => None,
                };
                let Some(ty) = ty else {
                    errors.push(format!(
                        "binding {name:?} names {:?}, which is no place the contract carry binds \
                         (a parameter, the result slot, a `&mut` exit value, or a block \
                         parameter of this function)",
                        binding.place
                    ));
                    continue;
                };
                let canonical = canonical_sort(&ty, pointer_bits);
                if canonical.as_ref() != Some(&binding.sort) {
                    errors.push(format!(
                        "binding {name:?} reads {:?} (IR type {ty}) at sort {:?}; the \
                         contract-bound tier admits only the canonical sort {canonical:?} — an \
                         `Int` over a fixed-width integer is the width strip, refused",
                        binding.place, binding.sort
                    ));
                }
            }
        }
        other => errors.push(format!("schema {other:?} is not a contract-carry schema")),
    }
    errors
}

#[cfg(test)]
mod tests;

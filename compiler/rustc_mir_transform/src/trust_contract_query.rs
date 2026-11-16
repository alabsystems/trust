// ignore-tidy-file-filelength -- pre-existing size, recorded 2026-08-21; do not grow casually
//! Trust: Query provider for compiler-native Trust contracts.
//!
use std::collections::{BTreeMap, BTreeSet};

use rustc_ast::ast::{BinOpKind, LitKind, UnOp};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def::{CtorOf, DefKind, Res};
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{
    Arm, BindingMode, ByRef, Closure, ClosureKind, ContractClauseOrigin, Expr, ExprKind, HirId,
    MatchSource, Pat, PatKind, QPath,
};
use rustc_index::IndexVec;
use rustc_middle::middle::region::{Scope, ScopeData, ScopeTree};
use rustc_middle::mir::trust_contract::{
    TrustContract, TrustContractBundle, TrustContractCitation, TrustContractKind,
    TrustContractPayloadType, TrustContractPredicate, TrustContractPredicateKind,
    TrustContractProposition, TrustContractPropositionDomain, TrustContractSource,
    TrustContractSourceBinding, TrustContractSubject, TrustContractSummary,
    TrustContractVerifierSort, TrustLoopId,
};
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_middle::ty::{self, Ty, TyCtxt, TypeVisitableExt, TypeckResults};
use rustc_span::def_id::LocalDefId;
use rustc_span::{Span, Symbol};

const LOWERED_COMPILER_CONTRACT_PREFIX: &str = "__trust_lowered_compiler_contract__:";
const ENSURES_RESULT_BINDING: &str = "result";

/// Trust: B0 (design revision 2 `requires-hyps` §3.7) — did this clause's
/// refusal name a Clean island DECLARATION of this crate?
///
/// A `requires` / `invariant` / `decreases` payload is validated against the
/// CLOSED source-contract predicate vocabulary, and an island definition is not
/// in it, so `requires small(a)` is refused as `unsupported source-contract
/// call \`small\`` with no indication that `small` is a real, kernel-checked
/// definition the author can see three lines above. The author's reasonable
/// reading is "the compiler cannot see my island"; the truth is "this clause
/// ROLE has no island lane yet, while `ensures` does". Saying which one it is
/// costs nothing and changes no verdict.
///
/// The match is on the RENDERED refusal, deliberately: it fires only when the
/// validator's own message names exactly this declaration, so if that message
/// ever changes the note stops appearing rather than attaching itself to an
/// unrelated refusal. The crate HIR is consulted only once the refusal already
/// contains the marker, so an ordinary clause pays nothing.
///
/// Returns the declaration name and its Clean surface kind.
fn island_declaration_named_in_refusal(
    tcx: TyCtxt<'_>,
    reason: &str,
) -> Option<(String, rustc_ast::CleanDeclKind)> {
    const MARKER: &str = "unsupported source-contract call `";
    if !reason.contains(MARKER) {
        return None;
    }
    for item_id in tcx.hir_crate_items(()).free_items() {
        if tcx.def_kind(item_id.owner_id) != DefKind::GlobalAsm {
            continue;
        }
        let item = tcx.hir_item(item_id);
        let rustc_hir::ItemKind::CleanIsland { decls, .. } = item.kind else { continue };
        for decl in decls {
            let name = decl.name.as_str();
            if name.is_empty() {
                continue;
            }
            if reason.contains(&format!("{MARKER}{name}`")) {
                return Some((name.to_string(), decl.kind));
            }
        }
    }
    None
}

/// Trust: B0 — attach the island-aware explanation to a refused native clause.
///
/// Options follow v7/D3 (what was refused, why, what to do instead) and are the
/// ones that exist TODAY: restate the predicate in the clause grammar and derive
/// the island fact inside a Lean theorem, or keep the definition for `ensures`,
/// which does have an island lane.
fn note_island_definition_in_native_clause(
    tcx: TyCtxt<'_>,
    diag: &mut rustc_errors::Diag<'_>,
    keyword: &str,
    reason: &str,
) {
    use rustc_ast::CleanDeclKind;

    let Some((name, kind)) = island_declaration_named_in_refusal(tcx, reason) else {
        return;
    };
    match kind {
        CleanDeclKind::Def
        | CleanDeclKind::Codef
        | CleanDeclKind::Opaque
        | CleanDeclKind::Instance => {
            diag.note(format!(
                "`{name}` is a Clean island definition in this crate, not an unknown name: a \
                 `{keyword}` payload is validated against the closed source-contract predicate \
                 vocabulary, which no island definition (and no Rust function) is a member of"
            ));
            diag.note(
                "`ensures` is the one clause role with an island lane today — the kernel judges \
                 an island-calling postcondition against this function's imported defining \
                 equation — so the two sides of a signature are not governed by the same \
                 admission rule",
            );
            diag.help(format!(
                "state the predicate in the clause grammar (comparisons, `&& || !`) and derive \
                 `{name} … = true` from it inside the Lean theorem, or keep `{name}` for an \
                 `ensures` clause"
            ));
        }
        CleanDeclKind::Theorem | CleanDeclKind::Axiom => {
            diag.note(format!(
                "`{name}` is a Clean island {}, which is a PROOF, not a predicate: a clause \
                 payload names a proposition to check, never a proof of one",
                if matches!(kind, CleanDeclKind::Axiom) { "axiom" } else { "theorem" }
            ));
            diag.help(format!(
                "cite it instead — `{keyword} <predicate> by {name}` — or state the predicate in \
                 the clause grammar"
            ));
        }
        _ => {
            diag.note(format!(
                "`{name}` is a Clean island declaration of this crate, but its surface kind \
                 cannot denote a verifier predicate"
            ));
        }
    }
}

#[derive(Clone, Copy)]
struct LoweredCollectionDomain {
    element: TrustContractPropositionDomain,
    /// Exact type-level length for `[T; N]`; slices have no static upper bound.
    fixed_length: Option<u128>,
}

#[derive(Clone, Copy)]
struct AuthoredHirContractClause<'hir> {
    kind: TrustContractKind,
    clause: &'hir rustc_hir::ContractClause,
}

#[derive(Clone, Copy)]
enum ContractPayloadContext<'a> {
    Function {
        source_sorts: &'a BTreeMap<String, trust_types::Sort>,
        variable_domains: &'a [LoweredVariableDomain],
        collection_domains: &'a BTreeMap<String, LoweredCollectionDomain>,
    },
    Loop {
        source_sorts: &'a BTreeMap<String, trust_types::Sort>,
        variable_domains: &'a [LoweredVariableDomain],
        collection_domains: &'a BTreeMap<String, LoweredCollectionDomain>,
        source_bindings: &'a [LoweredSourceBinding],
        source_place_bindings: &'a [LoweredSourceBinding],
    },
}

#[derive(Debug, PartialEq, Eq)]
enum HirContractOrderError {
    TooManyClauses,
    OrdinalOutOfRange { kind: TrustContractKind, ordinal: u32, total: usize },
    DuplicateOrdinal { ordinal: u32 },
    MissingOrdinal { ordinal: usize },
}

/// Rebuild the function-wide authored clause stream from the kind-specific
/// HIR arrays. The parser ordinal is the sole authority: kind-grouped order
/// and span sorting are both unsound when clauses are interleaved or macro
/// expansion assigns equal spans.
fn restore_hir_contract_authored_order<'hir>(
    requires: &'hir [rustc_hir::ContractClause],
    ensures: &'hir [rustc_hir::ContractClause],
    decreases: &'hir [rustc_hir::ContractClause],
) -> Result<Vec<AuthoredHirContractClause<'hir>>, HirContractOrderError> {
    let total = requires
        .len()
        .checked_add(ensures.len())
        .and_then(|total| total.checked_add(decreases.len()))
        .ok_or(HirContractOrderError::TooManyClauses)?;
    let mut slots = vec![None; total];
    for (kind, clauses) in [
        (TrustContractKind::Requires, requires),
        (TrustContractKind::Ensures, ensures),
        (TrustContractKind::Decreases, decreases),
    ] {
        for clause in clauses {
            let ordinal = usize::try_from(clause.ordinal)
                .map_err(|_| HirContractOrderError::TooManyClauses)?;
            let Some(slot) = slots.get_mut(ordinal) else {
                return Err(HirContractOrderError::OrdinalOutOfRange {
                    kind,
                    ordinal: clause.ordinal,
                    total,
                });
            };
            if slot.is_some() {
                return Err(HirContractOrderError::DuplicateOrdinal { ordinal: clause.ordinal });
            }
            *slot = Some(AuthoredHirContractClause { kind, clause });
        }
    }

    slots
        .into_iter()
        .enumerate()
        .map(|(ordinal, clause)| clause.ok_or(HirContractOrderError::MissingOrdinal { ordinal }))
        .collect()
}

fn checked_contract_summary(
    requires: usize,
    ensures: usize,
    invariants: usize,
    function_decreases: usize,
    loop_decreases: usize,
    opaque: usize,
) -> Option<TrustContractSummary> {
    let requires = u32::try_from(requires).ok()?;
    let ensures = u32::try_from(ensures).ok()?;
    let invariants = u32::try_from(invariants).ok()?;
    let decreases = u32::try_from(function_decreases.checked_add(loop_decreases)?).ok()?;
    let opaque = u32::try_from(opaque).ok()?;
    let total = requires.checked_add(ensures)?.checked_add(invariants)?.checked_add(decreases)?;
    Some(TrustContractSummary {
        total,
        requires,
        ensures,
        invariants,
        decreases,
        assertions: 0,
        opaque,
    })
}

/// Query provider for `trust_contracts`.
pub(crate) fn trust_contracts<'tcx>(
    tcx: TyCtxt<'tcx>,
    local_def_id: LocalDefId,
) -> TrustContractBundle<'tcx> {
    let def_id = local_def_id.to_def_id();
    // Trust: single-sourced with the metadata encoder's pre-filter (which
    // avoids executing this query at all for contract-less defs); kept here
    // too so other callers still get a well-defined empty bundle.
    if !TrustContractBundle::def_may_have_contracts(tcx, local_def_id) {
        return TrustContractBundle::empty(def_id);
    }

    let Some(body) = tcx.hir_maybe_body_owned_by(local_def_id) else {
        return TrustContractBundle::empty(def_id);
    };
    let Some(contract) = body.contract else {
        return TrustContractBundle::empty(def_id);
    };
    // Contract/MIR lowering uses a compact generated namespace for the return
    // place, pre-state values, modeled projections, and `__` metadata. Reject
    // a legal Rust parameter that occupies that namespace before any clause is lowered:
    // otherwise two distinct source meanings can become the same Formula leaf
    // and a false relation can collapse to reflexivity. The recursive pattern
    // visitor covers destructured parameters as well as direct bindings.
    if reject_unrepresentable_contract_parameter_names(tcx, body) {
        return TrustContractBundle::empty(def_id);
    }

    let authored_clauses = match restore_hir_contract_authored_order(
        contract.requires,
        contract.ensures,
        contract.decreases,
    ) {
        Ok(clauses) => clauses,
        Err(error) => {
            let span = contract
                .requires
                .first()
                .or_else(|| contract.ensures.first())
                .or_else(|| contract.decreases.first())
                .map_or(body.value.span, |clause| clause.span);
            tcx.dcx().span_delayed_bug(
                span,
                format!(
                    "function contract has inconsistent HIR authored ordinals; refusing to \
                     guess verifier indices: {error:?}"
                ),
            );
            return TrustContractBundle::empty(def_id);
        }
    };

    let mut contracts = IndexVec::new();
    let mut opaque = 0usize;
    let typeck_results = tcx.typeck(local_def_id);
    let signature_domains = signature_variable_domains(tcx, def_id, body, typeck_results);
    let signature_projections =
        signature_projection_environment(&signature_projection_leaves(tcx, body, typeck_results));
    let function_source_sorts = function_source_sorts(tcx, body, typeck_results);
    let function_collection_domains =
        function_collection_element_domains(tcx, body, typeck_results);
    for authored_clause in authored_clauses {
        let clause = authored_clause.clause;
        let predicate = lower_predicate(
            tcx,
            local_def_id,
            typeck_results,
            &body.value,
            clause.predicate_hir_id,
            clause.span,
            clause.payload,
            authored_clause.kind,
            clause.origin,
            // The citation lane owns a cited clause end to end; the snippet
            // lane must not widen what that lane's inventory sees.
            if clause.citation.is_some() {
                ClauseCitation::Present
            } else {
                ClauseCitation::Absent
            },
            &signature_domains,
            &signature_projections,
            ContractPayloadContext::Function {
                source_sorts: &function_source_sorts,
                variable_domains: &signature_domains,
                collection_domains: &function_collection_domains,
            },
            clause.citation.is_some(),
        );
        if is_opaque_summary_predicate(&predicate.kind) {
            opaque += 1;
        }
        contracts.push(TrustContract {
            citation: clause.citation.map(contract_citation),
            kind: authored_clause.kind,
            source: contract_source(clause.origin),
            subject: TrustContractSubject::Function,
            predicate,
            span: clause.span,
            keyword_span: None,
        });
    }

    // Trust: first-class loop clauses (E4/E5). Their predicates are always
    // native verifier vocabulary; each is paired with its loop header span so
    // MIR-side consumers can attribute the clause to the right loop. They
    // live OUTSIDE the dense fn-contract index (see `TrustContractBundle`).
    let mut invariants = 0usize;
    let mut loop_decreases = 0usize;
    let mut loop_contracts = Vec::with_capacity(contract.loop_clauses.len());
    let mut source_loops = FxHashMap::default();
    for clause in contract.loop_clauses {
        let kind = match clause.kind {
            rustc_hir::LoopClauseKind::Invariant => {
                invariants += 1;
                TrustContractKind::LoopInvariant
            }
            rustc_hir::LoopClauseKind::Decreases => {
                loop_decreases += 1;
                TrustContractKind::Decreases
            }
        };
        let loop_source_sorts = visible_loop_source_sorts(
            tcx,
            local_def_id,
            body,
            typeck_results,
            clause.loop_id,
            &signature_domains,
        );
        let (
            loop_variable_domains,
            loop_collection_domains,
            loop_source_bindings,
            loop_source_place_bindings,
        ) = visible_loop_variable_domains(
            tcx,
            local_def_id,
            body,
            typeck_results,
            clause.loop_id,
            &signature_domains,
        );
        let predicate = lower_predicate(
            tcx,
            local_def_id,
            typeck_results,
            &body.value,
            None,
            clause.payload_span,
            Some(clause.payload),
            kind,
            ContractClauseOrigin::Native,
            if clause.citation.is_some() {
                ClauseCitation::Present
            } else {
                ClauseCitation::Absent
            },
            &signature_domains,
            &signature_projections,
            ContractPayloadContext::Loop {
                source_sorts: &loop_source_sorts,
                variable_domains: &loop_variable_domains,
                collection_domains: &loop_collection_domains,
                source_bindings: &loop_source_bindings,
                source_place_bindings: &loop_source_place_bindings,
            },
            clause.citation.is_some(),
        );
        if is_opaque_summary_predicate(&predicate.kind) {
            opaque += 1;
        }
        let next_loop_id = TrustLoopId {
            index: u32::try_from(source_loops.len())
                .expect("a function cannot contain more than u32::MAX source loops"),
            hir_local_id: clause.loop_id.local_id.as_u32(),
        };
        let loop_id = *source_loops.entry(clause.loop_id).or_insert(next_loop_id);
        loop_contracts.push(TrustContract {
            citation: clause.citation.map(contract_citation),
            kind,
            source: TrustContractSource::Native,
            subject: TrustContractSubject::HirLoop {
                id: loop_id,
                loop_span: clause.loop_span,
                header_span: clause.header_span,
            },
            predicate,
            span: clause.payload_span,
            keyword_span: Some(clause.keyword_span),
        });
    }

    let Some(summary) = checked_contract_summary(
        contract.requires.len(),
        contract.ensures.len(),
        invariants,
        contract.decreases.len(),
        loop_decreases,
        opaque,
    ) else {
        tcx.dcx().span_delayed_bug(
            body.value.span,
            "function contract summary exceeds its u32 metadata representation",
        );
        return TrustContractBundle::empty(def_id);
    };
    TrustContractBundle { def_id, contracts, loop_contracts, summary }
}

fn contract_citation(citation: rustc_hir::TrustCitation) -> TrustContractCitation {
    TrustContractCitation { name: citation.name, span: citation.span }
}

fn contract_source(origin: ContractClauseOrigin) -> TrustContractSource {
    match origin {
        ContractClauseOrigin::Attribute => TrustContractSource::Attribute,
        ContractClauseOrigin::Native => TrustContractSource::Native,
    }
}

fn lower_predicate<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    typeck_results: &TypeckResults<'tcx>,
    body: &'tcx Expr<'tcx>,
    predicate_hir_id: Option<HirId>,
    span: Span,
    payload: Option<Symbol>,
    contract_kind: TrustContractKind,
    origin: ContractClauseOrigin,
    citation: ClauseCitation,
    signature_domains: &[LoweredVariableDomain],
    signature_projections: &ProjectionEnvironment,
    context: ContractPayloadContext<'_>,
    // Trust: does this clause carry a `by <theorem>` citation? A cited clause
    // has been DELEGATED BY ITS AUTHOR to the two-language citation lane, where
    // a Clean theorem discharges it against the kernel. Helper-call expansion
    // must not touch one: expanding first would make the clause ordinary
    // arithmetic, hand it to the solver, and silently trade a kernel-certified
    // discharge for a `Trusted` one — an AUTHORITY downgrade, invisible in the
    // verdict count. See `expand_contract_helper_calls`.
    cited: bool,
) -> TrustContractPredicate<'tcx> {
    // First-class native clauses are verifier-language parser islands rather
    // than Rust HIR expressions. Validate the exact supported roles with their
    // exact visible domains at this earliest always-on boundary.
    let native_clause_environment = match context {
        ContractPayloadContext::Function { source_sorts, variable_domains, collection_domains }
            if origin == ContractClauseOrigin::Native
                && matches!(
                    contract_kind,
                    TrustContractKind::Requires | TrustContractKind::Decreases
                ) =>
        {
            Some((source_sorts, variable_domains, collection_domains))
        }
        ContractPayloadContext::Loop {
            source_sorts, variable_domains, collection_domains, ..
        } if origin == ContractClauseOrigin::Native
            && matches!(
                contract_kind,
                TrustContractKind::LoopInvariant | TrustContractKind::Decreases
            ) =>
        {
            Some((source_sorts, variable_domains, collection_domains))
        }
        ContractPayloadContext::Function { .. } | ContractPayloadContext::Loop { .. } => None,
    };
    // Trust (E6 — a native `requires` may PROJECT A FIELD of a parameter).
    //
    // A native function `requires` is admitted by `lower_native_clause`, which
    // types the AUTHORED text against `function_source_sorts` — bare parameter
    // bindings only. It carries no `ProjectionEnvironment`, so an authored
    // chain (`self.patch_size`, `c.patch_size`) resolves NO name there and the
    // clause is a HARD ERROR ("source-contract variable `self` is not in
    // scope"). That is what made a precondition about a struct field
    // unstatable, while the byte-identical `ensures` spelling proved: native
    // `ensures` is excluded from `native_clause_environment` above and already
    // reaches the projection-aware lane below.
    //
    // The ORDER is the soundness argument. The exact-native lane still runs
    // FIRST and still WINS whenever it can type the clause, so no clause that
    // is accepted today changes meaning or lane. Only a clause the exact-native
    // lane would otherwise REFUSE is offered to the projection lane, and that
    // lane invents nothing: `SnippetParser::parse_projection_chain` resolves
    // each chain verbatim through `ProjectionEnvironment` (built by walking the
    // real field layout of the parameter types) and returns `None` for the
    // WHOLE clause on any miss, after which
    // `native_function_clause_is_source_typed` re-types the resulting canonical
    // text against the signature domains — which include the projected leaves
    // under their exact `place_to_var_name` spelling. If it also declines, the
    // exact-native lane's ORIGINAL refusal is emitted verbatim: a refusal is
    // never downgraded to silence.
    //
    // DELIBERATELY NOT DEFERRED — each would be unsound or meaningless here:
    //   * `decreases` and loop `invariant`: the snippet lane returns their
    //     payload as an UNRESOLVED opaque string (it short-circuits before
    //     `SnippetParser` runs), so an authored chain would reach the carrier
    //     spelled in a namespace nothing downstream can bind.
    //   * a clause carrying a typed HIR predicate (`predicate_hir_id`): that
    //     branch never consults `validated_native_clause`, so deferring there
    //     would drop the diagnostic entirely.
    let mut deferred_native_refusal: Option<String> = None;
    let defer_to_projection_lane = matches!(context, ContractPayloadContext::Function { .. })
        && origin == ContractClauseOrigin::Native
        && contract_kind == TrustContractKind::Requires
        && predicate_hir_id.is_none();
    let validated_native_clause = native_clause_environment.and_then(
        |(source_sorts, variable_domains, collection_domains)| {
            match lower_native_clause(
                tcx,
                span,
                payload,
                contract_kind,
                source_sorts,
                variable_domains,
                collection_domains,
            ) {
                Ok(kind) => Some(kind),
                Err(reason) if defer_to_projection_lane => {
                    deferred_native_refusal = Some(reason);
                    None
                }
                Err(reason) => {
                    let keyword = match contract_kind {
                        TrustContractKind::Requires => "requires",
                        TrustContractKind::Decreases => "decreases",
                        _ => "invariant",
                    };
                    // Trust: B0 — the headline is unchanged; when the refused
                    // call names a Clean island declaration of this crate, the
                    // notes say which lane is missing rather than leaving the
                    // author to read it as "the compiler cannot see my island".
                    let mut diag = tcx
                        .dcx()
                        .struct_span_err(span, format!("invalid `{keyword}` clause: {reason}"));
                    note_island_definition_in_native_clause(tcx, &mut diag, keyword, &reason);
                    diag.emit();
                    Some(TrustContractPredicateKind::Unsupported {
                        reason: Symbol::intern(&reason),
                    })
                }
            }
        },
    );

    let kind = if let Some(predicate_hir_id) = predicate_hir_id {
        // Typed clauses carry an exact identity from AST -> HIR lowering.
        // Spans are diagnostic only: distinct macro-expanded predicates may
        // have source-equal spans, and choosing the first matching expression
        // can silently bind one authored ordinal to another clause's formula.
        let exact_expr = if origin != ContractClauseOrigin::Attribute {
            tcx.dcx().span_delayed_bug(
                span,
                format!(
                    "non-attribute contract unexpectedly carried typed HIR predicate \
                     {predicate_hir_id:?}"
                ),
            );
            None
        } else if predicate_hir_id.owner == body.hir_id.owner {
            match tcx.hir_node(predicate_hir_id) {
                rustc_hir::Node::Expr(expr) => Some(expr),
                node => {
                    tcx.dcx().span_delayed_bug(
                        span,
                        format!(
                            "typed contract predicate {predicate_hir_id:?} resolved to non-expression \
                             HIR node {node:?}"
                        ),
                    );
                    None
                }
            }
        } else {
            tcx.dcx().span_delayed_bug(
                span,
                format!(
                    "typed contract predicate {predicate_hir_id:?} is owned by a different body \
                     than contract body {:?}",
                    body.hir_id.owner,
                ),
            );
            None
        };
        if crate::trust_verify::trust_env_var_present("TRUST_CONTRACT_INLINE_TRACE") {
            eprintln!(
                "TRUST_CONTRACT_INLINE_TRACE: path=exact-HIR present={}",
                exact_expr.is_some()
            );
        }
        exact_expr
            .and_then(|expr| lower_expr(tcx, typeck_results, expr, contract_kind))
            .unwrap_or_else(|| TrustContractPredicateKind::Unsupported {
                reason: unsupported_predicate_reason(tcx, span),
            })
    } else {
        // Opaque attributes and native clauses deliberately have no Rust
        // expression identity. A successfully validated native parser-island
        // payload wins; every other span-only clause stays in the
        // origin-exact snippet lane.
        if crate::trust_verify::trust_env_var_present("TRUST_CONTRACT_INLINE_TRACE") {
            eprintln!("TRUST_CONTRACT_INLINE_TRACE: path=snippet (no HIR expression identity)");
        }
        let mut projection_refusal = None;
        // A pending exact-native refusal means this call is the SECOND opinion
        // on an already-refused clause, and that lane's reason is the one the
        // author sees.
        let is_primary_lane = deferred_native_refusal.is_none();
        let lowered = validated_native_clause.or_else(|| {
            lower_contract_snippet(
                tcx,
                owner,
                span,
                payload,
                contract_kind,
                origin,
                citation,
                signature_domains,
                signature_projections,
                cited,
                &mut projection_refusal,
                is_primary_lane,
            )
        });
        // Trust (2026-10-03): a native `ensures` is typed by the snippet lane, which
        // refuses every method call, so `ensures result <= xs.len()` over a slice
        // parameter was always unsupported while the same `xs.len()` types in a
        // `requires`. Offer a clause the snippet lane REFUSED to the exact-native
        // lane, with the function's output sort added as `_0` (the binding `result`
        // denotes; its domain is the signature's `_0`). Only a fully typed proposition is kept, and every
        // clause the snippet lane accepts keeps its lane and meaning.
        let lowered = lowered.or_else(|| match context {
            ContractPayloadContext::Function {
                source_sorts,
                variable_domains,
                collection_domains,
            } if origin == ContractClauseOrigin::Native
                && contract_kind == TrustContractKind::Ensures
                && deferred_native_refusal.is_none() =>
            {
                let output =
                    tcx.fn_sig(owner.to_def_id()).instantiate_identity().skip_binder().output();
                // The return sort travels as `_0`, the key
                // `validate_source_spec_expr` reads `result`'s sort from.
                let (_, result_sort) =
                    loop_source_binding_from_ty(tcx, "result".to_string(), output)?;
                if source_sorts.contains_key("_0") {
                    return None;
                }
                let mut sorts = source_sorts.clone();
                sorts.insert("_0".to_string(), result_sort);
                lower_native_clause(
                    tcx,
                    span,
                    payload,
                    contract_kind,
                    &sorts,
                    variable_domains,
                    collection_domains,
                )
                .ok()
                .filter(|kind| matches!(kind, TrustContractPredicateKind::Typed { .. }))
            }
            ContractPayloadContext::Function { .. } | ContractPayloadContext::Loop { .. } => None,
        });
        match (lowered, deferred_native_refusal) {
            // Either the exact-native lane admitted it, or the projection lane
            // rescued a clause the exact-native lane could not name. In the
            // second case the projection lane bound every leaf to an exact
            // field of an exact parameter layout, so the deferred refusal is
            // discharged rather than suppressed.
            (Some(kind), _) => kind,
            // Both lanes declined. The exact-native lane's own reason is the
            // authored-language one, so it is what the author sees — byte for
            // byte the diagnostic this clause got before the projection lane
            // existed.
            (None, Some(reason)) => {
                let mut diag =
                    tcx.dcx().struct_span_err(span, format!("invalid `requires` clause: {reason}"));
                // The refusal above names the chain's HEAD (`self`, `c`) as
                // out of scope, because that head is not itself a scalar
                // binding. When the projection lane declined a specific chain,
                // say so: the head IS a parameter and the author needs to know
                // it is the FIELD PATH that has no exact place, not the name.
                if let Some(chain) = projection_refusal {
                    diag.note(format!(
                        "the field projection `{chain}` has no exact scalar place here"
                    ));
                    diag.help(
                        "a projection is admitted only when every segment is a field of a \
                         single-variant struct or a tuple with a known layout, and the leaf is a \
                         scalar (bool or a primitive integer); enums, unions, generic types, \
                         reference-typed fields below the head, and method calls are refused",
                    );
                }
                // Trust: B0 — see `note_island_definition_in_native_clause`.
                // This is the lane a native function `requires` actually takes,
                // so an island-calling precondition is refused here.
                note_island_definition_in_native_clause(tcx, &mut diag, "requires", &reason);
                diag.emit();
                TrustContractPredicateKind::Unsupported { reason: Symbol::intern(&reason) }
            }
            (None, None) => TrustContractPredicateKind::Unsupported {
                reason: unsupported_predicate_reason(tcx, span),
            },
        }
    };

    // Native clauses are verifier-language parser islands, not HIR
    // expressions. Preserve that boundary in the query schema instead of
    // stamping every payload `bool` (which is especially false for an E5
    // integer measure).
    let ty = match origin {
        ContractClauseOrigin::Attribute => TrustContractPayloadType::Rust(tcx.types.bool),
        ContractClauseOrigin::Native => {
            TrustContractPayloadType::Verifier(if contract_kind == TrustContractKind::Decreases {
                TrustContractVerifierSort::Int
            } else {
                TrustContractVerifierSort::Bool
            })
        }
    };
    let source_bindings = match context {
        ContractPayloadContext::Loop { source_bindings, .. }
            if origin == ContractClauseOrigin::Native =>
        {
            exact_predicate_source_bindings(&kind, source_bindings)
        }
        ContractPayloadContext::Function { .. } | ContractPayloadContext::Loop { .. } => Vec::new(),
    };
    let source_place_bindings = match context {
        ContractPayloadContext::Loop { source_place_bindings, .. }
            if origin == ContractClauseOrigin::Native =>
        {
            exact_predicate_source_place_bindings(&kind, source_place_bindings)
        }
        ContractPayloadContext::Function { .. } | ContractPayloadContext::Loop { .. } => None,
    };
    TrustContractPredicate { ty, kind, source_bindings, source_place_bindings }
}

/// Parse and type-check a supported first-class native clause at the earliest
/// always-on compiler boundary. Native clauses are not Rust HIR expressions,
/// so this uses the verifier-language elaborator and exact visible source domains.
/// When the complete expression fits the closed query vocabulary, successful
/// validation also carries a structural proposition with exact free-variable
/// domains. The authored spelling remains diagnostics, never proof authority.
fn lower_native_clause(
    tcx: TyCtxt<'_>,
    span: Span,
    payload: Option<Symbol>,
    contract_kind: TrustContractKind,
    source_sorts: &BTreeMap<String, trust_types::Sort>,
    visible_domains: &[LoweredVariableDomain],
    collection_domains: &BTreeMap<String, LoweredCollectionDomain>,
) -> Result<TrustContractPredicateKind, String> {
    let snippet;
    let payload_text = native_clause_payload_text(span, payload);
    let body = match &payload_text {
        // An expansion span cannot faithfully recover the authored payload (a
        // proc macro may stamp every emitted token with one call-site span,
        // and macro_rules substitution mixes definition- and call-site
        // spans), so the parser's token-rendered spelling is the authority
        // there. Authored source keeps the byte-exact snippet lane.
        Some(payload) => payload.as_str(),
        None => {
            snippet = tcx
                .sess
                .source_map()
                .span_to_snippet(span)
                .map_err(|_| "source text is unavailable".to_string())?;
            contract_body_from_clause_snippet(&snippet, contract_kind)
                .ok_or_else(|| "the clause body could not be recovered".to_string())?
        }
    };
    let body = validate_native_clause_body(body, contract_kind, source_sorts)?;
    // Every supported native role has already passed exact high-level source
    // validation above. When its lowered Formula fits the query vocabulary,
    // retain that structural tree instead of forcing E4/E5 or a function
    // measure back through an opaque string. In particular, `xs.len()` lowers
    // to `xs__len`; `native_clause_variable_domains` supplies the exact
    // pointer-sized domain while visible loop locals retain their HIR-derived
    // primitive widths and signedness.
    if let Some(predicate) = typed_native_clause_with_collection_domains(
        &body,
        contract_kind,
        source_sorts,
        visible_domains,
        collection_domains,
        u32::try_from(tcx.data_layout.pointer_size().bits()).ok(),
    ) {
        return Ok(predicate);
    }
    Ok(TrustContractPredicateKind::Opaque { text: Symbol::intern(&body) })
}

#[cfg(test)]
fn typed_native_clause(
    body: &str,
    contract_kind: TrustContractKind,
    source_sorts: &BTreeMap<String, trust_types::Sort>,
    visible_domains: &[LoweredVariableDomain],
    pointer_width: Option<u32>,
) -> Option<TrustContractPredicateKind> {
    typed_native_clause_with_collection_domains(
        body,
        contract_kind,
        source_sorts,
        visible_domains,
        &BTreeMap::new(),
        pointer_width,
    )
}

fn typed_native_clause_with_collection_domains(
    body: &str,
    contract_kind: TrustContractKind,
    source_sorts: &BTreeMap<String, trust_types::Sort>,
    visible_domains: &[LoweredVariableDomain],
    collection_domains: &BTreeMap<String, LoweredCollectionDomain>,
    pointer_width: Option<u32>,
) -> Option<TrustContractPredicateKind> {
    let expected_class = if contract_kind == TrustContractKind::Decreases {
        PropositionClass::Numeric
    } else {
        PropositionClass::Bool
    };
    let formula = trust_types::parse_spec_expr(body)?;
    let formula = reconcile_float_literal_formats(formula, source_sorts);
    let variable_domains = native_clause_variable_domains(
        &formula,
        source_sorts,
        visible_domains,
        collection_domains,
        pointer_width,
    )?;
    match lowered_contract_text_with_domains_for_class(
        body.to_string(),
        &variable_domains,
        expected_class,
    ) {
        typed @ TrustContractPredicateKind::Typed { .. } => Some(typed),
        _ => None,
    }
}

#[cfg(test)]
fn typed_native_function_requires(
    body: &str,
    source_sorts: &BTreeMap<String, trust_types::Sort>,
    signature_domains: &[LoweredVariableDomain],
    collection_domains: &BTreeMap<String, LoweredCollectionDomain>,
    pointer_width: Option<u32>,
) -> Option<TrustContractPredicateKind> {
    typed_native_clause_with_collection_domains(
        body,
        TrustContractKind::Requires,
        source_sorts,
        signature_domains,
        collection_domains,
        pointer_width,
    )
}

/// Extend scalar signature domains with exact synthetic projection domains
/// introduced by native source lowering. This is deliberately a closed lane:
/// collection `.len()` and one canonical literal index are representable in the
/// query proposition vocabulary. Only an exact, unshadowed visible collection
/// descriptor authorizes either synthetic leaf, and a fixed-array literal must
/// be in range. Unknown projections return None and keep the clause Opaque.
// `Formula::free_variables` is a set, but its iteration order cannot affect
// this query: the names are sorted immediately before any domain decision or
// output is made.
#[allow(rustc::potential_query_instability)]
fn native_clause_variable_domains(
    formula: &trust_types::Formula,
    source_sorts: &BTreeMap<String, trust_types::Sort>,
    signature_domains: &[LoweredVariableDomain],
    collection_domains: &BTreeMap<String, LoweredCollectionDomain>,
    pointer_width: Option<u32>,
) -> Option<Vec<LoweredVariableDomain>> {
    let mut free_variables: Vec<_> = formula.free_variables().into_iter().collect();
    free_variables.sort();
    let mut domains: Vec<_> = signature_domains
        .iter()
        .filter(|variable| free_variables.binary_search(&variable.name).is_ok())
        .cloned()
        .collect();
    for name in free_variables {
        if domains.iter().any(|variable| variable.name == name) {
            // A signature domain owns this leaf. The parser mints projection
            // leaves inside the reserved `__` family (`xs.len()` -> `xs__len`),
            // and the parameter gate rejects `__` binding spellings, so a
            // scalar parameter such as `xs_len` can no longer collapse onto a
            // projection leaf and needs no ambiguity refusal here.
            continue;
        }
        if let Some(base) = name.strip_suffix("__len") {
            if !matches!(source_sorts.get(base), Some(trust_types::Sort::Array(..))) {
                return None;
            }
            // A source sort proves only that some visible HIR binding with
            // this spelling is a collection. The descriptor is minted only
            // for an exact unshadowed HIR binding whose identity is carried
            // separately to downstream MIR reconstruction.
            collection_domains.get(base)?;
            domains.push(LoweredVariableDomain {
                name,
                domain: TrustContractPropositionDomain::PointerSizedInt {
                    width: pointer_width?,
                    signed: false,
                },
            });
            continue;
        }

        let (base, index) = canonical_literal_collection_projection(&name)?;
        let trust_types::Sort::Array(index_sort, element_sort) = source_sorts.get(base)? else {
            return None;
        };
        if index_sort.as_ref() != &trust_types::Sort::Int {
            return None;
        }
        let collection = *collection_domains.get(base)?;
        if collection.fixed_length.is_some_and(|length| index >= length) {
            return None;
        }
        let domain = collection.element;
        let domain_sort = match domain {
            TrustContractPropositionDomain::Bool => trust_types::Sort::Bool,
            // A float's sort is its BIT VECTOR, the same spelling
            // `sort_for_ty` gives a float place in the body. `FpFromBits` lifts
            // it where IEEE semantics are needed, so the variable itself must
            // stay at the bit width or the clause names a different symbol.
            TrustContractPropositionDomain::Float { width } => trust_types::Sort::BitVec(width),
            TrustContractPropositionDomain::MathematicalInt
            | TrustContractPropositionDomain::PointerSizedInt { .. }
            | TrustContractPropositionDomain::MachineInt { .. } => trust_types::Sort::Int,
        };
        if element_sort.as_ref() != &domain_sort {
            return None;
        }
        domains.push(LoweredVariableDomain { name, domain });
    }
    canonical_variable_domains(domains)
}

/// Recover the base and index of exactly one canonical nonnegative literal
/// collection projection (`xs[0]`). Source validation proves the visible base
/// has Array sort; the exact-binding descriptor checked by the caller supplies
/// source identity, exact element domain, and any fixed-array bound. Keeping
/// those authorities separate prevents an arbitrary parser variable or a
/// shadowing local from borrowing another collection's identity.
fn canonical_literal_collection_projection(name: &str) -> Option<(&str, u128)> {
    let without_close = name.strip_suffix(']')?;
    let (base, index) = without_close.rsplit_once('[')?;
    if base.is_empty()
        || base.contains(['[', ']'])
        || index.is_empty()
        || !index.bytes().all(|byte| byte.is_ascii_digit())
    {
        return None;
    }
    let parsed = index.parse::<u128>().ok()?;
    (parsed.to_string() == index).then_some((base, parsed))
}

#[cfg(test)]
fn validate_native_function_decreases_body(
    body: &str,
    signature_domains: &[LoweredVariableDomain],
) -> Result<String, String> {
    validate_native_clause_body(
        body,
        TrustContractKind::Decreases,
        &signature_input_source_sorts(signature_domains),
    )
}

fn signature_source_sorts(
    signature_domains: &[LoweredVariableDomain],
) -> BTreeMap<String, trust_types::Sort> {
    let mut signature_sorts = BTreeMap::new();
    for variable in signature_domains {
        let sort = match variable.domain {
            TrustContractPropositionDomain::Bool => trust_types::Sort::Bool,
            // See the collection-element arm above: the bit width, not
            // `Sort::Float`, because that is how the body spells the place.
            TrustContractPropositionDomain::Float { width } => trust_types::Sort::BitVec(width),
            TrustContractPropositionDomain::MathematicalInt
            | TrustContractPropositionDomain::PointerSizedInt { .. }
            | TrustContractPropositionDomain::MachineInt { .. } => trust_types::Sort::Int,
        };
        // `signature_variable_domains` is already canonicalized and returns an
        // empty set on ambiguity. Keep this helper total for the query path;
        // tests that construct duplicate synthetic rows retain the last sort,
        // and the source validator still fails any mismatched use closed.
        signature_sorts.insert(variable.name.clone(), sort);
    }
    signature_sorts
}

/// Source sorts for clauses evaluated before a function result exists.
///
/// `signature_variable_domains` includes MIR's synthetic `_0` row so an
/// `ensures result ...` clause can be typed. Loop invariants and decreases
/// clauses must not treat that internal row as a visible Rust binding (or reject
/// every scalar-returning function as though it declared a parameter `_0`).
fn signature_input_source_sorts(
    signature_domains: &[LoweredVariableDomain],
) -> BTreeMap<String, trust_types::Sort> {
    signature_source_sorts(signature_domains).into_iter().filter(|(name, _)| name != "_0").collect()
}

fn validate_native_clause_body(
    body: &str,
    contract_kind: TrustContractKind,
    source_sorts: &BTreeMap<String, trust_types::Sort>,
) -> Result<String, String> {
    // `_0` in an `ensures` environment is the return sort the caller inserted (a
    // parameter spelled `_0` is rejected before any clause is lowered).
    if let Some(name) = source_sorts.keys().find(|name| {
        trust_types::source_contract_synthetic_name_collision(name).is_some()
            && !(contract_kind == TrustContractKind::Ensures && name.as_str() == "_0")
    }) {
        return Err(format!(
            "visible binding `{name}` collides with the synthetic contract-variable namespace"
        ));
    }
    let clause = match contract_kind {
        TrustContractKind::Requires => trust_types::SourceContractClause::Requires,
        TrustContractKind::Ensures => trust_types::SourceContractClause::Ensures,
        TrustContractKind::LoopInvariant => trust_types::SourceContractClause::Invariant,
        TrustContractKind::Decreases => trust_types::SourceContractClause::Decreases,
        _ => return Err("unsupported native clause role".to_string()),
    };
    let validated =
        trust_types::validate_source_spec_expr_with_exact_projections(body, clause, source_sorts)
            .map_err(|error| error.to_string())?;
    // Exact source validation is the source-language admission authority.
    // It parses the complete high-level expression, resolves every source name
    // (including dereferences and quantifier binders), recursively checks
    // operand sorts, and enforces the clause's top-level sort. Do not repeat
    // scope checking after lowering: projections such as `xs.len()` deliberately
    // become synthetic solver leaves such as `xs__len`, which are not source
    // bindings and would be rejected spuriously here.
    Ok(validated)
}

/// Reject Rust parameter spellings that contract lowering cannot represent
/// injectively.
///
/// This is deliberately a query-level admission gate rather than a verifier
/// diagnostic sweep: every consumer of `trust_contracts` then receives either
/// an injectively named bundle or an empty bundle accompanied by a hard compiler
/// error. Besides the generated namespace, Rust hygiene permits two distinct
/// parameter HIR identities with one displayed name. Native proposition
/// payloads retain only that displayed name, so such a function must fail
/// before function-level clauses, monitors, or loop clauses can select either
/// binding. Quantifier binders are guarded by the shared `trust-types` parser
/// rule, and loop-local bindings are guarded by `validate_native_clause_body`
/// using the exact visible environment.
/// Trust (review round 41, 2026-10-02): whether `span` carries a LOCAL hygiene
/// mark (opaque `def_site`, or `macro_rules` semi-transparent). Source-contract propositions are plain
/// text matched by name, which is faithful for transparent and `macro_rules`
/// (semi-transparent) spans but not for def-site hygiene: a `pub macro` emitting
/// `fn f(lim: u8) .. invariant $inv` bound the CALL-site clause `lim <= 127` (a
/// static of 200) to the DEF-site parameter, and a def-site block `const lim` was
/// replaced by a call-site `let lim` the macro's own clause cannot see. Both were
/// proved and kernel-certified.
///
/// Review round 42 widened it to `macro_rules` LOCAL hygiene (semi-transparent
/// marks): a macro's own `let lim = 200` was recorded as an unsupported shadow, a
/// narrower call-site `let lim` pasted into the macro replaced it, and the macro's
/// clause was proved about the call-site value. Only transparent marks (a proc
/// macro's `Span::call_site()`) resolve exactly like unexpanded code.
fn has_local_hygiene(span: rustc_span::Span) -> bool {
    !span.normalize_to_macro_rules().ctxt().is_root()
}

fn reject_unrepresentable_contract_parameter_names<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &'tcx rustc_hir::Body<'tcx>,
) -> bool {
    struct Collector<'tcx> {
        tcx: TyCtxt<'tcx>,
        rejected: bool,
        parameter_ids: BTreeMap<String, u32>,
        ambiguous_names: BTreeSet<String>,
        // Review rounds 41-42: the `macro_rules`-normalized syntax context of every
        // clause payload. A parameter is bindable by displayed name only when it
        // shares that context: a def-site parameter does not see a call-site
        // clause's `lim` (a static), nor does a call-site parameter see a clause
        // written inside the macro.
        clause_ctxts: Vec<rustc_span::SyntaxContext>,
    }

    impl<'tcx> Visitor<'tcx> for Collector<'tcx> {
        fn visit_pat(&mut self, pat: &'tcx Pat<'tcx>) {
            if let PatKind::Binding(_, canonical_id, ident, _) = pat.kind
                && canonical_id == pat.hir_id
            {
                let name = ident.name.to_string();
                let id = canonical_id.local_id.as_u32();
                // A clause span need not carry its PAYLOAD's context (a native
                // clause's span can start at a macro-written keyword while the
                // payload is a call-site `$post` fragment, measured on round 41's
                // h4), so a macro-local parameter is refused outright; the context
                // comparison additionally refuses a call-site parameter under a
                // clause written inside a macro.
                let param_ctxt = ident.span.normalize_to_macro_rules().ctxt();
                if has_local_hygiene(ident.span)
                    || self.clause_ctxts.iter().any(|clause_ctxt| *clause_ctxt != param_ctxt)
                {
                    self.tcx.dcx().span_err(
                        pat.span,
                        format!(
                            "parameter `{name}` and a contract clause of this function have \
                             different macro hygiene; source-contract propositions are matched \
                             by displayed name and cannot respect it"
                        ),
                    );
                    self.rejected = true;
                }
                if let Some(previous_id) = self.parameter_ids.get(&name).copied()
                    && previous_id != id
                    && self.ambiguous_names.insert(name.clone())
                {
                    self.tcx.dcx().span_err(
                        pat.span,
                        format!(
                            "parameters named `{name}` have distinct hygienic identities; \
                             source-contract propositions cannot select one by displayed name"
                        ),
                    );
                    self.rejected = true;
                } else {
                    self.parameter_ids.entry(name.clone()).or_insert(id);
                }

                if let Some(collision) =
                    trust_types::source_contract_synthetic_name_collision(&name)
                {
                    let message = match collision {
                        trust_types::SourceContractSyntheticNameCollision::ReturnPlace => format!(
                            "parameter `{name}` collides with the source-contract return-place vocabulary"
                        ),
                        trust_types::SourceContractSyntheticNameCollision::OldValue => format!(
                            "parameter `{name}` collides with the source-contract synthetic pre-state namespace"
                        ),
                        trust_types::SourceContractSyntheticNameCollision::PositionalPlace => {
                            format!(
                                "parameter `{name}` collides with the source-contract positional MIR-place namespace"
                            )
                        }
                        trust_types::SourceContractSyntheticNameCollision::PredicateSymbol => {
                            format!(
                                "parameter `{name}` collides with the source-contract predicate-symbol namespace"
                            )
                        }
                        trust_types::SourceContractSyntheticNameCollision::GeneratedMetadata => {
                            format!(
                                "parameter `{name}` collides with Trust's generated Formula metadata namespace"
                            )
                        }
                    };
                    self.tcx.dcx().span_err(pat.span, message);
                    self.rejected = true;
                }
            }
            intravisit::walk_pat(self, pat);
        }
    }

    let clause_ctxts = body
        .contract
        .map(|contract| {
            contract
                .requires
                .iter()
                .chain(contract.ensures)
                .chain(contract.decreases)
                .map(|clause| clause.span)
                .chain(contract.loop_clauses.iter().map(|clause| clause.payload_span))
                .map(|span| span.normalize_to_macro_rules().ctxt())
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    let mut collector = Collector {
        tcx,
        rejected: false,
        parameter_ids: BTreeMap::new(),
        ambiguous_names: BTreeSet::new(),
        clause_ctxts,
    };
    for param in body.params {
        collector.visit_pat(param.pat);
    }
    collector.rejected
}

/// Every source binding introduced by the function signature, including
/// bindings whose type is outside the scalar proposition vocabulary. The
/// native contract surface is text, so a bare `f(...)` cannot be resolved as a
/// module function when a parameter named `f` would win ordinary Rust name
/// resolution (notably a function-pointer parameter).
fn contract_parameter_binding_names(tcx: TyCtxt<'_>, owner: LocalDefId) -> BTreeSet<String> {
    struct Collector {
        names: BTreeSet<String>,
    }

    impl<'tcx> Visitor<'tcx> for Collector {
        fn visit_pat(&mut self, pat: &'tcx Pat<'tcx>) {
            if let PatKind::Binding(_, canonical_id, ident, _) = pat.kind
                && canonical_id == pat.hir_id
            {
                self.names.insert(ident.name.to_string());
            }
            intravisit::walk_pat(self, pat);
        }
    }

    let Some(body) = tcx.hir_maybe_body_owned_by(owner) else {
        return BTreeSet::new();
    };
    let mut collector = Collector { names: BTreeSet::new() };
    for param in body.params {
        collector.visit_pat(param.pat);
    }
    collector.names
}

fn lower_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    typeck_results: &TypeckResults<'tcx>,
    expr: &'tcx Expr<'tcx>,
    contract_kind: TrustContractKind,
) -> Option<TrustContractPredicateKind> {
    if contract_kind == TrustContractKind::Requires
        && let ExprKind::Closure(closure) = &transparent_contract_expr(expr).kind
    {
        // `#[requires(predicate)]` is represented in HIR as a compiler-built
        // zero-argument closure whose body is the authored predicate. With an
        // exact AST -> HIR identity we intentionally land on that closure;
        // lower its body with the closure's own typeck results instead of
        // searching the enclosing function for a source-equal inner span.
        return lower_requires_closure(tcx, closure);
    }
    if contract_kind == TrustContractKind::Ensures {
        // An ensures clause may use a block to capture pre-state locals before
        // returning its checker closure. Follow only the expression's semantic
        // value/tail; a top-down visitor could select an unrelated closure in a
        // preceding statement and bind the wrong postcondition.
        if let Some(closure) = ensures_value_closure(expr) {
            return lower_ensures_closure(tcx, closure);
        }
    }

    let lowerer = ExprLowerer {
        tcx,
        typeck_results,
        result_binding: None,
        pat_bindings: Vec::new(),
        inline_depth: 0,
    };
    lowerer.lower_predicate(expr)
}

fn transparent_contract_expr<'tcx>(mut expr: &'tcx Expr<'tcx>) -> &'tcx Expr<'tcx> {
    loop {
        match &expr.kind {
            ExprKind::Type(inner, _) | ExprKind::DropTemps(inner) | ExprKind::Use(inner, _) => {
                expr = inner;
            }
            _ => return expr,
        }
    }
}

fn lower_requires_closure<'tcx>(
    tcx: TyCtxt<'tcx>,
    closure: &'tcx Closure<'tcx>,
) -> Option<TrustContractPredicateKind> {
    if closure.kind != ClosureKind::Closure {
        return None;
    }
    let body = tcx.hir_body(closure.body);
    if !body.params.is_empty() {
        return None;
    }
    let typeck_results = tcx.typeck_body(closure.body);
    let lowerer = ExprLowerer {
        tcx,
        typeck_results,
        result_binding: None,
        pat_bindings: Vec::new(),
        inline_depth: 0,
    };
    lowerer.lower_predicate(&body.value)
}

fn ensures_value_closure<'tcx>(expr: &'tcx Expr<'tcx>) -> Option<&'tcx Closure<'tcx>> {
    let expr = transparent_contract_expr(expr);
    match &expr.kind {
        ExprKind::Closure(closure) => Some(closure),
        ExprKind::Block(block, _) => block.expr.and_then(ensures_value_closure),
        _ => None,
    }
}

fn lower_ensures_closure<'tcx>(
    tcx: TyCtxt<'tcx>,
    closure: &'tcx Closure<'tcx>,
) -> Option<TrustContractPredicateKind> {
    if closure.kind != ClosureKind::Closure {
        return None;
    }

    let body = tcx.hir_body(closure.body);
    let [param] = body.params else {
        return None;
    };
    let PatKind::Binding(_, result_binding, _, None) = param.pat.kind else {
        return None;
    };

    let typeck_results = tcx.typeck_body(closure.body);
    let lowerer = ExprLowerer {
        tcx,
        typeck_results,
        result_binding: Some(result_binding),
        pat_bindings: Vec::new(),
        inline_depth: 0,
    };
    lowerer.lower_predicate(&body.value)
}

/// The token-rendered payload spelling, exactly when it must be the text
/// authority: only native verifier-language clauses carry one, and only an
/// expansion span makes `span_to_snippet` unable to recover the authored
/// payload. Ordinary authored source returns `None` and keeps the byte-exact
/// snippet lane, so non-macro obligation spellings are unchanged.
fn native_clause_payload_text(span: Span, payload: Option<Symbol>) -> Option<Symbol> {
    payload.filter(|_| span.from_expansion())
}

fn lower_contract_snippet(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    span: Span,
    payload: Option<Symbol>,
    contract_kind: TrustContractKind,
    origin: ContractClauseOrigin,
    citation: ClauseCitation,
    signature_domains: &[LoweredVariableDomain],
    signature_projections: &ProjectionEnvironment,
    cited: bool,
    // Attribution channel for the FIRST projection chain this lane could not
    // resolve. The caller owns the diagnostic because only it knows whether
    // another lane already accepted the clause.
    projection_refusal: &mut Option<String>,
    // Whether this lane is the PRIMARY authority for this clause.
    //
    // `false` when it is running as the SECOND opinion on a native `requires`
    // the exact-native lane already refused, which changes two things:
    //
    //   * it emits no refusal diagnostic of its own. The exact-native lane's
    //     reason is precise, authored-language, and already on its way to the
    //     author; a second attribution for the same clause would report one
    //     defect twice and name a different token as the fault.
    //   * transparent-helper expansion is OFF. The second opinion exists to
    //     resolve FIELD PROJECTIONS, which the exact-native lane cannot name.
    //     Expanding a helper call there would additionally make
    //     `requires helper(x) > 0` — a hard error today — start compiling, an
    //     unrelated and unmeasured capability change riding in on this one.
    is_primary_lane: bool,
) -> Option<TrustContractPredicateKind> {
    let snippet;
    let payload_text = native_clause_payload_text(span, payload);
    let body = match &payload_text {
        // See `lower_native_clause`: under expansion the parser's
        // token-rendered payload is the sole faithful spelling.
        Some(payload) => payload.as_str(),
        None => {
            snippet = tcx.sess.source_map().span_to_snippet(span).ok()?;
            contract_body_from_clause_snippet(&snippet, contract_kind)?
        }
    };
    // Trust: rewrite calls to transparent helpers into their own bodies BEFORE
    // the text parser sees them (see `expand_contract_helper_calls`). A snippet
    // with no expandable call is returned unchanged, so this is inert for every
    // clause that does not name one.
    // A CITED clause belongs to the two-language citation lane; expanding it
    // here would reroute it to the solver and silently downgrade its authority.
    let expanded = if cited || !is_primary_lane {
        body.to_string()
    } else {
        let shadowed_names = contract_parameter_binding_names(tcx, owner);
        expand_contract_helper_calls(tcx, owner, body, 0, signature_domains, &shadowed_names)
    };
    let mut literal_refusal = None;
    let lowered = lower_contract_snippet_body_with_domains(
        &expanded,
        contract_kind,
        origin,
        citation,
        signature_domains,
        signature_projections,
        &mut literal_refusal,
        projection_refusal,
    );
    // A clause refused BECAUSE OF a literal is the one refusal this lane can
    // attribute exactly, so it is the one that must never be silent. Everything
    // else still returns `None` and becomes `Unsupported` as before: naming a
    // cause we do not have would be worse than naming none.
    if is_primary_lane
        && lowered.is_none()
        && let Some(refusal) = literal_refusal
    {
        emit_contract_literal_refusal(tcx, span, contract_kind, &refusal);
    }
    lowered
}

/// Report an integer literal that a contract predicate cannot carry.
///
/// This exists because the failure it describes used to be INVISIBLE. The
/// clause was accepted by the parser that admits clauses, refused by the parser
/// that reads them, and the only trace was an UNKNOWN row whose message named
/// the whole predicate and no part of it — so a nine-digit bound written the way
/// every Rust style guide writes one silently stopped being proved. A refusal
/// carries the fix, with options (standing ruling v7/D3).
fn emit_contract_literal_refusal(
    tcx: TyCtxt<'_>,
    span: Span,
    contract_kind: TrustContractKind,
    refusal: &trust_types::int_literal::IntLiteralRefusal,
) {
    // Named, not spelled with a wildcard: the keyword is what tells the author
    // WHICH clause on the signature to go and edit, and a `_ => "invariant"`
    // arm would quietly mislabel every future clause kind.
    let keyword = match contract_kind {
        TrustContractKind::Requires => "requires",
        TrustContractKind::Ensures => "ensures",
        TrustContractKind::Decreases => "decreases",
        TrustContractKind::Invariant | TrustContractKind::LoopInvariant => "invariant",
        TrustContractKind::Assumes => "assumes",
        TrustContractKind::Asserts => "asserts",
        TrustContractKind::Refinement => "refinement",
        TrustContractKind::Temporal => "temporal",
    };
    tcx.dcx()
        .struct_span_err(
            span,
            format!(
                "unsupported numeric literal `{}` in this `{keyword}` clause: {}",
                refusal.literal, refusal.reason,
            ),
        )
        .with_help(refusal.fix.clone())
        .with_note(
            "the whole clause is refused fail-closed, so nothing in it is proved; without this \
             message the only symptom would be an UNKNOWN row naming the entire predicate",
        )
        .emit();
}

fn contract_body_from_clause_snippet(
    snippet: &str,
    contract_kind: TrustContractKind,
) -> Option<&str> {
    let mut body = snippet.trim();

    if let Some(stripped) = body.strip_prefix("#[").and_then(|s| s.strip_suffix(']')) {
        body = stripped.trim();
    }

    let expected_attr = match contract_kind {
        TrustContractKind::Requires => "requires",
        TrustContractKind::Ensures => "ensures",
        TrustContractKind::Temporal => "temporal",
        // Native loop-clause spans cover the predicate/measure itself (not an
        // attribute wrapper). Keeping these names here makes the fallback
        // robust to a future exact-compat attribute desugaring as well.
        TrustContractKind::LoopInvariant => "invariant",
        TrustContractKind::Decreases => "decreases",
        _ => return None,
    };

    if let Some(open_idx) = body.find('(') {
        let attr_name = body[..open_idx].trim().rsplit("::").next().unwrap_or_default();
        if attr_name == expected_attr {
            let close_idx = matching_close_paren(body, open_idx)?;
            if body[close_idx + 1..].trim().is_empty() {
                return Some(body[open_idx + 1..close_idx].trim());
            }
        }
    }

    Some(body)
}

fn matching_close_paren(text: &str, open_idx: usize) -> Option<usize> {
    if text.as_bytes().get(open_idx) != Some(&b'(') || !text.is_char_boundary(open_idx) {
        return None;
    }
    let mut depth = 0usize;
    let mut idx = open_idx;
    while idx < text.len() {
        if let Some(end) = protected_contract_token_end(text, idx) {
            idx = end;
            continue;
        }
        let ch = text[idx..].chars().next()?;
        match ch {
            '(' => depth += 1,
            ')' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(idx);
                }
            }
            _ => {}
        }
        idx += ch.len_utf8();
    }
    None
}

/// Return the byte after a token whose contents must be opaque to the helper
/// scanner: strings/chars and comments. Unterminated tokens consume the rest of
/// the snippet, which is the fail-closed direction — the parser will reject the
/// malformed clause and no helper-looking bytes inside it can gain meaning.
fn protected_contract_token_end(text: &str, start: usize) -> Option<usize> {
    let bytes = text.as_bytes();
    if start >= bytes.len() || !text.is_char_boundary(start) {
        return None;
    }

    if bytes[start..].starts_with(b"//") {
        return Some(text[start..].find('\n').map_or(text.len(), |offset| start + offset));
    }
    if bytes[start..].starts_with(b"/*") {
        let mut depth = 1usize;
        let mut idx = start + 2;
        while idx < bytes.len() {
            if bytes[idx..].starts_with(b"/*") {
                depth = depth.checked_add(1)?;
                idx += 2;
            } else if bytes[idx..].starts_with(b"*/") {
                depth -= 1;
                idx += 2;
                if depth == 0 {
                    return Some(idx);
                }
            } else {
                idx += text[idx..].chars().next()?.len_utf8();
            }
        }
        return Some(text.len());
    }

    // Raw Rust strings: r"...", r#"..."#, br#"..."#, and cr#"..."#.
    let prefix_len = if bytes[start..].starts_with(b"br") || bytes[start..].starts_with(b"cr") {
        2
    } else if bytes[start] == b'r' {
        1
    } else {
        0
    };
    if prefix_len != 0 {
        let mut quote = start + prefix_len;
        while bytes.get(quote) == Some(&b'#') {
            quote += 1;
        }
        if bytes.get(quote) == Some(&b'"') {
            let hashes = quote - (start + prefix_len);
            let mut idx = quote + 1;
            while idx < bytes.len() {
                if bytes[idx] == b'"'
                    && bytes.get(idx + 1..idx + 1 + hashes)
                        == Some(&bytes[start + prefix_len..quote])
                {
                    return Some(idx + 1 + hashes);
                }
                idx += text[idx..].chars().next()?.len_utf8();
            }
            return Some(text.len());
        }
    }

    let quote = match bytes[start] {
        b'"' => b'"',
        b'\'' => b'\'',
        _ => return None,
    };
    let mut escaped = false;
    let mut idx = start + 1;
    while idx < bytes.len() {
        let ch = text[idx..].chars().next()?;
        if escaped {
            escaped = false;
        } else if ch == '\\' {
            escaped = true;
        } else if ch as u32 == u32::from(quote) {
            return Some(idx + ch.len_utf8());
        }
        idx += ch.len_utf8();
    }
    Some(text.len())
}

/// Whether the clause being lowered carries an authored `by <theorem>`
/// citation.
///
/// A cited clause is owned end to end by the citation lane, which mints and
/// grades its own obligation inventory; the snippet lane must not change what
/// that lane sees. An UNCITED clause has no such owner, which is exactly why
/// the attribute surface's `result` spelling is admitted only in that case
/// (see `lower_contract_snippet_body_with_domains`).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum ClauseCitation {
    Present,
    Absent,
}

#[cfg(test)]
fn lower_contract_snippet_body(
    body: &str,
    contract_kind: TrustContractKind,
    origin: ContractClauseOrigin,
) -> Option<TrustContractPredicateKind> {
    lower_contract_snippet_body_with_domains(
        body,
        contract_kind,
        origin,
        ClauseCitation::Absent,
        &[],
        &ProjectionEnvironment::default(),
        &mut None,
        &mut None,
    )
}

fn lower_contract_snippet_body_with_domains(
    body: &str,
    contract_kind: TrustContractKind,
    origin: ContractClauseOrigin,
    citation: ClauseCitation,
    signature_domains: &[LoweredVariableDomain],
    signature_projections: &ProjectionEnvironment,
    // See `tokenize_contract_snippet`: set only when the clause is refused
    // BECAUSE OF a numeric literal, so the caller can attribute the refusal
    // instead of degrading to a silent `Unsupported`.
    literal_refusal: &mut Option<trust_types::int_literal::IntLiteralRefusal>,
    // Set only when a projection chain could not be resolved to an exact field
    // place. Attribution only; see `SnippetParser::projection_refusal`.
    projection_refusal: &mut Option<String>,
) -> Option<TrustContractPredicateKind> {
    let body = body.trim();
    // Trust: E4/E5 are verifier expressions in a parser island, not Rust HIR
    // expressions. Preserve the exact authored text for the machine-domain
    // `trust_types::parse_spec_expr` consumer. This applies to both loop E5 and
    // function-recursion E5: trying to run the function-clause Bool-only
    // snippet parser here rejects arithmetic measures and would turn a valid
    // `decreases e` into an inert `Unsupported` payload.
    if matches!(contract_kind, TrustContractKind::LoopInvariant | TrustContractKind::Decreases) {
        // Prime rejection is deliberately uniform across clause kinds (see the
        // comment below): a primed place has no bindable state here either, so
        // the opaque loop-clause carrier must not smuggle one past the source
        // boundary. `trust_types::parse_spec_expr` also rejects primes, but the
        // fail-close belongs at the first boundary that sees the text.
        if primed_identifier_in_contract_snippet(body).is_some() {
            return None;
        }
        return (!body.is_empty())
            .then(|| TrustContractPredicateKind::Opaque { text: Symbol::intern(body) });
    }
    // Trust (2026-08-26): the ATTRIBUTE surface has TWO `ensures` spellings and
    // only one of them was lowered here. The migration spelling is a closure
    // (`#[ensures(|r| ...)]`); the ratified spelling names the return place
    // directly (`#[ensures(result >= x)]`), which is also the ONLY spelling an
    // island-def-calling clause can use. `ensures_closure_snippet_body` returns
    // `None` for the latter and the `?` propagated that straight into
    // `Unsupported` — so `#[trust::ensures(result >= x)]` left a pair of
    // fail-closed sentinel obligations that a non-strict policy downgrades to
    // warnings, while the byte-identical native `ensures result >= x` lowered
    // into a real Postcondition VC and was proved (satisfied body) or REFUTED
    // (violated body). Same predicate, same body, one enforced and one inert:
    // measured on `veripb-core-proved`, an uncited attribute `result >= x` over
    // `x.wrapping_sub(1)` reported `0 proved, 0 failed, 2 unknown` and the build
    // stayed green.
    //
    // Binding `result` here is not a NEW reservation. `result` collides with the
    // source-contract return-place vocabulary
    // (`trust_types::source_contract_synthetic_name_collision`), so
    // `reject_unrepresentable_contract_parameter_names` has already emptied the
    // bundle of any contract-carrying function that has a parameter of that
    // name. In a non-closure attribute payload the identifier therefore has
    // exactly one possible meaning — the same one it has in native position.
    //
    // Scope is deliberately narrow in two directions:
    //   * CITED clauses keep the old treatment. The citation lane owns them end
    //     to end and mints its own obligation inventory; adding rows underneath
    //     it is a live-inventory change with no upside, since the kernel proof
    //     already closes the clause.
    //   * The new path is gated below by the SAME source-typing check native
    //     clauses must pass, so a clause the canonical formula consumer cannot
    //     elaborate — an island-definition call such as `eqOkW(machine, truth)`,
    //     whose callee is a Clean definition and not a signature-domain leaf —
    //     stays `Unsupported` and keeps flowing to the uncited island-defeq lane
    //     that owns it. This increment does not touch that lane's inputs.
    let mut attribute_result_spelling = false;
    let (expr, result_binding) = if contract_kind == TrustContractKind::Ensures {
        match origin {
            ContractClauseOrigin::Attribute => match ensures_closure_snippet_body(body) {
                Some((expr, result_binding)) => {
                    (expr, Some(SnippetResultBinding::ClosureReference(result_binding)))
                }
                None if citation == ClauseCitation::Absent => {
                    attribute_result_spelling = true;
                    (body, Some(SnippetResultBinding::NativeValue(ENSURES_RESULT_BINDING)))
                }
                None => return None,
            },
            ContractClauseOrigin::Native => {
                (body, Some(SnippetResultBinding::NativeValue(ENSURES_RESULT_BINDING)))
            }
        }
    } else {
        (strip_single_expr_block(body).unwrap_or(body), None)
    };

    let syntax = match origin {
        ContractClauseOrigin::Attribute => SnippetSyntax::AttributeCompatibility,
        ContractClauseOrigin::Native => SnippetSyntax::Native,
    };
    // A prime is reserved native grammar for a post-state place, but the
    // current contract carrier has no entry/post-state environment with which
    // to bind it. Treating `x'` as an ordinary formula variable would make it
    // unconstrained and could prove a contract about the wrong state. Keep the
    // grammar reservation, but reject every semantic use until lowering can
    // attach an exact MIR place and state epoch. This is deliberately uniform
    // across clause kinds: primes are not meaningful in requires, invariants,
    // or other one-state predicates either.
    //
    // Trust (D2 primes, 2026-09-30): one exception. In a NATIVE, uncited
    // `ensures`, a prime on a `&mut` parameter's pointee is bound to an exact
    // place: the projection environment resolves `self'.storage.detached` (and
    // `x'` for a scalar `&mut`) to the canonical place today's lane reads at exit
    // (see `LeafEpoch`). Every other primed spelling has no entry there and still
    // fails the clause closed, as does a clause mixing a primed and an unprimed
    // `&mut` pointee read. Requires, invariants, cited and attribute clauses keep
    // the uniform refusal.
    let primes_bindable = contract_kind == TrustContractKind::Ensures
        && origin == ContractClauseOrigin::Native
        && citation == ClauseCitation::Absent;
    if !primes_bindable && primed_identifier_in_contract_snippet(expr.trim()).is_some() {
        return None;
    }
    let lowered = SnippetParser::parse(
        expr.trim(),
        result_binding,
        syntax,
        signature_projections,
        literal_refusal,
        projection_refusal,
    )?;
    if let Some(value) = lowered.bool_literal {
        Some(TrustContractPredicateKind::BoolLiteral { value })
    } else if trust_types::parse_spec_expr(&lowered.text).is_some()
        && (!(origin == ContractClauseOrigin::Native || attribute_result_spelling)
            || native_function_clause_is_source_typed(
                &lowered.text,
                contract_kind,
                signature_domains,
            ))
    {
        // Do not label a syntactically captured clause as a supported opaque
        // predicate unless the canonical formula consumer can elaborate the
        // exact text. This closes the old two-parser gap where the compiler
        // query admitted vocabulary that vcgen later downgraded to
        // `Unsupported` (notably stale quantifier spellings and unknown binder
        // types). Failure is explicit and fail-closed at the source boundary.
        Some(lowered_contract_text_with_domains(lowered.text, signature_domains))
    } else {
        None
    }
}

/// Scope- and sort-check a successfully parsed native function clause before
/// it can become an opaque verifier payload. E4/E5 use the richer exact HIR
/// environment in `validate_native_clause_body`; this companion closes the
/// flat requires/ensures path without changing the grammar-only treatment of
/// unsupported constructs such as primed places (which never reach here).
fn native_function_clause_is_source_typed(
    body: &str,
    contract_kind: TrustContractKind,
    signature_domains: &[LoweredVariableDomain],
) -> bool {
    let clause = match contract_kind {
        TrustContractKind::Requires => trust_types::SourceContractClause::Requires,
        TrustContractKind::Ensures => trust_types::SourceContractClause::Ensures,
        // Native decreases is validated earlier with aggregate-aware source
        // sorts; loop invariants never use this function-clause snippet path.
        TrustContractKind::Decreases | TrustContractKind::LoopInvariant => return true,
        _ => return false,
    };
    trust_types::validate_source_spec_expr_with_exact_projections(
        body,
        clause,
        &signature_source_sorts(signature_domains),
    )
    .is_ok()
}

/// Return the first identifier carrying one or more trailing prime marks. This
/// small scanner remains usable for diagnostics even when the rest of a
/// malformed clause cannot be tokenized.
///
/// Trust (CITE-PRIME-NONASCII-1, 2026-10-05): identifiers are lexed on whole
/// characters with rustc's own predicates (`rustc_lexer::is_id_start` /
/// `is_id_continue`), not as ASCII byte runs. Rust identifiers may be
/// non-ASCII; the byte scanner reported `éa'` as `a'` and did not see `δ'` at
/// all. Both readers downstream of this gate (the snippet tokenizer and
/// `trust_types::parse_spec_expr`) refuse non-ASCII input, so the miss failed
/// closed, but this is the first boundary that must see the prime, and the
/// diagnostic must name the identifier the author wrote.
fn primed_identifier_in_contract_snippet(input: &str) -> Option<&str> {
    let mut chars = input.char_indices().peekable();
    while let Some((start, first)) = chars.next() {
        if !rustc_lexer::is_id_start(first) {
            continue;
        }
        let mut end = start + first.len_utf8();
        while let Some(&(index, next)) = chars.peek() {
            if !rustc_lexer::is_id_continue(next) {
                break;
            }
            end = index + next.len_utf8();
            chars.next();
        }
        let primes = input[end..].bytes().take_while(|&byte| byte == b'\'').count();
        if primes > 0 {
            return Some(&input[start..end + primes]);
        }
    }
    None
}

fn ensures_closure_snippet_body(body: &str) -> Option<(&str, &str)> {
    let mut rest = body.trim();
    if let Some(stripped) = rest.strip_prefix("move") {
        if stripped.chars().next().map_or(true, |ch| ch.is_whitespace() || ch == '|') {
            rest = stripped.trim_start();
        }
    }

    let after_open = rest.strip_prefix('|')?;
    let close_idx = after_open.find('|')?;
    let arg_spec = after_open[..close_idx].trim();
    if arg_spec.is_empty() || arg_spec.contains(',') {
        return None;
    }
    let arg_name = arg_spec.split(':').next()?.trim();
    if !is_simple_ident(arg_name) {
        return None;
    }

    let expr = after_open[close_idx + 1..].trim();
    let expr = strip_single_expr_block(expr).unwrap_or(expr);
    (!expr.trim().is_empty()).then_some((expr.trim(), arg_name))
}

fn strip_single_expr_block(expr: &str) -> Option<&str> {
    let inner = expr.trim().strip_prefix('{')?.strip_suffix('}')?.trim();
    if inner.is_empty() || inner.contains(';') {
        return None;
    }
    Some(inner)
}

fn is_simple_ident(text: &str) -> bool {
    let mut chars = text.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if first != '_' && !first.is_ascii_alphabetic() {
        return false;
    }
    chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
}

struct ExprLowerer<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck_results: &'a TypeckResults<'tcx>,
    result_binding: Option<HirId>,
    /// Active substitutions for pattern-bound variables introduced by a
    /// recognized `matches!(result, Ok(<bind>) if <guard>)` arm. Maps the
    /// binding's `HirId` to the spec text that stands for the corresponding
    /// component of the result's `Ok` payload (e.g. `result.unwrap()` for a
    /// single bind). A path to one of these binds inside the guard lowers to its
    /// substituted text instead of being rejected as the (forbidden) bare result
    /// binding. Empty outside a `matches!` guard.
    pat_bindings: Vec<(HirId, String)>,
    /// Trust: how many nested contract-predicate call inlines are already in
    /// progress (see `lower_inlined_call`). Bounds the inline unconditionally,
    /// which is what makes a MUTUALLY RECURSIVE pair of helpers terminate: no
    /// structural gate rules one out, because `fn f(x) -> i64 { g(x) }` and
    /// `fn g(x) -> i64 { f(x) }` are both single-tail-expression bodies.
    /// Exceeding the bound returns `None`, so the predicate fails closed.
    inline_depth: u32,
}

impl<'tcx> ExprLowerer<'_, 'tcx> {
    fn lower_predicate(&self, expr: &'tcx Expr<'tcx>) -> Option<TrustContractPredicateKind> {
        match &expr.kind {
            ExprKind::Lit(lit) => match lit.node {
                LitKind::Bool(value) => Some(TrustContractPredicateKind::BoolLiteral { value }),
                _ => self.lower_bool_expr_text(expr).map(|lowered| {
                    lowered_contract_text_with_domains(lowered.text, &lowered.variable_domains)
                }),
            },
            _ => self.lower_bool_expr_text(expr).map(|lowered| {
                lowered_contract_text_with_domains(lowered.text, &lowered.variable_domains)
            }),
        }
    }

    fn lower_bool_expr_text(&self, expr: &'tcx Expr<'tcx>) -> Option<LoweredExpr> {
        let lowered = self.lower_expr_text(expr)?;
        (lowered.ty == LoweredExprTy::Bool).then_some(lowered)
    }

    fn lower_expr_text(&self, expr: &'tcx Expr<'tcx>) -> Option<LoweredExpr> {
        match &expr.kind {
            ExprKind::Lit(lit) => match lit.node {
                LitKind::Bool(value) => {
                    Some(LoweredExpr::literal(value.to_string(), LoweredExprTy::Bool))
                }
                LitKind::Int(value, _) => i128::try_from(value.get())
                    .ok()
                    .map(|value| LoweredExpr::literal(value.to_string(), LoweredExprTy::Int)),
                // Trust: a float literal in a magnitude bound (`self.0 <= 1.0e30`).
                // Emit the source spelling verbatim as float-sorted text; the spec
                // parser's float tokenizer re-reads it. NaN/inf cannot appear as a
                // `LitKind::Float` source literal, so the value is always finite.
                LitKind::Float(sym, _) => {
                    Some(LoweredExpr::literal(sym.to_string(), LoweredExprTy::Float))
                }
                _ => None,
            },
            // A path naming a `const`/associated `const` is resolved to the
            // program's own value first; only a non-const path continues to the
            // local-binding lowering, so no existing variable arm changes.
            ExprKind::Path(qpath) => self
                .lower_const_path_expr(expr, qpath)
                .or_else(|| self.lower_path_expr(expr, qpath)),
            ExprKind::Unary(UnOp::Not, inner) => {
                let inner = self.lower_expr_text(inner)?;
                if inner.ty != LoweredExprTy::Bool {
                    return None;
                }
                Some(LoweredExpr {
                    text: format!("!({})", inner.text),
                    ty: LoweredExprTy::Bool,
                    variable_domains: inner.variable_domains,
                })
            }
            // Trust: integer negation `-x` in a contract predicate (e.g.
            // `ensures(|r| *r == -x)` for `abs`). The spec parser lowers a leading
            // `-` to `Formula::Neg`, so a `-(<int expr>)` text round-trips. Without
            // this arm the whole predicate was rejected as unsupported.
            ExprKind::Unary(UnOp::Neg, inner) => {
                let inner = self.lower_expr_text(inner)?;
                if inner.ty != LoweredExprTy::Int && inner.ty != LoweredExprTy::Float {
                    return None;
                }
                let ty = inner.ty;
                Some(LoweredExpr {
                    text: format!("-({})", inner.text),
                    ty,
                    variable_domains: inner.variable_domains,
                })
            }
            ExprKind::Unary(UnOp::Deref, inner) => self.lower_deref_expr(expr, inner),
            ExprKind::Binary(op, lhs, rhs) => {
                // Ok-payload ORDERING guard `d > c` / `d == c` over two Ok-payload
                // pattern bindings of a numeric-but-non-scalar type (`Rat` d,c in
                // `matches!(r, Ok((d,c)) if d > c)` — ny-cert selfcheck/branch). Emits
                // the pair-term ordering `result.unwrap().__trust_ok_0 <op> …_1` for
                // vcgen's Ordering-witness grounding (generate.rs b62 F4), which pins
                // the fact from the body's dominating `<Rat as PartialOrd>::{lt,le,gt,
                // ge}` guard. SOUND (fail-closed): the pair terms are FREE until that
                // lane pins them, so an ungroundable pair can only FAIL to prove, never
                // vacuously prove — adversarially verified (a flipped-false `d>c`
                // ensures is correctly refuted while the true ones prove). Neither
                // operand lowers on its own (a `&Rat` bind is non-scalar), so this is
                // purely additive over the fail-closed status quo.
                if matches!(
                    op.node,
                    BinOpKind::Lt
                        | BinOpKind::Le
                        | BinOpKind::Gt
                        | BinOpKind::Ge
                        | BinOpKind::Eq
                        | BinOpKind::Ne
                ) && let (Some(a), Some(b)) =
                    (self.ok_payload_binding_text(lhs), self.ok_payload_binding_text(rhs))
                {
                    let op_text = lower_bin_op(op.node)?;
                    return lowered_synthetic_expr(
                        format!("({a}) {op_text} ({b})"),
                        LoweredExprTy::Bool,
                        TrustContractPropositionDomain::MathematicalInt,
                    );
                }
                let lhs = self.lower_expr_text(lhs)?;
                let rhs = self.lower_expr_text(rhs)?;
                lower_binary_expr_text(op.node, lhs, rhs)
            }
            // `Use` is a value-transparent capture wrapper emitted around
            // compiler contract expressions. Exact HIR identity deliberately
            // lands on that authored expression instead of searching inward by
            // span, so the typed lowerer must look through the wrapper.
            ExprKind::Type(inner, _) | ExprKind::DropTemps(inner) | ExprKind::Use(inner, _) => {
                self.lower_expr_text(inner)
            }
            // Trust: a field projection `base.field` in a contract predicate (e.g.
            // `ensures(|r| *r == p.value)` for a struct accessor). Lowers to the text
            // `<base>.<INDEX>` (see `lower_projection_base` — the field is named by
            // its positional INDEX, matching the MIR `Field(i)` place naming and
            // `place_to_var_name`), so a postcondition referencing the field and the
            // return ground to the same `.i` projection. The base is an aggregate (a
            // struct parameter/capture/result binding), so its NAME is taken
            // directly (it has no scalar lowering); only the FIELD's type must be
            // scalar.
            ExprKind::Field(..) => {
                let text = self.lower_projection_base(expr)?;
                lowered_variable_expr(self.tcx, text, self.typeck_results.expr_ty(expr))
            }
            // Trust: a projected element read whose SCALAR is the element
            // itself (`self.d[0] <= 1.0e30` on `d: [f64; 4]` — no trailing
            // field). The projection-base lowering already produces the full
            // `<base>[k]` name with every static gate (builtin array, literal
            // in-range index); without this arm the value position fell to
            // `_ => None` and the whole clause died as Unsupported even though
            // the crate-side parser and gate accept the name.
            ExprKind::Index(..) => {
                let text = self.lower_projection_base(expr)?;
                lowered_variable_expr(self.tcx, text, self.typeck_results.expr_ty(expr))
            }
            // Trust: a value-preserving integer WIDENING cast `x as T` in a
            // contract predicate (`ensures(|r| *r == (x as u64))`, `x as usize`
            // guards). A widening (see `value_preserving_int_cast`) has the SAME
            // mathematical value as its operand, so the spec — which reasons in
            // arbitrary-precision Int — may DROP the cast and use the operand's
            // text directly, instead of rejecting the whole predicate as
            // unsupported. A narrowing / sign-changing / `usize`-`isize` cast is
            // NOT value-preserving and REJECTS (fail-closed — the operand text
            // would misrepresent the truncated/wrapped value, so refusing is the
            // only sound choice; never a false PROVE). Over-refutation audit #4
            // (cast half).
            ExprKind::Cast(inner, _) => {
                let src = self.typeck_results.expr_ty(inner);
                let dst = self.typeck_results.expr_ty(expr);
                if !value_preserving_int_cast(self.tcx, src, dst) {
                    return None;
                }
                let inner = self.lower_expr_text(inner)?;
                if inner.ty != LoweredExprTy::Int {
                    return None;
                }
                Some(LoweredExpr {
                    text: inner.text,
                    ty: LoweredExprTy::Int,
                    variable_domains: inner.variable_domains,
                })
            }
            // Trust: a CLOSED allow-list of boolean sign accessors on a numeric
            // receiver inside a contract predicate (e.g. `c.is_positive()` for the
            // rational `c` extracted from an `Ok` payload by a recognized
            // `matches!` arm — see the `Match` arm below). Lowers to the text
            // `<recv>.is_positive()` (resp. `.is_negative()` / `.is_zero()`), which
            // the spec parser models with the synthetic sign var `<recv>__sign` and
            // the trichotomy `__sign > 0` / `__sign < 0` / `__sign == 0`. The set is
            // CLOSED: any other method REJECTS (returns None) — never a guess, so a
            // method we do not exactly model can never silently weaken the VC.
            //
            // SEMANTICS (the predicate text emitted, read by spec_parse):
            //   recv.is_positive() ↦ "<recv>.is_positive()"  ⟹  <recv>__sign > 0
            //   recv.is_negative() ↦ "<recv>.is_negative()"  ⟹  <recv>__sign < 0
            //   recv.is_zero()     ↦ "<recv>.is_zero()"      ⟹  <recv>__sign == 0
            // The receiver must itself lower (to a value-typed term); the result is
            // a Bool. The synthetic `__sign` term is a free variable until the VC
            // layer links it to the receiver's value, so the predicate is
            // fail-closed (can only fail to prove, never vacuously prove).
            // Trust: a call `g(a1, .., an)` to a TRANSPARENT helper inside a
            // contract predicate — the shape that makes compositional
            // specification writable at all (`ensures result == scale(x)`).
            //
            // `TrustContractProposition` has NO call node: its closed vocabulary
            // is Bool/Int/UInt/Var plus arithmetic, comparison and the boolean
            // connectives. Minting a synthetic free var for the call would be
            // sound but useless — a term the VC layer cannot ground can only ever
            // FAIL to prove. So the call is INLINED instead: the callee's own tail
            // expression is lowered with its parameters bound to the
            // already-lowered actuals, yielding ordinary arithmetic in the
            // EXISTING vocabulary. No new proposition node, no VC-layer change,
            // and nothing left to ground.
            ExprKind::Call(callee, args) => self.lower_inlined_call(callee, args),
            ExprKind::MethodCall(segment, receiver, args, _) => {
                // No-argument accessors only. `is_positive`/`is_negative`/`is_zero`
                // and the `Option` accessors below are all `&self`/`self -> _` with
                // no extra args; a non-empty arg list is not an idiom we model -> reject.
                if !args.is_empty() {
                    return None;
                }
                let method = segment.ident.name;
                // Trust: the `Option` accessors on the ensures RESULT binding —
                // `is_none()`/`is_some()` (the discriminant predicates) and
                // `unwrap()` (the payload value). The crate-side spec parser models
                // `result.is_none()` as `_0__discr == 0`, `result.is_some()` as
                // `_0__discr != 0`, and `result.unwrap()` as the payload term
                // `_0__value` (`map_var_name("result") == "_0"`), which the vcgen
                // contract lane grounds to the body's in-body `Some`/`None`
                // construction (`enum_return_grounded_model_vars` + the discr/value
                // return pin). This lets an `Option`-returning function carry a live
                // `#[ensures(|r| r.is_none() || low <= r.unwrap() && r.unwrap() <= high)]`
                // that PROVES, instead of the whole predicate being rejected as an
                // unsupported contract expression. Gated to the EXACT result binding
                // of `Option` type (diagnostic item, not a name match — see
                // `receiver_is_result_option`), and for `unwrap` an INTEGER payload
                // (matching the `Sort::Int` the spec parser mints for `_0__value`);
                // anything else falls through to the sign allow-list / rejects.
                // SOUND: `_0__discr`/`_0__value` are free until the VC layer pins them
                // to the genuine constructed value, so an unpinnable predicate can
                // only FAIL to prove, never vacuously prove.
                match method.as_str() {
                    m @ ("is_none" | "is_some") if self.receiver_is_result_option(receiver) => {
                        return lowered_synthetic_expr(
                            format!("{ENSURES_RESULT_BINDING}.{m}()"),
                            LoweredExprTy::Bool,
                            TrustContractPropositionDomain::MathematicalInt,
                        );
                    }
                    "unwrap"
                        if self.receiver_is_result_option(receiver)
                            && lowered_expr_ty(self.tcx, self.typeck_results.expr_ty(expr))
                                == Some(LoweredExprTy::Int) =>
                    {
                        return lowered_variable_expr(
                            self.tcx,
                            format!("{ENSURES_RESULT_BINDING}.unwrap()"),
                            self.typeck_results.expr_ty(expr),
                        );
                    }
                    // Trust: `.len()` / `.is_empty()` on a std sequence (Vec /
                    // slice / array) projected out of the matched OK PAYLOAD of a
                    // recognized `matches!` arm (the ny-cert crown shape:
                    // `matches!(r, Ok(c) if c.entailment.premises.len() != ..)`).
                    // The crate-side spec parser ALREADY models these
                    // (`spec_parse::map_method_call`: `.len()` -> the synthetic
                    // Int var `<base>__len`; `.is_empty()` -> `<base>__len == 0`),
                    // so the lowering emits `<recv>.len()` verbatim.
                    //
                    // TWO closed gates, both fail-closed (return None -> the whole
                    // predicate stays SpecEnsuresUnparseable, never a guess):
                    //
                    // 1. The receiver TYPE must be the std `Vec` (diagnostic item,
                    //    never a name match) or a slice/array. Their `len` is the
                    //    inherent, PURE length accessor (inherent methods win over
                    //    any trait method of the same name), so two occurrences of
                    //    the same receiver text denote the SAME value and the one
                    //    minted `<base>__len` var models it exactly. A user type's
                    //    `len` has no such guarantee (an impure/nondeterministic
                    //    `len` under one shared var could vacuously prove
                    //    `x.len() == x.len()` while the runtime check fails).
                    //
                    // 2. The receiver must lower to a projection base STRICTLY
                    //    UNDER the Ok-payload term — `result.unwrap().<seg>…` (a
                    //    pat-binding substitution plus at least one projection —
                    //    see `collect_ok_pattern_bindings` /
                    //    `lower_projection_base`). The spec parser then mints
                    //    `_0__value.<seg>…__len`, whose FIRST path segment keeps the
                    //    `__value` marker, so `is_spec_model_var` classifies it as
                    //    a SPEC-MODEL term and an ungroundable predicate routes to
                    //    the fail-closed Unknown (SpecModelUngrounded). Any OTHER
                    //    base would mint a NON-model free var — a parameter `xs`
                    //    gives `xs__len`, the bare `result` gives `_0__len`, and
                    //    even the BARE payload `result.unwrap()` gives
                    //    `_0__value__len` (one undivided segment ending `__len`, NOT
                    //    `__value` — pinned NOT spec-model by trust-vcgen's
                    //    name-shape test) — and the postcondition would become a
                    //    refutable VC satisfiable by havoc: reported Failed with
                    //    a fabricated counterexample. Rejecting here keeps every
                    //    such shape fail-closed (SpecEnsuresUnparseable).
                    //
                    // SOUND: the minted `_0__value…_len` term is free until the VC
                    // layer pins it to a genuine body length, so the predicate can
                    // only FAIL to prove, never vacuously prove.
                    m @ ("len" | "is_empty") => {
                        let recv_ty = self.typeck_results.expr_ty(receiver).peel_refs();
                        let modeled_seq = recv_ty.is_slice()
                            || recv_ty.is_array()
                            || recv_ty.ty_adt_def().is_some_and(|adt| {
                                self.tcx.is_diagnostic_item(rustc_span::sym::Vec, adt.did())
                            });
                        if !modeled_seq {
                            return None;
                        }
                        let recv = self.lower_projection_base(receiver)?;
                        let payload_root = format!("{ENSURES_RESULT_BINDING}.unwrap().");
                        if !recv.starts_with(&payload_root) {
                            return None;
                        }
                        return lowered_synthetic_expr(
                            format!("{recv}.{m}()"),
                            if m == "len" { LoweredExprTy::Int } else { LoweredExprTy::Bool },
                            proposition_domain_from_ty(self.tcx, self.tcx.types.usize)?,
                        );
                    }
                    _ => {}
                }
                // CLOSED allow-list of numeric sign accessors — any other method
                // rejects (never a guess).
                let method_str = match method.as_str() {
                    m @ ("is_positive" | "is_negative" | "is_zero") => m,
                    _ => return None,
                };
                // The receiver of a sign predicate is EITHER a value-typed (Int)
                // term, OR an Ok-payload PATTERN BINDING of a numeric type that is
                // itself non-scalar — e.g. `c` of type `Rat`/`&Rat` in
                // `matches!(r, Ok(c) if c.is_positive())` (ny-cert selfcheck). For
                // the binding case the substituted payload term (`result.unwrap()`
                // / `…__trust_ok_i`) carries the sign; the crate spec parser + vcgen
                // sign-witness grounding (generate.rs b62 F4 — the payload type's OWN
                // inherent `is_positive`/`is_negative`/`is_zero` on the return place)
                // model `<payload>.is_positive()` via the synthetic `<payload>_sign`
                // var. SOUND: that var is FREE until the VC layer grounds it to the
                // payload's real sign, so an ungroundable payload can only FAIL to
                // prove, never vacuously prove (fail-closed) — identical discipline
                // to the Int path, which the `recv.ty != Int` gate would otherwise
                // reject because `&Rat`/`Rat` is not scalar-lowerable.
                let recv_text = if let Some(text) = self.ok_payload_binding_text(receiver) {
                    text
                } else {
                    let recv = self.lower_expr_text(receiver)?;
                    if recv.ty != LoweredExprTy::Int {
                        return None;
                    }
                    recv.text
                };
                lowered_synthetic_expr(
                    format!("{recv_text}.{method_str}()"),
                    LoweredExprTy::Bool,
                    TrustContractPropositionDomain::MathematicalInt,
                )
            }
            // Trust: the EXACT `matches!(result, Ok(<bind>) if <guard>)` idiom,
            // which desugars (library/core `macro_rules! matches!`) to a 2-arm
            // match:  `match <result> { Ok(<bind>) if <guard> => true, _ => false }`.
            // See `lower_matches_idiom` for the full structural recognizer and the
            // soundness argument. Any other match shape REJECTS (None) — we never
            // lower a match we do not fully model.
            ExprKind::Match(scrutinee, arms, MatchSource::Normal) => {
                // Two recognizers, both fail-closed (None unless the shape is
                // EXACT): the `matches!(r, Ok(c) if G)` macro desugar, and — the
                // ny-cert crown_deep "match-wrapper" ensures — the explicit
                // `match r { Ok(c) => G, Err(_) => true }` classification. They
                // are the SAME predicate written two ways; both lower to the same
                // `result.is_ok()`/payload-term modeling.
                self.lower_matches_idiom(scrutinee, arms)
                    .or_else(|| self.lower_ok_implies_match(scrutinee, arms))
            }
            _ => None,
        }
    }

    /// Recognize and lower EXACTLY the boolean `matches!` idiom
    /// `matches!(<result>, Ok(<bind>) if <guard>)`, which the `matches!` macro
    /// expands to the 2-arm match
    ///   `match <result> { Ok(<bind>) if <guard> => true, _ => false }`.
    ///
    /// We lower it to the SEMANTIC EQUIVALENT boolean text
    ///   `(<result>.is_ok()) && (<guard, with <bind> substituted to the Ok value>)`
    /// where `<result>` is the result binding (lowered to `result`). The spec
    /// parser models `result.is_ok()` as `_0__discr != 0` and the substituted bind
    /// as the Ok payload term(s).
    ///
    /// SOUNDNESS — why this is the exact semantic equivalent (and how it composes
    /// under the outer `!` that the checker writes):
    ///   `matches!(r, Ok(c) if G)`  ≡  `r is Ok  AND  G[c := Ok-value of r]`.
    /// Our text emits exactly `(r.is_ok()) && (G[c := r's Ok value])`, so the
    /// outer `!matches!(...)` (handled by the existing `Unary(Not)` arm) becomes
    /// `!((r.is_ok()) && G)` ≡ `r is Err OR ¬G` ≡ `Ok ⟹ ¬G` — precisely the
    /// checker's intended postcondition. We REJECT (None) unless the match is
    /// EXACTLY this shape (fail-closed): scrutinee = the result binding; arm 0 =
    /// guarded `Ok(<bind>)` -> `true`; arm 1 = `_` (or equivalently-bare) -> `false`.
    fn lower_matches_idiom(
        &self,
        scrutinee: &'tcx Expr<'tcx>,
        arms: &'tcx [Arm<'tcx>],
    ) -> Option<LoweredExpr> {
        // Exactly two arms: the guarded Ok-arm and the wildcard fallthrough.
        let [ok_arm, wild_arm] = arms else {
            return None;
        };

        // Arm 1 must be the bare `_ => false` fallthrough: a wildcard pattern, no
        // guard, body the literal `false`. (Anything else is not the `matches!`
        // shape — reject.)
        if !matches!(wild_arm.pat.kind, PatKind::Wild)
            || wild_arm.guard.is_some()
            || !expr_is_bool_lit(wild_arm.body, false)
        {
            return None;
        }

        // Arm 0 must be `Ok(<bind>) if <guard> => true`: a guarded `Ok(..)` tuple
        // pattern whose body is the literal `true`.
        if !expr_is_bool_lit(ok_arm.body, true) {
            return None;
        }
        let guard = ok_arm.guard?;

        // The scrutinee must be the result binding (possibly behind autoref/deref
        // temps), lowering to the spec text `result`.
        let result_text = self.lower_result_scrutinee(scrutinee)?;

        // The Ok-arm pattern: `Ok(<bind>)` where <bind> is a single binding or a
        // tuple of bindings. Confirm the variant is `Result::Ok` (lang item) and
        // collect (HirId -> Ok-payload text) substitutions for the guard.
        let pat_bindings = self.collect_ok_pattern_bindings(ok_arm.pat, &result_text)?;

        // Lower the guard with the bind substitutions active. The guard is a
        // boolean predicate over the Ok payload (e.g. `c.is_positive()`, `d > c`).
        let guard_lowerer = ExprLowerer {
            tcx: self.tcx,
            typeck_results: self.typeck_results,
            result_binding: self.result_binding,
            pat_bindings,
            inline_depth: self.inline_depth,
        };
        let guard = guard_lowerer.lower_expr_text(guard)?;
        if guard.ty != LoweredExprTy::Bool {
            return None;
        }

        // `(result.is_ok()) && (<guard>)`.
        Some(LoweredExpr {
            text: format!("({result_text}.is_ok()) && ({})", guard.text),
            ty: LoweredExprTy::Bool,
            variable_domains: merge_variable_domains(
                synthetic_variable_domains(
                    &format!("{result_text}.is_ok()"),
                    TrustContractPropositionDomain::MathematicalInt,
                )?,
                guard.variable_domains,
            )?,
        })
    }

    /// The scrutinee of a recognized `matches!` must be the ensures result
    /// binding (the closure parameter, typically `&Result<..>`), possibly behind
    /// type-ascription / drop-temps wrappers. Lowers it to the spec text
    /// `result`. Returns None for any other scrutinee (fail-closed).
    fn lower_result_scrutinee(&self, expr: &'tcx Expr<'tcx>) -> Option<String> {
        let result_binding = self.result_binding?;
        expr_is_local_path(expr, result_binding).then(|| ENSURES_RESULT_BINDING.to_string())
    }

    /// Confirm `pat` is `Result::Ok(<bind>)` and produce the substitutions that
    /// map each pattern binding's `HirId` to the spec text for the corresponding
    /// component of the result's `Ok` payload:
    ///   - single bind `Ok(c)`         -> `c` ↦ `<result>.unwrap()`
    ///   - tuple  bind `Ok((d, c))`     -> `d` ↦ `<result>.unwrap().__trust_ok_0`,
    ///                                     `c` ↦ `<result>.unwrap().__trust_ok_1`
    /// `<result>.unwrap()` is the spec parser's Ok-payload term (`_0__value`); the
    /// positional `__trust_ok_i` projections give the spec parser DISTINCT, STABLE
    /// field vars for the tuple components (each bind -> a distinct free var; the
    /// same bind -> the same var throughout the guard). These payload terms are
    /// free until the VC layer links them, so the predicate is fail-closed.
    ///
    /// REJECTS (None) unless the variant is exactly `Result::Ok` (confirmed via the
    /// `ResultOk` lang item) and the payload is a single binding or a tuple of
    /// plain bindings — never a guess.
    fn collect_ok_pattern_bindings(
        &self,
        pat: &'tcx Pat<'tcx>,
        result_text: &str,
    ) -> Option<Vec<(HirId, String)>> {
        let PatKind::TupleStruct(qpath, fields, dot_dot) = pat.kind else {
            return None;
        };
        // `Ok(<bind>)` has exactly one field and no `..`.
        if dot_dot.as_opt_usize().is_some() {
            return None;
        }
        // Confirm the variant is `Result::Ok` via the lang item (never name-match).
        if !self.is_result_ok_variant(&qpath, pat.hir_id) {
            return None;
        }
        let [payload] = fields else {
            return None;
        };

        let ok_value = format!("{result_text}.unwrap()");
        match payload.kind {
            // `Ok(c)` — single binding (no sub-pattern).
            PatKind::Binding(_, hir_id, _, None) => Some(vec![(hir_id, ok_value)]),
            // `Ok((d, c))` — a tuple of plain bindings (no `..`).
            PatKind::Tuple(elems, tuple_dot_dot) => {
                if tuple_dot_dot.as_opt_usize().is_some() {
                    return None;
                }
                let mut bindings = Vec::with_capacity(elems.len());
                for (idx, elem) in elems.iter().enumerate() {
                    let PatKind::Binding(_, hir_id, _, None) = elem.kind else {
                        return None;
                    };
                    bindings.push((hir_id, format!("{ok_value}.__trust_ok_{idx}")));
                }
                Some(bindings)
            }
            _ => None,
        }
    }

    /// True iff `qpath` (a tuple-struct PATTERN path at `hir_id`) resolves to the
    /// `Result::Ok` variant, confirmed against the `ResultOk` lang item. A pattern
    /// path resolves to the variant's constructor (`DefKind::Ctor(Variant, _)`);
    /// its parent is the variant DefId we compare to the lang item.
    fn is_result_ok_variant(&self, qpath: &QPath<'tcx>, hir_id: HirId) -> bool {
        let Some(ok_variant) = self.tcx.lang_items().result_ok_variant() else {
            return false;
        };
        match self.typeck_results.qpath_res(qpath, hir_id) {
            Res::Def(DefKind::Ctor(CtorOf::Variant, _), ctor_def_id) => {
                self.tcx.parent(ctor_def_id) == ok_variant
            }
            Res::Def(DefKind::Variant, variant_def_id) => variant_def_id == ok_variant,
            _ => false,
        }
    }

    /// Recognize and lower EXACTLY the explicit result-classification match
    ///   `match <result> { Ok(<bind>) => <G>, Err(_) => true }`
    /// (equivalently `_ => true` for the second arm — an exhaustive `Result`
    /// match with an `Ok(<bind>)` first arm can only reach the second arm on the
    /// `Err` value). This is the ny-cert crown_deep "match-wrapper" ensures shape
    ///   `|r| match r { Ok(c) => c.…premises.len() == c.…multipliers.len(),
    ///                  Err(_) => true }`
    /// authored as a full `match` rather than the `matches!` macro.
    ///
    /// It is the SAME boolean as `!matches!(<result>, Ok(<bind>) if !G)`:
    ///   `match r { Ok(c) => G, Err(_) => true }`  ≡  `r is Ok ⟹ G`
    ///                                             ≡  `¬(r.is_ok() ∧ ¬G)[c := Ok value]`.
    /// We emit exactly the `!matches!` spelling `!((<result>.is_ok()) && (!(<G>)))`
    /// — byte-for-byte the shape `lower_matches_idiom` produces for the
    /// equivalent `!matches!` sibling — reusing the identical
    /// `result.is_ok()`/payload-term modeling and the identical fail-closed
    /// pieces (`lower_result_scrutinee`, `collect_ok_pattern_bindings`, the guard
    /// sub-lowerer). Keeping `result.is_ok()` in the POSITIVE `is_ok` position
    /// (not `!(result.is_ok())`, which double-negates the return discriminant and
    /// left the native typed-CHC lane unable to ground it) is what makes the
    /// lowered text flow through the SAME vcgen spec parse + len-witness
    /// return-grounding as the `matches!` form: a `.len() == .len()` guard
    /// grounded by the body's dominating arity guard becomes a genuinely PROVED
    /// Postcondition, and any ungroundable shape stays the fail-closed
    /// SpecModelUngrounded Unknown — never a false PROVE.
    ///
    /// REJECTS (None) unless the match is EXACTLY this shape (fail-closed):
    /// scrutinee = the result binding; arm 0 = UNGUARDED `Ok(<bind>)` whose body
    /// lowers to a Bool `G`; arm 1 = UNGUARDED `Err(_)`/`_` whose body is the
    /// literal `true`.
    fn lower_ok_implies_match(
        &self,
        scrutinee: &'tcx Expr<'tcx>,
        arms: &'tcx [Arm<'tcx>],
    ) -> Option<LoweredExpr> {
        // Exactly two arms: the `Ok`-arm carrying the predicate and the `Err`/`_`
        // fallthrough that vacuously holds (`Err(_) => true`).
        let [ok_arm, else_arm] = arms else {
            return None;
        };

        // Arm 1 must be an UNGUARDED `Err(_)` (or the bare wildcard `_`) whose
        // body is the literal `true`. Anything else is not this idiom — reject.
        if else_arm.guard.is_some() || !expr_is_bool_lit(else_arm.body, true) {
            return None;
        }
        if !self.is_err_or_wild_pat(else_arm.pat) {
            return None;
        }

        // Arm 0 must be an UNGUARDED `Ok(<bind>) => <bool G>`.
        if ok_arm.guard.is_some() {
            return None;
        }

        // The scrutinee must be the result binding (possibly behind autoref/deref
        // temps), lowering to the spec text `result`.
        let result_text = self.lower_result_scrutinee(scrutinee)?;

        // The Ok-arm pattern: `Ok(<bind>)`. Confirm the variant is `Result::Ok`
        // (lang item) and collect (HirId -> Ok-payload text) substitutions.
        let pat_bindings = self.collect_ok_pattern_bindings(ok_arm.pat, &result_text)?;

        // Lower the arm body (the predicate `G`) with the bind substitutions.
        let guard_lowerer = ExprLowerer {
            tcx: self.tcx,
            typeck_results: self.typeck_results,
            result_binding: self.result_binding,
            pat_bindings,
            inline_depth: self.inline_depth,
        };
        let g = guard_lowerer.lower_expr_text(ok_arm.body)?;
        if g.ty != LoweredExprTy::Bool {
            return None;
        }

        // Emit the EXACT `!matches!(result, Ok(c) if !G)` spelling, byte-for-byte
        // the same shape `lower_matches_idiom` produces for the equivalent
        // `!matches!` sibling (`crown::Relu1Problem::certify`, which PROVES):
        //   `!((result.is_ok()) && (!(G)))`
        // This is the same boolean as the match wrapper —
        //   `match r { Ok(c) => G, Err(_) => true }` ≡ `r is Ok ⟹ G`
        //   ≡ `¬(r.is_ok() ∧ ¬G)` — but crucially keeps `result.is_ok()` in the
        // POSITIVE `is_ok` position (a single `_0__discr` disequality) instead of
        // the negated `!(result.is_ok())` that lowers to a DOUBLE-negated
        // discriminant `Not(Not(Eq(_0__discr, 0)))`. The negated form left the
        // native typed-CHC lane unable to ground the return discriminant and the
        // postcondition VC came back satisfiable (unknown); the positive
        // `is_ok`/single-negation form grounds and PROVES exactly as the
        // `!matches!` sibling does. `!(G)` for the crown_deep `G = (A) == (B)`
        // is `!((A) == (B))`, parser-identical to the sibling's `(A) != (B)`
        // (`!=` and `!(==)` both lower to `Not(Eq(..))`), so the len-witness
        // coverage/pins fire the same. SOUND: still fail-closed — an ungroundable
        // shape only fails to prove.
        let text = format!("!(({result_text}.is_ok()) && (!({})))", g.text);
        if contract_lower_debug() {
            eprintln!(
                "TRUST_MATCH_ENSURES_DEBUG lower_ok_implies_match RECOGNIZED \
                 (match-wrapper `Ok(c) => G, Err(_) => true`) -> `{text}`"
            );
        }
        // Same variable population as the `lower_matches_idiom` sibling above:
        // the discriminant probe `result.is_ok()` (MathematicalInt domain) merged
        // with the guard's own lowered domains — the formula ranges over exactly
        // those variables, so the certified-monitor domain set is identical.
        Some(LoweredExpr {
            text,
            ty: LoweredExprTy::Bool,
            variable_domains: merge_variable_domains(
                synthetic_variable_domains(
                    &format!("{result_text}.is_ok()"),
                    TrustContractPropositionDomain::MathematicalInt,
                )?,
                g.variable_domains,
            )?,
        })
    }

    /// True iff `pat` is the non-`Ok` complement of an exhaustive `Result` match
    /// whose other arm is `Ok(<bind>)`: either the bare wildcard `_`, or an
    /// `Err(..)` tuple-struct pattern confirmed via the `ResultErr` lang item
    /// (never a name match). The `Err` arm's inner binding is irrelevant — the
    /// arm body is the literal `true` regardless — so any `Err(_)`/`Err(e)`/
    /// `Err(..)` shape qualifies. Anything else REJECTS (fail-closed).
    fn is_err_or_wild_pat(&self, pat: &'tcx Pat<'tcx>) -> bool {
        match &pat.kind {
            PatKind::Wild => true,
            PatKind::TupleStruct(qpath, _, _) => self.is_result_err_variant(qpath, pat.hir_id),
            _ => false,
        }
    }

    /// True iff `qpath` (a tuple-struct PATTERN path at `hir_id`) resolves to the
    /// `Result::Err` variant, confirmed against the `ResultErr` lang item. Mirror
    /// of `is_result_ok_variant`.
    fn is_result_err_variant(&self, qpath: &QPath<'tcx>, hir_id: HirId) -> bool {
        let Some(err_variant) = self.tcx.lang_items().result_err_variant() else {
            return false;
        };
        match self.typeck_results.qpath_res(qpath, hir_id) {
            Res::Def(DefKind::Ctor(CtorOf::Variant, _), ctor_def_id) => {
                self.tcx.parent(ctor_def_id) == err_variant
            }
            Res::Def(DefKind::Variant, variant_def_id) => variant_def_id == err_variant,
            _ => false,
        }
    }

    /// Whether `expr` is the ensures RESULT binding whose type is the std/core
    /// `Option` ADT — possibly behind transparent `Type`/`DropTemps` wrappers and
    /// an autoref/deref (the `&Option` closure param is deref'd for
    /// `unwrap(self)` and autoref'd for `is_none(&self)`). Gates the `Option`
    /// accessor lowering below to the RETURN value only (fail-closed: any other
    /// receiver, or a non-`Option` type, rejects). The `Option` identity is the
    /// diagnostic item — never a name match — so a look-alike user enum cannot
    /// be admitted.
    fn receiver_is_result_option(&self, expr: &'tcx Expr<'tcx>) -> bool {
        let Some(result_binding) = self.result_binding else {
            return false;
        };
        let mut base = expr;
        loop {
            match &base.kind {
                ExprKind::Type(inner, _)
                | ExprKind::DropTemps(inner)
                | ExprKind::Use(inner, _)
                | ExprKind::Unary(UnOp::Deref, inner) => base = inner,
                _ => break,
            }
        }
        if !expr_is_local_path(base, result_binding) {
            return false;
        }
        self.typeck_results
            .expr_ty(base)
            .peel_refs()
            .ty_adt_def()
            .is_some_and(|adt| self.tcx.is_diagnostic_item(rustc_span::sym::Option, adt.did()))
    }

    /// The dotted name of a field-projection base — a local variable
    /// (parameter/capture), a nested field of one, or a CONSTANT index into a
    /// builtin fixed-length array field — WITHOUT requiring it to be a scalar
    /// (the base is a struct/aggregate; only the projected leaf is scalar).
    /// `p` → `"p"`, `p.inner` → `"p.inner"`, so `p.value` lowers to `"p.value"`;
    /// `self.cols[0]` → `"self.<cols idx>[0]"`. Builtin auto-derefs a base picks
    /// up from typeck ADJUSTMENTS (a `&self` receiver) are made explicit as
    /// postfix `*` markers (`self.scale` on `&self` → `"self*.2"`), matching the
    /// MIR place render — see `append_builtin_deref_markers`.
    fn lower_projection_base(&self, expr: &'tcx Expr<'tcx>) -> Option<String> {
        match &expr.kind {
            ExprKind::Path(QPath::Resolved(None, path)) => {
                if let Res::Local(local_id) = path.res {
                    if path.segments.len() == 1 {
                        // Trust: a `matches!`-arm PATTERN BINDING as a projection
                        // base (`Ok(c) if c.entailment.premises.len() != ..`):
                        // substitute the Ok-payload text, exactly as
                        // `lower_path_expr` already does for a scalar bind read.
                        // Within the guard the binding denotes the corresponding
                        // payload component of the matched scrutinee, so its
                        // projections must lower rooted at `result.unwrap()`
                        // (-> the spec parser's `_0__value…` terms, classified
                        // SPEC-MODEL by `is_spec_model_var` and routed to the
                        // fail-closed SpecModelUngrounded when ungroundable).
                        // Without the substitution the guard minted a FREE var
                        // named after the source binding (`c.0.1` — probe P6),
                        // which is NOT spec-model-shaped: once `_0__discr` grounds
                        // (Result-return grounding), such a predicate would reach
                        // a refutable VC whose havoc'd `c.*` terms false-FAIL it.
                        // Checked BEFORE the result-binding arm, mirroring
                        // `lower_path_expr` (binds are distinct locals anyway).
                        if let Some((_, text)) =
                            self.pat_bindings.iter().find(|(id, _)| *id == local_id)
                        {
                            return Some(text.clone());
                        }
                        // Trust: the ensures RESULT binding as a projection base
                        // (`#[ensures(|ret| ret.0 == ret.1)]` over a tuple return).
                        // Emit the canonical result token so `<result>.i` unifies
                        // with the return value's i-th component (`_0.i`) instead of
                        // rejecting the whole predicate as unsupported. Over-
                        // refutation audit defect #2. SOUND: a free projected term
                        // the VC layer binds to the return place; can only fail to
                        // prove, never vacuously prove.
                        if Some(local_id) == self.result_binding {
                            return Some(ENSURES_RESULT_BINDING.to_string());
                        }
                        // A `matches!`-arm pattern BIND (`Ok(c) if c.0 <= 1.0`)
                        // must not leak its bare source name as a projection
                        // base: the substituted payload text is not a
                        // projectable base, and the bare `c` would be bound BY
                        // NAME to any same-named body local — a postcondition
                        // proved against the WRONG value (round-13). Reject the
                        // clause (fail-closed; the un-projected bind keeps its
                        // substitution in `lower_path_expr`).
                        if self.pat_bindings.iter().any(|(id, _)| *id == local_id) {
                            return None;
                        }
                        return Some(path.segments[0].ident.name.to_string());
                    }
                }
                // Trust: the SIGNATURE-form result binding as a projection base
                // (`#[ensures(result.coeff <= degree)]`). The arm above matches
                // only the CLOSURE form, whose `ret` is a real local; written in
                // signature form `result` resolves to no local at all, so the
                // base lowered to `None` and the whole predicate was rejected as
                // "unsupported contract predicate expression".
                //
                // That is why a clause had to choose: the closure form is proved
                // by the native lane but can never be kernel-cited, and the
                // signature form can be cited but was not lowered, so citing one
                // cost its native obligations. Emitting the canonical token here
                // lets the SAME clause be both.
                //
                // SOUND, for the reason the closure arm already gives: this is a
                // free projected term the VC layer binds to the return place, so
                // it can only fail to prove, never vacuously prove. Restricted to
                // the exact single-segment identifier `result`, which
                // `trust_contracts` reserves.
                if path.segments.len() == 1
                    && path.segments[0].ident.name.as_str() == ENSURES_RESULT_BINDING
                {
                    return Some(ENSURES_RESULT_BINDING.to_string());
                }
                None
            }
            ExprKind::Field(base, _field_ident) => {
                let base_text = self.lower_projection_base(base)?;
                // Trust: builtin auto-deref of the base (a `&self` receiver) is
                // part of the MIR place — make it explicit HERE, where the base
                // text is consumed by a projection, so a bare path in a
                // non-projection position never picks up a stray marker from
                // unrelated adjustment records.
                let base_text = self.append_builtin_deref_markers(base, base_text)?;
                // Use the RESOLVED numeric field INDEX, not the source field name.
                // The MIR `Field(i)` place — and `place_to_var_name` — name every
                // field (tuple AND struct) positionally by index `.i`, so a struct
                // field `p.value` must lower to `<base>.<idx>` to unify with the
                // body (`_0.0`), not `<base>.value`. Tuple fields already carry a
                // numeric name, so this is index-identical for them. Over-refutation
                // audit defect #2 (struct-field half). `opt_field_index` returns
                // None for a non-ADT/tuple field access we cannot resolve — reject
                // (fail-closed) rather than emit a mismatched name.
                let idx = self.typeck_results.opt_field_index(expr.hir_id)?;
                Some(format!("{base_text}.{}", idx.as_usize()))
            }
            // Trust: a CONSTANT index into a builtin fixed-length array, in a
            // projection chain (`#[requires(self.cols[0].x <= 1.0e30)]`). Lowers
            // to `<base>[k]` — the contract-side canonical spelling; the vcgen
            // float lane canonicalizes the body place's `[k;min=L]` render to
            // `[k]` before matching. Admitted ONLY when every piece is
            // statically pinned down (anything else rejects, fail-closed —
            // never a guess):
            //   * typeck did NOT resolve this indexing to an `Index::index`
            //     method call — overloaded indexing (Vec, user impls) is a CALL
            //     in MIR, not the Index place projection this name claims;
            //   * the indexed base is a builtin `ty::Array` after peeling
            //     references, with a KNOWN length (a const-generic length or a
            //     slice has no static length to check the index against);
            //   * the index is a plain integer literal strictly below that
            //     length (an out-of-range literal names no element; a cast or
            //     runtime index is not a stable name).
            // SOUND: the emitted text either unifies with the body's
            // identically-indexed place or stays a free term the VC layer never
            // binds — it can only fail to prove, never vacuously prove; the
            // length check only ever REJECTS.
            ExprKind::Index(base, index, _) => {
                let base_text = self.lower_projection_base(base)?;
                let base_text = self.append_builtin_deref_markers(base, base_text)?;
                // INVARIANT this arm rests on: this rustc tree has NO builtin-
                // index fast path in typeck's `try_index_step` — ALL indexing is
                // initially recorded as the overloaded `Index::index` call, and
                // only writeback's `fix_index_builtin_expr` (rustc_hir_typeck/
                // src/writeback.rs) strips the method record + Borrow adjustment
                // for true builtin array/slice indexing. The gate below is
                // therefore meaningful ONLY over post-writeback typeck results
                // (which `tcx.typeck_body` gives us); if writeback's conditions
                // ever narrow, builtin indexing would re-appear as a method call
                // here and every indexed contract clause would reject —
                // fail-closed, but silently feature-dead.
                if self.typeck_results.is_method_call(expr) {
                    return None;
                }
                use rustc_middle::ty;
                let base_ty = self.typeck_results.expr_ty(base).peel_refs();
                let ty::Array(_, len) = base_ty.kind() else {
                    return None;
                };
                let len = len.try_to_target_usize(self.tcx)?;
                // The literal may sit behind the same value-transparent wrappers
                // the other arms look through.
                let mut index = *index;
                while let ExprKind::Type(inner, _)
                | ExprKind::DropTemps(inner)
                | ExprKind::Use(inner, _) = &index.kind
                {
                    index = inner;
                }
                let ExprKind::Lit(lit) = &index.kind else {
                    return None;
                };
                let LitKind::Int(value, _) = lit.node else {
                    return None;
                };
                let value = value.get();
                if value >= u128::from(len) {
                    return None;
                }
                Some(format!("{base_text}[{value}]"))
            }
            // Trust: an AUTHORED explicit deref base (`(*self).cols[0].x`) —
            // the exact prefix spelling this lane itself emits for the
            // implicit-deref case, so rejecting it from the author is a
            // confusing asymmetry. Same head-only discipline as the implicit
            // markers: only a pure deref-wrap of the chain head qualifies (a
            // mid-chain explicit deref has the same gate blast radius as an
            // implicit one and rejects the clause here).
            ExprKind::Unary(UnOp::Deref, inner) => {
                let inner_text = self.lower_projection_base(inner)?;
                if !text_is_deref_wrapped_head(&inner_text) {
                    return None;
                }
                Some(format!("(*{inner_text})"))
            }
            ExprKind::Type(inner, _) | ExprKind::DropTemps(inner) | ExprKind::Use(inner, _) => {
                self.lower_projection_base(inner)
            }
            _ => None,
        }
    }

    /// Make the builtin auto-derefs a projection BASE picks up from typeck
    /// ADJUSTMENTS explicit in the emitted spec text. `self.scale` on a `&self`
    /// receiver derefs the pointer before the field projection — the MIR place
    /// is `(*self).2` and `place_to_var_name` renders the pointee as `self*` —
    /// so the contract text must carry the deref or the two sides silently
    /// never unify (the bound becomes a free term and the obligation is KEPT:
    /// sound but useless). The TEXT form is the PREFIX spelling `(*self)` —
    /// the only spelling the spec parser's grammar accepts (its unary-`*` arm
    /// lowers `(*self).2` to the postfix-star VAR NAME `self*.2`; a literal
    /// postfix `self*` in text tokenizes as multiplication and rejects). One
    /// `(*...)` wrap per builtin deref step, in adjustment order. REJECTS
    /// (fail-closed):
    ///   * an OVERLOADED deref — `Deref::deref` is a method CALL in MIR, not a
    ///     `Deref` place projection, so the marker would name a place that does
    ///     not exist;
    ///   * a pin deref, and every other adjustment kind (borrows, pointer
    ///     coercions, never-to-any, reborrows) — they change the value's shape,
    ///     so the base text no longer names the adjusted value.
    /// The ensures RESULT binding is exempt from marker emission: `result`
    /// already denotes the return VALUE (the closure param is a reference and
    /// the VC layer binds the token to the return place itself), so its builtin
    /// deref steps are absorbed by the token — any other adjustment kind on it
    /// still rejects. Adjustments are read off the base expr node itself (where
    /// typeck's `check_field`/index lowering record them); a marker recorded
    /// elsewhere is simply missed, which only under-unifies (fail-closed).
    fn append_builtin_deref_markers(&self, base: &'tcx Expr<'tcx>, text: String) -> Option<String> {
        use rustc_middle::ty::adjustment::{Adjust, DerefAdjustKind};
        let adjustments = self.typeck_results.expr_adjustments(base);
        if adjustments.is_empty() {
            return Some(text);
        }
        if adjustments
            .iter()
            .any(|adjustment| !matches!(adjustment.kind, Adjust::Deref(DerefAdjustKind::Builtin)))
        {
            return None;
        }
        if self.result_binding.is_some_and(|binding| expr_is_local_path(base, binding)) {
            return Some(text);
        }
        // A `matches!`/match-arm Ok-payload PATTERN BINDING base (`c` in
        // `Ok(c) if c.entailment.premises.len() != …` / `Ok(c) => …`) is exempt
        // for the SAME reason as the result binding: its substituted text is the
        // Ok-payload term `result.unwrap()…`, which already denotes the return
        // value's OWNED `Ok` payload (`_0__value…`). Under match ergonomics the
        // closure sees `r: &Result`, so the binding is `&Payload` and a field
        // projection off it records a builtin deref — but that deref is an
        // artifact of the by-reference closure parameter, NOT of the owned
        // returned value the spec term names. Emitting a `(*…)` marker here would
        // desync the contract text from the `_0__value…_len` name the len-witness
        // grounding pins from the owned MIR construction (a bug main's marker
        // pass introduced over b62, which projected the payload binding without a
        // marker). Only an all-builtin-deref adjustment list reaches this point
        // (a shape-changing adjustment already returned None above), so the
        // exemption stays fail-closed: an unpinned term can only fail to prove.
        if let ExprKind::Path(QPath::Resolved(None, path)) = &base.kind
            && let Res::Local(local_id) = path.res
            && self.pat_bindings.iter().any(|(id, _)| *id == local_id)
        {
            if contract_lower_debug() {
                eprintln!(
                    "TRUST_MATCH_ENSURES_DEBUG append_builtin_deref_markers EXEMPT \
                     Ok-payload pat-binding base -> `{text}` (marker suppressed)"
                );
            }
            return Some(text);
        }
        // HEAD-only discipline: the assumption gate admits a deref marker ONLY
        // immediately after the chain head (`self*.2`), and rejects a mid-chain
        // star with a WHOLE-SET drop — one exotic conjunct (`self.bx[0].x` over
        // a `&`-typed field, a `&&T` base) would silently disable every other
        // assumed precondition of the function. The frontend knows the chain
        // shape at lowering time, so reject HERE (the one clause dies as
        // Unsupported, localized and attributed) rather than emit a name whose
        // crate-side rejection has function-wide blast radius.
        if !text_is_deref_wrapped_head(&text) {
            return None;
        }
        let mut text = text;
        for _ in adjustments {
            text = format!("(*{text})");
        }
        Some(text)
    }

    /// If `expr` is a bare path to an Ok-payload PATTERN BINDING (collected by
    /// `collect_ok_pattern_bindings` for a recognized `matches!(r, Ok(<bind>) if …)`
    /// arm), return its substituted payload text (`result.unwrap()` for `Ok(c)`, or
    /// `result.unwrap().__trust_ok_i` for a tuple component). Else None. Used by the
    /// sign-predicate arm to accept a numeric-but-non-scalar payload receiver (e.g. a
    /// `Rat` `c` in `Ok(c) if c.is_positive()`) whose value-typed lowering would
    /// otherwise reject at the `recv.ty != Int` gate. Peels the value-transparent
    /// `Type`/`DropTemps`/`Use` wrappers first (mirrors `lower_expr_text`).
    fn ok_payload_binding_text(&self, expr: &'tcx Expr<'tcx>) -> Option<String> {
        let mut e = expr;
        loop {
            match &e.kind {
                ExprKind::Type(inner, _) | ExprKind::DropTemps(inner) | ExprKind::Use(inner, _) => {
                    e = inner
                }
                ExprKind::Path(QPath::Resolved(None, path)) => {
                    let Res::Local(local_id) = path.res else {
                        return None;
                    };
                    return self
                        .pat_bindings
                        .iter()
                        .find(|(id, _)| *id == local_id)
                        .map(|(_, text)| text.clone());
                }
                _ => return None,
            }
        }
    }

    /// Lower a path that names a `const` or associated `const` to the EXACT
    /// value the program's own definition has.
    ///
    /// Two-language design §1 (literal program objects): the clause must denote
    /// THE constant the code uses, never a re-declared twin. That is why the
    /// value is obtained by asking rustc's own const evaluator to evaluate the
    /// resolved `DefId` — the same evaluation the program itself gets — rather
    /// than by pattern-matching a spelling such as `u32::MAX`. A change to the
    /// const's definition therefore changes the contract with it, and there is
    /// nothing to keep in sync.
    ///
    /// Fails closed (returns `None`, which makes the whole predicate
    /// `Unsupported` and a hard build error) whenever the value is not an exact
    /// integer or bool: a generic or otherwise unevaluable const, a reference/
    /// aggregate/float const, or an integer too wide for the contract grammar's
    /// `i128` literal token. Nothing is ever substituted on a guess.
    fn lower_const_path_expr(
        &self,
        expr: &'tcx Expr<'tcx>,
        qpath: &QPath<'tcx>,
    ) -> Option<LoweredExpr> {
        let Res::Def(DefKind::Const { .. } | DefKind::AssocConst { .. }, def_id) =
            self.typeck_results.qpath_res(qpath, expr.hir_id)
        else {
            return None;
        };

        // The const must be fully concrete here. A contract on a generic
        // function may name `T::LIMIT`, which has no single value at this
        // boundary; refuse rather than pick an instantiation.
        let args = self.typeck_results.node_args(expr.hir_id);
        if args.has_non_region_param() || args.has_non_region_infer() || args.has_aliases() {
            return None;
        }

        let typing_env = ty::TypingEnv::fully_monomorphized();
        let unevaluated = rustc_middle::mir::UnevaluatedConst::new(def_id, args);
        let value = self.tcx.const_eval_resolve(typing_env, unevaluated, expr.span).ok()?;
        lowered_constant_expr(self.tcx, value, self.typeck_results.expr_ty(expr))
    }

    /// Trust: inline a call to a TRANSPARENT helper appearing inside a contract
    /// predicate, so that a postcondition may name another function at all.
    ///
    /// The inline is faithful only if the callee's value is a closed function of
    /// its arguments alone. Every gate below establishes a piece of exactly that
    /// and is fail-closed — a `None` leaves the whole predicate unparseable
    /// (`SpecEnsuresUnparseable`), never a guess:
    ///
    /// 1. A free `fn`. `DefKind::Fn` rejects tuple-struct and enum-variant
    ///    constructors, trait/inherent methods (no receiver, so no
    ///    impl-resolution ambiguity and no `&mut self`), closures, and calls
    ///    through a function pointer.
    /// 2. LOCAL, so an HIR body exists to inline at all.
    /// 3. NON-GENERIC. Under a type parameter the body's arithmetic depends on
    ///    the instantiation, and the emitted text would not fix the sort the
    ///    proposition is read at.
    /// 4. A body that is a single tail expression with NO statements. A `let`, an
    ///    assignment or an early `return` is a computation this vocabulary cannot
    ///    represent, and admitting one would silently drop it.
    /// 5. Arity match, and every parameter a plain by-value, non-`mut` binding
    ///    (no `ref`, no subpattern) — the binding must denote precisely the
    ///    actual that replaces it.
    /// 6. Every path in the body resolves to one of those parameters or to a
    ///    `const`. This is the load-bearing gate: an unbound local would lower to
    ///    a free variable named in the CALLER's namespace and could capture an
    ///    unrelated term of the same name, and a `static` is not a function of
    ///    the arguments at all.
    ///
    /// PURITY needs no separate check — it follows from the fragment. The
    /// recursive `lower_expr_text` admits only literals, paths, casts and
    /// arithmetic/comparison operators, so nothing with an effect can lower.
    ///
    /// SOUND: the result is the callee's own expression over the caller's actual
    /// terms, in the same vocabulary the caller would have written by hand. It
    /// introduces no free variable, so unlike the `__len`/`__sign` lanes there is
    /// nothing for the VC layer to ground, and it cannot vacuously prove.
    fn lower_inlined_call(
        &self,
        callee: &'tcx Expr<'tcx>,
        args: &'tcx [Expr<'tcx>],
    ) -> Option<LoweredExpr> {
        let outcome = self.lower_inlined_call_reasoned(callee, args);
        if crate::trust_verify::trust_env_var_present("TRUST_CONTRACT_INLINE_TRACE") {
            match &outcome {
                Ok(lowered) => {
                    eprintln!("TRUST_CONTRACT_INLINE_TRACE: inlined -> `{}`", lowered.text)
                }
                Err(reason) => {
                    eprintln!("TRUST_CONTRACT_INLINE_TRACE: refused ({reason})")
                }
            }
        }
        outcome.ok()
    }

    /// Resolve the callee and hand the shared core its ALREADY-LOWERED actual
    /// texts. Two spellings reach that core — this HIR arm and the native
    /// grammar's text pre-pass (`expand_contract_helper_calls`) — and both go
    /// through [`inline_helper_call_reasoned`], so the two can never inline a
    /// helper under different gates.
    fn lower_inlined_call_reasoned(
        &self,
        callee: &'tcx Expr<'tcx>,
        args: &'tcx [Expr<'tcx>],
    ) -> Result<LoweredExpr, &'static str> {
        let ExprKind::Path(qpath) = &callee.kind else {
            return Err("callee is not a path");
        };
        let Res::Def(DefKind::Fn, def_id) = self.typeck_results.qpath_res(qpath, callee.hir_id)
        else {
            return Err("callee is not a free `fn` (ctor, method, closure or fn-pointer)");
        };
        let Some(local) = def_id.as_local() else {
            return Err("callee is not local (no HIR body to inline)");
        };

        // The emitted helper body is text, so any Rust coercion applied at the
        // call boundary would otherwise disappear. Require each actual's
        // original and adjusted type to be byte-for-byte the formal type. The
        // ordinary HIR resolver has already authenticated the callee `Res`;
        // this gate authenticates the exact instantiation that the text stands
        // for.
        let signature = self.tcx.fn_sig(def_id).instantiate_identity().skip_binder();
        if signature.inputs().len() != args.len() {
            return Err("arity mismatch");
        }
        for (actual, formal) in args.iter().zip(signature.inputs()) {
            if self.typeck_results.expr_ty(actual) != *formal
                || self.typeck_results.expr_ty_adjusted(actual) != *formal
            {
                return Err("an actual argument is not exactly the formal Rust type");
            }
        }

        // The actuals are lowered in the CALLER's scope, and their domains
        // would otherwise be dropped: the core splices them in as text.
        let mut actual_texts = Vec::with_capacity(args.len());
        let mut variable_domains = Vec::new();
        for arg in args {
            let Some(lowered) = self.lower_expr_text(arg) else {
                return Err("an actual argument does not lower");
            };
            actual_texts.push(lowered.text);
            variable_domains.extend(lowered.variable_domains);
        }

        let mut lowered =
            inline_helper_call_reasoned(self.tcx, local, &actual_texts, self.inline_depth)?;
        if lowered_expr_ty(self.tcx, signature.output()) != Some(lowered.ty) {
            return Err("the lowered helper result does not retain its Rust result type");
        }
        variable_domains.extend(lowered.variable_domains);
        lowered.variable_domains = variable_domains;
        Ok(lowered)
    }

    fn lower_path_expr(&self, expr: &'tcx Expr<'tcx>, qpath: &QPath<'tcx>) -> Option<LoweredExpr> {
        let QPath::Resolved(None, path) = qpath else {
            return None;
        };
        let Res::Local(local_id) = path.res else {
            return None;
        };
        if path.segments.len() != 1 {
            return None;
        }
        // A reference to a `matches!`-arm pattern binding (e.g. `c` in
        // `Ok(c) if c.is_positive()`) lowers to the substituted Ok-payload text.
        // The bind stands for a component of the Ok value, so it is value-typed
        // (Int) for the spec parser. Checked BEFORE the result-binding guard, since
        // these binds are distinct locals from the result binding anyway.
        if let Some((_, text)) = self.pat_bindings.iter().find(|(id, _)| *id == local_id) {
            return lowered_variable_expr(
                self.tcx,
                text.clone(),
                self.typeck_results.expr_ty(expr),
            );
        }
        if Some(local_id) == self.result_binding {
            return None;
        }
        // Trust: a shared-ref SCALAR parameter compared by value (`s <= 1.0`
        // with `s: &f64`) — typeck records builtin auto-deref ADJUSTMENTS on
        // the bare path and the MIR body reads the pointee `(*s)`, which the
        // extractor renders `s*`. Emit the PREFIX deref spelling `(*s)` (one
        // `(*...)` wrap per builtin deref step, in adjustment order — matching
        // `append_builtin_deref_markers`; the spec parser's unary-`*` arm
        // lowers it to the postfix-star var name `s*`, while a literal postfix
        // `s*` in text tokenizes as multiplication) and type the term by the
        // ADJUSTED (pointee) type, so the contract fact names the value the
        // body actually reads. ONLY an all-builtin-deref adjustment list
        // qualifies: an overloaded deref is a method call in MIR (no such
        // place), and a shape-changing adjustment (borrow / pointer coercion /
        // ...) means the bare name no longer denotes the adjusted value — both
        // fall through to the unadjusted lowering below, where a
        // reference-typed `expr_ty` rejects in `lowered_expr_ty` (fail-closed)
        // and a receiver-position autoref keeps its existing by-value lowering.
        // A path with NO adjustments is untouched, so a plain by-value param
        // can never pick up a stray marker.
        let adjustments = self.typeck_results.expr_adjustments(expr);
        if !adjustments.is_empty()
            && adjustments.iter().all(|adjustment| {
                use rustc_middle::ty::adjustment::{Adjust, DerefAdjustKind};
                matches!(adjustment.kind, Adjust::Deref(DerefAdjustKind::Builtin))
            })
        {
            let target = adjustments.last()?.target;
            let mut text = path.segments[0].ident.name.to_string();
            for _ in adjustments {
                text = format!("(*{text})");
            }
            return lowered_variable_expr(self.tcx, text, target);
        }
        lowered_variable_expr(
            self.tcx,
            path.segments[0].ident.name.to_string(),
            self.typeck_results.expr_ty(expr),
        )
    }

    fn lower_deref_expr(
        &self,
        expr: &'tcx Expr<'tcx>,
        inner: &'tcx Expr<'tcx>,
    ) -> Option<LoweredExpr> {
        let rust_ty = self.typeck_results.expr_ty(expr);
        // `*result` — the dereferenced return value → the result term.
        if let Some(result_binding) = self.result_binding {
            if expr_is_local_path(inner, result_binding) {
                return lowered_variable_expr(
                    self.tcx,
                    ENSURES_RESULT_BINDING.to_string(),
                    rust_ty,
                );
            }
        }
        // Trust: `*a` where `a` is a reference-typed PARAMETER (`a: &T`). The MIR
        // body reads `(*a)` and the extractor names that pointee `a*` (see
        // `place_to_var_name` for a `Deref` projection); the VC already models it
        // (a guarded `*a + 1` body proves). Emit the deref VERBATIM as prefix
        // `*a` text — the crate-side spec parser (`spec_parse::parse_unary`)
        // lowers a prefix `*a` to `Var("a*")`, matching the body naming — so
        // `#[requires(*a < 10)]` / `#[ensures]` over a `&T` parameter connect to
        // the body instead of failing as an unsupported predicate. Only a plain
        // single-segment local path that is NOT the result binding qualifies (the
        // result case returned above); everything else rejects (fail-closed —
        // never a guess). SOUND: `a*` is a free term until the VC layer binds it
        // to the parameter's pointee, so the predicate can only fail to prove,
        // never vacuously prove. `inner` may be wrapped in transparent
        // `Type`/`DropTemps`/`Use` nodes (as in `lower_projection_base`), so
        // strip them before matching the local path.
        let mut base = inner;
        while let ExprKind::Type(e, _) | ExprKind::DropTemps(e) | ExprKind::Use(e, _) = &base.kind {
            base = e;
        }
        if let ExprKind::Path(QPath::Resolved(None, path)) = &base.kind {
            if let Res::Local(local_id) = path.res {
                if path.segments.len() == 1 && Some(local_id) != self.result_binding {
                    // Trust: `*c` where `c` is a `matches!`-arm PATTERN BINDING —
                    // the natural spelling of an integer-payload guard
                    // (`matches!(r, Ok(c) if *c >= 0)`: with the `&Result<..>`
                    // scrutinee, match ergonomics bind `c: &i64`, so the source
                    // MUST deref to compare). Two cases, split on the COMPUTED
                    // binding mode (`pat_binding_modes` — post-ergonomics):
                    //   * ByRef (ergonomic or explicit `ref`): `c` is a reference
                    //     INTO the matched Ok-payload component, so `*c` denotes
                    //     EXACTLY the value the substitution text stands for
                    //     (`result.unwrap()[…]`) — emit it, mirroring
                    //     `lower_path_expr`'s bare-bind substitution (which reads
                    //     the same value through the ref the spec logic elides).
                    //   * ByValue: `c` IS the payload component, so `*c` derefs
                    //     INTO it (the payload is itself a pointer/handle) — a
                    //     value the payload term does NOT denote. No modeled text
                    //     exists: REJECT (fail-closed, never a guess).
                    // Never fall through to the parameter-deref emission below:
                    // that would emit `*c` VERBATIM, minting the free
                    // NON-spec-model var `c*` (the P6 free-var class), which
                    // becomes a refutable havoc'd VC — false-FAILED — once
                    // `_0__discr` grounds via the Result-return grounding.
                    if let Some((_, text)) =
                        self.pat_bindings.iter().find(|(id, _)| *id == local_id)
                    {
                        return match self.typeck_results.pat_binding_modes().get(local_id) {
                            Some(BindingMode(ByRef::Yes(..), _)) => {
                                lowered_variable_expr(self.tcx, text.clone(), rust_ty)
                            }
                            _ => None,
                        };
                    }
                    let name = path.segments[0].ident.name;
                    return lowered_variable_expr(self.tcx, format!("*{name}"), rust_ty);
                }
            }
        }
        None
    }
}

/// True iff `expr` is the boolean literal `value`. The `matches!` arm bodies are
/// the bare literals `=> true` / `=> false`; we also look through transparent
/// type-ascription / drop-temps / capture-use wrappers to stay robust.
/// Env gate for the contract-lowering decision-point trace. `TRUST_E9_DEBUG`
/// (already set by the verification-campaign harness) surfaces it alongside the
/// verifier's E9 discharge trace so a single rebuild confirms which lowering
/// path fired; `TRUST_CONTRACT_LOWER_DEBUG` enables it in isolation.
fn contract_lower_debug() -> bool {
    crate::trust_verify::trust_env_var_present("TRUST_E9_DEBUG")
        || crate::trust_verify::trust_env_var_present("TRUST_CONTRACT_LOWER_DEBUG")
}

fn expr_is_bool_lit(expr: &Expr<'_>, value: bool) -> bool {
    match &expr.kind {
        ExprKind::Lit(lit) => matches!(lit.node, LitKind::Bool(b) if b == value),
        ExprKind::Type(inner, _) | ExprKind::DropTemps(inner) | ExprKind::Use(inner, _) => {
            expr_is_bool_lit(inner, value)
        }
        _ => false,
    }
}

fn expr_is_local_path(expr: &Expr<'_>, expected: HirId) -> bool {
    match &expr.kind {
        ExprKind::Path(QPath::Resolved(None, path)) => {
            path.segments.len() == 1
                && matches!(path.res, Res::Local(local_id) if local_id == expected)
        }
        ExprKind::Type(inner, _) | ExprKind::DropTemps(inner) | ExprKind::Use(inner, _) => {
            expr_is_local_path(inner, expected)
        }
        _ => false,
    }
}

/// Whether an emitted base text is a bare chain HEAD — a plain identifier,
/// possibly under pure `(*...)` deref wraps (`self`, `(*self)`, `(*(*m))`) —
/// i.e. a deref marker appended to it lands IMMEDIATELY after the head, the
/// only star position the crate-side assumption gate admits. Any projection
/// token in the core (`.`, `[`, a leftover paren or star) means a wrap would
/// mint a MID-CHAIN deref name, which the gate rejects with a whole-set drop.
fn text_is_deref_wrapped_head(text: &str) -> bool {
    let mut core = text;
    while let Some(inner) = core.strip_prefix("(*").and_then(|s| s.strip_suffix(')')) {
        core = inner;
    }
    !core.is_empty() && !core.contains(['.', '[', '(', ')', '*'])
}

#[cfg(test)]
fn lowered_contract_text(text: String) -> TrustContractPredicateKind {
    lowered_contract_text_with_domains(text, &[])
}

fn lowered_contract_text_with_domains(
    text: String,
    variable_domains: &[LoweredVariableDomain],
) -> TrustContractPredicateKind {
    lowered_contract_text_with_domains_for_class(text, variable_domains, PropositionClass::Bool)
}

/// The formula sort a contract proposition domain denotes. Shared so the
/// re-parse reconciliation above and the domain-to-sort mappings elsewhere cannot
/// drift on what a float domain means.
fn proposition_domain_sort(domain: TrustContractPropositionDomain) -> trust_types::Sort {
    match domain {
        TrustContractPropositionDomain::Bool => trust_types::Sort::Bool,
        TrustContractPropositionDomain::Float { width } => {
            trust_types::Sort::float_for_width(width).unwrap_or(trust_types::Sort::BitVec(width))
        }
        TrustContractPropositionDomain::MathematicalInt
        | TrustContractPropositionDomain::PointerSizedInt { .. }
        | TrustContractPropositionDomain::MachineInt { .. } => trust_types::Sort::Int,
    }
}

fn lowered_contract_text_with_domains_for_class(
    text: String,
    variable_domains: &[LoweredVariableDomain],
    expected_class: PropositionClass,
) -> TrustContractPredicateKind {
    let canonical = Symbol::intern(&format!("{LOWERED_COMPILER_CONTRACT_PREFIX}{text}"));
    // This re-parses the canonical TEXT, so it gets a fresh binary64 float
    // literal and must reconcile it the same way every other consumer does.
    // Without this the proposition carried a binary64 constant against an `f32`
    // variable's domain, the sorts failed to merge, and the clause fell out as
    // Opaque — well-typed at the source and still never reaching a typed formula.
    let declared: BTreeMap<String, trust_types::Sort> = variable_domains
        .iter()
        .map(|variable| (variable.name.clone(), proposition_domain_sort(variable.domain)))
        .collect();
    if let Some(proposition) = trust_types::parse_spec_expr(&text)
        .map(|formula| reconcile_float_literal_formats(formula, &declared))
        .as_ref()
        .and_then(|formula| {
            query_proposition_from_formula(formula, variable_domains, expected_class)
        })
    {
        TrustContractPredicateKind::Typed { text: canonical, proposition }
    } else {
        TrustContractPredicateKind::Opaque { text: canonical }
    }
}

/// Copy the parser's supported structural vocabulary into the query-owned
/// proposition tree. Unsupported solver-only nodes stay opaque and therefore
/// can never mint certified-monitor authority.
fn query_proposition_from_formula(
    formula: &trust_types::Formula,
    variable_domains: &[LoweredVariableDomain],
    expected_class: PropositionClass,
) -> Option<TrustContractProposition> {
    let mut domains = FxHashMap::default();
    for variable in variable_domains {
        if domains.insert(variable.name.as_str(), variable.domain).is_some() {
            return None;
        }
    }

    let (proposition, sort) = query_proposition_from_formula_inner(formula, &domains)?;
    (sort.class() == expected_class).then_some(proposition)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum PropositionClass {
    Bool,
    Numeric,
}

/// The structural proposition sort, retaining the exact compiler-authenticated
/// machine domain whenever an expression contains a typed variable. Integer
/// literals have no intrinsic width or signedness and therefore carry `None`;
/// an adjacent typed operand may fix their domain, but two differently typed
/// variables must never be merged merely because both are numeric.
#[derive(Clone, Copy, PartialEq, Eq)]
enum PropositionSort {
    Bool,
    Numeric(Option<TrustContractPropositionDomain>),
}

impl PropositionSort {
    fn class(self) -> PropositionClass {
        match self {
            Self::Bool => PropositionClass::Bool,
            Self::Numeric(_) => PropositionClass::Numeric,
        }
    }
}

fn merge_numeric_sorts(
    lhs: PropositionSort,
    rhs: PropositionSort,
) -> Option<Option<TrustContractPropositionDomain>> {
    let (PropositionSort::Numeric(lhs), PropositionSort::Numeric(rhs)) = (lhs, rhs) else {
        return None;
    };
    match (lhs, rhs) {
        (Some(lhs), Some(rhs)) if lhs != rhs => None,
        (Some(domain), _) | (_, Some(domain)) => Some(Some(domain)),
        (None, None) => Some(None),
    }
}

fn query_proposition_from_formula_inner(
    formula: &trust_types::Formula,
    domains: &FxHashMap<&str, TrustContractPropositionDomain>,
) -> Option<(TrustContractProposition, PropositionSort)> {
    use TrustContractProposition as Proposition;
    use trust_types::Formula;

    let unary = |formula: &Formula| query_proposition_from_formula_inner(formula, domains);
    let binary = |lhs: &Formula, rhs: &Formula| Some((unary(lhs)?, unary(rhs)?));
    match formula {
        Formula::Bool(value) => Some((Proposition::Bool(*value), PropositionSort::Bool)),
        Formula::Int(value) => Some((Proposition::Int(*value), PropositionSort::Numeric(None))),
        Formula::UInt(value) => Some((Proposition::UInt(*value), PropositionSort::Numeric(None))),
        Formula::Var(name, _) => {
            let domain = *domains.get(name.as_str())?;
            let sort = if domain == TrustContractPropositionDomain::Bool {
                PropositionSort::Bool
            } else {
                PropositionSort::Numeric(Some(domain))
            };
            Some((Proposition::Var { name: Symbol::intern(name), domain }, sort))
        }
        Formula::SymVar(name, _) => {
            let text = name.as_str();
            let domain = *domains.get(text)?;
            let sort = if domain == TrustContractPropositionDomain::Bool {
                PropositionSort::Bool
            } else {
                PropositionSort::Numeric(Some(domain))
            };
            Some((Proposition::Var { name: Symbol::intern(text), domain }, sort))
        }
        Formula::Not(inner) => {
            let (inner, sort) = unary(inner)?;
            (sort == PropositionSort::Bool)
                .then_some((Proposition::Not(Box::new(inner)), PropositionSort::Bool))
        }
        Formula::And(terms) | Formula::Or(terms) => {
            let propositions = terms
                .iter()
                .map(|term| {
                    let (term, sort) = unary(term)?;
                    (sort == PropositionSort::Bool).then_some(term)
                })
                .collect::<Option<Vec<_>>>()?;
            Some((
                if matches!(formula, Formula::And(_)) {
                    Proposition::And(propositions)
                } else {
                    Proposition::Or(propositions)
                },
                PropositionSort::Bool,
            ))
        }
        Formula::Implies(lhs, rhs) => {
            let ((lhs, lhs_sort), (rhs, rhs_sort)) = binary(lhs, rhs)?;
            (lhs_sort == PropositionSort::Bool && rhs_sort == PropositionSort::Bool).then_some((
                Proposition::Implies(Box::new(lhs), Box::new(rhs)),
                PropositionSort::Bool,
            ))
        }
        Formula::Eq(lhs, rhs) => {
            let ((lhs, lhs_sort), (rhs, rhs_sort)) = binary(lhs, rhs)?;
            let compatible = (lhs_sort == PropositionSort::Bool
                && rhs_sort == PropositionSort::Bool)
                || merge_numeric_sorts(lhs_sort, rhs_sort).is_some();
            compatible
                .then_some((Proposition::Eq(Box::new(lhs), Box::new(rhs)), PropositionSort::Bool))
        }
        // Trust (SPEC-FLOAT-EQ-STRUCTURAL-1): the parser spells a `==` with a
        // float literal operand as IEEE `FpEq` (Rust `PartialEq` on floats, never
        // structural `=`). It is the same `Proposition::Eq` the arm above builds —
        // over float domains that proposition denotes `PartialEq`, and the static
        // lowering (`trust_mir_extract::trust_contract_proposition_to_formula`)
        // rebuilds `FpEq` from it — but only between two NUMERIC operands whose
        // domains agree, exactly like the IEEE ordering arms below.
        Formula::FpEq(lhs, rhs) => {
            let ((lhs, lhs_sort), (rhs, rhs_sort)) = binary(lhs, rhs)?;
            merge_numeric_sorts(lhs_sort, rhs_sort)?;
            Some((Proposition::Eq(Box::new(lhs), Box::new(rhs)), PropositionSort::Bool))
        }
        // The IEEE literal the spec parser builds for `1.0`. Carried by BITS,
        // which is what the proposition stores, so the round trip is exact
        // through both zeroes and any NaN payload.
        Formula::FpConst { bits, eb: 11, sb: 53 } => Some((
            Proposition::Float { bits: *bits as u64, width: 64 },
            PropositionSort::Numeric(Some(TrustContractPropositionDomain::Float { width: 64 })),
        )),
        Formula::FpConst { bits, eb: 8, sb: 24 } => Some((
            Proposition::Float { bits: *bits as u64, width: 32 },
            PropositionSort::Numeric(Some(TrustContractPropositionDomain::Float { width: 32 })),
        )),
        // The IEEE comparisons. Kept as their own arms rather than folded into
        // the integer ones below, because `merge_numeric_sorts` has to see two
        // FLOAT domains agree: a float compared against an integer domain is
        // ill-sorted and must decline, not silently pick one.
        Formula::FpLt(lhs, rhs)
        | Formula::FpLe(lhs, rhs)
        | Formula::FpGt(lhs, rhs)
        | Formula::FpGe(lhs, rhs) => {
            let ((lhs, lhs_sort), (rhs, rhs_sort)) = binary(lhs, rhs)?;
            merge_numeric_sorts(lhs_sort, rhs_sort)?;
            let proposition = match formula {
                Formula::FpLt(..) => Proposition::Lt(Box::new(lhs), Box::new(rhs)),
                Formula::FpLe(..) => Proposition::Le(Box::new(lhs), Box::new(rhs)),
                Formula::FpGt(..) => Proposition::Gt(Box::new(lhs), Box::new(rhs)),
                Formula::FpGe(..) => Proposition::Ge(Box::new(lhs), Box::new(rhs)),
                _ => unreachable!(),
            };
            Some((proposition, PropositionSort::Bool))
        }
        Formula::Lt(lhs, rhs)
        | Formula::Le(lhs, rhs)
        | Formula::Gt(lhs, rhs)
        | Formula::Ge(lhs, rhs) => {
            let ((lhs, lhs_sort), (rhs, rhs_sort)) = binary(lhs, rhs)?;
            merge_numeric_sorts(lhs_sort, rhs_sort)?;
            let proposition = match formula {
                Formula::Lt(..) => Proposition::Lt(Box::new(lhs), Box::new(rhs)),
                Formula::Le(..) => Proposition::Le(Box::new(lhs), Box::new(rhs)),
                Formula::Gt(..) => Proposition::Gt(Box::new(lhs), Box::new(rhs)),
                Formula::Ge(..) => Proposition::Ge(Box::new(lhs), Box::new(rhs)),
                _ => unreachable!(),
            };
            Some((proposition, PropositionSort::Bool))
        }
        Formula::Add(lhs, rhs)
        | Formula::Sub(lhs, rhs)
        | Formula::Mul(lhs, rhs)
        | Formula::Div(lhs, rhs)
        | Formula::Rem(lhs, rhs) => {
            let ((lhs, lhs_sort), (rhs, rhs_sort)) = binary(lhs, rhs)?;
            let domain = merge_numeric_sorts(lhs_sort, rhs_sort)?;
            let proposition = match formula {
                Formula::Add(..) => Proposition::Add(Box::new(lhs), Box::new(rhs)),
                Formula::Sub(..) => Proposition::Sub(Box::new(lhs), Box::new(rhs)),
                Formula::Mul(..) => Proposition::Mul(Box::new(lhs), Box::new(rhs)),
                Formula::Div(..) => Proposition::Div(Box::new(lhs), Box::new(rhs)),
                Formula::Rem(..) => Proposition::Rem(Box::new(lhs), Box::new(rhs)),
                _ => unreachable!(),
            };
            Some((proposition, PropositionSort::Numeric(domain)))
        }
        Formula::Neg(inner) => {
            let (inner, PropositionSort::Numeric(domain)) = unary(inner)? else {
                return None;
            };
            Some((Proposition::Neg(Box::new(inner)), PropositionSort::Numeric(domain)))
        }
        _ => None,
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum LoweredExprTy {
    Bool,
    Int,
    Float,
    /// A sequence: `Vec<T>`, `[T]`, `[T; N]`.
    ///
    /// Carried so a clause can NAME one. It has no proposition domain, so it
    /// follows the `Float` precedent exactly: empty `variable_domains`, which
    /// feeds the body-bound Trust-WP lane while staying opaque to
    /// certified-monitor authority until a sequence proposition domain
    /// exists. The equality arm is already generic over `lhs.ty == rhs.ty`,
    /// so `ret.terms == c.terms` lowers without touching it.
    Seq,
}

/// Trust: the shared core of contract-predicate helper inlining — the gates
/// that decide whether a callee's value is a CLOSED FUNCTION OF ITS ARGUMENTS,
/// plus the rendering of its body over the given actual texts.
///
/// Every gate is fail-closed; the `Err` states which one fired, and is what
/// `TRUST_CONTRACT_INLINE_TRACE` prints.
///
/// 1. NON-GENERIC. Under a type parameter the body's arithmetic depends on the
///    instantiation, and the emitted text would not fix the sort the
///    proposition is read at.
/// 2. A body that is a single tail expression with NO statements. A `let`, an
///    assignment or an early `return` is a computation this vocabulary cannot
///    represent, and admitting one would silently drop it.
/// 3. Arity match, and every parameter a plain by-value, non-`mut` binding (no
///    `ref`, no subpattern) — the binding must denote precisely the actual that
///    replaces it.
/// 4. Every path in the body resolves to one of those parameters or to a
///    `const`. This is the load-bearing gate: an unbound local would render to
///    a free variable named in the CALLER's namespace and could capture an
///    unrelated term of the same name, and a `static` is not a function of the
///    arguments at all.
///
/// PURITY needs no separate check — it follows from the fragment. The recursive
/// `lower_expr_text` admits only literals, paths, casts and
/// arithmetic/comparison operators, so nothing with an effect can lower.
///
/// SOUNDNESS, stated exactly: the result is the callee's OWN expression over
/// the caller's actual terms, in the same vocabulary the caller would have
/// written by hand. Inlining `g(a)` therefore yields precisely what the author
/// would have gotten by writing `g`'s body with `a` substituted for the
/// parameter — no more and no less. It mints no free variable, so unlike the
/// `__len`/`__sign` lanes there is nothing left for the VC layer to ground, and
/// it cannot vacuously prove. Whatever machine-width reading the surrounding
/// clause gets, both sides of the equation get the same one.
///
/// NOTE it does NOT assume the callee's own precondition. That is deliberate
/// and safe in this direction: an inlined term the solver cannot interpret (say
/// a division a `requires` would have excluded) leaves the clause harder to
/// prove, never easier, so the failure direction stays fail-closed.
fn inline_helper_call_reasoned<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee: LocalDefId,
    actual_texts: &[String],
    depth: u32,
) -> Result<LoweredExpr, &'static str> {
    if depth >= MAX_CONTRACT_INLINE_DEPTH {
        return Err("inline depth bound reached");
    }

    let own = tcx.generics_of(callee.to_def_id()).own_counts();
    if own.types != 0 || own.consts != 0 {
        return Err("callee is generic");
    }

    let Some(body) = tcx.hir_maybe_body_owned_by(callee) else {
        return Err("callee has no HIR body");
    };
    if body.params.len() != actual_texts.len() {
        return Err("arity mismatch");
    }

    let mut param_ids = Vec::with_capacity(body.params.len());
    for param in body.params {
        let PatKind::Binding(BindingMode(ByRef::No, rustc_ast::Mutability::Not), id, _, None) =
            param.pat.kind
        else {
            return Err("a parameter is not a plain by-value binding");
        };
        param_ids.push(id);
    }

    let ExprKind::Block(block, None) = &body.value.kind else {
        return Err("callee body is not a plain block");
    };
    if !block.stmts.is_empty() {
        return Err("callee body has statements");
    }
    let Some(tail) = block.expr else {
        return Err("callee body has no tail expression");
    };

    let callee_typeck = tcx.typeck(callee);
    let signature = tcx.fn_sig(callee.to_def_id()).instantiate_identity().skip_binder();
    if callee_typeck.expr_ty(tail) != signature.output()
        || callee_typeck.expr_ty_adjusted(tail) != signature.output()
    {
        return Err("callee tail expression reaches its result through a dropped coercion");
    }
    let mut only_params =
        InlinedBodyNamesOnlyParams { typeck_results: callee_typeck, params: &param_ids, ok: true };
    intravisit::Visitor::visit_expr(&mut only_params, tail);
    if !only_params.ok {
        return Err("callee body names something other than its own parameters");
    }

    // Parenthesize each actual: it is spliced into the callee's expression,
    // where a bare `a + b` would otherwise re-associate against the callee's
    // own operators.
    let pat_bindings =
        param_ids.iter().zip(actual_texts).map(|(id, text)| (*id, format!("({text})"))).collect();

    // The callee's body is typed by ITS OWN typeck results, and `result` is
    // meaningless inside it.
    let inner = ExprLowerer {
        tcx,
        typeck_results: callee_typeck,
        result_binding: None,
        pat_bindings,
        inline_depth: depth + 1,
    };
    let Some(lowered) = inner.lower_expr_text(tail) else {
        return Err("callee body does not lower (outside the predicate fragment)");
    };
    Ok(LoweredExpr {
        text: format!("({})", lowered.text),
        ty: lowered.ty,
        variable_domains: lowered.variable_domains,
    })
}

/// Resolve a bare snippet name through rustc's completed module binding table.
/// The table contains the actual `Res` selected by name resolution (including
/// imports and constructors), unlike a crate-wide string scan. This lane is
/// intentionally narrower than Rust: only one DIRECT same-module free function
/// is admitted. Aliases/reexports are refused because their textual spelling
/// no longer identifies the function body, and a signature binding with the
/// same name wins expression resolution over the module item.
fn resolved_direct_local_fn_named(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    shadowed_names: &BTreeSet<String>,
    name: &str,
) -> Result<LocalDefId, &'static str> {
    if shadowed_names.contains(name) {
        return Err("callee name is shadowed by a function parameter");
    }

    let module = tcx.parent_module_from_def_id(owner);
    let mut matches = tcx
        .module_children_local(module.to_local_def_id())
        .iter()
        .filter(|child| child.ident.name.as_str() == name);
    let Some(child) = matches.next() else {
        return Err("callee has no binding in the contract owner's module");
    };
    if matches.next().is_some() {
        return Err("callee name has more than one module binding");
    }
    if !child.reexport_chain.is_empty() {
        return Err("callee binding is an import or reexport");
    }
    let Res::Def(DefKind::Fn, def_id) = child.res else {
        return Err("callee module binding is not a free function");
    };
    let Some(local) = def_id.as_local() else {
        return Err("callee is not local");
    };
    if tcx.opt_local_parent(local) != Some(module.to_local_def_id()) {
        return Err("callee is not defined directly in the contract owner's module");
    }
    Ok(local)
}

fn exact_formula_domain(
    text: &str,
    variable_domains: &[LoweredVariableDomain],
) -> Option<TrustContractPropositionDomain> {
    let formula = trust_types::parse_spec_expr(text)?;
    let mut domains = FxHashMap::default();
    for variable in variable_domains {
        if domains.insert(variable.name.as_str(), variable.domain).is_some() {
            return None;
        }
    }
    let (_, sort) = query_proposition_from_formula_inner(&formula, &domains)?;
    match sort {
        PropositionSort::Bool => Some(TrustContractPropositionDomain::Bool),
        PropositionSort::Numeric(Some(domain)) => Some(domain),
        // A bare numeric literal has no authenticated machine width or
        // signedness. The caller may not supply one by textual context.
        PropositionSort::Numeric(None) => None,
    }
}

fn inline_snippet_helper_call_reasoned<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    shadowed_names: &BTreeSet<String>,
    caller_domains: &[LoweredVariableDomain],
    name: &str,
    actual_texts: &[String],
    depth: u32,
) -> Result<LoweredExpr, &'static str> {
    let callee = resolved_direct_local_fn_named(tcx, owner, shadowed_names, name)?;
    if actual_texts.is_empty() {
        // With no typed actual there is no source-domain anchor after the
        // function name is erased. In particular a numeric literal return
        // could silently acquire the surrounding result's width/signedness.
        return Err("zero-argument helper has no exact snippet-domain anchor");
    }

    let signature = tcx.fn_sig(callee.to_def_id()).instantiate_identity().skip_binder();
    if signature.inputs().len() != actual_texts.len() {
        return Err("arity mismatch");
    }
    for (actual, formal) in actual_texts.iter().zip(signature.inputs()) {
        let Some(formal_domain) = proposition_domain_from_ty(tcx, *formal) else {
            return Err("formal type has no exact proposition domain");
        };
        if exact_formula_domain(actual, caller_domains) != Some(formal_domain) {
            return Err("actual expression does not have the exact formal proposition domain");
        }
    }

    let Some(output_domain) = proposition_domain_from_ty(tcx, signature.output()) else {
        return Err("result type has no exact proposition domain");
    };
    let lowered = inline_helper_call_reasoned(tcx, callee, actual_texts, depth)?;
    if lowered_expr_ty(tcx, signature.output()) != Some(lowered.ty) {
        return Err("lowered helper result does not retain its Rust result type");
    }
    if exact_formula_domain(&lowered.text, &lowered.variable_domains) != Some(output_domain) {
        return Err("expanded helper result does not retain its exact proposition domain");
    }
    Ok(lowered)
}

/// Trust: names the snippet grammar owns, which must never be read as a call to
/// a user `fn` even if the crate happens to define one with that name.
const CONTRACT_SNIPPET_RESERVED_CALLEES: &[&str] = &["forall", "exists", "old"];

/// Trust: expand calls to transparent helpers in a NATIVE contract snippet.
///
/// Trust's own spec grammar (`fn f(..) requires P ensures Q`) reaches the
/// compiler as a snippet with no HIR expression identity, so it is lowered by
/// `SnippetParser` — a text parser — and never by the typed HIR lowerer. That
/// parser has no `TyCtxt` and therefore cannot resolve, let alone inline, a
/// callee. Rather than teach it to, this rewrites `g(a)` to `g`'s own body over
/// `a` BEFORE tokenizing, so the parser sees ordinary arithmetic and needs no
/// change at all.
///
/// Anything that does not resolve and pass every gate is left EXACTLY as it was
/// — the parser then refuses it precisely as before, so this can only ever turn
/// a refusal into a proof, never alter an existing verdict.
fn expand_contract_helper_calls(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    text: &str,
    depth: u32,
    caller_domains: &[LoweredVariableDomain],
    shadowed_names: &BTreeSet<String>,
) -> String {
    let mut inline = |name: &str, actual_texts: &[String], depth: u32| {
        let outcome = inline_snippet_helper_call_reasoned(
            tcx,
            owner,
            shadowed_names,
            caller_domains,
            name,
            actual_texts,
            depth,
        );
        if crate::trust_verify::trust_env_var_present("TRUST_CONTRACT_INLINE_TRACE") {
            match &outcome {
                Ok(lowered) => {
                    eprintln!("TRUST_CONTRACT_INLINE_TRACE: snippet `{name}` -> `{}`", lowered.text)
                }
                Err(reason) => {
                    eprintln!("TRUST_CONTRACT_INLINE_TRACE: snippet `{name}` refused ({reason})")
                }
            }
        }
        outcome.ok().map(|lowered| lowered.text)
    };
    rewrite_contract_helper_calls(text, depth, &mut inline)
}

/// Token-preserving core of the snippet pre-pass. Keeping name discovery and
/// byte copying independent of `TyCtxt` lets the UTF-8/string/comment boundary
/// itself be regression-tested; the callback still owns every semantic gate.
fn rewrite_contract_helper_calls(
    text: &str,
    depth: u32,
    inline: &mut impl FnMut(&str, &[String], u32) -> Option<String>,
) -> String {
    if depth >= MAX_CONTRACT_INLINE_DEPTH {
        return text.to_string();
    }
    let bytes = text.as_bytes();
    let mut out = String::with_capacity(text.len());
    let mut i = 0usize;
    while i < bytes.len() {
        if let Some(end) = protected_contract_token_end(text, i) {
            out.push_str(&text[i..end]);
            i = end;
            continue;
        }

        let c = bytes[i];
        if !(c.is_ascii_alphabetic() || c == b'_') {
            let ch = text[i..].chars().next().expect("i is kept on a UTF-8 boundary");
            out.push(ch);
            i += ch.len_utf8();
            continue;
        }
        let start = i;
        while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
            i += 1;
        }
        let name = &text[start..i];

        // A METHOD call (`x.len()`) and a qualified path (`m::f()`) are not
        // this lane's business; their own arms already decide them.
        let previous = text[..start].chars().next_back();
        let is_selected = previous.is_some_and(|ch| !ch.is_ascii() || matches!(ch, '.' | '#'))
            || (start >= 2 && &text[start - 2..start] == "::");
        let mut j = i;
        while j < bytes.len() && (bytes[j] as char).is_whitespace() {
            j += 1;
        }
        if is_selected
            || j >= bytes.len()
            || bytes[j] != b'('
            || CONTRACT_SNIPPET_RESERVED_CALLEES.contains(&name)
        {
            out.push_str(name);
            continue;
        }
        let Some(close) = matching_close_paren(text, j) else {
            out.push_str(name);
            continue;
        };

        // Arguments are themselves snippet text and may contain calls, so they
        // are expanded first (innermost-out).
        let inner = &text[j + 1..close];
        let actual_texts: Vec<String> = if inner.trim().is_empty() {
            Vec::new()
        } else {
            let Some(parts) = split_top_level_commas(inner) else {
                out.push_str(&text[start..=close]);
                i = close + 1;
                continue;
            };
            parts
                .into_iter()
                .map(|arg| rewrite_contract_helper_calls(arg.trim(), depth + 1, inline))
                .collect()
        };

        let expanded = inline(name, &actual_texts, depth);
        match expanded {
            Some(lowered) => {
                out.push_str(&lowered);
                i = close + 1;
            }
            None => {
                // A refused candidate is byte-identical to the source. Do not
                // opportunistically expand a nested call under an unresolved
                // outer call: that would contradict this pre-pass's fail-closed
                // contract even if the parser later refused the outer name.
                out.push_str(&text[start..=close]);
                i = close + 1;
            }
        }
    }
    out
}

/// Trust: split an argument list on its TOP-LEVEL commas — those not nested in
/// a bracket — so a nested call or index keeps its own arguments.
fn split_top_level_commas(input: &str) -> Option<Vec<&str>> {
    let bytes = input.as_bytes();
    let mut parts = Vec::new();
    let mut depth = 0i32;
    let mut start = 0usize;
    let mut idx = 0usize;
    while idx < bytes.len() {
        if let Some(end) = protected_contract_token_end(input, idx) {
            idx = end;
            continue;
        }
        match bytes[idx] {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => {
                depth = depth.checked_sub(1)?;
            }
            b',' if depth == 0 => {
                parts.push(&input[start..idx]);
                start = idx + 1;
            }
            _ => {}
        }
        idx += input[idx..].chars().next()?.len_utf8();
    }
    (depth == 0).then_some(())?;
    parts.push(&input[start..]);
    Some(parts)
}

/// Trust: the bound on nested contract-predicate call inlining
/// (`ExprLowerer::lower_inlined_call`). Deliberately small — a contract that
/// needs deeper nesting to state its property is better written with the
/// intermediate helper named directly.
const MAX_CONTRACT_INLINE_DEPTH: u32 = 4;

/// Trust: gate 6 of `ExprLowerer::lower_inlined_call` — an ALLOW-list over the
/// paths appearing in a helper body being inlined into a contract predicate.
///
/// Written as an allow-list rather than a deny-list on purpose: the question is
/// "is this path certainly a function of the arguments", and only two answers
/// are. A parameter is (it is replaced by the actual), and a `const` is (it
/// lowers to its own value). Everything else — a `static`, an unbound local, a
/// path to another item — is refused without needing to enumerate it.
struct InlinedBodyNamesOnlyParams<'a, 'tcx> {
    typeck_results: &'a TypeckResults<'tcx>,
    params: &'a [HirId],
    ok: bool,
}

impl<'tcx> Visitor<'tcx> for InlinedBodyNamesOnlyParams<'_, 'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        // A CALLEE path in call position is not a value being READ, so it is
        // not the kind of name this gate is about. Whether that function may
        // itself be inlined is decided by `lower_inlined_call`'s own gates,
        // applied to it recursively. Checking it here would reject every
        // NESTED call outright and make `MAX_CONTRACT_INLINE_DEPTH`
        // unreachable past the first level. The arguments are still checked.
        if let ExprKind::Call(callee, args) = &expr.kind
            && matches!(callee.kind, ExprKind::Path(_))
        {
            for arg in *args {
                self.visit_expr(arg);
            }
            return;
        }
        if let ExprKind::Path(qpath) = &expr.kind {
            let permitted = match self.typeck_results.qpath_res(qpath, expr.hir_id) {
                Res::Local(id) => self.params.contains(&id),
                Res::Def(DefKind::Const { .. } | DefKind::AssocConst { .. }, _) => true,
                _ => false,
            };
            if !permitted {
                self.ok = false;
            }
        }
        intravisit::walk_expr(self, expr);
    }
}

struct LoweredExpr {
    text: String,
    ty: LoweredExprTy,
    variable_domains: Vec<LoweredVariableDomain>,
}

impl LoweredExpr {
    fn literal(text: String, ty: LoweredExprTy) -> Self {
        Self { text, ty, variable_domains: Vec::new() }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct LoweredVariableDomain {
    name: String,
    domain: TrustContractPropositionDomain,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct LoweredSourceBinding {
    name: String,
    hir_local_id: u32,
}

/// Recover a complete, canonical source-root map for a native loop
/// proposition. Synthetic collection leaves (`xs__len`, `xs[0]`) are rebound
/// to the exact `xs` HIR binding. Any unmatched leaf rejects the whole map;
/// partial provenance must never authorize a proof lane.
fn exact_predicate_source_place_bindings(
    kind: &TrustContractPredicateKind,
    candidates: &[LoweredSourceBinding],
) -> Option<Vec<TrustContractSourceBinding>> {
    fn collect_names(proposition: &TrustContractProposition, names: &mut BTreeSet<String>) {
        use TrustContractProposition as Proposition;
        match proposition {
            Proposition::Var { name, .. } => {
                names.insert(name.to_string());
            }
            // A literal binds no name.
            Proposition::Float { .. } => {}
            Proposition::Not(inner) | Proposition::Neg(inner) => collect_names(inner, names),
            Proposition::And(terms) | Proposition::Or(terms) => {
                for term in terms {
                    collect_names(term, names);
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
                collect_names(lhs, names);
                collect_names(rhs, names);
            }
            Proposition::Bool(_) | Proposition::Int(_) | Proposition::UInt(_) => {}
        }
    }

    let proposition = match kind {
        TrustContractPredicateKind::Typed { proposition, .. } => proposition,
        // A literal has no free source roots, so the complete exact map is
        // the empty map rather than the fail-closed "unknown" state.
        TrustContractPredicateKind::BoolLiteral { .. } => return Some(Vec::new()),
        TrustContractPredicateKind::Opaque { .. }
        | TrustContractPredicateKind::MirLocal { .. }
        | TrustContractPredicateKind::Unsupported { .. } => return None,
    };
    let mut used = BTreeSet::new();
    collect_names(proposition, &mut used);
    let candidates = candidates
        .iter()
        .map(|binding| (binding.name.as_str(), binding))
        .collect::<BTreeMap<_, _>>();
    let mut roots = BTreeMap::<String, u32>::new();
    for leaf in used {
        let root = if candidates.contains_key(leaf.as_str()) {
            leaf.as_str()
        } else if let Some(base) = leaf.strip_suffix("__len") {
            base
        } else if let Some((base, _)) = canonical_literal_collection_projection(&leaf) {
            base
        } else {
            return None;
        };
        let binding = candidates.get(root)?;
        if let Some(previous) = roots.insert(binding.name.clone(), binding.hir_local_id)
            && previous != binding.hir_local_id
        {
            return None;
        }
    }
    Some(
        roots
            .into_iter()
            .map(|(name, hir_local_id)| TrustContractSourceBinding {
                name: Symbol::intern(&name),
                hir_local_id,
            })
            .collect(),
    )
}

/// Retain only exact source bindings actually used by this structural
/// proposition. Missing candidates are intentional: synthesized/projection
/// leaves remain statically meaningful but can never be rebound to a whole MIR
/// local by the certified-monitor lane.
fn exact_predicate_source_bindings(
    kind: &TrustContractPredicateKind,
    candidates: &[LoweredSourceBinding],
) -> Vec<TrustContractSourceBinding> {
    fn collect_names(proposition: &TrustContractProposition, names: &mut BTreeSet<String>) {
        use TrustContractProposition as Proposition;
        match proposition {
            Proposition::Var { name, .. } => {
                names.insert(name.to_string());
            }
            // A literal binds no name.
            Proposition::Float { .. } => {}
            Proposition::Not(inner) | Proposition::Neg(inner) => collect_names(inner, names),
            Proposition::And(terms) | Proposition::Or(terms) => {
                for term in terms {
                    collect_names(term, names);
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
                collect_names(lhs, names);
                collect_names(rhs, names);
            }
            Proposition::Bool(_) | Proposition::Int(_) | Proposition::UInt(_) => {}
        }
    }

    let TrustContractPredicateKind::Typed { proposition, .. } = kind else {
        return Vec::new();
    };
    let mut used = BTreeSet::new();
    collect_names(proposition, &mut used);
    let mut by_name = BTreeMap::new();
    let mut ambiguous = BTreeSet::new();
    for candidate in candidates {
        if !used.contains(&candidate.name) || ambiguous.contains(&candidate.name) {
            continue;
        }
        if let Some(previous) = by_name.insert(candidate.name.clone(), candidate.hir_local_id)
            && previous != candidate.hir_local_id
        {
            // An identity ambiguity cannot authorize either candidate.
            by_name.remove(&candidate.name);
            ambiguous.insert(candidate.name.clone());
        }
    }
    by_name
        .into_iter()
        .map(|(name, hir_local_id)| TrustContractSourceBinding {
            name: Symbol::intern(&name),
            hir_local_id,
        })
        .collect()
}

fn proposition_domain_from_ty(
    tcx: TyCtxt<'_>,
    ty: Ty<'_>,
) -> Option<TrustContractPropositionDomain> {
    use rustc_middle::ty::{IntTy, UintTy};
    if ty.is_bool() {
        return Some(TrustContractPropositionDomain::Bool);
    }
    let pointer_width = || u32::try_from(tcx.data_layout.pointer_size().bits()).ok();
    let (width, signed) = match ty.kind() {
        ty::Int(IntTy::Isize) => {
            return Some(TrustContractPropositionDomain::PointerSizedInt {
                width: pointer_width()?,
                signed: true,
            });
        }
        ty::Uint(UintTy::Usize) => {
            return Some(TrustContractPropositionDomain::PointerSizedInt {
                width: pointer_width()?,
                signed: false,
            });
        }
        ty::Int(kind) => (
            match kind {
                IntTy::I8 => 8,
                IntTy::I16 => 16,
                IntTy::I32 => 32,
                IntTy::I64 => 64,
                IntTy::I128 => 128,
                IntTy::Isize => unreachable!(),
            },
            true,
        ),
        ty::Uint(kind) => (
            match kind {
                UintTy::U8 => 8,
                UintTy::U16 => 16,
                UintTy::U32 => 32,
                UintTy::U64 => 64,
                UintTy::U128 => 128,
                UintTy::Usize => unreachable!(),
            },
            false,
        ),
        // A float PARAMETER gets a domain so it is in scope for a clause at all.
        // Without one `signature_variable_domains` skips it, the lowerer resolves
        // the name to nothing, and every `requires`/`ensures` mentioning it is a
        // hard error — which is what blocked the magnitude bound that
        // `float_range::contract_range` is written to consume.
        ty::Float(kind) => {
            return Some(TrustContractPropositionDomain::Float {
                width: match kind {
                    ty::FloatTy::F16 => 16,
                    ty::FloatTy::F32 => 32,
                    ty::FloatTy::F64 => 64,
                    ty::FloatTy::F128 => 128,
                },
            });
        }
        _ => return None,
    };
    Some(TrustContractPropositionDomain::MachineInt { width, signed })
}

fn collection_element_domain_from_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    name: String,
    ty: Ty<'tcx>,
) -> Option<(String, LoweredCollectionDomain)> {
    let (source_name, collection_ty) = match ty.kind() {
        ty::Ref(_, inner, _) => (name, *inner),
        ty::RawPtr(inner, _) => (format!("{name}*"), *inner),
        _ => (name, ty),
    };
    let (element, fixed_length) = match collection_ty.kind() {
        ty::Array(element, length) => {
            (*element, Some(u128::from(length.try_to_target_usize(tcx)?)))
        }
        ty::Slice(element) => (*element, None),
        // `Vec<T>` is an Adt, so it never reached the arms above and a clause
        // naming one was a HARD ERROR, not a soft refusal: "collection
        // accessor `len` requires an Array base, found Datatype
        // `std::vec::Vec<i64>`". Measured, same compiler: `requires
        // xs.len() == n` proves for `xs: &[i64]` and fails to COMPILE for
        // `xs: Vec<i64>` -- the identical clause over the identical element
        // type, refused for the container alone.
        //
        // A Vec models as its slice view for this purpose: the collection
        // domain carries only an element domain and an optional type-level
        // length, and a Vec has no static length, so it takes `None` exactly
        // as a slice does. Nothing here depends on the buffer, the capacity,
        // or the allocator.
        //
        // Gated on the DIAGNOSTIC ITEM, never a rendered path: a path test
        // would also fire on any user type whose path ends in `Vec`
        // (`mod fake { pub struct Vec<T>(T); }`), and admitting a look-alike
        // as a sequence is precisely the confusion this gate exists to avoid.
        ty::Adt(adt_def, args) if tcx.is_diagnostic_item(rustc_span::sym::Vec, adt_def.did()) => {
            (args.type_at(0), None)
        }
        _ => return None,
    };
    Some((
        source_name,
        LoweredCollectionDomain {
            element: proposition_domain_from_ty(tcx, element)?,
            fixed_length,
        },
    ))
}

/// Render an opaque aggregate's *sort name*.
///
/// This string is verifier DATA (a `Sort::Datatype` name that participates in
/// sort identity and in the typed-proposition digest), never diagnostic prose.
/// It must therefore be produced with `with_no_trimmed_paths!`, for two
/// independent reasons:
///
/// 1. SOUNDNESS OF THE NAME. A trimmed path is the shortest spelling that
///    happens to be unambiguous *in this crate's* diagnostic namespace. It is
///    context-dependent and non-injective across compilations, so two distinct
///    types can render to the same `Sort::Datatype` name. Sort identity must not
///    depend on what else the crate imports. This matches the policy already
///    stated on `trust_mir_extract::safe_def_path_str`, which every other Trust
///    identity string goes through.
/// 2. NO ICE WITH VERIFICATION OFF. Displaying a `DefId`-bearing type consults
///    the `trimmed_def_paths` query, which arms
///    `DiagCtxt::set_must_produce_diag`: rustc then asserts at drop that a
///    diagnostic really was emitted. `trust_check_clean_islands` runs the
///    `trust_contracts` query unconditionally — including under
///    `-Ztrust-verify=off`, where the contract is deliberately *not checked* and
///    so nothing is ever emitted. Requesting a trimmed path here made every
///    contract-bearing crate ICE with `` `trimmed_def_paths` called, diagnostics
///    were expected but none were emitted `` in the compatibility lane. See
///    `tests/ui/trust/contract_verify_off_no_ice.rs`.
fn opaque_sort_name(ty: Ty<'_>) -> String {
    with_no_trimmed_paths!(format!("{ty}"))
}

/// Source-level sort used to elaborate native E4/E5 clauses. Scalars retain
/// their logical Bool/Int sort, while arrays and slices retain their exact
/// element sort for indexing and collection accessors. Other aggregates stay
/// opaque: their names remain in scope, but ordinary fields are rejected until
/// exact source layouts are available.
fn loop_source_sort_from_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<trust_types::Sort> {
    match ty.kind() {
        ty::Bool => Some(trust_types::Sort::Bool),
        ty::Int(_) | ty::Uint(_) | ty::Char => Some(trust_types::Sort::Int),
        // A float binds at its IEEE sort, which is what the source validator
        // already gives a float LITERAL (`SpecExpr::FloatLit` sorts as
        // `Float { eb: 11, sb: 53 }`). Without this arm the parameter had no
        // source sort at all, so `requires x <= 1.0` reported `x` out of scope —
        // the variable was missing, not the literal.
        //
        // This is the SOURCE sort and is deliberately not the place sort: the
        // body spells a float local as its bit vector, and the proposition
        // translator lifts it with `FpFromBits`. The two layers agree through
        // that lift, not by sharing a spelling.
        ty::Float(kind) => trust_types::Sort::float_for_width(match kind {
            ty::FloatTy::F16 => 16,
            ty::FloatTy::F32 => 32,
            ty::FloatTy::F64 => 64,
            ty::FloatTy::F128 => 128,
        }),
        ty::Array(element, _) | ty::Slice(element) => Some(trust_types::Sort::Array(
            Box::new(trust_types::Sort::Int),
            Box::new(loop_source_sort_from_ty(tcx, *element).unwrap_or_else(|| {
                trust_types::Sort::Datatype {
                    name: opaque_sort_name(*element),
                    constructors: Vec::new(),
                }
            })),
        )),
        // `Vec<T>` sorts as its SLICE VIEW. Without this it fell to the
        // generic `ty::Adt` arm below and became an opaque `Sort::Datatype`,
        // so a clause naming one was a HARD ERROR rather than a soft refusal:
        // "collection accessor `len` requires an Array base, found Datatype
        // `std::vec::Vec<i64>`". Measured, same compiler: `requires
        // xs.len() == n` PROVES for `xs: &[i64]` and fails to COMPILE for
        // `xs: Vec<i64>` -- the same clause over the same element type,
        // refused for the container alone.
        //
        // The element sort is recovered exactly as the slice arm does,
        // falling back to an opaque datatype for a non-scalar element, so a
        // `Vec<Term>` sorts as `Array(Int, Datatype(Term))` just as
        // `&[Term]` does. Nothing here depends on the buffer, the capacity,
        // or the allocator: a sort carries the element and the fact that the
        // base is indexable, and a Vec is indexable exactly as its slice is.
        //
        // Gated on the DIAGNOSTIC ITEM, never a rendered path -- a path test
        // would also fire on a user type whose path ends in `Vec`.
        ty::Adt(adt_def, args)
            if tcx.is_diagnostic_item(rustc_span::sym::Vec, adt_def.did())
                && args.types().next().is_some() =>
        {
            let element = args.type_at(0);
            Some(trust_types::Sort::Array(
                Box::new(trust_types::Sort::Int),
                Box::new(loop_source_sort_from_ty(tcx, element).unwrap_or_else(|| {
                    trust_types::Sort::Datatype {
                        name: opaque_sort_name(element),
                        constructors: Vec::new(),
                    }
                })),
            ))
        }
        ty::Str => Some(trust_types::Sort::Array(
            Box::new(trust_types::Sort::Int),
            Box::new(trust_types::Sort::Int),
        )),
        ty::Adt(..) | ty::Tuple(..) | ty::Param(..) | ty::Alias(..) => {
            Some(trust_types::Sort::Datatype {
                name: opaque_sort_name(ty),
                constructors: Vec::new(),
            })
        }
        _ => None,
    }
}

/// Give a visible Rust binding its verifier-source spelling and sort. Scalar
/// references/pointers require the explicit source dereference `*x`, whose
/// canonical MIR/formula name is `x*`. Slice/array references retain the base
/// spelling because source indexing and `.len()` use Rust's deref coercion.
fn loop_source_binding_from_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    name: String,
    ty: Ty<'tcx>,
) -> Option<(String, trust_types::Sort)> {
    match ty.kind() {
        ty::Ref(_, inner, _) => {
            let sort = loop_source_sort_from_ty(tcx, *inner)?;
            let source_name = if matches!(inner.kind(), ty::Array(..) | ty::Slice(..) | ty::Str) {
                name
            } else {
                format!("{name}*")
            };
            Some((source_name, sort))
        }
        // Raw pointers never receive Rust's reference deref coercions. Even a
        // pointer to a slice must use explicit verifier syntax such as
        // `(*p).len()`, whose canonical source binding is `p*`.
        ty::RawPtr(inner, _) => {
            let sort = loop_source_sort_from_ty(tcx, *inner)?;
            Some((format!("{name}*"), sort))
        }
        _ => loop_source_sort_from_ty(tcx, ty).map(|sort| (name, sort)),
    }
}

/// Recover exact source sorts for function parameters used by a native E5
/// clause. Unlike proposition domains, this environment retains aggregate
/// parameters so measures such as `xs.len()` can be admitted without treating
/// a scalar as a collection. This is source/type admission only; MIR extraction
/// still has to rebind every accepted projection before it gains proof authority.
fn function_source_sorts<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &'tcx rustc_hir::Body<'tcx>,
    typeck_results: &TypeckResults<'tcx>,
) -> BTreeMap<String, trust_types::Sort> {
    struct Collector<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        typeck_results: &'a TypeckResults<'tcx>,
        sorts: BTreeMap<String, trust_types::Sort>,
    }

    impl<'tcx> Visitor<'tcx> for Collector<'_, 'tcx> {
        fn visit_pat(&mut self, pat: &'tcx Pat<'tcx>) {
            if let PatKind::Binding(_, canonical_id, ident, _) = pat.kind
                && canonical_id == pat.hir_id
                && let Some((name, sort)) = loop_source_binding_from_ty(
                    self.tcx,
                    ident.name.to_string(),
                    self.typeck_results.pat_ty(pat),
                )
            {
                self.sorts.insert(name, sort);
            }
            intravisit::walk_pat(self, pat);
        }
    }

    let mut collector = Collector { tcx, typeck_results, sorts: BTreeMap::new() };
    for param in body.params {
        collector.visit_pat(param.pat);
    }
    collector.sorts
}

/// Exact primitive element domains for collection parameters. This is kept
/// separate from the logical source-sort environment: source elaboration
/// intentionally treats every primitive integer as `Int`, while a structural
/// compiler proposition must still distinguish (for example) `u8`, `i8`, and
/// `usize` before it can authorize an executable monitor. Historical body-bound
/// TrustWP envelopes no longer mint compiler proof authority.
fn function_collection_element_domains<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &'tcx rustc_hir::Body<'tcx>,
    typeck_results: &TypeckResults<'tcx>,
) -> BTreeMap<String, LoweredCollectionDomain> {
    struct Collector<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        typeck_results: &'a TypeckResults<'tcx>,
        domains: BTreeMap<String, LoweredCollectionDomain>,
        ambiguous: BTreeSet<String>,
    }

    impl<'tcx> Visitor<'tcx> for Collector<'_, 'tcx> {
        fn visit_pat(&mut self, pat: &'tcx Pat<'tcx>) {
            if let PatKind::Binding(_, canonical_id, ident, _) = pat.kind
                && canonical_id == pat.hir_id
                && !ident.span.from_expansion()
                && let Some((name, domain)) = collection_element_domain_from_ty(
                    self.tcx,
                    ident.name.to_string(),
                    self.typeck_results.pat_ty(pat),
                )
                && !self.ambiguous.contains(&name)
                && self.domains.insert(name.clone(), domain).is_some()
            {
                self.domains.remove(&name);
                self.ambiguous.insert(name);
            }
            intravisit::walk_pat(self, pat);
        }
    }

    let mut collector =
        Collector { tcx, typeck_results, domains: BTreeMap::new(), ambiguous: BTreeSet::new() };
    for param in body.params {
        collector.visit_pat(param.pat);
    }
    collector.domains
}

/// Return the exact HIR identity for each uniquely named direct parameter.
///
/// A displayed spelling shared by distinct hygienic parameters is omitted,
/// even though the query-level admission gate rejects the complete contract
/// bundle first. Destructured parameters remain conservatively excluded.
fn unique_simple_parameter_hir_local_ids(body: &rustc_hir::Body<'_>) -> BTreeMap<String, u32> {
    let mut candidates = BTreeMap::<String, Option<u32>>::new();
    for param in body.params {
        let PatKind::Binding(_, canonical_id, ident, None) = param.pat.kind else {
            continue;
        };
        if canonical_id != param.pat.hir_id {
            continue;
        }
        let id = canonical_id.local_id.as_u32();
        use std::collections::btree_map::Entry;
        match candidates.entry(ident.name.to_string()) {
            Entry::Vacant(entry) => {
                entry.insert(Some(id));
            }
            Entry::Occupied(mut entry) => {
                if entry.get().is_some_and(|previous| previous != id) {
                    entry.insert(None);
                }
            }
        }
    }
    candidates.into_iter().filter_map(|(name, id)| id.map(|id| (name, id))).collect()
}

/// Recover the exact HIR bindings visible at a source loop. rustc's region
/// scope tree is the authority here: a similarly named binding elsewhere in
/// the body is never accepted, and a narrower visible binding correctly
/// shadows an outer one. This is intentionally source/type admission only;
/// downstream MIR reconstruction still rebinds every accepted name before a
/// clause can influence proof authority.
fn visible_loop_source_sorts<'tcx>(
    tcx: TyCtxt<'tcx>,
    local_def_id: LocalDefId,
    body: &'tcx rustc_hir::Body<'tcx>,
    typeck_results: &TypeckResults<'tcx>,
    loop_id: HirId,
    signature_domains: &[LoweredVariableDomain],
) -> BTreeMap<String, trust_types::Sort> {
    struct Collector<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        typeck_results: &'a TypeckResults<'tcx>,
        scope_tree: &'a ScopeTree,
        target: Scope,
        unique_parameter_hir_local_ids: &'a BTreeMap<String, u32>,
        // Key by the Rust identifier, not the verifier spelling. Keep visible
        // unsupported bindings as `None`: an inner aggregate/closure named `x`
        // must still shadow an outer supported integer `x` rather than
        // accidentally resurrecting the outer verifier binding.
        bindings: BTreeMap<String, (Scope, u32, Option<(String, trust_types::Sort)>)>,
        opaque_item_in_scope: bool,
    }

    impl<'tcx> Visitor<'tcx> for Collector<'_, 'tcx> {
        fn visit_pat(&mut self, pat: &'tcx Pat<'tcx>) {
            if let PatKind::Binding(_, canonical_id, ident, _) = pat.kind
                // Or-pattern alternatives share the first binding's canonical
                // id; visit that binding once rather than manufacturing an
                // ambiguity from repeated pattern syntax.
                && canonical_id == pat.hir_id
                && let Some(scope) = self.scope_tree.var_scope(canonical_id.local_id)
                && self.scope_tree.is_subscope_of(self.target, scope)
            {
                if has_local_hygiene(ident.span) {
                    self.opaque_item_in_scope = true;
                }
                // Contract desugaring and macros can inject LOCAL bindings
                // whose hygiene cannot be represented by the verifier's
                // plain-text names. Retain such a name as an unsupported
                // shadow instead of omitting it: omission could incorrectly
                // resurrect an outer same-named parameter. A function
                // parameter is different: its exact HIR binding and type are
                // the signature environment itself, including when a proc
                // macro emitted the whole function. Accept that exact
                // parameter identity while keeping every hygienic local
                // fail-closed. The `None` row never enters the source
                // environment.
                let rust_name = ident.name.to_string();
                let exact_unique_parameter = self.unique_parameter_hir_local_ids.get(&rust_name)
                    == Some(&canonical_id.local_id.as_u32());
                let hygienic_non_parameter = ident.span.from_expansion() && !exact_unique_parameter;
                let source_binding = if hygienic_non_parameter {
                    None
                } else {
                    loop_source_binding_from_ty(
                        self.tcx,
                        rust_name.clone(),
                        self.typeck_results.pat_ty(pat),
                    )
                };
                use std::collections::btree_map::Entry;
                match self.bindings.entry(rust_name) {
                    Entry::Vacant(entry) => {
                        entry.insert((scope, canonical_id.local_id.as_u32(), source_binding));
                    }
                    Entry::Occupied(mut entry) => {
                        let (previous_scope, previous_id, _) = entry.get();
                        if scope == *previous_scope
                            && canonical_id.local_id.as_u32() != *previous_id
                        {
                            // Macro hygiene permits distinct same-spelled
                            // bindings in one lexical scope. The verifier
                            // payload carries only the displayed name, so
                            // choosing either HIR identity would be unsound.
                            entry.get_mut().2 = None;
                        } else if scope != *previous_scope
                            && self.scope_tree.is_subscope_of(scope, *previous_scope)
                        {
                            entry.insert((scope, canonical_id.local_id.as_u32(), source_binding));
                        }
                    }
                }
            }
            intravisit::walk_pat(self, pat);
        }

        // Trust (review round 39, 2026-10-02): an item declared in a block
        // (`const lim: u8 = 200;`, a `static`, a `fn`) is visible in that whole
        // block and shadows an outer `let lim`, but it is no pattern binding, so
        // the outer `let` was accepted and a loop `invariant lim <= 127` was
        // proved about it while the `lim` in scope is 200. Record such an item as
        // an unsupported binding at the block's scope: the narrower-scope rule
        // below then shadows an outer `let` with it, and a `let` in a narrower
        // block still wins.
        fn visit_block(&mut self, block: &'tcx rustc_hir::Block<'tcx>) {
            let block_scope = Scope { local_id: block.hir_id.local_id, data: ScopeData::Node };
            if self.scope_tree.is_subscope_of(self.target, block_scope) {
                for stmt in block.stmts {
                    let rustc_hir::StmtKind::Item(item_id) = stmt.kind else { continue };
                    // An item whose names are not one syntactic ident (a glob
                    // `use m::*`, an `extern { static lim: u8; }` block) can shadow
                    // ANY name, a parameter included (review round 40): no name is
                    // bindable at this loop.
                    let Some(ident) = self.tcx.hir_item(item_id).kind.ident() else {
                        self.opaque_item_in_scope = true;
                        continue;
                    };
                    if has_local_hygiene(ident.span) {
                        self.opaque_item_in_scope = true;
                    }
                    use std::collections::btree_map::Entry;
                    match self.bindings.entry(ident.name.to_string()) {
                        Entry::Vacant(entry) => {
                            entry.insert((block_scope, u32::MAX, None));
                        }
                        Entry::Occupied(mut entry) => {
                            let (previous_scope, _, _) = entry.get();
                            if block_scope == *previous_scope
                                || self.scope_tree.is_subscope_of(block_scope, *previous_scope)
                            {
                                entry.insert((block_scope, u32::MAX, None));
                            }
                        }
                    }
                }
            }
            intravisit::walk_block(self, block);
        }
    }

    let scope_tree = tcx.region_scope_tree(local_def_id);
    let unique_parameter_hir_local_ids = unique_simple_parameter_hir_local_ids(body);
    let mut collector = Collector {
        tcx,
        typeck_results,
        scope_tree,
        target: Scope { local_id: loop_id.local_id, data: ScopeData::Node },
        unique_parameter_hir_local_ids: &unique_parameter_hir_local_ids,
        bindings: BTreeMap::new(),
        opaque_item_in_scope: has_local_hygiene(tcx.hir_span(loop_id)),
    };
    collector.visit_body(body);
    if collector.opaque_item_in_scope {
        return BTreeMap::new();
    }
    let visible_rust_names = collector.bindings.keys().cloned().collect::<BTreeSet<_>>();
    let mut sorts = collector
        .bindings
        .into_iter()
        .filter_map(|(_, (_, _, binding))| binding)
        .collect::<BTreeMap<_, _>>();
    // Region scope trees for closure owners may be redirected to the enclosing
    // function. Preserve exact scalar parameter domains as a conservative
    // fallback, without overwriting a lexically narrower binding recovered
    // above.
    for (name, sort) in signature_input_source_sorts(signature_domains) {
        let rust_name = name.strip_suffix('*').unwrap_or(&name);
        if !visible_rust_names.contains(rust_name)
            && unique_parameter_hir_local_ids.contains_key(rust_name)
        {
            sorts.entry(name).or_insert(sort);
        }
    }
    sorts
}

/// Recover exact primitive domains for the same visible HIR bindings accepted
/// by [`visible_loop_source_sorts`]. This is intentionally independent of MIR
/// debug info: ordinary builds may omit `var_debug_info`, while the query must
/// still distinguish (for example) `u8`, `i8`, and `usize` before an E4/E5
/// expression becomes a structural proposition.
fn visible_loop_variable_domains<'tcx>(
    tcx: TyCtxt<'tcx>,
    local_def_id: LocalDefId,
    body: &'tcx rustc_hir::Body<'tcx>,
    typeck_results: &TypeckResults<'tcx>,
    loop_id: HirId,
    signature_domains: &[LoweredVariableDomain],
) -> (
    Vec<LoweredVariableDomain>,
    BTreeMap<String, LoweredCollectionDomain>,
    Vec<LoweredSourceBinding>,
    Vec<LoweredSourceBinding>,
) {
    struct BindingDomains {
        scalar: Option<(LoweredVariableDomain, Option<LoweredSourceBinding>)>,
        collection: Option<(String, LoweredCollectionDomain)>,
        source_place: Option<LoweredSourceBinding>,
    }

    fn binding_domain<'tcx>(
        tcx: TyCtxt<'tcx>,
        name: String,
        ty: Ty<'tcx>,
        hir_local_id: u32,
    ) -> BindingDomains {
        let collection = collection_element_domain_from_ty(tcx, name.clone(), ty);
        let (name, scalar_ty, is_whole_scalar) = match ty.kind() {
            ty::Ref(_, inner, _) | ty::RawPtr(inner, _) => (format!("{name}*"), *inner, false),
            _ => (name, ty, true),
        };
        let scalar = proposition_domain_from_ty(tcx, scalar_ty).map(|domain| {
            let source_binding =
                is_whole_scalar.then(|| LoweredSourceBinding { name: name.clone(), hir_local_id });
            (LoweredVariableDomain { name, domain }, source_binding)
        });
        let source_place_name = scalar
            .as_ref()
            .map(|(domain, _)| domain.name.clone())
            .or_else(|| collection.as_ref().map(|(name, _)| name.clone()));
        let source_place =
            source_place_name.map(|name| LoweredSourceBinding { name, hir_local_id });
        BindingDomains { scalar, collection, source_place }
    }

    struct Collector<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        typeck_results: &'a TypeckResults<'tcx>,
        scope_tree: &'a ScopeTree,
        target: Scope,
        unique_parameter_hir_local_ids: &'a BTreeMap<String, u32>,
        bindings: BTreeMap<String, (Scope, u32, Option<BindingDomains>)>,
        opaque_item_in_scope: bool,
    }

    impl<'tcx> Visitor<'tcx> for Collector<'_, 'tcx> {
        fn visit_pat(&mut self, pat: &'tcx Pat<'tcx>) {
            if let PatKind::Binding(_, canonical_id, ident, _) = pat.kind
                && canonical_id == pat.hir_id
                && let Some(scope) = self.scope_tree.var_scope(canonical_id.local_id)
                && self.scope_tree.is_subscope_of(self.target, scope)
            {
                if has_local_hygiene(ident.span) {
                    self.opaque_item_in_scope = true;
                }
                // Mirror the source-sort collector exactly: a hygienic local
                // is an unsupported shadow, not permission to fall through to
                // an outer same-named scalar domain. An exact function
                // parameter remains admissible when a proc macro emitted the
                // whole function.
                let rust_name = ident.name.to_string();
                let exact_unique_parameter = self.unique_parameter_hir_local_ids.get(&rust_name)
                    == Some(&canonical_id.local_id.as_u32());
                let hygienic_non_parameter = ident.span.from_expansion() && !exact_unique_parameter;
                let domain = if hygienic_non_parameter {
                    None
                } else {
                    Some(binding_domain(
                        self.tcx,
                        rust_name.clone(),
                        self.typeck_results.pat_ty(pat),
                        canonical_id.local_id.as_u32(),
                    ))
                };
                use std::collections::btree_map::Entry;
                match self.bindings.entry(rust_name) {
                    Entry::Vacant(entry) => {
                        entry.insert((scope, canonical_id.local_id.as_u32(), domain));
                    }
                    Entry::Occupied(mut entry) => {
                        let (previous_scope, previous_id, _) = entry.get();
                        if scope == *previous_scope
                            && canonical_id.local_id.as_u32() != *previous_id
                        {
                            entry.get_mut().2 = None;
                        } else if scope != *previous_scope
                            && self.scope_tree.is_subscope_of(scope, *previous_scope)
                        {
                            entry.insert((scope, canonical_id.local_id.as_u32(), domain));
                        }
                    }
                }
            }
            intravisit::walk_pat(self, pat);
        }

        // Trust (review round 39, 2026-10-02): an item declared in a block
        // (`const lim: u8 = 200;`, a `static`, a `fn`) is visible in that whole
        // block and shadows an outer `let lim`, but it is no pattern binding, so
        // the outer `let` was accepted and a loop `invariant lim <= 127` was
        // proved about it while the `lim` in scope is 200. Record such an item as
        // an unsupported binding at the block's scope: the narrower-scope rule
        // below then shadows an outer `let` with it, and a `let` in a narrower
        // block still wins.
        fn visit_block(&mut self, block: &'tcx rustc_hir::Block<'tcx>) {
            let block_scope = Scope { local_id: block.hir_id.local_id, data: ScopeData::Node };
            if self.scope_tree.is_subscope_of(self.target, block_scope) {
                for stmt in block.stmts {
                    let rustc_hir::StmtKind::Item(item_id) = stmt.kind else { continue };
                    // An item whose names are not one syntactic ident (a glob
                    // `use m::*`, an `extern { static lim: u8; }` block) can shadow
                    // ANY name, a parameter included (review round 40): no name is
                    // bindable at this loop.
                    let Some(ident) = self.tcx.hir_item(item_id).kind.ident() else {
                        self.opaque_item_in_scope = true;
                        continue;
                    };
                    if has_local_hygiene(ident.span) {
                        self.opaque_item_in_scope = true;
                    }
                    use std::collections::btree_map::Entry;
                    match self.bindings.entry(ident.name.to_string()) {
                        Entry::Vacant(entry) => {
                            entry.insert((block_scope, u32::MAX, None));
                        }
                        Entry::Occupied(mut entry) => {
                            let (previous_scope, _, _) = entry.get();
                            if block_scope == *previous_scope
                                || self.scope_tree.is_subscope_of(block_scope, *previous_scope)
                            {
                                entry.insert((block_scope, u32::MAX, None));
                            }
                        }
                    }
                }
            }
            intravisit::walk_block(self, block);
        }
    }

    let scope_tree = tcx.region_scope_tree(local_def_id);
    let unique_parameter_hir_local_ids = unique_simple_parameter_hir_local_ids(body);
    let mut collector = Collector {
        tcx,
        typeck_results,
        scope_tree,
        target: Scope { local_id: loop_id.local_id, data: ScopeData::Node },
        unique_parameter_hir_local_ids: &unique_parameter_hir_local_ids,
        bindings: BTreeMap::new(),
        opaque_item_in_scope: has_local_hygiene(tcx.hir_span(loop_id)),
    };
    collector.visit_body(body);
    if collector.opaque_item_in_scope {
        return (Vec::new(), BTreeMap::new(), Vec::new(), Vec::new());
    }
    let visible_rust_names = collector.bindings.keys().cloned().collect::<BTreeSet<_>>();
    let mut domains = Vec::new();
    let mut collection_domains = BTreeMap::new();
    let mut source_bindings = Vec::new();
    let mut source_place_bindings = Vec::new();
    for (_, _, binding) in collector.bindings.into_values() {
        let Some(binding) = binding else { continue };
        source_place_bindings.extend(binding.source_place);
        if let Some((domain, source_binding)) = binding.scalar {
            domains.push(domain);
            source_bindings.extend(source_binding);
        }
        if let Some((name, domain)) = binding.collection {
            collection_domains.insert(name, domain);
        }
    }

    // The signature fallback below is needed only for redirected closure
    // region-scope trees. Keep a parallel exact identity map for simple whole
    // primitive parameters; reference/projection aliases are deliberately
    // absent.
    let signature_source_bindings = body
        .params
        .iter()
        .filter_map(|param| {
            let PatKind::Binding(_, canonical_id, ident, None) = param.pat.kind else {
                return None;
            };
            (unique_parameter_hir_local_ids.get(ident.name.as_str())
                == Some(&canonical_id.local_id.as_u32())
                && proposition_domain_from_ty(tcx, typeck_results.pat_ty(param.pat)).is_some())
            .then(|| {
                (
                    ident.name.to_string(),
                    LoweredSourceBinding {
                        name: ident.name.to_string(),
                        hir_local_id: canonical_id.local_id.as_u32(),
                    },
                )
            })
        })
        .collect::<BTreeMap<_, _>>();

    // Match the conservative closure-owner fallback in
    // `visible_loop_source_sorts`, but never revive a shadowed parameter.
    for domain in signature_domains.iter().filter(|domain| domain.name != "_0") {
        let rust_name = domain.name.strip_suffix('*').unwrap_or(&domain.name);
        if !visible_rust_names.contains(rust_name)
            && unique_parameter_hir_local_ids.contains_key(rust_name)
        {
            domains.push(domain.clone());
            if let Some(binding) = signature_source_bindings.get(&domain.name) {
                source_bindings.push(binding.clone());
                source_place_bindings.push(binding.clone());
            }
        }
    }
    for (name, domain) in function_collection_element_domains(tcx, body, typeck_results) {
        let rust_name = name.strip_suffix('*').unwrap_or(&name);
        if !visible_rust_names.contains(rust_name)
            && unique_parameter_hir_local_ids.contains_key(rust_name)
        {
            collection_domains.entry(name.clone()).or_insert(domain);
            if let Some(hir_local_id) = unique_parameter_hir_local_ids.get(rust_name) {
                source_place_bindings
                    .push(LoweredSourceBinding { name, hir_local_id: *hir_local_id });
            }
        }
    }
    (
        canonical_variable_domains(domains).unwrap_or_default(),
        collection_domains,
        canonical_source_bindings(source_bindings).unwrap_or_default(),
        canonical_source_bindings(source_place_bindings).unwrap_or_default(),
    )
}

/// Bounded depth for the projected-leaf walk. Mirrors
/// `trust_mir_extract::PROJECTED_LEAF_DEPTH_LIMIT`, whose spelling this
/// enumeration must agree with byte-for-byte.
const CONTRACT_PROJECTION_DEPTH_LIMIT: u32 = 8;
/// Entry budget per parameter. On exhaustion the walk simply stops emitting:
/// a missing leaf leaves its chain unresolvable, so the clause that projects
/// it stays `Unsupported` — never admitted under a guessed name.
const CONTRACT_PROJECTION_ENTRY_BUDGET: u32 = 512;

/// One scalar leaf of an aggregate parameter, in the three spellings the
/// contract pipeline needs to agree on.
struct ProjectedLeaf {
    /// The chain exactly as a contract author writes it in Rust source
    /// (`self.storage.flag`, `s.0`). Named fields keep their source name;
    /// tuple fields are already spelled by index.
    authored: String,
    /// The contract TEXT to emit. `spec_parse` lowers this to `canonical_var`
    /// — a leading deref MUST be written `(*self)` because the postfix-star
    /// var spelling is not itself parseable text.
    canonical_text: String,
    /// The var name `canonical_text` parses to, byte-identical to the name
    /// `trust_vcgen::place_to_var_name` mints for the matching MIR place
    /// (`(*_1).0.3` with local 1 named `self` renders `self*.0.3`).
    canonical_var: String,
    domain: TrustContractPropositionDomain,
    /// Which STATE of the place the authored spelling names. See [`LeafEpoch`].
    epoch: LeafEpoch,
}

/// Trust (D2 primes, M0(b1) of
/// docs/design/2026-09-29-descriptor-protocols-as-compiler-errors.md, 2026-09-30):
/// which state of a projected place an AUTHORED spelling denotes.
///
/// A primed head (`self'.storage.detached`, or `x'` for a scalar `x: &mut T`) is the
/// ratified D2 spelling of a `&mut` parameter's FINAL value
/// (docs/design/2026-07-09-two-language-spec-surface.md §3, D2). It resolves to the
/// same canonical place as the unprimed spelling, which today's native lane reads at
/// EXIT, so the prime binds exactly the value vcgen already reads there. It is only
/// ever admitted in an `ensures`. While the unprimed spelling of a `&mut` pointee
/// still means the exit value too, a clause may not mix the two: `*x' == *x` over
/// `*x += 1` would compare exit with exit and prove. D2's entry reading of the
/// unprimed spelling lifts that refusal.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum LeafEpoch {
    /// A by-value parameter's field, or a shared reference's pointee.
    Plain,
    /// A `&mut` parameter's pointee, spelled without a prime.
    MutPointeeUnprimed,
    /// A `&mut` parameter's pointee, spelled with a prime: its final value.
    Primed,
}

/// Authored projection chains resolved to their exact canonical spelling.
///
/// A chain is admitted ONLY if every segment resolves to a real field index of
/// a single-variant, non-enum, non-union aggregate and the leaf has an exact
/// proposition domain. Anything else is simply absent, and an absent chain
/// makes the whole clause `Unsupported` — the fix never guesses a name.
#[derive(Default)]
struct ProjectionEnvironment {
    canonical_text: FxHashMap<String, String>,
    /// The [`LeafEpoch`] of every admitted authored spelling.
    epochs: FxHashMap<String, LeafEpoch>,
    /// The `&mut` parameters, by source name: `*x` over one is an unprimed read of
    /// its pointee, which the mixed-epoch refusal must see.
    mut_params: FxHashSet<String>,
}

impl ProjectionEnvironment {
    fn resolve(&self, authored: &str) -> Option<&str> {
        self.canonical_text.get(authored).map(String::as_str)
    }

    fn epoch(&self, authored: &str) -> LeafEpoch {
        self.epochs.get(authored).copied().unwrap_or(LeafEpoch::Plain)
    }
}

/// Enumerate the scalar leaves reachable from each parameter through struct
/// and tuple fields.
///
/// This is the compiler-query twin of `trust_mir_extract::projected_leaf_sort`,
/// which resolves the identical positional spelling on the extraction side
/// (one chain at a time, from the chain names a contract spells). ENUMS
/// and UNIONS are never walked (their field view is variant-dependent, so a
/// chain name would be ambiguous); references below the head, generic
/// parameters, arrays, and every other shape stop the walk at that node.
fn signature_projection_leaves<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &'tcx rustc_hir::Body<'tcx>,
    typeck_results: &TypeckResults<'tcx>,
) -> Vec<ProjectedLeaf> {
    let mut leaves = Vec::new();
    for param in body.params {
        let PatKind::Binding(_, _, ident, None) = param.pat.kind else { continue };
        let ty = typeck_results.pat_ty(param.pat);
        // The head follows `signature_variable_domains`: a reference parameter
        // is dereferenced, which `place_to_var_name` renders as a POSTFIX star
        // on the var and which must be written `(*name)` as text.
        let (head_var, head_text, aggregate_ty, mutable) = match ty.kind() {
            ty::Ref(_, inner, mutability) => (
                format!("{}*", ident.name),
                format!("(*{})", ident.name),
                *inner,
                mutability.is_mut(),
            ),
            _ => (ident.name.to_string(), ident.name.to_string(), ty, false),
        };
        let mut budget = CONTRACT_PROJECTION_ENTRY_BUDGET;
        push_projected_leaves(
            tcx,
            &mut leaves,
            &ident.name.to_string(),
            &head_var,
            &head_text,
            aggregate_ty,
            CONTRACT_PROJECTION_DEPTH_LIMIT,
            &mut budget,
            if mutable { LeafEpoch::MutPointeeUnprimed } else { LeafEpoch::Plain },
        );
        // Trust (D2 primes, 2026-09-30): the primed spellings of a `&mut`
        // parameter's pointee, to the SAME canonical places. See `LeafEpoch`.
        if mutable {
            let primed_head = format!("{}'", ident.name);
            if let Some(domain) = proposition_domain_from_ty(tcx, aggregate_ty) {
                leaves.push(ProjectedLeaf {
                    authored: primed_head.clone(),
                    canonical_text: head_text.clone(),
                    canonical_var: head_var.clone(),
                    domain,
                    epoch: LeafEpoch::Primed,
                });
            }
            let mut primed_budget = CONTRACT_PROJECTION_ENTRY_BUDGET;
            push_projected_leaves(
                tcx,
                &mut leaves,
                &primed_head,
                &head_var,
                &head_text,
                aggregate_ty,
                CONTRACT_PROJECTION_DEPTH_LIMIT,
                &mut primed_budget,
                LeafEpoch::Primed,
            );
        }
    }
    leaves
}

fn push_projected_leaves<'tcx>(
    tcx: TyCtxt<'tcx>,
    leaves: &mut Vec<ProjectedLeaf>,
    authored: &str,
    canonical_var: &str,
    canonical_text: &str,
    ty: Ty<'tcx>,
    depth: u32,
    budget: &mut u32,
    epoch: LeafEpoch,
) {
    if depth == 0 || *budget == 0 {
        return;
    }
    // A type still carrying generic parameters has no field layout we can pin
    // here, and normalizing it in this query is not safe. Stop.
    if ty.has_non_region_param() {
        return;
    }
    let fields: Vec<(String, Ty<'tcx>)> = match ty.kind() {
        ty::Adt(def, args) => {
            // Only a single-variant, non-union ADT has an unconditional field
            // place. An enum field sits behind a discriminant and a union
            // field aliases its siblings; both must keep failing closed.
            if def.is_enum() || def.is_union() || def.variants().len() != 1 {
                return;
            }
            def.non_enum_variant()
                .fields
                .iter()
                // `FieldDef::ty` yields an `Unnormalized<_, Ty>` on this
                // toolchain; the projection walk only ever compares field
                // SHAPES (scalar vs ADT vs tuple) to decide whether a name is
                // projectable, and never reasons under an alias, so skipping
                // normalization here is the same choice `gvn` and
                // `remove_uninit_drops` make at their equivalent field walks.
                .map(|field| (field.name.to_string(), field.ty(tcx, *args).skip_normalization()))
                .collect()
        }
        ty::Tuple(items) => {
            items.iter().enumerate().map(|(index, item)| (index.to_string(), item)).collect()
        }
        _ => return,
    };
    for (index, (field_name, field_ty)) in fields.into_iter().enumerate() {
        if *budget == 0 {
            return;
        }
        // AUTHORED keeps the source spelling (`storage`); CANONICAL is always
        // positional, because `place_to_var_name` renders `Field(i)` as `.i`
        // and never by name. For a tuple struct the two coincide.
        let child_authored = format!("{authored}.{field_name}");
        let child_var = format!("{canonical_var}.{index}");
        let child_text = format!("{canonical_text}.{index}");
        match proposition_domain_from_ty(tcx, field_ty) {
            Some(domain) => {
                *budget -= 1;
                leaves.push(ProjectedLeaf {
                    authored: child_authored,
                    canonical_text: child_text,
                    canonical_var: child_var,
                    domain,
                    epoch,
                });
            }
            // No exact domain: recurse in case this is a nested aggregate.
            // A reference-typed field would need a further deref segment that
            // this spelling cannot express, so `push_projected_leaves` stops
            // on it (`ty::Ref` is not an `Adt`/`Tuple`).
            None => push_projected_leaves(
                tcx,
                leaves,
                &child_authored,
                &child_var,
                &child_text,
                field_ty,
                depth - 1,
                budget,
                epoch,
            ),
        }
    }
}

fn signature_projection_environment(leaves: &[ProjectedLeaf]) -> ProjectionEnvironment {
    let mut canonical_text: FxHashMap<String, String> = FxHashMap::default();
    let mut epochs: FxHashMap<String, LeafEpoch> = FxHashMap::default();
    let mut mut_params: FxHashSet<String> = FxHashSet::default();
    let mut ambiguous: BTreeSet<String> = BTreeSet::new();
    for leaf in leaves {
        if let Some(previous) =
            canonical_text.insert(leaf.authored.clone(), leaf.canonical_text.clone())
            && previous != leaf.canonical_text
        {
            // Two distinct places share one authored spelling. Neither may be
            // admitted: picking either could bind the clause to the wrong
            // place. Drop the entry entirely.
            ambiguous.insert(leaf.authored.clone());
        }
        epochs.insert(leaf.authored.clone(), leaf.epoch);
        // Every `&mut` parameter with a projectable leaf has a primed spelling, and
        // its head is the source name before the prime.
        if leaf.epoch == LeafEpoch::Primed
            && let Some((head, _)) = leaf.authored.split_once('\'')
        {
            mut_params.insert(head.to_string());
        }
    }
    for name in ambiguous {
        canonical_text.remove(&name);
        epochs.remove(&name);
    }
    ProjectionEnvironment { canonical_text, epochs, mut_params }
}

/// Put a float comparison into ONE IEEE format, using the parameter's declared
/// sort rather than the literal's.
///
/// The spec lexer builds every float literal as binary64, and the parser then
/// re-sorts a bare variable compared against one to binary64 as well. That is
/// right for `f64` and wrong for `f32`: the variable's real format is its
/// parameter's, so `requires x <= 1.0` on an `f32` produced a binary32 variable
/// against a binary64 constant and was refused as ill-typed operands.
///
/// This runs where BOTH the parsed formula and the declared source sorts are in
/// hand, which is the only place the reconciliation can be made. The parser has
/// no sorts; and doing it in the sort CHECK instead would let the clause validate
/// while the formula still carried the wide literal, handing the solver a
/// silently ill-sorted query — exactly what the refusal prevents.
///
/// EXACTNESS GATES THE NARROWING, and it is the whole safety of this. `1.0` and
/// `0.5` are the same number in binary32 and binary64, so rewriting them changes
/// nothing. `0.1` is NOT, and narrowing it would move the author's bound to a
/// number they did not write — so a literal that does not survive the round trip
/// is left alone and the clause keeps its honest refusal.
///
/// Only a comparison's own two operands are touched, only a LITERAL is rewritten,
/// and a variable is re-sorted to its DECLARED format and never to its peer's.
fn reconcile_float_literal_formats(
    formula: trust_types::Formula,
    source_sorts: &BTreeMap<String, trust_types::Sort>,
) -> trust_types::Formula {
    use trust_types::{Formula, Sort};

    fn declared_float(expr: &Formula, sorts: &BTreeMap<String, Sort>) -> Option<(u32, u32)> {
        let name = match expr {
            Formula::Var(name, _) => name.clone(),
            Formula::SymVar(sym, _) => sym.as_str().to_string(),
            _ => return None,
        };
        match sorts.get(&name) {
            Some(Sort::Float { eb, sb }) => Some((*eb, *sb)),
            _ => None,
        }
    }

    fn reformat(expr: Formula, eb: u32, sb: u32, sorts: &BTreeMap<String, Sort>) -> Formula {
        if declared_float(&expr, sorts) == Some((eb, sb)) {
            return match expr {
                Formula::Var(name, _) => Formula::Var(name, Sort::Float { eb, sb }),
                Formula::SymVar(sym, _) => {
                    Formula::Var(sym.as_str().to_string(), Sort::Float { eb, sb })
                }
                other => other,
            };
        }
        match expr {
            // THE SAME RULE the source sort checker applies, called rather than
            // restated: if those two ever disagreed, a clause would validate
            // while the solver received a wide literal against a narrow
            // variable.
            Formula::FpConst { bits, eb: 11, sb: 53 } if (eb, sb) != (11, 53) => {
                match u64::try_from(bits)
                    .ok()
                    .and_then(|wide| trust_types::float_literal_narrowed_bits(wide, eb, sb))
                {
                    Some(narrowed) => Formula::FpConst { bits: u128::from(narrowed), eb, sb },
                    None => Formula::FpConst { bits, eb: 11, sb: 53 },
                }
            }
            other => other,
        }
    }

    fn walk(expr: Formula, sorts: &BTreeMap<String, Sort>) -> Formula {
        let pair = |lhs: Box<Formula>, rhs: Box<Formula>| -> (Box<Formula>, Box<Formula>) {
            let (lhs, rhs) = (walk(*lhs, sorts), walk(*rhs, sorts));
            match declared_float(&lhs, sorts).or_else(|| declared_float(&rhs, sorts)) {
                Some((eb, sb)) => {
                    (Box::new(reformat(lhs, eb, sb, sorts)), Box::new(reformat(rhs, eb, sb, sorts)))
                }
                None => (Box::new(lhs), Box::new(rhs)),
            }
        };
        match expr {
            Formula::Lt(lhs, rhs) => {
                let (lhs, rhs) = pair(lhs, rhs);
                Formula::Lt(lhs, rhs)
            }
            Formula::Le(lhs, rhs) => {
                let (lhs, rhs) = pair(lhs, rhs);
                Formula::Le(lhs, rhs)
            }
            Formula::Gt(lhs, rhs) => {
                let (lhs, rhs) = pair(lhs, rhs);
                Formula::Gt(lhs, rhs)
            }
            Formula::Ge(lhs, rhs) => {
                let (lhs, rhs) = pair(lhs, rhs);
                Formula::Ge(lhs, rhs)
            }
            Formula::Eq(lhs, rhs) => {
                let (lhs, rhs) = pair(lhs, rhs);
                Formula::Eq(lhs, rhs)
            }
            // Trust (SPEC-FLOAT-EQ-STRUCTURAL-1): `x == 1.0` parses as IEEE `FpEq`;
            // its literal narrows onto an `f32` peer by the same rule as `Eq`.
            Formula::FpEq(lhs, rhs) => {
                let (lhs, rhs) = pair(lhs, rhs);
                Formula::FpEq(lhs, rhs)
            }
            Formula::Not(inner) => Formula::Not(Box::new(walk(*inner, sorts))),
            Formula::And(terms) => {
                Formula::And(terms.into_iter().map(|t| walk(t, sorts)).collect())
            }
            Formula::Or(terms) => Formula::Or(terms.into_iter().map(|t| walk(t, sorts)).collect()),
            Formula::Implies(lhs, rhs) => {
                Formula::Implies(Box::new(walk(*lhs, sorts)), Box::new(walk(*rhs, sorts)))
            }
            other => other,
        }
    }

    walk(formula, source_sorts)
}

fn signature_variable_domains<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: rustc_span::def_id::DefId,
    body: &'tcx rustc_hir::Body<'tcx>,
    typeck_results: &TypeckResults<'tcx>,
) -> Vec<LoweredVariableDomain> {
    let mut domains = Vec::new();
    for param in body.params {
        let PatKind::Binding(_, _, ident, None) = param.pat.kind else { continue };
        let ty = typeck_results.pat_ty(param.pat);
        let (name, scalar_ty) = match ty.kind() {
            ty::Ref(_, inner, _) => (format!("{}*", ident.name), *inner),
            _ => (ident.name.to_string(), ty),
        };
        if let Some(domain) = proposition_domain_from_ty(tcx, scalar_ty) {
            domains.push(LoweredVariableDomain { name, domain });
        }
    }
    // Projected scalar leaves of aggregate parameters. Each domain is the
    // FIELD's own `proposition_domain_from_ty` — no sort is ever invented, so
    // `projected_chain_sort` in the exact-projection validator is satisfied
    // with the real layout rather than by weakening the gate.
    for leaf in signature_projection_leaves(tcx, body, typeck_results) {
        // A primed spelling names a place an unprimed leaf already carries; it adds a
        // spelling, never a domain (see `LeafEpoch`).
        if leaf.epoch == LeafEpoch::Primed {
            continue;
        }
        domains.push(LoweredVariableDomain { name: leaf.canonical_var, domain: leaf.domain });
    }
    let output = tcx.fn_sig(def_id).instantiate_identity().skip_binder().output();
    if let Some(domain) = proposition_domain_from_ty(tcx, output) {
        domains.push(LoweredVariableDomain { name: "_0".to_string(), domain });
    }
    canonical_variable_domains(domains).unwrap_or_default()
}

/// Render an exactly evaluated constant as contract-grammar text.
///
/// Integers become a decimal literal (negatives use the `-(N)` spelling the
/// grammar's unary-minus arm accepts) and bools become `true`/`false`. A value
/// outside the grammar's `i128` literal range — every `u128` above `i128::MAX`
/// — is refused instead of being rendered as text that would silently re-lex to
/// a different number.
fn lowered_constant_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    value: rustc_middle::mir::ConstValue,
    ty: Ty<'tcx>,
) -> Option<LoweredExpr> {
    if ty.is_bool() {
        let value = value.try_to_bool()?;
        return Some(LoweredExpr::literal(value.to_string(), LoweredExprTy::Bool));
    }
    // Integers only, at the type's exact width. `int_bits_signed` doubles as the
    // admission test: it is `None` for every non-integer scalar (float, char,
    // reference, aggregate), none of which has an exact contract-grammar
    // literal. Taking the width from here rather than from a `layout_of` query
    // keeps the size used to read the scalar identical to the size the cast rule
    // reasons about, including for `usize`/`isize`.
    let (bits, signed) = int_bits_signed(tcx, ty)?;
    let size = rustc_abi::Size::from_bits(u64::from(bits));
    let scalar = value.try_to_scalar_int()?;
    if scalar.size() != size {
        return None;
    }
    // The contract grammar's integer token is an `i128`, so a `u128` above
    // `i128::MAX` has no exact literal. Refuse it rather than emit text that
    // would re-lex to a different number.
    let value =
        if signed { scalar.to_int(size) } else { i128::try_from(scalar.to_uint(size)).ok()? };
    // The grammar has no negative literal token; `-` is the unary-minus
    // operator, spelled here exactly as the `UnOp::Neg` arm spells it.
    let text = if value < 0 { format!("-({})", value.unsigned_abs()) } else { value.to_string() };
    Some(LoweredExpr::literal(text, LoweredExprTy::Int))
}

fn lowered_variable_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    text: String,
    rust_ty: Ty<'tcx>,
) -> Option<LoweredExpr> {
    let ty = lowered_expr_ty(tcx, rust_ty)?;
    // Compiler-owned executable-monitor identity currently has exact domains
    // only for Bool and primitive integers. Float predicates do not enter the
    // retired TrustWP authority path and remain opaque to certified-monitor
    // authority until a bit-exact float proposition domain exists.
    let variable_domains = match proposition_domain_from_ty(tcx, rust_ty) {
        Some(domain) => synthetic_variable_domains(&text, domain)?,
        None if ty == LoweredExprTy::Float || ty == LoweredExprTy::Seq => Vec::new(),
        None => return None,
    };
    Some(LoweredExpr { text, ty, variable_domains })
}

fn lowered_synthetic_expr(
    text: String,
    ty: LoweredExprTy,
    domain: TrustContractPropositionDomain,
) -> Option<LoweredExpr> {
    let variable_domains = synthetic_variable_domains(&text, domain)?;
    Some(LoweredExpr { text, ty, variable_domains })
}

fn synthetic_variable_domains(
    text: &str,
    domain: TrustContractPropositionDomain,
) -> Option<Vec<LoweredVariableDomain>> {
    let formula = trust_types::parse_spec_expr(text)?;
    let mut names = Vec::new();
    collect_query_formula_variable_names(&formula, &mut names)?;
    if names.is_empty() {
        return None;
    }
    canonical_variable_domains(
        names.into_iter().map(|name| LoweredVariableDomain { name, domain }).collect(),
    )
}

fn collect_query_formula_variable_names(
    formula: &trust_types::Formula,
    names: &mut Vec<String>,
) -> Option<()> {
    use trust_types::Formula;
    match formula {
        Formula::Bool(_) | Formula::Int(_) | Formula::UInt(_) => {}
        Formula::Var(name, _) => names.push(name.clone()),
        Formula::SymVar(name, _) => names.push(name.as_str().to_string()),
        Formula::Not(inner) | Formula::Neg(inner) => {
            collect_query_formula_variable_names(inner, names)?;
        }
        Formula::And(terms) | Formula::Or(terms) => {
            for term in terms {
                collect_query_formula_variable_names(term, names)?;
            }
        }
        Formula::Implies(lhs, rhs)
        | Formula::Eq(lhs, rhs)
        | Formula::Lt(lhs, rhs)
        | Formula::Le(lhs, rhs)
        | Formula::Gt(lhs, rhs)
        | Formula::Ge(lhs, rhs)
        | Formula::Add(lhs, rhs)
        | Formula::Sub(lhs, rhs)
        | Formula::Mul(lhs, rhs)
        | Formula::Div(lhs, rhs)
        | Formula::Rem(lhs, rhs) => {
            collect_query_formula_variable_names(lhs, names)?;
            collect_query_formula_variable_names(rhs, names)?;
        }
        _ => return None,
    }
    Some(())
}

fn canonical_variable_domains(
    domains: Vec<LoweredVariableDomain>,
) -> Option<Vec<LoweredVariableDomain>> {
    let mut by_name = std::collections::BTreeMap::new();
    for variable in domains {
        if let Some(previous) = by_name.insert(variable.name.clone(), variable.domain)
            && previous != variable.domain
        {
            return None;
        }
    }
    Some(by_name.into_iter().map(|(name, domain)| LoweredVariableDomain { name, domain }).collect())
}

fn canonical_source_bindings(
    bindings: Vec<LoweredSourceBinding>,
) -> Option<Vec<LoweredSourceBinding>> {
    let mut by_name = BTreeMap::new();
    for binding in bindings {
        if let Some(previous) = by_name.insert(binding.name.clone(), binding.hir_local_id)
            && previous != binding.hir_local_id
        {
            return None;
        }
    }
    Some(
        by_name
            .into_iter()
            .map(|(name, hir_local_id)| LoweredSourceBinding { name, hir_local_id })
            .collect(),
    )
}

fn merge_variable_domains(
    lhs: Vec<LoweredVariableDomain>,
    rhs: Vec<LoweredVariableDomain>,
) -> Option<Vec<LoweredVariableDomain>> {
    canonical_variable_domains(lhs.into_iter().chain(rhs).collect())
}

/// Is `ty` a sequence the clause language can name?
///
/// Slices and arrays, plus `Vec<T>` behind its DIAGNOSTIC ITEM -- never a
/// rendered path, which would also fire on a user type whose path ends in
/// `Vec`. A reference to one is transparent: `&[T]` and `&Vec<T>` name the
/// same sequence as the owned form, and a clause spells them identically.
fn is_sequence_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    let ty = match ty.kind() {
        ty::Ref(_, inner, _) => *inner,
        _ => ty,
    };
    match ty.kind() {
        ty::Slice(_) | ty::Array(..) => true,
        ty::Adt(adt_def, args) => {
            tcx.is_diagnostic_item(rustc_span::sym::Vec, adt_def.did())
                && args.types().next().is_some()
        }
        _ => false,
    }
}

fn lowered_expr_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<LoweredExprTy> {
    if is_sequence_ty(tcx, ty) {
        return Some(LoweredExprTy::Seq);
    }
    if ty.is_bool() {
        Some(LoweredExprTy::Bool)
    } else if ty.is_integral() {
        Some(LoweredExprTy::Int)
    } else if ty.is_floating_point() {
        // Trust: f32/f64 fields and operands. A float predicate lowers to the same
        // text form as an int one; the spec parser + verifier keep it float-sorted
        // so a magnitude bound `self.0 <= 1.0e30` discharges FloatOverflowToInfinity.
        Some(LoweredExprTy::Float)
    } else {
        None
    }
}

/// `(bit_width, is_signed)` for any primitive integer type, resolving `usize`/
/// `isize` at THIS COMPILATION'S EXACT TARGET pointer width.
///
/// The width is not a guess and not a host assumption: it is
/// `tcx.data_layout.pointer_size()`, the same authority
/// `proposition_domain_from_ty` already uses to build the
/// `PointerSizedInt { width }` domain that the contract's own free-variable
/// sidecar carries. A cast judgement made with it is therefore exactly as
/// target-specific as the proposition it feeds, and a cross-compile to a
/// narrower target re-decides it rather than inheriting this one.
fn int_bits_signed(tcx: TyCtxt<'_>, ty: Ty<'_>) -> Option<(u32, bool)> {
    use rustc_middle::ty::{IntTy, UintTy};
    match ty.kind() {
        ty::Int(IntTy::Isize) => {
            Some((u32::try_from(tcx.data_layout.pointer_size().bits()).ok()?, true))
        }
        ty::Uint(UintTy::Usize) => {
            Some((u32::try_from(tcx.data_layout.pointer_size().bits()).ok()?, false))
        }
        _ => fixed_int_bits_signed(ty),
    }
}

/// `(bit_width, is_signed)` for a FIXED-width primitive integer type. `usize`/
/// `isize` return `None` — their width is target-dependent, so a caller with no
/// target context cannot judge them; use [`int_bits_signed`] where a `TyCtxt`
/// is available. Non-integers return `None`.
fn fixed_int_bits_signed(ty: Ty<'_>) -> Option<(u32, bool)> {
    use rustc_middle::ty::{self, IntTy, UintTy};
    match ty.kind() {
        ty::Int(i) => match i {
            IntTy::I8 => Some((8, true)),
            IntTy::I16 => Some((16, true)),
            IntTy::I32 => Some((32, true)),
            IntTy::I64 => Some((64, true)),
            IntTy::I128 => Some((128, true)),
            IntTy::Isize => None,
        },
        ty::Uint(u) => match u {
            UintTy::U8 => Some((8, false)),
            UintTy::U16 => Some((16, false)),
            UintTy::U32 => Some((32, false)),
            UintTy::U64 => Some((64, false)),
            UintTy::U128 => Some((128, false)),
            UintTy::Usize => None,
        },
        _ => None,
    }
}

/// True iff an integer cast `src as dst` preserves the exact mathematical value
/// for EVERY `src` value — so a contract predicate may drop the cast and reason
/// about the operand directly (arbitrary-precision Int in the spec logic). The
/// only always-value-preserving integer casts are widenings:
///   * unsigned → unsigned, `dst_bits >= src_bits` (zero-extend);
///   * signed   → signed,   `dst_bits >= src_bits` (sign-extend);
///   * unsigned → signed,   `dst_bits >  src_bits` (needs the extra sign bit).
/// Signed → unsigned (negatives wrap) and any narrowing are NOT value-preserving
/// → rejected (fail-closed: the whole predicate becomes unsupported, never a
/// false PROVE).
///
/// `usize`/`isize` participate at the EXACT target pointer width (see
/// [`int_bits_signed`]) instead of being refused wholesale. That is what makes
/// the real-world guard `idx <= u32::MAX as usize` expressible: on a 64-bit
/// target `u32 as usize` is a widening and its value is preserved, while on a
/// 16-bit target the very same clause is refused because there it truncates.
/// The judgement is decided per compilation, never baked in.
fn value_preserving_int_cast(tcx: TyCtxt<'_>, src: Ty<'_>, dst: Ty<'_>) -> bool {
    let (Some(src), Some(dst)) = (int_bits_signed(tcx, src), int_bits_signed(tcx, dst)) else {
        return false;
    };
    value_preserving_int_cast_widths(src, dst)
}

/// The pure `(bits, signed)` core of [`value_preserving_int_cast`], split out so
/// the admission RULE itself is testable without a `TyCtxt`. `usize`/`isize`
/// arrive here already resolved to their target width, so this function decides
/// them by exactly the same arithmetic as any fixed-width pair.
fn value_preserving_int_cast_widths(
    (src_bits, src_signed): (u32, bool),
    (dst_bits, dst_signed): (u32, bool),
) -> bool {
    match (src_signed, dst_signed) {
        // Same signedness: widening keeps every value; narrowing truncates.
        (false, false) | (true, true) => dst_bits >= src_bits,
        // Unsigned -> signed needs a STRICTLY wider target: the target spends one
        // bit on the sign, so `u8 as i8` would send 255 to -1.
        (false, true) => dst_bits > src_bits,
        // Signed -> unsigned always loses the negatives (`-1i32 as u32`).
        (true, false) => false,
    }
}

fn lower_binary_expr_text(
    op: BinOpKind,
    lhs: LoweredExpr,
    rhs: LoweredExpr,
) -> Option<LoweredExpr> {
    let op_text = lower_bin_op(op)?;
    let variable_domains =
        merge_variable_domains(lhs.variable_domains.clone(), rhs.variable_domains.clone())?;
    match op {
        BinOpKind::And | BinOpKind::Or
            if lhs.ty == LoweredExprTy::Bool && rhs.ty == LoweredExprTy::Bool =>
        {
            Some(LoweredExpr {
                text: format!("({}) {op_text} ({})", lhs.text, rhs.text),
                ty: LoweredExprTy::Bool,
                variable_domains,
            })
        }
        BinOpKind::Eq | BinOpKind::Ne if lhs.ty == rhs.ty => Some(LoweredExpr {
            text: format!("({}) {op_text} ({})", lhs.text, rhs.text),
            ty: LoweredExprTy::Bool,
            variable_domains,
        }),
        BinOpKind::Lt | BinOpKind::Le | BinOpKind::Gt | BinOpKind::Ge
            if (lhs.ty == LoweredExprTy::Int && rhs.ty == LoweredExprTy::Int)
                || (lhs.ty == LoweredExprTy::Float && rhs.ty == LoweredExprTy::Float) =>
        {
            // Int·Int or Float·Float ordering. Mixed operands stay unsupported
            // (fail-closed): the spec parser keeps each side's sort, and a magnitude
            // bound is always same-sorted (`self.0 <= 1.0e30`, both Float).
            Some(LoweredExpr {
                text: format!("({}) {op_text} ({})", lhs.text, rhs.text),
                ty: LoweredExprTy::Bool,
                variable_domains,
            })
        }
        // Trust: integer ARITHMETIC inside a contract predicate (e.g. the `x + 1`
        // in `#[ensures(|r| *r == x + 1)]`). Without these the RHS could not be
        // lowered, so the WHOLE predicate fell to `Unsupported` -> a fail-closed
        // assertion that always FAILS, even for a perfectly valid contract.
        // Add/Sub/Mul/Div/Rem are emitted as the corresponding spec term — the
        // verifier checks div-by-zero/overflow as SEPARATE obligations, and the
        // predicate's `x / b` matches the body's identical division term, so a
        // CORRECT postcondition discharges (the terms cancel) while a WRONG one is
        // never falsely proved: it goes Unknown (constant-divisor cases ay refutes;
        // symbolic ones stay runtime-checked). Validated: `r == x / 2` for `x / 2`
        // proves; `r == x / 3` for `x / 2` does NOT (runtime-checked, no false proof).
        BinOpKind::Add | BinOpKind::Sub | BinOpKind::Mul | BinOpKind::Div | BinOpKind::Rem
            if lhs.ty == LoweredExprTy::Int && rhs.ty == LoweredExprTy::Int =>
        {
            Some(LoweredExpr {
                text: format!("({}) {op_text} ({})", lhs.text, rhs.text),
                ty: LoweredExprTy::Int,
                variable_domains,
            })
        }
        _ => None,
    }
}

fn lower_bin_op(op: BinOpKind) -> Option<&'static str> {
    match op {
        BinOpKind::And => Some("&&"),
        BinOpKind::Or => Some("||"),
        BinOpKind::Eq => Some("=="),
        BinOpKind::Ne => Some("!="),
        BinOpKind::Lt => Some("<"),
        BinOpKind::Le => Some("<="),
        BinOpKind::Gt => Some(">"),
        BinOpKind::Ge => Some(">="),
        BinOpKind::Add => Some("+"),
        BinOpKind::Sub => Some("-"),
        BinOpKind::Mul => Some("*"),
        BinOpKind::Div => Some("/"),
        BinOpKind::Rem => Some("%"),
        _ => None,
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum SnippetToken<'a> {
    Ident(&'a str),
    /// A Rust integer literal, kept as BOTH the authored spelling and the
    /// single integer it denotes.
    ///
    /// The value is what every ordinary use emits, re-spelled in bare decimal:
    /// that is what lets `999_999_999`, `0x3B9AC9FF` and `1000u32` reach the
    /// downstream formula parser, which reads decimal digits only. The spelling
    /// is kept because ONE use — a tuple-field index — must be the canonical
    /// spelling and not merely the right number.
    Int {
        spelling: &'a str,
        value: u128,
    },
    Gt,
    Ge,
    Lt,
    Le,
    EqEq,
    Ne,
    AndAnd,
    OrOr,
    Implies,
    CompatImplies,
    Bang,
    Star,
    Slash,
    Percent,
    Plus,
    Minus,
    LParen,
    RParen,
    Comma,
    Colon,
    DotDot,
    /// A single `.`, the projection-segment separator (`self.storage.flag`,
    /// `s.0`). Distinct from `DotDot`, which the tokenizer matches first, so a
    /// `Dot` is never part of a range.
    Dot,
}

/// The two snippet origins intentionally have different source grammars.
/// Attribute contracts retain the migration spellings (`old(x)` and bounded
/// function-form quantifiers); first-class clauses implement the ratified
/// language (`x'` and Lean-shaped typed binders). Keeping this distinction in
/// the parser prevents compatibility syntax from silently becoming native.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum SnippetSyntax {
    AttributeCompatibility,
    Native,
}

struct SnippetParser<'a> {
    tokens: Vec<SnippetToken<'a>>,
    index: usize,
    result_binding: Option<SnippetResultBinding<'a>>,
    syntax: SnippetSyntax,
    projections: &'a ProjectionEnvironment,
    /// The FIRST authored projection chain `ProjectionEnvironment` could not
    /// resolve, kept for attribution only. Like `literal_refusal`, this exists
    /// because the refusal it describes is otherwise INVISIBLE: the chain fails
    /// the whole clause closed (correctly), and the surviving diagnostic then
    /// names the chain's HEAD — a real parameter — as "not in scope", which
    /// points the author at the wrong token. Never proof authority.
    projection_refusal: Option<String>,
    /// A primed spelling (a `&mut` pointee's FINAL value) was read. See [`LeafEpoch`].
    saw_primed: bool,
    /// An unprimed `&mut` pointee was read (`self.x` or `*x` over a `&mut`
    /// parameter). Beside a primed read, the clause is refused: see [`LeafEpoch`].
    saw_unprimed_mut_pointee: bool,
}

#[derive(Copy, Clone)]
enum SnippetResultBinding<'a> {
    /// An attribute ensures closure receives `&Return`; bare use is invalid
    /// and only `*binding` denotes the result value.
    ClosureReference(&'a str),
    /// Native signature syntax binds `result` to the return value directly.
    NativeValue(&'a str),
}

impl<'a> SnippetParser<'a> {
    fn parse(
        input: &'a str,
        result_binding: Option<SnippetResultBinding<'a>>,
        syntax: SnippetSyntax,
        projections: &'a ProjectionEnvironment,
        literal_refusal: &mut Option<trust_types::int_literal::IntLiteralRefusal>,
        projection_refusal: &mut Option<String>,
    ) -> Option<SnippetExpr> {
        let tokens = tokenize_contract_snippet(input, syntax, literal_refusal)?;
        let mut parser = Self {
            tokens,
            index: 0,
            result_binding,
            syntax,
            projections,
            projection_refusal: None,
            saw_primed: false,
            saw_unprimed_mut_pointee: false,
        };
        let expr = parser.parse_implies();
        // Reported whether or not the parse survived: an unresolvable chain
        // makes `parse_implies` fail, which is exactly the case that needs
        // attributing.
        if parser.projection_refusal.is_some() {
            *projection_refusal = parser.projection_refusal.take();
        }
        let expr = expr?;
        // Mixed epochs: while an unprimed `&mut` pointee still reads the EXIT value,
        // a clause that also reads a primed one would compare exit with exit.
        if parser.saw_primed && parser.saw_unprimed_mut_pointee {
            return None;
        }
        if parser.is_eof() && expr.ty.can_be_bool() { Some(expr.into_bool()) } else { None }
    }

    fn is_eof(&self) -> bool {
        self.index == self.tokens.len()
    }

    fn peek(&self) -> Option<&SnippetToken<'a>> {
        self.tokens.get(self.index)
    }

    fn eat(&mut self, expected: &SnippetToken<'a>) -> bool {
        if self.peek() == Some(expected) {
            self.index += 1;
            true
        } else {
            false
        }
    }

    fn bump(&mut self) -> Option<SnippetToken<'a>> {
        let token = self.tokens.get(self.index).cloned()?;
        self.index += 1;
        Some(token)
    }

    // Verifier implication is right-associative. The ratified native spelling
    // is `==>`; the downstream formula parser's internal spelling is `=>`, so
    // snippet lowering canonicalizes both source spellings to that internal
    // representation. `=>` remains accepted only for attribute compatibility.
    fn parse_implies(&mut self) -> Option<SnippetExpr> {
        let lhs = self.parse_or()?;
        let has_implies = self.eat(&SnippetToken::Implies)
            || (self.syntax == SnippetSyntax::AttributeCompatibility
                && self.eat(&SnippetToken::CompatImplies));
        if has_implies {
            let rhs = self.parse_implies()?;
            lower_snippet_binary("=>", lhs, rhs, SnippetBinaryKind::Logic)
        } else {
            Some(lhs)
        }
    }

    fn parse_or(&mut self) -> Option<SnippetExpr> {
        let mut expr = self.parse_and()?;
        while self.eat(&SnippetToken::OrOr) {
            let rhs = self.parse_and()?;
            expr = lower_snippet_binary("||", expr, rhs, SnippetBinaryKind::Logic)?;
        }
        Some(expr)
    }

    fn parse_and(&mut self) -> Option<SnippetExpr> {
        let mut expr = self.parse_comparison()?;
        while self.eat(&SnippetToken::AndAnd) {
            let rhs = self.parse_comparison()?;
            expr = lower_snippet_binary("&&", expr, rhs, SnippetBinaryKind::Logic)?;
        }
        Some(expr)
    }

    fn parse_comparison(&mut self) -> Option<SnippetExpr> {
        let lhs = self.parse_additive()?;
        let Some((op, kind)) = self.peek().and_then(snippet_comparison_op) else {
            return Some(lhs);
        };
        self.bump()?;
        let rhs = self.parse_additive()?;
        lower_snippet_binary(op, lhs, rhs, kind)
    }

    // Integer `+`/`-` (left-assoc), below comparison and above multiplicative.
    fn parse_additive(&mut self) -> Option<SnippetExpr> {
        let mut expr = self.parse_multiplicative()?;
        loop {
            let op = match self.peek() {
                Some(SnippetToken::Plus) => "+",
                Some(SnippetToken::Minus) => "-",
                _ => break,
            };
            self.bump()?;
            let rhs = self.parse_multiplicative()?;
            expr = lower_snippet_binary(op, expr, rhs, SnippetBinaryKind::Arith)?;
        }
        Some(expr)
    }

    // Integer `*` (left-assoc). The tokenizer maps `*` to `Star`, which is also
    // the `*result` deref — but a PREFIX `*` is consumed inside `parse_atom`
    // (`parse_unary` -> `parse_atom`), so any `Star` we see HERE is INFIX, i.e.
    // multiply. So `*r == x * 2` disambiguates: prefix `*r` -> result, infix
    // `x * 2` -> `(x) * (2)`.
    fn parse_multiplicative(&mut self) -> Option<SnippetExpr> {
        let mut expr = self.parse_unary()?;
        loop {
            let op = match self.peek() {
                Some(SnippetToken::Star) => "*",
                Some(SnippetToken::Slash) => "/",
                Some(SnippetToken::Percent) => "%",
                _ => break,
            };
            self.bump()?;
            let rhs = self.parse_unary()?;
            expr = lower_snippet_binary(op, expr, rhs, SnippetBinaryKind::Arith)?;
        }
        Some(expr)
    }

    fn parse_unary(&mut self) -> Option<SnippetExpr> {
        if self.eat(&SnippetToken::Bang) {
            let inner = self.parse_unary()?;
            if !inner.ty.can_be_bool() {
                return None;
            }
            return Some(SnippetExpr {
                text: format!("!({})", inner.text),
                ty: SnippetExprTy::Bool,
                bool_literal: None,
            });
        }

        // Trust: unary integer negation `-x` (e.g. `ensures(|r| *r == -x)` for
        // `abs`). The spec parser lowers a leading `-` to `Formula::Neg`, so the
        // `-(<value expr>)` text round-trips. Mirrors the HIR `UnOp::Neg` arm.
        if self.eat(&SnippetToken::Minus) {
            let inner = self.parse_unary()?;
            if !inner.ty.can_be_value() {
                return None;
            }
            return Some(SnippetExpr {
                text: format!("-({})", inner.text),
                ty: SnippetExprTy::Value,
                bool_literal: None,
            });
        }

        self.parse_atom()
    }

    fn parse_atom(&mut self) -> Option<SnippetExpr> {
        match self.bump()? {
            // A projection chain is resolved as a WHOLE, from a bare-identifier
            // head, before any other identifier role is considered. Only the
            // natural Rust source spelling (`self.storage.flag`, `s.0`) is
            // accepted; it is rewritten to the canonical place text. Note
            // `parse_ident`'s roles (`old(..)`, quantifiers, `true`/`false`,
            // the result binding) are never followed by `.`, so this cannot
            // shadow them.
            SnippetToken::Ident(name) if self.peek() == Some(&SnippetToken::Dot) => {
                self.parse_projection_chain(name)
            }
            SnippetToken::Ident(name) => self.parse_ident(name),
            // Re-spell the constant in bare decimal. The VALUE is untouched —
            // this is only the respelling that makes an author's
            // `999_999_999`, `0x3B9AC9FF` or `1000u32` readable by
            // `trust_types::parse_spec_expr`, which the lowered text is handed
            // to next.
            SnippetToken::Int { value, .. } => Some(SnippetExpr {
                text: value.to_string(),
                ty: SnippetExprTy::Value,
                bool_literal: None,
            }),
            SnippetToken::Star => self.parse_deref(),
            SnippetToken::LParen => {
                let expr = self.parse_implies()?;
                self.eat(&SnippetToken::RParen).then_some(expr)
            }
            _ => None,
        }
    }

    /// Parse `head.seg.seg...` and rewrite it to the exact canonical place
    /// text, or reject the whole clause.
    ///
    /// Soundness: this function NEVER invents a name. The chain is looked up
    /// verbatim in `ProjectionEnvironment`, which was built by walking the
    /// real field layout of the parameter types, so the emitted text is either
    /// the byte-exact spelling `place_to_var_name` mints for that MIR place or
    /// nothing at all. A miss (unknown field, enum/union, reference field,
    /// generic type, non-scalar leaf, budget exhaustion, ambiguous spelling)
    /// returns `None`, which fails the entire clause closed.
    fn parse_projection_chain(&mut self, head: &'a str) -> Option<SnippetExpr> {
        // A projection off the ensures result binding has no signature entry
        // and must not be silently reinterpreted as a plain variable.
        if matches!(
            self.result_binding,
            Some(
                SnippetResultBinding::ClosureReference(binding)
                    | SnippetResultBinding::NativeValue(binding)
            ) if head == binding
        ) {
            return None;
        }
        let mut authored = head.to_string();
        while self.eat(&SnippetToken::Dot) {
            let segment = match self.bump()? {
                // A named struct field (`storage`) or a tuple index (`0`).
                SnippetToken::Ident(segment) => segment,
                // A tuple index is the CANONICAL bare-decimal spelling and
                // nothing else. `0_0` and `0x0` denote field 0, but they are
                // not the name `place_to_var_name` mints for it, and
                // `spec_parse` re-checks that exact canonicality on the text
                // this function produces — so admitting a respelled index here
                // would build a place nothing downstream resolves, and fail the
                // whole clause at a boundary that could no longer say why.
                SnippetToken::Int { spelling, value } if spelling == value.to_string() => spelling,
                _ => return None,
            };
            // `base.method(..)` is a CALL, not a place: it has no stable name
            // and must keep failing closed.
            if self.peek() == Some(&SnippetToken::LParen) {
                return None;
            }
            authored.push('.');
            authored.push_str(segment);
        }
        let Some(canonical) = self.projections.resolve(&authored) else {
            // Attribution only — the refusal itself is unchanged and still
            // fails the whole clause closed. Record the FIRST miss so a
            // diagnostic can name the chain rather than its head.
            if self.projection_refusal.is_none() {
                self.projection_refusal = Some(authored);
            }
            return None;
        };
        match self.projections.epoch(&authored) {
            LeafEpoch::Primed => self.saw_primed = true,
            LeafEpoch::MutPointeeUnprimed => self.saw_unprimed_mut_pointee = true,
            LeafEpoch::Plain => {}
        }
        Some(SnippetExpr {
            text: canonical.to_string(),
            // The leaf's exact sort is enforced downstream from the signature
            // domains (`native_function_clause_is_source_typed` and
            // `query_proposition_from_formula`), which are authoritative.
            ty: SnippetExprTy::Ambiguous,
            bool_literal: None,
        })
    }

    fn parse_ident(&mut self, name: &'a str) -> Option<SnippetExpr> {
        // `x'` for a scalar `x: &mut T` names its final value, through the same
        // resolution as a primed chain (see `LeafEpoch`). Any other primed name has no
        // place and fails the clause closed.
        if name.ends_with('\'') {
            let canonical = self.projections.resolve(name)?;
            self.saw_primed = true;
            return Some(SnippetExpr {
                text: canonical.to_string(),
                ty: SnippetExprTy::Ambiguous,
                bool_literal: None,
            });
        }
        if self.syntax == SnippetSyntax::AttributeCompatibility
            && name == "old"
            && self.eat(&SnippetToken::LParen)
        {
            let SnippetToken::Ident(inner) = self.bump()? else { return None };
            if matches!(
                self.result_binding,
                Some(SnippetResultBinding::ClosureReference(binding)
                    | SnippetResultBinding::NativeValue(binding)) if inner == binding
            ) || !self.eat(&SnippetToken::RParen)
            {
                return None;
            }
            return Some(SnippetExpr {
                text: format!("old({inner})"),
                ty: SnippetExprTy::Ambiguous,
                bool_literal: None,
            });
        }
        if matches!(name, "forall" | "exists") {
            if self.syntax == SnippetSyntax::AttributeCompatibility
                && self.eat(&SnippetToken::LParen)
            {
                return self.parse_compat_quantifier(name);
            }
            if self.syntax == SnippetSyntax::Native
                && matches!(self.peek(), Some(SnippetToken::Ident(_)))
            {
                return self.parse_native_quantifier(name);
            }
        }
        match name {
            "true" => Some(SnippetExpr {
                text: "true".to_string(),
                ty: SnippetExprTy::Bool,
                bool_literal: Some(true),
            }),
            "false" => Some(SnippetExpr {
                text: "false".to_string(),
                ty: SnippetExprTy::Bool,
                bool_literal: Some(false),
            }),
            // The return-place vocabulary (`result`, `_0`) denotes a value that
            // exists only where a result binding is in scope, i.e. an `ensures`
            // clause. With no binding — a `requires` clause — the generic
            // identifier arm below would hand the reserved spelling to
            // `trust_types::parse_spec_expr`, which maps it to `_0`, so
            // `#[trust::requires(result == 0)]` became a definition-ENTRY
            // assumption over the return place. `requires` is the ONLY clause
            // that is assumed, so that is the one place the reserved spelling
            // must not reach.
            //
            // The rule is on the BINDING, not on the origin or the clause
            // keyword, so it also covers every other bindingless kind that
            // reaches this parser (`Invariant`, `Assumes`, `Asserts`, ...) —
            // each of them is assumption-shaped, and none of them has a return
            // value for `result` to denote. The native `requires` path never
            // reaches here in production: `lower_predicate` routes it through
            // `lower_native_clause` / `validate_native_clause_body`, which
            // already errors with "`result` is only allowed in an ensures
            // clause" (tests/ui/trust/typed_citation_result_scope.rs).
            _ if self.result_binding.is_none()
                && trust_types::source_contract_synthetic_name_collision(name)
                    == Some(trust_types::SourceContractSyntheticNameCollision::ReturnPlace) =>
            {
                None
            }
            _ if matches!(
                self.result_binding,
                Some(SnippetResultBinding::ClosureReference(binding)) if name == binding
            ) =>
            {
                None
            }
            _ if matches!(
                self.result_binding,
                Some(SnippetResultBinding::NativeValue(binding)) if name == binding
            ) =>
            {
                Some(SnippetExpr {
                    text: ENSURES_RESULT_BINDING.to_string(),
                    ty: SnippetExprTy::Ambiguous,
                    bool_literal: None,
                })
            }
            _ => Some(SnippetExpr {
                text: name.to_string(),
                ty: SnippetExprTy::Ambiguous,
                bool_literal: None,
            }),
        }
    }

    /// Parse the legacy attribute compatibility quantifier surface:
    /// `forall(i, lo..hi, predicate)` / `exists(i, lo..hi, predicate)`.
    fn parse_compat_quantifier(&mut self, quantifier: &'a str) -> Option<SnippetExpr> {
        let SnippetToken::Ident(binding) = self.bump()? else { return None };
        if !self.eat(&SnippetToken::Comma) {
            return None;
        }
        let lo = self.parse_additive()?;
        if !lo.ty.can_be_value() || !self.eat(&SnippetToken::DotDot) {
            return None;
        }
        let hi = self.parse_additive()?;
        if !hi.ty.can_be_value() || !self.eat(&SnippetToken::Comma) {
            return None;
        }
        let body = self.parse_implies()?;
        if !body.ty.can_be_bool() || !self.eat(&SnippetToken::RParen) {
            return None;
        }
        Some(SnippetExpr {
            text: format!("{quantifier}({binding}, {}..{}, {})", lo.text, hi.text, body.text),
            ty: SnippetExprTy::Bool,
            bool_literal: None,
        })
    }

    /// Parse the first-class Lean-shaped binder surface:
    /// `forall i j: usize, predicate` / `exists x: T, predicate`.
    ///
    /// One type annotation may bind multiple adjacent names, matching the
    /// ratified grammar. Distinct binder types are expressed by nesting, just
    /// as in Lean (`forall i: usize, forall flag: bool, ...`).
    fn parse_native_quantifier(&mut self, quantifier: &'a str) -> Option<SnippetExpr> {
        let mut bindings = Vec::new();
        loop {
            let Some(SnippetToken::Ident(binding)) = self.peek().cloned() else {
                break;
            };
            if binding.contains('\'')
                || matches!(binding, "true" | "false" | "result" | "forall" | "exists")
                || bindings.contains(&binding)
            {
                return None;
            }
            self.bump()?;
            bindings.push(binding);
        }
        if bindings.is_empty() || !self.eat(&SnippetToken::Colon) {
            return None;
        }
        let SnippetToken::Ident(ty) = self.bump()? else { return None };
        if ty.contains('\'') || !self.eat(&SnippetToken::Comma) {
            return None;
        }
        let body = self.parse_implies()?;
        if !body.ty.can_be_bool() {
            return None;
        }
        Some(SnippetExpr {
            text: format!("{quantifier} {}: {ty}, {}", bindings.join(" "), body.text),
            ty: SnippetExprTy::Bool,
            bool_literal: None,
        })
    }

    // Prefix `*` deref. Two shapes:
    //   * `*result` — the ensures return binding. The deref IS the value, so fold
    //     it to the canonical result token (matches the HIR `lower_deref_expr`).
    //   * `*a` where `a` is a reference PARAMETER (`#[requires(*a <= 100)]`,
    //     `a: &u32`). PRESERVE the deref as prefix `*a` text: the body names the
    //     referent with a suffix `*` (`place_to_var_name`), and the crate-side
    //     spec parser (`spec_parse::parse_unary`) lowers a prefix `*a` to
    //     `Var("a*")` to match — so emitting `*a` (rather than rejecting) makes
    //     the predicate a real, body-connected obligation instead of an
    //     `Unsupported` false rejection. SOUND: `a*` is a free term the VC layer
    //     binds to the pointee, so the predicate can only fail to prove.
    fn parse_deref(&mut self) -> Option<SnippetExpr> {
        match self.bump()? {
            SnippetToken::Ident(name)
                if matches!(
                    self.result_binding,
                    Some(SnippetResultBinding::ClosureReference(binding)) if name == binding
                ) =>
            {
                Some(SnippetExpr {
                    text: ENSURES_RESULT_BINDING.to_string(),
                    ty: SnippetExprTy::Ambiguous,
                    bool_literal: None,
                })
            }
            SnippetToken::Ident(name)
                if matches!(
                    self.result_binding,
                    Some(SnippetResultBinding::NativeValue(binding)) if name == binding
                ) =>
            {
                None
            }
            // `*x'` is not a D2 spelling: the prime already names the pointee's final
            // value (`x'`).
            SnippetToken::Ident(name) if name.ends_with('\'') => None,
            SnippetToken::Ident(name) => {
                if self.projections.mut_params.contains(name) {
                    self.saw_unprimed_mut_pointee = true;
                }
                Some(SnippetExpr {
                    text: format!("*{name}"),
                    ty: SnippetExprTy::Ambiguous,
                    bool_literal: None,
                })
            }
            _ => None,
        }
    }
}

/// Tokenize one contract predicate.
///
/// `literal_refusal` is an OUT-PARAMETER, and it is the reason this function
/// takes one at all: a numeric literal it cannot read fails the whole clause,
/// and until 2026-08-29 that failure was indistinguishable from every other
/// parse failure — the caller returned `None`, the clause became `Unsupported`,
/// and an author who wrote `ensures result <= 999_999_999` got two UNKNOWN rows
/// and no diagnostic (§13.1, `docs/STRICT_VERIFICATION_FRAGMENT.md`). When the
/// refusal IS attributable to a literal, it is recorded here so
/// `lower_contract_snippet` can say so, with the fix (standing ruling v7/D3).
fn tokenize_contract_snippet<'a>(
    input: &'a str,
    syntax: SnippetSyntax,
    literal_refusal: &mut Option<trust_types::int_literal::IntLiteralRefusal>,
) -> Option<Vec<SnippetToken<'a>>> {
    let bytes = input.as_bytes();
    let mut tokens = Vec::new();
    let mut index = 0usize;

    while index < bytes.len() {
        let byte = bytes[index];
        if byte.is_ascii_whitespace() {
            index += 1;
            continue;
        }

        if byte.is_ascii_digit() {
            let start = index;
            // Rust's integer-literal token SHAPE, not just its decimal digits:
            // a digit followed by alphanumerics and `_`. Lexing the whole run
            // is what makes `999_999_999`, `0x3B9AC9FF` and `1000u32` ONE
            // literal instead of an integer followed by a stray identifier —
            // the shape that used to make the entire clause unparseable. It
            // stops before `.`, so a projection separator and the `..` range
            // token are unaffected.
            index += trust_types::int_literal::int_literal_run_len(&input[index..]);
            let spelling = &input[start..index];

            // A digit run immediately followed by `.<digit>` is a FLOAT
            // literal — unless the run is itself a tuple-field index, where
            // `s.0.0` is two nested segments and not `s.<0.0>`. This lane has
            // no float support in either direction, and saying so is the whole
            // point: closing only the integer half would leave the next
            // spelling exactly as invisible as the separator was.
            let field_index_context = matches!(tokens.last(), Some(SnippetToken::Dot));
            if !field_index_context
                && index + 1 < bytes.len()
                && bytes[index] == b'.'
                && bytes[index + 1].is_ascii_digit()
            {
                let mut end = index + 1;
                end += trust_types::int_literal::int_literal_run_len(&input[end..]);
                *literal_refusal = Some(trust_types::int_literal::IntLiteralRefusal {
                    literal: input[start..end].to_string(),
                    reason: "a contract predicate on this lane carries integers only".to_string(),
                    fix: "state the bound over integers — scale both sides by a constant \
                          (`10 * result <= 15` for `result <= 1.5`) — or move the comparison \
                          into a helper whose result the clause bounds"
                        .to_string(),
                });
                return None;
            }

            match trust_types::int_literal::read_contract_int_literal(spelling) {
                Ok(value) => tokens.push(SnippetToken::Int { spelling, value }),
                Err(refusal) => {
                    *literal_refusal = Some(refusal);
                    return None;
                }
            }
            continue;
        }

        if byte.is_ascii_alphabetic() || byte == b'_' {
            let start = index;
            index += 1;
            while index < bytes.len()
                && (bytes[index].is_ascii_alphanumeric() || bytes[index] == b'_')
            {
                index += 1;
            }
            if index < bytes.len() && bytes[index] == b'\'' {
                if syntax != SnippetSyntax::Native {
                    return None;
                }
                while index < bytes.len() && bytes[index] == b'\'' {
                    index += 1;
                }
            }
            tokens.push(SnippetToken::Ident(&input[start..index]));
            continue;
        }

        if input.as_bytes()[index..].starts_with(b"==>") {
            index += 3;
            tokens.push(SnippetToken::Implies);
            continue;
        }

        let token = match (byte, bytes.get(index + 1).copied()) {
            (b'>', Some(b'=')) => {
                index += 2;
                SnippetToken::Ge
            }
            (b'<', Some(b'=')) => {
                index += 2;
                SnippetToken::Le
            }
            (b'=', Some(b'=')) => {
                index += 2;
                SnippetToken::EqEq
            }
            (b'=', Some(b'>')) => {
                index += 2;
                SnippetToken::CompatImplies
            }
            (b'!', Some(b'=')) => {
                index += 2;
                SnippetToken::Ne
            }
            (b'&', Some(b'&')) => {
                index += 2;
                SnippetToken::AndAnd
            }
            (b'|', Some(b'|')) => {
                index += 2;
                SnippetToken::OrOr
            }
            (b'>', _) => {
                index += 1;
                SnippetToken::Gt
            }
            (b'<', _) => {
                index += 1;
                SnippetToken::Lt
            }
            (b'!', _) => {
                index += 1;
                SnippetToken::Bang
            }
            (b'*', _) => {
                index += 1;
                SnippetToken::Star
            }
            (b'/', _) => {
                index += 1;
                SnippetToken::Slash
            }
            (b'%', _) => {
                index += 1;
                SnippetToken::Percent
            }
            (b'+', _) => {
                index += 1;
                SnippetToken::Plus
            }
            (b'-', _) => {
                index += 1;
                SnippetToken::Minus
            }
            (b'(', _) => {
                index += 1;
                SnippetToken::LParen
            }
            (b')', _) => {
                index += 1;
                SnippetToken::RParen
            }
            (b',', _) => {
                index += 1;
                SnippetToken::Comma
            }
            (b':', _) => {
                index += 1;
                SnippetToken::Colon
            }
            (b'.', Some(b'.')) => {
                index += 2;
                SnippetToken::DotDot
            }
            // A LONE `.` separates projection segments. `DotDot` is matched
            // above, so nothing reaching here can be a range. Lexing it does
            // not admit anything on its own: `SnippetParser` accepts a `Dot`
            // only inside a projection chain whose every segment resolves to
            // an exact field index through `ProjectionEnvironment`, and an
            // unresolved chain still returns `None` for the whole clause.
            (b'.', _) => {
                index += 1;
                SnippetToken::Dot
            }
            _ => return None,
        };

        tokens.push(token);
    }

    Some(tokens)
}

fn snippet_comparison_op(token: &SnippetToken<'_>) -> Option<(&'static str, SnippetBinaryKind)> {
    match token {
        SnippetToken::Gt => Some((">", SnippetBinaryKind::Ordering)),
        SnippetToken::Ge => Some((">=", SnippetBinaryKind::Ordering)),
        SnippetToken::Lt => Some(("<", SnippetBinaryKind::Ordering)),
        SnippetToken::Le => Some(("<=", SnippetBinaryKind::Ordering)),
        SnippetToken::EqEq => Some(("==", SnippetBinaryKind::Equality)),
        SnippetToken::Ne => Some(("!=", SnippetBinaryKind::Equality)),
        _ => None,
    }
}

#[derive(Copy, Clone)]
enum SnippetBinaryKind {
    Logic,
    Equality,
    Ordering,
    // Integer arithmetic (`+`/`-`): produces a VALUE, not a Bool. Lets the snippet
    // (text) fallback lower a predicate with an arithmetic operand, e.g.
    // `(result) == ((x) + (1))` — reached when a `#[requires]` forces the
    // `#[ensures]` down the snippet path instead of the HIR lowerer.
    Arith,
}

fn lower_snippet_binary(
    op: &'static str,
    lhs: SnippetExpr,
    rhs: SnippetExpr,
    kind: SnippetBinaryKind,
) -> Option<SnippetExpr> {
    if let SnippetBinaryKind::Arith = kind {
        // Arithmetic yields a VALUE, not a Bool.
        return (lhs.ty.can_be_value() && rhs.ty.can_be_value()).then(|| SnippetExpr {
            text: format!("({}) {op} ({})", lhs.text, rhs.text),
            ty: SnippetExprTy::Value,
            bool_literal: None,
        });
    }
    let supported = match kind {
        SnippetBinaryKind::Logic => lhs.ty.can_be_bool() && rhs.ty.can_be_bool(),
        SnippetBinaryKind::Equality => lhs.ty.can_equal(rhs.ty),
        SnippetBinaryKind::Ordering => lhs.ty.can_be_value() && rhs.ty.can_be_value(),
        SnippetBinaryKind::Arith => unreachable!("handled above"),
    };
    supported.then(|| SnippetExpr {
        text: format!("({}) {op} ({})", lhs.text, rhs.text),
        ty: SnippetExprTy::Bool,
        bool_literal: None,
    })
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum SnippetExprTy {
    Bool,
    Value,
    Ambiguous,
}

impl SnippetExprTy {
    fn can_be_bool(self) -> bool {
        matches!(self, Self::Bool | Self::Ambiguous)
    }

    fn can_be_value(self) -> bool {
        matches!(self, Self::Value | Self::Ambiguous)
    }

    fn can_equal(self, other: Self) -> bool {
        matches!(
            (self, other),
            (Self::Bool, Self::Bool)
                | (Self::Value, Self::Value)
                | (Self::Ambiguous, _)
                | (_, Self::Ambiguous)
        )
    }
}

struct SnippetExpr {
    text: String,
    ty: SnippetExprTy,
    bool_literal: Option<bool>,
}

impl SnippetExpr {
    fn into_bool(mut self) -> Self {
        self.ty = SnippetExprTy::Bool;
        self
    }
}

fn is_opaque_summary_predicate(kind: &TrustContractPredicateKind) -> bool {
    match kind {
        TrustContractPredicateKind::Opaque { text } => {
            !text.as_str().starts_with(LOWERED_COMPILER_CONTRACT_PREFIX)
        }
        TrustContractPredicateKind::Unsupported { .. } => true,
        _ => false,
    }
}

/// R4 §1 recognition (increment 1 of the typed-citation seam; design note
/// 2026-07-22-r4-remaining-lanes-design.md §1a): every called identifier in
/// the snippet, in source order — a hand lexer, no resolution. The caller
/// checks each against the island environment; membership there is the only
/// authority consulted.
pub(crate) fn called_identifiers(snippet: &str) -> Vec<String> {
    lexed_identifiers(snippet, true)
}

/// The complement of [`called_identifiers`]: every identifier in the snippet
/// that is NOT followed by `(`, in source order — the BARE spelling a
/// zero-arity island definition is cited with (`result == forty_two_isl`, e6
/// probe f04). Same hand lexer, no resolution; candidates only. The caller
/// filters out the names Rust bindings shadow (`result`, parameters) and
/// checks the remainder against the island environment, whose membership is
/// the only authority consulted.
pub(crate) fn bare_identifiers(snippet: &str) -> Vec<String> {
    lexed_identifiers(snippet, false)
}

/// The shared hand lexer behind [`called_identifiers`] and
/// [`bare_identifiers`]: every identifier in the snippet, in source order,
/// split by whether a `(` follows (whitespace-tolerantly).
fn lexed_identifiers(snippet: &str, called: bool) -> Vec<String> {
    let bytes = snippet.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i].is_ascii_alphabetic() || bytes[i] == b'_' {
            let start = i;
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
            let mut j = i;
            while j < bytes.len() && bytes[j].is_ascii_whitespace() {
                j += 1;
            }
            let is_called = j < bytes.len() && bytes[j] == b'(';
            if is_called == called {
                out.push(snippet[start..i].to_string());
            }
        } else {
            i += 1;
        }
    }
    out
}

/// R4 §1 recognition: the first cited identifier — called, or bare (the
/// zero-arity citation spelling, e6 probe f04) — that names an unfoldable
/// island DEFINITION in this session's kernel-checked environment, if any.
/// Read-only against the [`crate::trust_verify::SessionIslandEnv`] stash;
/// `None` when islands are unchecked, the session is tainted, or no callee
/// matches — the diagnostic then keeps its generic attribution. This refines
/// MESSAGES only; the predicate still refuses (fail-closed) until the typed
/// citation row and its kernel-side discharge land per the seam map.
fn island_cited_callee(tcx: TyCtxt<'_>, snippet: &str) -> Option<String> {
    // Called identifiers first (the historical candidates), then bare ones —
    // a zero-arity island definition cited with no argument list (e6 probe
    // f04) deserves the same refined attribution. Message refinement only;
    // membership in the island environment below stays the sole authority.
    let mut candidates = called_identifiers(snippet);
    candidates.extend(bare_identifiers(snippet));
    if candidates.is_empty() {
        return None;
    }
    let env = crate::trust_verify::session_island_env(tcx.sess);
    if crate::trust_verify::trust_env_var_present("TRUST_ISLAND_CITE_TRACE") {
        eprintln!(
            "TRUST_ISLAND_CITE_TRACE: stash_populated={} candidates={candidates:?}",
            env.is_some()
        );
    }
    let env = env?;
    candidates
        .into_iter()
        .find(|name| trust_certify::clean_island::island_definition_value(&env, name).is_some())
}

fn unsupported_predicate_reason(tcx: TyCtxt<'_>, span: Span) -> Symbol {
    let source_map = tcx.sess.source_map();
    let detail = match source_map.span_to_snippet(span) {
        Ok(snippet) => {
            let snippet = snippet.trim();
            if let Some(identifier) = primed_identifier_in_contract_snippet(snippet) {
                // Trust (D2 primes, 2026-09-30): name the whole rule. From the snippet
                // alone it cannot be told which part refused the clause.
                format!(
                    "primed post-state identifier `{identifier}` has no verified MIR state \
                     binding here: a prime is bound only in an uncited native `ensures`, on a \
                     `&mut` parameter's pointee (`self'.field`, or `x'` for a scalar \
                     `x: &mut T`), and never beside an unprimed read of a `&mut` pointee, \
                     which still reads the final value too"
                )
            } else if let Some(name) = island_cited_callee(tcx, snippet) {
                format!(
                    "island citation `{name}` awaits typed-citation discharge (R4 §1); \
                     unsupported contract predicate expression `{snippet}`"
                )
            } else {
                format!("unsupported contract predicate expression `{snippet}`")
            }
        }
        Err(_) => {
            format!(
                "unsupported contract predicate expression at {}",
                embeddable_span_location(source_map, span)
            )
        }
    };
    Symbol::intern(&detail)
}

/// Trust (WS5.9 review, F-117): the `file:line:col: line:col` location of `span`, in the
/// shape of `SourceMap::span_to_diagnostic_string` but with the file rendered
/// `prefer_remapped_unconditionally` — the ONE rendering every file string that reaches a
/// published module takes.
///
/// `unsupported_predicate_reason` needs it because its text is not a diagnostic only: an
/// `Unsupported { reason }` clause is carried into the published trust-ir module as the
/// contract-disclosure `SpecModule` row (`trust_thir_lower::contract_disclosure`,
/// `{"unsupported":{"reason":...}}`). `span_to_diagnostic_string` follows the DIAGNOSTICS
/// component of `--remap-path-scope`, so under cargo's `trim-paths` default (`object`)
/// that row kept the checkout path while `Module.files` lost it: one module, two
/// renderings, and G8 byte identity lost on exactly the crates whose contract clause has no
/// snippet. Without any `--remap-path-prefix` the rendering is the local name, so the text
/// is unchanged. The sibling of `crate_module.rs::embeddable_span_string`, which renders
/// `SpecAnchor.span` the same way.
fn embeddable_span_location(source_map: &rustc_span::source_map::SourceMap, span: Span) -> String {
    let (source_file, lo_line, lo_col, hi_line, hi_col) = source_map.span_to_location_info(span);
    match source_file {
        Some(sf) => format!(
            "{}:{lo_line}:{lo_col}: {hi_line}:{hi_col}",
            sf.name.prefer_remapped_unconditionally()
        ),
        None => "no-location".to_string(),
    }
}

#[cfg(test)]
mod tests;

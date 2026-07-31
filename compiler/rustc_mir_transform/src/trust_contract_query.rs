//! Trust: Query provider for compiler-native Trust contracts.
//!
use std::collections::{BTreeMap, BTreeSet};

use rustc_ast::ast::{BinOpKind, LitKind, UnOp};
use rustc_data_structures::fx::FxHashMap;
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
use rustc_middle::ty::{self, Ty, TyCtxt, TypeckResults};
use rustc_span::def_id::LocalDefId;
use rustc_span::{Span, Symbol};

const LOWERED_COMPILER_CONTRACT_PREFIX: &str = "__trust_lowered_compiler_contract__:";
const ENSURES_RESULT_BINDING: &str = "result";

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
    let function_source_sorts = function_source_sorts(body, typeck_results);
    let function_collection_domains =
        function_collection_element_domains(tcx, body, typeck_results);
    for authored_clause in authored_clauses {
        let clause = authored_clause.clause;
        let predicate = lower_predicate(
            tcx,
            typeck_results,
            body.value,
            clause.predicate_hir_id,
            clause.span,
            clause.payload,
            authored_clause.kind,
            clause.origin,
            &signature_domains,
            ContractPayloadContext::Function {
                source_sorts: &function_source_sorts,
                variable_domains: &signature_domains,
                collection_domains: &function_collection_domains,
            },
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
        let (loop_variable_domains, loop_collection_domains, loop_source_bindings) =
            visible_loop_variable_domains(
                tcx,
                local_def_id,
                body,
                typeck_results,
                clause.loop_id,
                &signature_domains,
            );
        let predicate = lower_predicate(
            tcx,
            typeck_results,
            body.value,
            None,
            clause.payload_span,
            Some(clause.payload),
            kind,
            ContractClauseOrigin::Native,
            &signature_domains,
            ContractPayloadContext::Loop {
                source_sorts: &loop_source_sorts,
                variable_domains: &loop_variable_domains,
                collection_domains: &loop_collection_domains,
                source_bindings: &loop_source_bindings,
            },
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
    typeck_results: &TypeckResults<'tcx>,
    body: &'tcx Expr<'tcx>,
    predicate_hir_id: Option<HirId>,
    span: Span,
    payload: Option<Symbol>,
    contract_kind: TrustContractKind,
    origin: ContractClauseOrigin,
    signature_domains: &[LoweredVariableDomain],
    context: ContractPayloadContext<'_>,
) -> TrustContractPredicate<'tcx> {
    // First-class native clauses are verifier-language parser islands rather
    // than Rust HIR expressions. Validate the exact supported roles with their
    // exact visible domains at this earliest always-on boundary.
    let native_clause_environment = match context {
        ContractPayloadContext::Function {
            source_sorts,
            variable_domains,
            collection_domains,
        } if origin == ContractClauseOrigin::Native
            && matches!(
                contract_kind,
                TrustContractKind::Requires | TrustContractKind::Decreases
            ) =>
        {
            Some((source_sorts, variable_domains, collection_domains))
        }
        ContractPayloadContext::Loop {
            source_sorts,
            variable_domains,
            collection_domains,
            ..
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
    let validated_native_clause = native_clause_environment.map(
        |(source_sorts, variable_domains, collection_domains)| {
            lower_native_clause(
                tcx,
                span,
                payload,
                contract_kind,
                source_sorts,
                variable_domains,
                collection_domains,
            )
            .unwrap_or_else(|reason| {
                let keyword = match contract_kind {
                    TrustContractKind::Requires => "requires",
                    TrustContractKind::Decreases => "decreases",
                    _ => "invariant",
                };
                tcx.dcx().span_err(span, format!("invalid `{keyword}` clause: {reason}"));
                TrustContractPredicateKind::Unsupported { reason: Symbol::intern(&reason) }
            })
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
        validated_native_clause
            .or_else(|| {
                lower_contract_snippet(tcx, span, payload, contract_kind, origin, signature_domains)
            })
            .unwrap_or_else(|| TrustContractPredicateKind::Unsupported {
                reason: unsupported_predicate_reason(tcx, span),
            })
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
    TrustContractPredicate { ty, kind, source_bindings }
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
    // to `xs_len`; `native_clause_variable_domains` supplies the exact
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
/// query proposition vocabulary. Only an exact, unshadowed collection parameter
/// descriptor authorizes either synthetic leaf, and a fixed-array literal must
/// be in range. Unknown or loop-local projections return None and keep the
/// clause Opaque.
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
            // `xs.len()` and a real scalar parameter named `xs_len` collapse
            // to the same parser leaf. Never let the scalar's signature domain
            // authorize that ambiguous projection identity; keep the clause
            // opaque so every downstream proof lane fails closed.
            if name.strip_suffix("_len").is_some_and(|base| {
                matches!(source_sorts.get(base), Some(trust_types::Sort::Array(..)))
            }) {
                return None;
            }
            continue;
        }
        if let Some(base) = name.strip_suffix("_len") {
            if !matches!(source_sorts.get(base), Some(trust_types::Sort::Array(..))) {
                return None;
            }
            // A source sort proves only that some visible HIR binding with
            // this spelling is a collection. The descriptor is minted only
            // for the exact unshadowed parameter collection that downstream
            // MIR can rebind without guessing source identity.
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
/// has Array sort; the parameter descriptor checked by the caller supplies
/// source identity, exact element domain, and any fixed-array bound. Keeping
/// those authorities separate prevents an arbitrary parser variable or a
/// shadowing loop local from borrowing a parameter collection's identity.
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
    if let Some(name) = source_sorts
        .keys()
        .find(|name| trust_types::source_contract_synthetic_name_collision(name).is_some())
    {
        return Err(format!(
            "visible binding `{name}` collides with the synthetic contract-variable namespace"
        ));
    }
    let clause = match contract_kind {
        TrustContractKind::Requires => trust_types::SourceContractClause::Requires,
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
    // become synthetic solver leaves such as `xs_len`, which are not source
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
fn reject_unrepresentable_contract_parameter_names<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &'tcx rustc_hir::Body<'tcx>,
) -> bool {
    struct Collector<'tcx> {
        tcx: TyCtxt<'tcx>,
        rejected: bool,
        parameter_ids: BTreeMap<String, u32>,
        ambiguous_names: BTreeSet<String>,
    }

    impl<'tcx> Visitor<'tcx> for Collector<'tcx> {
        fn visit_pat(&mut self, pat: &'tcx Pat<'tcx>) {
            if let PatKind::Binding(_, canonical_id, ident, _) = pat.kind
                && canonical_id == pat.hir_id
            {
                let name = ident.name.to_string();
                let id = canonical_id.local_id.as_u32();
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
                        trust_types::SourceContractSyntheticNameCollision::Projection => format!(
                            "parameter `{name}` collides with the source-contract synthetic projection namespace"
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

    let mut collector = Collector {
        tcx,
        rejected: false,
        parameter_ids: BTreeMap::new(),
        ambiguous_names: BTreeSet::new(),
    };
    for param in body.params {
        collector.visit_pat(param.pat);
    }
    collector.rejected
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

    let lowerer =
        ExprLowerer { tcx, typeck_results, result_binding: None, pat_bindings: Vec::new() };
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
    let lowerer =
        ExprLowerer { tcx, typeck_results, result_binding: None, pat_bindings: Vec::new() };
    lowerer.lower_predicate(body.value)
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
    };
    lowerer.lower_predicate(body.value)
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
    span: Span,
    payload: Option<Symbol>,
    contract_kind: TrustContractKind,
    origin: ContractClauseOrigin,
    signature_domains: &[LoweredVariableDomain],
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
    lower_contract_snippet_body_with_domains(body, contract_kind, origin, signature_domains)
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
    let mut depth = 0usize;
    for (idx, ch) in text[open_idx..].char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(open_idx + idx);
                }
            }
            _ => {}
        }
    }
    None
}

#[cfg(test)]
fn lower_contract_snippet_body(
    body: &str,
    contract_kind: TrustContractKind,
    origin: ContractClauseOrigin,
) -> Option<TrustContractPredicateKind> {
    lower_contract_snippet_body_with_domains(body, contract_kind, origin, &[])
}

fn lower_contract_snippet_body_with_domains(
    body: &str,
    contract_kind: TrustContractKind,
    origin: ContractClauseOrigin,
    signature_domains: &[LoweredVariableDomain],
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
    let (expr, result_binding) = if contract_kind == TrustContractKind::Ensures {
        match origin {
            ContractClauseOrigin::Attribute => {
                let (expr, result_binding) = ensures_closure_snippet_body(body)?;
                (expr, Some(SnippetResultBinding::ClosureReference(result_binding)))
            }
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
    if primed_identifier_in_contract_snippet(expr.trim()).is_some() {
        return None;
    }
    let lowered = SnippetParser::parse(expr.trim(), result_binding, syntax)?;
    if let Some(value) = lowered.bool_literal {
        Some(TrustContractPredicateKind::BoolLiteral { value })
    } else if trust_types::parse_spec_expr(&lowered.text).is_some()
        && (origin != ContractClauseOrigin::Native
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

/// Return the first ASCII identifier carrying one or more trailing prime
/// marks. Native contract identifiers are ASCII today, matching the snippet
/// tokenizer. This small scanner remains usable for diagnostics even when the
/// rest of a malformed clause cannot be tokenized.
fn primed_identifier_in_contract_snippet(input: &str) -> Option<&str> {
    let bytes = input.as_bytes();
    let mut index = 0usize;
    while index < bytes.len() {
        if bytes[index].is_ascii_alphabetic() || bytes[index] == b'_' {
            let start = index;
            index += 1;
            while index < bytes.len()
                && (bytes[index].is_ascii_alphanumeric() || bytes[index] == b'_')
            {
                index += 1;
            }
            if index < bytes.len() && bytes[index] == b'\'' {
                while index < bytes.len() && bytes[index] == b'\'' {
                    index += 1;
                }
                return Some(&input[start..index]);
            }
        } else {
            index += 1;
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
            ExprKind::Path(qpath) => self.lower_path_expr(expr, qpath),
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
                if !value_preserving_int_cast(src, dst) {
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
            // the spec parser models with the synthetic sign var `<recv>_sign` and
            // the trichotomy `_sign > 0` / `_sign < 0` / `_sign == 0`. The set is
            // CLOSED: any other method REJECTS (returns None) — never a guess, so a
            // method we do not exactly model can never silently weaken the VC.
            //
            // SEMANTICS (the predicate text emitted, read by spec_parse):
            //   recv.is_positive() ↦ "<recv>.is_positive()"  ⟹  <recv>_sign > 0
            //   recv.is_negative() ↦ "<recv>.is_negative()"  ⟹  <recv>_sign < 0
            //   recv.is_zero()     ↦ "<recv>.is_zero()"      ⟹  <recv>_sign == 0
            // The receiver must itself lower (to a value-typed term); the result is
            // a Bool. The synthetic `_sign` term is a free variable until the VC
            // layer links it to the receiver's value, so the predicate is
            // fail-closed (can only fail to prove, never vacuously prove).
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
                // `result.is_none()` as `_0_discr == 0`, `result.is_some()` as
                // `_0_discr != 0`, and `result.unwrap()` as the payload term
                // `_0_value` (`map_var_name("result") == "_0"`), which the vcgen
                // contract lane grounds to the body's in-body `Some`/`None`
                // construction (`enum_return_grounded_model_vars` + the discr/value
                // return pin). This lets an `Option`-returning function carry a live
                // `#[ensures(|r| r.is_none() || low <= r.unwrap() && r.unwrap() <= high)]`
                // that PROVES, instead of the whole predicate being rejected as an
                // unsupported contract expression. Gated to the EXACT result binding
                // of `Option` type (diagnostic item, not a name match — see
                // `receiver_is_result_option`), and for `unwrap` an INTEGER payload
                // (matching the `Sort::Int` the spec parser mints for `_0_value`);
                // anything else falls through to the sign allow-list / rejects.
                // SOUND: `_0_discr`/`_0_value` are free until the VC layer pins them
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
                            && lowered_expr_ty(self.typeck_results.expr_ty(expr))
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
                    // Int var `<base>_len`; `.is_empty()` -> `<base>_len == 0`),
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
                    //    minted `<base>_len` var models it exactly. A user type's
                    //    `len` has no such guarantee (an impure/nondeterministic
                    //    `len` under one shared var could vacuously prove
                    //    `x.len() == x.len()` while the runtime check fails).
                    //
                    // 2. The receiver must lower to a projection base STRICTLY
                    //    UNDER the Ok-payload term — `result.unwrap().<seg>…` (a
                    //    pat-binding substitution plus at least one projection —
                    //    see `collect_ok_pattern_bindings` /
                    //    `lower_projection_base`). The spec parser then mints
                    //    `_0_value.<seg>…_len`, whose FIRST path segment keeps the
                    //    `_value` marker, so `is_spec_model_var` classifies it as
                    //    a SPEC-MODEL term and an ungroundable predicate routes to
                    //    the fail-closed Unknown (SpecModelUngrounded). Any OTHER
                    //    base would mint a NON-model free var — a parameter `xs`
                    //    gives `xs_len`, the bare `result` gives `_0_len`, and
                    //    even the BARE payload `result.unwrap()` gives
                    //    `_0_value_len` (one undivided segment ending `_len`, NOT
                    //    `_value` — pinned NOT spec-model by trust-vcgen's
                    //    name-shape test) — and the postcondition would become a
                    //    refutable VC satisfiable by havoc: reported Failed with
                    //    a fabricated counterexample. Rejecting here keeps every
                    //    such shape fail-closed (SpecEnsuresUnparseable).
                    //
                    // SOUND: the minted `_0_value…_len` term is free until the VC
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
                let recv = self.lower_expr_text(receiver)?;
                // The receiver of a sign predicate is a number, so it must have
                // lowered to a value-typed term (Int), never a Bool.
                if recv.ty != LoweredExprTy::Int {
                    return None;
                }
                lowered_synthetic_expr(
                    format!("{}.{}()", recv.text, method_str),
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
    /// parser models `result.is_ok()` as `_0_discr != 0` and the substituted bind
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
    /// `<result>.unwrap()` is the spec parser's Ok-payload term (`_0_value`); the
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
        // POSITIVE `is_ok` position (a single `_0_discr` disequality) instead of
        // the negated `!(result.is_ok())` that lowers to a DOUBLE-negated
        // discriminant `Not(Not(Eq(_0_discr, 0)))`. The negated form left the
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
                        // (-> the spec parser's `_0_value…` terms, classified
                        // SPEC-MODEL by `is_spec_model_var` and routed to the
                        // fail-closed SpecModelUngrounded when ungroundable).
                        // Without the substitution the guard minted a FREE var
                        // named after the source binding (`c.0.1` — probe P6),
                        // which is NOT spec-model-shaped: once `_0_discr` grounds
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
        // value's OWNED `Ok` payload (`_0_value…`). Under match ergonomics the
        // closure sees `r: &Result`, so the binding is `&Payload` and a field
        // projection off it records a builtin deref — but that deref is an
        // artifact of the by-reference closure parameter, NOT of the owned
        // returned value the spec term names. Emitting a `(*…)` marker here would
        // desync the contract text from the `_0_value…_len` name the len-witness
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
                    // `_0_discr` grounds via the Result-return grounding.
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
    std::env::var_os("TRUST_E9_DEBUG").is_some()
        || std::env::var_os("TRUST_CONTRACT_LOWER_DEBUG").is_some()
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

fn lowered_contract_text_with_domains_for_class(
    text: String,
    variable_domains: &[LoweredVariableDomain],
    expected_class: PropositionClass,
) -> TrustContractPredicateKind {
    let canonical = Symbol::intern(&format!("{LOWERED_COMPILER_CONTRACT_PREFIX}{text}"));
    if let Some(proposition) = trust_types::parse_spec_expr(&text).as_ref().and_then(|formula| {
        query_proposition_from_formula(formula, variable_domains, expected_class)
    }) {
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

    let (proposition, class) = query_proposition_from_formula_inner(formula, &domains)?;
    (class == expected_class).then_some(proposition)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum PropositionClass {
    Bool,
    Numeric,
}

fn query_proposition_from_formula_inner(
    formula: &trust_types::Formula,
    domains: &FxHashMap<&str, TrustContractPropositionDomain>,
) -> Option<(TrustContractProposition, PropositionClass)> {
    use TrustContractProposition as Proposition;
    use trust_types::Formula;

    let unary = |formula: &Formula| query_proposition_from_formula_inner(formula, domains);
    let binary = |lhs: &Formula, rhs: &Formula| Some((unary(lhs)?, unary(rhs)?));
    match formula {
        Formula::Bool(value) => Some((Proposition::Bool(*value), PropositionClass::Bool)),
        Formula::Int(value) => Some((Proposition::Int(*value), PropositionClass::Numeric)),
        Formula::UInt(value) => Some((Proposition::UInt(*value), PropositionClass::Numeric)),
        Formula::Var(name, _) => {
            let domain = *domains.get(name.as_str())?;
            let class = if domain == TrustContractPropositionDomain::Bool {
                PropositionClass::Bool
            } else {
                PropositionClass::Numeric
            };
            Some((Proposition::Var { name: Symbol::intern(name), domain }, class))
        }
        Formula::SymVar(name, _) => {
            let text = name.as_str();
            let domain = *domains.get(text)?;
            let class = if domain == TrustContractPropositionDomain::Bool {
                PropositionClass::Bool
            } else {
                PropositionClass::Numeric
            };
            Some((Proposition::Var { name: Symbol::intern(text), domain }, class))
        }
        Formula::Not(inner) => {
            let (inner, class) = unary(inner)?;
            (class == PropositionClass::Bool)
                .then_some((Proposition::Not(Box::new(inner)), PropositionClass::Bool))
        }
        Formula::And(terms) | Formula::Or(terms) => {
            let propositions = terms
                .iter()
                .map(|term| {
                    let (term, class) = unary(term)?;
                    (class == PropositionClass::Bool).then_some(term)
                })
                .collect::<Option<Vec<_>>>()?;
            Some((
                if matches!(formula, Formula::And(_)) {
                    Proposition::And(propositions)
                } else {
                    Proposition::Or(propositions)
                },
                PropositionClass::Bool,
            ))
        }
        Formula::Implies(lhs, rhs) => {
            let ((lhs, lhs_class), (rhs, rhs_class)) = binary(lhs, rhs)?;
            (lhs_class == PropositionClass::Bool && rhs_class == PropositionClass::Bool).then_some(
                (Proposition::Implies(Box::new(lhs), Box::new(rhs)), PropositionClass::Bool),
            )
        }
        Formula::Eq(lhs, rhs) => {
            let ((lhs, lhs_class), (rhs, rhs_class)) = binary(lhs, rhs)?;
            (lhs_class == rhs_class)
                .then_some((Proposition::Eq(Box::new(lhs), Box::new(rhs)), PropositionClass::Bool))
        }
        Formula::Lt(lhs, rhs)
        | Formula::Le(lhs, rhs)
        | Formula::Gt(lhs, rhs)
        | Formula::Ge(lhs, rhs) => {
            let ((lhs, lhs_class), (rhs, rhs_class)) = binary(lhs, rhs)?;
            if lhs_class != PropositionClass::Numeric || rhs_class != PropositionClass::Numeric {
                return None;
            }
            let proposition = match formula {
                Formula::Lt(..) => Proposition::Lt(Box::new(lhs), Box::new(rhs)),
                Formula::Le(..) => Proposition::Le(Box::new(lhs), Box::new(rhs)),
                Formula::Gt(..) => Proposition::Gt(Box::new(lhs), Box::new(rhs)),
                Formula::Ge(..) => Proposition::Ge(Box::new(lhs), Box::new(rhs)),
                _ => unreachable!(),
            };
            Some((proposition, PropositionClass::Bool))
        }
        Formula::Add(lhs, rhs)
        | Formula::Sub(lhs, rhs)
        | Formula::Mul(lhs, rhs)
        | Formula::Div(lhs, rhs)
        | Formula::Rem(lhs, rhs) => {
            let ((lhs, lhs_class), (rhs, rhs_class)) = binary(lhs, rhs)?;
            if lhs_class != PropositionClass::Numeric || rhs_class != PropositionClass::Numeric {
                return None;
            }
            let proposition = match formula {
                Formula::Add(..) => Proposition::Add(Box::new(lhs), Box::new(rhs)),
                Formula::Sub(..) => Proposition::Sub(Box::new(lhs), Box::new(rhs)),
                Formula::Mul(..) => Proposition::Mul(Box::new(lhs), Box::new(rhs)),
                Formula::Div(..) => Proposition::Div(Box::new(lhs), Box::new(rhs)),
                Formula::Rem(..) => Proposition::Rem(Box::new(lhs), Box::new(rhs)),
                _ => unreachable!(),
            };
            Some((proposition, PropositionClass::Numeric))
        }
        Formula::Neg(inner) => {
            let (inner, class) = unary(inner)?;
            (class == PropositionClass::Numeric)
                .then_some((Proposition::Neg(Box::new(inner)), PropositionClass::Numeric))
        }
        _ => None,
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum LoweredExprTy {
    Bool,
    Int,
    Float,
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

/// Source-level sort used to elaborate native E4/E5 clauses. Scalars retain
/// their logical Bool/Int sort, while arrays and slices retain their exact
/// element sort for indexing and collection accessors. Other aggregates stay
/// opaque: their names remain in scope, but ordinary fields are rejected until
/// exact source layouts are available.
fn loop_source_sort_from_ty(ty: Ty<'_>) -> Option<trust_types::Sort> {
    match ty.kind() {
        ty::Bool => Some(trust_types::Sort::Bool),
        ty::Int(_) | ty::Uint(_) | ty::Char => Some(trust_types::Sort::Int),
        ty::Array(element, _) | ty::Slice(element) => Some(trust_types::Sort::Array(
            Box::new(trust_types::Sort::Int),
            Box::new(loop_source_sort_from_ty(*element).unwrap_or_else(|| {
                trust_types::Sort::Datatype { name: format!("{element}"), constructors: Vec::new() }
            })),
        )),
        ty::Str => Some(trust_types::Sort::Array(
            Box::new(trust_types::Sort::Int),
            Box::new(trust_types::Sort::Int),
        )),
        ty::Adt(..) | ty::Tuple(..) | ty::Param(..) | ty::Alias(..) => {
            Some(trust_types::Sort::Datatype { name: format!("{ty}"), constructors: Vec::new() })
        }
        _ => None,
    }
}

/// Give a visible Rust binding its verifier-source spelling and sort. Scalar
/// references/pointers require the explicit source dereference `*x`, whose
/// canonical MIR/formula name is `x*`. Slice/array references retain the base
/// spelling because source indexing and `.len()` use Rust's deref coercion.
fn loop_source_binding_from_ty(name: String, ty: Ty<'_>) -> Option<(String, trust_types::Sort)> {
    match ty.kind() {
        ty::Ref(_, inner, _) => {
            let sort = loop_source_sort_from_ty(*inner)?;
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
            let sort = loop_source_sort_from_ty(*inner)?;
            Some((format!("{name}*"), sort))
        }
        _ => loop_source_sort_from_ty(ty).map(|sort| (name, sort)),
    }
}

/// Recover exact source sorts for function parameters used by a native E5
/// clause. Unlike proposition domains, this environment retains aggregate
/// parameters so measures such as `xs.len()` can be admitted without treating
/// a scalar as a collection. This is source/type admission only; MIR extraction
/// still has to rebind every accepted projection before it gains proof authority.
fn function_source_sorts<'tcx>(
    body: &'tcx rustc_hir::Body<'tcx>,
    typeck_results: &TypeckResults<'tcx>,
) -> BTreeMap<String, trust_types::Sort> {
    struct Collector<'a, 'tcx> {
        typeck_results: &'a TypeckResults<'tcx>,
        sorts: BTreeMap<String, trust_types::Sort>,
    }

    impl<'tcx> Visitor<'tcx> for Collector<'_, 'tcx> {
        fn visit_pat(&mut self, pat: &'tcx Pat<'tcx>) {
            if let PatKind::Binding(_, canonical_id, ident, _) = pat.kind
                && canonical_id == pat.hir_id
                && let Some((name, sort)) = loop_source_binding_from_ty(
                    ident.name.to_string(),
                    self.typeck_results.pat_ty(pat),
                )
            {
                self.sorts.insert(name, sort);
            }
            intravisit::walk_pat(self, pat);
        }
    }

    let mut collector = Collector { typeck_results, sorts: BTreeMap::new() };
    for param in body.params {
        collector.visit_pat(param.pat);
    }
    collector.sorts
}

/// Exact primitive element domains for collection parameters. This is kept
/// separate from the logical source-sort environment: source elaboration
/// intentionally treats every primitive integer as `Int`, while a structural
/// compiler proposition must still distinguish (for example) `u8`, `i8`, and
/// `usize` before it can authorize a monitor or a body-bound E4/E5 proof.
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
        typeck_results: &'a TypeckResults<'tcx>,
        scope_tree: &'a ScopeTree,
        target: Scope,
        unique_parameter_hir_local_ids: &'a BTreeMap<String, u32>,
        // Key by the Rust identifier, not the verifier spelling. Keep visible
        // unsupported bindings as `None`: an inner aggregate/closure named `x`
        // must still shadow an outer supported integer `x` rather than
        // accidentally resurrecting the outer verifier binding.
        bindings: BTreeMap<String, (Scope, u32, Option<(String, trust_types::Sort)>)>,
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
                    loop_source_binding_from_ty(rust_name.clone(), self.typeck_results.pat_ty(pat))
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
    }

    let scope_tree = tcx.region_scope_tree(local_def_id);
    let unique_parameter_hir_local_ids = unique_simple_parameter_hir_local_ids(body);
    let mut collector = Collector {
        typeck_results,
        scope_tree,
        target: Scope { local_id: loop_id.local_id, data: ScopeData::Node },
        unique_parameter_hir_local_ids: &unique_parameter_hir_local_ids,
        bindings: BTreeMap::new(),
    };
    collector.visit_body(body);
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
) {
    struct BindingDomains {
        scalar: Option<(LoweredVariableDomain, Option<LoweredSourceBinding>)>,
        collection: Option<(String, LoweredCollectionDomain)>,
    }

    fn binding_domain<'tcx>(
        tcx: TyCtxt<'tcx>,
        name: String,
        ty: Ty<'tcx>,
        hir_local_id: u32,
        collection_parameter: bool,
    ) -> BindingDomains {
        // Static E4 collection models are rooted in function arguments.
        // A loop-local collection (including a same-named shadow) may be
        // source-valid, but cannot receive structural proof authority until
        // its exact HIR binding is transported to the corresponding MIR place.
        let collection = collection_parameter
            .then(|| collection_element_domain_from_ty(tcx, name.clone(), ty))
            .flatten();
        let (name, scalar_ty, is_whole_scalar) = match ty.kind() {
            ty::Ref(_, inner, _) | ty::RawPtr(inner, _) => (format!("{name}*"), *inner, false),
            _ => (name, ty, true),
        };
        let scalar = proposition_domain_from_ty(tcx, scalar_ty).map(|domain| {
            let source_binding =
                is_whole_scalar.then(|| LoweredSourceBinding { name: name.clone(), hir_local_id });
            (LoweredVariableDomain { name, domain }, source_binding)
        });
        BindingDomains { scalar, collection }
    }

    struct Collector<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        typeck_results: &'a TypeckResults<'tcx>,
        scope_tree: &'a ScopeTree,
        target: Scope,
        unique_parameter_hir_local_ids: &'a BTreeMap<String, u32>,
        bindings: BTreeMap<String, (Scope, u32, Option<BindingDomains>)>,
    }

    impl<'tcx> Visitor<'tcx> for Collector<'_, 'tcx> {
        fn visit_pat(&mut self, pat: &'tcx Pat<'tcx>) {
            if let PatKind::Binding(_, canonical_id, ident, _) = pat.kind
                && canonical_id == pat.hir_id
                && let Some(scope) = self.scope_tree.var_scope(canonical_id.local_id)
                && self.scope_tree.is_subscope_of(self.target, scope)
            {
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
                        exact_unique_parameter,
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
    };
    collector.visit_body(body);
    let visible_rust_names = collector.bindings.keys().cloned().collect::<BTreeSet<_>>();
    let mut domains = Vec::new();
    let mut collection_domains = BTreeMap::new();
    let mut source_bindings = Vec::new();
    for (_, _, binding) in collector.bindings.into_values() {
        let Some(binding) = binding else { continue };
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
            }
        }
    }
    for (name, domain) in function_collection_element_domains(tcx, body, typeck_results) {
        let rust_name = name.strip_suffix('*').unwrap_or(&name);
        if !visible_rust_names.contains(rust_name)
            && unique_parameter_hir_local_ids.contains_key(rust_name)
        {
            collection_domains.entry(name).or_insert(domain);
        }
    }
    (
        canonical_variable_domains(domains).unwrap_or_default(),
        collection_domains,
        canonical_source_bindings(source_bindings).unwrap_or_default(),
    )
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
    let output = tcx.fn_sig(def_id).instantiate_identity().skip_binder().output();
    if let Some(domain) = proposition_domain_from_ty(tcx, output) {
        domains.push(LoweredVariableDomain { name: "_0".to_string(), domain });
    }
    canonical_variable_domains(domains).unwrap_or_default()
}

fn lowered_variable_expr(tcx: TyCtxt<'_>, text: String, rust_ty: Ty<'_>) -> Option<LoweredExpr> {
    let ty = lowered_expr_ty(rust_ty)?;
    // Compiler-owned executable-monitor identity currently has exact domains
    // only for Bool and primitive integers. Float predicates still feed the
    // body-bound Trust-WP lane, but must remain opaque to certified-monitor
    // authority until a bit-exact float proposition domain exists.
    let variable_domains = match proposition_domain_from_ty(tcx, rust_ty) {
        Some(domain) => synthetic_variable_domains(&text, domain)?,
        None if ty == LoweredExprTy::Float => Vec::new(),
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

fn lowered_expr_ty(ty: Ty<'_>) -> Option<LoweredExprTy> {
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

/// `(bit_width, is_signed)` for a FIXED-width primitive integer type. `usize`/
/// `isize` return `None` — their width is target-dependent, so a widening
/// judgement over them cannot be made statically-sound (a spec must not silently
/// bake in a target word size). Non-integers return `None`.
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
/// Signed → unsigned (negatives wrap), any narrowing, and `usize`/`isize`
/// (target-dependent width) are NOT value-preserving → rejected (fail-closed:
/// the whole predicate becomes unsupported, never a false PROVE).
fn value_preserving_int_cast(src: Ty<'_>, dst: Ty<'_>) -> bool {
    let (Some((src_bits, src_signed)), Some((dst_bits, dst_signed))) =
        (fixed_int_bits_signed(src), fixed_int_bits_signed(dst))
    else {
        return false;
    };
    match (src_signed, dst_signed) {
        (false, false) | (true, true) => dst_bits >= src_bits,
        (false, true) => dst_bits > src_bits,
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
    Int(&'a str),
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
    ) -> Option<SnippetExpr> {
        let tokens = tokenize_contract_snippet(input, syntax)?;
        let mut parser = Self { tokens, index: 0, result_binding, syntax };
        let expr = parser.parse_implies()?;
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
            SnippetToken::Ident(name) => self.parse_ident(name),
            SnippetToken::Int(value) => Some(SnippetExpr {
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

    fn parse_ident(&mut self, name: &'a str) -> Option<SnippetExpr> {
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
            SnippetToken::Ident(name) => Some(SnippetExpr {
                text: format!("*{name}"),
                ty: SnippetExprTy::Ambiguous,
                bool_literal: None,
            }),
            _ => None,
        }
    }
}

fn tokenize_contract_snippet(input: &str, syntax: SnippetSyntax) -> Option<Vec<SnippetToken<'_>>> {
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
            index += 1;
            while index < bytes.len() && bytes[index].is_ascii_digit() {
                index += 1;
            }
            tokens.push(SnippetToken::Int(&input[start..index]));
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
            if j < bytes.len() && bytes[j] == b'(' {
                out.push(snippet[start..i].to_string());
            }
        } else {
            i += 1;
        }
    }
    out
}

/// R4 §1 recognition: the first called identifier that names an unfoldable
/// island DEFINITION in this session's kernel-checked environment, if any.
/// Read-only against the [`crate::trust_verify::SessionIslandEnv`] stash;
/// `None` when islands are unchecked, the session is tainted, or no callee
/// matches — the diagnostic then keeps its generic attribution. This refines
/// MESSAGES only; the predicate still refuses (fail-closed) until the typed
/// citation row and its kernel-side discharge land per the seam map.
fn island_cited_callee(tcx: TyCtxt<'_>, snippet: &str) -> Option<String> {
    let candidates = called_identifiers(snippet);
    if candidates.is_empty() {
        return None;
    }
    tcx.sess.with_trust_compiler_state::<crate::trust_verify::SessionIslandEnv, _>(|state| {
        if std::env::var_os("TRUST_ISLAND_CITE_TRACE").is_some() {
            eprintln!(
                "TRUST_ISLAND_CITE_TRACE: stash_populated={} candidates={candidates:?}",
                state.env.is_some()
            );
        }
        let env = state.env.as_ref()?;
        candidates
            .into_iter()
            .find(|name| trust_certify::clean_island::island_definition_value(env, name).is_some())
    })
}

fn unsupported_predicate_reason(tcx: TyCtxt<'_>, span: Span) -> Symbol {
    let source_map = tcx.sess.source_map();
    let detail = match source_map.span_to_snippet(span) {
        Ok(snippet) => {
            let snippet = snippet.trim();
            if let Some(identifier) = primed_identifier_in_contract_snippet(snippet) {
                format!(
                    "primed post-state identifier `{identifier}` has no verified MIR state binding"
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
                source_map.span_to_diagnostic_string(span)
            )
        }
    };
    Symbol::intern(&detail)
}

#[cfg(test)]
mod tests;

// trust_vcgen/termination/recursion_scc.rs: the recursion-SCC (mutual
// recursion) termination lane.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;
use trust_types::*;

use super::{
    LoopInfo, conjoin_exact_preconditions, exact_recursion_preconditions,
    extract_decreases_contracts, local_ever_mutated, recursion_measure_bindings_at,
    source_contract_metadata, unique_parameter_local_by_name,
    unique_recursion_decreases_contract_index, unsupported_recursion_decreases_vc,
    validated_explicit_recursion_clause,
};

// ===========================================================================
// Recursion-SCC (mutual recursion) termination lane — 2026-09-25
// ===========================================================================
//
// RULING (docs/KNOWN_HAZARDS.md, "CLOSED 2026-09-25 — mutual
// recursion verified and could abort on stack overflow"): a call into another
// member of the caller's recursion SCC gets the SAME termination obligation a
// direct self call gets, and terminating mutual recursion is admitted exactly
// when a measure proves it. Before this lane, `fn a(n) { b(n) } fn b(n) { a(n) }`
// minted no `[termination]` row at all (each body's only recursive edge was a
// non-self call, which the direct-self lanes answer with "mint nothing"),
// verified, and aborted on stack overflow.
//
// THE MEASURE RULE (a shared-measure / ranking argument). Every member `f`
// carrying an authored function-level `decreases m_f` (one immutable integer
// parameter) gets, for EVERY SCC edge `f -> g` at call site `c` (`g == f`
// included), the self-call row with the callee's measure substituted:
//
//     guards(c) ∧ pre(f) ∧ ( m_g(args_c) >= m_f(entry)  ∨  m_f(entry) < 0 )
//
// If every edge's row is UNSAT, an infinite call chain `f0 -> f1 -> …` would
// yield `m_f0 > m_f1 > … >= 0` over the integers, which is impossible. The
// argument needs, and this lane enforces fail-closed:
//
//   (a) EVERY SCC edge charged. Every member reaches this lane (the compiler
//       installs the facts for each one), its calls into the SCC are
//       identified by the compiler from resolved `DefId`s, and any SCC
//       successor the local call graph has but no direct call terminator
//       realizes (a closure handed to a higher-order callee) is an
//       unmeasurable edge charged with an unprovable row.
//   (b) ONE measure per member. The value callers compare against
//       (`own_measure`, computed by the compiler from the member's `DefId`)
//       must equal the member's own clause and parameter position, or the
//       member is refused.
//   (c) An immutable measure parameter, so `m_f(entry)` names one value at
//       every call site, and no loop (a measure relates the call to the entry,
//       not the loop's iterations to each other — the self lane's rule).
//
// A member with NO clause gets an unprovable row for each of its SCC calls: the
// ruling admits mutual recursion only on a measure. A callee whose measure is
// absent or outside the fragment is not comparable, so the call is refused.
//
// RESIDUAL (recorded in docs/KNOWN_HAZARDS.md): a cycle the compiler's LOCAL
// call graph cannot see — through `dyn`, a function pointer, or a foreign
// generic that re-enters the crate (`x.into()` reaching a local `From` impl) —
// puts no function in a multi-member SCC; those calls stay with the
// direct-self lanes exactly as before.

/// Every call terminator of `func` filed in the compiler's SCC call set, in
/// block order, plus every filed block that is NOT a call terminator in this
/// body (the compiler's MIR and the extracted body disagree about it).
fn scc_call_sites<'a>(
    func: &'a VerifiableFunction,
    scc: &'a crate::RecursionSccContext,
) -> (Vec<((BlockId, &'a [Operand], &'a SourceSpan), &'a crate::RecursionSccCall)>, Vec<BlockId>) {
    let mut sites = Vec::new();
    let mut matched = FxHashSet::default();
    for block in &func.body.blocks {
        let (args, span) = match &block.terminator {
            Terminator::Call { args, span, .. } | Terminator::TailCall { args, span, .. } => {
                (args.as_slice(), span)
            }
            _ => continue,
        };
        if let Some(call) = scc.calls.get(&block.id.0) {
            matched.insert(block.id.0);
            sites.push(((block.id, args, span), call));
        }
    }
    let unmatched = scc
        .calls
        .keys()
        .filter(|block| !matched.contains(*block))
        .map(|block| BlockId(*block))
        .collect();
    (sites, unmatched)
}

/// A recursive edge no measure covers: a `[termination]` row whose violation
/// formula is `true`, so no engine can ever report it proved. It carries no
/// source-contract binding, so it can never be counted toward discharging an
/// authored clause either.
fn unmeasured_recursion_edge_vc(
    func: &VerifiableFunction,
    location: SourceSpan,
    measure: String,
) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::NonTermination {
            context: super::RECURSION_TERMINATION_CONTEXT.to_string(),
            measure,
        },
        function: func.name.as_str().into(),
        location,
        formula: Formula::Bool(true),
        contract_metadata: None,
        obligation: None,
    }
}

/// Why an authored measure on a recursion-SCC member cannot be related to
/// every recursive edge of its body — the SCC twin of
/// [`authored_recursion_identity_uncertainty`]. The one relaxation over that
/// gate: a call the compiler filed as a call into this SCC is classified (it
/// gets a measured row). Every other call, `Drop`, opaque or unrecognized
/// terminator stays an uncertainty.
fn scc_authored_measure_uncertainty(
    func: &VerifiableFunction,
    scc: &crate::RecursionSccContext,
    loops: &[LoopInfo],
    clause: &DecreasesClause,
    measure_decl: &LocalDecl,
) -> Option<String> {
    let own_matches = match &scc.own_measure {
        crate::RecursionSccMeasure::Param { position, name } => {
            measure_decl.index.checked_sub(1) == Some(*position) && *name == clause.measure
        }
        crate::RecursionSccMeasure::Absent | crate::RecursionSccMeasure::Unsupported(_) => false,
    };
    if !own_matches {
        return Some(format!(
            "function-level decreases `{}` is not the measure the other members of this \
             function's recursion cycle are compared against",
            clause.measure
        ));
    }
    if local_ever_mutated(func, measure_decl.index) {
        return Some(format!(
            "function-level decreases parameter `{}` is reassigned in the body, so its value at \
             a recursive call is not its entry value",
            clause.measure
        ));
    }
    if let Some(first) = loops.first() {
        return Some(format!(
            "a recursion measure cannot cover the loop headed at bb{} (back-edge from bb{}): a \
             call's descent says nothing about the loop's own iterations — add a `decreases` \
             clause to the loop, or restructure it as recursion",
            first.header.0, first._latch.0
        ));
    }
    func.body.blocks.iter().find_map(|block| match &block.terminator {
        Terminator::Call { func: callee, .. } | Terminator::TailCall { func: callee, .. }
            if !scc.calls.contains_key(&block.id.0) =>
        {
            Some(format!(
                "function-level decreases cannot classify call `{callee}` in bb{} as outside this \
                 function's recursion cycle",
                block.id.0
            ))
        }
        Terminator::Drop { .. } => Some(format!(
            "function-level decreases cannot classify Drop in bb{} as non-recursive",
            block.id.0
        )),
        Terminator::Opaque { kind, .. } => Some(format!(
            "function-level decreases cannot classify opaque terminator `{kind}` in bb{} as \
             non-recursive",
            block.id.0
        )),
        // Explicit, as in the direct-self gate: `Terminator` is non-exhaustive
        // across this crate boundary, so a wildcard `None` would silently treat
        // a future call/control-flow effect as non-recursive.
        Terminator::Call { .. }
        | Terminator::TailCall { .. }
        | Terminator::Goto(_)
        | Terminator::SwitchInt { .. }
        | Terminator::Return
        | Terminator::Assert { .. }
        | Terminator::Unreachable
        | Terminator::Resume => None,
        _ => Some(format!(
            "function-level decreases cannot classify an unrecognized terminator in bb{} as \
             non-recursive",
            block.id.0
        )),
    })
}

/// The recursion-SCC termination lane; see the section comment above.
pub(super) fn check_recursion_scc_termination(
    func: &VerifiableFunction,
    scc: &crate::RecursionSccContext,
    loops: &[LoopInfo],
    vcs: &mut Vec<VerificationCondition>,
) {
    let (sites, unmatched_blocks) = scc_call_sites(func, scc);

    // (a) Edges no call terminator of this body realizes are unmeasurable.
    for edge in &scc.unrealized_edges {
        vcs.push(unmeasured_recursion_edge_vc(
            func,
            func.span.clone(),
            format!("none (recursion cycle through `{edge}` is not a direct call)"),
        ));
    }
    for block in &unmatched_blocks {
        let callee = scc.calls.get(&block.0).map_or("<unknown>", |call| call.callee.as_str());
        vcs.push(unmeasured_recursion_edge_vc(
            func,
            func.span.clone(),
            format!("none (recursion cycle through `{callee}` in bb{} was not extracted)", block.0),
        ));
    }

    let decreases_clauses = extract_decreases_contracts(func);
    let clause = match validated_explicit_recursion_clause(func, &decreases_clauses) {
        Err((span, detail)) => {
            vcs.push(unsupported_recursion_decreases_vc(func, span, detail));
            return;
        }
        // No authored measure: every recursive edge is unmeasured. The ruling
        // admits mutual recursion only on a measure, so there is no inferred
        // fallback here (and no "mint nothing" arm).
        Ok(None) => {
            for ((_, _, span), call) in &sites {
                vcs.push(unmeasured_recursion_edge_vc(
                    func,
                    (*span).clone(),
                    format!(
                        "none (`{}` closes a recursion cycle; every member needs a `decreases` \
                         measure)",
                        call.callee
                    ),
                ));
            }
            return;
        }
        Ok(Some(clause)) => clause,
    };

    let Some(measure_decl) = unique_parameter_local_by_name(func, &clause.measure) else {
        vcs.push(unsupported_recursion_decreases_vc(
            func,
            clause.span.clone(),
            format!("function-level decreases parameter `{}` is not a parameter", clause.measure),
        ));
        return;
    };
    if let Some(detail) = scc_authored_measure_uncertainty(func, scc, loops, clause, measure_decl) {
        vcs.push(unsupported_recursion_decreases_vc(func, clause.span.clone(), detail));
        return;
    }
    if sites.is_empty() && scc.unrealized_edges.is_empty() && unmatched_blocks.is_empty() {
        // A multi-member SCC member realizes at least one SCC edge by
        // definition; reaching here means the facts and the body disagree.
        vcs.push(unsupported_recursion_decreases_vc(
            func,
            clause.span.clone(),
            "no call into this function's recursion cycle was found in its body".to_string(),
        ));
        return;
    }

    let source_contract_index = unique_recursion_decreases_contract_index(func, clause);
    let exact_preconditions = exact_recursion_preconditions(func);
    let mut rows = Vec::with_capacity(sites.len());
    for &((block, args, span), call) in &sites {
        // Trust (L0 termination guarantee): the same bounded walk as the
        // direct-self lane; a trip is a visible non-proof, never an absence.
        if trust_types::verify_budget::budget_exhausted() {
            vcs.push(unsupported_recursion_decreases_vc(
                func,
                func.span.clone(),
                format!(
                    "per-function verification budget exhausted before every call into this \
                     function's recursion cycle could be checked against decreases measure `{}`",
                    clause.measure
                ),
            ));
            return;
        }
        let arg_pos = match &call.callee_measure {
            crate::RecursionSccMeasure::Param { position, .. } => *position,
            crate::RecursionSccMeasure::Absent => {
                vcs.push(unsupported_recursion_decreases_vc(
                    func,
                    span.clone(),
                    format!(
                        "`{}` is in this function's recursion cycle but has no function-level \
                         `decreases` measure to compare with `{}`",
                        call.callee, clause.measure
                    ),
                ));
                return;
            }
            crate::RecursionSccMeasure::Unsupported(reason) => {
                vcs.push(unsupported_recursion_decreases_vc(
                    func,
                    span.clone(),
                    format!(
                        "the `decreases` measure of `{}` (in this function's recursion cycle) is \
                         not comparable with `{}`: {reason}",
                        call.callee, clause.measure
                    ),
                ));
                return;
            }
        };
        let Some((measure_entry, measure_call, binding_facts, exact_site_span)) =
            recursion_measure_bindings_at(func, block, args, measure_decl, arg_pos)
        else {
            vcs.push(unsupported_recursion_decreases_vc(
                func,
                span.clone(),
                format!(
                    "function-level decreases parameter `{}` could not be bound to every \
                     recursive call under exact machine semantics",
                    clause.measure
                ),
            ));
            return;
        };
        let not_decreasing = Formula::Or(vec![
            Formula::Ge(Box::new(measure_call), Box::new(measure_entry.clone())),
            Formula::Lt(Box::new(measure_entry), Box::new(Formula::Int(0))),
        ]);
        let core = if binding_facts.is_empty() {
            not_decreasing
        } else {
            let mut clauses = binding_facts;
            clauses.push(not_decreasing);
            Formula::And(clauses)
        };
        rows.push(VerificationCondition {
            kind: VcKind::NonTermination {
                context: super::RECURSION_TERMINATION_CONTEXT.to_string(),
                measure: clause.measure.clone(),
            },
            function: func.name.as_str().into(),
            location: exact_site_span.unwrap_or_else(|| span.clone()),
            formula: crate::generate::v2_conjoin_path_guards_for_hardened(
                func,
                block,
                conjoin_exact_preconditions(&exact_preconditions, core),
            ),
            contract_metadata: source_contract_metadata(source_contract_index),
            obligation: None,
        });
    }
    vcs.extend(rows);
}

#[cfg(test)]
#[path = "recursion_scc_tests.rs"]
mod tests;

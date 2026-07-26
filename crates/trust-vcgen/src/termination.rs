// trust_vcgen/termination.rs: Termination checking via decreases clauses
//
// Extracts loop variants and recursive function decreases measures from MIR,
// then generates VcKind::NonTermination verification conditions. Termination
// is proved by showing the measure:
//   1. Is bounded below (non-negative).
//   2. Strictly decreases on each loop iteration or recursive call.
//
// Loop variant extraction:
//   - Detect back-edges in the CFG: an edge latch -> header is a back-edge
//     iff `header` dominates `latch` (the sound natural-loop definition).
//   - For each back-edge, find integer variables modified in the loop body
//     that could serve as the decreasing measure.
//   - Function-level `decreases` metadata does NOT identify a loop site and is
//     used only for recursion. First-class loop-local clauses carry their own
//     authenticated source-loop identity and are handled by `contracts`.
//
// Recursive decreases detection:
//   - Detect self-calls (Call terminator where func matches the function name).
//   - Generate VC that the decreases measure at the call site is strictly less
//     than the measure at function entry.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;
use trust_types::*;

const RECURSION_DECREASES_UNSUPPORTED_KIND: &str = "ContractKind::Decreases::Recursion";

fn fallback_loop_measure_symbol(measure: &str, phase: &str) -> String {
    crate::generated_formula_symbol("termination", &format!("{measure}_{phase}"))
}

/// A detected loop in the MIR control flow graph.
#[derive(Debug, Clone)]
pub(crate) struct LoopInfo {
    /// Block ID of the loop header (target of the back-edge).
    pub(crate) header: BlockId,
    /// Block ID of the latch (source of the back-edge).
    pub(crate) _latch: BlockId,
    /// Block IDs of all blocks in the loop body (between header and latch).
    pub(crate) body_blocks: Vec<BlockId>,
}

/// A detected recursive call site.
#[derive(Debug, Clone)]
pub(crate) struct RecursiveCallSite {
    /// Block containing the recursive call.
    pub(crate) block: BlockId,
    /// Arguments passed to the recursive call.
    pub(crate) args: Vec<Operand>,
    /// Source span of the call.
    pub(crate) span: SourceSpan,
}

/// Detect loops by finding back-edges in the CFG.
///
/// A CFG edge `latch -> header` is a back-edge iff `header` dominates `latch`
/// -- the sound, standard definition of a natural-loop back-edge. We compute
/// the dominator relation explicitly (see `compute_dominators`) rather than
/// relying on block-ID ordering.
///
/// The previous implementation used the heuristic "target block ID <= source
/// block ID". That is unsound: rustc does not topologically order MIR block
/// IDs, so loopless forward/cross edges that happen to jump to a lower-numbered
/// block (e.g. match-guard / `SwitchInt` lowering where a guard-fail path
/// branches to an already-emitted wildcard arm) were fabricated as loops,
/// producing spurious `NonTermination` VCs on terminating code -- a Goal-1
/// false-fail.
pub(crate) fn detect_loops(body: &VerifiableBody) -> Vec<LoopInfo> {
    let n = body.blocks.len();
    if n == 0 {
        return Vec::new();
    }
    let dom = compute_dominators(body);
    let preds = compute_predecessors(body);
    let mut loops = Vec::new();

    for block in &body.blocks {
        let latch = block.id;
        if latch.0 >= n {
            continue;
        }
        for header in block_successors(&block.terminator) {
            // Back-edge iff the successor (`header`) dominates this block
            // (`latch`). A self-loop (header == latch) qualifies because every
            // block dominates itself.
            let is_back_edge =
                header.0 < n && dom.get(latch.0).is_some_and(|d| d.contains(&header.0));
            if !is_back_edge {
                continue;
            }
            // Recover the standard natural-loop body by walking predecessors
            // backwards from the latch and stopping at the header. Block IDs
            // are allocation order, not CFG order: an ID interval can both
            // omit real loop blocks and include unrelated ones. In particular,
            // allowing an unrelated/conditional assignment into the candidate
            // set can turn it into an unconditional decreasing step and mint a
            // false termination proof.
            let body_blocks = natural_loop_blocks(header, latch, &preds);

            loops.push(LoopInfo { header, _latch: latch, body_blocks });
        }
    }

    loops
}

/// Predecessor lists indexed by `BlockId`.
fn compute_predecessors(body: &VerifiableBody) -> Vec<Vec<usize>> {
    let n = body.blocks.len();
    let mut preds = vec![Vec::new(); n];
    for block in &body.blocks {
        if block.id.0 >= n {
            continue;
        }
        for succ in block_successors(&block.terminator) {
            if succ.0 < n {
                preds[succ.0].push(block.id.0);
            }
        }
    }
    preds
}

/// The natural-loop block set for one proven back-edge `latch -> header`.
fn natural_loop_blocks(header: BlockId, latch: BlockId, preds: &[Vec<usize>]) -> Vec<BlockId> {
    let mut members: FxHashSet<usize> = [header.0, latch.0].into_iter().collect();
    let mut work = if latch == header { Vec::new() } else { vec![latch.0] };
    while let Some(block) = work.pop() {
        let Some(block_preds) = preds.get(block) else {
            continue;
        };
        for &pred in block_preds {
            if members.insert(pred) && pred != header.0 {
                work.push(pred);
            }
        }
    }
    let mut members: Vec<_> = members.into_iter().map(BlockId).collect();
    members.sort_by_key(|id| id.0);
    members
}

/// Compute the dominator sets for every block via iterative dataflow.
///
/// `dominators[b]` is the set of block indices that dominate block `b` (every
/// path from entry to `b` passes through them). A block always dominates
/// itself; the entry block (index 0) is dominated only by itself.
///
/// Standard forward dataflow to a fixpoint:
///   dom(entry) = {entry}
///   dom(b)     = {b} ∪ (⋂ dom(p) for p ∈ preds(b))
///
/// `body.blocks` is indexed by `BlockId` (`blocks[i].id.0 == i`), matching the
/// convention used throughout vcgen (e.g. `generate.rs` indexes
/// `func.body.blocks[block_id.0]` directly), so block indices double as
/// positions. A defensive iteration cap keeps this total even on malformed IR.
fn compute_dominators(body: &VerifiableBody) -> Vec<FxHashSet<usize>> {
    let n = body.blocks.len();
    if n == 0 {
        return Vec::new();
    }

    let preds = compute_predecessors(body);

    const ENTRY: usize = 0;
    let all: FxHashSet<usize> = (0..n).collect();
    let mut dom: Vec<FxHashSet<usize>> = vec![all; n];
    dom[ENTRY] = std::iter::once(ENTRY).collect();

    let cap = n.saturating_mul(n).saturating_add(n).saturating_add(16);
    let mut iters = 0usize;
    let mut changed = true;
    while changed {
        changed = false;
        iters += 1;
        if iters > cap {
            break;
        }
        for i in 0..n {
            if i == ENTRY {
                continue;
            }
            let mut new_dom: Option<FxHashSet<usize>> = None;
            for &p in &preds[i] {
                new_dom = Some(match new_dom {
                    None => dom[p].clone(),
                    Some(acc) => acc.intersection(&dom[p]).copied().collect(),
                });
            }
            let mut new_dom = new_dom.unwrap_or_default();
            new_dom.insert(i);
            if new_dom != dom[i] {
                dom[i] = new_dom;
                changed = true;
            }
        }
    }

    dom
}

/// Detect recursive call sites (calls to the same function).
pub(crate) fn detect_recursive_calls(func: &VerifiableFunction) -> Vec<RecursiveCallSite> {
    let mut sites = Vec::new();

    for block in &func.body.blocks {
        if let Terminator::Call { func: callee, args, span, .. } = &block.terminator {
            if is_direct_self_call(func, callee) {
                sites.push(RecursiveCallSite {
                    block: block.id,
                    args: args.clone(),
                    span: span.clone(),
                });
            }
        }
    }

    sites
}

/// Match only the current function's exact definition path after removing
/// direct-call generic arguments.
///
/// rustc's callee spelling may include a terminal turbofish such as
/// `crate::f::<u32>`. `strip_generics` deliberately preserves path text rather
/// than performing suffix or bare-name matching, so a different module's
/// `other::f::<u32>` cannot be mistaken for self recursion. Its terminal-
/// turbofish spelling leaves one trailing `::`; remove that separator only
/// when generic text was actually stripped.
fn is_direct_self_call(func: &VerifiableFunction, callee: &str) -> bool {
    fn direct_call_identity(path: &str) -> String {
        let mut identity = trust_types::strip_generics(path);
        if identity != path && identity.ends_with("::") {
            identity.truncate(identity.len() - 2);
        }
        identity
    }

    direct_call_identity(callee) == direct_call_identity(&func.def_path)
}

/// Return why an authored recursion measure cannot be related to every call
/// edge in the body.
///
/// This is intentionally a whole-body, fail-closed gate. A non-self call may
/// be mutual recursion (or may conceal it behind a summary), while `Drop`,
/// `Opaque`, and any future unclassified terminator represent call/control-flow
/// effects whose recursion identity is not modeled by this bounded direct-self
/// lane. Once any such edge exists, emitting only the recognized self-call
/// rows—or a vacuous row when no self call was recognized—would overstate what
/// the authored clause actually proved.
fn authored_recursion_identity_uncertainty(func: &VerifiableFunction) -> Option<String> {
    func.body.blocks.iter().find_map(|block| match &block.terminator {
        Terminator::Call { func: callee, .. } if !is_direct_self_call(func, callee) => {
            Some(format!(
                "function-level decreases cannot classify non-self call `{callee}` in bb{} as \
                 non-recursive",
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
        // Keep this list explicit. `Terminator` is non-exhaustive across this
        // crate boundary, so a wildcard `None` would silently treat every new
        // call/control-flow effect as non-recursive and could authorize a
        // partial or vacuous E5 discharge.
        Terminator::Call { .. }
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

/// Find integer variables modified in a set of blocks.
///
/// Returns (local_index, variable_name) pairs for locals that are assigned
/// in the given blocks and have integer types.
pub(crate) fn modified_int_locals(
    func: &VerifiableFunction,
    blocks: &[BlockId],
) -> Vec<(usize, String)> {
    let mut modified = Vec::new();
    let block_set: FxHashSet<usize> = blocks.iter().map(|b| b.0).collect();

    for block in &func.body.blocks {
        if !block_set.contains(&block.id.0) {
            continue;
        }
        for stmt in &block.stmts {
            if let Statement::Assign { place, .. } = stmt
                && let Some(decl) = func.body.locals.get(place.local)
                && decl.ty.is_integer()
                && place.projections.is_empty()
            {
                let name = decl.name.clone().unwrap_or_else(|| format!("_{}", place.local));
                if !modified.iter().any(|(idx, _)| *idx == place.local) {
                    modified.push((place.local, name));
                }
            }
        }
    }

    modified
}

/// Extract function-level decreases clauses for recursive calls.
///
/// The current contract schema carries no loop header/site identity, so these
/// must not be relabeled as `LoopVariant`; doing so would attach one expression
/// to an arbitrary backedge.
pub(crate) fn extract_decreases_contracts(func: &VerifiableFunction) -> Vec<DecreasesClause> {
    func.contracts
        .iter()
        // A `bbN:` prefix is a first-class loop-local E5 clause.  It is
        // consumed by `contracts::generate_loop_decreases_vc`; treating it as
        // function-recursion metadata as well attaches the measure to the wrong
        // semantic site.
        .filter(|c| {
            matches!(c.kind, ContractKind::Decreases)
                && crate::contracts::loop_contract_body(&c.body).is_none()
                && !c.body.starts_with(crate::contracts::UNPAIRED_LOOP_CONTRACT_PREFIX)
        })
        .map(|c| DecreasesClause {
            measure: c.body.clone(),
            span: c.span.clone(),
            kind: DecreasesKind::Recursion,
        })
        .collect()
}

/// Generate termination verification conditions for a function.
///
/// Produces VcKind::NonTermination VCs for:
/// 1. Each detected loop with a safely inferred decreasing variant (plus
///    provably exit-less loops, which receive a refuting fallback VC).
/// 2. Each recursive call with a bindable inferred or function-level measure.
///
/// VC encoding: the formula represents the NEGATION of the termination
/// argument -- SAT means non-termination is possible, UNSAT means the
/// function terminates. Each VC is conjoined with:
/// - the function's declared `preconditions`, so callers' obligations are
///   respected when checking the well-foundedness conditions;
/// - bindings that tie the synthetic `measure_before/after` (loops) and
///   `measure_entry/call` (recursion) names to the concrete formulas
///   derived from the parameter / call argument / body assignment.
///
/// Without these bindings the synthetic vars are unconstrained and the
/// VC is trivially SAT, which made the old encoder useless: every loop
/// or recursion was reported as potentially non-terminating regardless
/// of its actual semantics. Binding the synthetic names to real
/// expressions lets the solver chain the precondition through the
/// well-foundedness check (e.g. `n >= 0` plus `measure_after = n - 1`
/// plus `measure_before = n` plus the non-decreasing disjunction is
/// UNSAT -- proving the loop terminates).
///
/// When the measure isn't a function-parameter name (e.g. it's an
/// explicit decreases-clause expression like `len - i`, or the
/// heuristic returned "unknown"), the synthetic-var fallback is used.
/// The VC stays over-approximate in that case but the surrounding
/// machinery still functions.
pub(crate) fn check_termination(func: &VerifiableFunction, vcs: &mut Vec<VerificationCondition>) {
    let loops = detect_loops(&func.body);
    let recursive_calls = detect_recursive_calls(func);
    let decreases_clauses = extract_decreases_contracts(func);
    let authored_recursion_uncertainty = if decreases_clauses.is_empty() {
        None
    } else {
        authored_recursion_identity_uncertainty(func)
    };

    // An authored recursion measure is proof surface even on a non-recursive
    // function: an unsupported expression must remain visible rather than
    // disappearing behind the trivial-recursion fast path. A well-typed
    // measure is visible too: with no recursive edge its decrease obligation
    // is vacuously closed, represented by an unsatisfiable violation formula.
    //
    // Do this independently of loop discovery. A non-recursive function may
    // still contain loops; those loop obligations are generated below, but
    // their presence must not make the function-level authored clause vanish.
    //
    // First gate the whole body's call topology. If any non-self Call, Drop,
    // Opaque, or future unclassified edge exists, this bounded direct-self lane
    // cannot establish either that recursion is absent (so vacuity would be
    // unsound) or that the recognized self-call rows cover every recursive
    // edge (so partial rows would be unsound). Emit one visible Unknown marker,
    // then continue through loop generation below.
    if let Some(detail) = &authored_recursion_uncertainty {
        let span = decreases_clauses
            .first()
            .map(|clause| clause.span.clone())
            .unwrap_or_else(|| func.span.clone());
        vcs.push(unsupported_recursion_decreases_vc(func, span, detail.clone()));
        if loops.is_empty() {
            return;
        }
    } else if recursive_calls.is_empty() {
        match validated_explicit_recursion_clause(func, &decreases_clauses) {
            Ok(Some(clause)) => {
                let source_contract_index = unique_recursion_decreases_contract_index(func, clause);
                vcs.push(VerificationCondition {
                    kind: VcKind::NonTermination {
                        context: "recursion".to_string(),
                        measure: clause.measure.clone(),
                    },
                    function: func.name.as_str().into(),
                    location: clause.span.clone(),
                    formula: Formula::Bool(false),
                    contract_metadata: source_contract_metadata(source_contract_index),
                });
            }
            Ok(None) => {}
            Err((span, detail)) => {
                vcs.push(unsupported_recursion_decreases_vc(func, span, detail));
            }
        }
        if loops.is_empty() {
            return;
        }
    }

    // Generate VCs for loops
    for loop_info in &loops {
        // An authored loop-local E5 measure has an exact transition VC in the
        // contract lane.  Do not also emit a heuristic measure for the same
        // header: the duplicate can false-fail a sound authored proof and, more
        // importantly, would obscure which evidence discharged the clause.
        if func.contracts.iter().any(|contract| {
            matches!(contract.kind, ContractKind::Decreases)
                && crate::contracts::loop_contract_body(&contract.body)
                    .is_some_and(|(header, _)| header == loop_info.header.0)
        }) {
            continue;
        }
        // Trust: piece #13 step-2 (safe-async data-safety) — SKIP a loop that is a
        // COROUTINE resume-state protocol sink. The compiler lowers an `async fn` /
        // coroutine's "resumed after {return,completion,panic,drop}" states as a
        // block whose terminator is `assert(false, ResumedAfter*)` that branches to
        // ITSELF (a self-loop with no exit edge). `loop_has_exit` therefore returns
        // false and the fallback below would emit a trivially-SAT `NonTermination`
        // VC that always FAILS — but this "non-termination" is an EXECUTOR-PROTOCOL
        // property (a well-behaved executor never polls a completed/panicked/dropped
        // future), NOT genuine non-termination of the user's code. Treating it as a
        // fatal termination REFUTATION would reject every zero-await `async fn`.
        // These protocol sinks are a Termination/protocol coverage gap (like the
        // r1_recursive `[unknown]` termination), not a data-safety failure, so we
        // emit NO obligation for them. SOUNDNESS: this skips ONLY a loop every one
        // of whose blocks is a `ResumedAfter*` protocol assert — a genuine user
        // infinite loop (`loop {}`) has no such assert and still emits its
        // `NonTermination` VC. See `loop_is_coroutine_protocol_sink`.
        if loop_is_coroutine_protocol_sink(func, loop_info) {
            continue;
        }
        let modified = modified_int_locals(func, &loop_info.body_blocks);

        // No exact authored loop-local measure reached this header (the
        // first-class `bbN:` contract carrier was handled above). For the
        // compatibility inference lane, try each modified integer in stable
        // body order and retain the first candidate that passes every
        // fail-closed binding gate; an unsafe first local must not hide a later
        // valid one. Function-level `decreases` belongs to recursion.
        let inferred = modified.iter().find_map(|(local, name)| {
            loop_measure_bindings(func, loop_info, name)
                .map(|(before, after)| (*local, name.clone(), before, after))
        });
        let fallback_measure =
            modified.first().map(|(_, name)| name.clone()).unwrap_or_else(|| "unknown".to_string());

        // Locate the span from the loop header block
        let span = func
            .body
            .blocks
            .get(loop_info.header.0)
            .map(|bb| terminator_span(&bb.terminator))
            .unwrap_or_default();

        // Use the concrete binding selected above, or retain synthetic
        // before/after vars for the narrow refuting fallback.
        //
        // When no real measure binds, the synthetic free-var encoding
        // `(after >= before) OR (before < 0)` is *trivially SAT* (pick
        // before = after = 0), so it can only ever report FAILED, never
        // prove. Emitting it on a terminating loop we simply can't measure
        // (e.g. `for i in 0..n`, whose decreasing measure is an iterator
        // temp, not a parameter) is a Goal-1 false-fail — Trust rejecting
        // code Rust accepts. So we only fall back to the synthetic VC when
        // the loop is *provably* non-terminating: no edge leaves the loop
        // body, so control can never escape. There the trivially-SAT VC's
        // FAILED verdict is a sound deduction ("no exit ⇒ no termination").
        // A loop with an exit but no bindable measure yields no obligation
        // (Unknown territory) rather than a spurious failure.
        let (measure_local, measure, measure_before, measure_after, has_unsigned_type_bound) =
            match inferred {
                Some((local, measure, before, after)) => {
                    (Some(local), measure, before, after, true)
                }
                None => {
                    if loop_has_exit(&func.body, loop_info) {
                        continue;
                    }
                    (
                        None,
                        fallback_measure.clone(),
                        Formula::Var(
                            fallback_loop_measure_symbol(&fallback_measure, "before"),
                            Sort::Int,
                        ),
                        Formula::Var(
                            fallback_loop_measure_symbol(&fallback_measure, "after"),
                            Sort::Int,
                        ),
                        false,
                    )
                }
            };

        let lower_bound = Formula::Ge(Box::new(measure_before.clone()), Box::new(Formula::Int(0)));
        let not_decreasing = Formula::Or(vec![
            // measure_after >= measure_before (didn't decrease)
            Formula::Ge(Box::new(measure_after), Box::new(measure_before.clone())),
            // measure_before < 0 (not bounded below)
            Formula::Lt(Box::new(measure_before), Box::new(Formula::Int(0))),
        ]);
        // A successfully bound automatic loop measure is unsigned (enforced
        // in `loop_measure_bindings`), so non-negativity is a type invariant
        // at every iteration. Carry it in the raw VC just as the recursion
        // lane does; relying on a function-entry precondition here would be
        // an unsound substitute for a loop invariant.
        let core = if has_unsigned_type_bound {
            Formula::And(vec![lower_bound, not_decreasing])
        } else {
            not_decreasing
        };

        vcs.push(VerificationCondition {
            kind: VcKind::NonTermination { context: "loop".to_string(), measure: measure.clone() },
            function: func.name.as_str().into(),
            location: span,
            formula: conjoin_loop_invariant_preconditions(func, measure_local, core),
            contract_metadata: None,
        });
    }

    // The function-level authored clause was accounted for before loop
    // generation. With no recursive edge there are no call-site decrease
    // obligations to add, and re-validating here would duplicate its marker.
    if authored_recursion_uncertainty.is_some() || recursive_calls.is_empty() {
        return;
    }

    // Generate VCs for recursive calls. Function-level `decreases` is authored
    // proof surface, so it must never disappear merely because this lane cannot
    // bind its expression. Today the exact supported fragment is one uniquely
    // named integer parameter. Anything else gets ONE visible, non-refutable
    // UnsupportedMir row for the function (rather than one row per call).
    let explicit_clause = match validated_explicit_recursion_clause(func, &decreases_clauses) {
        Ok(clause) => clause,
        Err((span, detail)) => {
            vcs.push(unsupported_recursion_decreases_vc(func, span, detail));
            return;
        }
    };

    let inferred_measure = || {
        if func.body.arg_count == 0 {
            return "unknown".to_string();
        }
        let end = (func.body.arg_count + 1).min(func.body.locals.len());
        func.body.locals[1..end]
            .iter()
            .find(|decl| decl.ty.int_width().is_some())
            .and_then(|decl| decl.name.clone())
            .unwrap_or_else(|| "unknown".to_string())
    };
    let measure = explicit_clause.map_or_else(inferred_measure, |clause| clause.measure.clone());
    let explicit_source_contract_index =
        explicit_clause.and_then(|clause| unique_recursion_decreases_contract_index(func, clause));
    let mut recursion_vcs = Vec::new();
    let mut explicit_binding_failure = None;
    for call_site in &recursive_calls {
        let Some((measure_entry, measure_call, binding_facts, exact_site_span)) =
            recursion_measure_bindings(func, call_site, &measure)
        else {
            if explicit_clause.is_some() {
                explicit_binding_failure = Some(call_site.span.clone());
                break;
            }
            // An inferred measure is heuristic coverage only. A binding miss
            // therefore means no row, never a synthetic refutation.
            continue;
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
        recursion_vcs.push(VerificationCondition {
            kind: VcKind::NonTermination {
                context: "recursion".to_string(),
                measure: measure.clone(),
            },
            function: func.name.as_str().into(),
            // Optimized MIR may coarsen distinct Call terminators to the same
            // body-wide source span.  A checked-chain binding carries the exact
            // predecessor Assert span that authenticated its machine-arithmetic
            // value; use that compiler-owned provenance to keep per-callsite
            // source rows distinguishable.  Direct operands retain the Call span.
            location: exact_site_span.unwrap_or_else(|| call_site.span.clone()),
            // Conjoin the recursive call site's DOMINATING PATH GUARDS as a
            // reachability hypothesis. `not_decreasing` is a VIOLATION formula
            // (proved by refutation search), so it counts only where the call
            // is actually reached. Without this, `walk(a, n-1, i)` under
            // `if n > 0` had its decrease VC solved with `n` unconstrained, and
            // PDR found the spurious `n = 0` counterexample against an
            // under-specified obligation (measured on
            // r1_recursive_self_stable_index: "[termination] FAILED ...
            // verified_counterexample = true"). The guard `n > 0` makes
            // `guard ∧ (call_measure >= entry_measure ∨ entry < 0)` UNSAT —
            // `n - 1 < n` and `n > 0 ⇒ n - 1 >= 0` — so the measure genuinely
            // decreases on every reachable recursive edge. Same shared path-guard
            // builder the per-statement arithmetic/bounds lanes use; a call
            // reachable UNconditionally gets no extra hypothesis and is
            // unchanged.
            formula: crate::generate::v2_conjoin_path_guards_for_hardened(
                func,
                call_site.block,
                conjoin_recursion_preconditions(func, core),
            ),
            contract_metadata: source_contract_metadata(explicit_source_contract_index),
        });
    }
    if let Some(span) = explicit_binding_failure {
        vcs.push(unsupported_recursion_decreases_vc(
            func,
            span,
            format!(
                "function-level decreases parameter `{measure}` could not be bound to every \
                 recursive call under exact machine semantics"
            ),
        ));
    } else {
        vcs.extend(recursion_vcs);
    }
}

fn unique_recursion_decreases_contract_index(
    func: &VerifiableFunction,
    clause: &DecreasesClause,
) -> Option<usize> {
    let mut matches = func.contracts.iter().enumerate().filter_map(|(index, contract)| {
        (matches!(contract.kind, ContractKind::Decreases)
            && contract.body == clause.measure
            && contract.span == clause.span
            && crate::contracts::loop_contract_body(&contract.body).is_none()
            && !contract.body.starts_with(crate::contracts::UNPAIRED_LOOP_CONTRACT_PREFIX))
        .then_some(index)
    });
    let index = matches.next()?;
    matches.next().is_none().then_some(index)
}

fn source_contract_metadata(source_contract_index: Option<usize>) -> Option<ContractMetadata> {
    source_contract_index.map(|source_contract_index| ContractMetadata {
        source_contract_index: Some(source_contract_index),
        ..ContractMetadata::default()
    })
}

fn unsupported_recursion_decreases_vc(
    func: &VerifiableFunction,
    span: SourceSpan,
    detail: String,
) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::UnsupportedMir {
            kind: RECURSION_DECREASES_UNSUPPORTED_KIND.to_string(),
            detail,
        },
        function: func.name.as_str().into(),
        location: span,
        // UnsupportedMir is preclassified Unknown. Keep the violation formula
        // satisfiable for direct solver callers too: it can never become Proved.
        formula: Formula::Bool(true),
        contract_metadata: None,
    }
}

fn validated_explicit_recursion_clause<'a>(
    func: &VerifiableFunction,
    decreases_clauses: &'a [DecreasesClause],
) -> Result<Option<&'a DecreasesClause>, (SourceSpan, String)> {
    let explicit: Vec<_> = decreases_clauses
        .iter()
        .filter(|clause| matches!(clause.kind, DecreasesKind::Recursion))
        .collect();
    match explicit.as_slice() {
        [] => Ok(None),
        [clause]
            if unique_parameter_local_by_name(func, &clause.measure)
                .is_some_and(|decl| decl.ty.int_width().is_some()) =>
        {
            Ok(Some(*clause))
        }
        [clause] => Err((
            clause.span.clone(),
            format!(
                "function-level decreases expression `{}` is outside the exact supported \
                 fragment (one uniquely named integer parameter)",
                clause.measure
            ),
        )),
        clauses => Err((
            clauses.first().map(|clause| clause.span.clone()).unwrap_or_default(),
            format!(
                "{} function-level decreases clauses require unsupported lexicographic \
                 recursion semantics",
                clauses.len()
            ),
        )),
    }
}

/// Conjoin only authored entry facts whose meaning remains exact at the
/// recursive call. Raw machine arithmetic is currently encoded as unbounded
/// Int and therefore cannot be an assumption (`u8::MAX + 1 == 0` is the
/// canonical mismatch). Every free name must map uniquely to a bare argument
/// local that is globally immutable; projected, synthetic, return, temp, and
/// versioned names are all dropped fail-closed.
fn conjoin_recursion_preconditions(func: &VerifiableFunction, formula: Formula) -> Formula {
    let mut preconditions = Vec::new();
    for precondition in &func.preconditions {
        if crate::contracts::formula_uses_unmodeled_machine_arithmetic_in_function(
            func,
            precondition,
        ) {
            continue;
        }
        let exact = precondition.free_variables().iter().all(|name| {
            let mut matching = func.body.locals.iter().filter(|decl| {
                decl.index > 0
                    && decl.index <= func.body.arg_count
                    && crate::place_to_var_name(func, &Place::local(decl.index)) == *name
            });
            let Some(local) = matching.next() else {
                return false;
            };
            matching.next().is_none() && !local_ever_mutated(func, local.index)
        });
        if exact {
            preconditions.push(precondition.clone());
        }
    }
    if preconditions.is_empty() {
        formula
    } else {
        preconditions.push(formula);
        Formula::And(preconditions)
    }
}

/// Conjoin only function-entry facts that remain true at every loop iteration.
///
/// A function precondition is not automatically a loop invariant. Reusing a
/// fact about the mutated measure (for example `n > d`) at an arbitrary
/// backedge can falsely prove `n = d` decreasing forever: it decreases once,
/// then stalls. A precondition is retained only when every free variable maps
/// uniquely through the verifier's canonical bare-local vocabulary and that
/// local is provably immutable for the whole function. Unknown, projected,
/// versioned, aliased, or measure variables fail closed.
fn conjoin_loop_invariant_preconditions(
    func: &VerifiableFunction,
    measure_local: Option<usize>,
    formula: Formula,
) -> Formula {
    let mut invariants = Vec::new();
    for precondition in &func.preconditions {
        let is_invariant = precondition.free_variables().iter().all(|name| {
            let mut matching =
                func.body.locals.iter().filter(|decl| {
                    crate::place_to_var_name(func, &Place::local(decl.index)) == *name
                });
            let Some(local) = matching.next() else {
                return false;
            };
            matching.next().is_none()
                && Some(local.index) != measure_local
                && !local_ever_mutated(func, local.index)
        });
        if is_invariant {
            invariants.push(precondition.clone());
        }
    }
    if invariants.is_empty() {
        formula
    } else {
        invariants.push(formula);
        Formula::And(invariants)
    }
}

/// If `measure` names an unsigned integer parameter and the loop has exactly
/// one assignment to that local which dominates the latch, return concrete
/// (measure_before, measure_after) formulas. `measure_before` is the current
/// integer value and `measure_after` is the rvalue lowered to a formula (with
/// references to the measure local meaning the pre-iteration value, since MIR
/// isn't SSA).
///
/// Returns `None` when:
/// - the measure isn't a parameter name (or is "unknown" from the heuristic);
/// - the loop body modifies the measure local more than once (chained
///   assignments would need real symbolic execution, not a one-shot
///   rvalue lowering);
/// - the assignment can be bypassed on a path to the latch, any other/opaque
///   write channel exists, or a non-measure step input is mutable;
/// - the single rvalue isn't a shape we can lower (e.g. an aggregate
///   or a complex projection).
///
/// One projected-read step IS lowered: the debug-build checked decrement
/// (`_T = CheckedSub(n, k); Assert(!_T.1) -> n = _T.0`), which resolves
/// through the step block's unique IN-LOOP Assert-predecessor — see
/// `resolve_loop_checked_step_chain` (the rung-F loop-lane port of the
/// recursion lane's a82a7c83e4 checked-chain resolution).
fn loop_measure_bindings(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
    measure: &str,
) -> Option<(Formula, Formula)> {
    let param_local = unique_parameter_local_by_name(func, measure)?;
    // The lower-bound proof below is over the integer value model. For an
    // unsigned local, `measure >= 0` is a type invariant at every iteration;
    // a signed function-entry precondition is not a loop invariant and must
    // not be silently reused as one.
    if !param_local.ty.is_integer() || param_local.ty.is_signed() {
        return None;
    }
    let assigns = assignments_to_local_in_body(func, &loop_info.body_blocks, param_local.index);
    if assigns.len() != 1 {
        return None;
    }
    let (assignment_block, assignment) = assigns[0];

    // The step must execute on every path that reaches this latch. A sole
    // assignment somewhere in the natural-loop set is insufficient: it may
    // sit behind a branch that the backedge bypasses.
    let dominators = compute_dominators(&func.body);
    if !dominators.get(loop_info._latch.0).is_some_and(|set| set.contains(&assignment_block.0)) {
        return None;
    }
    // SF-1 (adversarial-verify finding, docs/design-notes/
    // 2026-07-13-adversarial-verify-findings.md): the step must dominate EVERY
    // back-edge of this header, not just this LoopInfo's latch. detect_loops
    // mints one LoopInfo per back-edge, so a two-latch loop like
    // `while n > 0 { if c { continue; } n -= 1; }` would bind the measure off
    // the decrementing latch and mint a Proved termination obligation while
    // the `continue` latch — which can re-enter the header forever without
    // executing the step — silently emits nothing. Silence must not stand in
    // for the unproved back-edge: DECLINE the binding unless the step
    // dominates every latch of this header (single-latch loops are unaffected;
    // this can only remove Proved outcomes, never mint one).
    let header = loop_info.header;
    for block in &func.body.blocks {
        let is_back_edge_source = block_successors(&block.terminator).contains(&header)
            && dominators.get(block.id.0).is_some_and(|d| d.contains(&header.0));
        if is_back_edge_source
            && !dominators.get(block.id.0).is_some_and(|d| d.contains(&assignment_block.0))
        {
            return None;
        }
    }
    if loop_measure_has_write_risk(func, loop_info, param_local.index) {
        return None;
    }
    // rung-F loop checked-chain: the debug-build step `n = move (_T.0)` —
    // the unpack of an overflow-checked op computed in the step block's
    // unique IN-LOOP Assert-predecessor — resolves to the Assert-success
    // value `lhs op rhs`. The resolver carries its own fail-closed guard
    // set (including operand stability); any decline falls through to the
    // direct one-block path, which accepts only an exact bare integer
    // copy/constant. Raw fixed-width arithmetic is never reinterpreted as
    // mathematical Int here.
    let after = match resolve_loop_checked_step_chain(
        func,
        loop_info,
        assignment_block,
        assignment,
        param_local.index,
    ) {
        Some(after) => after,
        None => {
            if !measure_step_inputs_are_stable(func, assignment, param_local.index) {
                return None;
            }
            exact_loop_step_formula(func, assignment)?
        }
    };
    let before =
        Formula::Var(crate::place_to_var_name(func, &Place::local(param_local.index)), Sort::Int);
    Some((before, after))
}

/// Fail closed if the loop has a second or opaque write channel for the
/// candidate measure. `assignments_to_local_in_body` has already established
/// exactly one whole-local `Assign`; this guards projections, call results,
/// mutable/raw escapes, and IR channels whose writes cannot be enumerated.
fn loop_measure_has_write_risk(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
    measure_local: usize,
) -> bool {
    let in_loop: FxHashSet<usize> = loop_info.body_blocks.iter().map(|id| id.0).collect();
    for block in &func.body.blocks {
        let block_is_in_loop = in_loop.contains(&block.id.0);
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    if block_is_in_loop
                        && place.local == measure_local
                        && !place.projections.is_empty()
                    {
                        return true;
                    }
                    // An escape created anywhere in the function can be used
                    // by a call in the loop, so this is deliberately a
                    // whole-body gate rather than a loop-local one.
                    if matches!(rvalue, Rvalue::Ref { mutable: true, place } if place.local == measure_local)
                        || matches!(rvalue, Rvalue::AddressOf(_, place) if place.local == measure_local)
                    {
                        return true;
                    }
                }
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place }
                    if block_is_in_loop && place.local == measure_local =>
                {
                    return true;
                }
                Statement::Intrinsic { .. } | Statement::Unsupported { .. } if block_is_in_loop => {
                    return true;
                }
                _ => {}
            }
        }
        if !block_is_in_loop {
            continue;
        }
        match &block.terminator {
            Terminator::Call { dest, .. } if dest.local == measure_local => return true,
            Terminator::Opaque { .. } => return true,
            _ => {}
        }
    }
    false
}

/// Every non-measure input to the arithmetic step must denote one stable value
/// across the body. Otherwise a function-entry fact about that input can be
/// mistaken for a loop invariant (for example, `d > 0; d = 0; n -= d`).
fn measure_step_inputs_are_stable(
    func: &VerifiableFunction,
    rvalue: &Rvalue,
    measure_local: usize,
) -> bool {
    let stable_operand = |operand: &Operand| match operand {
        Operand::Constant(_) => true,
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => {
            place.local == measure_local || !local_ever_mutated(func, place.local)
        }
        _ => false,
    };
    match rvalue {
        Rvalue::Use(operand) | Rvalue::UnaryOp(UnOp::Neg, operand) => stable_operand(operand),
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            stable_operand(lhs) && stable_operand(rhs)
        }
        _ => false,
    }
}

/// Same idea for recursion: bind `measure_entry` to one uniquely named integer
/// parameter and `measure_call` to either an exact direct operand or the exact
/// success value of a checked-arithmetic Assert chain.
///
/// rung-F u32-bound: when the measure parameter's type is an UNSIGNED
/// integer, the parameter's type bound (`measure >= 0`) is conjoined as a
/// def. Without it the `measure_entry < 0` disjunct of the non-decreasing
/// encoding is satisfiable at an out-of-type model point (e.g.
/// `num_params = -1` for a `u32` measure), leaving a terminating
/// `f(n) -> f(n - 1)` recursion's VC SAT — undischargeable — for any
/// consumer of the RAW VC (the trust-clean census lane re-derives the same
/// bound via `augment_with_type_bounds`, but the VC itself must be
/// self-contained for every backend behind trust-router). The bound is a
/// TAUTOLOGY of the type in the extraction's value model (unsigned locals
/// are modeled by their non-negative integer value), so conjoining it can
/// only remove out-of-type models — it never masks a genuine
/// non-decreasing witness, which lives in the `measure_call >=
/// measure_entry` disjunct and is unaffected (see
/// `test_non_decreasing_u32_recursion_vc_stays_sat`). Raw fixed-width
/// arithmetic is NOT imported from the call block: modeling `u8` subtraction
/// as mathematical Int would falsely prove the wrapping cycle `f(n - 1)`.
/// Checked Add/Sub/Mul is admitted only through the exact Assert-success chain
/// below, where no overflow occurred. SIGNED measures get NO bound: they really
/// can descend below zero (`test_i32_recursion_vc_has_no_false_nonneg_bound`).
fn recursion_measure_bindings(
    func: &VerifiableFunction,
    call: &RecursiveCallSite,
    measure: &str,
) -> Option<(Formula, Formula, Vec<Formula>, Option<SourceSpan>)> {
    let measure_decl = unique_parameter_local_by_name(func, measure)?;
    if measure_decl.ty.int_width().is_none() {
        return None;
    }
    let param_pos = measure_decl.index.checked_sub(1)?;
    let arg = call.args.get(param_pos)?;
    let entry =
        Formula::Var(crate::place_to_var_name(func, &Place::local(measure_decl.index)), Sort::Int);
    // rung-F checked-chain: when the measure argument is the `.0` unpack of
    // an overflow-checked op living in the UNIQUE Assert-predecessor block
    // (the debug-build `n - 1` shape: `_3 = CheckedSub(n, 1);
    // Assert(!_3.1) -> bbC: _4 = _3.0; call self(_4)`), substitute the
    // Assert-success value (`Sub(n, 1)`) for the otherwise-free temp. See
    // `resolve_checked_arg_chain` for the fail-closed applicability guards.
    let block = func.body.blocks.iter().find(|b| b.id == call.block)?;
    let (call_arg, exact_site_span) =
        if let Some((checked, span)) = resolve_checked_arg_chain(func, block, arg) {
            (checked, Some(span))
        } else {
            // Importing same-block definitions here used to turn raw fixed-width
            // arithmetic into unbounded Int equalities. Decline until exact BV/domain
            // lowering exists. Comparisons/copies are deliberately not assumed either:
            // a direct bare operand needs no definition, and an unconstrained temp can
            // only prevent a proof.
            if block_has_unmodeled_recursion_arithmetic(func, block) {
                return None;
            }
            (exact_recursion_operand_formula(func, arg)?, None)
        };
    let mut facts = Vec::new();
    if !measure_decl.ty.is_signed() {
        facts.push(Formula::Ge(Box::new(entry.clone()), Box::new(Formula::Int(0))));
    }
    Some((entry, call_arg, facts, exact_site_span))
}

/// A direct recursion measure operand representable without call-block
/// dataflow. Opaque/symbolic/unsupported constants and projected places are
/// rejected instead of collapsing onto a reusable synthetic symbol.
fn exact_recursion_operand_formula(
    func: &VerifiableFunction,
    operand: &Operand,
) -> Option<Formula> {
    match operand {
        Operand::Copy(place) | Operand::Move(place)
            if place.projections.is_empty()
                && func.body.locals.get(place.local).is_some_and(|decl| {
                    decl.index == place.local && decl.ty.int_width().is_some()
                }) =>
        {
            Some(crate::operand_to_formula(func, operand))
        }
        Operand::Constant(ConstValue::Int(_) | ConstValue::Uint(_, _)) => {
            Some(crate::operand_to_formula(func, operand))
        }
        Operand::Constant(_)
        | Operand::Symbolic(_)
        | Operand::Unsupported { .. }
        | Operand::Copy(_)
        | Operand::Move(_) => None,
        _ => None,
    }
}

/// Raw machine arithmetic in a call block has no exact Int interpretation.
/// Checked ops are included: the sole admitted shape returns before this gate
/// through `resolve_checked_arg_chain`.
fn block_has_unmodeled_recursion_arithmetic(func: &VerifiableFunction, block: &BasicBlock) -> bool {
    block.stmts.iter().any(|stmt| {
        let Statement::Assign { rvalue, .. } = stmt else {
            return false;
        };
        match rvalue {
            Rvalue::BinaryOp(op, lhs, _) | Rvalue::CheckedBinaryOp(op, lhs, _)
                if matches!(
                    op,
                    BinOp::Add
                        | BinOp::Sub
                        | BinOp::Mul
                        | BinOp::Div
                        | BinOp::Rem
                        | BinOp::Shl
                        | BinOp::Shr
                ) =>
            {
                crate::operand_ty_cow(func, lhs).as_deref().and_then(Ty::int_width).is_some()
            }
            Rvalue::UnaryOp(UnOp::Neg | UnOp::Not, operand) => {
                crate::operand_ty_cow(func, operand).as_deref().and_then(Ty::int_width).is_some()
            }
            _ => false,
        }
    })
}

/// rung-F checked-chain: resolve a recursive call's measure argument THROUGH
/// the overflow-checked binary op that produced it in the call block's unique
/// Assert-predecessor.
///
/// Target shape (rustc's checked-arithmetic lowering, the REAL
/// `infer_implicit_n` MIR measured on the census dump 2026-07-11):
/// ```text
///   bbP: _T = CheckedSub(n, 1)
///        Assert(cond: move (_T.1), expected: false, Overflow(Sub)) -> bbC
///   bbC: _A = move (_T.0)
///        call self(.., move _A, ..)
/// ```
/// `extract_block_definitions(bbC)` yields only `_A == _T.0` with `_T.0`
/// FREE (the `CheckedBinaryOp` def is in ANOTHER block, and is skipped by the
/// scalar def extraction anyway), so the non-decreasing disjunct
/// `_A >= n` is satisfiable at any model point — no type bound can help.
/// On the Assert's SUCCESS edge (the only edge into `bbC` under the guards
/// below) the op did NOT overflow, so the machine value of `_T.0` IS the
/// mathematical `lhs op rhs`; substituting that formula for the call measure
/// is exact.
///
/// FAIL-CLOSED applicability guards — any miss returns `None` and the caller
/// falls back to the unresolved operand formula (the VC stays SAT, i.e.
/// undischargeable; a decline can never manufacture a proof):
/// 1. the argument is either a direct `Copy/Move(_T.0)` (optimized MIR), or a
///    bare-local read `_A` whose LAST call-block assignment is exactly
///    `_A = Copy/Move(_T.0)` (unoptimized MIR), and `_T` is not written in the
///    call block;
/// 2. the call block has EXACTLY ONE CFG predecessor, and it is an
///    `Assert { cond: _T.1, expected: false }` targeting the call block — a
///    second in-edge would bypass the no-overflow fact;
/// 3. the predecessor's LAST write to `_T` is `CheckedBinaryOp(Add|Sub|Mul,
///    lhs, rhs)` assigned to the WHOLE tuple;
/// 4. each operand is an integer constant or a bare-local read of a local
///    that is NEVER mutated anywhere in the body (no assignment, no call
///    dest, no `&mut`/`&raw` escape, and no `Opaque` terminator in the body
///    at all) — so its VC var denotes one value and the substitution cannot
///    equivocate between program points.
///
/// Guards 2–4 are shared with the loop-lane port as
/// `checked_chain_through_assert_pred` (the recursion lane passes an EMPTY
/// mutable-operand allowance, preserving the exact a82a7c83e4 behavior).
fn resolve_checked_arg_chain(
    func: &VerifiableFunction,
    call_block: &BasicBlock,
    arg: &Operand,
) -> Option<(Formula, SourceSpan)> {
    // Entry is reached directly when the function starts. An explicit CFG
    // predecessor targeting bb0 cannot establish that its Assert ran before
    // the entry block's first execution.
    if call_block.id.0 == 0 {
        return None;
    }
    // Guard 1: optimized MIR passes `_T.0` directly; unoptimized MIR first
    // unpacks it into `_A` in the call block. Keep the optional `_A` only for
    // the write-risk check below.
    let (arg_local, tuple_local) = match arg {
        Operand::Copy(p) | Operand::Move(p)
            if p.projections.len() == 1 && matches!(p.projections[0], Projection::Field(0)) =>
        {
            (None, p.local)
        }
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
            let arg_local = p.local;
            let mut tuple_local = None;
            for stmt in call_block.stmts.iter().rev() {
                let Statement::Assign { place, rvalue, .. } = stmt else {
                    continue;
                };
                if place.local != arg_local {
                    continue;
                }
                if !place.projections.is_empty() {
                    return None;
                }
                let Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) = rvalue else {
                    return None;
                };
                if src.projections.len() != 1 || !matches!(src.projections[0], Projection::Field(0))
                {
                    return None;
                }
                tuple_local = Some(src.local);
                break;
            }
            (Some(arg_local), tuple_local?)
        }
        _ => return None,
    };
    let writes_tuple = call_block
        .stmts
        .iter()
        .any(|stmt| matches!(stmt, Statement::Assign { place, .. } if place.local == tuple_local));
    if writes_tuple {
        return None;
    }
    let mut chain_locals = vec![tuple_local];
    if let Some(arg_local) = arg_local {
        chain_locals.push(arg_local);
    }
    if block_has_nonassign_write_risk(call_block, &chain_locals) {
        return None;
    }

    let (pred, op, lhs, rhs) =
        checked_chain_through_assert_pred(func, call_block, tuple_local, &[])?;
    Some((checked_op_formula(func, op, lhs, rhs), terminator_span(&pred.terminator)))
}

/// Shared guards 2–4 of the checked-chain resolution (extracted verbatim from
/// the recursion lane's `resolve_checked_arg_chain`, a82a7c83e4; also used by
/// the loop-lane port `resolve_loop_checked_step_chain`): starting from the
/// block that CONSUMES `_T.0`, find its unique no-overflow
/// `Assert`-predecessor, extract the whole-tuple `CheckedBinaryOp` that wrote
/// `_T`, and vet the operands. Any miss returns `None` (fail-closed).
///
/// `mutable_operand_allowance` lists locals an operand may name even though
/// they are mutated somewhere in the body — the CALLER must have separately
/// pinned their value at the checked op's read point. The recursion lane
/// passes `&[]` (never-mutated rule, unchanged); the loop lane passes its
/// measure local, whose ONLY in-loop write is the step assignment itself
/// (established by the caller's single-assignment + write-risk gates), which
/// is sequenced strictly after the checked op's read on every `bbP -> bbS`
/// path — so the read denotes the pre-iteration value, exactly what
/// `Var(measure)` means in the loop VC.
fn checked_chain_through_assert_pred<'a>(
    func: &'a VerifiableFunction,
    block: &BasicBlock,
    tuple_local: usize,
    mutable_operand_allowance: &[usize],
) -> Option<(&'a BasicBlock, BinOp, &'a Operand, &'a Operand)> {
    // Guard 2: unique predecessor, and it is the no-overflow Assert on `_T.1`.
    let mut preds =
        func.body.blocks.iter().filter(|b| block_successors(&b.terminator).contains(&block.id));
    let pred = preds.next()?;
    if preds.next().is_some() {
        return None;
    }
    let Terminator::Assert { cond, expected: false, target, .. } = &pred.terminator else {
        return None;
    };
    if *target != block.id {
        return None;
    }
    let cond_place = match cond {
        Operand::Copy(p) | Operand::Move(p) => p,
        _ => return None,
    };
    if cond_place.local != tuple_local
        || cond_place.projections.len() != 1
        || !matches!(cond_place.projections[0], Projection::Field(1))
    {
        return None;
    }

    // Guard 3: the predecessor's live write to `_T` is the checked op.
    let mut checked = None;
    for stmt in pred.stmts.iter().rev() {
        let Statement::Assign { place, rvalue, .. } = stmt else {
            continue;
        };
        if place.local != tuple_local {
            continue;
        }
        if !place.projections.is_empty() {
            return None;
        }
        let Rvalue::CheckedBinaryOp(op, lhs, rhs) = rvalue else {
            return None;
        };
        checked = Some((*op, lhs, rhs));
        break;
    }
    let (op, lhs, rhs) = checked?;
    if !matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
        return None;
    }
    if block_has_nonassign_write_risk(pred, &[tuple_local]) {
        return None;
    }

    // Guard 4: operands are constants or bare locals whose VC var denotes one
    // value — never mutated in the body, or explicitly vouched for by the
    // caller (see `mutable_operand_allowance` above).
    for operand in [lhs, rhs] {
        match operand {
            Operand::Constant(ConstValue::Int(_) | ConstValue::Uint(_, _)) => {}
            Operand::Copy(p) | Operand::Move(p)
                if p.projections.is_empty()
                    && func.body.locals.get(p.local).is_some_and(|decl| {
                        decl.index == p.local && decl.ty.int_width().is_some()
                    }) =>
            {
                if !mutable_operand_allowance.contains(&p.local)
                    && local_ever_mutated(func, p.local)
                {
                    return None;
                }
            }
            _ => return None,
        }
    }

    Some((pred, op, lhs, rhs))
}

/// The Assert-success value of a checked binary op: the exact mathematical
/// `lhs op rhs` (on the success edge the op did not overflow, so the machine
/// value of `_T.0` IS this formula).
fn checked_op_formula(
    func: &VerifiableFunction,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
) -> Formula {
    let l = crate::operand_to_formula(func, lhs);
    let r = crate::operand_to_formula(func, rhs);
    match op {
        BinOp::Add => Formula::Add(Box::new(l), Box::new(r)),
        BinOp::Sub => Formula::Sub(Box::new(l), Box::new(r)),
        BinOp::Mul => Formula::Mul(Box::new(l), Box::new(r)),
        _ => unreachable!("checked_chain_through_assert_pred gates to Add|Sub|Mul"),
    }
}

/// rung-F loop-lane port of the checked-chain resolution (recursion lane:
/// `resolve_checked_arg_chain`, landed a82a7c83e4; the loop-lane parity gap
/// was pinned by trust-clean's
/// `u32_checked_sub_loop_emits_no_nontermination_vc_yet`): resolve a loop's
/// measure STEP through the overflow-checked binary op that produced it in
/// the step block's unique Assert-predecessor.
///
/// Target shape (rustc's debug-build checked decrement, split across two
/// blocks):
/// ```text
///   bbP: _T = CheckedSub(n, 1)
///        Assert(cond: move (_T.1), expected: false, Overflow(Sub)) -> bbS
///   bbS: n = move (_T.0)
///        goto header                                        (back-edge)
/// ```
/// The direct one-block lowering declines this step (`_T.0` is a projected
/// read; `measure_step_inputs_are_stable` fails closed), so the landed lane
/// emitted NO obligation for the debug-shape countdown. On the Assert's
/// SUCCESS edge — the only way into `bbS` under the guards below — the op
/// did not overflow, so the machine value of `_T.0` IS the mathematical
/// `lhs op rhs`; substituting it for the step is exact.
///
/// FAIL-CLOSED applicability guards — any miss returns `None`, the caller
/// falls back to the direct path (which declines this shape), and the
/// exit-ful loop yields no obligation (open; a decline can never manufacture
/// a proof). On top of the shared recursion-lane guards
/// (`checked_chain_through_assert_pred`: unique Assert-pred on `_T.1`; live
/// whole-tuple `CheckedBinaryOp(Add|Sub|Mul)`; no non-`Assign` write channel
/// in either block; stable operands), the LOOP lane adds:
/// - the step block must NOT be the function ENTRY block: control
///   materializes there at function start without traversing any CFG edge,
///   so a unique explicit predecessor cannot establish that the Assert
///   precedes the first step execution (nor the pred-dominates-step fact the
///   substitution rests on);
/// - the Assert-predecessor must be INSIDE this loop's `body_blocks`: an
///   outside predecessor means the checked op runs ONCE, before the loop —
///   the step then re-assigns the SAME value every iteration (a
///   loop-INVARIANT step: `while n > 0 { n = k }` stalls forever for
///   `k > 0`), and substituting `lhs op rhs` would fabricate a fresh
///   decrease per iteration — a false termination proof. (For today's
///   `natural_loop_blocks` every predecessor of a non-header body block is
///   already in the body, and header/entry cases are excluded by the other
///   guards, so this is defense-in-depth against future body-set changes —
///   pinned directly by
///   `test_checked_sub_loop_assert_pred_outside_body_blocks_declines`.)
/// - `_T` must not be written in the step block (Assign channel here;
///   non-Assign channels via `block_has_nonassign_write_risk`);
/// - operands may name the MEASURE local itself (unlike the recursion
///   lane's never-mutated rule) — see `checked_chain_through_assert_pred`'s
///   allowance contract for why that read denotes `measure_before`. Any
///   OTHER mutated operand still declines.
fn resolve_loop_checked_step_chain(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
    step_block_id: BlockId,
    step_rvalue: &Rvalue,
    measure_local: usize,
) -> Option<Formula> {
    // Loop guard: never resolve a step living in the function entry block.
    if step_block_id.0 == 0 {
        return None;
    }
    // Step shape: `n = Copy/Move(_T.0)` (the whole-local destination is
    // already established by `assignments_to_local_in_body`).
    let Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) = step_rvalue else {
        return None;
    };
    if src.projections.len() != 1 || !matches!(src.projections[0], Projection::Field(0)) {
        return None;
    }
    let tuple_local = src.local;
    let step_block = func.body.blocks.iter().find(|b| b.id == step_block_id)?;
    let writes_tuple = step_block
        .stmts
        .iter()
        .any(|stmt| matches!(stmt, Statement::Assign { place, .. } if place.local == tuple_local));
    if writes_tuple {
        return None;
    }
    if block_has_nonassign_write_risk(step_block, &[tuple_local, measure_local]) {
        return None;
    }
    let (pred, op, lhs, rhs) =
        checked_chain_through_assert_pred(func, step_block, tuple_local, &[measure_local])?;
    // Loop guard: the Assert-predecessor must be part of THIS loop's body —
    // an outside pred is a once-before-the-loop computation (loop-invariant
    // step), not a per-iteration decrement.
    if !loop_info.body_blocks.contains(&pred.id) {
        return None;
    }
    Some(checked_op_formula(func, op, lhs, rhs))
}

/// Non-`Assign` write channels inside one block that could interpose on the
/// checked-chain's `_T -> _A` value flow: a `SetDiscriminant`/`Deinit` on one
/// of the chain locals, or ANY `Intrinsic`/`Unsupported`/unknown-variant
/// statement (their write targets are invisible). The plain `Assign` channel
/// is handled by the caller's own scans. Fail-closed: `true` declines.
fn block_has_nonassign_write_risk(block: &BasicBlock, locals: &[usize]) -> bool {
    block.stmts.iter().any(|stmt| match stmt {
        Statement::Assign { .. } => false,
        Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
            locals.contains(&place.local)
        }
        Statement::Intrinsic { .. } | Statement::Unsupported { .. } => true,
        Statement::StorageLive(_)
        | Statement::StorageDead(_)
        | Statement::Retag { .. }
        | Statement::PlaceMention(_)
        | Statement::Coverage
        | Statement::ConstEvalCounter
        | Statement::Nop => false,
        // #[non_exhaustive]: unknown future statement — assume write risk.
        _ => true,
    })
}

/// Conservative whole-body mutation check for `resolve_checked_arg_chain`
/// guard 4: `true` unless the local provably keeps its entry value for the
/// whole body. Writers considered: any `Assign` touching the local (any
/// projection), any `Call` destination, any `&mut`/`&raw` escape of it
/// (through which a callee or later statement could write), and — because the
/// `Opaque` terminator's write channel is invisible (`WriteEffect` docs) —
/// ANY `Opaque` terminator in the body at all. Fail-closed: over-reporting
/// mutation only declines the resolution.
fn local_ever_mutated(func: &VerifiableFunction, local: usize) -> bool {
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            // EXHAUSTIVE statement classification (no wildcard) so a new
            // write channel cannot silently bypass this guard.
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    if place.local == local {
                        return true;
                    }
                    match rvalue {
                        Rvalue::Ref { mutable: true, place: p } if p.local == local => {
                            return true;
                        }
                        Rvalue::AddressOf(_, p) if p.local == local => return true,
                        _ => {}
                    }
                }
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                    if place.local == local {
                        return true;
                    }
                }
                // Unknown write channels — fail closed.
                Statement::Intrinsic { .. } | Statement::Unsupported { .. } => return true,
                // Genuinely non-writing markers.
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::Retag { .. }
                | Statement::PlaceMention(_)
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::Nop => {}
                // `Statement` is #[non_exhaustive]: a future variant is an
                // unknown write channel — fail closed.
                _ => return true,
            }
        }
        match &block.terminator {
            Terminator::Call { dest, .. } if dest.local == local => return true,
            Terminator::Opaque { .. } => return true,
            _ => {}
        }
    }
    false
}

/// Look up exactly one function parameter by its canonical verifier name.
///
/// A raw source/debug name is insufficient: `place_to_var_name` deliberately
/// demotes names that collide with another local or with the fallback `_N`
/// vocabulary. Accepting such a name here while constructing `Var(name)` would
/// disconnect the authored measure from the executable argument. Require the
/// single source of truth for VC variable naming to preserve the name exactly;
/// every collision or fallback-shaped mismatch remains unsupported.
fn unique_parameter_local_by_name<'a>(
    func: &'a VerifiableFunction,
    name: &str,
) -> Option<&'a LocalDecl> {
    if func.body.arg_count == 0 {
        return None;
    }
    let end = (func.body.arg_count + 1).min(func.body.locals.len());
    let mut matches =
        func.body.locals[1..end].iter().filter(|decl| decl.name.as_deref() == Some(name));
    let unique = matches.next()?;
    (matches.next().is_none()
        && crate::place_to_var_name(func, &Place::local(unique.index)) == name)
        .then_some(unique)
}

/// All assignment sites and rvalues targeting `local_idx` (no projections)
/// within the given body blocks, in CFG order. Used to detect whether the loop
/// body modifies the measure local exactly once and whether that site
/// dominates the latch.
fn assignments_to_local_in_body<'a>(
    func: &'a VerifiableFunction,
    body_blocks: &[BlockId],
    local_idx: usize,
) -> Vec<(BlockId, &'a Rvalue)> {
    let in_loop: FxHashSet<usize> = body_blocks.iter().map(|b| b.0).collect();
    let mut out = Vec::new();
    for block in &func.body.blocks {
        if !in_loop.contains(&block.id.0) {
            continue;
        }
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt
                && place.local == local_idx
                && place.projections.is_empty()
            {
                out.push((block.id, rvalue));
            }
        }
    }
    out
}

/// Lower only a loop step whose machine meaning is already exact in the
/// mathematical-Int termination carrier.
///
/// Raw `BinaryOp`/`CheckedBinaryOp` and integer `Neg`/`Not` are deliberately
/// rejected. For example, lowering a raw `u8` step `n = n - 1` as `n - 1`
/// proves descent over Int while the executable step wraps `0 -> 255`. Checked
/// arithmetic is admitted solely by `resolve_loop_checked_step_chain`, after
/// its no-overflow Assert-success edge has been structurally established.
fn exact_loop_step_formula(func: &VerifiableFunction, r: &Rvalue) -> Option<Formula> {
    match r {
        Rvalue::Use(op) => exact_recursion_operand_formula(func, op),
        _ => None,
    }
}

/// Get all successor block IDs from a terminator.
fn block_successors(term: &Terminator) -> Vec<BlockId> {
    match term {
        Terminator::Goto(target) => vec![*target],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            let mut succs: Vec<BlockId> = targets.iter().map(|(_, t)| *t).collect();
            succs.push(*otherwise);
            succs
        }
        Terminator::Return | Terminator::Unreachable => vec![],
        Terminator::Call { target, .. } => target.iter().copied().collect(),
        Terminator::Assert { target, .. } => vec![*target],
        Terminator::Drop { target, .. } => vec![*target],
        Terminator::Opaque { targets, .. } => targets.clone(),
        _ => vec![],
    }
}

/// Does control have any way to leave the loop body?
///
/// Returns `true` if some block in the loop body either (a) has a successor
/// outside the body, or (b) ends in a terminator with no successors at all
/// (`Return`/`Unreachable`/`Resume`/`Terminate`/diverging `Call`), which
/// also lets control escape the loop (via function return or divergence).
///
/// `false` means *no* edge leaves the body: the loop is a provable infinite
/// loop (given its header is reachable). We use this to decide whether a
/// loop with no bindable decreasing measure should still get a termination
/// obligation: only exit-less loops do, so we never fabricate a spurious
/// non-termination failure on a terminating-but-unmeasurable loop.
///
/// The body-block set is the exact natural-loop set recovered by
/// `detect_loops`; block allocation order is never used as CFG structure.
fn loop_has_exit(body: &VerifiableBody, loop_info: &LoopInfo) -> bool {
    let in_loop: FxHashSet<usize> = loop_info.body_blocks.iter().map(|b| b.0).collect();
    for bid in &loop_info.body_blocks {
        let Some(bb) = body.blocks.iter().find(|b| b.id == *bid) else {
            continue;
        };
        let succs = block_successors(&bb.terminator);
        if succs.is_empty() {
            return true;
        }
        if succs.iter().any(|s| !in_loop.contains(&s.0)) {
            return true;
        }
    }
    false
}

/// Trust: piece #13 step-2 (safe-async data-safety) — whether `loop_info` is a
/// COROUTINE resume-state PROTOCOL SINK, i.e. an exit-less loop every one of
/// whose blocks terminates in a `ResumedAfter{Return,Panic,Drop}` assert. The
/// compiler lowers an `async fn` / coroutine's "resumed after completion /
/// panicking / drop" states as `assert(false, ResumedAfter*) -> [success:
/// <self>]` — a self-loop with no exit — which `loop_has_exit` reports as
/// non-terminating. That is an EXECUTOR-PROTOCOL property (a well-behaved
/// executor never re-polls a completed/panicked/dropped future), NOT genuine
/// non-termination of the user's code, so it must NOT emit a fatal
/// `NonTermination` refutation.
///
/// SOUNDNESS: this matches ONLY when EVERY block of the loop is a `ResumedAfter*`
/// protocol assert. A genuine user infinite loop (`loop {}`, `while true {}`)
/// contains a `Goto`/`SwitchInt`/other terminator, never a `ResumedAfter*`
/// assert, so it does NOT match and still emits its `NonTermination` VC — the
/// real non-termination detection is unweakened. `body_blocks` is non-empty for
/// any detected loop, so the `all` is never vacuously true.
fn loop_is_coroutine_protocol_sink(func: &VerifiableFunction, loop_info: &LoopInfo) -> bool {
    !loop_info.body_blocks.is_empty()
        && loop_info.body_blocks.iter().all(|bid| {
            func.body.blocks.iter().find(|b| b.id == *bid).is_some_and(|bb| {
                matches!(
                    &bb.terminator,
                    Terminator::Assert {
                        msg: AssertMessage::ResumedAfterReturn
                            | AssertMessage::ResumedAfterPanic
                            | AssertMessage::ResumedAfterDrop,
                        ..
                    }
                )
            })
        })
}

/// Extract a source span from a terminator, falling back to default.
fn terminator_span(term: &Terminator) -> SourceSpan {
    match term {
        Terminator::SwitchInt { span, .. }
        | Terminator::Call { span, .. }
        | Terminator::Assert { span, .. }
        | Terminator::Drop { span, .. }
        | Terminator::Opaque { span, .. } => span.clone(),
        _ => SourceSpan::default(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// SF-1 regression (adversarial-verify findings, 2026-07-13): a TWO-LATCH
    /// loop — `while n > 0 { if c { continue; } n -= 1; }` — must NOT mint a
    /// termination obligation from the decrementing latch alone: the
    /// `continue` latch re-enters the header without executing the step and
    /// can spin forever. Pre-guard, the decrement latch's LoopInfo bound the
    /// measure (its step dominates ITS latch) and the refuted VC graded
    /// Proved while the continue latch emitted nothing.
    /// MIR:
    ///   bb0: cond = n > 0; SwitchInt(cond) -> [1: bb1, otherwise: bb4]
    ///   bb1: SwitchInt(c) -> [1: bb2, otherwise: bb3]
    ///   bb2: goto bb0                (continue latch — NO step)
    ///   bb3: n = n - 1; goto bb0     (decrement latch — the step)
    ///   bb4: return
    fn two_latch_continue_loop() -> VerifiableFunction {
        VerifiableFunction {
            name: "two_latch".to_string(),
            def_path: "test::two_latch".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: Some("c".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("cond".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Gt,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(0, 64)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(3)),
                            targets: vec![(1, BlockId(1))],
                            otherwise: BlockId(4),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(2)),
                            targets: vec![(1, BlockId(2))],
                            otherwise: BlockId(3),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    // continue latch: back-edge with NO measure step
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![],
                        terminator: Terminator::Goto(BlockId(0)),
                    },
                    // decrement latch: the sole step
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![Statement::Assign {
                            place: Place::local(1),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Sub,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(1, 64)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Goto(BlockId(0)),
                    },
                    BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 2,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn sf1_two_latch_loop_declines_measure_binding() {
        let func = two_latch_continue_loop();
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        // No termination obligation may be minted off the decrementing latch:
        // a Proved outcome here would be a false proof (the continue latch can
        // spin forever). Declining leaves honest silence for this exit-ful
        // loop, exactly like other unresolved shapes.
        assert!(
            vcs.iter().all(|vc| !matches!(vc.kind, VcKind::NonTermination { .. })),
            "two-latch loop must not mint a NonTermination measure VC, got {vcs:?}"
        );
    }

    /// Build a function with a simple counted loop:
    /// ```
    /// fn countdown(mut n: u32) {
    ///     while n > 0 { n -= 1; }
    /// }
    /// ```
    /// MIR:
    ///   bb0: SwitchInt(n > 0) -> [1: bb1, otherwise: bb2]
    ///   bb1: n = n - 1; goto bb0   (back-edge to bb0)
    ///   bb2: return
    fn countdown_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "countdown".to_string(),
            def_path: "test::countdown".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: Some("cond".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![
                            // cond = n > 0
                            Statement::Assign {
                                place: Place::local(2),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Gt,
                                    Operand::Copy(Place::local(1)),
                                    Operand::Constant(ConstValue::Uint(0, 64)),
                                ),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(2)),
                            targets: vec![(1, BlockId(1))],
                            otherwise: BlockId(2),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan {
                                file: "test.rs".into(),
                                line_start: 2,
                                col_start: 5,
                                line_end: 2,
                                col_end: 30,
                            },
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![
                            // n = n - 1
                            Statement::Assign {
                                place: Place::local(1),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Sub,
                                    Operand::Copy(Place::local(1)),
                                    Operand::Constant(ConstValue::Uint(1, 64)),
                                ),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Goto(BlockId(0)), // back-edge
                    },
                    BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// A loop whose only apparent decrement is conditional:
    /// `take_step == false` reaches the latch without executing `n -= 1`.
    /// Treating the sole assignment anywhere in the loop as the per-backedge
    /// step would falsely prove this loop terminating for `n > 0`.
    fn conditional_decrement_loop_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "conditional_countdown".to_string(),
            def_path: "test::conditional_countdown".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: Some("take_step".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("keep_going".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Gt,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(0, 32)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(3)),
                            targets: vec![(1, BlockId(1))],
                            otherwise: BlockId(4),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(2)),
                            targets: vec![(1, BlockId(2))],
                            otherwise: BlockId(3),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(1),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Sub,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(1, 32)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Goto(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![],
                        terminator: Terminator::Goto(BlockId(0)),
                    },
                    BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 2,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Block IDs 2 and 3 lie numerically between the loop header/latch but are
    /// not in the loop. The old ID-range body admitted their assignments.
    fn noncontiguous_loop_function() -> VerifiableFunction {
        let mut func = conditional_decrement_loop_function();
        func.name = "noncontiguous_loop".to_string();
        func.def_path = "test::noncontiguous_loop".to_string();
        func.body.blocks = vec![
            BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Goto(BlockId(1)) },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    targets: vec![(1, BlockId(4))],
                    otherwise: BlockId(5),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Sub,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Uint(1, 32)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Goto(BlockId(5)),
            },
            BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Goto(BlockId(1)) },
            BasicBlock { id: BlockId(5), stmts: vec![], terminator: Terminator::Return },
        ];
        func
    }

    /// Build a function with an infinite loop (no decreasing variable):
    /// ```
    /// fn spin() { loop {} }
    /// ```
    /// MIR:
    ///   bb0: goto bb0  (self-loop)
    fn infinite_loop_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "spin".to_string(),
            def_path: "test::spin".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(0)), // self-loop
                }],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build a recursive function:
    /// ```
    /// fn factorial(n: u32) -> u32 {
    ///     if n == 0 { 1 } else { n * factorial(n - 1) }
    /// }
    /// ```
    fn recursive_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "factorial".to_string(),
            def_path: "test::factorial".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None }, // return
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: None }, // n == 0
                    LocalDecl { index: 3, ty: Ty::u32(), name: None }, // n - 1
                    LocalDecl { index: 4, ty: Ty::u32(), name: None }, // factorial(n-1)
                    LocalDecl { index: 5, ty: Ty::u32(), name: None }, // n * factorial(n-1)
                ],
                blocks: vec![
                    // bb0: check n == 0
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Eq,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(0, 64)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(2)),
                            targets: vec![(1, BlockId(1))],
                            otherwise: BlockId(2),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    // bb1: base case, return 1
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(1, 64))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                    // bb2: recursive case
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Sub,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(1, 64)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Call {
                            unwind: UnwindEdge::Unreachable,
                            is_unsafe_sig: false,
                            is_foreign: false,
                            func: "test::factorial".to_string(),
                            args: vec![Operand::Copy(Place::local(3))],
                            dest: Place::local(4),
                            target: Some(BlockId(3)),
                            span: SourceSpan {
                                file: "test.rs".into(),
                                line_start: 3,
                                col_start: 20,
                                line_end: 3,
                                col_end: 40,
                            },
                            atomic: None,
                        },
                    },
                    // bb3: multiply and return
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(5),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Mul,
                                    Operand::Copy(Place::local(1)),
                                    Operand::Copy(Place::local(4)),
                                ),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(0),
                                rvalue: Rvalue::Use(Operand::Copy(Place::local(5))),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build a function with an explicit decreases clause on recursion.
    fn recursive_with_decreases() -> VerifiableFunction {
        let mut func = recursive_checked_sub_function();
        func.contracts.push(Contract {
            kind: ContractKind::Decreases,
            span: SourceSpan::default(),
            body: "n".to_string(),
        });
        func
    }

    /// A loopless CFG with a cross/forward edge to a LOWER-numbered block.
    /// Mirrors match-guard lowering: the guard-fail path branches to an
    /// already-emitted wildcard-arm block whose ID is lower than the guard
    /// block, but no cycle exists.
    /// ```text
    ///   bb0: SwitchInt -> [1: bb1, otherwise: bb2]
    ///   bb1: return
    ///   bb2: SwitchInt -> [1: bb3, otherwise: bb1]   (bb2 -> bb1: lower ID)
    ///   bb3: return
    /// ```
    /// bb1 does NOT dominate bb2 (bb2 is reachable from bb0 without bb1), so
    /// the edge bb2 -> bb1 is a forward/cross edge, not a back-edge. The old
    /// `succ.0 <= block.id.0` heuristic wrongly flagged it as a loop.
    fn loopless_cross_edge_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "match_guard".to_string(),
            def_path: "test::match_guard".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: None },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(2)),
                            targets: vec![(1, BlockId(1))],
                            otherwise: BlockId(2),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(2)),
                            targets: vec![(1, BlockId(3))],
                            otherwise: BlockId(1), // cross edge to lower-numbered block
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    // --- Tests ---

    #[test]
    fn test_detect_loops_countdown() {
        let func = countdown_function();
        let loops = detect_loops(&func.body);
        assert_eq!(loops.len(), 1, "countdown has exactly one loop");
        assert_eq!(loops[0].header, BlockId(0));
        assert_eq!(loops[0]._latch, BlockId(1));
        assert!(loops[0].body_blocks.contains(&BlockId(0)));
        assert!(loops[0].body_blocks.contains(&BlockId(1)));
    }

    #[test]
    fn test_natural_loop_body_excludes_numeric_interlopers() {
        let func = noncontiguous_loop_function();
        let loops = detect_loops(&func.body);
        assert_eq!(loops.len(), 1);
        assert_eq!(loops[0].header, BlockId(1));
        assert_eq!(loops[0]._latch, BlockId(4));
        assert_eq!(loops[0].body_blocks, vec![BlockId(1), BlockId(4)]);
        assert!(
            modified_int_locals(&func, &loops[0].body_blocks).is_empty(),
            "an unrelated block in the numeric ID interval is not a loop measure source"
        );
    }

    #[test]
    fn test_conditional_measure_step_cannot_bind() {
        let func = conditional_decrement_loop_function();
        let loops = detect_loops(&func.body);
        assert_eq!(loops.len(), 1);
        assert!(loops[0].body_blocks.contains(&BlockId(2)));
        assert!(
            loop_measure_bindings(&func, &loops[0], "n").is_none(),
            "a decrement block that does not dominate the latch is not an unconditional step"
        );
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert!(
            vcs.is_empty(),
            "the existing policy leaves a measurable-but-unproved exiting loop unknown"
        );
    }

    #[test]
    fn test_unbindable_first_modified_local_does_not_hide_valid_measure() {
        let mut func = countdown_function();
        func.body.locals.push(LocalDecl { index: 3, ty: Ty::u32(), name: Some("scratch".into()) });
        func.body.blocks[0].stmts.insert(
            0,
            Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
                span: SourceSpan::default(),
            },
        );
        let Statement::Assign { rvalue, .. } = &mut func.body.blocks[1].stmts[0] else {
            panic!("countdown step is an assignment")
        };
        // Use an exact machine-to-Int step so this test remains about measure
        // selection rather than raw wrapping arithmetic.
        *rvalue = Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32)));
        let loops = detect_loops(&func.body);
        let modified = modified_int_locals(&func, &loops[0].body_blocks);
        assert_eq!(modified[0].1, "scratch");
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert!(matches!(
            &vcs[0].kind,
            VcKind::NonTermination { measure, .. } if measure == "n"
        ));
    }

    #[test]
    fn test_signed_entry_precondition_is_not_reused_as_loop_invariant() {
        let mut func = countdown_function();
        func.body.locals[1].ty = Ty::i32();
        func.preconditions.push(Formula::Ge(
            Box::new(Formula::Var("n".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ));
        let loops = detect_loops(&func.body);
        assert_eq!(loops.len(), 1);
        assert!(
            loop_measure_bindings(&func, &loops[0], "n").is_none(),
            "a function-entry fact is not a signed loop lower-bound invariant"
        );
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert!(vcs.is_empty(), "signed automatic measure must remain unproved");
    }

    #[test]
    fn test_measure_entry_precondition_is_not_reused_at_every_iteration() {
        let mut func = countdown_function();
        // Parameters must occupy locals 1..=arg_count. Insert `d` before the
        // condition temp and move that temp (and its uses) from local 2 to 3.
        func.body.locals.insert(2, LocalDecl { index: 2, ty: Ty::u32(), name: Some("d".into()) });
        func.body.locals[3].index = 3;
        func.body.arg_count = 2;
        let Statement::Assign { place, .. } = &mut func.body.blocks[0].stmts[0] else {
            panic!("countdown guard is an assignment")
        };
        *place = Place::local(3);
        let Terminator::SwitchInt { discr, .. } = &mut func.body.blocks[0].terminator else {
            panic!("countdown guard is a switch")
        };
        *discr = Operand::Copy(Place::local(3));
        let n_gt_d = Formula::Gt(
            Box::new(Formula::Var("n".into(), Sort::Int)),
            Box::new(Formula::Var("d".into(), Sort::Int)),
        );
        let d_positive =
            Formula::Gt(Box::new(Formula::Var("d".into(), Sort::Int)), Box::new(Formula::Int(0)));
        func.preconditions = vec![n_gt_d.clone(), d_positive.clone()];
        let Statement::Assign { rvalue, .. } = &mut func.body.blocks[1].stmts[0] else {
            panic!("countdown step is an assignment")
        };
        // This decreases on the first iteration under `n > d`, then stalls at
        // `n == d` forever while the `n > 0` loop guard remains true.
        *rvalue = Rvalue::Use(Operand::Copy(Place::local(2)));

        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1);
        let Formula::And(clauses) = &vcs[0].formula else {
            panic!("the stable d precondition and loop core are conjoined")
        };
        assert!(clauses.contains(&d_positive), "immutable-input fact remains invariant");
        assert!(
            !clauses.contains(&n_gt_d),
            "function-entry relation on the mutated measure is not a loop invariant"
        );
        assert!(
            vcs[0].formula.free_variables().contains("n"),
            "the unconstrained current measure keeps the non-decrease witness satisfiable"
        );
    }

    #[test]
    fn test_detect_loops_infinite() {
        let func = infinite_loop_function();
        let loops = detect_loops(&func.body);
        assert_eq!(loops.len(), 1, "infinite loop has one back-edge");
        assert_eq!(loops[0].header, BlockId(0));
        assert_eq!(loops[0]._latch, BlockId(0));
    }

    #[test]
    fn test_detect_loops_no_loops() {
        let func = recursive_function();
        let loops = detect_loops(&func.body);
        assert!(loops.is_empty(), "factorial has no loops");
    }

    #[test]
    fn test_detect_loops_loopless_cross_edge_no_false_loop() {
        // Regression: a forward/cross edge to a lower-numbered block must NOT
        // be detected as a loop. The old `succ.0 <= block.id.0` heuristic
        // fabricated a loop here, producing a spurious NonTermination VC on
        // terminating code (the match-guard false-fail). Dominator-based
        // detection sees that the target does not dominate the source.
        let func = loopless_cross_edge_function();
        let loops = detect_loops(&func.body);
        assert!(
            loops.is_empty(),
            "forward/cross edge to a lower block is not a back-edge; got {loops:?}"
        );

        // And the full termination check emits no VC for it.
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert!(vcs.is_empty(), "loopless CFG must produce no termination VCs");
    }

    #[test]
    fn test_compute_dominators_diamond() {
        // Diamond: bb0 -> {bb1, bb2} -> bb3 (the loopless_cross_edge shape,
        // minus the cross edge's effect on dominators). Verify the dominator
        // relation that makes the cross edge a non-back-edge.
        let func = loopless_cross_edge_function();
        let dom = compute_dominators(&func.body);
        assert_eq!(dom.len(), 4);
        // Entry dominates everything reachable; each block dominates itself.
        assert!(dom[0].contains(&0));
        assert!(dom[1].contains(&1) && dom[1].contains(&0));
        assert!(dom[2].contains(&2) && dom[2].contains(&0));
        // The crux: bb1 must NOT dominate bb2 (bb2 is reachable via bb0 only),
        // which is exactly why bb2 -> bb1 is not a back-edge.
        assert!(!dom[2].contains(&1), "bb1 must not dominate bb2");
    }

    #[test]
    fn test_detect_recursive_calls_factorial() {
        let func = recursive_function();
        let calls = detect_recursive_calls(&func);
        assert_eq!(calls.len(), 1, "factorial has one recursive call");
        assert_eq!(calls[0].block, BlockId(2));
    }

    #[test]
    fn test_detect_recursive_calls_non_recursive() {
        let func = countdown_function();
        let calls = detect_recursive_calls(&func);
        assert!(calls.is_empty(), "countdown is not recursive");
    }

    #[test]
    fn test_modified_int_locals_in_loop() {
        let func = countdown_function();
        let loops = detect_loops(&func.body);
        let modified = modified_int_locals(&func, &loops[0].body_blocks);
        assert!(modified.iter().any(|(_, name)| name == "n"), "n is modified in the loop");
    }

    #[test]
    fn test_raw_countdown_machine_step_is_declined() {
        let func = countdown_function();
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert!(
            vcs.is_empty(),
            "raw fixed-width n = n - 1 must not become mathematical Int: {vcs:?}"
        );
    }

    #[test]
    fn test_check_termination_infinite_loop_produces_vc() {
        let func = infinite_loop_function();
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1, "infinite loop produces 1 termination VC");
        assert!(matches!(
            &vcs[0].kind,
            VcKind::NonTermination { context, measure }
                if context == "loop" && measure == "unknown"
        ));
    }

    #[test]
    fn generated_fallback_measure_cannot_alias_source_parameters() {
        let mut func = infinite_loop_function();
        // These legal source parameters are the exact spellings used by the
        // old fallback.  Their invariant preconditions made the exit-less-loop
        // bad-state formula contradictory and could falsely prove termination.
        func.body.locals.extend([
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("unknown_before".into()) },
            LocalDecl { index: 2, ty: Ty::i32(), name: Some("unknown_after".into()) },
        ]);
        func.body.arg_count = 2;
        func.preconditions = vec![
            Formula::Eq(
                Box::new(Formula::Var("unknown_before".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            Formula::Eq(
                Box::new(Formula::Var("unknown_after".into(), Sort::Int)),
                Box::new(Formula::Int(-1)),
            ),
        ];

        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1);
        let vars = vcs[0].formula.free_variables();
        let before = fallback_loop_measure_symbol("unknown", "before");
        let after = fallback_loop_measure_symbol("unknown", "after");
        assert!(vars.contains("unknown_before") && vars.contains("unknown_after"));
        assert!(vars.contains(&before) && vars.contains(&after));
        assert_ne!(before, "unknown_before");
        assert_ne!(after, "unknown_after");
    }

    #[test]
    fn test_check_termination_recursive_produces_vc() {
        let func = recursive_checked_sub_function();
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1, "checked recursion produces 1 recursion termination VC");
        assert!(matches!(
            &vcs[0].kind,
            VcKind::NonTermination { context, measure }
                if context == "recursion" && measure == "n"
        ));
    }

    #[test]
    fn test_check_termination_with_decreases_clause() {
        let func = recursive_with_decreases();
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1);
        assert!(matches!(
            &vcs[0].kind,
            VcKind::NonTermination { context, measure }
                if context == "recursion" && measure == "n"
        ));
    }

    #[test]
    fn test_generic_direct_self_call_preserves_exact_recursion_identity() {
        let mut func = recursive_with_decreases();
        let Terminator::Call { func: callee, .. } = &mut func.body.blocks[3].terminator else {
            unreachable!();
        };
        // A terminal turbofish is how a direct generic call can appear in the
        // extracted callee path. Generic stripping must retain exact def-path
        // identity, including the trailing `::` left by the shared helper.
        *callee = "test::rec_cs::<u32>".to_string();

        assert!(
            !is_direct_self_call(&func, "rec_cs::<u32>"),
            "a bare terminal name must not alias an unrelated exact def-path"
        );
        assert!(is_direct_self_call(&func, "test::rec_cs::<u32>"));
        assert!(!is_direct_self_call(&func, "other::rec_cs::<u32>"));
        assert_eq!(detect_recursive_calls(&func).len(), 1);

        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1, "generic direct self-call must retain its exact E5 row");
        assert!(matches!(
            &vcs[0].kind,
            VcKind::NonTermination { context, measure }
                if context == "recursion" && measure == "n"
        ));
        assert_ne!(vcs[0].formula, Formula::Bool(false), "a real self-call is not vacuous");
        assert_eq!(
            vcs[0].contract_metadata.and_then(|metadata| metadata.source_contract_index),
            Some(0)
        );
    }

    #[test]
    fn test_check_termination_no_loops_no_recursion() {
        // A simple function with no loops and no recursion should produce no VCs
        let func = VerifiableFunction {
            name: "simple".to_string(),
            def_path: "test::simple".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert!(vcs.is_empty(), "simple function should produce no termination VCs");
    }

    #[test]
    fn test_non_termination_vc_has_no_runtime_fallback() {
        let kind = VcKind::NonTermination { context: "loop".to_string(), measure: "n".to_string() };
        assert!(!kind.has_runtime_fallback(true));
        assert!(!kind.has_runtime_fallback(false));
    }

    #[test]
    fn test_non_termination_vc_description() {
        let kind = VcKind::NonTermination { context: "loop".to_string(), measure: "n".to_string() };
        assert_eq!(kind.description(), "non-termination: loop measure `n` may not decrease");
    }

    #[test]
    fn test_non_termination_formula_structure() {
        let func = loop_checked_sub_function();
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1);

        // A bound loop VC carries the unsigned type invariant beside
        // Or([Ge(after, before), Lt(before, 0)]).
        let Formula::And(core) = &vcs[0].formula else {
            panic!("expected unsigned bound + non-termination disjunction")
        };
        assert!(core.iter().any(|f| is_nonneg_bound_on(f, "n")));
        let clauses = core
            .iter()
            .find_map(|f| match f {
                Formula::Or(clauses) => Some(clauses),
                _ => None,
            })
            .expect("non-termination disjunction");
        assert_eq!(clauses.len(), 2, "non-termination formula is Or of 2 clauses");
        assert!(
            matches!(&clauses[0], Formula::Ge(_, _)),
            "first clause: measure_after >= measure_before"
        );
        assert!(matches!(&clauses[1], Formula::Lt(_, _)), "second clause: measure_before < 0");
    }

    /// A terminating count-up loop whose decreasing measure is a *local*
    /// (not a parameter), so no real measure binds — exactly the shape of
    /// `for i in 0..10` after lowering. The loop has an exit edge.
    /// ```text
    ///   bb0: i = 0; goto bb1
    ///   bb1: cond = i < 10; SwitchInt(cond) -> [1: bb2, otherwise: bb3]
    ///   bb2: i = i + 1; goto bb1   (back-edge: bb1 dominates bb2)
    ///   bb3: return
    /// ```
    fn counting_up_loop_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "count_up".to_string(),
            def_path: "test::count_up".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("i".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: Some("cond".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(1),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(10, 32)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(2)),
                            targets: vec![(1, BlockId(2))],
                            otherwise: BlockId(3),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(1),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(1, 32)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Goto(BlockId(1)), // back-edge
                    },
                    BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// An argument-less recursive function — no integer parameter can serve
    /// as a decreases measure.
    /// ```text
    ///   bb0: call spin_rec() -> bb1
    ///   bb1: return
    /// ```
    fn recursive_no_args_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "spin_rec".to_string(),
            def_path: "test::spin_rec".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            unwind: UnwindEdge::Unreachable,
                            is_unsafe_sig: false,
                            is_foreign: false,
                            func: "test::spin_rec".to_string(),
                            args: vec![],
                            dest: Place::local(0),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_loop_has_exit_true_for_countdown() {
        let func = countdown_function();
        let loops = detect_loops(&func.body);
        assert_eq!(loops.len(), 1);
        assert!(
            loop_has_exit(&func.body, &loops[0]),
            "countdown's loop exits via the SwitchInt otherwise edge"
        );
    }

    #[test]
    fn test_loop_has_exit_false_for_infinite_loop() {
        let func = infinite_loop_function();
        let loops = detect_loops(&func.body);
        assert_eq!(loops.len(), 1);
        assert!(!loop_has_exit(&func.body, &loops[0]), "`loop {{}}` has no edge leaving the body");
    }

    #[test]
    fn test_terminating_unmeasurable_loop_produces_no_vc() {
        // `for i in 0..10`-shaped loop: the measure is a local temp, not a
        // parameter, so no real binding exists. Previously this emitted a
        // trivially-SAT synthetic VC that always FAILED — a Goal-1 false-fail
        // on terminating code. With an exit edge present and no bindable
        // measure, we must emit no termination obligation at all.
        let func = counting_up_loop_function();
        assert_eq!(detect_loops(&func.body).len(), 1, "fixture must contain one loop");
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert!(
            vcs.is_empty(),
            "terminating loop with an exit but no bindable measure must produce no VC, got {vcs:?}"
        );
    }

    #[test]
    fn test_recursion_without_bindable_measure_produces_no_vc() {
        // No integer parameter to bind as a measure → synthetic fallback
        // would be trivially SAT (spurious FAILED). Emit no obligation.
        let func = recursive_no_args_function();
        assert_eq!(detect_recursive_calls(&func).len(), 1, "fixture must contain one self-call");
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert!(
            vcs.is_empty(),
            "recursion with no bindable measure must produce no VC, got {vcs:?}"
        );
    }

    #[test]
    fn test_extract_decreases_contracts() {
        let func = recursive_with_decreases();
        let clauses = extract_decreases_contracts(&func);
        assert_eq!(clauses.len(), 1);
        assert_eq!(clauses[0].measure, "n");
        assert!(matches!(clauses[0].kind, DecreasesKind::Recursion));
    }

    #[test]
    fn test_decreases_clause_serialization_roundtrip() {
        let clause = DecreasesClause {
            measure: "len - i".to_string(),
            span: SourceSpan::default(),
            kind: DecreasesKind::LoopVariant { header_block: 3 },
        };
        let json = serde_json::to_string(&clause).expect("serialize");
        let round: DecreasesClause = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round.measure, "len - i");
        assert!(matches!(round.kind, DecreasesKind::LoopVariant { header_block: 3 }));
    }

    #[test]
    fn test_raw_machine_loop_step_is_not_bound_as_int() {
        // For a u8 countdown, importing raw `n = n - 1` as mathematical Int
        // would erase the executable 0 -> 255 wrap and could mint a false
        // termination proof.
        let mut func = countdown_function();
        func.body.locals[1].ty = Ty::u8();
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        let loops = detect_loops(&func.body);
        assert_eq!(loops.len(), 1);
        assert!(loop_measure_bindings(&func, &loops[0], "n").is_none());
        assert!(vcs.is_empty(), "raw u8 step must be declined: {vcs:?}");
    }

    #[test]
    fn test_loop_vc_excludes_mutated_measure_entry_precondition() {
        // `n > 10` holds only at function entry, not at every loop iteration.
        // The loop VC must carry only the unsigned type invariant and the
        // non-decrease disjunction, never this stale entry fact.
        let mut func = loop_checked_sub_function();
        let precondition =
            Formula::Gt(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(10)));
        func.preconditions.push(precondition.clone());

        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);

        let Formula::And(clauses) = &vcs[0].formula else {
            panic!("expected unsigned type bound and non-decrease disjunction");
        };
        assert_eq!(clauses.len(), 2);
        assert!(clauses.iter().any(|f| is_nonneg_bound_on(f, "n")));
        assert!(clauses.iter().any(|f| matches!(f, Formula::Or(_))));
        assert!(!clauses.contains(&precondition));
    }

    #[test]
    fn test_raw_machine_arithmetic_recursion_is_not_bound_as_int() {
        // Raw fixed-width `n - 1` is wrapping machine arithmetic, not
        // mathematical subtraction. The inferred lane may decline entirely;
        // it must never import `_3 = n - 1` and mint a termination proof.
        let func = recursive_function();
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert!(vcs.is_empty(), "raw fixed-width arithmetic must be declined: {vcs:?}");
    }

    #[test]
    fn test_recursion_vc_threads_preconditions() {
        // A comparison-only precondition on one globally immutable argument
        // remains an exact entry fact for recursion.
        let mut func = recursive_same_arg_function();
        let precondition =
            Formula::Ge(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(0)));
        func.preconditions.push(precondition.clone());

        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);

        let Formula::And(clauses) = &vcs[0].formula else {
            panic!("expected And when an exact precondition is present");
        };
        assert!(
            clauses.contains(&precondition),
            "precondition must appear as a conjunct of the recursion VC"
        );
    }

    #[test]
    fn test_decreases_kind_equality() {
        assert_eq!(DecreasesKind::Recursion, DecreasesKind::Recursion);
        assert_eq!(
            DecreasesKind::LoopVariant { header_block: 0 },
            DecreasesKind::LoopVariant { header_block: 0 }
        );
        assert_ne!(DecreasesKind::LoopVariant { header_block: 0 }, DecreasesKind::Recursion);
    }

    // --- rung-F u32-bound: unsigned-measure type bound on recursion VCs ---
    // (docs/design/2026-07-10-structural-fold-lane.md §1 last bullet)

    /// Top-level conjuncts of a termination VC formula (the formula itself
    /// when it isn't an `And`).
    fn top_conjuncts(f: &Formula) -> Vec<&Formula> {
        // Flatten NESTED `And`s: the recursive-decrease VC is now wrapped by the
        // call site's dominating path guards (`v2_conjoin_path_guards_for_hardened`),
        // which may itself be an `And`, so the `Or` violation disjunction sits one
        // level deeper than before. Recursively collecting leaves keeps these
        // structural assertions valid without weakening them.
        match f {
            Formula::And(v) => v.iter().flat_map(top_conjuncts).collect(),
            other => vec![other],
        }
    }

    /// Is `f` exactly the non-negativity type bound `Ge(Var(var), Int(0))`?
    fn is_nonneg_bound_on(f: &Formula, var: &str) -> bool {
        matches!(
            f,
            Formula::Ge(lhs, rhs)
                if matches!(lhs.as_ref(), Formula::Var(n, _) if n == var)
                    && matches!(rhs.as_ref(), Formula::Int(0))
        )
    }

    /// i32 variant of same-argument recursion. A signed measure has no type
    /// non-negativity fact, so its VC must not get a fabricated `n >= 0` bound.
    fn recursive_function_i32() -> VerifiableFunction {
        let mut func = recursive_same_arg_function();
        func.name = "spin_same_i".to_string();
        func.def_path = "test::spin_same_i".to_string();
        func.body.locals[1].ty = Ty::i32();
        for block in &mut func.body.blocks {
            if let Terminator::Call { func: callee, .. } = &mut block.terminator {
                *callee = "test::spin_same_i".to_string();
            }
        }
        func
    }

    /// A genuinely NON-decreasing u32 recursion: `fn spin_same(n: u32) {
    /// spin_same(n) }` — the call passes the measure through unchanged.
    /// ```text
    ///   bb0: call spin_same(n) -> bb1
    ///   bb1: return
    /// ```
    fn recursive_same_arg_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "spin_same".to_string(),
            def_path: "test::spin_same".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            unwind: UnwindEdge::Unreachable,
                            is_unsafe_sig: false,
                            is_foreign: false,
                            func: "test::spin_same".to_string(),
                            args: vec![Operand::Copy(Place::local(1))],
                            dest: Place::local(0),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// `fn wrap(n: u8) { wrap(<raw machine op>) }`. The arithmetic assignment
    /// and self-call intentionally share the call block, matching release MIR.
    fn raw_u8_recursion(step: Rvalue) -> VerifiableFunction {
        VerifiableFunction {
            name: "wrap".to_string(),
            def_path: "test::wrap".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::u8(), name: Some("n".into()) },
                    LocalDecl { index: 2, ty: Ty::u8(), name: Some("next".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: step,
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Call {
                            unwind: trust_types::UnwindEdge::Unreachable,
                            is_unsafe_sig: false,
                            is_foreign: false,
                            func: "test::wrap".to_string(),
                            args: vec![Operand::Copy(Place::local(2))],
                            dest: Place::local(0),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_raw_u8_arithmetic_recursion_declines_all_unmodeled_ops() {
        let n = || Operand::Copy(Place::local(1));
        let one = || Operand::Constant(ConstValue::Uint(1, 8));
        let mut steps: Vec<Rvalue> =
            [BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Div, BinOp::Rem, BinOp::Shl, BinOp::Shr]
                .into_iter()
                .map(|op| Rvalue::BinaryOp(op, n(), one()))
                .collect();
        steps.push(Rvalue::UnaryOp(UnOp::Neg, n()));
        steps.push(Rvalue::UnaryOp(UnOp::Not, n()));

        for step in steps {
            let func = raw_u8_recursion(step.clone());
            let mut vcs = Vec::new();
            check_termination(&func, &mut vcs);
            assert!(
                vcs.is_empty(),
                "raw fixed-width {step:?} must not become an Int termination proof: {vcs:?}"
            );
        }
    }

    #[test]
    fn test_raw_u8_arithmetic_loop_declines_all_unmodeled_ops() {
        let n = || Operand::Copy(Place::local(1));
        let one = || Operand::Constant(ConstValue::Uint(1, 8));
        let mut steps: Vec<Rvalue> =
            [BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Div, BinOp::Rem, BinOp::Shl, BinOp::Shr]
                .into_iter()
                .map(|op| Rvalue::BinaryOp(op, n(), one()))
                .collect();
        steps.push(Rvalue::UnaryOp(UnOp::Neg, n()));
        steps.push(Rvalue::UnaryOp(UnOp::Not, n()));

        for step in steps {
            let mut func = countdown_function();
            func.body.locals[1].ty = Ty::u8();
            let Statement::Assign { rvalue, .. } = &mut func.body.blocks[1].stmts[0] else {
                panic!("countdown step is an assignment")
            };
            *rvalue = step.clone();
            let loops = detect_loops(&func.body);
            assert_eq!(loops.len(), 1);
            assert!(
                loop_measure_bindings(&func, &loops[0], "n").is_none(),
                "raw fixed-width {step:?} must not bind as mathematical Int"
            );
            let mut vcs = Vec::new();
            check_termination(&func, &mut vcs);
            assert!(
                vcs.is_empty(),
                "raw fixed-width {step:?} must not become an Int termination proof: {vcs:?}"
            );
        }
    }

    #[test]
    fn test_unsafe_direct_recursion_operands_are_rejected() {
        let unsafe_args = vec![
            Operand::Symbolic(Formula::Sub(
                Box::new(Formula::Var("n".into(), Sort::Int)),
                Box::new(Formula::Int(1)),
            )),
            Operand::Constant(ConstValue::OpaqueScalar { width: 32, signed: false }),
            Operand::Unsupported { kind: "test".into(), detail: "opaque operand".into() },
            Operand::Copy(Place { local: 1, projections: vec![Projection::Field(0)] }),
        ];
        for arg in unsafe_args {
            let mut func = recursive_same_arg_function();
            let Terminator::Call { args, .. } = &mut func.body.blocks[0].terminator else {
                unreachable!()
            };
            args[0] = arg.clone();
            let mut vcs = Vec::new();
            check_termination(&func, &mut vcs);
            assert!(vcs.is_empty(), "unsafe recursion operand must be declined: {arg:?}");
        }
    }

    #[test]
    fn test_recursion_drops_arithmetic_and_mutable_preconditions() {
        let n = Formula::Var("n".into(), Sort::Int);
        let arithmetic = Formula::Lt(
            Box::new(Formula::Add(Box::new(n.clone()), Box::new(Formula::Int(1)))),
            Box::new(n.clone()),
        );
        let mut func = recursive_same_arg_function();
        func.preconditions.push(arithmetic.clone());
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1);
        assert!(!top_conjuncts(&vcs[0].formula).contains(&&arithmetic));

        let mutable = Formula::Eq(Box::new(n), Box::new(Formula::Int(0)));
        func.preconditions = vec![mutable.clone()];
        func.body.blocks[1].stmts.push(Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 32))),
            span: SourceSpan::default(),
        });
        vcs.clear();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1);
        assert!(!top_conjuncts(&vcs[0].formula).contains(&&mutable));
    }

    #[test]
    fn test_explicit_unbindable_decreases_is_one_visible_unknown() {
        let mut func = recursive_same_arg_function();
        func.contracts.push(Contract {
            kind: ContractKind::Decreases,
            span: SourceSpan::default(),
            body: "n - 1".to_string(),
        });
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1);
        assert!(matches!(
            &vcs[0].kind,
            VcKind::UnsupportedMir { kind, .. }
                if kind == RECURSION_DECREASES_UNSUPPORTED_KIND
        ));
        assert_eq!(vcs[0].formula, Formula::Bool(true));
    }

    fn authored_n_contract_span() -> SourceSpan {
        SourceSpan {
            file: "topology.rs".to_string(),
            line_start: 7,
            col_start: 5,
            line_end: 7,
            col_end: 16,
        }
    }

    fn assert_single_authored_topology_unknown(vcs: &[VerificationCondition]) {
        assert_eq!(vcs.len(), 1, "topology uncertainty must emit exactly one marker: {vcs:?}");
        assert!(matches!(
            &vcs[0].kind,
            VcKind::UnsupportedMir { kind, detail }
                if kind == RECURSION_DECREASES_UNSUPPORTED_KIND
                    && detail.contains("function-level decreases cannot classify")
        ));
        assert_eq!(
            vcs[0].formula,
            Formula::Bool(true),
            "the topology marker must stay satisfiable/Unknown, never false-Proved"
        );
        assert_eq!(vcs[0].location.file, "topology.rs");
        assert_eq!(vcs[0].location.line_start, 7, "retain the authored E5 source marker");
        assert!(
            vcs.iter().all(|vc| !matches!(vc.kind, VcKind::NonTermination { .. })),
            "uncertain topology must not leave vacuous or partial direct-self rows"
        );
    }

    #[test]
    fn authored_recursion_vacuity_has_an_explicit_known_benign_terminator_set() {
        let self_call = recursive_same_arg_function().body.blocks[0].terminator.clone();
        let known_benign = [
            self_call,
            Terminator::Goto(BlockId(0)),
            Terminator::SwitchInt {
                discr: Operand::Constant(ConstValue::Bool(true)),
                targets: vec![(1, BlockId(0))],
                otherwise: BlockId(0),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
            Terminator::Return,
            Terminator::Assert {
                unwind: trust_types::UnwindEdge::Unreachable,
                cond: Operand::Constant(ConstValue::Bool(true)),
                expected: true,
                msg: AssertMessage::Custom("known benign control edge".to_string()),
                target: BlockId(0),
                span: SourceSpan::default(),
            },
            Terminator::Unreachable,
            Terminator::Resume,
        ];

        for terminator in known_benign {
            let mut func = recursive_same_arg_function();
            func.body.blocks[0].terminator = terminator;
            assert!(
                authored_recursion_identity_uncertainty(&func).is_none(),
                "known benign terminator was unexpectedly treated as recursion-identity \
                 uncertainty"
            );
        }
    }

    #[test]
    fn test_nonself_call_blocks_vacuous_authored_recursion_decreases() {
        let mut func = recursive_same_arg_function();
        let Terminator::Call { func: callee, .. } = &mut func.body.blocks[0].terminator else {
            unreachable!();
        };
        // This can be the f -> g half of mutual recursion. The direct-self
        // lane cannot certify that it is non-recursive merely because `g`
        // differs from f's exact identity.
        *callee = "test::g::<u32>".to_string();
        func.contracts.push(Contract {
            kind: ContractKind::Decreases,
            span: authored_n_contract_span(),
            body: "n".to_string(),
        });

        assert!(detect_recursive_calls(&func).is_empty());
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_single_authored_topology_unknown(&vcs);
    }

    #[test]
    fn test_mixed_self_and_nonself_calls_do_not_emit_partial_decreases_rows() {
        let mut func = recursive_with_decreases();
        func.contracts[0].span = authored_n_contract_span();
        // Make the existing direct self-call flow into a second, non-self
        // call. Recognizing the first edge must not produce a partial proof.
        func.body.blocks[4].terminator = Terminator::Call {
            unwind: trust_types::UnwindEdge::Unreachable,
            is_unsafe_sig: false,
            is_foreign: false,
            func: "test::helper".to_string(),
            args: vec![Operand::Copy(Place::local(1))],
            dest: Place::local(0),
            target: Some(BlockId(5)),
            span: SourceSpan::default(),
            atomic: None,
        };
        func.body.blocks.push(BasicBlock {
            id: BlockId(5),
            stmts: vec![],
            terminator: Terminator::Return,
        });

        assert_eq!(detect_recursive_calls(&func).len(), 1, "fixture retains one direct self-call");
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_single_authored_topology_unknown(&vcs);
    }

    #[test]
    fn test_drop_and_opaque_block_vacuous_authored_recursion_decreases() {
        let uncertain = [
            Terminator::Drop {
                unwind: trust_types::UnwindEdge::Unreachable,
                place: Place::local(1),
                target: BlockId(1),
                span: SourceSpan::default(),
            },
            Terminator::Opaque {
                kind: "synthetic-control".to_string(),
                targets: vec![BlockId(1)],
                span: SourceSpan::default(),
            },
        ];

        for terminator in uncertain {
            let mut func = recursive_same_arg_function();
            func.body.blocks[0].terminator = terminator;
            func.contracts.push(Contract {
                kind: ContractKind::Decreases,
                span: authored_n_contract_span(),
                body: "n".to_string(),
            });

            let mut vcs = Vec::new();
            check_termination(&func, &mut vcs);
            assert_single_authored_topology_unknown(&vcs);
        }
    }

    #[test]
    fn test_uncertain_recursion_topology_retains_independent_loop_vc() {
        let mut func = recursive_same_arg_function();
        func.body.blocks = vec![
            BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Goto(BlockId(0)) },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: trust_types::UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "test::helper".to_string(),
                    args: vec![],
                    dest: Place::local(0),
                    target: Some(BlockId(2)),
                    span: SourceSpan::default(),
                    atomic: None,
                },
            },
            BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
        ];
        func.contracts.push(Contract {
            kind: ContractKind::Decreases,
            span: authored_n_contract_span(),
            body: "n".to_string(),
        });

        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 2, "one topology marker plus one independent loop VC");
        assert!(vcs.iter().any(|vc| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == RECURSION_DECREASES_UNSUPPORTED_KIND)
                && vc.formula == Formula::Bool(true)
        }));
        assert!(vcs.iter().any(|vc| {
            matches!(&vc.kind, VcKind::NonTermination { context, .. } if context == "loop")
        }));
        assert!(vcs.iter().all(|vc| {
            !matches!(&vc.kind, VcKind::NonTermination { context, .. } if context == "recursion")
        }));
    }

    #[test]
    fn test_colliding_recursion_measure_name_fails_closed() {
        let mut func = recursive_same_arg_function();
        func.body.locals.push(LocalDecl { index: 2, ty: Ty::u32(), name: Some("n".to_string()) });
        func.contracts.push(Contract {
            kind: ContractKind::Decreases,
            span: SourceSpan::default(),
            body: "n".to_string(),
        });

        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1);
        assert!(matches!(
            &vcs[0].kind,
            VcKind::UnsupportedMir { kind, .. }
                if kind == RECURSION_DECREASES_UNSUPPORTED_KIND
        ));
    }

    #[test]
    fn test_fallback_shaped_recursion_measure_name_fails_closed() {
        let mut func = recursive_same_arg_function();
        func.body.locals[1].name = Some("_2".to_string());
        // `_2` is the collision-safe fallback vocabulary of the next real local.
        func.body.locals.push(LocalDecl { index: 2, ty: Ty::u32(), name: None });
        func.contracts.push(Contract {
            kind: ContractKind::Decreases,
            span: SourceSpan::default(),
            body: "_2".to_string(),
        });

        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1);
        assert!(matches!(
            &vcs[0].kind,
            VcKind::UnsupportedMir { kind, .. }
                if kind == RECURSION_DECREASES_UNSUPPORTED_KIND
        ));
    }

    #[test]
    fn test_nonrecursive_unbindable_decreases_is_still_visible() {
        let mut func = recursive_same_arg_function();
        func.body.blocks[0].terminator = Terminator::Return;
        func.contracts.push(Contract {
            kind: ContractKind::Decreases,
            span: SourceSpan::default(),
            body: "n - 1".to_string(),
        });
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1);
        assert!(matches!(vcs[0].kind, VcKind::UnsupportedMir { .. }));
        assert_eq!(vcs[0].formula, Formula::Bool(true));
    }

    #[test]
    fn test_nonrecursive_exact_decreases_is_visible_and_vacuously_closed() {
        let mut func = recursive_same_arg_function();
        func.body.blocks[0].terminator = Terminator::Return;
        func.contracts.push(Contract {
            kind: ContractKind::Decreases,
            span: SourceSpan::default(),
            body: "n".to_string(),
        });
        assert!(
            authored_recursion_identity_uncertainty(&func).is_none(),
            "a call-free body with no Drop/Opaque edge is the exact vacuity fragment"
        );
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1);
        assert!(matches!(
            &vcs[0].kind,
            VcKind::NonTermination { context, measure }
                if context == "recursion" && measure == "n"
        ));
        assert_eq!(vcs[0].formula, Formula::Bool(false));
    }

    #[test]
    fn test_nonrecursive_exact_decreases_stays_visible_alongside_loop_obligations() {
        let mut func = recursive_same_arg_function();
        func.body.blocks.truncate(1);
        func.body.blocks[0].stmts.clear();
        func.body.blocks[0].terminator = Terminator::Goto(BlockId(0));
        func.contracts.push(Contract {
            kind: ContractKind::Decreases,
            span: SourceSpan::default(),
            body: "n".to_string(),
        });

        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);

        let authored = vcs
            .iter()
            .filter(|vc| {
                matches!(
                    &vc.kind,
                    VcKind::NonTermination { context, measure }
                        if context == "recursion" && measure == "n"
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(authored.len(), 1, "the function-level clause must remain one exact row");
        assert_eq!(authored[0].formula, Formula::Bool(false));
        assert_eq!(
            authored[0].contract_metadata.and_then(|metadata| metadata.source_contract_index),
            Some(0),
            "the vacuous row must retain exact authored-clause identity"
        );
        assert!(
            vcs.iter().any(|vc| {
                matches!(&vc.kind, VcKind::NonTermination { context, .. } if context == "loop")
            }),
            "accounting for the authored recursion clause must not skip independent loop analysis"
        );
    }

    #[test]
    fn test_u32_recursion_vc_conjoins_measure_type_bound() {
        // Every exact unsigned recursion VC carries the type tautology n >= 0.
        let func = recursive_same_arg_function();
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1);
        let conjuncts = top_conjuncts(&vcs[0].formula);
        assert!(
            conjuncts.iter().any(|c| is_nonneg_bound_on(c, "n")),
            "u32 measure VC must conjoin the type bound n >= 0; got {:?}",
            vcs[0].formula
        );
        // The non-decreasing disjunction itself is untouched (last conjunct).
        assert!(matches!(conjuncts.last(), Some(Formula::Or(_))));
    }

    #[test]
    fn test_i32_recursion_vc_has_no_false_nonneg_bound() {
        // Signed-measure control: fabricating `n >= 0` would hide the negative
        // portion of the actual machine domain. The bound must be unsigned-only.
        let func = recursive_function_i32();
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1, "i32 same-arg recursion still gets its VC");
        let conjuncts = top_conjuncts(&vcs[0].formula);
        assert!(
            !conjuncts.iter().any(|c| is_nonneg_bound_on(c, "n")),
            "signed measure must NOT get a fabricated n >= 0 bound: {:?}",
            vcs[0].formula
        );
    }

    #[test]
    fn test_non_decreasing_u32_recursion_vc_stays_sat() {
        // `fn spin_same(n: u32) { spin_same(n) }` — genuinely
        // non-terminating recursion. The unsigned type bound must never
        // mask the real witness: the `measure_call >= measure_entry`
        // disjunct is `n >= n` (true at every n >= 0), so the VC stays SAT
        // (undischargeable) with or without the bound. Pin the disjunct's
        // survival with identical `Var(n)` sides.
        let func = recursive_same_arg_function();
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1, "same-arg recursion still gets its VC");
        let conjuncts = top_conjuncts(&vcs[0].formula);
        let or = conjuncts
            .iter()
            .find_map(|c| match c {
                Formula::Or(v) => Some(v),
                _ => None,
            })
            .expect("non-termination disjunction must be present");
        let Formula::Ge(call, entry) = &or[0] else {
            panic!("first disjunct must be Ge(measure_call, measure_entry), got {:?}", or[0]);
        };
        assert_eq!(call, entry, "same-arg recursion: call measure == entry measure");
        assert!(
            matches!(
                (call.as_ref(), entry.as_ref()),
                (Formula::Var(a, _), Formula::Var(b, _)) if a == "n" && b == "n"
            ),
            "both sides must be the parameter Var(n)"
        );
    }

    // --- rung-F checked-chain: resolve the measure arg through the
    // overflow-checked op in the UNIQUE Assert-predecessor block ---
    //
    // The real `infer_implicit_n` MIR (debug/checked build) splits the
    // decrement across two blocks:
    //   bbP: _3 = CheckedSub(n, 1); Assert(!_3.1, Overflow(Sub)) -> bbC
    //   bbC: _4 = move (_3.0);      call self(_4)
    // The call-block-only def extraction leaves `_3.0` FREE, so the VC is
    // SAT at e.g. `_4 = n + 7` regardless of any type bound — measured on
    // the census dump 2026-07-11 (see the trust-clean regression test).

    /// `fn rec_cs(n: u32) { if n != 0 { rec_cs(n - 1) } }` with the
    /// overflow-checked two-block decrement shape above.
    fn recursive_checked_sub_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "rec_cs".to_string(),
            def_path: "test::rec_cs".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: None }, // n == 0
                    LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None }, // CheckedSub(n, 1)
                    LocalDecl { index: 4, ty: Ty::u32(), name: None }, // _3.0
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Eq,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(0, 32)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(2)),
                            targets: vec![(1, BlockId(1))],
                            otherwise: BlockId(2),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                    // bbP: checked decrement + overflow assert
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Sub,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(1, 32)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Move(Place {
                                local: 3,
                                projections: vec![Projection::Field(1)],
                            }),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Sub),
                            target: BlockId(3),
                            span: SourceSpan::default(),
                        },
                    },
                    // bbC: unpack .0 and recurse
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Move(Place {
                                local: 3,
                                projections: vec![Projection::Field(0)],
                            })),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Call {
                            unwind: UnwindEdge::Unreachable,
                            is_unsafe_sig: false,
                            is_foreign: false,
                            func: "test::rec_cs".to_string(),
                            args: vec![Operand::Move(Place::local(4))],
                            dest: Place::local(0),
                            target: Some(BlockId(4)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Optimized form of [`recursive_checked_sub_function`]: the unpack local
    /// is eliminated and the recursive call consumes `_3.0` directly.
    fn recursive_checked_sub_direct_projection_function() -> VerifiableFunction {
        let mut func = recursive_checked_sub_function();
        func.body.blocks[3].stmts.clear();
        let checked_span = SourceSpan {
            file: "recursive_checked.rs".to_string(),
            line_start: 19,
            col_start: 20,
            line_end: 19,
            col_end: 25,
        };
        let Terminator::Assert { span, .. } = &mut func.body.blocks[2].terminator else {
            unreachable!();
        };
        *span = checked_span;
        let Terminator::Call { args, .. } = &mut func.body.blocks[3].terminator else {
            unreachable!();
        };
        args[0] = Operand::Move(Place { local: 3, projections: vec![Projection::Field(0)] });
        func
    }

    /// Same shape, but the call block has TWO predecessors (a `goto` from a
    /// second branch joins it), so the Assert-success facts are NOT valid on
    /// every path into the call — the resolver must decline (fail-closed).
    fn recursive_checked_sub_two_preds_function() -> VerifiableFunction {
        let mut func = recursive_checked_sub_function();
        // Redirect bb1 (formerly `return`) to jump straight into the call
        // block bb3, creating a second in-edge that bypasses the Assert.
        func.body.blocks[1].terminator = Terminator::Goto(BlockId(3));
        func
    }

    /// Same shape, but the measure/operand local `n` is REASSIGNED after the
    /// call — its VC var no longer denotes a single value across the body, so
    /// the resolver must decline (fail-closed).
    fn recursive_checked_sub_mutated_operand_function() -> VerifiableFunction {
        let mut func = recursive_checked_sub_function();
        func.body.blocks[4].stmts.push(Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 32))),
            span: SourceSpan::default(),
        });
        func
    }

    /// A malicious/malformed CFG with an Assert predecessor targeting ENTRY.
    /// Entry still executes directly at function start, so that edge cannot
    /// establish the checked-success fact for the first call.
    fn recursive_checked_sub_entry_call_function() -> VerifiableFunction {
        let mut func = recursive_checked_sub_function();
        let call = func.body.blocks[3].clone();
        let pred = func.body.blocks[2].clone();
        func.body.blocks = vec![
            BasicBlock { id: BlockId(0), stmts: call.stmts, terminator: call.terminator },
            BasicBlock {
                id: BlockId(1),
                stmts: pred.stmts,
                terminator: match pred.terminator {
                    Terminator::Assert { cond, expected, msg, span, .. } => {
                        Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable, cond, expected, msg, target: BlockId(0), span }
                    }
                    _ => unreachable!(),
                },
            },
            BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
        ];
        if let Terminator::Call { target, .. } = &mut func.body.blocks[0].terminator {
            *target = Some(BlockId(2));
        }
        func
    }

    /// The Ge disjunct of the (single) recursion VC of `func`.
    fn recursion_ge_disjunct(func: &VerifiableFunction) -> (Formula, Formula) {
        let mut vcs = Vec::new();
        check_termination(func, &mut vcs);
        assert_eq!(vcs.len(), 1, "fixture must yield exactly one termination VC");
        // Search the WHOLE formula tree for the non-termination disjunction
        // `Or([Ge(call, entry), Lt(entry, 0)])`. Dominating path guards now
        // wrap the VC (possibly several `And` levels), so a top-level scan no
        // longer finds it; recurse through `And`/`Or` and select the `Or`
        // whose FIRST disjunct is the `Ge` measure comparison.
        fn find_ge_or(f: &Formula) -> Option<&Vec<Formula>> {
            match f {
                Formula::Or(v) if matches!(v.first(), Some(Formula::Ge(..))) => Some(v),
                Formula::And(v) | Formula::Or(v) => v.iter().find_map(find_ge_or),
                _ => None,
            }
        }
        let or = find_ge_or(&vcs[0].formula)
            .expect("non-termination Ge-disjunction must be present");
        let Formula::Ge(call, entry) = &or[0] else {
            unreachable!("selected Or has a Ge first disjunct by construction");
        };
        ((**call).clone(), (**entry).clone())
    }

    #[test]
    fn test_checked_sub_recursion_call_arg_resolves_through_assert_pred() {
        // The measure argument `_4 = _3.0` where `_3 = CheckedSub(n, 1)` in
        // the unique Assert-predecessor must resolve to `Sub(n, 1)` — on the
        // Assert's success edge no overflow occurred, so the machine value
        // IS the mathematical `n - 1`. Without the resolution the disjunct
        // is `Ge(_4, n)` with `_4` free — SAT no matter what type bound is
        // conjoined (the real infer_implicit_n blocker).
        let func = recursive_checked_sub_function();
        let (call, entry) = recursion_ge_disjunct(&func);
        assert!(
            matches!(entry, Formula::Var(ref nm, _) if nm == "n"),
            "entry side must stay Var(n), got {entry:?}"
        );
        match &call {
            Formula::Sub(lhs, rhs) => {
                assert!(matches!(lhs.as_ref(), Formula::Var(nm, _) if nm == "n"));
                assert!(matches!(rhs.as_ref(), Formula::Int(1)));
            }
            other => panic!("call side must resolve to Sub(n, 1), got {other:?}"),
        }
    }

    #[test]
    fn test_checked_sub_direct_projection_resolves_through_assert_pred() {
        let func = recursive_checked_sub_direct_projection_function();
        let (call, entry) = recursion_ge_disjunct(&func);
        assert!(matches!(entry, Formula::Var(ref name, _) if name == "n"));
        assert!(matches!(
            call,
            Formula::Sub(lhs, rhs)
                if matches!(lhs.as_ref(), Formula::Var(name, _) if name == "n")
                    && matches!(rhs.as_ref(), Formula::Int(1))
        ));
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1);
        assert_eq!(vcs[0].location.file, "recursive_checked.rs");
        assert_eq!(vcs[0].location.line_start, 19);
    }

    #[test]
    fn test_checked_sub_two_preds_declines_resolution() {
        // A second in-edge into the call block bypasses the Assert — the
        // success-edge fact does not hold on that path. Fail-closed: the
        // call arg must stay the unresolved temp (VC stays SAT, no
        // false-prove).
        let func = recursive_checked_sub_two_preds_function();
        let (call, _) = recursion_ge_disjunct(&func);
        assert!(
            matches!(call, Formula::Var(ref nm, _) if nm == "_4"),
            "two-pred call block must NOT resolve through the Assert, got {call:?}"
        );
    }

    #[test]
    fn test_checked_sub_mutated_operand_declines_resolution() {
        // `n` is reassigned in the body: the entry var and the operand read
        // no longer denote one value, so substituting `Sub(n, 1)` could
        // equivocate. Fail-closed decline.
        let func = recursive_checked_sub_mutated_operand_function();
        let (call, _) = recursion_ge_disjunct(&func);
        assert!(
            matches!(call, Formula::Var(ref nm, _) if nm == "_4"),
            "mutated operand must NOT resolve through the Assert, got {call:?}"
        );
    }

    #[test]
    fn test_checked_sub_assert_predecessor_cannot_justify_entry() {
        let func = recursive_checked_sub_entry_call_function();
        let (call, _) = recursion_ge_disjunct(&func);
        assert!(
            matches!(call, Formula::Var(ref name, _) if name == "_4"),
            "entry must not resolve through an explicit Assert predecessor: {call:?}"
        );
    }

    // --- rung-F loop-lane checked-chain port: the same two-block debug-build
    // decrement as a LOOP step (the trust-clean named gap
    // `u32_checked_sub_loop_emits_no_nontermination_vc_yet`, now closed) ---

    /// `fn countdown_cs(n: u32) { while n > 0 { n -= 1 } }` in the
    /// debug/checked shape — the decrement is an overflow-checked op in the
    /// step block's unique Assert-predecessor:
    /// ```text
    ///   bb0 (header): cond = n > 0; SwitchInt(cond) -> [1: bb1, otherwise: bb3]
    ///   bb1: _3 = CheckedSub(n, 1); Assert(!_3.1, Overflow(Sub)) -> bb2
    ///   bb2: n = move (_3.0); goto bb0   (back-edge)
    ///   bb3: return
    /// ```
    fn loop_checked_sub_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "countdown_cs".to_string(),
            def_path: "test::countdown_cs".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: Some("cond".into()) },
                    LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Gt,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(0, 32)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(2)),
                            targets: vec![(1, BlockId(1))],
                            otherwise: BlockId(3),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Sub,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(1, 32)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            unwind: trust_types::UnwindEdge::Unreachable,
                            cond: Operand::Move(Place {
                                local: 3,
                                projections: vec![Projection::Field(1)],
                            }),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Sub),
                            target: BlockId(2),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(1),
                            rvalue: Rvalue::Use(Operand::Move(Place {
                                local: 3,
                                projections: vec![Projection::Field(0)],
                            })),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Goto(BlockId(0)), // back-edge
                    },
                    BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Outside-pred control shape: the checked op lives in a PREHEADER,
    /// outside the loop —
    /// ```text
    ///   bb0 (preheader): _3 = CheckedSub(n, 1); Assert(!_3.1) -> bb1
    ///   bb1 (header):    cond = n > 0; SwitchInt -> [1: bb2, otherwise: bb3]
    ///   bb2 (step):      n = move (_3.0); goto bb1   (back-edge)
    ///   bb3: return
    /// ```
    /// The checked op runs ONCE: every iteration re-assigns the SAME value
    /// `n0 - 1`, so for `n0 >= 2` this loop genuinely NEVER terminates.
    fn loop_checked_sub_preheader_function() -> VerifiableFunction {
        let mut func = loop_checked_sub_function();
        func.name = "countdown_cs_preheader".to_string();
        func.def_path = "test::countdown_cs_preheader".to_string();
        let [b0, b1, b2, b3] = &mut func.body.blocks[..] else {
            panic!("checked fixture has 4 blocks");
        };
        // Move the checked-op block to the front (preheader) and rewire:
        // preheader -> header -> {step, exit}; step -> header (back-edge).
        std::mem::swap(b0, b1);
        b0.id = BlockId(0);
        b1.id = BlockId(1);
        let Terminator::Assert { target, .. } = &mut b0.terminator else {
            panic!("preheader ends in the overflow Assert");
        };
        *target = BlockId(1);
        let Terminator::SwitchInt { targets, otherwise, .. } = &mut b1.terminator else {
            panic!("header ends in a SwitchInt");
        };
        *targets = vec![(1, BlockId(2))];
        *otherwise = BlockId(3);
        b2.terminator = Terminator::Goto(BlockId(1)); // back-edge to header
        let _ = b3;
        func
    }

    /// Step-in-entry-block shape: the unpack `n = _3.0` lives in bb0. On the
    /// FIRST execution control materializes at bb0 without traversing any
    /// CFG edge, so a "unique Assert-predecessor" cannot cover it (and the
    /// checked op has not even run yet).
    /// ```text
    ///   bb0 (entry+header): n = move (_3.0); cond = n > 0;
    ///                       SwitchInt -> [1: bb1, otherwise: bb2]
    ///   bb1: _3 = CheckedSub(n, 1); Assert(!_3.1) -> bb0   (back-edge)
    ///   bb2: return
    /// ```
    fn loop_checked_sub_step_in_entry_function() -> VerifiableFunction {
        let mut func = loop_checked_sub_function();
        func.name = "countdown_cs_entry_step".to_string();
        func.def_path = "test::countdown_cs_entry_step".to_string();
        let unpack = func.body.blocks[2].stmts.remove(0);
        func.body.blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    unpack,
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Gt,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(0, 32)),
                        ),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    targets: vec![(1, BlockId(1))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Sub,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Uint(1, 32)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Assert {
                    unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Move(Place {
                        local: 3,
                        projections: vec![Projection::Field(1)],
                    }),
                    expected: false,
                    msg: AssertMessage::Overflow(BinOp::Sub),
                    target: BlockId(0), // back-edge
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
        ];
        func
    }

    #[test]
    fn test_checked_sub_loop_step_resolves_through_assert_pred() {
        // The step `n = _3.0` where `_3 = CheckedSub(n, 1)` in the unique
        // in-loop Assert-predecessor must bind with measure_after =
        // Sub(n, 1) — on the success edge the machine value IS the
        // mathematical n - 1. Before the port this shape did not bind at
        // all (the trust-clean named gap).
        let func = loop_checked_sub_function();
        let loops = detect_loops(&func.body);
        assert_eq!(loops.len(), 1);
        let (before, after) = loop_measure_bindings(&func, &loops[0], "n")
            .expect("checked-sub loop step must bind through the Assert-pred chain");
        assert!(matches!(before, Formula::Var(ref nm, _) if nm == "n"));
        match &after {
            Formula::Sub(lhs, rhs) => {
                assert!(matches!(lhs.as_ref(), Formula::Var(nm, _) if nm == "n"));
                assert!(matches!(rhs.as_ref(), Formula::Int(1)));
            }
            other => panic!("step must resolve to Sub(n, 1), got {other:?}"),
        }
    }

    #[test]
    fn test_checked_sub_loop_emits_bound_nontermination_vc() {
        // Full lane: the VC carries the unsigned type bound beside the
        // resolved disjunction — And([n >= 0, Or([n - 1 >= n, n < 0])]) —
        // the exact shape of the release-form countdown twin.
        let func = loop_checked_sub_function();
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1, "checked-sub countdown loop yields exactly one VC");
        assert!(matches!(
            &vcs[0].kind,
            VcKind::NonTermination { context, measure }
                if context == "loop" && measure == "n"
        ));
        let conjuncts = top_conjuncts(&vcs[0].formula);
        assert!(
            conjuncts.iter().any(|c| is_nonneg_bound_on(c, "n")),
            "u32 loop measure VC must conjoin the type bound n >= 0; got {:?}",
            vcs[0].formula
        );
        let or = conjuncts
            .iter()
            .find_map(|c| match c {
                Formula::Or(v) => Some(v),
                _ => None,
            })
            .expect("non-termination disjunction must be present");
        let Formula::Ge(after, before) = &or[0] else {
            panic!("first disjunct must be Ge(measure_after, measure_before), got {:?}", or[0]);
        };
        assert!(matches!(after.as_ref(), Formula::Sub(_, _)), "after must be Sub(n, 1)");
        assert!(matches!(before.as_ref(), Formula::Var(nm, _) if nm == "n"));
    }

    #[test]
    fn test_checked_sub_loop_two_preds_declines() {
        // A second in-edge into the step block bypasses the overflow Assert
        // — the success-edge fact is not valid on every entry. Fail-closed:
        // no binding, and (exit-ful loop) no obligation at all.
        let mut func = loop_checked_sub_function();
        let Terminator::SwitchInt { targets, .. } = &mut func.body.blocks[0].terminator else {
            panic!("header must be a SwitchInt");
        };
        targets.push((2, BlockId(2))); // second in-edge into the step block
        let loops = detect_loops(&func.body);
        assert_eq!(loops.len(), 1);
        assert!(
            loop_measure_bindings(&func, &loops[0], "n").is_none(),
            "two-pred step block must NOT resolve through the Assert"
        );
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert!(vcs.is_empty(), "two-pred step block must yield no VC, got {vcs:?}");
    }

    #[test]
    fn test_checked_sub_loop_preheader_assert_declines() {
        // The checked op lives OUTSIDE the loop (preheader): the step
        // re-assigns the SAME `n0 - 1` every iteration — a loop-INVARIANT
        // step; for n0 >= 2 this loop genuinely never terminates. The step
        // block's unique pred is the header SwitchInt, not an in-loop
        // Assert: no binding, no VC. Resolving `n - 1` here would fabricate
        // a fresh decrease per iteration — a false termination proof.
        let func = loop_checked_sub_preheader_function();
        let loops = detect_loops(&func.body);
        assert_eq!(loops.len(), 1);
        assert_eq!(loops[0].header, BlockId(1));
        assert!(
            !loops[0].body_blocks.contains(&BlockId(0)),
            "the preheader must not be part of the natural loop; got {:?}",
            loops[0].body_blocks
        );
        assert!(loop_measure_bindings(&func, &loops[0], "n").is_none());
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert!(vcs.is_empty(), "loop-invariant checked step must yield no VC, got {vcs:?}");
    }

    #[test]
    fn test_checked_sub_loop_assert_pred_outside_body_blocks_declines() {
        // Direct probe of the Assert-pred-INSIDE-body guard. For a natural
        // loop, `natural_loop_blocks` includes every predecessor of a
        // non-header body block by construction, so `check_termination`
        // cannot reach this state today; the guard is defense-in-depth
        // against future body-set changes (e.g. a capped walk). Hand the
        // binder a LoopInfo whose body excludes the Assert block: even
        // though the CFG-level chain is intact, resolution must DECLINE.
        let func = loop_checked_sub_function();
        let crafted = LoopInfo {
            header: BlockId(0),
            _latch: BlockId(2),
            body_blocks: vec![BlockId(0), BlockId(2)],
        };
        assert!(
            loop_measure_bindings(&func, &crafted, "n").is_none(),
            "an Assert-pred outside body_blocks must not resolve"
        );
    }

    #[test]
    fn test_checked_sub_loop_step_in_entry_block_declines() {
        // Control can materialize at the entry block without traversing any
        // CFG edge (and before the checked op has ever run), so the unique
        // explicit predecessor does not cover the first step execution.
        let func = loop_checked_sub_step_in_entry_function();
        let loops = detect_loops(&func.body);
        assert_eq!(loops.len(), 1);
        assert!(
            loop_measure_bindings(&func, &loops[0], "n").is_none(),
            "an entry-block step must NOT resolve through the Assert"
        );
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert!(vcs.is_empty(), "entry-block step must yield no VC, got {vcs:?}");
    }

    #[test]
    fn test_checked_sub_loop_mutated_nonmeasure_operand_declines() {
        // CheckedSub(n, k) where k is written elsewhere in the body: k's VC
        // var does not denote a single value, so substituting `n - k` could
        // equivocate between program points. Fail-closed decline. (The
        // MEASURE operand `n` is the one allowed mutable input — its only
        // in-loop write is the step itself.)
        let mut func = loop_checked_sub_function();
        func.body.locals.push(LocalDecl { index: 4, ty: Ty::u32(), name: Some("k".into()) });
        let Statement::Assign { rvalue, .. } = &mut func.body.blocks[1].stmts[0] else {
            panic!("checked step is an assignment");
        };
        *rvalue = Rvalue::CheckedBinaryOp(
            BinOp::Sub,
            Operand::Copy(Place::local(1)),
            Operand::Copy(Place::local(4)),
        );
        // k is (re)assigned after the loop — any write disqualifies it.
        func.body.blocks[3].stmts.push(Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(2, 32))),
            span: SourceSpan::default(),
        });
        let loops = detect_loops(&func.body);
        assert_eq!(loops.len(), 1);
        assert!(loop_measure_bindings(&func, &loops[0], "n").is_none());
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert!(vcs.is_empty(), "mutated non-measure operand must yield no VC, got {vcs:?}");
    }

    #[test]
    fn test_checked_sub_loop_nonassign_tuple_write_declines() {
        // A `Deinit` of the checked tuple inside the step block is a
        // non-`Assign` write channel interposed on the `_T -> n` value flow.
        let mut func = loop_checked_sub_function();
        func.body.blocks[2].stmts.insert(0, Statement::Deinit { place: Place::local(3) });
        let loops = detect_loops(&func.body);
        assert_eq!(loops.len(), 1);
        assert!(loop_measure_bindings(&func, &loops[0], "n").is_none());
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert!(vcs.is_empty(), "non-Assign tuple write must yield no VC, got {vcs:?}");
    }

    #[test]
    fn test_checked_sub_loop_signed_measure_unchanged_no_vc() {
        // SIGNED control (contract unchanged by the port): an i32 measure
        // does not bind (`loop_measure_bindings` declines signed measures
        // outright — a function-entry fact is not a signed loop lower-bound
        // invariant), and an exit-ful loop with no bindable measure yields
        // NO obligation. The checked-chain port must not alter this.
        let mut func = loop_checked_sub_function();
        func.body.locals[1].ty = Ty::i32();
        func.body.locals[3].ty = Ty::Tuple(vec![Ty::i32(), Ty::Bool]);
        let loops = detect_loops(&func.body);
        assert_eq!(loops.len(), 1);
        assert!(loop_measure_bindings(&func, &loops[0], "n").is_none());
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert!(vcs.is_empty(), "signed checked-sub loop must remain obligation-free, got {vcs:?}");
    }
}

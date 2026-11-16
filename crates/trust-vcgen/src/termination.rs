// ignore-tidy-file-filelength -- pre-existing size, recorded 2026-08-21; do not grow casually
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
//   - A member of a multi-member recursion SCC (compiler facts, keyed on
//     DefIds) is charged at EVERY call into its SCC instead, the callee's
//     measure substituted: see `termination/recursion_scc.rs` (2026-09-25).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;
use trust_types::*;

/// The `UnsupportedMir` kind of the visible, never-provable marker an authored or
/// budget-tripped recursion measure publishes when it cannot cover every
/// recursive edge (`unsupported_recursion_decreases_vc`). Exported (D9,
/// 2026-09-27) because the compiler's `termination-unmeasured` charge treats this
/// marker, like any `NonTermination { context: RECURSION_TERMINATION_CONTEXT }`
/// row, as the lane having made a VISIBLE termination statement for the function.
pub const RECURSION_DECREASES_UNSUPPORTED_KIND: &str = "ContractKind::Decreases::Recursion";

/// The `context` of every recursion `NonTermination` row this lane mints (the
/// direct-self inferred, compound and authored lanes, and the recursion-SCC lane).
/// A loop row carries `"loop"`. Exported for the same D9 reader as the marker kind
/// above, so the compiler matches the constant, not a copy of the literal.
pub const RECURSION_TERMINATION_CONTEXT: &str = "recursion";

// Trust (2026-09-25): the recursion-SCC (mutual recursion) lane lives in its own
// file so this one does not grow; see its module comment.
mod recursion_scc;

fn fallback_loop_measure_symbol(measure: &str, phase: &str) -> String {
    format!("__trust_termination__{measure}_{phase}")
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
    if crate::generate::cached_terminator_presence_for_body(body)
        .is_some_and(|tp| !tp.has_back_edge)
    {
        return Vec::new();
    }
    // Fast path for forward-only DAG CFGs: if every in-range successor `v` of every
    // block `u` (`u.id.0 < n`) satisfies `u.id.0 < v.0`, then every block `b < n` is
    // reachable from the virtual root in the augmented dominator graph via a path in
    // `{root} ∪ {0..=b}`, so no `v > u` can ever dominate `u`.
    let has_non_forward_edge = body.blocks.iter().any(|block| {
        block.id.0 < n
            && terminator_any_successor(&block.terminator, |succ| {
                succ.0 < n && succ.0 <= block.id.0
            })
    });
    if !has_non_forward_edge {
        return Vec::new();
    }
    let preds = compute_predecessors(body);
    let dom = compute_dominators_with_preds(body, &preds);
    let mut loops = Vec::new();

    for block in &body.blocks {
        let latch = block.id;
        if latch.0 >= n {
            continue;
        }
        for_each_block_successor(&block.terminator, |header| {
            // Back-edge iff the successor (`header`) dominates this block
            // (`latch`). A self-loop (header == latch) qualifies because every
            // block dominates itself.
            let is_back_edge = header.0 < n && dom.dominates(header.0, latch.0);
            if !is_back_edge {
                return;
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
        });
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
        for_each_block_successor(&block.terminator, |succ| {
            if succ.0 < n {
                preds[succ.0].push(block.id.0);
            }
        });
    }
    preds
}

/// The natural-loop block set for one proven back-edge `latch -> header`.
fn natural_loop_blocks(header: BlockId, latch: BlockId, preds: &[Vec<usize>]) -> Vec<BlockId> {
    if latch == header {
        return vec![header];
    }
    let mut members: FxHashSet<usize> = [header.0, latch.0].into_iter().collect();
    let mut work = vec![latch.0];
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
    members.sort_unstable_by_key(|id| id.0);
    members
}

/// The dominator relation of a body's CFG (`block_successors`), rooted at the entry.
///
/// `dominates(a, b)` answers exactly what the retired dense sets answered for
/// `dominators[b].contains(&a)` — the GREATEST fixpoint of
///   dom(entry) = {entry}
///   dom(b)     = {b} ∪ (⋂ dom(p) for p ∈ preds(b))      (an empty ⋂ is ∅)
/// — but from a dominator TREE: O(n + e) memory and O(1) per query, where the dense
/// `Vec<FxHashSet<usize>>` was Θ(n²) memory, Θ(n²) per refinement round, and carried
/// an iteration cap (`n² + n + 16`) for totality.
///
/// WHY THE TREE IS THAT FIXPOINT. Add a virtual root `R` with an edge to the entry and
/// to every block that has no predecessor. For a block reachable from `R`, the
/// equations above are the textbook dominator equations of the augmented graph with
/// `R` removed from every set (a predecessor-less block `s` gets `{s}`, exactly the
/// `∅`-intersection case; the entry gets `{entry}`, since `R -> entry` is an edge),
/// whose greatest solution is the true dominator relation — the tree's ancestor
/// relation. A block NOT reachable from `R` lies only on predecessor cycles that no
/// source enters, so the greatest fixpoint never removes anything from its initial
/// value, the set of ALL blocks: it is dominated by every block.
/// `termination_dominators_parity` compares the two on random graphs.
pub(crate) struct Dominators {
    n: usize,
    tree: crate::generate::cfg_index::DomTree,
}

impl Dominators {
    /// `a` dominates `b` (`dominators[b].contains(&a)` of the retired dense sets).
    pub(crate) fn dominates(&self, a: usize, b: usize) -> bool {
        if a >= self.n || b >= self.n {
            return false;
        }
        if !self.tree.reachable(b as u32) {
            return true;
        }
        self.tree.dominates(a as u32, b as u32)
    }
}

/// Compute the dominator relation of `body` (see [`Dominators`]).
///
/// `body.blocks` is indexed by `BlockId` (`blocks[i].id.0 == i`), matching the
/// convention used throughout vcgen, so block indices double as positions.
pub(crate) fn compute_dominators(body: &VerifiableBody) -> Dominators {
    let preds = compute_predecessors(body);
    compute_dominators_with_preds(body, &preds)
}

fn compute_dominators_with_preds(body: &VerifiableBody, preds: &[Vec<usize>]) -> Dominators {
    use crate::generate::cfg_index::{Csr, DomTree};
    let n = body.blocks.len();
    let root = n as u32;
    let mut edges: Vec<(u32, u32)> = Vec::with_capacity(n.saturating_mul(2));
    for (b, ps) in preds.iter().enumerate() {
        for &p in ps {
            edges.push((p as u32, b as u32));
        }
    }
    if n > 0 {
        edges.push((root, 0));
    }
    for (b, ps) in preds.iter().enumerate() {
        if b != 0 && ps.is_empty() {
            edges.push((root, b as u32));
        }
    }
    let rev: Vec<(u32, u32)> = edges.iter().map(|&(a, b)| (b, a)).collect();
    let succ = Csr::from_edges(n + 1, &edges);
    let pred_csr = Csr::from_edges(n + 1, &rev);
    Dominators { n, tree: DomTree::build(root, &succ, &pred_csr) }
}

/// The retired dense dominator sets, kept as the parity reference for
/// [`compute_dominators`].
#[cfg(test)]
pub(crate) fn compute_dominators_dense(body: &VerifiableBody) -> Vec<FxHashSet<usize>> {
    let n = body.blocks.len();
    if n == 0 {
        return Vec::new();
    }

    let preds = compute_predecessors(body);

    const ENTRY: usize = 0;
    let all: FxHashSet<usize> = (0..n).collect();
    let mut dom: Vec<FxHashSet<usize>> = vec![all; n];
    dom[ENTRY] = std::iter::once(ENTRY).collect();

    let mut changed = true;
    while changed {
        changed = false;
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
    if crate::generate::cached_terminator_presence_for_body(&func.body)
        .is_some_and(|tp| !tp.has_call && !tp.has_tail_call)
    {
        return Vec::new();
    }
    let mut sites = Vec::new();
    let mut own: Option<&str> = None;

    for block in &func.body.blocks {
        let (callee, args, span) = match &block.terminator {
            Terminator::Call { func, args, span, .. }
            | Terminator::TailCall { func, args, span, .. } => (func, args, span),
            _ => continue,
        };
        let own = *own.get_or_insert_with(|| direct_call_identity(&func.def_path));
        if is_direct_self_call_with_own(func, own, block.id, callee) {
            sites.push(RecursiveCallSite {
                block: block.id,
                args: args.clone(),
                span: span.clone(),
            });
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
#[cfg(test)]
fn is_direct_self_call(func: &VerifiableFunction, block: BlockId, callee: &str) -> bool {
    is_direct_self_call_with_own(func, direct_call_identity(&func.def_path), block, callee)
}

fn is_direct_self_call_with_own(
    func: &VerifiableFunction,
    own: &str,
    block: BlockId,
    callee: &str,
) -> bool {
    // Trust (ARGS-FINGERPRINT-READ-1 round 2, 2026-10-07): a callee carrying the
    // duplicate-crate-name argument fingerprint is NEVER a self call. The producer
    // writes it exactly when a def in the call's generic arguments — for a trait
    // method that includes `Self` — lives in a crate whose rendered name does not
    // identify it, so the qualifier this comparison keeps (`<W<dupty::T> as Tr>`)
    // may name either of two impls. MEASURED (round-1 review, `mut/chain.rs`): with
    // the tag stripped, `<W<dup_b::T> as Tr>::f::<G>` inside `<W<dup_a::T> as Tr>::f`
    // read as a self call and the non-recursive caller got a PROVED descent row
    // while the callee loops; the same edge without `<G>` was already proved on the
    // preview3 stage 1, because `direct_call_identity` drops ONE trailing group and
    // the tag was it. FAIL CLOSED: the edge becomes a non-self call, which both
    // recursion lanes report as an uncertainty.
    //
    // Trust (ARGS-FINGERPRINT-READ-1 round 3, 2026-10-07): and a block the
    // COMPILER did not file as a possible self call (decided from `DefId`s,
    // `crate::compiler_admits_direct_self_call`) is never one, whatever it
    // renders. The rendered def path is not an identity: two local impls whose
    // self types differ only in a same-named crate (`W<dup_a::T>` / `W<dup_b::T>`,
    // or `W<other::T>` / `W<T>` in a Cargo bin+lib pair) render ONE path, and a
    // MONOMORPHIC call into the other impl has no generic argument to tag.
    // MEASURED (`chain_ng.rs` on the preview3 stage 1 `7be75e9a80` and on round 2;
    // `r3/binlib.rs` on round 2): the non-recursive caller got a PROVED "recursion
    // measure `n` may not decrease" row while its callee loops. The set only
    // removes classifications; with no compiler context the path decides alone.
    if !callee.trim_end().starts_with(own) {
        return false;
    }
    if trust_types::args_display_may_name_a_same_named_crate(callee) {
        return false;
    }
    if direct_call_identity(callee) == own {
        return crate::compiler_admits_direct_self_call(&func.def_path, block);
    }
    // Trust (GENERIC-CALL-KEY-ALIAS-1 with ARGS-FINGERPRINT-READ-1 round 4,
    // 2026-10-10): since GENERIC-CALL-KEY-ALIAS-1 the extractor also writes
    // `::<__trust_alias@…>` on a trait call it CANNOT resolve (its arguments name a
    // type or const parameter), not only on one it resolved elsewhere. Inside
    // `impl<X> Tr for W<X>`, the where-clause call `<W<X> as Tr>::f(n)` is such a
    // call, and it runs this very body: the compiler files it from `DefId`s
    // (`SelfCallClass::ImplementedTraitItem`, unique def path). Reading every
    // alias as "never a self call" withdrew it from both recursion lanes, and D9's
    // `skipped` charge alone let `where_clause_self_call_unique_path.rs` build rc 0
    // where main refused it (MEASURED, the integrated stage 1 of `dca9c7d015`
    // against main `912bbdf300`). An alias whose untagged path is this function's
    // own is therefore a self call exactly when the compiler's INSTALLED set files
    // its block; with no set it stays a non-self call, as before.
    //
    // Trust (GCKA-SELF-CALL-2, 2026-10-10): the extractor no longer tags a call at
    // its caller's own identity arguments to the trait item the caller implements
    // (the where-clause call above is one), so such a call reaches the untagged
    // comparison above. This branch still reads a tagged one, such as a self call
    // whose def path another local function also renders.
    strip_local_key_alias_tag(callee).is_some_and(|base| direct_call_identity(base) == own)
        && crate::compiler_files_direct_self_call(&func.def_path, block)
}

/// The path of a callee whose ONLY terminal group is the extractor's local
/// definition key alias tag (`::<__trust_alias@` + 32 hex digits + `>`,
/// `trust_mir_extract::convert::tag_local_definition_key_alias`), with that group
/// removed; `None` for any other spelling.
fn strip_local_key_alias_tag(callee: &str) -> Option<&str> {
    const OPEN: &str = "::<__trust_alias@";
    let trimmed = callee.trim_end();
    let body = trimmed.strip_suffix('>')?;
    let at = body.rfind(OPEN)?;
    let hex = &body[at + OPEN.len()..];
    (hex.len() == 32 && hex.bytes().all(|b| b.is_ascii_hexdigit())).then(|| &trimmed[..at])
}

/// A call path with ONLY a terminal turbofish removed (`crate::f::<u32>` ->
/// `crate::f`; `<S as Tr>::f::<u32>` -> `<S as Tr>::f`).
///
/// Trust (2026-09-16, refuted): this used `trust_types::strip_generics`, which
/// erases EVERY `<...>` group — including a leading `<Self as Trait>` qualifier
/// — so `<crate::U as crate::Tr>::f` and `<crate::S as crate::Tr>::f` both
/// reduced to `::f` and compared EQUAL. Mutual recursion through two impls'
/// same-named trait method was classified as a direct self call, the inferred
/// lane saw no non-self call, and it minted a PROVED `[termination]` descent row
/// on a function that never returns (`S::f(1) -> U::f(0) -> U::g(0) ->
/// S::f(2) -> ...`, stack overflow at runtime). The qualifier is IDENTITY, not a
/// generic argument, and is kept verbatim; only the trailing `::<...>` that
/// rustc spells on a direct generic call is dropped.
// REBASE (2026-09-21): the parameter is spelled `callee`, not `path`. This takes a
// rendered CALLEE PATH, and the unsafe-mint campaign's forgeable-key scan
// (`sep_engine::tests::every_forgeable_key_predicate_in_this_crate_is_classified_\
// and_refuses_a_user_rebuild`) classifies a `&str` first parameter BY ITS NAME:
// `path` put this in the FILE-PATH class, where the only permitted disposition is
// `NotATrustDecision` — and this predicate decides direct self-recursion, which is
// what the inferred `[termination]` descent row rests on. Spelling it `callee` puts
// it in the callee-path class the scan already tracks (158+ members), which is what
// it actually is. Behaviour is unchanged.
//
// Trust (ARGS-FINGERPRINT-READ-1 round 2, 2026-10-07): the duplicate-crate-name
// argument fingerprint `::<__trust_args@HEX>` is KEPT here, so a tagged callee keeps
// its tag as its last `::<…>` group and never equals a bare def path. Round 1
// stripped it, and the review MEASURED why that is wrong: the producer writes the
// tag exactly when an argument names a crate whose rendered name does not identify
// it, and the impl's own `Self` (`W<dup_a::T>` vs `W<dup_b::T>`, both rendering
// `W<dupty::T>`) is part of the path this function keeps. Stripped, the call
// `<W<dup_b::T> as Tr>::f::<G>` inside `<W<dup_a::T> as Tr>::f` read as a SELF call,
// and the non-recursive caller got a PROVED "recursion measure n may not decrease"
// row while its callee loops forever. A generic fn's own self call `down::<T>` is
// not tagged (a `ty::Param` names no crate), so it is seen as in an ordinary graph.
fn direct_call_identity(callee: &str) -> &str {
    let trimmed = callee.trim_end();
    if !trimmed.ends_with('>') {
        return trimmed;
    }
    // Walk back over the balanced terminal `<...>` group, ignoring `->` return-type arrows.
    let bytes = trimmed.as_bytes();
    let mut depth = 0usize;
    let mut open = None;
    for (index, &b) in bytes.iter().enumerate().rev() {
        match b {
            b'>' if index == 0 || bytes[index - 1] != b'-' => depth += 1,
            b'<' => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    open = Some(index);
                    break;
                }
            }
            _ => {}
        }
    }
    match open {
        // Trust (ARGS-FINGERPRINT-READ-1 round 3, 2026-10-07): a verifier marker
        // group (`::<__trust_alias@…>`, `::<__trust_args@…>`, a total-call
        // sentinel) is IDENTITY, never a turbofish, and is kept. `__trust_alias@`
        // is written exactly when a call wears a local definition key WITHOUT
        // running that definition (SUMMARY-NAME-COLLIDE-1); stripping it made such
        // a call equal the key it was tagged away from, and so a self call.
        // `@` and a leading `__trust_` group cannot be spelled by a turbofish a
        // user writes as the WHOLE group content of a real self call (a type
        // named `__trust_x` keeps the path whole too, so it fails closed).
        Some(open)
            if trimmed[..open].ends_with("::") && !trimmed[open + 1..].starts_with("__trust_") =>
        {
            &trimmed[..open - 2]
        }
        // A terminal group not introduced by `::` is a qualifier or a malformed
        // spelling, never a turbofish: keep the path whole (no self-call match
        // unless byte-identical).
        _ => trimmed,
    }
}

/// Trust (2026-09-16, refuted): a recursion descent row is a WHOLE-FUNCTION
/// termination claim (`UNSAT means the function terminates`), but it speaks only
/// about the self-call edges. `loop { if n == 0 { return; } f(n - 1); }` proved
/// its descent (`n - 1 < n`) and was fully green under strict AND certify — and
/// never returns for `n > 0`: the descent returns and the loop re-runs with `n`
/// unchanged. The loop lane mints nothing for a loop whose measure it cannot
/// bind, so the false descent row was the body's ONLY termination verdict. A
/// CFG back-edge therefore makes both recursion lanes uncertain: the measure
/// relates the self-call to the entry, not the loop's iterations to each other.
/// Fail-closed: the authored lane reports it (`decreases` on the LOOP is the
/// fix), the inferred lane mints nothing.
fn enclosing_loop_uncertainty(
    has_recursive_calls: bool,
    loops: &[LoopInfo],
) -> Option<String> {
    // A body with no recursive edge makes no descent claim: an authored clause
    // there is vacuous by construction and stays visible alongside whatever the
    // loop lane mints (pinned by
    // `test_nonrecursive_exact_decreases_stays_visible_alongside_loop_obligations`).
    if !has_recursive_calls {
        return None;
    }
    let first = loops.first()?;
    Some(format!(
        "a recursion measure cannot cover the loop headed at bb{} (back-edge from bb{}): the \
         self-call's descent says nothing about the loop's own iterations — add a `decreases` \
         clause to the loop, or restructure it as recursion",
        first.header.0, first._latch.0
    ))
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
#[cfg(test)]
fn authored_recursion_identity_uncertainty(func: &VerifiableFunction) -> Option<String> {
    let recursive_calls = detect_recursive_calls(func);
    let loops = detect_loops(&func.body);
    authored_recursion_identity_uncertainty_with(func, &recursive_calls, &loops)
}

fn authored_recursion_identity_uncertainty_with(
    func: &VerifiableFunction,
    recursive_calls: &[RecursiveCallSite],
    loops: &[LoopInfo],
) -> Option<String> {
    if let Some(detail) = enclosing_loop_uncertainty(!recursive_calls.is_empty(), loops) {
        return Some(detail);
    }
    func.body.blocks.iter().find_map(|block| match &block.terminator {
        Terminator::Call { func: callee, .. } | Terminator::TailCall { func: callee, .. }
            if !recursive_calls.iter().any(|site| site.block == block.id) =>
        {
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

/// Trust (refuted 2026-09-16): the INFERRED lane's twin of
/// `authored_recursion_identity_uncertainty`. The inferred direct-self-call
/// descent rows are minted under `NonTermination { recursion }` — a
/// whole-function termination claim ("UNSAT means the function terminates") —
/// yet the lane used to run no topology gate at all, so `f(n) { back(n); f(n-1) }`
/// with `back(x) { f(x) }` shipped a PROVED `[termination]` row and overflowed
/// the stack (measured; the authored lane refuses the identical topology with
/// "cannot classify non-self call"). The gate is the authored one with a single
/// relaxation: a non-self call the COMPILER judged NON-REENTRANT — a vanilla
/// sysroot routine, installed through the `VcgenContext` — cannot re-enter this
/// crate and is not an uncertainty, so `fact(n - 1)?.checked_mul(n as u64)`
/// keeps its proof. Missing context classifies nothing (fail-closed).
fn inferred_recursion_identity_uncertainty(
    func: &VerifiableFunction,
    recursive_calls: &[RecursiveCallSite],
    loops: &[LoopInfo],
) -> Option<String> {
    if let Some(detail) = enclosing_loop_uncertainty(!recursive_calls.is_empty(), loops) {
        return Some(detail);
    }
    func.body.blocks.iter().find_map(|block| match &block.terminator {
        Terminator::Call { func: callee, .. } | Terminator::TailCall { func: callee, .. }
            if !recursive_calls.iter().any(|site| site.block == block.id)
                && !crate::callee_is_nonreentrant_for(&func.def_path, callee) =>
        {
            Some(format!(
                "inferred recursion measure cannot classify non-self call `{callee}` in bb{} as \
                 non-recursive",
                block.id.0
            ))
        }
        Terminator::Drop { .. } => Some(format!(
            "inferred recursion measure cannot classify Drop in bb{} as non-recursive",
            block.id.0
        )),
        Terminator::Opaque { kind, .. } => Some(format!(
            "inferred recursion measure cannot classify opaque terminator `{kind}` in bb{} as \
             non-recursive",
            block.id.0
        )),
        Terminator::Call { .. }
        | Terminator::TailCall { .. }
        | Terminator::Goto(_)
        | Terminator::SwitchInt { .. }
        | Terminator::Return
        | Terminator::Assert { .. }
        | Terminator::Unreachable
        | Terminator::Resume => None,
        _ => Some(format!(
            "inferred recursion measure cannot classify an unrecognized terminator in bb{} as \
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
    let blocks_sorted = blocks.is_sorted_by_key(|b| b.0);
    let in_blocks = |id: BlockId| {
        if blocks_sorted {
            blocks.binary_search_by_key(&id.0, |b| b.0).is_ok()
        } else {
            blocks.contains(&id)
        }
    };

    for block in &func.body.blocks {
        if !in_blocks(block.id) {
            continue;
        }
        for stmt in &block.stmts {
            if let Statement::Assign { place, .. } = stmt
                && let Some(decl) = func.body.locals.get(place.local)
                && decl.ty.is_integer()
                && place.projections.is_empty()
                && !modified.iter().any(|(idx, _)| *idx == place.local)
            {
                let name = decl.name.clone().unwrap_or_else(|| format!("_{}", place.local));
                modified.push((place.local, name));
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
    decreases_clauses_of(&func.contracts)
}

/// Trust (2026-09-25): the function-level recursion `decreases` measures of a
/// contract list, read EXACTLY as [`check_termination`] reads them (loop-local
/// and unpaired loop clauses excluded, the compiler-lowering marker stripped).
///
/// The compiler uses this to compute a recursion-SCC member's measure from the
/// member's own contract bundle, so the measure its callers compare against is
/// the one the member's own rows are checked with (see
/// `RecursionSccContext::own_measure`, which re-checks the equality).
#[must_use]
pub fn function_level_recursion_measures(contracts: &[Contract]) -> Vec<String> {
    decreases_clauses_of(contracts).into_iter().map(|clause| clause.measure).collect()
}

fn decreases_clauses_of(contracts: &[Contract]) -> Vec<DecreasesClause> {
    if contracts.is_empty() {
        return Vec::new();
    }
    contracts
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
            // Compiler-native clauses retain a schema marker in `Contract::body`
            // so their query provenance cannot be confused with compatibility
            // source text.  The marker is not part of the authored numeric
            // expression, however, and must never enter parameter lookup or
            // recursive-call substitution.
            measure: recursion_decreases_measure(&c.body).to_string(),
            span: c.span.clone(),
            kind: DecreasesKind::Recursion,
        })
        .collect()
}

fn recursion_decreases_measure(body: &str) -> &str {
    body.strip_prefix(crate::contracts::LOWERED_CONTRACT_PREFIX).unwrap_or(body).trim()
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
    // Trust (2026-09-25, mutual recursion): a member of a multi-member
    // recursion SCC is charged by the SCC lane for EVERY recursive edge (self
    // calls included) and never reaches the direct-self lanes below, whose
    // "mint nothing" arms are exactly how `a(n) { b(n) } b(n) { a(n) }` used to
    // verify. Loop rows are generated identically either way.
    if let Some(scc) = crate::recursion_scc_context_for(&func.def_path) {
        recursion_scc::check_recursion_scc_termination(func, &scc, &loops, vcs);
        generate_loop_termination_vcs(func, &loops, vcs);
        return;
    }
    let recursive_calls = detect_recursive_calls(func);
    if recursive_calls.is_empty() && loops.is_empty() && func.contracts.is_empty() {
        return;
    }
    let decreases_clauses = extract_decreases_contracts(func);
    let authored_recursion_uncertainty = if decreases_clauses.is_empty() {
        None
    } else {
        authored_recursion_identity_uncertainty_with(func, &recursive_calls, &loops)
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
                        context: RECURSION_TERMINATION_CONTEXT.to_string(),
                        measure: clause.measure.clone(),
                    },
                    function: func.name.as_str().into(),
                    location: clause.span.clone(),
                    formula: Formula::Bool(false),
                    contract_metadata: source_contract_metadata(source_contract_index),
                    obligation: None,
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
    generate_loop_termination_vcs(func, &loops, vcs);

    // The function-level authored clause was accounted for before loop
    // generation. With no recursive edge there are no call-site decrease
    // obligations to add, and re-validating here would duplicate its marker.
    if authored_recursion_uncertainty.is_some() || recursive_calls.is_empty() {
        return;
    }
    // Trust (refuted 2026-09-16): the INFERRED lane runs the same whole-body
    // topology gate as the authored one (relaxed only for compiler-judged
    // non-reentrant callees). When it fires the lane mints NOTHING — no
    // descent row under the whole-function `termination` label, and no
    // marker either: a visible no-fallback marker (Unknown) would make every
    // recursive function with an unclassified helper call fatal on every lane.
    // Trust (D9, ruled 2026-09-27): "nothing" here is no longer silence. The
    // compiler charges every direct self call of a function for which this lane
    // made no recursion statement as an `assumption:termination-unmeasured` row
    // (CONDITIONAL on the default lane, refused under `certify`) — see
    // `compiler/rustc_mir_transform/src/trust_verify/termination_unmeasured.rs`.
    // That charge reads exactly this all-or-nothing contract: a recursion row or
    // `RECURSION_DECREASES_UNSUPPORTED_KIND` marker for the function means every
    // recursive site was covered, NO such row means none was. Never mint a
    // PARTIAL set (pinned by
    // `inferred_recursion_rows_cover_every_self_call_site_or_none`).
    if decreases_clauses.is_empty()
        && inferred_recursion_identity_uncertainty(func, &recursive_calls, &loops).is_some()
    {
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

    // Compound `bound - counter` measure — the additive extension for
    // increasing-counter recursions (`cover(.., naxes, d)` counts `d` UP toward
    // `naxes`; the bare single-decreasing-param lane cannot bind such a shape).
    // Attempted ONLY in the inference regime (no authored function-level
    // `decreases`, which is exact proof surface we must never override) and ONLY
    // when EVERY fail-closed soundness guard in `infer_compound_recursion_measure`
    // holds. When it fires the emitted VC is UNSAT (Proved) by construction (see
    // `compound_recursion_vcs`), so this can only upgrade a bare-measure Unknown
    // to Proved — it never flips an existing verdict and never admits a
    // genuinely non-terminating recursion. `compound_recursion_vcs` is
    // all-or-nothing: a row for every site or none, and "none" leaves the
    // function with no recursion statement, which the compiler's D9 charge
    // reads as unmeasured (review F3, 2026-09-27).
    if explicit_clause.is_none()
        && let Some(compound) = infer_compound_recursion_measure(func, &recursive_calls)
    {
        vcs.extend(compound_recursion_vcs(func, &recursive_calls, &compound));
        return;
    }

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
    // Trust (verifier-perf, MEASURED 2026-08-31): the per-call-site path-guard
    // conjoin below needs two whole-CFG analyses that are pure functions of
    // `func`. Build them ONCE for the whole loop instead of once per recursive
    // call site. On `trust-spec-elab` this single call site was 99.9% of the R1
    // pre-pass's thread time (driver `sha256:6bf8876323cc…d60b2`): `elab_term`,
    // an 815-basic-block recursive syn tree-walker, paid two whole-CFG fixpoints
    // at EVERY one of its recursive edges. The cache holds a shared borrow of
    // `func`, so it cannot observe a mutation — see `FuncAnalysisScope`.
    // Trust (L0 termination guarantee): this loop is one of the VC-generation
    // walks the budget docs claim to bound. Measured 2026-08-31, it polled
    // nothing. A trip drops the whole recursion set and records ONE unsupported
    // row below — never a silent absence, and never a Proved.
    let mut budget_tripped = false;
    // Trust (refuted 2026-09-16, round 2): an inferred binding miss at ONE
    // self-call site used to `continue` while a sibling site still minted its
    // descent row under the whole-function `termination` label — so
    // `f(a - 1); let j = a / 3; f(a)` shipped a PROVED `[termination]` row and
    // overflowed the stack (the site sharing a block with the division was
    // silently dropped). A miss at any site now withholds every inferred row.
    let mut inferred_binding_miss = false;
    let exact_preconditions = exact_recursion_preconditions(func);
    for call_site in &recursive_calls {
        if trust_types::verify_budget::budget_exhausted() {
            budget_tripped = true;
            break;
        }
        let Some((measure_entry, measure_call, binding_facts, exact_site_span)) =
            recursion_measure_bindings(func, call_site, &measure)
        else {
            if explicit_clause.is_some() {
                explicit_binding_failure = Some(call_site.span.clone());
                break;
            }
            // An inferred measure is heuristic coverage only. A binding miss
            // therefore means no row, never a synthetic refutation — and (round
            // 2) no row for the SIBLING sites either: a partial set would be a
            // whole-function claim the unbound site was never checked against.
            inferred_binding_miss = true;
            break;
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
                context: RECURSION_TERMINATION_CONTEXT.to_string(),
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
                conjoin_exact_preconditions(&exact_preconditions, core),
            ),
            contract_metadata: source_contract_metadata(explicit_source_contract_index),
            obligation: None,
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
    } else if inferred_binding_miss {
        // Mint nothing: a visible no-fallback marker would make every recursive
        // function with an unbindable site fatal. Trust (D9, 2026-09-27): the
        // absence is no longer silent — the compiler charges every self call of
        // a function this lane left row-less as `assumption:termination-unmeasured`
        // (`trust_verify/termination_unmeasured.rs`), which is why a partial row
        // set must never be pushed here (see the comment above the topology gate).
    } else if budget_tripped {
        // Fail closed, LOUDLY. Dropping the partial `recursion_vcs` silently
        // would make an unchecked recursive edge indistinguishable from a
        // checked one — an obligation that DISAPPEARS is not one that proved.
        // Emit the same unsupported row the binding-failure arm emits, so the
        // truncation is a visible non-proof rather than an absence.
        vcs.push(unsupported_recursion_decreases_vc(
            func,
            func.span.clone(),
            format!(
                "per-function verification budget exhausted before every recursive call site \
                 could be checked against decreases measure `{measure}`"
            ),
        ));
    } else {
        vcs.extend(recursion_vcs);
    }
}

/// Generate the loop-lane `NonTermination` rows for every detected loop.
///
/// Factored out of [`check_termination`] (2026-09-25) so the recursion-SCC
/// lane runs the SAME loop generation as the direct-self lanes; the body is
/// unchanged.
fn generate_loop_termination_vcs(
    func: &VerifiableFunction,
    loops: &[LoopInfo],
    vcs: &mut Vec<VerificationCondition>,
) {
    let mut dominators: Option<Dominators> = None;
    for loop_info in loops {
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
            loop_measure_bindings_with_dom(func, loop_info, name, &mut dominators)
                .map(|(before, after)| (*local, name.clone(), before, after))
        });

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
                    let fallback_measure = modified
                        .first()
                        .map(|(_, name)| name.clone())
                        .unwrap_or_else(|| "unknown".to_string());
                    let before = Formula::Var(
                        fallback_loop_measure_symbol(&fallback_measure, "before"),
                        Sort::Int,
                    );
                    let after = Formula::Var(
                        fallback_loop_measure_symbol(&fallback_measure, "after"),
                        Sort::Int,
                    );
                    (None, fallback_measure, before, after, false)
                }
            };

        let lower_bound = has_unsigned_type_bound
            .then(|| Formula::Ge(Box::new(measure_before.clone()), Box::new(Formula::Int(0))));
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
        let core = match lower_bound {
            Some(lower_bound) => Formula::And(vec![lower_bound, not_decreasing]),
            None => not_decreasing,
        };

        vcs.push(VerificationCondition {
            kind: VcKind::NonTermination { context: "loop".to_string(), measure },
            function: func.name.as_str().into(),
            location: span,
            formula: conjoin_loop_invariant_preconditions(func, measure_local, core),
            contract_metadata: None,
            obligation: None,
        });
    }
}

fn unique_recursion_decreases_contract_index(
    func: &VerifiableFunction,
    clause: &DecreasesClause,
) -> Option<usize> {
    let mut matches = func.contracts.iter().enumerate().filter_map(|(index, contract)| {
        (matches!(contract.kind, ContractKind::Decreases)
            && recursion_decreases_measure(&contract.body) == clause.measure
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
        obligation: None,
    }
}

fn validated_explicit_recursion_clause<'a>(
    func: &VerifiableFunction,
    decreases_clauses: &'a [DecreasesClause],
) -> Result<Option<&'a DecreasesClause>, (SourceSpan, String)> {
    if decreases_clauses.is_empty() {
        return Ok(None);
    }
    let mut explicit = decreases_clauses
        .iter()
        .filter(|clause| matches!(clause.kind, DecreasesKind::Recursion));
    match (explicit.next(), explicit.next()) {
        (None, _) => Ok(None),
        (Some(clause), None)
            if unique_parameter_local_by_name(func, &clause.measure)
                .is_some_and(|decl| decl.ty.int_width().is_some()) =>
        {
            Ok(Some(clause))
        }
        (Some(clause), None) => Err((
            clause.span.clone(),
            format!(
                "function-level decreases expression `{}` is outside the exact supported \
                 fragment (one uniquely named integer parameter)",
                clause.measure
            ),
        )),
        (Some(first), Some(_)) => Err((
            first.span.clone(),
            format!(
                "{} function-level decreases clauses require unsupported lexicographic \
                 recursion semantics",
                2 + explicit.count()
            ),
        )),
    }
}

#[inline]
fn local_may_match_var_name_with_idx(
    decl: &LocalDecl,
    name: &str,
    parsed_idx: Option<usize>,
) -> bool {
    decl.name.as_deref() == Some(name) || parsed_idx == Some(decl.index)
}

/// Look up a `BasicBlock` by `BlockId` in O(1) when `body.blocks` is indexed
/// by `BlockId`, falling back to a linear scan on non-contiguous synthetic bodies.
#[inline]
fn block_by_id(body: &VerifiableBody, id: BlockId) -> Option<&BasicBlock> {
    body.blocks
        .get(id.0)
        .filter(|b| b.id == id)
        .or_else(|| body.blocks.iter().find(|b| b.id == id))
}

/// Conjoin only authored entry facts whose meaning remains exact at the
/// recursive call. Raw machine arithmetic is currently encoded as unbounded
/// Int and therefore cannot be an assumption (`u8::MAX + 1 == 0` is the
/// canonical mismatch). Every free name must map uniquely to a bare argument
/// local that is globally immutable; projected, synthetic, return, temp, and
/// versioned names are all dropped fail-closed.
pub(super) fn exact_recursion_preconditions(func: &VerifiableFunction) -> Vec<Formula> {
    if func.preconditions.is_empty() {
        return Vec::new();
    }
    let mut preconditions = Vec::new();
    for precondition in &func.preconditions {
        if crate::contracts::formula_uses_unmodeled_machine_arithmetic_in_function(
            func,
            precondition,
        ) {
            continue;
        }
        let exact = trust_types::all_free_variable_names(precondition, &mut |name| {
            if func.body.arg_count == 0 {
                return false;
            }
            let parsed_idx = name.strip_prefix('_').and_then(|rest| rest.parse::<usize>().ok());
            match crate::lookup_formula_local_decl(func, name, parsed_idx) {
                crate::FormulaLocalDeclLookup::None => false,
                crate::FormulaLocalDeclLookup::Unique(local) => {
                    local.index > 0
                        && local.index <= func.body.arg_count
                        && crate::place_to_var_name(func, &Place::local(local.index)) == name
                        && !local_ever_mutated(func, local.index)
                }
                crate::FormulaLocalDeclLookup::Ambiguous => {
                    let mut matching = func.body.locals.iter().filter(|decl| {
                        decl.index > 0
                            && decl.index <= func.body.arg_count
                            && local_may_match_var_name_with_idx(decl, name, parsed_idx)
                            && crate::place_to_var_name(func, &Place::local(decl.index)) == name
                    });
                    let Some(local) = matching.next() else {
                        return false;
                    };
                    matching.next().is_none() && !local_ever_mutated(func, local.index)
                }
            }
        });
        if exact {
            preconditions.push(precondition.clone());
        }
    }
    preconditions
}

pub(super) fn conjoin_exact_preconditions(
    exact_preconditions: &[Formula],
    formula: Formula,
) -> Formula {
    if exact_preconditions.is_empty() {
        formula
    } else {
        let mut clauses = Vec::with_capacity(exact_preconditions.len() + 1);
        clauses.extend_from_slice(exact_preconditions);
        clauses.push(formula);
        Formula::And(clauses)
    }
}

#[cfg(test)]
fn conjoin_recursion_preconditions(func: &VerifiableFunction, formula: Formula) -> Formula {
    conjoin_exact_preconditions(&exact_recursion_preconditions(func), formula)
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
    if func.preconditions.is_empty() {
        return formula;
    }
    let mut invariants = Vec::new();
    for precondition in &func.preconditions {
        let is_invariant = trust_types::all_free_variable_names(precondition, &mut |name| {
            let parsed_idx = name.strip_prefix('_').and_then(|rest| rest.parse::<usize>().ok());
            match crate::lookup_formula_local_decl(func, name, parsed_idx) {
                crate::FormulaLocalDeclLookup::None => false,
                crate::FormulaLocalDeclLookup::Unique(local) => {
                    Some(local.index) != measure_local
                        && crate::place_to_var_name(func, &Place::local(local.index)) == name
                        && !local_ever_mutated(func, local.index)
                }
                crate::FormulaLocalDeclLookup::Ambiguous => {
                    let mut matching = func.body.locals.iter().filter(|decl| {
                        local_may_match_var_name_with_idx(decl, name, parsed_idx)
                            && crate::place_to_var_name(func, &Place::local(decl.index)) == name
                    });
                    let Some(local) = matching.next() else {
                        return false;
                    };
                    matching.next().is_none()
                        && Some(local.index) != measure_local
                        && !local_ever_mutated(func, local.index)
                }
            }
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
#[cfg(test)]
fn loop_measure_bindings(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
    measure: &str,
) -> Option<(Formula, Formula)> {
    loop_measure_bindings_with_dom(func, loop_info, measure, &mut None)
}

fn loop_measure_bindings_with_dom(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
    measure: &str,
    dominators_slot: &mut Option<Dominators>,
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
    let dominators = dominators_slot.get_or_insert_with(|| compute_dominators(&func.body));
    if !dominators.dominates(assignment_block.0, loop_info._latch.0) {
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
    if assignment_block != header {
        for block in &func.body.blocks {
            if block.id == loop_info._latch || block.id == assignment_block {
                continue;
            }
            // PERF-COMPILER-VCGEN-747: test both O(1) `DomTree::dominates` conditions
            // before walking `block.terminator`'s successor targets.
            if !dominators.dominates(assignment_block.0, block.id.0)
                && dominators.dominates(header.0, block.id.0)
                && terminator_any_successor(&block.terminator, |s| s == header)
            {
                return None;
            }
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
    let body_blocks = &loop_info.body_blocks;
    let blocks_sorted = body_blocks.is_sorted_by_key(|b| b.0);
    let in_loop = |id: BlockId| {
        if blocks_sorted {
            body_blocks.binary_search_by_key(&id.0, |b| b.0).is_ok()
        } else {
            body_blocks.contains(&id)
        }
    };
    crate::any_local_write_candidate(func, &func.body.blocks, measure_local, |block, item| {
        let block_is_in_loop = in_loop(block.id);
        match item {
            Some(stmt) => match stmt {
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
                    matches!(rvalue, Rvalue::Ref { mutable: true, place } if place.local == measure_local)
                        || matches!(rvalue, Rvalue::AddressOf(_, place) if place.local == measure_local)
                }
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                    block_is_in_loop && place.local == measure_local
                }
                Statement::Intrinsic { .. } | Statement::Unsupported { .. } => block_is_in_loop,
                _ => false,
            },
            None => {
                if !block_is_in_loop {
                    return false;
                }
                match &block.terminator {
                    Terminator::Call { dest, .. } if dest.local == measure_local => true,
                    Terminator::Opaque { .. } => true,
                    _ => false,
                }
            }
        }
    })
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
    let param_pos = measure_decl.index.checked_sub(1)?;
    recursion_measure_bindings_at(func, call.block, &call.args, measure_decl, param_pos)
}

/// [`recursion_measure_bindings`] with the call argument chosen by POSITION
/// rather than by the caller's own parameter index.
///
/// A direct self call reads the caller's measure parameter back out of its own
/// argument list, so the two coincide. A call into ANOTHER member of the
/// recursion SCC compares the caller's entry measure (`measure_decl`) against
/// the CALLEE's measure at the call, which is the argument at the callee's
/// measure position (`arg_pos`, supplied by the compiler from the callee's
/// `DefId`). The argument's value is resolved exactly as for a self call.
fn recursion_measure_bindings_at(
    func: &VerifiableFunction,
    call_block: BlockId,
    call_args: &[Operand],
    measure_decl: &LocalDecl,
    arg_pos: usize,
) -> Option<(Formula, Formula, Vec<Formula>, Option<SourceSpan>)> {
    if measure_decl.ty.int_width().is_none() {
        return None;
    }
    let arg = call_args.get(arg_pos)?;
    let entry =
        Formula::Var(crate::place_to_var_name(func, &Place::local(measure_decl.index)), Sort::Int);
    // rung-F checked-chain: when the measure argument is the `.0` unpack of
    // an overflow-checked op living in the UNIQUE Assert-predecessor block
    // (the debug-build `n - 1` shape: `_3 = CheckedSub(n, 1);
    // Assert(!_3.1) -> bbC: _4 = _3.0; call self(_4)`), substitute the
    // Assert-success value (`Sub(n, 1)`) for the otherwise-free temp. See
    // `resolve_checked_arg_chain` for the fail-closed applicability guards.
    let block = block_by_id(&func.body, call_block)?;
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

// ===========================================================================
// Compound `bound - counter` recursion measure (additive termination lane)
// ===========================================================================
//
// SOUNDNESS MODEL. For a recursion whose bare single-decreasing-parameter
// measure fails (e.g. `cover(coords, naxes, d)` counts `d` UP), admit the
// compound measure `M = bound - counter` under FOUR fail-closed guards, all of
// which the pair of never-mutated integer VALUE parameters (`bound`, `counter`)
// makes checkable INTRAPROCEDURALLY:
//
//   (1) STRICT DECREASE. At every recursive call `counter` is passed as
//       `counter + k` / `counter.saturating_add(k)` with `k` a POSITIVE integer
//       literal (`resolve_counter_increment`), so `M_call = bound - (counter+k)`
//       is `M_entry - k < M_entry`.
//   (2) `bound` INVARIANCE. `bound` is a value parameter never written in the
//       body (`local_ever_mutated`) and passed UNCHANGED at every recursive
//       call (`operand_reads_unchanged_local`). A value parameter cannot be
//       mutated by any callee, so read-only-ness of the body is sufficient and
//       sound — `bound_call == bound_entry`.
//   (3) WELL-FOUNDEDNESS FROM A `>=`/`>` DOMINATING GUARD (NOT `==`). A base
//       guard `counter >= bound` (or `counter > bound`) whose block DOMINATES
//       every recursive-call block, and whose base (guard-TRUE) edge cannot
//       reach any recursive call, forces every path to a recursive call through
//       the guard-FALSE edge — where `counter < bound` (resp. `counter <= bound`)
//       holds. Since `counter`/`bound` are immutable that fact carries to the
//       call, giving `M_entry >= 1 > 0` (resp. `>= 0`). An `==` guard is
//       REJECTED: it only yields `counter != bound`, which does NOT bound `M`
//       below, and would falsely prove the non-terminating
//       `fn bad(bound,counter){ if counter==bound {return} bad(bound,counter+1) }`
//       called with `counter > bound`.
//   (4) The `not_decreasing` VC `(M_call >= M_entry) OR (M_entry < 0)` conjoined
//       with the guard fact is UNSAT: `M_call >= M_entry` reduces to `-k >= 0`
//       (false), and `M_entry < 0` (`bound < counter`) contradicts the fact.
//       So a VC is emitted ONLY for a genuinely terminating recursion.
//
// The `saturating_add(counter, k)` step is modeled as the plain `counter + k`
// increase: given the guard fact `counter < bound <= usize::MAX` we have
// `counter < usize::MAX`, so `saturating_add(counter, k) = min(counter+k, MAX)`
// is `>= counter + 1 > counter` — a genuine strict increase — and the
// `counter + k` substitution is refuted TOGETHER with the conjoined fact (it is
// never emitted without it). See `resolve_saturating_add_increment`.
//
// The extension is strictly ADDITIVE: it fires only in the no-authored-clause
// inference regime, and only when all guards hold (⇒ the VC is Proved), so it
// can never change an existing verdict from terminating to not, nor admit a
// recursion that may not terminate.

/// A validated compound `bound - counter` termination measure over two
/// never-mutated integer value parameters.
#[derive(Debug, Clone, Copy)]
struct CompoundRecursionMeasure {
    /// The loop-invariant upper bound parameter (`naxes` for `cover`).
    bound_local: usize,
    /// The strictly-increasing recursion variable (`d` for `cover`).
    counter_local: usize,
    /// `true` for a `counter >= bound` guard (well-foundedness fact
    /// `counter < bound`); `false` for `counter > bound` (fact `counter <= bound`).
    strict: bool,
}

/// Try to infer a sound `bound - counter` measure for `func`'s direct recursion.
/// Returns `Some` ONLY when every soundness guard (see the module note above)
/// holds; otherwise `None` and the caller falls back to the bare lane.
fn infer_compound_recursion_measure(
    func: &VerifiableFunction,
    recursive_calls: &[RecursiveCallSite],
) -> Option<CompoundRecursionMeasure> {
    if recursive_calls.is_empty() {
        return None;
    }
    let arg_count = func.body.arg_count;
    // Integer VALUE parameters that are never written in the body. Immutability
    // is what lets `Var(param)` denote one value at every program point — the
    // premise of the guard fact, `bound` invariance, and the increasing step.
    let value_params: Vec<usize> = func
        .body
        .locals
        .iter()
        .filter(|decl| {
            decl.index >= 1
                && decl.index <= arg_count
                && decl.ty.int_width().is_some()
                && !local_ever_mutated(func, decl.index)
        })
        .map(|decl| decl.index)
        .collect();
    if value_params.len() < 2 {
        return None;
    }
    let mut dominators: Option<Dominators> = None;
    let mut recur_blocks: Option<Vec<usize>> = None;
    for &counter_local in &value_params {
        let Some(counter_pos) = counter_local.checked_sub(1) else {
            continue;
        };
        // `counter` must be a strictly-increasing step of ITSELF at every call.
        let counter_increases = recursive_calls.iter().all(|call| {
            block_by_id(&func.body, call.block)
                .zip(call.args.get(counter_pos))
                .is_some_and(|(block, arg)| {
                    resolve_counter_increment(func, block, arg, counter_local).is_some()
                })
        });
        if !counter_increases {
            continue;
        }
        for &bound_local in &value_params {
            if bound_local == counter_local {
                continue;
            }
            let Some(bound_pos) = bound_local.checked_sub(1) else {
                continue;
            };
            // `bound` must be passed UNCHANGED (a read of the same immutable
            // param) at every recursive call.
            let bound_unchanged = recursive_calls.iter().all(|call| {
                call.args
                    .get(bound_pos)
                    .is_some_and(|arg| operand_reads_unchanged_local(func, arg, bound_local))
            });
            if !bound_unchanged {
                continue;
            }
            let dom = dominators.get_or_insert_with(|| compute_dominators(&func.body));
            let rblocks = recur_blocks
                .get_or_insert_with(|| recursive_calls.iter().map(|c| c.block.0).collect());
            if let Some(strict) =
                find_dominating_bound_guard_with_dom(func, dom, rblocks, counter_local, bound_local)
            {
                return Some(CompoundRecursionMeasure { bound_local, counter_local, strict });
            }
        }
    }
    None
}

/// If `arg` is a strictly-increasing step `counter + k` (k a positive integer
/// literal) of the `counter` param, return `k`. Handles the debug-build
/// `counter + k` (CheckedAdd + no-overflow Assert chain, via the vetted
/// `resolve_checked_arg_chain`) and `counter.saturating_add(k)`. Fail-closed.
fn resolve_counter_increment(
    func: &VerifiableFunction,
    call_block: &BasicBlock,
    arg: &Operand,
    counter_local: usize,
) -> Option<u128> {
    // (a) debug `counter + k`: `_A = _T.0` with `_T = CheckedAdd(counter, k)` in
    //     the unique no-overflow Assert predecessor (exact `counter + k` value).
    if let Some((formula, _span)) = resolve_checked_arg_chain(func, call_block, arg) {
        let expected_counter = crate::place_to_formula(func, &Place::local(counter_local));
        if let Some(k) = counter_increment_from_formula(&formula, &expected_counter) {
            return Some(k);
        }
    }
    // (b) `counter.saturating_add(k)`.
    resolve_saturating_add_increment(func, arg, counter_local)
}

/// Extract `k >= 1` from a resolved step formula shaped `counter + k`
/// (either operand order), where `expected_counter` is the counter param's own
/// formula. Any other shape (a decrement, a non-literal, `k == 0`) is rejected.
fn counter_increment_from_formula(formula: &Formula, expected_counter: &Formula) -> Option<u128> {
    let Formula::Add(l, r) = formula else {
        return None;
    };
    let k_side = if l.as_ref() == expected_counter {
        r.as_ref()
    } else if r.as_ref() == expected_counter {
        l.as_ref()
    } else {
        return None;
    };
    match k_side {
        Formula::Int(k) if *k >= 1 => u128::try_from(*k).ok(),
        Formula::UInt(k) if *k >= 1 => Some(*k),
        _ => None,
    }
}

/// The std integer inherent `saturating_add` method
/// (`core::num::<impl uN>::saturating_add` / signed siblings). CRATE-ORIGIN
/// anchored exactly like `generate::saturating_add_sub_method`: a user-defined
/// `mymod::saturating_add` must NOT match (matching one would inject a false
/// strictly-increasing-step channel — a false-PROVE hole).
fn is_std_saturating_add(callee: &str) -> bool {
    let tail = callee.rsplit("::").next().unwrap_or(callee);
    let tail = tail.split('<').next().unwrap_or(tail).trim();
    tail == "saturating_add"
        && (callee.starts_with("core::") || callee.starts_with("std::"))
        && callee.contains("::num::")
}

/// If `arg` is `copy/move _X` where `_X`'s ONE value — on EVERY channel, the
/// implicit ENTRY definition of a parameter included — is one std
/// `saturating_add(counter, k)` call, with `counter` a bare read of the counter
/// param and `k` a positive integer literal, return `k`. Fail-closed on every
/// mismatch. See the module note for why modeling the saturating step as
/// `counter + k` is sound.
///
/// THE VALUE QUESTION IS `local_defs`'S, and it must be: the `k` returned here is
/// INLINED by `compound_recursion_vcs` as `M_call = bound - (counter + k)`, so a
/// wrong answer is not a lost hypothesis, it is a termination VC that is UNSAT
/// for a step that never happened. This scan used to be hand-rolled over
/// `func.body.blocks` and was blind to the one channel that is not in them — a
/// `mut` PARAMETER passed at the counter position, whose only body store is the
/// saturating call, still carries its caller-chosen ENTRY value on every path
/// that skips the call, and the resolver reported an increment on those paths
/// too. `local_defs::unique_value_call` counts the entry definition, so such a
/// parameter is two-valued and declines.
fn resolve_saturating_add_increment(
    func: &VerifiableFunction,
    arg: &Operand,
    counter_local: usize,
) -> Option<u128> {
    let temp = match arg {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => p.local,
        _ => return None,
    };
    if crate::local_defs::is_parameter(func, temp) {
        return None;
    }
    let Terminator::Call { func: callee, args, .. } =
        crate::local_defs::unique_value_call(func, temp)?
    else {
        return None;
    };
    if !is_std_saturating_add(callee) || args.len() != 2 {
        return None; // temp defined by some other call
    }
    let counter_ok = matches!(
        &args[0],
        Operand::Copy(p) | Operand::Move(p)
            if p.projections.is_empty() && p.local == counter_local
    );
    if !counter_ok {
        return None;
    }
    match &args[1] {
        Operand::Constant(ConstValue::Uint(k, _)) if *k >= 1 => Some(*k),
        Operand::Constant(ConstValue::Int(k)) if *k >= 1 => u128::try_from(*k).ok(),
        _ => None,
    }
}

/// `true` iff `operand` denotes the current value of the never-mutated value
/// parameter `target_local`: either a direct bare read, or a bare read of a local
/// whose ONE value — again on every channel, the ENTRY definition included — is
/// `Use(bare read of target_local)`. Since `target_local` is immutable both forms
/// denote the entry value. Fail-closed.
///
/// The hop is adjudicated by `local_defs`, not by a scan of `func.body.blocks`
/// here. The two conjuncts are both needed and neither implies the other:
/// `is_single_static_assignment` refuses the channels a resolver must not
/// tolerate (a `Call` destination, a projected store, a `SetDiscriminant`/
/// `Deinit`/`Drop`, a `&mut`/`&raw` ESCAPE, an unlocatable pointer write) and
/// charges a parameter for its entry definition, so a `mut` parameter with one
/// body store scores two and declines; `unique_value_def` is what names the
/// value, and it declines every parameter outright.
fn operand_reads_unchanged_local(
    func: &VerifiableFunction,
    operand: &Operand,
    target_local: usize,
) -> bool {
    let place = match operand {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => p,
        _ => return false,
    };
    if place.local == target_local {
        return true;
    }
    let hop = place.local;
    !crate::local_defs::is_parameter(func, hop)
        && crate::local_defs::is_single_static_assignment(func, hop)
        && matches!(
            crate::local_defs::unique_value_def(func, hop),
            Some(Rvalue::Use(Operand::Copy(p) | Operand::Move(p)))
                if p.projections.is_empty() && p.local == target_local
        )
}

/// Find a base guard block that SOUNDLY establishes the well-foundedness fact on
/// every recursive-call edge, per guard (3) of the module note. Returns
/// `Some(strict)` — `true` for a `counter >= bound` guard (fact `counter < bound`),
/// `false` for `counter > bound` (fact `counter <= bound`).
///
/// Requires: a `SwitchInt` block `G` whose bool discriminant is defined in `G`
/// as a comparison of the two params expressing the BASE condition
/// `counter >= bound` / `counter > bound` (`classify_bound_comparison`, so the
/// base case is the guard-TRUE / value-1 edge and recursion is the guard-FALSE /
/// value-0 edge); `G` dominates every recursive-call block; and the base
/// (value-1) edge cannot reach any recursive-call block. Fail-closed on any miss.
fn find_dominating_bound_guard_with_dom(
    func: &VerifiableFunction,
    dominators: &Dominators,
    recur_blocks: &[usize],
    counter_local: usize,
    bound_local: usize,
) -> Option<bool> {
    if crate::generate::cached_terminator_presence_for_body(&func.body)
        .is_some_and(|tp| !tp.has_switch_int)
    {
        return None;
    }
    for guard in &func.body.blocks {
        let Terminator::SwitchInt { discr, targets, otherwise, .. } = &guard.terminator else {
            continue;
        };
        let discr_local = match discr {
            Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => p.local,
            _ => continue,
        };
        let Some(strict) =
            classify_bound_comparison(func, guard, discr_local, counter_local, bound_local)
        else {
            continue;
        };
        // `G` must dominate every recursive-call block.
        let dominates_all = recur_blocks.iter().all(|&rb| dominators.dominates(guard.id.0, rb));
        if !dominates_all {
            continue;
        }
        // The base case is the guard-TRUE (value-1) edge; it must not be able to
        // reach a recursive call, otherwise control could arrive at the call with
        // the guard TRUE (`counter >= bound`) and the fact would be unsound.
        let base_tgt = bool_switch_value_target(targets, *otherwise, 1);
        if block_reaches_any_block(func, base_tgt, recur_blocks) {
            continue;
        }
        return Some(strict);
    }
    None
}

/// Classify the bool discriminant defined in `block` (its last whole-local
/// assignment to `discr_local`) as a base guard expressing `counter >= bound`
/// (returns `Some(true)`) or `counter > bound` (`Some(false)`) over bare reads
/// of the two params. The four accepted spellings all place the base case on the
/// guard-TRUE edge and recursion on the guard-FALSE (value-0) edge:
///   `Ge(counter, bound)` / `Le(bound, counter)`  -> strict (`counter < bound`)
///   `Gt(counter, bound)` / `Lt(bound, counter)`  -> non-strict (`counter <= bound`)
/// Any other operator, operand order, or non-bare operand fails closed — in
/// particular an `==`/`!=` guard never matches.
fn classify_bound_comparison(
    func: &VerifiableFunction,
    block: &BasicBlock,
    discr_local: usize,
    counter_local: usize,
    bound_local: usize,
) -> Option<bool> {
    let _ = func;
    let mut cmp: Option<&Rvalue> = None;
    for stmt in block.stmts.iter().rev() {
        if let Statement::Assign { place, rvalue, .. } = stmt
            && place.local == discr_local
            && place.projections.is_empty()
        {
            cmp = Some(rvalue);
            break;
        }
    }
    let Rvalue::BinaryOp(op, lhs, rhs) = cmp? else {
        return None;
    };
    let reads = |operand: &Operand, local: usize| {
        matches!(operand, Operand::Copy(p) | Operand::Move(p)
            if p.projections.is_empty() && p.local == local)
    };
    let counter_then_bound = reads(lhs, counter_local) && reads(rhs, bound_local);
    let bound_then_counter = reads(lhs, bound_local) && reads(rhs, counter_local);
    match op {
        BinOp::Ge if counter_then_bound => Some(true),
        BinOp::Le if bound_then_counter => Some(true),
        BinOp::Gt if counter_then_bound => Some(false),
        BinOp::Lt if bound_then_counter => Some(false),
        _ => None,
    }
}

/// The target of a 2-valued (bool) `SwitchInt` for discriminant `value`: the
/// listed target if present, else `otherwise`.
fn bool_switch_value_target(
    targets: &[(u128, BlockId)],
    otherwise: BlockId,
    value: u128,
) -> BlockId {
    targets.iter().find(|(v, _)| *v == value).map(|(_, b)| *b).unwrap_or(otherwise)
}

/// Forward CFG reachability: `true` if any block in `targets` is reachable from
/// `start` (inclusive) along normal successor edges. Used to prove a base-case
/// edge cannot reach a recursive call.
fn block_reaches_any_block(func: &VerifiableFunction, start: BlockId, targets: &[usize]) -> bool {
    let mut seen: FxHashSet<usize> = FxHashSet::default();
    let mut stack = vec![start.0];
    while let Some(b) = stack.pop() {
        if !seen.insert(b) {
            continue;
        }
        if targets.contains(&b) {
            return true;
        }
        if let Some(block) = block_by_id(&func.body, BlockId(b)) {
            for_each_block_successor(&block.terminator, |succ| {
                stack.push(succ.0);
            });
        }
    }
    false
}

/// Build the per-call recursion VCs for a validated compound `bound - counter`
/// measure. Each VC is UNSAT (Proved) by construction (module note, guard (4)):
/// the strictly-increasing step makes `M_call = bound - (counter + k)` strictly
/// less than `M_entry = bound - counter` (`k >= 1`), and the conjoined
/// well-foundedness fact refutes the `M_entry < 0` disjunct.
///
/// ALL OR NOTHING: one row for EVERY site in `recursive_calls`, or an empty
/// `Vec`. A miss at any one site (its block not found, its counter increment not
/// re-resolved, or an increment `k` that does not fit `i128`) withholds every row,
/// never just that site's. A partial set would be read as "vcgen covered every
/// self call" by the compiler's D9 `termination-unmeasured` exemption
/// (`compiler/rustc_mir_transform/src/trust_verify/termination_unmeasured.rs`),
/// which would then leave the uncovered site uncharged: the silent green D9
/// closes. An empty set leaves the function with no recursion statement, so D9
/// charges every site instead (review F3, 2026-09-27).
fn compound_recursion_vcs(
    func: &VerifiableFunction,
    recursive_calls: &[RecursiveCallSite],
    compound: &CompoundRecursionMeasure,
) -> Vec<VerificationCondition> {
    let bound_name = crate::place_to_var_name(func, &Place::local(compound.bound_local));
    let counter_name = crate::place_to_var_name(func, &Place::local(compound.counter_local));
    let measure_label = format!("{bound_name} - {counter_name}");
    let Some(counter_pos) = compound.counter_local.checked_sub(1) else {
        return Vec::new();
    };
    let bound_var = || Formula::Var(bound_name.clone(), Sort::Int);
    let counter_var = || Formula::Var(counter_name.clone(), Sort::Int);
    // M_entry = bound - counter ; M_call = bound - (counter + k).
    let measure_entry = Formula::Sub(Box::new(bound_var()), Box::new(counter_var()));
    let entry_lt_zero = Formula::Lt(Box::new(measure_entry.clone()), Box::new(Formula::Int(0)));
    // Well-foundedness fact from the dominating base guard (guard (3)).
    let well_founded = if compound.strict {
        Formula::Lt(Box::new(counter_var()), Box::new(bound_var()))
    } else {
        Formula::Le(Box::new(counter_var()), Box::new(bound_var()))
    };
    let exact_preconditions = exact_recursion_preconditions(func);
    let mut vcs = Vec::with_capacity(recursive_calls.len());
    for call in recursive_calls {
        // Every call bound during inference, so a miss below is not expected; if
        // one happens it must not DROP just this site's row (a partial set, see
        // the doc comment): the whole function gets no row.
        let Some(block) = block_by_id(&func.body, call.block) else {
            return Vec::new();
        };
        let Some(k) = call
            .args
            .get(counter_pos)
            .and_then(|arg| resolve_counter_increment(func, block, arg, compound.counter_local))
        else {
            return Vec::new();
        };
        // Reachable in principle: a `u128` counter stepped by `k >= 2^127`.
        let Ok(k_int) = i128::try_from(k) else {
            return Vec::new();
        };
        let counter_call = Formula::Add(Box::new(counter_var()), Box::new(Formula::Int(k_int)));
        let measure_call = Formula::Sub(Box::new(bound_var()), Box::new(counter_call));
        let not_decreasing = Formula::Or(vec![
            Formula::Ge(Box::new(measure_call), Box::new(measure_entry.clone())),
            entry_lt_zero.clone(),
        ]);
        let core = Formula::And(vec![well_founded.clone(), not_decreasing]);
        vcs.push(VerificationCondition {
            kind: VcKind::NonTermination {
                context: RECURSION_TERMINATION_CONTEXT.to_string(),
                measure: measure_label.clone(),
            },
            function: func.name.as_str().into(),
            location: call.span.clone(),
            formula: conjoin_exact_preconditions(&exact_preconditions, core),
            contract_metadata: None,
            // Pre-obligation-record semantics: this producer does not write the
            // authenticated obligation record (None is stripped from the stable
            // content hash — see `stable_model_json`).
            obligation: None,
        });
    }
    vcs
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
    if call_block.id.0 == 0
        || crate::generate::cached_terminator_presence_for_body(&func.body)
            .is_some_and(|tp| !tp.has_assert)
    {
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
    let (pred, op, lhs, rhs) =
        checked_chain_through_assert_pred(func, call_block, tuple_local, &[])?;
    let writes_tuple = call_block
        .stmts
        .iter()
        .any(|stmt| matches!(stmt, Statement::Assign { place, .. } if place.local == tuple_local));
    if writes_tuple {
        return None;
    }
    let chain_buf = [tuple_local, arg_local.unwrap_or(tuple_local)];
    let chain_locals = if arg_local.is_some() { &chain_buf[..2] } else { &chain_buf[..1] };
    if block_has_nonassign_write_risk(call_block, chain_locals) {
        return None;
    }

    Some((checked_op_formula(func, op, lhs, rhs)?, terminator_span(&pred.terminator)))
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
    // PERF-COMPILER-VCGEN-695: if cached terminator presence shows the body has no
    // `Terminator::Assert`, no predecessor can be an assert block. Otherwise resolve
    // the unique predecessor in O(1) via `v2_predecessors` when available.
    if crate::generate::cached_terminator_presence_for_body(&func.body)
        .is_some_and(|tp| !tp.has_assert)
    {
        return None;
    }
    // Guard 2: unique predecessor, and it is the no-overflow Assert on `_T.1`.
    let pred = if let Some(preds_map) = crate::fn_memo::v2_predecessors(func) {
        preds_map.sole_predecessor(func, block.id)?
    } else {
        let mut preds = func
            .body
            .blocks
            .iter()
            .filter(|b| terminator_any_successor(&b.terminator, |s| s == block.id));
        let pred = preds.next()?;
        if preds.next().is_some() {
            return None;
        }
        pred
    };
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
) -> Option<Formula> {
    let l = crate::operand_to_formula(func, lhs);
    let r = crate::operand_to_formula(func, rhs);
    match op {
        BinOp::Add => Some(Formula::Add(Box::new(l), Box::new(r))),
        BinOp::Sub => Some(Formula::Sub(Box::new(l), Box::new(r))),
        BinOp::Mul => Some(Formula::Mul(Box::new(l), Box::new(r))),
        _ => None,
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
    if step_block_id.0 == 0
        || crate::generate::cached_terminator_presence_for_body(&func.body)
            .is_some_and(|tp| !tp.has_assert)
    {
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
    let step_block = block_by_id(&func.body, step_block_id)?;
    let (pred, op, lhs, rhs) =
        checked_chain_through_assert_pred(func, step_block, tuple_local, &[measure_local])?;
    // Loop guard: the Assert-predecessor must be part of THIS loop's body —
    // an outside pred is a once-before-the-loop computation (loop-invariant
    // step), not a per-iteration decrement.
    if !loop_info.body_blocks.contains(&pred.id) {
        return None;
    }
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
    checked_op_formula(func, op, lhs, rhs)
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
    crate::any_local_write_candidate(func, &func.body.blocks, local, |block, item| match item {
        Some(stmt) => {
            // EXHAUSTIVE statement classification (no wildcard) so a new
            // write channel cannot silently bypass this guard.
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    if place.local == local {
                        return true;
                    }
                    match rvalue {
                        Rvalue::Ref { mutable: true, place: p } if p.local == local => true,
                        Rvalue::AddressOf(_, p) if p.local == local => true,
                        _ => false,
                    }
                }
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                    place.local == local
                }
                // Unknown write channels — fail closed.
                Statement::Intrinsic { .. } | Statement::Unsupported { .. } => true,
                // Genuinely non-writing markers.
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::Retag { .. }
                | Statement::PlaceMention(_)
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::Nop => false,
                // `Statement` is #[non_exhaustive]: a future variant is an
                // unknown write channel — fail closed.
                _ => true,
            }
        }
        None => match &block.terminator {
            Terminator::Call { dest, .. } if dest.local == local => true,
            Terminator::Opaque { .. } => true,
            _ => false,
        },
    })
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
    let blocks_sorted = body_blocks.is_sorted_by_key(|b| b.0);
    let in_loop = |id: BlockId| {
        if blocks_sorted {
            body_blocks.binary_search_by_key(&id.0, |b| b.0).is_ok()
        } else {
            body_blocks.contains(&id)
        }
    };
    let mut out = Vec::new();
    crate::visit_local_write_stmts(func, &func.body.blocks, local_idx, |block, stmt| {
        if !in_loop(block.id) {
            return;
        }
        if let Statement::Assign { place, rvalue, .. } = stmt
            && place.local == local_idx
            && place.projections.is_empty()
        {
            out.push((block.id, rvalue));
        }
    });
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

/// Invoke `f` on each successor block ID of `term` without allocating a `Vec`.
#[inline]
fn for_each_block_successor(term: &Terminator, mut f: impl FnMut(BlockId)) {
    match term {
        Terminator::Goto(target) | Terminator::Assert { target, .. } | Terminator::Drop { target, .. } => {
            f(*target);
        }
        Terminator::SwitchInt { targets, otherwise, .. } => {
            for &(_, target) in targets {
                f(target);
            }
            f(*otherwise);
        }
        Terminator::Call { target: Some(target), .. } => {
            f(*target);
        }
        Terminator::Opaque { targets, .. } => {
            for &target in targets {
                f(target);
            }
        }
        Terminator::Return
        | Terminator::Unreachable
        | Terminator::Call { target: None, .. }
        | Terminator::TailCall { .. }
        | _ => {}
    }
}

/// Return `true` if any successor block ID of `term` satisfies `pred`.
#[inline]
fn terminator_any_successor(term: &Terminator, mut pred: impl FnMut(BlockId) -> bool) -> bool {
    match term {
        Terminator::Goto(target) | Terminator::Assert { target, .. } | Terminator::Drop { target, .. } => {
            pred(*target)
        }
        Terminator::SwitchInt { targets, otherwise, .. } => {
            targets.iter().any(|&(_, target)| pred(target)) || pred(*otherwise)
        }
        Terminator::Call { target: Some(target), .. } => pred(*target),
        Terminator::Opaque { targets, .. } => targets.iter().copied().any(pred),
        Terminator::Return
        | Terminator::Unreachable
        | Terminator::Call { target: None, .. }
        | Terminator::TailCall { .. }
        | _ => false,
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
    let body_blocks = &loop_info.body_blocks;
    let blocks_sorted = body_blocks.is_sorted_by_key(|b| b.0);
    let in_loop = |id: BlockId| {
        if blocks_sorted {
            body_blocks.binary_search_by_key(&id.0, |b| b.0).is_ok()
        } else {
            body_blocks.contains(&id)
        }
    };
    for bid in body_blocks {
        let Some(bb) = block_by_id(body, *bid) else {
            continue;
        };
        let mut has_any_succ = false;
        let mut has_exit_succ = false;
        for_each_block_successor(&bb.terminator, |s| {
            has_any_succ = true;
            if !has_exit_succ && !in_loop(s) {
                has_exit_succ = true;
            }
        });
        if !has_any_succ || has_exit_succ {
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
            block_by_id(&func.body, *bid).is_some_and(|bb| {
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
        | Terminator::TailCall { span, .. }
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
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
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
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
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
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
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
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
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
                            callee_identity: None,
                            callee_key: crate::sep_engine::tests::fixture_key("test::factorial"),
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
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
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

    /// The explicit-tail-call form of `recursive_with_decreases`.
    fn recursive_tail_with_decreases() -> VerifiableFunction {
        let mut func = recursive_with_decreases();
        let Terminator::Call {
            func: callee,
            args,
            span,
            atomic,
            is_foreign,
            is_unsafe_sig,
            callee_identity,
            callee_key,
            ..
        } = func.body.blocks[3].terminator.clone()
        else {
            unreachable!();
        };
        func.body.blocks[3].terminator = Terminator::TailCall {
            func: callee,
            args,
            span,
            atomic,
            is_foreign,
            is_unsafe_sig,
            callee_identity,
            callee_key,
        };
        func.body.blocks.truncate(4);
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
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
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
        // Entry dominates everything reachable; each block dominates itself.
        assert!(dom.dominates(0, 0));
        assert!(dom.dominates(1, 1) && dom.dominates(0, 1));
        assert!(dom.dominates(2, 2) && dom.dominates(0, 2));
        // The crux: bb1 must NOT dominate bb2 (bb2 is reachable via bb0 only),
        // which is exactly why bb2 -> bb1 is not a back-edge.
        assert!(!dom.dominates(1, 2), "bb1 must not dominate bb2");
        assert!(!dom.dominates(0, 4) && !dom.dominates(4, 0), "out of range is never a dominator");
    }

    /// The tree answers exactly what the retired dense greatest-fixpoint sets
    /// answered, for every ordered pair of blocks of random CFGs — including
    /// predecessor-less blocks, unreachable cycles no source enters (dominated by
    /// every block), self-loops and back edges into the entry.
    #[test]
    fn termination_dominators_parity() {
        let mut state = 0x2545_f491_4f6c_dd1du64;
        let mut next = |m: u64| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state % m
        };
        let mut pairs = 0usize;
        for _ in 0..300 {
            let n = 1 + next(14) as usize;
            let mut succs: Vec<Vec<usize>> = vec![Vec::new(); n];
            for v in 1..n {
                if next(4) != 0 {
                    succs[next(v as u64) as usize].push(v);
                }
            }
            for _ in 0..next(2 * n as u64 + 1) {
                succs[next(n as u64) as usize].push(next(n as u64) as usize);
            }
            let blocks: Vec<BasicBlock> = (0..n)
                .map(|i| {
                    let terminator = match succs[i].as_slice() {
                        [] => Terminator::Return,
                        [t] => Terminator::Goto(BlockId(*t)),
                        [first, rest @ ..] => Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(0)),
                            targets: rest
                                .iter()
                                .enumerate()
                                .map(|(k, t)| (k as u128, BlockId(*t)))
                                .collect(),
                            otherwise: BlockId(*first),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    };
                    BasicBlock { id: BlockId(i), stmts: vec![], terminator }
                })
                .collect();
            let body = VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::u32(), name: None }],
                blocks,
                arg_count: 0,
                return_ty: Ty::u32(),
                datatype_defs: Default::default(),
            };
            let dense = compute_dominators_dense(&body);
            let tree = compute_dominators(&body);
            for b in 0..n + 1 {
                for a in 0..n + 1 {
                    let want = dense.get(b).is_some_and(|d| d.contains(&a));
                    assert_eq!(
                        tree.dominates(a, b),
                        want,
                        "does {a} dominate {b}? succs {succs:?}"
                    );
                    pairs += 1;
                }
            }
        }
        assert!(pairs > 5_000);
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
    fn exact_direct_self_tail_call_retains_one_nonvacuous_e5_row() {
        let func = recursive_tail_with_decreases();
        crate::validate_function(&func).expect("the structured TailCall must be valid Trust MIR");
        let calls = detect_recursive_calls(&func);
        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].block, BlockId(3));

        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1, "one tail-call site must produce one exact E5 row");
        assert!(matches!(
            &vcs[0].kind,
            VcKind::NonTermination { context, measure }
                if context == "recursion" && measure == "n"
        ));
        assert_ne!(vcs[0].formula, Formula::Bool(false), "a real tail call is not vacuous");
        assert_eq!(vcs[0].location, calls[0].span);
        assert_eq!(
            vcs[0].contract_metadata.and_then(|metadata| metadata.source_contract_index),
            Some(0)
        );
    }

    #[test]
    fn nonself_tail_call_keeps_authored_decreases_fail_closed() {
        let mut func = recursive_tail_with_decreases();
        let Terminator::TailCall { func: callee, .. } = &mut func.body.blocks[3].terminator else {
            unreachable!();
        };
        *callee = "other::rec_cs".to_string();

        assert!(detect_recursive_calls(&func).is_empty());
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1);
        assert!(matches!(
            &vcs[0].kind,
            VcKind::UnsupportedMir { kind, detail }
                if kind == RECURSION_DECREASES_UNSUPPORTED_KIND
                    && detail.contains("non-self call `other::rec_cs`")
        ));
        assert_eq!(vcs[0].formula, Formula::Bool(true));
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
            !is_direct_self_call(&func, BlockId(0), "rec_cs::<u32>"),
            "a bare terminal name must not alias an unrelated exact def-path"
        );
        assert!(is_direct_self_call(&func, BlockId(0), "test::rec_cs::<u32>"));
        assert!(!is_direct_self_call(&func, BlockId(0), "other::rec_cs::<u32>"));
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

    /// Trust (refuted 2026-09-16): a direct self-call beside a non-self call the
    /// compiler did not classify mints NO inferred `termination` row (it may be
    /// mutual recursion through that call); the same body mints its descent row
    /// once the context says the callee is non-reentrant.
    #[test]
    fn inferred_recursion_lane_mints_nothing_beside_an_unclassified_non_self_call() {
        let mut func = recursive_checked_sub_function();
        // bb4 used to `Return`; make it call `test::back` first, then return in bb5.
        func.body.blocks[4].terminator = Terminator::Call {
            unwind: UnwindEdge::Unreachable,
            is_unsafe_sig: false,
            callee_identity: None,
            callee_key: None,
            is_foreign: false,
            func: "test::back".to_string(),
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
        assert_eq!(detect_recursive_calls(&func).len(), 1, "the direct self-call is still seen");

        let count_termination_rows = |vcs: &[VerificationCondition]| {
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::NonTermination { .. })).count()
        };

        // No context: `test::back` is unclassified — no termination claim at all.
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(
            count_termination_rows(&vcs),
            0,
            "an unclassified non-self call withholds the claim"
        );

        // The compiler says `test::back` is a non-reentrant (vanilla sysroot) callee.
        let mut names = trust_types::fx::FxHashSet::default();
        names.insert("test::back".to_string());
        let _scope = crate::enter_vcgen_context(
            &crate::VcgenContext::for_function(func.def_path.clone())
                .with_nonreentrant_callees(names),
        );
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(count_termination_rows(&vcs), 1, "a non-reentrant callee keeps the descent row");
        drop(_scope);

        // A context owned by ANOTHER function stamps nothing (fail-closed).
        let mut names = trust_types::fx::FxHashSet::default();
        names.insert("test::back".to_string());
        let _other = crate::enter_vcgen_context(
            &crate::VcgenContext::for_function("test::someone_else")
                .with_nonreentrant_callees(names),
        );
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(count_termination_rows(&vcs), 0);
    }

    /// Trust (refuted 2026-09-16, round 2): a binding miss at one self-call site
    /// (its block carries a division the measure binder does not model) must
    /// withhold the sibling site's descent row too — the lane mints nothing.
    #[test]
    fn inferred_recursion_lane_mints_nothing_when_any_self_call_site_fails_to_bind() {
        let mut func = recursive_checked_sub_function();
        // bb4 used to `Return`; make it a SECOND self-call site whose block also
        // computes `_5 = _1 / 3`, then return in bb5.
        func.body.locals.push(LocalDecl { index: 5, ty: Ty::u32(), name: None });
        func.body.blocks[4].stmts.push(Statement::Assign {
            place: Place::local(5),
            rvalue: Rvalue::BinaryOp(
                BinOp::Div,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Uint(3, 32)),
            ),
            span: SourceSpan::default(),
        });
        func.body.blocks[4].terminator = Terminator::Call {
            unwind: UnwindEdge::Unreachable,
            is_unsafe_sig: false,
            callee_identity: None,
            callee_key: None,
            is_foreign: false,
            func: "test::rec_cs".to_string(),
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
        assert_eq!(detect_recursive_calls(&func).len(), 2);
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::NonTermination { .. })).count(),
            0,
            "one unbindable site withholds every inferred termination row"
        );
        // Positive control: the same second site WITHOUT the division binds, and
        // both sites mint (the second one is refutable — `n` does not decrease).
        func.body.blocks[4].stmts.clear();
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::NonTermination { .. })).count(),
            2
        );
    }

    /// Trust (D9, 2026-09-27): the ALL-OR-NOTHING contract the compiler's
    /// `assumption:termination-unmeasured` charge reads. Its exemption is "this
    /// lane made a recursion statement for the function" (a recursion row, or the
    /// `RECURSION_DECREASES_UNSUPPORTED_KIND` marker); that is sound only if a
    /// direct-self function never gets a recursion row for SOME of its
    /// `detect_recursive_calls` sites and none for the rest.
    ///
    /// Review F3 (2026-09-27): each fixture states which side of the contract it
    /// is on, so a regression that makes every lane mint nothing fails here too
    /// (`rows == 0` alone would satisfy the contract vacuously). The binding
    /// fixtures must mint one row per site; the declining ones must mint none. The
    /// compound fixture runs under the context the compiler would install (its
    /// `saturating_add` step judged non-reentrant) — without it the topology gate
    /// withholds every row and the compound lane never runs.
    #[test]
    fn inferred_recursion_rows_cover_every_self_call_site_or_none() {
        // `rec_cs` with its `Return` in bb4 replaced by a second self call, the
        // round-2 shape above; `division` puts the unmodeled `_1 / 3` in its block.
        let two_sites = |division: bool| {
            let mut func = recursive_checked_sub_function();
            func.body.locals.push(LocalDecl { index: 5, ty: Ty::u32(), name: None });
            if division {
                func.body.blocks[4].stmts.push(Statement::Assign {
                    place: Place::local(5),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Div,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Uint(3, 32)),
                    ),
                    span: SourceSpan::default(),
                });
            }
            func.body.blocks[4].terminator = Terminator::Call {
                unwind: UnwindEdge::Unreachable,
                is_unsafe_sig: false,
                callee_identity: None,
                callee_key: None,
                is_foreign: false,
                func: "test::rec_cs".to_string(),
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
            func
        };
        // (label, fixture, binds at every site, callees the compiler would judge
        // non-reentrant, the measure label a binding fixture's rows must carry)
        let fixtures: [(&str, VerifiableFunction, bool, &[&str], Option<&str>); 7] = [
            ("checked decrement (binds)", recursive_checked_sub_function(), true, &[], None),
            ("no argument (no measure)", recursive_no_args_function(), false, &[], None),
            ("raw machine decrement (declined)", recursive_function(), false, &[], None),
            ("two sites, one unbindable", two_sites(true), false, &[], None),
            ("two sites, both bind", two_sites(false), true, &[], None),
            ("authored decreases", recursive_with_decreases(), true, &[], Some("n")),
            (
                "compound bound - counter",
                compound_temp_step(),
                true,
                &[SAT_ADD],
                Some("bound - counter"),
            ),
        ];
        for (label, func, binds, nonreentrant, measure_label) in fixtures {
            let sites = detect_recursive_calls(&func).len();
            assert!(sites > 0, "{label}: the fixture must call itself");
            let _scope = (!nonreentrant.is_empty()).then(|| {
                let names: trust_types::fx::FxHashSet<String> =
                    nonreentrant.iter().map(|name| (*name).to_string()).collect();
                crate::enter_vcgen_context(
                    &crate::VcgenContext::for_function(func.def_path.clone())
                        .with_nonreentrant_callees(names),
                )
            });
            let mut vcs = Vec::new();
            check_termination(&func, &mut vcs);
            let recursion_rows: Vec<&VerificationCondition> = vcs
                .iter()
                .filter(|vc| {
                    matches!(&vc.kind, VcKind::NonTermination { context, .. }
                        if context == RECURSION_TERMINATION_CONTEXT)
                })
                .collect();
            let rows = recursion_rows.len();
            let marker = vcs.iter().any(|vc| {
                matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                    if kind == RECURSION_DECREASES_UNSUPPORTED_KIND)
            });
            // The contract itself: never a partial set.
            assert!(
                marker || rows == 0 || rows == sites,
                "{label}: {rows} recursion row(s) for {sites} self-call site(s) is a PARTIAL \
                 termination claim: {vcs:#?}"
            );
            // Which side of it this fixture is on.
            if binds {
                assert!(
                    rows == sites && rows > 0 && !marker,
                    "{label}: a binding fixture must mint one recursion row per self-call site \
                     ({sites}), got {rows} (marker: {marker}): {vcs:#?}"
                );
                if let Some(expected) = measure_label {
                    assert!(
                        recursion_rows.iter().all(|vc| matches!(&vc.kind,
                            VcKind::NonTermination { measure, .. } if measure == expected)),
                        "{label}: every row must carry the measure `{expected}`: {vcs:#?}"
                    );
                }
            } else {
                assert!(
                    rows == 0 && !marker,
                    "{label}: a declining fixture must mint no recursion statement at all (the \
                     compiler's D9 charge covers it), got {rows} row(s) (marker: {marker}): \
                     {vcs:#?}"
                );
            }
        }
    }

    /// Review F3 (2026-09-27): `compound_recursion_vcs` is all-or-nothing. A site
    /// it cannot re-resolve (here: a call site whose block is not in the body)
    /// withholds EVERY row, not just that site's; the complete site set still
    /// mints one row per site.
    #[test]
    fn compound_recursion_vcs_withholds_every_row_on_any_site_miss() {
        let func = compound_temp_step();
        let calls = detect_recursive_calls(&func);
        assert_eq!(calls.len(), 1, "one recursive call: {calls:?}");
        let compound = infer_compound_recursion_measure(&func, &calls)
            .expect("the `bound - counter` measure is inferred for the control");
        assert_eq!(compound_recursion_vcs(&func, &calls, &compound).len(), 1);

        let mut with_miss = calls.clone();
        let mut phantom = calls[0].clone();
        phantom.block = BlockId(99);
        with_miss.push(phantom);
        assert!(
            compound_recursion_vcs(&func, &with_miss, &compound).is_empty(),
            "a miss at one site must withhold the sibling site's row too"
        );

        // The same with the miss FIRST: order does not matter.
        with_miss.reverse();
        assert!(compound_recursion_vcs(&func, &with_miss, &compound).is_empty());
    }

    /// Refuted 2026-09-16: `strip_generics` erased the `<Self as Trait>` qualifier,
    /// so two impls' same-named trait method compared EQUAL and mutual recursion
    /// through them was a "direct self call" — a PROVED descent row on a function
    /// that overflows the stack. Identity keeps the qualifier; only a terminal
    /// turbofish is stripped.
    #[test]
    fn direct_call_identity_keeps_the_qualified_self_and_strips_only_a_turbofish() {
        assert_eq!(direct_call_identity("crate::f::<u32>"), "crate::f");
        assert_eq!(direct_call_identity("crate::f"), "crate::f");
        assert_eq!(
            direct_call_identity("<crate::S as crate::Tr>::f::<u32>"),
            "<crate::S as crate::Tr>::f"
        );
        assert_eq!(
            direct_call_identity("<crate::S as crate::Tr>::f"),
            "<crate::S as crate::Tr>::f"
        );
        assert_ne!(
            direct_call_identity("<crate::U as crate::Tr>::f"),
            direct_call_identity("<crate::S as crate::Tr>::f"),
            "two impls' same-named method are two identities"
        );
        // A nested turbofish is stripped as one balanced group.
        assert_eq!(direct_call_identity("crate::f::<Vec<u32>>"), "crate::f");
        // A dangling `<` never panics and never matches anything else.
        assert_eq!(direct_call_identity("crate::f::<u32"), "crate::f::<u32");
    }

    /// ARGS-FINGERPRINT-READ-1 round 2: a tagged callee is never a self call. The
    /// tag means an argument (a trait method's `Self` included) names a crate whose
    /// rendered name does not identify it, so two impls' methods can render one
    /// qualified path; `direct_call_identity` drops ONE trailing group, and for a
    /// tagged call that group is the tag. The measured exploit shape: the call
    /// `<W<dup_b::T> as Tr>::f` from inside `<W<dup_a::T> as Tr>::f`, both
    /// rendering `<m::W<dupty::T> as m::Tr>::f`.
    #[test]
    fn a_callee_carrying_the_argument_fingerprint_is_never_a_self_call() {
        let tag = trust_types::render_trailing_args_fingerprint(0x452d_e392_92df_0dda, 0xf58d);
        let mut func = recursive_checked_sub_function();
        func.def_path = "<m::W<dupty::T> as m::Tr>::f".to_string();
        assert!(is_direct_self_call(&func, BlockId(0), "<m::W<dupty::T> as m::Tr>::f"));
        assert!(!is_direct_self_call(
            &func,
            BlockId(0),
            &format!("<m::W<dupty::T> as m::Tr>::f{tag}")
        ));
        assert!(!is_direct_self_call(
            &func,
            BlockId(0),
            &format!("<m::W<dupty::T> as m::Tr>::f::<G>{tag}")
        ));
        func.def_path = "m::down".to_string();
        assert!(is_direct_self_call(&func, BlockId(0), "m::down::<T>"));
        assert!(!is_direct_self_call(&func, BlockId(0), &format!("m::down::<T>{tag}")));
        // The identity reader itself keeps the tag (round 3: a verifier marker group
        // is never stripped as a turbofish).
        let tagged = format!("crate::f::<T>{tag}");
        assert_eq!(direct_call_identity(&tagged), tagged);
    }

    /// ARGS-FINGERPRINT-READ-1 round 3: a verifier marker group is identity, not a
    /// turbofish. `::<__trust_alias@…>` is written exactly when a call wears a local
    /// definition key WITHOUT running that definition; stripping it made the call
    /// equal that key again, i.e. a self call of the body it was tagged away from.
    #[test]
    fn direct_call_identity_keeps_a_verifier_marker_group() {
        let alias = "<m::W<k::V> as m::Tr>::get::<__trust_alias@00112233445566778899aabbccddeeff>";
        assert_eq!(direct_call_identity(alias), alias);
        let mut func = recursive_checked_sub_function();
        func.def_path = "<m::W<k::V> as m::Tr>::get".to_string();
        assert!(is_direct_self_call(&func, BlockId(0), "<m::W<k::V> as m::Tr>::get"));
        assert!(!is_direct_self_call(&func, BlockId(0), alias));
        // An ordinary turbofish is still stripped.
        assert_eq!(direct_call_identity("crate::f::<u32>"), "crate::f");
        // Every verifier marker group is kept, the argument fingerprint included.
        let args = "crate::f::<__trust_args@00112233445566778899aabbccddeeff>";
        assert_eq!(direct_call_identity(args), args);
    }

    /// GENERIC-CALL-KEY-ALIAS-1 with ARGS-FINGERPRINT-READ-1 round 4 (2026-10-10):
    /// the extractor now tags a trait call it cannot resolve
    /// (`<W<X> as Tr>::f::<__trust_alias@…>` inside `impl<X> Tr for W<X>`, a
    /// where-clause call that runs this body). Such an alias is a self call exactly
    /// when the compiler's INSTALLED set files its block and its untagged path is
    /// this body's own; no frame, an empty set, another owner's frame, another
    /// base path, a malformed tag or the argument fingerprint keep it a non-self
    /// call. Before the fix the filed frame read no self call, so the inferred lane
    /// minted no descent row and only D9's `skipped` charge remained
    /// (`where_clause_self_call_unique_path.rs` built rc 0 where main refuses it).
    #[test]
    fn an_unresolved_call_alias_of_this_body_is_a_self_call_only_where_the_compiler_files_it() {
        let own = "<m::W<X> as m::Tr>::f";
        let alias = format!("{own}::<__trust_alias@00112233445566778899aabbccddeeff>");
        let mut func = recursive_checked_sub_function();
        func.def_path = own.to_string();
        let mut call_block = None;
        for block in &mut func.body.blocks {
            if let Terminator::Call { func: f, .. } = &mut block.terminator {
                *f = alias.clone();
                call_block = Some(block.id);
            }
        }
        let call_block = call_block.expect("fixture has one call");
        let descent_rows = |func: &VerifiableFunction| {
            let mut vcs = Vec::new();
            check_termination(func, &mut vcs);
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::NonTermination { .. })).count()
        };
        // No compiler frame: the alias stays a non-self call (round 3's rule).
        assert_eq!(detect_recursive_calls(&func).len(), 0);
        assert_eq!(descent_rows(&func), 0);
        // The compiler filed the block: a self call, and the descent row is minted,
        // as for the untagged spelling.
        let filed = crate::VcgenContext::for_function(own.to_string())
            .with_direct_self_call_blocks(Some([call_block.0].into_iter().collect()));
        crate::with_vcgen_context(&filed, || {
            assert_eq!(detect_recursive_calls(&func).len(), 1);
            assert_eq!(descent_rows(&func), 1);
            // Another base path, a malformed tag and the argument fingerprint are
            // never self calls, filed or not.
            let other = "<m::W<Y> as m::Tr>::f::<__trust_alias@00112233445566778899aabbccddeeff>";
            assert!(!is_direct_self_call(&func, call_block, other));
            assert!(!is_direct_self_call(
                &func,
                call_block,
                &format!("{own}::<__trust_alias@0011>")
            ));
            assert!(!is_direct_self_call(
                &func,
                call_block,
                &format!("{own}::<__trust_alias@00112233445566778899aabbccddeefg>")
            ));
            let args = trust_types::render_trailing_args_fingerprint(0x1, 0x23);
            assert!(!is_direct_self_call(&func, call_block, &format!("{own}{args}")));
        });
        // The compiler did not file it: no self call.
        let unfiled = crate::VcgenContext::for_function(own.to_string())
            .with_direct_self_call_blocks(Some(std::collections::BTreeSet::new()));
        crate::with_vcgen_context(&unfiled, || {
            assert_eq!(detect_recursive_calls(&func).len(), 0);
        });
        // Another owner's set never lends a filing.
        let other_owner = crate::VcgenContext::for_function("m::other".to_string())
            .with_direct_self_call_blocks(Some([call_block.0].into_iter().collect()));
        crate::with_vcgen_context(&other_owner, || {
            assert_eq!(detect_recursive_calls(&func).len(), 0);
        });
    }

    /// ARGS-FINGERPRINT-READ-1 round 3: the rendered def path is not an identity.
    /// `impl Tr for W<dup_a::T>` and `impl Tr for W<dup_b::T>` (or `W<other::T>` /
    /// `W<T>` in a Cargo bin+lib pair) render ONE path, and a monomorphic call into
    /// the other impl carries no generic argument to tag. The compiler's
    /// `DefId`-decided self-call blocks are a conjunct: a block it did not file is
    /// never a self call, and the inferred lane then mints no descent row. MEASURED
    /// shape: `chain_ng.rs` (PROVED "recursion measure `n` may not decrease" on the
    /// non-recursive caller, preview3 and round 2).
    #[test]
    fn compiler_self_call_blocks_gate_a_rendered_self_call() {
        let mut func = recursive_checked_sub_function();
        func.def_path = "<m::W<dupty::T> as m::Tr>::f".to_string();
        let mut call_block = None;
        for block in &mut func.body.blocks {
            if let Terminator::Call { func: f, .. } = &mut block.terminator {
                *f = "<m::W<dupty::T> as m::Tr>::f".to_string();
                call_block = Some(block.id);
            }
        }
        let call_block = call_block.expect("fixture has one call");
        let descent_rows = |func: &VerifiableFunction| {
            let mut vcs = Vec::new();
            check_termination(func, &mut vcs);
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::NonTermination { .. })).count()
        };
        // No compiler context: the rendered path decides alone (pre-round-3).
        assert_eq!(detect_recursive_calls(&func).len(), 1);
        assert_eq!(descent_rows(&func), 1);
        // The compiler filed the block as a self call: unchanged.
        let filed = crate::VcgenContext::for_function(func.def_path.clone())
            .with_direct_self_call_blocks(Some([call_block.0].into_iter().collect()));
        crate::with_vcgen_context(&filed, || {
            assert_eq!(detect_recursive_calls(&func).len(), 1);
            assert_eq!(descent_rows(&func), 1);
        });
        // The compiler did NOT file it (the call resolves to the other impl): no
        // self call, no descent row.
        let unfiled = crate::VcgenContext::for_function(func.def_path.clone())
            .with_direct_self_call_blocks(Some(std::collections::BTreeSet::new()));
        crate::with_vcgen_context(&unfiled, || {
            assert_eq!(detect_recursive_calls(&func).len(), 0);
            assert_eq!(descent_rows(&func), 0, "a call into the other impl is not a self call");
        });
        // Another function's set never crosses (owner check).
        let other_owner = crate::VcgenContext::for_function("m::other".to_string())
            .with_direct_self_call_blocks(Some(std::collections::BTreeSet::new()));
        crate::with_vcgen_context(&other_owner, || {
            assert_eq!(detect_recursive_calls(&func).len(), 1);
        });
    }

    /// ARGS-FINGERPRINT-READ-1 round 4: `generate_vcs` pushes a FRESH frame, and
    /// round 3's set did not cross onto it, so every regeneration under the
    /// compiler's frame (the R1 oracle; vcgen-internal regenerations) compared
    /// rendered paths alone. The fresh frame of the SAME owner now inherits the
    /// set; another owner's never crosses.
    #[test]
    fn generate_vcs_fresh_frame_inherits_the_compiler_self_call_blocks() {
        let mut func = recursive_checked_sub_function();
        func.def_path = "<m::W<dupty::T> as m::Tr>::f".to_string();
        for block in &mut func.body.blocks {
            if let Terminator::Call { func: f, .. } = &mut block.terminator {
                *f = "<m::W<dupty::T> as m::Tr>::f".to_string();
            }
        }
        let recursion_rows = |vcs: Vec<VerificationCondition>| {
            vcs.iter()
                .filter(|vc| {
                    matches!(&vc.kind, VcKind::NonTermination { context, .. }
                        if context == RECURSION_TERMINATION_CONTEXT)
                })
                .count()
        };
        // No frame: the rendered path decides alone, and the descent row is minted.
        let unframed = recursion_rows(crate::generate_vcs(&func));
        assert!(unframed > 0, "fixture must mint a recursion row without context");
        // Under the compiler's frame that did NOT file the block, the fresh frame of
        // `generate_vcs` keeps that answer: no self call, no recursion row.
        let unfiled = crate::VcgenContext::for_function(func.def_path.clone())
            .with_direct_self_call_blocks(Some(std::collections::BTreeSet::new()));
        crate::with_vcgen_context(&unfiled, || {
            assert_eq!(recursion_rows(crate::generate_vcs(&func)), 0);
        });
        // Another owner's frame lends nothing.
        let other_owner = crate::VcgenContext::for_function("m::other".to_string())
            .with_direct_self_call_blocks(Some(std::collections::BTreeSet::new()));
        crate::with_vcgen_context(&other_owner, || {
            assert_eq!(recursion_rows(crate::generate_vcs(&func)), unframed);
        });
    }

    /// ARGS-FINGERPRINT-READ-1 round 5 (review of round 3, item iii): the
    /// discharge entry points (`generate_vcs_with_discharge`,
    /// `generate_vcs_with_discharge_and_summaries`) pushed a bare `for_function`
    /// frame through round 4, so under a compiler frame that did NOT file the block
    /// they still minted the descent row from the rendered path alone. Each now inherits
    /// the set from a frame of the same owner, and never from another owner's.
    #[test]
    fn discharge_entry_fresh_frames_inherit_the_compiler_self_call_blocks() {
        let mut func = recursive_checked_sub_function();
        func.def_path = "<m::W<dupty::T> as m::Tr>::f".to_string();
        for block in &mut func.body.blocks {
            if let Terminator::Call { func: f, .. } = &mut block.terminator {
                *f = "<m::W<dupty::T> as m::Tr>::f".to_string();
            }
        }
        let is_recursion_row = |vc: &VerificationCondition| {
            matches!(&vc.kind, VcKind::NonTermination { context, .. }
                if context == RECURSION_TERMINATION_CONTEXT)
        };
        let count = |(solver, pre): (
            Vec<VerificationCondition>,
            Vec<(VerificationCondition, VerificationResult)>,
        )| {
            solver.iter().filter(|vc| is_recursion_row(vc)).count()
                + pre.iter().filter(|(vc, _)| is_recursion_row(vc)).count()
        };
        let summaries = crate::modular::SummaryDatabase::new();
        let plain = || count(crate::generate_vcs_with_discharge(&func));
        let with_summaries =
            || count(crate::generate_vcs_with_discharge_and_summaries(&func, &summaries));
        // No frame: the rendered path decides alone, and both entries mint the row.
        let (plain_unframed, summaries_unframed) = (plain(), with_summaries());
        assert!(plain_unframed > 0, "fixture must mint a recursion row without context");
        assert!(summaries_unframed > 0, "fixture must mint a recursion row without context");
        // Under the owner's frame that did NOT file the block: no self call, no row.
        let unfiled = crate::VcgenContext::for_function(func.def_path.clone())
            .with_direct_self_call_blocks(Some(std::collections::BTreeSet::new()));
        crate::with_vcgen_context(&unfiled, || {
            assert_eq!(plain(), 0, "generate_vcs_with_discharge must inherit the set");
            assert_eq!(
                with_summaries(),
                0,
                "generate_vcs_with_discharge_and_summaries must inherit the set"
            );
        });
        // Another owner's frame lends nothing.
        let other_owner = crate::VcgenContext::for_function("m::other".to_string())
            .with_direct_self_call_blocks(Some(std::collections::BTreeSet::new()));
        crate::with_vcgen_context(&other_owner, || {
            assert_eq!(plain(), plain_unframed);
            assert_eq!(with_summaries(), summaries_unframed);
        });
    }

    /// ARGS-FINGERPRINT-READ-1 round 6 (review of round 5): round 5 also made
    /// `generate_full_assert_refutation_vcs` and the TINV row generator inherit the
    /// self-call set, but no test can fail on that: the set's only reader is
    /// `is_direct_self_call` (through `check_termination`, reached only from
    /// `generate/entry.rs`), and neither path reaches it. This pins the premise of that
    /// statement for the assert-refutation entry: on the fixture whose discharge entries
    /// DO mint a recursion row, it mints none with no frame, so a set has nothing to
    /// withdraw there. (The TINV generator mints only `TinvRowKey`-keyed type-invariant
    /// rows.) If this fails, the inheritance in `generate/assert_refutation.rs` becomes
    /// verdict-bearing and needs a pin like the discharge one above.
    #[test]
    fn full_assert_refutation_entry_mints_no_recursion_row_for_the_set_to_withdraw() {
        let mut func = recursive_checked_sub_function();
        func.def_path = "<m::W<dupty::T> as m::Tr>::f".to_string();
        for block in &mut func.body.blocks {
            if let Terminator::Call { func: f, .. } = &mut block.terminator {
                *f = "<m::W<dupty::T> as m::Tr>::f".to_string();
            }
        }
        let (solver, pre) = crate::generate_vcs_with_discharge(&func);
        let minted = solver
            .iter()
            .chain(pre.iter().map(|(vc, _)| vc))
            .filter(|vc| matches!(&vc.kind, VcKind::NonTermination { .. }))
            .count();
        assert!(minted > 0, "premise: the discharge entry mints a recursion row here");
        let refutation = crate::generate_full_assert_refutation_vcs(&func);
        assert_eq!(
            refutation
                .iter()
                .filter(|vc| matches!(&vc.kind, VcKind::NonTermination { .. }))
                .count(),
            0,
            "the full assert-refutation entry now mints termination rows: pin its set inheritance"
        );
    }

    #[test]
    fn same_named_trait_method_of_another_impl_is_not_a_self_call() {
        let mut func = recursive_checked_sub_function();
        func.def_path = "<test::S as test::Tr>::f".to_string();
        let retarget = |func: &mut VerifiableFunction, callee: &str| {
            for block in &mut func.body.blocks {
                if let Terminator::Call { func: f, .. } = &mut block.terminator {
                    *f = callee.to_string();
                }
            }
        };
        // Positive control: the self call spelled with OUR qualifier is direct and
        // the inferred lane mints its descent row.
        retarget(&mut func, "<test::S as test::Tr>::f");
        assert_eq!(detect_recursive_calls(&func).len(), 1);
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::NonTermination { .. })).count(),
            1
        );
        // The other impl's same-named method is NOT a self call: no recursive edge
        // is recognized, and the lane mints nothing (a non-self call it cannot
        // classify withholds the claim).
        retarget(&mut func, "<test::U as test::Tr>::f");
        assert_eq!(detect_recursive_calls(&func).len(), 0);
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::NonTermination { .. })).count(),
            0,
            "mutual recursion through a name collision must not mint a descent row"
        );
    }

    /// Refuted 2026-09-16: `loop { if n == 0 { return; } f(n - 1); }` proved its
    /// descent and was fully green, and never returns for `n > 0`. A back-edge in a
    /// recursive body withholds the inferred row.
    #[test]
    fn inferred_recursion_lane_mints_nothing_inside_an_enclosing_loop() {
        let mut func = recursive_checked_sub_function();
        // Control first: the loop-free body mints its descent row.
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::NonTermination { .. })).count(),
            1
        );
        // Re-enter the entry block after the self call returns: a natural loop.
        let last = func.body.blocks.len() - 1;
        assert!(matches!(func.body.blocks[last].terminator, Terminator::Return));
        func.body.blocks[last].terminator = Terminator::Goto(BlockId(0));
        assert!(!detect_loops(&func.body).is_empty(), "premise: the body now has a back-edge");
        assert_eq!(detect_recursive_calls(&func).len(), 1, "premise: the self call is unchanged");
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::NonTermination { .. })).count(),
            0,
            "the descent says nothing about the loop's iterations"
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
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
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
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
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
                            callee_identity: None,
                            callee_key: crate::sep_engine::tests::fixture_key("test::spin_rec"),
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
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
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

        let mut compiler_native = func;
        compiler_native.contracts[0].body =
            format!("{}n", crate::contracts::LOWERED_CONTRACT_PREFIX);
        let clauses = extract_decreases_contracts(&compiler_native);
        assert_eq!(clauses.len(), 1);
        assert_eq!(
            clauses[0].measure, "n",
            "the compiler schema marker is provenance, not part of the numeric measure",
        );
        let mut vcs = Vec::new();
        check_termination(&compiler_native, &mut vcs);
        assert!(
            vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::NonTermination { context, measure }
                    if context == "recursion" && measure == "n"
            )),
            "a compiler-native direct-self clause must generate its exact recursion VC: {vcs:#?}",
        );
        assert!(
            !vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::UnsupportedMir { detail, .. }
                    if detail.contains("outside the exact supported fragment")
            )),
            "the schema prefix must not demote a supported parameter measure: {vcs:#?}",
        );
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
                            callee_identity: None,
                            callee_key: crate::sep_engine::tests::fixture_key("test::spin_same"),
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
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
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
                            callee_identity: None,
                            callee_key: crate::sep_engine::tests::fixture_key("test::wrap"),
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
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
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
            Operand::Constant(ConstValue::opaque_scalar(32, false)),
            Operand::unsupported("test", "opaque operand"),
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
        // Targets are bb1 (the `Return` block): a terminator that jumps back to bb0 forms a
        // loop, which the 2026-09-16 enclosing-loop gate rightly reports on a recursive
        // body — the question here is terminator KIND, not CFG shape.
        let known_benign = [
            self_call,
            Terminator::Goto(BlockId(1)),
            Terminator::SwitchInt {
                discr: Operand::Constant(ConstValue::Bool(true)),
                targets: vec![(1, BlockId(1))],
                otherwise: BlockId(1),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
            Terminator::Return,
            Terminator::Assert {
                unwind: trust_types::UnwindEdge::Unreachable,
                cond: Operand::Constant(ConstValue::Bool(true)),
                expected: true,
                msg: AssertMessage::Custom("known benign control edge".to_string()),
                target: BlockId(1),
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
            callee_identity: None,
            callee_key: crate::sep_engine::tests::fixture_key("test::helper"),
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
                    callee_identity: None,
                    callee_key: crate::sep_engine::tests::fixture_key("test::helper"),
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
                            callee_identity: None,
                            callee_key: crate::sep_engine::tests::fixture_key("test::rec_cs"),
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
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
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
                    Terminator::Assert { cond, expected, msg, span, .. } => Terminator::Assert {
                        unwind: trust_types::UnwindEdge::Unreachable,
                        cond,
                        expected,
                        msg,
                        target: BlockId(0),
                        span,
                    },
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
        let or =
            find_ge_or(&vcs[0].formula).expect("non-termination Ge-disjunction must be present");
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
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
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

    // ── the compound `bound - counter` measure: the ENTRY-DEFINITION channel ──
    //
    // `resolve_saturating_add_increment` resolves the operand passed at the COUNTER
    // position and `compound_recursion_vcs` INLINES the `k` it returns as
    // `M_call = bound - (counter + k)`. A wrong `k` is therefore not a lost
    // hypothesis: it is a `NonTermination` VC that is UNSAT for a step that never
    // ran. The channel the hand-rolled block scan could not see is the one that is
    // not in `body.blocks` at all — a `mut` PARAMETER's implicit ENTRY definition.

    /// `fn f(bound, counter[, ...]) ` with `arg_count` params, `locals` many locals
    /// and `blocks` as its whole CFG.
    fn compound_func(
        name: &str,
        arg_count: usize,
        locals: Vec<LocalDecl>,
        blocks: Vec<BasicBlock>,
    ) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{name}"),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals,
                blocks,
                arg_count,
                return_ty: Ty::usize(),
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    fn usize_decl(index: usize, name: &str) -> LocalDecl {
        LocalDecl { index, ty: Ty::usize(), name: Some(name.into()) }
    }

    fn bool_decl(index: usize, name: &str) -> LocalDecl {
        LocalDecl { index, ty: Ty::Bool, name: Some(name.into()) }
    }

    fn call_term(callee: &str, args: Vec<Operand>, dest: usize, target: usize) -> Terminator {
        Terminator::Call {
            func: callee.to_string(),
            args,
            dest: Place::local(dest),
            target: Some(BlockId(target)),
            span: SourceSpan::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            callee_identity: None,
            callee_key: crate::sep_engine::tests::fixture_key(&callee.to_string()),
            unwind: UnwindEdge::Unreachable,
        }
    }

    const SAT_ADD: &str = "core::num::<impl usize>::saturating_add";

    /// `_5 = Ge(counter, bound); switch _5 { 1 => base, _ => other }` — the
    /// dominating base guard `classify_bound_comparison` accepts.
    fn base_guard_block(
        discr: usize,
        counter: usize,
        bound: usize,
        base: usize,
        other: usize,
    ) -> BasicBlock {
        BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(discr),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Ge,
                    Operand::Copy(Place::local(counter)),
                    Operand::Copy(Place::local(bound)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(discr)),
                targets: vec![(1, BlockId(base))],
                otherwise: BlockId(other),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        }
    }

    /// THE CONTROL. `fn cover(bound, counter)` whose counter step is
    /// `counter.saturating_add(1)` into a fresh TEMP `_4` that the call block itself
    /// produces. `_4` is not a parameter, has exactly one definition, and the step
    /// therefore genuinely runs on every path to the recursive call.
    ///
    ///   bb0: _3 = counter >= bound; switch _3 { 1 => bb3, _ => bb1 }
    ///   bb1: _4 = saturating_add(counter, 1) -> bb2
    ///   bb2: _0 = cover(bound, move _4)      -> bb3
    ///   bb3: return
    fn compound_temp_step() -> VerifiableFunction {
        compound_func(
            "cover",
            2,
            vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                usize_decl(1, "bound"),
                usize_decl(2, "counter"),
                bool_decl(3, "guard"),
                usize_decl(4, "step"),
            ],
            vec![
                base_guard_block(3, 2, 1, 3, 1),
                BasicBlock {
                    id: BlockId(1),
                    stmts: Vec::new(),
                    terminator: call_term(
                        SAT_ADD,
                        vec![
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Uint(1, 64)),
                        ],
                        4,
                        2,
                    ),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: Vec::new(),
                    terminator: call_term(
                        "test::cover",
                        vec![Operand::Copy(Place::local(1)), Operand::Move(Place::local(4))],
                        0,
                        3,
                    ),
                },
                BasicBlock { id: BlockId(3), stmts: Vec::new(), terminator: Terminator::Return },
            ],
        )
    }

    /// THE WITNESS. `fn bad(bound, counter, mut step, c)` — identical except that the
    /// saturating call's destination is the `mut` PARAMETER `_3`, and the store sits
    /// behind `c`. On `c == false` control reaches the recursive call with `_3` still
    /// holding its CALLER-CHOSEN ENTRY value, so no increment happened; `bad(5,0,0,false)`
    /// recurses forever. The entry definition is not in `body.blocks`, so an
    /// `Assign`+`Call`-dest scan of the blocks sees exactly one definition of `_3` and
    /// reports the step.
    ///
    ///   bb0: _5 = counter >= bound; switch _5 { 1 => bb4, _ => bb1 }
    ///   bb1: switch c { 1 => bb2, _ => bb3 }
    ///   bb2: _3 = saturating_add(counter, 1)      -> bb3      (SKIPPED when !c)
    ///   bb3: _0 = bad(bound, move _3, copy _3, c) -> bb4
    ///   bb4: return
    fn compound_mut_param_step() -> VerifiableFunction {
        compound_func(
            "bad",
            4,
            vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                usize_decl(1, "bound"),
                usize_decl(2, "counter"),
                usize_decl(3, "step"),
                bool_decl(4, "c"),
                bool_decl(5, "guard"),
            ],
            vec![
                base_guard_block(5, 2, 1, 4, 1),
                BasicBlock {
                    id: BlockId(1),
                    stmts: Vec::new(),
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(4)),
                        targets: vec![(1, BlockId(2))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: Vec::new(),
                    terminator: call_term(
                        SAT_ADD,
                        vec![
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Uint(1, 64)),
                        ],
                        3,
                        3,
                    ),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: Vec::new(),
                    terminator: call_term(
                        "test::bad",
                        vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Move(Place::local(3)),
                            Operand::Copy(Place::local(3)),
                            Operand::Copy(Place::local(4)),
                        ],
                        0,
                        4,
                    ),
                },
                BasicBlock { id: BlockId(4), stmts: Vec::new(), terminator: Terminator::Return },
            ],
        )
    }

    /// The control still resolves: the fix must not cost the lane its intended shape.
    #[test]
    fn a_fresh_temp_saturating_step_still_resolves_and_still_proves() {
        let func = compound_temp_step();
        assert_eq!(
            resolve_saturating_add_increment(&func, &Operand::Move(Place::local(4)), 2),
            Some(1),
            "a non-parameter temp with one defining call is single-valued"
        );
        let calls = detect_recursive_calls(&func);
        assert_eq!(calls.len(), 1, "one recursive call: {calls:?}");
        let compound = infer_compound_recursion_measure(&func, &calls)
            .expect("the `bound - counter` measure must still be inferred");
        assert_eq!((compound.bound_local, compound.counter_local, compound.strict), (1, 2, true));
        assert_eq!(compound_recursion_vcs(&func, &calls, &compound).len(), 1);
    }

    /// THE ROW. A `mut` parameter's ENTRY definition is not in `body.blocks`, so the
    /// call in `bb2` is its SECOND value, not its only one. `local_defs` counts the
    /// entry definition; the increment must not be reported.
    #[test]
    fn a_mut_parameter_counter_argument_reports_no_increment() {
        let func = compound_mut_param_step();
        assert!(
            crate::local_defs::is_parameter(&func, 3),
            "the witness is about a PARAMETER destination"
        );
        assert_eq!(
            crate::local_defs::value_count(&func, 3),
            trust_types::ValueCount::Exactly(2),
            "entry definition + the saturating call"
        );
        assert_eq!(
            crate::local_defs::unique_value_call(&func, 3).map(|_| ()),
            None,
            "a two-valued local has no unique defining call"
        );
        assert_eq!(
            resolve_saturating_add_increment(&func, &Operand::Move(Place::local(3)), 2),
            None,
            "the entry value reaches the call on the !c path — no increment happened"
        );
    }

    /// End to end: the phantom increment was the ONLY thing licensing the compound
    /// measure for this body, so no `bound - counter` measure is inferred and no
    /// termination VC is minted for a recursion that does not terminate.
    #[test]
    fn the_mut_parameter_witness_mints_no_compound_termination_vc() {
        let func = compound_mut_param_step();
        let calls = detect_recursive_calls(&func);
        assert_eq!(calls.len(), 1, "one recursive call: {calls:?}");
        assert!(
            infer_compound_recursion_measure(&func, &calls).is_none(),
            "a step that need not run cannot license the compound measure"
        );
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert!(
            !vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::NonTermination { context, measure }
                    if context == "recursion" && measure.contains('-')
            )),
            "no compound-measure recursion VC may be minted: {vcs:?}"
        );
    }

    /// The `bound`-invariance half of the same class: `operand_reads_unchanged_local`
    /// hops through a local whose ONE value is `Use(bound)`. A `mut` PARAMETER with
    /// that single body store still carries its entry value on a path that skips it,
    /// so the hop must be refused there and allowed through a fresh temp.
    #[test]
    fn the_bound_invariance_hop_refuses_a_mut_parameter_and_allows_a_temp() {
        let copy_bound = Rvalue::Use(Operand::Copy(Place::local(1)));
        let mut func = compound_temp_step();
        // Through the TEMP `_4`: one whole definition, no entry definition.
        func.body.blocks[1].stmts.push(Statement::Assign {
            place: Place::local(4),
            rvalue: copy_bound.clone(),
            span: SourceSpan::default(),
        });
        func.body.blocks[1].terminator = Terminator::Goto(BlockId(2));
        assert!(
            operand_reads_unchanged_local(&func, &Operand::Move(Place::local(4)), 1),
            "a temp whose sole value is `Use(bound)` denotes bound"
        );
        // Through the `mut` PARAMETER `_3` of the witness body: the same single store,
        // plus the entry definition no block scan can see.
        let mut param = compound_mut_param_step();
        param.body.blocks[2].stmts.push(Statement::Assign {
            place: Place::local(3),
            rvalue: copy_bound,
            span: SourceSpan::default(),
        });
        param.body.blocks[2].terminator = Terminator::Goto(BlockId(3));
        assert!(
            !operand_reads_unchanged_local(&param, &Operand::Move(Place::local(3)), 1),
            "a parameter's entry value is a second value the store does not replace"
        );
    }

    /// THE CAPTURED BODY, not a synthetic one. `-Ztrust-dump=mir` of
    ///
    /// ```ignore (illustrative)
    /// #[inline(never)]
    /// pub fn bad(bound: usize, counter: usize, mut step: usize, c: bool) -> usize {
    ///     if counter >= bound { return 0; }
    ///     if c { step = counter.saturating_add(1); }
    ///     bad(bound, step, 0, c)
    /// }
    /// ```
    ///
    /// compiled `-Copt-level=1 -Cpanic=abort -Ztrust-policy=certify` by a trustc built
    /// at the base of this change. `optimized_mir` puts the saturating call's
    /// destination directly on the `mut` PARAMETER `_3` (bb3) and passes `move _3` bare
    /// at the counter position of the self-call (bb5) — so this is what the verifier
    /// actually sees, not what a fixture author imagines it sees.
    const MIR_BAD_MUT_PARAM_STEP: &str = r#"{"name":"bad","def_path":"v2::bad","span":{"file":"v2.rs","line_start":2,"col_start":0,"line_end":6,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":1,"ty":{"Int":{"width":64,"signed":false}},"name":"bound"},{"index":2,"ty":{"Int":{"width":64,"signed":false}},"name":"counter"},{"index":3,"ty":{"Int":{"width":64,"signed":false}},"name":"step"},{"index":4,"ty":"Bool","name":"c"},{"index":5,"ty":"Bool","name":null}],"blocks":[{"id":0,"stmts":[{"StorageLive":5},{"Assign":{"place":{"local":5,"projections":[]},"rvalue":{"BinaryOp":["Ge",{"Copy":{"local":2,"projections":[]}},{"Copy":{"local":1,"projections":[]}}]},"span":{"file":"v2.rs","line_start":3,"col_start":7,"line_end":3,"col_end":23}}}],"terminator":{"SwitchInt":{"discr":{"Move":{"local":5,"projections":[]}},"targets":[[0,2]],"otherwise":1,"exhaustive_enum_unreachable":false,"span":{"file":"v2.rs","line_start":3,"col_start":7,"line_end":3,"col_end":23}}}},{"id":1,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,64]}}},"span":{"file":"v2.rs","line_start":3,"col_start":33,"line_end":3,"col_end":34}}},{"StorageDead":5}],"terminator":{"Goto":7}},{"id":2,"stmts":[{"StorageDead":5}],"terminator":{"SwitchInt":{"discr":{"Copy":{"local":4,"projections":[]}},"targets":[[0,5]],"otherwise":3,"exhaustive_enum_unreachable":false,"span":{"file":"v2.rs","line_start":4,"col_start":7,"line_end":4,"col_end":8}}}},{"id":3,"stmts":[],"terminator":{"Call":{"func":"core::num::<impl usize>::saturating_add","args":[{"Move":{"local":2,"projections":[]}},{"Constant":{"Uint":[1,64]}}],"dest":{"local":3,"projections":[]},"target":4,"span":{"file":"v2.rs","line_start":4,"col_start":18,"line_end":4,"col_end":43},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"callee_identity":{"stable_crate_id":14915136950559021302,"def_index":28215,"substs_digest":[14241860155052752853,2268345107747320411]}}}},{"id":4,"stmts":[],"terminator":{"Goto":5}},{"id":5,"stmts":[],"terminator":{"Call":{"func":"v2::bad","args":[{"Move":{"local":1,"projections":[]}},{"Move":{"local":3,"projections":[]}},{"Constant":{"Uint":[0,64]}},{"Move":{"local":4,"projections":[]}}],"dest":{"local":0,"projections":[]},"target":6,"span":{"file":"v2.rs","line_start":5,"col_start":4,"line_end":5,"col_end":26},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"callee_identity":{"stable_crate_id":4708491588023007029,"def_index":3,"substs_digest":[14241860155052752853,2268345107747320411]}}}},{"id":6,"stmts":[],"terminator":{"Goto":7}},{"id":7,"stmts":[],"terminator":"Return"}],"arg_count":4,"return_ty":{"Int":{"width":64,"signed":false}}},"contracts":[],"preconditions":[{"And":[{"Ge":[{"Var":["bound","Int"]},{"Int":0}]},{"Le":[{"Var":["bound","Int"]},{"Int":18446744073709551615}]}]},{"And":[{"Ge":[{"Var":["counter","Int"]},{"Int":0}]},{"Le":[{"Var":["counter","Int"]},{"Int":18446744073709551615}]}]},{"And":[{"Ge":[{"Var":["step","Int"]},{"Int":0}]},{"Le":[{"Var":["step","Int"]},{"Int":18446744073709551615}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

    /// The captured body agrees with the synthetic fixture above, and the resolver
    /// declines it: the phantom increment is refused on the REAL extracted MIR.
    ///
    /// RUNTIME ORACLE (stock rustc, `-Copt-level=1`): `bad(5, 0, 0, false)` skips the
    /// store, so `step` is still the caller's `0` at the call and the recursion is
    /// `bad(5, 0, 0, false)` forever — it does not terminate.
    #[test]
    fn the_captured_optimized_mir_of_the_witness_reports_no_increment() {
        let func: VerifiableFunction =
            serde_json::from_str(MIR_BAD_MUT_PARAM_STEP).expect("captured body must deserialize");
        assert_eq!(func.body.arg_count, 4);
        assert!(crate::local_defs::is_parameter(&func, 3), "`step` is a parameter");
        assert_eq!(
            crate::local_defs::value_count(&func, 3),
            trust_types::ValueCount::Exactly(2),
            "entry definition + the saturating call destination"
        );
        assert_eq!(
            resolve_saturating_add_increment(&func, &Operand::Move(Place::local(3)), 2),
            None,
            "the entry value reaches the self-call on the !c path"
        );
        let calls = detect_recursive_calls(&func);
        assert_eq!(calls.len(), 1, "one self-call: {calls:?}");
        assert!(
            infer_compound_recursion_measure(&func, &calls).is_none(),
            "no `bound - counter` measure may be inferred for a step that need not run"
        );
    }
}

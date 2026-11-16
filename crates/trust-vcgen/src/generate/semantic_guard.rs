// The semantic guard map: for each block, the path condition established by
// the switches that dominate it. Everything downstream that says "this fact
// only holds on this path" reads this map. The work ceilings bound the
// fixpoint on large bodies -- exceeding them degrades to no guard, never to a
// wrong one.

use super::*;

/// Whether a canonical `len()` call has the `isize::MAX` result bound.
/// `str`/`String` count bytes; a slice counts elements and therefore needs a
/// receiver whose extracted element type is provably non-ZST. `Vec<T>` stays
/// excluded because the verifier's current container type may erase `T`.
pub(super) fn len_call_result_has_isize_bound(
    func: &VerifiableFunction,
    callee: &str,
    args: &[Operand],
) -> bool {
    if args.len() != 1 {
        return false;
    }
    if trust_types::total_call_summaries::total_summary_len_bound(callee) {
        return true;
    }
    if !trust_types::total_call_summaries::total_summary_slice_len_call(callee) {
        return false;
    }
    let Some(receiver_ty) = crate::operand_ty_cow(func, &args[0]) else {
        return false;
    };
    let mut receiver_ty = receiver_ty.as_ref();
    while let Ty::Ref { inner, .. } = receiver_ty {
        receiver_ty = inner;
    }
    matches!(receiver_ty, Ty::Slice { elem } if trust_types::alloc_model::ty_is_definitely_nonzero_sized(elem))
}

pub(super) fn has_intrinsic_unsafe_surface(func: &VerifiableFunction) -> bool {
    if func.body.locals.iter().any(|local| ty_contains_raw_ptr(&local.ty)) {
        return true;
    }

    for block in &func.body.blocks {
        for stmt in &block.stmts {
            // The modeled `copy_nonoverlapping` statement reads and writes raw
            // memory, so it IS an intrinsic unsafe surface. Its src/dst are
            // normally raw-pointer LOCALS (caught by the `ty_contains_raw_ptr`
            // scan above), but gate on the statement itself so a body whose
            // pointer operands are not locals still reaches the sep engine —
            // this gate guards the ONLY lane that mints the copy's
            // bounds/overlap obligations (see `SepEngine::interpret_statement`).
            if let Statement::CopyNonOverlapping { .. } = stmt {
                return true;
            }
            let Statement::Assign { place, rvalue, .. } = stmt else {
                continue;
            };
            if crate::place_has_raw_deref(func, place) {
                return true;
            }
            match rvalue {
                Rvalue::Use(operand) if crate::operand_has_raw_deref(func, operand) => {
                    return true;
                }
                Rvalue::Ref { place, .. } | Rvalue::CopyForDeref(place)
                    if crate::place_has_raw_deref(func, place) =>
                {
                    return true;
                }
                Rvalue::AddressOf(_, _) => return true,
                _ => {}
            }
        }

        // T5A: `is_unsafe_sig` (rustc fn-signature safety, recorded at
        // extraction) must open this gate, or an unsafe-sig call with a name
        // the heuristic list misses (e.g. a local `unsafe fn danger()`) never
        // reaches `check_unsafe` and its missing-SAFETY demand silently never
        // fires. `is_foreign` is deliberately NOT keyed here: foreign calls are
        // handled fail-closed by the dedicated FFI lane (`is_foreign ||
        // is_extern_call` below), and opening the doc-lint gate for every libc
        // call would ADD demands — the opposite of this over-refutation fix.
        let unsafe_call = match &block.terminator {
            Terminator::Call { func, is_unsafe_sig, .. }
            | Terminator::TailCall { func, is_unsafe_sig, .. } => Some((func, *is_unsafe_sig)),
            _ => None,
        };
        if let Some((callee, is_unsafe_sig)) = unsafe_call
            && (is_unsafe_sig || crate::unsafe_verify::detection::is_unsafe_fn_call(callee))
        {
            return true;
        }
    }

    false
}

pub(super) fn ty_contains_raw_ptr(ty: &Ty) -> bool {
    match ty {
        Ty::RawPtr { .. } => true,
        Ty::Ref { inner, .. } => ty_contains_raw_ptr(inner),
        // Trust: piece #7a — a const-generic array must descend into its element
        // exactly like a concrete `[T; N]`. SOUNDNESS-CRITICAL: this classifier
        // drives conservative (havoc) handling; NOT descending would answer
        // "no raw pointer" for a `[*mut T; N]` and could drop a needed havoc.
        Ty::Slice { elem } | Ty::Array { elem, .. } | Ty::SymArray { elem, .. } => {
            ty_contains_raw_ptr(elem)
        }
        _ => false,
    }
}

/// verifier-perf: true iff `func` is too large/aggregate-heavy for the
/// statement-versioning + path-guard machinery to run in bounded time, measured
/// as the per-block work sum `Σ_b stmts_b × max(agg_operands_b, 1)` (see
/// `MAX_SEMANTIC_GUARD_WORK` for why per-block, not the old global triple
/// product). The kernel's recursive `Expr`/`ExprKind`/`Name` clusters lower to
/// deeply-nested `Ty::Adt`, and a `Debug`/`Clone`/builder over such a type (the
/// `def_eq`/`inductive_builder`/`fmt`/`clone` cluster) packs HUNDREDS of
/// thousands of datatype-field aggregate operands into few blocks; the per-block
/// sum for that shape is within a small factor of the old product, so it still
/// blows past the budget — the shapes the gate exists for keep gating, while a
/// many-small-blocks builder (each block's local product tiny) no longer does
/// (`reports/vcgen-budget-cost-model-2026-07-06.md`). An over-budget function
/// takes the UNVERSIONED, no-path-guard baseline instead.
///
/// SOUNDNESS: DROP-ONLY. Every consumer of this gate (the semantic-guard map, the
/// statement-version oracle) supplies ONLY extra hypotheses (path/dataflow facts,
/// finer SSA versions) that STRENGTHEN a PROVE. Skipping them can only weaken a
/// PROVE to a FAIL/Unknown, never turn a FAIL into a PROVE — the module's own
/// invariant ("Dropping a fact is always sound"). Symmetrically, UN-gating a
/// function is also sound: it only re-adds obligations/hypotheses through the
/// normal lanes, and the dynamic `gen_work` meter (lib.rs
/// `MAX_GENERATION_WORK_BUDGET`) remains the runtime backstop against a shape
/// this static estimate under-counts. The fixed budget sits far above any
/// ordinary function. It is deterministic because changing the threshold
/// changes which fail-closed obligations are generated; ambient process state
/// therefore must not alter it.
pub(crate) fn func_exceeds_vcgen_budget(func: &VerifiableFunction) -> bool {
    let trace = {
        static TRACE_BUDGET: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        *TRACE_BUDGET.get_or_init(|| crate::trust_vcgen_env_var_present("TRUST_VCGEN_TRACE_BUDGET"))
    };
    if !trace {
        let addr = std::ptr::from_ref(&func.body) as usize;
        if let Some(hit) = super::FUNC_ANALYSIS_MEMO.with(|memo| {
            memo.borrow()
                .iter()
                .rev()
                .find(|frame| frame.body_addr == addr)
                .and_then(|frame| frame.exceeds_vcgen_budget)
        }) {
            return hit;
        }
        let over = func_exceeds_vcgen_budget_uncached(func, false);
        super::FUNC_ANALYSIS_MEMO.with(|memo| {
            if let Some(frame) = memo
                .borrow_mut()
                .iter_mut()
                .rev()
                .find(|frame| frame.body_addr == addr)
            {
                frame.exceeds_vcgen_budget = Some(over);
            }
        });
        return over;
    }
    func_exceeds_vcgen_budget_uncached(func, true)
}

fn func_exceeds_vcgen_budget_uncached(func: &VerifiableFunction, trace: bool) -> bool {
    // Per-block product SUM, not a global triple product. (The versioning
    // oracle's query cost, which this model was first fitted to, is O(log) since
    // WS-E; what the caps still bound is the guard BFS's accumulated path facts —
    // see `MAX_SEMANTIC_GUARD_WORK`.) The true shape is Σ_b stmts_b × ops_b — the
    // global product over-estimated a many-small-blocks builder (aterm-spec's
    // ty_model! constructors: ~220 blocks × ~5 stmts × ~3 operands ≈ 3k real
    // work) by 500-2000×, fail-closing 73 functions that the CHC/PDR lane
    // proves outright (reports/vcgen-budget-cost-model-2026-07-06.md). The
    // kernel witnesses the cap exists for score essentially the SAME either
    // way (one block, hundreds of thousands of aggregate operands, so the
    // per-block sum ≈ the old product), and the absolute block/stmt caps plus
    // the dynamic gen_work meter (lib.rs MAX_GENERATION_WORK_BUDGET) remain
    // the backstops.
    let over_blocks = func.body.blocks.len() > MAX_SEMANTIC_GUARD_BLOCKS;
    if over_blocks && !trace {
        return true;
    }
    let mut total_stmts = 0usize;
    let mut total_agg_operands = 0usize;
    let mut work = 0usize;
    for b in &func.body.blocks {
        let stmts_len = b.stmts.len();
        total_stmts += stmts_len;
        if total_stmts > MAX_SEMANTIC_GUARD_STMTS && !trace {
            return true;
        }
        let ops: usize = b
            .stmts
            .iter()
            .map(|s| match s {
                Statement::Assign { rvalue: Rvalue::Aggregate(_, operands), .. } => operands.len(),
                _ => 0,
            })
            .sum();
        total_agg_operands += ops;
        work = work.saturating_add(stmts_len.saturating_mul(ops.max(1)));
        if work > MAX_SEMANTIC_GUARD_WORK && !trace {
            return true;
        }
    }
    let over =
        over_blocks || total_stmts > MAX_SEMANTIC_GUARD_STMTS || work > MAX_SEMANTIC_GUARD_WORK;
    if over && trace {
        eprintln!(
            "[VCGEN_BUDGET] gated {} blocks={} stmts={} agg_operands={} work={}",
            func.name,
            func.body.blocks.len(),
            total_stmts,
            total_agg_operands,
            work,
        );
    }
    over
}

/// The (sound, always-true) result bounds for an integer `Ord::min`/`max`/`clamp`
/// call, bound to `dest_var` (the caller passes the appropriate return-slot / call-dest
/// name for the call's `dest`). Returns empty for a non-min/max/clamp callee, the
/// wrong arity, or a `Self` that is not a primitive integer
/// (`call_facts::primitive_int_ord_method`, NAME-ANCHOR-2: a user `Ord` impl may
/// override `min`/`max`/`clamp`, so std's trait path alone does not name the body
/// that runs). This is the
/// SINGLE definition of the min/max/clamp result semantics, reused by BOTH:
///   * the `build_semantic_guard_map` call-dest arm — `dest_var` is the
///     `place_to_var_name` alias of the Call dest (`__ret` for the return slot); and
///   * the postcondition-lane return-slot pin — `dest_var` is the RAW `_0` the
///     `#[ensures]` clause reads (the call-dest alias `__ret` does NOT reach `_0` in
///     that lane, identical to the saturating/wrapping_neg return pins).
///
/// SOUNDNESS: `min(a,b) <= a,b` and `max(a,b) >= a,b` hold UNCONDITIONALLY (integer
/// `Ord`; `as Ord>` excludes floats, whose NaN breaks `<=`). `clamp(x,lo,hi)` PANICS
/// when `lo > hi`, so `lo <= result <= hi` holds ONLY on the non-panicking `lo <= hi`
/// path — emitted as the GUARDED fact `(lo <= hi) -> (lo <= result <= hi)` (vacuous, i.e.
/// no constraint, when `lo > hi`, so a clamp that panics is never false-proved), and
/// UNCONDITIONALLY only for a CONSTANT `lo <= hi` (which cannot panic — matching the
/// call-dest arm's `sr_clamp_index_safe` completeness carve-out). The caller is
/// responsible for the SSA gate on `dest_var` (a `&mut`-reassigned dest would go stale).
pub(super) fn ord_min_max_clamp_result_facts(
    func: &VerifiableFunction,
    callee: &str,
    args: &[Operand],
    dest: &Place,
    dest_var: &Formula,
) -> Vec<Formula> {
    let method = primitive_int_ord_method(func, callee, args, dest);
    ord_min_max_clamp_result_facts_for_method(func, method, args, dest_var)
}

fn ord_min_max_clamp_result_facts_for_method(
    func: &VerifiableFunction,
    method: Option<&str>,
    args: &[Operand],
    dest_var: &Formula,
) -> Vec<Formula> {
    let mut facts = Vec::new();
    if method == Some("min") && args.len() == 2 {
        // min(a, b) <= a  AND  min(a, b) <= b
        for arg in args {
            facts.push(Formula::Le(
                Box::new(dest_var.clone()),
                Box::new(crate::operand_to_formula(func, arg)),
            ));
        }
    } else if method == Some("max") && args.len() == 2 {
        // max(a, b) >= a  AND  max(a, b) >= b
        for arg in args {
            facts.push(Formula::Ge(
                Box::new(dest_var.clone()),
                Box::new(crate::operand_to_formula(func, arg)),
            ));
        }
    } else if method == Some("clamp") && args.len() == 3 {
        // GUARDED `(lo <= hi) -> (lo <= result <= hi)` — see the function-level
        // soundness note (clamp PANICS when `lo > hi`). Emitted unconditionally only
        // for a CONSTANT `lo <= hi` (cannot panic; ay does not fold a constant
        // `Gt(lo,hi)` so the disjunctive form would never discharge).
        let lo = crate::operand_to_formula(func, &args[1]);
        let hi = crate::operand_to_formula(func, &args[2]);
        let fact = match (operand_const_int(&args[1]), operand_const_int(&args[2])) {
            (Some(l), Some(h)) if l <= h => Formula::And(vec![
                Formula::Ge(Box::new(dest_var.clone()), Box::new(lo)),
                Formula::Le(Box::new(dest_var.clone()), Box::new(hi)),
            ]),
            _ => {
                let bound = Formula::And(vec![
                    Formula::Ge(Box::new(dest_var.clone()), Box::new(lo.clone())),
                    Formula::Le(Box::new(dest_var.clone()), Box::new(hi.clone())),
                ]);
                Formula::Or(vec![Formula::Gt(Box::new(lo), Box::new(hi)), bound])
            }
        };
        facts.push(fact);
    }
    facts
}

/// The byte size the Rust language fixes for a PRIMITIVE type name, independent
/// of target. `usize`/`isize`/pointers are deliberately absent: their size is
/// target-dependent, and this function has no target to consult.
///
/// The names are the ones `trust-mir-extract` writes into the callee path's
/// turbofish (`core::mem::size_of::<u64>`), i.e. the type as the input program
/// declared it — the same authority class as a `u8` parameter's `[0, 255]`.
fn primitive_type_size_bytes(ty_name: &str) -> Option<i128> {
    Some(match ty_name {
        "u8" | "i8" | "bool" => 1,
        "u16" | "i16" => 2,
        "u32" | "i32" | "f32" | "char" => 4,
        "u64" | "i64" | "f64" => 8,
        "u128" | "i128" => 16,
        _ => return None,
    })
}

/// The `T` of a `core::mem::NAME::<T>` / `std::mem::NAME::<T>` callee path, or
/// `None` for any other spelling. An EXACT path match (never a substring or a
/// suffix test) so a user function called `size_of` in a module named `mem`
/// cannot be credited with `core::mem::size_of`'s semantics.
fn mem_layout_query_arg<'a>(callee: &'a str, name: &str) -> Option<&'a str> {
    let rest = callee
        .strip_prefix("core::mem::")
        .or_else(|| callee.strip_prefix("std::mem::"))?
        .strip_prefix(name)?
        .strip_prefix("::<")?;
    rest.strip_suffix('>')
}

/// The layout facts for a `mem::size_of::<T>()` / `mem::align_of::<T>()` call at
/// a primitive `T`, bound to `dest_var`. Empty for any other callee, and for any
/// `T` whose layout is not language-fixed.
///
/// * `size_of::<T>()` is CONST-FOLDED to its exact value. For the primitives in
///   [`primitive_type_size_bytes`] that value is fixed by the language (`u64` is
///   64 bits on every target), so the equation is a fact about the type the
///   input program wrote — not an assumption about libcore's implementation.
/// * `align_of::<T>()` is NOT folded: the alignment of `u64`/`f64`/`u128` is
///   target-dependent (4 on x86-32, 8 on aarch64), and this lane has no target.
///   What IS target-independent is `1 <= align_of::<T>()` (alignment is always a
///   positive power of two) and `align_of::<T>() <= size_of::<T>()`, which
///   follows from `size_of::<T>()` being a nonzero multiple of `align_of::<T>()`
///   for these non-ZST primitives. Those two bounds are what make an
///   `align_of`-divisor obligation and an `align_of`-index obligation decidable.
fn mem_layout_call_dest_facts(
    callee: &str,
    dest_var_of: impl FnOnce() -> Formula,
) -> Vec<Formula> {
    if let Some(ty_name) = mem_layout_query_arg(callee, "size_of")
        && let Some(size) = primitive_type_size_bytes(ty_name)
    {
        return vec![Formula::Eq(Box::new(dest_var_of()), Box::new(Formula::Int(size)))];
    }
    if let Some(ty_name) = mem_layout_query_arg(callee, "align_of")
        && let Some(size) = primitive_type_size_bytes(ty_name)
    {
        let dest_var = dest_var_of();
        return vec![
            Formula::Ge(Box::new(dest_var.clone()), Box::new(Formula::Int(1))),
            Formula::Le(Box::new(dest_var), Box::new(Formula::Int(size))),
        ];
    }
    Vec::new()
}

pub(crate) fn build_semantic_guard_map(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    build_semantic_guard_map_impl(func, None)
}

/// Summary-aware variant of [`build_semantic_guard_map`]: in addition to the
/// stdlib total-call dest facts, it threads each *proved* callee's postcondition
/// as an ASSUMED conjunct, rebound to the call site and version-pinned to the
/// dest's post-call token (`dest#s{b}_t`) so it is sound under reassignment and
/// scoped to the dominated successors. This is the sound call-site postcondition
/// assumption (`designs/2026-06-25-trust-ir-composition-design.md` §4).
pub(crate) fn build_semantic_guard_map_with_summaries(
    func: &VerifiableFunction,
    summaries: &crate::modular::SummaryDatabase,
) -> FxHashMap<BlockId, Vec<Formula>> {
    build_semantic_guard_map_impl(func, Some(summaries))
}

pub(super) fn build_semantic_guard_map_impl(
    func: &VerifiableFunction,
    summaries: Option<&crate::modular::SummaryDatabase>,
) -> FxHashMap<BlockId, Vec<Formula>> {
    use std::collections::VecDeque;

    // verifier-perf: bail to an EMPTY guard map for over-budget functions (see
    // `func_exceeds_vcgen_budget`). SOUNDNESS: DROP-ONLY — fewer path/dataflow
    // hypotheses can only weaken a PROVE, never false-prove.
    if func_exceeds_vcgen_budget(func) {
        return FxHashMap::default();
    }

    #[derive(Clone, Copy, PartialEq, Eq)]
    enum VisitState {
        NotVisited,
        VisitedPrecise,
        VisitedWeakened,
    }

    let num_blocks = func.body.blocks.len();
    let mut result: FxHashMap<BlockId, Vec<Formula>> =
        FxHashMap::with_capacity_and_hasher(num_blocks, Default::default());
    let mut visited = vec![VisitState::NotVisited; num_blocks];
    // Statement-granular version oracle, built once: used to version each threaded
    // block-def at its establish point (replacing the deref-store-havoc kill).
    let sv = super::stmt_versions_for(func);
    // Snapshot the active `Arc`-backed callee summary context once for the body so
    // call-site fact producers do not repeat TLS `RefCell` borrows or clone `Vec`s.
    let active_callee_summaries = crate::current_callee_summaries();
    // Cache each block's own extracted & establish-versioned facts so a
    // `VISITED_PRECISE -> VISITED_WEAKENED` join/loop revisit reuses them
    // without re-extracting or re-versioning the block's statements and call dest.
    let mut block_own_facts: Vec<Option<Vec<Formula>>> = vec![None; num_blocks];
    // BFS: (block_id, accumulated_path_assumptions)
    let mut queue: VecDeque<(BlockId, Vec<Formula>)> =
        VecDeque::with_capacity(num_blocks.min(64));
    let mut live_targets: Vec<BlockId> = Vec::with_capacity(8);
    queue.push_back((BlockId(0), Vec::new()));

    let target_is_non_weakened = |target: BlockId, visited: &[VisitState]| -> bool {
        target.0 < num_blocks && visited[target.0] != VisitState::VisitedWeakened
    };
    let target_needs_enqueue = |target: BlockId,
                                guards: &[Formula],
                                visited: &[VisitState],
                                result: &FxHashMap<BlockId, Vec<Formula>>|
     -> bool {
        if target.0 >= num_blocks {
            return false;
        }
        match visited[target.0] {
            VisitState::VisitedWeakened => false,
            VisitState::VisitedPrecise => !result
                .get(&target)
                .map_or(guards.is_empty(), |existing| existing.as_slice() == guards),
            VisitState::NotVisited => true,
        }
    };

    while let Some((block_id, mut acc_guards)) = queue.pop_front() {
        if block_id.0 >= num_blocks {
            continue;
        }

        let block = &func.body.blocks[block_id.0];
        let has_live_successor = match &block.terminator {
            Terminator::Assert { target, .. }
            | Terminator::Goto(target)
            | Terminator::Call { target: Some(target), .. }
            | Terminator::Drop { target, .. } => target_is_non_weakened(*target, &visited),
            Terminator::SwitchInt { targets, otherwise, .. } => {
                target_is_non_weakened(*otherwise, &visited)
                    || targets.iter().any(|(_, t)| target_is_non_weakened(*t, &visited))
            }
            Terminator::Opaque { targets, .. } => {
                targets.iter().any(|t| target_is_non_weakened(*t, &visited))
            }
            Terminator::Call { target: None, .. }
            | Terminator::Return
            | Terminator::Unreachable
            | _ => false,
        };

        // P0-2: At join points (blocks reachable via multiple paths),
        // only keeping the first predecessor's guards is unsound — it creates
        // over-strong assumptions that can mask violations on the unrecorded
        // path. If a block is revisited with different guards, weaken the
        // block to Bool(true) and still reprocess its successors once so the
        // weaker assumptions reach downstream blocks. Bool(true) is the
        // terminal state: later revisits cannot weaken it further.
        //
        // Trust (2026-09-28): THIS COLLAPSE IS LOAD-BEARING IN LOOPS. Do not
        // narrow it without iteration-distinct version tokens. Tokens are static,
        // so inside a loop body a fact established early in an iteration can be
        // about the PREVIOUS iteration's value of a token that a later block of
        // the same iteration redefines. Collapsing every block revisited on the
        // loop's second pass is what cuts such a fact. Two narrowings were built
        // on 2026-09-28, and both PROVED a panicking program in trust-vcgen's own
        // suite (`escaped_local_seam_realmir::a7_the_temp_admission_refuses_every_non_carrier_spelling`,
        // `a7_loopcarried_payload_param_o1`):
        //  * the MEET at a revisited join (also measured with no reach on
        //    2026-09-20);
        //  * a single-predecessor block ADOPTING its predecessor's recomputed
        //    exit set, even when read from that predecessor's latest state rather
        //    than a stale queue entry.
        // The false refutation that motivated them stays open, and is pinned by
        // `tests/ui/trust/callee_postcondition_inside_loop.rs`.
        match visited[block_id.0] {
            VisitState::VisitedWeakened => continue,
            VisitState::VisitedPrecise => {
                if result
                    .get(&block_id)
                    .map_or(acc_guards.is_empty(), |existing| existing == &acc_guards)
                {
                    continue;
                }
                result.insert(block_id, vec![Formula::Bool(true)]);
                visited[block_id.0] = VisitState::VisitedWeakened;
                if !has_live_successor {
                    continue;
                }
                acc_guards = vec![Formula::Bool(true)];
            }
            VisitState::NotVisited => {
                visited[block_id.0] = VisitState::VisitedPrecise;
                if !acc_guards.is_empty() {
                    if has_live_successor {
                        result.insert(block_id, acc_guards.clone());
                    } else {
                        result.insert(block_id, acc_guards);
                        continue;
                    }
                } else if !has_live_successor {
                    continue;
                }
            }
        }

        let own_facts = block_own_facts[block_id.0].get_or_insert_with(|| {
            compute_block_own_semantic_facts(
                func,
                &sv,
                block,
                summaries,
                active_callee_summaries.as_ref(),
            )
        });
        let mut next_guards = acc_guards;
        next_guards.extend_from_slice(own_facts);

        // Propagate to successor blocks.
        // For Assert terminators, the target is the assert-passed successor.
        // For Goto/Call/Drop, propagate unchanged.
        // For SwitchInt, propagate to all unique live targets (semantic guards are
        // orthogonal to branch conditions; duplicate edges from the same SwitchInt
        // carry identical `next_guards` and would be immediate no-ops on pop).
        match &block.terminator {
            Terminator::Assert { target, .. }
            | Terminator::Goto(target)
            | Terminator::Call { target: Some(target), .. }
            | Terminator::Drop { target, .. } => {
                if target_needs_enqueue(*target, &next_guards, &visited, &result) {
                    queue.push_back((*target, next_guards));
                }
            }
            Terminator::SwitchInt { targets, otherwise, .. } => {
                live_targets.clear();
                for &(_, target) in targets {
                    if !live_targets.contains(&target)
                        && target_needs_enqueue(target, &next_guards, &visited, &result)
                    {
                        live_targets.push(target);
                    }
                }
                if !live_targets.contains(otherwise)
                    && target_needs_enqueue(*otherwise, &next_guards, &visited, &result)
                {
                    live_targets.push(*otherwise);
                }
                if let Some((&last, rest)) = live_targets.split_last() {
                    for &target in rest {
                        queue.push_back((target, next_guards.clone()));
                    }
                    queue.push_back((last, next_guards));
                }
            }
            Terminator::Opaque { targets, .. } => {
                live_targets.clear();
                for &target in targets {
                    if !live_targets.contains(&target)
                        && target_needs_enqueue(target, &next_guards, &visited, &result)
                    {
                        live_targets.push(target);
                    }
                }
                if let Some((&last, rest)) = live_targets.split_last() {
                    for &target in rest {
                        queue.push_back((target, next_guards.clone()));
                    }
                    queue.push_back((last, next_guards));
                }
            }
            Terminator::Call { target: None, .. }
            | Terminator::Return
            | Terminator::Unreachable => {}
            // Trust: Terminator is #[non_exhaustive]; unknown variants
            // are conservatively handled by not propagating guards.
            _ => {}
        }
    }

    // Trust (VEC-LEN-LOOP-1, 2026-10-07): the length of a std `Vec` that nothing between
    // its establishing read and the index can change, tied at each std index call. Added per USE
    // block after the walk, never propagated, so the join weakening above (which
    // drops every fact at a loop header) does not reach it; each fact is already
    // renamed at its block's terminal. See `vec_len_invariant` for the gates and the
    // soundness argument.
    for (block_id, fact) in super::vec_len_invariant::vec_len_invariant_use_facts(func, &sv) {
        result.entry(block_id).or_default().push(fact);
    }

    result
}

/// Extract and establish-version a single block's own semantic facts (assert-passed
/// semantics, statement/set-discriminant definitions, and `Terminator::Call` dest/summary
/// postconditions). Computed at most once per block during `build_semantic_guard_map_impl`.
fn compute_block_own_semantic_facts(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    block: &trust_types::BasicBlock,
    summaries: Option<&crate::modular::SummaryDatabase>,
    active_callee_summaries: Option<&crate::CalleeSummaryContext>,
) -> Vec<Formula> {
    // Trust: kill inherited facts that THIS block invalidates by reassigning
    // one of their free variables, BEFORE the fact set is recorded for this
    // block or threaded to successors. A CheckedSub `hi - lo` leaves the
    // assert-passed fact `hi >= lo` (and the block def `lo == hi`) in
    // `acc_guards`; if this block then does `lo = big`, those facts are
    // stale, and applied to this block's own `hi - lo` VC they vacuously
    // discharge a real underflow (a false-PROVE of a real overflow).
    // Dropping a fact is always sound — it can only weaken a PROVE to a
    // FAIL, never the reverse. Mirrors `extend_killing_redefs` in the v2
    // path-definition fixpoint, which closes the same hole on that path.
    // Trust: 2026-09-16 (round A11) — each def carries the index of its own
    // statement, which bounds its establish search below (set-discriminant defs
    // carry no index: the `discr_` namespace is rebound by no place write).
    //
    // Trust S2c: the INHERITED-GUARD, ASSERT-PASSED, and deref-store-havoc kills
    // are replaced by establish-point versioning + the EXEMPTION (threaded facts
    // conjoined after the whole-VC rename). The statement/set-discriminant/assert
    // semantic facts depend only on `(func, sv, block)`, so share both the raw
    // extraction and the establish-versioned facts through `PreparedBlockOutflow`.
    let mut own_guards = match sv.prepared_block_outflow(func, block) {
        Some(prepared) => prepared.stmt_and_assert_semantic_facts(func, sv, block),
        None => super::path_defs::PreparedBlockOutflow::stmt_and_assert_semantic_facts_uncached(
            func, sv, block,
        ),
    };

    // Trust S2c: the TERMINATOR-DEST kill is DELETED. A name the block's
    // terminator (`Call { dest }` / escaping `&mut`) reassigns has its OUT token
    // pinned to the terminator marker `s{b}_t` by the terminator-aware oracle, so
    // an establish-versioned threaded fact about it is name-disjoint from the
    // post-call successor read — the drop, by name-disjointness.

    // Modeled total-call postcondition: `len()` results are bounded by
    // `isize::MAX` (language invariant; see trust-types
    // total_call_summaries). Without this fact the formula lane sees an
    // unconstrained fresh result and false-FAILs safe `len() + k`
    // arithmetic. Added AFTER the terminator kill — the fact is about the
    // value this terminator just defined. The shared matcher keeps this
    // mirror in lockstep with the bridge's TrustIr `Assume`.
    if let Terminator::Call {
        func: callee,
        args,
        dest,
        target: Some(_),
        callee_key,
        callee_identity,
        ..
    } = &block.terminator
    {
        let call_tail = method_tail(callee);
        let reaches_summarized_body = std::cell::OnceCell::new();
        let call_reaches_summarized = || {
            *reaches_summarized_body.get_or_init(|| {
                active_callee_summaries
                    .is_some_and(|ctx| ctx.call_reaches_summarized_body(&block.terminator))
            })
        };

        // Trust S2c: these terminator-defined bounds are about the Call DEST.
        // Collect, then VERSION each (dest pinned to `s{b}_t`) before threading,
        // so a successor that reassigns the dest disconnects the stale bound
        // (replacing the deleted terminator kill).
        let term_dest_name = std::cell::OnceCell::new();
        let dest_var_of = || {
            Formula::Var(
                term_dest_name.get_or_init(|| crate::place_to_var_name(func, dest)).clone(),
                Sort::Int,
            )
        };
        let mut term_facts: Vec<Formula> = Vec::new();
        if dest.projections.is_empty()
            && args.len() == 1
            && call_tail == "len"
            && trust_types::total_call_summaries::total_summary_len_call(callee)
        {
            let dest_var = dest_var_of();
            term_facts.push(Formula::Ge(
                Box::new(dest_var.clone()),
                Box::new(Formula::Int(0)),
            ));
            if len_call_result_has_isize_bound(func, callee, args) {
                term_facts.push(Formula::Le(
                    Box::new(dest_var.clone()),
                    Box::new(Formula::Int(i64::MAX as i128)),
                ));
            }
            // Trust (TINV P1 on real MIR, 2026-10-06): `<[T]>::len(s)` on a SHARED
            // slice reference returns exactly `s`'s length metadata, so the dest is
            // tied to the receiver's `__slice_len` symbol as the receiver is AT this
            // call (the read side is versioned at the terminal, the dest at
            // `s{b}_t`, by `version_terminator_dest_fact` below). Without it a
            // `self.b.len()` whose receiver is a copy of a `&mut self` field
            // (`_27 = copy (*self).0; _5 = &(*_27); _4 = len(move _5)`) reached no
            // length fact at all: the global `_len == coll_len` tie declines a
            // base whose length is not stable for the whole body. Gated to a
            // `&[T]` receiver (`str`, `Vec`, `String` and every other receiver keep
            // no tie), and to the shared matcher's root-anchored std `len`.
            if crate::operand_ty_cow(func, &args[0]).is_some_and(|t| {
                matches!(t.as_ref(), Ty::Ref { mutable: false, inner }
                    if matches!(inner.as_ref(), Ty::Slice { .. }))
            }) && let Some(len) = crate::slice_len_formula(func, &args[0])
                && matches!(len, Formula::Var(_, Sort::Int))
            {
                term_facts.push(Formula::Eq(
                    Box::new(dest_var),
                    Box::new(len),
                ));
            }
        }

        let dest_is_ssa_cell = std::cell::OnceCell::new();
        let dest_is_ssa = || {
            *dest_is_ssa_cell.get_or_init(|| {
                dest.projections.is_empty()
                    && !crate::local_defs::is_parameter(func, dest.local)
                    && is_single_static_assignment(func, dest.local)
            })
        };

        // `mem::size_of::<T>()` / `mem::align_of::<T>()` at a primitive `T`
        // are compile-time constants of the INPUT PROGRAM. Left havoc'd,
        // `1024 / size_of::<u64>()` is refuted for division by zero on a
        // closed, input-free body. See `mem_layout_call_dest_facts` for what
        // each fact is derived from.
        if args.is_empty()
            && matches!(call_tail, "size_of" | "align_of")
            && crate::local_ty_ref(func, dest.local)
                .is_some_and(|ty| ty.int_width().is_some())
            && dest_is_ssa()
        {
            term_facts.extend(mem_layout_call_dest_facts(callee, dest_var_of));
        }

        // Model the ordered-min/max/clamp stdlib calls with their defining
        // (sound, always-true) result bounds. Without this the call result is
        // havoc'd, and a safety obligation over it — e.g. the bounds check for
        // `arr[n.min(3)]` (`min(n,3) <= 3 < len`) — is FALSELY REFUTED by the
        // SMT lane picking an out-of-range havoc value (a spurious cex). These
        // are integer Ord operations (`as Ord>` excludes floats, which have no
        // Ord and whose NaN breaks `<=`), so the bounds hold unconditionally.
        // SOUNDNESS (P0, hunt-5): only when the result local is single-static-assignment —
        // otherwise a `let p = &mut d; *p = e` reassigns `d` and the `d <= a` bound goes
        // stale (the same class as the global `build_min_max_facts` gate). The mut-borrow is
        // caught by `is_single_static_assignment`.
        let may_have_ssa_dest_fact = match call_tail {
            "min" | "max" | "saturating_add" | "saturating_sub" | "saturating_mul" => {
                args.len() == 2
            }
            "div_ceil" => args.len() == 2 && callee_key.is_some(),
            "clamp" => args.len() == 3,
            "from" | "into" | "wrapping_neg" | "to_bits" | "from_bits" => args.len() == 1,
            "unwrap_or" => args.len() == 2,
            "expect" | "unwrap" => !args.is_empty(),
            _ => false,
        } || callee.starts_with('@')
            || active_callee_summaries
                .is_some_and(|summary_ctx| summary_ctx.has_return_value_summary_for(callee));
        if may_have_ssa_dest_fact && dest_is_ssa() {
            // The min/max/clamp result semantics live in ONE place
            // (`ord_min_max_clamp_result_facts`) — see it for the clamp
            // `lo > hi` panic soundness argument. Here the dest is named by its
            // `place_to_var_name` alias (`__ret` for the return slot); the
            // postcondition lane re-emits the SAME facts under the RAW `_0` the
            // `#[ensures]` reads (the alias does not reach `_0` there).
            let ord_method = if matches!(call_tail, "min" | "max" | "clamp") {
                primitive_int_ord_method(func, callee, args, dest)
            } else {
                None
            };
            let ord_dest_var = ord_method.map(|_| dest_var_of());
            let ord_facts = if let Some(ref dest_var) = ord_dest_var {
                ord_min_max_clamp_result_facts_for_method(func, ord_method, args, dest_var)
            } else {
                Vec::new()
            };
            if !ord_facts.is_empty() {
                term_facts.extend(ord_facts);
                // Trust: 2026-09-16 (round A8) — the CANONICAL-LENGTH twin of each
                // `min`/`max` argument that is a `PtrMetadata`/`Len` temp: `dest <=
                // {root}__slice_len` beside `dest <= _4`. Versioned at this call by
                // `version_terminator_dest_fact` below, so the root's symbol is the
                // version live HERE — the sound spelling of what the global lane
                // (`build_min_max_facts`) can only state for a root that is never
                // reseated. See `callee_summaries::call_point_slice_len_of_arg`.
                // Same gate as the facts above (NAME-ANCHOR-2): a primitive
                // integer `Self`, so the impl is core's.
                if args.len() == 2
                    && let Some(dest_var) = ord_dest_var
                {
                    for arg in args {
                        let Some(len) = call_point_slice_len_of_arg(func, block, arg) else {
                            continue;
                        };
                        if ord_method == Some("min") {
                            term_facts
                                .push(Formula::Le(Box::new(dest_var.clone()), Box::new(len)));
                        } else if ord_method == Some("max") {
                            term_facts
                                .push(Formula::Ge(Box::new(dest_var.clone()), Box::new(len)));
                        }
                    }
                }
            } else if args.len() == 1
                && matches!(call_tail, "from" | "into")
                && is_bool_from_call(callee, callee_key.as_ref())
                && crate::operand_ty_cow(func, &args[0])
                    .is_some_and(|t| matches!(t.as_ref(), Ty::Bool))
                && crate::local_ty_ref(func, dest.local)
                    .is_some_and(|ty| ty.int_width().is_some())
            {
                // `<{int} as From<bool>>::from(b)` returns `b as {int}` ∈ {0, 1} — std's
                // impl only: the callee is keyed to a real sysroot crate and named by an
                // exact path (NUM-METHOD-ANCHOR-1). The
                // call result is otherwise havoc'd, so `(.. + usize::from(c)) * 4` (the
                // base64 codec capacity `(full_chunks + usize::from(rem > 0)) * 4`) is
                // FALSELY REFUTED by the SMT lane picking an out-of-range havoc value.
                // SOUND: a theorem of `From<bool>` for a primitive integer (the orphan
                // rule forbids any other impl on a primitive int); gated on an int-typed
                // dest so a non-primitive `From<bool>` newtype is correctly skipped.
                let dest_var = dest_var_of();
                term_facts
                    .push(Formula::Ge(Box::new(dest_var.clone()), Box::new(Formula::Int(0))));
                term_facts
                    .push(Formula::Le(Box::new(dest_var), Box::new(Formula::Int(1))));
            } else if args.len() == 1
                && matches!(call_tail, "from" | "into")
                && is_std_int_from_into_call(callee)
                && crate::operand_ty_cow(func, &args[0])
                    .is_some_and(|t| t.int_width().is_some_and(|w| w < 128))
                && crate::local_ty_ref(func, dest.local)
                    .is_some_and(|ty| ty.int_width().is_some_and(|w| w < 128))
            {
                // Trust (2026-09-24, TRUST-09): `<B as From<A>>::from(a)` /
                // `<A as Into<B>>::into(a)` between primitive integers returns `a`
                // unchanged — every such std impl is lossless and no other crate may
                // write one (see `is_std_int_from_into_call`). Left havoc'd,
                // `TABLE[usize::from(byte)]` over a `[_; 256]` is refuted with an
                // index of 256 that no `u8` produces. 128-bit operands fail closed,
                // as the sibling arms do.
                term_facts.push(Formula::Eq(
                    Box::new(dest_var_of()),
                    Box::new(crate::operand_to_formula(func, &args[0])),
                ));
            } else if args.len() == 2 && call_tail == "unwrap_or" && is_std_unwrap_or_call(callee) {
                // `Result`/`Option` `unwrap_or(default)` is TOTAL and returns either
                // the success payload or `default` — both values of the destination's
                // own type — so an int-typed dest satisfies its TYPE RANGE
                // unconditionally (for a `char` dest, modeled as `Int{32,unsigned}`,
                // the range is a sound WIDENING of the char scalar set). The result is
                // otherwise havoc'd, and a safety obligation over it (e.g. the bounds
                // check for `arr[x.try_into().unwrap_or(0)]`) is FALSELY REFUTED by
                // the SMT lane picking an out-of-range havoc value.
                //
                // width == 128 FAILS CLOSED (no facts at all): `Formula::Int` is
                // i128-backed, so `u128::MAX` is representable only via the
                // `Formula::UInt` escape hatch, and any literal beyond i64 is
                // unlowerable in the trust-wp lane (`Formula::has_large_integers`)
                // and rejected by the native typed-CHC Int parser (see the
                // signed-128 BV-neg routing above `v2_build_assert_negation_vc`) —
                // the codebase routes 128-bit obligations through the BV theory
                // instead, so no Int-sorted 128-bit range/payload fact is emitted.
                if let Some((width, signed)) = crate::local_ty_ref(func, dest.local)
                    .and_then(|ty| match ty {
                        Ty::Int { width, signed } => Some((*width, *signed)),
                        _ => None,
                    })
                    .filter(|&(w, _)| w < 128)
                {
                    let dest_var = dest_var_of();
                    term_facts
                        .push(crate::range::input_range_constraint(&dest_var, width, signed));
                    // The COMPOSED idiom `_r = T::try_from(_x); _d = unwrap_or(_r,
                    // _def)` additionally pins the dest's VALUE per branch — see
                    // `int_try_from_unwrap_or_facts` for the fact shapes and the
                    // full soundness gates (std anchors, `TryFromIntError` Result
                    // anchor, SSA/single-use conduit, stable source).
                    if let Some(facts) =
                        int_try_from_unwrap_or_facts(func, args, &dest_var, width, signed)
                    {
                        term_facts.extend(facts);
                    }
                }
            } else if args.len() == 1
                && call_tail == "wrapping_neg"
                && let Some((_, value)) = wrapping_neg_call_dest_value(func, &block.terminator)
            {
                // `dest = x.wrapping_neg()`: a total theorem of two's complement,
                // modeled with its exact value (an `Ite`) — see
                // `wrapping_neg_call_dest_value` for the signed/unsigned forms and
                // width gating. As an INTERMEDIATE result the dest is pinned here;
                // the return-slot case is pinned (Ite-lifted) in the postcondition
                // lane so a `#[ensures]` over `x.wrapping_neg()` connects to `_0`.
                term_facts.push(Formula::Eq(Box::new(dest_var_of()), Box::new(value)));
            } else if args.len() == 2
                && matches!(call_tail, "saturating_add" | "saturating_sub" | "saturating_mul")
                && let Some((_, clamped)) = saturating_call_dest_value(func, &block.terminator)
            {
                // `x.saturating_add(y)` / `x.saturating_sub(y)` as an INTERMEDIATE
                // result (e.g. `arr[i.saturating_sub(1)]`): pin the dest to its
                // exact clamped value so a downstream safety obligation over it is
                // not FALSELY REFUTED by a havoc'd result. The return-slot case (a
                // function that returns the saturating result directly, for a
                // `#[ensures]` over it) is pinned separately under the raw `_0`
                // name in the postcondition lane — see `saturating_call_dest_value`.
                term_facts.push(Formula::Eq(Box::new(dest_var_of()), Box::new(clamped)));
            } else if args.len() == 2
                && call_tail == "div_ceil"
                && callee_key.is_some()
                && let Some((_, a, b)) =
                    super::call_facts::div_ceil_call_operands(func, &block.terminator)
            {
                // `n.div_ceil(k)` on a std unsigned receiver as an INTERMEDIATE
                // result: pin the dest to its exact ceiling (by the ceiling's
                // linear characterization), so a dominating `n <= MAX` bounds
                // `vec![0; n.div_ceil(8)]` exactly as it bounds the hand-written
                // `(n + 7) / 8`. The zero divisor stays charged at the call
                // (`panic_calls::divzero_call`); the return slot is pinned in the
                // postcondition lane — see `div_ceil_call_dest_fact`.
                term_facts.push(super::call_facts::div_ceil_fact_from_operands(
                    &dest_var_of(),
                    a,
                    b,
                ));
            } else if callee.starts_with('@')
                && super::intrinsic_semantics::classify_value_modeled_intrinsic(callee).is_some()
                && let Some((_, intrinsic_facts)) =
                    value_modeled_intrinsic_facts(func, &block.terminator, &dest_var_of())
            {
                // `dest = ctpop/ctlz/cttz/bswap/bitreverse(x)` — a body-less rustc
                // intrinsic. It has NO MIR in any build, so before this lane the only
                // model was "cannot panic" and the dest was an unconstrained havoc:
                // `arr[x.count_ones() as usize]` into `[_; 33]` was FALSELY REFUTED
                // with `count_ones = 4294967295`. Pin the dest to the intrinsic's
                // EXACT bitvector definition (and, for the counting family, its
                // `[0, W]` range). The return-slot case is re-emitted under the raw
                // `_0` name in the postcondition lane, as the saturating pin above is.
                //
                // ADDS FACTS: see `intrinsic_semantics`'s header for the exhaustive
                // width-8 differential test and the falsification fixtures that stand
                // behind each definition.
                term_facts.extend(intrinsic_facts);
            } else if args.len() == 1
                && matches!(call_tail, "to_bits" | "from_bits")
                && let Some(fact) = float_bits_call_dest_fact(func, &block.terminator)
            {
                // `bits = v.to_bits()` / `r = f64::from_bits(b)`: an EXACT
                // bit-REINTERPRETATION (no rounding / no conversion), modeled
                // so the integer lane re-correlates with the float's IEEE
                // encoding. Without it the dest is havoc'd and disconnected
                // from the shared `Var(v, BitVec)` the fp compares read, which
                // FALSELY REFUTES a guarded `bits - 1` under `v != 0.0` (the
                // `f64_next_up_compat` shape). The returned fact is a complete,
                // correctly-sorted `Eq` (Int dest for to_bits, BitVec dest for
                // from_bits) — it deliberately does NOT use the Int-sorted
                // `dest_var` above. Full soundness + the shared-symbol argument
                // live in `float_bits_call_dest_fact`.
                term_facts.push(fact);
            } else if !args.is_empty()
                && matches!(call_tail, "expect" | "unwrap")
                && let Some(v) = expect_infallible_const_int_conversion(func, callee, args, dest)
            {
                // Trust (countdown-loop piece, B0): `_d = try_into(CONST).expect(..)`
                // with a provably-fitting constant — the dest IS the constant on
                // every completed call (success-by-construction; the recognizer's
                // hard gates pin the std primitive-int impl family and evaluate the
                // range at the exact target width). Pins the value so the
                // `remain % scale` / `remain / scale` zero-divisor obligations and
                // the loop-guard constant discharge. SSA-gated (above) + versioned
                // (below) like every fact in this lane.
                term_facts
                    .push(Formula::Eq(Box::new(dest_var_of()), Box::new(Formula::Int(v))));
            } else if let Some(summary_ctx) = active_callee_summaries
                && summary_ctx.has_return_value_summary_for(callee)
                && call_reaches_summarized()
            {
                // Trust (return-value summaries): a LOCAL callee with a whole-crate
                // return summary (computed at the analysis phase) licenses facts
                // about the value this call just defined. All three shapes share
                // one soundness argument: the recorded summary holds for EVERY
                // input and EVERY return path of the callee (the summary
                // computations fail closed with None otherwise), and this emission
                // is SSA-gated (above) + versioned (below), so a `&mut`
                // reassignment of the dest drops the stale fact — the same
                // staleness defense as the stdlib min/max/clamp bounds. A
                // PANICKING callee path returns nothing, so a claim about the
                // RETURNED value is vacuous there — and these facts are threaded
                // only to the call's SUCCESS target below, never an unwind edge.
                //   * UPPER bound (clamp-via-helper): `dest <= b` — discharges a
                //     guarded access THROUGH a bounding helper, e.g.
                //     `arr[clamp_idx(i)]` where `clamp_idx` returns `i.min(LEN-1)`;
                //   * LOWER bound (the mirror): `dest >= c` — discharges e.g. the
                //     Rem-by-zero obligation on `h % small_den(g)` where every
                //     `small_den` return site is a const `>= 1`;
                //   * CONST SET (strictly stronger; every return site a constant):
                //     `dest == c1 ∨ … ∨ dest == ck`.
                // D5-A: a same-crate callee with NONE of these (and no
                // injected postcondition below) leaves the dest free, and
                // `refutation_scope::unpinned_local_call_dests` MIRRORS this
                // list to withhold a SAT that chose it. A producer added
                // here belongs there too (missing it only over-withholds).
                // Only for a call that reaches the summarized body
                // (`call_reaches_summarized_body`).
                if let Some(bound) = summary_ctx.return_upper_bound(callee) {
                    term_facts.push(Formula::Le(
                        Box::new(dest_var_of()),
                        Box::new(Formula::Int(bound)),
                    ));
                }
                if let Some(lo) = summary_ctx.return_lower_bound(callee) {
                    term_facts.push(Formula::Ge(
                        Box::new(dest_var_of()),
                        Box::new(Formula::Int(lo)),
                    ));
                }
                // Trust (2026-09-30): the RETURN INTERVAL, from the interval
                // fixpoint over the callee's own body (`dest >= lo`, `dest <= hi`,
                // each side only when tighter than the return type). Deliberately
                // NOT mirrored in `unpinned_local_call_dests`: a range is not a
                // model of the value, so a counterexample that picked a value
                // inside it is still not an execution, and holding it is the
                // over-withholding direction.
                if let Some((lo, hi)) = summary_ctx.return_interval(callee) {
                    match (lo, hi) {
                        (Some(lo), Some(hi)) => {
                            let dest_var = dest_var_of();
                            term_facts.push(Formula::Ge(
                                Box::new(dest_var.clone()),
                                Box::new(Formula::Int(lo)),
                            ));
                            term_facts
                                .push(Formula::Le(Box::new(dest_var), Box::new(Formula::Int(hi))));
                        }
                        (Some(lo), None) => {
                            term_facts.push(Formula::Ge(
                                Box::new(dest_var_of()),
                                Box::new(Formula::Int(lo)),
                            ));
                        }
                        (None, Some(hi)) => {
                            term_facts.push(Formula::Le(
                                Box::new(dest_var_of()),
                                Box::new(Formula::Int(hi)),
                            ));
                        }
                        (None, None) => {}
                    }
                }
                if let Some(consts) = summary_ctx.return_const_set(callee) {
                    // A single-constant callee pins the dest exactly — no
                    // degenerate one-armed disjunction.
                    match consts {
                        [] => {}
                        [c] => {
                            let dest_var = dest_var_of();
                            term_facts.push(Formula::Eq(
                                Box::new(dest_var),
                                Box::new(Formula::Int(*c)),
                            ));
                        }
                        consts => {
                            let dest_var = dest_var_of();
                            let eqs: Vec<Formula> = consts
                                .iter()
                                .map(|c| {
                                    Formula::Eq(
                                        Box::new(dest_var.clone()),
                                        Box::new(Formula::Int(*c)),
                                    )
                                })
                                .collect();
                            term_facts.push(Formula::Or(eqs));
                        }
                    }
                }
            }
        }

        // Separate-compilation: a PROVED callee's postcondition is a fact about
        // the value THIS call just defined — structurally identical to the
        // stdlib total-call bounds above. Rebind the callee formals to the
        // actual arguments and the callee result `_0` to the caller dest
        // (`rebind_callee_postconditions`), then thread it through the SAME
        // `version_terminator_dest_fact` lane: the dest is pinned to the
        // post-call token `s{b}_t` (return-binding to a fresh post-SSA value)
        // and the fact propagates only to the dominated successors. CONJOINED,
        // never implied — the sound polarity for the "SAT iff violation"
        // convention (design 2026-06-25 §2/§4).
        //
        // SOUNDNESS gates — the list lives in
        // `callee_postcondition_is_injectable`, which is the authority; this
        // is its index, corrected 2026-08-31 after it named a gate that does
        // not exist. `summary.proved` is NOT one of them: it is read by no
        // production code on this path (only `postconditions_are_definitional`,
        // via `has_reusable_postcondition_evidence`, which is strictly
        // stronger — a `proved` dyn or sealed-contract summary still injects
        // nothing). The seven are (1) the definitional/reusable evidence bit;
        // (2) empty `dest` projections; (3) arity match — otherwise the
        // formal->arg rebinding would be ill-formed; (4)
        // `local_defs::dest_fact_is_version_pinnable(dest)` — NOT the gate the
        // min/max facts use, and it stopped being that on 2026-08-31. Those
        // facts are keyed on the dest's BARE name and need
        // `is_single_static_assignment`, which a PARAMETER's entry definition
        // refutes; this lane pins its clause to `{dest}#s{b}_t` just below and
        // needs only that this call be the dest's one whole write. Both refuse a
        // `&mut`-reassigned dest, so neither can leave a stale bound; (5) the
        // shared guard-ride predicate for a PRECONDITIONED summary; (6) at
        // least one clause machine-arithmetic-free and rebindable; and (7) the
        // TIME AXIS — no argument of this call may render to the dest's name,
        // or the retiming below reads it at the wrong time
        // (`terminator_args_read_name`).
        //
        // What is NOT a gate, and is the thing to look at first when a wrong
        // clause is suspected: the callee's IDENTITY. `summaries.get(callee)`
        // is a string lookup, `modular::FunctionSummary` carries no def-path
        // and no `CalleeIdentity`, and the `..` in the pattern above discards
        // the un-forgeable one the terminator does carry. The whole defence is
        // in the PRODUCER (`trust_verify.rs`'s `identity:name-collision`
        // DefId prescan and the `identity:generic` instantiation conjunct);
        // see `generate/summary_key_collision_tests.rs` for what that means
        // here.
        if let Some(summaries) = summaries
            && let Some(summary) = summaries.get(callee)
            && callee_postcondition_is_injectable(func, dest, summary, args)
        {
            for post in rebind_callee_postconditions(func, args, dest, summary) {
                term_facts.push(post);
            }
        }

        // `version_terminator_dest_fact` answers `None` — no fact at all —
        // when this call's own ARGUMENTS read the destination's name, the one
        // shape whose blanket post-call retiming would turn a pre-call read
        // into a post-call one. Fail closed for the WHOLE batch: every
        // producer above pins the dest against the arguments, so they share
        // one precondition (see `terminator_args_read_name`).
        if !term_facts.is_empty() {
            let term_dest_name =
                term_dest_name.get_or_init(|| crate::place_to_var_name(func, dest));
            for f in term_facts {
                if let Some(versioned) =
                    version_terminator_dest_fact(sv, func, block, term_dest_name, f)
                {
                    own_guards.push(versioned);
                }
            }
        }

        if let Some(summary_ctx) = active_callee_summaries {
            // Trust (derived trivial-setter summary): a recognized trivial-setter
            // callee (`fn set(p: &mut u32, v: u32) { *p = v; }` — see
            // `SetterSummary` for why the recognizer IS the proof) makes the
            // call's effect on the caller TOTAL AND EXACT: the mut-borrowed
            // target equals the stored value on the success continuation.
            // Without this the `&mut` arg is havocked (correct) but the caller
            // learns nothing about its NEW value, so `assert!(a == v)` after
            // `set(&mut a, v)` demotes to runtime-checked. All gates + the
            // versioning argument live in `trivial_setter_callsite_fact`.
            if summary_ctx.has_setter_summary_for(callee)
                && call_reaches_summarized()
                && let Some((_, fact)) = trivial_setter_callsite_fact(sv, func, block)
            {
                own_guards.push(fact);
            }

            // Trust (TRUST-10, field-read summary): `r = self.is_empty()` whose
            // callee is recorded as `ret ⇔ ((*self).nbits == 0)` (or a getter
            // `ret == (*self).nbits`) states that relation over THIS caller's
            // spelling of the field, pre-call and post-call — see
            // `return_field_summary` for the gates and the protector argument.
            if summary_ctx.has_return_field_summary_for(callee) {
                own_guards.extend(return_field_callsite_facts(sv, func, block));
            }
            // Trust: separately typed, exact-identity constructor field facts.
            // Actuals are pre-call; the field is explicitly the call's output.
            // This does not widen generic summary injection or result pinning.
            if callee_identity.is_some() && summary_ctx.has_constructor_return_for(callee) {
                own_guards.extend(super::constructor_return::constructor_return_callsite_facts(
                    sv, func, block,
                ));
            }
        }

        // Dispatch real-sysroot `SysrootItem`-keyed success-edge facts in one O(1) enum branch.
        if let Some(sysroot_item) =
            callee_key.as_ref().filter(|k| k.krate_is_real_sysroot).and_then(|k| k.sysroot_item)
        {
            use trust_types::SysrootItem as S;
            match sysroot_item {
                // STR_BYTES_POSITION_BOUND: `Some(i)` from `s.bytes().position(..)` is
                // `i + 1 <= len(s)`, guarded by the discriminant; see the producer.
                S::IteratorPosition | S::IteratorRposition => {
                    own_guards.extend(super::str_offset::str_bytes_position_dest_facts(
                        sv, func, block,
                    ));
                }
                // VEC_FROM_ELEM_LEN: `vec![x; n]`'s length is `n` on the success edge.
                S::VecFromElem => {
                    own_guards.extend(super::call_facts::vec_from_elem_len_facts(sv, func, block));
                }
                // MEM_REPLACE_SWAP: the exact effect of `mem::replace` / `mem::swap`.
                S::MemReplace | S::MemSwap | S::MemTake => {
                    own_guards.extend(super::call_facts::mem_replace_swap_facts(sv, func, block));
                }
                _ => {}
            }
        }
    }

    own_guards
}

#[cfg(test)]
mod mem_layout_fact_tests {
    use super::*;

    fn facts(callee: &str) -> Vec<Formula> {
        mem_layout_call_dest_facts(callee, || Formula::Var("_1".to_string(), Sort::Int))
    }

    /// `size_of::<T>()` at a primitive is CONST-FOLDED to its exact value — the
    /// value the Rust language fixes for that type on every target.
    #[test]
    fn size_of_at_a_primitive_is_folded_to_its_exact_value() {
        assert_eq!(
            facts("core::mem::size_of::<u64>"),
            vec![Formula::Eq(
                Box::new(Formula::Var("_1".to_string(), Sort::Int)),
                Box::new(Formula::Int(8))
            )]
        );
        assert_eq!(
            facts("std::mem::size_of::<bool>"),
            vec![Formula::Eq(
                Box::new(Formula::Var("_1".to_string(), Sort::Int)),
                Box::new(Formula::Int(1))
            )]
        );
    }

    /// `align_of::<T>()` must NEVER be folded to an exact value. The alignment of
    /// `u64`/`f64`/`u128` is 8 on aarch64 and x86-64 but 4 on x86-32 Linux, and
    /// this lane has no target to consult — an equation here would be a false
    /// fact on a real supported target. Only the two target-independent bounds
    /// are emitted, so this test fails if anyone "simplifies" it to a fold.
    #[test]
    fn align_of_is_bounded_never_folded() {
        let f = facts("core::mem::align_of::<u64>");
        assert_eq!(f.len(), 2, "align_of emits exactly the two bounds: {f:?}");
        assert!(
            !f.iter().any(|x| matches!(x, Formula::Eq(..))),
            "align_of must not be pinned to an exact value (target-dependent): {f:?}"
        );
        let v = Formula::Var("_1".to_string(), Sort::Int);
        assert_eq!(f[0], Formula::Ge(Box::new(v.clone()), Box::new(Formula::Int(1))));
        assert_eq!(f[1], Formula::Le(Box::new(v), Box::new(Formula::Int(8))));
    }

    /// A type whose size the LANGUAGE does not fix gets NO fact. `usize`/`isize`
    /// are target-dependent; a generic parameter is not even a type yet; a
    /// user ADT has a layout the compiler chooses.
    #[test]
    fn non_language_fixed_types_get_no_fact() {
        for callee in [
            "core::mem::size_of::<usize>",
            "core::mem::size_of::<isize>",
            "core::mem::size_of::<T>",
            "core::mem::align_of::<T>",
            "core::mem::size_of::<mycrate::Widget>",
        ] {
            assert!(facts(callee).is_empty(), "{callee} must yield no layout fact");
        }
    }

    /// The path match is EXACT. A user function that merely spells `size_of` in
    /// a module named `mem` is a different function with a different meaning.
    #[test]
    fn only_the_canonical_core_std_paths_match() {
        for callee in [
            "mycrate::mem::size_of::<u64>",
            "core::mem::size_of_val::<u64>",
            "core::men::size_of::<u64>",
            "size_of::<u64>",
        ] {
            assert!(facts(callee).is_empty(), "{callee} must not be credited with mem::size_of");
        }
    }

    #[test]
    fn switchint_duplicate_targets_preserve_precise_guards_and_join_collapse() {
        use std::collections::BTreeMap;
        use trust_types::{
            BasicBlock, BinOp, ConstValue, FunctionSpec, LocalDecl, SourceSpan, TupleLayouts,
            VerifiableBody,
        };

        let span = SourceSpan::default();
        let u32_ty = Ty::Int { width: 32, signed: false };
        let locals = vec![
            LocalDecl { index: 0, name: None, ty: u32_ty.clone() },
            LocalDecl { index: 1, name: Some("x".to_string()), ty: u32_ty.clone() },
            LocalDecl { index: 2, name: Some("y".to_string()), ty: u32_ty.clone() },
            LocalDecl { index: 3, name: Some("z".to_string()), ty: u32_ty.clone() },
        ];
        // bb0 defines `_2 = _1 + 1` and switches on `_1` with duplicate arms to `bb1` and `bb2`:
        //   0, 1, 2, otherwise -> bb1
        //   3, 4 -> bb2
        // bb1 defines `_3 = 7` and jumps to `bb3`.
        // bb2 jumps directly to `bb3` (so `bb3` joins differing guards from `bb1` vs `bb2`
        // and must collapse to `[Bool(true)]`).
        let blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Uint(1, 32)),
                    ),
                    span: span.clone(),
                }],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(1)),
                    targets: vec![
                        (0, BlockId(1)),
                        (1, BlockId(1)),
                        (2, BlockId(1)),
                        (3, BlockId(2)),
                        (4, BlockId(2)),
                    ],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: span.clone(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 32))),
                    span: span.clone(),
                }],
                terminator: Terminator::Goto(BlockId(3)),
            },
            BasicBlock {
                id: BlockId(2),
                stmts: Vec::new(),
                terminator: Terminator::Goto(BlockId(3)),
            },
            BasicBlock {
                id: BlockId(3),
                stmts: Vec::new(),
                terminator: Terminator::Goto(BlockId(4)),
            },
            BasicBlock {
                id: BlockId(4),
                stmts: Vec::new(),
                terminator: Terminator::Return,
            },
        ];
        let func = VerifiableFunction {
            name: "dup_switch".to_string(),
            def_path: "test::dup_switch".to_string(),
            span,
            body: VerifiableBody {
                locals,
                blocks,
                arg_count: 1,
                return_ty: u32_ty,
                datatype_defs: BTreeMap::new(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: FunctionSpec::default(),
            tuple_layouts: TupleLayouts::default(),
        };

        let map = build_semantic_guard_map(&func);
        // Same-source duplicate arms into bb1 and bb2 keep precise non-collapsed guards.
        assert_eq!(map.get(&BlockId(1)), map.get(&BlockId(2)));
        assert!(
            map.get(&BlockId(1)).is_some_and(|g| !g.is_empty() && g != &[Formula::Bool(true)]),
            "duplicate SwitchInt arms from bb0 must keep precise guards on bb1: {:?}",
            map.get(&BlockId(1))
        );
        // Join point bb3 and its downstream block bb4 collapse to `[Bool(true)]`.
        assert_eq!(map.get(&BlockId(3)), Some(&vec![Formula::Bool(true)]));
        assert_eq!(map.get(&BlockId(4)), Some(&vec![Formula::Bool(true)]));
    }
}

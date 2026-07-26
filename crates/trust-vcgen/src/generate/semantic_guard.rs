// The semantic guard map: for each block, the path condition established by
// the switches that dominate it. Everything downstream that says "this fact
// only holds on this path" reads this map. The work ceilings bound the
// fixpoint on large bodies -- exceeding them degrades to no guard, never to a
// wrong one.

use super::*;

pub(super) fn has_intrinsic_unsafe_surface(func: &VerifiableFunction) -> bool {
    if func.body.locals.iter().any(|local| ty_contains_raw_ptr(&local.ty)) {
        return true;
    }

    for block in &func.body.blocks {
        for stmt in &block.stmts {
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
        if let Terminator::Call { func: callee, is_unsafe_sig, .. } = &block.terminator
            && (*is_unsafe_sig || crate::unsafe_verify::detection::is_unsafe_fn_call(callee))
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
    let total_stmts: usize = func.body.blocks.iter().map(|b| b.stmts.len()).sum();
    // Per-block product SUM, not a global triple product. The versioning
    // oracle's query cost is bounded by the statements and aggregate operands
    // of the block it queries, so the true shape is Σ_b stmts_b × ops_b — the
    // global product over-estimated a many-small-blocks builder (aterm-spec's
    // ty_model! constructors: ~220 blocks × ~5 stmts × ~3 operands ≈ 3k real
    // work) by 500-2000×, fail-closing 73 functions that the CHC/PDR lane
    // proves outright (reports/vcgen-budget-cost-model-2026-07-06.md). The
    // kernel witnesses the cap exists for score essentially the SAME either
    // way (one block, hundreds of thousands of aggregate operands, so the
    // per-block sum ≈ the old product), and the absolute block/stmt caps plus
    // the dynamic gen_work meter (lib.rs MAX_GENERATION_WORK_BUDGET) remain
    // the backstops.
    let work: usize = func
        .body
        .blocks
        .iter()
        .map(|b| {
            let ops: usize = b
                .stmts
                .iter()
                .map(|s| match s {
                    Statement::Assign { rvalue: Rvalue::Aggregate(_, operands), .. } => {
                        operands.len()
                    }
                    _ => 0,
                })
                .sum();
            b.stmts.len().saturating_mul(ops.max(1))
        })
        .fold(0usize, usize::saturating_add);
    let over = func.body.blocks.len() > MAX_SEMANTIC_GUARD_BLOCKS
        || total_stmts > MAX_SEMANTIC_GUARD_STMTS
        || work > MAX_SEMANTIC_GUARD_WORK;
    if over && std::env::var("TRUST_VCGEN_TRACE_BUDGET").is_ok() {
        let total_agg_operands: usize = func
            .body
            .blocks
            .iter()
            .flat_map(|b| b.stmts.iter())
            .map(|s| match s {
                Statement::Assign { rvalue: Rvalue::Aggregate(_, operands), .. } => operands.len(),
                _ => 0,
            })
            .sum();
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
/// name). Returns empty for a non-min/max/clamp callee or the wrong arity. This is the
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
    dest_var: &Formula,
) -> Vec<Formula> {
    let mut facts = Vec::new();
    if is_ord_min_call(callee) && args.len() == 2 {
        // min(a, b) <= a  AND  min(a, b) <= b
        for arg in args {
            facts.push(Formula::Le(
                Box::new(dest_var.clone()),
                Box::new(crate::operand_to_formula(func, arg)),
            ));
        }
    } else if is_ord_max_call(callee) && args.len() == 2 {
        // max(a, b) >= a  AND  max(a, b) >= b
        for arg in args {
            facts.push(Formula::Ge(
                Box::new(dest_var.clone()),
                Box::new(crate::operand_to_formula(func, arg)),
            ));
        }
    } else if is_ord_clamp_call(callee) && args.len() == 3 {
        // GUARDED `(lo <= hi) -> (lo <= result <= hi)` — see the function-level
        // soundness note (clamp PANICS when `lo > hi`). Emitted unconditionally only
        // for a CONSTANT `lo <= hi` (cannot panic; ay does not fold a constant
        // `Gt(lo,hi)` so the disjunctive form would never discharge).
        let lo = crate::operand_to_formula(func, &args[1]);
        let hi = crate::operand_to_formula(func, &args[2]);
        let bound = Formula::And(vec![
            Formula::Ge(Box::new(dest_var.clone()), Box::new(lo.clone())),
            Formula::Le(Box::new(dest_var.clone()), Box::new(hi.clone())),
        ]);
        let fact = match (operand_const_int(&args[1]), operand_const_int(&args[2])) {
            (Some(l), Some(h)) if l <= h => bound,
            _ => Formula::Or(vec![Formula::Gt(Box::new(lo), Box::new(hi)), bound]),
        };
        facts.push(fact);
    }
    facts
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

    const NOT_VISITED: u8 = 0;
    const VISITED_PRECISE: u8 = 1;
    const VISITED_WEAKENED: u8 = 2;

    let mut result: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();
    let mut visited = vec![NOT_VISITED; func.body.blocks.len()];
    // Statement-granular version oracle, built once: used to version each threaded
    // block-def at its establish point (replacing the deref-store-havoc kill).
    let sv = StmtVersionCtx::build(func);
    // BFS: (block_id, accumulated_path_assumptions)
    let mut queue: VecDeque<(BlockId, Vec<Formula>)> = VecDeque::new();
    queue.push_back((BlockId(0), Vec::new()));

    while let Some((block_id, mut acc_guards)) = queue.pop_front() {
        if block_id.0 >= func.body.blocks.len() {
            continue;
        }

        let block = &func.body.blocks[block_id.0];

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
        let mut block_defs = guards::extract_block_definitions(func, block);
        block_defs.extend(extract_set_discriminant_definitions(func, block));
        // Trust S2c: the INHERITED-GUARD kill is DELETED — replaced by
        // establish-point versioning + the EXEMPTION (threaded facts conjoined after
        // the whole-VC rename). An inherited fact about a name THIS block reassigns
        // keeps its establish/entry version and is name-disjoint from this block's
        // reassigned read, instead of being dropped.

        // P0-2: At join points (blocks reachable via multiple paths),
        // only keeping the first predecessor's guards is unsound — it creates
        // over-strong assumptions that can mask violations on the unrecorded
        // path. If a block is revisited with different guards, weaken the
        // block to Bool(true) and still reprocess its successors once so the
        // weaker assumptions reach downstream blocks. Bool(true) is the
        // terminal state: later revisits cannot weaken it further.
        match visited[block_id.0] {
            VISITED_WEAKENED => continue,
            VISITED_PRECISE => {
                let existing = result.get(&block_id).cloned().unwrap_or_default();
                if existing == acc_guards {
                    continue;
                }
                acc_guards = vec![Formula::Bool(true)];
                result.insert(block_id, acc_guards.clone());
                visited[block_id.0] = VISITED_WEAKENED;
            }
            NOT_VISITED => {
                visited[block_id.0] = VISITED_PRECISE;
                if !acc_guards.is_empty() {
                    result.insert(block_id, acc_guards.clone());
                }
            }
            _ => unreachable!("unexpected semantic guard visitation state"),
        }

        // Collect new assumptions from this block:
        // 1. Semantic assert-passed guards (range + result definition)
        // 2. Dataflow definitions from assignment statements
        let mut next_guards = acc_guards;
        // Trust S2c: the ASSERT-PASSED kill is DELETED — each no-overflow fact is
        // VERSIONED at the `CheckedBinaryOp` establish point (entry operands stay
        // bare and ride the exemption). `d = hi - lo; lo = big` no longer leaks a
        // stale `hi >= lo`: the `lo` read is pinned to its pre-reassignment value.
        let assert_k = assert_passed_establish_stmt(func, block).unwrap_or(0);
        for f in guards::extract_assert_passed_semantics(func, block) {
            next_guards.push(version_assert_passed_fact(&sv, func, block, assert_k, f));
        }
        // Trust S2c: the deref-store-havoc KILL (`drop_havoced_block_defs`) is
        // REPLACED here by establish-point versioning. A non-canonicalizable
        // deref-store (`*r = v` through a reseated/opaque `&mut`) havocs its
        // referent `x`, and `extract_block_definitions` still emits the stale
        // pre-store `Eq(x, v_old)`. Versioning each threaded def at ITS predecessor
        // establish point pins the subject to its establishing-write token
        // (`x#s{B}_{k}`); the now-statement-granular inter-block oracle gives a
        // successor read of a HAVOCED `x` the havoc statement's DISTINCT token, so
        // the stale fact is name-disjoint from the live successor body and cannot
        // false-PROVE it (the drop, by name-disjointness). A LIVE def keeps the same
        // token as the successor read and still connects. Subsumption proven 0-
        // residual by `block_def_establish_subsumes_kill` (est token != terminal/OUT
        // token exactly when the subject is havoced).
        for d in block_defs {
            next_guards.push(version_block_def_at_establish(
                &sv,
                func,
                block,
                block.stmts.len(),
                d,
            ));
        }

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
        if let Terminator::Call { func: callee, args, dest, target: Some(_), .. } =
            &block.terminator
        {
            // Trust S2c: these terminator-defined bounds are about the Call DEST.
            // Collect, then VERSION each (dest pinned to `s{b}_t`) before threading,
            // so a successor that reassigns the dest disconnects the stale bound
            // (replacing the deleted terminator kill).
            let term_dest_name = crate::place_to_var_name(func, dest);
            let mut term_facts: Vec<Formula> = Vec::new();
            if trust_types::total_call_summaries::total_summary_len_bound(callee)
                && dest.projections.is_empty()
            {
                let dest_name = crate::place_to_var_name(func, dest);
                term_facts.push(Formula::Ge(
                    Box::new(Formula::Var(dest_name.clone(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ));
                term_facts.push(Formula::Le(
                    Box::new(Formula::Var(dest_name, Sort::Int)),
                    Box::new(Formula::Int(i64::MAX as i128)),
                ));
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
            if dest.projections.is_empty() && is_single_static_assignment(func, dest.local) {
                let dest_var = Formula::Var(crate::place_to_var_name(func, dest), Sort::Int);
                // The min/max/clamp result semantics live in ONE place
                // (`ord_min_max_clamp_result_facts`) — see it for the clamp
                // `lo > hi` panic soundness argument. Here the dest is named by its
                // `place_to_var_name` alias (`__ret` for the return slot); the
                // postcondition lane re-emits the SAME facts under the RAW `_0` the
                // `#[ensures]` reads (the alias does not reach `_0` there).
                let ord_facts = ord_min_max_clamp_result_facts(func, callee, args, &dest_var);
                if !ord_facts.is_empty() {
                    term_facts.extend(ord_facts);
                } else if is_bool_from_call(callee)
                    && args.len() == 1
                    && crate::operand_ty_cow(func, &args[0])
                        .is_some_and(|t| matches!(t.as_ref(), Ty::Bool))
                    && func
                        .body
                        .locals
                        .iter()
                        .any(|d| d.index == dest.local && d.ty.int_width().is_some())
                {
                    // `<{int} as From<bool>>::from(b)` returns `b as {int}` ∈ {0, 1}. The
                    // call result is otherwise havoc'd, so `(.. + usize::from(c)) * 4` (the
                    // base64 codec capacity `(full_chunks + usize::from(rem > 0)) * 4`) is
                    // FALSELY REFUTED by the SMT lane picking an out-of-range havoc value.
                    // SOUND: a theorem of `From<bool>` for a primitive integer (the orphan
                    // rule forbids any other impl on a primitive int); gated on an int-typed
                    // dest so a non-primitive `From<bool>` newtype is correctly skipped.
                    term_facts
                        .push(Formula::Ge(Box::new(dest_var.clone()), Box::new(Formula::Int(0))));
                    term_facts
                        .push(Formula::Le(Box::new(dest_var.clone()), Box::new(Formula::Int(1))));
                } else if is_std_unwrap_or_call(callee) && args.len() == 2 {
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
                    if let Some((width, signed)) = func
                        .body
                        .locals
                        .iter()
                        .find(|d| d.index == dest.local)
                        .and_then(|d| match &d.ty {
                            Ty::Int { width, signed } => Some((*width, *signed)),
                            _ => None,
                        })
                        .filter(|&(w, _)| w < 128)
                    {
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
                } else if let Some((_, value)) =
                    wrapping_neg_call_dest_value(func, &block.terminator)
                {
                    // `dest = x.wrapping_neg()`: a total theorem of two's complement,
                    // modeled with its exact value (an `Ite`) — see
                    // `wrapping_neg_call_dest_value` for the signed/unsigned forms and
                    // width gating. As an INTERMEDIATE result the dest is pinned here;
                    // the return-slot case is pinned (Ite-lifted) in the postcondition
                    // lane so a `#[ensures]` over `x.wrapping_neg()` connects to `_0`.
                    term_facts.push(Formula::Eq(Box::new(dest_var.clone()), Box::new(value)));
                } else if let Some((_, clamped)) =
                    saturating_call_dest_value(func, &block.terminator)
                {
                    // `x.saturating_add(y)` / `x.saturating_sub(y)` as an INTERMEDIATE
                    // result (e.g. `arr[i.saturating_sub(1)]`): pin the dest to its
                    // exact clamped value so a downstream safety obligation over it is
                    // not FALSELY REFUTED by a havoc'd result. The return-slot case (a
                    // function that returns the saturating result directly, for a
                    // `#[ensures]` over it) is pinned separately under the raw `_0`
                    // name in the postcondition lane — see `saturating_call_dest_value`.
                    term_facts.push(Formula::Eq(Box::new(dest_var.clone()), Box::new(clamped)));
                } else if let Some(fact) = float_bits_call_dest_fact(func, &block.terminator) {
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
                } else if let Some(v) =
                    expect_infallible_const_int_conversion(func, callee, args, dest)
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
                        .push(Formula::Eq(Box::new(dest_var.clone()), Box::new(Formula::Int(v))));
                } else {
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
                    if let Some(bound) = crate::callee_return_upper_bound(callee) {
                        term_facts.push(Formula::Le(
                            Box::new(dest_var.clone()),
                            Box::new(Formula::Int(bound)),
                        ));
                    }
                    if let Some(lo) = crate::callee_return_lower_bound(callee) {
                        term_facts.push(Formula::Ge(
                            Box::new(dest_var.clone()),
                            Box::new(Formula::Int(lo)),
                        ));
                    }
                    if let Some(consts) = crate::callee_return_const_set(callee) {
                        let mut eqs: Vec<Formula> = consts
                            .iter()
                            .map(|c| {
                                Formula::Eq(Box::new(dest_var.clone()), Box::new(Formula::Int(*c)))
                            })
                            .collect();
                        // A single-constant callee pins the dest exactly — no
                        // degenerate one-armed disjunction.
                        term_facts.push(if eqs.len() == 1 {
                            eqs.remove(0)
                        } else {
                            Formula::Or(eqs)
                        });
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
            // SOUNDNESS gates: (1) `summary.proved` — an unproved/speculative
            // contract is never assumed; (2) `is_single_static_assignment(dest)` +
            // empty projections — the same gate the min/max facts use, so a
            // `&mut`-reassigned dest cannot leave a stale bound; (3) arity match —
            // otherwise the formal->arg rebinding would be ill-formed.
            if let Some(summaries) = summaries
                && let Some(summary) = summaries.get(callee)
                && callee_postcondition_is_injectable(func, dest, summary, args.len())
            {
                for post in rebind_callee_postconditions(func, args, dest, summary) {
                    term_facts.push(post);
                }
            }

            for f in term_facts {
                next_guards.push(version_terminator_dest_fact(
                    &sv,
                    func,
                    block,
                    &term_dest_name,
                    f,
                ));
            }

            // Trust (derived trivial-setter summary): a recognized trivial-setter
            // callee (`fn set(p: &mut u32, v: u32) { *p = v; }` — see
            // `SetterSummary` for why the recognizer IS the proof) makes the
            // call's effect on the caller TOTAL AND EXACT: the mut-borrowed
            // target equals the stored value on the success continuation.
            // Without this the `&mut` arg is havocked (correct) but the caller
            // learns nothing about its NEW value, so `assert!(a == v)` after
            // `set(&mut a, v)` demotes to runtime-checked. All gates + the
            // versioning argument live in `trivial_setter_callsite_fact`.
            if let Some((_, fact)) = trivial_setter_callsite_fact(&sv, func, block) {
                next_guards.push(fact);
            }
        }

        // Propagate to successor blocks.
        // For Assert terminators, the target is the assert-passed successor.
        // For Goto/Call/Drop, propagate unchanged.
        // For SwitchInt, propagate to all targets (semantic guards are orthogonal
        // to branch conditions).
        match &block.terminator {
            Terminator::Assert { target, .. } => {
                queue.push_back((*target, next_guards));
            }
            Terminator::Goto(target) => {
                queue.push_back((*target, next_guards));
            }
            Terminator::SwitchInt { targets, otherwise, .. } => {
                for (_, target) in targets {
                    queue.push_back((*target, next_guards.clone()));
                }
                queue.push_back((*otherwise, next_guards));
            }
            Terminator::Call { target: Some(target), .. } => {
                queue.push_back((*target, next_guards));
            }
            Terminator::Call { target: None, .. } => {}
            Terminator::Drop { target, .. } => {
                queue.push_back((*target, next_guards));
            }
            Terminator::Opaque { targets, .. } => {
                for target in targets {
                    queue.push_back((*target, next_guards.clone()));
                }
            }
            Terminator::Return | Terminator::Unreachable => {}
            // Trust: Terminator is #[non_exhaustive]; unknown variants
            // are conservatively handled by not propagating guards.
            _ => {}
        }
    }

    result
}

// Unbounded-allocation obligations. An allocation whose element count comes
// from a bounded std collection is fine; one whose count is an opaque input is
// not, and must fail closed rather than be assumed small.

use super::*;

/// Emit an `UnboundedAllocation` obligation (#nia-oom) for every bulk heap
/// allocation whose element count is not provably `< UNBOUNDED_ALLOC_ELEM_CEILING`.
///
/// The FAILURE condition is `count >= CEILING`, conjoined with the reaching block
/// definitions, argument type ranges, and live preconditions — so an allocation
/// guarded by `#[requires(n <= BOUND)]` or a dominating `if n <= BOUND { … }`
/// DISCHARGES (the solver proves the failure UNSAT), while an unguarded
/// `Vec::with_capacity(untrusted_n)` / `ensure_num_vars(n)` FAILS with a
/// counterexample. This is a SAFETY invariant over the program text (where
/// allocations sit in the CFG), NOT a termination / total-memory bound — the
/// latter is undecidable (QF_NIA ⊇ Hilbert's 10th). It converts AY's exact
/// failure mode — a 203 GB unbounded growth that OOM-killed the host — into a
/// mechanically-flagged obligation that the fixed, budget-checked code discharges.
pub(super) fn generate_unbounded_allocation_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();
    if func.body.blocks.is_empty() {
        return vcs;
    }
    // Same discharge machinery the index-bounds / overflow checks use, so an
    // allocation bounded by a DOMINATING runtime guard (`if n <= BOUND { … }`),
    // an assert-passed semantic guard, or a `#[requires]` precondition proves —
    // while a truly unguarded one fails closed with a counterexample.
    let guard_paths_map = v2_build_path_guard_map(func);
    let semantic_guards = build_semantic_guard_map(func);
    let may_reassigned = v2_may_reassigned_per_block(func);
    // Trust (lane-A CSE): one statement-version oracle for the whole function.
    let sv = StmtVersionCtx::build(func);
    let empty = FxHashSet::default();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, span, .. } = &block.terminator else {
            continue;
        };
        // Resolve the allocation's element-count formula. Two shapes:
        //  - a direct-size call (`with_capacity`/`reserve`/`resize`/`from_elem`):
        //    the count is an explicit argument; or
        //  - an iterator sink (`collect`/`from_iter`): the count is the length of
        //    the source iterator, reconstructed from a bounded chain when derivable
        //    (and skipped — not false-flagged — when it is not).
        // `single_value` marks `Box::new`/`Rc::new`/`Arc::new`: count is fixed at 1,
        // so the count ceiling is irrelevant and the AVAILABILITY byte ceiling
        // (256 MiB) is applied to the value's recoverable CONSTANT byte size — an
        // oversized single value (`Box::new([0u8; 300 MiB])`) is itself the hazard,
        // unlike a `Vec` literal count which is trusted.
        let mut single_value = false;
        let (display, count_f): (&str, Formula) = if let Some((d, size_idx)) =
            bulk_alloc_call(callee)
        {
            match args.get(size_idx) {
                Some(size_op) => (d, operand_to_formula(func, size_op)),
                // The callee IS a recognized bulk-alloc sink, but the optimized
                // MIR did not preserve a size operand at the expected index (it
                // was inlined/dissolved away). Emit a VISIBLE UnsupportedMir
                // obligation — preclassified to Unknown, never false-PROVEd —
                // instead of silently dropping the allocation. Fail closed and
                // visible, not silent.
                None => {
                    vcs.push(unsupported_mir_vc(
                        func,
                        format!("UnboundedAllocation::{d}::count-not-derivable"),
                        format!(
                            "bulk allocation `{d}` recognized but element count not \
                             derivable from optimized MIR (size operand absent at index \
                             {size_idx}); cannot prove the allocation is bounded"
                        ),
                        span.clone(),
                    ));
                    continue;
                }
            }
        } else if let Some(d) = single_value_alloc_call(callee) {
            // `Box::new`/`Rc::new`/`Arc::new`: a single heap value of type `T`. There
            // is NO count operand — the count is exactly 1 — so the count ceiling can
            // never fire; the hazard is an OVERSIZED `T` caught by the byte terms
            // below (`alloc_element_byte_size` sizes `T` from the value operand, the
            // `from_elem`-style path). A small `Box::new(x)` recovers a tiny stride and
            // emits no obligation (drop-in preserved); a `Box::new([0u8; 1 << 40])`
            // capacity-overflows isize::MAX and fails closed.
            single_value = true;
            (d, Formula::Int(1))
        } else if let Some(d) = raw_alloc_call(callee) {
            // `alloc::alloc(layout)` / `Allocator::allocate(layout)`: the size lives
            // inside an opaque `Layout`, not derivable from optimized MIR. Surface a
            // VISIBLE UnsupportedMir (Unknown, never false-PROVEd) rather than silently
            // waving a genuine unbounded raw allocation through.
            vcs.push(unsupported_mir_vc(
                func,
                format!("UnboundedAllocation::{d}::size-not-derivable"),
                format!(
                    "raw allocation `{d}` recognized but the allocation size is carried \
                     in an opaque `Layout` value, not derivable from optimized MIR; \
                     cannot prove the allocation is bounded"
                ),
                span.clone(),
            ));
            continue;
        } else if is_collect_sink(callee) {
            let Some(iter_op) = args.first() else {
                continue;
            };
            // SOUND skip: collecting from an already-materialized std collection
            // (`.keys()/.values()/.iter()/.into_iter()/.drain()`, reached through
            // length-non-increasing adaptors) yields at most `source.len()`
            // elements. The source collection's own allocation was itself gated by
            // this pass when it was built, so this collect introduces NO new
            // unbounded hazard — the OOM obligation, if any, lives at the source
            // allocation, not here. Generative sources (ranges, `repeat`, custom
            // iterators — the real OOM shapes like `(0..1<<28).collect()`) are NOT
            // matched and remain gated by `iter_collect_count` below.
            if collect_source_is_bounded_std_collection(func, iter_op, 0) {
                continue;
            }
            match iter_collect_count(func, iter_op) {
                Some(c) => ("Iterator::collect", c),
                // A `collect`/`from_iter` sink whose source length is not
                // statically recoverable from the optimized MIR. Emit a VISIBLE
                // UnsupportedMir obligation (Unknown, never false-PROVEd) rather
                // than silently waving the allocation through.
                None => {
                    vcs.push(unsupported_mir_vc(
                        func,
                        "UnboundedAllocation::Iterator::collect::count-not-derivable".to_string(),
                        "bulk allocation recognized (collect/from_iter) but element \
                         count not derivable from optimized MIR; cannot prove the \
                         allocation is bounded"
                            .to_string(),
                        span.clone(),
                    ));
                    continue;
                }
            }
        } else {
            continue;
        };
        // Capacity-overflow element stride: `size_of::<T>()` for the allocation,
        // recovered from the element operand (from_elem) or the callee turbofish
        // (the `Vec` methods that erase T to u8). Used to catch the MULTI-BYTE
        // capacity overflow `count * stride >= isize::MAX` that the count-only
        // ceiling misses (SOUNDNESS, hunt-11: `Vec::<[u8; 1<<40]>::with_capacity(n)`
        // with `n < 2^27` panicked "capacity overflow" yet was kernel-certified).
        let cap_stride = alloc_element_byte_size(func, display, callee, args);
        // A literal constant size STRICTLY BELOW the ceiling is trivially bounded —
        // BUT a multi-byte element can capacity-overflow even at a small count, so
        // only skip when the BYTE product is also safe. The boundary itself is NOT
        // safe: the nn-dsl OOM allocated exactly `1 << 28` elements (== the ceiling),
        // so `<=` would wave the real bug through. Use `<` so exactly-at-ceiling
        // falls through to the VC.
        // A single-byte (`u8`) constant single value can never be an availability
        // hazard, so the byte budget below also clears it; only skip a single-value
        // alloc when its byte size is recoverable AND below the availability ceiling,
        // otherwise fall through so the byte terms decide. For the count-based sinks
        // (`single_value == false`) the original count+capacity skip is unchanged.
        let const_byte_safe = |n: i128| -> bool {
            cap_stride
                .is_none_or(|s| n.checked_mul(s).is_some_and(|b| b < ALLOC_CAPACITY_OVERFLOW_BYTES))
        };
        if single_value {
            // count is exactly 1: the count ceiling never applies. Bounded iff the
            // value's recoverable byte size is below BOTH the availability ceiling
            // (256 MiB) and capacity-overflow (isize::MAX); unrecoverable byte size
            // (`cap_stride == None`, an opaque `T`) is bounded — nothing to flag.
            let bounded = cap_stride.is_none_or(|s| {
                s < UNBOUNDED_ALLOC_BYTE_CEILING && s < ALLOC_CAPACITY_OVERFLOW_BYTES
            });
            if bounded {
                continue;
            }
        } else {
            match &count_f {
                Formula::Int(n) if *n < UNBOUNDED_ALLOC_ELEM_CEILING && const_byte_safe(*n) => {
                    continue;
                }
                Formula::UInt(n)
                    if (*n as i128) < UNBOUNDED_ALLOC_ELEM_CEILING
                        && const_byte_safe(*n as i128) =>
                {
                    continue;
                }
                _ => {}
            }
        }
        let count_disp = count_f.to_smtlib();
        // Failure condition: the requested element count REACHES OR EXCEEDS the
        // ceiling (`>=`, not `>`). An allocation of exactly the ceiling is the nn
        // OOM and must fail closed, not slip through the off-by-one at the boundary.
        //
        // Byte-aware tightening, `vec![x; n]` / from_elem ONLY: the element VALUE
        // is a real typed operand, so size T exactly (the only MIR allocation
        // whose element type is recoverable — RawVec<T> erases T to u8 elsewhere).
        // For a SYMBOLIC count of a multi-byte element, ALSO fail when
        // `elem_size * count` reaches the AVAILABILITY byte budget (256 MiB, far
        // below the element ceiling). Symbolic-only ⇒ a constant that already
        // cleared the element skip stays green: never a false ground hard error on
        // a legal `vec![0u64; 40_000_000]`.
        let count_is_const = matches!(count_f, Formula::Int(_) | Formula::UInt(_));
        // AVAILABILITY byte budget (256 MiB): a SYMBOLIC multi-byte allocation whose
        // element stride is recoverable, for ANY bulk-alloc display
        // (with_capacity/reserve/resize/from_elem) — unified to match the original
        // from_elem policy. Catches the realistic OOM where a moderate element
        // (`[u8; 4096]`) * a weakly-bounded count (`< 2^28`) is a 1 TiB allocation the
        // count-only ceiling waved through (SOUNDNESS, hunt-11). Symbolic-only ⇒ a
        // constant that cleared the element skip stays green (the explicit literal is
        // trusted; never a false ground hard error on a legal `vec![0u64; 40_000_000]`).
        // A single-value alloc has a CONSTANT (type-derived) byte size, but unlike a
        // trusted `Vec` literal count an oversized single value IS the hazard, so the
        // availability ceiling applies to it even though the count is const.
        let avail_stride: Option<i128> =
            if single_value || !count_is_const { cap_stride } else { None };
        let elem_ceiling = Formula::Ge(
            Box::new(count_f.clone()),
            Box::new(Formula::Int(UNBOUNDED_ALLOC_ELEM_CEILING)),
        );
        // Disjuncts of the FAILURE condition. The count ceiling (availability) is
        // always present; the AVAILABILITY byte term (256 MiB, symbolic multi-byte,
        // ALL displays) and the CAPACITY-OVERFLOW byte term (`stride * count >=
        // isize::MAX`, a real runtime panic, ALL displays incl. const counts) are
        // added when the stride is recoverable. Purely ADDITIVE — only ever turns
        // PROVED -> FAILED, never the reverse, so a genuinely-bounded allocation
        // (`stride * count < isize::MAX` and `< 256 MiB`) is unaffected; a stride-1
        // (`u8`) allocation gets neither (filtered `> 1`), exactly as before.
        let mut disjuncts = vec![elem_ceiling];
        if let Some(stride) = avail_stride {
            disjuncts.push(Formula::Ge(
                Box::new(Formula::Mul(Box::new(Formula::Int(stride)), Box::new(count_f.clone()))),
                Box::new(Formula::Int(UNBOUNDED_ALLOC_BYTE_CEILING)),
            ));
        }
        if let Some(stride) = cap_stride {
            disjuncts.push(Formula::Ge(
                Box::new(Formula::Mul(Box::new(Formula::Int(stride)), Box::new(count_f.clone()))),
                Box::new(Formula::Int(ALLOC_CAPACITY_OVERFLOW_BYTES)),
            ));
        }
        let body = if disjuncts.len() == 1 {
            disjuncts.pop().expect("non-empty")
        } else {
            Formula::Or(disjuncts)
        };
        let mut formula = v2_formula_with_block_defs(func, block, body);
        formula = conjoin_arg_type_ranges(func, formula);
        // verifier-precision: bound NON-parameter integer locals/temps too (sibling of
        // arg ranges). SOUNDNESS: DROP-ONLY — a true in-type-range fact.
        formula = conjoin_local_type_ranges(func, formula);
        // Lever A: bound fixed-width-integer datatype FIELDS too (same sound bound).
        formula = conjoin_datatype_field_ranges(func, formula);
        // Trust S2c (exemption): the whole-VC version rename runs FIRST, on the body
        // + same-block block-defs only. The THREADED facts (dominating path guards +
        // assert-passed semantic guards) are conjoined AFTER, EXEMPT from the rename —
        // so a guard's bare ENTRY-param read (`n` in `if n <= BOUND`) stays bare and
        // is name-disjoint from a reassigned body read (`n#s2_0`), instead of being
        // renamed onto it and false-PROVING a real OOM. A LIVE entry read (bare on
        // both sides) still connects; an establish-versioned semantic-guard subject
        // (`c#s0_0`) connects to the body's statement-granular reference.
        let killed = may_reassigned.get(&block.id).unwrap_or(&empty);
        formula =
            conjoin_preconditions_versioned(func, block.id, &func.preconditions, killed, formula);
        // Dominating control-flow guards (`if n <= BOUND`) — exempt.
        if let Some(block_guard_paths) = guard_paths_map.get(&block.id) {
            formula = v2_formula_with_path_guards(func, &sv, block_guard_paths, formula);
        }
        // Assert-passed semantic guards — exempt.
        if let Some(sem_guards) = semantic_guards.get(&block.id)
            && !sem_guards.is_empty()
        {
            let mut conjuncts = sem_guards.clone();
            conjuncts.push(formula);
            formula = Formula::And(conjuncts);
        }
        // Function-wide invariant facts (min/max result bounds, cast bounds, …)
        // — exempt like the guards (bare SSA-gated names). THIS lane's verdict
        // convention is verified "SAT ⇒ violation" (the formula IS the failure
        // condition), so conjoining unconditionally-true facts only removes
        // counterexamples real traces cannot exhibit — `h = ….min(16)` finally
        // bounds a collect count of `h`. Per-lane by design: the OUTERMOST
        // conjunction regressed and was reverted (see
        // vcgen-lane-convention-heterogeneity; commit c33e2ff20c).
        {
            let facts = build_global_invariant_facts(func);
            if !facts.is_empty() {
                let mut conjuncts = facts;
                conjuncts.push(formula);
                formula = Formula::And(conjuncts);
            }
        }
        // Collapse SSA locals' version tokens so the facts' bare names bind the
        // body reads (identity for single-write locals; parameter-aware gate).
        formula = normalize_ssa_version_tokens(func, &formula);
        vcs.push(VerificationCondition {
            kind: VcKind::UnboundedAllocation {
                callee: display.to_string(),
                count: count_disp,
                detail: format!(
                    "bulk allocation may reach or exceed {UNBOUNDED_ALLOC_ELEM_CEILING} elements: \
                     bound the size (e.g. `#[requires(n < BOUND)]` or a dominating check) \
                     or route it through a budget-checked allocator that fails closed"
                ),
            },
            function: func.name.clone().into(),
            location: span.clone(),
            formula,
            contract_metadata: None,
        });
    }
    vcs
}

/// The method tail of a callee path, stripped of generic noise (mirrors
/// `bulk_alloc_call`'s tail extraction).
pub(super) fn callee_tail(callee: &str) -> &str {
    // Turbofish-robust (see `method_tail`): `xs.collect::<Vec<_>>()` presents a
    // trailing `::<Vec<_>>` that a naive `rsplit("::")` would mistake for the
    // method name, silently disabling the collect/from_iter alloc gate.
    method_tail(callee)
}

/// Recognize an iterator sink that allocates an owned container proportional to
/// the source iterator's length, with NO explicit size operand on the call:
/// `Iterator::collect`, `FromIterator::from_iter`. The dominant way a giant
/// `Vec` is materialized — and the exact shape of the nn-dsl OOM
/// (`(0..1<<28).map(..).collect()`).
pub(super) fn is_collect_sink(callee: &str) -> bool {
    matches!(callee_tail(callee), "collect" | "from_iter")
}

/// Adaptors that preserve the source iterator's length, so the collected count
/// equals the count of their own source (recurse through them).
pub(super) fn is_len_preserving_adaptor(tail: &str) -> bool {
    matches!(
        tail,
        "map" | "filter_map" | "inspect" | "enumerate" | "copied" | "cloned" | "rev" | "by_ref"
    )
}

/// The (single, unprojected) local a value operand reads, if any.
pub(super) fn operand_local(op: &Operand) -> Option<usize> {
    match op {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => Some(p.local),
        _ => None,
    }
}

/// Find the defining statement/terminator of `local` within `func` — the
/// `Rvalue` that assigns it, or the `Call` whose destination it is.
pub(super) fn local_def(func: &VerifiableFunction, local: usize) -> Option<LocalDef<'_>> {
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt
                && place.local == local
                && place.projections.is_empty()
            {
                return Some(LocalDef::Rvalue(rvalue));
            }
        }
        if let Terminator::Call { dest, func: callee, args, .. } = &block.terminator
            && dest.local == local
            && dest.projections.is_empty()
        {
            return Some(LocalDef::Call { callee, args });
        }
    }
    None
}

/// Reconstruct the element count feeding a `collect`/`from_iter` sink when it is
/// statically derivable: a `Range` aggregate (`a..b` ⇒ `b - a`, constant-folded
/// so the ceiling skip still applies), optionally behind length-preserving
/// adaptors (`map`/`filter_map`/…) or capped by `take(n)`. Returns `None` when the
/// length is not recoverable — SOUND: emit no obligation rather than a false
/// positive on every `collect` (which would break drop-in Rust compatibility).
pub(super) fn iter_collect_count(func: &VerifiableFunction, iter_op: &Operand) -> Option<Formula> {
    iter_collect_count_rec(func, iter_op, 0)
}

pub(super) fn iter_collect_count_rec(
    func: &VerifiableFunction,
    iter_op: &Operand,
    depth: usize,
) -> Option<Formula> {
    if depth > 8 {
        return None;
    }
    let local = operand_local(iter_op)?;
    match local_def(func, local)? {
        LocalDef::Rvalue(Rvalue::Aggregate(AggregateKind::Adt { name, .. }, ops))
            if name.contains("Range") =>
        {
            // `a..b` ⇒ Aggregate(Range, [start, end]); count = end - start.
            let start = ops.first()?;
            let end = ops.get(1)?;
            let start_f = operand_to_formula(func, start);
            let end_f = operand_to_formula(func, end);
            match (&start_f, &end_f) {
                (Formula::Int(s), Formula::Int(e)) => Some(Formula::Int(e - s)),
                _ => Some(Formula::Sub(Box::new(end_f), Box::new(start_f))),
            }
        }
        // `let it = <iter>; it.collect()` — chase the move/copy alias.
        LocalDef::Rvalue(Rvalue::Use(inner)) => iter_collect_count_rec(func, inner, depth + 1),
        LocalDef::Call { callee, args } => {
            let tail = callee_tail(callee);
            if is_len_preserving_adaptor(tail) {
                // `src.map(f)` etc. — adaptor receiver is arg 0.
                iter_collect_count_rec(func, args.first()?, depth + 1)
            } else if tail == "take" {
                // `src.take(n)` — at most `n` elements (receiver arg 0, n arg 1).
                args.get(1).map(|n| operand_to_formula(func, n))
            } else if tail == "repeat_n" {
                // `core::iter::repeat_n(x, n).collect()` — a free fn yielding EXACTLY
                // `n` elements (element arg 0, count arg 1). The dominant constructor
                // for a runtime-sized homogeneous Vec that is not `vec![x; n]`.
                // (`repeat(x)`/`repeat_with(f)` are unbounded and only become a
                // sink behind a `take(n)`, already handled above.)
                args.get(1).map(|n| operand_to_formula(func, n))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// True iff `iter_op` is an iterator over an ALREADY-materialized std collection,
/// reached only through length-non-increasing adaptors. Such an iterator yields at
/// most `source.len()` elements, so collecting it allocates no more than the
/// source collection (whose own allocation this pass already gated when it was
/// built) — it is therefore bounded and introduces no NEW unbounded-allocation
/// hazard. Conservative: any unrecognized step returns `false` (stays gated).
pub(super) fn collect_source_is_bounded_std_collection(
    func: &VerifiableFunction,
    iter_op: &Operand,
    depth: usize,
) -> bool {
    if depth > 8 {
        return false;
    }
    let Some(local) = operand_local(iter_op) else {
        return false;
    };
    match local_def(func, local) {
        // `let it = <iter>; it.collect()` — chase the move/copy alias.
        Some(LocalDef::Rvalue(Rvalue::Use(inner))) => {
            collect_source_is_bounded_std_collection(func, inner, depth + 1)
        }
        Some(LocalDef::Call { callee, args }) => {
            let tail = callee_tail(callee);
            if is_std_collection_iter_producer(callee, tail)
                || is_str_view_iter_producer(callee, tail)
            {
                return true;
            }
            // `a.chain(b)` yields `a.len() + b.len()` — bounded iff BOTH sides are
            // bounded collection sources (the sum of two already-gated allocations
            // is itself bounded). Receiver is arg 0, the chained iterator arg 1.
            if tail == "chain" {
                return args
                    .first()
                    .is_some_and(|a| collect_source_is_bounded_std_collection(func, a, depth + 1))
                    && args.get(1).is_some_and(|b| {
                        collect_source_is_bounded_std_collection(func, b, depth + 1)
                    });
            }
            // Walk back through length-NON-INCREASING adaptors (each yields
            // `<= source` elements), receiver is arg 0.
            if is_len_preserving_adaptor(tail)
                || matches!(tail, "filter" | "take" | "skip" | "step_by" | "take_while")
            {
                if let Some(recv) = args.first() {
                    return collect_source_is_bounded_std_collection(func, recv, depth + 1);
                }
            }
            false
        }
        _ => false,
    }
}

/// An iterator-producer method that yields at most the receiver collection's
/// current length, matched by FULL callee path to a std collection so a custom
/// `iter()` (which could be unbounded) is never mistaken for one. Generative
/// producers (`Range`, `repeat`, `repeat_with`) are intentionally excluded.
pub(super) fn is_std_collection_iter_producer(callee: &str, tail: &str) -> bool {
    matches!(
        tail,
        "iter"
            | "iter_mut"
            | "into_iter"
            | "drain"
            | "keys"
            | "values"
            | "values_mut"
            | "into_keys"
            | "into_values"
    ) && (callee.contains("alloc::vec::")
        || callee.contains("std::vec::")
        || callee.contains("alloc::slice::")
        || callee.contains("core::slice::")
        || callee.contains("std::collections::")
        || callee.contains("alloc::collections::")
        || callee.contains("hash_map::")
        || callee.contains("hash_set::")
        || callee.contains("btree_map::")
        || callee.contains("btree_set::")
        || callee.contains("vec_deque::")
        || callee.contains("binary_heap::")
        || callee.contains("linked_list::"))
}

/// A str-view iterator producer (`chars`/`char_indices`/`bytes`/`encode_utf16`) on
/// a `str`/`String` receiver. WHY bounded: each yields a count `<=` the receiver's
/// UTF-8 byte length `L` (`bytes` == L; `chars`/`char_indices` <= L; `encode_utf16`
/// <= L since a UTF-16 unit count never exceeds the UTF-8 byte count). The `&str`/
/// `String` is an already-materialized input, so collecting a non-amplifying view of
/// it is linear-in-input — the SAME bounded-source invariant that already waves
/// through `Vec::iter().map(..).collect()` (a stride blowup), only strictly weaker.
pub(super) fn is_str_view_iter_producer(callee: &str, tail: &str) -> bool {
    matches!(tail, "chars" | "char_indices" | "bytes" | "encode_utf16")
        && (callee.contains("::str::")
            || callee.contains("alloc::string::")
            || callee.contains("std::string::"))
}

/// Summary-aware rvalue-safety generation: the array/slice INDEX-BOUNDS lane
/// consults the summary-aware guard map, so a proved callee postcondition like
/// `parse ensures _0 < len` can discharge `arr[parse(input)]`. `None` selects the
/// canonical non-summary behavior.
pub(super) fn generate_v2_rvalue_safety_vcs_impl(
    func: &VerifiableFunction,
    summaries: Option<&crate::modular::SummaryDatabase>,
) -> Vec<VerificationCondition> {
    let guard_paths_map = v2_build_path_guard_map(func);
    // Trust (lane-A CSE): one statement-version oracle for the whole function.
    let sv = StmtVersionCtx::build(func);
    let semantic_guards = match summaries {
        Some(s) => build_semantic_guard_map_with_summaries(func, s),
        None => build_semantic_guard_map(func),
    };
    let bounds_guard_targets = v2_bounds_guard_targets(func);

    let mut block_vcs: Vec<(BlockId, VerificationCondition)> = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place, rvalue, span } = stmt else {
                continue;
            };
            // A native `BoundsCheck` assert dominating this block already
            // discharges the index obligation. Skip both the rvalue-side
            // projection (read / `&arr[i]` / `CopyForDeref`) and the
            // destination-side projection (`arr[i] = v`) so we don't
            // double-emit a VC the assert already covers.
            let native_bounds_guarded = bounds_guard_targets.contains(&block.id);
            if native_bounds_guarded && rvalue_safety::is_direct_projection_load(rvalue) {
                continue;
            }
            // verifier-perf: borrowed resolve — `check_rvalue_safety` only INSPECTS the
            // destination type (it takes `Option<&Ty>`), so never clone the (possibly fat
            // recursive-ADT) declared root for the dest place.
            let dest_ty = crate::place_ty_cow(func, place);
            let mut stmt_vcs = Vec::new();
            rvalue_safety::check_rvalue_safety(
                func,
                block,
                rvalue,
                dest_ty.as_deref(),
                span,
                &mut stmt_vcs,
            );
            // STORE-side index bounds: `arr[i] = v` carries the `Index(i)`
            // projection on the assignment *destination*, which the rvalue
            // walk above never inspects. Bounds-check it with the same builder
            // (and same native-assert suppression) so an out-of-bounds write
            // is no longer reported safe.
            if !(native_bounds_guarded && rvalue_safety::place_needs_bounds_check(place)) {
                rvalue_safety::check_place_index_bounds(func, place, span, &mut stmt_vcs);
            }
            block_vcs.extend(stmt_vcs.into_iter().map(|vc| (block.id, vc)));
        }
    }

    // Trust S2c (exemption): path + semantic guards conjoined AFTER the rename (moved below).

    // Range-iterator yield facts (see `generate_v2_safety_vcs`): discharge an
    // `a[i]` bounds VC reached through a `for i in start..end` desugaring.
    let range_yield_guards = build_range_yield_guard_map(func);
    for (block_id, vc) in &mut block_vcs {
        if let Some(facts) = range_yield_guards.get(block_id)
            && !facts.is_empty()
        {
            let mut conjuncts = facts.clone();
            conjuncts.push(vc.formula.clone());
            vc.formula = Formula::And(conjuncts);
        }
    }
    let slice_iter_yield_guards = build_slice_iter_yield_guard_map(func);
    for (block_id, vc) in &mut block_vcs {
        if let Some(facts) = slice_iter_yield_guards.get(block_id)
            && !facts.is_empty()
        {
            let mut conjuncts = facts.clone();
            conjuncts.push(vc.formula.clone());
            vc.formula = Formula::And(conjuncts);
        }
    }

    // Trust: conjoin the function's declared preconditions onto each
    // rvalue-safety VC. This mirrors what `generate_v2_safety_vcs` does
    // for arithmetic/assert-derived VCs and is needed for VCs like
    // IndexOutOfBounds / CastOverflow whose safety depends on a
    // precondition like `idx < len` or `x <= u32::MAX`. Drop a precondition
    // at any block that may have reassigned one of its free variables, so a
    // stale `idx < len` cannot vacuously discharge an out-of-bounds index.
    // Trust: P-B — the version rename runs UNCONDITIONALLY (not gated on
    // preconditions). It must, so an establish-versioned threaded fact's LIVE
    // successor read gets renamed to the matching token (a bare body would never
    // connect to a `#`-versioned fact). With empty preconditions it is a
    // verdict-preserving alpha-rename.
    {
        let may_reassigned = v2_may_reassigned_per_block(func);
        let empty = FxHashSet::default();
        for (block_id, vc) in &mut block_vcs {
            let killed = may_reassigned.get(block_id).unwrap_or(&empty);
            vc.formula = conjoin_preconditions_versioned(
                func,
                *block_id,
                &func.preconditions,
                killed,
                vc.formula.clone(),
            );
        }
    }

    // Trust S2c (exemption): path guards + semantic guards conjoined AFTER the rename.
    for (block_id, vc) in &mut block_vcs {
        if let Some(block_guard_paths) = guard_paths_map.get(block_id) {
            vc.formula =
                v2_formula_with_path_guards(func, &sv, block_guard_paths, vc.formula.clone());
        }
    }
    for (block_id, vc) in &mut block_vcs {
        if let Some(sem_guards) = semantic_guards.get(block_id)
            && !sem_guards.is_empty()
        {
            let mut conjuncts = sem_guards.clone();
            conjuncts.push(vc.formula.clone());
            vc.formula = Formula::And(conjuncts);
        }
    }

    block_vcs.into_iter().map(|(_, vc)| vc).collect()
}

pub(super) fn v2_is_unsupported_mir_vc(vc: &VerificationCondition) -> bool {
    matches!(vc.kind, VcKind::UnsupportedMir { .. })
}

pub(super) fn v2_recognized_assert_proof_gap_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    target: BlockId,
    assert_kind: String,
    cond: &Operand,
    expected: bool,
    span: &SourceSpan,
) -> VerificationCondition {
    unsupported_mir_vc(
        func,
        format!("RecognizedSafetyAssertProofGap({assert_kind})"),
        format!(
            "bb{} -> bb{}: recognized safety assert builder returned no VC; cond={cond:?}, expected={expected}; malformed or unsupported evidence must remain an explicit proof gap",
            block.id.0, target.0
        ),
        span.clone(),
    )
}

/// Build a real overflow VC for `CheckedBinaryOp(op, lhs, rhs)` feeding an
/// `Assert { Overflow(op) }` terminator.
///
/// Formula: `input_range(lhs) AND input_range(rhs) AND NOT in_range(lhs op rhs)`.
/// SAT iff the operation overflows for some in-range inputs → test is_failed().
pub(super) fn v2_build_overflow_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    op: BinOp,
    span: &SourceSpan,
) -> Option<VerificationCondition> {
    // Find the CheckedBinaryOp assignment in this block that matches `op`.
    let (lhs, rhs) = block.stmts.iter().find_map(|stmt| {
        let Statement::Assign { rvalue: Rvalue::CheckedBinaryOp(stmt_op, l, r), .. } = stmt else {
            return None;
        };
        if *stmt_op == op { Some((l, r)) } else { None }
    })?;
    // The checked op's overflow is asserted at the block's Assert terminator, so
    // conjoin whole-block defs (`stmt_index = None`).
    v2_build_overflow_vc_for_operands(func, block, op, lhs, rhs, span, None)
}

/// Build an ArithmeticOverflow VC for `lhs OP rhs` (op in Add/Sub/Mul) from the
/// operands directly. Shared by the CheckedBinaryOp path (whole-block defs,
/// `stmt_index = None`) and the direct `Rvalue::BinaryOp` path (defs before the
/// statement, `stmt_index = Some`). Add/Sub use the LIA range encoding (keeping
/// conjoined preconditions/guards/block-defs so a bounded op PROVES); Mul uses
/// the decidable bitvector encoding. See the soundness/completeness notes below.
// Trust: reusable (ungated, pub(crate)) — the hardened panic_boundary path also
// needs these parameter type-range bounds (otherwise it over-refutes a
// provably-safe widened add like `a as u16 + b as u16`). Pure formula
// construction from the function's parameter types.
/// Conjoin type-range bounds for every function PARAMETER that appears free in
/// `formula`. The Add/Sub operands already carry their own
/// `input_range_constraint`, but a parameter that reaches the VC only through a
/// conjoined block definition (e.g. `hi`, reachable via `_3 == hi - lo`) is
/// otherwise unconstrained — the solver then fabricates a spurious overflow by
/// choosing an out-of-range value for it (the `safe_midpoint` `lo + (hi-lo)/2`
/// false-FAIL). MIR locals `1..=arg_count` are the parameters; each holds a
/// typed input value and is therefore UNCONDITIONALLY within its type range, so
/// conjoining these bounds is sound: it refutes only spurious counterexamples,
/// never a real overflow (whose witness also respects the parameter type
/// ranges). Restricted to parameters on purpose — bounding an intermediate
/// result would instead *assume* its producing op did not overflow, which is
/// only the separate per-statement VC's business.
pub(crate) fn conjoin_arg_type_ranges(func: &VerifiableFunction, formula: Formula) -> Formula {
    // Bound EVERY integer parameter unconditionally (not only those currently
    // free): a parameter that the VC references only through a *cross-block*
    // definition (e.g. `hi`, reached via `_3 == hi - lo` from an earlier block)
    // is conjoined onto this formula only later, after this point — so filtering
    // on the current free set would miss exactly the variable that needs the
    // bound. `in_range(p)` for an unreferenced parameter is a harmless true fact;
    // once the cross-block def connects `p`, the bound constrains it. Sound: a
    // parameter always holds a value within its type range.
    let mut bounds = Vec::new();
    for decl in &func.body.locals {
        if decl.index < 1 || decl.index > func.body.arg_count {
            continue; // local 0 is the return slot; > arg_count are temporaries
        }
        let Some(width) = decl.ty.int_width() else {
            continue;
        };
        let name = decl.name.clone().unwrap_or_else(|| format!("_{}", decl.index));
        bounds.push(crate::range::input_range_constraint(
            &Formula::Var(name, trust_types::Sort::Int),
            width,
            decl.ty.is_signed(),
        ));
    }
    if bounds.is_empty() {
        return formula;
    }
    bounds.push(formula);
    Formula::And(bounds)
}

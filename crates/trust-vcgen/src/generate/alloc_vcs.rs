// Unbounded-allocation obligations. An allocation whose element count comes
// from a bounded std collection is fine; one whose count is an opaque input is
// not, and must fail closed rather than be assumed small.

use trust_types::live_source_bound::LiveSourceCount;

use super::*;

/// Emit allocation safety obligations for bulk heap allocation. A nonzero
/// request without an exact element stride emits a visible layout Unknown before
/// constant-count elision or solver discharge. Literal zero remains separate.
///
/// With a known stride, the failure formula includes the target byte-capacity
/// limit and the existing element-count availability policy, conjoined with
/// reaching block definitions, argument ranges and live preconditions. Proving a
/// count-only availability bound cannot establish an unknown byte-capacity bound.
/// This is a local safety obligation, not a termination or total-memory proof.
pub(super) fn generate_unbounded_allocation_vcs(
    func: &VerifiableFunction,
) -> Vec<VerificationCondition> {
    generate_unbounded_allocation_vcs_with_width(func, crate::target_pointer_bits())
}

/// [`generate_unbounded_allocation_vcs`] for an explicit target pointer width, so
/// the width-dependent bounded-source grant can be tested without touching the
/// process-wide value (see [`bounded_source_grant_applies_at_width`]).
///
/// Trust (merge 2026-10-14): the lane now reads TWO width facts — the process-wide
/// [`crate::target_pointer_bits`] (local main's D12 gate, defaulting to 64) and
/// upstream's session fact ([`AllocTarget::for_session`], ALLOC-WIDTH-1, defaulting
/// to the narrowest modeled width). An explicit width is installed as both.
#[cfg(test)]
pub(super) fn generate_unbounded_allocation_vcs_at(
    func: &VerifiableFunction,
    pointer_bits: u32,
) -> Vec<VerificationCondition> {
    crate::with_target_pointer_bits(Some(pointer_bits), || {
        generate_unbounded_allocation_vcs_with_width(func, pointer_bits)
    })
}

/// The lane itself. `pointer_bits` feeds only the D12 bounded-source width gate
/// ([`bounded_source_grant_applies_at_width`]); every capacity line reads the
/// session target ([`AllocTarget::for_session`]). A grant needs both.
fn generate_unbounded_allocation_vcs_with_width(
    func: &VerifiableFunction,
    pointer_bits: u32,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();
    let _analysis_memo = crate::gen_work_memo_scope_if_unscoped();
    let _func_scope = super::FuncAnalysisScope::enter(func);
    if func.body.blocks.is_empty() || !super::terminator_presence_for(func).has_call {
        return vcs;
    }
    // Same discharge machinery the index-bounds / overflow checks use, so an
    // allocation bounded by a DOMINATING runtime guard (`if n <= BOUND { … }`),
    // an assert-passed semantic guard, or a `#[requires]` precondition proves —
    // while a truly unguarded one fails closed with a counterexample.
    // Built lazily on the first block that actually emits an `UnboundedAllocation`
    // formula, so functions with no non-trivial allocation obligation skip these
    // whole-body analyses entirely.
    let guard_paths_map: std::cell::OnceCell<std::rc::Rc<PathGuardMap>> =
        std::cell::OnceCell::new();
    let semantic_guards: std::cell::OnceCell<std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>>> =
        std::cell::OnceCell::new();
    let primitive_decimal_guards: std::cell::OnceCell<
        std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>>,
    > = std::cell::OnceCell::new();
    let sv: std::cell::OnceCell<std::rc::Rc<StmtVersionCtx>> = std::cell::OnceCell::new();
    let global_facts: std::cell::OnceCell<std::rc::Rc<RowGlobalFacts>> =
        std::cell::OnceCell::new();
    // (No per-block may-reassigned KILL set: `conjoin_preconditions_versioned`
    // ignores it — the version rename kills staleness — and materialising it was a
    // Θ(blocks × names) whole-CFG fixpoint.)
    let empty = FxHashSet::default();
    // Trust (ALLOC-WIDTH-1, 2026-10-08): every capacity line below is the
    // compilation target's own `isize::MAX`, and a live receiver is bounded only on
    // a 64-bit target ([`AllocTarget`]). `Err` is a pointer width this lane does not
    // model: each row is then a visible Unknown.
    let target = AllocTarget::for_session();
    let live_axiom = target.is_ok_and(|target| target.live_axiom);
    let mut fn_sym: Option<Symbol> = None;
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, span, callee_key, .. } = &block.terminator
        else {
            continue;
        };
        // Trust (ALLOC-RECEIVER-1, 2026-10-08): the row's count is ADDED to what a
        // live receiver already holds — `reserve(additional)`, a counted `extend`,
        // a counted `collect_into(&mut dest)` — rather than being the whole request.
        // RawVec asks for `(len + additional) * stride` and hashbrown resizes past
        // `items + additional`, so the capacity term charges the receiver too
        // ([`AllocTarget::live_receiver_items`]). Until 2026-10-08 these rows charged
        // `stride * additional` alone, and only the 256 MiB byte atom (deleted the
        // same day) stood between them and a false proof: with one live
        // `MaybeUninit<[u8; 1 << 35]>` element, `v.reserve(n)` under `n < 2^28` was
        // PROVED and panicked "capacity overflow" (review probe `probe_reserve.rs`;
        // `reserve_exact` and `extend(repeat_with(..).take(n))` likewise).
        let mut receiver_live = false;
        // Resolve the allocation's element-count formula. Two shapes:
        //  - a direct-size call (`with_capacity`/`reserve`/`resize`/`from_elem`):
        //    the count is an explicit argument; or
        //  - an iterator sink (`collect`/`from_iter`): the count is the length of
        //    the source iterator, reconstructed from a bounded chain when derivable
        //    (and skipped — not false-flagged — when it is not).
        // `single_value` marks `Box::new`/`Rc::new`/`Arc::new`: count is fixed at 1,
        // so the count ceiling is irrelevant and the value's recoverable CONSTANT
        // byte size is judged against the target's object limit (`isize::MAX` at
        // its pointer width, [`AllocTarget`]) alone — the 256 MiB availability
        // ceiling once applied here was deleted (ALLOC-BYTE-1, see `generate/mod.rs`).
        let mut single_value = false;
        // The direct-size arm's size operand, kept for the W4 ALLOC-LEN
        // classification below (`alloc_len::len_derived_allocation`).
        let mut direct_size_op: Option<&Operand> = None;
        let call_tail = callee_tail(callee);
        let is_collect_tail = matches!(call_tail, "collect" | "from_iter");
        let in_std_iter_ns = matches!(call_tail, "unzip" | "collect_into" | "extend")
            && (callee.contains("core::iter::") || callee.contains("std::iter::"));
        let bulk_dispatch = super::alloc_bounds::AllocCallDispatch::bulk_with_tail(call_tail);
        let (display, count_f): (&str, Formula) = if let Some((d, size_idx)) = bulk_dispatch {
            match args.get(size_idx) {
                // Trust (fa/struct-alloc, 2026-10-02): `bulk_alloc_call` matches the
                // METHOD TAIL, so a user `PtySession::resize(&self, size: PtySize)` is
                // read as `<[T]>::resize` and its by-value struct argument as the
                // element count. Every count this arm models — `with_capacity*`,
                // `reserve*`, `extend_reserve`, `resize*`, `from_elem` — is a `usize`
                // in std, so an operand whose type is KNOWN and is not an integer is
                // not an element count: the count-ceiling row it minted (`_25 =
                // PtySize { .. }` asked to stay below 2^28 elements, an integer
                // variable over a struct value) could only ever FAIL, with a
                // counterexample that described no allocation. MEASURED: orca-daemon
                // `rpc.rs` row on seal `321aaeda7` and stage-1 `f9e47e012`.
                //
                // Trust (fa/struct-alloc r2, 2026-10-02): but the name match also
                // catches REAL third-party allocators whose count sits elsewhere —
                // ndarray's `ArrayBase::reserve(&mut self, Axis, usize)` and
                // `ArrayBase::from_elem(shape, elem)` — so "not an integer at the std
                // index" proves only that the std signature does not apply, not that
                // nothing is allocated. MEASURED on r1 (`79f5ce3389`): both minted NO
                // row at all. So this is the same "recognized, count not derivable"
                // case as `None` below: a VISIBLE `UnsupportedMir` (preclassified
                // Unknown, never PROVEd, never a false counterexample) — fail closed
                // and visible, not silent. An integer count, or an operand whose type
                // is unknown, keeps the counted row exactly as before.
                Some(size_op) if operand_is_not_an_element_count(func, size_op) => {
                    vcs.push(unsupported_mir_vc(
                        func,
                        format!("UnboundedAllocation::{d}::count-not-an-integer"),
                        format!(
                            "call matched bulk allocation `{d}` by name, but its argument \
                             at index {size_idx} is not an integer, so the std signature \
                             does not apply and the element count is not derivable; \
                             cannot prove any allocation it makes is bounded"
                        ),
                        span.clone(),
                    ));
                    continue;
                }
                Some(size_op) => {
                    direct_size_op = Some(size_op);
                    // `reserve` / `reserve_exact` / `extend_reserve`: the count is
                    // the ADDITIONAL capacity over the receiver's live length.
                    // (`resize`'s count is the new TOTAL length, not an addition.)
                    receiver_live = d == "Vec::reserve";
                    // Trust (2026-10-14, ALLOC-RECEIVER-ZST-1): that length must be one
                    // memory bounds ([`live_receiver_length_is_bounded`], argument 0).
                    // Review round 59 kept a zero-sized `reserve`'s row, but the row
                    // was the element ceiling alone (no byte term at stride zero): a
                    // guard proved it and a constant count skipped it, while a full
                    // `Vec<()>` overflows on `reserve(1)`. Asked of a SYSROOT callee
                    // (or one with no compiler key): `bulk_alloc_call` matches the
                    // method tail, and a non-sysroot `reserve` (a local or dependency
                    // body, verified where it is written) keeps its counted row.
                    if receiver_live
                        && !callee_key.as_ref().is_some_and(|key| !key.krate_is_real_sysroot)
                        && !args.first().is_some_and(|recv| {
                            live_receiver_length_is_bounded(func, callee, callee_key.as_ref(), recv)
                        })
                    {
                        vcs.push(receiver_length_not_bounded_vc(func, d, span));
                        continue;
                    }
                    (d, operand_to_formula(func, size_op))
                }
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
        } else if let Some(d) =
            super::alloc_bounds::AllocCallDispatch::single_value_with_tail(callee, call_tail)
        {
            // `Box::new`/`Rc::new`/`Arc::new`: a single heap value of type `T`. There
            // is NO count operand — the count is exactly 1 — so the count ceiling can
            // never fire; the hazard is an OVERSIZED `T` caught by the byte terms
            // below (`alloc_element_byte_size` sizes `T` from the value operand, the
            // `from_elem`-style path). A small `Box::new(x)` recovers a tiny stride and
            // emits no obligation (drop-in preserved); a value past the target's
            // `isize::MAX` fails closed (a defense: rustc refuses such a type, see the
            // single-value arm below). `Box::new([0u8; 1 << 40])`, 1 TiB, is within a
            // 64-bit target's line and is not reported (ALLOC-BYTE-1).
            single_value = true;
            (d, Formula::Int(1))
        } else if let Some(d) =
            super::alloc_bounds::AllocCallDispatch::raw_with_tail(callee, call_tail)
        {
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
        } else if is_collect_tail
            || (in_std_iter_ns
                && ((call_tail == "unzip" && is_std_unzip_sink(callee))
                    || (call_tail == "collect_into" && is_std_collect_into_sink(callee))))
        {
            let Some(iter_op) = args.first() else {
                continue;
            };
            // `collect_into(&mut dest)` extends a LIVE destination (ALLOC-RECEIVER-1):
            // its fit check and its counted row both charge what `dest` already
            // holds. Before 2026-10-08 both treated it as a fresh `collect`.
            receiver_live = !is_collect_tail && call_tail == "collect_into";
            // Trust (2026-10-14, ALLOC-RECEIVER-ZST-1): and both charge it as a length
            // memory bounds, which `dest` (argument 1) must be shown to have, exactly
            // as `extend`'s receiver is below. A `Vec<()>` destination was granted
            // from any bounded source and its counted row was the element ceiling
            // alone; one more element overflows a full one.
            if receiver_live
                && !args.get(1).is_some_and(|dest| {
                    live_receiver_length_is_bounded(func, callee, callee_key.as_ref(), dest)
                })
            {
                vcs.push(receiver_length_not_bounded_vc(func, "Iterator::collect_into", span));
                continue;
            }
            // SOUND skip: collecting from an already-materialized std collection
            // (`.keys()/.values()/.iter()/.into_iter()/.drain()`, reached through
            // length-non-increasing adaptors) yields at most `source.len()`
            // elements. The source collection's own allocation was itself gated by
            // this pass when it was built, so this collect introduces NO new
            // unbounded hazard — the OOM obligation, if any, lives at the source
            // allocation, not here. Generative sources (ranges, `repeat`, custom
            // iterators — the real OOM shapes like `(0..1<<28).collect()`) are NOT
            // matched and remain gated by `iter_collect_count` below.
            //
            // Trust (W4 HASHMAP r3, 2026-09-29): "no NEW hazard" holds only when
            // the destination spends no more per item than the source can hold of
            // them — a bounded COUNT is not a bounded ALLOCATION of a larger element
            // ([`bounded_source_fits_sink`]). MEASURED on the redo's r2
            // (`b9288112d`): a 2^28-byte `&[u8]` zipped with
            // `repeat_with(MaybeUninit::<[u8; 1 << 35]>::uninit)` and collected into
            // a `HashMap<u8, _>` built rc=0 and panicked "Hash table capacity
            // overflow". A sink with no element-size token is not a std collection
            // this lane can size (a user `FromIterator`), and keeps the skip.
            //
            // Trust (2026-10-06, D12 option (a)): and only when the destination's
            // largest possible upfront reservation fits on the per-allocation axiom
            // too ([`bounded_source_max_items`]) — a bounded source says nothing about
            // how large each destination item is. Merged 2026-10-14 with the W4
            // HASHMAP r3 check above as a CONJUNCTION: the skip needs both. Where
            // that walk does not recognize the source (a keyed or `flat_map` leaf
            // only [`collect_source_live_count`] grants) it does not veto, and the
            // W4 fit check alone decides; the 64-bit width gate always applies.
            let bounded = collect_source_live_count(func, iter_op, 0);
            if let Some(count) = bounded
                && bounded_source_grant_applies_at_width(pointer_bits)
                && bounded_source_fits_sink(callee, count, receiver_live, live_axiom)
                    .unwrap_or(true)
                && bounded_source_max_items(func, iter_op, 0).is_none_or(|items| {
                    collect_sink_max_bytes_per_item(callee).is_some_and(|(per_item, fixed)| {
                        trust_types::alloc_model::bounded_source_reservation_fits(
                            collect_sink_min_reserved_items(callee, items),
                            per_item,
                            fixed,
                            receiver_live,
                        )
                    })
                })
            {
                continue;
            }
            match iter_collect_count(func, iter_op) {
                Some(c) => ("Iterator::collect", c),
                // A bounded source whose destination may not hold it, and no count
                // derivable either: a VISIBLE Unknown that says which.
                None if bounded.is_some() => {
                    vcs.push(bounded_source_overflow_vc(func, "Iterator::collect", span));
                    continue;
                }
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
        } else if in_std_iter_ns
            && call_tail == "extend"
            && is_capacity_reserving_std_extend(callee)
        {
            // Trust (2026-09-25, F2): `extend` into a collection that reserves
            // from `size_hint` is the SAME allocation as the `collect` sibling
            // above and is charged the same way: skipped only when the source is
            // a bounded, non-zero-sized std collection (an iterator over one, or
            // the collection value itself), counted when the count is derivable,
            // and a visible Unknown otherwise. The source is argument 1 (argument
            // 0 is `&mut self`). Before this arm `extend` charged nothing at all,
            // and `v.extend(iter::repeat(x).take(usize::MAX))` built exit 0 and
            // panicked "capacity overflow".
            let Some(iter_op) = args.get(1) else {
                continue;
            };
            // Both the grant below and the counted obligation bound what is ADDED
            // (the counted one in BYTES), so both need the RECEIVER's length bounded
            // by memory too. A `Vec<()>` can already hold `usize::MAX` elements, and
            // `extend(Some(()))` then panics "capacity overflow": it was proved
            // panic-free in both lanes (the zero-size rule's precondition audit,
            // 2026-09-29, `p10`), by the grant, and would have been by the count too
            // (one element of zero bytes). A receiver this cannot show bounded keeps
            // a visible Unknown — the question every live-receiver sink asks
            // ([`live_receiver_length_is_bounded`], ALLOC-RECEIVER-ZST-1).
            if !args.first().is_some_and(|recv| {
                live_receiver_length_is_bounded(func, callee, callee_key.as_ref(), recv)
            }) {
                vcs.push(receiver_length_not_bounded_vc(func, "Extend::extend", span));
                continue;
            }
            // The receiver (argument 0) is live: a counted row charges what it
            // already holds (ALLOC-RECEIVER-1).
            receiver_live = true;
            //
            // Trust (W4 HASHMAP r3, 2026-09-29): skipped only when the RECEIVER can
            // reserve that many more items than it may already hold
            // ([`bounded_source_fits_sink`] with a live receiver). Every receiver
            // this arm matches is a std collection, so one without an element-size
            // token (a generic element) is NOT skipped.
            let mut value_bounded: Option<Option<LiveSourceCount>> = None;
            let bounded = collect_source_live_count(func, iter_op, 0).or_else(|| {
                *value_bounded
                    .insert(operand_bounded_std_collection_value_count(func, iter_op))
            });
            // Trust (2026-10-06, D12 option (a)): the added items' reservation, on
            // top of the receiver's own live bytes, must fit (see the collect arm,
            // and its merge note: both checks must admit the skip).
            if let Some(count) = bounded
                && bounded_source_grant_applies_at_width(pointer_bits)
                && bounded_source_fits_sink(callee, count, true, live_axiom).unwrap_or(false)
            {
                let source_items = bounded_source_max_items(func, iter_op, 0).or_else(|| {
                    value_bounded
                        .unwrap_or_else(|| {
                            operand_bounded_std_collection_value_count(func, iter_op)
                        })
                        .and_then(|_| operand_place_ty(func, iter_op))
                        .and_then(|ty| live_collection_max_items(ty, None))
                });
                let reservation_fits = source_items.is_none_or(|items| {
                    args.first()
                        .and_then(|recv| extend_receiver_max_bytes_per_item(func, callee, recv))
                        .is_some_and(|per_item| {
                            trust_types::alloc_model::bounded_source_reservation_fits(
                                items, per_item, 0, true,
                            )
                        })
                });
                if reservation_fits {
                    continue;
                }
            }
            match iter_collect_count(func, iter_op) {
                Some(c) => ("Extend::extend", c),
                None if bounded.is_some() => {
                    vcs.push(bounded_source_overflow_vc(func, "Extend::extend", span));
                    continue;
                }
                None => {
                    vcs.push(unsupported_mir_vc(
                        func,
                        "UnboundedAllocation::Extend::extend::count-not-derivable".to_string(),
                        "`extend` reserves from its source's `size_hint` (capacity \
                         overflow panics on a huge one), and the source is neither a \
                         bounded, non-zero-sized std collection nor a derivable count; \
                         cannot prove the allocation is bounded"
                            .to_string(),
                        span.clone(),
                    ));
                    continue;
                }
            }
        } else {
            continue;
        };
        // RawVec allocates no backing storage for a zero-sized element, even at
        // usize::MAX capacity. Require both the DefId-derived Vec operation and
        // the extractor's exact layout token: a spelling fallback or the first
        // type parameter of another container/iterator cannot establish this.
        // This removes only the backing-allocation row. Callee, panic, Clone,
        // Drop, and logical len+additional overflow obligations remain intact.
        if parse_elem_bytes_token(callee) == Some(0)
            && callee_key.as_ref().is_some_and(|key| {
                key.krate_is_real_sysroot
                    // Trust (2026-10-07, review round 59): NOT `reserve`/`reserve_exact`.
                    // Their count is ADDITIONAL to a length that memory does not bound
                    // for a zero-sized element, and `len + additional` overflowing
                    // `usize` panics "capacity overflow": `Vec<()>` of length
                    // `usize::MAX - 2` then `reserve(5)` was reported with only a
                    // std-attributed advisory.
                    && key.is_one_of(&[
                        trust_types::SysrootItem::VecWithCapacity,
                        trust_types::SysrootItem::VecWithCapacityIn,
                        trust_types::SysrootItem::VecResize,
                        trust_types::SysrootItem::VecResizeWith,
                        trust_types::SysrootItem::VecFromElem,
                    ])
            })
        {
            continue;
        }
        // Trust (W4 HASHMAP r2, 2026-09-27): a std HASH-TABLE sink. The extractor
        // stamps it (by DefId: the callee's impl self type, a `collect`/
        // `collect_into`/`from_iter` destination, an `extend`/`extend_reserve`
        // receiver, an `unzip` half) with the hash-table token, whose stride is the
        // table ELEMENT (`(K, V)` for a `HashMap`, never `K` alone) and whose
        // capacity term is hashbrown's bucket layout
        // ([`hash_table_capacity_overflow_term`]). An unknown element, or a
        // `HashMap`/`HashSet` allocation method that arrives WITHOUT the token, fails
        // closed with a visible Unknown: neither a count-only charge nor
        // `count * stride` is sound for a table. MEASURED on the redo's r1
        // (`9eadf44e0`): `HashMap::<u8, [u8; 1 << 50]>::with_capacity(n)` under
        // `n < 2^20` was stamped `@1` from `K` alone, built rc=0 and panicked at
        // `n = 8192`.
        let table_stride = match trust_types::parse_trailing_table_elem_bytes_token(callee) {
            Some(trust_types::TableElemBytes::Known(stride)) => Some(stride),
            Some(trust_types::TableElemBytes::Unknown) => {
                let display = hash_table_sink_display(display);
                vcs.push(unsupported_mir_vc(
                    func,
                    format!(
                        "UnboundedAllocation::{display}::hash-table-element-size-not-derivable"
                    ),
                    format!(
                        "bulk allocation `{display}` into a std hash table whose element size \
                         is not derivable (a generic or layout-less element): hashbrown's \
                         bucket layout cannot be bounded; cannot prove the allocation is \
                         bounded"
                    ),
                    span.clone(),
                ));
                continue;
            }
            None if bulk_dispatch.is_some()
                && callee_is_std_hash_table_inherent(callee) =>
            {
                let display = hash_table_sink_display(display);
                vcs.push(unsupported_mir_vc(
                    func,
                    format!("UnboundedAllocation::{display}::hash-table-token-absent"),
                    format!(
                        "bulk allocation `{display}` on a std hash table carries no \
                         authoritative element-size token; hashbrown's bucket layout cannot \
                         be bounded; cannot prove the allocation is bounded"
                    ),
                    span.clone(),
                ));
                continue;
            }
            None => None,
        };
        // Trust (ALLOC-WIDTH-1, 2026-10-08): a pointer width this lane does not
        // model (16-bit) judges nothing: the row is a visible Unknown, never a
        // count-ceiling proof the target's object limit is far below.
        let target = match target {
            Ok(target) => target,
            Err(bits) => {
                let display =
                    if table_stride.is_some() { hash_table_sink_display(display) } else { display };
                vcs.push(unsupported_mir_vc(
                    func,
                    format!("UnboundedAllocation::{display}::pointer-width-not-modeled"),
                    format!(
                        "bulk allocation `{display}` on a {bits}-bit target: the allocation \
                         lane models 32- and 64-bit pointer widths, and the element ceiling \
                         (2^28) is above this target's largest object; cannot prove the \
                         allocation is bounded"
                    ),
                    span.clone(),
                ));
                continue;
            }
        };
        // Capacity-overflow element stride: `size_of::<T>()` for the allocation,
        // recovered from the exact layout token, element operand, callee
        // turbofish, or the existing one-byte String model. Used to catch the
        // MULTI-BYTE capacity overflow `count * stride >= isize::MAX` that the count-only
        // ceiling misses (SOUNDNESS, hunt-11: `Vec::<[u8; 1<<40]>::with_capacity(n)`
        // with `n < 2^27` panicked "capacity overflow" yet was kernel-certified).
        //
        // A hash-table sink's stride is its token's element size. The stride is kept
        // AS RECOVERED (zero and one included); [`capacity_overflow_term`] decides
        // which strides carry a term.
        let raw_stride = match table_stride {
            Some(stride) => Some(stride),
            None => counted_alloc_exact_stride(func, display, callee, args)
                .and_then(|stride| i128::try_from(stride).ok()),
        };
        let hash_table = table_stride.is_some();
        // Trust: a bound on the element COUNT says nothing about the BYTE
        // request when the element layout is unknown. In particular, a generic
        // `Vec<T>::with_capacity(n)` can overflow below the count ceiling for a
        // large T. Keep a visible Unknown before either the constant-count skip
        // or the solver can credit a count-only row. Zero requests and existing
        // single-value allocations keep their separate, layout-independent rules.
        if !single_value
            && raw_stride.is_none()
            && !matches!(&count_f, Formula::Int(0) | Formula::UInt(0))
        {
            vcs.push(unsupported_mir_vc(
                func,
                format!("UnboundedAllocation::{display}::element-size-not-derivable"),
                format!(
                    "bulk allocation `{display}` has no derivable element size: \
                     an element-count bound cannot establish its byte capacity; \
                     cannot prove the allocation is bounded"
                ),
                span.clone(),
            ));
            continue;
        }
        // The capacity disjunct `scale * count >= threshold`, at the target's object
        // limit and, for an additional count, net of what the live receiver holds
        // (ALLOC-WIDTH-1 / ALLOC-RECEIVER-1). `None`: no byte line beyond the
        // element ceiling (an unknown or zero-sized element, or a one-byte element
        // whose line the ceiling already excludes).
        //
        // Trust (2026-10-14, ALLOC-RECEIVER-ZST-1): a LIVE receiver whose stride this
        // lane cannot recover (`String::reserve`, `OsString::reserve`: no generic
        // argument, so no token) carried no term at all, so on a target without the
        // live-address-space axiom — where a receiver may already be full — its row
        // was the element ceiling alone, and `if n < 100 { s.reserve(n) }` was proved
        // on a 32-bit target although a `String` of `isize::MAX` bytes overflows on
        // `reserve(1)`. A sysroot live receiver that reaches this point has a length
        // memory bounds ([`live_receiver_length_is_bounded`]), so its element is at
        // least one byte, and at EVERY stride of one byte or more the term's threshold
        // is negative there (`object_limit - stride * (object_limit / stride + 1)`):
        // the row fails at every count. One byte is that verdict. (A non-sysroot
        // `reserve`, which skips that question, only fails where it used to pass.) A
        // hash table always has its token's stride here, so this term is contiguous.
        // On a 64-bit target the axiom bounds the receiver and nothing changes. (The
        // compiler refuses a verifying build for a narrower target under every
        // fail-closed policy, `trust_verify/narrow_target.rs`, so this was a false
        // verdict of the lane, which ALLOC-WIDTH-1 judges at the target's width, and
        // not of such a build.)
        let capacity = raw_stride
            .and_then(|stride| capacity_overflow_term(target, stride, hash_table, receiver_live))
            .or_else(|| {
                (receiver_live && !target.live_axiom && raw_stride.is_none())
                    .then(|| capacity_overflow_term(target, 1, false, true))
                    .flatten()
            });
        // W4 ALLOC-LEN (2026-09-25): a DefId-keyed fresh exact-capacity
        // constructor whose count is the length of a live sequence (or a sum
        // of two) AND whose allocation is at most the bytes those sequences
        // occupy (`availability_bounded`: every source stride known, non-zero
        // and at least the target's). Only then does the availability ceiling
        // not apply — the collect sibling's argument, made exact — and when its
        // capacity-overflow theorem also holds there is nothing left to prove;
        // otherwise ONLY the capacity-overflow disjunct is kept, below. Any
        // other len-derived count is an ordinary row: adversarial round 1
        // measured a ZST source (a02) and wider targets (a01, a11) verifying and
        // then aborting on 2^50-byte requests when the ceiling was dropped for
        // every len-derived count. See `alloc_len`'s module banner and
        // docs/TCB.md ("Live-length capacity").
        //
        // Never for a hash-table sink (landing merge with W4 HASHMAP,
        // 2026-09-29): `len_derived_allocation` keys only `Vec`/`String`
        // constructors, so a table never reaches it today, and its theorems are
        // about `stride * count` while a table allocates hashbrown's bucket
        // layout ([`hash_table_capacity_overflow_term`]). The filter only ever
        // routes a call back to the ordinary row.
        let len_derived = direct_size_op
            .filter(|_| !hash_table)
            .and_then(|op| len_derived_allocation(func, callee, callee_key.as_ref(), op))
            .filter(|ld| ld.availability_bounded);
        if len_derived.as_ref().is_some_and(|ld| ld.capacity_safe) {
            continue;
        }
        // Trust (2026-10-07): a counted allocation whose count IS the length of an
        // existing slice or str (`String::with_capacity(s.len())`, `vec![0; v.len()]`,
        // `out.reserve(v.len())`) is bounded the way a collect over that collection
        // is (`docs/DECISION_QUEUE.md` D12 option (a)): skipped only when that many
        // items times the exact stride fits, against the live-receiver budget for a
        // `reserve`. ordsweep2 strings/c04 hit the 2^28-element availability ceiling
        // on a count no larger than its own input. Merged 2026-10-14: never for a
        // hash-table sink, and only where ALLOC-WIDTH-1's live axiom also holds.
        //
        // Trust (2026-10-15, DECISION_QUEUE D102): and only where main's ALLOC-LEN
        // availability theorem ALSO drops the element ceiling for this count
        // (`len_derived`, already filtered on `availability_bounded`: a fresh
        // exact-capacity constructor whose every source stride is known, non-zero and
        // at least the target's). This skip answers the capacity panic only; the
        // ceiling is main's availability POLICY (docs/TCB.md "Live-length capacity",
        // half 1; ALLOC-ELEM-CEILING-1), which keeps it for a `reserve`'s additional
        // count, a `resize`, a target wider than its source and a generic source. As
        // merged, this skip waved all four through: measured on the stage 1 of the
        // merge, `tests/ui/trust/alloc_capacity_from_live_length.rs` `reserve`,
        // `resize`, `narrow_struct_source`, `pointer_wider_target` and
        // `pointer_generic_source` built with no allocation row. Fail-closed: the two
        // lines' rules are conjoined until D102 decides between them.
        if !single_value
            && !hash_table
            && len_derived.is_some()
            && target.live_axiom
            && bounded_source_grant_applies_at_width(pointer_bits)
            && counted_alloc_is_sequence_sink(callee)
            && let Some(size_op) = direct_size_op
            && let Some(items) = existing_length_max_items(func, size_op, 0)
            && let Some(stride) = counted_alloc_exact_stride(func, display, callee, args)
            // A `reserve` adds to the receiver's length, which only a non-zero-sized
            // element bounds (review round 59).
            && (!receiver_live || stride > 0)
            && trust_types::alloc_model::bounded_source_reservation_fits(
                items,
                stride,
                0,
                receiver_live,
            )
        {
            continue;
        }
        // A literal constant size STRICTLY BELOW the ceiling is trivially bounded —
        // BUT a multi-byte element can capacity-overflow even at a small count, so
        // only skip when the BYTE product is also safe. The boundary itself is NOT
        // safe: the nn-dsl OOM allocated exactly `1 << 28` elements (== the ceiling),
        // so `<=` would wave the real bug through. Use `<` so exactly-at-ceiling
        // falls through to the VC.
        // A single-value alloc is skipped when its byte size is unrecoverable or
        // within the target's object limit; otherwise it falls through so the
        // capacity term decides. For the count-based sinks (`single_value ==
        // false`) a constant count is skipped when it is below the ceiling and the
        // capacity term (if any) does not fire at it.
        //
        // Trust (W4 HASHMAP r2): a hash table's constant count is safe only when the
        // BUCKET bound does not fire ([`hash_table_capacity_overflow_term`]) —
        // `4097 * 2^50 < isize::MAX`, but 8192 buckets of `2^50` bytes are not.
        //
        // Trust (ALLOC-WIDTH-1 / ALLOC-RECEIVER-1, 2026-10-08): the skip asks the
        // SAME term the row would carry, so a constant `reserve(10)` is judged with
        // the receiver's live length and at the target's object limit — before,
        // it was judged at the 64-bit line with no receiver.
        let const_byte_safe = |n: i128| -> bool {
            capacity.is_none_or(|(scale, threshold)| {
                scale.checked_mul(n).is_some_and(|b| b < threshold)
            })
        };
        if single_value {
            // count is exactly 1: the count ceiling never applies. Bounded iff the
            // value's recoverable byte size is within the largest object the target
            // can hold (`isize::MAX` at its pointer width — a value of exactly
            // `isize::MAX` bytes has a valid `Layout`, so the line is `<=`);
            // unrecoverable byte size (`raw_stride == None`, an opaque `T`) is
            // bounded — nothing to flag. There is no availability budget below
            // that line (the 256 MiB one was deleted, ALLOC-BYTE-1).
            //
            // A DEFENSE, not a live check: rustc refuses any type of
            // `obj_size_bound` bytes or more (2^61 on a 64-bit target, 2^31 and
            // 2^15 on 32 and 16 bits, `rustc_abi::TargetDataLayout::obj_size_bound`),
            // which is at most `isize::MAX + 1` everywhere, so no value of a type
            // the compiler accepted for THIS target reaches it. It can fire only
            // where the stride is a fallback estimate (the spelled 64-bit layout
            // on a narrower target) or no target width was supplied.
            let bounded = raw_stride.is_none_or(|s| s <= target.object_limit);
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
        // Trust (2026-09-23, D3/W1a): the count as it enters the FORMULA atoms,
        // with a literal-zero range start folded (`end - 0` -> `end`). The
        // display string (`count_disp`, carried in the `VcKind` payload) and the
        // const-skip above keep the unfolded `count_f`. See
        // `fold_sub_literal_zero` for why this is exact and why it is literal-0
        // only.
        let atom_count = fold_sub_literal_zero(&count_f);
        // Failure condition: the requested element count REACHES OR EXCEEDS the
        // ceiling (`>=`, not `>`). An allocation of exactly the ceiling is the nn
        // OOM and must fail closed, not slip through the off-by-one at the boundary.
        //
        // No 256 MiB byte budget is added for a multi-byte element: it was deleted
        // (ALLOC-BYTE-1, see `generate/mod.rs`) together with the two fixes that
        // made it unnecessary — the target's own object limit and the live
        // receiver, both in the capacity term below. The element ceiling itself
        // is still a value threshold (`ALLOC-ELEM-CEILING-1`, OPEN).
        let elem_ceiling = Formula::Ge(
            Box::new(atom_count.clone()),
            Box::new(Formula::Int(UNBOUNDED_ALLOC_ELEM_CEILING)),
        );
        // Disjuncts of the FAILURE condition. The count ceiling (availability) is
        // always present; the CAPACITY-OVERFLOW byte term ([`capacity_overflow_term`]:
        // `stride * count >= isize::MAX` at the target's pointer width, hashbrown's
        // bucket layout for a table, net of a live receiver's length for an
        // additional count — a real runtime panic, ALL displays incl. const counts)
        // is added when the stride is recoverable. Purely ADDITIVE — only ever turns
        // PROVED -> FAILED, never the reverse, so a genuinely-bounded allocation is
        // unaffected; a one-byte element gets a byte term only where the ceiling does
        // not already exclude its line.
        let body = if let Some(ld) = &len_derived {
            // Len-derived and availability-bounded, capacity theorem NOT
            // established (a sum of two lengths each at least as wide as the
            // target, e.g. t23's same-stride `a.len() + b.len()`): the
            // availability disjuncts are dropped and the real panic — RawVec's
            // `count * size_of::<T>() > isize::MAX` capacity overflow — is the
            // whole failure condition, at the exact target stride (which is 1
            // for a byte buffer, where `capacity` records nothing). `isize_max` is
            // read from the count operand's own `usize` width — for these
            // DefId-keyed std constructors, the target's pointer width.
            // Spelled `T * count >= isize::MAX + 1` — the exact panic boundary,
            // in the same `Ge(Mul(stride, count), bound)` shape as the
            // capacity term below, which the kernel's scaled-chain recognizer
            // reads.
            Formula::Ge(
                Box::new(Formula::Mul(
                    Box::new(Formula::Int(ld.target_stride)),
                    Box::new(atom_count),
                )),
                Box::new(Formula::Int(ld.isize_max + 1)),
            )
        } else if let Some((scale, threshold)) = capacity {
            // Trust (W4 HASHMAP r2): a hash table's capacity term is hashbrown's
            // bucket layout, not `stride * count` (see
            // [`hash_table_capacity_overflow_term`]); same `Mul(Int, count) >= Int`
            // shape, as is a live receiver's (a lower threshold, same scale).
            Formula::Or(vec![elem_ceiling, capacity_atom(scale, threshold, &atom_count)])
        } else {
            elem_ceiling
        };
        let mut formula = v2_formula_with_block_defs(func, block, body);
        // Bound parameters, non-parameter integer/char locals/temps, and datatype
        // fields in a single fused pass (SOUNDNESS: DROP-ONLY — true carrier facts).
        formula = conjoin_arg_local_field_type_ranges(func, formula);
        // Trust S2c (exemption): the whole-VC version rename runs FIRST, on the body
        // + same-block block-defs only. The THREADED facts (dominating path guards +
        // assert-passed semantic guards) are conjoined AFTER, EXEMPT from the rename —
        // so a guard's bare ENTRY-param read (`n` in `if n <= BOUND`) stays bare and
        // is name-disjoint from a reassigned body read (`n#s2_0`), instead of being
        // renamed onto it and false-PROVING a real OOM. A LIVE entry read (bare on
        // both sides) still connects; an establish-versioned semantic-guard subject
        // (`c#s0_0`) connects to the body's statement-granular reference.
        let killed = &empty;
        formula =
            conjoin_preconditions_versioned(func, block.id, &func.preconditions, killed, formula);
        // Dominating control-flow guards (`if n <= BOUND`) — exempt.
        let guard_paths_map = guard_paths_map.get_or_init(|| super::guard_map_for(func));
        if let Some(block_guard_paths) = guard_paths_map.get(&block.id) {
            let sv = sv.get_or_init(|| super::stmt_versions_for(func));
            formula = v2_formula_with_path_guards(func, sv, block.id, block_guard_paths, formula);
        }
        // Assert-passed semantic guards — exempt.
        let semantic_guards =
            semantic_guards.get_or_init(|| super::semantic_guard_map_for(func, None));
        if let Some(sem_guards) = semantic_guards.get(&block.id)
            && !sem_guards.is_empty()
        {
            let mut conjuncts = Vec::with_capacity(sem_guards.len() + 1);
            conjuncts.extend(sem_guards.iter().cloned());
            conjuncts.push(formula);
            formula = Formula::And(conjuncts);
        }
        // Compiler-authenticated primitive formatting bounds belong to the
        // single-valued numeric len result, not the String's heap. Like the
        // arithmetic lane, attach them at derived uses AFTER versioning the
        // body, then let the existing SSA normalization connect live names.
        let primitive_decimal_guards = primitive_decimal_guards
            .get_or_init(|| super::primitive_decimal_len_guards_for(func));
        if let Some(facts) = primitive_decimal_guards.get(&block.id)
            && !facts.is_empty()
        {
            let mut conjuncts = Vec::with_capacity(facts.len() + 1);
            conjuncts.extend(facts.iter().cloned());
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
            // Less the element-read congruences the row cannot use (`RowGlobalFacts::for_row`).
            let facts = global_facts
                .get_or_init(|| build_global_invariant_facts(func))
                .for_row(&formula);
            if !facts.is_empty() {
                let mut conjuncts = facts;
                conjuncts.push(formula);
                formula = Formula::And(conjuncts);
            }
        }
        // Collapse SSA locals' version tokens so the facts' bare names bind the
        // body reads (identity for single-write locals; parameter-aware gate).
        formula = normalize_ssa_version_tokens_owned(func, formula);
        let row_display = if hash_table { hash_table_sink_display(display) } else { display };
        let detail = if len_derived.is_some() {
            // The W4 ALLOC-LEN capacity-only row: the count is the length of
            // live memory, so the only failure left is RawVec's capacity panic.
            "capacity overflow: the requested capacity (a sum of live-sequence \
             lengths) times the element size may exceed `isize::MAX` in the type \
             model; allocate from ONE sequence whose element is at least as wide, \
             or bound the lengths with a dominating check"
                .to_string()
        } else if receiver_live && !target.live_axiom && capacity.is_some() {
            // ALLOC-RECEIVER-1 without the live-address-space bound: the receiver
            // may already hold `isize::MAX` bytes, so no count is shown to fit.
            let width = target.pointer_bits.map_or_else(
                || "a target whose pointer width was not supplied (judged at 32 bits)".to_string(),
                |bits| format!("a {bits}-bit target"),
            );
            format!(
                "capacity overflow: this call adds its count to what the receiver already \
                 holds, and on {width} nothing bounds that length below `isize::MAX` \
                 bytes; reserve on a receiver whose length is known, or verify for a \
                 64-bit target"
            )
        } else {
            format!(
                "bulk allocation may reach or exceed {UNBOUNDED_ALLOC_ELEM_CEILING} elements: \
                 bound the size (e.g. `#[requires(n < BOUND)]` or a dominating check) \
                 or route it through a budget-checked allocator that fails closed"
            )
        };
        let function = *fn_sym.get_or_insert_with(|| func.name.as_str().into());
        vcs.push(VerificationCondition {
            kind: VcKind::UnboundedAllocation {
                callee: row_display.to_string(),
                count: count_disp,
                detail,
            },
            function,
            location: span.clone(),
            formula,
            contract_metadata: None,
            obligation: None,
        });
    }
    vcs
}

/// Test support (ALLOC-WIDTH-1, 2026-10-08): this lane's rows as the COMPILER
/// generates them on a 64-bit host, with the session's target pointer width
/// installed (`VcgenContext::with_target_pointer_bits`). A unit test that models a
/// 64-bit target's verdicts — the live-source skip, the 64-bit object limit —
/// says so through this; the bare entry judges as a caller with no target does
/// (the narrowest modeled width, no live bound).
#[cfg(test)]
pub(crate) fn generate_unbounded_allocation_vcs_on_64_bit(
    func: &VerifiableFunction,
) -> Vec<VerificationCondition> {
    crate::with_target_pointer_bits(Some(64), || generate_unbounded_allocation_vcs(func))
}

/// Trust (2026-09-23, D3/W1a): rewrite a TOP-LEVEL `Sub(t, 0)` to `t`; every
/// other formula is returned unchanged.
///
/// WHY. `iter_collect_count` spells the length of `start..end` as
/// `Sub(end, start)`, so `(0..n.min(8) as u32).collect()` (sweep s20) counts
/// `Sub(end, Int(0))`. The Clean kernel's scaled-chain recognizer wants a BARE
/// variable under the byte atom's `Mul(stride, _)` (`int_var_name` in
/// trust-certify's `chain_node`), so `8 * (end - 0) >= 2^28` was uncertifiable
/// while `8 * end >= 2^28` certifies. The row therefore carried only the
/// `SolverRevalidated` authority (and fell back to the authority-free interval
/// `Proved`, i.e. `UNKNOWN (interval)`, whenever `ay` was starved).
///
/// EXACT, not trusted. `t - 0 = t` holds in the integers, and the rewrite is
/// done HERE, in the obligation the kernel then checks — not inside the kernel
/// bridge — so the certificate is for the formula the VC actually stores. No
/// trusted rewrite is hidden inside the `Certified` class.
///
/// LITERAL ZERO ONLY. Folding any other start would be a false proof:
/// `(-268435456i64..n.min(8) as i64)` counts `Sub(end, Int(-268435456))`, which
/// can reach the ceiling, and dropping the literal makes it `end <= 8`
/// (railed by `tests/ui/trust/interval_decided_allocation_authority.rs`,
/// revision `nonzero_literal_start`, and the unit tests in
/// `alloc_count_fold_tests`). Non-recursive on purpose: only the count's own
/// outermost node is touched, never a subterm of `end`.
fn fold_sub_literal_zero(f: &Formula) -> Formula {
    match f {
        Formula::Sub(lhs, rhs) if matches!(**rhs, Formula::Int(0) | Formula::UInt(0)) => {
            (**lhs).clone()
        }
        other => other.clone(),
    }
}

#[cfg(test)]
#[path = "alloc_count_fold_tests.rs"]
mod alloc_count_fold_tests;

#[cfg(test)]
#[path = "local_formula_name_tests.rs"]
mod local_formula_name_tests;

#[cfg(test)]
#[path = "iter_hof_collect_count_tests.rs"]
mod iter_hof_collect_count_tests;

/// Trust (fa/struct-alloc, 2026-10-02): `op`'s type is KNOWN and is not one an
/// element count can have. Only integer carriers (`Int`, `PtrSizedInt`, `Bv`, the
/// mathematical `BignumNat`) and the types this lane cannot classify (`Unsupported`,
/// or no recoverable type at all) may carry a count; every other shape — a struct,
/// tuple, reference, pointer, float, bool, char, array, closure, fn item — is
/// listed explicitly so a new `Ty` variant falls on the charged side.
fn operand_is_not_an_element_count(func: &VerifiableFunction, op: &Operand) -> bool {
    // `operand_ty_cow`: an inspect-only caller must not clone a fat `Ty::Adt`
    // (lib.rs — the clone is the dominant `TrustVcGenWorkBudgetExceeded` driver).
    crate::operand_ty_cow(func, op).is_some_and(|ty| {
        matches!(
            ty.as_ref(),
            Ty::Bool
                | Ty::Char
                | Ty::Float { .. }
                | Ty::Ref { .. }
                | Ty::RawPtr { .. }
                | Ty::Slice { .. }
                | Ty::Seq { .. }
                | Ty::Str
                | Ty::Array { .. }
                | Ty::SymArray { .. }
                | Ty::Tuple(_)
                | Ty::Adt { .. }
                | Ty::Datatype { .. }
                | Ty::Unit
                | Ty::Never
                | Ty::Closure { .. }
                | Ty::FnDef { .. }
                | Ty::FnPtr { .. }
                | Ty::Dynamic { .. }
                | Ty::Coroutine { .. }
        )
    })
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
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn is_collect_sink(callee: &str) -> bool {
    matches!(callee_tail(callee), "collect" | "from_iter")
}

/// Trust (W4 HASHMAP r3, 2026-09-29): the name a hash-table allocation's row shows.
/// [`bulk_alloc_call`] names every `with_capacity`/`reserve` after `Vec`'s (its
/// display keys the `Vec` spelling fallback of [`alloc_element_byte_size`], so it
/// is not changed there); a row about a `HashMap`/`HashSet` said
/// `Vec::with_capacity` (probe round r2, cosmetic). Display only — no verdict,
/// recognizer or fallback reads it.
fn hash_table_sink_display(display: &str) -> &str {
    match display {
        "Vec::with_capacity" => "HashMap/HashSet::with_capacity",
        "Vec::reserve" => "HashMap/HashSet::reserve",
        other => other,
    }
}

/// Trust (W4 HASHMAP r3, 2026-09-29): does this lane charge a call to `callee` AT
/// THE CALL SITE — a bulk allocation with a count operand ([`bulk_alloc_call`]:
/// `with_capacity*`, `reserve*`, `extend_reserve`, `resize*`, `from_elem`, and since
/// the W4 ITER-HOF landing round the `Box`/`Rc`/`Arc` `new_uninit_slice*` /
/// `new_zeroed_slice*` constructors) or an
/// iterator sink that reserves from its source ([`is_collect_sink`],
/// [`is_capacity_reserving_std_extend`], [`is_std_unzip_sink`],
/// [`is_std_collect_into_sink`])?
///
/// NAME-ONLY, conservative and REFUSE-ONLY: its one consumer is
/// `callee_has_call_site_panic_family`, which the compiler asks of a sysroot fn
/// ITEM handed to a callee as a type argument (`Some(n).map(HashSet::with_capacity)`).
/// The item then runs inside the callee, where no `[unbounded_allocation]` row is
/// minted, so a `true` withholds the item's vanilla admission — it never grants
/// anything. That is also why the trait sinks are matched by their METHOD TAIL as
/// well as by their authenticated trait path: a fn item renders its qualified self
/// and trait however rustc prints the item, and a miss here is a false accept.
pub(super) fn callee_is_call_site_allocation_sink(callee: &str) -> bool {
    let tail = callee_tail(callee);
    super::alloc_bounds::AllocCallDispatch::bulk_with_tail(tail).is_some()
        || matches!(tail, "collect" | "from_iter" | "extend" | "unzip" | "collect_into")
}

/// Trust (W4 HASHMAP redo, 2026-09-25): `callee` is std's `Iterator::unzip`.
/// Its body is `let mut unzipped: (FromA, FromB) = Default::default();
/// unzipped.extend(self); unzipped` — core's tuple `Extend`, which reserves the
/// source's `size_hint().0` in BOTH halves (see
/// [`is_capacity_reserving_std_extend`]). So it is the same allocation as a
/// `collect` of the receiver and is charged the same way (receiver = argument
/// 0): skipped for a bounded, non-zero-sized source, counted when derivable, a
/// visible Unknown otherwise. Charged whatever the destination halves are (a
/// `BTreeSet` half reserves nothing — an over-charge, never a proof). MEASURED
/// on stage-1 `7c7e46061` (main): `repeat((1u32, 1u8)).take(n).unzip::<_, _,
/// Vec<u32>, Vec<u8>>()` built rc=0 and exited 101 at `n = usize::MAX`.
/// Authenticated on the trait path (`vc_callee_is_std_iter_trait_method`), not
/// the tail, so a user `unzip` is not matched.
pub(super) fn is_std_unzip_sink(callee: &str) -> bool {
    vc_callee_is_std_iter_trait_method(callee, "Iterator", "unzip")
}

/// Trust (W4 HASHMAP r2, 2026-09-27): `callee` is std's nightly
/// `Iterator::collect_into(self, &mut E) -> &mut E`, whose body is
/// `collection.extend(self); collection` — the same `size_hint().0` reservation as
/// `extend` and `collect`, so it is charged like `collect` of its RECEIVER
/// (argument 0): skipped for a bounded, non-zero-sized std source, counted when the
/// count is derivable, a visible Unknown otherwise. MEASURED on the redo's r1
/// (`9eadf44e0`): `repeat(1u64).take(n).collect_into(&mut set)` (a `HashSet`, a
/// `HashMap`, and `(0..n)` into a `HashSet<u64>`) built rc=0 and panicked "Hash
/// table capacity overflow" at `n = usize::MAX`; the `Vec` form built rc=0 on main
/// too (pre-existing). Authenticated on the trait path, so a user `collect_into`
/// is not matched.
pub(super) fn is_std_collect_into_sink(callee: &str) -> bool {
    vc_callee_is_std_iter_trait_method(callee, "Iterator", "collect_into")
}

/// Trust (W4 HASHMAP r2, 2026-09-27): the hashbrown BUCKET-LAYOUT bound behind a
/// std `HashMap`/`HashSet` allocation sink (the extractor's hash-table token,
/// [`trust_types::TRUST_TABLE_ELEM_BYTES_TOKEN_PREFIX`]).
///
/// A `Vec` of `count` elements of `stride` bytes panics "capacity overflow" exactly
/// when `stride * count > isize::MAX`. A hash table does not: hashbrown 0.17.1
/// (`raw.rs`, `capacity_to_buckets` / `TableLayout::calculate_layout_for`) allocates
///
/// ```text
///   buckets = 4 | 8 | 16                              for count < 15
///           = next_power_of_two(count * 8 / 7)        otherwise   (<= 16 * count / 7)
///   len     = round_up(stride * buckets, ctrl_align) + buckets + Group::WIDTH
/// ```
///
/// and panics "Hash table capacity overflow" when `len > isize::MAX - (ctrl_align -
/// 1)` (or `count * 8` overflows, which the count ceiling already charges). With
/// `ctrl_align = max(align_of::<T>(), Group::WIDTH) <= max(stride, 16)` for a
/// non-zero-sized `T` and `Group::WIDTH <= 16`, a panic implies
///
/// ```text
///   (stride + 1) * buckets + 2 * max(stride, 16) + 14 >= isize::MAX
///   ==>  16 * (stride + 1) * count  >=  7 * isize::MAX - 112 * (stride + 1) - 14 * max(stride, 16) - 98
/// ```
///
/// (substituting `buckets <= 16 + 16 * count / 7` and multiplying by 7). That
/// implication is all soundness needs: the failure disjunct below is TRUE whenever
/// the real allocation panics. It is tight to within one bucket doubling —
/// `HashSet::<[u8; 1 << 50]>::with_capacity(n)` fires from `n = 3577`, and the real
/// table panics from `n = 3585` — where `stride * count >= isize::MAX` would wait for
/// `n = 8192` (pinned, with a model of hashbrown's own arithmetic, by
/// `hash_table_layout_bound_tests`). MEASURED on the redo's r1 (`9eadf44e0`): `with_capacity(4097)` of
/// that set passed the constant skip (`4097 * 2^50 < isize::MAX`) and panicked, since
/// 8192 buckets are `2^63` bytes.
///
/// Returns `(scale, threshold)`: the disjunct is `scale * count >= threshold`, the
/// same `Mul(Int, count) >= Int` shape as the `Vec` capacity term.
///
/// Trust (ALLOC-WIDTH-1, 2026-10-08): `isize::MAX` above is the TARGET'S
/// (`object_limit`, [`AllocTarget`]); the derivation uses nothing else about the
/// width (`Group::WIDTH` is 16 with SSE2/NEON and the word size otherwise, at
/// most 16 on every target).
pub(super) fn hash_table_capacity_overflow_term(stride: i128, object_limit: i128) -> (i128, i128) {
    let stride = stride.max(0);
    let scale = 16 * (stride + 1);
    let threshold = 7 * object_limit - 112 * (stride + 1) - 14 * stride.max(16) - 98;
    (scale, threshold)
}

/// Does the hash-table capacity term ([`hash_table_capacity_overflow_term`]) FIRE
/// at the constant count `count` on a target whose object limit is
/// `object_limit`? An overflowing product fires (fail-closed). The lane itself
/// asks the same question through [`capacity_overflow_term`] (its constant skip);
/// this form is what `hash_table_layout_bound_tests` holds against hashbrown's
/// own arithmetic.
#[cfg(test)]
pub(super) fn hash_table_capacity_overflow_fires(
    stride: i128,
    count: i128,
    object_limit: i128,
) -> bool {
    let (scale, threshold) = hash_table_capacity_overflow_term(stride, object_limit);
    scale.checked_mul(count).is_none_or(|bytes| bytes >= threshold)
}

/// Trust (ALLOC-WIDTH-1 / ALLOC-RECEIVER-1, 2026-10-08): the capacity disjunct
/// `scale * count >= threshold` of a counted allocation row whose element is
/// `stride` bytes, or `None` when the row carries no byte line beyond the element
/// ceiling.
///
///  * The line is the TARGET'S `isize::MAX` (`target.object_limit`): `stride * count`
///    for a contiguous buffer, hashbrown's bucket layout for a table
///    ([`hash_table_capacity_overflow_term`]).
///  * An ADDITIONAL count (`receiver_live`: `reserve`, a counted `extend` or
///    `collect_into`) is added to what the receiver already holds, so the threshold
///    is lowered by `scale * held`, `held` being [`AllocTarget::live_receiver_items`]
///    — a strict upper bound on the receiver's length under the 64-bit
///    live-address-space axiom, and the whole object limit on any other target
///    (where the threshold goes negative and the row always fails: a receiver may
///    already be full). Exact algebra, not an approximation: `scale * (count + held)
///    >= threshold` is `scale * count >= threshold - scale * held`.
///  * A stride above one always carries its term (the shape every row carried before
///    2026-10-08). A one-byte contiguous element, or a zero- or one-byte table
///    element, carries it only where the element ceiling does not already exclude
///    every count that reaches it — on a 64-bit target never; a live receiver on a
///    narrower one, always. A zero-sized contiguous element allocates nothing and
///    carries none (its `len + additional` overflow is not a byte line).
pub(super) fn capacity_overflow_term(
    target: AllocTarget,
    stride: i128,
    hash_table: bool,
    receiver_live: bool,
) -> Option<(i128, i128)> {
    if stride < 0 || (!hash_table && stride == 0) {
        return None;
    }
    let (scale, mut threshold) = if hash_table {
        hash_table_capacity_overflow_term(stride, target.object_limit)
    } else {
        (stride, target.object_limit)
    };
    if receiver_live {
        let held = target.live_receiver_items(stride, hash_table);
        threshold = threshold.saturating_sub(scale.saturating_mul(held));
    }
    let excluded_by_ceiling = scale
        .checked_mul(UNBOUNDED_ALLOC_ELEM_CEILING - 1)
        .is_some_and(|largest| largest < threshold);
    (stride > 1 || !excluded_by_ceiling).then_some((scale, threshold))
}

/// Trust (ALLOC-WIDTH-1 / ALLOC-RECEIVER-1, 2026-10-08): the capacity disjunct
/// `scale * count >= threshold` as a formula whose constant is AT LEAST the element
/// ceiling — exactly the same set of counts.
///
/// WHY. trust-router's interval lane (`interval_backend::prove_alloc_bounded`)
/// reads this row's failure `Or` as a branch split, recognizes a failure atom only
/// as `Ge`/`Gt` against a constant of at least `2^28` (`ALLOC_VIOLATION_MIN_THRESHOLD`,
/// so a small guard comparison is never mistaken for one), and dismisses a branch
/// with no recognized atom as one that "allocates nothing". Every capacity line
/// used to be at least `2^28`, so that held implicitly. A live receiver on a
/// target without the live-address-space bound has a NEGATIVE threshold (the row
/// always fails), and a 32-bit table of a huge element a small one; spelled
/// plainly, the interval lane dismissed that disjunct and PROVED the row from the
/// guarded ceiling atom alone (`every_failing_row_stays_unproved_by_the_interval_lane`
/// measured it: `(or (>= n 268435456) (>= (* 8 n) (- 1)))` under `n < 100`).
///
/// So a threshold below the ceiling is spelled `scale * count + shift >=
/// CEILING` with `shift = CEILING - threshold > 0`: the same inequality with the
/// same constant added to both sides, in a shape the interval lane recognizes and
/// can only refute where the true one is false. A threshold at or above the
/// ceiling keeps today's `Mul(Int, count) >= Int` spelling, which the Clean
/// kernel's scaled-chain recognizer reads.
pub(super) fn capacity_atom(scale: i128, threshold: i128, count: &Formula) -> Formula {
    let product = Formula::Mul(Box::new(Formula::Int(scale)), Box::new(count.clone()));
    if threshold >= UNBOUNDED_ALLOC_ELEM_CEILING {
        return Formula::Ge(Box::new(product), Box::new(Formula::Int(threshold)));
    }
    // `saturating`: a shift past `i128::MAX` would need a threshold below
    // `2^28 - i128::MAX`; the saturated atom is then still true at every count >= 0,
    // as the true one is.
    let shift = UNBOUNDED_ALLOC_ELEM_CEILING.saturating_sub(threshold);
    Formula::Ge(
        Box::new(Formula::Add(Box::new(product), Box::new(Formula::Int(shift)))),
        Box::new(Formula::Int(UNBOUNDED_ALLOC_ELEM_CEILING)),
    )
}

/// Trust (W4 HASHMAP r2, 2026-09-27): the rendered callee of a direct-size
/// allocation call is an inherent method of std's `HashMap`/`HashSet`. A
/// REFUSING-direction fence only: the extractor stamps every such call with the
/// hash-table token by DefId, and a call this matches WITHOUT that token is failed
/// closed (never charged `count * stride`, never charged by count alone).
fn callee_is_std_hash_table_inherent(callee: &str) -> bool {
    matches!(
        path_head(callee),
        "std::collections::hash::map::HashMap"
            | "std::collections::HashMap"
            | "std::collections::hash::set::HashSet"
            | "std::collections::HashSet"
    )
}

// ======================================================================
// The AUTHENTICATED-STD-END-TO-END identity for a bounded iterator chain
// ======================================================================
//
// Everything in this section exists because of one measured false proof
// (2026-08-16). The chain walk below GRANTS: reaching a std collection producer
// through length-non-increasing adaptors makes `generate_unbounded_allocation_vcs`
// `continue` past the collect, so the obligation is not weakened, it DISAPPEARS.
// The old adaptor step tested the callee's LAST PATH SEGMENT and nothing else —
// no crate named, no root anchored, no stamp consulted:
//
//     pub struct Endless { pub i: u64 }
//     impl Iterator for Endless { fn next(&mut self) -> Option<u8> { … Some(0) } }
//     pub struct Adapt;
//     impl Adapt { pub fn map(s: core::slice::Iter<'_, u8>, _f: u8) -> Endless { … } }
//     // consumer, an ORDINARY crate name — no impersonation, no `--crate-name` trick:
//     pub fn boom(v: &Vec<u8>) -> Vec<u8> { mycrate::Adapt::map(v.iter(), 0).collect() }
//
// `mycrate::Adapt::map`'s tail is `map`, so the walk stepped through it to
// argument 0, found the genuine `core::slice::<impl [u8]>::iter`, concluded
// "bounded", and deleted the obligation — while `Endless::next` never returns
// `None`, so `boom` allocates without bound in every execution.
//
// AUTHENTICATED IS NOT THE SAME PROPERTY AS BOUNDED. That sentence is the
// 2026-08-17 (round 4) correction, and it is the reason the list below has four
// entries instead of two. The walk's conclusion is `count <= source.len()`, a
// BOUNDEDNESS claim; provenance authentication — however perfect — cannot carry
// it. MEASURED refutation, `fixtures/refute3-rangefrom/`: an impersonating crate
// declares
//
//     impl<'a, T> IntoIterator for &'a Vec<T> {
//         type IntoIter = core::ops::RangeFrom<u64>;          // GENUINE `core`
//         fn into_iter(self) -> …  { core::ops::RangeFrom { start: 0 } }
//     }
//
// `RangeFrom` is real `core`, is correctly NOT stamped, and never returns `None`.
// Both provenance halves read `true` and the obligation was deleted: consumer
// exit 0 with ZERO diagnostics on `stage2 (0a3cd0152)`, against exit 1 / 49
// diagnostic lines for the byte-identical aux renamed `mycrate`.
//
// FOUR conditions, each closing something none of the others does:
//
//   * the CALLEE path of every step (leaf producer and adaptor alike) must be an
//     authenticated sysroot spelling. This is what refuses `mycrate::Adapt::map`
//     and the crate-free module names (`hash_map::`, `::str::`) — and, via the
//     `__trust_crate@` stamp, what refuses a crate built `--crate-name alloc`.
//     Each side anchors the HALF of a qualified `<Self as Trait>::m` spelling
//     that its own claim is about: an ADAPTOR's claim is about the trait method
//     (`vc_callee_is_std_iter_trait_method` anchors the TRAIT path), a leaf
//     PRODUCER's claim is "at most the receiver collection's length"
//     (`producer_receiver_path` anchors the SELF type). Anchoring the raw
//     qualified string instead refuses both — `.into_iter()` is always that
//     spelling — which is the over-decline the 2026-08-17 repair removed.
//   * the RECEIVER of a leaf producer must authenticate as a sysroot collection
//     BY ITS OWN `Ty`, not only by the crate name rendered into the callee string
//     ([`producer_receiver_value_is_authenticated_sysroot`]). The string half is
//     not sufficient: the extractor's stamp is keyed on the callee's DEFINING
//     crate, so an impersonator's crate name appearing only as the qualified SELF
//     TYPE of a real-`core` trait method is never stamped, and
//     `producer_receiver_path` then reads `std::` straight out of the forgery.
//     The receiver OPERAND's type is stamped (it is an ADT name), which is why
//     this conjunct closes the class the string cannot.
//   * the VALUE at every step must have an authenticated sysroot ITERATOR type,
//     read from the MIR local's `Ty` (the compiler's own rendering of the type
//     whose `next` will actually run). This is what refuses a std-rooted callee
//     that RETURNS a user iterator — e.g. the generic spelling
//     `core::iter::traits::collect::IntoIterator::into_iter::<mycrate::Endless>`,
//     whose root anchors perfectly and whose `next` is arbitrary user code.
//   * the VALUE at every step must not be a KNOWN-UNBOUNDED sysroot iterator
//     ([`ty_is_unbounded_sysroot_iterator`]) — the boundedness half. Two tests
//     live there and neither subsumes the other: a deny-list of sysroot names
//     over the rendered field tree, and (2026-08-18) a refusal of any source
//     under a `core::iter::`/`std::iter::` root that the extractor did not render
//     or that belongs to no authenticated sysroot crate.
//
// No pair of these is a substitute for another. The extractor stamps callee paths
// AND `Ty::Adt` names (both renderers, since 2026-08-17) but stamps neither when
// the impersonator's name reaches the string as somebody else's generic argument;
// the type of a value says nothing about which crate's function produced it; and
// a genuine sysroot type says nothing at all about how many elements it yields.

/// Adaptors that preserve the source iterator's length EXACTLY, so the collected
/// count equals the count of their own source (recurse through them).
///
/// GRANTING — takes the `callee`, not only its tail, ON PURPOSE. The bare
/// `is_len_preserving_adaptor(tail)` this replaces was consumed at two sites and
/// authenticated nothing at either; giving the predicate no tail-only spelling is
/// what stops the next caller from re-opening the hole. [`vc_callee_is_std_iter_trait_method`]
/// is the shared iterator-protocol authenticator already used by the yield-fact
/// lane: it accepts both spellings the extractor produces for a std `Iterator`
/// method — the generic `std::iter::Iterator::map` and the qualified
/// `<core::slice::iter::Iter<'_, T> as core::iter::traits::iterator::Iterator>::cloned::<'_, T>`
/// (both spellings measured in the real dump corpus) — and refuses a trait path
/// that is not `core::iter::`/`std::iter::`-rooted.
pub(super) fn is_authenticated_std_len_preserving_adaptor(callee: &str, tail: &str) -> bool {
    matches!(
        tail,
        "map" | "filter_map" | "inspect" | "enumerate" | "copied" | "cloned" | "rev" | "by_ref"
    ) && vc_callee_is_std_iter_trait_method(callee, "Iterator", tail)
}

/// Adaptors that yield AT MOST the source iterator's length — the exactly-length
/// -preserving set plus the ones that drop elements. Sound for the bounded-source
/// walk (`<= source.len()` is all it needs) but NOT for count reconstruction,
/// which is why [`is_authenticated_std_len_preserving_adaptor`] stays separate.
///
/// GRANTING, and authenticated for the same reason. `Option::map`/`Option::filter`
/// (measured in the corpus as `std::option::Option::<T>::map`) used to satisfy the
/// old tail-only test; they are refused here, at no cost — `Option` is not an
/// `Iterator`, so no `Option::map` result can reach a `collect` sink.
pub(super) fn is_authenticated_std_len_nonincreasing_adaptor(callee: &str, tail: &str) -> bool {
    // Trust (2026-10-07): `zip` yields `min(self, other)` items and reports
    // `min(lower)`, so at most its RECEIVER's: the walk recurses into argument 0 only
    // and never needs the other side bounded. `fuse`, `skip_while` and `map_while`
    // yield and report no more than their source. `peekable` is NOT here: after a peek
    // it reports one more than its source, which a str view's `+ 1` does not cover.
    is_authenticated_std_len_preserving_adaptor(callee, tail)
        || (matches!(
            tail,
            "filter"
                | "take"
                | "skip"
                | "step_by"
                | "take_while"
                | "zip"
                | "fuse"
                | "skip_while"
                | "map_while"
        ) && vc_callee_is_std_iter_trait_method(callee, "Iterator", tail))
}

/// An authenticated FREE function in std's iterator module (`core::iter::repeat_n`),
/// as opposed to an `Iterator` trait method. Anchored to the `core::iter::`/
/// `std::iter::` module root after generic stripping, so `mycrate::iter::repeat_n`
/// and `mycrate::repeat_n` fail closed.
pub(super) fn is_authenticated_std_iter_free_fn(callee: &str, name: &str) -> bool {
    if callee.contains(" as ") || callee.starts_with('<') {
        return false;
    }
    let normalized = vc_strip_generics_cow(callee);
    (normalized.starts_with("core::iter::") || normalized.starts_with("std::iter::"))
        && normalized.strip_suffix(name).is_some_and(|head| head.ends_with("::"))
}

/// The VALUE-side half of the identity: `ty` is an authenticated sysroot
/// ITERATOR-carrying type, i.e. the `next` that will run is std's own code.
///
/// A `Ty::Ref` is transparent (`Iterator::by_ref` hands out `&mut I`, and a
/// reference's iterator identity is its pointee's). Everything else that is not a
/// root-authenticated ADT fails closed — a user ADT, a type parameter, a
/// `Ty::Unsupported`, a bare integer placeholder.
///
/// This is deliberately a ROOT test and not a closed list of std iterator ADTs:
/// the closed list would have to be maintained against every std release, and it
/// buys nothing against the only forgery a root test misses (a crate built
/// `--crate-name core` can name its struct `core::iter::adapters::map::Map` just
/// as easily as `core::Whatever`). That forgery is closed on the CALLEE side, by
/// the stamp; see the module note above.
///
/// PROVENANCE ONLY, and the name says so: a `true` here means "std's own `next`
/// runs", never "the iterator is finite". `core::ops::range::RangeFrom` passes
/// this test and yields forever. The boundedness question is
/// [`ty_is_unbounded_sysroot_iterator`]'s, and the walk asks BOTH.
pub(super) fn ty_is_authenticated_std_iterator(ty: &Ty) -> bool {
    match ty {
        Ty::Ref { inner, .. } => ty_is_authenticated_std_iterator(inner),
        Ty::Adt { name, .. } => trust_types::path_root_is_authenticated_sysroot_crate(name),
        _ => false,
    }
}

/// The sysroot iterator ADTs that are GENUINELY UNBOUNDED — a `Some` here is a
/// refusal, so the set is a DENY-list and every entry is a fact about std, not
/// about provenance.
///
/// Two anchored families, and the anchoring is the same shape both lanes already
/// use so they cannot drift:
///
///  * the RANGE family, read through [`range_family_adt_name`]. This is the exact
///    COMPLEMENT of [`iter_collect_count`]'s bounded pair: that function counts
///    `Range` and `RangeInclusive` and refuses the rest of the family (its doc
///    records `RangeFrom` by name — *"it is unbounded, has no `end` field"*).
///    Writing the complement rather than a second literal list is what stops the
///    two lanes from disagreeing about which ranges are finite the next time the
///    family grows.
///  * `core::iter::`/`std::iter::`-rooted sources and adaptors that yield forever
///    on their own account, enumerated from this tree's `library/core/src/iter/
///    sources/` (`repeat`, `repeat_with`, `successors`, `from_fn`,
///    `from_coroutine`) plus the one adaptor that manufactures infinity from a
///    finite source, `adapters::cycle::Cycle`. The other `sources` siblings are
///    deliberately absent because they are finite by construction and refusing
///    them would be an over-decline: `Empty` (0), `Once`/`OnceWith` (1), and
///    `RepeatN` (`n`, and no arm of the bounded-source walk produces one).
///
/// Matched on the LAST SEGMENT of the path HEAD — everything before the first
/// `<` — under a `core::iter::` / `std::iter::` root, so both spellings the
/// extractor emits are covered (the defining-module
/// `core::iter::sources::repeat::Repeat` and the re-export `core::iter::Repeat`)
/// while a user `mycrate::iter::Repeat` is not.
///
/// The head, and not [`vc_strip_generics`], for a MEASURED reason: that helper
/// counts `<`/`>` and a function-pointer argument contains a bare `>` in its
/// `->`, so `RepeatWith<fn() -> u8>` normalizes to `…::RepeatWith u8` and the
/// last segment stops matching. A REFUSING predicate that silently stops
/// refusing is the worst failure direction available, so this one does not
/// depend on balanced-angle-bracket parsing at all. (`vc_strip_generics` itself
/// stopped reading the arrow's `>` as a bracket on 2026-09-25, W4 ITER-HOF (c) —
/// its granting callers were failing closed on every fn-item turbofish. This
/// refusal stays on `path_head` regardless: it must not depend on ANY bracket
/// parse being right.)
pub(super) fn unbounded_sysroot_iterator_adt_name(name: &str) -> Option<&'static str> {
    if let Some(family) = range_family_adt_name(name) {
        return (!matches!(family, "Range" | "RangeInclusive")).then_some(family);
    }
    let head = path_head(name);
    if !(head.starts_with("core::iter::") || head.starts_with("std::iter::")) {
        return None;
    }
    match head.rsplit("::").next()? {
        "Repeat" => Some("Repeat"),
        "RepeatWith" => Some("RepeatWith"),
        "Successors" => Some("Successors"),
        "FromFn" => Some("FromFn"),
        "FromCoroutine" => Some("FromCoroutine"),
        "Cycle" => Some("Cycle"),
        _ => None,
    }
}

/// The path HEAD — everything before the first `<`, without a trailing `::`. The
/// same normalization [`unbounded_sysroot_iterator_adt_name`] has always used, and
/// deliberately NOT [`vc_strip_generics`]: see that function's doc for the
/// measured `fn() -> u8` mis-parse a balanced-bracket walk suffers.
fn path_head(name: &str) -> &str {
    name.split('<').next().unwrap_or(name).trim_end_matches("::")
}

/// `name` roots in the sysroot ITERATOR module — the crate-anchored spelling of
/// "this ADT is one of std's own iterator sources or adaptors". Factored out of
/// [`unbounded_sysroot_iterator_adt_name`] so the deny-LIST and the
/// unestablished-source refusal below cannot come to disagree about which names
/// are std's iterator machinery.
///
/// A stamped path (`__trust_crate@…::core::iter::…`) does not start with
/// `core::iter::`, so an impersonator's adaptor is not an adaptor here.
fn path_head_is_sysroot_iter_module(name: &str) -> bool {
    let head = path_head(name);
    head.starts_with("core::iter::") || head.starts_with("std::iter::")
}

/// `name` is std's own `Option`, by its two rendered spellings (the defining
/// module `core::option::Option` and the `std` re-export). Anchored the same way
/// as [`path_head_is_sysroot_iter_module`], so an impersonator's stamped
/// `Option` is not one.
fn path_head_is_sysroot_option(name: &str) -> bool {
    matches!(path_head(name), "core::option::Option" | "std::option::Option")
}

/// `name` is a sysroot SOURCE TRANSPORT: an ADT that is not itself in an
/// iterator module but whose payload IS the adapted source, so stopping at it
/// would read straight past the thing being measured.
///
/// `Box<I>` is the one that matters and it is not hypothetical: `impl Iterator
/// for Box<I>` exists, so `IntoIter = Box<endcrate::Endless>` is a legal
/// endless source whose root authenticates. MEASURED before this arm existed:
/// `Box<endcrate::Endless>` and `Map<Box<endcrate::Endless>, F>` both kept the
/// bounded-collect grant — 0 rows against their controls' 1, and the
/// `Box`-rooted one compiled exit 0 with zero diagnostic lines.
///
/// `Unique`/`NonNull` are here for the same reason one level down: they are how
/// `Box`'s payload is rendered once the extractor expands it. Note the ELEMENT
/// type of a bounded iterator also travels through `NonNull` — that is why this
/// predicate is consulted ONLY from the source-chain walk, which is already
/// inside a sysroot adaptor's source field, and never from the root scan.
fn path_head_is_source_transport(name: &str) -> bool {
    matches!(
        path_head(name),
        "alloc::boxed::Box"
            // Trust (1.101): how Box's payload renders one level down now.
            | "alloc::boxed::BoxRaw"
            | "std::boxed::Box"
            | "core::ptr::unique::Unique"
            | "core::ptr::non_null::NonNull"
    )
}

/// The BOUNDEDNESS half of the value-side identity: `ty` is (or CONTAINS) a
/// sysroot iterator that yields without end, so no walk may conclude
/// `count <= source.len()` about it.
///
/// REFUSING, not granting — a `true` deletes a grant, so the failure direction is
/// safe and the recursion may fail closed. It is a separate function from
/// [`ty_is_authenticated_std_iterator`] on purpose: three rounds were spent
/// perfecting provenance authentication, and the refutation that survived them
/// defeated the value side with a GENUINE, correctly-unstamped `core` ADT. These
/// are two different properties and the source now spells them separately.
///
/// THE FIELD WALK IS LOAD-BEARING, and measured. A name test alone reads
/// `core::iter::adapters::map::Map` — bounded-sounding, `core`-rooted — for the
/// value `Map<RangeFrom<u64>, fn(u64) -> u64>`, because
/// [`vc_strip_generics`] drops exactly the argument that carries the infinity.
/// The impersonator only has to write `type IntoIter = core::iter::Map<…>`, which
/// MEASURABLY still deletes the unbounded-allocation row on the unpatched tree
/// (`fixtures/unbounded-sysroot-iterator-2026-08-17/`). The compiler's own
/// rendering of the local's type carries `Map`'s `iter` field, and that field IS
/// the `RangeFrom`, so the answer is already in the bundle.
///
/// THE ERASURE, and why the deny-list alone is not the whole refusal (2026-08-18).
/// The extractor does not always render a field subtree: `compact_oversized_field`
/// collapses one over 64 nodes to a by-name `Ty::Datatype`, and an expanding
/// same-ADT recursion becomes `Ty::Unsupported`. Both used to hit a `_ => false`
/// arm here — a GRANT — so a deny-listed marker nested deeply enough was ERASED
/// before the name test could see it. MEASURED, `fixtures/compacted-source-
/// 2026-08-18/`: `Fuse<StepBy<Skip<Peekable<Enumerate<Cycle<Range<u64>>>>>>>` —
/// all genuine `core`, genuinely infinite — renders as
/// `Adt Fuse { iter: Datatype{"core::option::Option"} }` with the `Cycle` gone,
/// and the consumer compiled **exit 0 with zero diagnostic lines** while its
/// one-crate-name-away control was exit 1 with the row present.
///
/// So the refusal is now TWO tests, and neither subsumes the other:
///
///  * the DENY-LIST, over `Ty::Adt` names and now `Ty::Datatype` names too
///    (`compact_oversized_field` PRESERVES an aggregate's name, so a compacted
///    `Cycle` is still refusable by name);
///  * [`ty_iterator_source_boundedness_unestablished`], which refuses an
///    UNRENDERED or unauthenticated source under a sysroot-iterator root. This is
///    the one that catches the erasure above, where the surviving name
///    (`core::option::Option`) is not deny-listed and never could be.
///
/// The second test is deliberately ROOT-SCOPED rather than a blanket "no
/// `Ty::Datatype` anywhere". MEASURED over the 2 587 checked-in bundles: 209 of
/// them carry a `Ty::Datatype` marker somewhere, and refusing on any of them
/// would be a large, unjustified over-decline — a marker inside
/// `alloc::vec::into_iter::IntoIter<SomeBigUserEnum>` says nothing about how many
/// elements the iterator yields. Under a `core::iter::`/`std::iter::` ADT it says
/// exactly the thing this lane needs and cannot otherwise get: the source it
/// adapts was not rendered, so its boundedness is not established.
pub(super) fn ty_is_unbounded_sysroot_iterator(ty: &Ty) -> bool {
    ty_is_unbounded_sysroot_iterator_rec(ty, 0)
        || ty_iterator_source_boundedness_unestablished(ty, 0)
}

/// The DENY-LIST half of [`ty_is_unbounded_sysroot_iterator`] alone — for the one
/// caller whose sources are re-established argument by argument (a value built by
/// std `Iterator::chain`; see `collect_source_live_count`).
fn ty_is_denylisted_unbounded_sysroot_iterator(ty: &Ty) -> bool {
    ty_is_unbounded_sysroot_iterator_rec(ty, 0)
}

fn ty_is_unbounded_sysroot_iterator_rec(ty: &Ty, depth: usize) -> bool {
    if depth > TY_UNBOUNDED_SCAN_DEPTH {
        return true;
    }
    match ty {
        Ty::Ref { inner, .. } => ty_is_unbounded_sysroot_iterator_rec(inner, depth + 1),
        Ty::RawPtr { pointee, .. } => ty_is_unbounded_sysroot_iterator_rec(pointee, depth + 1),
        Ty::Adt { name, fields, .. } => {
            unbounded_sysroot_iterator_adt_name(name).is_some()
                || fields.iter().any(|(_, f)| ty_is_unbounded_sysroot_iterator_rec(f, depth + 1))
        }
        // A compacted / by-name aggregate. `compact_oversized_field` keeps the
        // aggregate's NAME, so the deny-list still applies to whatever it names;
        // its `variants` are empty for a by-name reference and carry the fields
        // for a defining occurrence, so both are walked.
        Ty::Datatype { name, variants } => {
            unbounded_sysroot_iterator_adt_name(name).is_some()
                || variants.iter().any(|(_, fs)| {
                    fs.iter().any(|(_, f)| ty_is_unbounded_sysroot_iterator_rec(f, depth + 1))
                })
        }
        Ty::Tuple(elems) => {
            elems.iter().any(|e| ty_is_unbounded_sysroot_iterator_rec(e, depth + 1))
        }
        _ => false,
    }
}

/// REFUSING, the second half of the boundedness test: `ty` is a sysroot ITERATOR
/// ADT (`core::iter::`/`std::iter::`-rooted) whose SOURCE is a rendering this walk
/// cannot decide, so `count <= source.len()` is not established for it.
///
/// TWO measured shapes, closed by one rule because they are one defect — the
/// source of a std adaptor is not something the deny-list can speak about:
///
///  * **the compacted source** (`fixtures/compacted-source-2026-08-18/`). The
///    field is a `Ty::Datatype` or `Ty::Unsupported` marker: the extractor
///    declined to render the subtree, so nothing downstream knows what it was.
///    An UNRENDERED source is exactly "boundedness not established".
///  * **the composed source** (`fixtures/adaptor-over-user-iterator-2026-08-18/`).
///    The field is an ADT rooted in no authenticated sysroot crate —
///    `Map<endcrate::Endless, fn(u64) -> u64>`, a `core`-rooted adaptor over a
///    USER iterator whose `next` never returns `None`. It passes BOTH existing
///    value-side conjuncts and always did: [`ty_is_authenticated_std_iterator`] is
///    a ROOT test and reads only `core::iter::adapters::map::Map`, and the
///    deny-list is a list of SYSROOT names, which `endcrate::Endless` is not.
///    MEASURED: 0 rows against the control's 1.
///
/// WHAT THIS DOES NOT REACH, and the walk must not be credited with it. When the
/// endless iterator is defined in the IMPERSONATING crate itself the field renders
/// `std::vec::Endless`, whose root authenticates, and no NAME test can tell it
/// from a real std iterator. Distinguishing it is the PRODUCER stamp's job
/// (`trust_mir_extract::convert::impersonates_sysroot_crate`, whose residual R2 —
/// a `#[rustc_diagnostic_item]` forgery — reaches the crate under compilation,
/// because an EXTERNAL crate is authenticated by artifact residency rather than
/// by attributes). This
/// function closes the composed shape only where the source crate is honestly
/// named; the sysroot-named-source half belongs to the stamp.
///
/// THE DESCENT STOPS AT THE FIRST NON-ITERATOR SYSROOT ADT, and that bound is what
/// keeps this from being an over-decline. Descending further would read
/// `alloc::vec::into_iter::IntoIter<mycrate::Foo>`'s `NonNull<mycrate::Foo>` —
/// the ELEMENT type of a perfectly bounded iterator — as an unauthenticated
/// source. A `core::iter::`/`std::iter::` ADT is walked into, and so is a
/// sysroot SOURCE TRANSPORT (`Box`, `Unique`, `NonNull` —
/// [`path_head_is_source_transport`]); nothing else is. The earlier wording here
/// said only an iterator-module ADT has "a field the thing being adapted", which
/// `impl Iterator for Box<I>` refutes.
fn ty_iterator_source_boundedness_unestablished(ty: &Ty, depth: usize) -> bool {
    if depth > TY_UNBOUNDED_SCAN_DEPTH {
        return true;
    }
    match ty {
        // `Iterator::by_ref` hands out `&mut I`; a tuple/aggregate temporary can
        // carry the adaptor. Same peeling the deny-list walk does.
        Ty::Ref { inner, .. } => ty_iterator_source_boundedness_unestablished(inner, depth + 1),
        Ty::RawPtr { pointee, .. } => {
            ty_iterator_source_boundedness_unestablished(pointee, depth + 1)
        }
        Ty::Tuple(elems) => {
            elems.iter().any(|e| ty_iterator_source_boundedness_unestablished(e, depth + 1))
        }
        Ty::Adt { name, fields, .. }
            if path_head_is_sysroot_iter_module(name) || path_head_is_source_transport(name) =>
        {
            fields.iter().any(|(_, f)| adaptor_source_field_unestablished(f, depth + 1))
        }
        _ => false,
    }
}

/// One FIELD of a sysroot iterator adaptor: `true` when its boundedness is not
/// established. See [`ty_iterator_source_boundedness_unestablished`].
fn adaptor_source_field_unestablished(ty: &Ty, depth: usize) -> bool {
    if depth > TY_UNBOUNDED_SCAN_DEPTH {
        return true;
    }
    match ty {
        Ty::Ref { inner, .. } => adaptor_source_field_unestablished(inner, depth + 1),
        Ty::RawPtr { pointee, .. } => adaptor_source_field_unestablished(pointee, depth + 1),
        // The extractor's two "not rendered" markers, in the one position where
        // that fact is load-bearing. A `Ty::Datatype` here is a
        // `compact_oversized_field` collapse or a by-name recursive reference; a
        // `Ty::Unsupported` is an expanding-generic recursion, a spent lowering
        // budget, or a bare `TyKind::Param`. None of them says how many elements
        // the adapted source yields.
        Ty::Datatype { .. } | Ty::Unsupported { .. } => true,
        Ty::Adt { name, fields, variants, .. } => {
            if !trust_types::path_root_is_authenticated_sysroot_crate(name) {
                // The composed shape: a std adaptor over somebody else's iterator.
                true
            } else if path_head_is_sysroot_iter_module(name) {
                // An adaptor over an adaptor — keep walking the source chain.
                fields.iter().any(|(_, f)| adaptor_source_field_unestablished(f, depth + 1))
            } else if path_head_is_source_transport(name) {
                // `impl Iterator for Box<I>` — the payload IS the source, so
                // stopping here reads past it. See `path_head_is_source_transport`.
                fields.iter().any(|(_, f)| adaptor_source_field_unestablished(f, depth + 1))
            } else if path_head_is_sysroot_option(name) {
                // `Option` is the ONE non-iterator sysroot ADT core's own adaptors
                // hold a SOURCE in, so it is transparent here and nothing else is.
                // MEASURED, `Chain<endcrate::Endless, core::option::IntoIter<u64>>`:
                // the source renders as `("a", Adt core::option::Option { … })`
                // with the user iterator one level down, and stopping at `Option`
                // granted it (0 rows against the control's 1). Both renderings are
                // walked because the extractor emits an enum as a flattened field
                // list AND a variant list.
                fields.iter().any(|(_, f)| adaptor_source_field_unestablished(f, depth + 1))
                    || variants.iter().any(|v| {
                        v.fields
                            .iter()
                            .any(|(_, f)| adaptor_source_field_unestablished(f, depth + 1))
                    })
            } else {
                // Every other sysroot ADT — `NonNull`, `PhantomData`,
                // `slice::Iter`, `vec::IntoIter`, `Range`. Its own boundedness is
                // the deny-list walk's question, not this one's; stopping here is
                // what bounds the over-decline (see above).
                false
            }
        }
        // A scalar/pointer/function/closure/slice/array payload carries no source.
        _ => false,
    }
}

/// Field-nesting budget for [`ty_is_unbounded_sysroot_iterator`]. MEASURED: the
/// deepest iterator value in the 2 572-bundle corpus is
/// `alloc::vec::into_iter::IntoIter`, whose rendered field tree bottoms out at 6;
/// 16 leaves room for a nested adaptor stack without ever making the budget
/// itself the answer for a real iterator.
const TY_UNBOUNDED_SCAN_DEPTH: usize = 16;

/// [`ty_is_unbounded_sysroot_iterator`] for the type of the local an operand
/// reads. `false` when there is no such local — this is the REFUSING side, so an
/// unreadable value is handled by [`operand_is_authenticated_std_iterator_value`],
/// which requires the same local and fails closed on its absence.
pub(super) fn operand_is_unbounded_sysroot_iterator_value(
    func: &VerifiableFunction,
    op: &Operand,
) -> bool {
    operand_local(op)
        .and_then(|local| crate::local_ty_ref(func, local))
        .is_some_and(ty_is_unbounded_sysroot_iterator)
}

/// [`ty_is_authenticated_std_iterator`] for the type of the local an operand
/// reads. `false` for anything without a single unprojected local — the same
/// shape [`operand_local`] already requires of every step of the walk.
pub(super) fn operand_is_authenticated_std_iterator_value(
    func: &VerifiableFunction,
    op: &Operand,
) -> bool {
    operand_local(op)
        .and_then(|local| crate::local_ty_ref(func, local))
        .is_some_and(ty_is_authenticated_std_iterator)
}

/// The (single, unprojected) local a value operand reads, if any.
pub(super) fn operand_local(op: &Operand) -> Option<usize> {
    match op {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => Some(p.local),
        _ => None,
    }
}

/// Find the defining statement/terminator of `local` within `func` — the
/// `Rvalue` that assigns it, or the `Call` whose destination it is — when that is
/// the ONE value `local` holds at every read.
///
/// Every caller INLINES the answer: the count derived from it BECOMES the `collect`
/// obligation's count (`iter_collect_count`'s own doc: "an UNDER-count is a false
/// proof"), the `sum`/`product` row's count and item range (`fold_source_bound`),
/// a slice index's range bounds (`collection_range::norm_usize_range`), a literal
/// `Duration`'s nanoseconds (`numeric_panic::literal_duration_nanos`). So the
/// question is the seam's VALUE question, `local_defs::unique_value_modulo_whole_drops`:
/// `unique_value_def`'s and `unique_value_call`'s answer, whichever channel the one
/// definition is on. It refuses a PARAMETER (its ENTRY definition is a second value), a
/// second whole write, a projected store (`LocalWrite::Partial`), a `&mut`/`&raw` alias
/// (`LocalWrite::Escape`) and an unlocatable write. Its one narrowing, a `Drop` of the
/// WHOLE local, ends the value rather than changing it (argued on the question):
/// `first.to_uppercase()` live across the `flat_map` call in the `capitalize` idiom is
/// dropped on that call's unwind edge, and the plain value questions would refuse it.
///
/// Trust (CL-FOLD-LOCALDEF-1, 2026-10-11): this asked
/// `local_defs::has_one_explicit_def` and then took the first matching block, and that
/// is the COUNTING question. It charges the entry definition and a second whole write,
/// but by design it counts neither `Partial` nor `Escape` (`body_value_count`'s doc), so
/// `let mut r = 0u8..4; r.end = 200; r.sum::<u8>()` resolved `r` to `0u8..4`. The same
/// held after `widen(&mut r)`, `mem::swap(&mut r, &mut big)`, `let p = &mut r; p.end =
/// 200;` and a closure capturing `r` or `r.end` by unique borrow. The sum row was
/// PROVED, kernel-certified, under `-Ztrust-policy=certify` (stage 1 of `2bf0ad72e3`),
/// and the program panics "attempt to add with overflow". The slice-index lane's
/// `RangeInclusive::new` arm (`*p = 0..=100` after `0..=0`) and the `Duration` literal
/// lane (`d = Duration::MAX` through a closure or `*p`) were the same hole.
/// `has_one_explicit_def` itself is unchanged: its count-channel callers key facts on
/// the BARE NAME, under version renaming, and do not inline a definition.
///
/// An alias is re-admitted in exactly two upper-bound consumers, [`fold_source_bound`]
/// and [`collect_source_live_count`], and only when every alias use is core's own
/// `Iterator::next` ([`origin_def_through_core_next`]).
pub(super) fn local_def(func: &VerifiableFunction, local: usize) -> Option<LocalDef<'_>> {
    whole_definition_as_local_def(crate::local_defs::unique_value_modulo_whole_drops(func, local)?)
}

/// Trust (W4 ITER-HOF (c), 2026-09-25; rebased 2026-09-29): the compiler-minted
/// [`trust_types::CalleeKey`] of the `Call` that is `local`'s ONE definition (the
/// same VALUE question as [`local_def`] since CL-FOLD-LOCALDEF-1) — the
/// `DefId`-derived identity a GRANTING arm keys on in preference to the rendered
/// callee. `None` when the definition is not a keyed call.
#[cfg(test)]
fn local_def_call_key(func: &VerifiableFunction, local: usize) -> Option<&trust_types::CalleeKey> {
    whole_definition_call_key(crate::local_defs::unique_value_modulo_whole_drops(func, local)?)
}

fn whole_definition_as_local_def(
    def: crate::local_defs::WholeDefinition<'_>,
) -> Option<LocalDef<'_>> {
    match def {
        crate::local_defs::WholeDefinition::Assign(rvalue) => Some(LocalDef::Rvalue(rvalue)),
        crate::local_defs::WholeDefinition::Call(Terminator::Call {
            func: callee, args, ..
        }) => Some(LocalDef::Call { callee, args }),
        crate::local_defs::WholeDefinition::Call(_) => None,
    }
}

fn whole_definition_call_key(
    def: crate::local_defs::WholeDefinition<'_>,
) -> Option<&trust_types::CalleeKey> {
    match def {
        crate::local_defs::WholeDefinition::Call(Terminator::Call { callee_key, .. }) => {
            callee_key.as_ref()
        }
        _ => None,
    }
}

/// Trust (CL-FOLD-LOCALDEF-1, 2026-10-11): true iff core's own `Iterator::next` is the
/// ONLY thing any `&mut`/`&raw` alias of `local` is used for.
/// `iter_mut_borrows_only_feed` with an admit that accepts exactly argument 0 of a call
/// that is `Iterator::next` by its rendered path (`callee_is_iterator_next`) AND by its
/// compiler-minted key (`CalleeKey::opt_is_real_sysroot`). Every conduit is then defined
/// once and is never read, written through, dropped, switched on, asserted on, captured
/// or handed to anything else: not `mem::swap`, not a user `fn(&mut Range<_>)`, not a
/// closure environment, not `by_ref`. True vacuously when there is no alias; the
/// origin questions below then refuse everything the value questions refuse.
///
/// This is the licence under which [`origin_def_through_core_next`] and
/// [`origin_call_key_through_core_next`] re-admit the alias channel that
/// [`local_def`] refuses. They have exactly two consumers, [`fold_source_bound`] and
/// [`collect_source_live_count`]. Each reads its answer only as an UPPER bound on what
/// the iterator still yields, and each states that argument where it asks.
fn core_next_is_the_only_alias_use(func: &VerifiableFunction, local: usize) -> bool {
    iter_mut_borrows_only_feed(func, local, |_, term, arg_ix| {
        arg_ix == 0
            && matches!(term, Terminator::Call { func: callee, callee_key, .. }
                if callee_is_iterator_next(callee)
                    && trust_types::CalleeKey::opt_is_real_sysroot(callee_key.as_ref()))
    })
}

/// The definition `local` was BUILT by, when [`local_def`] declines it only because the
/// local is `&mut`-borrowed by core's own `Iterator::next`
/// ([`core_next_is_the_only_alias_use`]). This is the ORIGIN question
/// (`local_defs::unique_initializing_modulo_whole_drops`), which differs from the value
/// question only in the alias channel and still refuses a parameter, a second whole
/// write, a field store (`r.end = 200`) and an unlocatable write. So, under the gate,
/// the only mutation `local` undergoes is `next` on itself, and the answer is "what it
/// was built from", NOT "what it holds". Use it only through a consumer whose argument
/// says why a bound read from the construction survives `next`.
fn origin_def_through_core_next(func: &VerifiableFunction, local: usize) -> Option<LocalDef<'_>> {
    let def = whole_definition_as_local_def(
        crate::local_defs::unique_initializing_modulo_whole_drops(func, local)?,
    )?;
    core_next_is_the_only_alias_use(func, local).then_some(def)
}

/// [`origin_def_through_core_next`]'s `CalleeKey` twin, as [`local_def_call_key`] is
/// [`local_def`]'s.
#[cfg(test)]
fn origin_call_key_through_core_next(
    func: &VerifiableFunction,
    local: usize,
) -> Option<&trust_types::CalleeKey> {
    let key = whole_definition_call_key(crate::local_defs::unique_initializing_modulo_whole_drops(
        func, local,
    )?)?;
    core_next_is_the_only_alias_use(func, local).then_some(key)
}

fn local_or_core_next_origin_def_and_key(
    func: &VerifiableFunction,
    local: usize,
) -> (Option<LocalDef<'_>>, Option<&trust_types::CalleeKey>) {
    if crate::local_defs::is_parameter(func, local) {
        return (None, None);
    }
    let whole_def = crate::local_defs::unique_value_modulo_whole_drops(func, local).or_else(|| {
        let init_def = crate::local_defs::unique_initializing_modulo_whole_drops(func, local)?;
        core_next_is_the_only_alias_use(func, local).then_some(init_def)
    });
    match whole_def {
        Some(whole_def) => (
            whole_definition_as_local_def(whole_def),
            whole_definition_call_key(whole_def),
        ),
        None => (None, None),
    }
}

/// THE FOLD SOURCE'S ORIGIN, for [`fold_source_bound`] alone: the `Range` /
/// `RangeInclusive` aggregate, or the `RangeInclusive::new` call, that a `sum`/`product`
/// source local was built by ([`origin_def_through_core_next`]), and nothing else.
///
/// It keeps `let mut r = 0u8..4; r.next(); r.sum::<u8>()` proved: `next` takes `&mut r`
/// (`LocalWrite::Escape`), so the VALUE question refuses `r`, and without this the row
/// is the `iterator-fold-overflow` Unknown, which the default lane refuses.
///
/// THE ARGUMENT. (1) Under [`core_next_is_the_only_alias_use`] and the origin question,
/// the only mutation of `local` is `Iterator::next` on itself. (2) The answer is used
/// only when it IS a std `Range`/`RangeInclusive` aggregate (`range_family_adt_name`) or
/// `RangeInclusive::new` (`is_range_inclusive_new_call`), so the receiver is core's own
/// range, and `next` is core's impl (coherence: no other crate can implement core's
/// `Iterator` for core's `Range`). (3) That `next` only moves `start` forward
/// (`RangeInclusive::next` may also set `exhausted`) and never moves `end`, so every
/// item still to come lies in the constructed `[start, end)` / `[start, end]`, and at
/// most the constructed count remain. (4) [`FoldSourceBound`]'s two slots are both
/// UPPER bounds (an over-count or a wider item range can only add a counterexample).
///
/// What it does NOT license: the CURRENT position, or an EXACT count.
/// `iter_collect_count`, the slice lane and the `Duration` lane read [`local_def`] only.
fn fold_range_origin(func: &VerifiableFunction, local: usize) -> Option<LocalDef<'_>> {
    let origin = whole_definition_as_local_def(
        crate::local_defs::unique_initializing_modulo_whole_drops(func, local)?,
    )?;
    let is_std_range = match &origin {
        LocalDef::Rvalue(Rvalue::Aggregate(AggregateKind::Adt { name, .. }, _)) => {
            matches!(range_family_adt_name(name), Some("Range" | "RangeInclusive"))
        }
        LocalDef::Call { callee, .. } => is_range_inclusive_new_call(callee),
        LocalDef::Rvalue(_) => false,
    };
    (is_std_range && core_next_is_the_only_alias_use(func, local)).then_some(origin)
}

/// Reconstruct the element count feeding a `collect`/`from_iter` sink when it is
/// statically derivable: a `Range` aggregate (`a..b` ⇒ `b - a`) or a
/// `RangeInclusive` one (`a..=b` ⇒ `b - a + 1`), constant-folded so the ceiling
/// skip still applies, optionally behind length-preserving adaptors
/// (`map`/`filter_map`/…) or capped by `take(n)`. Returns `None` when the length
/// is not recoverable — SOUND: emit no obligation rather than a false positive on
/// every `collect` (which would break drop-in Rust compatibility).
///
/// DIRECTION OF THE APPROXIMATION, for both range families. The formula is EXACT
/// on a non-empty range. On an EMPTY one (`end < start` for `..`, `end + 1 <
/// start` for `..=`) it goes non-positive while the true count is `0` — an
/// under-count, but only in the region where both values are far below the
/// ceiling, so the obligation `count < CEILING` is discharged for the same reason
/// in both readings. A `RangeInclusive` whose `exhausted` flag is already `true`
/// yields nothing while the formula still says `end - start + 1`: an OVER-count,
/// which can only ADD an obligation. Neither direction can turn an unbounded
/// allocation into a proof.
///
/// `RangeFrom` (`a..`) is deliberately absent from the aggregate arm: it is
/// unbounded, has no `end` field, and must reach a `take(n)` before any count
/// exists. The pre-2026-08-17 `name.contains("Range")` test matched it and then
/// fell out through `ops.get(1)?`; the family-anchored match refuses it up front.
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
        // GRANTING: the count this returns becomes the obligation's own count, so
        // an UNDER-count is a false proof (the solver discharges a ceiling the
        // program does not respect). The old test was `name.contains("Range")`,
        // which named no crate — a user `struct MyRange { a, b }` implementing an
        // endless `Iterator` matched it — and which also swallowed
        // `RangeInclusive` into the EXCLUSIVE arithmetic, under-counting it by one
        // at the ceiling boundary. [`range_family_adt_name`] is the anchored
        // range-family identity this crate already uses for the slice-index and
        // yield-fact lanes (one authenticator, not a second spelling of it); the
        // two families now get their own arithmetic instead of one being declined.
        LocalDef::Rvalue(Rvalue::Aggregate(AggregateKind::Adt { name, .. }, ops))
            if let Some(family @ ("Range" | "RangeInclusive")) = range_family_adt_name(name) =>
        {
            // `a..b`  ⇒ Aggregate(Range,          [start, end]);            count = end - start
            // `a..=b` ⇒ Aggregate(RangeInclusive, [start, end, exhausted]); count = end - start + 1
            //
            // The RangeInclusive field list is MEASURED, not assumed: stock rustc
            // (nightly-2026-04-20) renders `(0..=5)` as
            // `RangeInclusive::<i32> { start: const 0_i32, end: const 5_i32,
            // exhausted: const false }`. The arity is required exactly, so a future
            // std layout change fails closed (no count ⇒ a visible Unknown row)
            // instead of reading some other field as `end`.
            let inclusive = family == "RangeInclusive";
            if inclusive && ops.len() != 3 {
                return None;
            }
            let start = ops.first()?;
            let end = ops.get(1)?;
            let start_f = operand_to_formula(func, start);
            let end_f = operand_to_formula(func, end);
            match (&start_f, &end_f) {
                // CHECKED, both families: the previous `e - s` was a raw i128
                // subtraction, so a `Range` whose endpoints straddle the i128
                // extremes wrapped to a SMALL positive count — a count the ceiling
                // skip then waved through. `None` here is the fail-closed answer
                // (a visible `count-not-derivable` Unknown).
                (Formula::Int(s), Formula::Int(e)) => {
                    let span = e.checked_sub(*s)?;
                    Some(Formula::Int(if inclusive { span.checked_add(1)? } else { span }))
                }
                _ => {
                    let span = Formula::Sub(Box::new(end_f), Box::new(start_f));
                    Some(if inclusive {
                        Formula::Add(Box::new(span), Box::new(Formula::Int(1)))
                    } else {
                        span
                    })
                }
            }
        }
        // `let it = <iter>; it.collect()` — chase the move/copy alias.
        LocalDef::Rvalue(Rvalue::Use(inner)) => iter_collect_count_rec(func, inner, depth + 1),
        // Every arm here is AUTHENTICATED on the callee, for the reason on the
        // `Range` arm above: the count it returns is what the obligation is
        // solved against, so `mycrate::Adapt::map(0..3, f)` returning an endless
        // iterator used to buy the count `3`. The value-side identity is NOT
        // needed in this function and is deliberately not applied: every arm below
        // is sound for ANY receiver once its own callee is genuinely std's
        // (`Iterator::take(it, n)` yields at most `n` whatever `it` is; a
        // length-preserving hop just re-asks the question of argument 0), so
        // requiring it here would decline counts without closing anything.
        LocalDef::Call { callee, args } => {
            let tail = callee_tail(callee);
            if is_authenticated_std_len_preserving_adaptor(callee, tail) {
                // `src.map(f)` etc. — adaptor receiver is arg 0.
                iter_collect_count_rec(func, args.first()?, depth + 1)
            } else if tail == "take"
                && vc_callee_is_std_iter_trait_method(callee, "Iterator", "take")
            {
                // `src.take(n)` — at most `n` elements (receiver arg 0, n arg 1).
                args.get(1).map(|n| operand_to_formula(func, n))
            } else if tail == "repeat_n" && is_authenticated_std_iter_free_fn(callee, "repeat_n") {
                // `core::iter::repeat_n(x, n).collect()` — a free fn yielding EXACTLY
                // `n` elements (element arg 0, count arg 1). The dominant constructor
                // for a runtime-sized homogeneous Vec that is not `vec![x; n]`.
                // (`repeat(x)`/`repeat_with(f)` are unbounded and only become a
                // sink behind a `take(n)`, already handled above.)
                args.get(1).map(|n| operand_to_formula(func, n))
            } else if is_range_inclusive_new_call(callee) && args.len() == 2 {
                // Trust (2026-09-25): `a..=b` spelled `RangeInclusive::new(a, b)`
                // yields `b - a + 1` items (none when `a > b`, where the formula
                // goes non-positive — an over-count, which only adds an
                // obligation). Same arithmetic as the aggregate arm above.
                let start_f = operand_to_formula(func, &args[0]);
                let end_f = operand_to_formula(func, &args[1]);
                match (&start_f, &end_f) {
                    (Formula::Int(s), Formula::Int(e)) => {
                        e.checked_sub(*s)?.checked_add(1).map(Formula::Int)
                    }
                    _ => Some(Formula::Add(
                        Box::new(Formula::Sub(Box::new(end_f), Box::new(start_f))),
                        Box::new(Formula::Int(1)),
                    )),
                }
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Trust (2026-09-27): may the bounded-source grant below delete a collect/extend
/// capacity charge at all, on a target of this pointer width?
///
/// The grant reasons "the source already holds its items, so the destination
/// fits". That is a claim about bytes, and it fails in three ways the grant never
/// checks: the destination element can be LARGER than the source item (`u8` ->
/// `u64`, `&[u8]` -> `Vec<&u8>`, `str::chars` -> `char`), the destination can draw
/// on TWO live allocations (`chain`, and `extend`, which adds the collection's
/// own length), and growth can request TWICE what it needs (amortized doubling,
/// hash-table bucket overhead). On a 32-bit target each of these is a
/// capacity-overflow panic from an ordinary 256 MiB to 2 GiB input, so the grant
/// is withheld there and every such sink is charged.
///
/// On a 64-bit target the same shapes need a source beyond 2^58 bytes, which no
/// machine can address. So the grant is kept there, and that rests on an
/// address-space premise STRONGER than the `MAX_LIVE_ALLOC_BYTES` axiom
/// (`docs/TCB.md`), which covers a total factor of 2 only. The premise is
/// disclosed in `docs/TCB.md` and queued as `docs/DECISION_QUEUE.md` D12.
pub(super) fn bounded_source_grant_applies_at_width(pointer_bits: u32) -> bool {
    pointer_bits == 64
}

/// True iff `iter_op` is an iterator over an ALREADY-materialized std collection,
/// reached only through length-non-increasing adaptors. Such an iterator yields at
/// most `source.len()` elements, so collecting it allocates no more than the
/// source collection (whose own allocation this pass already gated when it was
/// built) — it is therefore bounded and introduces no NEW unbounded-allocation
/// hazard. Conservative: any unrecognized step returns `false` (stays gated).
///
/// AUTHENTICATED STD END TO END. Every recursion of this function is one step of
/// the chain, and it re-establishes BOTH halves of the identity described at
/// [`is_authenticated_std_len_preserving_adaptor`]: the VALUE it is asked about
/// must have an authenticated sysroot iterator type, and the CALLEE that produced
/// that value must be an authenticated sysroot iterator adaptor or collection
/// producer. Applying the value check HERE — at the single recursion entry rather
/// than once at the sink — is what makes the property hold of every intermediate
/// and not only of the collected operand: it is the collect's `Self` type at
/// depth 0, the adaptor's receiver type at every deeper step, and (for a
/// `FromIterator::from_iter` sink, whose `Self` is the CONTAINER and not the
/// iterator) the only place the iterator's identity appears at all.
///
/// Trust (W4 HASHMAP r3, 2026-09-29): the lane itself now asks
/// [`collect_source_live_count`], which answers `Some` exactly where this answered
/// `true`; this predicate form is kept for the predicate-level pins in
/// `bounded_source_value_tests`.
#[cfg(test)]
pub(super) fn collect_source_is_bounded_std_collection(
    func: &VerifiableFunction,
    iter_op: &Operand,
    depth: usize,
) -> bool {
    collect_source_live_count(func, iter_op, depth).is_some()
}

/// Trust (W4 HASHMAP r3, 2026-09-29): [`collect_source_is_bounded_std_collection`]
/// with its answer made a BOUND — how many items the source can yield
/// ([`LiveSourceCount`]): the most a live leaf can hold of its items (the leaf
/// receiver's element size, a lower bound — [`receiver_min_item_bytes`]; one byte
/// for a `str` view), summed over a `chain`, carried unchanged through a
/// length-non-increasing adaptor. `None` exactly where the predicate answered
/// `false`: the walk, its authentication and its F3 zero-sized rule are unchanged.
pub(super) fn collect_source_live_count(
    func: &VerifiableFunction,
    iter_op: &Operand,
    depth: usize,
) -> Option<LiveSourceCount> {
    if depth > 8 {
        return None;
    }
    let local = operand_local(iter_op)?;
    let local_ty = crate::local_ty_ref(func, local)?;
    // The value-side PROVENANCE half. A user ADT anywhere in the chain fails
    // closed here, whatever its producer's path spells — including a std-rooted
    // producer path that RETURNS a user iterator.
    if !ty_is_authenticated_std_iterator(local_ty) {
        return None;
    }
    // The value-side BOUNDEDNESS half, and a DIFFERENT property from the line
    // above: `core::ops::range::RangeFrom` is genuine, correctly unstamped `core`
    // and still yields forever. See the module note.
    //
    // Trust (W4 ITER-HOF (c), 2026-09-25): ONE exception to the unrendered-source
    // half, for a value BUILT by an authenticated std `Iterator::chain` call. The
    // extractor compacts a large field subtree to a by-name `Ty::Datatype`, and a
    // `Chain` of two real iterators is exactly the value that exceeds the budget —
    // measured on unaimed-90 d0/p06: `first.to_uppercase().chain(chars.flat_map(..))`
    // renders `Chain { a: Option<ToUppercase>, b: Datatype{"core::option::Option"} }`,
    // so the whole collect was refused as "source not established". For THIS value
    // the source is established another way, and more strongly: the `chain` arm
    // below walks BOTH arguments, each through this same entry with its OWN full
    // value-side checks on its OWN (separately rendered) type, and SUMS their
    // counts. `Chain::new(self, other.into_iter())` stores exactly those two
    // values — `other` must itself pass `operand_is_authenticated_std_iterator_value`,
    // so it is a std iterator whose `IntoIterator` is the blanket identity (the
    // orphan rule forbids any other impl on a std type) — and `Chain::next` pulls
    // only from them. The deny-list half still runs on the `Chain` value itself.
    //
    // Trust (CL-FOLD-LOCALDEF-1, 2026-10-11): `local_def` asks the VALUE question, which
    // refuses a `&mut` alias. A hand-advanced source (`let mut chars = word.chars();
    // chars.next(); ... chars.flat_map(..).collect()`, the `capitalize` idiom) is that
    // shape, so the walk falls back to the ORIGIN of `local` when every alias of it feeds
    // core's own `Iterator::next` ([`origin_def_through_core_next`]). Sound here because
    // every count this walk returns is an UPPER bound on what the value yields (a
    // collection's memory, a `chain` sum, a length-non-increasing adaptor, a constant
    // fanout), each is a property of the value as BUILT, and `next` on a std iterator
    // only consumes from it, so a bound on the built value bounds what remains. Before
    // this change the counting gate admitted every alias, including a store through one.
    let (def, key) = local_or_core_next_origin_def_and_key(func, local);
    let built_by_std_chain = matches!(
        &def,
        Some(LocalDef::Call { callee, .. })
            if callee_tail(callee) == "chain"
                && vc_callee_is_std_iter_trait_method(callee, "Iterator", "chain")
                && key.is_some_and(|k| k.krate_is_real_sysroot)
    );
    let unbounded = if built_by_std_chain {
        ty_is_denylisted_unbounded_sysroot_iterator(local_ty)
    } else {
        ty_is_unbounded_sysroot_iterator(local_ty)
    };
    if unbounded {
        return None;
    }
    match def {
        // `let it = <iter>; it.collect()` — chase the move/copy alias.
        Some(LocalDef::Rvalue(Rvalue::Use(inner))) => {
            collect_source_live_count(func, inner, depth + 1)
        }
        Some(LocalDef::Call { callee, args }) => {
            let tail = callee_tail(callee);
            // The leaf grant — the one place this walk returns a bare grant of
            // its own (every other `Some` is a recursive answer). Both
            // conjuncts are required: the callee-path predicates authenticate the
            // receiver's crate as RENDERED, and
            // `producer_receiver_value_is_authenticated_sysroot` authenticates the
            // receiver OPERAND, which is where the stamp actually lands.
            //
            // Trust (2026-09-25, F3): a THIRD conjunct for the collection
            // producers. "An existing collection bounds the count" is a claim
            // about MEMORY: the source already holds its elements, so it cannot
            // have more of them than fit. That is false for a ZERO-SIZED element
            // — `vec![(); 1 << 61]` costs no memory at all — and the collect then
            // allocates `2^61` destination elements: `v.iter().collect::<Vec<&()>>()`
            // built exit 0 and panicked "capacity overflow" (8-byte `&()` times
            // 2^61). [`producer_leaf_count_is_memory_bounded`] asks exactly that
            // question of the receiver. A str view needs no extra test: its
            // source is a byte buffer, and `u8` is one byte.
            if is_std_collection_iter_producer(callee, tail)
                && producer_receiver_value_is_authenticated_sysroot(func, args)
                && producer_leaf_count_is_memory_bounded(func, callee, args, iter_op)
            {
                let item_bytes = args
                    .first()
                    .and_then(|recv| operand_place_ty(func, recv))
                    .map_or(1, |recv_ty| receiver_min_item_bytes(recv_ty, 0));
                return Some(LiveSourceCount::memory_backed(item_bytes));
            }
            if is_str_view_iter_producer(callee, tail)
                && producer_receiver_value_is_authenticated_sysroot(func, args)
            {
                return Some(LiveSourceCount::str_view());
            }
            // Trust (W4 ITER-HOF (c), 2026-09-25): two more LEAF grants, keyed on
            // the compiler-minted `CalleeKey` (`DefId`-derived, minted only for an
            // artifact-resident sysroot crate) rather than on the rendered path.
            // See [`key_is_bounded_keyed_producer`] for each item's bound.
            //  * a `char` case mapping yields at most THREE items, with no live
            //    memory behind them: `LiveSourceCount::at_most(3)`;
            //  * a `BTreeMap`/`BTreeSet` sub-range yields at most the receiver's
            //    entries: the same receiver checks, and the same memory-backed
            //    count, as the collection producers above (rebased 2026-09-29 onto
            //    W4 HASHMAP r3's count and F3's memory-bounded receiver).
            if key_is_case_mapping_producer(key) {
                return Some(LiveSourceCount::at_most(CASE_MAPPING_MAX_CHARS));
            }
            if key_is_bounded_keyed_producer(key)
                && producer_receiver_value_is_authenticated_sysroot(func, args)
                && producer_leaf_count_is_memory_bounded(func, callee, args, iter_op)
            {
                let item_bytes = args
                    .first()
                    .and_then(|recv| operand_place_ty(func, recv))
                    .map_or(1, |recv_ty| receiver_min_item_bytes(recv_ty, 0));
                return Some(LiveSourceCount::memory_backed(item_bytes));
            }
            // `a.chain(b)` yields `a.len() + b.len()` — bounded iff BOTH sides are
            // bounded collection sources (the sum of two already-gated allocations
            // is itself bounded). Receiver is arg 0, the chained iterator arg 1.
            if tail == "chain" && vc_callee_is_std_iter_trait_method(callee, "Iterator", "chain") {
                let a = collect_source_live_count(func, args.first()?, depth + 1)?;
                let b = collect_source_live_count(func, args.get(1)?, depth + 1)?;
                return Some(a.chain(b));
            }
            // Walk back through length-NON-INCREASING adaptors (each yields
            // `<= source` elements), receiver is arg 0.
            if is_authenticated_std_len_nonincreasing_adaptor(callee, tail)
                && let Some(recv) = args.first()
            {
                return collect_source_live_count(func, recv, depth + 1);
            }
            // Trust (W4 ITER-HOF (c), 2026-09-25): `src.flat_map(f)` whose inner
            // iterator has a CONSTANT fanout bound. Each item of `src` becomes one
            // `U`, and each `U::IntoIter` here yields at most 3 items, so the
            // adapter yields at most `3 * src`'s bound — a constant multiple of an
            // already-bounded source. The fanout is read from the VALUE's own type
            // (`FlatMap`'s buffered `Option<U::IntoIter>` fields), never from the
            // turbofish: see [`flat_map_value_has_case_mapping_fanout`]. Receiver
            // is arg 0. The count is multiplied (saturating), never shared, so the
            // destination-fit check (`bounded_source_fits_sink`) sees the fanout.
            if tail == "flat_map"
                && vc_callee_is_std_iter_trait_method(callee, "Iterator", "flat_map")
                && key.is_some_and(|k| k.krate_is_real_sysroot)
                && flat_map_value_has_case_mapping_fanout(local_ty)
                && let Some(recv) = args.first()
            {
                let src = collect_source_live_count(func, recv, depth + 1)?;
                return Some(LiveSourceCount::at_most(
                    src.max_items().saturating_mul(CASE_MAPPING_MAX_CHARS),
                ));
            }
            None
        }
        _ => None,
    }
}

/// `ToLowercase`/`ToUppercase` hold at most three `char`s
/// (`CaseMappingIter(array::IntoIter<char, 3>)` in `core/src/char/mod.rs`).
const CASE_MAPPING_MAX_CHARS: u128 = 3;

/// The sysroot items the bounded-source walk grants as a LEAF by their
/// compiler-minted identity (W4 ITER-HOF (c), 2026-09-25). `None`, or a key with
/// no `sysroot_item` (a non-sysroot crate, a `--crate-name alloc` impersonator — the
/// key is minted only under `is_real_sysroot_crate`), grants nothing.
///
///  * `BTreeMap::range`/`range_mut`, `BTreeSet::range` — every item is an entry
///    of the receiver map/set, each at most once, so the adapter yields at most
///    `receiver.len()`: the `iter`/`keys`/`values` argument of
///    [`is_std_collection_iter_producer`] over a sub-range. The receiver OPERAND
///    must also authenticate (`producer_receiver_value_is_authenticated_sysroot`)
///    and be memory-bounded (`producer_leaf_count_is_memory_bounded`), as for every
///    collection producer. Its own panic (`start > end`, charged on main by F5) is
///    not this lane's question and keeps its own row.
///  * `char::to_lowercase`/`to_uppercase` (`ToLowercase`/`ToUppercase`) — a fixed
///    buffer of AT MOST THREE `char`s ([`CASE_MAPPING_MAX_CHARS`]). Bounded by a
///    constant, no receiver collection: the `char` receiver is a primitive, whose
///    inherent methods only `core` defines.
fn key_is_bounded_keyed_producer(key: Option<&trust_types::CalleeKey>) -> bool {
    use trust_types::SysrootItem as S;
    trust_types::CalleeKey::opt_is_one_of(
        key,
        &[
            S::BTreeMapRange,
            S::BTreeMapRangeMut,
            S::BTreeSetRange,
            S::CharToLowercase,
            S::CharToUppercase,
        ],
    )
}

/// The constant-bounded half of [`key_is_bounded_keyed_producer`] — the items with
/// no receiver collection to authenticate.
fn key_is_case_mapping_producer(key: Option<&trust_types::CalleeKey>) -> bool {
    use trust_types::SysrootItem as S;
    trust_types::CalleeKey::opt_is_one_of(key, &[S::CharToLowercase, S::CharToUppercase])
}

/// Does this `FlatMap` VALUE's own type bound its per-item fanout by the case
/// mapping's three?
///
/// `FlatMap<I, U, F>` renders as `FlatMap { inner: FlattenCompat { iter,
/// frontiter: Option<U::IntoIter>, backiter: Option<U::IntoIter> } }` (measured,
/// `-Ztrust-dump=mir` on `s.chars().flat_map(|c| c.to_lowercase())`). The two
/// buffers hold exactly the `U::IntoIter` each source item is turned into, so if
/// that type is `ToLowercase`/`ToUppercase` every source item contributes at most
/// three yields — whatever `U` itself is (a user `impl IntoIterator for X { type
/// IntoIter = ToLowercase; }` still hands over a ≤3-item iterator) and whatever
/// `f` computes. GRANTING, so every step is exact and fail-closed: each ADT must
/// root in an authenticated sysroot crate (`path_root_is_authenticated_sysroot_
/// crate` — unstamped and `core`/`alloc`/`std`-anchored), the field names must be
/// the two buffers, and BOTH buffers must carry the case-mapping type.
pub(super) fn flat_map_value_has_case_mapping_fanout(ty: &Ty) -> bool {
    fn authenticated_adt<'t>(ty: &'t Ty, head: &str) -> Option<&'t [(String, Ty)]> {
        match ty {
            Ty::Adt { name, fields, .. }
                if trust_types::path_root_is_authenticated_sysroot_crate(name)
                    && path_head(name) == head =>
            {
                Some(fields.as_slice())
            }
            _ => None,
        }
    }
    let Some(flat_map) = authenticated_adt(ty, "core::iter::adapters::flatten::FlatMap") else {
        return false;
    };
    let [(_, inner)] = flat_map else { return false };
    let Some(compat) = authenticated_adt(inner, "core::iter::adapters::flatten::FlattenCompat")
    else {
        return false;
    };
    let buffer = |name: &str| compat.iter().find(|(n, _)| n == name).map(|(_, t)| t);
    match (buffer("frontiter"), buffer("backiter")) {
        (Some(front), Some(back)) => {
            option_payload_is_case_mapping(front) && option_payload_is_case_mapping(back)
        }
        _ => false,
    }
}

/// Trust (2026-10-06, D12 option (a)): the most items this source can make a
/// destination reserve for UPFRONT, on the `MAX_LIVE_ALLOC_BYTES` axiom: its item
/// count, or for a str view its `size_hint().0`. `None` for every shape the walk
/// does not admit, including a source held in MANY allocations (`BTreeMap`,
/// `LinkedList`), which the per-allocation axiom bounds nothing about. The grant
/// sites compare this with the destination's bytes per item
/// ([`trust_types::alloc_model::bounded_source_reservation_fits`]): a bounded source
/// alone never bounded what the destination reserves.
///
/// Trust (merge 2026-10-14): upstream's [`collect_source_live_count`] (W4 HASHMAP r3)
/// is the lane's primary walk and decides whether a source is bounded at all; this
/// walk is a second, independent fit check that can only WITHHOLD a skip that walk
/// grants (a `Some` whose reservation does not fit), never add one. It asks the same
/// VALUE question through [`local_def`] and does not take the `Iterator::next`
/// origin fallback.
pub(super) fn bounded_source_max_items(
    func: &VerifiableFunction,
    iter_op: &Operand,
    depth: usize,
) -> Option<u128> {
    if depth > 8 {
        return None;
    }
    let local = operand_local(iter_op)?;
    let local_ty = crate::local_ty_ref(func, local)?;
    // The value-side PROVENANCE half. A user ADT anywhere in the chain fails
    // closed here, whatever its producer's path spells — including a std-rooted
    // producer path that RETURNS a user iterator.
    // The value-side BOUNDEDNESS half, and a DIFFERENT property from the line
    // above: `core::ops::range::RangeFrom` is genuine, correctly unstamped `core`
    // and still yields forever. See the module note.
    if !ty_is_authenticated_std_iterator(local_ty) || ty_is_unbounded_sysroot_iterator(local_ty) {
        return None;
    }
    match local_def(func, local) {
        // `let it = <iter>; it.collect()` — chase the move/copy alias.
        Some(LocalDef::Rvalue(Rvalue::Use(inner))) => {
            bounded_source_max_items(func, inner, depth + 1)
        }
        Some(LocalDef::Call { callee, args }) => {
            let tail = callee_tail(callee);
            // The leaf grant — the one place this walk returns a bare bound of
            // its own (every other `Some` is a recursive answer). Both
            // conjuncts are required: the callee-path predicates authenticate the
            // receiver's crate as RENDERED, and
            // `producer_receiver_value_is_authenticated_sysroot` authenticates the
            // receiver OPERAND, which is where the stamp actually lands.
            //
            // Trust (2026-09-25, F3): a THIRD conjunct for the collection
            // producers. "An existing collection bounds the count" is a claim
            // about MEMORY: the source already holds its elements, so it cannot
            // have more of them than fit. That is false for a ZERO-SIZED element
            // — `vec![(); 1 << 61]` costs no memory at all — and the collect then
            // allocates `2^61` destination elements: `v.iter().collect::<Vec<&()>>()`
            // built exit 0 and panicked "capacity overflow" (8-byte `&()` times
            // 2^61). [`producer_leaf_count_is_memory_bounded`] asks exactly that
            // question of the receiver.
            if is_std_collection_iter_producer(callee, tail)
                && producer_receiver_value_is_authenticated_sysroot(func, args)
                && producer_leaf_count_is_memory_bounded(func, callee, args, iter_op)
            {
                let recv_ty = args.first().and_then(|recv| operand_place_ty(func, recv))?;
                return live_collection_max_items(recv_ty, Some(callee));
            }
            // A str view's upfront reservation is its `size_hint().0`, not its item
            // count (`trust_types::alloc_model::str_view_max_reserved_items`).
            if is_str_view_iter_producer(callee, tail)
                && producer_receiver_value_is_authenticated_sysroot(func, args)
            {
                let kind = match tail {
                    "chars" | "char_indices" => "chars",
                    "encode_utf16" => "utf16",
                    "bytes" => "bytes",
                    _ => "split",
                };
                return Some(trust_types::alloc_model::str_view_max_reserved_items(kind));
            }
            // `a.chain(b)` yields `a.len() + b.len()` — bounded iff BOTH sides are
            // bounded collection sources. Receiver is arg 0, the chained iterator arg 1.
            if tail == "chain" && vc_callee_is_std_iter_trait_method(callee, "Iterator", "chain") {
                let a = bounded_source_max_items(func, args.first()?, depth + 1)?;
                let b = bounded_source_max_items(func, args.get(1)?, depth + 1)?;
                return a.checked_add(b);
            }
            // Walk back through length-NON-INCREASING adaptors (each yields
            // `<= source` elements), receiver is arg 0.
            if is_authenticated_std_len_nonincreasing_adaptor(callee, tail)
                && let Some(recv) = args.first()
            {
                return bounded_source_max_items(func, recv, depth + 1);
            }
            None
        }
        _ => None,
    }
}

/// The most elements an existing collection of type `ty` (behind any references)
/// holds, on the `MAX_LIVE_ALLOC_BYTES` axiom, when ALL of them live in ONE
/// allocation: a sequence holds `MAX_LIVE / size_of::<T>()`; a hash table stores
/// each entry beside a control byte, so `MAX_LIVE / (size_of::<K>() + 1)`; a
/// `String` one item per byte. `None` for a collection spread over many
/// allocations (`BTreeMap`/`BTreeSet`/`LinkedList`) and for anything unrecognized.
///
/// An ADT-rendered collection erases its element, so the element's size is read
/// from a SPELLING — the ADT name's own generics, then the `producer` callee's
/// (as [`spelled_or_iterated_element_nonzero`] does) — and is taken as one byte
/// when neither spells it: callers have already established that it is not
/// zero-sized, and a smaller size only ever raises the bound.
pub(super) fn live_collection_max_items(ty: &Ty, producer: Option<&str>) -> Option<u128> {
    use trust_types::alloc_model::{
        MAX_LIVE_ALLOC_BYTES, item_min_bytes_64, max_items_of_live_sequence,
    };
    let mut ty = ty;
    while let Ty::Ref { inner, .. } | Ty::RawPtr { pointee: inner, .. } = ty {
        ty = inner;
    }
    match ty {
        Ty::Slice { elem }
        | Ty::Seq { elem, .. }
        | Ty::Array { elem, .. }
        | Ty::SymArray { elem, .. } => max_items_of_live_sequence(item_min_bytes_64(elem).max(1)),
        Ty::Str => Some(MAX_LIVE_ALLOC_BYTES),
        Ty::Adt { name, .. } => {
            let producer_self = producer.map(|callee| {
                vc_qualified_self_ty(callee).map(vc_peel_reference_prefixes).unwrap_or(callee)
            });
            let spelled = [Some(name.as_str()), producer_self]
                .into_iter()
                .flatten()
                .find_map(|s| first_generic_arg(s).and_then(parse_spelled_type_byte_size))
                .and_then(|size| u128::try_from(size).ok())
                .unwrap_or(0)
                .max(1);
            let last = path_head(name).rsplit("::").next().unwrap_or_default();
            match last {
                "Vec" | "VecDeque" | "BinaryHeap" => max_items_of_live_sequence(spelled),
                "HashMap" | "HashSet" => max_items_of_live_sequence(spelled.checked_add(1)?),
                "String" => Some(MAX_LIVE_ALLOC_BYTES),
                "Option" => Some(1),
                _ => None,
            }
        }
        _ => None,
    }
}

/// The bytes a `collect`/`from_iter` sink reserves per item, from the extractor's
/// layout token (the destination element's exact size). A `HashMap`/`HashSet`
/// destination is charged
/// [`trust_types::alloc_model::hash_table_reserved_bytes_per_item`]. `None` without
/// a token.
///
/// Trust (merge 2026-10-14): the extractor now stamps a std hash-table sink with the
/// qualified `@table@N` token (W4 HASHMAP r2), which `parse_elem_bytes_token` never
/// reads; it is charged the same per-item and fixed bytes, and `@table@?` answers
/// `None`.
pub(super) fn collect_sink_max_bytes_per_item(callee: &str) -> Option<(u128, u128)> {
    match trust_types::parse_trailing_table_elem_bytes_token(callee) {
        Some(trust_types::TableElemBytes::Known(stride)) => {
            let size = u128::try_from(stride).ok()?;
            return Some((
                trust_types::alloc_model::hash_table_reserved_bytes_per_item(size)?,
                trust_types::alloc_model::HASH_TABLE_FIXED_BYTES,
            ));
        }
        Some(trust_types::TableElemBytes::Unknown) => return None,
        None => {}
    }
    let size = u128::try_from(parse_elem_bytes_token(callee)?).ok()?;
    if callee.contains("HashMap") || callee.contains("HashSet") {
        return Some((
            trust_types::alloc_model::hash_table_reserved_bytes_per_item(size)?,
            trust_types::alloc_model::HASH_TABLE_FIXED_BYTES,
        ));
    }
    Some((size, 0))
}

/// A `BTreeSet`/`BTreeMap` destination sorts what it collected, with a scratch buffer
/// of at least [`trust_types::alloc_model::BTREE_FROM_ITER_MIN_RESERVED_ITEMS`]
/// elements (review round 55).
pub(super) fn collect_sink_min_reserved_items(callee: &str, items: u128) -> u128 {
    if callee.contains("BTreeSet") || callee.contains("BTreeMap") {
        items.max(trust_types::alloc_model::BTREE_FROM_ITER_MIN_RESERVED_ITEMS)
    } else {
        items
    }
}

/// Is this `extend` callee `<String as Extend<char>>` or `<… as Extend<&char>>`? Read
/// from the trait half of the qualified spelling; anything else answers `false`, so a
/// `String` receiver keeps its charge.
pub(super) fn extend_item_is_char(callee: &str) -> bool {
    let Some((_, trait_half)) = callee.split_once(" as ") else {
        return false;
    };
    let Some((_, rest)) = trait_half.split_once("Extend<") else {
        return false;
    };
    let item = rest.split('>').next().unwrap_or_default().trim();
    let item = match item.strip_prefix('&') {
        // `&char`, `&'_ char`, `&'a char`: drop the reference and its lifetime.
        Some(pointee) => match pointee.trim_start().strip_prefix('\'') {
            Some(after_tick) => after_tick.split_once(' ').map_or("", |(_, ty)| ty.trim()),
            None => pointee.trim(),
        },
        None => item,
    };
    item == "char"
}

/// What a `String` `extend` reserves upfront per item. `Extend<char>`/`Extend<&char>`
/// reserve `size_hint().0` bytes: one per item. The string-item impls (`&str`,
/// `String`, `Box<str>`, `Cow<str>`) push each string in turn and reserve nothing
/// upfront, EXCEPT `Extend<&str>` over a by-value `[&str; N]`, whose `SpecExtendStr`
/// specialization reserves the SUM of the lengths (review round 54); an array or an
/// unreadable source type therefore answers `None`. Anything else answers `None`.
/// Review round 55: the char-only rule refused every ordinary `out.extend(words)`.
pub(super) fn string_extend_reserved_bytes_per_item(callee: &str) -> Option<u128> {
    if extend_item_is_char(callee) {
        return Some(1);
    }
    if !extend_item_is_string_like(callee) {
        return None;
    }
    let source = callee.rsplit_once("::extend::<")?.1.trim_start();
    (!source.starts_with('[') && !source.starts_with("&[")).then_some(0)
}

/// Is this `extend` callee's item `&str`, `String`, `Box<str>` or `Cow<str>`?
pub(super) fn extend_item_is_string_like(callee: &str) -> bool {
    let Some((_, trait_half)) = callee.split_once(" as ") else {
        return false;
    };
    let Some((_, rest)) = trait_half.split_once("Extend<") else {
        return false;
    };
    // The item runs to the `>` that closes `Extend<…>`.
    let mut depth = 1i32;
    let mut end = None;
    for (index, ch) in rest.char_indices() {
        match ch {
            '<' => depth += 1,
            '>' => {
                depth -= 1;
                if depth == 0 {
                    end = Some(index);
                    break;
                }
            }
            _ => {}
        }
    }
    let Some(end) = end else {
        return false;
    };
    let item = rest[..end].trim();
    let item = match item.strip_prefix('&') {
        Some(pointee) => match pointee.trim_start().strip_prefix('\'') {
            Some(after_tick) => after_tick.split_once(' ').map_or("", |(_, ty)| ty.trim()),
            None => pointee.trim(),
        },
        None => item,
    };
    item == "str"
        || item == "alloc::string::String"
        || item == "alloc::boxed::Box<str>"
        || item.starts_with("alloc::borrow::Cow<") && item.ends_with(", str>")
}

/// The bytes an `extend` receiver reserves per added item: a `Vec<T>` its element's
/// size (an upper bound, see [`trust_types::alloc_model::item_max_bytes_64`]), a
/// `String` one byte (`Extend<char>` reserves the lower bound in bytes and grows by
/// doubling after it). `None` for anything else, which keeps its charge.
pub(super) fn extend_receiver_max_bytes_per_item(
    func: &VerifiableFunction,
    callee: &str,
    recv: &Operand,
) -> Option<u128> {
    let mut ty = operand_place_ty(func, recv)?;
    while let Ty::Ref { inner, .. } = ty {
        ty = inner;
    }
    match ty {
        Ty::Seq { elem, .. } => trust_types::alloc_model::item_max_bytes_64(elem),
        // Only `Extend<char>`/`Extend<&char>` reserve one byte per item upfront: the
        // `&str` impls (`SpecExtendStr` for `[&str; N]` and slices) reserve the SUM of
        // the strings' lengths, which every item may borrow from one live allocation
        // (review round 54: a verified `out.extend([s; 131072])` panicked).
        Ty::Adt { name, .. } if path_head(name).ends_with("::String") => {
            string_extend_reserved_bytes_per_item(callee)
        }
        // `BinaryHeap<T> { data: Vec<T> }` extends through its `data` exactly as a
        // `Vec<T>` does (review round 56).
        Ty::Adt { name, fields, .. } if path_head(name).ends_with("::BinaryHeap") => {
            fields.iter().find(|(n, _)| n == "data").and_then(|(_, f)| match f {
                Ty::Seq { elem, .. } => trust_types::alloc_model::item_max_bytes_64(elem),
                _ => None,
            })
        }
        _ => None,
    }
}

/// The most a count operand can be when it is the LENGTH of an existing slice or str:
/// `PtrMetadata` of a `&[T]`/`&str` (or a pointer to one), or the result of std's
/// `len` on a collection, through single-assignment copies. A live slice of `T`
/// holds at most `MAX_LIVE_ALLOC_BYTES / size_of::<T>()` items; a zero-sized `T`
/// bounds nothing. `None` for anything else, which keeps the charge.
pub(super) fn existing_length_max_items(
    func: &VerifiableFunction,
    op: &Operand,
    depth: usize,
) -> Option<u128> {
    use trust_types::alloc_model::{
        MAX_LIVE_ALLOC_BYTES, item_min_bytes_64, max_items_of_live_sequence,
    };
    if depth > 4 {
        return None;
    }
    let local = operand_local(op)?;
    match local_def(func, local)? {
        LocalDef::Rvalue(Rvalue::Use(inner)) => existing_length_max_items(func, inner, depth + 1),
        // Only a REFERENCE: a raw slice pointer's length is any `usize`, built in safe
        // code by `ptr::slice_from_raw_parts` with no allocation behind it (review
        // round 58: `vec![0u8; slice_from_raw_parts(null(), n).len()]` was granted).
        LocalDef::Rvalue(Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, inner)) => {
            match operand_place_ty(func, inner)? {
                Ty::Ref { inner: pointee, .. } => match &**pointee {
                    Ty::Str => Some(MAX_LIVE_ALLOC_BYTES),
                    Ty::Slice { elem } => max_items_of_live_sequence(item_min_bytes_64(elem)),
                    _ => None,
                },
                _ => None,
            }
        }
        LocalDef::Call { callee, args }
            if args.len() == 1
                && !callee.starts_with('<')
                && callee_tail(callee) == "len" =>
        {
            let Some(recv_ty @ Ty::Ref { .. }) =
                args.first().and_then(|recv| operand_place_ty(func, recv))
            else {
                return None;
            };
            if !ty_receiver_is_authenticated_sysroot(recv_ty)
                || !producer_receiver_is_authenticated_sysroot(callee)
            {
                return None;
            }
            match live_collection_max_items(recv_ty, Some(callee))? {
                // `live_collection_max_items` takes a one-byte element where none is
                // spelled; a `len` result needs the receiver's element to be non-zero-sized.
                items if receiver_count_is_memory_bounded(recv_ty, callee, None, 0) => Some(items),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Is this counted-allocation sink a SEQUENCE's, whose reservation is the count times
/// the element size? `bulk_alloc_call` matches by method tail, so hashbrown's
/// `with_capacity`/`reserve` reach the same arm, and a hash table reserves per item
/// far more than its element (review round 58: `HashSet::<u8>::with_capacity(s.len())`
/// was granted at one byte per item). Anything not on this list keeps its charge.
pub(super) fn counted_alloc_is_sequence_sink(callee: &str) -> bool {
    if trust_types::path_has_unauthenticated_crate_stamp(callee) || callee.starts_with('<') {
        return false;
    }
    let normalized = vc_strip_generics_cow(callee);
    let Some((head, _)) = normalized.rsplit_once("::") else {
        return false;
    };
    matches!(
        head,
        "alloc::vec::Vec"
            | "std::vec::Vec"
            | "alloc::collections::vec_deque::VecDeque"
            | "std::collections::VecDeque"
            | "alloc::string::String"
            | "std::string::String"
            | "alloc::vec"
            | "std::vec"
    )
}

/// The EXACT element stride of a counted allocation, including one byte, which
/// `alloc_element_byte_size` does not report: the extractor's layout token, or one
/// byte for std's `String` (its buffer is bytes), or the spelled/operand size.
pub(super) fn counted_alloc_exact_stride(
    func: &VerifiableFunction,
    display: &str,
    callee: &str,
    args: &[Operand],
) -> Option<u128> {
    if let Some(token) = parse_elem_bytes_token(callee) {
        return u128::try_from(token).ok();
    }
    if !trust_types::path_has_unauthenticated_crate_stamp(callee)
        && matches!(
            vc_strip_generics_cow(callee).rsplit_once("::").map(|(head, _)| head),
            Some("alloc::string::String" | "std::string::String")
        )
    {
        return Some(1);
    }
    alloc_element_byte_size(func, display, callee, args).and_then(|s| u128::try_from(s).ok())
}

/// `Option<ToLowercase>` / `Option<ToUppercase>`, as the extractor renders an
/// `Option`: its payload is every non-`__tag` flattened field and every variant
/// field. At least one payload, and ALL of them the case-mapping iterator.
fn option_payload_is_case_mapping(ty: &Ty) -> bool {
    let Ty::Adt { name, fields, variants, .. } = ty else { return false };
    if !(trust_types::path_root_is_authenticated_sysroot_crate(name)
        && path_head_is_sysroot_option(name))
    {
        return false;
    }
    let mut payloads = fields
        .iter()
        .filter(|(n, _)| n != "__tag")
        .map(|(_, t)| t)
        .chain(variants.iter().flat_map(|v| v.fields.iter().map(|(_, t)| t)))
        .peekable();
    payloads.peek().is_some() && payloads.all(ty_is_case_mapping_iterator)
}

/// `core::char::ToLowercase` / `core::char::ToUppercase` — authenticated sysroot
/// ADTs holding at most three `char`s.
fn ty_is_case_mapping_iterator(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Adt { name, .. }
            if trust_types::path_root_is_authenticated_sysroot_crate(name)
                && matches!(path_head(name), "core::char::ToLowercase" | "core::char::ToUppercase")
    )
}

/// Trust (W4 HASHMAP r3, 2026-09-29): does the destination of the allocation sink
/// `callee` — read from the extractor's element-size token — have room for every
/// item of a bounded source (`count`), plus, for an `extend` (`receiver_is_live`),
/// whatever the receiver may already hold?
///
///  * a std hash table (`::<__trust_elem_bytes@table@N>`): hashbrown's bucket
///    layout ([`trust_types::live_source_bound::hash_table_capacity_fits`]); an
///    unknown table element (`@table@?`) answers `Some(false)`;
///  * any other std collection (`::<__trust_elem_bytes@N>`): a contiguous buffer
///    ([`trust_types::live_source_bound::contiguous_capacity_fits`]);
///  * no token: `None` — the sink is not a std collection the extractor could
///    size (a user `FromIterator`, or a still-generic element); the caller decides.
///
/// GRANTING (a `Some(true)` deletes the allocation obligation), so it rests only on
/// the extractor's exact layout and on the modeled-fact count bound.
///
/// Trust (ALLOC-WIDTH-1, 2026-10-08): that count bound,
/// `MAX_LIVE_USER_ADDRESS_SPACE_BYTES`, and the `isize::MAX` both fit checks use
/// are 64-bit facts. `live_axiom` is false on any other target (and when no
/// target width was supplied), and a sink this lane can size then answers
/// `Some(false)`: nothing bounds a live source below a 32-bit object limit.
pub(super) fn bounded_source_fits_sink(
    callee: &str,
    count: LiveSourceCount,
    receiver_is_live: bool,
    live_axiom: bool,
) -> Option<bool> {
    use trust_types::live_source_bound::{
        contiguous_capacity_fits, hash_table_capacity_fits, live_receiver_items,
    };
    let (elem_bytes, hash_table) = match trust_types::parse_trailing_table_elem_bytes_token(callee)
    {
        Some(trust_types::TableElemBytes::Known(stride)) => (stride, true),
        Some(trust_types::TableElemBytes::Unknown) => return Some(false),
        None => (parse_elem_bytes_token(callee)?, false),
    };
    if !live_axiom {
        return Some(false);
    }
    let Ok(elem_bytes) = u128::try_from(elem_bytes) else {
        return Some(false);
    };
    let mut items = count.max_items();
    if receiver_is_live {
        items = items.saturating_add(live_receiver_items(elem_bytes, hash_table));
    }
    Some(if hash_table {
        hash_table_capacity_fits(elem_bytes, items)
    } else {
        contiguous_capacity_fits(elem_bytes, items)
    })
}

/// The visible Unknown for a bounded source whose destination may not hold it
/// (see [`bounded_source_fits_sink`]) and whose count is not derivable either.
fn bounded_source_overflow_vc(
    func: &VerifiableFunction,
    display: &str,
    span: &SourceSpan,
) -> VerificationCondition {
    unsupported_mir_vc(
        func,
        format!("UnboundedAllocation::{display}::bounded-source-destination-may-overflow"),
        format!(
            "`{display}` over a bounded std collection, but the destination cannot be shown \
             to hold as many items as a live source may yield (its element size is \
             unknown, or that many elements pass isize::MAX / hashbrown's bucket layout); \
             cannot prove the allocation is bounded"
        ),
        span.clone(),
    )
}

/// Trust (W4 HASHMAP r3, 2026-09-29): a LOWER bound on the live bytes each item of
/// a collection-producer RECEIVER occupies — the element's size for a sequence
/// ([`ty_size_lower_bound`]), one byte for a `str` and for every other collection
/// (a hash table's control byte, a node's header). [`LiveSourceCount::memory_backed`]
/// clamps it to one byte; the receiver has already been shown memory-bounded
/// ([`producer_leaf_count_is_memory_bounded`]).
fn receiver_min_item_bytes(ty: &Ty, depth: usize) -> u128 {
    if depth > 4 {
        return 1;
    }
    match ty {
        Ty::Ref { inner, .. } => receiver_min_item_bytes(inner, depth + 1),
        Ty::RawPtr { pointee, .. } => receiver_min_item_bytes(pointee, depth + 1),
        Ty::Slice { elem }
        | Ty::Seq { elem, .. }
        | Ty::Array { elem, .. }
        | Ty::SymArray { elem, .. } => ty_size_lower_bound(elem, 0),
        _ => 1,
    }
}

/// Trust (W4 HASHMAP r3, 2026-09-29): a LOWER bound on `size_of` of `ty` on the
/// 64-bit lane (0 when nothing is known). Exact for the scalars, a pointer's word,
/// a `Vec`'s three words, an extracted ADT layout; an array is its element times
/// its length; a tuple the SUM of its fields (they never overlap); an ADT without
/// a layout the LARGEST of its rendered fields (sound for a struct and for a
/// union, whose fields overlap); an enum without a layout, 0.
fn ty_size_lower_bound(ty: &Ty, depth: usize) -> u128 {
    if depth > 16 {
        return 0;
    }
    match ty {
        Ty::Bool => 1,
        Ty::Char => 4,
        Ty::Int { width, .. } | Ty::Float { width } | Ty::Bv(width) => u128::from(*width / 8),
        Ty::PtrSizedInt { .. } | Ty::Ref { .. } | Ty::RawPtr { .. } | Ty::FnPtr { .. } => 8,
        Ty::Seq { .. } => 24,
        Ty::Array { elem, len } => {
            ty_size_lower_bound(elem, depth + 1).saturating_mul(u128::from(*len))
        }
        Ty::Tuple(elems) => elems
            .iter()
            .map(|elem| ty_size_lower_bound(elem, depth + 1))
            .fold(0u128, u128::saturating_add),
        Ty::Adt { layout: Some(layout), .. } => u128::from(layout.size),
        Ty::Adt { fields, variants, .. } if variants.is_empty() => {
            fields.iter().map(|(_, field)| ty_size_lower_bound(field, depth + 1)).max().unwrap_or(0)
        }
        _ => 0,
    }
}

/// Trust (2026-09-25, F3): does the RECEIVER of a collection iterator producer
/// hold its elements in memory, so that their COUNT is bounded by what exists?
///
/// GRANTING (a `true` lets [`collect_source_is_bounded_std_collection`] delete the
/// allocation obligation), so every shape this cannot decide answers `false`.
///
///  * a SEQUENCE (`[T]`, `Vec<T>`, `[T; N]`, `BinaryHeap<T>`'s `data`,
///    `VecDeque<T>`) holds one slot per element, so its length is bounded by
///    memory ONLY when `T` is not zero-sized. `Vec<()>` of length `2^61` is a
///    real, cheap value — the measured false accept this closes;
///  * a KEYED collection (`HashMap`/`HashSet`/`BTreeMap`/`BTreeSet`) stores each
///    DISTINCT key once, so even a zero-sized key admits at most one entry, and
///    a `LinkedList` heap-allocates a pointer-carrying node per element. Their
///    counts are bounded whatever the element is.
///
/// `VecDeque` erases `T` in its `RawVec`, so its element is read from the
/// producer's `VecDeque::<T>` turbofish, and failing that from the `slice::Iter`
/// pointer the ITERATOR value carries (`iter_op`'s own type).
pub(super) fn producer_leaf_count_is_memory_bounded(
    func: &VerifiableFunction,
    callee: &str,
    args: &[Operand],
    iter_op: &Operand,
) -> bool {
    let Some(recv_ty) = args.first().and_then(|recv| operand_place_ty(func, recv)) else {
        return false;
    };
    let iter_ty = operand_local(iter_op).and_then(|local| crate::local_ty_ref(func, local));
    receiver_count_is_memory_bounded(recv_ty, callee, iter_ty, 0)
}

fn receiver_count_is_memory_bounded(
    ty: &Ty,
    callee: &str,
    iter_ty: Option<&Ty>,
    depth: usize,
) -> bool {
    if depth > 4 {
        return false;
    }
    match ty {
        Ty::Ref { inner, .. } => {
            receiver_count_is_memory_bounded(inner, callee, iter_ty, depth + 1)
        }
        Ty::RawPtr { pointee, .. } => {
            receiver_count_is_memory_bounded(pointee, callee, iter_ty, depth + 1)
        }
        Ty::Slice { elem }
        | Ty::Seq { elem, .. }
        | Ty::Array { elem, .. }
        | Ty::SymArray { elem, .. } => elem_is_definitely_nonzero_sized(elem),
        // A byte buffer.
        Ty::Str => true,
        // The receiver's ROOT is already authenticated as a sysroot crate
        // (`producer_receiver_value_is_authenticated_sysroot`), so the collection
        // is identified by the type segment its path names, whichever module
        // spelling rendered it (`std::collections::hash::map::HashMap`,
        // `std::collections::hash_map::HashMap`, …).
        Ty::Adt { name, fields, .. } => {
            let head = path_head(name);
            let mut has_keyed_or_string = false;
            let mut has_binary_heap = false;
            let mut has_vec_or_deque = false;
            for seg in head.split("::") {
                match seg {
                    "HashMap" | "HashSet" | "BTreeMap" | "BTreeSet" | "LinkedList" | "String" => {
                        has_keyed_or_string = true;
                        break;
                    }
                    "BinaryHeap" => {
                        has_binary_heap = true;
                    }
                    "Vec" | "VecDeque" => {
                        has_vec_or_deque = true;
                    }
                    _ => {}
                }
            }
            if has_keyed_or_string {
                true
            } else if has_binary_heap && fields.iter().any(|(n, f)| {
                n == "data"
                    && matches!(f, Ty::Seq { elem, .. } if elem_is_definitely_nonzero_sized(elem))
            }) {
                // `BinaryHeap<T> { data: Vec<T> }` — the element survives in `data`.
                true
            } else if has_vec_or_deque || has_binary_heap {
                // A sequence rendered as an ADT erases `T` in its `RawVec`
                // (`VecDeque` always; `Vec` in older renderings), so the element is
                // read from a SPELLING — the ADT name's own generics, then the
                // producer callee's — and failing that from the element pointer the
                // ITERATOR value carries.
                spelled_or_iterated_element_nonzero(name, callee, iter_ty)
            } else {
                false
            }
        }
        _ => false,
    }
}

/// See the sequence arm of [`receiver_count_is_memory_bounded`].
fn spelled_or_iterated_element_nonzero(name: &str, callee: &str, iter_ty: Option<&Ty>) -> bool {
    let callee_self =
        vc_qualified_self_ty(callee).map(vc_peel_reference_prefixes).unwrap_or(callee);
    let spelled = [name, callee_self]
        .into_iter()
        .find_map(|s| first_generic_arg(s).and_then(parse_spelled_type_byte_size));
    match spelled {
        Some(size) => size > 0,
        None => iter_ty
            .and_then(|t| iterator_element_pointee(t, 0))
            .is_some_and(elem_is_definitely_nonzero_sized),
    }
}

/// The first non-lifetime generic argument of the FIRST `<…>` group in `s`
/// (`alloc::vec::Vec<u8>` -> `u8`, `alloc::collections::vec_deque::VecDeque::<u64>::iter`
/// -> `u64`). `None` when there is no group or the brackets do not balance.
pub(super) fn first_generic_arg(s: &str) -> Option<&str> {
    let open = s.find('<')?;
    let bytes = s.as_bytes();
    let mut depth = 0i32;
    for i in open..bytes.len() {
        match bytes[i] {
            b'<' => depth += 1,
            b'>' if i > 0 && bytes[i - 1] == b'-' => {}
            b'>' => {
                depth -= 1;
                if depth == 0 {
                    let inner = s.get(open + 1..i)?.trim();
                    return find_top_level_comma_item(inner, |arg| !arg.trim().starts_with('\''))
                        .map(str::trim);
                }
            }
            _ => {}
        }
    }
    None
}

/// The element type a sysroot iterator VALUE walks, read from its element
/// pointer — the `ptr: NonNull<T>` field that `slice::Iter`, `vec::IntoIter`
/// and every iterator wrapping one of them carries — within a small field depth.
/// `None` when no such field is rendered.
fn iterator_element_pointee(ty: &Ty, depth: usize) -> Option<&Ty> {
    if depth > 3 {
        return None;
    }
    match ty {
        Ty::Ref { inner, .. } => iterator_element_pointee(inner, depth + 1),
        Ty::Adt { name, fields, .. }
            if trust_types::path_root_is_authenticated_sysroot_crate(name) =>
        {
            let direct = fields.iter().find(|(n, _)| n == "ptr").and_then(|(_, t)| match t {
                Ty::Adt { fields: nn, .. } => {
                    match nn.iter().find(|(n, _)| n == "pointer").map(|(_, t)| t)? {
                        Ty::RawPtr { pointee, .. } => Some(pointee.as_ref()),
                        _ => None,
                    }
                }
                _ => None,
            });
            direct
                .or_else(|| fields.iter().find_map(|(_, f)| iterator_element_pointee(f, depth + 1)))
        }
        _ => None,
    }
}

/// Trust (2026-09-25, F3): `ty` is DEFINITELY not zero-sized. GRANTING — used only
/// to license "an existing collection of these bounds the count" — so an
/// undecidable shape (a type parameter, a compacted `Datatype`, a closure, an
/// unrendered layout) answers `false`.
///
/// An enum is non-zero-sized when one of its variants carries a non-zero-sized
/// field (rustc lays every variant with a non-ZST field out in full), or when at
/// least two variants are definitely INHABITED (a tag is then needed). A variant
/// that is uninhabited AND all-ZST is "absent" from rustc's layout — which is why
/// `Option<!>` is zero-sized — so such variants are not counted towards the two.
///
/// Trust (W4 ITER-HOF fix round 2, 2026-10-01): an enum with NO variants
/// (`core::convert::Infallible`, `enum Void {}`) is zero-sized and uninhabited, but
/// the extractor still renders it with its flattened `fields` view — one synthetic
/// `__tag` integer — and an empty `variants` list, which is exactly the shape of a
/// one-field STRUCT. The struct arm below read that `__tag` as a sized field, so
/// `Infallible` counted as non-zero-sized AND inhabited, and `Option<Infallible>` (a
/// ZST: `None` is its only value) became a "bounded" source. MEASURED on main
/// `07091c92c1` and on this item's fix-1 snapshot (adversarial probe p29):
/// `v.iter().map(|_| 1u8).collect::<Vec<u8>>()` over `&[Option<Infallible>]` built
/// rc=0, and a `usize::MAX`-long slice panicked "capacity overflow".
/// [`adt_is_variantless_enum_rendering`] now routes that shape away from the struct
/// arm in both predicates.
pub(super) fn ty_is_definitely_nonzero_sized(ty: &Ty, depth: usize) -> bool {
    if depth > 16 {
        return false;
    }
    if adt_is_variantless_enum_rendering(ty) {
        return false;
    }
    match ty {
        Ty::Bool
        | Ty::Int { .. }
        | Ty::PtrSizedInt { .. }
        | Ty::Char
        | Ty::Float { .. }
        | Ty::Bv(_)
        | Ty::Ref { .. }
        | Ty::RawPtr { .. }
        | Ty::FnPtr { .. }
        | Ty::Seq { .. } => true,
        Ty::Array { elem, len } => *len > 0 && ty_is_definitely_nonzero_sized(elem, depth + 1),
        Ty::Tuple(elems) => elems.iter().any(|e| ty_is_definitely_nonzero_sized(e, depth + 1)),
        Ty::Adt { layout: Some(layout), .. } => layout.size > 0,
        Ty::Adt { fields, variants, .. } if variants.is_empty() => {
            fields.iter().any(|(_, f)| ty_is_definitely_nonzero_sized(f, depth + 1))
        }
        Ty::Adt { variants, .. } => {
            variants
                .iter()
                .any(|v| v.fields.iter().any(|(_, f)| ty_is_definitely_nonzero_sized(f, depth + 1)))
                || variants
                    .iter()
                    .filter(|v| {
                        v.fields.iter().all(|(_, f)| ty_is_definitely_inhabited(f, depth + 1))
                    })
                    .count()
                    >= 2
        }
        _ => false,
    }
}

/// `ty` definitely has at least one value. Conservative: `false` when unsure.
fn ty_is_definitely_inhabited(ty: &Ty, depth: usize) -> bool {
    if depth > 16 {
        return false;
    }
    if adt_is_variantless_enum_rendering(ty) {
        return false;
    }
    match ty {
        Ty::Bool
        | Ty::Int { .. }
        | Ty::PtrSizedInt { .. }
        | Ty::Char
        | Ty::Float { .. }
        | Ty::Bv(_)
        | Ty::Unit
        | Ty::Ref { .. }
        | Ty::RawPtr { .. }
        | Ty::FnPtr { .. }
        | Ty::Seq { .. } => true,
        Ty::Array { elem, len } => *len == 0 || ty_is_definitely_inhabited(elem, depth + 1),
        Ty::Tuple(elems) => elems.iter().all(|e| ty_is_definitely_inhabited(e, depth + 1)),
        Ty::Adt { fields, variants, .. } if variants.is_empty() => {
            fields.iter().all(|(_, f)| ty_is_definitely_inhabited(f, depth + 1))
        }
        Ty::Adt { variants, .. } => variants
            .iter()
            .any(|v| v.fields.iter().all(|(_, f)| ty_is_definitely_inhabited(f, depth + 1))),
        _ => false,
    }
}

/// Trust (W4 ITER-HOF fix round 2, 2026-10-01): `ty` is an ENUM rendering that
/// carries no variant for the predicates above to read — `Infallible`,
/// `enum Void {}`, which are zero-sized and have no value. Read from the
/// extractor's own kind stamp (`AdtKind::Enum` with no variants), or, for a
/// `Ty::Adt` carrying no stamp (hand-built, or serialized before W19 stamped
/// kinds), from the enum rendering's synthetic `__tag` as its FIRST field with no
/// variant list. An unstamped `[__tag]` is exactly a variantless enum; an
/// unstamped `[__tag, __v1_0, ..]` with no variant list is an enum whose variants
/// were not carried, and the struct arm would read it as sized and inhabited from
/// `__tag` alone — `Option<Infallible>` in that view is `[__tag, __v1_0:
/// Infallible]`, a ZST. Both predicates above GRANT, so a shape this answers
/// `true` for can only withhold a grant.
///
/// Fix round 4 (2026-10-02) restored this leading-`__tag` rule. Fix round 3
/// (`73c03c0183`) had narrowed the unstamped arm to the exact `[__tag]`, blaming
/// this rule for three red `iter_hof_collect_count_tests`. That attribution was
/// wrong, MEASURED: trust-vcgen --lib on `73c03c0183` still failed the same three
/// (4337 passed, 3 failed). Their cause was stale `__trust_elem_bytes` tokens in
/// their `collect` callees (that module's doc), and none of their hand-built
/// `Option` fields reaches these predicates — only a receiver's ELEMENT does. The
/// narrowing gave the struct arm's grant back to an unstamped `[__tag, __v1_0:
/// Infallible]` element; `a_variantless_enum_payload_is_not_a_bounded_source` pins
/// that it grants nothing.
fn adt_is_variantless_enum_rendering(ty: &Ty) -> bool {
    let Ty::Adt { variants, fields, adt_kind, .. } = ty else {
        return false;
    };
    variants.is_empty()
        && match adt_kind {
            Some(kind) => *kind == trust_types::AdtKind::Enum,
            None => fields.first().is_some_and(|(name, _)| name == "__tag"),
        }
}

/// Trust (merge 2026-10-14): the GRANTING "at least one byte" question for this
/// lane. Local main moved the rule to
/// [`trust_types::alloc_model::ty_is_definitely_nonzero_sized`] (131e8d2e551);
/// upstream kept [`ty_is_definitely_nonzero_sized`] here and added the
/// variantless-enum rendering rule (W4 ITER-HOF fix round 2). Both GRANT, so a
/// length or count is bounded only when BOTH answer `true`.
pub(super) fn elem_is_definitely_nonzero_sized(ty: &Ty) -> bool {
    ty_is_definitely_nonzero_sized(ty, 0)
        && trust_types::alloc_model::ty_is_definitely_nonzero_sized(ty)
}

/// Trust (2026-09-25, F2): `callee` is `<C as Extend<A>>::extend` on a std
/// collection whose `extend` RESERVES from the source's `size_hint` — `Vec`,
/// `VecDeque`, `String`, `BinaryHeap` (its `data: Vec`), and the hash tables.
/// Each of those computes `reserve(lower_bound)` before inserting anything, so an
/// unbounded or huge `size_hint` panics "capacity overflow" at once:
/// `v.extend(iter::repeat(x).take(usize::MAX))` did, after building exit 0.
///
/// CHARGING, so a spelling this misses is a lost obligation, not a false one —
/// but it is also deliberately NOT a tail match: a LOCAL collection's own
/// `Extend` impl is a body of this crate and is verified where it is written.
/// The trait half is anchored by [`vc_callee_is_std_iter_trait_method`]
/// (`core::iter::traits::collect::Extend`), the self half by the qualified
/// receiver's path head. `BTreeMap`/`BTreeSet`/`LinkedList` are absent on
/// purpose: their `extend` inserts one element at a time and reserves nothing.
///
/// Trust (W4 HASHMAP redo, 2026-09-25): a TUPLE receiver is charged when any of
/// its components (recursively) is one of those collections. core's `impl
/// Extend<(A, B, ..)> for (ExtendA, ExtendB, ..)` runs `default_extend`, which
/// calls `extend_reserve(size_hint().0)` on EVERY component, so `(HashSet<u32>,
/// Vec<u8>).extend(iter::repeat(..).take(usize::MAX))` panics "capacity
/// overflow" exactly like the component's own `extend`. MEASURED on stage-1
/// `7c7e46061` (main): the `(Vec<u32>, Vec<u8>)` form built rc=0 and exited 101
/// (pre-existing), and the `HashSet` form would have followed it once std's hash
/// tables joined the vanilla class.
pub(super) fn is_capacity_reserving_std_extend(callee: &str) -> bool {
    if !vc_callee_is_std_iter_trait_method(callee, "Extend", "extend") {
        return false;
    }
    let Some(self_ty) = vc_qualified_self_ty(callee) else {
        return false;
    };
    ty_is_or_holds_capacity_reserving_collection(vc_peel_reference_prefixes(self_ty), 0)
}

/// The rendered type `name` is a collection whose `extend` reserves from `size_hint`
/// ([`is_capacity_reserving_std_extend`]), or is a tuple one of whose components
/// (recursively, to a small depth) does.
fn ty_is_or_holds_capacity_reserving_collection(name: &str, depth: usize) -> bool {
    if depth > 4 {
        return false;
    }
    if let Some(matched) = rendered_tuple_any_component(name, |component| {
        ty_is_or_holds_capacity_reserving_collection(
            vc_peel_reference_prefixes(component),
            depth + 1,
        )
    }) {
        return matched;
    }
    path_head_is_capacity_reserving_collection(name)
}

/// Test a predicate across the top-level components of a rendered TUPLE type
/// `(A, B<C, D>, (E, F))` without allocating a `Vec<&str>`; returns `None` for
/// anything that is not a parenthesized tuple (the unit `()` has no components).
/// Brackets of every kind are balanced, and the `>` of a `->` arrow is not counted.
fn rendered_tuple_any_component<'a>(s: &'a str, mut pred: impl FnMut(&'a str) -> bool) -> Option<bool> {
    let inner = s.trim().strip_prefix('(')?.strip_suffix(')')?;
    let bytes = inner.as_bytes();
    let mut has_component = false;
    let mut matched = false;
    let mut depth = 0i32;
    let mut start = 0usize;
    for (i, &b) in bytes.iter().enumerate() {
        match b {
            b'<' | b'(' | b'[' => depth += 1,
            b'>' if i > 0 && bytes[i - 1] == b'-' => {}
            b'>' | b')' | b']' => depth -= 1,
            b',' if depth == 0 => {
                let comp = inner[start..i].trim();
                has_component = true;
                if !matched && pred(comp) {
                    matched = true;
                }
                start = i + 1;
            }
            _ => {}
        }
        if depth < 0 {
            return None;
        }
    }
    if depth != 0 {
        return None;
    }
    let last = inner[start..].trim();
    if !last.is_empty() {
        has_component = true;
        if !matched && pred(last) {
            matched = true;
        }
    }
    has_component.then_some(matched)
}

#[cfg(test)]
fn rendered_tuple_components(s: &str) -> Option<Vec<&str>> {
    let mut out = Vec::new();
    rendered_tuple_any_component(s, |comp| {
        out.push(comp);
        false
    })?;
    Some(out)
}

fn path_head_is_capacity_reserving_collection(name: &str) -> bool {
    matches!(
        path_head(name),
        "alloc::vec::Vec"
            | "std::vec::Vec"
            | "alloc::collections::vec_deque::VecDeque"
            | "std::collections::VecDeque"
            | "alloc::string::String"
            | "std::string::String"
            | "alloc::collections::binary_heap::BinaryHeap"
            | "std::collections::BinaryHeap"
            | "std::collections::hash::map::HashMap"
            | "std::collections::HashMap"
            | "std::collections::hash::set::HashSet"
            | "std::collections::HashSet"
    )
}

/// Trust (2026-10-14, ALLOC-RECEIVER-ZST-1): does memory bound the length a LIVE
/// receiver ALREADY holds? Every row that ADDS to a receiver rests on it —
/// `reserve` / `reserve_exact` / `extend_reserve` (receiver argument 0), a std
/// `extend` (argument 0) and `Iterator::collect_into` (its destination, argument 1)
/// — and it is asked HERE, once, for all of them.
///
/// Each such call asks the receiver for `len + additional` slots. Its bounded-source
/// grant ([`bounded_source_fits_sink`] with a live receiver) and its counted row
/// ([`capacity_overflow_term`] with `receiver_live`) both charge the receiver's
/// existing length as [`AllocTarget::live_receiver_items`], a bound that holds only
/// when every element occupies live memory. A `Vec<()>` or `VecDeque<()>` can already
/// hold `usize::MAX` elements (`set_len(usize::MAX)` on a zero-sized `Vec` is sound),
/// and then ONE more panics "capacity overflow". Its element allocates nothing, so
/// the counted row carried no byte term and reduced to the element ceiling, which a
/// guard discharges, and the grant summed the receiver as `2^56 + 1` zero-byte items.
/// MEASURED on the stage 1 of `5184affbb97` (`-Ztrust-dump=mir`; the fixtures of
/// `tests/zst_receiver_growth_realmir.rs`): `if n < 100 { (0..n).map(|_| ())
/// .collect_into(v) }` and `if n < 100 { v.reserve(n) }` on `&mut Vec<()>` were
/// KERNEL-CERTIFIED rows, `v.reserve(5)` and `s.iter().map(|_| ()).collect_into(v)`
/// (`Vec<()>` and `VecDeque<()>`) had no row at all. Only `extend` asked (27264a61eb1,
/// which this generalizes); the compiler's ZST-GROWTH-1 fence refused each call on
/// its own, so these were false proofs of this lane, not of the build.
///
/// GRANTING, so every shape it cannot decide answers `false`, and the caller then
/// keeps a visible Unknown ([`receiver_length_not_bounded_vc`]). Bounded:
///  * a `Vec<T>` (`Ty::Seq`) or `BinaryHeap<T>` (its `data`) whose `T` is definitely at
///    least one byte;
///  * a `VecDeque<T>`, whose buffer erases `T`: only by the extractor's exact element
///    token, non-zero, on a callee the COMPILER keys as a sysroot item. Each sysroot
///    sink with a `VecDeque` receiver stamps the receiver's own element (`reserve*`
///    its first type argument `T`, `extend`/`extend_reserve` their `Self`'s element,
///    `collect_into` its destination's), so the token sizes this receiver;
///  * a `String`, `OsString` or `PathBuf` (bytes), a `HashMap`/`HashSet`/`BTreeMap`/
///    `BTreeSet` (each key is stored once: a zero-sized key admits one entry), a
///    `LinkedList` (one heap node per element).
///
/// A SEQUENCE receiver whose callee carries an element token of ZERO bytes answers
/// `false` whatever its operand's type says: the extractor read the destination's
/// element and found it zero-sized. (The keyed and node-based collections are bounded
/// whatever their element; a hash table's `@table@N` token is not this grammar and is
/// not read.) Everything else — a tuple of collections, a user collection (a
/// `collect_into` destination), an unreadable operand — answers `false`.
fn live_receiver_length_is_bounded(
    func: &VerifiableFunction,
    callee: &str,
    callee_key: Option<&trust_types::CalleeKey>,
    recv: &Operand,
) -> bool {
    let token = parse_elem_bytes_token(callee);
    let Some(mut ty) = operand_place_ty(func, recv) else {
        return false;
    };
    while let Ty::Ref { inner, .. } = ty {
        ty = inner;
    }
    let nonzero = |elem: &Ty| token != Some(0) && elem_is_definitely_nonzero_sized(elem);
    match ty {
        Ty::Seq { elem, .. } => nonzero(elem),
        Ty::Adt { name, fields, .. } => match path_head(name) {
            "alloc::string::String"
            | "std::string::String"
            | "std::ffi::os_str::OsString"
            | "std::ffi::OsString"
            | "std::path::PathBuf"
            | "std::collections::hash::map::HashMap"
            | "std::collections::HashMap"
            | "std::collections::hash::set::HashSet"
            | "std::collections::HashSet"
            | "alloc::collections::btree::map::BTreeMap"
            | "std::collections::BTreeMap"
            | "alloc::collections::btree::set::BTreeSet"
            | "std::collections::BTreeSet"
            | "alloc::collections::linked_list::LinkedList"
            | "std::collections::LinkedList" => true,
            "alloc::collections::binary_heap::BinaryHeap" | "std::collections::BinaryHeap" => {
                fields.iter().any(|(field, t)| {
                    field == "data" && matches!(t, Ty::Seq { elem, .. } if nonzero(elem))
                })
            }
            "alloc::collections::vec_deque::VecDeque" | "std::collections::VecDeque" => {
                token.is_some_and(|bytes| bytes > 0)
                    && callee_key.is_some_and(|key| key.krate_is_real_sysroot)
            }
            _ => false,
        },
        _ => false,
    }
}

/// Trust (2026-10-14, ALLOC-RECEIVER-ZST-1): the visible Unknown every live-receiver
/// sink keeps when [`live_receiver_length_is_bounded`] cannot show the receiver's
/// length bounded — `UnboundedAllocation::{display}::receiver-length-not-bounded`.
fn receiver_length_not_bounded_vc(
    func: &VerifiableFunction,
    display: &str,
    span: &SourceSpan,
) -> VerificationCondition {
    unsupported_mir_vc(
        func,
        format!("UnboundedAllocation::{display}::receiver-length-not-bounded"),
        format!(
            "`{display}` adds to what a collection already holds, and memory does not \
             bound that collection's own length (its element may be zero-sized, or the \
             collection or its element type is not recoverable), so even one added \
             element can overflow its capacity; cannot prove the allocation is bounded"
        ),
        span.clone(),
    )
}

/// Trust (2026-09-25, F2): an `IntoIterator` VALUE handed to `extend` that is
/// itself an existing collection (`v.extend(&w)`, `v.extend(arr)`,
/// `s.extend(other_set)`) whose count memory bounds — the value-side twin of the
/// iterator walk's leaf grant, with the same zero-sized-element rule.
///
/// Trust (W4 HASHMAP r3, 2026-09-29): answered as a bound ([`LiveSourceCount`]) —
/// a sequence's element size, one byte per item of a keyed or node-based
/// collection, one item of an `Option` — where it used to answer `true`.
pub(super) fn operand_bounded_std_collection_value_count(
    func: &VerifiableFunction,
    op: &Operand,
) -> Option<LiveSourceCount> {
    let mut ty = operand_place_ty(func, op)?;
    while let Ty::Ref { inner, .. } = ty {
        ty = inner;
    }
    match ty {
        Ty::Slice { elem } | Ty::Seq { elem, .. } | Ty::Array { elem, .. } => {
            elem_is_definitely_nonzero_sized(elem)
                .then(|| LiveSourceCount::memory_backed(ty_size_lower_bound(elem, 0)))
        }
        Ty::Adt { name, .. } => match path_head(name) {
            "std::collections::hash::map::HashMap"
            | "std::collections::hash::set::HashSet"
            | "alloc::collections::btree::map::BTreeMap"
            | "alloc::collections::btree::set::BTreeSet"
            | "alloc::collections::linked_list::LinkedList" => {
                Some(LiveSourceCount::memory_backed(1))
            }
            "core::option::Option" => Some(LiveSourceCount::at_most(1)),
            _ => None,
        },
        _ => None,
    }
}

/// Trust (2026-09-25): `core::ops::RangeInclusive::<T>::new(start, end)` — how
/// optimized MIR spells `a..=b` when it is not folded into an aggregate.
/// Anchored on the genuine `core` path (generics stripped, no qualified self, no
/// unauthenticated-crate stamp), so a user `RangeInclusive::new` does not match.
pub(super) fn is_range_inclusive_new_call(callee: &str) -> bool {
    !callee.contains(" as ")
        && !trust_types::path_has_unauthenticated_crate_stamp(callee)
        && matches!(
            vc_strip_generics_cow(callee).as_ref(),
            "core::ops::range::RangeInclusive::new" | "std::ops::RangeInclusive::new"
        )
}

/// Trust (2026-09-25, F4): the failure condition `count * factor > max` (or
/// `count * factor < min` when `upper` is false) as a LINEAR formula, so the
/// in-process solver can refute it with a counterexample instead of answering
/// `Unknown` on a nonlinear product (measured: `(a..b).sum::<u64>()` came back
/// Unknown -> runtime-checked -> built exit 0 while the product was symbolic).
///
///  * a constant factor or a constant count keeps the exact product (linear);
///  * two symbolic terms are split at `K = 2^ceil(bits/2)`: when `count <= K`
///    and `factor <= max / K` (`>= min / K`), the product cannot leave the type,
///    so `count > K || factor > max / K` is a SOUND over-approximation of the
///    failure. It can only refuse a program whose count and item are both large,
///    never admit one that overflows.
pub(super) fn fold_product_may_leave_range(
    count: &Formula,
    factor: &Formula,
    width: u32,
    signed: bool,
    upper: bool,
) -> Formula {
    let limit = if upper {
        crate::range::type_max_formula(width, signed)
    } else {
        crate::range::type_min_formula(width, signed)
    };
    let cmp = |product: Formula| {
        if upper {
            Formula::Gt(Box::new(product), Box::new(limit.clone()))
        } else {
            Formula::Lt(Box::new(product), Box::new(limit.clone()))
        }
    };
    if let Some(c) = closed_formula_int_value(factor) {
        return cmp(Formula::Mul(Box::new(Formula::Int(c)), Box::new(count.clone())));
    }
    if let Some(c) = closed_formula_int_value(count) {
        return cmp(Formula::Mul(Box::new(Formula::Int(c)), Box::new(factor.clone())));
    }
    let bits = if signed { width.saturating_sub(1) } else { width }.clamp(2, 128);
    let half = bits.div_ceil(2);
    let k = 1i128 << half.min(126);
    let rest = bits - half;
    let factor_limit = if upper {
        // floor(max / K) = 2^rest - 1 for both signednesses.
        Formula::Int((1i128 << rest.min(126)) - 1)
    } else {
        // min / K = -2^rest exactly.
        Formula::Int(-(1i128 << rest.min(126)))
    };
    Formula::Or(vec![
        Formula::Gt(Box::new(count.clone()), Box::new(Formula::Int(k))),
        if upper {
            Formula::Gt(Box::new(factor.clone()), Box::new(factor_limit))
        } else {
            Formula::Lt(Box::new(factor.clone()), Box::new(factor_limit))
        },
    ])
}

/// The integer a closed `Int`/`UInt`/`+`/`-`/`*` formula denotes, or `None`.
pub(super) fn closed_formula_int_value(f: &Formula) -> Option<i128> {
    match f {
        Formula::Int(n) => Some(*n),
        Formula::UInt(n) => i128::try_from(*n).ok(),
        Formula::Add(a, b) => {
            closed_formula_int_value(a)?.checked_add(closed_formula_int_value(b)?)
        }
        Formula::Sub(a, b) => {
            closed_formula_int_value(a)?.checked_sub(closed_formula_int_value(b)?)
        }
        Formula::Mul(a, b) => {
            closed_formula_int_value(a)?.checked_mul(closed_formula_int_value(b)?)
        }
        _ => None,
    }
}

/// Trust (2026-09-25, F4): what an integer `sum`/`product` fold can be charged
/// against — an UPPER bound on how many items its source yields, and an inclusive
/// range every item lies in. `None` in a slot is "not established".
///
/// DIRECTION. Both slots are consumed as upper bounds, so an OVER-count and a
/// WIDER item range are sound (they can only add a counterexample); an
/// under-count or a narrower range would be a false proof. That is why this walk
/// is not [`iter_collect_count`], whose `take(n)` count must be EXACT and whose
/// arms decline every length-reducing adaptor: here a reducing adaptor (`filter`,
/// `skip`, `take_while`) keeps the source's bounds as bounds.
///
/// `items: None` is "NOT MODELLED", never "anything in the accumulator's range":
/// a `map`/`filter_map`/`map_while`/`scan` result, or a repeated non-integer. The
/// 1c-fold mint in `safety.rs` does not substitute the type's range for it
/// (CL-FOLD-MAP-FORCED-1): with a constant count of 4, `4 * MAX > MAX` folds to
/// true, and the row was REFUTED, as a "guaranteed" violation, for
/// `(0..4usize).map(|_| 1u32).sum::<u32>()`, which returns 4.
#[derive(Default)]
pub(super) struct FoldSourceBound {
    pub(super) count: Option<Formula>,
    pub(super) items: Option<(Formula, Formula)>,
    /// Trust (2026-10-01): item bounds known on at most one side each, from a `map`
    /// closure's return-interval summary. The fold row fills an open side with the
    /// accumulator's own bound: a primitive integer accumulator `S` sums only `S` or
    /// `&S` items (core's `Sum`/`Product` impls; a user `Sum<u32>` impl is for a user
    /// accumulator, which has no integer row), so an integer-returning mapper there
    /// returns `S`.
    pub(super) partial_items: Option<(Option<i128>, Option<i128>)>,
}

/// Trust (2026-10-01): `(lo, hi)` bounding every value the local closure `mapper`
/// returns, from the whole-crate return-interval summary of its body
/// ([`crate::callee_return_interval`]); a side the summary leaves open (no tighter
/// than the return type) is filled at the fold row with the accumulator's own bound,
/// which is the closure's return type there (see `partial_items`). The closure names its
/// body; the summary applies only when that name selects exactly one summarized
/// body ([`crate::summary_body_is_unique_in`]: present in the compiler's body-identity
/// map, which drops shared, trait, interposable and intrinsic bodies). The summary
/// holds for every completed call of the body, which is what `Map::next` makes.
/// Sweep A10: `a.iter().map(|&x| x as u64).sum()` over `&[u32; 4]` was refuted with
/// items defaulted to the whole of `u64`.
fn closure_return_item_bounds(
    func: &VerifiableFunction,
    mapper: &Operand,
) -> Option<(Option<i128>, Option<i128>)> {
    // A capture-free closure, and a local fn ITEM (`map(widen)`), is passed as a
    // zero-sized callable constant naming its body; a capturing closure as a value.
    //
    // Trust (2026-10-01, review round 32): the rendered name alone can name a LOCAL
    // body for a FOREIGN callable (two crates built with one `--crate-name`), so the
    // callable's crate is checked too. A callable constant carries its crate's stable
    // id, which must be the summarized body's; a closure VALUE carries none, so it is
    // admitted only when this body constructs it (its one definition is a closure
    // aggregate of that name), which a foreign closure never is.
    // Trust (2026-10-09): `map(u32::from)` over `u8` items — core's lossless
    // primitive-integer `From`. Its items are the SOURCE type's values.
    if let Operand::Constant(trust_types::ConstValue::CallableItem {
        def_path,
        kind: trust_types::CallableKind::FnDef,
        ..
    }) = mapper
        && let Some(range) = lossless_primitive_int_from_source_range(def_path)
    {
        return Some((Some(range.0), Some(range.1)));
    }
    let (name, crate_id) = match mapper {
        Operand::Constant(trust_types::ConstValue::CallableItem {
            def_path,
            kind: trust_types::CallableKind::Closure | trust_types::CallableKind::FnDef,
            def_path_hash,
        }) => (def_path.as_str(), Some(def_path_hash.stable_crate_id())),
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
            if crate::local_defs::is_parameter(func, p.local) {
                return None;
            }
            match crate::local_defs::unique_value_def(func, p.local)? {
                Rvalue::Aggregate(trust_types::AggregateKind::Closure { name, .. }, _) => {
                    (name.as_str(), None)
                }
                _ => return None,
            }
        }
        _ => return None,
    };
    // The identity gate drops a trait item, an interposable body and a shared path.
    if !crate::summary_body_is_unique_in(name, crate_id) {
        return None;
    }
    crate::callee_return_interval(name)
}

/// The value range of `S` when `def_path` is exactly core's
/// `<D as core::convert::From<S>>::from` with `S` and `D` primitive integers and
/// `D` able to hold every `S` value.
///
/// SOUNDNESS: the orphan rule leaves `From<S> for D` between two primitive
/// integers to core alone, and every such impl core has is the lossless
/// widening, so the function returns its argument's value. The width/sign check
/// is defense in depth, and a crate-stamped path (a user crate built as
/// `--crate-name core`) declines, as do 128-bit types.
/// `map(u32::from)`: the mapper constant names core's TRAIT item
/// `core::convert::From::from`, and the `map` call's own generic argument spells
/// the instance, `fn(u8) -> u32 {<u32 as core::convert::From<u8>>::from}`. The
/// items are the source type's values when that instance is core's lossless
/// primitive-integer `From` ([`lossless_primitive_int_from_source_range`]).
fn lossless_from_mapper_items(
    callee: &str,
    mapper: &Operand,
) -> Option<(Option<i128>, Option<i128>)> {
    let Operand::Constant(trust_types::ConstValue::CallableItem {
        def_path,
        kind: trust_types::CallableKind::FnDef,
        ..
    }) = mapper
    else {
        return None;
    };
    if def_path != "core::convert::From::from"
        || !trust_types::path_root_is_authenticated_sysroot_crate(def_path)
    {
        return None;
    }
    // The instance spelled inside the `map` call's generic arguments, exactly once.
    let start = callee.find("{<")? + 1;
    let end = start + callee[start..].find(">::from}")? + ">::from".len();
    if callee[end + 1..].contains("{<") {
        return None;
    }
    let (lo, hi) = lossless_primitive_int_from_source_range(&callee[start..end])?;
    Some((Some(lo), Some(hi)))
}

pub(crate) fn lossless_primitive_int_from_source_range(def_path: &str) -> Option<(i128, i128)> {
    if trust_types::path_has_unauthenticated_crate_stamp(def_path) {
        return None;
    }
    let inner = def_path.strip_prefix('<')?.strip_suffix(">::from")?;
    let (dst, trait_part) = inner.split_once(" as ")?;
    let src = trait_part.strip_prefix("core::convert::From<")?.strip_suffix('>')?;
    // (signed, bits)
    let parse = |t: &str| -> Option<(bool, u32)> {
        Some(match t {
            "u8" => (false, 8),
            "u16" => (false, 16),
            "u32" => (false, 32),
            "u64" => (false, 64),
            "i8" => (true, 8),
            "i16" => (true, 16),
            "i32" => (true, 32),
            "i64" => (true, 64),
            _ => return None,
        })
    };
    let ((s_signed, s_bits), (d_signed, d_bits)) = (parse(src)?, parse(dst)?);
    let lossless = match (s_signed, d_signed) {
        (false, false) | (true, true) => d_bits >= s_bits,
        (false, true) => d_bits > s_bits,
        (true, false) => false,
    };
    if !lossless {
        return None;
    }
    Some(if s_signed {
        (-(1i128 << (s_bits - 1)), (1i128 << (s_bits - 1)) - 1)
    } else {
        (0, (1i128 << s_bits) - 1)
    })
}

pub(super) fn fold_source_bound(
    func: &VerifiableFunction,
    iter_op: &Operand,
    depth: usize,
) -> FoldSourceBound {
    if depth > 8 {
        return FoldSourceBound::default();
    }
    let Some(local) = operand_local(iter_op) else {
        return FoldSourceBound::default();
    };
    // The VALUE question first; when it declines, the range's ORIGIN, only through
    // core's own `Iterator::next` ([`fold_range_origin`], CL-FOLD-LOCALDEF-1).
    match local_def(func, local).or_else(|| fold_range_origin(func, local)) {
        // `a..b` yields `b - a` items in `[a, b - 1]`; `a..=b` yields at most
        // `b - a + 1` in `[a, b]`. Same anchored identity and arity rule as
        // `iter_collect_count`'s range arm. An exhausted or partially consumed
        // range yields a SUBSET of these, never more (`Range::next` only moves
        // `start` forward), so both are bounds. A range CHANGED after it was built
        // (`r.end = n`, `widen(&mut r)`, `mem::swap`, a closure capture) never
        // reaches this arm: `local_def` refuses it, and so does the origin gate.
        Some(LocalDef::Rvalue(Rvalue::Aggregate(AggregateKind::Adt { name, .. }, ops)))
            if let Some(family @ ("Range" | "RangeInclusive")) = range_family_adt_name(name) =>
        {
            let inclusive = family == "RangeInclusive";
            if inclusive && ops.len() != 3 {
                return FoldSourceBound::default();
            }
            let (Some(start), Some(end)) = (ops.first(), ops.get(1)) else {
                return FoldSourceBound::default();
            };
            let start_f = operand_to_formula(func, start);
            let end_f = operand_to_formula(func, end);
            let hi = if inclusive {
                end_f.clone()
            } else {
                Formula::Sub(Box::new(end_f.clone()), Box::new(Formula::Int(1)))
            };
            let items = Some((start_f.clone(), hi));
            let span = Formula::Sub(Box::new(end_f), Box::new(start_f));
            let count = if inclusive {
                Formula::Add(Box::new(span), Box::new(Formula::Int(1)))
            } else {
                span
            };
            FoldSourceBound { count: Some(count), items, partial_items: None }
        }
        Some(LocalDef::Rvalue(Rvalue::Use(inner))) => fold_source_bound(func, inner, depth + 1),
        // `a..=b` as `RangeInclusive::new(a, b)` — the spelling optimized MIR keeps
        // when the range is not folded into an aggregate.
        Some(LocalDef::Call { callee, args })
            if is_range_inclusive_new_call(callee) && args.len() == 2 =>
        {
            let start_f = operand_to_formula(func, &args[0]);
            let end_f = operand_to_formula(func, &args[1]);
            let count = Formula::Add(
                Box::new(Formula::Sub(Box::new(end_f.clone()), Box::new(start_f.clone()))),
                Box::new(Formula::Int(1)),
            );
            FoldSourceBound {
                count: Some(count),
                items: Some((start_f, end_f)),
                partial_items: None,
            }
        }
        Some(LocalDef::Call { callee, args }) => {
            let tail = callee_tail(callee);
            let is_iter = |m: &str| vc_callee_is_std_iter_trait_method(callee, "Iterator", m);
            let inner =
                || args.first().map(|a| fold_source_bound(func, a, depth + 1)).unwrap_or_default();
            // Every item is one of the source's items (a subset, in order or not).
            if matches!(
                tail,
                "filter"
                    | "take_while"
                    | "skip"
                    | "skip_while"
                    | "step_by"
                    | "rev"
                    | "by_ref"
                    | "copied"
                    | "cloned"
                    | "inspect"
                    | "fuse"
                    | "peekable"
            ) && is_iter(tail)
            {
                return inner();
            }
            // At most one item per source item, but a NEW value: count only. For
            // `map(f)` with `f` a local closure, the items are `f`'s return values,
            // so its return-interval summary bounds them (2026-10-01, sweep A10).
            if tail == "map" && is_iter("map") {
                let partial_items = args.get(1).and_then(|f| {
                    closure_return_item_bounds(func, f)
                        .or_else(|| lossless_from_mapper_items(callee, f))
                });
                return FoldSourceBound { count: inner().count, items: None, partial_items };
            }
            if matches!(tail, "filter_map" | "map_while" | "scan") && is_iter(tail) {
                return FoldSourceBound { count: inner().count, ..FoldSourceBound::default() };
            }
            // `take(n)` yields at most `n` of the source's items.
            if tail == "take" && is_iter("take") {
                let src = inner();
                let n = args.get(1).map(|n| operand_to_formula(func, n));
                return FoldSourceBound {
                    count: n.or(src.count),
                    items: src.items,
                    partial_items: src.partial_items,
                };
            }
            // `repeat_n(x, n)`: exactly `n` copies of `x`; `repeat(x)`: endless `x`.
            // The item is `x` itself only when `x` is an INTEGER value — a
            // `repeat(&x)` item is a reference, whose formula is not its value.
            let int_value = |x: &Operand| {
                crate::operand_ty_cow(func, x)
                    .is_some_and(|t| matches!(t.as_ref(), Ty::Int { .. } | Ty::PtrSizedInt { .. }))
                    .then(|| operand_to_formula(func, x))
            };
            if tail == "repeat_n" && is_authenticated_std_iter_free_fn(callee, "repeat_n") {
                let x = args.first().and_then(int_value);
                let n = args.get(1).map(|n| operand_to_formula(func, n));
                return FoldSourceBound {
                    count: n,
                    items: x.map(|x| (x.clone(), x)),
                    partial_items: None,
                };
            }
            if tail == "repeat" && is_authenticated_std_iter_free_fn(callee, "repeat") {
                let x = args.first().and_then(int_value);
                return FoldSourceBound {
                    count: None,
                    items: x.map(|x| (x.clone(), x)),
                    partial_items: None,
                };
            }
            FoldSourceBound::default()
        }
        _ => FoldSourceBound::default(),
    }
}

/// The RECEIVER path of a producer callee, normalized so its ROOT can be
/// anchored and so the collection-module disjuncts below read the receiver's own
/// path rather than a substring of some generic argument.
///
///  * `<alloc::vec::Vec<u8> as core::iter::…::IntoIterator>::into_iter` -> `alloc::vec::Vec`
///  * `<&std::collections::hash::map::HashMap<K, V> as …>::into_iter` -> `std::collections::hash::map::HashMap`
///  * `core::slice::<impl [u8]>::iter` -> `core::slice::iter`  (unqualified: the callee itself)
///
/// TWO normalizations, and each one is a measured defect on its own:
///
///  * **the qualified split.** The receiver of `.into_iter()` is spelled
///    `<Self as Trait>::into_iter`, which starts with `<`. Anchoring THAT string
///    refuses every `v.into_iter().collect()` in the language — the round-1 form
///    of this fix did exactly that, and `<alloc::vec::Vec<u8> as
///    core::iter::…::IntoIterator>::into_iter` went from a proved collect to an
///    `UnsupportedMir{count-not-derivable}` Unknown.
///  * **generic stripping.** The pre-2026-08-17 disjuncts scanned the WHOLE
///    callee, so a substring in a GENERIC ARGUMENT bought the grant for a
///    receiver that is not a collection at all. Measured on `main`:
///    `<core::iter::adapters::chain::Chain<mycrate::Endless,
///    core::slice::iter::Iter<'_, u8>> as core::iter::…::IntoIterator>::into_iter`
///    is `true` there — a Chain over an endless user iterator, granted "bounded"
///    because one of its type arguments mentions `core::slice::`. Reading the
///    receiver's own path closes that; see the `deliberate narrowings` note in
///    `authenticated_std_iter_chain_tests`.
pub(super) fn producer_receiver_path(callee: &str) -> String {
    producer_receiver_path_cow(callee).into_owned()
}

pub(super) fn producer_receiver_path_cow(s: &str) -> std::borrow::Cow<'_, str> {
    let self_ty = vc_qualified_self_ty(s).unwrap_or(s);
    super::iterator_yield::vc_strip_generics_cow(vc_peel_reference_prefixes(self_ty))
}

/// The producer/str-view anchor: the callee carries no unauthenticated-crate
/// stamp ANYWHERE, and the ROOT of its RECEIVER is an authenticated sysroot
/// crate.
///
/// The whole-string stamp scan and the receiver-root anchor are a conjunction
/// and neither is redundant. The scan alone reads a stamp placed at the front as
/// an ordinary path component (`__trust_crate@…::alloc::vec::Vec::<u8>::iter`
/// contains `alloc::vec::`); the anchor alone would read the AUTHENTICATED root
/// of a receiver whose generic argument came from an impersonator. Splitting the
/// qualifier for the anchor does not weaken the scan, because the scan still
/// runs on the untouched callee — a stamp in the trait half or in a generic
/// argument is still fatal.
pub(super) fn producer_receiver_is_authenticated_sysroot(callee: &str) -> bool {
    !trust_types::path_has_unauthenticated_crate_stamp(callee)
        && trust_types::path_root_is_authenticated_sysroot_crate(&producer_receiver_path_cow(
            callee,
        ))
}

/// The receiver's provenance read from the RECEIVER OPERAND'S OWN `Ty` instead of
/// from the rendered callee string — the second half of the producer anchor, and
/// the half that closes what [`producer_receiver_is_authenticated_sysroot`]
/// structurally cannot.
///
/// WHY A STRING IS NOT ENOUGH, measured. The extractor's `__trust_crate@` stamp is
/// keyed on the DEFINING crate of the thing being rendered. For
/// `<&std::vec::Vec<u8> as core::iter::traits::collect::IntoIterator>::into_iter`
/// the impersonator's crate name is not the callee's defining crate — it is
/// somebody else's qualified SELF TYPE — so no stamp is minted anywhere on that
/// string, and [`producer_receiver_path`] reads `std::vec::Vec` off the forgery
/// and authenticates it. The receiver OPERAND's type is an ADT NAME, which the
/// type-name renderer DOES stamp, so asking the operand asks a source the
/// impersonator does not control.
///
/// The accepted shapes are exactly the receiver shapes MEASURED at the ten
/// bounded-source grant sites in the 2 572-bundle corpus, and nothing else:
///
///  * an ADT whose root is an authenticated sysroot crate (`alloc::vec::Vec`) —
///    a stamped or user-rooted ADT is refused, which is the whole point;
///  * a primitive sequence — `[T]`, `str`, `[T; N]` — reached through any number
///    of `&`/`*` wrappers. Four of the six genuine grants are
///    `core::slice::<impl [T]>::iter` on a `&[T]`, whose element type is
///    sometimes `TyKind::Param` or a tuple, so the ELEMENT is deliberately not
///    inspected. A primitive carries no crate to impersonate, coherence forbids a
///    foreign `IntoIterator` impl on one, and the inherent impls that produce
///    their iterators exist only in std — where an impersonating definer WOULD be
///    stamped, because for an unqualified inherent path the defining crate is the
///    impersonator itself.
///
/// Everything else — no receiver argument, a constant/symbolic receiver, a
/// projection this cannot resolve, a `TyKind::Param` receiver — fails CLOSED.
/// MEASURED cost of that: zero rows across the 2 572 real bundles and the 533
/// `tests/ui/trust` bundles.
pub(super) fn producer_receiver_value_is_authenticated_sysroot(
    func: &VerifiableFunction,
    args: &[Operand],
) -> bool {
    args.first()
        .and_then(|recv| operand_place_ty(func, recv))
        .is_some_and(ty_receiver_is_authenticated_sysroot)
}

/// See [`producer_receiver_value_is_authenticated_sysroot`]. GRANTING, so every
/// unrecognized shape returns `false`.
fn ty_receiver_is_authenticated_sysroot(ty: &Ty) -> bool {
    match ty {
        Ty::Ref { inner, .. } => ty_receiver_is_authenticated_sysroot(inner),
        Ty::RawPtr { pointee, .. } => ty_receiver_is_authenticated_sysroot(pointee),
        Ty::Adt { name, .. } => trust_types::path_root_is_authenticated_sysroot_crate(name),
        // Trust (2026-10-07): the extractor mints `Ty::Seq` only for the `Vec`
        // diagnostic item of a real sysroot crate (`is_std_vec`). Without this arm,
        // `v.into_iter().collect()` over an owned `Vec` and `len()` of a `&Vec` were
        // never granted (the `Vec` -> `Ty::Seq` representation change blinded them).
        Ty::Slice { .. } | Ty::Seq { .. } | Ty::Str | Ty::Array { .. } | Ty::SymArray { .. } => {
            true
        }
        _ => false,
    }
}

/// The `Ty` an operand reads, resolving the place projections a receiver actually
/// wears. `Deref` unwraps a reference/raw pointer and `Field(i)` selects a struct
/// or tuple field, so `s.items.iter()` — which MIR lowers as a call on
/// `Copy((_1.0))` — is answered instead of being declined. Any other projection
/// (`Index`, `Downcast`, `Subslice`, …), a non-place operand, or a field index the
/// rendered type does not carry returns `None`, and every caller treats `None` as
/// a refusal.
pub(super) fn operand_place_ty<'f>(func: &'f VerifiableFunction, op: &Operand) -> Option<&'f Ty> {
    let place = match op {
        Operand::Copy(p) | Operand::Move(p) => p,
        _ => return None,
    };
    let mut ty = crate::local_ty_ref(func, place.local)?;
    for projection in &place.projections {
        ty = match (projection, ty) {
            (Projection::Deref, Ty::Ref { inner, .. }) => inner,
            (Projection::Deref, Ty::RawPtr { pointee, .. }) => pointee,
            (Projection::Field(i), Ty::Adt { fields, .. }) => &fields.get(*i)?.1,
            (Projection::Field(i), Ty::Tuple(elems)) => elems.get(*i)?,
            _ => return None,
        };
    }
    Some(ty)
}

/// An iterator-producer method that yields at most the receiver collection's
/// current length, matched by the RECEIVER's full path to a std collection so a
/// custom `iter()` (which could be unbounded) is never mistaken for one.
/// Generative producers (`Range`, `repeat`, `repeat_with`) are intentionally
/// excluded.
///
/// GRANTING, so the receiver is authenticated first
/// ([`producer_receiver_is_authenticated_sysroot`]). A `true` here can make
/// [`collect_source_is_bounded_std_collection`] `continue` past the whole
/// unbounded-allocation obligation — the collect is not weakened, it DISAPPEARS —
/// on the strength of the claim "this iterator yields at most the receiver's
/// current length". That claim is a theorem about std's collections only.
///
/// MEASURED false proof this closes: the old test was the unanchored
/// `callee.contains("alloc::vec::")`, which is satisfied by
/// `__trust_crate@1973d11b2baa21fa::alloc::vec::Vec::<u8>::iter` — the spelling the
/// extractor emits once it has REFUSED to authenticate a crate built
/// `--crate-name alloc` (fixture
/// `fixtures/trusted-root-spoof-endless-iter-2026-08-16`). The producer's stamp was
/// rendered inert here, so an impersonator's `Vec::iter` returning an endless
/// iterator collected without an obligation. Both conditions in the helper are
/// needed: the anchor rejects a stamp read past at the FRONT, the stamp scan
/// rejects an unauthenticated component under a genuine root. The bare-module
/// disjuncts below (`hash_map::`, `btree_set::`, …) name no crate at all and were
/// forgeable by any user module of that name, stamp or not; the anchored
/// receiver root now covers them too.
///
/// `BTreeMap::range`/`range_mut` and `BTreeSet::range` (W4 ITER-HOF (c)) are NOT
/// added to the tail list below: they are granted by their compiler-minted
/// `CalleeKey` in [`key_is_bounded_keyed_producer`], so a spelling can never buy
/// them.
pub(super) fn is_std_collection_iter_producer(callee: &str, tail: &str) -> bool {
    // Trust (2026-10-03): the slice SUB-SLICE producers. `windows(k)` yields
    // `len - k + 1` items, `chunks(k)` / `rchunks(k)` `ceil(len / k)`, and
    // `chunks_exact(k)` / `rchunks_exact(k)` `floor(len / k)` — each at most `len`
    // for every `k >= 1`, and `k == 0` panics in the constructor before anything is
    // yielded. So they are bounded exactly as `iter()` is, by the receiver's length,
    // and the caller's zero-sized-element test still applies. Inherent on `[T]`
    // only, so they are admitted for the unqualified inherent spelling
    // `core::slice::<impl [T]>::chunks` and nothing else: a qualified
    // `<core::slice::iter::Iter<'_, T> as UserTrait>::chunks` names a core receiver
    // but a user body.
    if matches!(tail, "windows" | "chunks" | "chunks_exact" | "rchunks" | "rchunks_exact") {
        if callee.starts_with('<') || trust_types::path_has_unauthenticated_crate_stamp(callee) {
            return false;
        }
        let recv = producer_receiver_path_cow(callee);
        return trust_types::path_root_is_authenticated_sysroot_crate(&recv)
            && recv.starts_with("core::slice::");
    }
    if !matches!(
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
    ) {
        return false;
    }
    if trust_types::path_has_unauthenticated_crate_stamp(callee) {
        return false;
    }
    let recv = producer_receiver_path_cow(callee);
    if !trust_types::path_root_is_authenticated_sysroot_crate(&recv) {
        return false;
    }
    recv.contains("alloc::vec::")
        || recv.contains("std::vec::")
        || recv.contains("alloc::slice::")
        || recv.contains("core::slice::")
        || recv.contains("std::collections::")
        || recv.contains("alloc::collections::")
        || recv.contains("hash_map::")
        || recv.contains("hash_set::")
        || recv.contains("btree_map::")
        || recv.contains("btree_set::")
        || recv.contains("vec_deque::")
        || recv.contains("binary_heap::")
        || recv.contains("linked_list::")
}

/// A str-view iterator producer (`chars`/`char_indices`/`bytes`/`encode_utf16`) on
/// a `str`/`String` receiver. WHY bounded: each yields a count `<=` the receiver's
/// UTF-8 byte length `L` (`bytes` == L; `chars`/`char_indices` <= L; `encode_utf16`
/// <= L since a UTF-16 unit count never exceeds the UTF-8 byte count). The `&str`/
/// `String` is an already-materialized input, so collecting a non-amplifying view of
/// it is linear-in-input — the SAME bounded-source invariant that already waves
/// through `Vec::iter().map(..).collect()` (a stride blowup), only strictly weaker.
///
/// GRANTING, and receiver-authenticated for the same reason as
/// [`is_std_collection_iter_producer`] — it feeds the same `continue`. Its
/// `contains("::str::")` disjunct was the weakest matcher of the pair: it named no
/// crate at all, so `mycrate::str::Endless::chars` matched. `<impl str>` receivers
/// still authenticate because their genuine spelling is
/// `core::str::<impl str>::chars`, which normalizes to `core::str::chars`
/// (measured in the real dump corpus), and a `<alloc::string::String as …>::chars`
/// qualified spelling normalizes to `alloc::string::String`.
pub(super) fn is_str_view_iter_producer(callee: &str, tail: &str) -> bool {
    if !matches!(
        tail,
        // Element-per-position views: at most `len` items.
        "chars"
            | "char_indices"
            | "bytes"
            | "encode_utf16"
            // The SPLIT family: at most `len + 2` items, which is bounded by the
            // same already-materialized haystack the views above are bounded by,
            // and is why they belong in the same lane.
            //
            // THE BOUND, stated exactly, because it is not `len + 1`. A pattern
            // may match the EMPTY string at every position: `"abc".split("")`
            // yields `["", "a", "b", "c", ""]`, five pieces for a three-byte
            // haystack. Pieces are one more than matches, and matches are one
            // more than the interior positions, so `len + 2` is the ceiling and
            // `len + 1` — the number a first reading writes down — is wrong.
            //
            // WHY A USER PATTERN CANNOT EXCEED IT. `core::str::pattern::Searcher`
            // is an UNSAFE trait whose contract requires the steps to partition
            // the haystack and to report `Done` only once every byte has been
            // visited, so a correct searcher advances monotonically and can
            // report at most `len + 1` match positions. An incorrect one is a
            // violation of an unsafe contract the implementor promised to keep,
            // which is the standing every other unsafe-trait obligation in this
            // tree has.
            //
            // This lane is a qualitative SKIP, not a numeric comparison: the
            // question it answers is whether the collect introduces a NEW
            // unbounded hazard beyond the source whose own allocation was
            // already gated. Two extra elements do not, and the lane already
            // admits a fourfold ELEMENT-SIZE amplification next door, since
            // `s.chars().collect::<Vec<char>>()` is four bytes per one-byte
            // source char.
            | "split"
            | "rsplit"
            | "splitn"
            | "rsplitn"
            | "split_terminator"
            | "rsplit_terminator"
            | "split_inclusive"
            | "split_whitespace"
            | "split_ascii_whitespace"
            | "lines"
    ) {
        return false;
    }
    // No trait-qualified spelling is a producer. Every genuine one is an INHERENT `str`
    // method, `core::str::<impl str>::{chars,bytes,split::<char>,lines,char_indices}` in
    // every dump measured (a `String` receiver auto-derefs to it), so a `<R as T>::m`
    // spelling can only be some trait's `m`. `<alloc::string::String as MySplit>::split`
    // put a USER trait on a std receiver and the receiver anchor alone let it through
    // (trip-count lane review, 2026-09-29, `p19a`). Requiring a std-rooted trait closed
    // that in an ordinary crate and not in one NAMED `std`, whose devirtualized trait
    // path read as the real one (`review6/auth` `e5_std`; `devirtualized_callee_name`
    // now stamps it). Refusing the whole spelling needs no crate identity at all.
    if super::iterator_yield::vc_qualified_trait_method(callee).is_some()
        || trust_types::path_has_unauthenticated_crate_stamp(callee)
    {
        return false;
    }
    let recv = producer_receiver_path_cow(callee);
    if !trust_types::path_root_is_authenticated_sysroot_crate(&recv) {
        return false;
    }
    recv.contains("::str::") || recv.contains("alloc::string::") || recv.contains("std::string::")
}

/// Summary-aware rvalue-safety generation: the array/slice INDEX-BOUNDS lane
/// consults the summary-aware guard map, so a proved callee postcondition like
/// `parse ensures _0 < len` can discharge `arr[parse(input)]`. `None` selects the
/// canonical non-summary behavior.
pub(super) fn generate_v2_rvalue_safety_vcs_impl(
    func: &VerifiableFunction,
    summaries: Option<&crate::modular::SummaryDatabase>,
) -> Vec<VerificationCondition> {
    let bounds_assert_by_target: std::cell::OnceCell<FxHashMap<BlockId, usize>> =
        std::cell::OnceCell::new();
    let sv_lazy: std::cell::OnceCell<std::rc::Rc<StmtVersionCtx>> = std::cell::OnceCell::new();

    // Each row carries its USE POINT, the statement it is emitted at (W-D2a/W-D2b,
    // 2026-09-28; see the copy-tie step below).
    let mut block_vcs: Vec<(BlockId, usize, VerificationCondition)> = Vec::new();
    for block in &func.body.blocks {
        // The SOLE native `BoundsCheck` assert whose success edge enters this
        // block, if any — a CANDIDATE authority the per-row exact binding below
        // must still confirm. Bare target identity used to suppress every index
        // row in the block, which let a `Lt(_i, len_A)` assert suppress
        // `B[_j]`'s rows on A's authority — the same identity weakness the
        // Overflow/OverflowNeg and Div/Rem lanes removed. See
        // `v2_bounds_assert_exactly_covers_place`.
        let mut sole_bounds_assert_cached: Option<Option<&trust_types::BasicBlock>> =
            (block.id.0 == 0).then_some(None);
        for (stmt_index, stmt) in block.stmts.iter().enumerate() {
            let Statement::Assign { place, rvalue, span } = stmt else {
                continue;
            };
            let mut stmt_vcs = Vec::new();
            // A native `BoundsCheck` assert EXACTLY BOUND to every index row of
            // the loaded place (canonical `Lt(index, len)` cond over THIS row's
            // index and THIS collection's length, sole-entry success edge)
            // already discharges the load obligation — skip the rvalue-side
            // projection walk (read / `&arr[i]` / `CopyForDeref`) so we don't
            // double-emit a VC the assert already covers. Anything short of the
            // exact binding keeps the row (over-report is fail-closed; a
            // dominating path guard can still discharge it downstream).
            let load_bounds_guarded =
                rvalue_safety::direct_projection_load_place(rvalue).is_some_and(|load_place| {
                    let sole_bounds_assert = *sole_bounds_assert_cached.get_or_insert_with(|| {
                        bounds_assert_by_target
                            .get_or_init(|| v2_sole_bounds_assert_by_target(func))
                            .get(&block.id)
                            .and_then(|assert_index| func.body.blocks.get(*assert_index))
                    });
                    sole_bounds_assert.is_some_and(|assert_block| {
                        v2_bounds_assert_exactly_covers_place(
                            func,
                            assert_block,
                            block,
                            stmt_index,
                            load_place,
                        )
                    })
                });
            if !load_bounds_guarded {
                // verifier-perf: borrowed resolve — `check_rvalue_safety` only INSPECTS the
                // destination type on `Rvalue::Aggregate(AggregateKind::Array, _)`, so skip
                // resolving `place` on every non-array-aggregate assignment and never clone
                // the (possibly fat recursive-ADT) declared root when resolved.
                let dest_ty = matches!(rvalue, Rvalue::Aggregate(trust_types::AggregateKind::Array, _))
                    .then(|| crate::place_ty_cow(func, place))
                    .flatten();
                rvalue_safety::check_rvalue_safety(
                    func,
                    block,
                    rvalue,
                    dest_ty.as_deref(),
                    span,
                    &mut stmt_vcs,
                );
            }
            // STORE-side index bounds: `arr[i] = v` carries the `Index(i)`
            // projection on the assignment *destination*, which the rvalue
            // walk above never inspects. Bounds-check it with the same builder
            // (and the same exact-binding native-assert suppression) so an
            // out-of-bounds write is no longer reported safe.
            let store_bounds_guarded = rvalue_safety::place_needs_bounds_check(place) && {
                let sole_bounds_assert = *sole_bounds_assert_cached.get_or_insert_with(|| {
                    bounds_assert_by_target
                        .get_or_init(|| v2_sole_bounds_assert_by_target(func))
                        .get(&block.id)
                        .and_then(|assert_index| func.body.blocks.get(*assert_index))
                });
                sole_bounds_assert.is_some_and(|assert_block| {
                    v2_bounds_assert_exactly_covers_place(
                        func,
                        assert_block,
                        block,
                        stmt_index,
                        place,
                    )
                })
            };
            if !store_bounds_guarded {
                rvalue_safety::check_place_index_bounds(func, place, span, &mut stmt_vcs);
            }
            // Trust (2026-09-28, W-D2a/W-D2b): the SAME-BLOCK copy ties this row reads
            // through. `_10 = copy (*_1).0; _0 = (*_10)[_2]` reads `_10`'s length, and
            // `_10`'s one definition, `_10__slice_len == p*.0__slice_len`, sits in
            // this block before the row. The path guards carry the DOMINATING blocks'
            // definitions, and nothing carried this block's own. So a guarded
            // `if i < p.s.len() { p.s[i] }` over a struct's slice field was REFUTED
            // with `_10__slice_len = 0`. That is a false refutation, fatal under every
            // policy, of valid Rust: a struct holding a slice, a captured slice, a
            // `Cursor { buf, pos }`. A plain slice parameter proved, because its read
            // needs no copy.
            // Only the copy ties join (`v2_formula_with_copy_ties_at_point_recorded`):
            // each is a versioned true equality pinned at ITS OWN statement, so a tie
            // whose source is overwritten before the row is name-disjoint and pruned.
            // The row's body is renamed at its own use point, here and at the
            // precondition step below. That is what keeps an establish-pinned tie and
            // the read on the same value.
            let has_copy_tie_candidate = !stmt_vcs.is_empty()
                && super::block_defs::block_has_copy_tie_candidate_until(block, stmt_index);
            for mut vc in stmt_vcs {
                if has_copy_tie_candidate {
                    let (combined, _, ties) =
                        super::block_defs::v2_formula_with_copy_ties_at_point_recorded(
                            func,
                            block,
                            stmt_index,
                            vc.formula.clone(),
                        );
                    if !ties.is_empty() {
                        // `combined` is `And(ties ++ [body renamed at stmt_index])`. Mirror
                        // the rename, then the conjoin, onto the recorded obligation, so
                        // `{body, wrappers}` still replays to `formula`.
                        let sv = sv_lazy.get_or_init(|| super::stmt_versions_for(func));
                        vc.formula = combined;
                        ob_record_rename_at(&mut vc, sv, func, block.id, stmt_index);
                        ob_record_conjoin_owned(&mut vc, ties);
                    }
                }
                block_vcs.push((block.id, stmt_index, vc));
            }
        }
    }
    if block_vcs.is_empty() {
        return Vec::new();
    }
    let guard_paths_map = super::guard_map_for(func);
    // Trust (lane-A CSE): one statement-version oracle for the whole function.
    let sv = sv_lazy.into_inner().unwrap_or_else(|| super::stmt_versions_for(func));
    let semantic_guards = super::semantic_guard_map_for(func, summaries);

    // Trust (2026-09-29, slice-length symbol proliferation — item 36984d56d6):
    // conjoin each row's PATH DEFINITIONS, exactly as the per-statement lane does
    // (`generate::safety`, "Conjoin predecessor definitions before guards"), at the
    // row's own statement point (`v2_live_path_defs_at_point`).
    //
    // WHY. A load/store index row's bound names one length symbol per PLACE —
    // `digits__slice_len` for `(*digits)[i]` — while the guards that dominate it
    // name the reborrow the loop condition read (`_6__slice_len`) and the bounds
    // assert's own boolean (`_10`). The equations between them
    // (`_6__slice_len == digits__slice_len`, `_10 == (_7 < _9)`,
    // `_9 == _8__slice_len`, `_8__slice_len == digits__slice_len`) are block
    // definitions of the DOMINATING blocks, which reach a successor only through the
    // path-definition map. This lane conjoined the path GUARDS (`_10`, `_4 <
    // _6__slice_len`) but never their definitions, so the store half of
    // `digits[i] -= 1` — rustc emits one bounds assert for the read and the write,
    // and the write lands two blocks later — was refuted at `digits__slice_len = 0`
    // beside `_6__slice_len = 1` (trust-ir-contract `formula.rs:1264`; pinned by
    // `tests/false_refutation_shapes_realmir.rs`). The per-statement row of the SAME
    // read carried all four equations and proved.
    //
    // SOUNDNESS: each kept fact is a true equation over block-ENTRY values that
    // survives the prefix kill of `stmts[..point]` (see
    // `v2_live_path_defs_at_point`), and the body is renamed at the SAME point
    // below, so a fact and the read it is about name the same value; a conjoined
    // fact can only delete infeasible models. A budget trip stops the loop, which
    // leaves the rest of the rows with FEWER hypotheses (PROVE -> FAIL only).
    //
    // COST: the path-definition fixpoint is built only for a body that HAS a row
    // (most bodies with no indexing have none), and `path_definition_map_for`
    // shares the scope-keyed result across all passes in the active `FuncAnalysisScope`.
    let path_definition_map = super::path_definition_map_for(func);
    for (block_id, point, vc) in &mut block_vcs {
        let point = *point;
        if trust_types::verify_budget::budget_exhausted() {
            break;
        }
        if v2_is_unsupported_mir_vc(vc) {
            continue;
        }
        if let Some(path_defs) = path_definition_map.get(block_id)
            && !path_defs.is_empty()
        {
            let live =
                v2_live_path_defs_at_point(func, &func.body.blocks[block_id.0], path_defs, point);
            if !live.is_empty() {
                ob_record_conjoin(vc, &live);
                let mut conjuncts = live;
                conjuncts.push(std::mem::replace(&mut vc.formula, Formula::Bool(true)));
                vc.formula = Formula::And(conjuncts);
            }
        }
        // Trust (2026-10-02, slices matched through a tuple): the row's OWN block's
        // length ties before `point`. The path definitions above are the
        // DOMINATING blocks' facts; a `ConstantIndex` an arm reads through a fresh
        // copy of a tuple field (`_17 = copy (_3.0); _10 = &(*_17)[0 of 1]`) has
        // its length named only by this block's copy tie
        // (`_17__slice_len == _3.0__slice_len`). Kept only where the rename at
        // this same `point` below leaves it unchanged; see
        // `v2_live_slice_len_ties_at_point`.
        let ties = v2_live_slice_len_ties_at_point(
            func,
            &func.body.blocks[block_id.0],
            point,
            &vc.formula,
        );
        if !ties.is_empty() {
            ob_record_conjoin(vc, &ties);
            let mut conjuncts = ties;
            conjuncts.push(std::mem::replace(&mut vc.formula, Formula::Bool(true)));
            vc.formula = Formula::And(conjuncts);
        }
    }

    // Trust S2c (exemption): path + semantic guards conjoined AFTER the rename (moved below).

    // Range-iterator yield facts (see `generate_v2_safety_vcs`): discharge an
    // `a[i]` bounds VC reached through a `for i in start..end` desugaring.
    let range_yield_guards = super::range_yield_guards_for(func);
    if !range_yield_guards.is_empty() {
        for (block_id, _, vc) in &mut block_vcs {
            if let Some(facts) = range_yield_guards.get(block_id)
                && !facts.is_empty()
            {
                // Trust (bounds ARM, GAP 1): mirror the `And([facts.., body])` conjoin onto
                // the recorded obligation as a `ConjoinFactsLast` wrapper (no-op when the VC
                // carries no obligation), so `{body, wrappers}` still replays to `formula`.
                ob_record_conjoin(vc, facts);
                let mut conjuncts = Vec::with_capacity(facts.len() + 1);
                conjuncts.extend(facts.iter().cloned());
                conjuncts.push(std::mem::replace(&mut vc.formula, Formula::Bool(true)));
                vc.formula = Formula::And(conjuncts);
            }
        }
    }
    let slice_iter_yield_guards = super::slice_iter_yield_guards_for(func);
    if !slice_iter_yield_guards.is_empty() {
        for (block_id, _, vc) in &mut block_vcs {
            if let Some(facts) = slice_iter_yield_guards.get(block_id)
                && !facts.is_empty()
            {
                ob_record_conjoin(vc, facts);
                let mut conjuncts = Vec::with_capacity(facts.len() + 1);
                conjuncts.extend(facts.iter().cloned());
                conjuncts.push(std::mem::replace(&mut vc.formula, Formula::Bool(true)));
                vc.formula = Formula::And(conjuncts);
            }
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
    if !block_vcs.is_empty() {
        let filtered_preconditions: Vec<Formula> = if func.preconditions.is_empty() {
            Vec::new()
        } else {
            func.preconditions
                .iter()
                .filter(|pre| {
                    !contracts::formula_uses_unmodeled_machine_arithmetic_in_function(func, pre)
                })
                .cloned()
                .collect()
        };
        for (block_id, point, vc) in &mut block_vcs {
            // Trust (bounds ARM, GAP 1): use the recorded variant so we can mirror the
            // whole-formula version rename onto the recorded body/subject/wrappers, THEN
            // record the filtered preconditions as an outer `ConjoinFactsLast` — exactly
            // as `generate_v2_safety_vcs` does for the arithmetic/negation arms.
            //
            // Trust (2026-09-29): renamed at the row's own statement POINT — the point
            // its path definitions were kept at above — not at the block terminal. A
            // terminal rename would move a read that PRECEDES a same-block write onto
            // the post-write token, name-disjoint from the entry facts about the value
            // it actually reads (`conjoin_preconditions_versioned_at_point_recorded`).
            let record_ob = vc.obligation.is_some();
            let old_formula = std::mem::replace(&mut vc.formula, Formula::Bool(true));
            let (new_formula, conjoined) = conjoin_preconditions_versioned_at_point_inner(
                func,
                &sv,
                *block_id,
                *point,
                &filtered_preconditions,
                old_formula,
                record_ob,
                true,
            );
            vc.formula = new_formula;
            if record_ob {
                let rename_point = row_rename_point(func, *block_id, *point);
                ob_record_rename_at(vc, &sv, func, *block_id, rename_point);
                ob_record_conjoin_owned(vc, conjoined);
            }
        }
    }

    // Trust S2c (exemption): path guards + semantic guards conjoined AFTER the rename.
    if !guard_paths_map.is_empty() {
        for (block_id, _, vc) in &mut block_vcs {
            if let Some(block_guard_paths) = guard_paths_map.get(block_id) {
                // Trust (bounds ARM, GAP 1): the dominating path-guard map is the sole
                // non-conjoining wrapper. Use the recorded variant to capture the per-path
                // terms and push a `PathGuardOr` wrapper mirroring the `Or` this builds.
                let formula = std::mem::replace(&mut vc.formula, Formula::Bool(true));
                if vc.obligation.is_some() {
                    let (new_formula, path_terms) = v2_formula_with_path_guards_recorded(
                        func,
                        &sv,
                        *block_id,
                        block_guard_paths,
                        formula,
                    );
                    vc.formula = new_formula;
                    if let Some(ob) = vc.obligation.as_mut() {
                        ob.wrappers.push(ObligationWrapper::PathGuardOr { paths: path_terms });
                    }
                } else {
                    vc.formula = v2_formula_with_path_guards(
                        func,
                        &sv,
                        *block_id,
                        block_guard_paths,
                        formula,
                    );
                }
            }
        }
    }
    if !semantic_guards.is_empty() {
        for (block_id, _, vc) in &mut block_vcs {
            if let Some(sem_guards) = semantic_guards.get(block_id)
                && !sem_guards.is_empty()
            {
                ob_record_conjoin(vc, sem_guards);
                let mut conjuncts = Vec::with_capacity(sem_guards.len() + 1);
                conjuncts.extend(sem_guards.iter().cloned());
                conjuncts.push(std::mem::replace(&mut vc.formula, Formula::Bool(true)));
                vc.formula = Formula::And(conjuncts);
            }
        }
    }

    // Trust (bounds ARM, GAP 1): FINAL token-collapse mirror. The rvalue lane does not
    // normalize its formula here (the outermost `generate_vcs` pass at entry.rs does, for
    // every lane), so mirror the SAME `normalize_ssa_version_tokens` collapse onto the
    // recorded body/subject/wrappers now. `normalize_ssa_version_tokens` is per-local
    // deterministic and distributes over `And`/`Or`, so per-piece normalization here plus
    // the wholesale formula normalization at entry.rs leave `reconstruct(record)` byte-
    // identical to the normalized `formula` (term-`Ite` elimination is mirrored at
    // entry.rs alongside the formula rewrite — see `ob_record_eliminate_ites`).
    for (_, _, vc) in &mut block_vcs {
        ob_record_normalize(vc, func);
    }

    block_vcs.into_iter().map(|(_, _, vc)| vc).collect()
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

/// Whether the `Overflow(op)` assert guarding this block provably cannot fire.
///
/// WHY THIS EXISTS SEPARATELY from the builder. In the assert lane a builder that
/// returns `None` means "could not analyse this", and the lane turns that into
/// `RecognizedSafetyAssertProofGap` — a fail-closed runtime check. So an
/// obligation that must not be minted at all has to be suppressed BEFORE the
/// builder is called, exactly as Div/Rem do with
/// `v2_assert_failure_is_known_false`. (`AssertMessage::BoundsCheck` used to be
/// cited here too; it no longer suppresses anything — its literal in-range case
/// mints a real, certifiable obligation. See the arm in `safety.rs`.)
/// `Overflow` was the arm that had no such
/// gate, which is why its provably-safe case could only be expressed as a
/// constant-false formula that no downstream authority could ever discharge.
///
/// Operand recovery requires the exact tuple local read by the assert condition.
/// A target-block operation is not a binding to a caller-controlled condition.
pub(super) fn v2_overflow_assert_provably_cannot_fire(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    _target: BlockId,
    op: BinOp,
    cond: &Operand,
    expected: bool,
) -> bool {
    // PERF-COMPILER-VCGEN-803: only a signed 128-bit `Mul` can be suppressed
    // (`v2_signed_mul_provably_cannot_overflow` answers `false` for every other op),
    // so skip the cond-binding scan for Add/Sub/Shl/Shr/... asserts outright.
    if expected || !matches!(op, BinOp::Mul) {
        return false;
    }
    if let Some((stmt_index, lhs, rhs)) =
        v2_find_checked_binop_for_assert_cond(func, block, cond, op)
    {
        return v2_signed_mul_provably_cannot_overflow(func, block, op, lhs, rhs, Some(stmt_index));
    }
    // Target+operator alone does not bind the public Assert condition to that
    // operation. Only the exact `.1` flag definition may suppress an assertion.
    false
}

/// Build an ArithmeticOverflow VC for `lhs OP rhs` (op in Add/Sub/Mul) from the
/// operands directly. Checked and direct BinaryOp callers both bind the exact
/// defining statement (`stmt_index = Some`) so later writes cannot rewrite the
/// operation's inputs. Add/Sub use the LIA range encoding (keeping
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
    conjoin_arg_type_ranges_step(func, formula).0
}

pub(super) fn arg_type_range_summary_rc(
    func: &VerifiableFunction,
) -> std::rc::Rc<crate::fn_memo::ArgTypeRangeSummary> {
    crate::fn_memo::arg_type_ranges(func, || compute_arg_type_range_summary(func))
}

pub(super) fn versioned_param_range_for_int_var(
    summary: &crate::fn_memo::ArgTypeRangeSummary,
    name: &str,
) -> Option<crate::range::RustScalarRange> {
    let range = name.split('#').next().and_then(|base| summary.param_ranges.get(base)).copied()?;
    if !summary.hash_local_names.is_empty() && summary.hash_local_names.contains(name) {
        return None;
    }
    Some(range)
}

pub(crate) fn conjoin_arg_type_ranges_step(
    func: &VerifiableFunction,
    formula: Formula,
) -> (Formula, bool) {
    if func.body.arg_count == 0 {
        return (formula, false);
    }
    let summary = arg_type_range_summary_rc(func);
    if summary.param_ranges.is_empty() {
        return (formula, false);
    }
    let versioned = versioned_param_type_ranges_from_summary(&formula, &summary);
    if summary.base_bounds.is_empty() && versioned.is_empty() {
        return (formula, false);
    }
    let mut bounds = Vec::with_capacity(summary.base_bounds.len() + versioned.len() + 1);
    bounds.extend(summary.base_bounds.iter().cloned());
    bounds.extend(versioned);
    bounds.push(formula);
    (Formula::And(bounds), true)
}

fn compute_arg_type_range_summary(func: &VerifiableFunction) -> crate::fn_memo::ArgTypeRangeSummary {
    // Bound EVERY integer parameter unconditionally (not only those currently
    // free): a parameter that the VC references only through a *cross-block*
    // definition (e.g. `hi`, reached via `_3 == hi - lo` from an earlier block)
    // is conjoined onto this formula only later, after this point — so filtering
    // on the current free set would miss exactly the variable that needs the
    // bound. `in_range(p)` for an unreferenced parameter is a harmless true fact;
    // once the cross-block def connects `p`, the bound constrains it. Sound: a
    // parameter always holds a value within its type range.
    let mut base_bounds = Vec::new();
    let mut base_var_names = Vec::new();
    let mut param_ranges: FxHashMap<String, crate::range::RustScalarRange> = FxHashMap::default();
    for decl in &func.body.locals {
        if decl.index < 1 || decl.index > func.body.arg_count {
            continue; // local 0 is the return slot; > arg_count are temporaries
        }
        // Bound the parameter's FORMULA name (`crate::local_var_name`). Its source
        // name is a different term whenever `place_to_var_name` declines it — and a
        // parameter spelled `_3` would have bounded the unnamed local 3 instead.
        let Some(range) = crate::range::rust_scalar_range(&decl.ty) else {
            continue;
        };
        let var_name = crate::local_var_name(func, decl);
        base_bounds.push(crate::range::rust_scalar_range_constraint(
            &Formula::Var(var_name.clone(), trust_types::Sort::Int),
            range,
        ));
        base_var_names.push(var_name.clone());
        param_ranges.insert(var_name, range);
    }
    let mut hash_local_names: FxHashSet<String> = FxHashSet::default();
    if !param_ranges.is_empty() {
        for decl in &func.body.locals {
            if let Some(name) = decl.name.as_deref()
                && name.contains('#')
            {
                hash_local_names.insert(name.to_owned());
            }
        }
    }
    crate::fn_memo::ArgTypeRangeSummary {
        base_bounds,
        base_var_names,
        param_ranges,
        hash_local_names,
    }
}

/// Bound the VERSIONED spellings of a parameter — `n#s1_0`, the entry sentinel
/// `n#e`, the mixed join token `n#e_s1_t` — the way the two sibling helpers already
/// bound versioned locals and fields.
///
/// The loop above bounds only the BARE name, so a parameter read that SSA versioning
/// renamed floats free on `Sort::Int` and the solver fabricates an out-of-type-range
/// value for it. `conjoin_datatype_field_ranges_excluding` carries the comment
/// describing this exact bug for FIELDS ("Looking up by `name` silently dropped every
/// range as soon as SSA versioning was present, allowing out-of-type-range false
/// witnesses"); the parameter arm is the last of the three that never got the repair.
/// MEASURED on a `u32` parameter whose only carrier is a pinned in-place update
/// (`n#s0_5 == n#e / 3`): the row was `Failed` with `n#e = 4294967298`, three above
/// `u32::MAX`, falsely refuting provably-safe code.
///
/// SOUNDNESS: a type range is a property of the local's DECLARED TYPE, not of a
/// program point. Rust guarantees a `u32` local's storage holds an inhabitant of
/// `u32` at EVERY point of the body, so `0 <= X <= u32::MAX` is true of every version
/// token naming a value of that local. That point-independence is the whole argument,
/// and it is what makes this unlike the entry-sentinel TIE: `Eq(n#e, n)` is a
/// point-to-point IDENTITY and needs three refusals, while this asserts nothing about
/// which point the symbol came from. Monotone — a pure `And` of a true fact can only
/// delete impossible counterexamples, never hide a real violation (whose witness is a
/// real execution, whose parameter values respect their type ranges).
fn versioned_param_type_ranges_from_summary(
    formula: &Formula,
    summary: &crate::fn_memo::ArgTypeRangeSummary,
) -> Vec<Formula> {
    if summary.param_ranges.is_empty() {
        return Vec::new();
    }

    let mut seen: FxHashSet<&str> = FxHashSet::default();
    let mut bounds = Vec::new();
    trust_types::visit_formula_nodes(formula, &mut |node| {
        let Formula::Var(name, sort) = node else {
            return;
        };
        // Only VERSIONED spellings; the bare name is already bounded above.
        if !name.contains('#') {
            return;
        }
        // SORT guard: emit only where the symbol occurs at `Sort::Int`, so a
        // bitvector-encoded symbol is not re-declared at a second sort. Stricter
        // than the two siblings, which build `Var(name, Sort::Int)` unconditionally.
        if *sort != trust_types::Sort::Int {
            return;
        }
        // COLLISION guard, the same refusal `pin_in_place_update_reads` and
        // `entry_sentinel_ties` make: `validate_function` does not reserve `#` in
        // local names and `place_to_var_name` permits it, so `n#e` may be a REAL,
        // differently-typed local. Bounding it by `n`'s type would be a FALSE bound,
        // not a weakening. Fail closed.
        if seen.contains(name.as_str()) {
            return;
        }
        let Some(range) = versioned_param_range_for_int_var(summary, name.as_str()) else {
            return;
        };
        seen.insert(name.as_str());
        bounds.push(crate::range::rust_scalar_range_constraint(
            &Formula::Var(name.clone(), trust_types::Sort::Int),
            range,
        ));
    });
    bounds
}

#[cfg(test)]
mod lossless_int_from_tests {
    use super::lossless_primitive_int_from_source_range as r;

    #[test]
    fn a_map_over_the_core_from_trait_item_reads_the_instance_from_the_map_call() {
        use trust_types::{CallableKind, ConstValue, Operand};
        let mapper = |path: &str| {
            Operand::Constant(ConstValue::CallableItem {
                def_path: path.to_string(),
                kind: CallableKind::FnDef,
                def_path_hash: trust_types::CallableDefPathHash::new(1, 1),
            })
        };
        let map = "<core::iter::adapters::copied::Copied<core::slice::iter::Iter<'_, u8>> as \
                   core::iter::traits::iterator::Iterator>::map::<u32, fn(u8) -> u32 \
                   {<u32 as core::convert::From<u8>>::from}>";
        assert_eq!(
            super::lossless_from_mapper_items(map, &mapper("core::convert::From::from")),
            Some((Some(0), Some(255)))
        );
        assert_eq!(super::lossless_from_mapper_items(map, &mapper("mycrate::From::from")), None);
        let lossy =
            map.replace("<u32 as core::convert::From<u8>>", "<u8 as core::convert::From<u32>>");
        assert_eq!(
            super::lossless_from_mapper_items(&lossy, &mapper("core::convert::From::from")),
            None
        );
    }

    #[test]
    fn core_lossless_int_from_is_recognized_and_everything_else_declines() {
        assert_eq!(r("<u32 as core::convert::From<u8>>::from"), Some((0, 255)));
        assert_eq!(r("<i64 as core::convert::From<i8>>::from"), Some((-128, 127)));
        assert_eq!(r("<i32 as core::convert::From<u16>>::from"), Some((0, 65535)));
        // Lossy or impossible pairs, other traits, 128-bit, stamped crates.
        assert_eq!(r("<u8 as core::convert::From<u32>>::from"), None);
        assert_eq!(r("<u32 as core::convert::From<i8>>::from"), None);
        assert_eq!(r("<i16 as core::convert::From<u16>>::from"), None);
        assert_eq!(r("<u128 as core::convert::From<u8>>::from"), None);
        assert_eq!(r("<u32 as mycrate::From<u8>>::from"), None);
        assert_eq!(r("<u32 as core::convert::TryFrom<u8>>::try_from"), None);
        let stamped = format!(
            "<u32 as {}::core::convert::From<u8>>::from",
            trust_types::TRUST_UNAUTHENTICATED_CRATE_PATH_PREFIX
        );
        assert_eq!(r(&stamped), None);
    }
}

/// Trust (W4 HASHMAP redo, 2026-09-25): the tuple-`Extend` and `unzip` sinks.
#[cfg(test)]
mod tuple_extend_unzip_sink_tests {
    use super::*;

    #[test]
    fn a_tuple_receiver_is_charged_when_a_component_reserves() {
        let set_vec = "<(std::collections::hash::set::HashSet<u32>, alloc::vec::Vec<u8>) as \
             core::iter::traits::collect::Extend<(u32, u8)>>::extend::<core::iter::Take<\
             core::iter::Repeat<(u32, u8)>>>";
        assert!(is_capacity_reserving_std_extend(set_vec));
        let nested = "<(alloc::collections::btree::set::BTreeSet<u32>, (u8, \
             std::collections::hash::map::HashMap<u32, u32>)) as \
             core::iter::traits::collect::Extend<(u32, (u8, (u32, u32)))>>::extend::<I>";
        assert!(is_capacity_reserving_std_extend(nested));
        let by_ref = "<&mut (alloc::vec::Vec<u32>, alloc::vec::Vec<u8>) as \
             core::iter::traits::collect::Extend<(u32, u8)>>::extend::<I>";
        assert!(is_capacity_reserving_std_extend(by_ref));
    }

    #[test]
    fn a_tuple_of_non_reserving_components_is_not_charged() {
        let btree = "<(alloc::collections::btree::set::BTreeSet<u32>, \
             alloc::collections::linked_list::LinkedList<u8>) as \
             core::iter::traits::collect::Extend<(u32, u8)>>::extend::<I>";
        assert!(!is_capacity_reserving_std_extend(btree));
        // A user `Extend` trait is not std's.
        let user = "<(alloc::vec::Vec<u32>, alloc::vec::Vec<u8>) as \
             mycrate::Extend<(u32, u8)>>::extend::<I>";
        assert!(!is_capacity_reserving_std_extend(user));
    }

    #[test]
    fn the_tuple_splitter_balances_brackets_and_arrows() {
        assert_eq!(
            rendered_tuple_components("(a::B<C, D>, (E, F), fn(u8) -> u8)"),
            Some(vec!["a::B<C, D>", "(E, F)", "fn(u8) -> u8"])
        );
        assert_eq!(rendered_tuple_components("(u8,)"), Some(vec!["u8"]));
        assert_eq!(rendered_tuple_components("()"), None);
        assert_eq!(rendered_tuple_components("alloc::vec::Vec<u8>"), None);
        assert_eq!(rendered_tuple_components("(a<b, c)"), None);
    }

    #[test]
    fn std_unzip_is_a_sink_and_a_user_unzip_is_not() {
        assert!(is_std_unzip_sink(
            "<core::iter::Take<core::iter::Repeat<(u32, u8)>> as \
             core::iter::traits::iterator::Iterator>::unzip::<u32, u8, \
             std::collections::hash::set::HashSet<u32>, alloc::vec::Vec<u8>>"
        ));
        assert!(!is_std_unzip_sink("mycrate::Pairs::unzip"));
        assert!(!is_std_unzip_sink(
            "<mycrate::Pairs as mycrate::Iterator>::unzip::<u32, u8, A, B>"
        ));
    }
}

/// Trust (W4 HASHMAP r2, 2026-09-28): the hash-table bucket-layout bound
/// ([`hash_table_capacity_overflow_term`]) against a model of hashbrown 0.17.1's
/// own layout arithmetic (`raw.rs` `capacity_to_buckets` and
/// `TableLayout::calculate_layout_for`), and the `collect_into` / hash-table
/// callee recognizers.
#[cfg(test)]
mod hash_table_layout_bound_tests {
    use super::*;

    /// hashbrown 0.17.1 `capacity_to_buckets` (cap > 0) on a `bits`-bit target;
    /// `None` = capacity overflow.
    fn model_buckets_at(cap: u128, size: u128, group_width: u128, bits: u32) -> Option<u128> {
        if cap < 15 {
            let min_cap = match (group_width, size) {
                (16, 0..=1) => 14,
                (16, 2..=3) | (8, 0..=1) => 7,
                _ => 3,
            };
            let cap = cap.max(min_cap);
            return Some(if cap < 4 {
                4
            } else if cap < 8 {
                8
            } else {
                16
            });
        }
        // `cap.checked_mul(8)?` on a `bits`-bit usize.
        let usize_max = (1u128 << bits) - 1;
        let times8 = cap.checked_mul(8).filter(|&v| v <= usize_max)?;
        Some((times8 / 7).next_power_of_two()).filter(|&v| v <= usize_max)
    }

    /// Does hashbrown 0.17.1 panic "Hash table capacity overflow" allocating a table
    /// for `cap` elements of `size` bytes aligned to `align` on a `bits`-bit target?
    fn model_panics_at(cap: u128, size: u128, align: u128, group_width: u128, bits: u32) -> bool {
        let isize_max = (1u128 << (bits - 1)) - 1;
        let usize_max = (1u128 << bits) - 1;
        let Some(buckets) = model_buckets_at(cap, size, group_width, bits) else { return true };
        let ctrl_align = align.max(group_width);
        let Some(ctrl_offset) = size
            .checked_mul(buckets)
            .filter(|&v| v <= usize_max)
            .and_then(|v| v.checked_add(ctrl_align - 1))
            .filter(|&v| v <= usize_max)
            .map(|v| v & !(ctrl_align - 1))
        else {
            return true;
        };
        let Some(len) = ctrl_offset.checked_add(buckets + group_width).filter(|&v| v <= usize_max)
        else {
            return true;
        };
        len > isize_max - (ctrl_align - 1)
    }

    /// The 64-bit model.
    fn model_panics(cap: u128, size: u128, align: u128, group_width: u128) -> bool {
        model_panics_at(cap, size, align, group_width, 64)
    }

    /// The smallest `cap` at which the `bits`-bit model panics (binary search; monotone).
    fn model_threshold_at(size: u128, align: u128, group_width: u128, bits: u32) -> u128 {
        let (mut lo, mut hi) = (1u128, 1u128 << (bits - 2));
        while lo < hi {
            let mid = (lo + hi) / 2;
            if model_panics_at(mid, size, align, group_width, bits) {
                hi = mid
            } else {
                lo = mid + 1
            }
        }
        lo
    }

    /// The smallest `cap` at which the 64-bit model panics.
    fn model_threshold(size: u128, align: u128, group_width: u128) -> u128 {
        model_threshold_at(size, align, group_width, 64)
    }

    #[test]
    fn the_bound_fires_wherever_hashbrown_panics() {
        // SOUNDNESS: for every stride, alignment and group width, the smallest
        // panicking count (and everything above it) makes the disjunct TRUE.
        let strides: [u128; 16] = [
            2,
            3,
            4,
            8,
            12,
            16,
            17,
            24,
            100,
            4096,
            1 << 20,
            (1 << 20) + 1,
            1 << 40,
            1 << 45,
            1 << 50,
            1 << 55,
        ];
        for size in strides {
            for align in [1u128, 2, 4, 8, 16, 32, 64] {
                if align > size || size % align != 0 {
                    continue; // a Rust layout's size is a multiple of its alignment
                }
                for group_width in [4u128, 8, 16] {
                    let first = model_threshold(size, align, group_width);
                    let stride = i128::try_from(size).unwrap();
                    for count in [first, first + 1, first + 7, 2 * first] {
                        assert!(model_panics(count, size, align, group_width));
                        assert!(
                            hash_table_capacity_overflow_fires(
                                stride,
                                i128::try_from(count).unwrap(),
                                ALLOC_CAPACITY_OVERFLOW_BYTES
                            ),
                            "stride {size} align {align} width {group_width}: hashbrown panics \
                             at {count} but the bound does not fire"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn the_bound_fires_wherever_hashbrown_panics_on_a_32_bit_target() {
        // ALLOC-WIDTH-1 (2026-10-08): the same derivation at a 32-bit target's
        // object limit. Before, the term was the 64-bit one on every target, and
        // a 32-bit table of 65536-byte elements panicking from 23 409 items was
        // judged against `7 * (2^63 - 1)`.
        let limit32 = AllocTarget::at_pointer_bits(Some(32)).unwrap().object_limit;
        assert_eq!(limit32, i128::from(i32::MAX));
        for size in [2u128, 3, 4, 8, 16, 24, 100, 4096, 65536, 1 << 20, 1 << 24] {
            for align in [1u128, 2, 4, 8, 16] {
                if align > size || size % align != 0 {
                    continue;
                }
                for group_width in [4u128, 8, 16] {
                    let first = model_threshold_at(size, align, group_width, 32);
                    let stride = i128::try_from(size).unwrap();
                    for count in [first, first + 1, 2 * first] {
                        assert!(model_panics_at(count, size, align, group_width, 32));
                        assert!(
                            hash_table_capacity_overflow_fires(
                                stride,
                                i128::try_from(count).unwrap(),
                                limit32
                            ),
                            "32-bit stride {size} align {align} width {group_width}: \
                             hashbrown panics at {count} but the bound does not fire"
                        );
                    }
                    // And the 64-bit term does NOT fire there: judging a 32-bit
                    // target at the 64-bit line is the false proof this closes.
                    let count = i128::try_from(first).unwrap();
                    if size >= 16 {
                        assert!(
                            !hash_table_capacity_overflow_fires(
                                stride,
                                count,
                                ALLOC_CAPACITY_OVERFLOW_BYTES
                            ),
                            "the 64-bit line must be the wrong one for 32-bit stride {size}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn a_live_table_reserve_fires_wherever_hashbrown_panics() {
        // ALLOC-RECEIVER-1 (2026-10-08): `reserve(additional)` on a LIVE table asks
        // hashbrown for `max(items + additional, full_capacity + 1)` slots, both
        // below `held + additional` with `held` the live-address-space bound on the
        // table's buckets. Wherever the model panics at `held + additional`, the
        // receiver row's term must fire at `additional` alone.
        let target = AllocTarget::at_pointer_bits(Some(64)).unwrap();
        for size in [2u128, 8, 24, 4096, 1 << 20, 1 << 35, 1 << 45] {
            for group_width in [8u128, 16] {
                let stride = i128::try_from(size).unwrap();
                let held = u128::try_from(target.live_receiver_items(stride, true)).unwrap() - 1;
                let (scale, threshold) =
                    capacity_overflow_term(target, stride, true, true).expect("a stride > 1");
                let first_total = model_threshold(size, 1, group_width);
                let first_additional = first_total.saturating_sub(held).max(1);
                for additional in [first_additional, first_additional + 1, 2 * first_additional] {
                    assert!(model_panics(held + additional, size, 1, group_width));
                    let count = i128::try_from(additional).unwrap();
                    assert!(
                        scale.checked_mul(count).is_none_or(|bytes| bytes >= threshold),
                        "stride {size} width {group_width}: a live table holding {held} \
                         panics at reserve({additional}) but the receiver term does not fire"
                    );
                }
            }
        }
    }

    #[test]
    fn the_measured_witness_and_its_boundary() {
        // `HashSet::<[u8; 1 << 50]>::with_capacity(n)`: hashbrown panics from 3585
        // (4096 buckets of 2^50 + 1 bytes); the bound fires from 3577 — within one
        // bucket doubling — and `stride * count >= isize::MAX` would wait for 8192.
        let stride: i128 = 1 << 50;
        assert!(!model_panics(3584, 1 << 50, 1, 16));
        assert!(model_panics(3585, 1 << 50, 1, 16));
        assert!(!hash_table_capacity_overflow_fires(stride, 3576, ALLOC_CAPACITY_OVERFLOW_BYTES));
        assert!(hash_table_capacity_overflow_fires(stride, 3577, ALLOC_CAPACITY_OVERFLOW_BYTES));
        assert!(hash_table_capacity_overflow_fires(stride, 3585, ALLOC_CAPACITY_OVERFLOW_BYTES));
        // r1's false accept: the constant 4097 passed `4097 * 2^50 < isize::MAX`.
        assert!(4097 * stride < ALLOC_CAPACITY_OVERFLOW_BYTES);
        assert!(hash_table_capacity_overflow_fires(stride, 4097, ALLOC_CAPACITY_OVERFLOW_BYTES));
        // An overflowing product fires (fail-closed).
        assert!(hash_table_capacity_overflow_fires(
            stride,
            i128::MAX / 2,
            ALLOC_CAPACITY_OVERFLOW_BYTES
        ));
    }

    #[test]
    fn small_tables_of_small_elements_stay_below_the_bound() {
        // Precision guard: ordinary constant capacities must not fire.
        for stride in [2i128, 8, 16, 24, 64, 4096] {
            for count in [0i128, 1, 16, 1024, 1 << 20] {
                assert!(
                    !hash_table_capacity_overflow_fires(
                        stride,
                        count,
                        ALLOC_CAPACITY_OVERFLOW_BYTES
                    ),
                    "{stride} x {count}"
                );
            }
        }
    }

    #[test]
    fn std_collect_into_is_a_sink_and_a_user_one_is_not() {
        assert!(is_std_collect_into_sink(
            "<core::iter::Take<core::iter::Repeat<u64>> as \
             core::iter::traits::iterator::Iterator>::collect_into::<\
             std::collections::hash::set::HashSet<u64>>"
        ));
        assert!(!is_std_collect_into_sink("mycrate::Sink::collect_into"));
        assert!(!is_std_collect_into_sink(
            "<mycrate::It as mycrate::Iterator>::collect_into::<alloc::vec::Vec<u64>>"
        ));
    }

    #[test]
    fn std_hash_table_inherent_fence_matches_only_std_tables() {
        assert!(callee_is_std_hash_table_inherent(
            "std::collections::hash::map::HashMap::<u8, [u8; 4]>::with_capacity"
        ));
        assert!(callee_is_std_hash_table_inherent(
            "std::collections::hash::set::HashSet::<u64, std::hash::RandomState>::\
             with_capacity_and_hasher"
        ));
        assert!(!callee_is_std_hash_table_inherent("alloc::vec::Vec::<u8>::with_capacity"));
        assert!(!callee_is_std_hash_table_inherent("hashbrown::HashMap::<u8, u8>::with_capacity"));
        assert!(!callee_is_std_hash_table_inherent("mycrate::HashMap::with_capacity"));
    }
}

// Trust (W4 HASHMAP r3, 2026-09-29): the two probe-round-r2 classes, pinned at the
// predicates. (1) a sysroot bulk-allocation fn ITEM handed to a higher-order
// function must count as a call-site charge, so the compiler withholds its vanilla
// admission; (2) the bounded-source skip must fit the DESTINATION, not only count
// the source.
#[cfg(test)]
mod bounded_source_destination_tests {
    use trust_types::{render_trailing_elem_bytes_token, render_trailing_table_elem_bytes_token};

    use super::*;

    #[test]
    fn allocation_fn_items_are_call_site_charges() {
        // Spellings of the fn items the r2 probes handed to `Option::map`,
        // `Result::map`, `Option::map_or_else`, `Iterator::map` and an `impl Fn`
        // (rustc's rendering of an inherent item and of a trait item with its
        // qualified self), plus their `Vec` twins.
        for callee in [
            "std::collections::HashSet::<u64>::with_capacity",
            "std::collections::hash::set::HashSet::<u64>::with_capacity",
            "std::collections::HashMap::<u64, u64>::with_capacity",
            "std::collections::HashMap::<std::string::String, std::vec::Vec<u8>>::with_capacity",
            "std::collections::HashSet::<u64, std::hash::RandomState>::with_capacity_and_hasher",
            "alloc::vec::Vec::<u64>::with_capacity",
            "std::vec::Vec::<u8>::with_capacity",
            "<std::collections::HashSet<u64> as core::iter::FromIterator<u64>>::from_iter::<core::iter::Take<core::iter::Repeat<u64>>>",
            "<std::collections::HashMap<u64, u64> as std::iter::FromIterator<(u64, u64)>>::from_iter::<I>",
            "<alloc::vec::Vec<u64> as core::iter::FromIterator<u64>>::from_iter::<core::ops::Range<u64>>",
            "<core::iter::Take<core::iter::Repeat<u64>> as core::iter::Iterator>::collect::<std::collections::HashSet<u64>>",
            "core::iter::Iterator::collect::<std::collections::HashMap<u64, u64>>",
            "<alloc::vec::Vec<u8> as core::iter::traits::collect::Extend<u8>>::extend::<core::ops::Range<u8>>",
            "<std::collections::HashSet<u64> as std::iter::Extend<u64>>::extend::<I>",
            "<I as core::iter::Iterator>::unzip::<u32, u8, alloc::vec::Vec<u32>, alloc::vec::Vec<u8>>",
            "<I as core::iter::Iterator>::collect_into::<alloc::vec::Vec<u8>>",
            "std::collections::HashMap::<u8, u8>::reserve",
            "alloc::vec::Vec::<u8>::resize",
            "alloc::vec::from_elem::<u8>",
        ] {
            assert!(callee_is_call_site_allocation_sink(callee), "{callee}");
            assert!(super::super::callee_has_call_site_panic_family(callee), "{callee}");
        }
        // Total sysroot items the family must keep admitting.
        for callee in [
            "std::collections::HashSet::<u64>::new",
            "alloc::vec::Vec::<u8>::new",
            "core::char::methods::<impl char>::is_whitespace",
            "core::cmp::Ord::min",
            "<std::collections::HashSet<u64> as core::default::Default>::default",
        ] {
            assert!(!callee_is_call_site_allocation_sink(callee), "{callee}");
        }
    }

    #[test]
    fn a_bounded_count_does_not_fit_an_inflated_destination() {
        let big = (1u64 << 35) + 8; // `(u8, MaybeUninit<[u8; 1 << 35]>)`
        let bytes = LiveSourceCount::memory_backed(1); // a `&[u8]`
        let table = format!(
            "<I as core::iter::Iterator>::collect::<std::collections::HashMap<u8, Big>>{}",
            render_trailing_table_elem_bytes_token(Some(big))
        );
        let vec = format!(
            "<I as core::iter::Iterator>::collect::<alloc::vec::Vec<(u8, Big)>>{}",
            render_trailing_elem_bytes_token(big)
        );
        assert_eq!(bounded_source_fits_sink(&table, bytes, false, true), Some(false));
        assert_eq!(bounded_source_fits_sink(&vec, bytes, false, true), Some(false));
        assert_eq!(bounded_source_fits_sink(&table, bytes, true, true), Some(false));
        assert_eq!(bounded_source_fits_sink(&vec, bytes, true, true), Some(false));
    }

    #[test]
    fn ordinary_destinations_of_bounded_sources_still_fit() {
        let words = LiveSourceCount::str_view();
        let map_str_u32 = format!(
            "<I as core::iter::Iterator>::collect::<std::collections::HashMap<&str, u32>>{}",
            render_trailing_table_elem_bytes_token(Some(24))
        );
        assert_eq!(bounded_source_fits_sink(&map_str_u32, words, false, true), Some(true));
        let set_of_u64 = format!(
            "<std::collections::HashSet<u64> as core::iter::Extend<u64>>::extend::<I>{}",
            render_trailing_table_elem_bytes_token(Some(8))
        );
        assert_eq!(
            bounded_source_fits_sink(&set_of_u64, LiveSourceCount::memory_backed(8), true, true),
            Some(true)
        );
        let vec_of_strings = format!(
            "<I as core::iter::Iterator>::collect::<alloc::vec::Vec<alloc::string::String>>{}",
            render_trailing_elem_bytes_token(24)
        );
        assert_eq!(bounded_source_fits_sink(&vec_of_strings, words, false, true), Some(true));
    }

    #[test]
    fn without_the_64_bit_live_axiom_no_sized_destination_fits() {
        // ALLOC-WIDTH-1 (2026-10-08): the live-source count bound (2^56 bytes of
        // live memory) and the `isize::MAX` the fit checks use are 64-bit facts. On
        // a 32-bit target, or with no target width supplied, a destination this
        // lane can size never fits a bounded source: the skip is not taken.
        let words = LiveSourceCount::str_view();
        let map_str_u32 = format!(
            "<I as core::iter::Iterator>::collect::<std::collections::HashMap<&str, u32>>{}",
            render_trailing_table_elem_bytes_token(Some(24))
        );
        let vec_of_strings = format!(
            "<I as core::iter::Iterator>::collect::<alloc::vec::Vec<alloc::string::String>>{}",
            render_trailing_elem_bytes_token(24)
        );
        for receiver_is_live in [false, true] {
            assert_eq!(
                bounded_source_fits_sink(&map_str_u32, words, receiver_is_live, false),
                Some(false)
            );
            assert_eq!(
                bounded_source_fits_sink(&vec_of_strings, words, receiver_is_live, false),
                Some(false)
            );
            // A sink the lane cannot size stays the caller's decision on every target.
            assert_eq!(
                bounded_source_fits_sink(
                    "<I as core::iter::Iterator>::collect::<mycrate::Bag>",
                    words,
                    receiver_is_live,
                    false
                ),
                None
            );
        }
    }

    #[test]
    fn an_unsized_destination_is_the_callers_decision() {
        let count = LiveSourceCount::memory_backed(1);
        // An unknown hash-table element never fits.
        let unknown_table = format!(
            "<I as core::iter::Iterator>::collect::<std::collections::HashSet<T>>{}",
            render_trailing_table_elem_bytes_token(None)
        );
        assert_eq!(bounded_source_fits_sink(&unknown_table, count, false, true), Some(false));
        // No token at all: `None` (the collect arm keeps the skip for a user
        // `FromIterator`; the extend arm, whose receiver is always std, refuses).
        assert_eq!(
            bounded_source_fits_sink(
                "<I as core::iter::Iterator>::collect::<mycrate::Bag>",
                count,
                false,
                true
            ),
            None
        );
    }

    #[test]
    fn lower_bounds_never_exceed_the_real_size() {
        assert_eq!(ty_size_lower_bound(&Ty::u8(), 0), 1);
        assert_eq!(ty_size_lower_bound(&Ty::u32(), 0), 4);
        assert_eq!(ty_size_lower_bound(&Ty::Char, 0), 4);
        assert_eq!(ty_size_lower_bound(&Ty::Tuple(vec![Ty::u8(), Ty::u32()]), 0), 5);
        assert_eq!(ty_size_lower_bound(&Ty::Array { elem: Box::new(Ty::u32()), len: 3 }, 0), 12);
        assert_eq!(
            ty_size_lower_bound(&Ty::Ref { mutable: false, inner: Box::new(Ty::Str) }, 0),
            8
        );
        // Nothing known about an unsized or opaque type.
        assert_eq!(ty_size_lower_bound(&Ty::Str, 0), 0);
        assert_eq!(ty_size_lower_bound(&Ty::Unit, 0), 0);
        // A receiver's item bytes: its element, clamped by `memory_backed`.
        let slice_of_u64 =
            Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u64()) }) };
        assert_eq!(receiver_min_item_bytes(&slice_of_u64, 0), 8);
        assert_eq!(receiver_min_item_bytes(&Ty::Str, 0), 1);
    }
}

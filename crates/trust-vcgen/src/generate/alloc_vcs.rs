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
pub(super) fn generate_unbounded_allocation_vcs(
    func: &VerifiableFunction,
) -> Vec<VerificationCondition> {
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
        // verifier-precision: bound NON-parameter integer/char locals and temps too
        // (sibling of arg ranges). SOUNDNESS: DROP-ONLY — a true carrier fact.
        formula = conjoin_local_type_ranges(func, formula);
        // Lever A: bound integer/char datatype FIELDS too (same sound carrier fact).
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
            obligation: None,
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
    is_authenticated_std_len_preserving_adaptor(callee, tail)
        || (matches!(tail, "filter" | "take" | "skip" | "step_by" | "take_while")
            && vc_callee_is_std_iter_trait_method(callee, "Iterator", tail))
}

/// An authenticated FREE function in std's iterator module (`core::iter::repeat_n`),
/// as opposed to an `Iterator` trait method. Anchored to the `core::iter::`/
/// `std::iter::` module root after generic stripping, so `mycrate::iter::repeat_n`
/// and `mycrate::repeat_n` fail closed.
pub(super) fn is_authenticated_std_iter_free_fn(callee: &str, name: &str) -> bool {
    if callee.contains(" as ") || callee.starts_with('<') {
        return false;
    }
    let normalized = vc_strip_generics(callee);
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
/// depend on balanced-angle-bracket parsing at all. (The same mis-parse exists in
/// `vc_strip_generics`' other callers; it is disclosed as a residual rather than
/// repaired here, because those are GRANTING lanes where it fails closed.)
pub(super) fn unbounded_sysroot_iterator_adt_name(name: &str) -> Option<&'static str> {
    if let Some(family) = range_family_adt_name(name) {
        return (!matches!(family, "Range" | "RangeInclusive")).then_some(family);
    }
    let head = path_head(name);
    if !path_head_is_sysroot_iter_module(name) {
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
            if matches!(range_family_adt_name(name), Some("Range" | "RangeInclusive")) =>
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
            let inclusive = range_family_adt_name(name) == Some("RangeInclusive");
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
    // The value-side PROVENANCE half. A user ADT anywhere in the chain fails
    // closed here, whatever its producer's path spells — including a std-rooted
    // producer path that RETURNS a user iterator.
    if !operand_is_authenticated_std_iterator_value(func, iter_op) {
        return false;
    }
    // The value-side BOUNDEDNESS half, and a DIFFERENT property from the line
    // above: `core::ops::range::RangeFrom` is genuine, correctly unstamped `core`
    // and still yields forever. See the module note.
    if operand_is_unbounded_sysroot_iterator_value(func, iter_op) {
        return false;
    }
    match local_def(func, local) {
        // `let it = <iter>; it.collect()` — chase the move/copy alias.
        Some(LocalDef::Rvalue(Rvalue::Use(inner))) => {
            collect_source_is_bounded_std_collection(func, inner, depth + 1)
        }
        Some(LocalDef::Call { callee, args }) => {
            let tail = callee_tail(callee);
            // The leaf grant — the one place this walk returns a bare grant of
            // its own (every other `true` is a recursive answer). Both
            // conjuncts are required: the callee-path predicates authenticate the
            // receiver's crate as RENDERED, and
            // `producer_receiver_value_is_authenticated_sysroot` authenticates the
            // receiver OPERAND, which is where the stamp actually lands.
            if (is_std_collection_iter_producer(callee, tail)
                || is_str_view_iter_producer(callee, tail))
                && producer_receiver_value_is_authenticated_sysroot(func, args)
            {
                return true;
            }
            // `a.chain(b)` yields `a.len() + b.len()` — bounded iff BOTH sides are
            // bounded collection sources (the sum of two already-gated allocations
            // is itself bounded). Receiver is arg 0, the chained iterator arg 1.
            if tail == "chain" && vc_callee_is_std_iter_trait_method(callee, "Iterator", "chain") {
                return args
                    .first()
                    .is_some_and(|a| collect_source_is_bounded_std_collection(func, a, depth + 1))
                    && args.get(1).is_some_and(|b| {
                        collect_source_is_bounded_std_collection(func, b, depth + 1)
                    });
            }
            // Walk back through length-NON-INCREASING adaptors (each yields
            // `<= source` elements), receiver is arg 0.
            if is_authenticated_std_len_nonincreasing_adaptor(callee, tail)
                && let Some(recv) = args.first()
            {
                return collect_source_is_bounded_std_collection(func, recv, depth + 1);
            }
            false
        }
        _ => false,
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
    let self_ty = vc_qualified_self_ty(callee).unwrap_or(callee);
    vc_strip_generics(vc_peel_reference_prefixes(self_ty))
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
        && trust_types::path_root_is_authenticated_sysroot_crate(&producer_receiver_path(callee))
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
        Ty::Slice { .. } | Ty::Str | Ty::Array { .. } | Ty::SymArray { .. } => true,
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
pub(super) fn is_std_collection_iter_producer(callee: &str, tail: &str) -> bool {
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
    if !producer_receiver_is_authenticated_sysroot(callee) {
        return false;
    }
    let recv = producer_receiver_path(callee);
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
    if !matches!(tail, "chars" | "char_indices" | "bytes" | "encode_utf16") {
        return false;
    }
    if !producer_receiver_is_authenticated_sysroot(callee) {
        return false;
    }
    let recv = producer_receiver_path(callee);
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
    let guard_paths_map = v2_build_path_guard_map(func);
    // Trust (lane-A CSE): one statement-version oracle for the whole function.
    let sv = StmtVersionCtx::build(func);
    let semantic_guards = match summaries {
        Some(s) => build_semantic_guard_map_with_summaries(func, s),
        None => build_semantic_guard_map(func),
    };
    let bounds_assert_by_target = v2_sole_bounds_assert_by_target(func);

    let mut block_vcs: Vec<(BlockId, VerificationCondition)> = Vec::new();
    for block in &func.body.blocks {
        // The SOLE native `BoundsCheck` assert whose success edge enters this
        // block, if any — a CANDIDATE authority the per-row exact binding below
        // must still confirm. Bare target identity used to suppress every index
        // row in the block, which let a `Lt(_i, len_A)` assert suppress
        // `B[_j]`'s rows on A's authority — the same identity weakness the
        // Overflow/OverflowNeg and Div/Rem lanes removed. See
        // `v2_bounds_assert_exactly_covers_place`.
        let sole_bounds_assert = bounds_assert_by_target
            .get(&block.id)
            .and_then(|assert_index| func.body.blocks.get(*assert_index));
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
            let load_bounds_guarded = sole_bounds_assert.is_some_and(|assert_block| {
                rvalue_safety::direct_projection_load_place(rvalue).is_some_and(|load_place| {
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
                // destination type (it takes `Option<&Ty>`), so never clone the (possibly fat
                // recursive-ADT) declared root for the dest place.
                let dest_ty = crate::place_ty_cow(func, place);
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
            let store_bounds_guarded = sole_bounds_assert.is_some_and(|assert_block| {
                rvalue_safety::place_needs_bounds_check(place)
                    && v2_bounds_assert_exactly_covers_place(
                        func,
                        assert_block,
                        block,
                        stmt_index,
                        place,
                    )
            });
            if !store_bounds_guarded {
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
            // Trust (bounds ARM, GAP 1): mirror the `And([facts.., body])` conjoin onto
            // the recorded obligation as a `ConjoinFactsLast` wrapper (no-op when the VC
            // carries no obligation), so `{body, wrappers}` still replays to `formula`.
            ob_record_conjoin(vc, facts);
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
            ob_record_conjoin(vc, facts);
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
            // Trust (bounds ARM, GAP 1): use the recorded variant so we can mirror the
            // whole-formula version rename onto the recorded body/subject/wrappers, THEN
            // record the filtered preconditions as an outer `ConjoinFactsLast` — exactly
            // as `generate_v2_safety_vcs` does for the arithmetic/negation arms.
            let (new_formula, conjoined) = conjoin_preconditions_versioned_recorded(
                func,
                *block_id,
                &func.preconditions,
                killed,
                vc.formula.clone(),
            );
            vc.formula = new_formula;
            if vc.obligation.is_some() {
                let terminal = func
                    .body
                    .blocks
                    .get(block_id.0)
                    .filter(|b| b.id == *block_id)
                    .map_or(0, |b| b.stmts.len());
                ob_record_rename_at(vc, &sv, func, *block_id, terminal);
                ob_record_conjoin(vc, &conjoined);
            }
        }
    }

    // Trust S2c (exemption): path guards + semantic guards conjoined AFTER the rename.
    for (block_id, vc) in &mut block_vcs {
        if let Some(block_guard_paths) = guard_paths_map.get(block_id) {
            // Trust (bounds ARM, GAP 1): the dominating path-guard map is the sole
            // non-conjoining wrapper. Use the recorded variant to capture the per-path
            // terms and push a `PathGuardOr` wrapper mirroring the `Or` this builds.
            let (new_formula, path_terms) = v2_formula_with_path_guards_recorded(
                func,
                &sv,
                block_guard_paths,
                vc.formula.clone(),
            );
            vc.formula = new_formula;
            if let Some(ob) = vc.obligation.as_mut() {
                ob.wrappers.push(ObligationWrapper::PathGuardOr { paths: path_terms });
            }
        }
    }
    for (block_id, vc) in &mut block_vcs {
        if let Some(sem_guards) = semantic_guards.get(block_id)
            && !sem_guards.is_empty()
        {
            ob_record_conjoin(vc, sem_guards);
            let mut conjuncts = sem_guards.clone();
            conjuncts.push(vc.formula.clone());
            vc.formula = Formula::And(conjuncts);
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
    for (_, vc) in &mut block_vcs {
        ob_record_normalize(vc, func);
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
    if expected {
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
        let Some(range) = crate::range::rust_type_range_constraint(
            &Formula::Var(
                decl.name.clone().unwrap_or_else(|| format!("_{}", decl.index)),
                trust_types::Sort::Int,
            ),
            &decl.ty,
        ) else {
            continue;
        };
        bounds.push(range);
    }
    bounds.extend(versioned_param_type_ranges(func, &formula));
    if bounds.is_empty() {
        return formula;
    }
    bounds.push(formula);
    Formula::And(bounds)
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
fn versioned_param_type_ranges(func: &VerifiableFunction, formula: &Formula) -> Vec<Formula> {
    // Keyed by `place_to_var_name`, the shadow/collision-aware spelling the formula
    // actually uses — the bare loop above keys on `decl.name`, so a SHADOWED
    // parameter has its bound attached to the wrong symbol there.
    let mut param_tys: FxHashMap<String, &Ty> = FxHashMap::default();
    for decl in &func.body.locals {
        if decl.index < 1 || decl.index > func.body.arg_count {
            continue;
        }
        param_tys.insert(place_to_var_name(func, &Place::local(decl.index)), &decl.ty);
    }
    if param_tys.is_empty() {
        return Vec::new();
    }

    let mut occurrences: Vec<(String, trust_types::Sort)> = Vec::new();
    collect_var_sorts(formula, &mut occurrences);

    let mut seen: FxHashSet<String> = FxHashSet::default();
    let mut bounds = Vec::new();
    for (name, sort) in occurrences {
        // Only VERSIONED spellings; the bare name is already bounded above.
        if !name.contains('#') {
            continue;
        }
        // SORT guard: emit only where the symbol occurs at `Sort::Int`, so a
        // bitvector-encoded symbol is not re-declared at a second sort. Stricter
        // than the two siblings, which build `Var(name, Sort::Int)` unconditionally.
        if sort != trust_types::Sort::Int {
            continue;
        }
        // COLLISION guard, the same refusal `pin_in_place_update_reads` and
        // `entry_sentinel_ties` make: `validate_function` does not reserve `#` in
        // local names and `place_to_var_name` permits it, so `n#e` may be a REAL,
        // differently-typed local. Bounding it by `n`'s type would be a FALSE bound,
        // not a weakening. Fail closed.
        if func.body.locals.iter().any(|l| l.name.as_deref() == Some(name.as_str())) {
            continue;
        }
        let Some(ty) = name.split('#').next().and_then(|base| param_tys.get(base)) else {
            continue;
        };
        if !seen.insert(name.clone()) {
            continue;
        }
        if let Some(range) = crate::range::rust_type_range_constraint(
            &Formula::Var(name.clone(), trust_types::Sort::Int),
            ty,
        ) {
            bounds.push(range);
        }
    }
    bounds
}

/// Every `Var` occurrence with the sort it occurs AT. `collect_formula_var_names`
/// discards the sort, which the sort guard above needs.
fn collect_var_sorts(f: &Formula, out: &mut Vec<(String, trust_types::Sort)>) {
    if let Formula::Var(name, sort) = f {
        out.push((name.clone(), sort.clone()));
    }
    for child in f.children() {
        collect_var_sorts(child, out);
    }
}

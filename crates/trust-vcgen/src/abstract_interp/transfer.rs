// trust_vcgen/abstract_interp/transfer.rs: Transfer functions, fixpoint computation,
// threshold widening, and invariant extraction
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::*;

use super::arithmetic::*;
use super::{AbstractDomain, Interval, IntervalDomain, ThresholdSet};

// ── Transfer Functions ─────────────────────────────────────────────────────

/// Resolve an operand to an interval in the given abstract state.
fn operand_to_interval(
    op: &Operand,
    func: &VerifiableFunction,
    state: &IntervalDomain,
) -> Interval {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            // Trust (2026-10-10, review round 115): a `u128` value is not representable
            // in this `i128` domain, and Top here is read by the arithmetic as the
            // `i128` RANGE, which excludes every value at or above 2^127. Whatever the
            // state holds for such a place (a branch can store `[101, i128::MAX]` for
            // `x > 100`) is not a bound on it, so it is read as Top and
            // [`operand_reads_u128`] keeps it out of the arithmetic.
            if operand_reads_u128(func, op) {
                return Interval::TOP;
            }
            let name = crate::place_to_var_name(func, place);
            let tracked = state.get(&name);
            // Trust (2026-09-30): a value read from a place of an integer type is a
            // value of that type (the validity invariant), so an untracked read
            // THROUGH A POINTER (a field through `&self`, an element through a
            // reference) or OUT OF AN ENUM PAYLOAD (`match d { A(x) => x }`) is at
            // least bounded by its type instead of Top. Places of
            // the function's own locals keep their own tracking: a local is seeded
            // with its type range, a checked result field `_k.0` is its own lane,
            // and giving either a type range where the domain had widened it to Top
            // only lengthened the environment (measured: the extra facts made the
            // in-process solver answer "incomplete" where it had found a real
            // counterexample, `callee_postcondition_inside_loop#stale_after_reassign`).
            // A `u128` has no representable range here (`type_to_interval`).
            if tracked == Interval::TOP
                && place.projections.iter().any(|projection| {
                    matches!(projection, Projection::Deref | Projection::Downcast(..))
                })
                && let Some(ty) = crate::place_ty_cow(func, place)
                && let Some(range) = type_to_interval(&ty)
            {
                return range;
            }
            tracked
        }
        Operand::Constant(cv) => match cv {
            ConstValue::Int(n) => Interval::constant(*n),
            ConstValue::Uint(n, _) => {
                if let Ok(v) = i128::try_from(*n) {
                    Interval::constant(v)
                } else {
                    Interval::TOP
                }
            }
            ConstValue::Bool(b) => Interval::constant(i128::from(*b)),
            ConstValue::Float(_) | ConstValue::Unit | ConstValue::CallableItem { .. } => {
                Interval::TOP
            }
            // Sound fallback for unknown ConstValue variants.
            _ => Interval::TOP,
        },
        // Sound fallback for unknown Operand variants.
        _ => Interval::TOP,
    }
}

/// Apply a single statement's abstract transfer function.
#[must_use]
pub fn transfer_function(
    stmt: &Statement,
    func: &VerifiableFunction,
    state: &IntervalDomain,
) -> IntervalDomain {
    let mut result = state.clone();
    transfer_function_in_place_core(stmt, func, &mut result, false);
    result
}

/// Apply a single statement's abstract transfer function in place without cloning `result`.
///
/// When `skip_lockstep_covered_havoc` is `true`, the caller (`transfer_one_statement_in_place`)
/// immediately follows this step with `StmtWrite::forget` derived from `CallHavoc::stmt_writes`,
/// which already covers opaque-deref-store `H` havoc (via `RebindSet::any_rebinder`) and
/// `SetDiscriminant`/`Deinit` union-covered rebinds.
fn transfer_function_in_place_core(
    stmt: &Statement,
    func: &VerifiableFunction,
    result: &mut IntervalDomain,
    skip_lockstep_covered_havoc: bool,
) {
    if result.is_unreachable {
        return;
    }

    match stmt {
        Statement::Assign { place, rvalue, .. } => {
            // Do not track bool-typed locals (e.g. comparison results like
            // `cond = n > 0`). Their [0,1] interval is a vacuous integer bound
            // and would be emitted as `Var(name, Int)` at the formula sink,
            // colliding with the `Var(name, Bool)` the same name carries in
            // branch guards. See `type_to_interval` for the full rationale.
            let is_bool_dest = place.projections.is_empty()
                && matches!(func.body.locals.get(place.local).map(|l| &l.ty), Some(Ty::Bool));
            if !is_bool_dest {
                let target_name = crate::place_to_var_name(func, place);
                // A discriminant read is decided below, where the destination type is
                // known ([`discriminant_read_hull`]); `eval_rvalue` answers TOP for it.
                let mut interval = eval_rvalue(rvalue, func, result);
                // Trust (2026-08-20, bare-BinaryOp wrapping): a PLAIN MIR
                // integer `Add`/`Sub`/`Mul` WRAPS mod 2^w — the
                // overflow-checked form is the separate `CheckedBinaryOp` +
                // `Assert` pair, whose overflow path never survives past its
                // assert edge. `eval_rvalue`'s mathematical interval is exact
                // for the bare form ONLY when it fits the destination type
                // entirely (then no input drawn from the operand intervals can
                // wrap); otherwise some execution may wrap and the machine
                // value can land anywhere in the type's range — clamp to that
                // full range (sound: it contains every machine value; Top when
                // the type range is unknown/unrepresentable). Without this,
                // `a ∈ [0,3] ⇒ a - 1 ∈ [-1,2]` EXCLUDED the real wrapped
                // value `u64::MAX` at `a == 0`, and `try_discharge_batch`
                // could discharge a bounds VC the runtime violates — the
                // interval-lane sibling of the unbounded-def false PROVE
                // fixed in `guards::extract_block_definitions` the same day.
                // Trust (2026-09-28): a bare `Shl` wraps too. Rust never panics on bits
                // shifted out (`64i8 << 1 == -128`; the overflow check covers only the
                // shift AMOUNT), so its mathematical interval must be clamped like
                // `Add`/`Sub`/`Mul`. `x ∈ [64, 127] ⇒ x << 1 ∈ [128, 254]` excluded
                // every real `i8` result.
                // Trust (2026-09-30, round 12; 2026-10-05, NEG-WRAP-OFF-1): a bare
                // integer `Neg` wraps too (`-MIN == MIN`; the overflow check is the
                // separate dominating `Assert(OverflowNeg)`), so its mathematical
                // interval is clamped like the binops'.
                if let Rvalue::BinaryOp(BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Shl, ..)
                | Rvalue::UnaryOp(UnOp::Neg, _) = rvalue
                {
                    interval = clamp_bare_binop_to_dest_range(interval, func, place);
                }
                // Trust (2026-09-28): a discriminant read is its enum's tag hull,
                // negative tags included — see [`discriminant_read_hull`].
                if let Rvalue::Discriminant(src) = rvalue {
                    interval = match discriminant_read_hull(func, src, place) {
                        Some((lo, hi)) => Interval::new(lo, hi),
                        None => Interval::TOP,
                    };
                }
                // Trust: 2026-09-16 (round A11) — a write REBINDS every tracked name
                // inside or above its destination, not only the destination's own
                // key: `p = q` rebinds `p.0`; `j = k` rebinds `s*[_j]` (the index
                // local embedded by number, reached through the fallback `_j`);
                // `a[_i] = w` may rebind `a[0]`; `x = &y` rebinds `x*`. The transfer
                // previously `set` the destination alone, so an element STORE's
                // interval `s*[_4] ∈ [3, 3]` survived the reseat `_4 = copy _3` in
                // the same block — the statement-transfer twin of the path-def
                // staleness the review named (`rev11c`: "the interval lane sets
                // `s*[_j]` on an element store and never kills it on a whole write
                // of `j`"). The whole-function join in `merged_interval_environment`
                // happened to mask it on the measured bodies (a block without the
                // store joins the name to Top), which is not a discipline. Forget
                // (Top) every rebound name before setting the destination — the
                // SAME directional relation the terminator havoc and the SMT lane's
                // kills use. SOUND: forgetting an interval can only WIDEN the
                // abstract state, so it can turn a PROVE into a not-proved, never
                // create a proof.
                // Trust: 2026-10-12 (UNION-SIBLING-WRITE-1) — a write through a union
                // field rebinds every overlapping sibling: forget each name its union
                // cover rebinds, the cover the formula lane's write oracles carry
                // (`generate::union_write_cover_name`). Before it, `u.a = x as u64` set
                // `u.0 ∈ [0, 2^32-1]` and the write of `u.1 = -1` left that interval on
                // `u.0`, whose bytes now read `u64::MAX`. The destination and its cover
                // are `generate::WrittenPlace`, the spelling `stmt_writes_name` tests
                // (INTERVAL-WRITE-LOCKSTEP-2); we reuse `target_name` directly here to
                // avoid minting a duplicate destination `String`.
                if !result.vars.is_empty() {
                    let fallback = (place.projections.is_empty()
                        && crate::generate::local_is_index_operand(func, place.local))
                    .then(|| crate::generate::local_fallback_name(place.local));
                    let cover = crate::generate::union_write_cover_name(func, place);
                    result.vars.retain(|name, _| {
                        name == &target_name
                            || !(crate::generate::dest_write_rebinds(&target_name, name)
                                || cover
                                    .as_deref()
                                    .is_some_and(|c| crate::generate::dest_write_rebinds(c, name))
                                || fallback.as_deref().is_some_and(|f| {
                                    crate::generate::write_covers_index_segment(f, name)
                                }))
                    });
                }
                // Trust: 2026-10-10 (review round 111) — a store through a pointer
                // whose referent does not fold (`deref_store_is_opaque`) may write any
                // local whose `&mut`/`&raw mut` was taken, or the pointee of any
                // mutable pointer: forget every name the SMT lane havocs at the same
                // store (`path_defs::stmt_writes_name`, one list,
                // `function_havoc_names`). The dest name alone (`_10*`) rebinds
                // nothing under the real referent: `let mut q = &mut m; let pp = &mut
                // q; **pp = v` (MIR `_10 = copy (*_5); (*_10) = _2`) kept `m ∈ [25,
                // 25]`, the copy `_7 = m` read it, and the conjoined `_7 ∈ [25, 25]`
                // discharged `a[m / 1]`: PROVED kernel-certified, panics at `v = 26`.
                // Forgetting only widens the state.
                // Trust: 2026-10-10 (review round 112) — a store through a `&mut`
                // PARAMETER that is never reseated, with no second `Deref`, writes
                // memory that existed before this frame, so it cannot reach the
                // storage of a local of the frame: names spelled without a `*` keep
                // their intervals (`let mut m = 3; let r = &mut m; *r = 5; *v = w;
                // a[m / 1]`, `v: &mut usize`, proved before the forget above and is
                // correct). A name with a `*` is memory behind some pointer, which
                // the parameter may alias, and is forgotten.
                if !skip_lockstep_covered_havoc
                    && !result.vars.is_empty()
                    && matches!(place.projections.first(), Some(Projection::Deref))
                    && crate::deref_store_is_opaque(func, place)
                {
                    let frame_storage_survives = store_spares_frame_storage(func, place);
                    let havoc = crate::generate::function_havoc_names(func);
                    result.vars.retain(|name, _| {
                        (frame_storage_survives && is_frame_storage_name(name))
                            || !havoc.iter().any(|h| crate::generate::write_rebinds(h, name))
                    });
                }
                result.set(target_name, interval);
                // Trust (2026-09-30): the checked result FIELD `_k.0`. On the path past
                // the overflow assert it is the mathematical result above (narrowed
                // there, `checked_result_field_on_success`); on any path it is a
                // value of its type, so here it gets the mathematical interval only
                // when that fits the type, and the type's range otherwise.
                if let Rvalue::CheckedBinaryOp(..) = rvalue
                    && tracking_checked_fields()
                    && let Some((field, elem_range)) = checked_result_field(func, place)
                {
                    match elem_range {
                        Some(range) if range.lo <= interval.lo && interval.hi <= range.hi => {
                            result.set(field, interval);
                        }
                        Some(range) => result.set(field, range),
                        None => {}
                    }
                }
            }
        }
        // Trust (2026-10-10, review round 115): the interval twins of the SMT lane's
        // non-`Assign` writes (`path_defs::stmt_writes_name`). A `copy_nonoverlapping`
        // (count not a literal zero) may write every local, so it forgets every
        // interval, and an intrinsic or unsupported statement is forgotten the same
        // way; `SetDiscriminant` and `Deinit` rebind their place. These were no-ops
        // here, so `let mut m = 1; copy_nonoverlapping(&v, &mut m, 1); let t = m; a[t]`
        // kept `t ∈ [1, 1]` from the def site and the bounds row was discharged.
        Statement::CopyNonOverlapping { count, .. } => {
            if !matches!(count, Operand::Constant(ConstValue::Int(0) | ConstValue::Uint(0, _))) {
                result.vars.clear();
            }
        }
        Statement::Intrinsic { name, .. } if name == "assume" => {}
        Statement::Intrinsic { .. } | Statement::Unsupported { .. } => result.vars.clear(),
        Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
            if !skip_lockstep_covered_havoc && !result.vars.is_empty() {
                let written = crate::place_to_var_name(func, place);
                result.vars.retain(|name, _| !crate::generate::write_rebinds(&written, name));
            }
        }
        Statement::Nop => {}
        _ => {}
    }
}

/// Whether `place` is `(*p).rest` with exactly one `Deref`, `p` a `&mut` parameter
/// whose own slot is never written or `&mut`/`&raw` borrowed in the body: the store
/// then reaches only memory the caller handed in, never a local of this frame. A
/// borrow THROUGH the parameter (`&mut (*p).1`, `&mut *p`) cannot reseat it, so the
/// slot question is asked modulo pointee borrows (round 113: `let q = &mut v.1; v.0 =
/// w; a[m / 1]` lost the proof of `m` under the wide escape classifier).
fn store_through_unreseated_mut_param(func: &VerifiableFunction, place: &Place) -> bool {
    let is_param = place.local >= 1 && place.local <= func.body.arg_count;
    is_param
        && place.projections.iter().filter(|p| matches!(p, Projection::Deref)).count() == 1
        && matches!(
            func.body.locals.get(place.local).map(|d| &d.ty),
            Some(Ty::Ref { mutable: true, .. })
        )
        && crate::local_defs::is_single_static_assignment_modulo_pointee_borrows(func, place.local)
}

/// Merge 2026-10-14: the ONE statement of the round-112 exemption, asked by every
/// interval-lane forget of a store (`transfer_function`'s opaque-store forget, the
/// lockstep [`StmtWrite::Function`]) and by both `cfg(test)` re-derivations of the
/// lockstep ([`transfer_statements_observed`],
/// [`assert_environment_bounds_every_statement_point`]): a store to `place` through a
/// never-reseated `&mut` parameter ([`store_through_unreseated_mut_param`]) cannot
/// write the body's own storage ([`is_frame_storage_name`]).
///
/// The formula path's oracle (`generate::stmt_writes_name`) still versions those names
/// at the store (it havocs the whole-function list). That is a superset of the store's
/// real writes, and the interval kept here is a bound on the value every such version
/// denotes, because no execution of the store changes it. This is the one place the
/// interval lane keeps a name the oracle versions; everywhere else the lockstep holds.
fn store_spares_frame_storage(func: &VerifiableFunction, place: &Place) -> bool {
    matches!(place.projections.first(), Some(Projection::Deref))
        && store_through_unreseated_mut_param(func, place)
}

/// A name of the body's OWN storage — a local, or a field or element of one — spelled
/// with no `*` (no step through a pointer). A name with a `*` is memory behind some
/// pointer, which a `&mut` parameter may alias.
fn is_frame_storage_name(name: &str) -> bool {
    !name.contains('*')
}

/// `cfg(test)` form of [`store_spares_frame_storage`] for a statement and a name.
#[cfg(test)]
fn stmt_spares_frame_storage(func: &VerifiableFunction, stmt: &Statement, name: &str) -> bool {
    matches!(stmt, Statement::Assign { place, .. } if store_spares_frame_storage(func, place))
        && is_frame_storage_name(name)
}

/// Trust (P0 call-arg &mut staleness): apply a block's TERMINATOR transfer to the
/// abstract state, run AFTER every statement transfer and BEFORE propagating to
/// successors. The fixpoint previously applied only statement transfers, so the
/// CFG-edge state out of a `Call`-terminated block kept the PRE-call interval of
/// any local the callee can write — its destination AND any local whose `&mut`/
/// `&raw mut` reference (or a nested mutable pointer) escapes into the call. That
/// stale interval then discharged a safety obligation about the POST-call value:
/// e.g. `let mut i = 0; set(&mut i, 99); arr[i]` kept `i ∈ [0,0]` across
/// `set(&mut i, …)`, so the bounds check `i < 4` was proved while `i == 99` at
/// runtime (a confirmed false PROVE in DEFAULT mode for `mem::swap`/`replace`/
/// `take` and user `&mut` setters).
///
/// Havoc (forget → Top) every name the call may reassign, computed by the SAME
/// `terminator_def_names` over-approximation the formula path uses at a `Call`
/// (`mutably_borrowed_local_names ∪ mutable_pointer_local_names ∪ {dest}`), so the
/// interval lane and the SMT lane stay in lockstep. SOUNDNESS: forgetting an
/// interval can only WIDEN the abstract state (Top is the lattice identity for the
/// join), so it can only turn a PROVE into a not-proved — it can never create a
/// false proof. A by-VALUE argument and a SHARED `&`/`*const` argument are NOT in
/// the havoc set (they cannot drive a mutation), so legitimate code that passes a
/// copy or a shared borrow before indexing still proves.
///
/// Trust (2026-10-04, trust-interval-drop-havoc): a `Drop` havocs too. Drop glue runs
/// user code (`impl Drop`) holding `&mut` to the dropped value and to everything
/// mut-reachable from it, so it havocs exactly the list the formula path gives it
/// (`terminator_def_names_structured`: the whole-function list, the dropped place and
/// its pointee, the names behind every stored reference). Until this change the
/// transfer skipped it, and the stale interval reached the obligations through the
/// base-name fallback of the discharge (`interval_for_var`), which reads a post-drop
/// SSA version (`c#s0_t`) as the bare `c`. MEASURED (probe rounds `dh-r1`/`dh-r2`,
/// verify-on against a verify-off truth run): with a guard holding `&mut c` whose
/// `Drop` stores `k` into `c`,
/// `let mut c = 0; { let _s = Setter { r: &mut c, v: k }; } match c { 0 => 0, n => n + u32::MAX }`
/// kept `c ∈ [0, 0]` past the drop, the `n` arm's overflow obligation was DISCHARGED
/// at generation (`solver_vcs=0 discharged=1`), so ay never saw it and the row was
/// published `runtime_checked` instead of the refutation the same write through a
/// `Call` gets; the build passed (rc 0) and `f(7)` panicked. Forgetting at the `Drop`
/// only widens the state, so it can turn a discharge into a dispatch and never create
/// one. Which terminators havoc is no longer a list kept here: see
/// [`terminator_havocs_intervals`].
///
/// `block` is `func.body.blocks[pos]`, and `havoc` is the run's [`CallHavoc`] for
/// `func`: the havoc set is computed once per block per fixpoint run and matched by
/// index (see [`CallHavoc`]), never re-derived and string-scanned per visit.
#[must_use]
fn transfer_terminator(
    havoc: &mut CallHavoc<'_>,
    pos: usize,
    block: &BasicBlock,
    mut result: IntervalDomain,
) -> IntervalDomain {
    if result.is_unreachable {
        return result;
    }
    // Trust: 2026-10-08 (H3 OPAQUE-ASM-OUTPUT) — and an `Opaque` terminator, whose
    // formula-path write set is `Function` plus EVERY local (its `asm!` outputs, a call
    // destination it could not lower: places the extraction did not keep). Without it the
    // state on an `asm!`'s out-edge kept the pre-asm interval of the asm's own output
    // (`k in [0, 3]` after `inout(reg) k` wrote 4..7), and the discharge's whole-function
    // join -- which a versioned name falls back to (`interval_for_var`) -- claims that
    // bound at every point `k` is a value. Drop glue is mirrored too (2026-10-08,
    // trust-interval-drop-havoc; the reproducer is in this function's doc): the formula
    // path havocs `Function` + the dropped place at a `Drop`, and so does this lane.
    // Which terminators havoc is [`terminator_havocs_intervals`], the one predicate the
    // index is built by.
    if let Some(kill) = havoc.of(pos, block) {
        // Forget any tracked variable whose name is (prefix-)overlapped by a
        // havoced name: the local itself, its pointee `x*`, a field `x.0`, …
        result.vars.retain(|name, _| !kill.rebinds(name));
    }
    result
}

/// The terminators the interval transfer havocs at: EVERY terminator that writes a
/// place, as `trust_types::Terminator::place_writes` classifies it — a `Call` (its
/// destination), a `TailCall`, a `Drop` (drop glue, 2026-10-08
/// trust-interval-drop-havoc) and an `Opaque` terminator (unlocatable writes,
/// 2026-10-08 H3 OPAQUE-ASM-OUTPUT). ONE predicate, read by the derivation
/// ([`BlockHavoc::of`]) and by its `cfg(test)` re-derivation ([`CallHavoc::of`]), so
/// the two cannot disagree about which blocks havoc.
///
/// It is the classifier and not a list of kinds kept here, because the list is how
/// this lane fell behind the formula path twice: it named `Call`/`TailCall` while
/// `terminator_def_names_structured` gave `Drop` and `Opaque` a write set, and each
/// gap was a stale interval deciding an obligation after the write. `place_writes`
/// is exhaustive over `Terminator` with no wildcard, so a new terminator does not
/// compile until it is classified there, and a classified writer havocs here without
/// anyone remembering this file. What it havocs is still the formula path's list; a
/// terminator this predicate skips must have an EMPTY list there, which
/// [`CallHavoc::of`] re-checks at every visit under `cfg(test)`.
fn terminator_havocs_intervals(terminator: &Terminator) -> bool {
    !matches!(terminator.place_writes(), trust_types::PlaceWrites::None)
}

/// The havoc of every havocking block ([`terminator_havocs_intervals`]) of ONE
/// function, derived at the block's first visit in a fixpoint run and INDEXED for the
/// per-name test.
///
/// Trust (2026-10-02, trust-fixpoint-deadline). [`transfer_terminator`] used to
/// re-derive `terminator_def_names(func, block)` at EVERY visit of a call block and
/// then test every tracked name against every havoc name with `write_rebinds`: per
/// visit, O(tracked names x havoc names) string comparisons. The interval fixpoint
/// visits a block up to ~20 times in its ascending phase and again in every
/// narrowing pass and repair round, and the whole fixpoint runs several times per
/// function (`merged_interval_environment` serves several lanes). MEASURED on
/// aterm-census `lock_order::run_lock_order_census` at `-Zmir-opt-level=2` (1044
/// blocks, 3603 locals, 358 call blocks; trust c24a6dc02a, the census-vcgen-hang fold
/// fix): the function spent 346 s — 226 s past its 120 s budget — and two `sample`s
/// put ~91% of it in this one `retain`: `write_rebinds` -> `place_names_overlap` /
/// `write_covers_index_segment`.
///
/// SAME DECISION. Each test is a `rebind_index::RebindSet` probe, whose
/// `any_rebinder(name)` answers exactly `set.iter().any(|h| write_rebinds(h, name))`
/// (pinned against the predicate by
/// `rebinder_structures_match_the_predicates_on_a_random_grammar`, and re-checked
/// here, name by name, under `cfg(test)` against the scan this replaced). A
/// terminator's havoc list is `terminator_def_names_structured(func, block)` flattened:
/// the whole-function list `H` ([`crate::generate::function_havoc_names`]) — unrefined
/// ([`TermHavoc::Function`]), refined per call ([`TermHavoc::Refined`]), restricted to
/// what a callee reaches without an argument ([`TermHavoc::Escape`], 2026-10-06) or
/// absent ([`TermHavoc::None`]) — followed by the terminator's extras (its destination
/// and the names derived from it; at a `Drop` the dropped place and its pointee; the
/// names behind every stored reference; at an `Opaque` terminator every local's write
/// names). "Some member of `H ++ extras`
/// rebinds `name`" is "some member of `H` does, or some extra does", so `H` is indexed
/// ONCE per run and shared by every unrefined block, and so is the escape arm's kept
/// list; a block indexes only its extras, or its whole refined list. (Before: a copy
/// of `H` per call block per visit.) The list is a function of
/// `(func, block)` and of ambient state no fixpoint run changes (the per-function
/// memos; the callee write-set stack of the enclosing generation), so deriving it at
/// the block's first visit is deriving it at every visit — re-derived and compared at
/// every visit under `cfg(test)`. Blocks are keyed by POSITION in `func.body.blocks`,
/// not by id, so a body that repeats an id still gets each block's own terminator.
///
/// [`TermHavoc::Function`]: crate::generate::TermHavoc::Function
/// [`TermHavoc::Refined`]: crate::generate::TermHavoc::Refined
/// [`TermHavoc::Escape`]: crate::generate::TermHavoc::Escape
/// [`TermHavoc::None`]: crate::generate::TermHavoc::None
pub(super) struct CallHavoc<'f> {
    func: &'f VerifiableFunction,
    /// The indexes more than one block of the run reads.
    shared: SharedHavoc,
    /// Per block position: `None` until first asked; then `Some(None)` for a
    /// terminator that havocs nothing, `Some(Some(havoc))` for one that does.
    by_block: Vec<Option<Option<BlockHavoc>>>,
    /// Per block position: `None` until first asked; then the block's statements
    /// that write MORE than their own destination ([`StmtWrite`]), in statement
    /// order — empty for nearly every block.
    stmts_by_block: Vec<Option<BlockStmtWrites>>,
}

/// One block's statements that write more than their own destination, in statement
/// order: `(statement index, what it writes)`.
type BlockStmtWrites = std::rc::Rc<[(usize, StmtWrite)]>;

/// The havoc indexes a fixpoint run builds once and every block that havocs the same
/// list reads.
#[derive(Default)]
struct SharedHavoc {
    /// `H` indexed, built at the first block that havocs it unrefined
    /// ([`TermHavoc::Function`]). `None` until then.
    ///
    /// [`TermHavoc::Function`]: crate::generate::TermHavoc::Function
    function: Option<std::rc::Rc<crate::generate::rebind_index::RebindSet>>,
    /// The escape arm's kept list indexed ([`TermHavoc::Escape`]), with the payload it
    /// was built from. The index is reused only for the SAME payload (`Rc::ptr_eq`):
    /// under the per-function memo scope every escape-arm call of a function carries
    /// one payload, so it is built once per run; with no memo scope each call carries
    /// its own copy and gets its own index — never another list's.
    ///
    /// [`TermHavoc::Escape`]: crate::generate::TermHavoc::Escape
    escape: Option<(
        std::rc::Rc<crate::generate::EscapeHavoc>,
        std::rc::Rc<crate::generate::rebind_index::RebindSet>,
    )>,
}

impl SharedHavoc {
    /// The whole-function list `H` ([`crate::generate::function_havoc_names`])
    /// indexed, built at the first terminator or statement of the run that havocs it
    /// unrefined and shared by every later one. `None` when `H` is empty.
    fn function_index(
        &mut self,
        func: &VerifiableFunction,
    ) -> Option<std::rc::Rc<crate::generate::rebind_index::RebindSet>> {
        let h = crate::generate::function_havoc_names(func);
        if h.is_empty() {
            return None;
        }
        let set = self.function.get_or_insert_with(|| {
            crate::fn_memo::count_interval_function_havoc_indexes();
            index_havoc_names(&h)
        });
        Some(std::rc::Rc::clone(set))
    }
}

/// What ONE STATEMENT writes beyond its own destination, as the formula path's
/// per-statement write oracle ([`crate::generate::stmt_writes_name`]) says it.
///
/// Trust (2026-10-08, trust-interval-drop-havoc). [`transfer_function`] forgets the
/// names its destination rebinds and nothing else. `stmt_writes_name` — the version
/// oracle's single-statement test — says four statements write more, and this lane
/// skipped all four:
///
/// * an OPAQUE DEREF STORE (`*p = v` where `p` does not fold to one referent: a
///   branch-selected or reseated pointer, a pointer loaded from memory, a parameter)
///   may write any place a pointer can reach, i.e. the whole-function list `H`
///   (`deref_store_havoc_names`). MEASURED, plain safe code with no call and no
///   drop: `let p = if k > 3 { &mut c } else { &mut d }; *p = k; match c { 0 => d,
///   n => n + u32::MAX }` kept `c ∈ [0, 0]` across the store, the `n` arm's
///   overflow was DISCHARGED at generation, ay never saw it, the row was published
///   `runtime_checked`, the build passed and `f(7)` panicked (probe round `as-r1`:
///   8 of 15 shapes — the pointer in a struct field, a tuple, an `Option`, reseated
///   in a loop, reborrowed, a division by zero). A pointer with ONE referent was
///   never affected: its store is spelled as a store to the referent.
/// * a `SetDiscriminant` and a `Deinit` write every name under their place;
/// * a `CopyNonOverlapping` that copies anything writes memory no place names: every
///   local is a possible write.
///
/// Trust (2026-10-12, INTERVAL-WRITE-LOCKSTEP-2). Wave 24 widened the oracle in two
/// ways that reached this enum's statements, and this lane followed neither (only
/// `transfer_function`'s `Assign` took the union cover). The lockstep check of
/// [`transfer_statements`] failed on main's own fixture
/// (`stmt_write_tests::a_statement_that_writes_no_place_and_a_borrow_forget_nothing`:
/// "kept `dst` across statement 0", the `c = 0` before `src = &raw mut c`):
///
/// * LAUNDERED-ALIAS-STORE: a write whose own name lands in escaped storage, in a body
///   that reads through a pointer the referent fold cannot resolve, havocs `H` like an
///   opaque store (`generate::write_havocs_function_list`). This lane still asked the
///   opaque-store test alone, so `len = n` kept the interval of `q*` (a read through
///   an unresolved copy of `&raw mut len`) and of every pointer local. The `Store`
///   channel now asks `write_havocs_function_list` itself: one predicate, so the two
///   lanes cannot drift on it again.
/// * UNION-SIBLING-WRITE-1: a `SetDiscriminant` / `Deinit` of a union field writes
///   every overlapping sibling. Their arms carry the cover now
///   (`generate::WrittenPlace`, the spelling the oracle tests).
///
/// The confined form of the opaque store (a constant field path under a struct
/// pointer, where the formula path spares the storing pointer's own tree) is NOT
/// distinguished: this lane forgets all of `H` at every opaque store, a superset of
/// the oracle's answer. Forgetting only widens, so that can cost a discharge and
/// never create one; what it costs today is nothing the discharge reads, since a
/// pointee name is already Top in the whole-function environment (the entry block
/// joins it there).
enum StmtWrite {
    /// A write that havocs `H` (`generate::write_havocs_function_list`: an opaque deref
    /// store, or a write into escaped storage a laundered pointer can read): every name
    /// `H` rebinds, except the write's own destination (which it has just set), and
    /// except the body's own storage when `spares_frame_storage`
    /// ([`store_spares_frame_storage`]: a store through a never-reseated `&mut`
    /// parameter, review round 112).
    Function {
        index: std::rc::Rc<crate::generate::rebind_index::RebindSet>,
        dest: String,
        spares_frame_storage: bool,
    },
    /// `SetDiscriminant`: every name the place or its union cover `write_rebinds`.
    Under(crate::generate::WrittenPlace),
    /// `Deinit`: every name the place or its union cover `dest_write_rebinds`.
    DestUnder(crate::generate::WrittenPlace),
    /// A statement whose writes no place names (a memory-writing `CopyNonOverlapping`,
    /// an intrinsic other than `assume`, an `Unsupported` statement): every tracked
    /// name.
    Everything,
}

impl StmtWrite {
    /// `None` for a statement that writes nothing beyond its own destination.
    ///
    /// Trust (2026-10-09, trust-interval-drop-havoc, independent review). WHICH
    /// statements write is read from `trust_types::Statement::place_writes`, the
    /// classifier that is exhaustive over `Statement` with no wildcard, and each of
    /// its channels is matched here with no wildcard either (`PlaceWriteChannel` is
    /// deliberately not `#[non_exhaustive]`). This used to be a list of four statement
    /// kinds ending in `_ => None`, the pattern [`terminator_havocs_intervals`]
    /// replaced on the terminator side for the reason given there: a list kept in
    /// this file is how the lane fell behind the formula path. A new `Statement`
    /// does not compile until `place_writes` classifies it; a new channel does not
    /// compile until it is matched below; and a statement classified UNLOCATABLE
    /// forgets every tracked name unless it is one of the two shapes measured to
    /// write nothing (a pointer copy of a literal zero elements, and `assume`, which
    /// the generator already treats as a metadata no-op). The one wildcard left is
    /// that fail-closed arm. Forgetting more than the write oracle versions is always
    /// allowed (it can cost a discharge and never create one), so `Intrinsic` and
    /// `Unsupported`, which `stmt_writes_name` answers `false` for behind its own
    /// wildcard, are forgotten here: the first "may mutate memory" by the generator's
    /// own account (`intrinsic_is_metadata_noop`), the second fails its function
    /// closed with an `UnsupportedMir` row whatever this lane keeps.
    fn of(
        func: &VerifiableFunction,
        stmt: &Statement,
        shared: &mut SharedHavoc,
    ) -> Option<StmtWrite> {
        use trust_types::PlaceWriteChannel as Channel;
        let places = match stmt.place_writes() {
            trust_types::PlaceWrites::None => return None,
            trust_types::PlaceWrites::Unlocatable => {
                return match stmt {
                    Statement::CopyNonOverlapping { .. }
                        if !crate::generate::copy_nonoverlapping_writes_memory(stmt) =>
                    {
                        None
                    }
                    Statement::Intrinsic { name, args }
                        if crate::generate::intrinsic_is_metadata_noop(func, name, args) =>
                    {
                        None
                    }
                    _ => Some(StmtWrite::Everything),
                };
            }
            trust_types::PlaceWrites::Places(places) => places,
        };
        let mut extra: Option<StmtWrite> = None;
        for (place, channel) in places {
            let write = match channel {
                // The destination of an `Assign`. `transfer_function` rebinds it (and
                // its union cover); it writes MORE exactly when the formula path's
                // oracle says it havocs `H`: an opaque deref store, or a write into
                // escaped storage a laundered pointer copy can read. The SAME predicate
                // `stmt_writes_name` asks (INTERVAL-WRITE-LOCKSTEP-2).
                //
                // Merge 2026-10-14 (review round 112 under the lockstep): a store
                // through a never-reseated `&mut` PARAMETER writes caller memory only,
                // so the body's own storage keeps its interval here exactly as it does
                // in `transfer_function` ([`store_spares_frame_storage`]). Without it
                // this forget undid the round-112 exemption, and `let mut m = 3; let r =
                // &mut m; *r = 5; *v = w; a[m / 1]` (`review111` `r1d`) lost its proof.
                Channel::Store => {
                    if crate::generate::write_havocs_function_list(func, place) {
                        shared.function_index(func).map(|index| StmtWrite::Function {
                            index,
                            dest: crate::place_to_var_name(func, place),
                            spares_frame_storage: store_spares_frame_storage(func, place),
                        })
                    } else {
                        None
                    }
                }
                Channel::SetDiscriminant => {
                    Some(StmtWrite::Under(crate::generate::WrittenPlace::of(func, place)))
                }
                Channel::Deinit => {
                    Some(StmtWrite::DestUnder(crate::generate::WrittenPlace::of(func, place)))
                }
                // Taking a mutable borrow or a raw address writes nothing at its own
                // statement: the write THROUGH it is a later deref store (above) or a
                // call (the terminator havoc), and the borrowed place is in `H` for
                // exactly those.
                Channel::MutBorrow | Channel::RawBorrow { .. } => None,
                // Terminator channels. No statement carries one; if one ever does,
                // nothing here knows what it writes.
                Channel::CallDest | Channel::TailCallReturn | Channel::DropGlue => {
                    Some(StmtWrite::Everything)
                }
            };
            extra = match (extra, write) {
                (None, write) => write,
                (extra @ Some(_), None) => extra,
                // Two extra writes in one statement: no statement has them today, and
                // the union of two write sets is not one of the shapes above.
                (Some(_), Some(_)) => Some(StmtWrite::Everything),
            };
        }
        extra
    }

    /// Whether this statement writes `name` beyond its own destination: the one
    /// predicate [`StmtWrite::forget`] and the environment's statement-point join
    /// ([`join_statement_values`]) both read.
    fn writes(&self, name: &str) -> bool {
        match self {
            StmtWrite::Function { index, dest, spares_frame_storage } => {
                name != dest
                    && !(*spares_frame_storage && is_frame_storage_name(name))
                    && index.any_rebinder(name)
            }
            StmtWrite::Under(place) => place.rebinds(name),
            StmtWrite::DestUnder(place) => place.dest_rebinds(name),
            StmtWrite::Everything => true,
        }
    }

    /// Forget every tracked name this statement writes.
    fn forget(&self, state: &mut IntervalDomain) {
        match self {
            StmtWrite::Everything => state.vars.clear(),
            _ => state.vars.retain(|name, _| !self.writes(name)),
        }
    }
}

/// Apply one statement transfer and its extra write havoc in place, asserting lockstep
/// under `cfg(test)` when differential checks are enabled.
fn transfer_one_statement_in_place(
    func: &VerifiableFunction,
    block: &BasicBlock,
    k: usize,
    stmt: &Statement,
    write: Option<&StmtWrite>,
    current: &mut IntervalDomain,
) {
    let _ = (block, k);
    transfer_function_in_place_core(stmt, func, current, true);
    if let Some(write) = write
        && !current.is_unreachable
    {
        write.forget(current);
    }
    #[cfg(test)]
    if crate::generate::differential_enabled() && !current.is_unreachable {
        let dest = match stmt {
            Statement::Assign { place, .. } => Some(crate::place_to_var_name(func, place)),
            _ => None,
        };
        for name in current.vars.keys() {
            // The round-112 exemption (`store_spares_frame_storage`) is the one
            // name this lane keeps across a write the oracle versions.
            if dest.as_deref() == Some(name.as_str())
                || stmt_spares_frame_storage(func, stmt, name)
            {
                continue;
            }
            assert!(
                !crate::generate::stmt_writes_name(func, block, k, name),
                "the interval lane kept `{name}` across statement {k} of bb{} ({stmt:?}), \
                 which the formula path's write oracle says that statement writes",
                block.id.0
            );
        }
    }
}

/// Every statement transfer of `block` (which is `func.body.blocks[pos]`), in order:
/// [`transfer_function`], then whatever the statement writes beyond its own
/// destination ([`StmtWrite`]). The four fixpoint walks call this and then
/// [`transfer_terminator`]; nothing else transfers a block.
///
/// LOCKSTEP, re-checked under `cfg(test)` at every statement of every walk: a name
/// this lane still tracks after a statement is one the formula path's
/// `stmt_writes_name` says the statement does NOT write (the destination the
/// statement has just set excepted). The interval lane may forget more than the
/// oracle; it may not keep what the oracle versions.
#[must_use]
fn transfer_statements(
    havoc: &mut CallHavoc<'_>,
    pos: usize,
    block: &BasicBlock,
    entry: IntervalDomain,
) -> IntervalDomain {
    let func = havoc.func;
    let writes = havoc.stmt_writes(pos, block);
    // In statement order, so one forward cursor finds each statement's entry.
    let mut pending = writes.iter().peekable();
    let mut current = entry;
    for (k, stmt) in block.stmts.iter().enumerate() {
        let write = pending.next_if(|(at, _)| *at == k).map(|(_, write)| write);
        transfer_one_statement_in_place(func, block, k, stmt, write, &mut current);
    }
    current
}

/// [`transfer_statements`], handing every statement's transfer to `observe` as it
/// happens: the statement, what it writes beyond its own destination, the state
/// before it and the state after it. The fixpoint walks observe nothing; the
/// environment's statement-point join ([`join_statement_values`]) reads the values a
/// statement leaves behind. ONE walk for both, so the environment cannot be joined
/// over a different transfer than the fixpoint ran.
#[must_use]
fn transfer_statements_observed(
    havoc: &mut CallHavoc<'_>,
    pos: usize,
    block: &BasicBlock,
    entry: IntervalDomain,
    mut observe: impl FnMut(&Statement, Option<&StmtWrite>, &IntervalDomain, &IntervalDomain),
) -> IntervalDomain {
    let func = havoc.func;
    let writes = havoc.stmt_writes(pos, block);
    // In statement order, so one forward cursor finds each statement's entry.
    let mut pending = writes.iter().peekable();
    let mut current = entry;
    for (k, stmt) in block.stmts.iter().enumerate() {
        let write = pending.next_if(|(at, _)| *at == k).map(|(_, write)| write);
        let mut next = current.clone();
        transfer_one_statement_in_place(func, block, k, stmt, write, &mut next);
        observe(stmt, write, &current, &next);
        current = next;
    }
    current
}

/// Trust (merge 2026-10-14): the state right after statement `k` of `block` (which is
/// `func.body.blocks[pos]`), from `entry`, by the ONE lockstep walk
/// ([`transfer_statements_observed`]). Read by the environment's def-site narrowing
/// (`narrow_single_assignments_to_their_def`), which must not see a state the
/// fixpoint's own walk would not have produced. `None` when `block` has no statement
/// `k`.
pub(super) fn state_after_statement(
    havoc: &mut CallHavoc<'_>,
    pos: usize,
    block: &BasicBlock,
    entry: IntervalDomain,
    k: usize,
) -> Option<IntervalDomain> {
    if k >= block.stmts.len() {
        return None;
    }
    let func = havoc.func;
    let writes = havoc.stmt_writes(pos, block);
    let mut pending = writes.iter().peekable();
    let mut current = entry;
    for (idx, stmt) in block.stmts.iter().enumerate().take(k + 1) {
        let write = pending.next_if(|(at, _)| *at == idx).map(|(_, write)| write);
        transfer_one_statement_in_place(func, block, idx, stmt, write, &mut current);
    }
    Some(current)
}

/// Trust (2026-10-09, trust-interval-drop-havoc, independent review, probe round
/// `rv-r4`): widen the whole-function environment `env` so that it bounds every value
/// a name holds BETWEEN two statements of a block, not only at block entries.
///
/// WHY. `merged_interval_environment` joined the fixpoint's block ENTRY states, and
/// the discharge reads a versioned name (`b#s0_1`: `b` as one particular statement
/// left it) through that environment's entry for the bare `b` (`interval_for_var`).
/// That is sound only if the entry bounds `b` at every point where `b` is a value,
/// and a join of entry states does not: a value written and overwritten inside ONE
/// block is no block's entry state. MEASURED on main and on this branch before the
/// change (review probes `e02`, `e03`; verify-on build against a verify-off run):
///
/// ```text
/// let mut a = 1u32; let mut b = 0u32;
/// let t = a; a = b; b = t;
/// k / a                      // a == 0: panics on every run
/// ```
///
/// is one block up to the division's `Assert`. Its entry state says nothing about
/// `a` and `b` (not yet values there), every later block says `b ∈ [1, 1]`, so the
/// environment said `b ∈ [1, 1]`; the obligation's own `Eq(_5, b#s0_1)` (the copy of
/// `b` while it was 0, `_5 ∈ [0, 0]`) evaluated FALSE, the violation was "unreachable",
/// the division by zero was discharged at generation, ay never saw it, and the build
/// passed. Not the entry block's privilege: wherever every name involved is bounded
/// by the environment (the locals the entry block defines, a parameter under a
/// `requires`), a value that lives only inside a later block is missed the same way.
///
/// WHAT. For every statement of every reachable block, walked from the block's
/// fixpoint entry state with the fixpoint's own transfer
/// ([`transfer_statements_observed`], the run's own havoc index), join into `env`:
///
/// * the value the statement leaves in its DESTINATION;
/// * "unknown" for every name the statement writes beyond its destination
///   ([`StmtWrite::writes`]), whether or not the state tracked it;
/// * the new value of every other name whose interval the transfer changed (a name
///   the destination rebinds is forgotten, so it joins as unknown).
///
/// An UNKNOWN value of a local is its type's range, not Top
/// ([`EnvironmentJoin::join`]): the state says Top of `_3 = copy _2.0` because it does
/// not track the field, and the `u32` `_3` is in `[0, u32::MAX]` all the same. That is
/// the bound the block-entry join already carries for a local nothing has written, so
/// this walk never makes the environment say less about a local than its type does.
/// A value unbounded on ONE side joins as its part within the type's range, and one
/// with a finite bound past the type as the whole range ([`as_value_of_type`]).
///
/// THE INVARIANT this buys, which is the one `interval_for_var` states: for every
/// reachable block, every statement `k` of it and every name `n` in `env`, the state
/// after statement `k` (read as a value of `n`'s type) is within `env` at `n` — except
/// for a local that is not yet a value there (a non-argument local of the ENTRY block before that block's first
/// write of it; `merged_interval_environment` leaves its entry contribution out for
/// the same reason). By induction over a block: at its entry the block-entry join
/// gives it; a statement either leaves a name's interval as it was, or changes it,
/// or makes the name a value for the first time by writing it, and the three bullets
/// are those cases. A terminator needs a step of its own only where it unwinds into a
/// cleanup block and returns nowhere else (the last step of the walk): on its normal
/// edges what it writes is havoced by [`transfer_terminator`] and is the entry state
/// of every successor, and the only edges that narrow (`SwitchInt`, the negation
/// check) narrow a value some statement or entry state already contributed. Re-derived under `cfg(test)` from the
/// formula path's write oracle by [`assert_environment_bounds_every_statement_point`].
///
/// NOT COVERED, and not claimed: a write made INSIDE a cleanup block. The fixpoint does
/// not follow unwind edges, so a cleanup block has no state to walk from. Cleanup code
/// is drop elaboration: it writes fresh temporaries (a reference for a drop call, a
/// discriminant read), which no reachable block bounds below their type range.
///
/// SOUND: every step is a join into `env`, which can only widen it. It can turn a
/// discharge into a dispatch and never create one.
///
/// THE COST. A name written twice in one block is now bounded by the hull of both
/// values where it was bounded by the last one. One poll of the ambient budget per
/// block, as every other walk of the fixpoint ([`fixpoint_budget_tripped`]); a trip
/// answers the refusal, an environment that bounds nothing.
pub(super) fn join_statement_values(
    havoc: &mut CallHavoc<'_>,
    fixpoint: &FixpointResult,
    env: &mut IntervalDomain,
) {
    // PERF-COMPILER-VCGEN-770: return before allocating `type_ranges` when the
    // environment is already unreachable or empty (every name is already Top).
    if env.is_unreachable || env.vars.is_empty() {
        return;
    }
    let func = havoc.func;
    // PERF-COMPILER-VCGEN-770: `EnvironmentJoin` only ever widens or removes keys
    // already present in `env.vars` (never inserts new keys), so `type_ranges` only
    // needs entries for locals whose formula name is currently bounded in `env.vars`.
    let mut type_ranges: FxHashMap<String, Interval> =
        FxHashMap::with_capacity_and_hasher(env.vars.len(), Default::default());
    for local in &func.body.locals {
        if let Some(range) = type_to_interval(&local.ty) {
            let name = crate::local_var_name(func, local);
            if env.vars.contains_key(&name) {
                type_ranges.insert(name, range);
            }
        }
    }
    let mut join = EnvironmentJoin { env, type_ranges };
    let env = &mut join;
    for (pos, block) in func.body.blocks.iter().enumerate() {
        // Nothing left to widen: every remaining name is already unbounded.
        if env.env.vars.is_empty() {
            return;
        }
        if fixpoint_budget_tripped() {
            env.env.vars.clear();
            return;
        }
        let Some(entry) = fixpoint.block_states.get(&block.id) else { continue };
        if entry.is_unreachable {
            continue;
        }
        if !block.stmts.is_empty() {
            let _ = transfer_statements_observed(
                havoc,
                pos,
                block,
                entry.clone(),
                |stmt, write, before, after| {
                    if let Statement::Assign { place, .. } = stmt {
                        let dest = crate::place_to_var_name(func, place);
                        env.join(&dest, after.get(&dest));
                    }
                    if let Some(write) = write {
                        env.forget_where(|name| write.writes(name));
                    }
                    for_each_changed_interval(before, after, |name, now| {
                        env.join(name, now);
                    });
                },
            );
        }
        // The one terminator write no block-entry state carries: a terminator that
        // unwinds into a CLEANUP block and has no normal successor. The fixpoint
        // propagates along the normal successors only (`terminator_successors`), so
        // what a diverging callee wrote through a `&mut c` before it unwound is the
        // entry state of no block, and the cleanup path runs after it. (With a normal
        // successor the havoced names are absent from that successor's entry state,
        // which the block-entry join has already read.)
        if block.terminator.unwind_cleanup_target().is_some()
            && !terminator_has_successors(&block.terminator)
            && let Some(kill) = havoc.of(pos, block)
        {
            env.forget_where(|name| kill.rebinds(name));
        }
    }
}

/// What the interval `value` the state holds for a local says about the VALUE the
/// local holds, given the range `range` of the local's integer type. A value of an
/// integer type is within the type's range wherever it is a value at all (the fact
/// [`type_aware_initial_state`] seeds and `narrow_place_operand` meets with), so the
/// answer is always within `range`:
///
/// * `value` within the range: `value`;
/// * `value` outside the range ONLY on a side the domain leaves unbounded
///   (`i128::MIN`, `i128::MAX`): the part of it within the range. An unbounded side
///   is the domain's spelling of "nothing known on this side": Top has two, and one
///   is what a one-sided fact leaves. `requires p.0 <= 3` gives the field `p.0` the
///   interval `[i128::MIN, 3]` (a projection has no seeded type range), `t = copy
///   p.0` gives the `u32` `t` the same, and what that says of `t` is `[0, 3]`;
/// * a FINITE bound outside the range, or nothing in common with the range: the
///   whole range. A finite bound past the type is a mathematical result the machine
///   value need not have (the domain's `Shl` is not truncated to the type), and such
///   an interval is not taken as evidence about the machine value on either side.
///
/// WHY THE MIDDLE CASE IS NOT THE WHOLE RANGE (2026-10-11, probe round `ep-r3`).
/// It was, and that made the environment say LESS than the block-entry join it
/// extends: with `requires p.0 <= 3`, `let big = p.0 >= 10; p.0 = 0; if big { .. }`
/// had the copy of `p.0` bounded by `[i128::MIN, 3]` at every block entry, the
/// statement walk joined the whole `u32` range on top, the dead branch's obligation
/// was dispatched, and the solver refuted a correct program (the formula has no tie
/// from the copy to the field once the field is stored to; the interval was what
/// decided it). SOUND on the footing the block-entry join already stands on: that
/// join takes a state's interval as a bound on the machine value, and so does this
/// case; the type's range bounds the machine value too, so the two together do.
fn as_value_of_type(value: Interval, range: &Interval) -> Interval {
    if value.leq(range) {
        return value;
    }
    let finite_below = value.lo != i128::MIN && value.lo < range.lo;
    let finite_above = value.hi != i128::MAX && value.hi > range.hi;
    if finite_below || finite_above {
        return *range;
    }
    let within = value.meet(range);
    if within.is_bottom() { *range } else { within }
}

/// Merge 2026-10-14: whether [`as_value_of_type`] takes `value` as EVIDENCE about a
/// value of the type with range `range`: it is not empty, has no FINITE bound past the
/// range, and shares a value with it. A side the domain leaves unbounded (`i128::MIN`,
/// `i128::MAX`) says nothing and is no evidence against it. The environment's def-site
/// narrowing (`narrow_single_assignments_to_their_def`) meets with a def-site value only
/// under this, so it never re-admits what the statement-point join discards.
pub(super) fn value_is_evidence_of_type(value: &Interval, range: &Interval) -> bool {
    let finite_below = value.lo != i128::MIN && value.lo < range.lo;
    let finite_above = value.hi != i128::MAX && value.hi > range.hi;
    !value.is_bottom() && !finite_below && !finite_above && !value.meet(range).is_bottom()
}

/// What [`join_statement_values`] joins into: the environment, and every local's type
/// range under the name the transfers write it by.
struct EnvironmentJoin<'e> {
    env: &'e mut IntervalDomain,
    /// [`type_to_interval`] of each local it is defined for, keyed by
    /// `crate::local_var_name` — the interval [`type_aware_initial_state`] seeds.
    type_ranges: FxHashMap<String, Interval>,
}

impl EnvironmentJoin<'_> {
    /// `env[name] = env[name] ⊔ value`. A name `env` does not carry is already Top.
    ///
    /// The `value` of a local joins as what it says about a value of the local's TYPE
    /// ([`as_value_of_type`]): itself when it is within the type's range, and never
    /// less than the type says. Joining the state's Top for `_3 = copy _2.0` (an
    /// operand it does not track) would erase the type-range bound the block-entry
    /// join keeps for the same local.
    fn join(&mut self, name: &str, value: Interval) {
        let Some(bound) = self.env.vars.get_mut(name) else { return };
        let value = match self.type_ranges.get(name) {
            Some(range) => as_value_of_type(value, range),
            None => value,
        };
        let joined = bound.join(&value);
        if joined == Interval::TOP {
            self.env.vars.remove(name);
        } else {
            *bound = joined;
        }
    }

    /// Every name the environment bounds that a statement or terminator `writes`
    /// holds an unknown value after it, whether or not the state tracked the name.
    fn forget_where(&mut self, writes: impl Fn(&str) -> bool) {
        let type_ranges = &self.type_ranges;
        self.env.vars.retain(|name, bound| {
            if !writes(name) {
                return true;
            }
            let value = match type_ranges.get(name.as_str()) {
                Some(range) => as_value_of_type(Interval::TOP, range),
                None => Interval::TOP,
            };
            let joined = bound.join(&value);
            if joined == Interval::TOP {
                false
            } else {
                *bound = joined;
                true
            }
        });
    }
}

/// Call `changed(name, interval after)` for every name whose interval differs
/// between two states of one walk (an absent name is Top on either side). Both maps
/// are ordered, so this is one merge walk and no lookup.
fn for_each_changed_interval(
    before: &IntervalDomain,
    after: &IntervalDomain,
    mut changed: impl FnMut(&str, Interval),
) {
    use std::cmp::Ordering;
    let mut was = before.vars.iter().peekable();
    let mut now = after.vars.iter().peekable();
    loop {
        let order = match (was.peek(), now.peek()) {
            (None, None) => return,
            (Some(_), None) => Ordering::Less,
            (None, Some(_)) => Ordering::Greater,
            (Some((a, _)), Some((b, _))) => a.cmp(b),
        };
        match order {
            // Tracked before, forgotten now.
            Ordering::Less => {
                if let Some((name, old)) = was.next()
                    && *old != Interval::TOP
                {
                    changed(name, Interval::TOP);
                }
            }
            // Untracked before, set now.
            Ordering::Greater => {
                if let Some((name, new)) = now.next()
                    && *new != Interval::TOP
                {
                    changed(name, *new);
                }
            }
            Ordering::Equal => {
                if let (Some((name, old)), Some((_, new))) = (was.next(), now.next())
                    && old != new
                {
                    changed(name, *new);
                }
            }
        }
    }
}

/// The invariant [`join_statement_values`] establishes, re-derived the slow way from
/// the FORMULA PATH's write oracle and asserted for every environment a test computes.
///
/// Each reachable block is walked from its fixpoint entry state. A statement is
/// applied as [`transfer_function`] and then forgets exactly the names
/// `stmt_writes_name` says it writes (its destination excepted) — the oracle, not this
/// lane's [`StmtWrite`] classification, so a statement the classification misses is
/// seen here as a state the environment does not bound. After every statement, every
/// name the environment bounds must hold the state's interval (read as a value of the
/// local's type: [`as_value_of_type`]). The one exception is
/// the one `merged_interval_environment` makes: a non-argument local of the ENTRY
/// block before that block first writes it — and "writes it" is asked of the oracle
/// too (`stmt_writes_name`, or the statement's own destination), not of the join.
#[cfg(test)]
pub(super) fn assert_environment_bounds_every_statement_point(
    func: &VerifiableFunction,
    fixpoint: &FixpointResult,
    env: &IntervalDomain,
    entry_id: Option<BlockId>,
    undefined_at_entry: &FxHashSet<String>,
) {
    if env.is_unreachable || env.vars.is_empty() {
        return;
    }
    // An EMPTY interval is the one bound nothing can hold, and `interval_domain_to_formula`
    // spells an environment that has one as `false`: every obligation it is conjoined
    // onto is then unsatisfiable, i.e. "proved". Block entries alone produced exactly
    // that (`let y = i32::MIN; -y`: the negation check's success edge leaves its operand
    // no value, and that edge was the only state joined), and main proved the negation
    // of `MIN`. A name the environment bounds has a value somewhere.
    for (name, bound) in &env.vars {
        assert!(
            !bound.is_bottom(),
            "the whole-function environment of `{}` bounds `{name}` by the EMPTY interval: as a \
             hypothesis that is `false`, and every obligation of the function is proved by it",
            func.name
        );
    }
    for block in &func.body.blocks {
        let Some(entry) = fixpoint.block_states.get(&block.id) else { continue };
        if entry.is_unreachable {
            continue;
        }
        let is_entry = Some(block.id) == entry_id;
        let type_range = |name: &str| {
            func.body
                .locals
                .iter()
                .find(|local| crate::local_var_name(func, local) == name)
                .and_then(|local| type_to_interval(&local.ty))
        };
        let mut written: FxHashSet<&str> = FxHashSet::default();
        let mut state = entry.clone();
        let bounded = |state: &IntervalDomain,
                       written: &FxHashSet<&str>,
                       at: &dyn std::fmt::Display| {
            for (name, bound) in &env.vars {
                if is_entry && undefined_at_entry.contains(name) && !written.contains(name.as_str())
                {
                    continue;
                }
                let held = match type_range(name) {
                    Some(range) => as_value_of_type(state.get(name), &range),
                    None => state.get(name),
                };
                assert!(
                    held.leq(bound),
                    "the whole-function environment bounds `{name}` by {bound:?}, but it holds \
                     {held:?} {at} of bb{} in `{}`: a versioned read of `{name}` there would be \
                     discharged against a value it does not have",
                    block.id.0,
                    func.name
                );
            }
        };
        bounded(&state, &written, &"at the entry");
        for (k, stmt) in block.stmts.iter().enumerate() {
            state = transfer_function(stmt, func, &state);
            let dest = match stmt {
                Statement::Assign { place, .. } => Some(crate::place_to_var_name(func, place)),
                _ => None,
            };
            if !state.is_unreachable {
                state.vars.retain(|name, _| {
                    dest.as_deref() == Some(name.as_str())
                        || stmt_spares_frame_storage(func, stmt, name)
                        || !crate::generate::stmt_writes_name(func, block, k, name)
                });
            }
            if is_entry {
                for name in undefined_at_entry {
                    if dest.as_deref() == Some(name.as_str())
                        || (crate::generate::stmt_writes_name(func, block, k, name)
                            && !stmt_spares_frame_storage(func, stmt, name))
                    {
                        written.insert(name);
                    }
                }
            }
            bounded(&state, &written, &format_args!("after statement {k}"));
        }
        // A terminator that unwinds into a cleanup block: every name the FORMULA path
        // says it writes holds an unknown value on that edge.
        if block.terminator.unwind_cleanup_target().is_some() {
            let writes = crate::generate::terminator_def_names(func, block);
            for (name, bound) in &env.vars {
                if !writes.iter().any(|w| crate::generate::write_rebinds(w, name)) {
                    continue;
                }
                let unknown = type_range(name).unwrap_or(Interval::TOP);
                assert!(
                    unknown.leq(bound),
                    "the whole-function environment bounds `{name}` by {bound:?} although the \
                     terminator of bb{} in `{}` writes it before unwinding into a cleanup block",
                    block.id.0,
                    func.name
                );
            }
        }
    }
}

impl<'f> CallHavoc<'f> {
    fn new(func: &'f VerifiableFunction) -> Self {
        let n = func.body.blocks.len();
        CallHavoc {
            func,
            shared: SharedHavoc::default(),
            by_block: (0..n).map(|_| None).collect(),
            stmts_by_block: vec![None; n],
        }
    }

    /// The statements of `block` (which is `func.body.blocks[pos]`) that write more
    /// than their own destination, derived at the block's first visit of the run.
    fn stmt_writes(&mut self, pos: usize, block: &BasicBlock) -> BlockStmtWrites {
        let (func, shared) = (self.func, &mut self.shared);
        let writes = self.stmts_by_block[pos].get_or_insert_with(|| {
            let mut out = Vec::new();
            for (k, stmt) in block.stmts.iter().enumerate() {
                if let Some(write) = StmtWrite::of(func, stmt, shared) {
                    out.push((k, write));
                }
            }
            out.into()
        });
        std::rc::Rc::clone(writes)
    }

    /// The havoc of `block`, which is `func.body.blocks[pos]`.
    fn of(&mut self, pos: usize, block: &BasicBlock) -> Option<&BlockHavoc> {
        let (func, shared) = (self.func, &mut self.shared);
        let slot = &*self.by_block[pos].get_or_insert_with(|| BlockHavoc::of(func, block, shared));
        // The purity this cache rests on, re-derived at every visit under `cfg(test)`:
        // the list a visit would have derived is the list the first visit derived.
        // Trust (2026-10-08, trust-interval-drop-havoc): for EVERY terminator, not only
        // the ones [`terminator_havocs_intervals`] admits — so a terminator the
        // predicate skips while the formula path gives it a write set (the `Drop` gap)
        // fails here, in every test that runs the fixpoint: the LOCKSTEP of the two
        // lanes is checked, not only the cache.
        #[cfg(test)]
        if crate::generate::differential_enabled() {
            let now = crate::generate::terminator_def_names(self.func, block);
            let cached: &[String] = slot.as_ref().map_or(&[], |h| &h.names);
            assert_eq!(
                cached,
                &now[..],
                "the interval havoc of bb{} is not the formula path's write set (a terminator \
                 the interval transfer skips, or a list that changed within a run)",
                block.id.0
            );
        }
        slot.as_ref()
    }
}

/// One havocking block's havoc, indexed: the shared index when the block havocs a
/// list other blocks havoc too (`H` unrefined, or the escape arm's kept list), and
/// the block's own names (its extras, or its whole refined list).
struct BlockHavoc {
    shared: Option<std::rc::Rc<crate::generate::rebind_index::RebindSet>>,
    own: crate::generate::rebind_index::RebindSet,
    /// The flattened list the scan this replaced walked, for the `cfg(test)`
    /// cross-checks.
    #[cfg(test)]
    names: Vec<String>,
}

/// `names` as a [`RebindSet`](crate::generate::rebind_index::RebindSet).
fn index_havoc_names(names: &[String]) -> std::rc::Rc<crate::generate::rebind_index::RebindSet> {
    let mut set = crate::generate::rebind_index::RebindSet::default();
    for name in names {
        set.insert(name);
    }
    std::rc::Rc::new(set)
}

impl BlockHavoc {
    /// `None` exactly when the scan this replaced did nothing: the terminator is not
    /// one the interval transfer havocs at ([`terminator_havocs_intervals`]), or its
    /// flattened havoc list is empty.
    fn of(
        func: &VerifiableFunction,
        block: &BasicBlock,
        shared_indexes: &mut SharedHavoc,
    ) -> Option<BlockHavoc> {
        use crate::generate::rebind_index::RebindSet;
        use crate::generate::{TermExtra, TermHavoc};
        if !terminator_havocs_intervals(&block.terminator) {
            return None;
        }
        crate::fn_memo::count_interval_havoc_sets();
        let defs = crate::generate::terminator_def_names_structured(func, block);
        #[cfg(test)]
        let names = defs.clone().flatten(func);
        let mut own = RebindSet::default();
        let mut own_names = 0usize;
        let shared = match &defs.havoc {
            TermHavoc::None => None,
            TermHavoc::Function => shared_indexes.function_index(func),
            TermHavoc::Refined(delta) => {
                for name in delta.flatten(&crate::generate::function_havoc_names(func)) {
                    own.insert(&name);
                    own_names += 1;
                }
                None
            }
            // Trust (2026-10-08, landing on CALL-HAVOC-ESCAPE-2 / TINV-18): the escape
            // arm havocs `kept` — the part of `H` a callee reaches without an argument
            // — and nothing of `dropped`; `TermDefs::flatten` reads `kept` and so does
            // this index.
            TermHavoc::Escape(escape) => {
                if escape.kept.is_empty() {
                    None
                } else {
                    let reused = shared_indexes.escape.as_ref().and_then(|(of, set)| {
                        std::rc::Rc::ptr_eq(of, escape).then(|| std::rc::Rc::clone(set))
                    });
                    let set = match reused {
                        Some(set) => set,
                        None => {
                            crate::fn_memo::count_interval_function_havoc_indexes();
                            let set = index_havoc_names(&escape.kept);
                            shared_indexes.escape =
                                Some((std::rc::Rc::clone(escape), std::rc::Rc::clone(&set)));
                            set
                        }
                    };
                    Some(set)
                }
            }
        };
        for extra in &defs.extra {
            let (TermExtra::Push(name) | TermExtra::PushIfAbsent(name)) = extra;
            own.insert(name);
            own_names += 1;
        }
        #[cfg(test)]
        assert_eq!(
            names.is_empty(),
            shared.is_none() && own_names == 0,
            "the indexed call havoc of bb{} and its flattened list disagree on emptiness",
            block.id.0
        );
        if shared.is_none() && own_names == 0 {
            return None;
        }
        Some(BlockHavoc {
            shared,
            own,
            #[cfg(test)]
            names,
        })
    }

    /// Some havoc name `h` has `write_rebinds(h, name)`.
    fn rebinds(&self, name: &str) -> bool {
        let hit = self.own.any_rebinder(name)
            || self.shared.as_ref().is_some_and(|set| set.any_rebinder(name));
        #[cfg(test)]
        if crate::generate::differential_enabled() {
            assert_eq!(
                hit,
                self.names.iter().any(|h| crate::generate::write_rebinds(h, name)),
                "the indexed call havoc disagrees with the write_rebinds scan on `{name}`"
            );
        }
        hit
    }
}

/// Trust (2026-10-02, trust-fixpoint-deadline): one poll of the ambient
/// per-function verification budget per unit of interval-fixpoint work — a worklist
/// pop of the ascending phase, a block of a narrowing pass, a block of a repair round.
///
/// WHY. The fixpoint was bounded only by its own iteration cap (`blocks * 20 + 100`
/// pops, then a bounded number of narrowing passes and repair rounds) and polled
/// nothing, so a body whose units are expensive ran on past the function's deadline
/// — 226 s past it on aterm-census `run_lock_order_census` (see [`CallHavoc`]) —
/// computing an answer the compiler then discarded (its post-generation and
/// post-construction checkpoints read the same deadline). The same class of defect
/// the referent fold had (census-vcgen-hang); this is the same cure.
///
/// THE POLL. `budget_exhausted` charges one step — the deterministic half: the
/// fixpoint's unit count is now part of the function's step count, exactly as the
/// referent fold's walk steps are — and reads the clock every `WALL_POLL_INTERVAL`
/// steps. `exhausted_readonly` additionally reads the clock NOW, and answers `true`
/// for a trip latched before this run began. That second read is the one difference
/// from the referent fold's poll, and it is deliberate: one unit here is a whole
/// block of statement transfers over every tracked name (milliseconds on a body with
/// thousands of locals), so a clock read only every 4096 units could overshoot the
/// deadline by minutes; an `Instant::now()` per unit is noise beside the unit.
///
/// A TRIP REFUSES ([`refuse_everything`]): every block's state becomes Top and
/// reachable — the interval domain's opaque answer, which bounds no variable,
/// discharges nothing and adds no hypothesis to any obligation. Nothing memoizes a
/// fixpoint result, so a refusal cannot outlive the run that produced it.
///
/// A unit whose poll passes is counted (`AnalysisMemoStats::interval_fixpoint_units`)
/// — the deterministic measure the budget tests pin.
fn fixpoint_budget_tripped() -> bool {
    let tripped = trust_types::verify_budget::budget_exhausted()
        || trust_types::verify_budget::exhausted_readonly();
    if !tripped {
        crate::fn_memo::count_interval_fixpoint_units();
    }
    tripped
}

/// The fixpoint's REFUSAL: every block Top and reachable — the answer that claims
/// nothing. SOUND for every consumer: Top contains every value, and no block is
/// claimed unreachable, so no obligation is discharged or strengthened by it.
fn refuse_everything(result: &mut FixpointResult) {
    for state in result.block_states.values_mut() {
        state.vars.clear();
        state.is_unreachable = false;
    }
}

/// Trust (2026-10-16, refutation scope S2): every block's entry state after at
/// most `sweeps` join-only passes over the body in block order, from the
/// type-aware initial state — NO widening and no narrowing, so a loop header's
/// state covers the values its loop-carried locals take within the first
/// iterations only (a pass carries a value once around each back edge), not
/// every iteration. It is an over-approximation of SHALLOW executions, never a
/// loop invariant: no consumer may read it as one, and none may prove from it.
/// The generic refutation scope reads it to ask whether a solver model's
/// loop-header value is one a shallow execution could hold.
///
/// When the walk has not settled after `sweeps` passes, each bound that still
/// moved on the LAST pass is carried on linearly for `horizon` more passes (the
/// last pass's step, `horizon` times over, saturating), so a counter that needs a
/// few hundred (a `u8` incremented from 0), or `2^32` (a `u32`), iterations to
/// reach a value still counts as shallow while one that needs `2^62` (a `usize`
/// stepped by 3) does not. The extrapolated state only ever GROWS the walk's, and a larger state only
/// keeps a refutation the scope would otherwise withhold.
///
/// `None` when the verify budget is spent (the walk would claim nothing).
pub(crate) fn shallow_ascent(
    func: &VerifiableFunction,
    sweeps: usize,
    horizon: i128,
) -> Option<FxHashMap<BlockId, IntervalDomain>> {
    let budget_spent = || {
        trust_types::verify_budget::budget_exhausted()
            || trust_types::verify_budget::exhausted_readonly()
    };
    // The summary-only precision steps (a checked result field `_k.0`, read as the
    // mathematical result past its overflow assert): without them a `+=` in debug
    // MIR loses its counter at the first back edge. They may settle a FIXPOINT
    // below the truth ([`SummaryPrecision`]); this walk is no fixpoint and proves
    // nothing, and the only effect of a smaller state is to keep a refutation.
    let _precision = SummaryPrecision::enter(true);
    let mut states: FxHashMap<BlockId, IntervalDomain> =
        FxHashMap::with_capacity_and_hasher(func.body.blocks.len(), Default::default());
    for block in &func.body.blocks {
        states.insert(block.id, IntervalDomain::bottom());
    }
    if let Some(first) = func.body.blocks.first() {
        states.insert(first.id, type_aware_initial_state(func));
    }
    let mut havoc = CallHavoc::new(func);
    let mut settled = false;
    let mut before_last: Option<FxHashMap<BlockId, IntervalDomain>> = None;
    for sweep in 0..sweeps {
        if budget_spent() {
            return None;
        }
        if sweep + 1 == sweeps {
            before_last = Some(states.clone());
        }
        let mut changed = false;
        for (pos, block) in func.body.blocks.iter().enumerate() {
            let entry = states.get(&block.id).cloned().unwrap_or_else(IntervalDomain::bottom);
            if entry.is_unreachable {
                continue;
            }
            let current = transfer_statements(&mut havoc, pos, block, entry);
            let current = transfer_terminator(&mut havoc, pos, block, current);
            for_each_successor_state_owned(&block.terminator, func, block, current, |succ, state| {
                let did_change = if let Some(old) = states.get_mut(&succ) {
                    old.join_owned_in_place(state)
                } else {
                    let mut fresh = IntervalDomain::bottom();
                    let c = fresh.join_owned_in_place(state);
                    if c {
                        states.insert(succ, fresh);
                    }
                    c
                };
                if did_change {
                    changed = true;
                }
            });
        }
        if !changed {
            settled = true;
            break;
        }
    }
    if budget_spent() {
        return None;
    }
    if !settled && let Some(before) = before_last {
        extrapolate_shallow(&mut states, &before, horizon);
    }
    Some(states)
}

/// [`shallow_ascent`]'s horizon: every bound of `states` that moved since
/// `before` (the state one pass earlier) moves on by its last step `horizon`
/// more times, saturating at the interval's ends. A block `before` had not
/// reached keeps its state: it has no step to carry on.
fn extrapolate_shallow(
    states: &mut FxHashMap<BlockId, IntervalDomain>,
    before: &FxHashMap<BlockId, IntervalDomain>,
    horizon: i128,
) {
    for (block, state) in states.iter_mut() {
        let Some(prev) = before.get(block) else { continue };
        if prev.is_unreachable || state.is_unreachable {
            continue;
        }
        for (name, interval) in state.vars.iter_mut() {
            if interval.lo > interval.hi {
                continue;
            }
            let Some(old) = prev.vars.get(name) else { continue };
            if old.lo > old.hi {
                continue;
            }
            if interval.hi > old.hi {
                let step = interval.hi.saturating_sub(old.hi);
                interval.hi = interval.hi.saturating_add(step.saturating_mul(horizon));
            }
            if interval.lo < old.lo {
                let step = old.lo.saturating_sub(interval.lo);
                interval.lo = interval.lo.saturating_sub(step.saturating_mul(horizon));
            }
        }
    }
}

/// Each block's position in `func.body.blocks`, by id. The FIRST block with an id
/// wins, which is the block the ascending phase's `find` by id used to return.
enum BlockPositions {
    Identity(usize),
    Map(FxHashMap<BlockId, usize>),
}

impl BlockPositions {
    #[inline]
    fn get(&self, id: &BlockId) -> Option<usize> {
        match self {
            BlockPositions::Identity(len) => (id.0 < *len).then_some(id.0),
            BlockPositions::Map(map) => map.get(id).copied(),
        }
    }
}

fn block_positions(func: &VerifiableFunction) -> BlockPositions {
    // PERF-COMPILER-VCGEN-693: canonical dense `BlockId`s (`b.id.0 == pos`) need
    // zero heap allocation and resolve in O(1) by bounds-checked index.
    if func.body.blocks.iter().enumerate().all(|(pos, block)| block.id.0 == pos) {
        return BlockPositions::Identity(func.body.blocks.len());
    }
    let mut positions =
        FxHashMap::with_capacity_and_hasher(func.body.blocks.len(), Default::default());
    for (pos, block) in func.body.blocks.iter().enumerate() {
        positions.entry(block.id).or_insert(pos);
    }
    BlockPositions::Map(positions)
}

/// The wrapping clamp for a bare (plain-MIR, therefore wrapping) integer
/// binop's destination — see the call site in [`transfer_function`] for the
/// soundness argument. Bottom passes through (unreachable stays unreachable);
/// a math interval contained in the destination's representable range is kept
/// EXACTLY (no input can wrap, so machine == math); anything else becomes the
/// full type range, or Top when the destination's integer range is unknown
/// (non-integer/u128 destinations — `type_bounds` refuses those).
fn clamp_bare_binop_to_dest_range(
    math: Interval,
    func: &VerifiableFunction,
    place: &Place,
) -> Interval {
    if math.is_bottom() {
        return math;
    }
    let range = crate::place_ty_cow(func, place).as_deref().and_then(|ty| match ty {
        // Faithful pointer-width spelling: the pinned 64-bit target
        // (`Ty::int_width`'s own convention). Kept local to this clamp so
        // `type_bounds`' authority surface in the discharge lane is unchanged.
        Ty::PtrSizedInt { signed } => {
            super::discharge::type_bounds(&Ty::Int { width: 64, signed: *signed })
        }
        other => super::discharge::type_bounds(other),
    });
    let Some((lo, hi)) = range else {
        return Interval::TOP;
    };
    if math.lo >= lo && math.hi <= hi { math } else { Interval::new(lo, hi) }
}

/// Evaluate an rvalue to an interval.
/// Whether `op` reads a `u128`: a place of that type, or a constant of that width.
/// See the `operand_to_interval` and `eval_rvalue` arms that consult it.
fn operand_reads_u128(func: &VerifiableFunction, op: &Operand) -> bool {
    match op {
        Operand::Copy(_) | Operand::Move(_) => matches!(
            crate::operand_ty_cow(func, op).as_deref(),
            Some(Ty::Int { width: 128, signed: false })
        ),
        Operand::Constant(ConstValue::Uint(_, 128)) => true,
        _ => false,
    }
}

fn eval_rvalue(rvalue: &Rvalue, func: &VerifiableFunction, state: &IntervalDomain) -> Interval {
    match rvalue {
        Rvalue::Use(op) => operand_to_interval(op, func, state),
        Rvalue::BinaryOp(op, lhs, rhs) | Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
            // Trust (2026-10-10, review round 115): the interval arithmetic reads an
            // unknown operand as `[i128::MIN, i128::MAX]`, a superset of every value
            // of every other integer type but not of a `u128`'s: `(x >> 121) as i32`
            // over `x: u128` was `[-64, 63]` (real `0..=127`), and the same for `/`
            // and `%` by large literals. No operation over a `u128` is evaluated.
            if operand_reads_u128(func, lhs) || operand_reads_u128(func, rhs) {
                return Interval::TOP;
            }
            let a = operand_to_interval(lhs, func, state);
            let mut b = operand_to_interval(rhs, func, state);
            // Trust (2026-09-30): a MIR shift uses the amount MODULO the operand's
            // width (and a checked build panics before any larger one), so an amount
            // interval that is not inside `[0, width - 1]` is replaced by it. The
            // interval shift below reads a shift literally, and an amount of 64 on a
            // `u64` would otherwise mean "shift everything out" where the machine
            // shifts by 0.
            if matches!(op, BinOp::Shl | BinOp::Shr) {
                // The width comes from a PLACE operand's declared type, or from a
                // constant that carries its own width. A bare signed constant carries
                // none (it renders at i64): its amount is kept only when it is below 8,
                // the narrowest width, and is otherwise any amount a mask can leave,
                // `[0, 127]` (rounds 11 and 12: `0x4000_0000i32 >> k` with `k` in
                // `[32, 33]` was read as zero, where the machine shifts by 0 or 1).
                let width = match lhs {
                    Operand::Copy(_) | Operand::Move(_) => {
                        match crate::operand_ty_cow(func, lhs).as_deref() {
                            Some(Ty::Int { width, .. }) => Some((i128::from(*width), true)),
                            _ => None,
                        }
                    }
                    Operand::Constant(ConstValue::Uint(_, width)) => {
                        Some((i128::from(*width), true))
                    }
                    _ => Some((8, false)),
                };
                match width {
                    Some((w, _)) if !b.is_bottom() && b.lo >= 0 && b.hi < w => {}
                    Some((w, true)) => b = Interval::new(0, w - 1),
                    Some((_, false)) => b = Interval::new(0, 127),
                    None => return Interval::TOP,
                }
            }
            match op {
                BinOp::Add => interval_add(&a, &b),
                BinOp::Sub => interval_sub(&a, &b),
                BinOp::Mul => interval_mul(&a, &b),
                BinOp::Div => interval_div(&a, &b),
                BinOp::Rem => interval_rem(&a, &b),
                BinOp::Shr => interval_shr(&a, &b),
                BinOp::Shl => interval_shl(&a, &b),
                BinOp::BitAnd => interval_bitand(&a, &b),
                BinOp::BitOr => interval_bitor(&a, &b),
                // Comparisons produce boolean [0, 1].
                BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    Interval::new(0, 1)
                }
                // Trust (2026-09-28): a three-way compare yields an `Ordering`, whose
                // discriminants are `-1`, `0` and `1`. It was `[0, 1]`, which excluded
                // `Less`, the same class as the negative-discriminant fact
                // (`discriminant_read_hull`).
                BinOp::Cmp => Interval::new(-1, 1),
                _ => Interval::TOP,
            }
        }
        Rvalue::UnaryOp(UnOp::Neg, op) => {
            let a = operand_to_interval(op, func, state);
            if a.is_bottom() {
                Interval::BOTTOM
            } else {
                let lo = a.hi.checked_neg();
                let hi = a.lo.checked_neg();
                match (lo, hi) {
                    (Some(lo), Some(hi)) => Interval { lo, hi },
                    _ => Interval::TOP,
                }
            }
        }
        Rvalue::Len(_) => Interval::new(0, i128::MAX),
        // Trust (2026-09-30): an `as` cast to an integer type keeps an integer
        // source's value exactly when the source interval fits the target type, so
        // `x as u32` over `x: u8` stays `[0, 255]` (it was Top, which made
        // `x as u32 + 1` unbounded). Otherwise the value is truncated or
        // reinterpreted, and lands somewhere in the target's range. A `u128` target
        // has no representable range (`type_to_interval`), so it is Top; a `u128`
        // source is never seeded, so it reaches here as Top. A float, pointer or
        // ADT source has no interval here and gets the target's range.
        Rvalue::Cast(op, to_ty) => {
            let Some(target) = type_to_interval(to_ty) else { return Interval::TOP };
            let source_is_integer = matches!(
                crate::operand_ty_cow(func, op).as_deref(),
                Some(Ty::Int { .. } | Ty::PtrSizedInt { .. })
            );
            let a = if source_is_integer {
                operand_to_interval(op, func, state)
            } else {
                Interval::TOP
            };
            if !a.is_bottom() && target.lo <= a.lo && a.hi <= target.hi { a } else { target }
        }
        // Trust (2026-09-28): TOP here; the statement transfer, which knows the
        // destination, narrows it to [`discriminant_read_hull`]. It was
        // `[0, i128::MAX]`, which a negative tag violates.
        Rvalue::Discriminant(_) => Interval::TOP,
        _ => Interval::TOP,
    }
}

/// Trust (2026-09-28, independent review of ENC-DEFECTS 13a): the values a
/// `Discriminant` read of `src` into `dest` can produce — the enum's DECODED tag
/// hull `[min tag, max tag]`.
///
/// Every read used to be `[0, i128::MAX]`. A discriminant is the tag as the
/// mathematical integer it denotes (`VariantDef::discriminant`), and a tag can be
/// negative: for `#[repr(i8)] enum S { Neg = -1, Pos = 5 }`, a parameter read in
/// the ENTRY block carried `d >= 0` into `merged_interval_environment`, and
/// `try_discharge_batch` proved `d - 127 - 1` although `S::Neg` overflows it
/// (measured on main and on the ENC branch alike: rc=0 "2 proved", and the
/// verify-off driver panics). Pre-existing; the review found it probing 13a, whose
/// "integer model = decoded tag" invariant this producer broke.
///
/// `None` (the caller keeps Top) when `src` is not an enum with known variants
/// (a struct is spelled `variants: []`), when `dest` is not an integer type whose
/// range holds every tag, or when a tag is negative under an UNSIGNED `dest` — the
/// one lossy spelling `VariantDef::discriminant` keeps (a `#[repr(u128)]` tag
/// above `i128::MAX`). The hull never exceeds `[0, i128::MAX]` for an enum whose
/// tags are non-negative, so no proof that stood on the old bound is lost there.
pub(crate) fn discriminant_read_hull(
    func: &VerifiableFunction,
    src: &Place,
    dest: &Place,
) -> Option<(i128, i128)> {
    let enum_ty = crate::place_ty_cow(func, src)?;
    let Ty::Adt { variants, adt_kind, .. } = enum_ty.as_ref() else { return None };
    if variants.is_empty() || matches!(adt_kind, Some(AdtKind::Struct | AdtKind::Union)) {
        return None;
    }
    let first = variants.first()?.discriminant;
    let (lo, hi) = variants[1..].iter().fold((first, first), |(lo, hi), v| {
        (lo.min(v.discriminant), hi.max(v.discriminant))
    });
    let dest_ty = crate::place_ty_cow(func, dest)?;
    let (type_lo, type_hi) = match dest_ty.as_ref() {
        Ty::PtrSizedInt { signed } => {
            super::discharge::type_bounds(&Ty::Int { width: 64, signed: *signed })?
        }
        Ty::Int { .. } => super::discharge::type_bounds(dest_ty.as_ref())?,
        _ => return None,
    };
    (type_lo <= lo && hi <= type_hi).then_some((lo, hi))
}

// ── Widen Point Detection ──────────────────────────────────────────────────

/// A program point where widening should be applied.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct WidenPoint {
    /// Block ID of the loop header.
    pub block: BlockId,
}

/// Detect widen points (loop headers) from a function's CFG.
///
/// A loop header is the target of a BACK edge: an edge into a block that is on
/// the current depth-first path from the entry. Every cycle of any CFG contains
/// such an edge, so widening at these targets bounds every ascending chain.
///
/// Trust (2026-10-09): this used to be "an edge from block N to block M with
/// M <= N", assuming MIR's block order follows the loop structure. It does not:
/// rustc lowers `match c { b'0'..=b'9' => .., }` with FORWARD edges to
/// lower-numbered blocks, so an acyclic range match got widen points, the
/// descending pass ran, and the result lost the arm's refinement (a `?`-returned
/// `c - b'0'` summarized as Top instead of `[0, 9]`). Widen-point placement
/// affects precision and termination only: every result is still checked by
/// [`repair_to_post_fixpoint`]. A self-loop is still not a widen point, as
/// before (its ascending chain is bounded by the iteration cap and the repair).
/// Blocks unreachable from the entry are searched afterwards so their cycles are
/// cut too.
#[must_use]
pub fn detect_widen_points(func: &VerifiableFunction) -> Vec<WidenPoint> {
    let n = func.body.blocks.len();
    let index_of: Option<FxHashMap<BlockId, usize>> = func
        .body
        .blocks
        .iter()
        .enumerate()
        .any(|(i, b)| b.id.0 != i)
        .then(|| {
            let mut map = FxHashMap::with_capacity_and_hasher(n, Default::default());
            for (i, b) in func.body.blocks.iter().enumerate() {
                map.insert(b.id, i);
            }
            map
        });
    // PERF-COMPILER-VCGEN-692: in a canonical CFG (`b.id.0 == i`), any non-self directed
    // cycle on `{0, ..., n - 1}` must contain at least one edge `u -> v` with `v < u`
    // (taking `u` as the maximum index on the cycle). When no block has an exit target
    // strictly below its own index, no non-self back-edge exists and we can return empty
    // without allocating `state`, `headers`, or per-block DFS `succs` vectors.
    if index_of.is_none()
        && !func.body.blocks.iter().enumerate().any(|(i, b)| {
            let mut has_back = false;
            b.terminator.for_each_exit_block_target(|id| {
                if id.0 < n && id.0 < i {
                    has_back = true;
                }
            });
            has_back
        })
    {
        return Vec::new();
    }
    let successors = |i: usize| -> Vec<usize> {
        let mut succs = Vec::new();
        func.body.blocks[i].terminator.for_each_exit_block_target(|id| {
            let idx = match &index_of {
                Some(map) => map.get(&id).copied(),
                None => (id.0 < n).then_some(id.0),
            };
            if let Some(idx) = idx {
                succs.push(idx);
            }
        });
        succs
    };
    // 0 = unvisited, 1 = on the DFS stack, 2 = finished.
    let mut state = vec![0u8; n];
    let mut headers = FxHashSet::default();
    for root in 0..n {
        if state[root] != 0 {
            continue;
        }
        let mut stack: Vec<(usize, Vec<usize>, usize)> = vec![(root, successors(root), 0)];
        state[root] = 1;
        while let Some((node, succs, next)) = stack.last_mut() {
            if *next < succs.len() {
                let succ = succs[*next];
                *next += 1;
                match state[succ] {
                    0 => {
                        state[succ] = 1;
                        let succ_list = successors(succ);
                        stack.push((succ, succ_list, 0));
                    }
                    1 if succ != *node => {
                        headers.insert(func.body.blocks[succ].id);
                    }
                    _ => {}
                }
            } else {
                state[*node] = 2;
                stack.pop();
            }
        }
    }
    let mut out: Vec<WidenPoint> = headers.into_iter().map(|block| WidenPoint { block }).collect();
    out.sort_by_key(|wp| wp.block.0);
    out
}

// ── Fixpoint Computation ───────────────────────────────────────────────────

/// Whether `term` has at least one normal successor block.
fn terminator_has_successors(term: &Terminator) -> bool {
    match term {
        Terminator::Goto(_)
        | Terminator::Drop { .. }
        | Terminator::SwitchInt { .. }
        | Terminator::Assert { .. } => true,
        Terminator::Call { target, .. } => target.is_some(),
        Terminator::Opaque { targets, .. } => !targets.is_empty(),
        Terminator::Return | Terminator::TailCall { .. } | Terminator::Unreachable => false,
        _ => false,
    }
}

/// Visit all successor block IDs from a terminator without allocating a `Vec<BlockId>`.
///
/// Unlike `exit_targets()` which returns `ClauseTarget::Panic` for Assert
/// terminators, this extracts the actual successor block IDs needed for
/// dataflow propagation.
fn for_each_terminator_successor(term: &Terminator, mut f: impl FnMut(BlockId)) {
    match term {
        Terminator::Goto(target) | Terminator::Drop { target, .. } => f(*target),
        Terminator::SwitchInt { targets, otherwise, .. } => {
            for (_, b) in targets {
                f(*b);
            }
            f(*otherwise);
        }
        Terminator::Assert { target, .. } => f(*target),
        Terminator::Call { target: Some(target), .. } => f(*target),
        Terminator::Opaque { targets, .. } => {
            for target in targets {
                f(*target);
            }
        }
        Terminator::Call { target: None, .. }
        | Terminator::Return
        | Terminator::TailCall { .. }
        | Terminator::Unreachable => {}
        _ => {}
    }
}

/// Extract all successor block IDs from a terminator.
///
/// Unlike `exit_targets()` which returns `ClauseTarget::Panic` for Assert
/// terminators, this extracts the actual successor block IDs needed for
/// dataflow propagation.
fn terminator_successors(term: &Terminator) -> Vec<BlockId> {
    let mut succs = Vec::new();
    for_each_terminator_successor(term, |id| succs.push(id));
    succs
}

/// Result of fixpoint computation: abstract state at each block entry.
#[derive(Debug, Clone)]
pub struct FixpointResult {
    /// Abstract state at entry to each block.
    pub block_states: FxHashMap<BlockId, IntervalDomain>,
}

/// Compute the abstract fixpoint over a function's CFG.
///
/// Uses chaotic iteration with widening at loop headers.
/// Convergence is guaranteed by widening (finite ascending chains).
#[must_use]
pub fn fixpoint(func: &VerifiableFunction, initial: IntervalDomain) -> FixpointResult {
    let widen_points: FxHashSet<BlockId> =
        detect_widen_points(func).into_iter().map(|wp| wp.block).collect();

    let mut states: FxHashMap<BlockId, IntervalDomain> =
        FxHashMap::with_capacity_and_hasher(func.body.blocks.len(), Default::default());
    for block in &func.body.blocks {
        states.insert(block.id, IntervalDomain::bottom());
    }

    // Entry block gets the initial state.
    if let Some(first) = func.body.blocks.first() {
        states.insert(first.id, initial);
    }

    let max_iterations = func.body.blocks.len() * 20 + 100;
    let mut worklist: VecDeque<BlockId> = VecDeque::with_capacity(func.body.blocks.len());
    let mut in_worklist: FxHashSet<BlockId> =
        FxHashSet::with_capacity_and_hasher(func.body.blocks.len(), Default::default());
    for block in &func.body.blocks {
        if in_worklist.insert(block.id) {
            worklist.push_back(block.id);
        }
    }
    let mut iteration = 0;
    let positions = block_positions(func);
    let mut havoc = CallHavoc::new(func);

    while let Some(block_id) = worklist.pop_front() {
        in_worklist.remove(&block_id);
        iteration += 1;
        if iteration > max_iterations {
            break;
        }
        // Trust (2026-10-02): the ambient budget, once per pop; a trip refuses.
        if fixpoint_budget_tripped() {
            let mut refused = FixpointResult { block_states: states };
            refuse_everything(&mut refused);
            return refused;
        }

        let Some(pos) = positions.get(&block_id) else {
            continue;
        };
        let block = &func.body.blocks[pos];

        let entry_state = states.get(&block_id).cloned().unwrap_or_else(IntervalDomain::bottom);
        if entry_state.is_unreachable {
            continue;
        }

        // Apply transfer functions for all statements in this block.
        let mut current = transfer_statements(&mut havoc, pos, block, entry_state);
        // Trust (P0): apply the TERMINATOR transfer (a `Call` havocs its dest +
        // every `&mut`-escaped local) before propagating.
        current = transfer_terminator(&mut havoc, pos, block, current);

        // Propagate to successors.
        // exit_targets() doesn't include Assert/Call success targets
        // (they return Panic/Return), so we extract them directly.
        for_each_terminator_successor(&block.terminator, |succ_id| {
            let do_widen = widen_points.contains(&succ_id);
            let changed = if let Some(old) = states.get_mut(&succ_id) {
                if do_widen {
                    old.widen_in_place_changed(&current)
                } else {
                    old.join_in_place_changed(&current)
                }
            } else {
                let mut fresh = IntervalDomain::bottom();
                let c = if do_widen {
                    fresh.widen_in_place_changed(&current)
                } else {
                    fresh.join_in_place_changed(&current)
                };
                if c {
                    states.insert(succ_id, fresh);
                }
                c
            };
            if changed && in_worklist.insert(succ_id) {
                worklist.push_back(succ_id);
            }
        });
    }

    let mut result = FixpointResult { block_states: states };
    // A trip inside the last pop's work (the havoc derivation polls too) is seen
    // here: the answer of a run any trip touched is the refusal.
    if trust_types::verify_budget::exhausted_readonly() {
        refuse_everything(&mut result);
    }
    result
}

/// Build a type-aware initial interval domain from a function's signature.
///
/// Initializes argument variables to their type's representable range
/// (e.g., u32 -> [0, 4294967295]), giving the abstract interpretation
/// much tighter starting bounds than Top. Additionally, declared
/// preconditions on parameters (e.g. `a <= 1000`) are folded into the
/// initial state so nonlinear safety obligations (in particular
/// multiplication) become decidable from the abstract state alone.
#[must_use]
pub fn type_aware_initial_state(func: &VerifiableFunction) -> IntervalDomain {
    let mut state = IntervalDomain::top();
    for (i, local) in func.body.locals.iter().enumerate() {
        // Skip the return slot (index 0) only.
        //
        // Trust 2026-09-18: every integer-typed local is seeded with its TYPE
        // range, not just the arguments. A `u32` local holds a value in
        // `[0, u32::MAX]` at every point where it holds a value at all, and
        // valid MIR cannot read one before its first definition, so the bound
        // is sound everywhere it means anything.
        //
        // Leaving a local unseeded was not merely imprecise, it let WIDENING
        // walk the interval clean outside the type: measured on
        // `loop { r += 1; if r > 5 { break; } }`, the `u32` counter reached a
        // lower bound of `i128::MIN`, because threshold widening descends
        // through the threshold set and runs out. An interval claiming a `u32`
        // can be negative is sound but useless, and it poisons every join it
        // takes part in.
        if i == 0 {
            continue;
        }
        // Keyed by the FORMULA name, the one every transfer below writes
        // (`place_to_var_name`); see `crate::local_var_name`.
        if let Some(interval) = type_to_interval(&local.ty) {
            state.set(crate::local_var_name(func, local), interval);
        }
    }

    // Refine using declared preconditions (e.g. `a <= 1000`,
    // `idx < len`, `divisor != 0`). Each refinement intersects the
    // existing interval with whatever bound the precondition exposes
    // about a single named variable; conjunctions are handled
    // recursively so multi-clause preconditions all contribute.
    for pre in &func.preconditions {
        refine_state_with_precondition(&mut state, pre);
    }

    state
}

/// Walk a precondition formula and tighten the abstract state for each
/// named integer-typed variable bound the formula exposes.
///
/// Handles the shapes the scale fixture and friends use directly:
/// `var <= lit`, `var < lit`, `var >= lit`, `var > lit`, `var != lit`,
/// `0 <= var`, conjunctions, and the same patterns with the literal on
/// the left-hand side. Unrecognized shapes are ignored — they remain
/// available as a hypothesis on each VC.
fn refine_state_with_precondition(state: &mut IntervalDomain, formula: &Formula) {
    match formula {
        Formula::And(conjuncts) => {
            for c in conjuncts {
                refine_state_with_precondition(state, c);
            }
        }
        Formula::Le(lhs, rhs) => {
            if let (Some(name), Some(v)) = (var_name(lhs), int_const(rhs)) {
                intersect(state, &name, Interval::new(i128::MIN, v));
            } else if let (Some(v), Some(name)) = (int_const(lhs), var_name(rhs)) {
                intersect(state, &name, Interval::new(v, i128::MAX));
            }
        }
        Formula::Lt(lhs, rhs) => {
            if let (Some(name), Some(v)) = (var_name(lhs), int_const(rhs)) {
                intersect(state, &name, Interval::new(i128::MIN, v.saturating_sub(1)));
            } else if let (Some(v), Some(name)) = (int_const(lhs), var_name(rhs)) {
                intersect(state, &name, Interval::new(v.saturating_add(1), i128::MAX));
            }
        }
        Formula::Ge(lhs, rhs) => {
            if let (Some(name), Some(v)) = (var_name(lhs), int_const(rhs)) {
                intersect(state, &name, Interval::new(v, i128::MAX));
            } else if let (Some(v), Some(name)) = (int_const(lhs), var_name(rhs)) {
                intersect(state, &name, Interval::new(i128::MIN, v));
            }
        }
        Formula::Gt(lhs, rhs) => {
            if let (Some(name), Some(v)) = (var_name(lhs), int_const(rhs)) {
                intersect(state, &name, Interval::new(v.saturating_add(1), i128::MAX));
            } else if let (Some(v), Some(name)) = (int_const(lhs), var_name(rhs)) {
                intersect(state, &name, Interval::new(i128::MIN, v.saturating_sub(1)));
            }
        }
        Formula::Not(inner) => {
            // Handle `!(var == c)` so divisor != 0 still tightens away the
            // single excluded point; intervals can't represent holes, so we
            // can only refine when one half of the excluded point sits
            // outside the current bound. We leave the generic case alone.
            if let Formula::Eq(lhs, rhs) = inner.as_ref() {
                let pair = match (var_name(lhs), int_const(rhs)) {
                    (Some(name), Some(v)) => Some((name, v)),
                    _ => match (var_name(rhs), int_const(lhs)) {
                        (Some(name), Some(v)) => Some((name, v)),
                        _ => None,
                    },
                };
                if let Some((name, v)) = pair {
                    let current = state.get(&name);
                    if current.lo == v {
                        intersect(state, &name, Interval::new(v.saturating_add(1), i128::MAX));
                    } else if current.hi == v {
                        intersect(state, &name, Interval::new(i128::MIN, v.saturating_sub(1)));
                    }
                }
            }
        }
        _ => {}
    }
}

/// Return the variable name of a simple `Formula::Var` (any sort).
fn var_name(formula: &Formula) -> Option<&str> {
    match formula {
        Formula::Var(name, _) => Some(name.as_str()),
        Formula::SymVar(name, _) => Some(name.as_str()),
        _ => None,
    }
}

/// Return the integer literal value of a simple `Formula::Int`/`Formula::UInt`.
fn int_const(formula: &Formula) -> Option<i128> {
    match formula {
        Formula::Int(v) => Some(*v),
        Formula::UInt(v) => i128::try_from(*v).ok(),
        _ => None,
    }
}

/// Intersect the interval already stored for `name` with `bound`.
fn intersect(state: &mut IntervalDomain, name: &str, bound: Interval) {
    if state.is_unreachable {
        return;
    }
    let current = state.get(name);
    let next = current.meet(&bound);
    if let Some(slot) = state.vars.get_mut(name) {
        *slot = next;
    } else {
        state.vars.insert(name.to_string(), next);
    }
}

/// Convert a type to its representable interval.
///
/// Returns `None` for non-numeric types, including `bool`. A bool's `[0,1]`
/// range is a vacuous integer bound (every bool already satisfies it) and is
/// never consumed by integer arithmetic — Rust requires an explicit cast,
/// which produces a fresh integer local. Tracking bools here only created a
/// sort conflict at the formula sink: the same name would surface as
/// `Var(name, Int)` from the emitted `[0,1]` bound *and* as `Var(name, Bool)`
/// in branch guards, breaking the SMT backend (a Goal-1 false-fail). So bools
/// are intentionally not tracked in the interval domain.
#[must_use]
pub fn type_to_interval(ty: &Ty) -> Option<Interval> {
    match ty {
        // Raw pointers are non-negative addresses.
        Ty::RawPtr { .. } => Some(Interval::new(0, i128::MAX)),
        Ty::Int { width, signed: true } => {
            if *width == 128 {
                Some(Interval::new(i128::MIN, i128::MAX))
            } else if *width > 0 && *width < 128 {
                let half = 1i128 << (width - 1);
                Some(Interval::new(-half, half - 1))
            } else {
                None
            }
        }
        Ty::Int { width, signed: false } => {
            if *width == 128 {
                // Trust (2026-09-30): NOT representable. `u128::MAX` does not fit an
                // `i128` bound, and the `[0, i128::MAX]` this used to answer EXCLUDES
                // every value at or above 2^127: round 10 of the callee-summary review
                // measured `x as i128` over `x: u128` kept in `[0, i128::MAX]`, so
                // `y < 0` was unreachable and a panicking index proved, certified.
                // `discharge::type_bounds` refused the same range (P1-12); this is
                // that answer here. Every caller reads `None` as "unknown".
                None
            } else if *width > 0 && *width < 128 {
                Some(Interval::new(0, (1i128 << width) - 1))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Extract threshold constants from a function's CFG.
///
/// Sources:
/// 1. SwitchInt target values (loop bounds, enum discriminants).
/// 2. Constants in comparison operands from Assign statements involving
///    Lt/Le/Gt/Ge/Eq BinOps.
/// 3. Type bounds (0, type_min, type_max) for each integer type in the
///    function's locals.
///
/// Always includes 0 as a threshold (common loop start).
#[must_use]
pub fn extract_thresholds(func: &VerifiableFunction) -> ThresholdSet {
    let mut values = Vec::new();

    // Always include 0.
    values.push(0);

    // Source 1 & 2: SwitchInt target values and constants in comparison operands.
    for block in &func.body.blocks {
        if let Terminator::SwitchInt { targets, .. } = &block.terminator {
            for (val, _) in targets {
                if let Ok(v) = i128::try_from(*val) {
                    values.push(v);
                    // Adjacent thresholds for off-by-one precision.
                    values.push(v.saturating_sub(1));
                    values.push(v.saturating_add(1));
                }
            }
        }
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue, .. } = stmt {
                extract_comparison_constants(rvalue, &mut values);
            }
        }
    }

    // Source 3: Type bounds from locals.
    for local in &func.body.locals {
        if let Some(interval) = type_to_interval(&local.ty) {
            if interval.lo != i128::MIN {
                values.push(interval.lo);
            }
            if interval.hi != i128::MAX {
                values.push(interval.hi);
            }
        }
    }

    ThresholdSet::new(values)
}

/// Extract constants from comparison rvalues.
fn extract_comparison_constants(rvalue: &Rvalue, values: &mut Vec<i128>) {
    match rvalue {
        Rvalue::BinaryOp(op, lhs, rhs) | Rvalue::CheckedBinaryOp(op, lhs, rhs)
            if matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq) =>
        {
            // Extract constant from RHS of comparison.
            if let Operand::Constant(cv) = rhs {
                extract_const_value(cv, values, true);
            }
            // Also extract constant from LHS.
            if let Operand::Constant(cv) = lhs {
                extract_const_value(cv, values, false);
            }
        }
        _ => {}
    }
}

/// Extract a numeric constant into the threshold values list.
/// If `with_neighbors` is true, also adds value-1 and value+1.
fn extract_const_value(cv: &ConstValue, values: &mut Vec<i128>, with_neighbors: bool) {
    let v = match cv {
        ConstValue::Int(n) => Some(*n),
        ConstValue::Uint(n, _) => i128::try_from(*n).ok(),
        _ => None,
    };
    if let Some(v) = v {
        values.push(v);
        if with_neighbors {
            values.push(v.saturating_sub(1));
            values.push(v.saturating_add(1));
        }
    }
}

// ── Configured Fixpoint ──────────────────────────────────────────────────

/// Configuration for abstract interpretation fixpoint computation.
#[derive(Debug, Clone)]
pub struct FixpointConfig {
    /// Number of join iterations before widening kicks in at each loop header.
    /// Default: 3.
    pub widen_delay: usize,
    /// Number of descending narrowing passes after widening converges.
    /// Default: 3.
    pub narrowing_passes: usize,
    /// Optional threshold set for threshold widening.
    pub thresholds: Option<ThresholdSet>,
}

impl Default for FixpointConfig {
    fn default() -> Self {
        Self { widen_delay: 3, narrowing_passes: 3, thresholds: None }
    }
}

impl FixpointConfig {
    /// Create config with auto-extracted thresholds from the function.
    #[must_use]
    pub fn for_function(func: &VerifiableFunction) -> Self {
        Self { thresholds: Some(extract_thresholds(func)), ..Self::default() }
    }
}

/// Compute successor states with condition narrowing from SwitchInt.
///
/// For SwitchInt terminators:
///   - Match arms: narrow the discriminant variable to [value, value].
///   - Otherwise arm: narrow the discriminant to exclude all match values.
///
/// For all other terminators: propagate the state unchanged.
#[cfg(test)]
pub(crate) fn compute_successor_states(
    terminator: &Terminator,
    func: &VerifiableFunction,
    block: &BasicBlock,
    state: &IntervalDomain,
) -> Vec<(BlockId, IntervalDomain)> {
    let cap = match terminator {
        Terminator::SwitchInt { targets, .. } => targets.len() + 1,
        Terminator::Call { target: None, .. }
        | Terminator::Return
        | Terminator::TailCall { .. }
        | Terminator::Unreachable => 0,
        _ => 1,
    };
    let mut successors = Vec::with_capacity(cap);
    for_each_successor_state_owned(terminator, func, block, state.clone(), |id, succ_state| {
        successors.push((id, succ_state));
    });
    successors
}

/// Visit every successor edge of `terminator` with its narrowed `IntervalDomain`,
/// moving `state` without cloning on single-successor terminators and on the final
/// (`otherwise` / last `Opaque`) arm of multi-successor terminators, and hoisting
/// `SwitchInt` discriminant lookups once across all arms.
fn for_each_successor_state_owned(
    terminator: &Terminator,
    func: &VerifiableFunction,
    block: &BasicBlock,
    state: IntervalDomain,
    mut on_succ: impl FnMut(BlockId, IntervalDomain),
) {
    match terminator {
        Terminator::SwitchInt { discr, targets, otherwise, .. } => {
            let discr_ty = crate::operand_ty_cow(func, discr);
            let discr_ty_ref = discr_ty.as_deref();
            let discr_place_name = match discr {
                Operand::Copy(place) | Operand::Move(place) => {
                    Some(crate::place_to_var_name(func, place))
                }
                _ => None,
            };
            let is_bool = matches!(discr_ty_ref, Some(Ty::Bool));
            let defining_cmp =
                if is_bool { discriminant_defining_comparison(block, discr) } else { None };
            let mut ascii_hull: Option<Option<(Operand, i128, i128)>> = None;

            // Each match arm: discr == value.
            for &(value, block_id) in targets {
                let mut narrowed = state.clone();
                narrow_from_condition_in_place(
                    &mut narrowed,
                    discr_ty_ref,
                    discr_place_name.as_deref(),
                    value,
                );
                let truth = branch_truth_with_bool(is_bool, Some(value), targets);
                narrow_through_comparison_precomputed(
                    &mut narrowed,
                    func,
                    block,
                    defining_cmp,
                    truth,
                );
                narrow_through_ascii_predicate_cached(
                    &mut narrowed,
                    func,
                    discr,
                    truth,
                    &mut ascii_hull,
                );
                on_succ(block_id, narrowed);
            }

            // Otherwise arm: discr != any target value. Moves `state` with zero cloning.
            let mut otherwise_state = state;
            narrow_from_otherwise_in_place(
                &mut otherwise_state,
                discr_ty_ref,
                discr_place_name,
                targets,
            );
            let truth = branch_truth_with_bool(is_bool, None, targets);
            narrow_through_comparison_precomputed(
                &mut otherwise_state,
                func,
                block,
                defining_cmp,
                truth,
            );
            narrow_through_ascii_predicate_cached(
                &mut otherwise_state,
                func,
                discr,
                truth,
                &mut ascii_hull,
            );
            on_succ(*otherwise, otherwise_state);
        }
        // Trust (2026-10-05, NEG-WRAP-OFF-1): the success edge of rustc's
        // negation check — `_c = Eq(x, MIN); assert(!_c)` — carries `x != MIN`.
        // The bare `Neg` behind it is now clamped as WRAPPING (see
        // `transfer_function`); without this edge fact the checks-ON `-x` of an
        // `x ∈ [MIN, -1]` would widen to the whole type, where it used to stay
        // `[1, 2^31]` only because the mathematical negation happened to agree
        // with the one value the assert rules out.
        Terminator::Assert {
            cond,
            expected: false,
            msg: AssertMessage::OverflowNeg,
            target,
            ..
        } => {
            let mut narrowed = state;
            narrow_past_overflow_neg_assert(&mut narrowed, func, block, cond);
            if tracking_checked_fields() {
                checked_result_field_on_success(&mut narrowed, func, cond, false);
            }
            on_succ(*target, narrowed);
        }
        Terminator::Assert { target, cond, expected, .. } => {
            // Propagate state to the success target, narrowing a checked result
            // field that this assert guards.
            let mut success = state;
            if tracking_checked_fields() {
                checked_result_field_on_success(&mut success, func, cond, *expected);
            }
            on_succ(*target, success);
        }
        Terminator::Goto(target)
        | Terminator::Drop { target, .. }
        | Terminator::Call { target: Some(target), .. } => on_succ(*target, state),
        Terminator::Call { target: None, .. }
        | Terminator::Return
        | Terminator::TailCall { .. }
        | Terminator::Unreachable => {}
        _ => {
            let mut ids = Vec::new();
            for_each_terminator_successor(terminator, |id| ids.push(id));
            if let Some((&last, init)) = ids.split_last() {
                for &id in init {
                    on_succ(id, state.clone());
                }
                on_succ(last, state);
            }
        }
    }
}

thread_local! {
    static SUMMARY_PRECISION: std::cell::Cell<(bool, bool)> =
        const { std::cell::Cell::new((false, false)) };
}

/// Whether the summary-only copy narrowing is on (see [`SummaryPrecision`]).
fn summary_precision() -> bool {
    SUMMARY_PRECISION.with(std::cell::Cell::get).0
}

/// Whether the summary-only tracking of a checked result field `_k.0` is on (see
/// [`SummaryPrecision`]).
fn tracking_checked_fields() -> bool {
    SUMMARY_PRECISION.with(std::cell::Cell::get).1
}

/// Trust (2026-09-30): the scope of two precision steps used by the
/// return-interval summary only: tracking a checked operation's result field
/// `_k.0`, and narrowing the source of a comparison's fresh copy
/// (`comparison_copy_source`).
///
/// OFF for the production environment on purpose. Both are branch narrowings that
/// can start biting a round early inside a loop, which is the interaction measured
/// 2026-09-18 (see [`repair_to_post_fixpoint`]): the iteration settles below the
/// fixpoint, and the repair gives the loop head up to Top, losing a bound the
/// environment had (the break-test bound that closed a false refutation; round 10
/// measured `while i >= 16 { i = i / 2 }` the same way). The return interval is
/// asked once per body, and there a loop that ends in Top costs only the summary.
///
/// The checked-field tracking reads an overflow assert's success edge as "no
/// overflow happened", which is true only where that assert is enforced. With
/// `-C overflow-checks=off` codegen drops an overflow assert that MIR still carries
/// (`#[rustc_inherit_overflow_checks]`), so the caller turns that half off
/// (`asserts_enforced`); measured in round 10: `x + 10` narrowed to `[10, 255]`
/// while the build wrapped `246 + 10` to 0.
struct SummaryPrecision {
    previous: (bool, bool),
}

impl SummaryPrecision {
    fn enter(asserts_enforced: bool) -> Self {
        Self { previous: SUMMARY_PRECISION.with(|flag| flag.replace((true, asserts_enforced))) }
    }
}

impl Drop for SummaryPrecision {
    fn drop(&mut self) {
        SUMMARY_PRECISION.with(|flag| flag.set(self.previous));
    }
}

/// Trust (2026-09-30): for a whole-local write of a `(T, bool)` tuple with `T` an
/// integer, the formula name of its result field `.0` and `T`'s range (`None` for
/// a `u128`, whose range this domain cannot represent).
fn checked_result_field(
    func: &VerifiableFunction,
    place: &Place,
) -> Option<(String, Option<Interval>)> {
    if !place.projections.is_empty() {
        return None;
    }
    let Ty::Tuple(elems) = crate::local_ty_ref(func, place.local)? else { return None };
    let [elem @ Ty::Int { .. }, Ty::Bool] = elems.as_slice() else { return None };
    let range = type_to_interval(elem);
    let field = Place { local: place.local, projections: vec![Projection::Field(0)] };
    Some((crate::place_to_var_name(func, &field), range))
}

/// Trust (2026-09-30): on the success edge of `assert(_k.1 == false)`, the
/// overflow flag of a checked operation is clear, so `_k.0` IS the mathematical
/// result, which the tuple's own entry `_k` holds (`eval_rvalue` gives a
/// `CheckedBinaryOp` its unwrapped interval), and a value of its type. Narrow
/// `_k.0` to that intersection.
///
/// SOUND for any definition of `_k`: the whole-tuple entry is non-Top only when
/// the latest write to `_k` was a checked operation (or a copy of one), every
/// write inside or above `_k` rebinds it (`transfer_function`), and the flag and
/// the field come from that same write. An empty intersection (the operation
/// always overflows) leaves the state alone.
fn checked_result_field_on_success(
    state: &mut IntervalDomain,
    func: &VerifiableFunction,
    cond: &Operand,
    expected: bool,
) {
    if expected {
        return;
    }
    let (Operand::Copy(flag) | Operand::Move(flag)) = cond else { return };
    if flag.projections != [Projection::Field(1)] {
        return;
    }
    let tuple = Place::local(flag.local);
    let Some((field, Some(range))) = checked_result_field(func, &tuple) else { return };
    let math = state.get(&crate::place_to_var_name(func, &tuple));
    let narrowed = math.meet(&range).meet(&state.get(&field));
    if !narrowed.is_bottom() {
        state.set(field, narrowed);
    }
}

/// The typed `SwitchInt`-label decode this interval domain uses.
///
/// `Ty::decode_switch_label` declines `Bool` on purpose (a bool switch is a
/// polarity, not an integer equality, and the FORMULA lanes render it
/// themselves). This domain has no boolean sort — it narrows the integer
/// interval of the modeled variable — so a bool discriminant is decoded as an
/// unsigned width-1 value, reproducing the previous `0`/`1` narrowing EXACTLY.
/// Anything wider than a bool's one bit is a malformed label and declines.
fn interval_switch_label(ty: &Ty, raw: u128) -> Option<i128> {
    if matches!(ty, Ty::Bool) {
        return trust_types::decode_raw_two_complement(raw, 1, false);
    }
    ty.decode_switch_label(raw)
}

/// Narrow state for the SwitchInt otherwise branch.
///
/// If the discriminant is a single variable, exclude all target values.
/// For a discriminant with interval [lo, hi] and excluded values {v1, ..., vn}:
///   - If excluded values are at the bottom of the range, raise lo.
///   - If excluded values are at the top of the range, lower hi.
///   - Otherwise, the narrowing is imprecise (intervals can't represent gaps).
#[cfg(test)]
#[must_use]
pub(crate) fn narrow_from_otherwise(
    state: &IntervalDomain,
    func: &VerifiableFunction,
    discr: &Operand,
    targets: &[(u128, BlockId)],
) -> IntervalDomain {
    let mut result = state.clone();
    if result.is_unreachable {
        return result;
    }
    if let Operand::Copy(place) | Operand::Move(place) = discr {
        let discr_ty = crate::operand_ty_cow(func, discr);
        let name = crate::place_to_var_name(func, place);
        narrow_from_otherwise_in_place(&mut result, discr_ty.as_deref(), Some(name), targets);
    }
    result
}

fn narrow_from_otherwise_in_place(
    result: &mut IntervalDomain,
    discr_ty: Option<&Ty>,
    discr_place_name: Option<String>,
    targets: &[(u128, BlockId)],
) {
    if result.is_unreachable {
        return;
    }
    // Collect excluded values. A raw MIR arm label is a two's-complement
    // BIT PATTERN at the discriminant's width, so it must be DECODED under
    // that type before it can be compared against an interval over the
    // value's mathematical range: the raw spelling read an `i32` `-1` arm as
    // `4294967295`, which never touches `[-2^31, 2^31-1]`'s edges and so
    // silently lost the exclusion. An undecodable label is DROPPED, which
    // only widens the `otherwise` interval (fails closed).
    let (Some(discr_ty), Some(name)) = (discr_ty, discr_place_name) else { return };
    let current = result.get(&name);
    if current.is_bottom() {
        return;
    }
    let mut lo = current.lo;
    let mut hi = current.hi;
    if let [(raw, _)] = targets {
        let Some(v) = interval_switch_label(discr_ty, *raw) else { return };
        if v == lo {
            lo = lo.saturating_add(1);
        }
        if v == hi {
            hi = hi.saturating_sub(1);
        }
    } else {
        let mut excluded: Vec<i128> =
            targets.iter().filter_map(|(v, _)| interval_switch_label(discr_ty, *v)).collect();
        excluded.sort_unstable();

        if excluded.is_empty() {
            return;
        }

        // Tighten bounds if excluded values are at the edges.
        for &v in &excluded {
            if v == lo {
                lo = lo.saturating_add(1);
            } else {
                break;
            }
        }
        for &v in excluded.iter().rev() {
            if v == hi {
                hi = hi.saturating_sub(1);
            } else {
                break;
            }
        }
    }

    if lo > hi {
        result.set(name, Interval::BOTTOM);
    } else if lo != current.lo || hi != current.hi {
        result.set(name, Interval::new(lo, hi));
    }
}

/// Apply descending narrowing passes to a fixpoint result.
///
/// Answers `true` iff the ambient budget tripped, in which case `result` has been
/// REFUSED ([`refuse_everything`]) and the caller must not refine it further.
#[must_use]
fn apply_narrowing_pass(
    func: &VerifiableFunction,
    result: &mut FixpointResult,
    widen_points: &FxHashSet<BlockId>,
    max_passes: usize,
    havoc: &mut CallHavoc<'_>,
) -> bool {
    for _ in 0..max_passes {
        let mut changed = false;
        for (pos, block) in func.body.blocks.iter().enumerate() {
            // Trust (2026-10-02): the ambient budget, once per block; a trip refuses.
            if fixpoint_budget_tripped() {
                refuse_everything(result);
                return true;
            }
            let entry_state =
                result.block_states.get(&block.id).cloned().unwrap_or_else(IntervalDomain::bottom);
            if entry_state.is_unreachable {
                continue;
            }
            let mut current = transfer_statements(havoc, pos, block, entry_state);
            // Trust (P0): terminator transfer (Call havocs dest + &mut-escaped locals).
            current = transfer_terminator(havoc, pos, block, current);
            // Trust (2026-10-09): propagate the EDGE-NARROWED states, exactly as
            // the ascending pass does. Propagating the raw `current` dropped every
            // `SwitchInt` refinement and joined the unrefined state into the arm
            // blocks, which the repair then had to widen to Top.
            for_each_successor_state_owned(
                &block.terminator,
                func,
                block,
                current,
                |succ_id, succ_state| {
                    let do_narrow = widen_points.contains(&succ_id);
                    let did_change = if let Some(old) = result.block_states.get_mut(&succ_id) {
                        if do_narrow {
                            old.narrow_owned_in_place(succ_state)
                        } else {
                            old.join_owned_in_place(succ_state)
                        }
                    } else {
                        let mut fresh = IntervalDomain::bottom();
                        let c = if do_narrow {
                            fresh.narrow_owned_in_place(succ_state)
                        } else {
                            fresh.join_owned_in_place(succ_state)
                        };
                        if c {
                            result.block_states.insert(succ_id, fresh);
                        }
                        c
                    };
                    if did_change {
                        changed = true;
                    }
                },
            );
        }
        if !changed {
            break;
        }
    }
    false
}

/// Compute the abstract fixpoint with threshold widening, delayed widening,
/// descending narrowing, and condition narrowing.
///
/// This is the full-featured replacement for `fixpoint()` and
/// `fixpoint_with_narrowing()`.
#[must_use]
pub fn fixpoint_configured(
    func: &VerifiableFunction,
    initial: IntervalDomain,
    config: &FixpointConfig,
) -> FixpointResult {
    fixpoint_configured_indexed(func, initial, config).0
}

/// [`fixpoint_configured`], also handing back the run's havoc index ([`CallHavoc`]):
/// `merged_interval_environment` walks every block once more with it
/// ([`join_statement_values`]), and the lists that walk needs are the ones this run
/// already derived.
#[must_use]
pub(super) fn fixpoint_configured_indexed<'f>(
    func: &'f VerifiableFunction,
    initial: IntervalDomain,
    config: &FixpointConfig,
) -> (FixpointResult, CallHavoc<'f>) {
    let widen_points: FxHashSet<BlockId> =
        detect_widen_points(func).into_iter().map(|wp| wp.block).collect();
    fixpoint_configured_with_widen_points_indexed(func, initial, config, widen_points)
}

/// PERF-COMPILER-VCGEN-769: run [`fixpoint_configured_indexed`] with default
/// `FixpointConfig::for_function` settings (`widen_delay: 3`, `narrowing_passes: 3`),
/// extracting thresholds only when `detect_widen_points(func)` is non-empty (an
/// acyclic CFG has no widen points, so `do_widen` is never true and `config.thresholds`
/// is never read).
#[must_use]
pub(super) fn fixpoint_for_function_indexed<'f>(
    func: &'f VerifiableFunction,
    initial: IntervalDomain,
) -> (FixpointResult, CallHavoc<'f>) {
    fixpoint_with_auto_thresholds_indexed(func, initial, 3, 3)
}

#[must_use]
fn fixpoint_with_auto_thresholds_indexed<'f>(
    func: &'f VerifiableFunction,
    initial: IntervalDomain,
    widen_delay: usize,
    narrowing_passes: usize,
) -> (FixpointResult, CallHavoc<'f>) {
    let widen_points: FxHashSet<BlockId> =
        detect_widen_points(func).into_iter().map(|wp| wp.block).collect();
    let thresholds = (!widen_points.is_empty()).then(|| extract_thresholds(func));
    let config = FixpointConfig { widen_delay, narrowing_passes, thresholds };
    fixpoint_configured_with_widen_points_indexed(func, initial, &config, widen_points)
}

#[must_use]
fn fixpoint_configured_with_widen_points_indexed<'f>(
    func: &'f VerifiableFunction,
    initial: IntervalDomain,
    config: &FixpointConfig,
    widen_points: FxHashSet<BlockId>,
) -> (FixpointResult, CallHavoc<'f>) {

    let mut states: FxHashMap<BlockId, IntervalDomain> =
        FxHashMap::with_capacity_and_hasher(func.body.blocks.len(), Default::default());
    for block in &func.body.blocks {
        states.insert(block.id, IntervalDomain::bottom());
    }
    if let Some(first) = func.body.blocks.first() {
        states.insert(first.id, initial);
    }

    // Per-block iteration count for delayed widening.
    // PERF-COMPILER-VCGEN-694: only widen-point headers ever consult `block_iterations`;
    // size to `widen_points.len()` and gate the hash probe/insert on `widen_points.contains`.
    let mut block_iterations: FxHashMap<BlockId, usize> =
        FxHashMap::with_capacity_and_hasher(widen_points.len(), Default::default());

    let max_iterations = func.body.blocks.len() * 20 + 100;
    let mut worklist: VecDeque<BlockId> = VecDeque::with_capacity(func.body.blocks.len());
    let mut in_worklist: FxHashSet<BlockId> =
        FxHashSet::with_capacity_and_hasher(func.body.blocks.len(), Default::default());
    for block in &func.body.blocks {
        if in_worklist.insert(block.id) {
            worklist.push_back(block.id);
        }
    }
    let mut iteration = 0;
    let positions = block_positions(func);
    let mut havoc = CallHavoc::new(func);

    // Phase 1: Ascending iteration with (threshold + delayed) widening.
    while let Some(block_id) = worklist.pop_front() {
        in_worklist.remove(&block_id);
        iteration += 1;
        if iteration > max_iterations {
            break;
        }
        // Trust (2026-10-02, trust-fixpoint-deadline): the ambient per-function
        // budget, once per pop; a trip refuses (see `fixpoint_budget_tripped`).
        if fixpoint_budget_tripped() {
            let mut refused = FixpointResult { block_states: states };
            refuse_everything(&mut refused);
            return (refused, havoc);
        }

        let Some(pos) = positions.get(&block_id) else {
            continue;
        };
        let block = &func.body.blocks[pos];

        let entry_state = states.get(&block_id).cloned().unwrap_or_else(IntervalDomain::bottom);
        if entry_state.is_unreachable {
            continue;
        }

        // Transfer through statements.
        let mut current = transfer_statements(&mut havoc, pos, block, entry_state);
        // Trust (P0): apply the TERMINATOR transfer (a `Call` havocs its dest +
        // every `&mut`-escaped local) before propagating, so a post-call read does
        // not inherit the stale pre-call interval.
        current = transfer_terminator(&mut havoc, pos, block, current);

        // Propagate to successors with condition narrowing.
        for_each_successor_state_owned(
            &block.terminator,
            func,
            block,
            current,
            |succ_id, succ_state| {
                let do_widen = widen_points.contains(&succ_id) && {
                    let count = block_iterations.entry(succ_id).or_insert(0);
                    *count += 1;
                    *count > config.widen_delay
                };

                let changed = if let Some(old) = states.get_mut(&succ_id) {
                    if do_widen {
                        match &config.thresholds {
                            Some(ts) => old.widen_with_thresholds_owned_in_place(succ_state, ts),
                            None => old.widen_owned_in_place(succ_state),
                        }
                    } else {
                        old.join_owned_in_place(succ_state)
                    }
                } else {
                    let mut fresh = IntervalDomain::bottom();
                    let c = if do_widen {
                        match &config.thresholds {
                            Some(ts) => fresh.widen_with_thresholds_owned_in_place(succ_state, ts),
                            None => fresh.widen_owned_in_place(succ_state),
                        }
                    } else {
                        fresh.join_owned_in_place(succ_state)
                    };
                    if c {
                        states.insert(succ_id, fresh);
                    }
                    c
                };

                if changed && in_worklist.insert(succ_id) {
                    worklist.push_back(succ_id);
                }
            },
        );
    }

    let mut result = FixpointResult { block_states: states };

    // Phase 2: Descending narrowing.
    if config.narrowing_passes > 0
        && !widen_points.is_empty()
        && apply_narrowing_pass(
            func,
            &mut result,
            &widen_points,
            config.narrowing_passes,
            &mut havoc,
        )
    {
        return (result, havoc);
    }

    // Phase 3: PROVE the answer is a post-fixpoint, and repair it where it is not.
    repair_to_post_fixpoint_with(func, &mut result, &mut havoc);

    // A trip inside the last unit's work (the havoc derivation and the statement
    // transfers' helpers poll too) is seen here: the answer of a run any trip
    // touched is the refusal.
    if trust_types::verify_budget::exhausted_readonly() {
        refuse_everything(&mut result);
    }
    (result, havoc)
}

/// Trust (2026-09-30, return-interval summary): the interval the return slot `_0`
/// holds at every `Return` of `func`, for EVERY input.
///
/// The production fixpoint (`type_aware_initial_state` + `fixpoint_configured`,
/// which ends in [`repair_to_post_fixpoint`]) over a clone with the preconditions
/// cleared, so no `requires` narrows an argument and the interval describes every
/// completed call. The repair pass checks propagation between blocks; the one
/// inclusion it does not check, that the entry block's state contains the initial
/// state, is checked here, over the union of both key sets (a missing entry is
/// Top). Each reachable `Return` block's entry state is carried through its own
/// statements and `_0`'s intervals are joined. A panicking path returns nothing,
/// so it constrains nothing here.
///
/// `None` when `_0` is not an integer the domain models, when no `Return` is
/// reachable, when the entry inclusion fails, or when the body is outside what the
/// domain tracks (`return_interval_admissible`).
///
/// `overflow_asserts_enforced` is whether this compilation keeps its overflow
/// asserts (`-C overflow-checks`); see [`SummaryPrecision`].
pub(crate) fn return_interval(
    func: &VerifiableFunction,
    overflow_asserts_enforced: bool,
) -> Option<Interval> {
    let _precision = SummaryPrecision::enter(overflow_asserts_enforced);
    let expanded = func.with_tail_calls_expanded();
    if !return_interval_admissible(expanded.as_ref()) {
        return None;
    }
    let mut probe = expanded.as_ref().clone();
    probe.preconditions.clear();
    let ret = probe
        .body
        .locals
        .first()
        .filter(|local| local.index == 0)
        .or_else(|| probe.body.locals.iter().find(|local| local.index == 0))?;
    type_to_interval(&ret.ty)?;
    let name = crate::local_var_name(&probe, ret);
    let initial = type_aware_initial_state(&probe);
    // Merge 2026-10-14: the run's havoc index is kept so the Return blocks below are
    // walked by the same LOCKSTEP statement transfer the fixpoint ran
    // (`transfer_statements`), never by `transfer_function` alone.
    // PERF-COMPILER-VCGEN-769: skip `extract_thresholds` on acyclic bodies.
    let (fixpoint, mut havoc) = fixpoint_for_function_indexed(&probe, initial.clone());
    let entry = fixpoint.block_states.get(&probe.body.blocks.first()?.id)?;
    static RETURN_INTERVAL_DEBUG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if *RETURN_INTERVAL_DEBUG
        .get_or_init(|| crate::trust_vcgen_env_var_present("TRUST_RETURN_INTERVAL_DEBUG"))
    {
        eprintln!("TRUST_RETURN_INTERVAL: {} `{name}` initial={initial:?}", probe.def_path);
        for (id, state) in &fixpoint.block_states {
            eprintln!("TRUST_RETURN_INTERVAL:   {id:?} {state:?}");
        }
    }
    if entry.is_unreachable
        || initial.vars.iter().any(|(v, init_iv)| !init_iv.leq(&entry.get(v)))
        || entry
            .vars
            .iter()
            .any(|(v, entry_iv)| !initial.vars.contains_key(v) && !Interval::TOP.leq(entry_iv))
    {
        return None;
    }
    let mut joined: Option<Interval> = None;
    for (pos, block) in probe.body.blocks.iter().enumerate() {
        if !matches!(block.terminator, Terminator::Return) {
            continue;
        }
        let state = fixpoint.block_states.get(&block.id)?;
        if state.is_unreachable {
            continue;
        }
        let current = transfer_statements(&mut havoc, pos, block, state.clone());
        let at_return = current.get(&name);
        joined = Some(joined.map_or(at_return, |j| j.join(&at_return)));
    }
    joined.filter(|interval| !interval.is_bottom())
}

/// Trust (2026-10-01, payload return-interval summary): for a function returning a
/// std `Option<iN>` or `Result<iN, E>`, the variant index of its payload arm
/// (`Some` = 1, `Ok` = 0), the interval that arm's integer payload lies in on
/// EVERY completed call, for every input, and the payload type's own range.
///
/// [`return_interval`]'s fixpoint and gates (the same admissibility, the cleared
/// preconditions, the entry inclusion, the summary precision scope), with one
/// structural premise in place of `_0` being an integer: EVERY write to `_0` in the
/// body is a whole aggregate of the return ADT (no projected or opaque write, no
/// call writing it, no move from another local). The payload a caller can observe
/// is then the operand of some payload-arm aggregate executed on its path, so the
/// join of each such operand's interval, at its own statement, over every reachable
/// block contains it. A block holding a payload site with no fixpoint state refuses.
///
/// Sweep A6 (m21, r06b, c42): `let h = digit(hi)?; let l = digit(lo)?; h * 10 + l`
/// with `digit` returning `Some(c)` under `c <= 9`.
pub(crate) fn return_payload_interval(
    func: &VerifiableFunction,
    overflow_asserts_enforced: bool,
) -> Option<(usize, Interval, Interval)> {
    let _precision = SummaryPrecision::enter(overflow_asserts_enforced);
    let expanded = func.with_tail_calls_expanded();
    if !return_interval_admissible(expanded.as_ref()) {
        return None;
    }
    let mut probe = expanded.as_ref().clone();
    probe.preconditions.clear();
    let ret = probe
        .body
        .locals
        .first()
        .filter(|local| local.index == 0)
        .or_else(|| probe.body.locals.iter().find(|local| local.index == 0))?;
    let Ty::Adt { name: adt, variants, .. } = &ret.ty else { return None };
    let (variant, arm) = match adt.as_str() {
        "core::option::Option" | "std::option::Option" => (1, "Some"),
        "core::result::Result" | "std::result::Result" => (0, "Ok"),
        _ => return None,
    };
    let payload_variant = variants.get(variant).filter(|v| v.name == arm)?;
    let [(_, payload_ty)] = payload_variant.fields.as_slice() else { return None };
    if !matches!(payload_ty, Ty::Int { .. }) {
        return None;
    }
    let type_range = type_to_interval(payload_ty)?;
    for block in &probe.body.blocks {
        for stmt in &block.stmts {
            match stmt.local_write(0) {
                LocalWrite::Untouched => {}
                LocalWrite::WholeNamed(Rvalue::Aggregate(AggregateKind::Adt { name, .. }, _))
                    if name == adt => {}
                _ => return None,
            }
        }
        if !matches!(block.terminator.local_write(0), LocalWrite::Untouched) {
            return None;
        }
    }
    let initial = type_aware_initial_state(&probe);
    // Merge 2026-10-14: walked by the LOCKSTEP statement transfer, as above.
    // PERF-COMPILER-VCGEN-769: skip `extract_thresholds` on acyclic bodies.
    let (fixpoint, mut havoc) = fixpoint_for_function_indexed(&probe, initial.clone());
    let entry = fixpoint.block_states.get(&probe.body.blocks.first()?.id)?;
    if entry.is_unreachable
        || initial.vars.iter().any(|(v, init_iv)| !init_iv.leq(&entry.get(v)))
        || entry
            .vars
            .iter()
            .any(|(v, entry_iv)| !initial.vars.contains_key(v) && !Interval::TOP.leq(entry_iv))
    {
        return None;
    }
    fn payload_site<'a>(stmt: &'a Statement, adt: &str, variant: usize) -> Option<&'a Operand> {
        match stmt {
            Statement::Assign {
                place,
                rvalue: Rvalue::Aggregate(AggregateKind::Adt { name, variant: v, .. }, ops),
                ..
            } if place.local == 0
                && place.projections.is_empty()
                && name == adt
                && *v == variant
                && ops.len() == 1 =>
            {
                ops.first()
            }
            _ => None,
        }
    }
    let is_payload_site = |stmt| payload_site(stmt, adt, variant);
    let mut joined: Option<Interval> = None;
    for (pos, block) in probe.body.blocks.iter().enumerate() {
        if !block.stmts.iter().any(|stmt| is_payload_site(stmt).is_some()) {
            continue;
        }
        let state = fixpoint.block_states.get(&block.id)?;
        if state.is_unreachable {
            continue;
        }
        let probe_ref = &probe;
        let _ = transfer_statements_observed(
            &mut havoc,
            pos,
            block,
            state.clone(),
            |stmt, _, before, _| {
                if before.is_unreachable {
                    return;
                }
                if let Some(op) = payload_site(stmt, adt, variant) {
                    let at_site = operand_to_interval(op, probe_ref, before);
                    joined = Some(joined.map_or(at_site, |j| j.join(&at_site)));
                }
            },
        );
    }
    joined.filter(|interval| !interval.is_bottom()).map(|interval| (variant, interval, type_range))
}

/// Trust (2026-09-30, round 10 of the review): whether every write in `func` is one
/// the interval domain sees, so the state it holds at a `Return` is a fact about
/// the call. Inside one function a stale interval is mostly harmless, because the
/// VC lanes version what they read; exported as a summary it is read by every
/// caller, and round 10 measured callers PROVED, kernel-certified, that panicked
/// through each shape refused here:
///  * a raw address, or a `&mut` used for anything but a direct call argument, of
///    any place: a write through it reaches a local the domain cannot name
///    (`let r = if c { &mut x } else { &mut y }; *r = 200`, `Some(&mut x)`, `**rr`),
///    and a guard holding one writes on drop. A `&mut` handed straight to a call
///    (`Iterator::next(&mut it)` in every `for` loop) is kept: every call havocs
///    each mutably borrowed local (`terminator_def_names`);
///  * a raw-pointer local: two raw pointers may alias, and the domain names each
///    pointee separately;
///  * a `u128` local: the domain's range for it stops at `i128::MAX`
///    (`type_to_interval`), which excludes real values;
///  * a `Drop` (a destructor can write memory) or an inline-asm terminator, and any
///    statement that writes memory or a discriminant outside an assignment;
///  * a union anywhere in a local's type (round 11): a write to one field does not
///    rebind its overlapping siblings (`u.a = 5; u.b = v; u.a` kept `[5, 5]`).
fn return_interval_admissible(func: &VerifiableFunction) -> bool {
    let local_ok = |ty: &Ty| {
        !matches!(ty, Ty::RawPtr { .. } | Ty::Int { width: 128, signed: false })
            && !ty_mentions_union(ty, 0)
    };
    if !func.body.locals.iter().all(|local| local_ok(&local.ty)) {
        return false;
    }
    func.body.blocks.iter().enumerate().all(|(block_index, block)| {
        let statements_ok = block.stmts.iter().enumerate().all(|(stmt_index, stmt)| match stmt {
            Statement::Assign { rvalue: Rvalue::AddressOf(..), .. } => false,
            Statement::Assign { place, rvalue: Rvalue::Ref { mutable: true, .. }, .. } => {
                place.projections.is_empty()
                    && mutable_borrow_only_passed_to_calls(
                        func,
                        place.local,
                        (block_index, stmt_index),
                    )
            }
            Statement::Assign { .. }
            | Statement::StorageLive(_)
            | Statement::StorageDead(_)
            | Statement::Nop
            | Statement::Coverage
            | Statement::ConstEvalCounter
            | Statement::PlaceMention(_)
            | Statement::Retag { .. } => true,
            _ => false,
        });
        statements_ok
            && !matches!(block.terminator, Terminator::Drop { .. } | Terminator::Opaque { .. })
    })
}

/// Whether the `&mut` borrow into `local` (defined at `def`) is used for nothing but
/// being passed, as itself, to calls: no other statement mentions `local` (storage
/// markers aside), and no terminator does except as a bare `move`/`copy` call
/// argument. Then only the callee can write through it, and the call havocs the
/// borrowed place with every other mutably borrowed local.
fn mutable_borrow_only_passed_to_calls(
    func: &VerifiableFunction,
    local: usize,
    def: (usize, usize),
) -> bool {
    func.body.blocks.iter().enumerate().all(|(block_index, block)| {
        let statements_ok = block.stmts.iter().enumerate().all(|(stmt_index, stmt)| {
            (block_index, stmt_index) == def
                || matches!(stmt, Statement::StorageLive(l) | Statement::StorageDead(l) if *l == local)
                || !crate::contracts::statement_mentions_local_anywhere(stmt, local)
        });
        let terminator_ok = match &block.terminator {
            Terminator::Call { args, dest, .. } => {
                !crate::contracts::place_mentions_local_anywhere(dest, local)
                    && args.iter().all(|arg| match arg {
                        Operand::Copy(place) | Operand::Move(place)
                            if place.local == local && place.projections.is_empty() =>
                        {
                            true
                        }
                        other => !crate::contracts::operand_mentions_local_anywhere(other, local),
                    })
            }
            other => !crate::contracts::terminator_mentions_local_anywhere(other, local),
        };
        statements_ok && terminator_ok
    })
}

/// Whether `ty` holds a union anywhere, through fields, elements, references and
/// captures. A type whose structure is hidden answers yes (fail closed): a recursive
/// type's cut point (`Ty::Datatype` with no variants; round 12 found a union behind
/// the marker of a recursive `RNode`), a type lowering gave up on (`Ty::Unsupported`;
/// round 13 found a union inside a struct past the node budget), and a coroutine,
/// whose state holds its captures. So does anything past a depth of 32.
fn ty_mentions_union(ty: &Ty, depth: usize) -> bool {
    if depth > 32 {
        return true;
    }
    let inner = |ty: &Ty| ty_mentions_union(ty, depth + 1);
    match ty {
        Ty::Adt { adt_kind: Some(trust_types::AdtKind::Union), .. } => true,
        Ty::Adt { fields, variants, .. } => {
            fields.iter().any(|(_, field)| inner(field))
                || variants.iter().any(|variant| variant.fields.iter().any(|(_, f)| inner(f)))
        }
        Ty::Datatype { variants, .. } => {
            variants.is_empty()
                || variants.iter().any(|(_, fields)| fields.iter().any(|(_, f)| inner(f)))
        }
        Ty::Unsupported { .. } | Ty::Coroutine { .. } => true,
        Ty::Tuple(elems) => elems.iter().any(inner),
        Ty::Closure { upvars, .. } => upvars.iter().any(inner),
        Ty::Ref { inner: pointee, .. } | Ty::RawPtr { pointee, .. } => inner(pointee),
        Ty::Array { elem, .. }
        | Ty::SymArray { elem, .. }
        | Ty::Slice { elem }
        | Ty::Seq { elem, .. } => inner(elem),
        _ => false,
    }
}

/// How many repair rounds to run before widening everything still growing.
/// Each round strictly increases the set of Top-valued entries, so this bound is
/// only a guard against pathological CFGs, not a correctness parameter.
const POST_FIXPOINT_REPAIR_ROUNDS: usize = 8;

/// Verify the converged result IS a post-fixpoint, and widen to Top wherever it
/// is not.
///
/// THE PROPERTY EVERY CONSUMER ASSUMES. A block state is only a sound
/// over-approximation if propagating once more cannot GROW it. The ascending
/// phase is supposed to guarantee that, and it does — as long as every transfer
/// on the way is monotone.
///
/// IT IS NOT GUARANTEED, AND THE FAILURE IS SILENT. Measured 2026-09-18 while
/// making the interval domain track a `CheckedBinaryOp`'s result field: with
/// threshold widening, a branch narrowing that starts biting one round earlier
/// can hand a successor a SMALLER state than the previous round, and the
/// iteration settles below the true fixpoint. On
/// `loop { r += 1; if r > 5 { break; } }` the loop head came out as `[0, 4]`
/// while 5 is plainly reachable, and the loop EXIT came out BOTTOM on a loop
/// that terminates. An environment that excludes a reachable state is the
/// false-proof direction: it can discharge an obligation the runtime violates.
///
/// That change was reverted. This pass is the durable answer, because the next
/// such interaction will not announce itself either.
///
/// SOUNDNESS: the only repair is raising an entry to Top, which is the lattice
/// identity and contains every value, so this pass can only WEAKEN the result.
/// It can turn a proof into a non-proof and can never create one. When a round
/// finds nothing growing, the result is a post-fixpoint by definition.
///
/// Trust (2026-10-02, trust-fixpoint-deadline): it polls the ambient budget once per
/// block, and a trip answers with what the pass already answers when its round
/// bound runs out — every entry dropped ([`refuse_everything`]). `havoc` is the
/// fixpoint run's call-havoc index ([`CallHavoc`]), shared with its ascending and
/// narrowing phases.
fn repair_to_post_fixpoint_with(
    func: &VerifiableFunction,
    result: &mut FixpointResult,
    havoc: &mut CallHavoc<'_>,
) {
    for _ in 0..POST_FIXPOINT_REPAIR_ROUNDS {
        let mut grew: FxHashMap<BlockId, Vec<String>> = FxHashMap::default();
        for (pos, block) in func.body.blocks.iter().enumerate() {
            if fixpoint_budget_tripped() {
                refuse_everything(result);
                return;
            }
            let Some(entry) = result.block_states.get(&block.id) else { continue };
            if entry.is_unreachable {
                continue;
            }
            let mut current = transfer_statements(havoc, pos, block, entry.clone());
            current = transfer_terminator(havoc, pos, block, current);
            for_each_successor_state_owned(
                &block.terminator,
                func,
                block,
                current,
                |succ_id, succ_state| {
                    let Some(stored) = result.block_states.get(&succ_id) else { return };
                    if succ_state.is_unreachable {
                        return;
                    }
                    if stored.is_unreachable {
                        // A successor recorded unreachable that a reachable
                        // predecessor propagates into is the same defect one step
                        // over: the whole state grew from bottom.
                        grew.entry(succ_id)
                            .or_default()
                            .extend(succ_state.vars.into_keys().chain(stored.vars.keys().cloned()));
                        return;
                    }
                    // Compare over the UNION of both key sets. A variable that grew
                    // all the way to Top is ABSENT from the propagated state — this
                    // domain stores only non-Top entries — so iterating the
                    // propagated state alone misses exactly the largest growth
                    // there is. Measured: the first cut of this pass repaired the
                    // loop head and left two blocks still holding an interval that
                    // excluded a reachable value.
                    for (name, stored_interval) in &stored.vars {
                        if !succ_state.vars.contains_key(name)
                            && !Interval::TOP.leq(stored_interval)
                        {
                            grew.entry(succ_id).or_default().push(name.clone());
                        }
                    }
                    for (name, succ_interval) in succ_state.vars {
                        if !succ_interval.leq(&stored.get(&name)) {
                            grew.entry(succ_id).or_default().push(name);
                        }
                    }
                },
            );
        }
        if grew.is_empty() {
            return;
        }
        for (block_id, names) in grew {
            let Some(state) = result.block_states.get_mut(&block_id) else { continue };
            state.is_unreachable = false;
            for name in names {
                state.vars.remove(&name);
            }
        }
    }
    // Still growing after the bound: drop every tracked entry, which is Top for
    // every variable and therefore the safest answer this pass can give.
    refuse_everything(result);
}

/// [`repair_to_post_fixpoint_with`] on its own, with a fresh call-havoc index: the
/// pass as the tests run it on an already-converged result. Production always runs
/// it inside [`fixpoint_configured`], sharing that run's index.
#[cfg(test)]
pub(crate) fn repair_to_post_fixpoint(func: &VerifiableFunction, result: &mut FixpointResult) {
    repair_to_post_fixpoint_with(func, result, &mut CallHavoc::new(func));
}

/// Compute fixpoint with a narrowing pass for precision recovery.
///
/// This is the backward-compatible entry point. New code should prefer
/// `fixpoint_configured()` with `FixpointConfig::for_function()`.
///
/// Now delegates to `fixpoint_configured()` with threshold widening,
/// delayed widening, and condition narrowing from SwitchInt.
#[must_use]
pub fn fixpoint_with_narrowing(
    func: &VerifiableFunction,
    initial: IntervalDomain,
    narrow_iterations: usize,
) -> FixpointResult {
    fixpoint_with_auto_thresholds_indexed(func, initial, 3, narrow_iterations).0
}

// ── Invariant Extraction ───────────────────────────────────────────────────

/// Extract loop invariant formulas from fixpoint results.
///
/// For each variable with a finite interval at a loop header, generates
/// bound constraints: `lo <= var` and `var <= hi`.
#[must_use]
pub fn extract_invariants(result: &FixpointResult, func: &VerifiableFunction) -> Vec<Formula> {
    let widen_points: FxHashSet<BlockId> =
        detect_widen_points(func).into_iter().map(|wp| wp.block).collect();

    let mut invariants = Vec::new();

    for block_id in &widen_points {
        let Some(state) = result.block_states.get(block_id) else {
            continue;
        };
        if state.is_unreachable {
            continue;
        }

        for (var_name, interval) in &state.vars {
            if interval.is_bottom() {
                continue;
            }
            match (interval.lo != i128::MIN, interval.hi != i128::MAX) {
                (true, true) => {
                    let var_formula = Formula::Var(var_name.clone(), Sort::Int);
                    invariants.push(Formula::Ge(
                        Box::new(var_formula.clone()),
                        Box::new(Formula::Int(interval.lo)),
                    ));
                    invariants.push(Formula::Le(
                        Box::new(var_formula),
                        Box::new(Formula::Int(interval.hi)),
                    ));
                }
                (true, false) => {
                    let var_formula = Formula::Var(var_name.clone(), Sort::Int);
                    invariants.push(Formula::Ge(
                        Box::new(var_formula),
                        Box::new(Formula::Int(interval.lo)),
                    ));
                }
                (false, true) => {
                    let var_formula = Formula::Var(var_name.clone(), Sort::Int);
                    invariants.push(Formula::Le(
                        Box::new(var_formula),
                        Box::new(Formula::Int(interval.hi)),
                    ));
                }
                (false, false) => {}
            }
        }
    }

    invariants
}

// ── Narrowing Conditions ───────────────────────────────────────────────────

/// Whether the branch being taken means the discriminant's defining comparison
/// evaluated TRUE. `arm` is `Some(label)` for a match arm and `None` for the
/// `otherwise` edge.
///
/// Only a BOOL discriminant has a truth value, and only the two-way shape
/// rustc emits for a condition (`targets == [(0, false_block)]`, otherwise the
/// true block, or its mirror) can be read. Anything else returns `None` and
/// nothing is narrowed.
pub(crate) fn branch_truth(
    func: &VerifiableFunction,
    discr: &Operand,
    arm: Option<u128>,
    targets: &[(u128, BlockId)],
) -> Option<bool> {
    let is_bool = matches!(crate::operand_ty_cow(func, discr).as_deref(), Some(Ty::Bool));
    branch_truth_with_bool(is_bool, arm, targets)
}

#[inline]
fn branch_truth_with_bool(
    is_bool: bool,
    arm: Option<u128>,
    targets: &[(u128, BlockId)],
) -> Option<bool> {
    if !is_bool {
        return None;
    }
    match arm {
        // An explicit arm states the discriminant's value directly.
        Some(0) => Some(false),
        Some(1) => Some(true),
        Some(_) => None,
        // The `otherwise` edge is the complement, and it is readable only when
        // the arms cover exactly one of the two truth values.
        None => match targets {
            [(0, _)] => Some(true),
            [(1, _)] => Some(false),
            _ => None,
        },
    }
}

/// The order comparison that DEFINES a `SwitchInt` discriminant, when the
/// branch can be read back through it onto the compared operands.
///
/// CONSERVATIVE BY CONSTRUCTION: the comparison must be the LAST statement of
/// the switching block. Nothing can then reassign the discriminant or either
/// operand between the comparison and the branch, so the intervals narrowed
/// below belong to exactly the values compared, and no reaching-definition
/// analysis is needed to establish it. rustc emits this shape for `if a < b`
/// and for a `loop`'s `break` test, which is what this exists to reach.
///
/// Equality is excluded. `Eq` would need a meet on both operands and `Ne` can
/// narrow only at an interval edge; neither is needed by the shapes this
/// serves, and an unneeded arm here is an unneeded way to be wrong.
pub(crate) fn discriminant_defining_comparison<'b>(
    block: &'b BasicBlock,
    discr: &Operand,
) -> Option<(BinOp, &'b Operand, &'b Operand)> {
    let (Operand::Copy(place) | Operand::Move(place)) = discr else { return None };
    if !place.projections.is_empty() {
        return None;
    }
    let Statement::Assign { place: dest, rvalue: Rvalue::BinaryOp(op, lhs, rhs), .. } =
        block.stmts.last()?
    else {
        return None;
    };
    if !dest.projections.is_empty() || dest.local != place.local {
        return None;
    }
    matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge).then_some((*op, lhs, rhs))
}

/// Read a taken branch BACK ONTO the operands of the comparison that produced
/// its discriminant.
///
/// `narrow_from_condition` pins the discriminant's own interval, which is the
/// bool temp and carries nothing useful — bools are deliberately untracked by
/// this domain. Without this step the fact never reaches the values actually
/// compared, and that omission is what made
/// `loop { r += 1; if r > 5 { break; } }` report a FALSE REFUTATION of its
/// overflow check: `r` was unconstrained at the loop head, so the solver
/// witnessed `r == u32::MAX`, a state the loop cannot reach. The `while`
/// spelling of the same program proves, because there the guard dominates the
/// increment and an ordinary path condition suffices.
///
/// SOUNDNESS. The narrowing states only what the taken edge guarantees. `taken`
/// is `None` for anything but the two-way bool shape, and the comparison must
/// be the block's last statement, so no intervening write can make the narrowed
/// interval belong to a different value. Both new bounds are computed from the
/// ORIGINAL intervals, never from an already-narrowed one. Only place operands
/// are written back; a constant cannot be narrowed.
/// Trust (2026-10-09): on the branch where a genuine std ascii predicate over a
/// stable whole `u8`/`char` local HELD, meet that local with the predicate's hull
/// (`crate::guards::ascii_predicate_tested_hull`). The predicate's definition is
/// the codepoint set, so the meet is exact up to the hull; the other branch learns
/// nothing (the complement is not an interval).
fn narrow_through_ascii_predicate_cached(
    result: &mut IntervalDomain,
    func: &VerifiableFunction,
    discr: &Operand,
    taken: Option<bool>,
    cache: &mut Option<Option<(Operand, i128, i128)>>,
) {
    if taken != Some(true) {
        return;
    }
    let hull = cache.get_or_insert_with(|| crate::guards::ascii_predicate_tested_hull(func, discr));
    let Some((tested, lo, hi)) = hull.as_ref() else {
        return;
    };
    let current = operand_to_interval(tested, func, result);
    if current.is_bottom() {
        return;
    }
    narrow_place_operand(result, func, tested, current.meet(&Interval::new(*lo, *hi)));
}

fn narrow_through_comparison_precomputed(
    result: &mut IntervalDomain,
    func: &VerifiableFunction,
    block: &BasicBlock,
    defining_cmp: Option<(BinOp, &Operand, &Operand)>,
    taken: Option<bool>,
) {
    let Some(taken) = taken else { return };
    let Some((op, lhs, rhs)) = defining_cmp else { return };
    // The negation of an order comparison is the opposite order: `!(a > b)` is
    // `a <= b`. Then normalise `>`/`>=` by swapping the operands, so only the
    // two `<`/`<=` cases have to be reasoned about below.
    let op = if taken { op } else { negate_order_comparison(op) };
    let (op, lhs, rhs) = match op {
        BinOp::Gt => (BinOp::Lt, rhs, lhs),
        BinOp::Ge => (BinOp::Le, rhs, lhs),
        other => (other, lhs, rhs),
    };
    let (l, r) = (operand_to_interval(lhs, func, result), operand_to_interval(rhs, func, result));
    if l.is_bottom() || r.is_bottom() {
        return;
    }
    // `a < b` gives `a <= hi(b) - 1` and `b >= lo(a) + 1`; `a <= b` gives
    // `a <= hi(b)` and `b >= lo(a)`. Saturating, so an unbounded peer leaves
    // the bound untouched instead of wrapping.
    let (l_hi, r_lo) = match op {
        BinOp::Lt => (r.hi.saturating_sub(1), l.lo.saturating_add(1)),
        BinOp::Le => (r.hi, l.lo),
        _ => return,
    };
    let (l_new, r_new) = (Interval::new(l.lo, l.hi.min(l_hi)), Interval::new(r.lo.max(r_lo), r.hi));
    narrow_place_operand(result, func, lhs, l_new);
    narrow_place_operand(result, func, rhs, r_new);
    // Trust (2026-09-30): rustc compares a mutable local through a fresh copy
    // (`_6 = copy i; _5 = Lt(move _6, 10)`), and narrowing only the copy leaves the
    // local itself at its type range. Inside the return-interval summary only
    // (`SummaryPrecision`), narrow the copy's source too — see
    // `comparison_copy_source`. In the production environment it was measured to
    // cost a bound: `while i >= 16 { i = i / 2 }` then settles below the fixpoint
    // at the loop head and the repair gives `i` up to Top (round 10).
    if summary_precision() {
        for (operand, narrowed) in [(lhs, l_new), (rhs, r_new)] {
            if let Some(source) = comparison_copy_source(block, operand) {
                let current = result.get(&crate::place_to_var_name(func, source));
                narrow_place(result, func, source, narrowed.meet(&current));
            }
        }
    }
}

/// Trust (2026-09-30): the local a comparison operand is a plain copy of, when
/// the copy is one of the (at most two) statements directly before the comparison,
/// storage markers aside, and only other such copies stand between them. Each copy writes a whole
/// temporary from a whole local, and no copy in the run writes a local another
/// one reads, so the source still holds the compared value at the end of the
/// block, which is the state the branch narrows.
fn comparison_copy_source<'b>(block: &'b BasicBlock, operand: &Operand) -> Option<&'b Place> {
    let (Operand::Copy(temp) | Operand::Move(temp)) = operand else { return None };
    if !temp.projections.is_empty() {
        return None;
    }
    let before_cmp = block.stmts.len().checked_sub(1)?;
    // Storage markers write no value, and rustc places one between two operand
    // copies (`_8 = copy lim; StorageLive(_9); _9 = copy n`).
    let mut iter = block.stmts[..before_cmp]
        .iter()
        .rev()
        .filter(|stmt| !matches!(stmt, Statement::StorageLive(_) | Statement::StorageDead(_)))
        .take(2)
        .map_while(|stmt| match stmt {
            Statement::Assign {
                place: dest,
                rvalue: Rvalue::Use(Operand::Copy(src) | Operand::Move(src)),
                ..
            } if dest.projections.is_empty() && src.projections.is_empty() => Some((dest, src)),
            _ => None,
        });
    let run = [iter.next(), iter.next()];
    if run
        .iter()
        .flatten()
        .any(|(_, src)| run.iter().flatten().any(|(dest, _)| dest.local == src.local))
    {
        return None;
    }
    run.iter().flatten().find(|(dest, _)| dest.local == temp.local).map(|(_, src)| *src)
}

/// Trust (2026-10-05, NEG-WRAP-OFF-1): read the success edge of an
/// `Assert(OverflowNeg)` back onto the negated value. rustc lowers a checked `-x`
/// as `_c = Eq(x, const MIN); assert(!move _c) -> target; target: _d = Neg(x)`, so
/// the edge guarantees `x != MIN`, which an interval can state exactly when `MIN`
/// is its lower bound: raise it to `MIN + 1` (an `x` pinned to `MIN` leaves the
/// edge unreachable, `BOTTOM`).
///
/// CONSERVATIVE BY CONSTRUCTION, as [`discriminant_defining_comparison`]: the
/// `Eq` must be the block's LAST statement and define the asserted local, one side
/// a place of a SIGNED machine-integer type and the other the constant that type's
/// `MIN` — anything else narrows nothing (the edge then propagates unchanged, the
/// prior behavior).
fn narrow_past_overflow_neg_assert(
    result: &mut IntervalDomain,
    func: &VerifiableFunction,
    block: &BasicBlock,
    cond: &Operand,
) {
    let (Operand::Copy(flag) | Operand::Move(flag)) = cond else { return };
    if !flag.projections.is_empty() {
        return;
    }
    let Some(Statement::Assign {
        place: dest, rvalue: Rvalue::BinaryOp(BinOp::Eq, lhs, rhs), ..
    }) = block.stmts.last()
    else {
        return;
    };
    if !dest.projections.is_empty() || dest.local != flag.local {
        return;
    }
    let (value, constant) = match (lhs, rhs) {
        (Operand::Copy(_) | Operand::Move(_), Operand::Constant(ConstValue::Int(k))) => (lhs, *k),
        (Operand::Constant(ConstValue::Int(k)), Operand::Copy(_) | Operand::Move(_)) => (rhs, *k),
        _ => return,
    };
    let (Operand::Copy(place) | Operand::Move(place)) = value else { return };
    let width = match crate::place_ty_cow(func, place).as_deref() {
        Some(Ty::Int { width, signed: true }) => *width,
        Some(Ty::PtrSizedInt { signed: true }) => 64,
        _ => return,
    };
    let Some((type_min, _)) = super::discharge::type_bounds(&Ty::Int { width, signed: true })
    else {
        return;
    };
    if constant != type_min {
        return;
    }
    let current = operand_to_interval(value, func, result);
    if current.is_bottom() || current.lo > type_min {
        return;
    }
    narrow_place_operand(result, func, value, Interval::new(type_min + 1, current.hi));
}

/// The negation of an order comparison.
pub(crate) fn negate_order_comparison(op: BinOp) -> BinOp {
    match op {
        BinOp::Lt => BinOp::Ge,
        BinOp::Le => BinOp::Gt,
        BinOp::Gt => BinOp::Le,
        BinOp::Ge => BinOp::Lt,
        other => other,
    }
}

/// Write a narrowed interval back, but only for a PLACE operand — a constant
/// has no binding to narrow. An empty result is recorded as `BOTTOM`, which is
/// this domain's own spelling for an unreachable edge.
fn narrow_place_operand(
    result: &mut IntervalDomain,
    func: &VerifiableFunction,
    operand: &Operand,
    narrowed: Interval,
) {
    let (Operand::Copy(place) | Operand::Move(place)) = operand else { return };
    narrow_place(result, func, place, narrowed);
}

fn narrow_place(
    result: &mut IntervalDomain,
    func: &VerifiableFunction,
    place: &Place,
    narrowed: Interval,
) {
    let place_ty = crate::place_ty_cow(func, place);
    // Trust (2026-10-10, review round 115): a `u128` has no interval here (see
    // `operand_reads_u128`); a branch against a literal past `i128::MAX` reads that
    // literal as Top and would cap the place below its real value.
    if matches!(place_ty.as_deref(), Some(Ty::Int { width: 128, signed: false })) {
        return;
    }
    // Intersect with the place's OWN type range before storing.
    //
    // Without this the narrowing states only the half the branch gave it: a
    // previously-untracked `u32` starts at Top, so `!(x > 5)` stores
    // `[i128::MIN, 5]`. That is sound, and it is also poison — a later
    // `y = x` copies the unknown lower bound onto `y`, and every join `y`
    // takes part in inherits it, which is exactly how the loop counter in
    // `loop { r += 1; if r > 5 { break; } }` ended up with an `i128` lower
    // bound on a `u32`. A value of type `u32` is in `[0, u32::MAX]` wherever
    // it is a value at all, so the meet is sound and it keeps the bound the
    // branch actually established.
    let bounded =
        match place_ty.as_deref().and_then(super::discharge::type_bounds) {
            Some((lo, hi)) => narrowed.meet(&Interval::new(lo, hi)),
            None => narrowed,
        };
    let name = crate::place_to_var_name(func, place);
    if bounded.is_bottom() {
        result.set(name, Interval::BOTTOM);
    } else {
        result.set(name, bounded);
    }
}

/// Narrow an interval domain in place based on a branch condition being true.
///
/// For comparisons like `x < 10`, narrows x's interval to [lo, 9].
fn narrow_from_condition_in_place(
    result: &mut IntervalDomain,
    discr_ty: Option<&Ty>,
    discr_place_name: Option<&str>,
    value: u128,
) {
    // Decode the raw arm label under the discriminant's declared type before
    // pinning the interval to it — `Interval::constant(4294967295)` for an
    // `i32` `-1` arm is a WRONG (and, against the type's own range, empty)
    // narrowing. An undecodable label leaves the interval untouched.
    if let (Some(ty), Some(name)) = (discr_ty, discr_place_name)
        && let Some(v) = interval_switch_label(ty, value)
    {
        result.set(name.to_string(), Interval::constant(v));
    }
}

//! Trust (2026-10-03): a std/core/alloc FUNCTION ITEM handed to generic code as a
//! value — bare (`o.unwrap_or_else(std::thread::park)`) or inside a forwarding
//! wrapper (`o.unwrap_or_else(AssertUnwindSafe(std::thread::current))`) — under a
//! policy that tolerates no runtime-checked row: `-Ztrust-policy=certify` and
//! `-Ztrust-policy=memory-safe`.
//!
//! ## The hole
//!
//! The item is called INSIDE the generic code, through its `FnOnce` shim
//! (`<fn() -> Thread {current} as FnOnce<()>>::call_once`), where no row of the
//! calling function is guaranteed to charge it. The indirect-call gate
//! (`function_has_unresolved_indirect_call`) asks each such item
//! (`forwarded_callable_is_unresolved`), and for a foreign one it asked
//! `foreign_fn_item_type_arg_is_accounted`, whose second arm admits any item of
//! the tolerated VANILLA-SYSROOT class (`callee_is_vanilla_sysroot`, outside
//! vcgen's call-site panic families). That arm is the default policy's standard: an
//! absent sysroot callee at foundational types is charged a `runtime_checked` row
//! that policy B reports and builds. It is not certify's or memory-safe's: both
//! refuse that row. The gate applied it on every policy.
//!
//! MEASURED on a stage 1 of `6011b74bad` (main `77e5f14c07` plus the wave-9
//! commits; flags `--edition 2021 -Ztrust-verify=on --crate-type lib
//! --emit=metadata`), exit 0 under certify, memory-safe AND strict:
//!  * `o.unwrap_or_else(AssertUnwindSafe(std::thread::current))`, and the same
//!    with `std::time::Instant::now` and `RandomState::new`;
//!  * `o.unwrap_or_else(std::thread::park)`, `o.unwrap_or_else(std::thread::yield_now)`
//!    (`o: Option<()>`) and `o.map(std::thread::sleep)` (`o: Option<Duration>`), no
//!    wrapper at all.
//!
//! None of these publishes a row for the item. Traced by the wave-9 scout on a stage
//! 1 of `782780ea0d` (not re-traced here): the wrapped call's absent-callee row
//! belonged to the bundled `<AssertUnwindSafe<_> as FnOnce<()>>::call_once`, which
//! the member-panic poison loop evicts, and the relowered root's closure-driving
//! consumer marker is bridge-local; the unit-returning bare forms reach the same
//! closure-driving path. The bare twin `o.unwrap_or_else(std::thread::current)`
//! is refused by certify and memory-safe (exit 1) only because its row survives:
//! `strip_generics` (`crates/trust-ir-bridge/src/lower.rs`) reads the `>` of the
//! item type's `->` as a closing bracket, so the consumer recognizer misses it and
//! the call falls to the absent-callee lane. A unit item type has no `->`, and inside
//! `AssertUnwindSafe<..>` the brackets rebalance. `std::thread::current` panics once
//! the thread's TLS is torn down (`init_current`), so certify accepted a call with a
//! real panic path that it refused one forwarding layer up.
//!
//! ## The rule
//!
//! [`foreign_callable_item_is_accounted`] is the gate's question for a FOREIGN item.
//! Under a policy that tolerates the vanilla-sysroot row
//! ([`policy_tolerates_vanilla_sysroot_row`]: the default `strict` policy and
//! advisory) it is `foreign_fn_item_type_arg_is_accounted`, unchanged. Under
//! `certify` and `memory-safe` it admits only what needs no tolerated row
//! ([`foreign_fn_item_is_structurally_accounted`]): a constructor (no body), or a
//! sysroot item whose own MIR `sysroot_fn_item_cannot_panic` shows unable to panic.
//! Everything else is unresolved, so the gate refuses the body (`skipped: 1`, "an
//! unresolved indirect call") with a note naming the item
//! ([`unaccounted_sysroot_callable_items`]).
//!
//! The rule is keyed on the item and the policy, never on whether a row happened to
//! survive the bridge, so the `strip_generics` accident decides nothing on these two
//! lanes: if that parse is fixed, `unwrap_or_else(std::thread::current)` stays
//! refused here.
//!
//! The vanilla arm stays on the default policy. There the wrapped and unit forms
//! still publish NO row while the bare twin publishes a `runtime_checked` one, so the
//! exit code agrees (policy B builds both) and the disclosure does not: that is
//! recorded as a residual (docs/KNOWN_HAZARDS.md), not closed here.
//!
//! ## What it costs
//!
//! A sysroot item the structural test cannot show total is refused as a callable on
//! these two lanes even when it IS total: `u32::count_ones` and `u32::swap_bytes`
//! (their bodies call an intrinsic, which the test does not follow),
//! `char::is_whitespace`, `str::to_owned`. A DIRECT call to the first two is accepted
//! by certify (the intrinsic is modeled); the callable form now is not. Measured with
//! the vanilla arm switched off (a `#[global_allocator]` in the crate makes every
//! sysroot item non-vanilla, which leaves exactly this rule): `<u32 as
//! Default>::default`, `u32::default`, `drop::<u32>`, `std::convert::identity`,
//! `String::new`, `Vec::new` and the constructor `Some` stay admitted. The same rule
//! also applies where other code asks the gate: memory-safe's classifier-skip
//! demotion (`uncharged_callable::memory_safe_skip_withheld`) is withheld for such a
//! body, and an `#[trust::assume_total]` body under these two policies that hands
//! such an item over is verified whole (`assume_total_cannot_cover_calls`) — an
//! over-refusal there, since that attribute assumes the body's panics away.
//! docs/DECISION_QUEUE.md "SYS-CALLABLE-1" records the costs and the recovery work.

use super::*;

/// Does `policy` tolerate the row a vanilla sysroot ABSENT callee is charged — the
/// `runtime_checked` absent-callee row `transport_row_is_vanilla_sysroot_absent_callee`
/// excuses? The default `strict` policy reports and builds it (completeness-gap
/// ruling B), and advisory fails nothing. `certify` demands full static discharge
/// (`TrustPolicy::requires_full_discharge`), and memory-safe admits only
/// compiler-marked assumption rows (`memory_safe_artifacts_have_non_demotable_failure`),
/// so both refuse it.
pub(super) fn policy_tolerates_vanilla_sysroot_row(policy: TrustPolicy) -> bool {
    !policy.requires_full_discharge() && !policy.is_memory_safe()
}

/// Is the FOREIGN function item `def_id` at `args` accounted for with NO tolerated
/// row: a constructor (an ADT or variant constructor has no body: it moves its
/// fields into a value), or an item of this compiler's sysroot whose own MIR cannot
/// panic (`sysroot_fn_item_cannot_panic`)? The first two arms of
/// `foreign_fn_item_type_arg_is_accounted`, which asks this first.
pub(super) fn foreign_fn_item_is_structurally_accounted<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: ty::GenericArgs<'tcx>,
) -> bool {
    matches!(tcx.def_kind(def_id), DefKind::Ctor(..))
        || (trust_mir_extract::def_is_in_real_sysroot_crate(tcx, def_id)
            && sysroot_fn_item_cannot_panic(
                tcx,
                def_id,
                args,
                SYSROOT_FN_ITEM_TOTALITY_DEPTH,
                &mut FxHashSet::default(),
            ))
}

/// The indirect-call gate's question for a FOREIGN function item that a callable
/// type argument hands over (`forwarded_callable_is_unresolved`): may it be treated
/// as accounted for under THIS session's policy? See the module doc.
pub(super) fn foreign_callable_item_is_accounted<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: ty::GenericArgs<'tcx>,
) -> bool {
    if policy_tolerates_vanilla_sysroot_row(tcx.sess.opts.unstable_opts.trust_policy) {
        return foreign_fn_item_type_arg_is_accounted(
            tcx,
            def_id,
            args,
            &mut FxHashMap::default(),
            HashTableCredit::Declared,
        );
    }
    let accounted = foreign_fn_item_is_structurally_accounted(tcx, def_id, args);
    if !accounted
        && trust_mir_extract::def_is_in_real_sysroot_crate(tcx, def_id)
        && env_flag_enabled("TRUST_VANILLA_DEBUG")
    {
        eprintln!(
            "[CALLABLE_TYPE_ARG] sysroot item `{}` is not shown unable to panic, and this \
             policy tolerates no runtime-checked row; not resolved",
            trust_mir_extract::safe_def_path_str_with_args(tcx, def_id, args),
        );
    }
    accounted
}

/// The std/core/alloc function items this body hands to a direct call as a
/// callable that the session's policy does NOT account for
/// ([`foreign_callable_item_is_accounted`]): each type argument of each direct call
/// is opened the way the gate opens it (`forwarded_callables`, then a sysroot
/// closure's parts, `uncharged_callable::sysroot_closure_callable_parts`). For the
/// refusal's NOTE only — it never decides a verdict. Empty under a policy that
/// tolerates the vanilla-sysroot row. Full paths, sorted and deduplicated.
pub(super) fn unaccounted_sysroot_callable_items<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Vec<String> {
    if policy_tolerates_vanilla_sysroot_row(tcx.sess.opts.unstable_opts.trust_policy) {
        return Vec::new();
    }
    let typing_env = body.typing_env(tcx);
    let mut items: Vec<DefId> = Vec::new();
    let mut visited: FxHashSet<Ty<'tcx>> = FxHashSet::default();
    for bb in body.basic_blocks.iter() {
        let Some(terminator) = &bb.terminator else { continue };
        let (TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. }) =
            &terminator.kind
        else {
            continue;
        };
        let ty::FnDef(_, args) = *func.ty(&body.local_decls, tcx).kind() else { continue };
        for arg in args.skip_binder().types() {
            collect_unaccounted_sysroot_items(tcx, typing_env, arg, &mut items, &mut visited);
        }
    }
    let mut paths: Vec<String> = items
        .into_iter()
        .map(|def_id| rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def_id)))
        .collect();
    paths.sort();
    paths.dedup();
    paths
}

/// [`unaccounted_sysroot_callable_items`] for one type argument, recursively through
/// a sysroot closure's parts, as `forwarded_callable_is_unresolved` recurses.
fn collect_unaccounted_sysroot_items<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    items: &mut Vec<DefId>,
    visited: &mut FxHashSet<Ty<'tcx>>,
) {
    if !visited.insert(ty) {
        return;
    }
    let mut callables = Vec::new();
    forwarded_callables(tcx, typing_env, ty, &mut callables);
    for callable in callables {
        match *callable.kind() {
            ty::FnDef(def_id, args)
                if !def_id.is_local()
                    && trust_mir_extract::def_is_in_real_sysroot_crate(tcx, def_id)
                    && !foreign_fn_item_is_structurally_accounted(
                        tcx,
                        def_id,
                        args.skip_binder(),
                    ) =>
            {
                items.push(def_id);
            }
            ty::Closure(..) | ty::CoroutineClosure(..) | ty::Coroutine(..) => {
                for part in uncharged_callable::sysroot_closure_callable_parts(tcx, callable)
                    .unwrap_or_default()
                {
                    collect_unaccounted_sysroot_items(tcx, typing_env, part, items, visited);
                }
            }
            _ => {}
        }
    }
}

/// The items [`unaccounted_sysroot_callable_items`] names, as a clause appended to
/// the "a function handed to generic code as a value" reason of a skip the gate
/// withholds (memory-safe's classifier skip, `#[trust::assume_total]`): empty when
/// there is none.
pub(super) fn unaccounted_sysroot_callable_clause<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> String {
    let items = unaccounted_sysroot_callable_items(tcx, body);
    if items.is_empty() {
        return String::new();
    }
    let quoted: Vec<String> = items.iter().map(|item| format!("`{item}`")).collect();
    format!(
        " — here {}, a std/core/alloc function this policy admits as a callable only when \
         its own MIR is shown unable to panic",
        quoted.join(", "),
    )
}

/// The refusal note for one item [`unaccounted_sysroot_callable_items`] names. The
/// ui fixtures match on its first sentence.
pub(super) fn unaccounted_sysroot_callable_note(item: &str) -> String {
    format!(
        "`{item}` is a std/core/alloc function handed to generic code as a value, so it \
         is called inside that code (through its `FnOnce` shim, bare or inside a \
         forwarding wrapper such as `AssertUnwindSafe`), where no row of this function \
         charges it. `-Z trust-policy=certify` and `-Z trust-policy=memory-safe` admit \
         such a callable only when it needs no runtime-checked row: a constructor, or a \
         sysroot function whose own MIR is shown unable to panic, and `{item}` is not \
         shown to be (it may panic, or it calls code that test does not follow). The \
         default policy reports a std routine's own panic as runtime-checked and \
         builds. Options: call it directly in a closure (`|| {item}(..)`), so the call \
         is charged where it is made and must be proved there; use the default policy; \
         or keep this an honest refusal"
    )
}

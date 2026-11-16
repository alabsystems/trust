//! Trust (2026-09-29): a `requires` on a TRAIT IMPL method is charged to no
//! caller, so the method's own verification may not rest on it.
//!
//! ## The hole
//!
//! A function with a `requires` is verified UNDER it: the clause is the body's
//! entry hypothesis (the `assumption:requires` row, "every caller must establish
//! the requires contract"), and each caller is charged a `Precondition` row for
//! it at its direct call (`add_direct_call_contract_summaries`). The caller-side
//! lane reads the contract of the `DefId` the call NAMES. A call to a trait impl
//! method never names the impl's item: `S.m(y)`, `<S as Tr>::m(y)`, `S::m(y)`, a
//! generic `T::m(y)`, a `dyn Tr` call, `<S as Tr>::m as fn(..)` and
//! `map(<S as Tr>::m)` all name the TRAIT's item, whose contract is the trait's
//! (a required trait method cannot carry one at all — `rustc_ast_lowering`
//! refuses a contract on a bodyless declaration). So the impl's `requires` was
//! assumed by its body and owed by nobody. MEASURED on stage 1 of origin/main
//! `8b8d68d1abe`, and again with the reified-pointer and callable-type-argument
//! gates of the same change applied (m3's std, both):
//!
//! ```text
//! pub trait Td { fn m(&self, x: u32) -> u32; }
//! impl Td for S { fn m(&self, x: u32) -> u32 requires x != 0 { 100 / x } }
//! pub fn p(y: u32) -> u32 { S.m(y) }
//! ```
//!
//! built exit 0 under `-Ztrust-policy=certify`, `p` counted VERIFIED (1 of 1),
//! and a verify-off `main` calling `p(0)` divided by zero. The same held for
//! `<S as Tr>::m(y)`, for the reified `<S as Tr>::m` called through a pointer,
//! and for an override whose `requires x > 5` is stronger than the trait
//! default's `requires x != 0` (the default's clause is what callers are charged).
//!
//! ## The rule
//!
//! On every fail-closed lane (strict, the default policy, `certify`; not
//! memory-safe, whose own gate already refuses the method's `assumption:requires`
//! row as "not an authenticated memory-safe assumption" — measured — and not
//! advisory), a local body
//! that is an associated `fn` of a TRAIT impl and owes a caller precondition
//! (`trust_mir_extract::def_owes_caller_precondition`, the same contract set the
//! direct-call lane charges) is refused with a compile error on the method. The
//! body's own rows are not touched; the refusal is the only effect.
//!
//! Inherent methods keep their `requires`: `S::div(&s, y)` and `s.div(y)` name the
//! inherent item, so the direct lane charges its clause, and the fn-pointer /
//! callable-argument gates refuse the uncharged routes
//! (`local_fn_item_is_verified_unconditionally`). A trait's DEFAULT method keeps
//! its `requires` too: every call that can reach the default body (a generic
//! `T::m`, a `dyn` call, a concrete call that resolves to the default) names the
//! trait item that carries the clause, so it is charged the clause that body
//! assumes.
//!
//! Trust (2026-10-06, DEFAULT-REQUIRES-OVERRIDE-CHARGE-1): this paragraph used to
//! say "every trait-dispatched call names the trait item that carries it, so
//! callers are charged exactly the clause its body assumes". That is false for a
//! concrete call that resolves to an OVERRIDE: the call names the trait item, so it
//! was charged the default's clause, but the body that runs is the override, which
//! does not inherit that clause (it is verified without it). See
//! [`call_resolves_to_requires_free_override`] for which calls now skip it.
//!
//! ## Cost
//!
//! A trait impl method with a `requires` is refused even where every caller in
//! fact satisfies it, and even when it restates the trait default's clause
//! verbatim. Nothing in `tests/` or `crates/` writes one (a source scan,
//! 2026-09-29). Recovering it is charging the RESOLVED impl item's clause at a
//! statically resolved trait call, and keeping this refusal for the routes that
//! cannot resolve (generic, `dyn`, a value handed to generic code); recorded as
//! OPEN/PROPOSED in docs/DECISION_QUEUE.md, not decided here.

use super::*;

/// The trait impl method `def_id`'s path when it owes a caller precondition no
/// trait-dispatched call charges; `None` for every other body.
fn uncharged_trait_impl_requires(tcx: TyCtxt<'_>, def_id: DefId) -> Option<DefId> {
    if !def_id.is_local() || !matches!(tcx.def_kind(def_id), rustc_hir::def::DefKind::AssocFn) {
        return None;
    }
    let impl_def_id = tcx.trait_impl_of_assoc(def_id)?;
    trust_mir_extract::def_owes_caller_precondition(tcx, def_id).then_some(impl_def_id)
}

/// Trust (2026-10-04, ADVISORY-REQUIRES-INSTANCE): is `def_id` a trait impl method,
/// local or not, that owes its caller a precondition
/// (`trust_mir_extract::def_owes_caller_precondition`) — a body verified UNDER a
/// clause that no call into it is charged? Two consumers, one predicate:
///
/// * the native callee closure never bundles such a body as a MEMBER (not the
///   root), in either drain;
/// * `elide_kernel_certified_checks` removes no check from such a body.
///
/// A bundled member is lowered with its own `requires` ASSUMED at its entry block
/// (`trust_ir_bridge`'s `emit_entry_precondition_assumes`): sound only while every
/// call into it is charged the clause. A named callee's call is charged by the
/// direct-call lane. A trait impl method's call is not — every route names the
/// TRAIT's item (module doc) — and the refusal above fires only on strict, the
/// default policy and certify. So under `-Ztrust-policy=advisory` (targo's
/// `--allow-l0-gaps`), `Bad.m(0)` or `f::<Bad>` reaching `impl Td for Bad { fn m(..,
/// x: u32) requires x != 0 { 100 / x } }` bundled the impl with `x != 0` assumed,
/// the `x = 0` path was infeasible, and the caller's panic-freedom row was PROVED
/// with no row anywhere charging the violated clause (and a caller of THAT caller
/// was proved with no failed row at all; strict published the same rows beside
/// the impl's refusal). Declined, the call keeps the bridge's absent-callee
/// may-panic arm: the caller's panic-freedom is not proved through it in any lane.
/// The impl method's own root run is unchanged (it is still verified under its
/// clause, and refused on the fail-closed lanes).
///
/// The elision consumer: the caller's row for that call is the absent-callee
/// `runtime_checked` row, which claims the callee's checks are in the program. Under
/// advisory the impl's own run still kernel-certified an overflow check under its
/// clause and DROPPED it (MEASURED on this change's first stage 1:
/// `impl Td for S { fn m(&self, x: u32) -> u32 requires x < 100 { x + 1 } }`,
/// `S.m(u32::MAX)` returned 0 from an advisory binary where a verify-off build
/// panics). A check proved only under a clause nobody is charged is not removed.
pub(super) fn entry_requires_charged_to_no_call(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    matches!(tcx.def_kind(def_id), rustc_hir::def::DefKind::AssocFn)
        && tcx.trait_impl_of_assoc(def_id).is_some()
        && trust_mir_extract::def_owes_caller_precondition(tcx, def_id)
}

/// Trust (2026-10-06, DEFAULT-REQUIRES-OVERRIDE-CHARGE-1): does a call whose callee
/// operand NAMES the trait method `callee` at `args` run an override that owes its
/// caller no precondition, while `callee` (the trait's default body) owes one? When
/// it does, the direct-call lane (`add_direct_call_contract_summaries`) does not
/// charge the default's `requires` at that call, and does not attach its `ensures`.
///
/// ## The hole
///
/// The direct-call lane reads the contract of the item a call NAMES. A concrete call
/// to a trait method (`c.q(x)`, `<C as Tq>::q(&c, x)`, `C::q(&c, x)`) names the trait
/// item, whose `DefId` is the default body's. So the caller was charged the default's
/// `requires` even when the call resolves to an override that does not have it:
///
/// ```text
/// pub trait Tq { fn q(&self, x: u32) -> u32 requires x != 0 { 100 / x } }
/// impl Tq for C { fn q(&self, x: u32) -> u32 { x } }
/// pub fn kq(c: &C, x: u32) -> u32 { c.q(x) }
/// ```
///
/// MEASURED (wave-20 scout, stage 1 of `4ccd862830`): `kq` was refused under the
/// default policy and `certify` with `[precond] FAILED`, counterexample `x = 0`, the
/// row naming `<C as Tq>::q`, whose own row is `no_obligations`. `kq(&C, 0)` returns
/// 0. The override is not verified under the default's clause: with
/// `fn q(&self, x: u32) -> u32 { 1000 / x }` it is `[divzero] FAILED` at `x = 0`. So
/// the charge protected no body that runs. A false refutation, not a false proof.
///
/// ## The rule
///
/// `true` only when all of these hold:
///
/// * `callee` is an associated `fn` of a TRAIT, and it owes its caller a precondition
///   (`trust_mir_extract::def_owes_caller_precondition`; a trait method can carry a
///   contract only on a default body, since `rustc_ast_lowering` refuses one on a
///   bodyless declaration). A callee that owes nothing keeps today's path untouched;
/// * `Instance::try_resolve` in `typing_env` (the body's post-analysis environment,
///   the one `build_dyn_dispatch_summaries` and the bundle collector resolve with)
///   answers `Ok(Some(_))` with `InstanceKind::Item(d)` and `d != callee`: the call
///   runs an override, exactly;
/// * `d` owes no precondition of its own.
///
/// Everything else answers `false` and keeps the default's charge: a call that
/// cannot be resolved here (generic, `Ok(None)`; an error), a `dyn` call
/// (`Virtual`), a shim, a call that resolves to the default body itself (an impl
/// that does not override), and an override that owes a `requires` of its own. That
/// last case is refused at the impl (`abort_on_uncharged_trait_impl_requires`); its
/// call keeps the default's clause, so no `Precondition` row is ever minted from an
/// item the call does not name. Charging the resolved impl's own clause at a
/// statically resolved call was declined by ADVISORY-REQUIRES-INSTANCE
/// (docs/DECISION_QUEUE.md) as the partial-devirtualization surface P-REQ declined;
/// this predicate only REMOVES a charge, and only where the item that runs owes none.
///
/// Sound because no body that runs at such a call assumes the default's clause: a
/// body is verified under exactly the `requires` it owes
/// (`def_owes_caller_precondition` reads the same contract set), and `d` owes none.
/// The default's body does not run at this call. The default's `ensures` describes
/// that body, so it is not attached either. The direct-call lane's later fall-through
/// may then charge the override's own entry asserts (`derived_bundled_member_summary`),
/// which is a charge for a body that does run.
pub(super) fn call_resolves_to_requires_free_override<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    callee: DefId,
    args: ty::GenericArgs<'tcx>,
) -> bool {
    if !matches!(tcx.def_kind(callee), DefKind::AssocFn) || tcx.trait_of_assoc(callee).is_none() {
        return false;
    }
    requires_free_override(
        callee,
        |def_id| trust_mir_extract::def_owes_caller_precondition(tcx, def_id),
        || match ty::Instance::try_resolve(tcx, typing_env, callee, args) {
            Ok(Some(instance)) => match instance.def {
                ty::InstanceKind::Item(item) => Some(item),
                _ => None,
            },
            Ok(None) | Err(_) => None,
        },
    )
}

/// The decision [`call_resolves_to_requires_free_override`] takes, over abstract
/// items. `named` is the item the call names, `owes` says whether an item owes its
/// caller a precondition, and `resolve_item` gives the item the call runs when it
/// resolves exactly to an `InstanceKind::Item` (else `None`). It is asked only when
/// `named` owes something. Pure, so the unit tests pin it.
fn requires_free_override<D: Copy + Eq>(
    named: D,
    owes: impl Fn(D) -> bool,
    resolve_item: impl FnOnce() -> Option<D>,
) -> bool {
    if !owes(named) {
        return false;
    }
    let Some(item) = resolve_item() else {
        return false;
    };
    // `item != named` is implied once `named` owes (the default body resolving to
    // itself owes too); it is spelled out because it is the rule: an OVERRIDE runs.
    item != named && !owes(item)
}

/// Trust (2026-10-05, ADVISORY-REQUIRES-CROSS-CRATE): can a crate OTHER than this
/// one call `def_id` — a body that owes its caller a precondition — so that its
/// clause is charged, if at all, under that crate's policy rather than this one's?
///
/// `elide_kernel_certified_checks` removes a check proved under the body's own
/// `requires`, which is sound only while every call into the body is charged the
/// clause AND a violated charge fails the build. This session can promise that for
/// its own calls (the direct-call lane charges them; the fail-closed lanes refuse
/// a violated or uncharged route; advisory elides nothing from such a body). It
/// cannot promise it for a call compiled in another crate: an advisory consumer
/// only WARNS on its failed `Precondition` row and refuses no uncharged route, and
/// a verify-off consumer charges nothing. MEASURED 2026-10-05 (stage 1 of
/// `71fc7a07cc`): `pub fn add1(x: u32) -> u32 requires x < 100 { x + 1 }` built on
/// the default policy as an rlib, its overflow check elided; a consumer calling
/// `la::add1(u32::MAX)` directly, or through `let fp: fn(u32) -> u32 = la::add1`,
/// built exit 0 under `-Ztrust-policy=advisory` (and under `-Ztrust-verify=off`)
/// and printed `0`, where a verify-off build of both crates panics.
///
/// Answered conservatively (`true` keeps the checks):
/// * a non-local `def_id`, or one carrying an extern indicator (`#[no_mangle]`,
///   `#[export_name]`, a non-internal `#[linkage]`) — callable by symbol;
/// * otherwise `false` when every crate type of this session is an executable
///   (nothing links against an executable's items);
/// * otherwise whether the item's typeck root is REACHABLE from this crate's
///   public interface (`EffectiveVisibilities::is_reachable`). A private item is
///   reached from outside only through this crate's own code: a direct call is
///   charged here, and a value minted from it is refused by the fail-closed
///   lanes' `uncharged_callable` seam (advisory elides nothing anyway).
///
/// Trust (2026-10-05, ADVISORY-REQUIRES-TRANSITIVE-1): this asks about the body
/// itself only. A direct call from this crate is charged here, but it may be
/// charged UNDER a caller's clause that only another crate's policy enforces; the
/// elision asks [`entry_requires_charged_only_in_this_crate`], which builds on this.
fn entry_requires_reachable_from_another_crate(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let Some(local) = def_id.as_local() else {
        return true;
    };
    let root = tcx.typeck_root_def_id(def_id);
    if tcx.codegen_fn_attrs(root).contains_extern_indicator() {
        return true;
    }
    if tcx
        .crate_types()
        .iter()
        .all(|crate_type| *crate_type == rustc_structures::CrateType::Executable)
    {
        return false;
    }
    let root_local = root.as_local().unwrap_or(local);
    tcx.effective_visibilities(()).is_reachable(root_local)
}

/// Trust (2026-10-05, ADVISORY-REQUIRES-TRANSITIVE-1): may a check proved under
/// `def_id`'s `requires` be removed? Only when every call that reaches the body is
/// charged the clause by THIS compilation, under entry hypotheses this compilation
/// charged too. `false` keeps the checks, and is the answer for anything this
/// cannot see: a non-local def, a body that is not a `fn` or associated `fn`.
///
/// ## The hole
///
/// [`entry_requires_reachable_from_another_crate`] asks only whether another crate
/// can call the body itself. A private body is called only from this crate, and
/// each such call is charged its clause, but the charge is proved under the
/// CALLER's entry hypotheses. When the caller owes a `requires` of its own and
/// another crate can call it, that hypothesis is enforced only under the other
/// crate's policy: an advisory consumer only warns on its failed `[precond]` row,
/// a verify-off one charges nothing. MEASURED 2026-10-05 on the stage 1 of
/// `c1c028f41f` with `tests/ui/trust/auxiliary/xcmreq_callee.rs`, built under
/// `certify`:
///
/// ```text
/// pub fn inc_via(x: u32) -> u32 requires x < 100 { bump(x) }
/// fn bump(x: u32) -> u32 requires x < 100 { x + 1 }
/// ```
///
/// `TRUST_ELIDE_DEBUG=1` reported `bump`'s overflow check elided and none in
/// `inc_via`. A verify-off consumer calling `inc_via(u32::MAX)` printed `0`, and so
/// did an advisory one, where a verify-off build of every crate panics.
///
/// ## The rule
///
/// Over the local `fn`s and associated `fn`s that owe a caller precondition
/// (`trust_mir_extract::def_owes_caller_precondition`):
///
/// * a body is EXPOSED when another crate can call it
///   ([`entry_requires_reachable_from_another_crate`]) or nothing charges its
///   clause ([`entry_requires_charged_to_no_call`]);
/// * a body that an exposed body NAMES ([`local_fns_named_by`]: a call, a method
///   call, a path, a fn item inside any type in its typeck results, which include
///   its closures and inline consts) is exposed too.
///
/// The checks of an exposed body are kept. So `bump` keeps its check, and so does
/// every body further down a chain of `requires` bodies that starts at one another
/// crate can call.
///
/// Exposure travels only through bodies that owe a caller precondition. A caller
/// with no `requires` is verified under no entry hypothesis its own callers owe,
/// so its charge of the callee's clause holds for every argument it is given, by
/// any crate. `pub fn outer(x: u32) -> u32 { if x < 100 { inner(x) } else { 0 } }`
/// keeps `inner`'s elision (`requires_dep_default_policy.rs`'s control). That is
/// the premise [`entry_requires_reachable_from_another_crate`] already rests on
/// for every private body: a call compiled in this crate is charged here, under
/// this crate's policy (and advisory elides nothing from a `requires` body).
///
/// ## Cost
///
/// Runtime only; no verdict changes. A private `requires` body that an exposed
/// `requires` body names keeps the overflow checks its clause proved, even where
/// the caller establishes the clause itself (`if x < 50 { bump(x) }` inside
/// `inc_via`) and even where the name is not a call. Recovering that needs the
/// charge's proof to show it did not rest on the caller's own clause.
pub(super) fn entry_requires_charged_only_in_this_crate(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let Some(local) = def_id.as_local() else {
        return false;
    };
    if let Some(answer) = with_crate_verification_state(tcx.sess, |state| {
        state.requires_charged_only_here.as_ref().map(|set| set.contains(&local))
    }) {
        return answer;
    }
    // Computed outside the state lock, since it runs queries. The answer is the
    // same whichever worker stores it first.
    let computed = requires_bodies_charged_only_here(tcx);
    let answer = computed.contains(&local);
    with_crate_verification_state(tcx.sess, |state| {
        if state.requires_charged_only_here.is_none() {
            state.requires_charged_only_here = Some(computed);
        }
    });
    answer
}

/// The local `fn`s and associated `fn`s that owe a caller precondition and are not
/// exposed (the rule in [`entry_requires_charged_only_in_this_crate`]).
fn requires_bodies_charged_only_here(tcx: TyCtxt<'_>) -> FxHashSet<LocalDefId> {
    let owing: Vec<LocalDefId> = tcx
        .hir_body_owners()
        .filter(|&owner| {
            matches!(tcx.def_kind(owner), DefKind::Fn | DefKind::AssocFn)
                && trust_mir_extract::def_owes_caller_precondition(tcx, owner.to_def_id())
        })
        .collect();
    unexposed_requires_bodies(
        &owing,
        |owner| {
            entry_requires_reachable_from_another_crate(tcx, owner.to_def_id())
                || entry_requires_charged_to_no_call(tcx, owner.to_def_id())
        },
        |owner| local_fns_named_by(tcx, owner),
    )
}

/// The members of `owing` that are not exposed. `exposed_entry` says whether a
/// member is exposed on its own; `names` lists what a member's body names.
/// Exposure travels from an exposed member to every member it names, and from
/// there on; a name that is not in `owing` carries nothing. Pure, so the unit
/// tests pin it.
fn unexposed_requires_bodies<N: Copy + Eq + Hash>(
    owing: &[N],
    exposed_entry: impl Fn(N) -> bool,
    mut names: impl FnMut(N) -> Vec<N>,
) -> FxHashSet<N> {
    let owing_set: FxHashSet<N> = owing.iter().copied().collect();
    let mut exposed: FxHashSet<N> = FxHashSet::default();
    let mut pending: Vec<N> = Vec::new();
    for &member in owing {
        if exposed_entry(member) && exposed.insert(member) {
            pending.push(member);
        }
    }
    while let Some(member) = pending.pop() {
        for named in names(member) {
            if owing_set.contains(&named) && exposed.insert(named) {
                pending.push(named);
            }
        }
    }
    owing.iter().copied().filter(|member| !exposed.contains(member)).collect()
}

/// Every LOCAL function that `owner`'s typeck results name: the item each method
/// call, overloaded operator, type-relative path and splatted call resolved to, and
/// every fn item type inside the type of any expression or pattern (a direct
/// call's callee, a function handed over as a value, a closure capturing one).
/// Closures, coroutines and inline consts share their parent's typeck results, so
/// what they name counts as the parent's. This over-approximates the calls the
/// body makes into this crate; a name that is not a call only keeps more checks.
fn local_fns_named_by(tcx: TyCtxt<'_>, owner: LocalDefId) -> Vec<LocalDefId> {
    let results = tcx.typeck(owner);
    let mut named: Vec<LocalDefId> = Vec::new();
    for (_, resolution) in results.type_dependent_defs().items_in_stable_order() {
        if let Ok((_, def_id)) = resolution
            && let Some(local) = def_id.as_local()
        {
            named.push(local);
        }
    }
    for (_, splatted) in results.splatted_defs().items_in_stable_order() {
        if let Ok(ty::SplattedDef::FnDef { def_id, .. }) = splatted
            && let Some(local) = def_id.as_local()
        {
            named.push(local);
        }
    }
    for (_, node_ty) in results.node_types().items_in_stable_order() {
        for inner in node_ty.walk().filter_map(|arg| arg.as_type()) {
            if let ty::FnDef(def_id, _) = *inner.kind()
                && let Some(local) = def_id.as_local()
            {
                named.push(local);
            }
        }
    }
    named
}

/// Refuse the body when [`uncharged_trait_impl_requires`] holds. Emits at most one
/// error.
pub(super) fn abort_on_uncharged_trait_impl_requires(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    func_path: &str,
) {
    if let Some(diagnostic) = prepare_uncharged_trait_impl_requires(tcx, body, func_path) {
        diagnostic.emit(tcx);
    }
}

pub(super) fn prepare_uncharged_trait_impl_requires(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    func_path: &str,
) -> Option<PreparedLocatedDiagnostic> {
    if body.source.promoted.is_some() {
        return None;
    }
    let def_id = body.source.def_id();
    let Some(impl_def_id) = uncharged_trait_impl_requires(tcx, def_id) else {
        return None;
    };
    let trait_path = tcx
        .impl_opt_trait_id(impl_def_id)
        .map_or_else(|| String::from("its trait"), |trait_id| tcx.def_path_str(trait_id));
    let span = tcx.def_span(def_id);
    let header = format!(
        "Trust verification failed for `{func_path}`: a `requires` on a trait impl \
         method is charged to no caller"
    );
    let children = vec![
        PreparedDiagnosticChild::Note(format!(
            "this body is verified UNDER its `requires`, but every call that reaches it — a \
             method call, `<_ as {trait_path}>::…`, generic code, a `dyn` call, a fn pointer — \
             names the trait's item, and callers are charged the TRAIT's contract, not this \
             impl's; nothing establishes this clause before the body runs"
        )),
        PreparedDiagnosticChild::Note(
            "options: move the precondition into an inherent function (its direct callers are \
             charged the clause) and call that from the impl on a checked path; make the \
             method total and drop the `requires`; or put the clause on a trait default method, \
             whose callers are charged it"
                .into(),
        ),
    ];
    Some(PreparedLocatedDiagnostic {
        span,
        diagnostic: PreparedDiagnostic { aborting: true, header, children },
    })
}

#[cfg(test)]
mod tests;

//! Trust (2026-09-30, residual L3 of the fn-pointer `requires` fix): in a
//! verifying session the MIR inliner keeps every call whose callee owes its
//! caller a `requires`.
//!
//! Since T6 (2026-10-09) a proof session runs the `-O0` MIR pipeline and refuses
//! `-Zmir-opt-level`, `-Zinline-mir` and `-Zmir-enable-passes` by name
//! (`rustc_driver_impl::trust_option_domain_error`), so `Inline` no longer runs in
//! a verifying session and `ForceInline` (`#[rustc_force_inline]`, which runs at
//! every level) is the route this rule still guards. The measurements below were
//! taken with the options a session can no longer pass.
//!
//! ## The hole
//!
//! A function with a `requires` is verified UNDER it. The clause is its body's
//! entry hypothesis, and each DIRECT caller is charged a `Precondition` row for it
//! (`add_direct_call_contract_summaries`, keyed on a `Call` whose callee operand is
//! a `FnDef` constant naming the item). The routes that reach the function with no
//! call to charge are refused: a reified pointer or a callable type argument
//! (`uncharged_callable`), a trait impl method's clause (`trait_impl_requires`). And
//! `elide_kernel_certified_checks` DROPS the function's kernel-certified Add/Sub/Mul
//! overflow `Assert`s, certified with the `requires` as a hypothesis, from the body
//! `optimized_mir` serves.
//!
//! `run_optimization_passes` runs `ForceInline` and `Inline` early and `TrustVerify`
//! LAST, so a caller is verified AFTER inlining. The inliner copies the callee's
//! `optimized_mir` (`try_instance_mir` → `instance_mir`; a dependency's is the body
//! its rmeta exports), which is the body the callee's own `TrustVerify` already
//! elided. MEASURED on a stage 1 of `fbc6068e3` at `-Copt-level=3
//! -Zmir-opt-level=2` (overflow checks are on in a verifying session at every
//! opt-level) with `pub fn add1(x: u32) -> u32 requires x < 100 { x + 1 }`: the
//! callers `add1(y)`, `Some(y).map(add1)`, `let g = add1; g(y)` and
//! `core::convert::identity(add1)(y)` each optimize to `_2 = AddWithOverflow(copy
//! _1, const 1_u32); _0 = copy (_2.0: u32)` under `scope (inlined add1)`. No `Call`
//! is left for the direct lane to charge. No reified constant or callable type
//! argument is left for the gate: `Option::map::<u32, fn(u32) -> u32 {add1}>`, the
//! `FnOnce` shim and `identity::<fn(u32) -> u32 {add1}>` were inlined too, and `let
//! g = add1` survives only as debuginfo. No `Assert` is left for an overflow row.
//! `f`'s only row is `no_obligations`; certify and the default policy exit 0, and
//! the certify-built library, linked into a verify-off `main`, returned
//! `f(u32::MAX) = Some(0)` / `0` where a build that keeps the check panics. At `-O0`
//! each is refused. `-Zinline-mir=yes` alone does the same, as does
//! `-Zmir-enable-passes=+Inline` at `-O0`, `-Zmir-opt-level=0 -Zinline-mir=yes`,
//! and `#[optimize(none)]` on the caller with `+Inline`; so does the closure the
//! gate's own note recommends, `map(|x| add1(x))` (the closure's `optimized_mir`
//! inlined `add1` first); so does a trait DEFAULT method's clause; and
//! `#[rustc_force_inline]` (behind `rustc_attrs`) does it at EVERY opt-level, under
//! certify, the default policy and advisory alike, because `ForceInline` always
//! runs. Across crates, `dep::add1(y)` built exit 0 under certify, the default
//! policy and memory-safe.
//!
//! ## The rule
//!
//! When Trust verification is on (`verification_enabled`, the predicate the E6
//! wrapping-call preservation in `resolve_callsite` reads, and the one under which
//! `TrustVerify` elides), `try_inlining` declines a callee that owes its caller a
//! precondition ([`keep_call_owing_requires`]):
//! `trust_mir_extract::def_owes_caller_precondition`, the contract set the
//! direct-call lane charges from (`trust_contracts`: a local bundle or HIR clause,
//! or the set the callee's crate exported to rmeta), asked of the item the call
//! NAMES and, when it differs, of the item it RESOLVES to. The call stays a call.
//! `RemoveZsts`, which runs right after the inliners in every session whose
//! `-Zmir-opt-level` is at least 1 (it is a required pass, so `#[optimize(none)]`
//! does not suppress it), turns a callee held in a fn-item local into the
//! constant, and the direct-call lane charges it exactly as at `-O0`. What wraps
//! the call is still inlined: `Option::map`, the `FnOnce` shim, `identity`, a local
//! closure. So after the rule, each measured shape above optimizes to
//! `_2 = add1(move _1)` inside `(inlined Option::<u32>::map…)` and is refused by
//! `[precond] FAILED`, counterexample `y = 100` (MEASURED on the same stage 1 with
//! `#[inline(never)]` on `add1` standing in for the rule, which makes the inliner
//! decline the same callee at the same point). `Inline` just leaves the call;
//! `ForceInline` reports its ordinary "could not be inlined" error with
//! [`KEEP_CALL_REASON`].
//!
//! The one exception is `ForceInline` under `-Ztrust-policy=advisory`. Advisory
//! verifies for its report and makes no proof claim, and a Trust rule may fail a
//! build only when a claim is made (`Session::trust_proof_claimed`). There the
//! `#[rustc_force_inline]` callee is inlined as before, and the gap is REPORTED
//! instead (`warn_advisory_force_inlined_requires`): nothing charges the clause
//! at that call, and the checks the callee's verification elided under it are
//! unguarded there. `Inline` keeps the call under advisory too, which fails
//! nothing and puts the `[precond]` row in the report.
//!
//! Declining an inline changes no semantics: the call runs the same body. It
//! changes a verdict only through the charge the call now carries: a caller that
//! proves the clause keeps its verdict (`if y < 100 { add1(y) } else { 0 }` built
//! exit 0 under certify with the call kept, as at `-O0`), and one that cannot is
//! refused as at `-O0`.
//!
//! ## Where the kept call is not a `[precond]` row: `-Zmir-opt-level=0`
//!
//! Where `RemoveZsts` does not run (`-Zmir-opt-level=0` with `-Zinline-mir=yes` or
//! `-Zmir-enable-passes=+Inline`, or `-Zmir-enable-passes=-RemoveZsts`), the call
//! an inlined `FnOnce` shim forwards keeps a fn-item LOCAL as its callee
//! (`_7 = move _8(move (_9.0: u32))`, `_8: fn(u32) -> u32 {add1}`). The rule keeps
//! it (the local's type still names `add1`), but the direct-call lane, keyed on a
//! `FnDef` constant, does not charge it, and the native lowering refuses the
//! terminator: "opaque MIR terminator `Call(indirect)` cannot be soundly lowered".
//! Fail-closed, through that row rather than `[precond]` (MEASURED with the stand-in
//! under certify, the default policy and memory-safe; BEFORE the rule the same
//! flags built exit 0). `requires_callee_erased_by_mir_inliner.rs`'s
//! `map_level0_inline_certify` pins it.
//!
//! ## Why not verify the pre-inline body
//!
//! `TrustVerify` verifies the body codegen receives: the R1 ruling's "the verified
//! MIR is still exactly the compiled MIR — nothing is verified on a clone"
//! (`rustc_session::trust_default_mir_opt_level_by_flags`), the O2-inline rows that
//! read what the inliner left, and the elision's block-identity join ("TrustVerify
//! is the last pass, so bb indices are stable") all rest on it. Verifying before
//! `Inline` would verify one body and ship another, for every lane, to fix one
//! route. Charging the inlined instance from the `SourceScope` that records it would
//! need the argument values at the inlined body's entry, which GVN and CopyProp have
//! rewritten by then; refusing any body with such a scope would also refuse the
//! guarded call above, which the kept call proves. Keeping the call is the smaller
//! change, and the only one here that leaves the verified body the compiled one.
//!
//! ## What else could erase such a call
//!
//! Only the two inliners, and both reach [`keep_call_owing_requires`] through
//! `try_inlining`. The other passes that rewrite a `Call` into statements or a
//! `Goto` — `InstSimplify` (`Clone::clone` of a trivially-copy type,
//! `size_of_val`/`align_of_val`, `raw_eq`, the validity-assert intrinsics),
//! `LowerIntrinsics`, `LowerSliceLenCalls` — name fixed core items and intrinsics,
//! and no sysroot item declares a `requires` (the direct-call lane would charge one
//! if it did). `SimplifyCfg` and `UnreachablePropagation` delete only unreachable
//! blocks, where nothing is owed; `LintAndRemoveUninhabited` drops only a return
//! edge; `RemoveUnneededDrops` removes only the `Drop` of a type that needs none, so
//! no user `Drop::drop` (a trait impl method, whose `requires` is refused at the
//! impl anyway) is erased. GVN or const propagation turning a call through a
//! reified pointer into a direct call makes it charged, not erased. LLVM's inliner
//! runs after verification, on MIR whose call was charged.
//!
//! ## Not asked: a Clean-origin def's caller obligations
//!
//! A Clean-origin def's erased hypothesis binders become caller obligations
//! (`CleanOriginPlan::preconditions`), charged at a direct call by
//! `clean_origin_callee_summary` — a second source that
//! `def_owes_caller_precondition` does not read, so this rule does not keep such a
//! call, and the value-use gate does not refuse such a def as a value. Both are
//! latent: the preconditions are empty for every plan today, because the plan lane
//! refuses a hypothesis binder outright (`trust_clean_origin::emit`). The increment
//! that lets a hypothesis-carrying def reach a plan must extend
//! `owing_callee` (and the gate) to ask it; `CleanOriginPlan::preconditions`
//! carries the same pointer.
//!
//! ## The dependency this protects (not changed here)
//!
//! `elide_kernel_certified_checks` removes a check that was proved under the
//! callee's `requires`. That is sound only while every execution that enters the
//! body has established the clause, i.e. while every call is charged: the direct
//! lane, the value-use gate, the trait-impl refusal and now this rule are what
//! keep it so. The rule does not reach a caller no verifier sees. A verify-off
//! crate that calls a verified dependency's `requires` function with an argument
//! outside the clause, directly or through the MIR inliner (untouched when
//! verification is off), runs the elided body and gets the wrapped value
//! (MEASURED, same stage 1: the certify-built library above returns `Some(0)` to a
//! verify-off `main`). That is an unverified caller breaking a contract, the same
//! as its direct call; it is recorded, not changed, here. So is its transitive
//! form: such a crate's own exported MIR, which inlined the elided body, carries
//! neither the call nor the check into a verifying crate that inlines or bundles it.
//! Trust (DEP-MEMBER-REQ-1, 2026-10-05): the BUNDLING half, and the same crate's
//! un-inlined call, are no longer silent: the B-lane declines a declared member
//! whose MIR calls, or had inlined, a function that owes its caller a `requires`
//! (`foreign_member_reaches_uncharged_requires` in `trust_verify.rs`), so the
//! verifying caller meets the absent-callee refusal. A body the D4-A lanes
//! RE-DERIVE as their own root (the C-FLOW `dyn` bar, the foreign-trait closure,
//! postcondition reuse) is declined when its encoded MIR inlined such a function:
//! re-derivation conjunct (7), `foreign_rederivation::body_inlines_requires_owing_callee`,
//! the same test the member drain reads (review of `444376149e`, 2026-10-05: the
//! C-FLOW form had built exit 0 under `certify` and returned 0 where vanilla Rust
//! panics). The INLINING half (a verifying session's explicit MIR inliner copying
//! such a dependency body, which owes nothing itself, into a root) is unchanged by
//! those rules.
//!
//! ## Cost
//!
//! * Only a verifying session that runs an inliner. `Inline` runs with an explicit
//!   `-Zinline-mir=yes` (whatever the level), or `-Zmir-enable-passes=+Inline`, or
//!   by level: at `-Zmir-opt-level=2` only with `-Copt-level=2` or `3` and no
//!   incremental session, and at `-Zmir-opt-level>=3` at every `-Copt-level`. The
//!   default verifying session runs level 1 at every `-Copt-level` (ruling R1), so
//!   `Inline` is off there. `ForceInline` always runs, but only for
//!   `#[rustc_force_inline]` items, which no sysroot or in-tree crate declares.
//!   With `-Ztrust-verify=off` [`keep_call_owing_requires`] returns before reading
//!   anything.
//! * Only a callee that owes a precondition is declined. Every other callee, the
//!   std adapters and shims around a `requires` function included, is inlined as
//!   before. LLVM still inlines the kept call at `-Copt-level>=1`; what is lost is
//!   MIR-level inlining of those callees, and a caller that keeps such a call is no
//!   longer a call-free leaf for `cross_crate_inlinable`'s automatic export.
//! * The question is, per distinct callee `DefId`, a memoized `trust_contracts`
//!   lookup for a dependency (an rmeta table read) and, for a local def, the HIR
//!   `contract` check `def_may_have_contracts`, which runs the query only for a
//!   def that has contracts; two when the call resolves to a different item.
//! * Verdicts, relative to the same flags before the rule: a correct call to a
//!   LOCAL `requires` function keeps its verdict (above). A correct call to a
//!   DEPENDENCY's `requires` function used to pass with no row at all, because
//!   the inlined body was never charged; the kept call now meets the absent-callee
//!   refusal every `-O0` call to a dependency's function meets (MEASURED with
//!   `#[inline(never)]` standing in: `if y < 100 { dep::add1_never(y) }` refused by
//!   that row only; and at `-O0`, `if y < 100 { dep::add1(y) }` with the MIR the
//!   `#[inline]` dependency exports is refused by the same row). That is `-O0`
//!   parity, not a new refusal class.
//!   `if y < 100 { Some(y).map(add1) } else { None }` still builds at
//!   `-Zmir-opt-level=2`, now on a charge: the inlined `map` leaves a DIRECT call
//!   whose precondition is proved (MEASURED the same way). At `-O0` the value-use
//!   gate refuses it, so that one verdict stays more permissive than `-O0` — soundly.
//!
//! ## Merged with main's W5 (integ/stage1-batch4, 2026-10-02)
//!
//! main landed the same fix independently as W5 (4d80508166, 2026-10-01): in a
//! verifying session `inline::resolve_callsite` declines a callee that
//! `trust_verify::callee_carries_trust_requires` says carries a `requires`, on the
//! static callee and on the resolved instance, BEFORE `try_inlining` is reached.
//! Both are kept. W5 decides first for every callee whose contract bundle has a
//! `requires`, except a `#[rustc_force_inline]` one; [`keep_call_owing_requires`]
//! then sees a forced callee and any callee W5 missed, which
//! `trust_mir_extract::def_owes_caller_precondition` (a local def's HIR clause
//! attributes as well as the bundle) still catches.
//! * W5 declines silently, so it must not decline a forced callee (fixed
//!   2026-10-02). It did at first: `ForceInline` never saw the site, reported no
//!   failure, and `validate.rs` ICEd on the forced call left behind ("broken MIR …
//!   `#[rustc_force_inline]`-annotated function not inlined") whenever the caller's
//!   verification raised no error first, e.g. `if y < 100 { add1_forced(y) } else
//!   { 0 }` under the default policy, strict and certify, and the unguarded caller
//!   under advisory (MEASURED on a stage 1 of integ/stage1-batch4). W5's two sites now
//!   let a callee whose static item is `#[rustc_force_inline]` through, and this
//!   rule decides it as before the merge: `ForceInline`'s "could not be inlined"
//!   error with [`KEEP_CALL_REASON`] under a proof-claiming policy, the inline plus
//!   the warning below under advisory. Not measured on a build of the fix.
//! * The `[TRUST_MIR_INLINE] kept call` trace is printed at W5's two sites too
//!   ([`trace_kept_call`]), for a callee the running inliner would otherwise consider
//!   (`Inliner::should_inline_for_callee`), so the fixtures' kept-call pins hold.

use super::*;

/// Why [`keep_call_owing_requires`] keeps a call. `ForceInline` prints it after
/// "could not be inlined due to: "; `Inline` only logs it.
pub(crate) const KEEP_CALL_REASON: &str = "the callee owes its caller a Trust `requires`, \
     which a verifying session charges only at a call that names it, so the call is kept";

/// `TRUST_MIR_INLINE_TRACE=1`: print each inlining decision this module makes or
/// observes (`[TRUST_MIR_INLINE] kept call to …`, `[TRUST_MIR_INLINE] inlined …`).
/// Items are spelled by `trust_mir_extract::safe_def_path_str`, the crate-prefixed,
/// alias-free identity path the verifier's own diagnostics use (so a local `add1`
/// is `krate::add1`, and a dependency's is `dep_crate::add1` whatever it was
/// imported as), which is what the ui fixtures' `~? RAW` lines match. Read once per
/// process: [`trace_inlined`] is reached for every inlined call.
fn trace_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| env_flag_enabled("TRUST_MIR_INLINE_TRACE"))
}

/// The item a call in `caller_body`'s block `block` resolved to `callee` must be
/// kept for: the item the call NAMES (its callee operand's `FnDef`, whose contract
/// the direct-call lane charges) when that owes its caller a precondition, else
/// the item it RESOLVES to when that differs and owes one (a trait item resolved
/// to an impl's method). `None` when neither does. A shim resolves to its trait
/// method (`FnOnce::call_once`), which owes nothing, so the shim is inlined and the
/// call it forwards is asked on its own.
fn owing_callee<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller_body: &Body<'tcx>,
    block: BasicBlock,
    callee: ty::Instance<'tcx>,
) -> Option<DefId> {
    let named = if let TerminatorKind::Call { func, .. } = &caller_body[block].terminator().kind
        && let ty::FnDef(def_id, _) = *func.ty(&caller_body.local_decls, tcx).kind()
    {
        Some(def_id)
    } else {
        None
    };
    if let Some(named) = named
        && trust_mir_extract::def_owes_caller_precondition(tcx, named)
    {
        return Some(named);
    }
    let resolved = callee.def_id();
    (Some(resolved) != named && trust_mir_extract::def_owes_caller_precondition(tcx, resolved))
        .then_some(resolved)
}

/// Trust (2026-09-30, L3): `Err` when the MIR inliner must keep this call — a
/// verifying session, and a callee that owes its caller a `requires` (module doc).
/// Called by `try_inlining` for `Inline` and `ForceInline` alike, after the
/// callee's own inlining checks and before its body is read; `callee_must_inline`
/// is the callee's `#[rustc_force_inline]`. Declining is the only effect: nothing
/// is inlined, charged or refused here. The advisory exception (module doc) warns
/// and lets the forced inline proceed.
pub(crate) fn keep_call_owing_requires<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller_body: &Body<'tcx>,
    block: BasicBlock,
    callee: ty::Instance<'tcx>,
    callee_must_inline: bool,
) -> Result<(), &'static str> {
    if !verification_enabled(tcx.sess) {
        return Ok(());
    }
    let Some(owing) = owing_callee(tcx, caller_body, block, callee) else {
        return Ok(());
    };
    if callee_must_inline && !tcx.sess.trust_proof_claimed() {
        warn_advisory_force_inlined_requires(tcx, caller_body, block, owing);
        return Ok(());
    }
    trace_kept_call(tcx, caller_body, owing);
    Err(KEEP_CALL_REASON)
}

/// `TRUST_MIR_INLINE_TRACE=1`: print that the call to `owing` in `caller_body` is
/// kept because it owes its caller a `requires`. Shared by this module's rule and by
/// main's W5 check in `inline::resolve_callsite`, which decides first (see the
/// module doc, "Merged with main's W5"). Observability only; it decides nothing.
pub(crate) fn trace_kept_call<'tcx>(tcx: TyCtxt<'tcx>, caller_body: &Body<'tcx>, owing: DefId) {
    if trace_enabled() {
        eprintln!(
            "[TRUST_MIR_INLINE] kept call to `{}` in `{}`: it owes its caller a `requires`",
            trust_mir_extract::safe_def_path_str(tcx, owing),
            trust_mir_extract::safe_def_path_str(tcx, caller_body.source.def_id()),
        );
    }
}

/// Advisory only (verification on, no proof claimed): `ForceInline` inlines a
/// `#[rustc_force_inline]` callee that owes its caller a `requires`, because keeping
/// the call would fail the build over a Trust rule, which only a proof-claiming
/// session may do. Report the gap that leaves at this call instead of hiding it.
fn warn_advisory_force_inlined_requires<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller_body: &Body<'tcx>,
    block: BasicBlock,
    owing: DefId,
) {
    let caller = trust_mir_extract::safe_def_path_str(tcx, caller_body.source.def_id());
    let callee = trust_mir_extract::safe_def_path_str(tcx, owing);
    tcx.dcx()
        .struct_span_warn(
            caller_body[block].terminator().source_info.span,
            format!(
                "Trust verification advisory for `{caller}`: `#[rustc_force_inline]` inlines \
                 `{callee}`, which owes its caller a `requires`, so this call is not charged \
                 for it"
            ),
        )
        .with_note(
            "the inlined body carries the checks its own verification elided under that \
             `requires`, unguarded at this call; every proof-claiming policy keeps the call \
             instead, and the forced inline then fails",
        )
        .emit();
}

/// `TRUST_MIR_INLINE_TRACE=1`, verifying session: print that `callee` was inlined
/// into `caller_body`. Observability only (the ui fixtures pin with it that a
/// `requires`-free callee is still inlined); it decides nothing.
pub(crate) fn trace_inlined<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller_body: &Body<'tcx>,
    callee: ty::Instance<'tcx>,
) {
    if trace_enabled() && verification_enabled(tcx.sess) {
        eprintln!(
            "[TRUST_MIR_INLINE] inlined `{}` into `{}`",
            trust_mir_extract::safe_def_path_str(tcx, callee.def_id()),
            trust_mir_extract::safe_def_path_str(tcx, caller_body.source.def_id()),
        );
    }
}

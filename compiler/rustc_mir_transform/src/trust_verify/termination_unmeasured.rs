//! Trust (D9, ruled 2026-09-27, owner-delegated): direct SELF recursion that no
//! `decreases` measure covers is charged as an `assumption:termination-unmeasured`
//! row. docs/DECISION_QUEUE.md "D9" is the ruling; docs/KNOWN_HAZARDS.md, "direct
//! SELF recursion is charged termination only when an integer measure binds", is
//! the hazard it closes.
//!
//! ## The hole
//!
//! vcgen's inferred direct-self termination lane (`crates/trust-vcgen/src/
//! termination.rs`, `check_termination`) mints its descent rows only when the
//! first integer parameter binds at every self call, every non-self call is a
//! vanilla sysroot routine and the body has no loop. Otherwise it mints NOTHING —
//! no row, no marker — because an Unknown marker would make every structurally
//! recursive function fatal on every lane. So `fn r(t: &T) -> u32 { r(t) }` and
//! `fn f(n: u64) -> u64 { let _ = g(); f(n) }` built rc 0 on every lane, `certify`
//! included, and overflowed the stack at run time: a silent green.
//!
//! ## The rule
//!
//! After verification, for a local `fn` / associated `fn` body (not promoted, not
//! Clean-origin) whose obligations were generated at a level that includes
//! termination (`NonTermination` is L1; see [`termination_claims_in_scope`]):
//!
//! * the SELF-CALL CENSUS is every `Call` / `TailCall` terminator whose callee —
//!   read by its fn-item TYPE ([`census_self_call_class`]), so a call through a local
//!   holding the fn item counts — resolves (`Instance::try_resolve`) to a plain
//!   `InstanceKind::Item` equal to the body's own `DefId`, or does not resolve and
//!   names the body's own `DefId` as written (a trait default method calling
//!   `self.m(..)`, which vcgen's string identity does not see as a self call), or
//!   (round 4 of ARGS-FINGERPRINT-READ-1, 2026-10-08) does not resolve and names
//!   the trait item the body implements ([`SelfCallClass`]; round 5: with NO
//!   exemption, see [`SelfCallClass::ImplementedTraitItem`]). The census is
//!   keyed on `DefId`s, never on rendered paths;
//! * if the census is non-empty and vcgen made NO recursion statement for this
//!   function — no `NonTermination { context: RECURSION_TERMINATION_CONTEXT }` row
//!   and no `RECURSION_DECREASES_UNSUPPORTED_KIND` marker among THIS function's
//!   result rows ([`vcgen_made_a_recursion_statement`]) — every census site is
//!   charged with one `assumption:termination-unmeasured` row (outcome `skipped`,
//!   solver `TERMINATION_UNMEASURED_ROW_SOLVER`, located at the call);
//! * the SELF-REFERENCE CENSUS (review F5, ruled YES 2026-09-27) is every place
//!   the body takes ITSELF as a value: a constant of its own fn-item type (peeled
//!   of references) anywhere but a call's callee position — `f as fn(..)`,
//!   `let g = f;`, `map(f)`, `Box::new(f)`, a promoted `&f`
//!   ([`self_reference_sites`]). A call through that value may re-enter the
//!   function, and no termination lane has a row for such a re-entry (vcgen reads
//!   call terminators; the recursion-SCC lane's call graph records no fn item
//!   taken as a value). So every reference is charged, one row each, with NO
//!   exemption — and never on top of an SCC row, because none covers it.
//! * the DISPATCH CENSUS (ARGS-FINGERPRINT-READ-1 round 6, 2026-10-08) is every
//!   call or fn value of the body — closures included — that dispatches through a
//!   trait method (it does not resolve to one plain body: a generic receiver, a
//!   `dyn` slot) one of whose LOCAL serving bodies reaches this body again over
//!   the local call graph ([`dispatch_reentry_sites`]): a forwarding impl that
//!   reaches `<X as Tr>::f` through a helper, a second trait or a closure; and
//!   (round 7) a `dyn Fn` / generic `F: Fn` call that a LOCAL CLOSURE may serve,
//!   when that closure reaches this body. Every such site is charged, one row
//!   each, with NO exemption: no termination lane follows a dispatched call.
//!
//! The default (strict) lane records the rows and passes, CONDITIONALLY (targo's
//! strict gate admits the shape through
//! `trust_types::assumption::strict_policy_publishes_assumption_row`), with a
//! warning in human output; memory-safe admits the row
//! (`memory_safe_artifacts_have_non_demotable_failure`); `certify` publishes the
//! rows and refuses the function with a compile error. The rows never carry
//! proof credit.
//!
//! ## Why the exemption is sound (the all-or-nothing contract)
//!
//! vcgen's recursion lanes emit, per function, either one recursion row for EVERY
//! self-call site `detect_recursive_calls` finds, or a visible never-provable
//! marker, or nothing at all — the round-2 rule ("a miss at any site now withholds
//! every inferred row"), pinned by vcgen's
//! `inferred_recursion_rows_cover_every_self_call_site_or_none`. A recursion row
//! that exists is solver-checked or Unknown (fatal); a marker is Unknown (fatal).
//! So "vcgen spoke" means the function's termination claim is visible and graded,
//! and "vcgen was silent" is exactly the silent-green case this seam charges.
//! The exemption reads only rows whose `function` is this body's (vcgen stamps the
//! item name; compiler-appended rows stamp the def path), never a callee's.
//!
//! ## What this does NOT cover (residuals, disclosed)
//!
//! * Recursion that neither calls this function directly nor takes it as a value
//!   in its own body, and that the dispatch census does not see: a cycle with two
//!   or more dispatched hops, a serving body outside this crate (a downstream impl
//!   that calls back, a foreign default body), a foreign generic that re-enters
//!   the crate (`x.into()` reaching a local `From` impl), drop glue, a call
//!   through a fn POINTER to a local closure or fn item that calls back (a fn
//!   pointer call dispatches through no trait), a LOCAL FN ITEM serving a
//!   dispatched `Fn*` call through `dyn` or a struct field (a fn item is a
//!   serving body only once its value is taken, which no cached fact records),
//!   or a fn pointer minted OUTSIDE the body (a `const`/`static`
//!   initializer, or a promoted aggregate such as `&[f, g]` whose reification
//!   happens in the promoted body). No census site exists, so nothing is charged
//!   (the recursion-SCC lane discloses the same residual). Since review F5,
//!   `let g: fn(u64) -> u64 = f; g(n)` is NOT in this class: the reification is
//!   a self reference, charged.
//! * A PARTIAL recursion row set (rows for some sites, none for others) would be
//!   exempted wholesale. Every vcgen recursion lane withholds all its rows on a
//!   miss at any site — the inferred lane since round 2, the compound
//!   `bound - counter` lane since review F3 (`compound_recursion_vcs` returns an
//!   empty set instead of skipping the site) — and the unit test above pins it
//!   per fixture. A future lane that dropped a single site would reopen the hole
//!   at that site.
//! * Loops: a loop with an exit edge and no bindable measure mints nothing and is
//!   NOT charged (loops are partial correctness, KNOWN_HAZARDS); `certify` refuses
//!   unmeasured recursion but still certifies such a loop.
//! * A caller of a charged function is not itself charged: the crate result is
//!   already conditional on the callee's row.
//!
//! ## Soundness shape
//!
//! Additive only. The seam adds rows, a warning and a certify-only error; it never
//! removes a verifier row, never changes an outcome, and never turns a refusal into
//! a pass. The only rows it strips are pre-existing rows claiming its own kind
//! (staleness/forgery defense, as the coroutine and global-alloc seams do).

use rustc_hir::def::DefKind;
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{Body, ConstOperand, Location, Operand, Terminator, TerminatorKind};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::Span;
use rustc_span::def_id::DefId;
use trust_types::assumption::{
    TERMINATION_UNMEASURED_ASSUMPTION_TAG, TERMINATION_UNMEASURED_ROW_SOLVER,
    is_termination_unmeasured_assumption_row,
};
use trust_types::{
    Outcome, ProofLevel, SourceSpan, TransportObligationResult, VcKind, VerificationCondition,
    VerificationResult,
};

use super::{
    PreparedDiagnostic, PreparedDiagnosticChild, PreparedLocatedDiagnostic, VerificationArtifacts,
};

/// The wire kind of the charge row: `assumption:termination-unmeasured`.
fn termination_unmeasured_row_kind() -> String {
    format!("assumption:{TERMINATION_UNMEASURED_ASSUMPTION_TAG}")
}

/// What `Instance::try_resolve` makes of a call terminator's callee operand.
/// Shared with `recursion_scc_termination_context`, which files SCC calls from
/// the same resolution (it skips [`DirectCallTarget::OtherInstance`] and an
/// unresolved trait method; this seam counts an unresolved callee that names the
/// body itself, the conservative direction for a charge).
pub(super) enum DirectCallTarget {
    /// Resolved to one plain body.
    Item(DefId),
    /// Resolved, but not to a plain item body (a shim, a `dyn` dispatch).
    OtherInstance,
    /// Did not resolve (too generic here, or an error): the callee as written.
    Unresolved(DefId),
}

impl DirectCallTarget {
    /// Whether this target is `own`: resolved to it, or unresolved and naming it.
    fn is(&self, own: DefId) -> bool {
        matches!(self, Self::Item(target) | Self::Unresolved(target) if *target == own)
    }
}

/// `Instance::try_resolve` of one fn item (`FnDef(def_id, generic_args)`).
fn resolve_fn_def<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    def_id: DefId,
    generic_args: ty::GenericArgs<'tcx>,
) -> DirectCallTarget {
    match ty::Instance::try_resolve(tcx, typing_env, def_id, generic_args) {
        Ok(Some(instance)) => match instance.def {
            ty::InstanceKind::Item(def_id) => DirectCallTarget::Item(def_id),
            _ => DirectCallTarget::OtherInstance,
        },
        _ => DirectCallTarget::Unresolved(def_id),
    }
}

/// `None` when the operand is not a constant fn item (a fn pointer, a closure
/// value, `dyn`): such a call names no body.
pub(super) fn resolve_direct_call_target<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    func: &Operand<'tcx>,
) -> Option<DirectCallTarget> {
    let (callee_def_id, generic_args) = func.const_fn_def()?;
    Some(resolve_fn_def(tcx, typing_env, callee_def_id, generic_args))
}

/// The charge for one body, and its sites for the human disclosure: one row per
/// unmeasured self CALL (MIR block order), then one row per self REFERENCE (MIR
/// order).
pub(super) struct TerminationUnmeasuredCharge {
    pub(super) rows: Vec<TransportObligationResult>,
    /// Direct self calls no vcgen recursion statement covers.
    pub(super) calls: Vec<Span>,
    /// This function taken as a VALUE (review F5, ruled YES 2026-09-27): a fn
    /// item constant naming it anywhere but a call's callee position — reified to
    /// a `fn` pointer, passed to another function, stored, or borrowed. Any later
    /// indirect call through that value may re-enter the function, and no
    /// termination lane charges that re-entry.
    pub(super) references: Vec<Span>,
    /// Calls (and fn values) that DISPATCH through a trait method — the callee
    /// does not resolve to one body here (a generic receiver, a `dyn` vtable) —
    /// where some local body that may serve that method reaches this function
    /// again over the local call graph ([`dispatch_reentry_sites`], round 6).
    pub(super) dispatches: Vec<Span>,
}

/// The D9 seam. `None` when nothing is charged: not a local `fn` body, a
/// Clean-origin body, obligations generated below L1 (never under certify, see
/// [`termination_claims_in_scope`]) or none generated at all (the synthetic
/// single-Unknown-row artifacts), or no uncovered site — no direct
/// self call vcgen left without a recursion statement, and no self reference.
///
/// The two kinds of site are exempted differently. A direct self call is exempt
/// when vcgen made a recursion statement for this function (the all-or-nothing
/// contract in the module doc: every self call vcgen sees is covered). A self
/// REFERENCE is never exempt: no termination lane has a row for it. vcgen's
/// direct-self lanes read call terminators only, and the recursion-SCC lane
/// charges only the edges of the local call graph
/// (`trust_direct_local_callees_of_body`: direct fn-item callees and closures
/// passed as arguments, never a fn item taken as a value), and Tarjan drops a
/// singleton component, so `t.kids.iter().map(size)` inside `size` is in no SCC.
/// Charging a reference therefore never double-charges a site an SCC row covers.
///
/// Every string is built from `func_path` (already rendered by the caller) and
/// fixed text: nothing here renders a type or a `def_path_str`, so a JSON-only
/// session that emits no diagnostic cannot trip `trimmed_def_paths`'
/// `must_produce_diag` (the X2 ICE `entry_termination_dispatch_rows` documents).
pub(super) fn termination_unmeasured_charge<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func_path: &str,
    artifacts: &VerificationArtifacts,
) -> Option<TerminationUnmeasuredCharge> {
    if body.source.promoted.is_some() {
        return None;
    }
    let def_id = body.source.def_id();
    let local = def_id.as_local()?;
    // Trust (ARGS-FINGERPRINT-READ-1 round 6): a CLOSURE body is in scope for the
    // dispatch census only. It cannot call or name itself as a fn item, so its
    // self-call and self-reference censuses are empty, but a closure inside a
    // forwarding impl can dispatch back into the impl that holds it (review
    // scratch `r9rev/probes/closure.rs`, measured with no termination row).
    let is_closure = matches!(tcx.def_kind(local), DefKind::Closure);
    if !is_closure && !matches!(tcx.def_kind(local), DefKind::Fn | DefKind::AssocFn) {
        return None;
    }
    // Clean-origin bodies are emitted from a kernel-checked Clean definition whose
    // termination is the kernel's (docs/TCB.md, the R1/R2 rows); they publish no
    // Rust verdict of their own today. Defensive.
    if crate::clean_origin_mir::is_clean_origin(tcx, local) {
        return None;
    }
    if !termination_claims_in_scope(artifacts.max_proof_level) {
        return None;
    }
    let mut calls = if is_closure { Vec::new() } else { direct_self_call_sites(tcx, body) };
    let references = if is_closure { Vec::new() } else { self_reference_sites(tcx, body) };
    // Never exempt: no termination lane follows a dispatched call (vcgen's direct-
    // self lanes do not see it as a self call, and the recursion-SCC lane files
    // only calls that resolve to one body), so no recursion statement covers it.
    let dispatches = dispatch_reentry_sites(tcx, body, local);
    if calls.is_empty() && references.is_empty() && dispatches.is_empty() {
        return None;
    }
    if !calls.is_empty() {
        let own_names = own_vc_function_names(tcx, def_id, func_path);
        if vcgen_made_a_recursion_statement(&artifacts.results, &own_names) {
            calls.clear();
        }
    }
    if calls.is_empty() && references.is_empty() && dispatches.is_empty() {
        return None;
    }
    let counts = SiteCounts {
        calls: calls.len(),
        references: references.len(),
        dispatches: dispatches.len(),
    };
    let row = |site: Span, kind: SiteKind| {
        termination_unmeasured_row(
            Some(super::source_span_from_rustc_span(tcx, site)),
            func_path,
            kind,
            counts,
        )
    };
    let rows = calls
        .iter()
        .map(|&site| row(site, SiteKind::Call))
        .chain(references.iter().map(|&site| row(site, SiteKind::Reference)))
        .chain(dispatches.iter().map(|&site| row(site, SiteKind::Dispatch)))
        .collect();
    Some(TerminationUnmeasuredCharge { rows, calls, references, dispatches })
}

/// How many sites of each kind one charge carries (for the row reason and both
/// diagnostics).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SiteCounts {
    calls: usize,
    references: usize,
    dispatches: usize,
}

/// Which kind of census site a row charges.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SiteKind {
    /// A direct self call.
    Call,
    /// This function taken as a value (review F5).
    Reference,
    /// A call or fn value dispatching through a trait method one of whose local
    /// implementations reaches this function again (round 6).
    Dispatch,
}

/// Whether this body's obligations were generated at a level that includes
/// termination. `max_level` is the level `filter_vcs_by_level` applied
/// (`VerificationArtifacts::max_proof_level`, recorded where the filter ran,
/// never re-derived); `None` means no obligations were generated (the synthetic
/// single-Unknown-row artifacts), and those bodies are already unproved.
/// Below L1 (`-Ztrust-verify-level=0`, for a body with no contract that owes no
/// callee `requires`) the compiler makes no termination claim for ANY function,
/// so a charge would be a new claim. That is a default-lane and memory-safe
/// statement only: `certify` never reaches this gate below L1 (2026-10-03,
/// docs/DECISION_QUEUE.md "L0-CERTIFY"; the driver refuses `-Ztrust-policy=certify
/// -Ztrust-verify-level=0`, and `effective_max_level` floors a certify session at
/// L1), so D9's certify refusal holds at every level a certify verdict exists.
fn termination_claims_in_scope(max_level: Option<ProofLevel>) -> bool {
    let termination = VcKind::NonTermination { context: String::new(), measure: String::new() };
    max_level.is_some_and(|max_level| termination.proof_level() <= max_level)
}

/// Every call of `body` that may run `body` itself, by `DefId` (see the module
/// doc): [`SelfCallClass::Own`], and every [`SelfCallClass::ImplementedTraitItem`]
/// call (round 5: with no structural exemption).
///
/// Trust (ARGS-FINGERPRINT-READ-1 round 4, 2026-10-08): the trait-item class is
/// NEW in this census. Before, only `Item(own) | Unresolved(own)` counted, so an
/// UNRESOLVED call to the trait item `body` implements — a where-clause
/// candidate such as `<W<(X, dup_a::T)> as Tr>::f(n)` under `where Self: Tr`,
/// or `<W<G> as Tr>::f::<G>(n)` under `where W<G>: Tr` in `impl Tr for W<u8>`
/// — was charged by nobody whenever vcgen did not read it as a self call.
/// MEASURED (scratchpad r5adv, preview3 stage 1 `7be75e9a80` and round 3):
/// `where_self_generic.rs` and `selfbound_alias.rs` built with no termination
/// row on both, and `selfbound_dup.rs` lost preview3's `unknown` row on round 3
/// (its def path is shared, so round 3's identity set withdrew the call from
/// vcgen), while each recurses forever with the same `n`.
fn direct_self_call_sites<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Vec<Span> {
    let own = body.source.def_id();
    let typing_env = ty::TypingEnv::post_analysis(tcx, own);
    let own_trait_item = tcx.trait_item_of(own);
    let mut sites = Vec::new();
    for data in body.basic_blocks.iter() {
        let Some(terminator) = &data.terminator else { continue };
        let (TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. }) =
            &terminator.kind
        else {
            continue;
        };
        let charged = match census_self_call_class(tcx, typing_env, body, func, own, own_trait_item)
        {
            SelfCallClass::Own | SelfCallClass::ImplementedTraitItem => true,
            SelfCallClass::NotSelf => false,
        };
        if charged {
            sites.push(terminator.source_info.span);
        }
    }
    sites
}

/// How one call terminator's callee relates to the body `own` that contains it,
/// decided from `DefId`s (never from a rendered path). Shared by D9's census
/// ([`direct_self_call_sites`]) and vcgen's identity set
/// ([`direct_self_call_identity_blocks`]), so the two read ONE resolution.
pub(super) enum SelfCallClass {
    /// Resolves to `own`, or does not resolve and names `own` as written.
    Own,
    /// Does not resolve, and names the trait item `own` implements: dispatch is
    /// decided by the callee's self type at monomorphization, which may select
    /// `own`'s impl (a where-clause candidate, a generic self type), or another
    /// impl that calls back into `own`.
    ///
    /// Trust (ARGS-FINGERPRINT-READ-1 round 5, 2026-10-08): NO exemption. Round 4
    /// left uncharged a call whose callee self type is a proper subterm of the
    /// impl's self type, arguing that every chain of such calls shrinks the
    /// instance type and ends. That argument only covers chains that stay inside
    /// `own`; the callee's self type is a parameter, and its impl can GROW the
    /// type again before re-entering `own`. MEASURED on the round-4 stage 1
    /// (review scratch `r7/dyn_shrink.rs`, `r8/probes/regrow.rs`), NO termination
    /// row on either while each recurses forever with the same `n`:
    /// `impl<X: ?Sized + Tr> Tr for &X { <X as Tr>::f(*self, n) }` with
    /// `X = dyn Tr` (the vtable dispatches back to `<&dyn Tr as Tr>::f`;
    /// `static S: &(dyn Tr + Sync) = &S`), and `impl<X: Tr> Tr for Box<X> {
    /// <X as Tr>::f(n) }` beside `impl Tr for u8 { <Box<u8> as Tr>::f(n) }`
    /// (polymorphic recursion through a different impl). Proving such a chain
    /// finite needs a whole-program argument no lane makes, so D9 charges every
    /// such call; the structural forwarding impl `impl<X: Fwd> Fwd for Box<X>`
    /// pays an assumption row (DECISION_QUEUE ARGS-FINGERPRINT-READ-1 round 5).
    ImplementedTraitItem,
    /// Anything else: another body, a shim, a `dyn` dispatch, a fn pointer.
    NotSelf,
}

/// The [`SelfCallClass`] of one call terminator. CENSUS-ONLY callee resolution
/// (review F6): the callee read by its TYPE, not by `Operand::const_fn_def`, so a
/// call through a LOCAL of fn-item type — `let r = f; r(n)`, which stays `move
/// _3(copy _1)` at `-Zmir-opt-level=0` — resolves exactly like the constant call
/// `f(n)`. A constant callee has the same `FnDef` type, so this finds every call
/// `resolve_direct_call_target` finds, and more. [`SelfCallClass::NotSelf`] for a
/// fn pointer, a closure value or `dyn`: no body is named.
///
/// The recursion-SCC lane keeps `resolve_direct_call_target` (constant callees,
/// the shape its own call-graph adjacency records); widening the SCC filing
/// rules is not this seam's business.
fn census_self_call_class<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    body: &Body<'tcx>,
    func: &Operand<'tcx>,
    own: DefId,
    own_trait_item: Option<DefId>,
) -> SelfCallClass {
    let ty::FnDef(def_id, generic_args) = *func.ty(&body.local_decls, tcx).kind() else {
        return SelfCallClass::NotSelf;
    };
    match resolve_fn_def(tcx, typing_env, def_id, generic_args.skip_binder()) {
        DirectCallTarget::Item(target) if target == own => SelfCallClass::Own,
        DirectCallTarget::Unresolved(target) if target == own => SelfCallClass::Own,
        DirectCallTarget::Unresolved(target) if own_trait_item == Some(target) => {
            SelfCallClass::ImplementedTraitItem
        }
        DirectCallTarget::Item(_)
        | DirectCallTarget::Unresolved(_)
        | DirectCallTarget::OtherInstance => SelfCallClass::NotSelf,
    }
}

/// Trust (ARGS-FINGERPRINT-READ-1 round 3, 2026-10-07): the call blocks of `body`
/// that MAY run `body` itself, decided from `DefId`s, for vcgen's direct-self
/// termination lanes (`VcgenContext::with_direct_self_call_blocks`), which take
/// it as a CONJUNCT of their rendered-path comparison.
///
/// The rendered def path is not an identity. Two local impls whose self types
/// differ only in a same-named crate render ONE path (`<W<dupty::T> as Tr>::f`
/// for `impl Tr for W<dup_a::T>` and `impl Tr for W<dup_b::T>`, or for
/// `W<other::T>` and `W<T>` in a Cargo bin+lib pair), and a call into the other
/// impl then read as a self call. MEASURED on the preview3 stage 1
/// (`7be75e9a80`) and on round 2: the non-recursive caller got a PROVED
/// "recursion measure `n` may not decrease" row while its callee loops forever
/// (`chain_ng.rs`, monomorphic; `binlib.rs`, generic, round 2).
///
/// A block is filed when its callee — read by TYPE ([`census_self_call_class`], the
/// census D9 charges) — resolves to `body`'s own `DefId`, or does not resolve and
/// names it, or does not resolve and names the trait item `body` implements while
/// no other local function renders `body`'s def path
/// (`trust_mir_extract::local_fn_definition_key_is_shared`; the rendering is
/// then the only identity left, and it is unique). Everything else — another
/// body, a shim, a `dyn` dispatch, a fn pointer — is not filed.
///
/// FAIL-CLOSED DIRECTION: vcgen ANDs this with its path comparison, so the set
/// can only REMOVE self-call classifications. A removed call is a non-self call:
/// the authored lane reports it as an uncertainty, the inferred lane mints no
/// descent row, and if it may in fact run this body D9 charges it: every
/// [`SelfCallClass::Own`] call is in D9's census, and so is every
/// [`SelfCallClass::ImplementedTraitItem`] call (the only class this set masks;
/// round 4: before it, D9 did not count the trait-item class, so a masked
/// where-clause self call went uncharged — `selfbound_dup.rs`, measured; round 5:
/// round 4's structural-shrinking exemption from that charge is gone).
/// `None` for a promoted body (no fact; vcgen keeps the path comparison).
pub(super) fn direct_self_call_identity_blocks<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Option<std::collections::BTreeSet<usize>> {
    if body.source.promoted.is_some() {
        return None;
    }
    let own = body.source.def_id();
    let typing_env = ty::TypingEnv::post_analysis(tcx, own);
    let own_trait_item = tcx.trait_item_of(own);
    let mut own_key_shared = None;
    let mut blocks = std::collections::BTreeSet::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        let Some(terminator) = &data.terminator else { continue };
        let (TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. }) =
            &terminator.kind
        else {
            continue;
        };
        let may_run_self =
            match census_self_call_class(tcx, typing_env, body, func, own, own_trait_item) {
                SelfCallClass::Own => true,
                SelfCallClass::ImplementedTraitItem => !*own_key_shared.get_or_insert_with(|| {
                    trust_mir_extract::local_fn_definition_key_is_shared(tcx, own)
                }),
                SelfCallClass::NotSelf => false,
            };
        if may_run_self {
            blocks.insert(bb.as_usize());
        }
    }
    Some(blocks)
}

/// Every place `body` takes ITSELF as a value (review F5): a constant whose type,
/// peeled of references, is a fn item resolving to (or naming) the body's own
/// `DefId`, anywhere except the callee operand of a `Call`/`TailCall` (that is a
/// call, the direct census's). This covers `f as fn(..)` (the `ReifyFnPointer`
/// cast's operand is that constant), `let g = f;`, `map(f)`, `Box::new(f)`, and a
/// promoted `&f`. One site per MIR location.
///
/// Every value of this function's fn-item type in the body originates at such a
/// constant, so counting the constants (not every later copy of a local holding
/// one) finds each reference once. Not seen: a fn pointer minted OUTSIDE this
/// body — in a `const`/`static` initializer, or in a promoted aggregate such as
/// `&[f, g]` whose reification happens in the promoted body (disclosed residual).
///
/// Only the body's statements and terminators are walked (`visit_basic_block_data`,
/// never `visit_body`): a debuginfo-only constant or a `required_consts` entry is
/// not a use of the value.
fn self_reference_sites<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Vec<Span> {
    let own = body.source.def_id();
    let mut census = SelfReferenceCensus {
        tcx,
        typing_env: ty::TypingEnv::post_analysis(tcx, own),
        own,
        sites: Vec::new(),
    };
    for (block, data) in body.basic_blocks.iter_enumerated() {
        census.visit_basic_block_data(block, data);
    }
    census.sites.into_iter().map(|(_, span)| span).collect()
}

struct SelfReferenceCensus<'tcx> {
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    own: DefId,
    sites: Vec<(Location, Span)>,
}

impl<'tcx> Visitor<'tcx> for SelfReferenceCensus<'tcx> {
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        match &terminator.kind {
            // The callee operand is a CALL, not a reference: skip it and visit
            // only the arguments (a fn item passed on is a reference).
            TerminatorKind::Call { args, .. } | TerminatorKind::TailCall { args, .. } => {
                for arg in args.iter() {
                    self.visit_operand(&arg.node, location);
                }
            }
            _ => self.super_terminator(terminator, location),
        }
    }

    fn visit_const_operand(&mut self, constant: &ConstOperand<'tcx>, location: Location) {
        // Only a fn item that IS the body, or a trait method (which may resolve to
        // the body's own impl item), can name it: any other fn item resolves to
        // itself or to a non-`Item` instance. So `Instance::try_resolve` runs only
        // on those candidates, never on every fn item a body passes around.
        //
        // Trust (ARGS-FINGERPRINT-READ-1 round 4): an unresolved reference to the
        // trait item this body implements may run this body exactly as such a
        // CALL may (`SelfCallClass::ImplementedTraitItem`), so it is charged on the
        // same terms (round 5: with no structural-shrinking exemption).
        if let ty::FnDef(def_id, generic_args) = *constant.const_.ty().peel_refs().kind()
            && (def_id == self.own || self.tcx.trait_of_assoc(def_id).is_some())
            && match resolve_fn_def(self.tcx, self.typing_env, def_id, generic_args.skip_binder()) {
                target if target.is(self.own) => true,
                DirectCallTarget::Unresolved(target) => {
                    self.tcx.trait_item_of(self.own) == Some(target)
                }
                DirectCallTarget::Item(_) | DirectCallTarget::OtherInstance => false,
            }
            && !self.sites.iter().any(|(seen, _)| *seen == location)
        {
            self.sites.push((location, constant.span));
        }
    }
}

/// Trust (ARGS-FINGERPRINT-READ-1 round 6, 2026-10-08): every call terminator and
/// fn value of `body` that DISPATCHES through a trait method one of whose local
/// bodies may reach `body` again — the census D9's self-call and self-reference
/// censuses leave out, because the cycle leaves `body` through a dispatched call
/// and comes back through another body.
///
/// MEASURED (review of round 5, scratch `r9rev/probes`, unix_hardened level 2 JSON,
/// on the preview3 stage 1 `7be75e9a80` and on round 5): NO termination row while
/// each recurses forever with the same `n`, when the forwarding body of
/// `impl<X: Tr> Tr for Box<X>` reaches `<X as Tr>::f` one hop away instead of
/// naming it: through a generic free helper (`helper.rs`, and the library-only
/// `helper_lib.rs`, whose twin `direct_lib.rs` IS charged since round 5), through a
/// second trait whose local impl calls back (`crosstrait.rs`: `<X as Other>::g`
/// with `impl Other for u8 { <Box<u8> as Tr>::f(n) }`), or from a closure in the
/// body (`closure.rs`).
///
/// A site is charged when its callee (read by TYPE, as [`census_self_call_class`]
/// reads it; or a fn-item constant outside callee position, as
/// [`self_reference_sites`] reads it) is a trait method that does not resolve to
/// one plain body here ([`dispatched_trait_item`]: a generic receiver, a `dyn`
/// vtable, a shim), the site is not already in D9's other censuses, and some LOCAL
/// body that may serve that method — the trait's own provided body, the item of
/// every local impl implementing it, and (round 7) for an `Fn*` / `AsyncFn*`
/// method every local closure that may implement it — reaches `body` over the crate's local
/// call graph (`trust_mir_direct_local_callees`, the recursion-SCC lane's
/// adjacency; [`DispatchReentry`]). `body` itself counts: an impl item dispatching
/// through `dyn` to its own method is charged here.
///
/// FAIL-CLOSED: a body that may serve the method but whose edges cannot be read
/// (it has MIR but is not a call-graph node: a Clean-origin or comptime body)
/// reaches `body` by assumption; so does everything when `body` is not a node.
///
/// NOT COVERED (disclosed, KNOWN_HAZARDS round 6): a cycle with TWO OR MORE
/// dispatched hops (the adjacency records no dispatched edge, so the hop out of
/// the serving body is invisible), a serving body outside this crate (a foreign
/// default body, or a DOWNSTREAM impl: the library-only `crosstrait` shape
/// `impl<X: Other> Tr for Box<X> { <X as Other>::g(n) }` is charged by nobody until
/// the crate that closes the cycle is compiled, and there the re-entry is a call
/// into a foreign body), drop glue, a local FN ITEM serving a dispatched `Fn*` call
/// from `dyn` or a struct field (review of round 6, scratch `r12/probes/
/// fnitem_dyn.rs`, `fnitem_struct.rs`: no row; a fn item passed directly as a call
/// argument is an SCC edge instead), and a call through a fn POINTER to a local
/// closure or fn item that calls back (`clos_fnptr.rs`: no row; a pointer call
/// dispatches through no trait). The whole class is a MISSING CHARGE — silent
/// divergence, never a false proof — and preview3 has every one of these gaps.
fn dispatch_reentry_sites<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    target: rustc_span::def_id::LocalDefId,
) -> Vec<Span> {
    let own = body.source.def_id();
    let typing_env = ty::TypingEnv::post_analysis(tcx, own);
    let own_trait_item = tcx.trait_item_of(own);
    let mut reentry = DispatchReentry::new(tcx, target);
    let mut sites = Vec::new();
    for data in body.basic_blocks.iter() {
        let Some(terminator) = &data.terminator else { continue };
        let (TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. }) =
            &terminator.kind
        else {
            continue;
        };
        if !matches!(
            census_self_call_class(tcx, typing_env, body, func, own, own_trait_item),
            SelfCallClass::NotSelf
        ) {
            continue;
        }
        let ty::FnDef(def_id, generic_args) = *func.ty(&body.local_decls, tcx).kind() else {
            continue;
        };
        if let Some(trait_item) =
            dispatched_trait_item(tcx, typing_env, def_id, generic_args.skip_binder())
            && reentry.may_reenter(trait_item)
        {
            sites.push(terminator.source_info.span);
        }
    }
    let mut census = DispatchReferenceCensus {
        tcx,
        typing_env,
        own,
        own_trait_item,
        reentry,
        sites: Vec::new(),
    };
    for (block, data) in body.basic_blocks.iter_enumerated() {
        census.visit_basic_block_data(block, data);
    }
    sites.extend(census.sites.into_iter().map(|(_, span)| span));
    sites
}

/// The trait method the fn item `FnDef(def_id, generic_args)` DISPATCHES through:
/// `Some(def_id)` when `def_id` is a trait method and `Instance::try_resolve` does
/// not pick one plain body for it here (it does not resolve, or resolves to a
/// `dyn` vtable slot or a shim). `None` for any other fn item, and for a trait
/// method that resolves to one body (that call is a plain edge of the local call
/// graph, the recursion-SCC lane's business).
fn dispatched_trait_item<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    def_id: DefId,
    generic_args: ty::GenericArgs<'tcx>,
) -> Option<DefId> {
    tcx.trait_of_assoc(def_id)?;
    match resolve_fn_def(tcx, typing_env, def_id, generic_args) {
        DirectCallTarget::Item(_) => None,
        DirectCallTarget::OtherInstance | DirectCallTarget::Unresolved(_) => Some(def_id),
    }
}

/// The fn values of [`dispatch_reentry_sites`]: a fn-item constant (peeled of
/// references) outside a call's callee position that dispatches through a trait
/// method, and is not already a self reference ([`SelfReferenceCensus`]).
struct DispatchReferenceCensus<'tcx> {
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    own: DefId,
    own_trait_item: Option<DefId>,
    reentry: DispatchReentry<'tcx>,
    sites: Vec<(Location, Span)>,
}

impl<'tcx> Visitor<'tcx> for DispatchReferenceCensus<'tcx> {
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        match &terminator.kind {
            TerminatorKind::Call { args, .. } | TerminatorKind::TailCall { args, .. } => {
                for arg in args.iter() {
                    self.visit_operand(&arg.node, location);
                }
            }
            _ => self.super_terminator(terminator, location),
        }
    }

    fn visit_const_operand(&mut self, constant: &ConstOperand<'tcx>, location: Location) {
        let ty::FnDef(def_id, generic_args) = *constant.const_.ty().peel_refs().kind() else {
            return;
        };
        let Some(trait_item) =
            dispatched_trait_item(self.tcx, self.typing_env, def_id, generic_args.skip_binder())
        else {
            return;
        };
        // Already a self reference (`SelfReferenceCensus` charges an UNRESOLVED fn
        // item naming the body or the trait item it implements); a `dyn` slot or
        // a shim naming them is not, and is charged here.
        let is_self_reference = (trait_item == self.own || self.own_trait_item == Some(trait_item))
            && matches!(
                resolve_fn_def(self.tcx, self.typing_env, def_id, generic_args.skip_binder()),
                DirectCallTarget::Unresolved(_)
            );
        if !is_self_reference
            && !self.sites.iter().any(|(seen, _)| *seen == location)
            && self.reentry.may_reenter(trait_item)
        {
            self.sites.push((location, constant.span));
        }
    }
}

/// Whether a dispatched trait method may run `target` again: some local body that
/// may serve it reaches `target` over the crate's local call graph. Memoized per
/// trait method; the explored set is shared across searches for ONE target, since
/// a completed search that did not find `target` explored a set whose forward
/// closure excludes it (cleared whenever a search stops early).
struct DispatchReentry<'tcx> {
    tcx: TyCtxt<'tcx>,
    target: rustc_span::def_id::LocalDefId,
    memo: rustc_data_structures::fx::FxHashMap<DefId, bool>,
    explored: rustc_data_structures::fx::FxHashSet<rustc_span::def_id::LocalDefId>,
}

impl<'tcx> DispatchReentry<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, target: rustc_span::def_id::LocalDefId) -> Self {
        Self { tcx, target, memo: Default::default(), explored: Default::default() }
    }

    fn may_reenter(&mut self, trait_item: DefId) -> bool {
        if let Some(&known) = self.memo.get(&trait_item) {
            return known;
        }
        let answer = self.local_servers(trait_item).into_iter().any(|server| self.reaches(server));
        self.memo.insert(trait_item, answer);
        answer
    }

    /// The local bodies that may serve `trait_item`: its provided body when the
    /// trait is local, the item implementing it in every local impl, and — for a
    /// method of `Fn` / `FnMut` / `FnOnce` / `AsyncFn*` — every local closure body
    /// whose type may implement that trait ([`closure_may_serve`]).
    fn local_servers(&self, trait_item: DefId) -> Vec<rustc_span::def_id::LocalDefId> {
        let tcx = self.tcx;
        let Some(trait_def_id) = tcx.trait_of_assoc(trait_item) else { return Vec::new() };
        let mut servers: Vec<_> = trait_item.as_local().into_iter().collect();
        for &impl_def_id in tcx.local_trait_impls(trait_def_id) {
            if let Some(&item) =
                tcx.impl_item_implementor_ids(impl_def_id.to_def_id()).get(&trait_item)
                && let Some(local) = item.as_local()
            {
                servers.push(local);
            }
        }
        // Trust (ARGS-FINGERPRINT-READ-1 round 7, 2026-10-08): a closure implements
        // the `Fn*` traits by a BUILTIN impl, so `local_trait_impls` never lists it,
        // and a dispatched `<F as Fn>::call` / `<dyn Fn as Fn>::call` served by a
        // local closure that calls back was charged by nobody (review of round 6,
        // scratch `r11rev/probes`: `clos_dyn`, `clos_dynarg`, `clos_struct`, no
        // termination row on preview3 or round 6). Every local closure body that
        // may implement the trait serves it.
        let fn_kind = tcx.fn_trait_kind_from_def_id(trait_def_id);
        let async_fn_kind = tcx.async_fn_trait_kind_from_def_id(trait_def_id);
        if fn_kind.is_some() || async_fn_kind.is_some() {
            servers.extend(tcx.mir_keys(()).iter().copied().filter(|&local| {
                matches!(tcx.def_kind(local), DefKind::Closure)
                    && closure_may_serve(tcx, local, fn_kind)
            }));
        }
        servers
    }

    fn reaches(&mut self, start: rustc_span::def_id::LocalDefId) -> bool {
        let tcx = self.tcx;
        if start == self.target {
            return true;
        }
        // A required method with no provided body runs nothing.
        if !tcx.is_mir_available(start.to_def_id()) {
            return false;
        }
        // Fail closed: the adjacency may be read only for call-graph nodes.
        if !super::trust_mir_call_graph_node_eligible(tcx, self.target)
            || !super::trust_mir_call_graph_node_eligible(tcx, start)
        {
            self.explored.clear();
            return true;
        }
        if !self.explored.insert(start) {
            return false;
        }
        let mut stack = vec![start];
        while let Some(node) = stack.pop() {
            for &next in tcx.trust_mir_direct_local_callees(node) {
                if next == self.target || !super::trust_mir_call_graph_node_eligible(tcx, next) {
                    self.explored.clear();
                    return true;
                }
                if self.explored.insert(next) {
                    stack.push(next);
                }
            }
        }
        false
    }
}

/// Whether the local closure-kinded body `closure` may serve a dispatched method of
/// an `Fn*` trait (`fn_kind` is `Some(kind)` for `Fn` / `FnMut` / `FnOnce`, `None`
/// for an `AsyncFn*` trait). Only two answers are `false`, both by the builtin
/// impls' shape: a plain closure whose inferred kind does not extend the `Fn*`
/// trait's (`ClosureKind::extends`: an `FnOnce` closure implements neither `Fn`
/// nor `FnMut`), and a coroutine body (an `async`/`gen` block or an `async fn`'s
/// body), which implements no `Fn*` or `AsyncFn*` trait. Anything else — an async
/// closure, a closure under an `AsyncFn*` trait, a kind not yet known — may serve
/// (fail-closed).
fn closure_may_serve(
    tcx: TyCtxt<'_>,
    closure: rustc_span::def_id::LocalDefId,
    fn_kind: Option<ty::ClosureKind>,
) -> bool {
    match *tcx.type_of(closure).instantiate_identity().skip_norm_wip().kind() {
        ty::Coroutine(..) => false,
        ty::Closure(_, args) => {
            match (fn_kind, args.as_closure().kind_ty().to_opt_closure_kind()) {
                (Some(trait_kind), Some(closure_kind)) => closure_kind.extends(trait_kind),
                _ => true,
            }
        }
        _ => true,
    }
}

/// The two spellings a row of THIS function carries in `VerificationCondition::
/// function`: vcgen stamps the extracted item name (`trust_mir_extract`'s
/// `opt_item_name`, falling back to the last path segment), compiler-appended rows
/// stamp the def path (`func_path` is `safe_def_path_str`, the extractor's
/// `def_path`). The precedent is the root-row filter reading
/// `vc.function == root.def_path || vc.function == root.name`.
fn own_vc_function_names(tcx: TyCtxt<'_>, def_id: DefId, func_path: &str) -> [String; 2] {
    let name = tcx
        .opt_item_name(def_id)
        .map(|symbol| symbol.to_string())
        .unwrap_or_else(|| func_path.rsplit("::").next().unwrap_or(func_path).to_string());
    [name, func_path.to_string()]
}

/// Whether vcgen made a recursion statement for the function named by
/// `own_names`: a recursion `NonTermination` row, or the recursion `decreases`
/// marker. Rows of other functions are ignored (a callee's row says nothing about
/// this body's self calls).
fn vcgen_made_a_recursion_statement(
    results: &[(VerificationCondition, VerificationResult)],
    own_names: &[String],
) -> bool {
    results.iter().any(|(vc, _)| {
        own_names.iter().any(|name| vc.function.as_str() == name.as_str())
            && match &vc.kind {
                VcKind::NonTermination { context, .. } => {
                    context == trust_vcgen::RECURSION_TERMINATION_CONTEXT
                }
                VcKind::UnsupportedMir { kind, .. } => {
                    kind == trust_vcgen::RECURSION_DECREASES_UNSUPPORTED_KIND
                }
                _ => false,
            }
    })
}

/// The row's detail: which function, which site, and why there is no claim.
/// Marker-free.
fn charge_detail(func_path: &str, kind: SiteKind) -> String {
    match kind {
        SiteKind::Call => format!(
            "termination of `{func_path}`: this self call binds no `decreases` measure, and the \
             direct-self termination lane made no claim for it"
        ),
        SiteKind::Reference => format!(
            "termination of `{func_path}`: this reference takes the function as a value, and a \
             call through it may re-enter the function where no `decreases` measure and no \
             termination lane reaches"
        ),
        SiteKind::Dispatch => format!(
            "termination of `{func_path}`: this call or fn value dispatches through a trait \
             method one of whose local implementations calls back into this function, and no \
             termination lane follows a dispatched call"
        ),
    }
}

/// What the charged sites are, for the row reason and both diagnostics. With no
/// self reference the text is exactly the diagnostics' pre-F5 wording, so every
/// call-only annotation stays valid.
///
/// Round 6: dispatched sites append their own clause, so a charge with none keeps
/// exactly the earlier wording.
fn sites_summary(counts: SiteCounts) -> String {
    let SiteCounts { calls, references, dispatches } = counts;
    let calls_text = format!("{calls} self call(s) bind no `decreases` measure");
    let references_text = format!(
        "{references} self reference(s) take this function as a value, which may re-enter it"
    );
    let dispatches_text = format!(
        "{dispatches} dispatched call(s) reach a trait method whose local implementation calls \
         back into this function"
    );
    let own = match (calls, references) {
        (0, 0) => None,
        (_, 0) => Some(calls_text),
        (0, _) => Some(format!("{references_text} with no `decreases` measure")),
        _ => Some(format!("{calls_text}, and {references_text}")),
    };
    match (own, dispatches) {
        (Some(own), 0) => own,
        (None, _) => format!("{dispatches_text}, with no `decreases` measure"),
        (Some(own), _) => format!("{own}; {dispatches_text}"),
    }
}

/// The row's reason (the critique's H4 text: it does not claim the function's
/// other rows verified — they are reported, and graded, separately).
fn charge_reason(counts: SiteCounts) -> String {
    format!(
        "termination assumption `{TERMINATION_UNMEASURED_ASSUMPTION_TAG}`: {}; this function's \
         other rows are reported separately; the crate's result is conditional on the \
         recursion terminating; `--certify` refuses it",
        sites_summary(counts)
    )
}

/// One charge row. The `transport_assumption_row` contract (`assumption:<tag>`
/// kind, `skipped`, no typed kind, "unverified assumption: " description, no
/// full-verifier marker text in any field), built without a `TyCtxt` so the shape
/// is unit-tested as a whole.
fn termination_unmeasured_row(
    location: Option<SourceSpan>,
    func_path: &str,
    kind: SiteKind,
    counts: SiteCounts,
) -> TransportObligationResult {
    TransportObligationResult {
        assumes: Vec::new(),
        gap_class: None,
        monitor: None,
        obligation_id: None,
        claim_digest_sha256: None,
        kind: termination_unmeasured_row_kind(),
        original_vc_snapshot: None,
        typed_kind: None,
        description: format!("unverified assumption: {}", charge_detail(func_path, kind)),
        location,
        outcome: Outcome::Skipped,
        solver: TERMINATION_UNMEASURED_ROW_SOLVER.to_string(),
        time_ms: 0,
        counterexample: None,
        counterexample_model: None,
        reason: Some(charge_reason(counts)),
        design_mandate: false,
        native_trust_ir: None,
        proof_evidence: None,
        grade: None,
    }
}

/// `rows` with every pre-existing row of the charge kind removed and the charge
/// (if any) appended. `None` — use `rows` unchanged — when there is no charge and
/// nothing to strip, so an uncharged body allocates nothing.
pub(super) fn rows_with_termination_unmeasured(
    rows: &[TransportObligationResult],
    charge: Option<&TerminationUnmeasuredCharge>,
) -> Option<Vec<TransportObligationResult>> {
    let kind = termination_unmeasured_row_kind();
    if charge.is_none() && !rows.iter().any(|row| row.kind == kind) {
        return None;
    }
    let mut out: Vec<TransportObligationResult> =
        rows.iter().filter(|row| row.kind != kind).cloned().collect();
    if let Some(charge) = charge {
        out.extend(charge.rows.iter().cloned());
    }
    Some(out)
}

/// The rows the ZERO-obligation transport branch publishes (critique H3: do NOT
/// divert a charged body to the `effective_rows` branch — that would drop the
/// honest `native-verification-gap` row, an Unknown, and leave only the charge,
/// which targo grades conditional: a weaker result). The base is exactly what the
/// branch published before D9 — the synthetic `no_obligations` row, the gap row,
/// or the transport rows — and the charge is appended to it.
pub(super) fn zero_obligation_rows(
    native_vacuously_clean: bool,
    transport_results: &[TransportObligationResult],
    charge: Option<&TerminationUnmeasuredCharge>,
) -> Vec<TransportObligationResult> {
    let base = if native_vacuously_clean {
        vec![super::transport_no_obligations_row()]
    } else if transport_results.is_empty() {
        vec![super::transport_native_verification_gap_row()]
    } else {
        transport_results.to_vec()
    };
    rows_with_termination_unmeasured(&base, charge).unwrap_or(base)
}

/// The exact compiler shape of the charge row, for the memory-safe admission
/// (critique H1: the ruling makes the default lane CONDITIONAL and says nothing
/// that would make memory-safe refuse; refusing there would be an unratified
/// capability loss). A row claiming the kind in any other shape stays fatal.
pub(super) fn transport_row_is_termination_unmeasured_assumption(
    row: &TransportObligationResult,
) -> bool {
    is_termination_unmeasured_assumption_row(&row.kind, &row.solver)
        && row.outcome == Outcome::Skipped
        && row.typed_kind.is_none()
        && !row.design_mandate
        && row.native_trust_ir.is_none()
        && row.proof_evidence.is_none()
}

const DISCLOSURE_NOTE: &str = "recorded as `assumption:termination-unmeasured` (skipped, NOT \
     proved): the crate's result is CONDITIONAL on this recursion terminating, and \
     `-Ztrust-policy=certify` refuses it";

const FIX_NOTE: &str = "add a function-level `decreases` naming an integer parameter that \
     strictly decreases at every self call; a structural measure over non-integer data (a \
     tree, a slice) has no `decreases` spelling yet";

const REFERENCE_FIX_NOTE: &str = "a call through a fn pointer, a `dyn Fn`, or a fn item handed \
     to another function is covered by no `decreases` clause: call this function directly \
     where it recurses, so a measure can bind at the call";

const DISPATCH_FIX_NOTE: &str = "a cycle that leaves this function through trait dispatch (a \
     generic or `dyn` receiver) and comes back through another body is covered by no `decreases` \
     clause: recurse by a direct self call where a measure can bind";

impl TerminationUnmeasuredCharge {
    fn counts(&self) -> SiteCounts {
        SiteCounts {
            calls: self.calls.len(),
            references: self.references.len(),
            dispatches: self.dispatches.len(),
        }
    }
}

/// The human disclosure on every non-`certify` lane (human output only; targo
/// reads the row).
pub(super) fn warn_termination_unmeasured(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    func_path: &str,
    charge: &TerminationUnmeasuredCharge,
) {
    prepare_termination_unmeasured_warning(tcx, body, func_path, charge).emit(tcx);
}

// Trust: retain the original source span and ordered diagnostic children as DATA.
pub(super) fn prepare_termination_unmeasured_warning(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    func_path: &str,
    charge: &TerminationUnmeasuredCharge,
) -> PreparedLocatedDiagnostic {
    let span = tcx.def_span(body.source.def_id());
    let header = format!(
        "Trust verification advisory for `{func_path}`: termination is ASSUMED, not proved \
         — {}",
        sites_summary(charge.counts())
    );
    let mut children = Vec::new();
    for &site in &charge.calls {
        children.push(PreparedDiagnosticChild::SpanNote(
            site,
            "this self call's termination is assumed".into(),
        ));
    }
    for &site in &charge.references {
        children.push(PreparedDiagnosticChild::SpanNote(
            site,
            "this reference may re-enter the function; that re-entry's termination is assumed"
                .into(),
        ));
    }
    for &site in &charge.dispatches {
        children.push(PreparedDiagnosticChild::SpanNote(
            site,
            "this dispatched call may re-enter the function through another body; that \
             re-entry's termination is assumed"
                .into(),
        ));
    }
    children.push(PreparedDiagnosticChild::Note(DISCLOSURE_NOTE.into()));
    if !charge.calls.is_empty() {
        children.push(PreparedDiagnosticChild::Note(FIX_NOTE.into()));
    }
    if !charge.references.is_empty() {
        children.push(PreparedDiagnosticChild::Note(REFERENCE_FIX_NOTE.into()));
    }
    if !charge.dispatches.is_empty() {
        children.push(PreparedDiagnosticChild::Note(DISPATCH_FIX_NOTE.into()));
    }
    PreparedLocatedDiagnostic {
        span,
        diagnostic: PreparedDiagnostic { aborting: false, header, children },
    }
}

/// `certify` refuses a function carrying the charge. Emitted in every output
/// mode, like the other certify aborts; the message renders only `func_path`.
pub(super) fn abort_on_termination_unmeasured(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    func_path: &str,
    charge: &TerminationUnmeasuredCharge,
) {
    prepare_termination_unmeasured_refusal(tcx, body, func_path, charge).emit(tcx);
}

// Trust: prepare the same certify refusal without emitting or rebuilding spans.
pub(super) fn prepare_termination_unmeasured_refusal(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    func_path: &str,
    charge: &TerminationUnmeasuredCharge,
) -> PreparedLocatedDiagnostic {
    let span = tcx.def_span(body.source.def_id());
    let header = format!(
        "Trust certify verification failed for `{func_path}`: termination is not \
         established — {}",
        sites_summary(charge.counts())
    );
    let mut children = Vec::new();
    for &site in &charge.calls {
        children.push(PreparedDiagnosticChild::SpanNote(
            site,
            "this self call has no termination proof".into(),
        ));
    }
    for &site in &charge.references {
        children.push(PreparedDiagnosticChild::SpanNote(
            site,
            "this reference may re-enter the function with no termination proof".into(),
        ));
    }
    for &site in &charge.dispatches {
        children.push(PreparedDiagnosticChild::SpanNote(
            site,
            "this dispatched call may re-enter the function through another body with no \
             termination proof"
                .into(),
        ));
    }
    children.push(PreparedDiagnosticChild::Note(
        "under `-Ztrust-policy=certify` an `assumption:termination-unmeasured` row is fatal; \
         the default lane records it and passes CONDITIONALLY"
            .into(),
    ));
    if !charge.calls.is_empty() {
        children.push(PreparedDiagnosticChild::Note(FIX_NOTE.into()));
    }
    if !charge.references.is_empty() {
        children.push(PreparedDiagnosticChild::Note(REFERENCE_FIX_NOTE.into()));
    }
    if !charge.dispatches.is_empty() {
        children.push(PreparedDiagnosticChild::Note(DISPATCH_FIX_NOTE.into()));
    }
    PreparedLocatedDiagnostic {
        span,
        diagnostic: PreparedDiagnostic { aborting: true, header, children },
    }
}

#[cfg(test)]
mod tests;

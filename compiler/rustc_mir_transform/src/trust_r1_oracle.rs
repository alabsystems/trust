// trust_r1_oracle.rs: the trustc caller-coverage oracle for R1 whole-program
// strengthening (#540). Computes the SOUND `CoverageSignals` the pure decision core
// (`trust_router::strengthen_whole_program`) needs: F's verdict may be flipped by an
// inferred precondition P only if EVERY possible caller of F establishes P. Any
// uncertainty here MUST force `Incomplete` coverage ⇒ F keeps its honest Failed
// verdict. See docs/STRENGTHEN-R1-CALLER-COVERAGE-ORACLE.md for the full reject list.
//
// INCREMENT 2a: the crate-wide address-taken / direct-call MIR scan is REAL now (it
// replaces increment 1's `address_taken = true` stub). `scan_crate_calls` walks every
// fn/closure body and marks a function `address_taken` iff its `FnDef` constant ever
// appears OUTSIDE the `func` position of a direct `Call`/`TailCall` (i.e. coerced to a
// fn pointer, placed in a `dyn` vtable, passed as a callback) — an uncountable caller.
// A direct-call `func` is recorded as an edge, NOT as address-taken.
//
// 2a-HARDENING (required BEFORE 2b enables any flip — both DONE here):
//   * BODY COVERAGE: the scan now walks EVERY mir_keys body, not just fn/closure
//     bodies. const/static/anon-const/inline-const item bodies are fetched via
//     `mir_for_ctfe` (the steal CONSUMER — stable even after early const-eval steals
//     `mir_drops_elaborated_and_const_checked`), trivial consts via `trivial_const`
//     (they keep no ctfe/promoted body), and EVERY owner's `promoted_mir` fragments
//     are scanned too — so a `FnDef` in `static T:[fn();1]=[f]` or a promoted `&[f]`
//     temp is caught as address-taken. A body we MUST account for but cannot
//     (fn-like `Steal` already stolen, or an unrecognized body-owner kind) POISONS
//     the whole scan (`incomplete = true`) ⇒ `compute_coverage_signals` rejects EVERY
//     function. We NEVER skip a missing body (that could hide an address-take).
//   * RECURSION: a full iterative Tarjan SCC over the direct-call `edges` now marks
//     every member of a call cycle `recursive` (mutual recursion), not just self-loops.

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_data_structures::unord::UnordSet;
use rustc_hir::def::DefKind;
use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{ConstOperand, Location, Terminator, TerminatorKind};
use rustc_middle::ty::{self, GenericArgsRef, TyCtxt, TypingEnv};
use rustc_span::def_id::{DefId, LocalDefId};
use trust_router::strengthen_whole_program::CoverageSignals;

// Trust (R1 completeness #3 — per-monomorphization caller coverage): a single resolved
// in-crate MONOMORPHIZATION of a callee `F::<A>` observed at a direct call site, together
// with the caller whose body holds it. A generic F's safety (e.g. `i < N` for `idx::<N>`)
// and its caller set DIFFER PER MONO, so R1 keys generic coverage on the (DefId, resolved
// GenericArgs) pair — NOT on the DefId alone. Only used for generic F closed in-crate; a
// pub-in-lib generic F keeps its visibility rejection (a downstream crate could instantiate
// a NEW mono with an unsafe caller).
#[derive(Clone)]
pub(crate) struct MonoCallSite<'tcx> {
    /// The resolved generic args of this call's callee instance (`A` in `F::<A>`).
    pub args: GenericArgsRef<'tcx>,
    /// The in-crate function whose body holds this call.
    pub caller: DefId,
    /// The call terminator's source `(line_start, col_start)`. Lets the per-mono harvest
    /// match EACH generated caller-site precondition VC (`vc.location`) to the mono it
    /// belongs to — so a caller that calls TWO monos of F (`idx::<4>(a,3); idx::<8>(b,5)`)
    /// discharges each site under ITS OWN mono's P (never conflating them). Source spans are
    /// mono-independent, so the generic-body span here matches the monomorphized-body VC span.
    pub call_line_col: (u32, u32),
}

/// One reproducible direct-call site from the same MIR scan that builds the
/// crate call graph.
///
/// Unlike [`MonoCallSite`], this inventory is independent of generic-instance
/// resolution. The recursive induction harvest uses it as the authoritative
/// multiset of intra-SCC edges: every exact `(caller, callee, span)` here must
/// have exactly one attributed precondition row, and no attributed row may
/// appear without a matching entry. Tail calls and calls in const/promoted
/// bodies are deliberately absent because they are recorded in
/// `hidden_call_target` and make recursive coverage ineligible altogether.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct DirectCallSite {
    pub caller: DefId,
    pub callee: DefId,
    pub call_site: trust_types::SourceSpan,
}

/// Whole-crate call facts feeding the coverage oracle.
pub(crate) struct CrateCallInfo<'tcx> {
    /// Functions whose `FnDef` is taken as a first-class value somewhere (fn pointer,
    /// vtable, callback) — i.e. reachable by an UNCOUNTABLE indirect call.
    pub address_taken: FxHashSet<DefId>,
    /// Functions in a call cycle: any member of an SCC of size > 1 (mutual recursion)
    /// or any function with a direct self-call (Tarjan over the direct-call `edges`).
    pub recursive: FxHashSet<DefId>,
    /// Trust (R1 completeness #4 — inductive recursive proof): for EACH recursive `DefId`
    /// (self-loop or mutual-recursion SCC member) its full call-cycle membership set. A
    /// self-recursive function maps to `{itself}`; a 2-member mutual-recursion SCC maps
    /// each member to `{both}`. The inductive-flip harvest needs the SCC members to (a)
    /// classify a caller edge as INTRA-SCC (an inductive recursive call whose args must
    /// preserve P) vs EXTERNAL (a base-case caller that must establish P), and (b) require
    /// the WHOLE SCC to be jointly inductive. Keyed by `DefId`, over the SAME Tarjan run
    /// that fills `recursive`. Absent for a non-recursive function.
    pub recursive_scc: FxHashMap<DefId, UnordSet<DefId>>,
    /// A body the scan was REQUIRED to account for was unavailable (an already-stolen
    /// fn-like `Steal`, or an unrecognized body-owner kind). When set, the scan may
    /// have missed an address-taking use, so `compute_coverage_signals` rejects EVERY
    /// function (no flip is sound). Fail-closed: we poison rather than skip.
    pub incomplete: bool,
    /// Reverse direct-call graph: callee `DefId` -> deduped caller `DefId`s, over the
    /// SAME edges Tarjan uses. Exhaustive for any `Total`-covered F (a Total F is neither
    /// address-taken nor externally reachable nor hidden-called ⇒ every caller is a
    /// recorded local direct-call edge). Keyed by `DefId` — no string/suffix resolution.
    pub callers: FxHashMap<DefId, Vec<DefId>>,
    /// Exact reproducible direct-call-site multiset. This is intentionally a
    /// `Vec`, not a set: two calls with the same source span remain two oracle
    /// edges and therefore require two generated discharge rows.
    pub direct_call_sites: Vec<DirectCallSite>,
    /// Callees reached by an edge the vcgen producer CANNOT reproduce: a `TailCall`
    /// (the extractor lowers it to `Terminator::Opaque`, so no precondition obligation is
    /// emitted for it), or any edge found while scanning a non-reproducible body (a
    /// const/static item body or a `promoted_mir` fragment). Folded into `is_public` so
    /// such a callee is never `Total` — closing the "covered but a hidden site is
    /// undischarged" hole.
    pub hidden_call_target: FxHashSet<DefId>,
    /// Trust (R1 completeness #3): per-callee resolved MONOMORPHIZATION call sites. For a
    /// generic in-crate F, `mono_call_sites[F]` lists every direct call whose callee
    /// resolves to a mono of F, tagged with the resolved args + the caller. Keyed by the
    /// callee's *generic* `DefId` (the shared def), so grouping by `args` recovers each
    /// distinct mono. Only populated from REPRODUCIBLE (fn/closure main) bodies, over the
    /// SAME direct-call edges the DefId-level `callers` graph uses.
    pub mono_call_sites: FxHashMap<DefId, Vec<MonoCallSite<'tcx>>>,
    /// Trust (R1 completeness #3): callees whose per-mono enumeration is NOT trustworthy —
    /// a direct call to the (generic) callee whose `Instance::try_resolve` returned
    /// `None`/`Err` (an unresolvable mono the scan cannot pin), OR a call reached through a
    /// non-reproducible/hidden edge. Such a callee is POISONED from per-mono coverage: R1
    /// must NOT flip a generic F if ANY of its call sites resolved ambiguously, because an
    /// unenumerated mono could have an unsafe caller. Fail-closed.
    pub mono_unresolved: FxHashSet<DefId>,
}

/// Trust (R1 completeness #3): the `(line_start, col_start)` of a source span, matching
/// `trust_mir_extract::convert_span`'s convention (1-based line, 0-based col; dummy → (0,0)).
/// Used to key a mono call site to the caller-site VC the producer emits for it.
fn span_line_col(tcx: TyCtxt<'_>, span: rustc_span::Span) -> (u32, u32) {
    if span.is_dummy() {
        return (0, 0);
    }
    let lo = tcx.sess.source_map().lookup_char_pos(span.lo());
    (lo.line as u32, lo.col.0 as u32)
}

/// Convert a rustc span byte-for-byte like
/// `trust_mir_extract::convert_span`, so the oracle's call-site identity and
/// the attributed VC producer can be compared structurally rather than by
/// diagnostic text or a fixed-width digest.
fn source_span(tcx: TyCtxt<'_>, span: rustc_span::Span) -> trust_types::SourceSpan {
    if span.is_dummy() {
        return trust_types::SourceSpan::default();
    }
    let source_map = tcx.sess.source_map();
    let lo = source_map.lookup_char_pos(span.lo());
    let hi = source_map.lookup_char_pos(span.hi());
    trust_types::SourceSpan {
        file: lo.file.name.prefer_local_unconditionally().to_string(),
        line_start: lo.line as u32,
        col_start: lo.col.0 as u32,
        line_end: hi.line as u32,
        col_end: hi.col.0 as u32,
    }
}

/// MIR visitor accumulating address-taken functions + direct-call edges for one body.
struct CallScan<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: DefId,
    /// The owner body's `TypingEnv`, used to `Instance::try_resolve` each call's callee
    /// `(DefId, GenericArgs)` to its monomorphization (Trust R1 completeness #3).
    owner_typing_env: TypingEnv<'tcx>,
    address_taken: &'a mut FxHashSet<DefId>,
    edges: &'a mut Vec<(DefId, DefId)>,
    /// Reproducible, non-tail direct sites, with multiplicity and exact span.
    direct_call_sites: &'a mut Vec<DirectCallSite>,
    /// Callees reached by an edge the producer cannot reproduce (a `TailCall`, or any
    /// edge in a non-reproducible body). Recorded so such a callee is poisoned from
    /// `Total` coverage — its call site would never become a discharge obligation.
    hidden: &'a mut FxHashSet<DefId>,
    /// Trust (R1 completeness #3): per-callee resolved mono call sites, keyed by the
    /// callee's generic DefId.
    mono_call_sites: &'a mut FxHashMap<DefId, Vec<MonoCallSite<'tcx>>>,
    /// Trust (R1 completeness #3): callees whose per-mono enumeration is untrustworthy.
    mono_unresolved: &'a mut FxHashSet<DefId>,
    /// True only for a fn/closure MAIN body (the bodies the producer re-runs on). Const/
    /// static item bodies and promoted fragments pass `false`, so every direct edge they
    /// carry is recorded `hidden`.
    reproducible: bool,
}

impl<'tcx> Visitor<'tcx> for CallScan<'_, 'tcx> {
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        let direct = match &terminator.kind {
            TerminatorKind::Call { func, args, .. } => {
                func.const_fn_def().map(|(callee, gargs)| (callee, gargs, args, false))
            }
            TerminatorKind::TailCall { func, args, .. } => {
                // The extractor lowers TailCall to Terminator::Opaque ⇒ no obligation.
                func.const_fn_def().map(|(callee, gargs)| (callee, gargs, args, true))
            }
            _ => None,
        };
        if let Some((callee, gargs, args, is_tail)) = direct {
            // Direct `FnDef` call: record the edge and visit ONLY the argument operands,
            // so the callee in `func` is NOT counted as address-taken. The destination
            // is a Place (carries no constants) and is safely skipped.
            self.edges.push((self.owner, callee));
            if is_tail || !self.reproducible {
                self.hidden.insert(callee);
            } else {
                self.direct_call_sites.push(DirectCallSite {
                    caller: self.owner,
                    callee,
                    call_site: source_span(self.tcx, terminator.source_info.span),
                });
            }
            // Trust (R1 completeness #3): resolve this call's monomorphization. Only a
            // reproducible, non-tail edge can become a per-caller discharge obligation, so
            // only those feed `mono_call_sites`; any OTHER kind of edge into `callee`
            // (tail-call, const/static/promoted body) is an unaccountable mono site ⇒
            // poison. A resolve failure (unknown mono) also poisons — fail-closed.
            if self.reproducible && !is_tail {
                match ty::Instance::try_resolve(self.tcx, self.owner_typing_env, callee, gargs) {
                    Ok(Some(instance)) => {
                        // Record under the callee's GENERIC def_id (the shared def);
                        // grouping the recorded sites by `args` recovers each mono.
                        // `instance.def_id()` == `callee` for `InstanceKind::Item`; for a
                        // shim/virtual/intrinsic instance it differs — such a callee is
                        // never a plain in-crate generic fn we per-mono cover, so poison it
                        // to stay fail-closed rather than mis-attribute its args.
                        if matches!(instance.def, ty::InstanceKind::Item(_))
                            && instance.def_id() == callee
                        {
                            let call_line_col =
                                span_line_col(self.tcx, terminator.source_info.span);
                            self.mono_call_sites.entry(callee).or_default().push(MonoCallSite {
                                args: instance.args,
                                caller: self.owner,
                                call_line_col,
                            });
                        } else {
                            self.mono_unresolved.insert(callee);
                        }
                    }
                    // Unresolvable (still-generic caller env, or an ambiguous instance) ⇒
                    // this mono is not pinned; poison the callee from per-mono coverage.
                    _ => {
                        self.mono_unresolved.insert(callee);
                    }
                }
            } else {
                self.mono_unresolved.insert(callee);
            }
            for a in args.iter() {
                self.visit_operand(&a.node, location);
            }
            return;
        }
        self.super_terminator(terminator, location);
    }

    fn visit_const_operand(&mut self, constant: &ConstOperand<'tcx>, _location: Location) {
        if let ty::FnDef(did, _) = constant.const_.ty().kind() {
            self.address_taken.insert(*did);
        }
    }
}

/// Scan EVERY mir_keys body once for address-taken functions + direct-call edges,
/// routing each body owner to the MIR query that still holds its elaborated body at
/// the analysis phase (mirrors `trust_init_backing_certificates`' pre-steal borrow for
/// fn-like bodies, and uses the steal CONSUMER queries for const/static + promoteds so
/// early const-eval cannot have stolen them out from under us). Any body we are
/// REQUIRED to account for but cannot ⇒ `incomplete = true` (poison the whole scan).
#[allow(rustc::untracked_query_information, rustc::potential_query_instability)]
pub(crate) fn scan_crate_calls<'tcx>(tcx: TyCtxt<'tcx>) -> CrateCallInfo<'tcx> {
    let mut address_taken = FxHashSet::default();
    let mut edges: Vec<(DefId, DefId)> = Vec::new();
    let mut direct_call_sites = Vec::new();
    let mut hidden: FxHashSet<DefId> = FxHashSet::default();
    let mut mono_call_sites: FxHashMap<DefId, Vec<MonoCallSite<'tcx>>> = FxHashMap::default();
    let mut mono_unresolved: FxHashSet<DefId> = FxHashSet::default();
    let mut incomplete = false;

    for &local in tcx.mir_keys(()) {
        let did = local.to_def_id();

        // (a) Tuple-struct / variant constructors are synthetic ADT-aggregate shims:
        //     they hold no `FnDef` constants and make no calls, so they can address-take
        //     nothing. Skipping them is sound (and avoids the ctor special-cases inside
        //     `mir_for_ctfe` / `promoted_mir`).
        if tcx.is_constructor(did) {
            continue;
        }

        // (b) Trivial consts (`const N: usize = 4`, including const-of-const chains)
        //     keep NO `mir_for_ctfe` / `promoted_mir` body — `mir_built` fast-paths them
        //     and those queries `debug_assert!(!is_trivial_const)`. Their whole body is a
        //     single `_0 = const <value>`; the ONLY function-valued thing it can hold is
        //     a `FnDef` ZST, so inspect the trivial value directly (sound, no assert, no
        //     skip). A trivial const has no promoteds, so we are done with it.
        if let Some((_val, ty)) = tcx.trivial_const(did) {
            if let ty::FnDef(callee, _) = ty.kind() {
                address_taken.insert(*callee);
            }
            continue;
        }

        // (c) Scan the owner's own (non-trivial) body via the right query.
        let body_scanned = match tcx.def_kind(did) {
            // fn / closure / coroutine / synthetic coroutine body, INCLUDING const fns:
            // the elaborated body is a `Steal` borrowed pre-codegen-steal. `mir_for_ctfe`
            // only CLONES a const fn (never steals it), and `optimized_mir`'s steal is a
            // codegen-phase event, so at the analysis phase this borrow is valid.
            DefKind::Fn | DefKind::AssocFn | DefKind::Closure | DefKind::SyntheticCoroutineBody => {
                let steal = tcx.mir_drops_elaborated_and_const_checked(local);
                if steal.is_stolen() {
                    false
                } else {
                    let body = steal.borrow();
                    let mut scan = CallScan {
                        tcx,
                        owner: did,
                        owner_typing_env: body.typing_env(tcx),
                        address_taken: &mut address_taken,
                        edges: &mut edges,
                        direct_call_sites: &mut direct_call_sites,
                        hidden: &mut hidden,
                        mono_call_sites: &mut mono_call_sites,
                        mono_unresolved: &mut mono_unresolved,
                        reproducible: true,
                    };
                    scan.visit_body(&body);
                    true
                }
            }
            // const / static / anon-const / inline-const ITEM body. `optimized_mir` is
            // never built for these (it panics on them); their elaborated body lives in
            // `mir_for_ctfe`, the steal CONSUMER, which returns a stable `&Body` even
            // after early const-eval already stole `mir_drops_elaborated_and_const_checked`.
            // `static T:[fn();1]=[f]` puts the `FnDef` `f` here.
            DefKind::Const { .. }
            | DefKind::AssocConst { .. }
            | DefKind::Static { .. }
            | DefKind::AnonConst
            | DefKind::InlineConst => {
                let body = tcx.mir_for_ctfe(did);
                let mut scan = CallScan {
                    tcx,
                    owner: did,
                    owner_typing_env: TypingEnv::post_analysis(tcx, did),
                    address_taken: &mut address_taken,
                    edges: &mut edges,
                    direct_call_sites: &mut direct_call_sites,
                    hidden: &mut hidden,
                    mono_call_sites: &mut mono_call_sites,
                    mono_unresolved: &mut mono_unresolved,
                    reproducible: false,
                };
                scan.visit_body(body);
                true
            }
            // Any other body-owner kind is unexpected here: fail closed (poison), never
            // silently skip — an unscanned body could hide an address-take.
            _ => false,
        };
        if !body_scanned {
            incomplete = true;
            continue;
        }

        // (d) Promoted fragments of this owner (`&[f]`, `&FOO` temporaries lifted out of
        //     the main body) carry their own `FnDef` constants. `promoted_mir` is the
        //     steal CONSUMER (stable `&IndexVec`, empty for most owners). Trivial consts
        //     (which have no promoteds and would trip the assert) already `continue`d above.
        for promoted in tcx.promoted_mir(did).iter() {
            let mut scan = CallScan {
                tcx,
                owner: did,
                owner_typing_env: TypingEnv::post_analysis(tcx, did),
                address_taken: &mut address_taken,
                edges: &mut edges,
                direct_call_sites: &mut direct_call_sites,
                hidden: &mut hidden,
                mono_call_sites: &mut mono_call_sites,
                mono_unresolved: &mut mono_unresolved,
                reproducible: false,
            };
            scan.visit_body(promoted);
        }
    }

    // MUST-FIX (global_asm escapes the scan): `mir_keys` STRIPS `DefKind::GlobalAsm` fake
    // bodies (rustc_mir_transform/src/lib.rs retains-filter), so the loop above never scans
    // them — yet `global_asm!{ sym F }`, or a template string naming F's mangled symbol, makes
    // F callable from inline assembly: an UNCOUNTABLE caller the address-taken scan cannot
    // enumerate (and a mangled-symbol string names no `FnDef` operand, so scanning the fake
    // body's operands would not even suffice). Fail closed exactly as for any unscannable body:
    // if the crate contains ANY global-asm item, poison the whole scan ⇒ no function is ever
    // `Total` ⇒ R1 is disabled crate-wide.
    if tcx.hir_crate_items(()).definitions().any(|d| matches!(tcx.def_kind(d), DefKind::GlobalAsm))
    {
        incomplete = true;
    }

    let (recursive, recursive_scc) = recursive_defs(&edges);
    // Trust: dedup via a seen-set, not `Vec::contains` — high fan-in callees
    // (utility fns called from thousands of sites) made the per-edge linear
    // scan quadratic. Insertion order of each callers list is preserved.
    let mut callers: FxHashMap<DefId, Vec<DefId>> = FxHashMap::default();
    let mut seen_edges: FxHashSet<(DefId, DefId)> = FxHashSet::default();
    for &(caller, callee) in &edges {
        if seen_edges.insert((caller, callee)) {
            callers.entry(callee).or_default().push(caller);
        }
    }
    CrateCallInfo {
        address_taken,
        recursive,
        recursive_scc,
        incomplete,
        callers,
        direct_call_sites,
        hidden_call_target: hidden,
        mono_call_sites,
        mono_unresolved,
    }
}

/// Iterative Tarjan SCC over the direct-call `edges`. Returns `(recursive, recursive_scc)`:
/// `recursive` is every `DefId` in a call cycle (each member of an SCC of size > 1 —
/// mutual recursion — plus any node with a direct self-call), and `recursive_scc` maps
/// each such `DefId` to the FULL set of its call-cycle members (Trust R1 completeness #4:
/// the inductive-flip harvest classifies each caller edge as intra-SCC vs external and
/// requires the whole SCC jointly inductive). A self-recursive node maps to `{itself}`;
/// every member of a size-N mutual-recursion SCC maps to the SAME N-member set. Iterative
/// (explicit work stack) to avoid blowing the native stack on deep call graphs. Endpoints
/// that are callees we never scanned (e.g. cross-crate) become sink nodes with no
/// out-edges and cannot manufacture a cycle.
fn recursive_defs(
    edges: &[(DefId, DefId)],
) -> (FxHashSet<DefId>, FxHashMap<DefId, UnordSet<DefId>>) {
    // 1. Intern both endpoints of every edge into a dense index space.
    let mut index_of: FxHashMap<DefId, u32> = FxHashMap::default();
    let mut nodes: Vec<DefId> = Vec::new();
    for &(a, b) in edges {
        for d in [a, b] {
            if !index_of.contains_key(&d) {
                index_of.insert(d, nodes.len() as u32);
                nodes.push(d);
            }
        }
    }
    let n = nodes.len();
    let mut recursive: FxHashSet<DefId> = FxHashSet::default();
    let mut recursive_scc: FxHashMap<DefId, UnordSet<DefId>> = FxHashMap::default();
    if n == 0 {
        return (recursive, recursive_scc);
    }

    // 2. Adjacency + self-edge flags.
    let mut adj: Vec<Vec<u32>> = vec![Vec::new(); n];
    let mut has_self = vec![false; n];
    for &(a, b) in edges {
        let ai = index_of[&a];
        let bi = index_of[&b];
        adj[ai as usize].push(bi);
        if ai == bi {
            has_self[ai as usize] = true;
        }
    }

    // 3. Iterative Tarjan. `idx == UNVISITED` marks not-yet-discovered.
    const UNVISITED: u32 = u32::MAX;
    let mut idx = vec![UNVISITED; n];
    let mut low = vec![0u32; n];
    let mut on_stack = vec![false; n];
    let mut scc_stack: Vec<u32> = Vec::new();
    let mut next_index: u32 = 0;
    // DFS frames: (node, next-adjacency-cursor). Cursor 0 also marks "first visit".
    let mut work: Vec<(u32, u32)> = Vec::new();
    let mut members: Vec<usize> = Vec::new();

    for start in 0..n {
        if idx[start] != UNVISITED {
            continue;
        }
        work.push((start as u32, 0));
        while let Some(&(v_u32, cursor)) = work.last() {
            let v = v_u32 as usize;
            if cursor == 0 {
                // First time we touch v: assign discovery index + push to the SCC stack.
                idx[v] = next_index;
                low[v] = next_index;
                next_index += 1;
                scc_stack.push(v_u32);
                on_stack[v] = true;
            }
            if (cursor as usize) < adj[v].len() {
                work.last_mut().unwrap().1 = cursor + 1;
                let w = adj[v][cursor as usize] as usize;
                if idx[w] == UNVISITED {
                    work.push((w as u32, 0));
                } else if on_stack[w] && idx[w] < low[v] {
                    low[v] = idx[w];
                }
            } else {
                // v fully explored: if it roots an SCC, pop the whole component.
                if low[v] == idx[v] {
                    members.clear();
                    loop {
                        let w = scc_stack.pop().unwrap() as usize;
                        on_stack[w] = false;
                        members.push(w);
                        if w == v {
                            break;
                        }
                    }
                    if members.len() > 1 {
                        // Trust (R1 completeness #4): a mutual-recursion SCC. Every member
                        // is `recursive`, AND each maps to the SHARED full member set so the
                        // inductive harvest can enumerate the whole cycle.
                        let member_dids: UnordSet<DefId> =
                            members.iter().map(|&m| nodes[m]).collect();
                        for &m in &members {
                            recursive.insert(nodes[m]);
                            recursive_scc.insert(nodes[m], member_dids.clone());
                        }
                    }
                }
                work.pop();
                if let Some(&(p_u32, _)) = work.last() {
                    let p = p_u32 as usize;
                    if low[v] < low[p] {
                        low[p] = low[v];
                    }
                }
            }
        }
    }

    // 4. Direct self-calls are recursive even though they form a size-1 SCC. Their SCC is
    //    the singleton `{itself}` (Trust R1 completeness #4). A self-call inside a LARGER
    //    mutual-recursion SCC already got the full member set at step 3 above; only insert
    //    the singleton when this node is not already recorded, so we never shrink a real
    //    mutual-recursion SCC down to `{itself}`.
    for v in 0..n {
        if has_self[v] {
            recursive.insert(nodes[v]);
            recursive_scc.entry(nodes[v]).or_insert_with(|| {
                let mut s = UnordSet::default();
                s.insert(nodes[v]);
                s
            });
        }
    }
    (recursive, recursive_scc)
}

/// The R1 danger sub-signals shared by the DefId-level coverage (`compute_coverage_signals`)
/// and the per-mono coverage (`generic_mono_coverable`). Every field is a "cannot enumerate
/// a caller" hazard EXCEPT `generic`, which is a "must switch to per-mono keying" flag (not a
/// hazard on its own once the closed-world condition holds).
struct DangerSignals {
    /// F is not an ordinary/assoc fn (closure, const, static, ctor, ...).
    bad_kind: bool,
    /// F is reachable from a downstream crate (visibility / symbol export / foreign).
    externally_exposed: bool,
    /// F is a trait-declared or trait-impl method (vtable / generic dispatch).
    trait_dispatchable: bool,
    /// F requires monomorphization (generic).
    generic: bool,
    /// F is in a call cycle (self- or mutual-recursion).
    recursive: bool,
    /// F is a local lang item (compiler-injected call sites the scan can't enumerate).
    lang_item: bool,
}

/// Compute the shared danger sub-signals for F. Pure over rustc queries + the crate scan.
fn compute_danger_signals(
    tcx: TyCtxt<'_>,
    f: LocalDefId,
    info: &CrateCallInfo<'_>,
) -> DangerSignals {
    let did = f.to_def_id();
    let kind = tcx.def_kind(did);
    let bad_kind = !matches!(kind, DefKind::Fn | DefKind::AssocFn);
    let ev = tcx.effective_visibilities(());
    let cg = tcx.codegen_fn_attrs(did);
    let exactly_bin = !tcx.crate_types().is_empty()
        && tcx
            .crate_types()
            .iter()
            .all(|ct| matches!(ct, rustc_session::config::CrateType::Executable));
    let visibility_exposed = !exactly_bin && ev.public_at_level(f).is_some();
    // The crate ENTRY function (`main`/`#[start]`) is invoked by the language
    // runtime, not by any enumerable in-crate call site — an external caller by
    // construction, in EVERY crate type (including exactly-bin, where the
    // visibility contribution is suppressed). Explicit, not incidental: without
    // this, `main` was excluded only because its zero-parameter signature made
    // every candidate `P` fail the contract-assumption gate — a brittle
    // side effect, not a stated invariant.
    let entry_invoked = tcx.entry_fn(()).is_some_and(|(entry_did, _)| entry_did == did);
    let externally_exposed = visibility_exposed
        || entry_invoked
        || cg.contains_extern_indicator()
        || cg.flags.intersects(CodegenFnAttrFlags::USED_COMPILER | CodegenFnAttrFlags::USED_LINKER)
        || tcx.is_foreign_item(did);
    let trait_dispatchable = matches!(kind, DefKind::AssocFn)
        && (tcx.trait_of_assoc(did).is_some() || tcx.trait_impl_of_assoc(did).is_some());
    let generic = tcx.generics_of(did).requires_monomorphization(tcx);
    let recursive = info.recursive.contains(&did);
    let lang_item = tcx.lang_items().iter().any(|(_, ldid)| ldid == did);
    DangerSignals {
        bad_kind,
        externally_exposed,
        trait_dispatchable,
        generic,
        recursive,
        lang_item,
    }
}

/// Trust (R1 completeness #3 — per-monomorphization caller coverage): is the GENERIC
/// function `f` coverable per-monomorphization? True iff F is a closed-world generic whose
/// every in-crate call site resolved to a concrete mono the scan could pin. The driver, on
/// `true`, runs the PER-MONO harvest (extract F monomorphized to each observed `A`, and
/// require every caller of each `F::<A>` to establish P for that mono) INSTEAD of the
/// DefId-level path — which cannot handle a generic (its `[u8; N]` stays symbolic).
///
/// SOUNDNESS — the closed-world condition is load-bearing: a mono `F::<A>` is coverable only
/// if ALL of its instantiations are IN THIS CRATE. A `pub` generic fn in a lib crate is NOT
/// closed (a downstream crate could instantiate `F::<A>` with an unsafe caller we never see),
/// so `externally_exposed` REJECTS it — identical to the DefId-level visibility gate. Every
/// other hazard (address-taken, recursion, trait-dispatch, lang-item, bad-kind, scan
/// incompleteness, hidden edge) is kept per-mono. `mono_unresolved` fail-closes any callee
/// with an unresolvable/tail/const-body call site. `mono_call_sites` must be non-empty (a
/// generic with zero in-crate call sites has no observed monos ⇒ nothing to flip). The pure
/// core (`mint_caller_propagation_certificate`, one sealed kernel-replayed certificate per
/// mono) still owns the final soundness decision per mono.
pub(crate) fn generic_mono_coverable(
    tcx: TyCtxt<'_>,
    f: LocalDefId,
    info: &CrateCallInfo<'_>,
) -> bool {
    let did = f.to_def_id();
    let d = compute_danger_signals(tcx, f, info);
    d.generic
        && !d.bad_kind
        && !d.externally_exposed
        && !d.trait_dispatchable
        && !d.recursive
        && !d.lang_item
        && !info.incomplete
        && !info.hidden_call_target.contains(&did)
        && !info.address_taken.contains(&did)
        && !info.mono_unresolved.contains(&did)
        && info.mono_call_sites.get(&did).is_some_and(|v| !v.is_empty())
}

/// Trust (R1 completeness #4 — inductive recursive proof): is the RECURSIVE function `f`
/// eligible for the inductive-invariant flip path? True iff F is in a call cycle (self- or
/// mutual-recursion) AND EVERY OTHER closed-world R1 hazard is clear — F is a private-or-
/// exactly-bin ordinary/assoc fn, not address-taken, not trait-dispatchable, not a lang
/// item, NON-GENERIC (a generic recursive fn would need per-mono AND induction jointly; we
/// stay fail-closed and defer it), the crate scan is complete, and no hidden/tail edge
/// reaches F. On `true` the driver runs `try_harvest_recursive_flip` (base case: every
/// EXTERNAL caller establishes P; inductive step: P proved preserved across each intra-SCC
/// recursive call) INSTEAD of the DefId path (which rejects any recursion outright).
///
/// SOUNDNESS — this only makes F *eligible* to be considered; the harvest itself must still
/// (a) build+solve a REAL inductive VC at every recursive call site and (b) discharge every
/// external caller. The recursion signal is the ONLY R1 hazard this relaxes; every other
/// caller-uncountability hazard is kept EXACTLY as the DefId path enforces it, so an
/// address-taken / pub-in-lib / generic / trait-dispatch recursive fn is still rejected.
pub(crate) fn recursive_inductive_coverable(
    tcx: TyCtxt<'_>,
    f: LocalDefId,
    info: &CrateCallInfo<'_>,
) -> bool {
    let did = f.to_def_id();
    let d = compute_danger_signals(tcx, f, info);
    d.recursive
        && !d.generic
        && !d.bad_kind
        && !d.externally_exposed
        && !d.trait_dispatchable
        && !d.lang_item
        && !info.incomplete
        && !info.hidden_call_target.contains(&did)
        && !info.address_taken.contains(&did)
        // The full SCC membership must be recorded (it always is when `d.recursive`),
        // and every SCC member must ALSO be a local, non-generic, private ordinary/assoc
        // fn with no other hazard — a mutual-recursion cycle is only jointly inductive if
        // the WHOLE cycle is closed-world coverable. A cross-crate or hazardous member ⇒
        // reject (fail-closed).
        && info
            .recursive_scc
            .get(&did)
            .is_some_and(|members| scc_all_members_coverable(tcx, members, info))
}

/// Trust (R1 completeness #4): every member of a mutual-recursion SCC must itself be a
/// local, non-generic, private/exactly-bin, non-address-taken, non-trait-dispatch,
/// non-lang-item ordinary/assoc fn with no hidden edge — else the cycle is not closed-world
/// jointly inductive and R1 must reject it. Fail-closed on any cross-crate / non-local /
/// hazardous member.
fn scc_all_members_coverable(
    tcx: TyCtxt<'_>,
    members: &UnordSet<DefId>,
    info: &CrateCallInfo<'_>,
) -> bool {
    // Query each member in stable DefPathHash order. This result is logically an `all`, but
    // deterministic query demand also keeps incremental diagnostics and caches reproducible.
    let members = tcx.with_stable_hashing_context(|mut hcx| members.to_sorted(&mut hcx, true));
    members.into_iter().all(|&m| {
        let Some(m_local) = m.as_local() else {
            return false; // a cross-crate SCC member ⇒ unenumerable ⇒ reject
        };
        let d = compute_danger_signals(tcx, m_local, info);
        // Do NOT check `d.recursive` here (every member IS recursive by construction).
        !d.generic
            && !d.bad_kind
            && !d.externally_exposed
            && !d.trait_dispatchable
            && !d.lang_item
            && !info.hidden_call_target.contains(&m)
            && !info.address_taken.contains(&m)
    })
}

/// Conservative caller-coverage signals for the local function `f`. Every hazard that
/// could mean "a caller exists that we cannot enumerate" forces `Incomplete` (via
/// `is_public` or `address_taken`); the pure core then keeps F's honest verdict.
pub(crate) fn compute_coverage_signals(
    tcx: TyCtxt<'_>,
    f: LocalDefId,
    info: &CrateCallInfo<'_>,
) -> CoverageSignals {
    let did = f.to_def_id();
    let kind = tcx.def_kind(did);

    // Not an ordinary/assoc fn (closure, const, static, ctor, ...) ⇒ reject.
    let bad_kind = !matches!(kind, DefKind::Fn | DefKind::AssocFn);
    // An out-of-crate DIRECT caller can exist only if F is reachable from a downstream
    // crate by a route the in-crate caller scan cannot enumerate: (1) F is nameable
    // downstream — directly, via a `pub use` re-export, or leaked through any interface
    // (`effective_visibilities` is public at SOME level); (2) F is exported by symbol
    // (`#[no_mangle]`/`#[export_name]`/explicit `#[linkage]` via `contains_extern_indicator`,
    // or kept-and-symbol-bearing via `#[used]`); or (3) F is a foreign/intrinsic item.
    //
    // We deliberately do NOT fold in `tcx.reachable_set(())`. That set ALSO contains
    // purely-PRIVATE helpers that are merely codegen-reachable THROUGH an exported caller
    // (inlined or monomorphized into it). Such a helper is never *independently* callable
    // downstream: every one of its invocations is either an enumerated in-crate direct call
    // OR an inlined/monomorphized copy of one of those callsites carrying the SAME actuals —
    // both covered by the per-caller discharge obligation, whose `¬P[σ]`-UNSAT certificate
    // proves P over ALL of the caller's free inputs (hence also for the exported caller's own
    // downstream callers). Folding `reachable_set` was sound but spuriously marked EVERY
    // private helper in a library crate not-Total (nothing was ever flippable). Likewise
    // `cross_crate_inlinable` is dropped: it gates whether F's MIR is *emitted* for inlining,
    // not whether F is independently callable — a non-exported inlinable F is still reached
    // only through an enumerated caller. Value-leaks (a `FnDef` used as a value / `impl Fn`
    // return / fn pointer / vtable entry) are caught independently below by `address_taken`
    // and by `trait_dispatchable`, NOT by visibility.
    let ev = tcx.effective_visibilities(());
    let cg = tcx.codegen_fn_attrs(did);
    // Trust (R1 completeness #1 — closed exactly-bin crate): in a compilation whose
    // crate-type set is EXACTLY {Executable}, the crate is CLOSED. A binary produces an
    // executable; nothing links a `.rlib`/`.so` against it, so a `pub fn` has NO
    // out-of-crate consumer that could name and call it. The ONLY external reachability
    // routes that survive in such a crate are symbol export / address-take / foreignness /
    // lang-item lowering — all of which we keep below. So in an exactly-bin crate the
    // `pub`-visibility contribution to `externally_exposed` is DROPPED: a private-or-pub
    // fn that is not symbol-exported, not address-taken, not foreign, not a lang item is
    // reachable ONLY through the in-crate caller scan R1 already enumerates exhaustively
    // (and whose every member must establish P). If the set contains ANY of
    // Lib/Rlib/Dylib/Cdylib/StaticLib/ProcMacro/Sdylib (or is empty) the crate may be
    // linked against downstream and a `pub fn` keeps its visibility-driven rejection —
    // identical to today's behavior. `is_empty()` guard: never treat an unknown/empty
    // crate-type set as closed (fail closed to the visibility gate).
    let exactly_bin = !tcx.crate_types().is_empty()
        && tcx
            .crate_types()
            .iter()
            .all(|ct| matches!(ct, rustc_session::config::CrateType::Executable));
    // The visibility contribution is suppressed ONLY in an exactly-bin (closed) crate.
    let visibility_exposed = !exactly_bin && ev.public_at_level(f).is_some();
    // The crate ENTRY function is invoked by the language runtime — an external
    // caller no in-crate scan enumerates, surviving even the exactly-bin
    // suppression above (a binary's `main` is precisely how the outside world
    // enters it). Explicit, not incidental (see `compute_danger_signals`).
    let entry_invoked = tcx.entry_fn(()).is_some_and(|(entry_did, _)| entry_did == did);
    let externally_exposed = visibility_exposed
        || entry_invoked
        || cg.contains_extern_indicator()
        || cg.flags.intersects(CodegenFnAttrFlags::USED_COMPILER | CodegenFnAttrFlags::USED_LINKER)
        || tcx.is_foreign_item(did);
    // Trait-declared OR trait-IMPL method ⇒ reachable via trait object / generic dispatch.
    // Both gates matter (spec R-TRAIT-8 + R-TRAIT-9): analysis-phase MIR records the
    // trait-DECL DefId at a `dyn`/generic callsite (so an impl method's `callers` map is
    // empty today), but the impl method is what lands in vtables — reject it directly so
    // the flip is impossible independent of that edge-keying invariant (defense-in-depth).
    let trait_dispatchable = matches!(kind, DefKind::AssocFn)
        && (tcx.trait_of_assoc(did).is_some() || tcx.trait_impl_of_assoc(did).is_some());
    // Generic F ⇒ pre-mono callsite scan can't pin σ; downstream may instantiate.
    let generic = tcx.generics_of(did).requires_monomorphization(tcx);
    // In a call cycle (self- or mutual-recursion SCC) ⇒ reject (folded into is_public).
    let recursive = info.recursive.contains(&did);
    // SHOULD-FIX (lang items): `reachable_set` formerly seeded EVERY local lang item; the
    // visibility/symbol signal above does not. A *function* lang item (a crate's own
    // `#[panic_handler]`, `eh_personality`, allocator/`oom` shim, `panic_bounds_check`, …) is
    // invoked by COMPILER-INJECTED lowering whose call sites are not direct `Call` edges at the
    // analysis seam — so `info.callers[F]` would be incomplete while F looks private. Reject any
    // local lang item ⇒ fail closed. The lang-item table is tiny and mostly cross-crate (core/
    // std), so this is a cheap, usually-empty scan for a normal crate.
    let lang_item = tcx.lang_items().iter().any(|(_, ldid)| ldid == did);

    CoverageSignals {
        // `info.incomplete` poisons EVERY function: the crate-wide scan could not account
        // for some body, so we cannot rule out an unseen address-taking use of `f`.
        is_public: info.incomplete
            || info.hidden_call_target.contains(&did)
            || bad_kind
            || externally_exposed
            || trait_dispatchable
            || generic
            || recursive
            || lang_item,
        // REAL scan now: address-taken ⇒ an uncountable indirect caller ⇒ reject.
        address_taken: info.address_taken.contains(&did),
        unresolved_callees: Vec::new(),
    }
}

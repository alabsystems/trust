//! Trust (2026-09-26, std-absent-callee): the SYSROOT PANIC CENSUS.
//!
//! # What it decides
//!
//! A call from a verified body into a `core`/`alloc`/`std` function whose body is
//! not in the lowered bundle reaches the bridge's absent-callee arm, which models
//! it as "may panic, unconditionally" (`Assert(false)` plus one
//! `[trust-absent-callee-assumption]` row). Under the default policy that row is a
//! reported completeness gap (the 2026-07-25 completeness-gap ruling, policy B);
//! under `-Ztrust-policy=certify` it is fatal. So before this module `certify`
//! refused every program that called ANY std routine the bundling lanes declined,
//! and the callee's real panic behaviour never entered the decision.
//!
//! The census reads that behaviour from std's OWN optimized MIR — the MIR this
//! toolchain's sysroot encodes for every function (`-Zalways-encode-mir`,
//! `src/bootstrap/src/core/build_steps/compile.rs`) — at the exact instance the
//! call resolves to, and answers one of two things:
//!
//! * [`CensusVerdict::Total`]: no panic site is reachable from the instance, for
//!   ANY argument values. The call carries no panic, so the compiler files it on
//!   the bridge's authenticated compiler-total channel and the blanket row is
//!   never minted. This is a DERIVATION over the callee's real body, not a name
//!   list: nothing is admitted because of what it is called.
//! * [`CensusVerdict::Reaches`]: the walk reached sites it cannot show
//!   non-panicking. The call keeps its row, and the sites — the function in std
//!   that holds each site, and what the site is — become the precise reason a
//!   `certify` refusal prints ([`certify_refusal_notes`]).
//!
//! The census never REMOVES a discharge another lane made and never adds a row:
//! a `Reaches` verdict leaves the call exactly where it was before this module.
//! Its only authority is the `Total` verdict, and that is what the rest of these
//! notes argue.
//!
//! # The walk
//!
//! A bounded, path-sensitive walk over the instance's MIR along NORMAL control
//! flow (an unwind edge is only taken after a panic, which the walk has already
//! reported as a site by then). A small constant environment follows each path:
//! MIR constants, copies of known locals, `Discriminant` of a known enum value,
//! boolean `!`/`&`/`|`/`^`, integer `==`/`!=` and unsigned orderings, and the
//! known return value of a callee the walk already summarized. A `SwitchInt` or
//! `Assert` whose operand is KNOWN on the path takes only the edge that value
//! selects; everything else takes every edge. A local whose address is taken
//! anywhere in the body is never tracked (it could be written through the
//! pointer), a projected write forgets its whole local, and a `Move` call operand
//! is forgotten after the call (MIR may pass it in place). A callee is read from
//! the call operand's `FnDef` TYPE, so a zero-sized function item held in a local
//! is followed like a constant one. `assume(c)` with `c` known `false` ends the
//! path — MIR defines it as equivalent to `Unreachable` — and after `assume(x)` a
//! tracked `bool` local `x` is known `true`. Every terminator must be one of:
//!
//! * `Goto`, `SwitchInt`, `Return`, `Unreachable` — no panic (`UnwindResume` and
//!   `UnwindTerminate` live only in cleanup blocks, which normal flow never
//!   reaches);
//! * `Assert` whose condition is known to hold on the path — no panic; any other
//!   `Assert` is a SITE (bounds, overflow, division);
//! * `Drop` of a type that needs no drop — nothing runs; otherwise the resolved
//!   drop glue is walked like a call;
//! * `Call`/`TailCall` that RETURNS, to a callee that is (a) a sysroot-resident
//!   `Item` with MIR and no extern indicator, walked recursively; (b) a compiler
//!   shim (drop glue, fn-pointer / closure / reify / clone / vtable / thread-local
//!   shims), whose MIR is walked the same way, so a user closure it forwards to is
//!   met as a non-sysroot `Item` and reported; (c) a `#[rustc_nounwind]`
//!   intrinsic that is handed no callable — except the three validity asserts
//!   (`assert_inhabited`, `assert_zero_valid`, `assert_mem_uninitialized_valid`),
//!   which panic for an invalid type and are decided by rustc's own
//!   `check_validity_requirement` at the instantiated type — plus its fallback
//!   body when it has one; (d) a foreign import with a non-unwinding C-family ABI
//!   that is not an allocator symbol (the `abi_total_panic_free_callees`
//!   doctrine: it cannot unwind into the caller, and it has no Rust body).
//!
//! Every other shape is a SITE: a diverging call (`panic_fmt`, `unwrap_failed`,
//! `capacity_overflow`, `handle_alloc_error`, `abort`, `exit` — every diverging
//! call is charged whatever the callee is, the same conservative over-charge the
//! bridge's `is_diverging_panic_or_abort_terminal` makes), a virtual or
//! fn-pointer call, a call into non-sysroot code (a user closure, a user impl
//! selected by a type argument), a sysroot item with an extern indicator (a
//! symbol a link can replace), a foreign Rust-ABI or unwinding symbol, the global
//! allocator (`#[rustc_allocator]`-family imports — a final link may bind a user
//! `#[global_allocator]`), inline asm, a coroutine terminator, recursion, an
//! unresolvable or unnormalizable call, a missing body, a type holding a coroutine
//! of the crate being compiled (below), or budget exhaustion. A site is never
//! excused; it only makes the verdict `Reaches`.
//!
//! # A coroutine of this crate is never queried
//!
//! The census runs inside the verified body's own `optimized_mir`, so it may only
//! send rustc queries that cannot need a body whose `optimized_mir` is already on
//! the stack (docs/KNOWN_HAZARDS.md, the CLOSED 2026-09-25 E0391 entry). Every query
//! it sends about a sysroot body is answered from crate metadata, except those that
//! reach a COROUTINE of the crate being compiled: rustc answers a coroutine's drop
//! glue (`resolve_instance_raw` reads `optimized_mir(coroutine).coroutine_drop_async()`)
//! and its layout (`coroutine_layout` is read off its `optimized_mir`) from that
//! coroutine's own optimized MIR, and so do the drop shims, `needs_drop`-guarded
//! resolutions, layout-dependent constants (`size_of::<T>()`, `T::IS_ZST`) and
//! validity checks of every type that holds one. An `async fn` that calls back into
//! the verified function (`async fn foo() { bar() }` / `fn bar() { drop(foo()) }`)
//! has its coroutine's `optimized_mir` on the stack below the verified body's, and
//! asking aborted valid Rust with `error[E0391]` under every policy. rustc's own
//! inliner avoids the same edge by never inlining into a coroutine. The oracle
//! `optimized_mir_query_would_cycle` cannot stand in for the rule: it sees only
//! bodies whose `TrustVerify` pass is running, not a coroutine whose
//! `optimized_mir` is earlier in its pipeline.
//!
//! So before any query, a root whose generic arguments, or a walked instance, call,
//! drop or constant whose type, holds a coroutine, coroutine closure or coroutine
//! witness DEFINED IN THIS CRATE — after normalization, so a revealed `impl Future`
//! counts, and through the declared fields of this crate's own ADTs, so a field
//! typed with a type-alias `impl Trait` counts — is declined: a root is refused
//! with that reason, a walked step is a site, and a constant is left unknown. A
//! coroutine of another crate is not declined: its optimized MIR comes from that
//! crate's metadata and is never on this compilation's query stack. This is a
//! decline, never a grant: such a call keeps the absent-callee row it had before
//! the census existed. The search is BOUNDED (`MAX_COROUTINE_SEARCH_TYPES` distinct
//! types per question) and a search that hits the bound answers "holds": a local
//! ADT whose fields recurse polymorphically (`struct S<T>(Option<Box<S<Vec<T>>>>)`)
//! yields a new, larger field type at every step, and an unbounded walk of it
//! overflowed the stack (SIGBUS) on valid Rust.
//!
//! # The one premise, and why it is not an assumption that a panicking callee cannot panic
//!
//! `Operand::RuntimeChecks(UbChecks)` evaluates to `false` in the walk. Those
//! operands guard `assert_unsafe_precondition!` (and std's IO-safety checks
//! such as `debug_assert_fd_is_open`): checks that detect UNDEFINED BEHAVIOUR — an
//! unsafe operation called outside its contract — and that in core's own words
//! are "optional, and cannot be relied on for safety" (`library/core/src/ub_checks.rs`).
//! On an execution without undefined behaviour they never fire, so a check that
//! fires is not a defined panic of the Rust program: it is UB made visible, and a
//! firing check aborts (`panic_nounwind`). UB-freedom is not this walk's
//! question. Inside a SAFE std routine, std's own unsafe code upholding its
//! preconditions is std's soundness — a row of std's unit, graded there and not
//! re-required by a caller (docs/design/2026-09-16-trust-core-architecture.md,
//! "Dependency premises are graded, not re-required"); and UB that a caller's own
//! `unsafe` code causes is that caller's own UB row. The census ROOT is therefore
//! restricted to SAFE functions: an `unsafe fn`'s preconditions are the caller's
//! obligation, which this walk must not speak for. The premise is recorded in
//! docs/TCB.md beside the census row. `RuntimeChecks(OverflowChecks)` and
//! `RuntimeChecks(ContractChecks)` are NOT given a value: the checks they guard
//! are defined panics, so their `Assert`s stay sites.
//!
//! The operand also appears as `assume(UbChecks)`: `UnreachablePropagation`
//! leaves it where a `switchInt(UbChecks)`'s checks-OFF arm was `Unreachable`,
//! which is the shape of the `unreachable_unchecked` / `assert_unchecked` family
//! (the checks-ON arm is the check that reports the UB). The walk ends that path.
//! That is the same premise, not a new one: the point is undefined behaviour in
//! the checks-off build, and a program's defined behaviour may not depend on
//! whether UB checks are on (the std text quoted above), so no UB-free execution
//! reaches it in either build.
//!
//! # Why the grant is keyed soundly
//!
//! The compiler-total channel is keyed by the call-site spelling
//! (`func_operand_name`), which renders the callee AND its generic arguments. The
//! census deliberately ignores the call's argument VALUES (the root is walked
//! with every argument unknown): its answer is a function of the resolved
//! instance alone, so every site that shares a key and resolves to the same
//! instance shares the answer. The bridge spends a granted key by NAME on every
//! row of the lowered module, so EVERY lowered body records its own sites — the
//! root and `DefId`-lane members in `collect_expected_absent_callees`, the B-lane
//! and comparator sub-lane members at admission as WITNESSES that can withhold a
//! key but never grant one ([`CensusDischarges::witness_body`]) — and a grant is
//! spent only on sites the census itself judged. Two things could
//! still make one key name two instances, and both withhold the key instead of
//! guessing:
//!
//! * a key spelled with a type or const PARAMETER (the rendered name of a
//!   parameter can coincide with a concrete type's, `direct_call_def_path`
//!   residual 1): such a site is never censused and is recorded DECLINED, which
//!   withholds the key from the whole bundle ([`CensusDischarges`]);
//! * any other rendering collision (residual 7c: two distinct local types
//!   rendered alike inside `args`): every lowered site records its own verdict,
//!   a site the census does not speak for records DECLINED, and one declining
//!   site withholds the key from the whole bundle. A bundle with a `DefId`-lane
//!   member the walk could not read is granted nothing.
//!
//! The crate-wide verdict cache is keyed by the resolved instance's STABLE HASH,
//! never by the rendered call key, so a rendering collision cannot let one
//! instance's answer stand for another's.
//!
//! A value-dependent answer (`load(Ordering::Relaxed)`, `char::from_digit(d, 10)`)
//! needs a per-site channel, which the bridge does not have; such a call is
//! refused with its site named, and the refusal says the census is
//! value-independent.
//!
//! # Measuring it
//!
//! `TRUST_NO_SYSROOT_CENSUS=1` withholds every census grant (strictly subtractive,
//! the `TRUST_NO_BUNDLE_STD` discipline), so a controlled pair runs on one binary
//! and the bundling lane's regression nets can still measure that lane alone.
//! `TRUST_SYSROOT_CENSUS_DEBUG=1` prints each root's verdict and reported sites;
//! `TRUST_SYSROOT_CENSUS_TRACE=1` every summarized instance and undecided branch;
//! `TRUST_SYSROOT_CENSUS_TRACE_MIR=<substring>` the MIR of matching instances.
//!
//! `TRUST_SYSROOT_CENSUS_FAULT_UNRESOLVED=<substring>` is a FAULT SEAM (the
//! `TRUST_SKIP_DEDUP_ORPHAN_FAULT` discipline): a root or walked call whose callee,
//! rendered with its arguments, contains the substring is treated as if
//! `Instance::try_resolve` had not resolved it. No well-typed monomorphic program
//! is known to reach those two arms, so this is how their fixture
//! (`tests/ui/trust/sysroot_census/certify_unresolved_call_in_std_body_refused.rs`)
//! exercises them. It can only turn a call the census would follow into a site, or a
//! root into a refusal: it removes proof, never adds it.
//!
//! # What this does not change
//!
//! Nothing that was refused because its callee can panic becomes accepted: a site
//! anywhere on a normally-reachable path keeps the row. `println!`'s backend
//! (`std::io::_print`) reaches `panic!("failed printing to {label}: {e}")` in
//! `print_to`; it stays refused under `certify`, and the refusal now says so
//! (docs/design/trust-std-design.md, amendment 2026-09-26).

use std::cell::RefCell;
use std::ops::ControlFlow;

use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
use rustc_middle::mir;
use rustc_middle::ty::layout::ValidityRequirement;
use rustc_middle::ty::{
    Instance, InstanceKind, ShimKind, TypeSuperVisitable, TypeVisitable, TypeVisitor,
};

use super::*;

/// The deepest call chain the walk follows from the root.
const MAX_DEPTH: u32 = 24;
/// Distinct `(instance, known arguments)` summaries one root may compute.
const MAX_SUMMARIES: usize = 512;
/// Block visits one root may spend, across every instance it walks.
const MAX_BLOCK_VISITS: usize = 20_000;
/// Distinct constant environments tracked per block before the block is
/// re-walked with nothing known (sound: fewer facts only means more paths).
const MAX_ENVS_PER_BLOCK: usize = 4;
/// Sites kept for the report. The verdict needs one; the report is for people.
const MAX_SITES: usize = 6;
/// Sites the report re-walk collects before it stops; the most direct
/// [`MAX_SITES`] of them are reported (see `census_instance`).
const REPORT_SITE_CAP: usize = 64;
/// The report re-walk RECORDS sites only in the root's own body and in the bodies
/// of the calls it makes directly; a deeper callee is still walked in full (so
/// every guard is pruned exactly as the verdict walk prunes it), and when it can
/// panic the direct call that reaches it is recorded instead.
const REPORT_RECORD_DEPTH: u32 = 1;
/// Distinct types one coroutine search ([`holds_local_coroutine`]) may visit before it
/// answers "holds" (module docs, "A coroutine of this crate is never queried"): the
/// field walk of a polymorphically recursive local ADT never meets a type twice.
const MAX_COROUTINE_SEARCH_TYPES: usize = 256;

/// A value the walk knows on one path.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Known {
    /// A `bool`, integer or `char`, as rustc's own bit pattern for its type.
    Bits(u128),
    /// An enum value, by variant.
    Variant(u32),
}

/// A sorted local -> value map. Sorted so environments compare by value.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
struct Env(Vec<(mir::Local, Known)>);

impl Env {
    fn get(&self, local: mir::Local) -> Option<Known> {
        self.0.binary_search_by_key(&local, |(l, _)| *l).ok().map(|i| self.0[i].1)
    }

    fn set(&mut self, local: mir::Local, value: Option<Known>) {
        match (self.0.binary_search_by_key(&local, |(l, _)| *l), value) {
            (Ok(i), Some(v)) => self.0[i].1 = v,
            (Ok(i), None) => {
                self.0.remove(i);
            }
            (Err(i), Some(v)) => self.0.insert(i, (local, v)),
            (Err(_), None) => {}
        }
    }
}

/// One reachable site the walk could not show non-panicking.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct PanicSite {
    /// Call depth from the root (0 = the root's own body).
    depth: u32,
    /// Report order: a diverging call first, an `Assert` next, a call the walk
    /// could not follow after that, and budget/recursion last.
    rank: u8,
    /// The sysroot function whose body holds the site.
    in_fn: String,
    /// What the site is.
    what: String,
    /// Where, as the source map renders it.
    at: String,
}

impl PanicSite {
    fn render(&self) -> String {
        format!("{} in `{}` ({})", self.what, self.in_fn, self.at)
    }
}

/// The census's answer for one root instance.
#[derive(Clone, Debug)]
pub(super) enum CensusVerdict {
    /// No panic site is reachable from the callee's body.
    Total,
    /// These sites are reachable (at most [`MAX_SITES`], most direct first).
    Reaches(Vec<PanicSite>),
}

/// What the compiler records about one absent sysroot call key, for the
/// `certify` refusal note. Diagnostics only: nothing reads it as a verdict.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct CensusReport {
    /// The census ran and found these sites (empty when it did not run).
    sites: Vec<String>,
    /// Why the census did not run, when it did not.
    not_applicable: Option<&'static str>,
    /// The callee is std's own stdout/stderr print backend
    /// (`def_is_std_print_backend`, authenticated by crate identity).
    print_backend: bool,
}

/// Summary of one walked instance: does it reach a site, and what does it
/// return when it returns normally with a value known on every path.
#[derive(Clone, Copy, Debug)]
struct Summary {
    total: bool,
    ret: Option<Known>,
}

const NOT_TOTAL: Summary = Summary { total: false, ret: None };

struct Census<'tcx> {
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    /// `true` for a REPORT walk, which keeps exploring after the first site (up to
    /// [`REPORT_SITE_CAP`]) and records only sites at depth <=
    /// [`REPORT_RECORD_DEPTH`], so the most direct sites can be named; `false` for
    /// the verdict walk, which stops at the first site. The two walks prune
    /// identically; only what they record differs.
    report: bool,
    /// `TRUST_SYSROOT_CENSUS_TRACE`: print every summarized instance and every
    /// branch the walk could not decide (diagnostics only).
    trace: bool,
    memo: FxHashMap<(Instance<'tcx>, Vec<Option<Known>>), Summary>,
    in_progress: FxHashSet<(Instance<'tcx>, Vec<Option<Known>>)>,
    block_visits: usize,
    exhausted: bool,
    sites: Vec<PanicSite>,
    /// Types already shown to hold no coroutine of this crate
    /// ([`holds_local_coroutine`]). A cache only: a `RefCell` so the `&self`
    /// constant reader can consult it too.
    coroutine_free: RefCell<FxHashSet<Ty<'tcx>>>,
    /// `TRUST_SYSROOT_CENSUS_FAULT_UNRESOLVED`, read once per walk (module docs,
    /// "Measuring it"; [`resolve_unless_faulted`]).
    fault_unresolved: Option<String>,
}

impl<'tcx> Census<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, report: bool) -> Self {
        Census {
            tcx,
            typing_env: ty::TypingEnv::fully_monomorphized(),
            report,
            trace: env_flag_enabled("TRUST_SYSROOT_CENSUS_TRACE"),
            memo: FxHashMap::default(),
            in_progress: FxHashSet::default(),
            block_visits: 0,
            exhausted: false,
            sites: Vec::new(),
            coroutine_free: RefCell::new(FxHashSet::default()),
            fault_unresolved: fault_unresolved_pattern(),
        }
    }

    fn fn_path(&self, def_id: DefId) -> String {
        trust_mir_extract::safe_def_path_str(self.tcx, def_id)
    }

    /// Does `value` hold a coroutine of the crate being compiled? Asked BEFORE any
    /// query about `value`'s types (module docs, "A coroutine of this crate is
    /// never queried").
    fn holds_local_coroutine<T: TypeVisitable<TyCtxt<'tcx>>>(&self, value: T) -> bool {
        holds_local_coroutine(
            self.tcx,
            self.typing_env,
            value,
            &mut *self.coroutine_free.borrow_mut(),
        )
    }

    fn site(&mut self, depth: u32, rank: u8, in_fn: DefId, span: rustc_span::Span, what: String) {
        if self.report && depth > REPORT_RECORD_DEPTH {
            return;
        }
        let site = PanicSite {
            depth,
            rank,
            in_fn: self.fn_path(in_fn),
            what,
            // Outside any macro expansion (`panic!`, `assert!`), so the location is
            // the line in the function that holds the site.
            at: self.tcx.sess.source_map().span_to_diagnostic_string(span.source_callsite()),
        };
        if !self.sites.contains(&site) {
            self.sites.push(site);
        }
    }

    /// Out of budget, or enough sites: stop exploring. The VERDICT walk needs
    /// one site to decide `Reaches` (the report re-walk collects the rest), so it
    /// stops at the first; a report walk collects up to [`REPORT_SITE_CAP`].
    fn saturated(&self) -> bool {
        let enough = if self.report { REPORT_SITE_CAP } else { 1 };
        self.exhausted || self.sites.len() >= enough
    }

    /// Walk a callee of a body at `depth`; in a report walk, a callee whose own
    /// sites lie below the recorded depth is named at the call that reaches it.
    fn visit_callee(
        &mut self,
        callee: Instance<'tcx>,
        args: Vec<Option<Known>>,
        depth: u32,
        owner: DefId,
        span: rustc_span::Span,
    ) -> Summary {
        let summary = self.visit(callee, args, depth + 1);
        if self.report && !summary.total && depth + 1 > REPORT_RECORD_DEPTH {
            self.site(
                depth,
                2,
                owner,
                span,
                format!(
                    "a call to `{}`, which reaches a panic site",
                    self.fn_path(callee.def_id())
                ),
            );
        }
        summary
    }

    /// Instantiate a value of `instance`'s MIR at its arguments. `None` when the
    /// type does not normalize (the caller turns that into a site).
    fn instantiate<T>(&self, instance: Instance<'tcx>, value: T) -> Option<T>
    where
        T: ty::TypeFoldable<TyCtxt<'tcx>>,
    {
        instance
            .try_instantiate_mir_and_normalize_erasing_regions(
                self.tcx,
                self.typing_env,
                ty::EarlyBinder::bind(self.tcx, value),
            )
            .ok()
    }

    /// Walk `instance` with the given argument values known.
    fn visit(&mut self, instance: Instance<'tcx>, args: Vec<Option<Known>>, depth: u32) -> Summary {
        let key = (instance, args);
        if let Some(summary) = self.memo.get(&key) {
            return *summary;
        }
        let owner = instance.def_id();
        if depth > MAX_DEPTH || self.memo.len() >= MAX_SUMMARIES {
            self.exhausted = true;
            self.site(
                depth,
                4,
                owner,
                self.tcx.def_span(owner),
                "the census budget ran out".into(),
            );
            return NOT_TOTAL;
        }
        if self.holds_local_coroutine(instance) {
            // Before `instance_mir`: a shim instantiated at such a type is built from
            // the coroutine's own optimized MIR.
            self.site(
                depth,
                3,
                owner,
                self.tcx.def_span(owner),
                "an instance at a type holding a coroutine of the crate being compiled (or \
                 not shown free of one)"
                    .into(),
            );
            self.memo.insert(key, NOT_TOTAL);
            return NOT_TOTAL;
        }
        if !self.in_progress.insert(key.clone()) {
            // Recursion: a cycle is declined rather than argued coinductively. A
            // node inside the cycle is cached as not-total, which is only ever
            // conservative.
            self.site(depth, 4, owner, self.tcx.def_span(owner), "recursion".into());
            return NOT_TOTAL;
        }
        let summary = self.walk(instance, &key.1, depth);
        if self.trace {
            with_no_trimmed_paths!(eprintln!(
                "[SYSROOT_CENSUS_TRACE] depth={depth} `{instance}` args={:?} -> total={} ret={:?}",
                key.1, summary.total, summary.ret
            ));
        }
        self.in_progress.remove(&key);
        self.memo.insert(key, summary);
        summary
    }

    fn walk(&mut self, instance: Instance<'tcx>, args: &[Option<Known>], depth: u32) -> Summary {
        let tcx = self.tcx;
        let owner = instance.def_id();
        let body = tcx.instance_mir(instance.def);
        // `TRUST_SYSROOT_CENSUS_TRACE_MIR=<substring>`: print the MIR of every walked
        // instance whose rendering contains the substring (diagnostics only).
        if let Some(filter) = std::env::var_os("TRUST_SYSROOT_CENSUS_TRACE_MIR")
            && with_no_trimmed_paths!(format!("{instance}")).contains(&*filter.to_string_lossy())
        {
            let mut out = Vec::new();
            if with_no_trimmed_paths!(
                rustc_middle::mir::pretty::MirWriter::new(tcx).write_mir_fn(body, &mut out)
            )
            .is_ok()
            {
                with_no_trimmed_paths!(eprintln!(
                    "[SYSROOT_CENSUS_TRACE] MIR of `{instance}`:\n{}",
                    String::from_utf8_lossy(&out)
                ));
            }
        }
        let addr_taken = address_taken_locals(body);
        let mut entry = Env::default();
        // A spread (`rust-call`) body re-packs its last argument; bind nothing then.
        if body.spread_arg.is_none() && args.len() == body.arg_count {
            for (i, value) in args.iter().enumerate() {
                let local = mir::Local::from_usize(i + 1);
                if !addr_taken.contains(&local) {
                    entry.set(local, *value);
                }
            }
        }
        let mut total = true;
        let mut returns: Vec<Option<Known>> = Vec::new();
        let mut seen: FxHashMap<mir::BasicBlock, Option<Vec<Env>>> = FxHashMap::default();
        let mut worklist: Vec<(mir::BasicBlock, Env)> = vec![(mir::START_BLOCK, entry)];
        while let Some((bb, env)) = worklist.pop() {
            if !total && self.saturated() {
                break;
            }
            // `None` in `seen` = the block was already walked with nothing known,
            // which covers every later state.
            let slot = seen.entry(bb).or_insert_with(|| Some(Vec::new()));
            let env = match slot {
                None => continue,
                Some(envs) if envs.contains(&env) => continue,
                Some(envs) if envs.len() >= MAX_ENVS_PER_BLOCK => {
                    *slot = None;
                    Env::default()
                }
                Some(envs) => {
                    envs.push(env.clone());
                    env
                }
            };
            self.block_visits += 1;
            if self.block_visits > MAX_BLOCK_VISITS {
                self.exhausted = true;
                self.site(depth, 4, owner, body.span, "the census budget ran out".into());
                return NOT_TOTAL;
            }
            let mut env = env;
            let data = &body.basic_blocks[bb];
            let mut live = true;
            for stmt in &data.statements {
                if !self.apply_statement(instance, body, &addr_taken, &mut env, &stmt.kind) {
                    live = false;
                    break;
                }
            }
            if !live {
                // An `assume` of a value known `false` on this path: MIR defines it
                // as equivalent to `Unreachable`, so the path has no continuation.
                continue;
            }
            let term = data.terminator();
            let span = term.source_info.span;
            use rustc_middle::mir::TerminatorKind as T;
            match &term.kind {
                T::Goto { target, .. } => worklist.push((*target, env)),
                T::SwitchInt { discr, targets } => {
                    match self.operand(instance, body, &env, discr) {
                        Some(Known::Bits(v)) => worklist.push((targets.target_for_value(v), env)),
                        _ => {
                            if self.trace {
                                with_no_trimmed_paths!(eprintln!(
                                    "[SYSROOT_CENSUS_TRACE]   `{instance}` {bb:?}: switch on {discr:?} \
                                 is not known on this path{}",
                                    trace_writers(body, discr)
                                ));
                            }
                            for target in targets.all_targets() {
                                worklist.push((*target, env.clone()));
                            }
                        }
                    }
                }
                T::Return => returns.push(env.get(mir::RETURN_PLACE)),
                T::Unreachable | T::UnwindResume | T::UnwindTerminate(_) => {}
                T::Assert { cond, expected, msg, target, .. } => {
                    let holds = matches!(
                        self.operand(instance, body, &env, cond),
                        Some(Known::Bits(v)) if v == u128::from(*expected)
                    );
                    if !holds {
                        total = false;
                        self.site(
                            depth,
                            1,
                            owner,
                            span,
                            format!("a `{}` check", assert_kind_name(msg)),
                        );
                    }
                    worklist.push((*target, env));
                }
                T::Drop { place, target, .. } => {
                    let Some(ty) = self.instantiate(instance, place.ty(&body.local_decls, tcx).ty)
                    else {
                        total = false;
                        self.site(
                            depth,
                            3,
                            owner,
                            span,
                            "a drop whose type does not normalize".into(),
                        );
                        continue;
                    };
                    if self.holds_local_coroutine(ty) {
                        // Before `needs_drop` / `resolve_drop_glue`, which read such a
                        // coroutine's optimized MIR.
                        total = false;
                        let what = with_no_trimmed_paths!(format!(
                            "the drop of `{ty}`, which holds (or is not shown free of) a \
                             coroutine of the crate being compiled"
                        ));
                        self.site(depth, 3, owner, span, what);
                        env.set(place.local, None);
                        worklist.push((*target, env));
                        continue;
                    }
                    // RIGID-ALIAS-CENSUS-1: renormalize rigid aliases before the
                    // old solver sees this type (see census_needs_drop's kin in
                    // trust-mir-extract's concurrency_effects).
                    let ty = ty::set_aliases_to_non_rigid(tcx, ty).skip_norm_wip();
                    if ty.needs_drop(tcx, self.typing_env) {
                        let glue = Instance::resolve_drop_glue(tcx, ty);
                        if !self.visit(glue, vec![None], depth + 1).total {
                            total = false;
                            // No trimmed paths: this runs in ordinary compilations, and a
                            // trimmed-path render arms `must_produce_diag` (`probe_label`).
                            let what = with_no_trimmed_paths!(format!("the drop of `{ty}`"));
                            self.site(depth, 2, owner, span, what);
                        }
                    }
                    // The glue is handed `&mut place`, so it may write anywhere in the
                    // dropped place — a projected place included: a field of an enum
                    // can hold that enum's niche, i.e. its discriminant. Forget the
                    // whole base local, never only a whole-local drop.
                    env.set(place.local, None);
                    worklist.push((*target, env));
                }
                T::Call { func, args: call_args, destination, target, .. } => match target {
                    None => {
                        // Diverging: the continuation never runs. Charged whatever
                        // the callee is (`panic_fmt`, `unwrap_failed`,
                        // `capacity_overflow`, `handle_alloc_error`, `abort`,
                        // `exit`) and never walked — the site IS the call.
                        total = false;
                        let name = self.callee_name(body, func);
                        self.site(
                            depth,
                            0,
                            owner,
                            span,
                            format!("a call to `{name}`, which does not return"),
                        );
                    }
                    Some(target) => {
                        let operands: Vec<&mir::Operand<'tcx>> =
                            call_args.iter().map(|arg| &arg.node).collect();
                        let callee = self.call(instance, body, &env, func, &operands, depth, span);
                        if !callee.total {
                            total = false;
                        }
                        // A `Move` operand may be passed in place and written by the
                        // callee (MIR's `Move` semantics), so its local is unknown
                        // after the call.
                        for arg in call_args.iter() {
                            if let mir::Operand::Move(place) = &arg.node {
                                env.set(place.local, None);
                            }
                        }
                        if destination.projection.is_empty()
                            && !addr_taken.contains(&destination.local)
                        {
                            env.set(destination.local, callee.ret);
                        } else {
                            env.set(destination.local, None);
                        }
                        worklist.push((*target, env));
                    }
                },
                T::TailCall { func, args: call_args, .. } => {
                    let operands: Vec<&mir::Operand<'tcx>> =
                        call_args.iter().map(|arg| &arg.node).collect();
                    let callee = self.call(instance, body, &env, func, &operands, depth, span);
                    if !callee.total {
                        total = false;
                    }
                    returns.push(callee.ret);
                }
                T::InlineAsm { .. } => {
                    total = false;
                    self.site(depth, 3, owner, span, "inline assembly".into());
                }
                T::Yield { .. }
                | T::CoroutineDrop
                | T::FalseEdge { .. }
                | T::FalseUnwind { .. } => {
                    total = false;
                    self.site(depth, 3, owner, span, "a coroutine or unlowered terminator".into());
                }
            }
        }
        if !total {
            return NOT_TOTAL;
        }
        let ret = match returns.split_first() {
            Some((first, rest)) if first.is_some() && rest.iter().all(|r| r == first) => *first,
            _ => None,
        };
        Summary { total: true, ret }
    }

    fn callee_name(&self, body: &mir::Body<'tcx>, func: &mir::Operand<'tcx>) -> String {
        match *func.ty(&body.local_decls, self.tcx).kind() {
            ty::FnDef(def_id, _) => self.fn_path(def_id),
            _ => "a function pointer".into(),
        }
    }

    /// Summarize one call that returns.
    fn call(
        &mut self,
        caller: Instance<'tcx>,
        body: &mir::Body<'tcx>,
        env: &Env,
        func: &mir::Operand<'tcx>,
        args: &[&mir::Operand<'tcx>],
        depth: u32,
        span: rustc_span::Span,
    ) -> Summary {
        let tcx = self.tcx;
        let owner = caller.def_id();
        // The callee is read from the operand's TYPE, not its spelling: a value of a
        // `FnDef` type can only be that one function item, whether the operand is a
        // constant or a local holding the zero-sized item (the shape
        // `remap_mir_for_const_eval_select` leaves behind). Anything else — a real
        // function pointer — is a site.
        let Some(fn_ty) = self.instantiate(caller, func.ty(&body.local_decls, tcx)) else {
            self.site(depth, 3, owner, span, "a call whose callee type does not normalize".into());
            return NOT_TOTAL;
        };
        let ty::FnDef(def_id, generic_args) = *fn_ty.kind() else {
            self.site(depth, 3, owner, span, "a call through a function pointer".into());
            return NOT_TOTAL;
        };
        // A tuple-struct or enum-variant CONSTRUCTOR has no body: it moves its
        // operands into a value and cannot panic, whoever owns the type.
        if matches!(tcx.def_kind(def_id), DefKind::Ctor(..)) {
            return Summary { total: true, ret: None };
        }
        if self.holds_local_coroutine(generic_args) {
            // Before `try_resolve`, which reads such a coroutine's optimized MIR for
            // its drop glue (and for its `Future`/`Iterator` instance).
            self.site(
                depth,
                3,
                owner,
                span,
                format!(
                    "a call to `{}` at a type holding a coroutine of the crate being compiled \
                     (or not shown free of one)",
                    self.fn_path(def_id)
                ),
            );
            return NOT_TOTAL;
        }
        let known_args: Vec<Option<Known>> =
            args.iter().map(|arg| self.operand(caller, body, env, arg)).collect();
        let Some(callee) = resolve_unless_faulted(
            tcx,
            self.typing_env,
            self.fault_unresolved.as_deref(),
            def_id,
            generic_args.skip_binder(),
        ) else {
            self.site(
                depth,
                3,
                owner,
                span,
                format!("an unresolved call to `{}`", self.fn_path(def_id)),
            );
            return NOT_TOTAL;
        };
        match callee.def {
            InstanceKind::Intrinsic(intrinsic_def) => {
                let summary = self.intrinsic(intrinsic_def, callee.args, owner, depth, span);
                // An intrinsic with a FALLBACK body runs that body wherever the
                // backend does not implement it natively: walk it too.
                let has_fallback =
                    tcx.intrinsic(intrinsic_def).is_some_and(|i| !i.must_be_overridden);
                if summary.total && has_fallback && tcx.is_mir_available(intrinsic_def) {
                    let fallback = Instance::new_raw(intrinsic_def, callee.args);
                    return Summary {
                        total: self.visit_callee(fallback, known_args, depth, owner, span).total,
                        ret: None,
                    };
                }
                summary
            }
            InstanceKind::Virtual(..) => {
                self.site(
                    depth,
                    3,
                    owner,
                    span,
                    format!("a dynamic-dispatch call to `{}`", self.fn_path(def_id)),
                );
                NOT_TOTAL
            }
            InstanceKind::LlvmIntrinsic(..) => {
                self.site(
                    depth,
                    3,
                    owner,
                    span,
                    format!("an LLVM-intrinsic call to `{}`", self.fn_path(def_id)),
                );
                NOT_TOTAL
            }
            InstanceKind::Item(item) => {
                if tcx.is_foreign_item(item) {
                    return self.foreign(item, owner, depth, span);
                }
                if !trust_mir_extract::def_is_in_sysroot_resident_crate(tcx, item) {
                    self.site(
                        depth,
                        2,
                        owner,
                        span,
                        format!("a call into non-sysroot code `{}`", self.fn_path(item)),
                    );
                    return NOT_TOTAL;
                }
                if tcx.codegen_fn_attrs(item).contains_extern_indicator() {
                    // `#[no_mangle]`, `#[export_name]`, `#[linkage]`, an externally
                    // implementable item or a std-internal symbol: the code a link
                    // binds under that symbol need not be this MIR.
                    self.site(
                        depth,
                        3,
                        owner,
                        span,
                        format!("a call to the exported symbol `{}`", self.fn_path(item)),
                    );
                    return NOT_TOTAL;
                }
                if !tcx.is_mir_available(item) {
                    self.site(
                        depth,
                        3,
                        owner,
                        span,
                        format!("a call to `{}`, whose MIR is not available", self.fn_path(item)),
                    );
                    return NOT_TOTAL;
                }
                self.visit_callee(callee, known_args, depth, owner, span)
            }
            InstanceKind::Shim(
                ShimKind::DropGlue(..)
                | ShimKind::FnPtr(..)
                | ShimKind::ClosureOnce { .. }
                | ShimKind::Clone(..)
                | ShimKind::Reify(..)
                | ShimKind::FnPtrAsPtr(..)
                | ShimKind::FnPtrFromPtr(..)
                | ShimKind::VTable(..)
                | ShimKind::ThreadLocal(..),
            ) => self.visit_callee(callee, known_args, depth, owner, span),
            InstanceKind::Shim(_) => {
                self.site(
                    depth,
                    3,
                    owner,
                    span,
                    format!("a call to a compiler shim for `{}`", self.fn_path(def_id)),
                );
                NOT_TOTAL
            }
        }
    }

    fn intrinsic(
        &mut self,
        intrinsic_def: DefId,
        args: ty::GenericArgs<'tcx>,
        owner: DefId,
        depth: u32,
        span: rustc_span::Span,
    ) -> Summary {
        let tcx = self.tcx;
        let Some(intrinsic) = tcx.intrinsic(intrinsic_def) else {
            self.site(depth, 3, owner, span, "an unrecognized intrinsic".into());
            return NOT_TOTAL;
        };
        // The three validity asserts PANIC when their type is invalid for the
        // requested initialization; rustc decides that at the instantiated type
        // (the same query `InstSimplify` folds them with).
        if let Some(requirement) = ValidityRequirement::from_intrinsic(intrinsic.name) {
            let valid = args.types().next().is_some_and(|ty| {
                matches!(
                    tcx.check_validity_requirement((
                        requirement,
                        self.typing_env.as_query_input(ty)
                    )),
                    Ok(true)
                )
            });
            if !valid {
                self.site(
                    depth,
                    0,
                    owner,
                    span,
                    format!("`{}`, which panics for this type", intrinsic.name),
                );
                return NOT_TOTAL;
            }
            return Summary { total: true, ret: None };
        }
        // An intrinsic that may unwind, or that is handed a callable (and so can
        // run code the walk does not see — `catch_unwind` runs its `try_fn`,
        // `const_eval_select` its runtime function), is not followed.
        let is_callable = |ty: Ty<'tcx>| {
            matches!(ty.kind(), ty::FnDef(..) | ty::FnPtr(..) | ty::Closure(..) | ty::Dynamic(..))
        };
        let signature = tcx.fn_sig(intrinsic_def).instantiate(tcx, args).skip_binder();
        let callable_arg =
            args.types().any(is_callable) || signature.inputs().iter().any(|ty| is_callable(*ty));
        if callable_arg
            || !tcx.codegen_fn_attrs(intrinsic_def).flags.contains(CodegenFnAttrFlags::NEVER_UNWIND)
        {
            self.site(
                depth,
                3,
                owner,
                span,
                format!("the intrinsic `{}`, which may unwind or run a callable", intrinsic.name),
            );
            return NOT_TOTAL;
        }
        Summary { total: true, ret: None }
    }

    fn foreign(
        &mut self,
        item: DefId,
        owner: DefId,
        depth: u32,
        span: rustc_span::Span,
    ) -> Summary {
        let tcx = self.tcx;
        let flags = tcx.codegen_fn_attrs(item).flags;
        if flags.intersects(
            CodegenFnAttrFlags::ALLOCATOR
                | CodegenFnAttrFlags::DEALLOCATOR
                | CodegenFnAttrFlags::REALLOCATOR
                | CodegenFnAttrFlags::ALLOCATOR_ZEROED,
        ) {
            self.site(
                depth,
                2,
                owner,
                span,
                format!(
                    "the global allocator (`{}`), which a final link may bind to a user \
                     `#[global_allocator]`",
                    self.fn_path(item)
                ),
            );
            return NOT_TOTAL;
        }
        let abi = tcx.fn_sig(item).skip_binder().abi();
        if super::extern_abi_is_non_unwinding(abi) {
            return Summary { total: true, ret: None };
        }
        self.site(
            depth,
            3,
            owner,
            span,
            format!("the foreign `{abi:?}` symbol `{}`, which may unwind", self.fn_path(item)),
        );
        NOT_TOTAL
    }

    /// Apply one statement to the path's environment. Returns `false` when the
    /// statement ends the path: `assume(c)` with `c` known `false` here, which MIR
    /// defines as equivalent to `TerminatorKind::Unreachable` ("If the argument is
    /// `false`, this operation is equivalent to `TerminatorKind::Unreachable`",
    /// `NonDivergingIntrinsic::Assume`). The optimizer emits exactly that shape for
    /// a UB-check guard whose other arm is `unreachable()` — `assume(UbChecks);
    /// precondition_check()` — so this is how the premise reaches such a guard.
    fn apply_statement(
        &mut self,
        instance: Instance<'tcx>,
        body: &mir::Body<'tcx>,
        addr_taken: &FxHashSet<mir::Local>,
        env: &mut Env,
        kind: &mir::StatementKind<'tcx>,
    ) -> bool {
        use rustc_middle::mir::StatementKind as S;
        if let S::Intrinsic(intrinsic) = kind
            && let mir::NonDivergingIntrinsic::Assume(operand) = &**intrinsic
        {
            match self.operand(instance, body, env, operand) {
                Some(Known::Bits(0)) => return false,
                Some(_) => {}
                // After `assume(x)` the path continues only where `x` holds.
                None => {
                    if let Some(place) = operand.place()
                        && place.projection.is_empty()
                        && !addr_taken.contains(&place.local)
                        && operand.ty(&body.local_decls, self.tcx).is_bool()
                    {
                        env.set(place.local, Some(Known::Bits(1)));
                    }
                }
            }
            return true;
        }
        match kind {
            S::Assign(assign) => {
                let (place, rvalue) = &**assign;
                if place.projection.is_empty() && !addr_taken.contains(&place.local) {
                    let value = self.rvalue(instance, body, env, rvalue);
                    env.set(place.local, value);
                } else {
                    env.set(place.local, None);
                }
            }
            S::StorageLive(local) | S::StorageDead(local) => env.set(*local, None),
            S::SetDiscriminant { place, .. } => env.set(place.local, None),
            // No statement below writes a tracked local: `Intrinsic`
            // (`copy_nonoverlapping`, `assume`) writes only through a pointer, and a
            // pointer to a local makes that local address-taken, hence untracked.
            S::FakeRead(..)
            | S::PlaceMention(..)
            | S::AscribeUserType(..)
            | S::Coverage(..)
            | S::Intrinsic(..)
            | S::ConstEvalCounter
            | S::Nop
            | S::BackwardIncompatibleDropHint { .. } => {}
        }
        true
    }

    fn rvalue(
        &self,
        instance: Instance<'tcx>,
        body: &mir::Body<'tcx>,
        env: &Env,
        rvalue: &mir::Rvalue<'tcx>,
    ) -> Option<Known> {
        use rustc_middle::mir::{BinOp, Rvalue, UnOp};
        match rvalue {
            Rvalue::Use(operand, _) => self.operand(instance, body, env, operand),
            Rvalue::UnaryOp(UnOp::Not, operand) => {
                let ty = operand.ty(&body.local_decls, self.tcx);
                match self.operand(instance, body, env, operand)? {
                    Known::Bits(v) if ty.is_bool() => Some(Known::Bits(u128::from(v == 0))),
                    _ => None,
                }
            }
            Rvalue::BinaryOp(op, operands) => {
                let (lhs, rhs) = &**operands;
                let ty = lhs.ty(&body.local_decls, self.tcx);
                let (Known::Bits(a), Known::Bits(b)) = (
                    self.operand(instance, body, env, lhs)?,
                    self.operand(instance, body, env, rhs)?,
                ) else {
                    return None;
                };
                let unsigned = ty.is_bool() || ty.is_char() || matches!(ty.kind(), ty::Uint(_));
                let bool_ty = ty.is_bool();
                let out = match op {
                    BinOp::Eq => a == b,
                    BinOp::Ne => a != b,
                    BinOp::Lt if unsigned => a < b,
                    BinOp::Le if unsigned => a <= b,
                    BinOp::Gt if unsigned => a > b,
                    BinOp::Ge if unsigned => a >= b,
                    BinOp::BitAnd if bool_ty => return Some(Known::Bits(a & b)),
                    BinOp::BitOr if bool_ty => return Some(Known::Bits(a | b)),
                    BinOp::BitXor if bool_ty => return Some(Known::Bits(a ^ b)),
                    _ => return None,
                };
                Some(Known::Bits(u128::from(out)))
            }
            // A variant literal of an enum: its variant is known, its fields are
            // not needed (only `Discriminant` reads it).
            Rvalue::Aggregate(kind, _) => match &**kind {
                mir::AggregateKind::Adt(def_id, variant, ..)
                    if self.tcx.adt_def(*def_id).is_enum() =>
                {
                    Some(Known::Variant(variant.as_u32()))
                }
                _ => None,
            },
            Rvalue::Discriminant(place) if place.projection.is_empty() => {
                let Known::Variant(v) = env.get(place.local)? else { return None };
                let ty = self.instantiate(instance, place.ty(&body.local_decls, self.tcx).ty)?;
                let ty::Adt(adt, _) = ty.kind() else { return None };
                if !adt.is_enum() {
                    return None;
                }
                let variant = rustc_abi::VariantIdx::from_u32(v);
                Some(Known::Bits(adt.discriminant_for_variant(self.tcx, variant).val))
            }
            _ => None,
        }
    }

    fn operand(
        &self,
        instance: Instance<'tcx>,
        body: &mir::Body<'tcx>,
        env: &Env,
        operand: &mir::Operand<'tcx>,
    ) -> Option<Known> {
        let _ = body;
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                if place.projection.is_empty() { env.get(place.local) } else { None }
            }
            // THE PREMISE (module docs): a UB check never fires on an execution
            // without undefined behaviour.
            mir::Operand::RuntimeChecks(mir::RuntimeChecks::UbChecks) => Some(Known::Bits(0)),
            mir::Operand::RuntimeChecks(_) => None,
            mir::Operand::Constant(constant) => {
                let value = self.instantiate(instance, constant.const_)?;
                // Before evaluating: a layout-dependent constant (`size_of::<T>()`,
                // `T::IS_ZST`) at such a type reads the coroutine's optimized MIR.
                // Unknown is always sound here; it only explores more paths.
                if self.holds_local_coroutine(value) {
                    return None;
                }
                let ty = value.ty();
                if ty.is_bool() || ty.is_char() || ty.is_integral() {
                    return value.try_eval_bits(self.tcx, self.typing_env).map(Known::Bits);
                }
                if let ty::Adt(adt, _) = ty.kind()
                    && adt.is_enum()
                {
                    let evaluated = value.eval(self.tcx, self.typing_env, constant.span).ok()?;
                    let destructured =
                        self.tcx.try_destructure_mir_constant_for_user_output(evaluated, ty)?;
                    return destructured.variant.map(|v| Known::Variant(v.as_u32()));
                }
                None
            }
        }
    }
}

/// `TRUST_SYSROOT_CENSUS_TRACE` only: every statement or call in `body` that writes
/// the local an undecided `SwitchInt` reads, so a trace says WHY it was undecided.
fn trace_writers<'tcx>(body: &mir::Body<'tcx>, discr: &mir::Operand<'tcx>) -> String {
    let Some(place) = discr.place() else { return String::new() };
    let mut out = String::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        for stmt in &data.statements {
            if let mir::StatementKind::Assign(assign) = &stmt.kind
                && assign.0.local == place.local
            {
                out.push_str(&format!("; {bb:?}: {:?} = {:?}", assign.0, assign.1));
            }
        }
        if let mir::TerminatorKind::Call { func, destination, .. } = &data.terminator().kind
            && destination.local == place.local
        {
            out.push_str(&format!("; {bb:?}: {destination:?} = call {func:?}"));
        }
    }
    out
}

/// Locals whose address is taken anywhere in `body`: a write through the pointer
/// is invisible to the walk, so these are never tracked.
fn address_taken_locals(body: &mir::Body<'_>) -> FxHashSet<mir::Local> {
    use rustc_middle::mir::Rvalue;
    let mut out = FxHashSet::default();
    for data in body.basic_blocks.iter() {
        for stmt in &data.statements {
            if let mir::StatementKind::Assign(assign) = &stmt.kind {
                match &assign.1 {
                    Rvalue::Ref(_, _, place)
                    | Rvalue::RawPtr(_, place)
                    | Rvalue::Reborrow(_, _, place) => {
                        out.insert(place.local);
                    }
                    _ => {}
                }
            }
        }
    }
    out
}

fn assert_kind_name(msg: &mir::AssertMessage<'_>) -> &'static str {
    use rustc_middle::mir::AssertKind as A;
    match msg {
        A::BoundsCheck { .. } => "bounds",
        A::Overflow(..) | A::OverflowNeg(..) => "arithmetic overflow",
        A::DivisionByZero(..) => "division by zero",
        A::RemainderByZero(..) => "remainder by zero",
        A::MisalignedPointerDereference { .. } => "pointer alignment",
        _ => "runtime",
    }
}

/// Does `value` hold a coroutine, coroutine closure or coroutine witness DEFINED IN
/// THIS CRATE — through its generic arguments, after normalization (a revealed
/// `impl Future` counts), or through the declared fields of this crate's own ADTs
/// (a field typed with a type-alias `impl Trait` counts)? An alias that does not
/// normalize counts as holding one (fail closed). Decided without asking rustc
/// anything about a coroutine: only `type_of`, `adt_def` and normalization, which
/// never read an `optimized_mir`. `known_free` caches types already shown free.
/// Trust (2026-10-10): also asked by the call-reach walk's entry
/// (`sysroot_drop_reach::call_site_reach`) before its first query about a call.
pub(super) fn holds_local_coroutine<'tcx, T: TypeVisitable<TyCtxt<'tcx>>>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    value: T,
    known_free: &mut FxHashSet<Ty<'tcx>>,
) -> bool {
    let mut finder =
        LocalCoroutineFinder { tcx, typing_env, known_free, visited: FxHashSet::default() };
    let holds = value.visit_with(&mut finder).is_break();
    if !holds {
        // The whole traversal finished without finding one, so every type it
        // visited is free: a type skipped because it was already being visited
        // was searched in full by the visit that entered it.
        let LocalCoroutineFinder { known_free, visited, .. } = finder;
        // A set union: the result does not depend on iteration order.
        #[allow(rustc::potential_query_instability)]
        known_free.extend(visited);
    }
    holds
}

struct LocalCoroutineFinder<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    known_free: &'a mut FxHashSet<Ty<'tcx>>,
    /// Types entered by this traversal (also what stops a recursive ADT).
    visited: FxHashSet<Ty<'tcx>>,
}

impl<'a, 'tcx> LocalCoroutineFinder<'a, 'tcx> {
    /// `ty` with its aliases normalized, or `None` when that fails. A type with
    /// aliases and vars bound OUTSIDE it (met inside a `for<'a>` binder) is never
    /// handed to the normalizer: `None`, which the caller treats as holding.
    fn normalized(&self, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
        if !ty.has_aliases() {
            return Some(ty);
        }
        if ty.has_escaping_bound_vars() {
            return None;
        }
        self.tcx.try_normalize_erasing_regions(self.typing_env, ty::Unnormalized::new_wip(ty)).ok()
    }
}

impl<'a, 'tcx> TypeVisitor<TyCtxt<'tcx>> for LocalCoroutineFinder<'a, 'tcx> {
    type Result = ControlFlow<()>;

    fn visit_ty(&mut self, ty: Ty<'tcx>) -> ControlFlow<()> {
        if self.known_free.contains(&ty) || !self.visited.insert(ty) {
            return ControlFlow::Continue(());
        }
        if self.visited.len() > MAX_COROUTINE_SEARCH_TYPES {
            // A search this walk cannot finish answers "holds": a decline, never a
            // grant (module docs). Before any `FieldDef::ty` of an ever-growing type.
            return ControlFlow::Break(());
        }
        match *ty.kind() {
            ty::Coroutine(def_id, _)
            | ty::CoroutineWitness(def_id, _)
            | ty::CoroutineClosure(def_id, _)
                if def_id.is_local() =>
            {
                return ControlFlow::Break(());
            }
            // An opaque type (`impl Future`) is revealed; anything that stays an
            // alias holds one as far as this check knows.
            ty::Alias(..) => match self.normalized(ty) {
                Some(normalized) if normalized != ty => normalized.visit_with(self)?,
                _ => return ControlFlow::Break(()),
            },
            // This crate's own ADT can name a coroutine in a field's declared type
            // (a type-alias `impl Trait`), not only through `args`. Another crate's
            // ADT cannot name one of this crate's coroutines except through `args`.
            ty::Adt(adt, args) if adt.did().is_local() => {
                for field in adt.all_fields() {
                    match self.normalized(field.ty(self.tcx, args).skip_normalization()) {
                        Some(field_ty) => field_ty.visit_with(self)?,
                        None => return ControlFlow::Break(()),
                    }
                }
            }
            _ => {}
        }
        ty.super_visit_with(self)
    }
}

/// Why a call is not censused at all, or `None` when it is a census root.
fn not_applicable<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee: DefId,
    generic_args: ty::GenericArgs<'tcx>,
) -> Option<&'static str> {
    if !matches!(tcx.def_kind(callee), DefKind::Fn | DefKind::AssocFn) {
        return Some("not a function item");
    }
    if tcx.intrinsic(callee).is_some() {
        return Some("a compiler intrinsic");
    }
    if generic_args.has_non_region_param() {
        return Some("instantiated at a type or const parameter of the calling body");
    }
    if !tcx.fn_sig(callee).skip_binder().safety().is_safe() {
        return Some("an `unsafe fn`, whose preconditions are the caller's obligation");
    }
    None
}

/// The census's verdict for one call, and the report for its refusal note.
struct CallCensus {
    total: bool,
    report: Option<CensusReport>,
}

/// Census the call `callee::<generic_args>` from a verified body, or `None` when
/// the callee is not a `core`/`alloc`/`std` function (the census speaks only for
/// the authenticated sysroot). Verdicts are cached crate-wide by the resolved
/// instance's stable hash (module docs, "Why the grant is keyed soundly").
fn census_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee: DefId,
    generic_args: ty::GenericArgs<'tcx>,
) -> Option<CallCensus> {
    if !trust_mir_extract::def_is_in_real_sysroot_crate(tcx, callee) {
        return None;
    }
    let print_backend = super::def_is_std_print_backend(tcx, callee);
    let refused = |reason: &'static str| CallCensus {
        total: false,
        report: Some(CensusReport {
            sites: Vec::new(),
            not_applicable: Some(reason),
            print_backend,
        }),
    };
    if let Some(reason) = not_applicable(tcx, callee, generic_args) {
        return Some(refused(reason));
    }
    let generic_args = tcx.erase_and_anonymize_regions(generic_args);
    let typing_env = ty::TypingEnv::fully_monomorphized();
    // Before `try_resolve`, the first query about the root's arguments (module docs,
    // "A coroutine of this crate is never queried").
    if holds_local_coroutine(tcx, typing_env, generic_args, &mut FxHashSet::default()) {
        return Some(refused(
            "instantiated at a type that holds (or is not shown free of) a coroutine (an \
             `async` body) of the crate \
             being compiled: rustc derives that type's drop glue and layout from the \
             coroutine's own optimized MIR, which may still be under construction in this \
             compilation (asking would be a query cycle, rustc's E0391)",
        ));
    }
    let Some(instance) = resolve_unless_faulted(
        tcx,
        typing_env,
        fault_unresolved_pattern().as_deref(),
        callee,
        generic_args,
    ) else {
        return Some(refused("a call whose instance does not resolve"));
    };
    let walkable = match instance.def {
        InstanceKind::Item(item) => {
            trust_mir_extract::def_is_in_sysroot_resident_crate(tcx, item)
                && !tcx.is_foreign_item(item)
                && !tcx.codegen_fn_attrs(item).contains_extern_indicator()
                && tcx.is_mir_available(item)
        }
        InstanceKind::Shim(..) => true,
        InstanceKind::Intrinsic(..)
        | InstanceKind::LlvmIntrinsic(..)
        | InstanceKind::Virtual(..) => false,
    };
    if !walkable {
        return Some(refused(
            "a call that does not resolve to a sysroot body with MIR (a user impl, a dynamic \
             call, an exported symbol or a foreign import)",
        ));
    }
    let cache_key = instance_cache_key(tcx, instance);
    if let Some(cached) = with_crate_verification_state(tcx.sess, |state| {
        state.sysroot_census_verdicts.get(&cache_key).cloned()
    }) {
        return Some(CallCensus { total: cached.0, report: cached.1 });
    }
    let verdict = census_instance(tcx, instance, callee);
    let (total, report) = match verdict {
        CensusVerdict::Total => (true, None),
        CensusVerdict::Reaches(sites) => (
            false,
            Some(CensusReport {
                sites: sites.iter().map(PanicSite::render).collect(),
                not_applicable: None,
                print_backend,
            }),
        ),
    };
    with_crate_verification_state(tcx.sess, |state| {
        state.sysroot_census_verdicts.insert(cache_key, (total, report.clone()));
    });
    Some(CallCensus { total, report })
}

/// The fault seam's pattern (module docs, "Measuring it"), when one is set.
fn fault_unresolved_pattern() -> Option<String> {
    std::env::var("TRUST_SYSROOT_CENSUS_FAULT_UNRESOLVED")
        .ok()
        .filter(|pattern| !pattern.is_empty())
}

/// `Instance::try_resolve` at the census's typing environment, `None` when it does
/// not resolve the call — or when the fault seam names the callee (`fault`, module
/// docs, "Measuring it"), which only ever turns a call into one the census does not
/// follow.
fn resolve_unless_faulted<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    fault: Option<&str>,
    def_id: DefId,
    generic_args: ty::GenericArgs<'tcx>,
) -> Option<Instance<'tcx>> {
    if let Some(pattern) = fault
        && trust_mir_extract::safe_def_path_str_with_args(tcx, def_id, generic_args)
            .contains(pattern)
    {
        return None;
    }
    ty::Instance::try_resolve(tcx, typing_env, def_id, generic_args).ok().flatten()
}

/// The crate-wide cache key of a resolved root instance: its stable hash
/// (`DefPathHash` of the item plus its generic arguments, the identity rustc's own
/// symbol hashes and incremental keys rest on), never a rendered path.
/// Trust (2026-10-10): also the call-reach walk's memo key
/// (`sysroot_drop_reach::CALL_REACH_MEMO`).
pub(super) fn instance_cache_key<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>) -> String {
    use rustc_data_structures::stable_hash::StableHash;
    let fingerprint: Fingerprint = tcx.with_stable_hashing_context(|mut hcx| {
        let mut hasher = StableHasher::new();
        instance.stable_hash(&mut hcx, &mut hasher);
        hasher.finish()
    });
    format!("{fingerprint}")
}

/// Walk one resolved root instance.
fn census_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    callee: DefId,
) -> CensusVerdict {
    let arity = tcx.fn_sig(callee).skip_binder().inputs().skip_binder().len();
    let mut census = Census::new(tcx, false);
    let root_ok = census.visit(instance, vec![None; arity], 0).total;
    let debug = env_flag_enabled("TRUST_SYSROOT_CENSUS_DEBUG");
    if debug {
        with_no_trimmed_paths!(eprintln!(
            "[SYSROOT_CENSUS] instance=`{instance}` total={root_ok} summaries={} block_visits={} \
             first_site={:?}",
            census.memo.len(),
            census.block_visits,
            census.sites.iter().map(PanicSite::render).collect::<Vec<_>>(),
        ));
    }
    if root_ok {
        return CensusVerdict::Total;
    }
    // Report the MOST DIRECT sites: the verdict walk is depth-first and stops at
    // its first site, which may be deep inside the first callee it followed. The
    // report re-walk is the same walk (same pruning, so every site it names is
    // reachable under the census's own reading) that keeps going, records only the
    // root's and its direct callees' own sites plus the direct calls into deeper
    // panicking code (`REPORT_RECORD_DEPTH`), and the shallowest are reported.
    let mut report = Census::new(tcx, true);
    report.visit(instance, vec![None; arity], 0);
    let mut sites = if report.sites.is_empty() { census.sites } else { report.sites };
    sites.sort_by(|a, b| (a.depth, a.rank).cmp(&(b.depth, b.rank)));
    sites.truncate(MAX_SITES);
    if debug {
        for site in &sites {
            eprintln!("[SYSROOT_CENSUS]   report depth={} {}", site.depth, site.render());
        }
    }
    CensusVerdict::Reaches(sites)
}

/// Census one call site of a walked body, record its refusal report under the
/// call key (diagnostics only), and return the verdict — `None` for a callee the
/// census does not speak for.
fn census_call_site<'tcx>(
    tcx: TyCtxt<'tcx>,
    call_key: &str,
    callee: DefId,
    generic_args: ty::GenericArgs<'tcx>,
) -> Option<bool> {
    // A/B measurement switch, DEFAULT ON, on the `TRUST_NO_BUNDLE_STD` discipline:
    // `TRUST_NO_SYSROOT_CENSUS=1` withholds every census grant, so each call it
    // would have discharged falls back to the fail-closed absent-callee arm where
    // it sat before the census existed. No setting admits anything; the only
    // direction available is less proof. It exists so a controlled pair can be
    // run on one binary, and so the bundling lane's regression nets
    // (`native_bundle_std_*`) can still measure that lane in isolation.
    if env_flag_enabled("TRUST_NO_SYSROOT_CENSUS") {
        return trust_mir_extract::def_is_in_real_sysroot_crate(tcx, callee).then_some(false);
    }
    let CallCensus { total, report } = census_call(tcx, callee, generic_args)?;
    if let Some(report) = report {
        with_crate_verification_state(tcx.sess, |state| {
            // First report wins; the note is a diagnostic and never a verdict.
            state.sysroot_census_reports.entry(call_key.to_owned()).or_insert(report);
        });
    }
    Some(total)
}

/// The per-bundle census ledger: a key is granted to the compiler-total channel
/// only when a WALKED site earned it (censused `Total`) and no recorded site of the
/// key declined; one declining site withholds it from the whole bundle (the
/// `GenericDispatchDischarges` discipline).
///
/// COVERAGE is what makes that rule sound, because the bridge spends a granted
/// key by NAME on every row of the lowered module. So every body the module
/// lowers records its sites here, in one of two roles:
///
/// * WALKED — the root and the `DefId`-lane members, through
///   `collect_expected_absent_callees` ([`Self::record`]): a total site is a
///   candidate grant, anything else withholds the key.
/// * WITNESS — the B-lane's instantiated foreign members and the comparator
///   sub-lane's bodies, at admission (`native_trust_ir_verifiable_function_closure`,
///   [`Self::witness_body`]), where their instantiated MIR exists: a site that is
///   not censused total withholds the key; a total one grants nothing.
///
/// Without the witness half, a B-lane member's call whose key renders like a
/// walked site's but resolves to another instance (`direct_call_def_path`
/// residual 7c: two distinct local types rendered alike inside `args`) would ride
/// a grant it never earned. A witness grants nothing because a key that occurs
/// ONLY inside B-lane members is left where it sat before the census: its call
/// keeps the absent-callee row, and the bundle's poison loop evicts that member
/// as before (measured: granting such keys retained members whose monomorphized
/// `Drop` terminators the bridge's structural drop classifier cannot yet
/// discharge — `tests/ui/trust/adapter_yield/slice_adapters.rs`'s `last_xor`
/// turned fatal on a `Windows` drop-glue row). The caller additionally withholds
/// every grant when a `DefId`-lane member went unread.
#[derive(Default)]
pub(super) struct CensusDischarges {
    total: FxHashSet<String>,
    declined: FxHashSet<String>,
}

impl CensusDischarges {
    /// Census one call site of a WALKED body and record the verdict. A site the
    /// census does not speak for (a callee outside `core`/`alloc`/`std`) records
    /// its key as DECLINED: nothing the census grants may be spent on a site it
    /// did not judge, so if its key ever coincided with a censused one, the key is
    /// withheld rather than shared.
    pub(super) fn record<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        call_key: &str,
        callee: DefId,
        generic_args: ty::GenericArgs<'tcx>,
    ) {
        let verdict = census_call_site(tcx, call_key, callee, generic_args);
        self.note(call_key, verdict);
    }

    /// The ledger's rule for one WALKED site: `Some(true)` (censused total) is a
    /// candidate grant; `Some(false)` (census declined) and `None` (the census does
    /// not speak for this callee) both withhold the key.
    fn note(&mut self, call_key: &str, verdict: Option<bool>) {
        match verdict {
            Some(true) => {
                self.total.insert(call_key.to_owned());
            }
            None | Some(false) => {
                self.declined.insert(call_key.to_owned());
            }
        }
    }

    /// The ledger's rule for one WITNESS site: it can only withhold.
    fn note_witness(&mut self, call_key: &str, verdict: Option<bool>) {
        if verdict != Some(true) {
            self.declined.insert(call_key.to_owned());
        }
    }

    /// Every direct call site of `body`, with the same `func_operand_name` key its
    /// extraction gives the bridge. A call whose callee operand is not a constant
    /// `FnDef` renders `<indirect>` or a type, never a function path, so it cannot
    /// share a census key.
    fn body_call_sites<'tcx>(
        tcx: TyCtxt<'tcx>,
        body: &mir::Body<'tcx>,
    ) -> Vec<(String, DefId, ty::GenericArgs<'tcx>)> {
        let mut sites = Vec::new();
        for block in body.basic_blocks.iter() {
            let func = match &block.terminator().kind {
                mir::TerminatorKind::Call { func, .. }
                | mir::TerminatorKind::TailCall { func, .. } => func,
                _ => continue,
            };
            let Some((callee, generic_args)) = func.const_fn_def() else { continue };
            sites.push((
                trust_mir_extract::func_operand_name_in_body(tcx, body, func),
                callee,
                generic_args,
            ));
        }
        sites
    }

    /// Record every direct call site of a WALKED `body` ([`Self::record`]).
    pub(super) fn record_body<'tcx>(&mut self, tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) {
        for (call_key, callee, generic_args) in Self::body_call_sites(tcx, body) {
            self.record(tcx, &call_key, callee, generic_args);
        }
    }

    /// Record every direct call site of a lowered body the walk never reaches (a
    /// B-lane or comparator sub-lane member) as a WITNESS: judged, able to withhold
    /// its key, never to grant it.
    pub(super) fn witness_body<'tcx>(&mut self, tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) {
        for (call_key, callee, generic_args) in Self::body_call_sites(tcx, body) {
            let verdict = census_call_site(tcx, &call_key, callee, generic_args);
            self.note_witness(&call_key, verdict);
        }
    }

    /// The keys the bundle may spend on the compiler-total channel.
    pub(super) fn into_credited(self) -> FxHashSet<String> {
        let CensusDischarges { mut total, declined } = self;
        if env_flag_enabled("TRUST_SYSROOT_CENSUS_DEBUG") {
            // Diagnostics only: a key some site judged total and another declined.
            #[allow(rustc::potential_query_instability)]
            let mut withheld: Vec<&String> =
                total.iter().filter(|key| declined.contains(*key)).collect();
            withheld.sort();
            for key in withheld {
                eprintln!(
                    "[SYSROOT_CENSUS] withheld key=`{key}`: total at one lowered site, declined \
                     at another"
                );
            }
        }
        #[allow(rustc::potential_query_instability)]
        total.retain(|key| !declined.contains(key));
        total
    }
}

/// THIS body's own census-total call keys: a key is in the set only when EVERY
/// call site of that key in `body` was censused `Total` (self-poisoning, the
/// `drop_absent_cell_set_calls` discipline). Recomputed from `body` alone —
/// never from a bundle-wide union — so a member's grant is never attributed to
/// this caller. Consumed by the zero-obligation call gates, which must see the
/// same discharge the bridge made for these calls.
pub(super) fn own_census_total_calls<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
) -> FxHashSet<String> {
    let mut ledger = CensusDischarges::default();
    ledger.record_body(tcx, body);
    ledger.into_credited()
}

/// The precise `certify` refusal notes for one unproved absent-callee row, when
/// the census has something to say about its callee: what it reached (or why it
/// did not run), and — for std's own print backend — why that panic can never be
/// discharged.
pub(super) fn certify_refusal_notes(sess: &Session, callee: &str) -> Vec<String> {
    let Some(report) = with_crate_verification_state(sess, |state| {
        state.sysroot_census_reports.get(callee).cloned()
    }) else {
        return Vec::new();
    };
    let mut notes = Vec::new();
    notes.push(if let Some(reason) = report.not_applicable {
        format!(
            "`{callee}` is a std/core/alloc function whose panic-freedom this compilation \
             cannot derive: it is {reason}, so the sysroot panic census does not run on it \
             and its call stays an unproved panic-freedom row"
        )
    } else {
        format!(
            "`{callee}` is a std/core/alloc function whose own MIR reaches {} that the sysroot \
             panic census cannot exclude for every argument value: {}",
            if report.sites.len() == 1 { "a panic site" } else { "panic sites" },
            report.sites.join("; ")
        )
    });
    if report.print_backend {
        notes.push(
            "this is std's stdout/stderr print backend (`print!`/`println!`/`eprint!`/\
             `eprintln!`): it panics (`failed printing to stdout`/`stderr`) whenever the \
             write returns an error — a full disk, EIO, a non-blocking descriptor returning \
             EAGAIN, a closed pipe while SIGPIPE is ignored — which depends on the process \
             environment, not on any value in this program, so no proof can exclude it. \
             `-Z trust-policy=certify` refuses it by design; the default policy reports it \
             as a runtime-checked gap and builds (docs/design/trust-std-design.md, \
             amendment 2026-09-26)"
                .to_string(),
        );
    }
    notes
}

#[cfg(test)]
mod tests;

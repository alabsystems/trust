//! Trust (D4 increment A, 2026-09-24): RE-DERIVATION of a declared dependency's
//! body, in place of a crate-level "compiled under a verifying lane" bit.
//!
//! # The decision this implements
//!
//! D4 asked for an rmeta bit so the `is_local()` gates of the shared panic-freedom
//! bar (`dyn_dispatch_reliance::dyn_target_is_verified_panic_free`) could accept
//! a dependency's impl. It was REJECTED: a bit is a verdict import at crate
//! granularity (`docs/TCB.md` "What a digest may attest": a digest may attest
//! WHICH body was checked, never THAT it passed); it would be `false` for every
//! dependency on the shipped `targo trust` lane, whose non-root units are all
//! compiled `-Ztrust-verify=off`; and a crate that verified clean still ships
//! panicking functions (`pub fn f(x: &i32) -> i32 { x + 1 }` builds rc=0 under
//! `-Ztrust-verify=on` and exits 101 at `i32::MAX`).
//!
//! Instead a foreign body is credited only when THIS compilation re-derives its
//! verdict from the dependency's encoded MIR, under THIS compilation's policy,
//! through the SAME evidence bar a local body clears. Nothing about the
//! dependency's own verification — its `-Ztrust-verify` setting, its policy, its
//! verdicts — is ever READ.
//!
//! Trust (DEP-MEMBER-REQ-1, 2026-10-05): that does NOT make a verify-on and a
//! verify-off dependency indistinguishable, as this paragraph used to claim. The
//! dependency's verification WRITES its encoded MIR: `elide_kernel_certified_checks`
//! drops each overflow `Assert` the kernel certified, and for a function that owes
//! its callers a `requires` that certificate was earned UNDER the clause. The
//! elided body is faithful to the artifact (the premise below), but it panics where
//! vanilla Rust panics only when every execution entering it established the
//! clause, i.e. only while every call is charged (docs/TCB.md,
//! `DefinitionEntryAssumption`). MEASURED on a stage 1 of main plus wave 13: a
//! certify-built `a::inc(x) requires x < 100 { x + 1 }`, called by a verify-off
//! `c::wrapper`, bundled into a declared consumer whose ROOT calls `c::wrapper`,
//! gave that root a proved row and a program that returns 0 where vanilla Rust
//! panics, while the same consumer against a verify-off `a` was refused. Where this
//! compilation reads such MIR, a call to a `requires`-owing function must be charged
//! here or the body is declined:
//!
//! * a body re-derived HERE as its own root is verified by this compilation's own
//!   pipeline, whose direct-call lane (`add_direct_call_contract_summaries`, reading
//!   the callee crate's exported contract set) charges each call that names such a
//!   function, as for a local root (read from the code; not measured for a
//!   re-derived root);
//! * a B-lane MEMBER's calls are charged nowhere, so a member that calls one, or
//!   whose encoded MIR had one INLINED, is not bundled
//!   (`foreign_member_reaches_uncharged_requires` in `trust_verify.rs`);
//! * a body re-derived here as its own root whose encoded MIR had a
//!   `requires`-owing body INLINED (a verify-off dependency built with a MIR
//!   inliner) has no call left for its verification to charge, so it is not
//!   re-derived: conjunct (7) below, [`body_inlines_requires_owing_callee`], which
//!   the member drain reads too. MEASURED before it existed (review of
//!   `444376149e`, 2026-10-05): a verify-off `-Copt-level=3` `impl Shape for Sq {
//!   fn area(&self) -> u32 { a::inc(self.0) } }` re-derived by the C-FLOW `dyn`
//!   bar for a certify consumer declaring only that crate (`let s: &dyn Shape =
//!   &Sq(v); s.area()`) built exit 0, and the program returned 0 for
//!   `u32::MAX` where vanilla Rust panics (docs/KNOWN_HAZARDS.md,
//!   DEP-MEMBER-REQ-1).
//!
//! # What makes a foreign body re-derivable here
//!
//! All of, checked in this order by [`foreign_rederivation_decline`]:
//!
//! 1. **Declared, by crate IDENTITY** ([`declared_scope_membership`]). The crate
//!    carries a name the caller-side build declaration
//!    `-Ztrust-bundle-foreign-crate=<name>` lists (which `targo` injects for the
//!    workspace libraries a unit depends on directly), AND it is the crate this
//!    compilation BINDS under that name — the artifact an `--extern <name>=<path>`
//!    entry points at, or, with no exact path, a crate this compilation's own
//!    source references directly — AND no second crate is bound under the same
//!    name. A same-named crate that only arrived transitively (a different
//!    `StableCrateId` behind the same string) is not declared. This is a
//!    CAPABILITY — permission to read the bytes and verify them as a subject —
//!    never a claim the callee makes about itself.
//! 2. **Statically linked.** The crate's code cannot reach the process through a
//!    dynamic library: it was not loaded from a `dylib` (or `sdylib`), and no
//!    dylib this compilation loads statically includes it. A dynamic library can
//!    be replaced after this compilation checked its MIR, so the body checked
//!    need not be the body that runs.
//! 3. **Not the sysroot.** Its policy bucket is `TrustOwned*` or `ExternalDep`.
//!    `UpstreamRustModified` (`core`/`std`/`alloc`/`rustc_*`/…) and `Unknown`
//!    stay out, so sysroot behaviour is byte-identical and `derive(Debug)` stays
//!    with D1. The bucket is name-derived, and that is safe in THIS direction:
//!    a crate that spoofs a sysroot name only loses re-derivation.
//! 4. **A function body with encoded MIR** — `DefKind::Fn`/`AssocFn` and
//!    `tcx.is_mir_available` (`-Zalways-encode-mir`, which `targo` injects on
//!    every unit). Without it there is nothing to re-derive.
//! 5. **No interposable symbol.** NOT `#[no_mangle]` / `#[export_name]` /
//!    `#[linkage]` / an externally-implementable item
//!    (`CodegenFnAttrs::contains_extern_indicator`): another object can replace
//!    such a symbol at link or load time. A Rust-mangled symbol carries the
//!    crate's disambiguator and is not in that class.
//! 6. **No user `unsafe` source** — neither in the body (its own
//!    `trust_def_has_user_unsafe_source` SOURCE FACT, computed by the dependency's
//!    own compiler from its HIR and encoded beside its MIR; see
//!    `rustc_mir_transform::trust_unsafe_source_fact`) nor in any non-sysroot
//!    body inlined into its encoded MIR. Some unsafe hazards leave no trace in
//!    MIR — InstSimplify erases a lifetime-only `transmute::<&'a T, &'static T>`
//!    to a copy, and the HIR half that charges it for a LOCAL body
//!    (`validity_transmute`) has no HIR to read for a foreign one — so without
//!    this conjunct a dependency body would clear a WEAKER bar than the same
//!    body compiled locally. A missing fact row reads as `true`.
//! 7. **No inlined `requires`-owing body** ([`body_inlines_requires_owing_callee`]).
//!    No `SourceScope` of its encoded MIR inlined a function that owes its caller
//!    a `requires` (`trust_mir_extract::def_owes_caller_precondition`, read from
//!    the callee crate's exported contract set). Such a callee's crate verified it
//!    UNDER the clause and may have elided the checks it proved there; the copy
//!    the dependency's MIR inliner made has no call left for this compilation's
//!    direct-call lane to charge with a `Precondition` row, so the re-derived
//!    verdict would silently assume the clause. Asked of every inlined scope,
//!    sysroot ones included: a callee that declares no `requires` answers `false`.
//! 8. **Proof-session MIR** (T6, 2026-10-09). The body's crate encoded MIR that
//!    the proof-session `-O0` MIR pipeline built
//!    (`trust_crate_mir_is_proof_session_pipeline`, a `CrateRoot` fact its own
//!    compiler wrote). A Cargo proof session builds every dependency so; a
//!    vanilla rmeta built at `-O` (direct `trustc`, a reused build) carries the
//!    MIR inliner's and GVN's output, and `-Ztrust-verify-session` is not part of
//!    the crate hash, so nothing else tells the two apart. Without this conjunct
//!    a dependency's speed row would decide its dependents' verdicts again.
//! 9. **Within the cost bound.** At most [`MAX_BODY_BLOCKS`] basic blocks and
//!    [`MAX_BODY_STATEMENTS`] statements (a re-derivation is a full verification
//!    of the body and its bundle), and — at admission, [`admit_foreign_rederivation`]
//!    — at most [`MAX_REDERIVED_BODIES_PER_CRATE`] distinct bodies per dependency
//!    crate and [`MAX_REDERIVED_BODIES_TOTAL`] per compilation. Above either the
//!    body is declined (fail-closed): every downstream compilation pays for what
//!    it re-derives, and nothing else bounds that. A caller whose verdict needs a
//!    whole SET of bodies (the foreign-trait closure) reserves the set first,
//!    all or nothing ([`reserve_foreign_rederivations`]), so it declines on cost
//!    BEFORE forcing anything rather than after spending the budget on a set it
//!    cannot finish. The postcondition-reuse lane,
//!    which predates this module and is already demand-bounded by authored
//!    `ensures` clauses, reads conjuncts (1)–(8) only
//!    ([`foreign_rederivation_soundness_decline`]).
//!
//! Meeting these is NOT credit. It only lets the bar run: the verdict still has
//! to come from `trust_proof_results(Item(def))` computed HERE, and the bar's
//! five conjuncts (every safety row Trusted/Certified with non-`None` strength,
//! no unproved absent-callee or drop-glue row, a real verification, no user
//! axiom) still apply, as do the authored-clause refusal and the cycle bails.
//!
//! # The premise (P-MIR), disclosed rather than new
//!
//! A declared dependency's encoded `optimized_mir` — and the user-`unsafe` source
//! fact encoded beside it — describe the body its linked object code was
//! generated from. For a generic or `#[inline]` body the consumer codegens from
//! that same MIR; for any other body it rests on rustc writing the rmeta tables
//! and running codegen from one `optimized_mir` result, with E0514's version
//! string as the only guard against a different producer. The
//! postcondition-reuse lane (`cross_crate_value_used`) already rests on it.
//! Because the MIR is faithful to the artifact, checks the dependency's own
//! verification elided are faithful too.
//!
//! Trust (OVF-ASSERT-XCRATE-1, 2026-10-06): its overflow-checks setting is NOT
//! carried by the MIR, although this paragraph used to say `-Coverflow-checks=off`
//! was faithful too. An OPTIONAL overflow assert (`OverflowNeg`, `Overflow(Add |
//! Sub | Mul | Shl | Shr)`) is in the MIR whenever the body was built with checks
//! on, inherits them, or MIR-inlined a body that did; whether it fires is decided
//! by the session that CODEGENS the body (`codegen_assert_terminator`). Since
//! OVF-ASSERT-ERASED-1 erased such an assert whenever THIS session had checks off,
//! a checks-off consumer read a checks-on dependency's live assert as erased and
//! proved panic-free a member whose linked code panics (measured on the stage 1 of
//! `4ccd862830`). `trust_mir_extract` now erases one only in a body this session
//! codegens (a local body); in a foreign body the assert keeps its panic edge and
//! its condition becomes the unsupported sentinel
//! (`OptionalOverflowAssertCodegen::ForeignUnknown`), so nothing is read off its
//! success edge. The producer-side half, a checks-on dependency's `#[inline]` or
//! generic body that a checks-off consumer codegens, is still open
//! (docs/KNOWN_HAZARDS.md, OVF-ASSERT-XCRATE-1).
//!
//! The interposition exclusion (5) applies to the CREDITED body only. A callee
//! of that body is reached through the ordinary bundling lanes and inherits
//! their premises, exactly as a local `#[no_mangle]` callee of a local body
//! does today. The user-`unsafe` exclusion (6) is ALSO applied to those
//! bundled callees ([`foreign_body_carries_user_unsafe_source`], called from the
//! member drain), because a member's erased hazard would otherwise reach the
//! credited root's verdict.
//!
//! # What stays exactly as it was
//!
//! * **The X1 rule.** A dependency's `Drop` is never admitted as bundle credit
//!   (`foreign_destructor_admission.rs`), and the `ExternalDep` widening of (3)
//!   is WITHHELD from the drop-glue premise
//!   ([`dependency_destructor_withheld_from_rederivation`]): a declared
//!   `ExternalDep` destructor declines there exactly as it did before this
//!   increment, when its verification decision was `Skip(ExternalDependencyScope)`.
//! * Every undeclared dependency, every MIR-less one, every sysroot body.
//! * Error transparency: a formatting sink still requires
//!   `fmt_error_transparency::impl_is_error_transparent`, which now reads a
//!   re-derivable foreign body's MIR under the same recognizer and otherwise
//!   still refuses (the `err_dep` revision of `xcrate_fmt_dep.rs`).

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def::DefKind;
use rustc_middle::mir::Body;
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;
use rustc_span::def_id::{CrateNum, DefId, LOCAL_CRATE};
use trust_mir_extract::policy::PolicyBucket;

/// Per-body cost bound, basic blocks. Measured on the stage-1 snapshot at
/// `4e9fe36bf` (`-Zunpretty=mir`, optimized): a hand-written 5-field
/// `debug_struct` impl is 8 blocks / 25 statements, a 3-variant `match` +
/// `write!` impl 10 / 36, `Ok(())` 1 / 2. Each re-derived body costs a full
/// verification (3–4 s of marginal wall time for those shapes on the same
/// compiler), so the bound keeps an outlier dependency body from dominating a
/// downstream build while leaving ordinary formatting and trait impls far below it.
pub(super) const MAX_BODY_BLOCKS: usize = 256;
/// Per-body cost bound, statements. See [`MAX_BODY_BLOCKS`].
pub(super) const MAX_BODY_STATEMENTS: usize = 2048;
/// Distinct bodies re-derived from ONE dependency crate in one compilation.
/// At the measured 3–4 s per body this caps one crate at roughly two minutes.
pub(super) const MAX_REDERIVED_BODIES_PER_CRATE: usize = 32;
/// Distinct bodies re-derived in one compilation, over every dependency.
pub(super) const MAX_REDERIVED_BODIES_TOTAL: usize = 64;

/// Why a declared NAME does not put a crate in the declared scope.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ScopeMiss {
    /// No `-Ztrust-bundle-foreign-crate` entry names this crate (or the scope is
    /// switched off, or the def is local).
    NameNotDeclared,
    /// The name is declared, but this is not the crate this compilation binds
    /// under it — a same-named crate that arrived some other way.
    NotTheBoundCrate,
    /// More than one crate this compilation binds carries the declared name, so
    /// the name identifies no single crate.
    AmbiguousName,
    /// The crate's code can reach the process through a dynamic library.
    DynamicLinkage,
}

/// Why a NON-LOCAL body is not re-derivable in this compilation. The first
/// failing conjunct, in the order the module docs list them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ForeignDecline {
    NotDeclared(ScopeMiss),
    SysrootOrUnknownBucket,
    NotAFunctionBody,
    NoEncodedMir,
    SymbolExported,
    UserUnsafeSource,
    /// Trust (DEP-MEMBER-REQ-1, 2026-10-05): conjunct (7).
    InlinedRequiresCallee,
    /// Trust (T6, 2026-10-09): conjunct (8).
    NotProofSessionMir,
    BodyTooLarge,
    BudgetExhausted,
}

impl ForeignDecline {
    /// Probe / diagnostic text. Each names the repair, because a foreign body's
    /// own verification never surfaces a diagnostic of its own.
    pub(super) fn reason(self) -> &'static str {
        match self {
            ForeignDecline::NotDeclared(ScopeMiss::NameNotDeclared) => {
                "is not local to this crate and its crate is not in the declared bundling scope \
                 (`-Ztrust-bundle-foreign-crate`), so it has no independent verdict here"
            }
            ForeignDecline::NotDeclared(ScopeMiss::NotTheBoundCrate) => {
                "is in a crate whose NAME is declared (`-Ztrust-bundle-foreign-crate`) but which \
                 is not the crate this compilation binds under that name (no `--extern` entry \
                 points at it and this crate does not reference it directly), so the declaration \
                 does not cover it"
            }
            ForeignDecline::NotDeclared(ScopeMiss::AmbiguousName) => {
                "is in a crate whose declared name is carried by more than one crate this \
                 compilation binds, so the declaration identifies no single crate"
            }
            ForeignDecline::NotDeclared(ScopeMiss::DynamicLinkage) => {
                "is in a declared crate whose code reaches the program through a dynamic library \
                 (a `dylib` dependency, or one statically included in a dylib), which can be \
                 replaced after this compilation checked its MIR, so it is never re-derived"
            }
            ForeignDecline::SysrootOrUnknownBucket => {
                "is a sysroot (or unclassified) body; its verdict is never re-derived here"
            }
            ForeignDecline::NoEncodedMir => {
                "is in the declared bundling scope but its crate encodes no MIR for it \
                 (build the dependency with `-Zalways-encode-mir`), so nothing can be re-derived"
            }
            ForeignDecline::NotAFunctionBody => {
                "is not a function body this compilation can re-derive"
            }
            ForeignDecline::SymbolExported => {
                "exports an unmangled or linkage-controlled symbol (`#[no_mangle]`, \
                 `#[export_name]`, `#[linkage]`), which another object can interpose at link \
                 time, so the body re-derived here need not be the body that runs"
            }
            ForeignDecline::UserUnsafeSource => {
                "contains user `unsafe` source (an `unsafe` block, an `unsafe fn`, or an `unsafe \
                 impl`, in its own body or a dependency body inlined into it) according to the \
                 source fact its crate encoded; some unsafe hazards leave no trace in encoded \
                 MIR, so such a body is never re-derived"
            }
            ForeignDecline::InlinedRequiresCallee => {
                "had a function that owes its caller a `requires` inlined into its encoded MIR; \
                 that function's crate may have elided the checks it proved under the clause, \
                 and the inlined copy leaves no call for this compilation to charge with the \
                 clause, so such a body is never re-derived (build the dependency without a MIR \
                 inliner, e.g. at `-Copt-level=0`, to keep the call)"
            }
            ForeignDecline::NotProofSessionMir => {
                "is in a crate whose encoded MIR the proof-session -O0 MIR pipeline did not \
                 build (a build at `-Copt-level` above 0 outside a Trust proof session, or one \
                 that set a MIR-pipeline option), so its inliner- and optimizer-shaped MIR is \
                 never re-derived (build the dependency in the proof session, as `targo trust` \
                 does)"
            }
            ForeignDecline::BodyTooLarge => {
                "exceeds the per-body re-derivation cost bound (basic blocks or statements of its \
                 encoded MIR), so it is not re-derived here"
            }
            ForeignDecline::BudgetExhausted => {
                "exceeds this compilation's re-derivation budget: it already re-derived the \
                 maximum number of dependency bodies (per crate or in total) its cost bound allows"
            }
        }
    }

    /// The postcondition-reuse lane's reason label for the same decline.
    pub(super) fn compose_reason(self) -> &'static str {
        match self {
            ForeignDecline::NotDeclared(ScopeMiss::NameNotDeclared) => {
                "identity:non-local-undeclared"
            }
            ForeignDecline::NotDeclared(ScopeMiss::NotTheBoundCrate) => "identity:not-bound-crate",
            ForeignDecline::NotDeclared(ScopeMiss::AmbiguousName) => "identity:ambiguous-name",
            ForeignDecline::NotDeclared(ScopeMiss::DynamicLinkage) => "identity:dynamic-linkage",
            ForeignDecline::SysrootOrUnknownBucket => "identity:sysroot-bucket",
            ForeignDecline::NotAFunctionBody => "identity:not-a-fn-body",
            ForeignDecline::NoEncodedMir => "identity:no-mir",
            ForeignDecline::SymbolExported => "identity:symbol-exported",
            ForeignDecline::UserUnsafeSource => "identity:user-unsafe-source",
            ForeignDecline::InlinedRequiresCallee => "identity:inlined-requires-callee",
            ForeignDecline::NotProofSessionMir => "identity:not-proof-session-mir",
            ForeignDecline::BodyTooLarge => "budget:body-size",
            ForeignDecline::BudgetExhausted => "budget:exhausted",
        }
    }
}

// ---------------------------------------------------------------------------
// (1) + (2): the declared scope, keyed on crate identity.
// ---------------------------------------------------------------------------

/// Session-scoped memo of [`declared_scope_membership`], per `CrateNum`. Lives on
/// the `Session` (`with_trust_compiler_state`), never in a process global: a
/// `CrateNum` means nothing outside the session that assigned it.
#[derive(Default)]
struct DeclaredScopeMemo {
    by_crate: FxHashMap<CrateNum, Result<(), ScopeMiss>>,
}

/// Is `krate` in the build-declared bundling scope — by IDENTITY, not by name?
/// See the module docs, conjuncts (1) and (2). `Err` names the first miss.
///
/// This is the one definition every declared-scope lane reads (through
/// `native_bundle_crate_is_declared`): the B-lane member drain, the foreign
/// contract bundle, the postcondition-reuse lane, the per-def verification
/// decision, and re-derivation. Narrowing it can only remove capability.
pub(super) fn declared_scope_membership(tcx: TyCtxt<'_>, krate: CrateNum) -> Result<(), ScopeMiss> {
    if krate == LOCAL_CRATE {
        return Err(ScopeMiss::NameNotDeclared);
    }
    let declared = &tcx.sess.opts.unstable_opts.trust_bundle_foreign_crate;
    if declared.is_empty() {
        return Err(ScopeMiss::NameNotDeclared);
    }
    let name = tcx.crate_name(krate);
    if !declared.iter().any(|candidate| candidate.as_str() == name.as_str()) {
        return Err(ScopeMiss::NameNotDeclared);
    }
    if let Some(memo) = tcx.sess.with_trust_compiler_state::<DeclaredScopeMemo, _>(|memo| {
        memo.by_crate.get(&krate).copied()
    }) {
        return memo;
    }
    // Computed OUTSIDE the state lock: the queries below must never run while
    // this session's Trust state mutex is held.
    let answer = compute_declared_scope_membership(tcx, krate, name);
    tcx.sess.with_trust_compiler_state::<DeclaredScopeMemo, _>(|memo| {
        memo.by_crate.insert(krate, answer);
    });
    answer
}

fn compute_declared_scope_membership(
    tcx: TyCtxt<'_>,
    krate: CrateNum,
    name: Symbol,
) -> Result<(), ScopeMiss> {
    if !crate_is_bound_here(tcx, krate, name) {
        return Err(ScopeMiss::NotTheBoundCrate);
    }
    if tcx.crates(()).iter().any(|&other| {
        other != krate && tcx.crate_name(other) == name && crate_is_bound_here(tcx, other, name)
    }) {
        return Err(ScopeMiss::AmbiguousName);
    }
    if crate_reaches_process_dynamically(tcx, krate) {
        return Err(ScopeMiss::DynamicLinkage);
    }
    Ok(())
}

/// Is `krate` the crate this compilation BINDS under the declared `name`?
///
/// With an `--extern <name>=<path>` entry (every `targo` unit, and the ladder
/// runner), the answer is decided by ARTIFACT: one of the crate's loaded source
/// files must be one of the canonicalized paths that entry names. The locator
/// only consults those paths for a direct reference (a dependency's own
/// dependency is found by hash on the search path), so a same-named crate that
/// arrived transitively was loaded from a different file and is not bound.
///
/// With no exact path (`extern crate x;` found on `-L`, as compiletest's
/// `aux-build` does), the crate must be one this compilation's own source names
/// directly (`ExternCrate::is_direct`). A crate `targo` declared but the source
/// never names is then not bound — a completeness cost, never a false proof.
fn crate_is_bound_here(tcx: TyCtxt<'_>, krate: CrateNum, name: Symbol) -> bool {
    let exact: Vec<&std::path::Path> = tcx
        .sess
        .opts
        .externs
        .get(name.as_str())
        .and_then(|entry| entry.files())
        .map(|files| files.map(|file| file.canonicalized().as_path()).collect())
        .unwrap_or_default();
    if !exact.is_empty() {
        let source = tcx.used_crate_source(krate);
        return source
            .paths()
            .chain(source.sdylib_interface.iter())
            .any(|loaded| exact.iter().any(|named| *named == loaded.as_path()));
    }
    tcx.extern_crate(krate).is_some_and(|extern_crate| extern_crate.is_direct())
}

/// Can `krate`'s code reach the process through a dynamic library? Either it was
/// loaded from one (a `dylib`/`sdylib` source file exists for it — erring toward
/// `true` when an rlib was ALSO found, since which one links is decided later),
/// or some dylib this compilation loads records it as a dependency (statically
/// included, or itself dynamic). Check-mode safe: it reads only the loader's
/// records, never `dependency_formats` (which demands rlibs a pipelined
/// `cargo check` does not have).
pub(super) fn crate_reaches_process_dynamically(tcx: TyCtxt<'_>, krate: CrateNum) -> bool {
    let is_dynamic_source = |cnum: CrateNum| {
        let source = tcx.used_crate_source(cnum);
        source.dylib.is_some() || source.sdylib_interface.is_some()
    };
    if is_dynamic_source(krate) {
        return true;
    }
    tcx.crates(()).iter().any(|&other| {
        other != krate
            && is_dynamic_source(other)
            && tcx.dylib_dependency_formats(other).iter().any(|&(dep, _)| dep == krate)
    })
}

// ---------------------------------------------------------------------------
// (3): the bucket conjunct, shared with the verification decision.
// ---------------------------------------------------------------------------

/// The bucket conjunct of the declared scope, shared with
/// `verification_scope_policy_decision` so the scope decision (which lets the
/// query provider VERIFY the body) and this predicate (which lets the bar ASK)
/// cannot drift apart.
///
/// `ExternalDep` is admitted since D4-A. The earlier `TrustOwned*`-only
/// restriction reasoned that an `ExternalDep` gap would be recorded as an
/// ASSUMPTION row (`unsupported_is_failure() == false`); that method has no
/// caller outside `trust-mir-extract`'s `policy.rs`, and the scope decision is
/// the only compiler consumer of the bucket, so widening it changes skip vs.
/// verify and never how a verdict is graded (measured controlled pair: one
/// `clamp_index` body gave `verdict=mint` named `trust_xcbundle_dep` and
/// `verdict:none` named `xcbundle_dep`, with nothing else different).
pub(super) fn declared_scope_bucket_is_rederivable(bucket: PolicyBucket) -> bool {
    matches!(
        bucket,
        PolicyBucket::TrustOwnedSpecBearing
            | PolicyBucket::TrustOwnedDefault
            | PolicyBucket::ExternalDep
    )
}

// ---------------------------------------------------------------------------
// (4)–(7): the per-body conjuncts.
// ---------------------------------------------------------------------------

/// Conjunct (6): does this FOREIGN body — or a non-sysroot body inlined into its
/// MIR — carry user `unsafe` source, according to the source fact each body's
/// own crate encoded? `true` for every body whose fact row is missing.
///
/// Sysroot bodies inlined into the MIR are skipped ([`crate_is_sysroot`]:
/// authenticated by lang-item ownership or by the loader's artifact residency,
/// never by crate name): the sysroot's `unsafe` is already in the base ("The
/// build and supply chain", `docs/TCB.md`), exactly as it is when the same std
/// or `hashbrown` body is inlined into a LOCAL root. Used by re-derivation, by
/// the B-lane member drain and by the drop-glue premise, so a credited root
/// cannot hide an erased hazard in a callee either.
pub(super) fn foreign_body_carries_user_unsafe_source(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    body: &Body<'_>,
) -> bool {
    if tcx.trust_def_has_user_unsafe_source(def_id) {
        return true;
    }
    body.source_scopes.iter().any(|scope| {
        scope.inlined.is_some_and(|(instance, _)| {
            let inlined = instance.def_id();
            !crate_is_sysroot(tcx, inlined.krate) && tcx.trust_def_has_user_unsafe_source(inlined)
        })
    })
}

/// Is `krate` the compiler's own sysroot — `core`/`alloc`/`std` by lang-item
/// ownership, or a sysroot-resident crate (`hashbrown`, `std_detect`, …) by the
/// loader's artifact path? The same two arms `foreign_destructor_admission`
/// authenticates the sysroot with; never a crate name.
pub(super) fn crate_is_sysroot(tcx: TyCtxt<'_>, krate: CrateNum) -> bool {
    krate != LOCAL_CRATE
        && (super::crate_is_authentic_foundational(tcx, krate)
            || trust_mir_extract::def_is_in_sysroot_resident_crate(tcx, krate.as_def_id()))
}

/// Trust (DEP-MEMBER-REQ-1, 2026-10-05): conjunct (7). Did the MIR inliner that
/// produced `body` (a dependency's encoded MIR) copy into it a function that owes
/// its caller a `requires` — a `SourceScope` whose `inlined` instance satisfies
/// `trust_mir_extract::def_owes_caller_precondition`? Such a copy has no call
/// left to charge (`scope 1 (inlined inc)` over a bare `AddWithOverflow`, the
/// overflow `Assert` elided by `inc`'s own crate under the clause).
///
/// THE one inlined-scope test for every lane that reads a dependency's MIR
/// without charging its inlined callees: re-derivation (here, for the C-FLOW
/// `dyn` bar, the foreign-trait closure and postcondition reuse) and the B-lane
/// member drain (`foreign_member_reaches_uncharged_requires` in
/// `trust_verify.rs`), so the two cannot drift. Every scope is asked, sysroot
/// ones included: `def_owes_caller_precondition` answers `false` for a callee
/// that declares no `requires`, at the cost of one memoized `trust_contracts`
/// read per callee crate.
pub(super) fn body_inlines_requires_owing_callee(tcx: TyCtxt<'_>, body: &Body<'_>) -> bool {
    body.source_scopes.iter().any(|scope| {
        scope.inlined.is_some_and(|(inlined, _)| {
            trust_mir_extract::def_owes_caller_precondition(tcx, inlined.def_id())
        })
    })
}

/// The effective bound: the default, or LOWER if the named environment variable
/// holds a smaller number. It can never be raised — a knob that only ever
/// declines more is the only kind a cost bound may carry (the fixtures use it to
/// show the decline fires).
fn lowered_bound(var: &str, default: usize) -> usize {
    std::env::var(var)
        .ok()
        .and_then(|value| value.trim().parse::<usize>().ok())
        .map_or(default, |value| value.min(default))
}

fn body_exceeds_cost_bound(body: &Body<'_>) -> bool {
    let blocks = body.basic_blocks.len();
    let statements: usize = body.basic_blocks.iter().map(|block| block.statements.len()).sum();
    blocks > lowered_bound("TRUST_REDERIVE_MAX_BODY_BLOCKS", MAX_BODY_BLOCKS)
        || statements > lowered_bound("TRUST_REDERIVE_MAX_BODY_STATEMENTS", MAX_BODY_STATEMENTS)
}

/// Conjuncts (1)–(8) only: the SOUNDNESS declines, with no cost bound. `None`
/// when `def_id` is a NON-LOCAL body whose re-derived verdict this compilation
/// may believe. The postcondition-reuse lane reads exactly this: it predates
/// D4-A, and its forced verifications are already bounded by demand (only a
/// callee with an authored `ensures` reaches it), so putting it under the new
/// cost bound would only turn a workspace's 33rd reused clause into a refusal.
pub(super) fn foreign_rederivation_soundness_decline(
    tcx: TyCtxt<'_>,
    def_id: DefId,
) -> Option<ForeignDecline> {
    foreign_rederivation_decline_inner(tcx, def_id, false)
}

/// `None` when `def_id` is a NON-LOCAL body this compilation may re-derive,
/// the per-compilation budget aside (the per-body size bound included); otherwise
/// the first conjunct that failed. A LOCAL def answers
/// `Some(NotDeclared(NameNotDeclared))`: locality is the caller's own arm, never
/// this one. Decision-free and repeatable — it consumes no budget; see
/// [`admit_foreign_rederivation`] for the one call that does.
pub(super) fn foreign_rederivation_decline(
    tcx: TyCtxt<'_>,
    def_id: DefId,
) -> Option<ForeignDecline> {
    foreign_rederivation_decline_inner(tcx, def_id, true)
}

fn foreign_rederivation_decline_inner(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    with_body_cost_bound: bool,
) -> Option<ForeignDecline> {
    if def_id.is_local() || !super::declared_bundle_scope_subject(tcx, def_id) {
        // `declared_bundle_scope_subject` also honours the A/B switches; name the
        // identity miss when there is one.
        let miss = match declared_scope_membership(tcx, def_id.krate) {
            Err(miss) => miss,
            Ok(()) => ScopeMiss::NameNotDeclared,
        };
        return Some(ForeignDecline::NotDeclared(miss));
    }
    let bucket = trust_mir_extract::policy::classify_def(tcx, def_id, super::step4_library_lane());
    if !declared_scope_bucket_is_rederivable(bucket) {
        return Some(ForeignDecline::SysrootOrUnknownBucket);
    }
    if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
        return Some(ForeignDecline::NotAFunctionBody);
    }
    if !tcx.is_mir_available(def_id) {
        return Some(ForeignDecline::NoEncodedMir);
    }
    if tcx.codegen_fn_attrs(def_id).contains_extern_indicator() {
        return Some(ForeignDecline::SymbolExported);
    }
    let body = tcx.optimized_mir(def_id);
    if foreign_body_carries_user_unsafe_source(tcx, def_id, body) {
        return Some(ForeignDecline::UserUnsafeSource);
    }
    // Trust (DEP-MEMBER-REQ-1, 2026-10-05): conjunct (7).
    if body_inlines_requires_owing_callee(tcx, body) {
        return Some(ForeignDecline::InlinedRequiresCallee);
    }
    // Trust (T6, 2026-10-09): conjunct (8).
    if !tcx.trust_crate_mir_is_proof_session_pipeline(def_id.krate) {
        return Some(ForeignDecline::NotProofSessionMir);
    }
    if with_body_cost_bound && body_exceeds_cost_bound(body) {
        return Some(ForeignDecline::BodyTooLarge);
    }
    None
}

/// Session-scoped record of the bodies ADMITTED to re-derivation, for the
/// per-crate and per-compilation cost bounds.
///
/// Trust (D4 increment B fix, 2026-09-25): plus the bodies RESERVED by a caller
/// that must force a whole SET of verdicts or none of them — the foreign-trait
/// closure ([`reserve_foreign_rederivations`]). A reserved body counts against
/// both caps exactly like an admitted one, so nothing forced in between (a
/// nested verification's own admissions) can exhaust the budget under the
/// reserving caller and make it decline half-way through, after the work. A
/// reservation turns into an admission when the body is actually admitted (by
/// anyone), and is released — leaving no charge — when the reserving caller
/// stops before forcing it.
#[derive(Default)]
pub(super) struct RederivationLedger {
    admitted: FxHashMap<CrateNum, FxHashSet<DefId>>,
    total: usize,
    reserved: FxHashMap<CrateNum, FxHashSet<DefId>>,
    reserved_total: usize,
}

impl RederivationLedger {
    fn is_admitted(&self, def_id: DefId) -> bool {
        self.admitted.get(&def_id.krate).is_some_and(|set| set.contains(&def_id))
    }

    fn is_reserved(&self, def_id: DefId) -> bool {
        self.reserved.get(&def_id.krate).is_some_and(|set| set.contains(&def_id))
    }

    /// Admitted plus reserved bodies of `krate`: what its per-crate cap is checked against.
    fn charged_in_crate(&self, krate: CrateNum) -> usize {
        self.admitted.get(&krate).map_or(0, |set| set.len())
            + self.reserved.get(&krate).map_or(0, |set| set.len())
    }

    /// Admitted plus reserved bodies over every crate: what the total cap is checked against.
    pub(super) fn charged_total(&self) -> usize {
        self.total + self.reserved_total
    }

    fn admit(&mut self, def_id: DefId) {
        if self.reserved.get_mut(&def_id.krate).is_some_and(|set| set.remove(&def_id)) {
            self.reserved_total -= 1;
        }
        if self.admitted.entry(def_id.krate).or_default().insert(def_id) {
            self.total += 1;
        }
    }

    /// The pure core of [`budget_decline`]: would admitting `def_id` exceed
    /// `caps` = `(per_crate, total)`? `record` charges it. An admitted body is
    /// re-admitted free; a RESERVED one converts its reservation (never charged
    /// twice).
    pub(super) fn admission_decline(
        &mut self,
        def_id: DefId,
        record: bool,
        (per_crate_cap, total_cap): (usize, usize),
    ) -> Option<ForeignDecline> {
        if self.is_admitted(def_id) {
            return None;
        }
        if self.is_reserved(def_id) {
            if record {
                self.admit(def_id);
            }
            return None;
        }
        if self.charged_in_crate(def_id.krate) >= per_crate_cap || self.charged_total() >= total_cap
        {
            return Some(ForeignDecline::BudgetExhausted);
        }
        if record {
            self.admit(def_id);
        }
        None
    }

    /// The pure core of [`reserve_foreign_rederivations`]: reserve every def of
    /// `defs` not yet admitted or reserved, ALL OR NOTHING against `caps`. `Ok`
    /// carries the defs newly reserved (to be released later); `Err` changes
    /// nothing.
    pub(super) fn try_reserve(
        &mut self,
        defs: &[DefId],
        (per_crate_cap, total_cap): (usize, usize),
    ) -> Result<Vec<DefId>, ForeignDecline> {
        let mut new: Vec<DefId> = Vec::new();
        for &def_id in defs {
            if !self.is_admitted(def_id) && !self.is_reserved(def_id) && !new.contains(&def_id) {
                new.push(def_id);
            }
        }
        let mut new_per_crate: FxHashMap<CrateNum, usize> = FxHashMap::default();
        for def_id in &new {
            *new_per_crate.entry(def_id.krate).or_default() += 1;
        }
        let per_crate_over = new.iter().any(|def_id| {
            self.charged_in_crate(def_id.krate) + new_per_crate[&def_id.krate] > per_crate_cap
        });
        if per_crate_over || self.charged_total() + new.len() > total_cap {
            return Err(ForeignDecline::BudgetExhausted);
        }
        for &def_id in &new {
            self.reserved.entry(def_id.krate).or_default().insert(def_id);
            self.reserved_total += 1;
        }
        Ok(new)
    }

    /// Release every def of `defs` that is still only RESERVED. One that was
    /// admitted meanwhile (its verdict was forced) keeps its charge.
    pub(super) fn release(&mut self, defs: impl IntoIterator<Item = DefId>) {
        for def_id in defs {
            if self.reserved.get_mut(&def_id.krate).is_some_and(|set| set.remove(&def_id)) {
                self.reserved_total -= 1;
            }
        }
    }
}

/// The effective `(per_crate, total)` caps on distinct re-derived bodies.
pub(super) fn budget_caps() -> (usize, usize) {
    (
        lowered_bound("TRUST_REDERIVE_MAX_BODIES", MAX_REDERIVED_BODIES_PER_CRATE),
        lowered_bound("TRUST_REDERIVE_MAX_BODIES", MAX_REDERIVED_BODIES_TOTAL),
    )
}

/// Would admitting `def_id` exceed the cost bound? `record` charges it.
/// A body already admitted is always re-admitted (the bound counts DISTINCT
/// bodies, and its verdict is computed once per compilation anyway), and so is
/// a body already RESERVED — its charge was taken when it was reserved, and
/// admitting it converts the reservation instead of charging twice.
fn budget_decline(tcx: TyCtxt<'_>, def_id: DefId, record: bool) -> Option<ForeignDecline> {
    let caps = budget_caps();
    tcx.sess.with_trust_compiler_state::<RederivationLedger, _>(|ledger| {
        ledger.admission_decline(def_id, record, caps)
    })
}

/// A held budget RESERVATION: the bodies [`reserve_foreign_rederivations`]
/// newly reserved. Dropping it releases every one of them that was never
/// admitted, so a caller that stops early — its set failed on an earlier
/// target — is charged only for the bodies whose verdicts were actually forced.
pub(super) struct ForeignRederivationReservation<'tcx> {
    tcx: TyCtxt<'tcx>,
    newly_reserved: Vec<DefId>,
}

impl ForeignRederivationReservation<'_> {
    /// Was `def_id` newly reserved by this reservation (not admitted or reserved
    /// before it)? The closure forces such bodies LAST, so a set that fails on a
    /// body whose verdict was already paid for charges nothing new.
    pub(super) fn is_new(&self, def_id: DefId) -> bool {
        self.newly_reserved.contains(&def_id)
    }
}

impl Drop for ForeignRederivationReservation<'_> {
    fn drop(&mut self) {
        let newly_reserved = std::mem::take(&mut self.newly_reserved);
        self.tcx.sess.with_trust_compiler_state::<RederivationLedger, _>(|ledger| {
            ledger.release(newly_reserved)
        });
    }
}

/// ALL-OR-NOTHING budget reservation for a SET of foreign bodies whose verdicts
/// a caller must force together (the foreign-trait closure: a verdict over an
/// impl set is worthless unless EVERY target is forced). Checked BEFORE anything
/// is forced, against the caps with every earlier admission and reservation
/// counted: either the bodies not yet admitted or reserved all fit, and they are
/// reserved; or none is, nothing is charged, and the answer is
/// `BudgetExhausted`. Every def must be NON-LOCAL and already clear
/// [`foreign_rederivation_decline`] (the caller's pre-pass); this reads the
/// budget only.
pub(super) fn reserve_foreign_rederivations<'tcx>(
    tcx: TyCtxt<'tcx>,
    defs: &[DefId],
) -> Result<ForeignRederivationReservation<'tcx>, ForeignDecline> {
    let caps = budget_caps();
    tcx.sess
        .with_trust_compiler_state::<RederivationLedger, _>(|ledger| ledger.try_reserve(defs, caps))
        .map(|newly_reserved| ForeignRederivationReservation { tcx, newly_reserved })
}

/// THE ADMISSION: [`foreign_rederivation_decline`], then the cost bound, which
/// it CHARGES. `None` means this compilation may now force the body's verdict.
/// Call it only where that verdict is about to be forced (the shared bar, the
/// postcondition-reuse lane); every diagnostic or structural reader uses
/// [`peek_foreign_rederivation`] or [`foreign_rederivation_decline`] instead.
pub(super) fn admit_foreign_rederivation(tcx: TyCtxt<'_>, def_id: DefId) -> Option<ForeignDecline> {
    foreign_rederivation_decline(tcx, def_id).or_else(|| budget_decline(tcx, def_id, true))
}

/// [`admit_foreign_rederivation`] without charging the budget: what it WOULD
/// answer now. For probes and diagnostic notes only.
pub(super) fn peek_foreign_rederivation(tcx: TyCtxt<'_>, def_id: DefId) -> Option<ForeignDecline> {
    foreign_rederivation_decline(tcx, def_id).or_else(|| budget_decline(tcx, def_id, false))
}

/// Trust (OD-1 phase 2 review fix, 2026-10-05): has this compilation already
/// ADMITTED `def_id` under the cost bound (its verdict forced, or being forced, for
/// a check that needed it)? Reads the ledger and charges nothing. An
/// instance-hypothesis discharge carries no credit, so it reads a dependency
/// callee's verdict only when this answers `true` and never spends the budget
/// the credit-bearing lanes share (`instance_hypothesis::dependency_callee_discharge`).
pub(super) fn foreign_rederivation_already_admitted(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.sess.with_trust_compiler_state::<RederivationLedger, _>(|ledger| ledger.is_admitted(def_id))
}

/// Is `def_id` a NON-LOCAL body whose verdict this compilation may re-derive,
/// budget aside? See the module docs. `false` for every local def.
pub(super) fn foreign_body_rederivable_here(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    foreign_rederivation_decline(tcx, def_id).is_none()
}

/// Local, or a foreign body re-derivable here: the set of bodies whose MIR a
/// verdict-bearing check in this compilation may read.
pub(super) fn body_is_local_or_rederivable(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    def_id.is_local() || foreign_body_rederivable_here(tcx, def_id)
}

/// The FOREIGN half of `dyn_dispatch_reliance::body_carries_authored_clause`'s
/// surface 1 (signature clauses). A local def reads the HIR pre-filter; a
/// foreign one has no HIR, so it reads the `trust_contracts` row rmeta carries
/// (`separate_provide_extern`). That is the SAME row the re-derivation conjoins
/// as body hypotheses, so a dependency that omitted it is verified WITHOUT the
/// hypotheses — stricter, never looser. The attribute surface (2) is scanned by
/// the caller for both arms.
///
/// FAIL-CLOSED: a def whose attributes rmeta cannot answer for is treated as
/// clause-bearing.
pub(super) fn foreign_signature_clause_or_unreadable(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    if def_id.is_local() {
        return true;
    }
    if !super::attrs_queryable(tcx, def_id) {
        return true;
    }
    super::trust_contracts_if_any(tcx, def_id).is_none_or(|bundle| !bundle.is_empty())
}

/// THE X1 RULE, kept intact across the D4-A widening. `true` exactly when
/// `destructor`'s verification decision became `Verify` only because D4-A
/// admitted the `ExternalDep` bucket into the declared scope: non-local,
/// `ExternalDep`, in the declared scope, and NOT already verified by the global
/// `include_dependencies` policy (that lane verified such a body before D4-A and
/// is left untouched). `drop_glue_discharges_panic_freedom` declines such a
/// destructor, so the drop-glue premise decides byte-identically to before
/// D4-A, where the same def was `Skip(ExternalDependencyScope)` and the premise
/// got no verdict.
///
/// Whether a re-derived dependency `Drop` may EVER be credited is a separate
/// widening that D4-A does not make; `xcrate_drop_glue_dep_destructor_not_
/// credited.rs`'s `hollow_declared` revision pins that it has not been made.
pub(super) fn dependency_destructor_withheld_from_rederivation(
    tcx: TyCtxt<'_>,
    destructor: DefId,
) -> bool {
    !destructor.is_local()
        && super::declared_bundle_scope_subject(tcx, destructor)
        && matches!(
            trust_mir_extract::policy::classify_def(tcx, destructor, super::step4_library_lane()),
            PolicyBucket::ExternalDep
        )
        && !super::TrustVerifyPolicy::from_session(tcx.sess).includes_non_local_mir()
}
